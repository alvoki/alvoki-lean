#include <charconv>
#include <chrono>
#include <cstdint>
#include <filesystem>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

#include <rocksdb/db.h>
#include <rocksdb/options.h>
#include <rocksdb/slice.h>
#include <rocksdb/version.h>
#include <rocksdb/write_batch.h>

namespace {
using Clock = std::chrono::steady_clock;
namespace fs = std::filesystem;

struct Samples {
    std::vector<uint64_t> batches;
    uint64_t total;
};

uint64_t parse_uint(const char* value, const char* argument) {
    const std::string_view text(value);
    uint64_t result;
    const auto parsed = std::from_chars(text.data(), text.data() + text.size(), result);
    if (parsed.ec != std::errc{} || parsed.ptr != text.data() + text.size()) {
        throw std::runtime_error(std::string(argument) + " must be an unsigned decimal integer");
    }
    return result;
}

void check_status(const rocksdb::Status& status, const char* operation) {
    if (!status.ok()) {
        throw std::runtime_error(std::string(operation) + ": " + status.ToString());
    }
}

uint64_t elapsed(Clock::time_point start) {
    return std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now() - start).count();
}

uint64_t payload(uint64_t key) {
    return key ^ UINT64_C(0xfedcba9876543210);
}

std::string encode_word(uint64_t word) {
    std::string bytes(8, '\0');
    for (unsigned i = 0; i < 8; ++i) {
        bytes[i] = static_cast<char>(static_cast<unsigned char>(word >> (8 * i)));
    }
    return bytes;
}

uint64_t decode_word(const rocksdb::Slice& bytes) {
    if (bytes.size() != 8) {
        throw std::runtime_error("expected one little-endian 64-bit word");
    }
    uint64_t word = 0;
    for (unsigned i = 0; i < 8; ++i) {
        word |= static_cast<uint64_t>(static_cast<unsigned char>(bytes[i])) << (8 * i);
    }
    return word;
}

std::unique_ptr<rocksdb::DB> open(const fs::path& path, bool create) {
    rocksdb::Options options;
    options.create_if_missing = create;
    options.error_if_exists = create;
    options.use_fsync = true;
    options.manual_wal_flush = false;
    options.compression = rocksdb::kNoCompression;
    options.compaction_style = rocksdb::kCompactionStyleLevel;
    options.max_background_jobs = 2;
    options.max_subcompactions = 1;
    rocksdb::DB* db = nullptr;
    check_status(rocksdb::DB::Open(options, path.string(), &db), "open");
    return std::unique_ptr<rocksdb::DB>(db);
}

Samples run_batches(rocksdb::DB& db, uint64_t count, uint64_t batch_size) {
    rocksdb::WriteOptions options;
    options.sync = true;
    options.disableWAL = false;
    Samples samples;
    samples.batches.reserve(count / batch_size);
    const auto started = Clock::now();
    for (uint64_t offset = 0; offset < count; offset += batch_size) {
        rocksdb::WriteBatch batch;
        for (uint64_t index = 0; index < batch_size; ++index) {
            const uint64_t key = offset + index;
            check_status(batch.Put(encode_word(key), encode_word(payload(key))), "prepare batch row");
        }
        const auto before = Clock::now();
        const auto status = db.Write(options, &batch);
        const auto ns = elapsed(before);
        check_status(status, "write batch");
        if (db.GetLatestSequenceNumber() != offset + batch_size) {
            throw std::runtime_error("unexpected batch sequence at row " + std::to_string(offset + batch_size));
        }
        samples.batches.push_back(ns);
    }
    samples.total = elapsed(started);
    return samples;
}

void verify_reopen(const fs::path& path, uint64_t count) {
    const auto db = open(path, false);
    if (db->GetLatestSequenceNumber() != count) {
        throw std::runtime_error("reopen returned the wrong committed sequence");
    }
    {
        const std::unique_ptr<rocksdb::Iterator> rows(db->NewIterator(rocksdb::ReadOptions{}));
        uint64_t seen = 0;
        for (rows->SeekToFirst(); rows->Valid(); rows->Next()) {
            const uint64_t key = decode_word(rows->key());
            if (key >= count || decode_word(rows->value()) != payload(key)) {
                throw std::runtime_error("unexpected reopened row for key " + std::to_string(key));
            }
            ++seen;
        }
        check_status(rows->status(), "verify reopened rows");
        if (seen != count) {
            throw std::runtime_error("reopen returned the wrong set of keys");
        }
    }
    check_status(db->Close(), "close reopened database");
}
}  // namespace

int main(int argc, char** argv) {
    try {
        if (argc == 2 && std::string_view(argv[1]) == "--version") {
            std::cout << rocksdb::GetRocksVersionAsString() << '\n';
            return 0;
        }
        if (argc != 4) {
            throw std::runtime_error("usage: rocksdb-batch PATH ROWS BATCH_SIZE");
        }
        const fs::path path(argv[1]);
        const uint64_t count = parse_uint(argv[2], "ROWS");
        const uint64_t batch_size = parse_uint(argv[3], "BATCH_SIZE");
        if (count == 0 || batch_size == 0 || count % batch_size != 0) {
            throw std::runtime_error("expected a positive row count divisible by the positive batch size");
        }
        if (!fs::is_directory(path) || !fs::is_empty(path)) {
            throw std::runtime_error("benchmark directory must be empty");
        }
        auto db = open(path, true);
        const auto samples = run_batches(*db, count, batch_size);
        check_status(db->Close(), "close");
        db.reset();
        verify_reopen(path, count);

        std::cout << "rows,kind,ns\n";
        uint64_t completed = 0;
        for (const auto ns : samples.batches) {
            completed += batch_size;
            std::cout << completed << ",batch," << ns << '\n';
        }
        std::cout << count << ",total," << samples.total << '\n';
        return 0;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
