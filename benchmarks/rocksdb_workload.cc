#include <algorithm>
#include <charconv>
#include <chrono>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <rocksdb/db.h>
#include <rocksdb/options.h>
#include <rocksdb/slice.h>
#include <rocksdb/version.h>

namespace {
using Clock = std::chrono::steady_clock;
using Values = std::unordered_map<uint64_t, uint64_t>;
namespace fs = std::filesystem;

struct Sample {
    uint64_t op;
    const char* kind;
    uint64_t measurement;
};

struct SnapshotDeleter {
    rocksdb::DB* db;

    void operator()(const rocksdb::Snapshot* snapshot) const {
        db->ReleaseSnapshot(snapshot);
    }
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

void verify_contents(rocksdb::DB& db, const rocksdb::ReadOptions& options,
                     const Values& expected, const char* view) {
    const std::unique_ptr<rocksdb::Iterator> rows(db.NewIterator(options));
    size_t count = 0;
    for (rows->SeekToFirst(); rows->Valid(); rows->Next()) {
        const uint64_t key = decode_word(rows->key());
        const auto entry = expected.find(key);
        if (entry == expected.end() || entry->second != decode_word(rows->value())) {
            throw std::runtime_error(std::string(view) + " disagrees with the oracle at key " +
                                     std::to_string(key));
        }
        ++count;
    }
    check_status(rows->status(), view);
    if (count != expected.size()) {
        throw std::runtime_error(std::string(view) + " has the wrong number of rows");
    }
}

Sample measure_get(rocksdb::DB& db, const rocksdb::ReadOptions& options, uint64_t key,
                   const uint64_t* expected, uint64_t completed, const char* kind) {
    const std::string key_bytes = encode_word(key);
    std::string value_bytes;
    const auto start = Clock::now();
    const auto status = db.Get(options, key_bytes, &value_bytes);
    const auto ns = elapsed(start);
    const bool absent = status.IsNotFound();
    if (!absent) {
        check_status(status, kind);
    }
    if (absent ? expected != nullptr : expected == nullptr || decode_word(value_bytes) != *expected) {
        throw std::runtime_error(std::string(kind) + " disagrees with the oracle at op " +
                                 std::to_string(completed));
    }
    return {completed, kind, ns};
}

uint64_t db_bytes(const fs::path& path) {
    uint64_t bytes = 0;
    for (const auto& entry : fs::recursive_directory_iterator(path)) {
        if (entry.is_regular_file()) {
            bytes += entry.file_size();
        }
    }
    return bytes;
}

uint64_t snapshot_key(const std::vector<uint64_t>& keys, uint64_t interval) {
    std::unordered_set<uint64_t> written;
    uint64_t last_write = 0;
    for (uint64_t i = 0; i < std::min<uint64_t>(interval, keys.size()); i += 2) {
        last_write = keys[i];
        written.insert(last_write);
    }

    const uint64_t release = interval > keys.size() / 3 ? keys.size() : 3 * interval;
    for (uint64_t i = interval; i < release; ++i) {
        if (i % 2 == 0 && written.count(keys[i]) != 0) {
            return keys[i];
        }
    }
    return last_write;
}

uint64_t process_write_bytes() {
    std::ifstream io("/proc/self/io");
    std::string field;
    uint64_t count;
    while (io >> field >> count) {
        if (field == "write_bytes:") {
            return count;
        }
    }
    throw std::runtime_error("could not read write_bytes from /proc/self/io");
}

std::vector<Sample> run(const fs::path& path, bool maintenance, uint64_t ops, uint64_t keys,
                        uint64_t interval, uint64_t seed) {
    if (fs::exists(path) && (!fs::is_directory(path) || !fs::is_empty(path))) {
        throw std::runtime_error("database path must be a fresh empty directory");
    }

    std::vector<uint64_t> trace;
    trace.reserve(ops);
    for (uint64_t i = 0; i < ops; ++i) {
        seed = seed * UINT64_C(6364136223846793005) + UINT64_C(1442695040888963407);
        trace.push_back((seed >> 32) % keys);
    }

    rocksdb::Options options;
    options.create_if_missing = true;
    options.error_if_exists = true;
    options.use_fsync = true;
    options.manual_wal_flush = false;
    options.compression = rocksdb::kNoCompression;
    options.compaction_style = rocksdb::kCompactionStyleLevel;
    options.disable_auto_compactions = maintenance;
    options.max_background_jobs = 2;
    options.max_subcompactions = 1;
    rocksdb::DB* opened = nullptr;
    check_status(rocksdb::DB::Open(options, path.string(), &opened), "open");
    const std::unique_ptr<rocksdb::DB> db(opened);

    rocksdb::WriteOptions write_options;
    write_options.sync = true;
    write_options.disableWAL = false;
    const rocksdb::ReadOptions read_options;
    rocksdb::FlushOptions flush_options;
    flush_options.wait = true;
    rocksdb::CompactRangeOptions compact_options;
    compact_options.exclusive_manual_compaction = true;
    compact_options.max_subcompactions = 1;

    Values live;
    const uint64_t held_key = maintenance ? snapshot_key(trace, interval) : 0;
    uint64_t snapshot_value = 0;
    std::unique_ptr<const rocksdb::Snapshot, SnapshotDeleter> pin(nullptr, SnapshotDeleter{db.get()});
    std::vector<Sample> samples;
    samples.reserve(ops);

    const auto written_before = process_write_bytes();
    const auto work_start = Clock::now();
    for (uint64_t i = 0; i < ops; ++i) {
        const uint64_t completed = i + 1;
        const uint64_t key = trace[i];
        if (i % 2 == 0) {
            const std::string key_bytes = encode_word(key);
            const std::string value_bytes = encode_word(completed);
            const auto start = Clock::now();
            const auto status = db->Put(write_options, key_bytes, value_bytes);
            const auto ns = elapsed(start);
            check_status(status, "put");
            samples.push_back({completed, "put", ns});
            live.insert_or_assign(key, completed);
        } else {
            const auto entry = live.find(key);
            const uint64_t* expected = entry == live.end() ? nullptr : &entry->second;
            samples.push_back(measure_get(*db, read_options, key, expected, completed, "get"));
        }

        if (!maintenance || completed % interval != 0) {
            continue;
        }
        const uint64_t cycle = completed / interval;
        if (cycle == 1) {
            snapshot_value = live.at(held_key);
            const auto start = Clock::now();
            const auto* snapshot = db->GetSnapshot();
            const auto ns = elapsed(start);
            if (snapshot == nullptr) {
                throw std::runtime_error("could not pin a RocksDB snapshot");
            }
            pin.reset(snapshot);
            samples.push_back({completed, "snapshot_pin", ns});
        }

        auto start = Clock::now();
        const auto flushed = db->Flush(flush_options);
        const auto flush_ns = elapsed(start);
        check_status(flushed, "flush");
        samples.push_back({completed, "checkpoint", flush_ns});

        if (cycle >= 2) {
            start = Clock::now();
            const auto compacted = db->CompactRange(compact_options, nullptr, nullptr);
            const auto compact_ns = elapsed(start);
            check_status(compacted, "compact");
            samples.push_back({completed, "compact", compact_ns});
        }

        if (pin) {
            rocksdb::ReadOptions old = read_options;
            old.snapshot = pin.get();
            samples.push_back(measure_get(*db, old, held_key, &snapshot_value, completed, "snapshot_get"));
            if (cycle == 3) {
                start = Clock::now();
                pin.reset();
                samples.push_back({completed, "snapshot_release", elapsed(start)});
            }
        }
        samples.push_back({completed, "db_bytes", db_bytes(path)});
    }
    const auto total_ns = elapsed(work_start);
    const auto written = process_write_bytes() - written_before;
    if (!maintenance) {
        samples.push_back({ops, "db_bytes", db_bytes(path)});
    }
    // File lengths describe the retained namespace. The process counter
    // measures storage-layer bytes attributed to the process during the loop.
    samples.push_back({ops, "process_write_bytes", written});
    samples.push_back({ops, "total", total_ns});

    verify_contents(*db, read_options, live, "latest view");
    pin.reset();
    check_status(db->Close(), "close");
    return samples;
}
}  // namespace

int main(int argc, char** argv) {
    try {
        if (argc == 2 && std::string_view(argv[1]) == "--version") {
            std::cout << rocksdb::GetRocksVersionAsString() << '\n';
            return 0;
        }
        if (argc != 7) {
            throw std::runtime_error("usage: rocksdb-workload PATH MODE OPS KEYS INTERVAL SEED");
        }
        const std::string_view mode(argv[2]);
        const bool maintenance = mode == "maintenance";
        if (!maintenance && mode != "mixed") {
            throw std::runtime_error("mode must be mixed or maintenance");
        }
        const uint64_t ops = parse_uint(argv[3], "OPS");
        const uint64_t keys = parse_uint(argv[4], "KEYS");
        const uint64_t interval = parse_uint(argv[5], "INTERVAL");
        const uint64_t seed = parse_uint(argv[6], "SEED");
        if (ops == 0 || keys == 0 || (maintenance && interval == 0)) {
            throw std::runtime_error("OPS and KEYS must be positive and maintenance requires a positive INTERVAL");
        }
        const auto samples = run(argv[1], maintenance, ops, keys, interval, seed);
        std::cout << "op,kind,ns\n";
        for (const auto& sample : samples) {
            std::cout << sample.op << ',' << sample.kind << ',' << sample.measurement << '\n';
        }
        return 0;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
