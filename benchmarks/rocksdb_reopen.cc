// Native writer and reader for the controlled process-death fixture.
#include <charconv>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <memory>
#include <stdexcept>
#include <string>
#include <string_view>

#include "rocksdb/db.h"
#include "rocksdb/options.h"

namespace {

constexpr uint64_t value_mask = 0xfedcba9876543210;

uint64_t positive_count(std::string_view input) {
    uint64_t count = 0;
    const auto result = std::from_chars(input.data(), input.data() + input.size(), count);
    if (result.ec != std::errc{} || result.ptr != input.data() + input.size() || count == 0) {
        throw std::runtime_error("expected a positive uint64 count");
    }
    return count;
}

std::string word(uint64_t input) {
    std::string bytes(8, '\0');
    for (int i = 7; i >= 0; --i) {
        bytes[i] = static_cast<char>(input & 0xff);
        input >>= 8;
    }
    return bytes;
}

void require(const rocksdb::Status& status) {
    if (!status.ok()) throw std::runtime_error(status.ToString());
}

std::unique_ptr<rocksdb::DB> open(const std::string& path, bool create) {
    rocksdb::Options options;
    options.create_if_missing = create;
    options.use_fsync = true;
    rocksdb::DB* db = nullptr;
    require(rocksdb::DB::Open(options, path, &db));
    return std::unique_ptr<rocksdb::DB>(db);
}

void write_keys(rocksdb::DB& db, uint64_t first, uint64_t stop) {
    rocksdb::WriteOptions options;
    options.sync = true;
    for (uint64_t key = first; key < stop; ++key) {
        require(db.Put(options, word(key), word(key ^ value_mask)));
    }
}

void populate(const std::string& path, uint64_t prefix, uint64_t size) {
    const auto db = open(path, true);
    write_keys(*db, 0, prefix);
    rocksdb::FlushOptions flush;
    flush.wait = true;
    require(db->Flush(flush));
    write_keys(*db, prefix, size);
    std::cout << "acknowledged " << size << std::endl;
    std::string line;
    std::getline(std::cin, line);
    throw std::runtime_error("writer's stdin closed before SIGKILL");
}

std::string peak_rss_line() {
    std::ifstream status("/proc/self/status");
    std::string line;
    while (std::getline(status, line)) {
        if (line.compare(0, 6, "VmHWM:") == 0) return line;
    }
    return "-";
}

void recover(const std::string& path, uint64_t size) {
    using Clock = std::chrono::steady_clock;
    const auto key = word(size - 1);
    std::string value;
    const auto start = Clock::now();
    const auto db = open(path, false);
    const auto first_read = db->Get(rocksdb::ReadOptions{}, key, &value);
    const auto elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now() - start);
    require(first_read);
    if (value != word((size - 1) ^ value_mask)) {
        throw std::runtime_error("first recovered read differed");
    }
    const auto rss = peak_rss_line();
    uint64_t expected = 0;
    std::unique_ptr<rocksdb::Iterator> rows(db->NewIterator(rocksdb::ReadOptions{}));
    for (rows->SeekToFirst(); rows->Valid(); rows->Next()) {
        if (expected >= size || rows->key() != word(expected) || rows->value() != word(expected ^ value_mask)) {
            throw std::runtime_error("unexpected recovered row at key " + std::to_string(expected));
        }
        ++expected;
    }
    require(rows->status());
    if (expected != size) throw std::runtime_error("recovered row count differed");
    rows.reset();
    std::cout << elapsed.count() << '\n' << rss << '\n';
    require(db->Close());
}

}  // namespace

int main(int argc, char** argv) {
    try {
        if (argc != 5) throw std::runtime_error("usage: rocksdb-reopen (write|read) DIR PREFIX SUFFIX");
        const auto prefix = positive_count(argv[3]);
        const auto suffix = positive_count(argv[4]);
        if (prefix > std::numeric_limits<uint64_t>::max() - suffix) {
            throw std::runtime_error("uint64 count overflow");
        }
        const std::string_view mode = argv[1];
        if (mode == "write") {
            populate(argv[2], prefix, prefix + suffix);
        } else if (mode == "read") {
            recover(argv[2], prefix + suffix);
        } else {
            throw std::runtime_error("expected write or read mode");
        }
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
