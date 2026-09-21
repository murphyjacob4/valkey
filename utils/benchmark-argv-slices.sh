#!/usr/bin/env bash
# Benchmark harness for zero-allocation request parsing (argv-slices)
# Implements the methodology in Section 10 of the spec.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
SERVER_BIN="${REPO_DIR}/src/valkey-server"
BENCHMARK_BIN="${REPO_DIR}/src/valkey-benchmark"
MEMTIER_BIN="$(command -v memtier_benchmark || echo "")"
PORT=26379
SERVER_CPU=0
CLIENT_CPU=1
RESULTS_DIR="${REPO_DIR}/benchmark_results"
REQUESTS=200000

mkdir -p "${RESULTS_DIR}"

if [[ ! -x "${SERVER_BIN}" ]]; then
    echo "Server binary not found at ${SERVER_BIN}. Please run make first." >&2
    exit 1
fi

if [[ ! -x "${BENCHMARK_BIN}" ]]; then
    echo "Benchmark binary not found at ${BENCHMARK_BIN}. Please run make first." >&2
    exit 1
fi

start_server() {
    local argv_slices="$1"
    local io_threads="${2:-1}"
    local log_file="${RESULTS_DIR}/server_${argv_slices}_io${io_threads}.log"

    echo "Starting valkey-server (argv-slices=${argv_slices}, io-threads=${io_threads})..."
    taskset -c "${SERVER_CPU}" "${SERVER_BIN}" \
        --port "${PORT}" \
        --save "" \
        --appendonly no \
        --protected-mode no \
        --io-threads "${io_threads}" \
        --io-threads-do-reads "$([[ "${io_threads}" -gt 1 ]] && echo "yes" || echo "no")" \
        --argv-slices "${argv_slices}" \
        --loglevel notice > "${log_file}" 2>&1 &
    local server_pid=$!

    # Wait for server to be responsive
    for i in $(seq 1 30); do
        if "${REPO_DIR}/src/valkey-cli" -p "${PORT}" ping >/dev/null 2>&1; then
            echo "Server ready (PID ${server_pid})"
            return 0
        fi
        sleep 0.1
    done

    echo "Server failed to start. Logs:" >&2
    cat "${log_file}" >&2
    exit 1
}

stop_server() {
    echo "Stopping server on port ${PORT}..."
    "${REPO_DIR}/src/valkey-cli" -p "${PORT}" shutdown nosave >/dev/null 2>&1 || true
    sleep 0.5
}

run_valkey_benchmark() {
    local argv_slices="$1"
    local p="$2"
    local d="$3"
    local cmd="$4"
    local out_file="${RESULTS_DIR}/vb_${argv_slices}_p${p}_d${d}_${cmd}.txt"

    echo "Running valkey-benchmark: cmd=${cmd} pipeline=${p} datasize=${d} (argv-slices=${argv_slices})"
    taskset -c "${CLIENT_CPU}" "${BENCHMARK_BIN}" \
        -p "${PORT}" \
        -t "${cmd}" \
        -n "${REQUESTS}" \
        -P "${p}" \
        -d "${d}" \
        -q --csv > "${out_file}" 2>&1

    cat "${out_file}"
}

run_memtier_benchmark() {
    local argv_slices="$1"
    local p="$2"
    local d="$3"
    local io_threads="$4"

    if [[ -z "${MEMTIER_BIN}" ]]; then
        echo "memtier_benchmark not installed, skipping memtier run."
        return 0
    fi

    local out_file="${RESULTS_DIR}/memtier_${argv_slices}_p${p}_d${d}_io${io_threads}.txt"
    echo "Running memtier_benchmark: pipeline=${p} datasize=${d} io-threads=${io_threads} (argv-slices=${argv_slices})"

    taskset -c "${CLIENT_CPU}" "${MEMTIER_BIN}" \
        -p "${PORT}" \
        -c 50 \
        -t 1 \
        --ratio=1:10 \
        --pipeline="${p}" \
        --data-size="${d}" \
        --requests="$((REQUESTS / 50))" \
        --print-percentiles 50,90,99 > "${out_file}" 2>&1

    grep -E "(Totals|SET|GET)" "${out_file}" || cat "${out_file}"
}

collect_info() {
    local argv_slices="$1"
    echo "--- Server Stats (argv-slices=${argv_slices}) ---"
    "${REPO_DIR}/src/valkey-cli" -p "${PORT}" info stats | grep -E "argv_|total_commands_processed" || true
    "${REPO_DIR}/src/valkey-cli" -p "${PORT}" info memory | grep -E "used_memory_human|mem_fragmentation_ratio" || true
}

run_suite() {
    local argv_slices="$1"
    local io_threads="${2:-1}"

    start_server "${argv_slices}" "${io_threads}"

    # Benchmark matrix per Section 10:
    # 1. valkey-benchmark at -P 1 and -P 16, 3 B and 64 B and 1024 B values
    for d in 3 64 1024; do
        for p in 1 16; do
            for cmd in set get incr; do
                if [[ "${cmd}" == "incr" && "${d}" -gt 64 ]]; then
                    continue # INCR does not use payload data size
                fi
                run_valkey_benchmark "${argv_slices}" "${p}" "${d}" "${cmd}"
            done
        done
    done

    # 2. memtier_benchmark, 50 conns, 1:10 ratio, pipeline 1 and 16
    for p in 1 16; do
        run_memtier_benchmark "${argv_slices}" "${p}" 64 "${io_threads}"
        run_memtier_benchmark "${argv_slices}" "${p}" 1024 "${io_threads}"
    done

    collect_info "${argv_slices}"
    stop_server
}

main() {
    trap stop_server EXIT INT TERM

    echo "=== Benchmarking Baseline (argv-slices no) ==="
    run_suite "no" 1

    echo "=== Benchmarking Optimized (argv-slices yes) ==="
    run_suite "yes" 1

    echo "=== Benchmarking Optimized with I/O Threads (argv-slices yes, io-threads 4) ==="
    run_suite "yes" 4

    echo "Benchmark suite completed. Results saved to ${RESULTS_DIR}."
}

if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    main "$@"
fi
