# Local setup (measured on macOS arm64, 2026-09-21)

The root README lists the dependencies but not their versions. These are the
versions that actually work, and the two traps that cost time.

## Toolchain

| tool | needed | note |
|------|--------|------|
| rustc | **>= 1.96** | `evm2@0.1.0 requires rustc 1.96`; 1.91 fails the build outright. Verified on 1.98.1. |
| python | **>= 3.9** | `evm.py` uses `str.removeprefix`. A system 3.7 fails at import. |
| bun | any recent | 1.4.2 verified. Required -- see below. |
| clang | 14+ | Apple clang 21 verified. |

## Trap 1: the stock Bend compiler cannot build this repo

Bend 2.0.25 **type-checks** everything under `full/` cleanly in ~4s, including
`full/main.bend`. It cannot **compile** it:

    Error: an arity over 255

The 2.0.25 changelog (#944) boxes wide records, but its own note says "a join
holding several wide results, or a wide value held across a non-tail call, is
refused with the same message" -- which is this case. So
`toolchain-layout.patch` and the copied compiler in `toolchain-debug/` are
still load-bearing, and `bend-local.sh` (hence bun) is required for any build.

Setting `BEND=~/.bend/bin/bend` to use the stock compiler gets you a clean type
check and then fails at codegen. Use it for proof work, not for builds.

## Trap 2: evm2-reference is a sibling, not a submodule

    git clone https://github.com/alloy-rs/evm2.git evm2-reference
    git -C evm2-reference checkout 0a5314efb28cbef7dc1a83e38ac75860b974adcd

It must sit beside the repo directory, not inside it.

## Full sequence

    cargo build --locked --manifest-path precompile-host/Cargo.toml
    cargo build --locked --manifest-path revm-adapter/Cargo.toml
    python3 evm.py --build
    python3 evm.py --backend js --build
    EVM_BACKEND=native python3 test_full_differential.py
    EVM_BACKEND=js python3 test_full_differential.py
    python3 test_precompiles.py
    python3 test_frame_invariants.py
    python3 test_contract_fixtures.py

## Baseline on this fork's `proof-oriented` branch (B1 applied)

    evm.py examples/return-42.json   success, gas 999982, output 0x..2a
    native differential              RESULT 624 0
    js differential                  RESULT 624 0
    precompiles                      js 37 cases 0 failures / native 37 cases 0 failures
    frame invariants                 56 []
    contract fixtures                RESULT 22 []
    local Bend suites                87 PASS, byte-identical to upstream

One pre-existing upstream failure: `full/opcode-tests.bend immediate_missing`.
Present on unmodified upstream too.

## Not yet standing: the 15,918-fixture state gate

`conformance/corpus-manifest.json` pins execution-specs
`tests-glamsterdam-devnet@v8.1.4`, **2.57 GB extracted**, not a repo artifact.
`conformance/full_state_gate.py` runs it at `--workers 12 --timeout 1200`, and
the README's own sequencing (native gate, then JS) implies hours.

That gate is the release-grade check and must pass before anything here is
proposed upstream. The suites above are the fast net for day-to-day work.
