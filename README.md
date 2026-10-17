# zevm

<a href="https://unlicense.org/"><img src="https://upload.wikimedia.org/wikipedia/commons/e/eb/PD-icon-black.svg" width="20" height="20" alt="Public domain"/></a>

An implementation of the Ethereum Virtual Machine in Zig. Currently under heavy development.

## Requirements

- Zig `0.16.0` — see [ziglang.org/download](https://ziglang.org/download/) for installation instructions.
- A C toolchain (`cc`) and `libc` — needed to build the vendored `libsecp256k1`.

## Building

```sh
zig build
```

## Running tests

```sh
make test
```

or directly:

```sh
zig build test --summary all
```

## Type-checking

```sh
make check
```

Compiles the library and examples without running tests or emitting a final binary, useful for fast diagnostics.

## Running the examples

```sh
zig build example -- basic
```

- `basic` — the minimal case: create a `State`, an `Evm`, and execute a transaction.
- `loop` — a hand-written `JUMP`/`JUMPI` loop bytecode program, run directly through `Interpreter`.
- `sync` — loads Ethereum mainnet's genesis allocation into a `State`, then replays real mainnet blocks 0..46299 (including the historic first-ever Ethereum transaction, at block 46147) through `Evm.processBlock`, continuously from genesis, from a bundled JSON fixture.
- `sync_era1` — replays real historical mainnet blocks from `.era1` files.

## Downloading real mainnet history

`sync_era1` and the `rzevm/examples/*_era1.rs` benchmarks below read `.era1` files — [Portal Network](https://github.com/ethereum/portal-network-specs)'s archival format for pre-merge mainnet history (RLP-encoded blocks, Snappy-compressed, in e2store containers, 8,192 blocks per file). Download them with:

```sh
make download-era1   # blocks 0..15,537,393 (all of pre-merge history)
```

It skips files already present.

## Benchmarking against revm

`rzevm/` is a separate Rust project alongside this one, used to compare zevm against [revm](https://github.com/bluealloy/revm) on identical workloads. Requires a Rust toolchain (`cargo`/`rustc`) in addition to Zig.

The real comparison is the full `.era1` replay:

```sh
make download-era1   # once, if you haven't already
make bench-era1
```

All three print a `decode`/`execute` breakdown, so EVM-execution speed and everything-else (parsing) can be compared separately. `zevm via Rust FFI` decodes blocks in Rust (same code as `revm`'s row) and calls into `libzevm.a` per block for `execute`, isolating FFI-call overhead from raw execution speed. As of the last run:

| | total | decode (parse + recover) | execute (EVM only) |
|---|---|---|---|
| revm (native Rust) | 78.57s | 63.22s | 13.38s |
| zevm via Rust FFI | 78.55s | 62.79s | 14.10s |
| **zevm (pure Zig)** | **74.11s** | **58.40s** | **13.92s** |

For a quick sanity check instead of the full 1M-block run, `make bench` runs a smaller (46,300-block, pre-parsed-JSON) version.

Both sides' final state has been checked against real chain data, but their own account-touched counters aren't directly comparable: zevm's counts only accounts that were actually written (balance/nonce/code/storage change), while revm's `cache.accounts.len()` also includes every account merely *read* (e.g. a `BALANCE`/`EXTCODESIZE`/`EXTCODEHASH` check, or a `DELEGATECALL`/`STATICCALL`/`CALLCODE` target resolution) via its read-through `CacheDB`, regardless of whether that read ever gets materialized in the real state trie. zevm's number is the one that matches real consensus-relevant state.

## Calling zevm from Rust via FFI

zevm exposes a C ABI (`src/ffi.zig`) that can be called from Rust. `rzevm/src/main.rs` demonstrates it, replaying genesis + blocks 0..46299 through zevm from a Rust process.

```sh
zig build -Doptimize=ReleaseFast
cd rzevm
cargo run --release --bin rzevm
```

## License

[The Unlicense](LICENSE) — public domain.
