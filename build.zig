const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const lib_mod = b.addModule("zevm", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
        // Rust builds position-independent executables by default, which
        // requires every statically-linked library to be PIC too — needed
        // for rzevm (the Rust FFI demo) to link against libzevm.a.
        .pic = true,
    });

    // Real libsecp256k1 (the same C library revm's own `secp256k1` crate is
    // backed by) — `ECRECOVER` calls from inside real contract execution
    // turned out to be ~24% of total replay cycles (measured via `perf`)
    // with Zig std's generic, pure-software `std.crypto.ecc.Secp256k1`,
    // dwarfing every other fix this project has made. revm's own default
    // build already prefers this same C library over its pure-Rust `k256`
    // fallback specifically for the speed — keeping zevm's precompile
    // pure-Zig wasn't preserving a fair "from scratch vs from scratch"
    // comparison, it was just leaving zevm slower for no reason revm
    // itself honors.
    //
    // Vendored directly under `third_party/secp256k1/` (a trimmed current
    // release, see that directory) rather than depending on the
    // `zig-eth-secp256k1` package: that package turned out to vendor a
    // ~2015-era libsecp256k1 snapshot (its own `ext.c`'s copyright header
    // names go-ethereum developers) — missing about a decade of upstream
    // performance work (windowed-multiplication tuning, baked-in
    // precomputed tables) that Rust's actively-maintained `secp256k1-sys`
    // tracks current with. Measured ~1.65x faster per recovery after
    // switching (50.1us -> ~30us), on top of the ~2x already gained from
    // fixing that package's field-representation build flags. A pleasant
    // side effect: the current upstream source auto-detects field/scalar
    // representation and wide-multiplication strategy from standard
    // compiler macros (`__SIZEOF_INT128__` etc.) — none of the manual
    // flags the old vendored copy needed hand-patched are needed at all
    // here; `ENABLE_MODULE_RECOVERY` is the only one required, since the
    // recovery module (unlike the base library) is opt-in.
    const secp256k1_lib = b.addLibrary(.{
        .linkage = .static,
        .name = "secp256k1",
        .root_module = b.createModule(.{ .target = target, .optimize = optimize }),
    });
    secp256k1_lib.root_module.addIncludePath(b.path("third_party/secp256k1"));
    secp256k1_lib.root_module.addIncludePath(b.path("third_party/secp256k1/src"));
    secp256k1_lib.root_module.addCSourceFiles(.{
        .files = &.{
            "third_party/secp256k1/src/secp256k1.c",
            "third_party/secp256k1/src/precomputed_ecmult.c",
            "third_party/secp256k1/src/precomputed_ecmult_gen.c",
        },
        .flags = &.{"-DENABLE_MODULE_RECOVERY=1"},
    });
    secp256k1_lib.root_module.link_libc = true;
    b.installArtifact(secp256k1_lib);

    lib_mod.linkLibrary(secp256k1_lib);
    lib_mod.link_libc = true;

    const lib = b.addLibrary(.{
        .linkage = .static,
        .name = "zevm",
        .root_module = lib_mod,
    });
    // Static libs don't bundle compiler-rt by default (only exes and
    // dynamic libs do) — needed here since a non-Zig linker (Rust's, for
    // rzevm) won't know to supply Zig's software implementations of
    // wide-integer division (our u256/u512 arithmetic needs them).
    lib.bundle_compiler_rt = true;
    b.installArtifact(lib);

    const lib_unit_tests = b.addTest(.{
        .root_module = lib_mod,
    });
    const run_lib_unit_tests = b.addRunArtifact(lib_unit_tests);

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_lib_unit_tests.step);

    // Type-check only, no codegen — wired up as ZLS's build-on-save step for fast diagnostics.
    const check_step = b.step("check", "Check compilation errors");
    check_step.dependOn(&lib.step);

    // Examples: `zig build example -- <name>`, dispatched from examples/example.zig.
    const example_exe = b.addExecutable(.{
        .name = "example",
        .root_module = b.createModule(.{
            .root_source_file = b.path("examples/example.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    example_exe.root_module.addImport("zevm", lib_mod);

    b.installArtifact(example_exe);
    check_step.dependOn(&example_exe.step);

    const example_run = b.addRunArtifact(example_exe);
    if (b.args) |args| example_run.addArgs(args);

    const example_step = b.step("example", "Run an example (zig build example -- <name>)");
    example_step.dependOn(&example_run.step);
}
