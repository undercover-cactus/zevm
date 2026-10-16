.PHONY: test check bench bench-era1 download-era1

BLOCKS_PER_FILE := 8192
ERA1_HOST := https://mainnet.era1.nimbus.team
ERA1_DEST := data/era1

test:
	zig build test --summary all

check:
	zig build check --summary all

# Downloads real pre-merge mainnet history (blocks 0..12,959,743, the last
# full file before London at block 12,965,000, covering Berlin) as .era1
# files into data/era1/. Safe to re-run: skips files already downloaded, so
# an interrupted run just picks up where it stopped.
download-era1:
	@mkdir -p $(ERA1_DEST)
	@max_index=$$(( 12959743 / $(BLOCKS_PER_FILE) )); \
	echo "Fetching directory listing..."; \
	listing="$$(curl -sL $(ERA1_HOST)/)"; \
	for i in $$(seq 0 $$max_index); do \
		index=$$(printf "%05d" "$$i"); \
		filename=$$(echo "$$listing" | grep -oE "mainnet-$${index}-[0-9a-f]+\.era1" | head -1); \
		if [ -z "$$filename" ]; then \
			echo "Could not find a file for index $$index in the directory listing" >&2; \
			exit 1; \
		fi; \
		if [ -f "$(ERA1_DEST)/$$filename" ]; then \
			echo "[$$i/$$max_index] already have $$filename"; \
			continue; \
		fi; \
		echo "[$$i/$$max_index] downloading $$filename..."; \
		curl -sL -o "$(ERA1_DEST)/$$filename.tmp" "$(ERA1_HOST)/$$filename"; \
		mv "$(ERA1_DEST)/$$filename.tmp" "$(ERA1_DEST)/$$filename"; \
	done; \
	echo "Done: $$(ls $(ERA1_DEST) | wc -l) files in $(ERA1_DEST)"

# A quick, small-scale sanity check. `bench-era1` below is the real comparison.
bench:
	@echo "=== zevm (ReleaseFast) ==="
	@zig build -Doptimize=ReleaseFast
	@zig-out/bin/example sync 2>&1 | tail -1
	@echo ""
	@echo "=== revm (release) ==="
	@cd rzevm && cargo run --release --example sync 2>/dev/null | tail -1

# The real comparison: 4,366,336 real historical mainnet blocks. Run `make download-era1` first.
bench-era1:
	@echo "=== zevm (ReleaseFast) ==="
	@zig build -Doptimize=ReleaseFast
	@zig-out/bin/example sync_era1 2>&1 | tail -6
	@echo ""
	@echo "=== revm (release) ==="
	@cd rzevm && cargo run --release --example revm_sync_era1 2>/dev/null | tail -5
	@echo ""
	@echo "=== zevm via Rust FFI (release) ==="
	@cd rzevm && cargo run --release --example sync_era1 2>/dev/null | tail -6
