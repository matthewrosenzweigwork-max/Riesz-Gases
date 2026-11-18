# Section S11 reader overlay

`content.json` supplies the reviewed mathematical text. `render_s11.py` generates the static chapter, exact source excerpts, native document sources and navigation links. The two theorem specifications are displayed as admitted declarations, alongside their separate, exact-type companion proofs. The five definitions are displayed verbatim from the frozen source. Reader equations have their own labels `(S11.1)` through `(S11.9)`; these are not additional manuscript result numbers.

## Reproduce the complete reader

Use the existing presentation builder from any directory:

```sh
python3 /path/to/HRS/blueprint/presentation/build_styled.py \
  --tree /path/to/HRS --output /new/path/HRS --with-coverage
```

The output directory must not exist. The builder first assembles the earlier reader, copies the manifest-verified source files and proof supplement, applies the S11 overlay, installs its pinned native search handoff, then validates local links and search destinations. Omitting `--with-coverage` produces a scoped reader with direct source-file links rather than missing source viewers. This remains a documentation bundle, not the complete Lean release.

To revise the extracted full candidate in place, preserve its original archive and run:

```sh
python3 /path/to/HRS/blueprint/s11/render_s11.py --tree /path/to/HRS
python3 /path/to/HRS/blueprint/s11/install_native_search.py --tree /path/to/HRS
python3 /path/to/HRS/blueprint/s11/validate_s11.py --tree /path/to/HRS
```

Rendering restores the chapter, so always reinstall native search aliases after rendering. The content and generator are bound by the presentation input lock. Reviewed changes require updating that lock explicitly; the builder never silently refreshes it.

## Native documentation scope

The native S11 sources are `S11.lean`, `S11Contents.lean`, and `MainS11.lean`. They accompany the six baseline and three whole-space modules. The twelve documentation modules compiled and rendered successfully with Lean 4.34.1 and the pinned renderer, using existing HRS and renderer library caches. No HRS module was compiled, and no Lake build or proof replay was run.

For a new native documentation run, assemble all twelve `.lean` documents into a fresh source directory and use `build_raw_native.py` with the six additional modules in this order: `Headline`, `HeadlineContents`, `MainHeadline`, `S11`, `S11Contents`, `MainS11`; set `--entry-module MainS11`. Follow `../BUILDING-RAW.md` for dependency/toolchain checks. Keep raw native output private; it may carry host-specific compiler metadata and unprocessed status badges. The static chapter uses distinct admitted-declaration and companion-proof labels and does not borrow a proof badge from the native specification binding.

## Checks

The overlay preserves all 97 authored TeX spans and nine exact source excerpts. The static page has no external assets or scripts. Tests cover local source/anchor links, ordered equation labels, responsive layouts, contrast, forced colors and keyboard horizontal scrolling. The cubic-tensor link opens the existing three-term formula in the whole-space chapter, including its enclosing notation disclosure.
