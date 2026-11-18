# Native documentation build

The raw generator compiles the six baseline Verso documents; the three additional documentation modules are `Headline`, `HeadlineContents` and `MainHeadline`. For the nine-module candidate, assemble them in an empty source directory, then run the driver from any directory:

```sh
D=/path/to/HRS/blueprint
mkdir "$WORK/doc-sources"
cp "$D"/*.lean "$D"/candidate-headlines/*.lean "$WORK/doc-sources/"
python3 "$D/build_raw_native.py" --renderer-root "$LOCAL_RENDERER" \
  --hrs-root "$BUILT_HRS" --lean "$INSTALLED_LEAN/bin/lean" \
  --docs-root "$WORK/doc-sources" --extra-module Headline \
  --extra-module HeadlineContents --extra-module MainHeadline \
  --entry-module MainHeadline --timeout-seconds 900 --output "$WORK/new-raw"
```

The output path must be new and outside all source roots. This uses a locally installed pinned Lean toolchain and already-compiled HRS and renderer dependencies. The driver checks the package manifests, revisions and tracked source state. It compiles documentation, never the base formalization. Existing cache provenance must be established separately.

The native output can contain compiler provenance, absolute paths and external asset references; it is a build intermediate. Use the [presentation builder](presentation/README.md) for the reader. Its sanitized native handoff binds the eight declaration cards, ordered mathematics, public anchors and search assets. The older editorial chapters are preserved as reviewed inputs. Reassembling the finished reader from those inputs works without a raw compiler work directory or network access.

No document build constitutes a proof replay or an independent-statement comparison.
