# Private styled reader assembly

This mixed-source pipeline preserves the accepted editorial baseline and regenerates the eight whole-space and seven S11 cards. It does not claim that raw Verso alone regenerates the earlier curated chapters.

## Build without private host paths

Requires Python 3 with lxml and Node.js. Tested with Python 3.12.3. KaTeX is vendored. No network, native build directory or Lean compilation is needed for this presentation step.

```sh
python3 /path/to/HRS/blueprint/presentation/build_styled.py \
  --tree /path/to/HRS \
  --output /new/location/HRS
```

The output must not exist. This scoped documentation bundle contains `reader/` and the selected frozen Lean files beneath `lean/`, plus the separate manifest-verified proof supplement. Serve the common HRS parent so source links work. It is not the full Lean release; composing that release retains the entire immutable Lean tree.

Coverage is opt-in: add `--with-coverage`. The builder copies coverage and every linked Lean file only after checking `lean/MANIFEST/SHA256SUMS_included_files.txt`, whose bytes are locked. An optional `--lean-manifest` accepts sha256sum rows or a JSON mapping from paths relative to lean/ to frozen SHA256 values. Without coverage mode neither the coverage directory nor its link is emitted.

## Explicit inputs

- `baseline/`: frozen, reviewed editorial HTML, native-document/source copies, tooltips and assets. These curated inputs are copied and navigationally adapted, not falsely described as regenerated prose.
- `compact-base.html`: frozen accepted reading-copy styles; its body is not the generated chapter.
- `equilibrium-and-paths.json`, `preparation-and-fields.json`, `conventions.md`: independently reviewed mathematical prose and exact Lean signature/proof strings.
- `render_headlines.py`, `mathml_variants.py`, `katex.js`: regenerate the eight cards, strict TeX/MathML, section-scoped equation numbers and accessible source/proof disclosures.
- `native-handoff/`: sanitized canonical data extracted from the verified native render. Only eight declaration bindings, ordered TeX, public aliases, source hashes, and 80 compiled search assets are retained. No private paths, native caches or raw rendered metadata are shipped.
- `notices/`: upstream third-party license texts and artifact provenance, including all 60 KaTeX font files. This selects no license for HRS.
- `INPUTS.json`: binds all presentation/native-handoff and relevant frozen document/Lean inputs. Changed inputs fail closed. Lock refresh is an explicit review step.

The whole-space cards' exact signatures and proofs are checked against frozen Lean. Each card's ordered TeX and declaration identity, plus all 419 TeX spans in order, must equal the canonical native data. Native search and all shards are integrated separately; baseline tooltip namespaces remain intact. All HTML references/fragments, search destinations and private-path leaks are checked. Receipts stay outside the reader output.

## Refreshing the original whole-space native handoff

The original whole-space handoff uses six baseline documents plus Headline, HeadlineContents and MainHeadline. The S11 extension adds three more modules; its separate workflow is linked below. Follow the separate raw-build instructions. A successful compiler/render receipt must be established independently before claiming that a raw input is genuine.

```sh
python3 /path/to/presentation/extract_native_handoff.py \
  --tree /path/to/HRS --raw /path/to/verified/html-multi \
  --verify-against /path/to/presentation/native-handoff \
  --output /new/canonical-handoff
```

This whitelist extractor ignores irrelevant host metadata but rejects any difference in the canonical mathematical bindings, ordered formulas, aliases or search payload. Initial extraction instead requires `--verified-raw-lock` with the independently verified raw SHA256 inventory. That private inventory is not needed or shipped for ordinary assembly. Legitimate changed mathematics requires a new fidelity review and explicit lock update.

## Verification and remaining boundary

Default assembly was tested after physically relocating its inputs, with no raw native directory argument. All 364 scoped output files, including S11 and the proof supplement, were byte-identical to the original-path assembly. A changed ordered formula was rejected; unrelated host metadata produced identical canonical data. This is not a relocated native compiler build or cold HRS proof replay.

Offline Chrome checked six widths 320–1920, open/closed disclosures, forced colors, keyboard math panning and eight named search queries at a genuine `/Riesz-Gases/HRS/` prefix. Screenshots at 320 and 1280 were visually reviewed. Search had no external requests or JavaScript errors; the sole missing request was the browser's unrelated favicon. The original whole-space chapter test had none. S11 was independently checked at the same six widths, with 24 open/closed and forced-color states, minimum observed text contrast 8.6:1, working keyboard math scrolling, and visually reviewed screenshots at 375 and 1280 pixels. Its only missing request was the unrelated favicon.

Full source regeneration of the old editorial baseline remains separate work. The third-party inventory records exact npm matches where established and does not invent a version for the Verso-compiled Unicode Input Component. Elasticlunr and Fuzzysort are documented vendored variants. Blueprint's source headers explicitly state Apache 2.0 although its pinned repository lacks a root LICENSE file. No publication, permission change, project-license choice or additional HRS proof build is performed.

## Section S11 overlay

When `../s11/content.json` is present, assembly also regenerates the seven S11 cards, copies the manifest-verified companion proof supplement, and installs the separately pinned native search handoff before link validation. Coverage mode copies all source viewers and their referenced source files; without coverage, S11 source links point directly to files. See [the S11 workflow](../s11/README.md). Earlier curated editorial inputs remain frozen. Neither this overlay nor its documentation compilation is a new HRS proof build.

## Manuscript navigation overlay

`navigation.py` applies the manuscript order from `manuscript-navigation.json`
after the original editorial baseline, whole-space cards, and S11 chapter are
assembled. It preserves historical URLs and anchors, mathematical expressions,
and source code, while suppressing the independent reader ordinals in headings,
Blueprint labels, and navigation. The main manuscript, its appendices, and the
supplement retain their own labels. With `--with-coverage`, section destinations
are the coverage section pages; scoped builds use the same section anchors in
the reader paper index. Feature links return to these sections. The overlay also
adds the corresponding feature links to coverage pages, idempotently; the frozen
locator generator and baseline remain historical inputs. `search_labels.py`
changes only search display templates, not native index records or destinations.
Both overlays run before all link and search-destination checks.
