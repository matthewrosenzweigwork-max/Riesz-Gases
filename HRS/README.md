# Fluctuations of Riesz gases

[Mathematical reader](reader/index.html) · [Browse the main paper and supplement](coverage/index.html) · [Reading the evidence](coverage/evidence.html)

The main paper, *Fluctuations, thermalization, and the first correction for periodic log/Riesz dynamics*, and its supplement, *Supplementary material: fluctuation fields and paths under quadratic confinement*, are by Jiaoyang Huang, Matthew Rosenzweig and Sylvia Serfaty. The reader pairs selected mathematical statements with their Lean declarations. Manuscript headings and numbers supply navigation; the Lean statements supply the hypotheses and conclusions.

- [Relaxation on moving windows (§S11)](reader/Relaxation-on-moving-windows/index.html): covariance and cubic-tensor relaxation, the stationary first correction, and five definitions, with exact Lean declarations and the two companion proofs.
- [Lean package](lean/README.md): 11,166 Lean files, including 244 vendored DGRHS modules. The complete original package has 11,184 tracked files. Its [scope note](lean/SCOPE_AND_EVIDENCE.md) documents the earlier comparisons and replays; read it with the [clarifications](coverage/evidence-clarifications.md).
- [Proof supplement](proof-supplement/README.md): the original 31 modules supplying the separate proofs for Supplement Proposition S11.1 and Corollary S11.2, with both exact types checked. The 31 companion modules are unchanged.
- [Documentation sources](blueprint/BUILDING-RAW.md): native Verso documents, portable presentation assembly, and paper-to-source locator.
- [Licensing](LICENSE.md): Apache-2.0 for original HRS software; CC BY 4.0 for original explanatory prose.
- [Third-party sources and notices](THIRD-PARTY.md): vendored Lean adaptations, dependency notices, reader components and fonts. The vendored Lean files are unchanged; three historical license sidecars are included alongside them.

To read offline, the mathematical prose and source index are static. For native search, serve the containing directory over loopback: from the extracted directory containing `Riesz-Gases/`, run `python3 -m http.server --bind 127.0.0.1 8000`, then open `http://127.0.0.1:8000/Riesz-Gases/HRS/reader/`.

[Changes since `hrs-v0.1.0` and targeted checks](lean/CURRENT_SOURCE_CHANGES.md).
