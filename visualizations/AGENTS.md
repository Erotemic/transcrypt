# Visualization authoring rules

The user wants an editable, explanatory Manim animation in the style of the
`aivm-secrets/visualizations` project, not a theorem-count marketing video.

- Explain one real `account.secret` file's lifecycle using real Git filters.
- Each scene records who holds the plaintext, key, record and path; sending a
  copy does not delete it from the sender.
- Use one semantic color per trust role. Green applies only to a precise
  source-derived Lean theorem, not the whole running app. Amber denotes a
  real assumption about cryptographic libraries, Git, OS or translation.
- **Distinguish implemented, proved, modeled, tested, assumed and planned.**
  Never silently promote a planned product feature into an implemented fact.
- Do not imply the Lean development proves AES-SIV, Argon2id, Git, the kernel,
  or the whole runtime adapter.
- Prefer short concrete on-screen captions. Put long TTS-friendly exposition
  in `storyboards/overview.toml`.
- Edit `tvis/plans/*.py` for geometry and beats, not duplicated renderer code.
  Preserve SVG and Manim parity.
- Source the examples from the actual repository. After implementation changes,
  inspect `docs/verification/V3-ASSUMPTIONS.md`, `V3-PROOF-COVERAGE.md`, and
  `proofs/aeneas/v3/PROOF-STATUS.md`. Update anchors and labels accordingly.
- Never load actual secret files or git credential state while rendering.
- Build and check `python3 -m tvis check` and unittest before packaging.
- Manim/FFmpeg output belongs only under ignored `visualizations/.build`.
- Do not describe your own reporting contract inside user-facing reports.
