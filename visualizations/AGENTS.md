# Visualization authoring rules

The user wants an editable, explanatory Manim animation in the style of the
`aivm-secrets/visualizations` project, not a theorem-count marketing video.

- Explain a concrete selected file's lifecycle using real Git filters; `account.secret` is just an example, not a hardcoded selection rule.
- Each scene records who holds the plaintext, key, record and path; sending a
  copy does not delete it from the sender.
- Use one semantic color per trust role. Green applies only to a precise
  source-derived Lean theorem, not the whole running app. Amber denotes a
  real assumption about cryptographic libraries, Git, OS or translation.
- Encode each operation's evidence as its own `Evidence` badge with a grounded theorem/assumption; a payload color never implies proof.
- Use typed packet kinds and an active `Processing` input/output step; a decision is not an OS write.
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
- `storyboards/presentation.toml` chooses per-slide format (`cover`, `cinema`,
  `split`, `diagram`, `evidence`, `statement`) and exact scene/beat still. It is
  distinct from `overview.toml` (truth/narration) and `plans` (geometry/evidence).
- HTML video only reflects Manim output if the file exists. Never synthesize
  fake security execution footage. The fully inlined HTML variant embeds MP4
  bytes; the default version uses movable relative sidecars.
- PDF contains faithful SVG stills, not universally playable movies. It must
  label video playback as a link to the companion HTML and never imply that a
  PDF link is a security proof.
- Maintain visual/tier parity across Manim, SVG, HTML and PDF. Test a static
  no-Manim export plus a video-embedding scenario, and render-check the PDF.
- For routine iteration, use `make preview SCENE=...`, `make scene SCENE=...`,
  or `make pdf`/`make pdf SLIDE=...`. Do not run `make all` just to validate
  one scene or a static PDF; preserve Manim partial-movie caches.
- Publishing a scene to HTML requires a *complete* MP4, never a `--still` or
  `--animation` fragment. PDF-only exports must not regenerate gallery or HTML.
- Do not describe your own reporting contract inside user-facing reports.

## Interactive presentation rule

The HTML presentation must behave as a click-to-advance slide show, not a
monolithic video player. Keep the named beats from `Diagram.beats` as actual
Manim `next_section` boundaries. `make scene SCENE=<id>` stages only that
scene's section MP4s; HTML automatically plays the selected beat section on
advance and freezes at its final frame. If section media is missing or stale,
use exact per-beat SVG states with the same keyboard/click navigation. PDF
export remains static and must never invoke Manim.
