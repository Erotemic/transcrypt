# Transcrypt v3: plaintext, ciphertext, and the formal proof boundary

A **narrated Manim walkthrough** of one protected file crossing from an ordinary
local checkout into public Git history and back, built from the same editable
plans as the offline SVG/HTML storyboard. Inspired by the animation authoring
and evidence-color conventions in the supplied `aivm-secrets/visualizations/`
repository.

The visuals teach the *current experimental implementation* in source snapshot
`861975a` (October 25, 2026), and explicitly identify *design goals* that the
user subsequently set. They are not a substitute for the source, independent
specification, Lean theorems, or cryptographic security analysis. In particular,
no Manim scene simulates the executable or produces new proof evidence.

## Fastest way to inspect or edit (no Manim)

From the Transcrypt repository:

```bash
cd ~/code/transcrypt/visualizations
python3 -m tvis check
python3 -m tvis list
python3 -m tvis preview clean --beat commit
python3 -m tvis gallery
xdg-open .build/storyboard.html
```

The self-contained gallery lets you change **scene** and **beat**, inspect the
current holdings of each component, read the narration, and locate the real
Rust, Lean and documentation sources behind every claim. All SVGs are generated
locally; no server, secret material or external assets are loaded. The `check`
command verifies that named Lean theorems exist in the referenced files,
plans have valid edges and layers, and that evidence sources resolve.

## Render an actual Manim video and interactive presentation

Manim Community 0.19 needs Cairo/Pango and FFmpeg. On Ubuntu, install its
native prerequisites once if they are not already available:

```bash
sudo apt-get install -y libcairo2-dev libpango1.0-dev pkg-config ffmpeg
```

This is an independent
Python authoring environment: it does **not** change Rust, Git configuration,
credentials, Lean, or the cryptographic implementation.

```bash
cd ~/code/transcrypt/visualizations
uv sync --extra manim --extra test
uv run python -m tvis render clean --quality l
uv run python -m tvis render proof --quality l
uv run python -m tvis all --quality l
xdg-open .build/presentation/index.html
```

If you already have Manim in the sibling `aivm-secrets` visualization
virtual environment, you can use that interpreter instead of installing a
second copy:

```bash
make all PYTHON=~/code/aivm-secrets/visualizations/.venv/bin/python QUALITY=l
```

`all` renders each changed scene's MP4 only once and builds a local HTML
presentation that switches between the **Manim video** and editable
**beat-by-beat SVG**. Run `make watch-all PYTHON=.venv/bin/python` to regenerate
clips after scene edits. Try `--quality m` or `h` after reviewing draft renders.
For narration-driven timing, change the `duration`/`hold` in plans and the
`narration` in the TOML storyboard. Video clips are silent so they work equally
well with live narration or a separately recorded TTS track.

## Scenes and evidence levels

| Scene | What it explains | Evidence |
| --- | --- | --- |
| `legend` | Local plaintext, public ciphertext, green and amber boundaries | architecture |
| `selection` | Git attributes and the future arbitrary-pattern policy | implemented + planned |
| `clean` | `git add`: filter, source-derived seal decision, Git index | proof + Git assumption |
| `record` | Exact 22-byte header, SIV tag and content | codec proof + crypto assumption |
| `clone` | Clone, authenticated unlock and hydration | proof + native-effects assumption |
| `attack` | Changed, misplaced or misbound records | conditional protocol proof |
| `inventory` | **Named production Rust functions actually proved** versus lifecycle models | 3 source-derived groups + model |
| `contract` | **Worked `open_record_spec` theorem:** Ok, Authentication failure, other refusals, and `Realizes` premise | conditional source-derived proof |
| `proof` | Rust -> Charon/Aeneas -> Lean vs independent specification | proof and translation assumption |
| `lifecycle` | Proved plan models are not verified native file writes | model proof + A4 |
| `assumptions` | A1/A2 versus A3/A4/A5/A7/A8/A9/A10/A13/A14 | explicit boundary |
| `offline` | Offline threat and intentionally disclosed metadata | accepted limitations |
| `roadmap` | Simple future UX: selected files, persistent unlock, migration | planned, **not** shipped |

**Vocabulary is strict:** `SOURCE-DERIVED PROOF` refers to compiled Lean
statements about production functions; `MODEL PROOF` refers only to a Lean
adapter model; `TESTED` to empirical tests; `TRUSTED PREMISE` to behavior
outside that proof; `DESIGN GOAL` to future functionality. In particular:

- `seal_record_spec` and `open_record_spec` are **conditional** on `Realizes`.
- `V3Primitives`/`Keyed` correctness (A5/A9) and algorithmic security (A10)
  are **not proved by Lean**.
- Git attributes, hooks, OS file writes and the adapter call order (A4/A7/A8)
  are **not end-to-end source-derived proofs**.
- A keyless audit validates *envelope shape*, not cryptographic authenticity.
- The illustrated baseline still restricts protection to `*.secret` and uses
  an in-memory agent. Arbitrary Git patterns and persistent local unlock are
  **vision** scenes, not completed implementation claims.

For a **complete named inventory** and a worked theorem translated into plain English,
read [`PROOF-ATLAS.md`](PROOF-ATLAS.md). The video now has dedicated
`inventory` and `contract` scenes instead of relying on a generic
"formally verified" label.

All canonical facts and caveats are in
`../docs/verification/V3-PROOF-COVERAGE.md`,
`../docs/verification/V3-ASSUMPTIONS.md` and
`../proofs/aeneas/v3/PROOF-STATUS.md`.

## Authoring map

```text
visualizations/
  storyboards/overview.toml        # order, long narration, theorem anchors
  tvis/
    diagram.py                      # Beat, Node, Link, Knowledge, Package
    plans/*.py                     # edit roles, geometry, packets and captions HERE
    scenes/*.py                    # minimal Manim class for each plan
    palette.py                     # semantic status colors, dark and light
    scene_base.py                  # incremental Manim animation engine
    svg_preview.py                 # SVG states from the SAME plans
    gallery.py                     # self-contained HTML storyboard
    presentation.py                # incremental MP4 + HTML compilation
    assets/icons/*.svg             # custom local vector artwork
  tests/test_storyboard.py          # no-Manim authoring/traceability regression
  .build/                          # generated: ignored by Git
```

Keep the scenes grounded in current files. To depict newly implemented
features or changed theorems, update the associated `plans/*.py`, TOML
`sources` and `proof_anchors`, and evidence labels **together**. The catalog
validator will fail if a referenced theorem disappears. Scene proof anchors
are not an exhaustive axiom audit: use the existing named Lean verification
and axiom checks for that.

For noninteractive CI authoring validation:

```bash
cd ~/code/transcrypt/visualizations
python3 -m unittest discover -s tests -p 'test_*.py' -v
python3 -m tvis check
```

No `.build` outputs belong in the overlay or the repository.
