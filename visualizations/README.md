# Transcrypt v3: plaintext, ciphertext, and the formal proof boundary

A **narrated Manim walkthrough** of one protected file crossing from an ordinary
local checkout into public Git history and back, built from the same editable
plans as the offline SVG/HTML storyboard. Inspired by the animation authoring
and evidence-color conventions in the supplied `aivm-secrets/visualizations/`
repository.

The visuals teach the *current experimental implementation* in source snapshot
`16cc957` (October 25, 2026). The previous storyboard was authored before
Git-attribute patterns and default stored-key unlock were implemented. They are not a substitute for the source, independent
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
current holdings of each component, see an operation-by-operation trust/evidence
register with exact theorem names or A-number assumptions, and locate the real
Rust, Lean and documentation sources behind every claim. All SVGs are generated
locally; no server, secret material or external assets are loaded. The `check`
command verifies that named Lean theorems exist in the referenced files,
plans have valid edges and layers, and that evidence sources resolve. Per-operation Lean badges are also checked
against theorem declarations in the scene's referenced Lean source files.

## Render Manim and export a full HTML/PDF presentation

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
uv sync --extra manim --extra presentation --extra test
uv run python -m tvis render unlock --quality l
uv run python -m tvis render clean --quality l
uv run python -m tvis render crypto --quality l
uv run python -m tvis all --quality l
xdg-open .build/presentation/index.html
xdg-open .build/presentation/presentation.pdf
```

If you already have Manim in the sibling `aivm-secrets` visualization
virtual environment, you can use that interpreter instead of installing a
second copy:

```bash
make all PYTHON=~/code/aivm-secrets/visualizations/.venv/bin/python QUALITY=l
```

`all` renders each changed scene's MP4 only once and builds a **20-slide
HTML presentation plus a 16:9 PDF**, speaker notes, and a separate technical
storyboard inspector. The HTML slides use genuine Manim MP4s when they exist;
missing videos fall back to plan-derived SVG diagrams, never invented motion.
The PDF uses SVG-derived static key beats and, for video slides, a link to the
corresponding HTML slide. PDF readers do not consistently support playable
embedded movies.

The presentation is authored independently from the source inspector:

```bash
# No Manim needed: a usable static slide deck now, or refresh after an edit
python3 -m tvis present --format both

# With already-rendered MP4s: ALSO generate a single, portable HTML file
# with the actual video bytes inlined, rather than relying on MP4 sidecars
python3 -m tvis present --format both --embed-videos
xdg-open .build/presentation/embedded.html

# Or the standard small HTML with relative videos/*.mp4 sidecars:
xdg-open .build/presentation/index.html

# Browse every animated beat, per-operation basis, and provenance separately:
xdg-open .build/presentation/storyboard.html
```

`--embed-videos` is optional: it base64-encodes each available MP4 once and can
produce a large HTML file. `index.html`, `presentation.pdf`, `speaker-notes.md`
and `storyboard.html` are always colocated in `.build/presentation/`. To share
`index.html` with real video, copy its `videos/` directory too. To share one
file, copy `embedded.html`. The PDF is static, but when viewed alongside the
HTML its movie-slide captions link to the appropriate HTML slide (some local
PDF viewers restrict opening file links).

Run `make watch-all PYTHON=.venv/bin/python` to regenerate clips after scene edits. Try `--quality m` or `h` after reviewing draft renders.
For narration-driven timing, change the `duration`/`hold` in plans and the
`narration` in the TOML storyboard. Video clips are silent so they work equally
well with live narration or a separately recorded TTS track.

## Data flow and trust encoding

Two **independent** visual channels are used:

1. **Moving tokens show what data moves**: `PLAIN` (local plaintext), `RECORD`
   (encrypted wire object), `KEY`, `PATH`, `DATA` (metadata), and `RESULT`
   (a decision, *not* an already performed OS effect). The active operation
   also displays a typed **input -> output** transformation beneath it.
2. **Badges beneath executable operations show its evidence tier**. This badge
   does not extend to a caller, a remote, or an entire lifecycle scene.

| Badge | Meaning | Example |
| --- | --- | --- |
| `LEAN: SOURCE PROOF` | A source-derived theorem names the actual extracted Rust function | `lock_action_spec`, `record_envelope_ok_spec` (shape only) |
| `LEAN: IF REALIZES` | Source-derived theorem requires an external primitive contract | `seal_record_spec`, `open_record_spec`, `authenticate_config_spec` |
| `LEAN: MODEL ONLY` | Proved Lean sequencing model, **not** the native adapter | `hydratePlan_spec` |
| `TESTED: NO PROOF` | Runtime adapter covered by tests/reviews, not source-derived proof | actual Git filter/Unix writer A4/A8 |
| `TRUSTED: CRYPTO` | Externally supplied cryptographic library/assumptions; tested but not proved in Lean | RustCrypto, Argon2id, AES-SIV A5/A9/A10 |
| `TRUSTED: GIT / OS` | Git and OS semantics, hook deployment or translation premise | A3/A7/A13/A19 |
| `IN CODE: NO PROOF` | Implemented without source-derived proof | general utility action |
| `DESIGN GOAL` | Not yet implemented; never promoted to a theorem | future adapter refinement |

Each proof badge has a **specific theorem name**; the storyboard validator
checks it against the scene's Lean source references. Amber is not a judgment
that an operation is insecure. It indicates a required external premise.

## Lifecycle scenes

| Scene | Data and operation | Important boundary |
| --- | --- | --- |
| `legend` | Typed tokens versus evidence badges | no blanket green boundary |
| `selection` | patterns -> Git verdict -> raw path | Git A19 versus proved parser |
| `unlock` | passphrase -> Argon2id -> config authentication -> stored key | external KDF, conditional core, native storage A17 |
| `clean` | local plaintext -> filter -> core -> Git index | adapter A4 and conditional seal |
| `crypto` | seal preconditions -> AES-SIV -> header/record | trusted RustCrypto versus Lean codec |
| `record` | public record 22-byte header, tag and encrypted body | codec proof versus crypto assumption |
| `rename` | old path -> decision -> resealed new-path record | proved `seal_action` versus tested Git move A18 |
| `audit` | committed bytes -> keyless shape -> auditor -> remote | no keyless authenticity; deployment A13/A14 |
| `clone` | public ciphertext -> authenticated open -> local plaintext | conditional core versus native writer |
| `lock` | local plaintext -> checked flush -> ciphertext -> forget key | `lock_action` proof versus filesystem/key deletion |
| `attack` | tampered ciphertext -> gate -> rejection or actual publication | conditional authentication, A10 |
| `inventory` | actual production theorems versus model theorems | exact Lean proof inventory |
| `contract` | worked `open_record_spec` | `Realizes` hypothesis visible |
| `proof` | Rust -> Charon/Aeneas -> Lean | A3 translation soundness |
| `lifecycle` | indexed record -> core -> Lean plan -> OS effects | source, model and tested are separate |
| `assumptions` | trust boundary ledger | A3/A4/A5/A7/A8/A13/A19 |
| `offline` | ciphertext metadata observed publicly | accepted information leakage |
| `roadmap` | **remaining assurance work**, not already-delivered features | adapter correspondence, crypto audit, deployment |

The current source already implements and tests generic Git-attribute patterns,
path-rebound renames, one-time v2 migration, and persistent **stored-key unlock
by default** (with `--private` as an optional memory-only mode). None is an
end-to-end Lean theorem about Git or the OS.

For the **complete named proof inventory** and a worked `open_record_spec`
statement, see [`PROOF-ATLAS.md`](PROOF-ATLAS.md).
Authoritative source facts: [`V3-PROOF-COVERAGE.md`](../docs/verification/V3-PROOF-COVERAGE.md),
[`V3-ASSUMPTIONS.md`](../docs/verification/V3-ASSUMPTIONS.md), and
[`PROOF-STATUS.md`](../proofs/aeneas/v3/PROOF-STATUS.md).

## Authoring map

```text
visualizations/
  storyboards/overview.toml        # scene catalog, long narration, theorem anchors
  tvis/
    diagram.py                      # Beat, Evidence, Processing, Node, Knowledge, Package
    plans/*.py                     # edit roles, trust tiers, typed packets and transformations HERE
    scenes/*.py                    # minimal Manim class for each plan
    palette.py                     # colors for payload roles and independent trust badges
    scene_base.py                  # incremental Manim animation engine
    svg_preview.py                 # SVG states from the SAME plans
    gallery.py                     # technical beat-by-beat SVG/HTML inspector
    slide_deck.py                  # heterogeneous full-slide HTML, video inlining
    pdf_slides.py                  # paged 16:9 static PDF with video-slide links
    assets/presentation.css        # slide templates / styles
    assets/presentation.js         # offline arrow-key/media navigation
    presentation.py                # incremental MP4 + HTML/PDF compilation
  storyboards/presentation.toml   # page order/layout (different for EACH slide)
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

### Editing the actual deck

`storyboards/presentation.toml` is the presentation editor. It selects the
`scene`, **named** `beat` for the static poster/PDF, a slide-specific `layout`,
and concise `points` for the stage. Available layouts are:

| Layout | What it displays |
| --- | --- |
| `cover` | Big framing title plus a still |
| `cinema` | Large Manim video (or exact SVG poster), small caption strip |
| `split` | Motion/diagram beside short explanation and operation evidence |
| `diagram` | Larger static visual with a compact takeaway |
| `evidence` | Per-operation proof/trust cards; no invented blanket guarantee |
| `statement` | Text-led framing, conclusions, limits and next steps |

A `split` slide can use `media = "diagram"` to suppress animation; `cinema`/
`split` default to video when the clip exists. You can show the same scene on
multiple slides with different beat/poster/layout choices without duplicating
assurance prose. To edit proof claims, modify the scene's `plans/*.py` and the
source-anchored `overview.toml`, **not** slide text alone. Both HTML and PDF
read the same operation `Evidence` objects. The `check` command validates that
each slide points to a real scene and named beat.

No `.build` outputs belong in the overlay or the repository.
