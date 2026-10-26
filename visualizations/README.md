# Transcrypt v3: plaintext, ciphertext, and the formal proof boundary

A **narrated Manim walkthrough** of one protected file crossing from an ordinary
local checkout into public Git history and back, built from the same editable
plans as the offline SVG/HTML storyboard. Inspired by the animation authoring
and evidence-color conventions in the supplied `aivm-secrets/visualizations/`
repository.

The visuals teach the *current experimental implementation* in source snapshot
`88001fd` (October 25, 2026). The previous storyboard was authored before
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

## Fast Makefile workflow: one clip or PDF, no full render

The default `make` target prints help instead of starting all Manim scenes.
The layout follows the supplied DKPS visualization project's separation of
**scene rendering** from **no-render deck/handout export**. Run `make setup`
once to install dependencies in `visualizations/.venv`; subsequent Makefile
commands use `uv run --no-sync python` to avoid resolving/syncing extras on
every quick edit, even when another virtual environment is active.

```bash
cd ~/code/transcrypt/visualizations
make list
make preview SCENE=unlock BEAT=store   # instant SVG preview; no Manim
make scene SCENE=unlock QUALITY=l       # one scene's beat clips, cached
make focus SCENE=unlock QUALITY=l       # one scene + focused click-through HTML
make pdf                                # all 22 static slides; no Manim
make pdf SCENE=unlock                   # one scene's slides only
make pdf SLIDE=sealing                  # one specific slide only
make pdf SCENES="clean crypto"          # selected scenes in deck order
make html                               # beat-by-beat slideshow, no Manim
make standalone                         # portable HTML with beat MP4s embedded
```

A targeted `make scene` renders a single Manim scene with `--save_sections`,
then publishes a separate MP4 **for each named beat** under
`.build/presentation/videos/sections/<scene>/`. The complete MP4 is retained
for the technical inspector, but the HTML slideshow uses the beat clips, never
a full-scene player. The fingerprint manifest is shared with `make all`; an
unchanged scene is reused. `make focus SCENE=unlock` also exports a focused
`index-unlock.html` without generating the other scenes. To force Manim to run again for that
scene, use `make scene SCENE=unlock FORCE=1`; `NO_CACHE=1` additionally disables
Manim's internal partial-movie cache if investigating stale frames.
`make still` and `make segment SCENE=unlock ANIMATION=0,2` render partial
material without publishing it as a complete scene video.

**PDF export never renders Manim**: it draws the precise selected static beats
from the authored plan. `make pdf` does not build HTML, the technical inspector,
or a video. It takes about a few seconds rather than rendering the full scene catalog.
A filtered export writes separate filenames, e.g.
`.build/presentation/presentation-unlock.pdf` or
`.build/presentation/presentation-sealing.pdf`, preserving the full
`presentation.pdf`. `make html SCENE=unlock` similarly writes
`index-unlock.html`. Filtered exports keep the order of
`storyboards/presentation.toml`; one scene can have multiple slides.

For the entire movie-and-deck build, explicitly run `make all QUALITY=l`.
The individual clips already staged with `make scene` are reused by `make all`
when their source fingerprints and render settings match. A full build can
still take time; it is not needed to evaluate a single scene or a PDF change.

`SCENE`, `SCENES`, `SLIDE`, and `SLIDES` work for `pdf`, `html`,
`standalone`, and `present` (with `SCENES`/`SLIDES` taking priority in the
Makefile if multiple filters are given). Use `make check` and `make test` for
non-Manim validation. `PYTHON=.venv/bin/python` can override the default runner.

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
make scene SCENE=unlock QUALITY=l
make scene SCENE=clean QUALITY=l
make scene SCENE=crypto QUALITY=l
make html
make pdf
# Optional and slower: compile the rest of the clips and complete presentation
make all QUALITY=l
xdg-open .build/presentation/index.html
xdg-open .build/presentation/presentation.pdf
```

If you already have Manim in the sibling `aivm-secrets` visualization
virtual environment, you can use that interpreter instead of installing a
second copy:

```bash
make all PYTHON=~/code/aivm-secrets/visualizations/.venv/bin/python QUALITY=l
```

`all` renders each changed scene's beat sections only once and builds a **22-slide
HTML presentation plus a 16:9 PDF**, speaker notes, and a separate technical
storyboard inspector. Each HTML click advances precisely one named operation
beat. It plays that beat's Manim section automatically and holds the final
frame until the next click; there is **no video Play button**. Missing beat
videos fall back to the plan-derived SVG snapshots with identical navigation.
The PDF uses SVG-derived static key beats and, for video slides, a link to the
corresponding HTML slide. PDF readers do not consistently support playable
embedded movies.

The presentation is authored independently from the source inspector:

```bash
# No Manim needed: a usable static slide deck now, or refresh after an edit
python3 -m tvis present --format both

# With already-rendered beat MP4s: a portable HTML presentation
# with each section inlined once (and no separate MP4 files required)
python3 -m tvis present --format both --embed-videos
xdg-open .build/presentation/embedded.html

# Or the small HTML with relative videos/sections/<scene>/*.mp4 sidecars:
xdg-open .build/presentation/index.html

# Browse every animated beat, per-operation basis, and provenance separately:
xdg-open .build/presentation/storyboard.html
```

`--embed-videos` is optional: it base64-encodes each available **beat section**
once and can produce a large HTML file. These sections are generated via
Manim's built-in `next_section` / `--save_sections` support, not a new render
pass or separate video-cutting job. `index.html`, `presentation.pdf`, `speaker-notes.md`
and `storyboard.html` are always colocated in `.build/presentation/`. To share
`index.html` with real video, copy its `videos/` directory too. To share one
file, copy `embedded.html`. The PDF is static, but when viewed alongside the
HTML its movie-slide captions link to the appropriate HTML slide (some local
PDF viewers restrict opening file links).

**Presentation controls:** click anywhere on a slide, press Right, or press
Space for the next beat. Left returns to the previous completed beat;
Shift+Right/Left skips a slide; R replays the current beat; N toggles speaker
notes. Per-operation evidence and input/output transformations update with
each beat. Plain SVG steps remain fully navigable without Manim. The PDF is
intentionally a static one-page-per-authored-slide companion, not a collection
of paused video segments.

Run `make watch-all` to regenerate clips after scene edits (this is a full-deck watcher). Try `--quality m` or `h` after reviewing draft renders.
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
| `status` | V0-V7 / P0-P6 roadmap progress with per-node evidence | internal gates complete, external R-01 pending |
| `inventory` | actual production theorems versus model theorems | exact Lean proof inventory |
| `contract` | worked `open_record_spec` | `Realizes` hypothesis visible |
| `proof` | Rust -> Charon/Aeneas -> Lean | A3 translation soundness |
| `lifecycle` | indexed record -> core -> Lean plan -> OS effects | source, model and tested are separate |
| `adapter` | Git replies -> proved parser -> A4 input facts -> proved seal decision | tests of inputs are not proof of caller correspondence |
| `assumptions` | trust boundary ledger | A3/A4/A5/A7/A8/A13/A19 |
| `offline` | ciphertext metadata observed publicly | accepted information leakage |
| `roadmap` | **remaining assurance work**, not already-delivered features | adapter correspondence, crypto audit, deployment |

The current source already implements and tests generic Git-attribute patterns,
path-rebound renames, one-time v2 migration, and persistent **stored-key unlock
by default** (with `--private` as an optional memory-only mode). None is an
end-to-end Lean theorem about Git or the OS.

The verification update adds `status` and `adapter` scenes and two slides
(`milestones`, `adapter-correspondence`). Render them individually while
reviewing proofs rather than rebuilding every animation:

```bash
make preview SCENE=status BEAT=review
make preview SCENE=adapter BEAT=provenance
make pdf SLIDE=milestones
make pdf SLIDE=adapter-correspondence
make focus SCENE=adapter QUALITY=l
make html SCENE=status
```

The milestones slide distinguishes V0-V5 achieved, V6 internally reviewed with
R-01 still open, V7 deferred, and product P0-P5 done/P6 pending. The adapter
scene shows why proving `parse_attr_response_spec`, `is_object_id_spec` or
`seal_action_spec` does **not** discharge Git input provenance, stored-key
loading, or native OS effects. Optional remote enforcement is a deployment
choice, not an uncompleted local core proof.

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
    slide_deck.py                  # heterogeneous HTML with click-driven beats
    beat_media.py                  # stage/validate one Manim section per beat
    pdf_slides.py                  # paged 16:9 static PDF with video-slide links
    assets/presentation.css        # slide templates / styles
    assets/presentation.js         # offline stepper: click/arrow/Space to next beat
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
`split` default to animated beat clips when staged. Any layout can opt in to
`media = "video"` for beat playback. Set `steps = "single"` to hold one
named beat (`beat = "..."`) or `steps = "all"` to advance through the whole
scene. Defaults: video media steps through all beats; diagram media stays on
one. Cover, evidence, and conclusion slides keep their independent layouts. You can show the same scene on
multiple slides with different beat/poster/layout choices without duplicating
assurance prose. To edit proof claims, modify the scene's `plans/*.py` and the
source-anchored `overview.toml`, **not** slide text alone. Both HTML and PDF
read the same operation `Evidence` objects. The `check` command validates that
each slide points to a real scene and named beat.

No `.build` outputs belong in the overlay or the repository.
