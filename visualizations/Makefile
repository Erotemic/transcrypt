# Fast local visualization builds. Run from visualizations/.
#
#   make                       # help, NOT an all-scenes render
#   make list                  # valid scene IDs and their source files
#   make preview SCENE=unlock BEAT=store  # instant SVG, no Manim
#   make scene SCENE=unlock     # just this scene's beat MP4s, cached
#   make scene SCENE=unlock FORCE=1   # force rerender of this one scene
#   make focus SCENE=unlock     # render one scene's beats, generate focused HTML
#   make still SCENE=unlock    # one static Manim frame; no presentation export
#   make pdf                   # full static PDF, NO Manim, HTML or inspector
#   make pdf SCENE=unlock      # PDF of only this scene's presentation slides
#   make pdf SLIDE=sealing     # PDF of one named presentation slide
#   make pdf SCENES="clean crypto"  # PDF of selected scenes, in authored order
#   make html                  # HTML using already staged MP4s; no Manim
#   make standalone            # portable HTML, embedding staged MP4s; no Manim
#   make present               # HTML and PDF, no Manim
#   make all                   # explicitly render changed videos + full deck
#
# PDF/HTML selections have distinct filenames and never replace the full deck.
# Manim keeps its partial-movie cache for quicker re-renders; NO_CACHE=1 disables it.

.DEFAULT_GOAL := help
UV      ?= uv
# Use the project's .venv even when a different virtualenv is activated.
# `make setup` once to install optional render/export dependencies.
PYTHON  ?= $(UV) run --no-sync python
SCENE   ?=
SCENES  ?=
SLIDE   ?=
SLIDES  ?=
BEAT    ?= last
QUALITY ?= l
THEME   ?= dark
SPEED   ?= 1
FORCE   ?= 0
OPEN    ?= 0
NO_CACHE ?= 0
FORMAT  ?= both
EMBED   ?= 0

ONE_SCENE := $(if $(strip $(SCENE)),$(SCENE),clean)
# The multi-selection variables override the single-selection variables.
SELECT := $(if $(strip $(SCENES)),--scenes $(SCENES),$(if $(strip $(SLIDES)),--slides $(SLIDES),$(if $(strip $(SLIDE)),--slide $(SLIDE),$(if $(strip $(SCENE)),--scene $(SCENE)))))
RENDER_OPTS := --quality $(QUALITY) --theme $(THEME) --speed $(SPEED) \
               $(if $(filter 1,$(FORCE)),--force) \
               $(if $(filter 1,$(OPEN)),--open) \
               $(if $(filter 1,$(NO_CACHE)),--no-cache)

.PHONY: help setup list check test preview gallery storyboard scene focus render still segment pdf html standalone present all watch-all

help:
	@echo 'Fast Transcrypt visualization targets (run from visualizations/):'
	@echo '  make list                         list scene IDs'
	@echo '  make preview SCENE=unlock BEAT=store   fast SVG beat (no Manim)'
	@echo '  make scene SCENE=unlock           one scene and its beat MP4s, reuse if current'
	@echo '  make scene SCENE=unlock FORCE=1   rerender even when inputs are unchanged'
	@echo '  make focus SCENE=unlock           stage one scene and its HTML slideshow'
	@echo '  make still SCENE=unlock           one Manim still (not published)'
	@echo '  make segment SCENE=unlock ANIMATION=0,2   render a subset of plays'
	@echo '  make pdf                          entire PDF only; no Manim/HTML/inspector'
	@echo '  make pdf SCENE=unlock             PDF with only unlock slides'
	@echo '  make pdf SLIDE=sealing            PDF with one named slide'
	@echo '  make pdf SCENES="clean crypto"     PDF with selected scenes'
	@echo '  make html                         click-through beat slideshow (no Manim)'
	@echo '  make standalone                   portable slideshow with beat MP4s inline'
	@echo '  make present                      HTML + PDF + source inspector, no Manim'
	@echo '  make all                          explicitly refresh all changed MP4s + deck'
	@echo '  make setup                        install optional Manim/PDF/test dependencies'
	@echo 'Variables: QUALITY=l|m|h|p  THEME=dark|light  SPEED=1  FORCE=0|1'
	@echo '           PYTHON="uv run --no-sync python" (override for another environment)'
	@echo '           SCENE/SCENES/SLIDE/SLIDES select PDF/HTML slides; omit for entire deck'

setup:
	$(UV) sync --extra manim --extra presentation --extra test

list:
	$(PYTHON) -m tvis list

check:
	$(PYTHON) -m tvis check

test:
	$(PYTHON) -m unittest discover -s tests -p 'test_*.py' -v

preview:
	$(PYTHON) -m tvis preview $(ONE_SCENE) --beat $(BEAT) --theme $(THEME)

gallery:
	$(PYTHON) -m tvis gallery --theme $(THEME)

storyboard:
	$(PYTHON) -m tvis storyboard

scene:
	$(PYTHON) -m tvis render $(ONE_SCENE) --publish $(RENDER_OPTS)

# One command to rebuild a focused beat-by-beat presentation. No other scenes.
focus:
	@test -n "$(SCENE)" || (echo 'Supply SCENE=<id>, e.g. make focus SCENE=unlock' >&2; exit 2)
	$(MAKE) scene SCENE=$(SCENE)
	$(MAKE) html SCENE=$(SCENE)

render: scene

still:
	$(PYTHON) -m tvis render $(ONE_SCENE) --still --quality $(QUALITY) --theme $(THEME) \
		$(if $(filter 1,$(OPEN)),--open) $(if $(filter 1,$(NO_CACHE)),--no-cache)

segment:
	@test -n "$(ANIMATION)" || (echo 'Supply ANIMATION=N or ANIMATION=N,M' >&2; exit 2)
	$(PYTHON) -m tvis render $(ONE_SCENE) --animation $(ANIMATION) --quality $(QUALITY) \
		--theme $(THEME) $(if $(filter 1,$(OPEN)),--open) $(if $(filter 1,$(NO_CACHE)),--no-cache)

# Export targets intentionally do not depend on scene or all.
pdf:
	$(PYTHON) -m tvis present --format pdf --theme $(THEME) $(SELECT)

html:
	$(PYTHON) -m tvis present --format html --theme $(THEME) $(SELECT)

standalone:
	$(PYTHON) -m tvis present --format html --embed-videos --theme $(THEME) $(SELECT)

present:
	$(PYTHON) -m tvis present --format both --theme $(THEME) $(SELECT)

all:
	$(PYTHON) -m tvis all --quality $(QUALITY) --theme $(THEME) --speed $(SPEED) \
		--format $(FORMAT) $(if $(filter 1,$(EMBED)),--embed-videos) \
		$(if $(filter 1,$(FORCE)),--force) $(if $(filter 1,$(NO_CACHE)),--no-cache)

watch-all:
	$(PYTHON) -m tvis watch all --mode all --quality $(QUALITY) --theme $(THEME)
