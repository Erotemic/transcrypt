# Independent Python visualization project; changes neither Rust nor Lean.
PYTHON ?= python3
SCENE ?= clean
BEAT ?= last
QUALITY ?= l

.PHONY: help list check storyboard preview gallery render still all watch-all test
help:
	@echo 'make gallery                 HTML storyboard without Manim'
	@echo 'make preview SCENE=clean BEAT=commit'
	@echo 'make render SCENE=proof QUALITY=l'
	@echo 'make all QUALITY=l          changed Manim clips + local HTML presentation'
	@echo 'make watch-all              incremental rebuild after edits'
	@echo 'make check                 source/proof/catalog/geometry validation'
	@echo 'make test                  Python authoring tests'
list:
	$(PYTHON) -m tvis list
check:
	$(PYTHON) -m tvis check
storyboard:
	$(PYTHON) -m tvis storyboard
preview:
	$(PYTHON) -m tvis preview $(SCENE) --beat $(BEAT)
gallery:
	$(PYTHON) -m tvis gallery
render:
	$(PYTHON) -m tvis render $(SCENE) --quality $(QUALITY)
still:
	$(PYTHON) -m tvis render $(SCENE) --quality $(QUALITY) --still
all:
	$(PYTHON) -m tvis all --quality $(QUALITY)
watch-all:
	$(PYTHON) -m tvis watch all --mode all --quality $(QUALITY)
test:
	$(PYTHON) -m unittest discover -s tests -p 'test_*.py' -v
