default: site

site:
	agda --html --html-dir=docs Everything.agda && cp docs/Everything.html docs/index.html

clean:
	rm -rf docs/

# Travis Setup (install Agda, the Agda standard library, acknowledgements, etc.)
AGDA_VERSION := 2.6.0
AGDA_STDLIB_VERSION := 1.1

travis-setup:\
	$(HOME)/.local/bin/agda\
	$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/src\
	$(HOME)/.agda/libraries

.phony: travis-setup

$(HOME)/.local/bin/agda:
	curl -L https://github.com/agda/agda/archive/v$(AGDA_VERSION).zip -o $(HOME)/agda-$(AGDA_VERSION).zip
	unzip -qq $(HOME)/agda-$(AGDA_VERSION).zip -d $(HOME)
	cd $(HOME)/agda-$(AGDA_VERSION);\
		stack install --stack-yaml=stack-8.0.2.yaml

$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/src:
	curl -L https://github.com/agda/agda-stdlib/archive/v$(AGDA_STDLIB_VERSION).zip -o $(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION).zip
	unzip -qq $(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION).zip -d $(HOME)
	mkdir -p $(HOME)/.agda

$(HOME)/.agda/libraries:
	echo "$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/standard-library.agda-lib" >> $(HOME)/.agda/libraries

# Travis check
travis-check:
	agda Everything.agda
