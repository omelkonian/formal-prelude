default: site

site:
	agda --html --html-dir=docs Everything.agda && cp docs/Everything.html docs/index.html

clean:
	rm -rf docs/
