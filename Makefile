all: deb

deb:
	elm make src/Main.elm --output=main.js

opt:
	elm make src/Main.elm --optimize --output=main.js

optmin:
	elm make src/Main.elm --optimize --output=main.js
	uglifyjs main.js --compress 'pure_funcs=[F2,F3,F4,F5,F6,F7,F8,F9,A2,A3,A4,A5,A6,A7,A8,A9],pure_getters,keep_fargs=false,unsafe_comps,unsafe' | uglifyjs --mangle --output main.js

start: deb
	xdg-open tool.html

startopt: opt
	xdg-open tool.html

startoptmin: optmin
	xdg-open tool.html

export: optmin
	zip tool.zip tool.html main.js font/**

clean:
	rm main.js
