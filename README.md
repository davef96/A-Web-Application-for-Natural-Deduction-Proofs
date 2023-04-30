# A Web Application for Natural Deduction Proofs
This work describes the implementation of an interactive web application that facilitates writing box style natural deduction proofs for statements in first-order logic. A search algorithm is able to automatically infer required line references and thus the user only has to state a rule to justify a formula. Utilizing a generic approach enables this project to support rules without the requirement of handling each rule explicitly by providing specific code. The primary goal of this application is the use for teaching purposes. A simple user interface is provided to allow for a good educational experience. This tool has been implemented using the functional web framework [Elm](https://elm-lang.org/).

## Launching the Application / Requirements
- [Elm](https://guide.elm-lang.org/install/elm.html) is required to compile the project 
- more tools are required to run the tests, etc. (see below)

## Compiling the Project
### Compiling a Development/Debug Build
- use `make` and then open `tool.html` manually
- or use `make start` instead (uses `xdg-open tool.html` after compiling the source files)
### Compiling a Release Build
- use `make opt` and then open `tool.html` manually or use `make startopt` to open it automatically
- OR use `make optmin` and then open `tool.html` manually or use `make startoptmin` to open it automatically; this option minimizes the size of the compiled `js` file using the tool `uglifyjs` (`npm install -g uglify-js`)
### Exporting the Compiled Project
- `make export` compiles an optimized + minimized build and then uses `zip` to export the required files as `tool.zip`

## Tests
run `elm-test` in this folder (`npm install -g elm-test`)

## Formatting
run `elm-format <dir>` (`npm install -g elm-format`) to format all source files in the given directory

## Known Bugs
- line number references may be displayed incorrectly (offset added) if the proof contains boxes that **only** fix variables in the first line and contain **no** other syntactically correct lines
- error messages and warnings regarding boxes may not be displayed at the correct position, i.e., they are not necessarily displayed in the box they refer to
- the style of the text displayed when hovering over elements (`title` attribute) is fully controlled by the user's browser; some unicode symbols may not be displayed correctly due to the chosen font;

## Usage
- open the tool and then click on the `Help` button in the toolbar; a short user manual will be displayed


