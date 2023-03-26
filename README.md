# A Web Application for Natural Deduction Proofs
This project implements an interactive web application that facilitates writing box style natural deduction proofs for statements in first-order logic. A searching algorithm is able to automatically infer required references and thus the user only has to state a rule to justify a formula. Utilizing a generic approach enables this project to handle rules without the requirement of covering each rule by a separate case. The primary goal of this application is the use for teaching purposes. A simple, intuitive user interface is provided to allow for a good educational experience. This tool has been implemented using the functional web framework Elm.

## Requirements
[Elm](https://guide.elm-lang.org/install/elm.html)

## Launching the App
### Local/Debugging
start `elm reactor` in the `src` folder and open `Main.elm`, e.g., ([http://localhost:8000/Main.elm](http://localhost:8000/Main.elm))
### Compiling a Release Build
`elm make ./src/Main.elm --optimize` open the created `html` file with your browser or host it on a server

## Tests
- uses [elm-test](https://github.com/elm-explorations/test/) (`npm install -g elm-test`)
- just run `elm-test` in this folder

## Formatting
- uses [elm-format](https://github.com/avh4/elm-format) (`npm install -g elm-format`)
- just run `elm-format <dir>` to format all source files in the given directory

## Known Bugs
- Variable capturing is not detected in some applications of the universal elimination rule
- Some valid applications of equality elimination are incorrectly classified as invalid
- The cursor/caret is moved to the end of the line whenever a keyword/shortcut in a string is replaced by a unicode symbol
- Some unicode symbols may be displayed incorrectly if the user's browser chooses a font that does not support these symbols
- Lines that only fix variables are not included when displaying a box reference, e.g., if a box contains lines 1 to 5 and line 1 only introduces variables then the application will display `2--5`



