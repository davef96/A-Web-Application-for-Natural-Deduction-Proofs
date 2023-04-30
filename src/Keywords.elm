-- this module provides replacement maps for keywords, shortcuts, and greek letters, plus functions to apply them
-- purpose: making entering goal and proof lines more user-friendly


module Keywords exposing (..)

import List
import Set exposing (Set)
import String
import Tuple


keywordReplacements : List ( String, String )
keywordReplacements =
    [ ( "all", "∀" ), ( "ex", "∃" ), ( "and", "∧" ), ( "conj", "∧" ), ( "or", "∨" ), ( "disj", "∨" ), ( "imp", "⟶" ), ( "bot", "⊥" ), ( "false", "⊥" ), ( "top", "⊤" ), ( "true", "⊤" ), ( "not", "¬" ), ( "neg", "¬" ), ( "iff", "⟷" ), ( "seq", "⊢" ), ( "eq", "＝" ) ]


shortcutReplacements : List ( String, String )
shortcutReplacements =
    [ ( "!", "∀" ), ( "?", "∃" ), ( "&", "∧" ), ( "|", "∨" ), ( "->", "⟶" ), ( "~", "¬" ), ( "<>", "⟷" ), ( ":-", "⊢" ), ( "=", "＝" ) ]


greekLetterReplacementsLower : List ( String, String )
greekLetterReplacementsLower =
    [ ( "alpha", "α" ), ( "beta", "β" ), ( "gamma", "γ" ), ( "delta", "δ" ), ( "eps", "ϵ" ), ( "zeta", "ζ" ), ( "theta", "θ" ), ( "eta", "η" ), ( "iota", "ι" ), ( "kappa", "κ" ), ( "lambda", "λ" ), ( "mu", "μ" ), ( "nu", "ν" ), ( "xi", "ξ" ), ( "omicron", "ο" ), ( "pi", "π" ), ( "rho", "ρ" ), ( "sigma", "σ" ), ( "tau", "τ" ), ( "ups", "υ" ), ( "phi", "ϕ" ), ( "chi", "χ" ), ( "psi", "ψ" ), ( "omega", "ω" ) ]


greekLetterReplacementsUpper : List ( String, String )
greekLetterReplacementsUpper =
    [ ( "Alpha", "Α" ), ( "Bet", "Β" ), ( "Gamma", "Γ" ), ( "Delta", "Δ" ), ( "Eps", "Ε" ), ( "Zeta", "Ζ" ), ( "Eta", "Η" ), ( "Theta", "Θ" ), ( "Iota", "Ι" ), ( "Kappa", "Κ" ), ( "Lambda", "Λ" ), ( "Mu", "Μ" ), ( "Nu", "Ν" ), ( "Xi", "Ξ" ), ( "Omicron", "Ο" ), ( "Pi", "Π" ), ( "Rho", "Ρ" ), ( "Sigma", "Σ" ), ( "Tau", "Τ" ), ( "Ups", "ϒ" ), ( "Phi", "Φ" ), ( "Chi", "Χ" ), ( "Psi", "Ψ" ), ( "Omega", "Ω" ) ]



-- map to obtain LaTeX symbol for some replacement


texSymbols : List ( String, String )
texSymbols =
    [ ( "∀", "\\forall" ), ( "∃", "\\exists" ), ( "∧", "\\land" ), ( "∨", "\\lor" ), ( "⟶", "\\longrightarrow" ), ( "⊥", "\\bot" ), ( "⊤", "\\top" ), ( "¬", "\\neg" ), ( "⟷", "\\longleftrightarrow" ), ( "⊢", "\\vdash" ), ( "＝", "=" ), ( "α", "\\alpha" ), ( "β", "\\beta" ), ( "γ", "\\gamma" ), ( "δ", "\\delta" ), ( "ϵ", "\\varepsilon" ), ( "ζ", "\\zeta" ), ( "θ", "\\theta" ), ( "η", "\\eta" ), ( "ι", "\\iota" ), ( "κ", "\\kappa" ), ( "λ", "\\lambda" ), ( "μ", "\\mu" ), ( "ν", "\\nu" ), ( "ξ", "\\xi" ), ( "ο", "\\omicron" ), ( "π", "\\pi" ), ( "ρ", "\\rho" ), ( "σ", "\\sigma" ), ( "τ", "\\tau" ), ( "υ", "\\upsilon" ), ( "ϕ", "\\phi" ), ( "χ", "\\chi" ), ( "ψ", "\\psi" ), ( "ω", "\\omega" ), ( "Α", "\\Alpha" ), ( "Β", "\\Beta" ), ( "Γ", "\\Gamma" ), ( "Δ", "\\Delta" ), ( "Ε", "\\Epsilon" ), ( "Ζ", "\\Zeta" ), ( "Η", "\\Eta" ), ( "Θ", "\\Theta" ), ( "Ι", "\\Iota" ), ( "Κ", "\\Kappa" ), ( "Λ", "\\Lambda" ), ( "Μ", "\\Mu" ), ( "Ν", "\\Nu" ), ( "Ξ", "\\Xi" ), ( "Ο", "\\Omicron" ), ( "Π", "\\Pi" ), ( "Ρ", "\\Rho" ), ( "Σ", "\\Sigma" ), ( "Τ", "\\Tau" ), ( "ϒ", "\\Upsilon" ), ( "Φ", "\\Phi" ), ( "Χ", "\\Chi" ), ( "Ψ", "\\Psi" ), ( "Ω", "\\Omega" ) ]


wrappedTexSymbols : List ( String, String )
wrappedTexSymbols =
    texSymbols
        |> List.map (\( lhs, rhs ) -> ( lhs, "{" ++ rhs ++ "}" ))


mathWrappedTexSymbols : List ( String, String )
mathWrappedTexSymbols =
    wrappedTexSymbols
        |> List.map (\( lhs, rhs ) -> ( lhs, "$" ++ rhs ++ "$" ))


displayReplacement : ( String, String ) -> String
displayReplacement r =
    let
        ( lhs, rhs ) =
            r
    in
    "('" ++ lhs ++ "' ↦ " ++ "'" ++ rhs ++ "')"


displayReplacements : List ( String, String ) -> List String
displayReplacements =
    List.map displayReplacement

acceptedReplacements : List ( String, String ) -> List String
acceptedReplacements rs =
    case rs of
        [] ->
            []
        (lhs, rhs) :: rest ->
            let
                (otheroptions, remaining) =
                    rest
                    |> List.partition (\(_, rhs1) -> rhs == rhs1)

                options =
                    (lhs, rhs) :: otheroptions
                    |> List.map Tuple.first

                str =
                    "(" ++ rhs ++ ": {" ++ String.join "," options ++ "})"
            in
            str :: acceptedReplacements remaining

displayAcceptedReplacements : List (String, String) -> String
displayAcceptedReplacements rs =
    rs
    |> acceptedReplacements
    |> String.join ", "

displayAllAcceptedReplacements : String
displayAllAcceptedReplacements =
    displayAcceptedReplacements (keywordReplacements ++ shortcutReplacements ++ greekLetterReplacementsLower ++ greekLetterReplacementsUpper)


displayKeywordReplacements : List String
displayKeywordReplacements =
    displayReplacements keywordReplacements


displayReplacementsFormattedHelper : List String -> Int -> String
displayReplacementsFormattedHelper xs i =
    if List.length xs > 0 then
        let
            next =
                List.take i xs

            rest =
                List.drop i xs

            recur =
                displayReplacementsFormattedHelper rest i
        in
        String.join ", " next ++ "\n" ++ recur

    else
        ""


displayKeywordReplacementsFormatted : Int -> String
displayKeywordReplacementsFormatted =
    displayReplacementsFormattedHelper displayKeywordReplacements


displayShortcutReplacements : List String
displayShortcutReplacements =
    displayReplacements shortcutReplacements


displayShortcutReplacementsFormatted : Int -> String
displayShortcutReplacementsFormatted =
    displayReplacementsFormattedHelper displayShortcutReplacements


displayGreekLetterReplacements : List String
displayGreekLetterReplacements =
    displayReplacements (greekLetterReplacementsLower ++ greekLetterReplacementsUpper)


displayGreekLetterReplacementsFormatted : Int -> String
displayGreekLetterReplacementsFormatted =
    displayReplacementsFormattedHelper displayGreekLetterReplacements


greekLettersLower : List String
greekLettersLower =
    List.map Tuple.second greekLetterReplacementsLower


greekLettersUpper : List String
greekLettersUpper =
    List.map Tuple.second greekLetterReplacementsUpper


greekLetters : List String
greekLetters =
    greekLettersLower ++ greekLettersUpper


keywords : List String
keywords =
    List.map Tuple.first keywordReplacements


shortcuts : List String
shortcuts =
    List.map Tuple.first shortcutReplacements



-- only logical connectives (does not include greek letters)


replacements : List String
replacements =
    List.map Tuple.second keywordReplacements



-- everything that currently would get replaced + logical connectives (cannot be used for vars, etc.)
-- if keyword replacement is disabled, then it is allowed to use keywords for vars, etc.


reserved : Bool -> Set String
reserved kword =
    let
        add =
            \b xs ys ->
                if b then
                    xs ++ ys

                else
                    ys
    in
    shortcuts
        |> add kword keywords
        |> (\x -> Set.fromList (x ++ replacements))



-- tests whether 'c' is in 'xs'


charElem : List String -> Char -> Bool
charElem xs c =
    List.map String.toList xs
        |> List.concat
        |> List.member c


isReplacement : Char -> Bool
isReplacement =
    charElem replacements


isGreekLetterLower : Char -> Bool
isGreekLetterLower =
    charElem greekLettersLower


isGreekLetterUpper : Char -> Bool
isGreekLetterUpper =
    charElem greekLettersUpper


isGreekLetter : Char -> Bool
isGreekLetter =
    charElem greekLetters



-- given a replacement list and a string, obtains the modified string


replace : List ( String, String ) -> String -> String
replace m s =
    List.foldl (\( k, v ) -> String.replace k v) s m



-- replaces unicode symbols in string by LaTeX symbol


replaceUnicodeSymbols : String -> String
replaceUnicodeSymbols =
    replace wrappedTexSymbols



-- replaces unicode symbols in string by LaTeX symbol and escape it in math mode using $...$


replaceAndEscapeUnicodeSymbols : String -> String
replaceAndEscapeUnicodeSymbols =
    replace mathWrappedTexSymbols



-- replaces shortcuts, keywords, and greek letters in s


replaceKeywords : Bool -> Bool -> Bool -> String -> String
replaceKeywords scut kword greek s =
    let
        ifreplace =
            \b map str ->
                if b then
                    replace map str

                else
                    str
    in
    s
        |> ifreplace scut shortcutReplacements
        |> ifreplace kword keywordReplacements
        |> ifreplace greek greekLetterReplacementsUpper
        |> ifreplace greek greekLetterReplacementsLower



-- replaces shortcuts, keywords, and greek letters in a pair (s1, s2)


replaceKeywordsPair : Bool -> Bool -> Bool -> ( String, String ) -> ( String, String )
replaceKeywordsPair scut kword greek pair =
    let
        call =
            replaceKeywords scut kword greek
    in
    Tuple.mapBoth call call pair



-- replaces AT MOST ONE keyword/shortcut/greek letter in s and additionally returns length difference (e.g., 'and' will be replaced by '∧'; hence, the length difference will be 2)


replaceSingle : Bool -> Bool -> Bool -> String -> ( String, Int, Bool )
replaceSingle scut kword greek s =
    let
        addif =
            \b map xs ->
                if b then
                    xs ++ [ map ]

                else
                    xs

        todo =
            []
                |> addif scut shortcutReplacements
                |> addif kword keywordReplacements
                |> addif greek greekLetterReplacementsUpper
                |> addif greek greekLetterReplacementsLower
    in
    todo
        |> List.foldl
            (\map state ->
                let
                    ( str, _, replaced ) =
                        state
                in
                if replaced then
                    state

                else
                    replaceSingleHelper map str
            )
            ( s, 0, False )



-- given map m, replace at most one key-value pair in s


replaceSingleHelper : List ( String, String ) -> String -> ( String, Int, Bool )
replaceSingleHelper m s =
    List.foldl
        (\( k, v ) state ->
            let
                ( str, _, replaced ) =
                    state
            in
            if not replaced && String.contains k str then
                ( String.replace k v str, String.length k - String.length v, True )

            else
                state
        )
        ( s, 0, False )
        m
