module Main exposing (..)

import Browser
import Browser.Dom as Dom
import Css exposing (..)
import Css.Global
import File exposing (File)
import File.Download as Download
import File.Select as Select
import Formula
import Html
import Html.Styled exposing (..)
import Html.Styled.Attributes exposing (..)
import Html.Styled.Events exposing (keyCode, on, onClick, onInput)
import Json.Decode
import Json.Encode
import Keywords
import List
import ModelDefs exposing (..)
import Parser exposing (..)
import Proof exposing (BuildLineState(..), BuildState)
import ProofChecking exposing (BlockCheck(..), CheckState, FactPos(..), ProofCheck(..))
import Set
import Task
import Utils



-- MAIN


main : Program () Model Msg
main =
    Browser.element { init = init, update = update, view = view >> toUnstyled, subscriptions = subscriptions }


init : () -> ( Model, Cmd Msg )
init _ =
    ( Model "" clearedProof defaultConfig False False "success" False lineSizeBase goalSizeBase jfcSizeBase, focusElement goalId )



-- SUBSCRIPTIONS


subscriptions : Model -> Sub Msg
subscriptions model =
    Sub.none



-- UPDATE


type Key
    = BackSpace
    | Tab
    | Enter
    | Esc
    | PageUp
    | PageDown
    | End
    | Home
    | Up
    | Down
    | Del
    | Other


onKeyEvent : (Int -> msg) -> Attribute msg
onKeyEvent tagger =
    on "keydown" (Json.Decode.map tagger keyCode)


mapToKey : Int -> Key
mapToKey code =
    case code of
        8 ->
            BackSpace

        9 ->
            Tab

        13 ->
            Enter

        27 ->
            Esc

        33 ->
            PageUp

        34 ->
            PageDown

        35 ->
            End

        36 ->
            Home

        38 ->
            Up

        40 ->
            Down

        46 ->
            Del

        _ ->
            Other


type Move
    = MoveUp
    | MoveDown
    | MoveTo Int


type LineMod
    = ModifyLineFrm String Bool -- frmstr movetojfc
    | ModifyLineJfc String Bool
    | DeleteLine



-- other operations such as merging could also be supported here


type BoxMod
    = SplitBox


type Field
    = FieldFrm
    | FieldJfc
    | FieldGoal


type FileType
    = Txt
    | LaTeX


type ToolEvent
    = GetPremises
    | ClearProof
    | MergeBlocks
    | ToggleLogic
    | ToggleQType
    | ToggleConjStronger
    | ToggleReplaceKW
    | ToggleReplaceSC
    | ToggleReplaceGreek
    | ToggleInputMode
    | ToggleHeuristics
    | Export FileType
    | Import -- txt only
    | Help


type Msg
    = Goal GoalType
    | LineEvent Int LineMod
    | BoxEvent Int BoxMod
    | KeyEvent Int Field Int -- line number, frm | jfc | goal, key code
    | MoveEvent Int Move -- line number, up | down
    | ToolEvent ToolEvent
    | MainPage -- go back to main page
    | ProofSelected File -- finished selecting proof txt as a result from ToolEvent 'Import'
    | ProofLoaded String -- finished loading data from selected file
    | NOP



-- rerun keyword replacement on goal (whenever cfg changes)


updateGoal : Config -> GoalType -> GoalType
updateGoal cfg =
    Keywords.replaceKeywords cfg.replacesc cfg.replacekw cfg.replacegreek



-- updates part in line 'n' (true: frm, false: jfc)


updateLinesPart : Bool -> Config -> Int -> String -> RawProof -> RawProof
updateLinesPart part cfg n s proof =
    let
        u =
            Keywords.replaceKeywords cfg.replacesc cfg.replacekw cfg.replacegreek s

        edit =
            if part then
                EditFormula u

            else
                EditJustification u
    in
    updateRawProof n edit proof



-- updates formula part in line 'n'


updateLinesFrm : Config -> Int -> String -> RawProof -> RawProof
updateLinesFrm =
    updateLinesPart True



-- updates justification part in line 'n'


updateLinesJfc : Config -> Int -> String -> RawProof -> RawProof
updateLinesJfc =
    updateLinesPart False



-- reruns keyword replacement for every line


updateAllLines : Config -> RawProof -> RawProof
updateAllLines cfg proof =
    proof
        |> updateRawProof 0 (UpdateAll cfg)



-- adds empty line below line 'n'


addLine : Int -> RawProof -> RawProof
addLine n proof =
    proof
        |> updateRawProof n (AddLine "" "")



-- deletes line 'n'


deleteLine : Int -> RawProof -> RawProof
deleteLine n proof =
    proof
        |> updateRawProof n RemoveLine



-- deletes line 'n' if 'frm' empty
-- instead of directly removing the line with 'RemoveLineIfEmpty', the check for emptiness is done after 'getLine' in order to update the focus accordingly
-- if 'split' is true and the line is inside a block, the block will get split (instead of removing the line)


deleteLineIfEmpty : Bool -> Int -> Model -> ( Model, Cmd Msg )
deleteLineIfEmpty split n model =
    case getLine n model.proof of
        Just ( frm, _, inblock ) ->
            if String.isEmpty frm then
                if split && inblock then
                    ( { model | proof = splitRawProof n model.proof }, focusElement (frmId n) )

                else
                    ( { model | proof = updateRawProof n RemoveLine model.proof }, focusElement (frmId (n - 1)) )

            else
                ( model, Cmd.none )

        Nothing ->
            ( model, Cmd.none )



-- swaps lines 'm' and 'n'


swapLines : Int -> Int -> RawProof -> RawProof
swapLines n m proof =
    if m < n then
        proof
            |> updateRawProof n (SwapLinesWith m)

    else if m > n then
        proof
            |> updateRawProof m (SwapLinesWith n)

    else
        proof



-- moves line 'n' according to move 'm'


moveLine : Int -> Move -> Model -> ( Model, Cmd Msg )
moveLine n m model =
    let
        other =
            case m of
                MoveUp ->
                    n - 1

                MoveDown ->
                    n + 1

                MoveTo k ->
                    k
    in
    ( { model | proof = swapLines n other model.proof }, focusElement (frmId other) )


goalId : String
goalId =
    "goal"


frmId : Int -> String
frmId n =
    if n == 0 then
        goalId

    else
        "frm" ++ String.fromInt n


jfcId : Int -> String
jfcId n =
    "jfc" ++ String.fromInt n


focusElement : String -> Cmd Msg
focusElement id =
    Task.attempt (\_ -> NOP) (Dom.focus id)


update : Msg -> Model -> ( Model, Cmd Msg )
update msg model =
    case msg of
        Goal g ->
            let
                oldcfg =
                    model.cfg

                altcfg1 =
                    { oldcfg | qtype = not oldcfg.qtype }

                altcfg2 =
                    { oldcfg | fol = not oldcfg.fol }

                -- select appropriate logic & quantifier format based on success of sequent parser
                newcfg =
                    case Parser.run (Formula.sequent (getParserConfig oldcfg)) g of
                        Ok _ ->
                            oldcfg

                        Err _ ->
                            case Parser.run (Formula.sequent (getParserConfig altcfg1)) g of
                                Ok _ ->
                                    altcfg1

                                Err _ ->
                                    case Parser.run (Formula.sequent (getParserConfig altcfg2)) g of
                                        Ok _ ->
                                            altcfg2

                                        Err _ ->
                                            oldcfg
            in
            ( { model | cfg = newcfg, goal = updateGoal newcfg g, proof = updateAllLines newcfg model.proof, gsize = goalSize g }, Cmd.none )

        BoxEvent n e ->
            case e of
                SplitBox ->
                    ( { model | proof = splitRawProof n model.proof }, focusElement (frmId n) )

        LineEvent n e ->
            case e of
                ModifyLineFrm f movetojfc ->
                    model.proof
                        |> (\p1 ->
                                (if Proof.isFixing f && not (beginsBlock n p1) && model.cfg.fol then
                                    updateRawProof n StartBlock p1

                                 else
                                    p1
                                )
                                    |> (\p2 ->
                                            ( { model | proof = updateLinesFrm model.cfg n f p2, lsize = Basics.max model.lsize (lineSize f) }
                                            , if movetojfc then
                                                focusElement (jfcId n)

                                              else
                                                -- we would lose focus when blocks get splitted
                                                focusElement (frmId n)
                                            )
                                       )
                           )

                ModifyLineJfc j movetofrm ->
                    model.proof
                        |> (\p1 ->
                                (if Proof.isAssumption j && not (beginsBlock n p1) then
                                    updateRawProof n StartBlock p1

                                 else
                                    p1
                                )
                                    |> (\p2 ->
                                            ( { model | proof = updateLinesJfc model.cfg n j p2, jfcsize = jfcSize j }
                                            , if movetofrm then
                                                focusElement (frmId n)

                                              else
                                                focusElement (jfcId n)
                                            )
                                       )
                           )

                DeleteLine ->
                    ( { model | proof = deleteLine n model.proof }, focusElement (frmId (n - 1)) )

        KeyEvent n field code ->
            let
                -- let element focus itself (would lose it upon indentation, etc.)
                cmd =
                    case field of
                        FieldFrm ->
                            focusElement (frmId n)

                        FieldJfc ->
                            focusElement (jfcId n)

                        FieldGoal ->
                            Cmd.none
            in
            case mapToKey code of
                BackSpace ->
                    case field of
                        -- field empty and outermost level ==> delete line
                        -- field empty and within block ==> split block
                        FieldFrm ->
                            deleteLineIfEmpty True n model

                        -- currently: do nothing
                        -- alternatively: field empty ==> goToFrmIfEmpty n model
                        FieldJfc ->
                            ( model, Cmd.none )

                        -- do nothing
                        FieldGoal ->
                            ( model, Cmd.none )

                Del ->
                    case field of
                        -- field empty ==> delete line
                        FieldFrm ->
                            deleteLineIfEmpty False n model

                        -- currently: do nothing
                        -- alternatively: field empty ==> goToFrmIfEmpty n model
                        FieldJfc ->
                            ( model, Cmd.none )

                        -- do nothing
                        FieldGoal ->
                            ( model, Cmd.none )

                Tab ->
                    case field of
                        FieldFrm ->
                            ( model, focusElement (jfcId n) )

                        FieldJfc ->
                            ( model, focusElement (frmId n) )

                        FieldGoal ->
                            -- if first line does not exist, it will be created
                            goToFirstLine model

                Esc ->
                    -- remove focus
                    ( model, focusElement (frmId n) )

                Enter ->
                    ( { model | proof = addLine n model.proof }, focusElement (frmId (n + 1)) )

                Up ->
                    case field of
                        FieldFrm ->
                            ( model, focusElement (frmId (n - 1)) )

                        FieldJfc ->
                            ( model, focusElement (jfcId (n - 1)) )

                        FieldGoal ->
                            ( model, Cmd.none )

                Down ->
                    case field of
                        FieldFrm ->
                            ( model, focusElement (frmId (n + 1)) )

                        FieldJfc ->
                            ( model, focusElement (jfcId (n + 1)) )

                        FieldGoal ->
                            ( model, focusElement (frmId 1) )

                _ ->
                    ( model, Cmd.none )

        MoveEvent n m ->
            moveLine n m model

        ToolEvent e ->
            case e of
                GetPremises ->
                    addPremises model

                ClearProof ->
                    clearProof model

                MergeBlocks ->
                    ( { model | proof = mergeBlocks model.proof }, Cmd.none )

                ToggleLogic ->
                    ( switchLanguage model, Cmd.none )

                ToggleQType ->
                    let
                        oldcfg =
                            model.cfg

                        currentqtype =
                            not oldcfg.qtype

                        newcfg =
                            { oldcfg | qtype = currentqtype }
                    in
                    ( { model | cfg = newcfg }, Cmd.none )

                ToggleConjStronger ->
                    let
                        oldcfg =
                            model.cfg

                        currentconjstronger =
                            not oldcfg.conjstronger

                        newcfg =
                            { oldcfg | conjstronger = currentconjstronger }
                    in
                    ( { model | cfg = newcfg }, Cmd.none )

                ToggleInputMode ->
                    let
                        oldcfg =
                            model.cfg

                        currentinputmode =
                            not oldcfg.inputmode

                        newcfg =
                            { oldcfg | inputmode = currentinputmode }
                    in
                    ( { model | cfg = newcfg }, Cmd.none )

                ToggleHeuristics ->
                    let
                        oldcfg =
                            model.cfg

                        currentheuristics =
                            not oldcfg.heuristics

                        newcfg =
                            { oldcfg | heuristics = currentheuristics }
                    in
                    ( { model | cfg = newcfg }, Cmd.none )

                ToggleReplaceKW ->
                    let
                        oldcfg =
                            model.cfg

                        currentkw =
                            not oldcfg.replacekw

                        newcfg =
                            { oldcfg | replacekw = currentkw }
                    in
                    if currentkw then
                        ( { model | cfg = newcfg, goal = updateGoal newcfg model.goal, proof = updateAllLines newcfg model.proof }, Cmd.none )

                    else
                        ( { model | cfg = newcfg }, Cmd.none )

                ToggleReplaceSC ->
                    let
                        oldcfg =
                            model.cfg

                        currentsc =
                            not oldcfg.replacesc

                        newcfg =
                            { oldcfg | replacesc = currentsc }
                    in
                    if currentsc then
                        ( { model | cfg = newcfg, goal = updateGoal newcfg model.goal, proof = updateAllLines newcfg model.proof }, Cmd.none )

                    else
                        ( { model | cfg = newcfg }, Cmd.none )

                ToggleReplaceGreek ->
                    let
                        oldcfg =
                            model.cfg

                        currentgreek =
                            not oldcfg.replacegreek

                        newcfg =
                            { oldcfg | replacegreek = currentgreek }
                    in
                    if currentgreek then
                        ( { model | cfg = newcfg, goal = updateGoal newcfg model.goal, proof = updateAllLines newcfg model.proof }, Cmd.none )

                    else
                        ( { model | cfg = newcfg }, Cmd.none )

                Export filetype ->
                    case filetype of
                        Txt ->
                            ( model, exportProofAsTxt model )

                        LaTeX ->
                            ( { model | latex = True }, Cmd.none )

                Import ->
                    -- user selects file to import
                    ( model, loadProofFromTxt )

                Help ->
                    ( { model | help = True }, Cmd.none )

        -- finished selecting file to import
        ProofSelected file ->
            ( model, importProofFromTxt file )

        -- received file content (string)
        ProofLoaded content ->
            decodeImportedContent content model

        MainPage ->
            ( { model | latex = False, error = False, help = False }, Cmd.none )

        NOP ->
            ( model, Cmd.none )


goToFirstLine : Model -> ( Model, Cmd Msg )
goToFirstLine model =
    case model.proof of
        RawBegin [] ->
            ( { model | proof = RawBegin [ RawStep "" "" ] }, focusElement (frmId 1) )

        _ ->
            ( model, focusElement (frmId 1) )


goToFrmIfEmpty : Int -> Model -> ( Model, Cmd Msg )
goToFrmIfEmpty n model =
    case getLine n model.proof of
        Just ( _, jfc, _ ) ->
            if String.isEmpty jfc then
                ( model, focusElement (frmId n) )

            else
                ( model, Cmd.none )

        Nothing ->
            ( model, Cmd.none )


decodeImportedContent : String -> Model -> ( Model, Cmd Msg )
decodeImportedContent content model =
    let
        data =
            Parser.run txtParser content
    in
    case data of
        Ok ( goaldata, proofdata, cfgdata ) ->
            let
                maxlinesize =
                    proofdata
                        |> List.map (\( _, ( l, _ ) ) -> lineSize l)
                        |> List.maximum
                        |> Maybe.withDefault lineSizeBase

                maxjfcsize =
                    proofdata
                        |> List.map (\( _, ( _, j ) ) -> jfcSize j)
                        |> List.maximum
                        |> Maybe.withDefault jfcSizeBase
            in
            ( { model | goal = goaldata, proof = RawBegin (Proof.splitIntoRawBlocks proofdata), cfg = cfgdata, gsize = goalSize goaldata, lsize = maxlinesize, jfcsize = maxjfcsize }, Cmd.none )

        Err x ->
            ( { model | error = True, lasterror = "Failed to import selected proof. Details: " ++ Utils.deadEndsToString x }, Cmd.none )



-- since Parser.spaces does not chomp '\t'


spacest : Parser ()
spacest =
    Parser.chompWhile (\c -> c == ' ' || c == '\n' || c == '\u{000D}' || c == '\t')



-- parse import txt


txtParser : Parser ( GoalType, List ( Int, ( String, String ) ), Config )
txtParser =
    succeed (\x y z -> ( x, y, z ))
        |. spacest
        |= goalParser
        |. spacest
        |= proofParser
        |. spacest
        |= cfgParser
        |. spacest
        |. Parser.end


goalParser : Parser GoalType
goalParser =
    succeed identity
        |. spacest
        |. symbol "goal ="
        |. spacest
        |. symbol "\""
        |= Parser.getChompedString (Parser.chompWhile (\c -> c /= '"'))
        |. symbol "\""


proofParser : Parser (List ( Int, ( String, String ) ))
proofParser =
    succeed identity
        |. spacest
        |. symbol "proof ="
        |. spacest
        |= proofLinesParser


proofLinesParser : Parser (List ( Int, ( String, String ) ))
proofLinesParser =
    Parser.sequence
        { start = "["
        , separator = ","
        , end = "]"
        , spaces = spacest
        , item = proofLineParser
        , trailing = Parser.Forbidden
        }


proofLineParser : Parser ( Int, ( String, String ) )
proofLineParser =
    succeed Tuple.pair
        |. spacest
        |. symbol "("
        |. spacest
        |= Parser.int
        |. spacest
        |. symbol ","
        |. spacest
        |= lineTupleParser
        |. spacest
        |. symbol ")"


lineTupleParser : Parser ( String, String )
lineTupleParser =
    succeed Tuple.pair
        |. spacest
        |. symbol "("
        |. spacest
        |. symbol "\""
        |= Parser.getChompedString (Parser.chompWhile (\c -> c /= '"'))
        |. symbol "\""
        |. spacest
        |. symbol ","
        |. spacest
        |. symbol "\""
        |= Parser.getChompedString (Parser.chompWhile (\c -> c /= '"'))
        |. symbol "\""
        |. spacest
        |. symbol ")"


boolParser : Char -> Parser Bool
boolParser d =
    Parser.getChompedString (Parser.chompWhile (\c -> c /= d))
        |> Parser.andThen
            (\s ->
                if s == "True" then
                    succeed True

                else
                    succeed False
            )


ruleSubsetParser : Char -> Parser RuleSubset
ruleSubsetParser d =
    Parser.getChompedString (Parser.chompWhile (\c -> c /= d))
        |> Parser.andThen
            (\sub ->
                case sub of
                    "NoRules" ->
                        succeed NoRules

                    "IntProp" ->
                        succeed IntProp

                    "Prop" ->
                        succeed Prop

                    "IntFOL" ->
                        succeed IntFOL

                    "FOL" ->
                        succeed FOL

                    _ ->
                        succeed FOL
            )


cfgParser : Parser Config
cfgParser =
    succeed Config
        |. spacest
        |. symbol "config ="
        |. spacest
        |. symbol "{"
        |. spacest
        |. symbol "fol:"
        |= boolParser ','
        |. spacest
        |. symbol ","
        |. spacest
        |. symbol "qtype:"
        |= boolParser ','
        |. spacest
        |. symbol ","
        |. spacest
        |. symbol "replacesc:"
        |= boolParser ','
        |. spacest
        |. symbol ","
        |. spacest
        |. symbol "replacekw:"
        |= boolParser ','
        |. spacest
        |. symbol ","
        |. spacest
        |. symbol "replacegreek:"
        |= boolParser ','
        |. spacest
        |. symbol ","
        |. spacest
        |. symbol "subset:"
        |= ruleSubsetParser ','
        |. spacest
        |. symbol ","
        |. spacest
        |. symbol "conjstronger:"
        |= boolParser ','
        |. spacest
        |. symbol ","
        |. spacest
        |. symbol "inputmode:"
        |= boolParser ','
        |. spacest
        |. symbol ","
        |. spacest
        |. symbol "heuristics:"
        |= boolParser '}'
        |. spacest
        |. symbol "}"


importProofFromTxt : File -> Cmd Msg
importProofFromTxt file =
    Task.perform ProofLoaded (File.toString file)


loadProofFromTxt : Cmd Msg
loadProofFromTxt =
    Select.file [ "text/plain" ] ProofSelected


saveTxt : String -> Cmd msg
saveTxt content =
    Download.string "proof.txt" "text/plain" content


proofLineToString : ( Int, ( String, String ) ) -> String
proofLineToString l =
    let
        ( k, ( frm, jfc ) ) =
            l
    in
    "( " ++ String.fromInt k ++ ", ( \"" ++ frm ++ "\", \"" ++ jfc ++ "\" ) )"


rawProofToStringHelper : Int -> RawProof -> String
rawProofToStringHelper start proof =
    let
        recur =
            List.foldl
                (\step state ->
                    let
                        ( k, xs ) =
                            state
                    in
                    case step of
                        RawStep _ _ ->
                            ( k, xs ++ [ rawProofToStringHelper k step ] )

                        _ ->
                            ( k, xs ++ [ rawProofToStringHelper (k + 1) step ] )
                )
                ( start, [] )
    in
    case proof of
        RawStep frm jfc ->
            proofLineToString ( start, ( frm, jfc ) )

        RawBegin ps ->
            recur ps
                |> Tuple.second
                |> String.join ","

        RawBlock ps ->
            recur ps
                |> Tuple.second
                |> String.join ","


rawProofToString : RawProof -> String
rawProofToString =
    rawProofToStringHelper 0


boolToString : Bool -> String
boolToString b =
    if b then
        "True"

    else
        "False"


ruleSubsetToString : RuleSubset -> String
ruleSubsetToString sub =
    case sub of
        NoRules ->
            "NoRules"

        IntProp ->
            "IntProp"

        Prop ->
            "Prop"

        IntFOL ->
            "IntFOL"

        FOL ->
            "FOL"


configToString : Config -> String
configToString cfg =
    "fol:" ++ boolToString cfg.fol ++ ",qtype:" ++ boolToString cfg.qtype ++ ",replacesc:" ++ boolToString cfg.replacesc ++ ",replacekw:" ++ boolToString cfg.replacekw ++ ",replacegreek:" ++ boolToString cfg.replacegreek ++ ",subset:" ++ ruleSubsetToString cfg.subset ++ ",conjstronger:" ++ boolToString cfg.conjstronger ++ ",inputmode:" ++ boolToString cfg.inputmode ++ ",heuristics:" ++ boolToString cfg.heuristics


exportProofAsTxt : Model -> Cmd msg
exportProofAsTxt model =
    "goal =\n\t\""
        ++ model.goal
        ++ "\"\n\nproof =\n\t[ "
        ++ rawProofToString model.proof
        ++ "\n\t]\n\nconfig =\n\t{"
        ++ configToString model.cfg
        ++ "}\n"
        |> saveTxt



-- obtain subproofs for LaTeX logicproof


getSubProofs : RawProof -> String
getSubProofs proof =
    let
        recur =
            List.foldl
                (\step str ->
                    str ++ getSubProofs step
                )
                ""
    in
    case proof of
        RawStep frm jfc ->
            let
                line =
                    frm ++ " & $" ++ jfc ++ "$"
            in
            "\\\\\n" ++ line

        RawBlock ps ->
            "\\\\\n" ++ "\\begin{subproof}\n" ++ recur ps ++ "\n\\end{subproof}\n"

        RawBegin ps ->
            recur ps



-- empty line in LaTeX proof: "\n\\\\\n"


removeEmptyLines : String -> String
removeEmptyLines =
    String.replace "\n\\\\\n" "\n"



-- "∀x. P(x,y)" ==> "∀x.\\,P(x,y)"


addDotSpace : String -> String
addDotSpace =
    String.replace ". " ".\\,"



-- "[z0]" ==> "z0\;"


removeBrackets : String -> String
removeBrackets str =
    str
        |> String.replace "[" ""
        |> String.replace "]" "\\;"



-- "$$" ==> ""


removeEmptyMath : String -> String
removeEmptyMath =
    String.replace "$$" ""


proofToLaTeX : Model -> String
proofToLaTeX model =
    ("% !TeX program = xelatex\n\n%\\usepackage{logicproof}\n%\\usepackage{unicode-math}\n\nGoal: $" ++ model.goal ++ "$\n\n\\begin{logicproof}{3}\n" ++ getSubProofs model.proof ++ "\n\\end{logicproof}") |> addDotSpace |> removeBrackets |> removeEmptyLines |> removeEmptyMath



-- switch between propositional logic and FOL
-- currently just converts the entire string to upper/lowercase respectively


switchLanguage : Model -> Model
switchLanguage model =
    let
        lang =
            not model.cfg.fol

        convert =
            \s ->
                if lang then
                    String.map
                        (\c ->
                            if Keywords.isGreekLetter c then
                                c

                            else
                                Char.toUpper c
                        )
                        s

                else
                    String.toLower s

        g =
            convert model.goal

        p =
            updateRawProof 0 (CaseConversion lang) model.proof

        oldcfg =
            model.cfg

        newcfg =
            { oldcfg
                | fol = lang
                , subset =
                    if lang then
                        FOL

                    else
                        Prop
            }
    in
    { model | cfg = newcfg, goal = g, proof = p }



-- default state of proof lines: 1 empty line


clearProof : Model -> ( Model, Cmd Msg )
clearProof model =
    ( { model | proof = clearedProof, lsize = lineSizeBase, jfcsize = jfcSizeBase }, focusElement (frmId 1) )



-- adds premises and conclusion (as stated in goal) to proof lines
-- proof still empty ==> premises + empty line + conclusion; focus empty line
-- proof not empty ==> premises + lines + conclusion; focus last line in lines


addPremises : Model -> ( Model, Cmd Msg )
addPremises model =
    let
        cfg =
            model.cfg

        goal =
            model.goal

        proof =
            model.proof
    in
    case Parser.run (Formula.sequent (getParserConfig cfg)) goal of
        Ok seq ->
            let
                ( premises, c ) =
                    seq

                conclusion =
                    RawStep (Formula.displayFormula cfg.qtype c) ""

                lines =
                    case proof of
                        RawBegin ps ->
                            case ps of
                                [] ->
                                    [ RawStep "" "" ]

                                _ ->
                                    ps

                        _ ->
                            [ RawStep "" "" ]

                ( newlines, cmd ) =
                    premises
                        |> List.map (\x -> RawStep (Formula.displayFormula cfg.qtype x) "premise")
                        |> (\prems -> ( prems ++ lines ++ [ conclusion ], focusElement (frmId (List.length prems + proofLengths lines)) ))

                maxlinesize =
                    newlines
                        |> RawBegin
                        |> proofToList
                        |> List.map (\( l, _ ) -> lineSize l)
                        |> List.maximum
                        |> Maybe.withDefault lineSizeBase
            in
            ( { model | proof = RawBegin newlines, lsize = maxlinesize }, cmd )

        Err _ ->
            ( model, focusElement goalId )



-- VIEW


goalSizeBase : Int
goalSizeBase =
    28


lineSizeBase : Int
lineSizeBase =
    20


jfcSizeBase : Int
jfcSizeBase =
    13


goalBuf : Int
goalBuf =
    2


lineBuf : Int
lineBuf =
    2


jfcBuf : Int
jfcBuf =
    2


lineSize : String -> Int
lineSize =
    fieldSize lineSizeBase lineBuf


goalSize : String -> Int
goalSize =
    fieldSize goalSizeBase goalBuf


jfcSize : String -> Int
jfcSize =
    fieldSize jfcSizeBase jfcBuf


fieldSize : Int -> Int -> String -> Int
fieldSize base buf s =
    let
        len =
            String.length s
    in
    if len > base then
        len + buf

    else
        base


linePlaceholder : Int -> String
linePlaceholder n =
    "Fact#" ++ String.fromInt n


jfcPlaceholder : Int -> String
jfcPlaceholder n =
    "Justification#" ++ String.fromInt n


styledTable2 : String -> List (Attribute msg) -> List (Html msg) -> Html msg
styledTable2 c =
    styled Html.Styled.table
        [ border3 (px 1) dashed (hex "#000000")
        , backgroundColor (hex c)
        , padding2 (px 1) (px 3)
        ]


styledTable3 : String -> List (Attribute msg) -> List (Html msg) -> Html msg
styledTable3 c =
    styled Html.Styled.table
        [ border3 (px 2) solid (hex "#000000")
        , borderRadius (px 5)
        , backgroundColor (hex c)
        , padding2 (px 1) (px 10)
        , margin (px 5)
        ]


styledTable1 : String -> List (Attribute msg) -> List (Html msg) -> Html msg
styledTable1 c =
    styled Html.Styled.table
        [ border3 (px 1) dotted (hex "#614070")
        , borderRadius (px 5)
        , backgroundColor (hex c)
        , padding2 (px 5) (px 10)
        ]


styledTd : Int -> List (Attribute msg) -> List (Html msg) -> Html msg
styledTd n =
    styled Html.Styled.td
        [ fontSize (px 16)
        , fontWeight bold
        , paddingRight (px (toFloat (n * 10) + 5))
        ]


toolbarButton : String -> String -> Bool -> List (Attribute msg) -> List (Html msg) -> Html msg
toolbarButton c1 c2 hv =
    styled Html.Styled.button
        ([ border (px 0)
         , borderRadius (px 3)
         , lineHeight (px 30)
         , textAlign center
         , backgroundColor (hex c1)
         , padding2 (px 5) (px 10)
         , display inlineBlock
         , overflow Css.hidden
         , textOverflow ellipsis
         , whiteSpace noWrap
         , verticalAlign middle
         , outline none
         , Css.disabled
            [ opacity (Css.num 0.6)
            , cursor notAllowed
            ]
         ]
            ++ (if hv then
                    [ hover
                        [ backgroundColor (hex c2)
                        , boxShadow5 (px 0) (px 1) (px 1) (px 0) (rgba 0 0 0 0.24)
                        , cursor pointer
                        ]
                    ]

                else
                    [ cursor auto ]
               )
        )


backButton : String -> String -> List (Attribute msg) -> List (Html msg) -> Html msg
backButton c1 c2 =
    styled Html.Styled.button
        [ Css.position Css.relative
        , Css.display Css.inlineBlock
        , border (px 0)
        , borderRadius (px 3)
        , lineHeight (px 30)
        , textAlign center
        , backgroundColor (hex c1)
        , padding2 (px 5) (px 10)
        , display inlineBlock
        , overflow Css.hidden
        , textOverflow ellipsis
        , whiteSpace noWrap
        , verticalAlign middle
        , outline none
        , cursor pointer
        , hover
            [ backgroundColor (hex c2)
            , boxShadow5 (px 0) (px 1) (px 1) (px 0) (rgba 0 0 0 0.24)
            ]
        , Css.disabled
            [ opacity (Css.num 0.6)
            , cursor notAllowed
            ]
        ]


listButton : Float -> String -> String -> List (Attribute msg) -> List (Html msg) -> Html msg
listButton w c1 c2 =
    styled Html.Styled.button
        [ border (px 0)
        , borderRadius (px 0)
        , Css.width (px w)
        , lineHeight (px 16)
        , textAlign left
        , backgroundColor (hex c1)
        , padding2 (px 5) (px 10)
        , display inlineBlock
        , overflow Css.hidden
        , textOverflow ellipsis
        , whiteSpace noWrap
        , verticalAlign middle
        , outline none
        , cursor pointer
        , hover
            [ backgroundColor (hex c2)
            , boxShadow5 (px 0) (px 1) (px 1) (px 0) (rgba 0 0 0 0.24)
            ]
        , Css.disabled
            [ opacity (Css.num 0.6)
            , cursor notAllowed
            ]
        ]


paddedTd : List (Attribute msg) -> List (Html msg) -> Html msg
paddedTd =
    styled Html.Styled.td
        [ padding2 (px 0) (px 0) ]


lineButton : String -> String -> Bool -> List (Attribute msg) -> List (Html msg) -> Html msg
lineButton c1 c2 hv =
    styled Html.Styled.button
        ([ border3 (px 1) solid (hex "#000000")
         , borderRadius (px 3)

         --, Css.height (px 24)
         , Css.width (px 20)
         , lineHeight (px 22)
         , textAlign center
         , padding2 (px 0) (px 0)
         , backgroundColor (hex "#F0F0F0")
         , display inlineBlock
         , Css.disabled
            [ opacity (Css.num 0.6)
            , cursor notAllowed
            ]
         ]
            ++ (if hv then
                    [ hover
                        [ backgroundColor (hex c2)
                        , boxShadow5 (px 0) (px 1) (px 1) (px 0) (rgba 0 0 0 0.24)
                        , cursor pointer
                        ]
                    ]

                else
                    [ cursor auto ]
               )
        )


styledInput : List (Attribute msg) -> List (Html msg) -> Html msg
styledInput =
    styled Html.Styled.input
        [ fontFamily monospace
        , hover
            [ border3 (px 2) solid (hex "#878686")
            ]
        ]


styledCheck : List (Attribute msg) -> List (Html msg) -> Html msg
styledCheck =
    styled Html.Styled.span
        [ fontFamily monospace
        , fontSize (px 20)
        , hover
            [ fontWeight bold
            ]
        ]


blockCheck : List (Attribute msg) -> List (Html msg) -> Html msg
blockCheck =
    styled Html.Styled.span
        [ fontFamily monospace
        , fontSize (px 10)
        , hover
            [ fontWeight normal
            ]
        ]


dropdown : Float -> String -> String -> String -> List (Attribute msg) -> List (Html msg) -> List (Attribute msg) -> List (Html msg) -> Html msg
dropdown w col1 col2 col3 attr1 html1 attr2 html2 =
    styled Html.Styled.div
        [ Css.position Css.relative
        , Css.display Css.inlineBlock
        , textAlign center
        , Css.hover
            [ Css.Global.descendants
                [ Css.Global.selector ".dropdown__content"
                    [ Css.display Css.block ]
                ]
            ]
        ]
        []
        [ toolbarButton col1 col2 False attr1 html1
        , styled Html.Styled.div
            [ Css.backgroundColor (Css.hex col3)
            , Css.position Css.absolute
            , Css.top <| Css.pct 100
            , Css.display Css.none
            , Css.width <| Css.px w
            , Css.zIndex <| Css.int 1
            ]
            ([ Html.Styled.Attributes.property "className" (Json.Encode.string "dropdown__content") ] ++ attr2)
            html2
        ]


dropdown1 : Float -> String -> String -> String -> List (Attribute msg) -> List (Html msg) -> List (Attribute msg) -> List (Html msg) -> Html msg
dropdown1 w col1 col2 col3 attr1 html1 attr2 html2 =
    styled Html.Styled.div
        [ Css.position Css.relative
        , Css.display Css.inlineBlock
        , textAlign center
        , Css.hover
            [ Css.Global.descendants
                [ Css.Global.selector ".dropdown__content1"
                    [ Css.display Css.block ]
                ]
            ]
        ]
        []
        [ lineButton col1 col2 False attr1 html1
        , styled Html.Styled.div
            [ Css.backgroundColor (Css.hex col3)
            , Css.position Css.absolute
            , Css.top <| Css.pct 100
            , Css.display Css.none
            , Css.width <| Css.px w
            , Css.zIndex <| Css.int 1
            ]
            ([ Html.Styled.Attributes.property "className" (Json.Encode.string "dropdown__content1") ] ++ attr2)
            html2
        ]


popup : String -> String -> List (Attribute msg) -> List (Attribute msg) -> List (Attribute msg) -> List (Html msg) -> Html msg
popup col1 col2 attr1 attr2 attr3 html2 =
    styled Html.Styled.div
        [ padding2 (px 10) (px 10)
        , fontFamily monospace
        , Css.position Css.fixed
        , Css.top (px 0)
        , Css.right (px 0)
        , Css.left (px 0)
        , Css.bottom (px 0)
        , Css.backgroundColor (Css.hex col1)
        ]
        attr1
        [ backButton "#b3c2ff" "#95a7ed" ([ title "Go back to main page" ] ++ attr3) [ text "Go Back" ]
        , styled Html.Styled.div
            [ Css.position Css.absolute
            , Css.width (pct 50)
            , Css.height (pct 50)
            , Css.top (px 0)
            , Css.right (px 0)
            , Css.left (px 0)
            , Css.bottom (px 0)
            , Css.margin Css.auto
            , Css.backgroundColor (Css.hex col2)
            ]
            []
            [ styled Html.Styled.textarea
                [ Css.width (pct 100)
                , Css.height (pct 100)
                , Css.margin Css.auto
                , Css.backgroundColor (Css.hex col2)
                , Css.resize none
                ]
                ([ autofocus True, readonly True ] ++ attr2)
                html2
            ]
        ]


globalDiv : List (Attribute msg) -> List (Html msg) -> Html msg
globalDiv =
    styled Html.Styled.div
        [ padding2 (px 10) (px 10)
        , fontFamily monospace
        ]


spacerDiv : List (Attribute msg) -> List (Html msg) -> Html msg
spacerDiv =
    styled Html.Styled.div
        [ Css.height (px 10) ]


defaultValue : String -> Attribute msg
defaultValue s =
    Html.Styled.Attributes.property "defaultValue" (Json.Encode.string s)


viewLaTeX : String -> Html msg
viewLaTeX str =
    str
        |> String.lines
        |> String.join "\n"
        |> text


view : Model -> Html Msg
view model =
    let
        cfg =
            model.cfg

        pcfg =
            getParserConfig cfg

        res =
            Proof.buildProof cfg.subset pcfg model.goal model.proof

        ( mcheckstate, s, buildstate ) =
            case res of
                -- error building proof
                Err x ->
                    ( Nothing, [ "Error: " ++ x ], [] )

                Ok ( mseq, prf, bstate ) ->
                    let
                        chk =
                            ProofChecking.check cfg.qtype cfg.heuristics cfg.subset ( mseq, prf )

                        ( st, chkmsgs ) =
                            case chk of
                                Ok r ->
                                    ( Just r, ProofChecking.displayProofState cfg.qtype r )

                                Err msg ->
                                    -- redundancy check failed
                                    ( Nothing, [ msg ] )

                        displayprf =
                            [ "Proof:", Proof.displayProof cfg.qtype prf ] ++ chkmsgs
                    in
                    ( st, displayprf, bstate )

        viewqed =
            case mcheckstate of
                Just ( _, _, ( pchk, _ ) ) ->
                    case List.head (List.reverse pchk) of
                        Just (LineQED _ _) ->
                            [ text "✓" ]

                        _ ->
                            []

                _ ->
                    []

        {- -- allows to display proof checking and build state, very useful for debugging
           viewprf =
               List.map (\t -> tr [] [ td [] [ text t ] ]) s

           viewbuild =
               tr [] [ td [] [ text "BuildState:" ] ]
                   :: List.indexedMap (\i t -> tr [] [ td [] [ text (String.fromInt (i + 1) ++ ": " ++ Proof.displayBuildLineState t) ] ]) buildstate
        -}
    in
    if model.error then
        popup "#7d7b8a" "#e7e3ff" [] [] [ onClick MainPage ] [ text model.lasterror ]

    else if model.help then
        popup "#7d7b8a" "#e7e3ff" [] [] [ onClick MainPage ] [ text "All elements provide useful information or tips when hovering over them.\nA new proof line below the current line can be spawned with 'Enter'.\nBoxes open automatically when a line is justified by an assumption or introduces variables.\nTo move between formula and justification field the key 'TAB' can be used.\nLines can be deleted with backspace when they are empty. If that line is within a block the block will be split, i.e., all lines before and after this line will be put into a separate block.\nHovering over the '...' button opens a dropdown menu that allows to delete or move the line or split the box at this point.\nThe toolbar provides buttons to insert premises and conclusion from the goal field into the proof lines, to merge consecutive boxes, to clear the proof, to change the syntax, to toggle replacements, to export the proof (txt or LaTeX), to import a txt proof, or to display this help page.\nError messages or further information can be viewed by hovering over the indicator symbol at the end of a line. A checkmark represents a valid proof step, a warning symbol indicates something that could be improved, an error symbol shows an error (either a parser error or checker error), a black box indicates a finished proof." ]

    else if model.latex then
        popup "#7d7b8a" "#e7e3ff" [] [] [ onClick MainPage ] [ viewLaTeX <| proofToLaTeX model ]

    else
        globalDiv
            []
            [ styledTable1 "#eddeff"
                [ title "Proof Goal" ]
                [ viewGoal model.gsize model.cfg model.goal ]
            , spacerDiv [] []
            , styledTable1 "#e3eeff"
                [ title "Proof Lines" ]
                (viewLines
                    model.lsize
                    model.jfcsize
                    model.cfg
                    model.proof
                    buildstate
                    mcheckstate
                )
            , spacerDiv [] []
            , styledTable1 "#e1f9fc"
                [ title "Toolbox" ]
                (viewTools model.cfg)
            , spacerDiv [] []

            {- , styledTable2 "#e3fcfa"
                   []
                   viewprf
               , spacerDiv [] []
               , styledTable2 "#e3fcfa"
                   []
                   viewbuild
            -}
            ]


displayLogic : Bool -> String
displayLogic fol =
    if fol then
        "Predicate Logic"

    else
        "Propositional Logic"


displayFormat : Bool -> String
displayFormat qtype =
    if qtype then
        "∀x (ϕ)"

    else
        "∀x. ϕ"


displayFormatHint : Bool -> String
displayFormatHint qtype =
    if qtype then
        "binds ψ ⩴ P | P(t,...,t) | t = t | ⊥ | ⊤ | ¬ψ | (ϕ)"

    else
        "binds everything after '.'"


viewTools : Config -> List (Html Msg)
viewTools cfg =
    let
        displayState =
            \x desc ->
                let
                    s =
                        if x then
                            "enabled"

                        else
                            "disabled"
                in
                desc ++ ": " ++ s

        displayToggle =
            \x desc ->
                let
                    s =
                        if x then
                            "Disable"

                        else
                            "Enable"
                in
                s ++ " " ++ desc

        displayStateKw =
            displayState cfg.replacekw "➤ Keywords"

        displayToggleKw =
            displayToggle cfg.replacekw "Keywords"

        displayStateSc =
            displayState cfg.replacesc "➤ Shortcuts"

        displayToggleSc =
            displayToggle cfg.replacesc "Shortcuts"

        displayStateGreek =
            displayState cfg.replacegreek "➤ Greek Letters"

        displayToggleGreek =
            displayToggle cfg.replacegreek "Greek Letters"

        displayStateHeuristics =
            displayState cfg.heuristics "➤ Heuristics"

        displayToggleHeuristics =
            displayToggle cfg.heuristics "Heuristics"

        overview =
            let
                t =
                    displayLogic cfg.fol ++ " [selected]\n"

                terms =
                    "• t ⩴ x | f(t,...,t)\n"

                folformulas =
                    if cfg.qtype then
                        "• ϕ ⩴ P | P(t,...,t) | (t = t) | ⊥ | ⊤ | (¬ϕ) | (ϕ∧ϕ) | (ϕ∨ϕ) | (ϕ⟶ϕ) | (ϕ⟷ϕ) | (∀x ϕ) | (∃x ϕ)\n"

                    else
                        "• ϕ ⩴ P | P(t,...,t) | (t = t) | ⊥ | ⊤ | (¬ϕ) | (ϕ∧ϕ) | (ϕ∨ϕ) | (ϕ⟶ϕ) | (ϕ⟷ϕ) | (∀x. ϕ) | (∃x. ϕ)\n"

                assoc =
                    "• [∧,∨,⟶,⟷] are right associative\n"

                omitouterparens =
                    "• omit outer parentheses\n"

                folprecedence =
                    if cfg.qtype then
                        "• binding precedence: [=] > [¬,∀,∃] > [∧,∨] > [⟶,⟷]\n"

                    else
                        "• binding precedence: [=] > [¬] > [∧,∨] > [⟶,⟷] > [∀,∃]\n"

                propformulas =
                    "ϕ ⩴ p | ⊥ | ⊤ | (¬ϕ) | (ϕ∧ϕ) | (ϕ∨ϕ) | (ϕ⟶ϕ) | (ϕ⟷ϕ)\n"

                propprecedence =
                    "• binding precedence: [¬] > [∧,∨] > [⟶,⟷]\n"
            in
            if cfg.fol then
                t ++ terms ++ folformulas ++ folprecedence ++ omitouterparens ++ assoc

            else
                t ++ propformulas ++ propprecedence ++ omitouterparens ++ assoc

        bg =
            "#beb3ff"

        dropwidth1 =
            if cfg.fol then
                185

            else
                190

        dropwidth2 =
            170

        dropwidth3 =
            80

        dropwidth4 =
            150

        button1a =
            listButton dropwidth1 bg "#ada2e8"

        button1b =
            listButton dropwidth2 bg "#ada2e8"

        button1c =
            listButton dropwidth3 bg "#ada2e8"

        button1d =
            listButton dropwidth4 bg "#ada2e8"

        button2 =
            toolbarButton "#b3c2ff" "#95a7ed" True

        displayConjStrength =
            \b ->
                if b then
                    "stronger than disjunction"

                else
                    "as strong as disjunction"

        displayConjPrec =
            \b ->
                if b then
                    "prec(∧) > prec(∨)"

                else
                    "prec(∧) ＝ prec(∨)"

        displayInputMode =
            \b ->
                if b then
                    "Drag & Drop"

                else
                    "List"

        hovercontent1 =
            [ button1a [ onClick (ToolEvent ToggleLogic), title ("Switch to " ++ displayLogic (not cfg.fol) ++ "\n\n" ++ overview) ] [ text ("➤ Input: " ++ displayLogic cfg.fol) ]
            , button1a [ onClick (ToolEvent ToggleQType), Html.Styled.Attributes.disabled (not cfg.fol), title qtitle ] [ text ("➤ Quantifier format: " ++ displayFormat cfg.qtype) ]
            , button1a [ onClick (ToolEvent ToggleConjStronger), title ("Make conjunction bind " ++ displayConjStrength (not cfg.conjstronger)) ] [ text ("➤ " ++ displayConjPrec cfg.conjstronger) ]
            ]

        hovercontent2 =
            [ button1b [ onClick (ToolEvent ToggleReplaceKW), title (displayToggleKw ++ "\n" ++ Keywords.displayKeywordReplacementsFormatted 4) ] [ text displayStateKw ]
            , button1b [ onClick (ToolEvent ToggleReplaceSC), title (displayToggleSc ++ "\n" ++ Keywords.displayShortcutReplacementsFormatted 4) ] [ text displayStateSc ]
            , button1b [ onClick (ToolEvent ToggleReplaceGreek), title (displayToggleGreek ++ "\n" ++ Keywords.displayGreekLetterReplacementsFormatted 6) ] [ text displayStateGreek ]
            ]

        hovercontent3 =
            [ button1c [ onClick (ToolEvent (Export Txt)), title "Download Text File" ] [ text "➤ txt" ]
            , button1c [ onClick (ToolEvent (Export LaTeX)), title "Show LaTeX Code" ] [ text "➤ LaTeX" ]
            ]

        hovercontent4 =
            [ button1d [ onClick (ToolEvent ToggleInputMode), title ("Switch to " ++ displayInputMode (not cfg.inputmode)) ] [ text ("➤ Mode: " ++ displayInputMode cfg.inputmode) ]
            , button1d [ onClick (ToolEvent ToggleHeuristics), title displayToggleHeuristics ] [ text displayStateHeuristics ]
            ]

        qtitle =
            "Toggle format for quantifiers\n• " ++ displayFormat cfg.qtype ++ " [selected]\n   • Hint: " ++ displayFormatHint cfg.qtype ++ "\n• " ++ displayFormat (not cfg.qtype) ++ "\n   • Hint: " ++ displayFormatHint (not cfg.qtype)
    in
    [ tr []
        [ td [] [ button2 [ onClick (ToolEvent GetPremises), title "Insert premises and conclusion into proof lines" ] [ text "Get Premises" ] ]
        , td [] [ button2 [ onClick (ToolEvent MergeBlocks), title "Merge consecutive boxes" ] [ text "Merge Boxes" ] ]
        , td [] [ button2 [ onClick (ToolEvent ClearProof), title "Delete proof lines" ] [ text "Clear Proof" ] ]
        , td [] [ dropdown dropwidth1 "#b3c2ff" "#95a7ed" bg [ title "" ] [ text "Syntax" ] [] hovercontent1 ]
        , td [] [ dropdown dropwidth2 "#b3c2ff" "#95a7ed" bg [ title "" ] [ text "Replacements" ] [] hovercontent2 ]
        , td [] [ dropdown dropwidth3 "#b3c2ff" "#95a7ed" bg [ title "" ] [ text "Export" ] [] hovercontent3 ]
        , td [] [ button2 [ onClick (ToolEvent Import), title "Import proof from txt file" ] [ text "Import" ] ]
        , td [] [ button2 [ onClick (ToolEvent Help), title "Display help page" ] [ text "Help" ] ]

        --, td [] [ dropdown dropwidth4 "#b3c2ff" "#95a7ed" bg [ title "" ] [ text "Advanced" ] [  ] hovercontent4 ]
        ]
    ]


viewGoal : Int -> Config -> GoalType -> Html Msg
viewGoal gsize cfg g =
    let
        example =
            if cfg.fol then
                "P, Q ⊢ P∧Q"

            else
                "a, b ⊢ a∧b"

        hint =
            "use keyword 'seq' or shortcut ':-' to enter '⊢'"
    in
    tr []
        [ td [] [ styledInput [ id "goal", size gsize, type_ "text", spellcheck False, autocomplete False, title ("Goal field. Enter premises and conclusion.\n• Example: '" ++ example ++ "'\n• Hint: " ++ hint), placeholder "Goal", value g, onInput Goal, onKeyEvent (KeyEvent 0 FieldGoal) ] [] ]
        , td [] [ checkGoal cfg g ]
        ]


checkGoal : Config -> GoalType -> Html Msg
checkGoal cfg g =
    case Parser.run (Formula.sequent (getParserConfig cfg)) g of
        Ok x ->
            styledCheck [ title ("Interpreted as:\n" ++ Formula.displaySeq cfg.qtype x) ] [ text "✓" ]

        Err x ->
            styledCheck [ title ("Error parsing goal. Details:\n" ++ Utils.deadEndsToString x) ] [ text "⛔" ]



-- (frmstring, move)


moveToJfcParser : Parser ( String, Bool )
moveToJfcParser =
    succeed Tuple.pair
        |= oneOf
            [ Parser.chompUntil ";" |> getChompedString
            , Parser.chompUntil "by" |> getChompedString
            ]
        |= (oneOf
                [ symbol ";"
                , symbol "by"
                ]
                |> Parser.andThen (\s -> succeed True)
           )



-- uses 'moveToJfcParser' to get (frmstring, move)


moveToJfc : String -> ( String, Bool )
moveToJfc s =
    case Parser.run moveToJfcParser s of
        Ok ( str, b ) ->
            ( str, b )

        Err _ ->
            ( s, False )



-- (jfcstring, move)


moveToFrmParser : Parser ( String, Bool )
moveToFrmParser =
    succeed Tuple.pair
        |= (Parser.chompUntil ";" |> getChompedString)
        |= (symbol ";" |> Parser.andThen (\s -> succeed True))



-- uses 'moveToFrmParser' to get (jfcstring, move)


moveToFrm : String -> ( String, Bool )
moveToFrm s =
    case Parser.run moveToFrmParser s of
        Ok ( str, b ) ->
            ( str, b )

        Err _ ->
            ( s, False )


addElementIf : Bool -> Html msg -> List (Html msg) -> List (Html msg)
addElementIf b btn xs =
    if b then
        xs ++ [ btn ]

    else
        xs


addElement : Html msg -> List (Html msg) -> List (Html msg)
addElement =
    addElementIf True


log10Helper : Int -> Int -> Int -> Int
log10Helper i acc x =
    let
        n =
            acc * 10
    in
    if n > x then
        Basics.max 0 (i - 1)

    else if n < x then
        log10Helper (i + 1) n x

    else
        i


log10 : Int -> Int
log10 =
    log10Helper 1 1


lineNumberSpacing : Int -> Int -> Int
lineNumberSpacing len n =
    log10 len - log10 n



-- display a single proof line together with build & checking information


viewLine : Int -> Int -> Config -> Int -> Maybe BuildLineState -> Maybe ProofCheck -> ( ( Int, Int ), ( String, String ), Bool ) -> Html Msg
viewLine lsize jfcsize cfg len mbuildstate mcheckstate l =
    let
        ( ( n, _ ), c, inblock ) =
            l

        ( sf, sj ) =
            c

        dropwidth =
            100

        bg =
            "#e8e8e8"

        button =
            listButton dropwidth bg "#adadad"

        hovercontent =
            []
                |> addElementIf (n /= len) (button [ onClick (MoveEvent n MoveDown), title "" ] [ text "Move Down" ])
                |> addElementIf (n > 1) (button [ onClick (MoveEvent n MoveUp), title "" ] [ text "Move Up" ])
                |> addElementIf (len > 1) (button [ onClick (LineEvent n DeleteLine), title "" ] [ text "Delete Line" ])
                |> addElementIf inblock (button [ onClick (BoxEvent n SplitBox), title "" ] [ text "Split Box" ])

        factexample =
            if cfg.fol then
                "P∧Q"

            else
                "a∧b"

        facthint =
            "use key 'TAB', keyword 'by' or shortcut ';' to jump to justification field"

        facttitle =
            "Fact field. Enter a formula you want to derive. \n• Example: '" ++ factexample ++ "'\n• Hint : " ++ facthint

        jfcexample =
            "∧i"

        jfchint =
            "use key 'TAB' or shortcut ';' to quickly jump to the fact field"

        jfctitle =
            "Justification field. How is the fact derived?\n• Example: '" ++ jfcexample ++ "'\n• Hint: " ++ jfchint

        displayDeps =
            \deps ->
                deps
                    |> List.filter
                        (\d ->
                            case d of
                                None ->
                                    False

                                _ ->
                                    True
                        )
                    |> (\ds ->
                            case ds of
                                [] ->
                                    ""

                                d :: [] ->
                                    case d of
                                        None ->
                                            ""

                                        LineNo _ ->
                                            "Referenced Line: " ++ ProofChecking.displayFactPos d

                                        Range _ _ ->
                                            "Referenced Lines: " ++ ProofChecking.displayFactPos d

                                _ ->
                                    "Referenced Lines: " ++ ProofChecking.displayFactPositions ds
                       )

        displayVersion =
            \ver ->
                let
                    v =
                        ProofChecking.displayRuleVersion ver
                in
                if String.isEmpty v then
                    ""

                else
                    "Rule Version: " ++ v

        displaySuccess =
            \deps ver ->
                let
                    d =
                        displayDeps deps

                    v =
                        displayVersion ver
                in
                if String.isEmpty d && String.isEmpty v then
                    ""

                else
                    "Checker:\n" ++ d ++ "\n" ++ v

        displayQED =
            \deps ver ->
                let
                    d =
                        displayDeps deps

                    v =
                        displayVersion ver

                    base =
                        "Checker:\nLine successfully derives proof goal."
                in
                base ++ "\n" ++ d ++ "\n" ++ v

        chkmsg =
            \varfix lineinterpretation mbuildwarning ->
                let
                    interpreted =
                        "Interpreted as:\n" ++ lineinterpretation

                    basemsg =
                        case mbuildwarning of
                            Nothing ->
                                interpreted

                            Just wmsg ->
                                interpreted ++ "\n\nBuilder:\n" ++ wmsg
                in
                -- able to parse line, check state of line (returned from checker)
                if varfix then
                    styledCheck [ title basemsg ] [ text "✓" ]

                else
                    case mcheckstate of
                        Just chk ->
                            case chk of
                                LineSuccess deps ver ->
                                    styledCheck [ title (basemsg ++ "\n\n" ++ displaySuccess deps ver) ] [ text "✓" ]

                                LineQED deps ver ->
                                    styledCheck [ title (basemsg ++ "\n\n" ++ displayQED deps ver) ] [ text "∎" ]

                                LineError msg ->
                                    styledCheck [ title (basemsg ++ "\n\nChecker:\n" ++ msg) ] [ text "⛔" ]

                                LineWarning msg ->
                                    styledCheck [ title (basemsg ++ "\n\nChecker:\n" ++ msg) ] [ text "⚠" ]

                        Nothing ->
                            styledCheck [ title (basemsg ++ "\n\nChecker:\nFix other errors first!") ] [ text "⚠" ]

        ( vfix, check ) =
            case mbuildstate of
                Nothing ->
                    ( False, chkmsg False "?" Nothing )

                Just buildstate ->
                    case buildstate of
                        BuildError msg ->
                            -- build error / parsing the line failed, no need to look into deeper errors/warnings
                            ( False, styledCheck [ title ("Builder:\n" ++ msg) ] [ text "⛔" ] )

                        BuildWarning msg interpretation ->
                            ( False, chkmsg False interpretation (Just msg) )

                        BuildOk varfix interpretation ->
                            ( varfix, chkmsg varfix interpretation Nothing )
    in
    Html.Styled.table []
        [ tr [ css [ whiteSpace noWrap ] ]
            (styledTd (lineNumberSpacing len n) [ title "Line Number" ] [ text (String.fromInt n ++ ". ") ]
                :: [ td []
                        [ styledInput
                            [ id (frmId n)
                            , size lsize
                            , type_ "text"
                            , spellcheck False
                            , autocomplete False
                            , title facttitle
                            , placeholder (linePlaceholder n)
                            , value sf
                            , onInput
                                (\s ->
                                    case moveToJfc s of
                                        ( str, b ) ->
                                            LineEvent n (ModifyLineFrm str b)
                                )
                            , onKeyEvent (KeyEvent n FieldFrm)
                            ]
                            []
                        ]
                   , td []
                        [ styledInput
                            [ id (jfcId n)
                            , size jfcsize
                            , type_ "text"
                            , spellcheck False
                            , autocomplete False
                            , title jfctitle
                            , placeholder
                                (if vfix then
                                    "fix"

                                 else
                                    jfcPlaceholder n
                                )
                            , value sj
                            , onInput
                                (\s ->
                                    case moveToFrm s of
                                        ( str, b ) ->
                                            LineEvent n (ModifyLineJfc str b)
                                )
                            , onKeyEvent (KeyEvent n FieldJfc)
                            , Html.Styled.Attributes.disabled vfix
                            ]
                            []
                        ]
                   , td [ css [ whiteSpace normal ] ] ([] |> addElementIf (hovercontent /= []) (dropdown1 dropwidth "#b3c2ff" "#95a7ed" bg [ title "" ] [ text "..." ] [] hovercontent))
                   , td [] [ check ]
                   ]
            )
        ]



-- helper to display proof lines together with build & checking information; what makes this a bit complex is that the checked proof diverges from the typed proof since lines that could not be parsed or just fix a variable are not included; hence, the references returned by the checker have to be corrected


viewLinesHelper : Int -> Int -> Bool -> RawProof -> ( ( Int, Int ), ( Config, Int, BuildState ), ( List ProofCheck, List ( BlockCheck, FactPos ), List (Html Msg) ) ) -> ( ( Int, Int ), ( Config, Int, BuildState ), ( List ProofCheck, List ( BlockCheck, FactPos ), List (Html Msg) ) )
viewLinesHelper lsize jfcsize inblock prf state =
    let
        ( ( i, offset ), ( cfg, len, buildstate ), ( pcheck, bcheck, msgs ) ) =
            state
    in
    case prf of
        RawStep frm jfc ->
            let
                ( mbuildstate, buildrest, skipcheck ) =
                    case buildstate of
                        [] ->
                            ( Nothing, [], False )

                        b :: bs ->
                            case b of
                                BuildOk varfix _ ->
                                    ( Just b, bs, varfix )

                                BuildError _ ->
                                    ( Just b, bs, True )

                                BuildWarning _ _ ->
                                    ( Just b, bs, False )

                newoffset =
                    if skipcheck then
                        offset + 1

                    else
                        offset

                ( thisblock, remainingblocks ) =
                    List.partition
                        (\( _, factpos ) ->
                            case factpos of
                                Range begin _ ->
                                    begin + newoffset == i + 1

                                _ ->
                                    False
                        )
                        bcheck

                blockmsg =
                    case thisblock of
                        ( b, _ ) :: _ ->
                            let
                                bmsg =
                                    \m ->
                                        [ tr [] [ td [] [ blockCheck [] [ text m ] ] ] ]
                            in
                            case b of
                                BlockError msg ->
                                    bmsg msg

                                BlockWarning msg ->
                                    bmsg msg

                                _ ->
                                    []

                        _ ->
                            []

                -- in case that the line only fixes vars OR could not be converted into a step, we do not get proofchecking information since this line is not represented in the proof type
                -- hence, we also have to correct line number references
                -- currently does not include the skipped line in 'Range j k'
                updateDeps =
                    \deps ->
                        deps
                            |> List.map
                                (\d ->
                                    case d of
                                        None ->
                                            None

                                        LineNo k ->
                                            if k >= i + 1 then
                                                k
                                                    + 1
                                                    |> LineNo

                                            else
                                                d

                                        Range j k ->
                                            let
                                                newj =
                                                    if j >= i + 1 then
                                                        j + 1

                                                    else
                                                        j

                                                newk =
                                                    if k >= i + 1 then
                                                        k + 1

                                                    else
                                                        k
                                            in
                                            Range newj newk
                                )

                ( mcheck, checkrest ) =
                    case pcheck of
                        [] ->
                            ( Nothing, [] )

                        c :: cs ->
                            if skipcheck then
                                pcheck
                                    |> List.map
                                        (\p ->
                                            case p of
                                                LineSuccess deps msg ->
                                                    deps
                                                        |> updateDeps
                                                        |> (\ds -> LineSuccess ds msg)

                                                LineQED deps msg ->
                                                    deps
                                                        |> updateDeps
                                                        |> (\ds -> LineQED ds msg)

                                                _ ->
                                                    p
                                        )
                                    |> (\pc ->
                                            ( Nothing, pc )
                                       )

                            else
                                ( Just c, cs )
            in
            ( ( i + 1, newoffset ), ( cfg, len, buildrest ), ( checkrest, remainingblocks, msgs ++ blockmsg ++ [ viewLine lsize jfcsize cfg len mbuildstate mcheck ( ( i + 1, newoffset ), ( frm, jfc ), inblock ) ] ) )

        RawBlock ps ->
            -- pack block into a new table
            let
                blockstate =
                    ( ( i, offset ), ( cfg, len, buildstate ), ( pcheck, bcheck, [] ) )

                ( ( j, boffset ), ( _, _, buildrest ), ( cs, bs, bmsgs ) ) =
                    List.foldl (viewLinesHelper lsize jfcsize True) blockstate ps

                tableblock =
                    [ styledTable3 "#e3eeff" [ title "" ] bmsgs
                    ]
            in
            ( ( j, boffset ), ( cfg, len, buildrest ), ( cs, bs, msgs ++ tableblock ) )

        RawBegin ps ->
            List.foldl (viewLinesHelper lsize jfcsize False) state ps



-- display proof lines with build & checking information


viewLines : Int -> Int -> Config -> RawProof -> BuildState -> Maybe CheckState -> List (Html Msg)
viewLines lsize jfcsize cfg prf buildstate mcheckstate =
    let
        len =
            proofLength prf
    in
    case mcheckstate of
        Just st ->
            let
                ( linestate, blockstate ) =
                    ProofChecking.stateToResult st
            in
            viewLinesHelper lsize jfcsize False prf ( ( 0, 0 ), ( cfg, len, buildstate ), ( linestate, blockstate, [] ) )
                |> (\( _, _, ( _, _, msgs ) ) -> msgs)

        Nothing ->
            viewLinesHelper lsize jfcsize False prf ( ( 0, 0 ), ( cfg, len, buildstate ), ( [], [], [] ) )
                |> (\( _, _, ( _, _, msgs ) ) -> msgs)
