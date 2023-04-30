port module Main exposing (main)

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
    receiveCaretPos ReceivedCaretPosFromJS



-- PORTS (for communicating with JS)


port requestCaretPos : String -> Cmd msg


port requestCaretCorrection : Json.Encode.Value -> Cmd msg


port receiveCaretPos : (Json.Encode.Value -> msg) -> Sub msg



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
    | Left
    | Right
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

        37 ->
            Left

        38 ->
            Up

        39 ->
            Right

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
    | EndBox
    | ExtendBox


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
    | ReceivedCaretPosFromJS Json.Encode.Value
    | NOP



-- rerun keyword replacement on goal (whenever cfg changes)


updateGoal : Config -> GoalType -> GoalType
updateGoal cfg goal =
    goal
        |> Keywords.replaceKeywords cfg.replacesc cfg.replacekw cfg.replacegreek



-- updates part in line 'n' (true: frm, false: jfc)


updateLinesPart : Bool -> Config -> Int -> String -> RawProof -> RawProof
updateLinesPart part cfg n s proof =
    let
        u =
            s

        --Keywords.replaceKeywords cfg.replacesc cfg.replacekw cfg.replacegreek s
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
-- leave block instead of deleting if criteria met


deleteLineIfEmpty : Bool -> Int -> Model -> ( Model, Cmd Msg )
deleteLineIfEmpty leaveblock n model =
    case getLine n model.proof of
        Just ( frm, _, inblock ) ->
            if String.isEmpty frm then
                -- leave block instead of deleting when line ends block
                if leaveblock && endsBlock model.proof n then
                    ( { model | proof = splitRawProof n model.proof }, focusElement (frmId n) )

                else
                    let
                        newproof =
                            updateRawProof n RemoveLine model.proof
                    in
                    ( { model | proof = newproof }
                    , if proofLength newproof >= n then
                        focusElement (frmId n)

                      else
                        focusElement (frmId (n - 1))
                    )

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


frmIdBase : String
frmIdBase =
    "frm"


frmId : Int -> String
frmId n =
    if n == 0 then
        goalId

    else
        frmIdBase ++ String.fromInt n


lineMenuId : Int -> String
lineMenuId n =
    lineMenuIdBase ++ String.fromInt n


lineMenuIdBase : String
lineMenuIdBase =
    "linemenu"


jfcIdBase : String
jfcIdBase =
    "jfc"


jfcId : Int -> String
jfcId n =
    jfcIdBase ++ String.fromInt n


focusElement : String -> Cmd Msg
focusElement id =
    Task.attempt (\_ -> NOP) (Dom.focus id)


defocusElement : String -> Cmd Msg
defocusElement id =
    Task.attempt (\_ -> NOP) (Dom.blur id)


update : Msg -> Model -> ( Model, Cmd Msg )
update msg model =
    -- do NOT do ANY keyword/shortcut replacements directly; instead:
    -- 1) request caret position
    -- 2) when caret position is received, call replacement function for this element
    -- 3) correct the caret position by taking replacement length into account (e.g., keyword 'and' is of length 3; symbol '∧' is of length 1; hence, caret := caret - 2)
    -- 4) request setting the corrected caret position
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
            -- only the caret position of the goal field matters here!
            ( { model | cfg = newcfg, goal = g, proof = updateAllLines newcfg model.proof, gsize = goalSize g }, requestCaretPos goalId )

        BoxEvent n e ->
            case e of
                SplitBox ->
                    ( { model | proof = splitRawProof n model.proof }, focusElement (frmId n) )

                EndBox ->
                    ( { model | proof = endBlock n model.proof }, focusElement (frmId n) )

                ExtendBox ->
                    ( { model | proof = extendBlock n model.proof }, focusElement (frmId n) )

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
                                                Cmd.batch [ focusElement (frmId n), requestCaretPos (frmId n) ]
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
                                                Cmd.batch [ focusElement (jfcId n), requestCaretPos (jfcId n) ]
                                            )
                                       )
                           )

                DeleteLine ->
                    ( { model | proof = deleteLine n model.proof }, focusElement (frmId (n - 1)) )

        KeyEvent n field code ->
            case mapToKey code of
                BackSpace ->
                    case field of
                        -- field empty ==> delete line
                        -- if last line in block, leave block before deleting
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
                    case field of
                        FieldFrm ->
                            ( model, defocusElement (frmId n) )

                        FieldJfc ->
                            ( model, defocusElement (jfcId n) )

                        FieldGoal ->
                            ( model, defocusElement goalId )

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
                    --( { model | proof = mergeBlocks model.proof }, Cmd.none )
                    ( model, Cmd.none )

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

        ReceivedCaretPosFromJS value ->
            case Json.Decode.decodeValue caretDecoder value of
                Ok data ->
                    case idToField data.id of
                        Just ( n, field ) ->
                            case field of
                                FieldGoal ->
                                    let
                                        ( newgoal, cmd ) =
                                            replacementWithCaretCorrection model.cfg goalId data.caret model.goal
                                    in
                                    ( { model | goal = newgoal }, cmd )

                                _ ->
                                    updateLineWithCaretCorrection model n field data.caret

                        Nothing ->
                            ( model, Cmd.none )

                Err err ->
                    ( model, Cmd.none )

        NOP ->
            ( model, Cmd.none )


updateLineWithCaretCorrection : Model -> Int -> Field -> Int -> ( Model, Cmd Msg )
updateLineWithCaretCorrection model n field caret =
    case getLine n model.proof of
        Just ( frm, jfc, _ ) ->
            let
                ( id, s, edit ) =
                    case field of
                        FieldGoal ->
                            ( "invalid", "", EditFormula )

                        FieldFrm ->
                            ( frmId n, frm, EditFormula )

                        FieldJfc ->
                            ( jfcId n, jfc, EditJustification )

                ( new, cmd ) =
                    replacementWithCaretCorrection model.cfg id caret s
            in
            ( { model | proof = updateRawProof n (edit new) model.proof }, cmd )

        Nothing ->
            ( model, Cmd.none )


replacementWithCaretCorrection : Config -> String -> Int -> String -> ( String, Cmd Msg )
replacementWithCaretCorrection cfg id caret s =
    s
        |> Keywords.replaceSingle cfg.replacesc cfg.replacekw cfg.replacegreek
        |> (\( updated, diff, replaced ) ->
                if replaced then
                    ( updated, requestCaretCorrection (encodeCorrection id (caret - diff)) )

                else
                    ( s, Cmd.none )
           )


idToField : String -> Maybe ( Int, Field )
idToField id =
    if String.startsWith goalId id then
        Just ( 0, FieldGoal )

    else if String.startsWith frmIdBase id then
        id
            |> String.dropLeft (String.length frmIdBase)
            |> String.toInt
            |> Maybe.map (\n -> ( n, FieldFrm ))

    else if String.startsWith jfcIdBase id then
        id
            |> String.dropLeft (String.length jfcIdBase)
            |> String.toInt
            |> Maybe.map (\n -> ( n, FieldJfc ))

    else
        Nothing


type alias CaretType =
    { id : String
    , caret : Int
    }


encodeCorrection : String -> Int -> Json.Encode.Value
encodeCorrection id caret =
    Json.Encode.object
        [ ( "id", Json.Encode.string id )
        , ( "caret", Json.Encode.int caret )
        ]


caretDecoder : Json.Decode.Decoder CaretType
caretDecoder =
    Json.Decode.map2 CaretType (Json.Decode.field "id" Json.Decode.string) (Json.Decode.field "caret" Json.Decode.int)


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
                |> String.join "\n    , "

        RawBlock ps ->
            recur ps
                |> Tuple.second
                |> String.join "\n    , "


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
    "goal =\n    \""
        ++ model.goal
        ++ "\"\n\nproof =\n    [ "
        ++ rawProofToString model.proof
        ++ "\n    ]\n\nconfig =\n    {"
        ++ configToString model.cfg
        ++ "}\n"
        |> saveTxt



-- obtain subproofs for LaTeX logicproof


getSubProofs : Model -> BuildState -> Maybe CheckState -> String
getSubProofs model buildstate mcheckstate =
    let
        checkstate =
            case mcheckstate of
                Just ( _, _, ( cs, _ ) ) ->
                    cs

                Nothing ->
                    []
    in
    case model.proof of
        RawBegin ps ->
            getSubProofsHelper model.cfg.qtype ( ( 1, 0, "" ), buildstate, checkstate ) ps
                |> (\( ( _, _, str ), _, _ ) -> str)

        _ ->
            "<~ Error obtaining subproofs! Invalid constructor. ~>"


getSubProofsHelper : Bool -> ( ( Int, Int, String ), BuildState, List ProofCheck ) -> List RawProof -> ( ( Int, Int, String ), BuildState, List ProofCheck )
getSubProofsHelper q =
    List.foldl
        (\step state ->
            let
                ( ( indent, i, str ), bs, cs ) =
                    state

                recurstate =
                    ( ( indent + 1, i, "" ), bs, cs )

                linestate =
                    ( ( indent, i + 1, str ), bs, cs )

                correctstate =
                    \( ( _, ni, nstr ), nbs, ncs ) ->
                        -- state after recursive call (block)
                        ( ( indent, ni, str ++ nstr ), nbs, ncs )

                wrapstr =
                    \before after ( ( nindent, ni, nstr ), nbs, ncs ) ->
                        ( ( nindent, ni, before ++ nstr ++ after ), nbs, ncs )

                updateinfo =
                    \nbs ncs ( ( nindent, ni, nstr ), _, _ ) ->
                        ( ( nindent, ni, nstr ), nbs, ncs )

                addstr =
                    \add ->
                        wrapstr "" add

                indentation =
                    String.repeat indent "\t"
            in
            case step of
                RawStep frm jfc ->
                    let
                        line =
                            Keywords.replaceUnicodeSymbols frm ++ "&" ++ Keywords.replaceAndEscapeUnicodeSymbols jfc

                        defaultline =
                            "\\\\\n" ++ indentation ++ line

                        displayDep =
                            \dep ->
                                case dep of
                                    None ->
                                        ""

                                    LineNo pos ->
                                        String.fromInt pos

                                    Range begin end ->
                                        String.fromInt begin ++ "--" ++ String.fromInt end

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
                                    |> List.map displayDep
                                    |> String.join ","
                                    |> (\s -> " " ++ s)

                        displayGenfs =
                            \genfs ->
                                genfs
                                    |> Formula.displayFormulas q
                                    |> Keywords.replaceUnicodeSymbols
                                    |> (\gen -> " with $" ++ gen ++ "$")

                        displayVer =
                            \ver ->
                                ver
                                    |> ProofChecking.displayRuleVersion
                                    |> (\v -> "$_" ++ v ++ "$")

                        addIfNotNil =
                            \xs sxs s ->
                                if List.isEmpty xs then
                                    s

                                else
                                    s ++ sxs

                        addIfNotDefault =
                            \ver s ->
                                if ProofChecking.verNonDefault ver then
                                    s ++ displayVer ver

                                else
                                    s

                        addinfo =
                            \deps genfs ver ->
                                defaultline
                                    |> addIfNotDefault ver
                                    |> addIfNotNil deps (displayDeps deps)
                                    |> addIfNotNil genfs (displayGenfs genfs)
                                    |> addstr

                        ( skip, rbs ) =
                            case bs of
                                (BuildOk varfix _) :: buildrest ->
                                    ( varfix, buildrest )

                                (BuildError _) :: buildrest ->
                                    ( True, buildrest )

                                (BuildWarning _ _) :: buildrest ->
                                    ( False, buildrest )

                                [] ->
                                    ( False, [] )

                        ( mcheck, checkrest ) =
                            getCheckInfo i skip cs
                    in
                    case mcheck of
                        Just (LineSuccess dependencies genforms version) ->
                            linestate
                                |> addinfo dependencies genforms version
                                |> updateinfo rbs checkrest

                        Just (LineQED dependencies genforms version) ->
                            linestate
                                |> addinfo dependencies genforms version
                                |> updateinfo rbs checkrest

                        _ ->
                            -- ignore errors & warnings here; user wants to export ==> will get proof!
                            linestate
                                |> addstr defaultline
                                |> updateinfo rbs checkrest

                RawBlock ps ->
                    getSubProofsHelper q recurstate ps
                        |> wrapstr ("\\\\\n" ++ indentation ++ "\\begin{subproof}\n") ("\n" ++ indentation ++ "\\end{subproof}\n")
                        |> correctstate

                RawBegin ps ->
                    getSubProofsHelper q recurstate ps
        )



-- empty line in LaTeX proof: "\n\\\\\n"


removeEmptyLines : String -> String
removeEmptyLines =
    String.replace "\n\\\\\n" "\n"


addSpace : String -> String
addSpace =
    String.replace " " "\\;"



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


addSequentSpace : String -> String
addSequentSpace =
    String.replace "⊢" "\\;⊢\\;"



-- currently just: "&" ==> " & "


improveCodeReadability : String -> String
improveCodeReadability =
    String.replace "&" " & "


proofToLaTeX : BuildState -> Maybe CheckState -> Model -> String
proofToLaTeX buildstate mcheckstate model =
    "%\\usepackage{logicproof}\n\n\\begin{center}\n" ++ ("$" ++ (Keywords.replaceUnicodeSymbols (addSequentSpace model.goal) ++ "$\n\n\\begin{logicproof}{3}\n" ++ getSubProofs model buildstate mcheckstate ++ "\n\\end{logicproof}") |> addSpace |> removeBrackets |> removeEmptyLines |> removeEmptyMath |> improveCodeReadability) ++ "\n\n\\end{center}"



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
    32


lineSizeBase : Int
lineSizeBase =
    20


jfcSizeBase : Int
jfcSizeBase =
    11


goalBuf : Int
goalBuf =
    2


lineBuf : Int
lineBuf =
    2


jfcBuf : Int
jfcBuf =
    1


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


goalPlaceholder : String
goalPlaceholder =
    "Premise_1,...,Premise_n ⊢ Conclusion"


frmPlaceholder : String
frmPlaceholder =
    "Formula"


jfcPlaceholder : String
jfcPlaceholder =
    "Justification"


styledTable2 : String -> List (Attribute msg) -> List (Html msg) -> Html msg
styledTable2 c =
    styled Html.Styled.table
        [ fontFamily inherit
        , border3 (px 1) dashed (hex "#000000")
        , backgroundColor (hex c)
        , padding2 (px 1) (px 3)
        ]


styledTable3 : String -> List (Attribute msg) -> List (Html msg) -> Html msg
styledTable3 c =
    styled Html.Styled.table
        [ fontFamily inherit
        , border3 (px 2) solid (hex "#000000")
        , borderRadius (px 5)
        , backgroundColor (hex c)
        , padding2 (px 1) (px 10)
        , margin (px 5)
        ]


styledTable1 : String -> List (Attribute msg) -> List (Html msg) -> Html msg
styledTable1 c =
    styled Html.Styled.table
        [ fontFamily inherit
        , border3 (px 1) dotted (hex "#614070")
        , borderRadius (px 5)
        , backgroundColor (hex c)
        , padding2 (px 5) (px 10)
        ]


styledTd : Int -> List (Attribute msg) -> List (Html msg) -> Html msg
styledTd n =
    styled Html.Styled.td
        [ fontFamily inherit
        , fontSize (px 16)
        , fontWeight bold
        , paddingRight (px (toFloat (n * 10) + 5))
        ]


toolbarButton : String -> String -> Bool -> List (Attribute msg) -> List (Html msg) -> Html msg
toolbarButton c1 c2 hv =
    styled Html.Styled.button
        ([ fontFamilies [ "Arial" ]
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
        [ fontFamilies [ "Arial" ]
        , Css.position Css.relative
        , Css.display Css.inlineBlock
        , border (px 0)
        , borderRadius (px 3)
        , lineHeight (px 30)
        , minWidth (px 100)
        , fontSize (px 14)
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
        [ fontFamilies [ "Arial" ]
        , border (px 0)
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
        [ fontFamily inherit
        , padding2 (px 0) (px 0)
        ]


lineButton : String -> String -> Bool -> List (Attribute msg) -> List (Html msg) -> Html msg
lineButton c1 c2 hv =
    styled Html.Styled.button
        ([ fontFamilies [ "Arial" ]
         , border3 (px 1) solid (hex "#000000")
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
        [ fontFamily inherit
        , hover
            [ border3 (px 2) solid (hex "#878686")
            ]
        ]


styledCheck : List (Attribute msg) -> List (Html msg) -> Html msg
styledCheck =
    styled Html.Styled.span
        [ fontFamily inherit
        , fontSize (px 20)
        , hover
            [ fontWeight bold
            ]
        ]


blockCheck : List (Attribute msg) -> List (Html msg) -> Html msg
blockCheck =
    styled Html.Styled.span
        [ fontFamily inherit
        , fontSize (px 10)
        , hover
            [ fontWeight normal
            ]
        ]


dropdown : Float -> String -> String -> String -> List (Attribute msg) -> List (Html msg) -> List (Attribute msg) -> List (Html msg) -> Html msg
dropdown w col1 col2 col3 attr1 html1 attr2 html2 =
    styled Html.Styled.div
        [ fontFamilies [ "Arial" ]
        , Css.position Css.relative
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
            [ fontFamilies [ "Arial" ]
            , Css.backgroundColor (Css.hex col3)
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
        [ fontFamilies [ "Arial" ]
        , Css.position Css.relative
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
            [ fontFamilies [ "Arial" ]
            , Css.backgroundColor (Css.hex col3)
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
        [ fontFamilies [ "NotoSansMono" ]
        , padding2 (px 10) (px 10)
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
            , Css.width (pct 85)
            , Css.height (pct 85)
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
        [ fontFamilies [ "NotoSansMono" ]
        , padding2 (px 10) (px 10)
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
                        Just (LineQED _ _ _) ->
                            [ text "✓" ]

                        _ ->
                            []

                _ ->
                    []

        sepline =
            "---------------------------------------"

        goaltext =
            "1) Entering the Proof Goal:\n" ++ sepline ++ "\nThe goal is a comma-separated list of premises followed by the symbol '⊢' and the conclusion, i.e, it can be entered according to the format 'P1,...,Pn ⊢ C'. The symbol '⊢' can be entered by typing the keyword 'seq' or using the shortcut ':-'. The premises and the conclusion are formulas in either propositional logic or predicate logic. The icon on the right-hand side of the field (error symbol, warning symbol or check mark) indicates whether the input is syntactically correct; further information is provided by hovering over it."

        frmtext =
            "2) Entering Formulas:\n" ++ sepline ++ "\nPropositional Formulas can be entered according to BNF1: " ++ bnfProp ++ "\nFormulas in predicate logic can be entered according to either BNF2: " ++ bnfFOL1 ++ " or BNF3: " ++ bnfFOL2 ++ " where terms are entered according to " ++ bnfTerm ++ "; the required settings will be chosen automatically by entering the proof goal using a supported syntax. Manual configuration is possible by using the dropdown menu 'Syntax 'in the toolbar and toggling the required options accordingly. This menu also allows to configure the binding precedence of '∧' and '∨'. By default these operators are on the same precedence level. All operators are right associative and parentheses can be omitted according to operator precedence. Using BNF1 the default operator precedence is " ++ precPropDefault ++ "; for BNF2 it is " ++ precFOL1Default ++ "; and for BNF3 it is " ++ precFOL2Default ++ ". Operators can be entered using (common) keywords/shortcuts (listed in section 4 under 'replacements')."

        linetext =
            "3) Entering Proof Lines:\n" ++ sepline ++ "\nEvery proof line consists of two input fields: the formula that should be derived and a justification (rule) how to derive it. In order to switch between these fields the key 'TAB' or the shortcut ';' can be used; another option is to use the keyword 'by' in the formula field, i.e., using 'formula by' will remove the keyword 'by' and jump to the justification field. The following justifications are accepted: " ++ Proof.displayAllowedJustifications FOL ++ ". The icon on the right-hand side of the line (error symbol, warning symbol, check mark, black box) indicates whether the input is syntactically correct and the formula can be derived in the current context; further information is provided by hovering over it. The required line number references will be inferred automatically and are displayed on the right-hand side of the icon. Boxes are opened automatically when variables are fixed or when an assumption is introduced. Variables can be fixed by stating them between brackets, e.g., as '[x0]' to fix the variable 'x0'. A formula can be stated on the same line if desired, e.g., '[x0] P(x0)'. If the line only fixes variables then no justification is required. New lines can be spawned below the current line using the key 'ENTER'. In order to leave a box the key 'BACKSPACE' can be used in the last (empty) line of the box. Other empty lines will be deleted directly when 'BACKSPACE' is used in the formula field. A line also offers a dropdown menu ('...') that allows to move or delete lines and provides options to extend the range of a box ('extend box') or to close a box prematurely ('end box'). These work as follows: 'end box' ends the box after the current line; 'extend box' extends the previous box until the current line."

        tooltext =
            "4) Toolbar:\n" ++ sepline ++ "\n* Get Premises: inserts premises and conclusion from the (syntactically correct) goal into the proof lines; if the proof is non-empty the premises will be added before and the conclusion after the already filled-in lines; the goal is interpreted during this process and thus the inserted formulas may differ from the formulas in the goal field by adding explicit parentheses\n* Clear Proof: deletes all proof lines\n* Syntax: opens dropdown menu to toggle syntax settings; choose propositional or predicate logic; choose quantifier syntax; choose if '∧' should bind stronger than '∨'\n* Replacements: opens dropdown menu to toggle automatic replacements of keywords, shortcuts and greek letters; the following replacements are possible: " ++ Keywords.displayAllAcceptedReplacements ++ " where the first element is the symbol and the second element is a set of possible keywords/shortcuts to enter the symbol\n* Export: exports the stated proof either as a text file (that can also be imported and stores the current settings as well; this file is downloaded directly) or as a LaTeX proof (opens an overlay where the LaTeX code is displayed)\n* Import: imports a proof (that has been exported previously)\n* Help: displays this page"

        errtext =
            "5) Error Messages:\n" ++ sepline ++ "\nAll error messages have to be viewed by hovering over the corresponding warning/error icon. The tool consists of two core parts: the builder (parses lines and builds a proof of a type suitable for the proof checker) and the checker (checks proof for correctness). The builder can only fail due to syntactical mistakes, the corresponding parser error message will tell you what symbol it expects at which position in the string. If it expects some kind of string (propositional atom, predicate symbol, variable, function symbol) it will just tell you that it expects 'var'. There are many different errors that can occur while checking the proof, e.g., if some dependencies (premises required by the stated rule) cannot be found, a message of the form 'Facts were not found: f1,...,fn' will be displayed. A missing fact does not necessarily mean that no candidates (formulas of the correct shape) were available for this rule premise, it means that the constraints could not be satisfied (finding other premises that depend on this premise). These error messages may contain placeholders for formulas ('?ϕ'), variables ('?v') or terms (?t) that correspond with the internal/abstract representation of a rule."

        bugtext =
            "6) Known Bugs:\n" ++ sepline ++ "\n* Font Dependency: the text when hovering over elements (e.g., check mark icon) is set by the HTML title attribute and thus the style/font is fully controlled by the user's web browser; some unicode symbols may not be displayed correctly due to the chosen font\n* Reference Offset: line number references may be displayed incorrectly if the proof contains boxes that only fix variables and contain no other syntactically correct lines\n* Box Messages: error messages and warnings regarding boxes may not be displayed at the correct position, i.e., they are not necessarily displayed in the box they refer to"

        helptext =
            goaltext ++ "\n\n" ++ frmtext ++ "\n\n" ++ linetext ++ "\n\n" ++ tooltext ++ "\n\n" ++ errtext ++ "\n\n" ++ bugtext


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
        popup "#7d7b8a" "#e7e3ff" [] [] [ onClick MainPage ] [ text helptext ]

    else if model.latex then
        popup "#7d7b8a" "#e7e3ff" [] [] [ onClick MainPage ] [ viewLaTeX <| proofToLaTeX buildstate mcheckstate model ]

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
                [ title "Toolbar" ]
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

bnfProp : String
bnfProp =
    "ϕ ⩴ p | ⊥ | ⊤ | (¬ϕ) | (ϕ∧ϕ) | (ϕ∨ϕ) | (ϕ⟶ϕ) | (ϕ⟷ϕ)"

bnfTerm : String
bnfTerm =
    "t ⩴ x | f(t,...,t)"

bnfFOL1 : String
bnfFOL1 =
    "ϕ ⩴ P | P(t,...,t) | (t = t) | ⊥ | ⊤ | (¬ϕ) | (ϕ∧ϕ) | (ϕ∨ϕ) | (ϕ⟶ϕ) | (ϕ⟷ϕ) | (∀x ϕ) | (∃x ϕ)"

bnfFOL2 : String
bnfFOL2 =
    "ϕ ⩴ P | P(t,...,t) | (t = t) | ⊥ | ⊤ | (¬ϕ) | (ϕ∧ϕ) | (ϕ∨ϕ) | (ϕ⟶ϕ) | (ϕ⟷ϕ) | (∀x. ϕ) | (∃x. ϕ)"

displayBNF : Config -> String
displayBNF cfg =
    if cfg.fol then
        if cfg.qtype then
            bnfFOL1
        else
            bnfFOL2

    else
        bnfProp


precPropDefault : String
precPropDefault =
    "{¬} > {∧,∨} > {⟶,⟷}"

precFOL1Default : String
precFOL1Default =
    "{=} > {¬,∀,∃} > {∧,∨} > {⟶,⟷}"

precFOL2Default : String
precFOL2Default =
    "{=} > {¬} > {∧,∨} > {⟶,⟷} > {∀,∃}"

displayPrecedence : Config -> String
displayPrecedence cfg =
    if cfg.fol then
        if cfg.qtype then
            if cfg.conjstronger then
                "{=} > {¬,∀,∃} > {∧} > {∨} > {⟶,⟷}"

            else
                precFOL1Default
        else if cfg.conjstronger then
            "{=} > {¬} > {∧} > {∨} > {⟶,⟷} > {∀,∃}"

        else
            precFOL2Default

    else if cfg.conjstronger then
        "{¬} > {∧} > {∨} > {⟶,⟷}"

    else
        precPropDefault

displayAssociativity : String
displayAssociativity =
    "{∧,∨,⟶,⟷} are right associative"


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
                    "• " ++ bnfTerm ++ "\n"

                bnf =
                    displayBNF cfg

                formulas =
                    "• " ++ bnf ++ "\n"

                assoc =
                    "• " ++ displayAssociativity ++ "\n"

                omitouterparens =
                    "• omit outer parentheses\n"

                precedence =
                    "• binding precedence: " ++ displayPrecedence cfg ++ "\n"
            in
            if cfg.fol then
                t ++ terms ++ formulas ++ precedence ++ omitouterparens ++ assoc

            else
                t ++ formulas ++ precedence ++ omitouterparens ++ assoc

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
            [ button1a [ onClick (ToolEvent ToggleLogic), title ("Switch to " ++ displayLogic (not cfg.fol) ++ "\n\n" ++ overview) ] [ text ("➤ " ++ displayLogic cfg.fol) ]
            ]
                |> addElementIf cfg.fol (button1a [ onClick (ToolEvent ToggleQType), title qtitle ] [ text ("➤ Quantifier format: " ++ displayFormat cfg.qtype) ])
                |> addElement (button1a [ onClick (ToolEvent ToggleConjStronger), title ("Make conjunction bind " ++ displayConjStrength (not cfg.conjstronger)) ] [ text ("➤ " ++ displayConjPrec cfg.conjstronger) ])

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
            "Toggle format for quantifiers\n• " ++ displayFormat cfg.qtype ++ " [selected]\n   • " ++ displayFormatHint cfg.qtype ++ "\n• " ++ displayFormat (not cfg.qtype) ++ "\n   • " ++ displayFormatHint (not cfg.qtype)
    in
    [ tr []
        [ td [] [ button2 [ onClick (ToolEvent GetPremises), title "Insert premises and conclusion into proof lines" ] [ text "Get Premises" ] ]

        --, td [] [ button2 [ onClick (ToolEvent MergeBlocks), title "Merge consecutive boxes" ] [ text "Merge Boxes" ] ]
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

        ( inputok, checkmsg ) =
            checkGoal cfg g

        hint =
            "use keyword 'seq' or shortcut ':-' to enter '⊢'"

        titlemsg =
            if inputok then
                ""

            else
                "State the Goal. Enter premises and conclusion.\n• example: '" ++ example ++ "'\n• " ++ hint ++ "\n• " ++ displayBNF cfg ++ "\n• " ++ displayPrecedence cfg ++ "\n• " ++ displayAssociativity
    in
    tr []
        [ td [] [ styledInput [ id "goal", size gsize, type_ "text", spellcheck False, autocomplete False, title titlemsg, placeholder goalPlaceholder, value g, onInput Goal, onKeyEvent (KeyEvent 0 FieldGoal) ] [] ]
        , td [] [ checkmsg ]
        ]


checkGoal : Config -> GoalType -> ( Bool, Html Msg )
checkGoal cfg g =
    case Parser.run (Formula.sequent (getParserConfig cfg)) g of
        Ok x ->
            ( True, styledCheck [ title ("Interpreted as:\n" ++ Formula.displaySeq cfg.qtype x) ] [ text "✓" ] )

        Err x ->
            ( False, styledCheck [ title ("Error parsing goal. Details:\n" ++ Utils.deadEndsToString x) ] [ text "⛔" ] )



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


viewLine : Int -> Int -> Config -> Int -> Maybe BuildLineState -> Maybe ProofCheck -> ( ( Int, Int ), ( String, String ), ( Bool, Bool, Bool ) ) -> Html Msg
viewLine lsize jfcsize cfg len mbuildstate mcheckstate l =
    let
        ( ( n, _ ), ( sf, sj ), ( inblock, lastinblock, blockbefore ) ) =
            l

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
                |> addElementIf blockbefore (button [ onClick (BoxEvent n ExtendBox), title "" ] [ text "Extend Box" ])
                |> addElementIf (inblock && not lastinblock) (button [ onClick (BoxEvent n EndBox), title "" ] [ text "End Box" ])

        --|> addElementIf inblock (button [ onClick (BoxEvent n SplitBox), title "" ] [ text "Split Box" ])
        factexample =
            if cfg.fol then
                "P∧Q"

            else
                "p∧q"

        frmhint1 =
            "use key 'TAB', keyword 'by' or shortcut ';' to jump to the justification field"

        frmtitle =
            "Enter a formula you want to derive. \n• example: '" ++ factexample ++ "'\n• " ++ frmhint1 ++ "\n• " ++ displayBNF cfg ++ "\n• " ++ displayPrecedence cfg ++ "\n• " ++ displayAssociativity

        jfcexample =
            "∧i"

        jfchint =
            "use key 'TAB' or shortcut ';' to quickly jump to the formula field"

        jfctitle =
            "Justify the formula. How can it be derived?\n• example: '" ++ jfcexample ++ "'\n• " ++ jfchint ++ "\n• accepted justifications: " ++ Proof.displayAllowedJustifications cfg.subset

        filteredDeps =
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

        depsUsed =
            \deps ->
                deps
                    |> filteredDeps
                    |> List.isEmpty
                    |> not

        displayDepsRaw =
            \deps ->
                deps
                    |> filteredDeps
                    |> ProofChecking.displayFactPositions

        displayDepsInline =
            \deps ->
                "using " ++ displayDepsRaw deps

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

        displayGeneralized =
            \gen ->
                let
                    g =
                        Formula.displayFormulas cfg.qtype gen
                in
                if String.isEmpty g then
                    ""

                else
                    "Intermediate form: " ++ g

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
            \deps gen ver ->
                let
                    d =
                        displayDeps deps

                    v =
                        displayVersion ver

                    g =
                        displayGeneralized gen
                in
                if String.isEmpty d && String.isEmpty v then
                    ""

                else if String.isEmpty g then
                    "Checker:\n" ++ d ++ "\n" ++ v

                else
                    "Checker:\n" ++ d ++ "\n" ++ g ++ "\n" ++ v

        displayQED =
            \deps gen ver ->
                let
                    d =
                        displayDeps deps

                    v =
                        displayVersion ver

                    g =
                        displayGeneralized gen

                    base =
                        "Checker:\nLine successfully derives proof goal."
                in
                if String.isEmpty g then
                    base ++ "\n" ++ d ++ "\n" ++ v

                else
                    base ++ "\n" ++ d ++ "\n" ++ g ++ "\n" ++ v

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
                    ( styledCheck [ title basemsg ] [ text "✓" ], [] )

                else
                    case mcheckstate of
                        Just chk ->
                            case chk of
                                LineSuccess deps genfs ver ->
                                    ( styledCheck [ title (basemsg ++ "\n\n" ++ displaySuccess deps genfs ver) ] [ text "✓" ], deps )

                                LineQED deps genfs ver ->
                                    ( styledCheck [ title (basemsg ++ "\n\n" ++ displayQED deps genfs ver) ] [ text "∎" ], deps )

                                LineError msg ->
                                    ( styledCheck [ title (basemsg ++ "\n\nChecker:\n" ++ msg) ] [ text "⛔" ], [] )

                                LineWarning msg ->
                                    ( styledCheck [ title (basemsg ++ "\n\nChecker:\n" ++ msg) ] [ text "⚠" ], [] )

                        Nothing ->
                            ( styledCheck [ title (basemsg ++ "\n\nChecker:\nFix other errors first!") ] [ text "⚠" ], [] )

        ( vfix, ( check, dependencies ) ) =
            case mbuildstate of
                Nothing ->
                    ( False, chkmsg False "?" Nothing )

                Just buildstate ->
                    case buildstate of
                        BuildError msg ->
                            -- build error / parsing the line failed, no need to look into deeper errors/warnings
                            ( False, ( styledCheck [ title ("Builder:\n" ++ msg) ] [ text "⛔" ], [] ) )

                        BuildWarning msg interpretation ->
                            ( False, chkmsg False interpretation (Just msg) )

                        BuildOk varfix interpretation ->
                            ( varfix, chkmsg varfix interpretation Nothing )
    in
    Html.Styled.table []
        [ tr [ css [ whiteSpace noWrap ] ]
            (styledTd (lineNumberSpacing len n) [ title ("Line #" ++ String.fromInt n) ] [ text (String.fromInt n ++ ". ") ]
                :: [ td []
                        [ styledInput
                            [ id (frmId n)
                            , size lsize
                            , type_ "text"
                            , spellcheck False
                            , autocomplete False
                            , title
                                (if String.isEmpty sf then
                                    frmtitle

                                 else
                                    ""
                                )
                            , placeholder frmPlaceholder
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
                            , title
                                (if String.isEmpty sj then
                                    jfctitle

                                 else
                                    ""
                                )
                            , placeholder
                                (if vfix then
                                    "fix"

                                 else
                                    jfcPlaceholder
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
                   , td [ css [ whiteSpace normal ] ] ([] |> addElementIf (hovercontent /= []) (dropdown1 dropwidth "#b3c2ff" "#95a7ed" bg [ id (lineMenuId n), title "" ] [ text "..." ] [] hovercontent))
                   , td [] [ check ]
                   ]
                |> addElementIf (dependencies |> depsUsed) (td [ css [ fontSize (px 11) ] ] [ text (displayDepsInline dependencies) ])
            )
        ]



-- in case that the line only fixes vars OR could not be converted into a step, we do not get proofchecking information since this line is not represented in the proof type
-- hence, we also have to correct line number references


updateDeps : Int -> List ProofCheck -> List FactPos -> List FactPos
updateDeps i chk deps =
    let
        current =
            i + 1
    in
    deps
        |> List.map
            (\d ->
                case d of
                    None ->
                        None

                    LineNo k ->
                        if k >= current then
                            LineNo (k + 1)

                        else
                            d

                    Range j k ->
                        let
                            newj =
                                if j == current && isOutermostReferencedBlock j k chk then
                                    j

                                else if j >= current then
                                    j + 1

                                else
                                    j

                            newk =
                                if k >= current then
                                    k + 1

                                else
                                    k
                        in
                        Range newj newk
            )



-- check whether block starting at this line is outermost referenced block (that starts at this line)


isOutermostReferencedBlock : Int -> Int -> List ProofCheck -> Bool
isOutermostReferencedBlock begin end =
    List.any
        (\checkline ->
            case checkline of
                LineSuccess deps genfs msg ->
                    deps
                        |> List.any
                            (\d ->
                                case d of
                                    Range b1 e1 ->
                                        b1
                                            == begin
                                            && e1
                                            > end
                                            |> not

                                    _ ->
                                        False
                            )

                LineQED deps genfs msg ->
                    deps
                        |> List.any
                            (\d ->
                                case d of
                                    Range b1 e1 ->
                                        b1
                                            == begin
                                            && e1
                                            > end
                                            |> not

                                    _ ->
                                        False
                            )

                _ ->
                    False
        )



-- corrects all dependencies in given list proofcheck (offset)


correctDepsInChecked : Int -> List ProofCheck -> List ProofCheck
correctDepsInChecked i =
    List.foldl
        (\checkline updated ->
            case checkline of
                LineSuccess deps genfs msg ->
                    deps
                        |> updateDeps i updated
                        |> (\ds -> LineSuccess ds genfs msg)
                        |> (\cl -> updated ++ [ cl ])

                LineQED deps genfs msg ->
                    deps
                        |> updateDeps i updated
                        |> (\ds -> LineQED ds genfs msg)
                        |> (\cl -> updated ++ [ cl ])

                checkerr ->
                    updated ++ [ checkerr ]
        )
        []


getCheckInfo : Int -> Bool -> List ProofCheck -> ( Maybe ProofCheck, List ProofCheck )
getCheckInfo i skipcheck pcheck =
    case pcheck of
        [] ->
            ( Nothing, [] )

        c :: cs ->
            if skipcheck then
                pcheck
                    |> correctDepsInChecked i
                    |> (\pc ->
                            ( Nothing, pc )
                       )

            else
                ( Just c, cs )



-- helper to display proof lines together with build & checking information; what makes this a bit complex is that the checked proof diverges from the typed proof since lines that could not be parsed or just fix a variable are not included; hence, the references returned by the checker have to be corrected


viewLinesHelper : Int -> Int -> Bool -> RawProof -> ( ( Int, Int, ( List Bool, Bool ) ), ( Config, Int, BuildState ), ( List ProofCheck, List ( BlockCheck, FactPos ), List (Html Msg) ) ) -> ( ( Int, Int, ( List Bool, Bool ) ), ( Config, Int, BuildState ), ( List ProofCheck, List ( BlockCheck, FactPos ), List (Html Msg) ) )
viewLinesHelper lsize jfcsize inblock prf state =
    let
        ( ( i, offset, ( ends, blockbefore ) ), ( cfg, len, buildstate ), ( pcheck, bcheck, msgs ) ) =
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
                                    if ProofChecking.proofQED pcheck then
                                        bmsg msg

                                    else
                                        []

                                BlockWarning msg ->
                                    if ProofChecking.proofQED pcheck then
                                        bmsg msg

                                    else
                                        []

                                _ ->
                                    []

                        _ ->
                            []

                ( mcheck, checkrest ) =
                    getCheckInfo i skipcheck pcheck

                ( lastinblock, endsrest ) =
                    case ends of
                        [] ->
                            ( False, [] )

                        l :: rest ->
                            ( l, rest )
            in
            ( ( i + 1, newoffset, ( endsrest, blockbefore ) ), ( cfg, len, buildrest ), ( checkrest, remainingblocks, msgs ++ blockmsg ++ [ viewLine lsize jfcsize cfg len mbuildstate mcheck ( ( i + 1, newoffset ), ( frm, jfc ), ( inblock, lastinblock, blockbefore ) ) ] ) )

        RawBlock ps ->
            -- pack block into a new table
            let
                blockstate =
                    ( ( i, offset, ( ends, False ) ), ( cfg, len, buildstate ), ( pcheck, bcheck, [] ) )

                ( ( j, boffset, ( bends, _ ) ), ( _, _, buildrest ), ( cs, bs, bmsgs ) ) =
                    List.foldl (viewLinesHelper lsize jfcsize True) blockstate ps

                tableblock =
                    [ styledTable3 "#e3eeff" [ title "" ] bmsgs
                    ]
            in
            ( ( j, boffset, ( bends, True ) ), ( cfg, len, buildrest ), ( cs, bs, msgs ++ tableblock ) )

        RawBegin ps ->
            List.foldl (viewLinesHelper lsize jfcsize False) state ps



-- display proof lines with build & checking information


viewLines : Int -> Int -> Config -> RawProof -> BuildState -> Maybe CheckState -> List (Html Msg)
viewLines lsize jfcsize cfg prf buildstate mcheckstate =
    let
        len =
            proofLength prf

        ends =
            List.range 1 len
                |> List.map (endsBlock prf)
    in
    case mcheckstate of
        Just st ->
            let
                ( linestate, blockstate ) =
                    ProofChecking.stateToResult st
            in
            viewLinesHelper lsize jfcsize False prf ( ( 0, 0, ( ends, False ) ), ( cfg, len, buildstate ), ( linestate, blockstate, [] ) )
                |> (\( _, _, ( _, _, msgs ) ) -> msgs)

        Nothing ->
            viewLinesHelper lsize jfcsize False prf ( ( 0, 0, ( ends, False ) ), ( cfg, len, buildstate ), ( [], [], [] ) )
                |> (\( _, _, ( _, _, msgs ) ) -> msgs)
