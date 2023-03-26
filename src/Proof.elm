-- this module defines the type of proofs and provides parsers & helper functions


module Proof exposing (..)

import Formula exposing (Formula, Seq)
import Keywords
import List
import ModelDefs exposing (ParserConfig, RuleSubset(..), VarType)
import Parser exposing ((|.), (|=), Parser, backtrackable, end, lazy, oneOf, problem, spaces, succeed, symbol, variable)
import Rule
import Set exposing (Set)
import Utils



-- type for parsing a string into a line
-- 'Line' regular line
-- 'BlockFix' first line in block: only fix variables (no formula)
-- 'BlockLine' first line in block (allows introducing vars)


type LineType
    = Line Formula Justification
    | BlockFix (List VarType)
    | BlockLine (List VarType) Formula Justification



-- type to represent proofs


type Proof
    = Step Formula Justification
    | Block (List VarType) (List Proof)
    | Begin (List Proof)



-- type for justifications


type Justification
    = Premise
    | Assumption
    | JRule String



-- types to keep track of errors while building proof


type BuildLineState
    = BuildOk Bool String -- only var fix, interpretation of line
    | BuildError String -- error msg
    | BuildWarning String String -- warning, interpretation


type alias BuildState =
    List BuildLineState



-- takes set of reserved vars and returns parser for list of vars
-- input of form "[x0,x1,x2]"


vars : ParserConfig -> Set VarType -> Parser (List VarType)
vars cfg rvs =
    Parser.sequence
        { start = "["
        , separator = ","
        , end = "]"
        , spaces = spaces
        , item = Formula.varHelper cfg rvs
        , trailing = Parser.Forbidden
        }



-- list of replacements (accepted justification names, corresponding constructor)


jfcReplacements : List ( List String, Justification )
jfcReplacements =
    [ ( [ "p", "prm", "prem", "premise" ], Premise )
    , ( [ "ass", "asm", "assm", "assumption" ], Assumption )
    ]



-- looks for replacement of given string in 'jfcReplacements'


lookupJustification : RuleSubset -> String -> Maybe Justification
lookupJustification sub s =
    case List.filter (\( xs, _ ) -> List.member s xs) jfcReplacements of
        [] ->
            if List.member s (Rule.currentRuleNames sub) then
                Just (JRule s)

            else
                Nothing

        ( _, j ) :: rs ->
            Just j



-- converts string to result of parsing a justification


convertToJustification : RuleSubset -> String -> Parser Justification
convertToJustification sub s =
    case lookupJustification sub s of
        Nothing ->
            problem ("Illegal justification: '" ++ s ++ "'")

        Just j ->
            succeed j



-- justification parser: accepts string composed of alphanumeric constants and symbols such as '⟶', '∨', etc.


justification : RuleSubset -> Parser Justification
justification sub =
    Parser.getChompedString (Parser.chompWhile (\c -> Char.isAlphaNum c || Keywords.isReplacement c))
        |> Parser.andThen (convertToJustification sub << String.toLower)



-- assumption parser: just checks if jfc is assumption
-- used to split blocks (happens before lines are parsed!)


jfcAssumption : Parser Bool
jfcAssumption =
    succeed identity
        |. spaces
        |= (justification NoRules |> Parser.andThen (\j -> succeed (j == Assumption)))
        |. spaces
        |. end



-- fixingLine parser: just checks if line fixes vars
-- used to avoid splitting blocks (happens before lines are parsed!)


fixingLine : Parser Bool
fixingLine =
    (succeed identity
        |= vars ModelDefs.defaultParserConfig Set.empty
        |. spaces
        |. Parser.chompUntilEndOr "\n"
        |. end
    )
        |> Parser.andThen (\_ -> succeed True)



-- (full) justification parser


jfcParser : RuleSubset -> Parser Justification
jfcParser sub =
    succeed identity
        |. spaces
        |= justification sub
        |. spaces
        |. end



-- parser for regular formula entered in line (not beginning of box)


frmParser : ParserConfig -> Parser Formula
frmParser cfg =
    succeed identity
        |. spaces
        |= Formula.formula cfg
        |. spaces
        |. end



-- parser for formula entered in first line of box
-- input of form: "[x0,x1,x2]" or "[x0,x1,x2] formula" or "formula"


blockFrmParser : ParserConfig -> Set VarType -> Parser ( List VarType, Maybe Formula )
blockFrmParser cfg rvs =
    succeed identity
        |= oneOf
            [ backtrackable
                ((succeed identity
                    |= vars cfg rvs
                    |. spaces
                    |. end
                 )
                    |> Parser.andThen (\vs -> succeed ( vs, Nothing ))
                )

            -- only fix vars in this line
            , succeed Tuple.pair
                |= oneOf
                    [ vars cfg rvs
                    , succeed [] -- vars optional
                    ]
                |. spaces
                |= (Formula.formula cfg |> Parser.andThen (\f -> succeed (Just f)))
                |. spaces
                |. end
            ]



-- parses tuple (frmstr, jfcstr)
-- runs appropriate parser (frmParser | blockFrmParser), chosen according to 'allowVars' and 'fol'
-- returns error or line


parseLine : RuleSubset -> ParserConfig -> Bool -> Set VarType -> ( String, String ) -> Result String LineType
parseLine sub cfg allowVars rvs line =
    let
        ( frmstr, jfcstr ) =
            line

        justify =
            \ctor frm ->
                case Parser.run (jfcParser sub) jfcstr of
                    Ok jfc ->
                        ctor frm jfc |> Ok

                    Err x ->
                        Utils.deadEndsToString x
                            |> Err
    in
    if allowVars && cfg.fol then
        case Parser.run (blockFrmParser cfg rvs) frmstr of
            Ok ( vs, mfrm ) ->
                case mfrm of
                    Nothing ->
                        -- does not require a justification
                        BlockFix vs
                            |> Ok

                    Just frm ->
                        justify (BlockLine vs) frm

            Err x ->
                Utils.deadEndsToString x
                    |> Err

    else
        case Parser.run (frmParser cfg) frmstr of
            Ok frm ->
                justify Line frm

            Err x ->
                Utils.deadEndsToString x
                    |> Err



-- step function for building proof, propagating (fatal) errors


parseLinesStep : RuleSubset -> ParserConfig -> ModelDefs.RawProof -> Result String ( Set VarType, List Proof, BuildState ) -> Result String ( Set VarType, List Proof, BuildState )
parseLinesStep sub cfg s state =
    case state of
        Ok ( rvs, prfs, bstate ) ->
            case parseLinesHelper sub cfg rvs s of
                Ok ( rvsn, mprf, nbstate ) ->
                    case mprf of
                        Just prf ->
                            Ok ( Set.union rvs rvsn, prf :: prfs, bstate ++ nbstate )

                        Nothing ->
                            Ok ( Set.union rvs rvsn, prfs, bstate ++ nbstate )

                Err msg ->
                    Err msg

        Err msg ->
            Err msg



-- helper to parse a raw block into a proof
-- returns error or (reserved vars, proof)


parseBlock : RuleSubset -> ParserConfig -> Bool -> Set VarType -> List ModelDefs.RawProof -> Result String ( Set VarType, Proof, BuildState )
parseBlock sub cfg outermost rvs sprfs =
    case sprfs of
        [] ->
            Err "Empty block!"

        x :: xs ->
            case x of
                -- a block usually starts with a step, optionally introducing vars
                ModelDefs.RawStep sf sj ->
                    -- not allowed to introduce vars in outermost block!
                    let
                        recur =
                            \vs rvsn mstep ->
                                case List.foldl (parseLinesStep sub cfg) (Ok ( rvsn, [], [] )) xs of
                                    Ok ( rvsr, rest, rstate ) ->
                                        let
                                            rs =
                                                List.reverse rest

                                            blocksteps =
                                                case mstep of
                                                    Just step ->
                                                        step :: rs

                                                    Nothing ->
                                                        rs
                                        in
                                        Ok ( rvsr, wrap outermost vs blocksteps, rstate )

                                    Err msg ->
                                        Err msg
                    in
                    case parseLine sub cfg (not outermost) rvs ( sf, sj ) of
                        Ok l ->
                            let
                                ( varfix, ( vs, fvs, mstep ) ) =
                                    case l of
                                        Line frm jfc ->
                                            ( False, ( [], Formula.freeVars frm, Step frm jfc |> Just ) )

                                        BlockFix vs1 ->
                                            ( True, ( vs1, Set.empty, Nothing ) )

                                        BlockLine vs1 frm jfc ->
                                            ( False, ( vs1, Formula.freeVars frm, Step frm jfc |> Just ) )

                                rvsn =
                                    Set.union (Set.union rvs fvs) (Set.fromList vs)
                            in
                            -- return original 'rvs' since reserved vars within the block do not affect anything outside!
                            recur vs rvsn mstep
                                |> Result.map (\( _, prfr, rstate ) -> ( rvs, prfr, BuildOk varfix (displayLine cfg.qtype l) :: rstate ))

                        Err msg ->
                            case recur [] Set.empty Nothing of
                                Ok ( _, prf, state ) ->
                                    Ok ( rvs, prf, BuildError msg :: state )

                                Err msg1 ->
                                    Err msg1

                ModelDefs.RawBegin ys ->
                    Err "Encountered constructor not handled in function 'parseBlock'!"

                -- if we encounter a block as the first thing inside a block, no variables will be introduced
                ModelDefs.RawBlock ys ->
                    case parseBlock sub cfg False rvs ys of
                        -- note that vars introduced inside the block, i.e., in 'ys', do not affect anything in 'xs'
                        Ok ( _, p, state ) ->
                            let
                                init =
                                    Ok ( rvs, [], [] )

                                ps =
                                    List.foldl (parseLinesStep sub cfg) init xs
                            in
                            case ps of
                                Ok ( _, rest, rstate ) ->
                                    let
                                        rs =
                                            List.reverse rest

                                        prf =
                                            (if blockEmpty state then
                                                rs

                                             else
                                                p :: rs
                                            )
                                                |> wrap outermost []
                                    in
                                    Ok ( rvs, prf, state ++ rstate )

                                Err msg ->
                                    Err msg

                        Err msg ->
                            Err msg



-- helper to check whether a block is empty (failed to build everything within block)


blockEmpty : BuildState -> Bool
blockEmpty state =
    state
        |> List.all
            (\st ->
                case st of
                    BuildError _ ->
                        True

                    _ ->
                        False
            )



-- helper to wrap corresponding constructor (Begin/Block) around list of raw proofs


wrap : Bool -> List VarType -> List Proof -> Proof
wrap outermost vs ps =
    if outermost then
        Begin ps

    else
        Block vs ps



-- helper to parse 'ModelDefs.RawProof' into 'Proof'
-- returns error or (reserved vars, proof)


parseLinesHelper : RuleSubset -> ParserConfig -> Set VarType -> ModelDefs.RawProof -> Result String ( Set VarType, Maybe Proof, BuildState )
parseLinesHelper sub cfg rvs sprf =
    case sprf of
        -- note that first line in block is handled in parseBlock directly!
        -- parser errors are captured in the buildstate, only fatal errors are propagated
        ModelDefs.RawStep sf sj ->
            case parseLine sub cfg False rvs ( sf, sj ) of
                Ok l ->
                    case l of
                        Line frm jfc ->
                            Ok ( Formula.freeVars frm, Step frm jfc |> Just, [ BuildOk False (displayLine cfg.qtype l) ] )

                        _ ->
                            Ok ( Set.empty, Nothing, [ BuildError "Encountered constructor not handled in function 'parseLinesHelper'!" ] )

                Err msg ->
                    Ok ( Set.empty, Nothing, [ BuildError msg ] )

        ModelDefs.RawBegin xs ->
            parseBlock sub cfg True rvs xs
                |> Result.map (\( vs, prf, state ) -> ( vs, Just prf, state ))

        ModelDefs.RawBlock xs ->
            parseBlock sub cfg False rvs xs
                |> Result.map (\( vs, prf, state ) -> ( vs, Just prf, state ))



-- parses 'ModelDefs.RawProof' into 'Proof'
-- returns error or proof


parseLines : RuleSubset -> ParserConfig -> Set VarType -> ModelDefs.RawProof -> Result String ( Proof, BuildState )
parseLines sub cfg rvs sprf =
    case parseLinesHelper sub cfg rvs sprf of
        Ok ( _, mprf, state ) ->
            case mprf of
                Nothing ->
                    Err ("Unable to build proof! Details: " ++ displayBuildState state)

                Just prf ->
                    Ok ( prf, state )

        Err msg ->
            Err msg



-- is raw line content justified by assumption?


isAssumption : String -> Bool
isAssumption s =
    Result.withDefault False (Parser.run jfcAssumption s)



-- is raw line fixing vars?


isFixing : String -> Bool
isFixing s =
    Result.withDefault False (Parser.run fixingLine s)



-- splits raw block content into multiple lists at points where line is assumption/fixing
-- input list is content of a block, i.e., everything on same indentation level
-- output list of list of block content


splitRawBlockContentUponAssumption : Int -> List ModelDefs.LineType -> List (List ModelDefs.LineType)
splitRawBlockContentUponAssumption indent xs =
    case xs of
        [] ->
            []

        y :: ys ->
            let
                ( _, ( line, _ ) ) =
                    y

                ( block, rest ) =
                    -- conditions for split, i.e., partitioning a block into several blocks:
                    -- *) no change in indentation
                    -- *) AND line justified by assumption appears LATER THAN in first line
                    -- *) OR line fixing vars appears LATER THAN in first line
                    Utils.rsplit (\( i, ( frm, jfc ) ) -> i == indent && (isAssumption jfc || isFixing frm)) ys
            in
            (y :: block) :: splitRawBlockContentUponAssumption indent rest



-- converts list of lines into helper type 'ModelDefs.RawProof', i.e., into steps and blocks
-- takes current indentation level


splitIntoRawBlocksHelper : Int -> List ModelDefs.LineType -> List ModelDefs.RawProof
splitIntoRawBlocksHelper i ls =
    case ls of
        [] ->
            []

        _ :: _ ->
            let
                -- everything up to an increase in indentation belongs to the current block
                -- however, the next block may close at some point, hence, also 'other' contains steps/blocks that belong in the current block
                ( currentA, other ) =
                    Utils.rsplit (\( j, _ ) -> j > i) ls

                partA =
                    List.map (\( _, ( frm, jfc ) ) -> ModelDefs.RawStep frm jfc) currentA
            in
            case other of
                [] ->
                    partA

                ( indent, _ ) :: _ ->
                    let
                        ( nextblock, currentB ) =
                            Utils.rsplit (\( j, _ ) -> j < indent) other

                        partB =
                            case nextblock of
                                -- cannot happen (no split would happen, i.e., 'other' would be empty)
                                [] ->
                                    [ ModelDefs.RawBlock [] ]

                                ( indentN, _ ) :: _ ->
                                    -- multiple blocks may be placed directly after another (same level of indentation)
                                    -- in case of an assumption: split 'xs' into list of blocks
                                    let
                                        mkBlock =
                                            \ys ->
                                                ModelDefs.RawBlock (splitIntoRawBlocksHelper indentN ys)
                                    in
                                    splitRawBlockContentUponAssumption indentN nextblock
                                        |> List.map mkBlock

                        partC =
                            splitIntoRawBlocksHelper i currentB
                    in
                    partA ++ partB ++ partC



-- converts list of lines into helper type 'ModelDefs.RawProof', i.e., into list of raw steps and raw blocks


splitIntoRawBlocks : List ModelDefs.LineType -> List ModelDefs.RawProof
splitIntoRawBlocks =
    splitIntoRawBlocksHelper 0



-- converts list of lines into a proof
-- returns error or proof


linesToProof : RuleSubset -> ParserConfig -> Set VarType -> List ModelDefs.LineType -> Result String ( Proof, BuildState )
linesToProof sub cfg rvs ls =
    let
        sprf =
            ModelDefs.RawBegin (splitIntoRawBlocks ls)
    in
    parseLines sub cfg rvs sprf



-- remove empty blocks from proof and return maybe proof


mprune : Proof -> Maybe Proof
mprune prf =
    case prf of
        Step _ _ ->
            Just prf

        Block vs ps ->
            let
                xs =
                    prune ps
            in
            if List.isEmpty vs && List.isEmpty xs then
                Nothing

            else
                Just (Block vs xs)

        Begin ps ->
            case prune ps of
                [] ->
                    Nothing

                xs ->
                    Just (Begin xs)



-- transform list of proofs into list of proofs where empty blocks have been removed


prune : List Proof -> List Proof
prune ps =
    ps
        |> List.foldl
            (\p state ->
                case mprune p of
                    Just proof ->
                        state ++ [ proof ]

                    Nothing ->
                        state
            )
            []



-- removes empty blocks from proof, an empty proof is represented by 'Begin []'


removeEmptyBlocks : Proof -> Proof
removeEmptyBlocks prf =
    prf
        |> mprune
        |> (\m ->
                case m of
                    Nothing ->
                        Begin []

                    Just x ->
                        x
           )



-- converts goal line & list of proof lines into a tuple (sequent, proof) if possible
-- in case of error returns msg


buildProof : RuleSubset -> ParserConfig -> ModelDefs.GoalType -> ModelDefs.RawProof -> Result String ( Maybe Seq, Proof, BuildState )
buildProof sub cfg g rawproof =
    let
        seq =
            case Parser.run (Formula.sequent cfg) g of
                Err _ ->
                    Nothing

                Ok x ->
                    Just x

        prems =
            case seq of
                Nothing ->
                    []

                Just x ->
                    Tuple.first x

        rvs =
            prems
                |> List.foldl
                    (\p state ->
                        Set.union state (Formula.freeVars p)
                    )
                    Set.empty

        prfp =
            parseLines sub cfg rvs rawproof
    in
    case prfp of
        -- global error, not captured in buildstate
        Err msg ->
            Err msg

        Ok ( y, state ) ->
            Ok ( seq, y |> removeEmptyBlocks, state )


buildProofFromLines : RuleSubset -> ParserConfig -> ModelDefs.GoalType -> List ModelDefs.LineType -> Result String ( Maybe Seq, Proof, BuildState )
buildProofFromLines sub cfg g ls =
    let
        seq =
            case Parser.run (Formula.sequent cfg) g of
                Err _ ->
                    Nothing

                Ok x ->
                    Just x

        prems =
            case seq of
                Nothing ->
                    []

                Just x ->
                    Tuple.first x

        rvs =
            prems
                |> List.foldl
                    (\p state ->
                        Set.union state (Formula.freeVars p)
                    )
                    Set.empty

        prfp =
            linesToProof sub cfg rvs ls
    in
    case prfp of
        -- global error, not captured in buildstate
        Err msg ->
            Err msg

        Ok ( y, state ) ->
            Ok ( seq, y |> removeEmptyBlocks, state )



-- converts justification to appropriate string


displayJustification : Justification -> String
displayJustification j =
    case j of
        Premise ->
            "premise"

        Assumption ->
            "assumption"

        JRule s ->
            s



-- converts proof to appropriate string


displayProof : Bool -> Proof -> String
displayProof q p =
    case p of
        Step f j ->
            let
                sf =
                    Formula.displayFormula q f

                sj =
                    displayJustification j
            in
            "Step (" ++ sf ++ ") (" ++ sj ++ ")"

        Block vs ps ->
            let
                svs =
                    String.join "," vs

                sps =
                    String.join "," (List.map (displayProof q) ps)
            in
            "Block [" ++ svs ++ "] [" ++ sps ++ "]"

        Begin ps ->
            let
                sps =
                    String.join "," (List.map (displayProof q) ps)
            in
            "Begin [" ++ sps ++ "]"



-- converts line to appropriate string


displayLine : Bool -> LineType -> String
displayLine q l =
    let
        showf =
            \frm ->
                Formula.displayFormula q frm

        showj =
            \jfc ->
                displayJustification jfc

        showfj =
            \frm jfc ->
                showf frm ++ " by " ++ showj jfc

        showvs =
            \vs ->
                "fix " ++ String.join "," vs

        showblock =
            \vs frm jfc ->
                if List.isEmpty vs then
                    showfj frm jfc

                else
                    showvs vs ++ "; " ++ showfj frm jfc
    in
    case l of
        Line frm jfc ->
            showfj frm jfc

        BlockFix vs ->
            showvs vs

        BlockLine vs frm jfc ->
            showblock vs frm jfc



-- converts buildlinestate to appropriate string


displayBuildLineState : BuildLineState -> String
displayBuildLineState b =
    case b of
        BuildOk vfix interpretation ->
            if vfix then
                interpretation ++ ": Ok (fixes vars)"

            else
                interpretation ++ ": Ok"

        BuildWarning msg interpretation ->
            interpretation ++ ": " ++ msg

        BuildError msg ->
            msg


displayBuildState : BuildState -> String
displayBuildState bs =
    bs
        |> List.map displayBuildLineState
        |> String.join ";"
