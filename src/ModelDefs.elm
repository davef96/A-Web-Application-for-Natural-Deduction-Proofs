-- this module provides definitions of types used in the model, and helper functions for processing the proof representation


module ModelDefs exposing (..)

import Keywords



-- MODEL
-- goal of form "p0, ..., pn ⊢ c"


type alias GoalType =
    String



-- type alias to make it more clear we're dealing with vars


type alias VarType =
    String



-- selected rule subset


type RuleSubset
    = NoRules
    | IntProp
    | Prop
    | IntFOL
    | FOL



-- raw proof representation (strings + box information)


type RawProof
    = RawStep String String -- formula justification
    | RawBlock (List RawProof)
    | RawBegin (List RawProof)



-- old representation of proof lines (for compatibility reasons: tests & exported txt)


type alias LineType =
    ( Int, ( String, String ) )



-- type to represent how proof should be modified


type EditRawProof
    = EditFormula String
    | EditJustification String
    | SetLine String String
    | RemoveLine
    | RemoveLineIfEmpty
    | AddLine String String
    | SwapLinesWith Int
    | StartBlock
    | UpdateAll Config
    | CaseConversion Bool



-- proof with 1 empty line (default state when clearing proof)


clearedProof : RawProof
clearedProof =
    RawBegin [ RawStep "" "" ]



-- adds new block to list of raw proofs


addBlock : List RawProof -> List RawProof -> List RawProof
addBlock block ps =
    let
        newblock =
            RawBlock block
    in
    ps ++ [ newblock ]



-- adds new step to list of raw proofs


addStep : ( String, String ) -> List RawProof -> List RawProof
addStep step ps =
    let
        ( frm, jfc ) =
            step

        newstep =
            RawStep frm jfc
    in
    ps ++ [ newstep ]



-- helper to obtain line as tuple ('frm', 'jfc', 'b') from raw proof, flag 'b' indicates whether line is inside a block


getLineHelper : Int -> Int -> RawProof -> ( Int, Maybe ( String, String, Bool ) )
getLineHelper n start proof =
    let
        recur =
            \inside ->
                List.foldl
                    (\step state ->
                        let
                            ( i, line ) =
                                state
                        in
                        case line of
                            Just _ ->
                                state

                            Nothing ->
                                case step of
                                    RawStep frm jfc ->
                                        let
                                            newi =
                                                i + 1

                                            newline =
                                                if newi == n then
                                                    Just ( frm, jfc, inside )

                                                else
                                                    Nothing
                                        in
                                        ( newi, newline )

                                    _ ->
                                        getLineHelper n i step
                    )
                    ( start, Nothing )
    in
    case proof of
        RawStep _ _ ->
            recur False [ proof ]

        RawBegin ps ->
            recur False ps

        RawBlock ps ->
            recur True ps



-- try to obtain line as tuple ('frm', 'jfc', 'b') from raw proof, flag 'b' indicates whether line is inside a block


getLine : Int -> RawProof -> Maybe ( String, String, Bool )
getLine n proof =
    getLineHelper n 0 proof
        |> Tuple.second



-- helper to check if line is beginning of a block


beginsBlockHelper : Int -> Int -> RawProof -> ( Int, Bool, Bool )
beginsBlockHelper n start proof =
    let
        recur =
            \b ps ->
                List.foldl
                    (\step state ->
                        let
                            ( i, firststep, result ) =
                                state
                        in
                        if result then
                            state

                        else
                            case step of
                                RawStep frm jfc ->
                                    let
                                        newi =
                                            i + 1

                                        newresult =
                                            newi == n && firststep
                                    in
                                    ( newi, False, newresult )

                                _ ->
                                    beginsBlockHelper n i step
                    )
                    ( start, b, False )
                    ps
    in
    case proof of
        RawStep _ _ ->
            recur False [ proof ]

        RawBegin ps ->
            recur False ps

        RawBlock ps ->
            recur True ps



-- check if line is beginning of block


beginsBlock : Int -> RawProof -> Bool
beginsBlock n proof =
    beginsBlockHelper n 0 proof
        |> (\( _, _, x ) -> x)


proofLength : RawProof -> Int
proofLength proof =
    case proof of
        RawStep _ _ ->
            1

        RawBegin ps ->
            proofLengths ps

        RawBlock ps ->
            proofLengths ps


proofLengths : List RawProof -> Int
proofLengths proofs =
    proofs
        |> List.map proofLength
        |> List.sum


proofToList : RawProof -> List ( String, String )
proofToList proof =
    let
        recur =
            List.foldl
                (\step list ->
                    list ++ proofToList step
                )
                []
    in
    case proof of
        RawStep frm jfc ->
            [ ( frm, jfc ) ]

        RawBegin ps ->
            recur ps

        RawBlock ps ->
            recur ps



-- merge consecutive blocks in proof


mergeBlocks : RawProof -> RawProof
mergeBlocks proof =
    case proof of
        RawBegin ps ->
            ps
                |> mergeBlocksHelper
                |> RawBegin

        _ ->
            proof



-- helper to merge consecutive blocks


mergeBlocksHelper : List RawProof -> List RawProof
mergeBlocksHelper proofs =
    case proofs of
        (RawBlock ps1) :: (RawBlock ps2) :: rest ->
            (RawBlock (mergeBlocksHelper ps1 ++ mergeBlocksHelper ps2) :: rest)
                |> mergeBlocksHelper

        (RawBlock ps) :: rest ->
            RawBlock (mergeBlocksHelper ps) :: mergeBlocksHelper rest

        step :: rest ->
            step :: mergeBlocksHelper rest

        [] ->
            []



-- content of block [s1,...,sn,...,sk] is split into ( [s1,...,sn-1], sn, [sn+1,...,sk] )


splitRawBlock : Int -> Int -> Int -> List RawProof -> RawProof -> ( Int, ( Int, List RawProof ), ( List RawProof, Maybe RawProof, List RawProof ) )
splitRawBlock n start depth acc proof =
    let
        recur =
            List.foldl
                (\step state ->
                    let
                        ( i, ( k, prf ), ( before, sn, after ) ) =
                            state
                    in
                    case step of
                        RawStep frm jfc ->
                            let
                                newi =
                                    i + 1

                                newtriple =
                                    if newi == n then
                                        ( before, RawStep frm jfc |> Just, after )

                                    else if newi < n then
                                        ( addStep ( frm, jfc ) before, sn, after )

                                    else
                                        ( before, sn, addStep ( frm, jfc ) after )
                            in
                            ( newi, ( k, prf ), newtriple )

                        RawBlock ps ->
                            let
                                blocklen =
                                    proofLengths ps
                            in
                            if i + blocklen < n then
                                ( i + blocklen, ( k, prf ), ( addBlock ps before, sn, after ) )

                            else if i >= n then
                                ( i + blocklen, ( k, prf ), ( before, sn, addBlock ps after ) )

                            else
                                splitRawBlock n i (k + 1) prf step
                                    |> (\( j, ( rk, rprf ), ( bb, snb, ba ) ) ->
                                            -- split happened directly (without further recursive calls)
                                            if rk == k + 1 then
                                                ( j, ( rk, rprf ), ( addBlock bb before, snb, addBlock ba after ) )

                                            else
                                                case snb of
                                                    Just stepn ->
                                                        case rprf of
                                                            [] ->
                                                                ( j, ( rk, addBlock (bb ++ [ stepn ] ++ ba) prf ), ( before, snb, after ) )

                                                            _ ->
                                                                ( j, ( rk, addBlock (bb ++ rprf ++ ba) prf ), ( before, snb, after ) )

                                                    Nothing ->
                                                        ( j, ( rk, addBlock (bb ++ ba) rprf ), ( before, snb, after ) )
                                       )

                        _ ->
                            state
                )
                ( start, ( depth, acc ), ( [], Nothing, [] ) )
    in
    case proof of
        RawStep _ _ ->
            recur [ proof ]

        RawBegin ps ->
            recur ps

        RawBlock ps ->
            recur ps



-- content of RawBegin [s1,...,sn,...,sk] is split into ( [s1,...,sn-1], sn, [sn+1,...,sk] )


splitRawProof : Int -> RawProof -> RawProof
splitRawProof n proof =
    splitRawBlock n 0 0 [] proof
        |> (\( _, ( _, acc ), ( before, sn, after ) ) ->
                case sn of
                    Just step ->
                        (case acc of
                            [] ->
                                before ++ [ step ] ++ after

                            _ ->
                                before ++ acc ++ after
                        )
                            |> pruneRaw
                            |> RawBegin

                    Nothing ->
                        proof
           )



-- updates list of raw proof (keeping track of line number)


updateRawProofs : Int -> Int -> Int -> EditRawProof -> List RawProof -> List RawProof -> ( Int, List RawProof, List RawProof )
updateRawProofs n start oldstart edit init prfs =
    List.foldl
        (\step state ->
            let
                -- prev is proof before going into recursive call, i.e., before starting box
                ( i, proof, prev ) =
                    state
            in
            case step of
                RawStep frm jfc ->
                    let
                        newi =
                            i + 1

                        ( newproof, newprev ) =
                            case edit of
                                UpdateAll cfg ->
                                    ( addStep (Keywords.replaceKeywordsPair cfg.replacesc cfg.replacekw cfg.replacegreek ( frm, jfc )) proof, prev )

                                CaseConversion upper ->
                                    let
                                        convert =
                                            if upper then
                                                String.map
                                                    (\c ->
                                                        if Keywords.isGreekLetter c then
                                                            c

                                                        else
                                                            Char.toUpper c
                                                    )

                                            else
                                                String.toLower
                                    in
                                    frm
                                        |> convert
                                        |> (\f ->
                                                addStep ( f, jfc ) proof
                                                    |> (\prf -> ( prf, prev ))
                                           )

                                _ ->
                                    if newi /= n then
                                        ( addStep ( frm, jfc ) proof, prev )

                                    else
                                        case edit of
                                            EditFormula str ->
                                                ( addStep ( str, jfc ) proof, prev )

                                            EditJustification str ->
                                                ( addStep ( frm, str ) proof, prev )

                                            RemoveLine ->
                                                ( proof, prev )

                                            RemoveLineIfEmpty ->
                                                if String.isEmpty frm then
                                                    ( proof, prev )

                                                else
                                                    ( addStep ( frm, jfc ) proof, prev )

                                            AddLine frm1 jfc1 ->
                                                proof
                                                    |> addStep ( frm, jfc )
                                                    |> addStep ( frm1, jfc1 )
                                                    |> (\prf -> ( prf, prev ))

                                            SwapLinesWith m ->
                                                -- obtain data from line m < n
                                                -- m may be in prev OR proof
                                                let
                                                    mprev =
                                                        m - oldstart
                                                in
                                                case getLine mprev (RawBegin prev) of
                                                    Just ( frm1, jfc1, _ ) ->
                                                        -- set line m < n with data of line n, add updated line n
                                                        ( addStep ( frm1, jfc1 ) proof, updateRawProofs mprev 0 0 (SetLine frm jfc) [] prev |> (\( _, prf1, _ ) -> prf1) )

                                                    Nothing ->
                                                        let
                                                            mproof =
                                                                m - start
                                                        in
                                                        case getLine mproof (RawBegin proof) of
                                                            Just ( frm1, jfc1, _ ) ->
                                                                proof
                                                                    |> updateRawProofs mproof 0 0 (SetLine frm jfc) []
                                                                    |> (\( _, prf, _ ) -> ( addStep ( frm1, jfc1 ) prf, prev ))

                                                            Nothing ->
                                                                ( addStep ( frm, jfc ) proof, prev )

                                            SetLine frm1 jfc1 ->
                                                ( addStep ( frm1, jfc1 ) proof, prev )

                                            StartBlock ->
                                                ( addBlock [ RawStep frm jfc, RawStep "" "" ] proof, prev )

                                            _ ->
                                                ( proof, prev )
                    in
                    -- do not modify 'newi' in case of remove/add (!)
                    ( newi, newproof, newprev )

                RawBlock ps ->
                    {- use 'proof' as 'init' to make currently built state available within block
                       - 'mod' is modified 'init'
                       - however, not everything is included in 'init' (only lines before box start of outer box)
                       - for full drag & drop all the lines would be required (!)
                    -}
                    let
                        ( j, block, mod ) =
                            updateRawProofs n i start edit proof ps
                    in
                    ( j, addBlock block mod, prev )

                RawBegin _ ->
                    state
        )
        ( start, [], init )
        prfs



-- update raw proof, ensuring at least one empty line exists before and after performing operation


updateRawProof : Int -> EditRawProof -> RawProof -> RawProof
updateRawProof n edit proof =
    case proof of
        RawBegin ps ->
            ps
                |> (\before ->
                        (if List.isEmpty before then
                            [ RawStep "" "" ]

                         else
                            before
                        )
                            |> updateRawProofs n 0 0 edit []
                            |> (\( _, prf, _ ) ->
                                    prf
                                        |> pruneRaw
                                        |> (\after ->
                                                (if List.isEmpty after then
                                                    [ RawStep "" "" ]

                                                 else
                                                    after
                                                )
                                                    |> RawBegin
                                                    |> removeEmptyBlocksRaw
                                           )
                               )
                   )

        _ ->
            proof



-- remove empty blocks from proof and return maybe proof


mpruneRaw : RawProof -> Maybe RawProof
mpruneRaw prf =
    case prf of
        RawStep _ _ ->
            Just prf

        RawBlock ps ->
            let
                xs =
                    pruneRaw ps
            in
            if List.isEmpty xs then
                Nothing

            else
                Just (RawBlock xs)

        RawBegin ps ->
            case pruneRaw ps of
                [] ->
                    Nothing

                xs ->
                    Just (RawBegin xs)



-- transform list of raw proofs into list of raw proofs where empty blocks have been removed


pruneRaw : List RawProof -> List RawProof
pruneRaw ps =
    ps
        |> List.foldl
            (\p state ->
                case mpruneRaw p of
                    Just proof ->
                        state ++ [ proof ]

                    Nothing ->
                        state
            )
            []



-- removes empty blocks from raw proof, an empty raw proof is represented by 'RawBegin []'


removeEmptyBlocksRaw : RawProof -> RawProof
removeEmptyBlocksRaw prf =
    prf
        |> mpruneRaw
        |> (\m ->
                case m of
                    Nothing ->
                        RawBegin []

                    Just x ->
                        x
           )



-- tool configuration


type alias Config =
    { fol : Bool
    , qtype : Bool
    , replacesc : Bool
    , replacekw : Bool
    , replacegreek : Bool
    , subset : RuleSubset
    , conjstronger : Bool
    , inputmode : Bool
    , heuristics : Bool
    }


defaultConfig : Config
defaultConfig =
    Config True True True True True FOL False False True



-- type alias for parser configuration (subset of Config type)


type alias ParserConfig =
    { fol : Bool -- FOL | Prop
    , kword : Bool -- keywords are reserved
    , qtype : Bool -- quantifier type
    , conjstronger : Bool -- conjunction binds stronger than disjunction?
    }


defaultParserConfig : ParserConfig
defaultParserConfig =
    ParserConfig True True True False


getParserConfig : Config -> ParserConfig
getParserConfig cfg =
    { fol = cfg.fol, qtype = cfg.qtype, kword = cfg.replacekw, conjstronger = cfg.conjstronger }


type alias Model =
    { goal : GoalType -- goal data
    , proof : RawProof -- proof data
    , cfg : Config -- configuration data (see above)
    , latex : Bool -- display latex page
    , error : Bool -- display error page
    , lasterror : String -- error msg to be displayed on error page
    , help : Bool -- display help page
    , lsize : Int -- current line field size
    , gsize : Int -- current goal field size
    , jfcsize : Int -- current jfc field size
    }
