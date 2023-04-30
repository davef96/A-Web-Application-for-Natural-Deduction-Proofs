-- this module provides a function to check proofs, and helper functions


module ProofChecking exposing (..)

import Formula exposing (Formula(..), FrmSubst, Operator(..), Seq, Term(..), TermSubst)
import ModelDefs exposing (ParserConfig, RuleSubset, VarType)
import Proof exposing (BuildLineState(..), Justification(..), Proof(..))
import Rule exposing (Abstract(..), IndexedMarkedPremises, MarkedAbstract, PremiseType(..), Rule, RuleConclusion(..), RulePremises, RuleVersion(..))
import Set exposing (Set)
import Utils



-- type to specify which lines were used to derive a certain fact
-- e.g., to represent the block for '⟶i 4-6' we can use 'Range 4 6'


type FactPos
    = LineNo Int
    | Range Int Int
    | None



-- type to keep track of facts while checking the proof
-- 'LineFact' has list of 'Factpos' that have been used to derive this fact (dependencies), and an assumption flag to keep track of assumed facts that have to be discharged


type Fact
    = LineFact Formula FactPos (List FactPos) Bool
    | BlockFact (List VarType) (List Fact) FactPos



-- type to represent outcomes of checking
-- 'LineSuccess' and 'LineQED' have a list of 'Factpos' that have been used to derive the fact in this line, a list of generalized versions of formulas required for matching, and the rule version used


type ProofCheck
    = LineSuccess (List FactPos) (List Formula) RuleVersion
    | LineQED (List FactPos) (List Formula) RuleVersion
    | LineError String
    | LineWarning String



-- similar type for blocks


type BlockCheck
    = BlockSuccess
    | BlockError String
    | BlockWarning String



-- type to keep track of position of a fact within a block
-- used in checker: assumptions only allowed if at beginning of block
-- used in redundancy checking: last line in block cannot be referenced, and thus, has to be ignored
-- note that we may have a single line block: line is both begin and end of block!


type PosInBlock
    = BlockBegin
    | BlockBeginEnd
    | BlockEnd
    | BlockAnywhere



-- type alias for final result of checking
-- 'BlockCheck' needs an additional 'FactPos', e.g., 'Range 4 6', to (quickly) obtain the corresponding lines within the respective block


type alias CheckResult =
    ( List ProofCheck, List ( BlockCheck, FactPos ) )



-- type alias for current state of proof checker
-- 1) current block level (assumptions allowed? proof finished?), line number (to calculate 'FactPos')
-- 2) currently available facts (used for deriving new facts via rule application)
-- 3) current result


type alias CheckState =
    ( ( Int, Int ), List Fact, CheckResult )



-- obtains position of given fact


getFactPos : Fact -> FactPos
getFactPos f =
    case f of
        LineFact _ pos _ _ ->
            pos

        BlockFact _ _ pos ->
            pos


displayFactPos : FactPos -> String
displayFactPos fp =
    case fp of
        None ->
            "None"

        LineNo n ->
            String.fromInt n

        Range n m ->
            String.fromInt n ++ "‒" ++ String.fromInt m


displayFactPositions : List FactPos -> String
displayFactPositions fps =
    case fps of
        [] ->
            "None"

        _ ->
            fps
                |> List.map displayFactPos
                |> String.join ","


displayBlockVars : List VarType -> String
displayBlockVars vs =
    case vs of
        [] ->
            "None"

        _ ->
            String.join "," vs


displayPosInBlock : PosInBlock -> String
displayPosInBlock pos =
    case pos of
        BlockBegin ->
            "Begin"

        BlockBeginEnd ->
            "BeginEnd"

        BlockAnywhere ->
            "Middle"

        BlockEnd ->
            "End"


displayFact : Bool -> Fact -> String
displayFact q f =
    case f of
        LineFact frm pos deps assm ->
            let
                assmtext =
                    if assm then
                        [ "<Assumption>" ]

                    else
                        []
            in
            String.join ", " ([ Formula.displayFormula q frm, displayFactPos pos, displayFactPositions deps ] ++ assmtext)

        BlockFact vs fs pos ->
            "BlockFact: {" ++ String.join ", " [ displayBlockVars vs, "[" ++ String.join "," (List.map (displayFact q) fs) ++ "]", displayFactPos pos ] ++ "}"


displayFacts : Bool -> List Fact -> List String
displayFacts q fs =
    List.indexedMap (\i f -> String.fromInt (i + 1) ++ ": " ++ displayFact q f) fs


displayRuleVersion : RuleVersion -> String
displayRuleVersion rulev =
    case rulev of
        Default ->
            ""

        V1 ->
            "1"

        V2 ->
            "2"


verNonDefault : RuleVersion -> Bool
verNonDefault rulev =
    case rulev of
        Default ->
            False

        _ ->
            True


displayLineState : Bool -> Int -> ProofCheck -> String
displayLineState q i c =
    let
        sn =
            String.fromInt (i + 1)
    in
    case c of
        LineSuccess deps genfs rulev ->
            sn ++ ": ✓" ++ displayFactPositions deps ++ ";" ++ Formula.displayFormulas q genfs ++ ";" ++ displayRuleVersion rulev

        LineQED deps genfs rulev ->
            sn ++ ": ∎" ++ displayFactPositions deps ++ ";" ++ Formula.displayFormulas q genfs ++ ";" ++ displayRuleVersion rulev

        LineError msg ->
            sn ++ ": ⛔" ++ msg

        LineWarning msg ->
            sn ++ ": ⚠" ++ msg


displayBlockState : FactPos -> BlockCheck -> String
displayBlockState pos c =
    let
        sn =
            displayFactPos pos
    in
    case c of
        BlockSuccess ->
            sn ++ ": ✓"

        BlockError msg ->
            sn ++ ": ⛔" ++ msg

        BlockWarning msg ->
            sn ++ ": ⚠" ++ msg


displayProofState : Bool -> CheckState -> List String
displayProofState q state =
    let
        ( ( level, i ), fs, result ) =
            state
    in
    [ "Iterator: " ++ String.fromInt i, "Level: " ++ String.fromInt level, "Facts: " ] ++ displayFacts q fs ++ displayProofChecking q result


displayProofChecking : Bool -> CheckResult -> List String
displayProofChecking q result =
    let
        ( xs, ys ) =
            result

        sxs =
            List.indexedMap (displayLineState q) xs

        sys =
            List.map (\( state, pos ) -> displayBlockState pos state) ys
    in
    [ "LineState: " ] ++ sxs ++ [ "BlockState: " ] ++ sys



-- converts state of checker to result


stateToResult : CheckState -> CheckResult
stateToResult =
    \( _, _, rs ) -> rs



-- checks each line (proof step) for correctness, i.e., checks if each stated fact can be derived using the given justification (in the current state)


check : Bool -> Bool -> RuleSubset -> ( Maybe Seq, Proof ) -> Result String CheckState
check q heuristics sub proof =
    let
        init =
            ( ( 0, 0 ), [], ( [], [] ) )

        ( mseq, prf ) =
            proof

        state =
            checker q heuristics sub ( mseq, ( prf, BlockBegin ) ) init

        result =
            stateToResult state
    in
    -- only check for redundant lines if proof free of errors AND proof finished
    if resultValid result && resultQED result then
        -- add redundancy information to state (currently ignoring errors in redundancyCheck)
        case redundancyCheck state of
            Ok x ->
                Ok x

            Err _ ->
                Ok state

    else
        -- simply propagate (final) state from checker
        Ok state



-- this function is used when blockvars are not explicitly fixed by user


fixVars : Int -> List String
fixVars n =
    if n <= 0 then
        []

    else
        let
            var =
                "x" ++ String.fromInt (1000000 - n)
        in
        var :: fixVars (n - 1)



-- checks if (checked) proof is free of errors
-- True: no errors, but may contain warnings, e.g., redundant lines


resultValid : CheckResult -> Bool
resultValid result =
    result
        |> Tuple.first
        |> proofValid



-- every line free of errors


proofValid : List ProofCheck -> Bool
proofValid ps =
    ps
        |> List.foldl
            (\x state ->
                case x of
                    LineError _ ->
                        False

                    _ ->
                        state
            )
            True



-- checks if (checked) proof is finished (proof contains line that derives proof goal)


resultQED : CheckResult -> Bool
resultQED result =
    result
        |> Tuple.first
        |> proofQED


proofQED : List ProofCheck -> Bool
proofQED ps =
    ps
        |> List.foldl
            (\x state ->
                case x of
                    LineQED _ _ _ ->
                        True

                    _ ->
                        state
            )
            False



-- helper for updating the checker state in case of an error


checkError : CheckState -> String -> CheckState
checkError state msg =
    case state of
        ( i, fs, ( pcs, bcs ) ) ->
            -- add error msg to pcs (for current line)
            ( i, fs, ( pcs ++ [ LineError msg ], bcs ) )



-- helper for updating the checker state in case of success for a blockfact


checkBlockSuccess : CheckState -> Fact -> CheckState
checkBlockSuccess state f =
    let
        ( i, fs, ( pcs, bcs ) ) =
            state

        pos =
            case f of
                BlockFact _ _ p ->
                    p

                _ ->
                    None
    in
    -- add blockfact to fs, add success to bcs (for current block)
    ( i, fs ++ [ f ], ( pcs, bcs ++ [ ( BlockSuccess, pos ) ] ) )



-- helper for updating the checker state in case of success


checkSuccess : CheckState -> Fact -> List Formula -> RuleVersion -> CheckState
checkSuccess =
    checkSuc LineSuccess



-- helper for updating the checker state in case of QED (success that ends the proof)


checkQED : CheckState -> Fact -> List Formula -> RuleVersion -> CheckState
checkQED =
    checkSuc LineQED



-- helper for 'checkAssumption', 'checkSuccess' and 'checkQED'


checkSuc : (List FactPos -> List Formula -> RuleVersion -> ProofCheck) -> CheckState -> Fact -> List Formula -> RuleVersion -> CheckState
checkSuc ctor state f genfs rulev =
    let
        ( i, fs, ( pcs, bcs ) ) =
            state

        pos =
            case f of
                LineFact _ _ p _ ->
                    p

                _ ->
                    []
    in
    -- add fact 'f' to 'fs' and respective constructor call to 'pcs'
    ( i, fs ++ [ f ], ( pcs ++ [ ctor pos genfs rulev ], bcs ) )



-- matches terms (no restrictions)
-- returns tuple: (required substitutions, not matchable substitutions)


matchTerms : Term -> Term -> ( List TermSubst, List TermSubst )
matchTerms t1 t2 =
    case t1 of
        Var _ ->
            -- x vs. y or x vs. f(...)
            ( [ ( t1, t2 ) ], [] )

        Func s1 ts1 ->
            case t2 of
                Var _ ->
                    -- f(...) vs. x ("Func-Var clash")
                    ( [], [ ( t1, t2 ) ] )

                Func s2 ts2 ->
                    if s1 == s2 && List.length ts1 == List.length ts2 then
                        -- f(...) vs. f(...)
                        List.map2 matchTerms ts1 ts2
                            |> (\rs -> ( List.concatMap Tuple.first rs, List.concatMap Tuple.second rs ))

                    else
                        -- f(...) vs. g(...) ("Func clash")
                        ( [], [ ( t1, t2 ) ] )



-- calls matchTermsGeneralized in decomposition step to be able to do recursive generalization


matchTermsGeneralizedHelper : Maybe ( Term, Term ) -> List String -> List String -> Term -> Term -> ( List TermSubst, List TermSubst, Maybe Term )
matchTermsGeneralizedHelper meq lbound rbound t1 t2 =
    case t1 of
        Var _ ->
            -- x vs. y or x vs. f(...)
            ( [ ( t1, t2 ) ], [], Just t1 )

        Func s1 ts1 ->
            case t2 of
                Var _ ->
                    -- f(...) vs. x ("Func-Var clash")
                    ( [], [ ( t1, t2 ) ], Nothing )

                Func s2 ts2 ->
                    if s1 == s2 && List.length ts1 == List.length ts2 then
                        -- f(...) vs. f(...)
                        List.map2 (matchTermsGeneralized meq lbound rbound) ts1 ts2
                            |> (\rs ->
                                    ( List.concatMap (\( x1, _, _ ) -> x1) rs
                                    , List.concatMap (\( _, x2, _ ) -> x2) rs
                                    , rs
                                        |> List.map (\( _, _, x3 ) -> x3)
                                        |> List.foldl (Maybe.map2 (\t ts -> ts ++ [ t ])) (Just [])
                                        |> Maybe.map (\ts -> Func s1 ts)
                                    )
                               )

                    else
                        -- f(...) vs. g(...) ("Func clash")
                        ( [], [ ( t1, t2 ) ], Nothing )



-- given equality lhs = rhs, checks if t1 == lhs and t2 == rhs and no capturing occurs


matchTermsGeneralized : Maybe ( Term, Term ) -> List String -> List String -> Term -> Term -> ( List TermSubst, List TermSubst, Maybe Term )
matchTermsGeneralized meq lbound rbound t1 t2 =
    let
        nobound =
            \l r ->
                ( l |> Formula.termVars |> Set.toList, r |> Formula.termVars |> Set.toList )
                    |> Tuple.mapBoth (List.any (\v -> List.member v lbound)) (List.any (\v -> List.member v rbound))
                    |> (\( b1, b2 ) -> not b1 && not b2)
    in
    case meq of
        Just ( lhs, rhs ) ->
            {- let
                   deb1 =
                       Debug.log "eq vs. terms = " ((lhs, "=====", rhs), (t1, "==?==",t2), (lbound, "<- lb | rb ->" ,rbound))
               in
            -}
            if t1 == lhs && t2 == rhs && nobound lhs rhs then
                --Debug.log "Terms were matched using a generalized form!"
                ( [], [], Just (Var "?") )

            else
                -- cannot insert '?' here since either:
                -- 1) some var in lhs or rhs is bound
                -- 2) further decomposition of t1 and t2 is required
                matchTermsGeneralizedHelper meq lbound rbound t1 t2

        Nothing ->
            -- no equality was given; normal matching suffices
            matchTerms t1 t2
                |> (\( x1, x2 ) -> ( x1, x2, Nothing ))



-- checks if two formulas match, and obtains required substitutions on formula and term level
-- left formula can contain formula placeholders, right formula must be fully instantiated (on formula level)
-- on success: returns (fsubsts, tsubsts, (errsubsts, capsubsts, genfrm)
-- 1) fsubsts: required formula substitutions, i.e., apply(fsubsts, frm1) = frm2 if fsubsts free of clashes
-- 2) tsubsts: required term substitutions, i.e., apply(fsubsts & tsubsts, frm1) = frm2 if fsubsts free of clashes, tsubsts free of clashes & capturing
-- 3) errsubts: term substitutions that were not possible (func-func or func-var clash while matching terms)
-- 4) capsubsts: term substitutions that lead to capturing
-- 5) genfrm: formula containing '?'; generalized form
-- on error: returns (errdetails, (subformula, subformula))
-- 1) errdetails: string describing why matching failed
-- 2) tuple of subformulas where matching yielded error, i.e., frm1 & frm2 from respective recursive call


matchFormulas : Formula -> Formula -> Result ( String, ( Formula, Formula ) ) ( List FrmSubst, List TermSubst, ( List TermSubst, List TermSubst, Maybe Formula ) )
matchFormulas frm1 frm2 =
    matchFormulasHelper Nothing [] [] frm1 frm2
        |> Result.map (\( x1, x2, ( x31, x32, _ ) ) -> ( x1, x2, ( x31, x32, Nothing ) ))



-- performs matching in case a generalized form is required (given t1 = t2)


matchFormulasGeneralized : Maybe ( Term, Term ) -> Formula -> Formula -> Result ( String, ( Formula, Formula ) ) ( List FrmSubst, List TermSubst, ( List TermSubst, List TermSubst, Maybe Formula ) )
matchFormulasGeneralized meq frm1 frm2 =
    matchFormulasHelper meq [] [] frm1 frm2


termNotFree : List String -> Term -> Bool
termNotFree bound term =
    term
        |> Formula.termVars
        |> Set.toList
        |> List.any (\v -> List.member v bound)



-- obtain substitutions that result in capturing
-- for normal matching it suffices to check that the replacement does not get captured; however, for generalized matching neither lhs nor rhs is allowed to be bound


capturedCheck : Maybe ( Term, Term ) -> List String -> List String -> List TermSubst -> List TermSubst
capturedCheck meq lbound rbound tsubsts =
    case meq of
        Nothing ->
            tsubsts
                |> List.filter
                    (\( _, replacement ) ->
                        replacement
                            |> termNotFree lbound
                    )
                |> Utils.removeEqPairs

        Just _ ->
            {- let
                   deb =
                       Debug.log "generalized capture check on " (tsubsts, lbound, rbound)
               in
               -- the left tuple element is cleaned up, simply for readability;
            -}
            ( tsubsts |> List.filter (\( lhs, rhs ) -> termNotFree lbound lhs), tsubsts |> List.filter (\( lhs, rhs ) -> termNotFree rbound rhs) )
                |> (\( xs1, ys1 ) ->
                        ( Utils.without ys1 xs1, ys1 )
                            |> (\( xs2, ys2 ) ->
                                    ( List.map (\( lhs, rhs ) -> ( rhs, lhs )) xs2, ys2 )
                                        |> (\( xs, ys ) ->
                                                xs
                                                    ++ ys
                                                    |> Utils.removeEqPairs
                                           )
                               )
                   )


matchFormulasHelper : Maybe ( Term, Term ) -> List String -> List String -> Formula -> Formula -> Result ( String, ( Formula, Formula ) ) ( List FrmSubst, List TermSubst, ( List TermSubst, List TermSubst, Maybe Formula ) )
matchFormulasHelper meq lbound rbound frm1 frm2 =
    let
        ( op1, args1 ) =
            Formula.deconstructFormula frm1

        ( op2, args2 ) =
            Formula.deconstructFormula frm2

        err =
            \details ->
                Err ( details, ( frm1, frm2 ) )

        -- we cannot deconstruct the formulas in case of quantifiers (losing quantifier information, i.e., bound var, when recurring on args)
        mqargs =
            case op1 of
                OpExists _ ->
                    case op2 of
                        OpExists _ ->
                            Just ( [ frm1 ], [ frm2 ] )

                        _ ->
                            Nothing

                OpForAll _ ->
                    case op2 of
                        OpForAll _ ->
                            Just ( [ frm1 ], [ frm2 ] )

                        _ ->
                            Nothing

                _ ->
                    Nothing

        recur =
            \lhsargs rhsargs mop ->
                List.map2
                    (\arg1 arg2 ->
                        let
                            ( rop, _ ) =
                                Formula.deconstructFormula arg2
                        in
                        case arg1 of
                            PredConst s1 ->
                                if Formula.abstract s1 then
                                    Ok ( [ ( arg1, arg2 ) ], [], ( [], [], Just arg1 ) )

                                else
                                    case arg2 of
                                        PredConst s2 ->
                                            if s1 == s2 then
                                                Ok ( [], [], ( [], [], Just arg1 ) )

                                            else
                                                err ("Name mismatch: '" ++ s1 ++ "' vs. '" ++ s2 ++ "'")

                                        _ ->
                                            err ("Operator mismatch: 'Predicate Constant' vs. '" ++ Formula.displayOperator rop ++ "'")

                            Equals ( t11, t12 ) ->
                                case arg2 of
                                    Equals ( t21, t22 ) ->
                                        let
                                            ( tsubsts1, errsubsts1, mt1 ) =
                                                matchTermsGeneralized meq lbound rbound t11 t21

                                            ( tsubsts2, errsubsts2, mt2 ) =
                                                matchTermsGeneralized meq lbound rbound t12 t22

                                            tsubsts =
                                                tsubsts1 ++ tsubsts2

                                            errsubsts =
                                                errsubsts1 ++ errsubsts2

                                            cap =
                                                capturedCheck meq lbound rbound tsubsts
                                        in
                                        Ok ( [], tsubsts, ( errsubsts, cap, Maybe.map2 (\t1 t2 -> Equals ( t1, t2 )) mt1 mt2 ) )

                                    _ ->
                                        err ("Operator mismatch: '＝' vs. '" ++ Formula.displayOperator rop ++ "'")

                            Predicate s1 ts1 ->
                                case arg2 of
                                    Predicate s2 ts2 ->
                                        if s1 == s2 && List.length ts1 == List.length ts2 then
                                            let
                                                ( tsubsts, errsubsts, mfrm ) =
                                                    List.map2 (matchTermsGeneralized meq lbound rbound) ts1 ts2
                                                        |> (\rs ->
                                                                ( List.concatMap (\( x1, _, _ ) -> x1) rs
                                                                , List.concatMap (\( _, x2, _ ) -> x2) rs
                                                                , rs
                                                                    |> List.map (\( _, _, x3 ) -> x3)
                                                                    |> List.foldl (Maybe.map2 (\t ts -> ts ++ [ t ])) (Just [])
                                                                    |> Maybe.map (\ts -> Predicate s1 ts)
                                                                )
                                                           )

                                                cap =
                                                    capturedCheck meq lbound rbound tsubsts
                                            in
                                            Ok ( [], tsubsts, ( errsubsts, cap, mfrm ) )

                                        else if s1 == s2 && List.length ts1 /= List.length ts2 then
                                            err ("Arity mismatch: " ++ String.fromInt (List.length ts1) ++ " vs. " ++ String.fromInt (List.length ts2))

                                        else
                                            err ("Name mismatch: '" ++ s1 ++ "' vs. '" ++ s2 ++ "'")

                                    _ ->
                                        err ("Operator mismatch: 'Predicate' vs. '" ++ Formula.displayOperator rop ++ "'")

                            Exists x1 f1 ->
                                case arg2 of
                                    Exists x2 f2 ->
                                        if Formula.abstract x2 then
                                            matchFormulasHelper meq (x2 :: lbound) (x1 :: rbound) f1 f2
                                                |> Result.map
                                                    (\( xs, ys, ( errs, cap, mfrm ) ) ->
                                                        ( xs, ys ++ [ ( Var x2, Var x1 ) ], ( errs, cap, mfrm |> Maybe.map (\frm -> Exists x2 frm) ) )
                                                    )

                                        else if Formula.abstract x1 && Formula.specificFormula f1 then
                                            -- flip arguments for recursive call
                                            matchFormulasHelper meq (x1 :: lbound) (x2 :: rbound) f2 f1
                                                |> Result.map (\( xs, ys, ( errs, cap, mfrm ) ) -> ( xs, ys ++ [ ( Var x1, Var x2 ) ], ( errs, cap, mfrm |> Maybe.map (\frm -> Exists x1 frm) ) ))

                                        else
                                            matchFormulasHelper meq (x1 :: lbound) (x2 :: rbound) f1 f2
                                                |> Result.map (\( xs, ys, ( errs, cap, mfrm ) ) -> ( xs, ys ++ [ ( Var x1, Var x2 ) ], ( errs, cap, mfrm |> Maybe.map (\frm -> Exists x1 frm) ) ))

                                    _ ->
                                        err ("Operator mismatch: '∃' vs. '" ++ Formula.displayOperator rop ++ "'")

                            ForAll x1 f1 ->
                                case arg2 of
                                    ForAll x2 f2 ->
                                        if Formula.abstract x2 then
                                            matchFormulasHelper meq (x2 :: lbound) (x1 :: rbound) f1 f2
                                                |> Result.map
                                                    (\( xs, ys, ( errs, cap, mfrm ) ) ->
                                                        ( xs, ys ++ [ ( Var x2, Var x1 ) ], ( errs, cap, mfrm |> Maybe.map (\frm -> ForAll x2 frm) ) )
                                                    )

                                        else if Formula.abstract x1 && Formula.specificFormula f1 then
                                            -- flip arguments for recursive call
                                            matchFormulasHelper meq (x1 :: lbound) (x2 :: rbound) f2 f1
                                                |> Result.map (\( xs, ys, ( errs, cap, mfrm ) ) -> ( xs, ys ++ [ ( Var x1, Var x2 ) ], ( errs, cap, mfrm |> Maybe.map (\frm -> ForAll x1 frm) ) ))

                                        else
                                            matchFormulasHelper meq (x1 :: lbound) (x2 :: rbound) f1 f2
                                                |> Result.map (\( xs, ys, ( errs, cap, mfrm ) ) -> ( xs, ys ++ [ ( Var x1, Var x2 ) ], ( errs, cap, mfrm |> Maybe.map (\frm -> ForAll x1 frm) ) ))

                                    _ ->
                                        err ("Operator mismatch: '∀' vs. '" ++ Formula.displayOperator rop ++ "'")

                            _ ->
                                matchFormulasHelper meq lbound rbound arg1 arg2
                    )
                    lhsargs
                    rhsargs
                    |> List.foldl
                        (Result.map2 (\( xs2, ys2, ( err2, cap2, mfrm2 ) ) ( xs1, ys1, ( err1, cap1, mfrms ) ) -> ( xs1 ++ xs2, ys1 ++ ys2, ( err1 ++ err2, cap1 ++ cap2, mfrms ++ [ mfrm2 ] ) )))
                        (Ok ( [], [], ( [], [], [] ) ))
                    |> (\x ->
                            case x of
                                Ok ( xs, ys, ( errs, cap, mfrms ) ) ->
                                    let
                                        cxs =
                                            xs
                                                |> Utils.removeDuplicates

                                        cys =
                                            ys
                                                |> Utils.removeDuplicates

                                        ( cerrs, ccap ) =
                                            ( Utils.removeDuplicates errs, Utils.removeDuplicates cap )

                                        mfrm =
                                            mfrms
                                                |> List.foldl (Maybe.map2 (\f fs -> fs ++ [ f ])) (Just [])
                                                |> (\mfs ->
                                                        case mop of
                                                            Just op ->
                                                                case mfs of
                                                                    Just fs ->
                                                                        Formula.reconstructFormula op fs

                                                                    Nothing ->
                                                                        Nothing

                                                            Nothing ->
                                                                case mfs of
                                                                    Just (f :: []) ->
                                                                        Just f

                                                                    _ ->
                                                                        Nothing
                                                   )
                                    in
                                    Ok ( cxs, cys, ( cerrs, ccap, mfrm ) )

                                Err e ->
                                    Err e
                       )
    in
    -- if formulas are equal, we do not need any substitutions
    if frm1 == frm2 then
        Ok ( [], [], ( [], [], Nothing ) )

    else
        case mqargs of
            Just ( qargs1, qargs2 ) ->
                recur qargs1 qargs2 Nothing

            Nothing ->
                if Rule.abstractPredConst frm1 then
                    -- trivial case: a placeholder matches any formula!
                    Ok ( [ ( frm1, frm2 ) ], [], ( [], [], Nothing ) )

                else if op1 == op2 && List.length args1 == List.length args2 then
                    -- operators match, recursively match args
                    recur args1 args2 (Just op1)

                else
                    -- operators do not match!
                    err ("Operator mismatch: '" ++ Formula.displayOperator op1 ++ "' vs. '" ++ Formula.displayOperator op2 ++ "'")



-- given a (partially) instantiated abstract fact, extracts ALL matching facts from 'fs'
-- returns list of
-- *) found fact
-- *) allowed termsubsts
-- *) required substitutions (on formula & term level), and triple (not matchable termsubst, capturing substitutions, maybe generalized formula)


findFact : Bool -> List Fact -> MarkedAbstract -> List TermSubst -> List ( Fact, List TermSubst, ( List FrmSubst, List TermSubst, ( List TermSubst, List TermSubst, Maybe Formula ) ) )
findFact q fs mafrm callowedtsubsts =
    let
        ( m, afrm ) =
            mafrm
    in
    case fs of
        [] ->
            []

        x :: xs ->
            let
                recur =
                    findFact q xs mafrm callowedtsubsts

                linefact =
                    \f ->
                        let
                            -- formula (containing placeholders), allowed tsubst
                            ( f1, fallowedtsubsts ) =
                                f

                            -- obtain terms t1 = t2 from allowed substs; currently only supported for conclusion vs. premise; only exactly one replacement supported; conclusion will be on lhs of matching and thus t1 has to be allowed replacement in conclusion; in more complex rules involving generalization the ordering (t1,t2) would have to be inferred from the premise instantiation order
                            meq =
                                case fallowedtsubsts of
                                    ( xf, rf ) :: [] ->
                                        case callowedtsubsts of
                                            ( xc, rc ) :: [] ->
                                                if xf == xc then
                                                    Just ( rc, rf )

                                                else
                                                    Nothing

                                            _ ->
                                                Nothing

                                    _ ->
                                        Nothing
                        in
                        case x of
                            LineFact frm pos _ _ ->
                                let
                                    matchresult =
                                        if m then
                                            matchFormulasGeneralized meq f1 frm

                                        else
                                            matchFormulas f1 frm
                                in
                                case matchresult of
                                    Ok ( fsubsts, tsubsts, errcapmfrm ) ->
                                        let
                                            ( atsubsts, _ ) =
                                                Formula.splitAbstractTermSubsts tsubsts

                                            allowedtsubsts =
                                                Formula.updateTermSubstsWithList atsubsts fallowedtsubsts
                                        in
                                        ( x, allowedtsubsts, ( fsubsts, tsubsts, errcapmfrm ) ) :: recur

                                    Err ( details, ( rf1, rf2 ) ) ->
                                        recur

                            _ ->
                                recur

                -- match 'head assms' with 'x1' and 'c' with 'x2'
                -- if assms == [] then block may start with another block, i.e., 'x1' is a block!!!
                -- 'x2' however, definitely has to be a linefact!
                matchBlock =
                    \assms c illegalexport x1 x2 ->
                        let
                            ( cf, callowedtsubst ) =
                                c

                            noassms =
                                List.isEmpty assms

                            matchconclusion =
                                \mass ->
                                    case x2 of
                                        LineFact frm2 pos2 _ _ ->
                                            let
                                                -- checks for each free var in frm2 if export would be illegal
                                                -- True: illegal export happened
                                                illexport =
                                                    Formula.freeVars frm2
                                                        |> Set.foldl
                                                            (\v state ->
                                                                state || List.member v illegalexport
                                                            )
                                                            False

                                                con =
                                                    if illexport then
                                                        Err ( "Last line in block is not allowed to contain fixed variables: " ++ String.join "," illegalexport, ( frm2, frm2 ) )

                                                    else
                                                        matchFormulas cf frm2
                                            in
                                            case mass of
                                                Nothing ->
                                                    case con of
                                                        Ok ( fsubsts2, tsubsts2, errcap2 ) ->
                                                            Just ( callowedtsubst, ( fsubsts2, tsubsts2, errcap2 ) )

                                                        _ ->
                                                            Nothing

                                                Just ( allowedassm, Ok ( fsubsts1, tsubsts1, ( errs1, cap1, mfrm1 ) ) ) ->
                                                    case con of
                                                        Ok ( fsubsts2, tsubsts2, ( errs2, cap2, mfrm2 ) ) ->
                                                            let
                                                                tsubsts =
                                                                    tsubsts1 ++ tsubsts2

                                                                ( atsubsts, _ ) =
                                                                    Formula.splitAbstractTermSubsts tsubsts

                                                                allowedtsubst =
                                                                    Formula.updateTermSubstsWithList atsubsts allowedassm

                                                                allowedtsubsts =
                                                                    allowedtsubst ++ callowedtsubst
                                                            in
                                                            Just ( allowedtsubsts, ( fsubsts1 ++ fsubsts2, tsubsts, ( errs1 ++ errs2, cap1 ++ cap2, Nothing ) ) )

                                                        _ ->
                                                            Nothing

                                                _ ->
                                                    Nothing

                                        _ ->
                                            Nothing
                        in
                        case x1 of
                            BlockFact _ _ _ ->
                                -- only match 'c' with 'x2'
                                if noassms then
                                    matchconclusion Nothing

                                else
                                    Nothing

                            LineFact frm1 pos1 _ frm1assm ->
                                let
                                    ass =
                                        -- changes would be requires here if at some point the application is adapted to handle rules that actually allow to introduce multiple assumption; however, the automatic start of boxes would need to be changed
                                        case List.head assms of
                                            Just ( f1, tsubst1 ) ->
                                                -- here we could allow that even though a rule allows to introduce an assumption the line is also accepted if it was NOT assumed; in the current implementation this does not make sense, since boxes are opened automatically by starting an assumption
                                                if frm1assm then
                                                    ( tsubst1, matchFormulas f1 frm1 )

                                                else
                                                    ( [], Err ( "Fact '" ++ Formula.displayFormula q frm1 ++ "' needs to be an assumption!", ( frm1, frm1 ) ) )

                                            Nothing ->
                                                -- no assumptions to match with, i.e., block does not allow any assumptions
                                                -- frm1 was assumed ==> block does not match
                                                if frm1assm then
                                                    ( [], Err ( "Fact '" ++ Formula.displayFormula q frm1 ++ "' is not allowed to be an assumption!", ( frm1, frm1 ) ) )

                                                else
                                                    ( [], Ok ( [], [], ( [], [], Nothing ) ) )
                                in
                                matchconclusion (Just ass)

                blockfact =
                    \vs1 assms c ->
                        case x of
                            -- note: single line block ==> first == last
                            BlockFact vs2 bfs pos ->
                                let
                                    first =
                                        List.head bfs

                                    last =
                                        List.head (List.reverse bfs)

                                    -- enforce fixing of all vars when block allows for it
                                    -- the function 'fixVars' fixes vars that are not explicitly fixed by the user
                                    fixed =
                                        vs2 ++ fixVars (List.length vs1 - List.length vs2)

                                    blockvarsubsts =
                                        List.map2 (\( v1, _ ) v2 -> ( Var v1, Var v2 )) vs1 fixed

                                    -- fixed vars that are NOT allowed to be exported
                                    illegalexport =
                                        List.map2 (\( _, export ) v2 -> ( v2, export )) vs1 fixed
                                            |> List.filter (Tuple.second >> not)
                                            |> List.map Tuple.first
                                in
                                case Maybe.map2 (matchBlock assms c illegalexport) first last of
                                    Just (Just ( allowedtsubsts, ( fsubsts, tsubsts, errcap ) )) ->
                                        ( x, allowedtsubsts, ( fsubsts, tsubsts ++ blockvarsubsts, errcap ) ) :: recur

                                    _ ->
                                        recur

                            _ ->
                                recur
            in
            case afrm of
                AbstractFormula frm ->
                    linefact frm

                AbstractBlock vs assms c ->
                    -- marking blocks currently not supported
                    blockfact vs assms c



-- processes list of 'findFact' results, returns (fact positions [deps], generalized formulas, rule version) upon success


processFoundFacts : Bool -> PremiseType -> List ( Int, MarkedAbstract ) -> ( List TermSubst, List TermSubst ) -> Set String -> List ( Int, Result Abstract (List ( Fact, List TermSubst, ( List FrmSubst, List TermSubst, ( List TermSubst, List TermSubst, Maybe Formula ) ) )) ) -> Result String ( List FactPos, List Formula, RuleVersion )
processFoundFacts q premtype afrms tsubstpair cbound xs =
    let
        -- (allowed termsubst in conclusion, termsubsts required to match with conclusion)
        ( mctsubst, ctsubsts ) =
            tsubstpair

        -- partition list into correct and error part
        ( iokfacts, ierrfacts ) =
            List.partition
                (\( _, x ) ->
                    case x of
                        Ok _ ->
                            True

                        Err _ ->
                            False
                )
                xs

        -- displays facts that were NOT found
        errs =
            List.map
                (\( _, x ) ->
                    case x of
                        Err a ->
                            Rule.displayAbstract q a

                        _ ->
                            "None"
                )
                ierrfacts

        -- obtain rule version based on position of fact
        getrulev =
            \i ->
                case i of
                    0 ->
                        V1

                    1 ->
                        V2

                    _ ->
                        Default

        -- list of list of ((i, fact, fsubsts), (abstract tsubsts, specific tsubsts, allowed tsubsts), (unmatchable termsubsts, capturing tsubsts, maybe formula for generalized form)
        ttss =
            List.map
                (\( i, x ) ->
                    case x of
                        Ok fs ->
                            List.map
                                (\y ->
                                    case y of
                                        ( fact, allowed, ( fsubsts, tsubsts, errcapmfrm ) ) ->
                                            ( ( i, fact, fsubsts )
                                            , tsubsts
                                                |> (\ss ->
                                                        ss
                                                            ++ ctsubsts
                                                            |> Formula.splitAbstractTermSubsts
                                                            -- note: do not apply Utils.removeEqPairs to be able to detect clash [x/x],[x/a] !!!
                                                            |> (\( tsubs1, tsubs2 ) -> ( Utils.removeDuplicates tsubs1, Utils.removeDuplicates tsubs2, Utils.removeDuplicates allowed ))
                                                   )
                                            , errcapmfrm
                                            )
                                )
                                fs

                        _ ->
                            []
                )
                iokfacts

        -- since we got a list of possible matches for each fact we were searching for, we have to try every combination for success
        -- an instance is such a combination
        instances =
            Utils.instances ttss

        tryinstances =
            if List.length instances == 0 && List.isEmpty errs then
                -- no fulfilled premises but also no errors (e.g. topI)
                Ok ( [ ( 0, None ) ], [] )

            else if List.length instances == 0 && not (List.isEmpty errs) then
                -- errors but at least one premise has to be fulfilled (e.g. disj)
                Ok ( [], [] )

            else
                List.foldl
                    (\instance inststate ->
                        let
                            ipos =
                                instance
                                    |> List.map
                                        (\( ( i, f, _ ), _, _ ) ->
                                            ( i, getFactPos f )
                                        )
                                    |> List.sortBy Tuple.first

                            atsubsts =
                                instance
                                    |> List.concatMap
                                        (\( _, ( asubsts, _, _ ), _ ) -> asubsts)

                            tsubsts =
                                instance
                                    |> List.concatMap
                                        (\( _, ( _, tsubsts1, _ ), _ ) -> tsubsts1)

                            errsubsts =
                                instance
                                    |> List.concatMap
                                        (\( _, _, ( err, _, _ ) ) -> err)

                            capsubsts =
                                instance
                                    |> List.concatMap
                                        (\( _, _, ( _, cap, _ ) ) -> cap)

                            mfrms =
                                instance
                                    |> List.map
                                        (\( _, _, ( _, _, mf ) ) -> mf)

                            genfs =
                                mfrms
                                    |> List.foldl
                                        (\mf gfs ->
                                            case mf of
                                                Just f ->
                                                    gfs ++ [ f ]

                                                Nothing ->
                                                    gfs
                                        )
                                        []

                            fsubsts =
                                instance
                                    |> List.concatMap
                                        (\( ( _, _, fsubsts1 ), _, _ ) ->
                                            fsubsts1
                                        )

                            clashingfrm =
                                Formula.clash fsubsts

                            allowedtsubsts =
                                instance
                                    |> List.concatMap
                                        (\( _, ( _, _, allowed ), _ ) ->
                                            allowed
                                        )
                                    |> List.map (Formula.updateTermSubstWithList atsubsts)

                            ctsubstu =
                                -- update only with atsubsts since we want an abstract form, e.g. [?t2/x]
                                Formula.updateTermSubstsWithList atsubsts mctsubst

                            -- list of illegal substitutions, i.e., terms that should not be replaced (according to used rule)
                            illegal =
                                let
                                    -- clashes irrelevant for illegal check
                                    -- however, if 'x' bound then [x/x] not allowed (if not explicitly allowed)
                                    -- atsubsts also irrelevant (abstract vars always allowed to be instantiated, just have to be clashfree)
                                    testcb =
                                        cbound |> Formula.updateVarsWithList atsubsts |> Set.toList |> List.map (\s -> Var s)

                                    ts =
                                        Utils.removeEqPairsExcept testcb tsubsts

                                    allowedinprems =
                                        \sub -> List.member sub allowedtsubsts

                                    abstractinprems =
                                        allowedtsubsts
                                            |> List.filter (\( _, y ) -> Formula.abstractTerm y)
                                            |> List.map Tuple.first

                                    -- terms that are mapped to an abstract term (unrestricted replacement)
                                    allowedinabstractprems =
                                        \( x, y ) ->
                                            List.any
                                                (\( x1, y1 ) ->
                                                    x == x1 && Formula.abstractTerm y1 && not (List.member y testcb)
                                                )
                                                allowedtsubsts
                                in
                                case ctsubstu of
                                    [] ->
                                        -- everything illegal that is not contained in allowedtsubsts (prems)
                                        List.filter (\sub -> not (allowedinprems sub || allowedinabstractprems sub)) ts

                                    _ ->
                                        let
                                            allowedincon =
                                                \sub -> List.any (\ctsub -> sub == ctsub) ctsubstu

                                            allowedinabstractcon =
                                                \( x, y ) -> List.any (\ctsub -> x == Tuple.first ctsub && Formula.abstractTerm (Tuple.second ctsub) && not (List.member y testcb)) ctsubstu
                                        in
                                        List.filter (\sub -> not (allowedinprems sub || allowedinabstractprems sub || allowedincon sub || allowedinabstractcon sub)) ts

                            -- list of clashing substitutions
                            clashing =
                                let
                                    ts =
                                        atsubsts ++ tsubsts
                                in
                                Formula.clash ts
                                    |> Utils.removeDuplicates

                            -- determines state based on the lists clashingfrm, clashing, illegal, and captured
                            checksubsts =
                                let
                                    clashfrmmsg =
                                        "Clashing Formula Substitutions: " ++ Formula.displayFrmSubsts q clashingfrm

                                    clashmsg =
                                        "Clashing Term Substitutions: " ++ Formula.displayTermSubsts clashing

                                    illmsg =
                                        case illegal of
                                            elem :: [] ->
                                                "Illegal Term Substitution: " ++ Formula.displayTermSubst elem

                                            _ ->
                                                "Illegal Term Substitutions: " ++ Formula.displayTermSubsts illegal

                                    errmsg =
                                        "Impossible Term Substitutions: " ++ Formula.displayTermSubsts errsubsts

                                    capturemsg =
                                        case capsubsts of
                                            elem :: [] ->
                                                "Term Substitution leads to Variable Capturing: " ++ Formula.displayTermSubst elem

                                            _ ->
                                                "Term Substitutions lead to Variable Capturing: " ++ Formula.displayTermSubsts capsubsts

                                    -- give user only the most helpful msg
                                    -- from user perspective "illegal" and "impossible" are the same thing
                                    uill =
                                        (illegal ++ errsubsts)
                                            |> Utils.removeDuplicates

                                    uillmsg =
                                        case uill of
                                            elem :: [] ->
                                                "Illegal Term Substitution: " ++ Formula.displayTermSubst elem

                                            _ ->
                                                "Illegal Term Substitutions: " ++ Formula.displayTermSubsts uill
                                in
                                case clashingfrm of
                                    [] ->
                                        case capsubsts of
                                            [] ->
                                                case uill of
                                                    [] ->
                                                        case clashing of
                                                            [] ->
                                                                Ok ( ipos, genfs )

                                                            _ ->
                                                                Err clashmsg

                                                    _ ->
                                                        Err uillmsg

                                            _ ->
                                                Err capturemsg

                                    _ ->
                                        Err clashfrmmsg

                            {- -- full error msgs
                               case clashingfrm of
                                   [] ->
                                       case illegal of
                                           [] ->
                                               case clashing of
                                                   [] ->
                                                       case errsubsts of
                                                           [] ->
                                                               case capsubsts of
                                                                   [] ->
                                                                       Ok ( ipos, genfs )

                                                                   _ ->
                                                                       Err capturemsg

                                                           _ ->
                                                               case capsubsts of
                                                                   [] ->
                                                                       Err errmsg

                                                                   _ ->
                                                                       Err (errmsg ++ "; " ++ capturemsg)

                                                   _ ->
                                                       case errsubsts of
                                                           [] ->
                                                               case capsubsts of
                                                                   [] ->
                                                                       Err clashmsg

                                                                   _ ->
                                                                       Err (clashmsg ++ "; " ++ capturemsg)

                                                           _ ->
                                                               case capsubsts of
                                                                   [] ->
                                                                       Err (clashmsg ++ "; " ++ errmsg)

                                                                   _ ->
                                                                       Err (clashmsg ++ "; " ++ errmsg ++ "; " ++ capturemsg)

                                           _ ->
                                               case clashing of
                                                   [] ->
                                                       case errsubsts of
                                                           [] ->
                                                               case capsubsts of
                                                                   [] ->
                                                                       Err illmsg

                                                                   _ ->
                                                                       Err (illmsg ++ "; " ++ capturemsg)

                                                           _ ->
                                                               case capsubsts of
                                                                   [] ->
                                                                       Err (illmsg ++ "; " ++ errmsg)

                                                                   _ ->
                                                                       Err (illmsg ++ "; " ++ errmsg ++ "; " ++ capturemsg)

                                                   _ ->
                                                       case errsubsts of
                                                           [] ->
                                                               case capsubsts of
                                                                   [] ->
                                                                       Err (clashmsg ++ "; " ++ illmsg)

                                                                   _ ->
                                                                       Err (clashmsg ++ "; " ++ illmsg ++ "; " ++ capturemsg)

                                                           _ ->
                                                               case capsubsts of
                                                                   [] ->
                                                                       Err (clashmsg ++ "; " ++ illmsg ++ "; " ++ errmsg)

                                                                   _ ->
                                                                       Err (clashmsg ++ "; " ++ illmsg ++ "; " ++ errmsg ++ "; " ++ capturemsg)

                                   _ ->
                                       Err clashfrmmsg
                            -}
                        in
                        -- err state is list of (ipos, errmsg)
                        case inststate of
                            -- build error
                            Err es ->
                                case checksubsts of
                                    Err msg ->
                                        ( ipos, msg )
                                            :: es
                                            |> Err

                                    -- found succeeding instance, ignore previous errors & propagate success
                                    Ok ( iposr, mfs ) ->
                                        Ok ( iposr, mfs )

                            -- propagate success
                            suc ->
                                suc
                    )
                    (Err [])
                    instances

        printerr =
            List.foldl
                (\( iposr, msg ) state ->
                    displayFactPositions iposr ++ ": " ++ msg ++ "; " ++ state
                )
                ""
    in
    case errs of
        [] ->
            case tryinstances of
                Err es ->
                    Err (printerr (List.map (\( ipos, msg ) -> ( List.map Tuple.second ipos, msg )) es))

                Ok ( ipos, genfs ) ->
                    case premtype of
                        All ->
                            Ok ( List.map Tuple.second ipos, genfs, Default )

                        Any ->
                            case List.head ipos of
                                Nothing ->
                                    Err "processFoundFacts: Unreachable case!"

                                Just ( i, pos ) ->
                                    Ok ( [ pos ], genfs, getrulev i )

        _ ->
            case premtype of
                All ->
                    Err ("Facts were not found: " ++ String.join ", " errs)

                Any ->
                    case tryinstances of
                        Err es ->
                            Err (printerr (List.map (\( ipos, msg ) -> ( List.map Tuple.second ipos, msg )) es))

                        Ok ( ipos, genfs ) ->
                            case ipos of
                                [] ->
                                    Err ("None of the possible facts were found: " ++ String.join ", " errs)

                                ( i, pos ) :: _ ->
                                    Ok ( [ pos ], genfs, getrulev i )



-- allows for backtracking in 'findFactsHelper'
-- flow:
-- try fact (apply subst to remaining afrms)
-- fail -> backtrack (try next fact)
-- note on errors:
-- the 'afrm' we start with has to fulfill everything in 'rest'
-- however, if 'afrm' already fails, 'rest' is easier fulfilled since it does not need to fulfill 'afrm' anymore!
-- hence, not necessarily every missing/failing fact is included in resulting list!


substFactsWithBackTracking : Bool -> Bool -> PremiseType -> List Fact -> ( Int, MarkedAbstract ) -> List ( Int, MarkedAbstract ) -> List TermSubst -> List ( Fact, List TermSubst, ( List FrmSubst, List TermSubst, ( List TermSubst, List TermSubst, Maybe Formula ) ) ) -> List ( Int, Result Abstract (List ( Fact, List TermSubst, ( List FrmSubst, List TermSubst, ( List TermSubst, List TermSubst, Maybe Formula ) ) )) )
substFactsWithBackTracking q heuristics premtype fs iafrm rest callowedtsubsts found =
    let
        ( i, ( m, afrm ) ) =
            iafrm

        recur =
            \instrest ucallowed ->
                findFactsHelper q heuristics premtype fs instrest ucallowed
    in
    case found of
        [] ->
            ( i, Err afrm ) :: recur rest callowedtsubsts

        ( fact, allowedtsubsts, ( fsubsts, tsubsts, errcapmfrm ) ) :: alt ->
            let
                atsubsts =
                    tsubsts
                        |> Formula.splitAbstractTermSubsts
                        |> Tuple.first

                instantiate =
                    \xs ->
                        let
                            -- index, data
                            ys =
                                List.map Tuple.first xs

                            zs =
                                List.map Tuple.second xs
                        in
                        zs
                            |> Rule.applyFrmSubstsMarked fsubsts
                            |> Rule.applyTermSubstsMarked atsubsts
                            |> List.map2 Tuple.pair ys

                try =
                    recur (instantiate rest) (Formula.updateTermSubstsWithList atsubsts callowedtsubsts)

                succAll =
                    try
                        |> List.all
                            (\x ->
                                case x of
                                    ( _, Err _ ) ->
                                        False

                                    ( _, Ok _ ) ->
                                        True
                            )

                succ =
                    case premtype of
                        All ->
                            succAll

                        Any ->
                            -- since we are already in the case '(fact, substs) :: alt'
                            True

                backtrack =
                    substFactsWithBackTracking q heuristics premtype fs iafrm rest callowedtsubsts alt
            in
            if succ then
                -- find all potential matches
                let
                    match =
                        ( fact, allowedtsubsts, ( fsubsts, tsubsts, errcapmfrm ) )

                    -- obtain rest of matches recursively
                    matches =
                        case List.head backtrack of
                            Nothing ->
                                []

                            Just h ->
                                case h of
                                    ( _, Err _ ) ->
                                        []

                                    ( _, Ok h1 ) ->
                                        h1
                in
                ( i, Ok (match :: matches) ) :: try

            else
                backtrack



-- tries to find all required abstract facts 'afrms' in list of available facts 'fs'


findFactsHelper : Bool -> Bool -> PremiseType -> List Fact -> List ( Int, MarkedAbstract ) -> List TermSubst -> List ( Int, Result Abstract (List ( Fact, List TermSubst, ( List FrmSubst, List TermSubst, ( List TermSubst, List TermSubst, Maybe Formula ) ) )) )
findFactsHelper q heuristics premtype fs afrms callowedtsubsts =
    case afrms of
        [] ->
            []

        _ ->
            let
                ( next, rest ) =
                    if heuristics then
                        Rule.getMostSpecificIndexedMarkedAbstractFact afrms

                    else
                        Rule.getNextIndexedMarkedAbstractFact afrms

                recur =
                    \instrest ->
                        findFactsHelper q heuristics premtype fs instrest callowedtsubsts
            in
            case next of
                -- cannot happen (we already checked that afrms is non-empty!)
                Nothing ->
                    ( -1, Err (AbstractFormula ( PredConst "unhandledError@findFactsHelper", [] )) ) :: recur rest

                Just afrm ->
                    findFact q fs (Tuple.second afrm) callowedtsubsts
                        |> substFactsWithBackTracking q heuristics premtype fs afrm rest callowedtsubsts



-- obtains fact positions (deps) and rule version (if possible)


findFacts : Bool -> Bool -> List Fact -> IndexedMarkedPremises -> ( List TermSubst, List TermSubst ) -> Set String -> Result String ( List FactPos, List Formula, RuleVersion )
findFacts q heuristics fs prems tsubstpair cbound =
    let
        ( premtype, afrms ) =
            prems

        ( callowedtsubsts, _ ) =
            tsubstpair
    in
    findFactsHelper q heuristics premtype fs afrms callowedtsubsts
        |> processFoundFacts q premtype afrms tsubstpair cbound



-- matches 'frm' with 'rule' and returns fact positions (deps) and rule version


matchRule : Bool -> Bool -> Formula -> Rule -> List Fact -> Result String ( List FactPos, List Formula, RuleVersion )
matchRule q heuristics frm rule fs =
    let
        markedrule =
            rule
                |> Rule.markPremises

        ( names, markedprems, conclusion ) =
            markedrule

        name =
            case List.head names of
                Just x ->
                    x

                Nothing ->
                    "unnamed rule"

        -- given conclusion, returns (partially) instantiated premises
        instantiatePremises =
            \con ->
                let
                    -- deconstruct conclusion into formula & allowed term substitution
                    ( cfrm, callowedtsubsts ) =
                        con
                in
                -- match cfrm (abstract rule conclusion) with frm (specific formula, i.e., the formula in the current proof step being checked)
                case matchFormulas cfrm frm of
                    -- "successful" match using the following substitutions
                    -- note that every fsubst is of the form (placeholder -> instantiated formula), i.e., always abstract
                    -- tsubsts non-empty only if cfrm contains "specific part" (e.g., when quantifiers are introduced -- allI, exI)
                    -- - on formula level, e.g. 'matchFormulas P(?1) P(x)', yields only abstract tsubsts, e.g. ?1 -> x
                    -- - on both formula & term level, e.g. 'matchFormulas P(x) P(y)', yields specific tsubsts, e.g. x -> y (does never make sense: illegal)
                    Ok ( fsubsts, tsubsts, ( errsubsts, cap, _ ) ) ->
                        let
                            -- obtain left abstract and left specific part of tsubsts
                            ( atsubsts, ctsubsts ) =
                                Formula.splitAbstractTermSubsts tsubsts

                            -- 1) instantiate premises (on formula level)
                            finst =
                                Rule.applyFrmSubstsToMarkedPrems markedprems fsubsts

                            -- 2) instantiate premises (on term level)
                            tinst =
                                Rule.applyTermSubstsToMarkedPrems finst atsubsts

                            -- 3) also instantiate allowed substitution of conclusion (remains unaltered for default rules)
                            updatedcallowedtsubsts =
                                Formula.updateTermSubstsWithList atsubsts callowedtsubsts

                            -- checks if a required term substitution (x,y) is allowed
                            isAllowed =
                                \( x, y ) ->
                                    List.any
                                        (\( xc, yc ) ->
                                            x == xc && (y == yc || Formula.abstractTerm yc)
                                        )
                                        updatedcallowedtsubsts

                            -- left or right abstract substitutions are never illegal (at this point)
                            -- left and right specific tsubsts are illegal if not explicitly allowed
                            illegal =
                                ctsubsts
                                    |> List.filter (\( x, y ) -> not (Formula.abstractTerm x || isAllowed ( x, y )))

                            -- formula substitutions may clash (e.g. LEM)
                            clashingfrm =
                                Formula.clash fsubsts

                            -- term substitutions may clash (e.g. =i)
                            clashingterm =
                                Formula.clash tsubsts
                        in
                        if List.isEmpty clashingfrm then
                            case cap of
                                [] ->
                                    case (illegal ++ errsubsts) |> Utils.removeDuplicates of
                                        [] ->
                                            if List.isEmpty clashingterm then
                                                Ok ( tinst, ( updatedcallowedtsubsts, tsubsts ) )

                                            else
                                                Err ("Clashing Term Substitutions: " ++ Formula.displayTermSubsts clashingterm)

                                        ill :: [] ->
                                            Err ("Illegal Term Substitution: " ++ Formula.displayTermSubst ill)

                                        ills ->
                                            Err ("Illegal Term Substitutions: " ++ Formula.displayTermSubsts ills)

                                c :: [] ->
                                    Err ("Term Substitution leads to Variable Capturing: " ++ Formula.displayTermSubst c)

                                _ ->
                                    Err ("Term Substitutions lead to Variable Capturing: " ++ Formula.displayTermSubsts cap)

                        else
                            Err ("Clashing Formula Substitutions: " ++ Formula.displayFrmSubsts q clashingfrm)

                    Err ( details, ( frm1, frm2 ) ) ->
                        Err (Formula.displayFormula q frm1 ++ " does not match with " ++ Formula.displayFormula q frm2 ++ "! Details: " ++ details)

        -- given conclusion, returns position of found facts and rule version
        getFacts =
            \con ->
                case instantiatePremises con of
                    Err msg ->
                        Err msg

                    Ok ( instprems, substpair ) ->
                        let
                            ( premtype, markedafrms ) =
                                instprems
                        in
                        findFacts q heuristics fs ( premtype, List.indexedMap Tuple.pair markedafrms ) substpair (Formula.boundVars (Tuple.first con))
    in
    case conclusion of
        Conclusion cfrm ->
            getFacts cfrm

        -- left option succeeds ==> V1
        -- right option succeeds ==> V2
        ConclusionEither cfrm1 cfrm2 ->
            case getFacts cfrm1 of
                Err msg1 ->
                    case getFacts cfrm2 of
                        Err msg2 ->
                            Err ("Every possible instantiation failed:\n1. " ++ msg1 ++ "\n2. " ++ msg2)

                        Ok ( pos, genfs, _ ) ->
                            Ok ( pos, genfs, V2 )

                Ok ( pos, genfs, _ ) ->
                    Ok ( pos, genfs, V1 )



-- proof checker


checker : Bool -> Bool -> RuleSubset -> ( Maybe Seq, ( Proof, PosInBlock ) ) -> CheckState -> CheckState
checker q heuristics sub problem state =
    let
        ( ( level, i ), fs, ( pcs, bcs ) ) =
            state

        ( mseq, ( prf, posinblock ) ) =
            problem

        blockbegin =
            case posinblock of
                BlockBegin ->
                    True

                BlockBeginEnd ->
                    True

                _ ->
                    False

        -- if no sequent was given, still check proof, treat conclusion as bottom
        ( prems, conclusion ) =
            case mseq of
                Just seq ->
                    seq

                Nothing ->
                    ( [], Bot )

        n =
            i + 1

        defstate =
            ( ( level, n ), fs, ( pcs, bcs ) )

        blockstate =
            ( ( level + 1, i ), fs, ( pcs, bcs ) )

        error =
            checkError defstate

        success =
            checkSuccess defstate

        qed =
            checkQED defstate

        blocksuccess =
            checkBlockSuccess

        skipemptyblock =
            ( ( level, n ), fs, ( pcs, bcs ++ [ ( BlockError "Empty block!", Range n n ) ] ) )
    in
    case prf of
        Step frm jfc ->
            let
                fct =
                    LineFact frm (LineNo n)

                rfct =
                    \deps ->
                        fct deps False

                nodeps =
                    fct [] False

                -- mark fact as assumption!
                assmdeps =
                    fct [] True

                succ =
                    -- derived conclusion, outermost block ==> QED
                    if frm == conclusion && level == 0 then
                        qed

                    else
                        success
            in
            case jfc of
                Premise ->
                    if List.member frm prems then
                        succ nodeps [] Default

                    else
                        error ("'" ++ Formula.displayFormula q frm ++ "'" ++ " is not a premise!")

                -- whether all assumptions are discharged is checked implicitly: if a rule requires a block then this abstract block has to allow for assumptions in order to match with a blockfact containing assumptions
                Assumption ->
                    -- no assumptions in outermost block
                    if level > 0 && blockbegin then
                        succ assmdeps [] Default

                    else
                        error "Assumptions are only allowed at the beginning of a box!"

                RuleName s ->
                    case Rule.getRule sub s of
                        Nothing ->
                            error ("There is no rule named '" ++ s ++ "'!")

                        Just rule ->
                            case matchRule q heuristics frm rule fs of
                                Err msg ->
                                    error msg

                                Ok ( pos, genfs, rulev ) ->
                                    succ (rfct pos) genfs rulev

        Block vs ps ->
            case ps of
                [] ->
                    skipemptyblock

                _ ->
                    let
                        ( ( l, k ), facts, cs ) =
                            ps
                                |> assignPosInBlock
                                |> List.map (\x -> ( mseq, x ))
                                |> List.foldl (checker q heuristics sub) blockstate

                        blockfact =
                            BlockFact vs (Utils.without fs facts) (Range n k)
                    in
                    -- we go inside the block with level + 1, hence, we have to subtract 1 when leaving the block
                    blocksuccess ( ( l - 1, k ), fs, cs ) blockfact

        Begin ps ->
            case ps of
                [] ->
                    error "Empty proof!"

                _ ->
                    ps
                        |> assignPosInBlock
                        |> List.map (\x -> ( mseq, x ))
                        |> List.foldl (checker q heuristics sub) state



-- checks if 'f' contains 'pos' as a reference?


referencedHelper : FactPos -> Fact -> Bool
referencedHelper pos f =
    case f of
        LineFact _ _ deps _ ->
            List.any (\p -> p == pos) deps

        BlockFact _ fs _ ->
            List.any (\g -> referencedHelper pos g) fs



-- checks if 'f' is referenced in 'fs'


referenced : Fact -> List Fact -> Bool
referenced f fs =
    case fs of
        [] ->
            False

        _ ->
            List.any (\g -> referencedHelper (getFactPos f) g) fs



-- assigns 'BlockPosition' to list of facts 'fs' (or list of proof type)
-- begin | anywhere | end | beginend


assignPosInBlock : List a -> List ( a, PosInBlock )
assignPosInBlock fs =
    let
        ( xs, mlast ) =
            Utils.splitLast fs

        zs =
            case xs of
                [] ->
                    []

                y :: ys ->
                    ( y, BlockBegin ) :: List.map (\x -> ( x, BlockAnywhere )) ys
    in
    case mlast of
        Just last ->
            -- single line block
            if List.isEmpty zs then
                [ ( last, BlockBeginEnd ) ]

            else
                zs ++ [ ( last, BlockEnd ) ]

        Nothing ->
            zs



-- step function to update the redundancy state


redundancyStep : ( Fact, PosInBlock ) -> ( List ( Fact, PosInBlock ), List Bool, List ( Bool, FactPos ) ) -> ( List ( Fact, PosInBlock ), List Bool, List ( Bool, FactPos ) )
redundancyStep fp xs =
    let
        ( cfs, lrs, brs ) =
            xs

        fs =
            List.map Tuple.first cfs

        ( f, bp ) =
            fp
    in
    case cfs of
        [] ->
            ( [], lrs, brs )

        _ :: ys ->
            case f of
                LineFact frm _ _ assumed ->
                    if referenced f fs || bp == BlockBegin && assumed || bp == BlockEnd || bp == BlockBeginEnd then
                        ( ys, lrs ++ [ False ], brs )

                    else
                        ( ys, lrs ++ [ True ], brs )

                BlockFact _ blockfacts pos ->
                    let
                        zs =
                            assignPosInBlock blockfacts

                        ( _, lrsb, brsb ) =
                            List.foldl redundancyStep ( zs, lrs, brs ) zs
                    in
                    if referenced f fs then
                        ( ys, lrsb, ( False, pos ) :: brsb )

                    else
                        ( ys, lrsb, ( True, pos ) :: brsb )



-- adds warnings where necessary (blocks)


addRedundancyWarningBlock : List ( BlockCheck, FactPos ) -> List ( Bool, FactPos ) -> List ( BlockCheck, FactPos )
addRedundancyWarningBlock bcs bs =
    case bs of
        [] ->
            bcs

        ( x, pos ) :: xs ->
            case bcs of
                [] ->
                    []

                ( y, _ ) :: ys ->
                    let
                        warning =
                            BlockWarning "Box currently not referenced, hence, redundant."

                        recur =
                            \z -> z :: addRedundancyWarningBlock ys xs
                    in
                    case y of
                        BlockSuccess ->
                            if x then
                                recur ( warning, pos )

                            else
                                recur ( y, pos )

                        _ ->
                            recur ( y, pos )



-- adds warnings where necessary (lines)


addRedundancyWarningLine : List ProofCheck -> List Bool -> List ProofCheck
addRedundancyWarningLine pcs bs =
    case bs of
        [] ->
            pcs

        x :: xs ->
            case pcs of
                [] ->
                    []

                y :: ys ->
                    let
                        w =
                            LineWarning "Line currently not referenced, hence, redundant."

                        recur =
                            \z -> z :: addRedundancyWarningLine ys xs
                    in
                    case y of
                        LineSuccess _ _ _ ->
                            if x then
                                recur w

                            else
                                recur y

                        _ ->
                            recur y



-- adds redundancy warnings to result of proof checking


addRedundancyWarning : CheckResult -> ( List Bool, List ( Bool, FactPos ) ) -> Result String CheckResult
addRedundancyWarning a b =
    let
        ( pcs, bcs ) =
            a

        ( bps, bbs ) =
            b

        lenpcs =
            List.length pcs

        lenbcs =
            List.length bcs

        lenbps =
            List.length bps

        lenbbs =
            List.length bbs
    in
    if lenpcs /= lenbps || lenbcs /= lenbbs then
        [ lenpcs, lenbps, lenbcs, lenbbs ]
            |> List.map String.fromInt
            |> String.join ","
            |> (\x -> Err ("addRedundancyWarning: length mismatch! Debug information: (" ++ x ++ ")"))

    else
        Ok ( addRedundancyWarningLine pcs bps, addRedundancyWarningBlock bcs bbs )



-- checks for redundant lines and blocks in the current proof checker state


redundancyCheck : CheckState -> Result String CheckState
redundancyCheck state =
    let
        ( i, fs, ( xs, ys ) ) =
            state

        fsp =
            assignPosInBlock fs

        ( _, xsr, ysr ) =
            List.foldl redundancyStep ( fsp, [], [] ) fsp

        ws =
            addRedundancyWarning ( xs, ys ) ( xsr, ysr )
    in
    case ws of
        Ok r ->
            Ok ( i, fs, r )

        Err msg ->
            Err msg



-- build the proof and checks if it is free of errors AND last line ends the proof (QED)


buildAndQuickCheck : Bool -> RuleSubset -> ParserConfig -> ModelDefs.GoalType -> List ModelDefs.LineType -> Bool
buildAndQuickCheck heuristics sub cfg g ls =
    case Proof.buildProofFromLines sub cfg g ls of
        Err _ ->
            False

        Ok ( mseq, prf, buildstate ) ->
            if
                buildstate
                    |> List.any
                        (\lstate ->
                            case lstate of
                                BuildError _ ->
                                    True

                                _ ->
                                    False
                        )
            then
                False

            else
                case check cfg.qtype heuristics sub ( mseq, prf ) of
                    Err _ ->
                        False

                    Ok x ->
                        stateToResult x
                            |> resultQED
