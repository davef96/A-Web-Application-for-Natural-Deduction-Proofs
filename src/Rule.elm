-- module to manage rules


module Rule exposing (..)

import Formula exposing (Formula(..), FrmSubst, Operator(..), Term(..), TermSubst)
import ModelDefs exposing (RuleSubset(..))
import Utils



-- phi[t/x]


type alias FrmWithSubst =
    ( Formula, List TermSubst )



-- type for block assumptions


type alias BlockAssms =
    List FrmWithSubst



-- type for matching with rules (premises)
-- a block allows to fix a list of variables, that may or may not be exported (last line in block contains variable)


type Abstract
    = AbstractFormula FrmWithSubst
    | AbstractBlock (List ( String, Bool )) BlockAssms FrmWithSubst



-- do all of the premises have to be satisfied (conjunction) or does "at least one" suffice (disjunction) ?


type PremiseType
    = All
    | Any



-- type alias for rule premises


type alias RulePremises =
    ( PremiseType, List Abstract )


type alias IndexedRulePremises =
    ( PremiseType, List ( Int, Abstract ) )



-- type for rule conclusion
-- note that a block cannot be a conclusion, hence, the new type definition


type RuleConclusion
    = Conclusion FrmWithSubst
    | ConclusionEither FrmWithSubst FrmWithSubst



-- (accepted rule names, premises, conclusion)


type alias Rule =
    ( List String, RulePremises, RuleConclusion )



-- rule version


type RuleVersion
    = V1
    | V2
    | Default


displayFrmWithSubst : Bool -> FrmWithSubst -> String
displayFrmWithSubst q f =
    let
        ( frm, tsubst ) =
            f
    in
    if List.isEmpty tsubst then
        Formula.displayFormula q frm

    else
        Formula.displayFormulaHelper q frm ++ Formula.displayTermSubsts tsubst


displayAbstract : Bool -> Abstract -> String
displayAbstract q a =
    case a of
        AbstractFormula frm ->
            displayFrmWithSubst q frm

        AbstractBlock vs assms c ->
            let
                fixvars =
                    List.map (\( v, b ) -> "?v" ++ v) vs

                strfix =
                    if List.isEmpty fixvars then
                        ""

                    else
                        "fix " ++ String.join "," fixvars ++ "; "

                assume =
                    List.map (displayFrmWithSubst q) assms

                strassume =
                    if List.isEmpty assume then
                        ""

                    else
                        "assume " ++ String.join "," assume ++ "; "

                strshow =
                    "show " ++ displayFrmWithSubst q c
            in
            "Block(" ++ strfix ++ strassume ++ strshow ++ ")"



-- predicate constant represents abstract variable (placeholder for a formula)


abstractPredConst : Formula -> Bool
abstractPredConst a =
    case a of
        PredConst s ->
            Formula.abstract s

        _ ->
            False



-- obtains abstract variables (predicate constant placeholders) in formula


abstractVars : Formula -> List Formula
abstractVars frm =
    let
        recur =
            \a b -> abstractVars a ++ abstractVars b
    in
    case frm of
        PredConst s ->
            if Formula.abstract s then
                [ PredConst s ]

            else
                []

        Neg a ->
            abstractVars a

        Conj a b ->
            recur a b

        Disj a b ->
            recur a b

        Impl a b ->
            recur a b

        Iff a b ->
            recur a b

        _ ->
            []



-- factor to determine block specificity


blockFactor : Int
blockFactor =
    5



-- how specific is a formula?
-- First: counts number of occurring instantiated atoms in formula
-- Second: counts connectives/quantifiers in formula


specificity : Formula -> ( Int, Int )
specificity f =
    let
        recur1 =
            \a ->
                let
                    ( x, y ) =
                        specificity a
                in
                ( x, y + 1 )

        recur2 =
            \a b ->
                let
                    ( x1, y1 ) =
                        specificity a

                    ( x2, y2 ) =
                        specificity b
                in
                ( x1 + x2, y1 + y2 + 1 )
    in
    case f of
        Neg a ->
            recur1 a

        Conj a b ->
            recur2 a b

        Disj a b ->
            recur2 a b

        Impl a b ->
            recur2 a b

        Iff a b ->
            recur2 a b

        Exists x a ->
            recur1 a

        ForAll x a ->
            recur1 a

        PredConst s ->
            if Formula.abstract s then
                ( 0, 0 )

            else
                ( 1, 0 )

        _ ->
            ( 1, 0 )



-- calculates specificity of given abstract fact
-- currently does not factor in term substitutions


abstractSpecificity : Abstract -> ( Int, Int )
abstractSpecificity f =
    case f of
        AbstractFormula ( frm, _ ) ->
            specificity frm

        AbstractBlock _ assms ( frm2, _ ) ->
            let
                ( ix, jx ) =
                    List.foldl
                        (\( frm, _ ) ( istate, jstate ) ->
                            let
                                ( i1, j1 ) =
                                    specificity frm
                            in
                            ( i1 + istate, j1 + jstate )
                        )
                        ( 0, 0 )
                        assms

                ( iy, jy ) =
                    specificity frm2

                ib =
                    blockFactor * (ix + iy)

                jb =
                    if (jx + jy) == 0 then
                        blockFactor + List.length assms

                    else
                        blockFactor * (jx + jy) + 1
            in
            ( ib, jb )



-- compare function to be able to sort abstract facts in descending order, i.e., the most specific fact will be the head of the list
-- 'compare x y' yields LT iff x > y (x more specific than y)


indexedSpecificityComparison : ( Int, Abstract ) -> ( Int, Abstract ) -> Order
indexedSpecificityComparison x y =
    let
        ( index1, a1 ) =
            x

        ( index2, a2 ) =
            y

        ( i1, j1 ) =
            abstractSpecificity a1

        ( i2, j2 ) =
            abstractSpecificity a2
    in
    case compare i1 i2 of
        LT ->
            GT

        GT ->
            LT

        EQ ->
            case compare j1 j2 of
                LT ->
                    GT

                GT ->
                    LT

                EQ ->
                    case compare index1 index2 of
                        LT ->
                            GT

                        GT ->
                            LT

                        EQ ->
                            EQ


specificityComparison : Abstract -> Abstract -> Order
specificityComparison x y =
    let
        ( i1, j1 ) =
            abstractSpecificity x

        ( i2, j2 ) =
            abstractSpecificity y
    in
    case compare i1 i2 of
        LT ->
            GT

        GT ->
            LT

        EQ ->
            case compare j1 j2 of
                LT ->
                    GT

                GT ->
                    LT

                EQ ->
                    EQ


getMostSpecificIndexedAbstractFact : List ( Int, Abstract ) -> ( Maybe ( Int, Abstract ), List ( Int, Abstract ) )
getMostSpecificIndexedAbstractFact afs =
    let
        sorted =
            List.sortWith indexedSpecificityComparison afs
    in
    case sorted of
        [] ->
            ( Nothing, [] )

        x :: xs ->
            ( Just x, xs )



-- obtains most specific abstract fact from given list


getMostSpecificAbstractFact : List Abstract -> ( Maybe Abstract, List Abstract )
getMostSpecificAbstractFact afs =
    let
        sorted =
            List.sortWith specificityComparison afs
    in
    case sorted of
        [] ->
            ( Nothing, [] )

        x :: xs ->
            ( Just x, xs )



-- deconstruct an abstract frm into a tuple (op, args, allowed tsubsts)


deconstructAbstract : Abstract -> Maybe ( Operator, List Formula, List TermSubst )
deconstructAbstract afrm =
    case afrm of
        AbstractFormula ( frm, tsubsts ) ->
            Formula.deconstructFormula frm
                |> (\( op, f ) -> Just ( op, f, tsubsts ))

        AbstractBlock _ _ _ ->
            Nothing



-- replaces sub formula, using the given substitution


replaceAbstractSubFormula : FrmSubst -> Abstract -> Abstract
replaceAbstractSubFormula fsubst afrm =
    case afrm of
        AbstractFormula ( frm, tsubsts ) ->
            AbstractFormula ( Formula.replaceSubFormula fsubst frm, tsubsts )

        AbstractBlock vs assms ( frm2, tsubsts2 ) ->
            AbstractBlock vs (List.map (\( frm, tsubsts1 ) -> ( Formula.replaceSubFormula fsubst frm, tsubsts1 )) assms) ( Formula.replaceSubFormula fsubst frm2, tsubsts2 )



-- replace term, using the given substitution


replaceAbstractTerm : TermSubst -> Abstract -> Abstract
replaceAbstractTerm tsubst afrm =
    case afrm of
        AbstractFormula ( frm, tsubsts1 ) ->
            AbstractFormula ( Formula.replaceAllOccurrencesBlindly tsubst frm, Formula.updateTermSubsts tsubst tsubsts1 )

        AbstractBlock vs assms ( frm2, tsubsts2 ) ->
            AbstractBlock vs (List.map (\( frm1, tsubsts1 ) -> ( Formula.replaceAllOccurrencesBlindly tsubst frm1, Formula.updateTermSubsts tsubst tsubsts1 )) assms) ( Formula.replaceAllOccurrencesBlindly tsubst frm2, Formula.updateTermSubsts tsubst tsubsts2 )


applyTermSubsts : List TermSubst -> List Abstract -> List Abstract
applyTermSubsts tsubsts afrms =
    List.foldr
        (\x state ->
            List.foldl replaceAbstractTerm x tsubsts :: state
        )
        []
        afrms


applyTermSubstsToPrems : RulePremises -> List TermSubst -> RulePremises
applyTermSubstsToPrems prems tsubsts =
    let
        ( premtype, afrms ) =
            prems
    in
    ( premtype, applyTermSubsts tsubsts afrms )


applyFrmSubsts : List FrmSubst -> List Abstract -> List Abstract
applyFrmSubsts fsubsts afrms =
    List.foldr
        (\x state ->
            List.foldl replaceAbstractSubFormula x fsubsts :: state
        )
        []
        afrms


applyFrmSubstsToPrems : RulePremises -> List FrmSubst -> RulePremises
applyFrmSubstsToPrems prems fsubsts =
    let
        ( premtype, afrms ) =
            prems
    in
    ( premtype, applyFrmSubsts fsubsts afrms )



-- the (currently) accepted rules
-- natural numbers are used for (abstract) predicates/atoms to make sure the abstract formulas differ from an actually instantiated formula
-- note that the rules that cannot be fully instantiated simply by their conclusion, are marked as 'partial' (they have to be instantiated while searching for the required facts)


currentRules : RuleSubset -> List Rule
currentRules sub =
    let
        impI =
            ( [ "⟶i" ], ( All, [ AbstractBlock [] [ ( PredConst "1", [] ) ] ( PredConst "2", [] ) ] ), Conclusion ( Impl (PredConst "1") (PredConst "2"), [] ) )

        -- partial
        impE =
            ( [ "⟶e", "mp" ], ( All, [ AbstractFormula ( Impl (PredConst "1") (PredConst "2"), [] ), AbstractFormula ( PredConst "1", [] ) ] ), Conclusion ( PredConst "2", [] ) )

        conjI =
            ( [ "∧i" ], ( All, [ AbstractFormula ( PredConst "1", [] ), AbstractFormula ( PredConst "2", [] ) ] ), Conclusion ( Conj (PredConst "1") (PredConst "2"), [] ) )

        conjE =
            ( [ "∧e" ], ( All, [ AbstractFormula ( Conj (PredConst "1") (PredConst "2"), [] ) ] ), ConclusionEither ( PredConst "1", [] ) ( PredConst "2", [] ) )

        disjI =
            ( [ "∨i" ], ( Any, [ AbstractFormula ( PredConst "1", [] ), AbstractFormula ( PredConst "2", [] ) ] ), Conclusion ( Disj (PredConst "1") (PredConst "2"), [] ) )

        -- partial (!)
        disjE =
            ( [ "∨e" ], ( All, [ AbstractFormula ( Disj (PredConst "1") (PredConst "2"), [] ), AbstractBlock [] [ ( PredConst "1", [] ) ] ( PredConst "3", [] ), AbstractBlock [] [ ( PredConst "2", [] ) ] ( PredConst "3", [] ) ] ), Conclusion ( PredConst "3", [] ) )

        notI =
            ( [ "¬i" ], ( All, [ AbstractBlock [] [ ( PredConst "1", [] ) ] ( Bot, [] ) ] ), Conclusion ( Neg (PredConst "1"), [] ) )

        -- partial
        notE =
            ( [ "¬e" ], ( All, [ AbstractFormula ( PredConst "1", [] ), AbstractFormula ( Neg (PredConst "1"), [] ) ] ), Conclusion ( Bot, [] ) )

        topI =
            ( [ "⊤i" ], ( All, [] ), Conclusion ( Top, [] ) )

        botE =
            ( [ "⊥e" ], ( All, [ AbstractFormula ( Bot, [] ) ] ), Conclusion ( PredConst "1", [] ) )

        dnI =
            ( [ "¬¬i", "dni" ], ( All, [ AbstractFormula ( PredConst "1", [] ) ] ), Conclusion ( Neg (Neg (PredConst "1")), [] ) )

        dnE =
            ( [ "¬¬e", "dne" ], ( All, [ AbstractFormula ( Neg (Neg (PredConst "1")), [] ) ] ), Conclusion ( PredConst "1", [] ) )

        pbc =
            ( [ "pbc" ], ( All, [ AbstractBlock [] [ ( Neg (PredConst "1"), [] ) ] ( Bot, [] ) ] ), Conclusion ( PredConst "1", [] ) )

        lem =
            ( [ "lem" ], ( All, [] ), Conclusion ( Disj (PredConst "1") (Neg (PredConst "1")), [] ) )

        -- partial
        mt =
            ( [ "mt" ], ( All, [ AbstractFormula ( Impl (PredConst "1") (PredConst "2"), [] ), AbstractFormula ( Neg (PredConst "2"), [] ) ] ), Conclusion ( Neg (PredConst "1"), [] ) )

        iffI =
            ( [ "⟷i" ], ( All, [ AbstractFormula ( Impl (PredConst "1") (PredConst "2"), [] ), AbstractFormula ( Impl (PredConst "2") (PredConst "1"), [] ) ] ), Conclusion ( Iff (PredConst "1") (PredConst "2"), [] ) )

        iffE =
            ( [ "⟷e" ], ( All, [ AbstractFormula ( Iff (PredConst "1") (PredConst "2"), [] ) ] ), ConclusionEither ( Impl (PredConst "1") (PredConst "2"), [] ) ( Impl (PredConst "2") (PredConst "1"), [] ) )

        eqI =
            ( [ "＝i" ], ( All, [] ), Conclusion ( Equals ( Var "1", Var "1" ), [] ) )

        eqE =
            ( [ "＝e" ], ( All, [ AbstractFormula ( Equals ( Var "-1", Var "-2" ), [] ), AbstractFormula ( PredConst "1", [ ( Var "3", Var "-1" ) ] ) ] ), Conclusion ( PredConst "1", [ ( Var "3", Var "-2" ) ] ) )

        allI =
            ( [ "∀i" ], ( All, [ AbstractBlock [ ( "1", True ) ] [] ( PredConst "1", [ ( Var "2", Var "1" ) ] ) ] ), Conclusion ( ForAll "2" (PredConst "1"), [] ) )

        allE =
            ( [ "∀e" ], ( All, [ AbstractFormula ( ForAll "1" (PredConst "1"), [] ) ] ), Conclusion ( PredConst "1", [ ( Var "1", Var "-2" ) ] ) )

        exI =
            ( [ "∃i" ], ( All, [ AbstractFormula ( PredConst "1", [ ( Var "1", Var "-2" ) ] ) ] ), Conclusion ( Exists "1" (PredConst "1"), [] ) )

        exE =
            ( [ "∃e" ], ( All, [ AbstractFormula ( Exists "1" (PredConst "1"), [] ), AbstractBlock [ ( "2", False ) ] [ ( PredConst "1", [ ( Var "1", Var "2" ) ] ) ] ( PredConst "2", [] ) ] ), Conclusion ( PredConst "2", [] ) )

        cp =
            ( [ "cp", "cpy", "copy" ], ( All, [ AbstractFormula ( PredConst "1", [] ) ] ), Conclusion ( PredConst "1", [] ) )

        -- subsets
        -- 1) intuitionistic propositional logic
        intprop =
            [ impI, impE, conjI, conjE, disjI, disjE, notI, notE, topI, botE, dnI, mt, iffI, iffE ]

        -- 2) (classical) propositional logic
        prop =
            intprop ++ [ dnE, pbc, lem ]

        -- 3) intuitionistic first-order logic
        intfol =
            intprop ++ [ eqI, eqE, allI, allE, exI, exE ]

        -- 4) (classical) first-order logic
        fol =
            intfol ++ [ dnE, pbc, lem ]
    in
    case sub of
        NoRules ->
            []

        IntProp ->
            cp :: intprop

        Prop ->
            cp :: prop

        IntFOL ->
            cp :: intfol

        FOL ->
            cp :: fol



-- list of all current rule names


currentRuleNames : RuleSubset -> List String
currentRuleNames sub =
    List.concatMap
        (\( names, _, _ ) ->
            names
        )
        (currentRules sub)


getRuleHelper : List Rule -> String -> Maybe Rule
getRuleHelper rs s =
    case rs of
        [] ->
            Nothing

        x :: xs ->
            let
                ( names, _, _ ) =
                    x

                recur =
                    getRuleHelper xs s
            in
            if List.member s names then
                Just x

            else
                recur



-- obtains the rule associated with the given name


getRule : RuleSubset -> String -> Maybe Rule
getRule sub =
    getRuleHelper (currentRules sub)
