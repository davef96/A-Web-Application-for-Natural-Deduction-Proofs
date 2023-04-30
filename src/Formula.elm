-- this module defines the ADT for formulas, and provides parsers & helper functions


module Formula exposing (..)

import Char
import Keywords
import List
import ModelDefs exposing (ParserConfig)
import Parser exposing ((|.), (|=), Parser, backtrackable, end, lazy, oneOf, spaces, succeed, symbol, variable)
import Pratt exposing (..)
import Set exposing (Set, singleton, union)
import String
import Utils



-- type for terms
-- removed constants, see below


type Term
    = Var String
    | Func String (List Term) -- constants have to be expressed as 'f()' in order to not impose any restrictions in parsing vars



-- type for FOL formulas
-- addition: constructor 'Iff' for '⟷'
-- lines marked with '*' extend propositional logic to FOL


type Formula
    = PredConst String -- Atom in propositional logic
    | Predicate String (List Term) -- *
    | Equals ( Term, Term ) -- *
    | Bot
    | Top
    | Neg Formula
    | Conj Formula Formula
    | Disj Formula Formula
    | Impl Formula Formula
    | Iff Formula Formula
    | ForAll String Formula -- *
    | Exists String Formula -- *



-- type alias for formula replacement/single-substitution (simple replacement of lhs with rhs)


type alias FrmSubst =
    ( Formula, Formula )



-- type alias for term replacement/single-substitution (simple replacement of lhs with rhs)


type alias TermSubst =
    ( Term, Term )



-- type alias for sequents (list of premises, conclusion)


type alias Seq =
    ( List Formula, Formula )



-- helper to parse something arbitrary between parentheses


parens : Parser a -> Parser a
parens p =
    succeed identity
        |. symbol "("
        |. spaces
        |= p
        |. spaces
        |. symbol ")"



-- the expression parser


expression : ParserConfig -> Parser Formula
expression cfg =
    let
        qprec =
            if cfg.qtype then
                4

            else
                0

        quantifiers =
            [ quantifier cfg qprec (symbol "∀") ForAll
            , quantifier cfg qprec (symbol "∃") Exists
            ]

        xs =
            [ literal (base cfg)
            , prefix 4 (symbol "¬") Neg
            , parenthesizedExpression
            ]

        ys =
            if cfg.fol then
                xs ++ quantifiers

            else
                xs
    in
    Pratt.expression
        { oneOf =
            ys
        , andThenOneOf =
            [ infixRight 1 (symbol "⟶") Impl
            , infixRight 1 (symbol "⟷") Iff
            , infixRight
                (if cfg.conjstronger then
                    3

                 else
                    2
                )
                (symbol "∧")
                Conj
            , infixRight 2 (symbol "∨") Disj
            ]
        , spaces = Parser.spaces
        }



-- parser for quantifiers/binders, takes precedence, symbol parser, constructor
-- format 1: '∀x. ϕ'
-- format 2: '∀x negExpr' | '∀x (ϕ)'


quantifier : ParserConfig -> Int -> Parser () -> (String -> expr -> expr) -> Config expr -> Parser expr
quantifier cfg precedence operator apply config =
    if cfg.qtype then
        succeed apply
            |. operator
            |= var cfg
            |= subExpression precedence config

    else
        succeed apply
            |. operator
            |= var cfg
            |. symbol "."
            |= subExpression precedence config



-- parser for expressions in parentheses


parenthesizedExpression : Config Formula -> Parser Formula
parenthesizedExpression config =
    parens <| subExpression 0 config



-- the final formula parser


formula : ParserConfig -> Parser Formula
formula cfg =
    succeed identity
        |= expression cfg
        |. end



-- base type to construct formulas from by using the operator table defined in the expression parser


baseFOL : ParserConfig -> Parser Formula
baseFOL cfg =
    oneOf
        [ succeed Bot
            |. symbol "⊥"
        , succeed Top
            |. symbol "⊤"
        , succeed Equals
            |= oneOf
                [ backtrackable (parens <| equality cfg)
                , equality cfg
                ]
        , succeed Predicate
            |= backtrackable pred
            |= args cfg
        , succeed PredConst
            |= pred
        ]



-- base type for propositional formulas (no term equality, no predicates with args, no binders)


baseProp : ParserConfig -> Parser Formula
baseProp cfg =
    oneOf
        [ succeed Bot
            |. symbol "⊥"
        , succeed Top
            |. symbol "⊤"
        , succeed PredConst
            -- Atom
            |= var cfg
        ]



-- chooses the corresponding base parser according to the arg


base : ParserConfig -> Parser Formula
base cfg =
    if cfg.fol then
        baseFOL cfg

    else
        baseProp cfg



-- parser for term equality


equality : ParserConfig -> Parser ( Term, Term )
equality cfg =
    succeed Tuple.pair
        |= lazy (\_ -> term cfg)
        |. spaces
        |. symbol "＝"
        |. spaces
        |= lazy (\_ -> term cfg)



-- parser for terms
-- currently 'func' = 'var', so 'func' needs to be backtrackable, it succeeds if followed by args
-- constants, i.e., 0-ary functions, can be expressed with 'some_name()'


term : ParserConfig -> Parser Term
term cfg =
    oneOf
        [ succeed Func
            |= backtrackable (func cfg)
            |= lazy (\_ -> args cfg)
        , succeed Var
            |= var cfg
        ]



-- parser for function/predicate arguments (term list in parentheses)


args : ParserConfig -> Parser (List Term)
args cfg =
    Parser.sequence
        { start = "("
        , separator = ","
        , end = ")"
        , spaces = spaces
        , item = term cfg
        , trailing = Parser.Forbidden
        }



-- helper for parsing variables
-- takes set of reserved var names and returns variable parser
-- if 'fol' then greek letters are not allowed for vars since they are only allowed for predicates


varHelper : ParserConfig -> Set String -> Parser String
varHelper cfg rvs =
    variable
        { start = \c -> Char.isLower c || (not cfg.fol && Keywords.isGreekLetterLower c)
        , inner = \c -> Char.isAlphaNum c || c == '_'
        , reserved = Set.union (Keywords.reserved cfg.kword) rvs
        }



-- helper for parsing variables


var : ParserConfig -> Parser String
var cfg =
    varHelper cfg Set.empty



-- helper for parsing function names
-- can only be used if function has arguments (parentheses after function name) to be able to differ between functions and variables


func : ParserConfig -> Parser String
func =
    var



-- helper for parsing predicate names


pred : Parser String
pred =
    variable
        { start = \c -> Char.isUpper c || Keywords.isGreekLetter c
        , inner = \c -> Char.isAlphaNum c || c == '_' || Keywords.isGreekLetter c
        , reserved = Set.empty
        }



-- parser for premises (list of formulas)


prems : ParserConfig -> Parser (List Formula)
prems cfg =
    Parser.sequence
        { start = ""
        , separator = ","
        , end = "⊢"
        , spaces = spaces
        , item = expression cfg -- formula requires end afterwards (!)
        , trailing = Parser.Forbidden
        }



-- parser for sequents (premises, conclusion)


sequent : ParserConfig -> Parser Seq
sequent cfg =
    succeed Tuple.pair
        |= prems cfg
        |. spaces
        |= formula cfg



-- obtains set of variables in a term


termVars : Term -> Set String
termVars t =
    case t of
        Var v ->
            singleton v

        Func _ ts ->
            termListVars ts



-- obtains set of variables in list of terms


termListVars : List Term -> Set String
termListVars ts =
    List.foldl
        (\x state ->
            Set.union (termVars x) state
        )
        Set.empty
        ts



-- helper to obtain free & bound variables
-- note however, that a variable may appear as both bound & free within a formula (e.g., Q(x) ∧ ∃x P(x))


frmVars : Formula -> ( Set String, Set String )
frmVars f =
    let
        recur =
            \x ->
                frmVars x

        recur2 =
            \x y ->
                let
                    ( free1, bound1 ) =
                        frmVars x

                    ( free2, bound2 ) =
                        frmVars y
                in
                ( Set.union free1 free2, Set.union bound1 bound2 )

        recurQ =
            \v y ->
                let
                    ( free, bound ) =
                        frmVars y
                in
                ( Set.remove v free, Set.insert v bound )
    in
    case f of
        Neg x ->
            recur x

        Conj x y ->
            recur2 x y

        Disj x y ->
            recur2 x y

        Impl x y ->
            recur2 x y

        Iff x y ->
            recur2 x y

        Predicate _ ts ->
            ( termListVars ts, Set.empty )

        Equals ( t1, t2 ) ->
            ( Set.union (termVars t1) (termVars t2), Set.empty )

        ForAll v frm ->
            recurQ v frm

        Exists v frm ->
            recurQ v frm

        _ ->
            ( Set.empty, Set.empty )



-- obtains set of variables in formula


vars : Formula -> Set String
vars f =
    f
        |> frmVars
        |> (\( s1, s2 ) -> Set.union s1 s2)



-- obtains set of free variables in a formula


freeVars : Formula -> Set String
freeVars f =
    f
        |> frmVars
        |> Tuple.first



-- obtains set of bound variables in a formula


boundVars : Formula -> Set String
boundVars f =
    f
        |> frmVars
        |> Tuple.second



-- replaces all occurrences of 'x' with 't1' in 't2'


replaceAllOccurrencesInTerm : TermSubst -> Term -> Term
replaceAllOccurrencesInTerm subst t2 =
    let
        ( x, t1 ) =
            subst
    in
    case t2 of
        Var s ->
            if x == Var s then
                t1

            else
                Var s

        Func s xs ->
            Func s (List.map (replaceAllOccurrencesInTerm subst) xs)



-- replaces all free occurrences of 'x' with 't' in 'frm'
-- returns tuple (frm[t/x], true if vars in t got captured | false otherwise)


replaceAllFreeOccurrences : TermSubst -> Formula -> ( Formula, Bool )
replaceAllFreeOccurrences =
    replaceAllFreeOccurrencesHelper []



-- replaces all free occurrences of 'x' with 't' in 'frm'
-- returns tuple (frm[t/x], true if vars in t got captured | false otherwise)


replaceAllFreeOccurrencesHelper : List String -> TermSubst -> Formula -> ( Formula, Bool )
replaceAllFreeOccurrencesHelper bound subst frm =
    let
        ( x, t ) =
            subst

        recur1h =
            \newbound phi ->
                replaceAllFreeOccurrencesHelper newbound subst phi

        recur1 =
            recur1h bound

        recur2 =
            \ctor phi psi ->
                let
                    ( frm1, b1 ) =
                        recur1 phi

                    ( frm2, b2 ) =
                        recur1 psi
                in
                ( ctor frm1 frm2, b1 || b2 )

        recurB =
            \ctor y phi ->
                -- not free occurrence
                if x == Var y then
                    ( ctor y phi, False )

                else
                    let
                        newbound =
                            y :: bound

                        b1 =
                            Set.foldl (\e state -> state || List.member e newbound) False (termVars t)

                        ( psi, b2 ) =
                            recur1h newbound phi
                    in
                    ( psi, b1 || b2 )
    in
    case frm of
        Neg a ->
            recur1 a

        Conj a b ->
            recur2 Conj a b

        Disj a b ->
            recur2 Disj a b

        Impl a b ->
            recur2 Impl a b

        Iff a b ->
            recur2 Iff a b

        Predicate p ts ->
            ( Predicate p (List.map (replaceAllOccurrencesInTerm subst) ts), False )

        Equals ( t1, t2 ) ->
            ( Equals ( replaceAllOccurrencesInTerm subst t1, replaceAllOccurrencesInTerm subst t2 ), False )

        ForAll y phi ->
            recurB ForAll y phi

        Exists y phi ->
            recurB Exists y phi

        f ->
            ( f, False )



-- replaces all occurrences of 'x' with 't' in 'frm' (blindly!)
-- even bound occurrences will get replaced and we do not care!


replaceAllOccurrencesBlindly : TermSubst -> Formula -> Formula
replaceAllOccurrencesBlindly subst frm =
    let
        ( x, t ) =
            subst

        recur =
            \phi ->
                replaceAllOccurrencesBlindly subst phi

        updateTerm =
            replaceAllOccurrencesInTerm subst

        updateBound =
            \z ->
                case updateTerm z of
                    Var k ->
                        k

                    _ ->
                        "error@replaceAllOccurrencesBlindly"
    in
    case frm of
        Neg a ->
            Neg (recur a)

        Conj a b ->
            Conj (recur a) (recur b)

        Disj a b ->
            Disj (recur a) (recur b)

        Impl a b ->
            Impl (recur a) (recur b)

        Iff a b ->
            Iff (recur a) (recur b)

        Predicate p ts ->
            Predicate p (List.map updateTerm ts)

        Equals ( t1, t2 ) ->
            Equals ( updateTerm t1, updateTerm t2 )

        ForAll y phi ->
            ForAll (updateBound (Var y)) (recur phi)

        Exists y phi ->
            Exists (updateBound (Var y)) (recur phi)

        f ->
            f



-- apply tsubst to variable list


updateVars : TermSubst -> Set String -> Set String
updateVars tsubst vs =
    let
        ( t1, t2 ) =
            tsubst
    in
    case t1 of
        Var s1 ->
            case t2 of
                Var s2 ->
                    vs
                        |> Set.map
                            (\v ->
                                if v == s1 then
                                    s2

                                else
                                    v
                            )

                _ ->
                    -- var would get replaced by term
                    vs

        _ ->
            -- lhs of subst is not a var
            vs



-- apply tsubsts to variable list


updateVarsWithList : List TermSubst -> Set String -> Set String
updateVarsWithList tsubsts vs =
    tsubsts
        |> List.foldl updateVars vs



-- apply tsubsts to single var


updateVarWithList : List TermSubst -> String -> String
updateVarWithList tsubsts v =
    Set.singleton v
        |> updateVarsWithList tsubsts
        |> Set.toList
        |> (\x ->
                case List.head x of
                    Just y ->
                        y

                    Nothing ->
                        v
           )



-- apply tsubst1 on tsubst2


updateTermSubst : TermSubst -> TermSubst -> TermSubst
updateTermSubst tsubst1 tsubst2 =
    let
        ( t21, t22 ) =
            tsubst2
    in
    ( replaceAllOccurrencesInTerm tsubst1 t21, replaceAllOccurrencesInTerm tsubst1 t22 )



-- apply tsubst1 on list tsubsts


updateTermSubsts : TermSubst -> List TermSubst -> List TermSubst
updateTermSubsts tsubst1 tsubsts =
    List.map (updateTermSubst tsubst1) tsubsts



-- apply list tsubsts on tsubst2


updateTermSubstWithList : List TermSubst -> TermSubst -> TermSubst
updateTermSubstWithList tsubsts tsubst2 =
    tsubsts
        |> List.foldl updateTermSubst tsubst2



-- apply list tsubsts1 on list tsubsts2


updateTermSubstsWithList : List TermSubst -> List TermSubst -> List TermSubst
updateTermSubstsWithList tsubsts1 tsubsts2 =
    List.map (updateTermSubstWithList tsubsts1) tsubsts2



-- obtain outermost bound var in frm


outermostBoundVar : Formula -> Maybe String
outermostBoundVar frm =
    case frm of
        Exists v _ ->
            Just v

        ForAll v _ ->
            Just v

        _ ->
            Nothing



-- obtain outermost abstract bound var in frm


outermostAbstractBoundVar : Formula -> Maybe String
outermostAbstractBoundVar frm =
    let
        check =
            \m ->
                case m of
                    Just s ->
                        if abstract s then
                            Just s

                        else
                            Nothing

                    Nothing ->
                        Nothing
    in
    frm
        |> outermostBoundVar
        |> check



-- split set of vars in (abstract vars, specific vars)


splitAbstractVars : Set String -> ( Set String, Set String )
splitAbstractVars =
    Set.partition abstract


splitAbstractTermSubsts : List TermSubst -> ( List TermSubst, List TermSubst )
splitAbstractTermSubsts =
    List.partition
        (\( x, _ ) ->
            case x of
                Var s ->
                    abstract s

                _ ->
                    False
        )



-- given (x,y) and (y,z) yields (x,z)


transTermSubst : TermSubst -> TermSubst -> TermSubst
transTermSubst tsubst1 tsubst2 =
    let
        ( x1, y1 ) =
            tsubst1

        ( x2, y2 ) =
            tsubst2
    in
    if y1 == x2 then
        ( x1, y2 )

    else
        tsubst1


transTermSubsts : List TermSubst -> TermSubst -> TermSubst
transTermSubsts tsubsts tsubst2 =
    tsubsts
        |> List.foldl (\x state -> transTermSubst state x) tsubst2



-- obtain clashes in subst


clash : List ( a, a ) -> List ( a, a )
clash substs =
    Utils.rightDiff substs



-- checks if subst list is free of clashes, i.e., no lhs element is mapped to two different rhs elements
-- assumes list to already be free of duplicates, e.g., [(Var x, Var y), (Var x, Var y)]


clashFree : List ( a, a ) -> Bool
clashFree xs =
    xs
        |> List.map Tuple.first
        |> Utils.unique


type Operator
    = OpTop
    | OpBot
    | OpId
    | OpNeg
    | OpForAll String
    | OpExists String
    | OpConj
    | OpDisj
    | OpImpl
    | OpIff -- "⟷"
    | OpEq -- "="


displayOperator : Operator -> String
displayOperator op =
    case op of
        OpTop ->
            "⊤"

        OpBot ->
            "⊥"

        OpId ->
            "id"

        OpNeg ->
            "¬"

        OpExists x ->
            if abstract x then
                "∃?v" ++ x

            else
                "∃" ++ x

        OpForAll x ->
            if abstract x then
                "∀?v" ++ x

            else
                "∀" ++ x

        OpConj ->
            "∧"

        OpDisj ->
            "∨"

        OpImpl ->
            "⟶"

        OpIff ->
            "⟷"

        OpEq ->
            "="



-- deconstructs a frm into a tuple (op, args)


deconstructFormula : Formula -> ( Operator, List Formula )
deconstructFormula frm =
    case frm of
        Top ->
            ( OpTop, [] )

        Bot ->
            ( OpBot, [] )

        Neg a ->
            ( OpNeg, [ a ] )

        Conj a b ->
            ( OpConj, [ a, b ] )

        Disj a b ->
            ( OpDisj, [ a, b ] )

        Impl a b ->
            ( OpImpl, [ a, b ] )

        Iff a b ->
            ( OpIff, [ a, b ] )

        Exists x a ->
            ( OpExists x, [ a ] )

        ForAll x a ->
            ( OpForAll x, [ a ] )

        Equals pair ->
            ( OpEq, [ Equals pair ] )

        PredConst s ->
            ( OpId, [ PredConst s ] )

        Predicate s ts ->
            ( OpId, [ Predicate s ts ] )


reconstructFormula : Operator -> List Formula -> Maybe Formula
reconstructFormula op fs =
    let
        binary =
            \bin ->
                case fs of
                    f1 :: f2 :: [] ->
                        bin f1 f2
                            |> Just

                    _ ->
                        Nothing
    in
    case op of
        OpTop ->
            Just Top

        OpBot ->
            Just Bot

        OpNeg ->
            fs
                |> List.head
                |> Maybe.map (\f -> Neg f)

        OpConj ->
            binary Conj

        OpDisj ->
            binary Disj

        OpImpl ->
            binary Impl

        OpIff ->
            binary Iff

        OpExists x ->
            fs
                |> List.head
                |> Maybe.map (\f -> Exists x f)

        OpForAll x ->
            fs
                |> List.head
                |> Maybe.map (\f -> ForAll x f)

        _ ->
            fs
                |> List.head



-- replaces sub formula, using given substitution


replaceSubFormula : FrmSubst -> Formula -> Formula
replaceSubFormula subst frm =
    let
        ( subfrm, replacement ) =
            subst

        recur =
            \f -> replaceSubFormula subst f
    in
    if frm == subfrm then
        replacement

    else
        case frm of
            Top ->
                frm

            Bot ->
                frm

            Neg a ->
                Neg (recur a)

            Conj a b ->
                Conj (recur a) (recur b)

            Disj a b ->
                Disj (recur a) (recur b)

            Impl a b ->
                Impl (recur a) (recur b)

            Iff a b ->
                Iff (recur a) (recur b)

            PredConst s ->
                frm

            Predicate s ts ->
                frm

            Equals ( t1, t2 ) ->
                frm

            -- careful: the replacement may contain variables that get captured here!
            Exists x a ->
                Exists x (recur a)

            ForAll x a ->
                ForAll x (recur a)



-- string is representation for abstract variable / placeholder (integer)


abstract : String -> Bool
abstract s =
    case String.toInt s of
        Just _ ->
            True

        Nothing ->
            False


type AbstractType
    = TypeA String
    | TypeB String
    | TypeNone


abstractWithType : String -> AbstractType
abstractWithType s =
    case String.toInt s of
        Just i ->
            if i >= 0 then
                TypeA s

            else
                i
                    |> abs
                    |> String.fromInt
                    |> TypeB

        Nothing ->
            TypeNone


abstractTerm : Term -> Bool
abstractTerm t =
    case t of
        Var s ->
            abstract s

        _ ->
            False



-- checks if given formula is purely abstract (consists only of placeholders and connectives)


abstractFormula : Formula -> Bool
abstractFormula frm =
    let
        recur1 =
            \a ->
                abstractFormula a

        recur2 =
            \a b ->
                abstractFormula a && abstractFormula b
    in
    case frm of
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

        ForAll x a ->
            abstract x && recur1 a

        Exists x a ->
            abstract x && recur1 a

        Equals ( t1, t2 ) ->
            abstractTerm t1 && abstractTerm t2

        PredConst s ->
            abstract s

        Predicate s ts ->
            ts
                |> List.foldl (\t state -> state && abstractTerm t) True
                |> (\r -> r && abstract s)

        _ ->
            False



-- checks if given formula is fully instantiated (does not contain any placeholders)


specificFormula : Formula -> Bool
specificFormula frm =
    let
        recur1 =
            \a ->
                specificFormula a

        recur2 =
            \a b ->
                specificFormula a && specificFormula b

        nabstract =
            \x ->
                not (abstract x)

        nabstractterm =
            \x ->
                not (abstractTerm x)
    in
    case frm of
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

        ForAll x a ->
            nabstract x && recur1 a

        Exists x a ->
            nabstract x && recur1 a

        Equals ( t1, t2 ) ->
            nabstractterm t1 && nabstractterm t2

        PredConst s ->
            nabstract s

        Predicate s ts ->
            ts
                |> List.foldl (\t state -> state && nabstractterm t) True
                |> (\r -> r && nabstract s)

        _ ->
            False


displayTerm : Term -> String
displayTerm t =
    case t of
        Var s ->
            case abstractWithType s of
                TypeA s1 ->
                    "?v" ++ s1

                TypeB s1 ->
                    "?t" ++ s1

                TypeNone ->
                    s

        Func s ts ->
            s ++ "(" ++ displayTermList ts ++ ")"


displayTermList : List Term -> String
displayTermList ts =
    ts
        |> List.map displayTerm
        |> String.join ","


displayTermSubst : TermSubst -> String
displayTermSubst subst =
    let
        ( lhs, rhs ) =
            subst
    in
    displayTerm lhs ++ " ↦ " ++ displayTerm rhs


displayTermSubsts : List TermSubst -> String
displayTermSubsts tsubsts =
    List.map displayTermSubst tsubsts
        |> String.join ", "


displayTermSubstFree : TermSubst -> String
displayTermSubstFree subst =
    let
        ( lhs, rhs ) =
            subst
    in
    "[" ++ displayTerm rhs ++ "/" ++ displayTerm lhs ++ "]"


displayTermSubstsFree : List TermSubst -> String
displayTermSubstsFree tsubsts =
    List.map displayTermSubstFree tsubsts
        |> String.join ","


displayFrmSubst : Bool -> FrmSubst -> String
displayFrmSubst q subst =
    let
        ( lhs, rhs ) =
            subst
    in
    "[" ++ displayFormula q rhs ++ "/" ++ displayFormula q lhs ++ "]"


displayFrmSubsts : Bool -> List FrmSubst -> String
displayFrmSubsts q fsubsts =
    List.map (displayFrmSubst q) fsubsts
        |> String.join ","



-- given formulas a b, yields "acb" with connective c, optionally put into parentheses


displayBinaryConnective : Bool -> Bool -> Formula -> Formula -> String -> String
displayBinaryConnective p q a b c =
    let
        l =
            displayFormulaHelper q a

        r =
            displayFormulaHelper q b

        s =
            l ++ c ++ r
    in
    if p then
        "(" ++ s ++ ")"

    else
        s


displayQuantifier : Bool -> Bool -> String -> String -> Formula -> String
displayQuantifier p q s x f =
    let
        sx =
            if abstract x then
                "?v" ++ x

            else
                x

        res =
            if q then
                s ++ sx ++ " " ++ displayFormulaHelper q f

            else
                s ++ sx ++ ". " ++ displayFormula q f
    in
    if p then
        "(" ++ res ++ ")"

    else
        res


displayFormulaHelper : Bool -> Formula -> String
displayFormulaHelper q f =
    case f of
        Top ->
            "⊤"

        Bot ->
            "⊥"

        PredConst s ->
            if abstract s then
                "?ϕ" ++ s

            else
                s

        Predicate s ts ->
            s ++ "(" ++ displayTermList ts ++ ")"

        Neg a ->
            "¬" ++ displayFormulaHelper q a

        Conj a b ->
            displayBinaryConnective True q a b " ∧ "

        Disj a b ->
            displayBinaryConnective True q a b " ∨ "

        Impl a b ->
            displayBinaryConnective True q a b " ⟶ "

        Iff a b ->
            displayBinaryConnective True q a b " ⟷ "

        Equals ( t1, t2 ) ->
            "(" ++ displayTerm t1 ++ " ＝ " ++ displayTerm t2 ++ ")"

        Exists x a ->
            displayQuantifier True q "∃" x a

        ForAll x a ->
            displayQuantifier True q "∀" x a



-- omit outermost parentheses


displayFormula : Bool -> Formula -> String
displayFormula q f =
    case f of
        Conj a b ->
            displayBinaryConnective False q a b " ∧ "

        Disj a b ->
            displayBinaryConnective False q a b " ∨ "

        Impl a b ->
            displayBinaryConnective False q a b " ⟶ "

        Iff a b ->
            displayBinaryConnective False q a b " ⟷ "

        Equals ( t1, t2 ) ->
            displayTerm t1 ++ " ＝ " ++ displayTerm t2

        Exists x a ->
            displayQuantifier False q "∃" x a

        ForAll x a ->
            displayQuantifier False q "∀" x a

        _ ->
            displayFormulaHelper q f


displayFormulas : Bool -> List Formula -> String
displayFormulas b fs =
    fs
        |> List.map (displayFormula b)
        |> String.join ", "


displaySeq : Bool -> Seq -> String
displaySeq q seq =
    let
        ( ps, c ) =
            seq

        ds =
            List.map (displayFormula q) ps

        l =
            String.join ", " ds

        r =
            displayFormula q c
    in
    l ++ " ⊢ " ++ r
