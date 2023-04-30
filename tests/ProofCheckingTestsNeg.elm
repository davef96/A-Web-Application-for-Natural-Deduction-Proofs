module ProofCheckingTestsNeg exposing (suite)

import Expect exposing (Expectation)
import Fuzz exposing (Fuzzer, int, list, string)
import ModelDefs exposing (..)
import ProofChecking exposing (..)
import Test exposing (..)


cfgFOL : ParserConfig
cfgFOL =
    { fol = True
    , qtype = True
    , kword = True
    , conjstronger = False
    }


cfgProp : ParserConfig
cfgProp =
    { fol = False
    , qtype = True
    , kword = True
    , conjstronger = False
    }



--buildAndQuickCheck : RuleSubset -> ParserConfig -> ModelDefs.GoalType -> List ModelDefs.LineType -> Bool


propCheck : GoalType -> List LineType -> Bool
propCheck =
    buildAndQuickCheck True Prop cfgProp


folCheck : GoalType -> List LineType -> Bool
folCheck =
    buildAndQuickCheck True FOL cfgFOL


suite : Test
suite =
    describe "Full Proof Tests (Parsing + Building + Checking) [INvalid Proofs]"
        [ describe "Propositional Logic"
            [ test "Proof by Assumption" <|
                \_ ->
                    let
                        goal =
                            " ⊢ a"

                        proof =
                            [ ( 0, ( "a", "assumption" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Proof by Renaming" <|
                \_ ->
                    let
                        goal =
                            "b ⊢ a"

                        proof =
                            [ ( 0, ( "a", "premise" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Proof by Assumption (indirect)" <|
                \_ ->
                    let
                        goal =
                            "a ⊢ ⊥"

                        proof =
                            [ ( 0, ( "a", "premise" ) )
                            , ( 0, ( "¬a", "assumption" ) )
                            , ( 0, ( "⊥", "¬e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Conclusion inside Box" <|
                \_ ->
                    let
                        goal =
                            "a ⊢ a"

                        proof =
                            [ ( 1, ( "a", "premise" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Proof by Assumption (inside box)" <|
                \_ ->
                    let
                        goal =
                            " ⊢ a"

                        proof =
                            [ ( 1, ( "a", "assumption" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Conjunction Introduction (missing fact)" <|
                \_ ->
                    let
                        goal =
                            "a ⊢ a ∧ b"

                        proof =
                            [ ( 0, ( "a", "premise" ) )
                            , ( 0, ( "a ∧ b", "∧i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Conjunction Elimination (wrong conclusion)" <|
                \_ ->
                    let
                        goal =
                            "p ∧ q ⊢ r"

                        proof =
                            [ ( 0, ( "p ∧ q", "premise" ) )
                            , ( 0, ( "r", "∧e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Double Negation Introduction (missing fact)" <|
                \_ ->
                    let
                        goal =
                            "⊢ ¬¬p"

                        proof =
                            [ ( 0, ( "¬¬p", "¬¬i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Implication Elimination (typo in premise)" <|
                \_ ->
                    let
                        -- 't' should be 'r'
                        goal =
                            "q, p ⟶ q, p ⟶ (q ⟶ t) ⊢ r"

                        proof =
                            [ ( 0, ( "p", "premise" ) )
                            , ( 0, ( "p ⟶ q", "premise" ) )
                            , ( 0, ( "p ⟶ (q ⟶ r)", "premise" ) )
                            , ( 0, ( "q", "⟶e" ) )
                            , ( 0, ( "q ⟶ r", "⟶e" ) )
                            , ( 0, ( "r", "⟶e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Modus Tollens + Double Negation Elimination (missing negation)" <|
                \_ ->
                    let
                        -- non-negated atom q in premise!
                        goal =
                            "¬p ⟶ q, q ⊢ p"

                        proof =
                            [ ( 0, ( "¬p ⟶ q", "premise" ) )
                            , ( 0, ( "q", "premise" ) )
                            , ( 0, ( "¬¬p", "MT" ) )
                            , ( 0, ( "p", "¬¬e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Implication Introduction (box missing)" <|
                \_ ->
                    let
                        goal =
                            "q ⊢ p ⟶ q"

                        proof =
                            [ ( 0, ( "q", "assumption" ) )
                            , ( 0, ( "p", "assumption" ) )
                            , ( 0, ( "p ⟶ q", "⟶i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Implication Introduction + Modus Tollens + Double Negation Introduction/Elimination (box missing)" <|
                \_ ->
                    let
                        goal =
                            "¬q ⟶ ¬p ⊢ p ⟶ q"

                        proof =
                            [ ( 0, ( "¬q ⟶ ¬p", "premise" ) )
                            , ( 0, ( "p", "assumption" ) )
                            , ( 0, ( "¬¬p", "¬¬i" ) )
                            , ( 0, ( "¬¬q", "MT" ) )
                            , ( 0, ( "q", "¬¬e" ) )
                            , ( 0, ( "p ⟶ q", "⟶i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Disjunction Introduction (missing fact)" <|
                \_ ->
                    let
                        goal =
                            " ⊢ q ∨ p"

                        proof =
                            [ ( 0, ( "q ∨ p", "∨i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Disjunction Introduction/Elimination (order wrong)" <|
                \_ ->
                    let
                        goal =
                            "p ∨ q ⊢ q ∨ p"

                        proof =
                            [ ( 0, ( "p ∨ q", "premise" ) )
                            , ( 1, ( "p", "assumption" ) )
                            , ( 1, ( "p ∨ q", "∨i" ) ) -- order wrong
                            , ( 1, ( "q", "assumption" ) )
                            , ( 1, ( "q ∨ p", "∨i" ) )
                            , ( 0, ( "q ∨ p", "∨e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Implication Elimination + Negation Introduction/Elimination (missing box)" <|
                \_ ->
                    let
                        goal =
                            "p ⟶ q, p ⟶ ¬q ⊢ ¬p"

                        proof =
                            [ ( 0, ( "p ⟶ q", "premise" ) )
                            , ( 0, ( "p ⟶ ¬q", "premise" ) )
                            , ( 0, ( "p", "assumption" ) )
                            , ( 0, ( "q", "⟶e" ) )
                            , ( 0, ( "¬q", "⟶e" ) )
                            , ( 0, ( "⊥", "¬e" ) )
                            , ( 0, ( "¬p", "¬i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Implication Elimination + Negation Introduction/Elimination (box without assm)" <|
                \_ ->
                    let
                        goal =
                            "p ⟶ q, p ⟶ ¬q ⊢ ¬p"

                        proof =
                            [ ( 0, ( "p ⟶ q", "premise" ) )
                            , ( 0, ( "p ⟶ ¬q", "premise" ) )
                            , ( 1, ( "q", "⟶e" ) )
                            , ( 1, ( "¬q", "⟶e" ) )
                            , ( 1, ( "⊥", "¬e" ) )
                            , ( 0, ( "¬p", "¬i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Bot by Top Introduction" <|
                \_ ->
                    let
                        goal =
                            "⊢ ⊥"

                        proof =
                            [ ( 0, ( "⊥", "⊤i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Proof by Top Introduction" <|
                \_ ->
                    let
                        goal =
                            "⊢ p"

                        proof =
                            [ ( 0, ( "p", "⊤i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Negation elimination (missing fact)" <|
                \_ ->
                    let
                        goal =
                            "p ⊢ ⊥"

                        proof =
                            [ ( 0, ( "p", "premise" ) )
                            , ( 0, ( "⊥", "¬e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Negation elimination (missing fact -- 2)" <|
                \_ ->
                    let
                        goal =
                            "¬p ⊢ ⊥"

                        proof =
                            [ ( 0, ( "¬p", "premise" ) )
                            , ( 0, ( "⊥", "¬e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "Negation elimination (different atoms)" <|
                \_ ->
                    let
                        goal =
                            "¬p, q ⊢ ⊥"

                        proof =
                            [ ( 0, ( "¬p", "premise" ) )
                            , ( 0, ( "q", "premise" ) )
                            , ( 0, ( "⊥", "¬e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "LEM (no negation)" <|
                \_ ->
                    let
                        goal =
                            "⊢ p ∨ p"

                        proof =
                            [ ( 0, ( "p ∨ p", "LEM" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "LEM (wrong order)" <|
                \_ ->
                    let
                        goal =
                            "⊢ ¬p ∨ p"

                        proof =
                            [ ( 0, ( "¬p ∨ p", "LEM" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "LEM (different atoms)" <|
                \_ ->
                    let
                        goal =
                            "⊢ q ∨ ¬p"

                        proof =
                            [ ( 0, ( "q ∨ ¬p", "LEM" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            , test "LEM + Disjunction Introduction/Elimination + Implication Elimination (not in box)" <|
                \_ ->
                    let
                        goal =
                            "p ⟶ q ⊢ ¬p ∨ q"

                        proof =
                            [ ( 0, ( "p ⟶ q", "premise" ) )
                            , ( 0, ( "p ∨ ¬p", "LEM" ) )
                            , ( 1, ( "p", "assumption" ) )
                            , ( 1, ( "q", "⟶e" ) )
                            , ( 1, ( "¬p ∨ q", "∨i" ) )
                            , ( 0, ( "¬p", "assumption" ) )
                            , ( 0, ( "¬p ∨ q", "∨i" ) )
                            , ( 0, ( "¬p ∨ q", "∨e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result False
            ]
        , describe "Propositional Logic with Predicates"
            [ test "Proof by Assumption" <|
                \_ ->
                    let
                        goal =
                            " ⊢ P(a)"

                        proof =
                            [ ( 0, ( "P(a)", "assumption" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Proof by Renaming" <|
                \_ ->
                    let
                        goal =
                            "P(a) ⊢ P(b)"

                        proof =
                            [ ( 0, ( "P(b)", "premise" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Conclusion inside Box" <|
                \_ ->
                    let
                        goal =
                            "P(a) ⊢ P(a)"

                        proof =
                            [ ( 1, ( "P(a)", "premise" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Proof by Assumption (inside box)" <|
                \_ ->
                    let
                        goal =
                            " ⊢ P(a)"

                        proof =
                            [ ( 1, ( "P(a)", "assumption" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Conjunction Introduction (missing fact/renaming)" <|
                \_ ->
                    let
                        goal =
                            "P(a) ⊢ P(a) ∧ P(b)"

                        proof =
                            [ ( 0, ( "P(a)", "premise" ) )
                            , ( 0, ( "P(a) ∧ P(b)", "∧i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Conjunction Introduction (renaming)" <|
                \_ ->
                    let
                        goal =
                            "P(a), P(c) ⊢ P(a) ∧ P(b)"

                        proof =
                            [ ( 0, ( "P(a)", "premise" ) )
                            , ( 0, ( "P(c)", "premise" ) )
                            , ( 0, ( "P(a) ∧ P(b)", "∧i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Conjunction Introduction (missing fact/renaming -- 2)" <|
                \_ ->
                    let
                        goal =
                            "P(a,b,c) ⊢ P(a,b,c) ∧ P(b,a,c)"

                        proof =
                            [ ( 0, ( "P(a,b,c)", "premise" ) )
                            , ( 0, ( "P(a,b,c) ∧ P(b,a,c)", "∧i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Conjunction Introduction (renaming -- 2)" <|
                \_ ->
                    let
                        goal =
                            "P(a,a), P(b,a) ⊢ P(a,a) ∧ P(b,b)"

                        proof =
                            [ ( 0, ( "P(a,a)", "premise" ) )
                            , ( 0, ( "P(b,a)", "premise" ) )
                            , ( 0, ( "P(a,a) ∧ P(b,b)", "∧i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            ]
        , describe "Predicate Logic"
            [ test "Universal Introduction (by assumption)" <|
                \_ ->
                    let
                        goal =
                            "⊢ ∀x P(x)"

                        proof =
                            [ ( 1, ( "[x0] P(x0)", "assumption" ) )
                            , ( 0, ( "∀x(P(x))", "∀i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Introduction (by assumption -- 2)" <|
                \_ ->
                    let
                        goal =
                            "⊢ ∀x P(x)"

                        proof =
                            [ ( 1, ( "[x0]", "" ) )
                            , ( 1, ( "P(x0)", "assumption" ) )
                            , ( 0, ( "∀x(P(x))", "∀i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Introduction/Elimination (capturing)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃x0 P(x,x0) ⊢ ∀z ∃x0 P(x0,x0)"

                        proof =
                            [ ( 0, ( "∀x (∃x0 P(x,x0))", "premise" ) )
                            , ( 1, ( "[x0]", "" ) )
                            , ( 1, ( "∃x0 P(x0,x0)", "∀e" ) )
                            , ( 0, ( "∀z (∃x0 P(x0,x0))", "∀i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Introduction/Elimination (capturing -- 2)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃x0 P(x,x0) ⊢ ∀z ∃x0 P(f(g(x0)),z)"

                        proof =
                            [ ( 0, ( "∀x (∃x0 P(x,x0))", "premise" ) )
                            , ( 1, ( "[x0]", "" ) )
                            , ( 1, ( "∃x0 P(f(g(x0)),x0)", "∀e" ) )
                            , ( 0, ( "∀z ∃x0 P(f(g(x0)),z)", "∀i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (different predicates: arity)" <|
                \_ ->
                    let
                        goal =
                            "∀x P ⊢ P(a)"

                        proof =
                            [ ( 0, ( "∀x(P)", "premise" ) )
                            , ( 0, ( "P(a)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (different predicates: arity -- 2)" <|
                \_ ->
                    let
                        goal =
                            "∀x P(x) ⊢ P(a,a)"

                        proof =
                            [ ( 0, ( "∀x(P(x))", "premise" ) )
                            , ( 0, ( "P(a,a)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (eliminating free var)" <|
                \_ ->
                    let
                        goal =
                            "∀x P(x,y) ⊢ P(x,x)"

                        proof =
                            [ ( 0, ( "∀x(P(x,y))", "premise" ) )
                            , ( 0, ( "P(x,x)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (eliminating free var -- 2)" <|
                \_ ->
                    let
                        goal =
                            "∀x (Q(x,y) ∧ (∃y ∃x P(x,y,z))) ⊢ (Q(f(x,y,z),x) ∧ (∃y ∃x P(x,y,z)))"

                        proof =
                            [ ( 0, ( "∀x (Q(x,y) ∧ (∃y (∃x P(x,y,z))))", "premise" ) )
                            , ( 0, ( "Q(f(x,y,z),x) ∧ (∃y (∃x P(x,y,z)))", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (eliminating free var/swap)" <|
                \_ ->
                    let
                        goal =
                            "∀x P(x,y) ⊢ P(y,x)"

                        proof =
                            [ ( 0, ( "∀x(P(x,y))", "premise" ) )
                            , ( 0, ( "P(y,x)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (clashing elimination)" <|
                \_ ->
                    let
                        goal =
                            "∀x P(x,y,x) ⊢ P(a,y,y)"

                        proof =
                            [ ( 0, ( "∀x(P(x,y,x))", "premise" ) )
                            , ( 0, ( "P(a,y,y)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (clashing elimination 2)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃y P(x,y,x) ⊢ ∃y P(a,y,b)"

                        proof =
                            [ ( 0, ( "∀x (∃y P(x,y,x))", "premise" ) )
                            , ( 0, ( "∃y P(a,y,b)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (clashing elimination 3)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃y P(x,y,x) ⊢ ∃y P(x,y,b)"

                        proof =
                            [ ( 0, ( "∀x (∃y P(x,y,x))", "premise" ) )
                            , ( 0, ( "∃y P(x,y,b)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (clashing elimination 4)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃y ∃x P(x,y,x) ⊢ ∃y ∃x P(z,y,x)"

                        proof =
                            [ ( 0, ( "∀x (∃y (∃x P(x,y,x)))", "premise" ) )
                            , ( 0, ( "∃y (∃x P(z,y,x))", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (clashing elimination 5)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃y ∀z (P(x,f(b)) ⟶ Q(h(f(b),a,b,f(b)),y) ⟶ R(y,x)) ⊢ ∃y ∀z (P(f(a,b,c),f(b)) ⟶ Q(h(f(b),a,b,f(b)),y) ⟶ R(y,f(b)))"

                        proof =
                            [ ( 0, ( "∀x (∃y (∀z (P(x,f(b)) ⟶ (Q(h(f(b),a,b,f(b)),y) ⟶ R(y,x)))))", "premise" ) )
                            , ( 0, ( "∃y (∀z (P(f(a,b,c),f(b)) ⟶ (Q(h(f(b),a,b,f(b)),y) ⟶ R(y,f(b)))))", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (capturing)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃y P(x,y) ⊢ ∃y P(y,y)"

                        proof =
                            [ ( 0, ( "∀x ∃y P(x,y)", "premise" ) )
                            , ( 0, ( "∃y P(y,y)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (capturing 2)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃y P(x,y) ⊢ ∃y P(f(g(h(x,x,f(y)))),y)"

                        proof =
                            [ ( 0, ( "∀x (∃y P(x,y))", "premise" ) )
                            , ( 0, ( "∃y P(f(g(h(x,x,f(y)))),y)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (capturing 3)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃y P(x,y,x) ⊢ ∃y P(y,y,k)"

                        proof =
                            [ ( 0, ( "∀x (∃y P(x,y,x))", "premise" ) )
                            , ( 0, ( "∃y P(y,y,k)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (capturing 5)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃y P(x,y,x) ⊢ ∃y P(y,y,y)"

                        proof =
                            [ ( 0, ( "∀x (∃y P(x,y,x))", "premise" ) )
                            , ( 0, ( "∃y P(y,y,y)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (capturing 6)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃y P(f(x,y),y,g(h(x,x,y))) ⊢ ∃y P(f(f(y),y),y,g(h(f(y),f(y),y)))"

                        proof =
                            [ ( 0, ( "∀x (∃y P(f(x,y),y,g(h(x,x,y))))", "premise" ) )
                            , ( 0, ( "∃y P(f(f(y),y),y,g(h(f(y),f(y),y)))", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (renaming of bound var)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∀y P(x,y,x) ⊢ ∀k P(a,k,a)"

                        proof =
                            [ ( 0, ( "∀x ∀y (P(x,y,x))", "premise" ) )
                            , ( 0, ( "∀k P(a,k,a)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (renaming of bound var -- 2)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃y P(x,y,x) ⊢ ∃k P(a,k,a)"

                        proof =
                            [ ( 0, ( "∀x ∃y (P(x,y,x))", "premise" ) )
                            , ( 0, ( "∃k P(a,k,a)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (eliminating bound var)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∀y P(x,y,x) ⊢ ∀y P(x,x,x)"

                        proof =
                            [ ( 0, ( "∀x ∀y (P(x,y,x))", "premise" ) )
                            , ( 0, ( "∀y P(x,x,x)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (eliminating bound var -- 2)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃y P(x,y,x) ⊢ ∃y P(a,a,a)"

                        proof =
                            [ ( 0, ( "∀x ∃y (P(x,y,x))", "premise" ) )
                            , ( 0, ( "∃y P(a,a,a)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (eliminating bound var -- 3)" <|
                \_ ->
                    let
                        goal =
                            "∀x. ∃x. ∃y. ∀x. P(x) ⊢ ∃x. ∃y. ∀x. P(f(k))"

                        proof =
                            [ ( 0, ( "∀x. ∃x. ∃y. ∀x. P(x)", "premise" ) )
                            , ( 0, ( "∃x. ∃y. ∀x. P(f(k))", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (eliminating bound var -- 4)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃x P(x) ⊢ ∃x P(k)"

                        proof =
                            [ ( 0, ( "∀x (∃x P(x))", "premise" ) )
                            , ( 0, ( "∃x P(k)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (eliminating bound var -- 5)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃x P(x,x,y) ⊢ ∃x P(k,x,y)"

                        proof =
                            [ ( 0, ( "∀x (∃x P(x,x,y))", "premise" ) )
                            , ( 0, ( "∃x P(k,x,y)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (eliminating bound var -- 6)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃x P(x,x,y) ⊢ ∃x P(k,k,y)"

                        proof =
                            [ ( 0, ( "∀x (∃x P(x,x,y))", "premise" ) )
                            , ( 0, ( "∃x P(k,k,y)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Elimination (direct double elimination)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∀y P(x,y,x) ⊢ P(a,k,a)"

                        proof =
                            [ ( 0, ( "∀x ∀y (P(x,y,x))", "premise" ) )
                            , ( 0, ( "P(a,k,a)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Introduction (different predicates: arity)" <|
                \_ ->
                    let
                        goal =
                            "P(a) ⊢ ∃x P"

                        proof =
                            [ ( 0, ( "P(a)", "premise" ) )
                            , ( 0, ( "∃x(P)", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Introduction (different predicates: arity -- 2)" <|
                \_ ->
                    let
                        goal =
                            "P(a,a) ⊢ ∃x P(a)"

                        proof =
                            [ ( 0, ( "P(a,a)", "premise" ) )
                            , ( 0, ( "∃x(P(a))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Introduction (clashing existential)" <|
                \_ ->
                    let
                        goal =
                            "P(a,b) ⊢ ∃x P(x,x)"

                        proof =
                            [ ( 0, ( "P(a,b)", "premise" ) )
                            , ( 0, ( "∃x(P(x,x))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Introduction (clashing existential -- 2)" <|
                \_ ->
                    let
                        goal =
                            "P(a,b,a) ⊢ ∃x P(x,x,a)"

                        proof =
                            [ ( 0, ( "P(a,b,a)", "premise" ) )
                            , ( 0, ( "∃x(P(x,x,a))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Introduction (clashing existential -- 3)" <|
                \_ ->
                    let
                        goal =
                            "P(a,b,f(a)) ⊢ ∃x P(x,b,x)"

                        proof =
                            [ ( 0, ( "P(a,b,f(a))", "premise" ) )
                            , ( 0, ( "∃x P(x,b,x)", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Introduction (clash/illegal)" <|
                \_ ->
                    let
                        goal =
                            "∃x P(x,a,x,y) ⊢ ∃x ∃x P(x,a,x,x)"

                        proof =
                            [ ( 0, ( "∃x P(x,a,x,y)", "premise" ) )
                            , ( 0, ( "∃x (∃x P(x,a,x,x))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Introduction (clash/illegal -- 2)" <|
                \_ ->
                    let
                        goal =
                            "∃x ∀y P(x,a,x,f(x,y)) ⊢ ∃y ∃x ∀y P(x,y,x,f(x,y))"

                        proof =
                            [ ( 0, ( "∃x (∀y P(x,a,x,f(x,y)))", "premise" ) )
                            , ( 0, ( "∃y (∃x (∀y P(x,y,x,f(x,y))))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Introduction (capturing)" <|
                \_ ->
                    let
                        goal =
                            "∃x P(x,a,x,f(x)) ⊢ ∃y ∃x P(x,a,x,y)"

                        proof =
                            [ ( 0, ( "∃x P(x,a,x,f(x))", "premise" ) )
                            , ( 0, ( "∃y (∃x P(x,a,x,y))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Introduction (capturing -- 2)" <|
                \_ ->
                    let
                        goal =
                            "∃x P(x,a,x,f(x,x)) ⊢ ∃y ∃x P(x,a,x,f(x,y))"

                        proof =
                            [ ( 0, ( "∃x P(x,a,x,f(x,x))", "premise" ) )
                            , ( 0, ( "∃y (∃x P(x,a,x,f(x,y)))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Introduction (capturing -- 3)" <|
                \_ ->
                    let
                        goal =
                            "∃x ∀y P(x,g(x,y),x,f(x,y)) ⊢ ∃z ∃x ∀y P(x,z,x,f(x,y))"

                        proof =
                            [ ( 0, ( "∃x (∀y P(x,g(x,y),x,f(x,y)))", "premise" ) )
                            , ( 0, ( "∃z (∃x (∀y P(x,z,x,f(x,y))))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Introduction (capturing -- 3.1)" <|
                \_ ->
                    let
                        goal =
                            "∃x ∀y P(x,g(x),x,f(x,y)) ⊢ ∃z ∃x ∀y P(x,z,x,f(x,y))"

                        proof =
                            [ ( 0, ( "∃x (∀y P(x,g(x),x,f(x,y)))", "premise" ) )
                            , ( 0, ( "∃z (∃x (∀y P(x,z,x,f(x,y))))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Introduction (capturing -- 3.2)" <|
                \_ ->
                    let
                        goal =
                            "∃x ∀y P(x,g(y),x,f(x,y)) ⊢ ∃z ∃x ∀y P(x,z,x,f(x,y))"

                        proof =
                            [ ( 0, ( "∃x (∀y P(x,g(y),x,f(x,y)))", "premise" ) )
                            , ( 0, ( "∃z (∃x (∀y P(x,z,x,f(x,y))))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Introduction (illegal substitution)" <|
                \_ ->
                    let
                        goal =
                            "P(a) ⊢ ∀x P(x)"

                        proof =
                            [ ( 1, ( "[x0] P(a)", "premise" ) )
                            , ( 0, ( "∀x P(x)", "∀i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Universal Introduction (illegal substitution, no var fixed)" <|
                \_ ->
                    let
                        goal =
                            "P(a,x0) ⊢ ∀x P(a,x)"

                        proof =
                            [ ( 1, ( "P(a,x0)", "premise" ) )
                            , ( 0, ( "∀x P(a,x)", "∀i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Introduction (t1 /= t2) [1]" <|
                \_ ->
                    let
                        goal =
                            " ⊢ s ＝ t"

                        proof =
                            [ ( 0, ( "s ＝ t", "＝i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Introduction (t1 /= t2) [2]" <|
                \_ ->
                    let
                        goal =
                            "⊢ f(x) ＝ f(y)"

                        proof =
                            [ ( 0, ( "f(x) ＝ f(y)", "＝i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Introduction (t1 /= t2) [3]" <|
                \_ ->
                    let
                        goal =
                            "⊢ f(x,x) ＝ f(x,y)"

                        proof =
                            [ ( 0, ( "f(x,x) ＝ f(x,y)", "＝i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Introduction (t1 /= t2) [4]" <|
                \_ ->
                    let
                        goal =
                            "⊢ f(x,g(x),y) ＝ f(x,g(y),y)"

                        proof =
                            [ ( 0, ( "f(x,g(x),y) ＝ f(x,g(y),y)", "＝i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (equal to arbitrary term)" <|
                \_ ->
                    let
                        goal =
                            "s ＝ t, t ＝ u ⊢ u ＝ k"

                        proof =
                            [ ( 0, ( "s ＝ t", "premise" ) )
                            , ( 0, ( "t ＝ u", "premise" ) )
                            , ( 0, ( "u ＝ u", "＝i" ) )
                            , ( 0, ( "u ＝ k", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (order swapped)" <|
                \_ ->
                    let
                        goal =
                            "s ＝ t, t ＝ u ⊢ s ＝ u"

                        proof =
                            [ ( 0, ( "s ＝ t", "premise" ) )
                            , ( 0, ( "t ＝ u", "premise" ) )
                            , ( 0, ( "u ＝ s", "＝e" ) ) -- swapped
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (flipped)" <|
                \_ ->
                    let
                        goal =
                            "f(g(x),h(y)) ＝ a(q), P(a(q), f(x), a(q)) ⊢ P(a(q), f(x), f(g(x),h(y)) )"

                        proof =
                            [ ( 0, ( "f(g(x),h(y)) ＝ a(q)", "premise" ) )
                            , ( 0, ( "P(a(q),f(x),a(q))", "premise" ) )
                            , ( 0, ( "P(a(q),f(x),f(g(x),h(y)))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (capturing)" <|
                \_ ->
                    let
                        goal =
                            "x ＝ y, ∃y ∀z P(z,y,x) ⊢ ∃y ∀z P(z,y,y)"

                        proof =
                            [ ( 0, ( "x ＝ y", "premise" ) )
                            , ( 0, ( "∃y (∀z P(z,y,x))", "premise" ) )
                            , ( 0, ( "∃y (∀z P(z,y,y))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (capturing -- 2)" <|
                \_ ->
                    let
                        goal =
                            "a ＝ f(y), ∀x ∃y ∀z P(x,y,z,a) ⊢ ∀x ∃y ∀z P(x,y,z,f(y))"

                        proof =
                            [ ( 0, ( "a ＝ f(y)", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z,a)))", "premise" ) )
                            , ( 0, ( "∀x ∃y ∀z P(x,y,z,f(y))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (capturing -- 2 flipped)" <|
                \_ ->
                    let
                        goal =
                            "f(y) ＝ a, ∀x ∃y ∀z P(x,y,z,a) ⊢ ∀x ∃y ∀z P(x,y,z,f(y))"

                        proof =
                            [ ( 0, ( "f(y) ＝ a", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z,a)))", "premise" ) )
                            , ( 0, ( "∀x ∃y ∀z P(x,y,z,f(y))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (capturing -- 3)" <|
                \_ ->
                    let
                        goal =
                            "f(a) ＝ g(x,y), ∀x ∃y ∀z P(x,y,z,f(a)) ⊢ ∀x ∃y ∀z P(x,y,z,g(x,y))"

                        proof =
                            [ ( 0, ( "f(a) ＝ g(x,y)", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z,f(a))))", "premise" ) )
                            , ( 0, ( "∀x ∃y ∀z P(x,y,z,g(x,y))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (capturing -- 4)" <|
                \_ ->
                    let
                        goal =
                            "f(a) ＝ f(z), ∀x ∃y ∀z P(x,y,z,f(a)) ⊢ ∀x ∃y ∀z P(x,y,z,f(z))"

                        proof =
                            [ ( 0, ( "f(a) ＝ f(z)", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z,f(a))))", "premise" ) )
                            , ( 0, ( "∀x ∃y ∀z P(x,y,z,f(z))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (capturing -- 5)" <|
                \_ ->
                    let
                        goal =
                            "f(a,a) ＝ h(a,y), ∀x ∃y ∀z P(x,y,z,f(a,a)) ⊢ ∀x ∃y ∀z P(x,y,z,h(a,y))"

                        proof =
                            [ ( 0, ( "f(a,a) ＝ h(a,y)", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z,f(a,a))))", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z,h(a,y))))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (capturing -- 6)" <|
                \_ ->
                    let
                        goal =
                            "h(a,y) ＝ f(a,a), ∀x ∃y ∀z P(x,y,z,h(a,y)) ⊢ ∀x ∃y ∀z P(x,y,z,f(a,a))"

                        proof =
                            [ ( 0, ( "h(a,y) ＝ f(a,a)", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z,h(a,y))))", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z,f(a,a))))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (capturing -- 7)" <|
                \_ ->
                    let
                        goal =
                            "z ＝ a, ∀x ∃y ∀z P(x,y,z,f(z,a)) ⊢ ∀x ∃y ∀z P(x,y,z,f(a,a))"

                        proof =
                            [ ( 0, ( "z ＝ a", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z,f(z,a))))", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z,f(a,a))))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (capturing -- 8)" <|
                \_ ->
                    let
                        goal =
                            "z ＝ a, ∀x ∃y ∀z P(x,y,z,f(z,z)) ⊢ ∀x ∃y ∀z P(x,y,z,f(a,a))"

                        proof =
                            [ ( 0, ( "z ＝ a", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z,f(z,z))))", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z,f(a,a))))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (capturing -- 9)" <|
                \_ ->
                    let
                        goal =
                            "z ＝ a, ∀x ∃y ∀z P(x,y,z,f(z,z)) ⊢ ∀x ∃y ∀z P(x,y,z,f(a,z))"

                        proof =
                            [ ( 0, ( "z ＝ a", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z,f(z,z))))", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z,f(a,z))))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (capturing -- 10)" <|
                \_ ->
                    let
                        goal =
                            "z ＝ a, ∀x ∃y ∀z (P(x,x) ⟶ Q(z,y) ⟶ R(y,x)) ⊢ ∀x ∃y ∀z (P(x,x) ⟶ Q(a,y) ⟶ R(y,x))"

                        proof =
                            [ ( 0, ( "z ＝ a", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z (P(x,x) ⟶ (Q(z,y) ⟶ R(y,x)))))", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z (P(x,x) ⟶ (Q(a,y) ⟶ R(y,x)))))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (capturing -- 11)" <|
                \_ ->
                    let
                        goal =
                            "f(b,z) ＝ g(a), ∀x ∃y ∀z (P(x,x) ⟶ Q(f(b,z),y) ⟶ R(y,x)) ⊢ ∀x ∃y ∀z (P(x,x) ⟶ Q(g(a),y) ⟶ R(y,x))"

                        proof =
                            [ ( 0, ( "f(b,z) ＝ g(a)", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z (P(x,x) ⟶ (Q(f(b,z),y) ⟶ R(y,x)))))", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z (P(x,x) ⟶ (Q(g(a),y) ⟶ R(y,x)))))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (renaming bound var / capturing)" <|
                \_ ->
                    let
                        goal =
                            "x ＝ y, ∀x P(z,y,x) ⊢ ∀y P(z,y,y)"

                        proof =
                            [ ( 0, ( "x ＝ y", "premise" ) )
                            , ( 0, ( "∀x P(z,y,x)", "premise" ) )
                            , ( 0, ( "∀y P(z,y,y)", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (renaming bound var / capturing -- 2)" <|
                \_ ->
                    let
                        goal =
                            "x ＝ y, ∀x P(z,y,x) ⊢ ∀y P(z,y,x)"

                        proof =
                            [ ( 0, ( "x ＝ y", "premise" ) )
                            , ( 0, ( "∀x P(z,y,x)", "premise" ) )
                            , ( 0, ( "∀y P(z,y,x)", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (renaming bound var / capturing -- 3)" <|
                \_ ->
                    let
                        goal =
                            "x ＝ y, ∀x P(z,y,x) ⊢ ∀x P(z,y,y)"

                        proof =
                            [ ( 0, ( "x ＝ y", "premise" ) )
                            , ( 0, ( "∀x P(z,y,x)", "premise" ) )
                            , ( 0, ( "∀x P(z,y,y)", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (renaming bound var / capturing -- 4)" <|
                \_ ->
                    let
                        goal =
                            "x ＝ y, ∀x P(z,y,x,f(x)) ⊢ ∀x P(z,y,x,f(y))"

                        proof =
                            [ ( 0, ( "x ＝ y", "premise" ) )
                            , ( 0, ( "∀x P(z,y,x,f(x))", "premise" ) )
                            , ( 0, ( "∀x P(z,y,x,f(y))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (renaming bound var / capturing -- 5)" <|
                \_ ->
                    let
                        goal =
                            "x ＝ y, ∀x ∃y ∀z P(x,y,z) ⊢ ∀x ∃x ∀z P(x,y,z)"

                        proof =
                            [ ( 0, ( "x ＝ y", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z)))", "premise" ) )
                            , ( 0, ( "∀x (∃x (∀z P(x,y,z)))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (renaming bound var / capturing -- 6)" <|
                \_ ->
                    let
                        goal =
                            "x ＝ y, ∀x ∃y ∀z P(x,y,z) ⊢ ∀y ∃y ∀z P(x,y,z)"

                        proof =
                            [ ( 0, ( "x ＝ y", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z)))", "premise" ) )
                            , ( 0, ( "∀y (∃y (∀z P(x,y,z)))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (renaming bound var / capturing -- 7)" <|
                \_ ->
                    let
                        goal =
                            "x ＝ y, ∀x ∃y ∀z P(x,y,z) ⊢ ∀x ∃y ∀z P(y,y,z)"

                        proof =
                            [ ( 0, ( "x ＝ y", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z)))", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(y,y,z)))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Equality Elimination (renaming bound var / capturing -- 8)" <|
                \_ ->
                    let
                        goal =
                            "x ＝ y, ∀x ∃y ∀z P(x,y,z) ⊢ ∀y ∃x ∀z P(x,y,z)"

                        proof =
                            [ ( 0, ( "x ＝ y", "premise" ) )
                            , ( 0, ( "∀x (∃y (∀z P(x,y,z)))", "premise" ) )
                            , ( 0, ( "∀y (∃x (∀z P(x,y,z)))", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Exporting a local variable" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃y P(x,y), ∀x ∀y (P(x,y) ⟶ Q(x,y)) ⊢ ∃y ∀x Q(x,y)"

                        proof =
                            [ ( 0, ( "∀x(∃y(P(x,y)))", "premise" ) )
                            , ( 0, ( "∀x(∀y((P(x,y) ⟶ Q(x,y))))", "premise" ) )
                            , ( 1, ( "[x0] ∃y P(x0,y)", "∀e" ) )
                            , ( 1, ( "∀y (P(x0,y) ⟶ Q(x0,y))", "∀e" ) )
                            , ( 2, ( "[y0] P(x0,y0)", "ass" ) )
                            , ( 2, ( "P(x0,y0) ⟶ Q(x0,y0)", "∀e" ) )
                            , ( 2, ( "Q(x0,y0)", "⟶e" ) )
                            , ( 1, ( "Q(x0,y0)", "∃e" ) )
                            , ( 0, ( "∀x Q(x,y0)", "∀i" ) )
                            , ( 0, ( "∃y(∀x(Q(x,y)))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Elimination (capturing)" <|
                \_ ->
                    let
                        goal =
                            "∃x ∀x0 P(x0,x) ⊢ ∃x ∀x P(x,x)"

                        proof =
                            [ ( 0, ( "∃x (∀x0 P(x0,x))", "premise" ) )
                            , ( 1, ( "[x0] ∀x0 P(x0,x0)", "ass" ) )
                            , ( 2, ( "[x1]", "" ) )
                            , ( 2, ( "P(x1,x1)", "∀e" ) )
                            , ( 1, ( "∀x P(x,x)", "∀i" ) )
                            , ( 1, ( "∃x ∀x P(x,x)", "∃i" ) )
                            , ( 0, ( "∃x ∀x P(x,x)", "∃e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Elimination (capturing 2)" <|
                \_ ->
                    let
                        goal =
                            "∃x ∀x0 P(f(x0),x) ⊢ ∃x ∀x P(f(x),x)"

                        proof =
                            [ ( 0, ( "∃x (∀x0 P(f(x0),x))", "premise" ) )
                            , ( 1, ( "[x0] ∀x0 P(f(x0),x0)", "ass" ) )
                            , ( 2, ( "[x1]", "" ) )
                            , ( 2, ( "P(f(x1),x1)", "∀e" ) )
                            , ( 1, ( "∀x P(f(x),x)", "∀i" ) )
                            , ( 1, ( "∃x ∀x P(f(x),x)", "∃i" ) )
                            , ( 0, ( "∃x ∀x P(f(x),x)", "∃e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Elimination (capturing 3)" <|
                \_ ->
                    let
                        goal =
                            "∃x ∀x0 P(f(x0),x) ⊢ P(f(a), a)"

                        proof =
                            [ ( 0, ( "∃x (∀x0 P(f(x0),x))", "premise" ) )
                            , ( 1, ( "[x0] ∀x0 P(f(x0),x0)", "ass" ) )
                            , ( 1, ( "P(f(a), a)", "∀e" ) )
                            , ( 0, ( "P(f(a), a)", "∃e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Elimination (capturing/illegal)" <|
                \_ ->
                    let
                        goal =
                            "∃x ∀x0 P(f(x0),x) ⊢ P(f(a), a)"

                        proof =
                            [ ( 0, ( "∃x (∀x0 P(f(x0),x))", "premise" ) )
                            , ( 1, ( "[x0] ∀x0 P(f(x0),g(x0))", "ass" ) )
                            , ( 1, ( "P(f(a), g(a))", "∀e" ) )
                            , ( 0, ( "P(f(a), g(a))", "∃e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Elimination (illegal)" <|
                \_ ->
                    let
                        goal =
                            "∃x ∀x0 P(f(x0),x) ⊢ P(f(a), g(k))"

                        proof =
                            [ ( 0, ( "∃x (∀x0 P(f(x0),x))", "premise" ) )
                            , ( 1, ( "[x0] ∀x0 P(f(x0),g(k))", "ass" ) )
                            , ( 1, ( "P(f(a), g(k))", "∀e" ) )
                            , ( 0, ( "P(f(a), g(k))", "∃e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Elimination (clash)" <|
                \_ ->
                    let
                        goal =
                            "∃x ∃y (P(x,y) ∧ ∀x P(x,a)) ⊢ ∃z ∃y (P(z,y) ∧ (∀x P(z,a)))"

                        proof =
                            [ ( 0, ( "∃x (∃y (P(x,y) ∧ (∀x P(x,a))))", "premise" ) )
                            , ( 1, ( "[x0] ∃y (P(x0,y) ∧ (∀x P(x0,a)))", "ass" ) )
                            , ( 1, ( "∃z ∃y (P(z,y) ∧ (∀x P(z,a)))", "∃i" ) )
                            , ( 0, ( "∃z ∃y (P(z,y) ∧ (∀x P(z,a)))", "∃e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            , test "Existential Elimination (clash -- 2)" <|
                \_ ->
                    let
                        goal =
                            "∃x ∃y (P(y,y) ∧ ∀x P(x,a)) ⊢ ∃z ∃y (P(y,y) ∧ ∀x P(z,a))"

                        proof =
                            [ ( 0, ( "∃x ∃y (P(y,y) ∧ ∀x P(x,a))", "premise" ) )
                            , ( 1, ( "[x0] ∃y (P(y,y) ∧ ∀x P(x0,a))", "ass" ) )
                            , ( 1, ( "∃z ∃y (P(y,y) ∧ ∀x P(z,a))", "∃i" ) )
                            , ( 0, ( "∃z ∃y (P(y,y) ∧ ∀x P(z,a))", "∃e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result False
            ]
        ]
