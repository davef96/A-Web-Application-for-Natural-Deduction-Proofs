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
            , test "Equality Introduction (t1 /= t2)" <|
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
            ]
        ]
