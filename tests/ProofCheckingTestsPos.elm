module ProofCheckingTestsPos exposing (suite)

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
    describe "Full Proof Tests (Parsing + Building + Checking) [Valid Proofs]"
        [ describe "Propositional Logic"
            [ test "Conjunction Introduction (simple)" <|
                \_ ->
                    let
                        goal =
                            "a, b ⊢ a ∧ b"

                        proof =
                            [ ( 0, ( "a", "premise" ) )
                            , ( 0, ( "b", "premise" ) )
                            , ( 0, ( "a ∧ b", "∧i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Conjunction Introduction (simple, reordered)" <|
                \_ ->
                    let
                        goal =
                            "a, b ⊢ b ∧ a"

                        proof =
                            [ ( 0, ( "a", "premise" ) )
                            , ( 0, ( "b", "premise" ) )
                            , ( 0, ( "b ∧ a", "∧i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Conjunction Introduction (advanced)" <|
                \_ ->
                    let
                        goal =
                            "p, q, r ⊢ (r ∧ q) ∧ p"

                        proof =
                            [ ( 0, ( "p", "premise" ) )
                            , ( 0, ( "q", "premise" ) )
                            , ( 0, ( "r", "premise" ) )
                            , ( 0, ( "r ∧ q", "∧i" ) )
                            , ( 0, ( "(r ∧ q) ∧ p", "∧i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Conjunction Introduction/Elimination" <|
                \_ ->
                    let
                        goal =
                            "p ∧ q, r ⊢ r ∧ q"

                        proof =
                            [ ( 0, ( "p ∧ q", "premise" ) )
                            , ( 0, ( "r", "premise" ) )
                            , ( 0, ( "q", "∧e" ) )
                            , ( 0, ( "r ∧ q", "∧i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Double Negation Introduction/Elimination + Conjunction Introduction" <|
                \_ ->
                    let
                        goal =
                            "p, ¬¬(q ∧ r) ⊢ ¬¬p ∧ r"

                        proof =
                            [ ( 0, ( "p", "premise" ) )
                            , ( 0, ( "¬¬(q ∧ r)", "premise" ) )
                            , ( 0, ( "¬¬p", "¬¬i" ) )
                            , ( 0, ( "q ∧ r", "¬¬e" ) )
                            , ( 0, ( "r", "∧e" ) )
                            , ( 0, ( "¬¬p ∧ r", "∧i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Implication Elimination" <|
                \_ ->
                    let
                        goal =
                            "p, p ⟶ q, p ⟶ (q ⟶ r) ⊢ r"

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
                    Expect.equal result True
            , test "Modus Tollens + Double Negation Elimination" <|
                \_ ->
                    let
                        goal =
                            "¬p ⟶ q, ¬q ⊢ p"

                        proof =
                            [ ( 0, ( "¬p ⟶ q", "premise" ) )
                            , ( 0, ( "¬q", "premise" ) )
                            , ( 0, ( "¬¬p", "MT" ) )
                            , ( 0, ( "p", "¬¬e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Implication Introduction + Modus Tollens + Double Negation Introduction/Elimination" <|
                \_ ->
                    let
                        goal =
                            "¬q ⟶ ¬p ⊢ p ⟶ q"

                        proof =
                            [ ( 0, ( "¬q ⟶ ¬p", "premise" ) )
                            , ( 1, ( "p", "assumption" ) )
                            , ( 1, ( "¬¬p", "¬¬i" ) )
                            , ( 1, ( "¬¬q", "MT" ) )
                            , ( 1, ( "q", "¬¬e" ) )
                            , ( 0, ( "p ⟶ q", "⟶i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Disjunction Introduction + Conjunction Elimination" <|
                \_ ->
                    let
                        goal =
                            "p ∧ q ⊢ ¬q ∨ p"

                        proof =
                            [ ( 0, ( "p ∧ q", "premise" ) )
                            , ( 0, ( "p", "∧e" ) )
                            , ( 0, ( "¬q ∨ p", "∨i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Disjunction Introduction/Elimination" <|
                \_ ->
                    let
                        goal =
                            "p ∨ q ⊢ q ∨ p"

                        proof =
                            [ ( 0, ( "p ∨ q", "premise" ) )
                            , ( 1, ( "p", "assumption" ) )
                            , ( 1, ( "q ∨ p", "∨i" ) )
                            , ( 1, ( "q", "assumption" ) )
                            , ( 1, ( "q ∨ p", "∨i" ) )
                            , ( 0, ( "q ∨ p", "∨e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Implication Introduction (single line)" <|
                \_ ->
                    let
                        goal =
                            "⊢ p ⟶ p"

                        proof =
                            [ ( 1, ( "p", "assumption" ) )
                            , ( 0, ( "p ⟶ p", "⟶i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Disjunction Introduction/Elimination + Implication Introduction" <|
                \_ ->
                    let
                        goal =
                            "⊢ p ∨ q ⟶ q ∨ p"

                        proof =
                            [ ( 1, ( "p ∨ q", "assumption" ) )
                            , ( 2, ( "p", "assumption" ) )
                            , ( 2, ( "q ∨ p", "∨i" ) )
                            , ( 2, ( "q", "assumption" ) )
                            , ( 2, ( "q ∨ p", "∨i" ) )
                            , ( 1, ( "q ∨ p", "∨e" ) )
                            , ( 0, ( "p ∨ q ⟶ q ∨ p", "⟶i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Implication Elimination + Negation Introduction/Elimination" <|
                \_ ->
                    let
                        goal =
                            "p ⟶ q, p ⟶ ¬q ⊢ ¬p"

                        proof =
                            [ ( 0, ( "p ⟶ q", "premise" ) )
                            , ( 0, ( "p ⟶ ¬q", "premise" ) )
                            , ( 1, ( "p", "assumption" ) )
                            , ( 1, ( "q", "⟶e" ) )
                            , ( 1, ( "¬q", "⟶e" ) )
                            , ( 1, ( "⊥", "¬e" ) )
                            , ( 0, ( "¬p", "¬i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Implication Elimination + Negation Elimination + Bottom Elimination" <|
                \_ ->
                    let
                        goal =
                            "p, p ⟶ q, p ⟶ ¬q ⊢ r"

                        proof =
                            [ ( 0, ( "p", "premise" ) )
                            , ( 0, ( "p ⟶ q", "premise" ) )
                            , ( 0, ( "p ⟶ ¬q", "premise" ) )
                            , ( 0, ( "q", "⟶e" ) )
                            , ( 0, ( "¬q", "⟶e" ) )
                            , ( 0, ( "⊥", "¬e" ) )
                            , ( 0, ( "r", "⊥e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Top Introduction" <|
                \_ ->
                    let
                        goal =
                            "⊢ ⊤"

                        proof =
                            [ ( 0, ( "⊤", "⊤i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Proof By Contradiction + Implication Introduction/Elimination + Negation Elimination" <|
                \_ ->
                    let
                        goal =
                            "p ⟶ q ∨ r, q ⟶ ¬p, ¬r ⟶ p ⊢ q ⟶ r"

                        proof =
                            [ ( 0, ( "p ⟶ q ∨ r", "premise" ) )
                            , ( 0, ( "q ⟶ ¬p", "premise" ) )
                            , ( 0, ( "¬r ⟶ p", "premise" ) )
                            , ( 1, ( "q", "assumption" ) )
                            , ( 1, ( "¬p", "⟶e" ) )
                            , ( 2, ( "¬r", "assumption" ) )
                            , ( 2, ( "p", "⟶e" ) )
                            , ( 2, ( "⊥", "¬e" ) )
                            , ( 1, ( "r", "PBC" ) )
                            , ( 0, ( "q ⟶ r", "⟶i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "LEM + Disjunction Introduction/Elimination" <|
                \_ ->
                    let
                        goal =
                            "⊢ ¬p ∨ p"

                        proof =
                            [ ( 0, ( "p ∨ ¬p", "LEM" ) )
                            , ( 1, ( "p", "assumption" ) )
                            , ( 1, ( "¬p ∨ p", "∨i" ) )
                            , ( 1, ( "¬p", "assumption" ) )
                            , ( 1, ( "¬p ∨ p", "∨i" ) )
                            , ( 0, ( "¬p ∨ p", "∨e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "LEM + Disjunction Introduction/Elimination + Implication Elimination" <|
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
                            , ( 1, ( "¬p", "assumption" ) )
                            , ( 1, ( "¬p ∨ q", "∨i" ) )
                            , ( 0, ( "¬p ∨ q", "∨e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Deriving MT" <|
                \_ ->
                    let
                        goal =
                            "ϕ ⟶ ψ, ¬ψ ⊢ ¬ϕ"

                        proof =
                            [ ( 0, ( "ϕ ⟶ ψ", "premise" ) )
                            , ( 0, ( "¬ψ", "premise" ) )
                            , ( 1, ( "ϕ", "assumption" ) )
                            , ( 1, ( "ψ", "⟶e" ) )
                            , ( 1, ( "⊥", "¬e" ) )
                            , ( 0, ( "¬ϕ", "¬i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Deriving Double Negation Introduction" <|
                \_ ->
                    let
                        goal =
                            "ϕ ⊢ ¬¬ϕ"

                        proof =
                            [ ( 0, ( "ϕ", "premise" ) )
                            , ( 1, ( "¬ϕ", "assumption" ) )
                            , ( 1, ( "⊥", "¬e" ) )
                            , ( 0, ( "¬¬ϕ", "¬i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Deriving LEM" <|
                \_ ->
                    let
                        goal =
                            "⊢ ϕ ∨ ¬ϕ"

                        proof =
                            [ ( 1, ( "¬(ϕ ∨ ¬ϕ)", "assumption" ) )
                            , ( 2, ( "ϕ", "assumption" ) )
                            , ( 2, ( "ϕ ∨ ¬ϕ", "∨i" ) )
                            , ( 2, ( "⊥", "¬e" ) )
                            , ( 1, ( "¬ϕ", "¬i" ) )
                            , ( 1, ( "ϕ ∨ ¬ϕ", "∨i" ) )
                            , ( 1, ( "⊥", "¬e" ) )
                            , ( 0, ( "¬¬(ϕ ∨ ¬ϕ)", "¬i" ) )
                            , ( 0, ( "ϕ ∨ ¬ϕ", "¬¬e" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            , test "Conjunction Introduction + Implication Introduction/Elimination" <|
                \_ ->
                    let
                        goal =
                            "p ∧ q ⟶ r ⊢ p ⟶ (q ⟶ r)"

                        proof =
                            [ ( 0, ( "p ∧ q ⟶ r", "premise" ) )
                            , ( 1, ( "p", "assumption" ) )
                            , ( 2, ( "q", "assumption" ) )
                            , ( 2, ( "p ∧ q", "∧i" ) )
                            , ( 2, ( "r", "⟶e" ) )
                            , ( 1, ( "q ⟶ r", "⟶i" ) )
                            , ( 0, ( "p ⟶ (q ⟶ r)", "⟶i" ) )
                            ]

                        result =
                            propCheck goal proof
                    in
                    Expect.equal result True
            ]
        , describe "Predicate Logic"
            [ test "Universal Elimination (0)" <|
                \_ ->
                    let
                        goal =
                            "∀x P ⊢ P"

                        proof =
                            [ ( 0, ( "∀x(P)", "premise" ) )
                            , ( 0, ( "P", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination (1)" <|
                \_ ->
                    let
                        goal =
                            "∀x P(x) ⊢ P(a)"

                        proof =
                            [ ( 0, ( "∀x(P(x))", "premise" ) )
                            , ( 0, ( "P(a)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination (1.1)" <|
                \_ ->
                    let
                        goal =
                            "∀x P(x) ⊢ P(x)"

                        proof =
                            [ ( 0, ( "∀x(P(x))", "premise" ) )
                            , ( 0, ( "P(x)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination (2.1)" <|
                \_ ->
                    let
                        goal =
                            "∀x P(x,y) ⊢ P(y,y)"

                        proof =
                            [ ( 0, ( "∀x(P(x,y))", "premise" ) )
                            , ( 0, ( "P(y,y)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination (2.2)" <|
                \_ ->
                    let
                        goal =
                            "∀x P(x,y) ⊢ P(a,y)"

                        proof =
                            [ ( 0, ( "∀x(P(x,y))", "premise" ) )
                            , ( 0, ( "P(a,y)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination (3)" <|
                \_ ->
                    let
                        goal =
                            "∀x P(x,y,x) ⊢ P(a,y,a)"

                        proof =
                            [ ( 0, ( "∀x(P(x,y,x))", "premise" ) )
                            , ( 0, ( "P(a,y,a)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination (3.1)" <|
                \_ ->
                    let
                        goal =
                            "∀x P(x,y,a) ⊢ P(a,y,a)"

                        proof =
                            [ ( 0, ( "∀x(P(x,y,a))", "premise" ) )
                            , ( 0, ( "P(a,y,a)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination (3.2)" <|
                \_ ->
                    let
                        goal =
                            "∀x P(a,y,x) ⊢ P(a,y,a)"

                        proof =
                            [ ( 0, ( "∀x(P(a,y,x))", "premise" ) )
                            , ( 0, ( "P(a,y,a)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination (3.3)" <|
                \_ ->
                    let
                        goal =
                            "∀x P(a,y,a) ⊢ P(a,y,a)"

                        proof =
                            [ ( 0, ( "∀x(P(a,y,a))", "premise" ) )
                            , ( 0, ( "P(a,y,a)", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination (4)" <|
                \_ ->
                    let
                        goal =
                            "∀x(∀y((P(x) ⟶ Q(y)))) ⊢ ∀y (P(y0) ⟶ Q(y))"

                        proof =
                            [ ( 0, ( "∀x(∀y((P(x) ⟶ Q(y))))", "premise" ) )
                            , ( 0, ( "∀y((P(y0) ⟶ Q(y)))", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination (4.1)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃y P(x,y) ⊢ ∃y P(a,y)"

                        proof =
                            [ ( 0, ( "∀x(∃y(P(x,y)))", "premise" ) )
                            , ( 0, ( "∃y(P(a,y))", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination (4.2)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∃y ∀z P(x,y,z) ⊢ ∃y ∀z P(a,y,z)"

                        proof =
                            [ ( 0, ( "∀x(∃y(∀z(P(x,y,z))))", "premise" ) )
                            , ( 0, ( "∃y(∀z(P(a,y,z)))", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination (4.3)" <|
                \_ ->
                    let
                        goal =
                            "∀x ∀y ∀z P(x,y,z) ⊢ ∀z P(a,a,z)"

                        proof =
                            [ ( 0, ( "∀x(∀y(∀z(P(x,y,z))))", "premise" ) )
                            , ( 0, ( "∀y(∀z(P(a,y,z)))", "∀e" ) )
                            , ( 0, ( "∀z(P(a,a,z))", "∀e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Existential Introduction (0)" <|
                \_ ->
                    let
                        goal =
                            "P ⊢ ∃x P"

                        proof =
                            [ ( 0, ( "P", "premise" ) )
                            , ( 0, ( "∃x(P)", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Existential Introduction (0.1)" <|
                \_ ->
                    let
                        goal =
                            "¬P ⊢ ∃x ¬P"

                        proof =
                            [ ( 0, ( "¬P", "premise" ) )
                            , ( 0, ( "∃x(¬P)", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Existential Introduction (1)" <|
                \_ ->
                    let
                        goal =
                            "P(a) ⊢ ∃x P(a)"

                        proof =
                            [ ( 0, ( "P(a)", "premise" ) )
                            , ( 0, ( "∃x(P(a))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Existential Introduction (1.1)" <|
                \_ ->
                    let
                        goal =
                            "P(a) ⊢ ∃x P(x)"

                        proof =
                            [ ( 0, ( "P(a)", "premise" ) )
                            , ( 0, ( "∃x(P(x))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Existential Introduction (2.1)" <|
                \_ ->
                    let
                        goal =
                            "P(a,a) ⊢ ∃x P(a,a)"

                        proof =
                            [ ( 0, ( "P(a,a)", "premise" ) )
                            , ( 0, ( "∃x(P(a,a))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Existential Introduction (2.2)" <|
                \_ ->
                    let
                        goal =
                            "P(a,a) ⊢ ∃x P(x,x)"

                        proof =
                            [ ( 0, ( "P(a,a)", "premise" ) )
                            , ( 0, ( "∃x(P(x,x))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Existential Introduction (2.3)" <|
                \_ ->
                    let
                        goal =
                            "P(a,a) ⊢ ∃x P(x,a)"

                        proof =
                            [ ( 0, ( "P(a,a)", "premise" ) )
                            , ( 0, ( "∃x(P(x,a))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Existential Introduction (2.4)" <|
                \_ ->
                    let
                        goal =
                            "P(a,a) ⊢ ∃x P(a,x)"

                        proof =
                            [ ( 0, ( "P(a,a)", "premise" ) )
                            , ( 0, ( "∃x(P(a,x))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Existential Introduction (3)" <|
                \_ ->
                    let
                        goal =
                            "P(a,b,a) ⊢ ∃x P(a,b,x)"

                        proof =
                            [ ( 0, ( "P(a,b,a)", "premise" ) )
                            , ( 0, ( "∃x(P(a,b,x))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Existential Introduction (3.1)" <|
                \_ ->
                    let
                        goal =
                            "P(a,b,a) ⊢ ∃x P(x,b,x)"

                        proof =
                            [ ( 0, ( "P(a,b,a)", "premise" ) )
                            , ( 0, ( "∃x(P(x,b,x))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Existential Introduction (3.2)" <|
                \_ ->
                    let
                        goal =
                            "P(a,b,a) ⊢ ∃x P(x,b,a)"

                        proof =
                            [ ( 0, ( "P(a,b,a)", "premise" ) )
                            , ( 0, ( "∃x(P(x,b,a))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Existential Introduction (3.3)" <|
                \_ ->
                    let
                        goal =
                            "P(a,b,a) ⊢ ∃x P(a,b,a)"

                        proof =
                            [ ( 0, ( "P(a,b,a)", "premise" ) )
                            , ( 0, ( "∃x(P(a,b,a))", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Equality Introduction" <|
                \_ ->
                    let
                        goal =
                            " ⊢ t ＝ t"

                        proof =
                            [ ( 0, ( "t ＝ t", "＝i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Equality Elimination (1)" <|
                \_ ->
                    let
                        goal =
                            "s ＝ t ⊢ t ＝ s"

                        proof =
                            [ ( 0, ( "s ＝ t", "premise" ) )
                            , ( 0, ( "s ＝ s", "＝i" ) )
                            , ( 0, ( "t ＝ s", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Equality Elimination (2)" <|
                \_ ->
                    let
                        goal =
                            "s ＝ t, t ＝ u ⊢ s ＝ u"

                        proof =
                            [ ( 0, ( "s ＝ t", "premise" ) )
                            , ( 0, ( "t ＝ u", "premise" ) )
                            , ( 0, ( "s ＝ u", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Equality Elimination (3)" <|
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
                    Expect.equal result True
            , test "Equality Elimination (4)" <|
                \_ ->
                    let
                        goal =
                            "x ＝ y, P(z,y,x) ⊢ P(z,y,y)"

                        proof =
                            [ ( 0, ( "x ＝ y", "premise" ) )
                            , ( 0, ( "P(z,y,x)", "premise" ) )
                            , ( 0, ( "P(z,y,y)", "＝e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Introduction (0)" <|
                \_ ->
                    let
                        goal =
                            "P ⊢ ∀x P"

                        proof =
                            [ ( 1, ( "[x0] P", "premise" ) )
                            , ( 0, ( "∀x P", "∀i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Introduction (0.5)" <|
                \_ ->
                    let
                        goal =
                            "¬P ⊢ ∀x ¬P"

                        proof =
                            [ ( 1, ( "¬P", "premise" ) )
                            , ( 0, ( "∀x(¬P)", "∀i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Introduction (0.1)" <|
                \_ ->
                    let
                        goal =
                            "P(a) ⊢ ∀x P(a)"

                        proof =
                            [ ( 1, ( "[x0] P(a)", "premise" ) )
                            , ( 0, ( "∀x P(a)", "∀i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Introduction/Elimination, Implication Elimination" <|
                \_ ->
                    let
                        goal =
                            "∀x (P(a) ⟶ P(x)), P(a) ⊢ ∀x P(x)"

                        proof =
                            [ ( 0, ( "∀x((P(a) ⟶ P(x)))", "premise" ) )
                            , ( 0, ( "P(a)", "premise" ) )
                            , ( 1, ( "[x0] P(a) ⟶ P(x0)", "∀e" ) )
                            , ( 1, ( "P(x0)", "⟶e" ) )
                            , ( 0, ( "∀x(P(x))", "∀i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Introduction/Elimination, Implication Elimination (1)" <|
                \_ ->
                    let
                        goal =
                            "∀x (P(x) ⟶ Q(x)), ∀x P(x) ⊢ ∀x Q(x)"

                        proof =
                            [ ( 0, ( "∀x((P(x) ⟶ Q(x)))", "premise" ) )
                            , ( 0, ( "∀x(P(x))", "premise" ) )
                            , ( 1, ( "[x0] P(x0) ⟶ Q(x0)", "∀e" ) )
                            , ( 1, ( "P(x0)", "∀e" ) )
                            , ( 1, ( "Q(x0)", "⟶e" ) )
                            , ( 0, ( "∀x(Q(x))", "∀i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Introduction/Elimination, Implication Introduction/Elimination" <|
                \_ ->
                    let
                        goal =
                            "P ⟶ ∀x Q(x) ⊢ ∀x (P ⟶ Q(x))"

                        proof =
                            [ ( 0, ( "P ⟶ ∀x(Q(x))", "premise" ) )
                            , ( 1, ( "[x0]", "" ) )
                            , ( 2, ( "P", "assumption" ) )
                            , ( 2, ( "∀x(Q(x))", "⟶e" ) )
                            , ( 2, ( "Q(x0)", "∀e" ) )
                            , ( 1, ( "P ⟶ Q(x0)", "⟶i" ) )
                            , ( 0, ( "∀x((P ⟶ Q(x)))", "∀i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination, Exists Introduction" <|
                \_ ->
                    let
                        goal =
                            "∀x ϕ ⊢ ∃x ϕ"

                        proof =
                            [ ( 0, ( "∀x(ϕ)", "premise" ) )
                            , ( 0, ( "ϕ", "∀e" ) )
                            , ( 0, ( "∃x(ϕ)", "∃i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination, Exists Elimination, Implication Elimination" <|
                \_ ->
                    let
                        goal =
                            "∃x P(x), ∀x (P(x) ⟶ Q(a)) ⊢ Q(a)"

                        proof =
                            [ ( 0, ( "∃x(P(x))", "premise" ) )
                            , ( 0, ( "∀x((P(x) ⟶ Q(a)))", "premise" ) )
                            , ( 1, ( "[x0] P(x0)", "assumption" ) )
                            , ( 1, ( "P(x0) ⟶ Q(a)", "∀e" ) )
                            , ( 1, ( "Q(a)", "⟶e" ) )
                            , ( 0, ( "Q(a)", "∃e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination, Exists Introduction/Elimination, Implication Elimination" <|
                \_ ->
                    let
                        goal =
                            "∀x (P(x) ⟶ Q(x)), ∃x P(x) ⊢ ∃x Q(x) "

                        proof =
                            [ ( 0, ( "∀x((P(x) ⟶ Q(x)))", "premise" ) )
                            , ( 0, ( "∃x(P(x))", "premise" ) )
                            , ( 1, ( "[x0] P(x0)", "assumption" ) )
                            , ( 1, ( "P(x0) ⟶ Q(x0)", "∀e" ) )
                            , ( 1, ( "Q(x0)", "⟶e" ) )
                            , ( 1, ( "∃x(Q(x))", "∃i" ) )
                            , ( 0, ( "∃x(Q(x))", "∃e" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Introduction/Elimination, Exists Elimination, Implication Elimination" <|
                \_ ->
                    let
                        goal =
                            "∃x(P(x)), ∀x ∀y (P(x) ⟶ Q(y)) ⊢ ∀y Q(y) "

                        proof =
                            [ ( 0, ( "∃x(P(x))", "premise" ) )
                            , ( 0, ( "∀x ∀y (P(x) ⟶ Q(y))", "premise" ) )
                            , ( 1, ( "[z]", "" ) )
                            , ( 2, ( "[y0] P(y0)", "assumption" ) )
                            , ( 2, ( "∀y (P(y0) ⟶ Q(y))", "∀e" ) )
                            , ( 2, ( "P(y0) ⟶ Q(z)", "∀e" ) )
                            , ( 2, ( "Q(z)", "⟶e" ) )
                            , ( 1, ( "Q(z)", "∃e" ) )
                            , ( 0, ( "∀y(Q(y))", "∀i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Introduction, Exists Introduction, Negation Elimination, PBC" <|
                \_ ->
                    let
                        goal =
                            "¬∀x ϕ ⊢ ∃x ¬ϕ"

                        proof =
                            [ ( 0, ( "¬∀x ϕ", "premise" ) )
                            , ( 1, ( "¬∃x ¬ϕ", "assumption" ) )
                            , ( 2, ( "[x0]", "" ) )
                            , ( 3, ( "¬ϕ", "assumption" ) )
                            , ( 3, ( "∃x ¬ϕ", "∃i" ) )
                            , ( 3, ( "⊥", "¬e" ) )
                            , ( 2, ( "ϕ", "PBC" ) )
                            , ( 1, ( "∀x ϕ", "∀i" ) )
                            , ( 1, ( "⊥", "¬e" ) )
                            , ( 0, ( "∃x ¬ϕ", "PBC" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Elimination, Exists Elimination, Negation Introduction/Elimination" <|
                \_ ->
                    let
                        goal =
                            "∃x ¬ϕ ⊢ ¬∀x ϕ"

                        proof =
                            [ ( 0, ( "∃x(¬ϕ)", "premise" ) )
                            , ( 1, ( "∀x ϕ", "assumption" ) )
                            , ( 2, ( "[x0] ¬ϕ", "assumption" ) )
                            , ( 2, ( "ϕ", "∀e" ) )
                            , ( 2, ( "⊥", "¬e" ) )
                            , ( 1, ( "⊥", "∃e" ) )
                            , ( 0, ( "¬∀x(ϕ)", "¬i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            , test "Universal Introduction, Exists Introduction, Negation Introduction/Elimination" <|
                \_ ->
                    let
                        goal =
                            "¬∃x P(x) ⊢ ∀x ¬P(x)"

                        proof =
                            [ ( 1, ( "[x] ¬∃x(P(x))", "premise" ) )
                            , ( 2, ( "P(x)", "assumption" ) )
                            , ( 2, ( "∃x P(x)", "∃i" ) )
                            , ( 2, ( "⊥", "¬e" ) )
                            , ( 1, ( "¬P(x)", "¬i" ) )
                            , ( 0, ( "∀x(¬P(x))", "∀i" ) )
                            ]

                        result =
                            folCheck goal proof
                    in
                    Expect.equal result True
            ]
        ]
