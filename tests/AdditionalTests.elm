module AdditionalTests exposing (suite)

import Expect exposing (Expectation)
import Formula exposing (..)
import Fuzz exposing (Fuzzer, int, list, string)
import Rule exposing (..)
import Test exposing (..)


lessSpecificThan : Order
lessSpecificThan =
    GT


moreSpecificThan : Order
moreSpecificThan =
    LT


equallySpecific : Order
equallySpecific =
    EQ


suite : Test
suite =
    describe "Abstract Specificity Tests"
        [ describe "specificityComparison"
            [ describe "Block vs. Formula"
                [ test "Block([], [], Top) vs. Formula(Top)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( Top, [] )

                            y =
                                AbstractFormula ( Top, [] )

                            c =
                                specificityComparison x y

                            expect =
                                moreSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], 1) vs. Formula(1)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( PredConst "1", [] )

                            y =
                                AbstractFormula ( PredConst "1", [] )

                            c =
                                specificityComparison x y

                            expect =
                                moreSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], 1) vs. Formula(Top)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( PredConst "1", [] )

                            y =
                                AbstractFormula ( Top, [] )

                            c =
                                specificityComparison x y

                            expect =
                                lessSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], 1) vs. Formula(1 ⟶ Top)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( PredConst "1", [] )

                            y =
                                AbstractFormula ( Impl (PredConst "1") Top, [] )

                            c =
                                specificityComparison x y

                            expect =
                                lessSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], 1) vs. Formula(1 ⟶ 2)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( PredConst "1", [] )

                            y =
                                AbstractFormula ( Impl (PredConst "1") (PredConst "2"), [] )

                            c =
                                specificityComparison x y

                            expect =
                                moreSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], 1) vs. Formula(¬1)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( PredConst "1", [] )

                            y =
                                AbstractFormula ( Neg (PredConst "1"), [] )

                            c =
                                specificityComparison x y

                            expect =
                                moreSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], 1) vs. Formula(¬¬1)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( PredConst "1", [] )

                            y =
                                AbstractFormula ( Neg (Neg (PredConst "1")), [] )

                            c =
                                specificityComparison x y

                            expect =
                                moreSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], 1) vs. Formula(¬¬¬¬1)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( PredConst "1", [] )

                            y =
                                AbstractFormula ( Neg (Neg (Neg (Neg (PredConst "1")))), [] )

                            c =
                                specificityComparison x y

                            expect =
                                moreSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], 1) vs. Formula(¬1 ⟶ 2)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( PredConst "1", [] )

                            y =
                                AbstractFormula ( Impl (Neg (PredConst "1")) (PredConst "2"), [] )

                            c =
                                specificityComparison x y

                            expect =
                                moreSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], Top) vs. Formula(¬1 ⟶ 2)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( Top, [] )

                            y =
                                AbstractFormula ( Impl (Neg (PredConst "1")) (PredConst "2"), [] )

                            c =
                                specificityComparison x y

                            expect =
                                moreSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [1], ¬p ∨ p) vs. Formula(¬p ∨ p) " <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [ ( Neg (PredConst "p"), [] ) ] ( Disj (Neg (PredConst "1")) (PredConst "1"), [] )

                            y =
                                AbstractFormula ( Disj (Neg (PredConst "1")) (PredConst "1"), [] )

                            c =
                                specificityComparison x y

                            expect =
                                moreSpecificThan
                        in
                        Expect.equal c expect
                ]
            , describe "Block vs. Block"
                [ test "Block([], [], Top) vs. Block([], [], 1)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( Top, [] )

                            y =
                                AbstractBlock [] [] ( PredConst "1", [] )

                            c =
                                specificityComparison x y

                            expect =
                                moreSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], Top) vs. Block([], [Top], Top)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( Top, [] )

                            y =
                                AbstractBlock [] [ ( Top, [] ) ] ( Top, [] )

                            c =
                                specificityComparison x y

                            expect =
                                lessSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], 1) vs. Block([], [1], 2)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( PredConst "1", [] )

                            y =
                                AbstractBlock [] [ ( PredConst "1", [] ) ] ( PredConst "2", [] )

                            c =
                                specificityComparison x y

                            expect =
                                lessSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [1], 2) vs. Block([], [1,2], 3)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [ ( PredConst "1", [] ) ] ( PredConst "2", [] )

                            y =
                                AbstractBlock [] [ ( PredConst "1", [] ), ( PredConst "2", [] ) ] ( PredConst "3", [] )

                            c =
                                specificityComparison x y

                            expect =
                                lessSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], Bot) vs. Block([], [1], 2)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( Bot, [] )

                            y =
                                AbstractBlock [] [ ( PredConst "1", [] ) ] ( PredConst "2", [] )

                            c =
                                specificityComparison x y

                            expect =
                                moreSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], Bot) vs. Block([], [1], Bot)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( Bot, [] )

                            y =
                                AbstractBlock [] [ ( PredConst "1", [] ) ] ( Bot, [] )

                            c =
                                specificityComparison x y

                            expect =
                                lessSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], Bot) vs. Block([], [Top], Bot)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( Bot, [] )

                            y =
                                AbstractBlock [] [ ( Top, [] ) ] ( Bot, [] )

                            c =
                                specificityComparison x y

                            expect =
                                lessSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], ¬1) vs. Block([], [], 1)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( Neg (PredConst "1"), [] )

                            y =
                                AbstractBlock [] [] ( PredConst "1", [] )

                            c =
                                specificityComparison x y

                            expect =
                                moreSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [], ¬1) vs. Block([], [1], 2)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( Neg (PredConst "1"), [] )

                            y =
                                AbstractBlock [] [ ( PredConst "1", [] ) ] ( PredConst "2", [] )

                            c =
                                specificityComparison x y

                            expect =
                                equallySpecific
                        in
                        Expect.equal c expect
                , test "Block([], [], ¬1) vs. Block([], [Top], 1)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [] ( Neg (PredConst "1"), [] )

                            y =
                                AbstractBlock [] [ ( Top, [] ) ] ( PredConst "1", [] )

                            c =
                                specificityComparison x y

                            expect =
                                lessSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [1], ¬1) vs. Block([], [Top], 1)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [ ( PredConst "1", [] ) ] ( Neg (PredConst "1"), [] )

                            y =
                                AbstractBlock [] [ ( Top, [] ) ] ( PredConst "1", [] )

                            c =
                                specificityComparison x y

                            expect =
                                lessSpecificThan
                        in
                        Expect.equal c expect
                , test "Block([], [p], ¬p ∨ p) vs. Block([], [¬p], ¬p ∨ p)" <|
                    \_ ->
                        let
                            x =
                                AbstractBlock [] [ ( PredConst "p", [] ) ] ( Disj (Neg (PredConst "1")) (PredConst "1"), [] )

                            y =
                                AbstractBlock [] [ ( Neg (PredConst "p"), [] ) ] ( Disj (Neg (PredConst "1")) (PredConst "1"), [] )

                            c =
                                specificityComparison x y

                            expect =
                                lessSpecificThan
                        in
                        Expect.equal c expect
                ]
            ]
        ]
