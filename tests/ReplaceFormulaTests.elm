module ReplaceFormulaTests exposing (suite)

import Expect exposing (Expectation)
import Formula exposing (..)
import Fuzz exposing (Fuzzer, int, list, string)
import Rule exposing (..)
import Test exposing (..)




suite : Test
suite =
    describe "ReplaceFormula"
        [ describe "replaceSubFormula"
            [ test "Neg (1)" <|
                \_ ->
                    let
                        x =
                            PredConst "1"

                        fsubst =
                            (PredConst "1", Neg (PredConst "P"))

                        m =
                            replaceSubFormula fsubst x

                        expect =
                            Neg (PredConst "P")
                    in
                    Expect.equal m expect
            , test "Neg (2)" <|
                \_ ->
                    let
                        x =
                            Neg (PredConst "1")

                        fsubst =
                            (PredConst "1", Neg (PredConst "P"))

                        m =
                            replaceSubFormula fsubst x

                        expect =
                            Neg (Neg (PredConst "P"))
                    in
                    Expect.equal m expect
            , test "Neg (3)" <|
                \_ ->
                    let
                        x =
                            ForAll "1" (PredConst "1")

                        fsubst =
                            (PredConst "1", Neg (PredConst "P"))

                        m =
                            replaceSubFormula fsubst x

                        expect =
                            ForAll "1" (Neg (PredConst "P"))
                    in
                    Expect.equal m expect
            , test "Neg (4)" <|
                \_ ->
                    let
                        x =
                            Exists "1" (PredConst "1")

                        fsubst =
                            (PredConst "1", Neg (PredConst "P"))

                        m =
                            replaceSubFormula fsubst x

                        expect =
                            Exists "1" (Neg (PredConst "P"))
                    in
                    Expect.equal m expect

            ]
        ]
