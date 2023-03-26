module MatchingTests exposing (suite)

import Expect exposing (Expectation)
import Formula exposing (..)
import Fuzz exposing (Fuzzer, int, list, string)
import ProofChecking exposing (..)
import Rule exposing (..)
import Test exposing (..)



-- matchFormulas : Formula -> Formula -> Result ( String, ( Formula, Formula ) ) ( List FrmSubst, List TermSubst, List String)


suite : Test
suite =
    describe "Matching Tests"
        [ describe "matchFormulas"
            [ test "match(y = z, f(x) = g(x))" <|
                \_ ->
                    let
                        x =
                            Equals ( Var "y", Var "z" )

                        y =
                            Equals ( Func "f" [ Var "x" ], Func "g" [ Var "x" ] )

                        m =
                            matchFormulas x y

                        expect =
                            Ok ( [], [ ( Var "y", Func "f" [ Var "x" ] ), ( Var "z", Func "g" [ Var "x" ] ) ], ([], []) )
                    in
                    Expect.equal m expect
            , test "match(∀?v1(P(?v1)), ∀x(P(x)))" <|
                \_ ->
                    let
                        x =
                            ForAll "1" (Predicate "P" [ Var "1" ])

                        y =
                            ForAll "x" (Predicate "P" [ Var "x" ])

                        m =
                            matchFormulas x y

                        expect =
                            Ok ( [], [ ( Var "1", Var "x" ) ], (["1"], ["x"]) )
                    in
                    Expect.equal m expect
            ]
        ]
