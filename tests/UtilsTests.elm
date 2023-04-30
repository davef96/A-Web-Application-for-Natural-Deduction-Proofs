module UtilsTests exposing (suite)

import Expect exposing (Expectation)
import Fuzz exposing (Fuzzer, int, list, string)
import Rule exposing (..)
import Set
import Test exposing (..)
import Utils exposing (..)



--extractSingle : Int -> List a -> Maybe a
--extract : List Int -> List (List a) -> List a
--increment : List ( Int, Int ) -> List ( Int, Int )
--finished : List ( Int, Int ) -> Bool
--reset : List (Int, Int) -> List (Int, Int)
--instances : List (List a) -> List (List a)


suite : Test
suite =
    describe "Utils Tests"
        [ describe "tuples"
            [ test "tuples [1,2,3]" <|
                \_ ->
                    let
                        m =
                            tuples [ 1, 2, 3 ]
                                |> Set.fromList

                        expect =
                            [ ( 1, 2 ), ( 1, 3 ), ( 2, 3 ), ( 2, 1 ), ( 3, 1 ), ( 3, 2 ) ]
                                |> Set.fromList
                    in
                    Expect.equal m expect
            ]
        , describe "Instances & Helpers"
            [ test "extractSingle 2 [0,1,2,3]" <|
                \_ ->
                    let
                        m =
                            extractSingle 2 [ 0, 1, 2, 3 ]

                        expect =
                            Just 2
                    in
                    Expect.equal m expect
            , test "extract [0,1,2] [[0,1], [0,1,2], [0,1,2,3]]" <|
                \_ ->
                    let
                        m =
                            extract [ 0, 1, 2 ] [ [ 0, 1 ], [ 0, 1, 2 ], [ 0, 1, 2, 3 ] ]

                        expect =
                            Just [ 0, 1, 2 ]
                    in
                    Expect.equal m expect
            , test "increment [(0,1), (1,1), (1,2)]" <|
                \_ ->
                    let
                        m =
                            increment [ ( 0, 1 ), ( 1, 1 ), ( 1, 2 ) ]

                        expect =
                            [ ( 0, 1 ), ( 1, 1 ), ( 2, 2 ) ]
                    in
                    Expect.equal m expect
            , test "finished [(0,1), (1,1), (1,2)]" <|
                \_ ->
                    let
                        m =
                            finished [ ( 0, 1 ), ( 1, 1 ), ( 1, 2 ) ]

                        expect =
                            False
                    in
                    Expect.equal m expect
            , test "finished [(1,1), (1,1), (2,2)]" <|
                \_ ->
                    let
                        m =
                            finished [ ( 1, 1 ), ( 1, 1 ), ( 2, 2 ) ]

                        expect =
                            True
                    in
                    Expect.equal m expect
            , test "reset [(0,1), (1,1), (1,2)]" <|
                \_ ->
                    let
                        m =
                            reset [ ( 0, 1 ), ( 1, 1 ), ( 1, 2 ) ]

                        expect =
                            [ ( 0, 1 ), ( 0, 1 ), ( 0, 2 ) ]
                    in
                    Expect.equal m expect
            , test "instances [[0,1], [0,1,2], [0,1,2,3]]" <|
                \_ ->
                    let
                        m =
                            instances [ [ 0, 1 ], [ 0, 1, 2 ], [ 0, 1, 2, 3 ] ]

                        expect =
                            [ [ 0, 0, 0 ]
                            , [ 0, 0, 1 ]
                            , [ 0, 0, 2 ]
                            , [ 0, 0, 3 ]
                            , [ 0, 1, 0 ]
                            , [ 0, 1, 1 ]
                            , [ 0, 1, 2 ]
                            , [ 0, 1, 3 ]
                            , [ 0, 2, 0 ]
                            , [ 0, 2, 1 ]
                            , [ 0, 2, 2 ]
                            , [ 0, 2, 3 ]
                            , [ 1, 0, 0 ]
                            , [ 1, 0, 1 ]
                            , [ 1, 0, 2 ]
                            , [ 1, 0, 3 ]
                            , [ 1, 1, 0 ]
                            , [ 1, 1, 1 ]
                            , [ 1, 1, 2 ]
                            , [ 1, 1, 3 ]
                            , [ 1, 2, 0 ]
                            , [ 1, 2, 1 ]
                            , [ 1, 2, 2 ]
                            , [ 1, 2, 3 ]
                            ]
                    in
                    Expect.equal m expect
            ]
        ]
