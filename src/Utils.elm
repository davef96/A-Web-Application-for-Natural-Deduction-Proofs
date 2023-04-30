module Utils exposing (..)

import Parser
import String



-- appends pairs of lists pairwise


appendTuples : ( List a, List b ) -> ( List a, List b ) -> ( List a, List b )
appendTuples pair1 pair2 =
    let
        ( xs1, xs2 ) =
            pair1

        ( ys1, ys2 ) =
            pair2
    in
    ( xs1 ++ ys1, xs2 ++ ys2 )



-- remove duplicates in both lists within a tuple


removeDuplicatesInTuple : ( List a, List b ) -> ( List a, List b )
removeDuplicatesInTuple pair =
    let
        ( xs, ys ) =
            pair
    in
    ( removeDuplicates xs, removeDuplicates ys )



-- get all tuples from list (cartesian/cross product with itself)


tuples : List a -> List ( a, a )
tuples xs =
    let
        cross =
            List.foldl
                (\x state ->
                    List.map (\y -> ( x, y )) xs ++ state
                )
                []
                xs
    in
    cross
        |> removeEqPairs



-- extract element at position i in xs


extractSingle : Int -> List a -> Maybe a
extractSingle i xs =
    xs
        |> List.drop i
        |> List.head



-- extracts respective position from respective list


extract : List Int -> List (List a) -> Maybe (List a)
extract is xss =
    case is of
        [] ->
            Just []

        i :: ri ->
            case xss of
                [] ->
                    Just []

                xs :: rxs ->
                    let
                        recur =
                            extract ri rxs
                    in
                    case extractSingle i xs of
                        Just e ->
                            case recur of
                                Nothing ->
                                    Nothing

                                Just rest ->
                                    Just (e :: rest)

                        Nothing ->
                            Nothing



-- increments last counter with value < len, given list of (i, len_i)


increment : List ( Int, Int ) -> List ( Int, Int )
increment xs =
    xs
        |> List.reverse
        |> incrementHelper []
        |> List.reverse


incrementHelper : List ( Int, Int ) -> List ( Int, Int ) -> List ( Int, Int )
incrementHelper acc xs =
    case xs of
        [] ->
            []

        ( i, len ) :: rest ->
            if i < len then
                reset (List.reverse acc) ++ ( i + 1, len ) :: rest

            else
                incrementHelper (( i, len ) :: acc) rest



-- reset counters


reset : List ( Int, Int ) -> List ( Int, Int )
reset xs =
    xs
        |> List.map (\( i, len ) -> ( 0, len ))



-- all counters are equal to the length of the respective list


finished : List ( Int, Int ) -> Bool
finished xs =
    xs
        |> List.foldl
            (\( i, len ) state ->
                if i < len then
                    False

                else
                    state
            )
            True



-- obtain all instances, i.e., combinations of elements of each list


instances : List (List a) -> List (List a)
instances xss =
    let
        cnt =
            List.map (\xs -> ( 0, List.length xs )) xss
    in
    instancesHelper [] cnt xss


instancesHelper : List (List a) -> List ( Int, Int ) -> List (List a) -> List (List a)
instancesHelper acc cnt xss =
    if finished cnt then
        acc
            |> List.reverse

    else
        let
            instance =
                extract (List.map Tuple.first cnt) xss
        in
        case instance of
            Nothing ->
                instancesHelper acc (increment cnt) xss

            Just inst ->
                instancesHelper (inst :: acc) (increment cnt) xss



-- (x,y) => (y,x)


swapTuples : List ( a, a ) -> List ( a, a )
swapTuples xs =
    List.map (\( x, y ) -> ( y, x )) xs



-- checks if 'xs' is composed of unique elements


unique : List a -> Bool
unique xs =
    let
        ys =
            removeDuplicates xs
    in
    List.length xs == List.length ys



-- obtains tuples in list where lhs occurs multiple times with different rhs


rightDiff : List ( a, a ) -> List ( a, a )
rightDiff xs =
    case xs of
        [] ->
            []

        ( x1, y1 ) :: ys ->
            case List.filter (\( x2, y2 ) -> x1 == x2 && y1 /= y2) ys of
                [] ->
                    rightDiff ys |> removeDuplicates

                zs ->
                    ( x1, y1 ) :: zs ++ rightDiff ys |> removeDuplicates



-- obtain differences in lists
-- first: elements missing in second list
-- second: elements missing in first list


diff : List a -> List a -> ( List a, List a )
diff xs ys =
    ( sublistMissing xs ys, sublistMissing ys xs )



-- returns list of elements in 'xs' that are missing in 'ys'


sublistMissing : List a -> List a -> List a
sublistMissing xs ys =
    case xs of
        [] ->
            []

        z1 :: zs1 ->
            let
                recur =
                    sublistMissing zs1 ys
            in
            if List.member z1 ys then
                recur

            else
                z1 :: recur



-- checks if 'xs' is sublist of 'ys'


sublist : List a -> List a -> Bool
sublist xs ys =
    sublistMissing xs ys
        |> List.isEmpty



-- obtains indices of elements in 'xs' in list 'ys'


getIndices : List a -> List a -> List (Maybe Int)
getIndices xs ys =
    case xs of
        [] ->
            []

        z :: zs ->
            let
                recur =
                    getIndices zs ys
            in
            case anyElemPos (\y -> y == z) ys of
                Nothing ->
                    Nothing :: recur

                Just ( _, i ) ->
                    Just i :: recur



-- reorders list elements according to index list


reorder : List a -> List (Maybe Int) -> List a
reorder xs is =
    reorderHelper xs is
        |> List.sortWith
            (\( i, _ ) ( j, _ ) ->
                compare i j
            )
        |> List.map (\( _, x ) -> x)


reorderHelper : List a -> List (Maybe Int) -> List ( Int, a )
reorderHelper xs is =
    case is of
        [] ->
            List.indexedMap Tuple.pair xs

        mi :: ks ->
            case mi of
                Nothing ->
                    reorderHelper xs ks

                Just i ->
                    case xs of
                        [] ->
                            []

                        x :: ys ->
                            -- put x on position i in result
                            ( i, x ) :: reorderHelper ys ks



-- removes duplicates in given list


removeDuplicates : List a -> List a
removeDuplicates xs =
    case xs of
        [] ->
            []

        y :: ys ->
            let
                zs =
                    List.filter (\z -> z /= y) ys
            in
            y :: removeDuplicates zs



-- removes pairs where first == second


removeEqPairs : List ( a, a ) -> List ( a, a )
removeEqPairs xs =
    case xs of
        [] ->
            []

        ( y1, y2 ) :: ys ->
            if y1 == y2 then
                removeEqPairs ys

            else
                ( y1, y2 ) :: removeEqPairs ys



-- remove pairs where first == second && first in list xs


removeEqPairsFor : List a -> List ( a, a ) -> List ( a, a )
removeEqPairsFor xs ys =
    case ys of
        [] ->
            []

        ( y1, y2 ) :: rest ->
            if y1 == y2 && List.member y1 xs then
                removeEqPairsFor xs rest

            else
                ( y1, y2 ) :: removeEqPairsFor xs rest



-- remove pairs where first == second && first not in list xs


removeEqPairsExcept : List a -> List ( a, a ) -> List ( a, a )
removeEqPairsExcept xs ys =
    case ys of
        [] ->
            []

        ( y1, y2 ) :: rest ->
            if y1 == y2 && not (List.member y1 xs) then
                removeEqPairsExcept xs rest

            else
                ( y1, y2 ) :: removeEqPairsExcept xs rest



-- removes first list from second


without : List a -> List a -> List a
without xs ys =
    case xs of
        [] ->
            ys

        z :: zs ->
            without zs (List.filter (\y -> y /= z) ys)



-- helper for 'anyElemPos': keeps track of list position and finds first element that satisfies predicate p


anyElemPosHelper : Int -> (a -> Bool) -> List a -> Maybe ( a, Int )
anyElemPosHelper i p xs =
    case xs of
        [] ->
            Nothing

        y :: ys ->
            if p y then
                Just ( y, i )

            else
                anyElemPosHelper (i + 1) p ys



-- obtains first list element that satisfies predicate p, with position


anyElemPos : (a -> Bool) -> List a -> Maybe ( a, Int )
anyElemPos =
    anyElemPosHelper 0



-- obtains first list element that satisfies predicate p


anyElem : (a -> Bool) -> List a -> Maybe a
anyElem p xs =
    Maybe.map Tuple.first (anyElemPos p xs)



-- obtains first list element that satisfies predicate p, and the list without this element


anyElemRemove : (a -> Bool) -> List a -> ( Maybe a, List a )
anyElemRemove p xs =
    let
        ( ys, y, zs ) =
            split p xs
    in
    ( y, ys ++ zs )



-- helper to split a list into 3 parts, according to a predicate p


splitHelper : List a -> (a -> Bool) -> List a -> ( List a, Maybe a, List a )
splitHelper acc p xs =
    let
        rs =
            List.reverse acc
    in
    case xs of
        [] ->
            -- predicate was never satisfied
            ( rs, Nothing, [] )

        y :: ys ->
            if p y then
                ( rs, Just y, ys )

            else
                splitHelper (y :: acc) p ys



-- splits list into 3 parts, according to a predicate p


split : (a -> Bool) -> List a -> ( List a, Maybe a, List a )
split =
    splitHelper []



-- splits list into two parts according to given predicate (split element in lhs)


lsplit : (a -> Bool) -> List a -> ( List a, List a )
lsplit p xs =
    case split p xs of
        ( ys, Nothing, zs ) ->
            ( ys, zs )

        ( ys, Just z, zs ) ->
            ( ys ++ [ z ], zs )



-- splits list into two parts according to given predicate (split element in rhs)


rsplit : (a -> Bool) -> List a -> ( List a, List a )
rsplit p xs =
    case split p xs of
        ( ys, Nothing, zs ) ->
            ( ys, zs )

        ( ys, Just z, zs ) ->
            ( ys, z :: zs )



-- helper to split a list into (xs, Maybe last)


splitLastHelper : List a -> List a -> ( List a, Maybe a )
splitLastHelper acc xs =
    case xs of
        [] ->
            ( [], Nothing )

        y :: ys ->
            case ys of
                [] ->
                    ( List.reverse acc, Just y )

                _ ->
                    splitLastHelper (y :: acc) ys



-- splits list into (xs, Maybe last)


splitLast : List a -> ( List a, Maybe a )
splitLast =
    splitLastHelper []



-- since 'deadEndsToString' is not implemented in the Parser module...
-- inspired by https://github.com/elm/parser/pull/16/files


deadEndsToString : List Parser.DeadEnd -> String
deadEndsToString deadends =
    case deadends of
        [] ->
            ""

        deadend :: _ ->
            let
                ( disjunction, others ) =
                    deadends
                        |> List.partition (\d -> d.row == deadend.row && d.col == deadend.col)

                ( expecting, errors ) =
                    disjunction
                        |> List.map (\d -> problemToString d.problem)
                        |> removeDuplicates
                        |> List.partition Tuple.first
                        |> Tuple.mapBoth (List.map Tuple.second) (List.map Tuple.second)

                strexp =
                    "Expecting " ++ String.join " | " expecting

                strerr =
                    String.join " & " errors

                strpos =
                    " at row=" ++ String.fromInt deadend.row ++ ", col=" ++ String.fromInt deadend.col

                str =
                    if List.isEmpty errors then
                        strexp ++ strpos

                    else if List.isEmpty expecting then
                        strerr

                    else
                        strexp ++ ", " ++ strerr ++ " at row=" ++ String.fromInt deadend.row ++ ", col=" ++ String.fromInt deadend.col
            in
            str ++ deadEndsToString others



-- returns (expecting, string)


problemToString : Parser.Problem -> ( Bool, String )
problemToString p =
    case p of
        Parser.Expecting s ->
            ( True, "'" ++ s ++ "'" )

        Parser.ExpectingInt ->
            ( True, "int" )

        Parser.ExpectingHex ->
            ( True, "hex" )

        Parser.ExpectingOctal ->
            ( True, "octal" )

        Parser.ExpectingBinary ->
            ( True, "binary" )

        Parser.ExpectingFloat ->
            ( True, "float" )

        Parser.ExpectingNumber ->
            ( True, "number" )

        Parser.ExpectingVariable ->
            ( True, "var" )

        Parser.ExpectingSymbol s ->
            ( True, "'" ++ s ++ "'" )

        Parser.ExpectingKeyword s ->
            ( True, "'" ++ s ++ "'" )

        Parser.ExpectingEnd ->
            ( True, "end" )

        Parser.UnexpectedChar ->
            ( False, "unexpected char" )

        Parser.Problem s ->
            ( False, s )

        Parser.BadRepeat ->
            ( False, "bad repeat" )
