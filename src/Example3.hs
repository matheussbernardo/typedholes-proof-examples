{-@ LIQUID "--exact-data-cons" @-}
-- Based on paper: Theorem Proving for All: Equational Reasoning in Liquid Haskell (Functional Pearl)

module Example3 where
    import Prelude hiding ((<>), reverse, length, (++))
    import Language.Haskell.Liquid.ProofCombinators ((===), (***), (?), QED(QED), Proof)

    {-@ length :: [a] -> {v:Int | 0 <= v } @-}
    length :: [a] -> Int
    length [] = 0
    length (_:xs) = 1 + length xs
    {-@ measure length @-}

    {-@ reverse :: is:[a] -> {os:[a] | length is == length os} @-}
    reverse :: [a] -> [a]
    reverse [] = []
    reverse (x:xs) = reverse xs ++ [x]

    {-@ (++) :: xs:[a] -> ys:[a] -> {zs:[a] | length zs == length xs + length ys} @-}
    (++) :: [a] -> [a] -> [a]
    [] ++ ys = ys
    (x:xs) ++ ys = x : (xs ++ ys)
    {-@ infixl ++ @-}

    {-@ reflect reverse @-}
    {-@ reflect ++ @-}

    {-@ reverseApp :: xs:[a] -> ys:[a] -> {zs:[a] | zs == reverse xs ++ ys} @-}
    reverseApp :: [a] -> [a] -> [a]
    reverseApp [] ys     
        = reverse [] ++ ys
        === [] ++ ys 
        === ys
    reverseApp (x:xs) ys 
        = reverse (x:xs) ++ ys
        === (reverse xs ++ [x]) ++ ys
        === (reverse xs ++ [x] ++ ys) ? _ -- I need a lemma here! Can the hole help me?
        === reverse xs ++ ([x] ++ ys)
        -- It continues here following the paper
