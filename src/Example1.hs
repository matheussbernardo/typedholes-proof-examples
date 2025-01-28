{-@ LIQUID "--exact-data-cons" @-}
-- Based on https://ucsd-progsys.github.io/liquidhaskell-blog/2016/10/06/structural-induction.lhs/

module Example1 where
    import Prelude hiding ((<>))
    import Language.Haskell.Liquid.ProofCombinators ((===), (***), QED(QED), Proof)
    

    {-@ reflect empty @-}
    empty  :: [a]
    empty  = []

    {-@ infix <> @-}
    {-@ reflect <> @-}
    (<>) :: [a] -> [a] -> [a]
    [] <> xs = xs
    (x:xs) <> ys = x : (xs <> ys)

    {-@ leftId  :: x:[a] -> { (empty <> x) == x } @-}
    leftId :: [a] -> Proof
    leftId x
        =   empty <> x
        === _
        === x
        *** QED

    {-@ rightId  :: x:[a] -> { (x <> empty) == x } @-}
    rightId :: [a] -> Proof
    rightId x = _

    {-@ assoc  :: x:[a] -> y:[a] -> z:[a] -> { (x <> (y <> z)) == ((x <> y) <> z) } @-}
    assoc :: [a] -> [a] -> [a] -> Proof
    assoc x y z = _
