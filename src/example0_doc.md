# Proof Interaction Documentation Format

## 1. Proof Name:
*Simple List Length Intrinsic Proof*

## 2. Initial Proof with Typed Hole:
```haskell
module Example0 where
    hole = undefined
    -- len is the length of a list in the logic
    {-@ listLength :: xs:[a] -> {v : Nat | v == len xs} @-}
    listLength :: [a] -> Int
    listLength [] = hole
    listLength (x:xs) = hole
```
*(The `hole` represents the typed hole where LH should provide feedback.)*

## 3. Expected LH Response to Typed Hole:
- **First Hole Type Information:** 
  LiquidHaskell could display the type of the first hole
  and it is reasonable that substituting `xs` for `[]`
  `hole :: {v : Nat | v == len [] }`
- **Second Hole Type Information:**
  LiquidHaskell could display the type of the second hole
  and it is reasonable that substituting `xs` for `(x:xs)`
  `hole :: {v : Nat | v == len (x:xs) }`


## 4. User Reaction & Next Step:
The user replaces the first `hole` with `0`:
```haskell
  listLength [] = 0
```

The user replaces the second `hole` with `1 + hole`
```haskell
  listLength (x:xs) = 1 + hole
```

## 5. Expected LH Response to Typed Hole:
- **Hole Type Information:** 
  Given the specification:
  `{-@ listLength :: xs:[a] -> {v : Nat | v == len xs} @-}`
  We know that `v == len (x:xs)` and we know that
  `v == (1 + hole)` so we can discover that `(1 + hole) == len (x:xs)`
  Simplifying to `hole == len (x:xs) - 1` and with further simplification
  `hole == len xs`

  


