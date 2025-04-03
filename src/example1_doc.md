# Proof Interaction Documentation Format

## 1. Proof Name:
*Extrinsic List Length*

## 2. Initial Proof with Typed Hole:
```haskell
{-@ listLength :: xs:[a] -> {v : Nat | v == len xs} @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_:xs) = 1 + listLength xs
{-@ measure listLength @-}

{-@ listLengthProof :: xs:[a] -> {listLength xs == len xs} @-}
listLengthProof :: [a] -> Proof
listLengthProof = hole
```
*(The `hole` represents the typed hole where LH should provide feedback.)*

## 3. Expected LH Response to Typed Hole:
- **Hole Information:** 
  LH should display the type of the hole
  In this case: `hole :: xs:[a] -> {listLength xs == len xs}`
- **Possible Feedback from LH:**
  - Suggest a Case Split to continue the proof.

## 4. User Reaction & Next Step:
The user replaces `hole` with the case split (this could also be automated):
```haskell
{-@ listLengthProof :: xs:[a] -> {listLength xs == len xs} @-}
listLengthProof :: [a] -> Proof
listLengthProof []     = hole
listLengthProof (x:xs) = hole
```

## 5. Next LH Response:


## 6. Completion Criteria:
- The proof is complete when LH verifies that all steps hold.
- No remaining typed holes (`_`) in the proof.
- The final proof should match LiquidHaskell’s expectations without errors.