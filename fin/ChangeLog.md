## 0.3

- Remove `Data.Fin.Enum` module. It didn't work as well as hoped.
- Add `EqP` and `OrdP` instances.
- Add `GShow Fin` instance.

## 0.2.1

- Add `boring` instances
- Explicitly implement `>=` and `>` for `Nat`.
- `<=`, `>=` and `min` for `Nat` are lazier
- Add `NFData (SNat n)` instance
- Add `GEq`, `GCompare`, `GNFData`, `GShow` (from `some` package) instances for `SNat`.

## 0.2

- `SNat` is now what was called `InlineInduction`.
  To migrate code from `fin-0.1` to `fin-0.2` it's often enough to
  replace `InlineInduction` with `SNatI`, and `inlineInduction` with `induction`. 
- Explicitly mark all modules as Safe or Trustworthy.

## 0.1.2

- Add `universe-base` `Universe` and `Finite` instances

## 0.1.1

- Add `isMin` and `isMax`
- Add `mirror`, `weakenRight1` and `weakenLeft1`
- Add `Mult2` and `DivMod2`
- Explicitly derive `Typeable SNat` and `Typeable LEProof`
- Derive `Typeable` for `Z` and `S` on GHC-7.8 explicitly
- Add `QuickCheck` instances for `Nat` and `Fin`

## 0.1

- Rename `Fin` constructors to `FZ` and `FS`.
  Now you can have both `Nat` and `Fin` imported unqualified in a single module.

## 0.0.3

- Add `Data.Type.Nat.LE`, `Data.Type.Nat.LT` and `Data.Type.Nat.LE.ReflStep`
  modules
- Add `withSNat` and `discreteNat`

## 0.0.2

- In `Fin` add: `append` and `split`
- Add `(Enum a, Enum b) => Enum (Either a b)` instance

## 0.0.1

- GHC-8.4.1 / base-4.11 support

## 0

- First version. Released on an unsuspecting world.
