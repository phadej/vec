# Revision history for fin

## 0.1.1

- Add `isMin` and `isMax`

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
