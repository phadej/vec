# fin and vec

## Vec

`vec` provides few approache to work with `Vec`:
- `naive`: explicit recusion
    - no need to keep constraints around for most functions
    - simple
    - slow
- `pull`: `Vec n a` represented as `Fin n -> a`
    - Fuses well
    - Some code is hard to write (e.g. `Traversable`)
    - relatively simple
- `inline`, using `InlineInduction`:
    - exploits how GHC dictionary resolution works
    - makes code to unroll completely for staticaly known sizes
    - fast in that case

## Dependencies

![](https://raw.githubusercontent.com/phadej/vec/master/deps.png)

And with dependency flags turned off:

![](https://raw.githubusercontent.com/phadej/vec/master/deps-mini.png)


## Benchmarks: dotProduct

- `list` version sets the baseline, built-in fusion seems to kick in.
- `vector` and `unboxed` vector are 3x slower.
- *this library*, naive `vec` is even slower
- `Data.Vec.Pull` approach is slower, *except*
- that without conversions it's up to speed with `vector`
- `inline` (using `InlineInduction` over size) is *faster* than list version.

```
benchmarking dot product/list
time                 23.73 ns   (23.61 ns .. 23.88 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 23.69 ns   (23.58 ns .. 23.89 ns)
std dev              450.1 ps   (292.0 ps .. 731.3 ps)
variance introduced by outliers: 27% (moderately inflated)

benchmarking dot product/vector
time                 80.74 ns   (80.16 ns .. 81.42 ns)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 80.83 ns   (80.23 ns .. 82.21 ns)
std dev              2.760 ns   (1.657 ns .. 4.830 ns)
variance introduced by outliers: 53% (severely inflated)

benchmarking dot product/unboxed
time                 79.95 ns   (79.34 ns .. 80.74 ns)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 80.44 ns   (79.61 ns .. 82.51 ns)
std dev              4.278 ns   (2.029 ns .. 7.869 ns)
variance introduced by outliers: 74% (severely inflated)

benchmarking dot product/vec
time                 130.2 ns   (129.0 ns .. 131.6 ns)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 130.1 ns   (129.1 ns .. 131.7 ns)
std dev              4.185 ns   (3.108 ns .. 5.425 ns)
variance introduced by outliers: 49% (moderately inflated)

benchmarking dot product/pull
time                 245.3 ns   (245.1 ns .. 245.5 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 246.3 ns   (244.7 ns .. 254.1 ns)
std dev              9.924 ns   (409.7 ps .. 22.69 ns)
variance introduced by outliers: 59% (severely inflated)

benchmarking dot product/pull'
time                 71.18 ns   (70.73 ns .. 71.64 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 70.79 ns   (70.44 ns .. 71.30 ns)
std dev              1.397 ns   (925.3 ps .. 2.095 ns)
variance introduced by outliers: 27% (moderately inflated)

benchmarking dot product/inline
time                 20.91 ns   (20.64 ns .. 21.25 ns)
                     0.999 R²   (0.998 R² .. 0.999 R²)
mean                 21.12 ns   (20.90 ns .. 21.37 ns)
std dev              784.4 ps   (575.5 ps .. 1.107 ns)
variance introduced by outliers: 60% (severely inflated)
```
