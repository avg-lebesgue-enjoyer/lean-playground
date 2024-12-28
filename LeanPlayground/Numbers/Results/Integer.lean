/- @file LeanPlayground/Numbers/Results/Integer.lean
 - Results proven about the integers ℤ.
 -/

/- IMPORTS: ℤ -/
import LeanPlayground.Numbers.Integer
import LeanPlayground.Numbers.Results.Natural



/- LAUNCH: Results -/

namespace Numbers.ℤ.results

  -- SECTION: Notation


  /- SECTION: Results yet to be proven
    [0.] Coersion ℕ ↪ ℤ
    [1.] Ring ℤ
      Include subtraction
    [2.] Order
      Positive numbers
      `<` and `≤`
    [3.] Euclidean division and Bezout's lemma
      Primality (include respecting `ℕ.prime` along `ℕ ↪ ℤ`)
      Euclidean division (include respecting `ℕ.euclidean_division` along `ℕ ↪ ℤ`)
      `gcd`
      Bezout's lemma
      (After this is done, move to a new file `Modular.lean` and start reasoning about `ℤ ⧸ n`; goal is still fund. arith.)
  -/


end Numbers.ℤ.results
