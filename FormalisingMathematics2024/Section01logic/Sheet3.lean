/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro hnT
  apply hnT
  triv
  done

example : False → ¬True := by
  exfalso
  done

example : ¬False → True := by
  change (False → False) → True
  intro
  triv

example : True → ¬False := by
  intro
  exfalso
  done

example : False → ¬P := by
  exfalso
  done

example : P → ¬P → False := by
  intro hP hnP
  apply hnP
  exact hP
  done

example : P → ¬¬P := by
  change P → ((P → False) → False)
  intro hP hPF
  apply hPF
  exact hP
  done

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ
  change (Q → False) → (P → False)
  intro hQF hP
  apply hQF
  apply hPQ
  exact hP
  done

example : ¬¬False → False := by
  intro hnnF
  apply hnnF
  exfalso
  done

example : ¬¬P → P := by
  intro hnnP
  by_contra hnP
  apply hnnP
  exact hnP
  done

example : (¬Q → ¬P) → P → Q := by
  intro hnQnP P
  by_contra nQ
  exact hnQnP nQ P
  done
