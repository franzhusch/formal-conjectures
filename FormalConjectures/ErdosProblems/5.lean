/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 5

*Reference:* [erdosproblems.com/5](https://www.erdosproblems.com/5)

Let $S$ be the set of limit points of $(p_{n+1}-p_n)/\log n$. This problem asks whether
$S=[0,\infty]$. Although this conjecture remains unproven, a lot is known about $S$. Some highlights:

- $\infty \in S$ by Westzynthius' result [We31] on large prime gaps,
- $0 \in S$ by the work of Goldston, Pintz, and Yildirim [GPY09] on small prime gaps,
- Erdős [Er55] and Ricci [Ri56] independently showed that $S$ has positive Lebesgue measure,
- Hildebrand and Maier [HiMa88] showed that $S$ contains arbitrarily large (finite) numbers,
- Pintz [Pi16] showed that there exists some small constant $c>0$ such that $[0,c] \subset S$,
- Banks, Freiberg, and Maynard [BFM16] showed that at least $12.5\%$ of $[0,\infty)$ belongs to $S$,
- Merikoski [Me20] showed that at least $1/3$ of $[0,\infty)$ belongs to $S$, and that $S$ has
  bounded gaps.
-/

open scoped Topology NNReal
open Filter Real Set

namespace Erdos5

/--
The sequence of normalized prime gaps: $(p_{n+1} - p_n) / \log n$.
We use `EReal` to allow for infinite limit points.
-/
noncomputable def normalizedPrimeGap (n : ℕ) : EReal :=
  if n = 0 then 0 else (primeGap n : ℝ) / Real.log n

/--
The set of limit points (cluster points) of the normalized prime gap sequence.
A point $C$ is a limit point if there exists an infinite sequence $n_i$ such that
$\lim_{i \to \infty} (p_{n_i+1} - p_{n_i}) / \log n_i = C$.
-/
noncomputable def primeGapLimitPoints : Set EReal :=
  { C | MapClusterPt C atTop normalizedPrimeGap }

/--
The finite part of the set of limit points, as a subset of ℝ.
-/
noncomputable def finitePrimeGapLimitPoints : Set ℝ :=
  { c : ℝ | (c : EReal) ∈ primeGapLimitPoints }

/--
Erdős Problem 5: Is the set of limit points of $(p_{n+1}-p_n)/\log n$ equal to $[0, \infty]$?

Equivalently (as noted by Weisenberg), since the set of limit points is closed, this is
equivalent to asking whether the set is dense in $[0, \infty]$.
-/
@[category research open, AMS 11]
theorem erdos_5 : answer(sorry) ↔ primeGapLimitPoints = Set.Ici (0 : EReal) := by
  sorry

/--
Westzynthius [We31] proved that $\infty \in S$, i.e., there exist arbitrarily large prime gaps
relative to $\log n$.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.westzynthius_infinity :
    (⊤ : EReal) ∈ primeGapLimitPoints := by
  sorry

/--
Goldston, Pintz, and Yildirim [GPY09] proved that $0 \in S$, i.e., there exist arbitrarily small
prime gaps relative to $\log n$.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.goldston_pintz_yildirim_zero :
    (0 : EReal) ∈ primeGapLimitPoints := by
  sorry

/--
Erdős [Er55] and Ricci [Ri56] independently showed that $S$ has positive Lebesgue measure.
We state this for the finite part of $S$ intersected with $(0, \infty)$.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.erdos_ricci_positive_measure :
    0 < MeasureTheory.volume (finitePrimeGapLimitPoints ∩ Set.Ioi 0) := by
  sorry

/--
Hildebrand and Maier [HiMa88] showed that $S$ contains arbitrarily large finite numbers.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.hildebrand_maier_arbitrarily_large :
    ∀ M : ℝ, ∃ C ∈ primeGapLimitPoints, M < C ∧ C < ⊤ := by
  sorry

/--
Pintz [Pi16] showed that there exists some small constant $c > 0$ such that $[0, c] \subset S$.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.pintz_interval :
    ∃ c : ℝ, 0 < c ∧ Set.Icc (0 : EReal) c ⊆ primeGapLimitPoints := by
  sorry

/--
Banks, Freiberg, and Maynard [BFM16] showed that at least $12.5\%$ of $[0,\infty)$ belongs to $S$.

The precise statement is that the lower density (as $X \to \infty$) of the set
$\{x \in [0, X] : x \in S\}$ within $[0, X]$ is at least $0.125$.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.banks_freiberg_maynard :
    0.125 ≤ atTop.liminf
      (fun X : ℝ =>
        (MeasureTheory.volume (finitePrimeGapLimitPoints ∩ Set.Icc 0 X)).toReal / X) := by
  sorry

/--
Merikoski [Me20] showed that at least $1/3$ of $[0,\infty)$ belongs to $S$.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.merikoski_one_third :
    (1 : ℝ) / 3 ≤ atTop.liminf
      (fun X : ℝ =>
        (MeasureTheory.volume (finitePrimeGapLimitPoints ∩ Set.Icc 0 X)).toReal / X) := by
  sorry

/--
Merikoski [Me20] also showed that $S$ has bounded gaps, i.e., there exists $B > 0$ such that
for any $x \in [0, \infty)$, the interval $[x, x + B]$ contains a point of $S$.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.merikoski_bounded_gaps :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, 0 ≤ x →
      (Set.Icc x (x + B) ∩ finitePrimeGapLimitPoints).Nonempty := by
  sorry

/--
Alternative formulation: For any $C \geq 0$, is there an infinite sequence of $n_i$ such that
$\lim_{i \to \infty} (p_{n_i+1} - p_{n_i}) / \log n_i = C$?
-/
@[category research open, AMS 11]
theorem erdos_5.variants.explicit_formulation :
    answer(sorry) ↔ ∀ C : ℝ≥0, ∃ u : ℕ → ℕ, StrictMono u ∧
      Tendsto (fun i => (primeGap (u i) : ℝ) / Real.log (u i)) atTop (𝓝 (C : ℝ)) := by
  sorry

/--
The density question: For all $c \geq 0$, does the density of integers for which
$(p_{n+1} - p_n) / \log n < c$ exist and is it a continuous function of $c$?

This is related to Erdős Problem 234.
-/
@[category research open, AMS 11]
theorem erdos_5.variants.density_exists : answer(sorry) ↔ ∃ f : ℝ≥0 → ℝ, Continuous f ∧
    ∀ c : ℝ≥0, HasDensity {n : ℕ | (primeGap n : ℝ) / Real.log n < c} (f c) := by
  sorry

end Erdos5
