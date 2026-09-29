import LeanMachineLearning.Online.Bandit.Algorithms.Regret.UCB
import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
import TrustAnnotations

/-!
# Bandits: what UCB's regret bound rests on

The definitions that `Bandits.UCB.regret_le_of_gt_two'`, the regret bound of the UCB algorithm, rests
on, declared from outside LeanMachineLearning: where they are meant to apply, what they are
determined up to, and theorems that pin them down.

* **Domains**, where junk values sit: an empirical mean and a confidence width divide by a number
  of pulls, and a mean is a Bochner integral, 0 for rewards with no integrable mean.
* **What `argmax` is determined up to**: one index among those where the function is largest.
* **Characterizations**, each by one theorem: the largest value of a tuple, the arm Round-Robin
  pulls, and the regret as a sum of gaps.
* **Specifications** and an **example**: properties that show a definition is the intended one.

A theorem of LeanMachineLearning cannot carry an annotation from outside it, so the specifications
are restatements here, each proved by the lemma it restates, or directly when LeanMachineLearning
has none.
-/

open MeasureTheory ProbabilityTheory Finset Learning Bandits

/-! ## Domains -/

attribute [domain (0 < pullCount' n h a) "the empirical mean of an arm never pulled is 0 / 0 = 0"]
  Learning.empMean'

attribute [domain (0 < pullCount' n h a) "the width of an arm never pulled is √(x / 0) = 0, where \
the textbook's index is +∞; the UCB algorithm pulls every arm once before it compares indices"]
  Bandits.UCB.ucbWidth'

attribute [domain (∀ b, Integrable id (ν b)) "the mean of an arm whose rewards have no integrable \
mean is 0 (`integral_undef`), and so is a supremum of means not bounded above"]
  Bandits.regret

attribute [domain (∀ b, Integrable id (ν b)) "the mean of an arm whose rewards have no integrable \
mean is 0 (`integral_undef`)"]
  Bandits.gap

/-! ## What `argmax` is determined up to -/

attribute [up_to (fun i j => f i = f j) "one index among those where f is largest: ties are broken \
by a choice, and a statement that tells two maximizers apart is about that choice"]
  argmax

namespace LMLCatalogue

/-! ## The largest value of a tuple -/

section Max

variable {ι α : Type*} [LinearOrder α] [Fintype ι] [Nonempty ι]

/-- **The largest value of a tuple is the value it takes that bounds all the others.** -/
@[characterization Function.max "the value it takes that bounds all the others"]
theorem eq_max_iff (f : ι → α) (x : α) : x = Function.max f ↔ (∃ i, f i = x) ∧ ∀ i, f i ≤ x := by
  constructor
  · rintro rfl
    exact ⟨exists_argmax f, Function.le_max f⟩
  · rintro ⟨⟨i, rfl⟩, hi⟩
    exact le_antisymm (Function.le_max f i) (Finset.sup'_le _ _ fun j _ => hi j)

/-- LeanMachineLearning's `isMaxOn_argmax`: it is an index where the tuple is largest. -/
@[specifies argmax "it is an index where the tuple is largest"]
theorem le_argmax (f : ι → α) (i : ι) : f i ≤ f (argmax f) :=
  isMaxOn_argmax f i

end Max

/-! ## Round-Robin -/

/-- **Round-Robin pulls arm `n % K` at time `n`.** -/
@[characterization Learning.RoundRobin.nextAction "arm n % K at time n"]
theorem eq_nextAction_iff {K : ℕ} [NeZero K] (n : ℕ) (i : Fin K) :
    i = RoundRobin.nextAction K n ↔ (i : ℕ) = n % K := by
  simp [RoundRobin.nextAction, Fin.ext_iff]

/-! ## UCB -/

/-- For its first `K` rounds, UCB pulls the arms in turn, as Round-Robin does: every arm has been
pulled once when it first compares indices. -/
@[specifies Bandits.UCB.nextArm "for its first K rounds, it pulls the arms in turn"]
theorem nextArm_of_lt {K : ℕ} [NeZero K] {c : ℝ} {n : ℕ} (hn : n < K) (h : Hist Unit (Fin K) ℝ n) :
    UCB.nextArm K c n h = RoundRobin.nextAction K n := by
  simp [UCB.nextArm, hn]

/-- From round `K` on, UCB pulls an arm of largest index: empirical mean plus confidence width. -/
@[specifies Bandits.UCB.nextArm "from round K on, an arm of largest index: empirical mean plus width"]
theorem index_le_nextArm {K : ℕ} [NeZero K] {c : ℝ} {n : ℕ} (hn : K ≤ n) (h : Hist Unit (Fin K) ℝ n)
    (a : Fin K) :
    empMean' n h a + UCB.ucbWidth' c n h a ≤
      empMean' n h (UCB.nextArm K c n h) + UCB.ucbWidth' c n h (UCB.nextArm K c n h) := by
  simp only [UCB.nextArm, not_lt.mpr hn, ↓reduceIte]
  exact isMaxOn_argmax (fun b => empMean' n h b + UCB.ucbWidth' c n h b) a

/-! ## Gaps and regret -/

section Regret

variable {𝓐 Ω : Type*} {m𝓐 : MeasurableSpace 𝓐} {ν : Kernel 𝓐 ℝ} {A : ℕ → Ω → 𝓐} {t : ℕ} {ω : Ω}

/-- LeanMachineLearning's `gap_nonneg`: no arm has a negative gap, for finitely many arms. -/
@[specifies Bandits.gap "no arm has a negative gap, for finitely many arms"]
theorem gap_nonneg [Finite 𝓐] {a : 𝓐} : 0 ≤ gap ν a :=
  Bandits.gap_nonneg

/-- **The regret is the sum of the gaps of the arms pulled**: LeanMachineLearning's
`regret_eq_sum_gap`. -/
@[characterization Bandits.regret "the sum of the gaps of the arms pulled"]
theorem eq_regret_iff (x : ℝ) : x = regret ν A t ω ↔ x = ∑ s ∈ range t, gap ν (A s ω) := by
  rw [regret_eq_sum_gap]

/-- LeanMachineLearning's `regret_nonneg`: the regret is never negative, for finitely many arms. -/
@[specifies Bandits.regret "it is never negative, for finitely many arms"]
theorem regret_nonneg [Finite 𝓐] : 0 ≤ regret ν A t ω :=
  Bandits.regret_nonneg

/-- Pulling one arm at every round costs its gap at every round. -/
@[specifies Bandits.regret "pulling one arm at every round costs its gap at every round"]
theorem regret_const (a : 𝓐) : regret ν (fun _ _ => a) t ω = t * gap ν a := by
  rw [regret_eq_sum_gap]
  simp

/-- Pulling a best arm at every round has no regret. -/
@[specifies Bandits.regret "pulling a best arm at every round has no regret"]
theorem regret_const_of_gap_eq_zero {a : 𝓐} (ha : gap ν a = 0) : regret ν (fun _ _ => a) t ω = 0 := by
  rw [regret_const, ha, mul_zero]

end Regret

/-! ## Algorithm-environment sequences -/

/-- LeanMachineLearning's `IT.isAlgEnvSeq_trajMeasure`: every algorithm and environment have an
algorithm-environment sequence, on the trajectory measure of the Ionescu-Tulcea theorem. Theorems
that assume one, such as UCB's regret bound, are not vacuous. -/
@[example_of Learning.IsAlgEnvSeq]
theorem isAlgEnvSeq_trajMeasure {𝓞 𝓐 𝓨 : Type*} [MeasurableSpace 𝓞] [MeasurableSpace 𝓐]
    [MeasurableSpace 𝓨] [StandardBorelSpace 𝓞] [Nonempty 𝓞] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    [StandardBorelSpace 𝓨] [Nonempty 𝓨] (alg : Algorithm 𝓞 𝓐 𝓨) (env : Environment 𝓞 𝓐 𝓨) :
    IsAlgEnvSeq IT.obs IT.action IT.feedback alg env (trajMeasure alg env) :=
  IT.isAlgEnvSeq_trajMeasure alg env

end LMLCatalogue
