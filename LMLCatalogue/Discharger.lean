import LeanMachineLearning.Online.Bandit.Regret
import LeanMachineLearning.SequentialLearning.Algorithm
import Mathlib.Probability.Moments.SubGaussian

/-!
# How the catalogue's domains are shown to hold

The well-definedness analyzer ([LeanTrustBuilders/well-defined](https://github.com/LeanTrustBuilders/well-defined))
checks each use of a definition with a declared domain against what is in scope where it sits. Its
default dischargers know nothing of the facts that put LeanMachineLearning's statements inside the
domains this catalogue and the Mathlib catalogue declare: that subgaussian rewards have integrable
means, and that the regret of an algorithm-environment sequence is integrable.

`lml_catalogue_discharger` is those facts: CI names it as a discharger
(`trust-extract welldefined --discharger lml_catalogue_discharger`). It is a `solve_by_elim` over
them, so what it proves is proved, and what it misses stays open rather than being guessed.
-/

open MeasureTheory ProbabilityTheory Finset Learning Bandits
open scoped NNReal

namespace LMLCatalogue

/-- Rewards whose centred values are subgaussian have an integrable mean. -/
theorem integrable_id_of_hasSubgaussianMGF {𝓐 : Type*} {m𝓐 : MeasurableSpace 𝓐} {ν : Kernel 𝓐 ℝ}
    [IsMarkovKernel ν] {σ2 : ℝ≥0} (h : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) :
    ∀ a, Integrable id (ν a) := fun a ↦ by
  have : (id : ℝ → ℝ) = fun x ↦ (x - (ν a)[id]) + (ν a)[id] := funext fun x ↦ by simp
  rw [this]
  exact (h a).integrable.add (integrable_const _)

/-- The regret of an algorithm-environment sequence with finitely many arms is integrable: it is a
bounded function of the arms pulled. -/
theorem integrable_regret {𝓞 𝓐 𝓨 Ω : Type*} [MeasurableSpace 𝓞] {m𝓐 : MeasurableSpace 𝓐}
    [MeasurableSpace 𝓨] [Finite 𝓐] [MeasurableSingletonClass 𝓐] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {ν : Kernel 𝓐 ℝ} {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐}
    {Y : ℕ → Ω → 𝓨} {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
    (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) : Integrable (regret ν A n) P := by
  have : regret ν A n = fun ω ↦ ∑ s ∈ range n, gap ν (A s ω) := funext fun _ ↦ regret_eq_sum_gap
  rw [this]
  exact integrable_finsetSum _ fun s _ ↦
    (Integrable.of_finite (f := fun a ↦ gap ν a)).comp_measurable (h.measurable_action s)

end LMLCatalogue

/-- The facts behind the domains of LeanMachineLearning's bandit statements, as a discharger for the
well-definedness analyzer. -/
macro "lml_catalogue_discharger" : tactic => `(tactic| solve_by_elim (maxDepth := 6)
  [LMLCatalogue.integrable_id_of_hasSubgaussianMGF, LMLCatalogue.integrable_regret])
