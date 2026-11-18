import Mathlib
import HRS.MC.CepN3Aux2

/-!
# Packet CEPN3, auxiliary 4: pathwise tube stability

For one sample path of the maximal solution, driven by a Brownian path that is `δ`-close to the rescaled noise
path `w` on `[0,T']`, the deterministic tube estimate `cep_N2` keeps the solution `ε'`-close to the steering
path `c` as long as the solution exists.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepN3

open HRS HRS.MC.CepN4

variable {N : ℕ}

theorem cepn3_path_claim {D : DynData 1} {T' : ℝ} {c v w : ℝ → Fin N → Euc 1} {σs ε' η δ : ℝ}
    (hσs : 0 < σs) (hvw : ∀ t, v t = σs • w t) (hδη : σs * δ < η)
    (hN2 : ∀ (y V : ℝ → Fin N → Euc 1) (s : ℝ), 0 ≤ s → s ≤ T' → Continuous y →
        ‖y 0 - c 0‖ < η → (∀ t ∈ Set.Icc 0 s, ‖V t - v t‖ < η) →
        (∀ t ∈ Set.Icc 0 s, y t ∈ liftedFree 1 N) →
        (∀ t ∈ Set.Icc 0 s, y t = y 0 + (∫ u in (0 : ℝ)..t, liftedDrift D (y u)) + V t) →
        ∀ t ∈ Set.Icc 0 s, ‖y t - c t‖ < ε')
    {τ : WithTop ℝ} {Yω : ℝ → Fin N → Euc 1} {X : ℝ≥0 → Fin N → Euc 1}
    (hcont : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ → ContinuousOn Yω (Set.Icc 0 t))
    (hfree : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ → Yω t ∈ liftedFree 1 N)
    (heq : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ →
      Yω t = Yω 0 + (∫ u in Set.Icc 0 t, liftedDrift D (Yω u)) + σs • X (Real.toNNReal t))
    (hinit : ‖Yω 0 - c 0‖ < η)
    (htube : ∀ t : ℝ≥0, (t : ℝ) ≤ T' → ‖X t - w t‖ ≤ δ) :
    ∀ s : ℝ, 0 ≤ s → s ≤ T' → (s : WithTop ℝ) < τ → ∀ t ∈ Set.Icc 0 s, ‖Yω t - c t‖ < ε' := by
  intro s hs0 hsT hsτ
  set κ : ℝ → ℝ := fun t => max 0 (min t s) with hκ
  have hκc : Continuous κ := by fun_prop
  have hκmem : ∀ t, κ t ∈ Set.Icc 0 s := fun t => ⟨le_max_left _ _, max_le hs0 (min_le_right _ _)⟩
  have hκid : ∀ t ∈ Set.Icc 0 s, κ t = t := fun t ht => by
    simp only [hκ, min_eq_left ht.2, max_eq_right ht.1]
  have hyc : Continuous fun t => Yω (κ t) :=
    (hcont s hs0 hsτ).comp_continuous hκc hκmem
  have hκ0 : κ 0 = 0 := hκid 0 ⟨le_rfl, hs0⟩
  refine fun t ht => ?_
  have key := hN2 (fun t => Yω (κ t)) (fun t => σs • X (Real.toNNReal t)) s hs0 hsT hyc
    (by simpa [hκ0] using hinit) ?_ ?_ ?_ t ht
  · simpa [hκid t ht] using key
  · intro t ht
    have h1 : v t = σs • w t := hvw t
    have h2 : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht.1
    have h3 := htube (Real.toNNReal t) (by rw [h2]; exact ht.2.trans hsT)
    rw [h2] at h3
    rw [h1, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hσs]
    calc σs * ‖X (Real.toNNReal t) - w t‖ ≤ σs * δ := mul_le_mul_of_nonneg_left h3 hσs.le
      _ < η := hδη
  · intro t ht
    simp only [hκid t ht]
    exact hfree t ht.1 (lt_of_le_of_lt (by exact_mod_cast ht.2) hsτ)
  · intro t ht
    simp only [hκid t ht, hκ0]
    have hI : ∫ u in (0 : ℝ)..t, liftedDrift D (Yω (κ u)) = ∫ u in Set.Icc 0 t, liftedDrift D (Yω u) := by
      rw [intervalIntegral.integral_of_le ht.1, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
      simp only [hκid u ⟨hu.1, hu.2.trans ht.2⟩]
    rw [hI]
    exact heq t ht.1 (lt_of_le_of_lt (by exact_mod_cast ht.2) hsτ)

end HRS.MC.CepN3
