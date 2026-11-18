import HRS.MC.E214PD
import HRS.MC.E213U3C

/-!
# E214N1: the limit of an exponentially Cauchy family of projective tensors (`exists_limit_of_cauchy`)
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MC.E214N

set_option maxSynthPendingDepth 3

/-- The limit of an exponentially Cauchy family of projective tensors exists and is exponentially close to every member. -/
theorem exists_limit_of_cauchy_proof {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (F : ℝ → projTensor B 3) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (h : ∀ a h : ℝ, 0 ≤ a → 0 ≤ h → ‖F (a + h) - F a‖ ≤ C * Real.exp (-c * a)) :
    ∃ L : projTensor B 3, ∀ a : ℝ, 0 ≤ a → ‖F a - L‖ ≤ C * Real.exp (-c * a) := by
  haveI : CompleteSpace (TensorDual B 3) := inferInstance
  haveI : CompleteSpace (projTensor B 3) :=
    (HRS.MC.E213U3.u3_isClosed_proj B 3).completeSpace_coe
  -- difference estimate in terms of naturals
  have hnat : ∀ N n : ℕ, N ≤ n → ‖F n - F N‖ ≤ C * Real.exp (-c * N) := by
    intro N n hNn
    have := h (N : ℝ) ((n : ℝ) - N) (Nat.cast_nonneg N)
      (sub_nonneg.2 (by exact_mod_cast hNn))
    simpa using this
  have hb : Tendsto (fun N : ℕ => 2 * C * Real.exp (-c * N)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => Real.exp (-c * N)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc))
      refine this.congr (fun N => ?_)
      simp [mul_comm]
    simpa using h1.const_mul (2 * C)
  have hcs : CauchySeq (fun n : ℕ => F n) := by
    refine cauchySeq_of_le_tendsto_0 (fun N => 2 * C * Real.exp (-c * N)) (fun n m N hn hm => ?_) hb
    rw [dist_eq_norm]
    have h1 := hnat N n hn
    have h2 := hnat N m hm
    calc ‖F n - F m‖ = ‖(F n - F N) - (F m - F N)‖ := by congr 1; abel
      _ ≤ ‖F n - F N‖ + ‖F m - F N‖ := norm_sub_le _ _
      _ ≤ 2 * C * Real.exp (-c * N) := by linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨L, fun a ha => ?_⟩
  have hlim : Tendsto (fun n : ℕ => ‖F a - F n‖) atTop (𝓝 ‖F a - L‖) :=
    (tendsto_const_nhds.sub hL).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop ⌈a⌉₊] with n hn
  have hna : a ≤ n := (Nat.le_ceil a).trans (by exact_mod_cast hn)
  have := h a ((n : ℝ) - a) ha (sub_nonneg.2 hna)
  rw [norm_sub_rev]
  simpa using this

end HRS.MC.E214N

end
