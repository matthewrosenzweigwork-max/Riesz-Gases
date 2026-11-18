import HRS.MC.CepE6aA8
import HRS.MC.CepE6DS2
import HRS.MC.CepE6DW3
import HRS.MC.CepE2Aux2

/-!
# Packet CEPE6E, file 1: deterministic basics for conjunct (e)

* continuity and monotonicity of `∇Φ` on the open alcove;
* the resolvent `J_n` is nonexpansive and `‖z - J_n z‖ ≤ ‖∇Φ(z)‖ / n` on the alcove (from monotonicity);
* uniform convergence is preserved by composition with a continuous map (on a compact time set).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6E

open HRS HRS.MC.Cepa

variable {N : ℕ}

/-- `∇Φ` is continuous on the open alcove. -/
theorem cepe6e_gr_continuousOn (a : ℝ) :
    ContinuousOn (gradient (cep_chamberPot a N)) (cep_Alcove N) := by
  intro z hz
  refine ContinuousAt.continuousWithinAt ?_
  have hev : gradient (cep_chamberPot a N) =ᶠ[𝓝 z]
      fun w => HRS.MC.CepE1.cepe1_pairGrad (HRS.MC.CepE1.cepe1_h1 a N) w := by
    filter_upwards [HRS.MC.CepE6A.e6a_alcove_open.mem_nhds hz] with w hw
    exact HRS.MC.CepE6A.e6a_hasGrad hw
  exact (HRS.MC.CepE6A.e6a_pairGrad_cont hz).congr_of_eventuallyEq hev

/-- Monotonicity of `∇Φ` on the open alcove. -/
theorem cepe6e_gr_monotone {a : ℝ} (ha : 0 ≤ a) {x y : Ch N} (hx : x ∈ cep_Alcove N)
    (hy : y ∈ cep_Alcove N) :
    0 ≤ ⟪gradient (cep_chamberPot a N) x - gradient (cep_chamberPot a N) y, x - y⟫ := by
  rw [HRS.MC.CepE6A.e6a_hasGrad hx, HRS.MC.CepE6A.e6a_hasGrad hy]
  exact HRS.MC.CepE2.cepe2_monotone ha hx hy

/-- The resolvent is nonexpansive. -/
theorem cepe6e_J_nonexp {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J) {n : ℝ}
    (hn : 0 < n) (x y : Ch N) : ‖J n x - J n y‖ ≤ ‖x - y‖ := by
  have hm := cepe6e_gr_monotone ha.le (hJ.mem n x hn) (hJ.mem n y hn)
  rw [← hJ.force n x hn, ← hJ.force n y hn] at hm
  have e : n • (x - J n x) - n • (y - J n y) = n • ((x - y) - (J n x - J n y)) := by
    rw [← smul_sub]; congr 1; abel
  rw [e, inner_smul_left, inner_sub_left] at hm
  simp only [conj_trivial] at hm
  have h1 : ‖J n x - J n y‖ ^ 2 ≤ ⟪x - y, J n x - J n y⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    have := (mul_nonneg_iff_of_pos_left hn).1 hm
    linarith
  have h2 : ⟪x - y, J n x - J n y⟫ ≤ ‖x - y‖ * ‖J n x - J n y‖ := real_inner_le_norm _ _
  by_cases h0 : ‖J n x - J n y‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖J n x - J n y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

/-- The Yosida defect at an alcove point: `‖n (z - J_n z)‖ ≤ ‖∇Φ(z)‖`. -/
theorem cepe6e_J_defect {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J) {n : ℝ}
    (hn : 0 < n) {z : Ch N} (hz : z ∈ cep_Alcove N) :
    ‖n • (z - J n z)‖ ≤ ‖gradient (cep_chamberPot a N) z‖ := by
  have hm := cepe6e_gr_monotone ha.le (hJ.mem n z hn) hz
  set G : Ch N := n • (z - J n z) with hG
  rw [← hJ.force n z hn] at hm
  have e : J n z - z = -(n⁻¹ • G) := by
    rw [hG, smul_smul, inv_mul_cancel₀ hn.ne', one_smul]; abel
  rw [e, inner_neg_right, inner_smul_right, inner_sub_left] at hm
  have h1 : ‖G‖ ^ 2 ≤ ⟪gradient (cep_chamberPot a N) z, G⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    have hn' : 0 < n⁻¹ := inv_pos.2 hn
    have : n⁻¹ * (⟪G, G⟫ - ⟪gradient (cep_chamberPot a N) z, G⟫) ≤ 0 := by linarith
    by_contra hc
    push Not at hc
    nlinarith [mul_pos hn' (by linarith : 0 < ⟪G, G⟫ - ⟪gradient (cep_chamberPot a N) z, G⟫)]
  have h2 : ⟪gradient (cep_chamberPot a N) z, G⟫ ≤ ‖gradient (cep_chamberPot a N) z‖ * ‖G‖ :=
    real_inner_le_norm _ _
  by_cases h0 : ‖G‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖G‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

/-- `‖z - J_n z‖ ≤ ‖∇Φ(z)‖ / n` on the alcove. -/
theorem cepe6e_J_close {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J) {n : ℝ}
    (hn : 0 < n) {z : Ch N} (hz : z ∈ cep_Alcove N) :
    ‖z - J n z‖ ≤ ‖gradient (cep_chamberPot a N) z‖ / n := by
  have h := cepe6e_J_defect ha hJ hn hz
  rw [norm_smul, Real.norm_of_nonneg hn.le] at h
  rw [le_div_iff₀ hn]
  linarith

/-- Uniform convergence is preserved by composition with a continuous map, on a compact time set. -/
theorem cepe6e_tuo_comp {X : Type*} [PseudoMetricSpace X] {H : Ch N → X} (hH : Continuous H)
    {Zs : ℕ → ℝ → Ch N} {Zl : ℝ → Ch N} {S : Set ℝ} (hS : IsCompact S) (hZl : ContinuousOn Zl S)
    (hu : TendstoUniformlyOn Zs Zl atTop S) :
    TendstoUniformlyOn (fun i s => H (Zs i s)) (fun s => H (Zl s)) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  set K : Set (Ch N) := Metric.cthickening 1 (Zl '' S) with hK
  have hKc : IsCompact K := (hS.image_of_continuousOn hZl).cthickening
  have huc : UniformContinuousOn H K := hKc.uniformContinuousOn_of_continuous hH.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc ε hε
  filter_upwards [hu (min δ 1) (lt_min hδ one_pos)] with i hi s hs
  have h1 := hi s hs
  have h2 : Zs i s ∈ K := by
    refine Metric.mem_cthickening_of_dist_le _ (Zl s) 1 _ ⟨s, hs, rfl⟩ ?_
    rw [dist_comm]; exact (h1.trans_le (min_le_right _ _)).le
  have h3 : Zl s ∈ K := Metric.self_subset_cthickening _ ⟨s, hs, rfl⟩
  have := hδ' (Zl s) h3 (Zs i s) h2 (lt_of_lt_of_le h1 (min_le_left _ _))
  simpa [dist_comm] using this

/-- Uniform convergence on `[0,T]` of continuous real functions passes to the interval integrals. -/
theorem cepe6e_integral_tuo {T : ℝ} (hT : 0 ≤ T) {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ i, ContinuousOn (F i) (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T))
    (h : TendstoUniformlyOn F f atTop (Icc 0 T)) :
    Tendsto (fun i => ∫ s in (0 : ℝ)..T, F i s) atTop (𝓝 (∫ s in (0 : ℝ)..T, f s)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε / (T + 1) := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 h (ε / (T + 1)) hε'] with i hi
  rw [dist_eq_norm, ← intervalIntegral.integral_sub ((hF i).intervalIntegrable_of_Icc hT)
    (hf.intervalIntegrable_of_Icc hT)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
    (f := fun s => F i s - f s) (C := ε / (T + 1)) (fun s hs => by
      rw [uIoc_of_le hT] at hs
      have := hi s ⟨hs.1.le, hs.2⟩
      rw [Real.dist_eq, abs_sub_comm] at this
      simpa [Real.norm_eq_abs] using this.le)
  refine lt_of_le_of_lt this ?_
  rw [sub_zero, abs_of_nonneg hT]
  have e : ε / (T + 1) * T = ε * (T / (T + 1)) := by ring
  rw [e]
  have : T / (T + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
  nlinarith

end HRS.MC.CepE6E
