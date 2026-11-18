import HRS.MS.S104eReg2

/-!
# S10.4 (nonlinear), packet S104E-3: weak continuity of the density path of a resulting solution

`s104e_sqrt_integrable`: `√ρ_β ∈ L¹` (Gaussian bound).  `s104e_weak_cont`: for every bounded continuous `ψ`, `t ↦ ∫ ψ ρ^t` is continuous on `[0,∞)`
(the `cont` field of `CoeffHypRd`), from the continuity of `t ↦ v_t ∈ Σ^{102d+1020}` and the Sobolev bound `‖w‖_∞ ≤ C ‖w‖_{Σ^m}` (`mn_force_bound`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104e

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S104b HRS.MS.Mov63 HRS.MS.S105r

variable {d : ℕ}

theorem s104e_probInt {ρ : Euc d → ℝ} (h : HRS.Whole.IsProbDensity ρ) : Integrable ρ := by
  by_contra hn
  have := h.integral_one
  rw [integral_undef hn] at this
  exact zero_ne_one this

theorem s104e_sqrt_integrable {ρβ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (hq : 0 < q')
    (hR : HRS.MS.Gap.GapRef d ρβ q' B) : Integrable (fun x => Real.sqrt (ρβ x)) := by
  obtain ⟨-, -, c, hc, hb⟩ := HRS.MS.Mov0.mv0_sqrt_gauss hq hR
  obtain ⟨C, hb0⟩ := hb 0
  obtain ⟨P, hP, hPb⟩ := HRS.MS.Thm.rege_poly_gauss_bdd hc (d + 1)
  have hint : Integrable (fun x : Euc d => (1 + ‖x‖) ^ (-((d : ℝ) + 1))) :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; linarith)
  refine (hint.const_mul (C * P)).mono' (hR.smooth.continuous.sqrt.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have h1 := hb0 x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
  have h2 := hPb ‖x‖ (norm_nonneg _)
  have hpos : 0 < (1 + ‖x‖) := by positivity
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans h1
    have he : 0 < Real.exp (-c * ‖x‖ ^ 2) := Real.exp_pos _
    by_contra hneg
    push Not at hneg
    nlinarith
  have h3 : (1 + ‖x‖) ^ (-((d : ℝ) + 1)) * (1 + ‖x‖) ^ ((d + 1 : ℕ) : ℝ) = 1 := by
    rw [← Real.rpow_add hpos]; push_cast; ring_nf; simp
  have h4 : (1 + ‖x‖) ^ ((d + 1 : ℕ) : ℝ) = (1 + ‖x‖) ^ (d + 1) := Real.rpow_natCast _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h5 : Real.exp (-c * ‖x‖ ^ 2) ≤ P * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by
    have hpw : 0 < (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := Real.rpow_pos_of_pos hpos _
    have : (1 + ‖x‖) ^ (-((d : ℝ) + 1)) * ((1 + ‖x‖) ^ (d + 1) * Real.exp (-c * ‖x‖ ^ 2)) ≤
        (1 + ‖x‖) ^ (-((d : ℝ) + 1)) * P := mul_le_mul_of_nonneg_left h2 hpw.le
    rw [← mul_assoc, ← h4, h3, one_mul] at this
    linarith
  calc Real.sqrt (ρβ x) ≤ C * Real.exp (-c * ‖x‖ ^ 2) := (le_abs_self _).trans h1
    _ ≤ C * (P * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := mul_le_mul_of_nonneg_left h5 hC
    _ = C * P * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by ring

theorem s104e_weak_cont (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {εstar ε c₁ C₁ : ℝ} {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ)
    {ψ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ} (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ)
    {f : Euc d → ℝ} (hf : Continuous f) (hB : ∃ B : ℝ, ∀ x, |f x| ≤ B) :
    ContinuousOn (fun r => ∫ x, f x * ρ r x) (Ici 0) := by
  obtain ⟨B, hBdef, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd ha hβ hρβ
  have hq : 0 < β * a := mul_pos hβ ha
  have hpos : ∀ x, 0 < ρβ x := hR.pos
  have hρβc : Continuous ρβ := hR.smooth.continuous
  obtain ⟨Bf, hBf⟩ := hB
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 102 * d + 1020 := ⟨_, rfl⟩
  have hmR : (m : ℝ) = 102 * (d : ℝ) + 1020 := by rw [hm]; push_cast; ring
  have hm1 : (d : ℝ) / 2 + ((0 : ℕ) : ℝ) + 2 < m := by
    rw [hmR]; push_cast; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  obtain ⟨Cv, hCv0, hCv⟩ := mn_force_bound hd hs0 hsd β a hβ ha ρβ hρβ 0 m hm1
  have hsI := s104e_sqrt_integrable hq hR
  have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf 0)
  set v : ℝ → Euc d → ℝ := fun t x => (ρ t x - ρβ x) / Real.sqrt (ρβ x) with hv
  have hvc : ∀ t, 0 ≤ t → Continuous (v t) := fun t ht =>
    ((hres.regular t ht).sub hρβc).div hρβc.sqrt (fun x => (Real.sqrt_pos.2 (hpos x)).ne')
  have hvm : ∀ t, 0 ≤ t → MemOsc (m : ℝ) (v t) := fun t ht => by
    rw [hmR]; exact (hres.weighted t ht).1
  have hrho : ∀ t x, ρ t x = ρβ x + Real.sqrt (ρβ x) * v t x := fun t x => by
    have hsq : 0 < Real.sqrt (ρβ x) := Real.sqrt_pos.2 (hpos x)
    simp only [hv]; field_simp; ring
  have hcont : ContinuousOn (fun t : ℝ => OscSpace.ofFun (d := d) (m : ℝ) (v t)) (Ici 0) := by
    rw [hmR]; exact hres.cont
  have hint : ∀ t, 0 ≤ t → Integrable (fun x => f x * ρ t x) := fun t ht =>
    (s104e_probInt ((hres.global t).density t (Set.mem_Icc.2 ⟨ht, le_rfl⟩))).bdd_mul
      hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hBf x)
  intro r₀ hr₀
  have hr₀' : (0 : ℝ) ≤ r₀ := hr₀
  have hbound : ∀ r : ℝ, 0 ≤ r → ‖(∫ x, f x * ρ r x) - ∫ x, f x * ρ r₀ x‖ ≤
      (Bf * Cv * ∫ x, Real.sqrt (ρβ x)) * dist (OscSpace.ofFun (d := d) (m : ℝ) (v r))
        (OscSpace.ofFun (d := d) (m : ℝ) (v r₀)) := by
    intro r hr
    set D := dist (OscSpace.ofFun (d := d) (m : ℝ) (v r)) (OscSpace.ofFun (d := d) (m : ℝ) (v r₀)) with hD
    have hwm := HRS.MS.MovLin.mov2d_memOsc_sub (hvm r hr) (hvm r₀ hr₀')
    have hwc : Continuous (fun z => v r z - v r₀ z) := (hvc r hr).sub (hvc r₀ hr₀')
    have hDn : oscNorm (m : ℝ) (fun z => v r z - v r₀ z) = D := by
      rw [hD, dist_eq_norm, ← HRS.MS.MovLin.mov2d_ofFun_sub (hvm r hr) (hvm r₀ hr₀'),
        OscSpace.norm_ofFun _ hwm]
    obtain ⟨-, hsup, -⟩ := hCv _ hwc hwm
    have hpt : ∀ x, |v r x - v r₀ x| ≤ Cv * D := fun x => by
      have := hsup 0 (by omega) x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, hDn] at this
      exact this
    rw [← integral_sub (hint r hr) (hint r₀ hr₀')]
    have hD0 : 0 ≤ D := dist_nonneg
    have hgi : Integrable (fun x => (Bf * (Cv * D)) * Real.sqrt (ρβ x)) := hsI.const_mul _
    refine (norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun x => ?_)).trans ?_
    · have hdiff : ρ r x - ρ r₀ x = Real.sqrt (ρβ x) * (v r x - v r₀ x) := by
        rw [hrho r x, hrho r₀ x]; ring
      have : f x * ρ r x - f x * ρ r₀ x = f x * (Real.sqrt (ρβ x) * (v r x - v r₀ x)) := by
        rw [← hdiff]; ring
      rw [this, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have h1 := hBf x
      have h2 := hpt x
      have hs0' := Real.sqrt_nonneg (ρβ x)
      calc |f x| * (Real.sqrt (ρβ x) * |v r x - v r₀ x|)
          ≤ Bf * (Real.sqrt (ρβ x) * (Cv * D)) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hs0') (by positivity) hBf0
        _ = Bf * (Cv * D) * Real.sqrt (ρβ x) := by ring
    · rw [integral_const_mul]
      have : Bf * (Cv * D) * ∫ x, Real.sqrt (ρβ x) = (Bf * Cv * ∫ x, Real.sqrt (ρβ x)) * D := by ring
      exact this.le
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  have hD := tendsto_iff_dist_tendsto_zero.1 (hcont r₀ hr₀)
  have hK : Tendsto (fun r => (Bf * Cv * ∫ x, Real.sqrt (ρβ x)) *
      dist (OscSpace.ofFun (d := d) (m : ℝ) (v r)) (OscSpace.ofFun (d := d) (m : ℝ) (v r₀)))
      (𝓝[Ici 0] r₀) (𝓝 0) := by
    simpa using hD.const_mul (Bf * Cv * ∫ x, Real.sqrt (ρβ x))
  refine squeeze_zero' (Filter.Eventually.of_forall fun r => dist_nonneg) ?_ hK
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [dist_eq_norm]
  exact hbound r hr

end HRS.MS.S104e
