import Mathlib

/-!
# SA1, Aux1: global Gagliardo-Nirenberg-Sobolev inequality (no compact support)

Part of the proof of the S.A.1 embeddings (`HRS.Whole.DecayingDensity.sobolev_embeds_cb`, `h_embeds_sobolev`; Definition S.A.1,
last sentence; claim 2 `commutatorNorm_le` is tied from `HRS/MS/S1c2Tie.lean`).  Plan:

* Both embeddings are one-derivative ladders `W^{1,a} → L^r` (`SobEmbAux2`: step, `SobEmbAux3`: interpolation and ladder,
  `SobEmbAux4`: conversion to `sobolevWNorm`), plus a Morrey estimate `W^{1,q} → L^∞`, `q > d` (`SobEmbAux5`) and its glue
  (`SobEmbAux6`); `SobEmbTie` has the `type_of%` ties.  No Fourier analysis is used.
* Truth/junk audit: all three frozen statements are true as stated.  The integrability hypotheses make the Bochner integrals in
  `sobolevWNorm` genuine; the real `iSup`s of `cbNorm` are bounded by a genuine pointwise bound; claim 3's conclusion integrals are
  proved integrable.
* Mathlib proves the Gagliardo-Nirenberg-Sobolev inequality `‖u‖_{q*} ≤ K ‖Du‖_q` only for compactly supported `C¹` `u`
  (`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`).  This file removes the compact support: for `C¹` `v` with `v, Dv ∈ L^q`,
  `1 ≤ q < d`, the cutoffs `χ(·/R) v` are admissible, `‖D(χ_R v)‖_q ≤ ‖Dv‖_q + (L/R)‖v‖_q`, and Fatou's lemma gives
  `‖v‖_{q*} ≤ K ‖Dv‖_q`.

Main result: `sa1_gns_global`.
-/

noncomputable section

open MeasureTheory Filter Topology Module
open scoped ENNReal NNReal ContDiff

namespace HRS.SA1

variable {d : ℕ}

/-- A fixed smooth cutoff, equal to `1` near `0`, with values in `[0,1]` and compact support. -/
def sa1_bump : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := ⟨1, 2, one_pos, one_lt_two⟩

theorem sa1_bump_contDiff : ContDiff ℝ ∞ (sa1_bump (d := d)) := sa1_bump.contDiff

theorem sa1_bump_zero : (sa1_bump (d := d)) 0 = 1 :=
  sa1_bump.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)

/-- The rescaled cutoff `x ↦ χ(x/(n+1))`. -/
def sa1_cut (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sa1_bump (((n : ℝ) + 1)⁻¹ • x)

theorem sa1_cut_contDiff (n : ℕ) : ContDiff ℝ ∞ (sa1_cut (d := d) n) :=
  sa1_bump_contDiff.comp (contDiff_const_smul _)

theorem sa1_cut_nonneg (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ sa1_cut n x :=
  sa1_bump.nonneg

theorem sa1_cut_le_one (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : sa1_cut n x ≤ 1 :=
  sa1_bump.le_one

theorem sa1_cut_hasCompactSupport (n : ℕ) : HasCompactSupport (sa1_cut (d := d) n) := by
  have h := sa1_bump.hasCompactSupport (c := (0 : EuclideanSpace ℝ (Fin d)))
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  let e : EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d) :=
    Homeomorph.smulOfNeZero ((n : ℝ) + 1)⁻¹ (inv_ne_zero hn)
  exact h.comp_homeomorph e

theorem sa1_cut_tendsto (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun n : ℕ => sa1_cut n x) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹) • x) atTop (𝓝 ((0 : ℝ) • x)) := by
    refine Tendsto.smul_const ?_ x
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  rw [zero_smul] at h1
  have h2 := (sa1_bump_contDiff (d := d)).continuous.tendsto 0
  rw [sa1_bump_zero] at h2
  exact h2.comp h1

/-- Uniform bound for the derivative of the cutoffs: `‖Dχ_n‖ ≤ B/(n+1)`. -/
theorem sa1_cut_fderiv_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin d)),
    ‖fderiv ℝ (sa1_cut n) x‖ ≤ B / ((n : ℝ) + 1) := by
  have h1 : ContDiff ℝ ∞ (sa1_bump (d := d)) := sa1_bump_contDiff
  obtain ⟨B, hB⟩ := ((sa1_bump.hasCompactSupport (c := (0 : EuclideanSpace ℝ (Fin d)))).fderiv ℝ).exists_bound_of_continuous
    (h1.continuous_fderiv (by simp))
  refine ⟨max B 0, le_max_right _ _, fun n x => ?_⟩
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hd : HasFDerivAt (sa1_cut (d := d) n)
      ((fderiv ℝ (sa1_bump (d := d)) (((n : ℝ) + 1)⁻¹ • x)).comp
        (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))) x := by
    have h2 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin d) => ((n : ℝ) + 1)⁻¹ • x)
        (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) x :=
      ((((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))).hasFDerivAt (x := x))
    exact ((h1.differentiable (by simp)) _).hasFDerivAt.comp x h2
  rw [hd.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h3 : ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))‖ ≤ ((n : ℝ) + 1)⁻¹ := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d))
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [inv_pos.2 hn]
  calc ‖fderiv ℝ (sa1_bump (d := d)) (((n : ℝ) + 1)⁻¹ • x)‖ *
        ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))‖
      ≤ max B 0 * ((n : ℝ) + 1)⁻¹ :=
        mul_le_mul ((hB _).trans (le_max_left _ _)) h3 (norm_nonneg _) (le_max_right _ _)
    _ = max B 0 / ((n : ℝ) + 1) := by rw [div_eq_mul_inv]


/-- **Global Gagliardo-Nirenberg-Sobolev inequality.**  For `1 ≤ q < d` and `q'⁻¹ = q⁻¹ - d⁻¹` there is a constant `K` with
`‖v‖_{q'} ≤ K ‖Dv‖_q` for every `C¹` function `v` with `v ∈ L^q` (no compact support, no finiteness of `‖Dv‖_q` needed:
the bound is trivial if it is infinite). -/
theorem sa1_gns_global {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {q q' : ℝ≥0} (hq : 1 ≤ q) (hqd : (q : ℝ) < d)
    (hq' : (q' : ℝ)⁻¹ = (q : ℝ)⁻¹ - (d : ℝ)⁻¹) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ v : EuclideanSpace ℝ (Fin d) → F, ContDiff ℝ 1 v →
      eLpNorm v q volume < ⊤ → eLpNorm v q' volume ≤ K * eLpNorm (fderiv ℝ v) q volume := by
  have hdpos : (0 : ℝ) < d := lt_of_le_of_lt (by exact_mod_cast zero_le_one.trans hq) hqd
  have hd0 : 0 < d := by exact_mod_cast hdpos
  have hfr : (finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) = d := by simp
  have hq'pos : q' ≠ 0 := by
    intro h
    rw [h] at hq'
    have : (q : ℝ)⁻¹ - (d : ℝ)⁻¹ > 0 := by
      have h1 : (d : ℝ)⁻¹ < (q : ℝ)⁻¹ := inv_strictAnti₀ (by exact_mod_cast zero_lt_one.trans_le hq) hqd
      linarith
    simp at hq'
    linarith
  obtain ⟨B, hB0, hB⟩ := sa1_cut_fderiv_bound (d := d)
  set K0 : ℝ≥0 := SNormLESNormFDerivOfEqConst F (volume : Measure (EuclideanSpace ℝ (Fin d))) q with hK0
  refine ⟨K0 + 1, by positivity, fun v hv hvq => ?_⟩
  by_cases hDv : eLpNorm (fderiv ℝ v) q volume = ⊤
  · rw [hDv, ENNReal.mul_top (by simp)]
    exact le_top
  have hvc : Continuous v := hv.continuous
  have hdv : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by simp)
  have hqq : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by exact_mod_cast hq
  -- the cutoff functions
  set w : ℕ → EuclideanSpace ℝ (Fin d) → F := fun n x => sa1_cut n x • v x with hw
  have hw_cd : ∀ n, ContDiff ℝ 1 (w n) := fun n =>
    ((sa1_cut_contDiff n).of_le (by simp)).smul hv
  have hw_cs : ∀ n, HasCompactSupport (w n) := fun n => (sa1_cut_hasCompactSupport n).smul_right
  have hw_meas : ∀ n, AEStronglyMeasurable (w n) volume := fun n => (hw_cd n).continuous.aestronglyMeasurable
  have hfd : ∀ n x, ‖fderiv ℝ (w n) x‖ ≤ ‖fderiv ℝ v x‖ + (B / ((n : ℝ) + 1)) * ‖v x‖ := by
    intro n x
    have hc : DifferentiableAt ℝ (sa1_cut (d := d) n) x :=
      ((sa1_cut_contDiff n).differentiable (by simp)) x
    have hv' : DifferentiableAt ℝ v x := (hv.differentiable (by simp)) x
    have : fderiv ℝ (w n) x = sa1_cut n x • fderiv ℝ v x + (fderiv ℝ (sa1_cut n) x).smulRight (v x) :=
      fderiv_smul hc hv'
    rw [this]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_of_nonneg (sa1_cut_nonneg n x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (sa1_cut_le_one n x)
    · rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right (hB n x) (norm_nonneg (v x))
  have hE1 : ∀ n, eLpNorm (w n) q' volume ≤ (K0 : ℝ≥0∞) * eLpNorm (fderiv ℝ (w n)) q volume := fun n => by
    have := eLpNorm_le_eLpNorm_fderiv_of_eq (volume : Measure (EuclideanSpace ℝ (Fin d))) (hw_cd n) (hw_cs n)
      (p := q) (p' := q') hq (by rw [finrank_euclideanSpace_fin]; exact hd0) (by rw [hfr]; exact hq')
    exact this
  have hE2 : ∀ n, eLpNorm (fderiv ℝ (w n)) q volume ≤
      eLpNorm (fderiv ℝ v) q volume + ENNReal.ofReal (B / ((n : ℝ) + 1)) * eLpNorm v q volume := by
    intro n
    have hmeas : AEStronglyMeasurable (fderiv ℝ (w n)) volume :=
      ((hw_cd n).continuous_fderiv (by simp)).aestronglyMeasurable
    have h1 : eLpNorm (fderiv ℝ (w n)) q volume ≤ eLpNorm ((fun x => ‖fderiv ℝ v x‖) +
        ((B / ((n : ℝ) + 1)) • fun x => ‖v x‖)) q volume :=
      eLpNorm_mono_real hmeas (fun x => by simpa [Pi.add_apply, smul_eq_mul] using hfd n x)
    refine h1.trans ((eLpNorm_add_le hqq).trans ?_)
    rw [eLpNorm_const_smul, eLpNorm_norm _ hdv.aestronglyMeasurable, eLpNorm_norm _ hvc.aestronglyMeasurable,
      Real.enorm_eq_ofReal (by positivity)]
  have hlim : eLpNorm v q' volume ≤ liminf (fun n => eLpNorm (w n) q' volume) atTop := by
    have hq'0 : (0 : ℝ) < q' := by exact_mod_cast pos_iff_ne_zero.2 hq'pos
    have h := MeasureTheory.Lp.eLpNorm'_lim_le_liminf_eLpNorm' (μ := volume) hq'0 hw_meas (f_lim := v)
      (Eventually.of_forall fun x => by
        have := (sa1_cut_tendsto (d := d) x).smul_const (v x)
        simpa [hw] using this)
    rw [eLpNorm_nnreal_eq_eLpNorm' hq'pos hvc.aestronglyMeasurable]
    refine h.trans (le_of_eq ?_)
    congr 1
    funext n
    exact (eLpNorm_nnreal_eq_eLpNorm' hq'pos (hw_meas n)).symm
  have hb : Tendsto (fun n : ℕ => (K0 : ℝ≥0∞) * (eLpNorm (fderiv ℝ v) q volume +
      ENNReal.ofReal (B / ((n : ℝ) + 1)) * eLpNorm v q volume)) atTop
      (𝓝 ((K0 : ℝ≥0∞) * eLpNorm (fderiv ℝ v) q volume)) := by
    have h0 : Tendsto (fun n : ℕ => B / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul B
      simpa [div_eq_mul_inv] using this
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (B / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h0
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hvq.ne)
    rw [zero_mul] at h2
    have h3 := (tendsto_const_nhds (x := eLpNorm (fderiv ℝ v) q volume)).add h2
    rw [add_zero] at h3
    exact ENNReal.Tendsto.const_mul h3 (Or.inr ENNReal.coe_ne_top)
  calc eLpNorm v q' volume ≤ liminf (fun n => eLpNorm (w n) q' volume) atTop := hlim
    _ ≤ liminf (fun n : ℕ => (K0 : ℝ≥0∞) * (eLpNorm (fderiv ℝ v) q volume +
        ENNReal.ofReal (B / ((n : ℝ) + 1)) * eLpNorm v q volume)) atTop := by
        refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
        exact (hE1 n).trans (by gcongr; exact hE2 n)
    _ = (K0 : ℝ≥0∞) * eLpNorm (fderiv ℝ v) q volume := hb.liminf_eq
    _ ≤ ((K0 + 1 : ℝ≥0) : ℝ≥0∞) * eLpNorm (fderiv ℝ v) q volume := by
        gcongr
        exact_mod_cast le_add_of_nonneg_right zero_le_one

end HRS.SA1
