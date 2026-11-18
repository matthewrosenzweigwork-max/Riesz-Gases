import HRS.MS.S16FracAux2
import HRS.Commutator.Whole.LocalAuxKR
import HRS.MH.ScreenedS3
import HRS.MS.CzPvAux2

/-!
# S16-FRAC, part 3: `Δg * u = -c Λ^θ u` (input E3 of S.A.16)

Packet S16-FRAC (`docs/CZ_PLAN.md`, row S16-FRAC).  Notation as in `S16FracAux2`: `d ≥ 1`, `0 ≤ s < d`,
`g = rieszKernel d s`, `θ = s + 2 - d`; `θ ∈ (0, 2)` is exactly the range `0 < s + 2 - d` (and `θ < 2` is
`s < d`).  The identification `Δ|x|^{-s} = s θ |x|^{-s-2}` (finite part) with `Λ^θ` is stated in the only meaningful
non-junk form: for a real Schwartz function `u`,

* `s16frac_lap_fracLap` (**main**): there is `c > 0` (depending only on `d, s`) such that for every real Schwartz
  `u` and every `x`,
  `∑_i ∂_i ∂_i (g * u)(x) = -c · fracLap d θ u x`,
  where the left side is the Laplacian of the convolution `convFun g u` (iterated Fréchet derivatives, all of which
  exist by `S16FracAux2`; equal to `g * Δu` by `s16frac_lap_conv`) and `fracLap` is the frozen singular-integral
  `Λ^θ` of `HRS.Whole.AppendixA` (no normalising constant).  `s16frac_lap_fracSym` is the same with
  `s16frac_fracSym`, the absolutely convergent symmetrised integral `∫ (2u(x)-u(x-z)-u(x+z))/2 |z|^{-d-θ} dz`
  (equal to `fracLap` by `HRS.CZ.Pv.fracLap_eq_symm`).
  The constant is not computed (`c = (2π)² c₁ / C₀`, `c₁ > 0` the constant of `kg_fourier_h_proof`, `C₀ > 0`
  of `s16frac_C0`); by the distributional identity `Δ|x|^{-s} = s (s+2-d) f.p. |x|^{-s-2}` one expects `c = s (s+2-d)` up to the omitted
  normalisation of `fracLap` (not proved here; only `c > 0` is).
* Proof: Fourier side.  `g * ∂_i φ` has symbol `c₁ (2π ξ_i) |ξ|^{s-d} i 𝓕φ` (`kg_fourier_h_proof`, from
  `riesz_potential_fourier`), hence `g * Δu (x) = -(2π)² c₁ ∫ |ξ|^θ 𝓕u(ξ) e^{2πi x·ξ} dξ`
  (`s16frac_lap_fourier`); on the other side Fourier inversion and Fubini give
  `fracSym u (x) = C₀ ∫ |ξ|^θ 𝓕u(ξ) e^{2πi x·ξ} dξ` (`s16frac_fracSym_fourier`) with
  `C₀ = ∫ (1 - cos(2π z·e)) |z|^{-d-θ} dz`, and `∫ (1 - cos(2π z·ξ)) |z|^{-d-θ} dz = C₀ |ξ|^θ` by scaling and a
  reflection (`s16frac_h_integral`; no polar coordinates).
* `s = 0` is included (`g = -log|x|`, then `d = 1`, `θ = 1`).

Nothing is assumed beyond `1 ≤ d`, `0 ≤ s < d`, `0 < s + 2 - d`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff FourierTransform SchwartzMap

noncomputable section

namespace HRS.S16Frac

open HRS.Whole HRS.S16Cze HRS.MH.Screened

variable {d : ℕ} {s : ℝ}

lemma s16frac_integrableOn_ball_rpow (hd : 1 ≤ d) {α : ℝ} (hα : α < d) (r : ℝ) :
    IntegrableOn (fun z : Euc d => ‖z‖ ^ (-α)) (ball 0 r) := by
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) (f := fun z : Euc d => ‖z‖ ^ (-α)) (C := 1)
    (α := α) (r := r) (by rw [finrank_euclideanSpace_fin]; exact hd)
    (by rw [finrank_euclideanSpace_fin]; exact hα) (Eventually.of_forall fun x => ?_)
    (measurable_norm.pow_const _).aestronglyMeasurable
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]

lemma s16frac_integrableOn_tail_rpow (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s) :
    IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) {z : Euc d | 1 < ‖z‖} := by
  have hS : MeasurableSet {z : Euc d | 1 < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have h := integrable_one_add_norm (E := Euc d) (μ := volume) (r := s)
    (by rw [finrank_euclideanSpace_fin]; exact hs)
  refine Integrable.mono' (h.const_mul ((2 : ℝ) ^ s)).integrableOn
    (measurable_norm.pow_const _).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' hS).2 (ae_of_all _ fun z hz => ?_)
  have hz1 : 1 < ‖z‖ := hz
  have hn : 0 < ‖z‖ := by linarith
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hn.le _)]
  have h1 : (2 * ‖z‖) ^ (-s) ≤ (1 + ‖z‖) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have h2 : (2 * ‖z‖) ^ (-s) = (2 : ℝ) ^ (-s) * ‖z‖ ^ (-s) := Real.mul_rpow (by norm_num) hn.le
  have h3 : (2 : ℝ) ^ s * (2 : ℝ) ^ (-s) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have h4 : ‖z‖ ^ (-s) = (2 : ℝ) ^ s * ((2 : ℝ) ^ (-s) * ‖z‖ ^ (-s)) := by
    rw [← mul_assoc, h3, one_mul]
  rw [h4, ← h2]
  exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by norm_num) _)

/-- the second-difference kernel `(1 - cos(2π z·ξ)) |z|^{-(d+θ)}` -/
def s16frac_h (d : ℕ) (θ : ℝ) (ξ z : Euc d) : ℝ :=
  (1 - Real.cos (2 * Real.pi * inner ℝ z ξ)) * ‖z‖ ^ (-((d : ℝ) + θ))

lemma s16frac_h_nonneg (θ : ℝ) (ξ z : Euc d) : 0 ≤ s16frac_h d θ ξ z := by
  unfold s16frac_h
  exact mul_nonneg (by linarith [Real.cos_le_one (2 * Real.pi * inner ℝ z ξ)])
    (Real.rpow_nonneg (norm_nonneg _) _)

lemma s16frac_h_meas (θ : ℝ) (ξ : Euc d) : Measurable (s16frac_h d θ ξ) := by
  unfold s16frac_h
  have : Measurable fun z : Euc d => inner ℝ z ξ := by fun_prop
  exact (measurable_const.sub (Real.measurable_cos.comp (measurable_const.mul this))).mul
    (measurable_norm.pow_const _)

lemma s16frac_h_le_ball (θ : ℝ) (ξ z : Euc d) (hz : z ≠ 0) :
    s16frac_h d θ ξ z ≤ (2 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * ‖z‖ ^ (-((d : ℝ) + θ - 2)) := by
  unfold s16frac_h
  have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h1 := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * inner ℝ z ξ)
  have h2 : |inner ℝ z ξ| ≤ ‖z‖ * ‖ξ‖ := abs_real_inner_le_norm z ξ
  have h3 : (inner ℝ z ξ) ^ 2 ≤ (‖z‖ * ‖ξ‖) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h4 : 1 - Real.cos (2 * Real.pi * inner ℝ z ξ) ≤ 2 * Real.pi ^ 2 * (‖z‖ ^ 2 * ‖ξ‖ ^ 2) := by
    nlinarith [sq_nonneg Real.pi]
  have h5 : ‖z‖ ^ (-((d : ℝ) + θ - 2)) = ‖z‖ ^ 2 * ‖z‖ ^ (-((d : ℝ) + θ)) := by
    rw [show -((d : ℝ) + θ - 2) = 2 + -((d : ℝ) + θ) by ring, Real.rpow_add hzp, Real.rpow_two]
  rw [h5]
  have hp : 0 ≤ ‖z‖ ^ (-((d : ℝ) + θ)) := Real.rpow_nonneg hzp.le _
  calc (1 - Real.cos (2 * Real.pi * inner ℝ z ξ)) * ‖z‖ ^ (-((d : ℝ) + θ))
      ≤ (2 * Real.pi ^ 2 * (‖z‖ ^ 2 * ‖ξ‖ ^ 2)) * ‖z‖ ^ (-((d : ℝ) + θ)) := by gcongr
    _ = _ := by ring

lemma s16frac_h_le_tail (θ : ℝ) (ξ z : Euc d) :
    s16frac_h d θ ξ z ≤ 2 * ‖z‖ ^ (-((d : ℝ) + θ)) := by
  unfold s16frac_h
  have hp : 0 ≤ ‖z‖ ^ (-((d : ℝ) + θ)) := Real.rpow_nonneg (norm_nonneg _) _
  have := Real.neg_one_le_cos (2 * Real.pi * inner ℝ z ξ)
  nlinarith

lemma s16frac_h_integrable (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (ξ : Euc d) :
    Integrable (s16frac_h d θ ξ) := by
  have hm : AEStronglyMeasurable (s16frac_h d θ ξ) volume :=
    (s16frac_h_meas (d := d) θ ξ).aestronglyMeasurable
  have hcover : (ball (0 : Euc d) 2 ∪ {z : Euc d | 1 < ‖z‖}) = univ := by
    ext z; simp only [mem_union, mem_ball_zero_iff, mem_setOf_eq, mem_univ, iff_true]
    by_cases h : ‖z‖ < 2
    · exact Or.inl h
    · exact Or.inr (by linarith [not_lt.1 h])
  have h1 : IntegrableOn (s16frac_h d θ ξ) (ball 0 2) := by
    have hb := (s16frac_integrableOn_ball_rpow (d := d) hd (α := (d : ℝ) + θ - 2) (by linarith) 2).const_mul
      (2 * Real.pi ^ 2 * ‖ξ‖ ^ 2)
    refine hb.mono' hm.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_ball fun z _ => ?_
    by_cases hz : z = 0
    · subst hz
      have : s16frac_h d θ ξ 0 = 0 := by simp [s16frac_h]
      rw [this]; simp only [norm_zero]
      positivity
    · rw [Real.norm_of_nonneg (s16frac_h_nonneg θ ξ z)]
      exact s16frac_h_le_ball θ ξ z hz
  have h2 : IntegrableOn (s16frac_h d θ ξ) {z : Euc d | 1 < ‖z‖} := by
    have hb := (s16frac_integrableOn_tail_rpow (d := d) hd (s := (d : ℝ) + θ) (by linarith)).const_mul 2
    refine hb.mono' hm.restrict ?_
    refine ae_restrict_of_forall_mem (measurableSet_lt measurable_const measurable_norm) fun z _ => ?_
    rw [Real.norm_of_nonneg (s16frac_h_nonneg θ ξ z)]
    exact s16frac_h_le_tail θ ξ z
  have := h1.union h2
  rwa [hcover, integrableOn_univ] at this

/-- the constant `C₀ = ∫ (1 - cos(2π z·e)) |z|^{-d-θ} dz` for the unit vector `e = e_{i0}` -/
def s16frac_C0 (i0 : Fin d) (θ : ℝ) : ℝ :=
  ∫ z : Euc d, s16frac_h d θ (EuclideanSpace.single i0 (1 : ℝ)) z

lemma s16frac_h_zero (θ : ℝ) (z : Euc d) : s16frac_h d θ 0 z = 0 := by
  simp [s16frac_h]

/-- scaling: `h (r w0) z = r^{d+θ} h w0 (r z)` -/
lemma s16frac_h_scale (θ : ℝ) {r : ℝ} (hr : 0 < r) (w0 z : Euc d) :
    s16frac_h d θ (r • w0) z = r ^ ((d : ℝ) + θ) * s16frac_h d θ w0 (r • z) := by
  unfold s16frac_h
  have h1 : inner ℝ z (r • w0) = inner ℝ (r • z) w0 := by
    rw [real_inner_smul_right, real_inner_smul_left]
  rw [h1, norm_smul, Real.norm_of_nonneg hr.le]
  by_cases hz : z = 0
  · subst hz; simp
  have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [Real.mul_rpow hr.le hzp.le]
  have key : r ^ ((d : ℝ) + θ) * r ^ (-((d : ℝ) + θ)) = 1 := by
    rw [← Real.rpow_add hr]; simp
  generalize r ^ ((d : ℝ) + θ) = A at key ⊢
  generalize r ^ (-((d : ℝ) + θ)) = B at key ⊢
  generalize (1 - Real.cos (2 * Real.pi * inner ℝ (r • z) w0)) = X
  generalize ‖z‖ ^ (-((d : ℝ) + θ)) = Z
  linear_combination (-(X * Z)) * key

/-- rotation invariance for unit vectors -/
lemma s16frac_h_rot (i0 : Fin d) (θ : ℝ) {w0 : Euc d} (hw0 : ‖w0‖ = 1) :
    ∫ z : Euc d, s16frac_h d θ w0 z = s16frac_C0 i0 θ := by
  have hn : ‖w0‖ = ‖EuclideanSpace.single i0 (1 : ℝ)‖ := by simp [hw0]
  set T : Euc d ≃ₗᵢ[ℝ] Euc d := Submodule.reflection (ℝ ∙ (w0 - EuclideanSpace.single i0 (1 : ℝ)))ᗮ with hT
  have hTw0 : T w0 = EuclideanSpace.single i0 (1 : ℝ) := Submodule.reflection_sub hn
  have hpt : ∀ z, s16frac_h d θ w0 z = s16frac_h d θ (EuclideanSpace.single i0 (1 : ℝ)) (T z) := by
    intro z
    unfold s16frac_h
    rw [← hTw0, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map]
  simp_rw [hpt]
  unfold s16frac_C0
  exact T.measurePreserving.integral_comp T.toHomeomorph.measurableEmbedding _

lemma s16frac_h_integral (hd : 1 ≤ d) (i0 : Fin d) {θ : ℝ} (hθ0 : 0 < θ) (ξ : Euc d) :
    ∫ z : Euc d, s16frac_h d θ ξ z = s16frac_C0 i0 θ * ‖ξ‖ ^ θ := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [s16frac_h_zero, hθ0.ne']
  have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set w0 : Euc d := ‖ξ‖⁻¹ • ξ with hw0
  have hw0n : ‖w0‖ = 1 := by
    rw [hw0, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  have hξw0 : ξ = ‖ξ‖ • w0 := by
    rw [hw0, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have h1 : ∀ z, s16frac_h d θ ξ z = ‖ξ‖ ^ ((d : ℝ) + θ) * s16frac_h d θ w0 (‖ξ‖ • z) := by
    intro z
    conv_lhs => rw [hξw0]
    exact s16frac_h_scale θ hr w0 z
  simp_rw [h1]
  rw [integral_const_mul, Measure.integral_comp_smul (volume : Measure (Euc d))
    (fun z => s16frac_h d θ w0 z) ‖ξ‖, s16frac_h_rot i0 θ hw0n, finrank_euclideanSpace_fin,
    smul_eq_mul]
  have e1 : |((‖ξ‖ ^ d)⁻¹ : ℝ)| = (‖ξ‖ ^ (d : ℝ))⁻¹ := by
    rw [abs_of_nonneg (by positivity), Real.rpow_natCast]
  have e2 : ‖ξ‖ ^ ((d : ℝ) + θ) = ‖ξ‖ ^ (d : ℝ) * ‖ξ‖ ^ θ := Real.rpow_add hr _ _
  have e3 : ‖ξ‖ ^ (d : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  rw [e1, e2]
  field_simp

lemma s16frac_C0_pos (hd : 1 ≤ d) (i0 : Fin d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) :
    0 < s16frac_C0 i0 θ := by
  have hi := s16frac_h_integrable hd hθ0 hθ2 (EuclideanSpace.single i0 (1 : ℝ))
  unfold s16frac_C0
  rw [integral_pos_iff_support_of_nonneg (fun z => s16frac_h_nonneg θ _ z) hi]
  -- the support contains the open set `{0 < z i0 < 1}`
  have hopen : IsOpen {z : Euc d | 0 < z i0 ∧ z i0 < 1} := by
    have hc : Continuous fun z : Euc d => z i0 := by fun_prop
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have hne : ({z : Euc d | 0 < z i0 ∧ z i0 < 1}).Nonempty :=
    ⟨(1 / 2 : ℝ) • EuclideanSpace.single i0 (1 : ℝ), by simp; norm_num⟩
  have hsub : {z : Euc d | 0 < z i0 ∧ z i0 < 1} ⊆
      Function.support (s16frac_h d θ (EuclideanSpace.single i0 (1 : ℝ))) := by
    intro z hz
    obtain ⟨hz0, hz1⟩ := hz
    have hzn : z ≠ 0 := by
      intro h; rw [h] at hz0; simp at hz0
    have hzp : 0 < ‖z‖ := norm_pos_iff.2 hzn
    have hin : inner ℝ z (EuclideanSpace.single i0 (1 : ℝ)) = z i0 := by
      simp [EuclideanSpace.inner_single_right]
    simp only [Function.mem_support, s16frac_h, hin]
    refine mul_ne_zero ?_ (Real.rpow_pos_of_pos hzp _).ne'
    have : Real.cos (2 * Real.pi * z i0) ≠ 1 := by
      intro h
      have := (Real.cos_eq_one_iff_of_lt_of_lt (x := 2 * Real.pi * z i0)
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])).1 h
      have : z i0 = 0 := by
        have := Real.pi_pos
        nlinarith
      linarith
    intro h; apply this; linarith
  exact lt_of_lt_of_le (hopen.measure_pos volume hne) (measure_mono hsub)

/-! ### Fourier representation of `g * Δ u` -/

/-- Fourier transform of a coordinate derivative -/
lemma s16frac_ft_pd (u : 𝓢(Euc d, ℝ)) (j : Fin d) (ξ : Euc d) :
    𝓕 (fun y : Euc d => ((s16cze_pd u j y : ℝ) : ℂ)) ξ =
      (2 * Real.pi * Complex.I * (ξ j : ℂ)) * 𝓕 (fun y : Euc d => ((u y : ℝ) : ℂ)) ξ := by
  have hF := HRS.Commutator.Whole.cmxMY_fourier_partial (s3Cx u) j ξ
  have hD : (fun ζ : Euc d => fderiv ℝ (s3Cx u) ζ (EuclideanSpace.single j (1 : ℝ))) =
      fun y : Euc d => ((s16cze_pd u j y : ℝ) : ℂ) := by
    funext ζ
    have h1 : fderiv ℝ (s3Cx u) ζ (EuclideanSpace.single j (1 : ℝ)) = s3D u j ζ := by
      unfold s3D; rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [h1, s3D_apply, s16cze_pd_apply]
  rw [hD] at hF
  exact hF

/-- the symbol integrand `‖ξ‖^θ 𝓕u(ξ) e^{2πi x·ξ}` -/
def s16frac_sym (θ : ℝ) (u : 𝓢(Euc d, ℝ)) (x ξ : Euc d) : ℂ :=
  ((‖ξ‖ ^ θ : ℝ) : ℂ) * 𝓕 (fun y : Euc d => ((u y : ℝ) : ℂ)) ξ *
    Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ))

lemma s16frac_sum_sq_rpow (hs0 : 0 ≤ s) (hθ : 0 < s + 2 - d) (ξ : Euc d) :
    ∑ i : Fin d, (ξ i) ^ 2 * ‖ξ‖ ^ (s - d) = ‖ξ‖ ^ (s + 2 - d) := by
  have hsq : ∑ i : Fin d, (ξ i) ^ 2 = ‖ξ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  rw [← Finset.sum_mul, hsq]
  by_cases hξ : ξ = 0
  · subst hξ
    simp [Real.zero_rpow hθ.ne']
  · have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    rw [show s + 2 - (d : ℝ) = 2 + (s - d) by ring, Real.rpow_add hr, Real.rpow_two]

/-- **Fourier representation of `g * Δu`**: there is `c > 0` with
`g * Δu (x) = -(2π)² c ∫ ‖ξ‖^θ 𝓕u(ξ) e^{2πi x·ξ} dξ`, `θ = s + 2 - d`. -/
theorem s16frac_lap_fourier (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ : 0 < s + 2 - d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (u : 𝓢(Euc d, ℝ)) (x : Euc d),
      ((HRS.Whole.convFun (rieszKernel d s) (fun z => ∑ i : Fin d, s16cze_pd (s16cze_pd u i) i z) x : ℝ) : ℂ) =
        -(((2 * Real.pi) ^ 2 * c : ℝ) : ℂ) * ∫ ξ : Euc d, s16frac_sym (s + 2 - d) u x ξ := by
  obtain ⟨c, hc, h⟩ := kg_fourier_h_proof hd hs0 hsd
  refine ⟨c, hc, fun u x => ?_⟩
  -- the terms
  set f : Fin d → Euc d → ℂ := fun i ξ =>
    ((c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Complex.I *
      𝓕 (fun y : Euc d => ((s16cze_pd u i y : ℝ) : ℂ)) ξ *
      Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)) with hf
  have hterm : ∀ i : Fin d, ((HRS.Whole.convFun (rieszKernel d s) (⇑(s16cze_pd (s16cze_pd u i) i)) x : ℝ) : ℂ) =
      ∫ ξ, f i ξ := by
    intro i
    have h1 := (h i (s16cze_pd u i) x).2
    have e1 : HRS.Whole.convFun (rieszKernel d s)
        (fun z => fderiv ℝ (⇑(s16cze_pd u i)) z (EuclideanSpace.single i (1 : ℝ))) x =
        HRS.Whole.convFun (rieszKernel d s) (⇑(s16cze_pd (s16cze_pd u i) i)) x := by
      congr 1
    rw [e1] at h1
    exact h1
  have hint : ∀ i : Fin d, Integrable (f i) := by
    intro i
    have h1 := (h i (s16cze_pd u i) x).1
    refine h1.mul_bdd (c := 1) ?_ (Eventually.of_forall fun ξ => ?_)
    · exact (by fun_prop : Continuous fun ξ : Euc d =>
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ))).aestronglyMeasurable
    · rw [show (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ) : ℂ) = ((2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I
        by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  -- the sum of convolutions
  have hconv : HRS.Whole.convFun (rieszKernel d s) (fun z => ∑ i : Fin d, s16cze_pd (s16cze_pd u i) i z) x =
      ∑ i : Fin d, HRS.Whole.convFun (rieszKernel d s) (⇑(s16cze_pd (s16cze_pd u i) i)) x := by
    simp only [s16cze_conv_swap]
    rw [← integral_finsetSum]
    · congr 1; funext y; rw [Finset.mul_sum]
    · intro i _
      have := s16frac_conv_int hd hs0 hsd (s16cze_pd (s16cze_pd u i) i) x
      simpa [smul_eq_mul] using this
  rw [hconv]
  push_cast
  simp_rw [hterm]
  rw [← integral_finsetSum _ (fun i _ => hint i), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [hf, s16frac_sym, s16frac_ft_pd]
  have hk := s16frac_sum_sq_rpow (d := d) hs0 hθ ξ
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hk' : ∑ i : Fin d, ((ξ i : ℂ)) ^ 2 * ((‖ξ‖ ^ (s - d) : ℝ) : ℂ) = ((‖ξ‖ ^ (s + 2 - d) : ℝ) : ℂ) := by
    rw [← hk]; push_cast; rfl
  generalize 𝓕 (fun y : Euc d => ((u y : ℝ) : ℂ)) ξ = U
  generalize Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)) = E
  rw [← hk']
  generalize ‖ξ‖ ^ (s - (d : ℝ)) = N
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  linear_combination ((c : ℂ) * (2 * (Real.pi : ℂ)) ^ 2 * ((ξ i : ℂ)) ^ 2 * (N : ℂ)
    * U * E) * hI

/-! ### Fourier representation of the symmetrised fractional Laplacian -/

/-- `𝓕 u` for real `u` -/
def s16frac_U (u : 𝓢(Euc d, ℝ)) : Euc d → ℂ := 𝓕 (fun y : Euc d => ((u y : ℝ) : ℂ))

/-- the Fourier transform as a Schwartz function -/
def s16frac_Us (u : 𝓢(Euc d, ℝ)) : 𝓢(Euc d, ℂ) := 𝓕 (s3Cx u)

lemma s16frac_U_eq (u : 𝓢(Euc d, ℝ)) : s16frac_U u = ⇑(s16frac_Us u) := by
  unfold s16frac_U s16frac_Us
  rw [SchwartzMap.fourier_coe]
  rfl

lemma s16frac_U_integrable (u : 𝓢(Euc d, ℝ)) : Integrable (s16frac_U u) := by
  rw [s16frac_U_eq]; exact (s16frac_Us u).integrable

lemma s16frac_U_cont (u : 𝓢(Euc d, ℝ)) : Continuous (s16frac_U u) := by
  rw [s16frac_U_eq]; exact (s16frac_Us u).continuous

/-- the character `e^{2πi y·ξ}` -/
def s16frac_E (y ξ : Euc d) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ))

lemma s16frac_E_norm (y ξ : Euc d) : ‖s16frac_E y ξ‖ = 1 := by
  unfold s16frac_E
  rw [show (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ) : ℂ) =
    ((2 * Real.pi * inner ℝ y ξ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]

lemma s16frac_E_cont (y : Euc d) : Continuous (s16frac_E y) := by
  unfold s16frac_E; fun_prop

lemma s16frac_E_sub (x z ξ : Euc d) :
    s16frac_E (x - z) ξ = s16frac_E x ξ * Complex.exp (-(((2 * Real.pi * inner ℝ z ξ : ℝ) : ℂ)) * Complex.I) := by
  unfold s16frac_E
  rw [← Complex.exp_add, inner_sub_left]
  congr 1; push_cast; ring

lemma s16frac_E_add (x z ξ : Euc d) :
    s16frac_E (x + z) ξ = s16frac_E x ξ * Complex.exp (((2 * Real.pi * inner ℝ z ξ : ℝ) : ℂ) * Complex.I) := by
  unfold s16frac_E
  rw [← Complex.exp_add, inner_add_left]
  congr 1; push_cast; ring

lemma s16frac_UE_integrable (u : 𝓢(Euc d, ℝ)) (y : Euc d) :
    Integrable (fun ξ => s16frac_U u ξ * s16frac_E y ξ) :=
  (s16frac_U_integrable u).mul_bdd (c := 1) (s16frac_E_cont y).aestronglyMeasurable
    (Eventually.of_forall fun ξ => (s16frac_E_norm y ξ).le)

/-- Fourier inversion: `u(y) = ∫ 𝓕u(ξ) e^{2πi y·ξ} dξ` -/
lemma s16frac_inv (u : 𝓢(Euc d, ℝ)) (y : Euc d) :
    ((u y : ℝ) : ℂ) = ∫ ξ : Euc d, s16frac_U u ξ * s16frac_E y ξ := by
  have h : (𝓕⁻ (𝓕 (s3Cx u)) : SchwartzMap (Euc d) ℂ) = s3Cx u := FourierPair.fourierInv_fourier_eq _
  have h2 := congrArg (fun T : SchwartzMap (Euc d) ℂ => T y) h
  simp only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at h2
  have h3 : ((u y : ℝ) : ℂ) = (s3Cx u) y := rfl
  rw [h3, ← h2]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  have hU : (𝓕 (s3Cx u)) ξ = s16frac_U u ξ := by rw [s16frac_U_eq]; rfl
  rw [hU, s16frac_E, mul_comm]
  congr 2
  push_cast
  rw [real_inner_comm]; ring

/-- second difference in Fourier form -/
lemma s16frac_second_diff_fourier (u : 𝓢(Euc d, ℝ)) (x z : Euc d) :
    (((u x - (u (x - z) + u (x + z)) / 2 : ℝ)) : ℂ) =
      ∫ ξ : Euc d, s16frac_U u ξ * s16frac_E x ξ * ((1 - Real.cos (2 * Real.pi * inner ℝ z ξ) : ℝ) : ℂ) := by
  push_cast
  have hA := s16frac_UE_integrable u x
  have hB := s16frac_UE_integrable u (x - z)
  have hC := s16frac_UE_integrable u (x + z)
  have h' : Integrable (fun ξ => (s16frac_U u ξ * s16frac_E (x - z) ξ + s16frac_U u ξ * s16frac_E (x + z) ξ) / 2) :=
    (hB.add hC).div_const 2
  have key : ∫ ξ, (s16frac_U u ξ * s16frac_E x ξ -
      (s16frac_U u ξ * s16frac_E (x - z) ξ + s16frac_U u ξ * s16frac_E (x + z) ξ) / 2) =
      (∫ ξ, s16frac_U u ξ * s16frac_E x ξ) -
        ((∫ ξ, s16frac_U u ξ * s16frac_E (x - z) ξ) + ∫ ξ, s16frac_U u ξ * s16frac_E (x + z) ξ) / 2 := by
    rw [integral_sub hA h', integral_div, integral_add hB hC]
  rw [s16frac_inv u x, s16frac_inv u (x - z), s16frac_inv u (x + z), ← key]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [s16frac_E_sub, s16frac_E_add, Complex.cos]
  push_cast
  ring_nf

/-- the symmetrised (absolutely convergent) form of the fractional Laplacian,
`∫ (2u(x) - u(x-z) - u(x+z))/2 |z|^{-d-θ} dz` (equal to the frozen `fracLap`, `fracLap_eq_symm`) -/
def s16frac_fracSym (d : ℕ) (θ : ℝ) (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ z : Euc d, (2 * u x - u (x - z) - u (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ)

lemma s16frac_rpow_le (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2) (r : ℝ) (hr : 0 ≤ r) :
    r ^ θ ≤ 1 + r ^ 2 := by
  rcases le_total r 1 with h | h
  · have := Real.rpow_le_one hr h hθ0.le
    nlinarith [sq_nonneg r]
  · have h1 : r ^ θ ≤ r ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hθ2.le
    rw [Real.rpow_two] at h1
    linarith

lemma s16frac_sym_integrable (u : 𝓢(Euc d, ℝ)) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) :
    Integrable (fun ξ : Euc d => ‖s16frac_U u ξ‖ * ‖ξ‖ ^ θ) := by
  have h1 := (s16frac_U_integrable u).norm
  have h2 : Integrable (fun ξ : Euc d => ‖ξ‖ ^ 2 * ‖(s16frac_Us u) ξ‖) :=
    SchwartzMap.integrable_pow_mul (volume : Measure (Euc d)) (s16frac_Us u) 2
  have hU : ∀ ξ, s16frac_U u ξ = s16frac_Us u ξ := fun ξ => by rw [s16frac_U_eq]
  refine (h1.add h2).mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact ((s16frac_U_cont u).norm.mul (continuous_norm.rpow_const fun _ => Or.inr hθ0.le)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
    have := s16frac_rpow_le θ hθ0 hθ2 ‖ξ‖ (norm_nonneg _)
    have h3 := mul_le_mul_of_nonneg_left this (norm_nonneg ((s16frac_Us u) ξ))
    simp only [Pi.add_apply, hU]
    nlinarith [h3]

/-- **Fourier representation of the symmetrised fractional Laplacian**:
`∫ (2u(x) - u(x-z) - u(x+z))/2 |z|^{-d-θ} dz = C₀ ∫ ‖ξ‖^θ 𝓕u(ξ) e^{2πi x·ξ} dξ`, `C₀ > 0`. -/
theorem s16frac_fracSym_fourier (hd : 1 ≤ d) (i0 : Fin d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    ((s16frac_fracSym d θ u x : ℝ) : ℂ) = (s16frac_C0 i0 θ : ℂ) * ∫ ξ : Euc d, s16frac_sym θ u x ξ := by
  set F : Euc d → Euc d → ℂ := fun z ξ =>
    s16frac_U u ξ * s16frac_E x ξ * ((s16frac_h d θ ξ z : ℝ) : ℂ) with hF
  -- step 1: pointwise in `z`
  have h1 : ∀ z : Euc d, (((2 * u x - u (x - z) - u (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ) : ℝ) : ℂ) =
      ∫ ξ, F z ξ := by
    intro z
    have hD := s16frac_second_diff_fourier u x z
    have e1 : (2 * u x - u (x - z) - u (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ) =
        (u x - (u (x - z) + u (x + z)) / 2) * ‖z‖ ^ (-((d : ℝ) + θ)) := by
      rw [Real.rpow_neg (norm_nonneg _), div_eq_mul_inv]; ring
    rw [e1, Complex.ofReal_mul, hD, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hF, s16frac_h]
    push_cast; ring
  -- measurability on the product
  have hmeas : Measurable (fun p : Euc d × Euc d => F p.1 p.2) := by
    have hh : Measurable (fun p : Euc d × Euc d => s16frac_h d θ p.2 p.1) := by
      unfold s16frac_h
      have hin : Continuous fun p : Euc d × Euc d => inner ℝ p.1 p.2 :=
        continuous_inner.comp (continuous_fst.prodMk continuous_snd)
      exact (measurable_const.sub (Real.measurable_cos.comp (measurable_const.mul hin.measurable))).mul
        (measurable_fst.norm.pow_const _)
    have hU : Measurable (fun p : Euc d × Euc d => s16frac_U u p.2) :=
      (s16frac_U_cont u).measurable.comp measurable_snd
    have hE : Measurable (fun p : Euc d × Euc d => s16frac_E x p.2) :=
      (s16frac_E_cont x).measurable.comp measurable_snd
    exact (hU.mul hE).mul (Complex.measurable_ofReal.comp hh)
  -- integrability on the product
  have hint : Integrable (Function.uncurry F) ((volume : Measure (Euc d)).prod volume) := by
    have hmeas' : AEStronglyMeasurable (Function.uncurry F)
        ((volume : Measure (Euc d)).prod (volume : Measure (Euc d))) := hmeas.aestronglyMeasurable
    rw [integrable_prod_iff' hmeas']
    refine ⟨Eventually.of_forall fun ξ => ?_, ?_⟩
    · have := ((s16frac_h_integrable hd hθ0 hθ2 ξ).ofReal (𝕜 := ℂ)).const_mul
        (s16frac_U u ξ * s16frac_E x ξ)
      exact this
    · have hn : ∀ ξ : Euc d, ∫ z, ‖Function.uncurry F (z, ξ)‖ =
          ‖s16frac_U u ξ‖ * (s16frac_C0 i0 θ * ‖ξ‖ ^ θ) := by
        intro ξ
        have : ∀ z : Euc d, ‖Function.uncurry F (z, ξ)‖ = ‖s16frac_U u ξ‖ * s16frac_h d θ ξ z := by
          intro z
          simp only [Function.uncurry, hF, norm_mul, s16frac_E_norm, mul_one, Complex.norm_real,
            Real.norm_of_nonneg (s16frac_h_nonneg θ ξ z)]
        simp_rw [this]
        rw [integral_const_mul, s16frac_h_integral hd i0 hθ0]
      simp_rw [hn]
      have := (s16frac_sym_integrable u hθ0 hθ2).const_mul (s16frac_C0 i0 θ)
      refine this.congr (Eventually.of_forall fun ξ => ?_)
      simp only; ring
  -- Fubini and evaluation
  rw [s16frac_fracSym, ← integral_complex_ofReal]
  simp_rw [h1]
  rw [integral_integral_swap hint]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [hF, s16frac_sym, s16frac_U, s16frac_E]
  rw [integral_const_mul, integral_complex_ofReal,
    s16frac_h_integral hd i0 hθ0]
  push_cast; ring

/-! ### `Δ g * u = -c Λ^θ u` -/

/-- **`Δ(g * u) = g * Δu = -c Λ^θ u`** with the symmetrised fractional Laplacian -/
theorem s16frac_lap_fracSym (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ : 0 < s + 2 - d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (u : 𝓢(Euc d, ℝ)) (x : Euc d),
      HRS.Whole.convFun (rieszKernel d s) (fun z => ∑ i : Fin d, s16cze_pd (s16cze_pd u i) i z) x =
        -c * s16frac_fracSym d (s + 2 - d) u x := by
  have hθ2 : s + 2 - (d : ℝ) < 2 := by linarith
  obtain ⟨c, hc, hA⟩ := s16frac_lap_fourier hd hs0 hsd hθ
  set i0 : Fin d := ⟨0, hd⟩ with hi0
  have hC0 := s16frac_C0_pos hd i0 hθ hθ2
  refine ⟨(2 * Real.pi) ^ 2 * c / s16frac_C0 i0 (s + 2 - d), by positivity, fun u x => ?_⟩
  have h1 := hA u x
  have h2 := s16frac_fracSym_fourier hd i0 hθ hθ2 u x
  apply Complex.ofReal_injective
  rw [h1]
  push_cast
  set J : ℂ := ∫ ξ : Euc d, s16frac_sym (s + 2 - d) u x ξ
  rw [h2]
  have : (s16frac_C0 i0 (s + 2 - d) : ℂ) ≠ 0 := by exact_mod_cast hC0.ne'
  field_simp

/-- **`Δ g * u = -c Λ^θ u`** (supplement L10328-10343), `g = rieszKernel d s`, `θ = s + 2 - d ∈ (0, 2)`,
with `Δ g * u := Δ (g * u)` the Laplacian of the convolution (the sum of the iterated coordinate derivatives of
`convFun g u`, all of which exist: part 2) and `Λ^θ u = fracLap d θ u` the frozen singular-integral fractional
Laplacian (without normalising constant).  `c > 0` depends only on `d, s`. -/
theorem s16frac_lap_fracLap (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ : 0 < s + 2 - d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (u : 𝓢(Euc d, ℝ)) (x : Euc d),
      ∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) u) y
        (EuclideanSpace.single i (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)) =
        -c * HRS.Whole.AppendixA.fracLap d (s + 2 - d) u x := by
  have hθ2 : s + 2 - (d : ℝ) < 2 := by linarith
  obtain ⟨c, hc, h⟩ := s16frac_lap_fracSym hd hs0 hsd hθ
  refine ⟨c, hc, fun u x => ?_⟩
  rw [s16frac_lap_conv hd hs0 hsd u x, h u x]
  obtain ⟨B, L, M, hf⟩ := HRS.CZ.Pv.PvC2.of_schwartz u
  rw [HRS.CZ.Pv.fracLap_eq_symm hd hθ hθ2 hf x]
  rfl

end HRS.S16Frac
