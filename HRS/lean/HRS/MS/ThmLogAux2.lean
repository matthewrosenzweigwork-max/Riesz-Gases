import HRS.MS.ThmLogAux1
import HRS.MS.PsdAux2
import HRS.Whole.Thermal

/-!
# THM-7 (part 1): (K2) for the logarithmic kernel `K̃` via the chordal form

With `u = stereoInv` (`HRS.Whole.stereoInv`): `|u x - u y|² = 4 |x-y|² / ((1+|x|²)(1+|y|²))` (`t67_chordal`), hence
`K̃ x y = -log |u x - u y| + (3/2) log 2` for `x ≠ y` (`t67_K_eq_chordal`).  Each Gaussian slice
`exp (-t |u x - u y|²)` is positive definite against `f ⊗ f` (`t67_gauss_feature`: cosine representation of the
Gaussian over a standard Gaussian on `ℝ^{d+1}`, no sign trick needed), and the Frullani argument of
`HRS.MS.Psd.psd2_core` runs verbatim for the abstract distance `R(x,y) = |u x - u y|` (`t67_frullani_core`).
`ThmSetting.k2` is proved directly (`t67_k2`), without comparing `E_K̃` with `E_g`; absolute integrability of the
`-log R` pairing comes from `-log R = K̃ - (3/2) log 2` a.e. and `f ⊗ f ∈ L¹`.  `t67_setting` packages
`ThmSetting (t67K d) (t67gammaBar d a β) B`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

lemma t67_stereo_apply_castSucc (x : Euc d) (i : Fin d) :
    (stereoInv x) (Fin.castSucc i) = 2 * x i / (1 + ‖x‖ ^ 2) := by
  simp [stereoInv]

lemma t67_stereo_apply_last (x : Euc d) :
    (stereoInv x) (Fin.last d) = (‖x‖ ^ 2 - 1) / (1 + ‖x‖ ^ 2) := by
  simp [stereoInv]

/-- The chordal distance: `|u x - u y|² = 4 |x-y|² / ((1+|x|²)(1+|y|²))`. -/
lemma t67_chordal (x y : Euc d) :
    ‖stereoInv x - stereoInv y‖ ^ 2 = 4 * ‖x - y‖ ^ 2 / ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) := by
  have ha : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have hb : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by positivity
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [PiLp.sub_apply, t67_stereo_apply_castSucc, t67_stereo_apply_last, Real.norm_eq_abs, sq_abs]
  have hx : ∑ i, x i ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [sq_abs]
  have hy : ∑ i, y i ^ 2 = ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [sq_abs]
  have hxy : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * ∑ i, x i * y i := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
    have : ∀ i, (x i - y i) ^ 2 = x i ^ 2 + y i ^ 2 - 2 * (x i * y i) := fun i => by ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hx, hy]
  have hs : ∑ i : Fin d, (2 * x i / (1 + ‖x‖ ^ 2) - 2 * y i / (1 + ‖y‖ ^ 2)) ^ 2 =
      4 / (1 + ‖x‖ ^ 2) ^ 2 * ‖x‖ ^ 2 + 4 / (1 + ‖y‖ ^ 2) ^ 2 * ‖y‖ ^ 2 -
        8 / ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) * ∑ i, x i * y i := by
    have : ∀ i : Fin d, (2 * x i / (1 + ‖x‖ ^ 2) - 2 * y i / (1 + ‖y‖ ^ 2)) ^ 2 =
        4 / (1 + ‖x‖ ^ 2) ^ 2 * x i ^ 2 + 4 / (1 + ‖y‖ ^ 2) ^ 2 * y i ^ 2 -
          8 / ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) * (x i * y i) := fun i => by
      field_simp
      ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hx, hy]
  rw [hs, hxy]
  field_simp
  ring

lemma t67_stereo_continuous : Continuous (stereoInv : Euc d → EuclideanSpace ℝ (Fin (d + 1))) := by
  unfold stereoInv
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]
    fun_prop (disch := intros; positivity)
  · simp only [Fin.snoc_castSucc]
    fun_prop (disch := intros; positivity)

lemma t67_stereo_measurable : Measurable (stereoInv : Euc d → EuclideanSpace ℝ (Fin (d + 1))) :=
  t67_stereo_continuous.measurable

/-- Off the diagonal, `K̃ = -log |u x - u y| + (3/2) log 2`. -/
lemma t67_K_eq_chordal {x y : Euc d} (hxy : x ≠ y) :
    t67K d x y = -Real.log ‖stereoInv x - stereoInv y‖ + (3 / 2) * Real.log 2 := by
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hch := t67_chordal x y
  have hA : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have hB : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by positivity
  have hR : 0 < ‖stereoInv x - stereoInv y‖ := by
    have : 0 < ‖stereoInv x - stereoInv y‖ ^ 2 := by rw [hch]; positivity
    exact lt_of_not_ge fun h => by nlinarith [norm_nonneg (stereoInv x - stereoInv y)]
  have hlog : Real.log (‖stereoInv x - stereoInv y‖ ^ 2) =
      Real.log 4 + 2 * Real.log ‖x - y‖ - t67l x - t67l y := by
    rw [hch, Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_mul hA.ne' hB.ne', Real.log_pow]
    unfold t67l
    push_cast
    ring
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [Real.log_pow] at hlog
  unfold t67K
  rw [t67_g]
  push_cast at hlog
  linarith

open InnerProductSpace ProbabilityTheory in
/-- A Gaussian-feature slice: for a measurable `φ : ℝ^d → ℝ^m` and `f ∈ L¹`, the kernel
`exp (-τ |φ x - φ y|²)` is positive definite against `f`. -/
theorem t67_gauss_feature {m : ℕ} {φ : Euc d → Euc m} (hφ : Measurable φ) {f : Euc d → ℝ}
    (hfm : Measurable f) (hf : Integrable f) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ ∫ z, Real.exp (-(‖φ z.1 - φ z.2‖ ^ 2 * τ)) * (f z.1 * f z.2)
      ∂((volume : Measure (Euc d)).prod volume) := by
  set γ := stdGaussian (Euc m) with hγ
  set l : ℝ := Real.sqrt (2 * τ) with hl
  have hmaj : Integrable (fun z : Euc d × Euc d => |f z.1| * |f z.2|)
      ((volume : Measure (Euc d)).prod volume) := hf.abs.mul_prod hf.abs
  set Φ : (Euc d × Euc d) × Euc m → ℝ := fun p =>
    f p.1.1 * f p.1.2 * Real.cos (l * (inner ℝ p.2 (φ p.1.1) - inner ℝ p.2 (φ p.1.2))) with hΦ
  have hΦm : Measurable Φ := by
    have h1 : Measurable (fun p : (Euc d × Euc d) × Euc m => inner ℝ p.2 (φ p.1.1)) :=
      measurable_snd.inner (hφ.comp (measurable_fst.comp measurable_fst))
    have h2 : Measurable (fun p : (Euc d × Euc d) × Euc m => inner ℝ p.2 (φ p.1.2)) :=
      measurable_snd.inner (hφ.comp (measurable_snd.comp measurable_fst))
    exact (((hfm.comp (measurable_fst.comp measurable_fst)).mul
      (hfm.comp (measurable_snd.comp measurable_fst))).mul
        (Real.measurable_cos.comp ((h1.sub h2).const_mul l)))
  have hΦi : Integrable Φ (((volume : Measure (Euc d)).prod volume).prod γ) := by
    have hmaj2 : Integrable (fun p : (Euc d × Euc d) × Euc m => |f p.1.1| * |f p.1.2|)
        (((volume : Measure (Euc d)).prod volume).prod γ) := by
      have := hmaj.mul_prod (integrable_const (1 : ℝ) (μ := γ))
      simpa using this
    refine Integrable.mono' hmaj2 hΦm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [hΦ]
    simp only [Real.norm_eq_abs, abs_mul]
    calc |f p.1.1| * |f p.1.2| * |Real.cos (l * (inner ℝ p.2 (φ p.1.1) - inner ℝ p.2 (φ p.1.2)))|
        ≤ |f p.1.1| * |f p.1.2| * 1 := by gcongr; exact Real.abs_cos_le_one _
      _ = _ := by ring
  have hstep1 : ∫ z, Real.exp (-(‖φ z.1 - φ z.2‖ ^ 2 * τ)) * (f z.1 * f z.2)
        ∂((volume : Measure (Euc d)).prod volume) =
      ∫ z, ∫ ξ, Φ (z, ξ) ∂γ ∂((volume : Measure (Euc d)).prod volume) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hΦ]
    rw [integral_const_mul]
    have := Q34.gauss_kernel_eq (d := m) hτ (φ z.1) (φ z.2)
    rw [← this]
    have e : -(‖φ z.1 - φ z.2‖ ^ 2 * τ) = -τ * ‖φ z.1 - φ z.2‖ ^ 2 := by ring
    rw [e]
    ring
  rw [hstep1, integral_integral_swap (f := fun z ξ => Φ (z, ξ)) hΦi]
  refine integral_nonneg fun ξ => ?_
  set f1 : Euc d → ℝ := fun x => f x * Real.cos (l * inner ℝ ξ (φ x)) with hf1
  set f2 : Euc d → ℝ := fun x => f x * Real.sin (l * inner ℝ ξ (φ x)) with hf2
  have hin : Measurable (fun x : Euc d => inner ℝ ξ (φ x)) :=
    measurable_const.inner hφ
  have hf1m : Measurable f1 := hfm.mul (Real.measurable_cos.comp (hin.const_mul l))
  have hf2m : Measurable f2 := hfm.mul (Real.measurable_sin.comp (hin.const_mul l))
  have hf1i : Integrable f1 := by
    refine Integrable.mono' hf.abs hf1m.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [hf1]; simp only [Real.norm_eq_abs, abs_mul]
    calc |f x| * |Real.cos (l * inner ℝ ξ (φ x))| ≤ |f x| * 1 := by
          gcongr; exact Real.abs_cos_le_one _
      _ = |f x| := by ring
  have hf2i : Integrable f2 := by
    refine Integrable.mono' hf.abs hf2m.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [hf2]; simp only [Real.norm_eq_abs, abs_mul]
    calc |f x| * |Real.sin (l * inner ℝ ξ (φ x))| ≤ |f x| * 1 := by
          gcongr; exact Real.abs_sin_le_one _
      _ = |f x| := by ring
  have hsplit : ∀ z : Euc d × Euc d, Φ (z, ξ) = f1 z.1 * f1 z.2 + f2 z.1 * f2 z.2 := by
    intro z
    simp only [hΦ, hf1, hf2]
    rw [mul_sub, Real.cos_sub]
    ring
  simp_rw [hsplit]
  rw [integral_add (hf1i.mul_prod hf1i) (hf2i.mul_prod hf2i), integral_prod_mul, integral_prod_mul]
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- The Frullani slice argument for an abstract positive "distance" `R` on pairs: if every Gaussian slice
`exp (-t R²)` is positive against `f ⊗ f` and `∫ f = 0`, then the logarithmic energy `-log R` is nonnegative
(absolute integrability of the `-log R` pairing is a hypothesis). -/
theorem t67_frullani_core {f : Euc d → ℝ} (hfm : Measurable f) (hf : Integrable f)
    (hmass : ∫ x, f x = 0) {R : Euc d × Euc d → ℝ} (hRm : Measurable R)
    (hR : ∀ᵐ z ∂((volume : Measure (Euc d)).prod volume), 0 < R z)
    (hslice : ∀ t : ℝ, 0 < t → 0 ≤ ∫ z, Real.exp (-(R z ^ 2 * t)) * (f z.1 * f z.2)
      ∂((volume : Measure (Euc d)).prod volume))
    (hI : Integrable (fun z => (-Real.log (R z)) * (f z.1 * f z.2))
      ((volume : Measure (Euc d)).prod volume)) :
    0 ≤ ∫ z, (-Real.log (R z)) * (f z.1 * f z.2) ∂((volume : Measure (Euc d)).prod volume) := by
  set μ2 : Measure (Euc d × Euc d) := (volume : Measure (Euc d)).prod volume with hμ2
  set μt : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ)) with hμt
  set Ψ : (Euc d × Euc d) × ℝ → ℝ :=
    fun q => HRS.MS.Psd.psd2_g (R q.1) q.2 * (f q.1.1 * f q.1.2) with hΨ
  have hff : Integrable (fun z : Euc d × Euc d => f z.1 * f z.2) μ2 := hf.mul_prod hf
  have hΨm : Measurable Ψ := by
    have h1 : Measurable (fun q : (Euc d × Euc d) × ℝ => q.2 ^ ((0 : ℝ) / 2 - 1)) :=
      measurable_snd.pow_const _
    have h2 : Measurable (fun q : (Euc d × Euc d) × ℝ =>
        Real.exp (-(R q.1 ^ 2 * q.2)) - Real.exp (-(1 * q.2))) := by
      have a1 : Measurable (fun q : (Euc d × Euc d) × ℝ => R q.1 ^ 2 * q.2) :=
        ((hRm.comp measurable_fst).pow_const 2).mul measurable_snd
      exact (Real.measurable_exp.comp a1.neg).sub
        (Real.measurable_exp.comp (measurable_snd.const_mul 1).neg)
    exact (h1.mul h2).mul
      ((hfm.comp (measurable_fst.comp measurable_fst)).mul (hfm.comp (measurable_snd.comp measurable_fst)))
  have hΨi : Integrable Ψ (μ2.prod μt) := by
    rw [integrable_prod_iff hΨm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [hR] with z hz
      exact (HRS.MS.Psd.psd2_g_int hz).mul_const (f z.1 * f z.2)
    · have hae : (fun z : Euc d × Euc d => 2 * ‖(-Real.log (R z)) * (f z.1 * f z.2)‖)
          =ᵐ[μ2] fun z => ∫ t, ‖Ψ (z, t)‖ ∂μt := by
        filter_upwards [hR] with z hz
        have e : ∫ t, ‖Ψ (z, t)‖ ∂μt =
            (∫ t in Set.Ioi (0 : ℝ), ‖HRS.MS.Psd.psd2_g (R z) t‖) * ‖f z.1 * f z.2‖ := by
          rw [← integral_mul_const]
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          simp only [hΨ, norm_mul]
        rw [e, HRS.MS.Psd.psd2_g_abs hz, norm_mul, Real.norm_eq_abs, abs_neg, Real.norm_eq_abs]
        ring
      exact (hI.norm.const_mul 2).congr hae
  have hswap := integral_integral_swap (μ := μ2) (ν := μt) (f := fun z t => Ψ (z, t)) hΨi
  have hL : ∫ z, ∫ t, Ψ (z, t) ∂μt ∂μ2 = 2 * ∫ z, (-Real.log (R z)) * (f z.1 * f z.2) ∂μ2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hR] with z hz
    have e : ∫ t, Ψ (z, t) ∂μt =
        (∫ t in Set.Ioi (0 : ℝ), HRS.MS.Psd.psd2_g (R z) t) * (f z.1 * f z.2) := by
      rw [← integral_mul_const]
    rw [e, HRS.MS.Psd.psd2_g_val hz]
    ring
  have hR1 : ∀ t : ℝ, 0 < t → 0 ≤ ∫ z, Ψ (z, t) ∂μ2 := by
    intro t ht
    have hE : Integrable (fun z : Euc d × Euc d =>
        Real.exp (-(R z ^ 2 * t)) * (f z.1 * f z.2)) μ2 := by
      refine Integrable.mono' hff.norm ?_ (Filter.Eventually.of_forall fun z => ?_)
      · have : Measurable (fun z : Euc d × Euc d =>
            Real.exp (-(R z ^ 2 * t)) * (f z.1 * f z.2)) :=
          (Real.measurable_exp.comp ((hRm.pow_const 2).mul_const t).neg).mul
            ((hfm.comp measurable_fst).mul (hfm.comp measurable_snd))
        exact this.aestronglyMeasurable
      · have h1 : Real.exp (-(R z ^ 2 * t)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (R z)]
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        calc _ ≤ 1 * ‖f z.1 * f z.2‖ := by gcongr
          _ = _ := one_mul _
    have hC : Integrable (fun z : Euc d × Euc d => Real.exp (-(1 * t)) * (f z.1 * f z.2)) μ2 :=
      hff.const_mul _
    have hz0 : ∫ z, f z.1 * f z.2 ∂μ2 = 0 := by
      rw [hμ2, integral_prod_mul f f, hmass, zero_mul]
    have e : ∫ z, Ψ (z, t) ∂μ2 = t ^ ((0 : ℝ) / 2 - 1) *
        ∫ z, Real.exp (-(R z ^ 2 * t)) * (f z.1 * f z.2) ∂μ2 := by
      have e1 : ∀ z : Euc d × Euc d, Ψ (z, t) = t ^ ((0 : ℝ) / 2 - 1) *
          (Real.exp (-(R z ^ 2 * t)) * (f z.1 * f z.2) -
            Real.exp (-(1 * t)) * (f z.1 * f z.2)) := fun z => by
        simp only [hΨ, HRS.MS.Psd.psd2_g]; ring
      simp_rw [e1]
      rw [integral_const_mul, integral_sub hE hC, integral_const_mul, hz0]
      ring
    rw [e]
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (hslice t ht)
  have hR2 : 0 ≤ ∫ t, ∫ z, Ψ (z, t) ∂μ2 ∂μt := by
    refine integral_nonneg_of_ae ?_
    rw [hμt, Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun t ht => hR1 t ht
  have := hswap
  rw [hL] at this
  linarith

lemma t67_chordal_pos {x y : Euc d} (hxy : x ≠ y) : 0 < ‖stereoInv x - stereoInv y‖ := by
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hch := t67_chordal x y
  have : 0 < ‖stereoInv x - stereoInv y‖ ^ 2 := by rw [hch]; positivity
  exact lt_of_not_ge fun h => by nlinarith [norm_nonneg (stereoInv x - stereoInv y)]

/-- (K2) for `K̃`, measurable `f`, with the product integrability of the `K̃`-pairing. -/
theorem t67_k2_core (hd : 1 ≤ d) {f : Euc d → ℝ} (hfm : Measurable f) (hf : Integrable f)
    (hmass : ∫ x, f x = 0)
    (hint : Integrable (fun p : Euc d × Euc d => t67K d p.1 p.2 * f p.1 * f p.2)
      ((volume : Measure (Euc d)).prod volume)) :
    0 ≤ ∫ p : Euc d × Euc d, t67K d p.1 p.2 * f p.1 * f p.2
      ∂((volume : Measure (Euc d)).prod volume) := by
  set μ2 : Measure (Euc d × Euc d) := (volume : Measure (Euc d)).prod volume with hμ2
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hdiag : ∀ᵐ z ∂μ2, z.1 ≠ z.2 := HRS.Whole.Q34.diag_ae (volume : Measure (Euc d))
  have hff : Integrable (fun z : Euc d × Euc d => f z.1 * f z.2) μ2 := hf.mul_prod hf
  have hz0 : ∫ z, f z.1 * f z.2 ∂μ2 = 0 := by
    rw [hμ2, integral_prod_mul f f, hmass, zero_mul]
  set R : Euc d × Euc d → ℝ := fun p => ‖stereoInv p.1 - stereoInv p.2‖ with hR
  have hRm : Measurable R :=
    measurable_norm.comp ((t67_stereo_measurable.comp measurable_fst).sub
      (t67_stereo_measurable.comp measurable_snd))
  have hRpos : ∀ᵐ z ∂μ2, 0 < R z := by
    filter_upwards [hdiag] with z hz
    exact t67_chordal_pos hz
  have hpt : ∀ᵐ z ∂μ2, (-Real.log (R z)) * (f z.1 * f z.2) =
      t67K d z.1 z.2 * f z.1 * f z.2 - (3 / 2 * Real.log 2) * (f z.1 * f z.2) := by
    filter_upwards [hdiag] with z hz
    rw [t67_K_eq_chordal hz]
    simp only [hR]
    ring
  have hI : Integrable (fun z : Euc d × Euc d => (-Real.log (R z)) * (f z.1 * f z.2)) μ2 :=
    (hint.sub (hff.const_mul (3 / 2 * Real.log 2))).congr (hpt.mono fun z hz => hz.symm)
  have hslice : ∀ t : ℝ, 0 < t → 0 ≤ ∫ z, Real.exp (-(R z ^ 2 * t)) * (f z.1 * f z.2) ∂μ2 :=
    fun t ht => t67_gauss_feature t67_stereo_measurable hfm hf ht
  have hcore := t67_frullani_core hfm hf hmass hRm hRpos hslice hI
  have e : ∫ z, t67K d z.1 z.2 * f z.1 * f z.2 ∂μ2 =
      ∫ z, (-Real.log (R z)) * (f z.1 * f z.2) ∂μ2 := by
    have h1 : ∫ z, (-Real.log (R z)) * (f z.1 * f z.2) ∂μ2 =
        ∫ z, t67K d z.1 z.2 * f z.1 * f z.2 ∂μ2 - ∫ z, (3 / 2 * Real.log 2) * (f z.1 * f z.2) ∂μ2 := by
      rw [← integral_sub hint (hff.const_mul _)]
      exact integral_congr_ae hpt
    rw [h1, integral_const_mul, hz0]
    ring
  rw [e]
  exact hcore

/-- **(K2) for `(K̃)`**, in the form required by `ThmSetting.k2`. -/
theorem t67_k2 (hd : 1 ≤ d) {f : Euc d → ℝ} (hf : Integrable f)
    (habs : Integrable (fun p : Euc d × Euc d => |t67K d p.1 p.2 * f p.1 * f p.2|)
      ((volume : Measure (Euc d)).prod volume))
    (hmass : ∫ x, f x = 0) : 0 ≤ pairE (t67K d) f f := by
  have h1 : AEStronglyMeasurable (fun p : Euc d × Euc d => f p.1)
      ((volume : Measure (Euc d)).prod volume) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Euc d)))
        (ν := (volume : Measure (Euc d))))
  have h2 : AEStronglyMeasurable (fun p : Euc d × Euc d => f p.2)
      ((volume : Measure (Euc d)).prod volume) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Euc d)))
        (ν := (volume : Measure (Euc d))))
  have hm : AEStronglyMeasurable (fun p : Euc d × Euc d => t67K d p.1 p.2 * f p.1 * f p.2)
      ((volume : Measure (Euc d)).prod volume) :=
    ((t67K_measurable.aestronglyMeasurable).mul h1).mul h2
  have hint : Integrable (fun p : Euc d × Euc d => t67K d p.1 p.2 * f p.1 * f p.2)
      ((volume : Measure (Euc d)).prod volume) :=
    (integrable_norm_iff hm).1 (habs.congr (ae_of_all _ fun p => by simp only [Real.norm_eq_abs]))
  rw [t012_pairE_eq_prod hint]
  set f' : Euc d → ℝ := hf.aestronglyMeasurable.mk f with hf'
  have hm' : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae : f =ᵐ[volume] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hq1 : (fun p : Euc d × Euc d => f p.1) =ᵐ[(volume : Measure (Euc d)).prod volume]
      fun p => f' p.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Euc d)))
      (ν := (volume : Measure (Euc d)))).ae_eq_comp hae
  have hq2 : (fun p : Euc d × Euc d => f p.2) =ᵐ[(volume : Measure (Euc d)).prod volume]
      fun p => f' p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Euc d)))
      (ν := (volume : Measure (Euc d)))).ae_eq_comp hae
  have hP : (fun p : Euc d × Euc d => t67K d p.1 p.2 * f p.1 * f p.2)
      =ᵐ[(volume : Measure (Euc d)).prod volume] fun p => t67K d p.1 p.2 * f' p.1 * f' p.2 := by
    filter_upwards [hq1, hq2] with p hp1 hp2
    simp only [hp1, hp2]
  rw [integral_congr_ae hP]
  exact t67_k2_core hd hm' (hf.congr hae) (by rw [← integral_congr_ae hae]; exact hmass)
    (hint.congr hP)

/-- The abstract setting of THM-0..4 for the logarithmic kernel `K̃` and the reference density `γ̄`. -/
theorem t67_setting (hd : 1 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ B : ℝ, ThmSetting (t67K d) (t67gammaBar d a β) B := by
  obtain ⟨B, hB⟩ := t67_k1 hd ha hβ
  exact ⟨B,
    { meas := t67K_measurable
      symm := t67K_symm
      nonneg := t67K_nonneg
      r_prob := t67gammaBar_isProbDensity ha hβ
      r_pos := t67gammaBar_pos ha hβ
      k1 := hB
      k2 := fun f hf habs hmass => t67_k2 hd hf habs hmass }⟩

end HRS.MS.Thm

end
