import HRS.Equilibrium.Parametrix.Defs

/-!
# Packet PX3b: the Newton potential solves the Poisson equation (auxiliary file)

Everything here is the classical potential theory of the Newton kernel `Γ` on `ℝ^d`, `d ≥ 2`,
which is not in Mathlib: local integrability, harmonicity off `0`, the weak identity
`∫ E Δg = -g(0)` for `g ∈ C²_c` (via smooth radial truncations `E_ε`), and the pointwise Poisson
equation `-2ν Δ(Γ * H) = H` for a compactly supported integrable `H` that is `C²` near the point.
-/

open MeasureTheory Filter Topology Set
open scoped Convolution

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

/-! ### Laplacian of a radial function -/

lemma hasFDerivAt_normSq_sub (c x : Euc d) :
    HasFDerivAt (fun x : Euc d => ‖x - c‖ ^ 2) (2 • innerSL ℝ (x - c)) x := by
  have h := (hasStrictFDerivAt_norm_sq (x - c)).hasFDerivAt
  have h2 : HasFDerivAt (fun x : Euc d => x - c) (ContinuousLinearMap.id ℝ (Euc d)) x :=
    (hasFDerivAt_id x).sub_const c
  have h3 := h.comp x h2
  rw [ContinuousLinearMap.comp_id] at h3
  exact h3

lemma laplacian_radial (c w : Euc d) (g g' g'' : ℝ → ℝ)
    (h1 : ∀ᶠ t in 𝓝 (‖w - c‖ ^ 2), HasDerivAt g (g' t) t)
    (h2 : HasDerivAt g' (g'' (‖w - c‖ ^ 2)) (‖w - c‖ ^ 2)) :
    Laplacian.laplacian (fun x : Euc d => g (‖x - c‖ ^ 2)) w =
      2 * d * g' (‖w - c‖ ^ 2) + 4 * ‖w - c‖ ^ 2 * g'' (‖w - c‖ ^ 2) := by
  set f : Euc d → ℝ := fun x => g (‖x - c‖ ^ 2) with hf
  set φ : Euc d → Euc d →L[ℝ] ℝ := fun x => g' (‖x - c‖ ^ 2) • (2 • innerSL ℝ (x - c)) with hφ
  have hcont : Continuous fun x : Euc d => ‖x - c‖ ^ 2 := by fun_prop
  have h1' : ∀ᶠ x in 𝓝 w, HasDerivAt g (g' (‖x - c‖ ^ 2)) (‖x - c‖ ^ 2) :=
    hcont.continuousAt.eventually h1
  have hfd : fderiv ℝ f =ᶠ[𝓝 w] φ := by
    filter_upwards [h1'] with x hx
    exact (hx.comp_hasFDerivAt x (hasFDerivAt_normSq_sub c x)).fderiv
  have ha : HasFDerivAt (fun x : Euc d => g' (‖x - c‖ ^ 2))
      (g'' (‖w - c‖ ^ 2) • (2 • innerSL ℝ (w - c))) w :=
    h2.comp_hasFDerivAt w (hasFDerivAt_normSq_sub c w)
  have hL : HasFDerivAt (fun x : Euc d => (2 : ℕ) • innerSL ℝ (x - c))
      ((2 : ℕ) • (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)) w := by
    have : HasFDerivAt (fun x : Euc d => x - c) (ContinuousLinearMap.id ℝ (Euc d)) w :=
      (hasFDerivAt_id w).sub_const c
    have h3 := (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).hasFDerivAt.comp w this
    have h4 := h3.const_smul (2 : ℕ)
    exact h4
  have hφd : HasFDerivAt φ _ w := ha.smul hL
  have hsec : ∀ v : Euc d, iteratedFDeriv ℝ 2 f w ![v, v] =
      2 * g' (‖w - c‖ ^ 2) * ‖v‖ ^ 2 + 4 * g'' (‖w - c‖ ^ 2) * (inner ℝ (w - c) v) ^ 2 := by
    intro v
    rw [iteratedFDeriv_two_apply, hfd.fderiv_eq, hφd.fderiv]
    have hv : (innerSL ℝ) v v = ‖v‖ ^ 2 := by
      simp [innerSL_apply_apply]
    simp
    rw [hv]
    simp only [inner_sub_left]
    ring
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [hsec]
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  have hsq : ∑ i, inner ℝ (w - c) (b i) ^ 2 = ‖w - c‖ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right (w - c)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsq]
  simp only [OrthonormalBasis.norm_eq_one]
  simp
  ring

/-! ### The kernel `E` -/

/-- `1 / (d · vol B₁)`. -/
def newtonC (d : ℕ) : ℝ := 1 / ((d : ℝ) * (volume (Metric.ball (0 : Euc d) 1)).toReal)

lemma ballVol_pos (hd : 1 ≤ d) : 0 < (volume (Metric.ball (0 : Euc d) 1)).toReal := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne

lemma newtonC_pos (hd : 1 ≤ d) : 0 < newtonC d := by
  have : (0 : ℝ) < d := by exact_mod_cast hd
  unfold newtonC
  have := ballVol_pos (d := d) hd
  positivity

lemma newtonC_mul (hd : 1 ≤ d) : (d : ℝ) * (volume (Metric.ball (0 : Euc d) 1)).toReal * newtonC d = 1 := by
  have h1 : (0 : ℝ) < d := by exact_mod_cast hd
  have := ballVol_pos (d := d) hd
  unfold newtonC
  field_simp

lemma newtonC_two : newtonC 2 = 1 / (2 * Real.pi) := by
  unfold newtonC
  have : (volume (Metric.ball (0 : Euc 2) 1)).toReal = Real.pi := by
    rw [EuclideanSpace.volume_ball_fin_two]
    simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [this]; norm_num

/-- Profile of the fundamental solution as a function of `s = |z|²`. -/
def e0 (d : ℕ) (s : ℝ) : ℝ :=
  if d = 2 then -(1 / (4 * Real.pi)) * Real.log s
  else newtonC d / ((d : ℝ) - 2) * s ^ (((2 : ℝ) - d) / 2)

/-- The fundamental solution of `-Δ`. -/
def Efund (d : ℕ) (z : Euc d) : ℝ := e0 d (‖z‖ ^ 2)

lemma newtonKernel_eq (d : ℕ) (ν : ℝ) (z : Euc d) :
    newtonKernel d ν z = (1 / (2 * ν)) * Efund d z := by
  unfold newtonKernel Efund e0 newtonC
  by_cases h : d = 2
  · simp only [h, if_true]
    subst h
    rw [Real.log_pow]
    push_cast
    ring
  · simp only [h, if_false]
    congr 1
    have hd : ((d : ℝ) - 2) ≠ 0 := by
      intro h0; apply h; exact_mod_cast (by linarith : (d : ℝ) = 2)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
    have : ((2 : ℕ) : ℝ) * (((2 : ℝ) - d) / 2) = 2 - d := by push_cast; ring
    rw [this]
    field_simp

/-- Derivative of the profile. -/
def eprime (d : ℕ) (s : ℝ) : ℝ := -(newtonC d / 2) * s ^ (-(d : ℝ) / 2)

lemma hasDerivAt_e0 {s : ℝ} (hs : 0 < s) : HasDerivAt (e0 d) (eprime d s) s := by
  by_cases h : d = 2
  · subst h
    have h1 := (Real.hasDerivAt_log hs.ne').const_mul (-(1 / (4 * Real.pi)))
    have h2 : e0 2 = fun s => -(1 / (4 * Real.pi)) * Real.log s := by ext; simp [e0]
    rw [h2]
    convert h1 using 1
    unfold eprime
    rw [newtonC_two]
    have : s ^ (-((2 : ℕ) : ℝ) / 2) = s⁻¹ := by
      rw [show (-((2 : ℕ) : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
    rw [this]
    field_simp
    norm_num
  · have hd : ((d : ℝ) - 2) ≠ 0 := by
      intro h0; apply h; exact_mod_cast (by linarith : (d : ℝ) = 2)
    have h1 := (Real.hasDerivAt_rpow_const (x := s) (p := ((2 : ℝ) - d) / 2) (Or.inl hs.ne')).const_mul
      (newtonC d / ((d : ℝ) - 2))
    have h2 : e0 d = fun s => newtonC d / ((d : ℝ) - 2) * s ^ (((2 : ℝ) - d) / 2) := by
      ext; simp [e0, h]
    rw [h2]
    convert h1 using 1
    unfold eprime
    have : -(d : ℝ) / 2 = ((2 : ℝ) - d) / 2 - 1 := by ring
    rw [this]
    field_simp
    ring

def kprime (d : ℕ) (s : ℝ) : ℝ := (newtonC d * d / 4) * s ^ (-(d : ℝ) / 2 - 1)

lemma hasDerivAt_eprime {s : ℝ} (hs : 0 < s) : HasDerivAt (eprime d) (kprime d s) s := by
  have h1 := (Real.hasDerivAt_rpow_const (x := s) (p := -(d : ℝ) / 2) (Or.inl hs.ne')).const_mul
    (-(newtonC d / 2))
  unfold eprime kprime
  convert h1 using 1
  ring

lemma harmonic_aux {s : ℝ} (hs : 0 < s) : 2 * d * eprime d s + 4 * s * kprime d s = 0 := by
  unfold eprime kprime
  have : s ^ (-(d : ℝ) / 2 - 1) * s = s ^ (-(d : ℝ) / 2) := by
    rw [Real.rpow_sub_one hs.ne']; field_simp
  calc 2 * (d : ℝ) * (-(newtonC d / 2) * s ^ (-(d : ℝ) / 2)) +
        4 * s * (newtonC d * d / 4 * s ^ (-(d : ℝ) / 2 - 1))
      = 2 * (d : ℝ) * (-(newtonC d / 2) * s ^ (-(d : ℝ) / 2)) +
        newtonC d * d * (s ^ (-(d : ℝ) / 2 - 1) * s) := by ring
    _ = 0 := by rw [this]; ring

lemma contDiffAt_e0 (n : WithTop ℕ∞) {s : ℝ} (hs : 0 < s) : ContDiffAt ℝ n (e0 d) s := by
  by_cases h : d = 2
  · have h2 : e0 d = fun s => -(1 / (4 * Real.pi)) * Real.log s := by ext; simp [e0, h]
    rw [h2]
    exact contDiffAt_const.mul (Real.contDiffAt_log.mpr hs.ne')
  · have h2 : e0 d = fun s => newtonC d / ((d : ℝ) - 2) * s ^ (((2 : ℝ) - d) / 2) := by
      ext; simp [e0, h]
    rw [h2]
    exact contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne hs.ne')

lemma contDiffAt_Efund (n : WithTop ℕ∞) {z : Euc d} (hz : z ≠ 0) : ContDiffAt ℝ n (Efund d) z := by
  have hs : 0 < ‖z‖ ^ 2 := by positivity
  exact (contDiffAt_e0 n hs).comp z (contDiffAt_id.norm_sq ℝ)

lemma laplacian_Efund {z : Euc d} (hz : z ≠ 0) : Laplacian.laplacian (Efund d) z = 0 := by
  have hs : 0 < ‖z - 0‖ ^ 2 := by simpa using (by positivity : 0 < ‖z‖ ^ 2)
  have h := laplacian_radial (0 : Euc d) z (e0 d) (eprime d) (kprime d)
    (by filter_upwards [lt_mem_nhds hs] with t ht using hasDerivAt_e0 ht)
    (hasDerivAt_eprime hs)
  have h2 := harmonic_aux (d := d) hs
  simp only [sub_zero] at h h2 hs
  have h3 : Efund d = fun x => e0 d (‖x‖ ^ 2) := rfl
  rw [h3]; exact h.trans h2

lemma continuousOn_Efund : ContinuousOn (Efund d) {0}ᶜ := fun z hz =>
  (contDiffAt_Efund 0 hz).continuousAt.continuousWithinAt

lemma powMul_e0 (hd : 2 ≤ d) {y : ℝ} (hy : 0 < y) :
    y ^ (d - 1) * e0 d (y ^ 2) =
      if d = 2 then -(1 / (2 * Real.pi)) * (y * Real.log y)
      else newtonC d / ((d : ℝ) - 2) * y := by
  by_cases h : d = 2
  · subst h
    simp only [e0, ite_true]
    rw [Real.log_pow]
    simp
    ring
  · simp only [e0, h, ite_false]
    have h1 : (y ^ 2) ^ (((2 : ℝ) - d) / 2) = y ^ ((2 : ℝ) - d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
      congr 1; push_cast; ring
    rw [h1]
    have h2 : y ^ (d - 1) = y ^ (((d : ℝ) - 1)) := by
      rw [← Real.rpow_natCast]; congr 1
      rw [Nat.cast_sub (by omega)]; simp
    have h3 : y ^ (((d : ℝ) - 1)) * y ^ ((2 : ℝ) - d) = y := by
      rw [← Real.rpow_add hy]; norm_num
    calc y ^ (d - 1) * (newtonC d / ((d : ℝ) - 2) * y ^ ((2 : ℝ) - d))
        = newtonC d / ((d : ℝ) - 2) * (y ^ (d - 1) * y ^ ((2 : ℝ) - d)) := by ring
      _ = _ := by rw [h2, h3]

lemma integrableOn_Efund_ball (hd : 2 ≤ d) (R : ℝ) :
    IntegrableOn (Efund d) (Metric.ball (0 : Euc d) R) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Euc d) := inferInstance
  have key := (integrableOn_fun_norm_addHaar (volume : Measure (Euc d)) (f := fun y : ℝ => e0 d (y ^ 2))
    (r := R)).mpr
  refine key ?_
  rw [finrank_euclideanSpace_fin]
  let h : ℝ → ℝ := fun y => if d = 2 then -(1 / (2 * Real.pi)) * (y * Real.log y)
      else newtonC d / ((d : ℝ) - 2) * y
  have hc : Continuous h := by
    by_cases h2 : d = 2
    · simp only [h, h2, ite_true]
      exact continuous_const.mul Real.continuous_mul_log
    · simp only [h, h2, ite_false]
      fun_prop
  have hI : IntegrableOn h (Set.Icc 0 R) := hc.integrableOn_Icc
  refine (hI.mono_set Set.Ioo_subset_Icc_self).congr_fun ?_ measurableSet_Ioo
  intro y hy
  simp only [smul_eq_mul]
  exact (powMul_e0 hd hy.1).symm

lemma locallyIntegrable_Efund (hd : 2 ≤ d) : LocallyIntegrable (Efund d) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Euc d)
  exact (integrableOn_Efund_ball hd R).mono_set hR


/-! ### Green's second identity -/

lemma laplacian_eq_sum_fderiv {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (x : Euc d) :
    Laplacian.laplacian f x = ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.basisFun (Fin d) ℝ i)) x
      (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  have h2 := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)).hasFDerivAt.comp x hD
  have h3 : fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.basisFun (Fin d) ℝ i)) x =
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)) ∘SL
        fderiv ℝ (fderiv ℝ f) x := h2.fderiv
  rw [h3]
  simp

lemma px3b_contDiff_fderiv_apply {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (v : Euc d) :
    ContDiff ℝ 1 (fun y => fderiv ℝ f y v) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

lemma green2 {φ g : Euc d → ℝ} (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) :
    ∫ x, φ x * Laplacian.laplacian g x = ∫ x, Laplacian.laplacian φ x * g x := by
  have step : ∀ i : Fin d, ∫ x, φ x * fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.basisFun (Fin d) ℝ i)) x
        (EuclideanSpace.basisFun (Fin d) ℝ i) =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.basisFun (Fin d) ℝ i)) x
        (EuclideanSpace.basisFun (Fin d) ℝ i) * g x := by
    intro i
    set v := EuclideanSpace.basisFun (Fin d) ℝ i with hv
    have hgi := px3b_contDiff_fderiv_apply hg v
    have hφi := px3b_contDiff_fderiv_apply hφ v
    have hgc : HasCompactSupport (fun y => fderiv ℝ g y v) := hc.fderiv_apply ℝ v
    have hcont_g : Continuous g := hg.continuous
    have hcont_φ : Continuous φ := hφ.continuous
    have c1 : Continuous (fun y => fderiv ℝ φ y v) := hφi.continuous
    have c2 : Continuous (fun y => fderiv ℝ g y v) := hgi.continuous
    have c3 : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ g y v) x v) :=
      (hgi.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have c4 : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ φ y v) x v) :=
      (hφi.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have e1 : ∫ x, φ x * fderiv ℝ (fun y => fderiv ℝ g y v) x v =
        - ∫ x, fderiv ℝ φ x v * fderiv ℝ g x v := by
      refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
      · exact (c1.mul c2).integrable_of_hasCompactSupport (hgc.mul_left)
      · exact (hcont_φ.mul c3).integrable_of_hasCompactSupport (by
          have := hgc.fderiv_apply ℝ v
          exact this.mul_left)
      · exact (hcont_φ.mul c2).integrable_of_hasCompactSupport hgc.mul_left
      · intro x _; exact (hφ.differentiable (by norm_num)) x
      · intro x _; exact (hgi.differentiable (by norm_num)) x
    have e2 : ∫ x, fderiv ℝ φ x v * fderiv ℝ g x v =
        - ∫ x, fderiv ℝ (fun y => fderiv ℝ φ y v) x v * g x := by
      refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
      · exact (c4.mul hcont_g).integrable_of_hasCompactSupport hc.mul_left
      · exact (c1.mul c2).integrable_of_hasCompactSupport hgc.mul_left
      · exact (c1.mul hcont_g).integrable_of_hasCompactSupport hc.mul_left
      · intro x _; exact (hφi.differentiable (by norm_num)) x
      · intro x _; exact (hg.differentiable (by norm_num)) x
    rw [e1, e2]; ring
  have hint1 : ∀ i : Fin d, Integrable (fun x => φ x * fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.basisFun (Fin d) ℝ i)) x
        (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
    intro i
    have hgi := px3b_contDiff_fderiv_apply hg (EuclideanSpace.basisFun (Fin d) ℝ i)
    have hgc : HasCompactSupport (fun y => fderiv ℝ g y (EuclideanSpace.basisFun (Fin d) ℝ i)) :=
      hc.fderiv_apply ℝ _
    exact (hφ.continuous.mul ((hgi.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hgc.fderiv_apply ℝ _ |>.mul_left)
  have hint2 : ∀ i : Fin d, Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.basisFun (Fin d) ℝ i)) x
        (EuclideanSpace.basisFun (Fin d) ℝ i) * g x) := by
    intro i
    have hφi := px3b_contDiff_fderiv_apply hφ (EuclideanSpace.basisFun (Fin d) ℝ i)
    exact (((hφi.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hg.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  have l1 : (fun x => φ x * Laplacian.laplacian g x) = fun x => ∑ i : Fin d, φ x * fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.basisFun (Fin d) ℝ i)) x
        (EuclideanSpace.basisFun (Fin d) ℝ i) := by
    ext x; rw [laplacian_eq_sum_fderiv hg x, Finset.mul_sum]
  have l2 : (fun x => Laplacian.laplacian φ x * g x) = fun x => ∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.basisFun (Fin d) ℝ i)) x
        (EuclideanSpace.basisFun (Fin d) ℝ i) * g x := by
    ext x; rw [laplacian_eq_sum_fderiv hφ x, Finset.sum_mul]
  rw [l1, l2, integral_finsetSum _ (fun i _ => hint1 i), integral_finsetSum _ (fun i _ => hint2 i)]
  exact Finset.sum_congr rfl fun i _ => step i


/-! ### Smooth radial truncations of `E` -/

/-- A smooth step: `0` for `x ≤ 1/4`, `1` for `x ≥ 1`. -/
def stp (x : ℝ) : ℝ := Real.smoothTransition ((4 / 3) * x - 1 / 3)

lemma stp_contDiff (n : ℕ∞) : ContDiff ℝ n stp :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

lemma stp_of_le {x : ℝ} (h : x ≤ 1 / 4) : stp x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma stp_of_ge {x : ℝ} (h : 1 ≤ x) : stp x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma stp_mono : Monotone stp := fun a b h =>
  Real.smoothTransition.monotone (by linarith)

lemma stp_nonneg (x : ℝ) : 0 ≤ stp x := Real.smoothTransition.nonneg _

lemma stp_le_one (x : ℝ) : stp x ≤ 1 := Real.smoothTransition.le_one _

lemma deriv_stp_nonneg (x : ℝ) : 0 ≤ deriv stp x := stp_mono.deriv_nonneg

lemma hasDerivAt_stp (x : ℝ) : HasDerivAt stp (deriv stp x) x :=
  (((stp_contDiff 1).differentiable (by simp)) x).hasDerivAt

lemma deriv_stp_of_lt {x : ℝ} (h : x < 1 / 4) : deriv stp x = 0 := by
  have : stp =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds h] with y hy using stp_of_le (le_of_lt hy)
  rw [this.deriv_eq]; simp

lemma deriv_stp_of_gt {x : ℝ} (h : 1 < x) : deriv stp x = 0 := by
  have : stp =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds h] with y hy using stp_of_ge (le_of_lt hy)
  rw [this.deriv_eq]; simp

variable (d) in
/-- Derivative of the truncated profile. -/
def kfun (ε t : ℝ) : ℝ := eprime d t * stp (t / ε ^ 2)

variable (d) in
/-- Derivative of `kfun`. -/
def kdfun (ε t : ℝ) : ℝ :=
  if 0 < t then kprime d t * stp (t / ε ^ 2) + eprime d t * (deriv stp (t / ε ^ 2) / ε ^ 2) else 0

lemma eprime_nonpos (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) : eprime d t ≤ 0 := by
  unfold eprime
  have := newtonC_pos hd
  have : 0 < t ^ (-(d : ℝ) / 2) := Real.rpow_pos_of_pos ht _
  nlinarith

lemma kfun_of_le {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ ε ^ 2 / 4) : kfun d ε t = 0 := by
  unfold kfun
  rw [stp_of_le, mul_zero]
  rw [div_le_iff₀ (by positivity)]; linarith

lemma kfun_of_ge {ε t : ℝ} (hε : 0 < ε) (ht : ε ^ 2 ≤ t) : kfun d ε t = eprime d t := by
  unfold kfun
  rw [stp_of_ge, mul_one]
  rw [le_div_iff₀ (by positivity)]; linarith

lemma kfun_nonpos (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (t : ℝ) : kfun d ε t ≤ 0 := by
  by_cases ht : 0 < t
  · unfold kfun
    exact mul_nonpos_of_nonpos_of_nonneg (eprime_nonpos hd ht) (stp_nonneg _)
  · rw [kfun_of_le hε (by have ht' := not_lt.mp ht; nlinarith [sq_nonneg ε])]

lemma kdfun_of_lt {ε t : ℝ} (hε : 0 < ε) (ht : t < ε ^ 2 / 4) : kdfun d ε t = 0 := by
  unfold kdfun
  split_ifs with h0
  · have h1 : t / ε ^ 2 < 1 / 4 := by rw [div_lt_iff₀ (by positivity)]; linarith
    rw [stp_of_le h1.le, deriv_stp_of_lt h1]; simp
  · rfl

lemma hasDerivAt_kfun {ε : ℝ} (hε : 0 < ε) (t : ℝ) : HasDerivAt (kfun d ε) (kdfun d ε t) t := by
  by_cases ht : 0 < t
  · have h1 := hasDerivAt_eprime (d := d) ht
    have h2 : HasDerivAt (fun t : ℝ => stp (t / ε ^ 2)) (deriv stp (t / ε ^ 2) / ε ^ 2) t := by
      have h3 := (hasDerivAt_stp (t / ε ^ 2)).comp t ((hasDerivAt_id t).div_const (ε ^ 2))
      exact h3.congr_deriv (by ring)
    have := h1.mul h2
    unfold kfun kdfun
    rw [if_pos ht]
    exact this
  · have : kfun d ε =ᶠ[𝓝 t] fun _ => 0 := by
      have : t < ε ^ 2 / 4 := by have ht' := not_lt.mp ht; nlinarith [sq_nonneg ε, pow_pos hε 2]
      filter_upwards [Iio_mem_nhds this] with y hy using kfun_of_le hε hy.le
    have h0 : kdfun d ε t = 0 := kdfun_of_lt hε (by have ht' := not_lt.mp ht; nlinarith [pow_pos hε 2])
    rw [h0]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq this

lemma contDiff_kfun (n : ℕ∞) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ n (kfun d ε) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : 0 < t
  · have h1 : ContDiffAt ℝ n (eprime d) t := by
      unfold eprime
      exact contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne ht.ne')
    have h2 : ContDiffAt ℝ n (fun t : ℝ => stp (t / ε ^ 2)) t :=
      ((stp_contDiff n).contDiffAt).comp t (contDiffAt_id.div_const _)
    exact h1.mul h2
  · have : kfun d ε =ᶠ[𝓝 t] fun _ => 0 := by
      have : t < ε ^ 2 / 4 := by have ht' := not_lt.mp ht; nlinarith [sq_nonneg ε, pow_pos hε 2]
      filter_upwards [Iio_mem_nhds this] with y hy using kfun_of_le hε hy.le
    exact (contDiffAt_const).congr_of_eventuallyEq this


variable (d) in
/-- The truncated profile `g_ε`, equal to `e0` for `s ≥ ε²`. -/
def gfun (ε s : ℝ) : ℝ := e0 d (ε ^ 2) + ∫ t in (ε ^ 2)..s, kfun d ε t

lemma hasDerivAt_gfun {ε : ℝ} (hε : 0 < ε) (s : ℝ) : HasDerivAt (gfun d ε) (kfun d ε s) s := by
  have hc : Continuous (kfun d ε) :=
    (contDiff_kfun (d := d) 0 hε).continuous
  have := (hc.integral_hasStrictDerivAt (ε ^ 2) s).hasDerivAt
  exact this.const_add _

lemma gfun_of_ge {ε s : ℝ} (hε : 0 < ε) (hs : ε ^ 2 ≤ s) : gfun d ε s = e0 d s := by
  have hε2 : 0 < ε ^ 2 := by positivity
  unfold gfun
  have h1 : ∫ t in (ε ^ 2)..s, kfun d ε t = ∫ t in (ε ^ 2)..s, eprime d t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hs] at ht
    exact kfun_of_ge hε ht.1
  rw [h1, intervalIntegral.integral_eq_sub_of_hasDerivAt (f := e0 d)]
  · ring
  · intro t ht
    rw [uIcc_of_le hs] at ht
    exact hasDerivAt_e0 (lt_of_lt_of_le hε2 ht.1)
  · apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hs] at ht
    exact (hasDerivAt_eprime (lt_of_lt_of_le hε2 ht.1)).continuousAt.continuousWithinAt

lemma contDiff_gfun {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 2 (gfun d ε) := by
  have hd : ∀ s, deriv (gfun d ε) s = kfun d ε s := fun s => (hasDerivAt_gfun hε s).deriv
  have hdiff : Differentiable ℝ (gfun d ε) := fun s => (hasDerivAt_gfun hε s).differentiableAt
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨hdiff, by simp, ?_⟩
  have : deriv (gfun d ε) = kfun d ε := funext hd
  rw [this]
  exact contDiff_kfun 1 hε

lemma gfun_antitone (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) : Antitone (gfun d ε) := by
  refine antitone_of_deriv_nonpos (fun s => (hasDerivAt_gfun hε s).differentiableAt) ?_
  intro s
  rw [(hasDerivAt_gfun hε s).deriv]
  exact kfun_nonpos hd hε s

lemma laplacian_gfun {ε : ℝ} (hε : 0 < ε) (c w : Euc d) :
    Laplacian.laplacian (fun x : Euc d => gfun d ε (‖x - c‖ ^ 2)) w =
      2 * d * kfun d ε (‖w - c‖ ^ 2) + 4 * ‖w - c‖ ^ 2 * kdfun d ε (‖w - c‖ ^ 2) :=
  laplacian_radial c w (gfun d ε) (kfun d ε) (kdfun d ε)
    (Eventually.of_forall fun t => hasDerivAt_gfun hε t) (hasDerivAt_kfun hε _)

variable (d) in
/-- Minus the Laplacian of the truncated kernel, as a function of `s = |w|²`. -/
def etaF (ε s : ℝ) : ℝ := -(2 * d * kfun d ε s + 4 * s * kdfun d ε s)

lemma etaF_eq {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) :
    etaF d ε s = (-4 * s * eprime d s / ε ^ 2) * deriv stp (s / ε ^ 2) := by
  unfold etaF kfun kdfun
  rw [if_pos hs]
  have := harmonic_aux (d := d) hs
  field_simp
  linear_combination (-(stp (s / ε ^ 2))) * ε ^ 2 * this

lemma etaF_of_nonpos {ε s : ℝ} (hε : 0 < ε) (hs : s ≤ 0) : etaF d ε s = 0 := by
  have h1 : kfun d ε s = 0 := kfun_of_le hε (by nlinarith [pow_pos hε 2])
  have h2 : kdfun d ε s = 0 := kdfun_of_lt hε (by nlinarith [pow_pos hε 2])
  simp [etaF, h1, h2]

lemma etaF_of_gt {ε s : ℝ} (hε : 0 < ε) (hs : ε ^ 2 < s) : etaF d ε s = 0 := by
  have hs0 : 0 < s := lt_trans (by positivity) hs
  rw [etaF_eq hε hs0, deriv_stp_of_gt]
  · simp
  · rw [lt_div_iff₀ (by positivity)]; linarith

lemma etaF_of_lt {ε s : ℝ} (hε : 0 < ε) (hs : s < ε ^ 2 / 4) : etaF d ε s = 0 := by
  have h1 : kfun d ε s = 0 := kfun_of_le hε hs.le
  have h2 : kdfun d ε s = 0 := kdfun_of_lt hε hs
  simp [etaF, h1, h2]

lemma etaF_nonneg (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (s : ℝ) : 0 ≤ etaF d ε s := by
  by_cases hs : 0 < s
  · rw [etaF_eq hε hs]
    have h1 := eprime_nonpos hd hs
    have h2 := deriv_stp_nonneg (s / ε ^ 2)
    have h3 : 0 ≤ -4 * s * eprime d s := by nlinarith
    positivity
  · rw [etaF_of_nonpos hε (not_lt.mp hs)]

lemma continuous_etaF {ε : ℝ} (hε : 0 < ε) : Continuous (etaF d ε) := by
  have h1 : Continuous (kfun d ε) := (contDiff_kfun (d := d) 0 hε).continuous
  have h2 : Continuous (kdfun d ε) := by
    have : kdfun d ε = deriv (kfun d ε) := funext fun t => (hasDerivAt_kfun hε t).deriv.symm
    rw [this]
    exact (contDiff_kfun (d := d) 1 hε).continuous_deriv le_rfl
  unfold etaF
  fun_prop

lemma radial_aux (m : ℕ) {y : ℝ} (hy : 0 < y) :
    y ^ (m + 1) * (-4 * y ^ 2 * eprime (m + 2) (y ^ 2)) = 2 * newtonC (m + 2) * y := by
  unfold eprime
  have h1 : (y ^ 2) ^ (-((m + 2 : ℕ) : ℝ) / 2) = (y ^ (m + 2))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_neg_one, ← Real.rpow_natCast,
      ← Real.rpow_mul hy.le]
    congr 1
    push_cast; ring
  rw [h1]
  have : y ^ (m + 2) ≠ 0 := by positivity
  field_simp
  ring

lemma integral_etaF (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∫ w : Euc d, etaF d ε (‖w‖ ^ 2) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  have : Nonempty (Fin (m + 2)) := ⟨0⟩
  rw [integral_fun_norm_addHaar volume (fun y : ℝ => etaF (m + 2) ε (y ^ 2))]
  rw [finrank_euclideanSpace_fin]
  have hc := newtonC_pos (d := m + 2) (by omega)
  set c := newtonC (m + 2) with hcdef
  -- the radial integrand is `c * d/dy (stp (y^2/ε^2))`
  have key : ∀ y ∈ Ioi (0 : ℝ), y ^ (m + 2 - 1) • etaF (m + 2) ε (y ^ 2) =
      c * (deriv stp (y ^ 2 / ε ^ 2) * (2 * y / ε ^ 2)) := by
    intro y hy
    have hy : 0 < y := hy
    rw [etaF_eq hε (by positivity), smul_eq_mul]
    have := radial_aux m hy
    have e : m + 2 - 1 = m + 1 := by omega
    rw [e]
    have h2 : y ^ (m + 1) * (-4 * y ^ 2 * eprime (m + 2) (y ^ 2) / ε ^ 2 * deriv stp (y ^ 2 / ε ^ 2)) =
        (y ^ (m + 1) * (-4 * y ^ 2 * eprime (m + 2) (y ^ 2))) / ε ^ 2 * deriv stp (y ^ 2 / ε ^ 2) := by
      ring
    rw [h2, this]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi key]
  have hderiv : ∀ y ∈ Ici (0 : ℝ), HasDerivAt (fun y : ℝ => c * stp (y ^ 2 / ε ^ 2))
      (c * (deriv stp (y ^ 2 / ε ^ 2) * (2 * y / ε ^ 2))) y := by
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / ε ^ 2) (2 * y / ε ^ 2) y := by
      have := ((hasDerivAt_id y).pow 2).div_const (ε ^ 2)
      simpa using this
    have h2 := (hasDerivAt_stp (y ^ 2 / ε ^ 2)).comp y h1
    exact (h2.const_mul c)
  have hcont : Continuous (fun y : ℝ => c * (deriv stp (y ^ 2 / ε ^ 2) * (2 * y / ε ^ 2))) := by
    have : Continuous (deriv stp) := (stp_contDiff 1).continuous_deriv le_rfl
    fun_prop
  have hint : IntegrableOn (fun y : ℝ => c * (deriv stp (y ^ 2 / ε ^ 2) * (2 * y / ε ^ 2))) (Ioi 0) := by
    have hcs : HasCompactSupport (fun y : ℝ => c * (deriv stp (y ^ 2 / ε ^ 2) * (2 * y / ε ^ 2))) := by
      refine HasCompactSupport.intro (isCompact_Icc (a := -ε) (b := ε)) fun y hy => ?_
      have hy' : ε < |y| := by
        by_contra h
        exact hy (abs_le.mp (not_lt.mp h))
      have : 1 < y ^ 2 / ε ^ 2 := by
        rw [lt_div_iff₀ (by positivity)]
        nlinarith [sq_abs y, abs_nonneg y]
      rw [deriv_stp_of_gt this]; simp
    exact (hcont.integrable_of_hasCompactSupport hcs).integrableOn
  have hlim : Tendsto (fun y : ℝ => c * stp (y ^ 2 / ε ^ 2)) atTop (𝓝 c) := by
    have : (fun y : ℝ => c * stp (y ^ 2 / ε ^ 2)) =ᶠ[atTop] fun _ => c := by
      filter_upwards [eventually_ge_atTop ε] with y hy
      rw [stp_of_ge, mul_one]
      rw [le_div_iff₀ (by positivity)]; nlinarith
    exact tendsto_const_nhds.congr' this.symm
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [this]
  simp only [zero_pow two_ne_zero, zero_div, stp_of_le (show (0 : ℝ) ≤ 1 / 4 by norm_num), mul_zero,
    sub_zero]
  have := newtonC_mul (d := m + 2) (by omega)
  simp only [smul_eq_mul, nsmul_eq_mul, Measure.real]
  push_cast at this ⊢
  rw [← hcdef] at this
  nlinarith [this]


lemma e0_antitoneOn (hd : 1 ≤ d) : AntitoneOn (e0 d) (Ioi 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
  · exact fun s hs => (hasDerivAt_e0 hs).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; exact fun s hs => (hasDerivAt_e0 hs).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]; intro s hs
    rw [(hasDerivAt_e0 hs).deriv]; exact eprime_nonpos hd hs

lemma gfun_bound (hd : 1 ≤ d) {ε s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hs : 0 < s) (hsε : s ≤ ε ^ 2) :
    0 ≤ e0 d s - gfun d ε s ∧ e0 d s - gfun d ε s ≤ e0 d s - e0 d 1 := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hD : AntitoneOn (fun s => e0 d s - gfun d ε s) (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
    · intro t ht
      exact ((hasDerivAt_e0 ht).sub (hasDerivAt_gfun hε t)).continuousAt.continuousWithinAt
    · rw [interior_Ioi]; intro t ht
      exact ((hasDerivAt_e0 ht).sub (hasDerivAt_gfun hε t)).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]; intro t ht
      have hh : HasDerivAt (fun s => e0 d s - gfun d ε s) (eprime d t - kfun d ε t) t :=
        (hasDerivAt_e0 ht).sub (hasDerivAt_gfun hε t)
      rw [hh.deriv]
      have h1 := eprime_nonpos hd ht
      unfold kfun
      have := stp_le_one (t / ε ^ 2)
      nlinarith
  have h0 : e0 d (ε ^ 2) - gfun d ε (ε ^ 2) = 0 := by rw [gfun_of_ge hε le_rfl]; ring
  have hlow : 0 ≤ e0 d s - gfun d ε s := by
    have := hD hs hε2 hsε
    simp only at this
    linarith
  refine ⟨hlow, ?_⟩
  have h1 : gfun d ε (ε ^ 2) ≤ gfun d ε s := gfun_antitone hd hε hsε
  rw [gfun_of_ge hε le_rfl] at h1
  have h2 : e0 d 1 ≤ e0 d (ε ^ 2) := e0_antitoneOn hd hε2 (by norm_num : (0 : ℝ) < 1)
    (by nlinarith)
  linarith

lemma etaF_support {ε : ℝ} (hε : 0 < ε) {u : Euc d} (hu : ε < ‖u‖) : etaF d ε (‖u‖ ^ 2) = 0 :=
  etaF_of_gt hε (by nlinarith)

lemma integrable_etaF (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun u : Euc d => etaF d ε (‖u‖ ^ 2)) := by
  have hc : Continuous (fun u : Euc d => etaF d ε (‖u‖ ^ 2)) :=
    (continuous_etaF hε).comp (continuous_norm.pow 2)
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) ε) ?_)
  intro u hu
  exact etaF_support hε (by simpa using hu)

lemma approx_identity (hd : 2 ≤ d) {g : Euc d → ℝ} (hg : Continuous g) (z : Euc d) :
    Tendsto (fun ε : ℝ => ∫ u : Euc d, etaF d ε (‖u‖ ^ 2) * g (z + u)) (𝓝[>] 0) (𝓝 (g z)) := by
  rw [Metric.tendsto_nhds]
  intro τ hτ
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.mp (hg.continuousAt (x := z)) (τ / 2) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  have hε0 : 0 < ε := hε.1
  have hint := integral_etaF hd hε0
  have hI := integrable_etaF hd hε0
  have hJ : Integrable (fun u : Euc d => etaF d ε (‖u‖ ^ 2) * g (z + u)) := by
    have hc : Continuous (fun u : Euc d => etaF d ε (‖u‖ ^ 2) * g (z + u)) :=
      ((continuous_etaF hε0).comp (continuous_norm.pow 2)).mul (hg.comp (continuous_const.add continuous_id))
    refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) ε) ?_)
    intro u hu
    rw [etaF_support hε0 (by simpa using hu), zero_mul]
  have key : (∫ u : Euc d, etaF d ε (‖u‖ ^ 2) * g (z + u)) - g z =
      ∫ u : Euc d, etaF d ε (‖u‖ ^ 2) * (g (z + u) - g z) := by
    have : ∫ u : Euc d, etaF d ε (‖u‖ ^ 2) * (g (z + u) - g z) =
        (∫ u : Euc d, etaF d ε (‖u‖ ^ 2) * g (z + u)) - ∫ u : Euc d, etaF d ε (‖u‖ ^ 2) * g z := by
      rw [← integral_sub hJ (hI.mul_const _)]
      congr 1; ext u; ring
    rw [this, integral_mul_const, hint]; ring
  rw [Real.dist_eq, key]
  have hb : ∀ u : Euc d, ‖etaF d ε (‖u‖ ^ 2) * (g (z + u) - g z)‖ ≤ (τ / 2) * etaF d ε (‖u‖ ^ 2) := by
    intro u
    by_cases hu : ε < ‖u‖
    · rw [etaF_support hε0 hu]; simp
    · have hu' : ‖u‖ < δ := lt_of_le_of_lt (not_lt.mp hu) hε.2
      have h1 := hδg (x := z + u) (by rw [dist_eq_norm, add_sub_cancel_left]; exact hu')
      rw [Real.dist_eq] at h1
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (etaF_nonneg (by omega) hε0 _), Real.norm_eq_abs]
      nlinarith [etaF_nonneg (d := d) (by omega) hε0 (‖u‖ ^ 2)]
  have := norm_integral_le_of_norm_le (hI.const_mul (τ / 2)) (Eventually.of_forall hb)
  rw [integral_const_mul, hint] at this
  rw [← Real.norm_eq_abs]
  linarith

lemma continuous_laplacian {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) :
    Continuous (Laplacian.laplacian g) := by
  have : Laplacian.laplacian g = fun x => ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.basisFun (Fin d) ℝ i)) x
      (EuclideanSpace.basisFun (Fin d) ℝ i) := funext fun x => laplacian_eq_sum_fderiv hg x
  rw [this]
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((px3b_contDiff_fderiv_apply hg _).continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma laplacian_hasCompactSupport {g : Euc d → ℝ} (hc : HasCompactSupport g) :
    HasCompactSupport (Laplacian.laplacian g) := by
  refine hc.mono' ?_
  intro x hx
  by_contra hxs
  have h0 : g =ᶠ[𝓝 x] fun _ => 0 := by
    have : (tsupport g)ᶜ ∈ 𝓝 x := (isClosed_tsupport g).isOpen_compl.mem_nhds hxs
    filter_upwards [this] with y hy using image_eq_zero_of_notMem_tsupport hy
  have := (InnerProductSpace.laplacian_congr_nhds h0).eq_of_nhds
  apply hx
  simpa using this

/-- The weak form of `-ΔE = δ`. -/
theorem weak_poisson (hd : 2 ≤ d) {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g)
    (z : Euc d) :
    ∫ w, Efund d w * Laplacian.laplacian g (z - w) = - g z := by
  set Dg := Laplacian.laplacian g with hDg
  have hDgc : Continuous Dg := continuous_laplacian hg
  have hDgs : HasCompactSupport Dg := laplacian_hasCompactSupport hc
  have hDg' : Continuous (fun w => Dg (z - w)) := hDgc.comp (continuous_const.sub continuous_id)
  have hDgs' : HasCompactSupport (fun w => Dg (z - w)) := hDgs.comp_homeomorph (Homeomorph.subLeft z)
  have hE := locallyIntegrable_Efund hd
  have hEint : Integrable (fun w => Efund d w * Dg (z - w)) :=
    hE.integrable_smul_right_of_hasCompactSupport hDg' hDgs'
  obtain ⟨M, hM⟩ := hDg'.bounded_above_of_compact_support hDgs'
  -- the truncated kernel and its identity
  have hmain : ∀ ε : ℝ, 0 < ε →
      ∫ w, gfun d ε (‖w‖ ^ 2) * Dg (z - w) = - ∫ w, etaF d ε (‖w‖ ^ 2) * g (z + w) := by
    intro ε hε
    have hφ : ContDiff ℝ 2 (fun w : Euc d => gfun d ε (‖w - z‖ ^ 2)) :=
      (contDiff_gfun hε).comp (contDiff_id.sub contDiff_const |>.norm_sq ℝ)
    have e1 : ∫ w, gfun d ε (‖w‖ ^ 2) * Dg (z - w) = ∫ w, gfun d ε (‖w - z‖ ^ 2) * Dg w := by
      rw [← integral_sub_left_eq_self (fun w => gfun d ε (‖w‖ ^ 2) * Dg (z - w)) volume z]
      congr 1; ext w
      rw [sub_sub_cancel, norm_sub_rev]
    have e2 := green2 hφ hg hc
    have e3 : Laplacian.laplacian (fun w : Euc d => gfun d ε (‖w - z‖ ^ 2)) =
        fun w => - etaF d ε (‖w - z‖ ^ 2) := by
      ext w; rw [laplacian_gfun hε z w]; simp [etaF]
    rw [e1, hDg, e2, e3]
    have e4 : ∫ w, - etaF d ε (‖w - z‖ ^ 2) * g w = - ∫ w, etaF d ε (‖w‖ ^ 2) * g (z + w) := by
      rw [← integral_neg]
      rw [← integral_sub_right_eq_self (fun w => -(etaF d ε (‖w‖ ^ 2) * g (z + w))) z]
      congr 1; ext w
      simp
    exact e4
  have hEε : ∀ ε : ℝ, 0 < ε → Integrable (fun w : Euc d => gfun d ε (‖w‖ ^ 2) * Dg (z - w)) := by
    intro ε hε
    have hgc : Continuous (fun w : Euc d => gfun d ε (‖w‖ ^ 2)) :=
      (contDiff_gfun hε).continuous.comp (continuous_norm.pow 2)
    exact (hgc.mul hDg').integrable_of_hasCompactSupport hDgs'.mul_left
  -- dominated convergence for the difference
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z)
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hae0 : ∀ᵐ w : Euc d, w ≠ 0 := by
    have := (Set.countable_singleton (0 : Euc d)).ae_notMem (volume : Measure (Euc d))
    filter_upwards [this] with w hw using by simpa using hw
  have hlim1 : Tendsto (fun ε : ℝ => ∫ w, (Efund d w - gfun d ε (‖w‖ ^ 2)) * Dg (z - w)) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Euc d)))
      (l := 𝓝[>] (0 : ℝ))
      (F := fun ε w => (Efund d w - gfun d ε (‖w‖ ^ 2)) * Dg (z - w)) (f := fun _ => 0)
      (bound := fun w => M * ((Metric.ball (0 : Euc d) 1).indicator (fun w => |Efund d w| + |e0 d 1|) w))
      ?_ ?_ ?_ ?_
    · simpa using this
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
      have hgc : Continuous (fun w : Euc d => gfun d ε (‖w‖ ^ 2)) :=
        (contDiff_gfun hε.1).continuous.comp (continuous_norm.pow 2)
      exact (hE.aestronglyMeasurable.sub hgc.aestronglyMeasurable).mul hDg'.aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
      filter_upwards [hae0] with w hw0
      have hbnd0 : 0 ≤ M * ((Metric.ball (0 : Euc d) 1).indicator (fun w => |Efund d w| + |e0 d 1|) w) := by
        apply mul_nonneg hM0
        apply Set.indicator_nonneg
        intro x _; positivity
      by_cases hw1 : ε ≤ ‖w‖
      · have : Efund d w = gfun d ε (‖w‖ ^ 2) := by
          rw [gfun_of_ge hε.1 (by nlinarith [hε.1])]; rfl
        simp only [this, sub_self, zero_mul, norm_zero]
        exact hbnd0
      · have hw1' := not_le.mp hw1
        have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
        have hwball : w ∈ Metric.ball (0 : Euc d) 1 := by
          rw [mem_ball_zero_iff]; linarith [hε.2]
        have hb := gfun_bound (d := d) (by omega) hε.1 hε.2.le (s := ‖w‖ ^ 2) (by positivity)
          (by nlinarith)
        rw [Set.indicator_of_mem hwball]
        rw [norm_mul, Real.norm_eq_abs]
        have h1 : |Efund d w - gfun d ε (‖w‖ ^ 2)| ≤ |Efund d w| + |e0 d 1| := by
          have : Efund d w = e0 d (‖w‖ ^ 2) := rfl
          rw [this, abs_of_nonneg hb.1]
          have := hb.2
          have h2 := le_abs_self (e0 d (‖w‖ ^ 2))
          have h3 := neg_abs_le (e0 d 1)
          linarith
        calc |Efund d w - gfun d ε (‖w‖ ^ 2)| * ‖Dg (z - w)‖
            ≤ (|Efund d w| + |e0 d 1|) * M :=
              mul_le_mul h1 (hM w) (norm_nonneg _) (by positivity)
          _ = _ := by ring
    · refine Integrable.const_mul ?_ M
      rw [integrable_indicator_iff measurableSet_ball]
      exact ((integrableOn_Efund_ball hd 1).norm.add (integrableOn_const (measure_ball_lt_top.ne)))
    · filter_upwards [hae0] with w hw0
      have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hwpos] with ε hε
      have : Efund d w = gfun d ε (‖w‖ ^ 2) := by
        rw [gfun_of_ge hε.1 (by nlinarith [hε.1, hε.2])]; rfl
      simp [this]
  have hlim2 := (approx_identity hd hg.continuous z).neg
  have hsum := hlim1.add hlim2
  have hconst : Tendsto (fun _ : ℝ => ∫ w, Efund d w * Dg (z - w)) (𝓝[>] 0)
      (𝓝 (0 + -g z)) := by
    refine hsum.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
    show (∫ w, (Efund d w - gfun d ε (‖w‖ ^ 2)) * Dg (z - w)) +
      -(∫ u, etaF d ε (‖u‖ ^ 2) * g (z + u)) = _
    rw [← hmain ε hε.1, ← integral_add (hEint.sub (hEε ε hε.1) |>.congr (Eventually.of_forall fun w => by simp only [Pi.sub_apply]; ring)) (hEε ε hε.1)]
    congr 1; ext w; ring
  have := tendsto_nhds_unique tendsto_const_nhds hconst
  linarith


/-! ### Derivatives of convolutions -/

lemma fderiv_conv_apply {f h : Euc d → ℝ} (hf : LocallyIntegrable f) (hh : ContDiff ℝ 1 h)
    (hch : HasCompactSupport h) (x v : Euc d) :
    fderiv ℝ (fun y => ∫ t, f t * h (y - t)) x v = ∫ t, f t * fderiv ℝ h (x - t) v := by
  have h1 := hch.hasFDerivAt_convolution_right (μ := (volume : Measure (Euc d)))
    (ContinuousLinearMap.mul ℝ ℝ) hf hh x
  have h2 : (fun y => ∫ t, f t * h (y - t)) = f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] h := by
    ext y; simp [convolution_def]
  rw [h2, h1.fderiv]
  simp only [convolution_def]
  have hint : Integrable (fun t => f t • fderiv ℝ h (x - t)) := by
    have hc : Continuous (fun t => fderiv ℝ h (x - t)) :=
      (hh.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)
    have hs : HasCompactSupport (fun t => fderiv ℝ h (x - t)) :=
      hch.fderiv (𝕜 := ℝ) |>.comp_homeomorph (Homeomorph.subLeft x)
    exact hf.integrable_smul_right_of_hasCompactSupport hc hs
  have := ContinuousLinearMap.integral_comp_comm (ContinuousLinearMap.apply ℝ ℝ v) hint
  have e : ∀ t, ((ContinuousLinearMap.precompR (Euc d) (ContinuousLinearMap.mul ℝ ℝ)) (f t))
      (fderiv ℝ h (x - t)) = f t • fderiv ℝ h (x - t) := by
    intro t; ext w; simp
  simp_rw [e]
  rw [← ContinuousLinearMap.apply_apply' v, ← ContinuousLinearMap.integral_comp_comm _ hint]
  simp

lemma contDiff_conv {f g : Euc d → ℝ} (hf : LocallyIntegrable f) (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) : ContDiff ℝ 2 (fun y => ∫ t, f t * g (y - t)) := by
  have := hc.contDiff_convolution_right (μ := (volume : Measure (Euc d))) (n := 2)
    (ContinuousLinearMap.mul ℝ ℝ) hf (by exact_mod_cast hg)
  have h2 : (fun y => ∫ t, f t * g (y - t)) = f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g := by
    ext y; simp [convolution_def]
  rw [h2]
  exact_mod_cast this

lemma laplacian_conv {f g : Euc d → ℝ} (hf : LocallyIntegrable f) (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) (x : Euc d) :
    Laplacian.laplacian (fun y => ∫ t, f t * g (y - t)) x =
      ∫ t, f t * Laplacian.laplacian g (x - t) := by
  have hC := contDiff_conv hf hg hc
  rw [laplacian_eq_sum_fderiv hC x]
  have step : ∀ i : Fin d,
      fderiv ℝ (fun y => fderiv ℝ (fun y => ∫ t, f t * g (y - t)) y
        (EuclideanSpace.basisFun (Fin d) ℝ i)) x (EuclideanSpace.basisFun (Fin d) ℝ i) =
      ∫ t, f t * fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.basisFun (Fin d) ℝ i)) (x - t)
        (EuclideanSpace.basisFun (Fin d) ℝ i) := by
    intro i
    have h1 : (fun y => fderiv ℝ (fun y => ∫ t, f t * g (y - t)) y
        (EuclideanSpace.basisFun (Fin d) ℝ i)) =
        fun y => ∫ t, f t * (fun y => fderiv ℝ g y (EuclideanSpace.basisFun (Fin d) ℝ i)) (y - t) := by
      ext y
      exact fderiv_conv_apply hf (hg.of_le (by norm_num)) hc y _
    rw [h1]
    exact fderiv_conv_apply hf (px3b_contDiff_fderiv_apply hg _) (hc.fderiv_apply ℝ _) x _
  simp_rw [step]
  have hint : ∀ i : Fin d, Integrable (fun t => f t *
      fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.basisFun (Fin d) ℝ i)) (x - t)
        (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
    intro i
    have hgi := px3b_contDiff_fderiv_apply hg (EuclideanSpace.basisFun (Fin d) ℝ i)
    have hc1 : Continuous (fun t => fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.basisFun (Fin d) ℝ i)) (x - t)
        (EuclideanSpace.basisFun (Fin d) ℝ i)) :=
      ((hgi.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp (continuous_const.sub continuous_id)
    have hs1 : HasCompactSupport (fun t => fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.basisFun (Fin d) ℝ i)) (x - t)
        (EuclideanSpace.basisFun (Fin d) ℝ i)) :=
      ((hc.fderiv_apply ℝ _).fderiv_apply ℝ _).comp_homeomorph (Homeomorph.subLeft x)
    exact hf.integrable_smul_right_of_hasCompactSupport hc1 hs1
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  congr 1; ext t
  rw [laplacian_eq_sum_fderiv hg (x - t), Finset.mul_sum]

/-! ### The Poisson equation for the Newton potential -/

/-- Splitting of an integrable compactly supported `H` that is `C²` near `z`: a `C²` compactly
supported part agreeing with `H` near `z`, and a remainder vanishing near `z`. -/
lemma exists_split {H : Euc d → ℝ} {z : Euc d}
    (hHz : ContDiffAt ℝ 2 H z) :
    ∃ r : ℝ, 0 < r ∧ ∃ H1 : Euc d → ℝ, ContDiff ℝ 2 H1 ∧ HasCompactSupport H1 ∧
      (∀ w ∈ Metric.ball z (r / 4), H1 w = H w) ∧ (∀ w, H1 w ≠ 0 → w ∈ Metric.ball z r) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hHz.eventually (by simp))
  let η : ContDiffBump z := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hηr : η.rOut = r / 2 := rfl
  have hηi : η.rIn = r / 4 := rfl
  refine ⟨r, hr, fun w => η w * H w, ?_, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hw : w ∈ Metric.ball z r
    · exact (η.contDiffAt (n := 2)).mul (hball w hw)
    · have hw' : w ∉ tsupport η := by
        rw [ContDiffBump.tsupport_eq, hηr]
        intro h
        apply hw
        rw [Metric.mem_ball]
        have := mem_closedBall_iff_norm.mp h
        rw [dist_eq_norm]
        linarith
      have : (fun w => η w * H w) =ᶠ[𝓝 w] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hw'] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq this
  · exact η.hasCompactSupport.mul_right
  · intro w hw
    have : η w = 1 := ContDiffBump.one_of_mem_closedBall _ (by
      rw [hηi]; exact Metric.ball_subset_closedBall hw)
    simp [this]
  · intro w hw
    have hη : η w ≠ 0 := left_ne_zero_of_mul hw
    have : w ∈ Function.support η := hη
    rw [ContDiffBump.support_eq, hηr] at this
    exact Metric.ball_subset_ball (by linarith) this

/-- A smooth compactly supported kernel agreeing with `E` on the annulus `r/8 ≤ |x| ≤ R`. -/
lemma exists_Ktilde {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    ∃ K : Euc d → ℝ, ContDiff ℝ 2 K ∧ HasCompactSupport K ∧
      (∀ x : Euc d, r / 8 ≤ ‖x‖ → ‖x‖ ≤ R → K x = Efund d x) ∧
      (∀ x : Euc d, r / 8 < ‖x‖ → ‖x‖ < R → Laplacian.laplacian K x = 0) := by
  let b1 : ContDiffBump (0 : Euc d) := ⟨r / 16, r / 8, by positivity, by linarith⟩
  let b2 : ContDiffBump (0 : Euc d) := ⟨R, R + 1, hR, by linarith⟩
  have hb1 : ∀ x : Euc d, r / 8 ≤ ‖x‖ → b1 x = 0 := fun x hx =>
    ContDiffBump.zero_of_le_dist _ (by simpa [dist_zero_right] using hx)
  have hb2 : ∀ x : Euc d, ‖x‖ ≤ R → b2 x = 1 := fun x hx =>
    ContDiffBump.one_of_mem_closedBall _ (by simpa using hx)
  have hKeq : ∀ x : Euc d, r / 8 ≤ ‖x‖ → ‖x‖ ≤ R →
      b2 x * ((1 - b1 x) * Efund d x) = Efund d x := by
    intro x h1 h2
    rw [hb1 x h1, hb2 x h2]; ring
  refine ⟨fun x => b2 x * ((1 - b1 x) * Efund d x), ?_, b2.hasCompactSupport.mul_right, hKeq, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hw : w = 0
    · subst hw
      have : (fun x => b2 x * ((1 - b1 x) * Efund d x)) =ᶠ[𝓝 (0 : Euc d)] fun _ => 0 := by
        filter_upwards [b1.eventuallyEq_one] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq this
    · exact b2.contDiffAt.mul ((contDiffAt_const.sub b1.contDiffAt).mul (contDiffAt_Efund 2 hw))
  · intro x h1 h2
    have hx0 : x ≠ 0 := by
      intro h; rw [h] at h1; simp at h1; linarith
    have : (fun x => b2 x * ((1 - b1 x) * Efund d x)) =ᶠ[𝓝 x] Efund d := by
      have hopen : {y : Euc d | r / 8 < ‖y‖ ∧ ‖y‖ < R} ∈ 𝓝 x :=
        (isOpen_lt continuous_const continuous_norm |>.inter (isOpen_lt continuous_norm continuous_const)).mem_nhds
          ⟨h1, h2⟩
      filter_upwards [hopen] with y hy using hKeq y hy.1.le hy.2.le
    rw [(InnerProductSpace.laplacian_congr_nhds this).eq_of_nhds]
    exact laplacian_Efund hx0

theorem newton_poisson_aux (hd : 2 ≤ d) {H : Euc d → ℝ} (hH : Integrable H)
    (hHc : HasCompactSupport H) {z : Euc d} (hHz : ContDiffAt ℝ 2 H z) :
    ContDiffAt ℝ 2 (fun y => ∫ w, Efund d (y - w) * H w) z ∧
      Laplacian.laplacian (fun y => ∫ w, Efund d (y - w) * H w) z = - H z := by
  obtain ⟨r, hr, H1, hH1, hH1c, hH1eq, hH1supp⟩ := exists_split hHz
  have hE := locallyIntegrable_Efund hd
  have hH1int : Integrable H1 := hH1.continuous.integrable_of_hasCompactSupport hH1c
  set H2 : Euc d → ℝ := fun w => H w - H1 w with hH2def
  have hH2int : Integrable H2 := hH.sub hH1int
  have hH2z : ∀ w ∈ Metric.ball z (r / 4), H2 w = 0 := fun w hw => by
    simp [hH2def, hH1eq w hw]
  obtain ⟨Rs, hRs⟩ := hHc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set R0 : ℝ := |Rs| + ‖z‖ + r with hR0
  have hH2supp : ∀ w, H2 w ≠ 0 → ‖w‖ ≤ R0 := by
    intro w hw
    by_cases hHw : H w = 0
    · have : H1 w ≠ 0 := by
        intro h; apply hw; simp [hH2def, hHw, h]
      have := hH1supp w this
      rw [Metric.mem_ball, dist_eq_norm] at this
      have := norm_le_insert' w z
      have : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
        have := norm_le_norm_add_norm_sub' w z
        linarith
      linarith [abs_nonneg Rs]
    · have : w ∈ tsupport H := subset_tsupport _ hHw
      have := hRs this
      rw [mem_closedBall_zero_iff] at this
      linarith [le_abs_self Rs, norm_nonneg z]
  set R : ℝ := ‖z‖ + r + R0 + 1 with hRdef
  have hRpos : 0 < R := by
    have := norm_nonneg z
    have := abs_nonneg Rs
    simp only [hRdef, hR0]; linarith
  obtain ⟨K, hK, hKc, hKeq, hKlap⟩ := exists_Ktilde (d := d) hr hRpos
  -- the two convolution pieces
  set A : Euc d → ℝ := fun y => ∫ t, Efund d t * H1 (y - t) with hAdef
  set B : Euc d → ℝ := fun y => ∫ w, H2 w * K (y - w) with hBdef
  have hA : ContDiff ℝ 2 A := contDiff_conv hE hH1 hH1c
  have hB : ContDiff ℝ 2 B := contDiff_conv hH2int.locallyIntegrable hK hKc
  have hUeq : (fun y => ∫ w, Efund d (y - w) * H w) =ᶠ[𝓝 z] fun y => A y + B y := by
    filter_upwards [Metric.ball_mem_nhds z (by linarith : (0 : ℝ) < r / 8)] with y hy
    have hy' : ‖y - z‖ < r / 8 := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    have hsub : ∫ w, Efund d (y - w) * H w = ∫ t, Efund d t * H (y - t) := by
      rw [← integral_sub_left_eq_self (fun t => Efund d t * H (y - t)) volume y]
      congr 1; ext w; rw [sub_sub_cancel]
    have i1 : Integrable (fun t => Efund d t * H1 (y - t)) :=
      hE.integrable_smul_right_of_hasCompactSupport
        (hH1.continuous.comp (continuous_const.sub continuous_id))
        (hH1c.comp_homeomorph (Homeomorph.subLeft y))
    obtain ⟨C, hC⟩ := hK.continuous.bounded_above_of_compact_support hKc
    have hKE : ∀ t, Efund d t * H2 (y - t) = K t * H2 (y - t) := by
      intro t
      by_cases ht : H2 (y - t) = 0
      · simp [ht]
      · have h1 : r / 4 ≤ ‖(y - t) - z‖ := by
          by_contra hlt
          exact ht (hH2z _ (by rw [Metric.mem_ball, dist_eq_norm]; linarith [not_le.mp hlt]))
        have h2 := hH2supp _ ht
        have h3 : r / 8 ≤ ‖t‖ := by
          have : ‖(y - t) - z‖ ≤ ‖t‖ + ‖y - z‖ := by
            have := norm_sub_le (y - z) t
            rw [show (y - t) - z = (y - z) - t by abel]
            linarith
          linarith
        have h4 : ‖t‖ ≤ R := by
          have : ‖t‖ ≤ ‖y‖ + ‖y - t‖ := by
            have := norm_sub_le y (y - t)
            rw [sub_sub_cancel] at this
            linarith
          have : ‖y‖ ≤ ‖z‖ + ‖y - z‖ := by
            have := norm_le_norm_add_norm_sub' y z
            linarith
          simp only [hRdef]; linarith
        rw [hKeq t h3 h4]
    have i2 : Integrable (fun t => Efund d t * H2 (y - t)) := by
      simp_rw [hKE]
      exact (hH2int.comp_sub_left y).bdd_mul hK.continuous.aestronglyMeasurable
        (Eventually.of_forall hC)
    have hB' : B y = ∫ t, K t * H2 (y - t) := by
      rw [hBdef]
      simp only
      rw [← integral_sub_left_eq_self (fun w => H2 w * K (y - w)) volume y]
      congr 1; ext t; rw [sub_sub_cancel, mul_comm]
    have hA' : A y = ∫ t, Efund d t * H1 (y - t) := rfl
    rw [hsub, hA', hB', ← integral_add i1 (by simpa only [hKE] using i2)]
    congr 1; ext t
    rw [← hKE t]
    simp only [hH2def]
    ring
  have hcd : ContDiffAt ℝ 2 (fun y => ∫ w, Efund d (y - w) * H w) z :=
    (hA.add hB).contDiffAt.congr_of_eventuallyEq hUeq
  refine ⟨hcd, ?_⟩
  rw [(InnerProductSpace.laplacian_congr_nhds hUeq).eq_of_nhds]
  have hsum : Laplacian.laplacian (A + B) z = Laplacian.laplacian A z + Laplacian.laplacian B z :=
    hA.contDiffAt.laplacian_add hB.contDiffAt
  have hAz : Laplacian.laplacian A z = - H1 z := by
    rw [hAdef, laplacian_conv hE hH1 hH1c z]
    exact weak_poisson hd hH1 hH1c z
  have hBz : Laplacian.laplacian B z = 0 := by
    rw [hBdef, laplacian_conv hH2int.locallyIntegrable hK hKc z]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : H2 t = 0
    · simp [ht]
    · show H2 t * Laplacian.laplacian K (z - t) = 0
      have h1 : r / 4 ≤ ‖t - z‖ := by
        by_contra hlt
        exact ht (hH2z t (by rw [Metric.mem_ball, dist_eq_norm]; linarith [not_le.mp hlt]))
      have h2 := hH2supp t ht
      rw [hKlap (z - t) (by rw [norm_sub_rev]; linarith) (by
        have := norm_sub_le z t
        simp only [hRdef]; linarith)]
      simp
  have : (fun y => A y + B y) = A + B := rfl
  rw [this, hsum, hAz, hBz, hH1eq z (Metric.mem_ball_self (by positivity))]
  simp


/-- The Poisson equation `-2ν Δ (Γ * H) = H` for the Newton kernel `Γ`, a compactly supported
integrable `H` that is `C²` near `z`. -/
theorem newtonKernel_poisson (hd : 2 ≤ d) {ν : ℝ} (hν : 0 < ν) {H : Euc d → ℝ}
    (hH : Integrable H) (hHc : HasCompactSupport H) {z : Euc d} (hHz : ContDiffAt ℝ 2 H z) :
    -(2 * ν) * Laplacian.laplacian (fun z' => ∫ w, newtonKernel d ν (z' - w) * H w) z = H z := by
  obtain ⟨hcd, hlap⟩ := newton_poisson_aux hd hH hHc hHz
  have h1 : (fun z' => ∫ w, newtonKernel d ν (z' - w) * H w) =
      (1 / (2 * ν)) • fun y => ∫ w, Efund d (y - w) * H w := by
    ext y
    simp only [Pi.smul_apply, smul_eq_mul, newtonKernel_eq, mul_assoc]
    rw [integral_const_mul]
  rw [h1, InnerProductSpace.laplacian_smul _ hcd, hlap]
  have : ν ≠ 0 := hν.ne'
  simp only [smul_eq_mul]
  field_simp

/-! ### Chart facts for the Poisson packet -/

lemma one_add_abs_log_pow_le (b : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 → (1 + |Real.log y|) ^ b ≤ C * y ^ (-δ) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · refine ⟨1, one_pos, fun y hy hy1 => ?_⟩
    simp only [pow_zero, one_mul]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by linarith)
  · have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    set a : ℝ := δ / b with ha
    have ha0 : 0 < a := by positivity
    refine ⟨(1 + 1 / a) ^ b, by positivity, fun y hy hy1 => ?_⟩
    have h1 : 1 ≤ y ^ (-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by linarith)
    have h2 : |Real.log y| ≤ y ^ (-a) / a := by
      have hl : Real.log y ≤ 0 := Real.log_nonpos hy.le hy1
      rw [abs_of_nonpos hl, ← Real.log_inv]
      have := Real.log_le_rpow_div (inv_nonneg.mpr hy.le) ha0
      rwa [Real.inv_rpow hy.le, ← Real.rpow_neg hy.le] at this
    have h3 : 1 + |Real.log y| ≤ (1 + 1 / a) * y ^ (-a) := by
      have : y ^ (-a) / a = (1 / a) * y ^ (-a) := by ring
      nlinarith
    calc (1 + |Real.log y|) ^ b ≤ ((1 + 1 / a) * y ^ (-a)) ^ b :=
          pow_le_pow_left₀ (by positivity) h3 b
      _ = (1 + 1 / a) ^ b * (y ^ (-a)) ^ b := mul_pow _ _ _
      _ = (1 + 1 / a) ^ b * y ^ (-δ) := by
          rw [← Real.rpow_natCast (y ^ (-a)) b, ← Real.rpow_mul hy.le]
          congr 2
          rw [ha]; field_simp

lemma integrableOn_rpow_log (hd : 1 ≤ d) {σ : ℝ} (hσ : σ < d) (b : ℕ) {R : ℝ} (hR : R ≤ 1) :
    IntegrableOn (fun w : Euc d => ‖w‖ ^ (-σ) * (1 + |Real.log ‖w‖|) ^ b) (Metric.ball 0 R) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  refine (integrableOn_fun_norm_addHaar (volume : Measure (Euc d))
    (f := fun y : ℝ => y ^ (-σ) * (1 + |Real.log y|) ^ b) (r := R)).mpr ?_
  rw [finrank_euclideanSpace_fin]
  by_cases hR0 : R ≤ 0
  · rw [Ioo_eq_empty (by linarith)]; exact integrableOn_empty
  have hR0' := not_le.mp hR0
  set δ : ℝ := ((d : ℝ) - σ) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨C, hC, hCb⟩ := one_add_abs_log_pow_le b hδ0
  have hint : IntegrableOn (fun y : ℝ => C * y ^ (((d : ℝ) - 1) - σ - δ)) (Ioo 0 R) := by
    refine Integrable.const_mul ?_ C
    have h1 : IntervalIntegrable (fun y : ℝ => y ^ (((d : ℝ) - 1) - σ - δ)) volume 0 R :=
      intervalIntegral.intervalIntegrable_rpow' (by rw [hδ]; linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR0'.le] at h1
    exact h1.mono_set Ioo_subset_Ioc_self
  refine Integrable.mono' hint ?_ ?_
  · have : ContinuousOn (fun y : ℝ => y ^ (d - 1) • (y ^ (-σ) * (1 + |Real.log y|) ^ b)) (Ioo 0 R) := by
      intro y hy
      have hy0 : y ≠ 0 := hy.1.ne'
      refine ContinuousAt.continuousWithinAt ?_
      simp only [smul_eq_mul]
      have : ContinuousAt (fun y : ℝ => y ^ (-σ)) y := Real.continuousAt_rpow_const _ _ (Or.inl hy0)
      have h2 : ContinuousAt Real.log y := Real.continuousAt_log hy0
      fun_prop (disch := assumption)
    exact this.aestronglyMeasurable measurableSet_Ioo
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun y hy => ?_)
    have hy0 : 0 < y := hy.1
    have hy1 : y ≤ 1 := by linarith [hy.2]
    have h1 := hCb y hy0 hy1
    simp only [smul_eq_mul, norm_mul]
    rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ y ^ (d - 1)),
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ y ^ (-σ)),
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (1 + |Real.log y|) ^ b)]
    have h2 : y ^ (d - 1) = y ^ (((d : ℝ) - 1)) := by
      rw [← Real.rpow_natCast]; congr 1
      rw [Nat.cast_sub hd]; simp
    have h3 : C * y ^ (((d : ℝ) - 1) - σ - δ) =
        y ^ (((d : ℝ) - 1)) * (y ^ (-σ) * (C * y ^ (-δ))) := by
      rw [show ((d : ℝ) - 1) - σ - δ = ((d : ℝ) - 1) + (-σ) + (-δ) by ring,
        Real.rpow_add hy0, Real.rpow_add hy0]
      ring
    rw [h3, h2]
    have : 0 ≤ y ^ (-σ) := by positivity
    have : 0 ≤ y ^ (((d : ℝ) - 1)) := by positivity
    gcongr

lemma mk_chart_ne (X w : Euc d) (hw0 : w ≠ 0) (hw : ‖w‖ < 1) :
    Torus.mk (X + (1 / 2 : ℝ) • w) ≠ Torus.mk (X - (1 / 2 : ℝ) • w) := by
  intro h
  apply hw0
  ext i
  have h1 := congr_fun h i
  simp only [Torus.mk, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h1
  have h2 := (QuotientAddGroup.eq).mp h1
  rw [AddSubgroup.mem_zmultiples_iff] at h2
  obtain ⟨k, hk⟩ := h2
  have hk' : (k : ℝ) = -w i := by
    have : ((k • (1 : ℝ) : ℝ)) = (k : ℝ) := by simp
    rw [← this, hk]; ring
  have hwi : |w i| < 1 := by
    have := PiLp.norm_apply_le w i
    rw [Real.norm_eq_abs] at this
    linarith
  have hk0 : k = 0 := by
    have : |(k : ℝ)| < 1 := by rw [hk', abs_neg]; exact hwi
    have h3 : |k| < 1 := by exact_mod_cast this
    exact Int.abs_lt_one_iff.mp h3
  have : w i = 0 := by
    rw [hk0] at hk'; simpa using hk'.symm
  simpa using this

lemma px3b_isOpen_offDiag' : IsOpen (offDiag d) :=
  isOpen_ne_fun (Torus.continuous_mk.comp continuous_fst) (Torus.continuous_mk.comp continuous_snd)

lemma contDiffAt_chart {σ : ℝ} {b : ℕ → ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b 2 B F) (X : Euc d) {w : Euc d} (hw0 : w ≠ 0) (hw : ‖w‖ < 1) :
    ContDiffAt ℝ 2 (fun w' => toChart F (X, w')) w := by
  have hmem : ((X + (1 / 2 : ℝ) • w, X - (1 / 2 : ℝ) • w) : Euc d × Euc d) ∈ offDiag d :=
    mk_chart_ne X w hw0 hw
  have h1 : ContDiffAt ℝ 2 (lift2 F) (X + (1 / 2 : ℝ) • w, X - (1 / 2 : ℝ) • w) :=
    (hF.smooth.contDiffAt (px3b_isOpen_offDiag'.mem_nhds hmem)).of_le (by exact_mod_cast le_rfl)
  have h2 : ContDiffAt ℝ 2 (fun w' : Euc d => ((X + (1 / 2 : ℝ) • w', X - (1 / 2 : ℝ) • w') : Euc d × Euc d)) w :=
    (by fun_prop : ContDiff ℝ 2 (fun w' : Euc d => ((X + (1 / 2 : ℝ) • w', X - (1 / 2 : ℝ) • w') : Euc d × Euc d))).contDiffAt
  exact h1.comp w h2

lemma norm_chart_le {σ : ℝ} {b : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : Conormal σ b 2 B F) (X : Euc d) {w : Euc d} (hw0 : w ≠ 0) (hw : ‖w‖ < r0) :
    |toChart F (X, w)| ≤ B * (1 + ‖w‖ ^ (-σ) * (1 + |Real.log ‖w‖|) ^ b) := by
  have h := hF.near 0 0 (by norm_num) X w hw0 hw
  simpa [mixedDeriv, norm_iteratedFDeriv_zero] using h

lemma chi_eq_one {w : Euc d} (hw : ‖w‖ ≤ 1 / 32) : chi d w = 1 :=
  ContDiffBump.one_of_mem_closedBall _ (by simpa using hw)

lemma chi_eq_zero {w : Euc d} (hw : 1 / 16 ≤ ‖w‖) : chi d w = 0 :=
  ContDiffBump.zero_of_le_dist _ (by simpa [dist_zero_right] using hw)

lemma chi_nonneg (w : Euc d) : 0 ≤ chi d w := ContDiffBump.nonneg _

lemma chi_le_one (w : Euc d) : chi d w ≤ 1 := ContDiffBump.le_one _

lemma chi_hasCompactSupport : HasCompactSupport (chi d) := ContDiffBump.hasCompactSupport _

lemma chi_contDiff (n : ℕ∞) : ContDiff ℝ n (chi d) := ContDiffBump.contDiff _

lemma norm_lt_of_chi_ne {w : Euc d} (h : chi d w ≠ 0) : ‖w‖ < 1 / 16 := by
  by_contra hh
  exact h (chi_eq_zero (not_lt.mp hh))

/-- The source `χ(w) G(X, w)` of the Newton potential in the chart. -/
def chartSource (F : Torus d → Torus d → ℝ) (X : Euc d) (w : Euc d) : ℝ :=
  chi d w * toChart F (X, w)

lemma chartSource_hasCompactSupport (F : Torus d → Torus d → ℝ) (X : Euc d) :
    HasCompactSupport (chartSource F X) :=
  chi_hasCompactSupport.mul_right

lemma chartSource_continuousOn {σ : ℝ} {b : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : Conormal σ b 2 B F) (X : Euc d) : ContinuousOn (chartSource F X) {0}ᶜ := by
  intro w hw
  have hw0 : w ≠ 0 := hw
  refine ContinuousAt.continuousWithinAt ?_
  by_cases h8 : ‖w‖ < 1 / 8
  · exact ((chi_contDiff 0).continuous.continuousAt).mul
      (contDiffAt_chart hF X hw0 (by linarith)).continuousAt
  · have : chartSource F X =ᶠ[𝓝 w] fun _ => 0 := by
      have hopen : {y : Euc d | 1 / 16 < ‖y‖} ∈ 𝓝 w :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds
          (show (1 / 16 : ℝ) < ‖w‖ by linarith [not_lt.mp h8])
      filter_upwards [hopen] with y hy
      simp [chartSource, chi_eq_zero hy.le]
    exact continuousAt_const.congr this.symm

lemma chartSource_integrable (hd : 1 ≤ d) {σ : ℝ} (hσ : σ < d) {b : ℕ} {B : ℝ}
    {F : Torus d → Torus d → ℝ} (hF : Conormal σ b 2 B F) (X : Euc d) :
    Integrable (chartSource F X) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hsupp : Function.support (chartSource F X) ⊆ Metric.ball (0 : Euc d) (1 / 16) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right]
    exact norm_lt_of_chi_ne (left_ne_zero_of_mul hw)
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  have hmeas : AEStronglyMeasurable (chartSource F X) (volume : Measure (Euc d)) := by
    have := (chartSource_continuousOn hF X).aestronglyMeasurable (measurableSet_singleton (0 : Euc d)).compl
      (μ := volume)
    rwa [restrict_compl_singleton] at this
  have hg : IntegrableOn (fun w : Euc d => B * (1 + ‖w‖ ^ (-σ) * (1 + |Real.log ‖w‖|) ^ b))
      (Metric.ball (0 : Euc d) (1 / 16)) := by
    refine Integrable.const_mul ?_ B
    exact (integrableOn_const (measure_ball_lt_top.ne)).add
      (integrableOn_rpow_log hd hσ b (by norm_num))
  refine Integrable.mono' hg hmeas.restrict ?_
  have hae : ∀ᵐ w : Euc d, w ≠ 0 := by
    have := (Set.countable_singleton (0 : Euc d)).ae_notMem (volume : Measure (Euc d))
    filter_upwards [this] with w hw using by simpa using hw
  refine (ae_restrict_iff' measurableSet_ball).mpr ?_
  filter_upwards [hae] with w hw0 hw
  have hw' : ‖w‖ < 1 / 16 := by simpa using hw
  have h1 := norm_chart_le hF X hw0 (by unfold r0; linarith)
  calc ‖chartSource F X w‖ = chi d w * |toChart F (X, w)| := by
        rw [chartSource, norm_mul, Real.norm_of_nonneg (chi_nonneg w), Real.norm_eq_abs]
    _ ≤ 1 * |toChart F (X, w)| := by
        gcongr; exact chi_le_one w
    _ ≤ _ := by rw [one_mul]; exact h1

theorem newtonChart_poisson_aux (hd : 2 ≤ d) {ν : ℝ} (hν : 0 < ν) {σ : ℝ} (hσ : σ < d) {b : ℕ}
    {B : ℝ} {F : Torus d → Torus d → ℝ} (hF : Conormal σ b 2 B F) (X z : Euc d) (hz0 : z ≠ 0)
    (hz : ‖z‖ < 1 / 32) :
    -(2 * ν) * Laplacian.laplacian (fun z' => newtonChart d ν (toChart F) (X, z')) z =
      toChart F (X, z) := by
  have hcd : ContDiffAt ℝ 2 (chartSource F X) z :=
    ((chi_contDiff 2).contDiffAt).mul (contDiffAt_chart hF X hz0 (by linarith))
  have hP := newtonKernel_poisson hd hν (chartSource_integrable (by omega) hσ hF X)
    (chartSource_hasCompactSupport F X) hcd
  have hloc : (fun z' => newtonChart d ν (toChart F) (X, z')) =ᶠ[𝓝 z]
      fun z' => ∫ w, newtonKernel d ν (z' - w) * chartSource F X w := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
      (show ‖z‖ < 1 / 32 from hz)] with y hy
    have : chi d y = 1 := chi_eq_one (le_of_lt hy)
    simp only [newtonChart, chartSource, this, one_mul]
  rw [(InnerProductSpace.laplacian_congr_nhds hloc).eq_of_nhds, hP]
  simp [chartSource, chi_eq_one hz.le]


end HRS.Parx

end
