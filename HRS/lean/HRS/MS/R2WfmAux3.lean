import HRS.MS.R2WfmAux2
import HRS.MS.Comm

/-!
# HRS.MS.R2Wfm Aux3 -- weighted plane waves and the polynomial envelope of their commutator kernels

Packet S97.  `s97_pw Pw ξ φ₀ z = ⟨z⟩^P cos(2π⟨z,ξ⟩ + φ₀)` (`φ₀ = 0`: cosine, `φ₀ = -π/2`: sine), its explicit gradient field
`s97_gpw`, the weighted mean value inequality `s97_mvt`, the Hessian bound of `⟨x⟩^P` (`s97_norm_H`), the weighted Lipschitz bound
`‖∇φ(x) - ∇φ(y)‖ ≤ K (1+|ξ|)² (⟨x⟩+⟨y⟩)^P |x-y|` (`s97_gpw_lip`), and `s97_poly_kernel`: the kernel
`h_φ(x,y) = (∇φ(x) - ∇φ(y))·∇g(x-y)` of `φ = s97_pw` lies in `IsR2PolyPairKernel s Pw (K (1+|ξ|)²)`.
-/

open MeasureTheory
open scoped FourierTransform ENNReal NNReal

noncomputable section
namespace HRS.MS.R2Wfm
open HRS.Whole HRS.MS.R2Poly

variable {d : ℕ}

theorem s97_jb_nonneg (x : Euc d) : 0 ≤ jbracket x := zero_le_one.trans (s95_one_le_jb x)

theorem s97_jb_mono {z x : Euc d} (h : ‖z‖ ≤ ‖x‖) : jbracket z ≤ jbracket x := by
  unfold jbracket
  exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg z])

/-- Weighted mean value inequality. -/
theorem s97_mvt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E}
    {f' : Euc d → Euc d →L[ℝ] E} {Pw K : ℝ} (hP : 0 ≤ Pw) (hK : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hb : ∀ z, ‖f' z‖ ≤ K * jbracket z ^ Pw) (x y : Euc d) :
    ‖f x - f y‖ ≤ K * (jbracket x + jbracket y) ^ Pw * ‖x - y‖ := by
  set R : ℝ := max ‖x‖ ‖y‖ with hR
  have hconv : Convex ℝ (Metric.closedBall (0 : Euc d) R) := convex_closedBall _ _
  have hx : y ∈ Metric.closedBall (0 : Euc d) R := by
    rw [mem_closedBall_zero_iff]; exact le_max_right _ _
  have hy : x ∈ Metric.closedBall (0 : Euc d) R := by
    rw [mem_closedBall_zero_iff]; exact le_max_left _ _
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℝ) (f := f) (f' := f')
    (s := Metric.closedBall (0 : Euc d) R) (C := K * (jbracket x + jbracket y) ^ Pw)
    (fun z _ => (hf z).hasFDerivWithinAt) (fun z hz => by
      rw [mem_closedBall_zero_iff] at hz
      refine (hb z).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (s97_jb_nonneg z) ?_ hP) hK
      rcases le_total ‖x‖ ‖y‖ with h | h
      · rw [hR, max_eq_right h] at hz
        have := s97_jb_mono (x := y) hz
        linarith [s97_jb_nonneg x]
      · rw [hR, max_eq_left h] at hz
        have := s97_jb_mono (x := x) hz
        linarith [s97_jb_nonneg y]) hconv hx hy
  simpa [norm_sub_rev] using key


theorem s97_jbpow_eq (Pw : ℝ) (z : Euc d) : jbracket z ^ Pw = (1 + ‖z‖ ^ 2) ^ (Pw / 2) := by
  unfold jbracket
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1; ring

theorem s97_one_add_pos (z : Euc d) : 0 < 1 + ‖z‖ ^ 2 := by positivity

/-- `z ↦ (1+‖z‖²)^e` -/
theorem s97_hasFDerivAt_g (e : ℝ) (z : Euc d) :
    HasFDerivAt (fun z : Euc d => (1 + ‖z‖ ^ 2) ^ e)
      ((e * (1 + ‖z‖ ^ 2) ^ (e - 1) * 2) • innerSL ℝ z) z := by
  have h1 := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add 1).rpow_const (p := e)
    (Or.inl (s97_one_add_pos z).ne')
  convert h1 using 1
  ext v
  simp [mul_assoc]

theorem s97_hasFDerivAt_w (Pw : ℝ) (z : Euc d) :
    HasFDerivAt (fun z : Euc d => jbracket z ^ Pw)
      ((Pw * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1)) • innerSL ℝ z) z := by
  have h := s97_hasFDerivAt_g (Pw / 2) z
  have e : (fun z : Euc d => jbracket z ^ Pw) = fun z => (1 + ‖z‖ ^ 2) ^ (Pw / 2) := by
    funext z; exact s97_jbpow_eq Pw z
  rw [e]
  convert h using 2
  ring

theorem s97_pow_le_jb (z : Euc d) {e Pw : ℝ} (he : e ≤ Pw / 2) : (1 + ‖z‖ ^ 2) ^ e ≤ jbracket z ^ Pw := by
  rw [s97_jbpow_eq]
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖z‖]) he

theorem s97_norm_w' (Pw : ℝ) (hP : 0 ≤ Pw) (z : Euc d) :
    ‖(Pw * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1)) • innerSL ℝ z‖ ≤ Pw * jbracket z ^ Pw := by
  rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hP (Real.rpow_nonneg (s97_one_add_pos z).le _))]
  have h1 : ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - 1), norm_nonneg z]
  have h2 : (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1) * (1 + ‖z‖ ^ 2) = (1 + ‖z‖ ^ 2) ^ (Pw / 2) := by
    rw [← Real.rpow_add_one (s97_one_add_pos z).ne']; congr 1; ring
  rw [s97_jbpow_eq, ← h2]
  have : 0 ≤ (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1) := Real.rpow_nonneg (s97_one_add_pos z).le _
  calc Pw * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1) * ‖z‖ = Pw * ((1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1) * ‖z‖) := by ring
    _ ≤ Pw * ((1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1) * (1 + ‖z‖ ^ 2)) := by gcongr


/-- The gradient field `∇⟨x⟩^P = P (1+|x|²)^{P/2-1} x`. -/
def s97_W1 (Pw : ℝ) (z : Euc d) : Euc d := (Pw * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1)) • z

/-- Hessian of `⟨x⟩^P`. -/
def s97_H (Pw : ℝ) (z : Euc d) : Euc d →L[ℝ] Euc d :=
  (Pw * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1)) • ContinuousLinearMap.id ℝ (Euc d) +
    ((Pw * ((Pw / 2 - 1) * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1 - 1) * 2)) • innerSL ℝ z).smulRight z

theorem s97_hasFDerivAt_W1 (Pw : ℝ) (z : Euc d) : HasFDerivAt (s97_W1 Pw) (s97_H Pw z) z := by
  have hc : HasFDerivAt (fun z : Euc d => Pw * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1))
      (Pw • ((Pw / 2 - 1) * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1 - 1) * 2) • innerSL ℝ z) z :=
    (s97_hasFDerivAt_g (Pw / 2 - 1) z).const_mul Pw
  have h := hc.smul (hasFDerivAt_id z)
  refine h.congr_fderiv ?_
  unfold s97_H
  congr 2
  ext v
  simp [mul_assoc]

theorem s97_norm_H (Pw : ℝ) (hP : 0 ≤ Pw) (z : Euc d) :
    ‖s97_H Pw z‖ ≤ Pw * (1 + |Pw - 2|) * jbracket z ^ Pw := by
  have hpos := s97_one_add_pos z
  have hg0 : 0 ≤ (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1) := Real.rpow_nonneg hpos.le _
  have hjb := s97_pow_le_jb z (e := Pw / 2 - 1) (Pw := Pw) (by linarith)
  have h1 : ‖(Pw * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1)) • ContinuousLinearMap.id ℝ (Euc d)‖ ≤
      Pw * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1) := by
    refine (norm_smul _ _).le.trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hP hg0)]
    calc Pw * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1) * ‖ContinuousLinearMap.id ℝ (Euc d)‖
        ≤ Pw * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1) * 1 := by
          gcongr; exact ContinuousLinearMap.norm_id_le
      _ = _ := mul_one _
  have h2 : ‖((Pw * ((Pw / 2 - 1) * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1 - 1) * 2)) • innerSL ℝ z).smulRight z‖ ≤
      Pw * |Pw - 2| * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1) := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, innerSL_apply_norm, Real.norm_eq_abs]
    have e1 : |Pw * ((Pw / 2 - 1) * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1 - 1) * 2)| =
        Pw * |Pw - 2| * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1 - 1) := by
      have : Pw * ((Pw / 2 - 1) * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1 - 1) * 2) =
          Pw * (Pw - 2) * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1 - 1) := by ring
      rw [this, abs_mul, abs_mul, abs_of_nonneg hP, abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
    rw [e1]
    have h3 : (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1 - 1) * (1 + ‖z‖ ^ 2) = (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1) := by
      rw [← Real.rpow_add_one hpos.ne']; congr 1; ring
    have h4 : ‖z‖ * ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    calc Pw * |Pw - 2| * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1 - 1) * ‖z‖ * ‖z‖
        = Pw * |Pw - 2| * ((1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1 - 1) * (‖z‖ * ‖z‖)) := by ring
      _ ≤ Pw * |Pw - 2| * ((1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1 - 1) * (1 + ‖z‖ ^ 2)) := by
          gcongr
      _ = _ := by rw [h3]
  calc ‖s97_H Pw z‖ ≤ _ := norm_add_le _ _
    _ ≤ Pw * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1) + Pw * |Pw - 2| * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1) := add_le_add h1 h2
    _ = Pw * (1 + |Pw - 2|) * (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1) := by ring
    _ ≤ Pw * (1 + |Pw - 2|) * jbracket z ^ Pw := by gcongr


/-- Weighted plane wave `⟨x⟩^P cos(2π⟨x,ξ⟩ + φ₀)`. -/
def s97_pw (Pw : ℝ) (ξ : Euc d) (φ0 : ℝ) (z : Euc d) : ℝ :=
  jbracket z ^ Pw * Real.cos (2 * Real.pi * inner ℝ z ξ + φ0)

/-- Its gradient field. -/
def s97_gpw (Pw : ℝ) (ξ : Euc d) (φ0 : ℝ) (z : Euc d) : Euc d :=
  Real.cos (2 * Real.pi * inner ℝ z ξ + φ0) • s97_W1 Pw z -
    (2 * Real.pi * jbracket z ^ Pw * Real.sin (2 * Real.pi * inner ℝ z ξ + φ0)) • ξ

theorem s97_hasFDerivAt_pw (Pw : ℝ) (ξ : Euc d) (φ0 : ℝ) (z : Euc d) :
    HasFDerivAt (s97_pw Pw ξ φ0) (innerSL ℝ (s97_gpw Pw ξ φ0 z)) z := by
  have hw := s97_hasFDerivAt_w Pw z
  have hθ : HasFDerivAt (fun y : Euc d => 2 * Real.pi * inner ℝ y ξ + φ0) (((2 * Real.pi : ℝ)) • innerSL ℝ ξ) z := by
    have : (fun y : Euc d => 2 * Real.pi * inner ℝ y ξ + φ0) = fun y => ((2 * Real.pi : ℝ)) • innerSL ℝ ξ y + φ0 := by
      funext y; simp [real_inner_comm]
    rw [this]
    exact (((innerSL ℝ ξ).hasFDerivAt).const_smul ((2 * Real.pi : ℝ))).add_const φ0
  have h := hw.mul hθ.cos
  refine h.congr_fderiv ?_
  ext v
  simp only [s97_gpw, s97_W1, innerSL_apply_apply, inner_sub_left, inner_smul_left, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, RCLike.conj_to_real]
  ring

theorem s97_gradient_pw (Pw : ℝ) (ξ : Euc d) (φ0 : ℝ) (z : Euc d) :
    gradient (s97_pw Pw ξ φ0) z = s97_gpw Pw ξ φ0 z := by
  have : HasGradientAt (s97_pw Pw ξ φ0) (s97_gpw Pw ξ φ0 z) z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    refine (s97_hasFDerivAt_pw Pw ξ φ0 z).congr_fderiv ?_
    ext v
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  exact this.gradient


theorem s97_norm_W1 (Pw : ℝ) (hP : 0 ≤ Pw) (z : Euc d) : ‖s97_W1 Pw z‖ ≤ Pw * jbracket z ^ Pw := by
  have h := s97_norm_w' Pw hP z
  unfold s97_W1
  rw [norm_smul]
  rw [norm_smul, innerSL_apply_norm] at h
  exact h

theorem s97_theta_lip (ξ x y : Euc d) (φ0 : ℝ) :
    |(2 * Real.pi * inner ℝ x ξ + φ0) - (2 * Real.pi * inner ℝ y ξ + φ0)| ≤ 2 * Real.pi * ‖ξ‖ * ‖x - y‖ := by
  have : (2 * Real.pi * inner ℝ x ξ + φ0) - (2 * Real.pi * inner ℝ y ξ + φ0) = 2 * Real.pi * inner ℝ (x - y) ξ := by
    rw [inner_sub_left]; ring
  rw [this, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  calc 2 * Real.pi * |inner ℝ (x - y) ξ| ≤ 2 * Real.pi * (‖x - y‖ * ‖ξ‖) := by
        gcongr; exact abs_real_inner_le_norm _ _
    _ = _ := by ring

theorem s97_gpw_lip (Pw : ℝ) (hP : 0 ≤ Pw) (ξ : Euc d) (φ0 : ℝ) (x y : Euc d) :
    ‖s97_gpw Pw ξ φ0 x - s97_gpw Pw ξ φ0 y‖ ≤
      (Pw * (1 + |Pw - 2|) + 4 * Real.pi * Pw + 4 * Real.pi ^ 2) * (1 + ‖ξ‖) ^ 2 *
        (jbracket x + jbracket y) ^ Pw * ‖x - y‖ := by
  set ρ : ℝ := jbracket x + jbracket y with hρ
  set Hs : ℝ := Pw * (1 + |Pw - 2|) with hHs
  have hHs0 : 0 ≤ Hs := mul_nonneg hP (by positivity)
  have hjx := s97_jb_nonneg x
  have hjy := s97_jb_nonneg y
  have hρ0 : 0 ≤ ρ ^ Pw := Real.rpow_nonneg (by linarith) _
  have ha : ‖s97_W1 Pw x - s97_W1 Pw y‖ ≤ Hs * ρ ^ Pw * ‖x - y‖ :=
    s97_mvt hP hHs0 (s97_hasFDerivAt_W1 Pw) (s97_norm_H Pw hP) x y
  have hb : |jbracket x ^ Pw - jbracket y ^ Pw| ≤ Pw * ρ ^ Pw * ‖x - y‖ := by
    have := s97_mvt (f := fun z : Euc d => jbracket z ^ Pw) hP hP (s97_hasFDerivAt_w Pw) (s97_norm_w' Pw hP) x y
    simpa [Real.norm_eq_abs] using this
  have hjyρ : jbracket y ^ Pw ≤ ρ ^ Pw := Real.rpow_le_rpow hjy (by linarith) hP
  have hc : ‖s97_W1 Pw y‖ ≤ Pw * ρ ^ Pw := (s97_norm_W1 Pw hP y).trans (mul_le_mul_of_nonneg_left hjyρ hP)
  have hθ := s97_theta_lip ξ x y φ0
  have hcos : |Real.cos (2 * Real.pi * inner ℝ x ξ + φ0) - Real.cos (2 * Real.pi * inner ℝ y ξ + φ0)| ≤
      2 * Real.pi * ‖ξ‖ * ‖x - y‖ := (Real.abs_cos_sub_cos_le _ _).trans hθ
  have hsin : |Real.sin (2 * Real.pi * inner ℝ x ξ + φ0) - Real.sin (2 * Real.pi * inner ℝ y ξ + φ0)| ≤
      2 * Real.pi * ‖ξ‖ * ‖x - y‖ := (Real.abs_sin_sub_sin_le _ _).trans hθ
  set a1 := Real.cos (2 * Real.pi * inner ℝ x ξ + φ0)
  set a2 := Real.cos (2 * Real.pi * inner ℝ y ξ + φ0)
  set b1 := Real.sin (2 * Real.pi * inner ℝ x ξ + φ0)
  set b2 := Real.sin (2 * Real.pi * inner ℝ y ξ + φ0)
  set wx := jbracket x ^ Pw
  set wy := jbracket y ^ Pw
  have ha1 : |a1| ≤ 1 := Real.abs_cos_le_one _
  have hb1 : |b1| ≤ 1 := Real.abs_sin_le_one _
  have hdec : s97_gpw Pw ξ φ0 x - s97_gpw Pw ξ φ0 y =
      a1 • (s97_W1 Pw x - s97_W1 Pw y) + (a1 - a2) • s97_W1 Pw y -
        (2 * Real.pi * ((wx - wy) * b1 + wy * (b1 - b2))) • ξ := by
    unfold s97_gpw
    module
  rw [hdec]
  have hπ : 0 < 2 * Real.pi := by positivity
  have hxy := norm_nonneg (x - y)
  have hξ := norm_nonneg ξ
  have t1 : ‖a1 • (s97_W1 Pw x - s97_W1 Pw y)‖ ≤ Hs * ρ ^ Pw * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |a1| * ‖s97_W1 Pw x - s97_W1 Pw y‖ ≤ 1 * (Hs * ρ ^ Pw * ‖x - y‖) := mul_le_mul ha1 ha (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have t2 : ‖(a1 - a2) • s97_W1 Pw y‖ ≤ (2 * Real.pi * ‖ξ‖ * ‖x - y‖) * (Pw * ρ ^ Pw) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hcos hc (norm_nonneg _) (by positivity)
  have t3 : ‖(2 * Real.pi * ((wx - wy) * b1 + wy * (b1 - b2))) • ξ‖ ≤
      2 * Real.pi * (Pw * ρ ^ Pw * ‖x - y‖ + ρ ^ Pw * (2 * Real.pi * ‖ξ‖ * ‖x - y‖)) * ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hπ]
    have hwy : |wy| ≤ ρ ^ Pw := by
      rw [abs_of_nonneg (Real.rpow_nonneg hjy _)]; exact hjyρ
    have : |(wx - wy) * b1 + wy * (b1 - b2)| ≤ Pw * ρ ^ Pw * ‖x - y‖ + ρ ^ Pw * (2 * Real.pi * ‖ξ‖ * ‖x - y‖) := by
      calc |(wx - wy) * b1 + wy * (b1 - b2)| ≤ |(wx - wy) * b1| + |wy * (b1 - b2)| := abs_add_le _ _
        _ = |wx - wy| * |b1| + |wy| * |b1 - b2| := by rw [abs_mul, abs_mul]
        _ ≤ (Pw * ρ ^ Pw * ‖x - y‖) * 1 + ρ ^ Pw * (2 * Real.pi * ‖ξ‖ * ‖x - y‖) :=
            add_le_add (mul_le_mul hb hb1 (abs_nonneg _) (by positivity)) (mul_le_mul hwy hsin (abs_nonneg _) hρ0)
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hπ.le) hξ
  have hsum : ‖a1 • (s97_W1 Pw x - s97_W1 Pw y) + (a1 - a2) • s97_W1 Pw y -
      (2 * Real.pi * ((wx - wy) * b1 + wy * (b1 - b2))) • ξ‖ ≤
      (Hs + 4 * Real.pi * Pw * ‖ξ‖ + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * ρ ^ Pw * ‖x - y‖ := by
    calc _ ≤ ‖a1 • (s97_W1 Pw x - s97_W1 Pw y) + (a1 - a2) • s97_W1 Pw y‖ +
          ‖(2 * Real.pi * ((wx - wy) * b1 + wy * (b1 - b2))) • ξ‖ := norm_sub_le _ _
      _ ≤ (‖a1 • (s97_W1 Pw x - s97_W1 Pw y)‖ + ‖(a1 - a2) • s97_W1 Pw y‖) +
          ‖(2 * Real.pi * ((wx - wy) * b1 + wy * (b1 - b2))) • ξ‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (Hs * ρ ^ Pw * ‖x - y‖ + (2 * Real.pi * ‖ξ‖ * ‖x - y‖) * (Pw * ρ ^ Pw)) +
          2 * Real.pi * (Pw * ρ ^ Pw * ‖x - y‖ + ρ ^ Pw * (2 * Real.pi * ‖ξ‖ * ‖x - y‖)) * ‖ξ‖ := by
          gcongr
      _ = _ := by ring
  refine hsum.trans ?_
  have hξ1 : ‖ξ‖ ≤ (1 + ‖ξ‖) ^ 2 := by nlinarith
  have hξ2 : ‖ξ‖ ^ 2 ≤ (1 + ‖ξ‖) ^ 2 := by nlinarith
  have hξ0 : 1 ≤ (1 + ‖ξ‖) ^ 2 := by nlinarith
  have hπp : 0 ≤ 4 * Real.pi * Pw := by positivity
  have hπ2 : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  have key : Hs + 4 * Real.pi * Pw * ‖ξ‖ + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 ≤
      (Hs + 4 * Real.pi * Pw + 4 * Real.pi ^ 2) * (1 + ‖ξ‖) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hξ0 hHs0, mul_le_mul_of_nonneg_left hξ1 hπp, mul_le_mul_of_nonneg_left hξ2 hπ2]
  have := mul_le_mul_of_nonneg_right key (mul_nonneg hρ0 hxy)
  calc _ = (Hs + 4 * Real.pi * Pw * ‖ξ‖ + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * (ρ ^ Pw * ‖x - y‖) := by ring
    _ ≤ _ := by nlinarith [this]


theorem s97_gpw_cont (Pw : ℝ) (ξ : Euc d) (φ0 : ℝ) : Continuous (s97_gpw Pw ξ φ0) := by
  have h1 : Continuous (fun z : Euc d => (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1)) :=
    (by fun_prop : Continuous fun z : Euc d => 1 + ‖z‖ ^ 2).rpow_const (fun z => Or.inl (s97_one_add_pos z).ne')
  have h2 : Continuous (fun z : Euc d => jbracket z ^ Pw) :=
    (by unfold jbracket; fun_prop : Continuous fun z : Euc d => jbracket z).rpow_const
      (fun z => Or.inl (zero_lt_one.trans_le (s95_one_le_jb z)).ne')
  unfold s97_gpw s97_W1
  fun_prop

theorem s97_gpw_cont2 (Pw : ℝ) (φ0 : ℝ) : Continuous (fun p : Euc d × Euc d => s97_gpw Pw p.1 φ0 p.2) := by
  have h1 : Continuous (fun z : Euc d => (1 + ‖z‖ ^ 2) ^ (Pw / 2 - 1)) :=
    (by fun_prop : Continuous fun z : Euc d => 1 + ‖z‖ ^ 2).rpow_const (fun z => Or.inl (s97_one_add_pos z).ne')
  have h2 : Continuous (fun z : Euc d => jbracket z ^ Pw) :=
    (by unfold jbracket; fun_prop : Continuous fun z : Euc d => jbracket z).rpow_const
      (fun z => Or.inl (zero_lt_one.trans_le (s95_one_le_jb z)).ne')
  have h1' : Continuous (fun p : Euc d × Euc d => (1 + ‖p.2‖ ^ 2) ^ (Pw / 2 - 1)) := h1.comp continuous_snd
  have h2' : Continuous (fun p : Euc d × Euc d => jbracket p.2 ^ Pw) := h2.comp continuous_snd
  unfold s97_gpw s97_W1
  fun_prop

theorem s97_comm_bound {s : ℝ} (hs0 : 0 ≤ s) {v : Euc d → Euc d} {Λ : ℝ} (hΛ : 0 ≤ Λ) (x y : Euc d)
    (hxy : x ≠ y) (hlip : ‖v x - v y‖ ≤ Λ * ‖x - y‖) :
    |commutatorKernel d s v x y| ≤ max s 1 * Λ * (1 + rieszWeight s (x - y)) := by
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hzpos : 0 < ‖x - y‖ := norm_pos_iff.mpr hz
  have hW := HRS.MS.Wr.wr3_rieszWeight_nonneg (d := d) s (x - y)
  by_cases hs : s = 0
  · subst hs
    have hG : ‖rieszKernelGrad d 0 (x - y)‖ = ‖x - y‖⁻¹ := by
      rw [movtr_rieszKernelGrad_norm 0 le_rfl hz]
      norm_num [movtr_sigma, Real.rpow_neg_one]
    have key : |commutatorKernel d 0 v x y| ≤ Λ := by
      unfold commutatorKernel
      calc |inner ℝ (v x - v y) (rieszKernelGrad d 0 (x - y))|
          ≤ ‖v x - v y‖ * ‖rieszKernelGrad d 0 (x - y)‖ := abs_real_inner_le_norm _ _
        _ ≤ (Λ * ‖x - y‖) * ‖x - y‖⁻¹ :=
            mul_le_mul hlip hG.le (norm_nonneg _) (by positivity)
        _ = Λ := by rw [mul_assoc, mul_inv_cancel₀ hzpos.ne', mul_one]
    calc |commutatorKernel d 0 v x y| ≤ Λ := key
      _ ≤ max 0 1 * Λ * (1 + rieszWeight 0 (x - y)) := by
          have : (1 : ℝ) ≤ max 0 1 := le_max_right _ _
          nlinarith [mul_nonneg hΛ hW]
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hw : rieszWeight s (x - y) = ‖x - y‖ ^ (-s) := by simp [rieszWeight, hs]
    have hG : ‖rieszKernelGrad d s (x - y)‖ = s * ‖x - y‖ ^ (-s - 1) := by
      rw [movtr_rieszKernelGrad_norm s hs0 hz]
      simp [movtr_sigma, hs]
    have hpow : ‖x - y‖ ^ (-s) = ‖x - y‖ ^ (-s - 1) * ‖x - y‖ := by
      rw [← Real.rpow_add_one hzpos.ne']
      congr 1
      ring
    have key : |commutatorKernel d s v x y| ≤ s * Λ * ‖x - y‖ ^ (-s) := by
      unfold commutatorKernel
      calc |inner ℝ (v x - v y) (rieszKernelGrad d s (x - y))|
          ≤ ‖v x - v y‖ * ‖rieszKernelGrad d s (x - y)‖ := abs_real_inner_le_norm _ _
        _ ≤ (Λ * ‖x - y‖) * (s * ‖x - y‖ ^ (-s - 1)) :=
            mul_le_mul hlip hG.le (norm_nonneg _) (by positivity)
        _ = s * Λ * ‖x - y‖ ^ (-s) := by rw [hpow]; ring
    rw [hw] at hW ⊢
    have hsΛ : 0 ≤ s * Λ := mul_nonneg hs0 hΛ
    have hm : s ≤ max s 1 := le_max_left _ _
    calc |commutatorKernel d s v x y| ≤ s * Λ * ‖x - y‖ ^ (-s) := key
      _ ≤ max s 1 * Λ * (1 + ‖x - y‖ ^ (-s)) := by
          have h1 : s * Λ ≤ max s 1 * Λ := mul_le_mul_of_nonneg_right hm hΛ
          nlinarith [mul_nonneg hΛ hW, mul_le_mul_of_nonneg_right hm hΛ]


/-- Constant of the polynomial envelope of the commutator kernel of a weighted plane wave. -/
def s97_Kc (s Pw : ℝ) : ℝ := max s 1 * (Pw * (1 + |Pw - 2|) + 4 * Real.pi * Pw + 4 * Real.pi ^ 2)

theorem s97_Kc_nonneg {s : ℝ} (Pw : ℝ) (hP : 0 ≤ Pw) : 0 ≤ s97_Kc s Pw := by
  unfold s97_Kc
  have : (0 : ℝ) ≤ max s 1 := le_trans zero_le_one (le_max_right _ _)
  positivity

theorem s97_poly_kernel {s : ℝ} (hs0 : 0 ≤ s) {Pw : ℝ} (hP : 0 ≤ Pw) (ξ : Euc d) (φ0 : ℝ) :
    IsR2PolyPairKernel s Pw (s97_Kc s Pw * (1 + ‖ξ‖) ^ 2)
      (commutatorKernel d s (fun x => gradient (s97_pw Pw ξ φ0) x)) := by
  have hg : (fun x => gradient (s97_pw Pw ξ φ0) x) = s97_gpw Pw ξ φ0 := by
    funext z; exact s97_gradient_pw Pw ξ φ0 z
  rw [hg]
  refine ⟨HRS.MS.Comm.comm_meas _ (s97_gpw_cont Pw ξ φ0).measurable, HRS.MS.Comm.comm_symm _, ?_⟩
  intro x y hxy
  have hl := s97_gpw_lip Pw hP ξ φ0 x y
  have hρ : 0 ≤ (jbracket x + jbracket y) ^ Pw :=
    Real.rpow_nonneg (add_nonneg (s97_jb_nonneg x) (s97_jb_nonneg y)) _
  have hKc : 0 ≤ Pw * (1 + |Pw - 2|) + 4 * Real.pi * Pw + 4 * Real.pi ^ 2 := by positivity
  have := s97_comm_bound hs0 (Λ := (Pw * (1 + |Pw - 2|) + 4 * Real.pi * Pw + 4 * Real.pi ^ 2) * (1 + ‖ξ‖) ^ 2 *
    (jbracket x + jbracket y) ^ Pw) (by positivity) x y hxy (v := s97_gpw Pw ξ φ0) (by
      have := hl; nlinarith [norm_nonneg (x - y)])
  refine this.trans (le_of_eq ?_)
  unfold s97_Kc
  ring

end HRS.MS.R2Wfm
end
