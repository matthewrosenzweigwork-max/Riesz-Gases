import HRS.Main.GFB2Aux7

/-!
# Packet GFB2, part 8: the Lipschitz and fractional-derivative bounds for the transport field `v = Mᵀ ∇ψ`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

theorem gfb2_inner_grad_eq_dirTor (ψ : Torus d → ℝ) (c : Euc d) (x : Torus d) :
    inner ℝ (Torus.grad ψ x) c = KernelGrad.dirTor ψ c x := by
  have h1 : inner ℝ (Torus.grad ψ x) c = fderiv ℝ (Torus.lift ψ) (Torus.rep x) c := by
    unfold Torus.grad
    exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
  rw [h1]
  have h2 := congrFun (KernelGrad.lift_dirTor ψ c) (Torus.rep x)
  simp only [Torus.lift, Function.comp, Torus.mk_rep] at h2
  exact h2.symm

/-- Lipschitz bound of a directional derivative: `|∂_c ψ(x) - ∂_c ψ(y)| ≤ ‖c‖ ‖ψ‖_{C²} |x-y|`. -/
theorem gfb2_dirTor_lipschitz {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) (c : Euc d) :
    KernelGrad.IsLipschitz (‖c‖ * Torus.cbNorm 2 ψ) (KernelGrad.dirTor ψ c) := by
  intro x y
  by_cases hc : c = 0
  · subst hc
    have : KernelGrad.dirTor ψ (0 : Euc d) = fun _ => 0 := by
      funext z; simp [KernelGrad.dirTor, KernelGrad.Dtor]
    simp [this]
  have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
  set w : Euc d := ‖c‖⁻¹ • c with hw
  have hwn : ‖w‖ ≤ 1 := by
    rw [hw, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hcn.ne']
  have hdir : KernelGrad.dirTor ψ c = fun z => ‖c‖ * KernelGrad.dirTor ψ w z := by
    funext z
    have : c = ‖c‖ • w := by rw [hw, smul_smul, mul_inv_cancel₀ hcn.ne', one_smul]
    conv_lhs => rw [this]
    simp [KernelGrad.dirTor, KernelGrad.Dtor, map_smul]
  have h2 : Torus.IsCk 1 (KernelGrad.dirTor ψ w) := by
    have h2' : Torus.IsCk ((1 + 1 : ℕ) : WithTop ℕ∞) ψ := by exact_mod_cast hψ
    exact_mod_cast KernelGrad.isCk_dirTor h2' w
  have hL : KernelGrad.IsLipschitz (Torus.cbNorm 1 (KernelGrad.dirTor ψ w)) (KernelGrad.dirTor ψ w) := by
    refine KernelGrad.isLipschitz_of_fderiv_le h2 fun y => ?_
    rw [← KernelGrad.norm_iteratedFDeriv_one' (f := Torus.lift (KernelGrad.dirTor ψ w))]
    exact KernelGrad.norm_iteratedFDeriv_le_cbNorm h2 le_rfl y
  have hcb : Torus.cbNorm 1 (KernelGrad.dirTor ψ w) ≤ Torus.cbNorm 2 ψ := by
    have h2'' : Torus.IsCk ((1 + 1 : ℕ) : WithTop ℕ∞) ψ := by exact_mod_cast hψ
    exact KernelGrad.cbNorm_dirTor_le h2'' hwn
  rw [hdir]
  simp only
  rw [← mul_sub, abs_mul, abs_of_pos hcn, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((hL x y).trans (mul_le_mul_of_nonneg_right hcb (by
    unfold KernelGrad.tdist; exact norm_nonneg _))) hcn.le


theorem gfb2_cbNorm_nonneg (φ : Torus d → ℝ) (k : ℕ) : 0 ≤ Torus.cbNorm k φ :=
  KernelGrad.cbNorm_nonneg' φ k

theorem gfb2_lipschitzVF {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) (M : Matrix (Fin d) (Fin d) ℝ)
    {cM : ℝ} (hcM0 : 0 ≤ cM) (hcM : ∀ v : Euc d, ‖Torus.matVec M v‖ ≤ cM * ‖v‖) :
    IsLipschitzVF (cM * Torus.cbNorm 2 ψ) (gfb2_v M ψ) := by
  intro x y
  set u : Euc d := gfb2_v M ψ x - gfb2_v M ψ y with hu
  have htd : 0 ≤ KernelGrad.tdist x y := by unfold KernelGrad.tdist; exact norm_nonneg _
  have hcb := gfb2_cbNorm_nonneg ψ 2
  by_cases h0 : u = 0
  · rw [h0, norm_zero]
    exact mul_nonneg (mul_nonneg hcM0 hcb) htd
  have hun : 0 < ‖u‖ := norm_pos_iff.2 h0
  set e : Euc d := ‖u‖⁻¹ • u with he
  have hen : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hun.ne']
  have hue : inner ℝ u e = ‖u‖ := by
    rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  set c : Euc d := Torus.matVec M e with hc
  have h1 : inner ℝ u e = KernelGrad.dirTor ψ c x - KernelGrad.dirTor ψ c y := by
    show inner ℝ (gfb2_v M ψ x - gfb2_v M ψ y) e = _
    unfold gfb2_v
    rw [inner_sub_left, ← Duality.inner_matVec_transpose, ← Duality.inner_matVec_transpose,
      gfb2_inner_grad_eq_dirTor, gfb2_inner_grad_eq_dirTor]
  have h2 := gfb2_dirTor_lipschitz hψ c x y
  have hcn : ‖c‖ ≤ cM := by
    have := hcM e
    rw [hen, mul_one] at this
    exact this
  calc ‖u‖ = inner ℝ u e := hue.symm
    _ = KernelGrad.dirTor ψ c x - KernelGrad.dirTor ψ c y := h1
    _ ≤ |KernelGrad.dirTor ψ c x - KernelGrad.dirTor ψ c y| := le_abs_self _
    _ ≤ ‖c‖ * Torus.cbNorm 2 ψ * KernelGrad.tdist x y := h2
    _ ≤ cM * Torus.cbNorm 2 ψ * KernelGrad.tdist x y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcn hcb) htd


/-- A real function with prescribed (Hermitian, absolutely summable) Fourier coefficients. -/
theorem gfb2_exists_of_coeffs (c : Lattice d → ℂ) (hc : Summable fun k => ‖c k‖)
    (hherm : ∀ k, c (-k) = (starRingEnd ℂ) (c k)) :
    ∃ w : Torus d → ℝ, Continuous w ∧ (∀ x, |w x| ≤ ∑' k, ‖c k‖) ∧ ∀ l, Torus.fcoef w l = c l := by
  classical
  set W : Torus d → ℂ := fun x => ∑' k, c k * Torus.mode k x with hW
  have hterm : ∀ k x, ‖c k * Torus.mode k x‖ = ‖c k‖ := fun k x => by
    rw [norm_mul, Torus.norm_mode, mul_one]
  have hWc : Continuous W := by
    refine continuous_tsum (fun k => continuous_const.mul (Torus.continuous_mode k)) hc
      (fun k x => (hterm k x).le)
  -- reality
  have hreal : ∀ x, (starRingEnd ℂ) (W x) = W x := by
    intro x
    have h1 : (starRingEnd ℂ) (W x) = ∑' k, c (-k) * Torus.mode (-k) x := by
      rw [hW]
      simp only
      rw [Complex.conj_tsum]
      refine tsum_congr fun k => ?_
      rw [map_mul, hherm k, Torus.mode_neg]
    rw [h1]
    exact (Equiv.neg (Lattice d)).tsum_eq (fun k => c k * Torus.mode k x)
  set w : Torus d → ℝ := fun x => (W x).re with hwdef
  have hwW : ∀ x, ((w x : ℝ) : ℂ) = W x := fun x => by
    have := Complex.conj_eq_iff_re.1 (hreal x)
    simpa [hwdef] using this
  refine ⟨w, Complex.continuous_re.comp hWc, fun x => ?_, fun l => ?_⟩
  · have h1 : |w x| ≤ ‖W x‖ := Complex.abs_re_le_norm _
    refine h1.trans ?_
    rw [hW]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun k => hterm k x))
    exact hc.congr fun k => (hterm k x).symm
  · unfold Torus.fcoef
    have e : (fun x => Torus.mode (-l) x * ((w x : ℝ) : ℂ)) =
        fun x => ∑' k, c k * (Torus.mode (-l) x * Torus.mode k x) := by
      funext x
      rw [hwW, hW]
      simp only
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      ring
    rw [e]
    have hmeas : ∀ k, AEStronglyMeasurable (fun x => c k * (Torus.mode (-l) x * Torus.mode k x)) volume :=
      fun k => (continuous_const.mul ((Torus.continuous_mode _).mul (Torus.continuous_mode _))).aestronglyMeasurable
    have hfin : ∑' k, ∫⁻ x, ‖c k * (Torus.mode (-l) x * Torus.mode k x)‖ₑ ∂(volume : Measure (Torus d)) ≠ ⊤ := by
      have h1 : ∀ k, ∫⁻ x, ‖c k * (Torus.mode (-l) x * Torus.mode k x)‖ₑ ∂(volume : Measure (Torus d)) =
          ENNReal.ofReal ‖c k‖ := by
        intro k
        have : ∀ x, ‖c k * (Torus.mode (-l) x * Torus.mode k x)‖ₑ = ENNReal.ofReal ‖c k‖ := by
          intro x
          rw [← ofReal_norm_eq_enorm, norm_mul, norm_mul, Torus.norm_mode, Torus.norm_mode]
          simp
        simp only [this, lintegral_const, measure_univ, mul_one]
      simp only [h1]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => norm_nonneg _) hc]
      exact ENNReal.ofReal_ne_top
    rw [integral_tsum hmeas hfin]
    have h2 : ∀ k, ∫ x, c k * (Torus.mode (-l) x * Torus.mode k x) = if k = l then c k else 0 := by
      intro k
      rw [integral_const_mul, Torus.integral_mode_mul]
      by_cases hk : k = l
      · subst hk; simp
      · have : ¬(-l + k = 0) := fun h => hk (by
          have := congrArg (· + l) h
          simpa using this)
        simp [this, hk]
    simp only [h2]
    rw [tsum_ite_eq]


theorem gfb2_fcoef_dirTor {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) (c : Euc d) (k : Lattice d) :
    Torus.fcoef (KernelGrad.dirTor ψ c) k =
      (2 * Real.pi * Complex.I * (Lattice.dot k c : ℝ)) * Torus.fcoef ψ k := by
  have hG : Torus.Per (Torus.lift ψ) := fun y n => Torus.lift_periodic ψ y n
  have hd : ContDiff ℝ 1 (Torus.lift ψ) := by
    have h1 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (Torus.lift ψ) := by exact_mod_cast hψ
    exact h1.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))
  have h := Torus.fcoef_fderiv hG hd c k
  have e1 : Torus.descend (fun y => _root_.fderiv ℝ (Torus.lift ψ) y c) = KernelGrad.dirTor ψ c := by
    have := congrArg Torus.descend (KernelGrad.lift_dirTor ψ c)
    rw [Torus.descend_lift] at this
    exact this.symm
  rw [e1, Torus.descend_lift] at h
  exact h

theorem gfb2_v_apply_eq (M : Matrix (Fin d) (Fin d) ℝ) (ψ : Torus d → ℝ) (j : Fin d) :
    (fun x => gfb2_v M ψ x j) =
      KernelGrad.dirTor ψ (Torus.matVec M (EuclideanSpace.single j (1 : ℝ))) := by
  funext x
  rw [← gfb2_inner_grad_eq_dirTor ψ _ x, Duality.inner_matVec_transpose]
  unfold gfb2_v
  rw [EuclideanSpace.inner_single_right]
  simp

theorem gfb2_fcoef_neg (g : Torus d → ℝ) (k : Lattice d) :
    Torus.fcoef g (-k) = (starRingEnd ℂ) (Torus.fcoef g k) := by
  unfold Torus.fcoef
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [neg_neg, map_mul, Complex.conj_ofReal, Torus.mode_neg]
  simp [Torus.mode_neg]


theorem gfb2_coef_bound (c : Euc d) (ψ : Torus d → ℝ) (k : Lattice d) :
    ‖(((2 * Real.pi * Lattice.enorm k) ^ (((d : ℝ) + 1) / 2) : ℝ) : ℂ) *
        ((2 * Real.pi * Complex.I * (Lattice.dot k c : ℝ)) * Torus.fcoef ψ k)‖ ≤
      ‖c‖ * (Lattice.jp k ^ (d + 2) * ‖Torus.fcoef ψ k‖) := by
  set E := Lattice.enorm k with hE
  set J := Lattice.jp k with hJ
  set a : ℝ := ((d : ℝ) + 1) / 2 with ha
  have hpi := Real.pi_pos
  have hE0 : 0 ≤ E := by rw [hE]; unfold Lattice.enorm; exact norm_nonneg _
  have hA0 : 0 ≤ 2 * Real.pi * E := by positivity
  have hAJ : 2 * Real.pi * E ≤ J := Torus.two_pi_enorm_le_jp k
  have hJ1 : 1 ≤ J := Torus.jp_ge_one k
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hnorm : ‖(((2 * Real.pi * E) ^ a : ℝ) : ℂ) *
      ((2 * Real.pi * Complex.I * (Lattice.dot k c : ℝ)) * Torus.fcoef ψ k)‖ =
      (2 * Real.pi * E) ^ a * (2 * Real.pi * |Lattice.dot k c| * ‖Torus.fcoef ψ k‖) := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, abs_of_nonneg (Real.rpow_nonneg hA0 a),
      Complex.norm_ofNat, mul_one]
    rw [abs_of_pos hpi]
  rw [hnorm]
  have hdot := Torus.abs_dot_le k c
  have h1 : (2 * Real.pi * E) ^ a * (2 * Real.pi * |Lattice.dot k c| * ‖Torus.fcoef ψ k‖) ≤
      (2 * Real.pi * E) ^ a * (2 * Real.pi * (E * ‖c‖) * ‖Torus.fcoef ψ k‖) := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hA0 a)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdot (by positivity)) (norm_nonneg _)
  refine h1.trans ?_
  have h2 : (2 * Real.pi * E) ^ a * (2 * Real.pi * E) ≤ J ^ a * J :=
    mul_le_mul (Real.rpow_le_rpow hA0 hAJ ha0) hAJ hA0 (Real.rpow_nonneg (by linarith) a)
  have h3 : J ^ a * J ≤ J ^ (d + 2) := by
    have : J ^ a * J = J ^ (a + 1) := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    rw [this, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hJ1 ?_
    rw [ha]; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have h4 := h2.trans h3
  calc (2 * Real.pi * E) ^ a * (2 * Real.pi * (E * ‖c‖) * ‖Torus.fcoef ψ k‖)
      = ((2 * Real.pi * E) ^ a * (2 * Real.pi * E)) * (‖c‖ * ‖Torus.fcoef ψ k‖) := by ring
    _ ≤ J ^ (d + 2) * (‖c‖ * ‖Torus.fcoef ψ k‖) :=
        mul_le_mul_of_nonneg_right h4 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖c‖ * (J ^ (d + 2) * ‖Torus.fcoef ψ k‖) := by ring


theorem gfb2_component_fracDeriv {γ : ℝ} (hγ : (2 * d + 10 : ℝ) < γ) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) (hMem : MemSobolev γ ψ) (c : Euc d) :
    ∃ w : Torus d → ℝ, Continuous w ∧
      (∀ x, |w x| ≤ ‖c‖ * ((1 + Real.sqrt (∑' k : NonzeroLattice d,
        Lattice.jp k.1 ^ (-(2 * (γ - ((d + 2 : ℕ) : ℝ))))) ) * sobolevNorm γ ψ)) ∧
      ∀ k, Torus.fcoef w k = (((2 * Real.pi * Lattice.enorm k) ^ (((d : ℝ) + 1) / 2) : ℝ) : ℂ) *
        Torus.fcoef (KernelGrad.dirTor ψ c) k := by
  classical
  set coef : Lattice d → ℂ := fun k => (((2 * Real.pi * Lattice.enorm k) ^ (((d : ℝ) + 1) / 2) : ℝ) : ℂ) *
    ((2 * Real.pi * Complex.I * (Lattice.dot k c : ℝ)) * Torus.fcoef ψ k) with hcoef
  have hint : Integrable ψ := hMem.1.integrable one_le_two
  have hmi : (d : ℝ) / 2 + ((d + 2 : ℕ) : ℝ) < γ := by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨hsum, hbd⟩ := Torus.sobolev_coeff_bound hmi hint hMem.2
  have hbound := gfb2_coef_bound c ψ
  have hcs : Summable fun k => ‖coef k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hbound k) (hsum.mul_left ‖c‖)
  have hherm : ∀ k, coef (-k) = (starRingEnd ℂ) (coef k) := by
    intro k
    have hdn : Lattice.dot (-k) c = - Lattice.dot k c := by
      rw [Torus.dot_eq_inner, Torus.dot_eq_inner, Torus.toEuc_neg, inner_neg_left]
    simp only [hcoef]
    rw [gfb2_fcoef_neg ψ k, Uniform.Q12.q12_enorm_neg, hdn]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Complex.ofReal_neg]
    ring
  obtain ⟨w, hwc, hwb, hwf⟩ := gfb2_exists_of_coeffs coef hcs hherm
  refine ⟨w, hwc, fun x => ?_, fun k => ?_⟩
  · refine (hwb x).trans ?_
    have h1 : ∑' k, ‖coef k‖ ≤ ‖c‖ * ∑' k : Lattice d, Lattice.jp k ^ (d + 2) * ‖Torus.fcoef ψ k‖ := by
      rw [← tsum_mul_left]
      exact hcs.tsum_le_tsum (fun k => hbound k) (hsum.mul_left ‖c‖)
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine hbd.trans ?_
    have hT : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * γ) * Torus.funRealCoeff ψ k ^ 2 :=
      tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
    have hS1 : |Torus.mean ψ| ≤ sobolevNorm γ ψ :=
      (by unfold sobolevNorm; exact Real.abs_le_sqrt (by linarith [sq_nonneg (Torus.mean ψ)]))
    have hS2 : Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * γ) * Torus.funRealCoeff ψ k ^ 2)
        ≤ sobolevNorm γ ψ := Real.sqrt_le_sqrt (by linarith [sq_nonneg (Torus.mean ψ)])
    have hC0 := Real.sqrt_nonneg (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (γ - ((d + 2 : ℕ) : ℝ)))))
    calc |Torus.mean ψ| + Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (γ - ((d + 2 : ℕ) : ℝ))))) *
          Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * γ) * Torus.funRealCoeff ψ k ^ 2)
        ≤ sobolevNorm γ ψ + Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (γ - ((d + 2 : ℕ) : ℝ))))) *
          sobolevNorm γ ψ := add_le_add hS1 (mul_le_mul_of_nonneg_left hS2 hC0)
      _ = _ := by ring
  · rw [hwf k, gfb2_fcoef_dirTor hψ c k]


/-- The transport-field bound `‖Mᵀ∇ψ‖_* ≲ ‖ψ‖_{H^γ}` with a constant depending only on `d, γ, M`. -/
theorem gfb2_transport_bound {γ : ℝ} (hγ : (2 * d + 10 : ℝ) < γ) (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) :
    ∃ cT : ℝ, 0 ≤ cT ∧ ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → MemSobolev γ ψ →
      HasTransportBound d s (gfb2_v M ψ) (cT * sobolevNorm γ ψ) := by
  classical
  obtain ⟨cM, hcM0, hcM⟩ := Q54c.exists_matVec_bound M
  have hm2 : (d : ℝ) / 2 + ((2 : ℕ) : ℝ) < γ := by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨Cemb, hCemb⟩ := cbNorm_le_sobolevNorm 2 γ hm2
  set Cg : ℝ := Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (γ - ((d + 2 : ℕ) : ℝ))))) with hCg
  set S1 : ℝ := ∑ j : Fin d, ‖Torus.matVec M (EuclideanSpace.single j (1 : ℝ))‖ with hS1
  refine ⟨cM * max Cemb 0 + S1 * (1 + Cg), ?_, fun ψ hψ hMem => ?_⟩
  · have : 0 ≤ S1 := Finset.sum_nonneg fun j _ => norm_nonneg _
    have : 0 ≤ Cg := Real.sqrt_nonneg _
    positivity
  have hsob0 : 0 ≤ sobolevNorm γ ψ := Real.sqrt_nonneg _
  have hcb : Torus.cbNorm 2 ψ ≤ max Cemb 0 * sobolevNorm γ ψ :=
    (hCemb ψ hMem hψ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsob0)
  have hS1nn : 0 ≤ S1 := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hCg0 : 0 ≤ Cg := Real.sqrt_nonneg _
  refine ⟨cM * Torus.cbNorm 2 ψ, S1 * ((1 + Cg) * sobolevNorm γ ψ), mul_nonneg hcM0 (gfb2_cbNorm_nonneg ψ 2),
    by positivity, gfb2_lipschitzVF hψ M hcM0 hcM, ?_, ?_⟩
  · intro _
    have hcomp : ∀ j : Fin d, ∃ w : Torus d → ℝ, Continuous w ∧
        (∀ x, |w x| ≤ ‖Torus.matVec M (EuclideanSpace.single j (1 : ℝ))‖ * ((1 + Cg) * sobolevNorm γ ψ)) ∧
        ∀ k, Torus.fcoef w k = (((2 * Real.pi * Lattice.enorm k) ^ (((d : ℝ) + 1) / 2) : ℝ) : ℂ) *
          Torus.fcoef (KernelGrad.dirTor ψ (Torus.matVec M (EuclideanSpace.single j (1 : ℝ)))) k := fun j =>
      gfb2_component_fracDeriv hγ hψ hMem _
    choose wj hwjc hwjb hwjf using hcomp
    set w : Torus d → Euc d := fun x => WithLp.toLp 2 (fun j => wj j x) with hw
    refine ⟨w, ?_, ?_⟩
    · intro j k
      have e1 : (fun x => w x j) = wj j := rfl
      have e2 := gfb2_v_apply_eq M ψ j
      rw [e1, e2]
      exact hwjf j k
    · have hwc : Continuous w := (PiLp.continuous_toLp 2 _).comp (continuous_pi hwjc)
      have hbd : ∀ x, ‖w x‖ ≤ S1 * ((1 + Cg) * sobolevNorm γ ψ) := by
        intro x
        have h1 : ‖w x‖ ≤ ∑ j, |wj j x| := by
          rw [EuclideanSpace.norm_eq]
          refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
          have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |wj i x|)
            (fun i _ => abs_nonneg _)
          simpa [sq_abs, hw] using this
        refine h1.trans ?_
        rw [hS1, Finset.sum_mul]
        exact Finset.sum_le_sum fun j _ => hwjb j x
      refine (eLpNorm_le_of_ae_bound hwc.aestronglyMeasurable (Eventually.of_forall hbd)).trans ?_
      simp
  · have hLip : cM * Torus.cbNorm 2 ψ ≤ cM * (max Cemb 0 * sobolevNorm γ ψ) :=
      mul_le_mul_of_nonneg_left hcb hcM0
    have hF0 : 0 ≤ S1 * ((1 + Cg) * sobolevNorm γ ψ) := by positivity
    calc cM * Torus.cbNorm 2 ψ + (if s < (d : ℝ) - 2 then S1 * ((1 + Cg) * sobolevNorm γ ψ) else 0)
        ≤ cM * (max Cemb 0 * sobolevNorm γ ψ) + S1 * ((1 + Cg) * sobolevNorm γ ψ) := by
          refine add_le_add hLip ?_
          split_ifs
          · exact le_rfl
          · exact hF0
      _ = (cM * max Cemb 0 + S1 * (1 + Cg)) * sobolevNorm γ ψ := by ring

end HRS.GF
