import HRS.MS.PrepStatAux1
import HRS.MS.Comm

/-!
# HRS.MS.PrepStatAux2 -- linear clause (Hoeffding + Donsker--Varadhan) and the commutator kernel (S3.2, part 2)

Packet S32, namespace `HRS.MS.PrepStat`.

* `s32_pair_empirical`: `μ_N(a) = N⁻¹ ∑ a(x_i)`.
* `s32_mgf_bound`: under `μ^{⊗N}` (`μ` a probability measure, `|a| ≤ A`),
  `∫ e^{t ∑_i (a(x_i) - μ a)} ≤ e^{N A² t²/2}` (Hoeffding's lemma, Mathlib `HasSubgaussianMGF`).
* `s32_linear_bound`: for every probability law `f` with `H(f | μ^{⊗N}) < ∞` and every `λ > 0`:
  `E_f |μ_N(a) - μ(a)| ≤ (Nλ)⁻¹ (H(f | μ^{⊗N}) + N A² λ²/2 + 1)` (with integrability).
* `s32_commN_eq`, `s32_pairEnergy_const_mul`, `s32_comm_isBounded`: `Comm_N(v) = 2 𝖥^{h_v}`,
  linearity of the pair energy in the kernel, and `h_v ∈ IsBoundedPairKernel s (s+1)` for `1`-Lipschitz `v`
  (all `0 ≤ s`, including `s = 0` where `commutatorKernel_isBounded_proof` does not apply).

Helper lemmas carry the prefix `s32_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MS.PrepStat

open HRS.Whole HRS.MS.Wr

variable {d N : ℕ}

theorem s32_pair_empirical (X : EucConfig d N) {a : Euc d → ℝ} (ha : Measurable a) :
    HRS.Whole.pair (HRS.Whole.empirical X) a = (N : ℝ)⁻¹ * ∑ i, a (X i) := by
  unfold HRS.Whole.pair HRS.Whole.empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [ENNReal.toReal_inv]
  · intro i _
    exact integrable_dirac enorm_lt_top

theorem s32_mgf_bound {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : Euc d → ℝ}
    (ha : Measurable a) {A : ℝ} (hA : ∀ x, |a x| ≤ A) (t : ℝ) :
    ∫⁻ X : EucConfig d N, ENNReal.ofReal
        (Real.exp (t * ∑ i, (a (X i) - ∫ x, a x ∂μ))) ∂(Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (Real.exp (N * A ^ 2 * t ^ 2 / 2)) := by
  set m : ℝ := ∫ x, a x ∂μ with hm
  set c0 : ℝ≥0 := (‖A - -A‖₊ / 2) ^ 2 with hc0
  have hc0r : (c0 : ℝ) = A ^ 2 := by
    simp only [hc0, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat]
    have : |A - -A| = 2 * |A| := by
      rw [sub_neg_eq_add, ← two_mul, abs_mul, abs_two]
    rw [this]
    have h2 : (2 * |A| / 2) = |A| := by ring
    rw [h2, sq_abs]
  have hind : iIndepFun (fun (i : Fin N) (X : EucConfig d N) => a (X i) - m)
      (Measure.pi fun _ : Fin N => μ) :=
    iIndepFun_pi (X := fun (_ : Fin N) (x : Euc d) => a x - m)
      (fun _ => (ha.sub_const m).aemeasurable)
  have hsub : ∀ i : Fin N, HasSubgaussianMGF (fun X : EucConfig d N => a (X i) - m) c0
      (Measure.pi fun _ : Fin N => μ) := by
    intro i
    have hmean : (Measure.pi fun _ : Fin N => μ)[fun X : EucConfig d N => a (X i)] = m := by
      exact integral_comp_eval (μ := fun _ : Fin N => μ) (f := a) ha.aestronglyMeasurable
    have h := hasSubgaussianMGF_of_mem_Icc (μ := Measure.pi fun _ : Fin N => μ)
      (X := fun X : EucConfig d N => a (X i)) (a := -A) (b := A)
      ((ha.comp (measurable_pi_apply i)).aemeasurable)
      (Filter.Eventually.of_forall fun X => abs_le.1 (hA (X i)))
    rw [hmean] at h
    exact h
  have hS := HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ) (fun i _ => hsub i)
  have hmg := hS.mgf_le t
  have hint := hS.integrable_exp_mul t
  have hcoe : ((∑ _i : Fin N, c0 : ℝ≥0) : ℝ) = N * A ^ 2 := by
    rw [NNReal.coe_sum]
    simp [hc0r]
  rw [hcoe] at hmg
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun X =>
    (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal hmg

/-- The linear statistic is `N⁻¹ ∑ (a(x_i) - μ a)`. -/
theorem s32_linear_stat (X : EucConfig d N) {μ : Measure (Euc d)} {a : Euc d → ℝ}
    (ha : Measurable a) (hN : 0 < N) :
    HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a =
      (N : ℝ)⁻¹ * ∑ i, (a (X i) - ∫ x, a x ∂μ) := by
  rw [s32_pair_empirical X ha, Finset.sum_sub_distrib]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold HRS.Whole.pair
  field_simp

/-- **Linear clause**: entropy inequality (Donsker--Varadhan) plus Hoeffding under `μ^{⊗N}`. -/
theorem s32_linear_bound {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : Euc d → ℝ}
    (ha : Measurable a) {A : ℝ} (hA : ∀ x, |a x| ≤ A) (hN : 0 < N)
    (f : Measure (EucConfig d N)) [IsProbabilityMeasure f]
    (hKL : InformationTheory.klDiv f (Measure.pi fun _ : Fin N => μ) ≠ ∞) {lam : ℝ}
    (hlam : 0 < lam) :
    Integrable (fun X : EucConfig d N =>
        |HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a|) f ∧
      ∫ X, |HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a| ∂f ≤
        ((N : ℝ) * lam)⁻¹ * ((InformationTheory.klDiv f (Measure.pi fun _ : Fin N => μ)).toReal +
          (N * A ^ 2 * lam ^ 2 / 2 + 1)) := by
  set π : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hπ
  set Ψ : EucConfig d N → ℝ := fun X => ∑ i, (a (X i) - ∫ x, a x ∂μ) with hΨ
  have hΨm : Measurable Ψ :=
    Finset.measurable_sum _ fun i _ => ((ha.comp (measurable_pi_apply i)).sub_const _)
  set A' : ℝ := N * A ^ 2 * lam ^ 2 / 2 with hA'
  have hp : ∫⁻ X, ENNReal.ofReal (Real.exp (lam * Ψ X)) ∂π ≤ ENNReal.ofReal (Real.exp A') := by
    have := s32_mgf_bound (d := d) (N := N) (μ := μ) ha hA lam
    simpa only [hΨ, hA'] using this
  have hm : ∫⁻ X, ENNReal.ofReal (Real.exp (-(lam * Ψ X))) ∂π ≤ ENNReal.ofReal (Real.exp A') := by
    have := s32_mgf_bound (d := d) (N := N) (μ := μ) ha hA (-lam)
    have e : ((-lam) ^ 2) = lam ^ 2 := by ring
    rw [e] at this
    simpa only [hΨ, hA', neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib] using this
  have hZ' := wr9_lintegral_exp_abs π hΨm hlam hp hm
  have hA'0 : 0 ≤ A' := by positivity
  have hZ : ∫⁻ X, ENNReal.ofReal (Real.exp (lam * |Ψ X|)) ∂π ≤ ENNReal.ofReal (Real.exp (A' + 1)) := by
    refine hZ'.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [Real.exp_add]
    have := Real.exp_pos A'
    nlinarith
  obtain ⟨hi, hb⟩ := wr9_dv_abs π f hKL hΨm hlam (by linarith : 0 ≤ A' + 1) hZ
  have hrel : ∀ X : EucConfig d N,
      |HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a| = (N : ℝ)⁻¹ * |Ψ X| := by
    intro X
    rw [s32_linear_stat X ha hN, abs_mul, abs_of_pos (inv_pos.2 (by exact_mod_cast hN))]
  simp only [hrel]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  calc (N : ℝ)⁻¹ * ∫ X, |Ψ X| ∂f ≤ (N : ℝ)⁻¹ * (lam⁻¹ * ((InformationTheory.klDiv f π).toReal + (A' + 1))) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hN0.le)
    _ = ((N : ℝ) * lam)⁻¹ * ((InformationTheory.klDiv f π).toReal + (N * A ^ 2 * lam ^ 2 / 2 + 1)) := by
        rw [mul_inv, ← mul_assoc]

/-! ### The commutator kernel -/

theorem s32_commN_eq (s : ℝ) (v : Euc d → Euc d) (X : EucConfig d N) (μ : Measure (Euc d)) :
    commN d s v X μ = 2 * pairEnergy (commutatorKernel d s v) X μ := by
  unfold commN centeredPairFunctional pairEnergy
  ring

theorem s32_pairEnergy_const_mul (c : ℝ) (h : Euc d → Euc d → ℝ) (X : EucConfig d N)
    (μ : Measure (Euc d)) :
    pairEnergy (fun x y => c * h x y) X μ = c * pairEnergy h X μ := by
  unfold pairEnergy
  simp only [integral_const_mul, ← Finset.mul_sum]
  ring

theorem s32_rieszWeight_nonneg (s : ℝ) (z : Euc d) : 0 ≤ rieszWeight s z := by
  unfold rieszWeight
  split_ifs
  · exact le_max_right _ _
  · exact Real.rpow_nonneg (norm_nonneg _) _

/-- The commutator kernel of a `1`-Lipschitz field is in the class `IsBoundedPairKernel s (s+1)`,
for every `0 ≤ s` (`commutatorKernel_isBounded_proof` needs `0 < s`; at `s = 0` the bound is
`|h| ≤ 1`). -/
theorem s32_comm_isBounded {s : ℝ} (hs0 : 0 ≤ s) {v : Euc d → Euc d} (hv : LipschitzWith 1 v) :
    IsBoundedPairKernel s (s + 1) (commutatorKernel d s v) := by
  refine ⟨HRS.MS.Comm.comm_meas v hv.continuous.measurable, HRS.MS.Comm.comm_symm v,
    fun x y hxy => ?_⟩
  have hW := s32_rieszWeight_nonneg (d := d) s (x - y)
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hzpos : 0 < ‖x - y‖ := norm_pos_iff.mpr hz
    have hG : ‖rieszKernelGrad d 0 (x - y)‖ = ‖x - y‖⁻¹ := by
      rw [movtr_rieszKernelGrad_norm 0 le_rfl hz]
      norm_num [movtr_sigma, Real.rpow_neg_one]
    have key : |commutatorKernel d 0 v x y| ≤ 1 := by
      unfold commutatorKernel
      calc |inner ℝ (v x - v y) (rieszKernelGrad d 0 (x - y))|
          ≤ ‖v x - v y‖ * ‖rieszKernelGrad d 0 (x - y)‖ := abs_real_inner_le_norm _ _
        _ ≤ (((1 : ℝ≥0) : ℝ) * ‖x - y‖) * ‖x - y‖⁻¹ :=
            mul_le_mul (HRS.MS.Comm.comm_lip hv x y) hG.le (norm_nonneg _) (by positivity)
        _ = 1 := by simp [mul_assoc, mul_inv_cancel₀ hzpos.ne']
    nlinarith
  · have := HRS.MS.Comm.comm_bound_pos hpos 1 v hv x y hxy
    simp only [NNReal.coe_one, mul_one] at this
    have h1 : s * (1 + rieszWeight s (x - y)) ≤ (s + 1) * (1 + rieszWeight s (x - y)) := by
      nlinarith
    linarith

/-- Scaling: `h_v = Λ h_{Λ⁻¹ v}`. -/
theorem s32_commKernel_scale (s : ℝ) {Λ : ℝ≥0} (hΛ : Λ ≠ 0) (v : Euc d → Euc d) (x y : Euc d) :
    commutatorKernel d s v x y = (Λ : ℝ) * commutatorKernel d s ((Λ : ℝ)⁻¹ • v) x y := by
  have h : (Λ : ℝ) ≠ 0 := by exact_mod_cast hΛ
  unfold commutatorKernel
  simp only [Pi.smul_apply, ← smul_sub, real_inner_smul_left]
  field_simp

theorem s32_lipschitz_scale {Λ : ℝ≥0} (hΛ : Λ ≠ 0) {v : Euc d → Euc d} (hv : LipschitzWith Λ v) :
    LipschitzWith 1 ((Λ : ℝ)⁻¹ • v) := by
  have h : (0 : ℝ) < Λ := by exact_mod_cast pos_iff_ne_zero.2 hΛ
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [Pi.smul_apply, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 h), NNReal.coe_one, one_mul]
  have := HRS.MS.Comm.comm_lip hv x y
  calc (Λ : ℝ)⁻¹ * ‖v x - v y‖ ≤ (Λ : ℝ)⁻¹ * ((Λ : ℝ) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left this (inv_nonneg.2 h.le)
    _ = ‖x - y‖ := by field_simp

theorem s32_commN_zero (s : ℝ) {v : Euc d → Euc d} (hv : LipschitzWith 0 v) (X : EucConfig d N)
    (μ : Measure (Euc d)) : commN d s v X μ = 0 := by
  have hconst : ∀ x y, v x = v y := fun x y => by
    have := HRS.MS.Comm.comm_lip hv x y
    simp only [NNReal.coe_zero, zero_mul] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have hv0 : ∀ x y, v x - v y = 0 := fun x y => sub_eq_zero.2 (hconst x y)
  unfold commN centeredPairFunctional commutatorKernel
  simp [hv0]

/-! ### Entropy monotonicity along an invariant strong solution -/

/-- **Entropy decreases along the flow** (the reweighting argument of SCOPE_A S3.2).  If the
canonical particle dynamics `D` leaves `Q` invariant (`hInv`, for every realization started from `Q`
and independent of the Brownian motion) and a realization has initial law `Q.withDensity r`
(`r > 0` measurable) with `H(law X₀ | Q) < ∞`, then `H(law (X t) | Q) ≤ H(law X₀ | Q)`.
Proof: `P' = r(X₀)⁻¹ P` makes `X` a realization started from `Q` (`hInv` gives `law_{P'}(X t) = Q`),
and `H(law_P X_t | Q) = H(law_P X_t | law_{P'} X_t) ≤ H(P | P') = H(law X₀ | Q)` (data
processing, `klDiv_map_le`). -/
theorem s32_entropy_nonincreasing {d N : ℕ} (D : WholeDyn d)
    (Q : Measure (EucConfig d N)) [IsProbabilityMeasure Q]
    (hInv : ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (T : ℝ) (X₀' : Ω' → EucConfig d N) (W' : ℝ≥0 → Ω' → (Fin N → Euc d))
      (X' : ℝ≥0 → Ω' → EucConfig d N), IsVectorBrownian P' W' →
      IndepFun X₀' (fun ζ t => W' t ζ) P' → law P' X₀' = Q →
      IsWholeStrongSolution P' D T X₀' W' X' → ∀ t : ℝ≥0, (t : ℝ) ≤ T → law P' (X' t) = Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ)
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hW : IsVectorBrownian P W) (hind : IndepFun X₀ (fun ζ t => W t ζ) P)
    {r : EucConfig d N → ℝ} (hr : Measurable r) (hpos : ∀ x, 0 < r x)
    (hlaw : law P X₀ = Q.withDensity (fun x => ENNReal.ofReal (r x)))
    (hKL : InformationTheory.klDiv (law P X₀) Q ≠ ∞)
    (hsol : IsWholeStrongSolution P D T X₀ W X) (t : ℝ≥0) (ht : (t : ℝ) ≤ T) :
    InformationTheory.klDiv (law P (X t)) Q ≤ InformationTheory.klDiv (law P X₀) Q := by
  have hX0m : Measurable (X 0) := hsol.adapted 0
  have hXX : X 0 =ᵐ[P] X₀ := hsol.init
  have hmap0 : P.map (X 0) = P.map X₀ := Measure.map_congr hXX
  have hlaw0 : P.map (X 0) = Q.withDensity (fun x => ENNReal.ofReal (r x)) := by
    rw [hmap0]; exact hlaw
  have hKL0 : InformationTheory.klDiv (P.map (X 0)) Q ≠ ∞ := by rw [hmap0]; exact hKL
  have hind0 : IndepFun (X 0) (fun ζ t => W t ζ) P := hind.congr hXX.symm Filter.EventuallyEq.rfl
  have hk : Measurable (fun x : EucConfig d N => ENNReal.ofReal (r x)⁻¹) :=
    ENNReal.measurable_ofReal.comp hr.inv
  have hk1 := s32_pullback_one P hX0m hr hpos hlaw0
  have hP'prob := s32_pullback_prob P hX0m hr hpos hlaw0
  set P' := P.withDensity (fun ζ => ENNReal.ofReal (r (X 0 ζ))⁻¹) with hP'
  have hac : P' ≪ P := withDensity_absolutelyContinuous _ _
  have hBM : IsVectorBrownian P' W :=
    s32_isVectorBrownian_wd P hX0m (k := fun x : EucConfig d N => ENNReal.ofReal (r x)⁻¹) hk hk1
      hW hind0
  have hind' : IndepFun (X 0) (fun ζ t => W t ζ) P' :=
    s32_wd_indep P hX0m (k := fun x : EucConfig d N => ENNReal.ofReal (r x)⁻¹) hk hk1 hind0
  have hmapQ : law P' (X 0) = Q := s32_pullback_map P hX0m hr hpos hlaw0
  have hsol' : IsWholeStrongSolution P' D T (X 0) W X :=
    ⟨Filter.Eventually.of_forall fun _ => rfl, hac.ae_le hsol.eqn, hac.ae_le hsol.cont,
      hsol.adapted, hac.ae_le hsol.no_collision⟩
  have h : law P' (X t) = Q := hInv P' T (X 0) W X hBM hind' hmapQ hsol' t ht
  calc InformationTheory.klDiv (law P (X t)) Q
      = InformationTheory.klDiv (P.map (X t)) (P'.map (X t)) := by
        show InformationTheory.klDiv (P.map (X t)) Q = _
        rw [show P'.map (X t) = Q from h]
    _ ≤ InformationTheory.klDiv P P' := InformationTheory.klDiv_map_le P P' (hsol.adapted t)
    _ = InformationTheory.klDiv (P.map (X 0)) Q := s32_kl_pullback P hX0m hr hpos hlaw0 hKL0
    _ = InformationTheory.klDiv (law P X₀) Q := by rw [hmap0]

end HRS.MS.PrepStat
