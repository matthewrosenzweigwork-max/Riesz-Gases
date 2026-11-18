import HRS.MS.CritWholeCRDefs

/-!
# S8.1 XS, CR01: pole-tilt duality for bounded tests, with the `L²(μ)` norm of the test

For `f` bounded, `|∫ f d(pole marginal) - ∫ f d(cavity marginal)| ≤ C ‖f‖_{L²(μ)} r_N` uniformly in `x` and `t ∈ [0,1]`:
the exchangeable statistic `A_f = n⁻¹ ∑ f(Y_i)` is compared by the generic `EF.ef_tv` along `P_0.tilted (t X_x)` (variances
from `wr13b_pole_variance`, midpoint second difference from `CavResp.cgf_diff_mono` and `wr13c2_insDefect_le`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

/-- `n⁻¹ ∑ f(Y_j)`. -/
def fracOf {n : ℕ} (f : Euc d → ℝ) (Y : EucConfig d n) : ℝ := (1 / (n : ℝ)) * ∑ j, f (Y j)

theorem s81b_integral_frac {n : ℕ} (hn : 0 < n) {f : Euc d → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ y, |f y| ≤ B) (Pm : Measure (EucConfig d n)) [IsProbabilityMeasure Pm]
    (hR : HRS.External.Entropy.IsExchangeable Pm) :
    ∫ Y, fracOf f Y ∂Pm = ∫ y, f y ∂(Pm.map (fun Y => Y ⟨0, hn⟩)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold fracOf
  have hj : ∀ j : Fin n, Integrable (fun Y : EucConfig d n => f (Y j)) Pm := fun j =>
    Integrable.of_bound (C := B) (hf.comp (measurable_pi_apply j)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Y => by simpa [Real.norm_eq_abs] using hB (Y j))
  rw [integral_const_mul, integral_finset_sum _ fun j _ => hj j]
  have : ∀ j : Fin n, ∫ Y, f (Y j) ∂Pm = ∫ y, f y ∂(Pm.map (fun Y => Y ⟨0, hn⟩)) := by
    intro j
    rw [← hR.marginal_eq j ⟨0, hn⟩, integral_map (measurable_pi_apply j).aemeasurable hf.aestronglyMeasurable]
  simp_rw [this]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem s81b_abs_frac_le {n : ℕ} (hn : 0 < n) {f : Euc d → ℝ} {B : ℝ} (hB : ∀ y, |f y| ≤ B)
    (Y : EucConfig d n) : |fracOf f Y| ≤ B := by
  unfold fracOf
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_mul, abs_of_pos (by positivity)]
  have : |∑ j, f (Y j)| ≤ n * B := by
    calc _ ≤ ∑ j, |f (Y j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, B := Finset.sum_le_sum fun j _ => hB _
      _ = n * B := by simp
  calc 1 / (n : ℝ) * |∑ j, f (Y j)| ≤ 1 / (n : ℝ) * (n * B) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = B := by field_simp

theorem s81b_frac_meas {n : ℕ} {f : Euc d → ℝ} (hf : Measurable f) : Measurable (fracOf (n := n) f) :=
  (Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)).const_mul _

/-- `sqrt (log (e N)) ≤ 3 sqrt (log N)` for `N ≥ 2`, i.e. `sqrt (δ_N/N) ≤ 3 r_N`. -/
theorem s81b_sqrt_delta_le (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) :
    Real.sqrt (deltaN d ((d : ℝ) / 2) N / N) ≤ 3 * rate N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
  have hlogpos : 0 < Real.log N := by linarith
  have hδ : deltaN d ((d : ℝ) / 2) N = (N : ℝ)⁻¹ * Real.log (Real.exp 1 * N) := by
    simp only [deltaN, lt_self_iff_false, if_false, if_true]
  have hl : Real.log (Real.exp 1 * N) = 1 + Real.log N := by
    rw [Real.log_mul (Real.exp_pos _).ne' hN0.ne', Real.log_exp]
  have : deltaN d ((d : ℝ) / 2) N / N = (1 + Real.log N) / (N : ℝ) ^ 2 := by
    rw [hδ, hl]; field_simp
  rw [this, rate]
  have e : 3 * (Real.sqrt (Real.log N) / N) = Real.sqrt (9 * Real.log N / (N : ℝ) ^ 2) := by
    rw [show 9 * Real.log N / (N : ℝ) ^ 2 = (3 / N) ^ 2 * Real.log N by field_simp; norm_num, Real.sqrt_mul' _ hlogpos.le,
      Real.sqrt_sq (by positivity)]
    ring
  rw [e]
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_div_iff_of_pos_right (by positivity)]
  nlinarith

theorem s81b_pole_dual (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ f : Euc d → ℝ, Measurable f → ∀ B : ℝ, (∀ y, |f y| ≤ B) →
        |(∫ y, f y ∂(firstMarginal (pole D N x t))) -
            ∫ y, f y ∂(firstMarginal (cavity D N))| ≤
          C * l2Norm (mu D) f * rate N := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < ((d : ℝ) / 2) := by linarith
  have hsd : ((d : ℝ) / 2) < d := by linarith
  have hβp : 0 < βp := hβm.trans_le hβ
  obtain ⟨C₁, hC₁, hvar⟩ := wr13b_pole_variance hd hs0 hsd βp M
  obtain ⟨Cd, hCd0, hCd⟩ := wr13c2_insDefect_le hd hs0 hsd hβm βp M
  set K2 : ℝ := |Cd| * Real.exp |Cd| with hK2
  refine ⟨3 * (2 * Real.sqrt (2 * (C₁ * K2))), by positivity, fun D N hN x t ht f hfm B hB => ?_⟩
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hββp : D.beta ≤ βp := D.beta_mem.2
  have hprob : IsProbabilityMeasure (mu D) := Q34.isProbabilityMeasure_nu D.prob
  set μ : Measure (Euc d) := mu D with hμ
  have hconv := wr13a_conv_le_density hd1 hs0 hsd D.prob D.bound
  have hP0 : IsProbabilityMeasure (cavity D N) := wr13a_cavityLaw_isProb hs0 hconv hβ0.le N
  have hpos : 0 < N - 1 := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hpos
  have hnN : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hrate : 0 ≤ rate N := by unfold rate; positivity
  have hl2 : 0 ≤ l2Norm μ f := Real.sqrt_nonneg _
  have hfirst : ∀ P : Measure (EucConfig d (N - 1)), firstMarginal P = P.map (fun Y => Y ⟨0, hpos⟩) := by
    intro P; unfold firstMarginal; simp only [hpos, dite_true]
  have hfsq : ∫ y, f y ^ 2 ∂μ = l2Norm μ f ^ 2 := by
    unfold l2Norm; rw [Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)]
  have hfint : Integrable (fun y => f y ^ 2) μ :=
    Integrable.of_bound (C := B ^ 2) (hfm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        calc f y ^ 2 = |f y| ^ 2 := (sq_abs _).symm
          _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hB y) 2)
  -- the case t = 0
  rcases eq_or_lt_of_le ht.1 with h0 | htpos
  · have e0 : pole D N x t = cavity D N := by
      rw [← h0]; exact wr13c2_poleLaw_zero hs0 hconv hβ0.le N x
    rw [e0, sub_self, abs_zero]
    positivity
  set P0 := cavity D N with hP0def
  set X := wr13c2_X d ((d : ℝ) / 2) N D.beta x with hXdef
  have hXm : Measurable X := wr13c2_X_meas hs0 N D.beta x
  have hXb : ∀ Y, X Y ≤ 0 := wr13c2_X_le_zero hs0 hβ0.le N x
  have hXtm : Measurable (fun Y => t * X Y) := hXm.const_mul t
  have hXtb : ∀ Y, t * X Y ≤ 0 := fun Y => mul_nonpos_of_nonneg_of_nonpos ht.1 (hXb Y)
  have hδ := wr13c_deltaN_pos_le_one hd1 hs0 hsd (by omega : 1 ≤ N)
  obtain ⟨-, -, -, hΔ⟩ := hCd D.rho D.prob D.bound D.beta D.beta_mem.1 hββp N hN x
  have hcgf : ∀ u : ℝ, cgf (fun Y => t * X Y) P0 u = cgf X P0 (u * t) := by
    intro u; unfold cgf mgf; congr 1; refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
    simp only; congr 1; ring
  have hmid := CavResp.cgf_diff_mono (P := P0) hXm hXb htpos ht.2
  have hΔ' : cgf (fun Y => t * X Y) P0 1 - 2 * cgf (fun Y => t * X Y) P0 (1 / 2) ≤ |Cd| * deltaN d ((d : ℝ) / 2) N := by
    rw [hcgf, hcgf, one_mul, show 1 / 2 * t = t / 2 by ring]
    refine hmid.trans ?_
    have e1 := congrFun (wr13c2_insertionPressure_eq (d := d) (s := (d : ℝ) / 2) N D.beta (mu D) x) 1
    have e2 := congrFun (wr13c2_insertionPressure_eq (d := d) (s := (d : ℝ) / 2) N D.beta (mu D) x) (1 / 2)
    rw [e1, e2] at hΔ
    exact hΔ.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hδ.1.le)
  have hee := wr13c2_exp_sub_one_le _ |Cd| (deltaN d ((d : ℝ) / 2) N) hδ.1.le hδ.2 (abs_nonneg _) hΔ'
  have e1 : P0.tilted (fun Y => t * X Y) = pole D N x t := (wr13c2_poleLaw_eq_tilted hs0 hconv hβ0.le ht.1 N x).symm
  haveI hP1 := wr13c2_poleLaw_isProb hs0 hconv hβ0.le ht.1 N x
  have htv := HRS.MarginalAux.EF.ef_tv (P := P0) hXtm hXtb (s81b_frac_meas (n := N - 1) hfm)
    (fun Y => s81b_abs_frac_le hpos hB Y)
  have hint1 : ∫ Y, fracOf f Y ∂(P0.tilted (fun Y => t * X Y)) = ∫ y, f y ∂(firstMarginal (pole D N x t)) := by
    rw [e1, hfirst]
    exact s81b_integral_frac hpos hfm hB _ (wr13b_poleLaw_exchangeable hs0 hconv hβ0.le ht.1 N x)
  have hint0 : ∫ Y, fracOf f Y ∂P0 = ∫ y, f y ∂(firstMarginal P0) := by
    rw [hfirst]
    exact s81b_integral_frac hpos hfm hB _ (wr13c2_cavityLaw_exchangeable hs0 hconv hβ0.le N)
  rw [hint1, hint0] at htv
  -- the variances
  have hvarf : ∀ P : Measure (EucConfig d (N - 1)),
      evariance (fun Y : EucConfig d (N - 1) => ∑ i, f (Y i)) P ≤
        ENNReal.ofReal (C₁ * ((N - 1 : ℕ) : ℝ)) * ENNReal.ofReal (∫ y, f y ^ 2 ∂μ) →
      Var[fracOf (n := N - 1) f; P] ≤ (C₁ * l2Norm μ f ^ 2) / ((N - 1 : ℕ) : ℝ) := by
    intro P h
    have h2 : Var[fracOf (n := N - 1) f; P] =
        (1 / ((N - 1 : ℕ) : ℝ)) ^ 2 * (evariance (fun Y : EucConfig d (N - 1) => ∑ i, f (Y i)) P).toReal :=
      variance_const_mul (1 / ((N - 1 : ℕ) : ℝ)) (fun Y : EucConfig d (N - 1) => ∑ i, f (Y i)) P
    rw [h2]
    have h4 : (evariance (fun Y : EucConfig d (N - 1) => ∑ i, f (Y i)) P).toReal ≤
        C₁ * ((N - 1 : ℕ) : ℝ) * l2Norm μ f ^ 2 := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h
      rw [← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal (by positivity), hfsq] at this
      exact this
    calc (1 / ((N - 1 : ℕ) : ℝ)) ^ 2 * (evariance _ P).toReal
        ≤ (1 / ((N - 1 : ℕ) : ℝ)) ^ 2 * (C₁ * ((N - 1 : ℕ) : ℝ) * l2Norm μ f ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by field_simp
  have hf2 : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ y, f y ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hfint (Filter.Eventually.of_forall fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  have hpv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Var[fracOf (n := N - 1) f; pole D N x τ] ≤
      (C₁ * l2Norm μ f ^ 2) / ((N - 1 : ℕ) : ℝ) := by
    intro τ hτ
    refine hvarf _ ((hvar D.rho D.prob D.bound D.beta hβ0 hββp N hN x τ hτ f hfm).trans ?_)
    refine mul_le_mul' le_rfl ?_
    rw [← hf2]
    refine lintegral_mono fun y => ?_
    have : ENNReal.ofReal (Real.exp (-(τ * (D.beta / N)) * rieszKernel d ((d : ℝ) / 2) (x - y))) ≤ 1 := by
      refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 ?_)
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.2 (mul_nonneg hτ.1 (div_nonneg hβ0.le (Nat.cast_nonneg _)))) (wr13a_g_nonneg hs0 _)
    calc _ ≤ ‖f y‖ₑ ^ 2 * 1 := mul_le_mul' le_rfl this
      _ = _ := mul_one _
  have hV0 := hpv 0 ⟨le_rfl, zero_le_one⟩
  have hV1 := hpv t ht
  have e0 : pole D N x 0 = P0 := wr13c2_poleLaw_zero hs0 hconv hβ0.le N x
  rw [e0] at hV0
  rw [← e1] at hV1
  refine htv.trans ?_
  have hch := wr13c2_sqrt_chain (n := ((N - 1 : ℕ) : ℝ)) (N := (N : ℝ)) hn0 hN0 hnN
    (K1 := C₁ * l2Norm μ f ^ 2) (K2 := K2) (by positivity) (by positivity) hδ.1.le hV0 hV1 hee
  refine hch.trans ?_
  have hsq : Real.sqrt (2 * (C₁ * l2Norm μ f ^ 2 * K2)) = l2Norm μ f * Real.sqrt (2 * (C₁ * K2)) := by
    rw [show 2 * (C₁ * l2Norm μ f ^ 2 * K2) = l2Norm μ f ^ 2 * (2 * (C₁ * K2)) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hl2]
  rw [hsq]
  have h3 := s81b_sqrt_delta_le hd1 hN
  have hc : 0 ≤ l2Norm μ f * Real.sqrt (2 * (C₁ * K2)) := by positivity
  calc 2 * (l2Norm μ f * Real.sqrt (2 * (C₁ * K2))) * Real.sqrt (deltaN d ((d : ℝ) / 2) N / N)
      ≤ 2 * (l2Norm μ f * Real.sqrt (2 * (C₁ * K2))) * (3 * rate N) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

end HRS.Whole.S81b
