import HRS.MS.S21G2_W00

/-!
# S21G2 W01 -- jet norm identity and linearity on smooth finite-energy test functions (R26-T3.W01)

`‖jet f‖ₑ = weightedSobolevE r P f` (the finite coordinate sum includes order zero) and `jet (f + c g) = jet f + c jet g`.
Contract verbatim (qualified names).  Helper names carry the prefix `s21g2_w01_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

section Aux

variable {d r : ℕ}

theorem s21g2_w01_pd_cont {f : HRS.Euc d → ℝ} (hf : ContDiff ℝ r f) {j : ℕ} (hj : j ≤ r)
    (i : Fin j → Fin d) : Continuous (HRS.Whole.partialDeriv i f) := by
  unfold HRS.Whole.partialDeriv
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => HRS.Euc d) ℝ
    (fun l => EuclideanSpace.single (i l) 1)).continuous.comp
    (hf.continuous_iteratedFDeriv (by exact_mod_cast hj))

theorem s21g2_w01_enorm_sq {ι : Type*} [Fintype ι] (z : EuclideanSpace ℝ ι) :
    ‖z‖ₑ ^ (2 : ℝ) = ∑ i, ENNReal.ofReal (z i ^ 2) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity),
    ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
  simp only [Real.norm_eq_abs, sq_abs]

theorem s21g2_w01_lint {f : HRS.Euc d → ℝ} (hf : ContDiff ℝ r f) (P : ℝ) :
    ∫⁻ x, ‖r26t3_jetfun r f x‖ₑ ^ (2 : ℝ) ∂(r26t3_weightMeasure d P) =
      ∑ j ∈ Finset.range (r + 1), ∑ i : Fin j → Fin d,
        ∫⁻ x, ENNReal.ofReal (HRS.Whole.jbracket x ^ (-2 * P) * (HRS.Whole.partialDeriv i f x) ^ 2) := by
  have hjb : Continuous (HRS.Whole.jbracket (d := d)) := by unfold HRS.Whole.jbracket; fun_prop
  have hw : Measurable (fun x : HRS.Euc d => ENNReal.ofReal (HRS.Whole.jbracket x ^ (-2 * P))) :=
    (hjb.measurable.pow_const _).ennreal_ofReal
  have hterm : ∀ i : JetIndex d r, Measurable (fun x : HRS.Euc d => ENNReal.ofReal
      (HRS.Whole.jbracket x ^ (-2 * P) * (HRS.Whole.partialDeriv i.2 f x) ^ 2)) := fun i =>
    ((hjb.measurable.pow_const _).mul
      ((s21g2_w01_pd_cont hf (Nat.lt_succ_iff.1 i.1.2) i.2).measurable.pow_const _)).ennreal_ofReal
  have hpt : ∀ x : HRS.Euc d, ENNReal.ofReal (HRS.Whole.jbracket x ^ (-2 * P)) *
      ‖r26t3_jetfun r f x‖ₑ ^ (2 : ℝ) =
      ∑ i : JetIndex d r, ENNReal.ofReal (HRS.Whole.jbracket x ^ (-2 * P) * (HRS.Whole.partialDeriv i.2 f x) ^ 2) :=
    fun x => by
    rw [s21g2_w01_enorm_sq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ENNReal.ofReal_mul (by unfold HRS.Whole.jbracket; positivity)]
    rfl
  have hg : Measurable (fun x : HRS.Euc d => ‖r26t3_jetfun r f x‖ₑ ^ (2 : ℝ)) := by
    simp_rw [s21g2_w01_enorm_sq]
    exact Finset.measurable_sum _ fun i _ =>
      ((s21g2_w01_pd_cont hf (Nat.lt_succ_iff.1 i.1.2) i.2).measurable.pow_const _).ennreal_ofReal
  unfold r26t3_weightMeasure
  rw [lintegral_withDensity_eq_lintegral_mul₀ hw.aemeasurable hg.aemeasurable]
  simp only [Pi.mul_apply, hpt]
  rw [lintegral_finsetSum _ fun i _ => hterm i, Fintype.sum_sigma]
  exact Fin.sum_univ_eq_sum_range
    (fun n => ∑ i : Fin n → Fin d, ∫⁻ x, ENNReal.ofReal
      (HRS.Whole.jbracket x ^ (-2 * P) * (HRS.Whole.partialDeriv i f x) ^ 2)) (r + 1)

end Aux

theorem s21g2_w01_pd_lin {d r : ℕ} {f g : HRS.Euc d → ℝ} (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g)
    (c : ℝ) {j : ℕ} (hj : j ≤ r) (i : Fin j → Fin d) (x : HRS.Euc d) :
    HRS.Whole.partialDeriv i (f + c • g) x =
      HRS.Whole.partialDeriv i f x + c * HRS.Whole.partialDeriv i g x := by
  have hfj : ContDiffAt ℝ j f x := (hf.of_le (by exact_mod_cast hj)).contDiffAt
  have hgj : ContDiffAt ℝ j g x := (hg.of_le (by exact_mod_cast hj)).contDiffAt
  unfold HRS.Whole.partialDeriv
  have e : f + c • g = f + fun y => c • g y := rfl
  rw [e, iteratedFDeriv_add_apply hfj (hgj.const_smul c), iteratedFDeriv_const_smul_apply' hgj]
  simp

theorem r26t3_jet_norm {d r : ℕ} (P : ℝ) (f : HRS.Euc d → ℝ) (hf : HRS.Whole.IsR2WeightedTest r P f) :
    MemLp (r26t3_jetfun r f) 2 (r26t3_weightMeasure d P) ∧
    ‖r26t3_jet r P f‖ₑ=HRS.Whole.weightedSobolevE r P f := by
  have hl := s21g2_w01_lint hf.1 P
  have hv : AEStronglyMeasurable (r26t3_jetfun r f) (r26t3_weightMeasure d P) := by
    refine Continuous.aestronglyMeasurable ?_
    unfold r26t3_jetfun
    exact (PiLp.continuous_toLp 2 (fun _ : JetIndex d r => ℝ)).comp
      (continuous_pi fun i => s21g2_w01_pd_cont hf.1 (Nat.lt_succ_iff.1 i.1.2) i.2)
  have hnorm : eLpNorm (r26t3_jetfun r f) 2 (r26t3_weightMeasure d P) =
      HRS.Whole.weightedSobolevE r P f := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hv]
    simp only [ENNReal.toReal_ofNat, hl, HRS.Whole.weightedSobolevE]
  have hmem : MemLp (r26t3_jetfun r f) 2 (r26t3_weightMeasure d P) := by
    show eLpNorm _ _ _ < ⊤
    rw [hnorm]; exact hf.2
  refine ⟨hmem, ?_⟩
  unfold r26t3_jet
  rw [dite_cond_eq_true (eq_true hmem), Lp.enorm_toLp hmem, hnorm]

theorem r26t3_jet_linear {d r : ℕ} (P : ℝ) (f g : HRS.Euc d → ℝ)
    (hf : HRS.Whole.IsR2WeightedTest r P f) (hg : HRS.Whole.IsR2WeightedTest r P g) (c : ℝ) :
    r26t3_jet r P (f+c•g)=r26t3_jet r P f+c•r26t3_jet r P g := by
  have hmf := (r26t3_jet_norm P f hf).1
  have hmg := (r26t3_jet_norm P g hg).1
  have hfun : r26t3_jetfun r (f + c • g) = r26t3_jetfun r f + c • r26t3_jetfun r g := by
    funext x
    ext i
    show HRS.Whole.partialDeriv i.2 (f + c • g) x =
      HRS.Whole.partialDeriv i.2 f x + c * HRS.Whole.partialDeriv i.2 g x
    exact s21g2_w01_pd_lin hf.1 hg.1 c (Nat.lt_succ_iff.1 i.1.2) i.2 x
  have hmc : MemLp (r26t3_jetfun r (f + c • g)) 2 (r26t3_weightMeasure d P) := by
    rw [hfun]; exact hmf.add (hmg.const_smul c)
  unfold r26t3_jet
  rw [dite_cond_eq_true (eq_true hmc), dite_cond_eq_true (eq_true hmf), dite_cond_eq_true (eq_true hmg), ← MemLp.toLp_const_smul c hmg, ← MemLp.toLp_add hmf (hmg.const_smul c)]
  congr 1

end HRS.MS.R26T3
