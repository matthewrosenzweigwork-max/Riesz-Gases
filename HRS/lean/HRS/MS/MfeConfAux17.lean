import HRS.MS.MfeConfAux16
import HRS.MP.SelfSimP4Gibbs
import HRS.MP.SelfSimP4Flow

/-!
# S.B.1, packets F10/F5 (initial second moment, flow hypotheses for the regularised laws)

* `sb1_canonW_le`: for `V ≥ c_V|x|² - C_V` (`c_V > 0`) and `s ≥ 0` the canonical Gibbs weight `e^{-βH_N}` is dominated by a Gaussian
  `M e^{-a‖Z‖²}` (the log kernel is bounded below by `-log(1+|x|)`);
* `sb1_moment_of_kl`: finite relative entropy with respect to a normalised weight with Gaussian majorant gives a finite second moment
  (Donsker-Varadhan, as `p4g_moment`);
* `sb1_init_moment`: the initial law of `WholeMFEHyp` has a finite second moment (from `gibbs_entropy`);
* `sb1_flow_hyp`: the laws of the regularised solutions `Y^M` satisfy `P4FlowHyp` (weak Fokker-Planck, moments, narrow continuity)
  by `p4_flow_hyp_proof`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

open HRS.MP.SelfSimP4Impl HRS.MP.SelfSimP4

variable {d N : ℕ}

theorem sb1_riesz_lower (s : ℝ) (hs0 : 0 ≤ s) (x : Euc d) :
    -Real.log (1 + ‖x‖) ≤ Whole.rieszKernel d s x := by
  unfold Whole.rieszKernel
  by_cases h : s = 0
  · simp only [h, ite_true]
    by_cases hx : ‖x‖ = 0
    · simp [hx]
    · have hx' : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
      have : Real.log ‖x‖ ≤ Real.log (1 + ‖x‖) := Real.log_le_log hx' (by linarith)
      linarith
  · simp only [h, ite_false]
    have h1 : 0 ≤ Real.log (1 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
    have h2 : 0 ≤ ‖x‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg x) _
    linarith

theorem sb1_pi_norm_sq_le (Z : Whole.EucConfig d N) : ‖Z‖ ^ 2 ≤ ∑ i, ‖Z i‖ ^ 2 := by
  have hs : 0 ≤ ∑ i, ‖Z i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have : ‖Z‖ ≤ Real.sqrt (∑ i, ‖Z i‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun i => ‖Z i‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  calc ‖Z‖ ^ 2 ≤ (Real.sqrt (∑ i, ‖Z i‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = ∑ i, ‖Z i‖ ^ 2 := Real.sq_sqrt hs

/-- Lower bound of the canonical Hamiltonian. -/
theorem sb1_H_lower {s : ℝ} (hs0 : 0 ≤ s) {V : Euc d → ℝ} {cV CV : ℝ} (hcV : 0 < cV)
    (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ V x) (Z : Whole.EucConfig d N) :
    (cV / 2) * ‖Z‖ ^ 2 - N * CV - 2 * (N : ℝ) ^ 2 / cV ≤
      Whole.canonicalHamiltonian (Whole.rieszKernel d s) V Z := by
  unfold Whole.canonicalHamiltonian
  have hA : cV * ‖Z‖ ^ 2 - N * CV ≤ ∑ i, V (Z i) := by
    calc cV * ‖Z‖ ^ 2 - N * CV ≤ cV * ∑ i, ‖Z i‖ ^ 2 - N * CV := by
          have := mul_le_mul_of_nonneg_left (sb1_pi_norm_sq_le Z) hcV.le
          linarith
      _ = ∑ i, (cV * ‖Z i‖ ^ 2 - CV) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp
      _ ≤ ∑ i, V (Z i) := Finset.sum_le_sum fun i _ => hV (Z i)
  have hterm : ∀ i j : Fin N, -(2 * ‖Z‖) ≤ Whole.rieszKernel d s (Z i - Z j) := by
    intro i j
    have h1 := sb1_riesz_lower s hs0 (Z i - Z j)
    have h2 : Real.log (1 + ‖Z i - Z j‖) ≤ ‖Z i - Z j‖ := by
      have := Real.log_le_sub_one_of_pos (by linarith [norm_nonneg (Z i - Z j)] : 0 < 1 + ‖Z i - Z j‖)
      linarith
    have h3 : ‖Z i - Z j‖ ≤ 2 * ‖Z‖ := by
      calc ‖Z i - Z j‖ ≤ ‖Z i‖ + ‖Z j‖ := norm_sub_le _ _
        _ ≤ ‖Z‖ + ‖Z‖ := add_le_add (norm_le_pi_norm Z i) (norm_le_pi_norm Z j)
        _ = 2 * ‖Z‖ := by ring
    linarith
  have hB : -(2 * (N : ℝ) * ‖Z‖) ≤ (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      Whole.rieszKernel d s (Z i - Z j) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    have hN : (0 : ℝ) < N := by exact_mod_cast h
    have hsum : -(2 * (N : ℝ) ^ 2 * ‖Z‖) ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        Whole.rieszKernel d s (Z i - Z j) := by
      calc -(2 * (N : ℝ) ^ 2 * ‖Z‖) = ∑ _i : Fin N, ∑ _j : Fin N, -(2 * ‖Z‖) := by
            simp; ring
        _ ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), -(2 * ‖Z‖) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hnn : 0 ≤ ‖Z‖ := norm_nonneg _
            calc ∑ _j : Fin N, -(2 * ‖Z‖) = -(N * (2 * ‖Z‖)) := by simp
              _ ≤ -(((Finset.univ.filter (fun j => i < j)).card : ℝ) * (2 * ‖Z‖)) := by
                  have : ((Finset.univ.filter (fun j => i < j)).card : ℝ) ≤ N := by
                    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
                  nlinarith
              _ = ∑ _j ∈ Finset.univ.filter (fun j => i < j), -(2 * ‖Z‖) := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    calc -(2 * (N : ℝ) * ‖Z‖) = (1 / (N : ℝ)) * (-(2 * (N : ℝ) ^ 2 * ‖Z‖)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  have hC : -(2 * (N : ℝ) * ‖Z‖) ≥ -((cV / 2) * ‖Z‖ ^ 2) - 2 * (N : ℝ) ^ 2 / cV := by
    have e : (cV / 2) * ‖Z‖ ^ 2 - 2 * N * ‖Z‖ + 2 * (N : ℝ) ^ 2 / cV =
        (cV * ‖Z‖ - 2 * N) ^ 2 / (2 * cV) := by field_simp; ring
    have hnn : 0 ≤ (cV * ‖Z‖ - 2 * N) ^ 2 / (2 * cV) := by positivity
    linarith
  linarith

theorem sb1_canonW_le {s : ℝ} (hs0 : 0 ≤ s) {V : Euc d → ℝ} {cV CV : ℝ} (hcV : 0 < cV)
    (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ V x) {β : ℝ} (hβ : 0 < β) (Z : Whole.EucConfig d N) :
    Real.exp (-β * Whole.canonicalHamiltonian (Whole.rieszKernel d s) V Z) ≤
      Real.exp (β * (N * CV + 2 * (N : ℝ) ^ 2 / cV)) * Real.exp (-((β * cV / 2) * ‖Z‖ ^ 2)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h := sb1_H_lower (N := N) hs0 hcV hV Z
  nlinarith [mul_le_mul_of_nonneg_left h hβ.le]

/-- Finite relative entropy with respect to a normalised weight with Gaussian majorant gives a finite second moment. -/
theorem sb1_moment_of_kl {G : Whole.EucConfig d N → ℝ} (hGm : Measurable G) {M a : ℝ} (ha : 0 < a)
    (hGle : ∀ x, G x ≤ M * Real.exp (-(a * ‖x‖ ^ 2))) (hZ0 : Whole.AppendixALemmas.gibbsPartitionW G ≠ 0)
    (hZt : Whole.AppendixALemmas.gibbsPartitionW G ≠ ⊤) (μ : Measure (Whole.EucConfig d N))
    [IsProbabilityMeasure μ] (hKL : klDiv μ (Whole.AppendixALemmas.gibbsRefW G) ≠ ⊤) :
    ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ < ⊤ := by
  haveI hQ := p4g_ref_prob G hGm hZ0 hZt
  set c : ℝ := a / 2 with hc
  have hcpos : 0 < c := by positivity
  set F : Whole.EucConfig d N → ℝ := fun x => c * ‖x‖ ^ 2 with hF
  have hFm : Measurable F := (measurable_norm.pow_const 2).const_mul _
  have hF0 : ∀ x, 0 ≤ F x := fun x => by positivity
  have hJ : ∫⁻ x, ENNReal.ofReal (Real.exp (F x)) * ENNReal.ofReal (G x) < ⊤ := by
    have hint : Integrable (fun Ξ : Whole.EucConfig d N => M * Real.exp (-(c * ‖Ξ‖ ^ 2))) volume :=
      (p4g_integrable_gauss_pi (c := c) hcpos).const_mul _
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hint.lintegral_lt_top
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc Real.exp (F x) * G x ≤ Real.exp (F x) * (M * Real.exp (-(a * ‖x‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left (hGle x) (Real.exp_pos _).le
      _ = M * Real.exp (-(c * ‖x‖ ^ 2)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          simp only [hF, hc]; ring
  set J := ∫⁻ x, ENNReal.ofReal (Real.exp (F x)) * ENNReal.ofReal (G x) with hJdef
  have hQint : ∫⁻ x, ENNReal.ofReal (Real.exp (F x)) ∂(Whole.AppendixALemmas.gibbsRefW G) =
      (Whole.AppendixALemmas.gibbsPartitionW G)⁻¹ * J := by
    unfold Whole.AppendixALemmas.gibbsRefW
    rw [lintegral_smul_measure, smul_eq_mul,
      lintegral_withDensity_eq_lintegral_mul _ hGm.ennreal_ofReal
        (show Measurable fun a => ENNReal.ofReal (Real.exp (F a)) from
          (Real.measurable_exp.comp hFm).ennreal_ofReal)]
    congr 1
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    rw [mul_comm]
  have hfinJ : (Whole.AppendixALemmas.gibbsPartitionW G)⁻¹ * J ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZ0) hJ.ne
  set q : ℝ := ((Whole.AppendixALemmas.gibbsPartitionW G)⁻¹ * J).toReal with hq
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hK : 0 ≤ Real.log (1 + q) := Real.log_nonneg (by linarith)
  have hZ : ∫⁻ x, ENNReal.ofReal (Real.exp (F x)) ∂(Whole.AppendixALemmas.gibbsRefW G) ≤
      ENNReal.ofReal (Real.exp (Real.log (1 + q))) := by
    rw [hQint, Real.exp_log (by linarith), ← ENNReal.ofReal_toReal hfinJ]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hdv := dv_lintegral (Whole.AppendixALemmas.gibbsRefW G) μ hKL hFm hF0 hK hZ
  have hlt : ∫⁻ x, ENNReal.ofReal (F x) ∂μ < ⊤ :=
    lt_of_le_of_lt hdv (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hKL, ENNReal.ofReal_lt_top⟩)
  have hrew : ∀ x : Whole.EucConfig d N, ENNReal.ofReal (‖x‖ ^ 2) =
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (F x) := fun x => by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [hF]
    field_simp
  simp_rw [hrew]
  rw [lintegral_const_mul _ hFm.ennreal_ofReal]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlt


theorem sb1_canonH_meas {g V : Euc d → ℝ} (hg : Measurable g) (hV : Measurable V) :
    Measurable fun X : Whole.EucConfig d N => Whole.canonicalHamiltonian g V X := by
  unfold Whole.canonicalHamiltonian
  refine Measurable.add (Finset.measurable_sum _ fun i _ => hV.comp (measurable_pi_apply i)) ?_
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_) _
  exact hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

theorem sb1_canonical_eq_ref {g V : Euc d → ℝ} {β : ℝ}
    (hint : Integrable fun X : Whole.EucConfig d N => Real.exp (-β * Whole.canonicalHamiltonian g V X)) :
    Whole.canonicalGibbs g V N β = Whole.AppendixALemmas.gibbsRefW
      (fun X : Whole.EucConfig d N => Real.exp (-β * Whole.canonicalHamiltonian g V X)) := by
  unfold Whole.canonicalGibbs Whole.AppendixALemmas.gibbsRefW Whole.AppendixALemmas.gibbsPartitionW
    Whole.canonicalPartition
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun X => (Real.exp_pos _).le)]

/-- **F10 (initial second moment)**: finite relative entropy with respect to the canonical Gibbs ensemble gives a finite
second moment, for a confining `V` and `s ≥ 0`. -/
theorem sb1_init_moment {Ω : Type*} [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {D : Whole.WholeDyn d} (hs0 : 0 ≤ D.s) (hβ : 0 < D.invβ) (hVm : Measurable D.V)
    (hcV : ∃ cV CV : ℝ, 0 < cV ∧ ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) {X₀ : Ω → Whole.EucConfig d N}
    (hent : relEntropy (Pm.map X₀) (Whole.canonicalGibbs (Whole.rieszKernel d D.s) D.V N (1 / D.invβ)) ≠ ⊤) :
    ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(Pm.map X₀) < ⊤ := by
  obtain ⟨cV, CV, hcV0, hV⟩ := hcV
  set β : ℝ := 1 / D.invβ with hβdef
  have hβ0 : 0 < β := by positivity
  set G : Whole.EucConfig d N → ℝ := fun X =>
    Real.exp (-β * Whole.canonicalHamiltonian (Whole.rieszKernel d D.s) D.V X) with hG
  have hGm : Measurable G := Real.measurable_exp.comp
    (measurable_const.mul (sb1_canonH_meas (sb1_measurable_rieszKernel D.s) hVm))
  set M : ℝ := Real.exp (β * (N * CV + 2 * (N : ℝ) ^ 2 / cV)) with hM
  set a : ℝ := β * cV / 2 with ha
  have ha0 : 0 < a := by positivity
  have hGle : ∀ x, G x ≤ M * Real.exp (-(a * ‖x‖ ^ 2)) := fun x =>
    sb1_canonW_le hs0 hcV0 hV hβ0 x
  have hgauss : Integrable (fun Ξ : Whole.EucConfig d N => M * Real.exp (-(a * ‖Ξ‖ ^ 2))) volume :=
    (p4g_integrable_gauss_pi (c := a) ha0).const_mul _
  have hint : Integrable G := by
    refine hgauss.mono' hGm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hGle x
  have hZt : Whole.AppendixALemmas.gibbsPartitionW G ≠ ⊤ := by
    unfold Whole.AppendixALemmas.gibbsPartitionW
    exact (lt_of_le_of_lt (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hGle x))
      hgauss.lintegral_lt_top).ne
  have hZ0 : Whole.AppendixALemmas.gibbsPartitionW G ≠ 0 :=
    (p4g_lintegral_pos_of_pos hGm fun x => Real.exp_pos _).ne'
  have heq : Whole.canonicalGibbs (Whole.rieszKernel d D.s) D.V N β =
      Whole.AppendixALemmas.gibbsRefW G := sb1_canonical_eq_ref hint
  have hKL : klDiv (Pm.map X₀) (Whole.AppendixALemmas.gibbsRefW G) ≠ ⊤ := by
    rw [← heq]; exact hent
  exact sb1_moment_of_kl hGm ha0 hGle hZ0 hZt (Pm.map X₀) hKL

/-- **F5**: the laws of the regularised solutions satisfy the flow hypotheses of the level-`M` analysis. -/
theorem sb1_flow_hyp (D : Whole.WholeDyn d) {B : ℝ} (P : Sb1Pot D.V B) {s r₀ : ℝ} {k : Euc d → ℝ}
    (hk : IsP4Kernel d s r₀ k) (hν : 0 ≤ D.invβ) {S : ℝ} (hS : 0 < S) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hY : P4AddSol Pm D.invβ (fun _ => sb1DriftM D k N) S ℱ W' W Y)
    (hm0 : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(law Pm (Y 0)) < ⊤) :
    P4FlowHyp D.invβ (fun _ => sb1DriftM D k N) S (fun r => law Pm (Y (Real.toNNReal r))) := by
  obtain ⟨K, hK⟩ := sb1_driftM_lip D hk P N
  have hbc : Continuous (Function.uncurry fun (_ : ℝ) => sb1DriftM D k N) :=
    hK.continuous.comp continuous_snd
  exact p4_flow_hyp_proof (b := fun _ => sb1DriftM D k N) Pm hν hS hbc ⟨K, fun _ _ => hK⟩ hY hm0

end HRS.MS.MfeConf
