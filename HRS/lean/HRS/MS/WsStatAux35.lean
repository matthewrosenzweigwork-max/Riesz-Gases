import HRS.MS.WsStatAux34

/-!
# S21 packet K-4: helper lemmas for the final assembly

* `s21_meanEmp_norm_integrable`: finite second moment of the empirical measure gives a first moment for `meanEmpirical`.
* `s21IP_meas`: measurability of the centred initial path in the configuration.
* `s21_hrem_scale`: scaling of the remainder bound (`sigma = sqrt N sqrt beta`).
* `s21_dyn_setup`: `S.dyn N = quadraticGradientDyn`.
* `s21_energyMomentE_le`: `E_{N,1} <= ofReal (K delta_N + o_N)` from the stationary energy bound.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem
open HRS (Euc)

variable {d : ℕ}

theorem s21_meanEmp_norm_integrable {N : ℕ} (hN : 0 < N) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → EucConfig d N) (hY : Measurable Y)
    (hmom : ∫⁻ ζ, ENNReal.ofReal (HRS.Whole.pair (HRS.Whole.empirical (Y ζ)) (fun x => ‖x‖ ^ 2)) ∂P < ⊤) :
    Integrable (fun x : Euc d => ‖x‖) (HRS.Whole.meanEmpirical (P.map Y)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set g : Ω → ℝ := fun ζ => HRS.Whole.pair (HRS.Whole.empirical (Y ζ)) (fun x => ‖x‖ ^ 2) with hg
  have hgm : Measurable g := s21_pair_emp_meas hN Y hY (measurable_norm.pow_const 2)
  have hg0 : ∀ ζ, 0 ≤ g ζ := fun ζ => by
    simp only [hg]
    rw [HRS.Whole.pair_empirical hN]
    positivity
  have hgi : Integrable g P := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have : ∀ ζ, ‖g ζ‖ₑ = ENNReal.ofReal (g ζ) := fun ζ => by
      rw [Real.enorm_eq_ofReal (hg0 ζ)]
    simp_rw [this]
    exact hmom
  have hi : ∀ i : Fin N, Integrable (fun ζ => ‖Y ζ i‖) P := by
    intro i
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add (hgi.const_mul (N : ℝ)))
      ((continuous_norm.measurable.comp_aemeasurable ((measurable_pi_apply i).comp hY).aemeasurable).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have h1 : ‖Y ζ i‖ ^ 2 ≤ N * g ζ := by
      simp only [hg]
      rw [HRS.Whole.pair_empirical hN]
      rw [← mul_assoc, mul_inv_cancel₀ hNr.ne', one_mul]
      exact Finset.single_le_sum (f := fun j => ‖Y ζ j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    show ‖Y ζ i‖ ≤ 1 + N * g ζ
    nlinarith [sq_nonneg (‖Y ζ i‖ - 1)]
  rw [s21_meanEmpirical_eq_sum]
  refine Integrable.smul_measure ?_ (by simpa using hN.ne')
  refine integrable_finsetSum_measure.2 fun i _ => ?_
  rw [Measure.map_map (measurable_pi_apply i) hY]
  haveI : IsProbabilityMeasure (P.map (fun ζ => Y ζ i)) :=
    (Measure.isProbabilityMeasure_map_iff ((measurable_pi_apply i).comp hY).aemeasurable).2 inferInstance
  exact (integrable_map_measure continuous_norm.aestronglyMeasurable
    ((measurable_pi_apply i).comp hY).aemeasurable).2 (hi i)

theorem s21IP_meas (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (νb : Measure (Euc d)) [IsProbabilityMeasure νb]
    (hν : Integrable (fun x : Euc d => ‖x‖) νb) :
    Measurable (s21IP b.m b.T hbv.hT.le (S.coeff N) N νb) := by
  have hT : 0 ≤ b.T := hbv.hT.le
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b.T := ⟨le_rfl, hT⟩
  obtain ⟨Cf, hCf⟩ := HRS.MS.Star.general_orbits_features_proof b hbv
  have hbd : ∀ (a : Fin d) (z : Euc d), ‖gradFeature (S.coeff N) b.m b.T a 0 z‖ ≤ |Cf| := fun a z => by
    have := (hCf S N a 0 h0).2 0 (Nat.zero_le _) z
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (le_abs_self _)
  have hmeas : ∀ a : Fin d, Measurable fun z : Euc d => gradFeature (S.coeff N) b.m b.T a 0 z := by
    intro a
    have := (s56_feat_meas b hbv S N hC a).comp (measurable_const (a := (0 : ℝ)).prodMk measurable_id)
    have e := mrrClamp_of_mem h0
    simp only [Function.comp_def, e] at this
    exact this
  exact (s56EvalPath hT).continuous.measurable.comp
    (s56_k0_meas (S.coeff N) b.m b.T (Real.sqrt N) |Cf| (abs_nonneg _) hmeas hbd (by omega) νb hν)

theorem s21_hrem_scale {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (c : ℝ) (hc : 0 ≤ c)
    {ι : Type*} {J : Type*} [Nonempty J] (v : J → ι → Ω → ℝ) :
    (∫⁻ ζ, (⨆ t : J, l2NormE (fun α : ι => c * v t α ζ)) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal c * (∫⁻ ζ, (⨆ t : J, l2NormE (fun α : ι => v t α ζ)) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
  have h1 : ∀ ζ, (⨆ t : J, l2NormE (fun α : ι => c * v t α ζ)) =
      ENNReal.ofReal c * ⨆ t : J, l2NormE (fun α : ι => v t α ζ) := fun ζ => by
    simp_rw [s56_l2NormE_mul, abs_of_nonneg hc]
    rw [ENNReal.mul_iSup]
  simp_rw [h1, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.rpow_mul]
  norm_num

theorem s21_dyn_setup {s a β T : ℝ} {θ : Euc d → ℝ} {Λ K C₀ : ℝ}
    (S : WholeSetup (s21Bounds d s a β T θ Λ K C₀)) (hinv' : ∀ N, S.invβ N = β⁻¹) (N : ℕ) :
    S.dyn N = quadraticGradientDyn d s a β := by
  rw [s21_dyn_eq]
  unfold WholeSetup.dyn
  rw [hinv' N]
  rfl

theorem s21_energyMomentE_le {b : WholeBounds d} (S : WholeSetup b) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N) {Kε : ℝ}
    (hint : ∀ t ∈ Set.Icc (0 : ℝ) b.T, Integrable (fun ζ => |rieszModulatedEnergy d b.s (X (Real.toNNReal t) ζ)
        (HRS.Whole.withDensityReal (S.ρ N t))|) P)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) b.T, ∫ ζ, |rieszModulatedEnergy d b.s (X (Real.toNNReal t) ζ)
        (HRS.Whole.withDensityReal (S.ρ N t))| ∂P ≤ Kε)
    (ho : 0 ≤ HRS.oN d b.s b.C₀ N) :
    S.energyMomentE N 1 P X ≤ ENNReal.ofReal (Kε + HRS.oN d b.s b.C₀ N) := by
  unfold WholeSetup.energyMomentE
  refine iSup_le fun t => ?_
  have ht := t.2
  simp only [ENNReal.rpow_one, div_one]
  have hi : Integrable (fun ζ => |rieszModulatedEnergy d b.s (X (Real.toNNReal t) ζ)
      (HRS.Whole.withDensityReal (S.ρ N t))| + HRS.oN d b.s b.C₀ N) P := (hint t ht).add (integrable_const _)
  calc ∫⁻ ζ, ENNReal.ofReal |rieszModulatedEnergy d b.s (X (Real.toNNReal t) ζ)
        (HRS.Whole.withDensityReal (S.ρ N t)) + HRS.oN d b.s b.C₀ N| ∂P
      ≤ ∫⁻ ζ, ENNReal.ofReal (|rieszModulatedEnergy d b.s (X (Real.toNNReal t) ζ)
        (HRS.Whole.withDensityReal (S.ρ N t))| + HRS.oN d b.s b.C₀ N) ∂P :=
        lintegral_mono fun ζ => ENNReal.ofReal_le_ofReal (by
          refine (abs_add_le _ _).trans ?_
          rw [abs_of_nonneg ho])
    _ = ENNReal.ofReal (∫ ζ, (|rieszModulatedEnergy d b.s (X (Real.toNNReal t) ζ)
        (HRS.Whole.withDensityReal (S.ρ N t))| + HRS.oN d b.s b.C₀ N) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hi
          (Filter.Eventually.of_forall fun ζ => add_nonneg (abs_nonneg _) ho)).symm
    _ ≤ ENNReal.ofReal (Kε + HRS.oN d b.s b.C₀ N) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_add (hint t ht) (integrable_const _), integral_const]
        have := hb t ht
        simp
        linarith

end HRS.MS.S21
