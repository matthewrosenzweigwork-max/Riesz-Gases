import HRS.MS.WsInitGAux6
import HRS.MS.WsStatAux14
import HRS.MS.WsStatAux11
import HRS.MS.WsStatAux4

/-!
# S21 packet G, part 7: coordinates of the initial `K`-state and the cosine series of the orbit

* `s21g_k0_eval`: `coord (evalA (s56k0 C m T σ ν μ')(t))_α = σ (pair ν (U^{0,t}φ_α) - pair μ' (U^{0,t}φ_α))` for arbitrary probability measures
  `ν, μ'` with finite first moment (generalisation of `s21_k0_eval_gen`).
* `s21g_series`: `∑_j coord (s21gVec σ t α)_j f_{σ j}(x) = U^{0,t}φ_α(x)` pointwise (reindexing of the cosine series).
* `s21g_meanEmp_norm_integrable`: finite second moments of the empirical measure give a first moment for `meanEmpirical`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS HRS.Whole HRS.MS.GenPath HRS.MP.RdRem

variable {d : ℕ}

theorem s21g_k0_eval (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ) (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (σ : ℝ) (ν μ' : Measure (Euc d)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ'] (hν : Integrable (fun x : Euc d => ‖x‖) ν)
    (hμ : Integrable (fun x : Euc d => ‖x‖) μ') {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) (α : MultiIndex d) :
    OscDual.coord ((s56k0 (S.coeff N) b.m b.T σ ν μ').evalA t) α =
      σ * (HRS.Whole.pair ν (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) -
        HRS.Whole.pair μ' (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) := by
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
  have hcl := s56_osc_classical b hbv S N ht α
  obtain ⟨B, hB⟩ := hcl.bdd 0 (Nat.zero_le _)
  have hh : ContDiff ℝ 1 (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) :=
    (hcl.c2 0 ⟨le_rfl, ht.1⟩).of_le (by norm_num)
  rw [HRS.MS.S52.s52_coord_evalA ht.1 ht.2]
  rw [s56_k0_inner (S.coeff N) b.m b.T σ |Cf| (abs_nonneg _) hmeas hbd ν μ' hν hμ
    (HRS.MS.S52.s52y1 b.m b.T t α)
    (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) hh B
    (fun z => by
      have := hB 0 ⟨le_rfl, ht.1⟩ z
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this)
    (fun a z => by
      rw [HRS.MS.S52.s52_pair_grad_y1 hC ht.2 a h0 z α]
      simp [ht.1])]
  rfl

/-- The pointwise cosine series of the orbit, in the enumeration `σ`. -/
theorem s21g_series {C : WholeCoeff d} {M T : ℝ} (hT : 0 < T) {k : ℕ}
    (hmem : ∀ n α, MemCb k (r2CosOrbitTest C M T n α))
    (hsum : Summable fun q : ℕ × MultiIndex d => cbNorm k (r2CosOrbitTest C M T q.1 q.2))
    (hcont : ∀ (α : MultiIndex d) (x : Euc d),
      ContinuousOn (fun t => propagatorW C 0 t (oscTestFun M α) x) (Set.Icc (0 : ℝ) T))
    (σ : ℕ ≃ ℕ × MultiIndex d) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) (x : Euc d) :
    HasSum (fun j : ℕ => SeqL2.coord (s21gVec σ hT t α) j * r2CosOrbitTest C M T (σ j).1 (σ j).2 x)
      (propagatorW C 0 t (oscTestFun M α) x) := by
  classical
  have h := s11p_orbit_hasSum C M hT hmem hsum hcont α x t ht
  set g : ℕ → ℕ := fun n => σ.symm (n, α) with hg
  have hginj : Function.Injective g := fun a b hab => by
    have := σ.symm.injective hab
    simpa using this
  set F : ℕ → ℝ := fun j => SeqL2.coord (s21gVec σ hT t α) j * r2CosOrbitTest C M T (σ j).1 (σ j).2 x with hF
  have hz : ∀ j ∉ Set.range g, F j = 0 := by
    intro j hj
    simp only [hF, s21gVec_coord]
    by_cases hα : (σ j).2 = α
    · exfalso
      apply hj
      refine ⟨(σ j).1, ?_⟩
      simp only [hg]
      have : ((σ j).1, α) = σ j := Prod.ext rfl hα.symm
      rw [this, Equiv.symm_apply_apply]
    · simp [hα]
  rw [← hginj.hasSum_iff hz]
  convert h using 1
  funext n
  simp only [Function.comp_apply, hF, hg, s21gVec_coord, Equiv.apply_symm_apply, if_true]
  rfl

theorem s21g_meanEmp_norm_integrable {N : ℕ} (hN : 0 < N) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → EucConfig d N) (hY : Measurable Y)
    (hmom : ∫⁻ ζ, ENNReal.ofReal (HRS.Whole.pair (HRS.Whole.empirical (Y ζ)) (fun x => ‖x‖ ^ 2)) ∂P < ⊤) :
    Integrable (fun x : Euc d => ‖x‖) (HRS.Whole.meanEmpirical (P.map Y)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set g : Ω → ℝ := fun ζ => HRS.Whole.pair (HRS.Whole.empirical (Y ζ)) (fun x => ‖x‖ ^ 2) with hg
  have hgm : Measurable g := by
    have e : g = fun ζ => (N : ℝ)⁻¹ * ∑ i, ‖Y ζ i‖ ^ 2 :=
      funext fun ζ => HRS.Whole.pair_empirical hN _ _
    rw [e]
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (measurable_norm.comp ((measurable_pi_apply i).comp hY)).pow_const 2)
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

end HRS.MS.S21
