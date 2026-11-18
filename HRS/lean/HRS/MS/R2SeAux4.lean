import HRS.MS.R2SeAux3

/-!
# S9.9 `r2_static_edgeworth`, packet 4: the Stein remainder is the centred pair energy

Worker S99, namespace `S99`.  For the commutator kernel `h = commutatorKernel d s (∇χ)` of a corrector (`‖D²χ‖ ≤ B₂`):

* `s99_pairE_decomp`: `pairEnergy h X μ = ½ D_N(h;ν) - μ_N(H_μ - H_ν) + const` (pure algebra);
* `s99_Rp_eq`: the Stein remainder of S4.6, `s45_Rp μ ν Q h = -(pairEnergy h X μ - E_Q pairEnergy h)`, i.e. `R = -B_N/N` with
  `B_N = N(F^h_N - E F^h_N)` (the quadratic statistic of the TeX proof, S L7580-7583).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_pairE_decomp (hN : 1 ≤ N) (h : Euc d → Euc d → ℝ) (X : EucConfig d N)
    (μ ν : Measure (Euc d)) :
    pairEnergy h X μ = (1 / 2) * centeredPairFunctional h X ν -
      pair (empirical X) (fun x => (∫ y, h x y ∂μ) - ∫ y, h x y ∂ν) +
      (1 / 2) * ((∫ x, ∫ y, h x y ∂μ ∂μ) - ∫ x, ∫ y, h x y ∂ν ∂ν) := by
  have hN' : 0 < N := hN
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  rw [pair_empirical hN', Finset.sum_sub_distrib]
  unfold pairEnergy centeredPairFunctional
  field_simp
  ring

theorem s99_Rp_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ C c BU Cs : ℝ}
    (hT : ThermalData d s a β C c BU) (hN : 2 ≤ N) (hS : S46.S46Static d s a β γ Cs N)
    {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ) {B2 : ℝ} (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2)
    (X : EucConfig d N) :
    s45_Rp (thermalMeasure d s a β) (S46.s46_nu d s a β γ N) (S46.s46_P d s a β γ N)
        (commutatorKernel d s (gradient χ)) X =
      -(pairEnergy (commutatorKernel d s (gradient χ)) X (thermalMeasure d s a β) -
        ∫ Y, pairEnergy (commutatorKernel d s (gradient χ)) Y (thermalMeasure d s a β)
          ∂(S46.s46_P d s a β γ N)) := by
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := hS.prob
  set P := S46.s46_P d s a β γ N with hPdef
  set μ := thermalMeasure d s a β with hμdef
  set v := gradient χ with hvdef
  set h := commutatorKernel d s v with hhdef
  set ν := S46.s46_nu d s a β γ N with hνdef
  haveI hνprob : IsProbabilityMeasure ν := by
    have : ν = P.map (fun X : EucConfig d N => X ⟨0, by omega⟩) := by
      rw [hνdef]; unfold S46.s46_nu firstMarginal; rw [dif_pos (by omega)]
    rw [this]
    constructor
    rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ]
    simp
  haveI hμprob : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hv1 : ContDiff ℝ 1 v := s45_contDiff_gradient hχ
  have hvd : Differentiable ℝ v := hv1.differentiable one_ne_zero
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  set Λ : ℝ≥0 := ⟨B2, hB20⟩ with hΛdef
  have hLip : LipschitzWith Λ v := lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
    have := hB2 x
    rw [← NNReal.coe_le_coe, coe_nnnorm]; exact this)
  have hhm : Measurable (Function.uncurry h) :=
    HRS.MS.Comm.comm_meas (s := s) v hv1.continuous.measurable
  obtain ⟨φN, hφNm, hνeq, hφNb, hφN2, hφNn⟩ := hS.marg
  obtain ⟨Bh, hBh0, hBh⟩ := s45_Hbounds hd hs0 hsd hT hLip hφNb hφNm ν hνeq
  set Hd : Euc d → ℝ := fun x => (∫ y, h x y ∂μ) - ∫ y, h x y ∂ν with hHd
  have hHd_meas : Measurable Hd :=
    ((hhm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable).sub
      (hhm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hHd_bd : ∀ x, |Hd x| ≤ 2 * Bh := fun x => by
    obtain ⟨h1, h2⟩ := hBh x
    calc |Hd x| ≤ |∫ y, h x y ∂μ| + |∫ y, h x y ∂ν| := abs_sub _ _
      _ ≤ 2 * Bh := by linarith
  have hDm : Measurable fun X : EucConfig d N => centeredPairFunctional h X ν :=
    HRS.MS.Wr.wr14a_measurable_D hhm ν
  obtain ⟨-, hq⟩ := hS.comm Λ v hLip
  have hDi : Integrable (fun X : EucConfig d N => centeredPairFunctional h X ν) P := by
    have hlt : evariance (fun X : EucConfig d N => centeredPairFunctional h X ν) P < ⊤ :=
      lt_of_le_of_lt hq.2.2 ENNReal.ofReal_lt_top
    exact ((evariance_lt_top_iff_memLp hDm.aestronglyMeasurable).1 hlt).integrable one_le_two
  have hYi : Integrable (fun X : EucConfig d N => pair (empirical X) Hd) P :=
    Integrable.of_bound (s45_measurable_pair_empirical hN1 hHd_meas).aestronglyMeasurable (2 * Bh)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact s45_abs_pair_empirical_le hN1 hHd_bd X)
  have hEY : ∫ X, pair (empirical X) Hd ∂P = pair ν Hd :=
    s45_E_pair_empirical hN1 hS.exch hHd_meas hHd_bd
  set K0 : ℝ := (1 / 2) * ((∫ x, ∫ y, h x y ∂μ ∂μ) - ∫ x, ∫ y, h x y ∂ν ∂ν) with hK0
  have hpe : ∀ X : EucConfig d N, pairEnergy h X μ =
      (1 / 2) * centeredPairFunctional h X ν - pair (empirical X) Hd + K0 :=
    fun X => s99_pairE_decomp hN1 h X μ ν
  have h1 : Integrable (fun Y : EucConfig d N => (1 / 2) * centeredPairFunctional h Y ν) P :=
    hDi.const_mul _
  have e1 : ∫ Y : EucConfig d N, ((1 / 2) * centeredPairFunctional h Y ν - pair (empirical Y) Hd + K0) ∂P =
      (∫ Y : EucConfig d N, (1 / 2) * centeredPairFunctional h Y ν ∂P) -
        ∫ Y : EucConfig d N, pair (empirical Y) Hd ∂P + K0 := by
    have h2 : Integrable (fun Y : EucConfig d N => (1 / 2) * centeredPairFunctional h Y ν -
        pair (empirical Y) Hd) P := h1.sub hYi
    rw [integral_add h2 (integrable_const _), integral_sub h1 hYi]
    simp
  have hint : ∫ Y, pairEnergy h Y μ ∂P =
      (1 / 2) * ∫ Y, centeredPairFunctional h Y ν ∂P - pair ν Hd + K0 := by
    simp_rw [hpe]
    rw [e1, integral_const_mul, hEY]
  rw [hint, hpe X]
  unfold s45_Rp
  ring

end S99

end
