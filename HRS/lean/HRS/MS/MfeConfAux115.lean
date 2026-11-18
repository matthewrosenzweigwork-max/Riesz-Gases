import HRS.MS.MfeConfAux114

/-!
# S.B.1, packet F9 (part 18): the regularised strong solutions of the standing hypotheses, their laws and their limit

`sb1_Y_data`: on the probability space of `WholeMFEHyp` (horizon `T > 0`) the regularised additive-noise solutions
`Y^M` (kernel `k_M = sb1kM`) started at `X 0` exist, equal the selected singular solution `X` on `[0,T]` for `M ≥ M(ω)` a.s.,
and have the laws `sb1Flow D k_M N (law X 0) (Wiener) t`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.MD.EQLawPath HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_Y_data (D : Whole.WholeDyn d) (hM : D.M = -1) (hs0 : 0 ≤ D.s) {B : ℝ} (P : Sb1Pot D.V B) {T : ℝ} (hT : 0 < T)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X₀ : Ω → Whole.EucConfig d N} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hX : Whole.IsWholeStrongSolution Pm D T X₀ W X) (hF : Whole.IsWholeFilteredSolution Pm ℱ W' W X) :
    ∃ Ys : ℕ → ℝ → Ω → Whole.EucConfig d N,
      (∀ M, IsAdditiveSDESolution Pm (p4r_shiftFil ℱ) W' (fun _ => sb1DriftM D (sb1kM d D.s M) N)
        (p4r_sigma d N D.invβ) (X 0) (fun _ => ⊤) (Ys M)) ∧
      (∀ᵐ ζ ∂Pm, ∀ᶠ M : ℕ in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T → Ys M (t : ℝ) ζ = X t ζ) ∧
      (∀ M (t : ℝ), 0 ≤ t → Pm.map (Ys M t) =
        sb1Flow D (sb1kM d D.s M) N (Pm.map (X 0)) (Pm.map (bfPath (p4r_shiftFil_brownian hF.brownian))) t) := by
  have hW' : IsBrownianFiltration Pm (p4r_shiftFil ℱ) W' := p4r_shiftFil_brownian hF.brownian
  have hY0 : ∀ t : ℝ, Measurable[p4r_shiftFil ℱ t] (X 0) := fun t =>
    (hF.adapted 0).mono (ℱ.mono (le_max_right t 0)) le_rfl
  have hex : ∀ M : ℕ, ∃ Ys : ℝ → Ω → Whole.EucConfig d N,
      IsAdditiveSDESolution Pm (p4r_shiftFil ℱ) W' (fun _ => sb1DriftM D (sb1kM d D.s M) N)
        (p4r_sigma d N D.invβ) (X 0) (fun _ => ⊤) Ys := fun M =>
    exists_sde_solution_global_exists hW' _ (sb1_driftM_isLip D (sb1kM_isKernel D.s hs0 M) P N) _ hY0
  choose Ys hYs using hex
  have hae := sb1_ident D hM P hT hX hF (gM := sb1kM d D.s) (fun M => sb1kM_isKernel D.s hs0 M) hYs
  refine ⟨Ys, hYs, hae, fun M t ht => ?_⟩
  exact sb1_law_repr hW' (sb1_driftM_isLip D (sb1kM_isKernel D.s hs0 M) P N) (hY0 0) (hYs M) ht

theorem sb1_ae_inj (hd : 1 ≤ d) : ∀ᵐ X : Whole.EucConfig d N ∂(volume : Measure (Whole.EucConfig d N)),
    ∀ i j, i ≠ j → X i ≠ X j := by
  have h := p4g_collision_null (d := d) hd N
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with X hX i j hij hEq
  exact hX ⟨i, j, hij, hEq⟩

/-- the unnormalised regularised Gibbs weight -/
def sb1Gw (D : Whole.WholeDyn d) (k : Euc d → ℝ) (N : ℕ) (Z : Whole.EucConfig d N) : ℝ :=
  Real.exp (-D.invβ⁻¹ * sb1Hs D k N Z)

theorem sb1_sing_le (D : Whole.WholeDyn d) (hβ : 0 < D.invβ) (hs0 : 0 ≤ D.s) (hd : 1 ≤ d) (M : ℕ) :
    ∀ᵐ Z : Whole.EucConfig d N ∂(volume : Measure (Whole.EucConfig d N)),
      sb1Gw D (Whole.rieszKernel d D.s) N Z ≤ sb1Gw D (sb1kM d D.s M) N Z := by
  filter_upwards [sb1_ae_inj (N := N) hd] with Z hZ
  unfold sb1Gw
  refine Real.exp_le_exp.2 ?_
  have hβ0 : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  have hle : sb1Hs D (sb1kM d D.s M) N Z ≤ sb1Hs D (Whole.rieszKernel d D.s) N Z := by
    unfold sb1Hs p4k_pairSum
    have : ∑ i, ∑ j ∈ Finset.univ.erase i, sb1kM d D.s M (Z i - Z j) ≤
        ∑ i, ∑ j ∈ Finset.univ.erase i, Whole.rieszKernel d D.s (Z i - Z j) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
        (sb1kM_isKernel D.s hs0 M).le_riesz _ (sub_ne_zero.2 (hZ i j (Finset.ne_of_mem_erase hj).symm))
    have hN0 : (0 : ℝ) ≤ 1 / (2 * (N : ℝ)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hN0]
  nlinarith

/-- **domination by the unnormalised regularised Gibbs measure**, uniformly in `M` -/
theorem sb1_Y_dom (D : Whole.WholeDyn d) (hs0 : 0 ≤ D.s) (hd : 1 ≤ d) {B : ℝ} (P : Sb1Pot D.V B) (hθ : 0 < D.invβ)
    {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) {T : ℝ} (hT : 0 < T)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW : IsBrownianFiltration Pm ℱ W')
    {Y₀ : Ω → Whole.EucConfig d N} (hY0 : Measurable[ℱ 0] Y₀) (M : ℕ) {Ys : ℝ → Ω → Whole.EucConfig d N}
    (hYs : IsAdditiveSDESolution Pm ℱ W' (fun _ => sb1DriftM D (sb1kM d D.s M) N) (p4r_sigma d N D.invβ) Y₀
      (fun _ => ⊤) Ys)
    {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hbdd : Pm.map Y₀ ≤ ENNReal.ofReal c0 • sb1Dm (fun Z => sb1Gw D (Whole.rieszKernel d D.s) N Z))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Pm.map (Ys t) ≤ ENNReal.ofReal c0 • sb1Dm (fun Z => sb1Gw D (sb1kM d D.s M) N Z) := by
  have hk := sb1kM_isKernel (d := d) D.s hs0 M
  have hHc := sb1_Hs_cont D hk P N
  have hlow := hk.lower
  have hz := sb1_gz_pos hθ hHc hlow hcV hV
  have hGM : ∀ Z, sb1Gw D (sb1kM d D.s M) N Z = sb1Gz D (sb1kM d D.s M) N * sb1Gq D (sb1kM d D.s M) N Z := by
    intro Z
    unfold sb1Gw sb1Gq
    field_simp
  have hscale : sb1Dm (fun Z => sb1Gw D (sb1kM d D.s M) N Z) =
      ENNReal.ofReal (sb1Gz D (sb1kM d D.s M) N) • sb1Gam D (sb1kM d D.s M) N := by
    unfold sb1Gam sb1Dm
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext Z
    show ENNReal.ofReal (sb1Gw D (sb1kM d D.s M) N Z) = ENNReal.ofReal (sb1Gz D (sb1kM d D.s M) N) *
      ENNReal.ofReal (sb1Gq D (sb1kM d D.s M) N Z)
    rw [hGM Z, ENNReal.ofReal_mul hz.le]
  have hmono : sb1Dm (fun Z => sb1Gw D (Whole.rieszKernel d D.s) N Z) ≤ sb1Dm (fun Z => sb1Gw D (sb1kM d D.s M) N Z) := by
    unfold sb1Dm
    exact withDensity_mono ((sb1_sing_le D hθ hs0 hd M).mono fun Z hZ => ENNReal.ofReal_le_ofReal hZ)
  have hc : Pm.map Y₀ ≤ (ENNReal.ofReal c0 * ENNReal.ofReal (sb1Gz D (sb1kM d D.s M) N)) • sb1Gam D (sb1kM d D.s M) N := by
    refine hbdd.trans ?_
    rw [mul_smul, ← hscale]
    exact Measure.le_iff'.2 fun A => by
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' le_rfl (hmono A)
  have := sb1_flow_dom D hk P hθ hcV hV hT hW hY0 hYs hc ht
  rw [mul_smul, ← hscale] at this
  exact this

end HRS.MS.MfeConf
