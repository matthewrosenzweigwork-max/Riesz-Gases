import HRS.MC.S7FCW12C

/-!
# FC-E packet, part D: finite-rank particle pair is `AEMeasurable` (E3, prefix `s7fcw12_`)

* `s7fcw12_toL2_fcPart_aemeasurable`: `ω ↦ toL2 r T (fun t => fcPartAt .. (a+t) ω)` is `AEMeasurable` (`0 ≤ a`).
* `s7_FC_E3_finite_rank_measurable_proof`: the E3 pair, statement copied from `HRS/MC/S7FCPlan.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

namespace HRS.MC.Sec7.S7FCW12

variable {d : ℕ}

/-- The finite-rank particle pair `ω ↦ toL2 (fcPartAt ..(a+·) ω)` is `AEMeasurable`. -/
theorem s7fcw12_toL2_fcPart_aemeasurable (R : Regime d) (r T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t))
    (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    AEMeasurable (fun ω => toL2 r T (fun t => fcPartAt r S K (fun t => withDensityReal (R.ρ t)) P X (a + t) ω)) P := by
  have hc0 : ∀ᵐ ω ∂P, ContinuousOn (fun t => X (a + t).toNNReal ω) (Set.Icc 0 T) :=
    hcont.mono fun ω hω => (continuous_pi fun i =>
      (hω i).comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))).continuousOn
  obtain ⟨V, hVm, N0, -, hN0, hVN⟩ := s7fcw12_caratheodory P hT.le
    (fun t ω => X (a + t).toNNReal ω) (fun t => hadapt _) hc0 0
  set G : ℝ × Ω → NegSobolev d r := fun q =>
    fcPartTilde r S K (withDensityReal fun y => s7fcw12_rhoPos R (a + q.1, y)) (V q.1 q.2) with hG_def
  have hGm : Measurable G :=
    s7fcw12_fcPartTilde_measurable R r S K (fun q : ℝ × Ω => a + q.1) (by fun_prop)
      (fun q => V q.1 q.2) hVm
  have hGs : StronglyMeasurable G := hGm.stronglyMeasurable
  set M : ℝ → NegSobolev d r := fun t => ∫ ω', G (t, ω') ∂P with hM_def
  have hM : Measurable M := (hGs.integral_prod_right' (ν := P)).measurable
  set Fp : ℝ → Ω → NegSobolev d r := fun t ω => G (t, ω) - M t with hFp_def
  have hFp : Measurable (Function.uncurry Fp) := hGm.sub (hM.comp measurable_fst)
  have hkey : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, ω ∉ N0 →
      fcPartAt r S K (fun t => withDensityReal (R.ρ t)) P X (a + t) ω = Fp t ω := by
    intro t ht ω hω
    have hat : 0 ≤ a + t := add_nonneg ha ht.1
    have hμ : withDensityReal (R.ρ (a + t)) = withDensityReal fun y => s7fcw12_rhoPos R (a + t, y) := by
      congr 1
      funext y
      rw [s7fcw12_rhoPos_eq R hat y]
    have hV1 : X (a + t).toNNReal ω = V t ω := (hVN ω hω t ht).symm
    have hV2 : ∀ᵐ ω' ∂P, X (a + t).toNNReal ω' = V t ω' := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω' hω'
      exact (hVN ω' hω' t ht).symm
    show fcPartTilde r S K (withDensityReal (R.ρ (a + t))) (X (a + t).toNNReal ω) -
      ∫ ω', fcPartTilde r S K (withDensityReal (R.ρ (a + t))) (X (a + t).toNNReal ω') ∂P = Fp t ω
    rw [hμ, hV1, integral_congr_ae (hV2.mono fun ω' h' => congrArg _ h')]
  have hmeas : Measurable fun ω => toL2 r T (fun t => Fp t ω) := s7fcw12_toL2_measurable T Fp hFp
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  exact (s7fcw12_toL2_congr r T _ _ fun t ht => hkey t ht ω hω).symm

theorem s7_FC_E3_finite_rank_measurable_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ} (hN : 1 ≤ N)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization R.D P
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)
    (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) :
    AEMeasurable (fun ω => (zetaWin r T 0 P X ω,
      toL2 r T (fun t => fcPartAt r S K (fun t => withDensityReal (R.ρ t)) P X (0 + t) ω))) P := by
  have hS := hreal.solution T
  have hm : (d : ℝ) < 2 * r := by
    rw [hr]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hN0 : 0 < N := by omega
  refine AEMeasurable.prodMk (s7fcw12_aemeasurable_zetaWin r T hT hm P X hS.adapted hS.cont hN0) ?_
  exact s7fcw12_toL2_fcPart_aemeasurable R r T hT 0 le_rfl S K P X hS.adapted hS.cont

end HRS.MC.Sec7.S7FCW12
