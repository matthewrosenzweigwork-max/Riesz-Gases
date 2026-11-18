import HRS.MC.S7FCH3D
import HRS.MC.S7FCGSmall
import HRS.MC.QRPChaosLim
import HRS.MC.QRPHd

/-!
# S7FCH3E: coordinate moments and convergence of the kernel error (H3, part E)

* `S7FCH3_moment_gen`: from the abstract chaos bound (`qrs_chaos_lp_lim` with `F = ∅`) to a `lintegral` moment bound
  of a half-Wick variable in terms of a bound `Tb` for the Hilbert-Schmidt mass;
* `S7FCH3_eps_tendsto`: `∬ (h_{∇e_k} - K_L)² dx dy → 0` from the `L^{2+ε}(μ⁰ × μ⁰)` convergence of `FCKernelData`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH3

open HRS HRS.Sec7 HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCW9

variable {d : ℕ}

theorem S7FCH3_wickSection_empty {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {r : ℝ} (η : Ω → NegSobolev d r)
    (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ) (ω : Ω) : wickSection P η μ h ∅ ω = 0 := by
  simp [wickSection]

theorem S7FCH3_moment_gen {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {r : ℝ} (η0 : Ω' → NegSobolev d r) (K0 : ℝ) (hK0 : 0 ≤ K0) (p Cp : ℝ) (hp : 2 ≤ p) (hCp : 0 ≤ Cp)
    (hchaos : ∀ (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ) (Q : Ω' → ℝ),
      IsHalfWick P' η0 μ h Q → AEStronglyMeasurable Q P' →
      (Summable fun q : NonzeroLattice d × NonzeroLattice d => wickCoeff μ h q.1 q.2 ^ 2) →
      eLpNorm (fun ω => Q ω - wickSection P' η0 μ h ∅ ω) (ENNReal.ofReal p) P' ≤
        ENNReal.ofReal (Cp * K0 * Real.sqrt (tailHS (wickCoeff μ h) ∅)))
    {μ : Measure (Torus d)} {h : Torus d → Torus d → ℝ} {Q : Ω' → ℝ} (hQ : IsHalfWick P' η0 μ h Q)
    (hQm : AEStronglyMeasurable Q P')
    (hsum : Summable fun q : NonzeroLattice d × NonzeroLattice d => wickCoeff μ h q.1 q.2 ^ 2) {Tb : ℝ}
    (hTb : tailHS (wickCoeff μ h) ∅ ≤ Tb) :
    ∫⁻ ω, ENNReal.ofReal (|Q ω| ^ p) ∂P' ≤ ENNReal.ofReal ((Cp * K0) ^ p * Tb ^ (p / 2)) := by
  have h0 := S7FCW9_tailHS_nonneg (wickCoeff μ h) ∅
  have hch := hchaos μ h Q hQ hQm hsum
  simp only [S7FCH3_wickSection_empty, sub_zero] at hch
  have h1 := S7FCW9_lint_of_chaos P' Q p Cp K0 (tailHS (wickCoeff μ h) ∅) hp hK0 hCp h0 hch
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 hTb (by linarith)) ?_
  exact Real.rpow_nonneg (mul_nonneg hCp hK0) _

theorem S7FCH3_vol_le {ρ₀ : Torus d → ℝ} {m₀ : ℝ} (hm₀ : 0 < m₀) (h0 : ∀ x, m₀ ≤ ρ₀ x) :
    (volume : Measure (Torus d)) ≤ ENNReal.ofReal (1 / m₀) • withDensityReal ρ₀ := by
  refine Measure.le_iff.2 fun s hs => ?_
  unfold withDensityReal
  rw [Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc (volume : Measure (Torus d)) s = ∫⁻ _ in s, 1 ∂volume := by simp
    _ ≤ _ := lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  have : (1 : ℝ) ≤ 1 / m₀ * ρ₀ x := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hm₀]; linarith [h0 x]
  calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal this

theorem S7FCH3_eps_tendsto (R : Regime d) {ε₂ c : ℝ} {K : NonzeroLattice d → ℕ → FRKernel d}
    (hK : FCKernelData R ε₂ c K) (k : NonzeroLattice d) :
    Tendsto (fun L : ℕ => ∫ z : Torus d × Torus d,
      (hTransport d R.D.s (Torus.realMode k) z.1 z.2 - (K k L).toFun z.1 z.2) ^ 2
        ∂((volume : Measure (Torus d)).prod volume)) atTop (𝓝 0) := by
  obtain ⟨-, hε, -, -, hconv⟩ := hK
  obtain ⟨m₀, M₀, hm₀, hbd⟩ := R.bounds
  have hdens : IsProbDensity (R.ρ 0) := (R.mf 1 one_pos).density 0 ⟨le_rfl, zero_le_one⟩
  haveI : IsProbabilityMeasure (withDensityReal (R.ρ 0)) := isProb_withDensityReal hdens
  have hsd : R.D.s < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast R.hd
    linarith [R.hs]
  have hsm := HRS.FieldSingAux.isSmooth_realMode k
  have hmeas : ∀ L : ℕ, Measurable (Function.uncurry fun x y =>
      (K k L).toFun x y - hTransport d R.D.s (Torus.realMode k) x y) := fun L =>
    (S7FCH3_FR_cont (K k L)).measurable.sub (HRS.MC.WCI.wci_hT_measurable hsd hsm)
  have h1 := HRS.MC.Sec7.FCG.fcg_small (μ0 := withDensityReal (R.ρ 0)) (μt := volume)
    (κ := 1 / m₀) (S7FCH3_vol_le hm₀ (fun x => (hbd 0 le_rfl x).1)) hmeas hε (hconv k)
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  rw [ENNReal.toReal_zero] at h2
  refine h2.congr fun L => ?_
  simp only [Function.comp]
  have hm2 : Measurable (fun z : Torus d × Torus d =>
      (hTransport d R.D.s (Torus.realMode k) z.1 z.2 - (K k L).toFun z.1 z.2) ^ 2) :=
    ((HRS.MC.WCI.wci_hT_measurable hsd hsm).sub (S7FCH3_FR_cont (K k L)).measurable).pow_const 2
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _) hm2.aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun z => ?_
  congr 1
  ring

end HRS.MC.Sec7.S7FCH3

end
