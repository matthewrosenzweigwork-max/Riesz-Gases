import HRS.MC.S7FCW12D
import HRS.Equilibrium.Parametrix.PXFIDAuxB

/-!
# FC-E packet, part E: generic centred-field measurability (prefix `s7fcw12_`)

* `s7fcw12_centred_aemeasurable`: `ω ↦ toL2 (F t ω)` is `AEMeasurable` when `F t ω = Ψ t (Y t ω) − E[Ψ t (Y t ·)]`
  (vector-valued centring), with `Ψ` jointly measurable and `Y` a.s. continuous.
* `s7fcw12_coord_aemeasurable`: the same with coordinatewise centring `ofSeq (k ↦ Ψ k t (Y t ω) − E[..])`.
* `s7fcw12_quadTilde_measurable`: the particle quadratic field `(t, X) ↦ quadFieldTilde (μ_t) X` is jointly measurable.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

namespace HRS.MC.Sec7.S7FCW12

variable {d : ℕ}

/-- Vector-valued centring: `ω ↦ toL2 (t ↦ Ψ t (Y t ω) − E Ψ t (Y t ·))` is `AEMeasurable`. -/
theorem s7fcw12_centred_aemeasurable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {r T : ℝ} (hT : 0 < T) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ → Ω → E) (hY : ∀ t, Measurable (Y t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) (e0 : E)
    (Ψ : ℝ → E → NegSobolev d r) (hΨ : Measurable fun q : ℝ × E => Ψ q.1 q.2)
    (F : ℝ → Ω → NegSobolev d r)
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, F t ω = Ψ t (Y t ω) - ∫ ω', Ψ t (Y t ω') ∂P) :
    AEMeasurable (fun ω => HRS.Sec7.toL2 r T (fun t => F t ω)) P := by
  obtain ⟨V, hVm, N0, -, hN0, hVN⟩ := s7fcw12_caratheodory P hT.le Y hY hc e0
  set G : ℝ × Ω → NegSobolev d r := fun q => Ψ q.1 (V q.1 q.2) with hG_def
  have hGm : Measurable G := hΨ.comp (measurable_fst.prodMk hVm)
  set M : ℝ → NegSobolev d r := fun t => ∫ ω', G (t, ω') ∂P with hM_def
  have hM : Measurable M := (hGm.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  set Fp : ℝ → Ω → NegSobolev d r := fun t ω => G (t, ω) - M t with hFp_def
  have hFp : Measurable (Function.uncurry Fp) := hGm.sub (hM.comp measurable_fst)
  have hkey : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, ω ∉ N0 → F t ω = Fp t ω := by
    intro t ht ω hω
    have hV1 : Y t ω = V t ω := (hVN ω hω t ht).symm
    have hV2 : ∀ᵐ ω' ∂P, Ψ t (Y t ω') = Ψ t (V t ω') := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω' hω'
      rw [(hVN ω' hω' t ht).symm]
    rw [hF t ht ω, hV1, integral_congr_ae hV2]
  have hmeas : Measurable fun ω => HRS.Sec7.toL2 r T (fun t => Fp t ω) :=
    s7fcw12_toL2_measurable T Fp hFp
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  exact (s7fcw12_toL2_congr r T _ _ fun t ht => hkey t ht ω hω).symm

/-- Coordinatewise centring: `ω ↦ toL2 (t ↦ ofSeq (k ↦ Ψ k t (Y t ω) − E[Ψ k t (Y t ·)]))` is `AEMeasurable`. -/
theorem s7fcw12_coord_aemeasurable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {r T : ℝ} (hT : 0 < T) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ → Ω → E) (hY : ∀ t, Measurable (Y t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) (e0 : E)
    (Ψ : NonzeroLattice d → ℝ → E → ℝ) (hΨ : ∀ k, Measurable fun q : ℝ × E => Ψ k q.1 q.2)
    (F : ℝ → Ω → NegSobolev d r)
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω,
      F t ω = NegSobolev.ofSeq r (fun k => Ψ k t (Y t ω) - ∫ ω', Ψ k t (Y t ω') ∂P)) :
    AEMeasurable (fun ω => HRS.Sec7.toL2 r T (fun t => F t ω)) P := by
  obtain ⟨V, hVm, N0, -, hN0, hVN⟩ := s7fcw12_caratheodory P hT.le Y hY hc e0
  set G : NonzeroLattice d → ℝ × Ω → ℝ := fun k q => Ψ k q.1 (V q.1 q.2) with hG_def
  have hGm : ∀ k, Measurable (G k) := fun k => (hΨ k).comp (measurable_fst.prodMk hVm)
  set M : NonzeroLattice d → ℝ → ℝ := fun k t => ∫ ω', G k (t, ω') ∂P with hM_def
  have hM : ∀ k, Measurable (M k) := fun k =>
    ((hGm k).stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  set Fp : ℝ → Ω → NegSobolev d r := fun t ω => NegSobolev.ofSeq r (fun k => G k (t, ω) - M k t) with hFp_def
  have hFp : Measurable (Function.uncurry Fp) :=
    s7fcw12_measurable_ofSeq (fun (q : ℝ × Ω) (k : NonzeroLattice d) => G k q - M k q.1)
      (fun k => (hGm k).sub ((hM k).comp measurable_fst))
  have hkey : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, ω ∉ N0 → F t ω = Fp t ω := by
    intro t ht ω hω
    rw [hF t ht ω]
    congr 1
    funext k
    have hV1 : Y t ω = V t ω := (hVN ω hω t ht).symm
    have hV2 : ∀ᵐ ω' ∂P, Ψ k t (Y t ω') = Ψ k t (V t ω') := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω' hω'
      rw [(hVN ω' hω' t ht).symm]
    rw [hV1, integral_congr_ae hV2]
  have hmeas : Measurable fun ω => HRS.Sec7.toL2 r T (fun t => Fp t ω) :=
    s7fcw12_toL2_measurable T Fp hFp
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  exact (s7fcw12_toL2_congr r T _ _ fun t ht => hkey t ht ω hω).symm

/-- The transport kernel `h_f(x,y) = ⟪∇f(x) − ∇f(y), ∇G(x − y)⟫` is jointly measurable. -/
theorem s7fcw12_meas_hTransport (s : ℝ) (hsd : s < (d : ℝ)) (f : Torus d → ℝ) :
    Measurable fun q : Torus d × Torus d => hTransport d s f q.1 q.2 := by
  unfold hTransport
  have h1 : Measurable fun q : Torus d × Torus d => Torus.grad f q.1 - Torus.grad f q.2 :=
    ((HRS.Parx.PXFID.measurable_grad f).comp measurable_fst).sub
      ((HRS.Parx.PXFID.measurable_grad f).comp measurable_snd)
  have h2 : Measurable fun q : Torus d × Torus d => periodicRieszGrad d s (q.1 - q.2) :=
    (HRS.KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd)
  exact h1.inner h2

/-- The particle quadratic field is jointly measurable in the time parameter and the configuration. -/
theorem s7fcw12_quadTilde_measurable (R : Regime d) (r : ℝ) {N : ℕ} :
    Measurable fun q : ℝ × Config d N =>
      quadFieldTilde r R.D.s (withDensityReal fun y => s7fcw12_rhoPos R (q.1, y)) q.2 := by
  have hsd : R.D.s < (d : ℝ) := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith [R.hs]
  have hρ : Measurable fun p : ℝ × Torus d => s7fcw12_rhoPos R (p.1, p.2) :=
    (s7fcw12_rhoPos_measurable R).comp measurable_id
  have hmodE : ∀ k : NonzeroLattice d, Measurable fun p : ℝ × Config d N =>
      modulatedEnergy (hTransport d R.D.s (Torus.realMode k)) p.2
        (withDensityReal fun y => s7fcw12_rhoPos R (p.1, y)) :=
    fun k => s7fcw12_meas_modEnergy _ (s7fcw12_meas_hTransport R.D.s hsd _)
      (fun t y => s7fcw12_rhoPos R (t, y)) hρ
  unfold quadFieldTilde
  exact s7fcw12_measurable_ofSeq
    (fun (q : ℝ × Config d N) (k : NonzeroLattice d) => (N : ℝ) *
      modulatedEnergy (hTransport d R.D.s (Torus.realMode k)) q.2
        (withDensityReal fun y => s7fcw12_rhoPos R (q.1, y)))
    (fun k => measurable_const.mul (hmodE k))

end HRS.MC.Sec7.S7FCW12
