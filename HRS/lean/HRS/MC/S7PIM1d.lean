import HRS.MC.S7PIM1c

/-!
# Packet piM, part M1d: joint strong measurability of `(u, ω) ↦ ℬ_N^u(ω)` (prefix `S7PIM_`)

The particle path is a.s. continuous, so by the Carathéodory device `s7fcw12_caratheodory` it has a jointly measurable
version `V` which agrees with it on `[0,T]` off a null set; the centred field is then jointly measurable.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIM

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.S7FCW12

variable {d : ℕ}

/-- The jointly measurable kernel `Ψ(t, x) = ℬ̃(x; μ_t)` (with the density `ρ` set to `0` at negative times). -/
def S7PIM_Psi (R : Regime d) (m : ℝ) {N : ℕ} (t : ℝ) (x : Config d N) : NegSobolev d m :=
  quadFieldTilde m R.D.s (withDensityReal fun y => s7fcw12_rhoPos R (t, y)) x

theorem S7PIM_Psi_meas (R : Regime d) (m : ℝ) {N : ℕ} :
    Measurable fun q : ℝ × Config d N => S7PIM_Psi R m (N := N) q.1 q.2 :=
  s7fcw12_quadTilde_measurable R m

theorem S7PIM_B_eq (R : Regime d) (m : ℝ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω =
      S7PIM_Psi R m t (X t.toNNReal ω) - ∫ ω', S7PIM_Psi R m t (X t.toNNReal ω') ∂P := by
  have hμ : withDensityReal (R.ρ t) = withDensityReal fun y => s7fcw12_rhoPos R (t, y) := by
    congr 1
    funext y
    rw [s7fcw12_rhoPos_eq R ht y]
  simp only [quadFieldAt, S7PIM_Psi, hμ]

theorem S7PIM_B_jointly (R : Regime d) (m : ℝ) {T : ℝ} (hT : 0 < T) {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N)
    (hadapt : ∀ t : ℝ≥0, Measurable (X t)) (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    AEStronglyMeasurable
      (fun p : ℝ × Ω => quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) := by
  have hc : ∀ᵐ ω ∂P, ContinuousOn (fun t : ℝ => X t.toNNReal ω) (Set.Icc 0 T) :=
    hcont.mono fun ω hω =>
      (continuous_pi fun i => (hω i).comp continuous_real_toNNReal).continuousOn
  obtain ⟨V, hVm, N0, hN0m, hN0, hVN⟩ :=
    s7fcw12_caratheodory P hT.le (fun t ω => X t.toNNReal ω) (fun t => hadapt _) hc (fun _ => 0)
  have hGm : Measurable fun q : ℝ × Ω => S7PIM_Psi R m q.1 (V q.1 q.2) := by
    have h1 : Measurable fun q : ℝ × Ω => ((q.1, V q.1 q.2) : ℝ × Config d N) :=
      measurable_fst.prodMk hVm
    have h2 := Measurable.comp (g := fun q : ℝ × Config d N => S7PIM_Psi R m q.1 q.2)
      (f := fun q : ℝ × Ω => ((q.1, V q.1 q.2) : ℝ × Config d N)) (S7PIM_Psi_meas R m) h1
    exact h2
  have hM : Measurable fun t : ℝ => ∫ ω', S7PIM_Psi R m t (V t ω') ∂P :=
    (hGm.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have hFp : Measurable fun q : ℝ × Ω =>
      S7PIM_Psi R m q.1 (V q.1 q.2) - ∫ ω', S7PIM_Psi R m q.1 (V q.1 ω') ∂P :=
    hGm.sub (hM.comp measurable_fst)
  have hkey : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, ω ∉ N0 →
      quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω =
        S7PIM_Psi R m t (V t ω) - ∫ ω', S7PIM_Psi R m t (V t ω') ∂P := by
    intro t ht ω hω
    have hV1 : X t.toNNReal ω = V t ω := (hVN ω hω t ht).symm
    have hV2 : ∀ᵐ ω' ∂P, S7PIM_Psi R m t (X t.toNNReal ω') = S7PIM_Psi R m t (V t ω') := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω' hω'
      rw [(hVN ω' hω' t ht).symm]
    rw [S7PIM_B_eq R m P X ht.1 ω, hV1, integral_congr_ae hV2]
  have hae : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P),
      quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X p.1 p.2 =
        S7PIM_Psi R m p.1 (V p.1 p.2) - ∫ ω', S7PIM_Psi R m p.1 (V p.1 ω') ∂P := by
    have h1 : ∀ᵐ u ∂(volume.restrict (Set.Icc (0 : ℝ) T)), u ∈ Set.Icc (0 : ℝ) T :=
      ae_restrict_mem measurableSet_Icc
    have h2 : ∀ᵐ ω ∂P, ω ∉ N0 := measure_eq_zero_iff_ae_notMem.1 hN0
    have h1' := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Icc (0 : ℝ) T))
      (ν := P)).ae h1
    have h2' := (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Set.Icc (0 : ℝ) T))
      (ν := P)).ae h2
    filter_upwards [h1', h2'] with p hp1 hp2
    exact hkey p.1 hp1 p.2 hp2
  exact hFp.aestronglyMeasurable.congr (hae.mono fun p hp => hp.symm)

end HRS.MC.Sec7.S7PIM

end
