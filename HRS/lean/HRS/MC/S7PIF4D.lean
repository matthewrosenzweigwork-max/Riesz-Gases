import HRS.MC.S7PIF4C
import HRS.MC.S7PIF1Quad
import HRS.MC.L2C3Aux5

/-!
# Packet piF4, part D: the pathwise decomposition of the interaction integral

For `φ` smooth, `0 < τ ≤ T`, `f_r = U^{r,τ} φ`, `G_r(ω) = flucInteraction (f_r) (X_r ω) (ρ_r)` and `B_r = ℬ_N^r` (centred field):
there is a deterministic `K` with, a.s. for all `u ∈ [0,τ]`,
`∫_{(0,u]} G_r dr = -(1/N) (∫_{(0,u]} eval (B_r) (f_r) dr + K(u))`.
`K(u) = ∫_{(0,u]} eval (E ℬ̃_r) (f_r) dr`.  Route: `F2` (`eval ℬ̃_r (f_r) = -N G_r` off collisions), the definition `ℬ = ℬ̃ - E ℬ̃`, and
integrability of `r ↦ eval (B_r) (f_r)` (M1 + part A) and of `G` (hypothesis, from `F1`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF4

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- `r ↦ eval (b r) (U^{r,τ} φ)` is integrable on `(0,u]` for `b ∈ L¹([0,T];E_m)`. -/
theorem S7PIF4_h_integrable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {τ : ℝ} (hτ : τ ∈ Set.Ioc 0 T) {u : ℝ}
    (hu : u ∈ Set.Icc 0 τ) {b : ℝ → NegSobolev d m} (hb : MemLp b 1 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    IntegrableOn (fun r => NegSobolev.eval (b r) (propagator R.D R.ρ r τ φ)) (Set.Ioc 0 u) := by
  obtain ⟨C, hC0, hC⟩ := S7PIF4_eval_prop_bound R m hm T hT hφ
  have hSτ : Set.Ioc 0 u ⊆ Set.Icc 0 τ := fun r hr => ⟨hr.1.le, hr.2.trans hu.2⟩
  have hsub : Set.Ioc 0 u ⊆ Set.Icc 0 T := fun r hr => ⟨hr.1.le, hr.2.trans (hu.2.trans hτ.2)⟩
  have hbI : Integrable (fun r => ‖b r‖) (volume.restrict (Set.Ioc 0 u)) :=
    ((hb.integrable le_rfl).mono_measure (Measure.restrict_mono hsub le_rfl)).norm
  have hbS : AEStronglyMeasurable b (volume.restrict (Set.Ioc 0 u)) :=
    hb.aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hae : ∀ᵐ r ∂(volume.restrict (Set.Ioc (0 : ℝ) u)), r ∈ Set.Icc (0 : ℝ) τ :=
    (ae_restrict_mem measurableSet_Ioc).mono fun r hr => hSτ hr
  have hm' := S7PIF4_eval_prop_aesm R m hm T hT hφ hτ (rr := fun r : ℝ => r) measurable_id hbS hae
  refine Integrable.mono' (hbI.const_mul C) hm' ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_
  rw [Real.norm_eq_abs]
  exact hC τ hτ r (hSτ hr) (b r)

/-- Boundedness and measurability of the empirical pairing. -/
theorem S7PIF4_flucPair_integrable {N : ℕ} (hN : 1 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → Config d N) (hY : Measurable Y) {g : Torus d → ℝ}
    (hg : Continuous g) (ρ : Torus d → ℝ) : Integrable (fun ω => flucPair (Y ω) ρ g) P := by
  have hN0 : 0 < N := hN
  have hbdd : ∀ i : Fin N, Integrable (fun ω' => g (Y ω' i)) P := fun i => by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hg).isBounded.exists_norm_le
    exact Integrable.of_bound (hg.measurable.comp ((measurable_pi_apply i).comp hY)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω' => hC _ ⟨_, Set.mem_univ _, rfl⟩)
  have : (fun ω => flucPair (Y ω) ρ g) =
      fun ω => (N : ℝ)⁻¹ * ∑ i, g (Y ω i) - pair (withDensityReal ρ) g :=
    funext fun ω => by unfold flucPair; rw [pair_empirical hN0]
  rw [this]
  exact ((integrable_finsetSum _ (fun i _ => hbdd i)).const_mul _).sub (integrable_const _)

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

theorem S7PIF4_path_decomp {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {τ : ℝ} (hτ : τ ∈ Set.Ioc 0 T)
    (hG : ∀ᵐ ω ∂P, IntegrableOn
      (fun r => flucInteraction R.D (propagator R.D R.ρ r τ φ) (X r.toNNReal ω) (R.ρ r)) (Set.Icc 0 τ)) :
    ∃ K : ℝ → ℝ, ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc (0 : ℝ) τ,
      ∫ r in Set.Ioc 0 u, flucInteraction R.D (propagator R.D R.ρ r τ φ) (X r.toNNReal ω) (R.ρ r) =
        -(1 / (N : ℝ)) * ((∫ r in Set.Ioc 0 u,
          NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω)
            (propagator R.D R.ρ r τ φ)) + K u) := by
  have hS := hreal.solution T
  have hN0 : 0 < N := hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
  obtain ⟨hM1a, -, -⟩ := HRS.MC.Sec7.S7PIM.s7_PIM_B_integrable_proof R m hm T hT N hN P X₀ W X hreal
  set c : ℝ → ℝ := fun r => NegSobolev.eval
    (∫ ω', quadFieldTilde m R.D.s (withDensityReal (R.ρ r)) (X r.toNNReal ω') ∂P)
    (propagator R.D R.ρ r τ φ) with hc
  refine ⟨fun u => ∫ r in Set.Ioc 0 u, c r, ?_⟩
  -- the pointwise decomposition
  have hpt : ∀ ω, (∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet d N) → ∀ r ∈ Set.Icc (0 : ℝ) τ,
      flucInteraction R.D (propagator R.D R.ρ r τ φ) (X r.toNNReal ω) (R.ρ r) =
        -(1 / (N : ℝ)) * (NegSobolev.eval
          (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω) (propagator R.D R.ρ r τ φ) + c r) := by
    intro ω hcol r hr
    have hsm := (HRS.MC.L2C0.l2c0_proof R φ hφ r τ hr.1 hr.2).1
    have hws : A33WS m (propagator R.D R.ρ r τ φ) := a33_ws_smooth m hsm
    have hinj : Function.Injective (X r.toNNReal ω) := by
      intro i j hij
      by_contra hne
      refine hcol r.toNNReal ?_ ⟨i, j, hne, hij⟩
      rw [Real.coe_toNNReal _ hr.1]; exact hr.2.trans hτ.2
    have hF2 := HRS.MC.Sec7.S7PIF1.s7_PIF_quad_eval_proof R m hm hN (R.ρ r) (S7PIF4_rho_smooth R hr.1)
      _ hsm _ hinj
    have e : NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω)
        (propagator R.D R.ρ r τ φ) =
        NegSobolev.eval (quadFieldTilde m R.D.s (withDensityReal (R.ρ r)) (X r.toNNReal ω))
          (propagator R.D R.ρ r τ φ) - c r := by
      unfold quadFieldAt
      exact S7PIF4_eval_sub m hws _ _
    rw [e, sub_add_cancel, hF2]
    field_simp
  have hgood : ∀ᵐ ω ∂P, (∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet d N) ∧
      IntegrableOn (fun r => flucInteraction R.D (propagator R.D R.ρ r τ φ) (X r.toNNReal ω) (R.ρ r))
        (Set.Icc 0 τ) ∧
      MemLp (fun r => quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω) 1
        (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    filter_upwards [hS.no_collision, hG, hM1a] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨ω0, h0col, h0G, h0M⟩ := hgood.exists
  -- `c` is integrable on `(0, τ]`
  have hcint : IntegrableOn c (Set.Ioc 0 τ) := by
    have hh := S7PIF4_h_integrable R m hm T hT hφ hτ ⟨hτ.1.le, le_rfl⟩ h0M
    have h1 : IntegrableOn (fun r => -(N : ℝ) *
        flucInteraction R.D (propagator R.D R.ρ r τ φ) (X r.toNNReal ω0) (R.ρ r) -
        NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω0)
          (propagator R.D R.ρ r τ φ)) (Set.Ioc 0 τ) :=
      ((h0G.mono_set Set.Ioc_subset_Icc_self).const_mul (-(N : ℝ))).sub hh
    refine h1.congr_fun (fun r hr => ?_) measurableSet_Ioc
    have := hpt ω0 h0col r ⟨hr.1.le, hr.2⟩
    simp only
    rw [this]
    field_simp
    ring
  filter_upwards [hgood] with ω ⟨hcol, hGi, hMem⟩ u hu
  have hh := S7PIF4_h_integrable R m hm T hT hφ hτ hu hMem
  have hcu : IntegrableOn c (Set.Ioc 0 u) := hcint.mono_set (Set.Ioc_subset_Ioc_right hu.2)
  calc _ = ∫ r in Set.Ioc 0 u, -(1 / (N : ℝ)) * (NegSobolev.eval
          (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω) (propagator R.D R.ρ r τ φ) + c r) :=
        setIntegral_congr_fun measurableSet_Ioc fun r hr =>
          hpt ω hcol r ⟨hr.1.le, hr.2.trans hu.2⟩
    _ = _ := by rw [integral_const_mul, integral_add hh hcu]

end Prob

end HRS.MC.Sec7.S7PIF4

end
