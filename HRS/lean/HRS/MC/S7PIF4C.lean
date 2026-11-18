import HRS.MC.S7PIF4B

/-!
# Packet piF4, part C: the centred `ℬ`-integral has mean zero

`S7PIF4_J_mean_zero`: for smooth `φ`, `0 < τ ≤ T`, `0 ≤ u ≤ τ`, the random variable
`J_u(ω) = ∫_{(0,u]} eval (ℬ_N^r ω) (U^{r,τ} φ) dr` is integrable and has mean zero.  Route: M1 (joint measurability and
`E ∫ ‖ℬ_N‖ < ∞`), `S1` + `pie_Vbound` (domination by `C ‖ℬ_N^r‖`, measurability through `pie_V_aesm`), Fubini, and for each fixed `r`
`E ℬ_N^r = 0` in `E_m` (`ℬ̃_N^r` integrable: part B) against the continuous linear functional `eval · (U^{r,τ} φ)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF4

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

/-- For fixed `r ∈ [0,τ]`, the centred field has mean zero against `U^{r,τ} φ`. -/
theorem S7PIF4_E_fixed {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {τ : ℝ} {r : ℝ} (hr : r ∈ Set.Icc 0 τ) :
    ∫ ω, NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω)
      (propagator R.D R.ρ r τ φ) ∂P = 0 := by
  have hsm := (HRS.MC.L2C0.l2c0_proof R φ hφ r τ hr.1 hr.2).1
  have hws : A33WS m (propagator R.D R.ρ r τ φ) := a33_ws_smooth m hsm
  set ℓ := S7PIF4_evalCLM m hws
  have hint := S7PIF4_tilde_integrable R m hm hN P X₀ W X hreal hr.1
  have e : ∀ ω, NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω)
      (propagator R.D R.ρ r τ φ) =
      ℓ (quadFieldTilde m R.D.s (withDensityReal (R.ρ r)) (X r.toNNReal ω)) -
        ℓ (∫ ω', quadFieldTilde m R.D.s (withDensityReal (R.ρ r)) (X r.toNNReal ω') ∂P) := by
    intro ω
    unfold quadFieldAt
    exact S7PIF4_eval_sub m hws _ _
  simp_rw [e]
  rw [integral_sub (ℓ.integrable_comp hint) (integrable_const _), ℓ.integral_comp_comm hint]
  simp

theorem S7PIF4_J_mean_zero {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {τ : ℝ} (hτ : τ ∈ Set.Ioc 0 T)
    {u : ℝ} (hu : u ∈ Set.Icc 0 τ) :
    Integrable (fun ω => ∫ r in Set.Ioc 0 u,
      NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω)
        (propagator R.D R.ρ r τ φ)) P ∧
    ∫ ω, (∫ r in Set.Ioc 0 u,
      NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω)
        (propagator R.D R.ρ r τ φ)) ∂P = 0 := by
  obtain ⟨hM1a, hM1b, hM1c⟩ := HRS.MC.Sec7.S7PIM.s7_PIM_B_integrable_proof R m hm T hT N hN P X₀ W X hreal
  set B : ℝ × Ω → NegSobolev d m :=
    fun p => quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X p.1 p.2 with hBdef
  have hSsub : Set.Ioc 0 u ⊆ Set.Icc 0 T := fun r hr => ⟨hr.1.le, hr.2.trans (hu.2.trans hτ.2)⟩
  have hSτ : Set.Ioc 0 u ⊆ Set.Icc 0 τ := fun r hr => ⟨hr.1.le, hr.2.trans hu.2⟩
  have hBint : Integrable B ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) := by
    refine (integrable_prod_iff' hM1b).2 ⟨?_, hM1c⟩
    filter_upwards [hM1a] with ω hω
    exact hω.integrable le_rfl
  have hle : (volume.restrict (Set.Ioc (0 : ℝ) u)).prod P ≤ (volume.restrict (Set.Icc (0 : ℝ) T)).prod P :=
    Measure.prod_mono (Measure.restrict_mono hSsub le_rfl) le_rfl
  have hBint' : Integrable B ((volume.restrict (Set.Ioc (0 : ℝ) u)).prod P) := hBint.mono_measure hle
  obtain ⟨C, hC0, hC⟩ := S7PIF4_eval_prop_bound R m hm T hT hφ
  set H : ℝ × Ω → ℝ := fun p => NegSobolev.eval (B p) (propagator R.D R.ρ p.1 τ φ) with hH
  have hae : ∀ᵐ p ∂((volume.restrict (Set.Ioc (0 : ℝ) u)).prod P), p.1 ∈ Set.Icc (0 : ℝ) τ := by
    have h1 : ∀ᵐ r ∂(volume.restrict (Set.Ioc (0 : ℝ) u)), r ∈ Set.Icc (0 : ℝ) τ :=
      (ae_restrict_mem measurableSet_Ioc).mono fun r hr => hSτ hr
    exact (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Ioc (0 : ℝ) u))
      (ν := P)).ae h1
  have hHmeas : AEStronglyMeasurable H ((volume.restrict (Set.Ioc (0 : ℝ) u)).prod P) :=
    S7PIF4_eval_prop_aesm R m hm T hT hφ hτ (rr := Prod.fst) measurable_fst hBint'.aestronglyMeasurable hae
  have hHint : Integrable H ((volume.restrict (Set.Ioc (0 : ℝ) u)).prod P) := by
    refine Integrable.mono' (hBint'.norm.const_mul C) hHmeas ?_
    filter_upwards [hae] with p hp
    rw [Real.norm_eq_abs]
    exact hC τ hτ p.1 hp (B p)
  refine ⟨hHint.integral_prod_right, ?_⟩
  have hswap := integral_integral_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) u)) (ν := P)
    (f := fun r ω => H (r, ω)) hHint
  show ∫ ω, (∫ r in Set.Ioc 0 u, H (r, ω)) ∂P = 0
  rw [← hswap]
  refine setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_
  exact S7PIF4_E_fixed R m hm T hT N hN P X₀ W X hreal hφ (hSτ hr)

end Prob

end HRS.MC.Sec7.S7PIF4

end
