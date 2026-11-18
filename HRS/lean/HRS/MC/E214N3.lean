import HRS.MC.E214PD
import HRS.MC.E214H7
import HRS.MD.EQBurnGaussLinMain
import HRS.MD.EQGaussWindow

/-!
# E214N3: the time-shifted stationary Gaussian limit field (`shifted_limit`)

Route: the limit field `η` of a `GaussData` of the stationary datum `Ss` is a `HRS.IsStationaryGaussianField` (the bridge
`E214H.bridge_proof` applied to the stationary regime with the pair `(Y₀, Y₀, η, η)`); the shifted field `η(h+·)` is again
one (the finite-dimensional laws depend on the lags only: `eqgw_lagCov_shift`); a stationary Gaussian field is a linear
fluctuation solution with initial value `Z 0` (`eq_gauss_lin_proof`, this settles the independence of the later noise
increments from `η(h)`, trap T17); the law of `η(h)` is that of `η(0) = Y₀` by `eq_gauss_window_law_proof` at `T = 0`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214N

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

section Shift

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (sd : StatDatum S β₀ m hE)

theorem stat_dyn_eq : sd.Ss.dyn = S.dyn := sd.hD

theorem stat_s_eq : sd.Ss.s = S.s := congrArg DynData.s (stat_dyn_eq sd)

theorem stat_V_eq : sd.Ss.V = S.V := congrArg DynData.V (stat_dyn_eq sd)

theorem stat_β_eq : sd.Ss.β = S.β := by
  have h : sd.Ss.β⁻¹ = S.β⁻¹ := congrArg DynData.invβ (stat_dyn_eq sd)
  exact inv_injective h

/-- The thermal density of the stationary regime is the thermal density of `S`. -/
theorem stat_rhoβ_eq : (regime sd.Ss S.β sd.hEs).ρβ = (regime S β₀ hE).ρβ := by
  obtain ⟨hth, -, -⟩ := (regime sd.Ss S.β sd.hEs).thermal
  have h1 : IsThermalDensity (periodicRiesz d sd.Ss.s) sd.Ss.V sd.Ss.β (regime sd.Ss S.β sd.hEs).ρβ := hth
  rw [stat_s_eq sd, stat_V_eq sd, stat_β_eq sd] at h1
  exact HRS.MC.E214H.thermal_eq S β₀ hE _ h1

theorem stat_rho_fun : sd.Ss.ρ = fun _ => (regime sd.Ss S.β sd.hEs).ρβ := by
  rw [stat_rhoβ_eq sd]; exact sd.hρ

theorem stat_rho0 : sd.Ss.ρ0 = (regime sd.Ss S.β sd.hEs).ρβ := by
  rw [stat_rhoβ_eq sd]; exact sd.hρ₀

/-- The limit field of a `GaussData` of the stationary datum is a stationary Gaussian field. -/
theorem gds_stationary (gds : GaussData sd.Ss S.β sd.hEs) :
    IsStationaryGaussianField gds.P₀ sd.Ss.s sd.Ss.β sd.Ss.hs0 sd.Ss.hsd sd.Ss.hβ sd.Ss.V
      (regime sd.Ss S.β sd.hEs).ρβ (rLvl d) gds.η := by
  obtain ⟨Y₀, hY, hlin⟩ := gds.limit
  have hρ := stat_rho_fun sd
  refine HRS.MC.E214H.bridge_proof sd.Ss S.β sd.hEs gds.P₀ Y₀ Y₀ gds.η gds.η ⟨hY, ?_, hlin, ?_⟩
  · have hb : (regime sd.Ss S.β sd.hEs).β = S.β := stat_β_eq sd
    have h0 := stat_rho0 sd
    show IsCenteredGaussianWithCov (rLvl d) (gds.P₀.map Y₀)
      (susceptibilityCov (periodicRiesz d sd.Ss.dyn.s) (withDensityReal (regime sd.Ss S.β sd.hEs).ρβ)
        (regime sd.Ss S.β sd.hEs).β)
    rw [hb, ← h0]
    exact hY
  · intro T
    have := hlin T
    rw [hρ] at this
    exact this

theorem shifted_stationary (gds : GaussData sd.Ss S.β sd.hEs) (h : ℝ) (hh : 0 ≤ h) :
    IsStationaryGaussianField gds.P₀ sd.Ss.s sd.Ss.β sd.Ss.hs0 sd.Ss.hsd sd.Ss.hβ sd.Ss.V
      (regime sd.Ss S.β sd.hEs).ρβ (rLvl d) (fun u ω => gds.η (h + u) ω) := by
  have hz := gds_stationary sd gds
  refine ⟨fun t => hz.meas _, ?_, ?_⟩
  · filter_upwards [hz.cont] with ω hω
    exact hω.comp (continuousOn_const.add continuousOn_id) (fun t ht => Set.mem_Ici.2 (add_nonneg hh ht))
  · intro p τ φ hτ hφ
    have := hz.gaussian p (fun a => h + τ a) φ (fun a => add_nonneg hh (hτ a)) hφ
    rw [HRS.MD.EQGaussWindow.eqgw_lagCov_shift] at this
    exact this

theorem linSol_mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : DynData d} {ρ : ℝ → Torus d → ℝ}
    {r q T T' : ℝ} {Y₀ : Ω → NegSobolev d r} {Y : ℝ → Ω → NegSobolev d r}
    (h : IsLinearFluctuationSolution P D ρ r q T' Y₀ Y) (hT : T ≤ T') :
    IsLinearFluctuationSolution P D ρ r q T Y₀ Y := by
  refine ⟨h.init, ?_, h.meas, fun p ts φ hts hφ => h.gaussian_part p ts φ
    (fun a => ⟨(hts a).1, (hts a).2.trans hT⟩) hφ⟩
  filter_upwards [h.cont] with ω hω
  exact hω.mono fun t ht => ⟨ht.1, ht.2.trans hT⟩

/-- Evaluation of a path on `[0,0]` at time `0`. -/
def ev0 {r : ℝ} (w : PathSpace d r 0) : NegSobolev d r := w.at' ⟨0, Set.left_mem_Icc.2 le_rfl⟩

theorem continuous_ev0 {r : ℝ} : Continuous (ev0 (d := d) (r := r)) :=
  (continuous_eval_const (⟨0, Set.left_mem_Icc.2 le_rfl⟩ : Set.Icc (0 : ℝ) 0) :
    Continuous fun w : C(Set.Icc (0 : ℝ) 0, NegSobolev d r) => w _)

/-- The law of `η(a)` is the push-forward of the law of the window path at `T = 0`. -/
theorem map_eta_eq_window (gds : GaussData sd.Ss S.β sd.hEs) (a : ℝ) (ha : 0 ≤ a) :
    gds.P₀.map (fun ω => gds.η (a + 0) ω) =
      (gds.P₀.map (Main.windowPath (rLvl d) 0 a gds.η)).map ev0 := by
  have hz := gds_stationary sd gds
  obtain ⟨hm1, -⟩ := HRS.MD.EQGaussWindow.eqgw_fidi sd.Ss.hd sd.Ss.hs0 sd.Ss.hsd sd.Ss.V sd.Ss.hβ
    (regime sd.Ss S.β sd.hEs).ρβ (rLvl d) 0 gds.P₀ gds.η hz a ha
  rw [AEMeasurable.map_map_of_aemeasurable continuous_ev0.measurable.aemeasurable hm1]
  refine Measure.map_congr ?_
  filter_upwards [hz.cont] with ω hω
  have := HRS.MD.EQGaussWindow.eqgw_windowPath_at (M := rLvl d) 0 a ha gds.η ω hω
    ⟨0, Set.left_mem_Icc.2 le_rfl⟩
  simpa [Function.comp, ev0] using this.symm

/-- The law of `η(h)` is that of `η(0) = Y₀`. -/
theorem eta_law_shift (gds : GaussData sd.Ss S.β sd.hEs) (Y₀ : gds.Ω₀ → NegSobolev d (rLvl d))
    (hinit : ∀ᵐ ω ∂gds.P₀, gds.η 0 ω = Y₀ ω) (h : ℝ) (hh : 0 ≤ h) :
    gds.P₀.map (fun ω => gds.η (h + 0) ω) = gds.P₀.map Y₀ := by
  have hz := gds_stationary sd gds
  have hw := HRS.MD.EQGaussWindow.eq_gauss_window_law_proof sd.Ss.hd sd.Ss.hs0 sd.Ss.hsd sd.Ss.V
    sd.Ss.hβ (regime sd.Ss S.β sd.hEs).ρβ (rLvl d) 0 le_rfl gds.P₀ gds.P₀ gds.η gds.η hz hz h 0 hh le_rfl
  rw [map_eta_eq_window sd gds h hh]
  have h0 := map_eta_eq_window sd gds 0 le_rfl
  have h00 : gds.P₀.map (fun ω => gds.η (0 + 0) ω) = gds.P₀.map Y₀ := by
    refine Measure.map_congr ?_
    filter_upwards [hinit] with ω hω
    simpa using hω
  rw [h00] at h0
  rw [h0]
  exact congrArg (fun μ => μ.map ev0) hw

theorem shifted_limit_proof (gds : GaussData sd.Ss S.β sd.hEs) (h : ℝ) (hh : 0 ≤ h) :
    IsGaussianLimitField sd.Ss.dyn sd.Ss.ρ (withDensityReal sd.Ss.ρ0) S.β (rLvl d) gds.P₀
      (fun u ω => gds.η (h + u) ω) := by
  obtain ⟨Y₀, hY, hlin⟩ := gds.limit
  have hz' := shifted_stationary sd gds h hh
  have hlaw := eta_law_shift sd gds Y₀ (hlin 0).init h hh
  refine ⟨fun ω => gds.η (h + 0) ω, ?_, fun T => ?_⟩
  · rw [hlaw]; exact hY
  · have hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < rLvl d := by
      unfold rLvl
      refine max_lt ?_ ?_ <;> (have : (0 : ℝ) ≤ d := Nat.cast_nonneg d) <;> linarith
    obtain ⟨hρth, -, -⟩ := (regime sd.Ss S.β sd.hEs).thermal
    have key := HRS.MD.EQBurnGaussLin.eq_gauss_lin_proof sd.Ss.hd sd.Ss.hs0 sd.Ss.hsd sd.Ss.V sd.Ss.hV
      sd.Ss.hβ (regime sd.Ss S.β sd.hEs).ρβ hρth (rLvl d) hm (max T 0) (le_max_right _ _) gds.P₀ _ hz'
    have key' := linSol_mono key (le_max_left T 0)
    rw [stat_rho_fun sd]
    exact key'

end Shift

end HRS.MC.E214N

end
