import HRS.MC.S7PIF6Cyl
import HRS.MC.S7PIRJ
import HRS.MC.S7PIF10D

/-!
# Packet piF10 (F10): `s7_PIF_cyl_concl_proof` (namespace `HRS.MC.Sec7.S7PIF10`)

The conclusion of `path_Ito` for the cylindrical functional `G ∘ obsVec` (`Pj = id`).  The statement is copied verbatim from
`HRS/MC/S7PIPlan.lean` (`HRS.MC.Sec7.PIPlan.s7_PIF_cyl_concl`); the tie is in `HRS/MC/S7PIF10Tie.lean`.

Route.  `A(ω) = ∫_{(0,T]} cylA_r(ω) dr` and `J(ω) = ∫_{(0,T]} cylJ_r(ω) dr`.
* The two `IsRS` clauses are `s7_PIF_RS_drift_proof` (with `w = ζ_N(ω)`, `b = ℬ_N(ω)`, `M1`) and `s7_PIF_RS_J_proof` (with `z = η_N(ω)`; the tensors
  come from PI-D with the bounded representative of `M2`, and the pairings are integrable by the bracket identity and `F5`).
* `A` is integrable (parts C, D).  The cylindrical Itô identity `F7` can be split pathwise (both densities are integrable on `(0,T]`),
  giving `J = 2√N (L + N^{-1/2} A - Mart)` a.s. with `L` bounded and measurable, hence `J` is integrable; integrating the identity
  over `Ω` (`E Mart = 0`) is the last clause.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF10

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3 HRS.MC.Sec7.S7PIF5

variable {d : ℕ}

/-- a `C_b` function is bounded -/
theorem S7PIF10_G_bound {q : ℕ} {G : EuclideanSpace ℝ (Fin q) → ℝ} {k : ℕ} (hG : MemCb k G)
    (x : EuclideanSpace ℝ (Fin q)) : |G x| ≤ ⨆ z, ‖iteratedFDeriv ℝ 0 G z‖ := by
  have := S7PIS3_cb_bound (j := 0) hG (Nat.zero_le _) x
  simpa using this

/-- the heat function is bounded by the sup norm of `G` -/
theorem S7PIF10_gaussHeat_bound {q : ℕ} (S : ℝ → Matrix (Fin q) (Fin q) ℝ)
    {G : EuclideanSpace ℝ (Fin q) → ℝ} {k : ℕ} (hG : MemCb k G) (u : ℝ) (c : EuclideanSpace ℝ (Fin q)) :
    |gaussHeat S G u c| ≤ ⨆ z, ‖iteratedFDeriv ℝ 0 G z‖ := by
  unfold gaussHeat
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ⨆ z, ‖iteratedFDeriv ℝ 0 G z‖) ?_).trans (by simp)
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs]
  exact S7PIF10_G_bound hG _

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

/-- **F10 (the conclusion of `path_Ito` for a cylindrical functional `G ∘ obsVec`)**
(statement of `HRS.MC.Sec7.PIPlan.s7_PIF_cyl_concl`, copied verbatim). -/
theorem s7_PIF_cyl_concl_proof (γ : ℝ → Measure (PathSpace d m T))
    (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i))
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 4 G) :
    PathItoConcl R m T γ N P X (fun w => G (obsVec m T t φ w)) (ContinuousLinearMap.id ℝ (PathSpace d m T)) := by
  classical
  obtain ⟨ℱ, W', hF⟩ := hreal.filtered
  have hG2 : MemCb 2 G := S7PIF10_memCb_mono hG (by norm_num)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  obtain ⟨Mart, hMi, hM0, hF7⟩ := HRS.MC.Sec7.S7PIF6.s7_PIF_ito_cyl_proof R m hm T hT N hN P X₀ W X hreal hF
    t φ ht hφ G hG
  have hM1 := HRS.MC.Sec7.S7PIM.s7_PIM_B_integrable_proof R m hm T hT N hN P X₀ W X hreal
  have hM3 := (HRS.MC.Sec7.S7PIM.s7_PIM_zeta_path_proof R m hm T hT N hN P X₀ W X hreal).2
  have hzi := S7PIF10_eta_pair_int R m hm T hT N hN P X₀ W X hreal hF t φ ht hφ
  have hJt := S7PIF10_hJ R m hm T hT N hN P X₀ W X hreal
  have hAint := S7PIF10_A_int R m hm T hT N hN P X₀ W X hreal hF γ hγ t φ ht hφ G hG
  obtain ⟨O, hO⟩ := HRS.MC.Sec7.S7PIS2.s7_PIS_obs_clm_proof m T t φ ht hφ
  have hHO := HRS.MC.Sec7.S7PIB.s7_PIF_heat_obs_proof R m T hT γ hγ t φ ht hφ G hG2
  -- the two integrated densities
  set A : Ω → ℝ := fun ω => ∫ r in Set.Ioc 0 T, cylA R m T P X t φ G ω r with hA
  set J : Ω → ℝ := fun ω => ∫ r in Set.Ioc 0 T, cylJ R m T P X t φ G ω r with hJ
  -- the left-hand side of the cylindrical Itô identity
  set L : Ω → ℝ := fun ω =>
    G (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) T)) -
      gaussHeat (obsCov R.D R.ρ t φ) G 0 (obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω))) with hL
  -- measurability and boundedness of `L`
  have hz0 : Measurable (fun ω => obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω))) :=
    (S7PIF5_init_meas R m hm T hT N hN P X₀ W X hreal hF t φ ht hφ 0).mono (ℱ.le 0) le_rfl
  have hLm1 : AEMeasurable (fun ω => G (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) T))) P := by
    have : (fun ω => G (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) T))) =
        fun ω => G (O (zetaWin m T 0 P X ω)) := by
      funext ω
      rw [S7PIF10_obs_predicted_T R m hm T hT t φ ht, hO]
    rw [this]
    exact hG.1.continuous.measurable.comp_aemeasurable (O.continuous.measurable.comp_aemeasurable hM3)
  have hLm2 : Measurable (fun ω => gaussHeat (obsCov R.D R.ρ t φ) G 0
      (obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω)))) :=
    (S7PIF10_gaussHeat_cont (obsCov R.D R.ρ t φ) hG 0).measurable.comp hz0
  have hLi1 : Integrable (fun ω => G (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) T))) P :=
    Integrable.mono' (integrable_const (⨆ z, ‖iteratedFDeriv ℝ 0 G z‖)) hLm1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact S7PIF10_G_bound hG _)
  have hLi2 : Integrable (fun ω => gaussHeat (obsCov R.D R.ρ t φ) G 0
      (obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω)))) P :=
    Integrable.mono' (integrable_const (⨆ z, ‖iteratedFDeriv ℝ 0 G z‖)) hLm2.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact S7PIF10_gaussHeat_bound _ hG _ _)
  have hLi : Integrable L P := hLi1.sub hLi2
  -- the pathwise split of the Itô identity
  have hsplit : ∀ᵐ ω ∂P, L ω = -(Real.sqrt N)⁻¹ * A ω + (1 / (2 * Real.sqrt N)) * J ω + Mart ω := by
    filter_upwards [hM1.1, hzi, hF7] with ω h1 h2 h3
    have hIA := S7PIF10_cylA_int R m hm T hT γ hγ t φ ht hφ G hG2 P X ω h1
    have hIJ := S7PIF10_cylJ_int R m hm T hT γ hγ t φ ht hφ G hG2 P X ω h2
    have := h3
    rw [integral_add (hIA.const_mul _) (hIJ.const_mul _), integral_const_mul, integral_const_mul] at this
    exact this
  -- integrability of `J`
  have hJi : Integrable J P := by
    have hexp : Integrable (fun ω => 2 * Real.sqrt N * (L ω + (Real.sqrt N)⁻¹ * A ω - Mart ω)) P :=
      ((hLi.add (hAint.const_mul _)).sub hMi).const_mul _
    refine hexp.congr ?_
    filter_upwards [hsplit] with ω hω
    rw [hω]
    field_simp
    ring
  unfold PathItoConcl
  refine ⟨A, J, hAint, hJi, ?_, ?_, ?_⟩
  · -- the drift clause
    filter_upwards [hM1.1] with ω hω
    exact HRS.MC.Sec7.S7PIR.s7_PIF_RS_drift_proof R m hm T hT γ hγ t φ ht hφ G hG2 (zetaWin m T 0 P X ω)
      (fun u => quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω) hω
  · -- the covariance clause
    filter_upwards [hJt, hzi] with ω h1 h2
    exact HRS.MC.Sec7.S7PIR.s7_PIF_RS_J_proof R m hm T hT γ hγ t φ ht hφ G hG2 (zetaWin m T 0 P X ω)
      (fun u => etaE m (X u.toNNReal ω) (withDensityReal (R.ρ u))) h1 h2
  · -- the identity
    have hlhs : ∫ ω, G (obsVec m T t φ (ContinuousLinearMap.id ℝ (PathSpace d m T) (zetaWin m T 0 P X ω))) ∂P =
        ∫ ω, G (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) T)) ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [ContinuousLinearMap.id_apply]
      rw [S7PIF10_obs_predicted_T R m hm T hT t φ ht]
    have hheat : ∫ ω, heatFn γ (fun w => G (obsVec m T t φ (ContinuousLinearMap.id ℝ (PathSpace d m T) w))) 0
        (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) ∂P =
        ∫ ω, gaussHeat (obsCov R.D R.ρ t φ) G 0
          (obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω))) ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      exact hHO.1 0 ⟨le_rfl, hT.le⟩ _
    have hintL : ∫ ω, L ω ∂P = ∫ ω, G (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) T)) ∂P -
        ∫ ω, gaussHeat (obsCov R.D R.ρ t φ) G 0
          (obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω))) ∂P :=
      integral_sub hLi1 hLi2
    have hintL2 : ∫ ω, L ω ∂P = -(Real.sqrt N)⁻¹ * ∫ ω, A ω ∂P + (1 / (2 * Real.sqrt N)) * ∫ ω, J ω ∂P := by
      rw [integral_congr_ae hsplit]
      rw [integral_add (f := fun a => -(Real.sqrt N)⁻¹ * A a + 1 / (2 * Real.sqrt N) * J a) (g := Mart)
        ((hAint.const_mul _).add (hJi.const_mul _)) hMi]
      rw [integral_add (f := fun a => -(Real.sqrt N)⁻¹ * A a) (g := fun a => 1 / (2 * Real.sqrt N) * J a)
        (hAint.const_mul _) (hJi.const_mul _), integral_const_mul, integral_const_mul, hM0, add_zero]
    rw [hlhs, hheat]
    linarith

end Prob

end HRS.MC.Sec7.S7PIF10

end
