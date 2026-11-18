import HRS.MC.E213U16f
import HRS.Main.GFB1Aux1
import HRS.MC.E213U10A
import HRS.MC.E213U13o

/-!
# Packet e213u16, file g: the predicted path as a continuous linear map, and the future noise `Γ_τ = Z - 𝖳_τ Z`

* `predCLM`: `w ↦ predicted w τ` as a continuous linear endomorphism of `𝒳_{m,H}`;
* `Gam τ ω = Z ω - predicted (Z ω) τ`, `Z = Zwin H 0`; its law is a centred Gaussian measure.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10

variable {d : ℕ}

section Pred

variable {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m)

theorem u16_pathAt_add {T : ℝ} (w₁ w₂ : PathSpace d m T) (t : ℝ) :
    pathAt (w₁ + w₂) t = pathAt w₁ t + pathAt w₂ t := by
  unfold pathAt
  by_cases h : t ∈ Set.Icc (0 : ℝ) T
  · rw [dif_pos h, dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h, dif_neg h]; simp

theorem u16_pathAt_smul {T : ℝ} (c : ℝ) (w : PathSpace d m T) (t : ℝ) :
    pathAt (c • w) t = c • pathAt w t := by
  unfold pathAt
  by_cases h : t ∈ Set.Icc (0 : ℝ) T
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h]; simp

theorem u16_vprop_lin {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (F G : NegSobolev d m) (c : ℝ) :
    Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t u (F + c • G) =
      Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t u F + c • Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t u G := by
  obtain ⟨C, c', hC, hc, Vev, hsp⟩ := HRS.MC.E213U1.u1_vev hE
  rw [hsp.2.1 u t hu hut, hsp.2.1 u t hu hut, hsp.2.1 u t hu hut, map_add, map_smul]

theorem u16_vprop_smul {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (F : NegSobolev d m) (c : ℝ) :
    Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t u (c • F) =
      c • Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t u F := by
  obtain ⟨C, c', hC, hc, Vev, hsp⟩ := HRS.MC.E213U1.u1_vev hE
  rw [hsp.2.1 u t hu hut, hsp.2.1 u t hu hut, map_smul]

theorem u16_predicted_pathAt {H : ℝ} (hH : 0 < H) (w : PathSpace d m H) {τ t : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H)
    (ht : t ∈ Set.Icc (0 : ℝ) H) :
    pathAt (predicted (regime S β₀ hE).D (regime S β₀ hE).ρ w τ) t =
      if t ≤ τ then pathAt w t else Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t τ (pathAt w τ) :=
  (HRS.MC.Sec7.S7PIS1.s7_PIS_path_facts_proof (regime S β₀ hE) m hE.m_gt H hH).1 w τ t hτ ht

theorem u16_predicted_bound {H : ℝ} (hH : 0 < H) :
    ∃ CY : ℝ, 1 ≤ CY ∧ ∀ (w : PathSpace d m H) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) H →
      ‖predicted (regime S β₀ hE).D (regime S β₀ hE).ρ w τ‖ ≤ CY * ‖w‖ := by
  obtain ⟨C, c, hC, hc, hV⟩ := HRS.MC.E213D.vprop_stable_of_prepared S β₀ hE m
  refine ⟨max 1 C, le_max_left _ _, fun w τ hτ => ?_⟩
  refine (ContinuousMap.norm_le _ (by positivity)).2 (fun t => ?_)
  show ‖(predicted (regime S β₀ hE).D (regime S β₀ hE).ρ w τ).at' t‖ ≤ _
  rw [← u10_pathAt_eq, u16_predicted_pathAt hE hH w hτ t.2]
  split_ifs with h
  · exact (u10_pathAt_norm_le w _).trans (le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _))
  · have hlt : τ ≤ (t : ℝ) := (not_le.1 h).le
    refine (hV τ t hτ.1 hlt _).trans ?_
    have h1 : Real.exp (-c * (t - τ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    calc C * Real.exp (-c * (t - τ)) * ‖pathAt w τ‖ ≤ C * 1 * ‖w‖ := by
          gcongr
          exact u10_pathAt_norm_le w τ
      _ ≤ max 1 C * ‖w‖ := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- `w ↦ 𝖳_τ w` as a continuous linear map. -/
def predCLM {H : ℝ} (hH : 0 < H) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) : PathSpace d m H →L[ℝ] PathSpace d m H :=
  LinearMap.mkContinuous
    { toFun := fun w => predicted (regime S β₀ hE).D (regime S β₀ hE).ρ w τ
      map_add' := fun w₁ w₂ => by
        refine u10_path_ext fun t ht => ?_
        rw [u16_pathAt_add, u16_predicted_pathAt hE hH _ hτ ht, u16_predicted_pathAt hE hH _ hτ ht,
          u16_predicted_pathAt hE hH _ hτ ht]
        split_ifs with h
        · rw [u16_pathAt_add]
        · have := u16_vprop_lin hE (c := 1) hτ.1 (not_le.1 h).le (pathAt w₁ τ) (pathAt w₂ τ)
          rw [u16_pathAt_add]
          simpa using this
      map_smul' := fun c w => by
        refine u10_path_ext fun t ht => ?_
        rw [u16_pathAt_smul, RingHom.id_apply, u16_predicted_pathAt hE hH _ hτ ht,
          u16_predicted_pathAt hE hH _ hτ ht]
        split_ifs with h
        · rw [u16_pathAt_smul]
        · rw [u16_pathAt_smul]
          exact u16_vprop_smul hE hτ.1 (not_le.1 h).le _ c }
    (Classical.choose (u16_predicted_bound hE hH)) (fun w =>
      (Classical.choose_spec (u16_predicted_bound hE hH)).2 w τ hτ)

theorem predCLM_apply {H : ℝ} (hH : 0 < H) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) (w : PathSpace d m H) :
    predCLM hE hH hτ w = predicted (regime S β₀ hE).D (regime S β₀ hE).ρ w τ := rfl

end Pred

section Gam

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_Z_aemeasurable (H : ℝ) (hH : 0 < H) : AEMeasurable (gd.Zwin H 0) gd.P₀ := by
  obtain ⟨C, -, hC⟩ := HRS.MC.E213U11.u11_eta_moment gd H hH 1 le_rfl
  have h := (hC 0 le_rfl).1
  exact (HRS.MD.EQInterp.epath (rLvl_le hE) H).continuous.measurable.comp_aemeasurable h

/-- The future noise `Γ_τ = Z - 𝖳_τ Z`, `Z = Zwin H 0`. -/
def Gam (H τ : ℝ) (ω : gd.Ω₀) : PathSpace d m H :=
  gd.Zwin H 0 ω - predicted (regime S β₀ hE).D (regime S β₀ hE).ρ (gd.Zwin H 0 ω) τ

theorem u16_Gam_eq (H : ℝ) (hH : 0 < H) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) :
    Gam gd H τ = fun ω => (ContinuousLinearMap.id ℝ (PathSpace d m H) - predCLM hE hH hτ) (gd.Zwin H 0 ω) := rfl

theorem u16_Gam_aemeasurable (H : ℝ) (hH : 0 < H) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) :
    AEMeasurable (Gam gd H τ) gd.P₀ := by
  rw [u16_Gam_eq gd H hH hτ]
  exact (ContinuousLinearMap.id ℝ (PathSpace d m H) - predCLM hE hH hτ).continuous.measurable.comp_aemeasurable
    (u16_Z_aemeasurable gd H hH)

theorem u16_isCentered_map {B B' : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [SecondCountableTopology B] [NormedAddCommGroup B'] [NormedSpace ℝ B'] [MeasurableSpace B']
    [BorelSpace B'] [SecondCountableTopology B'] {γ : Measure B} (h : IsCenteredGaussian γ) (A : B →L[ℝ] B') :
    IsCenteredGaussian (γ.map A) := by
  have := h.1
  refine ⟨inferInstance, fun L => ?_⟩
  rw [integral_map A.continuous.measurable.aemeasurable L.continuous.aestronglyMeasurable]
  exact h.2 (L.comp A)

theorem u16_Gam_centered (H : ℝ) (hH : 0 < H) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) :
    IsCenteredGaussian (gd.P₀.map (Gam gd H τ)) := by
  obtain ⟨ξ, -, hξ⟩ := chaos_data_proof gd H hH
  have h0 := (hξ 0 le_rfl).1
  set A := ContinuousLinearMap.id ℝ (PathSpace d m H) - predCLM hE hH hτ with hA
  have := u16_isCentered_map h0 A
  have hm := AEMeasurable.map_map_of_aemeasurable A.continuous.measurable.aemeasurable (u16_Z_aemeasurable gd H hH)
  rw [u16_Gam_eq gd H hH hτ]
  have e : (fun ω => A (gd.Zwin H 0 ω)) = A ∘ gd.Zwin H 0 := rfl
  rw [show (fun ω => (ContinuousLinearMap.id ℝ (PathSpace d m H) - predCLM hE hH hτ) (gd.Zwin H 0 ω)) =
    A ∘ gd.Zwin H 0 from rfl, ← hm]
  exact this

end Gam

section GamCoord

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_Z_at {H : ℝ} (hH : 0 < H) {ω : gd.Ω₀} (hc : ContinuousOn (fun t => gd.η t ω) (Set.Icc 0 H))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) H) :
    pathAt (gd.Zwin H 0 ω) t = NegSobolev.embed m (gd.η t ω) := by
  unfold pathAt
  rw [dif_pos ht]
  have h1 := e213q_procWin_at (m := rLvl d) (Z := gd.η) H 0 le_rfl ω (by simpa using hc) ⟨t, ht⟩
  unfold GaussData.Zwin
  rw [HRS.MD.EQInterp.epath_at', h1]
  simp

theorem u16_eval_zero {m' : ℝ} (φ : Torus d → ℝ) : NegSobolev.eval (0 : NegSobolev d m') φ = 0 := by
  have h : ∀ k, NegSobolev.fourierCoeff (0 : NegSobolev d m') k = 0 := fun k => by
    have : NegSobolev.coord (0 : NegSobolev d m') k = 0 := rfl
    simp [NegSobolev.fourierCoeff, this]
  unfold NegSobolev.eval
  simp [h]

/-- Pairings of the future noise with smooth test functions. -/
theorem u16_Gam_eval {H : ℝ} (hH : 0 < H) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) {ω : gd.Ω₀}
    (hc : ContinuousOn (fun t => gd.η t ω) (Set.Icc 0 H)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) H)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    NegSobolev.eval (pathAt (Gam gd H τ ω) t) φ =
      if τ < t then NegSobolev.eval (gd.η t ω) φ - NegSobolev.eval (gd.η τ ω) (propagator S.dyn S.ρ τ t φ) else 0 := by
  unfold Gam
  rw [HRS.MC.E213U10.u10_pathAt_sub, u16_predicted_pathAt hE hH _ hτ ht, u16_Z_at gd hH hc ht]
  by_cases h : τ < t
  · rw [if_neg (not_le.2 h), if_pos h, u16_Z_at gd hH hc hτ,
      HRS.GF.gf_eval_sub_proof _ _ hφ, HRS.MD.EQGaussLift.eqgl_eval_embed (rLvl_le hE)]
    rw [u16_V_eval (HRS.MC.E213A.regimeOfPrepared S β₀ hE) m hE.m_gt hτ.1 h.le _ hφ,
      HRS.MD.EQGaussLift.eqgl_eval_embed (rLvl_le hE)]
    rfl
  · rw [if_pos (not_lt.1 h), if_neg h, sub_self]
    exact u16_eval_zero φ

end GamCoord

end HRS.MC.E213U16

end
