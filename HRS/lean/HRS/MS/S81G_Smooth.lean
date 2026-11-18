import HRS.MS.MfeConfAux103

/-!
# S81G, packet G4: entropy contraction of the regularised flow for an ARBITRARY initial law

`s81g_smooth_contraction`: for a truncated kernel `k` (`IsP4Kernel`), the regularised flow `sb1Flow` started at a probability
measure `ν₀` with finite second moment and `H(ν₀ | Γ_k) < ∞` satisfies `H(flow_t | Γ_k) ≤ H(ν₀ | Γ_k)`, `t ≥ 0`
(static case of `sb1_level_ineq`; the proof of `sb1_gam_invariant` with `ν₀` in place of `Γ_k`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl HRS.MS.MfeConf HRS.MD.EQLawPath
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S81G

variable {d N : ℕ}

theorem s81g_smooth_contraction (D : Whole.WholeDyn d) {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k)
    {B : ℝ} (P : Sb1Pot D.V B) (hθ : 0 < D.invβ) {cV CV : ℝ} (hcV : 0 < cV)
    (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x)
    (ν₀ : Measure (Whole.EucConfig d N)) [IsProbabilityMeasure ν₀]
    (hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂ν₀ < ⊤) (hfin : klDiv ν₀ (sb1Gam D k N) ≠ ⊤)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW : IsBrownianFiltration Pm ℱ W')
    {t : ℝ} (ht : 0 ≤ t) :
    klDiv (sb1Flow D k N ν₀ (Pm.map (bfPath hW)) t) (sb1Gam D k N) ≤ klDiv ν₀ (sb1Gam D k N) := by
  obtain ⟨Ω', mΩ', P', hP', ℱ', W'', Wc, Y, hY, h0, hlaw⟩ := sb1_flow_of_init D hk P ν₀ (t + 1) hW
  have hS : (0 : ℝ) < t + 1 := by linarith
  have htS : t ∈ Set.Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  have hHc := sb1_Hs_cont D hk P N
  have hlow := hk.lower
  haveI hΓ := sb1_gam_prob hθ hHc hlow hcV hV
  have hmom' : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(law P' (Y 0)) < ⊤ := by
    rw [h0]; exact hmom
  have hμ := sb1_flow_hyp D P hk hθ.le hS hY hmom'
  obtain ⟨Kl, B', K', M', CV', hMol⟩ := sb1_molData_regularised hS.le D hk P N hμ
  have hz := sb1_gz_pos hθ hHc hlow hcV hV
  set c : ℝ := D.invβ * Real.log (sb1Gz D k N) with hc
  have hq : ∀ x : Whole.EucConfig d N, Real.exp (-D.invβ⁻¹ * (sb1Hs D k N x + c)) = sb1Gq D k N x := by
    intro x
    have hθ0 := hθ.ne'
    have e : -D.invβ⁻¹ * (sb1Hs D k N x + c) = -D.invβ⁻¹ * sb1Hs D k N x - Real.log (sb1Gz D k N) := by
      rw [hc]; field_simp; ring
    rw [e, Real.exp_sub, Real.exp_log hz]
    rfl
  have hqD : (fun x : Whole.EucConfig d N => Real.exp (-D.invβ⁻¹ * (sb1Hs D k N x + c))) = sb1Gq D k N :=
    funext hq
  have hS0 : ∀ s, 0 ≤ (fun _ : ℝ => (0 : ℝ)) s := fun s => le_rfl
  obtain ⟨CHs, hCHs⟩ : ∃ C0 : ℝ, ∀ x, 0 ≤ sb1Hs D k N x + c + C0 := by
    refine ⟨N * CV + (N : ℝ) ^ 2 / cV - c, fun x => ?_⟩
    have := sb1_Hs_lower D hlow N hcV hV x
    nlinarith [sq_nonneg ‖x‖]
  have hclamp : p4m_clamp (t + 1) t = t := p4m_clamp_eq htS
  have h00 : p4m_clamp (t + 1) 0 = 0 := p4m_clamp_eq ⟨le_rfl, hS.le⟩
  have key := sb1_level_ineq (θ := D.invβ) (T := t + 1) (b := fun _ => sb1DriftM D k N) (H := sb1Hs D k N)
    (w := fun _ _ => 0) (Ψ := fun _ _ => c) (Wψ := fun _ _ => 0) hMol
    (sb1_tilt_zero D.invβ (t + 1) c _) hθ (DS := fun _ => 0) hS0 (integrableOn_const (by simp))
    (fun s _ x y => by rw [sb1S_zero, sb1S_zero]; simp)
    (fun s _ => by
      beta_reduce
      simp only [hq]
      exact sb1_Gq_lintegral hθ hHc hlow hcV hV)
    (Lw := 0) (LipschitzWith.const _) (C0 := CHs) (fun x => hCHs x)
    (by
      simp only [hqD, h00]
      change klDiv (law P' (Y (Real.toNNReal 0))) (sb1Gam D k N) ≠ ⊤
      rw [Real.toNNReal_zero, h0]
      exact hfin) htS
  obtain ⟨hne, hle⟩ := key
  beta_reduce at hne hle
  simp only [hq, hclamp, h00, Real.toNNReal_zero, h0, sb1S_zero, integral_zero, add_zero] at hne hle
  change klDiv (law P' (Y (Real.toNNReal t))) (sb1Gam D k N) ≠ ⊤ at hne
  change (klDiv (law P' (Y (Real.toNNReal t))) (sb1Gam D k N)).toReal ≤
    (klDiv ν₀ (sb1Gam D k N)).toReal at hle
  rw [← hlaw t ht]
  exact (ENNReal.toReal_le_toReal hne hfin).1 hle

end HRS.MS.S81G
