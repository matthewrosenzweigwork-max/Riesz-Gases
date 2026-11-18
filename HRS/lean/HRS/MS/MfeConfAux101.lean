import HRS.MS.MfeConfAux100

/-!
# S.B.1, packet F9 (part 4): invariance of the Gibbs measure `Γ_k` under the regularised flow

A flow `Y` of the regularised system (`P4AddSol`) started from `Γ_k` stays at `Γ_k`: the static case of `sb1_level_ineq`
(zero transport field `w`, constant tilt `Ψ = θ log Z_k`, source `S = 0`) gives `H(law(Y_t) | Γ_k) ≤ H(law(Y_0) | Γ_k) = 0`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_innerL_zero : p4InnerL (0 : EucConfig d N) = 0 := by
  ext h; simp [p4m_inner_eq]

theorem sb1S_zero (θ : ℝ) (b : ℝ → EucConfig d N → EucConfig d N) (r : ℝ) (x : EucConfig d N) :
    sb1S θ b (fun _ _ => 0) (fun _ _ => 0) r x = 0 := by
  simp [sb1S, sb1div, p4m_q, sb1_innerL_zero]

theorem sb1_tilt_zero (θ T c : ℝ) (b : ℝ → EucConfig d N → EucConfig d N) :
    Sb1Tilt θ T b (fun _ _ => 0) (fun _ _ => c) (fun _ _ => 0) (fun _ => |c|) (fun _ => 0) (fun _ => 0)
      (fun _ => 0) where
  Ψc := continuous_const
  Ψgrad := fun r x => by
    have h0 : p4InnerL ((fun (_ : ℝ) (_ : EucConfig d N) => (0 : EucConfig d N)) r x) = 0 := by
      ext h; simp [p4m_inner_eq]
    rw [h0]
    exact hasFDerivAt_const c x
  wc := continuous_const
  w1 := fun r => contDiff_const
  dwc := by
    have : (fun (r : ℝ) (x : EucConfig d N) => sb1div ((fun (_ : ℝ) (_ : EucConfig d N) => (0 : EucConfig d N)) r) x) =
        fun _ _ => 0 := by
      funext r x; simp [sb1div]
    simp only [this]
    exact continuous_const
  Wc := continuous_const
  Wd := fun r _ x => hasDerivAt_const r c
  nn := fun r => ⟨abs_nonneg c, le_rfl, le_rfl, le_rfl⟩
  Ψg := fun r x => by
    have := p4m_q_nonneg x
    nlinarith [abs_nonneg c]
  wg := fun r x => by simp
  Sg := fun r x => by
    rw [sb1S_zero]; simp
  intΨ := integrableOn_const (by simp)
  intB := integrableOn_const (by simp)
  intK := integrableOn_const (by simp)
  intS := integrableOn_const (by simp)

theorem sb1_Hs_cont (D : Whole.WholeDyn d) {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) {B : ℝ}
    (P : Sb1Pot D.V B) (N : ℕ) : Continuous (sb1Hs D k N) :=
  continuous_iff_continuousAt.2 fun x => (sb1_hasFDerivAt_Hs' D hk P N x).continuousAt

/-- **invariance** of `Γ_k` under the regularised flow -/
theorem sb1_gam_invariant (D : Whole.WholeDyn d) {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) {B : ℝ}
    (P : Sb1Pot D.V B) (hθ : 0 < D.invβ) {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x)
    {S : ℝ} (hS : 0 < S) {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hY : P4AddSol Pm D.invβ (fun _ => sb1DriftM D k N) S ℱ W' W Y) (h0 : law Pm (Y 0) = sb1Gam D k N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S) : law Pm (Y (Real.toNNReal t)) = sb1Gam D k N := by
  have hHc := sb1_Hs_cont D hk P N
  have hlow := hk.lower
  haveI hΓ := sb1_gam_prob hθ hHc hlow hcV hV
  have hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(law Pm (Y 0)) < ⊤ := by
    rw [h0]; exact sb1_gam_moment hθ hHc hlow hcV hV
  have hμ := sb1_flow_hyp D P hk hθ.le hS hY hmom
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
  have hclamp : p4m_clamp S t = t := p4m_clamp_eq ht
  have h00 : p4m_clamp S 0 = 0 := p4m_clamp_eq ⟨le_rfl, hS.le⟩
  have key := sb1_level_ineq (θ := D.invβ) (T := S) (b := fun _ => sb1DriftM D k N) (H := sb1Hs D k N)
    (w := fun _ _ => 0) (Ψ := fun _ _ => c) (Wψ := fun _ _ => 0) hMol
    (sb1_tilt_zero D.invβ S c _) hθ (DS := fun _ => 0) hS0 (integrableOn_const (by simp))
    (fun s _ x y => by rw [sb1S_zero, sb1S_zero]; simp)
    (fun s _ => by
      beta_reduce
      simp only [hq]
      exact sb1_Gq_lintegral hθ hHc hlow hcV hV)
    (Lw := 0) (LipschitzWith.const _) (C0 := CHs) (fun x => hCHs x)
    (by
      simp only [hqD, h00]
      change klDiv (law Pm (Y (Real.toNNReal 0))) (sb1Gam D k N) ≠ ⊤
      rw [Real.toNNReal_zero, h0, klDiv_self]
      exact ENNReal.zero_ne_top) ht
  obtain ⟨hne, hle⟩ := key
  beta_reduce at hne hle
  simp only [hq, hclamp, h00, Real.toNNReal_zero, h0, sb1S_zero, integral_zero, add_zero] at hne hle
  change klDiv (law Pm (Y (Real.toNNReal t))) (sb1Gam D k N) ≠ ⊤ at hne
  change (klDiv (law Pm (Y (Real.toNNReal t))) (sb1Gam D k N)).toReal ≤ (klDiv (sb1Gam D k N) (sb1Gam D k N)).toReal at hle
  rw [klDiv_self, ENNReal.toReal_zero] at hle
  have h0' : klDiv (law Pm (Y (Real.toNNReal t))) (sb1Gam D k N) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm hle ENNReal.toReal_nonneg) with h | h
    · exact h
    · exact absurd h hne
  haveI := (hμ.prob t)
  exact (klDiv_eq_zero_iff.1 h0')

end HRS.MS.MfeConf
