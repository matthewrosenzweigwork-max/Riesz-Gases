import HRS.Energy.G336Aux1

/-!
# G336 final: relocated proofs for Proposition 3.36 (statements verbatim)

Plan and statement check: header of `HRS/Energy/G336Aux1.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d : ℕ}

theorem gronwall_gradient_flow_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (T Λ lam₀ ΛV σ₀ : ℝ) (hT : 0 ≤ T) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : DynData d), D.s = s → D.invβ ≤ σ₀ → Torus.cbNorm (PDE.mStar d + 2) D.V ≤ ΛV →
      ∀ (N : ℕ), 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Torus d → ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Config d N),
        MFEHyp P D N T Λ lam₀ ρ X₀ W X →
        ∀ t ∈ Set.Icc 0 T,
          ∫⁻ ω, ENNReal.ofReal (correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t) ∂P ≤
            ENNReal.ofReal (C * (D.invβ *
              (normRelEntropy N (P.map X₀) (Measure.pi fun _ : Fin N => withDensityReal (ρ 0))).toReal +
              ∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P)) := by
  by_cases hl : 0 < lam₀
  swap
  · refine ⟨0, 1, le_rfl, one_pos, ?_⟩
    intro D _ _ _ N _ Ω _ P _ ρ X₀ W X h
    exact absurd h.pos_density.1 hl
  obtain ⟨C₀m, C₁, hC₀m, hC₁, hmfe⟩ := mfe_uniform_proof' hd hs0 hsd
  obtain ⟨B₀, hB₀, hnn⟩ := Commutator.energy_add_oN_nonneg hd hs0 hsd
  obtain ⟨Ct, hCt0, hCt⟩ := transport_bound_uniform_proof hd hs0 hsd Λ lam₀ ΛV σ₀ hl
  set C₀ : ℝ := max C₀m B₀ with hC₀def
  set C : ℝ := Real.exp (C₁ * (T * Ct)) with hCdef
  refine ⟨C₀, C, le_max_of_le_left hC₀m, Real.exp_pos _, ?_⟩
  intro D hDs hDσ hDV N hN Ω _ P _ ρ X₀ W X h t ht
  have hΛ1 : 1 ≤ Λ := h.Λ_ge
  have hΛ0 : 0 ≤ Λ := by linarith
  have hβ : 0 < D.invβ := h.pos_temp
  subst hDs
  set o : ℝ := oNΛ d D.s C₀ Λ N with ho
  set o₁ : ℝ := oNΛ d D.s C₀m Λ N with ho₁
  have hoo : o₁ ≤ o := oNΛ_mono_C₀ (le_max_left _ _) hΛ0 N
  have hoB : oNΛ d D.s B₀ Λ N ≤ o := oNΛ_mono_C₀ (le_max_right _ _) hΛ0 N
  have hρΛ : ∀ r ∈ Set.Icc 0 T, ∀ x, ρ r x ≤ Λ := fun r hr x =>
    (le_abs_self _).trans ((PDE.R2Aux.abs_le_cbNorm (h.mf_reg r hr).1 x).trans (h.mf_reg r hr).2)
  -- transport bound
  have hTB : ∀ r ∈ Set.Icc 0 T, HasTransportBound d D.s (mfeTransport D (ρ r)) Ct := fun r hr =>
    hCt D rfl hβ hDσ h.V_reg hDV (ρ r) (h.mf.density r hr) (h.mf_reg r hr).1 (h.mf_reg r hr).2
      (fun x => (h.pos_density.2 r hr x))
  have key := hmfe D rfl N hN T Λ lam₀ hT P ρ X₀ W X h (fun _ => Ct)
    (integrableOn_const (by simp)) hTB
  have hint : ∫ r in Set.Icc (0 : ℝ) T, Ct = T * Ct := by
    rw [setIntegral_const]; simp [Real.volume_real_Icc_of_le hT]
  have hX : ∀ r : ℝ≥0, Measurable (X r) := h.sol.adapted
  -- nonnegativity of the corrected energy a.s.
  have hnonneg : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      0 ≤ rieszEnergy d D.s (X (Real.toNNReal r) ω) (withDensityReal (ρ r)) + o := by
    intro r hr
    filter_upwards [h.sol.no_collision] with ω hω
    have := hnn Λ hΛ1 N hN (ρ r) (h.mf.density r hr) (hρΛ r hr) _
      (hω (Real.toNNReal r) (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2))
    linarith
  -- time 0
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hfin0 := h.mfe_init
  have hint0 := hfin0.2
  have hX₀m : AEMeasurable X₀ P := by
    have : X 0 =ᵐ[P] X₀ := by
      filter_upwards [h.sol.init] with ω hω using hω
    exact (hX 0).aemeasurable.congr this
  have hce0 : ∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P =
      ∫ x, rieszEnergy d D.s x (withDensityReal (ρ 0)) ∂(P.map X₀) + o := by
    rw [← g336_integral_map P X₀ hX₀m _ o hint0]
    refine integral_congr_ae ?_
    filter_upwards [h.sol.init] with ω hω
    simp only [correctedEnergy, hω]
    rfl
  obtain ⟨-, hfint, hineq⟩ := key t ht
  have hineq' := hineq
  simp only [hint] at hineq'
  unfold modulatedFreeEnergy at hineq'
  have hnnt := hnonneg t ht
  have hgoal : ∫⁻ ω, ENNReal.ofReal (correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t) ∂P =
      ENNReal.ofReal (∫ x, rieszEnergy d D.s x (withDensityReal (ρ t)) ∂(P.map (X (Real.toNNReal t))) + o) :=
    g336_lintegral_map P (X (Real.toNNReal t)) (hX _).aemeasurable _ o hfint.2 hnnt
  rw [hgoal, hce0]
  apply ENNReal.ofReal_le_ofReal
  have hHt : 0 ≤ (normRelEntropy N (P.map (X (Real.toNNReal t)))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ t))).toReal := ENNReal.toReal_nonneg
  have hC1 : 1 ≤ C := by
    rw [hCdef]; apply Real.one_le_exp
    exact mul_nonneg hC₁.le (mul_nonneg hT hCt0)
  have hmul := mul_nonneg hβ.le hHt
  have hdo : 0 ≤ o - o₁ := by linarith
  have hCo : o - o₁ ≤ C * (o - o₁) := by nlinarith
  nlinarith

example := (@gronwall_gradient_flow_proof : type_of% @HRS.gronwall_gradient_flow)

end HRS
