import HRS.PDE.MovAAux22
import HRS.PDE.MovSXAux7

/-!
# MOVA Aux23: `movT_traj_bounds`; the degenerate case `T = 0` of `movT_source_exp_uniform`
(the decomposition `movT_srcReg_decomp` is false there, see `MovAFinal`; the exponential bound is
recovered by replacing `ρt` with the mean-field right-hand side, which changes `S^M` by a bounded amount).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_traj_bounds {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} (h : MovTraj D T ρ) :
    ∃ c₀ Lu : ℝ, 0 < c₀ ∧ 0 < Lu ∧ (∀ r ∈ Set.Icc 0 T, ∀ x, c₀ ≤ ρ r x) ∧
      ∀ r ∈ Set.Icc 0 T, IsLipschitzVF Lu (mfeTransport D (ρ r)) := by
  by_cases hT : 0 ≤ T
  · obtain ⟨ρt, hρt⟩ := h.classical
    obtain ⟨c₀, hc₀, hc₀low⟩ := mova_traj_c0 hT hρt (fun r hr x => h.pos r hr x)
    obtain ⟨Λ₂, hΛ₂⟩ := h.bounds
    set Λ : ℝ := max Λ₂ 0 with hΛdef
    have hΛ0 : 0 ≤ Λ := le_max_right _ _
    have hκ := h.pos_temp
    have hL1g := mova_L1_nonneg (periodicRiesz d D.s)
    have hV0 : 0 ≤ Torus.cbNorm 2 D.V := KernelGrad.cbNorm_nonneg' D.V 2
    refine ⟨c₀, d * (D.invβ * (Λ / c₀ + Λ * Λ / (c₀ * c₀)) +
      mova_L1 (periodicRiesz d D.s) * Λ + Torus.cbNorm 2 D.V) + 1, hc₀, by positivity, hc₀low,
      fun r hr => ?_⟩
    have := mova_lip_mfeTransport D h.V_reg hκ (h.ck r hr) hc₀ (hc₀low r hr) (Λ := Λ)
      ((hΛ₂ r hr).trans (le_max_left Λ₂ 0))
    exact mova_isLipschitzVF_mono (by linarith) this
  · refine ⟨1, 1, one_pos, one_pos, fun r hr => absurd (hr.1.trans hr.2) hT, fun r hr =>
      absurd (hr.1.trans hr.2) hT⟩

set_option maxHeartbeats 1600000 in
/-- The exponential bound for `T = 0`. -/
theorem mova_source_exp_uniform_zero (hN : 2 ≤ N) {D : DynData d} {ρ ρt : ℝ → Torus d → ℝ}
    (htr : MovTraj D 0 ρ) (hρt : IsC12Test 0 ρ ρt) :
    ∃ l C M₀ : ℝ, 0 < l ∧ ∀ M : ℝ, M₀ ≤ M → ∀ r ∈ Set.Icc (0 : ℝ) 0,
      ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N M ρ ρt r X|))
        ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) ≤ ENNReal.ofReal (Real.exp C) := by
  set ρt' : ℝ → Torus d → ℝ := fun r x => mova_pdeRHS D (ρ r) x with hρt'
  have hcP := mova_cont_pde D hρt htr.V_reg
  have hρt'c : ∀ r ∈ Set.Icc (0 : ℝ) 0, Continuous (ρt' r) := fun r hr =>
    hcP.comp (continuous_const.prodMk continuous_id :
      Continuous fun x : Torus d => ((⟨r, hr⟩ : Set.Icc (0 : ℝ) 0), x))
  have hdec := mova_srcReg_decomp_gen hN htr hρt le_rfl hρt'c (fun r hr x => rfl)
  obtain ⟨l, C, M₀, hl, hbound⟩ := movsx_source_exp_uniform_of hN htr hdec (mova_traj_bounds htr)
  obtain ⟨c₀, hc₀, hc₀low⟩ := mova_traj_c0 le_rfl hρt (fun r hr x => htr.pos r hr x)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 0 := ⟨le_rfl, le_rfl⟩
  obtain ⟨Bρ, hBρ0, hBρ⟩ := mova_bound_of_continuous
    ((mova_cont_ρt_slice hρt h0).sub (hρt'c 0 h0))
  have hκ := htr.pos_temp
  set Bd : ℝ := (1 / c₀ + D.invβ⁻¹ * (mova_L1 (periodicRiesz d D.s) + mova_L1 (mova_kM D 0))) * Bρ
    with hBd
  have hBd0 : 0 ≤ Bd := by
    rw [hBd]
    have := mova_L1_nonneg (periodicRiesz d D.s)
    have := mova_L1_nonneg (mova_kM D 0)
    have : 0 < D.invβ⁻¹ := inv_pos.2 hκ
    positivity
  refine ⟨l, C + 2 * N * Bd * l, max M₀ 0, hl, fun M hM r hr => ?_⟩
  have hr0 : r = 0 := le_antisymm hr.2 hr.1
  subst hr0
  have hM0 : 0 ≤ M := (le_max_right _ _).trans hM
  have hM₀ : M₀ ≤ M := (le_max_left _ _).trans hM
  have hQ := movT_QReg_isProb (N := N) D htr M h0
  haveI := hQ
  have hdiff : ∀ X : Config d N, |movT_srcReg D N M ρ ρt 0 X| ≤ |movT_srcReg D N M ρ ρt' 0 X| +
      2 * N * Bd := by
    intro X
    have := mova_srcReg_diff_le D hM0 (ρ := ρ) (ρt₁ := ρt) (ρt₂ := ρt') (r := 0) (N := N)
      (htr.ck 0 h0) (htr.pos 0 h0) hc₀ (hc₀low 0 h0) (mova_cont_ρt_slice hρt h0) (hρt'c 0 h0) hκ
      (Bρ := Bρ) (fun x => hBρ x) X
    have h2 := abs_sub_abs_le_abs_sub (movT_srcReg D N M ρ ρt 0 X) (movT_srcReg D N M ρ ρt' 0 X)
    linarith
  have hb := hbound M hM₀ 0 h0
  calc ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N M ρ ρt 0 X|))
        ∂(movT_Q (b15c_gReg d D.s M) D N ρ 0)
      ≤ ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (2 * N * Bd * l)) *
          ENNReal.ofReal (Real.exp (l * |movT_srcReg D N M ρ ρt' 0 X|))
          ∂(movT_Q (b15c_gReg d D.s M) D N ρ 0) := by
        refine lintegral_mono fun X => ?_
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have := mul_le_mul_of_nonneg_left (hdiff X) hl.le
        nlinarith
    _ = ENNReal.ofReal (Real.exp (2 * N * Bd * l)) * ∫⁻ X : Config d N,
          ENNReal.ofReal (Real.exp (l * |movT_srcReg D N M ρ ρt' 0 X|))
          ∂(movT_Q (b15c_gReg d D.s M) D N ρ 0) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (2 * N * Bd * l)) * ENNReal.ofReal (Real.exp C) :=
        mul_le_mul' le_rfl hb
    _ = ENNReal.ofReal (Real.exp (C + 2 * N * Bd * l)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_comm]

end HRS
