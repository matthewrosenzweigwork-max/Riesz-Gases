import HRS.MS.MfeConfAux91

/-!
# S.B.1, packet F8 (part 24): `κ`, `κ'`: continuity, bounds, derivative
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Traj

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

theorem sb1_lv_kappa_cont (hk4 : IsP4Kernel d D.s r₀ k) (hθ : 0 < D.invβ) (hN : 1 ≤ N) :
    Continuous (sb1_lv_kappa D k N hT ρ) := by
  have hk := sb1KerU_of_p4 H.tr.hs0 hk4
  have hβ : 0 ≤ D.invβ⁻¹ := (inv_pos.2 hθ).le
  have hK := sb1_lv_Kb_cont H hT hk hβ hN (N := N)
  have hlog : Continuous fun s => Real.log (sb1_lv_Kb k D.invβ⁻¹ N hT ρ s) :=
    continuous_iff_continuousAt.2 fun s => hK.continuousAt.log (sb1_lv_Kb_pos H hT hk hβ hN s).ne'
  exact (continuous_const.mul hlog).add (continuous_const.mul (sb1_lv_cb_cont H hT hk))

theorem sb1_lv_kappa_bound (hk4 : IsP4Kernel d D.s r₀ k) (hθ : 0 < D.invβ) (hN : 1 ≤ N) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ s, |sb1_lv_kappa D k N hT ρ s| ≤ Ck := by
  have hk := sb1KerU_of_p4 H.tr.hs0 hk4
  have hβ : 0 ≤ D.invβ⁻¹ := (inv_pos.2 hθ).le
  obtain ⟨m, M, hm, hmM⟩ := sb1_lv_Kb_bounds H hT hk hβ hN (N := N)
  set Cc := (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) +
      sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) with hCc
  refine ⟨D.invβ * (|Real.log m| + |Real.log M|) + ((N : ℝ) / 2) * Cc, ?_, fun s => ?_⟩
  · have : 0 ≤ Cc := (abs_nonneg _).trans (sb1_lv_cb_bound H hT hk 0)
    positivity
  · have hl : |Real.log (sb1_lv_Kb k D.invβ⁻¹ N hT ρ s)| ≤ |Real.log m| + |Real.log M| := by
      obtain ⟨h1, h2⟩ := hmM s
      have hp := sb1_lv_Kb_pos H hT hk hβ hN s
      have a1 : Real.log m ≤ Real.log (sb1_lv_Kb k D.invβ⁻¹ N hT ρ s) := Real.log_le_log hm h1
      have a2 : Real.log (sb1_lv_Kb k D.invβ⁻¹ N hT ρ s) ≤ Real.log M := Real.log_le_log hp h2
      rw [abs_le]
      constructor <;> nlinarith [neg_abs_le (Real.log m), le_abs_self (Real.log M), abs_nonneg (Real.log m),
        abs_nonneg (Real.log M)]
    unfold sb1_lv_kappa
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_pos hθ]
      exact mul_le_mul_of_nonneg_left hl hθ.le
    · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) / 2)]
      exact mul_le_mul_of_nonneg_left (sb1_lv_cb_bound H hT hk s) (by positivity)

theorem sb1_lv_kappa'_cont (hk4 : IsP4Kernel d D.s r₀ k) (hθ : 0 < D.invβ) (hN : 1 ≤ N) :
    Continuous (sb1_lv_kappa' D k N hT ρ) := by
  have hk := sb1KerU_of_p4 H.tr.hs0 hk4
  have hβ : 0 ≤ D.invβ⁻¹ := (inv_pos.2 hθ).le
  have hK := sb1_lv_Kb_cont H hT hk hβ hN (N := N)
  have hKd := sb1_lv_Kdot_cont H hT hk4 hβ hN (N := N)
  exact (continuous_const.mul (hKd.div hK (fun s => (sb1_lv_Kb_pos H hT hk hβ hN s).ne'))).add
    (continuous_const.mul (sb1_lv_cdot_cont H hT hk4))

theorem sb1_lv_kappa'_bound (hk4 : IsP4Kernel d D.s r₀ k) (hθ : 0 < D.invβ) (hN : 1 ≤ N) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ s, |sb1_lv_kappa' D k N hT ρ s| ≤ Cd := by
  have hk := sb1KerU_of_p4 H.tr.hs0 hk4
  have hβ : 0 ≤ D.invβ⁻¹ := (inv_pos.2 hθ).le
  obtain ⟨m, M, hm, hmM⟩ := sb1_lv_Kb_bounds H hT hk hβ hN (N := N)
  have hBd : Integrable (fun X : Whole.EucConfig d N => ∏ l, sb1w ((d : ℝ) + 2) (X l)) volume :=
    Integrable.fintype_prod (fun _ => sb1w_int H.tr.hd (p := (d : ℝ) + 2) (by linarith))
  set CK := sb1Kb d D B C C3 D.invβ⁻¹ N * ∫ X : Whole.EucConfig d N, ∏ l, sb1w ((d : ℝ) + 2) (X l) with hCK
  have hCK0 : 0 ≤ CK := by
    have := (abs_nonneg (sb1Wdot D ρ k D.invβ⁻¹ N 0 (fun _ => 0)))
    have hb := sb1_Wdot_bound H hk hβ hN ⟨le_rfl, hT⟩ (fun _ => (0 : Euc d))
    have h1 : 0 ≤ sb1Kb d D B C C3 D.invβ⁻¹ N * ∏ l : Fin N, sb1w ((d : ℝ) + 2) ((fun _ => (0 : Euc d)) l) :=
      this.trans hb
    have h2 : 0 < ∏ l : Fin N, sb1w ((d : ℝ) + 2) ((fun _ => (0 : Euc d)) l) :=
      Finset.prod_pos fun l _ => sb1w_pos _ _
    have h3 : 0 ≤ sb1Kb d D B C C3 D.invβ⁻¹ N := by
      by_contra hneg
      push Not at hneg
      nlinarith
    exact mul_nonneg h3 (integral_nonneg fun X => Finset.prod_nonneg fun l _ => (sb1w_pos _ _).le)
  set Cdot := (sb1CA D B C C3 * (1 + sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)) +
      C3 * sb1CGd d D.s (sb1CA D B C C3)) * ∫ x : Euc d, sb1w ((d : ℝ) + 1) x with hCdot
  have hCdot0 : 0 ≤ Cdot := (abs_nonneg _).trans (sb1_lv_cdot_bound H hT hk4 0)
  refine ⟨D.invβ * (CK / m) + ((N : ℝ) / 2) * Cdot, by positivity, fun s => ?_⟩
  have hKd : |sb1_lv_Kdot D k D.invβ⁻¹ N hT ρ s| ≤ CK := by
    unfold sb1_lv_Kdot
    have := norm_integral_le_of_norm_le (hBd.const_mul (sb1Kb d D B C C3 D.invβ⁻¹ N))
      (f := fun X : Whole.EucConfig d N => sb1Wdot D ρ k D.invβ⁻¹ N (sb1_lv_cl' hT s) X)
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact sb1_Wdot_bound H hk hβ hN (sb1_lv_cl'_mem hT s) X)
    rw [integral_const_mul, Real.norm_eq_abs] at this
    exact this
  unfold sb1_lv_kappa'
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos hθ]
    refine mul_le_mul_of_nonneg_left ?_ hθ.le
    rw [abs_div, abs_of_pos (sb1_lv_Kb_pos H hT hk hβ hN s)]
    exact div_le_div₀ hCK0 hKd hm (hmM s).1
  · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) / 2)]
    exact mul_le_mul_of_nonneg_left (sb1_lv_cdot_bound H hT hk4 s) (by positivity)

theorem sb1_lv_kappa_dt (hk4 : IsP4Kernel d D.s r₀ k) (hθ : 0 < D.invβ) (hN : 1 ≤ N) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (sb1_lv_kappa D k N hT ρ) (sb1_lv_kappa' D k N hT ρ s) s := by
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 H.tr.hs0
  have hk := sb1KerU_of_p4 H.tr.hs0 hk4
  have hβ : 0 ≤ D.invβ⁻¹ := (inv_pos.2 hθ).le
  have hIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
  have hcl : sb1_lv_cl' hT s = s := by unfold sb1_lv_cl'; rw [Set.projIcc_of_mem hT hIcc]
  have hKd := sb1_hasDerivAt_K H hT hk hRg hβ hN hs (N := N)
  have hcd := sb1_hasDerivAt_c H hT hk hs
  have hKpos := sb1_lv_Kb_pos H hT hk hβ hN s (N := N)
  have hev : sb1_lv_kappa D k N hT ρ =ᶠ[𝓝 s] fun r => D.invβ * Real.log (∫ X : Whole.EucConfig d N, sb1Wf k D.invβ⁻¹ N ρ r X) +
      ((N : ℝ) / 2) * sb1c k (ρ r) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    have hrI : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
    have hcr : sb1_lv_cl' hT r = r := by unfold sb1_lv_cl'; rw [Set.projIcc_of_mem hT hrI]
    have := sb1_lv_Kb_eq H hT (k := k) (β := D.invβ⁻¹) (N := N) r
    rw [hcr] at this
    unfold sb1_lv_kappa sb1_lv_cb
    rw [this]
    simp only [sb1_lv_rb, Set.projIcc_of_mem hT hrI]
  have hK0 : (∫ X : Whole.EucConfig d N, sb1Wf k D.invβ⁻¹ N ρ s X) ≠ 0 := by
    have := sb1_lv_Kb_eq H hT (k := k) (β := D.invβ⁻¹) (N := N) s
    rw [hcl] at this
    rw [← this]; exact hKpos.ne'
  have hall := ((hKd.log hK0).const_mul D.invβ).add (hcd.const_mul ((N : ℝ) / 2))
  refine (hall.congr_deriv ?_).congr_of_eventuallyEq hev
  unfold sb1_lv_kappa' sb1_lv_Kdot sb1_lv_Kb sb1_lv_cdot
  rw [hcl]
  have e1 : Whole.gibbsNormalizer k N D.invβ⁻¹ (Whole.withDensityReal (sb1_lv_rb hT ρ s)) =
      ∫ X : Whole.EucConfig d N, sb1Wf k D.invβ⁻¹ N ρ s X := by
    have := sb1_lv_Kb_eq H hT (k := k) (β := D.invβ⁻¹) (N := N) s
    rw [hcl] at this
    exact this
  rw [e1]
  unfold sb1cdot
  rfl

end Traj

end HRS.MS.MfeConf
