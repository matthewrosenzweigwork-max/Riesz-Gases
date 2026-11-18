import HRS.MC.E214K4

/-!
# Packet E214K, part 5: `vprop_compare_modes_proof` (P2a, basis-vector form of M3)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214K

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDI

variable {d : ℕ}

theorem fc_sub' {a : ℝ} (A B : NegSobolev d a) (l : NonzeroLattice d) :
    NegSobolev.fourierCoeff (A - B) l = NegSobolev.fourierCoeff A l - NegSobolev.fourierCoeff B l := by
  unfold NegSobolev.fourierCoeff
  have : NegSobolev.coord (A - B) l = NegSobolev.coord A l - NegSobolev.coord B l := rfl
  rw [this]; ring

/-- The Fourier coefficients of the dual evolution applied to a basis vector. -/
theorem fc_vev_modeVec {a : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (V : ℝ → ℝ → NegSobolev d a →L[ℝ] NegSobolev d a) (hdual : IsDualEvolution D ρ a V)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (k l : NonzeroLattice d) :
    NegSobolev.fourierCoeff (V t u (modeVec a k)) l =
      Torus.funRealCoeff (propagator D ρ u t (Torus.realMode l)) k := by
  rw [← q38b_eval_realMode, hdual u t hu hut _ _ (HRS.Uniform.Q48b.q48b_isSmooth_realMode l),
    HRS.MC.Sec7.S7PIDM.S7PIDM_eval_modeVec]

theorem modeVec_eq_embed {j1 m : ℝ} (hjm : j1 ≤ m) (k : NonzeroLattice d) :
    modeVec m k = NegSobolev.embed m (modeVec j1 k) := by
  show NegSobolev.ofSeq m (fun j : NonzeroLattice d => if j = k then (1 : ℝ) else 0) =
    NegSobolev.ofSeq m (NegSobolev.fourierCoeff (modeVec j1 k))
  congr 1
  funext l
  rw [HRS.MC.Sec7.S7PIDM.S7PIDM_fc_modeVec]

/-- **P2a, basis-vector form of M3.** -/
theorem vprop_compare_modes_proof {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} :
    ∃ C c κ : ℝ, 0 < C ∧ 0 < c ∧ 0 < κ ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ k : NonzeroLattice d,
      ‖Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t u (HRS.MC.Sec7.PID.modeVec m k) -
          Vprop (regime S β₀ hE).D (fun _ => (regime S β₀ hE).ρβ) m t u
            (HRS.MC.Sec7.PID.modeVec m k)‖ ≤
        C * Real.exp (-c * (t - u)) * Real.exp (-κ * u) * ‖HRS.MC.Sec7.PID.modeVec (d := d) m k‖ := by
  have hth := regime_thermal S β₀ hE
  have hrm : rLvl d ≤ m := rLvl_le hE
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast S.hd
  have hrl : rLvl d = 2 * (d : ℝ) + 6 := rfl
  have hm0 : 0 ≤ (m - 1) / 2 := by rw [hrl] at hrm; linarith
  set n : ℕ := ⌊(m - 1) / 2⌋₊ with hn
  have hn1 : (n : ℝ) ≤ (m - 1) / 2 := Nat.floor_le hm0
  have hn2 : (m - 1) / 2 < n + 1 := Nat.lt_floor_add_one _
  set j1 : ℕ := 2 * n with hj1
  set j2 : ℕ := 2 * n + 4 with hj2
  have hj1r : (j1 : ℝ) = 2 * n := by rw [hj1]; push_cast; ring
  have hj2r : (j2 : ℝ) = 2 * n + 4 := by rw [hj2]; push_cast; ring
  have hj1m : (j1 : ℝ) < m := by rw [hj1r]; linarith
  have hmj2 : m < (j2 : ℝ) := by rw [hj2r]; linarith
  have hj1d : (d : ℝ) / 2 + 4 < j1 := by rw [hj1r]; rw [hrl] at hrm; linarith
  have hj2d : (d : ℝ) / 2 + 4 < j2 := by rw [hj2r]; rw [hrl] at hrm; linarith
  have hev1 : Even j1 := even_two_mul n
  have hev2 : Even j2 := ⟨n + 2, by rw [hj2]; ring⟩
  obtain ⟨C1, c1, κ1, hC1, hc1, hκ1, hcmp1⟩ := compare_level_at S hth (j1 : ℝ) j1 hev1 hj1d rfl
  obtain ⟨C2, c2, κ2, hC2, hc2, hκ2, hcmp2⟩ := compare_level_at S hth (j2 : ℝ) j2 hev2 hj2d rfl
  obtain ⟨VR1, Wc1, hVR1, hWc1⟩ := exists_dual S hth (j1 : ℝ)
  obtain ⟨VR2, Wc2, hVR2, hWc2⟩ := exists_dual S hth (j2 : ℝ)
  refine ⟨max C1 C2, min c1 c2, min κ1 κ2, lt_max_of_lt_left hC1, lt_min hc1 hc2, lt_min hκ1 hκ2,
    fun u t hu hut k => ?_⟩
  set M : ℝ := max C1 C2 * Real.exp (-(min c1 c2) * (t - u)) * Real.exp (-(min κ1 κ2) * u) with hM
  have hM0 : 0 ≤ M := by positivity
  have hx : 0 ≤ t - u := sub_nonneg.2 hut
  have hmono : ∀ (Ci ci κi : ℝ), 0 ≤ Ci → Ci ≤ max C1 C2 → min c1 c2 ≤ ci → min κ1 κ2 ≤ κi →
      Ci * Real.exp (-ci * (t - u)) * Real.exp (-κi * u) ≤ M := by
    intro Ci ci κi hCi hC hc hκ
    have e1 : Real.exp (-ci * (t - u)) ≤ Real.exp (-(min c1 c2) * (t - u)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have e2 : Real.exp (-κi * u) ≤ Real.exp (-(min κ1 κ2) * u) :=
      Real.exp_le_exp.2 (by nlinarith)
    exact mul_le_mul (mul_le_mul hC e1 (Real.exp_pos _).le (hCi.trans hC)) e2 (Real.exp_pos _).le
      (by positivity)
  have hb1 : ‖VR1 t u - Wc1 t u‖ ≤ M :=
    (hcmp1 u t hu hut VR1 Wc1 hVR1 hWc1).trans
      (hmono C1 c1 κ1 hC1.le (le_max_left _ _) (min_le_left _ _) (min_le_left _ _))
  have hb2 : ‖VR2 t u - Wc2 t u‖ ≤ M :=
    (hcmp2 u t hu hut VR2 Wc2 hVR2 hWc2).trans
      (hmono C2 c2 κ2 hC2.le (le_max_right _ _) (min_le_right _ _) (min_le_right _ _))
  have hG1n : ‖(VR1 t u - Wc1 t u) (modeVec (j1 : ℝ) k)‖ ≤ M * Lattice.jp k.1 ^ (-(j1 : ℝ)) := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [S7PIDI_norm_modeVec]
    exact mul_le_mul_of_nonneg_right hb1 (Real.rpow_nonneg (Torus.jp_pos _).le _)
  have hG2n : ‖(VR2 t u - Wc2 t u) (modeVec (j2 : ℝ) k)‖ ≤ M * Lattice.jp k.1 ^ (-(j2 : ℝ)) := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [S7PIDI_norm_modeVec]
    exact mul_le_mul_of_nonneg_right hb2 (Real.rpow_nonneg (Torus.jp_pos _).le _)
  have hX : Vprop S.dyn S.ρ m t u (modeVec m k) -
      Vprop S.dyn (fun _ => (regime S β₀ hE).ρβ) m t u (modeVec m k) =
        NegSobolev.embed m ((VR1 t u - Wc1 t u) (modeVec (j1 : ℝ) k)) := by
    rw [modeVec_eq_embed hj1m.le k, vprop_embed hj1m.le S.dyn S.ρ VR1 hVR1 hu hut,
      vprop_embed hj1m.le S.dyn (fun _ => (regime S β₀ hE).ρβ) Wc1 hWc1 hu hut,
      ← HRS.MD.EQGaussLift.eqgl_embed_sub hj1m.le, sub_apply]
  have hfc2 : ∀ l, NegSobolev.fourierCoeff ((VR2 t u - Wc2 t u) (modeVec (j2 : ℝ) k)) l =
      NegSobolev.fourierCoeff ((VR1 t u - Wc1 t u) (modeVec (j1 : ℝ) k)) l := by
    intro l
    rw [sub_apply, sub_apply, fc_sub', fc_sub', fc_vev_modeVec _ _ VR2 hVR2 hu hut,
      fc_vev_modeVec _ _ Wc2 hWc2 hu hut, fc_vev_modeVec _ _ VR1 hVR1 hu hut,
      fc_vev_modeVec _ _ Wc1 hWc1 hu hut]
  have hmain := norm_interp (Torus.jp_pos k.1) hM0 hj1m hmj2
    (X := Vprop S.dyn S.ρ m t u (modeVec m k) -
      Vprop S.dyn (fun _ => (regime S β₀ hE).ρβ) m t u (modeVec m k))
    (G1 := (VR1 t u - Wc1 t u) (modeVec (j1 : ℝ) k)) (G2 := (VR2 t u - Wc2 t u) (modeVec (j2 : ℝ) k))
    (fun l => by rw [hX, HRS.MD.EQGaussLift.eqgl_fourierCoeff_embed hj1m.le]) hfc2 hG1n hG2n
  show ‖Vprop S.dyn S.ρ m t u (modeVec m k) -
      Vprop S.dyn (fun _ => (regime S β₀ hE).ρβ) m t u (modeVec m k)‖ ≤ M * ‖modeVec (d := d) m k‖
  rw [S7PIDI_norm_modeVec]
  exact hmain

end HRS.MC.E214K

end
