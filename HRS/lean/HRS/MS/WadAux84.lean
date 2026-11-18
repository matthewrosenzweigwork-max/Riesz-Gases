import HRS.MS.WadAux83

/-!
# S8.3, packet S8E-3, part 5: Lipschitz bound for classical solutions in terms of the datum

`s8e_diff_adm`: for the frozen classical solution `f` with datum `φ` (`Wt M Φ0 φ`, `|φ(y+z) - φ(y)| ≤ Φ1 ‖z‖ ⟨y⟩^M`), `t ≤ T`, and
`‖ζ‖ < 1/8`,  `|f_0(x+ζ) - f_0(x)| ≤ K (Φ0 + Φ1) ‖ζ‖ ⟨x⟩^M`, `K = K(d,a,β,T,M)`.  (A priori estimate for the
flow-shifted difference with source `Bop_{ρ(·+z)-ρ}(f_s(·+z))` of size `‖ζ‖ Θ_f ρ_λ(s)`.)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_diff_adm (hd : 2 ≤ d) {a β T M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T) (hM : 0 ≤ M)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ lam K : ℝ, 0 ≤ lam ∧ 0 ≤ K ∧ ∀ {t Φ0 Φ1 : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}, 0 < t → t ≤ T →
      IsClassicalAdjointW (critCoeff d a β ρβ) t φ f → Wt M Φ0 φ →
      0 ≤ Φ1 → (∀ (y z : Euc d), ‖z‖ < 1 / 4 → |φ (y + z) - φ y| ≤ Φ1 * ‖z‖ * jbracket y ^ M) →
      ∀ ζ : Euc d, ‖ζ‖ < 1 / 8 →
      S84Adm lam t M (s8e_u a ζ f) (K * (Φ0 + Φ1) * ‖ζ‖) ∧ ∀ r ∈ Set.Icc 0 t, ∀ y : Euc d,
        |s8e_u a ζ f r y| ≤ K * (Φ0 + Φ1) * ‖ζ‖ * jbracket y ^ M := by
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have hg := s84_thermal_gaussReg hd ha hβ hρ
  obtain ⟨lam₀, K₀, hlam₀, hK₀, hK₀adm⟩ := s8d_apriori_adm hd ha hν hT hM hg
  obtain ⟨CB, hCB0, hCB⟩ := s84_B_bound hd hg hM
  obtain ⟨Cρ, c', hCρ, hc', hρd⟩ := s8e_thermal_diff hd ha hβ hρ
  obtain ⟨Kc, hKc0, hKc⟩ := s8e_B_bound_unif hd hc' hM
  obtain ⟨lam, K, hlam, hK, hKgen⟩ := s8e_apriori_gen (d := d) ha hν hT hM (cB := 2 * CB) (by positivity)
  set E0 : ℝ := Real.exp (lam₀ * T) with hE0
  have hE00 : 0 < E0 := Real.exp_pos _
  refine ⟨lam, K * (1 + Kc * Cρ * (2 * (3 ^ M * (K₀ * E0)))), hlam, by positivity, ?_⟩
  intro t Φ0 Φ1 φ f ht htT hf hφ hΦ1 hLip ζ hζ
  have hΦ0 : 0 ≤ Φ0 := hφ.nonneg
  have hζ4 : ‖ζ‖ < 1 / 4 := by linarith
  have sol := s84_sol_of_classical a β ha hβ ρβ ht hf hφ
  have hadmw := hK₀adm ht htT sol
  have hΘw : 0 ≤ K₀ * Φ0 := mul_nonneg hK₀ hΦ0
  obtain ⟨B1, B2, hB⟩ := sol.bdd
  have hC2 : ∀ s ∈ Set.Icc 0 t, s84_C2b (f s) (max B1 B2) := fun s hs =>
    ⟨sol.c2 s hs, fun y => ⟨(hB s hs y).1.trans (le_max_left _ _), (hB s hs y).2.trans (le_max_right _ _)⟩⟩
  -- the datum of the shifted difference
  have hΦu : Wt M (Φ1 * ‖ζ‖) (s8e_u a ζ f t) := fun y => by
    unfold s8e_u
    rw [hf.terminal]
    have hzt : ‖s8e_zs a ζ t‖ ≤ ‖ζ‖ := s8e_zs_norm ha.le ht.le ζ
    rw [Real.norm_eq_abs]
    refine (hLip y _ (lt_of_le_of_lt hzt hζ4)).trans ?_
    have hj := Real.rpow_nonneg (s83_jb_pos y).le M
    calc Φ1 * ‖s8e_zs a ζ t‖ * jbracket y ^ M ≤ Φ1 * ‖ζ‖ * jbracket y ^ M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzt hΦ1) hj
      _ = _ := rfl
  have hS := s8e_shift_sol ha hν hM ht sol hζ4 hΦu
  set Ex : ℝ := Kc * Cρ * ‖ζ‖ * (2 * (3 ^ M * (K₀ * Φ0 * E0))) with hEx
  have hEx0 : 0 ≤ Ex := by rw [hEx]; positivity
  have hq : ∀ Θ : ℝ, 0 ≤ Θ → S84Adm lam t M (s8e_u a ζ f) Θ → ∀ s ∈ Set.Ico 0 t,
      Wt M ((2 * CB * Θ + Ex) * s84_wt lam t s)
        ((fun s y => s84_Bop ρβ (f s) (y + s8e_zs a ζ s) - s84_Bop ρβ (f s) y) s) :=
    fun Θ hΘ hadm s hs => by
      have := s8e_qu_wt hd hg hM hCB hKc hKc0 hCρ hρd (a := a) (T := T) (lam₀ := lam₀) (lam := lam)
        (ζ := ζ) (f := f) hC2 ha.le (by linarith) hadmw hΘw htT hlam hlam₀ hΘ hadm hs
      convert this using 3
  obtain ⟨hadm, hbd⟩ := hKgen ht htT hEx0 hS hq
  have hn := norm_nonneg ζ
  have hfin : Φ1 * ‖ζ‖ + Ex ≤ (1 + Kc * Cρ * (2 * (3  ^ M * (K₀ * E0)))) * (Φ0 + Φ1) * ‖ζ‖ := by
    rw [hEx]
    have h1 : 0 ≤ Kc * Cρ * (2 * (3 ^ M * (K₀ * E0))) := by positivity
    nlinarith [mul_nonneg (mul_nonneg h1 hn) hΦ1, mul_nonneg hn hΦ0]
  have hKfin : K * (Φ1 * ‖ζ‖ + Ex) ≤
      K * (1 + Kc * Cρ * (2 * (3 ^ M * (K₀ * E0)))) * (Φ0 + Φ1) * ‖ζ‖ := by
    calc K * (Φ1 * ‖ζ‖ + Ex) ≤ K * ((1 + Kc * Cρ * (2 * (3 ^ M * (K₀ * E0)))) * (Φ0 + Φ1) * ‖ζ‖) :=
          mul_le_mul_of_nonneg_left hfin hK
      _ = _ := by ring
  refine ⟨hadm.mono hKfin, fun r hr y => ?_⟩
  have hj := Real.rpow_nonneg (s83_jb_pos y).le M
  exact (hbd r hr y).trans (mul_le_mul_of_nonneg_right hKfin hj)

theorem s8e_diff_bound (hd : 2 ≤ d) {a β T M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T) (hM : 0 ≤ M)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t Φ0 Φ1 : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}, 0 < t → t ≤ T →
      IsClassicalAdjointW (critCoeff d a β ρβ) t φ f → Wt M Φ0 φ →
      0 ≤ Φ1 → (∀ (y z : Euc d), ‖z‖ < 1 / 4 → |φ (y + z) - φ y| ≤ Φ1 * ‖z‖ * jbracket y ^ M) →
      ∀ ζ : Euc d, ‖ζ‖ < 1 / 8 → ∀ x : Euc d,
      |f 0 (x + ζ) - f 0 x| ≤ K * (Φ0 + Φ1) * ‖ζ‖ * jbracket x ^ M := by
  obtain ⟨lam, K, -, hK, h⟩ := s8e_diff_adm hd ha hβ hT hM hρ
  refine ⟨K, hK, fun {t Φ0 Φ1 φ f} ht htT hf hφ hΦ1 hLip ζ hζ x => ?_⟩
  have := (h ht htT hf hφ hΦ1 hLip ζ hζ).2 0 ⟨le_rfl, ht.le⟩ x
  have hz0 : s8e_zs a ζ 0 = ζ := by simp [s8e_zs]
  have hu0 : s8e_u a ζ f 0 x = f 0 (x + ζ) - f 0 x := by unfold s8e_u; rw [hz0]
  rwa [hu0] at this

end HRS.MS.Wad
