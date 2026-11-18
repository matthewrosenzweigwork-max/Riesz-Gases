import HRS.MS.ToriConvAux6

/-!
# MS-TORI-DRIFTCONV, helper file 7: the level hypothesis for the coefficient family `(μ_L, ρ^t)`

`tcv_lvl_mu`: for `j ≤ m + 1`, `tcv_Lvl d j (L ↦ μ_L^t) (ρ^t)`: uniform `C^{j+2}` bounds, `D^i μ_L → D^i ρ`
locally uniformly (`D^i μ_L = Z_L^{-1} D^i ρ` on `|y| < L/4`, `Z_L → 1`), integrability and uniform tails.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriConv

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.ToriCoefA HRS.MS.ToriCoefB

variable {d : ℕ}

theorem tcv_lvl_mu (m : ℕ) (T Λ : ℝ) (s : ℝ) (ζ : Euc d → ℝ)
    (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (ρ : ℝ → Euc d → ℝ) (hρ : CoeffHypRd s m Λ T ρ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (j : ℕ) (hj : j ≤ m + 1) :
    tcv_Lvl d j (fun L => perL L fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x))
      (ρ t) := by
  classical
  choose K hK0 hK using fun i : ℕ => tca_bdd_iter ζ hζ i
  have hprob : HRS.Whole.IsProbDensity (ρ t) := hρ.prob t ht
  obtain ⟨hMC, hWfin, hWle⟩ := hρ.regular.1 t ht
  have hWle' : (weightedSupE (m + 3) ((d : ℝ) + 3) (ρ t)).toReal ≤ |Λ| := by
    have hcb0 : 0 ≤ cbNorm (m + 3) (ρ t) :=
      Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun z => norm_nonneg _
    have := le_abs_self Λ
    linarith
  have hWk : ∀ k : ℕ, k ≤ m + 3 → ∀ w : Euc d,
      jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ k (ρ t) w‖ ≤ (d : ℝ) ^ k * |Λ| := fun k hk w =>
    (tca_weight_le (m + 3) ((d : ℝ) + 3) (ρ t) hWfin.ne k hk w).trans
      (mul_le_mul_of_nonneg_left hWle' (pow_nonneg (Nat.cast_nonneg d) _))
  have hρB : ∀ y : Euc d, |ρ t y| ≤ |Λ| * tca_g y := by
    intro y
    exact tca_abs_le_weight (ρ t) |Λ| (fun y' => by
      have := hWk 0 (Nat.zero_le _) y'
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, one_mul] at this
      exact this) y
  have hρcd : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (ρ t) := hMC.1
  obtain ⟨N, hN⟩ := tca_tail (d := d) (1 / (2 * (|Λ| + 1))) (by positivity)
  have hBε : |Λ| * (1 / (2 * (|Λ| + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg Λ]
  have hZ : ∀ L : ℝ, max 1 (4 * (N : ℝ)) ≤ L → 1 / 2 ≤ ∫ y, ζ (L⁻¹ • y) * ρ t y := by
    intro L hL
    have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
    have hL4 : (N : ℝ) ≤ L / 4 := by
      have := (le_max_right _ _).trans hL
      linarith
    exact tca_Z_ge hζ (ρ t) hprob |Λ| (abs_nonneg _) hρB L (by linarith) N hL4 _ hN hBε
  have hc : ∀ L : ℝ, max 1 (4 * (N : ℝ)) ≤ L →
      0 < (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ ∧ (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ ≤ 2 := by
    intro L hL
    have := hZ L hL
    refine ⟨inv_pos.2 (by linarith), ?_⟩
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    linarith
  have hpkg : ∀ L : ℝ, max 1 (4 * (N : ℝ)) ≤ L →
      ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞)
        (perL L fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x)) ∧
      ∀ i ≤ m + 3, ∀ y : Euc d,
        ‖iteratedFDeriv ℝ i
          (perL L fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x)) y‖ ≤
          2 * tca_S d K |Λ| i := fun L hL => by
    have h := tca_mu_package hζ L ((le_max_left _ _).trans hL) (m + 3) (ρ t) hρcd K hK hK0 |Λ|
      (abs_nonneg _) hWk _ (hc L hL).1 (hc L hL).2
    exact ⟨h.1, h.2.1⟩
  -- constants
  have hS0 : ∀ i, 0 ≤ tca_S d K |Λ| i := fun i => tca_S_nonneg d K hK0 |Λ| (abs_nonneg _) i
  obtain ⟨SS, hSS⟩ : ∃ SS : ℝ, SS = ∑ i ∈ Finset.range (m + 4), 2 * tca_S d K |Λ| i := ⟨_, rfl⟩
  obtain ⟨SR, hSR⟩ : ∃ SR : ℝ, SR = ∑ i ∈ Finset.range (m + 4), (d : ℝ) ^ i * |Λ| := ⟨_, rfl⟩
  have hSS0 : 0 ≤ SS := by
    rw [hSS]; exact Finset.sum_nonneg fun i _ => by linarith [hS0 i]
  have hSR0 : 0 ≤ SR := by
    rw [hSR]; exact Finset.sum_nonneg fun i _ => by positivity
  have hSSle : ∀ i, i ≤ m + 3 → 2 * tca_S d K |Λ| i ≤ SS := fun i hi => by
    rw [hSS]
    exact Finset.single_le_sum (f := fun i => 2 * tca_S d K |Λ| i)
      (fun i _ => by linarith [hS0 i]) (Finset.mem_range.2 (by omega))
  have hSRle : ∀ i, i ≤ m + 3 → (d : ℝ) ^ i * |Λ| ≤ SR := fun i hi => by
    rw [hSR]
    exact Finset.single_le_sum (f := fun i => (d : ℝ) ^ i * |Λ|)
      (fun i _ => by positivity) (Finset.mem_range.2 (by omega))
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, Bd = SS + SR := ⟨_, rfl⟩
  have hBd0 : 0 ≤ Bd := by rw [hBd]; linarith
  have hSSBd : ∀ i, i ≤ m + 3 → 2 * tca_S d K |Λ| i ≤ Bd := fun i hi => by
    rw [hBd]; linarith [hSSle i hi]
  have hρD : ∀ i, i ≤ m + 3 → ∀ y : Euc d, ‖iteratedFDeriv ℝ i (ρ t) y‖ ≤ (d : ℝ) ^ i * |Λ| := by
    intro i hi y
    have hjb1 : 1 ≤ jbracket y ^ ((d : ℝ) + 3) :=
      Real.one_le_rpow (tca_one_le_jbracket y) (by positivity)
    exact (le_mul_of_one_le_left (norm_nonneg _) hjb1).trans (hWk i hi y)
  have hρBd : ∀ i, i ≤ m + 3 → ∀ y : Euc d, ‖iteratedFDeriv ℝ i (ρ t) y‖ ≤ Bd := fun i hi y =>
    (hρD i hi y).trans ((hSRle i hi).trans (by rw [hBd]; linarith))
  have hρG : ∀ i, i ≤ m + 3 → ∀ y : Euc d, ‖iteratedFDeriv ℝ i (ρ t) y‖ ≤ Bd * tca_g y := by
    intro i hi y
    have h1 : ‖iteratedFDeriv ℝ i (ρ t) y‖ ≤ ((d : ℝ) ^ i * |Λ|) * tca_g y := by
      have := tca_abs_le_weight (fun y => ‖iteratedFDeriv ℝ i (ρ t) y‖) ((d : ℝ) ^ i * |Λ|)
        (fun y' => by rw [abs_norm]; exact hWk i hi y') y
      rwa [abs_norm] at this
    have h2 : (d : ℝ) ^ i * |Λ| ≤ Bd := (hSRle i hi).trans (by rw [hBd]; linarith)
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (tca_g_nonneg y))
  have hρcont : ∀ i, i ≤ m + 3 → Continuous fun y : Euc d => ‖iteratedFDeriv ℝ i (ρ t) y‖ := by
    intro i hi
    exact (hρcd.continuous_iteratedFDeriv (m := i) (by exact_mod_cast hi)).norm
  refine ⟨max 1 (4 * (N : ℝ)), Bd, le_max_left _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L hL
    exact (hpkg L hL).1.of_le (by exact_mod_cast (by omega : j + 2 ≤ m + 3))
  · exact hρcd.of_le (by exact_mod_cast (by omega : j + 2 ≤ m + 3))
  · intro L hL i hi y
    exact ((hpkg L hL).2 i (by omega) y).trans (hSSBd i (by omega))
  · intro i hi y
    exact hρBd i (by omega) y
  · intro i hi
    refine Integrable.mono' (tca_g_integrable.const_mul Bd) (hρcont i (by omega)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_norm]
    exact hρG i (by omega) y
  · -- locally uniform convergence
    intro i hi K' hK' η hη
    obtain ⟨RK, hRK⟩ := hK'.isBounded.exists_norm_le
    have hε'pos : 0 < η / (2 * (|Λ| + 1) * (Bd + 1)) := by positivity
    obtain ⟨N', hN'⟩ := tca_tail (d := d) _ hε'pos
    refine ⟨max (max 1 (4 * (N : ℝ))) (max (4 * (N' : ℝ)) (4 * RK + 1)), fun L hL y hy => ?_⟩
    have hLN : max 1 (4 * (N : ℝ)) ≤ L := (le_max_left _ _).trans hL
    have hL1 : 1 ≤ L := (le_max_left _ _).trans hLN
    have hL0 : 0 < L := by linarith
    have hLN' : (N' : ℝ) ≤ L / 4 := by
      have := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
      linarith
    have hyL : ‖y‖ < L / 4 := by
      have h1 := hRK y hy
      have := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
      linarith
    have hρi : ContDiff ℝ (i : WithTop ℕ∞) (ρ t) :=
      hρcd.of_le (by exact_mod_cast (by omega : i ≤ m + 3))
    show ‖iteratedFDeriv ℝ i
      (perL L fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x)) y -
        iteratedFDeriv ℝ i (ρ t) y‖ ≤ η
    rw [tcv_mu_near hζ hL0 i (ρ t) hρi _ y hyL]
    have hZ1 := hZ L hLN
    have hZc := tcv_Z_close hζ (ρ t) hprob |Λ| (abs_nonneg _) hρB L hL0 N' hLN' _ hN'
    generalize (∫ y, ζ (L⁻¹ • y) * ρ t y) = Z at hZ1 hZc
    have h1 : Z⁻¹ • iteratedFDeriv ℝ i (ρ t) y - iteratedFDeriv ℝ i (ρ t) y =
        (Z⁻¹ - 1) • iteratedFDeriv ℝ i (ρ t) y := by rw [sub_smul, one_smul]
    rw [h1, norm_smul, Real.norm_eq_abs]
    have h2 := tcv_inv_sub hZ1
    have h3 : |Z⁻¹ - 1| ≤ 2 * (|Λ| * (η / (2 * (|Λ| + 1) * (Bd + 1)))) := by
      have := mul_le_mul_of_nonneg_left hZc (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    have h4 := hρBd i (by omega) y
    have hΛ1 : (|Λ| + 1) ≠ 0 := by positivity
    have hB1 : (Bd + 1) ≠ 0 := by positivity
    have e : 2 * (|Λ| * (η / (2 * (|Λ| + 1) * (Bd + 1)))) * Bd =
        η * ((|Λ| / (|Λ| + 1)) * (Bd / (Bd + 1))) := by
      field_simp
    have hq1 : |Λ| / (|Λ| + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hq2 : Bd / (Bd + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hq : (|Λ| / (|Λ| + 1)) * (Bd / (Bd + 1)) ≤ 1 :=
      mul_le_one₀ hq1 (by positivity) hq2
    calc |Z⁻¹ - 1| * ‖iteratedFDeriv ℝ i (ρ t) y‖
        ≤ (2 * (|Λ| * (η / (2 * (|Λ| + 1) * (Bd + 1))))) * Bd :=
          mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
      _ = η * ((|Λ| / (|Λ| + 1)) * (Bd / (Bd + 1))) := e
      _ ≤ η * 1 := mul_le_mul_of_nonneg_left hq hη.le
      _ = η := mul_one η
  · -- tails
    intro i hi K' hK' ε hε
    obtain ⟨RK, hRK⟩ := hK'.isBounded.exists_norm_le
    have hD2 : (0 : ℝ) < 2 ^ d * (Bd + 1) := by positivity
    have hε'' : 0 < ε / (2 ^ d * (Bd + 1)) := div_pos hε hD2
    obtain ⟨N'', hN''⟩ := tca_tail (d := d) _ hε''
    refine ⟨(N'' : ℝ) + RK, fun R hR => ⟨max (2 * R) (max 1 (4 * (N : ℝ))), fun L hL x hx => ?_⟩⟩
    have hL2R : 2 * R ≤ L := (le_max_left _ _).trans hL
    have hLN : max 1 (4 * (N : ℝ)) ≤ L := (le_max_right _ _).trans hL
    have hL1 : 1 ≤ L := (le_max_left _ _).trans hLN
    have hL0 : 0 < L := by linarith
    have hx1 := hRK x hx
    have hsub : (N'' : ℝ) ≤ R - ‖x‖ := by linarith
    have hmono := tcv_tail_mono (d := d) hsub
    have hI0 : 0 ≤ ∫ u in {u : Euc d | R - ‖x‖ ≤ ‖u‖}, tca_g u :=
      setIntegral_nonneg (measurableSet_le measurable_const measurable_norm)
        fun u _ => tca_g_nonneg u
    have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    have hfin : 2 ^ d * Bd * ∫ u in {u : Euc d | R - ‖x‖ ≤ ‖u‖}, tca_g u ≤ ε := by
      calc 2 ^ d * Bd * ∫ u in {u : Euc d | R - ‖x‖ ≤ ‖u‖}, tca_g u
          ≤ 2 ^ d * Bd * (ε / (2 ^ d * (Bd + 1))) :=
            mul_le_mul_of_nonneg_left (hmono.trans hN'') (by positivity)
        _ ≤ 2 ^ d * (Bd + 1) * (ε / (2 ^ d * (Bd + 1))) := by
            have : 0 ≤ ε / (2 ^ d * (Bd + 1)) := hε''.le
            nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ d) this]
        _ = ε := by field_simp
    constructor
    · have hc' := hc L hLN
      have hvan : ∀ y : Euc d, L / 3 ≤ ‖y‖ →
          (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • y) * ρ t y) = 0 := by
        intro y hy
        rw [tca_zeta_far_val hζ L hL0 y hy, zero_mul, mul_zero]
      have hB : ∀ w : Euc d, ‖iteratedFDeriv ℝ i
          (fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x)) w‖ ≤ Bd * tca_g w := by
        intro w
        refine (tcb_f_weighted hζ L hL1 (m + 3) (ρ t) hρcd K hK hK0 |Λ| (abs_nonneg _) hWk _
          hc'.1 hc'.2 i (by omega) w).trans ?_
        exact mul_le_mul_of_nonneg_right (hSSBd i (by omega)) (tca_g_nonneg w)
      have := tcv_cube_tail hL0
        (fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x)) hvan i Bd hB x R
        (by linarith)
      exact this.trans hfin
    · have := tcv_euc_tail (fun w => ‖iteratedFDeriv ℝ i (ρ t) w‖) Bd hBd0 (hρG i (by omega))
        (fun w => norm_nonneg _) (hρcont i (by omega)) x R
      refine this.trans ?_
      refine le_trans ?_ hfin
      nlinarith [mul_nonneg (sub_nonneg.2 h2d) (mul_nonneg hBd0 hI0)]

end HRS.MS.ToriConv
