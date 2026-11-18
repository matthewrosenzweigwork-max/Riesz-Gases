import HRS.MS.WadAux92

/-!
# S8.3, packet S8E-5, part 4: `x' ↦ U_t(R x')(y)` is continuous and decays

`s8e_G_cont`: continuity (uniform continuity of the weighted kernel `Q`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_G_cont (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {Cd c : ℝ} (hCd : 0 ≤ Cd)
    (h2a : S8e2a a β M ρβ Cd c) {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R)
    (hdc : IsDoublyCentered (HRS.Whole.withDensityReal ρβ) R) {t : ℝ} (ht : 1 ≤ t) (y : Euc d) :
    Continuous fun x' => s85_Ulim a β ρβ M t (R x') y := by
  rw [continuous_iff_continuousAt]
  intro x2
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨N0, hN00, hN0⟩ := s8e_Qa_bdd hR
  set κ : ℝ := Cd * Real.exp (-c * t) * jbracket y ^ M with hκ
  have hκ0 : 0 ≤ κ := mul_nonneg (mul_nonneg hCd (Real.exp_pos _).le) (Real.rpow_nonneg (s83_jb_pos y).le _)
  set P2 : ℝ := jbracket x2 ^ M with hP2
  have hP20 : 0 < P2 := Real.rpow_pos_of_pos (s83_jb_pos x2) _
  set η1 : ℝ := min 1 (ε / (4 * (κ + 1) * (N0 + 1))) with hη1
  have hη10 : 0 < η1 := lt_min one_pos (by positivity)
  set η2 : ℝ := ε / (4 * (κ + 1) * (P2 + 1)) with hη2
  have hη20 : 0 < η2 := by positivity
  obtain ⟨δ1, hδ1, hP⟩ := Metric.continuousAt_iff.1 (s85_jb_rpow_continuous (d := d) M).continuousAt η1 hη10
  obtain ⟨δ2, hδ2, hQ⟩ := Metric.uniformContinuous_iff.1 (s8e_Qa_unif hR) η2 hη20
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun x1 hx1 => ?_⟩
  have hx1a : dist x1 x2 < δ1 := lt_of_lt_of_le hx1 (min_le_left _ _)
  have hx1b : dist x1 x2 < δ2 := lt_of_lt_of_le hx1 (min_le_right _ _)
  have hPd : |jbracket x1 ^ M - P2| < η1 := by
    have := hP hx1a
    rwa [Real.dist_eq] at this
  have hP1 : jbracket x1 ^ M ≤ P2 + 1 := by
    have := (abs_lt.1 hPd).2
    have := min_le_left (1 : ℝ) (ε / (4 * (κ + 1) * (N0 + 1)))
    linarith
  have hP10 : 0 ≤ jbracket x1 ^ M := Real.rpow_nonneg (s83_jb_pos x1).le M
  have hQd : ∀ y' : Euc d, |s8e_Qa M R (x1, y') - s8e_Qa M R (x2, y')| < η2 := fun y' => by
    have := hQ (a := (x1, y')) (b := (x2, y')) (by
      rw [Prod.dist_eq]; simp [hx1b, hδ2])
    rwa [Real.dist_eq] at this
  set ε' : ℝ := (P2 + 1) * η2 + η1 * N0 with hε'
  have hwt : Wt M ε' (fun y' => R x1 y' - R x2 y') := fun y' => by
    show ‖R x1 y' - R x2 y'‖ ≤ ε' * jbracket y' ^ M
    rw [Real.norm_eq_abs, s8e_R_eq M R x1 y', s8e_R_eq M R x2 y']
    have hj := Real.rpow_nonneg (s83_jb_pos y').le M
    have e : jbracket x1 ^ M * jbracket y' ^ M * s8e_Qa M R (x1, y') -
        jbracket x2 ^ M * jbracket y' ^ M * s8e_Qa M R (x2, y') =
        jbracket y' ^ M * (jbracket x1 ^ M * (s8e_Qa M R (x1, y') - s8e_Qa M R (x2, y')) +
          (jbracket x1 ^ M - jbracket x2 ^ M) * s8e_Qa M R (x2, y')) := by ring
    rw [e, abs_mul, abs_of_nonneg hj]
    have t1 : |jbracket x1 ^ M * (s8e_Qa M R (x1, y') - s8e_Qa M R (x2, y'))| ≤ (P2 + 1) * η2 := by
      rw [abs_mul, abs_of_nonneg hP10]
      exact mul_le_mul hP1 (hQd y').le (abs_nonneg _) (by positivity)
    have t2 : |(jbracket x1 ^ M - jbracket x2 ^ M) * s8e_Qa M R (x2, y')| ≤ η1 * N0 := by
      rw [abs_mul]
      exact mul_le_mul hPd.le (hN0 _) (abs_nonneg _) hη10.le
    have := (abs_add_le _ _).trans (add_le_add t1 t2)
    calc jbracket y' ^ M * |_| ≤ jbracket y' ^ M * ε' := mul_le_mul_of_nonneg_left this hj
      _ = _ := by ring
  have hd2 := s8e_diff_pt hd ha hβ hρ hMpos h2a hR hdc ht hwt y
  have hε'b : ε' ≤ ε / (2 * (κ + 1)) := by
    have h1 : (P2 + 1) * η2 = ε / (4 * (κ + 1)) := by rw [hη2]; field_simp
    have h2 : η1 * N0 ≤ ε / (4 * (κ + 1)) := by
      have : η1 ≤ ε / (4 * (κ + 1) * (N0 + 1)) := min_le_right _ _
      calc η1 * N0 ≤ (ε / (4 * (κ + 1) * (N0 + 1))) * N0 := mul_le_mul_of_nonneg_right this hN00
        _ ≤ (ε / (4 * (κ + 1) * (N0 + 1))) * (N0 + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = ε / (4 * (κ + 1)) := by field_simp
    rw [hε']
    have : ε / (2 * (κ + 1)) = ε / (4 * (κ + 1)) + ε / (4 * (κ + 1)) := by field_simp; ring
    linarith
  have hκε : κ * ε' < ε := by
    calc κ * ε' ≤ κ * (ε / (2 * (κ + 1))) := mul_le_mul_of_nonneg_left hε'b hκ0
      _ < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith
  have hd3 : Cd * Real.exp (-c * t) * ε' * jbracket y ^ M = κ * ε' := by rw [hκ]; ring
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hd2.trans hd3.le) hκε

end HRS.MS.Wad
