import HRS.MS.S82UA5

/-!
# S8.2 A01 (S82U): pointwise bound of the triple model
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T

lemma u_uW_perm {d : ℕ} (M : ℝ) (x y z : Euc d) :
    uW M x z y = uW M x y z ∧ uW M y z x = uW M x y z := by
  unfold uW; constructor <;> ring

lemma u_tp_ge {d : ℕ} (x y z : Euc d) :
    pole x y ≤ triplePole x y z ∧ pole x z ≤ triplePole x y z ∧ pole y z ≤ triplePole x y z ∧
    pole x y * pole x z ≤ triplePole x y z ∧ pole x y * pole y z ≤ triplePole x y z ∧
    pole x z * pole y z ≤ triplePole x y z := by
  have a := u_pole_pos x y
  have b := u_pole_pos x z
  have c := u_pole_pos y z
  unfold triplePole
  have h1 : 0 ≤ pole x y * pole x z := by positivity
  have h2 : 0 ≤ pole x y * pole y z := by positivity
  have h3 : 0 ≤ pole x z * pole y z := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma u_gt_bound_W {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hA : 0 ≤ A) (hQ : PairCorrector a beta rho M A f Q)
    {p q : Euc d} (hpq : p ≠ q) {W : ℝ} (hW : Phase2S82.pairWeight M p q ≤ W) :
    ‖s82p2_gt Q p q‖ ≤ A * W * pole p q := by
  have hs1 : 1 ≤ criticalS d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    unfold criticalS; linarith
  have h := s82p2_gt_norm_le hQ p q hpq
  have hz : 0 < ‖p - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hpq)
  have hr0 : 0 < smallRadius p q := u_min_pos hz
  have hr1 : smallRadius p q ≤ 1 := min_le_left _ _
  have hrad := (s82t_radial (criticalS d) (smallRadius p q) hs1 hr0 hr1).2
  have hpole : 1 + smallRadius p q ^ (1 - criticalS d) ≤ pole p q := by unfold pole; exact hrad
  refine h.trans ?_
  have hpw0 : 0 ≤ Phase2S82.pairWeight M p q := by
    unfold Phase2S82.pairWeight
    exact mul_nonneg (u_jb_rpow_pos M p).le (u_jb_rpow_pos M q).le
  have hr2 : 0 ≤ smallRadius p q ^ (1 - criticalS d) := Real.rpow_nonneg hr0.le _
  calc A * Phase2S82.pairWeight M p q * (1 + smallRadius p q ^ (1 - criticalS d))
      ≤ A * W * (1 + smallRadius p q ^ (1 - criticalS d)) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hA) (by linarith)
    _ ≤ A * W * pole p q := by
        apply mul_le_mul_of_nonneg_left hpole (mul_nonneg hA ((hpw0.trans hW)))

lemma u_tp_sub {d : ℕ} (x y z : Euc d) :
    pole x z * (pole x y + pole y z) ≤ triplePole x y z ∧
    pole y z * (pole x y + pole x z) ≤ triplePole x y z ∧
    pole x y * (pole x z + pole y z) ≤ triplePole x y z := by
  have a := u_pole_pos x y
  have b := u_pole_pos x z
  have c := u_pole_pos y z
  unfold triplePole
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ pole x y) (by linarith : (0:ℝ) ≤ pole y z),
    mul_nonneg (by linarith : (0:ℝ) ≤ pole x y) (by linarith : (0:ℝ) ≤ pole x z),
    mul_nonneg (by linarith : (0:ℝ) ≤ pole x z) (by linarith : (0:ℝ) ≤ pole y z)]

lemma u_comb (e1 e2 e3 f1 f2 f3 f4 f5 f6 j1 j2 j3 Ce K X : ℝ) (hX : 0 ≤ X)
    (h1 : |e1| ≤ Ce * X) (h2 : |e2| ≤ Ce * X) (h3 : |e3| ≤ Ce * X)
    (g1 : |f1| ≤ K * X) (g2 : |f2| ≤ K * X) (g3 : |f3| ≤ K * X) (g4 : |f4| ≤ K * X)
    (g5 : |f5| ≤ K * X) (g6 : |f6| ≤ K * X)
    (i1 : |j1| ≤ X) (i2 : |j2| ≤ X) (i3 : |j3| ≤ X) :
    |(1 / 3 : ℝ) * ((-e1) + (-e2) + (-e3) + (f1 + f2 + f3 + f4 + f5 + f6) - j1 - j2 - j3)| ≤
      (Ce + 2 * K + 1) * X := by
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 3)]
  have := abs_le.1 h1; have := abs_le.1 h2; have := abs_le.1 h3
  have := abs_le.1 g1; have := abs_le.1 g2; have := abs_le.1 g3
  have := abs_le.1 g4; have := abs_le.1 g5; have := abs_le.1 g6
  have := abs_le.1 i1; have := abs_le.1 i2; have := abs_le.1 i3
  have key : |(-e1) + (-e2) + (-e3) + (f1 + f2 + f3 + f4 + f5 + f6) - j1 - j2 - j3| ≤
      3 * Ce * X + 6 * K * X + 3 * X := by
    rw [abs_le]; constructor <;> linarith
  nlinarith [key]

theorem uGm_bound {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hQ : PairCorrector a beta rho M A f Q)
    {Fm : Euc d → Euc d} {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x, ‖Fm x‖ ≤ K)
    {Jt : Euc d → Euc d → ℝ}
    (hJ : ∀ x y, x ≠ y → |Jt x y| ≤ A * Phase2S82.pairWeight M x y * pole x y)
    {x y z : Euc d} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    |uGm Fm (s82p2_gt Q) Jt x y z| ≤
      (HRS.Whole.movtr_sigma (criticalS d) * (2 ^ M * 2 ^ criticalS d + 6) + 2 * K + 1) *
        (A * uW M x y z * triplePole x y z) := by
  set g := s82p2_gt Q with hg
  set Ce := HRS.Whole.movtr_sigma (criticalS d) * (2 ^ M * 2 ^ criticalS d + 6) with hCe
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hσ := s82t_sigma_nonneg (criticalS d) hs0
  have hC : (0 : ℝ) ≤ 2 ^ M * 2 ^ criticalS d := by positivity
  have hCe0 : 0 ≤ Ce := mul_nonneg hσ (by linarith)
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := u_wt1 hM x y z
  obtain ⟨tp1, tp2, tp3, tp4, tp5, tp6⟩ := u_tp_ge x y z
  set Wv := uW M x y z with hWv
  set tp := triplePole x y z with htp
  have hW0 : 0 ≤ Wv := by linarith
  have htp0 : 0 ≤ tp := by linarith [u_pole_pos x y]
  set X := A * Wv * tp with hX
  have hX0 : 0 ≤ X := mul_nonneg (mul_nonneg hA hW0) htp0
  -- edges
  have e1 := u_edge_bound hd hM hA hQ hxz hxy.symm.symm hyz.symm
  have e2 := u_edge_bound hd hM hA hQ hyz hxy.symm hxz.symm
  have e3 := u_edge_bound hd hM hA hQ hxy hxz hyz
  have hperm := u_uW_perm M x y z
  rw [hperm.1] at e1
  rw [hperm.2] at e2
  rw [u_pole_symm z y] at e1
  rw [u_pole_symm y x, u_pole_symm z x] at e2
  have bnd : ∀ P : ℝ, P ≤ tp → Ce * (A * Wv * P) ≤ Ce * X := by
    intro P hP
    rw [hX]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP (mul_nonneg hA hW0)) hCe0
  have E1 : |inner ℝ (rieszKernelGrad d (criticalS d) (x - z)) (g x y - g z y)| ≤ Ce * X := by
    exact e1.trans (bnd _ (u_tp_sub x y z).1)
  have E2 : |inner ℝ (rieszKernelGrad d (criticalS d) (y - z)) (g y x - g z x)| ≤ Ce * X := by
    exact e2.trans (bnd _ (u_tp_sub x y z).2.1)
  have E3 : |inner ℝ (rieszKernelGrad d (criticalS d) (x - y)) (g x z - g y z)| ≤ Ce * X := by
    exact e3.trans (bnd _ (u_tp_sub x y z).2.2)
  -- mean force terms
  have F1 : ∀ p q : Euc d, p ≠ q → Phase2S82.pairWeight M p q ≤ Wv → pole p q ≤ tp →
      |inner ℝ (Fm p) (g p q)| ≤ K * X := by
    intro p q hpq hpw hpt
    have h1 := u_gt_bound_W hd hA hQ hpq hpw
    calc |inner ℝ (Fm p) (g p q)| ≤ ‖Fm p‖ * ‖g p q‖ := abs_real_inner_le_norm _ _
      _ ≤ K * (A * Wv * pole p q) := mul_le_mul (hK p) h1 (norm_nonneg _) hK0
      _ ≤ K * X := by
          rw [hX]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpt (mul_nonneg hA hW0)) hK0
  have pwxy : Phase2S82.pairWeight M x y ≤ Wv := w3
  have pwyx : Phase2S82.pairWeight M y x ≤ Wv := by
    unfold Phase2S82.pairWeight at *; linarith [mul_comm (jbracket x ^ M) (jbracket y ^ M)]
  have pwxz : Phase2S82.pairWeight M x z ≤ Wv := w1
  have pwzx : Phase2S82.pairWeight M z x ≤ Wv := by
    unfold Phase2S82.pairWeight at *; linarith [mul_comm (jbracket x ^ M) (jbracket z ^ M)]
  have pwyz : Phase2S82.pairWeight M y z ≤ Wv := w2
  have pwzy : Phase2S82.pairWeight M z y ≤ Wv := by
    unfold Phase2S82.pairWeight at *; linarith [mul_comm (jbracket y ^ M) (jbracket z ^ M)]
  have f1 := F1 x y hxy pwxy tp1
  have f2 := F1 y x hxy.symm pwyx (by rw [u_pole_symm]; exact tp1)
  have f3 := F1 x z hxz pwxz tp2
  have f4 := F1 z x hxz.symm pwzx (by rw [u_pole_symm]; exact tp2)
  have f5 := F1 y z hyz pwyz tp3
  have f6 := F1 z y hyz.symm pwzy (by rw [u_pole_symm]; exact tp3)
  -- J terms
  have J1 : |Jt x y| ≤ X := by
    refine (hJ x y hxy).trans ?_
    rw [hX]
    have := mul_le_mul_of_nonneg_left (tp1) (mul_nonneg hA hW0)
    calc A * Phase2S82.pairWeight M x y * pole x y ≤ A * Wv * pole x y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pwxy hA) (by linarith [u_pole_pos x y])
      _ ≤ _ := this
  have J2 : |Jt x z| ≤ X := by
    refine (hJ x z hxz).trans ?_
    rw [hX]
    have := mul_le_mul_of_nonneg_left (tp2) (mul_nonneg hA hW0)
    calc A * Phase2S82.pairWeight M x z * pole x z ≤ A * Wv * pole x z :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pwxz hA) (by linarith [u_pole_pos x z])
      _ ≤ _ := this
  have J3 : |Jt y z| ≤ X := by
    refine (hJ y z hyz).trans ?_
    rw [hX]
    have := mul_le_mul_of_nonneg_left (tp3) (mul_nonneg hA hW0)
    calc A * Phase2S82.pairWeight M y z * pole y z ≤ A * Wv * pole y z :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pwyz hA) (by linarith [u_pole_pos y z])
      _ ≤ _ := this
  have hgroup := uT_group Fm g hxy hxz hyz
  have h3 : uGm Fm g Jt x y z = (1 / 3) * ((-inner ℝ (rieszKernelGrad d (criticalS d) (x - z)) (g x y - g z y))
      + (-inner ℝ (rieszKernelGrad d (criticalS d) (y - z)) (g y x - g z x))
      + (-inner ℝ (rieszKernelGrad d (criticalS d) (x - y)) (g x z - g y z))
      + (inner ℝ (Fm x) (g x y) + inner ℝ (Fm y) (g y x) + inner ℝ (Fm x) (g x z) +
          inner ℝ (Fm z) (g z x) + inner ℝ (Fm y) (g y z) + inner ℝ (Fm z) (g z y))
      - Jt x y - Jt x z - Jt y z) := by
    unfold uGm
    rw [hgroup]; ring
  rw [h3]
  have := u_comb _ _ _ _ _ _ _ _ _ _ _ _ Ce K X hX0 E1 E2 E3 f1 f2 f3 f4 f5 f6 J1 J2 J3
  exact this

end HRS.MS.S82U
