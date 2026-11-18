import HRS.MS.SA12X4V1

/-!
# S.A.12 X5 G0: the moving weighted cell energy is bounded by the continuous weighted jet energy

`∑_y ω_y (χ_y^τ)² ≤ K ϖ` for the advected cutoffs of the flow of `-b` (`K` depends on `d, Cb, T` only), hence
`∑_y ω_y 𝓕_y(τ)(u) ≤ K J_m(u)` (the moving analogue of `sa12x4_W0_le_J`, which is the case `τ = 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near
  HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12X4

variable {d : ℕ}

theorem sa12x5_rpow_neg_le {a b c p : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hp : 0 ≤ p)
    (h : a ≤ c * b) : b ^ (-p) ≤ c ^ p * a ^ (-p) := by
  have h1 : a ^ p ≤ (c * b) ^ p := Real.rpow_le_rpow ha.le h hp
  rw [Real.mul_rpow hc.le hb.le] at h1
  rw [Real.rpow_neg hb.le, Real.rpow_neg ha.le]
  have hP1 : 0 < c ^ p := Real.rpow_pos_of_pos hc p
  have hP2 : 0 < a ^ p := Real.rpow_pos_of_pos ha p
  have hP3 : 0 < b ^ p := Real.rpow_pos_of_pos hb p
  rw [← one_div, ← one_div, mul_one_div, div_le_div_iff₀ hP3 hP2]
  nlinarith [h1]

theorem sa12x5_moving_cover_sum_le (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (m : ℕ) (Cb T : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d), IsAdvectingDrift m Cb T b →
      IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : Euc d,
      ∑' y, ENNReal.ofReal (jbracket (cellPt d y) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal (advCutoff χ Ψ τ (cellPt d y) x ^ 2) ≤
        ENNReal.ofReal K * ENNReal.ofReal (jbracket x ^ (-((d : ℝ) + 3))) := by
  classical
  obtain ⟨N, hN⟩ := sa12x4_lattice_count hd 2
  set p : ℝ := (d : ℝ) + 3 with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  set Cw : ℝ := (Real.sqrt 2 * Real.sqrt (1 + (2 : ℝ) ^ 2)) ^ p with hCw
  have hCw0 : 0 ≤ Cw := Real.rpow_nonneg (by positivity) _
  set Cg : ℝ := (2 * Real.exp (|Cb| * |T|)) ^ p with hCg
  have hCg0 : 0 ≤ Cg := Real.rpow_nonneg (by positivity) _
  refine ⟨N * (Cw * Cg), by positivity, fun b Ψ hb hΨ τ hτ x => ?_⟩
  have hT : 0 ≤ T := hτ.1.trans hτ.2
  have hfl := HRS.MS.UniqC3.uc3_flowFacts hT hb hΨ
  set q : Euc d := Function.invFun (Ψ τ) x with hq
  have hqx : Ψ τ q = x := hfl.inv_right τ hτ x
  obtain ⟨S, hSc, hS⟩ := hN q
  have hzero : ∀ y ∉ S, ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) *
      ENNReal.ofReal (advCutoff χ Ψ τ (cellPt d y) x ^ 2) = 0 := by
    intro y hy
    have hfar : ¬ ‖cellPt d y - q‖ ≤ 2 := fun h => hy (hS y h)
    have : advCutoff χ Ψ τ (cellPt d y) x = 0 := by
      unfold advCutoff
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := hχ.2.2.1 hmem
      rw [mem_ball_zero_iff, norm_sub_rev] at this
      exact hfar this.le
    rw [this]; simp
  rw [tsum_eq_sum hzero]
  have hj : ∀ v : Euc d, 0 < jbracket v := fun v => HRS.MS.Lc.lc2_jb_pos v
  have hCb : 0 ≤ Cb := HRS.MS.UniqC3.uc3_Cb_nonneg hT hb
  have hgrow : jbracket x ≤ (2 * Real.exp (|Cb| * |T|)) * jbracket q := by
    have hg := (sa12x4_flow_growth hT hb hΨ hτ q).1
    rw [hqx] at hg
    have hle1 : jbracket x ≤ 1 + ‖x‖ := by
      unfold jbracket
      rw [show (1 + ‖x‖) = Real.sqrt ((1 + ‖x‖) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg x])
    have hexp : Real.exp (Cb * τ) ≤ Real.exp (|Cb| * |T|) := by
      apply Real.exp_le_exp.2
      calc Cb * τ ≤ |Cb| * τ := mul_le_mul_of_nonneg_right (le_abs_self _) hτ.1
        _ ≤ |Cb| * |T| := mul_le_mul_of_nonneg_left (hτ.2.trans (le_abs_self T)) (abs_nonneg _)
    have hq2 := HRS.MS.Lc.lc2_le_jb q
    have hE0 : 0 < Real.exp (Cb * τ) := Real.exp_pos _
    calc jbracket x ≤ 1 + ‖x‖ := hle1
      _ ≤ (1 + ‖q‖) * Real.exp (Cb * τ) := hg
      _ ≤ (2 * jbracket q) * Real.exp (|Cb| * |T|) := by
          exact mul_le_mul hq2 hexp hE0.le (mul_nonneg (by norm_num) (hj q).le)
      _ = _ := by ring
  have hqj : jbracket q ^ (-p) ≤ Cg * jbracket x ^ (-p) :=
    sa12x5_rpow_neg_le (hj x) (hj q) (by positivity) hp0 hgrow
  have hterm : ∀ y ∈ S, ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) *
      ENNReal.ofReal (advCutoff χ Ψ τ (cellPt d y) x ^ 2) ≤
      ENNReal.ofReal (Cw * Cg) * ENNReal.ofReal (jbracket x ^ (-p)) := by
    intro y _
    by_cases hnear : ‖q - cellPt d y‖ ≤ 2
    · have hc := sa12x4_varpi_comp p hp0 2 q (cellPt d y) hnear
      have hadv1 : advCutoff χ Ψ τ (cellPt d y) x ^ 2 ≤ 1 := by
        have h := hχ.2.2.2.1 (q - cellPt d y)
        have h' : advCutoff χ Ψ τ (cellPt d y) x ∈ Icc (0 : ℝ) 1 := h
        nlinarith [h'.1, h'.2]
      have hcc : jbracket (cellPt d y) ^ (-p) ≤ Cw * (Cg * jbracket x ^ (-p)) :=
        hc.trans (mul_le_mul_of_nonneg_left hqj hCw0)
      calc ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) * ENNReal.ofReal (advCutoff χ Ψ τ (cellPt d y) x ^ 2)
          ≤ ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) * 1 := by
            gcongr
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hadv1
        _ = ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) := mul_one _
        _ ≤ ENNReal.ofReal ((Cw * Cg) * jbracket x ^ (-p)) :=
            ENNReal.ofReal_le_ofReal (by rw [mul_assoc]; exact hcc)
        _ = _ := ENNReal.ofReal_mul (by positivity)
    · have : advCutoff χ Ψ τ (cellPt d y) x = 0 := by
        unfold advCutoff
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have := hχ.2.2.1 hmem
        rw [mem_ball_zero_iff] at this
        exact hnear this.le
      rw [this]; simp
  calc ∑ y ∈ S, ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) *
        ENNReal.ofReal (advCutoff χ Ψ τ (cellPt d y) x ^ 2)
      ≤ ∑ _y ∈ S, ENNReal.ofReal (Cw * Cg) * ENNReal.ofReal (jbracket x ^ (-p)) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ≥0∞) * (ENNReal.ofReal (Cw * Cg) * ENNReal.ofReal (jbracket x ^ (-p))) := by simp
    _ ≤ (N : ℝ≥0∞) * (ENNReal.ofReal (Cw * Cg) * ENNReal.ofReal (jbracket x ^ (-p))) := by gcongr
    _ = ENNReal.ofReal (N * (Cw * Cg)) * ENNReal.ofReal (jbracket x ^ (-p)) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]

theorem sa12x5_W_le_J (hd : 1 ≤ d) (m' : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (m : ℕ) (Cb T : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d), IsAdvectingDrift m' Cb T b →
      IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T, ∀ {u : Euc d → ℝ}, ContDiff ℝ ∞ u →
      (∀ (z : Fin d → ℤ) {j : ℕ} (idx : Fin j → Fin d),
        Integrable (fun x => (advCutoff χ Ψ τ (cellPt d z) x * partialDeriv idx u x) ^ 2)) →
      ∑' y, ENNReal.ofReal (jbracket (cellPt d y) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal (cellEnergy m χ Ψ τ (cellPt d y) u) ≤ ENNReal.ofReal K * sa12x4_J m u := by
  obtain ⟨K, hK0, hK⟩ := sa12x5_moving_cover_sum_le hd χ hχ m' Cb T
  refine ⟨K, hK0, fun b Ψ hb hΨ τ hτ u hu hint => ?_⟩
  have hT : 0 ≤ T := hτ.1.trans hτ.2
  have hfl := HRS.MS.UniqC3.uc3_flowFacts hT hb hΨ
  have hci : Continuous (Function.invFun (Ψ τ)) := (hfl.contDiff_inv τ hτ).continuous
  rw [sa12x4_W_eq m χ hχ Ψ τ hci hu hint, sa12x4_J, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  calc ENNReal.ofReal (sa12x4_Z m u x) * ∑' y, ENNReal.ofReal (jbracket (cellPt d y) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal (advCutoff χ Ψ τ (cellPt d y) x ^ 2)
      ≤ ENNReal.ofReal (sa12x4_Z m u x) * (ENNReal.ofReal K * ENNReal.ofReal (jbracket x ^ (-((d : ℝ) + 3)))) := by
        gcongr; exact hK b Ψ hb hΨ τ hτ x
    _ = _ := by ring

end HRS.MH.AdjointRd.Phase2SA12X5
