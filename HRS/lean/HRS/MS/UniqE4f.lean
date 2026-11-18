import HRS.MS.UniqE4e

/-!
# E4 of `UniqPlan.md`, part 6: the bound `|∫ [η_ε, ρ'] F · H| ≤ ε C (…)`

* `e4_comm_far`  : far region `{2R ≤ |y - c₀|}`, via `n0_far_pairing_H` and the decaying commutator bound.
* `e4_comm_near` : near region `B̄(c₀, 2R)`, via Cauchy–Schwarz (weighted), M3 and Young (`e4_kcd_near`).
* `e4_comm_integral_bound` : the total.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE4

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3 HRS.MS.UniqE3 HRS.MS.UniqN0

variable {d : ℕ}

theorem e4_jbracket_le (x : Euc d) : jbracket x ≤ 1 + ‖x‖ := by
  unfold jbracket
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg x]

theorem e4_comm_far {s : ℝ} (hs0 : 0 ≤ s) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (B : ℝ), 0 ≤ B → ∀ (F : Euc d → ℝ),
      LocMass B F → ∀ (ρ : Euc d → ℝ), ContDiff ℝ 1 ρ →
      (∀ y, ‖fderiv ℝ ρ y‖ ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) →
      ∀ (i : Fin d) (c0 : Euc d) (R : ℝ) (ψ : Euc d → ℝ), 1 ≤ R → ContDiff ℝ 1 ψ →
      HasCompactSupport ψ → Function.support ψ ⊆ closedBall c0 R →
      ∫⁻ y in {y : Euc d | 2 * R ≤ ‖y - c0‖}, ‖comm d ε ρ F y * kernelConvDeriv d s i ψ y‖ₑ ≤
        ENNReal.ofReal (C * ε * A * (∫ x, |ψ x|) * B) := by
  obtain ⟨C1, hC1, hC1'⟩ := n0_far_pairing_H d hs0
  obtain ⟨N, hN⟩ := e4_locMass_moll_abs d
  set κ : ℝ := (d : ℝ) + 3 with hκ
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  refine ⟨C1 * 2 ^ κ * Real.sqrt N, by positivity, ?_⟩
  intro ε hε hε1 B hB F hF ρ hρ hρ1 i c0 R ψ hR hψ hψc hsupp
  set Λ : ℝ := ε * (A * 2 ^ κ) with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  set a : Euc d → ℝ := fun y => Λ * (1 + ‖y‖) ^ (-κ) with ha
  have ha0 : ∀ y, 0 ≤ a y := fun y => by positivity
  have hf := hN ε hε hε1 B hB F hF
  have hja : ∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ := by
    intro x
    rw [abs_of_nonneg (ha0 x)]
    have hj : 0 ≤ jbracket x := by unfold jbracket; positivity
    have h1 : jbracket x ^ κ ≤ (1 + ‖x‖) ^ κ := Real.rpow_le_rpow hj (e4_jbracket_le x) hκ0
    have h2 : (1 + ‖x‖) ^ κ * (1 + ‖x‖) ^ (-κ) = 1 := by
      rw [← Real.rpow_add (by positivity)]; simp
    calc jbracket x ^ κ * (Λ * (1 + ‖x‖) ^ (-κ))
        ≤ (1 + ‖x‖) ^ κ * (Λ * (1 + ‖x‖) ^ (-κ)) := by gcongr
      _ = Λ * ((1 + ‖x‖) ^ κ * (1 + ‖x‖) ^ (-κ)) := by ring
      _ = Λ := by rw [h2, mul_one]
  have key := hC1' Λ (Real.sqrt N * B) c0 R (moll d ε (fun x => ‖F x‖)) a ψ i hΛ0 hR hf hja
    hψ hψc hsupp
  refine le_trans (lintegral_mono fun y => ?_) (key.trans (le_of_eq ?_))
  · -- pointwise bound
    have hLy : ∀ x : Euc d, ‖x - y‖ < ε → |ρ x - ρ y| ≤ ε * (A * 2 ^ κ * (1 + ‖y‖) ^ (-κ)) := by
      intro x hx
      have h1 := e4_lip_local hρ hκ0 hρ1 hA y x (lt_of_lt_of_le hx hε1)
      have hLy0 : 0 ≤ A * 2 ^ κ * (1 + ‖y‖) ^ (-κ) := by positivity
      calc |ρ x - ρ y| ≤ (A * 2 ^ κ * (1 + ‖y‖) ^ (-κ)) * ‖x - y‖ := h1
        _ ≤ (A * 2 ^ κ * (1 + ‖y‖) ^ (-κ)) * ε := mul_le_mul_of_nonneg_left hx.le hLy0
        _ = _ := mul_comm _ _
    have hc := e4_comm_abs_le_loc hε hρ.continuous hF.locallyIntegrable y hLy
    have hfy : 0 ≤ moll d ε (fun x => ‖F x‖) y :=
      integral_nonneg fun z => mul_nonneg (eta_nonneg hε _) (norm_nonneg _)
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [abs_mul]
    rw [abs_of_nonneg hfy, abs_of_nonneg (ha0 y)]
    calc |comm d ε ρ F y| * |kernelConvDeriv d s i ψ y|
        ≤ (ε * (A * 2 ^ κ * (1 + ‖y‖) ^ (-κ)) * moll d ε (fun x => ‖F x‖) y) *
            |kernelConvDeriv d s i ψ y| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
      _ = _ := by simp only [ha, hΛ]; ring
  · congr 1
    rw [abs_of_nonneg (by positivity : 0 ≤ Real.sqrt N * B)]
    simp only [hΛ]
    ring

theorem e4_amgm {c h ε : ℝ} (hε : 0 < ε) : |c| * |h| ≤ 1 / (2 * ε) * c ^ 2 + ε / 2 * h ^ 2 := by
  have h1 := sq_nonneg (|c| - ε * |h|)
  have e1 : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
  have e2 : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
  rw [e1, e2]
  have : 1 / (2 * ε) * |c| ^ 2 + ε / 2 * |h| ^ 2 - |c| * |h| =
      (|c| - ε * |h|) ^ 2 / (2 * ε) := by
    field_simp
    ring
  have h3 : 0 ≤ (|c| - ε * |h|) ^ 2 / (2 * ε) := by positivity
  linarith

theorem e4_comm_near {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {R : ℝ} (hR : 1 ≤ R)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (B : ℝ), 0 ≤ B → ∀ (F : Euc d → ℝ),
      LocMass B F → ∀ (ρ : Euc d → ℝ), (∀ x y, |ρ x - ρ y| ≤ A * ‖x - y‖) →
      ∀ (c0 : Euc d) (ψ : Euc d → ℝ) (Q : ℝ), 0 ≤ Q → ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      Function.support ψ ⊆ closedBall c0 R → (∫⁻ x, ‖D1 i ψ x‖ₑ ^ 2 ≤ ENNReal.ofReal Q) →
      ∫⁻ y in closedBall c0 (2 * R), ‖comm d ε ρ F y * kernelConvDeriv d s i ψ y‖ₑ ≤
        ENNReal.ofReal (ε * (C * (A ^ 2 * B ^ 2 + Q))) := by
  obtain ⟨N2, hN2⟩ := exists_ball_sq_bound d (2 * R + 2)
  obtain ⟨G, hG0, hG⟩ := e4_kcd_near hs0 hsd i (R := R) (by linarith)
  refine ⟨((N2 : ℝ) + G ^ 2) / 2, by positivity, ?_⟩
  intro ε hε hε1 B hB F hF ρ hρ c0 ψ Q hQ hψ hψc hsupp hD
  set S : Set (Euc d) := closedBall c0 (2 * R) with hS
  have hSm : MeasurableSet S := measurableSet_closedBall
  have hcont : Continuous (HRS.MS.UniqM3.comm d ε ρ F) :=
    e4_comm_continuous hε (m3_continuous_of_lip hA hρ) hF.locallyIntegrable
  set c := HRS.MS.UniqM3.comm d ε ρ F with hc
  set H := kernelConvDeriv d s i ψ with hH
  have hpt : ∀ y, ‖c y * H y‖ₑ ≤ ENNReal.ofReal (1 / (2 * ε)) * ‖c y‖ₑ ^ 2 +
      ENNReal.ofReal (ε / 2) * ‖H y‖ₑ ^ 2 := by
    intro y
    rw [enorm_mul, enorm_sq_eq, enorm_sq_eq, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (e4_amgm hε)
  -- the two integrals
  have hA1 : ∫⁻ y in S, ‖c y‖ₑ ^ 2 ≤ ENNReal.ofReal ((ε * A) ^ 2) * (N2 * ENNReal.ofReal (B ^ 2)) := by
    have hm := m3_comm_lintegral_ball_le hε hA hρ hF c0 (2 * R + 1)
    refine (lintegral_mono_set (closedBall_subset_ball (by linarith))).trans (hm.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    exact (lintegral_mono_set (ball_subset_ball (by linarith))).trans (hN2 B F hF c0)
  have hA2 : ∫⁻ y in S, ‖H y‖ₑ ^ 2 ≤ ENNReal.ofReal (G ^ 2) * ENNReal.ofReal Q :=
    (hG c0 ψ hψ hψc hsupp).trans (mul_le_mul_of_nonneg_left hD zero_le)
  have hsplit : ∫⁻ y in S, (ENNReal.ofReal (1 / (2 * ε)) * ‖c y‖ₑ ^ 2 +
      ENNReal.ofReal (ε / 2) * ‖H y‖ₑ ^ 2) =
      ENNReal.ofReal (1 / (2 * ε)) * (∫⁻ y in S, ‖c y‖ₑ ^ 2) +
        ENNReal.ofReal (ε / 2) * (∫⁻ y in S, ‖H y‖ₑ ^ 2) := by
    rw [lintegral_add_left ((hcont.measurable.enorm.pow_const 2).const_mul _),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ y in S, ‖c y * H y‖ₑ
      ≤ ∫⁻ y in S, (ENNReal.ofReal (1 / (2 * ε)) * ‖c y‖ₑ ^ 2 +
          ENNReal.ofReal (ε / 2) * ‖H y‖ₑ ^ 2) := lintegral_mono hpt
    _ = _ := hsplit
    _ ≤ ENNReal.ofReal (1 / (2 * ε)) * (ENNReal.ofReal ((ε * A) ^ 2) *
          (N2 * ENNReal.ofReal (B ^ 2))) +
        ENNReal.ofReal (ε / 2) * (ENNReal.ofReal (G ^ 2) * ENNReal.ofReal Q) :=
        add_le_add (mul_le_mul_of_nonneg_left hA1 zero_le)
          (mul_le_mul_of_nonneg_left hA2 zero_le)
    _ = ENNReal.ofReal (ε / 2 * (A ^ 2 * (N2 * B ^ 2)) + ε / 2 * (G ^ 2 * Q)) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hN : (0 : ℝ) ≤ N2 := Nat.cast_nonneg N2
        have hB2 : 0 ≤ B ^ 2 := by positivity
        nlinarith [mul_nonneg hε.le (mul_nonneg (sq_nonneg A) (mul_nonneg hN hB2)),
          mul_nonneg hε.le (mul_nonneg (sq_nonneg G) hQ), mul_nonneg hε.le (mul_nonneg (sq_nonneg A) hB2),
          mul_nonneg hε.le hQ, mul_nonneg hε.le (mul_nonneg hN hQ), mul_nonneg hε.le (mul_nonneg (sq_nonneg G) hB2)]

theorem e4_comm_integral_bound {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {R : ℝ}
    (hR : 1 ≤ R) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (B : ℝ), 0 ≤ B → ∀ (F : Euc d → ℝ),
      LocMass B F → ∀ (ρ : Euc d → ℝ), ContDiff ℝ 1 ρ →
      (∀ y, ‖fderiv ℝ ρ y‖ ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) →
      ∀ (c0 : Euc d) (ψ : Euc d → ℝ) (P Q : ℝ), 0 ≤ Q → ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      Function.support ψ ⊆ closedBall c0 R → (∫⁻ x, ‖D1 i ψ x‖ₑ ^ 2 ≤ ENNReal.ofReal Q) →
      (∫ x, |ψ x|) ≤ P →
      |∫ y, HRS.MS.UniqM3.comm d ε ρ F y * kernelConvDeriv d s i ψ y| ≤
        ε * (C * (A ^ 2 * B ^ 2 + Q + A * P * B)) := by
  obtain ⟨Cf, hCf0, hCf⟩ := e4_comm_far (d := d) hs0 A hA
  obtain ⟨Cn, hCn0, hCn⟩ := e4_comm_near hs0 hsd i hR A hA
  refine ⟨Cn + Cf, by positivity, ?_⟩
  intro ε hε hε1 B hB F hF ρ hρ hρ1 c0 ψ P Q hQ hψ hψc hsupp hD hP
  have hlip : ∀ x y, |ρ x - ρ y| ≤ A * ‖x - y‖ :=
    fun x y => e4_lip_global hρ (by positivity : (0 : ℝ) ≤ (d : ℝ) + 3) hρ1 hA x y
  have hnear := hCn ε hε hε1 B hB F hF ρ hlip c0 ψ Q hQ hψ hψc hsupp hD
  have hfar := hCf ε hε hε1 B hB F hF ρ hρ hρ1 i c0 R ψ hR hψ hψc hsupp
  have hSm : MeasurableSet (closedBall c0 (2 * R)) := measurableSet_closedBall
  have htot : ENNReal.ofReal ‖∫ y, HRS.MS.UniqM3.comm d ε ρ F y * kernelConvDeriv d s i ψ y‖ ≤
      ENNReal.ofReal (ε * (Cn * (A ^ 2 * B ^ 2 + Q))) +
        ENNReal.ofReal (Cf * ε * A * (∫ x, |ψ x|) * B) := by
    rw [ofReal_norm]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← lintegral_add_compl _ hSm]
    refine add_le_add hnear ?_
    refine le_trans (lintegral_mono_set ?_) hfar
    intro y hy
    simp only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] at hy
    exact (show 2 * R ≤ ‖y - c0‖ from hy.le)
  have hI0 : 0 ≤ ∫ x, |ψ x| := integral_nonneg fun x => abs_nonneg _
  have hP0 : 0 ≤ P := hI0.trans hP
  have hfar' : Cf * ε * A * (∫ x, |ψ x|) * B ≤ Cf * ε * A * P * B := by
    gcongr
  have hX : 0 ≤ A ^ 2 * B ^ 2 + Q + A * P * B := by positivity
  have hsum : ε * (Cn * (A ^ 2 * B ^ 2 + Q)) + Cf * ε * A * P * B ≤
      ε * ((Cn + Cf) * (A ^ 2 * B ^ 2 + Q + A * P * B)) := by
    have e : ε * ((Cn + Cf) * (A ^ 2 * B ^ 2 + Q + A * P * B)) -
        (ε * (Cn * (A ^ 2 * B ^ 2 + Q)) + Cf * ε * A * P * B) =
        ε * Cn * (A * P * B) + ε * Cf * (A ^ 2 * B ^ 2 + Q) := by ring
    have : 0 ≤ ε * Cn * (A * P * B) + ε * Cf * (A ^ 2 * B ^ 2 + Q) := by positivity
    linarith
  have hnn1 : 0 ≤ ε * (Cn * (A ^ 2 * B ^ 2 + Q)) := by positivity
  have hnn2 : 0 ≤ Cf * ε * A * (∫ x, |ψ x|) * B := by positivity
  have h2 : ENNReal.ofReal ‖∫ y, HRS.MS.UniqM3.comm d ε ρ F y * kernelConvDeriv d s i ψ y‖ ≤
      ENNReal.ofReal (ε * ((Cn + Cf) * (A ^ 2 * B ^ 2 + Q + A * P * B))) := by
    refine htot.trans ?_
    rw [← ENNReal.ofReal_add hnn1 hnn2]
    exact ENNReal.ofReal_le_ofReal ((add_le_add le_rfl hfar').trans hsum)
  rw [← Real.norm_eq_abs]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

end HRS.MS.UniqE4
