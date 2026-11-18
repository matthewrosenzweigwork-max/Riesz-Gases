import HRS.MS.SA12X3C10D

/-!
# S.A.12 C10 (SA12X3), part E: a real-centre uloc piece is bounded by the fine-lattice cell supremum
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3_piece_le_cellSup (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ K1 : ℝ, 0 < K1 ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d), IsAdvectingDrift m Cb T b →
      IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T, ∀ u : Euc d → ℝ, ContDiff ℝ ∞ u → ∀ c : Euc d,
        sobolevNormE (m : ℝ) (fun x => χ (x - c) * u x) ^ 2 ≤ ENNReal.ofReal K1 * cellSup m χ Ψ τ u := by
  obtain ⟨CF, hCF0, hflow⟩ := HRS.MH.Screened.flow_lip_sep_proof hd m Cb T χ χh hχ
  obtain ⟨B, R, -, -, hf⟩ := advected_cutoff_jets d hd m Cb T χ χh hχ
  obtain ⟨B1, hB10, hB1⟩ := sa12x3_stat_B m hχ.1.1 hχ.1.2.1
  set L : ℝ := Real.exp (CF * T) with hLdef
  have hL0 : 0 ≤ L := (Real.exp_pos _).le
  have hfin := sa12c12_finite_cells hd (2 * L + 1)
  set K0 : Finset (Fin d → ℤ) := hfin.toFinset with hK0def
  have hK0 : ∀ k : Fin d → ℤ, ‖cellPt d k‖ ≤ 2 * L + 1 → k ∈ K0 := fun k hk => by
    rw [hK0def, Set.Finite.mem_toFinset]; exact hk
  set Kp : ℝ := B1 ^ 2 * 4 ^ m * ((m : ℝ) + 1) ^ 2 * (d : ℝ) ^ m with hKp
  have hKp0 : 0 ≤ Kp := by positivity
  set M0 : ℝ := ∑ n ∈ Finset.range (m + 1), (d : ℝ) ^ n with hM0
  have hM00 : 0 ≤ M0 := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨2 ^ m * M0 * Kp * (K0.card : ℝ) + 1, by positivity, ?_⟩
  intro b Ψ hb hΨ τ hτ u hu c
  have hT0 : 0 ≤ T := hτ.1.trans hτ.2
  obtain ⟨-, hlipI, -⟩ := hflow b Ψ hb hΨ τ hτ
  have hLτ : Real.exp (CF * τ) ≤ L := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτ.2 hCF0)
  have hLip : ∀ x y, ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ L * ‖x - y‖ := fun x y =>
    (hlipI x y).trans (mul_le_mul_of_nonneg_right hLτ (norm_nonneg _))
  obtain ⟨z0, hz0⟩ := sa12x3_cover_pt hd hχ.1 hL0 hLip K0 hK0 c
  -- the covering weights
  set w : (Fin d → ℤ) → Euc d → ℝ := fun k => advCutoff χ Ψ τ (cellPt d (z0 + k)) with hw
  have hwc : ∀ k, Continuous (w k) := fun k => (hf b Ψ hb hΨ τ hτ (cellPt d (z0 + k))).1.1.continuous
  have hwcs : ∀ k, HasCompactSupport (w k) := fun k =>
    sa12x2_advCutoff_hasCompactSupport hT0 hb hΨ hτ hχ.1.2.1 _
  have hfC : ContDiff ℝ ∞ (fun x => χ (x - c) * u x) := (hχ.1.1.comp (contDiff_id.sub contDiff_const)).mul hu
  have hfc : HasCompactSupport (fun x => χ (x - c) * u x) := by
    have : HasCompactSupport (fun y => χ (y - c)) := by
      have := hχ.1.2.1.comp_homeomorph (Homeomorph.subRight c)
      exact this
    exact this.mul_right
  set E : (Fin d → ℤ) → ℝ := fun k => cellEnergy m χ Ψ τ (cellPt d (z0 + k)) u with hE
  have hE0 : ∀ k, 0 ≤ E k := fun k => sa12x2_cellEnergy_nonneg m χ Ψ τ _ u
  have hYi : ∀ k, Integrable (fun x => w k x ^ 2 * sa12z3_Y m u x) ∧
      ∫ x, w k x ^ 2 * sa12z3_Y m u x ≤ E k := fun k => sa12x3_wY_le_jetSq m (hwc k) (hwcs k) hu
  -- the pointwise bound
  have hpt : ∀ {n : ℕ}, n ≤ m → ∀ (idx : Fin n → Fin d) (x : Euc d),
      (partialDeriv idx (fun y => χ (y - c) * u y) x) ^ 2 ≤ Kp * ∑ k ∈ K0, w k x ^ 2 * sa12z3_Y m u x := by
    intro n hn idx x
    classical
    have h1 := sa12x3_stat_pt hd hχ.1.1 hχ.1.2.2.1 hB10 c (fun i hi y => hB1 c i hi y) hu hn idx x
    refine h1.trans ?_
    have hY : 0 ≤ sa12z3_Y m u x := Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun γ _ => sq_nonneg _
    have hs0 : 0 ≤ ∑ k ∈ K0, w k x ^ 2 * sa12z3_Y m u x :=
      Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) hY
    rw [hKp]
    by_cases hx : x ∈ closedBall c 2
    · obtain ⟨k, hk, hwk⟩ := hz0 x hx
      rw [if_pos hx]
      have : sa12z3_Y m u x ≤ ∑ k ∈ K0, w k x ^ 2 * sa12z3_Y m u x := by
        calc sa12z3_Y m u x = w k x ^ 2 * sa12z3_Y m u x := by
              have : w k x = 1 := hwk
              rw [this]; ring
          _ ≤ _ := Finset.single_le_sum (f := fun k => w k x ^ 2 * sa12z3_Y m u x)
              (fun k _ => mul_nonneg (sq_nonneg _) hY) hk
      have hc0 : 0 ≤ B1 ^ 2 * 4 ^ m * ((m : ℝ) + 1) ^ 2 * (d : ℝ) ^ m := by positivity
      nlinarith
    · rw [if_neg hx]; simpa using mul_nonneg (by positivity : 0 ≤ B1 ^ 2 * 4 ^ m * ((m : ℝ) + 1) ^ 2 * (d : ℝ) ^ m) hs0
  have hI : ∀ {n : ℕ}, n ≤ m → ∀ (idx : Fin n → Fin d),
      ∫ x, (partialDeriv idx (fun y => χ (y - c) * u y) x) ^ 2 ≤ Kp * ∑ k ∈ K0, E k := by
    intro n hn idx
    have hcs : Continuous (partialDeriv idx (fun y => χ (y - c) * u y)) ∧
        HasCompactSupport (partialDeriv idx (fun y => χ (y - c) * u y)) :=
      ⟨(sa12z3_pd_contDiff_inf hfC idx).continuous, sa12z3_pd_compact hfc idx⟩
    have hint : Integrable (fun x => (partialDeriv idx (fun y => χ (y - c) * u y) x) ^ 2) :=
      Continuous.integrable_of_hasCompactSupport (μ := (volume : Measure (Euc d)))
        (hcs.1.pow 2) (hcs.2.comp_left (g := fun t : ℝ => t ^ 2) (by simp))
    have hint2 : Integrable (fun x => Kp * ∑ k ∈ K0, w k x ^ 2 * sa12z3_Y m u x) :=
      (integrable_finset_sum _ fun k _ => (hYi k).1).const_mul Kp
    calc ∫ x, (partialDeriv idx (fun y => χ (y - c) * u y) x) ^ 2
        ≤ ∫ x, Kp * ∑ k ∈ K0, w k x ^ 2 * sa12z3_Y m u x := integral_mono hint hint2 fun x => hpt hn idx x
      _ = Kp * ∑ k ∈ K0, ∫ x, w k x ^ 2 * sa12z3_Y m u x := by
          rw [integral_const_mul, integral_finset_sum _ fun k _ => (hYi k).1]
      _ ≤ Kp * ∑ k ∈ K0, E k :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => (hYi k).2) hKp0
  have hJ : sa12x3_Jraw m (fun y => χ (y - c) * u y) ≤ M0 * (Kp * ∑ k ∈ K0, E k) := by
    unfold sa12x3_Jraw
    calc ∑ n ∈ Finset.range (m + 1), ∑ i : Fin n → Fin d, ∫ x, (partialDeriv i (fun y => χ (y - c) * u y) x) ^ 2
        ≤ ∑ n ∈ Finset.range (m + 1), ∑ _i : Fin n → Fin d, Kp * ∑ k ∈ K0, E k :=
          Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun i _ =>
            hI (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) i
      _ = M0 * (Kp * ∑ k ∈ K0, E k) := by
          rw [hM0, Finset.sum_mul]
          refine Finset.sum_congr rfl fun n _ => ?_
          simp
  have hsob := (sa12x3_sob_jet m (sa12z3_cd_of_inf hfC m) hfc).1
  refine hsob.trans ?_
  have hEsum : 0 ≤ ∑ k ∈ K0, E k := Finset.sum_nonneg fun k _ => hE0 k
  calc ENNReal.ofReal (2 ^ m * sa12x3_Jraw m (fun y => χ (y - c) * u y))
      ≤ ENNReal.ofReal (2 ^ m * M0 * Kp * ∑ k ∈ K0, E k) := by
        apply ENNReal.ofReal_le_ofReal
        calc (2 : ℝ) ^ m * sa12x3_Jraw m (fun y => χ (y - c) * u y)
            ≤ 2 ^ m * (M0 * (Kp * ∑ k ∈ K0, E k)) := mul_le_mul_of_nonneg_left hJ (by positivity)
          _ = _ := by ring
    _ = ENNReal.ofReal (2 ^ m * M0 * Kp) * ∑ k ∈ K0, ENNReal.ofReal (E k) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg fun k _ => hE0 k]
    _ ≤ ENNReal.ofReal (2 ^ m * M0 * Kp) * ((K0.card : ℝ≥0∞) * cellSup m χ Ψ τ u) := by
        gcongr
        calc ∑ k ∈ K0, ENNReal.ofReal (E k) ≤ ∑ _k ∈ K0, cellSup m χ Ψ τ u :=
              Finset.sum_le_sum fun k _ => le_iSup (fun z : Fin d → ℤ =>
                ENNReal.ofReal (cellEnergy m χ Ψ τ (cellPt d z) u)) (z0 + k)
          _ = (K0.card : ℝ≥0∞) * cellSup m χ Ψ τ u := by simp
    _ = ENNReal.ofReal (2 ^ m * M0 * Kp * (K0.card : ℝ)) * cellSup m χ Ψ τ u := by
        rw [ENNReal.ofReal_mul (p := 2 ^ m * M0 * Kp) (by positivity), ENNReal.ofReal_natCast]
        ring
    _ ≤ _ := by
        gcongr
        linarith

end HRS.MH.AdjointRd.Phase2SA12Near
