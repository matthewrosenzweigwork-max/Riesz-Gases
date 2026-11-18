import HRS.Commutator.Torus.TPOSAux15

/-!
# T-POS helpers, part 16: `tr_coef_formula` and `tr_g_zero`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

theorem tpos_coef_formula (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (η : ℝ) (hη : 0 < η) :
    (∀ k : Lattice d, Torus.fcoef (fTorus s η : Torus d → ℝ) k =
        (((if k = 0 then 0 else tScale s * fHatEta d s η (Lattice.toEuc k) : ℝ)) : ℂ)) ∧
      (∀ k : Lattice d, Torus.fcoef (gTorus s η : Torus d → ℝ) k = ((gTcoef d s η k : ℝ) : ℂ)) ∧
      Summable (fun k : Lattice d => |gTcoef d s η k|) ∧
      Continuous (Torus.lift (gTorus s η : Torus d → ℝ)) := by
  obtain ⟨r, δ, hδ, hr, hsing⟩ := tpos_local_data (d := d) (s := s) hd hs0 hsd
  have hsum := tpos_gTcoef_summable (d := d) hs0 hsd hη
  refine ⟨tpos_fcoef_fTorus hs0 hsd hη, tpos_fcoef_gTorus hd hs0 hsd hη, hsum, ?_⟩
  have h := (tpos_gTorus_eq hd hs0 hsd hη r δ hδ hr hsing).1
  rw [h]
  exact (tposH_continuous hsum).comp Torus.continuous_mk

lemma tpos_Gloc_zero_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (r : Torus d → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      |tposGloc s η r 0 - (tScale s * η ^ (-s) * Whole.g1Zero d s -
        (if s = 0 then Real.log η else 0))| ≤ B := by
  classical
  have hd0 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hts := tpos_tScale_pos hs0
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith
  have hcp := Whole.cPhi_pos d hs0 hs2
  have h2 : (0 : ℝ) < 2 * (d : ℝ) + 4 - s := by linarith
  set K1 : ℝ := Whole.cPhi d s / (2 * (d : ℝ) + 4 - s) with hK1
  set Zs : ℝ := ∑' m : Lattice d, ‖Lattice.toEuc m‖ ^ (-(2 * (d : ℝ) + 4)) with hZs
  set Km : ℝ := Whole.cPhi d s * (∫ x : Euc d, Whole.phi x) / ((d : ℝ) - s) with hKm
  have hphi : 0 ≤ ∫ x : Euc d, Whole.phi x :=
    integral_nonneg fun x => (Whole.phiR_pos (d := d) _).le
  have hKm0 : 0 ≤ Km := by
    rw [hKm]; have : 0 < (d : ℝ) - s := by linarith
    positivity
  have hZs_sum : Summable (fun m : Lattice d => ‖Lattice.toEuc m‖ ^ (-(2 * (d : ℝ) + 4))) :=
    tpos_summable_rpow (by linarith)
  have hZs0 : 0 ≤ Zs := tsum_nonneg fun m => by positivity
  refine ⟨|r (Torus.mk 0)| + tScale s * (K1 * Zs) + tScale s * Km, by positivity, fun η hη hη1 => ?_⟩
  have hg1 : Whole.g1 s (η⁻¹ • (0 : Euc d)) = Whole.g1Zero d s := by
    simp [Whole.g1]
  have hexp : η ^ (2 * (d : ℝ) + 4 - s) ≤ 1 := Real.rpow_le_one hη.le hη1 h2.le
  have hKη : Whole.cPhi d s / (2 * (d : ℝ) + 4 - s) * η ^ (2 * (d : ℝ) + 4 - s) ≤ K1 := by
    rw [hK1]
    calc _ ≤ Whole.cPhi d s / (2 * (d : ℝ) + 4 - s) * 1 :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := mul_one _
  -- the tail sum
  set term : Lattice d → ℝ := fun m => if m = 0 then 0 else Whole.fTrunc s η (0 + Lattice.toEuc m)
    with hterm
  have hterm_nn : ∀ m, 0 ≤ term m := by
    intro m; simp only [hterm]; split_ifs
    · exact le_refl _
    · exact tpos_fTrunc_nonneg hs0 hs2 η _
  have hterm_le : ∀ m, term m ≤ K1 * ‖Lattice.toEuc m‖ ^ (-(2 * (d : ℝ) + 4)) := by
    intro m
    by_cases hm : m = 0
    · simp only [hterm, hm, if_true]
      have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      rw [this, norm_zero, Real.zero_rpow (by linarith)]; simp
    · simp only [hterm, hm, if_false]
      have hz : (0 : Euc d) + Lattice.toEuc m ≠ 0 := by
        rw [zero_add]
        intro h; apply hm
        funext i
        have := congrFun (congrArg WithLp.ofLp h) i
        simpa [Lattice.toEuc] using this
      rw [zero_add] at hz ⊢
      calc Whole.fTrunc s η (Lattice.toEuc m)
          ≤ Whole.cPhi d s / (2 * (d : ℝ) + 4 - s) * η ^ (2 * (d : ℝ) + 4 - s) *
            ‖Lattice.toEuc m‖ ^ (-(2 * (d : ℝ) + 4)) := tpos_fTrunc_le hs0 hs2 hη hz
        _ ≤ K1 * ‖Lattice.toEuc m‖ ^ (-(2 * (d : ℝ) + 4)) :=
            mul_le_mul_of_nonneg_right hKη (by positivity)
  have hterm_sum : Summable term :=
    Summable.of_nonneg_of_le hterm_nn hterm_le (hZs_sum.mul_left K1)
  have hS0 : 0 ≤ ∑' m, term m := tsum_nonneg hterm_nn
  have hS1 : ∑' m, term m ≤ K1 * Zs := by
    calc ∑' m, term m ≤ ∑' m : Lattice d, K1 * ‖Lattice.toEuc m‖ ^ (-(2 * (d : ℝ) + 4)) :=
          hterm_sum.tsum_le_tsum hterm_le (hZs_sum.mul_left K1)
      _ = K1 * Zs := by rw [hZs, tsum_mul_left]
  have hc := tpos_integral_perio_fTrunc hs0 hsd hη (d := d)
  have hc0 : 0 ≤ ∫ x : Torus d, perio (Whole.fTrunc s η : Euc d → ℝ) x := by
    rw [hc, ← hKm]
    exact mul_nonneg hKm0 (Real.rpow_nonneg hη.le _)
  have hc1 : ∫ x : Torus d, perio (Whole.fTrunc s η : Euc d → ℝ) x ≤ Km := by
    rw [hc, ← hKm]
    calc Km * η ^ ((d : ℝ) - s) ≤ Km * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one hη.le hη1 (by linarith)) hKm0
      _ = Km := mul_one _
  have hexpr : tposGloc s η r 0 - (tScale s * η ^ (-s) * Whole.g1Zero d s -
      (if s = 0 then Real.log η else 0)) =
      r (Torus.mk 0) - tScale s * ∑' m, term m +
        tScale s * ∫ x : Torus d, perio (Whole.fTrunc s η : Euc d → ℝ) x := by
    unfold tposGloc
    rw [hg1]
    simp only [hterm, smul_zero, zero_add]
    ring
  rw [hexpr]
  have hr0 := abs_nonneg (r (Torus.mk 0))
  rw [abs_le]
  constructor
  · have := neg_abs_le (r (Torus.mk 0))
    nlinarith [mul_le_mul_of_nonneg_left hS1 hts.le, mul_nonneg hts.le hc0]
  · have := le_abs_self (r (Torus.mk 0))
    nlinarith [mul_le_mul_of_nonneg_left hc1 hts.le, mul_nonneg hts.le hS0]

theorem tpos_g_zero (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      (0 < s → |gTorus0 d s η| ≤ C * η ^ (-s)) ∧ (s = 0 → |gTorus0 d s η + Real.log η| ≤ C) := by
  have hd0 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith
  have hcp := Whole.cPhi_pos d hs0 hs2
  obtain ⟨r, δ, hδ, hr, hsing⟩ := tpos_local_data (d := d) (s := s) hd hs0 hsd
  obtain ⟨B, hB0, hB⟩ := tpos_Gloc_zero_bound hd hs0 hsd r
  refine ⟨Whole.cPhi d s + |Whole.g1Zero d s| + B + 1, by positivity, fun η hη hη1 => ?_⟩
  have h0 := (tpos_gTorus_eq hd hs0 hsd hη r δ hδ hr hsing).2
  have hb := hB η hη hη1
  rw [← h0] at hb
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · have hs0' : s ≠ 0 := hs.ne'
    have hts : tScale s = s := by simp [tScale, hs0']
    have hg : Whole.g1Zero d s = Whole.cPhi d s / s := by simp [Whole.g1Zero, hs0']
    have hA : tScale s * η ^ (-s) * Whole.g1Zero d s - (if s = 0 then Real.log η else 0) =
        Whole.cPhi d s * η ^ (-s) := by
      rw [hts, hg, if_neg hs0']; field_simp; ring
    rw [hA] at hb
    have h1 : 1 ≤ η ^ (-s) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη hη1 (by linarith)
    have h2 : |gTorus0 d s η| ≤ Whole.cPhi d s * η ^ (-s) + B := by
      have := abs_sub_abs_le_abs_sub (gTorus0 d s η) (Whole.cPhi d s * η ^ (-s))
      rw [abs_of_nonneg (by positivity : 0 ≤ Whole.cPhi d s * η ^ (-s))] at this
      linarith
    nlinarith [abs_nonneg (Whole.g1Zero d s), mul_le_mul_of_nonneg_left h1 hcp.le]
  · subst hs
    have hts : tScale 0 = 1 := by simp [tScale]
    have hA : tScale 0 * η ^ (-(0 : ℝ)) * Whole.g1Zero d 0 - (if (0 : ℝ) = 0 then Real.log η else 0) =
        Whole.g1Zero d 0 - Real.log η := by
      simp [hts]
    rw [hA] at hb
    have : gTorus0 d 0 η + Real.log η = (gTorus0 d 0 η - (Whole.g1Zero d 0 - Real.log η)) +
        Whole.g1Zero d 0 := by ring
    rw [this]
    calc |(gTorus0 d 0 η - (Whole.g1Zero d 0 - Real.log η)) + Whole.g1Zero d 0|
        ≤ |gTorus0 d 0 η - (Whole.g1Zero d 0 - Real.log η)| + |Whole.g1Zero d 0| := abs_add_le _ _
      _ ≤ _ := by linarith [abs_nonneg (Whole.g1Zero d 0)]

end HRS.Commutator.TorusNote
