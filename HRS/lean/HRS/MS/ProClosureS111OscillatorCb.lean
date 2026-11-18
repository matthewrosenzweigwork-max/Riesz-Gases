import HRS.MS.S111X1G2

/-!
Quantitative bounded-derivative estimates on the original oscillator test
class. The coefficients are those of the actual Hermite expansion; no
additional Schwartz or finite-combination assumption is imposed.

The extra summability margin used here is harmless for `wholeSpaceIndex`.
It lets the proof use the elementary bound of one Hilbert coordinate by
the norm, followed by an absolutely summable spectral weight.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1

variable {d : ℕ} {m : ℝ}

theorem oscillator_coefficient_bound {phi : Euc d → ℝ}
    (hphi : MemOsc m phi) (alpha : MultiIndex d) :
    |HRS.Whole.hermiteCoeff phi alpha| * oscEigenvalue d alpha ^ (m / 2) ≤
      oscNorm m phi := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (show lp (fun _ : MultiIndex d => ℝ) 2 from OscSpace.ofFun m phi) alpha
  change |OscSpace.coord (OscSpace.ofFun m phi) alpha| ≤ ‖OscSpace.ofFun m phi‖ at h
  rw [OscSpace.coord_ofFun_eq hphi, OscSpace.norm_ofFun phi hphi, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (oscEv_pos alpha).le _)] at h
  simpa only [mul_comm] using h

/-- All derivatives through order `k` are bounded linearly by the original
oscillator norm. The constant precedes the test function. -/
theorem oscillator_derivative_norm_bound (k n : ℕ)
    (hn : (k : ℝ) + (d : ℝ) / 2 < n)
    (hm : (d : ℝ) < (m - n) / 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ phi : Euc d → ℝ, IsOscTest m phi →
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j phi x‖ ≤ B * oscNorm m phi := by
  obtain ⟨C, hC0, hC⟩ := hermite_deriv_bound_le (d := d) k n hn
  let w : MultiIndex d → ℝ := fun alpha =>
    oscEigenvalue d alpha ^ (-((m - n) / 2))
  have hw0 : ∀ alpha, 0 ≤ w alpha := fun alpha =>
    Real.rpow_nonneg (oscEv_pos alpha).le _
  have hws : Summable w := OscDual.summable_oscEv_neg_rpow hm
  refine ⟨C * ∑' alpha, w alpha, mul_nonneg hC0 (tsum_nonneg hw0), ?_⟩
  intro phi hphi
  have hm' : (d : ℝ) < m - n := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hn0 : (d : ℝ) / 2 < n := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hfun : phi = fun x => ∑' alpha,
      HRS.Whole.hermiteCoeff phi alpha * hermiteFunD alpha x :=
    funext (hermite_series_eq hn0 hm' hphi.1.continuous hphi.2)
  have hc : ∀ alpha,
      |HRS.Whole.hermiteCoeff phi alpha| * oscEigenvalue d alpha ^ ((n : ℝ) / 2) ≤
        oscNorm m phi * w alpha := by
    intro alpha
    have he : oscEigenvalue d alpha ^ ((n : ℝ) / 2) =
        oscEigenvalue d alpha ^ (m / 2) * w alpha := by
      dsimp [w]
      rw [← Real.rpow_add (oscEv_pos alpha)]
      congr 1
      ring
    rw [he, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (oscillator_coefficient_bound hphi.2 alpha)
      (hw0 alpha)
  have hsum : Summable (fun alpha => C * oscNorm m phi * w alpha) :=
    hws.mul_left _
  have hcd : ∀ alpha, ContDiff ℝ (k : WithTop ℕ∞)
      (fun y => HRS.Whole.hermiteCoeff phi alpha * hermiteFunD alpha y) :=
    fun alpha => contDiff_const.mul
      ((contDiff_hermiteFunD alpha).of_le (by exact_mod_cast le_top))
  have hbd : ∀ (j : ℕ) (alpha : MultiIndex d) (x : Euc d), (j : ℕ∞) ≤ k →
      ‖iteratedFDeriv ℝ j
        (fun y => HRS.Whole.hermiteCoeff phi alpha * hermiteFunD alpha y) x‖ ≤
        C * oscNorm m phi * w alpha := by
    intro j alpha x hj
    have hjk : j ≤ k := by exact_mod_cast hj
    change ‖iteratedFDeriv ℝ j
        (HRS.Whole.hermiteCoeff phi alpha • hermiteFunD alpha) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply
      (a := HRS.Whole.hermiteCoeff phi alpha) (i := j) (f := hermiteFunD alpha)
      (((contDiff_hermiteFunD alpha).of_le (by exact_mod_cast le_top)).contDiffAt),
      norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |HRS.Whole.hermiteCoeff phi alpha| *
          (C * oscEigenvalue d alpha ^ ((n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (hC j hjk alpha x) (abs_nonneg _)
      _ = C * (|HRS.Whole.hermiteCoeff phi alpha| *
          oscEigenvalue d alpha ^ ((n : ℝ) / 2)) := by ring
      _ ≤ C * (oscNorm m phi * w alpha) :=
        mul_le_mul_of_nonneg_left (hc alpha) hC0
      _ = _ := by ring
  intro j hj x
  have hit := iteratedFDeriv_tsum (𝕜 := ℝ) (N := (k : ℕ∞))
    (f := fun alpha y => HRS.Whole.hermiteCoeff phi alpha * hermiteFunD alpha y)
    (v := fun _ alpha => C * oscNorm m phi * w alpha) hcd
    (fun _ _ => hsum) hbd (k := j) (by exact_mod_cast hj)
  have hit' : iteratedFDeriv ℝ j phi x =
      ∑' alpha, iteratedFDeriv ℝ j
        (fun y => HRS.Whole.hermiteCoeff phi alpha * hermiteFunD alpha y) x := by
    conv_lhs => rw [hfun]
    exact congrFun hit x
  have hnorm : Summable (fun alpha => ‖iteratedFDeriv ℝ j
      (fun y => HRS.Whole.hermiteCoeff phi alpha * hermiteFunD alpha y) x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun alpha => hbd j alpha x (by exact_mod_cast hj)) hsum
  rw [hit']
  calc
    _ ≤ ∑' alpha, ‖iteratedFDeriv ℝ j
        (fun y => HRS.Whole.hermiteCoeff phi alpha * hermiteFunD alpha y) x‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' alpha, C * oscNorm m phi * w alpha :=
      Summable.tsum_le_tsum (fun alpha => hbd j alpha x (by exact_mod_cast hj))
        hnorm hsum
    _ = (C * ∑' alpha, w alpha) * oscNorm m phi := by
      rw [tsum_mul_left]
      ring

theorem oscillator_cbNorm_bound (k n : ℕ)
    (hn : (k : ℝ) + (d : ℝ) / 2 < n)
    (hm : (d : ℝ) < (m - n) / 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ phi : Euc d → ℝ, IsOscTest m phi →
      MemCb k phi ∧ cbNorm k phi ≤ B * oscNorm m phi := by
  obtain ⟨B, hB, hb⟩ := oscillator_derivative_norm_bound k n hn hm
  refine ⟨((k : ℝ) + 1) * B, mul_nonneg (by positivity) hB, ?_⟩
  intro phi hphi
  refine ⟨⟨hphi.1.of_le (by exact_mod_cast le_top), fun j hj =>
    ⟨B * oscNorm m phi, by rintro _ ⟨x, rfl⟩; exact hb phi hphi j hj x⟩⟩, ?_⟩
  unfold cbNorm
  calc
    _ ≤ ∑ _j ∈ Finset.range (k + 1), B * oscNorm m phi :=
      Finset.sum_le_sum fun j hj => ciSup_le fun x =>
        hb phi hphi j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) x
    _ = (((k : ℝ) + 1) * B) * oscNorm m phi := by simp; ring

theorem oscillator_ulNorm_bound (k n : ℕ)
    (hn : (k : ℝ) + (d : ℝ) / 2 < n)
    (hm : (d : ℝ) < (m - n) / 2)
    {theta : Euc d → ℝ} (htheta : IsUlCutoff theta) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ phi : Euc d → ℝ, IsOscTest m phi →
      ulNormE k theta phi ≤ ENNReal.ofReal (B * oscNorm m phi) := by
  obtain ⟨B, hB, hb⟩ := oscillator_cbNorm_bound k n hn hm
  obtain ⟨chi, hchi⟩ := HRS.MS.Ul.ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := HRS.MS.Ul.ul_equiv k theta chi htheta hchi
  obtain ⟨Cc, hCc, hcb⟩ := HRS.MS.Ul.ulocNormE_le_cb k chi hchi
  refine ⟨Ce * Cc * B, by positivity, fun phi hphi => ?_⟩
  calc
    _ ≤ ENNReal.ofReal Ce * HRS.Whole.AppendixA.ulocNormE k chi phi := (hequ phi).1
    _ ≤ ENNReal.ofReal Ce * ENNReal.ofReal (Cc * cbNorm k phi) := by
      gcongr
      exact hcb phi (hb phi hphi).1
    _ = ENNReal.ofReal (Ce * (Cc * cbNorm k phi)) := by
      rw [ENNReal.ofReal_mul hCe.le]
    _ ≤ ENNReal.ofReal ((Ce * Cc * B) * oscNorm m phi) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ Ce * (Cc * (B * oscNorm m phi)) := by
          gcongr
          exact (hb phi hphi).2
        _ = _ := by ring

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.oscillator_derivative_norm_bound
#print axioms HRS.MS.ProClosureS111.oscillator_ulNorm_bound
