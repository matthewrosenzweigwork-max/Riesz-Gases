import HRS.MS.Fp81S21WindowSup2

/-!
# HRS S2.1(iii), SOL40 packet 9d: ENNReal scalar Minkowski

Source audit carried forward from the compiled producers:

* `s102_zf P X ζ u f` is `√N` times empirical minus actual-mean pairing.
* `r2QuadField s μ P X u ζ f` is `N` times pair energy minus its actual-law
  expectation; it is positive centered and the moving orbit identity places
  `−(√N)⁻¹` outside it.
* `fp81s21_moving_orbit_zeta` evaluates the propagator at terminal time `t`
  and integrates the moving-law drift at physical time `r`.
* `fp81s21_window_Bpos` includes the oscillator amplitude in its square-sum
  envelope. The scalar coordinate itself does not receive a second weight.

This file is the direct ENNReal L⁶ Minkowski brick, with no `Lp`-valued map.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

private lemma fp81s21_ennreal_sixth_root_pow (x : ℝ≥0∞) :
    (x ^ (1 / 6 : ℝ)) ^ 6 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Scalar Minkowski's integral inequality in ENNReal form for exponent six.
The proof truncates the inner integral, applies Hölder with exponents 6/5 and
6 to its fifth power times the integrand, then uses monotone convergence. -/
theorem fp81s21_lintegral_minkowski_six
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure S) [SFinite ν]
    (g : S → Ω → ℝ≥0∞)
    (hg : Measurable (Function.uncurry g)) :
    (∫⁻ ω, (∫⁻ s, g s ω ∂ν) ^ (6 : ℕ) ∂P) ^ (1 / 6 : ℝ) ≤
      ∫⁻ s, (∫⁻ ω, (g s ω) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ∂ν := by
  classical
  let F : Ω → ℝ≥0∞ := fun ω => ∫⁻ s, g s ω ∂ν
  have hFmeas : Measurable F := by
    dsimp [F]
    exact (hg.comp measurable_swap).lintegral_prod_right'
  let n : S → ℝ≥0∞ := fun s =>
    (∫⁻ ω, (g s ω) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ)
  let A : ℝ≥0∞ := ∫⁻ s, n s ∂ν
  by_cases hAtop : A = ∞
  · have hAtop' :
        (∫⁻ s, (∫⁻ ω, (g s ω) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ∂ν) = ∞ := by
      simpa [A, n] using hAtop
    rw [hAtop']
    exact le_top
  have hpq : ((6 : ℝ) / 5).HolderConjugate (6 : ℝ) := by
    exact Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  let trunc : ℕ → Ω → ℝ≥0∞ := fun k ω => min (F ω) (k : ℝ≥0∞)
  have htruncMeas (k : ℕ) : Measurable (trunc k) := by
    exact hFmeas.min measurable_const
  have htruncBound (k : ℕ) (ω : Ω) : trunc k ω ≤ (k : ℝ≥0∞) := min_le_right _ _
  have hterm (k : ℕ) :
      (∫⁻ ω, (trunc k ω) ^ (6 : ℕ) ∂P) ≤ A ^ (6 : ℕ) := by
    let T : ℝ≥0∞ := ∫⁻ ω, (trunc k ω) ^ (6 : ℕ) ∂P
    have hTfinite : T ≤ (k : ℝ≥0∞) ^ 6 := by
      calc
        T ≤ ∫⁻ ω, (k : ℝ≥0∞) ^ (6 : ℕ) ∂P := by
          apply lintegral_mono
          intro ω
          exact pow_le_pow_left₀ (by positivity) (htruncBound k ω) 6
        _ = (k : ℝ≥0∞) ^ 6 := by simp
    have hTfinite' : T ≠ ∞ := by
      apply ne_of_lt (lt_of_le_of_lt hTfinite ?_)
      exact ENNReal.pow_lt_top ENNReal.coe_lt_top
    have hTpowTop : T ^ (5 / 6 : ℝ) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hTfinite'
    have hgm : Measurable fun z : Ω × S => g z.2 z.1 := hg.comp measurable_swap
    have hprod : Measurable fun z : Ω × S =>
        (trunc k z.1) ^ (5 : ℕ) * g z.2 z.1 := by
      exact (htruncMeas k).pow_const 5 |>.comp measurable_fst |>.mul hgm
    have hpow : ∀ ω, ((trunc k ω) ^ (5 : ℕ)) ^ (6 / 5 : ℝ) =
        (trunc k ω) ^ (6 : ℕ) := by
      intro ω
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    have hHolder (s : S) :
        (∫⁻ ω, (trunc k ω) ^ (5 : ℕ) * g s ω ∂P) ≤
          T ^ (5 / 6 : ℝ) * n s := by
      have hgs : AEMeasurable (fun ω => g s ω) P := by
        exact (hg.comp (measurable_const.prodMk measurable_id)).aemeasurable
      calc
        (∫⁻ ω, (trunc k ω) ^ (5 : ℕ) * g s ω ∂P) ≤
            (∫⁻ ω, ((trunc k ω) ^ (5 : ℕ)) ^ (6 / 5 : ℝ) ∂P) ^
                (1 / ((6 : ℝ) / 5)) *
              (∫⁻ ω, (g s ω) ^ (6 : ℝ) ∂P) ^ (1 / (6 : ℝ)) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq
            ((htruncMeas k).pow_const 5).aemeasurable hgs
        _ = T ^ (5 / 6 : ℝ) * n s := by
          have hfirst :
              (∫⁻ ω, ((trunc k ω) ^ (5 : ℕ)) ^ (6 / 5 : ℝ) ∂P) = T :=
            lintegral_congr fun ω => hpow ω
          rw [hfirst]
          congr 1
          · congr 1 <;> norm_num
    have hswap :
        (∫⁻ ω, ∫⁻ s, (trunc k ω) ^ (5 : ℕ) * g s ω ∂ν ∂P) =
          ∫⁻ s, ∫⁻ ω, (trunc k ω) ^ (5 : ℕ) * g s ω ∂P ∂ν := by
      exact lintegral_lintegral_swap hprod.aemeasurable
    have hfactor (ω : Ω) :
        (∫⁻ s, (trunc k ω) ^ (5 : ℕ) * g s ω ∂ν) =
          (trunc k ω) ^ (5 : ℕ) * F ω := by
      have htruncTop : trunc k ω ≠ ∞ :=
        ne_of_lt (lt_of_le_of_lt (htruncBound k ω) ENNReal.coe_lt_top)
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top htruncTop)]
    have hTle : T ≤ T ^ (5 / 6 : ℝ) * A := by
      calc
        T = ∫⁻ ω, (trunc k ω) ^ (6 : ℕ) ∂P := rfl
        _ ≤ ∫⁻ ω, (trunc k ω) ^ (5 : ℕ) * F ω ∂P := by
          apply lintegral_mono
          intro ω
          calc
            (trunc k ω) ^ (6 : ℕ) =
                (trunc k ω) ^ (5 : ℕ) * trunc k ω := by ring
            _ ≤ (trunc k ω) ^ (5 : ℕ) * F ω := by
              gcongr
              exact min_le_left _ _
        _ = ∫⁻ ω, ∫⁻ s, (trunc k ω) ^ (5 : ℕ) * g s ω ∂ν ∂P := by
          apply lintegral_congr
          intro ω
          rw [hfactor]
        _ = ∫⁻ s, ∫⁻ ω, (trunc k ω) ^ (5 : ℕ) * g s ω ∂P ∂ν := hswap
        _ ≤ ∫⁻ s, T ^ (5 / 6 : ℝ) * n s ∂ν := by
          apply lintegral_mono
          exact hHolder
        _ = T ^ (5 / 6 : ℝ) * A := by
          rw [← lintegral_const_mul' _ _ hTpowTop]
    have hroot : T ^ (1 / 6 : ℝ) ≤ A := by
      by_cases hTzero : T = 0
      · simp [hTzero]
      have hsplit : T ^ (1 / 6 : ℝ) * T ^ (5 / 6 : ℝ) = T := by
        rw [← ENNReal.rpow_add_of_nonneg (x := T) (1 / 6) (5 / 6)
          (by norm_num) (by norm_num)]
        norm_num
      have hfactor0 : T ^ (5 / 6 : ℝ) ≠ 0 := by
        intro hz
        have : T = 0 := by rw [← hsplit, hz]; simp
        exact hTzero this
      have hmul : T ^ (1 / 6 : ℝ) * T ^ (5 / 6 : ℝ) ≤
          A * T ^ (5 / 6 : ℝ) := by
        calc
          T ^ (1 / 6 : ℝ) * T ^ (5 / 6 : ℝ) = T := hsplit
          _ ≤ T ^ (5 / 6 : ℝ) * A := hTle
          _ = A * T ^ (5 / 6 : ℝ) := mul_comm _ _
      exact (ENNReal.mul_le_mul_iff_left hfactor0 hTpowTop).1 hmul
    calc
      T = (T ^ (1 / 6 : ℝ)) ^ (6 : ℕ) := (fp81s21_ennreal_sixth_root_pow T).symm
      _ ≤ A ^ (6 : ℕ) := pow_le_pow_left₀ bot_le hroot 6
  let Tfull : ℝ≥0∞ := ∫⁻ ω, F ω ^ (6 : ℕ) ∂P
  have hsup (ω : Ω) : F ω ^ (6 : ℕ) = ⨆ k : ℕ, (trunc k ω) ^ (6 : ℕ) := by
    rw [← ENNReal.iSup_pow]
    have hmin : (⨆ k : ℕ, min (F ω) (k : ℝ≥0∞)) = F ω := by
      by_cases htop : F ω = ∞
      · simp [htop, ENNReal.iSup_natCast]
      obtain ⟨k, hk⟩ := exists_nat_gt (F ω).toReal
      have hle : F ω ≤ (k : ℝ≥0∞) := by
        calc
          F ω = ENNReal.ofReal (F ω).toReal := (ENNReal.ofReal_toReal htop).symm
          _ ≤ ENNReal.ofReal (k : ℝ) := ENNReal.ofReal_le_ofReal (le_of_lt hk)
          _ = (k : ℝ≥0∞) := by simp
      apply le_antisymm
      · exact iSup_le fun j => min_le_left _ _
      · exact le_iSup_of_le k (by rw [min_eq_left hle])
    rw [hmin]
  have hdir : Directed (· ≤ ·) (fun k : ℕ => fun ω => (trunc k ω) ^ (6 : ℕ)) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩ <;> intro ω
    · exact pow_le_pow_left₀ bot_le (min_le_min_left _ (by exact_mod_cast le_max_left i j)) 6
    · exact pow_le_pow_left₀ bot_le (min_le_min_left _ (by exact_mod_cast le_max_right i j)) 6
  have hmeas : ∀ k : ℕ, AEMeasurable (fun ω => (trunc k ω) ^ (6 : ℕ)) P := by
    intro k
    exact ((htruncMeas k).pow_const 6).aemeasurable
  have hTfull : Tfull ≤ A ^ (6 : ℕ) := by
    rw [show Tfull = ∫⁻ ω, ⨆ k : ℕ, (trunc k ω) ^ (6 : ℕ) ∂P by
      exact lintegral_congr hsup]
    exact (lintegral_iSup_directed hmeas hdir).trans_le (iSup_le hterm)
  have hrootFinal : (Tfull) ^ (1 / 6 : ℝ) ≤ A := by
    calc
      Tfull ^ (1 / 6 : ℝ) ≤ (A ^ (6 : ℕ)) ^ (1 / 6 : ℝ) :=
        ENNReal.rpow_le_rpow hTfull (by norm_num)
      _ = A := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
  simpa only [Tfull, F, A, n] using hrootFinal

#print axioms fp81s21_ennreal_sixth_root_pow
#print axioms fp81s21_lintegral_minkowski_six

end HRS.Fp81.S21

end
