import HRS.MS.GenPathAux6
import HRS.MS.CovMeasAux22

/-!
# S2.1(iii), packet 15d-1: unit-clock block reconstruction

The path clock is the unit interval, while the feature space has observation
horizon `H`.  The clipped clock selects the feature-time value of the `B`
coordinate; the terminal feature supplies `evalA` and the subtracted `B`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9 HRS.MS.CovMeas

variable {d : ℕ} {m H : ℝ}

/- Exact intended declarations:
def fp81s21_blockClock (a : ℝ) (k : ℕ) (t : Icc (0 : ℝ) H) : Icc (0 : ℝ) 1
def fp81s21_blockRecon (hH : 0 ≤ H) (a : ℝ) (k : ℕ) :
  PathSp 1 (KSpace d m H) →L[ℝ] OscPath d m H
theorem fp81s21_blockRecon_apply (hH : 0 ≤ H) (a : ℝ) (k : ℕ)
    (y : PathSp 1 (KSpace d m H)) (t : Icc (0 : ℝ) H) :
  (show C(Icc (0 : ℝ) H, OscDual d m) from fp81s21_blockRecon hH a k y) t =
    (pcm y fp81s21_unitClockEndpoint).evalA t - (pcm y fp81s21_unitClockEndpoint).B +
      (pcm y (fp81s21_blockClock a k t)).B
theorem fp81s21_blockRecon_norm_le (hH : 0 ≤ H) (a : ℝ) (k : ℕ) :
  ‖fp81s21_blockRecon (d := d) (m := m) hH a k‖ ≤ 3 + Real.sqrt H
theorem fp81s21_blockRecon_coord (hH : 0 ≤ H) (a : ℝ) (k : ℕ)
    (y : PathSp 1 (KSpace d m H)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H)
    (α : MultiIndex d) :
  OscDual.coord (r2PathAt (fp81s21_blockRecon hH a k y) t) α =
    inner ℝ (pcm y fp81s21_unitClockEndpoint) (s101P m H t α) +
      inner ℝ (pcm y (fp81s21_blockClock a k ⟨t, ht⟩)) (s101Q m H α)
-/

/-- The unit-clock clipping `max 0 (min (a+t-k) 1)`. -/
def fp81s21_blockClock (a : ℝ) (k : ℕ) (t : Icc (0 : ℝ) H) : Icc (0 : ℝ) 1 :=
  ⟨max 0 (min (a + (t : ℝ) - (k : ℝ)) 1),
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩⟩

/-- The terminal point of the unit path clock. -/
def fp81s21_unitClockEndpoint : Icc (0 : ℝ) 1 :=
  ⟨1, by simp only [Set.mem_Icc]; constructor <;> norm_num⟩

theorem fp81s21_blockClock_continuous (a : ℝ) (k : ℕ) :
    Continuous (fun t : Icc (0 : ℝ) H => fp81s21_blockClock a k t) := by
  have hmem : ∀ t : Icc (0 : ℝ) H,
      max 0 (min (a + (t : ℝ) - (k : ℝ)) 1) ∈ Icc (0 : ℝ) 1 :=
    fun t => (fp81s21_blockClock a k t).property
  exact Continuous.subtype_mk
    (continuous_const.max
      (((continuous_const.add continuous_subtype_val).sub continuous_const).min continuous_const)) hmem

private def fp81s21_blockReconFun (hH : 0 ≤ H) (a : ℝ) (k : ℕ)
    (y : PathSp 1 (KSpace d m H)) : OscPath d m H :=
  ⟨fun t =>
      (pcm y fp81s21_unitClockEndpoint).evalA t -
        (pcm y fp81s21_unitClockEndpoint).B + (pcm y (fp81s21_blockClock a k t)).B,
    by
      have hEval : Continuous
          (fun t : Icc (0 : ℝ) H => (pcm y fp81s21_unitClockEndpoint).evalA t) :=
        continuousOn_iff_continuous_restrict.1
          (u9_continuousOn_evalA hH (pcm y fp81s21_unitClockEndpoint))
      have hB : Continuous
          (fun t : Icc (0 : ℝ) H => (pcm y (fp81s21_blockClock a k t)).B) :=
        u9_continuous_B.comp
          ((pcm y).continuous.comp (fp81s21_blockClock_continuous a k))
      exact (hEval.sub continuous_const).add hB⟩

private theorem fp81s21_blockReconFun_apply (hH : 0 ≤ H) (a : ℝ) (k : ℕ)
    (y : PathSp 1 (KSpace d m H)) (t : Icc (0 : ℝ) H) :
    (show C(Icc (0 : ℝ) H, OscDual d m) from fp81s21_blockReconFun hH a k y) t =
      (pcm y fp81s21_unitClockEndpoint).evalA t -
        (pcm y fp81s21_unitClockEndpoint).B + (pcm y (fp81s21_blockClock a k t)).B := rfl

private def fp81s21_blockReconLin (hH : 0 ≤ H) (a : ℝ) (k : ℕ) :
    PathSp 1 (KSpace d m H) →ₗ[ℝ] OscPath d m H where
  toFun y := fp81s21_blockReconFun hH a k y
  map_add' y z := by
    refine ContinuousMap.ext fun t => ?_
    change (show C(Icc (0 : ℝ) H, OscDual d m) from
        fp81s21_blockReconFun hH a k (y + z)) t =
      (show C(Icc (0 : ℝ) H, OscDual d m) from fp81s21_blockReconFun hH a k y) t +
        (show C(Icc (0 : ℝ) H, OscDual d m) from fp81s21_blockReconFun hH a k z) t
    rw [fp81s21_blockReconFun_apply, fp81s21_blockReconFun_apply,
      fp81s21_blockReconFun_apply, pcm_add, pcm_add,
      s56_evalA_add, s56_B_add, s56_B_add]
    abel
  map_smul' c y := by
    refine ContinuousMap.ext fun t => ?_
    change (show C(Icc (0 : ℝ) H, OscDual d m) from
        fp81s21_blockReconFun hH a k (c • y)) t =
      c • (show C(Icc (0 : ℝ) H, OscDual d m) from fp81s21_blockReconFun hH a k y) t
    rw [fp81s21_blockReconFun_apply, fp81s21_blockReconFun_apply,
      pcm_smul, pcm_smul, s56_evalA_smul, s56_B_smul, s56_B_smul]
    simp only [smul_sub, smul_add, RingHom.id_apply]

/-- The bounded linear unit-clock reconstruction into the observation path. -/
def fp81s21_blockRecon (hH : 0 ≤ H) (a : ℝ) (k : ℕ) :
    PathSp 1 (KSpace d m H) →L[ℝ] OscPath d m H :=
  (fp81s21_blockReconLin hH a k).mkContinuous (3 + Real.sqrt H) (by
    have hs : 0 ≤ Real.sqrt H := Real.sqrt_nonneg _
    intro y
    refine (ContinuousMap.norm_le
      (show C(Icc (0 : ℝ) H, OscDual d m) from fp81s21_blockReconFun hH a k y)
      (by positivity)).2 fun t => ?_
    rw [fp81s21_blockReconFun_apply]
    have hrec := u9_recon_norm_le hH
      (pcm y fp81s21_unitClockEndpoint) (pcm y (fp81s21_blockClock a k t)) (t : ℝ)
    have hterminal := norm_pcm_apply_le y fp81s21_unitClockEndpoint
    have hclock := norm_pcm_apply_le y (fp81s21_blockClock a k t)
    calc
      ‖(pcm y fp81s21_unitClockEndpoint).evalA (t : ℝ) -
          (pcm y fp81s21_unitClockEndpoint).B +
          (pcm y (fp81s21_blockClock a k t)).B‖
          ≤ (2 + Real.sqrt H) * ‖pcm y fp81s21_unitClockEndpoint‖ +
              ‖pcm y (fp81s21_blockClock a k t)‖ := hrec
      _ ≤ (2 + Real.sqrt H) * ‖y‖ + ‖y‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hterminal (by positivity)) hclock
      _ = (3 + Real.sqrt H) * ‖y‖ := by ring)

/-- Pointwise formula for the unit-clock block reconstruction. -/
theorem fp81s21_blockRecon_apply (hH : 0 ≤ H) (a : ℝ) (k : ℕ)
    (y : PathSp 1 (KSpace d m H)) (t : Icc (0 : ℝ) H) :
    (show C(Icc (0 : ℝ) H, OscDual d m) from fp81s21_blockRecon hH a k y) t =
      (pcm y fp81s21_unitClockEndpoint).evalA t -
        (pcm y fp81s21_unitClockEndpoint).B + (pcm y (fp81s21_blockClock a k t)).B := rfl

/-- The reconstruction operator norm does not depend on the block or its index. -/
theorem fp81s21_blockRecon_norm_le (hH : 0 ≤ H) (a : ℝ) (k : ℕ) :
    ‖fp81s21_blockRecon (d := d) (m := m) hH a k‖ ≤ 3 + Real.sqrt H :=
  LinearMap.mkContinuous_norm_le
    (fp81s21_blockReconLin (d := d) (m := m) hH a k) (by positivity) _

#print axioms fp81s21_blockRecon_apply
#print axioms fp81s21_blockRecon_norm_le
#print axioms fp81s21_blockClock_continuous

end HRS.Fp81.S21

end
