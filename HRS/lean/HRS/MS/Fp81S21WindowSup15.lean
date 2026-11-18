import HRS.MS.Fp81S21WindowSup14

/-!
# HRS S2.1(iii), SOL40 packet 9d: abstract two-time drift bound

The compiled definition is
`r2QuadField s μ P X v ω f = N * (pairEnergy (commutatorKernel d s
  (fun x => gradient f x)) (X v ω) μ - ∫ pairEnergy ... dP)`.
For a terminal-time family, its derivative has the form
`q(s,ω) + ∫_b^s k(v,s,ω) dv`, where `q` is the quadratic slice at test
`φ` and `k` is the slice at the propagated terminal derivative.  This file
proves the resulting `H + H²` path-supremum estimate from uniform fixed-slice
sixth moments and the stated pathwise derivative identity.  The actual moving
quadratic-field FTC and its two-time measurability remain field-specific.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HRS.Fp81.S21

private theorem fp81s21_window_interval_integral_sixth_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b s K : ℝ) (hbs : b ≤ s) (hK : 0 ≤ K)
    (k : ℝ → Ω → ℝ)
    (hk : Measurable (Function.uncurry k))
    (hki : ∀ ω, IntervalIntegrable (fun v => k v ω) volume b s)
    (hMoment : ∀ v ∈ Icc b s,
      (∫⁻ ω, (ENNReal.ofReal |k v ω|) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
        ENNReal.ofReal K) :
    (∫⁻ ω, (ENNReal.ofReal |∫ v in b..s, k v ω ∂volume|) ^ (6 : ℝ) ∂P) ^
        (1 / 6 : ℝ) ≤ ENNReal.ofReal ((s - b) * K) := by
  classical
  let J : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ v in Icc b s, ENNReal.ofReal |k v ω| ∂volume
  let f : ℝ → Ω → ℝ≥0∞ := fun v ω => ENNReal.ofReal |k v ω|
  have hAbsPoint (ω : Ω) :
      ENNReal.ofReal |∫ v in b..s, k v ω ∂volume| ≤ J ω := by
    have hkiAbs : IntervalIntegrable (fun v => |k v ω|) volume b s := by
      simpa only [Real.norm_eq_abs] using (hki ω).norm
    have hAbsIcc : IntegrableOn (fun v => |k v ω|) (Icc b s) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hbs).1 hkiAbs
    have hRealENN := ofReal_integral_eq_lintegral_ofReal hAbsIcc
      (Filter.Eventually.of_forall fun v => abs_nonneg (k v ω))
    have hIccEq :
        (∫ v in Icc b s, |k v ω| ∂volume) =
          ∫ v in b..s, |k v ω| ∂volume := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hbs]
    have hAbs := intervalIntegral.abs_integral_le_integral_abs
      (f := fun v => k v ω) (μ := volume) (a := b) (b := s) hbs
    calc
      ENNReal.ofReal |∫ v in b..s, k v ω ∂volume| ≤
          ENNReal.ofReal (∫ v in b..s, |k v ω| ∂volume) :=
        ENNReal.ofReal_le_ofReal hAbs
      _ = J ω := by
        dsimp [J]
        rw [← hIccEq]
        exact hRealENN
  have hkMeas : Measurable (Function.uncurry f) := by
    exact ENNReal.measurable_ofReal.comp
      (measurable_abs.comp hk)
  have hMink := fp81s21_lintegral_minkowski_six P
    (volume.restrict (Icc b s)) f hkMeas
  have hMinkLeft :
      (∫⁻ ω, J ω ^ (6 : ℕ) ∂P) ^ (1 / 6 : ℝ) ≤
        ∫⁻ v in Icc b s,
          (∫⁻ ω, (ENNReal.ofReal |k v ω|) ^ (6 : ℝ) ∂P) ^
            (1 / 6 : ℝ) ∂volume := by
    simpa [J, f] using hMink
  have hMinkRight :
      ∫⁻ v in Icc b s,
        (∫⁻ ω, (ENNReal.ofReal |k v ω|) ^ (6 : ℝ) ∂P) ^
          (1 / 6 : ℝ) ∂volume ≤ ENNReal.ofReal ((s - b) * K) := by
    calc
      _ ≤ ∫⁻ v in Icc b s, ENNReal.ofReal K ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
        exact hMoment v hv
      _ = ENNReal.ofReal ((s - b) * K) := by
        rw [lintegral_const]
        have hVol : volume (Icc b s) = ENNReal.ofReal (s - b) := by
          rw [Real.volume_Icc]
        rw [Measure.restrict_apply_univ, hVol]
        rw [← ENNReal.ofReal_mul hK]
        congr 1
        ring
  have hCompareNat :
      (∫⁻ ω, (ENNReal.ofReal |∫ v in b..s, k v ω ∂volume|) ^ (6 : ℕ) ∂P) ≤
        ∫⁻ ω, J ω ^ (6 : ℕ) ∂P := by
    apply lintegral_mono
    intro ω
    exact pow_le_pow_left₀ bot_le (hAbsPoint ω) 6
  have hLeftPower :
      (∫⁻ ω, (ENNReal.ofReal |∫ v in b..s, k v ω ∂volume|) ^ (6 : ℝ) ∂P) =
        ∫⁻ ω, (ENNReal.ofReal |∫ v in b..s, k v ω ∂volume|) ^ (6 : ℕ) ∂P := by
    apply lintegral_congr
    intro ω
    exact ENNReal.rpow_natCast _ 6
  have hJPower :
      (∫⁻ ω, J ω ^ (6 : ℝ) ∂P) = ∫⁻ ω, J ω ^ (6 : ℕ) ∂P := by
    apply lintegral_congr
    intro ω
    exact ENNReal.rpow_natCast (J ω) 6
  have hCompare :
      (∫⁻ ω, (ENNReal.ofReal |∫ v in b..s, k v ω ∂volume|) ^ (6 : ℝ) ∂P) ≤
        ∫⁻ ω, J ω ^ (6 : ℝ) ∂P := by
    rw [hLeftPower, hJPower]
    exact hCompareNat
  calc
    (∫⁻ ω, (ENNReal.ofReal |∫ v in b..s, k v ω ∂volume|) ^ (6 : ℝ) ∂P) ^
        (1 / 6 : ℝ) ≤ (∫⁻ ω, J ω ^ (6 : ℕ) ∂P) ^ (1 / 6 : ℝ) := by
          rw [← hJPower]
          exact ENNReal.rpow_le_rpow hCompare (by norm_num)
    _ ≤ ENNReal.ofReal ((s - b) * K) := hMinkLeft.trans hMinkRight

/-- Two uniform fixed-slice L⁶ bounds yield the `H + H²` upper-integral
supremum bound for an integrated drift path, provided its derivative is the
baseline slice plus a triangular time integral.  All suprema remain under
`lintegral`; no measurability of the path supremum is assumed. -/
theorem fp81s21_window_double_time_sup_sixth
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b H K : ℝ) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (q g : ℝ → Ω → ℝ) (k : ℝ → ℝ → Ω → ℝ)
    (hq : Measurable (Function.uncurry q))
    (hg : Measurable (Function.uncurry g))
    (hk : Measurable (Function.uncurry (Function.uncurry k)))
    (hgi : ∀ ω, IntervalIntegrable (fun s => g s ω) volume b (b + H))
    (hki : ∀ s ∈ Icc b (b + H), ∀ ω,
      IntervalIntegrable (fun v => k v s ω) volume b s)
    (hRep : ∀ s ∈ Icc b (b + H), ∀ ω,
      g s ω = q s ω + ∫ v in b..s, k v s ω ∂volume)
    (hqMoment : ∀ s ∈ Icc b (b + H),
      (∫⁻ ω, (ENNReal.ofReal |q s ω|) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
        ENNReal.ofReal K)
    (hkMoment : ∀ v ∈ Icc b (b + H), ∀ s ∈ Icc b (b + H),
      (∫⁻ ω, (ENNReal.ofReal |k v s ω|) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
        ENNReal.ofReal K) :
    (∫⁻ ω, (⨆ t : Icc b (b + H),
      ENNReal.ofReal |∫ s in b..(t : ℝ), g s ω ∂volume|) ^ (6 : ℝ) ∂P) ^
        (1 / 6 : ℝ) ≤ ENNReal.ofReal (K * (H + H ^ 2)) := by
  classical
  have hDerivativeMoment : ∀ s ∈ Icc b (b + H),
      (∫⁻ ω, (ENNReal.ofReal |g s ω|) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
        ENNReal.ofReal ((1 + H) * K) := by
    intro s hs
    have hbs : b ≤ s := hs.1
    have hKfixed (v : ℝ) (hv : v ∈ Icc b s) :
        (∫⁻ ω, (ENNReal.ofReal |k v s ω|) ^ (6 : ℝ) ∂P) ^
            (1 / 6 : ℝ) ≤ ENNReal.ofReal K :=
      hkMoment v (⟨hv.1, le_trans hv.2 hs.2⟩) s hs
    have hkFixedMeas : Measurable (Function.uncurry (fun v ω => k v s ω)) := by
      exact hk.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
    have hInner := fp81s21_window_interval_integral_sixth_bound P b s K hbs hK
      (fun v ω => k v s ω) hkFixedMeas (hki s hs) hKfixed
    let J : Ω → ℝ := fun ω => ∫ v in b..s, k v s ω ∂volume
    have hqFixed : Measurable (q s) := hq.comp (measurable_const.prodMk measurable_id)
    have hgFixed : Measurable (g s) := hg.comp (measurable_const.prodMk measurable_id)
    have hJeq : J = fun ω => g s ω - q s ω := by
      funext ω
      dsimp [J]
      rw [hRep s hs ω]
      ring
    have hJmeas : Measurable J := by
      rw [hJeq]
      exact hgFixed.sub hqFixed
    let Q : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal |q s ω|
    let J' : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal |J ω|
    have hQmeas : Measurable Q := ENNReal.measurable_ofReal.comp
      (measurable_abs.comp hqFixed)
    have hJ'meas : Measurable J' := ENNReal.measurable_ofReal.comp
      (measurable_abs.comp hJmeas)
    have hDom (ω : Ω) :
        ENNReal.ofReal |g s ω| ≤ Q ω + J' ω := by
      have hAbs : |g s ω| ≤ |q s ω| + |J ω| := by
        rw [hRep s hs ω]
        exact abs_add_le (q s ω) (J ω)
      calc
        ENNReal.ofReal |g s ω| ≤ ENNReal.ofReal (|q s ω| + |J ω|) :=
          ENNReal.ofReal_le_ofReal hAbs
        _ = Q ω + J' ω := by
          simp [Q, J', ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    have hDomMoment :
        (∫⁻ ω, (ENNReal.ofReal |g s ω|) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
          (∫⁻ ω, (Q ω + J' ω) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) := by
      apply ENNReal.rpow_le_rpow
      · apply lintegral_mono
        intro ω
        exact ENNReal.rpow_le_rpow (hDom ω) (by norm_num)
      · norm_num
    have hTriangle := ENNReal.lintegral_Lp_add_le (μ := P)
      hQmeas.aemeasurable hJ'meas.aemeasurable
      (by norm_num : 1 ≤ (6 : ℝ))
    have hQbound :
        (∫⁻ ω, Q ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤ ENNReal.ofReal K := by
      simpa [Q] using hqMoment s hs
    have hJbound :
        (∫⁻ ω, J' ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤ ENNReal.ofReal (H * K) := by
      have hInnerH : (s - b) * K ≤ H * K := by
        apply mul_le_mul_of_nonneg_right _ hK
        linarith [hs.2]
      calc
        _ ≤ ENNReal.ofReal ((s - b) * K) := by simpa [J, J'] using hInner
        _ ≤ ENNReal.ofReal (H * K) := ENNReal.ofReal_le_ofReal hInnerH
    have hSumBound :
        (∫⁻ ω, (Q ω + J' ω) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
          ENNReal.ofReal K + ENNReal.ofReal (H * K) := by
      exact hTriangle.trans (add_le_add hQbound hJbound)
    have hAddBound : ENNReal.ofReal K + ENNReal.ofReal (H * K) =
        ENNReal.ofReal ((1 + H) * K) := by
      rw [← ENNReal.ofReal_add hK (mul_nonneg hH hK)]
      congr 1
      ring
    exact hDomMoment.trans (hSumBound.trans_eq hAddBound)
  have hK' : 0 ≤ (1 + H) * K := mul_nonneg (by linarith) hK
  have hFinal := fp81s21_window_integral_sup_sixth_of_derivative_bound
    P b H ((1 + H) * K) hH hK' g hg hgi hDerivativeMoment
  have hEq : H * ((1 + H) * K) = K * (H + H ^ 2) := by ring
  simpa [hEq] using hFinal

#print axioms fp81s21_window_double_time_sup_sixth

end HRS.Fp81.S21

end
