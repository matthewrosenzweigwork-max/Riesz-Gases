import HRS.Uniform.Q48eAux1
import HRS.MS.Fp81S21WindowMeas3
import HRS.MS.Fp81S21UnitCov2

/-!
# S2.1(iii), packet 16a-2: localized unit-clock window density

A block index is a natural number, embedded into physical time by `↑k`. The
localized density is zero outside the unit clock interval and outside the
physical set `I ∩ [0,a+H]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.MS.CovMeas HRS.MS.FixEq HRS.MS.R2WinErr

variable {d : ℕ}

/-- Unit-clock restriction of the measurable window representative to a
physical measurable set and one natural-number block. -/
def fp81s21_windowLocalD (I : Set ℝ) (k : ℕ) (C : WholeCoeff d)
    (m H a : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (s : ℝ) : KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ :=
  if s ∈ Icc (0 : ℝ) 1 ∧ (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H) then
    fp81s21_windowDm C m H a z ha hH ((k : ℝ) + s)
  else 0

lemma fp81s21_windowLocalD_apply (I : Set ℝ) (k : ℕ) (C : WholeCoeff d)
    (m H a : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (s : ℝ) (u w : KSpace d m H) :
    fp81s21_windowLocalD I k C m H a z ha hH s u w =
      if s ∈ Icc (0 : ℝ) 1 ∧ (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H) then
        fp81s21_windowDm C m H a z ha hH ((k : ℝ) + s) u w
      else 0 := by
  classical
  by_cases h : s ∈ Icc (0 : ℝ) 1 ∧
      (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H)
  · simp only [fp81s21_windowLocalD, if_pos h]
  · simp only [fp81s21_windowLocalD, if_neg h]
    simp

/-- Input data for the localized density. `fp81s21_hPos` is the time-dependent
positive-order feature bound; the global envelope used to choose the measurable
representative is derived at `v = a`. -/
structure fp81s21_WindowLocalInput
    {d : ℕ} (C : WholeCoeff d) (m H a : ℝ) (r : ℕ) (P : ℝ)
    (z : ℝ → (Euc d → ℝ) → ℝ) (Cmix cdec : ℝ) : Prop where
  fp81s21_hd : 1 ≤ d
  fp81s21_hH : 0 < H
  fp81s21_ha : 0 ≤ a
  fp81s21_horb : R2OrbitSummable C m (a + H) r
  fp81s21_hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ α : MultiIndex d, ∀ x : Euc d,
    propagatorW C v v (oscTestFun m α) x = oscTestFun m α x
  fp81s21_hz : IsR2L1F r P (a + H) z
  fp81s21_hP : (d : ℝ) < 2 * P
  fp81s21_hm : R2JIntegrandMeas C m (a + H) z
  fp81s21_hCmix : 0 ≤ Cmix
  fp81s21_hcdec : 0 < cdec
  fp81s21_hPos : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ j : ℕ,
    1 ≤ j → j ≤ r + 1 → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (fp81s21_window_feature C m H a v) x‖ ≤
        fp81s21_window_feature_Bpos d r H Cmix cdec a v

/-- The decay profile is dominated by the uniform envelope fixed at the
observation start. -/
theorem fp81s21_windowLocalInput_hPosEnvelope
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec) :
    ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 →
      ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fp81s21_window_feature C m H a v) x‖ ≤
        fp81s21_window_feature_Bpos d r H Cmix cdec a a := by
  intro v hv j hj1 hj2 x
  have hA : 0 ≤ 2 + (d : ℝ) ^ (r + 1) *
      ((volume.restrict (Icc (0 : ℝ) H)) Set.univ).toReal ^ (1 / 2 : ℝ) := by
    positivity
  have hQ : 0 ≤ Cmix * Real.sqrt (∑' α : MultiIndex d, (s104_b d α) ^ 2) :=
    mul_nonneg D.fp81s21_hCmix (Real.sqrt_nonneg _)
  have he : Real.exp (-cdec * max (a - v) 0) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hm : 0 ≤ max (a - v) 0 := le_max_right _ _
    have hmul : 0 ≤ cdec * max (a - v) 0 :=
      mul_nonneg D.fp81s21_hcdec.le hm
    nlinarith
  have hea : Real.exp (-cdec * max (a - a) 0) = 1 := by simp
  have hb : fp81s21_window_feature_Bpos d r H Cmix cdec a v ≤
      fp81s21_window_feature_Bpos d r H Cmix cdec a a := by
    unfold fp81s21_window_feature_Bpos fp81s21_window_Bpos
    rw [hea]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hQ) hA
  exact (D.fp81s21_hPos v hv j hj1 hj2 x).trans hb

/-- The block interval, clipped to the physical history. -/
def fp81s21_windowLocalBlock (a H : ℝ) (k : ℕ) : Set ℝ :=
  Icc (k : ℝ) ((k : ℝ) + 1) ∩ Icc (0 : ℝ) (a + H)

/-- The weighted feature envelope at a physical time is bounded by its
uniform value at the observation start. -/
lemma fp81s21_windowLocal_featureB_le_envelope
    (d r : ℕ) (H Cmix cdec a v : ℝ) (hcdec : 0 < cdec)
    (hCmix : 0 ≤ Cmix) :
    fp81s21_window_feature_Bpos d r H Cmix cdec a v ≤
      fp81s21_window_feature_Bpos d r H Cmix cdec a a := by
  unfold fp81s21_window_feature_Bpos fp81s21_window_Bpos
  have hA : 0 ≤ 2 + (d : ℝ) ^ (r + 1) *
      ((volume.restrict (Icc (0 : ℝ) H)) Set.univ).toReal ^ (1 / 2 : ℝ) := by
    positivity
  have hQ : 0 ≤ Cmix * Real.sqrt (∑' α : MultiIndex d, (s104_b d α) ^ 2) :=
    mul_nonneg hCmix (Real.sqrt_nonneg _)
  have he : Real.exp (-cdec * max (a - v) 0) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hm : 0 ≤ max (a - v) 0 := le_max_right _ _
    have hmul : 0 ≤ cdec * max (a - v) 0 := mul_nonneg hcdec.le hm
    nlinarith
  have hea : Real.exp (-cdec * max (a - a) 0) = 1 := by simp
  rw [hea]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hQ) hA

theorem fp81s21_windowLocal_entries_measurable
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    {I : Set ℝ} (hI : MeasurableSet I) (k : ℕ) :
    ∀ x y, Measurable fun s => fp81s21_windowLocalD I k C m H a z
      D.fp81s21_ha (le_of_lt D.fp81s21_hH) s x y := by
  intro x y
  have hD := fp81s21_windowDm_meas_entries D.fp81s21_hd D.fp81s21_hH
    D.fp81s21_ha D.fp81s21_horb D.fp81s21_hterminal D.fp81s21_hz D.fp81s21_hP
    D.fp81s21_hm (fp81s21_windowLocalInput_hPosEnvelope D) x y
  have hcomp : Measurable fun s =>
      fp81s21_windowDm C m H a z D.fp81s21_ha (le_of_lt D.fp81s21_hH)
        ((k : ℝ) + s) x y :=
    hD.comp (measurable_const.add measurable_id)
  have hset : MeasurableSet {s : ℝ | s ∈ Icc (0 : ℝ) 1 ∧
      (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H)} := by
    exact measurableSet_Icc.inter
      ((hI.inter measurableSet_Icc).preimage (measurable_const.add measurable_id))
  have hfun : (fun s => fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
      (le_of_lt D.fp81s21_hH) s x y) = fun s =>
        if s ∈ Icc (0 : ℝ) 1 ∧ (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H)
        then fp81s21_windowDm C m H a z D.fp81s21_ha (le_of_lt D.fp81s21_hH)
          ((k : ℝ) + s) x y else 0 := by
    funext s
    exact fp81s21_windowLocalD_apply I k C m H a z D.fp81s21_ha
      (le_of_lt D.fp81s21_hH) s x y
  rw [hfun]
  exact Measurable.ite hset hcomp measurable_const

theorem fp81s21_windowLocal_symm
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec) (I : Set ℝ) (k : ℕ) :
    ∀ s u w, fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
      (le_of_lt D.fp81s21_hH) s u w =
      fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) s w u := by
  intro s u w
  by_cases h : s ∈ Icc (0 : ℝ) 1 ∧ (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H)
  · rw [fp81s21_windowLocalD_apply, if_pos h,
      fp81s21_windowLocalD_apply, if_pos h]
    exact fp81s21_windowDm_symm D.fp81s21_hd D.fp81s21_hH D.fp81s21_ha
      D.fp81s21_horb D.fp81s21_hz D.fp81s21_hP D.fp81s21_hm ((k : ℝ) + s) u w
  · rw [fp81s21_windowLocalD_apply, if_neg h,
      fp81s21_windowLocalD_apply, if_neg h]

theorem fp81s21_windowLocal_bddOrthonormalSums
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (I : Set ℝ) (k : ℕ) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      BddAbove (Set.range fun p : OrthonormalPairs (KSpace d m H) =>
        ∑ i, |fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s (p.1.2.1 i) (p.1.2.2 i)|) := by
  obtain ⟨G, hG, hspec⟩ := fp81s21_windowDm_good_spec
    D.fp81s21_hd D.fp81s21_hH D.fp81s21_ha D.fp81s21_horb D.fp81s21_hterminal
    D.fp81s21_hz D.fp81s21_hP D.fp81s21_hm (fp81s21_windowLocalInput_hPosEnvelope D)
  intro s hs
  by_cases hloc : (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H)
  · have hv : (k : ℝ) + s ∈ Icc (0 : ℝ) (a + H) := hloc.2
    by_cases hgood : (k : ℝ) + s ∈ G
    · have hd := fp81s21_windowD_data D.fp81s21_hd D.fp81s21_hH
        D.fp81s21_ha D.fp81s21_horb D.fp81s21_hterminal D.fp81s21_hz D.fp81s21_hP
        hv (D.fp81s21_hPos ((k : ℝ) + s) hv)
      have heq : fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s = fp81s21_windowD C m H a z ((k : ℝ) + s) := by
        rw [fp81s21_windowLocalD, if_pos ⟨hs, hloc⟩, hspec, if_pos hgood]
      rw [heq]
      exact hd.2.2.1
    · have heq : fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s = 0 := by
        rw [fp81s21_windowLocalD, if_pos ⟨hs, hloc⟩, hspec, if_neg hgood]
      rw [heq]
      refine ⟨0, ?_⟩
      rintro _ ⟨p, rfl⟩
      simp
  · have heq : fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) s = 0 := by
      unfold fp81s21_windowLocalD
      rw [if_neg (fun hh => hloc hh.2)]
    rw [heq]
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    simp

/-- Translate a set integral on the unit clock to the corresponding physical
block interval, keeping an arbitrary measurable indicator set. -/
lemma fp81s21_windowLocal_lintegral_shift
    (F : ℝ → ℝ≥0∞) (S : Set ℝ) (hS : MeasurableSet S) (k : ℕ) :
    (∫⁻ s in Icc (0 : ℝ) 1, S.indicator F ((k : ℝ) + s)) =
    ∫⁻ v in Icc (k : ℝ) ((k : ℝ) + 1) ∩ S, F v := by
  calc
    (∫⁻ s in Icc (0 : ℝ) 1, S.indicator F ((k : ℝ) + s)) =
        ∫⁻ v in Icc (k : ℝ) ((k : ℝ) + 1), S.indicator F v :=
      HRS.Uniform.Q48e.lintegral_Icc_shift (S.indicator F) (k : ℝ) 1
    _ = ∫⁻ v in Icc (k : ℝ) ((k : ℝ) + 1) ∩ S, F v := by
      rw [lintegral_indicator hS, Measure.restrict_restrict hS, Set.inter_comm]

/-- The trace bound with the uniform envelope, used to establish integrability
of the localized trace norm. -/
theorem fp81s21_windowLocal_trace_bound_envelope
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (I : Set ℝ) (k : ℕ) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      ENNReal.ofReal (HRS.traceNormForm
        (fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s)) ≤
        if (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H) then
          ENNReal.ofReal |2 * C.ν| * dualNormE r P (z ((k : ℝ) + s)) *
            ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r *
              (fp81s21_window_feature_Bpos d r H Cmix cdec a a) ^ 2))
        else 0 := by
  intro s hs
  by_cases hloc : (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H)
  · have hlocal : fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) s =
        fp81s21_windowDm C m H a z D.fp81s21_ha (le_of_lt D.fp81s21_hH)
          ((k : ℝ) + s) := by
      unfold fp81s21_windowLocalD
      rw [if_pos ⟨hs, hloc⟩]
    rw [hlocal]
    simpa [hloc] using fp81s21_windowDm_trace_bound D.fp81s21_hd D.fp81s21_hH
      D.fp81s21_ha D.fp81s21_horb D.fp81s21_hterminal D.fp81s21_hz D.fp81s21_hP
      D.fp81s21_hm (fp81s21_windowLocalInput_hPosEnvelope D) ((k : ℝ) + s) hloc.2
  · have hlocal : fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) s = 0 := by
      unfold fp81s21_windowLocalD
      rw [if_neg (fun hh => hloc hh.2)]
    rw [hlocal, traceNormForm_zero_eq]
    simp [hloc]

/-- At every unit-clock time, the localized trace norm is bounded using the
physical-time decay profile. The profile remains inside the pointwise bound. -/
theorem fp81s21_windowLocal_trace_bound_weighted
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (I : Set ℝ) (k : ℕ) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      ENNReal.ofReal (HRS.traceNormForm
        (fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s)) ≤
        if (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H) then
          ENNReal.ofReal |2 * C.ν| * dualNormE r P (z ((k : ℝ) + s)) *
            ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r *
              (fp81s21_window_feature_Bpos d r H Cmix cdec a ((k : ℝ) + s)) ^ 2))
        else 0 := by
  classical
  obtain ⟨G, hG, hspec⟩ := fp81s21_windowDm_good_spec
    D.fp81s21_hd D.fp81s21_hH D.fp81s21_ha D.fp81s21_horb D.fp81s21_hterminal
    D.fp81s21_hz D.fp81s21_hP D.fp81s21_hm (fp81s21_windowLocalInput_hPosEnvelope D)
  intro s hs
  by_cases hloc : (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H)
  · have hv : (k : ℝ) + s ∈ Icc (0 : ℝ) (a + H) := hloc.2
    have hlocal : fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) s =
        fp81s21_windowDm C m H a z D.fp81s21_ha (le_of_lt D.fp81s21_hH)
          ((k : ℝ) + s) := by
      unfold fp81s21_windowLocalD
      rw [if_pos ⟨hs, hloc⟩]
    by_cases hgood : (k : ℝ) + s ∈ G
    · have hdata := fp81s21_windowD_data D.fp81s21_hd D.fp81s21_hH
        D.fp81s21_ha D.fp81s21_horb D.fp81s21_hterminal D.fp81s21_hz D.fp81s21_hP
        hv (D.fp81s21_hPos ((k : ℝ) + s) hv)
      rw [hlocal, hspec, if_pos hgood]
      simpa [hloc] using hdata.2.2.2
    · rw [hlocal, hspec, if_neg hgood]
      rw [traceNormForm_zero_eq]
      simp [hloc]
  · have hlocal : fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) s = 0 := by
      unfold fp81s21_windowLocalD
      rw [if_neg (fun hh => hloc hh.2)]
    rw [hlocal, traceNormForm_zero_eq]
    simp [hloc]

/-- Translated local trace bound over the clipped physical block. The decay
factor remains inside the integral through the feature profile. -/
theorem fp81s21_windowLocal_lintegral_bound_weighted
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    {I : Set ℝ} (hI : MeasurableSet I) (k : ℕ) :
    ∫⁻ s in Icc (0 : ℝ) 1,
      ENNReal.ofReal (HRS.traceNormForm
        (fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s)) ≤
      ∫⁻ v in fp81s21_windowLocalBlock a H k ∩ I,
        ENNReal.ofReal |2 * C.ν| * dualNormE r P (z v) *
          ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r *
            (fp81s21_window_feature_Bpos d r H Cmix cdec a v) ^ 2)) := by
  let F : ℝ → ℝ≥0∞ := fun v =>
    ENNReal.ofReal |2 * C.ν| * dualNormE r P (z v) *
      ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r *
        (fp81s21_window_feature_Bpos d r H Cmix cdec a v) ^ 2))
  have hS : MeasurableSet (I ∩ Icc (0 : ℝ) (a + H)) := hI.inter measurableSet_Icc
  have hset : Icc (k : ℝ) ((k : ℝ) + 1) ∩ (I ∩ Icc (0 : ℝ) (a + H)) =
      fp81s21_windowLocalBlock a H k ∩ I := by
    ext v
    simp [fp81s21_windowLocalBlock, and_assoc, and_left_comm, and_comm]
  calc
    ∫⁻ s in Icc (0 : ℝ) 1,
        ENNReal.ofReal (HRS.traceNormForm
          (fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
            (le_of_lt D.fp81s21_hH) s)) ≤
        ∫⁻ s in Icc (0 : ℝ) 1,
          (I ∩ Icc (0 : ℝ) (a + H)).indicator F ((k : ℝ) + s) := by
      refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
      have hbound := fp81s21_windowLocal_trace_bound_weighted D I k s hs
      by_cases hloc : (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H)
      · simpa [F, Set.indicator, hloc] using hbound
      · simpa [F, Set.indicator, hloc] using hbound
    _ = ∫⁻ v in Icc (k : ℝ) ((k : ℝ) + 1) ∩
          (I ∩ Icc (0 : ℝ) (a + H)), F v :=
        fp81s21_windowLocal_lintegral_shift F (I ∩ Icc (0 : ℝ) (a + H)) hS k
    _ = ∫⁻ v in fp81s21_windowLocalBlock a H k ∩ I, F v := by rw [hset]

/-- Integrability on the unit clock, obtained from the uniform trace envelope
and the physical `IsR2L1F` lintegral hypothesis. -/
theorem fp81s21_windowLocal_trace_integrable
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    {I : Set ℝ} (hI : MeasurableSet I) (k : ℕ) :
    IntegrableOn
      (fun s => HRS.traceNormForm
        (fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s)) (Icc (0 : ℝ) 1) := by
  let K : ℝ≥0∞ := ENNReal.ofReal |2 * C.ν| *
    ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r *
      (fp81s21_window_feature_Bpos d r H Cmix cdec a a) ^ 2))
  let S : Set ℝ := fp81s21_windowLocalBlock a H k ∩ I
  let F : ℝ → ℝ≥0∞ := fun v => K * dualNormE r P (z v)
  have hSmeas : MeasurableSet (I ∩ Icc (0 : ℝ) (a + H)) :=
    hI.inter measurableSet_Icc
  have hK : K < ⊤ := by
    dsimp [K]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hKne : K ≠ ⊤ := ne_of_lt hK
  have hsub : S ⊆ Icc (0 : ℝ) (a + H) := by
    intro v hv
    exact hv.1.2
  have hbound :
      ∫⁻ s in Icc (0 : ℝ) 1,
        ENNReal.ofReal (HRS.traceNormForm
          (fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
            (le_of_lt D.fp81s21_hH) s)) ≤
        ∫⁻ v in S, F v := by
    calc
      ∫⁻ s in Icc (0 : ℝ) 1,
          ENNReal.ofReal (HRS.traceNormForm
            (fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
              (le_of_lt D.fp81s21_hH) s)) ≤
        ∫⁻ s in Icc (0 : ℝ) 1,
          (I ∩ Icc (0 : ℝ) (a + H)).indicator F ((k : ℝ) + s) := by
          refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
          have hbound := fp81s21_windowLocal_trace_bound_envelope D I k s hs
          by_cases hloc : (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H)
          · simpa [K, F, Set.indicator, hloc, mul_assoc, mul_left_comm, mul_comm]
              using hbound
          · simpa [K, F, Set.indicator, hloc, mul_assoc, mul_left_comm, mul_comm]
              using hbound
      _ = ∫⁻ v in Icc (k : ℝ) ((k : ℝ) + 1) ∩
            (I ∩ Icc (0 : ℝ) (a + H)), F v :=
          fp81s21_windowLocal_lintegral_shift F
            (I ∩ Icc (0 : ℝ) (a + H)) hSmeas k
      _ = ∫⁻ v in S, F v := by
          have hsets : Icc (k : ℝ) ((k : ℝ) + 1) ∩
              (I ∩ Icc (0 : ℝ) (a + H)) = S := by
            ext v
            simp [S, fp81s21_windowLocalBlock, and_assoc, and_left_comm, and_comm]
          rw [hsets]
  have hfull : ∫⁻ v in Icc (0 : ℝ) (a + H), dualNormE r P (z v) < ⊤ :=
    D.fp81s21_hz.2.2
  have hsetfinite : ∫⁻ v in S, F v < ⊤ := by
    calc
      ∫⁻ v in S, F v = K * ∫⁻ v in S, dualNormE r P (z v) := by
        dsimp [F]
        rw [lintegral_const_mul' _ _ hKne]
      _ ≤ K * ∫⁻ v in Icc (0 : ℝ) (a + H), dualNormE r P (z v) :=
        by
          gcongr
      _ < ⊤ := ENNReal.mul_lt_top hK hfull
  have hfinite :
      ∫⁻ s in Icc (0 : ℝ) 1,
        ENNReal.ofReal (HRS.traceNormForm
          (fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
            (le_of_lt D.fp81s21_hH) s)) < ⊤ := lt_of_le_of_lt hbound hsetfinite
  have hmeasEntries := fp81s21_windowLocal_entries_measurable D hI k
  have hmeas : Measurable fun s => HRS.traceNormForm
      (fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) s) :=
    HRS.measurable_traceNormForm _ hmeasEntries
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun s => HRS.traceNormForm_nonneg _)]
  exact hfinite

/-- Covariance density addition after compression, almost everywhere on the
physical history. -/
theorem fp81s21_windowDm_add_ae
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z z' : ℝ → (Euc d → ℝ) → ℝ}
    (A : S101Adm C m (a + H) r P z) (A' : S101Adm C m (a + H) r P z')
    (ha : 0 ≤ a) (hH : 0 < H) :
    ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) (a + H))),
      fp81s21_windowDm C m H a (z + z') ha (le_of_lt hH) v =
        fp81s21_windowDm C m H a z ha (le_of_lt hH) v +
          fp81s21_windowDm C m H a z' ha (le_of_lt hH) v := by
  have hL : 0 ≤ a + H := by linarith
  filter_upwards [s101_Dm_ae_add A A' hL,
    ae_restrict_mem measurableSet_Icc] with v hdm hv
  ext u w
  by_cases hle : v ≤ a
  · simp [fp81s21_windowDm, hv, hle, hdm,
      HRS.Uniform.Kot.formComp_apply, ContinuousLinearMap.add_apply]
  · simp [fp81s21_windowDm, hv, hle, hdm,
      HRS.Uniform.Kot.formComp_apply, ContinuousLinearMap.add_apply]

/-- Covariance density scalar homogeneity after compression, almost everywhere
on the physical history. -/
theorem fp81s21_windowDm_smul_ae
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} (A : S101Adm C m (a + H) r P z)
    (ha : 0 ≤ a) (hH : 0 < H) (c : ℝ) :
    ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) (a + H))),
      fp81s21_windowDm C m H a (c • z) ha (le_of_lt hH) v =
        c • fp81s21_windowDm C m H a z ha (le_of_lt hH) v := by
  have hL : 0 ≤ a + H := by linarith
  filter_upwards [s101_Dm_ae_smul c A hL,
    ae_restrict_mem measurableSet_Icc] with v hdm hv
  ext u w
  by_cases hle : v ≤ a
  · simp [fp81s21_windowDm, hv, hle, hdm,
      HRS.Uniform.Kot.formComp_apply, ContinuousLinearMap.smul_apply]
  · simp [fp81s21_windowDm, hv, hle, hdm,
      HRS.Uniform.Kot.formComp_apply, ContinuousLinearMap.smul_apply]

/-- Addition commutes almost everywhere with measurable indicator localization
and translation to the unit clock. -/
theorem fp81s21_windowLocal_add_ae
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z z' : ℝ → (Euc d → ℝ) → ℝ}
    (A : S101Adm C m (a + H) r P z) (A' : S101Adm C m (a + H) r P z')
    (ha : 0 ≤ a) (hH : 0 < H) (I : Set ℝ) (k : ℕ) :
    ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)),
      fp81s21_windowLocalD I k C m H a (z + z') ha (le_of_lt hH) s =
        fp81s21_windowLocalD I k C m H a z ha (le_of_lt hH) s +
          fp81s21_windowLocalD I k C m H a z' ha (le_of_lt hH) s := by
  let J : Set ℝ := Icc (k : ℝ) ((k : ℝ) + 1)
  let Tset : Set ℝ := Icc (0 : ℝ) (a + H)
  have hphys := fp81s21_windowDm_add_ae A A' ha hH
  have hambient : ∀ᵐ v ∂volume, v ∈ Tset →
      fp81s21_windowDm C m H a (z + z') ha (le_of_lt hH) v =
        fp81s21_windowDm C m H a z ha (le_of_lt hH) v +
          fp81s21_windowDm C m H a z' ha (le_of_lt hH) v := by
    rw [ae_restrict_iff' measurableSet_Icc] at hphys
    simpa [Tset] using hphys
  have hblock : ∀ᵐ v ∂(volume.restrict J), v ∈ Tset →
      fp81s21_windowDm C m H a (z + z') ha (le_of_lt hH) v =
        fp81s21_windowDm C m H a z ha (le_of_lt hH) v +
          fp81s21_windowDm C m H a z' ha (le_of_lt hH) v := by
    rw [ae_restrict_iff' (by simp [J] : MeasurableSet J)]
    filter_upwards [hambient] with v hv hJ
    exact hv
  have hmp := fp81s21_window_shift_measurePreserving (k : ℝ) 1
  have hunit := hmp.quasiMeasurePreserving.ae hblock
  filter_upwards [hunit, ae_restrict_mem measurableSet_Icc] with s hsum hs
  by_cases hloc : (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H)
  · have hdm := hsum hloc.2
    ext u w
    have hdm' := congrArg (fun F => F u w) hdm
    simpa [fp81s21_windowLocalD, hs, hloc] using hdm'
  ·
    ext u w
    simp [fp81s21_windowLocalD_apply, hs, hloc]

/-- Scalar homogeneity commutes almost everywhere with measurable indicator
localization and translation to the unit clock. -/
theorem fp81s21_windowLocal_smul_ae
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} (A : S101Adm C m (a + H) r P z)
    (ha : 0 ≤ a) (hH : 0 < H) (c : ℝ) (I : Set ℝ) (k : ℕ) :
    ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)),
      fp81s21_windowLocalD I k C m H a (c • z) ha (le_of_lt hH) s =
        c • fp81s21_windowLocalD I k C m H a z ha (le_of_lt hH) s := by
  let J : Set ℝ := Icc (k : ℝ) ((k : ℝ) + 1)
  let Tset : Set ℝ := Icc (0 : ℝ) (a + H)
  have hphys := fp81s21_windowDm_smul_ae A ha hH c
  have hambient : ∀ᵐ v ∂volume, v ∈ Tset →
      fp81s21_windowDm C m H a (c • z) ha (le_of_lt hH) v =
        c • fp81s21_windowDm C m H a z ha (le_of_lt hH) v := by
    rw [ae_restrict_iff' measurableSet_Icc] at hphys
    simpa [Tset] using hphys
  have hblock : ∀ᵐ v ∂(volume.restrict J), v ∈ Tset →
      fp81s21_windowDm C m H a (c • z) ha (le_of_lt hH) v =
        c • fp81s21_windowDm C m H a z ha (le_of_lt hH) v := by
    rw [ae_restrict_iff' (by simp [J] : MeasurableSet J)]
    filter_upwards [hambient] with v hv hJ
    exact hv
  have hmp := fp81s21_window_shift_measurePreserving (k : ℝ) 1
  have hunit := hmp.quasiMeasurePreserving.ae hblock
  filter_upwards [hunit, ae_restrict_mem measurableSet_Icc] with s hscale hs
  ext u w
  by_cases hloc : (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H)
  · have hdm := hscale hloc.2
    have hdm' := congrArg (fun F => F u w) hdm
    simpa [fp81s21_windowLocalD, hs, hloc] using hdm'
  · simp [fp81s21_windowLocalD, hs, hloc]

/-- The translated density has the raw window-form specification almost
everywhere on the restricted unit clock. The restriction to the physical
block is explicit in the measure-preserving translation argument. -/
theorem fp81s21_windowLocal_ae_raw_spec
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (I : Set ℝ) (k : ℕ) :
    ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ u w,
      fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) s u w =
      if (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H) then
        2 * C.ν * z ((k : ℝ) + s)
          (s101Fm (fp81s21_window_feature C m H a ((k : ℝ) + s))
            (s101Rk u w))
      else 0 := by
  let J : Set ℝ := Icc (k : ℝ) ((k : ℝ) + 1)
  let Tset : Set ℝ := Icc (0 : ℝ) (a + H)
  have hphys := fp81s21_windowDm_ae_eq_windowD
    D.fp81s21_hd D.fp81s21_hH D.fp81s21_ha D.fp81s21_horb
    D.fp81s21_hterminal D.fp81s21_hz D.fp81s21_hP D.fp81s21_hm
    (fp81s21_windowLocalInput_hPosEnvelope D)
  have hambient : ∀ᵐ v ∂volume, v ∈ Tset →
      fp81s21_windowDm C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) v = fp81s21_windowD C m H a z v := by
    rw [ae_restrict_iff' measurableSet_Icc] at hphys
    simpa [Tset] using hphys
  have hblock : ∀ᵐ v ∂(volume.restrict J), v ∈ Tset →
      fp81s21_windowDm C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) v = fp81s21_windowD C m H a z v := by
    rw [ae_restrict_iff' (by simp [J] : MeasurableSet J)]
    filter_upwards [hambient] with v hv hJ
    exact hv
  have hmp := fp81s21_window_shift_measurePreserving (k : ℝ) 1
  have hunit := hmp.quasiMeasurePreserving.ae hblock
  filter_upwards [hunit, ae_restrict_mem measurableSet_Icc] with s hdm hs
  intro u w
  by_cases hloc : (k : ℝ) + s ∈ I ∩ Icc (0 : ℝ) (a + H)
  · have hv := hloc.2
    have hraw := (fp81s21_windowD_data D.fp81s21_hd D.fp81s21_hH
      D.fp81s21_ha D.fp81s21_horb D.fp81s21_hterminal D.fp81s21_hz
      D.fp81s21_hP hv (D.fp81s21_hPos ((k : ℝ) + s) hv)).1 u w
    have hdm' := hdm hv
    simp [fp81s21_windowLocalD, hs, hloc, hdm', hraw]
  · simp [fp81s21_windowLocalD, hs, hloc]

/-- All five clauses of the unit-clock trace-density interface required by
`fp81s21_unitCov_congr`. This is exported after the measurable, pointwise,
integral, and translated-form clauses above. -/
theorem fp81s21_windowLocal_isTraceDensityL1
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    {I : Set ℝ} (hI : MeasurableSet I) (k : ℕ) :
    IsTraceDensityL1 1
      (fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fp81s21_windowLocal_symm D I k
  · intro s hs
    exact fp81s21_windowLocal_bddOrthonormalSums D I k s hs
  · exact fp81s21_windowLocal_entries_measurable D hI k
  · exact fp81s21_windowLocal_trace_integrable D hI k

#print axioms fp81s21_windowLocalD_apply
#print axioms fp81s21_windowLocal_featureB_le_envelope
#print axioms fp81s21_windowLocalInput_hPosEnvelope
#print axioms fp81s21_windowLocal_entries_measurable
#print axioms fp81s21_windowLocal_symm
#print axioms fp81s21_windowLocal_bddOrthonormalSums
#print axioms fp81s21_windowLocal_trace_bound_weighted
#print axioms fp81s21_windowLocal_lintegral_shift
#print axioms fp81s21_windowLocal_trace_bound_envelope
#print axioms fp81s21_windowLocal_lintegral_bound_weighted
#print axioms fp81s21_windowLocal_trace_integrable
#print axioms fp81s21_windowLocal_isTraceDensityL1
#print axioms fp81s21_windowDm_add_ae
#print axioms fp81s21_windowDm_smul_ae
#print axioms fp81s21_windowLocal_add_ae
#print axioms fp81s21_windowLocal_smul_ae
#print axioms fp81s21_windowLocal_ae_raw_spec

end HRS.Fp81.S21

end
