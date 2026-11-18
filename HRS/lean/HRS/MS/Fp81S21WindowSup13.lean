import HRS.MS.Fp81S21WindowSup12
import HRS.MS.Fp81S21Radius
import HRS.MS.Fp81S21ParticleSixthSlices

/-!
# HRS S2.1(iii), SOL40 packet 9d: centered-coordinate adapters

The compiled definitions used here are `s102_zf P X ω u f = √N *
  (pair (empirical (X u ω)) f - pair (meanEmpirical (P.map (X u))) f)` and
`SixthBound P Y M = Integrable (fun ω => ‖Y ω‖^6) P ∧
  (∫ ω, ‖Y ω‖^6 ∂P) ≤ M`.  The source identity `s102_zf_eq` rewrites the first
definition as the reference-centered raw slice minus its own expectation.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open HRS.Whole HRS.MS.R2Interp HRS.MS.S21 HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.CovMeas

namespace HRS.Fp81.S21

/-- The sixth root factors through a nonnegative deterministic amplitude. -/
theorem fp81s21_real_sixth_root_product
    {C B a : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (ha : 0 ≤ a) :
    (C * (B * a) ^ 6) ^ (1 / 6 : ℝ) = C ^ (1 / 6 : ℝ) * B * a := by
  have hBa : 0 ≤ B * a := mul_nonneg hB ha
  rw [Real.mul_rpow hC (pow_nonneg hBa 6)]
  have hpow : ((B * a) ^ 6) ^ (1 / 6 : ℝ) = B * a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hBa]
    norm_num
  rw [hpow]
  ring

/-- Sixth power followed by its reciprocal power returns an `ENNReal`. -/
theorem fp81s21_ennreal_sixth_root_pow (x : ℝ≥0∞) :
    (x ^ (6 : ℝ)) ^ (1 / 6 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- The upper-integral sixth root of a real coordinate is its `eLpNorm`. -/
theorem fp81s21_lintegral_sixth_root_eq_eLpNorm
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y) :
    (∫⁻ ω, ENNReal.ofReal |Y ω| ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) =
      eLpNorm Y (ENNReal.ofReal 6) P := by
  rw [HRS.MS.R2Wfm.s97_lint_eq P Y hY.aestronglyMeasurable
    (r := 6) (by norm_num)]
  exact fp81s21_ennreal_sixth_root_pow _

/-- The centered empirical field is the reference-centered raw fluctuation
minus its own expectation. -/
theorem fp81s21_window_s102_zf_centered_raw
    {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) (u : ℝ)
    (hX : Measurable (X u.toNNReal)) (hN : 0 < N)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    {f : Euc d → ℝ} (hf : Measurable f) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, |f x| ≤ B) (ω : Ω) :
    s102_zf P X ω u f =
      Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ω)) f -
            HRS.Whole.pair μ f) -
        ∫ ω', Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ω')) f -
            HRS.Whole.pair μ f) ∂P := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hEmpMeas : Measurable (fun ω' : Ω =>
      HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ω')) f) :=
    (S45.s45_measurable_pair_empirical hN1 hf).comp hX
  have hEmpBound (ω' : Ω) :
      |HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ω')) f| ≤ B :=
    S45.s45_abs_pair_empirical_le hN1 hB (X u.toNNReal ω')
  have hEmpInt : Integrable
      (fun ω' : Ω => HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ω')) f) P :=
    Integrable.of_bound hEmpMeas.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω' => by
        rw [Real.norm_eq_abs]
        exact hEmpBound ω')
  let Q : Ω → ℝ := fun ω' =>
    HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ω')) f -
      HRS.Whole.pair μ f
  have hQInt : Integrable Q P := by
    dsimp [Q]
    exact hEmpInt.sub (integrable_const _)
  have hScale :
      (∫ ω', Real.sqrt N * Q ω' ∂P) =
        Real.sqrt N * ∫ ω', Q ω' ∂P := by
    exact integral_const_mul _ _
  rw [HRS.MS.R2Interp.s102_zf_eq hN P X u hX μ hf hB ω, hScale]
  dsimp [Q]
  ring

/-- A bounded test gives a deterministic pathwise bound on the centered
coordinate, sufficient for interval integrability of its time derivative. -/
theorem fp81s21_window_s102_zf_abs_bound
    {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) (u : ℝ)
    (hX : Measurable (X u.toNNReal)) (hN : 0 < N)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    {f : Euc d → ℝ} (hf : Measurable f) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, |f x| ≤ B) (ω : Ω) :
    |s102_zf P X ω u f| ≤ 4 * Real.sqrt N * B := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hμInt : Integrable f μ :=
    Integrable.of_bound hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hμBound : |HRS.Whole.pair μ f| ≤ B := by
    change |∫ x, f x ∂μ| ≤ B
    calc
      |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, B ∂μ := integral_mono_ae hμInt.abs (integrable_const B)
          (Filter.Eventually.of_forall fun x => hB x)
      _ = B := by simp
  have hEmpBound (ω' : Ω) :
      |HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ω')) f| ≤ B :=
    S45.s45_abs_pair_empirical_le hN1 hB (X u.toNNReal ω')
  let Y : Ω → ℝ := fun ω' => Real.sqrt N *
      (HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ω')) f -
        HRS.Whole.pair μ f)
  have hEmpMeas : Measurable (fun ω' : Ω =>
      HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ω')) f) :=
    (S45.s45_measurable_pair_empirical hN1 hf).comp hX
  have hYBound (ω' : Ω) : |Y ω'| ≤ 2 * Real.sqrt N * B := by
    dsimp [Y]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt N *
          |HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ω')) f -
            HRS.Whole.pair μ f| ≤
        Real.sqrt N *
          (|HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ω')) f| +
            |HRS.Whole.pair μ f|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt N * (B + B) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (hEmpBound ω') hμBound) (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt N * B := by ring
  have hYMeas : Measurable Y := by
    dsimp [Y]
    exact measurable_const.mul (hEmpMeas.sub_const _)
  have hYInt : Integrable Y P :=
    Integrable.of_bound hYMeas.aestronglyMeasurable (2 * Real.sqrt N * B)
      (Filter.Eventually.of_forall fun ω' => by
        rw [Real.norm_eq_abs]
        exact hYBound ω')
  have hMeanBound : |∫ ω', Y ω' ∂P| ≤ 2 * Real.sqrt N * B := by
    calc
      |∫ ω', Y ω' ∂P| ≤ ∫ ω', |Y ω'| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω', 2 * Real.sqrt N * B ∂P :=
          integral_mono_ae hYInt.abs (integrable_const _)
            (Filter.Eventually.of_forall hYBound)
      _ = 2 * Real.sqrt N * B := by simp
  have hCentered := fp81s21_window_s102_zf_centered_raw P X u hX hN μ hf
    hB0 hB ω
  change |s102_zf P X ω u f| ≤ _
  rw [hCentered]
  calc
    |Y ω - ∫ ω', Y ω' ∂P| ≤ |Y ω| + |∫ ω', Y ω' ∂P| := abs_sub _ _
    _ ≤ 2 * Real.sqrt N * B + 2 * Real.sqrt N * B :=
        add_le_add (hYBound ω) hMeanBound
    _ = 4 * Real.sqrt N * B := by ring

/-- The wR29 reference-centered sixth-moment slice controls the exactly
centered `s102_zf` coordinate after the generic factor-two centering cost. -/
theorem fp81s21_window_s102_zf_eLpNorm_bound
    {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) (u : ℝ)
    (hX : Measurable (X u.toNNReal)) (hN : 0 < N)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    {f : Euc d → ℝ} (hf : Measurable f) {B C : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, |f x| ≤ B)
    (hC0 : 0 ≤ C)
    (hSlice : SixthBound P
      (fun ω => Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ω)) f -
          HRS.Whole.pair μ f)) (C * B ^ 6)) :
    eLpNorm (fun ω => s102_zf P X ω u f) (ENNReal.ofReal 6) P ≤
      ENNReal.ofReal (2 * C ^ (1 / 6 : ℝ) * B) := by
  classical
  let Y : Ω → ℝ := fun ω => Real.sqrt N *
      (HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ω)) f -
        HRS.Whole.pair μ f)
  have hEmpMeas : Measurable (fun ω : Ω =>
      HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ω)) f) :=
    (S45.s45_measurable_pair_empirical (Nat.succ_le_of_lt hN) hf).comp hX
  have hYmeas : Measurable Y := by
    dsimp [Y]
    exact measurable_const.mul (hEmpMeas.sub_const _)
  have hCenter :
      (fun ω => s102_zf P X ω u f) = fun ω => Y ω - ∫ ω', Y ω' ∂P := by
    funext ω
    exact fp81s21_window_s102_zf_centered_raw P X u hX hN μ hf
      hB0 hB ω
  have hCentered0 := fp81s21_centered_sixth_eLpNorm P Y hYmeas
    (C * B ^ 6) hSlice
  have hCentered :
      eLpNorm (fun ω => Y ω - ∫ ω', Y ω' ∂P) (ENNReal.ofReal 6) P ≤
        2 * eLpNorm Y (ENNReal.ofReal 6) P := by
    simpa using hCentered0
  have hRaw := fp81s21_sixthBound_eLpNorm P Y (C * B ^ 6) hYmeas
    (mul_nonneg hC0 (pow_nonneg hB0 6)) hSlice
  have hRoot : (C * B ^ 6) ^ (1 / 6 : ℝ) = C ^ (1 / 6 : ℝ) * B := by
    simpa using fp81s21_real_sixth_root_product hC0 hB0 (by norm_num : (0 : ℝ) ≤ 1)
  rw [hCenter]
  calc
    eLpNorm (fun ω => Y ω - ∫ ω', Y ω' ∂P) (ENNReal.ofReal 6) P ≤
        2 * eLpNorm Y (ENNReal.ofReal 6) P := hCentered
    _ ≤ 2 * ENNReal.ofReal ((C * B ^ 6) ^ (1 / 6 : ℝ)) :=
      by gcongr
    _ = ENNReal.ofReal (2 * ((C * B ^ 6) ^ (1 / 6 : ℝ))) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    _ = ENNReal.ofReal (2 * C ^ (1 / 6 : ℝ) * B) := by rw [hRoot]; ring

/-- Initial-coordinate supremum bound on every shifted finite window. The
supremum is kept under `lintegral`, so no measurability of the path supremum is
claimed. -/
theorem fp81s21_window_initial_sup_sixth (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ H : ℝ, 0 < H → ∀ N : ℕ, 2 ≤ N →
            ∀ A : Particle R N, ∀ b : ℝ, 0 ≤ b →
              ∀ α : MultiIndex p.d,
                (∫⁻ ω, (⨆ t : Icc b (b + H),
                  ENNReal.ofReal (abs (s102_zf A.P A.X ω b
                    (propagatorW (r26t3_coeff R) b (t : ℝ)
                      (oscTestFun (wholeSpaceIndex p.d : ℝ) α))))) ^ (6 : ℝ) ∂A.P) ^
                    (1 / 6 : ℝ) ≤
                  ENNReal.ofReal (C * (1 + H) * s104_b p.d α) := by
  classical
  obtain ⟨δCommon, Co, co, hδCommon, hδCommonHalf, hco, hCommon⟩ :=
    fp81s21_common_radius p
  obtain ⟨δMoment, hδMoment, hδMomentHalf, hMoment⟩ :=
    fp81s21_particle_sixth_slices p
  obtain ⟨δOrbit, hδOrbit, hδOrbitHalf, hOrbit⟩ :=
    fp81s21_window_zero_order_orbit_bound_all_horizons p
  let δ0 : ℝ := min δCommon (min δMoment δOrbit)
  have hδ0 : 0 < δ0 := by
    dsimp [δ0]
    exact lt_min hδCommon (lt_min hδMoment hδOrbit)
  have hδ0half : δ0 ≤ 1 / 2 := by
    dsimp [δ0]
    exact (min_le_left _ _).trans hδCommonHalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  have hδC : δ ≤ δCommon := hδle.trans (min_le_left _ _)
  have hδM : δ ≤ δMoment :=
    hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδO : δ ≤ δOrbit :=
    hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hClaims, _hHex, hTerm, _hWindow⟩ :=
    hCommon δ hδ hδC R.ρβ R.thermal
  obtain ⟨Cmom, hCmom, hMomAt⟩ := hMoment δ hδ hδM R
  obtain ⟨Borb, hBorb, hOrbitAt⟩ := hOrbit δ hδ hδO R
  let Csup : ℝ := 2 * Cmom ^ (1 / 6 : ℝ) * Borb
  have hCsup : 0 ≤ Csup := by
    dsimp [Csup]
    positivity
  refine ⟨Csup, hCsup, ?_⟩
  intro H hH N hN A b hb α
  let T : ℝ := b + H
  have hT : 0 < T := by dsimp [T]; linarith
  have hbT : b ∈ Icc (0 : ℝ) T := by
    constructor
    · exact hb
    · dsimp [T]
      linarith
  obtain ⟨_cOrbit, hData⟩ :=
    fp81s21_moving_s101data_of_common p R hT hClaims hTerm
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ0half
  have hρb : HRS.Whole.IsProbDensity (R.ρ b) :=
    ((HRS.MS.R26T3.r26t3_reference_data p δ hδ hδhalf R).2.2.1 b hb).1
  let μ : Measure (Euc p.d) := HRS.MS.R26T3.r26t3_mu R b
  haveI hμ : IsProbabilityMeasure μ := HRS.Whole.U1.u1_isProb hρb
  have hNpos : 0 < N := by omega
  have hX : Measurable (A.X b.toNNReal) :=
    (A.strong T).adapted b.toNNReal
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let Cw := r26t3_coeff R
  let φ : Euc p.d → ℝ := oscTestFun m α
  have hbEnd : b ∈ Icc b T := by
    constructor
    · exact le_rfl
    · dsimp [T]
      linarith
  have hFmeas : Measurable (propagatorW Cw b b φ) := by
    simpa [Cw, m, φ] using
    (hData.smoothU α b hbT b hbEnd).continuous.measurable
  let f : Euc p.d → ℝ := propagatorW Cw b b φ
  have hfmeas : Measurable f := by simpa [f] using hFmeas
  let q : ℝ → Euc p.d → ℝ := fun s x => s101Th Cw m T b s α x
  have hqjoint : Measurable (Function.uncurry q) := by
    dsimp [q, Cw, m, T]
    exact fp81s21_s101Th_joint_measurable hData hbT α
  have hqmeas (s : ℝ) : Measurable (q s) :=
    hqjoint.comp (measurable_const.prodMk measurable_id)
  let Bamp : ℝ := Borb * s104_b p.d α
  have hBamp : 0 ≤ Bamp := by
    dsimp [Bamp]
    exact mul_nonneg hBorb (HRS.MS.R2WinErr.s104_b_nonneg α)
  have hFbound (t : ℝ) (ht : t ∈ Icc b T) (x : Euc p.d) :
      |propagatorW Cw b t φ x| ≤ Bamp := by
    exact (hOrbitAt H hH b hb α t (by simpa [T] using ht) x).1
  have hQbound (s : ℝ) (x : Euc p.d) : |q s x| ≤ Bamp := by
    by_cases hs : b < s ∧ s ≤ T
    · have hs' : s ∈ Icc b T := ⟨hs.1.le, hs.2⟩
      simpa [q, s101Th, hs, Cw, m, T] using
        (hOrbitAt H hH b hb α s (by simpa [T] using hs') x).2
    · simpa [q, s101Th, hs] using hBamp
  let cfun : A.Ω → ℝ := fun ω => s102_zf A.P A.X ω b f
  let gfun : ℝ → A.Ω → ℝ := fun s ω => s102_zf A.P A.X ω b (q s)
  have hcFamily : Measurable (fun z : ℝ × A.Ω =>
      s102_zf A.P A.X z.2 b ((fun _ : ℝ => f) z.1)) := by
    exact fp81s21_s102_zf_family_measurable A.P A.X b hX hNpos
      (fun _ : ℝ => f) (hfmeas.comp measurable_snd)
  have hc : Measurable cfun := by
    dsimp [cfun]
    let e : A.Ω → ℝ × A.Ω := fun ω => (b, ω)
    have he : Measurable e := measurable_const.prodMk measurable_id
    change Measurable (fun ω =>
      (fun z : ℝ × A.Ω =>
        s102_zf A.P A.X z.2 b ((fun _ : ℝ => f) z.1)) (e ω))
    exact hcFamily.comp he
  have hg : Measurable (Function.uncurry gfun) := by
    dsimp [gfun]
    exact fp81s21_s102_zf_family_measurable A.P A.X b hX hNpos q hqjoint
  have hGbound (s : ℝ) (ω : A.Ω) :
      |gfun s ω| ≤ 4 * Real.sqrt N * Bamp := by
    exact fp81s21_window_s102_zf_abs_bound A.P A.X b hX hNpos μ
      (hqmeas s) hBamp (hQbound s) ω
  have hgi : ∀ ω, IntervalIntegrable (fun s => gfun s ω) volume b (b + H) := by
    intro ω
    let e : ℝ → ℝ × A.Ω := fun s => (s, ω)
    have he : Measurable e := measurable_id.prodMk measurable_const
    have hsection : Measurable (fun s : ℝ => gfun s ω) := by
      change Measurable ((Function.uncurry gfun) ∘ e)
      exact hg.comp he
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := 4 * Real.sqrt N * Bamp)
      measure_Ioc_lt_top.ne hsection.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]
      exact hGbound s ω
  have hMomentNorm (f' : Euc p.d → ℝ) (hf' : Measurable f')
      (hfb' : ∀ x, |f' x| ≤ Bamp) :
      eLpNorm (fun ω => s102_zf A.P A.X ω b f') (ENNReal.ofReal 6) A.P ≤
        ENNReal.ofReal (Csup * s104_b p.d α) := by
    have hSlice := (hMomAt N hN A b hb Bamp hBamp).2 f' hf' hfb'
    have hbound := fp81s21_window_s102_zf_eLpNorm_bound
      (P := A.P) (X := A.X) (u := b) hX hNpos μ (B := Bamp) (C := Cmom)
      hf' hBamp hfb' hCmom hSlice
    calc
      _ ≤ ENNReal.ofReal (2 * Cmom ^ (1 / 6 : ℝ) * Bamp) := hbound
      _ = ENNReal.ofReal (Csup * s104_b p.d α) := by
        dsimp [Bamp, Csup]
        congr 1
        ring
  have hcLp :
      (∫⁻ ω, (ENNReal.ofReal |cfun ω|) ^ (6 : ℝ) ∂A.P) ^ (1 / 6 : ℝ) ≤
        ENNReal.ofReal (Csup * s104_b p.d α) := by
    rw [fp81s21_lintegral_sixth_root_eq_eLpNorm A.P cfun hc]
    exact hMomentNorm f hfmeas (hFbound b hbEnd)
  have hgLp (s : ℝ) :
      (∫⁻ ω, (ENNReal.ofReal |gfun s ω|) ^ (6 : ℝ) ∂A.P) ^ (1 / 6 : ℝ) ≤
        ENNReal.ofReal (Csup * s104_b p.d α) := by
    let es : A.Ω → ℝ × A.Ω := fun ω => (s, ω)
    have hes : Measurable es := measurable_const.prodMk measurable_id
    have hGs : Measurable (gfun s) := by
      change Measurable ((Function.uncurry gfun) ∘ es)
      exact hg.comp hes
    rw [fp81s21_lintegral_sixth_root_eq_eLpNorm A.P (gfun s) hGs]
    exact hMomentNorm (q s) (hqmeas s) (hQbound s)
  have hSupAbstract := fp81s21_window_lintegral_sup_bound A.P b H cfun gfun
    hc hg hH.le hgi
  have hTermIntegral :
      (∫⁻ s in Icc b (b + H),
        (∫⁻ ω, (ENNReal.ofReal |gfun s ω|) ^ (6 : ℝ) ∂A.P) ^
          (1 / 6 : ℝ) ∂volume) ≤
        ENNReal.ofReal (H * (Csup * s104_b p.d α)) := by
    calc
      _ ≤ ∫⁻ s in Icc b (b + H), ENNReal.ofReal (Csup * s104_b p.d α) ∂volume := by
        apply lintegral_mono
        intro s
        exact hgLp s
      _ = ENNReal.ofReal (H * (Csup * s104_b p.d α)) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ,
          Set.univ_inter, Real.volume_Icc]
        simp [hH.le]
        exact mul_comm _ _
  have hFTC (ω : A.Ω) (t : ℝ) (ht : t ∈ Icc b (b + H)) :
      s102_zf A.P A.X ω b (propagatorW Cw b t φ) =
        cfun ω + ∫ s in b..t, gfun s ω := by
    have h := fp81s21_window_s102_zf_ftc A.P A.X hData hbT
      (by simpa [T] using ht) hX hNpos α ω
    simpa [cfun, gfun, q, Cw, m, T, f, φ] using h
  have hSupEq (ω : A.Ω) :
      (⨆ t : Icc b (b + H), ENNReal.ofReal (abs
        (s102_zf A.P A.X ω b (propagatorW Cw b (t : ℝ) φ)))) =
      ⨆ t : Icc b (b + H), ENNReal.ofReal (abs
        (cfun ω + ∫ s in b..(t : ℝ), gfun s ω)) := by
    apply iSup_congr
    intro t
    rw [hFTC ω t t.property]
  have hPathIntegralEq :
      (∫⁻ ω, (⨆ t : Icc b (b + H), ENNReal.ofReal (abs
        (s102_zf A.P A.X ω b (propagatorW Cw b (t : ℝ) φ)))) ^ (6 : ℝ) ∂A.P) =
      ∫⁻ ω, (⨆ t : Icc b (b + H), ENNReal.ofReal (abs
        (cfun ω + ∫ s in b..(t : ℝ), gfun s ω))) ^ (6 : ℝ) ∂A.P := by
    apply lintegral_congr
    intro ω
    rw [hSupEq ω]
  calc
    (∫⁻ ω, (⨆ t : Icc b (b + H), ENNReal.ofReal (abs
        (s102_zf A.P A.X ω b (propagatorW Cw b (t : ℝ) φ)))) ^ (6 : ℝ) ∂A.P) ^
        (1 / 6 : ℝ) =
      (∫⁻ ω, (⨆ t : Icc b (b + H), ENNReal.ofReal (abs
        (cfun ω + ∫ s in b..(t : ℝ), gfun s ω))) ^ (6 : ℝ) ∂A.P) ^
        (1 / 6 : ℝ) := by rw [hPathIntegralEq]
    _ ≤ (∫⁻ ω, (ENNReal.ofReal |cfun ω|) ^ (6 : ℝ) ∂A.P) ^
          (1 / 6 : ℝ) +
        ∫⁻ s in Icc b (b + H),
          (∫⁻ ω, (ENNReal.ofReal |gfun s ω|) ^ (6 : ℝ) ∂A.P) ^
            (1 / 6 : ℝ) ∂volume := hSupAbstract
    _ ≤ ENNReal.ofReal (Csup * s104_b p.d α) +
        ENNReal.ofReal (H * (Csup * s104_b p.d α)) :=
      add_le_add hcLp hTermIntegral
    _ = ENNReal.ofReal (Csup * (1 + H) * s104_b p.d α) := by
      have hK0 : 0 ≤ Csup * s104_b p.d α :=
        mul_nonneg hCsup (HRS.MS.R2WinErr.s104_b_nonneg α)
      have hHK0 : 0 ≤ H * (Csup * s104_b p.d α) :=
        mul_nonneg hH.le hK0
      rw [← ENNReal.ofReal_add hK0 hHK0]
      congr 1
      ring
    _ = ENNReal.ofReal (Csup * (1 + H) * s104_b p.d α) := rfl

#print axioms fp81s21_real_sixth_root_product
#print axioms fp81s21_ennreal_sixth_root_pow
#print axioms fp81s21_lintegral_sixth_root_eq_eLpNorm
#print axioms fp81s21_window_s102_zf_centered_raw
#print axioms fp81s21_window_s102_zf_abs_bound
#print axioms fp81s21_window_s102_zf_eLpNorm_bound
#print axioms fp81s21_window_initial_sup_sixth

end HRS.Fp81.S21

end
