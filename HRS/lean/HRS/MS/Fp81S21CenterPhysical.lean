import HRS.MS.Fp81S21AvgPackageRetained
import HRS.MS.Fp81S21CenterCor2
import HRS.MS.Fp81S21CenterCor3
import HRS.MS.Fp81S21CoeffCenter2
import HRS.MS.Fp81S21CoeffCenter3
import HRS.MS.Fp81S21WickApprox39

/-! Centered SqErr consequences for the retained physical averaging package.
The first-moment exports retain the exact `MomentRep` selections: the retained
particle eta coefficient, and packet 31's particle/Gaussian linear and
quadratic coefficients. Zero means are exported only through the existing
Gaussian-centering and law-centered quadratic results. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.defProp false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

private theorem fp81s21_centerPhysical_sqErr_right_congr
    {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
    (P : Measure Ω) (f g g' : Ω → V) (ε : ℝ)
    (hgg' : g =ᵐ[P] g') (hSq : fp81s21_SqErr P f g ε) :
    fp81s21_SqErr P f g' ε := by
  have hErr : (fun ω => ‖f ω - g ω‖ ^ 2) =ᵐ[P]
      (fun ω => ‖f ω - g' ω‖ ^ 2) := by
    filter_upwards [hgg'] with ω hω
    simp [hω]
  refine ⟨hSq.1.congr hErr, ?_⟩
  calc
    (∫ ω, ‖f ω - g' ω‖ ^ 2 ∂P) =
        ∫ ω, ‖f ω - g ω‖ ^ 2 ∂P := integral_congr_ae hErr.symm
    _ ≤ ε ^ 2 := hSq.2

/-- Centering both variables under their common probability law costs the
factor two in the SqErr norm parameter. -/
theorem fp81s21_centerPhysical_SqErr
    {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → V) (ε : ℝ)
    (hε : 0 ≤ ε) (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hSq : fp81s21_SqErr P X Y ε) :
    fp81s21_SqErr P
      (fun ω => X ω - ∫ ω', X ω' ∂P)
      (fun ω => Y ω - ∫ ω', Y ω' ∂P) (2 * ε) := by
  let D : Ω → V := fun ω => X ω - Y ω
  let C : Ω → V := fun ω => (X ω - ∫ ω', X ω' ∂P) -
    (Y ω - ∫ ω', Y ω' ∂P)
  have hD : MemLp D 2 P := by exact hX.sub hY
  have hXc : MemLp (fun ω => X ω - ∫ ω', X ω' ∂P) 2 P :=
    hX.sub (memLp_const _)
  have hYc : MemLp (fun ω => Y ω - ∫ ω', Y ω' ∂P) 2 P :=
    hY.sub (memLp_const _)
  have hC : MemLp C 2 P := by exact hXc.sub hYc
  have hCenter : eLpNorm C 2 P ≤ 2 * eLpNorm D 2 P := by
    simpa [C, D] using HRS.Fp81.V01.fp81_s21_center_L2' X Y hX hY
  have hDformula : eLpNorm D 2 P =
      ENNReal.ofReal (Real.sqrt (∫ ω, ‖D ω‖ ^ 2 ∂P)) := by
    rw [hD.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp [Real.sqrt_eq_rpow]
  have hDbound : eLpNorm D 2 P ≤ ENNReal.ofReal ε := by
    rw [hDformula]
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_iff.mpr
    exact ⟨hε, by simpa [D] using hSq.2⟩
  have hCbound : eLpNorm C 2 P ≤ ENNReal.ofReal (2 * ε) := by
    calc
      eLpNorm C 2 P ≤ 2 * eLpNorm D 2 P := hCenter
      _ ≤ 2 * ENNReal.ofReal ε := by gcongr
      _ = ENNReal.ofReal (2 * ε) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  have hCint : Integrable (fun ω => ‖C ω‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hC.aestronglyMeasurable).1 hC
  have hCformula : eLpNorm C 2 P =
      ENNReal.ofReal (Real.sqrt (∫ ω, ‖C ω‖ ^ 2 ∂P)) := by
    rw [hC.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp [Real.sqrt_eq_rpow]
  have hCroot : Real.sqrt (∫ ω, ‖C ω‖ ^ 2 ∂P) ≤ 2 * ε := by
    have h := hCbound
    rw [hCformula] at h
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by norm_num) hε)).mp h
  have hCsq : (∫ ω, ‖C ω‖ ^ 2 ∂P) ≤ (2 * ε) ^ 2 := by
    have hI : 0 ≤ ∫ ω, ‖C ω‖ ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    rw [← Real.sq_sqrt hI]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) hε)).2 hCroot
  have hEq : (fun ω => ‖C ω‖ ^ 2) =ᵐ[P]
      (fun ω => ‖(X ω - ∫ ω', X ω' ∂P) -
        (Y ω - ∫ ω', Y ω' ∂P)‖ ^ 2) := by
    filter_upwards with ω
    rfl
  refine ⟨hCint.congr hEq, ?_⟩
  calc
    (∫ ω, ‖(X ω - ∫ ω', X ω' ∂P) -
        (Y ω - ∫ ω', Y ω' ∂P)‖ ^ 2 ∂P) =
      ∫ ω, ‖C ω‖ ^ 2 ∂P := integral_congr_ae hEq.symm
    _ ≤ (2 * ε) ^ 2 := hCsq

/-- The same estimate for a continuous-linear image, with the time-section
mean rewritten as the image of the original Bochner mean. -/
theorem fp81s21_centerPhysical_CLM_SqErr
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → X) (U : Ω → Y) (S : Y →L[ℝ] X) (ε : ℝ)
    (hε : 0 ≤ ε) (hf : MemLp f 2 P) (hU : MemLp U 2 P)
    (hSq : fp81s21_SqErr P f (fun ω => S (U ω)) ε) :
    fp81s21_SqErr P
      (fun ω => f ω - ∫ ω', f ω' ∂P)
      (fun ω => S (U ω - ∫ ω', U ω' ∂P)) (2 * ε) := by
  have hY : MemLp (fun ω => S (U ω)) 2 P := hU.continuousLinearMap_comp S
  have hRaw := fp81s21_centerPhysical_SqErr P f (fun ω => S (U ω)) ε
    hε hf hY hSq
  have hUInt : Integrable U P := hU.integrable one_le_two
  have hMean : (∫ ω, S (U ω) ∂P) = S (∫ ω, U ω ∂P) :=
    S.integral_comp_comm hUInt
  have hEq : (fun ω => S (U ω) - ∫ ω', S (U ω') ∂P) =ᵐ[P]
      (fun ω => S (U ω - ∫ ω', U ω' ∂P)) := by
    filter_upwards with ω
    rw [hMean]
    exact (map_sub S (U ω) (∫ ω', U ω' ∂P)).symm
  exact fp81s21_centerPhysical_sqErr_right_congr P _ _ _ _ hEq hRaw

/-- Apply the centered CLM estimate to the two fields and the common profile
provided at the leaf of `fp81s21_physical_avgPackage_retained`. -/
theorem fp81s21_centerPhysical_retained_avgPair
    {ΩN ΩG X Y : Type*} [MeasurableSpace ΩN] [MeasurableSpace ΩG]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (PN : Measure ΩN) [IsProbabilityMeasure PN]
    (PG : Measure ΩG) [IsProbabilityMeasure PG]
    (XN : ΩN → X) (UN : ΩN → Y) (XG : ΩG → X) (UG : ΩG → Y)
    (S : ℕ → Y →L[ℝ] X) (ω : ℕ → ℝ)
    (hXN : MemLp XN 2 PN) (hUN : MemLp UN 2 PN)
    (hXG : MemLp XG 2 PG) (hUG : MemLp UG 2 PG)
    (hω : ∀ k, 0 ≤ ω k)
    (hRaw : ∀ k, fp81s21_SqErr PN XN (fun ζ => S k (UN ζ)) (ω k) ∧
      fp81s21_SqErr PG XG (fun ζ => S k (UG ζ)) (ω k)) :
    ∀ k, fp81s21_SqErr PN
        (fun ζ => XN ζ - ∫ ζ', XN ζ' ∂PN)
        (fun ζ => S k (UN ζ - ∫ ζ', UN ζ' ∂PN)) (2 * ω k) ∧
      fp81s21_SqErr PG
        (fun ζ => XG ζ - ∫ ζ', XG ζ' ∂PG)
        (fun ζ => S k (UG ζ - ∫ ζ', UG ζ' ∂PG)) (2 * ω k) := by
  intro k
  exact ⟨fp81s21_centerPhysical_CLM_SqErr PN XN UN (S k) (ω k)
      (hω k) hXN hUN (hRaw k).1,
    fp81s21_centerPhysical_CLM_SqErr PG XG UG (S k) (ω k)
      (hω k) hXG hUG (hRaw k).2⟩

/-- The first-moment data attached to one exact coefficient selection. -/
structure fp81s21_MomentRepFirstMomentData
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ → Ω → (HRS.Euc d → ℝ) → ℝ)
    (q : ℝ → Ω → HRS.MS.R26T6.r26t6_Coeff) (M u : ℝ) : Prop where
  integrable : Integrable (q u) P
  dualNorm_firstMoment : AEMeasurable
      (fun ζ => HRS.Whole.dualNormE r Pw (Q u ζ)) P ∧
    (∫⁻ ζ, HRS.Whole.dualNormE r Pw (Q u ζ) ∂P) ≤
      ENNReal.ofReal (Real.sqrt M)

/-- First-moment integrability and the dual-norm bound for the exact
coefficient selected by a `MomentRep`; no centering is asserted here. -/
theorem fp81s21_centerPhysical_MomentRep_firstMoment
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : HRS.MS.R26T6.r26t6_WeightedChart d r Pw)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ → Ω → (HRS.Euc d → ℝ) → ℝ)
    (q : ℝ → Ω → HRS.MS.R26T6.r26t6_Coeff) (M u : ℝ)
    (hrep : fp81s21_MomentRep E P Q q M) (hu : 0 ≤ u) :
    fp81s21_MomentRepFirstMomentData (r := r) (Pw := Pw) P Q q M u := by
  exact ⟨(hrep.2 u hu).1.integrable one_le_two,
    fp81s21_MomentRep_firstMoment E P Q q M hrep u hu⟩

/-- At a retained-package leaf, `qN` represents the particle eta field in
the weak chart, so it is integrable and has the stated dual-norm first moment. -/
theorem fp81s21_centerPhysical_retained_particle_eta
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (E : HRS.MS.R26T6.r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (A : HRS.MS.R26T3.Particle R N)
    (qN : ℝ → A.Ω → HRS.MS.R26T6.r26t6_Coeff) (M2 u : ℝ)
    (hrep : fp81s21_MomentRep E A.P (fp81s21_particleEmpField R N A) qN M2)
    (hu : 0 ≤ u) :
    fp81s21_MomentRepFirstMomentData (r := 2 * p.d + 8)
      (Pw := (p.d : ℝ) + 2) A.P (fp81s21_particleEmpField R N A) qN M2 u :=
  fp81s21_centerPhysical_MomentRep_firstMoment E A.P _ qN M2 u hrep hu

/-- Strong and weak first-moment data for packet 31's exact particle eta and
law-centered quadratic selections. These do not assert zero mean. -/
theorem fp81s21_centerPhysical_S31_particle_firstMoments
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (εN εG εB : ℕ → ℝ) (S31 : fp81s21_Physical31 p R Es E εN εG εB)
    (N : ℕ) (hN : 2 ≤ N) (A : Particle R N) (u : ℝ) (hu : 0 ≤ u) :
    fp81s21_MomentRepFirstMomentData (r := 2 * p.d + 6) (Pw := (p.d : ℝ) + 4) (P := A.P)
      (Q := fp81s21_particleEmpField R N A) (S31.qsηN N hN A) S31.MN u ∧
    fp81s21_MomentRepFirstMomentData (r := 2 * p.d + 6) (Pw := (p.d : ℝ) + 4) (P := A.P)
      (Q := fp81s21_particleQuadField R N A) (S31.qsBN N hN A) S31.MN u ∧
    fp81s21_MomentRepFirstMomentData (r := 2 * p.d + 8) (Pw := (p.d : ℝ) + 2) (P := A.P)
      (Q := fp81s21_particleEmpField R N A)
      (fun v ζ => fp81s21_particle_embedField p Es E (S31.qsηN N hN A v ζ))
      S31.MN u ∧
    fp81s21_MomentRepFirstMomentData (r := 2 * p.d + 8) (Pw := (p.d : ℝ) + 2) (P := A.P)
      (Q := fp81s21_particleQuadField R N A)
      (fun v ζ => fp81s21_particle_embedField p Es E (S31.qsBN N hN A v ζ))
      S31.MN u := by
  rcases S31.particle N hN A with ⟨hη, hB, _, _, hηE, hBE, _⟩
  exact ⟨fp81s21_centerPhysical_MomentRep_firstMoment Es A.P _ _ S31.MN u hη hu,
    fp81s21_centerPhysical_MomentRep_firstMoment Es A.P _ _ S31.MN u hB hu,
    fp81s21_centerPhysical_MomentRep_firstMoment E A.P _ _ S31.MN u hηE hu,
    fp81s21_centerPhysical_MomentRep_firstMoment E A.P _ _ S31.MN u hBE hu⟩

/-- Strong and weak first-moment data for packet 31's exact Gaussian linear
selection. -/
theorem fp81s21_centerPhysical_S31_gaussian_linear_firstMoments
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (εN εG εB : ℕ → ℝ) (S31 : fp81s21_Physical31 p R Es E εN εG εB)
    (G : GaussianRealization R) (u : ℝ) (hu : 0 ≤ u) :
    fp81s21_MomentRepFirstMomentData (r := 2 * p.d + 6) (Pw := (p.d : ℝ) + 4) (P := G.P)
      (Q := fun v ζ f => OscDual.eval (G.Z v ζ) f) (S31.gaussian.qsηG G)
      S31.gaussian.MηG u ∧
    fp81s21_MomentRepFirstMomentData (r := 2 * p.d + 8) (Pw := (p.d : ℝ) + 2) (P := G.P)
      (Q := fun v ζ f => OscDual.eval (G.Z v ζ) f)
      (fp81s21_gaussian_embedFamily p Es E (S31.gaussian.qsηG G))
      S31.gaussian.MηG u := by
  have hLin := (S31.gaussian.gaussian_linear G).coefficients
  exact ⟨fp81s21_centerPhysical_MomentRep_firstMoment Es G.P _ _
      S31.gaussian.MηG u hLin.strong_momentRep hu,
    fp81s21_centerPhysical_MomentRep_firstMoment E G.P _ _
      S31.gaussian.MηG u hLin.weak_momentRep hu⟩

/-- Strong and weak first-moment data for packet 31's exact Gaussian Wick
selection. -/
theorem fp81s21_centerPhysical_S31_gaussian_wick_firstMoments
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (εN εG εB : ℕ → ℝ) (S31 : fp81s21_Physical31 p R Es E εN εG εB)
    (G : GaussianRealization R) (u : ℝ) (hu : 0 ≤ u) :
    fp81s21_MomentRepFirstMomentData (r := 2 * p.d + 6) (Pw := (p.d : ℝ) + 4) (P := G.P)
      (Q := fp81s21_wickChartField Es (S31.gaussian.quadratic.qs G))
      (S31.gaussian.quadratic.qs G)
      (S31.gaussian.quadratic.Kstar ^ 4 * S31.gaussian.quadratic.B / 2) u ∧
    fp81s21_MomentRepFirstMomentData (r := 2 * p.d + 8) (Pw := (p.d : ℝ) + 2) (P := G.P)
      (Q := fp81s21_wickChartField Es (S31.gaussian.quadratic.qs G))
      (S31.gaussian.quadratic.qe G)
      (S31.gaussian.quadratic.Kstar ^ 4 * S31.gaussian.quadratic.B / 2) u := by
  rcases S31.gaussian.quadratic.payload G with
    ⟨_, _, _, hB, hBe, _, _, _⟩
  exact ⟨fp81s21_centerPhysical_MomentRep_firstMoment Es G.P _ _
      (S31.gaussian.quadratic.Kstar ^ 4 * S31.gaussian.quadratic.B / 2) u hB hu,
    fp81s21_centerPhysical_MomentRep_firstMoment E G.P _ _
      (S31.gaussian.quadratic.Kstar ^ 4 * S31.gaussian.quadratic.B / 2) u hBe hu⟩

/-- Transfer a zero Bochner mean between two exact coefficient selections of
the same field and chart, when their `MomentRep`s prove they agree a.e. -/
theorem fp81s21_centerPhysical_transfer_mean
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw)
    (E : HRS.MS.R26T6.r26t6_WeightedChart d r Pw)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ → Ω → (HRS.Euc d → ℝ) → ℝ)
    (q q₀ : ℝ → Ω → HRS.MS.R26T6.r26t6_Coeff) (M M₀ u : ℝ)
    (hrep : fp81s21_MomentRep E P Q q M)
    (hrep₀ : fp81s21_MomentRep E P Q q₀ M₀)
    (hu : 0 ≤ u) (hmean : (∫ ζ, q₀ u ζ ∂P) = 0) :
    (∫ ζ, q u ζ ∂P) = 0 := by
  have hae := fp81s21_MomentRep_eq_ae hP E P Q q q₀ M M₀ hrep hrep₀ u hu
  calc
    (∫ ζ, q u ζ ∂P) = ∫ ζ, q₀ u ζ ∂P := integral_congr_ae hae
    _ = 0 := hmean

/-- Existing Gaussian-linear centering applies to its own strong and weak
representatives, selected from the centered Gaussian coordinate certificate. -/
def fp81s21_centerPhysical_gaussian_linear_centered :=
  fp81s21_gaussian_coord_firstMoment_center

/-- Existing Gaussian-Wick centering applies to its own selected strong and
weak `qsB`/`qB` representatives. -/
def fp81s21_centerPhysical_gaussian_wick_centered :=
  fp81s21_centerCor_gaussian_wick

/-- The particle quadratic export centers the field under the actual
particle law; its raw quadratic precursor is not claimed to be centered. -/
def fp81s21_centerPhysical_particleQuad_centered :=
  fp81s21_particleQuadCoeff_firstMoment_centered

#print axioms HRS.Fp81.S21.fp81s21_centerPhysical_SqErr
#print axioms HRS.Fp81.S21.fp81s21_centerPhysical_CLM_SqErr
#print axioms HRS.Fp81.S21.fp81s21_centerPhysical_retained_avgPair
#print axioms HRS.Fp81.S21.fp81s21_centerPhysical_MomentRep_firstMoment
#print axioms HRS.Fp81.S21.fp81s21_centerPhysical_retained_particle_eta
#print axioms HRS.Fp81.S21.fp81s21_centerPhysical_S31_particle_firstMoments
#print axioms HRS.Fp81.S21.fp81s21_centerPhysical_S31_gaussian_linear_firstMoments
#print axioms HRS.Fp81.S21.fp81s21_centerPhysical_S31_gaussian_wick_firstMoments
#print axioms HRS.Fp81.S21.fp81s21_centerPhysical_transfer_mean
#print axioms HRS.Fp81.S21.fp81s21_centerPhysical_gaussian_linear_centered
#print axioms HRS.Fp81.S21.fp81s21_centerPhysical_gaussian_wick_centered
#print axioms HRS.Fp81.S21.fp81s21_centerPhysical_particleQuad_centered

end HRS.Fp81.S21
end
