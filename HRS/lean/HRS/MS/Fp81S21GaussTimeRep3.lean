import HRS.MS.Fp81S21GaussTimeRep2
import HRS.MS.Fp81S21TimeRep15

/-!
The linear Gaussian field has a canonical weighted extension through its
embedded chart coefficients. The raw oscillator evaluation is identified
with this extension on compact tests only; propagated-test identification is
a separate obligation.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
open HRS.MS.R2Interp

local instance fp81s21_gaussTimeRep3_measSpace (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_gaussTimeRep3_borelSpace (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

universe u v w

private theorem fp81s21_gaussian_transport_projection
    {α : Sort u} {P : α → Sort v} {Q : α → Sort w}
    (f : ∀ a, P a → Q a) {a b : α} (h : a = b) (x : P a) :
    f b (h ▸ x) = h ▸ f a x := by
  cases h
  rfl

/-- The canonical weighted extension of a Gaussian coefficient field.
For every coefficient vector, this is a weighted-continuous linear
functional; it is not defined by the totalized raw oscillator tsum. -/
noncomputable def fp81s21_gaussian_Qhat
    {d r : ℕ} {Pw : ℝ} {Ω : Type*}
    (E : r26t6_WeightedChart d r Pw)
    (q : ℝ → Ω → r26t6_Coeff) :
    ℝ → Ω → (Euc d → ℝ) → ℝ :=
  fun u ω f => fp81s21_chartAction E (q u ω) f

/-- The scalar coefficient size is the Hilbert norm of the canonical
embedded Gaussian representative. -/
def fp81s21_gaussian_C
    {Ω : Type*} (q : ℝ → Ω → r26t6_Coeff) :
    ℝ → Ω → ℝ :=
  fun u ω => ‖q u ω‖

/-- All fixed-chart linear Gaussian conclusions for one chosen strong
representative and its canonical weak-chart embedding. The raw oscillator
identity is asserted only on compact tests. -/
structure fp81s21_gaussian_canonical_payload
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (M : ℝ) (qs : ℝ → Ω → r26t6_Coeff)
    (q : ℝ → Ω → r26t6_Coeff) (ε : ℕ → ℝ) : Prop where
  strong_momentRep :
    fp81s21_MomentRep Es P Q qs M
  strong_firstMoment :
    ∀ u : ℝ, 0 ≤ u →
      AEMeasurable (fun ω => dualNormE (2 * p.d + 6)
        ((p.d : ℝ) + 4) (Q u ω)) P ∧
      (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
        (Q u ω) ∂P) ≤ ENNReal.ofReal (Real.sqrt M)
  weak_momentRep :
    fp81s21_MomentRep E P Q q M
  weak_firstMoment :
    ∀ u : ℝ, 0 ≤ u →
      AEMeasurable (fun ω => dualNormE (2 * p.d + 8)
        ((p.d : ℝ) + 2) (Q u ω)) P ∧
      (∫⁻ ω, dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
        (Q u ω) ∂P) ≤ ENNReal.ofReal (Real.sqrt M)
  compact_agreement :
    ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
      ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) H)).prod P),
        ∀ f, IsR2Test f →
          fp81s21_chartAction E (q (a + z.1) z.2) f =
            Q (a + z.1) z.2 f
  time_sections :
    ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
      ∃ U : Ω → Lp r26t6_Coeff 2
          (volume.restrict (Set.Icc (0 : ℝ) H)),
        fp81s21_TimeL2Rep P q M a H U ∧
        ∀ m : ℕ,
          fp81s21_SqErr P U
            (fun ω => fp81s21_timeProject H m (U ω))
            (Real.sqrt (H * M) * ε m) ∧
          ∀ ρ : ℝ, 0 < ρ →
            P {ω | ρ < ‖U ω - fp81s21_timeProject H m (U ω)‖} ≤
              ENNReal.ofReal (H * M * (ε m) ^ 2 / ρ ^ 2)

/-- The canonical weighted Gaussian contract: the coefficient moment and
pointwise weighted extension are both explicit, and the same time section
has a full TimeRep plus the projection and Markov tails. The inherited raw
oscillator identification remains compact-test only. -/
structure fp81s21_gaussian_canonical_time_payload
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (M : ℝ) (qs : ℝ → Ω → r26t6_Coeff)
    (q : ℝ → Ω → r26t6_Coeff) (ε : ℕ → ℝ) : Prop where
  coefficients :
    fp81s21_gaussian_canonical_payload p Es E P Q M qs q ε
  coefficient_secondMoment :
    ∀ u : ℝ, 0 ≤ u →
      (∫ ω, fp81s21_gaussian_C q u ω ^ 2 ∂P) ≤ M
  weighted_compatibility :
    ∀ u : ℝ, ∀ ω : Ω,
      S102Z (2 * p.d + 8) ((p.d : ℝ) + 2)
        (fp81s21_gaussian_Qhat E q u ω)
  time_representation :
    ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
      ∃ U : Ω → Lp r26t6_Coeff 2
          (volume.restrict (Set.Icc (0 : ℝ) H)),
        fp81s21_TimeRep E P (fp81s21_gaussian_Qhat E q) q M a H U ∧
        ∀ m : ℕ,
          fp81s21_SqErr P U
            (fun ω => fp81s21_timeProject H m (U ω))
            (Real.sqrt (H * M) * ε m) ∧
          ∀ ρ : ℝ, 0 < ρ →
            P {ω | ρ < ‖U ω - fp81s21_timeProject H m (U ω)‖} ≤
              ENNReal.ofReal (H * M * (ε m) ^ 2 / ρ ^ 2)

private theorem fp81s21_gaussian_normalizedStrong
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4)
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Q : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (qs : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hstrong : fp81s21_MomentRep Es P Q qs M) :
    fp81s21_MomentRep (hExp.symm ▸ Es) P Q qs M := by
  let Pkg : ℝ → Type := fun w =>
    PSigma fun Eη : r26t6_WeightedChart p.d (2 * p.d + 6) w =>
      fp81s21_MomentRep Eη P Q qs M
  let hPkg : Pkg ((p.d : ℝ) + 4) := ⟨Es, hstrong⟩
  let hPkg' : Pkg (((p.d : ℝ) + 2) + 2) := hExp.symm ▸ hPkg
  have hcast := fp81s21_gaussian_transport_projection
    (fun w (x : Pkg w) => x.1) hExp.symm hPkg
  have hchart : hPkg'.1 = hExp.symm ▸ Es := by
    simpa [hPkg', hPkg, Pkg] using hcast
  rw [← hchart]
  exact hPkg'.2

private theorem fp81s21_gaussian_payload_of_sections
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (M : ℝ) (qs q : ℝ → Ω → r26t6_Coeff) (ε : ℕ → ℝ)
    (hM : 0 ≤ M) (hε : ∀ m, 0 ≤ ε m)
    (hstrong : fp81s21_MomentRep Es P Q qs M)
    (hweak : fp81s21_MomentRep E P Q q M)
    (hqmeas : Measurable (Function.uncurry q))
    (htime : ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
      ∃ U : Ω → Lp r26t6_Coeff 2
          (volume.restrict (Set.Icc (0 : ℝ) H)),
        fp81s21_TimeL2Rep P q M a H U ∧
        ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) H)).prod P),
          ∀ f, IsR2Test f →
            fp81s21_chartAction E (q (a + z.1) z.2) f =
              Q (a + z.1) z.2 f)
    (htail : ∀ m u, 0 ≤ u →
      Integrable (fun ω => ‖q u ω - fp81s21_projectField m (q u ω)‖ ^ 2) P ∧
      (∫ ω, ‖q u ω - fp81s21_projectField m (q u ω)‖ ^ 2 ∂P) ≤
        M * (ε m) ^ 2) :
    fp81s21_gaussian_canonical_payload p Es E P Q M qs q ε := by
  have hfirstStrong : ∀ u : ℝ, 0 ≤ u →
      AEMeasurable (fun ω => dualNormE (2 * p.d + 6)
        ((p.d : ℝ) + 4) (Q u ω)) P ∧
      (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
        (Q u ω) ∂P) ≤ ENNReal.ofReal (Real.sqrt M) := by
    intro u hu
    exact fp81s21_MomentRep_firstMoment Es P Q qs M hstrong u hu
  have hfirstWeak : ∀ u : ℝ, 0 ≤ u →
      AEMeasurable (fun ω => dualNormE (2 * p.d + 8)
        ((p.d : ℝ) + 2) (Q u ω)) P ∧
      (∫⁻ ω, dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
        (Q u ω) ∂P) ≤ ENNReal.ofReal (Real.sqrt M) := by
    intro u hu
    exact fp81s21_MomentRep_firstMoment E P Q q M hweak u hu
  have hcompact : ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
      ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) H)).prod P),
        ∀ f, IsR2Test f →
          fp81s21_chartAction E (q (a + z.1) z.2) f = Q (a + z.1) z.2 f := by
    intro a ha H hH
    obtain ⟨_, _, hc⟩ := htime a ha H hH
    exact hc
  refine ⟨hstrong, hfirstStrong, hweak, hfirstWeak, hcompact, ?_⟩
  intro a ha H hH
  obtain ⟨U, hcore, _⟩ := htime a ha H hH
  have htails := fp81s21_time_projection_tails P q M a H U hqmeas
    hcore hM ha (le_of_lt hH) ε hε htail
  exact ⟨U, hcore, fun m => ⟨(htails m).1, (htails m).2⟩⟩

private theorem fp81s21_gaussian_fixed_time_projection_tail
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2))
    (hPs : (p.d : ℝ) < 2 * (((p.d : ℝ) + 2) + 2))
    (hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4)
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Q : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (qs : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hrep : fp81s21_MomentRep (hExp.symm ▸ Es) P Q qs M)
    (ε : ℕ → ℝ) (hε : ∀ m, 0 ≤ ε m)
    (hoperator : ∀ m,
      ‖fp81s21_embedField hP hPs (hExp.symm ▸ Es) E -
        (fp81s21_projectField m).comp
          (fp81s21_embedField hP hPs (hExp.symm ▸ Es) E)‖ ≤ ε m) :
    ∀ m u, 0 ≤ u →
      Integrable (fun ω =>
        ‖fp81s21_embedField hP hPs (hExp.symm ▸ Es) E (qs u ω) -
          fp81s21_projectField m
            (fp81s21_embedField hP hPs (hExp.symm ▸ Es) E (qs u ω))‖ ^ 2) P ∧
      (∫ ω,
        ‖fp81s21_embedField hP hPs (hExp.symm ▸ Es) E (qs u ω) -
          fp81s21_projectField m
            (fp81s21_embedField hP hPs (hExp.symm ▸ Es) E (qs u ω))‖ ^ 2 ∂P) ≤
        M * (ε m) ^ 2 := by
  intro m u hu
  let K : r26t6_Coeff →L[ℝ] r26t6_Coeff :=
    fp81s21_embedField hP hPs (hExp.symm ▸ Es) E
  let T : r26t6_Coeff →L[ℝ] r26t6_Coeff :=
    K - (fp81s21_projectField m).comp K
  have hTnorm : ‖T‖ ≤ ε m := by
    simpa [T, K] using hoperator m
  rcases hrep.2 u hu with ⟨hmem, hsecond, _⟩
  have hsourceSq : Integrable (fun ω => ‖qs u ω‖ ^ 2) P :=
    hmem.norm.integrable_sq
  have htailMem : MemLp (fun ω => T (qs u ω)) 2 P :=
    hmem.continuousLinearMap_comp T
  have htailSq : Integrable
      (fun ω => ‖K (qs u ω) -
        fp81s21_projectField m (K (qs u ω))‖ ^ 2) P := by
    simpa [T, K] using htailMem.norm.integrable_sq
  have hpoint : ∀ ω,
      ‖K (qs u ω) - fp81s21_projectField m (K (qs u ω))‖ ≤
        ε m * ‖qs u ω‖ := by
    intro ω
    calc
      ‖K (qs u ω) - fp81s21_projectField m (K (qs u ω))‖ =
          ‖T (qs u ω)‖ := by simp [T]
      _ ≤ ‖T‖ * ‖qs u ω‖ := T.le_opNorm _
      _ ≤ ε m * ‖qs u ω‖ :=
        mul_le_mul_of_nonneg_right hTnorm (norm_nonneg _)
  have hpointSq : ∀ ω,
      ‖K (qs u ω) - fp81s21_projectField m (K (qs u ω))‖ ^ 2 ≤
        (ε m) ^ 2 * ‖qs u ω‖ ^ 2 := by
    intro ω
    calc
      ‖K (qs u ω) - fp81s21_projectField m (K (qs u ω))‖ ^ 2 ≤
          (ε m * ‖qs u ω‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (hε m) (norm_nonneg _))).2
          (hpoint ω)
      _ = (ε m) ^ 2 * ‖qs u ω‖ ^ 2 := by ring
  have hscaledSq : Integrable
      (fun ω => (ε m) ^ 2 * ‖qs u ω‖ ^ 2) P :=
    hsourceSq.const_mul _
  refine ⟨htailSq, ?_⟩
  calc
    (∫ ω, ‖K (qs u ω) -
        fp81s21_projectField m (K (qs u ω))‖ ^ 2 ∂P) ≤
        ∫ ω, (ε m) ^ 2 * ‖qs u ω‖ ^ 2 ∂P :=
      integral_mono_ae htailSq hscaledSq
        (Filter.Eventually.of_forall hpointSq)
    _ = (ε m) ^ 2 * ∫ ω, ‖qs u ω‖ ^ 2 ∂P := integral_const_mul _ _
    _ ≤ (ε m) ^ 2 * M := mul_le_mul_of_nonneg_left hsecond (sq_nonneg _)
    _ = M * (ε m) ^ 2 := by ring

private theorem fp81s21_gaussian_canonical_one
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2))
    (hPs : (p.d : ℝ) < 2 * (((p.d : ℝ) + 2) + 2))
    (hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4)
    (ε : ℕ → ℝ) (hε : ∀ m, 0 ≤ ε m)
    (hoperator : ∀ m,
      ‖fp81s21_embedField hP hPs (hExp.symm ▸ Es) E -
        (fp81s21_projectField m).comp
          (fp81s21_embedField hP hPs (hExp.symm ▸ Es) E)‖ ≤ ε m)
    {δ : ℝ} (R : Trajectory p δ) (G : GaussianRealization R)
    (M : ℝ) (hM : 0 ≤ M) (qs : ℝ → G.Ω → r26t6_Coeff)
    (hstrong : fp81s21_MomentRep Es G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) qs M)
    (hweak : fp81s21_MomentRep E G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f)
      (fp81s21_gaussian_embedFamily p Es E qs) M)
    (hqmeas : Measurable
      (Function.uncurry (fp81s21_gaussian_embedFamily p Es E qs)))
    (htime : ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
      ∃ U : G.Ω → Lp r26t6_Coeff 2
          (volume.restrict (Set.Icc (0 : ℝ) H)),
        fp81s21_TimeL2Rep G.P (fp81s21_gaussian_embedFamily p Es E qs)
          M a H U ∧
        ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) H)).prod G.P),
          ∀ f, IsR2Test f →
            fp81s21_chartAction E
              ((fp81s21_gaussian_embedFamily p Es E qs) (a + z.1) z.2) f =
                OscDual.eval (G.Z (a + z.1) z.2) f) :
    fp81s21_gaussian_canonical_payload p Es E G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) M qs
      (fp81s21_gaussian_embedFamily p Es E qs) ε := by
  let Q : ℝ → G.Ω → (Euc p.d → ℝ) → ℝ :=
    fun u ω f => OscDual.eval (G.Z u ω) f
  let q : ℝ → G.Ω → r26t6_Coeff :=
    fp81s21_gaussian_embedFamily p Es E qs
  have hstrong' : fp81s21_MomentRep (hExp.symm ▸ Es) G.P Q qs M :=
    fp81s21_gaussian_normalizedStrong p Es hExp G.P Q qs M hstrong
  have htail : ∀ m u, 0 ≤ u →
      Integrable (fun ω => ‖q u ω - fp81s21_projectField m (q u ω)‖ ^ 2) G.P ∧
      (∫ ω, ‖q u ω - fp81s21_projectField m (q u ω)‖ ^ 2 ∂G.P) ≤
        M * (ε m) ^ 2 := by
    intro m u hu
    obtain ⟨hi, hb⟩ := fp81s21_gaussian_fixed_time_projection_tail
      p Es E hP hPs hExp G.P Q qs M hstrong' ε hε hoperator m u hu
    exact ⟨by simpa [q, fp81s21_gaussian_embedFamily] using hi,
      by simpa [q, fp81s21_gaussian_embedFamily] using hb⟩
  exact fp81s21_gaussian_payload_of_sections p Es E G.P Q M
    qs q ε hM hε hstrong hweak hqmeas htime htail

private theorem fp81s21_gaussian_canonical_one_from_bridge
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2))
    (hPs : (p.d : ℝ) < 2 * (((p.d : ℝ) + 2) + 2))
    (hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4)
    (ε : ℕ → ℝ) (hε : ∀ m, 0 ≤ ε m)
    (hoperator : ∀ m,
      ‖fp81s21_embedField hP hPs (hExp.symm ▸ Es) E -
        (fp81s21_projectField m).comp
          (fp81s21_embedField hP hPs (hExp.symm ▸ Es) E)‖ ≤ ε m)
    {δ : ℝ} (R : Trajectory p δ) (G : GaussianRealization R)
    (M : ℝ) (hM : 0 ≤ M) (qs : ℝ → G.Ω → r26t6_Coeff)
    (hstrong : fp81s21_MomentRep Es G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) qs M)
    (hPayload :
      fp81s21_MomentRep E G.P
        (fun u ω f => OscDual.eval (G.Z u ω) f)
        (fp81s21_gaussian_embedFamily p Es E qs) M ∧
      fp81s21_MomentRep E G.P
        (fun u ω f => OscDual.eval (G.Z u ω) f)
        (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)) M ∧
      Measurable (Function.uncurry
        (fp81s21_gaussian_embedFamily p Es E qs)) ∧
      (∀ u : ℝ, 0 ≤ u →
        (fun ω => fp81s21_gaussian_embedFamily p Es E qs u ω) =ᵐ[G.P]
          (fun ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω))) ∧
      ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
        ∃ U : G.Ω → Lp r26t6_Coeff 2
            (volume.restrict (Set.Icc (0 : ℝ) H)),
          fp81s21_TimeL2Rep G.P
            (fp81s21_gaussian_embedFamily p Es E qs) M a H U ∧
          (∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) H)).prod G.P),
            ∀ f, IsR2Test f →
              fp81s21_chartAction E
                ((fp81s21_gaussian_embedFamily p Es E qs) (a + z.1) z.2) f =
                  OscDual.eval (G.Z (a + z.1) z.2) f)) :
    fp81s21_gaussian_canonical_payload p Es E G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) M qs
      (fp81s21_gaussian_embedFamily p Es E qs) ε := by
  obtain ⟨hweak, _, hqmeas, _, htime⟩ := hPayload
  exact fp81s21_gaussian_canonical_one p Es E hP hPs hExp
    ε hε hoperator R G M hM qs hstrong hweak hqmeas htime

private theorem fp81s21_gaussian_canonical_realizations
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2))
    (hPs : (p.d : ℝ) < 2 * (((p.d : ℝ) + 2) + 2))
    (hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4)
    (ε : ℕ → ℝ) (hε : ∀ m, 0 ≤ ε m)
    (hoperator : ∀ m,
      ‖fp81s21_embedField hP hPs (hExp.symm ▸ Es) E -
        (fp81s21_projectField m).comp
          (fp81s21_embedField hP hPs (hExp.symm ▸ Es) E)‖ ≤ ε m) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
        ∃ M : ℝ, 0 ≤ M ∧
          ∀ G : GaussianRealization R,
            ∃ qs : ℝ → G.Ω → r26t6_Coeff,
              fp81s21_gaussian_canonical_payload p Es E G.P
                (fun u ω f => OscDual.eval (G.Z u ω) f) M qs
                (fp81s21_gaussian_embedFamily p Es E qs) ε := by
  obtain ⟨δ₀, hδ₀, hhalf, hbridge⟩ :=
    fp81s21_gaussian_compact_product_bridge p Es E
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨M, hM, hrealizations⟩ := hbridge δ hδ hδle R
  refine ⟨M, hM, ?_⟩
  intro G
  obtain ⟨qs, hstrong, hPayload⟩ := hrealizations G
  have hbuilt := fp81s21_gaussian_canonical_one_from_bridge
    p Es E hP hPs hExp ε hε hoperator R G M hM qs hstrong hPayload
  exact ⟨qs, hbuilt⟩

/-- A packaged realization statement keeps the prescribed order of
choices: the chart profile is fixed before the radius, and each moment
constant is fixed before a Gaussian realization. -/
structure fp81s21_gaussian_canonical_result
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) : Type where
  epsilon : ℕ → ℝ
  epsilon_nonneg : ∀ m, 0 ≤ epsilon m
  epsilon_tendsto : Tendsto epsilon atTop (𝓝 0)
  delta₀ : ℝ
  delta₀_positive : 0 < delta₀
  delta₀_half : delta₀ ≤ 1 / 2
  realizations :
    ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ → ∀ R : Trajectory p δ,
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ G : GaussianRealization R,
          ∃ qs : ℝ → G.Ω → r26t6_Coeff,
            fp81s21_gaussian_canonical_payload p Es E G.P
              (fun u ω f => OscDual.eval (G.Z u ω) f) M qs
              (fp81s21_gaussian_embedFamily p Es E qs) epsilon

/-- Selects one Gaussian coefficient family that carries the strong and
embedded moments, first moments, compact-test raw identification, and time
projection tails. The canonical embedded field is defined by the displayed
let; raw weighted-test evaluation is not asserted. -/
theorem fp81s21_gaussian_canonical_compact_time_tails (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    Nonempty (fp81s21_gaussian_canonical_result p Es E) := by
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith [p.hd]
  have hPs : (p.d : ℝ) < 2 * (((p.d : ℝ) + 2) + 2) := by
    nlinarith [p.hd]
  have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
  let Es' : r26t6_WeightedChart p.d (2 * p.d + 6)
      (((p.d : ℝ) + 2) + 2) := hExp.symm ▸ Es
  let hProfile := fp81s21_embedField_projectionProfile hP hPs Es' E
  let ε := Classical.choose hProfile
  have hProfileSpec := Classical.choose_spec hProfile
  rcases hProfileSpec with ⟨hε, hεlim, hprofile⟩
  let hRealizations := fp81s21_gaussian_canonical_realizations
    p Es E hP hPs hExp ε hε hprofile
  let δ₀ := Classical.choose hRealizations
  have hRealizationsSpec := Classical.choose_spec hRealizations
  rcases hRealizationsSpec with ⟨hδ₀, hhalf, hrealizations⟩
  exact ⟨{
    epsilon := ε
    epsilon_nonneg := hε
    epsilon_tendsto := hεlim
    delta₀ := δ₀
    delta₀_positive := hδ₀
    delta₀_half := hhalf
    realizations := hrealizations
  }⟩

/-- The complete canonical weighted-field realization package, with the
same chart-first profile and radius order as the compact coefficient result. -/
structure fp81s21_gaussian_canonical_time_result
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) : Type where
  epsilon : ℕ → ℝ
  epsilon_nonneg : ∀ m, 0 ≤ epsilon m
  epsilon_tendsto : Tendsto epsilon atTop (𝓝 0)
  delta₀ : ℝ
  delta₀_positive : 0 < delta₀
  delta₀_half : delta₀ ≤ 1 / 2
  realizations :
    ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ → ∀ R : Trajectory p δ,
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ G : GaussianRealization R,
          ∃ qs : ℝ → G.Ω → r26t6_Coeff,
            fp81s21_gaussian_canonical_time_payload p Es E G.P
              (fun u ω f => OscDual.eval (G.Z u ω) f) M qs
              (fp81s21_gaussian_embedFamily p Es E qs) epsilon

/-- The canonical Gaussian extension carries pointwise weighted
compatibility and a full TimeRep with the same coefficient-section tails.
Its equality with raw OscDual.eval is only the compact-test field inherited
from the coefficient payload; propagated-test identification is separate. -/
theorem fp81s21_gaussian_canonical_TimeRep_tails (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    Nonempty (fp81s21_gaussian_canonical_time_result p Es E) := by
  let coefficientResult := Classical.choice
    (fp81s21_gaussian_canonical_compact_time_tails p Es E)
  let ε := coefficientResult.epsilon
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith [p.hd]
  refine ⟨{
    epsilon := coefficientResult.epsilon
    epsilon_nonneg := coefficientResult.epsilon_nonneg
    epsilon_tendsto := coefficientResult.epsilon_tendsto
    delta₀ := coefficientResult.delta₀
    delta₀_positive := coefficientResult.delta₀_positive
    delta₀_half := coefficientResult.delta₀_half
    realizations := ?_
  }⟩
  intro δ hδ hδle R
  obtain ⟨M, hM, hrealizations⟩ :=
    coefficientResult.realizations δ hδ hδle R
  refine ⟨M, hM, ?_⟩
  intro G
  obtain ⟨qs, hcoeff⟩ := hrealizations G
  let Q : ℝ → G.Ω → (Euc p.d → ℝ) → ℝ :=
    fun u ω f => OscDual.eval (G.Z u ω) f
  let q : ℝ → G.Ω → r26t6_Coeff :=
    fp81s21_gaussian_embedFamily p Es E qs
  change fp81s21_gaussian_canonical_payload
    p Es E G.P Q M qs q ε at hcoeff
  refine ⟨qs, ?_⟩
  change fp81s21_gaussian_canonical_time_payload
    p Es E G.P Q M qs q ε
  refine ⟨hcoeff, ?_, ?_, ?_⟩
  · intro u hu
    exact (hcoeff.weak_momentRep.2 u hu).2.1
  · intro u ω
    exact fp81s21_chartAction_S102Z E (q u ω)
  · intro a ha H hH
    obtain ⟨U, hcore, htails⟩ := hcoeff.time_sections a ha H hH
    have hcompactQhat : ∀ᵐ z ∂((volume.restrict
        (Set.Icc (0 : ℝ) H)).prod G.P),
        ∀ f, IsR2Test f →
          fp81s21_chartAction E (q (a + z.1) z.2) f =
            fp81s21_gaussian_Qhat E q (a + z.1) z.2 f := by
      filter_upwards [] with z
      intro f hf
      rfl
    have hZQhat : ∀ᵐ z ∂((volume.restrict
        (Set.Icc (0 : ℝ) H)).prod G.P),
        S102Z (2 * p.d + 8) ((p.d : ℝ) + 2)
          (fp81s21_gaussian_Qhat E q (a + z.1) z.2) := by
      filter_upwards [] with z
      exact fp81s21_chartAction_S102Z E (q (a + z.1) z.2)
    have hTime := fp81s21_TimeRep_of_TimeL2Rep_product hP E G.P
      (fp81s21_gaussian_Qhat E q) q M a H U hcore hcompactQhat hZQhat
    exact ⟨U, hTime, htails⟩

#print axioms HRS.Fp81.S21.fp81s21_gaussian_Qhat
#print axioms HRS.Fp81.S21.fp81s21_gaussian_C
#print axioms HRS.Fp81.S21.fp81s21_gaussian_canonical_payload
#print axioms HRS.Fp81.S21.fp81s21_gaussian_canonical_time_payload
#print axioms HRS.Fp81.S21.fp81s21_gaussian_canonical_result
#print axioms HRS.Fp81.S21.fp81s21_gaussian_canonical_time_result
#print axioms HRS.Fp81.S21.fp81s21_gaussian_canonical_compact_time_tails
#print axioms HRS.Fp81.S21.fp81s21_gaussian_canonical_TimeRep_tails

end HRS.Fp81.S21
