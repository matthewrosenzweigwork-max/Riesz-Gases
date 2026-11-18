import HRS.MS.Fp81S21VersionN
import HRS.MS.Fp81S21VersionHolder6

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Set
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.MS.R26T3 HRS.MS.R26T6

/-- The particle continuous version obtained from the uniform B8 increment
bound. The selected strong representatives and B6-ii/B7 certificates remain
visible so the section identities refer to the same B8 choice. -/
theorem fp81s21_particle_continuous_version_from_b8
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (M6 CL Cm : ℝ) (hM6 : 0 ≤ M6) (hCL : 0 ≤ CL) (hCm : 0 ≤ Cm)
    (L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (hL : ∀ u, 0 ≤ u → ‖L u‖ ≤ CL)
    (hLjoint : Measurable (fun z : ℝ × r26t6_Coeff => L z.1 z.2))
    (hdata : ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
      ∃ qs qB0 m : ℝ → A.Ω → r26t6_Coeff,
        Measurable (Function.uncurry qs) ∧
        Measurable (Function.uncurry qB0) ∧
        fp81s21_Six A.P qs M6 ∧ fp81s21_Six A.P qB0 M6 ∧
        (∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
          ∀ᵐ ω ∂A.P, ∀ s t : Icc (0 : ℝ) H, s ≤ t →
            fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω) -
              fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω) =
            (∫ v in Icc (s : ℝ) (t : ℝ),
              fp81s21_empFour_drift N L qs qB0 (a + v) ω) +
              (m (a + t) ω - m (a + s) ω)) ∧
        (∀ H : ℝ, 0 < H → ∀ a : ℝ, 0 ≤ a →
          ∀ s t : Icc (0 : ℝ) H,
            MemLp (fun ω => m (a + t) ω - m (a + s) ω) 4 A.P ∧
            (∫ ω, ‖m (a + t) ω - m (a + s) ω‖ ^ 4 ∂A.P) ≤
              Cm * |(t : ℝ) - s| ^ 2)) :
    ∀ H : ℝ, 0 < H →
      ∃ Cη : ℝ, 0 ≤ Cη ∧ ∃ D : ℝ, 0 ≤ D ∧
        ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ a : ℝ, 0 ≤ a →
          ∃ qs qB0 m : ℝ → A.Ω → r26t6_Coeff,
            Measurable (Function.uncurry qs) ∧
            Measurable (Function.uncurry qB0) ∧
            fp81s21_Six A.P qs M6 ∧ fp81s21_Six A.P qB0 M6 ∧
            (∀ a' : ℝ, 0 ≤ a' → ∀ H' : ℝ, 0 < H' →
              ∀ᵐ ω ∂A.P, ∀ s t : Icc (0 : ℝ) H', s ≤ t →
                fp81s21_gaussian_chartEmbed p Es E (qs (a' + t) ω) -
                  fp81s21_gaussian_chartEmbed p Es E (qs (a' + s) ω) =
                (∫ v in Icc (s : ℝ) (t : ℝ),
                  fp81s21_empFour_drift N L qs qB0 (a' + v) ω) +
                  (m (a' + t) ω - m (a' + s) ω)) ∧
            (∀ H' : ℝ, 0 < H' → ∀ a' : ℝ, 0 ≤ a' →
              ∀ s t : Icc (0 : ℝ) H',
                MemLp (fun ω => m (a' + t) ω - m (a' + s) ω) 4 A.P ∧
                (∫ ω, ‖m (a' + t) ω - m (a' + s) ω‖ ^ 4 ∂A.P) ≤
                  Cm * |(t : ℝ) - s| ^ 2) ∧
            fp81s21_Inc4 A.P
              (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)) H Cη ∧
            ∃ X : A.Ω → C(Icc (0 : ℝ) H, r26t6_Coeff),
              Measurable X ∧ MemLp X 2 A.P ∧
              (∀ t : Icc (0 : ℝ) H,
                (fun ω => X ω t) =ᵐ[A.P]
                  (fun ω => fp81s21_gaussian_chartEmbed p Es E
                    (qs (a + t) ω))) ∧
              ∃ B : A.Ω → ℝ, Measurable B ∧ (∀ ω, 0 ≤ B ω) ∧
                Integrable (fun ω => B ω ^ 2) A.P ∧
                (∫ ω, B ω ^ 2 ∂A.P) ≤ D ∧
                ∀ᵐ ω ∂A.P, ∀ s t : Icc (0 : ℝ) H,
                  ‖X ω t - X ω s‖ ≤
                    B ω * |(t : ℝ) - s| ^ (1 / 8 : ℝ) := by
  intro H hH
  obtain ⟨Cη, hCη, hB8⟩ :=
    fp81s21_empirical_fourth_increments_uniform_from_components
      p R Es E M6 CL Cm hM6 hCL hCm L hL hLjoint hdata H hH
  obtain ⟨D, hD, hHolder⟩ :=
    fp81s21_exists_holder_version (E := r26t6_Coeff)
      H (1 + M6) Cη hH hCη
  refine ⟨Cη, hCη, D, hD, ?_⟩
  intro N hN A a ha
  obtain ⟨qs, qB0, m, hqsJoint, hqB0Joint, hqsSix, hqB0Six,
    hB6ii, hB7, hInc⟩ := hB8 N hN A
  let qη : ℝ → A.Ω → r26t6_Coeff :=
    fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)
  have hIncη : fp81s21_Inc4 A.P qη H Cη := by
    simpa [qη] using hInc
  have hInitial := fp81s21_embedded_initial_fourth
    p Es E A.P qs M6 hqsJoint hqsSix a ha
  have hqηMeas : ∀ t, Measurable (qη t) := by
    simpa [qη] using hInitial.1
  have hqηMem : MemLp (qη a) 4 A.P := by
    simpa [qη] using hInitial.2.1
  have hqηBound : (∫ ω, ‖qη a ω‖ ^ 4 ∂A.P) ≤ 1 + M6 := by
    simpa [qη] using hInitial.2.2
  refine ⟨qs, qB0, m, hqsJoint, hqB0Joint, hqsSix, hqB0Six,
    hB6ii, hB7, hInc, ?_⟩
  exact hHolder A.P qη a hqηMeas hqηMem hqηBound (hIncη a ha)

#print axioms HRS.Fp81.S21.fp81s21_particle_continuous_version_from_b8

end HRS.Fp81.S21
