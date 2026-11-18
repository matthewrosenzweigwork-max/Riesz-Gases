import HRS.MS.Fp81S21B6iiFinal2
import HRS.MS.Fp81S21VersionN
import HRS.MS.Fp81S21VersionN2
import HRS.MS.Fp81S21VersionTime

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Set
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.MS.R26T3 HRS.MS.R26T6

local instance fp81s21_versionNTime_CH_measSpace (H : ℝ) : MeasurableSpace
    (C(Icc (0 : ℝ) H, r26t6_Coeff)) := borel _
local instance fp81s21_versionNTime_CH_borelSpace (H : ℝ) : BorelSpace
    (C(Icc (0 : ℝ) H, r26t6_Coeff)) := ⟨rfl⟩

/-- The physical V1-N construction using the representatives selected by
B6-ii. It retains their strong and weak moment representations so later
physical time sections can identify the same selected weak-chart class. -/
theorem fp81s21_particle_continuous_version_physical (p : Parameters) :
    ∃ CL : ℝ, 0 ≤ CL ∧
    ∃ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∃ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ M2 M6 Cm : ℝ, 0 ≤ M2 ∧ 0 ≤ M6 ∧ 0 ≤ Cm ∧
        ∃ L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff,
          Measurable (fun z : ℝ × r26t6_Coeff => L z.1 z.2) ∧
          (∀ u : ℝ, 0 ≤ u → ‖L u‖ ≤ CL) ∧
          ∃ qsη : (N : ℕ) → (hN : 2 ≤ N) →
              (A : Particle R N) → ℝ → A.Ω → r26t6_Coeff,
          ∃ qB0 : (N : ℕ) → (hN : 2 ≤ N) →
              (A : Particle R N) → ℝ → A.Ω → r26t6_Coeff,
          ∃ m : (N : ℕ) → (hN : 2 ≤ N) →
              (A : Particle R N) → ℝ → A.Ω → r26t6_Coeff,
            (∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ A : Particle R N,
              fp81s21_MomentRep Es A.P
                (fp81s21_particleEmpField R N A) (qsη N hN A) M2 ∧
              fp81s21_MomentRep E A.P
                (fp81s21_particleQuadRawField R N A) (qB0 N hN A) M2 ∧
              (Measurable (Function.uncurry (qsη N hN A)) ∧
                Measurable (Function.uncurry (qB0 N hN A)) ∧
                fp81s21_Six A.P (qsη N hN A) M6 ∧
                fp81s21_Six A.P (qB0 N hN A) M6) ∧
              (∀ H : ℝ, 0 < H → ∀ a : ℝ, 0 ≤ a →
                ∀ s t : Icc (0 : ℝ) H,
                  MemLp (fun ω => m N hN A (a + t) ω - m N hN A (a + s) ω) 4 A.P ∧
                  (∫ ω, ‖m N hN A (a + t) ω - m N hN A (a + s) ω‖ ^ 4 ∂A.P) ≤
                    Cm * |(t : ℝ) - s| ^ 2) ∧
              ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
                ∀ᵐ ω ∂A.P, ∀ s t : Icc (0 : ℝ) H, s ≤ t →
                  fp81s21_gaussian_chartEmbed p Es E
                      ((qsη N hN A) (a + t) ω) -
                    fp81s21_gaussian_chartEmbed p Es E
                      ((qsη N hN A) (a + s) ω) =
                  (∫ v in Icc (s : ℝ) (t : ℝ),
                    fp81s21_empFour_drift N L (qsη N hN A) (qB0 N hN A)
                      (a + v) ω) +
                    (m N hN A (a + t) ω - m N hN A (a + s) ω)) ∧
            ∀ H : ℝ, 0 < H →
              ∃ Cη D : ℝ, 0 ≤ Cη ∧ 0 ≤ D ∧
                ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ A : Particle R N,
                  ∀ a : ℝ, 0 ≤ a →
                    ∃ X : A.Ω → C(Icc (0 : ℝ) H, r26t6_Coeff),
                      Measurable X ∧ MemLp X 2 A.P ∧
                      (∀ t : Icc (0 : ℝ) H,
                        (fun ω => X ω t) =ᵐ[A.P]
                          (fun ω => fp81s21_gaussian_chartEmbed p Es E
                            ((qsη N hN A) (a + t) ω))) ∧
                      ∃ B : A.Ω → ℝ, Measurable B ∧
                        (∀ ω, 0 ≤ B ω) ∧
                        Integrable (fun ω => B ω ^ 2) A.P ∧
                        (∫ ω, B ω ^ 2 ∂A.P) ≤ D ∧
                        ∀ᵐ ω ∂A.P, ∀ s t : Icc (0 : ℝ) H,
                          ‖X ω t - X ω s‖ ≤
                            B ω * |(t : ℝ) - s| ^ (1 / 8 : ℝ) := by
  obtain ⟨CL, hCL, Es, E, δ0, hδ0, hδ0half, hB6⟩ :=
    fp81s21_b6ii p
  refine ⟨CL, hCL, Es, E, δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨M2, M6, Cm, hM2, hM6, hCm, L, hLjoint, hLbound, hNA⟩ :=
    hB6 δ hδ hδle R
  choose Fp qsη qB0 m hdata using hNA
  refine ⟨M2, M6, Cm, hM2, hM6, hCm, L, hLjoint, hLbound,
    qsη, qB0, m, ?_, ?_⟩
  · intro N hN A
    rcases hdata N hN A with
      ⟨hηrep, hBrep, hfields, hm, hIto, hHS, hB7, hEq⟩
    rcases hfields with ⟨hqsJoint, hqB0Joint, hqsSix, hqB0Six⟩
    refine ⟨hηrep, hBrep,
      ⟨hqsJoint, hqB0Joint, hqsSix, hqB0Six⟩, ?_, ?_⟩
    · intro H hH a ha s t
      exact hB7 H hH a ha s t
    · intro a ha H hH
      filter_upwards [hEq a ha H hH] with ω hω
      intro s t hst
      have hraw := hω.2 s t hst
      rw [← fp81s21_b6ii_empFourDrift_eq_vectorDrift N L
        (qsη N hN A) (qB0 N hN A)] at hraw
      calc
        _ = (∫ v in Icc (s : ℝ) (t : ℝ),
              fp81s21_empFour_drift N L (qsη N hN A) (qB0 N hN A)
                (a + v) ω) + m N hN A (a + t) ω -
              m N hN A (a + s) ω := hraw
        _ = (∫ v in Icc (s : ℝ) (t : ℝ),
              fp81s21_empFour_drift N L (qsη N hN A) (qB0 N hN A)
                (a + v) ω) +
              (m N hN A (a + t) ω - m N hN A (a + s) ω) := by abel
  · intro H hH
    let CD : ℝ := 8 * (CL ^ 4 + 1) * (1 + M6)
    let Cη : ℝ := 8 * (CD * H ^ 2 + Cm)
    have hCD : 0 ≤ CD := by dsimp [CD]; positivity
    have hCη : 0 ≤ Cη := by dsimp [Cη, CD]; positivity
    obtain ⟨D, hD, hHolder⟩ :=
      fp81s21_exists_holder_version (E := r26t6_Coeff)
        H (1 + M6) Cη hH hCη
    refine ⟨Cη, D, hCη, hD, ?_⟩
    intro N hN A a ha
    rcases hdata N hN A with
      ⟨hηrep, hBrep, hfields, hm, hIto, hHS, hB7, hEq⟩
    rcases hfields with ⟨hqsJoint, hqB0Joint, hqsSix, hqB0Six⟩
    let qs : ℝ → A.Ω → r26t6_Coeff := qsη N hN A
    let qB : ℝ → A.Ω → r26t6_Coeff := qB0 N hN A
    let mart : ℝ → A.Ω → r26t6_Coeff := m N hN A
    have hB6emp : ∀ a' : ℝ, 0 ≤ a' → ∀ H' : ℝ, 0 < H' →
        ∀ᵐ ω ∂A.P, ∀ s t : Icc (0 : ℝ) H', s ≤ t →
          fp81s21_gaussian_chartEmbed p Es E (qs (a' + t) ω) -
              fp81s21_gaussian_chartEmbed p Es E (qs (a' + s) ω) =
            (∫ v in Icc (s : ℝ) (t : ℝ),
              fp81s21_empFour_drift N L qs qB (a' + v) ω) +
              (mart (a' + t) ω - mart (a' + s) ω) := by
      intro a' ha' H' hH'
      filter_upwards [hEq a' ha' H' hH'] with ω hω
      intro s t hst
      have hvector :
          fp81s21_gaussian_chartEmbed p Es E (qs (a' + t) ω) -
              fp81s21_gaussian_chartEmbed p Es E (qs (a' + s) ω) =
            (∫ v in Icc (s : ℝ) (t : ℝ),
              fp81s21_b6ii_vectorDrift N L qs qB (a' + v) ω) +
              mart (a' + t) ω - mart (a' + s) ω := by
        simpa [qs, qB, mart] using hω.2 s t hst
      rw [← fp81s21_b6ii_empFourDrift_eq_vectorDrift N L qs qB] at hvector
      calc
        _ = (∫ v in Icc (s : ℝ) (t : ℝ),
              fp81s21_empFour_drift N L qs qB (a' + v) ω) +
              mart (a' + t) ω - mart (a' + s) ω := hvector
        _ = (∫ v in Icc (s : ℝ) (t : ℝ),
              fp81s21_empFour_drift N L qs qB (a' + v) ω) +
              (mart (a' + t) ω - mart (a' + s) ω) := by abel
    have hDrift := fp81s21_empFour_integrated_drift_fourth A.P N hN
      qs qB L M6 CL hM6 hCL hLbound hLjoint hqsJoint hqB0Joint hqsSix hqB0Six
    have hIncCore := fp81s21_empirical_fourth_increments_from_components
      p R N A Es E qs qB mart L CD Cm hCD hCm hB6emp hDrift hB7
    have hInc : fp81s21_Inc4 A.P
        (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)) H Cη := by
      simpa [Cη] using hIncCore H hH
    have hInitial := fp81s21_embedded_initial_fourth
      p Es E A.P qs M6 hqsJoint hqsSix a ha
    let qη : ℝ → A.Ω → r26t6_Coeff :=
      fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)
    have hqηMeas : ∀ t, Measurable (qη t) := by
      simpa [qη] using hInitial.1
    have hHolderOut := hHolder A.P qη a hqηMeas hInitial.2.1 hInitial.2.2
      (hInc a ha)
    simpa [qη, qs] using hHolderOut

#print axioms HRS.Fp81.S21.fp81s21_particle_continuous_version_physical

end HRS.Fp81.S21
