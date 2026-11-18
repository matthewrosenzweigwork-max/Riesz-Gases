import HRS.MS.R26T8AA10
import HRS.MS.R26T8AD01
import HRS.MS.R26T8AR07
import HRS.MS.R26T8AR13
import HRS.MS.R26T8AO01a

/-!
# S8.2 T8A O01: `r26t8a_normal_form_family` from C15 and P29

`r26t8a_C15_stmt` and `r26t8a_P29_stmt` are exactly the statements of packets C15 (`r26t8a_pointwise_pin_comparison`) and P29
(`r26t8a_weighted_pair_corrector`); `r26t8a_normal_form_family_of hC15 hP29` is the statement of O01.  Once C15 and P29 are proved
the packet export is `r26t8a_normal_form_family := r26t8a_normal_form_family_of r26t8a_pointwise_pin_comparison
r26t8a_weighted_pair_corrector`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

/-- The statement of packet C15 `r26t8a_pointwise_pin_comparison`. -/
def r26t8a_C15_stmt : Prop :=
  ∀ (d : ℕ) (_ : 2 ≤ d) (a beta C0 : ℝ) (_ : 0 < a) (_ : 0 < beta) (q : Euc d → ℝ) (_ : ShortRangePole d q),
    ∃ C : ℝ, 0 < C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ,
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C

/-- The statement of packet P29 `r26t8a_weighted_pair_corrector`. -/
def r26t8a_P29_stmt : Prop :=
  ∀ (d : ℕ) (_ : 2 ≤ d) (a beta : ℝ) (_ : 0 < a) (_ : 0 < beta),
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∃ Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ,
        (∀ f g : Euc d → ℝ, ∀ A B : ℝ,
          TestBound (testOrder d) A f → TestBound (testOrder d) B g →
          ∀ c : ℝ, Psi (f + c • g) = Psi f + c • Psi g) ∧
        (∀ c : ℝ, Psi (fun _ => c) = 0) ∧
        ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
          PairCorrector a beta rho M (C * A) f (Psi f) ∧
          MemLp (aSource (HRS.Whole.withDensityReal rho) f) 2 (HRS.Whole.withDensityReal rho) ∧
          eLpNorm (aSource (HRS.Whole.withDensityReal rho) f) 2 (HRS.Whole.withDensityReal rho) ≤ ENNReal.ofReal (C * A)

set_option maxHeartbeats 12800000 in
theorem r26t8a_normal_form_family_of (hC15 : r26t8a_C15_stmt) (hP29 : r26t8a_P29_stmt)
    (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∃ Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ,
        r26t8a_NormalFormFamily d a beta M C rho Psi := by
  classical
  by_cases hex : ∃ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho
  swap
  · exact ⟨0, 0, le_rfl, le_rfl, fun rho hrho => (hex ⟨rho, hrho⟩).elim⟩
  obtain ⟨rho0, hrho0⟩ := hex
  obtain ⟨C0, q, hC0, hcal⟩ := r26t8a_calibrated_reference_native d hd a beta ha hbeta
  obtain ⟨h0, hcal0⟩ := hcal rho0 hrho0
  have hq : ShortRangePole d q := hcal0.short
  obtain ⟨C1, hC1, hwr⟩ := r26t8a_finite_pin_reference_adapter d hd a beta C0 ha hbeta q
  obtain ⟨C2, hC2, hpin⟩ := hC15 d hd a beta C1 ha hbeta q hq
  obtain ⟨C3, M, hC3, hM, hP⟩ := hP29 d hd a beta ha hbeta
  obtain ⟨C4, hC4, hA10⟩ := r26t8a_normal_form_bound d hd a beta M C1 C2 ha hbeta hM q hq
  refine ⟨max C3 (C4 * (1 + C3)), M, le_max_of_le_left hC3, hM, fun rho hrho => ?_⟩
  obtain ⟨Psi, hlin, hconst, hcorr⟩ := hP rho hrho
  obtain ⟨h, hcalr⟩ := hcal rho hrho
  have hweak := hwr rho hrho h hcalr
  have hpc := hpin rho hrho h hweak
  refine ⟨Psi, ?_⟩
  have hmain : ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f → ∀ N : ℕ, 2 ≤ N →
      GeneratorClosure a beta (r26t8a_correctedQ (N := N) a beta Psi f)
        (fun X => -scalarForcing a beta rho f X + r26t8a_correctedD a beta rho Psi f X) ∧
      MemLp (r26t8a_correctedD (N := N) a beta rho Psi f) 2 (canonicalP d N a beta) ∧
      (∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
        scalarForcing a beta rho f X =
          -particleGenerator (quadraticGradientDyn d (criticalS d) a beta)
            (r26t8a_correctedQ a beta Psi f) X + r26t8a_correctedD a beta rho Psi f X) ∧
      eLpNorm (r26t8a_correctedQ (N := N) a beta Psi f) 2 (canonicalP d N a beta) +
        (∫⁻ X, ∑ i, ‖Phase2S82.configGrad (r26t8a_correctedQ a beta Psi f) X i‖ₑ ^ 2 ∂canonicalP d N a beta) ^ (1 / 2 : ℝ) +
        eLpNorm (r26t8a_correctedD (N := N) a beta rho Psi f) 2 (canonicalP d N a beta) ≤
          ENNReal.ofReal (C4 * (A + C3 * A) * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
    intro f A hA hTB N hN
    obtain ⟨hPC, hAm, hAb⟩ := hcorr f A hA hTB
    exact hA10 rho hrho h hweak hpc Psi f A (C3 * A) hA (mul_nonneg hC3 hA) hTB hPC hAm hAb N hN
  refine ⟨hlin, hconst, ?_, ?_, ?_, ?_⟩
  · intro f A hA hTB
    exact r26t8a_o01_PairCorrector_mono (hcorr f A hA hTB).1 (mul_le_mul_of_nonneg_right (le_max_left _ _) hA)
  · intro N hN f A hA hTB
    exact (hmain f A hA hTB N hN).1
  · intro N hN f A hA hTB X hX
    exact (hmain f A hA hTB N hN).2.2.1 X hX
  · intro N hN f A hA hTB
    obtain ⟨-, hD, -, hb⟩ := hmain f A hA hTB N hN
    refine ⟨hD, hb.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hNr : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hN0.le _
    have : C4 * (A + C3 * A) ≤ max C3 (C4 * (1 + C3)) * A := by
      have h1 : C4 * (A + C3 * A) = C4 * (1 + C3) * A := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hA
    exact mul_le_mul_of_nonneg_right this hNr

end HRS.MS.R26T8A

end
