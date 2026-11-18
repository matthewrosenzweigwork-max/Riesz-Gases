import HRS.Commutator.Torus.NRSTAux10
import HRS.PDE.MeanFieldFejer
import HRS.Commutator.Torus.TEXTAux1

/-!
# NRS-T, part 11: Fejér mollification of vector fields on the torus (Lipschitz constant preserved)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ComplexConjugate ENNReal

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ}

/-- The Fejér kernel of order `n+1`. -/
abbrev fj (d n : ℕ) : Torus d → ℝ := HRS.PDE.MFThermalExist.fejer (n + 1)

lemma fj_nonneg (n : ℕ) (x : Torus d) : 0 ≤ fj d n x := HRS.PDE.MFThermalExist.fejer_nonneg _ x

lemma fj_cont (n : ℕ) : Continuous (fj d n) := HRS.PDE.MFThermalExist.fejer_continuous _

lemma fj_integral (n : ℕ) : ∫ x, fj d n x = 1 :=
  HRS.PDE.MFThermalExist.integral_fejer _ (Nat.succ_pos n)

lemma fj_integrable (n : ℕ) : Integrable (fj d n) :=
  (fj_cont n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Fejér mollification of a vector field. -/
def mollV (n : ℕ) (u : Torus d → Euc d) (x : Torus d) : Euc d := ∫ z, fj d n z • u (x - z)

lemma integrable_moll {u : Torus d → Euc d} (hu : Continuous u) (n : ℕ) (x : Torus d) :
    Integrable (fun z => fj d n z • u (x - z)) := by
  have hc : Continuous fun z : Torus d => fj d n z • u (x - z) :=
    (fj_cont n).smul (hu.comp (continuous_const.sub continuous_id))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma mollV_apply {u : Torus d → Euc d} (hu : Continuous u) (n : ℕ) (x : Torus d) (j : Fin d) :
    mollV n u x j = ∫ z, fj d n z * u (x - z) j := by
  unfold mollV
  have := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integral_comp_comm (integrable_moll hu n x)
  simpa using this.symm

lemma tdist_sub_sub (x y z : Torus d) : KernelGrad.tdist (x - z) (y - z) = KernelGrad.tdist x y := by
  unfold KernelGrad.tdist
  rw [sub_sub_sub_cancel_right]

lemma mollV_lip {u : Torus d → Euc d} (hu : Continuous u) {L : ℝ} (hL : 0 ≤ L)
    (hlip : IsLipschitzVF L u) (n : ℕ) : IsLipschitzVF L (mollV n u) := by
  intro x y
  unfold mollV
  rw [← integral_sub (integrable_moll hu n x) (integrable_moll hu n y)]
  calc ‖∫ z, (fj d n z • u (x - z) - fj d n z • u (y - z))‖
      ≤ ∫ z, ‖fj d n z • u (x - z) - fj d n z • u (y - z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, fj d n z * (L * KernelGrad.tdist x y) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
          ((fj_integrable n).mul_const _) (Filter.Eventually.of_forall fun z => ?_)
        dsimp only
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (fj_nonneg n z)]
        refine mul_le_mul_of_nonneg_left ?_ (fj_nonneg n z)
        have := hlip (x - z) (y - z)
        rwa [tdist_sub_sub] at this
    _ = L * KernelGrad.tdist x y := by rw [integral_mul_const, fj_integral, one_mul]

end HRS.Commutator.TorusNote.NRST
