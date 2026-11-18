import HRS.Commutator.Torus.NRSTAux15
import HRS.Commutator.Torus.Defs

/-!
# NRS-T, part 16: `TorusSubTransport` passes to the Fejér means
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ComplexConjugate ENNReal

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ}

open Classical in
/-- Measurable regularisation of a vector field (components that are not a.e. measurable are zeroed). -/
def regW (w : Torus d → Euc d) (x : Torus d) : Euc d :=
  WithLp.toLp 2 fun j => if AEStronglyMeasurable (fun y => w y j) volume then w x j else 0

lemma norm_regW_le (w : Torus d → Euc d) (x : Torus d) : ‖regW w x‖ ≤ ‖w x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
  unfold regW
  by_cases h : AEStronglyMeasurable (fun y => w y j) volume
  · simp [h]
  · simp [h]; positivity

lemma aestronglyMeasurable_regW (w : Torus d → Euc d) : AEStronglyMeasurable (regW w) volume := by
  have : ∀ j : Fin d, AEStronglyMeasurable (fun x => (regW w x) j) volume := by
    intro j
    unfold regW
    by_cases h : AEStronglyMeasurable (fun y => w y j) volume
    · simpa [h] using h
    · simpa [h] using aestronglyMeasurable_const
  have e : regW w = fun x => ∑ j : Fin d, (regW w x j) • EuclideanSpace.single j (1 : ℝ) := by
    funext x
    ext i
    simp [Finset.sum_apply, PiLp.single_apply, Pi.single_apply]
  rw [e]
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => (this j).smul_const _

lemma fcoef_regW (w : Torus d → Euc d) (j : Fin d) (k : Lattice d) :
    Torus.fcoef (fun x => regW w x j) k = Torus.fcoef (fun x => w x j) k := by
  by_cases h : AEStronglyMeasurable (fun y => w y j) volume
  · have : (fun x => regW w x j) = fun x => w x j := by
      funext x; simp [regW, h]
    rw [this]
  · have h0 : (fun x => regW w x j) = fun _ => (0 : ℝ) := by
      funext x; simp [regW, h]
    rw [h0]
    have hni : ¬ Integrable (fun x => Torus.mode (-k) x * ((w x j : ℝ) : ℂ)) := by
      intro hint
      apply h
      have h1 : AEStronglyMeasurable (fun x => Torus.mode k x * (Torus.mode (-k) x * ((w x j : ℝ) : ℂ))) volume :=
        ((Torus.continuous_mode k).aestronglyMeasurable).mul hint.aestronglyMeasurable
      have h2 : (fun x => Torus.mode k x * (Torus.mode (-k) x * ((w x j : ℝ) : ℂ))) = fun x => ((w x j : ℝ) : ℂ) := by
        funext x
        rw [← mul_assoc, ← Torus.mode_add, add_neg_cancel, Torus.mode_zero, one_mul]
      rw [h2] at h1
      exact (Complex.reCLM.continuous.comp_aestronglyMeasurable h1).congr
        (Filter.Eventually.of_forall fun x => by simp)
    unfold Torus.fcoef
    rw [integral_undef hni]
    simp

lemma isFracDeriv_regW {a : ℝ} {v w : Torus d → Euc d} (h : IsFracDeriv a v w) :
    IsFracDeriv a v (regW w) := by
  intro j k
  rw [fcoef_regW]
  exact h j k

lemma transport_moll {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {v : Torus d → Euc d} {K : ℝ}
    (hv : TorusSubTransport d s v K) (n : ℕ) : TorusSubTransport d s (vOf (Vn n v)) K := by
  obtain ⟨L, F, hL0, hF0, hLip, ⟨w, hw, hwn⟩, hLF⟩ := hv
  have hvc : Continuous v := IsLipschitzVF.continuous hL0 hLip
  have hden : 0 < (d : ℝ) - s - 2 := by linarith
  have hd2 : (2 : ℝ) < d := by linarith
  have hp1 : 1 ≤ 2 * (d : ℝ) / ((d : ℝ) - s - 2) := by
    rw [le_div_iff₀ hden]; linarith
  set P : ℝ≥0∞ := ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - s - 2)) with hP
  have hP1 : 1 ≤ P := by
    rw [hP, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1
  have hreg : eLpNorm (regW w) P volume ≤ ENNReal.ofReal F :=
    (eLpNorm_mono (aestronglyMeasurable_regW w) fun x => norm_regW_le w x).trans hwn
  have hlt : eLpNorm (regW w) P volume < ⊤ := lt_of_le_of_lt hreg ENNReal.ofReal_lt_top
  have hmem : MemLp (regW w) P volume := hlt
  have hint : Integrable (regW w) := hmem.integrable hP1
  refine ⟨L, F, hL0, hF0, vOf_Vn_lip hvc hL0 hLip n, ⟨mollV n (regW w),
    isFracDeriv_moll hint (isFracDeriv_regW hw) n, ?_⟩, hLF⟩
  exact (eLpNorm_mollV_le (aestronglyMeasurable_regW w) hp1 n).trans hreg

end HRS.Commutator.TorusNote.NRST
