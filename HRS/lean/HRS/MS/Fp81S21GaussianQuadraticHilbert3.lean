import HRS.MS.Fp81S21GaussianQuadraticHilbert2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators
open HRS HRS.MC.E213U13 HRS.MS.R26T6
namespace HRS.Fp81.S21

/-- Every bounded scalar functional of a coefficient second-chaos field is
in the same scalar second chaos. -/
theorem fp81s21_InQ2_coeff_functional
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    (q : Ω → r26t6_Coeff) (hq : MemLp q 2 P)
    (hcoord : ∀ j, InQ2 hξ (fun ω => q ω j))
    (ℓ : r26t6_Coeff →L[ℝ] ℝ) :
    InQ2 hξ (fun ω => ℓ (q ω)) := by
  let Y : ℕ → Ω → ℝ := fun n ω => ℓ (fp81s21_projectField n (q ω))
  have hY : ∀ n, InQ2 hξ (Y n) := by
    intro n
    have heq : Y n = fun ω => ∑ j ∈ Finset.range n,
        ℓ (fp81s21_coeffBasis j) * q ω j := by
      funext ω
      simp [Y, fp81s21_projectField_apply_coordinate, mul_comm]
    rw [heq]
    exact InQ2.sum _ fun j _ => InQ2.const_mul _ (hcoord j)
  have hz : AEStronglyMeasurable (fun ω => ℓ (q ω)) P :=
    ℓ.continuous.comp_aestronglyMeasurable hq.aestronglyMeasurable
  have ht : Tendsto (fun n => eLpNorm (fun ω => fp81s21_projectField n (q ω) - q ω) 2 P)
      atTop (𝓝 0) := by
    have hq' : MemLp q (ENNReal.ofReal (2 : ℝ)) P := by simpa using hq
    simpa using dct_proj hq.aestronglyMeasurable (q := 2) (by norm_num) hq'
      fp81s21_projectField fp81s21_projectField_norm_le fp81s21_projectField_tendsto
  have hm : ∀ n, AEStronglyMeasurable (fun ω => Y n ω - ℓ (q ω)) P :=
    fun n => (hY n).1.aestronglyMeasurable.sub hz
  have hb : ∀ n, eLpNorm (fun ω => Y n ω - ℓ (q ω)) 2 P ≤
      ENNReal.ofReal ‖ℓ‖ * eLpNorm (fun ω => fp81s21_projectField n (q ω) - q ω) 2 P := by
    intro n
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hm n)
      (Filter.Eventually.of_forall fun ω => ?_) 2
    simpa [Y, ← map_sub] using ℓ.le_opNorm (fp81s21_projectField n (q ω) - q ω)
  have ht' : Tendsto (fun n => eLpNorm (fun ω => Y n ω - ℓ (q ω)) 2 P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => bot_le) hb
    simpa using ENNReal.Tendsto.const_mul ht (Or.inr (by simp))
  apply InQ2.of_tendsto (l := atTop) hY hz
  exact (tendsto_lintegral_iff_eLpNorm hm (by norm_num)).2 (by simpa using ht')

/-- Bounded linear maps preserve coefficient-valued second-chaos fields. -/
theorem fp81s21_InQ2_coeff_map
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    (q : Ω → r26t6_Coeff) (hq : MemLp q 2 P)
    (hcoord : ∀ j, InQ2 hξ (fun ω => q ω j))
    (A : r26t6_Coeff →L[ℝ] r26t6_Coeff) :
    MemLp (fun ω => A (q ω)) 4 P ∧
      (∫ ω, ‖A (q ω)‖ ^ 4 ∂P) ≤ 15 * (∫ ω, ‖A (q ω)‖ ^ 2 ∂P) ^ 2 := by
  apply fp81s21_InQ2_coeff_fourth hξ (fun ω => A (q ω)) (A.comp_memLp' hq)
  intro j
  exact fp81s21_InQ2_coeff_functional hξ q hq hcoord
    ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 j).comp A)

#print axioms fp81s21_InQ2_coeff_functional
#print axioms fp81s21_InQ2_coeff_map
end HRS.Fp81.S21
end
