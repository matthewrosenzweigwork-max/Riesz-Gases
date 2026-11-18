import HRS.MC.E213TCons
import HRS.MC.E214PD

/-!
# Packet e214m, file 1: differences of Bochner product tensors

`norm_bochTensor3_sub_le_proof` and `norm_bochTensor21_sub_le_proof` (statements of `E214Plan`, relocated).
No integrability hypothesis beyond the plan statements is needed: if one of the two integrands is integrable
then so is the other (their difference is dominated by the integrable sum of the three terms); otherwise
both Bochner integrals are the junk value `0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

set_option maxSynthPendingDepth 3

namespace HRS.MC.E214M

open HRS HRS.Contr HRS.MC.E213T

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem m_trilinear_sub (M : B [×3]→L[ℝ] ℝ) (x y z x' y' z' : B) :
    M ![x, y, z] - M ![x', y', z'] =
      M ![x - x', y, z] + M ![x', y - y', z] + M ![x', y', z - z'] := by
  have e1 : (![x - x', y, z] : Fin 3 → B) = Function.update ![x', y, z] 0 (x - x') := by
    ext i; fin_cases i <;> simp [Function.update]
  have e1a : (![x, y, z] : Fin 3 → B) = Function.update ![x', y, z] 0 x := by
    ext i; fin_cases i <;> simp [Function.update]
  have e1b : (![x', y, z] : Fin 3 → B) = Function.update ![x', y, z] 0 x' := by
    ext i; fin_cases i <;> simp [Function.update]
  have e2 : (![x', y - y', z] : Fin 3 → B) = Function.update ![x', y', z] 1 (y - y') := by
    ext i; fin_cases i <;> simp [Function.update]
  have e2a : (![x', y, z] : Fin 3 → B) = Function.update ![x', y', z] 1 y := by
    ext i; fin_cases i <;> simp [Function.update]
  have e2b : (![x', y', z] : Fin 3 → B) = Function.update ![x', y', z] 1 y' := by
    ext i; fin_cases i <;> simp [Function.update]
  have e3 : (![x', y', z - z'] : Fin 3 → B) = Function.update ![x', y', z'] 2 (z - z') := by
    ext i; fin_cases i <;> simp [Function.update]
  have e3a : (![x', y', z] : Fin 3 → B) = Function.update ![x', y', z'] 2 z := by
    ext i; fin_cases i <;> simp [Function.update]
  have e3b : (![x', y', z'] : Fin 3 → B) = Function.update ![x', y', z'] 2 z' := by
    ext i; fin_cases i <;> simp [Function.update]
  have h1 := M.map_update_sub ![x', y, z] 0 x x'
  have h2 := M.map_update_sub ![x', y', z] 1 y y'
  have h3 := M.map_update_sub ![x', y', z'] 2 z z'
  rw [← e1, ← e1a, ← e1b] at h1
  rw [← e2, ← e2a, ← e2b] at h2
  rw [← e3, ← e3a, ← e3b] at h3
  rw [h1, h2, h3]
  ring

theorem m_elem3_sub (x y z x' y' z' : B) :
    (elemTensor ![x, y, z] : TensorDual B 3) - elemTensor ![x', y', z'] =
      elemTensor ![x - x', y, z] + elemTensor ![x', y - y', z] + elemTensor ![x', y', z - z'] := by
  ext M
  simp only [sub_apply, add_apply, elemTensor_apply]
  exact m_trilinear_sub M x y z x' y' z'

section Bochner

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Generic form: if `f, f'` are a.e. strongly measurable with `‖f - f'‖ ≤ G` a.e., `G` integrable, then
`‖∫ f - ∫ f'‖ ≤ ∫ G` (no integrability of `f` needed; both integrals are the junk value `0` if neither is
integrable). -/
theorem m_norm_integral_sub_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (P : Measure Ω) {f f' : Ω → F} (hf : AEStronglyMeasurable f P) (hf' : AEStronglyMeasurable f' P)
    {G : Ω → ℝ} (hG : Integrable G P) (hle : ∀ᵐ ω ∂P, ‖f ω - f' ω‖ ≤ G ω) :
    ‖∫ ω, f ω ∂P - ∫ ω, f' ω ∂P‖ ≤ ∫ ω, G ω ∂P := by
  have hd : Integrable (fun ω => f ω - f' ω) P :=
    Integrable.mono' hG (hf.sub hf') hle
  have hGnn : 0 ≤ ∫ ω, G ω ∂P := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hle] with ω h using (norm_nonneg _).trans h
  by_cases hI : Integrable f P
  · have hI' : Integrable f' P := by
      have : Integrable (fun ω => f ω - (f ω - f' ω)) P := hI.sub hd
      exact this.congr (ae_of_all _ fun ω => by simp)
    rw [← integral_sub hI hI']
    exact (norm_integral_le_integral_norm _).trans (integral_mono_ae hd.norm hG hle)
  · have hI' : ¬ Integrable f' P := by
      intro h
      apply hI
      exact (hd.add h).congr (ae_of_all _ fun ω => by simp)
    rw [integral_undef hI, integral_undef hI']
    simpa using hGnn

theorem norm_bochTensor3_sub_le_proof {Ω B : Type*} [MeasurableSpace Ω] [NormedAddCommGroup B]
    [NormedSpace ℝ B] (P : Measure Ω) {x y z x' y' z' : Ω → B}
    (hx : AEStronglyMeasurable x P) (hy : AEStronglyMeasurable y P) (hz : AEStronglyMeasurable z P)
    (hx' : AEStronglyMeasurable x' P) (hy' : AEStronglyMeasurable y' P) (hz' : AEStronglyMeasurable z' P)
    (h1 : Integrable (fun ω => ‖x ω - x' ω‖ * ‖y ω‖ * ‖z ω‖) P)
    (h2 : Integrable (fun ω => ‖x' ω‖ * ‖y ω - y' ω‖ * ‖z ω‖) P)
    (h3 : Integrable (fun ω => ‖x' ω‖ * ‖y' ω‖ * ‖z ω - z' ω‖) P) :
    ‖bochTensor3 P x y z - bochTensor3 P x' y' z'‖ ≤
      ∫ ω, (‖x ω - x' ω‖ * ‖y ω‖ * ‖z ω‖ + ‖x' ω‖ * ‖y ω - y' ω‖ * ‖z ω‖ +
        ‖x' ω‖ * ‖y' ω‖ * ‖z ω - z' ω‖) ∂P := by
  unfold bochTensor3
  refine m_norm_integral_sub_le P (elemTensor3_continuous.comp_aestronglyMeasurable (hx.prodMk (hy.prodMk hz)))
    (elemTensor3_continuous.comp_aestronglyMeasurable (hx'.prodMk (hy'.prodMk hz'))) ((h1.add h2).add h3) (ae_of_all _ fun ω => ?_)
  rw [m_elem3_sub]
  refine (norm_add₃_le).trans ?_
  have := elemTensor3_norm_le (x ω - x' ω) (y ω) (z ω)
  have := elemTensor3_norm_le (x' ω) (y ω - y' ω) (z ω)
  have := elemTensor3_norm_le (x' ω) (y' ω) (z ω - z' ω)
  linarith

theorem norm_bochTensor21_sub_le_proof {Ω B : Type*} [MeasurableSpace Ω] [NormedAddCommGroup B]
    [NormedSpace ℝ B] (P : Measure Ω) [IsProbabilityMeasure P]
    {J J' : Ω → TensorDual B 2} {g g' : Ω → B}
    (hJ : AEStronglyMeasurable J P) (hJ' : AEStronglyMeasurable J' P)
    (hg : AEStronglyMeasurable g P) (hg' : AEStronglyMeasurable g' P)
    (h1 : Integrable (fun ω => ‖J ω - J' ω‖ * ‖g ω‖) P)
    (h2 : Integrable (fun ω => ‖J' ω‖ * ‖g ω - g' ω‖) P) :
    ‖bochTensor21 P J g - bochTensor21 P J' g'‖ ≤
      ∫ ω, (‖J ω - J' ω‖ * ‖g ω‖ + ‖J' ω‖ * ‖g ω - g' ω‖) ∂P := by
  unfold bochTensor21
  refine m_norm_integral_sub_le P (bochTensor21_aestronglyMeasurable hJ hg)
    (bochTensor21_aestronglyMeasurable hJ' hg') (h1.add h2) (ae_of_all _ fun ω => ?_)
  have e : tensorCons (J ω) (g ω) - tensorCons (J' ω) (g' ω) =
      tensorCons (J ω - J' ω) (g ω) + tensorCons (J' ω) (g ω - g' ω) := by
    have h1 := tensorCons_add_left (J ω - J' ω) (J' ω) (g ω)
    have h2 := tensorCons_add_right (J' ω) (g ω - g' ω) (g' ω)
    rw [sub_add_cancel] at h1 h2
    rw [h1, h2]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have := norm_tensorCons_le (J ω - J' ω) (g ω)
  have := norm_tensorCons_le (J' ω) (g ω - g' ω)
  linarith

end Bochner

end HRS.MC.E214M
end
