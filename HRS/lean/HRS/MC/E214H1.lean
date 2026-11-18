import HRS.Main.HeadlineEdgeworth

/-!
# E214H1: the second-moment estimate behind the covariance relaxation (steps B3-B4)

For random elements `X, Y` of a normed space `B` with `E‖X‖² ≤ A`, `E‖Y‖² ≤ A` and `E‖X - Y‖² ≤ ε²` the
second-moment tensors satisfy `covDist P P X Y ≤ 2 √A ε` (`covDist_le_L2`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HRS.MC.E214H

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {Ω : Type*} [MeasurableSpace Ω]

theorem quad_abs_le (M : B [×2]→L[ℝ] ℝ) (u v : B) : |M ![u, v]| ≤ ‖M‖ * (‖u‖ * ‖v‖) := by
  have := M.le_opNorm ![u, v]
  simpa [Fin.prod_univ_two, Real.norm_eq_abs] using this

theorem quad_sub_left (M : B [×2]→L[ℝ] ℝ) (a b c : B) :
    M ![a - b, c] = M ![a, c] - M ![b, c] := by
  have h := M.toMultilinearMap.map_update_sub ![a, c] 0 a b
  have e1 : (Function.update ![a, c] 0 (a - b)) = ![a - b, c] := by
    ext i; fin_cases i <;> simp
  have e2 : (Function.update ![a, c] 0 a) = ![a, c] := by
    ext i; fin_cases i <;> simp
  have e3 : (Function.update ![a, c] 0 b) = ![b, c] := by
    ext i; fin_cases i <;> simp
  rw [e1, e2, e3] at h
  exact h

theorem quad_sub_right (M : B [×2]→L[ℝ] ℝ) (a b c : B) :
    M ![c, a - b] = M ![c, a] - M ![c, b] := by
  have h := M.toMultilinearMap.map_update_sub ![c, a] 1 a b
  have e1 : (Function.update ![c, a] 1 (a - b)) = ![c, a - b] := by
    ext i; fin_cases i <;> simp
  have e2 : (Function.update ![c, a] 1 a) = ![c, a] := by
    ext i; fin_cases i <;> simp
  have e3 : (Function.update ![c, a] 1 b) = ![c, b] := by
    ext i; fin_cases i <;> simp
  rw [e1, e2, e3] at h
  exact h

theorem quad_diag_sub (M : B [×2]→L[ℝ] ℝ) (x y : B) :
    M ![x, x] - M ![y, y] = M ![x - y, x] + M ![y, x - y] := by
  rw [quad_sub_left, quad_sub_right]; ring

theorem continuous_quad (M : B [×2]→L[ℝ] ℝ) : Continuous fun z : B => M ![z, z] :=
  M.cont.comp (continuous_pi fun i => by fin_cases i <;> simp <;> exact continuous_id)

/-- Cauchy-Schwarz for nonnegative square-integrable functions. -/
theorem cs_integral {P : Measure Ω} {f g : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hfm : AEStronglyMeasurable f P) (hgm : AEStronglyMeasurable g P)
    (hf : Integrable (fun ω => f ω ^ 2) P) (hg : Integrable (fun ω => g ω ^ 2) P) :
    ∫ ω, f ω * g ω ∂P ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) * Real.sqrt (∫ ω, g ω ^ 2 ∂P) := by
  have hp : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hfl : MemLp f (ENNReal.ofReal 2) P := by
    rw [show ENNReal.ofReal 2 = 2 by simp]
    exact (memLp_two_iff_integrable_sq hfm).2 hf
  have hgl : MemLp g (ENNReal.ofReal 2) P := by
    rw [show ENNReal.ofReal 2 = 2 by simp]
    exact (memLp_two_iff_integrable_sq hgm).2 hg
  have := integral_mul_le_Lp_mul_Lq_of_nonneg hp (Filter.Eventually.of_forall hf0)
    (Filter.Eventually.of_forall hg0) hfl hgl
  simp only [Real.rpow_two, one_div] at this
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, one_div]
  exact this

theorem integrable_mul_of_sq {P : Measure Ω} {f g : Ω → ℝ}
    (hfm : AEStronglyMeasurable f P) (hgm : AEStronglyMeasurable g P)
    (hf : Integrable (fun ω => f ω ^ 2) P) (hg : Integrable (fun ω => g ω ^ 2) P) :
    Integrable (fun ω => f ω * g ω) P := by
  refine Integrable.mono' (g := fun ω => f ω ^ 2 + g ω ^ 2) (hf.add hg) (hfm.mul hgm)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  have := two_mul_le_add_sq (|f ω|) (|g ω|)
  rw [abs_mul]
  nlinarith [sq_abs (f ω), sq_abs (g ω), abs_nonneg (f ω), abs_nonneg (g ω)]

theorem covDist_le_L2 (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → B)
    (hX : AEStronglyMeasurable X P) (hY : AEStronglyMeasurable Y P) {A ε : ℝ} (hε : 0 ≤ ε)
    (hXi : Integrable (fun ω => ‖X ω‖ ^ 2) P) (hYi : Integrable (fun ω => ‖Y ω‖ ^ 2) P)
    (hdi : Integrable (fun ω => ‖X ω - Y ω‖ ^ 2) P)
    (hXA : ∫ ω, ‖X ω‖ ^ 2 ∂P ≤ A) (hYA : ∫ ω, ‖Y ω‖ ^ 2 ∂P ≤ A)
    (hd : ∫ ω, ‖X ω - Y ω‖ ^ 2 ∂P ≤ ε ^ 2) :
    HRS.Main.covDist P P X Y ≤ 2 * Real.sqrt A * ε := by
  have hA : 0 ≤ A := (integral_nonneg fun ω => sq_nonneg _).trans hXA
  refine Real.iSup_le (fun M => ?_) (by positivity)
  obtain ⟨M, hM⟩ := M
  have hgm : Continuous fun z : B => M ![z, z] := continuous_quad M
  have hbound : ∀ z : B, |M ![z, z]| ≤ ‖z‖ ^ 2 := fun z => by
    have := quad_abs_le M z z
    have h2 : ‖M‖ * (‖z‖ * ‖z‖) ≤ 1 * (‖z‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_right hM (mul_self_nonneg _)
    nlinarith
  have hIX : Integrable (fun ω => M ![X ω, X ω]) P :=
    Integrable.mono' hXi (hgm.comp_aestronglyMeasurable hX)
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hbound (X ω))
  have hIY : Integrable (fun ω => M ![Y ω, Y ω]) P :=
    Integrable.mono' hYi (hgm.comp_aestronglyMeasurable hY)
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hbound (Y ω))
  set u : Ω → ℝ := fun ω => ‖X ω - Y ω‖ with hu
  have hum : AEStronglyMeasurable u P := (hX.sub hY).norm
  have hXm : AEStronglyMeasurable (fun ω => ‖X ω‖) P := hX.norm
  have hYm : AEStronglyMeasurable (fun ω => ‖Y ω‖) P := hY.norm
  have hu2 : Integrable (fun ω => u ω ^ 2) P := hdi
  have h1i : Integrable (fun ω => u ω * ‖X ω‖) P := integrable_mul_of_sq hum hXm hu2 hXi
  have h2i : Integrable (fun ω => ‖Y ω‖ * u ω) P := integrable_mul_of_sq hYm hum hYi hu2
  have hcs1 := cs_integral (P := P) (f := u) (g := fun ω => ‖X ω‖) (fun ω => norm_nonneg _)
    (fun ω => norm_nonneg _) hum hXm hu2 hXi
  have hcs2 := cs_integral (P := P) (f := fun ω => ‖Y ω‖) (g := u) (fun ω => norm_nonneg _)
    (fun ω => norm_nonneg _) hYm hum hYi hu2
  have hsu : Real.sqrt (∫ ω, u ω ^ 2 ∂P) ≤ ε := by
    calc _ ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hd
      _ = ε := Real.sqrt_sq hε
  have hsX : Real.sqrt (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ Real.sqrt A := Real.sqrt_le_sqrt hXA
  have hsY : Real.sqrt (∫ ω, ‖Y ω‖ ^ 2 ∂P) ≤ Real.sqrt A := Real.sqrt_le_sqrt hYA
  have hpt : ∀ ω, |M ![X ω, X ω] - M ![Y ω, Y ω]| ≤ u ω * ‖X ω‖ + ‖Y ω‖ * u ω := by
    intro ω
    rw [quad_diag_sub]
    have e1 := quad_abs_le M (X ω - Y ω) (X ω)
    have e2 := quad_abs_le M (Y ω) (X ω - Y ω)
    have n1 : 0 ≤ ‖X ω - Y ω‖ * ‖X ω‖ := by positivity
    have n2 : 0 ≤ ‖Y ω‖ * ‖X ω - Y ω‖ := by positivity
    have f1 : ‖M‖ * (‖X ω - Y ω‖ * ‖X ω‖) ≤ ‖X ω - Y ω‖ * ‖X ω‖ := by nlinarith
    have f2 : ‖M‖ * (‖Y ω‖ * ‖X ω - Y ω‖) ≤ ‖Y ω‖ * ‖X ω - Y ω‖ := by nlinarith
    calc _ ≤ |M ![X ω - Y ω, X ω]| + |M ![Y ω, X ω - Y ω]| := abs_add_le _ _
      _ ≤ _ := by simp only [hu]; linarith
  rw [← integral_sub hIX hIY]
  calc |∫ ω, (M ![X ω, X ω] - M ![Y ω, Y ω]) ∂P|
      ≤ ∫ ω, |M ![X ω, X ω] - M ![Y ω, Y ω]| ∂P := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun ω => M ![X ω, X ω] - M ![Y ω, Y ω])
    _ ≤ ∫ ω, (u ω * ‖X ω‖ + ‖Y ω‖ * u ω) ∂P :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _)
          (h1i.add h2i) (Filter.Eventually.of_forall hpt)
    _ = ∫ ω, u ω * ‖X ω‖ ∂P + ∫ ω, ‖Y ω‖ * u ω ∂P := integral_add h1i h2i
    _ ≤ 2 * Real.sqrt A * ε := by
        have s1 : Real.sqrt (∫ ω, u ω ^ 2 ∂P) * Real.sqrt (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ ε * Real.sqrt A :=
          mul_le_mul hsu hsX (Real.sqrt_nonneg _) hε
        have s2 : Real.sqrt (∫ ω, ‖Y ω‖ ^ 2 ∂P) * Real.sqrt (∫ ω, u ω ^ 2 ∂P) ≤ Real.sqrt A * ε :=
          mul_le_mul hsY hsu (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        nlinarith

end HRS.MC.E214H

end
