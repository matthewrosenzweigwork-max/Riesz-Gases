import Mathlib

/-!
# S11.1 X2, projection removal (packet H03)

Generic Banach-space statement: a bound on the covariance forms of the projected random elements
passes to the limit when the projections are contractions converging strongly.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.S111X2

/-- Pointwise limit of the projected quadratic forms. -/
theorem s111x2_quad_tendsto {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Pn : ℕ → B →L[ℝ] B) (hlim : ∀ x : B, Tendsto (fun n => Pn n x) atTop (𝓝 x))
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => B) ℝ) (x : B) :
    Tendsto (fun n => M ![Pn n x, Pn n x]) atTop (𝓝 (M ![x, x])) := by
  have hv : Tendsto (fun n => (![Pn n x, Pn n x] : Fin 2 → B)) atTop (𝓝 ![x, x]) := by
    rw [tendsto_pi_nhds]
    intro i; fin_cases i <;> simpa using hlim x
  exact (M.cont.tendsto _).comp hv

/-- Limit of the integrals of the projected quadratic forms. -/
theorem s111x2_integral_quad_tendsto {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → B) (hX : MemLp X 2 P) (Pn : ℕ → B →L[ℝ] B) (hPn : ∀ n, ‖Pn n‖ ≤ 1)
    (hlim : ∀ x : B, Tendsto (fun n => Pn n x) atTop (𝓝 x))
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => B) ℝ) (hM : ‖M‖ ≤ 1) :
    Tendsto (fun n => ∫ z, M ![Pn n (X z), Pn n (X z)] ∂P) atTop
      (𝓝 (∫ z, M ![X z, X z] ∂P)) := by
  have hbd : ∀ b : B, ‖M ![b, b]‖ ≤ ‖b‖ ^ 2 := by
    intro b
    have := M.le_opNorm ![b, b]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    calc ‖M ![b, b]‖ ≤ ‖M‖ * (‖b‖ * ‖b‖) := this
      _ ≤ 1 * (‖b‖ * ‖b‖) := by gcongr
      _ = ‖b‖ ^ 2 := by ring
  have hint : Integrable (fun z => ‖X z‖ ^ 2) P := hX.norm.integrable_sq
  have hXm : AEStronglyMeasurable X P := hX.aestronglyMeasurable
  have hcont : ∀ n, Continuous (fun b : B => M ![Pn n b, Pn n b]) := by
    intro n
    have : Continuous (fun b : B => (![Pn n b, Pn n b] : Fin 2 → B)) := by
      refine continuous_pi fun i => ?_
      fin_cases i <;> simpa using (Pn n).continuous
    exact M.cont.comp this
  apply tendsto_integral_of_dominated_convergence (fun z => ‖X z‖ ^ 2)
  · intro n; exact (hcont n).comp_aestronglyMeasurable hXm
  · exact hint
  · intro n
    refine Eventually.of_forall fun z => ?_
    calc ‖M ![Pn n (X z), Pn n (X z)]‖ ≤ ‖Pn n (X z)‖ ^ 2 := hbd _
      _ ≤ ‖X z‖ ^ 2 := by
        have := (Pn n).le_opNorm (X z)
        have h2 : ‖Pn n (X z)‖ ≤ ‖X z‖ := this.trans (by nlinarith [hPn n, norm_nonneg (X z)])
        gcongr
  · exact Eventually.of_forall fun z => s111x2_quad_tendsto Pn hlim M (X z)

/-- **H03**: removing the finite projections. -/
theorem s111x2_covariance_projection_limit
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {Omega₁ Omega₂ : Type*} [MeasurableSpace Omega₁] [MeasurableSpace Omega₂]
    (P₁ : Measure Omega₁) (P₂ : Measure Omega₂)
    (X₁ : Omega₁ → B) (X₂ : Omega₂ → B)
    (hX₁ : MemLp X₁ 2 P₁) (hX₂ : MemLp X₂ 2 P₂)
    (Pn : ℕ → B →L[ℝ] B)
    (hPn : ∀ n, ‖Pn n‖ ≤ 1)
    (hlim : ∀ x : B, Tendsto (fun n => Pn n x) atTop (𝓝 x))
    (A : ℝ)
    (hcov : ∀ n : ℕ, ∀ M : B [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 →
      |∫ z, M ![Pn n (X₁ z), Pn n (X₁ z)] ∂P₁ -
        ∫ z, M ![Pn n (X₂ z), Pn n (X₂ z)] ∂P₂| ≤ A) :
    ∀ M : B [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 →
      |∫ z, M ![X₁ z, X₁ z] ∂P₁ -
        ∫ z, M ![X₂ z, X₂ z] ∂P₂| ≤ A := by
  intro M hM
  have h1 := s111x2_integral_quad_tendsto P₁ X₁ hX₁ Pn hPn hlim M hM
  have h2 := s111x2_integral_quad_tendsto P₂ X₂ hX₂ Pn hPn hlim M hM
  have h3 := (h1.sub h2).abs
  exact le_of_tendsto' h3 (fun n => hcov n M hM)

end HRS.MS.S111X2
