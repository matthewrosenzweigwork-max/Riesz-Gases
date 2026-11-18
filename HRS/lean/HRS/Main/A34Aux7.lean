import HRS.Main.A34Aux6

/-!
# Packet A34, helper 7: comparison of the noise integrands (Gaussian part of the statistic)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

/-- the fibrewise gradient field `1_{r ≤ t} ∇U^{r,t}φ` -/
def a34_u (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t : ℝ) (φ : Torus d → ℝ) :
    ℝ × Torus d → Euc d :=
  fun p => if p.1 ∈ Set.Icc 0 t then Torus.grad (propagator D ρ p.1 t φ) p.2 else 0

theorem a34_g_eq_u (D : DynData d) (ρ : ℝ → Torus d → ℝ) (q t : ℝ) (φ : Torus d → ℝ)
    (ht : 0 < t) : a33_g D ρ q t φ = fun p => Real.sqrt (2 * q) • a34_u D ρ t φ p := by
  funext p
  unfold a33_g a34_u
  by_cases h : p.1 ∈ Set.Icc 0 t
  · simp [h, ht]
  · simp [h]

theorem a34_h_eq (D : DynData d) (ρ : ℝ → Torus d → ℝ) (q t : ℝ) (φ : Torus d → ℝ)
    (ht : 0 < t) : a34_h D ρ q t φ =
      fun p => (Real.sqrt (ρ p.1 p.2) * Real.sqrt (2 * q)) • a34_u D ρ t φ p := by
  funext p
  unfold a34_h
  rw [a34_g_eq_u D ρ q t φ ht, smul_smul]

theorem a34_u_meas_bd (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t : ℝ) (φ : Torus d → ℝ)
    (f : ℝ → Torus d → ℝ) (hcl : IsClassicalAdjointSolution D ρ t φ f)
    (hpe : ∀ r ∈ Set.Icc 0 t, propagator D ρ r t φ = f r) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ r ∈ Set.Icc 0 t, ∀ x, ‖Torus.grad (propagator D ρ r t φ) x‖ ≤ K) :
    Measurable (a34_u D ρ t φ) ∧ ∀ p, ‖a34_u D ρ t φ p‖ ≤ K := by
  classical
  constructor
  · have h1 := a33_grad_meas_of_classical D ρ t φ f hcl
    have h2 : a34_u D ρ t φ = fun p => (if p.1 ∈ Set.Icc 0 t then Torus.grad (f p.1) p.2 else 0) := by
      funext p
      unfold a34_u
      by_cases h : p.1 ∈ Set.Icc 0 t
      · simp [h, hpe p.1 h]
      · simp [h]
    rw [h2]
    exact h1
  · intro p
    unfold a34_u
    split_ifs with h
    · exact hK p.1 h p.2
    · simpa using hK0

theorem a34_sq_sub_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (Real.sqrt x - Real.sqrt y) ^ 2 ≤ |x - y| := by
  have hx' := Real.sq_sqrt hx
  have hy' := Real.sq_sqrt hy
  have ha := Real.sqrt_nonneg x
  have hb := Real.sqrt_nonneg y
  rcases le_total (Real.sqrt y) (Real.sqrt x) with h | h
  · have : y ≤ x := by nlinarith
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  · have : x ≤ y := by nlinarith
    rw [abs_of_nonpos (by linarith)]
    nlinarith

theorem a34_gauss_diff {T t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) {ρ₁ ρ₂ : ℝ → Torus d → ℝ}
    (hρ₁ : A33Rho T ρ₁) (hρ₂ : A33Rho T ρ₂) {Λ : ℝ}
    (hΛ₁ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |ρ₁ r x| ≤ Λ)
    (hΛ₂ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |ρ₂ r x| ≤ Λ) (D₁ D₂ : DynData d) {q₁ q₂ : ℝ}
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) {φ₁ φ₂ : Torus d → ℝ}
    (f₁ f₂ : ℝ → Torus d → ℝ) (hcl₁ : IsClassicalAdjointSolution D₁ ρ₁ t φ₁ f₁)
    (hcl₂ : IsClassicalAdjointSolution D₂ ρ₂ t φ₂ f₂)
    (hpe₁ : ∀ r ∈ Set.Icc 0 t, propagator D₁ ρ₁ r t φ₁ = f₁ r)
    (hpe₂ : ∀ r ∈ Set.Icc 0 t, propagator D₂ ρ₂ r t φ₂ = f₂ r) {K : ℝ} (hK0 : 0 ≤ K)
    (hK₁ : ∀ r ∈ Set.Icc 0 t, ∀ x, ‖Torus.grad (propagator D₁ ρ₁ r t φ₁) x‖ ≤ K)
    (hK₂ : ∀ r ∈ Set.Icc 0 t, ∀ x, ‖Torus.grad (propagator D₂ ρ₂ r t φ₂) x‖ ≤ K)
    {δρ δq : ℝ} (hδρ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |ρ₁ r x - ρ₂ r x| ≤ δρ)
    (hδq : |2 * q₁ - 2 * q₂| ≤ δq) {Y : ℝ}
    (hY : ∫ p, ‖a34_u D₁ ρ₁ t φ₁ p - a34_u D₂ ρ₂ t φ₂ p‖ ^ 2 ∂(a33_mu0 d T) ≤ Y) :
    |Real.sqrt (2 * q₁ * ∫ r in Set.Icc 0 (min t t), ∫ x : Torus d,
        inner ℝ (Torus.grad (propagator D₁ ρ₁ r t φ₁) x) (Torus.grad (propagator D₁ ρ₁ r t φ₁) x) *
          ρ₁ r x) -
      Real.sqrt (2 * q₂ * ∫ r in Set.Icc 0 (min t t), ∫ x : Torus d,
        inner ℝ (Torus.grad (propagator D₂ ρ₂ r t φ₂) x) (Torus.grad (propagator D₂ ρ₂ r t φ₂) x) *
          ρ₂ r x)| ≤
    Real.sqrt (2 * K ^ 2 * (Λ * δq + 2 * q₂ * δρ) * (a33_mu0 d T).real Set.univ +
      2 * (2 * q₂ * Λ) * Y) := by
  classical
  have htI : t ∈ Set.Icc 0 T := ⟨ht0.le, htT⟩
  obtain ⟨hm₁, hb₁⟩ := a34_u_meas_bd D₁ ρ₁ t φ₁ f₁ hcl₁ hpe₁ hK0 hK₁
  obtain ⟨hm₂, hb₂⟩ := a34_u_meas_bd D₂ ρ₂ t φ₂ f₂ hcl₂ hpe₂ hK0 hK₂
  have hge₁ := a34_g_eq_u D₁ ρ₁ q₁ t φ₁ ht0
  have hge₂ := a34_g_eq_u D₂ ρ₂ q₂ t φ₂ ht0
  have hgm₁ : Measurable (a33_g D₁ ρ₁ q₁ t φ₁) := by rw [hge₁]; exact hm₁.const_smul (Real.sqrt (2 * q₁))
  have hgm₂ : Measurable (a33_g D₂ ρ₂ q₂ t φ₂) := by rw [hge₂]; exact hm₂.const_smul (Real.sqrt (2 * q₂))
  have hgb₁ : ∀ p, ‖a33_g D₁ ρ₁ q₁ t φ₁ p‖ ≤ Real.sqrt (2 * q₁) * K := fun p => by
    rw [hge₁]; simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hb₁ p) (Real.sqrt_nonneg _)
  have hgb₂ : ∀ p, ‖a33_g D₂ ρ₂ q₂ t φ₂ p‖ ≤ Real.sqrt (2 * q₂) * K := fun p => by
    rw [hge₂]; simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hb₂ p) (Real.sqrt_nonneg _)
  rw [a34_cov_eq hρ₁ D₁ hq₁ htI hgm₁ hgb₁, a34_cov_eq hρ₂ D₂ hq₂ htI hgm₂ hgb₂]
  set μ := a33_mu0 d T with hμ
  have : IsFiniteMeasure μ := inferInstance
  -- the functions `a_i`
  set a₁ : ℝ × Torus d → ℝ := fun p => Real.sqrt (ρ₁ p.1 p.2) * Real.sqrt (2 * q₁) with ha₁def
  set a₂ : ℝ × Torus d → ℝ := fun p => Real.sqrt (ρ₂ p.1 p.2) * Real.sqrt (2 * q₂) with ha₂def
  have ha₁m : AEMeasurable a₁ μ := (hρ₁.aemeasurable.sqrt).mul_const _
  have ha₂m : AEMeasurable a₂ μ := (hρ₂.aemeasurable.sqrt).mul_const _
  have hh₁ := a34_h_eq D₁ ρ₁ q₁ t φ₁ ht0
  have hh₂ := a34_h_eq D₂ ρ₂ q₂ t φ₂ ht0
  have hae := a33_ae_mu0 (d := d) T
  have hMem : ∀ (ρ : ℝ → Torus d → ℝ) (q : ℝ) (D : DynData d) (hρ : A33Rho T ρ)
      (hΛ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |ρ r x| ≤ Λ) (a : ℝ × Torus d → ℝ)
      (ha : a = fun p => Real.sqrt (ρ p.1 p.2) * Real.sqrt (2 * q)) (am : AEMeasurable a μ)
      (u : ℝ × Torus d → Euc d) (hum : Measurable u) (hub : ∀ p, ‖u p‖ ≤ K),
      MemLp (fun p => a p • u p) 2 μ := by
    intro ρ q D hρ hΛ a ha am u hum hub
    refine MemLp.of_bound (C := Real.sqrt Λ * Real.sqrt (2 * q) * K)
      (am.smul hum.aemeasurable).aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    rw [norm_smul, Real.norm_eq_abs, ha]
    simp only
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    refine mul_le_mul ?_ (hub p) (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ((le_abs_self _).trans (hΛ p.1 hp p.2)))
      (Real.sqrt_nonneg _)
  have hmem₁ := hMem ρ₁ q₁ D₁ hρ₁ hΛ₁ a₁ rfl ha₁m _ hm₁ hb₁
  have hmem₂ := hMem ρ₂ q₂ D₂ hρ₂ hΛ₂ a₂ rfl ha₂m _ hm₂ hb₂
  have hTri := a34_sqrt_tri hmem₁ hmem₂
  have hE : ∀ (i : ℕ), True := fun _ => trivial
  have e₁ : (∫ p, ‖a34_h D₁ ρ₁ q₁ t φ₁ p‖ ^ 2 ∂μ) = ∫ p, ‖a₁ p • a34_u D₁ ρ₁ t φ₁ p‖ ^ 2 ∂μ := by
    rw [hh₁]
  have e₂ : (∫ p, ‖a34_h D₂ ρ₂ q₂ t φ₂ p‖ ^ 2 ∂μ) = ∫ p, ‖a₂ p • a34_u D₂ ρ₂ t φ₂ p‖ ^ 2 ∂μ := by
    rw [hh₂]
  rw [e₁, e₂]
  refine hTri.trans (Real.sqrt_le_sqrt ?_)
  refine a34_E1 (hm₁.aemeasurable) (hm₂.aemeasurable) ha₁m ha₂m (K := K)
    (Eventually.of_forall hb₁) (Eventually.of_forall hb₂) (ε := Λ * δq + 2 * q₂ * δρ)
    (B := 2 * q₂ * Λ) ?_ ?_ ?_ hY (M := Real.sqrt Λ * Real.sqrt (2 * q₁) * K +
      Real.sqrt Λ * Real.sqrt (2 * q₂) * K) ?_
  · -- 0 ≤ B
    have : 0 ≤ Λ := by
      have := hΛ₁ 0 ⟨le_rfl, (ht0.le.trans htT)⟩ (Classical.arbitrary _)
      exact (abs_nonneg _).trans this
    positivity
  · filter_upwards [hae] with p hp
    have h1 := hρ₁.nonneg p.1 hp p.2
    have h2 := hρ₂.nonneg p.1 hp p.2
    have e1 : a₁ p = Real.sqrt (ρ₁ p.1 p.2 * (2 * q₁)) := by
      simp only [ha₁def]; rw [Real.sqrt_mul h1]
    have e2 : a₂ p = Real.sqrt (ρ₂ p.1 p.2 * (2 * q₂)) := by
      simp only [ha₂def]; rw [Real.sqrt_mul h2]
    rw [e1, e2]
    refine (a34_sq_sub_sqrt_le (mul_nonneg h1 (by linarith)) (mul_nonneg h2 (by linarith))).trans ?_
    have : ρ₁ p.1 p.2 * (2 * q₁) - ρ₂ p.1 p.2 * (2 * q₂) =
        ρ₁ p.1 p.2 * (2 * q₁ - 2 * q₂) + (2 * q₂) * (ρ₁ p.1 p.2 - ρ₂ p.1 p.2) := by ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (hΛ₁ p.1 hp p.2) hδq (abs_nonneg _) ((abs_nonneg _).trans (hΛ₁ p.1 hp p.2))
    · rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * q₂)]
      exact mul_le_mul_of_nonneg_left (hδρ p.1 hp p.2) (by linarith)
  · filter_upwards [hae] with p hp
    have h2 := hρ₂.nonneg p.1 hp p.2
    simp only [ha₂def]
    rw [mul_pow, Real.sq_sqrt h2, Real.sq_sqrt (by linarith)]
    calc ρ₂ p.1 p.2 * (2 * q₂) ≤ Λ * (2 * q₂) :=
          mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hΛ₂ p.1 hp p.2)) (by linarith)
      _ = 2 * q₂ * Λ := by ring
  · filter_upwards [hae] with p hp
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, show a₁ p = _ from rfl]
      rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      refine mul_le_mul ?_ (hb₁ p) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ((le_abs_self _).trans (hΛ₁ p.1 hp p.2)))
        (Real.sqrt_nonneg _)
    · rw [norm_smul, Real.norm_eq_abs, show a₂ p = _ from rfl]
      rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      refine mul_le_mul ?_ (hb₂ p) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ((le_abs_self _).trans (hΛ₂ p.1 hp p.2)))
        (Real.sqrt_nonneg _)

theorem a34_grad_sub {u v : Torus d → ℝ} (hu : Torus.IsCk 1 u) (hv : Torus.IsCk 1 v) (x : Torus d) :
    Torus.grad (fun y => u y - v y) x = Torus.grad u x - Torus.grad v x := by
  have := a33_grad_lin hu hv 1 (-1) x
  have e : (fun y => u y - v y) = fun y => 1 * u y + (-1) * v y := by funext y; ring
  rw [e, this]
  simp [sub_eq_add_neg]

/-- crude bound on the squared difference of two bounded fields -/
theorem a34_Y_sup {T : ℝ} {u₁ u₂ : ℝ × Torus d → Euc d} (hm₁ : Measurable u₁)
    (hm₂ : Measurable u₂) {K : ℝ} (hb₁ : ∀ p, ‖u₁ p‖ ≤ K) (hb₂ : ∀ p, ‖u₂ p‖ ≤ K) :
    ∫ p, ‖u₁ p - u₂ p‖ ^ 2 ∂(a33_mu0 d T) ≤ (K + K) ^ 2 * (a33_mu0 d T).real Set.univ := by
  have hbd : ∀ p, ‖u₁ p - u₂ p‖ ≤ K + K := fun p =>
    (norm_sub_le _ _).trans (add_le_add (hb₁ p) (hb₂ p))
  have hI : Integrable (fun p => ‖u₁ p - u₂ p‖ ^ 2) (a33_mu0 d T) :=
    a34_integrable_sq (hm₁.sub hm₂).aemeasurable (Eventually.of_forall hbd)
  calc ∫ p, ‖u₁ p - u₂ p‖ ^ 2 ∂(a33_mu0 d T) ≤ ∫ p, (K + K) ^ 2 ∂(a33_mu0 d T) :=
        integral_mono hI (integrable_const _) fun p =>
          pow_le_pow_left₀ (norm_nonneg _) (hbd p) 2
    _ = _ := by rw [integral_const]; simp [smul_eq_mul, mul_comm]

/-- `H¹` bound on the squared difference of the gradient fields. -/
theorem a34_Y_H1 {T t Z : ℝ} (ht : t ∈ Set.Icc 0 T) (D₁ D₂ : DynData d)
    (ρ₁ ρ₂ : ℝ → Torus d → ℝ) {φ₁ φ₂ : Torus d → ℝ}
    (hm₁ : Measurable (a34_u D₁ ρ₁ t φ₁)) (hm₂ : Measurable (a34_u D₂ ρ₂ t φ₂)) {K : ℝ}
    (hb₁ : ∀ p, ‖a34_u D₁ ρ₁ t φ₁ p‖ ≤ K) (hb₂ : ∀ p, ‖a34_u D₂ ρ₂ t φ₂ p‖ ≤ K)
    (hC₁ : ∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsCk 2 (propagator D₁ ρ₁ r t φ₁))
    (hC₂ : ∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsCk 2 (propagator D₂ ρ₂ r t φ₂))
    (hZ : ∀ r ∈ Set.Icc (0 : ℝ) t,
      sobolevNorm 1 (fun x => propagator D₁ ρ₁ r t φ₁ x - propagator D₂ ρ₂ r t φ₂ x) ≤ Z) :
    ∫ p, ‖a34_u D₁ ρ₁ t φ₁ p - a34_u D₂ ρ₂ t φ₂ p‖ ^ 2 ∂(a33_mu0 d T) ≤ t * Z ^ 2 := by
  have hbd : ∀ p, ‖a34_u D₁ ρ₁ t φ₁ p - a34_u D₂ ρ₂ t φ₂ p‖ ≤ K + K := fun p =>
    (norm_sub_le _ _).trans (add_le_add (hb₁ p) (hb₂ p))
  refine a34_Y_bound (u := fun p => a34_u D₁ ρ₁ t φ₁ p - a34_u D₂ ρ₂ t φ₂ p) ht (hm₁.sub hm₂) hbd ?_
    (Y₀ := Z ^ 2) ?_ (sq_nonneg _)
  · intro p hp
    simp [a34_u, hp]
  · intro r hr
    have hw : Torus.IsCk 2 (fun x => propagator D₁ ρ₁ r t φ₁ x - propagator D₂ ρ₂ r t φ₂ x) :=
      (hC₁ r hr).sub (hC₂ r hr)
    have h1 := a34_grad_H1 hw
    have e : ∀ x : Torus d, ‖(a34_u D₁ ρ₁ t φ₁ (r, x) - a34_u D₂ ρ₂ t φ₂ (r, x))‖ ^ 2 =
        ‖Torus.grad (fun y => propagator D₁ ρ₁ r t φ₁ y - propagator D₂ ρ₂ r t φ₂ y) x‖ ^ 2 := by
      intro x
      rw [a34_grad_sub ((hC₁ r hr).of_le (by norm_num)) ((hC₂ r hr).of_le (by norm_num))]
      simp [a34_u, hr]
    simp_rw [e]
    refine h1.trans ?_
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hZ r hr) 2

end HRS.A34
