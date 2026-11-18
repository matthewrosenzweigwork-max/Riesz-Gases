import Mathlib
import HRS.Main.A33Aux6

/-!
# Packet A33, helper 7: linearity of the noise vectors in the test function
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A33

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

lemma a33_grad_lin {u v : Torus d → ℝ} (hu : Torus.IsCk 1 u) (hv : Torus.IsCk 1 v) (α β : ℝ)
    (x : Torus d) :
    Torus.grad (fun y => α * u y + β * v y) x = α • Torus.grad u x + β • Torus.grad v x := by
  unfold Torus.grad
  have hu' : DifferentiableAt ℝ (Torus.lift u) (Torus.rep x) :=
    (hu.differentiable (by norm_num)) _
  have hv' : DifferentiableAt ℝ (Torus.lift v) (Torus.rep x) :=
    (hv.differentiable (by norm_num)) _
  have h : Torus.lift (fun y => α * u y + β * v y) = fun z => α * Torus.lift u z + β * Torus.lift v z :=
    rfl
  rw [h]
  have hd := (hu'.hasFDerivAt.const_mul α).add (hv'.hasFDerivAt.const_mul β)
  unfold gradient
  have hd' : HasFDerivAt (fun z => α * Torus.lift u z + β * Torus.lift v z)
      (α • fderiv ℝ (Torus.lift u) x.rep + β • fderiv ℝ (Torus.lift v) x.rep) x.rep := hd
  rw [hd'.fderiv]
  simp [map_add, map_smul]

lemma a33_grad_const (c : ℝ) (x : Torus d) : Torus.grad (fun _ : Torus d => c) x = 0 := by
  unfold Torus.grad
  exact gradient_const _ _

lemma a33_coeFn_sum_lp {α E ι : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (J : Finset ι) (f : ι → Lp E 2 μ) :
    ⇑(∑ i ∈ J, f i) =ᵐ[μ] fun ω => ∑ i ∈ J, (f i : α → E) ω := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero E 2 μ] with ω h
    rw [Finset.sum_empty, Finset.sum_empty]
    exact h
  | insert a J ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ J, f i), ih] with ω h1 h2
    simp only [Finset.sum_insert ha, h1, h2, Pi.add_apply]

namespace A33Setup

variable (S : A33Setup d)

theorem prop_isCk {t : ℝ} (ht : t ∈ Set.Ioc 0 S.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {r : ℝ} (hr : r ∈ Set.Icc 0 t) : Torus.IsCk 2 (propagator S.D S.ρ r t φ) := by
  have hex := S.exists_classical ht hφ
  rw [a33_propagator_eq_choose S.D S.ρ t φ hex]
  exact hex.choose_spec.c2 r hr

theorem grad_prop_lin {t : ℝ} (ht : t ∈ Set.Ioc 0 S.T) {φ ψ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) (α β : ℝ) {r : ℝ} (hr : r ∈ Set.Icc 0 t)
    (x : Torus d) :
    Torus.grad (propagator S.D S.ρ r t (fun y => α * φ y + β * ψ y)) x =
      α • Torus.grad (propagator S.D S.ρ r t φ) x + β • Torus.grad (propagator S.D S.ρ r t ψ) x := by
  rw [prop_lin S.hd S.D.s S.D.hs0 S.D.hsd S.J S.hJ S.R S.MB S.Λ S.VB S.D S.ν₀ S.T S.ρ S.hA ht
    (dom_smooth hφ) (dom_smooth hψ) α β hr]
  exact a33_grad_lin (ClassicalAux.isCk_of_le (by norm_num) (S.prop_isCk ht hφ hr))
    (ClassicalAux.isCk_of_le (by norm_num) (S.prop_isCk ht hψ hr)) α β x

theorem grad_prop_const {t : ℝ} (ht : t ∈ Set.Ioc 0 S.T) (c : ℝ) {r : ℝ} (hr : r ∈ Set.Icc 0 t)
    (x : Torus d) : Torus.grad (propagator S.D S.ρ r t (fun _ => c)) x = 0 := by
  rw [prop_const S.hd S.D.s S.D.hs0 S.D.hsd S.J S.hJ S.R S.MB S.Λ S.VB S.D S.ν₀ S.T S.ρ S.hA ht c hr]
  exact a33_grad_const c x

theorem g_lin (q : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) {φ ψ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) (α β : ℝ) :
    a33_g S.D S.ρ q t (fun y => α * φ y + β * ψ y) =
      fun p => α • a33_g S.D S.ρ q t φ p + β • a33_g S.D S.ρ q t ψ p := by
  funext p
  unfold a33_g
  by_cases h : p.1 ∈ Set.Icc 0 t ∧ 0 < t
  · rw [if_pos h, if_pos h, if_pos h, S.grad_prop_lin ⟨h.2, ht.2⟩ hφ hψ α β h.1]
    simp [smul_add, smul_comm α, smul_comm β]
  · rw [if_neg h, if_neg h, if_neg h]
    simp

theorem g_const (q : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) (c : ℝ) :
    a33_g S.D S.ρ q t (fun _ => c) = 0 := by
  funext p
  unfold a33_g
  by_cases h : p.1 ∈ Set.Icc 0 t ∧ 0 < t
  · rw [if_pos h, S.grad_prop_const ⟨h.2, ht.2⟩ c h.1]
    simp
  · rw [if_neg h]; rfl

theorem g_tr (q : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (e : ℕ ≃ NonzeroLattice d) (n : ℕ) :
    a33_g S.D S.ρ q t (a33_tr φ e n) = fun p =>
      ∑ i ∈ Finset.range n, Torus.funRealCoeff φ (e i) • a33_g S.D S.ρ q t (Torus.realMode (e i)) p := by
  induction n with
  | zero =>
    have h0 : a33_tr φ e 0 = fun _ => (0 : ℝ) := by
      funext y; simp [a33_tr]
    rw [h0, S.g_const q ht 0]
    funext p
    simp
  | succ n ih =>
    have h1 : a33_tr φ e (n + 1) = fun y => 1 * a33_tr φ e n y +
        Torus.funRealCoeff φ (e n) * Torus.realMode (e n) y := by
      funext y; simp [a33_tr, Finset.sum_range_succ]
    rw [h1, S.g_lin q ht (a33_tr_smooth φ e n) (HRS.FieldSingAux.isSmooth_realMode (e n)) 1
      (Torus.funRealCoeff φ (e n)), ih]
    funext p
    simp [Finset.sum_range_succ]

theorem g_res (q : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (e : ℕ ≃ NonzeroLattice d) (n : ℕ) :
    a33_g S.D S.ρ q t (a33_res φ e n) = fun p =>
      a33_g S.D S.ρ q t φ p - ∑ i ∈ Finset.range n,
        Torus.funRealCoeff φ (e i) • a33_g S.D S.ρ q t (Torus.realMode (e i)) p := by
  set m : Torus d → ℝ := fun y => 1 * (fun _ : Torus d => Torus.mean φ) y + 1 * a33_tr φ e n y with hm
  have hms : Torus.IsSmooth m := by
    unfold Torus.IsSmooth Torus.IsCk
    have h1 := a33_tr_smooth φ e n
    unfold Torus.IsSmooth Torus.IsCk at h1
    exact (contDiff_const.mul contDiff_const).add (contDiff_const.mul h1)
  have hres : a33_res φ e n = fun y => 1 * φ y + (-1) * m y := by
    funext y; simp [a33_res, hm]; ring
  have hgm : a33_g S.D S.ρ q t m = a33_g S.D S.ρ q t (a33_tr φ e n) := by
    rw [hm, S.g_lin q ht (a33_isSmooth_const _) (a33_tr_smooth φ e n) 1 1, S.g_const q ht]
    funext p; simp
  rw [hres, S.g_lin q ht hφ hms 1 (-1), hgm, S.g_tr q ht hφ e n]
  funext p
  simp [sub_eq_add_neg]

theorem vec_res_ae (q : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) (e : ℕ ≃ NonzeroLattice d) (n : ℕ) :
    ⇑(a33_vec S q t φ - ∑ i ∈ Finset.range n,
        Torus.funRealCoeff φ (e i) • a33_vec S q t (Torus.realMode (e i))) =ᵐ[a33_nu d S.T S.ρ]
      a33_g S.D S.ρ q t (a33_res φ e n) := by
  have hall : ∀ᵐ p ∂(a33_nu d S.T S.ρ), ∀ i ∈ Finset.range n,
      (Torus.funRealCoeff φ (e i) • a33_vec S q t (Torus.realMode (e i)) :
        Lp (Euc d) 2 (a33_nu d S.T S.ρ)) p =
        Torus.funRealCoeff φ (e i) • a33_g S.D S.ρ q t (Torus.realMode (e i)) p := by
    refine (Filter.eventually_all_finset (Finset.range n)).2 fun i _ => ?_
    filter_upwards [Lp.coeFn_smul (Torus.funRealCoeff φ (e i))
      (a33_vec S q t (Torus.realMode (e i))),
      S.vec_ae q ht (HRS.FieldSingAux.isSmooth_realMode (e i))] with p h1 h2
    rw [h1, Pi.smul_apply, h2]
  filter_upwards [Lp.coeFn_sub (a33_vec S q t φ) (∑ i ∈ Finset.range n,
      Torus.funRealCoeff φ (e i) • a33_vec S q t (Torus.realMode (e i))),
    a33_coeFn_sum_lp (Finset.range n)
      (fun i => Torus.funRealCoeff φ (e i) • a33_vec S q t (Torus.realMode (e i))),
    S.vec_ae q ht hφ, hall] with p h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, S.g_res q ht hφ e n]
  rw [Finset.sum_congr rfl h4]

theorem vec_res_norm (q : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, t ∈ Set.Icc 0 S.T → ∀ {φ : Torus d → ℝ}, Torus.IsSmooth φ →
      ∀ (e : ℕ ≃ NonzeroLattice d) (n : ℕ),
      ‖a33_vec S q t φ - ∑ i ∈ Finset.range n,
        Torus.funRealCoeff φ (e i) • a33_vec S q t (Torus.realMode (e i))‖ ≤
        K * sobolevNorm (mStar d : ℝ) (a33_res φ e n) := by
  haveI := S.rho.nu_finite
  obtain ⟨B, hB0, hB⟩ := S.g_bound' q
  refine ⟨(measureUnivNNReal (a33_nu d S.T S.ρ) : ℝ) ^ ((2 : ENNReal).toReal)⁻¹ * B,
    mul_nonneg (by positivity) hB0, fun {t} ht {φ} hφ e n => ?_⟩
  have h0 : 0 ≤ B * sobolevNorm (mStar d : ℝ) (a33_res φ e n) := mul_nonneg hB0 (Real.sqrt_nonneg _)
  have := Lp.norm_le_of_ae_bound (μ := a33_nu d S.T S.ρ) (p := 2)
    (f := a33_vec S q t φ - ∑ i ∈ Finset.range n,
        Torus.funRealCoeff φ (e i) • a33_vec S q t (Torus.realMode (e i))) h0 (by
      filter_upwards [S.vec_res_ae q ht hφ e n] with p hp
      rw [hp]
      exact hB t ht _ (a33_res_smooth hφ e n) p)
  calc _ ≤ _ := this
    _ = _ := by ring

end A33Setup

end HRS.A33
