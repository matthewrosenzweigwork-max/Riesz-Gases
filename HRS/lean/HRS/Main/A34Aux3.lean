import HRS.Main.A34Aux2

/-!
# Packet A34, helper 3: the noise integrand for a classical test function

Measurability and boundedness of `a33_g` for a classical adjoint solution, the identification of the
`surrogateCov` entry with `∫ ‖a34_h‖² d(a33_mu0)`, the bound `∫ ‖u‖² ≤ t Y₀` for fibrewise bounds
and the `H¹` bound `∫ |∇u|² ≤ ‖u‖²_{H¹}`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33

variable {d : ℕ}

theorem a34_g_zero (D : DynData d) (ρ : ℝ → Torus d → ℝ) (q t : ℝ) (φ : Torus d → ℝ)
    (ht : ¬ 0 < t) : a33_g D ρ q t φ = 0 := by
  funext p
  unfold a33_g
  simp [ht]

theorem a34_g_meas_bd (D : DynData d) (ρ : ℝ → Torus d → ℝ) (q t : ℝ) (φ : Torus d → ℝ)
    (ht : 0 < t) (f : ℝ → Torus d → ℝ) (hcl : IsClassicalAdjointSolution D ρ t φ f)
    (hpe : ∀ r ∈ Set.Icc 0 t, propagator D ρ r t φ = f r) {K : ℝ}
    (hK : ∀ r ∈ Set.Icc 0 t, ∀ x, ‖Torus.grad (propagator D ρ r t φ) x‖ ≤ K) :
    Measurable (a33_g D ρ q t φ) ∧ ∀ p, ‖a33_g D ρ q t φ p‖ ≤ Real.sqrt (2 * q) * K := by
  classical
  constructor
  · have h1 := a33_grad_meas_of_classical D ρ t φ f hcl
    have h2 : a33_g D ρ q t φ = fun p => Real.sqrt (2 * q) •
        (if p.1 ∈ Set.Icc 0 t then Torus.grad (f p.1) p.2 else 0) := by
      funext p
      unfold a33_g
      by_cases h : p.1 ∈ Set.Icc 0 t
      · simp [h, ht, hpe p.1 h]
      · simp [h]
    rw [h2]
    exact h1.const_smul (Real.sqrt (2 * q))
  · intro p
    unfold a33_g
    split_ifs with h
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hK p.1 h.1 p.2) (Real.sqrt_nonneg _)
    · simp only [norm_zero]
      refine mul_nonneg (Real.sqrt_nonneg _) ?_
      exact (norm_nonneg _).trans (hK 0 ⟨le_rfl, ht.le⟩ (Classical.arbitrary _))

theorem a34_cov_eq {T : ℝ} {ρ : ℝ → Torus d → ℝ} (hρ : A33Rho T ρ) (D : DynData d) {q t : ℝ}
    (hq : 0 ≤ q) (ht : t ∈ Set.Icc 0 T) {φ : Torus d → ℝ}
    (hmeas : Measurable (a33_g D ρ q t φ)) {B : ℝ} (hbd : ∀ p, ‖a33_g D ρ q t φ p‖ ≤ B) :
    2 * q * ∫ r in Set.Icc 0 (min t t), ∫ x : Torus d,
        inner ℝ (Torus.grad (propagator D ρ r t φ) x) (Torus.grad (propagator D ρ r t φ) x) *
          ρ r x = ∫ p, ‖a34_h D ρ q t φ p‖ ^ 2 ∂(a33_mu0 d T) := by
  classical
  rcases ht.1.eq_or_lt with h0 | h0
  · have hz : a33_g D ρ q t φ = 0 := a34_g_zero D ρ q t φ (by rw [← h0]; exact lt_irrefl _)
    have : ∀ p, a34_h D ρ q t φ p = 0 := fun p => by
      simp [a34_h, hz]
    simp only [this, norm_zero]
    rw [← h0, min_self, Set.Icc_self, setIntegral_measure_zero _ (by simp), mul_zero]
    simp
  · obtain ⟨Bρ, hBρ⟩ := hρ.bound
    set F : ℝ × Torus d → ℝ := fun p => ‖a34_h D ρ q t φ p‖ ^ 2 with hF
    have hFae : ∀ᵐ p ∂(a33_mu0 d T), F p = ρ p.1 p.2 * ‖a33_g D ρ q t φ p‖ ^ 2 := by
      filter_upwards [a33_ae_mu0 (d := d) T] with p hp
      simp only [hF, a34_h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        mul_pow, Real.sq_sqrt (hρ.nonneg p.1 hp p.2)]
    have hFm : AEStronglyMeasurable F (a33_mu0 d T) := by
      refine (AEStronglyMeasurable.congr ?_ (Filter.EventuallyEq.symm (show F =ᵐ[a33_mu0 d T] _ from hFae)))
      exact (hρ.aemeasurable.mul (hmeas.norm.pow_const 2).aemeasurable).aestronglyMeasurable
    have hFint : Integrable F (a33_mu0 d T) := by
      refine Integrable.of_bound hFm (Bρ * B ^ 2) ?_
      filter_upwards [hFae, a33_ae_mu0 (d := d) T] with p h1 hp
      rw [h1, Real.norm_eq_abs, abs_mul]
      refine mul_le_mul (hBρ p.1 hp p.2) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hBρ p.1 hp p.2))
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbd p) 2
    have hfub := integral_prod F hFint
    have hprod : a33_mu0 d T = (volume.restrict (Set.Icc 0 T)).prod volume := rfl
    rw [hprod, hfub]
    set Φ : ℝ → ℝ := fun r => ∫ x : Torus d,
      inner ℝ (Torus.grad (propagator D ρ r t φ) x) (Torus.grad (propagator D ρ r t φ) x) *
        ρ r x with hΦ
    have hinner : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫ x : Torus d, F (r, x) =
        (Set.Icc 0 t).indicator (fun r => 2 * q * Φ r) r := by
      intro r hr
      by_cases hr' : r ∈ Set.Icc 0 t
      · rw [Set.indicator_of_mem hr']
        have : ∀ x : Torus d, F (r, x) = 2 * q * (inner ℝ (Torus.grad (propagator D ρ r t φ) x)
            (Torus.grad (propagator D ρ r t φ) x) * ρ r x) := by
          intro x
          simp only [hF, a34_h, a33_g, hr', h0, and_self, ite_true, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hρ.nonneg r hr x),
            real_inner_self_eq_norm_sq]
          rw [Real.sq_sqrt (by linarith)]
          ring
        simp_rw [this]
        rw [integral_const_mul]
      · rw [Set.indicator_of_notMem hr']
        have : ∀ x : Torus d, F (r, x) = 0 := by
          intro x
          have : a33_g D ρ q t φ (r, x) = 0 := by
            unfold a33_g
            exact if_neg (fun h => hr' h.1)
          simp [hF, a34_h, this]
        simp_rw [this]
        simp
    have hcongr : ∫ r, ∫ x : Torus d, F (r, x) ∂volume ∂(volume.restrict (Set.Icc 0 T)) =
        ∫ r, (Set.Icc 0 t).indicator (fun r => 2 * q * Φ r) r ∂(volume.restrict (Set.Icc 0 T)) := by
      refine integral_congr_ae ?_
      exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hinner)
    rw [hcongr, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.2 (Set.Icc_subset_Icc le_rfl ht.2), min_self, integral_const_mul]

/-- `∫ |∇u|² ≤ ‖u‖²_{H¹}` for `u ∈ C²`. -/
theorem a34_grad_H1 {u : Torus d → ℝ} (hu : Torus.IsCk 2 u) :
    ∫ x, ‖Torus.grad u x‖ ^ 2 ≤ sobolevNorm 1 u ^ 2 := by
  have hu1 : Torus.IsCk 1 u := hu.of_le (by norm_num)
  have huc : Continuous u := MFAux.continuous_of_isCk hu1
  have hL2 : MemLp u 2 volume := huc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm2 : MemHs ((2 : ℕ) : ℝ) (coeffOf u) := MFSemigroup.memHs_nat_of_isCk 2 u hu
  have hm1' : MemHs 1 (coeffOf u) := hm2.mono (by norm_num)
  have hS : MemSobolev 1 u := memSobolev_of_memHs 1 u hL2 hm1'
  rw [← (hsNormSq_coeffOf 1 u hS).2, ← MFApriori.grad_parseval hu1]
  have hterm : ∀ k : Lattice d, sobWeight 0 k *
      ‖((2 * Real.pi * Lattice.enorm k : ℝ) : ℂ) * coeffOf u k‖ ^ 2 ≤ sobWeight 1 k * ‖coeffOf u k‖ ^ 2 := by
    intro k
    rw [sobWeight_zero, one_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    unfold sobWeight
    rw [Real.rpow_one]
    nlinarith [sq_nonneg (Real.pi * Lattice.enorm k)]
  unfold hsNormSq
  refine Summable.tsum_le_tsum hterm ?_ hm1'
  exact Summable.of_nonneg_of_le (fun k => mul_nonneg (by rw [sobWeight_zero]; norm_num) (sq_nonneg _))
    hterm hm1'

/-- Fibrewise bounds integrate over `[0,t]`. -/
theorem a34_Y_bound {T t : ℝ} (ht : t ∈ Set.Icc 0 T) {u : ℝ × Torus d → Euc d}
    (hu : Measurable u) {K : ℝ} (hK : ∀ p, ‖u p‖ ≤ K)
    (hz : ∀ p : ℝ × Torus d, p.1 ∉ Set.Icc 0 t → u p = 0) {Y₀ : ℝ}
    (hY : ∀ r ∈ Set.Icc (0 : ℝ) t, ∫ x : Torus d, ‖u (r, x)‖ ^ 2 ≤ Y₀) (hY0 : 0 ≤ Y₀) :
    ∫ p, ‖u p‖ ^ 2 ∂(a33_mu0 d T) ≤ t * Y₀ := by
  classical
  have hint : Integrable (fun p => ‖u p‖ ^ 2) (a33_mu0 d T) :=
    a34_integrable_sq hu.aemeasurable (Eventually.of_forall hK)
  have hprod : a33_mu0 d T = (volume.restrict (Set.Icc 0 T)).prod volume := rfl
  rw [hprod] at hint ⊢
  rw [integral_prod _ hint]
  have hI : Integrable (fun r => ∫ x : Torus d, ‖u (r, x)‖ ^ 2) (volume.restrict (Set.Icc 0 T)) :=
    hint.integral_prod_left
  have hle : ∀ᵐ r ∂(volume.restrict (Set.Icc 0 T)),
      ∫ x : Torus d, ‖u (r, x)‖ ^ 2 ≤ (Set.Icc 0 t).indicator (fun _ => Y₀) r := by
    refine Eventually.of_forall fun r => ?_
    by_cases hr : r ∈ Set.Icc 0 t
    · rw [Set.indicator_of_mem hr]; exact hY r hr
    · rw [Set.indicator_of_notMem hr]
      have : ∀ x : Torus d, ‖u (r, x)‖ ^ 2 = 0 := fun x => by simp [hz (r, x) hr]
      simp_rw [this]; simp
  have h2 := integral_mono_ae hI ((integrable_indicator_iff measurableSet_Icc).2
    (integrableOn_const (by rw [Measure.restrict_apply measurableSet_Icc, Set.inter_eq_left.2 (Set.Icc_subset_Icc le_rfl ht.2)]; simp) (by simp)) ) hle
  refine h2.trans ?_
  rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.2 (Set.Icc_subset_Icc le_rfl ht.2)]
  simp [Measure.real, mul_comm, ht.1]

end HRS.A34
