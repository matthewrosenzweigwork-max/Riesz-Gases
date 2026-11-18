import HRS.MS.SuppU11Aux1
import HRS.Whole.Q34Aux18

/-!
# U11 helper file 2: Bessel inequality for the response form `β⟨f, R_{β,μ} e_ℓ⟩`.

For `K_μ` a bounded symmetric nonnegative operator on `L²(ν)` (the Q34 packet), the form
`Q(U,V) = β⟨(I+βK)U, V⟩` is symmetric positive semidefinite, the responses `R e_ℓ` are
`Q`-orthonormal (the hypothesis `orth`), and the coefficients `β⟨f, R e_ℓ⟩ = Q(Rf, Re_ℓ)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.Whole

variable {d : ℕ}

section Model

variable {ρ : Euc d → ℝ} {M s : ℝ}
variable [IsProbabilityMeasure (withDensityReal ρ)]

lemma u11_toLp_Pc {f : Euc d → ℝ} (hf : MemL2Zero (withDensityReal ρ) f) :
    Q34.Pc (withDensityReal ρ) (hf.1.toLp f) = hf.1.toLp f := by
  have h0 : inner ℝ (Q34.one2 (withDensityReal ρ)) (hf.1.toLp f) = 0 := by
    rw [Q34.inner_one2]
    exact (integral_congr_ae (MemLp.coeFn_toLp hf.1)).trans hf.2
  rw [Q34.Pc_apply, h0]
  simp

lemma u11_resp_isResponse (h : Q34.Q34Hyp d s ρ M) {β : ℝ} (hβ : 0 < β) {ψ : Euc d → ℝ}
    (hψ : MemL2Zero (withDensityReal ρ) ψ) :
    IsResponse (rieszKernel d s) (withDensityReal ρ) β ψ
      (responseInverse (rieszKernel d s) (withDensityReal ρ) β ψ) := by
  have hex := (Q34.partD h hβ hψ).1
  unfold responseInverse
  rw [dif_pos hex]
  exact hex.choose_spec

lemma u11_resp_lp (h : Q34.Q34Hyp d s ρ M) {β : ℝ} (hβ : 0 < β) {ψ : Euc d → ℝ}
    (hψ : MemL2Zero (withDensityReal ρ) ψ) :
    (u11_resp_isResponse h hβ hψ).1.1.toLp
        (responseInverse (rieszKernel d s) (withDensityReal ρ) β ψ) +
      β • Q34.Kc h ((u11_resp_isResponse h hβ hψ).1.1.toLp
        (responseInverse (rieszKernel d s) (withDensityReal ρ) β ψ)) = hψ.1.toLp ψ := by
  set r := responseInverse (rieszKernel d s) (withDensityReal ρ) β ψ with hr
  have hresp := u11_resp_isResponse h hβ hψ
  set Y := hresp.1.1.toLp r with hY
  have hYae : r =ᵐ[withDensityReal ρ] (Y : Euc d → ℝ) := (MemLp.coeFn_toLp hresp.1.1).symm
  have hKY := Q34.kop_class h hYae (u11_toLp_Pc hresp.1)
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add Y (β • Q34.Kc h Y), Lp.coeFn_smul β (Q34.Kc h Y), hKY, hresp.2,
    hYae, MemLp.coeFn_toLp hψ.1] with x h1 h2 h3 h4 h5 h6
  have hpm : projMean (withDensityReal ρ) ψ x = ψ x := by simp [projMean, pair, hψ.2]
  have h4' : r x + β * Kop (rieszKernel d s) (withDensityReal ρ) r x =
      projMean (withDensityReal ρ) ψ x := h4
  rw [h1]
  simp only [Pi.add_apply]
  rw [h2, h6]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← h3, ← h5]
  linarith [h4', hpm]

/-- The form `Q(U,V) = β⟨U,V⟩ + β²⟨KU,V⟩ = β⟨(I+βK)U, V⟩`. -/
def u11Q (h : Q34.Q34Hyp d s ρ M) (β : ℝ) :
    Lp ℝ 2 (withDensityReal ρ) →ₗ[ℝ] Lp ℝ 2 (withDensityReal ρ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun U V => β * inner ℝ U V + β ^ 2 * inner ℝ (Q34.Kc h U) V)
    (by intro U1 U2 V; simp only [inner_add_left, map_add]; ring)
    (by intro c U V; simp only [real_inner_smul_left, map_smul, smul_eq_mul]; ring)
    (by intro U V1 V2; simp only [inner_add_right]; ring)
    (by intro c U V; simp only [real_inner_smul_right, smul_eq_mul]; ring)

lemma u11Q_apply (h : Q34.Q34Hyp d s ρ M) (β : ℝ) (U V : Lp ℝ 2 (withDensityReal ρ)) :
    u11Q h β U V = β * inner ℝ U V + β ^ 2 * inner ℝ (Q34.Kc h U) V := rfl

lemma u11Q_eq (h : Q34.Q34Hyp d s ρ M) (β : ℝ) (U V : Lp ℝ 2 (withDensityReal ρ)) :
    u11Q h β U V = β * inner ℝ (U + β • Q34.Kc h U) V := by
  rw [u11Q_apply, inner_add_left, real_inner_smul_left]
  ring

lemma u11Q_symm (h : Q34.Q34Hyp d s ρ M) (β : ℝ) (U V : Lp ℝ 2 (withDensityReal ρ)) :
    u11Q h β U V = u11Q h β V U := by
  have e1 : inner ℝ V U = inner ℝ U V := real_inner_comm U V
  have e2 : inner ℝ (Q34.Kc h V) U = inner ℝ (Q34.Kc h U) V :=
    (real_inner_comm U (Q34.Kc h V)).trans (Q34.Kc_symm h U V).symm
  rw [u11Q_apply, u11Q_apply, e1, e2]

lemma u11Q_pos (h : Q34.Q34Hyp d s ρ M) {β : ℝ} (hβ : 0 < β) (U : Lp ℝ 2 (withDensityReal ρ)) :
    0 ≤ u11Q h β U U := by
  rw [u11Q_apply]
  have h1 := real_inner_self_nonneg (x := U)
  have h2 := Q34.Kc_pos h U
  positivity

lemma u11_bessel_model (h : Q34.Q34Hyp d s ρ M) {β : ℝ} (hβ : 0 < β) (e : ℕ → Euc d → ℝ)
    (he : ∀ l, MemL2Zero (withDensityReal ρ) (e l))
    (horth : ∀ l j, β * l2Inner (withDensityReal ρ) (e l)
      (responseInverse (rieszKernel d s) (withDensityReal ρ) β (e j)) = if l = j then 1 else 0)
    {f : Euc d → ℝ} (hf : MemL2Zero (withDensityReal ρ) f) (S : Finset ℕ) :
    ∑ l ∈ S, (β * l2Inner (withDensityReal ρ) f
      (responseInverse (rieszKernel d s) (withDensityReal ρ) β (e l))) ^ 2 ≤
      β * ∫ x, f x ^ 2 ∂(withDensityReal ρ) := by
  set ν := withDensityReal ρ with hν
  have hRm : ∀ ψ, MemL2Zero ν ψ →
      MemL2Zero ν (responseInverse (rieszKernel d s) ν β ψ) :=
    fun ψ hψ => (u11_resp_isResponse h hβ hψ).1
  set Y : ℕ → Lp ℝ 2 ν := fun l => (hRm _ (he l)).1.toLp
    (responseInverse (rieszKernel d s) ν β (e l)) with hYdef
  set E : ℕ → Lp ℝ 2 ν := fun l => (he l).1.toLp (e l) with hEdef
  have hYE : ∀ l, Y l + β • Q34.Kc h (Y l) = E l := fun l => u11_resp_lp h hβ (he l)
  set Yf : Lp ℝ 2 ν := (hRm _ hf).1.toLp (responseInverse (rieszKernel d s) ν β f) with hYf
  set Ff : Lp ℝ 2 ν := hf.1.toLp f with hFf
  have hYF : Yf + β • Q34.Kc h Yf = Ff := u11_resp_lp h hβ hf
  have hinE : ∀ l j, inner ℝ (E l) (Y j) =
      l2Inner ν (e l) (responseInverse (rieszKernel d s) ν β (e j)) := fun l j =>
    (Q34.l2Inner_eq (MemLp.coeFn_toLp (he l).1).symm (MemLp.coeFn_toLp (hRm _ (he j)).1).symm).symm
  have hQorth : ∀ l j, u11Q h β (Y l) (Y j) = if l = j then 1 else 0 := by
    intro l j
    rw [u11Q_eq, hYE l, hinE, horth]
  have hcoef : ∀ l, β * l2Inner ν f (responseInverse (rieszKernel d s) ν β (e l)) =
      u11Q h β Yf (Y l) := by
    intro l
    rw [u11Q_eq, hYF]
    have := Q34.l2Inner_eq (ν := ν) (MemLp.coeFn_toLp hf.1).symm
      (MemLp.coeFn_toLp (hRm _ (he l)).1).symm
    rw [this]
  have hdiag : u11Q h β Yf Yf ≤ β * ∫ x, f x ^ 2 ∂ν := by
    rw [u11Q_eq, hYF]
    have h1 := Q34.l2Inner_eq (ν := ν) (MemLp.coeFn_toLp hf.1).symm
      (MemLp.coeFn_toLp (hRm _ hf).1).symm
    have h2 := (Q34.partD h hβ hf).2.2.2.1
    rw [← h1]
    exact mul_le_mul_of_nonneg_left h2 hβ.le
  have hb := u11_bessel (u11Q h β) (u11Q_symm h β) (u11Q_pos h hβ) Y hQorth Yf S
  calc ∑ l ∈ S, (β * l2Inner ν f (responseInverse (rieszKernel d s) ν β (e l))) ^ 2
      = ∑ l ∈ S, u11Q h β Yf (Y l) ^ 2 := Finset.sum_congr rfl fun l _ => by rw [hcoef]
    _ ≤ u11Q h β Yf Yf := hb
    _ ≤ _ := hdiag

end Model

/-- Sup bound of the oscillator test functions. -/
lemma u11_osc_bound : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (m : ℝ) (α : MultiIndex d) (x : Euc d),
    |oscTestFun m α x| ≤ C0 * oscEigenvalue d α ^ (-(m / 2)) := by
  obtain ⟨C, hC⟩ := hermiteFunD_uniform_bound (d := d)
  refine ⟨max C 0, le_max_right _ _, fun m α x => ?_⟩
  unfold oscTestFun
  have hpos : 0 ≤ oscEigenvalue d α ^ (-(m / 2)) :=
    Real.rpow_nonneg (oscEv_pos α).le _
  rw [abs_mul, abs_of_nonneg hpos, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hC α x).trans (le_max_left _ _)) hpos

lemma u11_osc_continuous (m : ℝ) (α : MultiIndex d) : Continuous (oscTestFun m α) :=
  continuous_const.mul (contDiff_hermiteFunD α).continuous

/-- Centered bounded continuous functions: `P_ν φ ∈ L²_0` and its second moment is `≤ 4K²`. -/
lemma u11_projMean_bound (ν : Measure (Euc d)) [IsProbabilityMeasure ν] {φ : Euc d → ℝ}
    (hφ : Continuous φ) {K : ℝ} (hK : ∀ x, |φ x| ≤ K) :
    MemL2Zero ν (projMean ν φ) ∧ ∫ x, projMean ν φ x ^ 2 ∂ν ≤ 4 * K ^ 2 := by
  have hmem : MemLp φ 2 ν :=
    MemLp.of_bound hφ.aestronglyMeasurable K
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hK x)
  have hI : Integrable φ ν := hmem.integrable (by norm_num)
  have hc : |pair ν φ| ≤ K := by
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := φ) (C := K)
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hK x)
    simpa [pair, Real.norm_eq_abs] using this
  have hmem2 : MemLp (projMean ν φ) 2 ν := by
    unfold projMean
    exact hmem.sub (memLp_const (pair ν φ))
  refine ⟨⟨hmem2, ?_⟩, ?_⟩
  · simp only [projMean]
    rw [integral_sub hI (integrable_const _), integral_const]
    simp [pair]
  · have hb : ∀ x, projMean ν φ x ^ 2 ≤ (2 * K) ^ 2 := by
      intro x
      have h1 := hK x
      have h2 := abs_le.1 h1
      have h3 := abs_le.1 hc
      have hK0 : 0 ≤ K := (abs_nonneg _).trans h1
      simp only [projMean]
      nlinarith [h2.1, h2.2, h3.1, h3.2]
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun x => projMean ν φ x ^ 2)
      (C := (2 * K) ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hb x)
    have h4 : ∫ x, projMean ν φ x ^ 2 ∂ν ≤ (2 * K) ^ 2 := by
      refine (le_abs_self _).trans ?_
      simpa [Real.norm_eq_abs] using this
    nlinarith [h4]

end HRS.Whole
