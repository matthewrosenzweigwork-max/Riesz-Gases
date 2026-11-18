import HRS.MS.SuppU11Aux3
import HRS.Whole.CriticalNoise

/-!
# S8.8.A03: finite synthesis bound in the direction opposite to Bessel

`s88_finite_synthesis_bound`: for spectral data `(e_l, ω_l)` of a thermal equilibrium `ρ`, there is `K ≥ 0`
with `‖∑_{i<p} r_i e_i‖²_{L²(μ)} ≤ K ∑ r_i²` for every finite coefficient vector.  The proof uses only the
`Q`-orthonormality of the responses `Y_i = R e_i` for the form `Q(U,V) = β⟨(I+βK)U,V⟩` and the norm bound
`‖K‖ ≤ Mg` of the Riesz operator: with `Y = ∑ r_i Y_i` one has `Y + βKY = ∑ r_i e_i`,
`Q(Y,Y) = ∑ r_i²` and `Q(Y,Y) ≥ β‖Y‖²`.  The constant is `K = (1 + β Mg)² / β`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S88Breakdown

open HRS HRS.Whole

section Core

variable {d : ℕ} {ν : Measure (Euc d)}

lemma s88_ae_sum {ι : Type*} (n : Finset ι) (E : ι → Lp ℝ 2 ν) (r : ι → ℝ) :
    (⇑(∑ i ∈ n, r i • E i : Lp ℝ 2 ν) : Euc d → ℝ) =ᵐ[ν]
      fun x => ∑ i ∈ n, r i * (E i : Euc d → ℝ) x := by
  classical
  induction n using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℝ 2 ν
  | insert a n ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (r a • E a) (∑ i ∈ n, r i • E i), Lp.coeFn_smul (r a) (E a), ih]
      with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, h3, Finset.sum_insert ha]

end Core

section Model

variable {d : ℕ} {ρ : Euc d → ℝ} {M s : ℝ}
variable [IsProbabilityMeasure (HRS.Whole.withDensityReal ρ)]

/-- Core finite synthesis estimate at the level of the Q34 hypotheses. -/
theorem s88_fin_core (h : Q34.Q34Hyp d s ρ M) {β : ℝ} (hβ : 0 < β) (e : ℕ → Euc d → ℝ)
    (he : ∀ l, MemL2Zero (HRS.Whole.withDensityReal ρ) (e l))
    (horth : ∀ l j, β * HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ) (e l)
      (HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (e j)) = if l = j then 1 else 0)
    {p : ℕ} (r : Fin p → ℝ) :
    ∫ x, (∑ i : Fin p, r i * e (i : ℕ) x) ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
      ((1 + β * Q34.Mg d s M) ^ 2 / β) * ∑ i : Fin p, (r i) ^ 2 := by
  set ν := HRS.Whole.withDensityReal ρ with hν
  have hRm : ∀ ψ, MemL2Zero ν ψ →
      MemL2Zero ν (HRS.Whole.responseInverse (rieszKernel d s) ν β ψ) :=
    fun ψ hψ => (u11_resp_isResponse h hβ hψ).1
  set Y : ℕ → Lp ℝ 2 ν := fun l => (hRm _ (he l)).1.toLp
    (HRS.Whole.responseInverse (rieszKernel d s) ν β (e l)) with hYdef
  set E : ℕ → Lp ℝ 2 ν := fun l => (he l).1.toLp (e l) with hEdef
  have hYE : ∀ l, Y l + β • Q34.Kc h (Y l) = E l := fun l => u11_resp_lp h hβ (he l)
  have hinE : ∀ l j, inner ℝ (E l) (Y j) =
      HRS.Whole.l2Inner ν (e l) (HRS.Whole.responseInverse (rieszKernel d s) ν β (e j)) := fun l j =>
    (Q34.l2Inner_eq (MemLp.coeFn_toLp (he l).1).symm (MemLp.coeFn_toLp (hRm _ (he j)).1).symm).symm
  have hQorth : ∀ l j, u11Q h β (Y l) (Y j) = if l = j then 1 else 0 := by
    intro l j
    rw [u11Q_eq, hYE l, hinE, horth]
  set Ys : Lp ℝ 2 ν := ∑ i : Fin p, r i • Y (i : ℕ) with hYs
  set Fs : Lp ℝ 2 ν := ∑ i : Fin p, r i • E (i : ℕ) with hFs
  have hF : Ys + β • Q34.Kc h Ys = Fs := by
    have : Ys + β • Q34.Kc h Ys = ∑ i : Fin p, r i • (Y (i : ℕ) + β • Q34.Kc h (Y (i : ℕ))) := by
      simp only [hYs, map_sum, map_smul, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm]
    rw [this]
    exact Finset.sum_congr rfl fun i _ => by rw [hYE]
  have hQ : u11Q h β Ys Ys = ∑ i : Fin p, r i ^ 2 := by
    have : u11Q h β Ys Ys = ∑ j : Fin p, r j * ∑ i : Fin p, r i * u11Q h β (Y (i : ℕ)) (Y (j : ℕ)) := by
      simp only [hYs, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hQorth, Fin.val_inj, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ j]
    simp [sq]
  have hlow : β * ‖Ys‖ ^ 2 ≤ u11Q h β Ys Ys := by
    rw [u11Q_apply, real_inner_self_eq_norm_sq]
    have := Q34.Kc_pos h Ys
    nlinarith [sq_nonneg β]
  have hnorm : ‖Fs‖ ≤ (1 + β * Q34.Mg d s M) * ‖Ys‖ := by
    rw [← hF]
    calc ‖Ys + β • Q34.Kc h Ys‖ ≤ ‖Ys‖ + ‖β • Q34.Kc h Ys‖ := norm_add_le _ _
      _ = ‖Ys‖ + β * ‖Q34.Kc h Ys‖ := by rw [norm_smul, Real.norm_of_nonneg hβ.le]
      _ ≤ ‖Ys‖ + β * (Q34.Mg d s M * ‖Ys‖) := by
          gcongr
          exact Q34.Kc_norm_le h Ys
      _ = _ := by ring
  have hae : (fun x => ∑ i : Fin p, r i * e (i : ℕ) x) =ᵐ[ν] (Fs : Euc d → ℝ) := by
    have h1 := s88_ae_sum (ν := ν) (Finset.univ : Finset (Fin p)) (fun i => E (i : ℕ)) r
    have h2 : ∀ᵐ x ∂ν, ∀ i : Fin p, (E (i : ℕ) : Euc d → ℝ) x = e (i : ℕ) x :=
      ae_all_iff.2 fun i => MemLp.coeFn_toLp (he (i : ℕ)).1
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hFs, hx1]
    exact Finset.sum_congr rfl fun i _ => by rw [hx2 i]
  rw [Q34.integral_sq_eq hae]
  have hY2 : ‖Ys‖ ^ 2 ≤ (∑ i : Fin p, r i ^ 2) / β := by
    rw [le_div_iff₀ hβ]; nlinarith [hlow, hQ]
  calc ‖Fs‖ ^ 2 ≤ ((1 + β * Q34.Mg d s M) * ‖Ys‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (1 + β * Q34.Mg d s M) ^ 2 * ‖Ys‖ ^ 2 := by ring
    _ ≤ (1 + β * Q34.Mg d s M) ^ 2 * ((∑ i : Fin p, r i ^ 2) / β) :=
        mul_le_mul_of_nonneg_left hY2 (sq_nonneg _)
    _ = _ := by ring

end Model

theorem s88_finite_synthesis_bound {d : ℕ} (hd : 2 ≤ d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (ρ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ)
    (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) (hdata : IsSpectralData d β ρ e om) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : ℕ) (r : Fin p → ℝ),
      (∫ x, (∑ i : Fin p, r i * e (i : ℕ) x) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤
        K * ∑ i : Fin p, (r i) ^ 2 := by
  have hprob : HRS.Whole.IsProbDensity ρ := hρ.1.1
  obtain ⟨M, hM⟩ := u11_rho_le hd ha hβ hρ
  have := Q34.isProbabilityMeasure_nu hprob
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hQ : Q34.Q34Hyp d ((d : ℝ) / 2) ρ M :=
    ⟨by omega, by positivity, by linarith, hprob, hM⟩
  have hM0 : 0 ≤ M := (hprob.nonneg 0).trans (hM 0)
  have hMg0 := Q34.Mg_nonneg hQ.hd hQ.hsd hM0
  refine ⟨(1 + β * Q34.Mg d ((d : ℝ) / 2) M) ^ 2 / β, by positivity, fun p r => ?_⟩
  exact s88_fin_core hQ hβ e hdata.centered hdata.orth r

end HRS.MS.S88Breakdown
