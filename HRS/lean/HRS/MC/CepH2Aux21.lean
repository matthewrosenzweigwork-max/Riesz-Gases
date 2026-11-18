import HRS.MC.CepH2Aux20

/-!
# CEPH2, helper 21: pointwise fundamental theorem of calculus for the free-energy density

`Φ(u_t(x), x) - Φ(u_0(x), x) = ∫_0^t (ℓ_s(x) + 1) a(s,x) ds` for `Φ(r,x) = r log r + r U(x)/θ`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- The free-energy density `Φ(r, x) = r log r + r U(x)/θ`. -/
def h2_Phi (θ : ℝ) (U : Ch N → ℝ) (r : ℝ) (x : Ch N) : ℝ := r * Real.log r + r * U x / θ

section
variable {θ v : ℝ} {U : Ch N → ℝ} {K : ℝ≥0} {μ : ℝ → Measure (Ch N)} {T M : ℝ}

theorem H2Set.mu_time (S : H2Set θ v U K μ T M) (x : Ch N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    h2_mu v (μ t) x = h2_mu v (μ 0) x + ∫ s in Icc (0 : ℝ) t, ∫ y, h2_A θ v U x y ∂μ s := by
  have := S.hfp _ (h2_test_per_sub S.hv x) t ht
  simp_rw [h2_gen_per_sub S.hv θ U x] at this
  exact this

theorem H2Set.cont_u (S : H2Set θ v U K μ T M) (x : Ch N) : Continuous fun s => h2_mu v (μ s) x :=
  h2_continuous_integral_s S.hnar (h2_good_per S.hv U) x

theorem H2Set.cont_a (S : H2Set θ v U K μ T M) (x : Ch N) :
    Continuous fun s => ∫ y, h2_A θ v U x y ∂μ s :=
  h2_continuous_integral_s S.hnar (h2_good_A S.hv θ S.hU1 S.hUper S.hK) x

theorem H2Set.mu_pos (S : H2Set θ v U K μ T M) (s : ℝ) (x : Ch N) : 0 < h2_mu v (μ s) x := by
  haveI := S.hprob s
  exact h2_mu_pos S.hv (μ s) x

theorem H2Set.pointwise_ftc (S : H2Set θ v U K μ T M) (x : Ch N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    h2_Phi θ U (h2_mu v (μ t) x) x - h2_Phi θ U (h2_mu v (μ 0) x) x =
      ∫ s in Icc (0 : ℝ) t, (h2_ell θ v U (μ s) x + 1) * ∫ y, h2_A θ v U x y ∂μ s := by
  have ht0 : 0 ≤ t := ht.1
  set f : ℝ → ℝ := fun s => h2_mu v (μ s) x with hf
  set a : ℝ → ℝ := fun s => ∫ y, h2_A θ v U x y ∂μ s with ha
  have hfc : Continuous f := S.cont_u x
  have hac : Continuous a := S.cont_a x
  have hfpos : ∀ s, 0 < f s := fun s => S.mu_pos s x
  set ψ : ℝ → ℝ := fun r => r * Real.log r + r * U x / θ with hψ
  have hψd : ∀ r, 0 < r → HasDerivAt ψ (Real.log r + 1 + U x / θ) r := by
    intro r hr
    have h1 := (hasDerivAt_id r).mul (Real.hasDerivAt_log hr.ne')
    have h2 := ((hasDerivAt_id r).mul_const (U x)).div_const θ
    refine (h1.add h2).congr_deriv ?_
    have : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
    simp only [id_eq, one_mul]
    rw [this]
  set F : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, a r with hF
  have hrep : ∀ s ∈ Icc (0 : ℝ) T, f s = f 0 + F s := by
    intro s hs
    have := S.mu_time x hs
    rw [hF]
    simp only [hf]
    rw [this, intervalIntegral.integral_of_le hs.1, integral_Icc_eq_integral_Ioc]
  have hfd : ∀ s ∈ Ioo (0 : ℝ) T, HasDerivAt f (a s) s := by
    intro s hs
    have hF' : HasDerivAt F (a s) s := (hac.integral_hasStrictDerivAt 0 s).hasDerivAt
    have hev : f =ᶠ[𝓝 s] fun s' => f 0 + F s' := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with s' hs'
      exact hrep s' ⟨hs'.1.le, hs'.2.le⟩
    exact (hF'.const_add (f 0)).congr_of_eventuallyEq hev
  have hgc : Continuous fun s => (Real.log (f s) + 1 + U x / θ) * a s :=
    ((hfc.log fun s => (hfpos s).ne').add continuous_const |>.add continuous_const).mul hac
  have hcont : ContinuousOn (ψ ∘ f) (Icc 0 t) := by
    have : Continuous (ψ ∘ f) :=
      (hfc.mul (hfc.log fun s => (hfpos s).ne')).add ((hfc.mul continuous_const).div_const θ)
    exact this.continuousOn
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) t, HasDerivAt (ψ ∘ f) ((Real.log (f s) + 1 + U x / θ) * a s) s := by
    intro s hs
    exact (hψd (f s) (hfpos s)).comp s (hfd s ⟨hs.1, hs.2.trans_le ht.2⟩)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht0 hcont hderiv
    (hgc.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_of_le ht0, ← integral_Icc_eq_integral_Ioc] at key
  have e : ∀ s, (h2_ell θ v U (μ s) x + 1) * ∫ y, h2_A θ v U x y ∂μ s =
      (Real.log (f s) + 1 + U x / θ) * a s := fun s => by
    simp only [h2_ell, hf, ha]; ring
  simp_rw [e]
  rw [key]
  rfl

end

end HRS.MC.CepH2
