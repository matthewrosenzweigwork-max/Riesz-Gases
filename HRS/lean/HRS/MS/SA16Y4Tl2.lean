import HRS.MS.SA16Y4Tl1
import HRS.MS.SA16Y4Wk1
import HRS.MS.SA16SOp3

/-!
# S.A.16 (SA16Y4) Tl2: limit of the transport pairing, derivative on the solution (`C^0` convergence of the coefficients)

`sa16y4_div_ibp`: `∫ wrep G · div(cψ) = -∑_k ∫ G_{e_k} (c_k ψ)` for `c_k ∈ C^1`, `ψ ∈ C_c^∞`, `m ≥ 1`.
`sa16y4_transport_limit`: if `c_N → c` uniformly on `supp ψ` (`C^0` only), `g_N` bounded and weakly convergent to `G`, then
`∫ wrep g_N · div(c_N ψ) → ∫ wrep G · div(c ψ)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Tl2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y4_cpsi_data {c : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hc : ∀ k, ContDiff ℝ 1 (c k))
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (k : Fin d) :
    ContDiff ℝ 1 (fun y => c k y * ψ y) ∧
      MemLp (fun y => c k y * ψ y) (ENNReal.conjExponent (ENNReal.ofReal p)) volume ∧
      MemLp (fun x => fderiv ℝ (fun y => c k y * ψ y) x (EuclideanSpace.single k 1))
        (ENNReal.conjExponent (ENNReal.ofReal p)) volume := by
  have h1 : ContDiff ℝ 1 (fun y => c k y * ψ y) := (hc k).mul (hψ.1.of_le (by exact_mod_cast le_top))
  have hs : HasCompactSupport (fun y => c k y * ψ y) := hψ.2.mul_left
  refine ⟨h1, h1.continuous.memLp_of_hasCompactSupport hs, ?_⟩
  refine (((h1.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport ?_
  exact (hs.fderiv ℝ).comp_left (g := fun A : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => A (EuclideanSpace.single k 1)) (by simp)

theorem sa16y4_div_ibp {m : ℕ} (hm : 1 ≤ m) {c : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : ∀ k, ContDiff ℝ 1 (c k)) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (G : WmpSpace d m p) :
    ∫ x, wrep d m p G x * sa16so_divFun c ψ x =
      -∑ k : Fin d, ∫ x, sa16y4_cmp d m p (sa16y4_tau1 d m hm k) G x * (c k x * ψ x) := by
  have hint : ∀ k : Fin d, Integrable (fun x => wrep d m p G x *
      fderiv ℝ (fun y => c k y * ψ y) x (EuclideanSpace.single k 1)) := fun k =>
    (sa16y3_wrep_memLp G).integrable_mul (sa16y4_cpsi_data (p := p) hc hψ k).2.2
  unfold sa16so_divFun
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun k _ => hint k, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨h1, h2, h3⟩ := sa16y4_cpsi_data (p := p) hc hψ k
  have := sa16y4_comp_ibp (p := p) hm k h1 h2 h3 G
  rw [← neg_neg (∫ x, wrep d m p G x * fderiv ℝ (fun y => c k y * ψ y) x (EuclideanSpace.single k 1)), ← this]
  rfl

theorem sa16y4_transport_limit {m : ℕ} (hm : 1 ≤ m) {Bm R0 : ℝ} (cs : ℕ → Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (hcs : ∀ N k, ContDiff ℝ 1 (cs N k)) (cl : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (hcl : ∀ k, ContDiff ℝ 1 (cl k)) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ)
    (hψ0 : ∀ x, R0 < ‖x‖ → ψ x = 0)
    (huni : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ k x, ‖x‖ ≤ R0 → |cs N k x - cl k x| ≤ ε)
    (gs : ℕ → WmpSpace d m p) (G : WmpSpace d m p) (hbd : ∀ j, ‖gs j‖ ≤ Bm)
    (hw : ∀ ℓ : StrongDual ℝ (WmpSpace d m p), Tendsto (fun j => ℓ (gs j)) atTop (𝓝 (ℓ G))) :
    Tendsto (fun N => ∫ x, wrep d m p (gs N) x * sa16so_divFun (cs N) ψ x) atTop
      (𝓝 (∫ x, wrep d m p G x * sa16so_divFun cl ψ x)) := by
  simp_rw [sa16y4_div_ibp (p := p) hm (hcs _) hψ, sa16y4_div_ibp (p := p) hm hcl hψ]
  refine (tendsto_finsetSum _ fun k _ => ?_).neg
  have hq : ENNReal.conjExponent (ENNReal.ofReal p) ≠ ⊤ := (sa16y3_conj_bridge (Fact.out : 2 ≤ p)).1
  have hq0 : ENNReal.conjExponent (ENNReal.ofReal p) ≠ 0 := by
    intro h
    have := (sa16y3_conj_bridge (Fact.out : 2 ≤ p)).2.1
    rw [h] at this; norm_num at this
  have hcont : ∀ N, Continuous (fun y => cs N k y * ψ y) := fun N => (hcs N k).continuous.mul hψ.1.continuous
  have hcont' : Continuous (fun y => cl k y * ψ y) := (hcl k).continuous.mul hψ.1.continuous
  refine sa16y4_comp_tendsto_Lq (p := p) (sa16y4_tau1 d m hm k) gs G hbd hw (fun N x => cs N k x * ψ x)
    (fun x => cl k x * ψ x) (fun N => (hcont N).aestronglyMeasurable) hcont'.aestronglyMeasurable
    (fun N => (sa16y4_cpsi_data (p := p) (hcs N) hψ k).2.1) (sa16y4_cpsi_data (p := p) hcl hψ k).2.1 ?_
  refine sa16y4_Lq_of_unif hq hq0 R0 _ _ hcont hcont' (fun N x hx => by simp [hψ0 x hx])
    (fun x hx => by simp [hψ0 x hx]) ?_
  intro ε hε
  obtain ⟨S, hS⟩ := hψ.1.continuous.bounded_above_of_compact_support hψ.2
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  filter_upwards [huni (ε / (S + 1)) (by positivity)] with N hN x
  by_cases hx : ‖x‖ ≤ R0
  · have := hN k x hx
    calc |cs N k x * ψ x - cl k x * ψ x| = |cs N k x - cl k x| * |ψ x| := by rw [← sub_mul, abs_mul]
      _ ≤ (ε / (S + 1)) * S := mul_le_mul this (by simpa [Real.norm_eq_abs] using hS x) (abs_nonneg _) (by positivity)
      _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
  · rw [not_le] at hx
    simp [hψ0 x hx, hε.le]

end Tl2

end HRS.Whole.AppendixA.Phase2SA16R
