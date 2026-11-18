import HRS.MS.UniqM2

/-!
# M2 of `UniqPlan.md`, part 2: local-to-global for weak derivatives
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff Manifold

namespace HRS.MS.UniqM2

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqM1

variable {d : ℕ}

theorem integrable_mul_fderiv {u : Euc d → ℝ} (hu : LocallyIntegrable u volume) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (e : Euc d) :
    Integrable (fun x => u x * fderiv ℝ ψ x e) volume := by
  have hco : Continuous (fun x => fderiv ℝ ψ x e) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport (fun x => fderiv ℝ ψ x e) := hc.fderiv_apply ℝ e
  exact (hu.integrable_smul_left_of_hasCompactSupport hco hcs).congr
    (Eventually.of_forall fun x => by simp [mul_comm])

theorem integrable_mul_test {u : Euc d → ℝ} (hu : LocallyIntegrable u volume) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun x => u x * ψ x) volume := by
  exact (hu.integrable_smul_left_of_hasCompactSupport hψ.continuous hc).congr
    (Eventually.of_forall fun x => by simp [mul_comm])

/-- Local-to-global for the weak derivative identity, by a smooth partition of unity. -/
theorem glue_identity {u v : Euc d → ℝ} (hu : LocallyIntegrable u volume)
    (hv : LocallyIntegrable v volume) (e : Euc d)
    (h : ∀ c : Euc d, ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball c 1 →
      ∫ x, u x * fderiv ℝ ψ x e = - ∫ x, v x * ψ x)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∫ x, u x * fderiv ℝ ψ x e = - ∫ x, v x * ψ x := by
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Euc d) (isClosed_tsupport ψ)
    (fun c : Euc d => ball c 1) (fun c => isOpen_ball)
    (fun x _ => Set.mem_iUnion.2 ⟨x, mem_ball_self one_pos⟩)
  have hfin := f.locallyFinite.finite_nonempty_inter_compact hc
  set I := hfin.toFinset with hI
  have hfd : ∀ i, ContDiff ℝ ∞ (f i) := fun i => (f i).contMDiff.contDiff
  set g : Euc d → Euc d → ℝ := fun i x => f i x * ψ x with hg
  have hg1 : ∀ i, ContDiff ℝ ∞ (g i) := fun i => (hfd i).mul hψ
  have hg2 : ∀ i, HasCompactSupport (g i) := fun i => hc.mul_left
  have hg3 : ∀ i, tsupport (g i) ⊆ ball i 1 := fun i =>
    (tsupport_mul_subset_left).trans (hf i)
  have hsum : ∀ x, ψ x = ∑ i ∈ I, g i x := by
    intro x
    by_cases hx : x ∈ tsupport ψ
    · have h1 := f.sum_eq_one hx
      rw [finsum_eq_sum_of_support_subset _ (s := I) ?_] at h1
      · simp only [hg, ← Finset.sum_mul, h1, one_mul]
      · intro i hi
        rw [Function.mem_support] at hi
        simp only [hI, Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
        exact ⟨x, Function.mem_support.2 hi, hx⟩
    · have : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this, hg]
  have hψeq : ψ = fun x => ∑ i ∈ I, g i x := funext hsum
  have hder : ∀ x, fderiv ℝ ψ x e = ∑ i ∈ I, fderiv ℝ (g i) x e := by
    intro x
    have h1 : HasFDerivAt ψ (∑ i ∈ I, fderiv ℝ (g i) x) x := by
      rw [hψeq]
      exact HasFDerivAt.fun_sum fun i _ => ((hg1 i).differentiable (by simp) x).hasFDerivAt
    rw [h1.fderiv]
    simp
  have hL : ∫ x, u x * fderiv ℝ ψ x e = ∑ i ∈ I, ∫ x, u x * fderiv ℝ (g i) x e := by
    rw [← integral_finsetSum _ fun i _ => integrable_mul_fderiv hu (hg1 i) (hg2 i) e]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [hder, Finset.mul_sum]
  have hR : ∫ x, v x * ψ x = ∑ i ∈ I, ∫ x, v x * g i x := by
    rw [← integral_finsetSum _ fun i _ => integrable_mul_test hv (hg1 i) (hg2 i)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show v x * ψ x = ∑ i ∈ I, v x * g i x
    rw [← Finset.mul_sum, ← hsum x]
  rw [hL, hR, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => h i (g i) (hg1 i) (hg2 i) (hg3 i)


/-! ### Uniqueness of the weak derivative on an open set -/

theorem ae_eq_of_weak_eq {U : Set (Euc d)} (hU : IsOpen U) {a b : Euc d → ℝ}
    (ha : LocallyIntegrable a volume) (hb : LocallyIntegrable b volume)
    (h : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, a x * ψ x = ∫ x, b x * ψ x) :
    ∀ᵐ x, x ∈ U → a x = b x := by
  have h0 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) (f := fun x => a x - b x)
    ((ha.sub hb).locallyIntegrableOn U) (fun g hg hc hs => by
      have e1 := integrable_mul_test ha hg hc
      have e2 := integrable_mul_test hb hg hc
      have : ∫ x, g x • (a x - b x) = (∫ x, a x * g x) - ∫ x, b x * g x := by
        rw [← integral_sub e1 e2]
        exact integral_congr_ae (Eventually.of_forall fun x => by simp only [smul_eq_mul]; ring)
      rw [this, h g hg hc hs, sub_self])
  filter_upwards [h0] with x hx hxU
  exact sub_eq_zero.1 (hx hxU)

/-- Two functions that satisfy the weak-derivative identity against all test functions supported in
`closedBall c 1`, resp. `closedBall c' 1`, agree a.e. on `ball c 1 ∩ ball c' 1`. -/
theorem ae_eq_of_local {u : Euc d → ℝ} (e : Euc d) {c c' : Euc d} {V V' : Euc d → ℝ}
    (hV : LocallyIntegrable V volume) (hV' : LocallyIntegrable V' volume)
    (h : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ closedBall c 1 →
      ∫ x, u x * fderiv ℝ ψ x e = - ∫ x, V x * ψ x)
    (h' : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ closedBall c' 1 →
      ∫ x, u x * fderiv ℝ ψ x e = - ∫ x, V' x * ψ x) :
    ∀ᵐ x, x ∈ ball c 1 ∩ ball c' 1 → V x = V' x := by
  refine ae_eq_of_weak_eq (isOpen_ball.inter isOpen_ball) hV hV' fun ψ hψ hc hs => ?_
  have h1 := h ψ hψ hc (hs.trans (Set.inter_subset_left.trans ball_subset_closedBall))
  have h2 := h' ψ hψ hc (hs.trans (Set.inter_subset_right.trans ball_subset_closedBall))
  linarith

end HRS.MS.UniqM2
