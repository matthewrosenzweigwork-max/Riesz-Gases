import HRS.MS.UniqE3

/-!
# E3 of `UniqPlan.md`, part 2: the diffusion term (D)

* `e3_diff_exact`: `ν ∫ u Δ(η_ε * P) = ν ∫ (η_ε * u) ΔP` exactly (no commutator) for `P ∈ C²_c`, `LocMass u`.
* `e3_diffusion_identity`: with `P = ς z_ε`, `z_ε = η_ε * u`:
  `ν ∫ u Δφ = -ν (∫ ς |∇z_ε|² + ∫ z_ε ∇ς·∇z_ε)`.
* `e3_diffusion_bound`: if `|∇ς|² ≤ Γ ς`, `ς ≥ 0`, `tsupport ς ⊆ S` and `ν ≥ 0`:
  `2 · ν ∫ u Δφ ≤ -ν ∫ ς |∇z_ε|² + ν Γ ∫_S z_ε²`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3

variable {d : ℕ}

theorem e3_integral_mul_sum {f : Euc d → ℝ} {g : Fin d → Euc d → ℝ}
    (h : ∀ i, Integrable (fun x => f x * g i x) volume) :
    ∫ x, f x * ∑ i, g i x = ∑ i, ∫ x, f x * g i x := by
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => h i)

theorem e3_D1_mul {f g : Euc d → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin d)
    (x : Euc d) : D1 i (fun y => f y * g y) x = f x * D1 i g x + g x * D1 i f x := by
  simp only [D1]
  rw [fderiv_fun_mul (hf x) (hg x)]
  simp

theorem e3_fderiv_eq_zero_of_notMem {f : Euc d → ℝ} {x : Euc d} (hx : x ∉ tsupport f) :
    fderiv ℝ f x = 0 := by
  have hev : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
  rw [hev.fderiv_eq]; simp

theorem e3_hasCompactSupport_of_zero {f : Euc d → ℝ} {K : Set (Euc d)} (hK : IsCompact K)
    (h : ∀ x, x ∉ K → f x = 0) : HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact hK (fun x hx => by
    by_contra hxK; exact hx (h x hxK))

/-- `ν ∫ u Δ(η_ε * P) = ν ∫ (η_ε * u) ΔP`: no commutator. -/
theorem e3_diff_exact {D : WholeDyn d} {ε : ℝ} (hε : 0 < ε) {B : ℝ} {u : Euc d → ℝ}
    (hu : LocMass B u) {P : Euc d → ℝ} (hP : ContDiff ℝ 2 P) (hPc : HasCompactSupport P) :
    fpDiff D u (moll d ε P) = D.invβ * ∫ x, moll d ε u x * Laplacian.laplacian P x := by
  unfold fpDiff
  congr 1
  have hP1 : ContDiff ℝ 1 P := hP.of_le (by norm_num)
  have hD : ∀ i, ContDiff ℝ 1 (D1 i P) := fun i => D1_contDiff hP i
  have hDc : ∀ i, HasCompactSupport (D1 i P) := fun i => D1_supp hPc i
  have hDD : ∀ i, Continuous (D1 i (D1 i P)) := fun i => e3_continuous_D1 (hD i) i
  have hDDs : ∀ i, HasCompactSupport (D1 i (D1 i P)) := fun i => D1_supp (hDc i) i
  have hsm : ContDiff ℝ 2 (moll d ε P) :=
    (moll_contDiff hε hP1.continuous.locallyIntegrable).of_le (by norm_num)
  have hlapm : ∀ x, Laplacian.laplacian (moll d ε P) x = ∑ i, moll d ε (D1 i (D1 i P)) x := by
    intro x
    rw [lap_eq hsm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e3_D1_moll hε hP1 hPc i, e3_D1_moll hε (hD i) (hDc i) i]
  have hlapP : ∀ x, Laplacian.laplacian P x = ∑ i, D1 i (D1 i P) x := lap_eq hP
  have hz : Continuous (moll d ε u) := e3_moll_continuous hε hu.locallyIntegrable
  simp_rw [hlapm, hlapP]
  rw [e3_integral_mul_sum (fun i => e3_integrable_mul hu.locallyIntegrable
      (e3_moll_continuous hε (hDD i).locallyIntegrable) (e3_moll_hasCompactSupport hε (hDDs i))),
    e3_integral_mul_sum (fun i => (hz.mul (hDD i)).integrable_of_hasCompactSupport
      ((hDDs i).mul_left))]
  exact Finset.sum_congr rfl fun i _ =>
    e3_integral_mul_moll hε hu (hDD i) (hDDs i)

/-- Integration by parts for the Laplacian. -/
theorem e3_lap_ibp {z P : Euc d → ℝ} (hz : ContDiff ℝ 1 z) (hP : ContDiff ℝ 2 P)
    (hPc : HasCompactSupport P) :
    ∫ x, z x * Laplacian.laplacian P x = - ∑ i, ∫ x, D1 i z x * D1 i P x := by
  have hlapP : ∀ x, Laplacian.laplacian P x = ∑ i, D1 i (D1 i P) x := lap_eq hP
  simp_rw [hlapP]
  rw [e3_integral_mul_sum (fun i => (hz.continuous.mul (e3_continuous_D1 (D1_contDiff hP i) i)
    ).integrable_of_hasCompactSupport ((D1_supp (D1_supp hPc i) i).mul_left)),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => e3_ibp hz (D1_contDiff hP i) (Or.inr (D1_supp hPc i)) i

/-- **(D), exact form.** -/
theorem e3_diffusion_identity {D : WholeDyn d} {ε : ℝ} (hε : 0 < ε) {B : ℝ} {u : Euc d → ℝ}
    (hu : LocMass B u) {ς : Euc d → ℝ} (hς : ContDiff ℝ 2 ς) (hςc : HasCompactSupport ς) :
    fpDiff D u (moll d ε (fun x => ς x * moll d ε u x)) =
      -(D.invβ * ((∫ x, ς x * ‖fderiv ℝ (moll d ε u) x‖ ^ 2) +
        ∫ x, moll d ε u x * ∑ i, D1 i ς x * D1 i (moll d ε u) x)) := by
  have hzs : ContDiff ℝ ∞ (moll d ε u) := moll_contDiff hε hu.locallyIntegrable
  have hz2 : ContDiff ℝ 2 (moll d ε u) := hzs.of_le (by norm_num)
  have hz1 : ContDiff ℝ 1 (moll d ε u) := hzs.of_le (by norm_num)
  have hP : ContDiff ℝ 2 (fun x => ς x * moll d ε u x) := hς.mul hz2
  have hP1 : ContDiff ℝ 1 (fun x => ς x * moll d ε u x) := hP.of_le (by norm_num)
  have hPc : HasCompactSupport (fun x => ς x * moll d ε u x) := hςc.mul_right
  have hς1 : ContDiff ℝ 1 ς := hς.of_le (by norm_num)
  rw [e3_diff_exact hε hu hP hPc, e3_lap_ibp hz1 hP hPc]
  have hpt : ∀ x, ∑ i, D1 i (moll d ε u) x * D1 i (fun x => ς x * moll d ε u x) x =
      ς x * ‖fderiv ℝ (moll d ε u) x‖ ^ 2 +
        moll d ε u x * ∑ i, D1 i ς x * D1 i (moll d ε u) x := by
    intro x
    rw [e3_norm_sq_fderiv, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e3_D1_mul (hς.differentiable (by norm_num)) (hz2.differentiable (by norm_num))]
    simp only [D1]
    ring
  have hint1 : Integrable (fun x => ς x * ‖fderiv ℝ (moll d ε u) x‖ ^ 2) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hςc.mul_right
    exact hς.continuous.mul ((hz1.continuous_fderiv (by simp)).norm.pow 2)
  have hint2 : Integrable (fun x => moll d ε u x * ∑ i, D1 i ς x * D1 i (moll d ε u) x) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hz1.continuous.mul (continuous_finsetSum _ fun i _ =>
        (e3_continuous_D1 hς1 i).mul (e3_continuous_D1 hz1 i))
    · refine e3_hasCompactSupport_of_zero hςc.isCompact (fun x hx => ?_)
      have : fderiv ℝ ς x = 0 := e3_fderiv_eq_zero_of_notMem hx
      simp [D1, this]
  have hsum : ∑ i, ∫ x, D1 i (moll d ε u) x * D1 i (fun x => ς x * moll d ε u x) x =
      (∫ x, ς x * ‖fderiv ℝ (moll d ε u) x‖ ^ 2) +
        ∫ x, moll d ε u x * ∑ i, D1 i ς x * D1 i (moll d ε u) x := by
    rw [← integral_add hint1 hint2, ← integral_finsetSum]
    · exact integral_congr_ae (Eventually.of_forall fun x => hpt x)
    · intro i _
      exact ((e3_continuous_D1 hz1 i).mul (e3_continuous_D1 hP1 i)).integrable_of_hasCompactSupport
        ((D1_supp hPc i).mul_left)
  rw [hsum]
  ring

/-- Pointwise Young inequality used for the cross term. -/
theorem e3_young {ς a2 z Γ S1 : ℝ} (hς : 0 ≤ ς) (hΓ : 0 ≤ Γ) (ha2 : 0 ≤ a2)
    (h : S1 ^ 2 ≤ Γ * ς * a2) : -2 * (z * S1) ≤ ς * a2 + Γ * z ^ 2 := by
  have hR : 0 ≤ ς * a2 + Γ * z ^ 2 := by positivity
  have h1 : (-2 * (z * S1)) ^ 2 ≤ (ς * a2 + Γ * z ^ 2) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg z), sq_nonneg (ς * a2 - Γ * z ^ 2)]
  exact (abs_le_of_sq_le_sq' h1 hR).2

/-- **(D), inequality form.** -/
theorem e3_diffusion_bound {D : WholeDyn d} (hν : 0 ≤ D.invβ) {ε : ℝ} (hε : 0 < ε) {B : ℝ}
    {u : Euc d → ℝ} (hu : LocMass B u) {ς : Euc d → ℝ} (hς : ContDiff ℝ 2 ς)
    (hςc : HasCompactSupport ς) (hς0 : ∀ x, 0 ≤ ς x) {Γ : ℝ} (hΓ0 : 0 ≤ Γ)
    (hΓ : ∀ x, ‖fderiv ℝ ς x‖ ^ 2 ≤ Γ * ς x) {S : Set (Euc d)} (hS : IsCompact S)
    (hSς : tsupport ς ⊆ S) :
    2 * fpDiff D u (moll d ε (fun x => ς x * moll d ε u x)) ≤
      -(D.invβ * ∫ x, ς x * ‖fderiv ℝ (moll d ε u) x‖ ^ 2) +
        D.invβ * Γ * ∫ x in S, moll d ε u x ^ 2 := by
  have hzs : ContDiff ℝ ∞ (moll d ε u) := moll_contDiff hε hu.locallyIntegrable
  have hz1 : ContDiff ℝ 1 (moll d ε u) := hzs.of_le (by norm_num)
  have hς1 : ContDiff ℝ 1 ς := hς.of_le (by norm_num)
  rw [e3_diffusion_identity hε hu hς hςc]
  set z : Euc d → ℝ := moll d ε u with hzdef
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hint1 : Integrable (fun x => ς x * ‖fderiv ℝ z x‖ ^ 2) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hςc.mul_right
    exact hς.continuous.mul ((hz1.continuous_fderiv (by simp)).norm.pow 2)
  have hint2 : Integrable (fun x => z x * ∑ i, D1 i ς x * D1 i z x) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hz1.continuous.mul (continuous_finsetSum _ fun i _ =>
        (e3_continuous_D1 hς1 i).mul (e3_continuous_D1 hz1 i))
    · refine e3_hasCompactSupport_of_zero hςc.isCompact (fun x hx => ?_)
      have : fderiv ℝ ς x = 0 := e3_fderiv_eq_zero_of_notMem hx
      simp [D1, this]
  have hint3 : Integrable (S.indicator fun x => Γ * z x ^ 2) volume := by
    refine (integrable_indicator_iff hSm).2 ?_
    exact (hz1.continuous.pow 2 |>.const_mul Γ).continuousOn.integrableOn_compact hS
  -- pointwise
  have hpt : ∀ x, -2 * (z x * ∑ i, D1 i ς x * D1 i z x) ≤
      ς x * ‖fderiv ℝ z x‖ ^ 2 + S.indicator (fun x => Γ * z x ^ 2) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      refine e3_young (hς0 x) hΓ0 (sq_nonneg _) ?_
      have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => D1 i ς x) (fun i => D1 i z x)
      have h2 : ∑ i, (D1 i ς x) ^ 2 = ‖fderiv ℝ ς x‖ ^ 2 := (e3_norm_sq_fderiv _).symm
      have h3 : ∑ i, (D1 i z x) ^ 2 = ‖fderiv ℝ z x‖ ^ 2 := (e3_norm_sq_fderiv _).symm
      rw [h2, h3] at h1
      exact h1.trans (by
        have := mul_le_mul_of_nonneg_right (hΓ x) (sq_nonneg ‖fderiv ℝ z x‖)
        linarith)
    · rw [Set.indicator_of_notMem hx]
      have hx' : x ∉ tsupport ς := fun h => hx (hSς h)
      have h0 : fderiv ℝ ς x = 0 := e3_fderiv_eq_zero_of_notMem hx'
      have h00 : ς x = 0 := image_eq_zero_of_notMem_tsupport hx'
      simp [D1, h0, h00]
  have hmono : ∫ x, -2 * (z x * ∑ i, D1 i ς x * D1 i z x) ≤
      ∫ x, (ς x * ‖fderiv ℝ z x‖ ^ 2 + S.indicator (fun x => Γ * z x ^ 2) x) :=
    integral_mono (hint2.const_mul (-2)) (hint1.add hint3) hpt
  rw [integral_const_mul, integral_add hint1 hint3, integral_indicator hSm,
    integral_const_mul] at hmono
  have key := mul_le_mul_of_nonneg_left hmono hν
  nlinarith [key]

end HRS.MS.UniqE3
