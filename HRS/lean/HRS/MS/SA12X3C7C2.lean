import HRS.MS.SA12X3C7C1

/-!
# S.A.12 C7 (SA12X3), part C2 (7C): derivatives of the far box term

Let `H` be continuous and `N` open with `H = 0` on `B(x,h)` for `x ∈ N`, `N` within `B(c, R''-h/2)`.  There is a global smooth
`Ŝ` equal on `N` to `x ↦ ∫_{box(c)} ∂_iγ(x-y) H(y) dy`, with `∂^idx Ŝ(x) = ∫_{box(c)} ∂^{snoc idx i}γ(x-y) H(y) dy`
on `N` (the kernel is cut off by `C1`; the derivative then falls on the cut kernel by B1).
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MS.UniqT3 HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3_box_measurable (L : ℝ) (c : Euc d) : MeasurableSet {y : Euc d | y - c ∈ centeredBox d L} := by
  have : {y : Euc d | y - c ∈ centeredBox d L} = ⋂ i, {y : Euc d | -(L / 2) ≤ (y - c) i ∧ (y - c) i < L / 2} := by
    ext y; simp [centeredBox]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  have hc : Continuous (fun y : Euc d => (y - c) i) := (EuclideanSpace.proj i).continuous.comp (continuous_id.sub continuous_const)
  exact (measurableSet_le measurable_const hc.measurable).inter (measurableSet_lt hc.measurable measurable_const)

theorem sa12x3_far_deriv {s L : ℝ} {γ : Euc d → ℝ}
    (hγ : HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ) {h R'' : ℝ} (hh : 0 < h) (hR : 0 < R'')
    (hRL : R'' < L / 2) {c : Euc d} {N : Set (Euc d)} (hN : IsOpen N)
    (hNc : ∀ x ∈ N, ‖x - c‖ + h / 2 ≤ R'') {H : Euc d → ℝ} (hH : Continuous H)
    (hH0 : ∀ x ∈ N, ∀ y ∈ ball x h, H y = 0) (i : Fin d) :
    ∃ Sh : Euc d → ℝ, ContDiff ℝ ∞ Sh ∧
      (∀ x ∈ N, Sh x = ∫ y in {y | y - c ∈ centeredBox d L},
          fderiv ℝ γ (x - y) (EuclideanSpace.single i (1 : ℝ)) * H y) ∧
      ∀ (n : ℕ) (idx : Fin n → Fin d), ∀ x ∈ N, partialDeriv idx Sh x =
        ∫ y in {y | y - c ∈ centeredBox d L}, partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) γ (x - y) * H y := by
  set a : ℝ := L / 2 + R'' with ha
  have haL : a < L := by rw [ha]; linarith
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < a := by rw [ha]; linarith
  obtain ⟨ρ, hρ, hρc, hρ1, hρts⟩ := sa12x3_box_cutoff (d := d) (L := L) hh haL ha0
  have hgh : ContDiff ℝ ∞ (fun u => ρ u * γ u) := sa12x3_cutoff_smooth hh hγ hρ hρts
  have hghc : HasCompactSupport (fun u => ρ u * γ u) := hρc.mul_right
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  set Kt : Euc d → ℝ := fun u => fderiv ℝ (fun u => ρ u * γ u) u e with hKt
  have hKtc : ContDiff ℝ ∞ Kt :=
    ((hgh.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hKts : HasCompactSupport Kt := hghc.fderiv_apply (𝕜 := ℝ) e
  set A : Set (Euc d) := {y | y - c ∈ centeredBox d L} with hA
  have hAm : MeasurableSet A := sa12x3_box_measurable L c
  set H1 : Euc d → ℝ := A.indicator H with hH1
  have hH1i : LocallyIntegrable H1 (volume : Measure (Euc d)) := hH.locallyIntegrable.indicator hAm
  set Sh : Euc d → ℝ := fun x => ∫ y, Kt (x - y) * H1 y with hSh
  have hconv : Sh = HRS.Whole.convFun H1 Kt := by
    funext x'
    have h' := integral_sub_left_eq_self (μ := (volume : Measure (Euc d)))
      (fun t => Kt (x' - t) * H1 t) x'
    simp only [sub_sub_cancel] at h'
    simp only [hSh]
    unfold HRS.Whole.convFun
    rw [← h']
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  -- smoothness
  have hsm : ContDiff ℝ ∞ Sh := by
    have hfun : HRS.Whole.convFun H1 Kt = H1 ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] Kt := by
      funext x'
      have h' := integral_sub_left_eq_self (μ := (volume : Measure (Euc d))) (fun t => H1 t * Kt (x' - t)) x'
      simp only [sub_sub_cancel] at h'
      simpa [convolution_def, HRS.Whole.convFun] using h'
    rw [hconv, hfun]
    exact hKts.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hH1i hKtc
  -- the region where the cut kernel agrees with the kernel
  set O : Set (Euc d) := {u | h / 2 < ‖u‖ ∧ ∀ i, |u i| < a} with hO
  have hOopen : IsOpen O := by
    refine IsOpen.inter (isOpen_lt continuous_const continuous_norm) ?_
    have : {u : Euc d | ∀ i, |u i| < a} = ⋂ i, {u : Euc d | |u i| < a} := by ext u; simp
    show IsOpen {u : Euc d | ∀ i, |u i| < a}
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (continuous_abs.comp (EuclideanSpace.proj i).continuous) continuous_const
  have hρO : ∀ u ∈ O, ρ u = 1 := fun u hu => hρ1 u hu.1.le fun i => (hu.2 i).le
  have hghO : EqOn (fun u => ρ u * γ u) γ O := fun u hu => by simp [hρO u hu]
  -- relevant points lie in O
  have hrel : ∀ x ∈ N, ∀ y, y ∈ A → H y ≠ 0 → x - y ∈ O := by
    intro x hx y hyA hHy
    have hyb : y ∉ ball x h := fun hy => hHy (hH0 x hx y hy)
    refine ⟨?_, fun k => ?_⟩
    · have : h ≤ dist y x := by simpa [mem_ball] using hyb
      rw [dist_eq_norm] at this
      rw [← norm_neg, neg_sub] at this
      linarith
    · have h1 : |(x - c) k| ≤ ‖x - c‖ := by
        have := PiLp.norm_apply_le (x - c) k
        simpa using this
      have h2 := hNc x hx
      have h3 : -(L / 2) ≤ (y - c) k ∧ (y - c) k < L / 2 := hyA k
      have e1 : (x - y) k = (x - c) k - (y - c) k := by simp
      rw [e1]
      have := abs_le.1 h1
      rw [abs_lt]
      constructor <;> nlinarith [h3.1, h3.2, this.1, this.2]
  -- values on N
  have hval : ∀ x ∈ N, Sh x = ∫ y in A, fderiv ℝ γ (x - y) e * H y := by
    intro x hx
    rw [← integral_indicator hAm]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hSh, hH1]
    by_cases hyA : y ∈ A
    · by_cases hHy : H y = 0
      · simp [hHy, Set.indicator_of_mem hyA]
      · have hxy := hrel x hx y hyA hHy
        have : fderiv ℝ (fun u => ρ u * γ u) (x - y) = fderiv ℝ γ (x - y) :=
          (Filter.eventuallyEq_of_mem (hOopen.mem_nhds hxy) hghO).fderiv_eq
        simp [hKt, this, Set.indicator_of_mem hyA]
    · simp [Set.indicator_of_notMem hyA]
  refine ⟨Sh, hsm, hval, fun n idx x hx => ?_⟩
  -- derivatives on N
  have hpdconv : partialDeriv idx Sh x = HRS.Whole.convFun H1 (partialDeriv idx Kt) x := by
    rw [hconv]
    exact sa12x3_pd_conv_gen hH1i n Kt (hKtc.of_le (sa12x2_le_top n)) hKts idx x
  rw [hpdconv]
  unfold HRS.Whole.convFun
  have hsub := integral_sub_left_eq_self (μ := (volume : Measure (Euc d)))
    (fun t => H1 (x - t) * partialDeriv idx Kt t) x
  simp only [sub_sub_cancel] at hsub
  rw [← hsub]
  rw [← integral_indicator hAm]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [hH1]
  by_cases hyA : y ∈ A
  · by_cases hHy : H y = 0
    · simp [hHy, Set.indicator_of_mem hyA]
    · have hxy := hrel x hx y hyA hHy
      have e1 : partialDeriv idx Kt (x - y) = partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) γ (x - y) := by
        have h1 := (sa12x2_pd_right (fun u => ρ u * γ u) (hgh.of_le (sa12x2_le_top (n + 1))) idx i (x - y)).symm
        have h2 := sa12x3_pd_congr_open hOopen hghO (Fin.snoc idx i : Fin (n + 1) → Fin d) hxy
        rw [h2] at h1
        exact h1
      simp [Set.indicator_of_mem hyA, e1, mul_comm]
  · simp [Set.indicator_of_notMem hyA]

end HRS.MH.AdjointRd.Phase2SA12Near
