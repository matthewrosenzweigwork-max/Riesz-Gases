import HRS.MS.SA16Y8Ul1
import HRS.MS.SA16SSt1

/-!
# S.A.16 (SA16Y8) Rp4: the `C²` representative of an element of `W^{m,p}`, `m > 2 + d/p` (classical clause, K3)

`sa16y8_rep`: there are `C, α > 0` such that every `z ∈ W^{m,p}` has a `C²` function `u` with `wrep z = u` a.e.,
`‖u‖_∞, ‖Du‖_∞, ‖D²u‖_∞ ≤ C‖z‖` and `‖D²u(x+h) - D²u(x)‖ ≤ C‖h‖^α ‖z‖` (`‖h‖ ≤ 1`).  Proof: limit of `C_c^∞` approximations
(uniform Cauchy for `φ, Dφ, D²φ` by `sa16y8_bounds`, `hasFDerivAt_of_tendstoUniformly`), identification with `wrep z` by pairing with test functions.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16 HRS.Whole.AppendixA.Phase2SA16R
open Phase2SA16Transfer Phase2SA16Evolution

section Rp4
variable {d : ℕ}

lemma sa16y8_sub_fd (a b : ccSub d) (x : Euc d) :
    fderiv ℝ (a - b).1 x = fderiv ℝ a.1 x - fderiv ℝ b.1 x := by
  have : (a - b).1 = fun y => a.1 y - b.1 y := rfl
  rw [this]
  exact fderiv_sub ((a.2.1.differentiable (by simp)) x) ((b.2.1.differentiable (by simp)) x)

lemma sa16y8_sub_D2 (a b : ccSub d) (x : Euc d) :
    sa16y8_D2 (a - b).1 x = sa16y8_D2 a.1 x - sa16y8_D2 b.1 x := by
  have h1 : fderiv ℝ (a - b).1 = fun y => fderiv ℝ a.1 y - fderiv ℝ b.1 y := funext (sa16y8_sub_fd a b)
  have hda : Differentiable ℝ (fderiv ℝ a.1) :=
    ((a.2.1.fderiv_right (m := ∞) (by simp)).differentiable (by simp))
  have hdb : Differentiable ℝ (fderiv ℝ b.1) :=
    ((b.2.1.fderiv_right (m := ∞) (by simp)).differentiable (by simp))
  unfold sa16y8_D2
  rw [h1]
  exact fderiv_sub (hda x) (hdb x)

/-- a limit bound for differences of nested continuous linear maps (evaluated pointwise) -/
lemma sa16y8_nested_limit_le
    (P Q : ℕ → Euc d →L[ℝ] (Euc d →L[ℝ] ℝ)) {P' Q' : Euc d →L[ℝ] (Euc d →L[ℝ] ℝ)}
    (hP : ∀ v w : Euc d, Tendsto (fun n => P n v w) atTop (𝓝 (P' v w)))
    (hQ : ∀ v w : Euc d, Tendsto (fun n => Q n v w) atTop (𝓝 (Q' v w)))
    {bn : ℕ → ℝ} {b : ℝ} (hb : Tendsto bn atTop (𝓝 b)) (h : ∀ n, ‖P n - Q n‖ ≤ bn n) :
    ‖P' - Q'‖ ≤ b := by
  have hb0 : 0 ≤ b := ge_of_tendsto' hb fun n => (ContinuousLinearMap.opNorm_nonneg _).trans (h n)
  refine ContinuousLinearMap.opNorm_le_bound _ hb0 fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  have hlim : Tendsto (fun n => |(P n - Q n) v w|) atTop (𝓝 |(P' - Q') v w|) := by
    simp only [ContinuousLinearMap.sub_apply]
    exact ((hP v w).sub (hQ v w)).abs
  have hlim2 : Tendsto (fun n => bn n * ‖v‖ * ‖w‖) atTop (𝓝 (b * ‖v‖ * ‖w‖)) :=
    (hb.mul_const _).mul_const _
  have := le_of_tendsto_of_tendsto hlim hlim2 (Eventually.of_forall fun n => by
    calc |(P n - Q n) v w| ≤ ‖(P n - Q n) v w‖ := le_of_eq (Real.norm_eq_abs _).symm
      _ ≤ ‖(P n - Q n) v‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖P n - Q n‖ * ‖v‖) * ‖w‖ := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ bn n * ‖v‖ * ‖w‖ := by gcongr; exact h n)
  simpa [ContinuousLinearMap.sub_apply, Real.norm_eq_abs] using this

lemma sa16y8_nested_limit_le0
    (P : ℕ → Euc d →L[ℝ] (Euc d →L[ℝ] ℝ)) {P' : Euc d →L[ℝ] (Euc d →L[ℝ] ℝ)}
    (hP : ∀ v w : Euc d, Tendsto (fun n => P n v w) atTop (𝓝 (P' v w)))
    {bn : ℕ → ℝ} {b : ℝ} (hb : Tendsto bn atTop (𝓝 b)) (h : ∀ n, ‖P n‖ ≤ bn n) :
    ‖P'‖ ≤ b := by
  have hb0 : 0 ≤ b := ge_of_tendsto' hb fun n => (ContinuousLinearMap.opNorm_nonneg _).trans (h n)
  refine ContinuousLinearMap.opNorm_le_bound _ hb0 fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  have hlim : Tendsto (fun n => |P n v w|) atTop (𝓝 |P' v w|) := (hP v w).abs
  have hlim2 : Tendsto (fun n => bn n * ‖v‖ * ‖w‖) atTop (𝓝 (b * ‖v‖ * ‖w‖)) :=
    (hb.mul_const _).mul_const _
  have := le_of_tendsto_of_tendsto hlim hlim2 (Eventually.of_forall fun n => by
    calc |P n v w| ≤ ‖P n v w‖ := le_of_eq (Real.norm_eq_abs _).symm
      _ ≤ ‖P n v‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖P n‖ * ‖v‖) * ‖w‖ := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ bn n * ‖v‖ * ‖w‖ := by gcongr; exact h n)
  simpa [Real.norm_eq_abs] using this

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 6400000 in
theorem sa16y8_rep_seq (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] {C α : ℝ} (hC : 0 < C) (hα : 0 < α)
    (hB : ∀ φ : ccSub d,
      (∀ x, ‖φ.1 x‖ ≤ C * ‖sa16r_Jcc d m p φ‖) ∧ (∀ x, ‖fderiv ℝ φ.1 x‖ ≤ C * ‖sa16r_Jcc d m p φ‖) ∧
      (∀ x, ‖sa16y8_D2 φ.1 x‖ ≤ C * ‖sa16r_Jcc d m p φ‖) ∧
      ∀ x h : Euc d, ‖h‖ ≤ 1 → ‖sa16y8_D2 φ.1 (x + h) - sa16y8_D2 φ.1 x‖ ≤ C * ‖h‖ ^ α * ‖sa16r_Jcc d m p φ‖)
    (z : WmpSpace d m p) (φ : ℕ → ccSub d) (hJn : Tendsto (fun n => sa16r_Jcc d m p (φ n)) atTop (𝓝 z)) :
    ∃ u : Euc d → ℝ, ContDiff ℝ 2 u ∧
      wrep d m p z =ᵐ[volume] u ∧ (∀ x, ‖u x‖ ≤ C * ‖z‖) ∧ (∀ x, ‖fderiv ℝ u x‖ ≤ C * ‖z‖) ∧
      (∀ x, ‖sa16y8_D2 u x‖ ≤ C * ‖z‖) ∧
      (∀ x h : Euc d, ‖h‖ ≤ 1 → ‖sa16y8_D2 u (x + h) - sa16y8_D2 u x‖ ≤ C * ‖h‖ ^ α * ‖z‖) ∧
      (∀ x, Tendsto (fun n => (φ n).1 x) atTop (𝓝 (u x))) ∧
      (∀ x, Tendsto (fun n => fderiv ℝ (φ n).1 x) atTop (𝓝 (fderiv ℝ u x))) ∧
      (∀ x v w : Euc d, Tendsto (fun n => sa16y8_D2 (φ n).1 x v w) atTop (𝓝 (sa16y8_D2 u x v w))) := by
  have hcau := hJn.cauchySeq
  have hCJ : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n k : ℕ, N ≤ n → N ≤ k →
      ‖sa16r_Jcc d m p (φ n) - sa16r_Jcc d m p (φ k)‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hcau ε hε
    exact ⟨N, fun n k hn hk => by rw [← dist_eq_norm]; exact (hN n hn k hk).le⟩
  have hJd : ∀ n k, sa16r_Jcc d m p (φ n - φ k) = sa16r_Jcc d m p (φ n) - sa16r_Jcc d m p (φ k) :=
    fun n k => map_sub _ _ _
  -- uniform Cauchy for the three families
  have hU0 := sa16y8_unif_of_cauchy (G := ℝ) (fun n x => (φ n).1 x) (fun ε hε => by
    obtain ⟨N, hN⟩ := hCJ (ε / C) (by positivity)
    refine ⟨N, fun n k hn hk x => ?_⟩
    have := (hB (φ n - φ k)).1 x
    rw [hJd] at this
    have e : (φ n - φ k).1 x = (φ n).1 x - (φ k).1 x := rfl
    rw [e] at this
    calc ‖(φ n).1 x - (φ k).1 x‖ ≤ C * ‖sa16r_Jcc d m p (φ n) - sa16r_Jcc d m p (φ k)‖ := this
      _ ≤ C * (ε / C) := mul_le_mul_of_nonneg_left (hN n k hn hk) hC.le
      _ = ε := by field_simp)
  have hU1 := sa16y8_unif_of_cauchy (G := Euc d →L[ℝ] ℝ) (fun n x => fderiv ℝ (φ n).1 x) (fun ε hε => by
    obtain ⟨N, hN⟩ := hCJ (ε / C) (by positivity)
    refine ⟨N, fun n k hn hk x => ?_⟩
    have := (hB (φ n - φ k)).2.1 x
    rw [hJd, sa16y8_sub_fd] at this
    calc ‖fderiv ℝ (φ n).1 x - fderiv ℝ (φ k).1 x‖ ≤ C * ‖sa16r_Jcc d m p (φ n) - sa16r_Jcc d m p (φ k)‖ := this
      _ ≤ C * (ε / C) := mul_le_mul_of_nonneg_left (hN n k hn hk) hC.le
      _ = ε := by field_simp)
  have hU2 := sa16y8_unif_of_cauchy (G := Euc d →L[ℝ] (Euc d →L[ℝ] ℝ)) (fun n x => sa16y8_D2 (φ n).1 x)
    (fun ε hε => by
    obtain ⟨N, hN⟩ := hCJ (ε / C) (by positivity)
    refine ⟨N, fun n k hn hk x => ?_⟩
    have := (hB (φ n - φ k)).2.2.1 x
    rw [hJd, sa16y8_sub_D2] at this
    calc ‖sa16y8_D2 (φ n).1 x - sa16y8_D2 (φ k).1 x‖ ≤ C * ‖sa16r_Jcc d m p (φ n) - sa16r_Jcc d m p (φ k)‖ := this
      _ ≤ C * (ε / C) := mul_le_mul_of_nonneg_left (hN n k hn hk) hC.le
      _ = ε := by field_simp)
  obtain ⟨g0, hT0, hp0⟩ := hU0
  obtain ⟨g1, hT1, hp1⟩ := hU1
  obtain ⟨g2, hT2, hp2⟩ := hU2
  have hdiff : ∀ n, Differentiable ℝ (φ n).1 := fun n => (φ n).2.1.differentiable (by simp)
  have hdiff1 : ∀ n, Differentiable ℝ (fderiv ℝ (φ n).1) := fun n =>
    ((φ n).2.1.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hd0 : ∀ x, HasFDerivAt g0 (g1 x) x := fun x =>
    hasFDerivAt_of_tendstoUniformly (f := fun n => (φ n).1) (f' := fun n => fderiv ℝ (φ n).1) hT1
      (fun n y => (hdiff n y).hasFDerivAt) hp0 x
  have hd1 : ∀ x, HasFDerivAt g1 (g2 x) x := fun x =>
    hasFDerivAt_of_tendstoUniformly (f := fun n => fderiv ℝ (φ n).1) (f' := fun n => sa16y8_D2 (φ n).1) hT2
      (fun n y => (hdiff1 n y).hasFDerivAt) hp1 x
  have hfd0 : fderiv ℝ g0 = g1 := funext fun x => (hd0 x).fderiv
  have hfd1 : fderiv ℝ g1 = g2 := funext fun x => (hd1 x).fderiv
  have hg2c : Continuous g2 := hT2.continuous (Eventually.of_forall fun n =>
    (sa16y8_D2_smooth (φ n).2.1).continuous).frequently
  have hcd1 : ContDiff ℝ 1 g1 := by
    rw [contDiff_one_iff_fderiv]
    exact ⟨fun x => (hd1 x).differentiableAt, by rw [hfd1]; exact hg2c⟩
  have hcd : ContDiff ℝ 2 g0 := by
    have : ContDiff ℝ (1 + 1) g0 := by
      rw [contDiff_succ_iff_fderiv]
      exact ⟨fun x => (hd0 x).differentiableAt, by simp, by rw [hfd0]; exact hcd1⟩
    simpa [one_add_one_eq_two] using this
  obtain ⟨Bj, hBj⟩ := hJn.norm.bddAbove_range
  have hBj' : ∀ n, ‖sa16r_Jcc d m p (φ n)‖ ≤ Bj := fun n => hBj ⟨n, rfl⟩
  have hlimJ : Tendsto (fun n => C * ‖sa16r_Jcc d m p (φ n)‖) atTop (𝓝 (C * ‖z‖)) := hJn.norm.const_mul C
  have hev : ∀ (y : Euc d) (v w : Euc d), Tendsto (fun n => sa16y8_D2 (φ n).1 y v w) atTop (𝓝 (g2 y v w)) := by
    intro y v w
    have hc : Continuous (fun A : Euc d →L[ℝ] (Euc d →L[ℝ] ℝ) => A v w) :=
      (ContinuousLinearMap.apply ℝ ℝ w).continuous.comp ((ContinuousLinearMap.apply ℝ (Euc d →L[ℝ] ℝ) v).continuous)
    exact (hc.tendsto (g2 y)).comp (hp2 y)
  have hD2g : sa16y8_D2 g0 = g2 := by
    unfold sa16y8_D2
    rw [hfd0, hfd1]
  refine ⟨g0, hcd, ?_, ?_, ?_, ?_, ?_, hp0, ?_, ?_⟩
  · -- identification with `wrep z`
    refine ae_eq_of_integral_contDiff_smul_eq (sa16sx_loc m z) hcd.continuous.locallyIntegrable
      (fun g hg hgs => ?_)
    have hgg : IsCcInfty g := ⟨hg, hgs⟩
    have hgc : Continuous g := hg.continuous
    have hl1 : Tendsto (fun n => ∫ x, (φ n).1 x * g x) atTop (𝓝 (∫ x, wrep d m p z x * g x)) := by
      have := ((sa16r_ell d m p hgg).continuous.tendsto z).comp hJn
      rw [← sa16r_ell_apply hgg m z]
      refine this.congr (fun n => ?_)
      show sa16r_ell d m p hgg (sa16r_Jcc d m p (φ n)) = _
      rw [sa16r_ell_apply, sa16r_Jcc_eq]
      refine integral_congr_ae ?_
      filter_upwards [sa16r_cc_elt_wrep (p := p) (φ n).2 m] with x hx
      rw [hx]
    have hl2 : Tendsto (fun n => ∫ x, (φ n).1 x * g x) atTop (𝓝 (∫ x, g0 x * g x)) := by
      refine tendsto_integral_of_dominated_convergence (fun x => C * Bj * ‖g x‖) (fun n => ?_) ?_ (fun n => ?_)
        (Eventually.of_forall fun x => (hp0 x).mul_const (g x))
      · exact ((φ n).2.1.continuous.mul hgc).aestronglyMeasurable
      · exact (hgc.integrable_of_hasCompactSupport hgs).norm.const_mul _
      · refine Eventually.of_forall fun x => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (((hB (φ n)).1 x).trans
          (mul_le_mul_of_nonneg_left (hBj' n) hC.le)) (norm_nonneg _)
    have := tendsto_nhds_unique hl1 hl2
    simp only [smul_eq_mul]
    rw [show (fun x => g x * wrep d m p z x) = fun x => wrep d m p z x * g x from funext fun x => mul_comm _ _,
      show (fun x => g x * g0 x) = fun x => g0 x * g x from funext fun x => mul_comm _ _]
    exact this
  · intro x
    exact le_of_tendsto_of_tendsto (hp0 x).norm hlimJ (Eventually.of_forall fun n => (hB (φ n)).1 x)
  · intro x
    rw [hfd0]
    exact le_of_tendsto_of_tendsto (hp1 x).norm hlimJ (Eventually.of_forall fun n => (hB (φ n)).2.1 x)
  · intro x
    rw [hD2g]
    exact sa16y8_nested_limit_le0 (d := d) (fun n => sa16y8_D2 (φ n).1 x) (hev x) hlimJ
      (fun n => (hB (φ n)).2.2.1 x)
  · intro x h hh
    rw [hD2g]
    have hlim2 : Tendsto (fun n => C * ‖h‖ ^ α * ‖sa16r_Jcc d m p (φ n)‖) atTop (𝓝 (C * ‖h‖ ^ α * ‖z‖)) :=
      hJn.norm.const_mul _
    exact sa16y8_nested_limit_le (d := d) (fun n => sa16y8_D2 (φ n).1 (x + h)) (fun n => sa16y8_D2 (φ n).1 x)
      (hev (x + h)) (hev x) hlim2 (fun n => (hB (φ n)).2.2.2 x h hh)
  · intro x
    rw [hfd0]
    exact hp1 x
  · intro x v w
    rw [hD2g]
    exact hev x v w


theorem sa16y8_rep (d m : ℕ) (hd : 1 ≤ d) (p : ℝ) [Fact (2 ≤ p)] (hmp : 2 + (d : ℝ) / p < m) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ z : WmpSpace d m p, ∃ u : Euc d → ℝ, ContDiff ℝ 2 u ∧
      wrep d m p z =ᵐ[volume] u ∧ (∀ x, ‖u x‖ ≤ C * ‖z‖) ∧ (∀ x, ‖fderiv ℝ u x‖ ≤ C * ‖z‖) ∧
      (∀ x, ‖sa16y8_D2 u x‖ ≤ C * ‖z‖) ∧
      ∀ x h : Euc d, ‖h‖ ≤ 1 → ‖sa16y8_D2 u (x + h) - sa16y8_D2 u x‖ ≤ C * ‖h‖ ^ α * ‖z‖ := by
  obtain ⟨C, α, hC, hα, hB⟩ := sa16y8_bounds d m hd p hmp
  refine ⟨C, α, hC, hα, fun z => ?_⟩
  obtain ⟨xs, hxr, hxt⟩ := mem_closure_iff_seq_limit.1 ((sa16r_Jcc_dense d m p) z)
  choose φ hφ using hxr
  have hJn : Tendsto (fun n => sa16r_Jcc d m p (φ n)) atTop (𝓝 z) := by
    have e : (fun n => sa16r_Jcc d m p (φ n)) = xs := funext hφ
    rw [e]; exact hxt
  obtain ⟨u, h1, h2, h3, h4, h5, h6, -⟩ := sa16y8_rep_seq d m p hC hα hB z φ hJn
  exact ⟨u, h1, h2, h3, h4, h5, h6⟩

end Rp4

end HRS.Whole.AppendixA.Phase2SA16Q
