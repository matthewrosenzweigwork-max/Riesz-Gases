import HRS.MS.SA12V2

/-!
# S.A.12 C17, Fubini for the periodic convolution against a compactly supported test

`∫_{ℝ^d} ψ(x) (γ ⊛_L g)(x) dx = ∫_{[0,L)^d} g(y) ∫_{ℝ^d} ψ(x) γ(x-y) dx dy`, and the identification of the inner
integral with `h_ψ(y) = ∫ γ(y-u) ψ(u) du` when `γ` is even.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

/-- `h_ψ(w) = ∫ γ(w-u) ψ(u) du`, the test function of the nonlocal term (`nonlocalTestPer`). -/
def sa12vH (γ ψ : Euc d → ℝ) (w : Euc d) : ℝ := ∫ u, γ (w - u) * ψ u

theorem sa12v_H_eq_conv (γ ψ : Euc d → ℝ) :
    sa12vH γ ψ = MeasureTheory.convolution ψ γ (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext w
  simp only [sa12vH, convolution_def, ContinuousLinearMap.mul_apply']
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm _ _)

theorem sa12v_H_smooth {γ ψ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) : ContDiff ℝ ∞ (sa12vH γ ψ) := by
  rw [sa12v_H_eq_conv]
  exact hψc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hψ hγ

theorem sa12v_H_periodic {L : ℝ} {γ : Euc d → ℝ}
    (hγp : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x) (ψ : Euc d → ℝ) :
    ∀ (x : Euc d) (k : Fin d → ℤ), sa12vH γ ψ (x + L • latticePt k) = sa12vH γ ψ x := by
  intro x k
  unfold sa12vH
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show γ (x + L • latticePt k - u) * ψ u = γ (x - u) * ψ u
  have : x + L • latticePt (d := d) k - u = (x - u) + L • latticePt k := by abel
  rw [this, hγp]

theorem sa12v_grad_coord (f : Euc d → ℝ) (y : Euc d) (j : Fin d) :
    gradient f y j = fderiv ℝ f y (EuclideanSpace.single j 1) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Euc d)
    (x := EuclideanSpace.single j 1) (y := fderiv ℝ f y)
  have h2 : inner ℝ (EuclideanSpace.single j (1 : ℝ)) (gradient f y) = gradient f y j := by
    rw [EuclideanSpace.inner_single_left]; simp
  rw [← h, ← h2, real_inner_comm]
  rfl

/-- Fubini: the transposed identity for the periodic convolution. -/
theorem sa12v_fubini (L : ℝ) {γ g ψ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume)
    (hg : Continuous g) (Bg : ℝ) (hgb : ∀ y, ‖g y‖ ≤ Bg) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (fun x => ψ x * perConv L γ g x) ∧
    ∫ x, ψ x * perConv L γ g x =
      ∫ y in periodBox d L, g y * ∫ x, ψ x * γ (x - y) := by
  set ν : Measure (Euc d) := volume.restrict (periodBox d L) with hν
  obtain ⟨Bψ, hBψ⟩ := hψc.exists_bound_of_continuous hψ
  have hBψ0 : 0 ≤ Bψ := (norm_nonneg _).trans (hBψ 0)
  have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hgb 0)
  have hK : IsCompact (tsupport ψ) := hψc
  obtain ⟨Rk, hRk⟩ := hK.isBounded.exists_norm_le
  set R : ℝ := Rk + Real.sqrt (d * L ^ 2) with hR
  have hΦ : Integrable (fun q : Euc d × Euc d => ψ q.1 * γ (q.1 - q.2) * g q.2)
      ((volume : Measure (Euc d)).prod ν) := by
    set B : Set (Euc d) := Metric.closedBall 0 R with hB
    have hγB : IntegrableOn γ B volume := hγ.integrableOn_isCompact (isCompact_closedBall _ _)
    have hG : Integrable (B.indicator (fun u => ‖γ u‖)) volume :=
      (integrable_indicator_iff measurableSet_closedBall).2 hγB.norm
    have h1 : Integrable (fun q : Euc d × Euc d => B.indicator (fun u => ‖γ u‖) q.1 * (1 : ℝ))
        ((volume : Measure (Euc d)).prod ν) :=
      hG.mul_prod (integrable_const (1 : ℝ))
    have h2 := (measurePreserving_sub_prod (volume : Measure (Euc d)) ν).integrable_comp_of_integrable h1
    have hmeas : AEStronglyMeasurable (fun q : Euc d × Euc d => ψ q.1 * γ (q.1 - q.2) * g q.2)
        ((volume : Measure (Euc d)).prod ν) := by
      have h3 : AEStronglyMeasurable (fun q : Euc d × Euc d => γ q.1)
          ((volume : Measure (Euc d)).prod ν) := hγ.aestronglyMeasurable.comp_fst
      have h4 := h3.comp_measurePreserving (measurePreserving_sub_prod (volume : Measure (Euc d)) ν)
      exact ((hψ.comp continuous_fst).aestronglyMeasurable.mul h4).mul
        (hg.comp continuous_snd).aestronglyMeasurable
    refine Integrable.mono' (h2.const_mul (Bψ * Bg)) hmeas ?_
    have hy : ∀ᵐ q ∂((volume : Measure (Euc d)).prod ν), q.2 ∈ periodBox d L :=
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Euc d))) (ν := ν)).ae
        (ae_restrict_mem (sa12c20_box_meas L))
    filter_upwards [hy] with q hq
    simp only [Function.comp, norm_mul]
    by_cases hx : ψ q.1 = 0
    · rw [hx, norm_zero, zero_mul, zero_mul]
      exact mul_nonneg (mul_nonneg hBψ0 hBg0)
        (mul_nonneg (Set.indicator_nonneg (fun u _ => norm_nonneg _) _) zero_le_one)
    · have hxs : q.1 ∈ tsupport ψ := subset_tsupport _ (Function.mem_support.2 hx)
      have hqR : q.1 - q.2 ∈ B := by
        rw [hB, Metric.mem_closedBall, dist_zero_right]
        calc ‖q.1 - q.2‖ ≤ ‖q.1‖ + ‖q.2‖ := norm_sub_le _ _
          _ ≤ Rk + Real.sqrt (d * L ^ 2) := add_le_add (hRk _ hxs) (sa12c20_box_norm L _ hq)
      rw [Set.indicator_of_mem hqR, mul_one]
      have hψ0 : 0 ≤ ‖γ (q.1 - q.2)‖ := norm_nonneg _
      calc ‖ψ q.1‖ * ‖γ (q.1 - q.2)‖ * ‖g q.2‖ ≤ Bψ * ‖γ (q.1 - q.2)‖ * Bg :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hBψ _) hψ0) (hgb _) (norm_nonneg _)
              (mul_nonneg hBψ0 hψ0)
        _ = Bψ * Bg * ‖γ (q.1 - q.2)‖ := by ring
  have hint : Integrable (fun x => ∫ y, ψ x * γ (x - y) * g y ∂ν) volume := hΦ.integral_prod_left
  have hE : ∀ x, ψ x * perConv L γ g x = ∫ y, ψ x * γ (x - y) * g y ∂ν := by
    intro x
    unfold perConv
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only [mul_assoc])
  refine ⟨hint.congr (Filter.Eventually.of_forall fun x => (hE x).symm), ?_⟩
  simp_rw [hE]
  rw [integral_integral_swap hΦ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ∫ x, ψ x * γ (x - y) * g y = g y * ∫ x, ψ x * γ (x - y)
  rw [integral_mul_const, mul_comm]

/-- The inner integral of the Fubini identity, via evenness of `γ`. -/
theorem sa12v_inner_eq {γ ψ : Euc d → ℝ} (hev : ∀ᵐ u ∂(volume : Measure (Euc d)), γ (-u) = γ u)
    (y : Euc d) : ∫ x, ψ x * γ (x - y) = sa12vH γ ψ y := by
  unfold sa12vH
  have h1 : ∀ᵐ x ∂(volume : Measure (Euc d)), γ (-(y - x)) = γ (y - x) :=
    (Measure.measurePreserving_sub_left (volume : Measure (Euc d)) y).quasiMeasurePreserving.ae hev
  refine integral_congr_ae ?_
  filter_upwards [h1] with x hx
  have : x - y = -(y - x) := by abel
  show ψ x * γ (x - y) = γ (y - x) * ψ x
  rw [this, hx, mul_comm]


theorem sa12v_partialDeriv_one (F : Euc d → ℝ) (j : Fin d) (x : Euc d) :
    partialDeriv (fun _ : Fin 1 => j) F x = fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ)) := by
  unfold partialDeriv
  rw [iteratedFDeriv_one_apply]

/-- The `(i,j)` summand of the nonlocal identity. -/
theorem sa12v_pair (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L)
    {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) {m f ψ : Euc d → ℝ}
    (hm : ContDiff ℝ ∞ m) (hmp : ∀ (x : Euc d) (k : Fin d → ℤ), m (x + L • latticePt k) = m x)
    (hf : ContDiff ℝ ∞ f) (hfp : ∀ (x : Euc d) (k : Fin d → ℤ), f (x + L • latticePt k) = f x)
    (hψ : IsCcInfty ψ) (i j : Fin d) :
    Integrable (fun x => ψ x * perConv L γ
      (fun y => fderiv ℝ (fun y => m y * fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))) y
        (EuclideanSpace.single i (1 : ℝ))) x) ∧
    ∫ x, ψ x * perConv L γ
      (fun y => fderiv ℝ (fun y => m y * fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))) y
        (EuclideanSpace.single i (1 : ℝ))) x =
    ∫ z in periodBox d L, f z * fderiv ℝ (fun y => m y * gradient (sa12vH γ ψ) y i) z
        (EuclideanSpace.single j (1 : ℝ)) := by
  set ei : Euc d := EuclideanSpace.single i (1 : ℝ) with hei
  set ej : Euc d := EuclideanSpace.single j (1 : ℝ) with hej
  set hj : Euc d → ℝ := fun y => m y * fderiv ℝ f y ej with hhj
  set H : Euc d → ℝ := sa12vH γ ψ with hH
  have hHs : ContDiff ℝ ∞ H := sa12v_H_smooth hγ.locInt hψ.1 hψ.2
  have hHp : ∀ (x : Euc d) (k : Fin d → ℤ), H (x + L • latticePt k) = H x :=
    sa12v_H_periodic hγ.periodic ψ
  have hfd : ContDiff ℝ ∞ (fun y => fderiv ℝ f y ej) :=
    (hf.fderiv_right (m := ∞) (by exact_mod_cast le_top)).clm_apply contDiff_const
  have hhjs : ContDiff ℝ ∞ hj := hm.mul hfd
  have hhjp : ∀ (x : Euc d) (k : Fin d → ℤ), hj (x + L • latticePt k) = hj x := by
    intro x k
    simp only [hhj, hmp, sa12v_fderiv_periodic L hfp ej]
  set g : Euc d → ℝ := fun y => fderiv ℝ hj y ei with hg
  have hgc : Continuous g :=
    ((hhjs.continuous_fderiv (by simp))).clm_apply continuous_const
  have hgp : ∀ (x : Euc d) (k : Fin d → ℤ), g (x + L • latticePt k) = g x :=
    sa12v_fderiv_periodic L hhjp ei
  obtain ⟨Bg, hBg⟩ := sa12v_bdd L hL g hgc hgp
  obtain ⟨hint, heq⟩ := sa12v_fubini L hγ.locInt hgc Bg hBg hψ.1.continuous hψ.2
  refine ⟨hint, ?_⟩
  rw [heq]
  have hev := sa12v_gamma_even_ae hd hs0 hsd hL hγ
  simp_rw [sa12v_inner_eq hev]
  -- first integration by parts
  have e1 := sa12v_per_ibp L hL (u := hj) (w := H) (hhjs.of_le (by simp)) (hHs.of_le (by simp)) hhjp hHp i
  -- second integration by parts
  set q : Euc d → ℝ := fun y => m y * gradient H y i with hq
  have hgradH : ContDiff ℝ ∞ (fun y => gradient H y i) := by
    have : (fun y => gradient H y i) = fun y => fderiv ℝ H y ei := funext fun y => sa12v_grad_coord H y i
    rw [this]
    exact (hHs.fderiv_right (m := ∞) (by exact_mod_cast le_top)).clm_apply contDiff_const
  have hqs : ContDiff ℝ ∞ q := hm.mul hgradH
  have hqp : ∀ (x : Euc d) (k : Fin d → ℤ), q (x + L • latticePt k) = q x := by
    intro x k
    have : ∀ y, gradient H y i = fderiv ℝ H y ei := fun y => sa12v_grad_coord H y i
    simp only [hq, this, hmp, sa12v_fderiv_periodic L hHp ei]
  have e2 := sa12v_per_ibp L hL (u := f) (w := q) (hf.of_le (by simp)) (hqs.of_le (by simp)) hfp hqp j
  have eq1 : ∀ z, g z * H z = fderiv ℝ hj z ei * H z := fun z => rfl
  calc ∫ y in periodBox d L, g y * H y
      = ∫ y in periodBox d L, fderiv ℝ hj y ei * H y := rfl
    _ = -∫ z in periodBox d L, hj z * fderiv ℝ H z ei := e1
    _ = -∫ z in periodBox d L, fderiv ℝ f z ej * q z := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        show m z * fderiv ℝ f z ej * fderiv ℝ H z ei = fderiv ℝ f z ej * (m z * gradient H z i)
        rw [sa12v_grad_coord]; ring
    _ = ∫ z in periodBox d L, f z * fderiv ℝ q z ej := by rw [e2, neg_neg]


theorem sa12v_integrableOn_cb (L : ℝ) {f : Euc d → ℝ} (hf : Continuous f) :
    IntegrableOn f (centeredBox d L) := by
  have hK := HRS.MS.ToriCoefB.tcb_compact_Icc (d := d) (-(L / 2)) (L / 2)
  refine (hf.continuousOn.integrableOn_compact hK).mono_set ?_
  intro x hx i
  exact ⟨(hx i).1, (hx i).2.le⟩

/-- The nonlocal identity `∫ ψ 𝒢_L[f] = ∫_{box} f · nonlocalTestPer ψ`. -/
theorem sa12v_nonlocal (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L)
    {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) (M : Matrix (Fin d) (Fin d) ℝ)
    {m f ψ : Euc d → ℝ}
    (hm : ContDiff ℝ ∞ m) (hmp : ∀ (x : Euc d) (k : Fin d → ℤ), m (x + L • latticePt k) = m x)
    (hf : ContDiff ℝ ∞ f) (hfp : ∀ (x : Euc d) (k : Fin d → ℤ), f (x + L • latticePt k) = f x)
    (hψ : IsCcInfty ψ) :
    Integrable (fun x => ψ x * perNonlocal L γ M m f x) ∧
    ∫ x, ψ x * perNonlocal L γ M m f x =
      ∫ x in centeredBox d L, f x * nonlocalTestPer L γ M m ψ x := by
  set H : Euc d → ℝ := sa12vH γ ψ with hH
  have hHs : ContDiff ℝ ∞ H := sa12v_H_smooth hγ.locInt hψ.1 hψ.2
  have hHp : ∀ (x : Euc d) (k : Fin d → ℤ), H (x + L • latticePt k) = H x :=
    sa12v_H_periodic hγ.periodic ψ
  have hpair := fun i j => sa12v_pair hd hs0 hsd hL hγ hm hmp hf hfp hψ i j
  -- pointwise expansion of the left side
  have hexp : ∀ x, ψ x * perNonlocal L γ M m f x = ∑ i : Fin d, ∑ j : Fin d,
      M j i * (ψ x * perConv L γ
        (fun y => fderiv ℝ (fun y => m y * fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))) y
          (EuclideanSpace.single i (1 : ℝ))) x) := by
    intro x
    unfold perNonlocal
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hfd : ContDiff ℝ ∞ (fun y => fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))) :=
      (hf.fderiv_right (m := ∞) (by exact_mod_cast le_top)).clm_apply contDiff_const
    have hhjs : ContDiff ℝ ∞ (fun y => m y * fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))) :=
      hm.mul hfd
    have hhjp : ∀ (x : Euc d) (k : Fin d → ℤ),
        m (x + L • latticePt k) * fderiv ℝ f (x + L • latticePt k) (EuclideanSpace.single j (1 : ℝ)) =
          m x * fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)) := by
      intro x k
      rw [hmp, sa12v_fderiv_periodic L hfp _]
    rw [periodic_convolution_derivative L hL γ _ hγ.locInt hγ.periodic (hhjs.of_le (by simp)) hhjp i x]
    ring
  simp_rw [hexp]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hpair i j).1.const_mul _, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hpair i j).1.const_mul _]
  -- the right side
  have hqs : ∀ i : Fin d, ContDiff ℝ ∞ (fun y => m y * gradient H y i) := by
    intro i
    have h1 : ContDiff ℝ ∞ (fun y => gradient H y i) := by
      have : (fun y => gradient H y i) = fun y => fderiv ℝ H y (EuclideanSpace.single i (1 : ℝ)) :=
        funext fun y => sa12v_grad_coord H y i
      rw [this]
      exact (hHs.fderiv_right (m := ∞) (by exact_mod_cast le_top)).clm_apply contDiff_const
    exact hm.mul h1
  have hqp : ∀ i : Fin d, ∀ (x : Euc d) (k : Fin d → ℤ),
      m (x + L • latticePt k) * gradient H (x + L • latticePt k) i = m x * gradient H x i := by
    intro i x k
    have : ∀ y, gradient H y i = fderiv ℝ H y (EuclideanSpace.single i (1 : ℝ)) :=
      fun y => sa12v_grad_coord H y i
    simp only [this, hmp, sa12v_fderiv_periodic L hHp _]
  have hcontij : ∀ i j : Fin d, Continuous (fun x => f x * fderiv ℝ (fun y => m y * gradient H y i) x
      (EuclideanSpace.single j (1 : ℝ))) := fun i j =>
    hf.continuous.mul (((hqs i).continuous_fderiv (by simp)).clm_apply continuous_const)
  have hperij : ∀ i j : Fin d, ∀ (x : Euc d) (k : Fin d → ℤ),
      f (x + L • latticePt k) * fderiv ℝ (fun y => m y * gradient H y i) (x + L • latticePt k)
        (EuclideanSpace.single j (1 : ℝ)) =
      f x * fderiv ℝ (fun y => m y * gradient H y i) x (EuclideanSpace.single j (1 : ℝ)) := by
    intro i j x k
    rw [hfp, sa12v_fderiv_periodic L (hqp i) _]
  have hR : ∀ x, f x * nonlocalTestPer L γ M m ψ x = ∑ i : Fin d, ∑ j : Fin d, M j i *
      (f x * fderiv ℝ (fun y => m y * gradient H y i) x (EuclideanSpace.single j (1 : ℝ))) := by
    intro x
    unfold nonlocalTestPer
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sa12v_partialDeriv_one]
    change f x * (M j i * _) = M j i * (f x * fderiv ℝ (fun y => m y *
      gradient (fun w => ∫ u, γ (w - u) * ψ u) y i) x (EuclideanSpace.single j (1 : ℝ)))
    ring
  simp_rw [hR]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (sa12v_integrableOn_cb L (hcontij i j)).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hpair i j).1.const_mul _,
    integral_finsetSum _ fun j _ => (sa12v_integrableOn_cb L (hcontij i j)).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_const_mul, (hpair i j).2]
  congr 1
  exact (sa12v_centered_eq L hL (hperij i j)).symm

end HRS.MH.AdjointRd.Phase2SA12Construction
