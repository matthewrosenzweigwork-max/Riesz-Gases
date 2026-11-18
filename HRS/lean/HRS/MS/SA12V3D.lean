import HRS.MS.SA12V3C

/-!
# S.A.12 N1/N2 (SA12V3 worker), part D: large period, near the origin (C18)

`γ_L = g + c + L^{-s} q(·/L)` on `‖z‖ < δ L`: the convolution `∫ γ_L(x-u) φ(u) du` is bounded by a constant independent of
`L` and converges to `∫ g(x-u) φ(u) du` (`g` the Euclidean Riesz kernel), uniformly in the test function `φ` (mean zero,
support radius `R`, bound `B`) and in `x` with `x - supp φ ⊂ B(0, r')`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12v3_ae_ne_zero (hd : 1 ≤ d) : ∀ᵐ z ∂(volume : Measure (Euc d)), z ≠ (0 : Euc d) := by
  haveI : NeZero d := ⟨by omega⟩
  rw [ae_iff]
  simpa using measure_singleton (0 : Euc d)

/-- Pointwise a.e. form of the C18 decomposition on a ball, uniformly in `L ≥ L₁`. -/
theorem sa12v3_C18_ball (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ M Lq : ℝ, 0 ≤ M ∧ 0 ≤ Lq ∧ ∀ r' : ℝ, 0 < r' → ∃ L₁ : ℝ, 1 ≤ L₁ ∧ ∀ L : ℝ, L₁ ≤ L →
      ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ → ∃ c c' : ℝ,
        ∀ᵐ z ∂(volume : Measure (Euc d)), z ∈ Metric.closedBall (0 : Euc d) r' →
          |γ z - c| ≤ |rieszKernel d s z| + M ∧ |(γ z - rieszKernel d s z) - c'| ≤ Lq * r' / L := by
  obtain ⟨δ, q, hδ, hq, hloc⟩ := periodic_kernel_local hd s hs0 hsd
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : Euc d) δ).exists_bound_of_continuousOn
    hq.continuous.continuousOn
  obtain ⟨Lq0, hLq0⟩ := (isCompact_closedBall (0 : Euc d) δ).exists_bound_of_continuousOn
    (hq.continuous_fderiv (by simp)).continuousOn
  have hM : 0 ≤ max M0 0 := le_max_right _ _
  have hLq : 0 ≤ max Lq0 0 := le_max_right _ _
  refine ⟨max M0 0, max Lq0 0, hM, hLq, fun r' hr' => ⟨max 1 ((r' + 1) / δ), le_max_left _ _, ?_⟩⟩
  intro L hL γ hγ
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
  have hδL : r' + 1 ≤ δ * L := by
    have h1 : (r' + 1) / δ ≤ L := (le_max_right _ _).trans hL
    rw [div_le_iff₀ hδ] at h1; linarith
  obtain ⟨c, hc0, hc⟩ := hloc L hL1 γ hγ
  refine ⟨c, c + L ^ (-s) * q 0, ?_⟩
  filter_upwards [sa12v3_ae_ne_zero hd] with z hz0 hzb
  rw [Metric.mem_closedBall, dist_zero_right] at hzb
  have hz1 : ‖z‖ < δ * L := by linarith
  have hform := hc z hz0 hz1
  have hLs0 : 0 ≤ L ^ (-s) := Real.rpow_nonneg hL0.le _
  have hLs1 : L ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hyn : ‖L⁻¹ • z‖ ≤ r' / L := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL0, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hzb hL0.le
  have hyδ : ‖L⁻¹ • z‖ ≤ δ := by
    refine hyn.trans ?_
    rw [div_le_iff₀ hL0]; linarith
  have hymem : L⁻¹ • z ∈ Metric.closedBall (0 : Euc d) δ := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hyδ
  constructor
  · have e : γ z - c = rieszKernel d s z + L ^ (-s) * q (L⁻¹ • z) := by rw [hform]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h1 : |L ^ (-s) * q (L⁻¹ • z)| ≤ max M0 0 := by
      rw [abs_mul, abs_of_nonneg hLs0]
      have := hM0 _ hymem
      rw [Real.norm_eq_abs] at this
      exact (mul_le_mul hLs1 (this.trans (le_max_left _ _)) (abs_nonneg _) zero_le_one).trans (one_mul _).le
    linarith
  · have e : (γ z - rieszKernel d s z) - (c + L ^ (-s) * q 0) = L ^ (-s) * (q (L⁻¹ • z) - q 0) := by
      rw [hform]; ring
    rw [e, abs_mul, abs_of_nonneg hLs0]
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := q) (C := max Lq0 0)
      (s := Metric.closedBall (0 : Euc d) δ) (x := 0) (y := L⁻¹ • z)
      (fun y _ => (hq.differentiable (by simp)) y)
      (fun y hy => (hLq0 y hy).trans (le_max_left _ _)) (convex_closedBall 0 δ)
      (Metric.mem_closedBall_self hδ.le) hymem
    rw [Real.norm_eq_abs, sub_zero] at hmv
    calc L ^ (-s) * |q (L⁻¹ • z) - q 0| ≤ 1 * (max Lq0 0 * (r' / L)) :=
          mul_le_mul hLs1 (hmv.trans (mul_le_mul_of_nonneg_left hyn hLq)) (abs_nonneg _) zero_le_one
      _ = _ := by ring

/-- Uniform bound for large `L`, near the origin. -/
theorem sa12v3_near_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (r' : ℝ) (hr' : 0 < r') :
    ∃ L₁ C : ℝ, 1 ≤ L₁ ∧ 0 ≤ C ∧ ∀ L : ℝ, L₁ ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ (R B : ℝ) (φ : Euc d → ℝ), sa12v3_Test R B φ → ∀ x : Euc d, (∀ u : Euc d, ‖u‖ ≤ R → ‖x - u‖ ≤ r') →
        |∫ u, γ (x - u) * φ u| ≤ C * B := by
  obtain ⟨M, Lq, hM, hLq, hball⟩ := sa12v3_C18_ball hd s hs0 hsd
  obtain ⟨L₁, hL₁, hL⟩ := hball r' hr'
  have hg := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hGi : IntegrableOn (fun z => |rieszKernel d s z| + M) (Metric.closedBall (0 : Euc d) r') volume :=
    ((hg.integrableOn_isCompact (isCompact_closedBall _ _)).norm).add
      (integrableOn_const measure_closedBall_lt_top.ne)
  refine ⟨L₁, ∫ z in Metric.closedBall (0 : Euc d) r', (|rieszKernel d s z| + M), hL₁,
    setIntegral_nonneg Metric.isClosed_closedBall.measurableSet (fun z _ => by positivity), ?_⟩
  intro L hLL γ hγ R B φ hT x hx
  obtain ⟨c, c', hcc⟩ := hL L hLL γ hγ
  have := sa12v3_conv_le hγ.locInt hT x 0 (r' := r') (fun u hu => by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hx u hu) c (fun z => |rieszKernel d s z| + M)
    (fun z => by positivity) hGi (by filter_upwards [hcc] with z hz hzm using (hz hzm).1)
  exact this.trans (le_of_eq (mul_comm _ _))

/-- Convergence to the Euclidean Riesz kernel for large `L`, near the origin. -/
theorem sa12v3_near_conv (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (r' : ℝ) (hr' : 0 < r')
    (η : ℝ) (hη : 0 < η) :
    ∃ L₁ : ℝ, 1 ≤ L₁ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ (R B : ℝ) (φ : Euc d → ℝ), sa12v3_Test R B φ → ∀ x : Euc d, (∀ u : Euc d, ‖u‖ ≤ R → ‖x - u‖ ≤ r') →
        |(∫ u, γ (x - u) * φ u) - ∫ u, rieszKernel d s (x - u) * φ u| ≤ η * B := by
  obtain ⟨M, Lq, hM, hLq, hball⟩ := sa12v3_C18_ball hd s hs0 hsd
  obtain ⟨L₁, hL₁, hL⟩ := hball r' hr'
  have hg := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  set V : ℝ := (volume : Measure (Euc d)).real (Metric.closedBall (0 : Euc d) r') with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  refine ⟨max L₁ (Lq * r' * V / η), hL₁.trans (le_max_left _ _), ?_⟩
  intro L hLL γ hγ R B φ hT x hx
  have hLa : L₁ ≤ L := (le_max_left _ _).trans hLL
  have hLb : Lq * r' * V / η ≤ L := (le_max_right _ _).trans hLL
  have hL0 : 0 < L := lt_of_lt_of_le one_pos (hL₁.trans hLa)
  obtain ⟨c, c', hcc⟩ := hL L hLa γ hγ
  have hf : LocallyIntegrable (fun z => γ z - rieszKernel d s z) volume := hγ.locInt.sub hg
  have key := sa12v3_conv_le hf hT x 0 (r' := r') (fun u hu => by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hx u hu) c' (fun _ => Lq * r' / L)
    (fun _ => by positivity) (integrableOn_const measure_closedBall_lt_top.ne)
    (by filter_upwards [hcc] with z hz hzm using (hz hzm).2)
  rw [setIntegral_const, smul_eq_mul, ← hV] at key
  have e : (∫ u, (γ (x - u) - rieszKernel d s (x - u)) * φ u) =
      (∫ u, γ (x - u) * φ u) - ∫ u, rieszKernel d s (x - u) * φ u := by
    have : ∀ u, (γ (x - u) - rieszKernel d s (x - u)) * φ u =
        γ (x - u) * φ u - rieszKernel d s (x - u) * φ u := fun u => by ring
    simp_rw [this]
    exact integral_sub (sa12v3_lint hγ.locInt hT x) (sa12v3_lint hg hT x)
  have key2 : |(∫ u, γ (x - u) * φ u) - ∫ u, rieszKernel d s (x - u) * φ u| ≤ B * (V * (Lq * r' / L)) := by
    rw [← e]; exact key
  refine key2.trans ?_
  have hB := hT.B_nonneg
  have h1 : V * (Lq * r' / L) ≤ η := by
    have : Lq * r' * V ≤ η * L := by
      rw [div_le_iff₀ hη] at hLb; linarith
    calc V * (Lq * r' / L) = (Lq * r' * V) / L := by ring
      _ ≤ η := by rw [div_le_iff₀ hL0]; linarith
  calc B * (V * (Lq * r' / L)) ≤ B * η := mul_le_mul_of_nonneg_left h1 hB
    _ = _ := by ring

end HRS.MH.AdjointRd.Phase2SA12V3
