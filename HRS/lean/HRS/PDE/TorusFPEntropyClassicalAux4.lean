import HRS.PDE.TorusFPEntropyClassicalAux3

/-!
# D3-a (classical layer), helper 4: the relative Fisher information of a classical density

For `μ = P.withDensity w` and a smooth vector field `ζ` the integrand of `d1_fisherInfo` integrates by parts
(`∫ div ζ · wG = -∫ ζ · ∇(wG)`, coordinatewise `PDE.integral_partialDeriv_mul`) to
`∫ (2 ζ·v - ‖ζ‖²) dμ`, `v = ∇ log w - ∇ψ`.  After this identity the functional is continuous in `ζ` for the
sup norm, so the supremum over *smooth* fields is `∫ ‖v‖² dμ` by uniform approximation of the (only
continuous) field `v` (no `C¹` approximation is needed).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d3a_smoothE_ck1 {ζ : Torus n → Euc n} (hζ : Torus.IsSmooth ζ) : Torus.IsCk 1 ζ := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ζ) := hζ
  exact h.of_le (by norm_num)

theorem d3a_smoothE_cont {ζ : Torus n → Euc n} (hζ : Torus.IsSmooth ζ) : Continuous ζ :=
  Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ζ) from hζ).continuous

theorem d3a_comp_ck {k : WithTop ℕ∞} {ζ : Torus n → Euc n} (hζ : Torus.IsCk k ζ) (j : Fin n) :
    Torus.IsCk k (fun y => (ζ y).ofLp j) := by
  unfold Torus.IsCk
  exact (EuclideanSpace.proj j : Euc n →L[ℝ] ℝ).contDiff.comp hζ

theorem d3a_div_eq {ζ : Torus n → Euc n} (hζ : Torus.IsCk 1 ζ) (x : Torus n) :
    Torus.div ζ x = ∑ j, Torus.partialDeriv j (fun y => (ζ y).ofLp j) x := by
  unfold Torus.div
  refine Finset.sum_congr rfl fun j _ => ?_
  have hd : DifferentiableAt ℝ (Torus.lift ζ) (Torus.rep x) :=
    (hζ.differentiable one_ne_zero) (Torus.rep x)
  have h := (EuclideanSpace.proj j : Euc n →L[ℝ] ℝ).hasFDerivAt.comp (Torus.rep x) hd.hasFDerivAt
  have e : Torus.lift (fun y => (ζ y).ofLp j) =
      (EuclideanSpace.proj j : Euc n →L[ℝ] ℝ) ∘ Torus.lift ζ := rfl
  simp only [Torus.partialDeriv]
  rw [e, h.fderiv]
  simp

theorem d3a_continuous_grad_ck1 {φ : Torus n → ℝ} (hφ : Torus.IsCk 1 φ) :
    Continuous (Torus.grad φ) := by
  apply Torus.continuous_of_continuous_lift
  have e : Torus.lift (Torus.grad φ) = gradient (Torus.lift φ) := by
    funext y
    exact grad_mk φ y
  rw [e]
  exact d1_continuous_gradient_euc hφ

theorem d3a_sum_lin1 (d p q : Fin n → ℝ) (A B : ℝ) :
    A * (-2 * ∑ j, d j + B * ∑ j, p j - ∑ j, q j) =
      ∑ j, A * (-2 * d j + B * p j - q j) := by
  have h : ∀ j, A * (-2 * d j + B * p j - q j) = (A * (-2)) * d j + (A * B) * p j - A * q j :=
    fun j => by ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem d3a_sum_lin2 (a q : Fin n → ℝ) (A : ℝ) :
    A * (2 * ∑ j, a j - ∑ j, q j) = ∑ j, A * (2 * a j - q j) := by
  have h : ∀ j, A * (2 * a j - q j) = (A * 2) * a j - A * q j := fun j => by ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Coordinate identity: after integration by parts in the `j`-th direction. -/
theorem d3a_fisher_coord {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {w ψ : Torus n → ℝ} (hw : Torus.IsCk 2 w) (hpos : ∀ x, 0 < w x) (hψ : Torus.IsCk 2 ψ)
    {a : Torus n → ℝ} (ha : Torus.IsSmooth a) (j : Fin n) :
    ∫ x, w x * d1_gibbsWeight κ U x * (-2 * Torus.partialDeriv j a x +
        2 * κ⁻¹ * (a x * Torus.partialDeriv j (d3_tiltPot κ U ψ) x) - a x ^ 2) =
      ∫ x, w x * d1_gibbsWeight κ U x * (2 * (a x * (Torus.partialDeriv j (fun y => Real.log (w y)) x -
        Torus.partialDeriv j ψ x)) - a x ^ 2) := by
  have hκ0 : κ ≠ 0 := hκ.ne'
  have hU1 := d3a_smooth_ck1 hU
  have hw1 := d3a_ck2_ck1 hw
  have hψ1 := d3a_ck2_ck1 hψ
  have ha1 := d3a_smooth_ck1 ha
  have hG1 := d1c_gibbs_isCk1 (κ := κ) hU1
  have hwG1 : Torus.IsCk 1 (fun y => w y * d1_gibbsWeight κ U y) := hw1.mul hG1
  have hlog1 : Torus.IsCk 1 (fun y => Real.log (w y)) := d3a_isCk_log hw1 hpos
  have cw := d3a_continuous_of_ck1 hw1
  have cG := d1c_gibbs_continuous (κ := κ) hU
  have ca := d3a_continuous_of_ck1 ha1
  have cda : Continuous (Torus.partialDeriv j a) := PDE.continuous_partialDeriv j a ha1
  have cdψ : Continuous (Torus.partialDeriv j ψ) := PDE.continuous_partialDeriv j ψ hψ1
  have cdU : Continuous (Torus.partialDeriv j U) := PDE.continuous_partialDeriv j U hU1
  have cdl : Continuous (Torus.partialDeriv j (fun y => Real.log (w y))) :=
    PDE.continuous_partialDeriv j _ hlog1
  have cdwG : Continuous (Torus.partialDeriv j (fun y => w y * d1_gibbsWeight κ U y)) :=
    PDE.continuous_partialDeriv j _ hwG1
  have hpdV : ∀ x, Torus.partialDeriv j (d3_tiltPot κ U ψ) x =
      Torus.partialDeriv j U x - κ * Torus.partialDeriv j ψ x := fun x => d3a_pd_tilt hU1 hψ1 j x
  have cV : Continuous (Torus.partialDeriv j (d3_tiltPot κ U ψ)) := by
    have : Torus.partialDeriv j (d3_tiltPot κ U ψ) =
        fun x => Torus.partialDeriv j U x - κ * Torus.partialDeriv j ψ x := funext hpdV
    rw [this]
    exact cdU.sub (continuous_const.mul cdψ)
  have hpdl : ∀ x, Torus.partialDeriv j (fun y => Real.log (w y)) x =
      Torus.partialDeriv j w x / w x := fun x => d3a_pd_log hw1 hpos j x
  have hpdwG : ∀ x, Torus.partialDeriv j (fun y => w y * d1_gibbsWeight κ U y) x =
      Torus.partialDeriv j w x * d1_gibbsWeight κ U x +
        w x * (-(κ⁻¹ * Torus.partialDeriv j U x) * d1_gibbsWeight κ U x) := fun x => by
    rw [d3a_pd_mul hw1 hG1 j x, d1c_partialDeriv_gibbs hU1 j x]
  have hIBP := PDE.integral_partialDeriv_mul j a (fun y => w y * d1_gibbsWeight κ U y) ha1 hwG1
  have hA : ∫ x, -2 * (Torus.partialDeriv j a x * (w x * d1_gibbsWeight κ U x)) =
      2 * ∫ x, a x * Torus.partialDeriv j (fun y => w y * d1_gibbsWeight κ U y) x := by
    rw [integral_const_mul, hIBP]
    ring
  have hB1 : Continuous fun x => -2 * (Torus.partialDeriv j a x * (w x * d1_gibbsWeight κ U x)) :=
    continuous_const.mul (cda.mul (cw.mul cG))
  have hB2 : Continuous fun x => w x * d1_gibbsWeight κ U x *
      (2 * κ⁻¹ * (a x * Torus.partialDeriv j (d3_tiltPot κ U ψ) x) - a x ^ 2) :=
    (cw.mul cG).mul ((continuous_const.mul (ca.mul cV)).sub (ca.pow 2))
  have hB3 : Continuous fun x => 2 * (a x * Torus.partialDeriv j
      (fun y => w y * d1_gibbsWeight κ U y) x) := continuous_const.mul (ca.mul cdwG)
  calc ∫ x, w x * d1_gibbsWeight κ U x * (-2 * Torus.partialDeriv j a x +
        2 * κ⁻¹ * (a x * Torus.partialDeriv j (d3_tiltPot κ U ψ) x) - a x ^ 2)
      = ∫ x, (-2 * (Torus.partialDeriv j a x * (w x * d1_gibbsWeight κ U x)) +
          w x * d1_gibbsWeight κ U x *
            (2 * κ⁻¹ * (a x * Torus.partialDeriv j (d3_tiltPot κ U ψ) x) - a x ^ 2)) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        ring
    _ = (∫ x, -2 * (Torus.partialDeriv j a x * (w x * d1_gibbsWeight κ U x))) +
          ∫ x, w x * d1_gibbsWeight κ U x *
            (2 * κ⁻¹ * (a x * Torus.partialDeriv j (d3_tiltPot κ U ψ) x) - a x ^ 2) :=
        integral_add (d3a_hint _ hB1) (d3a_hint _ hB2)
    _ = (∫ x, 2 * (a x * Torus.partialDeriv j (fun y => w y * d1_gibbsWeight κ U y) x)) +
          ∫ x, w x * d1_gibbsWeight κ U x *
            (2 * κ⁻¹ * (a x * Torus.partialDeriv j (d3_tiltPot κ U ψ) x) - a x ^ 2) := by
        rw [hA, integral_const_mul]
    _ = ∫ x, (2 * (a x * Torus.partialDeriv j (fun y => w y * d1_gibbsWeight κ U y) x) +
          w x * d1_gibbsWeight κ U x *
            (2 * κ⁻¹ * (a x * Torus.partialDeriv j (d3_tiltPot κ U ψ) x) - a x ^ 2)) :=
        (integral_add (d3a_hint _ hB3) (d3a_hint _ hB2)).symm
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        have hwx : w x ≠ 0 := (hpos x).ne'
        beta_reduce
        rw [hpdwG x, hpdV x, hpdl x]
        field_simp
        ring

/-- The integration-by-parts formula for the integrand of `d1_fisherInfo` against `P.withDensity w`. -/
theorem d3a_fisher_formula {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {w ψ : Torus n → ℝ} (hw : Torus.IsCk 2 w) (hpos : ∀ x, 0 < w x) (hψ : Torus.IsCk 2 ψ)
    {ζ : Torus n → Euc n} (hζ : Torus.IsSmooth ζ) :
    ∫ x, (-2 * Torus.div ζ x + 2 * κ⁻¹ * inner ℝ (ζ x) (Torus.grad (d3_tiltPot κ U ψ) x) - ‖ζ x‖ ^ 2)
        ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w x)) =
      ∫ x, (2 * inner ℝ (ζ x) (Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x) - ‖ζ x‖ ^ 2)
        ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w x)) := by
  obtain ⟨c, hc⟩ := d3a_exists_c (κ := κ) hU
  have hU1 := d3a_smooth_ck1 hU
  have hw1 := d3a_ck2_ck1 hw
  have hψ1 := d3a_ck2_ck1 hψ
  have hζ1 := d3a_smoothE_ck1 hζ
  have cw := d3a_continuous_of_ck1 hw1
  have cG := d1c_gibbs_continuous (κ := κ) hU
  have hlog1 : Torus.IsCk 1 (fun y => Real.log (w y)) := d3a_isCk_log hw1 hpos
  rw [d3a_integral_withDensity cw.measurable (fun x => (hpos x).le),
    d3a_integral_withDensity cw.measurable (fun x => (hpos x).le), hc, hc]
  congr 1
  have hcomp : ∀ j : Fin n, Torus.IsSmooth (fun y => (ζ y).ofLp j) := fun j => d3a_comp_ck hζ j
  have hL : ∀ x, w x * (-2 * Torus.div ζ x +
        2 * κ⁻¹ * inner ℝ (ζ x) (Torus.grad (d3_tiltPot κ U ψ) x) - ‖ζ x‖ ^ 2) *
        d1_gibbsWeight κ U x =
      ∑ j, w x * d1_gibbsWeight κ U x * (-2 * Torus.partialDeriv j (fun y => (ζ y).ofLp j) x +
        2 * κ⁻¹ * ((ζ x).ofLp j * Torus.partialDeriv j (d3_tiltPot κ U ψ) x) -
          ((ζ x).ofLp j) ^ 2) := by
    intro x
    rw [show w x * (-2 * Torus.div ζ x +
        2 * κ⁻¹ * inner ℝ (ζ x) (Torus.grad (d3_tiltPot κ U ψ) x) - ‖ζ x‖ ^ 2) *
        d1_gibbsWeight κ U x = w x * d1_gibbsWeight κ U x * (-2 * Torus.div ζ x +
        2 * κ⁻¹ * inner ℝ (ζ x) (Torus.grad (d3_tiltPot κ U ψ) x) - ‖ζ x‖ ^ 2) by ring,
      d3a_div_eq hζ1 x, d3a_inner_eq_sum, d3a_norm_sq_eq (ζ x)]
    simp only [d1c_grad_component]
    exact d3a_sum_lin1 (fun j => Torus.partialDeriv j (fun y => (ζ y).ofLp j) x)
      (fun j => (ζ x).ofLp j * Torus.partialDeriv j (d3_tiltPot κ U ψ) x)
      (fun j => ((ζ x).ofLp j) ^ 2) (w x * d1_gibbsWeight κ U x) (2 * κ⁻¹)
  have hR : ∀ x, w x * (2 * inner ℝ (ζ x) (Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x) -
        ‖ζ x‖ ^ 2) * d1_gibbsWeight κ U x =
      ∑ j, w x * d1_gibbsWeight κ U x * (2 * ((ζ x).ofLp j *
        (Torus.partialDeriv j (fun y => Real.log (w y)) x - Torus.partialDeriv j ψ x)) -
          ((ζ x).ofLp j) ^ 2) := by
    intro x
    rw [show w x * (2 * inner ℝ (ζ x) (Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x) -
        ‖ζ x‖ ^ 2) * d1_gibbsWeight κ U x = w x * d1_gibbsWeight κ U x *
        (2 * inner ℝ (ζ x) (Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x) -
        ‖ζ x‖ ^ 2) by ring, d3a_inner_eq_sum, d3a_norm_sq_eq (ζ x)]
    simp only [PiLp.sub_apply, d1c_grad_component]
    exact d3a_sum_lin2 (fun j => (ζ x).ofLp j *
        (Torus.partialDeriv j (fun y => Real.log (w y)) x - Torus.partialDeriv j ψ x))
      (fun j => ((ζ x).ofLp j) ^ 2) (w x * d1_gibbsWeight κ U x)
  have hintT : ∀ j : Fin n, Integrable (fun x => w x * d1_gibbsWeight κ U x *
      (-2 * Torus.partialDeriv j (fun y => (ζ y).ofLp j) x +
        2 * κ⁻¹ * ((ζ x).ofLp j * Torus.partialDeriv j (d3_tiltPot κ U ψ) x) -
          ((ζ x).ofLp j) ^ 2)) := by
    intro j
    have h1 := d3a_smooth_ck1 (hcomp j)
    have ca := d3a_continuous_of_ck1 h1
    have cda : Continuous (Torus.partialDeriv j (fun y => (ζ y).ofLp j)) :=
      PDE.continuous_partialDeriv j _ h1
    have cV : Continuous (Torus.partialDeriv j (d3_tiltPot κ U ψ)) := by
      have : Torus.partialDeriv j (d3_tiltPot κ U ψ) =
          fun x => Torus.partialDeriv j U x - κ * Torus.partialDeriv j ψ x :=
        funext fun x => d3a_pd_tilt hU1 hψ1 j x
      rw [this]
      exact (PDE.continuous_partialDeriv j U hU1).sub
        (continuous_const.mul (PDE.continuous_partialDeriv j ψ hψ1))
    exact d3a_hint _ ((cw.mul cG).mul (((continuous_const.mul cda).add
      (continuous_const.mul (ca.mul cV))).sub (ca.pow 2)))
  have hintS : ∀ j : Fin n, Integrable (fun x => w x * d1_gibbsWeight κ U x *
      (2 * ((ζ x).ofLp j * (Torus.partialDeriv j (fun y => Real.log (w y)) x -
        Torus.partialDeriv j ψ x)) - ((ζ x).ofLp j) ^ 2)) := by
    intro j
    have h1 := d3a_smooth_ck1 (hcomp j)
    have ca := d3a_continuous_of_ck1 h1
    exact d3a_hint _ ((cw.mul cG).mul ((continuous_const.mul (ca.mul
      ((PDE.continuous_partialDeriv j _ hlog1).sub (PDE.continuous_partialDeriv j ψ hψ1)))).sub
      (ca.pow 2)))
  simp_rw [hL, hR]
  rw [integral_finsetSum _ fun j _ => hintT j, integral_finsetSum _ fun j _ => hintS j]
  exact Finset.sum_congr rfl fun j _ => d3a_fisher_coord hκ hU hw hpos hψ (hcomp j) j

/-- Uniform approximation of a continuous vector field by smooth ones, with a quantitative square bound. -/
theorem d3a_approx_field {v : Torus n → Euc n} (hv : Continuous v) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ζ : Torus n → Euc n, Torus.IsSmooth ζ ∧ ∀ x, ‖ζ x - v x‖ ^ 2 ≤ n * δ ^ 2 := by
  have h : ∀ j : Fin n, ∃ a : Torus n → ℝ, Torus.IsSmooth a ∧ ∀ x, |(v x).ofLp j - a x| ≤ δ :=
    fun j => d1_exists_smooth_approx (f := fun x => (v x).ofLp j)
      ((EuclideanSpace.proj j : Euc n →L[ℝ] ℝ).continuous.comp hv) hδ
  choose a ha hab using h
  refine ⟨fun x => WithLp.toLp 2 (fun j => a j x), ?_, fun x => ?_⟩
  · unfold Torus.IsSmooth Torus.IsCk
    refine contDiff_euclidean.2 fun j => ?_
    exact ha j
  · rw [d3a_norm_sq_eq]
    calc ∑ j, ((WithLp.toLp 2 (fun j => a j x) - v x).ofLp j) ^ 2 ≤ ∑ _j : Fin n, δ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have e : (WithLp.toLp 2 (fun j => a j x) - v x).ofLp j = a j x - (v x).ofLp j := by simp
          rw [e]
          have h2 : |a j x - (v x).ofLp j| ≤ δ := by rw [abs_sub_comm]; exact hab j x
          exact sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
      _ = n * δ ^ 2 := by simp

/-- The vector field `v = ∇ log w - ∇ψ`. -/
def d3a_v (w ψ : Torus n → ℝ) (x : Torus n) : Euc n :=
  Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x

/-- **Fisher information of a classical density** (`d3_fisher_classical`). -/
theorem d3a_fisher {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {w ψ : Torus n → ℝ} (hw : Torus.IsCk 2 w) (hwpos : ∀ x, 0 < w x) (hψ : Torus.IsCk 2 ψ) :
    d1_fisherInfo κ (d3_tiltPot κ U ψ)
        ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w x))
      = ENNReal.ofReal (∫ x, ‖Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x‖ ^ 2
          ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w x))) := by
  haveI hP := d3a_gibbs_isProb (κ := κ) hU
  have hw1 := d3a_ck2_ck1 hw
  have hψ1 := d3a_ck2_ck1 hψ
  have cw := d3a_continuous_of_ck1 hw1
  have hlog1 : Torus.IsCk 1 (fun y => Real.log (w y)) := d3a_isCk_log hw1 hwpos
  haveI hfin : IsFiniteMeasure ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w x)) :=
    isFiniteMeasure_withDensity_ofReal (d3a_hint _ cw).hasFiniteIntegral
  set μ := (d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w x) with hμ
  show _ = ENNReal.ofReal (∫ x, ‖d3a_v w ψ x‖ ^ 2 ∂μ)
  have cv : Continuous (d3a_v w ψ) := (d3a_continuous_grad_ck1 hlog1).sub (d3a_continuous_grad_ck1 hψ1)
  have hvn : Continuous fun x => ‖d3a_v w ψ x‖ ^ 2 := cv.norm.pow 2
  have hform : ∀ ζ : Torus n → Euc n, Torus.IsSmooth ζ →
      ∫ x, (-2 * Torus.div ζ x + 2 * κ⁻¹ * inner ℝ (ζ x) (Torus.grad (d3_tiltPot κ U ψ) x) -
        ‖ζ x‖ ^ 2) ∂μ = ∫ x, (2 * inner ℝ (ζ x) (d3a_v w ψ x) - ‖ζ x‖ ^ 2) ∂μ :=
    fun ζ hζ => d3a_fisher_formula hκ hU hw hwpos hψ hζ
  have hintS : ∀ ζ : Torus n → Euc n, Torus.IsSmooth ζ →
      Integrable (fun x => 2 * inner ℝ (ζ x) (d3a_v w ψ x) - ‖ζ x‖ ^ 2) μ := fun ζ hζ =>
    d3a_hint μ ((continuous_const.mul ((d3a_smoothE_cont hζ).inner cv)).sub
      ((d3a_smoothE_cont hζ).norm.pow 2))
  have hpt : ∀ (ζ : Torus n → Euc n) (x : Torus n),
      2 * inner ℝ (ζ x) (d3a_v w ψ x) - ‖ζ x‖ ^ 2 = ‖d3a_v w ψ x‖ ^ 2 - ‖ζ x - d3a_v w ψ x‖ ^ 2 := by
    intro ζ x
    rw [norm_sub_sq_real]
    ring
  have hS : ∀ ζ : Torus n → Euc n, Torus.IsSmooth ζ →
      ∫ x, (2 * inner ℝ (ζ x) (d3a_v w ψ x) - ‖ζ x‖ ^ 2) ∂μ =
        (∫ x, ‖d3a_v w ψ x‖ ^ 2 ∂μ) - ∫ x, ‖ζ x - d3a_v w ψ x‖ ^ 2 ∂μ := by
    intro ζ hζ
    have hc2 : Continuous fun x => ‖ζ x - d3a_v w ψ x‖ ^ 2 := ((d3a_smoothE_cont hζ).sub cv).norm.pow 2
    rw [← integral_sub (d3a_hint μ hvn) (d3a_hint μ hc2)]
    exact integral_congr_ae (ae_of_all _ fun x => hpt ζ x)
  have hnn : ∀ ζ : Torus n → Euc n, 0 ≤ ∫ x, ‖ζ x - d3a_v w ψ x‖ ^ 2 ∂μ := fun ζ =>
    integral_nonneg fun x => sq_nonneg _
  unfold d1_fisherInfo
  apply le_antisymm
  · refine iSup₂_le fun ζ hζ => ?_
    rw [hform ζ hζ, hS ζ hζ]
    exact ENNReal.ofReal_le_ofReal (by linarith [hnn ζ])
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε hb => ?_
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = μ.real Set.univ := ⟨_, rfl⟩
    have hm0 : 0 ≤ m := by rw [hm]; exact measureReal_nonneg
    have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    set δ : ℝ := Real.sqrt ((ε : ℝ) / (((n : ℝ) + 1) * (m + 1))) with hδ
    have hδpos : 0 < δ := Real.sqrt_pos.2 (by positivity)
    have hδ2 : δ ^ 2 = (ε : ℝ) / (((n : ℝ) + 1) * (m + 1)) :=
      Real.sq_sqrt (by positivity)
    obtain ⟨ζ, hζ, hζb⟩ := d3a_approx_field cv hδpos
    have hint2 : ∫ x, ‖ζ x - d3a_v w ψ x‖ ^ 2 ∂μ ≤ ε := by
      calc ∫ x, ‖ζ x - d3a_v w ψ x‖ ^ 2 ∂μ ≤ ∫ _x, (n : ℝ) * δ ^ 2 ∂μ :=
            integral_mono (d3a_hint μ (((d3a_smoothE_cont hζ).sub cv).norm.pow 2))
              (integrable_const _) hζb
        _ = m * ((n : ℝ) * δ ^ 2) := by
            rw [integral_const, smul_eq_mul, ← hm]
        _ ≤ ε := by
            rw [hδ2]
            have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            have key : (n : ℝ) * m / (((n : ℝ) + 1) * (m + 1)) ≤ 1 := by
              rw [div_le_one (by positivity)]
              nlinarith
            calc m * ((n : ℝ) * ((ε : ℝ) / (((n : ℝ) + 1) * (m + 1))))
                = (ε : ℝ) * ((n : ℝ) * m / (((n : ℝ) + 1) * (m + 1))) := by ring
              _ ≤ (ε : ℝ) * 1 := mul_le_mul_of_nonneg_left key hεr.le
              _ = ε := mul_one _
    have hSζ : ∫ x, (‖d3a_v w ψ x‖ ^ 2) ∂μ ≤ (∫ x, (2 * inner ℝ (ζ x) (d3a_v w ψ x) - ‖ζ x‖ ^ 2) ∂μ) + ε := by
      rw [hS ζ hζ]
      linarith
    calc ENNReal.ofReal (∫ x, ‖d3a_v w ψ x‖ ^ 2 ∂μ)
        ≤ ENNReal.ofReal ((∫ x, (2 * inner ℝ (ζ x) (d3a_v w ψ x) - ‖ζ x‖ ^ 2) ∂μ) + ε) :=
          ENNReal.ofReal_le_ofReal hSζ
      _ ≤ ENNReal.ofReal (∫ x, (2 * inner ℝ (ζ x) (d3a_v w ψ x) - ‖ζ x‖ ^ 2) ∂μ) + ENNReal.ofReal ε :=
          ENNReal.ofReal_add_le
      _ ≤ _ := by
          refine add_le_add ?_ (by simp)
          refine le_iSup₂_of_le ζ hζ (le_of_eq ?_)
          rw [hform ζ hζ]

end HRS
