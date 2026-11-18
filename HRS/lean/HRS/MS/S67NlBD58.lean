import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.PoisSgAux2

/-!
# S6.7 nonlinear, packet S6.7nl.58: derivative-only homogeneous OU gradient estimate

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4830-4834, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions: none.
For the zero drift the pathwise flow is the explicit map `x -> exp(-(q/nu) tau) x + sqrt 2 U_tau`
(the random ODE `Z' = -q' Z` is solved by `exp(-q' t) x`, uniqueness by a zero-derivative
argument), so differentiation under the expectation is `sg_family`, and the chain rule gives the
exact factor `exp(-q t)` for `tau = nu t`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

lemma s67bd_zero_cb (m : ℕ) : HasCbBound (d := d) m 0 (fun _ : Euc d => (0 : Euc d)) := by
  refine ⟨contDiff_const, fun j _ x => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · rw [iteratedFDeriv_const_of_ne (by omega)]; simp

lemma s67bd_pfZ_zero_drift {q' : ℝ} (hq : 0 ≤ q') {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) (x : Euc d) {τ : ℝ} (hτ : 0 ≤ τ) :
    pfZ q' (fun _ : Euc d => (0 : Euc d)) w x τ = Real.exp (-q' * τ) • x := by
  have H : PfHyp q' 0 1 (fun _ : Euc d => (0 : Euc d)) w :=
    ⟨hq, le_rfl, s67bd_zero_cb 1, hw, hw0⟩
  set Z := pfZ q' (fun _ : Euc d => (0 : Euc d)) w x with hZ
  have hF : ∀ s, pfDrift q' (fun _ : Euc d => (0 : Euc d)) w s (Z s) = -q' • Z s := by
    intro s; simp [pfDrift]
  have hderiv := pf_hasDerivWithinAt_of_integral (T := τ)
    (F := fun s => pfDrift q' (fun _ : Euc d => (0 : Euc d)) w s (Z s)) (Z := Z) (x := x)
    (pf_continuousOn_drift H x hτ) (fun t ht => pf_Z_eq H x ht.1)
  have hY : ∀ s ∈ Icc (0 : ℝ) τ,
      HasDerivWithinAt (fun s => Real.exp (q' * s) • Z s) 0 (Icc 0 τ) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (q' * s)) (Real.exp (q' * s) * q') s := by
      simpa using ((hasDerivAt_id s).const_mul q').exp
    have h2 := (h1.hasDerivWithinAt (s := Icc 0 τ)).smul (hderiv s hs)
    convert h2 using 1
    rw [hF s]
    module
  have hcont : ContinuousOn (fun s => Real.exp (q' * s) • Z s) (Icc 0 τ) :=
    fun s hs => (hY s hs).continuousWithinAt
  have hder : ∀ s ∈ Ico (0 : ℝ) τ,
      HasDerivWithinAt (fun s => Real.exp (q' * s) • Z s) 0 (Ici s) s := fun s hs =>
    (hY s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc hs.1 le_rfl))
  have hconst := constant_of_has_deriv_right_zero hcont hder τ ⟨hτ, le_rfl⟩
  simp only [mul_zero, Real.exp_zero, one_smul] at hconst
  rw [show Z 0 = x from pf_Z_zero H x] at hconst
  calc Z τ = Real.exp (-q' * τ) • (Real.exp (q' * τ) • Z τ) := by
        rw [smul_smul, ← Real.exp_add]; simp
    _ = Real.exp (-q' * τ) • x := by rw [hconst]

lemma s67bd_flowMap_zero_drift {q' : ℝ} (hq : 0 ≤ q') {w : ℝ≥0 → Fin d → ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    flowMap q' (fun _ : Euc d => (0 : Euc d)) w τ =
      fun x => Real.exp (-q' * τ) • x + Real.sqrt 2 • ouShift q' w τ := by
  funext x
  unfold flowMap
  rw [s67bd_pfZ_zero_drift hq hw hw0 x hτ]

lemma s67bd_gradient_norm (f : Euc d → ℝ) (y : Euc d) :
    ‖gradient f y‖ = ‖fderiv ℝ f y‖ := by
  unfold gradient
  exact LinearIsometryEquiv.norm_map _ _

theorem s67bd_ou_gradient {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : IsBrownianFiltration P ℱ W)
    (ν q : ℝ) (hν : 0 < ν) (hq : 0 < q)
    (u : Euc d → ℝ) (hu : MemCb 1 u) (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ x, ‖gradient u x‖ ≤ D) (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ 1 (sg P W (q / ν) (fun _ => 0) (ν * t) u) ∧
    ∀ x, ‖gradient (sg P W (q / ν) (fun _ => 0) (ν * t) u) x‖ ≤
      Real.exp (-q * t) * D := by
  have hq' : 0 < q / ν := div_pos hq hν
  have hτ : 0 ≤ ν * t := mul_nonneg hν.le ht
  have hW' := sgNoise_of_brownian hW
  have hexp : Real.exp (-(q / ν) * (ν * t)) = Real.exp (-q * t) := by
    congr 1; field_simp
  have hE1 : Real.exp (-q * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hE0 : 0 < Real.exp (-q * t) := Real.exp_pos _
  set phi : Ω → Euc d → Euc d := fun o =>
    flowMap (q / ν) (fun _ : Euc d => (0 : Euc d)) (fun s => W s o) (ν * t) with hphidef
  have hphi : ∀ o, phi o = fun x => Real.exp (-q * t) • x +
      Real.sqrt 2 • ouShift (q / ν) (fun s => W s o) (ν * t) := fun o => by
    rw [hphidef]
    simp only
    rw [s67bd_flowMap_zero_drift hq'.le (hW'.cont o) (hW'.zero o) hτ, hexp]
  have hphidiff : ∀ o, ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (phi o) := fun o => by
    rw [hphi o]
    exact (contDiff_id.const_smul _).add contDiff_const
  have hphifd : ∀ o x, ‖iteratedFDeriv ℝ 1 (phi o) x‖ ≤ Real.exp (-q * t) := fun o x => by
    rw [norm_iteratedFDeriv_one, hphi o]
    have hh : HasFDerivAt (fun x : Euc d => Real.exp (-q * t) • x +
        Real.sqrt 2 • ouShift (q / ν) (fun s => W s o) (ν * t))
        (Real.exp (-q * t) • ContinuousLinearMap.id ℝ (Euc d)) x :=
      ((hasFDerivAt_id x).const_smul (Real.exp (-q * t))).add_const
        (Real.sqrt 2 • ouShift (q / ν) (fun s => W s o) (ν * t))
    rw [hh.fderiv, norm_smul, Real.norm_of_nonneg hE0.le]
    calc Real.exp (-q * t) * ‖ContinuousLinearMap.id ℝ (Euc d)‖ ≤ Real.exp (-q * t) * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hE0.le
      _ = Real.exp (-q * t) := mul_one _
  obtain ⟨M0, hM0⟩ := hu.2 0 (Nat.zero_le _)
  have hM : ∀ i ≤ 1, ∀ y, ‖iteratedFDeriv ℝ i u y‖ ≤ max M0 D := by
    intro i hi y
    interval_cases i
    · exact (hM0 ⟨y, rfl⟩).trans (le_max_left _ _)
    · rw [norm_iteratedFDeriv_one, ← s67bd_gradient_norm]
      exact (hb y).trans (le_max_right _ _)
  obtain ⟨h1, h2, _⟩ := sg_family (P := P) (k := 1) (φ := phi)
    (sg_measurable_flowMap hW' hq'.le le_rfl (s67bd_zero_cb 1) hτ) hphidiff hu.1 hM (D := 1)
    le_rfl (fun o x j hj1 hj2 => by
      obtain rfl : j = 1 := le_antisymm hj2 hj1
      exact (hphifd o x).trans hE1)
  have hsg : sg P W (q / ν) (fun _ => (0 : Euc d)) (ν * t) u = fun x => ∫ o, u (phi o x) ∂P := rfl
  rw [hsg]
  refine ⟨by exact_mod_cast h1, fun x => ?_⟩
  have hpt : ∀ o, ‖iteratedFDeriv ℝ 1 (fun y => u (phi o y)) x‖ ≤ Real.exp (-q * t) * D := by
    intro o
    rw [norm_iteratedFDeriv_one]
    have hdh : DifferentiableAt ℝ u (phi o x) := (hu.1.differentiable (by norm_num)) _
    have hdf : DifferentiableAt ℝ (phi o) x := ((hphidiff o).differentiable (by norm_num)) x
    have e : fderiv ℝ (fun y => u (phi o y)) x = (fderiv ℝ u (phi o x)).comp (fderiv ℝ (phi o) x) :=
      fderiv_comp x hdh hdf
    rw [e]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [mul_comm]
    have hf1 : ‖fderiv ℝ (phi o) x‖ ≤ Real.exp (-q * t) := by
      rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]; exact hphifd o x
    have hf2 : ‖fderiv ℝ u (phi o x)‖ ≤ D := by
      rw [← s67bd_gradient_norm]; exact hb _
    exact mul_le_mul hf1 hf2 (norm_nonneg _) hE0.le
  rw [s67bd_gradient_norm, ← norm_iteratedFDeriv_one (𝕜 := ℝ), h2 1 le_rfl x]
  have := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun o => iteratedFDeriv ℝ 1 (fun y => u (phi o y)) x)
    (C := Real.exp (-q * t) * D) (Eventually.of_forall hpt)
  simpa using this

end HRS.MS.BreakdownS67
