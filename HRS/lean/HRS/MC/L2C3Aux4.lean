import HRS.MC.L2C3Aux3
import HRS.MC.L2C1

/-!
# Packet L2C-3, helper 4: the fixed-time Lyapunov inequality

For the centered, forced path `v = P_β ũ - S` (`ũ` a solution of the backward equation along `ρ^s`, `S` a solution of
the frozen equation) the derivative of `⟨y, A_β⁻¹ y⟩` is `2⟨A_β⁻¹ y, y'⟩` with
`y' = P_β(𝓛_s ũ) - (-A_β L_β) S`.  `l2c3_ft` evaluates this pairing:
`⟨A⁻¹ y, y'⟩ ≤ -ν ∫ρ_β|∇v|² + M ‖A⁻¹‖ ‖y‖` where `M` is the form bound of the generator perturbation.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

namespace HRS.MC.L2C3

variable {d : ℕ}

theorem l2c3_isCk_of_smooth {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (n : ℕ) :
    Torus.IsCk (n : WithTop ℕ∞) f :=
  MFSemigroup.isCk_nat_of_isSmooth hf n

theorem l2c3_integrable {μ : Measure (Torus d)} [IsFiniteMeasure μ] {f : Torus d → ℝ}
    (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- `Q_β 𝓛_β = -A_β L_β` for the regime. -/
theorem l2c3_op_order (R : Regime d) {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) :
    projMean (withDensityReal R.ρβ) (backwardGenerator R.D R.ρβ f) =
      equilibriumGen d R.D.s R.ρβ R.β⁻¹ f := by
  have hd1 : 1 ≤ d := by have := R.hd; omega
  have hD := HRS.MC.L2C1.l2c1_dyn_eq R
  obtain ⟨hth, hsm, hpos⟩ := R.thermal
  rw [hD]
  exact equilibrium_operator_order hd1 R.D.s R.D.hs0 R.D.hsd R.β R.hβ R.D.V
    (l2c3_isCk_of_smooth R.hV 2) R.ρβ hth (l2c3_isCk_of_smooth hsm 2) hpos f hf

theorem l2c3_bg_cont (R : Regime d) {ρ f : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (hf : Torus.IsCk 2 f) :
    Continuous (backwardGenerator R.D ρ f) := by
  have hd1 : 1 ≤ d := by have := R.hd; omega
  exact MFSemigroup.continuous_backwardGenerator R.D (ClassicalAux.convKernelFacts hd1 R.D)
    (l2c3_isCk_of_smooth R.hV 1) hρ hf

theorem l2c3_eqGen_cont (R : Regime d) {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) :
    Continuous (equilibriumGen d R.D.s R.ρβ R.β⁻¹ f) := by
  rw [← l2c3_op_order R hf]
  have hc := l2c3_bg_cont R (l2c3_isCk_of_smooth R.thermal.2.1 1) hf
  exact hc.sub continuous_const

theorem l2c3_pair_add {μ : Measure (Torus d)} [IsFiniteMeasure μ] {A B : Torus d → ℝ}
    (hA : Continuous A) (hB : Continuous B) :
    pair μ (fun x => A x + B x) = pair μ A + pair μ B := by
  unfold pair
  exact integral_add (l2c3_integrable hA) (l2c3_integrable hB)

theorem l2c3_ft {R : Regime d} (Cx : Ctx R) {s : ℝ} (hs : 0 ≤ s) {f g : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (hg : Torus.IsCk 2 g) (hg0 : pair (withDensityReal R.ρβ) g = 0)
    (y u' e : Lp ℝ 2 (withDensityReal R.ρβ)) {M : ℝ} (hM0 : 0 ≤ M)
    (hy : ⇑y =ᵐ[withDensityReal R.ρβ] fun x => projMean (withDensityReal R.ρβ) f x - g x)
    (hu' : ⇑u' =ᵐ[withDensityReal R.ρβ] fun x =>
      projMean (withDensityReal R.ρβ) (backwardGenerator R.D (R.ρ s) f) x -
        equilibriumGen d R.D.s R.ρβ R.β⁻¹ g x)
    (he : ⇑e =ᵐ[withDensityReal R.ρβ] fun x =>
      backwardGenerator R.D (R.ρ s) f x - backwardGenerator R.D R.ρβ f x)
    (hM : ∀ w : Lp ℝ 2 (withDensityReal R.ρβ), |inner ℝ e w| ≤ M * ‖w‖) :
    inner ℝ (Cx.Rop y) u' ≤
      -R.β⁻¹ * (∫ x, R.ρβ x * ‖Torus.grad (fun x => projMean (withDensityReal R.ρβ) f x - g x) x‖ ^ 2) +
        M * ‖Cx.Rop‖ * ‖y‖ := by
  obtain ⟨hth, hsm, hpos⟩ := R.thermal
  have hf1 : Torus.IsCk 1 f := l2c3_isCk_of_smooth hf 1
  have hf2 : Torus.IsCk 2 f := l2c3_isCk_of_smooth hf 2
  have hg1 : Torus.IsCk 1 g := hg.of_le (by norm_num)
  have hρ1 : Torus.IsCk 1 R.ρβ := l2c3_isCk_of_smooth hsm 1
  have hβ : 0 < R.β := R.hβ
  obtain ⟨Λ, hΛ⟩ := HRS.MC.RegSet.reg_proof R 1
  have hρs : Torus.IsCk 1 (R.ρ s) := (hΛ s s ⟨hs, le_rfl⟩).1
  have cLs := l2c3_bg_cont R hρs hf2
  have cLb := l2c3_bg_cont R hρ1 hf2
  set pert : Torus d → ℝ := fun x => backwardGenerator R.D (R.ρ s) f x - backwardGenerator R.D R.ρβ f x
    with hpert
  have cpert : Continuous pert := cLs.sub cLb
  set m : ℝ := pair (withDensityReal R.ρβ) pert with hm
  -- the classes of `eqGen f`, `eqGen g`
  have cEf := l2c3_eqGen_cont R hf2
  have cEg := l2c3_eqGen_cont R hg
  set a : Lp ℝ 2 (withDensityReal R.ρβ) := (cEf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).toLp _
    with ha
  set b : Lp ℝ 2 (withDensityReal R.ρβ) := (cEg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).toLp _
    with hb
  have haae : ⇑a =ᵐ[(withDensityReal R.ρβ)] equilibriumGen d R.D.s R.ρβ R.β⁻¹ f := MemLp.coeFn_toLp _
  have hbae : ⇑b =ᵐ[(withDensityReal R.ρβ)] equilibriumGen d R.D.s R.ρβ R.β⁻¹ g := MemLp.coeFn_toLp _
  -- pointwise decomposition of the centered generator
  have hsplit : ∀ x, projMean (withDensityReal R.ρβ) (backwardGenerator R.D (R.ρ s) f) x =
      equilibriumGen d R.D.s R.ρβ R.β⁻¹ f x + (pert x - m) := by
    intro x
    have h1 : backwardGenerator R.D (R.ρ s) f = fun x => backwardGenerator R.D R.ρβ f x + pert x := by
      funext x; simp only [hpert]; ring
    have h2 := l2c3_pair_add (μ := withDensityReal R.ρβ) cLb cpert
    have h3 := congrFun (l2c3_op_order R hf2) x
    unfold projMean at h3 ⊢
    rw [h1, h2]
    simp only [pair] at h3 ⊢
    rw [← h3]
    simp only [hm, pair]
    ring
  have hu'eq : u' = a - b + e - m • l2c3_one (withDensityReal R.ρβ) := by
    refine Lp.ext ?_
    filter_upwards [hu', haae, hbae, he, l2c3_one_ae (withDensityReal R.ρβ),
      Lp.coeFn_sub (a - b + e) (m • l2c3_one (withDensityReal R.ρβ)), Lp.coeFn_add (a - b) e, Lp.coeFn_sub a b,
      Lp.coeFn_smul m (l2c3_one (withDensityReal R.ρβ))] with x h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [h6]
    simp only [Pi.sub_apply]
    rw [h7]
    simp only [Pi.add_apply]
    rw [h8, h9]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1, h2, h3, h4, h5, hsplit x]
    ring
  rw [hu'eq, inner_sub_right, inner_add_right, inner_sub_right, real_inner_smul_right]
  -- the two energy terms
  have hv1 : Torus.IsCk 1 (fun x => projMean (withDensityReal R.ρβ) f x - g x) :=
    (isCk_sub_const hf1 _).sub hg1
  have hgv : ∀ x, Torus.grad (fun x => projMean (withDensityReal R.ρβ) f x - g x) x = Torus.grad f x - Torus.grad g x := by
    intro x
    have h1 : Torus.IsCk 1 (projMean (withDensityReal R.ρβ) f) := isCk_sub_const hf1 _
    rw [grad_sub h1 hg1, MFSemigroup.grad_projMean]
  have T1 : inner ℝ (Cx.Rop y) a =
      -R.β⁻¹ * ∫ x, R.ρβ x * inner ℝ (Torus.grad f x)
        (Torus.grad (fun x => projMean (withDensityReal R.ρβ) f x - g x) x) := by
    rw [Cx.hRs, ← inner_R_eqGen R.D.s Cx.hKS R.β hβ hρ1 hpos Cx.Rop Cx.hRA' hf2 hv1 a y haae hy]
  have T2 : inner ℝ (Cx.Rop y) b =
      -R.β⁻¹ * ∫ x, R.ρβ x * inner ℝ (Torus.grad g x)
        (Torus.grad (fun x => projMean (withDensityReal R.ρβ) f x - g x) x) := by
    rw [Cx.hRs, ← inner_R_eqGen R.D.s Cx.hKS R.β hβ hρ1 hpos Cx.Rop Cx.hRA' hg hv1 b y hbae hy]
  have hgc : Continuous (Torus.grad (fun x => projMean (withDensityReal R.ρβ) f x - g x)) := continuous_grad hv1
  have hfc : Continuous (Torus.grad f) := continuous_grad hf1
  have hgc' : Continuous (Torus.grad g) := continuous_grad hg1
  have cρ := Cx.hρc
  have T12 : inner ℝ (Cx.Rop y) a - inner ℝ (Cx.Rop y) b =
      -R.β⁻¹ * ∫ x, R.ρβ x * ‖Torus.grad (fun x => projMean (withDensityReal R.ρβ) f x - g x) x‖ ^ 2 := by
    rw [T1, T2, ← mul_sub, ← integral_sub]
    · congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [← mul_sub, ← inner_sub_left, ← hgv x, real_inner_self_eq_norm_sq]
    · exact l2c3_integrable (cρ.mul (hfc.inner hgc))
    · exact l2c3_integrable (cρ.mul (hgc'.inner hgc))
  -- the perturbation term
  have T3 : inner ℝ (Cx.Rop y) e ≤ M * ‖Cx.Rop‖ * ‖y‖ := by
    rw [real_inner_comm]
    calc inner ℝ e (Cx.Rop y) ≤ |inner ℝ e (Cx.Rop y)| := le_abs_self _
      _ ≤ M * ‖Cx.Rop y‖ := hM _
      _ ≤ M * (‖Cx.Rop‖ * ‖y‖) := mul_le_mul_of_nonneg_left (Cx.Rop.le_opNorm y) hM0
      _ = M * ‖Cx.Rop‖ * ‖y‖ := by ring
  -- the mean term vanishes
  have T4 : inner ℝ (Cx.Rop y) (l2c3_one (withDensityReal R.ρβ)) = 0 := by
    rw [real_inner_comm, l2c3_inner_one_Rop Cx y, l2c3_inner_one]
    have : ∫ x, y x ∂(withDensityReal R.ρβ) = ∫ x, (projMean (withDensityReal R.ρβ) f x - g x) ∂(withDensityReal R.ρβ) := integral_congr_ae hy
    rw [this]
    have hc1 : Continuous (projMean (withDensityReal R.ρβ) f) := (isCk_sub_const hf1 _ |> fun h => MFAux.continuous_of_isCk h)
    have hc2 : Continuous g := MFAux.continuous_of_isCk hg1
    rw [integral_sub (l2c3_integrable hc1) (l2c3_integrable hc2)]
    have := MFSemigroup.pair_projMean (withDensityReal R.ρβ) f
    unfold pair at this hg0
    rw [this, hg0]; ring
  rw [T4, mul_zero, sub_zero]
  linarith [T12, T3]

end HRS.MC.L2C3
