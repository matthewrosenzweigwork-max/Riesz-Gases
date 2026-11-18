import HRS.MC.S7FCF5A1

/-!
# Block A3 of packet `fcf5`: joint measurability of the generator in `(u,x)`

Proof of `fcf5_A3_gen_meas` (`S7FCF5Plan.lean`).  The local part `β⁻¹ Δf(x) - ⟨∇V(x), ∇f(x)⟩` is continuous in `x`
(`s7fcw7_L0_cont`).  The interaction integral is rewritten, pointwise in `(u,x)`, as the integral against the Lebesgue
measure of the integrand `((u,x),y) ↦ ρ^{max u 0}(y) h_f(x,y)`, which is jointly measurable (`A1` gives joint continuity
of `(u,y) ↦ ρ^{max u 0}(y)`, `s7fcw7_hT_meas` the joint measurability of `h_f`); then
`StronglyMeasurable.integral_prod_right'` gives its measurability.  Namespace `HRS.MC.Sec7.S7FCF5A`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5A

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCW7

variable {d : ℕ}

/-- The generator is jointly measurable in `(u,x)` (proof of `fcf5_A3_gen_meas`). -/
theorem fcf5_A3_gen_meas_proof (R : Regime d) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    Measurable (fun p : ℝ × Torus d => fcGen R (max p.1 0) f p.2) := by
  have hL : Continuous (fun x : Torus d => R.D.invβ * Torus.laplacian f x -
      inner ℝ (Torus.grad R.D.V x) (Torus.grad f x)) := s7fcw7_L0_cont R hf
  obtain ⟨m₀, M₀, hm₀, hb⟩ := R.bounds
  have hρc : Continuous (fun q : ℝ × Torus d => R.ρ (max q.1 0) q.2) := by
    have hmap : Continuous (fun q : ℝ × Torus d => (max q.1 0, q.2)) :=
      (continuous_fst.max continuous_const).prodMk continuous_snd
    exact (fcf5_A1_rho_cont_proof R).comp_continuous hmap
      (fun q => ⟨Set.mem_Ici.2 (le_max_right _ _), Set.mem_univ _⟩)
  have hG1 : Measurable (fun z : (ℝ × Torus d) × Torus d => R.ρ (max z.1.1 0) z.2) :=
    hρc.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hT2 : Measurable (fun q : Torus d × Torus d => hTransport d R.D.s f q.1 q.2) :=
    s7fcw7_hT_meas (s7fcw7_sd R.hd R.hs) hf
  have hpair : Measurable (fun z : (ℝ × Torus d) × Torus d => (z.1.2, z.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hT2 : Measurable (fun q : Torus d × Torus d => hTransport d R.D.s f q.1 q.2) :=
    s7fcw7_hT_meas (s7fcw7_sd R.hd R.hs) hf
  have hG2 : Measurable (fun z : (ℝ × Torus d) × Torus d =>
      (fun q : Torus d × Torus d => hTransport d R.D.s f q.1 q.2) (z.1.2, z.2)) :=
    hT2.comp hpair
  have hF : StronglyMeasurable (fun z : (ℝ × Torus d) × Torus d =>
      R.ρ (max z.1.1 0) z.2 * (fun q : Torus d × Torus d => hTransport d R.D.s f q.1 q.2) (z.1.2, z.2)) :=
    (hG1.mul hG2).stronglyMeasurable
  have hJ : Measurable (fun p : ℝ × Torus d => ∫ y, R.ρ (max p.1 0) y * hTransport d R.D.s f p.2 y) :=
    (hF.integral_prod_right' (ν := volume)).measurable
  have hρ0 : ∀ u : ℝ, ∀ y, 0 ≤ R.ρ (max u 0) y := fun u y =>
    hm₀.le.trans (hb (max u 0) (le_max_right _ _) y).1
  have hEq : ∀ p : ℝ × Torus d,
      ∫ y, hTransport d R.D.s f p.2 y ∂(withDensityReal (R.ρ (max p.1 0))) =
        ∫ y, R.ρ (max p.1 0) y * hTransport d R.D.s f p.2 y :=
    fun p => HRS.PDE.MFPairing.integral_withDensityReal
      (S7FCF5A_rho_cont_x R (le_max_right _ _)).measurable (hρ0 p.1 ) (hTransport d R.D.s f p.2)
  have hfun : (fun p : ℝ × Torus d => fcGen R (max p.1 0) f p.2) = fun p : ℝ × Torus d =>
      (R.D.invβ * Torus.laplacian f p.2 - inner ℝ (Torus.grad R.D.V p.2) (Torus.grad f p.2)) -
        ∫ y, R.ρ (max p.1 0) y * hTransport d R.D.s f p.2 y := by
    funext p
    unfold fcGen
    rw [hEq p]
  rw [hfun]
  exact (hL.measurable.comp measurable_snd).sub hJ

end HRS.MC.Sec7.S7FCF5A

end
