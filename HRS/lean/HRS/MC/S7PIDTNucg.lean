import HRS.MC.S7PIDTNuc
import HRS.MC.S7PIDTPhi
import HRS.MC.S7PIDTVec

/-!
# Packet PI-D, sub-packet T (part 12): `nuc` of the truncated kernel nodes as an integral over the coordinate families
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDT

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

theorem S7PIDT_nucg (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (c c' : ℝ) (hc : 0 ≤ c) (hlt : c < c') (hc' : c' ≤ T) (F : Finset (NonzeroLattice d))
    {r : ℕ} (emb : EuclideanSpace ℝ (Fin r) →L[ℝ] NegSobolev d m) (G : NegSobolev d m → EuclideanSpace ℝ (Fin r))
    (hembG : ∀ a, emb (G a) = truncF m F a) (hGc : Continuous G) 
    (p q : ℝ → ℝ) (e e' : NegSobolev d m) (b : ℝ)
    (hmeas : ∀ ν i, i ≤ 2 ^ ν → AEStronglyMeasurable (fun u => kernelNodes R.D R.ρ m c c' ν p e u i)
      (volume.restrict (Set.Ioc c c')))
    (hmeas' : ∀ ν i, i ≤ 2 ^ ν → AEStronglyMeasurable (fun u => kernelNodes R.D R.ρ m c c' ν q e' u i)
      (volume.restrict (Set.Ioc c c')))
    (hbd : ∀ ν i, i ≤ 2 ^ ν → ∀ u ∈ Set.Ioc c c', ‖kernelNodes R.D R.ρ m c c' ν p e u i‖ ≤ b)
    (hbd' : ∀ ν i, i ≤ 2 ^ ν → ∀ u ∈ Set.Ioc c c', ‖kernelNodes R.D R.ρ m c c' ν q e' u i‖ ≤ b)
    (ν μ : ℕ) (τ : ℕ → ℕ) (hτ : ∀ j ≤ 2 ^ μ, τ j ≤ 2 ^ ν)
    (Φ : (Fin (2 ^ μ + 1) → NegSobolev d m) →L[ℝ] PathSpace d m T)
    (hΦ : ∀ v : ℕ → NegSobolev d m, polyPath R.D R.ρ m T c c' μ v = Φ (fun i => v i.1))
    (M : PathSpace d m T [×2]→L[ℝ] ℝ) :
    nuc R.D R.ρ m T c c' μ
        (fun u i => truncF m F (kernelNodes R.D R.ρ m c c' ν p e u (τ i)))
        (fun u i => truncF m F (kernelNodes R.D R.ρ m c c' ν q e' u (τ i))) M =
      ∫ u in Set.Ioc c c', M ![Φ (fun j => emb (G (kernelNodes R.D R.ρ m c c' ν p e u (τ j.1)))),
        Φ (fun j => emb (G (kernelNodes R.D R.ρ m c c' ν q e' u (τ j.1))))] := by
  have hlip : LipschitzWith 1 (fun a : NegSobolev d m => truncF m F a) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
      exact S7PIDT_trunc_sub_le m F a b
  rw [S7PIDT_nuc_apply R m hm T hT c c' hc hlt.le hc' μ _ _ b
    (fun i hi => hlip.continuous.comp_aestronglyMeasurable (hmeas ν (τ i) (hτ i hi)))
    (fun i hi => hlip.continuous.comp_aestronglyMeasurable (hmeas' ν (τ i) (hτ i hi)))
    (fun i hi => (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu =>
      (S7PIDT_trunc_norm_le m F _).trans (hbd ν (τ i) (hτ i hi) u hu)))
    (fun i hi => (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu =>
      (S7PIDT_trunc_norm_le m F _).trans (hbd' ν (τ i) (hτ i hi) u hu))) M]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show M ![polyPath R.D R.ρ m T c c' μ _, polyPath R.D R.ρ m T c c' μ _] = _
  rw [hΦ, hΦ]
  simp only [hembG]

end HRS.MC.Sec7.S7PIDT

end
