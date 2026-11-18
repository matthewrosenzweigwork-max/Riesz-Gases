import HRS.MC.E213U16d
import HRS.MC.L2C5Aux2
import HRS.MC.L2C3
import HRS.Main.GFEVMAux1

/-!
# Packet e213u16, file e: propagator cocycle, duality, Fourier coefficients of `V`, kernel integrability

* `u16_cocycle`: `U^{r,t}φ = U^{r,σ}U^{σ,t}φ` for smooth `φ`, `0 ≤ r ≤ σ < t`;
* `u16_V_eval`: `⟨V^{t,u}F, φ⟩ = ⟨F, U^{u,t}φ⟩` (restatement of `s7_PIS_V_eval_proof` with the horizon free);
* `u16_kernel_integrableOn`: the covariance kernel `r ↦ ∫ ∇U^{r,ta}φ_a·∇U^{r,tb}φ_b ρ_r` is integrable on `[0,ta∧tb]`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan

variable {d : ℕ}

section Propag

theorem u16_cocycle (R : Regime d) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {r σ t : ℝ} (hr : 0 ≤ r)
    (hrσ : r ≤ σ) (hσt : σ < t) :
    propagator R.D R.ρ r t φ = propagator R.D R.ρ r σ (propagator R.D R.ρ σ t φ) := by
  have ht : 0 < t := lt_of_le_of_lt (hr.trans hrσ) hσt
  have H := HRS.MC.Sec7.S7PIS1.S7PIS1_hyp R t ht (HRS.PDE.mStar d) le_rfl
  exact HRS.MC.Sec7.PIE.pie_prop_semigroup H ⟨ht, le_rfl⟩ (HRS.A33.dom_smooth hφ) hr hrσ hσt

theorem u16_V_eval (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t)
    (F : NegSobolev d m) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    NegSobolev.eval (Vprop R.D R.ρ m t u F) φ = NegSobolev.eval F (propagator R.D R.ρ u t φ) :=
  HRS.MC.Sec7.S7PIS1.s7_PIS_V_eval_proof R m hm (max t 1) (lt_of_lt_of_le one_pos (le_max_right _ _)) u t hu hut
    (le_max_left _ _) F φ hφ

end Propag

section Kernel

theorem u16_rho_cont' (R : Regime d) (t : ℝ) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => R.ρ p.1 p.2 :=
  (HRS.MC.L2C5.l2c5_rho_cont R t).comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    (fun p => ⟨p.1.2, Set.mem_univ _⟩)

theorem u16_kernel_cont (R : Regime d) {φa φb : Torus d → ℝ} (hφa : Torus.IsSmooth φa) (hφb : Torus.IsSmooth φb)
    {ta tb : ℝ} (hta : 0 < ta) (htb : 0 < tb) :
    ContinuousOn (fun r => ∫ x, inner ℝ (Torus.grad (propagator R.D R.ρ r ta φa) x)
      (Torus.grad (propagator R.D R.ρ r tb φb) x) * R.ρ r x) (Set.Icc 0 (min ta tb)) := by
  obtain ⟨F, hF, hFp⟩ := HRS.MC.L2C3.l2c3_classical R hta hφa
  obtain ⟨G, hG, hGp⟩ := HRS.MC.L2C3.l2c3_classical R htb hφb
  have hs0 : 0 ≤ min ta tb := le_min hta.le htb.le
  have hF' := HRS.GF.gfm_restrict hF (r := min ta tb) ⟨hs0, min_le_left _ _⟩
  have hG' := HRS.GF.gfm_restrict hG (r := min ta tb) ⟨hs0, min_le_right _ _⟩
  have hc := HRS.MC.L2C5.l2c5_cross_cont hF' hG' (w := fun v x => R.ρ v x)
    (u16_rho_cont' R (min ta tb))
  refine hc.congr fun r hr => ?_
  have h1 : r ∈ Set.Icc 0 ta := ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have h2 : r ∈ Set.Icc 0 tb := ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
  simp only [hFp r h1, hGp r h2]

theorem u16_kernel_integrableOn (R : Regime d) {φa φb : Torus d → ℝ} (hφa : Torus.IsSmooth φa)
    (hφb : Torus.IsSmooth φb) {ta tb : ℝ} (hta : 0 ≤ ta) (htb : 0 ≤ tb) :
    IntegrableOn (fun r => ∫ x, inner ℝ (Torus.grad (propagator R.D R.ρ r ta φa) x)
      (Torus.grad (propagator R.D R.ρ r tb φb) x) * R.ρ r x) (Set.Icc 0 (min ta tb)) := by
  by_cases h : 0 < min ta tb
  · exact (u16_kernel_cont R hφa hφb (lt_min_iff.1 h).1 (lt_min_iff.1 h).2).integrableOn_Icc
  · have h0 : min ta tb = 0 := le_antisymm (not_lt.1 h) (le_min hta htb)
    rw [h0]
    have : volume.restrict (Set.Icc (0 : ℝ) 0) = 0 := Measure.restrict_eq_zero.2 (by simp)
    unfold IntegrableOn
    rw [this]
    exact integrable_zero_measure

end Kernel

end HRS.MC.E213U16

end
