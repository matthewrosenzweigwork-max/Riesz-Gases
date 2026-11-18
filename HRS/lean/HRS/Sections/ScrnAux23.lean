import HRS.Sections.ScrnAux22
import HRS.Main.GFSpec1
import HRS.Stochastic.DualityProof

/-!
# Packet SCRN, part 23: the time-zero transported test and the one-test duality identity

* `scrn_isC12Test_zero`: the constant-in-time datum `r ↦ ψ` is an `IsC12Test` on `[0,0]`.
* `scrn_dual_one`: for a test with terminal time `t_a ≥ 0` carried by a classical adjoint solution
  (`t_a > 0`) or the constant datum (`t_a = 0`), the duality identity with `ρ ≡ 1` and `V = 0`:
  `⟨ψ, ρ_N^{t_a}⟩ = ⟨f^0, ρ_N^0⟩ + M_N^{t_a}[f] + ∫_0^{t_a} flucInteraction(f^r, X^r) dr`, a.s.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d : ℕ}

theorem scrn_isC12Test_zero {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    IsC12Test 0 (fun _ => ψ) (fun _ _ => (0 : ℝ)) := by
  refine ⟨fun r _ => hψ, fun j hj => ?_, fun x r hr => ?_, continuous_const⟩
  · have hc : ContDiff ℝ 2 (Torus.lift ψ) := hψ
    have := (hc.continuous_iteratedFDeriv (by exact_mod_cast hj : (j : WithTop ℕ∞) ≤ 2))
    exact this.comp continuous_snd
  · exfalso
    exact absurd hr.2 (not_lt.2 hr.1.le)

/-- The duality identity for one test, `ρ ≡ 1`, `V = 0` (the `t = 0` case included). -/
theorem scrn_dual_one (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} {ℱ : MeasureTheory.Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsFilteredSolution P ℱ W' W X) {T : ℝ}
    (hsolT : IsStrongSolution P (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) T X₀ W X)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) {ψ : Torus d → ℝ} (hψ2 : Torus.IsCk 2 ψ)
    {f : ℝ → Torus d → ℝ}
    (hf : (t = 0 ∧ f = fun _ => ψ) ∨ (0 < t ∧ IsClassicalAdjointSolution
      (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (fun _ _ => (1 : ℝ)) t ψ f)) :
    ∀ᵐ ω ∂P,
      flucPair (X (Real.toNNReal t) ω) (fun _ => (1 : ℝ)) ψ =
        flucPair (X 0 ω) (fun _ => (1 : ℝ)) (f 0) +
        empiricalMartingale P ℱ W' (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) t f X
          ((Real.toNNReal t : ℝ≥0) : ℝ) ω +
        ∫ r in (0 : ℝ)..t, flucInteraction (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (f r)
          (X (Real.toNNReal r) ω) (fun _ => (1 : ℝ)) := by
  set D := PDE.mfData d s hs0 hsd (fun _ => 0) β hβ with hD
  rcases hf with ⟨h0, hfc⟩ | ⟨hpos, hcl⟩
  · subst h0
    subst hfc
    refine Filter.Eventually.of_forall fun ω => ?_
    have hm : empiricalMartingale P ℱ W' D 0 (fun _ => ψ) X ((Real.toNNReal 0 : ℝ≥0) : ℝ) ω = 0 := by
      unfold empiricalMartingale
      exact itoIntegral_of_nonpos P ℱ W' _ (by simp) ω
    rw [hm, intervalIntegral.integral_same]
    simp
  · have hd1 : 1 ≤ d := by omega
    have hV : Torus.IsCk 2 D.V := by
      show Torus.IsCk 2 (fun _ : Torus d => (0 : ℝ))
      unfold Torus.IsCk Torus.lift; exact contDiff_const
    have hρ := scrn_isMeanFieldSolution_one hd1 D rfl T
    have hreg : IsRegularMF (d := d) 3 (Torus.cbNorm 3 (fun _ : Torus d => (1 : ℝ))) T (fun _ _ => (1 : ℝ)) := by
      intro r hr
      refine ⟨?_, le_rfl⟩
      unfold Torus.IsCk Torus.lift; exact contDiff_const
    have hocc : D.M = 0 ∨ NullContactOccupation P T X := Or.inr (HRS.GF.nullContactOccupation_of_strong hsolT)
    have : NeZero N := ⟨by omega⟩
    have hall := (duality_identity_all hd1 hN hV hρ hreg hsolT.toContact hF hocc
      (t := t) ⟨hpos, ht.2⟩ hψ2 hcl).2
    filter_upwards [hall] with ω hω
    have h := (hω t ⟨hpos.le, le_rfl⟩).2
    have hterm : f t = ψ := hcl.terminal
    simp only [hterm] at h
    exact h

end HRS
