import HRS.MS.SA12X3C6A

/-!
# S.A.12 C6 (SA12X3), part B: the Galilean shift of drift and flow

`Ψ'_σ x = Ψ_σ(x+c) - Ψ_σ c`, `b'_σ y = b_σ(y + Ψ_σ c) - b_σ(Ψ_σ c)`: again an advecting drift with its negative flow,
and `advCutoff χ Ψ' τ z' y = advCutoff χ Ψ τ (c+z') (y + Ψ_τ c)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

def sa12x3_Psi (Ψ : ℝ → Euc d → Euc d) (c : Euc d) (σ : ℝ) (x : Euc d) : Euc d :=
  Ψ σ (x + c) - Ψ σ c

def sa12x3_drift (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d) (c : Euc d) (σ : ℝ) (y : Euc d) : Euc d :=
  b σ (y + Ψ σ c) - b σ (Ψ σ c)

theorem sa12x3_flow {T : ℝ} {b : ℝ → Euc d → Euc d} {Ψ : ℝ → Euc d → Euc d} (hΨ : IsNegDriftFlow T b Ψ)
    (c : Euc d) : IsNegDriftFlow T (sa12x3_drift b Ψ c) (sa12x3_Psi Ψ c) := by
  refine ⟨fun x => ?_, fun x τ hτ => ?_, fun τ hτ => ?_⟩
  · simp [sa12x3_Psi, hΨ.init]
  · have h := (hΨ.ode (x + c) τ hτ).sub (hΨ.ode c τ hτ)
    refine h.congr_deriv ?_
    simp only [sa12x3_drift, sa12x3_Psi, sub_add_cancel]
    abel
  · have hb := hΨ.bij τ hτ
    have : sa12x3_Psi Ψ c τ = (fun y => y - Ψ τ c) ∘ (Ψ τ) ∘ (fun x => x + c) := rfl
    rw [this]
    exact ((Equiv.subRight (Ψ τ c)).bijective.comp hb).comp (Equiv.addRight c).bijective

theorem sa12x3_drift_adv {m : ℕ} {Cb T : ℝ} {b : ℝ → Euc d → Euc d} {Ψ : ℝ → Euc d → Euc d}
    (hb : IsAdvectingDrift m Cb T b) (hΨ : IsNegDriftFlow T b Ψ) (c : Euc d) :
    IsAdvectingDrift m Cb T (sa12x3_drift b Ψ c) := by
  have hcontΨ : ContinuousOn (fun σ => Ψ σ c) (Icc 0 T) := fun σ hσ => (hΨ.ode c σ hσ).continuousWithinAt
  refine ⟨?_, fun τ hτ => ?_, fun τ hτ j hj1 hjm x => ?_, fun τ hτ x => ?_⟩
  · have hg1 : ContinuousOn (fun p : ℝ × Euc d => (p.1, p.2 + Ψ p.1 c)) (Icc 0 T ×ˢ univ) :=
      continuousOn_fst.prodMk (continuousOn_snd.add (hcontΨ.comp continuousOn_fst
        (fun p hp => hp.1)))
    have hg2 : ContinuousOn (fun p : ℝ × Euc d => (p.1, Ψ p.1 c)) (Icc 0 T ×ˢ univ) :=
      continuousOn_fst.prodMk (hcontΨ.comp continuousOn_fst (fun p hp => hp.1))
    have h1 := hb.cont.comp hg1 (fun p hp => ⟨hp.1, mem_univ _⟩)
    have h2 := hb.cont.comp hg2 (fun p hp => ⟨hp.1, mem_univ _⟩)
    exact h1.sub h2
  · exact ((hb.smooth τ hτ).comp (contDiff_id.add contDiff_const)).sub contDiff_const
  · have hs := hb.smooth τ hτ
    have hf : ContDiff ℝ (m + 1) (fun y => b τ (y + Ψ τ c)) := hs.comp (contDiff_id.add contDiff_const)
    have e : sa12x3_drift b Ψ c τ = (fun y => b τ (y + Ψ τ c)) - fun _ => b τ (Ψ τ c) := rfl
    have hfj : ContDiff ℝ j (fun y => b τ (y + Ψ τ c)) := hf.of_le (by exact_mod_cast hjm)
    rw [e, iteratedFDeriv_sub_apply (hfj.contDiffAt) contDiff_const.contDiffAt,
      iteratedFDeriv_const_of_ne (by omega), iteratedFDeriv_comp_add_right]
    simpa using hb.deriv_bdd τ hτ j hj1 hjm (x + Ψ τ c)
  · have hs := hb.smooth τ hτ
    have hdiff : Differentiable ℝ (b τ) := hs.differentiable (by exact_mod_cast Nat.succ_ne_zero m)
    have hfd : ∀ z, ‖fderiv ℝ (b τ) z‖ ≤ Cb := fun z => by
      rw [← norm_iteratedFDeriv_one]
      exact hb.deriv_bdd τ hτ 1 le_rfl (by omega) z
    have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hfd 0)
    have hmv := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
      (f := b τ) (C := Cb) (fun z _ => hdiff z) (fun z _ => hfd z) (mem_univ (Ψ τ c))
      (mem_univ (x + Ψ τ c))
    have : ‖b τ (x + Ψ τ c) - b τ (Ψ τ c)‖ ≤ Cb * ‖x‖ := by
      simpa using hmv
    show ‖b τ (x + Ψ τ c) - b τ (Ψ τ c)‖ ≤ _
    nlinarith [this, hCb]

theorem sa12x3_invFun_shift {T : ℝ} {b : ℝ → Euc d → Euc d} {Ψ : ℝ → Euc d → Euc d} (hΨ : IsNegDriftFlow T b Ψ)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (c y : Euc d) :
    Function.invFun (sa12x3_Psi Ψ c τ) y = Function.invFun (Ψ τ) (y + Ψ τ c) - c := by
  have hbij := hΨ.bij τ hτ
  have hinj : Function.Injective (sa12x3_Psi Ψ c τ) := by
    have : sa12x3_Psi Ψ c τ = (fun y => y - Ψ τ c) ∘ (Ψ τ) ∘ (fun x => x + c) := rfl
    rw [this]
    exact ((Equiv.subRight (Ψ τ c)).injective.comp hbij.1).comp (Equiv.addRight c).injective
  apply hinj
  have hsurj : ∃ a, sa12x3_Psi Ψ c τ a = y := by
    obtain ⟨u, hu⟩ := hbij.2 (y + Ψ τ c)
    exact ⟨u - c, by simp [sa12x3_Psi, hu]⟩
  rw [Function.invFun_eq hsurj]
  simp only [sa12x3_Psi, sub_add_cancel]
  rw [Function.invFun_eq (hbij.2 (y + Ψ τ c))]
  abel

theorem sa12x3_adv_shift {T : ℝ} {b : ℝ → Euc d → Euc d} {Ψ : ℝ → Euc d → Euc d} (hΨ : IsNegDriftFlow T b Ψ)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (χ : Euc d → ℝ) (c z' y : Euc d) :
    advCutoff χ (sa12x3_Psi Ψ c) τ z' y = advCutoff χ Ψ τ (c + z') (y + Ψ τ c) := by
  unfold advCutoff
  rw [sa12x3_invFun_shift hΨ hτ]
  congr 1
  abel

end HRS.MH.AdjointRd.Phase2SA12Construction
