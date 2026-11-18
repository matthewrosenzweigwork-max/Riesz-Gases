import HRS.MS.SA16RDuh1

/-!
# S.A.16 (SA16R) Duh2: the weak (integrated) equation of the Duhamel solution

`sa16r_ell hψ`: the pairing `G ↦ ∫ (zeroth component of G) ψ` on `WmpSpace d k p` for `ψ ∈ C_c^∞`.
`SA16RHeatWeak`: the weak heat identities for the gain operator and the free term (to be proved from `∂_a g_a = Δ g_a`:
packet P5b); `sa16r_fixedn_weak`: under them the Duhamel solution satisfies
`⟨u(τ),ψ⟩ = ⟨φ,ψ⟩ + ∫_0^τ (ν⟨u(r),χ⟩ + ⟨K_r u(r), ψ⟩) dr`, `χ = Δψ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Duh2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the pairing with a test function `ψ ∈ C_c^∞` -/
def sa16r_ell (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    WmpSpace d k p →L[ℝ] ℝ :=
  (sa16s_pair d k p (wZero d k) hψ.1.continuous hψ.2).comp (WmpSpace d k p).subtypeL

lemma sa16r_ell_apply {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (k : ℕ) (G : WmpSpace d k p) :
    sa16r_ell d k p hψ G = ∫ x, wrep d k p G x * ψ x := by
  unfold sa16r_ell
  rw [ContinuousLinearMap.comp_apply, sa16s_pair_apply]
  rfl

/-- the weak heat identities for `Γ_{νs}` and for the free term `e^{ντΔ}φ`, tested against `ψ`, with `χ = Δψ` -/
def SA16RHeatWeak (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] (ν T : ℝ) {ψ χ : Euc d → ℝ} (hψ : IsCcInfty ψ)
    (hχ : IsCcInfty χ) : Prop :=
  (∀ (y : WmpSpace d k p), ∀ s ∈ Ioc (0 : ℝ) T,
      sa16r_ell d (k + 1) p hψ (sa16r_GamT d k p ν s y) =
        sa16r_ell d k p hψ y + ∫ σ in (0 : ℝ)..s, ν * sa16r_ell d (k + 1) p hχ (sa16r_GamT d k p ν σ y)) ∧
  (∀ (φ : WmpSpace d (k + 1) p), ∀ τ ∈ Icc (0 : ℝ) T,
      sa16r_ell d (k + 1) p hψ (sa16r_f0 d k p ν φ τ) =
        sa16r_ell d (k + 1) p hψ φ + ∫ σ in (0 : ℝ)..τ, ν * sa16r_ell d (k + 1) p hχ (sa16r_f0 d k p ν φ σ))

/-- **The weak equation of the mild solution.** -/
theorem sa16r_fixedn_weak {ν T B : ℝ} (hν : 0 < ν) (hT : 0 < T) (hB : 0 ≤ B) (k : ℕ)
    (K : ℝ → WmpSpace d (k + 1) p →L[ℝ] WmpSpace d k p)
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ B)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) (φ : WmpSpace d (k + 1) p)
    {ψ χ : Euc d → ℝ} (hψ : IsCcInfty ψ) (hχ : IsCcInfty χ) (hHW : SA16RHeatWeak d k p ν T hψ hχ)
    {u : ℝ → WmpSpace d (k + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d k p ν φ τ +
      voltOp (gainKer (sa16r_GamT d k p ν) K) u τ) :
    ∀ τ ∈ Icc (0 : ℝ) T, sa16r_ell d (k + 1) p hψ (u τ) = sa16r_ell d (k + 1) p hψ φ +
      ∫ r in (0 : ℝ)..τ, (ν * sa16r_ell d (k + 1) p hχ (u r) + sa16r_ell d k p hψ (K r (u r))) := by
  have h := sa16r_gainData hν k K hKb hKc
  have hC := sa16r_Cgam_nonneg d hν T
  have hE := sa16r_volt_weak h hC hB hT (sa16r_f0_cont hν k φ) hu hsol
    (sa16r_ell d (k + 1) p hψ) (ν • sa16r_ell d (k + 1) p hχ) (sa16r_ell d k p hψ)
    (sa16r_ell d (k + 1) p hψ φ)
    (fun y s hs => by simpa [ContinuousLinearMap.smul_apply] using hHW.1 y s hs)
    (fun τ hτ => by simpa [ContinuousLinearMap.smul_apply] using hHW.2 φ τ hτ)
  intro τ hτ
  simpa [ContinuousLinearMap.smul_apply] using hE τ hτ

lemma sa16r_ell_iota {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (k : ℕ) (G : WmpSpace d (k + 1) p) :
    sa16r_ell d k p hψ (sa16r_iota d k p G) = sa16r_ell d (k + 1) p hψ G := by
  rw [sa16r_ell_apply, sa16r_ell_apply]
  refine integral_congr_ae ?_
  filter_upwards [sa16r_iota_wrep (p := p) k G] with x hx
  rw [hx]

/-- the free-term identity follows from the gain-operator identity -/
theorem SA16RHeatWeak.of_first {ν T : ℝ} (k : ℕ) {ψ χ : Euc d → ℝ} (hψ : IsCcInfty ψ) (hχ : IsCcInfty χ)
    (h1 : ∀ (y : WmpSpace d k p), ∀ s ∈ Ioc (0 : ℝ) T,
      sa16r_ell d (k + 1) p hψ (sa16r_GamT d k p ν s y) =
        sa16r_ell d k p hψ y + ∫ σ in (0 : ℝ)..s, ν * sa16r_ell d (k + 1) p hχ (sa16r_GamT d k p ν σ y)) :
    SA16RHeatWeak d k p ν T hψ hχ := by
  refine ⟨h1, fun φ τ hτ => ?_⟩
  rcases eq_or_lt_of_le hτ.1 with h0 | hpos
  · subst h0
    simp [sa16r_f0]
  · have hf : ∀ σ : ℝ, 0 < σ → sa16r_f0 d k p ν φ σ = sa16r_GamT d k p ν σ (sa16r_iota d k p φ) := by
      intro σ hσ
      simp [sa16r_f0, hσ, sa16r_H, sa16r_GamT]
    have := h1 (sa16r_iota d k p φ) τ ⟨hpos, hτ.2⟩
    rw [sa16r_ell_iota, ← hf τ hpos] at this
    rw [this]
    congr 1
    rw [intervalIntegral.integral_of_le hτ.1, intervalIntegral.integral_of_le hτ.1]
    refine setIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
    beta_reduce
    rw [hf σ hσ.1]

end Duh2

end HRS.Whole.AppendixA.Phase2SA16R
