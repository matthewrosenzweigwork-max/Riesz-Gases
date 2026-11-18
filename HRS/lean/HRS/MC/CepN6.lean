import HRS.MC.CepN6Aux12
import HRS.MC.CepS1
import HRS.MC.CepS2
import HRS.MC.CepC2
import HRS.MC.CepC3
import HRS.Stochastic.Bridge

/-!
# Packet CEPN6: necessity in B.13 (contact below the threshold `a < N β⁻¹`)

Proof of `HRS.MC.Cepa.cep_N6_contact_below_threshold` (spec file `HRS/MC/CepaSpec.lean`, kept as `sorry`).
Route: the setup of `CepS3` (Brownian filtration, `Y₀ = rep ∘ X₀`, maximal solution `S2`), the assumed
noncollision gives `τ > T` a.s. by `C2 (→)`; the sorting permutation `π` of the coordinates of `Y₀` is
`ℱ₀`-measurable, and the contradiction is `CepN6Aux12.n6_core` (N3 steering, N4 gap dynamics, N5/N5b Bessel
hitting, a Kolmogorov bound for the other particles, and a compactness argument).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepN6

open HRS HRS.MC.CepN4

theorem n6_rep_mem (x : Torus 1) : Torus.rep x 0 ∈ Set.Ico (0 : ℝ) 1 := by
  have := (AddCircle.equivIco (1 : ℝ) 0 (x 0)).2
  simpa [Torus.rep] using this

section Necessity

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- **N6 (B.13, necessity)**. -/
theorem cep_N6_contact_below_threshold_proof [IsProbabilityMeasure P]
    (hN : 2 ≤ N) {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : HRS.MC.CepC0.cep_IsC11 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {X : ℝ≥0 → Ω → Config 1 N} (hX : IsCepaLepingleFlow P D T X₀ W X)
    (hbelow : a < (N : ℝ) * D.invβ) :
    ¬ ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet 1 N := by
  classical
  intro hall
  have hs1 : D.s < 1 := by simpa using D.hsd
  have hK : KernelLocal 1 D.s := kernelLocal_d1 D.hs0 hs1
  have hb : IsLocLipschitzDrift (liftedFree 1 N) (fun _ Z => liftedDrift D Z) :=
    HRS.MC.CepC0.cep_C0_locLipschitz_proof D hK.smoothOffZero hV
  obtain ⟨W', hW'm, hWW', hBF, hX₀ℱ⟩ :=
    exists_isBrownianFiltration_of_isVectorBrownian P W hW X₀ hX₀ hind
  set ℱ := generatedFiltration P X₀ hX₀ W' hW'm with hℱ
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀, X₀ ω₀ ∉ collisionSet 1 N := hdist.exists
  let rep : Ω → Fin N → Euc 1 := fun ω i => Torus.rep (X₀ ω i)
  have hmk : ∀ ω, (fun i => Torus.mk (rep ω i)) = X₀ ω := fun ω =>
    funext fun i => Torus.mk_rep _
  have hcoll : MeasurableSet (collisionSet 1 N) := (isClosed_collisionSet 1 N).measurableSet
  let Y₀ : Ω → Fin N → Euc 1 := fun ω => if X₀ ω ∈ collisionSet 1 N then rep ω₀ else rep ω
  have hY₀m : ∀ t : ℝ, Measurable[ℱ t] Y₀ := by
    intro t
    let _ : MeasurableSpace Ω := ℱ t
    have hrep : Measurable rep := measurable_pi_iff.2 fun i =>
      (measurable_torusRep 1).comp ((measurable_pi_apply i).comp (hX₀ℱ t))
    exact Measurable.ite (hX₀ℱ t hcoll) measurable_const hrep
  have hY₀0 : ∀ ω, Y₀ ω ∈ liftedFree 1 N := by
    intro ω
    show (fun i => Torus.mk (Y₀ ω i)) ∉ collisionSet 1 N
    by_cases h : X₀ ω ∈ collisionSet 1 N
    · simp only [Y₀, h, ↓reduceIte]
      rw [hmk ω₀]
      exact hω₀
    · simp only [Y₀, h, ↓reduceIte]
      rw [hmk ω]
      exact h
  have hY₀rng : ∀ ω i, Y₀ ω i 0 ∈ Set.Ico (0 : ℝ) 1 := by
    intro ω i
    by_cases h : X₀ ω ∈ collisionSet 1 N
    · simp only [Y₀, h, ↓reduceIte]
      exact n6_rep_mem _
    · simp only [Y₀, h, ↓reduceIte]
      exact n6_rep_mem _
  have hY₀ae : ∀ᵐ ω ∂P, (fun i => Torus.mk (Y₀ ω i)) = X₀ ω := by
    filter_upwards [hdist] with ω h
    simp only [Y₀, h, ↓reduceIte]
    exact hmk ω
  obtain ⟨τ, Y, hsol⟩ := HRS.MC.CepS2.cep_S2_maximal_c11_proof (N := N) D hK hV hBF Y₀ hY₀m hY₀0
  have hcol := HRS.MC.CepC3.cep_C3_collision_alternative_proof D hK hV hBF hsol
  have hC2 := HRS.MC.CepC2.cep_C2_noncollision_iff_nonexplosion_proof hb hT.le hdist hWW'
    hBF.cont hX.toContact hX.toContact.cont hsol hY₀ae hcol
  have htop := hC2.1 hall
  exact n6_core hN hs hβ ha hM hV hBF hsol
    (π := n6_pi Y₀) (fun σ => n6_pi_meas (m := ℱ 0) (hsol.init_meas 0) σ)
    (fun ω => n6_pi_strict (hY₀0 ω) (hY₀rng ω)) hT htop hbelow

end Necessity

end HRS.MC.CepN6
