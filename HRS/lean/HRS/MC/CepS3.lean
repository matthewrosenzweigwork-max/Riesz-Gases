import HRS.MC.CepS1
import HRS.MC.CepS2
import HRS.MC.CepC2
import HRS.MC.CepC3
import HRS.Stochastic.Bridge

/-!
# Packet CEPS3: sufficiency in B.13 (`N β⁻¹ ≤ a` implies a.s. noncollision on `[0,T]`)

Proof of `HRS.MC.Cepa.cep_S3_noncollision_of_threshold` (spec file `HRS/MC/CepaSpec.lean`, kept as `sorry`).
Route: Brownian filtration from `exists_isBrownianFiltration_of_isVectorBrownian`, `Y₀ = rep ∘ X₀`
(redefined on the null collision set), maximal solution `S2`, `τ = ⊤` a.s. by `S1`, then `C2 (←)`.
This file does not import the spec file; `cep_IsC11` is the duplicate `HRS.MC.CepC0.cep_IsC11`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepS3

open HRS

section Sufficiency

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- **S3 (B.13, sufficiency)**. -/
theorem cep_S3_noncollision_of_threshold_proof [IsProbabilityMeasure P]
    (hN : 2 ≤ N) {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : HRS.MC.CepC0.cep_IsC11 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {X : ℝ≥0 → Ω → Config 1 N} (hX : IsCepaLepingleFlow P D T X₀ W X)
    (hthr : (N : ℝ) * D.invβ ≤ a) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet 1 N := by
  classical
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
  have hY₀ae : ∀ᵐ ω ∂P, (fun i => Torus.mk (Y₀ ω i)) = X₀ ω := by
    filter_upwards [hdist] with ω h
    simp only [Y₀, h, ↓reduceIte]
    exact hmk ω
  obtain ⟨τ, Y, hsol⟩ := HRS.MC.CepS2.cep_S2_maximal_c11_proof (N := N) D hK hV hBF Y₀ hY₀m hY₀0
  have htop : ∀ᵐ ω ∂P, τ ω = ⊤ :=
    HRS.MC.CepS1.cep_S1_no_explosion_log_proof D hs ha hM hthr hV hBF hsol
  have hcol := HRS.MC.CepC3.cep_C3_collision_alternative_proof D hK hV hBF hsol
  have hC2 := HRS.MC.CepC2.cep_C2_noncollision_iff_nonexplosion_proof hb hT.le hdist hWW'
    hBF.cont hX.toContact hX.toContact.cont hsol hY₀ae hcol
  refine hC2.2 ?_
  filter_upwards [htop] with ω h
  rw [h]
  exact WithTop.coe_lt_top _

end Sufficiency

end HRS.MC.CepS3
