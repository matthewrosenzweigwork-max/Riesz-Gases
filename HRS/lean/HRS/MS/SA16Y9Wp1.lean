import HRS.MS.SA16Y9Wi1

/-!
# S.A.16 (SA16Y9) Wp1: weak limits of two approximation families along a common subsequence (stability, G2b)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Wp1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the conditional limit identity of a family along `φs` -/
def SA16Approx.LimId {m : ℕ} {t CG Bm : ℝ} (A : SA16Approx d m p t CG Bm) (φs : ℕ → ℕ) (G : ℝ → WmpSpace d m p) : Prop :=
  ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (c0 : ℝ) (flim : ℝ → ℝ),
    Tendsto (fun n => sa16r_ell d (m + 1 + 1) p hψ (A.φ n)) atTop (𝓝 c0) →
    (∀ σ ∈ Icc (0 : ℝ) t, Tendsto (fun j => A.f hψ (φs j) σ) atTop (𝓝 (flim σ))) →
    (∀ τ ∈ Icc (0 : ℝ) t, sa16r_ell d m p hψ (G τ) = c0 + ∫ σ in (0 : ℝ)..τ, flim σ) ∧
      IntegrableOn flim (Icc 0 t)

set_option maxHeartbeats 1600000 in
theorem sa16y9_weak_pair {m : ℕ} {t CG Bm1 Bm2 : ℝ} (ht : 0 < t) (A1 : SA16Approx d m p t CG Bm1)
    (A2 : SA16Approx d m p t CG Bm2) (hCG : 0 ≤ CG)
    (hdiv1 : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ cN R0 : ℝ, 0 ≤ cN ∧
      ∀ n, ∀ r ∈ Icc (0 : ℝ) t, ∀ x, |sa16so_divFun (A1.bc n r) ψ x| ≤
        cN * (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0).indicator (fun _ => (1 : ℝ)) x)
    (hdiv2 : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ cN R0 : ℝ, 0 ≤ cN ∧
      ∀ n, ∀ r ∈ Icc (0 : ℝ) t, ∀ x, |sa16so_divFun (A2.bc n r) ψ x| ≤
        cN * (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0).indicator (fun _ => (1 : ℝ)) x)
    (hνb1 : ∃ νb : ℝ, ∀ n, A1.ν n ≤ νb) (hνb2 : ∃ νb : ℝ, ∀ n, A2.ν n ≤ νb) :
    ∃ φs : ℕ → ℕ, StrictMono φs ∧ ∃ G1 G2 : ℝ → WmpSpace d m p,
      (∀ τ ∈ Icc (0 : ℝ) t, ∀ ℓ : StrongDual ℝ (WmpSpace d m p),
        Tendsto (fun j => ℓ (sa16sz_iota2 d m p (A1.u (φs j) τ))) atTop (𝓝 (ℓ (G1 τ)))) ∧
      (∀ τ ∈ Icc (0 : ℝ) t, ∀ ℓ : StrongDual ℝ (WmpSpace d m p),
        Tendsto (fun j => ℓ (sa16sz_iota2 d m p (A2.u (φs j) τ))) atTop (𝓝 (ℓ (G2 τ)))) ∧
      (∀ ℓ : StrongDual ℝ (WmpSpace d m p), ContinuousOn (fun τ => ℓ (G1 τ)) (Icc (0 : ℝ) t)) ∧
      (∀ ℓ : StrongDual ℝ (WmpSpace d m p), ContinuousOn (fun τ => ℓ (G2 τ)) (Icc (0 : ℝ) t)) ∧
      A1.LimId φs G1 ∧ A2.LimId φs G2 := by
  obtain ⟨φs1, hφs1, G1, -, hGn1, hGc1, -⟩ := sa16y4_weak_limit ht A1 hCG hdiv1 hνb1
  have hdiv2' : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ cN R0 : ℝ, 0 ≤ cN ∧
      ∀ n, ∀ r ∈ Icc (0 : ℝ) t, ∀ x, |sa16so_divFun ((A2.reindex φs1).bc n r) ψ x| ≤
        cN * (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0).indicator (fun _ => (1 : ℝ)) x := by
    intro ψ hψ
    obtain ⟨cN, R0, hcN, h⟩ := hdiv2 hψ
    exact ⟨cN, R0, hcN, fun n => h (φs1 n)⟩
  obtain ⟨νb2, hνb2⟩ := hνb2
  obtain ⟨φs', hφs', G2, -, hGn2, hGc2, hlim2⟩ :=
    sa16y4_weak_limit ht (A2.reindex φs1) hCG hdiv2' ⟨νb2, fun n => hνb2 (φs1 n)⟩
  have hφ : StrictMono (φs1 ∘ φs') := hφs1.comp hφs'
  refine ⟨φs1 ∘ φs', hφ, G1, G2, fun τ hτ ℓ => (hGn1 τ hτ ℓ).comp hφs'.tendsto_atTop, hGn2, hGc1, hGc2, ?_, ?_⟩
  · intro ψ hψ c0 flim hc hf
    exact sa16y9_weak_identity ht A1 hCG hdiv1 hνb1 (φs1 ∘ φs') hφ G1
      (fun τ hτ ℓ => (hGn1 τ hτ ℓ).comp hφs'.tendsto_atTop) hψ c0 flim hc hf
  · intro ψ hψ c0 flim hc hf
    exact hlim2 hψ c0 flim (hc.comp hφs1.tendsto_atTop) hf

end Wp1

end HRS.Whole.AppendixA.Phase2SA16R
