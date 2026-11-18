import HRS.MS.SA16Y9En4

/-!
# S.A.16 (SA16Y9) Wi1: the limit identity along an arbitrary subsequence, and a common subsequence for two families (stability, G2a)

`sa16y9_weak_identity`: the last part of `sa16y4_weak_limit` (limit identity of the weak identity for the integrands `A.f`), for any
strictly increasing `φs` along which `ι² u_n(τ) ⇀ G τ`.  `SA16Approx.reindex`, `sa16y9_weak_pair`: a common subsequence for two families.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Wi1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- reindexing the approximation sequence along `σ : ℕ → ℕ` -/
def SA16Approx.reindex {m : ℕ} {t CG Bm : ℝ} (A : SA16Approx d m p t CG Bm) (σ : ℕ → ℕ) : SA16Approx d m p t CG Bm where
  ν := fun n => A.ν (σ n)
  hν := fun n => A.hν (σ n)
  bc := fun n => A.bc (σ n)
  B' := fun n => A.B' (σ n)
  hbo := fun n => A.hbo (σ n)
  T1 := fun n => A.T1 (σ n)
  T0 := fun n => A.T0 (σ n)
  hcomp := fun n => A.hcomp (σ n)
  hT0 := fun n => A.hT0 (σ n)
  K := fun n => A.K (σ n)
  hK := fun n => A.hK (σ n)
  Bk := fun n => A.Bk (σ n)
  hKb := fun n => A.hKb (σ n)
  hKc := fun n => A.hKc (σ n)
  φ := fun n => A.φ (σ n)
  u := fun n => A.u (σ n)
  hu := fun n => A.hu (σ n)
  hsol := fun n => A.hsol (σ n)
  hbd := fun n => A.hbd (σ n)

set_option maxHeartbeats 3200000 in
theorem sa16y9_weak_identity {m : ℕ} {t CG Bm : ℝ} (ht : 0 < t) (A : SA16Approx d m p t CG Bm)
    (hCG : 0 ≤ CG) (hdiv : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ cN R0 : ℝ, 0 ≤ cN ∧
      ∀ n, ∀ r ∈ Icc (0 : ℝ) t, ∀ x, |sa16so_divFun (A.bc n r) ψ x| ≤
        cN * (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0).indicator (fun _ => (1 : ℝ)) x)
    (hνb : ∃ νb : ℝ, ∀ n, A.ν n ≤ νb) (φs : ℕ → ℕ) (hφs : StrictMono φs) (G : ℝ → WmpSpace d m p)
    (hGn : ∀ τ ∈ Icc (0 : ℝ) t, ∀ ℓ : StrongDual ℝ (WmpSpace d m p),
        Tendsto (fun j => ℓ (sa16sz_iota2 d m p (A.u (φs j) τ))) atTop (𝓝 (ℓ (G τ))))
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (c0 : ℝ) (flim : ℝ → ℝ)
    (hc : Tendsto (fun n => sa16r_ell d (m + 1 + 1) p hψ (A.φ n)) atTop (𝓝 c0))
    (hf : ∀ σ ∈ Icc (0 : ℝ) t, Tendsto (fun j => A.f hψ (φs j) σ) atTop (𝓝 (flim σ))) :
    (∀ τ ∈ Icc (0 : ℝ) t, sa16r_ell d m p hψ (G τ) = c0 + ∫ σ in (0 : ℝ)..τ, flim σ) ∧
      IntegrableOn flim (Icc 0 t) := by
  obtain ⟨νb, hνb⟩ := hνb
  have hBm0 : 0 ≤ Bm := (norm_nonneg _).trans (A.hbd 0 0 ⟨le_rfl, ht.le⟩)
  have hνb0 : 0 ≤ νb := (A.hν 0).le.trans (hνb 0)
  have hdata : ∃ Lf : ℝ, 0 ≤ Lf ∧ ∀ n,
      (∀ τ ∈ Icc (0 : ℝ) t, sa16r_ell d (m + 1 + 1) p hψ (A.u n τ) =
        sa16r_ell d (m + 1 + 1) p hψ (A.φ n) + ∫ σ in (0 : ℝ)..τ, A.f hψ n σ) ∧
      ContinuousOn (A.f hψ n) (Icc 0 t) ∧ ∀ σ ∈ Icc (0 : ℝ) t, |A.f hψ n σ| ≤ Lf := by
    obtain ⟨cN, R0, hcN, hNb⟩ := hdiv hψ
    set V : ℝ := (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0)).toReal ^ (1 / Real.conjExponent p) with hV
    have hV0 : 0 ≤ V := Real.rpow_nonneg ENNReal.toReal_nonneg _
    refine ⟨(νb * ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ + cN * V + ‖sa16r_ell d m p hψ‖ * CG) * Bm, by positivity,
      fun n => ?_⟩
    have h := sa16y4_weak_integrand (p := p) (m := m) (ν := A.ν n) (T := t) (B' := A.B' n) (Bk := A.Bk n)
      (CG := CG) (cN := cN) (R0 := R0) (Bm := Bm) (A.hν n) ht hcN (A.bc n) (A.hbo n) (A.T1 n) (A.T0 n)
      (A.hcomp n) (A.hT0 n) (A.K n) (A.hK n) (A.hKb n) (A.hKc n) (A.φ n) hψ (hNb n) (A.hu n) (A.hsol n)
      (A.hbd n)
    refine ⟨h.1, h.2.1, fun σ hσ => (h.2.2 σ hσ).trans ?_⟩
    have : A.ν n * ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ ≤ νb * ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ :=
      mul_le_mul_of_nonneg_right (hνb n) (ContinuousLinearMap.opNorm_nonneg _)
    refine mul_le_mul_of_nonneg_right ?_ hBm0
    simp only [hV] at *
    linarith
  obtain ⟨Lf, hLf0, hLf⟩ := hdata
  refine ⟨fun τ hτ => ?_, sa16y4_integrableOn_limit (Lf := Lf) (fun j => A.f hψ (φs j)) flim
    (fun j => (hLf (φs j)).2.1) (fun j σ hσ => (hLf (φs j)).2.2 σ hσ) hf⟩
  exact sa16y3_limit_identity (T := t) (Lf := Lf) (c0 := c0)
    (fun n τ => sa16r_ell d (m + 1 + 1) p hψ (A.u n τ)) (fun n => A.f hψ n)
    (fun n => sa16r_ell d (m + 1 + 1) p hψ (A.φ n)) (fun n => (hLf n).2.1) (fun n σ hσ => (hLf n).2.2 σ hσ)
    (fun n τ hτ => (hLf n).1 τ hτ) hc φs hφs (fun τ => sa16r_ell d m p hψ (G τ)) flim
    (fun τ hτ => by
      have := (hGn τ hτ (sa16r_ell d m p hψ))
      simp_rw [sa16y3_ell_iota2 hψ] at this
      exact this) hf τ hτ

end Wi1

end HRS.Whole.AppendixA.Phase2SA16R
