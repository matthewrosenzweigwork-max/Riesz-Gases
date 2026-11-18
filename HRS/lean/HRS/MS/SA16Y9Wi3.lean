import HRS.MS.SA16Y9Cr4
import HRS.MS.SA16Y5Fin5f

/-!
# S.A.16 (SA16Y9) Wi3: limit identity along any subsequence and common subsequence for two `SA16ApproxF` families (fractional regime)

Copy of `Wi2` for the fractional interface `SA16ApproxF` (`N : W^{m+2} →L W^{m}`, singular Volterra kernel).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Wi3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- reindexing the approximation sequence along `σ : ℕ → ℕ` -/
def SA16ApproxF.reindex {m : ℕ} {t Bm γ : ℝ} (A : SA16ApproxF d m p t Bm γ) (σ : ℕ → ℕ) : SA16ApproxF d m p t Bm γ where
  ν := fun n => A.ν (σ n)
  hν := fun n => A.hν (σ n)
  bc := fun n => A.bc (σ n)
  B' := fun n => A.B' (σ n)
  hbo := fun n => A.hbo (σ n)
  Bf := fun n => A.Bf (σ n)
  hBf := fun n => A.hBf (σ n)
  BB := fun n => A.BB (σ n)
  hBb := fun n => A.hBb (σ n)
  hBc := fun n => A.hBc (σ n)
  N := fun n => A.N (σ n)
  BN := fun n => A.BN (σ n)
  hNb := fun n => A.hNb (σ n)
  hNc := fun n => A.hNc (σ n)
  CN := fun n => A.CN (σ n)
  hγ := A.hγ
  hγ1 := A.hγ1
  hsharp := fun n => A.hsharp (σ n)
  hiota := fun n => A.hiota (σ n)
  φ := fun n => A.φ (σ n)
  u := fun n => A.u (σ n)
  hu := fun n => A.hu (σ n)
  hsol := fun n => A.hsol (σ n)
  hbd := fun n => A.hbd (σ n)

set_option maxHeartbeats 3200000 in
theorem sa16y9f_weak_identity {m : ℕ} {t Bm γ : ℝ} (ht : 0 < t) (A : SA16ApproxF d m p t Bm γ)
    (hNl : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ n, ∀ r ∈ Icc (0 : ℝ) t,
      ∀ y, |sa16r_ell d m p hψ (A.N n r y)| ≤ Cn * ‖sa16sz_iota2 d m p y‖)
    (hdiv : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ cN R0 : ℝ, 0 ≤ cN ∧
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
    obtain ⟨Cn, hCn0, hCn⟩ := hNl hψ
    set V : ℝ := (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0)).toReal ^ (1 / Real.conjExponent p) with hV
    have hV0 : 0 ≤ V := Real.rpow_nonneg ENNReal.toReal_nonneg _
    refine ⟨(νb * ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ + cN * V + Cn) * Bm, by positivity,
      fun n => ?_⟩
    have h := sa16y5f_weak_integrand (p := p) (m := m) (ν := A.ν n) (T := t) (B' := A.B' n) (BB := A.BB n)
      (BN := A.BN n) (CN := A.CN n) (γ := γ) (Cn := Cn) (cN := cN) (R0 := R0) (Bm := Bm) (A.hν n) ht A.hγ A.hγ1 hcN
      hCn0 (A.bc n) (A.hbo n) (A.Bf n) (A.hBf n) (A.hBb n) (A.hBc n) (A.N n) (A.hNb n) (A.hNc n)
      (A.hsharp n) (A.hiota n) (A.φ n) hψ (fun r hr y => hCn n r hr y) (hNb n) (A.hu n) (A.hsol n)
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

/-- the conditional limit identity of a family along `φs` -/
def SA16ApproxF.LimId {m : ℕ} {t Bm γ : ℝ} (A : SA16ApproxF d m p t Bm γ) (φs : ℕ → ℕ) (G : ℝ → WmpSpace d m p) : Prop :=
  ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (c0 : ℝ) (flim : ℝ → ℝ),
    Tendsto (fun n => sa16r_ell d (m + 1 + 1) p hψ (A.φ n)) atTop (𝓝 c0) →
    (∀ σ ∈ Icc (0 : ℝ) t, Tendsto (fun j => A.f hψ (φs j) σ) atTop (𝓝 (flim σ))) →
    (∀ τ ∈ Icc (0 : ℝ) t, sa16r_ell d m p hψ (G τ) = c0 + ∫ σ in (0 : ℝ)..τ, flim σ) ∧
      IntegrableOn flim (Icc 0 t)

set_option maxHeartbeats 1600000 in
theorem sa16y9f_weak_pair {m : ℕ} {t Bm1 Bm2 γ : ℝ} (ht : 0 < t) (A1 : SA16ApproxF d m p t Bm1 γ)
    (A2 : SA16ApproxF d m p t Bm2 γ)
    (hNl1 : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ n, ∀ r ∈ Icc (0 : ℝ) t,
      ∀ y, |sa16r_ell d m p hψ (A1.N n r y)| ≤ Cn * ‖sa16sz_iota2 d m p y‖)
    (hNl2 : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ n, ∀ r ∈ Icc (0 : ℝ) t,
      ∀ y, |sa16r_ell d m p hψ (A2.N n r y)| ≤ Cn * ‖sa16sz_iota2 d m p y‖)
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
  obtain ⟨φs1, hφs1, G1, -, hGn1, hGc1, -⟩ := sa16y5f_weak_limit ht A1 hNl1 hdiv1 hνb1
  have hNl2' : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ n, ∀ r ∈ Icc (0 : ℝ) t,
      ∀ y, |sa16r_ell d m p hψ ((A2.reindex φs1).N n r y)| ≤ Cn * ‖sa16sz_iota2 d m p y‖ := by
    intro ψ hψ
    obtain ⟨Cn, hCn0, h⟩ := hNl2 hψ
    exact ⟨Cn, hCn0, fun n => h (φs1 n)⟩
  have hdiv2' : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ cN R0 : ℝ, 0 ≤ cN ∧
      ∀ n, ∀ r ∈ Icc (0 : ℝ) t, ∀ x, |sa16so_divFun ((A2.reindex φs1).bc n r) ψ x| ≤
        cN * (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0).indicator (fun _ => (1 : ℝ)) x := by
    intro ψ hψ
    obtain ⟨cN, R0, hcN, h⟩ := hdiv2 hψ
    exact ⟨cN, R0, hcN, fun n => h (φs1 n)⟩
  obtain ⟨νb2, hνb2⟩ := hνb2
  obtain ⟨φs', hφs', G2, -, hGn2, hGc2, hlim2⟩ :=
    sa16y5f_weak_limit ht (A2.reindex φs1) hNl2' hdiv2' ⟨νb2, fun n => hνb2 (φs1 n)⟩
  have hφ : StrictMono (φs1 ∘ φs') := hφs1.comp hφs'
  refine ⟨φs1 ∘ φs', hφ, G1, G2, fun τ hτ ℓ => (hGn1 τ hτ ℓ).comp hφs'.tendsto_atTop, hGn2, hGc1, hGc2, ?_, ?_⟩
  · intro ψ hψ c0 flim hc hf
    exact sa16y9f_weak_identity ht A1 hNl1 hdiv1 hνb1 (φs1 ∘ φs') hφ G1
      (fun τ hτ ℓ => (hGn1 τ hτ ℓ).comp hφs'.tendsto_atTop) hψ c0 flim hc hf
  · intro ψ hψ c0 flim hc hf
    exact hlim2 hψ c0 flim (hc.comp hφs1.tendsto_atTop) hf

end Wi3

end HRS.Whole.AppendixA.Phase2SA16R
