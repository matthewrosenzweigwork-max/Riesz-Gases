import HRS.MS.SA16Y4Li1
import HRS.MS.SA16Y3S4
import HRS.MS.SA16Y3S5a
import HRS.MS.SA16Y3S6a
import HRS.MS.SA16Y4Id3

/-!
# S.A.16 (SA16Y4) Lm1: weak limit of the approximate solutions and the limit weak identity (interface check)

`SA16Approx`: the data of the `n`-th approximation (as produced by `sa16y4_approx`/`sa16y4_Kfam`): viscosity `ν_n`, coefficients
`bc_n(σ)` (`SA16BddCoef`), operators `T1_n(σ), T0_n(σ)` with `ι T1 = T0 ι`, `‖T0‖ ≤ CG`, `K_n(σ) = B_{bc} - T1 ι` bounded and
strongly continuous, the mild solution `u_n` and the uniform level-`m` bound `Bm`.
`sa16y4_weak_limit`: (1) `sa16y3_compact_weak` applies (equi-Lipschitz pairings from `sa16y3_lip_trunc`, constants depending on `ψ`
and on the uniform `cN`); (2) along the subsequence, if the integrands `f_n(σ)` of the weak identity converge pointwise to `flim` and
`ℓ_ψ(φ_n) → c0`, then `ℓ_ψ(G τ) = c0 + ∫_0^τ flim` for every `τ ∈ [0,t]`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Lm1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- data of the sequence of approximate solutions on `[0,t]` -/
structure SA16Approx (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (t CG Bm : ℝ) where
  ν : ℕ → ℝ
  hν : ∀ n, 0 < ν n
  bc : ℕ → ℝ → Fin d → EuclideanSpace ℝ (Fin d) → ℝ
  B' : ℕ → ℝ
  hbo : ∀ n, ∀ r ∈ Icc (0 : ℝ) t, SA16BddCoef (m + 1) (B' n) (bc n r)
  T1 : ℕ → ℝ → WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p
  T0 : ℕ → ℝ → WmpSpace d m p →L[ℝ] WmpSpace d m p
  hcomp : ∀ n, ∀ r ∈ Icc (0 : ℝ) t, (sa16r_iota d m p).comp (T1 n r) = (T0 n r).comp (sa16r_iota d m p)
  hT0 : ∀ n, ∀ r ∈ Icc (0 : ℝ) t, ‖T0 n r‖ ≤ CG
  K : ℕ → ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p
  hK : ∀ n r, K n r = sa16so_B d (m + 1) p (bc n r) - (T1 n r).comp (sa16r_iota d (m + 1) p)
  Bk : ℕ → ℝ
  hKb : ∀ n, ∀ r ∈ Icc (0 : ℝ) t, ‖K n r‖ ≤ Bk n
  hKc : ∀ n, ∀ x, ContinuousOn (fun r => K n r x) (Icc 0 t)
  φ : ℕ → WmpSpace d (m + 1 + 1) p
  u : ℕ → ℝ → WmpSpace d (m + 1 + 1) p
  hu : ∀ n, ContinuousOn (u n) (Icc 0 t)
  hsol : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, u n τ = sa16r_f0 d (m + 1) p (ν n) (φ n) τ +
    voltOp (gainKer (sa16r_GamT d (m + 1) p (ν n)) (K n)) (u n) τ
  hbd : ∀ n, ∀ r ∈ Icc (0 : ℝ) t, ‖sa16sz_iota2 d m p (u n r)‖ ≤ Bm

/-- the integrand of the weak identity of the `n`-th approximation -/
def SA16Approx.f {m : ℕ} {t CG Bm : ℝ} (A : SA16Approx d m p t CG Bm) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : IsCcInfty ψ) (n : ℕ) (σ : ℝ) : ℝ :=
  A.ν n * sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ) (A.u n σ) +
    sa16r_ell d (m + 1) p hψ (A.K n σ (A.u n σ))

set_option maxHeartbeats 1600000 in
theorem sa16y4_weak_limit {m : ℕ} {t CG Bm : ℝ} (ht : 0 < t) (A : SA16Approx d m p t CG Bm)
    (hCG : 0 ≤ CG) (hdiv : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ cN R0 : ℝ, 0 ≤ cN ∧
      ∀ n, ∀ r ∈ Icc (0 : ℝ) t, ∀ x, |sa16so_divFun (A.bc n r) ψ x| ≤
        cN * (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0).indicator (fun _ => (1 : ℝ)) x)
    (hνb : ∃ νb : ℝ, ∀ n, A.ν n ≤ νb) :
    ∃ φs : ℕ → ℕ, StrictMono φs ∧ ∃ G : ℝ → WmpSpace d m p,
      (∀ τ ∈ Icc (0 : ℝ) t, ‖G τ‖ ≤ (Fintype.card (WIndex d m) : ℝ) * Bm) ∧
      (∀ τ ∈ Icc (0 : ℝ) t, ∀ ℓ : StrongDual ℝ (WmpSpace d m p),
        Tendsto (fun j => ℓ (sa16sz_iota2 d m p (A.u (φs j) τ))) atTop (𝓝 (ℓ (G τ)))) ∧
      (∀ ℓ : StrongDual ℝ (WmpSpace d m p), ContinuousOn (fun τ => ℓ (G τ)) (Icc (0 : ℝ) t)) ∧
      ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (c0 : ℝ) (flim : ℝ → ℝ),
        Tendsto (fun n => sa16r_ell d (m + 1 + 1) p hψ (A.φ n)) atTop (𝓝 c0) →
        (∀ σ ∈ Icc (0 : ℝ) t, Tendsto (fun j => A.f hψ (φs j) σ) atTop (𝓝 (flim σ))) →
        (∀ τ ∈ Icc (0 : ℝ) t, sa16r_ell d m p hψ (G τ) = c0 + ∫ σ in (0 : ℝ)..τ, flim σ) ∧
          IntegrableOn flim (Icc 0 t) := by
  obtain ⟨νb, hνb⟩ := hνb
  have hBm0 : 0 ≤ Bm := (norm_nonneg _).trans (A.hbd 0 0 ⟨le_rfl, ht.le⟩)
  have hνb0 : 0 ≤ νb := (A.hν 0).le.trans (hνb 0)
  -- the weak-identity data, uniformly in n
  have hdata : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ Lf : ℝ, 0 ≤ Lf ∧ ∀ n,
      (∀ τ ∈ Icc (0 : ℝ) t, sa16r_ell d (m + 1 + 1) p hψ (A.u n τ) =
        sa16r_ell d (m + 1 + 1) p hψ (A.φ n) + ∫ σ in (0 : ℝ)..τ, A.f hψ n σ) ∧
      ContinuousOn (A.f hψ n) (Icc 0 t) ∧ ∀ σ ∈ Icc (0 : ℝ) t, |A.f hψ n σ| ≤ Lf := by
    intro ψ hψ
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
  -- equi-Lipschitz pairings
  have hLip : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ L : ℝ≥0, ∀ n,
      LipschitzOnWith L (fun τ => sa16r_ell d m p hψ (sa16sz_iota2 d m p (A.u n τ))) (Icc (0 : ℝ) t) := by
    intro ψ hψ
    obtain ⟨cN, R0, hcN, hNb⟩ := hdiv hψ
    set V : ℝ := (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0)).toReal ^ (1 / Real.conjExponent p) with hV
    have hV0 : 0 ≤ V := Real.rpow_nonneg ENNReal.toReal_nonneg _
    set Lc : ℝ := (νb * ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ + cN * V + ‖sa16r_ell d m p hψ‖ * CG) * Bm with hLc
    have hLc0 : 0 ≤ Lc := by positivity
    refine ⟨Real.toNNReal Lc, fun n => ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun τ hτ τ' hτ' => ?_
    have h := sa16y3_lip_trunc (p := p) (m := m) (ν := A.ν n) (T := t) (B' := A.B' n) (Bk := A.Bk n)
      (CG := CG) (cN := cN) (R0 := R0) (Bm := Bm) (A.hν n) ht hcN (A.bc n) (A.hbo n) (A.T1 n) (A.T0 n)
      (A.hcomp n) (A.hT0 n) (A.K n) (A.hK n) (A.hKb n) (A.hKc n) (A.φ n) hψ (sa16sw_cc_lap hψ)
      (sa16sw_heatWeak (A.hν n) t (m + 1) hψ) (hNb n) (A.hu n) (A.hsol n) (A.hbd n) τ hτ τ' hτ'
    rw [Real.dist_eq, Real.dist_eq, sa16y3_ell_iota2 hψ, sa16y3_ell_iota2 hψ, Real.coe_toNNReal _ hLc0]
    refine h.trans ?_
    have : A.ν n * ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ ≤ νb * ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ :=
      mul_le_mul_of_nonneg_right (hνb n) (ContinuousLinearMap.opNorm_nonneg _)
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    refine mul_le_mul_of_nonneg_right ?_ hBm0
    rw [hV] at hLc ⊢
    linarith
  obtain ⟨φs, hφs, G, hGn, hGw, hGc⟩ := sa16y3_compact_weak (p := p) (m := m) ht.le
    (fun n τ => sa16sz_iota2 d m p (A.u n τ)) (fun n τ hτ => A.hbd n τ hτ) (fun {ψ} hψ => hLip hψ)
  refine ⟨φs, hφs, G, hGn, hGw, hGc, fun {ψ} hψ c0 flim hc hf => ?_⟩
  obtain ⟨Lf, hLf0, hLf⟩ := hdata hψ
  refine ⟨fun τ hτ => ?_, sa16y4_integrableOn_limit (Lf := Lf) (fun j => A.f hψ (φs j)) flim
    (fun j => (hLf (φs j)).2.1) (fun j σ hσ => (hLf (φs j)).2.2 σ hσ) hf⟩
  have hlim := sa16y3_limit_identity (T := t) (Lf := Lf) (c0 := c0)
    (fun n τ => sa16r_ell d (m + 1 + 1) p hψ (A.u n τ)) (fun n => A.f hψ n)
    (fun n => sa16r_ell d (m + 1 + 1) p hψ (A.φ n)) (fun n => (hLf n).2.1) (fun n σ hσ => (hLf n).2.2 σ hσ)
    (fun n τ hτ => (hLf n).1 τ hτ) hc φs hφs (fun τ => sa16r_ell d m p hψ (G τ)) flim
    (fun τ hτ => by
      have := (hGw τ hτ (sa16r_ell d m p hψ))
      simp_rw [sa16y3_ell_iota2 hψ] at this
      exact this) hf τ hτ
  exact hlim

end Lm1

end HRS.Whole.AppendixA.Phase2SA16R
