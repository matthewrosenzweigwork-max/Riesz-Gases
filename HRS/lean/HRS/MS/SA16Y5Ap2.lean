import HRS.MS.SA16Y4Ap2
import HRS.MS.SA16Y5Dn1
import HRS.MS.SA16Y3EnD14

/-!
# S.A.16 (SA16Y5) Ap2: approximate solutions for the order-one iso nonlocal term (time-interpolated coefficients)

`M = -(lam • 1)`, `lam ≥ 0`, `d-2 < s < d-1`, `d < p(s+1)`.  `sa16y5_Gop` is the (unique) order-one operator of a density; the `N`-th approximation has the
piecewise-linear interpolant `NInt σ = ∑ hat_i(σ) Gop(ρ_N ⋆ μ_{t-σ_i})` as nonlocal term and `K = B_{bc} - NInt`, solved by `sa16r_fixedn_mild`.
The dissipativity `hN` of the interpolant follows nodewise from `sa16y5_diss` (convexity), so `sa16y3_energy_solution_dissD` gives the
`N`-uniform energy bound with exponent `p cTr(B) + p lam C`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Ap2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

open Classical in
/-- the order-one nonlocal operator of a density -/
def sa16y5_Gop (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (μ : Euc d → ℝ) :
    WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p :=
  if h : ∃ T, SA16IsoOp d (m + 1) p s M μ T then Classical.choose h else 0

lemma sa16y5_Gop_eq {m : ℕ} {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {μ : Euc d → ℝ}
    {T : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p} (hT : SA16IsoOp d (m + 1) p s M μ T) :
    sa16y5_Gop d m p s M μ = T := by
  have h : ∃ T, SA16IsoOp d (m + 1) p s M μ T := ⟨T, hT⟩
  unfold sa16y5_Gop
  rw [dif_pos h]
  have h1 := Classical.choose_spec h
  exact sa16so_clm_ext fun φ => sa16r_wrep_inj d (m + 1) p _ _ (by
    filter_upwards [h1 φ, hT φ] with x e1 e2
    rw [e1, e2])

/-- interpolated nonlocal operator -/
def sa16y5_NInt (d m N : ℕ) (p : ℝ) [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (σ : ℝ) : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p :=
  ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ • sa16y5_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))

/-- the interpolated Duhamel family -/
def sa16y5_Kint (d m N : ℕ) (p : ℝ) [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : ℝ) : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p :=
  sa16so_B d (m + 1) p (sa16y4_bcInt d N t b σ) - sa16y5_NInt d m N p s M t μ σ

/-- interpolated density -/
def sa16y5_aInt (d N : ℕ) (t : ℝ) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (σ : ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * sa16q_mol N (μ (t - (i : ℝ) * t / N)) y

theorem sa16y5_mild_energy {m : ℕ} {ν T B B' Bk cNl : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbc : ∀ r ∈ Icc (0 : ℝ) T, SA16DerCoef (m + 1) B (bc r))
    (hbo : ∀ r ∈ Icc (0 : ℝ) T, SA16BddCoef (m + 1) B' (bc r))
    (N' : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hN : ∀ r ∈ Icc (0 : ℝ) T, ∀ G : WmpSpace d (m + 1 + 1) p,
      fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(sa16r_iota d m p (N' r G))) ≤
        cNl * jetEnergy d m p (sa16sz_iota2 d m p G))
    (K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : ∀ r, K r = sa16so_B d (m + 1) p (bc r) - N' r)
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ Bk) (hBk : 0 ≤ Bk)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) (φ : WmpSpace d (m + 1 + 1) p) :
    ∃ u : ℝ → WmpSpace d (m + 1 + 1) p, ContinuousOn u (Icc 0 T) ∧
      (∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
        voltOp (gainKer (sa16r_GamT d (m + 1) p ν) K) u τ) ∧
      ∀ τ ∈ Icc (0 : ℝ) T,
        jetEnergy d m p (sa16sz_iota2 d m p (u τ)) ≤
          jetEnergy d m p (sa16sz_iota2 d m p φ) * Real.exp ((p * sa16sz_cTr d m p B + cNl) * τ) := by
  obtain ⟨u, hu, hsol, -⟩ := sa16r_fixedn_mild (p := p) hν hT hBk (m + 1) K hKb hKc φ
  exact ⟨u, hu, hsol, sa16y3_energy_solution_dissD hν hT bc hbc hbo N' hN K hK hKb hBk hKc φ hu hsol⟩

end Ap2

end HRS.Whole.AppendixA.Phase2SA16R
