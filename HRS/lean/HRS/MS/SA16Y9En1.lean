import HRS.MS.SA16Y3EnD14
import HRS.MS.SA16Y9Gr1

/-!
# S.A.16 (SA16Y9) En1: energy inequality with a source (stability, P3)

`sa16y9_energy_diff`: if `w : [0,T] → W^{m+2,p}` has `ι² w` strongly differentiable in `W^{m,p}` with
`(ι² w)' = ν Δw + ι B_bc w - N w + S` (`hN`, `SA16DerCoef` as in `sa16y3_energy_strongD`), `jetEnergy(S)^{1/p} ≤ s`, then
`jetEnergy(ι² w τ)^{1/p} ≤ e^{c₊τ/p}(jetEnergy(ι² w 0)^{1/p} + s τ)`, `c = p cTr(B) + cNl`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2 HRS.Whole.AppendixA.Phase2SA16S

section En1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y9_jetEnergy_nonneg (k : ℕ) (G : WmpSpace d k p) : 0 ≤ jetEnergy d k p G := by
  rw [sa16v2_jetEnergy_eq_norm]
  exact Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem sa16y9_energy_diff {m : ℕ} {ν T B B' cNl s : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbc : ∀ r ∈ Ioo (0 : ℝ) T, SA16DerCoef (m + 1) B (bc r))
    (hbo : ∀ r ∈ Ioo (0 : ℝ) T, SA16BddCoef (m + 1) B' (bc r))
    (N : ℝ → WmpSpace d (m + 1 + 1) p → WmpSpace d m p)
    (hN : ∀ r ∈ Ioo (0 : ℝ) T, ∀ G : WmpSpace d (m + 1 + 1) p,
      fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(N r G)) ≤ cNl * jetEnergy d m p (sa16sz_iota2 d m p G))
    {w : ℝ → WmpSpace d (m + 1 + 1) p} (hw : ContinuousOn w (Icc 0 T)) (S : ℝ → WmpSpace d m p)
    (hS : ∀ τ ∈ Ioo (0 : ℝ) T, jetEnergy d m p (S τ) ^ (1 / p) ≤ s)
    (hder : ∀ τ ∈ Ioo (0 : ℝ) T, HasDerivAt (fun r => sa16sz_iota2 d m p (w r))
      (ν • sa16so_Lap d m p (w τ) + sa16r_iota d m p (sa16so_B d (m + 1) p (bc τ) (w τ)) - N τ (w τ) + S τ) τ) :
    ∀ τ ∈ Icc (0 : ℝ) T, jetEnergy d m p (sa16sz_iota2 d m p (w τ)) ^ (1 / p) ≤
      Real.exp (max (p * sa16sz_cTr d m p B + cNl) 0 / p * τ) *
        (jetEnergy d m p (sa16sz_iota2 d m p (w 0)) ^ (1 / p) + s * τ) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  set e : ℝ → ℝ := fun τ => jetEnergy d m p (sa16sz_iota2 d m p (w τ)) with he
  have hcont : ContinuousOn e (Icc 0 T) :=
    (sa16sz_jetEnergy_cont m).comp_continuousOn ((sa16sz_iota2 d m p).continuous.comp_continuousOn hw)
  have he0 : ∀ τ ∈ Icc (0 : ℝ) T, 0 ≤ e τ := fun τ _ => sa16y9_jetEnergy_nonneg _ _
  refine sa16y9_gronwall_src hp2 (le_max_right _ _) hs e (fun τ => jetEnergy d m p (S τ) ^ (1 / p)) hcont he0
    (fun τ _ => Real.rpow_nonneg (sa16y9_jetEnergy_nonneg _ _) _) hS ?_
  intro τ hτ
  have hE := (sa16v2_jetEnergy_hasFDerivAt d m p (sa16sz_iota2 d m p (w τ))).comp_hasDerivAt τ (hder τ hτ)
  refine ⟨_, hE, ?_⟩
  have hfd : fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p (w τ)) =
      sa16v2_Dj d m p (sa16sz_iota2 d m p (w τ)) :=
    (sa16v2_jetEnergy_hasFDerivAt d m p _).fderiv
  rw [map_add]
  have h1 := sa16y3_gen_energy_dissD m hν (hbc τ hτ) (hbo τ hτ) (N τ) (hN τ hτ) (w τ)
  rw [hfd] at h1
  have h2 := sa16y9_Dj_le d m p (sa16sz_iota2 d m p (w τ)) (S τ)
  rw [sa16y9_conj_inv p hp2] at h2
  have h3 : (p * sa16sz_cTr d m p B + cNl) * e τ ≤ max (p * sa16sz_cTr d m p B + cNl) 0 * e τ :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (he0 τ (Ioo_subset_Icc_self hτ))
  refine (add_le_add h1 h2).trans ?_
  show _ ≤ max (p * sa16sz_cTr d m p B + cNl) 0 * e τ + p * (e τ ^ (1 - 1 / p) * jetEnergy d m p (S τ) ^ (1 / p))
  linarith

end En1

end HRS.Whole.AppendixA.Phase2SA16R
