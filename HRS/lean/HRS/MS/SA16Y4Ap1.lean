import HRS.MS.SA16Y4Dr1
import HRS.MS.SA16Y4Nl3
import HRS.MS.SA16Y3M2

/-!
# S.A.16 (SA16Y4) Ap1: the approximate solutions with `n`-uniform constants (conditional only on `hKc`)

`sa16y4_Kfam`: the Duhamel family `K_σ = B_{χ_{n+1}(ρ_n ⋆ b_{t-σ})} - G^{(m+1)}[ρ_n ⋆ μ_{t-σ}] ι` (coefficients at time `t - σ`).
`sa16y4_approx`: given a drift family with `‖b_r 0‖ ≤ A`, `‖D^j b_r‖ ≤ L` (`1 ≤ j ≤ m+2`) and regular densities, there are
`cE, CN` (independent of `n`, of the viscosities `ν_n > 0` and of the data) such that for every `n` for which `hKc`
(strong continuity of `σ ↦ K_σ y` on `[0,t]`) holds, there is a mild solution `u ∈ C([0,t]; W^{m+2,p})` with
`‖ι² u τ‖_{W^{m,p}} ≤ CN ‖ι² φ_n‖ e^{cE τ}`.  Only `hKc` (qualitative) is not proved here.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Ap1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the Duhamel family of the `n`-th approximation -/
def sa16y4_Kfam (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (σ : ℝ) : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p :=
  sa16so_B d (m + 1) p (fun i => sa16y4_tm d n (fun y => b (t - σ) y i)) -
    (sa16so_G d (m + 1) p s M (sa16q_mol n (μ (t - σ)))).comp (sa16r_iota d (m + 1) p)

set_option maxHeartbeats 1600000 in
theorem sa16y4_approx (d m : ℕ) (hd : 1 ≤ d) (s p MB Λ A L t : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs2 : s ≤ (d : ℝ) - 2) (hfar : (d : ℝ) < p * (s + 1)) (hA0 : 0 ≤ A) (hL0 : 0 ≤ L) (ht : 0 < t)
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : ∀ i j, |M i j| ≤ MB)
    (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ r))
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hb : ∀ r ∈ Icc (0 : ℝ) t, ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (b r) ∧ ‖b r 0‖ ≤ A ∧
      ∀ j, 1 ≤ j → j ≤ m + 2 → ∀ x, ‖iteratedFDeriv ℝ j (b r) x‖ ≤ L) :
    ∃ cE CN : ℝ, 0 < CN ∧ ∀ (ν : ℕ → ℝ), (∀ n, 0 < ν n) → ∀ (φ : ℕ → WmpSpace d (m + 1 + 1) p) (n : ℕ),
      (∀ x, ContinuousOn (fun σ => sa16y4_Kfam d m p s M t μ b n σ x) (Icc 0 t)) →
      ∃ u : ℝ → WmpSpace d (m + 1 + 1) p, ContinuousOn u (Icc 0 t) ∧
        (∀ τ ∈ Icc (0 : ℝ) t, u τ = sa16r_f0 d (m + 1) p (ν n) (φ n) τ +
          voltOp (gainKer (sa16r_GamT d (m + 1) p (ν n)) (sa16y4_Kfam d m p s M t μ b n)) u τ) ∧
        ∀ τ ∈ Icc (0 : ℝ) t, ‖sa16sz_iota2 d m p (u τ)‖ ≤ CN * ‖sa16sz_iota2 d m p (φ n)‖ * Real.exp (cE * τ) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  obtain ⟨B, hB0, B', hFam⟩ := sa16y4_trunc_mol_coef d m hA0 hL0
  obtain ⟨CG, CG1, hCG, hCG1, hnl⟩ := sa16y4_nl_pair d m hd s p MB Λ hs0 hs2 hfar
  obtain ⟨CN, hCN, hnorm⟩ := sa16y3_norm_of_energy (d := d) (p := p) m
  refine ⟨(p * sa16sz_cTr d m p B + p * sa16y3_CJ d m p * CG) / p, CN, hCN, fun ν hν φ n hKc => ?_⟩
  -- coefficient data
  have hcoef : ∀ r ∈ Icc (0 : ℝ) t,
      SA16DerCoef (m + 1) B (fun i => sa16y4_tm d n (fun y => b r y i)) ∧
        SA16BddCoef (m + 1) (B' n) (fun i => sa16y4_tm d n (fun y => b r y i)) := by
    intro r hr
    obtain ⟨hbs, hb0, hbL⟩ := hb r hr
    have hbs1 : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (b r) := hbs.of_le (by exact_mod_cast Nat.le_succ _)
    have hcomp := fun i => sa16y4_comp_bounds (k := m + 1) (by omega) hbs1 hb0
      (fun j hj1 hjk x => hbL j hj1 (by omega) x) i
    exact hFam n _ (fun i => (hcomp i).1) (fun i y => (hcomp i).2.1 y) (fun i j hj1 hjk x => (hcomp i).2.2 j hj1 hjk x)
  have hnlr : ∀ r ∈ Icc (0 : ℝ) t,
      ‖sa16so_G d m p s M (sa16q_mol n (μ r))‖ ≤ CG ∧ ‖sa16so_G d (m + 1) p s M (sa16q_mol n (μ r))‖ ≤ CG1 ∧
        (sa16r_iota d m p).comp (sa16so_G d (m + 1) p s M (sa16q_mol n (μ r))) =
          (sa16so_G d m p s M (sa16q_mol n (μ r))).comp (sa16r_iota d m p) := by
    intro r hr
    obtain ⟨T1, T0, h0, h1, hc, hs0', hs1'⟩ := hnl M hM (μ r) (hμ r hr) n
    rw [sa16so_G_eq hs0', sa16so_G_eq hs1']
    exact ⟨h0, h1, hc⟩
  set Bk : ℝ := sa16so_cB d (m + 1) (B' n) + CG1 * ‖sa16r_iota d (m + 1) p‖ with hBk
  have hB'0 : 0 ≤ B' n := (hcoef 0 ⟨le_rfl, ht.le⟩).2.nonneg
  have hBk0 : 0 ≤ Bk := by
    rw [hBk]
    exact add_nonneg (sa16so_cB_nonneg d (m + 1) hB'0) (mul_nonneg hCG1.le (ContinuousLinearMap.opNorm_nonneg _))
  have hKb : ∀ σ ∈ Icc (0 : ℝ) t, ‖sa16y4_Kfam d m p s M t μ b n σ‖ ≤ Bk := by
    intro σ hσ
    have hr : t - σ ∈ Icc (0 : ℝ) t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    unfold sa16y4_Kfam
    set X := sa16so_B d (m + 1) p (fun i => sa16y4_tm d n (fun y => b (t - σ) y i)) with hX
    set Y := (sa16so_G d (m + 1) p s M (sa16q_mol n (μ (t - σ)))).comp (sa16r_iota d (m + 1) p) with hY
    have h1 : ‖X‖ ≤ sa16so_cB d (m + 1) (B' n) := sa16so_B_norm (p := p) (hcoef _ hr).2
    have h2 : ‖Y‖ ≤ CG1 * ‖sa16r_iota d (m + 1) p‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hnlr _ hr).2.1 (ContinuousLinearMap.opNorm_nonneg _))
    have h3 : ‖X - Y‖ ≤ ‖X‖ + ‖Y‖ := norm_sub_le X Y
    rw [hBk]
    linarith
  obtain ⟨u, hu, hsol, hen⟩ := sa16y3_mild_energy (p := p) (m := m) (ν := ν n) (T := t) (B := B) (B' := B' n)
    (Bk := Bk) (CG := CG) (hν n) ht (fun σ => fun i => sa16y4_tm d n (fun y => b (t - σ) y i))
    (fun σ hσ => (hcoef _ ⟨by linarith [hσ.2], by linarith [hσ.1]⟩).1)
    (fun σ hσ => (hcoef _ ⟨by linarith [hσ.2], by linarith [hσ.1]⟩).2)
    (fun σ => sa16so_G d (m + 1) p s M (sa16q_mol n (μ (t - σ))))
    (fun σ => sa16so_G d m p s M (sa16q_mol n (μ (t - σ))))
    (fun σ hσ => (hnlr _ ⟨by linarith [hσ.2], by linarith [hσ.1]⟩).2.2)
    (fun σ hσ => (hnlr _ ⟨by linarith [hσ.2], by linarith [hσ.1]⟩).1)
    (sa16y4_Kfam d m p s M t μ b n) (fun σ => rfl) hKb hBk0 hKc (φ n)
  refine ⟨u, hu, hsol, fun τ hτ => ?_⟩
  have := hnorm (sa16sz_iota2 d m p (u τ)) (sa16sz_iota2 d m p (φ n))
    ((p * sa16sz_cTr d m p B + p * sa16y3_CJ d m p * CG) * τ) (hen τ hτ)
  refine this.trans (le_of_eq ?_)
  congr 2
  field_simp

end Ap1

end HRS.Whole.AppendixA.Phase2SA16R
