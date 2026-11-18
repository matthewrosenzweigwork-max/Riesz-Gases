import HRS.MS.FixEqP3Aux20

/-!
# S5.7 `fixed_equation` (worker S57P), part 33: Hölder bound in the terminal time of `U_N - U`
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ} {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K KN : ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν νN : ℝ}
  {c cN : ℝ → Euc d → Euc d} {ρ ρN : ℝ → Euc d → ℝ} {A Λc νbar : ℝ} {m : ℝ} {J : ℕ}
  {L' Dν Dc Dρ : ℝ}

theorem s57p_pair_d (hθ : IsUlCutoff θ) (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M Q : Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (K KN : ℝ) (m : ℝ) (J : ℕ)
    (hJ1 : 3 * (n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) + 9 ≤ J)
    (hJ2 : 3 * ((n + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) + 1 + ⌈(d : ℝ) / 2⌉₊) + 9 ≤ J) (T : ℝ) (hT : 0 ≤ T)
    {A Λc νbar : ℝ} (hA : 0 ≤ A) (hΛc : 0 ≤ Λc) (hνbar : 0 ≤ νbar) :
    ∃ Cp2 : ℝ, 0 ≤ Cp2 ∧ ∀ {ν νN : ℝ} {c cN : ℝ → Euc d → Euc d} {ρ ρN : ℝ → Euc d → ℝ} {L' Dν Dc Dρ : ℝ},
      S57pFx θ T n K s M Q ν c ρ A Λc νbar → S57pFx θ T n KN s M Q νN cN ρN A Λc νbar →
      UlAdjointInput θ (fixedEqCoeff s M Q ν c ρ) T (n + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) K →
      (∀ t ∈ Set.Icc (0 : ℝ) T, RgDecay ((n + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) + 1 + ⌈(d : ℝ) / 2⌉₊ + 2) (fun _ => A) (ρN t)) →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ ((n + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) (cN t) ∧
        ∀ i ≤ (n + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ i (cN t) x‖ ≤ Λc) →
      S57pDelta (n + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) L' T ν νN c cN ρ ρN Dν Dc Dρ → (d : ℝ) + 3 ≤ L' →
      ∀ α : MultiIndex d, ∀ s₀ t₀ : ℝ, 0 ≤ s₀ → s₀ ≤ t₀ → t₀ ≤ T → ∀ r ∈ Set.Icc (0 : ℝ) s₀, ∀ x,
        ‖iteratedFDeriv ℝ 1 (fun y => (propagatorW (fixedEqCoeff s M Q ν c ρ) r t₀ (oscTestFun m α) y -
            propagatorW (fixedEqCoeff s M Q νN cN ρN) r t₀ (oscTestFun m α) y) -
          (propagatorW (fixedEqCoeff s M Q ν c ρ) r s₀ (oscTestFun m α) y -
            propagatorW (fixedEqCoeff s M Q νN cN ρN) r s₀ (oscTestFun m α) y)) x‖ ≤
          Cp2 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * (max Dν 0 + max Dc 0 + max Dρ 0) * (t₀ - s₀) := by
  set e := ⌈(d : ℝ) / 2⌉₊ with he
  obtain ⟨Cud, hCud0, hCud⟩ := s57p_diff_bound hθ n
  obtain ⟨Cj2, hCj2, hjets2⟩ := s57p_osc_jets hθ hd m J ((n + 1 + e + 3) + 1 + e) hJ2
  obtain ⟨Cg1, hCg1, hgen1⟩ := s57p_gen_jets hθ hd hs0 hsd M Q m J (n + 1 + 1 + e) hJ1 hA hΛc hνbar
  obtain ⟨Cg2, hCg2, hgen2⟩ := s57p_gen_jets hθ hd hs0 hsd M Q m J ((n + 1 + e + 3) + 1 + e) hJ2 hA hΛc hνbar
  obtain ⟨hCu10, hCu1⟩ := s57pCu_spec hθ (n + 1)
  obtain ⟨hCu20, hCu2⟩ := s57pCu_spec hθ (n + 1 + e + 3)
  have hCgD := s57pCg_nonneg (d := d) hs0 M (n + 1 + e)
  set R1 := n + 1 + 1 + e with hR1
  set R2 := (n + 1 + e + 3) + 1 + e with hR2
  refine ⟨T * (|KN| * (Cud * (s57pCg d s M (n + 1 + e) * (|K| * (s57pCu θ hθ (n + 1 + e + 3) * Cg2))))) +
    |K| * (s57pCu θ hθ (n + 1) * (s57pCg d s M (n + 1 + e) * Cj2)), ?_, ?_⟩
  · have h1 := mul_nonneg hT (mul_nonneg (abs_nonneg KN) (mul_nonneg hCud0 (mul_nonneg hCgD
      (mul_nonneg (abs_nonneg K) (mul_nonneg hCu20 hCg2)))))
    have h2 := mul_nonneg (abs_nonneg K) (mul_nonneg hCu10 (mul_nonneg hCgD hCj2))
    exact add_nonneg h1 h2
  intro ν νN c cN ρ ρN L' Dν Dc Dρ Fx FxN adj2 hρN2 hcN2 Δ hL' α s₀ t₀ hs0' hst htT r hr x
  set φ := oscTestFun m α with hφ
  set lam := oscEigenvalue d α ^ (((J : ℝ) - m) / 2) with hlamdef
  have hlam : 0 ≤ lam := Real.rpow_nonneg (oscEigenvalue_pos α).le _
  set Dt := max Dν 0 + max Dc 0 + max Dρ 0 with hDt
  have hDt0 : 0 ≤ Dt := by positivity
  have hn4 := Fx.hn4
  have hsT : s₀ ∈ Set.Icc (0 : ℝ) T := ⟨hs0', hst.trans htT⟩
  have hφ1 : ContDiff ℝ (R1 : WithTop ℕ∞) φ := s55_cd_of_inf _ (hjets2 α).1
  have hφb : ∀ l ≤ R1, ∀ y, ‖iteratedFDeriv ℝ l φ y‖ ≤ Cj2 * lam := fun l hl y => (hjets2 α).2 l (by omega) y
  have hBφ0 : 0 ≤ Cj2 * lam := mul_nonneg hCj2 hlam
  have hBg0 : 0 ≤ Cg1 * lam := mul_nonneg hCg1 hlam
  have hgC : ∀ u ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (R1 : WithTop ℕ∞) (generatorW (fixedEqCoeff s M Q ν c ρ) u φ) ∧
      ∀ l ≤ R1, ∀ y, ‖iteratedFDeriv ℝ l (generatorW (fixedEqCoeff s M Q ν c ρ) u φ) y‖ ≤ Cg1 * lam := fun u hu =>
    hgen1 Fx.hν (Fx.hρ u hu) (Fx.hc u hu).1 (Fx.hc u hu).2 α
  have hgN : ∀ u ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (R1 : WithTop ℕ∞) (generatorW (fixedEqCoeff s M Q νN cN ρN) u φ) ∧
      ∀ l ≤ R1, ∀ y, ‖iteratedFDeriv ℝ l (generatorW (fixedEqCoeff s M Q νN cN ρN) u φ) y‖ ≤ Cg1 * lam := fun u hu =>
    hgen1 FxN.hν (FxN.hρ u hu) (FxN.hc u hu).1 (FxN.hc u hu).2 α
  have c1 := s57p_td_int hθ Fx.fam hn4 hBφ0 hBg0 hφ1 hφb hgC hs0' hst htT r hr 1 (by omega) x
  have c2 := s57p_td_int hθ FxN.fam hn4 hBφ0 hBg0 hφ1 hφb hgN hs0' hst htT r hr 1 (by omega) x
  have i1 := s57p_td_ii hθ Fx.fam hn4 hBφ0 hBg0 hφ1 hφb hgC hr.1 hr.2 hst htT (i := 1) (by omega) x
  have i2 := s57p_td_ii hθ FxN.fam hn4 hBφ0 hBg0 hφ1 hφb hgN hr.1 hr.2 hst htT (i := 1) (by omega) x
  set CC := fixedEqCoeff s M Q ν c ρ with hCC
  set CN := fixedEqCoeff s M Q νN cN ρN with hCN
  set BA := T * (|KN| * (Cud * (s57pCg d s M (n + 1 + e) * Dt * (|K| * (s57pCu θ hθ (n + 1 + e + 3) * (Cg2 * lam)))))) with hBA
  set BB := |K| * (s57pCu θ hθ (n + 1) * (s57pCg d s M (n + 1 + e) * Dt * (Cj2 * lam))) with hBB
  have hBA0 : 0 ≤ BA := mul_nonneg hT (mul_nonneg (abs_nonneg _) (mul_nonneg hCud0 (mul_nonneg
    (mul_nonneg hCgD hDt0) (mul_nonneg (abs_nonneg _) (mul_nonneg hCu20 (mul_nonneg hCg2 hlam))))))
  have hBB0 : 0 ≤ BB := mul_nonneg (abs_nonneg _) (mul_nonneg hCu10 (mul_nonneg (mul_nonneg hCgD hDt0) hBφ0))
  have hpt : ∀ u ∈ Set.Ioc s₀ t₀, ‖iteratedFDeriv ℝ 1 (propagatorW CC r u (generatorW CC u φ)) x -
      iteratedFDeriv ℝ 1 (propagatorW CN r u (generatorW CN u φ)) x‖ ≤ BA + BB := by
    intro u hu
    have huT : u ∈ Set.Icc (0 : ℝ) T := ⟨hs0'.trans hu.1.le, hu.2.trans htT⟩
    have hru : r ∈ Set.Icc (0 : ℝ) u := ⟨hr.1, hr.2.trans hu.1.le⟩
    have hsubu : ∀ τ ∈ Set.Icc (0 : ℝ) u, τ ∈ Set.Icc (0 : ℝ) T := fun τ hτ => ⟨hτ.1, hτ.2.trans huT.2⟩
    obtain ⟨hψC1, hψCb⟩ := hgC u huT
    obtain ⟨hψN1, hψNb⟩ := hgN u huT
    obtain ⟨hψN2, hψN2b⟩ := hgen2 FxN.hν (hρN2 u huT) (hcN2 u huT).1 (hcN2 u huT).2 α
    have hBN2 : 0 ≤ Cg2 * lam := mul_nonneg hCg2 hlam
    obtain ⟨hclA, hOA⟩ := hCu2 adj2 hBN2 hψN2 hψN2b u huT
    obtain ⟨hclN, hON⟩ := hCu1 FxN.fam.adj hBg0 hψN1 hψNb u huT
    have hA := hCud (M := M) (Q := Q) (ν := ν) (νN := νN) (c := c) (cN := cN) (ρ := ρ) (ρN := ρN) (s := s) (t := u)
      huT.1 hn4 (Fx.fe.mono huT.2) (FxN.fe.mono huT.2) (fun t' ht' => FxN.fam.uniq t' (hsubu t' ht'))
      (KN := KN) (FxN.fam.mono huT.2).adj (K' := n + 1 + e + 3) le_rfl hL' Δ.hν
      (fun τ hτ => Δ.hc τ (hsubu τ hτ)) (fun τ hτ => Δ.hρ τ (hsubu τ hτ)) hclA hclN
      (Bf := |K| * (s57pCu θ hθ (n + 1 + e + 3) * (Cg2 * lam))) (BfN := |KN| * (s57pCu θ hθ (n + 1) * (Cg1 * lam)))
      (fun r' hr' => hOA r' hr')
      (fun r' hr' => ⟨((hON r' hr').1).of_le (by exact_mod_cast (by omega : 4 ≤ n + 1)),
        fun j hj y => (hON r' hr').2 j (by omega) y⟩) r hru 1 (by omega) x
    -- the generator difference
    have hdg := s57p_gen_diff (T := T) M Q Fx.fe FxN.fe (n + 1 + e) (K' := n + 1 + e + 3) le_rfl hL' Δ.hν Δ.hc Δ.hρ u huT
      (Cj2 * lam) φ hBφ0 (s55_cd_of_inf _ (hjets2 α).1) (fun l hl y => (hjets2 α).2 l (by omega) y)
    have hRe : n + 1 + e + 1 = n + 1 + 1 + e := by omega
    have hrg1 : ContDiff ℝ (R1 : WithTop ℕ∞) (fun y => generatorW CC u φ y - generatorW CN u φ y) := by
      have := hdg.1; rw [hRe] at this; exact this
    have hrgb : ∀ l ≤ R1, ∀ y, ‖iteratedFDeriv ℝ l (fun y => generatorW CC u φ y - generatorW CN u φ y) y‖ ≤
        s57pCg d s M (n + 1 + e) * Dt * (Cj2 * lam) := fun l hl y => by
      have := hdg.2 l (by omega) y
      simpa using this
    obtain ⟨-, hOB⟩ := hCu1 Fx.fam.adj (mul_nonneg (mul_nonneg hCgD hDt0) hBφ0) hrg1 hrgb u huT
    have hlin := s57p_prop_lin2 hθ Fx.fam hBg0 hBg0 hψC1 hψCb hψN1 hψNb 1 (-1) huT r hru
    have hfeq : (fun y => (1 : ℝ) * generatorW CC u φ y + (-1 : ℝ) * generatorW CN u φ y) =
        fun y => generatorW CC u φ y - generatorW CN u φ y := by funext y; ring
    rw [hfeq] at hlin
    have hUC : propagatorW CC r u (generatorW CC u φ) = fun y => propagatorW CC r u
        (fun z => generatorW CC u φ z - generatorW CN u φ z) y + propagatorW CC r u (generatorW CN u φ) y := by
      funext y
      have h : propagatorW CC r u (fun z => generatorW CC u φ z - generatorW CN u φ z) y =
          (1 : ℝ) * propagatorW CC r u (generatorW CC u φ) y + (-1 : ℝ) * propagatorW CC r u (generatorW CN u φ) y :=
        congrFun hlin y
      linarith
    have hc1B : ContDiff ℝ 1 (propagatorW CC r u (fun z => generatorW CC u φ z - generatorW CN u φ z)) :=
      ((hOB r hru).1).of_le (by exact_mod_cast (by omega : 1 ≤ n + 1))
    have hc1N : ContDiff ℝ 1 (propagatorW CC r u (generatorW CN u φ)) :=
      ((hOA r hru).1).of_le (by exact_mod_cast (by omega : 1 ≤ n + 1 + e + 3))
    have hc1M : ContDiff ℝ 1 (propagatorW CN r u (generatorW CN u φ)) :=
      ((hON r hru).1).of_le (by exact_mod_cast (by omega : 1 ≤ n + 1))
    rw [hUC]
    have e1 : iteratedFDeriv ℝ 1 (fun y => propagatorW CC r u (fun z => generatorW CC u φ z - generatorW CN u φ z) y +
        propagatorW CC r u (generatorW CN u φ) y) x = iteratedFDeriv ℝ 1 (propagatorW CC r u
          (fun z => generatorW CC u φ z - generatorW CN u φ z)) x + iteratedFDeriv ℝ 1 (propagatorW CC r u (generatorW CN u φ)) x :=
      iteratedFDeriv_add_apply hc1B.contDiffAt hc1N.contDiffAt
    have e2 : iteratedFDeriv ℝ 1 (fun y => propagatorW CC r u (generatorW CN u φ) y - propagatorW CN r u (generatorW CN u φ) y) x =
        iteratedFDeriv ℝ 1 (propagatorW CC r u (generatorW CN u φ)) x - iteratedFDeriv ℝ 1 (propagatorW CN r u (generatorW CN u φ)) x :=
      iteratedFDeriv_sub_apply hc1N.contDiffAt hc1M.contDiffAt
    have hAB := hA
    rw [e2] at hAB
    have hnA : ‖iteratedFDeriv ℝ 1 (propagatorW CC r u (generatorW CN u φ)) x -
        iteratedFDeriv ℝ 1 (propagatorW CN r u (generatorW CN u φ)) x‖ ≤ BA := by
      refine hAB.trans ?_
      calc u * (|KN| * (Cud * (s57pCg d s M (n + 1 + e) * Dt * (|K| * (s57pCu θ hθ (n + 1 + e + 3) * (Cg2 * lam))))))
          ≤ T * (|KN| * (Cud * (s57pCg d s M (n + 1 + e) * Dt * (|K| * (s57pCu θ hθ (n + 1 + e + 3) * (Cg2 * lam)))))) :=
            mul_le_mul_of_nonneg_right (hu.2.trans htT) (mul_nonneg (abs_nonneg _) (mul_nonneg hCud0 (mul_nonneg
              (mul_nonneg hCgD hDt0) (mul_nonneg (abs_nonneg _) (mul_nonneg hCu20 (mul_nonneg hCg2 hlam))))))
        _ = BA := rfl
    have hnB := (hOB r hru).2 1 (by omega) x
    rw [e1]
    calc ‖iteratedFDeriv ℝ 1 (propagatorW CC r u (fun z => generatorW CC u φ z - generatorW CN u φ z)) x +
          iteratedFDeriv ℝ 1 (propagatorW CC r u (generatorW CN u φ)) x -
          iteratedFDeriv ℝ 1 (propagatorW CN r u (generatorW CN u φ)) x‖
        = ‖iteratedFDeriv ℝ 1 (propagatorW CC r u (fun z => generatorW CC u φ z - generatorW CN u φ z)) x +
          (iteratedFDeriv ℝ 1 (propagatorW CC r u (generatorW CN u φ)) x -
            iteratedFDeriv ℝ 1 (propagatorW CN r u (generatorW CN u φ)) x)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hnB hnA |>.trans (le_of_eq (add_comm _ _)))
  rw [show (fun y => (propagatorW CC r t₀ φ y - propagatorW CN r t₀ φ y) -
      (propagatorW CC r s₀ φ y - propagatorW CN r s₀ φ y)) =
      (fun y => (propagatorW CC r t₀ φ y - propagatorW CC r s₀ φ y) -
      (propagatorW CN r t₀ φ y - propagatorW CN r s₀ φ y)) from by funext y; ring]
  have ht₀T : t₀ ∈ Set.Icc (0 : ℝ) T := ⟨hs0'.trans hst, htT⟩
  have hr₀ : r ∈ Set.Icc (0 : ℝ) t₀ := ⟨hr.1, hr.2.trans hst⟩
  have hsm1 : ∀ (F' : S57pFx θ T n K s M Q ν c ρ A Λc νbar) (t' : ℝ), t' ∈ Set.Icc (0 : ℝ) T → r ∈ Set.Icc (0 : ℝ) t' →
      ContDiff ℝ 1 (propagatorW CC r t' φ) := fun F' t' ht' hrt' => by
    obtain ⟨-, hO⟩ := hCu1 F'.fam.adj hBφ0 hφ1 hφb t' ht'
    exact ((hO r hrt').1).of_le (by exact_mod_cast (by omega : 1 ≤ n + 1))
  have hsm2 : ∀ (F' : S57pFx θ T n KN s M Q νN cN ρN A Λc νbar) (t' : ℝ), t' ∈ Set.Icc (0 : ℝ) T → r ∈ Set.Icc (0 : ℝ) t' →
      ContDiff ℝ 1 (propagatorW CN r t' φ) := fun F' t' ht' hrt' => by
    obtain ⟨-, hO⟩ := hCu1 F'.fam.adj hBφ0 hφ1 hφb t' ht'
    exact ((hO r hrt').1).of_le (by exact_mod_cast (by omega : 1 ≤ n + 1))
  have hC1 : ContDiff ℝ 1 (fun y => propagatorW CC r t₀ φ y - propagatorW CC r s₀ φ y) :=
    (hsm1 Fx t₀ ht₀T hr₀).sub (hsm1 Fx s₀ hsT hr)
  have hN1 : ContDiff ℝ 1 (fun y => propagatorW CN r t₀ φ y - propagatorW CN r s₀ φ y) :=
    (hsm2 FxN t₀ ht₀T hr₀).sub (hsm2 FxN s₀ hsT hr)
  have e : iteratedFDeriv ℝ 1 (fun y => (propagatorW CC r t₀ φ y - propagatorW CC r s₀ φ y) -
      (propagatorW CN r t₀ φ y - propagatorW CN r s₀ φ y)) x =
      iteratedFDeriv ℝ 1 (fun y => propagatorW CC r t₀ φ y - propagatorW CC r s₀ φ y) x -
        iteratedFDeriv ℝ 1 (fun y => propagatorW CN r t₀ φ y - propagatorW CN r s₀ φ y) x :=
    iteratedFDeriv_sub_apply hC1.contDiffAt hN1.contDiffAt
  rw [e, c1, c2, ← intervalIntegral.integral_sub i1 i2]
  have hfin := intervalIntegral.norm_integral_le_of_norm_le_const (a := s₀) (b := t₀) (C := BA + BB)
    (f := fun u => iteratedFDeriv ℝ 1 (propagatorW CC r u (generatorW CC u φ)) x -
      iteratedFDeriv ℝ 1 (propagatorW CN r u (generatorW CN u φ)) x) (fun u hu => by
      rw [Set.uIoc_of_le hst] at hu; exact hpt u hu)
  rw [abs_of_nonneg (sub_nonneg.2 hst)] at hfin
  refine hfin.trans (le_of_eq ?_)
  rw [hBA, hBB]
  ring

end HRS.MS.FixEq
