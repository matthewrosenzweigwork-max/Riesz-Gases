import HRS.MS.SA12X2R36S5A
import HRS.MS.SA12X2R36J
import HRS.MS.SA12X2R36L
import HRS.MS.SA12Z3NearN7E
import HRS.MS.SA12CellR35

/-!
# S.A.12 R36 (SA12X3): `r3_near_cell`

Assembly: finite Leibniz expansion of `jetPair` (S4), the per-term cell bound (S3: weak near/far pairing bounds
from P1 and the cover bounds S1, S2), summation over `(j, idx, i, l)` with `MatBound` (S5A), scale choice (S5A).
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near
  HRS.MH.AdjointRdP HRS.MS.UniqT3

theorem r3_near_cell_gen (d : ℕ) (hd : 1 ≤ d) (s : ℝ)
    (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : (d : ℝ)-2 < s)
    (m : ℕ) (hm : 1 ≤ m) (MB Λ Cb T : ℝ)
    (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) (E : Finset (Fin d → ℤ)) (hE : CoversBall8 E) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ν₀ : ℝ, 0 < ν₀ →
      EucNlBound s m Λ Cb T χ χh E
        (C*(1+ν₀^(-(PDE.thetaOrder d s/(2-PDE.thetaOrder d s)))))
        (ν₀/(8*E.card)) (fun M => PDE.MatBound MB M) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨B, R, hBpos, hR1, hR35⟩ := advected_cutoff_jets d hd (m' + 1) Cb T χ χh hχ
  have hs2' : (d : ℝ) < s + 2 := by linarith
  obtain ⟨C1, hC1, hcell⟩ := sa12x2_cell_term (d := d) (s := s) hd hs0 hsd hs2' m' R (by linarith)
  have hE0 : (1 : ℝ) ≤ E.card := by
    have hne : E.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have h0 : (0 : Euc d) ∈ closedBall (0 : Euc d) 8 := by simp
      have := hE h0
      simp [hne] at this
    exact_mod_cast Finset.card_pos.2 hne
  set Λ' : ℝ := max Λ 0 with hΛ'
  have hΛ'0 : 0 ≤ Λ' := le_max_right _ _
  set Ba : ℝ := 2 ^ (m' + 2) * B * Λ' with hBa
  have hBa0 : 0 ≤ Ba := by positivity
  set Kc : ℝ := sa12x2_Kc d (m' + 1) Ba with hKc
  have hKc0 : 0 ≤ Kc := sa12x2_Kc_nonneg d (m' + 1) Ba
  set Kall : ℝ := 8 * B ^ 2 + 2 * Kc + 2 with hKall
  have hKall0 : 0 ≤ Kall := by positivity
  set S : ℝ := ∑ j ∈ Finset.range (m' + 1 + 1), (Nat.choose (m' + 1) j : ℝ) * ((d : ℝ) ^ j * ((d : ℝ) * d)) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => by positivity
  set X : ℝ := 2 * S * max MB 0 * Kall with hX
  have hX0 : 0 ≤ X := by positivity
  set Cn : ℝ := ∫ k, |r3N1 d s k| with hCn
  have hCn0 : 0 ≤ Cn := integral_nonneg fun _ => abs_nonneg _
  have hg : 0 < (d : ℝ) - s := by linarith
  have hθ : 0 ≤ s + 2 - d := by linarith
  obtain ⟨C, hC0, hCr⟩ := sa12x2_r_choice (g := (d : ℝ) - s) (θ := s + 2 - d) (X := X) (Cn := Cn)
    (C1 := C1) (e := (E.card : ℝ)) hg hθ hX0 hCn0 hC1 hE0
  refine ⟨C, hC0, fun ν0 hν0 => ?_⟩
  obtain ⟨r, hr0, hr1, hrκ, hrA⟩ := hCr ν0 hν0
  have hp : PDE.thetaOrder d s / (2 - PDE.thetaOrder d s) = (s + 2 - d) / ((d : ℝ) - s) := by
    unfold PDE.thetaOrder
    congr 1
    ring
  rw [hp]
  intro b Ψ hb hΨ M hM μ hμ F hF τ hτ z
  have hT0 : 0 ≤ T := hτ.1.trans hτ.2
  -- cutoff regularity
  have hRz := hR35 b Ψ hb hΨ τ hτ
  have hω : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
      HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k))) := fun k _ =>
    ⟨(hRz (cellPt d (z + k))).1.1.continuous,
      sa12x2_advCutoff_hasCompactSupport hT0 hb hΨ hτ hχ.1.2.1 _⟩
  set c0 : Euc d := cellPt d z with hc0
  obtain ⟨⟨hwd, hwhd⟩, hjets, hsupp⟩ := hRz c0
  set w : Euc d → ℝ := advCutoff χ Ψ τ c0 with hw
  set a : Euc d → ℝ := fun y => advCutoff χh Ψ τ c0 y * μ y with ha
  have hw1c : ContDiff ℝ 1 w := hwd.of_le (by exact_mod_cast (show 1 ≤ m' + 1 + 1 by omega))
  have hwcs : HasCompactSupport w := sa12x2_advCutoff_hasCompactSupport hT0 hb hΨ hτ hχ.1.2.1 c0
  -- the density
  have hμ1 : ContDiff ℝ ((m' + 2 : ℕ) : WithTop ℕ∞) μ :=
    hμ.1.of_le (by exact_mod_cast (show m' + 2 ≤ m' + 1 + 3 by omega))
  have hμB : ∀ j ≤ m' + 2, ∀ x, ‖iteratedFDeriv ℝ j μ x‖ ≤ Λ' := fun j hj x =>
    sa12x2_density_jet hμ j (by omega) x
  have hχh1 : ContDiff ℝ ((m' + 2 : ℕ) : WithTop ℕ∞) (advCutoff χh Ψ τ c0) :=
    hwhd.of_le (by exact_mod_cast le_refl _)
  have haC : ContDiff ℝ ((m' + 2 : ℕ) : WithTop ℕ∞) a := hχh1.mul hμ1
  have haB : ∀ j ≤ m' + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ Ba := by
    intro j hj x
    have h := sa12x2_jet_mul_bound (k := m' + 2) (f := advCutoff χh Ψ τ c0) (g := μ) (B := B) (C := Λ')
      hBpos.le hΛ'0 hχh1 hμ1 (fun j hj x => (hjets j (by omega) x).2) hμB j hj x
    refine h.trans ?_
    have : (2 : ℝ) ^ j ≤ 2 ^ (m' + 2) := pow_le_pow_right₀ (by norm_num) hj
    rw [hBa]
    gcongr
  -- supports
  have hsupp' : tsupport a ⊆ closedBall (Ψ τ c0) R := by
    refine closure_minimal ?_ isClosed_closedBall
    intro y hy
    exact hsupp (Function.support_mul_subset_left _ _ hy)
  have hwsup : tsupport w ⊆ closedBall (Ψ τ c0) R := by
    refine closure_minimal ?_ isClosed_closedBall
    intro y hy
    exact hsupp (sa12z3_adv_support_le hχ Ψ τ c0 hy)
  have hacs : HasCompactSupport a :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (Ψ τ c0) R)
      (fun y hy => hsupp' (subset_tsupport _ hy))
  have hWc : Continuous (sa12z3_W E χ Ψ τ z) := by
    unfold sa12z3_W
    exact continuous_finsetSum _ fun k hk => ((hω k hk).1).pow 2
  have hWa : ∀ x ∈ tsupport a, 1 ≤ sa12z3_W E χ Ψ τ z x := by
    have hcl : IsClosed {x | 1 ≤ sa12z3_W E χ Ψ τ z x} := isClosed_le continuous_const hWc
    refine fun x hx => (closure_minimal ?_ hcl : tsupport a ⊆ _) hx
    intro y hy
    have hy' : advCutoff χh Ψ τ c0 y ≠ 0 := left_ne_zero_of_mul hy
    have := sa12z3_advh_ne_norm_lt hχ Ψ τ c0 hy'
    exact sa12z3_W_ge_one hχ hE Ψ τ z y this.le
  have hwW : ∀ x, w x ≠ 0 → 1 ≤ sa12z3_W E χ Ψ τ z x := by
    intro x hx
    have := sa12z3_adv_ne_norm_lt hχ Ψ τ c0 hx
    exact sa12z3_W_ge_one hχ hE Ψ τ z x (by linarith)
  have hw1 : ∀ x, |w x| ≤ 1 := by
    intro x
    have h : w x ∈ Icc (0 : ℝ) 1 := hχ.1.2.2.2.1 (Function.invFun (Ψ τ) x - c0)
    exact abs_le.2 ⟨by linarith [h.1], h.2⟩
  have hwB : ∀ x, ‖fderiv ℝ w x‖ ≤ B := fun x => by
    rw [← norm_iteratedFDeriv_one]
    exact (hjets 1 (by omega) x).1
  -- the expansion and the per-term bound
  rw [sa12x2_jetPair_expand hs0 hsd M haC hacs hF.1 hwd.continuous hwcs]
  have hκ : ∫ h, |r3Kn d s r h| = Cn * r ^ ((d : ℝ) - s) := r3Kn_l1 hd s hr0
  have hEn : 0 ≤ ∑ k ∈ E, cellEnergy (m' + 1) χ Ψ τ (cellPt d (z + k)) F :=
    Finset.sum_nonneg fun k _ => sa12x2_cellEnergy_nonneg (m' + 1) χ Ψ τ _ F
  have hDi : 0 ≤ ∑ k ∈ E, cellDissip (m' + 1) χ Ψ τ (cellPt d (z + k)) F :=
    Finset.sum_nonneg fun k _ => sa12x2_cellDissip_nonneg (m' + 1) χ Ψ τ _ F
  set En := ∑ k ∈ E, cellEnergy (m' + 1) χ Ψ τ (cellPt d (z + k)) F with hEn_def
  set Di := ∑ k ∈ E, cellDissip (m' + 1) χ Ψ τ (cellPt d (z + k)) F with hDi_def
  set P : ℝ := (Cn * r ^ ((d : ℝ) - s)) * (Kall * (En + Di)) +
    C1 * r ^ (-(s + 2 - d)) * (Kall * En) with hP
  have hrr : 0 ≤ r ^ ((d : ℝ) - s) := Real.rpow_nonneg hr0.le _
  have hrt : 0 ≤ r ^ (-(s + 2 - d)) := Real.rpow_nonneg hr0.le _
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hsum := sa12x2_sum_bound (m := m' + 1) (M := M) (MB := MB) (P := P) (fun i j => hM i j) hP0
    (fun j idx i l => ∫ x, (w x ^ 2 * partialDeriv idx F x) *
      firstRiesz d s i (partialDeriv idx (fun y => a y * D1 l F y)) x)
    (by
      intro j hj idx i l
      have h := hcell r hr0 hr1 hF.1 hω (c := Ψ τ c0) (w := w) (a := a) (B := Ba) (B1 := B) hBa0 hBpos.le
        haC haB hsupp' hWa hw1c hwcs hw1 hwB hwsup hwW j hj idx i l
      rw [hκ] at h
      exact h)
  refine hsum.trans ?_
  have hXeq : 2 * S * max MB 0 * P =
      X * Cn * r ^ ((d : ℝ) - s) * (En + Di) + X * C1 * r ^ (-(s + 2 - d)) * En := by
    rw [hP, hX]; ring
  rw [hXeq]
  have e1 := mul_le_mul_of_nonneg_right hrκ hDi
  have e2 := mul_le_mul_of_nonneg_right hrA hEn
  nlinarith [e1, e2]

theorem r3_near_cell (d : ℕ) (hd : 1 ≤ d) (s : ℝ)
    (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : (d : ℝ)-2 < s)
    (m : ℕ) (hm : 1 ≤ m) (MB Λ Cb T : ℝ)
    (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (E : Finset (Fin d → ℤ)) (C : ℝ), CoversBall8 E ∧ 0 ≤ C ∧
      ∀ ν₀ : ℝ, 0 < ν₀ →
      EucNlBound s m Λ Cb T χ χh E
        (C*(1+ν₀^(-(PDE.thetaOrder d s/(2-PDE.thetaOrder d s)))))
        (ν₀/(8*E.card)) (fun M => PDE.MatBound MB M) := by
  obtain ⟨E, hE⟩ := sa12z3_E_exists hd
  obtain ⟨C, hC0, hC⟩ := r3_near_cell_gen d hd s hs0 hsd hs2 m hm MB Λ Cb T χ χh hχ E hE
  exact ⟨E, C, hE, hC0, hC⟩

end HRS.MH.AdjointRd.Phase2SA12
