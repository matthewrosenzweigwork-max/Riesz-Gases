import HRS.MS.SA12X5N4

/-!
# S.A.12 X5 N5: the near operator applied to a small density, in cell-energy form
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3 HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near
  HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRdP

variable {d : ℕ}

theorem sa12x5_Y_mono {n m : ℕ} (h : n ≤ m) (F : Euc d → ℝ) (x : Euc d) :
    sa12z3_Y n F x ≤ sa12z3_Y m F x := by
  unfold sa12z3_Y
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
    fun r _ _ => Finset.sum_nonneg fun γ _ => sq_nonneg _

theorem sa12x5_near_cell (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (Cb T : ℝ)
    (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) (E : Finset (Fin d → ℤ)) (hE : CoversBall8 E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T,
      ∀ (M : Matrix (Fin d) (Fin d) ℝ) (MB : ℝ), PDE.MatBound MB M → ∀ (a F : Euc d → ℝ),
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ F → ∀ A : ℝ, 0 ≤ A →
      (∀ j ≤ m + 1, ∀ y, ‖iteratedFDeriv ℝ j a y‖ ≤ A) →
      ∀ z : Fin d → ℤ, ∀ n ≤ m, ∀ idx : Fin n → Fin d,
        ∫ x, (advCutoff χ Ψ τ (cellPt d z) x * partialDeriv idx
          (eucNonlocal s M (fun y => advCutoff χh Ψ τ (cellPt d z) y * a y) F) x) ^ 2 ≤
          C * MB ^ 2 * A ^ 2 * ∑ k ∈ E, cellEnergy (m + 2) χ Ψ τ (cellPt d (z + k)) F := by
  obtain ⟨B, R, hBpos, hR1, hR35⟩ := advected_cutoff_jets d hd m Cb T χ χh hχ
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set CK : ℝ := ∫ u in closedBall (0 : Euc d) (R + R), |rieszKernel d s u| with hCKdef
  have hCK0 : 0 ≤ CK := integral_nonneg fun u => abs_nonneg _
  set cN : ℝ := 4 ^ (m + 1) * (d : ℝ) ^ (m + 2) with hcN
  have hcN0 : 0 ≤ cN := by positivity
  refine ⟨(d : ℝ) ^ 4 * CK ^ 2 * (cN * (2 ^ (m + 1) * B) ^ 2), by positivity, ?_⟩
  intro b Ψ hb hΨ τ hτ M MB hM a F ha hF A hA0 hA z n hn idx
  have hT0 : 0 ≤ T := hτ.1.trans hτ.2
  have hRz := hR35 b Ψ hb hΨ τ hτ
  have hω : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
      HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k))) := fun k _ =>
    ⟨(hRz (cellPt d (z + k))).1.1.continuous,
      sa12x2_advCutoff_hasCompactSupport hT0 hb hΨ hτ hχ.1.2.1 _⟩
  set c0 : Euc d := cellPt d z with hc0
  obtain ⟨⟨hwd, hwhd⟩, hjets, hsupp⟩ := hRz c0
  set w : Euc d → ℝ := advCutoff χ Ψ τ c0 with hw
  set a' : Euc d → ℝ := fun y => advCutoff χh Ψ τ c0 y * a y with ha'def
  have ha1 : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) a :=
    ha.of_le (by exact_mod_cast (le_top : ((m + 1 : ℕ) : ℕ∞) ≤ ⊤))
  have ha'C : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) a' := hwhd.mul ha1
  set Ba : ℝ := 2 ^ (m + 1) * B * A with hBa
  have hBa0 : 0 ≤ Ba := by positivity
  have ha'B : ∀ r ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ r a' x‖ ≤ Ba := by
    intro r hr x
    have h := sa12x2_jet_mul_bound (k := m + 1) (f := advCutoff χh Ψ τ c0) (g := a) (B := B) (C := A)
      hBpos.le hA0 hwhd ha1 (fun j hj x => (hjets j hj x).2) hA r hr x
    refine h.trans ?_
    have : (2 : ℝ) ^ r ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) hr
    rw [hBa]
    gcongr
  have hsupp' : Function.support a' ⊆ closedBall (Ψ τ c0) R :=
    (Function.support_mul_subset_left _ _).trans hsupp
  have hacs : HasCompactSupport a' :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (Ψ τ c0) R) hsupp'
  have hws : Function.support w ⊆ closedBall (Ψ τ c0) R :=
    (sa12z3_adv_support_le hχ Ψ τ c0).trans hsupp
  have hw1 : ∀ x, |w x| ≤ 1 := by
    intro x
    have h : w x ∈ Icc (0 : ℝ) 1 := hχ.1.2.2.2.1 (Function.invFun (Ψ τ) x - c0)
    exact abs_le.2 ⟨by linarith [h.1], h.2⟩
  have hWc : Continuous (sa12z3_W E χ Ψ τ z) := by
    unfold sa12z3_W
    exact continuous_finsetSum _ fun k hk => ((hω k hk).1).pow 2
  have hWa : ∀ x ∈ tsupport a', 1 ≤ sa12z3_W E χ Ψ τ z x := by
    have hcl : IsClosed {x | 1 ≤ sa12z3_W E χ Ψ τ z x} := isClosed_le continuous_const hWc
    refine fun x hx => (closure_minimal ?_ hcl : tsupport a' ⊆ _) hx
    intro y hy
    have hy' : advCutoff χh Ψ τ c0 y ≠ 0 := left_ne_zero_of_mul hy
    have := sa12z3_advh_ne_norm_lt hχ Ψ τ c0 hy'
    exact sa12z3_W_ge_one hχ hE Ψ τ z y this.le
  have hDF : ∀ l : Fin d, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (D1 l F) := fun l =>
    ((hF.fderiv_right (m := ∞) (by simp)).of_le (by exact_mod_cast le_top)).clm_apply contDiff_const
  have hg : ∀ l : Fin d, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => a' y * D1 l F y) :=
    fun l => ha'C.mul (hDF l)
  have hgc : ∀ l : Fin d, HasCompactSupport (fun y => a' y * D1 l F y) := fun l => hacs.mul_right
  have hV : ∀ i l : Fin d, ∫ x, partialDeriv (Fin.cons i idx : Fin (n + 1) → Fin d)
      (fun y => a' y * D1 l F y) x ^ 2 ≤ cN * Ba ^ 2 * ∑ k ∈ E, cellEnergy (m + 2) χ Ψ τ (cellPt d (z + k)) F := by
    intro i l
    have hvcont : Continuous (partialDeriv (Fin.cons i idx : Fin (n + 1) → Fin d)
        (fun y => a' y * D1 l F y)) := by
      have := sa12z3_pd_contDiff (k := m + 1) (n := n + 1) (hg l) (by omega) (Fin.cons i idx)
      exact this.continuous
    have hvcs := sa12z3_pd_compact (hgc l) (Fin.cons i idx : Fin (n + 1) → Fin d)
    have h := sa12x2_cover_gen (m + 2) hF hω (K1 := cN * Ba ^ 2) (K2 := 0) (by positivity) le_rfl
      (f := partialDeriv (Fin.cons i idx : Fin (n + 1) → Fin d) (fun y => a' y * D1 l F y))
      hvcont hvcs
      (fun x => by
        have h1 := sa12x5_pd_prod_le hd (N := n + 1) (a' := a') (F := F)
          (ha'C.of_le (by exact_mod_cast (by omega : n + 1 ≤ m + 1))) hBa0
          (fun r hr x => ha'B r (by omega) x) hF l (Fin.cons i idx) x
        have h2 := sa12x5_Y_mono (by omega : n + 1 + 1 ≤ m + 2) F x
        have h3 : (4 : ℝ) ^ (n + 1) * (d : ℝ) ^ (n + 1 + 1) ≤ cN := by
          rw [hcN]
          exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega))
            (pow_le_pow_right₀ hd1 (by omega)) (by positivity) (by positivity)
        have h4 := sa12z3_Y_nonneg (n + 1 + 1) F x
        have h5 := sa12x2_Yd_nonneg (m + 2) F x
        calc _ ≤ (4 ^ (n + 1) * (d : ℝ) ^ (n + 1 + 1)) * Ba ^ 2 * sa12z3_Y (n + 1 + 1) F x := h1
          _ ≤ cN * Ba ^ 2 * sa12z3_Y (m + 2) F x := by
              gcongr
          _ = _ := by ring)
      (fun x hx => by
        refine hWa x ?_
        have h1 := sa12z3_pd_support (Fin.cons i idx : Fin (n + 1) → Fin d)
          (f := fun y => a' y * D1 l F y) (Function.mem_support.2 hx)
        exact tsupport_mul_subset_left h1)
    simpa using h
  have hy := sa12x5_near_young hd hs0 hsd M hM (m := m) (a' := a') (F := F) (w := w) (c := Ψ τ c0) (R := R)
    ha'C hacs hF hwd.continuous hws hw1 hsupp' (CK := CK)
    (V := cN * Ba ^ 2 * ∑ k ∈ E, cellEnergy (m + 2) χ Ψ τ (cellPt d (z + k)) F) le_rfl hn idx hV
  refine hy.trans (le_of_eq ?_)
  rw [hBa]
  ring

end HRS.MH.AdjointRd.Phase2SA12X5
