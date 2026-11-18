import HRS.MS.SA12X5N6

/-!
# S.A.12 X5 N7: the smooth part of the near identity applied to a small density, in cell-energy form
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

theorem sa12x5_smooth_cell (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (m : ℕ) (Cb T : ℝ)
    (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) (E : Finset (Fin d → ℤ)) (hE : CoversBall8 E)
    (q : Euc d → ℝ) (hq : ContDiff ℝ ∞ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T,
      ∀ (M : Matrix (Fin d) (Fin d) ℝ) (MB : ℝ), PDE.MatBound MB M → ∀ (a F : Euc d → ℝ),
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ F → ∀ A : ℝ, 0 ≤ A →
      (∀ j ≤ m + 1, ∀ y, ‖iteratedFDeriv ℝ j a y‖ ≤ A) →
      ∀ z : Fin d → ℤ, ∀ n ≤ m, ∀ idx : Fin n → Fin d, ∀ L : ℝ, 1 ≤ L →
        ∫ x, (advCutoff χ Ψ τ (cellPt d z) x * partialDeriv idx (fun x => ∑ i : Fin d, ∑ j : Fin d,
          M j i * (L ^ (-s - 1) * ∫ y, fderiv ℝ q (L⁻¹ • (x - y)) (EuclideanSpace.single i (1 : ℝ)) *
            (advCutoff χh Ψ τ (cellPt d z) y * a y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))))) x) ^ 2 ≤
          C * MB ^ 2 * A ^ 2 * ∑ k ∈ E, cellEnergy (m + 2) χ Ψ τ (cellPt d (z + k)) F := by
  obtain ⟨B, R, hBpos, hR1, hR35⟩ := advected_cutoff_jets d hd m Cb T χ χh hχ
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨Cq0, hCq0⟩ := (isCompact_closedBall (0 : Euc d) (R + R)).exists_bound_of_continuousOn
    (hq.continuous_fderiv (by simp)).continuousOn
  set Cq : ℝ := max Cq0 0 with hCq
  have hCq0' : 0 ≤ Cq := le_max_right _ _
  set CK : ℝ := Cq * (volume (closedBall (0 : Euc d) (R + R))).toReal with hCKdef
  have hCK0 : 0 ≤ CK := by positivity
  set cN : ℝ := 4 ^ (m + 1) * (d : ℝ) ^ (m + 2) with hcN
  have hcN0 : 0 ≤ cN := by positivity
  refine ⟨(d : ℝ) ^ 4 * CK ^ 2 * (cN * (2 ^ (m + 1) * B) ^ 2), by positivity, ?_⟩
  intro b Ψ hb hΨ τ hτ M MB hM a F ha hF A hA0 hA z n hn idx L hL
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
  have hV : ∀ l : Fin d, ∫ x, partialDeriv idx (fun y => a' y * D1 l F y) x ^ 2 ≤
      cN * Ba ^ 2 * ∑ k ∈ E, cellEnergy (m + 2) χ Ψ τ (cellPt d (z + k)) F := by
    intro l
    have hvcont : Continuous (partialDeriv idx (fun y => a' y * D1 l F y)) := by
      have := sa12z3_pd_contDiff (k := m + 1) (n := n) (hg l) (by omega) idx
      exact this.continuous
    have hvcs := sa12z3_pd_compact (hgc l) idx
    have h := sa12x2_cover_gen (m + 2) hF hω (K1 := cN * Ba ^ 2) (K2 := 0) (by positivity) le_rfl
      (f := partialDeriv idx (fun y => a' y * D1 l F y)) hvcont hvcs
      (fun x => by
        have h1 := sa12x5_pd_prod_le hd (N := n) (a' := a') (F := F)
          (ha'C.of_le (by exact_mod_cast (by omega : n ≤ m + 1))) hBa0
          (fun r hr x => ha'B r (by omega) x) hF l idx x
        have h2 := sa12x5_Y_mono (by omega : n + 1 ≤ m + 2) F x
        have h3 : (4 : ℝ) ^ n * (d : ℝ) ^ (n + 1) ≤ cN := by
          rw [hcN]
          exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega))
            (pow_le_pow_right₀ hd1 (by omega)) (by positivity) (by positivity)
        have h4 := sa12z3_Y_nonneg (n + 1) F x
        have h5 := sa12x2_Yd_nonneg (m + 2) F x
        calc _ ≤ (4 ^ n * (d : ℝ) ^ (n + 1)) * Ba ^ 2 * sa12z3_Y (n + 1) F x := h1
          _ ≤ cN * Ba ^ 2 * sa12z3_Y (m + 2) F x := by
              gcongr
          _ = _ := by ring)
      (fun x hx => by
        refine hWa x ?_
        have h1 := sa12z3_pd_support idx (f := fun y => a' y * D1 l F y) (Function.mem_support.2 hx)
        exact tsupport_mul_subset_left h1)
    simpa using h
  -- the kernels
  set kk : Fin d → Euc d → ℝ := fun i u => L ^ (-s - 1) *
    fderiv ℝ q (L⁻¹ • u) (EuclideanSpace.single i (1 : ℝ)) with hkk
  have hkc : ∀ i, Continuous (kk i) := fun i =>
    continuous_const.mul (((hq.continuous_fderiv (by simp)).comp (continuous_const_smul L⁻¹)).clm_apply
      continuous_const)
  have hLs : L ^ (-s - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hLs0 : 0 ≤ L ^ (-s - 1) := Real.rpow_nonneg (by linarith) _
  have hCKi : ∀ i, ∫ u in closedBall (0 : Euc d) (R + R), |kk i u| ≤ CK := by
    intro i
    have hb : ∀ u ∈ closedBall (0 : Euc d) (R + R), ‖|kk i u|‖ ≤ Cq := by
      intro u hu
      rw [Real.norm_eq_abs, abs_abs]
      have hu' : ‖L⁻¹ • u‖ ≤ R + R := by
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < L)]
        have : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
        have hu2 : ‖u‖ ≤ R + R := by simpa using hu
        calc L⁻¹ * ‖u‖ ≤ 1 * ‖u‖ := by gcongr
          _ ≤ _ := by linarith
      have h1 : ‖fderiv ℝ q (L⁻¹ • u)‖ ≤ Cq0 := hCq0 _ (by simpa using hu')
      have h2 : |fderiv ℝ q (L⁻¹ • u) (EuclideanSpace.single i (1 : ℝ))| ≤ Cq := by
        have := (fderiv ℝ q (L⁻¹ • u)).le_opNorm (EuclideanSpace.single i (1 : ℝ))
        rw [Real.norm_eq_abs] at this
        simp only [PiLp.norm_single, norm_one, mul_one] at this
        exact this.trans (h1.trans (le_max_left _ _))
      simp only [hkk, abs_mul, abs_of_nonneg hLs0]
      calc L ^ (-s - 1) * |fderiv ℝ q (L⁻¹ • u) (EuclideanSpace.single i (1 : ℝ))| ≤ 1 * Cq :=
            mul_le_mul hLs h2 (abs_nonneg _) zero_le_one
        _ = Cq := one_mul _
    have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Euc d)))
      (s := closedBall (0 : Euc d) (R + R)) (C := Cq) measure_closedBall_lt_top
      (f := fun u => |kk i u|) hb
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    simpa [hCKdef, Measure.real, mul_comm] using this
  have hy := sa12x5_conv_young_gen hd hkc M hM (m := m) (a' := a') (F := F) (w := w) (c := Ψ τ c0) (R := R)
    ha'C hacs hF hwd.continuous hws hw1 hsupp' (CK := CK)
    (V := cN * Ba ^ 2 * ∑ k ∈ E, cellEnergy (m + 2) χ Ψ τ (cellPt d (z + k)) F) hCKi hn idx hV
  have hfun : (fun x => ∑ i : Fin d, ∑ j : Fin d,
          M j i * (L ^ (-s - 1) * ∫ y, fderiv ℝ q (L⁻¹ • (x - y)) (EuclideanSpace.single i (1 : ℝ)) *
            (advCutoff χh Ψ τ (cellPt d z) y * a y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))))) =
      fun x => ∑ i : Fin d, ∑ l : Fin d, M l i *
        HRS.Whole.convFun (kk i) (fun y => a' y * D1 l F y) x := by
    funext x
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    unfold HRS.Whole.convFun
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hkk, ha'def, D1]
    ring
  rw [hfun]
  refine hy.trans (le_of_eq ?_)
  rw [hBa]
  ring

end HRS.MH.AdjointRd.Phase2SA12X5
