import HRS.MS.SA12X3C7B4

/-!
# S.A.12 C7 (SA12X3), part B5 (7B): the smooth-kernel term, energy-level pairing bound

`-2 jetPair m w F S ≤ AS · max MB 0 · Λ₀ · ∑_{k∈E} cellEnergy` for
`S x = ∑_{ij} M_{ji} L^{-s-1} ∫ ∂_i q(L⁻¹(x-y)) (η μ ∂_jF)(y) dy`, uniformly in `L ≥ 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MS.UniqT3 HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3_pd_one (F : Euc d → ℝ) (j : Fin d) (x : Euc d) :
    partialDeriv (fun _ : Fin 1 => j) F x = fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ)) := by
  unfold partialDeriv
  rw [iteratedFDeriv_one_apply]

theorem sa12x3_smooth_pairing {q : Euc d → ℝ} (hq : ContDiff ℝ ∞ q) (m : ℕ) (hm : 1 ≤ m) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ AS : ℝ, 0 ≤ AS ∧ ∀ (s L : ℝ), 0 ≤ s → 1 ≤ L → ∀ (M : Matrix (Fin d) (Fin d) ℝ) (MB Λ0 : ℝ),
      (∀ i j, |M i j| ≤ MB) → ∀ (c : Euc d) (E : Finset (Fin d → ℤ)) (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d)
      (τ : ℝ) (z : Fin d → ℤ) (F : Euc d → ℝ), ContDiff ℝ ∞ F →
      (∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
        HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k)))) →
      ∀ (w η μ : Euc d → ℝ), Continuous w → HasCompactSupport w → (∀ x, |w x| ≤ 1) →
      tsupport w ⊆ ball c ρ → (∀ x, w x ≠ 0 → 1 ≤ sa12z3_W E χ Ψ τ z x) →
      ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) η → (∀ x, 0 ≤ η x) → (∀ x, η x ≤ 1) → tsupport η ⊆ ball c ρ →
      (∀ x, η x ≠ 0 → 1 ≤ sa12z3_W E χ Ψ τ z x) → ContDiff ℝ ∞ μ → (∀ x, |μ x| ≤ Λ0) →
        ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => ∑ i : Fin d, ∑ j : Fin d, M j i * (L ^ (-s - 1) *
          ∫ y, fderiv ℝ q (L⁻¹ • (x - y)) (EuclideanSpace.single i (1 : ℝ)) *
            (η y * μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))))) ∧
        -(2 * jetPair m w F (fun x => ∑ i : Fin d, ∑ j : Fin d, M j i * (L ^ (-s - 1) *
          ∫ y, fderiv ℝ q (L⁻¹ • (x - y)) (EuclideanSpace.single i (1 : ℝ)) *
            (η y * μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))))) ≤
          AS * max MB 0 * Λ0 * ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F := by
  obtain ⟨Kk, hKk0, hKk⟩ := sa12x3_smooth_pd hq m hρ
  set V : ℝ := (volume (ball (0 : Euc d) ρ)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set S0 : ℝ := ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j with hS0
  have hS00 : 0 ≤ S0 := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨2 * S0 * Kk * (d : ℝ) ^ 2 * V, by positivity, ?_⟩
  intro s L hs0 hL M MB Λ0 hM c E χ Ψ τ z F hF hω w η μ hw hwc hw1 hwsup hwW hη hη0 hη1 hηs hηW hμ hμb
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hΛ0 : 0 ≤ Λ0 := (abs_nonneg _).trans (hμb 0)
  have hMB0 : ∀ i j, |M i j| ≤ max MB 0 := fun i j => (hM i j).trans (le_max_left _ _)
  have hLs : L ^ (-s - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hLs0 : 0 ≤ L ^ (-s - 1) := Real.rpow_nonneg hL0.le _
  set En := ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F with hEn
  have hEn0 : 0 ≤ En := Finset.sum_nonneg fun k _ => sa12x2_cellEnergy_nonneg m χ Ψ τ _ F
  have hVb : (volume (ball c ρ)).toReal = V := by rw [hV, Measure.addHaar_ball_center]
  -- the pieces G_j = η μ ∂_jF
  set G : Fin d → Euc d → ℝ := fun j y => η y * μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)) with hG
  have hGs : ∀ j, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (G j) := fun j =>
    (hη.mul (hμ.of_le (sa12x2_le_top _))).mul
      (((hF.of_le (sa12x2_le_top (m + 2))).fderiv_right (m := ((m + 1 : ℕ) : WithTop ℕ∞))
        (by exact_mod_cast le_refl _)).clm_apply contDiff_const)
  have hGsup : ∀ j, tsupport (G j) ⊆ ball c ρ := fun j =>
    (tsupport_mul_subset_left (f := fun y => η y * μ y)).trans
      ((tsupport_mul_subset_left (f := η) (g := μ)).trans hηs)
  have hGcs : ∀ j, HasCompactSupport (G j) := fun j =>
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c ρ)
      fun y hy => ball_subset_closedBall (hGsup j (subset_tsupport _ hy))
  -- (F2): ∫ η (∂_jF)^2 ≤ En
  have hF2 : ∀ j : Fin d, ∫ x, (Real.sqrt (η x) * fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) ^ 2 ≤ En := by
    intro j
    have hsq : Continuous (fun x => Real.sqrt (η x)) := Real.continuous_sqrt.comp hη.continuous
    have hdc : Continuous (fun x => fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) :=
      ((hF.fderiv_right (m := ∞) (by simp)).continuous).clm_apply continuous_const
    have hcs : HasCompactSupport (fun x => Real.sqrt (η x) * fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) := by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c ρ) fun y hy => ?_
      have : η y ≠ 0 := fun h0 => hy (by simp [h0])
      exact ball_subset_closedBall (hηs (subset_tsupport _ (Function.mem_support.2 this)))
    have := sa12x2_cover_gen m hF hω (K1 := 1) (K2 := 0) zero_le_one le_rfl
      (f := fun x => Real.sqrt (η x) * fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) (hsq.mul hdc) hcs
      (fun x => by
        have h1 := sa12x2_sq_le_Y (m := m) (n := 1) hm F (fun _ => j) x
        rw [sa12x3_pd_one] at h1
        have h3 := sa12x2_Yd_nonneg m F x
        have : (Real.sqrt (η x) * fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) ^ 2 =
            η x * (fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (hη0 x)]
        rw [this]
        have := mul_le_mul (hη1 x) h1 (sq_nonneg _) zero_le_one
        nlinarith)
      (fun x hx => hηW x (fun h0 => hx (by simp [h0])))
    simpa using this
  -- (F3): ∫ |G_j| ≤ Λ0 √V √En
  have hηV : ∫ x, Real.sqrt (η x) ^ 2 ≤ V := by
    have : ∫ x, Real.sqrt (η x) ^ 2 = ∫ x, η x := by simp only [Real.sq_sqrt (hη0 _)]
    rw [this, ← hVb]
    exact sa12x3_int_le_vol hη.continuous hη0 hη1 fun x hx => by
      by_contra h0
      exact hx (hηs (subset_tsupport _ h0))
  have hG1 : ∀ j : Fin d, ∫ y, |G j y| ≤ Λ0 * (Real.sqrt V * Real.sqrt En) := by
    intro j
    have hdc : Continuous (fun x => fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) :=
      ((hF.fderiv_right (m := ∞) (by simp)).continuous).clm_apply continuous_const
    have hsq : Continuous (fun x => Real.sqrt (η x)) := Real.continuous_sqrt.comp hη.continuous
    have hcs : HasCompactSupport (fun x => Real.sqrt (η x) * fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) := by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c ρ) fun y hy => ?_
      have : η y ≠ 0 := fun h0 => hy (by simp [h0])
      exact ball_subset_closedBall (hηs (subset_tsupport _ (Function.mem_support.2 this)))
    have hcs' : HasCompactSupport (fun x => Real.sqrt (η x)) := by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c ρ) fun y hy => ?_
      have : η y ≠ 0 := fun h0 => hy (by simp [h0])
      exact ball_subset_closedBall (hηs (subset_tsupport _ (Function.mem_support.2 this)))
    have hcsb := sa12x3_cs hsq hcs' (hsq.mul hdc) hcs hηV (hF2 j)
    have hpt : ∀ y, |G j y| ≤ Λ0 * (|Real.sqrt (η y)| * |Real.sqrt (η y) * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))|) := by
      intro y
      have hs := Real.sq_sqrt (hη0 y)
      have hs0 := Real.sqrt_nonneg (η y)
      simp only [hG, abs_mul, abs_of_nonneg hs0, abs_of_nonneg (hη0 y)]
      calc η y * |μ y| * |fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))|
          ≤ η y * Λ0 * |fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hμb y) (hη0 y)) (abs_nonneg _)
        _ = Λ0 * ((Real.sqrt (η y) * Real.sqrt (η y)) * |fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))|) := by
            rw [Real.mul_self_sqrt (hη0 y)]; ring
        _ = Λ0 * (Real.sqrt (η y) * (Real.sqrt (η y) * |fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))|)) := by
            ring
    have hGint : Integrable (fun y => |G j y|) :=
      ((hGs j).continuous.abs).integrable_of_hasCompactSupport (hGcs j).abs
    have hmaj : Integrable (fun y => Λ0 * (|Real.sqrt (η y)| *
        |Real.sqrt (η y) * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))|)) := by
      refine Continuous.integrable_of_hasCompactSupport
        (continuous_const.mul (hsq.abs.mul (hsq.mul hdc).abs)) ?_
      refine HasCompactSupport.intro (K := closedBall c ρ) (isCompact_closedBall c ρ) fun y hy => ?_
      have : η y = 0 := by
        by_contra h0
        exact hy (ball_subset_closedBall (hηs (subset_tsupport _ h0)))
      simp [this]
    calc ∫ y, |G j y| ≤ ∫ y, Λ0 * (|Real.sqrt (η y)| *
          |Real.sqrt (η y) * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))|) :=
          integral_mono hGint hmaj hpt
      _ = Λ0 * ∫ y, |Real.sqrt (η y)| * |Real.sqrt (η y) * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))| :=
          integral_const_mul _ _
      _ ≤ Λ0 * (Real.sqrt V * Real.sqrt En) := mul_le_mul_of_nonneg_left hcsb hΛ0
  -- the kernel pieces
  have hk : ∀ i : Fin d, Continuous (fun u => fderiv ℝ q (L⁻¹ • u) (EuclideanSpace.single i (1 : ℝ))) := fun i =>
    ((hq.continuous_fderiv (by simp)).comp (continuous_id.const_smul L⁻¹)).clm_apply continuous_const
  set Sij : Fin d → Fin d → Euc d → ℝ := fun i j x =>
    ∫ y, fderiv ℝ q (L⁻¹ • (x - y)) (EuclideanSpace.single i (1 : ℝ)) * G j y with hSij
  have hSs : ∀ i j, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Sij i j) := fun i j => sa12x3_conv_smooth (hk i).locallyIntegrable (hGs j) (hGcs j)
  set Sf : Euc d → ℝ := fun x => ∑ i : Fin d, ∑ j : Fin d, M j i * (L ^ (-s - 1) * Sij i j x) with hSf
  have hSfs : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Sf := ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    contDiff_const.mul (contDiff_const.mul (hSs i j))
  refine ⟨hSfs, ?_⟩
  have hSfn : ∀ (n : ℕ), n ≤ m → ∀ (idx : Fin n → Fin d) (x : Euc d), partialDeriv idx Sf x =
      ∑ i : Fin d, ∑ j : Fin d, M j i * (L ^ (-s - 1) * partialDeriv idx (Sij i j) x) := by
    intro n hn idx x
    have hcd : ∀ i j, ContDiff ℝ n (Sij i j) := fun i j => (hSs i j).of_le (by exact_mod_cast (by omega : n ≤ m + 1))
    have hSeq : Sf = fun y => ∑ i ∈ (Finset.univ : Finset (Fin d)),
        (fun _ => (1 : ℝ)) i * (fun i y => ∑ j : Fin d, (M j i * L ^ (-s - 1)) * Sij i j y) i y := by
      funext y
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [one_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hSeq, sa12z3_pd_sum (Finset.univ : Finset (Fin d)) (fun i y => ∑ j : Fin d, (M j i * L ^ (-s - 1)) *
      Sij i j y) (fun _ => 1) (n := n) (fun i _ => ContDiff.sum fun j _ => contDiff_const.mul (hcd i j)) idx x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_mul, sa12z3_pd_sum (Finset.univ : Finset (Fin d)) (fun j y => Sij i j y)
      (fun j => M j i * L ^ (-s - 1)) (n := n) (fun j _ => hcd i j) idx x]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- pointwise bound of the derivatives of S on the ball
  set Bd : ℝ := max MB 0 * Kk * (d : ℝ) ^ 2 * (Λ0 * (Real.sqrt V * Real.sqrt En)) with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  have hpdS : ∀ n ≤ m, ∀ (idx : Fin n → Fin d), ∀ x ∈ ball c ρ, |partialDeriv idx Sf x| ≤ Bd := by
    intro n hn idx x hx
    rw [hSfn n hn idx x]
    have hterm : ∀ i j : Fin d, |M j i * (L ^ (-s - 1) * partialDeriv idx (Sij i j) x)| ≤
        max MB 0 * Kk * (Λ0 * (Real.sqrt V * Real.sqrt En)) := by
      intro i j
      have h1 := hKk L hL i c (G j) (hGs j).continuous (hGsup j) n hn idx x hx
      have h2 := hG1 j
      rw [abs_mul, abs_mul, abs_of_nonneg hLs0]
      have h3 : |partialDeriv idx (Sij i j) x| ≤ Kk * (Λ0 * (Real.sqrt V * Real.sqrt En)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hKk0)
      have h4 : L ^ (-s - 1) * |partialDeriv idx (Sij i j) x| ≤ Kk * (Λ0 * (Real.sqrt V * Real.sqrt En)) :=
        (mul_le_mul hLs h3 (abs_nonneg _) zero_le_one).trans (by rw [one_mul])
      calc |M j i| * (L ^ (-s - 1) * |partialDeriv idx (Sij i j) x|)
          ≤ max MB 0 * (Kk * (Λ0 * (Real.sqrt V * Real.sqrt En))) :=
            mul_le_mul (hMB0 j i) h4 (mul_nonneg hLs0 (abs_nonneg _)) (le_max_right _ _)
        _ = max MB 0 * Kk * (Λ0 * (Real.sqrt V * Real.sqrt En)) := by ring
    calc |∑ i : Fin d, ∑ j : Fin d, M j i * (L ^ (-s - 1) * partialDeriv idx (Sij i j) x)|
        ≤ ∑ i : Fin d, |∑ j : Fin d, M j i * (L ^ (-s - 1) * partialDeriv idx (Sij i j) x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, |M j i * (L ^ (-s - 1) * partialDeriv idx (Sij i j) x)| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, max MB 0 * Kk * (Λ0 * (Real.sqrt V * Real.sqrt En)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = Bd := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hBd]
          ring
  -- the energy of w ∂^idx F
  have hwV : ∫ x, w x ^ 2 ≤ V := by
    rw [← hVb]
    exact sa12x3_int_le_vol (hw.pow 2) (fun x => sq_nonneg _)
      (fun x => by nlinarith [hw1 x, abs_nonneg (w x), sq_abs (w x)])
      fun x hx => by
        by_contra h0
        exact hx (hwsup (subset_tsupport _ (fun h => h0 (by simp [h]))))
  have hwp : ∀ n ≤ m, ∀ (idx : Fin n → Fin d), ∫ x, (w x * partialDeriv idx F x) ^ 2 ≤ En := by
    intro n hn idx
    have hpc : Continuous (partialDeriv idx F) := (sa12z3_pd_contDiff_inf hF idx).continuous
    have := sa12x2_cover_gen m hF hω (K1 := 1) (K2 := 0) zero_le_one le_rfl
      (f := fun x => w x * partialDeriv idx F x) (hw.mul hpc) (hwc.mul_right)
      (fun x => by
        have h1 := sa12x2_sq_le_Y hn F idx x
        have h3 := sa12x2_Yd_nonneg m F x
        have hw2 : w x ^ 2 ≤ 1 := by nlinarith [hw1 x, abs_nonneg (w x), sq_abs (w x)]
        have : (w x * partialDeriv idx F x) ^ 2 ≤ partialDeriv idx F x ^ 2 := by
          rw [mul_pow]
          exact mul_le_of_le_one_left (sq_nonneg _) hw2
        nlinarith)
      (fun x hx => hwW x (fun h0 => hx (by simp [h0])))
    simpa using this
  -- the pairing for each (j, idx)
  have hpair : ∀ n ≤ m, ∀ (idx : Fin n → Fin d),
      |∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Sf x)| ≤ Bd * (Real.sqrt V * Real.sqrt En) := by
    intro n hn idx
    have hpc : Continuous (partialDeriv idx F) := (sa12z3_pd_contDiff_inf hF idx).continuous
    have hSc : Continuous (partialDeriv idx Sf) :=
      (sa12x2_pd_cd (k := 0) (by simpa using hSfs.of_le (by exact_mod_cast (by omega : n ≤ m + 1))) idx).continuous
    have hcont : Continuous (fun x => w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Sf x)) :=
      (hw.pow 2).mul (hpc.mul hSc)
    have hcs : HasCompactSupport (fun x => w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Sf x)) :=
      (hwc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_right
    have hint : Integrable (fun x => |w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Sf x)|) :=
      hcont.abs.integrable_of_hasCompactSupport hcs.abs
    have hcsb := sa12x3_cs hw hwc (hw.mul hpc) (hwc.mul_right) hwV (hwp n hn idx)
    have hmaj : Integrable (fun x => Bd * (|w x| * |w x * partialDeriv idx F x|)) := by
      refine Continuous.integrable_of_hasCompactSupport
        (continuous_const.mul (hw.abs.mul (hw.mul hpc).abs)) ?_
      refine HasCompactSupport.intro (K := tsupport w) hwc fun y hy => ?_
      have : w y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [this]
    calc |∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Sf x)|
        ≤ ∫ x, |w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Sf x)| := abs_integral_le_integral_abs
      _ ≤ ∫ x, Bd * (|w x| * |w x * partialDeriv idx F x|) := by
          refine integral_mono hint hmaj fun x => ?_
          by_cases hx : w x = 0
          · simp [hx]
          · have hxb : x ∈ ball c ρ := hwsup (subset_tsupport _ hx)
            have hb := hpdS n hn idx x hxb
            calc |w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Sf x)|
                = (|w x| * |w x * partialDeriv idx F x|) * |partialDeriv idx Sf x| := by
                  simp only [abs_mul, abs_pow]; ring
              _ ≤ (|w x| * |w x * partialDeriv idx F x|) * Bd :=
                  mul_le_mul_of_nonneg_left hb (by positivity)
              _ = Bd * (|w x| * |w x * partialDeriv idx F x|) := by ring
      _ = Bd * ∫ x, |w x| * |w x * partialDeriv idx F x| := integral_const_mul _ _
      _ ≤ Bd * (Real.sqrt V * Real.sqrt En) := mul_le_mul_of_nonneg_left hcsb hBd0
  -- assemble
  show -(2 * jetPair m w F Sf) ≤ _
  unfold jetPair
  have hsum : ∀ j ∈ Finset.range (m + 1), -((Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
      ∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Sf x)) ≤
      (Nat.choose m j : ℝ) * ((d : ℝ) ^ j * (Bd * (Real.sqrt V * Real.sqrt En))) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.1 hj)
    have h1 : -(∑ idx : Fin j → Fin d, ∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Sf x)) ≤
        (d : ℝ) ^ j * (Bd * (Real.sqrt V * Real.sqrt En)) := by
      calc -(∑ idx : Fin j → Fin d, ∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Sf x))
          = ∑ idx : Fin j → Fin d, -(∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Sf x)) := by
            rw [Finset.sum_neg_distrib]
        _ ≤ ∑ idx : Fin j → Fin d, Bd * (Real.sqrt V * Real.sqrt En) :=
            Finset.sum_le_sum fun idx _ => (neg_le_abs _).trans (hpair j hjm idx)
        _ = (d : ℝ) ^ j * (Bd * (Real.sqrt V * Real.sqrt En)) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hc : (0 : ℝ) ≤ Nat.choose m j := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left h1 hc
    linarith
  have hfin := Finset.sum_le_sum hsum
  rw [Finset.sum_neg_distrib] at hfin
  have hsv : Real.sqrt V * Real.sqrt V = V := Real.mul_self_sqrt hV0
  have hse : Real.sqrt En * Real.sqrt En = En := Real.mul_self_sqrt hEn0
  have hrhs : ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ((d : ℝ) ^ j * (Bd * (Real.sqrt V * Real.sqrt En))) =
      S0 * max MB 0 * Kk * (d : ℝ) ^ 2 * Λ0 * V * En := by
    have : Bd * (Real.sqrt V * Real.sqrt En) = max MB 0 * Kk * (d : ℝ) ^ 2 * Λ0 * (V * En) := by
      rw [hBd]
      calc _ = max MB 0 * Kk * (d : ℝ) ^ 2 * Λ0 * ((Real.sqrt V * Real.sqrt V) * (Real.sqrt En * Real.sqrt En)) := by ring
        _ = _ := by rw [hsv, hse]
    simp_rw [this]
    rw [hS0, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hrhs] at hfin
  have hneg : -(2 * ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
      ∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Sf x)) =
      2 * (-∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
      ∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Sf x)) := by ring
  rw [hneg]
  have : -∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
      ∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Sf x) ≤ S0 * max MB 0 * Kk * (d : ℝ) ^ 2 * Λ0 * V * En := by
    exact hfin
  nlinarith [this]

end HRS.MH.AdjointRd.Phase2SA12Near
