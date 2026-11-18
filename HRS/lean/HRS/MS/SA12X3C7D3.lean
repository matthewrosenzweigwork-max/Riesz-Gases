import HRS.MS.SA12X3C7D2

/-!
# S.A.12 C7 (SA12X3): `periodic_nonlocal_regimes`

Assembly: `perNonlocal = near + smooth + far` on each cell (`sa12x3_per_identity`); the near part by `near_local_regimes` (C6) at the real
centre `cellPt z`, the smooth part by `sa12x3_smooth_pairing`, the far part by `sa12x3_far_pairing_sm` with the fine-lattice kernel of
`sa12x3_far_kernel` (`screened_far_periodic` of T7 at every kernel order).
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12x3_lam_ge {Rg : PDE.Regime} {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ν ν₀ : ℝ}
    (hR : RdRegimeHolds Rg d s M ν ν₀) {C C6 : ℝ} (h : C6 ≤ C) (θ : ℝ) :
    Rg.lambdaM C6 ν₀ θ + (C - C6) ≤ Rg.lambdaM C ν₀ θ := by
  cases Rg with
  | R3 =>
    have hν : 0 < ν₀ := hR.2.1
    have hu : 0 ≤ ν₀ ^ (-(θ / (2 - θ))) := Real.rpow_nonneg hν.le _
    simp only [PDE.Regime.lambdaM]
    nlinarith [mul_nonneg (sub_nonneg.2 h) hu]
  | R2b _ => exact absurd hR id
  | _ => simp only [PDE.Regime.lambdaM]; linarith

theorem sa12x3_lam_nonneg {Rg : PDE.Regime} {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ν ν₀ : ℝ}
    (hR : RdRegimeHolds Rg d s M ν ν₀) {C : ℝ} (h : 0 ≤ C) (θ : ℝ) : 0 ≤ Rg.lambdaM C ν₀ θ := by
  cases Rg with
  | R3 =>
    have hu : 0 ≤ ν₀ ^ (-(θ / (2 - θ))) := Real.rpow_nonneg hR.2.1.le _
    simp only [PDE.Regime.lambdaM]
    positivity
  | R2b _ => exact absurd hR id
  | _ => simpa only [PDE.Regime.lambdaM] using h

theorem periodic_nonlocal_regimes (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s)
    (hsd : s<d) (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime)
    (MB Λ ΛV νbar Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (E : Finset (Fin d → ℤ)) (C CK L₁ : ℝ),
      CoversBall8 E ∧ 0<C ∧ 0 ≤ CK ∧
      ∀ ν ν₀ : ℝ,
        NlCellBound s m MB Λ ΛV νbar Cb T χ χh E
          (Rg.lambdaM C ν₀ (PDE.thetaOrder d s)) (nearSpill Rg ν₀ E) CK L₁
          (fun M => PDE.MatBound MB M ∧ RdRegimeHolds Rg d s M ν ν₀) := by
  obtain ⟨E, C₆, hE, hC₆, hnear⟩ := near_local_regimes hd s hs0 hsd m hm Rg MB ((m + 4) * Λ) Cb T χ χh hχ
  obtain ⟨R', δ, h0, L₂, q, hR', hδ, h0p, hq, hid⟩ := sa12x3_per_identity hd s hs0 hsd m Cb T χ χh hχ
  obtain ⟨Rg', hg, hRg', hhg, hgeom⟩ := sa12x3_geom hd m Cb T χ χh hχ
  obtain ⟨AS, hAS, hSP⟩ := sa12x3_smooth_pairing hq m hm (ρ := Rg' + 1) (by linarith)
  obtain ⟨Cs, L₁f, hCs, hFK⟩ := sa12x3_far_kernel hd hs0 hsd m hm Λ Cb T χ χh hχ
  obtain ⟨B1, R1, hB1, hR1, hf⟩ := advected_cutoff_jets d hd m Cb T χ χh hχ
  set S0 : ℝ := ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j with hS0
  have hS00 : 0 ≤ S0 := Finset.sum_nonneg fun j _ => by positivity
  set MB' : ℝ := max MB 0 with hMB'
  set Λ' : ℝ := max Λ 0 with hΛ'
  set K1 : ℝ := AS * MB' * Λ' with hK1
  set K3 : ℝ := S0 * (d : ℝ) ^ 4 * MB' ^ 2 * (Cs * Λ ^ 2) with hK3
  have hK10 : 0 ≤ K1 := by positivity
  have hK30 : 0 ≤ K3 := by positivity
  refine ⟨E, C₆ + K1 + S0 + K3 + 1, Cs, max (max (max 1 L₂) L₁f) (2 * (Rg' + hg / 2) + 1), hE,
    by positivity, hCs, fun ν ν₀ => ?_⟩
  intro L γ M ν' μ V b hLL hPD hreg Ψ hΨ τ hτ
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hLL))
  have hL2 : L₂ ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hLL))
  have hLf : L₁f ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hLL)
  have hRL : Rg' + hg / 2 < L / 2 := by
    have := le_trans (le_max_right _ _) hLL
    linarith
  have hb := hPD.b_drift
  have hμs := hPD.μ_smooth τ hτ
  obtain ⟨Kfin, hrow, hcol, hKF⟩ := hFK b Ψ hb hΨ L γ hLf hPD.hγ (μ τ) hμs (hPD.μ_periodic τ hτ)
    (hPD.μ_decay τ hτ) τ hτ
  refine ⟨Kfin, hrow, hcol, ?_⟩
  intro F hF hFp z
  have hF1 : ContDiff ℝ ∞ F := hF.1
  set c0 : Euc d := cellPt d z with hc0
  have hcut := hf b Ψ hb hΨ τ hτ c0
  have hωk : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
      HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k))) := fun k _ =>
    ⟨(hf b Ψ hb hΨ τ hτ _).1.1.continuous,
      sa12x2_advCutoff_hasCompactSupport (hτ.1.trans hτ.2) hb hΨ hτ hχ.1.2.1 _⟩
  have hwc : Continuous (advCutoff χ Ψ τ c0) := hcut.1.1.continuous
  have hwcs : HasCompactSupport (advCutoff χ Ψ τ c0) :=
    sa12x2_advCutoff_hasCompactSupport (hτ.1.trans hτ.2) hb hΨ hτ hχ.1.2.1 c0
  obtain ⟨hηts, hwN⟩ := hgeom b Ψ hb hΨ τ hτ c0
  have hη1 : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (advCutoff χh Ψ τ c0) :=
    hcut.1.2.of_le (by exact_mod_cast le_refl _)
  have hw1 : ∀ x, |advCutoff χ Ψ τ c0 x| ≤ 1 := by
    intro x
    have h : advCutoff χ Ψ τ c0 x ∈ Icc (0 : ℝ) 1 := hχ.1.2.2.2.1 _
    exact abs_le.2 ⟨by linarith [h.1], h.2⟩
  have hwsup : tsupport (advCutoff χ Ψ τ c0) ⊆ ball (Ψ τ c0) (Rg' + 1) := by
    refine (closure_minimal (s := Function.support (advCutoff χ Ψ τ c0))
      (t := closedBall (Ψ τ c0) Rg') (fun x hx => ?_) isClosed_closedBall).trans
      (closedBall_subset_ball (by linarith))
    exact ball_subset_closedBall (hwN x hx).1
  have hwW : ∀ x, advCutoff χ Ψ τ c0 x ≠ 0 → 1 ≤ sa12z3_W E χ Ψ τ z x := fun x hx =>
    sa12z3_W_ge_one hχ hE Ψ τ z x (by
      have := sa12z3_adv_ne_norm_lt hχ Ψ τ c0 hx
      linarith)
  have hηW : ∀ x, advCutoff χh Ψ τ c0 x ≠ 0 → 1 ≤ sa12z3_W E χ Ψ τ z x := fun x hx =>
    sa12z3_W_ge_one hχ hE Ψ τ z x (le_of_lt (sa12z3_advh_ne_norm_lt hχ Ψ τ c0 hx))
  have hμb : ∀ x, |μ τ x| ≤ Λ' := fun x => by
    have := hPD.μ_bdd τ hτ 0 (by omega) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hΛ0 : 0 ≤ Λ' := (abs_nonneg _).trans (hμb 0)
  have hηsub : tsupport (advCutoff χh Ψ τ c0) ⊆ ball (Ψ τ c0) (Rg' + 1) :=
    hηts.trans (ball_subset_ball (by linarith))
  have hMb : ∀ i j, |M i j| ≤ MB := fun i j => hreg.1 i j
  have hη0 : ∀ x, 0 ≤ advCutoff χh Ψ τ c0 x := fun x => (hχ.2.2.2.2.1 _ : advCutoff χh Ψ τ c0 x ∈ Icc (0 : ℝ) 1).1
  have hη1' : ∀ x, advCutoff χh Ψ τ c0 x ≤ 1 := fun x => (hχ.2.2.2.2.1 _ : advCutoff χh Ψ τ c0 x ∈ Icc (0 : ℝ) 1).2
  obtain ⟨hSsm, hSb⟩ := hSP s L hs0 hL1 M MB Λ' hMb (Ψ τ c0) E χ Ψ τ z F hF1 hωk (advCutoff χ Ψ τ c0)
    (advCutoff χh Ψ τ c0) (μ τ) hwc hwcs hw1 hwsup hwW hη1 hη0 hη1' hηsub hηW hμs hμb
  set En : ℝ := ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F with hEn
  have hEn0 : 0 ≤ En := Finset.sum_nonneg fun k _ => sa12x2_cellEnergy_nonneg m χ Ψ τ _ F
  set X : ℝ := (∑' z'', (Kfin z z'' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z'' F)).toReal with hX
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hwp : ∀ n ≤ m, ∀ idx : Fin n → Fin d, ∫ x, (advCutoff χ Ψ τ c0 x * partialDeriv idx F x) ^ 2 ≤ En := by
    intro n hn idx
    have hpc : Continuous (partialDeriv idx F) := (sa12z3_pd_contDiff_inf hF1 idx).continuous
    have := sa12x2_cover_gen m hF1 hωk (K1 := 1) (K2 := 0) zero_le_one le_rfl
      (f := fun x => advCutoff χ Ψ τ c0 x * partialDeriv idx F x) (hwc.mul hpc) (hwcs.mul_right)
      (fun x => by
        have h1 := sa12x2_sq_le_Y hn F idx x
        have h3 := sa12x2_Yd_nonneg m F x
        have hw2 : advCutoff χ Ψ τ c0 x ^ 2 ≤ 1 := by
          have := hw1 x
          nlinarith [abs_nonneg (advCutoff χ Ψ τ c0 x), sq_abs (advCutoff χ Ψ τ c0 x)]
        have : (advCutoff χ Ψ τ c0 x * partialDeriv idx F x) ^ 2 ≤ partialDeriv idx F x ^ 2 := by
          rw [mul_pow]; exact mul_le_of_le_one_left (sq_nonneg _) hw2
        nlinarith)
      (fun x hx => hwW x (fun h0 => hx (by simp [h0])))
    simpa using this
  obtain ⟨Fs, hFs, hFsEq, hFsb⟩ := sa12x3_far_pairing_sm (s := s) (L := L) (γ := γ) hPD.hγ (h := hg)
    (R' := Rg') (R'' := Rg' + hg / 2) hhg (by linarith) le_rfl hRL (c := Ψ τ c0) M MB hMb hwc hwcs
    (η := advCutoff χh Ψ τ c0) (μ := μ τ) hη1.continuous hμs.continuous hF1 hwN m hwp
    (fun n hn idx i j => hKF F hF hFp z n hn idx i j)
  -- the near part
  have hNa : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => advCutoff χh Ψ τ c0 y * μ τ y) :=
    hη1.mul (hμs.of_le (sa12x2_le_top _))
  have hNac : HasCompactSupport (fun y => advCutoff χh Ψ τ c0 y * μ τ y) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (Ψ τ c0) (Rg' + 1))
      fun y hy => ball_subset_closedBall (hηsub (subset_tsupport _ (fun h0 => hy (by simp [h0]))))
  have hNsm : ContDiff ℝ m (eucNonlocal s M (fun y => advCutoff χh Ψ τ c0 y * μ τ y) F) :=
    sa12x3_eucNL_smooth hs0 hsd M (by exact_mod_cast hNa) hNac hF1
  have hsplit := sa12x3_jetPair_split (m := m) (w := advCutoff χ Ψ τ c0) (F := F)
    (G := fun x => perNonlocal L γ M (μ τ) F x)
    (N := eucNonlocal s M (fun y => advCutoff χh Ψ τ c0 y * μ τ y) F) (S := fun x => ∑ i : Fin d, ∑ j : Fin d,
      M j i * (L ^ (-s - 1) * ∫ y, fderiv ℝ q (L⁻¹ • (x - y)) (EuclideanSpace.single i (1 : ℝ)) *
        (advCutoff χh Ψ τ c0 y * μ τ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))))
    (Fs := Fs) hwc hwcs hF1 hNsm (hSsm.of_le (by exact_mod_cast Nat.le_succ m)) (hFs.of_le (sa12x2_le_top _))
    (fun x hx => by
      have := hid b Ψ hb hΨ τ hτ c0 L γ hL2 hL1 hPD.hγ M (μ τ) F hμs hF1 (hPD.μ_periodic τ hτ) hFp x hx
      rw [this, ← hFsEq x hx]
      rfl)
  have hN := hnear b Ψ hb hΨ M ν ν₀ hreg.1 hreg.2 (μ τ)
    ⟨hμs.of_le (sa12x2_le_top _), fun j _ => ⟨Λ, by
      rintro _ ⟨x, rfl⟩; exact hPD.μ_bdd τ hτ j (by omega) x⟩⟩
    (by
      unfold cbNorm
      calc ∑ j ∈ Finset.range (m + 3 + 1), (⨆ x : Euc d, ‖iteratedFDeriv ℝ j (μ τ) x‖) ≤
            ∑ j ∈ Finset.range (m + 3 + 1), Λ :=
          Finset.sum_le_sum fun j hj => ciSup_le fun x => hPD.μ_bdd τ hτ j (by
            have := Finset.mem_range.1 hj; omega) x
        _ = (m + 4) * Λ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring)
    (fun x => (hPD.μ_prob τ hτ).1 x) F hF τ hτ c0
  have hcp : ∀ k, c0 + cellPt d k = cellPt d (z + k) := fun k => (sa12z3_cellPt_add z k).symm
  simp only [hcp] at hN
  have hlam0 := sa12x3_lam_nonneg hreg.2 hC₆.le (PDE.thetaOrder d s)
  have hlam := sa12x3_lam_ge hreg.2 (show C₆ ≤ C₆ + K1 + S0 + K3 + 1 by linarith) (PDE.thetaOrder d s)
  show -(2 * jetPair m (advCutoff χ Ψ τ c0) F (fun x => perNonlocal L γ M (μ τ) F x)) ≤ _
  rw [hsplit]
  have e1 := mul_le_mul_of_nonneg_right (show Rg.lambdaM C₆ ν₀ (PDE.thetaOrder d s) + K1 + S0 ≤
    Rg.lambdaM (C₆ + K1 + S0 + K3 + 1) ν₀ (PDE.thetaOrder d s) by linarith) hEn0
  have e2 := mul_le_mul_of_nonneg_right (show K3 ≤ Rg.lambdaM (C₆ + K1 + S0 + K3 + 1) ν₀ (PDE.thetaOrder d s)
    by linarith) hX0
  have hFs' : S0 * (d : ℝ) ^ 4 * MB' ^ 2 * (Cs * Λ ^ 2 * X) = K3 * X := by rw [hK3]; ring
  nlinarith [hN, hSb, hFsb, hFs']

end HRS.MH.AdjointRd.Phase2SA12Construction
