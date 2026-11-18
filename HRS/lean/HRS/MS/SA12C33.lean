import HRS.MS.SA12C32

/-!
# S.A.12(c), packet E7.05: the global periodic nonlocal inequality in box form

For `L ≥ L_min` and a smooth periodic `F`, `μ ≥ 0` (periodic, bounded jets, periodic decay):
`-2⟨F, 𝒢_L F⟩_{m,L} ≤ nearSpill·card(E)·D_{m,L}(F) + (λ_M·card(E) + C_rem)·E_{m,L}(F)`.
(`near_local_regimes` at auxiliary zero drift and identity flow, averaged over the centres `c ∈ Q_L`; the
remainder `𝒢_L - 𝒢^{near}_c` is controlled by the E7.04 family bound.)
-/

set_option autoImplicit false
set_option maxHeartbeats 25600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12c_periodic_global_nonlocal_form (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hs1 : (d : ℝ) < 2 * (s + 1)) (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime) (MB Λ : ℝ)
    {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) :
    ∃ (E : Finset (Fin d → ℤ)) (C Crem Lmin : ℝ), CoversBall8 E ∧ 0 < C ∧ 0 ≤ Crem ∧ 40 ≤ Lmin ∧
      ∀ L : ℝ, Lmin ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ M : Matrix (Fin d) (Fin d) ℝ, PDE.MatBound MB M → ∀ ν ν₀ : ℝ, RdRegimeHolds Rg d s M ν ν₀ →
      ∀ μ F : Euc d → ℝ, ContDiff ℝ ∞ μ → (∀ x, 0 ≤ μ x) →
        (∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x) →
        (∀ j ≤ m + 3, ∀ x, ‖iteratedFDeriv ℝ j μ x‖ ≤ Λ) →
        (∀ x : Euc d, ∃ k : Fin d → ℤ, jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * |μ x| ≤ Λ) →
        ContDiff ℝ ∞ F → (∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) → BddJets m F →
        ContDiff ℝ ∞ (perNonlocal L γ M μ F) →
        -(2 * boxJetPair m L F (perNonlocal L γ M μ F)) ≤
          nearSpill Rg ν₀ E * E.card * boxDissip m L F +
            (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * E.card + Crem) * boxEnergy m L F := by
  obtain ⟨E, C, hE, hC, hnear⟩ := near_local_regimes hd s hs0 hsd m hm Rg MB ((m + 4) * Λ) 1 1 χ χh hχ
  obtain ⟨L1, hL1, C4, hC4, h4⟩ := sa12c_remainder_family_bound hd s hs0 hsd hs1 m hm hχ MB
  obtain ⟨C₀, hC₀, hdens⟩ := sa12c_density_l2 d
  refine ⟨E, C, 1 + C4 * (C₀ * Λ ^ 2), L1, hE, hC, by positivity, hL1, ?_⟩
  intro L hL γ hγ M hM ν ν₀ hR μ F hμ hμnn hμp hμb hμdec hF hFp hFb hPer
  have hL0 : 0 < L := by linarith
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hμb 0 (by omega) 0)
  have hcχ0 : 0 < ∫ v, χ v ^ 2 := sa12c_chi_sq_pos hχ hd
  set cχ : ℝ := ∫ v, χ v ^ 2 with hcχ
  have hK2 : ∫ x in periodBox d L, μ x ^ 2 ≤ C₀ * Λ ^ 2 := hdens hL0 hμ.continuous hμp hμdec
  obtain ⟨hRint, hRbound⟩ := h4 L hL γ hγ M hM μ F hμ hF hμp hFp (C₀ * Λ ^ 2) hK2
  set P : Euc d → ℝ := perNonlocal L γ M μ F with hP
  have hPp : ∀ (x : Euc d) (k : Fin d → ℤ), P (x + L • latticePt k) = P x :=
    fun x k => sa12c_perNonlocal_periodic hγ.periodic M μ F x k
  have hPm : ContDiff ℝ m P := hPer.of_le (by exact_mod_cast le_top)
  obtain ⟨hJi, hJ⟩ := sa12c_avg_jetPair hL0 hχ hF hPm hFp hPp
  obtain ⟨hFi, hFE⟩ := sa12c_avg_jetSq hL0 hχ m hF hFp 0
  simp only [add_zero] at hFi hFE
  have hdiss : ∀ k : Fin d → ℤ, Integrable (fun c => dissipSq m (fun x => χ (x - (c + cellPt d k))) F)
      (volume.restrict (periodBox d L)) ∧
      ∫ c in periodBox d L, dissipSq m (fun x => χ (x - (c + cellPt d k))) F = cχ * boxDissip m L F :=
    fun k => sa12c_avg_dissip hL0 hχ m hF hFp (cellPt d k)
  have henergy : ∀ k : Fin d → ℤ, Integrable (fun c => jetSq m (fun x => χ (x - (c + cellPt d k))) F)
      (volume.restrict (periodBox d L)) ∧
      ∫ c in periodBox d L, jetSq m (fun x => χ (x - (c + cellPt d k))) F = cχ * boxEnergy m L F :=
    fun k => sa12c_avg_jetSq hL0 hχ m hF hFp (cellPt d k)
  -- zero drift / identity flow data
  have e' : ∀ (g : Euc d → ℝ) (z : Euc d),
      advCutoff g (fun (_ : ℝ) (x : Euc d) => x) 0 z = fun x => g (x - z) :=
    fun g z => funext fun x => sa12c_advCutoff_id g 0 z x
  have hμs : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) μ := hμ.of_le (by simp)
  have hnearC : ∀ c : Euc d, -(2 * jetPair m (fun x => χ (x - c)) F
        (eucNonlocal s M (fun y => χh (y - c) * μ y) F)) ≤
      nearSpill Rg ν₀ E * ∑ k ∈ E, dissipSq m (fun x => χ (x - (c + cellPt d k))) F +
        Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * ∑ k ∈ E, jetSq m (fun x => χ (x - (c + cellPt d k))) F := by
    intro c
    have h := hnear (fun _ _ => 0) (fun _ x => x) (sa12c_drift_zero m) sa12c_flow_id M ν ν₀ hM hR μ
      ⟨hμs, fun j _ => ⟨Λ, by
        rintro _ ⟨x, rfl⟩; exact hμb j (by omega) x⟩⟩
      (by
        unfold cbNorm
        calc ∑ j ∈ Finset.range (m + 3 + 1), (⨆ x : Euc d, ‖iteratedFDeriv ℝ j μ x‖) ≤
              ∑ j ∈ Finset.range (m + 3 + 1), Λ :=
            Finset.sum_le_sum fun j hj => ciSup_le fun x => hμb j (by
              have := Finset.mem_range.1 hj; omega) x
          _ = (m + 4) * Λ := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring)
      hμnn F hFb 0 ⟨le_rfl, zero_le_one⟩ c
    simp only [cellDissip, cellEnergy, e'] at h
    exact h
  -- the pointwise inequality
  have hpt : ∀ c : Euc d, -(2 * jetPair m (fun x => χ (x - c)) F P) ≤
      (nearSpill Rg ν₀ E * ∑ k ∈ E, dissipSq m (fun x => χ (x - (c + cellPt d k))) F +
        Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * ∑ k ∈ E, jetSq m (fun x => χ (x - (c + cellPt d k))) F) +
      jetSq m (fun x => χ (x - c)) F +
      jetSq m (fun x => χ (x - c)) (fun x => P x - eucNonlocal s M (fun y => χh (y - c) * μ y) F x) := by
    intro c
    have hw : Continuous fun x => χ (x - c) := hχ.1.1.continuous.comp (continuous_id.sub continuous_const)
    have hwc : HasCompactSupport fun x => χ (x - c) := by
      refine HasCompactSupport.intro (isCompact_closedBall c 2) fun x hx => ?_
      rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hx
      exact sa12c_chi_support hχ _ hx.le
    set N : Euc d → ℝ := eucNonlocal s M (fun y => χh (y - c) * μ y) F with hN
    have ha : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => χh (y - c) * μ y) :=
      ((hχ.2.1.comp (contDiff_id.sub contDiff_const)).mul hμ).of_le (by exact_mod_cast le_top)
    have hac : HasCompactSupport fun y => χh (y - c) * μ y := by
      refine HasCompactSupport.intro (isCompact_closedBall c 8) fun y hy => ?_
      rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hy
      have : χh (y - c) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have := hχ.2.2.2.1 hmem
        rw [Metric.mem_ball, dist_zero_right] at this
        linarith
      simp [this]
    have hNm : ContDiff ℝ m N := sa12x3_eucNL_smooth hs0 hsd M ha hac hF
    have hSm : ContDiff ℝ m (fun x => P x - N x) := hPm.sub hNm
    have hsplit := sa12x3_jetPair_split (m := m) (w := fun x => χ (x - c)) (F := F) (G := P) (N := N)
      (S := fun x => P x - N x) (Fs := fun _ => 0) hw hwc hF hNm hSm contDiff_const
      (fun x _ => by simp)
    have hz : jetPair m (fun x => χ (x - c)) F (fun _ => 0) = 0 := by
      simp [jetPair, partialDeriv]
    rw [hz, add_zero] at hsplit
    have h1 := sa12c_jetPair_neg_le (m := m) hw hwc hF hSm
    have h2 := hnearC c
    rw [hsplit]
    linarith
  -- integrate over the centres
  have hint : Integrable (fun c => jetPair m (fun x => χ (x - c)) F P) (volume.restrict (periodBox d L)) := hJi
  have hI1 : Integrable (fun c => nearSpill Rg ν₀ E * ∑ k ∈ E, dissipSq m (fun x => χ (x - (c + cellPt d k))) F)
      (volume.restrict (periodBox d L)) := (integrable_finset_sum _ fun k _ => (hdiss k).1).const_mul _
  have hI2 : Integrable (fun c => Rg.lambdaM C ν₀ (PDE.thetaOrder d s) *
      ∑ k ∈ E, jetSq m (fun x => χ (x - (c + cellPt d k))) F) (volume.restrict (periodBox d L)) :=
    (integrable_finset_sum _ fun k _ => (henergy k).1).const_mul _
  have hleftI : Integrable (fun c => -(2 * jetPair m (fun x => χ (x - c)) F P))
      (volume.restrict (periodBox d L)) := by
    convert (hint.const_mul (-2)) using 1
    funext c; ring
  have hrightI : Integrable (fun c =>
      ((nearSpill Rg ν₀ E * ∑ k ∈ E, dissipSq m (fun x => χ (x - (c + cellPt d k))) F) +
       (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * ∑ k ∈ E, jetSq m (fun x => χ (x - (c + cellPt d k))) F) +
       jetSq m (fun x => χ (x - c)) F) +
       jetSq m (fun x => χ (x - c)) (fun x => P x - eucNonlocal s M (fun y => χh (y - c) * μ y) F x))
      (volume.restrict (periodBox d L)) := ((hI1.add hI2).add hFi).add hRint
  have hmono : (∫ c in periodBox d L, -(2 * jetPair m (fun x => χ (x - c)) F P)) ≤
      ∫ c in periodBox d L,
      ((nearSpill Rg ν₀ E * ∑ k ∈ E, dissipSq m (fun x => χ (x - (c + cellPt d k))) F) +
       (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * ∑ k ∈ E, jetSq m (fun x => χ (x - (c + cellPt d k))) F) +
       jetSq m (fun x => χ (x - c)) F) +
       jetSq m (fun x => χ (x - c)) (fun x => P x - eucNonlocal s M (fun y => χh (y - c) * μ y) F x) :=
    integral_mono_ae hleftI hrightI (Eventually.of_forall hpt)
  have hLi : (∫ c in periodBox d L, -(2 * jetPair m (fun x => χ (x - c)) F P)) =
      -(2 * (cχ * boxJetPair m L F P)) := by
    have he : (fun c : Euc d => -(2 * jetPair m (fun x => χ (x - c)) F P)) =
        fun c => (-2) * jetPair m (fun x => χ (x - c)) F P := by funext c; ring
    rw [he, integral_const_mul, hJ]
    ring
  have hId : (∫ c in periodBox d L,
      nearSpill Rg ν₀ E * ∑ k ∈ E, dissipSq m (fun x => χ (x - (c + cellPt d k))) F) =
      nearSpill Rg ν₀ E * (E.card : ℝ) * (cχ * boxDissip m L F) := by
    calc
      _ = nearSpill Rg ν₀ E * ∑ k ∈ E, ∫ c in periodBox d L,
          dissipSq m (fun x => χ (x - (c + cellPt d k))) F := by
        rw [integral_const_mul, integral_finset_sum _ fun k _ => (hdiss k).1]
      _ = nearSpill Rg ν₀ E * ∑ k ∈ E, cχ * boxDissip m L F := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        exact (hdiss k).2
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; push_cast; ring
  have hIe : (∫ c in periodBox d L,
      Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * ∑ k ∈ E, jetSq m (fun x => χ (x - (c + cellPt d k))) F) =
      Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * (E.card : ℝ) * (cχ * boxEnergy m L F) := by
    calc
      _ = Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * ∑ k ∈ E, ∫ c in periodBox d L,
          jetSq m (fun x => χ (x - (c + cellPt d k))) F := by
        rw [integral_const_mul, integral_finset_sum _ fun k _ => (henergy k).1]
      _ = Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * ∑ k ∈ E, cχ * boxEnergy m L F := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        exact (henergy k).2
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; push_cast; ring
  have hfour {f g h k : Euc d → ℝ}
      (hf : Integrable f (volume.restrict (periodBox d L)))
      (hg : Integrable g (volume.restrict (periodBox d L)))
      (hh : Integrable h (volume.restrict (periodBox d L)))
      (hk : Integrable k (volume.restrict (periodBox d L))) :
      (∫ c in periodBox d L, f c + g c + h c + k c) =
      (∫ c in periodBox d L, f c) + (∫ c in periodBox d L, g c) +
      (∫ c in periodBox d L, h c) + (∫ c in periodBox d L, k c) := by
    have h1 : (∫ c in periodBox d L, f c + g c + h c + k c) =
        (∫ c in periodBox d L, f c + g c + h c) + (∫ c in periodBox d L, k c) := by
      simpa only [Pi.add_apply] using (integral_add ((hf.add hg).add hh) hk)
    have h2 : (∫ c in periodBox d L, f c + g c + h c) =
        (∫ c in periodBox d L, f c + g c) + (∫ c in periodBox d L, h c) := by
      simpa only [Pi.add_apply] using (integral_add (hf.add hg) hh)
    have h3 : (∫ c in periodBox d L, f c + g c) =
        (∫ c in periodBox d L, f c) + (∫ c in periodBox d L, g c) := by
      simpa only [Pi.add_apply] using (integral_add hf hg)
    rw [h1, h2, h3]
  have hI : (∫ c in periodBox d L,
      ((nearSpill Rg ν₀ E * ∑ k ∈ E, dissipSq m (fun x => χ (x - (c + cellPt d k))) F) +
       (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * ∑ k ∈ E, jetSq m (fun x => χ (x - (c + cellPt d k))) F) +
       jetSq m (fun x => χ (x - c)) F) +
       jetSq m (fun x => χ (x - c)) (fun x => P x - eucNonlocal s M (fun y => χh (y - c) * μ y) F x)) =
      (nearSpill Rg ν₀ E * (E.card : ℝ) * (cχ * boxDissip m L F) +
       Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * (E.card : ℝ) * (cχ * boxEnergy m L F) +
       cχ * boxEnergy m L F) +
       ∫ c in periodBox d L, jetSq m (fun x => χ (x - c))
        (fun x => P x - eucNonlocal s M (fun y => χh (y - c) * μ y) F x) := by
    rw [hfour hI1 hI2 hFi hRint, hId, hIe, hFE]

  have htotal := hmono
  rw [hLi, hI] at htotal
  have htotal2 : -(2 * (cχ * boxJetPair m L F P)) ≤
      nearSpill Rg ν₀ E * (E.card : ℝ) * (cχ * boxDissip m L F) +
      (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * (E.card : ℝ) + (1 + C4 * (C₀ * Λ ^ 2))) *
      (cχ * boxEnergy m L F) := by
    nlinarith [hRbound]
  have hscaled : cχ * (-(2 * boxJetPair m L F P)) ≤
      cχ * (nearSpill Rg ν₀ E * (E.card : ℝ) * boxDissip m L F +
        (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * (E.card : ℝ) + (1 + C4 * (C₀ * Λ ^ 2))) * boxEnergy m L F) := by
    nlinarith [htotal2]
  by_contra hn
  have hlt : nearSpill Rg ν₀ E * E.card * boxDissip m L F +
      (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * E.card + (1 + C4 * (C₀ * Λ ^ 2))) * boxEnergy m L F <
      -(2 * boxJetPair m L F P) := lt_of_not_ge hn
  exact (not_lt_of_ge hscaled) (mul_lt_mul_of_pos_left hlt hcχ0)

end HRS.MH.AdjointRd.Phase2SA12C
