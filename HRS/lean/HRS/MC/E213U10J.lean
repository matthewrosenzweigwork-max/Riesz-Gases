import HRS.MC.E213U10I

/-!
# Packet e213u10, part J: pathwise identification of the actual Riemann--Stieltjes integrals

Deterministic lemmas: for a horizon-`(a+T)` path `W₀` that agrees on `[b, a+T]` with the lift of a window path `w`, and a coefficient
that agrees (a.e., resp. pointwise) on `[0,a+T]` with the canonical near coefficient of `β` (resp. `z`), the actual integrals
`rsA`, `rsJ` equal the pair-space functionals `u10_FD (w, β)`, `u10_FJ (w, z)`.  The tags `τ < b` are removed by `u10_isRS_clamp`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

theorem u10_liftW_pathAt (hE : EdgeworthHyp S β₀ m) (b L H : ℝ) (hL : 0 ≤ L) (hH : H ≤ b + L)
    (w : PathSpace d (rLvl d) L) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) H) (hbt : b ≤ t) :
    pathAt (u10_liftW hE b L H hL hH w) t = NegSobolev.embed m (pathAt w (t - b)) := by
  have hmem : t - b ∈ Set.Icc (0 : ℝ) L := ⟨by linarith, by linarith [ht.2]⟩
  rw [u10_pathAt_eq (u10_liftW hE b L H hL hH w) ⟨t, ht⟩, u10_liftW_apply, u10_liftLM_at']
  congr 1
  rw [u10_pathAt_eq w ⟨t - b, hmem⟩]
  congr 1
  apply Subtype.ext
  simp only [u10_clamp_val]
  exact max_eq_left (sub_nonneg.2 hbt)

theorem u10_winJ_near_zero (R : Regime d) (m T a : ℝ) (ha : 0 ≤ a) (b : ℝ) (f : ℝ → NegSobolev d m) {u u' : ℝ}
    (h : u' ≤ b) : winJ R m T a ha (nearCoef b f) (Set.Ioc u u') = 0 := by
  have hne : ∀ᵐ v : ℝ ∂volume, v ∉ ({b} : Set ℝ) := (Set.countable_singleton b).ae_notMem volume
  have hshr := u10_winJ_shrink R m T a ha (z := nearCoef b f) (I := Set.Ioc u u') (I' := ∅) measurableSet_Ioc
    (Set.empty_subset _) (by
      filter_upwards [hne] with v hv hvI _
      have hvb : v ≠ b := fun e => hv (by simp [e])
      have : v < b := lt_of_le_of_ne (hvI.2.trans h) hvb
      simp [nearCoef, not_le.2 this])
  rw [hshr, u10_winJ_empty]

theorem u10_rsA_eq_FD (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (b L : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hL : 0 ≤ L)
    (hH : a + T ≤ b + L) (W₀ : PathSpace d m (a + T)) (w : PathSpace d (rLvl d) L)
    (hW : ∀ t ∈ Set.Icc b (a + T), pathAt W₀ t = pathAt (u10_liftW hE b L (a + T) hL hH w) t)
    (c : ℝ → NegSobolev d m) (β : L2Path d (rLvl d) L)
    (hc : ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Set.Icc (0 : ℝ) (a + T) → c v = u10_cD b L m β v) :
    rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) W₀ c = u10_FD hE T a ha Φ b L hL hH (w, β) := by
  have hH0 : 0 < a + T := by linarith
  have hreg := HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ
  have hY := HRS.MC.E213U7.e213u7_Y_cont hE T hT a ha W₀
  have hA := HRS.MC.E213U7.e213u7_fderiv_cont hE T a ha Φ hreg _ hY
  obtain ⟨I, hI⟩ := HRS.MC.E213U7.e213u7_drift_exists hE T hT a ha
    (fun τ => fderiv ℝ (Ucan hE T a ha Φ τ) (winPred (regime S β₀ hE) m T a ha W₀ τ))
    hA (u10_cD b L m β) (u10_cD_memLp hE T a b L hL hH β)
  set S' : ℝ → ℝ → ℝ → ℝ := fun τ u u' => fderiv ℝ (Ucan hE T a ha Φ τ)
    (winPred (regime S β₀ hE) m T a ha W₀ τ) (winDrift (regime S β₀ hE) m T a ha (u10_cD b L m β) u u') with hS'
  have hI' : IsRS (a + T) S' I := hI
  -- the actual sums
  have hact : IsRS (a + T) (rsSumD (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha W₀ τ)
      (fun u u' => winDrift (regime S β₀ hE) m T a ha c u u')) I := by
    refine HRS.MC.E213U7.e213u7_isRS_congr hI' (fun τ u u' hu huτ hτu' hu'T => ?_)
    show _ = fderiv ℝ (Ucan hE T a ha Φ τ) (winPred (regime S β₀ hE) m T a ha W₀ τ)
      (winDrift (regime S β₀ hE) m T a ha c u u')
    rw [u10_winDrift_congr (regime S β₀ hE) m T a ha (f := c) (g := u10_cD b L m β) (u := u) (u' := u')]
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hc] with v hv hvm
    exact hv ⟨hu.trans hvm.1.le, hvm.2.trans hu'T⟩
  have hrs : rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) W₀ c = I := HRS.MC.E213U7.e213u7_rsLim_eq hH0 hact
  rw [hrs]
  -- the canonical sums
  have hcan := u10_SD_isRS hE T hT a ha Φ hΦ b L hL hH (w, β)
  have h1 := u10_isRS_clamp b hI'
  have h2 := u10_isRS_clamp b hcan
  have h3 : IsRS (a + T) (fun τ u u' => u10_SD hE T a ha Φ b L hL hH (w, β) (min (max τ b) u') u u') I := by
    refine HRS.MC.E213U7.e213u7_isRS_congr h1 (fun τ u u' hu huτ hτu' hu'T => ?_)
    show S' (min (max τ b) u') u u' = u10_SD hE T a ha Φ b L hL hH (w, β) (min (max τ b) u') u u'
    unfold u10_SD rsSumD
    show fderiv ℝ (Ucan hE T a ha Φ (min (max τ b) u')) (winPred (regime S β₀ hE) m T a ha W₀ (min (max τ b) u'))
        (winDrift (regime S β₀ hE) m T a ha (u10_cD b L m β) u u') =
      fderiv ℝ (Ucan hE T a ha Φ (min (max τ b) u')) (u10_Y hE T a ha b L hL hH w (min (max τ b) u'))
        (winDrift (regime S β₀ hE) m T a ha (u10_cD b L m β) u u')
    by_cases hub : u' ≤ b
    · have h0 : winDrift (regime S β₀ hE) m T a ha (u10_cD b L m β) u u' = 0 :=
        u10_winDrift_near_zero (regime S β₀ hE) m T a ha b _ hub
      rw [h0, map_zero, map_zero]
    · have hub' : b < u' := not_le.1 hub
      have hmax : max τ b ≤ u' := max_le hτu' hub'.le
      have hτ' : min (max τ b) u' = max τ b := min_eq_left hmax
      have hτb : b ≤ max τ b := le_max_right _ _
      have hτm : max τ b ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hb.trans hτb, hmax.trans hu'T⟩
      rw [hτ']
      congr 2
      unfold u10_Y
      exact u10_winPred_congr hE T hT a ha b hba _ _ (fun t ht => hW t ht) hτm hτb
  exact HRS.MC.E213U1.isRS_unique_proof hH0 h3 h2

theorem u10_rsJ_eq_FJ (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (b L : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hL : 0 ≤ L)
    (hH : a + T ≤ b + L) (W₀ : PathSpace d m (a + T)) (w : PathSpace d (rLvl d) L)
    (hW : ∀ t ∈ Set.Icc b (a + T), pathAt W₀ t = pathAt (u10_liftW hE b L (a + T) hL hH w) t)
    (zc : ℝ → NegSobolev d m) (z : PathSpace d (rLvl d) L)
    (hz : ∀ v : ℝ, 0 ≤ v → v ≤ a + T → zc v = u10_cJ b L m z v) :
    rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) W₀ zc = u10_FJ hE T a ha Φ b L hL hH (w, z) := by
  have hH0 : 0 < a + T := by linarith
  have hreg := HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ
  have hY := HRS.MC.E213U7.e213u7_Y_cont hE T hT a ha W₀
  have hMc := HRS.MC.E213U7.e213u7_iFD_cont hE T a ha Φ hreg _ hY 2 le_rfl
  obtain ⟨I, hI⟩ := HRS.MC.E213U7.e213u7_J_exists hE T hT a ha _ hMc (u10_cJ b L m z)
    (nearCoef 0 (nearCoef b (u10_zq b L z)))
    (fun v hv => by
      rw [HRS.MC.E213U7.e213u7_nc0_apply _ hv]
      exact congrFun (HRS.MC.E213U7.e213u7_near_embed hE b (u10_zq b L z)) v)
    (u10_nearCoef0_meas b (u10_zq_meas b L z)) ‖z‖
    (fun u _ => (HRS.MC.E213U7.e213u7_norm_near_le 0 _ u).trans
      ((HRS.MC.E213U7.e213u7_norm_near_le b _ u).trans (u10_zq_norm_le b L z u)))
  set S' : ℝ → ℝ → ℝ → ℝ := fun τ u u' => winJ (regime S β₀ hE) m T a ha (u10_cJ b L m z) (Set.Ioc u u')
    (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) (winPred (regime S β₀ hE) m T a ha W₀ τ)) with hS'
  have hI' : IsRS (a + T) S' I := hI
  have hact : IsRS (a + T) (rsSumJ (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha W₀ τ)
      (fun u u' => winJ (regime S β₀ hE) m T a ha zc (Set.Ioc u u'))) I := by
    refine HRS.MC.E213U7.e213u7_isRS_congr hI' (fun τ u u' hu huτ hτu' hu'T => ?_)
    show _ = winJ (regime S β₀ hE) m T a ha zc (Set.Ioc u u')
      (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) (winPred (regime S β₀ hE) m T a ha W₀ τ))
    rw [u10_winJ_congr_on (regime S β₀ hE) m T a ha (z := zc) (z' := u10_cJ b L m z) measurableSet_Ioc
      (fun v hv h0 => hz v h0 (hv.2.trans hu'T))]
  have hrs : rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) W₀ zc = I := HRS.MC.E213U7.e213u7_rsLim_eq hH0 hact
  rw [hrs]
  have hcan := u10_SJ_isRS hE T hT a ha Φ hΦ b L hL hH (w, z)
  have h1 := u10_isRS_clamp b hI'
  have h2 := u10_isRS_clamp b hcan
  have h3 : IsRS (a + T) (fun τ u u' => u10_SJ hE T a ha Φ b L hL hH (w, z) (min (max τ b) u') u u') I := by
    refine HRS.MC.E213U7.e213u7_isRS_congr h1 (fun τ u u' hu huτ hτu' hu'T => ?_)
    show S' (min (max τ b) u') u u' = u10_SJ hE T a ha Φ b L hL hH (w, z) (min (max τ b) u') u u'
    unfold u10_SJ rsSumJ
    show winJ (regime S β₀ hE) m T a ha (u10_cJ b L m z) (Set.Ioc u u')
        (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ (min (max τ b) u'))
          (winPred (regime S β₀ hE) m T a ha W₀ (min (max τ b) u'))) =
      winJ (regime S β₀ hE) m T a ha (u10_cJ b L m z) (Set.Ioc u u')
        (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ (min (max τ b) u')) (u10_Y hE T a ha b L hL hH w (min (max τ b) u')))
    by_cases hub : u' ≤ b
    · have h0 : winJ (regime S β₀ hE) m T a ha (u10_cJ b L m z) (Set.Ioc u u') = 0 :=
        u10_winJ_near_zero (regime S β₀ hE) m T a ha b _ hub
      rw [h0]
      rfl
    · have hub' : b < u' := not_le.1 hub
      have hmax : max τ b ≤ u' := max_le hτu' hub'.le
      have hτ' : min (max τ b) u' = max τ b := min_eq_left hmax
      have hτb : b ≤ max τ b := le_max_right _ _
      have hτm : max τ b ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hb.trans hτb, hmax.trans hu'T⟩
      rw [hτ']
      congr 2
      unfold u10_Y
      exact u10_winPred_congr hE T hT a ha b hba _ _ (fun t ht => hW t ht) hτm hτb
  exact HRS.MC.E213U1.isRS_unique_proof hH0 h3 h2

end HRS.MC.E213U10

end
