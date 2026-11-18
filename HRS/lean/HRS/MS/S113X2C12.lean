import HRS.MS.S113X2C11

/-!
# S11.3 X2 wiring (worker S11W), C12: `S113XLocalizedI` from the cores QREG and LIOUVILLE
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory intervalIntegral
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2C

open HRS HRS.Whole HRS.MS.S113X2 HRS.MS.S113X2B
open HRS.MC.CepP3 (Jc Jc_single fderiv2_comp_clm)
open HRS.MS.S113BD (s113x_Q s113x_source S113XLocalizedI s113_powerMass s113_powerTilt s113c_Gp s113x_Q_prob s113x_K_pos)

variable {d N : ℕ}

theorem s113c_localized_of_cores (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {q β : ℝ} (hβ : 0 < β)
    (hq : 0 < q) {ρ₀ : Euc d → ℝ} (hρ₀ : IsThermalEquilibrium d s q β ρ₀) {j m : ℕ}
    {εstar r c₀ c C₁ : ℝ} (hC₁ : 0 < C₁) (hc₀ : 0 < c₀)
    (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁)
    (hLiou : S113XLiouville d s q β) (hQReg : S113XQReg d s q β ρ₀ j m εstar r c₀) :
    S113XLocalizedI d s q β ρ₀ j m εstar r c₀ := by
  intro f0 hf0 ρ hρ N hN Ω _ P _ X₀ W X hX hac0 p₀ hp₀ hmom
  have hQf := fun t (ht : 0 ≤ t) => s113c_Q_facts hd hs0 hs hβ hq hρ₀ hC₁ hc₀ hNL hf0 hρ hN ht
  set Q := s113x_Q d s β ρ N with hQdef
  set qm : ℝ → EucConfig d N → ℝ := fun t => movQDensity d s β N (ρ t) with hqm
  have hQd : ∀ t, 0 ≤ t → Q t = volume.withDensity (fun x => ENNReal.ofReal (qm t x)) := fun t ht => (hQf t ht).1
  have hqpos : ∀ t, 0 ≤ t → ∀ x, 0 < qm t x := fun t ht => (hQf t ht).2.1
  have hqmeas : ∀ t, 0 ≤ t → Measurable (qm t) := fun t ht => (hQf t ht).2.2
  have hQp : ∀ t, 0 ≤ t → IsProbabilityMeasure (Q t) := fun t ht =>
    s113x_Q_prob hd hs0 hs hβ hq hρ₀ hC₁ hc₀ hNL hf0 hρ hN ht
  have hqint : ∀ t, 0 ≤ t → Integrable (qm t) volume := fun t ht => by
    haveI := hQp t ht
    exact s113c_q_integrable (hqmeas t ht) (hqpos t ht) (Q t) (hQd t ht)
  have hqmeas' : ∀ t, 0 ≤ t → Measurable (fun x => ENNReal.ofReal (qm t x)) := fun t ht =>
    ENNReal.measurable_ofReal.comp (hqmeas t ht)
  have hvolac : ∀ t, 0 ≤ t → (volume : Measure (EucConfig d N)) ≪ Q t := fun t ht => by
    rw [hQd t ht]
    exact withDensity_absolutelyContinuous' (hqmeas' t ht).aemeasurable
      (Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.2 (hqpos t ht x)).ne')
  have hQvol : ∀ t, 0 ≤ t → Q t ≪ volume := fun t ht => by
    rw [hQd t ht]; exact withDensity_absolutelyContinuous _ _
  have hinit : P.map X₀ ≪ (volume : Measure (EucConfig d N)) := hac0.trans (hQvol 0 le_rfl)
  have hsol := hX.sol 0
  -- localization
  set h0 : EucConfig d N → ℝ := r2MovRatio d s β ρ N (P.map X₀) 0 with hh0
  have hh0m : Measurable h0 := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  set chi : ℕ → EucConfig d N → ℝ := fun n z => if h0 z ≤ n then 1 else 0 with hchi
  have hchim : ∀ n, Measurable (chi n) := fun n =>
    Measurable.ite (measurableSet_le hh0m measurable_const) measurable_const measurable_const
  have hchi0 : ∀ n z, 0 ≤ chi n z := fun n z => by simp only [hchi]; split_ifs <;> norm_num
  have hchi1 : ∀ n z, chi n z ≤ 1 := fun n z => by simp only [hchi]; split_ifs <;> norm_num
  have hlim : ∀ᵐ ζ ∂P, Tendsto (fun n => chi n (X₀ ζ)) atTop (𝓝 1) := Filter.Eventually.of_forall fun ζ => by
    obtain ⟨N0, hN0⟩ := exists_nat_ge (h0 (X₀ ζ))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop N0] with n hn
    simp only [hchi]
    rw [if_pos (hN0.trans (by exact_mod_cast hn))]
  set Q' : ℝ → Measure (EucConfig d N) := fun t => Q (max t 0) with hQ'
  have hQ'eq : ∀ t, 0 ≤ t → Q' t = Q t := fun t ht => by simp [hQ', max_eq_left ht]
  haveI : ∀ t, SigmaFinite (Q' t) := fun t => by
    haveI := hQp (max t 0) (le_max_right _ _)
    exact inferInstance
  have hQ'ac : ∀ t, 0 ≤ t → ∀ A, MeasurableSet A → Q' t A = 0 →
      volume (A ∩ (eucCollisionSet d N)ᶜ) = 0 := by
    intro t ht A hA hA0
    rw [hQ'eq t ht] at hA0
    exact measure_mono_null Set.inter_subset_left (hvolac t ht hA0)
  have hinit' : P.map X₀ ≪ Q' 0 := by rw [hQ'eq 0 le_rfl]; exact hac0
  have hA3 := fun (t : ℝ) (ht : 0 ≤ t) =>
    s113a_removal_of_localization hβ hX Q' hQ'ac hinit' chi hchim hchi0 hchi1 hlim ht
  set Dn := s113a_domain d N with hDn
  set rr0 : ℕ → ℝ → EucConfig d N → ℝ := fun n t x =>
    ((s113a_killedLaw P (Dn n) X₀ X (chi n) t.toNNReal).rnDeriv (Q t) x).toReal with hrr0
  have hrr0m : ∀ n t, Measurable (rr0 n t) := fun n t => (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hrr00 : ∀ n t x, 0 ≤ rr0 n t x := fun n t x => ENNReal.toReal_nonneg
  -- the bundle for each localization and horizon
  have hbun : ∀ n m : ℕ, 1 ≤ m → ∃ (u : ℝ → EucConfig d N → ℝ) (Z : ℝ), 0 ≤ Z ∧ (∀ t x, 0 ≤ u t x) ∧
      (∀ t, Measurable (u t)) ∧ (∀ t ∈ Set.Icc (0 : ℝ) m, ∀ x, u t x / qm t x ≤ Z) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) m, s113a_killedLaw P (Dn n) X₀ X (chi n) t.toNNReal =
        volume.withDensity (fun x => ENNReal.ofReal (u t x))) ∧
      ∀ p : ℝ → ℝ, AbsolutelyContinuousOnInterval p 0 m → (∀ t ∈ Set.Icc (0 : ℝ) m, 1 < p t) →
        IntervalIntegrable (s113c_Gc d s q β N ρ u p) volume 0 m ∧
        ∀ s' t : ℝ, 0 ≤ s' → s' ≤ t → t ≤ m →
          s113c_Mc d s β N ρ u p t - s113c_Mc d s β N ρ u p s' ≤ ∫ τ in s'..t, s113c_Gc d s q β N ρ u p τ := by
    intro n m hm
    have hmT : (0 : ℝ) < m := by exact_mod_cast hm
    have hDo : IsOpen (Dn n) := s113a_domain_isOpen d N n
    have hDc : IsCompact (closure (Dn n)) := s113a_domain_closure_compact d N n
    have hDf : closure (Dn n) ⊆ (eucCollisionSet d N)ᶜ := s113a_domain_closure_subset_free d N n
    obtain ⟨qt, G', hQr⟩ := hQReg f0 hf0 ρ hρ N hN m hmT (closure (Dn n)) hDc (fun x hx => hDf hx)
    obtain ⟨Cq, hCq⟩ := s113c_qmax hDc hQr
    haveI := hQp 0 le_rfl
    have hC0 : s113a_killedLaw P (Dn n) X₀ X (chi n) 0 ≤ ENNReal.ofReal (n * Cq) • volume := by
      rw [s113c_killedLaw_zero hX (Dn n) hDo (chi n) (hchim n)]
      refine s113c_initial_bound (P.map X₀) (qm 0) (Q 0) (hQd 0 le_rfl) hac0 (chi n) (hchim n) (n := n) ?_
        (Dn n) hDo.measurableSet (Cq := Cq) (fun x hx => hCq 0 ⟨le_rfl, hmT.le⟩ x (subset_closure hx))
      filter_upwards [Measure.rnDeriv_lt_top (P.map X₀) (Q 0)] with x hx
      simp only [hchi]
      by_cases hle : h0 x ≤ n
      · rw [if_pos hle, ENNReal.ofReal_one, one_mul]
        have : ((P.map X₀).rnDeriv (Q 0) x) = ENNReal.ofReal (h0 x) := by
          show _ = ENNReal.ofReal (((P.map X₀).rnDeriv (Q 0) x).toReal)
          exact (ENNReal.ofReal_toReal hx.ne).symm
        rw [this]
        exact ENNReal.ofReal_le_ofReal hle
      · rw [if_neg hle]; simp
    obtain ⟨B, hB0, hB⟩ := hLiou hβ N hN P X₀ W X hX (Dn n) hDo hDc hDf (chi n) (hchim n) (hchi0 n) (hchi1 n)
      (n * Cq) hC0 m hmT.le
    exact s113c_bundle hβ hX (Dn n) hDo hDc hDf (chi n) (hchim n) (hchi0 n) (hchi1 n) hinit hmT hB0 hB hQr
  choose! u Z hZ using hbun
  set mi : ℝ → ℕ := fun t => ⌈t⌉₊ + 1 with hmi
  have hmi1 : ∀ t, 1 ≤ mi t := fun t => by simp [hmi]
  have hmile : ∀ t, 0 ≤ t → t ≤ mi t := fun t ht => by
    have := Nat.le_ceil t
    simp only [hmi]; push_cast; linarith
  set Lc : ℕ → ℝ → ℝ := fun n t => ∑ k ∈ Finset.Icc 1 (mi t), Z n k with hLc
  have hLc0 : ∀ n t, 0 ≤ Lc n t := fun n t =>
    Finset.sum_nonneg fun k hk => (hZ n k (Finset.mem_Icc.1 hk).1).1
  have hLcmono : ∀ n t T, t ≤ T → Lc n t ≤ Lc n T := fun n t T htT => by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right ?_) fun k hk _ =>
      (hZ n k (Finset.mem_Icc.1 hk).1).1
    simp only [hmi]
    have := Nat.ceil_mono htT
    omega
  have hZLc : ∀ n t, Z n (mi t) ≤ Lc n t := fun n t =>
    Finset.single_le_sum (f := fun k => Z n k) (fun k hk => (hZ n k (Finset.mem_Icc.1 hk).1).1)
      (Finset.mem_Icc.2 ⟨hmi1 t, le_rfl⟩)
  -- `rr0` is `u/q` almost everywhere
  have hrr0ae : ∀ n m : ℕ, 1 ≤ m → ∀ t ∈ Set.Icc (0 : ℝ) m,
      rr0 n t =ᵐ[volume.withDensity (fun x => ENNReal.ofReal (qm t x))] fun x => u n m t x / qm t x := by
    intro n m hm t ht
    obtain ⟨-, hu0, hum, -, hdens, -⟩ := hZ n m hm
    haveI : SigmaFinite (volume.withDensity (fun x => ENNReal.ofReal (qm t x))) := by
      rw [← hQd t ht.1]; haveI := hQp t ht.1; infer_instance
    rw [← hQd t ht.1]
    have := s113c_rnDeriv_ae (hqmeas t ht.1) (hqpos t ht.1) (hum t) (hu0 t) _ (hdens t ht)
    rw [← hQd t ht.1] at this
    exact this
  set rr : ℕ → ℝ → EucConfig d N → ℝ := fun n t x => min (rr0 n t x) (Lc n t) with hrr
  have hrreq : ∀ n t, 0 ≤ t → rr n t =ᵐ[Q t] rr0 n t := by
    intro n t ht
    have h1 := hrr0ae n (mi t) (hmi1 t) t ⟨ht, hmile t ht⟩
    rw [← hQd t ht] at h1
    have h2 : ∀ x, u n (mi t) t x / qm t x ≤ Z n (mi t) := (hZ n (mi t) (hmi1 t)).2.2.2.1 t ⟨ht, hmile t ht⟩
    filter_upwards [h1] with x hx
    simp only [hrr]
    rw [min_eq_left]
    rw [hx]
    exact (h2 x).trans (hZLc n t)
  have hrru : ∀ n m : ℕ, 1 ≤ m → ∀ t ∈ Set.Icc (0 : ℝ) m,
      rr n t =ᵐ[volume.withDensity (fun x => ENNReal.ofReal (qm t x))] fun x => u n m t x / qm t x := by
    intro n m hm t ht
    have h1 := hrreq n t ht.1
    rw [hQd t ht.1] at h1
    exact h1.trans (hrr0ae n m hm t ht)
  have hrrm : ∀ n t, Measurable (rr n t) := fun n t => (hrr0m n t).min measurable_const
  have hrr0' : ∀ n t x, 0 ≤ rr n t x := fun n t x => le_min (hrr00 n t x) (hLc0 n t)
  refine ⟨rr, hrrm, hrr0', ?_, ?_, ?_, ?_⟩
  · intro n T
    exact ⟨Lc n T, fun t ht x => (min_le_right _ _).trans (hLcmono n t T ht.2)⟩
  · intro t ht
    have hA := hA3 t ht
    rw [hQ'eq t ht] at hA
    refine ⟨hA.1, ?_⟩
    refine (hA.2.2).congr fun n => ?_
    refine lintegral_congr_ae ?_
    filter_upwards [hrreq n t ht] with x hx
    have hx' : rr n t x = rr0 n t x := hx
    rw [hx']
    rfl
  · intro n
    have hA := hA3 0 le_rfl
    rw [hQ'eq 0 le_rfl] at hA
    have hle := hA.2.1 n
    have hmap : P.map (X (0 : ℝ).toNNReal) = P.map X₀ := by
      rw [Real.toNNReal_zero]; exact Measure.map_congr hsol.init
    rw [hmap] at hle
    refine le_trans ?_ le_self_add
    unfold r2MovPowerMoment
    refine lintegral_mono_ae ?_
    filter_upwards [hle] with x hx
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hrr0' n 0 x) ?_ (by linarith))
    exact (min_le_left _ _).trans hx
  · intro p hp hp1 n T hT
    set M := mi T with hM
    have hM1 : 1 ≤ M := hmi1 T
    have hTM : T ≤ M := hmile T hT
    obtain ⟨hZ0, hu0, hum, hratio, hdens, hchain⟩ := hZ n M hM1
    have hpM : AbsolutelyContinuousOnInterval p 0 M := hp M (by positivity)
    obtain ⟨hGi, hch⟩ := hchain p hpM (fun t ht => hp1 t ht.1)
    have hMeq : ∀ t ∈ Set.Icc (0 : ℝ) M, s113_powerMass (Q t) (rr n t) (p t) =
        s113c_Mc d s β N ρ (u n M) p t := by
      intro t ht
      rw [hQd t ht.1]
      exact s113c_mass_conv (qm t) (hqmeas t ht.1) (hqpos t ht.1) (u n M t) (rr n t)
        (hrru n M hM1 t ht) (p t)
    have hGeq : ∀ τ ∈ Set.Icc (0 : ℝ) M, s113c_Gp Q (rr n) (s113x_source d s q β N ρ) p τ =
        s113c_Gc d s q β N ρ (u n M) p τ := by
      intro τ hτ
      have hp0 : 0 ≤ p τ := by linarith [hp1 τ hτ.1]
      have hint := s113c_hint (hqmeas τ hτ.1) (hqpos τ hτ.1) (hqint τ hτ.1) (hum τ) (hu0 τ)
        (hratio τ hτ) (p τ) hp0
      have e1 := s113c_tilt_conv (μ := volume) (qm τ) (u n M τ) (rr n τ) (s113x_source d s q β N ρ τ)
        (s113x_source d s q β N ρ τ) (hqmeas τ hτ.1) (hqpos τ hτ.1) (hu0 τ) (hrrm n τ) (hrr0' n τ)
        (hrru n M hM1 τ hτ) Filter.EventuallyEq.rfl (p τ) hint
      have hlogae : (fun x => Real.log (rr n τ x)) =ᵐ[volume.withDensity (fun x => ENNReal.ofReal (qm τ x))]
          fun x => Real.log (u n M τ x / qm τ x) := by
        filter_upwards [hrru n M hM1 τ hτ] with x hx
        rw [hx]
      have e2 := s113c_tilt_conv (μ := volume) (qm τ) (u n M τ) (rr n τ) (fun x => Real.log (rr n τ x))
        (fun x => Real.log (u n M τ x / qm τ x)) (hqmeas τ hτ.1) (hqpos τ hτ.1) (hu0 τ) (hrrm n τ) (hrr0' n τ)
        (hrru n M hM1 τ hτ) hlogae (p τ) hint
      simp only [s113c_Gp, s113c_Gc]
      rw [hQd τ hτ.1, mul_assoc, e1, mul_assoc, e2]
      congr 2
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      ring
    have hsub : Set.uIcc (0 : ℝ) T ⊆ Set.uIcc 0 (M : ℝ) := by
      rw [Set.uIcc_of_le hT, Set.uIcc_of_le (by positivity)]
      exact Set.Icc_subset_Icc le_rfl hTM
    refine ⟨?_, fun s' t hs hst htT => ?_⟩
    · have h1 := hGi.mono_set hsub
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at h1 ⊢
      refine h1.congr_fun (fun τ hτ => ?_) measurableSet_Ioc
      exact (hGeq τ ⟨hτ.1.le, hτ.2.trans hTM⟩).symm
    · have hs'M : s' ∈ Set.Icc (0 : ℝ) M := ⟨hs, (hst.trans htT).trans hTM⟩
      have htM : t ∈ Set.Icc (0 : ℝ) M := ⟨hs.trans hst, htT.trans hTM⟩
      rw [hMeq t htM, hMeq s' hs'M]
      refine (hch s' t hs hst (htT.trans hTM)).trans (le_of_eq ?_)
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [Set.uIcc_of_le hst] at hτ
      exact (hGeq τ ⟨hs.trans hτ.1, hτ.2.trans (htT.trans hTM)⟩).symm

end HRS.MS.S113X2C

end
