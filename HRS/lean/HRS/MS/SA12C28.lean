import HRS.MS.SA12C27

/-!
# S.A.12(c), packet E7.04: the remainder family bound

`∫_{c ∈ Q_L} jetSq_m(χ(·-c); perNonlocal - eucNonlocal(χ̂_c μ)) ≤ C c_χ Λμ² E_{m,L}(F)`
(periodic Young inequality + uniform `L²` bound of the remainder kernel + exact translation averaging).
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

theorem sa12c_remainder_family_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hs1 : (d : ℝ) < 2 * (s + 1)) (m : ℕ) (hm : 1 ≤ m) {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh)
    (MB : ℝ) :
    ∃ L1 : ℝ, 40 ≤ L1 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, L1 ≤ L → ∀ γ : Euc d → ℝ,
      IsPeriodicRieszKernel d s L γ → ∀ M : Matrix (Fin d) (Fin d) ℝ, PDE.MatBound MB M →
      ∀ μ F : Euc d → ℝ, ContDiff ℝ ∞ μ → ContDiff ℝ ∞ F →
      (∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x) →
      (∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) →
      ∀ K2 : ℝ, ∫ x in periodBox d L, μ x ^ 2 ≤ K2 →
        Integrable (fun c => jetSq m (fun x => χ (x - c))
          (fun x => perNonlocal L γ M μ F x - eucNonlocal s M (fun y => χh (y - c) * μ y) F x))
          (volume.restrict (periodBox d L)) ∧
        ∫ c in periodBox d L, jetSq m (fun x => χ (x - c))
          (fun x => perNonlocal L γ M μ F x - eucNonlocal s M (fun y => χh (y - c) * μ y) F x) ≤
          C * (∫ x, χ x ^ 2) * K2 * boxEnergy m L F := by
  obtain ⟨δ, q, hδ0, hδ1, hq, hloc⟩ := sa12c_kernel_local_deriv hd s hs0 hsd
  obtain ⟨L0, hL01, C3, hC30, hK3⟩ := sa12c_remainder_kernel_l2 hd s hs0 hsd hs1 m hχ
  refine ⟨max L0 (max 40 (4 / δ)), le_trans (le_max_left _ _) (le_max_right _ _),
    ((d : ℝ) + 1) ^ m * ((d : ℝ) ^ 4 * MB ^ 2 * C3), by positivity, ?_⟩
  intro L hL γ hγ M hM μ F hμ hF hμp hFp K2 hμ2
  have hL0' : L0 ≤ L := (le_max_left _ _).trans hL
  have hL40 : 40 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have h4δ : 4 / δ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have h4 : 4 ≤ δ * L := by rwa [div_le_iff₀ hδ0, mul_comm] at h4δ
  obtain ⟨⟨c0, hc0⟩, -⟩ := hloc L hL1 γ hγ
  have hΘ : ∀ z : Euc d, z ≠ 0 → ‖z‖ < 4 → γ z = rieszKernel d s z + sa12cTh s L c0 q z :=
    fun z hz0 hz4 => hc0 z hz0 (lt_of_lt_of_le hz4 h4)
  set e : Fin d → Euc d := fun j => EuclideanSpace.single j (1 : ℝ) with he
  set fj : Fin d → Euc d → ℝ := fun j y => μ y * fderiv ℝ F y (e j) with hfj
  have hfjs : ∀ j, ContDiff ℝ ∞ (fj j) := fun j =>
    hμ.mul ((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hfjc : ∀ j, Continuous (fj j) := fun j => (hfjs j).continuous
  have hfjp : ∀ j (x : Euc d) (k : Fin d → ℤ), fj j (x + L • latticePt k) = fj j x := by
    intro j x k
    simp only [hfj]
    rw [hμp x k, sa12v_fderiv_periodic L hFp (e j) x k]
  have hfjb : ∀ j, ∃ B : ℝ, ∀ x, |fj j x| ≤ B := fun j => by
    obtain ⟨B, hB⟩ := sa12v_bdd L hL0 (fj j) (hfjc j) (hfjp j)
    exact ⟨B, fun x => by simpa [Real.norm_eq_abs] using hB x⟩
  choose Bf hBf using hfjb
  set E : ℝ := boxEnergy m L F with hEdef
  have hE0 : 0 ≤ E := boxEnergy_nonneg m L F
  have hχc : Continuous χ := hχ.1.1.continuous
  have hχ0 : ∀ u : Euc d, 2 ≤ ‖u‖ → χ u = 0 := by
    intro u hu
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hχ.1.2.2.1 hmem
    rw [Metric.mem_ball, dist_zero_right] at this
    linarith
  -- the smooth family
  let Hij : ∀ {j : ℕ}, (Fin j → Fin d) → Fin d → Fin d → Euc d → Euc d → ℝ :=
    fun {j} α i j' v x => ∫ z in sa12cWcell d L,
      sa12cKap s L c0 q χ χh γ (Fin.snoc α i : Fin (j + 1) → Fin d) v z * fj j' (x - z) 
  have hHc : ∀ {j : ℕ} (α : Fin j → Fin d) i j', Continuous (fun p : Euc d × Euc d => Hij α i j' p.1 p.2) :=
    fun {j} α i j' => sa12c_H_continuous hL0 hχ hq hγ (Fin.snoc α i : Fin (j + 1) → Fin d) (hfjc j') (hBf j')
  have hHp : ∀ {j : ℕ} (α : Fin j → Fin d) i j' (v x : Euc d) (k : Fin d → ℤ),
      Hij α i j' v (x + L • latticePt k) = Hij α i j' v x := by
    intro j α i j' v x k
    simp only [Hij]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [show x + L • latticePt k - z = (x - z) + L • latticePt k by abel, hfjp]
  let Hs : ∀ {j : ℕ}, (Fin j → Fin d) → Euc d → Euc d → ℝ :=
    fun {j} α v x => ∑ i : Fin d, ∑ j' : Fin d, M j' i * Hij α i j' v x 
  let Fam : ∀ {j : ℕ}, (Fin j → Fin d) → Euc d → Euc d → ℝ :=
    fun {j} α c x => (χ (x - c) * Hs α (x - c) x) ^ 2 
  have hFcont : ∀ {j : ℕ} (α : Fin j → Fin d), Continuous (Function.uncurry (Fam α)) := by
    intro j α
    have h1 : Continuous fun p : Euc d × Euc d => Hs α (p.2 - p.1) p.2 := by
      simp only [Hs]
      refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j' _ => continuous_const.mul ?_
      exact (hHc α i j').comp ((continuous_snd.sub continuous_fst).prodMk continuous_snd)
    exact ((hχc.comp (continuous_snd.sub continuous_fst)).mul h1).pow 2
  have hFper : ∀ {j : ℕ} (α : Fin j → Fin d) (c x : Euc d) (k : Fin d → ℤ),
      Fam α (c + L • latticePt k) (x + L • latticePt k) = Fam α c x := by
    intro j α c x k
    simp only [Fam, Hs]
    have e1 : x + L • latticePt k - (c + L • latticePt k) = x - c := by abel
    rw [e1]
    simp_rw [hHp]
  have hFsupp : ∀ {j : ℕ} (α : Fin j → Fin d) (c x : Euc d), 2 < ‖x - c‖ → Fam α c x = 0 := by
    intro j α c x hx
    simp [Fam, hχ0 _ hx.le]
  -- identification with the true jets
  have hFtrue : ∀ {j : ℕ} (α : Fin j → Fin d) (c x : Euc d),
      (χ (x - c) * partialDeriv α (fun x => perNonlocal L γ M μ F x -
        eucNonlocal s M (fun y => χh (y - c) * μ y) F x) x) ^ 2 = Fam α c x := by
    intro j α c x
    by_cases hx : ‖x - c‖ < 2
    · have := sa12c_remainder_jet hd hs0 hsd hL40 hχ hγ hq hΘ M hμ hF hμp hFp c x hx α
      rw [this]
    · push Not at hx
      simp [Fam, hχ0 _ hx]
  -- the key bound for each jet
  have hkey : ∀ {j : ℕ}, j ≤ m → ∀ α : Fin j → Fin d,
      ∫ c in periodBox d L, ∫ x, Fam α c x ≤
        (∫ x, χ x ^ 2) * ((d : ℝ) ^ 4 * MB ^ 2 * C3 * K2 * E) := by
    intro j hj α
    rw [sa12c_avg_family hL0 (hFcont α) (hFper α) (R := 2) (hFsupp α)]
    set K : ℝ := (d : ℝ) ^ 4 * MB ^ 2 * C3 * K2 * E with hK
    have hχint : Integrable (fun v : Euc d => χ v ^ 2) volume := by
      refine (hχc.pow 2).integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 2) fun v hv => ?_
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hv
      simp [hχ0 v hv.le]
    have hQm := sa12c20_box_meas (d := d) L
    -- bound of the inner integral for a fixed `v`
    have hH2 : ∀ v : Euc d, ‖v‖ < 2 → ∀ i j', ∫ x in periodBox d L, (Hij α i j' v x) ^ 2 ≤
        C3 * (K2 * E) := by
      intro v hv i j'
      obtain ⟨hint_cube, hbound⟩ := hK3 L hL0' γ hγ (j + 1) (by omega) (by omega)
        (Fin.snoc α i : Fin (j + 1) → Fin d) v hv.le
      have hae := sa12c_kap_ae_rho (s := s) (L := L) (c0 := c0) hd hL40 hχ hq hΘ
        (Fin.snoc α i : Fin (j + 1) → Fin d) v hv
      have hρW : IntegrableOn (fun z => (sa12cKap s L c0 q χ χh γ (Fin.snoc α i : Fin (j + 1) → Fin d) v z) ^ 2)
          (sa12cWcell d L) volume :=
        (hint_cube.mono_set (sa12c_W_sub_cube (d := d) L)).congr_fun_ae (hae.mono fun z hz => by simpa only [] using congrArg (fun t : ℝ => t ^ 2) hz.symm)
      have hKW : ∫ z in sa12cWcell d L, (sa12cKap s L c0 q χ χh γ (Fin.snoc α i : Fin (j + 1) → Fin d) v z) ^ 2 ≤ C3 := by
        calc _ = ∫ z in sa12cWcell d L, (sa12cRho s χh γ (Fin.snoc α i : Fin (j + 1) → Fin d) v z) ^ 2 :=
              integral_congr_ae (hae.mono fun z hz => by simpa only [] using congrArg (fun t : ℝ => t ^ 2) hz)
          _ ≤ ∫ z in sa12cCube d L, (sa12cRho s χh γ (Fin.snoc α i : Fin (j + 1) → Fin d) v z) ^ 2 :=
              setIntegral_mono_set (hint_cube) (Eventually.of_forall fun z => sq_nonneg _)
                (HasSubset.Subset.eventuallyLE (sa12c_W_sub_cube (d := d) L))
          _ ≤ C3 := hbound
      have hY := sa12c_young hL0
        (ρ := fun z => sa12cKap s L c0 q χ χh γ (Fin.snoc α i : Fin (j + 1) → Fin d) v z) (f := fj j')
        (sa12cKap_continuous hL0 hχ hq hγ _ v).aestronglyMeasurable hρW (hfjc j') (hfjp j')
      have hL1b : (∫ y in periodBox d L, |fj j' y|) ^ 2 ≤ K2 * E := by
        have h1 := sa12c_L1_bound hL0 hμ.continuous
          ((hF.continuous_fderiv (by simp)).clm_apply continuous_const :
            Continuous fun x => fderiv ℝ F x (e j'))
        have h2 := sa12c_first_jet_le hm L hF j'
        have h3 : (∫ y in periodBox d L, |fj j' y|) = ∫ x in periodBox d L, |μ x * fderiv ℝ F x (e j')| := rfl
        rw [h3]
        refine h1.trans ?_
        exact mul_le_mul hμ2 h2 (setIntegral_nonneg hQm fun x _ => sq_nonneg _)
          ((setIntegral_nonneg hQm fun x _ => sq_nonneg _).trans hμ2)
      have hHij : ∫ x in periodBox d L, (Hij α i j' v x) ^ 2 ≤
          (∫ z in sa12cWcell d L, (sa12cKap s L c0 q χ χh γ (Fin.snoc α i : Fin (j + 1) → Fin d) v z) ^ 2) *
            (∫ y in periodBox d L, |fj j' y|) ^ 2 := hY
      refine hHij.trans ?_
      exact mul_le_mul hKW hL1b (sq_nonneg _) hC30
    have hmain : ∀ v : Euc d, ‖v‖ < 2 → ∫ x in periodBox d L, (Hs α v x) ^ 2 ≤ K := by
      intro v hv
      have hHvc : ∀ i j', Continuous fun x => Hij α i j' v x :=
        fun i j' => (hHc α i j').comp (continuous_const.prodMk continuous_id)
      have hI : ∀ i j', IntegrableOn (fun x => (Hij α i j' v x) ^ 2) (periodBox d L) :=
        fun i j' => sa12v_integrableOn_box L ((hHvc i j').pow 2)
      have hpt : ∀ x, (Hs α v x) ^ 2 ≤ ((d : ℝ) ^ 2 * MB ^ 2) *
          ∑ i : Fin d, ∑ j' : Fin d, (Hij α i j' v x) ^ 2 := fun x =>
        sa12c_matsum_sq hM (fun i j' => Hij α i j' v x)
      have hIs : IntegrableOn (fun x => ((d : ℝ) ^ 2 * MB ^ 2) *
          ∑ i : Fin d, ∑ j' : Fin d, (Hij α i j' v x) ^ 2) (periodBox d L) := by
        exact (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j' _ => hI i j').const_mul _
      calc ∫ x in periodBox d L, (Hs α v x) ^ 2
          ≤ ∫ x in periodBox d L, ((d : ℝ) ^ 2 * MB ^ 2) *
              ∑ i : Fin d, ∑ j' : Fin d, (Hij α i j' v x) ^ 2 :=
            integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hIs (Eventually.of_forall hpt)
        _ = ((d : ℝ) ^ 2 * MB ^ 2) * ∑ i : Fin d, ∑ j' : Fin d, ∫ x in periodBox d L, (Hij α i j' v x) ^ 2 := by
            rw [integral_const_mul, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j' _ => hI i j']
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [integral_finset_sum _ fun j' _ => hI i j']
        _ ≤ ((d : ℝ) ^ 2 * MB ^ 2) * ∑ _i : Fin d, ∑ _j' : Fin d, C3 * (K2 * E) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j' _ => hH2 v hv i j'
        _ = K := by simp [hK]; ring
    refine (integral_mono_of_nonneg (Eventually.of_forall fun v =>
      setIntegral_nonneg hQm fun x _ => sq_nonneg _) (hχint.mul_const K) (Eventually.of_forall fun v => ?_)).trans
      (le_of_eq (by rw [integral_mul_const]))
    by_cases hv : ‖v‖ < 2
    · have hfam : ∀ x, Fam α (x - v) x = χ v ^ 2 * (Hs α v x) ^ 2 := by
        intro x; simp only [Fam, sub_sub_cancel]; ring
      change (∫ x in periodBox d L, Fam α (x - v) x) ≤ _
      simp_rw [hfam]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hmain v hv) (sq_nonneg _)
    · have hχv : χ v = 0 := hχ0 v (not_lt.1 hv)
      have hfam : ∀ x, Fam α (x - v) x = 0 := by
        intro x; simp [Fam, hχv]
      change (∫ x in periodBox d L, Fam α (x - v) x) ≤ _
      simp_rw [hfam]
      simp [hχv]
  -- sum over jets
  have hint : ∀ {j : ℕ} (α : Fin j → Fin d), Integrable (fun c => ∫ x, Fam α c x)
      (volume.restrict (periodBox d L)) := fun {j} α =>
    sa12v_integrableOn_box L (sa12c_avg_inner_cont (hFcont α) (fun c x hx => hFsupp α c x hx))
  have hjeq : ∀ c : Euc d, jetSq m (fun x => χ (x - c))
        (fun x => perNonlocal L γ M μ F x - eucNonlocal s M (fun y => χh (y - c) * μ y) F x) =
      ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ α : Fin j → Fin d, ∫ x, Fam α c x := by
    intro c
    simp only [jetSq]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    exact integral_congr_ae (Eventually.of_forall fun x => hFtrue α c x)
  have hjint : Integrable (fun c => jetSq m (fun x => χ (x - c))
      (fun x => perNonlocal L γ M μ F x - eucNonlocal s M (fun y => χh (y - c) * μ y) F x))
      (volume.restrict (periodBox d L)) := by
    simp_rw [hjeq]
    exact integrable_finset_sum _ fun j _ => (integrable_finset_sum _ fun α _ => hint α).const_mul _
  refine ⟨hjint, ?_⟩
  calc ∫ c in periodBox d L, jetSq m (fun x => χ (x - c))
        (fun x => perNonlocal L γ M μ F x - eucNonlocal s M (fun y => χh (y - c) * μ y) F x)
      = ∫ c in periodBox d L, ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) *
          ∑ α : Fin j → Fin d, ∫ x, Fam α c x := by
        refine integral_congr_ae (Eventually.of_forall fun c => hjeq c)
    _ = ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) *
          ∑ α : Fin j → Fin d, ∫ c in periodBox d L, ∫ x, Fam α c x := by
        rw [integral_finset_sum _ fun j _ => (integrable_finset_sum _ fun α _ => hint α).const_mul _]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul, integral_finset_sum _ fun α _ => hint α]
    _ ≤ ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) *
          ∑ _α : Fin j → Fin d, ((∫ x, χ x ^ 2) * ((d : ℝ) ^ 4 * MB ^ 2 * C3 * K2 * E)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ =>
          hkey (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) α) (Nat.cast_nonneg _)
    _ = (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j) *
          ((∫ x, χ x ^ 2) * ((d : ℝ) ^ 4 * MB ^ 2 * C3 * K2 * E)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow]
        ring
    _ = (((d : ℝ) + 1) ^ m * ((d : ℝ) ^ 4 * MB ^ 2 * C3)) * (∫ x, χ x ^ 2) * K2 * E := by
        rw [sa12c_choose_card d m]; ring

end HRS.MH.AdjointRd.Phase2SA12C
