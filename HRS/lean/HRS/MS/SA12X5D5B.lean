import HRS.MS.SA12X5D5A
import HRS.MS.SA12V2
import HRS.MS.ToriConvAux3
import HRS.MS.ToriCoefBAux5
import HRS.MS.SA12X3W5A

/-!
# S.A.12 X5 D5B: regularity of the periodic drift (`C^∞` in `x`, jointly continuous jets)

For a smooth periodic density path `μ` with `PeriodicTimeSmooth T μ`, every coordinate of `b = M ∇γ_L ⊛ μ - ∇V`
(`torusDriftL`) satisfies `sa12x5_PJC` and `b τ` is `C^∞`.  The cancellation convolution `tcb_T` commutes with `D1 i` and
with all partial derivatives.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction HRS.MS.ToriCoefB HRS.MS.ToriConv

variable {d : ℕ}

theorem sa12x5_nat_le_infty (n : ℕ) : ((n : ℕ) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top

theorem sa12x5_D1_periodic {L : ℝ} {g : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (z : Fin d → ℤ), g (x + L • latticePt z) = g x) (i : Fin d) (y : Euc d)
    (z : Fin d → ℤ) :
    HRS.MS.UniqT3.D1 i g (y + L • latticePt z) = HRS.MS.UniqT3.D1 i g y := by
  unfold HRS.MS.UniqT3.D1
  have h1 : (fun y' => g (y' + L • latticePt (d := d) z)) = g := funext fun y' => hper y' z
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (L • latticePt (d := d) z) (x := y)
  rw [h1] at h2
  rw [← h2]

theorem sa12x5_T_comm {L : ℝ} {k : Euc d → ℝ} {Kf : ℝ} (hL : 0 < L) (hk : tcb_Kern L k Kf) {g : Euc d → ℝ}
    (hg : ContDiff ℝ ∞ g) (hper : ∀ (x : Euc d) (z : Fin d → ℤ), g (x + L • latticePt z) = g x) (i : Fin d) :
    HRS.MS.UniqT3.D1 i (tcb_T L k g) = tcb_T L k (HRS.MS.UniqT3.D1 i g) := by
  funext x
  obtain ⟨Bd, hBd⟩ := sa12v_smooth_bdd L hL hg hper 2
  have hd2 : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) g := hg.of_le (sa12x5_nat_le_infty _)
  have hdf := tcv_hasFDerivAt_lvl hk (n := 0) hd2 (Bd := Bd) (fun i hi y => hBd i (by omega) y) x
  have hgd : Differentiable ℝ (fderiv ℝ g) :=
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp))
  have h0 : ∀ y, ‖fderiv ℝ g y‖ ≤ Bd := fun y => by
    have := hBd 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  have h1 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ Bd := fun y => by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hBd 2 (by omega) y
  have hint := tcb_F_integrable hk (fderiv ℝ g) hgd Bd Bd h0 h1 x
  set e : Euc d := EuclideanSpace.single i 1 with he
  show fderiv ℝ (tcb_T L k g) x e = tcb_T L k (HRS.MS.UniqT3.D1 i g) x
  rw [hdf.fderiv]
  unfold tcb_T
  have hcomm := (ContinuousLinearMap.apply ℝ ℝ e).integral_comp_comm hint
  have hpt : ∀ z, (ContinuousLinearMap.apply ℝ ℝ e) (tcb_F k (fderiv ℝ g) x z) =
      tcb_F k (HRS.MS.UniqT3.D1 i g) x z := by
    intro z
    unfold tcb_F
    by_cases hz : z ∈ tcb_N d
    · simp [Set.indicator_of_mem hz, HRS.MS.UniqT3.D1, he]
    · simp [Set.indicator_of_notMem hz, HRS.MS.UniqT3.D1, he]
  have := hcomm
  simp only [hpt] at this
  exact this.symm

theorem sa12x5_T_smooth {L : ℝ} {k : Euc d → ℝ} {Kf : ℝ} (hL : 0 < L) (hk : tcb_Kern L k Kf) {g : Euc d → ℝ}
    (hg : ContDiff ℝ ∞ g) (hper : ∀ (x : Euc d) (z : Fin d → ℤ), g (x + L • latticePt z) = g x) :
    ContDiff ℝ ∞ (tcb_T L k g) := by
  refine contDiff_infty.2 fun n => ?_
  obtain ⟨Bd, hBd⟩ := sa12v_smooth_bdd L hL hg hper (n + 2)
  exact tcv_T_contDiff hk Bd n ℝ g (hg.of_le (sa12x5_nat_le_infty _)) hBd

theorem sa12x5_T_pd {L : ℝ} {k : Euc d → ℝ} {Kf : ℝ} (hL : 0 < L) (hk : tcb_Kern L k Kf) :
    ∀ (n : ℕ) (g : Euc d → ℝ), ContDiff ℝ ∞ g → (∀ (x : Euc d) (z : Fin d → ℤ), g (x + L • latticePt z) = g x) →
      ∀ idx : Fin n → Fin d, partialDeriv idx (tcb_T L k g) = tcb_T L k (partialDeriv idx g) := by
  intro n
  induction n with
  | zero =>
    intro g hg hper idx
    funext x
    rw [sa12x5_pd_zero]
    have : partialDeriv idx g = g := funext fun y => sa12x5_pd_zero idx g y
    rw [this]
  | succ n ih =>
    intro g hg hper idx
    obtain ⟨idx', i, rfl⟩ : ∃ (idx' : Fin n → Fin d) (i : Fin d), idx = Fin.snoc idx' i :=
      ⟨Fin.init idx, idx (Fin.last n), (Fin.snoc_init_self idx).symm⟩
    have hTg := sa12x5_T_smooth hL hk hg hper
    have hD1 : ContDiff ℝ ∞ (HRS.MS.UniqT3.D1 i g) := sa12y_D1_contDiff hg i
    have e1 : partialDeriv (Fin.snoc idx' i : Fin (n + 1) → Fin d) (tcb_T L k g) =
        partialDeriv idx' (tcb_T L k (HRS.MS.UniqT3.D1 i g)) := by
      funext x
      rw [sa12x5_pd_snoc hTg, sa12x5_T_comm hL hk hg hper i]
    have e2 : partialDeriv (Fin.snoc idx' i : Fin (n + 1) → Fin d) g =
        partialDeriv idx' (HRS.MS.UniqT3.D1 i g) := by
      funext x
      rw [sa12x5_pd_snoc hg]
    rw [e1, e2]
    exact ih _ hD1 (sa12x5_D1_periodic hper i) idx'

theorem sa12x5_pd_contDiff {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {n : ℕ} (idx : Fin n → Fin d) :
    ContDiff ℝ ∞ (partialDeriv idx f) := by
  unfold partialDeriv
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ
    (fun l => (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d))).contDiff.comp
    (hf.iteratedFDeriv_right (m := ∞) (i := n) (by simp))

theorem sa12x5_pd_norm_le {f : Euc d → ℝ} {n : ℕ} (idx : Fin n → Fin d) (y : Euc d) :
    |partialDeriv idx f y| ≤ ‖iteratedFDeriv ℝ n f y‖ := by
  unfold partialDeriv
  rw [← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have : ∏ l : Fin n, ‖(EuclideanSpace.single (idx l) (1 : ℝ) : Euc d)‖ = 1 := by
    simp [EuclideanSpace.norm_single]
  rw [this, mul_one]

theorem sa12x5_fderiv_pd_norm_le {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {n : ℕ} (idx : Fin n → Fin d) (y : Euc d) :
    ‖fderiv ℝ (partialDeriv idx f) y‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f y‖ := by
  set m : Fin n → Euc d := fun l => EuclideanSpace.single (idx l) (1 : ℝ) with hm
  have hdi : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    (hf.iteratedFDeriv_right (m := ∞) (i := n) (by simp)).differentiable (by simp)
  have hpd : partialDeriv idx f =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ m) ∘ (iteratedFDeriv ℝ n f) := rfl
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  have h1 : fderiv ℝ (partialDeriv idx f) y v =
      iteratedFDeriv ℝ (n + 1) f y (Fin.cons v m) := by
    rw [hpd, fderiv_comp y (ContinuousLinearMap.differentiableAt _) (hdi y),
      ContinuousLinearMap.fderiv, iteratedFDeriv_succ_apply_left]
    simp
  rw [h1]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have : ∏ l : Fin (n + 1), ‖(Fin.cons v m : Fin (n + 1) → Euc d) l‖ = ‖v‖ := by
    rw [Fin.prod_univ_succ]
    simp [hm, EuclideanSpace.norm_single]
  rw [this, mul_comm]

theorem sa12x5_jet_unif {L T t : ℝ} (hL : 0 < L) (ht : t ≤ T) {μ : ℝ → Euc d → ℝ}
    (hper : ∀ τ ∈ Icc (0 : ℝ) T, ∀ (x : Euc d) (z : Fin d → ℤ), μ τ (x + L • latticePt z) = μ τ x)
    (hTime : PeriodicTimeSmooth T μ) (n : ℕ) :
    ∃ B : ℝ, ∀ σ ∈ Icc (0 : ℝ) t, ∀ y : Euc d, ‖iteratedFDeriv ℝ n (μ σ) y‖ ≤ B := by
  have hsub : Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d)) ⊆ Icc (0 : ℝ) T ×ˢ univ :=
    prod_mono (Icc_subset_Icc_right ht) subset_rfl
  obtain ⟨B, hB⟩ := sa12v_bdd_param 0 t L hL (fun q : ℝ × Euc d => iteratedFDeriv ℝ n (μ q.1) q.2)
    ((hTime n).mono hsub) (fun σ hσ x z => sa12v_iter_periodic L (hper σ ⟨hσ.1, hσ.2.trans ht⟩) n x z)
  exact ⟨B, fun σ hσ y => hB σ hσ y⟩

theorem sa12x5_T_PJC {L Kf T t : ℝ} {k : Euc d → ℝ} (hL : 0 < L) (hk : tcb_Kern L k Kf) (ht : t ≤ T)
    {μ : ℝ → Euc d → ℝ} (hsm : ∀ τ ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (μ τ))
    (hper : ∀ τ ∈ Icc (0 : ℝ) T, ∀ (x : Euc d) (z : Fin d → ℤ), μ τ (x + L • latticePt z) = μ τ x)
    (hTime : PeriodicTimeSmooth T μ) : sa12x5_PJC t (fun τ => tcb_T L k (μ τ)) := by
  have hsub : Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d)) ⊆ Icc (0 : ℝ) T ×ˢ univ :=
    prod_mono (Icc_subset_Icc_right ht) subset_rfl
  have hmem : ∀ τ ∈ Icc (0 : ℝ) t, τ ∈ Icc (0 : ℝ) T := fun τ hτ => ⟨hτ.1, hτ.2.trans ht⟩
  refine ⟨fun τ hτ => sa12x5_T_smooth hL hk (hsm τ (hmem τ hτ)) (hper τ (hmem τ hτ)), fun n idx => ?_⟩
  have hgc : ContinuousOn (fun p : ℝ × Euc d => partialDeriv idx (μ p.1) p.2) (Icc (0 : ℝ) t ×ˢ univ) := by
    unfold partialDeriv
    exact (continuous_eval_const (fun l : Fin n => (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d))).comp_continuousOn
      ((hTime n).mono hsub)
  obtain ⟨B0, hB0⟩ := sa12x5_jet_unif hL ht hper hTime n
  obtain ⟨B1, hB1⟩ := sa12x5_jet_unif hL ht hper hTime (n + 1)
  have key := sa12v_T_cont hk (fun σ => partialDeriv idx (μ σ)) t hgc
    (fun σ hσ => (sa12x5_pd_contDiff (hsm σ (hmem σ hσ)) idx).differentiable (by simp)) B0 B1
    (fun σ hσ y => by
      rw [Real.norm_eq_abs]; exact (sa12x5_pd_norm_le idx y).trans (hB0 σ hσ y))
    (fun σ hσ y => (sa12x5_fderiv_pd_norm_le (hsm σ (hmem σ hσ)) idx y).trans (hB1 σ hσ y))
  refine key.congr fun p hp => ?_
  rw [sa12x5_T_pd hL hk n (μ p.1) (hsm p.1 (hmem p.1 hp.1)) (hper p.1 (hmem p.1 hp.1)) idx]

theorem sa12x5_grad_coord (f : Euc d → ℝ) (x : Euc d) (i : Fin d) :
    gradient f x i = HRS.MS.UniqT3.D1 i f x := by
  have h2 := EuclideanSpace.inner_single_right i (1 : ℝ) (gradient f x)
  have h3 := InnerProductSpace.toDual_symm_apply (x := EuclideanSpace.single i (1 : ℝ))
    (y := fderiv ℝ f x)
  simp only [one_mul, RCLike.conj_to_real] at h2
  unfold HRS.MS.UniqT3.D1
  exact h2.symm.trans h3

/-- Regularity of the periodic drift coordinates. -/
theorem sa12x5_drift_PJC (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {T L t : ℝ}
    {γ : Euc d → ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ} {μ : ℝ → Euc d → ℝ} {V : Euc d → ℝ}
    {b : ℝ → Euc d → Euc d} (hP : PerSmooth s T L γ M ν μ V b) (hTime : PeriodicTimeSmooth T μ)
    (ht : t ≤ T) (i : Fin d) :
    sa12x5_PJC t (fun τ x => b τ x i) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hP.hL
  obtain ⟨Kf, hKf⟩ := sa12v_kern hd hs0 hsd
  have hk := fun c => hKf L hP.hL γ hP.hγ c
  have hmem : ∀ τ ∈ Icc (0 : ℝ) t, τ ∈ Icc (0 : ℝ) T := fun τ hτ => ⟨hτ.1, hτ.2.trans ht⟩
  have hTc : ∀ c : Fin d, sa12x5_PJC t (fun τ => tcb_T L (fun z => gradient γ z c) (μ τ)) := fun c =>
    sa12x5_T_PJC hL0 (hk c) ht hP.μ_smooth hP.μ_periodic hTime
  have hsum := sa12x5_PJC_sub
    (sa12x5_PJC_sum (t := t) (Finset.univ : Finset (Fin d))
      (fun c τ x => M i c * tcb_T L (fun z => gradient γ z c) (μ τ) x)
      (fun c _ => sa12x5_PJC_smul (hTc c) (M i c)))
    (sa12x5_PJC_const (t := t) (sa12y_D1_contDiff hP.V_smooth i))
  refine sa12x5_PJC_congr (fun τ hτ => ?_) hsum
  funext x
  have hτT := hmem τ hτ
  have hμs := hP.μ_smooth τ hτT
  obtain ⟨Bd, hBd⟩ := sa12v_smooth_bdd L hL0 hμs (hP.μ_periodic τ hτT) 1
  have hb := congrFun (hP.b_eq τ hτT) x
  rw [hb]
  symm
  show (Torus.matVec M (convGradConvL L (gradient γ) (μ τ) x) - gradient V x) i = _
  rw [PiLp.sub_apply, HRS.PDE.SA12W2.sa12x3w_matVec_apply, sa12x5_grad_coord]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [tcb_conv_coord (gradient γ) hk (μ τ) (hμs.of_le (by exact_mod_cast le_top)) Bd Bd
    (fun y => by have := hBd 0 (by omega) y; rwa [norm_iteratedFDeriv_zero] at this)
    (fun y => by have := hBd 1 (by omega) y; rwa [norm_iteratedFDeriv_one] at this) x c]

theorem sa12x5_drift_smooth (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {T L t : ℝ}
    {γ : Euc d → ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ} {μ : ℝ → Euc d → ℝ} {V : Euc d → ℝ}
    {b : ℝ → Euc d → Euc d} (hP : PerSmooth s T L γ M ν μ V b) (hTime : PeriodicTimeSmooth T μ)
    (ht : t ≤ T) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) : ContDiff ℝ ∞ (b τ) :=
  contDiff_euclidean.2 fun i => (sa12x5_drift_PJC hd hs0 hsd hP hTime ht i).1 τ hτ

end HRS.MH.AdjointRd.Phase2SA12X5
