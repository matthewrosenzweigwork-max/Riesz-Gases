import HRS.MS.SA12X5N7
import HRS.MS.SA12X5N1

/-!
# S.A.12 X5 N8: the jets of `perNonlocal L γ M a F` on a cell, per index tuple, from the near/smooth/far identity
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3 HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near
  HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRdP HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x5_sq_sum_bound {M : Matrix (Fin d) (Fin d) ℝ} {MB : ℝ} (hM : PDE.MatBound MB M)
    (u : Fin d → Fin d → ℝ) :
    (∑ i : Fin d, ∑ l : Fin d, M l i * u i l) ^ 2 ≤
      (d : ℝ) ^ 2 * MB ^ 2 * ∑ i : Fin d, ∑ l : Fin d, u i l ^ 2 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
    (f := fun i => ∑ l : Fin d, M l i * u i l)
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ∀ i : Fin d, (∑ l : Fin d, M l i * u i l) ^ 2 ≤ (d : ℝ) * ∑ l : Fin d, (M l i * u i l) ^ 2 :=
    fun i => by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun l => M l i * u i l)
      simpa only [Finset.card_univ, Fintype.card_fin] using this
  have h3 : ∀ i l : Fin d, (M l i * u i l) ^ 2 ≤ MB ^ 2 * u i l ^ 2 := fun i l => by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by
      have := hM l i
      nlinarith [abs_nonneg (M l i), sq_abs (M l i)]) (sq_nonneg _)
  calc (∑ i : Fin d, ∑ l : Fin d, M l i * u i l) ^ 2
      ≤ (d : ℝ) * ∑ i : Fin d, (∑ l : Fin d, M l i * u i l) ^ 2 := h1
    _ ≤ (d : ℝ) * ∑ i : Fin d, ((d : ℝ) * ∑ l : Fin d, MB ^ 2 * u i l ^ 2) := by
        gcongr with i _
        refine (h2 i).trans ?_
        gcongr with l _
        exact h3 i l
    _ = (d : ℝ) ^ 2 * MB ^ 2 * ∑ i : Fin d, ∑ l : Fin d, u i l ^ 2 := by
        simp only [← Finset.mul_sum]
        ring

theorem sa12x5_perNL_idx (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (Cb T : ℝ)
    (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) (E : Finset (Fin d → ℤ)) (hE : CoversBall8 E) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T,
      ∀ (L : ℝ) (γ : Euc d → ℝ), L₀ ≤ L → HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ →
      ∀ (M : Matrix (Fin d) (Fin d) ℝ) (MB : ℝ), PDE.MatBound MB M → ∀ (a F : Euc d → ℝ),
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ F → (∀ (x : Euc d) (k : Fin d → ℤ), a (x + L • latticePt k) = a x) →
      (∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) → ∀ A : ℝ, 0 ≤ A →
      (∀ j ≤ m + 1, ∀ y, ‖iteratedFDeriv ℝ j a y‖ ≤ A) →
      ∀ z : Fin d → ℤ, ∀ n ≤ m, ∀ idx : Fin n → Fin d, ∀ Fb : ℝ,
      (∀ i j : Fin d, ∫ x, (advCutoff χ Ψ τ (cellPt d z) x * sa12x3_Tfar L γ (Ψ τ (cellPt d z))
        (advCutoff χh Ψ τ (cellPt d z)) a F idx i j x) ^ 2 ≤ Fb) →
        ∫ x, (advCutoff χ Ψ τ (cellPt d z) x * partialDeriv idx (fun x => perNonlocal L γ M a F x) x) ^ 2 ≤
          C * MB ^ 2 * A ^ 2 * ∑ k ∈ E, cellEnergy (m + 2) χ Ψ τ (cellPt d (z + k)) F +
            3 * (d : ℝ) ^ 4 * MB ^ 2 * Fb := by
  obtain ⟨R2, δ, h2, L₂, q, hR2, hδ, hh2, hq, hid⟩ := sa12x3_per_identity hd s hs0 hsd m Cb T χ χh hχ
  obtain ⟨CN, hCN0, hCN⟩ := sa12x5_near_cell hd hs0 hsd m Cb T χ χh hχ E hE
  obtain ⟨CS, hCS0, hCS⟩ := sa12x5_smooth_cell hd hs0 m Cb T χ χh hχ E hE q hq
  obtain ⟨R', h, hR', hh, hgeom⟩ := sa12x3_geom hd m Cb T χ χh hχ
  obtain ⟨B, R, hBpos, hR1, hR35⟩ := advected_cutoff_jets d hd m Cb T χ χh hχ
  refine ⟨3 * (CN + CS), max (max L₂ 1) (2 * (R' + h / 2) + 1), by positivity, ?_⟩
  intro b Ψ hb hΨ τ hτ L γ hL hγ M MB hM a F ha hF hap hFp A hA0 hA z n hn idx Fb hFb
  have hL₂ : L₂ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hL1 : 1 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hRL : R' + h / 2 < L / 2 := by
    have := (le_max_right _ _).trans hL
    linarith
  have hK : LocallyIntegrable (rieszKernel d s) (volume : Measure (Euc d)) :=
    rieszKernel_locallyIntegrable hs0 hsd
  have hRz := hR35 b Ψ hb hΨ τ hτ
  set c0 : Euc d := cellPt d z with hc0
  obtain ⟨⟨hwd, hwhd⟩, hjets, hsupp⟩ := hRz c0
  set w : Euc d → ℝ := advCutoff χ Ψ τ c0 with hw
  set η : Euc d → ℝ := advCutoff χh Ψ τ c0 with hη
  set a' : Euc d → ℝ := fun y => η y * a y with ha'def
  have hwcont : Continuous w := hwd.continuous
  have hηcont : Continuous η := hwhd.continuous
  have ha1 : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) a :=
    ha.of_le (by exact_mod_cast (le_top : ((m + 1 : ℕ) : ℕ∞) ≤ ⊤))
  have ha'C : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) a' := hwhd.mul ha1
  have hsupp' : Function.support a' ⊆ closedBall (Ψ τ c0) R :=
    (Function.support_mul_subset_left _ _).trans hsupp
  have hacs : HasCompactSupport a' :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (Ψ τ c0) R) hsupp'
  have hws : Function.support w ⊆ closedBall (Ψ τ c0) R :=
    (sa12z3_adv_support_le hχ Ψ τ c0).trans hsupp
  have hwc : HasCompactSupport w :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (Ψ τ c0) R) hws
  -- the three pieces
  set Nf : Euc d → ℝ := eucNonlocal s M a' F with hNf
  set kk : Fin d → Euc d → ℝ := fun i u => L ^ (-s - 1) *
    fderiv ℝ q (L⁻¹ • u) (EuclideanSpace.single i (1 : ℝ)) with hkk
  have hkc : ∀ i, Continuous (kk i) := fun i =>
    continuous_const.mul (((hq.continuous_fderiv (by simp)).comp (continuous_const_smul L⁻¹)).clm_apply
      continuous_const)
  set Sf : Euc d → ℝ := fun x => ∑ i : Fin d, ∑ j : Fin d,
    M j i * (L ^ (-s - 1) * ∫ y, fderiv ℝ q (L⁻¹ • (x - y)) (EuclideanSpace.single i (1 : ℝ)) *
      (η y * a y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) with hSf
  obtain ⟨Sh, hSs, hFar, hpd⟩ := sa12x3_far_pd hγ hh (R'' := R' + h / 2) (by linarith) le_rfl hRL M
    hwcont hηcont ha.continuous hF (hgeom b Ψ hb hΨ τ hτ c0).2
  set Ff : Euc d → ℝ := fun y => ∑ i : Fin d, ∑ j : Fin d, M j i * Sh i j y with hFf
  -- regularity of Nf and Sf
  have hDF : ∀ l : Fin d, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (D1 l F) := fun l =>
    ((hF.fderiv_right (m := ∞) (by simp)).of_le (by exact_mod_cast le_top)).clm_apply contDiff_const
  have hg : ∀ l : Fin d, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => a' y * D1 l F y) :=
    fun l => ha'C.mul (hDF l)
  have hgc : ∀ l : Fin d, HasCompactSupport (fun y => a' y * D1 l F y) := fun l => hacs.mul_right
  have hNcd : ContDiff ℝ m Nf := by
    have ha1' : ContDiff ℝ 1 a' := ha'C.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
    have hfn : Nf = fun y => ∑ i, ∑ j, M j i *
        HRS.Whole.convFun (rieszKernel d s) (D1 i (fun y => a' y * D1 j F y)) y :=
      funext fun y => sa12z3_eucNL_eq hs0 hsd M ha1' hacs hF y
    rw [hfn]
    refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_const.mul ?_
    refine sa12x5_convFun_cd hK ?_ (D1_supp (hgc j) i)
    exact ((hg j).fderiv_right (m := m) (by push_cast; rfl)).clm_apply contDiff_const
  have hSfun : Sf = fun x => ∑ i : Fin d, ∑ l : Fin d, M l i *
      HRS.Whole.convFun (kk i) (fun y => a' y * D1 l F y) x := by
    funext x
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    unfold HRS.Whole.convFun
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hkk, ha'def, D1]
    ring
  have hScd : ContDiff ℝ m Sf := by
    rw [hSfun]
    refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_const.mul ?_
    exact sa12x5_convFun_cd (hkc i).locallyIntegrable
      ((hg j).of_le (by exact_mod_cast (by omega : m ≤ m + 1))) (hgc j)
  have hFcd : ContDiff ℝ ∞ Ff :=
    ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_const.mul (hSs i j)
  -- the pointwise decomposition of the jets on `{w ≠ 0}`
  have hU : IsOpen {x | w x ≠ 0} := isOpen_ne_fun hwcont continuous_const
  have hdec : ∀ x, w x * partialDeriv idx (fun x => perNonlocal L γ M a F x) x =
      w x * partialDeriv idx Nf x + w x * partialDeriv idx Sf x + w x * partialDeriv idx Ff x := by
    intro x
    by_cases hx : w x = 0
    · simp [hx]
    · have hev : (fun x => perNonlocal L γ M a F x) =ᶠ[𝓝 x] fun y => Nf y + Sf y + Ff y := by
        filter_upwards [hU.mem_nhds hx] with y hy
        have h1 := hid b Ψ hb hΨ τ hτ c0 L γ hL₂ hL1 hγ M a F ha hF hap hFp y hy
        have h2 := hFar y hy
        have h1' : perNonlocal L γ M a F y = Nf y + Sf y + sa12x3_Far L γ (Ψ τ c0) M η a F y := h1
        rw [h1', h2]
      have e1 : partialDeriv idx (fun x => perNonlocal L γ M a F x) x =
          partialDeriv idx (fun y => Nf y + Sf y + Ff y) x := by
        unfold partialDeriv
        rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds]
      have hNn : ContDiffAt ℝ n Nf x := (hNcd.of_le (by exact_mod_cast hn)).contDiffAt
      have hSn : ContDiffAt ℝ n Sf x := (hScd.of_le (by exact_mod_cast hn)).contDiffAt
      have hFn : ContDiffAt ℝ n Ff x := (hFcd.of_le (by exact_mod_cast le_top)).contDiffAt
      have e2 : partialDeriv idx (fun y => Nf y + Sf y + Ff y) x =
          partialDeriv idx Nf x + partialDeriv idx Sf x + partialDeriv idx Ff x := by
        unfold partialDeriv
        have h3 : iteratedFDeriv ℝ n (fun y => Nf y + Sf y + Ff y) x =
            iteratedFDeriv ℝ n (fun y => Nf y + Sf y) x + iteratedFDeriv ℝ n Ff x :=
          iteratedFDeriv_add_apply (f := fun y => Nf y + Sf y) (g := Ff) (hNn.add hSn) hFn
        have h4 : iteratedFDeriv ℝ n (fun y => Nf y + Sf y) x =
            iteratedFDeriv ℝ n Nf x + iteratedFDeriv ℝ n Sf x :=
          iteratedFDeriv_add_apply (f := Nf) (g := Sf) hNn hSn
        rw [h3, h4]
        simp only [ContinuousMultilinearMap.add_apply]
      rw [e1, e2]; ring
  -- continuity and integrability
  have hcont : ∀ f : Euc d → ℝ, ContDiff ℝ m f → Continuous (fun x => w x * partialDeriv idx f x) := by
    intro f hf
    have := sa12z3_pd_contDiff (k := m) (n := n) hf hn idx
    exact hwcont.mul this.continuous
  have hcs : ∀ f : Euc d → ℝ, HasCompactSupport (fun x => w x * partialDeriv idx f x) := fun f =>
    hwc.mul_right
  have hintg : ∀ f : Euc d → ℝ, ContDiff ℝ m f →
      Integrable (fun x => (w x * partialDeriv idx f x) ^ 2) volume := fun f hf =>
    Continuous.integrable_of_hasCompactSupport ((hcont f hf).pow 2)
      ((hcs f).comp_left (g := fun t : ℝ => t ^ 2) (by simp))
  have hNi := hintg Nf hNcd
  have hSi := hintg Sf hScd
  have hFi := hintg Ff (hFcd.of_le (by exact_mod_cast le_top))
  -- the three bounds
  have bN : ∫ x, (w x * partialDeriv idx Nf x) ^ 2 ≤
      CN * MB ^ 2 * A ^ 2 * ∑ k ∈ E, cellEnergy (m + 2) χ Ψ τ (cellPt d (z + k)) F :=
    hCN b Ψ hb hΨ τ hτ M MB hM a F ha hF A hA0 (fun j hj y => hA j hj y) z n hn idx
  have bS : ∫ x, (w x * partialDeriv idx Sf x) ^ 2 ≤
      CS * MB ^ 2 * A ^ 2 * ∑ k ∈ E, cellEnergy (m + 2) χ Ψ τ (cellPt d (z + k)) F :=
    hCS b Ψ hb hΨ τ hτ M MB hM a F ha hF A hA0 (fun j hj y => hA j hj y) z n hn idx L hL1
  have hTeq : ∀ i j x, w x * partialDeriv idx (Sh i j) x =
      w x * sa12x3_Tfar L γ (Ψ τ c0) η a F idx i j x := by
    intro i j x
    by_cases hx : w x = 0
    · simp [hx]
    · rw [hpd n idx i j x hx]
  have hShn : ∀ i j, ContDiff ℝ n (Sh i j) := fun i j =>
    (hSs i j).of_le (by exact_mod_cast le_top)
  have hFjet : ∀ x, partialDeriv idx Ff x = ∑ i : Fin d, ∑ j : Fin d, M j i * partialDeriv idx (Sh i j) x := by
    intro x
    have h1 := sa12z3_pd_sum (Finset.univ : Finset (Fin d)) (fun i y => ∑ j : Fin d, M j i * Sh i j y)
      (fun _ => 1) (n := n) (fun i _ => ContDiff.sum fun j _ => contDiff_const.mul (hShn i j)) idx x
    simp only [one_mul] at h1
    show partialDeriv idx (fun y => ∑ i : Fin d, ∑ j : Fin d, M j i * Sh i j y) x = _
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 := sa12z3_pd_sum (Finset.univ : Finset (Fin d)) (fun j y => Sh i j y) (fun j => M j i)
      (n := n) (fun j _ => hShn i j) idx x
    rw [h2]
  have hPc : ∀ i j, Continuous (fun x => w x * partialDeriv idx (Sh i j) x) := fun i j =>
    hwcont.mul (sa12z3_pd_contDiff_inf (hSs i j) idx).continuous
  have hPi : ∀ i j, Integrable (fun x => (w x * partialDeriv idx (Sh i j) x) ^ 2) volume := fun i j =>
    Continuous.integrable_of_hasCompactSupport ((hPc i j).pow 2)
      ((hwc.mul_right (f' := partialDeriv idx (Sh i j))).comp_left (g := fun t : ℝ => t ^ 2) (by simp))
  have bF : ∫ x, (w x * partialDeriv idx Ff x) ^ 2 ≤ (d : ℝ) ^ 4 * MB ^ 2 * Fb := by
    have hpt : ∀ x, (w x * partialDeriv idx Ff x) ^ 2 ≤
        (d : ℝ) ^ 2 * MB ^ 2 * ∑ i : Fin d, ∑ j : Fin d, (w x * partialDeriv idx (Sh i j) x) ^ 2 := by
      intro x
      have := sa12x5_sq_sum_bound hM (fun i j => w x * partialDeriv idx (Sh i j) x)
      rw [hFjet x, Finset.mul_sum]
      calc (∑ i : Fin d, w x * ∑ j : Fin d, M j i * partialDeriv idx (Sh i j) x) ^ 2
          = (∑ i : Fin d, ∑ j : Fin d, M j i * (w x * partialDeriv idx (Sh i j) x)) ^ 2 := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ ≤ _ := this
    have hRint : Integrable (fun x => (d : ℝ) ^ 2 * MB ^ 2 * ∑ i : Fin d, ∑ j : Fin d,
        (w x * partialDeriv idx (Sh i j) x) ^ 2) volume :=
      (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hPi i j).const_mul _
    refine (integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hRint
      (Eventually.of_forall hpt)).trans ?_
    rw [integral_const_mul, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hPi i j]
    have hsum : ∑ i : Fin d, ∫ x, ∑ j : Fin d, (w x * partialDeriv idx (Sh i j) x) ^ 2 ≤
        (d : ℝ) * ((d : ℝ) * Fb) := by
      calc ∑ i : Fin d, ∫ x, ∑ j : Fin d, (w x * partialDeriv idx (Sh i j) x) ^ 2
          = ∑ i : Fin d, ∑ j : Fin d, ∫ x, (w x * partialDeriv idx (Sh i j) x) ^ 2 :=
            Finset.sum_congr rfl fun i _ => integral_finset_sum _ fun j _ => hPi i j
        _ ≤ ∑ i : Fin d, ∑ j : Fin d, Fb := by
            gcongr with i _ j _
            have := hFb i j
            refine le_of_eq_of_le ?_ this
            exact integral_congr_ae (Eventually.of_forall fun x => by
              simp only
              rw [hTeq i j x])
        _ = _ := by simp
    calc (d : ℝ) ^ 2 * MB ^ 2 * ∑ i : Fin d, ∫ x, ∑ j : Fin d, (w x * partialDeriv idx (Sh i j) x) ^ 2
        ≤ (d : ℝ) ^ 2 * MB ^ 2 * ((d : ℝ) * ((d : ℝ) * Fb)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (d : ℝ) ^ 4 * MB ^ 2 * Fb := by ring
  -- assemble
  have hptt : ∀ x, (w x * partialDeriv idx (fun x => perNonlocal L γ M a F x) x) ^ 2 ≤
      3 * ((w x * partialDeriv idx Nf x) ^ 2 + (w x * partialDeriv idx Sf x) ^ 2 +
        (w x * partialDeriv idx Ff x) ^ 2) := by
    intro x
    rw [hdec x]
    nlinarith [sq_nonneg (w x * partialDeriv idx Nf x - w x * partialDeriv idx Sf x),
      sq_nonneg (w x * partialDeriv idx Nf x - w x * partialDeriv idx Ff x),
      sq_nonneg (w x * partialDeriv idx Sf x - w x * partialDeriv idx Ff x)]
  have hGi : Integrable (fun x => 3 * ((w x * partialDeriv idx Nf x) ^ 2 + (w x * partialDeriv idx Sf x) ^ 2 +
        (w x * partialDeriv idx Ff x) ^ 2)) volume := ((hNi.add hSi).add hFi).const_mul _
  refine (integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hGi
    (Eventually.of_forall hptt)).trans ?_
  rw [integral_const_mul, integral_add (f := fun x => (w x * partialDeriv idx Nf x) ^ 2 +
    (w x * partialDeriv idx Sf x) ^ 2) (g := fun x => (w x * partialDeriv idx Ff x) ^ 2) (hNi.add hSi) hFi,
    integral_add (f := fun x => (w x * partialDeriv idx Nf x) ^ 2)
    (g := fun x => (w x * partialDeriv idx Sf x) ^ 2) hNi hSi]
  nlinarith [bN, bS, bF]

end HRS.MH.AdjointRd.Phase2SA12X5
