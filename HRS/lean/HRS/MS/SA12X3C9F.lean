import HRS.MS.SA12X3C9E

/-!
# S.A.12 C9 (SA12X3), part F: the integrated rate of one jet
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MS.UniqT3
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3_rate_idx {m n : ℕ} (hn : n ≤ m) {E : Finset (Fin d → ℤ)} {χ : Euc d → ℝ}
    {Ψ : ℝ → Euc d → Euc d} {τ : ℝ} {z : Fin d → ℤ} {F G : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hω : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
      HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k))))
    {w : Euc d → ℝ} (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w) (hw1 : ∀ x, |w x| ≤ 1)
    (hwW : ∀ x ∈ tsupport w, 1 ≤ sa12z3_W E χ Ψ τ z x) {B1 : ℝ} (hB1 : ∀ x, ‖fderiv ℝ w x‖ ≤ B1)
    {b : Euc d → Euc d} {Cb : ℝ} (hbC : ContDiff ℝ (m + 1) b)
    (hbb : ∀ k, 1 ≤ k → k ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ k b x‖ ≤ Cb) (ν : ℝ) (hν : 0 ≤ ν)
    (idx : Fin n → Fin d) :
    ∫ x, (2 * w x ^ 2 * (partialDeriv idx F x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian F y + inner ℝ (b y) (gradient F y) + G y) x) +
      2 * w x * inner ℝ (b x) (gradient w x) * partialDeriv idx F x ^ 2) ≤
      -(ν * ∑ i : Fin d, ∫ x, (w x * partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x) ^ 2) +
        (4 * ν * d * B1 ^ 2 + d * Cb + 1 + ((d : ℝ) * (Cb * 2 ^ m)) ^ 2 * sa12z3_cT d m) *
          ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F +
        ∫ x, 2 * w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x) := by
  set W : Euc d → ℝ := partialDeriv idx F with hWdef
  have hWi : ContDiff ℝ ∞ W := sa12z3_pd_contDiff_inf hF idx
  have hW2 : ContDiff ℝ 2 W := sa12z3_cd_of_inf hWi 2
  have hW1 : ContDiff ℝ 1 W := sa12z3_cd_of_inf hWi 1
  have hWc : Continuous W := hWi.continuous
  have hbC1 : ContDiff ℝ 1 b := hbC.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
  have hCb0 : 0 ≤ Cb := (norm_nonneg _).trans (hbb 1 le_rfl (by omega) 0)
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  set En : ℝ := ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F with hEn
  have hEn0 : 0 ≤ En := Finset.sum_nonneg fun k _ => sa12x2_cellEnergy_nonneg m χ Ψ τ _ F
  have hwcont : Continuous w := hw.continuous
  have hdw : ∀ i : Fin d, Continuous (fun x => fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ))) := fun i =>
    (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDW : ∀ i : Fin d, Continuous (fun x => fderiv ℝ W x (EuclideanSpace.single i (1 : ℝ))) := fun i =>
    (hW1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDDW : ∀ i : Fin d, Continuous (fun x => D1 i (D1 i W) x) := fun i =>
    (sa12y_D1_contDiff (sa12y_D1_contDiff hWi i) i).continuous
  have hz : ∀ x, x ∉ tsupport w → w x = 0 ∧ ∀ v, fderiv ℝ w x v = 0 := by
    intro x hx
    refine ⟨image_eq_zero_of_notMem_tsupport hx, fun v => ?_⟩
    have hev : w =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
    have := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hev
    rw [this]; simp
  have hint : ∀ f : Euc d → ℝ, Continuous f → (∀ x, x ∉ tsupport w → f x = 0) → Integrable f := fun f hf h0 =>
    Continuous.integrable_of_hasCompactSupport (μ := (volume : Measure (Euc d))) hf
      (HasCompactSupport.intro hwc fun x hx => h0 x hx)
  have hcov : ∀ (f : Euc d → ℝ) (K : ℝ), 0 ≤ K → Continuous f → (∀ x, x ∉ tsupport w → f x = 0) →
      (∀ x, f x ≠ 0 → 1 ≤ sa12z3_W E χ Ψ τ z x) → (∀ x, f x ^ 2 ≤ K * sa12z3_Y m F x) →
      ∫ x, f x ^ 2 ≤ K * En := by
    intro f K hK hfc hf0 hfW hfK
    have := sa12x2_cover_gen m hF hω (K1 := K) (K2 := 0) hK le_rfl hfc
      (HasCompactSupport.intro hwc fun x hx => hf0 x hx)
      (fun x => by have := sa12x2_Yd_nonneg m F x; nlinarith [hfK x]) hfW
    simpa using this
  have hWY : ∀ x, W x ^ 2 ≤ sa12z3_Y m F x := fun x => sa12x2_sq_le_Y hn F idx x
  have hw2 : ∫ x, (w x * W x) ^ 2 ≤ 1 * En := by
    refine hcov (fun x => w x * W x) 1 zero_le_one (hwcont.mul hWc) (fun x hx => by simp [(hz x hx).1])
      (fun x hx => hwW x (subset_tsupport _ (fun h0 => hx (by simp [h0])))) (fun x => ?_)
    have h1 := hw1 x
    have : (w x) ^ 2 ≤ 1 := by nlinarith [abs_nonneg (w x), sq_abs (w x)]
    calc (w x * W x) ^ 2 = w x ^ 2 * W x ^ 2 := by ring
      _ ≤ 1 * W x ^ 2 := by gcongr
      _ ≤ 1 * sa12z3_Y m F x := by gcongr; exact hWY x
  -- smoothness of the transport term
  have hbi : ∀ i : Fin d, ContDiff ℝ n (fun y => b y i) := fun i =>
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp hbC).of_le (by exact_mod_cast (by omega : n ≤ m + 1))
  have hinC : ContDiff ℝ n (fun y => inner ℝ (b y) (gradient F y)) := by
    have : (fun y => inner ℝ (b y) (gradient F y)) = fun y => ∑ i : Fin d, b y i * D1 i F y := by
      funext y; rw [sa12x3_inner_grad]
    rw [this]
    exact ContDiff.sum fun i _ => (hbi i).mul (sa12z3_cd_of_inf (sa12y_D1_contDiff hF i) n)
  set Q : Euc d → ℝ := partialDeriv idx (fun y => inner ℝ (b y) (gradient F y)) with hQ
  have hQc : Continuous Q := (sa12x2_pd_cd (k := 0) (by simpa using hinC) idx).continuous
  have hbfd : Continuous (fun x => fderiv ℝ W x (b x)) :=
    (hW1.continuous_fderiv one_ne_zero).clm_apply hbC1.continuous
  have hwfd : Continuous (fun x => fderiv ℝ w x (b x)) :=
    (hw.continuous_fderiv one_ne_zero).clm_apply hbC1.continuous
  set Cm : Euc d → ℝ := fun x => Q x - fderiv ℝ W x (b x) with hCm
  have hCmc : Continuous Cm := hQc.sub hbfd
  set pG : Euc d → ℝ := partialDeriv idx G with hpG
  have hpGc : Continuous pG := (sa12z3_pd_contDiff_inf hG idx).continuous
  -- the pieces
  have hdec : ∀ x, (2 * w x ^ 2 * (partialDeriv idx F x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian F y + inner ℝ (b y) (gradient F y) + G y) x) +
      2 * w x * inner ℝ (b x) (gradient w x) * partialDeriv idx F x ^ 2) =
      (∑ i : Fin d, ν * (2 * w x ^ 2 * W x * D1 i (D1 i W) x)) +
      (2 * w x ^ 2 * (W x * fderiv ℝ W x (b x)) + 2 * w x * fderiv ℝ w x (b x) * W x ^ 2) +
      2 * w x ^ 2 * (W x * Cm x) + 2 * w x ^ 2 * (W x * pG x) := by
    intro x
    rw [sa12x3_rate_decomp hn hbC hF hG ν idx x, Finset.mul_sum, Finset.mul_sum]
  have hP1c : ∀ i : Fin d, Continuous (fun x => 2 * w x ^ 2 * W x * D1 i (D1 i W) x) := fun i =>
    ((continuous_const.mul (hwcont.pow 2)).mul hWc).mul (hDDW i)
  have hv : ∀ x, x ∉ tsupport w → w x = 0 := fun x hx => (hz x hx).1
  have hI1 : ∀ i : Fin d, Integrable (fun x => ν * (2 * w x ^ 2 * W x * D1 i (D1 i W) x)) := fun i =>
    hint _ (continuous_const.mul (hP1c i)) fun x hx => by simp [hv x hx]
  have hTrc : Continuous (fun x => 2 * w x ^ 2 * (W x * fderiv ℝ W x (b x)) + 2 * w x * fderiv ℝ w x (b x) * W x ^ 2) :=
    ((continuous_const.mul (hwcont.pow 2)).mul (hWc.mul hbfd)).add
      (((continuous_const.mul hwcont).mul hwfd).mul (hWc.pow 2))
  have hI2 := hint _ hTrc fun x hx => by simp [hv x hx, (hz x hx).2]
  have hP3c : Continuous (fun x => 2 * w x ^ 2 * (W x * Cm x)) :=
    (continuous_const.mul (hwcont.pow 2)).mul (hWc.mul hCmc)
  have hI3 := hint _ hP3c fun x hx => by simp [hv x hx]
  have hP4c : Continuous (fun x => 2 * w x ^ 2 * (W x * pG x)) :=
    (continuous_const.mul (hwcont.pow 2)).mul (hWc.mul hpGc)
  have hI4 := hint _ hP4c fun x hx => by simp [hv x hx]
  have hsplit : ∫ x, (2 * w x ^ 2 * (partialDeriv idx F x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian F y + inner ℝ (b y) (gradient F y) + G y) x) +
      2 * w x * inner ℝ (b x) (gradient w x) * partialDeriv idx F x ^ 2) =
      (∑ i : Fin d, ν * ∫ x, 2 * w x ^ 2 * W x * D1 i (D1 i W) x) +
      (∫ x, (2 * w x ^ 2 * (W x * fderiv ℝ W x (b x)) + 2 * w x * fderiv ℝ w x (b x) * W x ^ 2)) +
      (∫ x, 2 * w x ^ 2 * (W x * Cm x)) + ∫ x, 2 * w x ^ 2 * (W x * pG x) := by
    simp_rw [hdec]
    have hIs : Integrable (fun x => ∑ i : Fin d, ν * (2 * w x ^ 2 * W x * D1 i (D1 i W) x)) :=
      integrable_finsetSum _ fun i _ => hI1 i
    have h12 : Integrable (fun x => (∑ i : Fin d, ν * (2 * w x ^ 2 * W x * D1 i (D1 i W) x)) +
        (2 * w x ^ 2 * (W x * fderiv ℝ W x (b x)) + 2 * w x * fderiv ℝ w x (b x) * W x ^ 2)) := hIs.add hI2
    have h123 : Integrable (fun x => (∑ i : Fin d, ν * (2 * w x ^ 2 * W x * D1 i (D1 i W) x)) +
        (2 * w x ^ 2 * (W x * fderiv ℝ W x (b x)) + 2 * w x * fderiv ℝ w x (b x) * W x ^ 2) +
        2 * w x ^ 2 * (W x * Cm x)) := h12.add hI3
    rw [integral_add h123 hI4, integral_add h12 hI3, integral_add hIs hI2,
      integral_finsetSum _ fun i _ => hI1 i]
    simp only [integral_const_mul]
  have hFn : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F := hF.of_le (sa12x2_le_top _)
  -- (A) the cutoff-gradient energy
  have hDw : ∀ i : Fin d, ∫ x, (fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ)) * W x) ^ 2 ≤ B1 ^ 2 * En := by
    intro i
    refine hcov (fun x => fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ)) * W x) (B1 ^ 2) (sq_nonneg _)
      ((hdw i).mul hWc) (fun x hx => by simp [(hz x hx).2]) (fun x hx => ?_) (fun x => ?_)
    · refine hwW x ?_
      by_contra hxn
      exact hx (by simp [(hz x hxn).2])
    · have h1 : |fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ))| ≤ B1 := by
        have := (fderiv ℝ w x).le_opNorm (EuclideanSpace.single i (1 : ℝ))
        have hn1 : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
        rw [hn1, mul_one] at this
        rw [← Real.norm_eq_abs]
        exact this.trans (hB1 x)
      have h2 : (fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ))) ^ 2 ≤ B1 ^ 2 := by
        nlinarith [abs_nonneg (fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ))), sq_abs (fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ)))]
      calc (fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ)) * W x) ^ 2 =
          (fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ))) ^ 2 * W x ^ 2 := by ring
        _ ≤ B1 ^ 2 * W x ^ 2 := by gcongr
        _ ≤ B1 ^ 2 * sa12z3_Y m F x := by gcongr; exact hWY x
  -- (D) diffusion
  have hD : ∀ i : Fin d, ∫ x, 2 * w x ^ 2 * W x * D1 i (D1 i W) x ≤
      -(∫ x, (w x * partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x) ^ 2) + 4 * (B1 ^ 2 * En) := by
    intro i
    set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
    have h1 : ∫ x, 2 * w x ^ 2 * W x * D1 i (D1 i W) x =
        -(2 * ∫ x, w x ^ 2 * (fderiv ℝ W x e) ^ 2) -
          4 * ∫ x, w x * fderiv ℝ w x e * W x * fderiv ℝ W x e := sa12x3_ibp_diffusion hw hwc hW2 i
    have hsnoc : ∀ x, partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x = fderiv ℝ W x e := fun x =>
      (sa12x2_pd_snoc n F hFn idx i x).symm
    have hA : ∫ x, (w x * partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x) ^ 2 =
        ∫ x, w x ^ 2 * (fderiv ℝ W x e) ^ 2 := by simp_rw [hsnoc, mul_pow]
    have hXi : Integrable (fun x => w x * fderiv ℝ w x e * W x * fderiv ℝ W x e) :=
      hint _ (((hwcont.mul (hdw i)).mul hWc).mul (hDW i)) fun x hx => by simp [(hz x hx).1]
    have hAi : Integrable (fun x => w x ^ 2 * (fderiv ℝ W x e) ^ 2) :=
      hint _ ((hwcont.pow 2).mul ((hDW i).pow 2)) fun x hx => by simp [(hz x hx).1]
    have hBi : Integrable (fun x => (fderiv ℝ w x e * W x) ^ 2) :=
      hint _ (((hdw i).mul hWc).pow 2) fun x hx => by simp [(hz x hx).2]
    have hY : -(4 * ∫ x, w x * fderiv ℝ w x e * W x * fderiv ℝ W x e) ≤
        (∫ x, w x ^ 2 * (fderiv ℝ W x e) ^ 2) + 4 * ∫ x, (fderiv ℝ w x e * W x) ^ 2 := by
      calc -(4 * ∫ x, w x * fderiv ℝ w x e * W x * fderiv ℝ W x e)
          = ∫ x, -(4 * (w x * fderiv ℝ w x e * W x * fderiv ℝ W x e)) := by
            rw [integral_neg, integral_const_mul]
        _ ≤ ∫ x, (w x ^ 2 * (fderiv ℝ W x e) ^ 2 + 4 * (fderiv ℝ w x e * W x) ^ 2) :=
            integral_mono (hXi.const_mul 4).neg (hAi.add (hBi.const_mul 4)) fun x => by
              nlinarith [sq_nonneg (w x * fderiv ℝ W x e + 2 * (fderiv ℝ w x e * W x))]
        _ = _ := by rw [integral_add hAi (hBi.const_mul 4), integral_const_mul]
    rw [h1, hA]
    have := hDw i
    nlinarith [hY, this]
  -- (T) transport
  have hbd : Differentiable ℝ b := hbC1.differentiable one_ne_zero
  have hdivb : ∀ x, |∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))| ≤ d * Cb := by
    intro x
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i : Fin d, |fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))| ≤ Cb := by
      intro i
      have h1 : HasFDerivAt (fun y => b y i) ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp (fderiv ℝ b x)) x :=
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x (hbd x).hasFDerivAt
      rw [h1.fderiv]
      have h2 : ‖fderiv ℝ b x‖ ≤ Cb := by
        rw [← norm_iteratedFDeriv_one]; exact hbb 1 le_rfl (by omega) x
      have h3 := (fderiv ℝ b x).le_opNorm (EuclideanSpace.single i (1 : ℝ))
      have hn1 : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
      rw [hn1, mul_one] at h3
      have h4 := PiLp.norm_apply_le (fderiv ℝ b x (EuclideanSpace.single i (1 : ℝ))) i
      simp only [ContinuousLinearMap.comp_apply]
      rw [← Real.norm_eq_abs]
      exact (h4.trans h3).trans h2
    calc ∑ i : Fin d, |fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))| ≤ ∑ _i : Fin d, Cb :=
          Finset.sum_le_sum fun i _ => this i
      _ = d * Cb := by simp
  have hTr : ∫ x, (2 * w x ^ 2 * (W x * fderiv ℝ W x (b x)) + 2 * w x * fderiv ℝ w x (b x) * W x ^ 2) ≤
      d * Cb * En := by
    rw [sa12x3_ibp_transport hw hwc hW1 hbC1]
    have hφi : Integrable (fun x => w x ^ 2 * W x ^ 2) :=
      hint _ ((hwcont.pow 2).mul (hWc.pow 2)) fun x hx => by simp [(hz x hx).1]
    have hdc : Continuous (fun x => ∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))) :=
      continuous_finsetSum _ fun i _ =>
        (((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp hbC1).continuous_fderiv one_ne_zero).clm_apply
          continuous_const
    have hdi : Integrable (fun x => (∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))) *
        (w x ^ 2 * W x ^ 2)) := hint _ (hdc.mul ((hwcont.pow 2).mul (hWc.pow 2))) fun x hx => by simp [(hz x hx).1]
    calc -∫ x, (∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))) * (w x ^ 2 * W x ^ 2)
        = ∫ x, -((∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))) *
            (w x ^ 2 * W x ^ 2)) := (integral_neg _).symm
      _ ≤ ∫ x, (d * Cb) * (w x ^ 2 * W x ^ 2) := integral_mono hdi.neg (hφi.const_mul _) fun x => by
          have := hdivb x
          have h0 : 0 ≤ w x ^ 2 * W x ^ 2 := by positivity
          nlinarith [abs_nonneg (∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))),
            neg_abs_le (∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ)))]
      _ = d * Cb * ∫ x, (w x * W x) ^ 2 := by
          rw [integral_const_mul]; simp_rw [mul_pow]
      _ ≤ d * Cb * En := by
          have := mul_le_mul_of_nonneg_left hw2 (by positivity : (0 : ℝ) ≤ d * Cb)
          linarith
  -- (C) the commutator
  have hCmb : ∀ x, |Cm x| ≤ d * (Cb * 2 ^ m * sa12z3_T m F x) := fun x =>
    sa12x3_comm_pt hn hbC (fun k hk1 hkm => hbb k hk1 hkm) hF idx x
  have hCm2 : ∫ x, (w x * Cm x) ^ 2 ≤ ((d : ℝ) * (Cb * 2 ^ m)) ^ 2 * sa12z3_cT d m * En := by
    refine hcov (fun x => w x * Cm x) (((d : ℝ) * (Cb * 2 ^ m)) ^ 2 * sa12z3_cT d m) (mul_nonneg (sq_nonneg _) (sa12z3_cT_nonneg d m))
      (hwcont.mul hCmc) (fun x hx => by simp [(hz x hx).1])
      (fun x hx => hwW x (subset_tsupport _ (fun h0 => hx (by simp [h0])))) (fun x => ?_)
    have h1 := hCmb x
    have hw2' : w x ^ 2 ≤ 1 := by nlinarith [hw1 x, abs_nonneg (w x), sq_abs (w x)]
    have hT := sa12z3_T_sq m F x
    calc (w x * Cm x) ^ 2 = w x ^ 2 * Cm x ^ 2 := by ring
      _ ≤ 1 * Cm x ^ 2 := by gcongr
      _ ≤ (d * (Cb * 2 ^ m * sa12z3_T m F x)) ^ 2 := by
          rw [one_mul]; nlinarith [abs_nonneg (Cm x), sq_abs (Cm x), h1]
      _ = ((d : ℝ) * (Cb * 2 ^ m)) ^ 2 * sa12z3_T m F x ^ 2 := by ring
      _ ≤ ((d : ℝ) * (Cb * 2 ^ m)) ^ 2 * (sa12z3_cT d m * sa12z3_Y m F x) := by gcongr
      _ = _ := by ring
  have hP3 : ∫ x, 2 * w x ^ 2 * (W x * Cm x) ≤ (∫ x, (w x * W x) ^ 2) + ∫ x, (w x * Cm x) ^ 2 := by
    have hi1 : Integrable (fun x => (w x * W x) ^ 2) :=
      hint _ ((hwcont.mul hWc).pow 2) fun x hx => by simp [(hz x hx).1]
    have hi2 : Integrable (fun x => (w x * Cm x) ^ 2) :=
      hint _ ((hwcont.mul hCmc).pow 2) fun x hx => by simp [(hz x hx).1]
    rw [← integral_add hi1 hi2]
    exact integral_mono hI3 (hi1.add hi2) fun x => by nlinarith [sq_nonneg (w x * W x - w x * Cm x)]
  -- assemble
  rw [hsplit]
  have hsumD : ∑ i : Fin d, ν * ∫ x, 2 * w x ^ 2 * W x * D1 i (D1 i W) x ≤
      ∑ i : Fin d, ν * (-(∫ x, (w x * partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x) ^ 2) +
        4 * (B1 ^ 2 * En)) := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hD i) hν
  have hsumD' : ∑ i : Fin d, ν * (-(∫ x, (w x * partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x) ^ 2) +
        4 * (B1 ^ 2 * En)) = -(ν * ∑ i : Fin d, ∫ x, (w x * partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x) ^ 2) +
        4 * ν * d * B1 ^ 2 * En := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_neg, Finset.sum_neg_distrib]
    ring
  have hP3' := hP3
  have e4 : ∫ x, 2 * w x ^ 2 * (W x * pG x) = ∫ x, 2 * w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x) := rfl
  rw [e4]
  linarith [hsumD, hsumD', hTr, hP3', hCm2, hw2]

end HRS.MH.AdjointRd.Phase2SA12Near
