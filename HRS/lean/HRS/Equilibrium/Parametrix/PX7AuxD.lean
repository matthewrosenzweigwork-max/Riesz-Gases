import HRS.Equilibrium.Parametrix.PX7AuxC

/-!
# Packet PX7, file D: the pair semigroup on `C^{2m}` kernels

`pairSemigroup τ R = ev (PP τ (arr R))`; consequences: `C²` bounds with exponential decay, continuity of the
jets in `τ`, doubly centering, linearity and symmetry.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.PX7

open HRS.PDE.MFAdjoint

variable {d : ℕ}

section PairKernel

variable {D : DynData d} {ρ : Torus d → ℝ} {m : ℕ} {T : ℝ → Coeff d → Coeff d} {Ah : Coeff d → Coeff d}

theorem px7_PP_bound (hOV : OV D ρ m T Ah) :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ τ : ℝ, 0 ≤ τ → ∀ u : Arr d, Mem2 (m : ℝ) (m : ℝ) u →
      Mem2 (m : ℝ) (m : ℝ) (PP T τ u) ∧
        nrm2 (m : ℝ) (m : ℝ) (PP T τ u) ≤ M ^ 2 * Real.exp (-(2 * c) * τ) * nrm2 (m : ℝ) (m : ℝ) u := by
  obtain ⟨M, c, hM, hc, hop⟩ := hOV.opok
  refine ⟨M, c, hM, hc, fun τ hτ u hu => ?_⟩
  have hF := hop τ hτ
  obtain ⟨h1, h2⟩ := px7_colOp_mem hF hu
  obtain ⟨h3, h4⟩ := px7_rowOp_mem hF h1
  refine ⟨h3, ?_⟩
  unfold PP
  have e : M ^ 2 * Real.exp (-(2 * c) * τ) = (M * Real.exp (-c * τ)) * (M * Real.exp (-c * τ)) := by
    have : Real.exp (-(2 * c) * τ) = Real.exp (-c * τ) * Real.exp (-c * τ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  rw [e]
  calc _ ≤ (M * Real.exp (-c * τ)) * nrm2 (m : ℝ) (m : ℝ) (colOp (T τ) u) := h4
    _ ≤ (M * Real.exp (-c * τ)) * ((M * Real.exp (-c * τ)) * nrm2 (m : ℝ) (m : ℝ) u) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- Array data of a `C^{m+m}` kernel. -/
theorem px7_arr_data (hOV : OV D ρ m T Ah) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : Torus d → Torus d → ℝ, IsCk2 (m + m) R →
      Mem2 (m : ℝ) (m : ℝ) (arr R) ∧ RS (arr R) ∧ nrm2 (m : ℝ) (m : ℝ) (arr R) ≤ K * cbNorm2 (m + m) R := by
  obtain ⟨K, hK, h⟩ := px7_parseval (d := d) m m
  refine ⟨K, hK, fun R hR => ?_⟩
  obtain ⟨h1, h2⟩ := h R hR
  have hc : Continuous (lift2 R) := by
    have : IsCk2 0 R := hR.of_le (by exact_mod_cast Nat.zero_le _)
    simpa [IsCk2] using this.continuous
  exact ⟨h1, px7_arr_RS hc, h2⟩

/-- The pair semigroup in tensor form. -/
theorem px7_pair_ev (hOV : OV D ρ m T Ah) {R : Torus d → Torus d → ℝ} (hR : IsCk2 (m + m) R)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    pairSemigroup D ρ τ R = ev (PP T τ (arr R)) := by
  obtain ⟨K, hK, h⟩ := px7_arr_data hOV
  obtain ⟨h1, h2, -⟩ := h R hR
  have hRe : R = ev (arr R) := funext fun x => funext fun y => px7_inversion hOV.hd hR x y
  funext x y
  conv_lhs => rw [hRe]
  exact px7_key hOV hτ h1 h2 x y

theorem px7_pair_C2 (hOV : OV D ρ m T Ah) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ R : Torus d → Torus d → ℝ, IsCk2 (m + m) R → ∀ τ : ℝ, 0 ≤ τ →
      IsCk2 2 (pairSemigroup D ρ τ R) ∧
      cbNorm2 2 (pairSemigroup D ρ τ R) ≤ (C * cbNorm2 (m + m) R) * Real.exp (-c * τ) := by
  obtain ⟨M, c, hM, hc, hPP⟩ := px7_PP_bound hOV
  obtain ⟨K, hK, hdata⟩ := px7_arr_data hOV
  obtain ⟨A, hA, hev⟩ := px7_ev_C2 (d := d) (m := m) (by have := hOV.hm_gt; linarith)
  refine ⟨A * (M ^ 2 * K), 2 * c, by positivity, by positivity, fun R hR τ hτ => ?_⟩
  obtain ⟨h1, -, h3⟩ := hdata R hR
  obtain ⟨h4, h5⟩ := hPP τ hτ _ h1
  rw [px7_pair_ev hOV hR hτ]
  obtain ⟨h6, h7⟩ := hev _ h4
  refine ⟨h6, h7.trans ?_⟩
  have hE := (Real.exp_pos (-(2 * c) * τ)).le
  calc A * nrm2 (m : ℝ) (m : ℝ) (PP T τ (arr R))
      ≤ A * (M ^ 2 * Real.exp (-(2 * c) * τ) * nrm2 (m : ℝ) (m : ℝ) (arr R)) :=
        mul_le_mul_of_nonneg_left h5 hA
    _ ≤ A * (M ^ 2 * Real.exp (-(2 * c) * τ) * (K * cbNorm2 (m + m) R)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring


theorem px7_pair_jets (hOV : OV D ρ m T Ah) {R : Torus d → Torus d → ℝ} (hR : IsCk2 (m + m) R)
    (i : ℕ) (hi : i ≤ 2) (p : Euc d × Euc d) :
    ContinuousOn (fun τ => iteratedFDeriv ℝ i (lift2 (pairSemigroup D ρ τ R)) p) (Set.Ici 0) := by
  intro σ hσ
  have hσ' : 0 ≤ σ := hσ
  obtain ⟨K, hK, hdata⟩ := px7_arr_data hOV
  obtain ⟨h1, -, -⟩ := hdata R hR
  obtain ⟨A, hA, hev⟩ := px7_ev_C2 (d := d) (m := m) (by have := hOV.hm_gt; linarith)
  obtain ⟨M, c, hM, hc, hPP⟩ := px7_PP_bound hOV
  set u := arr R with hu
  have hmemτ : ∀ τ : ℝ, 0 ≤ τ → Mem2 (m : ℝ) (m : ℝ) (PP T τ u) := fun τ hτ => (hPP τ hτ u h1).1
  have hbound : ∀ᶠ τ in 𝓝[Set.Ici 0] σ,
      ‖iteratedFDeriv ℝ i (lift2 (pairSemigroup D ρ τ R)) p -
        iteratedFDeriv ℝ i (lift2 (pairSemigroup D ρ σ R)) p‖ ≤
      A * nrm2 (m : ℝ) (m : ℝ) (PP T τ u - PP T σ u) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ' : 0 ≤ τ := hτ
    have ma := hmemτ τ hτ'
    have mb := hmemτ σ hσ'
    have hsa := px7_summable_of_mem2 hOV.hd ma
    have hsb := px7_summable_of_mem2 hOV.hd mb
    obtain ⟨hc1, hn1⟩ := hev _ ma
    obtain ⟨hc2, hn2⟩ := hev _ mb
    have hsub := (ma.sub mb).1
    obtain ⟨hc3, hn3⟩ := hev _ hsub
    rw [px7_pair_ev hOV hR hτ', px7_pair_ev hOV hR hσ']
    have e : lift2 (ev (PP T τ u)) - lift2 (ev (PP T σ u)) = lift2 (ev (PP T τ u - PP T σ u)) := by
      funext q
      simp only [Pi.sub_apply, lift2]
      rw [px7_ev_sub hsa hsb]
    have hca : ContDiffAt ℝ (i : WithTop ℕ∞) (lift2 (ev (PP T τ u))) p :=
      (hc1.of_le (by exact_mod_cast hi)).contDiffAt
    have hcb : ContDiffAt ℝ (i : WithTop ℕ∞) (lift2 (ev (PP T σ u))) p :=
      (hc2.of_le (by exact_mod_cast hi)).contDiffAt
    rw [← iteratedFDeriv_sub_apply hca hcb, e]
    exact (MFPair.norm_iteratedFDeriv_le_cbNorm2 hc3 hi p).trans hn3
  have hlim : Tendsto (fun τ => A * nrm2 (m : ℝ) (m : ℝ) (PP T τ u - PP T σ u)) (𝓝[Set.Ici 0] σ) (𝓝 0) := by
    simpa using (px7_PP_cont hOV hσ' h1).const_mul A
  have : Tendsto (fun τ => iteratedFDeriv ℝ i (lift2 (pairSemigroup D ρ τ R)) p) (𝓝[Set.Ici 0] σ)
      (𝓝 (iteratedFDeriv ℝ i (lift2 (pairSemigroup D ρ σ R)) p)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero' (Filter.Eventually.of_forall fun τ => norm_nonneg _) hbound hlim
  exact this


theorem px7_inv_C2 (hOV : OV D ρ m T Ah) :
    ∃ Cinv : ℝ, 0 ≤ Cinv ∧ ∀ R : Torus d → Torus d → ℝ, IsCk2 (m + m) R →
      IsCk2 2 (pairInverse D ρ R) ∧ cbNorm2 2 (pairInverse D ρ R) ≤ Cinv * cbNorm2 (m + m) R ∧
      (∀ x y, IntegrableOn (fun t => pairSemigroup D ρ t R x y) (Set.Ici 0)) := by
  obtain ⟨C0, c0, hC0, hc0, hC2⟩ := px7_pair_C2 hOV
  refine ⟨3 * C0 / c0, by positivity, fun R hR => ?_⟩
  have hreg : ∀ t : ℝ, 0 ≤ t → IsCk2 2 (pairSemigroup D ρ t R) := fun t ht => (hC2 R hR t ht).1
  have hbd : ∀ t : ℝ, 0 ≤ t → cbNorm2 2 (pairSemigroup D ρ t R) ≤
      (C0 * cbNorm2 (m + m) R) * Real.exp (-c0 * t) := fun t ht => (hC2 R hR t ht).2
  have hcont : ∀ i : ℕ, i ≤ 2 → ∀ p : Euc d × Euc d,
      ContinuousOn (fun t => iteratedFDeriv ℝ i (lift2 (pairSemigroup D ρ t R)) p) (Set.Ici 0) :=
    fun i hi p => px7_pair_jets hOV hR i hi p
  obtain ⟨-, hpt, hCk, -⟩ := MFPair.integral_family_isCk2 2 (fun t => pairSemigroup D ρ t R)
    (C0 * cbNorm2 (m + m) R) c0 hc0 hreg hbd hcont
  obtain ⟨-, hb⟩ := MFPair.family_tail 2 (fun t => pairSemigroup D ρ t R) (C0 * cbNorm2 (m + m) R) c0 hc0
    hreg hbd hcont 0 le_rfl
  refine ⟨hCk, ?_, hpt⟩
  unfold cbNorm2
  have hn : 0 ≤ cbNorm2 (m + m) R := MFPair.cbNorm2_nonneg _ _
  calc ∑ i ∈ Finset.range (2 + 1), ⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ i (lift2 (pairInverse D ρ R)) p‖
      ≤ ∑ i ∈ Finset.range (2 + 1), (C0 * cbNorm2 (m + m) R) * Real.exp (-c0 * 0) / c0 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        refine ciSup_le fun p => ?_
        exact hb i hi' p
    _ = 3 * C0 / c0 * cbNorm2 (m + m) R := by
        simp only [Finset.sum_const, Finset.card_range, mul_zero, Real.exp_zero, mul_one, nsmul_eq_mul]
        push_cast; field_simp


theorem px7_coeff_bdd {ρ : Torus d → ℝ} (hρc : Continuous ρ) : ∃ B : ℝ, ∀ k, ‖coeffOf ρ k‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hρc.continuousOn
  refine ⟨B, fun k => ?_⟩
  rw [coeffOf_eq_fcoef]
  exact Torus.norm_fcoef_le_of_bound (g := ρ) (B := B) (fun x => by
    simpa [Real.norm_eq_abs] using hB x (Set.mem_univ x)) k

theorem px7_mC_acol (hOV : OV D ρ m T Ah) {w : Arr d} (hw : Mem2 (m : ℝ) (m : ℝ) w)
    (hcol : ∀ l, px7_mC ρ (col w l) = 0) (y : Torus d) : px7_mC ρ (acol w y) = 0 := by
  obtain ⟨B, hB⟩ := px7_coeff_bdd hOV.rho_cont
  have hs := px7_summable_of_mem2 hOV.hd hw
  have hsum : Summable (Function.uncurry fun k l => conj (coeffOf ρ k) * (w k l * Torus.mode l y)) := by
    refine Summable.of_norm_bounded (hs.mul_left |B|) fun p => ?_
    simp only [Function.uncurry, norm_mul, Torus.norm_mode, mul_one, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right ((hB p.1).trans (le_abs_self B)) (norm_nonneg _)
  unfold px7_mC acol
  have e1 : ∀ k, conj (coeffOf ρ k) * ∑' l, w k l * Torus.mode l y =
      ∑' l, conj (coeffOf ρ k) * (w k l * Torus.mode l y) := fun k => tsum_mul_left.symm
  simp_rw [e1]
  rw [← hsum.tsum_comm]
  have e2 : ∀ l, ∑' k, conj (coeffOf ρ k) * (w k l * Torus.mode l y) =
      Torus.mode l y * ∑' k, conj (coeffOf ρ k) * col w l k := by
    intro l
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by simp [col]; ring
  simp_rw [e2]
  have : ∀ l, ∑' k, conj (coeffOf ρ k) * col w l k = 0 := fun l => hcol l
  simp [this]

theorem px7_PP_cen (hOV : OV D ρ m T Ah) {τ : ℝ} (hτ : 0 ≤ τ) {u : Arr d}
    (hu : Mem2 (m : ℝ) (m : ℝ) u) :
    (∀ l, px7_mC ρ (col (PP T τ u) l) = 0) ∧ (∀ k, px7_mC ρ (fun l => PP T τ u k l) = 0) := by
  obtain ⟨M, c, hM, hc, hop⟩ := hOV.opok
  have hF := hop τ hτ
  constructor
  · intro l
    rw [px7_PP_comm hOV hτ hu]
    have hm : MemHs (m : ℝ) (col (rowOp (T τ) u) l) := px7_mem2_col (px7_rowOp_mem hF hu).1 l
    exact hOV.mean τ hτ _ hm
  · intro k
    have hm : MemHs (m : ℝ) (fun l' => colOp (T τ) u k l') :=
      px7_mem2_col (Mem2.transp (px7_colOp_mem hF hu).1).1 k
    exact hOV.mean τ hτ _ hm

theorem px7_ev_pair_x (hOV : OV D ρ m T Ah) {w : Arr d} (hw : Mem2 (m : ℝ) (m : ℝ) w) (hRS : RS w)
    (hcol : ∀ l, px7_mC ρ (col w l) = 0) (y : Torus d) :
    pair (withDensityReal ρ) (fun x => ev w x y) = 0 := by
  obtain ⟨hc, -, hco⟩ := px7_slice_x hOV.hm0 hOV.hd hw hRS y
  have hsum := px7_summable_of_mem2 hOV.hd hw
  have h1 := meanCoeff_coeffOf hOV.prob hOV.rho_cont hc
  have hρr : IsRealCoeff (coeffOf ρ) :=
    isRealCoeff_coeffOf ρ (MFAdjoint.integrable_of_cont hOV.rho_cont)
  have hreal : IsRealCoeff (coeffOf (fun x => ev w x y)) := by
    rw [hco]; exact px7_acol_real hRS hsum y
  have h2 := px7_meanCoeff_eq hρr hreal
  rw [h1, hco, px7_mC_acol hOV hw hcol y] at h2
  exact_mod_cast h2

theorem px7_ev_pair_y (hOV : OV D ρ m T Ah) {w : Arr d} (hw : Mem2 (m : ℝ) (m : ℝ) w) (hRS : RS w)
    (hrow : ∀ k, px7_mC ρ (fun l => w k l) = 0) (x : Torus d) :
    pair (withDensityReal ρ) (fun y => ev w x y) = 0 := by
  have e : (fun y => ev w x y) = fun y => ev (tr w) y x := funext fun y => (px7_ev_tr w y x).symm
  rw [e]
  exact px7_ev_pair_x hOV (Mem2.transp hw).1 (fun k l => hRS l k) hrow x

theorem px7_pair_cen (hOV : OV D ρ m T Ah) {R : Torus d → Torus d → ℝ} (hR : IsCk2 (m + m) R)
    {τ : ℝ} (hτ : 0 ≤ τ) : DoublyCentered (withDensityReal ρ) (pairSemigroup D ρ τ R) := by
  obtain ⟨K, hK, hdata⟩ := px7_arr_data hOV
  obtain ⟨h1, h2, -⟩ := hdata R hR
  rw [px7_pair_ev hOV hR hτ]
  obtain ⟨M, -, hmem⟩ := px7_PP_mem hOV hτ
  have hm := (hmem _ h1).1
  have hrs := px7_PP_RS hOV hτ h1 h2
  obtain ⟨hc, hr⟩ := px7_PP_cen hOV hτ h1
  exact ⟨fun y => px7_ev_pair_x hOV hm hrs hc y, fun x => px7_ev_pair_y hOV hm hrs hr x⟩

theorem px7_inv_cen (hOV : OV D ρ m T Ah) {R : Torus d → Torus d → ℝ} (hR : IsCk2 (m + m) R) :
    DoublyCentered (withDensityReal ρ) (pairInverse D ρ R) := by
  obtain ⟨C0, c0, hC0, hc0, hC2⟩ := px7_pair_C2 hOV
  exact MFPair.integral_family_doublyCentered 2 (fun t => pairSemigroup D ρ t R)
    (C0 * cbNorm2 (m + m) R) c0 hc0 (fun t ht => (hC2 R hR t ht).1) (fun t ht => (hC2 R hR t ht).2)
    (fun p => px7_pair_jets hOV hR 0 (by norm_num) p) hOV.prob hOV.rho_cont
    (fun t ht => px7_pair_cen hOV hR ht)

theorem px7_ev_smul (a : ℝ) (u : Arr d) (x y : Torus d) : ev ((a : ℂ) • u) x y = a * ev u x y := by
  unfold ev
  rw [← Complex.re_ofReal_mul, ← tsum_mul_left]
  congr 1
  exact tsum_congr fun p => by simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem px7_PP_lin (hOV : OV D ρ m T Ah) {τ : ℝ} (hτ : 0 ≤ τ) {u v : Arr d}
    (hu : Mem2 (m : ℝ) (m : ℝ) u) (hv : Mem2 (m : ℝ) (m : ℝ) v) (a b : ℂ) :
    PP T τ (a • u + b • v) = a • PP T τ u + b • PP T τ v := by
  obtain ⟨M, c, hM, hc, hop⟩ := hOV.opok
  have hF := hop τ hτ
  have hau := (hu.smul a).1
  have hbv := (hv.smul b).1
  have e1 : colOp (T τ) (a • u + b • v) = a • colOp (T τ) u + b • colOp (T τ) v := by
    rw [px7_colOp_add hF hau hbv, px7_colOp_smul hF hu, px7_colOp_smul hF hv]
  have hcu := (px7_colOp_mem hF hu).1
  have hcv := (px7_colOp_mem hF hv).1
  unfold PP
  rw [e1, px7_rowOp_add hF (hcu.smul a).1 (hcv.smul b).1, px7_rowOp_smul hF hcu, px7_rowOp_smul hF hcv]

theorem px7_pair_lin (hOV : OV D ρ m T Ah) {R R' : Torus d → Torus d → ℝ} (hR : IsCk2 (m + m) R)
    (hR' : IsCk2 (m + m) R') (a b : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    pairSemigroup D ρ τ (fun x y => a * R x y + b * R' x y) =
      fun x y => a * pairSemigroup D ρ τ R x y + b * pairSemigroup D ρ τ R' x y := by
  obtain ⟨K, hK, hdata⟩ := px7_arr_data hOV
  obtain ⟨h1, h2, -⟩ := hdata R hR
  obtain ⟨h1', h2', -⟩ := hdata R' hR'
  have hRR : IsCk2 (m + m) (fun x y => a * R x y + b * R' x y) := by
    have e : lift2 (fun x y => a * R x y + b * R' x y) = fun p => a * lift2 R p + b * lift2 R' p := rfl
    unfold IsCk2; rw [e]
    exact (contDiff_const.mul hR).add (contDiff_const.mul hR')
  have harr : arr (fun x y => a * R x y + b * R' x y) = (a : ℂ) • arr R + (b : ℂ) • arr R' := by
    funext k l
    exact px7_arr_lin hR.continuous hR'.continuous a b k l
  rw [px7_pair_ev hOV hRR hτ, px7_pair_ev hOV hR hτ, px7_pair_ev hOV hR' hτ, harr,
    px7_PP_lin hOV hτ h1 h1']
  obtain ⟨M, -, hmem⟩ := px7_PP_mem hOV hτ
  have hm1 := (hmem _ h1).1
  have hm2 := (hmem _ h1').1
  funext x y
  rw [px7_ev_add (px7_summable_of_mem2 hOV.hd (hm1.smul _).1) (px7_summable_of_mem2 hOV.hd (hm2.smul _).1),
    px7_ev_smul, px7_ev_smul]

theorem px7_inv_lin (hOV : OV D ρ m T Ah) {R R' : Torus d → Torus d → ℝ} (hR : IsCk2 (m + m) R)
    (hR' : IsCk2 (m + m) R') (a b : ℝ) :
    pairInverse D ρ (fun x y => a * R x y + b * R' x y) =
      fun x y => a * pairInverse D ρ R x y + b * pairInverse D ρ R' x y := by
  obtain ⟨Cinv, -, hinv⟩ := px7_inv_C2 hOV
  have i1 := (hinv R hR).2.2
  have i2 := (hinv R' hR').2.2
  funext x y
  unfold pairInverse
  calc ∫ t in Set.Ici (0 : ℝ), pairSemigroup D ρ t (fun x y => a * R x y + b * R' x y) x y
      = ∫ t in Set.Ici (0 : ℝ), (a * pairSemigroup D ρ t R x y + b * pairSemigroup D ρ t R' x y) := by
        refine setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
        have := congrFun (congrFun (px7_pair_lin hOV hR hR' a b (Set.mem_Ici.1 ht)) x) y
        simpa using this
    _ = _ := by
        rw [integral_add ((i1 x y).const_mul a) ((i2 x y).const_mul b), integral_const_mul,
          integral_const_mul]

theorem px7_pair_symm (hOV : OV D ρ m T Ah) {R : Torus d → Torus d → ℝ} (hR : IsCk2 (m + m) R)
    (hs : ∀ x y, R x y = R y x) {τ : ℝ} (hτ : 0 ≤ τ) (x y : Torus d) :
    pairSemigroup D ρ τ R x y = pairSemigroup D ρ τ R y x := by
  obtain ⟨K, hK, hdata⟩ := px7_arr_data hOV
  obtain ⟨h1, h2, -⟩ := hdata R hR
  obtain ⟨M, c, hM, hc, hop⟩ := hOV.opok
  have hF := hop τ hτ
  have hut : tr (arr R) = arr R := by
    funext k l
    have := px7_arr_trK hR.continuous k l
    have e : trK R = R := funext fun x => funext fun y => (hs y x)
    rw [e] at this
    exact this.symm
  have hP : tr (PP T τ (arr R)) = PP T τ (arr R) := by
    have a1 : tr (rowOp (T τ) (colOp (T τ) (arr R))) = colOp (T τ) (tr (colOp (T τ) (arr R))) := by
      rw [px7_rowOp_eq]; rfl
    have a2 : tr (colOp (T τ) (arr R)) = rowOp (T τ) (tr (arr R)) := by
      rw [px7_colOp_eq]; rfl
    unfold PP
    rw [a1, a2, hut]
    exact px7_arr_comm hF hF h1
  rw [px7_pair_ev hOV hR hτ]
  rw [← px7_ev_tr (PP T τ (arr R)) x y, hP]

theorem px7_inv_symm (hOV : OV D ρ m T Ah) {R : Torus d → Torus d → ℝ} (hR : IsCk2 (m + m) R)
    (hs : ∀ x y, R x y = R y x) (x y : Torus d) :
    pairInverse D ρ R x y = pairInverse D ρ R y x := by
  unfold pairInverse
  exact setIntegral_congr_fun measurableSet_Ici fun t ht => px7_pair_symm hOV hR hs (Set.mem_Ici.1 ht) x y

end PairKernel

end HRS.PDE.PX7

end
