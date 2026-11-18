import HRS.MS.UlMildAux1

/-!
# UL-4, part 2 (UlMildAux2): the perturbation `ulPert`, its regularity and the smoothing estimate

(docstring: see `UlMildAux3.lean`.)  Helper lemmas carry the prefix `ul4_`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.Ul
open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW
open HRS.MS.Lc HRS.MD.EQLawPath

variable {d : ℕ}

/-- The perturbation `B u = c·∇u - N u` of the base operator `L_0 = νΔ - Qx·∇`:
`generatorW (fixedViscosityCoeff s M Q ν c ρ) 0 u = L_0 u + ulPert s M ρ c u` (`generatorW_fixed`). -/
def ulPert (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (c : Euc d → Euc d)
    (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  inner ℝ (c x) (gradient u x) - ulNL s M ρ u x

/-- the smoothing exponent `γ = max(1, 2-(d-s))/2 ∈ [1/2, 1)` -/
def ul4gam (d : ℕ) (s : ℝ) : ℝ := max 1 (2 - ((d : ℝ) - s)) / 2

theorem ul4_gam_bounds {s : ℝ} (hsd : s < d) : 1 / 2 ≤ ul4gam d s ∧ ul4gam d s < 1 := by
  unfold ul4gam
  constructor
  · have := le_max_left (1 : ℝ) (2 - ((d : ℝ) - s)); linarith
  · have : max 1 (2 - ((d : ℝ) - s)) < 2 := max_lt (by norm_num) (by linarith)
    linarith

/-- `1 + t^{-1/2} ≤ (T^γ + T^{γ-1/2}) t^{-γ}` for `0 < t ≤ T`, `γ ≥ 1/2` -/
theorem ul4_rpow_aux {γ : ℝ} (hγ : 1 / 2 ≤ γ) {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    1 + 1 / Real.sqrt t ≤ (T ^ γ + T ^ (γ - 1 / 2)) * t ^ (-γ) := by
  have hT : 0 < T := ht.trans_le htT
  have h1 : 1 = t ^ γ * t ^ (-γ) := by
    rw [← Real.rpow_add ht]; simp
  have h2 : 1 / Real.sqrt t = t ^ (γ - 1 / 2) * t ^ (-γ) := by
    rw [← Real.rpow_add ht, Real.sqrt_eq_rpow]
    have : γ - 1 / 2 + -γ = -(1 / 2) := by ring
    rw [this, Real.rpow_neg ht.le, one_div]
  have h3 : t ^ γ ≤ T ^ γ := Real.rpow_le_rpow ht.le htT (by linarith)
  have h4 : t ^ (γ - 1 / 2) ≤ T ^ (γ - 1 / 2) := Real.rpow_le_rpow ht.le htT (by linarith)
  have h5 : 0 ≤ t ^ (-γ) := (Real.rpow_pos_of_pos ht _).le
  calc 1 + 1 / Real.sqrt t = (t ^ γ + t ^ (γ - 1 / 2)) * t ^ (-γ) := by
        rw [add_mul, ← h1, ← h2]
    _ ≤ _ := by gcongr

/-- `⟨c, ∇u⟩ = ∑ c_i ∂_i u` -/
theorem ul4_inner_grad (c : Euc d → Euc d) (u : Euc d → ℝ) (x : Euc d) :
    inner ℝ (c x) (gradient u x) = ∑ i, c x i * fderiv ℝ u x (EuclideanSpace.single i 1) := by
  have h1 : ∀ i, gradient u x i = fderiv ℝ u x (EuclideanSpace.single i 1) := by
    intro i
    have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single i (1 : ℝ))
      (y := fderiv ℝ u x)
    rw [EuclideanSpace.inner_single_right] at this
    simpa [gradient] using this
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← h1 i]
  simp [mul_comm]

/-! ### Properties of `C_c^∞ + const` -/

theorem ul4_ccc_props {g : Euc d → ℝ} (hg : IsCcInftyPlusConst g) :
    ContDiff ℝ ∞ g ∧ (∀ m : ℕ, HRS.MemCb m g) ∧ HasCompactSupport (fderiv ℝ g) := by
  obtain ⟨h, c0, hh, hhc, rfl⟩ := hg
  have hgs : ContDiff ℝ ∞ (fun x => h x + c0) := hh.add contDiff_const
  refine ⟨hgs, fun m => ⟨hgs.of_le (by exact_mod_cast le_top), fun j hj => ?_⟩, ?_⟩
  · have hcb := ul3_memCb_of_cs m hh hhc
    by_cases hj0 : j = 0
    · subst hj0
      obtain ⟨B, hB⟩ := hcb.2 0 (Nat.zero_le _)
      refine ⟨B + |c0|, ?_⟩
      rintro _ ⟨x, rfl⟩
      have := hB ⟨x, rfl⟩
      simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this ⊢
      exact (abs_add_le _ _).trans (by linarith)
    · obtain ⟨B, hB⟩ := hcb.2 j hj
      refine ⟨B, ?_⟩
      rintro _ ⟨x, rfl⟩
      have := ul0_iteratedFDeriv_sub_const h hh (-c0) j hj0 x
      simp only [sub_neg_eq_add] at this
      show ‖iteratedFDeriv ℝ j (fun x => h x + c0) x‖ ≤ B
      rw [this]; exact hB ⟨x, rfl⟩
  · have e : fderiv ℝ (fun x => h x + c0) = fderiv ℝ h := by
      funext x
      exact fderiv_add_const c0
    rw [e]; exact hhc.fderiv (𝕜 := ℝ)

theorem ul4_hcs_sum {ι : Type*} (S : Finset ι) (f : ι → Euc d → ℝ)
    (h : ∀ i ∈ S, HasCompactSupport (f i)) : HasCompactSupport (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (HasCompactSupport.zero (α := Euc d) (β := ℝ) : HasCompactSupport (0 : Euc d → ℝ))
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- finite sums in `ulocNormE` -/
theorem ul4_uloc_sum (m : ℕ) (χ : Euc d → ℝ) {ι : Type*} (S : Finset ι) (f : ι → Euc d → ℝ) :
    ulocNormE m χ (fun x => ∑ i ∈ S, f i x) ≤ ∑ i ∈ S, ulocNormE m χ (f i) := by
  refine iSup_le fun z => ?_
  have e : (fun x => χ (x - z) * ∑ i ∈ S, f i x) = fun x => ∑ i ∈ S, χ (x - z) * f i x := by
    funext x; rw [Finset.mul_sum]
  rw [e]
  refine (HRS.MS.UlocCut.uc_sum_le (m : ℝ) S (fun i x => χ (x - z) * f i x)).trans ?_
  exact Finset.sum_le_sum fun i _ => le_iSup (fun z : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - z) * f i x) z

/-- differences in `ulocNormE` (with the scalar constant) -/
theorem ul4_uloc_sub (m : ℕ) (χ : Euc d → ℝ) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ a b : Euc d → ℝ,
      ulocNormE m χ (fun x => a x - b x) ≤ ulocNormE m χ a + ENNReal.ofReal Cs * ulocNormE m χ b := by
  obtain ⟨Cs, hCs0, hCs⟩ := ul3_scalar m χ
  refine ⟨Cs, hCs0, fun a b => ?_⟩
  have e : (fun x => a x - b x) = fun x => a x + (-1 : ℝ) * b x := by funext x; ring
  rw [e]
  refine (ul0_ulocNormE_add m χ _ _).trans (add_le_add le_rfl ((hCs (-1) b).trans ?_))
  simp

/-! ### The splitting of the nonlocal term for `C_c^∞ + const` data -/

theorem ul4_nl_split {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Euc d → ℝ, IsCcInftyPlusConst g → ∃ n f : Euc d → ℝ,
      (∀ x, ulNL s M ρ g x = n x + f x) ∧ Continuous n ∧ (∃ B : ℝ, ∀ x, |n x| ≤ B) ∧
      Integrable n volume ∧
      sobolevNormE ((k : ℝ) - 2 + ((d : ℝ) - s)) n ≤ ENNReal.ofReal C * ulocNormE k χ g ∧
      MemCb (k - 1) f ∧ cbNorm (k - 1) f ≤ C * (ulocNormE k χ g).toReal := by
  obtain ⟨ψ, rfl⟩ := hρ
  have hd : 0 < d := by
    have : (0 : ℝ) < d := lt_of_le_of_lt hs0 hsd
    exact_mod_cast this
  have hk2 : 2 ≤ k := by omega
  obtain ⟨Cg, hCg0, hG⟩ := ul1_sobolev_G hχ ψ M k hk2 hd
  obtain ⟨Cf, hCf0, hF⟩ := ul1_far hχ hs0 ψ M k hk2 hd
  obtain ⟨CL, -, hL⟩ := ul1_L1_F hχ ψ M k (by omega) hd
  obtain ⟨Ct, hCt, hTC⟩ := HRS.MS.Tc3.tc3_riesz_loc_sobolevNormE_gain (d := d) (θ := ul1Th d)
    ul1_th_contDiff ul1_th_compact hs0 hsd
  obtain ⟨Cl, hCl, hle⟩ := ulocNormE_le_cb k χ hχ
  obtain ⟨Cc, hCc0, hCc⟩ := ul_nl_cont hs0 hsd M ψ ⟨ψ, rfl⟩ k hk
  refine ⟨max (Ct * Cg) Cf, le_max_of_le_right hCf0, fun g hg => ?_⟩
  obtain ⟨hgs, hgcb, hgdc⟩ := ul4_ccc_props hg
  have hu : ContDiff ℝ k g := hgs.of_le (by exact_mod_cast le_top)
  have hU : ulocNormE k χ g < ⊤ :=
    lt_of_le_of_lt (hle g (hgcb k)) ENNReal.ofReal_lt_top
  obtain ⟨hGmem, hGbd⟩ := hG g hu hU
  obtain ⟨f, hfx, hMemCb, hcb⟩ := hF g hu hU
  set n : Euc d → ℝ := HRS.Whole.convFun (ul1H d s) (ul1G ψ M g) with hn
  have hmr : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
    rw [Nat.cast_sub hk2]; norm_num
  have hnbd : sobolevNormE ((k : ℝ) - 2 + ((d : ℝ) - s)) n ≤
      ENNReal.ofReal (max (Ct * Cg) Cf) * ulocNormE k χ g := by
    have h1 := hTC (((k - 2 : ℕ) : ℝ)) (ul1G ψ M g)
    rw [hmr] at h1 hGbd
    refine h1.trans ?_
    calc ENNReal.ofReal Ct * sobolevNormE ((k : ℝ) - 2) (ul1G ψ M g)
        ≤ ENNReal.ofReal Ct * (ENNReal.ofReal Cg * ulocNormE k χ g) := by gcongr
      _ = ENNReal.ofReal (Ct * Cg) * ulocNormE k χ g := by
          rw [← mul_assoc, ENNReal.ofReal_mul hCt.le]
      _ ≤ _ := by gcongr; exact le_max_left _ _
  have hid : ∀ x, ulNL s M ψ g x = n x + f x := fun x => by
    rw [ul1_ulNL_eq hs0 hsd ψ M hk2 hu (fun j => (hL g hu hU j).1) x, hfx x]
  obtain ⟨hnlcb, -⟩ := hCc g (hgcb k)
  have hnl_cont : Continuous (ulNL s M ψ g) :=
    hnlcb.1.continuous
  have hf_cont : Continuous f := hMemCb.1.continuous
  have hn_eq : n = fun x => ulNL s M ψ g x - f x := by funext x; rw [hid x]; ring
  have hn_cont : Continuous n := by rw [hn_eq]; exact hnl_cont.sub hf_cont
  obtain ⟨B1, hB1⟩ := ul3C_bdd_of_cb (m := k - 2) hnlcb
  obtain ⟨B2, hB2⟩ := ul3C_bdd_of_cb hMemCb
  -- integrability of `n` as a convolution of two integrable functions
  have hGc : Continuous (ul1G ψ M g) := (ul1_G_contDiff ψ M hk2 hu).continuous
  have hGcs : HasCompactSupport (ul1G ψ M g) := by
    unfold ul1G
    refine ul4_hcs_sum Finset.univ _ (fun j _ => ?_)
    have h1 : HasCompactSupport (fun y => ψ y * fderiv ℝ g y (ul1w M j)) :=
      ((hgdc.comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (ul1w M j)) (by simp))).mul_left
    exact (h1.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ =>
      L (EuclideanSpace.single j (1 : ℝ))) (by simp)
  have hGi : Integrable (ul1G ψ M g) volume := hGc.integrable_of_hasCompactSupport hGcs
  have hHi : Integrable (ul1H d s) volume := ul1_H_integrable hs0 hsd
  have hnint : Integrable n volume := by
    have := hGi.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hHi
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hn, HRS.Whole.convFun, convolution_def, ContinuousLinearMap.mul_apply']
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  refine ⟨n, f, hid, hn_cont, ⟨B1 + B2, fun x => ?_⟩, hnint, hnbd, hMemCb, ?_⟩
  · rw [hn_eq]
    exact (abs_sub _ _).trans (add_le_add (hB1 x) (hB2 x))
  · exact hcb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ENNReal.toReal_nonneg)

/-! ### Linearity of `ouSg` and bounds for `C_b` coefficients -/

theorem ul4_ouSg_add (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) {f g : Euc d → ℝ} (hf : Measurable f)
    (hg : Measurable g) {Bf Bg : ℝ} (hBf : ∀ x, |f x| ≤ Bf) (hBg : ∀ x, |g x| ≤ Bg) :
    ouSg Q ν τ (fun x => f x + g x) = fun x => ouSg Q ν τ f x + ouSg Q ν τ g x := by
  funext x
  have hi : ∀ (u : Euc d → ℝ), Measurable u → ∀ B : ℝ, (∀ x, |u x| ≤ B) →
      Integrable (fun y => u (ouExp Q τ x + y)) (ouLaw Q ν τ) := fun u hu B hB =>
    Integrable.of_bound (hu.comp (measurable_const.add measurable_id)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB _)
  exact integral_add (hi f hf Bf hBf) (hi g hg Bg hBg)

theorem ul4_memCb_coord {c : Euc d → Euc d} (hc : IsSmoothBounded c) (i : Fin d) (m : ℕ) :
    HRS.MemCb m (fun x => c x i) := by
  have hci : ContDiff ℝ ∞ (fun x => c x i) := contDiff_euclidean.1 hc.1 i
  refine ⟨hci.of_le (by exact_mod_cast le_top), fun j hj => ?_⟩
  obtain ⟨B, hB⟩ := hc.2 j
  set L : Euc d →L[ℝ] ℝ := EuclideanSpace.proj i with hL
  refine ⟨‖L‖ * B, ?_⟩
  rintro _ ⟨x, rfl⟩
  have h1 := L.norm_iteratedFDeriv_comp_left (f := c) (x := x) (N := ∞) (n := j) hc.1.contDiffAt
    (by exact_mod_cast le_top)
  exact h1.trans (mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _))

theorem ul4_mul3 {a b : ℝ} (ha : 0 ≤ a) (U V : ℝ≥0∞) (hUV : V ≤ U) :
    ENNReal.ofReal a * V ≤ ENNReal.ofReal a * U := by gcongr

theorem ul4_comb {a b c C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hC : 0 ≤ C) (U : ℝ≥0∞) :
    ENNReal.ofReal a * U + ENNReal.ofReal C * (ENNReal.ofReal b * U + ENNReal.ofReal c * U) =
      ENNReal.ofReal (a + C * (b + c)) * U := by
  rw [← add_mul (ENNReal.ofReal b), ← ENNReal.ofReal_add hb hc, ← mul_assoc,
    ← ENNReal.ofReal_mul hC, ← add_mul, ← ENNReal.ofReal_add ha (by positivity)]

theorem ul4_ofReal_mul_mul' {a b : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) := (ENNReal.ofReal_mul ha).symm

theorem ul4_ofReal_mul_mul {a b : ℝ} (ha : 0 ≤ a) (U : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * U) = ENNReal.ofReal (a * b) * U := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul ha]

/-! ### The smoothing estimate for `C_c^∞ + const` data -/

/-- **Smoothing estimate (smooth data).**  `‖P_t (ulPert g)‖_{H^k_uloc} ≤ K t^{-γ} ‖g‖_{H^k_uloc}` for
`g ∈ C_c^∞ + const`, `0 < t ≤ T`, `γ = max(1,2-(d-s))/2 ∈ [1/2,1)`. -/
theorem ul4_pert_smooth {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    {c : Euc d → Euc d} (hc : IsSmoothBounded c) (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν)
    (T : ℝ) (k : ℕ) (hk : 3 ≤ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Ioc (0 : ℝ) T, ∀ g : Euc d → ℝ, IsCcInftyPlusConst g →
      ulocNormE k χ (ouSg Q ν t (ulPert s M ρ c g)) ≤
        ENNReal.ofReal (K * t ^ (-ul4gam d s)) * ulocNormE k χ g := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hn2 : 2 ≤ n := by omega
  obtain ⟨hγ0, hγ1⟩ := ul4_gam_bounds hsd
  set γ := ul4gam d s with hγdef
  set α : ℝ := max 1 (2 - ((d : ℝ) - s)) with hα
  have hds : 0 < (d : ℝ) - s := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hα2 : α ≤ 2 := max_le (by norm_num) (by linarith)
  have hαge : 2 - ((d : ℝ) - s) ≤ α := le_max_right _ _
  have hαγ : -α / 2 = -γ := by rw [hγdef, ul4gam]; ring
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  obtain ⟨Csp, hCsp0, hsplit⟩ := ul4_nl_split hχ hs0 hsd M ρ hρ (n + 1) hk
  obtain ⟨Cg1, hCg1, hgain1⟩ := ouSg_ulocNormE_gain n χ hχ Q hν T
  obtain ⟨Cg2, hCg2, hgain2⟩ := ouSg_sobolevNormE_gain Q hν T (t := ((n + 1 : ℕ) : ℝ) - α) (α := α)
    (by push_cast; linarith) hα0 hα2
  obtain ⟨Cloc, hCloc, hloc⟩ := ul4_uloc_le_sob (n + 1) χ hχ
  obtain ⟨Cm, hCm, hmul⟩ := ulocNormE_mul_cb n χ
  obtain ⟨Cd, hCd, hder⟩ := ul4_deriv_uloc n χ hχ
  obtain ⟨Cl, hCl, hlecb⟩ := ulocNormE_le_cb n χ hχ
  obtain ⟨Cl1, hCl1, hlecb1⟩ := ulocNormE_le_cb (n + 1) χ hχ
  obtain ⟨Cs, hCs, hsub⟩ := ul4_uloc_sub (n + 1) χ
  set T' : ℝ := max T 0 with hT'
  set Kr : ℝ := T' ^ γ + T' ^ (γ - 1 / 2) with hKr
  have hKr0 : 0 ≤ Kr := by positivity
  set cbs : ℝ := ∑ i, HRS.cbNorm n (fun x => c x i) with hcbs
  have hcbs0 : 0 ≤ cbs := Finset.sum_nonneg fun i _ => ul0_cbNorm_nonneg _ _
  set Ka : ℝ := Cg1 * Kr * (Cm * Cd * cbs) with hKa
  set Kb : ℝ := Cg1 * Kr * (Cl * Csp) with hKb
  set Kc : ℝ := Cloc * Cg2 * Csp with hKc
  have hKa0 : 0 ≤ Ka := by positivity
  have hKb0 : 0 ≤ Kb := by positivity
  have hKc0 : 0 ≤ Kc := by positivity
  refine ⟨Ka + Cs * (Kb + Kc) + 1, by positivity, fun t ht g hg => ?_⟩
  obtain ⟨hgs, hgcb, hgdc⟩ := ul4_ccc_props hg
  have ht0 : 0 < t := ht.1
  have htT' : t ≤ T' := ht.2.trans (le_max_left _ _)
  have hrp := ul4_rpow_aux hγ0 ht0 htT'
  have hrp0 : 0 ≤ t ^ (-γ) := (Real.rpow_pos_of_pos ht0 _).le
  set U : ℝ≥0∞ := ulocNormE (n + 1) χ g with hU
  have hUfin : U < ⊤ := lt_of_le_of_lt (hlecb1 g (hgcb (n + 1))) ENNReal.ofReal_lt_top
  obtain ⟨nl, f, hid, hnc, ⟨Bn, hBn⟩, hni, hnS, hfcb, hfn⟩ := hsplit g hg
  simp only [Nat.add_sub_cancel] at hfcb hfn
  simp only [Nat.cast_add, Nat.cast_one] at hnS
  -- the transport part
  set φ1 : Euc d → ℝ := fun x => inner ℝ (c x) (gradient g x) with hφ1
  have hφ1e : φ1 = fun x => ∑ i, c x i * fderiv ℝ g x (EuclideanSpace.single i 1) := by
    funext x; exact ul4_inner_grad c g x
  have hdg : ContDiff ℝ ∞ (fderiv ℝ g) := hgs.fderiv_right (by simp)
  have hφ1s : ContDiff ℝ ∞ φ1 := by
    rw [hφ1e]
    exact ContDiff.sum fun i _ => (contDiff_euclidean.1 hc.1 i).mul (hdg.clm_apply contDiff_const)
  have hφ1c : HasCompactSupport φ1 := by
    rw [hφ1e]
    refine ul4_hcs_sum Finset.univ _ fun i _ => ?_
    exact (hgdc.comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single i (1 : ℝ)))
      (by simp)).mul_left
  obtain ⟨Mφ0, -, hMφ0⟩ := ul3C_bdd hφ1s hφ1c 0
  obtain ⟨Mφ1, -, hMφ1⟩ := ul3C_bdd hφ1s hφ1c 1
  have hφB : ∀ y, |φ1 y| ≤ Mφ0 := fun y => by
    have := hMφ0 y; rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hφM : ∀ y, ‖fderiv ℝ φ1 y‖ ≤ Mφ1 := fun y => by
    have := hMφ1 y; rwa [norm_iteratedFDeriv_one] at this
  have hφn : ulocNormE n χ φ1 ≤ ENNReal.ofReal (Cm * Cd * cbs) * U := by
    rw [hφ1e]
    refine (ul4_uloc_sum n χ Finset.univ _).trans ?_
    have hterm : ∀ i : Fin d, ulocNormE n χ (fun x => c x i * fderiv ℝ g x (EuclideanSpace.single i 1)) ≤
        ENNReal.ofReal (Cm * HRS.cbNorm n (fun x => c x i)) * (ENNReal.ofReal Cd * U) := fun i =>
      (hmul _ (ul4_memCb_coord hc i n) _).trans
        (mul_le_mul' le_rfl (hder g (hgs.of_le (by exact_mod_cast le_top)) i))
    refine (Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
    simp_rw [ul4_ofReal_mul_mul (mul_nonneg hCm.le (ul0_cbNorm_nonneg _ _))]
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
      (fun i _ => mul_nonneg (mul_nonneg hCm.le (ul0_cbNorm_nonneg _ _)) hCd.le)]
    congr 2
    rw [hcbs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hP1 : ulocNormE (n + 1) χ (ouSg Q ν t φ1) ≤ ENNReal.ofReal (Ka * t ^ (-γ)) * U := by
    refine (hgain1 t ht φ1 (hφ1s.of_le (by exact_mod_cast le_top)) Mφ0 Mφ1 hφB hφM).trans ?_
    calc ENNReal.ofReal (Cg1 * (1 + 1 / Real.sqrt t)) * ulocNormE n χ φ1
        ≤ ENNReal.ofReal (Cg1 * (Kr * t ^ (-γ))) * (ENNReal.ofReal (Cm * Cd * cbs) * U) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (by gcongr)) hφn
      _ = ENNReal.ofReal (Ka * t ^ (-γ)) * U := by
          rw [ul4_ofReal_mul_mul (by positivity)]
          congr 2; rw [hKa]; ring
  -- the smooth far part
  have hf1 : ContDiff ℝ 1 f := hfcb.1.of_le (by exact_mod_cast (by omega : 1 ≤ n))
  have hfB : ∀ y, |f y| ≤ HRS.cbNorm n f := fun y => by
    have := ul3_cb_apply hfcb (Nat.zero_le n) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hfM : ∀ y, ‖fderiv ℝ f y‖ ≤ HRS.cbNorm n f := fun y => by
    have := ul3_cb_apply hfcb (by omega : 1 ≤ n) y
    rwa [norm_iteratedFDeriv_one] at this
  have hPf : ulocNormE (n + 1) χ (ouSg Q ν t f) ≤ ENNReal.ofReal (Kb * t ^ (-γ)) * U := by
    refine (hgain1 t ht f hf1 _ _ hfB hfM).trans ?_
    have h1 : ulocNormE n χ f ≤ ENNReal.ofReal (Cl * Csp) * U := by
      refine (hlecb f hfcb).trans ?_
      have : ENNReal.ofReal (Cl * HRS.cbNorm n f) ≤ ENNReal.ofReal (Cl * (Csp * U.toReal)) :=
        ENNReal.ofReal_le_ofReal (by gcongr)
      refine this.trans (le_of_eq ?_)
      rw [← mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hUfin.ne]
    calc ENNReal.ofReal (Cg1 * (1 + 1 / Real.sqrt t)) * ulocNormE n χ f
        ≤ ENNReal.ofReal (Cg1 * (Kr * t ^ (-γ))) * (ENNReal.ofReal (Cl * Csp) * U) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (by gcongr)) h1
      _ = ENNReal.ofReal (Kb * t ^ (-γ)) * U := by
          rw [ul4_ofReal_mul_mul (by positivity)]
          congr 2; rw [hKb]; ring
  -- the near part
  have hPn : ulocNormE (n + 1) χ (ouSg Q ν t nl) ≤ ENNReal.ofReal (Kc * t ^ (-γ)) * U := by
    have h1 := hgain2 t ht nl hnc.measurable ⟨Bn, hBn⟩ hni
    rw [sub_add_cancel, hαγ] at h1
    have h2 : sobolevNormE (((n + 1 : ℕ) : ℝ) - α) nl ≤ ENNReal.ofReal Csp * U := by
      refine (ul0_sobE_mono ?_ nl).trans hnS
      push_cast; linarith
    refine (hloc _).trans ?_
    calc ENNReal.ofReal Cloc * sobolevNormE ((n + 1 : ℕ) : ℝ) (ouSg Q ν t nl)
        ≤ ENNReal.ofReal Cloc * (ENNReal.ofReal (Cg2 * t ^ (-γ)) * (ENNReal.ofReal Csp * U)) :=
          mul_le_mul' le_rfl (h1.trans (mul_le_mul' le_rfl h2))
      _ = ENNReal.ofReal (Kc * t ^ (-γ)) * U := by
          rw [ul4_ofReal_mul_mul (by positivity), ul4_ofReal_mul_mul (by positivity)]
          congr 2; rw [hKc]; ring
  -- assembly
  have hpe : ulPert s M ρ c g = fun x => φ1 x - (nl x + f x) := by
    funext x; simp only [ulPert, hφ1]; rw [hid x]
  have hnfB : ∀ x, |nl x + f x| ≤ Bn + HRS.cbNorm n f := fun x =>
    (abs_add_le _ _).trans (add_le_add (hBn x) (hfB x))
  have hflin : ouSg Q ν t (fun x => nl x + f x) = fun x => ouSg Q ν t nl x + ouSg Q ν t f x :=
    ul4_ouSg_add Q ν t hnc.measurable hfcb.1.continuous.measurable hBn hfB
  have hlin : ouSg Q ν t (ulPert s M ρ c g) = fun x => ouSg Q ν t φ1 x - (ouSg Q ν t nl x + ouSg Q ν t f x) := by
    have hmeas : Measurable (fun x => nl x + f x) := hnc.measurable.add hfcb.1.continuous.measurable
    rw [hpe, ul3C_sub_lin Q ν t hφ1s.continuous.measurable hmeas hφB hnfB, hflin]
  rw [hlin]
  refine (hsub _ _).trans ?_
  have h2 : ulocNormE (n + 1) χ (fun x => ouSg Q ν t nl x + ouSg Q ν t f x) ≤
      ENNReal.ofReal (Kc * t ^ (-γ)) * U + ENNReal.ofReal (Kb * t ^ (-γ)) * U :=
    (ul0_ulocNormE_add (n + 1) χ _ _).trans (add_le_add hPn hPf)
  calc ulocNormE (n + 1) χ (ouSg Q ν t φ1) + ENNReal.ofReal Cs * ulocNormE (n + 1) χ
        (fun x => ouSg Q ν t nl x + ouSg Q ν t f x)
      ≤ ENNReal.ofReal (Ka * t ^ (-γ)) * U + ENNReal.ofReal Cs *
          (ENNReal.ofReal (Kc * t ^ (-γ)) * U + ENNReal.ofReal (Kb * t ^ (-γ)) * U) :=
        add_le_add hP1 (mul_le_mul' le_rfl h2)
    _ = ENNReal.ofReal (Ka * t ^ (-γ) + Cs * (Kc * t ^ (-γ) + Kb * t ^ (-γ))) * U :=
        ul4_comb (by positivity) (by positivity) (by positivity) hCs.le U
    _ ≤ ENNReal.ofReal ((Ka + Cs * (Kb + Kc) + 1) * t ^ (-γ)) * U := by
        gcongr
        nlinarith [mul_nonneg hCs.le hKb0, mul_nonneg hCs.le hKc0]

/-! ### Regularity and linearity of `ulPert` on `C_b^4` -/

theorem ul4_inner_eq (c : Euc d → Euc d) (u : Euc d → ℝ) (x : Euc d) :
    inner ℝ (c x) (gradient u x) = fderiv ℝ u x (c x) := by
  have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := c x) (y := fderiv ℝ u x)
  unfold gradient; rw [real_inner_comm]; exact this

theorem ul4_pert_cb {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
    (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) {c : Euc d → Euc d} (hc : IsSmoothBounded c) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ u : Euc d → ℝ, MemCb 4 u →
      MemCb 2 (ulPert s M ρ c u) ∧ ∀ x, |ulPert s M ρ c u x| ≤ Cp * cbNorm 4 u := by
  obtain ⟨Cn, hCn0, hCn⟩ := ul_nl_cont hs0 hsd M ρ hρ 4 (by norm_num)
  choose Bc hBc using hc.2
  have hBc0 : ∀ j, 0 ≤ Bc j := fun j => (norm_nonneg _).trans (hBc j 0)
  refine ⟨Cn + Bc 0, add_nonneg hCn0 (hBc0 0), fun u hu => ?_⟩
  obtain ⟨hnl, hnlb⟩ := hCn u hu
  have hcb0 : 0 ≤ cbNorm 4 u := ul0_cbNorm_nonneg _ _
  have hfd : ContDiff ℝ 2 (fderiv ℝ u) := hu.1.fderiv_right (by norm_num)
  have hc2 : ContDiff ℝ 2 c := contDiff_infty.1 hc.1 2
  have htr : MemCb 2 (fun x => fderiv ℝ u x (c x)) := by
    refine ⟨hfd.clm_apply hc2, fun j hj => ?_⟩
    refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * cbNorm 4 u * Bc (j - i), ?_⟩
    rintro _ ⟨x, rfl⟩
    refine (norm_iteratedFDeriv_clm_apply (N := 2) hfd hc2 x (by exact_mod_cast hj)).trans ?_
    refine Finset.sum_le_sum fun i hi => ?_
    have h1 : ‖iteratedFDeriv ℝ i (fderiv ℝ u) x‖ ≤ cbNorm 4 u := by
      rw [norm_iteratedFDeriv_fderiv]
      exact ul3_cb_apply hu (by have := Finset.mem_range.1 hi; omega) x
    have h2 := hBc (j - i) x
    gcongr
  have hpe : ulPert s M ρ c u = fun x => fderiv ℝ u x (c x) - ulNL s M ρ u x := by
    funext x; simp only [ulPert, ul4_inner_eq]
  refine ⟨by rw [hpe]; exact ul1_memCb_sub htr (by simpa using hnl), fun x => ?_⟩
  rw [hpe]
  have h1 : |fderiv ℝ u x (c x)| ≤ cbNorm 4 u * Bc 0 := by
    have h1 := (fderiv ℝ u x).le_opNorm (c x)
    have h2 : ‖fderiv ℝ u x‖ ≤ cbNorm 4 u := by
      have := ul3_cb_apply hu (by norm_num : 1 ≤ 4) x
      rwa [norm_iteratedFDeriv_one] at this
    have h3 := hBc 0 x
    rw [norm_iteratedFDeriv_zero] at h3
    rw [← Real.norm_eq_abs]
    exact h1.trans (by gcongr)
  have h2 : |ulNL s M ρ u x| ≤ Cn * cbNorm 4 u := by
    have := ul3_cb_apply hnl (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans hnlb
  calc |fderiv ℝ u x (c x) - ulNL s M ρ u x| ≤ |fderiv ℝ u x (c x)| + |ulNL s M ρ u x| := abs_sub _ _
    _ ≤ cbNorm 4 u * Bc 0 + Cn * cbNorm 4 u := add_le_add h1 h2
    _ = (Cn + Bc 0) * cbNorm 4 u := by ring

theorem ul4_pert_sub {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
    (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) (c : Euc d → Euc d) {u v : Euc d → ℝ}
    (hu : MemCb 4 u) (hv : MemCb 4 v) (x : Euc d) :
    ulPert s M ρ c (fun y => u y - v y) x = ulPert s M ρ c u x - ulPert s M ρ c v x := by
  have hu1 : ContDiff ℝ 1 u := hu.1.of_le (by exact_mod_cast (by norm_num : 1 ≤ 4))
  have hv1 : ContDiff ℝ 1 v := hv.1.of_le (by exact_mod_cast (by norm_num : 1 ≤ 4))
  simp only [ulPert, ul4_inner_eq]
  rw [ul_nl_sub hs0 hsd M ρ hρ (by norm_num) hu hv x,
    fderiv_fun_sub (hu1.differentiable one_ne_zero x) (hv1.differentiable one_ne_zero x)]
  simp only [sub_apply]; ring

/-! ### The smoothing estimate on the closure -/

/-- **Smoothing estimate on `UlClosure`.**  For `(4 + d/2) < k`, `0 < t ≤ T`:
`‖P_t (ulPert u)‖_{H^k_ul} ≤ K t^{-γ} ‖u‖_{H^k_ul}` for every `u ∈ UlClosure k θ`
(from the smooth case by approximation and lower semicontinuity). -/
theorem ul4_pert_est {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
    (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) {c : Euc d → Euc d} (hc : IsSmoothBounded c)
    (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (T : ℝ) (k : ℕ) (hk : (4 : ℝ) + (d : ℝ) / 2 < k)
    (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) :
    ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Ioc (0 : ℝ) T, ∀ u : Euc d → ℝ, UlClosure k θ u →
      ulNormE k θ (ouSg Q ν t (ulPert s M ρ c u)) ≤
        ENNReal.ofReal (K * t ^ (-ul4gam d s)) * ulNormE k θ u := by
  obtain ⟨χ, hχ⟩ := ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := ul_equiv k θ χ hθ hχ
  have hk3 : 3 ≤ k := by
    have h4 : (3 : ℝ) < k := by
      have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
      linarith
    exact_mod_cast h4.le
  have hk4 : (4 : ℝ) + (d : ℝ) / 2 < k := hk
  obtain ⟨K0, hK0, hsm⟩ := ul4_pert_smooth hχ hs0 hsd M ρ hρ hc Q hν T k hk3
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 4 hk θ hθ
  obtain ⟨Cp, hCp0, hpcb⟩ := ul4_pert_cb hs0 hsd M ρ hρ hc
  obtain ⟨Cs, hCs, hsub⟩ := ul4_uloc_sub k χ
  refine ⟨Ce * K0 * Ce, by positivity, fun t ht u hu => ?_⟩
  set B0 : ℝ := K0 * t ^ (-ul4gam d s) with hB0
  have hB00 : 0 ≤ B0 := by have := Real.rpow_nonneg ht.1.le (-ul4gam d s); positivity
  have hufin := ul0_ulNormE_lt_top_of_closure k θ hθ hu
  obtain ⟨hu4, hucb⟩ := hcb u hu
  obtain ⟨hφ2, hφB⟩ := hpcb u hu4
  have hφc : Continuous (ulPert s M ρ c u) := hφ2.1.continuous
  -- the approximants
  have hex : ∀ j : ℕ, ∃ g : Euc d → ℝ, IsCcInftyPlusConst g ∧
      ulNormE k θ (fun x => u x - g x) ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1)) := fun j => by
    obtain ⟨g, hg, hle⟩ := hu.2 (1 / ((j : ℝ) + 1)) (by positivity)
    exact ⟨g, hg, hle⟩
  choose g hgc hgle using hex
  have hdj : ∀ j, UlClosure k θ (fun x => u x - g j x) := fun j => ul0_closure_sub_ccc k θ hu (hgc j)
  have hdcb : ∀ j, cbNorm 4 (fun x => u x - g j x) ≤ Ccb * (1 / ((j : ℝ) + 1)) := fun j => by
    refine ((hcb _ (hdj j)).2).trans ?_
    gcongr
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hgle j)
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hg4 : ∀ j, MemCb 4 (g j) := fun j => (ul4_ccc_props (hgc j)).2.1 4
  have hdiff : ∀ j x, |ulPert s M ρ c u x - ulPert s M ρ c (g j) x| ≤ Cp * (Ccb * (1 / ((j : ℝ) + 1))) :=
    fun j x => by
      rw [← ul4_pert_sub hs0 hsd M ρ hρ c hu4 (hg4 j) x]
      exact (((hpcb _ (hcb _ (hdj j)).1).2 x)).trans (by gcongr; exact hdcb j)
  -- the sequence
  set seq : ℕ → Euc d → ℝ := fun j => ouSg Q ν t (ulPert s M ρ c (g j)) with hseq
  have hφj2 : ∀ j, MemCb 2 (ulPert s M ρ c (g j)) := fun j => (hpcb _ (hg4 j)).1
  have hφjB : ∀ j x, |ulPert s M ρ c (g j) x| ≤ Cp * cbNorm 4 u + Cp * Ccb := fun j x => by
    have h1 := hdiff j x
    have h2 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have h3 := hφB x
    calc |ulPert s M ρ c (g j) x| ≤ |ulPert s M ρ c u x| + |ulPert s M ρ c u x - ulPert s M ρ c (g j) x| := by
          have := abs_sub (ulPert s M ρ c u x) (ulPert s M ρ c u x - ulPert s M ρ c (g j) x)
          simpa using this
      _ ≤ Cp * cbNorm 4 u + Cp * (Ccb * (1 / ((j : ℝ) + 1))) := add_le_add h3 h1
      _ ≤ _ := by
          have : Cp * (Ccb * (1 / ((j : ℝ) + 1))) ≤ Cp * Ccb := by
            calc Cp * (Ccb * (1 / ((j : ℝ) + 1))) ≤ Cp * (Ccb * 1) := by gcongr
              _ = Cp * Ccb := by ring
          linarith
  have hseqB : ∀ j x, |seq j x| ≤ Cp * cbNorm 4 u + Cp * Ccb := fun j x =>
    ul4_ouSg_abs_le Q ν t (hφjB j) x
  have hseq_lim : ∀ x, Tendsto (fun j => seq j x) atTop (𝓝 (ouSg Q ν t (ulPert s M ρ c u) x)) := by
    intro x
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
      (g := fun j : ℕ => Cp * (Ccb * (1 / ((j : ℝ) + 1)))) ?_
    · have hmφ : Measurable (ulPert s M ρ c u) := hφc.measurable
      have hmj : Measurable (ulPert s M ρ c (g j)) := (hφj2 j).1.continuous.measurable
      obtain ⟨Bu, hBu⟩ := ul3C_bdd_of_cb hφ2
      obtain ⟨Bj, hBj⟩ := ul3C_bdd_of_cb (hφj2 j)
      have := ul3C_sub_lin Q ν t hmφ hmj hBu hBj
      rw [Real.dist_eq]
      simp only [hseq]
      have e : ouSg Q ν t (ulPert s M ρ c u) x - ouSg Q ν t (ulPert s M ρ c (g j)) x =
          ouSg Q ν t (fun y => ulPert s M ρ c u y - ulPert s M ρ c (g j) y) x := by
        rw [this]
      rw [abs_sub_comm, e]
      exact ul4_ouSg_abs_le Q ν t (hdiff j) x
    · have h1 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (h1.const_mul Ccb).const_mul Cp
  have hAfin : ulocNormE k χ u < ⊤ :=
    lt_of_le_of_lt (hequ u).2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hufin)
  have hmain : ulocNormE k χ (ouSg Q ν t (ulPert s M ρ c u)) ≤
      ENNReal.ofReal B0 * ulocNormE k χ u := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε hfin => ?_
    have hε' : (0 : ℝ) < ε := NNReal.coe_pos.2 hε
    set δ : ℝ := (ε : ℝ) / (B0 * Cs * Ce + 1) with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨J, hJ⟩ := exists_nat_one_div_lt hδ0
    have hbd : ∀ n, ulocNormE k χ (seq (n + J)) ≤
        ENNReal.ofReal B0 * (ulocNormE k χ u + ENNReal.ofReal (Cs * Ce * δ)) := by
      intro n
      have h1 := hsm t ht (g (n + J)) (hgc _)
      have e : g (n + J) = fun x => u x - (u x - g (n + J) x) := by funext x; ring
      have h2 : ulocNormE k χ (g (n + J)) ≤ ulocNormE k χ u +
          ENNReal.ofReal Cs * ulocNormE k χ (fun x => u x - g (n + J) x) := by
        conv_lhs => rw [e]
        exact hsub u _
      have hle : 1 / (((n + J : ℕ) : ℝ) + 1) ≤ δ := by
        refine le_trans ?_ hJ.le
        gcongr
        push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h3 : ulocNormE k χ (fun x => u x - g (n + J) x) ≤ ENNReal.ofReal (Ce * δ) :=
        ((hequ _).2.trans (mul_le_mul' le_rfl (hgle _))).trans (by
          rw [← ENNReal.ofReal_mul hCe.le]
          exact ENNReal.ofReal_le_ofReal (by gcongr))
      refine h1.trans (mul_le_mul' le_rfl (h2.trans (add_le_add le_rfl ?_)))
      calc ENNReal.ofReal Cs * ulocNormE k χ (fun x => u x - g (n + J) x)
          ≤ ENNReal.ofReal Cs * ENNReal.ofReal (Ce * δ) := mul_le_mul' le_rfl h3
        _ = ENNReal.ofReal (Cs * Ce * δ) := by rw [← ENNReal.ofReal_mul hCs.le]; congr 1; ring
    have hlsc := ulocNormE_lsc k χ hχ (fun n => seq (n + J)) (ouSg Q ν t (ulPert s M ρ c u))
      (Cp * cbNorm 4 u + Cp * Ccb) (fun n x => hseqB _ x)
      (fun x => (tendsto_add_atTop_iff_nat J).2 (hseq_lim x)) _ hbd
    refine hlsc.trans ?_
    rw [mul_add, ul4_ofReal_mul_mul' hB00]
    gcongr
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (B0 * Cs * Ce + 1) * δ = ε := by rw [hδ]; field_simp
    nlinarith [mul_nonneg hB00 (mul_nonneg hCs.le hCe.le), mul_pos hδ0 hε']
  calc ulNormE k θ (ouSg Q ν t (ulPert s M ρ c u))
      ≤ ENNReal.ofReal Ce * ulocNormE k χ (ouSg Q ν t (ulPert s M ρ c u)) := (hequ _).1
    _ ≤ ENNReal.ofReal Ce * (ENNReal.ofReal B0 * ulocNormE k χ u) := mul_le_mul' le_rfl hmain
    _ ≤ ENNReal.ofReal Ce * (ENNReal.ofReal B0 * (ENNReal.ofReal Ce * ulNormE k θ u)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (hequ u).2)
    _ = ENNReal.ofReal (Ce * K0 * Ce * t ^ (-ul4gam d s)) * ulNormE k θ u := by
        rw [ul4_ofReal_mul_mul hB00, ul4_ofReal_mul_mul hCe.le]
        congr 2; rw [hB0]; ring

end HRS.MS.Ul
