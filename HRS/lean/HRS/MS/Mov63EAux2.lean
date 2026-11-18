import HRS.MS.Mov63EAux1

/-!
# S6.3, packet N6 (part 2): from the Hermite coefficients to every `C_c^∞` test function

Namespace `HRS.MS.Mov63`, prefix `mne_`.  See `Mov63EAux1` for the plan and the statement checks.

* `mne_parseval_d`: Parseval for the dilated Hermite system `h̃_α`.  `mne_pair_hasSum`, `mne_pair_partial`: for `f ∈ L²`, `y ∈ Σ^r` (`r ≥ 0`),
  `⟨f,y⟩ = ∑_α ⟨f,h̃_α⟩⟨h̃_α,y⟩` and every partial sum is bounded by `‖f‖_{L²}‖y‖`.
* **`mne_weak_lin`**: for `φ ∈ C_c^∞`, `t ≥ 0`: `⟨φ,v_t⟩ - ⟨φ,v_0⟩ = ∫_{[0,t]} ( -⟨S₀φ,v_x⟩ + ⟨φ,-R v_x + B(v_x,v_x)⟩ ) dx`
  (the converse of `mnc_weak_linear`): multiply the coefficient identity `mne_coeff_int` by `⟨φ,h̃_α⟩`, sum over `degree ≤ N`, `N → ∞`
  (dominated convergence in `x`; `⟨S₀φ,h̃_α⟩ = q|α|⟨φ,h̃_α⟩` by `mov2d_dcoeff_S0`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

section Pair

variable (hβ : 0 < β) (hq : 0 < q)
include hβ hq

lemma mne_dcoeff_eq_ipL {r : ℝ} (hr : 0 ≤ r) {g : Euc d → ℝ} (hg : MemOsc r g) (α : MultiIndex d) :
    mnc_ipL (mnc_hα d β q α) hr (OscSpace.ofFun r g) = mov2b_dcoeff (mov_dil β q) g α := by
  rw [mnc_ipL_ofFun (mnc_hα_good hβ hq α).1.l2 hr hg]
  unfold mov2b_dcoeff mnc_hα
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-- Parseval for the dilated Hermite system. -/
lemma mne_parseval_d {f g : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hg : MemLp g 2 (volume : Measure (Euc d))) :
    HasSum (fun α => mov2b_dcoeff (mov_dil β q) f α * mov2b_dcoeff (mov_dil β q) g α) (∫ x, f x * g x) := by
  have hl := mov_dil_pos hβ hq
  set l := mov_dil β q with hldef
  have h1 := mova2_parseval_inner (mov2b_memLp_inv hl hf) (mov2b_memLp_inv hl hg)
  have h2 := h1.mul_left ((l ^ d)⁻¹)
  have hint : ∫ y, f (l⁻¹ • y) * g (l⁻¹ • y) = l ^ d * ∫ x, f x * g x := by
    have h := Measure.integral_comp_smul (volume : Measure (Euc d)) (fun x => f x * g x) l⁻¹
    simp only [finrank_euclideanSpace_fin, smul_eq_mul] at h
    rw [h, abs_of_nonneg (by positivity), inv_pow, inv_inv]
  have hld : (0 : ℝ) < l ^ d := by positivity
  convert h2 using 1
  · funext α
    rw [mov2b_dcoeff_eq hl, mov2b_dcoeff_eq hl]
    have hss : Real.sqrt (l ^ d) * Real.sqrt (l ^ d) = l ^ d := Real.mul_self_sqrt hld.le
    have e : Real.sqrt (l ^ d) * (l ^ d)⁻¹ * hermiteCoeff (fun y => f (l⁻¹ • y)) α *
        (Real.sqrt (l ^ d) * (l ^ d)⁻¹ * hermiteCoeff (fun y => g (l⁻¹ • y)) α) =
        (Real.sqrt (l ^ d) * Real.sqrt (l ^ d)) * ((l ^ d)⁻¹) ^ 2 *
          (hermiteCoeff (fun y => f (l⁻¹ • y)) α * hermiteCoeff (fun y => g (l⁻¹ • y)) α) := by ring
    rw [e, hss]
    field_simp
  · rw [hint]; field_simp

lemma mne_pair_hasSum {r : ℝ} (hr : 0 ≤ r) {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (y : OscSpace d r) :
    HasSum (fun α => mov2b_dcoeff (mov_dil β q) f α * mnc_ipL (mnc_hα d β q α) hr y) (mnc_ipL f hr y) := by
  obtain ⟨g, hg, rfl⟩ := mnc_exists_fun_real hr y
  rw [mnc_ipL_ofFun hf hr hg]
  simp_rw [mne_dcoeff_eq_ipL hβ hq hr hg]
  exact mne_parseval_d hβ hq hf hg.1

lemma mne_pair_partial {r : ℝ} (hr : 0 ≤ r) {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (y : OscSpace d r) (S : Finset (MultiIndex d)) :
    |∑ α ∈ S, mov2b_dcoeff (mov_dil β q) f α * mnc_ipL (mnc_hα d β q α) hr y| ≤
      Real.sqrt (∫ x, f x ^ 2) * ‖y‖ := by
  obtain ⟨g, hg, rfl⟩ := mnc_exists_fun_real hr y
  simp_rw [mne_dcoeff_eq_ipL hβ hq hr hg]
  have hA : ∑ α ∈ S, mov2b_dcoeff (mov_dil β q) f α ^ 2 ≤ ∫ x, f x ^ 2 := by
    have := mne_parseval_d hβ hq hf hf
    simp_rw [← sq] at this
    exact sum_le_hasSum S (fun _ _ => sq_nonneg _) this
  have hB : ∑ α ∈ S, mov2b_dcoeff (mov_dil β q) g α ^ 2 ≤ ∫ x, g x ^ 2 := by
    have := mne_parseval_d hβ hq hg.1 hg.1
    simp_rw [← sq] at this
    exact sum_le_hasSum S (fun _ _ => sq_nonneg _) this
  have hgy : ∫ x, g x ^ 2 ≤ ‖OscSpace.ofFun r g‖ ^ 2 := by
    have h1 : mov2d_j hr (OscSpace.ofFun r g) = OscSpace.ofFun 0 g := mov2d_j_ofFun hr hg
    have h2 : ‖OscSpace.ofFun (0 : ℝ) g‖ ≤ ‖OscSpace.ofFun r g‖ := by
      rw [← h1]
      exact ((mov2d_j hr).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (mov2d_j_norm_le hr))
    have h3 : ‖OscSpace.ofFun (0 : ℝ) g‖ = Real.sqrt (∫ x, g x ^ 2) := by
      rw [OscSpace.norm_ofFun g ⟨hg.1, by simpa using mov2b_coeff_sq_summable hg.1⟩, oscNorm_zero g hg.1]
    rw [h3] at h2
    have h4 : 0 ≤ ∫ x, g x ^ 2 := integral_nonneg fun x => sq_nonneg _
    calc ∫ x, g x ^ 2 = Real.sqrt (∫ x, g x ^ 2) ^ 2 := (Real.sq_sqrt h4).symm
      _ ≤ _ := by gcongr
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun α => mov2b_dcoeff (mov_dil β q) f α)
    (fun α => mov2b_dcoeff (mov_dil β q) g α)
  have hF0 : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hsq : (∑ α ∈ S, mov2b_dcoeff (mov_dil β q) f α * mov2b_dcoeff (mov_dil β q) g α) ^ 2 ≤
      (∫ x, f x ^ 2) * ‖OscSpace.ofFun r g‖ ^ 2 := by
    refine hcs.trans ?_
    calc _ ≤ (∫ x, f x ^ 2) * (∑ α ∈ S, mov2b_dcoeff (mov_dil β q) g α ^ 2) :=
          mul_le_mul_of_nonneg_right hA (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ ≤ (∫ x, f x ^ 2) * ‖OscSpace.ofFun r g‖ ^ 2 := mul_le_mul_of_nonneg_left (hB.trans hgy) hF0
  have := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul hF0, Real.sqrt_sq (norm_nonneg _)] at this
  exact this

end Pair

section WeakLin

variable (H : Mov2dTh d s β q ρ) {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m)

variable {H hm}

/-- **Mild ⇒ linear weak identity against `C_c^∞` tests** (the reverse of `mnc_weak_linear`):
`⟨φ,v_t⟩ - ⟨φ,v_0⟩ = ∫_0^t ( -⟨S₀φ,v_x⟩ + ⟨φ, F(v_x)⟩ ) dx`, `F(v) = -R v + B(v,v)`. -/
theorem mne_weak_lin {v : ℝ → OscSpace d (m : ℝ)} (hmild : MneMild H hm v) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) {t : ℝ} (ht : 0 ≤ t) :
    mnc_ipL φ (Nat.cast_nonneg m) (v t) - mnc_ipL φ (Nat.cast_nonneg m) (v 0) =
      ∫ x in Icc (0 : ℝ) t, (-(mnc_ipL (mov_S0 d β q φ) (Nat.cast_nonneg m) (v x)) +
        mnc_ipL φ (mnb_sub_a_nonneg H hm) (mneF H hm v x)) := by
  have hβ := H.hβ
  have hq := H.hq
  set l := mov_dil β q with hldef
  set φS : 𝓢R := hφc.toSchwartzMap hφ with hφSdef
  have hφS : (⇑φS : Euc d → ℝ) = φ := rfl
  obtain ⟨χ, hχ⟩ := mov2d_S0_schwartz (d := d) (β := β) (q := q) φS
  rw [hφS] at hχ
  have hφ2 : MemLp φ 2 (volume : Measure (Euc d)) := by rw [← hφS]; exact φS.memLp 2
  have hψ2 : MemLp (mov_S0 d β q φ) 2 (volume : Measure (Euc d)) := by rw [← hχ]; exact χ.memLp 2
  have hcoef : ∀ α : MultiIndex d, mov2b_dcoeff l (mov_S0 d β q φ) α =
      q * (α.degree : ℝ) * mov2b_dcoeff l φ α := by
    intro α
    have := mov2d_dcoeff_S0 (d := d) hβ hq φS χ (by rw [hφS]; exact hχ) α
    rw [← hχ]
    simpa [hφS] using this
  have hr0 : 0 ≤ (m : ℝ) - movA d s := mnb_sub_a_nonneg H hm
  have hvT : ContinuousOn v (Icc 0 t) := hmild.cont.mono Icc_subset_Ici_self
  have hFT : ContinuousOn (mneF H hm v) (Icc 0 t) := (mneF_cont hmild.cont).mono Icc_subset_Ici_self
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hvT
  obtain ⟨M', hM'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hFT
  have hex : Tendsto (mova2_S d) atTop atTop := tendsto_atTop_finset_of_monotone mova2_S_mono mova2_S_exh
  set a : MultiIndex d → ℝ := fun α => mov2b_dcoeff l φ α with hadef
  set ℓ0 : MultiIndex d → OscSpace d (m : ℝ) →L[ℝ] ℝ := fun α => mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m)
    with hℓ0
  set ℓ1 : MultiIndex d → OscSpace d ((m : ℝ) - movA d s) →L[ℝ] ℝ := fun α => mnc_ipL (mnc_hα d β q α) hr0
    with hℓ1
  -- the partial sums of the identity
  have hN : ∀ N : ℕ, ∑ α ∈ mova2_S d N, a α * (ℓ0 α (v t) - ℓ0 α (v 0)) =
      ∫ x in Icc (0 : ℝ) t, ((-(∑ α ∈ mova2_S d N, mov2b_dcoeff l (mov_S0 d β q φ) α * ℓ0 α (v x))) +
        ∑ α ∈ mova2_S d N, a α * ℓ1 α (mneF H hm v x)) := by
    intro N
    have hint : ∀ α : MultiIndex d, IntegrableOn (fun x => -(q * (α.degree : ℝ)) * ℓ0 α (v x) + ℓ1 α (mneF H hm v x))
        (Icc 0 t) := by
      intro α
      exact (((continuousOn_const.mul ((ℓ0 α).continuous.comp_continuousOn hvT)).add
        ((ℓ1 α).continuous.comp_continuousOn hFT))).integrableOn_Icc
    have e1 : ∀ α ∈ mova2_S d N, a α * (ℓ0 α (v t) - ℓ0 α (v 0)) =
        ∫ x in Icc (0 : ℝ) t, a α * (-(q * (α.degree : ℝ)) * ℓ0 α (v x) + ℓ1 α (mneF H hm v x)) := by
      intro α _
      rw [integral_const_mul, ← mne_coeff_int hmild α ht]
    rw [Finset.sum_congr rfl e1, ← integral_finset_sum]
    · refine setIntegral_congr_fun measurableSet_Icc (fun x _ => ?_)
      show ∑ α ∈ mova2_S d N, a α * (-(q * (α.degree : ℝ)) * ℓ0 α (v x) + ℓ1 α (mneF H hm v x)) = _
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [hcoef, hadef]; ring
    · intro α _
      exact (hint α).const_mul _
  -- limits
  have hLHS : Tendsto (fun N : ℕ => ∑ α ∈ mova2_S d N, a α * (ℓ0 α (v t) - ℓ0 α (v 0))) atTop
      (𝓝 (mnc_ipL φ (Nat.cast_nonneg m) (v t) - mnc_ipL φ (Nat.cast_nonneg m) (v 0))) := by
    have h1 := mne_pair_hasSum hβ hq (Nat.cast_nonneg m) hφ2 (v t)
    have h2 := mne_pair_hasSum hβ hq (Nat.cast_nonneg m) hφ2 (v 0)
    have h3 := (h1.sub h2).comp hex
    refine h3.congr (fun N => ?_)
    simp only [Function.comp]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [hadef, hℓ0, hldef]
    ring
  have hRHS : Tendsto (fun N : ℕ => ∫ x in Icc (0 : ℝ) t,
      ((-(∑ α ∈ mova2_S d N, mov2b_dcoeff l (mov_S0 d β q φ) α * ℓ0 α (v x))) +
        ∑ α ∈ mova2_S d N, a α * ℓ1 α (mneF H hm v x))) atTop
      (𝓝 (∫ x in Icc (0 : ℝ) t, (-(mnc_ipL (mov_S0 d β q φ) (Nat.cast_nonneg m) (v x)) +
        mnc_ipL φ hr0 (mneF H hm v x)))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun _ => Real.sqrt (∫ x, (mov_S0 d β q φ x) ^ 2) * M + Real.sqrt (∫ x, φ x ^ 2) * M') ?_ ?_ ?_ ?_
    · intro N
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Icc
      refine ContinuousOn.add ?_ ?_
      · refine ContinuousOn.neg (continuousOn_finset_sum _ fun α _ => continuousOn_const.mul ?_)
        exact (ℓ0 α).continuous.comp_continuousOn hvT
      · exact continuousOn_finset_sum _ fun α _ => continuousOn_const.mul ((ℓ1 α).continuous.comp_continuousOn hFT)
    · exact integrable_const _
    · intro N
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun x hx => ?_)
      have b1 := mne_pair_partial hβ hq (Nat.cast_nonneg m) hψ2 (v x) (mova2_S d N)
      have b2 := mne_pair_partial hβ hq hr0 hφ2 (mneF H hm v x) (mova2_S d N)
      have h1 : ‖v x‖ ≤ M := hM x hx
      have h2 : ‖mneF H hm v x‖ ≤ M' := hM' x hx
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
      gcongr
      · exact b1.trans (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _))
      · exact b2.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun x hx => ?_)
      have g1 := (mne_pair_hasSum hβ hq (Nat.cast_nonneg m) hψ2 (v x)).comp hex
      have g2 := (mne_pair_hasSum hβ hq hr0 hφ2 (mneF H hm v x)).comp hex
      exact (g1.neg.add g2)
  have heq : ∀ N : ℕ, ∑ α ∈ mova2_S d N, a α * (ℓ0 α (v t) - ℓ0 α (v 0)) = ∫ x in Icc (0 : ℝ) t,
      ((-(∑ α ∈ mova2_S d N, mov2b_dcoeff l (mov_S0 d β q φ) α * ℓ0 α (v x))) +
        ∑ α ∈ mova2_S d N, a α * ℓ1 α (mneF H hm v x)) := hN
  exact tendsto_nhds_unique hLHS (hRHS.congr (fun N => (heq N).symm))

end WeakLin

end HRS.MS.Mov63

end
