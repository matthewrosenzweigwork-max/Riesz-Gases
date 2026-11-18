import HRS.MS.PathFidiAux1

/-!
# SA26 packet P2: Schwartz tests, bounds of the adjoint orbits, cutoff norms, B5 (commutator input)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.PathFidi

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-! ### Schwartz tests are Sobolev tests of every order -/

open scoped FourierTransform in
theorem sa26_schwartz_weighted_int (g : SchwartzMap (Euc d) ℂ) (k : ℕ) :
    Integrable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ k * ‖g ξ‖ ^ 2) := by
  obtain ⟨C0, hC0pos, hC0⟩ := g.decay 0 0
  obtain ⟨Ck, hCkpos, hCk⟩ := g.decay k 0
  have hg0 : ∀ ξ, ‖g ξ‖ ≤ C0 := fun ξ => by
    have := hC0 ξ
    simpa [norm_iteratedFDeriv_zero] using this
  have hgk : ∀ ξ, ‖ξ‖ ^ k * ‖g ξ‖ ≤ Ck := fun ξ => by
    have := hCk ξ
    simpa [norm_iteratedFDeriv_zero] using this
  have hi0 : Integrable (fun ξ : Euc d => ‖g ξ‖) := g.integrable.norm
  have hik : Integrable (fun ξ : Euc d => ‖ξ‖ ^ k * ‖g ξ‖) := by
    simpa using g.integrable_pow_mul volume k
  have hpow : ∀ r : ℝ, 0 ≤ r → (1 + r) ^ k ≤ 2 ^ k * (1 + r ^ k) := fun r hr => by
    rcases le_total r 1 with h | h
    · calc (1 + r) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
        _ ≤ 2 ^ k * (1 + r ^ k) := by
          have : 0 ≤ r ^ k := pow_nonneg hr k
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
    · calc (1 + r) ^ k ≤ (2 * r) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
        _ = 2 ^ k * r ^ k := by rw [mul_pow]
        _ ≤ 2 ^ k * (1 + r ^ k) := by
          have : 0 ≤ r ^ k := pow_nonneg hr k
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
  have hint : Integrable (fun ξ : Euc d => (1 + ‖ξ‖) ^ k * ‖g ξ‖) := by
    refine Integrable.mono' ((hi0.add hik).const_mul (2 ^ k)) ?_ (Eventually.of_forall fun ξ => ?_)
    · exact (Continuous.mul (by fun_prop) g.continuous.norm).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      calc (1 + ‖ξ‖) ^ k * ‖g ξ‖ ≤ 2 ^ k * (1 + ‖ξ‖ ^ k) * ‖g ξ‖ :=
            mul_le_mul_of_nonneg_right (hpow _ (norm_nonneg _)) (norm_nonneg _)
        _ = 2 ^ k * (‖g ξ‖ + ‖ξ‖ ^ k * ‖g ξ‖) := by ring
  have hbd : ∀ ξ : Euc d, (1 + ‖ξ‖) ^ k * ‖g ξ‖ ≤ 2 ^ k * (C0 + Ck) := fun ξ => by
    calc (1 + ‖ξ‖) ^ k * ‖g ξ‖ ≤ 2 ^ k * (1 + ‖ξ‖ ^ k) * ‖g ξ‖ :=
          mul_le_mul_of_nonneg_right (hpow _ (norm_nonneg _)) (norm_nonneg _)
      _ = 2 ^ k * (‖g ξ‖ + ‖ξ‖ ^ k * ‖g ξ‖) := by ring
      _ ≤ 2 ^ k * (C0 + Ck) := by
          gcongr
          · exact hg0 ξ
          · exact hgk ξ
  set c : ℝ := (1 + 2 * Real.pi) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  refine Integrable.mono' (hint.const_mul (c ^ k * (2 ^ k * (C0 + Ck)))) ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (Continuous.mul (by fun_prop) (g.continuous.norm.pow 2)).aestronglyMeasurable
  · have h1 : 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 ≤ c * (1 + ‖ξ‖) ^ 2 := by
      rw [hc]
      nlinarith [Real.pi_pos, norm_nonneg ξ, mul_nonneg Real.pi_pos.le (norm_nonneg ξ),
        mul_nonneg (mul_nonneg Real.pi_pos.le Real.pi_pos.le) (norm_nonneg ξ)]
    have h2 : (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ k ≤ (c * (1 + ‖ξ‖) ^ 2) ^ k :=
      pow_le_pow_left₀ (by positivity) h1 k
    rw [Real.norm_of_nonneg (by positivity)]
    have hp : ((1 + ‖ξ‖) ^ 2) ^ k = (1 + ‖ξ‖) ^ k * (1 + ‖ξ‖) ^ k := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    calc (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ k * ‖g ξ‖ ^ 2 ≤ (c * (1 + ‖ξ‖) ^ 2) ^ k * ‖g ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = c ^ k * (((1 + ‖ξ‖) ^ k * ‖g ξ‖) * ((1 + ‖ξ‖) ^ k * ‖g ξ‖)) := by
          rw [mul_pow, hp]; ring
      _ ≤ c ^ k * ((2 ^ k * (C0 + Ck)) * ((1 + ‖ξ‖) ^ k * ‖g ξ‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hbd ξ) (by positivity)) (by positivity)
      _ = c ^ k * (2 ^ k * (C0 + Ck)) * ((1 + ‖ξ‖) ^ k * ‖g ξ‖) := by ring

open scoped FourierTransform in
theorem sa26_schwartz_memSob (ψ : SchwartzMap (Euc d) ℝ) (k : ℕ) :
    HRS.PDE.ToolboxRd.MemSobolev (k : ℝ) (fun x => ψ x) := by
  refine ⟨ψ.memLp 2 volume, ?_⟩
  set φ : SchwartzMap (Euc d) ℂ := ψ.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM with hφ
  have hF := HRS.PDE.ToolboxRd.FourierAux.fourierL2_schwartz ψ
  have hg : (⇑(SchwartzMap.fourierTransformCLM ℂ φ) : Euc d → ℂ) = 𝓕 (fun x : Euc d => ((ψ x : ℝ) : ℂ)) := rfl
  have hint := sa26_schwartz_weighted_int (SchwartzMap.fourierTransformCLM ℂ φ) k
  refine hint.congr ?_
  filter_upwards [hF] with ξ hξ
  have e : HRS.PDE.ToolboxRd.fourierL2 (fun x => ψ x) ξ = (SchwartzMap.fourierTransformCLM ℂ φ) ξ := by
    rw [hξ]; rfl
  rw [e, Real.rpow_natCast]

theorem sa26_schwartz_sob (ψ : SchwartzMap (Euc d) ℝ) (k : ℕ) : IsSobolevTest (k : ℝ) (fun x => ψ x) :=
  ⟨ψ.smooth (⊤ : ℕ∞), sa26_schwartz_memSob ψ k⟩


/-! ### Bounds of the adjoint orbits -/

theorem sa26_iter_le_of_partial {f : Euc d → ℝ} {j : ℕ} {B : ℝ}
    (hB : ∀ l ≤ j, ∀ (i : Fin l → Fin d) (x : Euc d), |partialDeriv i f x| ≤ B) :
    ∀ l ≤ j, ∀ x, ‖iteratedFDeriv ℝ l f x‖ ≤ (d : ℝ) ^ l * B :=
  fun l hl x => (HRS.MP.RdInit.mri_norm_iter_le l f x).trans
    (HRS.MS.Go.s55_card_sum_le l _ fun idx => hB l hl idx x)

theorem sa26_memCb_of_iter {f : Euc d → ℝ} {j : ℕ} {B : ℝ} (hf : ContDiff ℝ j f)
    (hB : ∀ l ≤ j, ∀ x, ‖iteratedFDeriv ℝ l f x‖ ≤ B) :
    MemCb j f ∧ cbNorm j f ≤ (j + 1) * B := by
  refine ⟨⟨hf, fun l hl => ⟨B, ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hB l hl x
  · unfold cbNorm
    calc ∑ l ∈ Finset.range (j + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ l f z‖
        ≤ ∑ _l ∈ Finset.range (j + 1), B := by
          refine Finset.sum_le_sum fun l hl => ciSup_le fun z => hB l ?_ z
          have := Finset.mem_range.1 hl
          omega
      _ = (j + 1) * B := by simp

theorem sa26_adj_bounds {C : WholeCoeff d} {Γ : ℝ} {j : ℕ} {T K : ℝ} (hd : 1 ≤ d)
    (h : AdjointInputOneD Γ j C T K) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T)
    {φ : Euc d → ℝ} (hφ : IsSobolevTest Γ φ) :
    (∃ f, IsClassicalAdjointW C t φ f) ∧ ContDiff ℝ j (propagatorW C r t φ) ∧
      0 ≤ K * HRS.Whole.sobolevNorm Γ φ ∧
      ∀ l ≤ j, ∀ x, ‖iteratedFDeriv ℝ l (propagatorW C r t φ) x‖ ≤ (d : ℝ) ^ j * (K * HRS.Whole.sobolevNorm Γ φ) := by
  obtain ⟨hex, hcd, -, hbd⟩ := h r t hr hrt htT φ hφ
  have h0 : 0 ≤ K * HRS.Whole.sobolevNorm Γ φ := by
    have := hbd 0 (Nat.zero_le _) (fun i => Fin.elim0 i) 0
    exact (abs_nonneg _).trans this
  refine ⟨hex, hcd, h0, fun l hl x => ?_⟩
  have := sa26_iter_le_of_partial (fun l' hl' i x' => hbd l' hl' i x') l hl x
  refine this.trans ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast hd) hl) h0

theorem sa26_lip_transport (M : Matrix (Fin d) (Fin d) ℝ) {f : Euc d → ℝ} (hf : MemCb 2 f) :
    HasLipBoundW (fun x => Torus.matVec M.transpose (gradient f x))
      (HRS.MS.SuppU15.u15_cM M.transpose * cbNorm 2 f) := by
  have hcb0 : 0 ≤ cbNorm 2 f := Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hcM0 := HRS.MS.SuppU15.u15_cM_nonneg M.transpose
  refine ⟨Real.toNNReal (HRS.MS.SuppU15.u15_cM M.transpose * cbNorm 2 f), ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hcM0 hcb0)]
    have e1 : Torus.matVec M.transpose (gradient f x) - Torus.matVec M.transpose (gradient f y) =
        Torus.matVec M.transpose (gradient f x - gradient f y) := by
      simp only [Torus.matVec]; simp
    rw [e1]
    calc ‖Torus.matVec M.transpose (gradient f x - gradient f y)‖
        ≤ HRS.MS.SuppU15.u15_cM M.transpose * ‖gradient f x - gradient f y‖ :=
          HRS.MS.SuppU15.u15_matVec_norm_le _ _
      _ ≤ HRS.MS.SuppU15.u15_cM M.transpose * (cbNorm 2 f * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (HRS.MS.Go.s55_grad_lip_cb hf x y) hcM0
      _ = HRS.MS.SuppU15.u15_cM M.transpose * cbNorm 2 f * ‖x - y‖ := by ring
  · rw [Real.coe_toNNReal _ (mul_nonneg hcM0 hcb0)]

theorem sa26_oNΛ_mono (d : ℕ) (s : ℝ) {C C' : ℝ} (hC : C ≤ C') {Λ : ℝ} (hΛ : 0 ≤ Λ) (N : ℕ) :
    oNΛ d s C Λ N ≤ oNΛ d s C' Λ N := by
  unfold oNΛ
  have : 0 ≤ Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) :=
    mul_nonneg (Real.rpow_nonneg hΛ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  nlinarith

/-! ### The gradient of an orbit and the bilinear products -/

theorem sa26_grad_contDiff {U : Euc d → ℝ} {k : ℕ} (hU : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) U) :
    ContDiff ℝ (k : WithTop ℕ∞) (gradient U) := by
  have h1 : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ U) :=
    hU.fderiv_right (m := (k : WithTop ℕ∞)) (by exact_mod_cast le_refl (k + 1))
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp h1

theorem sa26_norm_iter_grad {U : Euc d → ℝ} {k : ℕ} (x : Euc d) :
    ‖iteratedFDeriv ℝ k (gradient U) x‖ = ‖iteratedFDeriv ℝ (k + 1) U x‖ := by
  have e : gradient U = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ U := rfl
  rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]

theorem sa26_inner_grad_bounds {U V : Euc d → ℝ} {k : ℕ}
    (hU : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) U) (hV : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) V)
    {B₁ B₂ : ℝ} (hB₁ : ∀ l ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ l U x‖ ≤ B₁)
    (hB₂ : ∀ l ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ l V x‖ ≤ B₂) :
    ContDiff ℝ (k : WithTop ℕ∞) (fun x => inner ℝ (gradient U x) (gradient V x)) ∧
      ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n (fun x => inner ℝ (gradient U x) (gradient V x)) x‖ ≤
        2 ^ n * (B₁ * B₂) := by
  have hgU := sa26_grad_contDiff hU
  have hgV := sa26_grad_contDiff hV
  have hB10 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ 0 (Nat.zero_le _) 0)
  have hB20 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ 0 (Nat.zero_le _) 0)
  refine ⟨hgU.inner ℝ hgV, fun n hn x => ?_⟩
  have h := ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (f := gradient U) (g := gradient V) (N := (k : WithTop ℕ∞))
    hgU hgV x (n := n) (by exact_mod_cast hn) (norm_innerSL_le ℝ)
  refine le_trans (le_of_eq rfl) (h.trans ?_)
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (gradient U) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (gradient V) x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (B₁ * B₂) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [sa26_norm_iter_grad, sa26_norm_iter_grad]
        have h1 := hB₁ (i + 1) (by omega) x
        have h2 := hB₂ (n - i + 1) (by omega) x
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) hB10) (Nat.cast_nonneg _)
    _ = 2 ^ n * (B₁ * B₂) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n


theorem sa26_cNorm_inner (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ (U V : Euc d → ℝ) (B₁ B₂ : ℝ), ContDiff ℝ ((mStar d : ℕ) : WithTop ℕ∞) U →
      ContDiff ℝ ((mStar d : ℕ) : WithTop ℕ∞) V →
      (∀ l ≤ mStar d, ∀ x, ‖iteratedFDeriv ℝ l U x‖ ≤ B₁) →
      (∀ l ≤ mStar d, ∀ x, ‖iteratedFDeriv ℝ l V x‖ ≤ B₂) →
      cNormE χ (fun x => inner ℝ (gradient U x) (gradient V x)) ≤ ENNReal.ofReal (Cn * (B₁ * B₂)) := by
  obtain ⟨k, hk⟩ : ∃ k, mStar d = k + 1 := ⟨mStar d - 1, by unfold mStar; omega⟩
  have hk1 : 1 ≤ k := by unfold mStar at hk; omega
  have hkm : mStar d - 1 = k := by omega
  obtain ⟨Cu, hCu0, hCu⟩ := HRS.MS.Ul.ulocNormE_le_cb k χ hχ
  refine ⟨3 + Cu * (((k : ℝ) + 1) * 2 ^ k), by positivity, fun U V B₁ B₂ hU hV hB₁ hB₂ => ?_⟩
  rw [hk] at hU hV hB₁ hB₂
  have hB10 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ 0 (Nat.zero_le _) 0)
  have hB20 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ 0 (Nat.zero_le _) 0)
  have hP : 0 ≤ B₁ * B₂ := mul_nonneg hB10 hB20
  obtain ⟨hHcd, hHb⟩ := sa26_inner_grad_bounds hU hV hB₁ hB₂
  set H : Euc d → ℝ := fun x => inner ℝ (gradient U x) (gradient V x) with hH
  have hHb' : ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n H x‖ ≤ 2 ^ k * (B₁ * B₂) := fun n hn x =>
    (hHb n hn x).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hP)
  obtain ⟨hmem, hcb⟩ := sa26_memCb_of_iter hHcd hHb'
  have hul : ulocNormE k χ H ≤ ENNReal.ofReal (Cu * (((k : ℝ) + 1) * (2 ^ k * (B₁ * B₂)))) :=
    (hCu H hmem).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcb hCu0.le))
  have hlip : lipNormE H ≤ ENNReal.ofReal (3 * (B₁ * B₂)) := by
    unfold lipNormE
    have h1 : (⨆ x, ENNReal.ofReal |H x|) ≤ ENNReal.ofReal (B₁ * B₂) :=
      iSup_le fun x => ENNReal.ofReal_le_ofReal (by
        have := hHb 0 (Nat.zero_le _) x
        simpa [norm_iteratedFDeriv_zero] using this)
    have h2 : (⨆ p : {p : Euc d × Euc d // p.1 ≠ p.2},
        ENNReal.ofReal (|H p.1.1 - H p.1.2| / ‖p.1.1 - p.1.2‖)) ≤ ENNReal.ofReal (2 * (B₁ * B₂)) := by
      refine iSup_le fun p => ENNReal.ofReal_le_ofReal ?_
      have hne : 0 < ‖p.1.1 - p.1.2‖ := norm_pos_iff.2 (sub_ne_zero.2 p.2)
      rw [div_le_iff₀ hne]
      have hdf : Differentiable ℝ H := hHcd.differentiable (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hk1)
      have hf : ∀ z, ‖fderiv ℝ H z‖ ≤ 2 * (B₁ * B₂) := fun z => by
        rw [← norm_iteratedFDeriv_one]
        simpa using hHb 1 hk1 z
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := H) (s := Set.univ)
        (fun z _ => hdf z) (fun z _ => hf z) convex_univ (Set.mem_univ p.1.2) (Set.mem_univ p.1.1)
      simpa [Real.norm_eq_abs, mul_comm] using this
    calc _ ≤ ENNReal.ofReal (B₁ * B₂) + ENNReal.ofReal (2 * (B₁ * B₂)) := add_le_add h1 h2
      _ = ENNReal.ofReal (3 * (B₁ * B₂)) := by
          rw [← ENNReal.ofReal_add hP (by positivity)]
          congr 1; ring
  unfold cNormE
  rw [hkm]
  calc lipNormE H + ulocNormE k χ H
      ≤ ENNReal.ofReal (3 * (B₁ * B₂)) +
        ENNReal.ofReal (Cu * (((k : ℝ) + 1) * (2 ^ k * (B₁ * B₂)))) := add_le_add hlip hul
    _ = ENNReal.ofReal ((3 + Cu * (((k : ℝ) + 1) * 2 ^ k)) * (B₁ * B₂)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring


/-! ### B5: the selected commutator estimate from the field adjoint input -/

/-- `F + o ≥ 0` at the constants `(C₀, Λ)` of the statement, for `C₀` large (`Λ > 0` is arbitrary, possibly `< 1`). -/
theorem sa26_energy_nonneg (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) :
    ∃ C₁ : ℝ, 0 < Λ → ∀ C₀ : ℝ, C₁ ≤ C₀ → ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → (s = 0 → Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ)) →
      ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
        0 ≤ rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + oNΛ d s C₀ Λ N := by
  obtain ⟨C₀', C₁c, hC₀', hpair⟩ := HRS.MH.CoercTest.p_assembly d hd s hs0 hsd
  obtain ⟨C₂, hC₂⟩ := sa26_oN_comp d hd s hs0 Λ C₀'
  refine ⟨C₂, fun hΛ C₀ hC N hN ρ hρ hρΛ hlog X hX => ?_⟩
  have hcomp := (hpair C₀' le_rfl).1
  have h1 := hcomp.2 (max Λ 1) (le_max_right _ _) N hN ρ hρ
    (fun x => (hρΛ x).trans (le_max_left _ _)) hlog X hX
  have h2 := hC₂ hΛ C₀ hC N (by omega)
  linarith

section B5

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ} {𝔈 : ℕ → ℝ}

/-- the weighted bound of the density slices as a pointwise bound -/
theorem sa26_weighted_zero (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S.T) (x : Euc d) :
    jbracket x ^ ((d : ℝ) + 3) * |S.ρ N t x| ≤ max Λ 0 := by
  obtain ⟨hcb, hfin, hle⟩ := (hS.mean_field.regular N hN).1 t ht
  have hcb0 : 0 ≤ cbNorm r (S.ρ N t) :=
    Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hΛ : 0 ≤ Λ := (sa26_Lam_pos hS).le
  have h1 : (weightedSupE r ((d : ℝ) + 3) (S.ρ N t)).toReal ≤ Λ := by linarith
  have h2 : weightedSupE r ((d : ℝ) + 3) (S.ρ N t) ≤ ENNReal.ofReal Λ :=
    (ENNReal.le_ofReal_iff_toReal_le hfin.ne hΛ).2 h1
  exact HRS.MS.SuppU15.u15_weighted_zero h2 x

theorem sa26_mono_mul {A A' E' E : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A') (hE : E' ≤ E) (hE0 : 0 ≤ E) :
    A * E' ≤ A' * E := by
  calc A * E' ≤ A * E := mul_le_mul_of_nonneg_left hE hA
    _ ≤ A' * E := mul_le_mul_of_nonneg_right hAA hE0

/-- log-integrability of the density slices at `s = 0` -/
theorem sa26_log_int (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal (S.ρ N t)) :=
  Q09A.log_integrable_withDensityReal ((hS.mean_field.solution N hN).density t ht)
    ((hS.mean_field.solution N hN).second_moment t ht)

/-! ### B5, assembly -/

theorem sa26_B5_super (s : ℝ) (fd : FieldDensityRd d s) (ν₀ MB Λ ΛV G₀ Kad : ℝ) (hd : 1 ≤ d) (hs0 : 0 ≤ s)
    (hsd : s < d) (hsc : (d : ℝ) - 2 ≤ s) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ (S : WholeMainData d), S.s = s → fd.Holds S ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ) (m20 : ℝ) (r mV : ℕ),
        RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈 → FieldAdjointInputRd fd S Kad →
        ∃ K' : ℝ, 0 ≤ K' ∧ SelectedCommutatorInput S (fd.Gamma : ℝ) S.T K' C₀ Λ fd.eN := by
  obtain ⟨C₁e, hC₁e⟩ := sa26_energy_nonneg hd hs0 hsd Λ
  obtain ⟨Lm, hLm⟩ := HRS.MS.SuppU15.u15_logmoment (d := d) (L := (d : ℝ) + 3) (by linarith) Λ
  obtain ⟨C₀B, CB, hC₀B, hCB, hB⟩ :=
    HRS.MH.CommSuper.whole_commutator_super_of_concentration_proof (d := d) hd hs0 hsd hsc Lm
  obtain ⟨C₂, hC₂⟩ := sa26_oN_comp d hd s hs0 Λ C₀B
  refine ⟨max C₁e C₂, fun C₀ hC₀ S hSs hHolds R 𝔈 m20 r mV hS hF => ?_⟩
  have hΛ := sa26_Lam_pos hS
  have he : ∀ N, fd.eN N = 0 := by
    have h1 := hHolds 1 le_rfl
    cases fd with
    | nd Rg => intro N; rfl
    | decSub c =>
      exfalso
      have h2 : S.s < (d : ℝ) - 2 := h1
      rw [hSs] at h2
      linarith
    | decSuperIso m p => intro N; rfl
    | decSuperHilb m => intro N; rfl
  have hm2 : 2 ≤ mStar d := by unfold mStar; omega
  have hcM0 := HRS.MS.SuppU15.u15_cM_nonneg S.M.transpose
  refine ⟨CB * (HRS.MS.SuppU15.u15_cM S.M.transpose * (3 * ((d : ℝ) ^ mStar d * max Kad 0))),
    mul_nonneg hCB.le (mul_nonneg hcM0 (by positivity)), ?_⟩
  intro N hN X hX r' t hr' hrt htT φ hφ
  have hN1 : 1 ≤ N := by omega
  have hrT : r' ∈ Set.Icc (0 : ℝ) S.T := ⟨hr', hrt.trans htT⟩
  obtain ⟨-, hcd, h0, hit⟩ := sa26_adj_bounds hd (hF.deriv N hN1) hr' hrt htT hφ
  set U := propagatorW (S.coeff N) r' t φ with hU
  set B : ℝ := (d : ℝ) ^ mStar d * (Kad * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ) with hBdef
  have hmem := sa26_memCb_of_iter (j := 2) (f := U)
    (hcd.of_le (by exact_mod_cast hm2)) (fun l hl x => hit l (by omega) x)
  have hlip := sa26_lip_transport S.M hmem.1
  have hprob := (hS.mean_field.solution N hN1).density r' hrT
  have hρle : ∀ x, S.ρ N r' x ≤ max Λ 1 := fun x => (sa26_rho_le hS hN1 hrT x).trans (le_max_left _ _)
  have hlog : s = 0 → HasLogMoment (HRS.Whole.withDensityReal (S.ρ N r')) Lm :=
    fun _ => hLm (S.ρ N r') hprob (fun x => sa26_weighted_zero hS hN1 hrT x)
  obtain ⟨-, hb⟩ := hB (max Λ 1) (le_max_right _ _) N hN (S.ρ N r') hprob hρle hlog X hX _ _ hlip
  have hE0 := hC₁e hΛ C₀ (le_trans (le_max_left _ _) hC₀) N hN (S.ρ N r') hprob
    (fun x => sa26_rho_le hS hN1 hrT x) (fun _ => sa26_log_int hS hN1 hrT) X
    (fun ⟨i, j, hij, h⟩ => hij (hX h))
  have ho := hC₂ hΛ C₀ (le_trans (le_max_right _ _) hC₀) N hN1
  have hcb0 : 0 ≤ cbNorm 2 U := Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hcb3 : cbNorm 2 U ≤ 3 * B := by
    have := hmem.2
    norm_num at this
    linarith
  have hB0 : 0 ≤ B := by positivity
  have hA0 : 0 ≤ CB * (HRS.MS.SuppU15.u15_cM S.M.transpose * cbNorm 2 U) :=
    mul_nonneg hCB.le (mul_nonneg hcM0 hcb0)
  have hAA : CB * (HRS.MS.SuppU15.u15_cM S.M.transpose * cbNorm 2 U) ≤
      CB * (HRS.MS.SuppU15.u15_cM S.M.transpose * (3 * B)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcb3 hcM0) hCB.le
  have hsob : 0 ≤ HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ := Real.sqrt_nonneg _
  have hKB : CB * (HRS.MS.SuppU15.u15_cM S.M.transpose * (3 * B)) ≤
      CB * (HRS.MS.SuppU15.u15_cM S.M.transpose * (3 * ((d : ℝ) ^ mStar d * max Kad 0))) *
        HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ := by
    have h1 : Kad * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ ≤ max Kad 0 * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hsob
    have h2 : B ≤ (d : ℝ) ^ mStar d * (max Kad 0 * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    calc CB * (HRS.MS.SuppU15.u15_cM S.M.transpose * (3 * B))
        ≤ CB * (HRS.MS.SuppU15.u15_cM S.M.transpose * (3 * ((d : ℝ) ^ mStar d *
            (max Kad 0 * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ)))) := by gcongr
      _ = _ := by ring
  rw [hSs, he N]
  calc |commN d s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r' t φ) x)) X
          (HRS.Whole.withDensityReal (S.ρ N r'))|
      ≤ CB * (HRS.MS.SuppU15.u15_cM S.M.transpose * cbNorm 2 U) *
        (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (S.ρ N r')) + oNΛ d s C₀B (max Λ 1) N) := hb
    _ ≤ CB * (HRS.MS.SuppU15.u15_cM S.M.transpose * (3 * B)) *
        (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (S.ρ N r')) + oNΛ d s C₀ Λ N) := by
        refine sa26_mono_mul hA0 hAA ?_ hE0
        exact add_le_add_right ho _
    _ ≤ CB * (HRS.MS.SuppU15.u15_cM S.M.transpose * (3 * ((d : ℝ) ^ mStar d * max Kad 0))) *
        HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ *
        (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (S.ρ N r')) + oNΛ d s C₀ Λ N) :=
        mul_le_mul_of_nonneg_right hKB hE0
    _ = _ := by ring

theorem sa26_B5_sub (s : ℝ) (c : DecayingDensity d s) (ν₀ MB Λ ΛV G₀ Kad : ℝ) (hd : 1 ≤ d) (hs0 : 0 ≤ s)
    (hsub : s < (d : ℝ) - 2) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ (S : WholeMainData d), S.s = s →
      (FieldDensityRd.decSub c).Holds S ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ) (m20 : ℝ) (r mV : ℕ),
        RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈 → FieldAdjointInputRd (FieldDensityRd.decSub c) S Kad →
        ∃ K' : ℝ, 0 ≤ K' ∧ SelectedCommutatorInput S ((FieldDensityRd.decSub c).Gamma : ℝ) S.T K' C₀ Λ
          (FieldDensityRd.decSub c).eN := by
  have hsd : s < d := by linarith
  obtain ⟨C₁e, hC₁e⟩ := sa26_energy_nonneg hd hs0 hsd Λ
  obtain ⟨Lm, hLm⟩ := HRS.MS.SuppU15.u15_logmoment (d := d) (L := (d : ℝ) + 3) (by linarith) Λ
  have key : ∃ C₀B CB : ℝ, 0 ≤ C₀B ∧ 0 < CB ∧ ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ,
      HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ') → (s = 0 → HasLogMoment (HRS.Whole.withDensityReal ρ) Lm) →
      ∀ X : EucConfig d N, Function.Injective X → ∀ (v : Euc d → Euc d) (K : ℝ),
        HasFracTransportBound c.regularity c.integrability v K →
        |commN d s v X (HRS.Whole.withDensityReal ρ)| ≤
          CB * K * (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + oNΛ d s C₀B Λ' N +
            CB * c.errorRate N) := by
    cases c with
    | sharp a ha =>
      obtain ⟨C₀B, CB, hC₀B, hCB, hB⟩ :=
        HRS.Commutator.Whole.whole_commutator_sub_sharp_of_subcoulomb (d := d) hs0 hsub a
          ⟨ha.1, lt_of_lt_of_le ha.2 (min_le_left _ _)⟩ Lm
      refine ⟨C₀B, CB, hC₀B, hCB, fun Λ' hΛ' N hN ρ hρ hρΛ hlog X hX v K hv => ?_⟩
      obtain ⟨-, hb⟩ := hB Λ' hΛ' N hN ρ hρ hρΛ hlog X hX v K hv
      simpa [DecayingDensity.errorRate] using hb
    | lower hs' =>
      obtain ⟨C₀B, CB, hC₀B, hCB, hB⟩ :=
        HRS.Commutator.Whole.whole_commutator_sub_lower_of_subcoulomb (d := d) hs0 hsub Lm
      refine ⟨C₀B, CB, hC₀B, hCB, fun Λ' hΛ' N hN ρ hρ hρΛ hlog X hX v K hv => ?_⟩
      obtain ⟨-, hb⟩ := hB Λ' hΛ' N hN ρ hρ hρΛ hlog X hX v K hv
      exact hb
  obtain ⟨C₀B, CB, hC₀B, hCB, hB⟩ := key
  obtain ⟨C₂, hC₂⟩ := sa26_oN_comp d hd s hs0 Λ C₀B
  refine ⟨max C₁e C₂, fun C₀ hC₀ S hSs hHolds R 𝔈 m20 r mV hS hF => ?_⟩
  have hΛ := sa26_Lam_pos hS
  have hw := hF.wbound
  unfold FieldDensityRd.wInput at hw
  have hm1 : (1 : ℝ) ≤ max 1 CB := le_max_left _ _
  refine ⟨CB * max 1 CB * max Kad 0,
    mul_nonneg (mul_nonneg hCB.le (le_trans zero_le_one hm1)) (le_max_right _ _), ?_⟩
  intro N hN X hX r' t hr' hrt htT φ hφ
  have hN1 : 1 ≤ N := by omega
  have hrT : r' ∈ Set.Icc (0 : ℝ) S.T := ⟨hr', hrt.trans htT⟩
  obtain ⟨L, F, hF0, hlipL, hfr, hLF⟩ := hw N hN1 r' t hr' hrt htT φ hφ
  have hfrac : HasFracTransportBound c.regularity c.integrability
      (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r' t φ) x))
      (Kad * HRS.Whole.sobolevNorm (c.gammaIndex : ℝ) φ) := ⟨L, F, hF0, hlipL, hfr, hLF⟩
  have hK0 : 0 ≤ Kad * HRS.Whole.sobolevNorm (c.gammaIndex : ℝ) φ :=
    le_trans (add_nonneg L.coe_nonneg hF0) hLF
  have hprob := (hS.mean_field.solution N hN1).density r' hrT
  have hρle : ∀ x, S.ρ N r' x ≤ max Λ 1 := fun x => (sa26_rho_le hS hN1 hrT x).trans (le_max_left _ _)
  have hlog : s = 0 → HasLogMoment (HRS.Whole.withDensityReal (S.ρ N r')) Lm :=
    fun _ => hLm (S.ρ N r') hprob (fun x => sa26_weighted_zero hS hN1 hrT x)
  have hb := hB (max Λ 1) (le_max_right _ _) N hN (S.ρ N r') hprob hρle hlog X hX _ _ hfrac
  have hE0 := hC₁e hΛ C₀ (le_trans (le_max_left _ _) hC₀) N hN (S.ρ N r') hprob
    (fun x => sa26_rho_le hS hN1 hrT x) (fun _ => sa26_log_int hS hN1 hrT) X
    (fun ⟨i, j, hij, h⟩ => hij (hX h))
  have ho := hC₂ hΛ C₀ (le_trans (le_max_right _ _) hC₀) N hN1
  have he0 : 0 ≤ c.errorRate N := HRS.MP.RdRem.mrr_eN_nonneg (FieldDensityRd.decSub c) N
  have hsob : 0 ≤ HRS.Whole.sobolevNorm (c.gammaIndex : ℝ) φ := Real.sqrt_nonneg _
  rw [hSs]
  set Fv := rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (S.ρ N r')) with hFv
  have hE' : Fv + oNΛ d s C₀B (max Λ 1) N + CB * c.errorRate N ≤
      max 1 CB * (Fv + oNΛ d s C₀ Λ N + c.errorRate N) := by
    have h1 : Fv + oNΛ d s C₀B (max Λ 1) N ≤ Fv + oNΛ d s C₀ Λ N := by linarith
    have h2 : Fv + oNΛ d s C₀ Λ N ≤ max 1 CB * (Fv + oNΛ d s C₀ Λ N) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hm1) hE0]
    have h3 : CB * c.errorRate N ≤ max 1 CB * c.errorRate N :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) he0
    nlinarith
  have hA0 : 0 ≤ CB * (Kad * HRS.Whole.sobolevNorm (c.gammaIndex : ℝ) φ) := mul_nonneg hCB.le hK0
  have hEE : 0 ≤ Fv + oNΛ d s C₀ Λ N + c.errorRate N := by linarith
  calc |commN d s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r' t φ) x)) X
          (HRS.Whole.withDensityReal (S.ρ N r'))|
      ≤ CB * (Kad * HRS.Whole.sobolevNorm (c.gammaIndex : ℝ) φ) *
        (Fv + oNΛ d s C₀B (max Λ 1) N + CB * c.errorRate N) := hb
    _ ≤ CB * (Kad * HRS.Whole.sobolevNorm (c.gammaIndex : ℝ) φ) *
        (max 1 CB * (Fv + oNΛ d s C₀ Λ N + c.errorRate N)) :=
        mul_le_mul_of_nonneg_left hE' hA0
    _ ≤ CB * (max Kad 0 * HRS.Whole.sobolevNorm (c.gammaIndex : ℝ) φ) *
        (max 1 CB * (Fv + oNΛ d s C₀ Λ N + c.errorRate N)) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (le_trans zero_le_one hm1) hEE)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _) hsob) hCB.le
    _ = CB * max 1 CB * max Kad 0 * HRS.Whole.sobolevNorm (c.gammaIndex : ℝ) φ *
        (Fv + oNΛ d s C₀ Λ N + (FieldDensityRd.decSub c).eN N) := by
        simp only [FieldDensityRd.eN]
        ring

end B5

end HRS.MS.PathFidi
