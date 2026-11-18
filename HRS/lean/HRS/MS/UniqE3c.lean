import HRS.MS.UniqE3b

/-!
# E3 of `UniqPlan.md`, part 3: the cell energy and the energy conversion (C)

`cellEnergy χ Ψ σ w := ⨆_c ∫⁻ ofReal(ς_c^σ w²)`.

* `e3_cover_ball` **(C)**: `∫_{B̄(e,r)} w² ≤ coverN · cellEnergy` (from `FlowBundle.cover_lower`, `ball_cell`).
* `e3_cellEnergy_le`: `cellEnergy (η_ε * u) ≤ N B²` for `LocMass B u` (ε-independent, `ε ≤ 1`).
* `e3_varsigma_grad_sq`: `|∇ς|² ≤ Γ ς` with `Γ` depending only on `χ, Cb, t`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3

variable {d : ℕ}

/-- The sup-energy `⨆_c ∫ ς_c^σ w²` (in `ℝ≥0∞`). -/
def cellEnergy (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (σ : ℝ) (w : Euc d → ℝ) : ℝ≥0∞ :=
  ⨆ c : Euc d, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ σ c x * w x ^ 2)

/-- The multiplicity of `FlowBundle.ball_cell` for a ball of radius `r`. -/
def coverN (d : ℕ) (Cb t r : ℝ) : ℕ :=
  ⌊(2 * ((2 + Real.exp (Cb * t) * r) * (cellScale d : ℝ)) + 1) ^ d⌋₊

theorem e3_le_cellEnergy (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (σ : ℝ) (w : Euc d → ℝ)
    (c : Euc d) : ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ σ c x * w x ^ 2) ≤ cellEnergy χ Ψ σ w :=
  le_iSup (fun c : Euc d => ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ σ c x * w x ^ 2)) c

/-- **(C)** energy conversion: the mass of `w²` on a closed ball is at most `coverN` times the sup-energy. -/
theorem e3_cover_ball {m : ℕ} {Cb t : ℝ} {χ χh : Euc d → ℝ} {b : ℝ → Euc d → Euc d}
    {Ψ : ℝ → Euc d → Euc d} {K : ℝ} (hF : FlowBundle d m Cb t χ χh b Ψ K) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) t) {r : ℝ} (hr : 0 ≤ r) {w : Euc d → ℝ} (hw : Continuous w)
    (e : Euc d) :
    ∫⁻ x in closedBall e r, ENNReal.ofReal (w x ^ 2) ≤
      (coverN d Cb t r : ℝ≥0∞) * cellEnergy χ Ψ σ w := by
  set G : Euc d → ℝ≥0∞ := (closedBall e r).indicator (fun x => ENNReal.ofReal (w x ^ 2)) with hG
  have hGm : Measurable G :=
    (ENNReal.measurable_ofReal.comp (hw.pow 2).measurable).indicator measurableSet_closedBall
  have hlow := hF.cover_lower σ hσ G hGm
  rw [hG, lintegral_indicator measurableSet_closedBall] at hlow
  refine hlow.trans ?_
  set S : Set (Fin d → ℤ) :=
    {z | (closedBall e r ∩ tsupport (varsigma χ Ψ σ (cellPt d z))).Nonempty} with hS
  have hSenc : S.encard ≤ ((coverN d Cb t r : ℕ) : ℕ∞) := hF.ball_cell σ hσ e r hr
  have hSfin : S.Finite := Set.finite_of_encard_le_coe hSenc
  set T : (Fin d → ℤ) → ℝ≥0∞ := fun z =>
    ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ σ (cellPt d z) x) * G x with hT
  have hT0 : ∀ z ∉ hSfin.toFinset, T z = 0 := by
    intro z hz
    have hz' : z ∉ S := by simpa using hz
    have h0 : ∀ x, ENNReal.ofReal (varsigma χ Ψ σ (cellPt d z) x) * G x = 0 := by
      intro x
      by_cases hx : x ∈ closedBall e r
      · have : varsigma χ Ψ σ (cellPt d z) x = 0 := by
          by_contra hne
          exact hz' ⟨x, hx, subset_tsupport _ (Function.mem_support.2 hne)⟩
        simp [this]
      · simp [hG, Set.indicator_of_notMem hx]
    simp [hT, h0]
  have hTE : ∀ z, T z ≤ cellEnergy χ Ψ σ w := by
    intro z
    refine le_trans (lintegral_mono fun x => ?_) (e3_le_cellEnergy χ Ψ σ w (cellPt d z))
    by_cases hx : x ∈ closedBall e r
    · have h0 := (hF.range σ hσ (cellPt d z) x).1
      simp only [hG, Set.indicator_of_mem hx]
      rw [← ENNReal.ofReal_mul h0]
    · simp [hG, Set.indicator_of_notMem hx]
  have hcard : hSfin.toFinset.card ≤ coverN d Cb t r := by
    have h1 : hSfin.toFinset.card = S.ncard := (Set.ncard_eq_toFinset_card S hSfin).symm
    have h2 : (S.ncard : ℕ∞) = S.encard := hSfin.cast_ncard_eq
    have h3 : (S.ncard : ℕ∞) ≤ (coverN d Cb t r : ℕ∞) := h2.trans_le hSenc
    rw [h1]; exact_mod_cast h3
  rw [tsum_eq_sum hT0]
  calc ∑ z ∈ hSfin.toFinset, T z ≤ ∑ z ∈ hSfin.toFinset, cellEnergy χ Ψ σ w :=
        Finset.sum_le_sum fun z _ => hTE z
    _ = (hSfin.toFinset.card : ℝ≥0∞) * cellEnergy χ Ψ σ w := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (coverN d Cb t r : ℝ≥0∞) * cellEnergy χ Ψ σ w :=
        mul_le_mul_left (by exact_mod_cast hcard) _

/-- `cellEnergy (η_ε * u) ≤ N B²` for `LocMass B u`, `0 < ε ≤ 1` (`N` depends only on `d, Cb, t`). -/
theorem e3_cellEnergy_le {m : ℕ} {Cb t : ℝ} {χ χh : Euc d → ℝ} {b : ℝ → Euc d → Euc d}
    {Ψ : ℝ → Euc d → Euc d} {K : ℝ} (hF : FlowBundle d m Cb t χ χh b Ψ K) :
    ∃ N : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (B : ℝ) (u : Euc d → ℝ), LocMass B u →
      ∀ σ ∈ Icc (0 : ℝ) t, cellEnergy χ Ψ σ (moll d ε u) ≤ (N : ℝ≥0∞) * ENNReal.ofReal (B ^ 2) := by
  obtain ⟨N, hN⟩ := moll_mass_le_const d (2 * Real.exp (Cb * t) + 1)
  refine ⟨N, fun ε hε hε1 B u hu σ hσ => iSup_le fun c => ?_⟩
  have hpt : ∀ x, ENNReal.ofReal (varsigma χ Ψ σ c x * moll d ε u x ^ 2) ≤
      (ball (Ψ σ c) (2 * Real.exp (Cb * t) + 1)).indicator
        (fun x => ‖moll d ε u x‖ₑ ^ 2) x := by
    intro x
    by_cases hx : x ∈ ball (Ψ σ c) (2 * Real.exp (Cb * t) + 1)
    · rw [Set.indicator_of_mem hx, enorm_sq_eq]
      refine ENNReal.ofReal_le_ofReal ?_
      exact mul_le_of_le_one_left (sq_nonneg _) (hF.range σ hσ c x).2
    · rw [Set.indicator_of_notMem hx]
      have hx' : x ∉ tsupport (varsigma χ Ψ σ c) := fun h => hx (by
        have := hF.supp σ hσ c h
        rw [mem_closedBall] at this
        rw [mem_ball]; linarith)
      rw [image_eq_zero_of_notMem_tsupport hx']
      simp
  calc ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ σ c x * moll d ε u x ^ 2)
      ≤ ∫⁻ x, (ball (Ψ σ c) (2 * Real.exp (Cb * t) + 1)).indicator
        (fun x => ‖moll d ε u x‖ₑ ^ 2) x := lintegral_mono hpt
    _ = ∫⁻ x in ball (Ψ σ c) (2 * Real.exp (Cb * t) + 1), ‖moll d ε u x‖ₑ ^ 2 :=
        lintegral_indicator measurableSet_ball _
    _ ≤ _ := hN ε hε hε1 B u hu (Ψ σ c)

/-- `|∇ς|² ≤ Γ ς` with `Γ` depending only on `χ, Cb, t`. -/
theorem e3_varsigma_grad_sq {m : ℕ} {Cb t : ℝ} {χ : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d}
    (hχ : IsUlocCutoff χ) (hF : FlowFacts m Cb t Ψ) (hCb : 0 ≤ Cb) :
    ∃ Γ : ℝ, 0 ≤ Γ ∧ ∀ σ ∈ Icc (0 : ℝ) t, ∀ c x : Euc d,
      ‖fderiv ℝ (varsigma χ Ψ σ c) x‖ ^ 2 ≤ Γ * varsigma χ Ψ σ c x := by
  obtain ⟨M, hM⟩ := (hχ.1.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hχ.2.1.fderiv (𝕜 := ℝ))
  set M' : ℝ := max M 0 with hM'
  set Lc : ℝ := Real.exp (Cb * t) with hLc
  have hM'0 : 0 ≤ M' := le_max_right _ _
  refine ⟨4 * (M' * Lc) ^ 2, by positivity, fun σ hσ c x => ?_⟩
  set Φ : Euc d → Euc d := Function.invFun (Ψ σ) with hΦ
  have hΦd : Differentiable ℝ Φ := (hF.contDiff_inv σ hσ).differentiable (by simp)
  have hΦL : ‖fderiv ℝ Φ x‖ ≤ Lc := by
    have hlip : LipschitzWith (Real.exp (Cb * σ)).toNNReal Φ := by
      refine LipschitzWith.of_dist_le_mul fun a a' => ?_
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.exp_pos _).le]
      exact hF.lip_inv σ hσ a a'
    have := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := x)
    refine this.trans ?_
    rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (by nlinarith [hσ.2, hCb])
  set ϑ : Euc d → ℝ := fun y => χ (Φ y - c) with hϑ
  have hf : HasFDerivAt (fun y => Φ y - c) (fderiv ℝ Φ x) x := (hΦd x).hasFDerivAt.sub_const c
  have hg : HasFDerivAt χ (fderiv ℝ χ (Φ x - c)) (Φ x - c) :=
    ((hχ.1.differentiable (by simp)) _).hasFDerivAt
  have hϑ' : HasFDerivAt ϑ ((fderiv ℝ χ (Φ x - c)).comp (fderiv ℝ Φ x)) x := hg.comp x hf
  have hϑL : ‖fderiv ℝ ϑ x‖ ≤ M' * Lc := by
    rw [hϑ'.fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul ((hM (Φ x - c)).trans (le_max_left _ _)) hΦL (norm_nonneg _) hM'0
  have hς : varsigma χ Ψ σ c = fun y => ϑ y ^ 2 := rfl
  have hpow : fderiv ℝ (varsigma χ Ψ σ c) x = (2 * ϑ x) • fderiv ℝ ϑ x := by
    rw [hς, fderiv_fun_pow 2 hϑ'.differentiableAt]
    simp
  rw [hpow, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hς]
  show (2 * ϑ x) ^ 2 * ‖fderiv ℝ ϑ x‖ ^ 2 ≤ 4 * (M' * Lc) ^ 2 * ϑ x ^ 2
  have := pow_le_pow_left₀ (norm_nonneg _) hϑL 2
  nlinarith [sq_nonneg (ϑ x)]

end HRS.MS.UniqE3
