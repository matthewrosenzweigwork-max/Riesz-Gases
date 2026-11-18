import HRS.Commutator.Whole.XLIAux10

/-!
# X-LI part 11: the Bessel-type symbol profiles `(ε² + 4π²|η|²)^{s/2} ρ(η)`
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- a smooth compactly supported function has bounded derivatives -/
lemma bdd_iteratedFDeriv_of_cs {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ)
    (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ η, ‖iteratedFDeriv ℝ n θ η‖ ≤ B := by
  have h1 : Continuous (iteratedFDeriv ℝ n θ) :=
    hθ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have h2 : HasCompactSupport (iteratedFDeriv ℝ n θ) := hcs.iteratedFDeriv n
  obtain ⟨C, hC⟩ := (h1.norm.bounded_above_of_compact_support h2.norm)
  exact ⟨max C 0, le_max_right _ _, fun η => by simpa using (hC η).trans (le_max_left C 0)⟩

lemma SymFam.const {R : ℝ} {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hs : ∀ η : 𝔼, R < ‖η‖ → θ η = 0) :
    SymFam R (fun _ => θ) := by
  have hcs : HasCompactSupport θ := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : 𝔼) R) ?_
    intro η hη
    by_contra h
    exact hη (hs η (by simpa using h))
  choose B hB0 hB using fun n : ℕ => bdd_iteratedFDeriv_of_cs hθ hcs n
  refine ⟨fun _ => hθ, fun _ => hs, ∑ n ∈ Finset.range (d + 2), B n,
    Finset.sum_nonneg fun n _ => hB0 n, fun _ i hi η => ?_⟩
  refine (hB i η).trans ?_
  exact Finset.single_le_sum (f := B) (fun n _ => hB0 n) (by simpa [Nat.lt_succ_iff] using hi)

/-- the Bessel-type profile -/
def thB (s ε : ℝ) (η : 𝔼) : ℂ :=
  (((ε ^ 2 + 4 * Real.pi ^ 2 * ‖η‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * rho η

lemma thBj_contDiff (s : ℝ) : ContDiff ℝ ∞ (fun p : ℝ × 𝔼 => thB s p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1 ^ 2 + 4 * Real.pi ^ 2 * ‖p.2‖ ^ 2 = 0
  · have h2 : ‖p.2‖ = 0 := by
      have h1 : 0 ≤ p.1 ^ 2 := sq_nonneg _
      have h3 : 0 ≤ 4 * Real.pi ^ 2 * ‖p.2‖ ^ 2 := by positivity
      have h4 : 4 * Real.pi ^ 2 * ‖p.2‖ ^ 2 = 0 := by linarith
      have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
      have : ‖p.2‖ ^ 2 = 0 := by
        rcases mul_eq_zero.1 h4 with h | h
        · exact absurd h hpi.ne'
        · exact h
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have hev : (fun q : ℝ × 𝔼 => thB s q.1 q.2) =ᶠ[𝓝 p] fun _ => 0 := by
      have hopen : IsOpen {q : ℝ × 𝔼 | ‖q.2‖ < 1 / 2} :=
        isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
      filter_upwards [hopen.mem_nhds (show ‖p.2‖ < 1 / 2 by rw [h2]; norm_num)] with q hq
      have hq' : ‖q.2‖ < 1 / 2 := hq
      unfold thB
      rw [rho_eq_zero_of_le hq'.le]; simp
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev
  · have h1 : ContDiffAt ℝ ∞ (fun q : ℝ × 𝔼 => q.1 ^ 2 + 4 * Real.pi ^ 2 * ‖q.2‖ ^ 2) p :=
      ((contDiff_fst.pow 2).add (contDiff_const.mul
        ((contDiff_norm_sq ℝ).comp contDiff_snd))).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun q : ℝ × 𝔼 => (q.1 ^ 2 + 4 * Real.pi ^ 2 * ‖q.2‖ ^ 2) ^ (s / 2)) p :=
      h1.rpow_const_of_ne hp
    have h3 : ContDiffAt ℝ ∞ (fun q : ℝ × 𝔼 =>
        (((q.1 ^ 2 + 4 * Real.pi ^ 2 * ‖q.2‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p h2
    exact h3.mul ((rho_contDiff.comp contDiff_snd).contDiffAt)

lemma thB_contDiff (s ε : ℝ) : ContDiff ℝ ∞ (thB s ε : 𝔼 → ℂ) := by
  have h : (thB s ε : 𝔼 → ℂ) = (fun p : ℝ × 𝔼 => thB s p.1 p.2) ∘ (fun η : 𝔼 => (ε, η)) := rfl
  rw [h]
  exact (thBj_contDiff s).comp ((contDiff_const (c := ε)).prodMk (contDiff_id (𝕜 := ℝ) (E := 𝔼)))

lemma thB_supp (s ε : ℝ) {η : 𝔼} (h : 2 < ‖η‖) : thB s ε η = 0 := by
  unfold thB
  rw [rho_eq_zero_of_ge h.le]; simp

/-- uniform bounds for the derivatives of `thB s ε` for `ε ∈ [0,4]` -/
lemma thB_bound (s : ℝ) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 4 → ∀ η : 𝔼, ‖iteratedFDeriv ℝ n (thB s ε : 𝔼 → ℂ) η‖ ≤ B := by
  set g : ℝ × 𝔼 → ℂ := fun p => thB s p.1 p.2 with hg
  have hgd : ContDiff ℝ ∞ g := thBj_contDiff s
  have hK : IsCompact (Set.Icc (0 : ℝ) 4 ×ˢ closedBall (0 : 𝔼) 2) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcont : Continuous (iteratedFDeriv ℝ n g) :=
    hgd.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨max C 0, hC0, fun ε hε0 hε4 η => ?_⟩
  by_cases hη : ‖η‖ ≤ 2
  · have e : (thB s ε : 𝔼 → ℂ) = (fun z : ℝ × 𝔼 => g ((ε, (0 : 𝔼)) + z)) ∘
        (ContinuousLinearMap.inr ℝ ℝ 𝔼) := by
      funext η'
      simp [hg]
    have hfd : ContDiff ℝ ∞ (fun z : ℝ × 𝔼 => g ((ε, (0 : 𝔼)) + z)) :=
      hgd.comp (contDiff_const.add contDiff_id)
    rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hfd η (by exact_mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h1 : ∏ i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ 𝔼‖ ≤ 1 := by
      rw [Finset.prod_const]
      exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ ℝ 𝔼)
    have h2 : ‖iteratedFDeriv ℝ n (fun z : ℝ × 𝔼 => g ((ε, (0 : 𝔼)) + z))
        (ContinuousLinearMap.inr ℝ ℝ 𝔼 η)‖ ≤ max C 0 := by
      rw [iteratedFDeriv_comp_add_left]
      have hmem : (ε, (0 : 𝔼)) + (ContinuousLinearMap.inr ℝ ℝ 𝔼 η) ∈
          Set.Icc (0 : ℝ) 4 ×ˢ closedBall (0 : 𝔼) 2 := by
        refine ⟨⟨by simpa using hε0, by simpa using hε4⟩, ?_⟩
        simpa using hη
      exact (hC _ hmem).trans (le_max_left _ _)
    calc _ ≤ ‖iteratedFDeriv ℝ n (fun z : ℝ × 𝔼 => g ((ε, (0 : 𝔼)) + z))
          (ContinuousLinearMap.inr ℝ ℝ 𝔼 η)‖ * ∏ i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ 𝔼‖ := by
          exact le_rfl
      _ ≤ max C 0 * 1 := by gcongr
      _ = max C 0 := mul_one _
  · push Not at hη
    have : (thB s ε : 𝔼 → ℂ) =ᶠ[𝓝 η] fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hη] with y hy
      exact thB_supp s ε hy
    have h2 := (this.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
    rw [h2, iteratedFDeriv_fun_zero]
    simpa using hC0

/-- pointwise domination of the profile by `ρ` -/
lemma thB_norm_le (s : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε4 : ε ≤ 4) (η : 𝔼) :
    ‖thB s ε η‖ ≤ (200 : ℝ) ^ |s| * ‖rho η‖ := by
  by_cases hρ : rho η = 0
  · simp [thB, hρ]
  · have hlo : 1 / 2 < ‖η‖ := by
      by_contra h; exact hρ (rho_eq_zero_of_le (not_lt.1 h))
    have hhi : ‖η‖ < 2 := by
      by_contra h; exact hρ (rho_eq_zero_of_ge (not_lt.1 h))
    unfold thB
    rw [norm_mul, Complex.norm_real]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hpi3 := Real.pi_gt_three
    have hpi4 := Real.pi_lt_d2
    set x := ε ^ 2 + 4 * Real.pi ^ 2 * ‖η‖ ^ 2 with hx
    have hx1 : 1 ≤ x := by
      have h1 : 1 / 4 < ‖η‖ ^ 2 := by nlinarith
      have h2 : 9 < Real.pi ^ 2 := by nlinarith
      have h3 : 0 ≤ ε ^ 2 := sq_nonneg _
      nlinarith
    have hx2 : x ≤ 200 := by
      have h1 : ‖η‖ ^ 2 < 4 := by nlinarith
      have h2 : Real.pi ^ 2 < 10 := by nlinarith
      have h3 : ε ^ 2 ≤ 16 := by nlinarith
      have h4 : 0 ≤ ‖η‖ ^ 2 := sq_nonneg _
      have h5 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
      nlinarith [mul_pos (by norm_num : (0:ℝ) < 4) (sq_pos_of_pos (by linarith : 0 < Real.pi))]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    rcases le_total 0 s with hs | hs
    · calc x ^ (s / 2) ≤ (200 : ℝ) ^ (s / 2) := Real.rpow_le_rpow (by linarith) hx2 (by linarith)
        _ ≤ (200 : ℝ) ^ |s| := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          rw [abs_of_nonneg hs]; linarith
    · calc x ^ (s / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
        _ ≤ (200 : ℝ) ^ |s| := Real.one_le_rpow (by norm_num) (abs_nonneg _)

lemma thB_rep (s ε : ℝ) (η : 𝔼) : rhoT η * thB s ε η = thB s ε η := by
  unfold thB
  rw [mul_left_comm, rhoT_mul_rho]

/-- the clamped scale parameter -/
def epsj (j : ℤ) : ℝ := min (((2 : ℝ) ^ j)⁻¹) 4

lemma epsj_nonneg (j : ℤ) : 0 ≤ epsj j :=
  le_min (inv_nonneg.2 (zpow_pos (by norm_num) j).le) (by norm_num)

lemma epsj_le (j : ℤ) : epsj j ≤ 4 := min_le_right _ _

lemma epsj_eq {j : ℤ} (hj : -2 ≤ j) : epsj j = ((2 : ℝ) ^ j)⁻¹ := by
  unfold epsj
  refine min_eq_left ?_
  have : (2 : ℝ) ^ (-2 : ℤ) ≤ (2 : ℝ) ^ j := zpow_le_zpow_right₀ (by norm_num) hj
  rw [inv_le_comm₀ (zpow_pos (by norm_num) j) (by norm_num)]
  have h2 : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
  rw [h2] at this
  linarith

/-- the family of Bessel-type profiles `j ↦ thB s (ε_j)` -/
def Ths (s : ℝ) (j : ℤ) : 𝔼 → ℂ := thB s (epsj j)

lemma symFam_Ths (s : ℝ) : SymFam 2 (Ths s : ℤ → 𝔼 → ℂ) := by
  choose B hB0 hB using fun n : ℕ => thB_bound (d := d) s n
  refine ⟨fun j => thB_contDiff s _, fun j η h => thB_supp s _ h, ∑ n ∈ Finset.range (d + 2), B n,
    Finset.sum_nonneg fun n _ => hB0 n, fun j i hi η => ?_⟩
  refine (hB i _ (epsj_nonneg j) (epsj_le j) η).trans ?_
  exact Finset.single_le_sum (f := B) (fun n _ => hB0 n) (by simpa [Nat.lt_succ_iff] using hi)

lemma symFam_rhoT : SymFam 4 (fun _ => (rhoT : 𝔼 → ℂ)) :=
  SymFam.const rhoT_contDiff (fun η h => rhoT_eq_zero_of_ge h.le)

lemma symFam_rho : SymFam 2 (fun _ => (rho : 𝔼 → ℂ)) :=
  SymFam.const rho_contDiff (fun η h => rho_eq_zero_of_ge h.le)

lemma Ths_sq_sum (s : ℝ) (ξ : 𝔼) :
    ∑' j : ℤ, ‖Ths s j (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 ≤ ENNReal.ofReal ((200 : ℝ) ^ |s|) ^ 2 * 2 := by
  calc ∑' j : ℤ, ‖Ths s j (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2
      ≤ ∑' j : ℤ, ENNReal.ofReal ((200 : ℝ) ^ |s|) ^ 2 * ‖rho (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        have h := thB_norm_le s (epsj_nonneg j) (epsj_le j) (((2 : ℝ) ^ j)⁻¹ • ξ)
        have h' : ‖Ths s j (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ≤
            ENNReal.ofReal ((200 : ℝ) ^ |s|) * ‖rho (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm (rho _), ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal h
        calc ‖Ths s j (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2
            ≤ (ENNReal.ofReal ((200 : ℝ) ^ |s|) * ‖rho (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ) ^ 2 := by gcongr
          _ = _ := by rw [mul_pow]
    _ = ENNReal.ofReal ((200 : ℝ) ^ |s|) ^ 2 * ∑' j : ℤ, ‖rho (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal ((200 : ℝ) ^ |s|) ^ 2 * 2 := by
        gcongr
        exact rho_sq_sum_le ξ

/-- the Bessel-type Littlewood–Paley family is a reproducing LP family -/
lemma isLPRep_Ths (s : ℝ) : IsLPRep (fun j => dK (Ths s : ℤ → 𝔼 → ℂ) j) :=
  isLPRep_dK (symFam_Ths s) (symFam_rhoT) (fun j ξ => thB_rep s (epsj j) ξ)
    (M := ENNReal.ofReal ((200 : ℝ) ^ |s|) ^ 2 * 2)
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (by simp)) (Ths_sq_sum s)

end HRS.Commutator.Whole.XLI
