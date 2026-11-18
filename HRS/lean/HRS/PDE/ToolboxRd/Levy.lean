import HRS.PDE.ToolboxRd.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Lemma C.3 (ii) on `ℝ^d`: construction of the Lévy kernel

Package LEVY of the `ℝ^d` case.  For a symbol `m` with `IsHomogSymbol θ m`, `0 < θ < 2`, we construct
`𝔨 = levyK θ m`, the dyadic (Littlewood–Paley) sum over **all** `j ∈ ℤ`
`𝔨(z) = -∑_{j∈ℤ} 2^{j(θ+d)} G(2^j z)`, `G = 𝓕 (m ψ)` Schwartz, `ψ(ξ) = χ(ξ) - χ(2ξ)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff FourierTransform

namespace HRS.PDE.ToolboxRd.LevyAux

variable {d : ℕ}

/-! ### (a) The dyadic scale and the Littlewood–Paley partition -/

/-- the dyadic scale `2^j`, `j ∈ ℤ` -/
def lam (j : ℤ) : ℝ := (2 : ℝ) ^ (j : ℝ)

theorem lam_pos (j : ℤ) : 0 < lam j := Real.rpow_pos_of_pos (by norm_num) _

theorem lam_add (i j : ℤ) : lam (i + j) = lam i * lam j := by
  unfold lam; rw [Int.cast_add, Real.rpow_add (by norm_num)]

theorem lam_zero : lam 0 = 1 := by simp [lam]

theorem lam_one : lam 1 = 2 := by simp [lam]

theorem lam_neg (j : ℤ) : lam (-j) = (lam j)⁻¹ := by
  unfold lam; rw [Int.cast_neg, Real.rpow_neg (by norm_num)]

theorem lam_rpow (j : ℤ) (x : ℝ) : (lam j) ^ x = (2 : ℝ) ^ ((j : ℝ) * x) := by
  unfold lam; rw [← Real.rpow_mul (by norm_num)]

theorem lam_rpow_add (j : ℤ) (x y : ℝ) : (lam j) ^ (x + y) = (lam j) ^ x * (lam j) ^ y :=
  Real.rpow_add (lam_pos j) x y

theorem lam_rpow_natCast (j : ℤ) (n : ℕ) : (lam j) ^ (n : ℝ) = (lam j) ^ n :=
  Real.rpow_natCast _ _

theorem lam_mono {i j : ℤ} (h : i ≤ j) : lam i ≤ lam j :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast h)

theorem lam_succ (j : ℤ) : lam (j + 1) = 2 * lam j := by
  rw [lam_add, lam_one]; ring

/-- the bump (`≡ 1` on the unit ball, supported in the ball of radius 2) -/
def bumpR (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- the radial cutoff `χ` -/
def chiR (d : ℕ) (ξ : Euc d) : ℝ := bumpR d ξ

theorem contDiff_chiR : ContDiff ℝ ∞ (chiR d) := (bumpR d).contDiff

theorem chiR_one {ξ : Euc d} (h : ‖ξ‖ ≤ 1) : chiR d ξ = 1 :=
  ContDiffBump.one_of_mem_closedBall (bumpR d) (by simpa [bumpR] using h)

theorem chiR_zero {ξ : Euc d} (h : 2 ≤ ‖ξ‖) : chiR d ξ = 0 :=
  ContDiffBump.zero_of_le_dist (bumpR d) (by simpa [bumpR] using h)

theorem chiR_neg (ξ : Euc d) : chiR d (-ξ) = chiR d ξ := ContDiffBump.neg (bumpR d) ξ

/-- `ψ(ξ) = χ(ξ) - χ(2ξ)` -/
def psiR (d : ℕ) (ξ : Euc d) : ℝ := chiR d ξ - chiR d ((2 : ℝ) • ξ)

theorem contDiff_psiR : ContDiff ℝ ∞ (psiR d) :=
  contDiff_chiR.sub (contDiff_chiR.comp (contDiff_id.const_smul (2 : ℝ)))

theorem psiR_neg (ξ : Euc d) : psiR d (-ξ) = psiR d ξ := by
  unfold psiR
  rw [smul_neg, chiR_neg, chiR_neg]

theorem psiR_small {ξ : Euc d} (h : ‖ξ‖ ≤ 1 / 2) : psiR d ξ = 0 := by
  unfold psiR
  rw [chiR_one (by linarith), chiR_one, sub_self]
  rw [norm_smul]; simp; linarith

theorem psiR_large {ξ : Euc d} (h : 2 ≤ ‖ξ‖) : psiR d ξ = 0 := by
  unfold psiR
  rw [chiR_zero h, chiR_zero, sub_self]
  rw [norm_smul]; simp; linarith

/-- the telescoping identity `ψ(2^{-j}ξ) = χ(2^{-j}ξ) - χ(2^{-(j-1)}ξ)` -/
theorem psiR_lam (ξ : Euc d) (j : ℤ) :
    psiR d (lam (-j) • ξ) = chiR d (lam (-j) • ξ) - chiR d (lam (-(j - 1)) • ξ) := by
  unfold psiR
  have : (2 : ℝ) • lam (-j) • ξ = lam (-(j - 1)) • ξ := by
    rw [smul_smul]
    congr 1
    have : -(j - 1) = -j + 1 := by ring
    rw [this, lam_succ]
  rw [this]

theorem hasSum_psiR {ξ : Euc d} (hξ : ξ ≠ 0) :
    HasSum (fun j : ℤ => psiR d (lam (-j) • ξ)) 1 := by
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  -- choose `N` with `2^N ≥ ‖ξ‖` and `2^N ‖ξ‖ ≥ 2`
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (max ‖ξ‖ (2 / ‖ξ‖)) (by norm_num : (1 : ℝ) < 2)
  have hlamN : lam (N : ℤ) = (2 : ℝ) ^ N := by
    unfold lam; rw [Int.cast_natCast, Real.rpow_natCast]
  have h1 : ‖ξ‖ ≤ lam (N : ℤ) := by rw [hlamN]; exact le_trans (le_max_left _ _) hN.le
  have h2 : 2 / ‖ξ‖ ≤ lam (N : ℤ) := by rw [hlamN]; exact le_trans (le_max_right _ _) hN.le
  have h2' : 2 ≤ lam (N : ℤ) * ‖ξ‖ := by
    rw [div_le_iff₀ hpos] at h2; linarith
  have hnorm : ∀ j : ℤ, ‖lam (-j) • ξ‖ = lam (-j) * ‖ξ‖ := by
    intro j; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lam_pos _)]
  -- the support is inside `[-N, N]`
  let s : Finset ℤ := (Finset.range (2 * N + 1)).image (fun i : ℕ => (i : ℤ) - N)
  have hz : ∀ j ∉ s, psiR d (lam (-j) • ξ) = 0 := by
    intro j hj
    have hj' : j < -(N : ℤ) ∨ (N : ℤ) < j := by
      by_contra hcon
      push Not at hcon
      apply hj
      simp only [s, Finset.mem_image, Finset.mem_range]
      refine ⟨(j + N).toNat, ?_, ?_⟩ <;> omega
    rcases hj' with hj' | hj'
    · apply psiR_large
      rw [hnorm]
      have : lam (N + 1 : ℤ) ≤ lam (-j) := lam_mono (by omega)
      rw [lam_succ] at this
      have : 2 ≤ lam (-j) * ‖ξ‖ := by nlinarith
      linarith
    · apply psiR_small
      rw [hnorm]
      have : lam (-j) ≤ lam (-((N : ℤ) + 1)) := lam_mono (by omega)
      rw [lam_neg ((N : ℤ) + 1), lam_succ] at this
      have h3 : lam (-j) * ‖ξ‖ ≤ (2 * lam (N : ℤ))⁻¹ * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right this hpos.le
      have h4 : (2 * lam (N : ℤ))⁻¹ * ‖ξ‖ ≤ 1 / 2 := by
        rw [inv_mul_le_iff₀ (by have := lam_pos (N : ℤ); positivity)]
        nlinarith
      linarith
  have hsum : HasSum (fun j : ℤ => psiR d (lam (-j) • ξ)) (∑ j ∈ s, psiR d (lam (-j) • ξ)) :=
    hasSum_sum_of_ne_finset_zero hz
  have hinj : Function.Injective (fun i : ℕ => (i : ℤ) - N) := by
    intro a b h; simp only [sub_left_inj] at h; exact_mod_cast h
  have hval : ∑ j ∈ s, psiR d (lam (-j) • ξ) = 1 := by
    simp only [s]
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    have : ∀ i : ℕ, psiR d (lam (-((i : ℤ) - N)) • ξ)
        = (fun i : ℕ => chiR d (lam (-((i : ℤ) - N - 1)) • ξ)) (i + 1)
          - (fun i : ℕ => chiR d (lam (-((i : ℤ) - N - 1)) • ξ)) i := by
      intro i
      rw [psiR_lam]
      simp only [Nat.cast_add, Nat.cast_one]
      have e1 : ((i : ℤ) + 1 - N - 1) = (i : ℤ) - N := by ring
      have e2 : ((i : ℤ) - N - 1) = (i : ℤ) - N - 1 := rfl
      rw [e1]
    simp_rw [this]
    rw [Finset.sum_range_sub (fun i : ℕ => chiR d (lam (-((i : ℤ) - N - 1)) • ξ))]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
      zero_sub]
    have e3 : (2 * (N : ℤ) + 1 - N - 1) = N := by ring
    rw [e3]
    have e4 : -(-(N : ℤ) - 1) = (N : ℤ) + 1 := by ring
    rw [e4]
    have a1 : chiR d (lam (-(N : ℤ)) • ξ) = 1 := by
      apply chiR_one
      rw [hnorm, lam_neg]
      rw [inv_mul_le_iff₀ (lam_pos _)]; linarith
    have a2 : chiR d (lam ((N : ℤ) + 1) • ξ) = 0 := by
      apply chiR_zero
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lam_pos _), lam_succ]
      nlinarith
    rw [a1, a2]; ring
  rw [hval] at hsum
  exact hsum


theorem inv_formula (P : SchwartzMap (Euc d) ℂ) (η : Euc d) :
    P η = ∫ v : Euc d, Complex.exp (↑(2 * Real.pi * inner ℝ v η) * Complex.I) • (𝓕 P : SchwartzMap (Euc d) ℂ) v := by
  have h : (𝓕⁻ (𝓕 P) : SchwartzMap (Euc d) ℂ) = P := FourierPair.fourierInv_fourier_eq P
  have h2 := congrArg (fun f : SchwartzMap (Euc d) ℂ => f η) h
  rw [← h2, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']

theorem integrable_phase_smul (H : SchwartzMap (Euc d) ℂ) (η : Euc d) :
    Integrable (fun v : Euc d => Complex.exp (↑(2 * Real.pi * inner ℝ v η) * Complex.I) • H v) := by
  refine (H.integrable (μ := volume)).norm.mono' ?_ (ae_of_all _ fun v => ?_)
  · have : Continuous (fun v : Euc d => Complex.exp (↑(2 * Real.pi * inner ℝ v η) * Complex.I) • H v) := by
      have := H.continuous
      fun_prop
    exact this.aestronglyMeasurable
  · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- cos-form of Fourier inversion for an even function -/
theorem cos_inversion (P : SchwartzMap (Euc d) ℂ) (hP : ∀ ξ, P (-ξ) = P ξ) (η : Euc d) :
    P η = ∫ v : Euc d, ((Real.cos (2 * Real.pi * inner ℝ v η) : ℝ) : ℂ) * (𝓕 P : SchwartzMap (Euc d) ℂ) v := by
  let H : SchwartzMap (Euc d) ℂ := 𝓕 P
  have h1 := inv_formula P η
  have h2 := inv_formula P (-η)
  rw [hP] at h2
  have h3 : P η + P η = ∫ v : Euc d, (2 * ((Real.cos (2 * Real.pi * inner ℝ v η) : ℝ) : ℂ)) * H v := by
    calc P η + P η = (∫ v : Euc d, Complex.exp (↑(2 * Real.pi * inner ℝ v η) * Complex.I) • H v)
        + ∫ v : Euc d, Complex.exp (↑(2 * Real.pi * inner ℝ v (-η)) * Complex.I) • H v := by
          rw [← h1, ← h2]
      _ = _ := ?_
    rw [← integral_add (integrable_phase_smul H η) (integrable_phase_smul H (-η))]
    congr 1; ext v
    simp only [inner_neg_right, smul_eq_mul]
    rw [Complex.ofReal_cos]
    rw [Complex.cos]
    push_cast
    ring_nf
  have h4 : ∫ v : Euc d, (2 * ((Real.cos (2 * Real.pi * inner ℝ v η) : ℝ) : ℂ)) * H v
      = 2 * ∫ v : Euc d, ((Real.cos (2 * Real.pi * inner ℝ v η) : ℝ) : ℂ) * H v := by
    rw [← integral_const_mul]; congr 1; ext v; ring
  rw [h4] at h3
  have : (2 : ℂ) * P η = 2 * ∫ v : Euc d, ((Real.cos (2 * Real.pi * inner ℝ v η) : ℝ) : ℂ) * H v := by
    rw [← h3]; ring
  exact mul_left_cancel₀ (by norm_num) this


/-- `Φ_ℝ = m ψ` -/
def PhiR (m : Euc d → ℝ) (ξ : Euc d) : ℝ := m ξ * psiR d ξ

/-- the complex-valued profile `Φ` -/
def PhiC (m : Euc d → ℝ) (ξ : Euc d) : ℂ := ((PhiR m ξ : ℝ) : ℂ)

theorem PhiR_neg {m : Euc d → ℝ} (he : ∀ ξ, m (-ξ) = m ξ) (ξ : Euc d) : PhiR m (-ξ) = PhiR m ξ := by
  simp [PhiR, he, psiR_neg]

theorem PhiR_large (m : Euc d → ℝ) {ξ : Euc d} (h : 2 ≤ ‖ξ‖) : PhiR m ξ = 0 := by
  simp [PhiR, psiR_large h]

theorem PhiR_zero (m : Euc d → ℝ) : PhiR m 0 = 0 := by
  simp [PhiR, psiR_small (ξ := (0 : Euc d)) (by simp)]

theorem contDiff_PhiR {m : Euc d → ℝ} (hsm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0}) :
    ContDiff ℝ ∞ (PhiR m) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst hξ
    have hev : PhiR m =ᶠ[𝓝 (0 : Euc d)] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : Euc d) (by norm_num : (0 : ℝ) < 1 / 2)] with ξ hξ
      have : ‖ξ‖ ≤ 1 / 2 := by rw [mem_ball_zero_iff] at hξ; exact hξ.le
      simp [PhiR, psiR_small this]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact (hsm.contDiffAt (isOpen_ne.mem_nhds hξ)).mul contDiff_psiR.contDiffAt

theorem contDiff_PhiC {m : Euc d → ℝ} (hsm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0}) :
    ContDiff ℝ ∞ (PhiC m) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_PhiR hsm)

theorem hasCompactSupport_PhiC (m : Euc d → ℝ) : HasCompactSupport (PhiC m) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 2) fun ξ hξ => ?_
  have : 2 ≤ ‖ξ‖ ∨ ‖ξ‖ < 2 := le_or_gt _ _
  rcases this with h | h
  · simp [PhiC, PhiR_large m h]
  · exact absurd (by simpa using h.le) hξ

/-- `Φ` as a Schwartz function -/
def PhiS {m : Euc d → ℝ} (hsm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0}) : SchwartzMap (Euc d) ℂ :=
  (hasCompactSupport_PhiC m).toSchwartzMap (contDiff_PhiC hsm)

theorem PhiS_apply {m : Euc d → ℝ} (hsm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0}) (ξ : Euc d) :
    PhiS hsm ξ = ((PhiR m ξ : ℝ) : ℂ) := rfl

/-- the real profile `G = Re 𝓕 Φ`, a Schwartz function -/
def Gfun (m : Euc d → ℝ) (w : Euc d) : ℝ := (𝓕 (PhiC m) w).re

/-- `G` as a real Schwartz function -/
def GS {m : Euc d → ℝ} (hsm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0}) : SchwartzMap (Euc d) ℝ :=
  (𝓕 (PhiS hsm)).postcompCLM (Complex.reCLM)

theorem GS_apply {m : Euc d → ℝ} (hsm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0}) (w : Euc d) :
    GS hsm w = Gfun m w := by
  simp only [GS, SchwartzMap.postcompCLM_apply, Complex.reCLM_apply, Gfun]
  rw [SchwartzMap.fourier_coe]
  rfl

theorem Gfun_neg {m : Euc d → ℝ} (he : ∀ ξ, m (-ξ) = m ξ) (w : Euc d) : Gfun m (-w) = Gfun m w := by
  have h1 : (PhiC m) ∘ (LinearIsometryEquiv.neg ℝ (E := Euc d)) = PhiC m := by
    funext ξ; simp [PhiC, PhiR_neg he]
  have := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := Euc d)) (PhiC m) w
  rw [h1] at this
  simp only [Gfun]
  rw [this]
  rfl

theorem Gfun_cos {m : Euc d → ℝ} (hsm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0}) (he : ∀ ξ, m (-ξ) = m ξ)
    (η : Euc d) :
    ∫ w, Gfun m w * Real.cos (2 * Real.pi * inner ℝ η w) = PhiR m η := by
  have h := cos_inversion (PhiS hsm) (fun ξ => by simp [PhiS_apply, PhiR_neg he]) η
  have h2 := congrArg Complex.re h
  rw [PhiS_apply, Complex.ofReal_re] at h2
  rw [h2]
  have hint : Integrable (fun v : Euc d => ((Real.cos (2 * Real.pi * inner ℝ v η) : ℝ) : ℂ) *
      (𝓕 (PhiS hsm) : SchwartzMap (Euc d) ℂ) v) := by
    refine ((𝓕 (PhiS hsm) : SchwartzMap (Euc d) ℂ).integrable (μ := volume)).norm.mono' ?_ (ae_of_all _ fun v => ?_)
    · have := (𝓕 (PhiS hsm) : SchwartzMap (Euc d) ℂ).continuous
      exact (by fun_prop : Continuous (fun v : Euc d => ((Real.cos (2 * Real.pi * inner ℝ v η) : ℝ) : ℂ) *
        (𝓕 (PhiS hsm) : SchwartzMap (Euc d) ℂ) v)).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  congr 1; ext w
  rw [real_inner_comm]
  have : (𝓕 (PhiS hsm) : SchwartzMap (Euc d) ℂ) w = 𝓕 (PhiC m) w := by
    rw [SchwartzMap.fourier_coe]; rfl
  rw [this, Complex.re_ofReal_mul, Gfun, mul_comm]



universe u


/-- locally uniform summable bounds on all the derivatives of a family on `U` -/
def LocSummable {ι : Type*} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (U : Set E) (f : ι → E → F) : Prop :=
  ∀ x₀ ∈ U, ∃ s : Set E, IsOpen s ∧ IsPreconnected s ∧ x₀ ∈ s ∧ s ⊆ U ∧ ∀ k : ℕ, ∃ v : ι → ℝ,
    Summable v ∧ ∀ i, ∀ x ∈ s, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v i

theorem hasFDerivAt_tsum_local {ι : Type*} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {U : Set E}
    {f : ι → E → F} (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hloc : LocSummable U f) {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∑' i, f i y) (∑' i, fderiv ℝ (f i) x) x := by
  obtain ⟨s, hs, hs', hxs, hsU, hk⟩ := hloc x hx
  obtain ⟨v0, hv0, hb0⟩ := hk 0
  obtain ⟨v1, hv1, hb1⟩ := hk 1
  refine hasFDerivAt_tsum_of_isPreconnected hv1 hs hs' (f' := fun i y => fderiv ℝ (f i) y)
    (fun i y _ => ((hf i).differentiable (by simp)).differentiableAt.hasFDerivAt) (fun i y hy => ?_)
    hxs ?_ hxs
  · simpa using hb1 i y hy
  · refine Summable.of_norm_bounded hv0 fun i => ?_
    simpa using hb0 i x hxs

theorem contDiffOn_tsum_local {ι : Type*} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) :
    ∀ (n : ℕ) (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : ι → E → F), (∀ i, ContDiff ℝ ∞ (f i)) → LocSummable U f →
      ContDiffOn ℝ n (fun x => ∑' i, f i x) U := by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ f hf hloc
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun x hx => (hasFDerivAt_tsum_local hf hloc hx).continuousAt.continuousWithinAt
  | succ n ih =>
    intro F _ _ _ f hf hloc
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hasFDerivAt_tsum_local hf hloc hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have hf' : ∀ i, ContDiff ℝ ∞ (fderiv ℝ (f i)) := fun i => by
      have := (hf i).fderiv_right (m := ∞) (by rw [← ENat.coe_top_add_one]; rfl)
      exact this
    have hloc' : LocSummable U (fun i => fderiv ℝ (f i)) := by
      intro x₀ hx₀
      obtain ⟨s, hs, hs', hxs, hsU, hk⟩ := hloc x₀ hx₀
      refine ⟨s, hs, hs', hxs, hsU, fun k => ?_⟩
      obtain ⟨v, hv, hb⟩ := hk (k + 1)
      exact ⟨v, hv, fun i x hx => by rw [norm_iteratedFDeriv_fderiv]; exact hb i x hx⟩
    refine (ih (E →L[ℝ] F) (fun i => fderiv ℝ (f i)) hf' hloc').congr fun x hx => ?_
    exact (hasFDerivAt_tsum_local hf hloc hx).fderiv

theorem contDiffOn_infty_tsum_local {ι : Type*} {E F : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {U : Set E}
    (hU : IsOpen U) {f : ι → E → F} (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hloc : LocSummable U f) :
    ContDiffOn ℝ ∞ (fun x => ∑' i, f i x) U :=
  contDiffOn_infty.2 fun n => contDiffOn_tsum_local hU n F f hf hloc



/-! ### (c) The dyadic sum for a Schwartz profile -/

theorem lam_rpow_zpow (j : ℤ) (x : ℝ) : (lam j) ^ x = ((2 : ℝ) ^ x) ^ j := by
  rw [lam_rpow, mul_comm, Real.rpow_mul_intCast (by norm_num)]

theorem summable_dyadic_min {p q c₁ c₂ : ℝ} (hp : 0 < p) (hq : 0 < q) (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂) :
    Summable (fun j : ℤ => min (c₁ * lam j ^ p) (c₂ * lam j ^ (-q))) := by
  have hnn : ∀ j : ℤ, 0 ≤ min (c₁ * lam j ^ p) (c₂ * lam j ^ (-q)) := fun j =>
    le_min (mul_nonneg h1 (Real.rpow_nonneg (lam_pos j).le _))
      (mul_nonneg h2 (Real.rpow_nonneg (lam_pos j).le _))
  refine Summable.of_nat_of_neg ?_ ?_
  · have hr : (2 : ℝ) ^ (-q) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hg : Summable (fun n : ℕ => c₂ * ((2 : ℝ) ^ (-q)) ^ n) :=
      (summable_geometric_of_lt_one (by positivity) hr).mul_left c₂
    refine Summable.of_nonneg_of_le (fun n => hnn _) (fun n => ?_) hg
    refine (min_le_right _ _).trans (le_of_eq ?_)
    rw [lam_rpow_zpow, zpow_natCast]
  · have hr : (2 : ℝ) ^ (-p) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hg : Summable (fun n : ℕ => c₁ * ((2 : ℝ) ^ (-p)) ^ n) :=
      (summable_geometric_of_lt_one (by positivity) hr).mul_left c₁
    refine Summable.of_nonneg_of_le (fun n => hnn _) (fun n => ?_) hg
    refine (min_le_left _ _).trans (le_of_eq ?_)
    rw [lam_rpow_zpow, zpow_neg, ← inv_zpow, ← Real.rpow_neg (by norm_num), zpow_natCast]

/-- the `j`-th dyadic piece `2^{j(θ+d)} G(2^j z)` -/
def kterm (G : SchwartzMap (Euc d) ℝ) (θ : ℝ) (j : ℤ) (z : Euc d) : ℝ :=
  lam j ^ (θ + d) * G (lam j • z)

theorem contDiff_kterm (G : SchwartzMap (Euc d) ℝ) (θ : ℝ) (j : ℤ) : ContDiff ℝ ∞ (kterm G θ j) := by
  unfold kterm
  exact contDiff_const.mul ((G.smooth ⊤).comp (contDiff_id.const_smul (lam j)))

theorem norm_iteratedFDeriv_kterm (G : SchwartzMap (Euc d) ℝ) (θ : ℝ) (k : ℕ) (j : ℤ) (z : Euc d) :
    ‖iteratedFDeriv ℝ k (kterm G θ j) z‖ =
      lam j ^ (θ + d) * (lam j ^ k * ‖iteratedFDeriv ℝ k G (lam j • z)‖) := by
  have h1 : kterm G θ j = (lam j ^ (θ + d)) • (fun z => G (lam j • z)) := by
    funext z; simp [kterm]
  have hc : ContDiff ℝ ∞ (fun z : Euc d => G (lam j • z)) :=
    (G.smooth ⊤).comp (contDiff_id.const_smul (lam j))
  rw [h1, iteratedFDeriv_const_smul_apply (hc.contDiffAt.of_le (mod_cast le_top)), iteratedFDeriv_comp_const_smul _ ((G.smooth ⊤).of_le (mod_cast le_top))]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (lam_pos j), abs_pow]
  rw [abs_of_pos (Real.rpow_pos_of_pos (lam_pos j) _)]


/-- locally uniform summable bounds for the derivatives of the pieces -/
theorem dyadic_bound (G : SchwartzMap (Euc d) ℝ) {θ : ℝ} (ha : 0 < θ + d) (k : ℕ) {r : ℝ}
    (hr : 0 < r) :
    ∃ v : ℤ → ℝ, Summable v ∧ ∀ (j : ℤ) (z : Euc d), r ≤ ‖z‖ →
      ‖iteratedFDeriv ℝ k (kterm G θ j) z‖ ≤ v j := by
  set N : ℕ := ⌈θ + d + k⌉₊ + 1 with hN
  have hNk : θ + d + k + 1 ≤ N := by
    have := Nat.le_ceil (θ + d + k)
    rw [hN]; push_cast; linarith
  obtain ⟨C0, hC0, hD0⟩ := G.decay 0 k
  obtain ⟨C1, hC1, hD1⟩ := G.decay N k
  have hq : 0 < (N : ℝ) - (θ + d + k) := by linarith
  have hp : 0 < θ + d + k := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  refine ⟨fun j => min (C0 * lam j ^ (θ + d + k)) ((C1 * (r⁻¹) ^ N) * lam j ^ (-((N : ℝ) - (θ + d + k)))),
    summable_dyadic_min hp hq hC0.le (by positivity), fun j z hz => ?_⟩
  have hs := lam_pos j
  rw [norm_iteratedFDeriv_kterm]
  set D := ‖iteratedFDeriv ℝ k (⇑G) (lam j • z)‖ with hD
  have hD_nn : 0 ≤ D := norm_nonneg _
  have hw : lam j * r ≤ ‖lam j • z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left hz hs.le
  have hmain : lam j ^ (θ + d) * lam j ^ k = lam j ^ (θ + d + k) := by
    rw [← lam_rpow_natCast, ← lam_rpow_add]
  have hDle0 : D ≤ C0 := by simpa using hD0 (lam j • z)
  have hDle1 : (lam j * r) ^ N * D ≤ C1 := by
    refine le_trans ?_ (hD1 (lam j • z))
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hw N) hD_nn
  refine le_min ?_ ?_
  · calc lam j ^ (θ + d) * (lam j ^ k * D) = lam j ^ (θ + d + k) * D := by rw [← hmain]; ring
      _ ≤ lam j ^ (θ + d + k) * C0 := mul_le_mul_of_nonneg_left hDle0 (by positivity)
      _ = C0 * lam j ^ (θ + d + k) := by ring
  · have hpos : 0 < (lam j * r) ^ N := by positivity
    have hneg : lam j ^ (-((N : ℝ) - (θ + d + k))) = lam j ^ (θ + d + k) / lam j ^ N := by
      rw [show -((N : ℝ) - (θ + d + k)) = (θ + d + k) - N by ring, Real.rpow_sub hs,
        Real.rpow_natCast]
    rw [hneg]
    have : D ≤ C1 / (lam j * r) ^ N := by rw [le_div_iff₀ hpos]; linarith
    calc lam j ^ (θ + d) * (lam j ^ k * D) = lam j ^ (θ + d + k) * D := by rw [← hmain]; ring
      _ ≤ lam j ^ (θ + d + k) * (C1 / (lam j * r) ^ N) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = C1 * r⁻¹ ^ N * (lam j ^ (θ + d + k) / lam j ^ N) := by
          rw [mul_pow, inv_pow]; field_simp

/-- the dyadic sum -/
def ksum (G : SchwartzMap (Euc d) ℝ) (θ : ℝ) (z : Euc d) : ℝ := ∑' j : ℤ, kterm G θ j z

theorem locSummable_kterm (G : SchwartzMap (Euc d) ℝ) {θ : ℝ} (ha : 0 < θ + d) :
    LocSummable {z : Euc d | z ≠ 0} (kterm G θ) := by
  intro z₀ hz₀
  have hn : 0 < ‖z₀‖ := norm_pos_iff.2 hz₀
  refine ⟨Metric.ball z₀ (‖z₀‖ / 2), Metric.isOpen_ball, (convex_ball _ _).isPreconnected,
    Metric.mem_ball_self (by positivity), ?_, fun k => ?_⟩
  · intro z hz hz0
    subst hz0
    rw [Metric.mem_ball, dist_zero_left] at hz
    linarith
  · obtain ⟨v, hv, hb⟩ := dyadic_bound G ha k (half_pos hn)
    refine ⟨v, hv, fun j z hz => hb j z ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have := norm_sub_norm_le z₀ z
    linarith [norm_sub_rev z₀ z]

theorem contDiffOn_ksum (G : SchwartzMap (Euc d) ℝ) {θ : ℝ} (ha : 0 < θ + d) :
    ContDiffOn ℝ ∞ (ksum G θ) {z : Euc d | z ≠ 0} :=
  contDiffOn_infty_tsum_local isOpen_ne (contDiff_kterm G θ) (locSummable_kterm G ha)

theorem kterm_even {G : SchwartzMap (Euc d) ℝ} (hG : ∀ w, G (-w) = G w) (θ : ℝ) (j : ℤ) (z : Euc d) :
    kterm G θ j (-z) = kterm G θ j z := by
  simp [kterm, smul_neg, hG]

theorem ksum_even {G : SchwartzMap (Euc d) ℝ} (hG : ∀ w, G (-w) = G w) (θ : ℝ) (z : Euc d) :
    ksum G θ (-z) = ksum G θ z := by
  simp [ksum, kterm_even hG]

theorem kterm_scale (G : SchwartzMap (Euc d) ℝ) (θ : ℝ) (n j : ℤ) (z : Euc d) :
    kterm G θ j (lam n • z) = lam n ^ (-(θ + d)) * kterm G θ (j + n) z := by
  unfold kterm
  rw [smul_smul, ← lam_add, lam_add j n, Real.mul_rpow (lam_pos j).le (lam_pos n).le]
  have h : lam n ^ (-(θ + d)) * lam n ^ (θ + d) = 1 := by
    rw [← Real.rpow_add (lam_pos n)]; simp
  calc _ = (lam n ^ (-(θ + d)) * lam n ^ (θ + d)) * (lam j ^ (θ + d) * G ((lam j * lam n) • z)) := by
        rw [h, one_mul]
    _ = _ := by ring


theorem ksum_scale (G : SchwartzMap (Euc d) ℝ) (θ : ℝ) (n : ℤ) (z : Euc d) :
    ksum G θ (lam n • z) = lam n ^ (-(θ + d)) * ksum G θ z := by
  unfold ksum
  simp_rw [kterm_scale]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight n).tsum_eq (fun j => kterm G θ j z)

theorem ksum_bound (G : SchwartzMap (Euc d) ℝ) {θ : ℝ} (ha : 0 < θ + d) :
    ∃ C : ℝ, ∀ z : Euc d, z ≠ 0 → |ksum G θ z| ≤ C * ‖z‖ ^ (-(d : ℝ) - θ) := by
  obtain ⟨v, hv, hb⟩ := dyadic_bound G ha 0 one_pos
  have hC0 : ∀ z' : Euc d, 1 ≤ ‖z'‖ → |ksum G θ z'| ≤ ∑' j, v j := by
    intro z' hz'
    have := tsum_of_norm_bounded (f := fun j => kterm G θ j z') hv.hasSum (fun j => by
      have := hb j z' hz'
      simpa using this)
    simpa [ksum] using this
  refine ⟨(∑' j, v j) * 2 ^ (θ + d), fun z hz => ?_⟩
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hn (one_lt_two : (1 : ℝ) < 2)
  have hlam : lam n = (2 : ℝ) ^ n := by unfold lam; exact Real.rpow_intCast 2 n
  rw [← hlam] at hn1
  rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0), ← hlam] at hn2
  set z' : Euc d := lam (-n) • z with hz'
  have hzz : z = lam n • z' := by
    rw [hz', smul_smul, ← lam_add]; simp [lam_zero]
  have hz'n : 1 ≤ ‖z'‖ := by
    rw [hz', norm_smul, Real.norm_eq_abs, abs_of_pos (lam_pos _), lam_neg, inv_mul_eq_div,
      le_div_iff₀ (lam_pos n)]
    linarith
  have h1 : |ksum G θ z| ≤ lam n ^ (-(θ + d)) * ∑' j, v j := by
    rw [hzz, ksum_scale, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (lam_pos n) _)]
    exact mul_le_mul_of_nonneg_left (hC0 z' hz'n) (Real.rpow_pos_of_pos (lam_pos n) _).le
  have h2 : lam n ^ (-(θ + d)) ≤ 2 ^ (θ + d) * ‖z‖ ^ (-(θ + d)) := by
    have : lam n ^ (-(θ + d)) ≤ (‖z‖ / 2) ^ (-(θ + d)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    refine this.trans (le_of_eq ?_)
    rw [Real.div_rpow hn.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have h3 : -(d : ℝ) - θ = -(θ + d) := by ring
  rw [h3]
  calc |ksum G θ z| ≤ lam n ^ (-(θ + d)) * ∑' j, v j := h1
    _ ≤ (2 ^ (θ + d) * ‖z‖ ^ (-(θ + d))) * ∑' j, v j :=
        mul_le_mul_of_nonneg_right h2 ((abs_nonneg _).trans (hC0 z' hz'n))
    _ = _ := by ring


theorem continuousOn_ksum (G : SchwartzMap (Euc d) ℝ) {θ : ℝ} (ha : 0 < θ + d) :
    ContinuousOn (ksum G θ) {z : Euc d | z ≠ 0} :=
  (contDiffOn_ksum G ha).continuousOn

theorem measurable_ksum (G : SchwartzMap (Euc d) ℝ) {θ : ℝ} (ha : 0 < θ + d) :
    Measurable (ksum G θ) :=
  measurable_of_continuousOn_compl_singleton (0 : Euc d) (continuousOn_ksum G ha)



/-! ### (d) The symbol of the dyadic sum -/

/-- `1 - cos 2π⟨η,w⟩` -/
def phase (η w : Euc d) : ℝ := 1 - Real.cos (2 * Real.pi * inner ℝ η w)

theorem phase_nonneg (η w : Euc d) : 0 ≤ phase η w := by
  unfold phase; linarith [Real.cos_le_one (2 * Real.pi * inner ℝ η w)]

theorem phase_le_two (η w : Euc d) : phase η w ≤ 2 := by
  unfold phase; linarith [Real.neg_one_le_cos (2 * Real.pi * inner ℝ η w)]

theorem phase_le_sq (η w : Euc d) : phase η w ≤ 2 * Real.pi ^ 2 * ‖η‖ ^ 2 * ‖w‖ ^ 2 := by
  unfold phase
  have h := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * inner ℝ η w)
  have h2 : (inner ℝ η w) ^ 2 ≤ ‖η‖ ^ 2 * ‖w‖ ^ 2 := by
    have := abs_real_inner_le_norm η w
    calc (inner ℝ η w) ^ 2 = |inner ℝ η w| ^ 2 := (sq_abs _).symm
      _ ≤ (‖η‖ * ‖w‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = _ := by ring
  have hpi : 0 ≤ Real.pi ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hpi]

theorem continuous_phase (η : Euc d) : Continuous (phase η) := by
  unfold phase; fun_prop

theorem integrable_G_phase (G : SchwartzMap (Euc d) ℝ) (η : Euc d) :
    Integrable (fun w => G w * phase η w) := by
  refine ((G.integrable (μ := volume)).norm.const_mul 2).mono' ?_ (ae_of_all _ fun w => ?_)
  · exact (G.continuous.mul (continuous_phase η)).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs (phase η w), abs_of_nonneg (phase_nonneg η w)]
    nlinarith [norm_nonneg (G w), phase_le_two η w, phase_nonneg η w]

/-- `∫ |G w| |1 - cos 2π⟨η,w⟩| dw ≤ min(2 M₀, 2π²M₂ ‖η‖²)` -/
theorem J_bound (G : SchwartzMap (Euc d) ℝ) (η : Euc d) :
    ∫ w, ‖G w * phase η w‖ ≤
      min (2 * ∫ w, ‖G w‖) ((2 * Real.pi ^ 2 * ‖η‖ ^ 2) * ∫ w, ‖w‖ ^ 2 * ‖G w‖) := by
  have hI := (integrable_G_phase G η).norm
  have h0 : Integrable (fun w => ‖G w‖) := (G.integrable (μ := volume)).norm
  have h2 : Integrable (fun w => ‖w‖ ^ 2 * ‖G w‖) := G.integrable_pow_mul volume 2
  refine le_min ?_ ?_
  · rw [← integral_const_mul]
    refine integral_mono hI (h0.const_mul 2) fun w => ?_
    simp only
    rw [norm_mul, Real.norm_eq_abs (phase η w), abs_of_nonneg (phase_nonneg η w)]
    nlinarith [norm_nonneg (G w), phase_le_two η w, phase_nonneg η w]
  · rw [← integral_const_mul]
    refine integral_mono hI (h2.const_mul _) fun w => ?_
    simp only
    rw [norm_mul, Real.norm_eq_abs (phase η w), abs_of_nonneg (phase_nonneg η w)]
    have := phase_le_sq η w
    nlinarith [norm_nonneg (G w), phase_nonneg η w, mul_le_mul_of_nonneg_left this (norm_nonneg (G w))]

theorem integral_scale (f : Euc d → ℝ) (θ : ℝ) (j : ℤ) :
    ∫ z, lam j ^ (θ + d) * f (lam j • z) = lam j ^ θ * ∫ w, f w := by
  rw [integral_const_mul, Measure.integral_comp_smul volume f (lam j)]
  rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.2 (pow_pos (lam_pos j) d)), smul_eq_mul,
    lam_rpow_add, lam_rpow_natCast]
  have h : lam j ^ d ≠ 0 := (pow_pos (lam_pos j) d).ne'
  field_simp


theorem phase_scale (ξ z : Euc d) (j : ℤ) : phase (lam (-j) • ξ) (lam j • z) = phase ξ z := by
  unfold phase
  rw [inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  have : lam (-j) * lam j = 1 := by rw [← lam_add]; simp [lam_zero]
  congr 2
  calc 2 * Real.pi * (lam (-j) * (lam j * inner ℝ ξ z)) = 2 * Real.pi * ((lam (-j) * lam j) * inner ℝ ξ z) := by ring
    _ = _ := by rw [this]; ring

theorem kterm_phase (G : SchwartzMap (Euc d) ℝ) (θ : ℝ) (ξ : Euc d) (j : ℤ) (z : Euc d) :
    kterm G θ j z * phase ξ z =
      lam j ^ (θ + d) * ((fun w => G w * phase (lam (-j) • ξ) w) (lam j • z)) := by
  simp only [kterm, phase_scale]; ring

theorem integrable_term (G : SchwartzMap (Euc d) ℝ) (θ : ℝ) (ξ : Euc d) (j : ℤ) :
    Integrable (fun z => kterm G θ j z * phase ξ z) := by
  have := ((integrable_G_phase G (lam (-j) • ξ)).comp_smul (lam_pos j).ne').const_mul (lam j ^ (θ + d))
  refine this.congr (ae_of_all _ fun z => ?_)
  exact (kterm_phase G θ ξ j z).symm

theorem integral_term (G : SchwartzMap (Euc d) ℝ) (θ : ℝ) (ξ : Euc d) (j : ℤ) :
    ∫ z, kterm G θ j z * phase ξ z = lam j ^ θ * ∫ w, G w * phase (lam (-j) • ξ) w := by
  simp_rw [kterm_phase]
  exact integral_scale (fun w => G w * phase (lam (-j) • ξ) w) θ j

theorem integral_norm_term (G : SchwartzMap (Euc d) ℝ) (θ : ℝ) (ξ : Euc d) (j : ℤ) :
    ∫ z, ‖kterm G θ j z * phase ξ z‖ = lam j ^ θ * ∫ w, ‖G w * phase (lam (-j) • ξ) w‖ := by
  have : ∀ z, ‖kterm G θ j z * phase ξ z‖ =
      lam j ^ (θ + d) * ((fun w => ‖G w * phase (lam (-j) • ξ) w‖) (lam j • z)) := by
    intro z
    rw [kterm_phase, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (lam_pos j) _)]
  simp_rw [this]
  exact integral_scale (fun w => ‖G w * phase (lam (-j) • ξ) w‖) θ j

theorem summable_norm_terms (G : SchwartzMap (Euc d) ℝ) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (ξ : Euc d) : Summable (fun j : ℤ => ∫ z, ‖kterm G θ j z * phase ξ z‖) := by
  set M0 : ℝ := ∫ w, ‖G w‖ with hM0
  set M2 : ℝ := ∫ w, ‖w‖ ^ 2 * ‖G w‖ with hM2
  have hM0n : 0 ≤ M0 := integral_nonneg fun w => norm_nonneg _
  have hM2n : 0 ≤ M2 := integral_nonneg fun w => by positivity
  have hs := summable_dyadic_min (p := θ) (q := 2 - θ) (c₁ := 2 * M0)
    (c₂ := 2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * M2) hθ0 (by linarith) (by positivity) (by positivity)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hs
  · exact integral_nonneg fun z => norm_nonneg _
  · rw [integral_norm_term]
    have hJ := J_bound G (lam (-j) • ξ)
    have hl := lam_pos j
    have hnorm : ‖lam (-j) • ξ‖ = (lam j)⁻¹ * ‖ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lam_pos _), lam_neg]
    rw [hnorm] at hJ
    refine le_min ?_ ?_
    · calc _ ≤ lam j ^ θ * (2 * M0) := mul_le_mul_of_nonneg_left (hJ.trans (min_le_left _ _)) (by positivity)
        _ = _ := by ring
    · have h2 := hJ.trans (min_le_right _ _)
      calc _ ≤ lam j ^ θ * ((2 * Real.pi ^ 2 * ((lam j)⁻¹ * ‖ξ‖) ^ 2) * M2) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by
          have : lam j ^ (-(2 - θ)) = lam j ^ θ / lam j ^ 2 := by
            rw [show -(2 - θ) = θ - 2 by ring, Real.rpow_sub hl, ← Real.rpow_natCast]
            norm_num
          rw [this]
          field_simp


theorem integrable_tsum_aux {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    {F : ι → α → ℝ} (hF : ∀ j, Integrable (F j) μ) (hs : Summable fun j => ∫ a, ‖F j a‖ ∂μ)
    (hmeas : AEStronglyMeasurable (fun a => ∑' j, F j a) μ) :
    Integrable (fun a => ∑' j, F j a) μ := by
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ a, ‖∑' j, F j a‖ₑ ∂μ ≤ ∫⁻ a, ∑' j, ‖F j a‖ₑ ∂μ :=
        lintegral_mono fun a => enorm_tsum_le_tsum_enorm
    _ = ∑' j, ∫⁻ a, ‖F j a‖ₑ ∂μ := lintegral_tsum fun j => (hF j).1.aemeasurable.enorm
    _ = ∑' j, ENNReal.ofReal (∫ a, ‖F j a‖ ∂μ) := by
        refine tsum_congr fun j => ?_
        rw [ofReal_integral_norm_eq_lintegral_enorm (hF j)]
    _ = ENNReal.ofReal (∑' j, ∫ a, ‖F j a‖ ∂μ) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg fun a => norm_nonneg _) hs).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem integral_G_phase (G : SchwartzMap (Euc d) ℝ) (P : Euc d → ℝ)
    (hP : ∀ η, ∫ w, G w * Real.cos (2 * Real.pi * inner ℝ η w) = P η) (η : Euc d) :
    ∫ w, G w * phase η w = P 0 - P η := by
  have h0 := hP 0
  simp only [inner_zero_left, mul_zero, Real.cos_zero, mul_one] at h0
  have hc : Integrable (fun w => G w * Real.cos (2 * Real.pi * inner ℝ η w)) := by
    have := (G.integrable (μ := volume)).sub (integrable_G_phase G η)
    refine this.congr (ae_of_all _ fun w => ?_)
    simp only [Pi.sub_apply, phase]; ring
  have : ∀ w, G w * phase η w = G w - G w * Real.cos (2 * Real.pi * inner ℝ η w) := by
    intro w; unfold phase; ring
  simp_rw [this]
  rw [integral_sub (G.integrable (μ := volume)) hc, h0, hP η]

theorem symbol_generic (G : SchwartzMap (Euc d) ℝ) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (P : Euc d → ℝ) (hP : ∀ η, ∫ w, G w * Real.cos (2 * Real.pi * inner ℝ η w) = P η)
    (ξ : Euc d) :
    Integrable (fun z => ksum G θ z * phase ξ z) ∧
    HasSum (fun j : ℤ => lam j ^ θ * (P 0 - P (lam (-j) • ξ))) (∫ z, ksum G θ z * phase ξ z) := by
  have ha : 0 < θ + d := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have htsum : (fun z => ksum G θ z * phase ξ z) = fun z => ∑' j : ℤ, kterm G θ j z * phase ξ z := by
    funext z; unfold ksum; rw [tsum_mul_right]
  have hs := summable_norm_terms G hθ0 hθ2 ξ
  have hint : Integrable (fun z => ksum G θ z * phase ξ z) := by
    rw [htsum]
    exact integrable_tsum_aux (integrable_term G θ ξ) hs (by
      rw [← htsum]
      exact ((measurable_ksum G ha).mul (continuous_phase ξ).measurable).aestronglyMeasurable)
  refine ⟨hint, ?_⟩
  have := hasSum_integral_of_summable_integral_norm (integrable_term G θ ξ) hs
  rw [← htsum] at this
  convert this using 1
  funext j
  rw [integral_term, integral_G_phase G P hP]



/-! ### (e) The kernel and the core theorem -/

/-- The Lévy kernel `𝔨(z) = -∑_{j∈ℤ} 2^{j(θ+d)} G(2^j z)`, `G = Re 𝓕 (m ψ)`. -/
def levyK (θ : ℝ) (m : Euc d → ℝ) (z : Euc d) : ℝ :=
  -∑' j : ℤ, lam j ^ (θ + d) * Gfun m (lam j • z)

theorem levyK_eq {θ : ℝ} {m : Euc d → ℝ} (hsm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0}) :
    levyK θ m = fun z => -ksum (GS hsm) θ z := by
  funext z
  simp only [levyK, ksum, kterm, GS_apply]

theorem GS_even {m : Euc d → ℝ} (hsm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0}) (he : ∀ ξ, m (-ξ) = m ξ)
    (w : Euc d) : GS hsm (-w) = GS hsm w := by
  rw [GS_apply, GS_apply, Gfun_neg he]

theorem levyK_even {θ : ℝ} {m : Euc d → ℝ} (hm : IsHomogSymbol θ m) (z : Euc d) :
    levyK θ m (-z) = levyK θ m z := by
  rw [levyK_eq hm.smooth]
  simp only
  rw [ksum_even (GS_even hm.smooth hm.even)]

theorem levyK_smooth {θ : ℝ} (hθ : 0 < θ) {m : Euc d → ℝ} (hm : IsHomogSymbol θ m) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (levyK θ m) {z | z ≠ 0} := by
  have ha : 0 < θ + d := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  rw [levyK_eq hm.smooth]
  exact (contDiffOn_ksum _ ha).neg

theorem levyK_bound {θ : ℝ} (hθ : 0 < θ) {m : Euc d → ℝ} (hm : IsHomogSymbol θ m) :
    ∃ C : ℝ, ∀ z : Euc d, z ≠ 0 → |levyK θ m z| ≤ C * ‖z‖ ^ (-(d : ℝ) - θ) := by
  have ha : 0 < θ + d := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  obtain ⟨C, hC⟩ := ksum_bound (GS hm.smooth) ha
  refine ⟨C, fun z hz => ?_⟩
  rw [levyK_eq hm.smooth]
  simpa [abs_neg] using hC z hz

theorem levy_measurable {θ : ℝ} (hθ : 0 < θ) {m : Euc d → ℝ} (hm : IsHomogSymbol θ m) :
    Measurable (levyK θ m) := by
  have ha : 0 < θ + d := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  rw [levyK_eq hm.smooth]
  exact (measurable_ksum _ ha).neg

theorem levyK_symbol {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {m : Euc d → ℝ} (hm : IsHomogSymbol θ m)
    (ξ : Euc d) :
    Integrable (fun z => levyK θ m z * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z))) ∧
    ∫ z, levyK θ m z * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z)) = m ξ := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [hm.zero]
  have hP : ∀ η, ∫ w, GS hm.smooth w * Real.cos (2 * Real.pi * inner ℝ η w) = PhiR m η := by
    intro η
    simp_rw [GS_apply]
    exact Gfun_cos hm.smooth hm.even η
  obtain ⟨hint, hsum⟩ := symbol_generic (GS hm.smooth) hθ0 hθ2 (PhiR m) hP ξ
  have hterm : ∀ j : ℤ, lam j ^ θ * (PhiR m 0 - PhiR m (lam (-j) • ξ)) =
      -m ξ * psiR d (lam (-j) • ξ) := by
    intro j
    rw [PhiR_zero]
    unfold PhiR
    rw [hm.homog _ (lam_pos _)]
    have : lam j ^ θ * lam (-j) ^ θ = 1 := by
      rw [← Real.mul_rpow (lam_pos j).le (lam_pos _).le, ← lam_add]; simp [lam_zero]
    calc _ = -(lam j ^ θ * lam (-j) ^ θ * m ξ * psiR d (lam (-j) • ξ)) := by ring
      _ = _ := by rw [this]; ring
  have h2 : HasSum (fun j : ℤ => lam j ^ θ * (PhiR m 0 - PhiR m (lam (-j) • ξ))) (-m ξ) := by
    simp_rw [hterm]
    simpa using (hasSum_psiR hξ).mul_left (-m ξ)
  have h3 := hsum.unique h2
  rw [levyK_eq hm.smooth]
  simp only [neg_mul]
  refine ⟨hint.neg, ?_⟩
  rw [integral_neg]
  have : ∫ z, ksum (GS hm.smooth) θ z * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z)) = -m ξ := h3
  rw [this]; ring

/-- The kernel half of Lemma C.3 (ii) on `ℝ^d`. -/
theorem levy_core {θ : ℝ} {m : Euc d → ℝ} (_hd : 1 ≤ d) (hθ0 : 0 < θ) (hθ2 : θ < 2) (hm : IsHomogSymbol θ m) :
    ∃ 𝔨 : Euc d → ℝ,
      (∀ z, 𝔨 (-z) = 𝔨 z) ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) 𝔨 {z | z ≠ 0} ∧
      (∃ C : ℝ, ∀ z : Euc d, z ≠ 0 → |𝔨 z| ≤ C * ‖z‖ ^ (-(d : ℝ) - θ)) ∧
      ∀ ξ : Euc d, Integrable (fun z => 𝔨 z * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z))) ∧
        ∫ z, 𝔨 z * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z)) = m ξ :=
  ⟨levyK θ m, levyK_even hm, levyK_smooth hθ0 hm, levyK_bound hθ0 hm, levyK_symbol hθ0 hθ2 hm⟩



/-! ### (f) Integrability of `|𝔨| min(|z|², 1)` -/

open Set in
theorem integrableOn_radial_aux (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) :
    IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ (Euc d) - 1) •
      (y ^ (-(d : ℝ) - θ) * min (y ^ 2) 1)) (Ioi 0) := by
  rw [finrank_euclideanSpace_fin]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun y : ℝ => y ^ (1 - θ)) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := 1 - θ)
        (by linarith))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
    refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioc
    obtain ⟨hy0, hy1⟩ := hy
    have hm : min (y ^ 2) 1 = y ^ 2 := min_eq_left (pow_le_one₀ hy0.le hy1)
    simp only [smul_eq_mul, hm]
    rw [← Real.rpow_natCast, ← Real.rpow_natCast y 2, ← Real.rpow_add hy0, ← Real.rpow_add hy0]
    congr 1
    push_cast [Nat.cast_sub hd]
    ring
  · have h1 : IntegrableOn (fun y : ℝ => y ^ (-1 - θ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy1 : (1 : ℝ) < y := hy
    have hy0 : 0 < y := by linarith
    have hm : min (y ^ 2) 1 = 1 := min_eq_right (one_le_pow₀ hy1.le)
    simp only [smul_eq_mul, hm, mul_one]
    rw [← Real.rpow_natCast, ← Real.rpow_add hy0]
    congr 1
    push_cast [Nat.cast_sub hd]
    ring

/-- A kernel with `|𝔨(z)| ≤ C |z|^{-d-θ}`, `0 < θ < 2`, is integrable against `min(|z|², 1)`. -/
theorem kernel_min_integrable (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {𝔨 : Euc d → ℝ}
    (hb : ∃ C : ℝ, ∀ z : Euc d, z ≠ 0 → |𝔨 z| ≤ C * ‖z‖ ^ (-(d : ℝ) - θ))
    (hmeas : Measurable 𝔨) :
    Integrable (fun z => |𝔨 z| * min (‖z‖ ^ 2) 1) := by
  obtain ⟨C, hC⟩ := hb
  have : Nontrivial (Euc d) := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have hg : Integrable (fun z : Euc d => |C| * (‖z‖ ^ (-(d : ℝ) - θ) * min (‖z‖ ^ 2) 1)) := by
    refine Integrable.const_mul ?_ _
    exact (integrable_fun_norm_addHaar (volume : Measure (Euc d))
      (f := fun y : ℝ => y ^ (-(d : ℝ) - θ) * min (y ^ 2) 1)).2 (integrableOn_radial_aux hd hθ0 hθ2)
  refine hg.mono' ((hmeas.abs.mul (by fun_prop)).aestronglyMeasurable) ?_
  have hae : ∀ᵐ z : Euc d ∂volume, z ≠ 0 := by
    have : (volume : Measure (Euc d)) {0} = 0 := measure_singleton 0
    exact compl_mem_ae_iff.2 this
  filter_upwards [hae] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (le_min (by positivity) zero_le_one))]
  have h1 := hC z hz
  have h2 : 0 ≤ min (‖z‖ ^ 2) 1 := le_min (by positivity) zero_le_one
  calc |𝔨 z| * min (‖z‖ ^ 2) 1 ≤ (C * ‖z‖ ^ (-(d : ℝ) - θ)) * min (‖z‖ ^ 2) 1 :=
        mul_le_mul_of_nonneg_right h1 h2
    _ ≤ (|C| * ‖z‖ ^ (-(d : ℝ) - θ)) * min (‖z‖ ^ 2) 1 := by
        gcongr
        exact le_abs_self C
    _ = _ := by ring


end HRS.PDE.ToolboxRd.LevyAux
