import HRS.MS.MovInterpAux3
import HRS.PDE.ToolboxRd.Fourier

/-!
# MOVA3B1, part 1: Fourier-side bookkeeping for the `Σ → H` interpolation

Namespace `HRS.MS.MovOsc`, helpers `mova3b1_`.  Everything here is the Fourier-side input of
`mo_interp_osc_H` (file `MovBridgeAux2`): for a map `T` linear on the Hermite span with values in
`L²`, the Fourier transform of `T (∑ c_α h_α)` is `∑ c_α \hat{T h_α}` (`mova3b1_fourier_T_comb`),
and the endpoint hypotheses `‖T f‖_{H^s} ≤ M ‖f‖_{Σ^r}` (real `f`) extend to complex coefficients
(`mova3b1_endpoint_sob`): the cross term between real and imaginary parts vanishes because the
Fourier transform of a real function is Hermitian (`fourierL2_neg`) and the weight is even.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ComplexConjugate
open HRS.Whole HRS.MS.MovInterp HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

namespace HRS.MS.MovOsc

variable {d : ℕ}

/-- The Sobolev weight `1 + 4π²|ξ|²`. -/
def mova3b1_W (ξ : Euc d) : ℝ := 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2

lemma mova3b1_W_ge (ξ : Euc d) : 1 ≤ mova3b1_W ξ := by
  unfold mova3b1_W; nlinarith [sq_nonneg (Real.pi * ‖ξ‖), sq_nonneg ‖ξ‖, Real.pi_pos]

lemma mova3b1_W_pos (ξ : Euc d) : 0 < mova3b1_W ξ := lt_of_lt_of_le one_pos (mova3b1_W_ge ξ)

lemma mova3b1_W_cont : Continuous (mova3b1_W : Euc d → ℝ) := by
  unfold mova3b1_W; fun_prop

lemma mova3b1_W_neg (ξ : Euc d) : mova3b1_W (-ξ) = mova3b1_W ξ := by simp [mova3b1_W]

/-- `W^e` is the integrand weight of `sobolevNormSq`. -/
lemma mova3b1_sobolevNormSq_eq (s : ℝ) (u : Euc d → ℝ) :
    HRS.PDE.ToolboxRd.sobolevNormSq s u = ∫ ξ, mova3b1_W ξ ^ s * ‖fourierL2 u ξ‖ ^ 2 := rfl

lemma mova3b1_memSobolev_iff (s : ℝ) (u : Euc d → ℝ) :
    HRS.PDE.ToolboxRd.MemSobolev s u ↔ MemLp u 2 volume ∧
      Integrable fun ξ => mova3b1_W ξ ^ s * ‖fourierL2 u ξ‖ ^ 2 := Iff.rfl

/-! ### Odd functions -/

lemma mova3b1_integral_odd {g : Euc d → ℝ} (h : ∀ᵐ ξ ∂(volume : Measure (Euc d)), g (-ξ) = -g ξ) :
    ∫ ξ, g ξ = 0 := by
  have h1 : ∫ ξ, g (-ξ) = ∫ ξ, g ξ := integral_neg_eq_self g volume
  have h2 : ∫ ξ, g (-ξ) = ∫ ξ, -g ξ := integral_congr_ae h
  rw [h2, integral_neg] at h1
  linarith

/-! ### Fourier transform of a finite combination -/

lemma mova3b1_fourier_sum {ι : Type*} {g : ι → Euc d → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (S : Finset ι) (c : ι → ℝ) :
    fourierL2 (fun x => ∑ i ∈ S, c i * g i x) =ᵐ[volume]
      fun ξ => ∑ i ∈ S, (c i : ℂ) * fourierL2 (g i) ξ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0 := fourierL2_smul (MemLp.zero : MemLp (fun _ : Euc d => (0 : ℝ)) 2 volume) 0
    simp only [zero_mul] at h0
    simpa using h0
  | insert a S ha ih =>
    have hS : MemLp (fun x => ∑ i ∈ S, c i * g i x) 2 volume := by
      have : (fun x => ∑ i ∈ S, c i * g i x) = ∑ i ∈ S, fun x => c i * g i x := by
        funext x; simp
      rw [this]
      exact memLp_finsetSum' S fun i _ => (hg i).const_mul (c i)
    have ha' : MemLp (fun x => c a * g a x) 2 volume := (hg a).const_mul (c a)
    have e : (fun x => ∑ i ∈ insert a S, c i * g i x) =
        fun x => (fun x => c a * g a x) x + (fun x => ∑ i ∈ S, c i * g i x) x := by
      funext x; simp [Finset.sum_insert ha]
    rw [e]
    filter_upwards [fourierL2_add ha' hS, fourierL2_smul (hg a) (c a), ih] with ξ h1 h2 h3
    rw [h1, h2, h3, Finset.sum_insert ha]

section LinearMap

variable {T : (Euc d → ℝ) → (Euc d → ℝ)}

lemma mova3b1_fourier_T_comb
    (hlin : ∀ f ∈ mo_Hspan d, ∀ g ∈ mo_Hspan d, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f ∈ mo_Hspan d, MemLp (T f) 2 (volume : Measure (Euc d)))
    (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    fourierL2 (T (mova3_comb S c)) =ᵐ[volume]
      fun ξ => ∑ α ∈ S, (c α : ℂ) * fourierL2 (T (hermiteFunD α)) ξ := by
  rw [mova3_T_comb hlin]
  exact mova3b1_fourier_sum (fun α => hL2 _ (mova3_hermite_mem α)) S c

/-! ### The cross term -/

/-- `∫ W^e |A + iB|² = ∫ W^e |A|² + ∫ W^e |B|²` for Fourier transforms of real `L²` functions. -/
lemma mova3b1_sq_split {u v : Euc d → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) (e : ℝ)
    (hIu : Integrable fun ξ => mova3b1_W ξ ^ e * ‖fourierL2 u ξ‖ ^ 2)
    (hIv : Integrable fun ξ => mova3b1_W ξ ^ e * ‖fourierL2 v ξ‖ ^ 2) :
    Integrable (fun ξ => mova3b1_W ξ ^ e *
        ‖fourierL2 u ξ + Complex.I * fourierL2 v ξ‖ ^ 2) ∧
      ∫ ξ, mova3b1_W ξ ^ e * ‖fourierL2 u ξ + Complex.I * fourierL2 v ξ‖ ^ 2 =
        (∫ ξ, mova3b1_W ξ ^ e * ‖fourierL2 u ξ‖ ^ 2) +
          ∫ ξ, mova3b1_W ξ ^ e * ‖fourierL2 v ξ‖ ^ 2 := by
  set A := fourierL2 u with hA
  set B := fourierL2 v with hB
  set X : Euc d → ℝ := fun ξ => 2 * (mova3b1_W ξ ^ e * (A ξ * conj (B ξ)).im) with hX
  have hAm : AEStronglyMeasurable A volume := aestronglyMeasurable_fourierL2 hu
  have hBm : AEStronglyMeasurable B volume := aestronglyMeasurable_fourierL2 hv
  have hWe : Continuous fun ξ : Euc d => mova3b1_W ξ ^ e :=
    mova3b1_W_cont.rpow_const fun ξ => Or.inl (mova3b1_W_pos ξ).ne'
  have hXm : AEStronglyMeasurable X volume := by
    refine (aestronglyMeasurable_const.mul ((hWe.aestronglyMeasurable).mul ?_))
    exact (Complex.continuous_im.comp_aestronglyMeasurable (hAm.mul hBm.star))
  have hXi : Integrable X := by
    refine (hIu.add hIv).mul_const 2 |>.mono' hXm (Eventually.of_forall fun ξ => ?_)
    have hw0 : 0 ≤ mova3b1_W ξ ^ e := Real.rpow_nonneg (mova3b1_W_pos ξ).le _
    simp only [hX, Real.norm_eq_abs, abs_mul, abs_two, abs_of_nonneg hw0]
    have h1 : |(A ξ * conj (B ξ)).im| ≤ ‖A ξ * conj (B ξ)‖ := Complex.abs_im_le_norm _
    have h2 : ‖A ξ * conj (B ξ)‖ ≤ (‖A ξ‖ ^ 2 + ‖B ξ‖ ^ 2) / 2 := by
      rw [norm_mul, Complex.norm_conj]; nlinarith [sq_nonneg (‖A ξ‖ - ‖B ξ‖)]
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hw0
    simp only [Pi.add_apply]
    nlinarith
  have hpt : ∀ ξ, mova3b1_W ξ ^ e * ‖A ξ + Complex.I * B ξ‖ ^ 2 =
      mova3b1_W ξ ^ e * ‖A ξ‖ ^ 2 + mova3b1_W ξ ^ e * ‖B ξ‖ ^ 2 + X ξ := by
    intro ξ
    simp only [hX, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re,
      Complex.conj_im]
    ring
  have hodd : ∀ᵐ ξ ∂(volume : Measure (Euc d)), X (-ξ) = - X ξ := by
    filter_upwards [fourierL2_neg hu, fourierL2_neg hv] with ξ h1 h2
    simp only [hX, mova3b1_W_neg, hA, hB, h1, h2, Complex.mul_im, Complex.conj_re,
      Complex.conj_im]
    ring
  have hXz : ∫ ξ, X ξ = 0 := mova3b1_integral_odd hodd
  have hfun : (fun ξ => mova3b1_W ξ ^ e * ‖A ξ + Complex.I * B ξ‖ ^ 2) =
      fun ξ => (mova3b1_W ξ ^ e * ‖A ξ‖ ^ 2 + mova3b1_W ξ ^ e * ‖B ξ‖ ^ 2) + X ξ :=
    funext hpt
  rw [hfun]
  refine ⟨(hIu.add hIv).add hXi, ?_⟩
  have hsum : Integrable (fun ξ => mova3b1_W ξ ^ e * ‖A ξ‖ ^ 2 + mova3b1_W ξ ^ e * ‖B ξ‖ ^ 2) :=
    hIu.add hIv
  rw [integral_add hsum hXi, integral_add hIu hIv, hXz, add_zero]

/-- The endpoint bound for complex coefficients. -/
lemma mova3b1_endpoint_sob
    (hlin : ∀ f ∈ mo_Hspan d, ∀ g ∈ mo_Hspan d, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f ∈ mo_Hspan d, MemLp (T f) 2 (volume : Measure (Euc d)))
    {r s M : ℝ}
    (h : ∀ f ∈ mo_Hspan d, HRS.PDE.ToolboxRd.MemSobolev s (T f) ∧
      Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s (T f)) ≤ M * oscNorm r f)
    (S : Finset (MultiIndex d)) (u : MultiIndex d → ℂ) :
    Integrable (fun ξ => mova3b1_W ξ ^ s *
        ‖∑ α ∈ S, u α * fourierL2 (T (hermiteFunD α)) ξ‖ ^ 2) ∧
      ∫ ξ, mova3b1_W ξ ^ s * ‖∑ α ∈ S, u α * fourierL2 (T (hermiteFunD α)) ξ‖ ^ 2 ≤
        M ^ 2 * ∑ α ∈ S, oscEigenvalue d α ^ r * ‖u α‖ ^ 2 := by
  set a := mova3_comb S (fun α => (u α).re) with ha
  set b := mova3_comb S (fun α => (u α).im) with hb
  have haM := mova3_comb_mem S (fun α => (u α).re)
  have hbM := mova3_comb_mem S (fun α => (u α).im)
  obtain ⟨⟨_, hIa⟩, hna⟩ := h a haM
  obtain ⟨⟨_, hIb⟩, hnb⟩ := h b hbM
  have hTa := hL2 a haM
  have hTb := hL2 b hbM
  obtain ⟨hI, hEq⟩ := mova3b1_sq_split hTa hTb s hIa hIb
  have hae : (fun ξ => ∑ α ∈ S, u α * fourierL2 (T (hermiteFunD α)) ξ) =ᵐ[volume]
      fun ξ => fourierL2 (T a) ξ + Complex.I * fourierL2 (T b) ξ := by
    filter_upwards [mova3b1_fourier_T_comb hlin hL2 S (fun α => (u α).re),
      mova3b1_fourier_T_comb hlin hL2 S (fun α => (u α).im)] with ξ h1 h2
    rw [ha, hb, h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    conv_lhs => rw [← Complex.re_add_im (u α)]
    ring
  have hcongr : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      mova3b1_W ξ ^ s * ‖∑ α ∈ S, u α * fourierL2 (T (hermiteFunD α)) ξ‖ ^ 2 =
        mova3b1_W ξ ^ s * ‖fourierL2 (T a) ξ + Complex.I * fourierL2 (T b) ξ‖ ^ 2 := by
    filter_upwards [hae] with ξ hξ
    rw [hξ]
  refine ⟨hI.congr (hcongr.mono fun ξ hξ => hξ.symm), ?_⟩
  rw [integral_congr_ae hcongr, hEq]
  have hsq : ∀ (x : ℝ), 0 ≤ x → ∀ y : ℝ, Real.sqrt x ≤ y → x ≤ y ^ 2 := by
    intro x hx y hy
    exact (Real.sqrt_le_iff.1 hy).2
  have h1 := hsq _ (integral_nonneg fun ξ => mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _)
    (sq_nonneg _)) _ hna
  have h2 := hsq _ (integral_nonneg fun ξ => mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _)
    (sq_nonneg _)) _ hnb
  have hnn : ∀ (g : MultiIndex d → ℝ), 0 ≤ ∑ α ∈ S, oscEigenvalue d α ^ r * g α ^ 2 := fun g =>
    Finset.sum_nonneg fun α _ => mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _)
  have n1 : oscNorm r a ^ 2 = ∑ α ∈ S, oscEigenvalue d α ^ r * (u α).re ^ 2 := by
    rw [ha, mova3_oscNorm_comb]; exact Real.sq_sqrt (hnn _)
  have n2 : oscNorm r b ^ 2 = ∑ α ∈ S, oscEigenvalue d α ^ r * (u α).im ^ 2 := by
    rw [hb, mova3_oscNorm_comb]; exact Real.sq_sqrt (hnn _)
  have e3 : ∑ α ∈ S, oscEigenvalue d α ^ r * ‖u α‖ ^ 2 =
      (∑ α ∈ S, oscEigenvalue d α ^ r * (u α).re ^ 2) +
        ∑ α ∈ S, oscEigenvalue d α ^ r * (u α).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [e3, ← n1, ← n2, mul_add]
  have h1' : ∫ ξ, mova3b1_W ξ ^ s * ‖fourierL2 (T a) ξ‖ ^ 2 ≤ M ^ 2 * oscNorm r a ^ 2 := by
    rw [← mul_pow]; exact h1
  have h2' : ∫ ξ, mova3b1_W ξ ^ s * ‖fourierL2 (T b) ξ‖ ^ 2 ≤ M ^ 2 * oscNorm r b ^ 2 := by
    rw [← mul_pow]; exact h2
  linarith

end LinearMap

end HRS.MS.MovOsc
