import HRS.MS.UniqQAux6
import HRS.MS.UlNl

/-!
# UNIQ-Q, part 7: the nonlocal term is bounded by `‖∇u‖_∞` and the Hölder seminorm of `∇u`

`uniqq_cc_bound`: the cancellation integral of `F ∈ C¹ ∩ L¹` against `∂_k g` is bounded by `H ∫ ballF(s+1-β) + c ‖F‖_{L¹}`
when `|F(y) - F(x)| ≤ H |x-y|^β` near `x`.  `uniqq_nl_bound`: `|N u (x)| ≤ K (G + H)` where `G` bounds `∇u` and
`H` is the `β`-Hölder constant of `∇u` (`s + 1 - d < β < 1`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.UniqQ

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc HRS.MS.UniqN2a

variable {d : ℕ}

/-- bound for the cancellation integral -/
theorem uniqq_cc_bound {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hβs : s + 1 - d < β) (k : Fin d) {F : Euc d → ℝ} (hF : ContDiff ℝ 1 F) (hFi : Integrable F)
    {H : ℝ} (hH : 0 ≤ H) (x : Euc d) (hHol : ∀ y, ‖x - y‖ ≤ 1 / 4 → |F y - F x| ≤ H * ‖x - y‖ ^ β) :
    |∫ y, (if ‖x - y‖ ≤ 1 / 4 then (F y - F x) * kap d s k (x - y) else F y * kap d s k (x - y))| ≤
      max 1 s * H * (∫ z, ballF (d := d) (s + 1 - β) z) + max 1 s * 8 ^ (s + 1) * ∫ y, |F y| := by
  have hs'0 : 0 < s + 1 - β := by linarith
  have hs'd : s + 1 - β < d := by linarith
  have hball : Integrable (fun y => ballF (d := d) (s + 1 - β) (x - y)) :=
    (ballF_integrable hs'0 hs'd).comp_sub_left x
  have hm1 : (0 : ℝ) ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
  have hmaj : Integrable (fun y => max 1 s * H * ballF (d := d) (s + 1 - β) (x - y) +
      max 1 s * 8 ^ (s + 1) * |F y|) :=
    (hball.const_mul _).add (hFi.abs.const_mul _)
  have hint := ul1_comp_integrable hs0 hsd k hF hFi x
  have hbd := norm_integral_le_of_norm_le hmaj (μ := volume)
    (f := fun y => if ‖x - y‖ ≤ 1 / 4 then (F y - F x) * kap d s k (x - y) else F y * kap d s k (x - y))
    (Filter.Eventually.of_forall fun y => by
      have hb0 : 0 ≤ ballF (d := d) (s + 1 - β) (x - y) := ballF_nonneg _ _
      have hfar0 : 0 ≤ max 1 s * 8 ^ (s + 1) * |F y| := by positivity
      have hnear0 : 0 ≤ max 1 s * H * ballF (d := d) (s + 1 - β) (x - y) := by positivity
      by_cases hy : ‖x - y‖ ≤ 1 / 4
      · simp only [hy, ite_true]
        by_cases hy0 : x - y = 0
        · have : y = x := by rw [sub_eq_zero] at hy0; exact hy0.symm
          subst this
          simp only [sub_self, zero_mul, norm_zero] at hnear0 ⊢
          linarith
        · have hn : 0 < ‖x - y‖ := norm_pos_iff.2 hy0
          have hb := kap_bound hs0 k hy0
          have h1 : ‖x - y‖ ^ β * ‖x - y‖ ^ (-s - 1) = ‖x - y‖ ^ (-(s + 1 - β)) := by
            rw [← Real.rpow_add hn]; congr 1; ring
          have hbl : ballF (d := d) (s + 1 - β) (x - y) = ‖x - y‖ ^ (-(s + 1 - β)) := by
            simp [ballF, show ‖x - y‖ < 1 by linarith]
          rw [Real.norm_eq_abs, abs_mul]
          calc |F y - F x| * |kap d s k (x - y)|
              ≤ (H * ‖x - y‖ ^ β) * (max 1 s * ‖x - y‖ ^ (-s - 1)) :=
                mul_le_mul (hHol y hy) hb (abs_nonneg _) (by positivity)
            _ = max 1 s * H * ballF (d := d) (s + 1 - β) (x - y) := by rw [hbl, ← h1]; ring
            _ ≤ _ := by linarith
      · simp only [hy, ite_false]
        have hy' : 1 / 8 ≤ ‖x - y‖ := by linarith [not_le.1 hy]
        rw [Real.norm_eq_abs, abs_mul]
        calc |F y| * |kap d s k (x - y)| ≤ |F y| * (max 1 s * 8 ^ (s + 1)) :=
              mul_le_mul_of_nonneg_left (ul1_kap_far_bound hs0 k hy') (abs_nonneg _)
          _ = max 1 s * 8 ^ (s + 1) * |F y| := by ring
          _ ≤ _ := by linarith)
  have hI : ∫ y, (max 1 s * H * ballF (d := d) (s + 1 - β) (x - y) + max 1 s * 8 ^ (s + 1) * |F y|) =
      max 1 s * H * (∫ z, ballF (d := d) (s + 1 - β) z) + max 1 s * 8 ^ (s + 1) * ∫ y, |F y| := by
    rw [integral_add (hball.const_mul _) (hFi.abs.const_mul _), integral_const_mul, integral_const_mul,
      integral_sub_left_eq_self (fun z => ballF (d := d) (s + 1 - β) z) volume x]
  rw [hI] at hbd
  rwa [Real.norm_eq_abs] at hbd

theorem uniqq_self_le_rpow {r β : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hβ1 : β ≤ 1) : r ≤ r ^ β := by
  rcases hr0.eq_or_lt with h | h
  · rw [← h]; exact Real.rpow_nonneg le_rfl _
  · have := Real.rpow_le_rpow_of_exponent_ge h hr1 hβ1
    simpa using this

/-- **the nonlocal term is controlled by `∇u` in `C^β`** -/
theorem uniqq_nl_bound {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hβs : s + 1 - d < β) (M : Matrix (Fin d) (Fin d) ℝ) (ψ : SchwartzMap (Euc d) ℝ) :
    ∃ KN : ℝ, 0 ≤ KN ∧ ∀ {u : Euc d → ℝ}, ContDiff ℝ 2 u → ∀ {G H : ℝ}, 0 ≤ G → 0 ≤ H →
      (∀ y, ‖gradient u y‖ ≤ G) → (∀ x a, ‖gradient u (x + a) - gradient u x‖ ≤ H * ‖a‖ ^ β) →
      ∀ x, |ulNL s M ψ u x| ≤ KN * (G + H) := by
  set Bψ : ℝ := SchwartzMap.seminorm ℝ 0 0 ψ with hBψ
  set Lψ : ℝ := SchwartzMap.seminorm ℝ 0 1 ψ with hLψ
  set Iψ : ℝ := ∫ y, |ψ y| with hIψ
  set Ib : ℝ := ∫ z, ballF (d := d) (s + 1 - β) z with hIb
  have hBψ0 : 0 ≤ Bψ := apply_nonneg _ _
  have hLψ0 : 0 ≤ Lψ := apply_nonneg _ _
  have hIψ0 : 0 ≤ Iψ := integral_nonneg fun _ => abs_nonneg _
  have hIb0 : 0 ≤ Ib := integral_nonneg fun z => ballF_nonneg _ _
  have hm1 : (0 : ℝ) ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
  have hψd : ContDiff ℝ 1 (ψ : Euc d → ℝ) := (ψ.smooth _).of_le (by exact_mod_cast le_top)
  have hψB : ∀ y, |ψ y| ≤ Bψ := fun y => by
    have := SchwartzMap.norm_le_seminorm ℝ ψ y
    rwa [Real.norm_eq_abs] at this
  have hψL : ∀ y, ‖fderiv ℝ ψ y‖ ≤ Lψ := fun y => by
    have := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ ψ 1 y
    rwa [norm_iteratedFDeriv_one] at this
  set KN : ℝ := ∑ j : Fin d, (max 1 s * (Bψ + Lψ) * ‖ul1w M j‖ * Ib + max 1 s * 8 ^ (s + 1) * Iψ * ‖ul1w M j‖)
    with hKN
  have hKN0 : 0 ≤ KN := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨KN, hKN0, fun {u} hu {G H} hG hH hGb hHb x => ?_⟩
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  set F : Fin d → Euc d → ℝ := fun j y => ψ y * fderiv ℝ u y (ul1w M j) with hF
  have hFc : ∀ j, ContDiff ℝ 1 (F j) := fun j =>
    (ul1_F_contDiff ψ M (m := 2) (by norm_num) hu j).of_le (by exact_mod_cast (by norm_num : 1 ≤ 2 - 1))
  have hA : ∀ j y, |fderiv ℝ u y (ul1w M j)| ≤ G * ‖ul1w M j‖ := by
    intro j y
    rw [← uniqq_grad_inner]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hGb y) (norm_nonneg _))
  have hFb : ∀ j y, |F j y| ≤ |ψ y| * (G * ‖ul1w M j‖) := fun j y => by
    simp only [hF]; rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hA j y) (abs_nonneg _)
  have hFi : ∀ j, Integrable (F j) := fun j =>
    (ψ.integrable.abs.mul_const (G * ‖ul1w M j‖)).mono' (hFc j).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hFb j y)
  have hFL1 : ∀ j, ∫ y, |F j y| ≤ Iψ * (G * ‖ul1w M j‖) := fun j => by
    rw [hIψ, ← integral_mul_const]
    exact integral_mono (hFi j).abs (ψ.integrable.abs.mul_const _) (hFb j)
  have hHol : ∀ j y, ‖x - y‖ ≤ 1 / 4 →
      |F j y - F j x| ≤ ((Bψ * H + Lψ * G) * ‖ul1w M j‖) * ‖x - y‖ ^ β := by
    intro j y hxy
    have hr1 : ‖x - y‖ ≤ 1 := by linarith
    have hself := uniqq_self_le_rpow (norm_nonneg (x - y)) hr1 hβ1.le
    have h1 : |fderiv ℝ u y (ul1w M j) - fderiv ℝ u x (ul1w M j)| ≤ H * ‖x - y‖ ^ β * ‖ul1w M j‖ := by
      have := hHb x (y - x)
      rw [add_sub_cancel, norm_sub_rev y x] at this
      rw [← uniqq_grad_inner, ← uniqq_grad_inner, ← inner_sub_left]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right this (norm_nonneg _))
    have h2 : |ψ y - ψ x| ≤ Lψ * ‖x - y‖ := by
      have := ul4_lip_of_cb hψd hψL y x
      rwa [norm_sub_rev y x] at this
    have e : F j y - F j x = ψ y * (fderiv ℝ u y (ul1w M j) - fderiv ℝ u x (ul1w M j)) +
        (ψ y - ψ x) * fderiv ℝ u x (ul1w M j) := by simp only [hF]; ring
    rw [e]
    calc _ ≤ |ψ y * (fderiv ℝ u y (ul1w M j) - fderiv ℝ u x (ul1w M j))| +
          |(ψ y - ψ x) * fderiv ℝ u x (ul1w M j)| := abs_add_le _ _
      _ = |ψ y| * |fderiv ℝ u y (ul1w M j) - fderiv ℝ u x (ul1w M j)| +
          |ψ y - ψ x| * |fderiv ℝ u x (ul1w M j)| := by rw [abs_mul, abs_mul]
      _ ≤ Bψ * (H * ‖x - y‖ ^ β * ‖ul1w M j‖) + (Lψ * ‖x - y‖) * (G * ‖ul1w M j‖) := by
          gcongr
          · exact hψB y
          · exact hA j x
      _ ≤ Bψ * (H * ‖x - y‖ ^ β * ‖ul1w M j‖) + (Lψ * ‖x - y‖ ^ β) * (G * ‖ul1w M j‖) := by
          gcongr
      _ = _ := by ring
  have hcomp : ∀ j, (convGradConvW (rieszKernelGrad d s) (F j) x) j =
      ∫ y, (if ‖x - y‖ ≤ 1 / 4 then (F j y - F j x) * kap d s j (x - y)
        else F j y * kap d s j (x - y)) := fun j => ul1_conv_comp hs0 hsd j (hFc j) (hFi j) x
  have hrepr : ulNL s M ψ u x = ∑ j, (convGradConvW (rieszKernelGrad d s) (F j) x) j := by
    unfold ulNL
    simp only [ul1_matVec]
    rfl
  rw [hrepr]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j ∈ Finset.univ, |(convGradConvW (rieszKernelGrad d s) (F j) x) j| ≤
      (max 1 s * (Bψ + Lψ) * ‖ul1w M j‖ * Ib + max 1 s * 8 ^ (s + 1) * Iψ * ‖ul1w M j‖) * (G + H) := by
    intro j _
    rw [hcomp j]
    have hHF : 0 ≤ (Bψ * H + Lψ * G) * ‖ul1w M j‖ := by positivity
    have h1 := uniqq_cc_bound hs0 hsd hβ0 hβ1 hβs j (hFc j) (hFi j) hHF x (hHol j)
    refine h1.trans ?_
    have h2 : max 1 s * 8 ^ (s + 1) * ∫ y, |F j y| ≤ max 1 s * 8 ^ (s + 1) * (Iψ * (G * ‖ul1w M j‖)) :=
      mul_le_mul_of_nonneg_left (hFL1 j) (by positivity)
    have h3 : max 1 s * ((Bψ * H + Lψ * G) * ‖ul1w M j‖) * Ib ≤
        max 1 s * (Bψ + Lψ) * ‖ul1w M j‖ * Ib * (G + H) := by
      have : (Bψ * H + Lψ * G) ≤ (Bψ + Lψ) * (G + H) := by
        nlinarith [mul_nonneg hBψ0 hG, mul_nonneg hLψ0 hH]
      have hw := norm_nonneg (ul1w M j)
      calc max 1 s * ((Bψ * H + Lψ * G) * ‖ul1w M j‖) * Ib
          = max 1 s * ‖ul1w M j‖ * Ib * (Bψ * H + Lψ * G) := by ring
        _ ≤ max 1 s * ‖ul1w M j‖ * Ib * ((Bψ + Lψ) * (G + H)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have h4 : max 1 s * 8 ^ (s + 1) * (Iψ * (G * ‖ul1w M j‖)) ≤
        max 1 s * 8 ^ (s + 1) * Iψ * ‖ul1w M j‖ * (G + H) := by
      have hw := norm_nonneg (ul1w M j)
      calc max 1 s * 8 ^ (s + 1) * (Iψ * (G * ‖ul1w M j‖))
          = max 1 s * 8 ^ (s + 1) * Iψ * ‖ul1w M j‖ * G := by ring
        _ ≤ max 1 s * 8 ^ (s + 1) * Iψ * ‖ul1w M j‖ * (G + H) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc _ ≤ max 1 s * ((Bψ * H + Lψ * G) * ‖ul1w M j‖) * Ib +
          max 1 s * 8 ^ (s + 1) * (Iψ * (G * ‖ul1w M j‖)) := by
          have : max 1 s * ((Bψ * H + Lψ * G) * ‖ul1w M j‖) * Ib =
              max 1 s * (Bψ * H + Lψ * G) * ‖ul1w M j‖ * Ib := by ring
          nlinarith [h2]
      _ ≤ _ := by nlinarith [h3, h4]
  calc _ ≤ ∑ j : Fin d, (max 1 s * (Bψ + Lψ) * ‖ul1w M j‖ * Ib +
        max 1 s * 8 ^ (s + 1) * Iψ * ‖ul1w M j‖) * (G + H) := Finset.sum_le_sum hterm
    _ = KN * (G + H) := by rw [hKN, Finset.sum_mul]

end HRS.MS.UniqQ
