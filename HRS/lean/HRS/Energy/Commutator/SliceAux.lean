import HRS.Energy.Commutator.Basic

/-!
# Auxiliary lemmas for `Slice.lean` (packet CM-S1)

* the Laplace/Stieltjes swap `Γ(1-β) ∫ t^{β-1} h(t) dt = ∫ l^{-β} ∫ e^{-lt} h(t) dt dl`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

namespace SliceAux

/-- `∫_0^∞ l^{-β} e^{-lt} dl = Γ(1-β) t^{β-1}`. -/
theorem integral_laplace {β t : ℝ} (hβ : β < 1) (ht : 0 < t) :
    ∫ l in Ioi (0 : ℝ), l ^ (-β) * Real.exp (-(l * t)) = Real.Gamma (1 - β) * t ^ (β - 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 - β) (r := t) (by linarith) ht
  have e : (1 - β) - 1 = -β := by ring
  rw [e] at h
  have h' : ∫ l in Ioi (0 : ℝ), l ^ (-β) * Real.exp (-(l * t)) =
      ∫ l in Ioi (0 : ℝ), l ^ (-β) * Real.exp (-(t * l)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun l => ?_)
    simp only [mul_comm l t]
  rw [h', h, one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, mul_comm]
  congr 2; ring

theorem integrableOn_laplace {β t : ℝ} (hβ : β < 1) (ht : 0 < t) :
    IntegrableOn (fun l : ℝ => l ^ (-β) * Real.exp (-(l * t))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -β) (b := t)
    (by linarith) one_pos ht
  refine this.congr_fun (fun l _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring_nf

/-- The Laplace/Stieltjes swap. -/
theorem stieltjes_swap {β : ℝ} (h1 : β < 1) {h : ℝ → ℝ} (hc : ContinuousOn h (Ioi 0))
    (hi : IntegrableOn (fun t => t ^ (β - 1) * h t) (Ioi 0)) :
    IntegrableOn (fun l : ℝ => l ^ (-β) * ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * h t) (Ioi 0) ∧
    Real.Gamma (1 - β) * ∫ t in Ioi (0 : ℝ), t ^ (β - 1) * h t =
      ∫ l in Ioi (0 : ℝ), l ^ (-β) * ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * h t := by
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set F : ℝ × ℝ → ℝ := fun p => p.1 ^ (-β) * (Real.exp (-p.1 * p.2) * h p.2) with hF
  have hmeas : AEStronglyMeasurable F (μ.prod μ) := by
    rw [hμ, Measure.prod_restrict]
    refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod measurableSet_Ioi)
    refine ContinuousOn.mul ?_ (ContinuousOn.mul ?_ ?_)
    · exact (continuousOn_fst.rpow_const fun p hp => Or.inl (ne_of_gt hp.1))
    · fun_prop
    · exact hc.comp continuousOn_snd (fun p hp => hp.2)
  have hinner : ∀ t ∈ Ioi (0 : ℝ), ∫ l, ‖F (l, t)‖ ∂μ = |h t| * (Real.Gamma (1 - β) * t ^ (β - 1)) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have : ∀ l ∈ Ioi (0 : ℝ), ‖F (l, t)‖ = |h t| * (l ^ (-β) * Real.exp (-(l * t))) := by
      intro l hl
      have hl' : (0 : ℝ) < l := hl
      simp only [hF, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hl' _),
        abs_of_pos (Real.exp_pos _)]
      rw [neg_mul]; ring
    rw [hμ, setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul, integral_laplace h1 ht']
  have hint : Integrable F (μ.prod μ) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨?_, ?_⟩
    · rw [hμ, ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have this : IntegrableOn _ (Ioi (0:ℝ)) :=
        (integrableOn_laplace h1 (show (0:ℝ) < t from ht)).const_mul (h t)
      refine this.congr_fun (fun l _ => ?_) measurableSet_Ioi
      simp only [hF]; rw [neg_mul]; ring
    · have h2 : Integrable (fun t => |h t| * (Real.Gamma (1 - β) * t ^ (β - 1))) μ := by
        have this : IntegrableOn _ (Ioi (0:ℝ)) := (hi.norm).const_mul (Real.Gamma (1 - β))
        refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
        have ht' : (0:ℝ) < t := ht
        simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
        ring
      refine h2.congr ?_
      rw [hμ, EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall fun t ht => (hinner t ht).symm
  refine ⟨?_, ?_⟩
  · have := hint.integral_prod_left
    refine this.congr ?_
    refine Filter.Eventually.of_forall fun l => ?_
    simp only [hF, integral_const_mul]
  · have hswap := integral_integral_swap (f := fun l t => F (l, t)) (μ := μ) (ν := μ) hint
    have e1 : ∫ l, ∫ t, F (l, t) ∂μ ∂μ =
        ∫ l in Ioi (0 : ℝ), l ^ (-β) * ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * h t := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall fun l => ?_
      simp only [hF, hμ, integral_const_mul]
    have e2 : ∫ t, ∫ l, F (l, t) ∂μ ∂μ =
        Real.Gamma (1 - β) * ∫ t in Ioi (0 : ℝ), t ^ (β - 1) * h t := by
      rw [← integral_const_mul]
      rw [hμ]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht' : (0:ℝ) < t := ht
      have : ∀ l ∈ Ioi (0 : ℝ), F (l, t) = h t * (l ^ (-β) * Real.exp (-(l * t))) := by
        intro l _
        simp only [hF]; rw [neg_mul]; ring
      show ∫ l in Ioi (0 : ℝ), F (l, t) = _
      rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul, integral_laplace h1 ht']
      ring
    rw [← e1, ← e2]
    exact hswap.symm

/-- Scaling `u = b t` in the subordination integral. -/
theorem scale_integral {β b : ℝ} (hb : 0 < b) {H : ℝ → ℝ}
    (hi : IntegrableOn (fun u => u ^ (β - 1) * H u) (Ioi 0)) :
    IntegrableOn (fun t => t ^ (β - 1) * H (b * t)) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), u ^ (β - 1) * H u = b ^ β * ∫ t in Ioi (0 : ℝ), t ^ (β - 1) * H (b * t) := by
  have hpt : ∀ t : ℝ, 0 < t → (b * t) ^ (β - 1) * H (b * t) = b ^ (β - 1) * (t ^ (β - 1) * H (b * t)) := by
    intro t ht
    rw [Real.mul_rpow hb.le ht.le]; ring
  have hi' : IntegrableOn (fun t => (b * t) ^ (β - 1) * H (b * t)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun u => u ^ (β - 1) * H u) 0 hb).mpr
      (by simpa using hi)
    exact this
  have hbp : 0 < b ^ (β - 1) := Real.rpow_pos_of_pos hb _
  have hi2 : IntegrableOn (fun t => t ^ (β - 1) * H (b * t)) (Ioi 0) := by
    have this : IntegrableOn _ (Ioi (0:ℝ)) := hi'.const_mul (b ^ (β - 1))⁻¹
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    show (b ^ (β - 1))⁻¹ * ((b * t) ^ (β - 1) * H (b * t)) = _
    rw [hpt t ht]; field_simp
  refine ⟨hi2, ?_⟩
  have h := integral_comp_mul_left_Ioi (fun u => u ^ (β - 1) * H u) 0 hb
  simp only [mul_zero, smul_eq_mul] at h
  have h2 : ∫ t in Ioi (0 : ℝ), (b * t) ^ (β - 1) * H (b * t) =
      b ^ (β - 1) * ∫ t in Ioi (0 : ℝ), t ^ (β - 1) * H (b * t) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht => hpt t ht
  rw [h2] at h
  have e : b ^ (β - 1) = b ^ β / b := Real.rpow_sub_one hb.ne' β
  rw [e] at h
  field_simp at h
  linarith

/-- The bridge: subordination integral in `u` equals the Stieltjes mixture of the slice integrals
(`u = 4π² t`). -/
theorem bridge {β : ℝ} (h1 : β < 1) {H : ℝ → ℝ} (hc : ContinuousOn H (Ioi 0))
    (hi : IntegrableOn (fun u => u ^ (β - 1) * H u) (Ioi 0)) :
    IntegrableOn (fun l : ℝ => l ^ (-β) *
      ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * H (4 * Real.pi ^ 2 * t)) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), u ^ (β - 1) * H u =
      ((4 * Real.pi ^ 2) ^ β / Real.Gamma (1 - β)) *
        ∫ l in Ioi (0 : ℝ), l ^ (-β) * ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * H (4 * Real.pi ^ 2 * t) := by
  have hb : 0 < 4 * Real.pi ^ 2 := by positivity
  obtain ⟨hi2, he⟩ := scale_integral (β := β) hb hi
  have hc2 : ContinuousOn (fun t => H (4 * Real.pi ^ 2 * t)) (Ioi 0) := by
    refine hc.comp (continuousOn_const.mul continuousOn_id) fun t ht => ?_
    have : (0:ℝ) < t := ht
    show 0 < 4 * Real.pi ^ 2 * t
    positivity
  obtain ⟨hA, hB⟩ := stieltjes_swap h1 hc2 hi2
  refine ⟨hA, ?_⟩
  have hG : 0 < Real.Gamma (1 - β) := Real.Gamma_pos_of_pos (by linarith)
  rw [he, ← hB]
  field_simp

/-! ### Gradient machinery for `Ψ` (copied from `HRS/Kernel/GradSmooth.lean`, which is not imported here) -/

section PsiGrad

open HRS HRS.KernelAux HRS.KernelGrad
open scoped Real

variable {d : ℕ}

/-! ### Gradient of the subordination integrand, uniformly away from the origin -/

theorem norm_le_card_of_box {x : Euc d} (hx : ∀ i, |x i| ≤ 1/2) : ‖x‖ ≤ d := by
  have h := norm_toLp_le_sum (d := d) (WithLp.ofLp x)
  rw [WithLp.toLp_ofLp] at h
  refine h.trans ?_
  calc ∑ j, |(WithLp.ofLp x) j| ≤ ∑ _j : Fin d, (1 : ℝ) := Finset.sum_le_sum fun j _ => by
        have := hx j; linarith
    _ = d := by simp

theorem psiG_bound_unif (j : Fin d) {r : ℝ} (hr : 0 < r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Euc d, (∀ i, |x i| ≤ 1/2) → r ≤ ‖x‖ → ∀ u : ℝ, 0 < u →
      |psiG j (Torus.mk x) u| ≤ M * Real.exp (-u) := by
  obtain ⟨K, hK0, hK⟩ := psiG_small_bound (d := d) j
  obtain ⟨M1, hM10, hM1⟩ := psiG_large_bound (d := d) j
  set c0 := min (π ^ 2 * r ^ 2) (π ^ 2 / 8) with hc0
  have hc0p : 0 < c0 := lt_min (by positivity) (by positivity)
  set R : ℝ := (d : ℝ) with hR
  have hR0 : 0 ≤ R := by positivity
  set M0 := π ^ d * (2 * π ^ 2) * (R + K) * (((d + 1).factorial : ℝ) / c0 ^ (d + 1)) with hM0
  have hM00 : 0 ≤ M0 := by positivity
  refine ⟨M0 * Real.exp 1 + M1, by positivity, fun x hx hrx u hu => ?_⟩
  have hxR : ‖x‖ ≤ R := norm_le_card_of_box hx
  rcases le_total u 1 with h1 | h1
  · refine (hK x hx u hu h1).trans ?_
    set w := 1 / u with hw
    have hw0 : 0 < w := by positivity
    have hsq : Real.sqrt (π / u) ≤ π * w := by
      have h2 : 1 ≤ π / u := by rw [le_div_iff₀ hu]; linarith [Real.pi_gt_three]
      have h3 : Real.sqrt (π / u) ≤ π / u := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
      calc Real.sqrt (π / u) ≤ π / u := h3
        _ = π * w := by rw [hw]; ring
    have he1 : Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) ≤ Real.exp (-(c0 * w)) := by
      rw [Real.exp_le_exp, hw]
      have : c0 ≤ π ^ 2 * ‖x‖ ^ 2 := (min_le_left _ _).trans (by gcongr)
      have : c0 * (1 / u) ≤ π ^ 2 * ‖x‖ ^ 2 * (1 / u) := by gcongr
      have e : π ^ 2 * ‖x‖ ^ 2 / u = π ^ 2 * ‖x‖ ^ 2 * (1 / u) := by ring
      linarith
    have he2 : Real.exp (-(π ^ 2 / (8 * u))) ≤ Real.exp (-(c0 * w)) := by
      rw [Real.exp_le_exp, hw]
      have : c0 ≤ π ^ 2 / 8 := min_le_right _ _
      have : c0 * (1 / u) ≤ π ^ 2 / 8 * (1 / u) := by gcongr
      have e : π ^ 2 / (8 * u) = π ^ 2 / 8 * (1 / u) := by field_simp
      linarith
    have hpe := pow_exp_bound c0 hc0p (d + 1) w hw0.le
    have hfin : Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) *
        (‖x‖ * Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) + K * Real.exp (-(π ^ 2 / (8 * u)))) ≤ M0 := by
      have hxe : ‖x‖ * Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) ≤ R * Real.exp (-(c0 * w)) :=
        mul_le_mul hxR he1 (Real.exp_pos _).le hR0
      calc Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) *
            (‖x‖ * Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) + K * Real.exp (-(π ^ 2 / (8 * u))))
          ≤ (π * w) ^ d * (2 * π ^ 2 * w) * (R * Real.exp (-(c0 * w)) + K * Real.exp (-(c0 * w))) := by
            have e : 2 * π ^ 2 / u = 2 * π ^ 2 * w := by rw [hw]; ring
            rw [e]
            have hK' : K * Real.exp (-(π ^ 2 / (8 * u))) ≤ K * Real.exp (-(c0 * w)) := by gcongr
            have hs' : Real.sqrt (π / u) ^ d ≤ (π * w) ^ d := by gcongr
            gcongr
        _ = π ^ d * (2 * π ^ 2) * (R + K) * (w ^ (d + 1) * Real.exp (-(c0 * w))) := by ring
        _ ≤ M0 := by rw [hM0]; gcongr
    have : 1 ≤ Real.exp 1 * Real.exp (-u) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; linarith
    nlinarith [Real.exp_pos (-u), Real.exp_pos 1]
  · refine (hM1 _ u h1).trans ?_
    have : 0 ≤ M0 * Real.exp 1 * Real.exp (-u) := by positivity
    nlinarith [Real.exp_pos (-u)]

/-- the gradient (a continuous linear functional) of `y ↦ Ψ(t, mk y)` -/
def psiGrad (y : Euc d) (t : ℝ) : Euc d →L[ℝ] ℝ :=
  ∑ j, psiG j (Torus.mk y) t • (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)

theorem psiGrad_apply (y : Euc d) (t : ℝ) (v : Euc d) :
    psiGrad y t v = ∑ j, psiG j (Torus.mk y) t * v j := by
  simp [psiGrad, ContinuousLinearMap.sum_apply]

theorem summable_psiG_term (j : Fin d) {t : ℝ} (ht : 0 < t) (x : Torus d) :
    Summable fun k : Lattice d =>
      -(Real.exp (-t * Lattice.enorm k ^ 2) * (2 * π * ((k j : ℤ) : ℝ)) * Torus.sinMode k x) := by
  refine Summable.of_norm_bounded ((summable_pow_gauss_lattice d ht 1).mul_left (2 * π)) fun k => ?_
  rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  have h1 := abs_coord_le_enorm k j
  have hk0 : 0 ≤ Lattice.enorm k := norm_nonneg _
  have h2 : |Torus.sinMode k x| ≤ 1 := by
    rw [Torus.sinMode]; exact (Complex.abs_im_le_norm _).trans (by rw [Torus.norm_mode])
  calc Real.exp (-t * Lattice.enorm k ^ 2) * (2 * π * |((k j : ℤ) : ℝ)|) * |Torus.sinMode k x|
      ≤ Real.exp (-t * Lattice.enorm k ^ 2) * (2 * π * Lattice.enorm k) * 1 := by gcongr
    _ = _ := by ring

theorem hasFDerivAt_psiFn {t : ℝ} (ht : 0 < t) (y : Euc d) :
    HasFDerivAt (fun y : Euc d => psiFn (Torus.mk y) t) (psiGrad y t) y := by
  set f : Lattice d → Euc d → ℝ := fun k y =>
    if k = 0 then 0 else Real.exp (-t * Lattice.enorm k ^ 2) * Real.cos (Torus.freqFunctional k y) with hf
  set f' : Lattice d → Euc d → (Euc d →L[ℝ] ℝ) := fun k y =>
    if k = 0 then 0 else (-(Real.exp (-t * Lattice.enorm k ^ 2) * Real.sin (Torus.freqFunctional k y))) •
      Torus.freqFunctional k with hf'
  have hfeq : (fun y : Euc d => psiFn (Torus.mk y) t) = fun y => ∑' k, f k y := by
    funext y
    unfold psiFn
    refine tsum_congr fun k => ?_
    by_cases hk : k = 0
    · simp [hf, hk]
    · simp only [hf, hk, if_false, Torus.cosMode_mk, Torus.freqFunctional_apply]
  have hder : ∀ k y, HasFDerivAt (f k) (f' k y) y := by
    intro k y
    by_cases hk : k = 0
    · simp only [hf, hf', hk, if_true]; exact hasFDerivAt_const _ _
    · simp only [hf, hf', hk, if_false]
      have h1 := (Real.hasDerivAt_cos (Torus.freqFunctional k y)).comp_hasFDerivAt y
        (Torus.freqFunctional k).hasFDerivAt
      have h2 := h1.const_mul (Real.exp (-t * Lattice.enorm k ^ 2))
      have h3 : HasFDerivAt (fun y => Real.exp (-t * Lattice.enorm k ^ 2) *
          Real.cos (Torus.freqFunctional k y))
          (Real.exp (-t * Lattice.enorm k ^ 2) • (-Real.sin (Torus.freqFunctional k y) • Torus.freqFunctional k)) y := h2
      convert h3 using 1
      simp only [smul_smul, mul_neg]
  have hbd : ∀ k y, ‖f' k y‖ ≤ 2 * π * (Lattice.enorm k ^ 1 * Real.exp (-t * Lattice.enorm k ^ 2)) := by
    intro k y
    by_cases hk : k = 0
    · subst hk
      simp only [hf', if_true, norm_zero]
      have : 0 ≤ Lattice.enorm (0 : Lattice d) := norm_nonneg _
      exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg this _) (Real.exp_pos _).le)
    · simp only [hf', hk, if_false]
      rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 := Real.abs_sin_le_one (Torus.freqFunctional k y)
      have h2 := Torus.norm_freqFunctional_le k
      have hk0 : 0 ≤ Lattice.enorm k := norm_nonneg _
      calc Real.exp (-t * Lattice.enorm k ^ 2) * |Real.sin (Torus.freqFunctional k y)| *
            ‖Torus.freqFunctional k‖
          ≤ Real.exp (-t * Lattice.enorm k ^ 2) * 1 * (2 * π * Lattice.enorm k) := by gcongr
        _ = _ := by ring
  have hf0 : Summable fun k => f k y := by
    refine (psi_summable (Torus.mk y) ht).congr fun k => ?_
    by_cases hk : k = 0
    · simp [hf, hk]
    · simp only [hf, hk, if_false, Torus.cosMode_mk, Torus.freqFunctional_apply]
  have hH := hasFDerivAt_tsum ((summable_pow_gauss_lattice d ht 1).mul_left (2 * π)) hder hbd hf0 y
  rw [hfeq]
  convert hH using 1
  -- identify the derivative
  have hsumm : Summable fun k => f' k y :=
    Summable.of_norm_bounded ((summable_pow_gauss_lattice d ht 1).mul_left (2 * π)) (hbd · y)
  ext v
  rw [psiGrad_apply]
  have hv : (∑' k, f' k y) v = ∑' k, f' k y v := by
    have := (ContinuousLinearMap.apply ℝ ℝ v).map_tsum hsumm
    simpa using this
  rw [hv]
  have hpsi : ∀ j, psiG j (Torus.mk y) t * v j =
      ∑' k, -(Real.exp (-t * Lattice.enorm k ^ 2) * (2 * π * ((k j : ℤ) : ℝ)) * Torus.sinMode k (Torus.mk y)) * v j := by
    intro j
    unfold psiG
    rw [tsum_mul_right]
  simp_rw [hpsi]
  rw [← Summable.tsum_finsetSum (fun j _ => (summable_psiG_term j ht (Torus.mk y)).mul_right (v j))]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · simp [hf', hk]
  · simp only [hf', hk, if_false, ContinuousLinearMap.smul_apply, smul_eq_mul, Torus.freqFunctional_apply,
      Torus.sinMode_mk, Lattice.dot, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_lattice_of_mk_eq {x y : Euc d} (h : Torus.mk x = Torus.mk y) :
    ∃ m : Lattice d, x = y + Lattice.toEuc m := by
  have : ∀ i, ∃ n : ℤ, (n : ℝ) = x i - y i := by
    intro i
    have hi := congrFun h i
    simp only [Torus.mk] at hi
    have : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, hi, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp this
    exact ⟨n, by simpa using hn⟩
  choose m hm using this
  refine ⟨m, ?_⟩
  ext i
  simp [Lattice.toEuc, hm]

theorem norm_sub_toEuc_ge_of_box {x : Euc d} (hx : ∀ i, |x i| ≤ 1/2) (m : Lattice d) :
    ‖x‖ ≤ ‖x - Lattice.toEuc m‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  simp only [Real.norm_eq_abs, sq_abs, Lattice.toEuc]
  have := abs_sq_le_sub_sq (x i) (hx i) (m i)
  simp only [PiLp.sub_apply]
  nlinarith [sq_abs (x i)]

/-- uniform bound for the gradient of the subordination integrand near a point of the box
(not the origin). -/
theorem psiG_bound_near (j : Fin d) {x0 : Euc d} (hx0 : ∀ i, |x0 i| ≤ 1/2) (hx0n : x0 ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Euc d, ‖y - x0‖ < ‖x0‖ / 2 → ∀ u : ℝ, 0 < u →
      |psiG j (Torus.mk y) u| ≤ M * Real.exp (-u) := by
  have hρ : 0 < ‖x0‖ := norm_pos_iff.mpr hx0n
  obtain ⟨M, hM0, hM⟩ := psiG_bound_unif (d := d) j (r := ‖x0‖ / 2) (by positivity)
  refine ⟨M, hM0, fun y hy u hu => ?_⟩
  obtain ⟨x, hxm, hxb⟩ := exists_mk_box (Torus.mk y)
  obtain ⟨m, hm⟩ := exists_lattice_of_mk_eq hxm
  have hneg : Lattice.toEuc (-m) = -Lattice.toEuc m := by ext i; simp [Lattice.toEuc]
  have h1 : ‖x0‖ ≤ ‖x0 + Lattice.toEuc m‖ := by
    have := norm_sub_toEuc_ge_of_box hx0 (-m)
    rwa [hneg, sub_neg_eq_add] at this
  have h3 : ‖x0 + Lattice.toEuc m‖ ≤ ‖x0 - y‖ + ‖y + Lattice.toEuc m‖ := by
    have := norm_add_le (x0 - y) (y + Lattice.toEuc m)
    rwa [show x0 - y + (y + Lattice.toEuc m) = x0 + Lattice.toEuc m by abel] at this
  have h4 : ‖x0 - y‖ = ‖y - x0‖ := norm_sub_rev _ _
  have hr : ‖x0‖ / 2 ≤ ‖x‖ := by rw [hm]; linarith
  have := hM x hxb hr u hu
  rwa [hxm] at this

theorem norm_psiGrad_le (y : Euc d) (t : ℝ) : ‖psiGrad y t‖ ≤ ∑ j, |psiG j (Torus.mk y) t| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ => abs_nonneg _) fun v => ?_
  rw [psiGrad_apply, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  gcongr
  have := PiLp.norm_apply_le v j
  rwa [Real.norm_eq_abs] at this

theorem mk_ne_zero_ne_zero {x : Euc d} (h : Torus.mk x ≠ 0) : x ≠ 0 := by
  intro hx
  apply h
  rw [hx]
  funext i
  simp [Torus.mk]

/-- Differentiation of the slice kernel under the integral sign (at a point of the box). -/
theorem hasFDerivAt_slice_box {l : ℝ} (hl : 0 ≤ l) {x0 : Euc d} (hx0 : ∀ i, |x0 i| ≤ 1/2)
    (hx0n : Torus.mk x0 ≠ 0) :
    HasFDerivAt (fun y : Euc d => ∫ t in Ioi (0 : ℝ),
        Real.exp (-l * t) * psiFn (Torus.mk y) (4 * Real.pi ^ 2 * t))
      (∑ j, (∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiG j (Torus.mk x0) (4 * Real.pi ^ 2 * t)) •
        (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)) x0 := by
  have hb : 0 < 4 * Real.pi ^ 2 := by positivity
  set b : ℝ := 4 * Real.pi ^ 2 with hb_def
  have hx0z : x0 ≠ 0 := mk_ne_zero_ne_zero hx0n
  have hρ : 0 < ‖x0‖ := norm_pos_iff.mpr hx0z
  choose M hM0 hM using fun j : Fin d => psiG_bound_near j hx0 hx0z
  set C : ℝ := ∑ j, M j with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => hM0 j
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-(b * t))) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -b) (by linarith) (0 : ℝ)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [neg_mul]
  have hbdint : Integrable (fun t : ℝ => C * Real.exp (-(b * t))) (volume.restrict (Ioi (0:ℝ))) :=
    hexp.const_mul C
  have hcontF : ∀ y : Euc d, ContinuousOn
      (fun t : ℝ => Real.exp (-l * t) * psiFn (Torus.mk y) (b * t)) (Ioi 0) := by
    intro y
    refine (by fun_prop : Continuous fun t : ℝ => Real.exp (-l * t)).continuousOn.mul ?_
    refine (psi_continuousOn _).comp (continuousOn_const.mul continuousOn_id) fun t ht => ?_
    have : (0:ℝ) < t := ht
    show 0 < b * t
    positivity
  have hcontF' : ContinuousOn (fun t : ℝ => Real.exp (-l * t) • psiGrad x0 (b * t)) (Ioi 0) := by
    have : (fun t : ℝ => Real.exp (-l * t) • psiGrad x0 (b * t)) =
        fun t => ∑ j, (Real.exp (-l * t) * psiG j (Torus.mk x0) (b * t)) •
          (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) := by
      funext t
      simp only [psiGrad, Finset.smul_sum, smul_smul, smul_eq_mul]
    rw [this]
    refine continuousOn_finset_sum _ fun j _ => ?_
    have hc1 : ContinuousOn (fun t : ℝ => Real.exp (-l * t) * psiG j (Torus.mk x0) (b * t)) (Ioi 0) := by
      refine (by fun_prop : Continuous fun t : ℝ => Real.exp (-l * t)).continuousOn.mul ?_
      refine (psiG_continuousOn j _).comp (continuousOn_const.mul continuousOn_id) fun t ht => ?_
      have : (0:ℝ) < t := ht
      show 0 < b * t
      positivity
    exact hc1.smul continuousOn_const
  obtain ⟨M0, hM00, hM0b⟩ := psi_bound (Torus.mk x0) hx0n
  have hint0 : Integrable (fun t : ℝ => Real.exp (-l * t) * psiFn (Torus.mk x0) (b * t))
      (volume.restrict (Ioi (0:ℝ))) := by
    refine Integrable.mono' (hexp.const_mul M0) ((hcontF x0).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : (0:ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 := hM0b (b * t) (by positivity)
    have h2 : Real.exp (-l * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    calc Real.exp (-l * t) * |psiFn (Torus.mk x0) (b * t)|
        ≤ 1 * (M0 * Real.exp (-(b * t))) := by gcongr
      _ = _ := by ring
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun (y : Euc d) (t : ℝ) => Real.exp (-l * t) * psiFn (Torus.mk y) (b * t))
    (F' := fun (y : Euc d) (t : ℝ) => Real.exp (-l * t) • psiGrad y (b * t))
    (x₀ := x0) (s := Metric.ball x0 (‖x0‖ / 2))
    (bound := fun t => C * Real.exp (-(b * t)))
    (Metric.ball_mem_nhds _ (by positivity))
    (Filter.Eventually.of_forall fun y => (hcontF y).aestronglyMeasurable measurableSet_Ioi)
    hint0
    (hcontF'.aestronglyMeasurable measurableSet_Ioi)
    ?_ hbdint ?_
  · convert key using 1
    have hint : ∀ j, Integrable (fun t : ℝ => Real.exp (-l * t) * psiG j (Torus.mk x0) (b * t))
        (volume.restrict (Ioi (0:ℝ))) := by
      intro j
      refine Integrable.mono' (hexp.const_mul (M j)) ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        refine (by fun_prop : Continuous fun t : ℝ => Real.exp (-l * t)).continuousOn.mul ?_
        refine (psiG_continuousOn j _).comp (continuousOn_const.mul continuousOn_id) fun t ht => ?_
        have : (0:ℝ) < t := ht
        show 0 < b * t
        positivity
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
        have ht' : (0:ℝ) < t := ht
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have h1 := hM j x0 (by simpa using hρ) (b * t) (by positivity)
        have h2 : Real.exp (-l * t) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith
        calc Real.exp (-l * t) * |psiG j (Torus.mk x0) (b * t)|
            ≤ 1 * (M j * Real.exp (-(b * t))) := by gcongr
          _ = _ := by ring
    have : (fun t : ℝ => Real.exp (-l * t) • psiGrad x0 (b * t)) =
        fun t => ∑ j, (Real.exp (-l * t) * psiG j (Torus.mk x0) (b * t)) •
          (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) := by
      funext t
      simp only [psiGrad, Finset.smul_sum, smul_smul, smul_eq_mul]
    rw [this, integral_finsetSum _ fun j _ => (hint j).smul_const _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul_const]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht y hy => ?_)
    have ht' : (0:ℝ) < t := ht
    have hy' : ‖y - x0‖ < ‖x0‖ / 2 := by simpa [dist_eq_norm] using hy
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h2 : Real.exp (-l * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    calc Real.exp (-l * t) * ‖psiGrad y (b * t)‖
        ≤ 1 * ∑ j, |psiG j (Torus.mk y) (b * t)| := by
          gcongr; exact norm_psiGrad_le y (b * t)
      _ ≤ 1 * ∑ j, (M j * Real.exp (-(b * t))) := by
          gcongr with j _
          simpa using hM j y hy' (b * t) (by positivity)
      _ = _ := by rw [← Finset.sum_mul]; ring
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht y _ => ?_)
    have ht' : (0:ℝ) < t := ht
    exact (hasFDerivAt_psiFn (by positivity : 0 < b * t) y).const_mul (Real.exp (-l * t)) |>.congr_fderiv
      (by simp [smul_eq_mul])

theorem mk_toEuc' (m : Lattice d) : Torus.mk (Lattice.toEuc m) = 0 := by
  funext i
  simp [Torus.mk, Lattice.toEuc]

/-- Differentiation of the slice kernel, at an arbitrary lift `y0` of a point `≠ 0`. -/
theorem hasFDerivAt_slice {l : ℝ} (hl : 0 ≤ l) {y0 : Euc d} (hy0 : Torus.mk y0 ≠ 0) :
    HasFDerivAt (fun y : Euc d => ∫ t in Ioi (0 : ℝ),
        Real.exp (-l * t) * psiFn (Torus.mk y) (4 * Real.pi ^ 2 * t))
      (∑ j, (∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiG j (Torus.mk y0) (4 * Real.pi ^ 2 * t)) •
        (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)) y0 := by
  obtain ⟨x0, hxm, hxb⟩ := exists_mk_box (Torus.mk y0)
  obtain ⟨m, hm⟩ := exists_lattice_of_mk_eq hxm
  have hx0n : Torus.mk x0 ≠ 0 := by rw [hxm]; exact hy0
  have h := hasFDerivAt_slice_box hl hxb hx0n
  rw [hxm] at h
  have hadd : HasFDerivAt (fun y : Euc d => y + Lattice.toEuc m) (ContinuousLinearMap.id ℝ (Euc d)) y0 :=
    (hasFDerivAt_id y0).add_const _
  have hm' : y0 + Lattice.toEuc m = x0 := hm.symm
  have h' : HasFDerivAt (fun y : Euc d => ∫ t in Ioi (0 : ℝ),
        Real.exp (-l * t) * psiFn (Torus.mk y) (4 * Real.pi ^ 2 * t))
      (∑ j, (∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiG j (Torus.mk y0) (4 * Real.pi ^ 2 * t)) •
        (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)) (y0 + Lattice.toEuc m) := by
    rw [hm']; exact h
  have h2 := (h'.comp y0 hadd).congr_fderiv (ContinuousLinearMap.comp_id _)
  have hfun : (fun y : Euc d => ∫ t in Ioi (0 : ℝ),
        Real.exp (-l * t) * psiFn (Torus.mk (y + Lattice.toEuc m)) (4 * Real.pi ^ 2 * t)) =
      fun y => ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiFn (Torus.mk y) (4 * Real.pi ^ 2 * t) := by
    funext y
    rw [Torus.mk_add, mk_toEuc', add_zero]
  exact hfun ▸ h2

theorem integrableOn_psiG {a : ℝ} (ha : 0 < a) (j : Fin d) {x : Torus d} (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * psiG j x t) (Ioi 0) := by
  obtain ⟨xe, rfl, hxe⟩ := exists_mk_box x
  obtain ⟨M, hM0, hM⟩ := psiG_bound j xe hxe (mk_ne_zero_ne_zero hx)
  refine Integrable.mono' ((Real.GammaIntegral_convergent ha).const_mul M) ?_ ?_
  · exact (ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht))
      (psiG_continuousOn j _)).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : (0:ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
    have h1 := hM t ht'
    calc t ^ (a - 1) * |psiG j (Torus.mk xe) t| ≤ t ^ (a - 1) * (M * Real.exp (-t)) := by gcongr
      _ = _ := by ring

/-- Absolute version of `KernelGrad.heat_comp_bound`: the subordination integral of `|∂_jΨ|`. -/
theorem psiG_abs_bound {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (j : Fin d) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ y : Euc d, (∀ i, |y i| ≤ 1 / 2) → y ≠ 0 →
      IntegrableOn (fun t : ℝ => t ^ (((d : ℝ) - s) / 2 - 1) * |psiG j (Torus.mk y) t|) (Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), t ^ (((d : ℝ) - s) / 2 - 1) * |psiG j (Torus.mk y) t| ≤
        C1 * ‖y‖ ^ (-s - 1) + C2 := by
  obtain ⟨K, hK0, hK⟩ := psiG_small_bound (d := d) j
  obtain ⟨M1, hM10, hM1⟩ := psiG_large_bound (d := d) j
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set n : ℝ := (d:ℝ) / 2 + 1 with hn_def
  have hn : 0 < n := by rw [hn_def]; positivity
  have han : a < n := by rw [ha_def, hn_def]; linarith
  set c : ℝ := n ^ n * Real.exp (-n) with hc_def
  have hc0 : 0 ≤ c := by positivity
  set P : ℝ := 2 * π ^ 2 * Real.sqrt π ^ d with hP
  have hP0 : 0 ≤ P := by positivity
  set C0 : ℝ := ∫ v in Ioi (0:ℝ), v ^ (a - 1) * min c (v ^ (-n)) with hC0
  have hC00 : 0 ≤ C0 := by
    refine setIntegral_nonneg measurableSet_Ioi fun v hv => ?_
    have hv0 : (0:ℝ) < v := hv
    have := le_min hc0 (Real.rpow_nonneg hv0.le (-n))
    have := Real.rpow_pos_of_pos hv0 (a - 1)
    positivity
  set θ2 : ℝ := π ^ 2 / 8 with hθ2
  have hθ2p : 0 < θ2 := by positivity
  refine ⟨P * C0 * π ^ (-(s + 2)), P * K * (θ2 ^ (a - n) * C0) + M1 * Real.Gamma a,
    by positivity, by have := (Real.Gamma_pos_of_pos ha).le; positivity,
    fun y hy hy0 => ?_⟩
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  set θ1 : ℝ := π ^ 2 * ‖y‖ ^ 2 with hθ1
  have hθ1p : 0 < θ1 := by positivity
  set m1 : ℝ → ℝ := fun u => min (c * θ1 ^ (-n)) (u ^ (-n)) with hm1
  set m2 : ℝ → ℝ := fun u => min (c * θ2 ^ (-n)) (u ^ (-n)) with hm2
  set Bm : ℝ → ℝ := fun t => P * ‖y‖ * m1 t + P * K * m2 t + M1 * Real.exp (-t) with hBm
  -- antitone majorants
  have hmono : ∀ (X : ℝ) {t u : ℝ}, 0 < t → t ≤ u → min X (u ^ (-n)) ≤ min X (t ^ (-n)) := by
    intro X t u ht htu
    exact min_le_min_left _ (Real.rpow_le_rpow_of_nonpos ht htu (by linarith))
  have hexpmin : ∀ (θ : ℝ), 0 < θ → ∀ u : ℝ, 0 < u →
      u ^ (-n) * Real.exp (-θ / u) ≤ min (c * θ ^ (-n)) (u ^ (-n)) := by
    intro θ hθ u hu
    refine le_min (t_pow_exp_bound hn hθ hu) ?_
    have : Real.exp (-θ / u) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ θ / u := by positivity
      rw [neg_div]; linarith
    have hp := Real.rpow_nonneg hu.le (-n)
    nlinarith
  have hpsi : ∀ u : ℝ, 0 < u → |psiG j (Torus.mk y) u| ≤ Bm u := by
    intro u hu
    have h1 : 0 ≤ P * ‖y‖ * m1 u := by
      have := le_min (mul_nonneg hc0 (Real.rpow_nonneg hθ1p.le (-n))) (Real.rpow_nonneg hu.le (-n))
      positivity
    have h2 : 0 ≤ P * K * m2 u := by
      have := le_min (mul_nonneg hc0 (Real.rpow_nonneg hθ2p.le (-n))) (Real.rpow_nonneg hu.le (-n))
      positivity
    have h3 : 0 ≤ M1 * Real.exp (-u) := by positivity
    rcases le_or_gt u 1 with hu1 | hu1
    · have h := hK y hy u hu hu1
      have hpow : Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) = P * u ^ (-n) := by
        rw [sqrt_div_pow_eq d hu, hP, div_eq_mul_inv (2 * π ^ 2), ← Real.rpow_neg_one u,
          hn_def]
        have : Real.sqrt π ^ d * u ^ (-(d:ℝ)/2) * (2 * π ^ 2 * u ^ (-1:ℝ)) =
            2 * π ^ 2 * Real.sqrt π ^ d * (u ^ (-(d:ℝ)/2) * u ^ (-1:ℝ)) := by ring
        rw [this, ← Real.rpow_add hu]
        congr 2; ring
      have e1 : Real.exp (-(π ^ 2 * ‖y‖ ^ 2 / u)) = Real.exp (-θ1 / u) := by rw [hθ1, neg_div]
      have e2 : Real.exp (-(π ^ 2 / (8 * u))) = Real.exp (-θ2 / u) := by
        rw [hθ2]; congr 1; field_simp
      rw [hpow, e1, e2] at h
      refine h.trans ?_
      have k1 := hexpmin θ1 hθ1p u hu
      have k2 := hexpmin θ2 hθ2p u hu
      have : P * u ^ (-n) * (‖y‖ * Real.exp (-θ1 / u) + K * Real.exp (-θ2 / u)) =
          P * ‖y‖ * (u ^ (-n) * Real.exp (-θ1 / u)) + P * K * (u ^ (-n) * Real.exp (-θ2 / u)) := by ring
      rw [this]
      simp only [hBm]
      have := mul_le_mul_of_nonneg_left k1 (mul_nonneg hP0 hr.le)
      have := mul_le_mul_of_nonneg_left k2 (mul_nonneg hP0 hK0)
      simp only [hm1, hm2]
      linarith
    · have h := hM1 (Torus.mk y) u hu1.le
      refine h.trans ?_
      simp only [hBm]
      linarith [mul_comm M1 (Real.exp (-u))]
  -- integrals
  obtain ⟨hi1, hv1⟩ := integral_min_rpow ha han hc0 hθ1p
  obtain ⟨hi2, hv2⟩ := integral_min_rpow ha han hc0 hθ2p
  have hGi := Real.GammaIntegral_convergent ha
  have heq : ∀ t : ℝ, t ^ (a - 1) * Bm t = P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n))) +
      P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n))) +
      M1 * (Real.exp (-t) * t ^ (a - 1)) := by
    intro t; simp only [hBm, hm1, hm2]; ring
  have hBi : IntegrableOn (fun t => t ^ (a - 1) * Bm t) (Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ => P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n))) +
      P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n))) +
      M1 * (Real.exp (-t) * t ^ (a - 1))) (Ioi 0) :=
      ((hi1.const_mul _).add (hi2.const_mul _)).add (hGi.const_mul _)
    exact h.congr_fun (fun t _ => (heq t).symm) measurableSet_Ioi
  have hBint : ∫ t in Ioi (0:ℝ), t ^ (a - 1) * Bm t =
      P * ‖y‖ * (θ1 ^ (a - n) * C0) + P * K * (θ2 ^ (a - n) * C0) + M1 * Real.Gamma a := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => heq t)]
    have f1 : IntegrableOn (fun t : ℝ => P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n)))) (Ioi 0) :=
      hi1.const_mul _
    have f2 : IntegrableOn (fun t : ℝ => P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n)))) (Ioi 0) :=
      hi2.const_mul _
    have f3 : IntegrableOn (fun t : ℝ => M1 * (Real.exp (-t) * t ^ (a - 1))) (Ioi 0) := hGi.const_mul _
    have f12 : IntegrableOn (fun t : ℝ => P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n))) +
        P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n)))) (Ioi 0) := f1.add f2
    rw [integral_add f12 f3, integral_add f1 f2, integral_const_mul, integral_const_mul,
      integral_const_mul, hv1, hv2, ← Real.Gamma_eq_integral ha]
  have hpsiI : IntegrableOn (fun t : ℝ => t ^ (a - 1) * |psiG j (Torus.mk y) t|) (Ioi 0) := by
    refine Integrable.mono' hBi ?_ ?_
    · exact (ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht))
        (psiG_continuousOn j _).abs).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have ht0 : (0:ℝ) < t := ht
      have hp := Real.rpow_pos_of_pos ht0 (a - 1)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hpsi t ht0) hp.le
  have hθ1pow : ‖y‖ * θ1 ^ (a - n) = π ^ (-(s + 2)) * ‖y‖ ^ (-s - 1) := by
    have hexp : a - n = -(s / 2 + 1) := by rw [ha_def, hn_def]; ring
    rw [hexp, hθ1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le, ← Real.rpow_mul hr.le]
    have e3 : ‖y‖ * (π ^ ((2:ℕ) * -(s / 2 + 1) : ℝ) * ‖y‖ ^ ((2:ℕ) * -(s / 2 + 1) : ℝ)) =
        π ^ ((2:ℕ) * -(s / 2 + 1) : ℝ) * (‖y‖ ^ (1:ℝ) * ‖y‖ ^ ((2:ℕ) * -(s / 2 + 1) : ℝ)) := by
      rw [Real.rpow_one]; ring
    rw [e3, ← Real.rpow_add hr]
    congr 2 <;> push_cast <;> ring
  refine ⟨hpsiI, ?_⟩
  have hle : ∫ t in Ioi (0:ℝ), t ^ (a - 1) * |psiG j (Torus.mk y) t| ≤
      ∫ t in Ioi (0:ℝ), t ^ (a - 1) * Bm t := by
    refine setIntegral_mono_on hpsiI hBi measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) < t := ht
    have hp := Real.rpow_pos_of_pos ht0 (a - 1)
    exact mul_le_mul_of_nonneg_left (hpsi t ht0) hp.le
  refine hle.trans ?_
  rw [hBint]
  have e : P * ‖y‖ * (θ1 ^ (a - n) * C0) = P * C0 * (π ^ (-(s + 2)) * ‖y‖ ^ (-s - 1)) := by
    rw [← hθ1pow]; ring
  linarith [e]

/-- The `j`-th component of the slice force, `∫_0^∞ e^{-lt} ∂_jΨ(z,4π²t) dt`. -/
def sgc (j : Fin d) (l : ℝ) (z : Torus d) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiG j z (4 * Real.pi ^ 2 * t)

theorem measurable_psiG_uncurry (j : Fin d) :
    Measurable fun p : Torus d × ℝ => psiG j p.1 p.2 := by
  unfold psiG
  refine Measurable.tsum fun k => ?_
  have h1 : Continuous fun p : Torus d × ℝ => Real.exp (-p.2 * Lattice.enorm k ^ 2) :=
    Real.continuous_exp.comp (continuous_snd.neg.mul continuous_const)
  have h2 : Continuous fun p : Torus d × ℝ => Torus.sinMode k p.1 :=
    (Torus.continuous_sinMode k).comp continuous_fst
  exact (((h1.mul continuous_const).mul h2).neg).measurable

theorem measurable_sgc (j : Fin d) : Measurable fun p : ℝ × Torus d => sgc j p.1 p.2 := by
  unfold sgc
  have hm : Measurable fun q : (ℝ × Torus d) × ℝ =>
      Real.exp (-q.1.1 * q.2) * psiG j q.1.2 (4 * Real.pi ^ 2 * q.2) := by
    refine Measurable.mul (by fun_prop) ?_
    exact (measurable_psiG_uncurry j).comp (measurable_fst.snd.prodMk (measurable_const.mul measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

theorem abs_sgc_le (j : Fin d) {l : ℝ} (z : Torus d) :
    |sgc j l z| ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * |psiG j z (4 * Real.pi ^ 2 * t)| := by
  unfold sgc
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- Absolute bound on the Stieltjes mixture of the slice forces. -/
theorem slice_abs_bound {s : ℝ} (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin d) (z : Torus d), z ≠ 0 →
      IntegrableOn (fun l : ℝ => l ^ (-(((d : ℝ) - s) / 2)) * |sgc j l z|) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-(((d : ℝ) - s) / 2)) * |sgc j l z| ≤
        C * (KernelGrad.tdist z 0 ^ (-s - 1) + 1) := by
  set β : ℝ := ((d : ℝ) - s) / 2 with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hβ1 : β < 1 := by rw [hβ]; linarith
  have hb : 0 < 4 * Real.pi ^ 2 := by positivity
  have hG : 0 < Real.Gamma (1 - β) := Real.Gamma_pos_of_pos (by linarith)
  choose C1 C2 hC1 hC2 hC using fun j : Fin d => psiG_abs_bound hs0 hsd j
  set Cs : ℝ := ∑ j, (C1 j + C2 j) with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun j _ => add_nonneg (hC1 j) (hC2 j)
  refine ⟨Real.Gamma (1 - β) * (4 * Real.pi ^ 2) ^ (-β) * Cs, by positivity, fun j z hz => ?_⟩
  obtain ⟨y, rfl, hy⟩ := exists_mk_box z
  have hy0 : y ≠ 0 := mk_ne_zero_ne_zero hz
  obtain ⟨hI, hJ⟩ := hC j y hy hy0
  set H : ℝ → ℝ := fun u => |psiG j (Torus.mk y) u| with hH
  have hcH : ContinuousOn H (Ioi 0) := (psiG_continuousOn j _).abs
  have hi : IntegrableOn (fun u => u ^ (β - 1) * H u) (Ioi 0) := hI
  obtain ⟨hi2, he⟩ := scale_integral (β := β) hb hi
  have hcH2 : ContinuousOn (fun t => H (4 * Real.pi ^ 2 * t)) (Ioi 0) := by
    refine hcH.comp (continuousOn_const.mul continuousOn_id) fun t ht => ?_
    have : (0:ℝ) < t := ht
    show 0 < 4 * Real.pi ^ 2 * t
    positivity
  obtain ⟨hA, hB⟩ := stieltjes_swap hβ1 hcH2 hi2
  have hmeas : AEStronglyMeasurable (fun l : ℝ => l ^ (-β) * |sgc j l (Torus.mk y)|)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have h1 : Measurable fun l : ℝ => sgc j l (Torus.mk y) :=
      (measurable_sgc j).comp (measurable_id.prodMk measurable_const)
    exact ((measurable_id.pow_const _).mul h1.abs).aestronglyMeasurable
  have hpt : ∀ l ∈ Ioi (0 : ℝ), l ^ (-β) * |sgc j l (Torus.mk y)| ≤
      l ^ (-β) * ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * H (4 * Real.pi ^ 2 * t) := by
    intro l hl
    have hl' : (0:ℝ) < l := hl
    exact mul_le_mul_of_nonneg_left (abs_sgc_le j _) (Real.rpow_pos_of_pos hl' _).le
  have hint : IntegrableOn (fun l : ℝ => l ^ (-β) * |sgc j l (Torus.mk y)|) (Ioi 0) := by
    refine Integrable.mono' hA hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun l hl => ?_)
    have hl' : (0:ℝ) < l := hl
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos hl' _).le (abs_nonneg _))]
    exact hpt l hl
  refine ⟨hint, ?_⟩
  have h1 : ∫ l in Ioi (0 : ℝ), l ^ (-β) * |sgc j l (Torus.mk y)| ≤
      ∫ l in Ioi (0 : ℝ), l ^ (-β) * ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * H (4 * Real.pi ^ 2 * t) :=
    setIntegral_mono_on hint hA measurableSet_Ioi hpt
  rw [← hB] at h1
  have hbp : 0 < (4 * Real.pi ^ 2) ^ β := Real.rpow_pos_of_pos hb _
  have h2 : ∫ t in Ioi (0 : ℝ), t ^ (β - 1) * H (4 * Real.pi ^ 2 * t) =
      (4 * Real.pi ^ 2) ^ (-β) * ∫ u in Ioi (0 : ℝ), u ^ (β - 1) * H u := by
    rw [he, Real.rpow_neg hb.le]; field_simp
  rw [h2] at h1
  refine h1.trans ?_
  rw [KernelGrad.tdist_mk hy]
  have hr : 0 ≤ ‖y‖ ^ (-s - 1) := Real.rpow_nonneg (norm_nonneg _) _
  have hC1' : C1 j ≤ Cs := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => C1 j + C2 j) (fun i _ => add_nonneg (hC1 i) (hC2 i)) (Finset.mem_univ j))
    linarith [hC2 j]
  have hC2' : C2 j ≤ Cs := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => C1 j + C2 j) (fun i _ => add_nonneg (hC1 i) (hC2 i)) (Finset.mem_univ j))
    linarith [hC1 j]
  have hJ' : ∫ u in Ioi (0 : ℝ), u ^ (β - 1) * H u ≤ Cs * (‖y‖ ^ (-s - 1) + 1) := by
    refine hJ.trans ?_
    nlinarith [hC1', hC2', hr, hC1 j, hC2 j]
  calc Real.Gamma (1 - β) * ((4 * Real.pi ^ 2) ^ (-β) * ∫ u in Ioi (0 : ℝ), u ^ (β - 1) * H u)
      ≤ Real.Gamma (1 - β) * ((4 * Real.pi ^ 2) ^ (-β) * (Cs * (‖y‖ ^ (-s - 1) + 1))) := by
        gcongr
    _ = _ := by ring

theorem norm_boxPt_eq {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ 1 / 2) : ‖boxPt y‖ = ‖y‖ := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    have : ‖((y i : ℝ) : UnitAddCircle)‖ = |y i| := by
      rw [AddCircle.norm_coe_eq_abs_iff (1:ℝ) one_ne_zero]; simpa using hy i
    rw [show boxPt y i = ((y i : ℝ) : UnitAddCircle) from rfl, this]
    simpa [Real.norm_eq_abs] using norm_le_pi_norm y i
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    have : ‖((y i : ℝ) : UnitAddCircle)‖ = |y i| := by
      rw [AddCircle.norm_coe_eq_abs_iff (1:ℝ) one_ne_zero]; simpa using hy i
    have h2 := norm_le_pi_norm (boxPt y) i
    rw [show boxPt y i = ((y i : ℝ) : UnitAddCircle) from rfl, this] at h2
    simpa [Real.norm_eq_abs] using h2

theorem tdist_le_dim (z : Torus d) : KernelGrad.tdist z 0 ≤ d := by
  rw [KernelGrad.tdist_zero_right]
  exact norm_le_card_of_box (KernelGrad.abs_centeredRep_le z)

theorem integrable_tdist_rpow {α : ℝ} (hd : 0 < d) (hα0 : 0 ≤ α) (hα : α < d) :
    Integrable (fun z : Torus d => KernelGrad.tdist z 0 ^ (-α)) := by
  have hm : Measurable fun z : Torus d => KernelGrad.tdist z 0 ^ (-α) :=
    (CoercAux.continuous_tdist_zero.measurable).pow_const _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_torus_box (fun x => ‖KernelGrad.tdist x 0 ^ (-α)‖ₑ)]
  have hI := integrableOn_Box_rpow hd hα
  calc ∫⁻ y in Box d, ‖KernelGrad.tdist (boxPt y) 0 ^ (-α)‖ₑ
      ≤ ∫⁻ y in Box d, ‖‖y‖ ^ (-α)‖ₑ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae (ae_ne_pi hd), ae_restrict_mem (measurableSet_Box d)]
          with y hy0 hyB
        have hyb := Box_abs_le hyB
        have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
        have hle : ‖y‖ ≤ KernelGrad.tdist (boxPt y) 0 := by
          rw [← norm_boxPt_eq hyb]; exact KernelGrad.norm_le_tdist _
        rw [Real.enorm_of_nonneg (Real.rpow_nonneg (KernelGrad.tdist_nonneg _ _) _),
          Real.enorm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hpos hle (by linarith))
    _ < ∞ := hI.2

theorem integrable_conv_prod {ρ : Torus d → ℝ} {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ)
    {φ : Torus d → ℝ} (hφm : Measurable φ) (hφ : Integrable φ) :
    Integrable (fun p : Torus d × Torus d => φ (p.1 - p.2))
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  haveI : SFinite (withDensityReal ρ) := by unfold withDensityReal; infer_instance
  have hmeas : Measurable fun p : Torus d × Torus d => φ (p.1 - p.2) :=
    hφm.comp (measurable_fst.sub measurable_snd)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hmeas' : Measurable fun p : Torus d × Torus d => ‖φ (p.1 - p.2)‖ₑ := hmeas.enorm
  rw [lintegral_prod _ hmeas'.aemeasurable]
  have h1 : ∀ x : Torus d, ∫⁻ y, ‖φ (x - y)‖ₑ ∂(withDensityReal ρ) ≤
      ENNReal.ofReal Λ * ∫⁻ y, ‖φ y‖ₑ :=
    fun x => KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ‖φ z‖ₑ) x
  have h2 : ∫⁻ y, ‖φ y‖ₑ < ⊤ := hφ.hasFiniteIntegral
  have hμ : (withDensityReal ρ) Set.univ < ⊤ := by
    unfold withDensityReal
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ x, ENNReal.ofReal (ρ x) ≤ ∫⁻ _x : Torus d, ENNReal.ofReal Λ :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hΛ x)
      _ < ⊤ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  calc ∫⁻ x, ∫⁻ y, ‖φ (x - y)‖ₑ ∂(withDensityReal ρ) ∂(withDensityReal ρ)
      ≤ ∫⁻ _x, (ENNReal.ofReal Λ * ∫⁻ y, ‖φ y‖ₑ) ∂(withDensityReal ρ) := lintegral_mono h1
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2) hμ

theorem sgc_integrable {s : ℝ} (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) (j : Fin d)
    {z : Torus d} (hz : z ≠ 0) :
    IntegrableOn (fun l : ℝ => l ^ (-(((d : ℝ) - s) / 2)) * sgc j l z) (Ioi 0) := by
  obtain ⟨C, -, hC⟩ := slice_abs_bound hs0 hs hsd
  have hI := (hC j z hz).1
  have hmeas : AEStronglyMeasurable (fun l : ℝ => l ^ (-(((d : ℝ) - s) / 2)) * sgc j l z)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have h1 : Measurable fun l : ℝ => sgc j l z :=
      (measurable_sgc j).comp (measurable_id.prodMk measurable_const)
    exact ((measurable_id.pow_const _).mul h1).aestronglyMeasurable
  refine Integrable.mono' hI hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun l hl => ?_)
  have hl' : (0:ℝ) < l := hl
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hl' _)]

/-- The slice force as a vector. -/
def sgv (l : ℝ) (z : Torus d) : Euc d := WithLp.toLp 2 (fun j => sgc j l z)

theorem measurable_sgv : Measurable fun p : ℝ × Torus d => sgv p.1 p.2 := by
  unfold sgv
  exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr fun j => measurable_sgc j)

theorem norm_sgv_le (l : ℝ) (z : Torus d) : ‖sgv l z‖ ≤ ∑ j, |sgc j l z| := by
  unfold sgv
  have h := norm_toLp_le_sum (fun j => sgc j l z)
  simpa using h

end PsiGrad

/-! ### Abstract Fubini for the Stieltjes mixture -/

section Fubini

variable {Y : Type*} [MeasurableSpace Y]

theorem fub_gen (ν : Measure Y) [SFinite ν] (F : ℝ → Y → ℝ)
    (hF : Measurable fun p : ℝ × Y => F p.1 p.2)
    (h1 : ∀ y, IntegrableOn (fun l => F l y) (Ioi 0))
    (Θ : Y → ℝ) (hΘ : Integrable Θ ν) (h2 : ∀ y, ∫ l in Ioi (0 : ℝ), ‖F l y‖ ≤ Θ y) :
    Integrable (fun p : ℝ × Y => F p.1 p.2) ((volume.restrict (Ioi (0 : ℝ))).prod ν) ∧
    Integrable (fun l => ∫ y, F l y ∂ν) (volume.restrict (Ioi (0 : ℝ))) ∧
    (∀ᵐ l ∂(volume.restrict (Ioi (0 : ℝ))), Integrable (F l) ν) ∧
    Integrable (fun y => ∫ l in Ioi (0 : ℝ), F l y) ν ∧
    ∫ y, (∫ l in Ioi (0 : ℝ), F l y) ∂ν = ∫ l in Ioi (0 : ℝ), (∫ y, F l y ∂ν) := by
  have hint : Integrable (fun p : ℝ × Y => F p.1 p.2) ((volume.restrict (Ioi (0 : ℝ))).prod ν) := by
    rw [integrable_prod_iff' hF.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall h1, ?_⟩
    refine Integrable.mono' hΘ ?_ ?_
    · exact (hF.norm.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioi (0 : ℝ)))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun l => norm_nonneg _)]
      exact h2 y
  refine ⟨hint, hint.integral_prod_left, hint.prod_right_ae, hint.integral_prod_right, ?_⟩
  exact (integral_integral_swap (f := fun l y => F l y) hint).symm

theorem offDiag_stieltjes {d N : ℕ} {β c : ℝ} (kS : ℝ → Torus d → Torus d → ℝ)
    (kI : Torus d → Torus d → ℝ) (X : Config d N) (μ : Measure (Torus d)) [SFinite μ]
    (hmeas : Measurable fun p : ℝ × (Torus d × Torus d) => kS p.1 p.2.1 p.2.2)
    (h1 : ∀ x y, IntegrableOn (fun l => l ^ (-β) * kS l x y) (Ioi 0))
    (h1' : ∀ x y, kI x y = c * ∫ l in Ioi (0 : ℝ), l ^ (-β) * kS l x y)
    (Θ : Torus d → ℝ)
    (h2 : ∀ x y, ∫ l in Ioi (0 : ℝ), ‖l ^ (-β) * kS l x y‖ ≤ Θ (x - y))
    (hΘ1 : ∀ x, Integrable (fun y => Θ (x - y)) μ)
    (hΘ2 : Integrable (fun p : Torus d × Torus d => Θ (p.1 - p.2)) (μ.prod μ)) :
    offDiagPairing kI X μ = c * ∫ l in Ioi (0 : ℝ), l ^ (-β) * offDiagPairing (kS l) X μ := by
  set ν₀ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hν₀
  -- the B-terms
  have hB : ∀ x0 : Torus d,
      Integrable (fun l => l ^ (-β) * ∫ y, kS l x0 y ∂μ) ν₀ ∧
      ∫ y, kI x0 y ∂μ = c * ∫ l in Ioi (0 : ℝ), l ^ (-β) * ∫ y, kS l x0 y ∂μ := by
    intro x0
    have hm : Measurable fun p : ℝ × Torus d => p.1 ^ (-β) * kS p.1 x0 p.2 := by
      have h := hmeas.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd) :
        Measurable fun p : ℝ × Torus d => (p.1, (x0, p.2)))
      exact (measurable_fst.pow_const _).mul h
    obtain ⟨-, hb, -, -, hd⟩ := fub_gen μ (fun l y => l ^ (-β) * kS l x0 y) hm (fun y => h1 x0 y)
      (fun y => Θ (x0 - y)) (hΘ1 x0) (fun y => h2 x0 y)
    have e1 : ∀ l, ∫ y, l ^ (-β) * kS l x0 y ∂μ = l ^ (-β) * ∫ y, kS l x0 y ∂μ := fun l => integral_const_mul _ _
    simp only [e1] at hb hd
    refine ⟨hb, ?_⟩
    rw [← hd, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => h1' x0 y)
  -- the C-term
  have hC : Integrable (fun l => l ^ (-β) * ∫ x, ∫ y, kS l x y ∂μ ∂μ) ν₀ ∧
      ∫ x, ∫ y, kI x y ∂μ ∂μ = c * ∫ l in Ioi (0 : ℝ), l ^ (-β) * ∫ x, ∫ y, kS l x y ∂μ ∂μ := by
    have hm : Measurable fun p : ℝ × (Torus d × Torus d) => p.1 ^ (-β) * kS p.1 p.2.1 p.2.2 :=
      (measurable_fst.pow_const _).mul hmeas
    obtain ⟨-, hb, hc, hr, hd⟩ := fub_gen (μ.prod μ) (fun l p => l ^ (-β) * kS l p.1 p.2) hm
      (fun p => h1 p.1 p.2) (fun p => Θ (p.1 - p.2)) hΘ2 (fun p => h2 p.1 p.2)
    have e2 : ∀ᵐ l ∂ν₀, ∫ p, l ^ (-β) * kS l p.1 p.2 ∂(μ.prod μ) = l ^ (-β) * ∫ x, ∫ y, kS l x y ∂μ ∂μ := by
      filter_upwards [hc] with l hl
      rw [integral_prod _ hl]
      simp only [integral_const_mul]
    refine ⟨hb.congr e2, ?_⟩
    have e3 : ∫ x, ∫ y, kI x y ∂μ ∂μ = ∫ p, kI p.1 p.2 ∂(μ.prod μ) := by
      refine (integral_prod (fun p : Torus d × Torus d => kI p.1 p.2) ?_).symm
      have := hr.const_mul c
      exact this.congr (Filter.Eventually.of_forall fun p => (h1' p.1 p.2).symm)
    have e4 : ∫ p, kI p.1 p.2 ∂(μ.prod μ) =
        c * ∫ p, (∫ l in Ioi (0 : ℝ), l ^ (-β) * kS l p.1 p.2) ∂(μ.prod μ) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => h1' p.1 p.2)
    rw [e3, e4, hd]
    congr 1
    exact integral_congr_ae e2
  -- the A-terms
  have hA : Integrable (fun l => l ^ (-β) * ∑ i, ∑ j ∈ Finset.univ.erase i, kS l (X i) (X j)) ν₀ ∧
      ∑ i, ∑ j ∈ Finset.univ.erase i, kI (X i) (X j) =
        c * ∫ l in Ioi (0 : ℝ), l ^ (-β) * ∑ i, ∑ j ∈ Finset.univ.erase i, kS l (X i) (X j) := by
    have hint : ∀ i j, Integrable (fun l => l ^ (-β) * kS l (X i) (X j)) ν₀ := fun i j => h1 (X i) (X j)
    have e : ∀ l, l ^ (-β) * ∑ i, ∑ j ∈ Finset.univ.erase i, kS l (X i) (X j) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, l ^ (-β) * kS l (X i) (X j) := by
      intro l
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    simp only [e]
    refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j, ?_⟩
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint i j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact h1' (X i) (X j)
  -- the B-sum
  have hBs : Integrable (fun l => l ^ (-β) * ∑ i, ∫ y, kS l (X i) y ∂μ) ν₀ ∧
      ∑ i, ∫ y, kI (X i) y ∂μ = c * ∫ l in Ioi (0 : ℝ), l ^ (-β) * ∑ i, ∫ y, kS l (X i) y ∂μ := by
    have e : ∀ l, l ^ (-β) * ∑ i, ∫ y, kS l (X i) y ∂μ = ∑ i, l ^ (-β) * ∫ y, kS l (X i) y ∂μ := fun l => by
      rw [Finset.mul_sum]
    simp only [e]
    refine ⟨integrable_finsetSum _ fun i _ => (hB (X i)).1, ?_⟩
    rw [integral_finsetSum _ fun i _ => (hB (X i)).1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (hB (X i)).2
  -- assemble
  unfold offDiagPairing
  have eA := hA.2
  have eB := hBs.2
  have eC := hC.2
  have key : ∀ l, l ^ (-β) * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, kS l (X i) (X j)
      - (2 / (N : ℝ)) * ∑ i, ∫ y, kS l (X i) y ∂μ + ∫ x, ∫ y, kS l x y ∂μ ∂μ) =
      (1 / (N : ℝ) ^ 2) * (l ^ (-β) * ∑ i, ∑ j ∈ Finset.univ.erase i, kS l (X i) (X j))
      - (2 / (N : ℝ)) * (l ^ (-β) * ∑ i, ∫ y, kS l (X i) y ∂μ) + l ^ (-β) * ∫ x, ∫ y, kS l x y ∂μ ∂μ := by
    intro l; ring
  simp only [key]
  have i1 : Integrable (fun l : ℝ => 1 / (N : ℝ) ^ 2 *
      (l ^ (-β) * ∑ i, ∑ j ∈ Finset.univ.erase i, kS l (X i) (X j))) ν₀ := hA.1.const_mul _
  have i2 : Integrable (fun l : ℝ => 2 / (N : ℝ) *
      (l ^ (-β) * ∑ i, ∫ y, kS l (X i) y ∂μ)) ν₀ := hBs.1.const_mul _
  have i12 : Integrable (fun l : ℝ => 1 / (N : ℝ) ^ 2 *
      (l ^ (-β) * ∑ i, ∑ j ∈ Finset.univ.erase i, kS l (X i) (X j)) -
      2 / (N : ℝ) * (l ^ (-β) * ∑ i, ∫ y, kS l (X i) y ∂μ)) ν₀ := i1.sub i2
  rw [integral_add i12 hC.1, integral_sub i1 i2, integral_const_mul, integral_const_mul]
  rw [eA, eB, eC]
  ring

end Fubini

/-! ### Periodisation of the Yukawa profile -/

section Periodization

open HRS HRS.KernelAux

variable {d : ℕ}

theorem boxPt_ne_zero {y : Fin d → ℝ} (hy : y ∈ Box d) (hy0 : y ≠ 0) : boxPt y ≠ 0 := by
  intro h
  apply hy0
  funext i
  have h1 : (((y i : ℝ)) : UnitAddCircle) = 0 := congrFun h i
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h1
  have hi := hy i
  simp only [mem_Ioc] at hi
  have hn' : (n : ℝ) = y i := by simpa using hn
  have a1 : (n : ℝ) < 1 := by linarith [hi.2]
  have a2 : (-1 : ℝ) < n := by linarith [hi.1]
  have b1 : n < 1 := by exact_mod_cast a1
  have b2 : -1 < n := by exact_mod_cast a2
  have : n = 0 := by omega
  subst this
  simpa using hn'.symm

/-- the heat kernel term -/
def heatTerm (d : ℕ) (y : Fin d → ℝ) (m : Lattice d) (l t : ℝ) : ℝ :=
  Real.exp (-l * t) * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
    Real.exp (-‖(WithLp.toLp 2 (fun i => y i - (m i : ℝ)) : Euc d)‖ ^ 2 / (4 * t)))

theorem heatTerm_nonneg (y : Fin d → ℝ) (m : Lattice d) (l : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ heatTerm d y m l t := by
  unfold heatTerm
  have := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi * t) (-(d : ℝ) / 2)
  positivity

theorem continuousOn_heatTerm (y : Fin d → ℝ) (m : Lattice d) (l : ℝ) :
    ContinuousOn (heatTerm d y m l) (Ioi 0) := by
  unfold heatTerm
  refine (by fun_prop : Continuous fun t : ℝ => Real.exp (-l * t)).continuousOn.mul
    (ContinuousOn.mul ?_ ?_)
  · exact ((continuousOn_const.mul continuousOn_id).rpow_const fun t ht =>
      Or.inl (by have : (0:ℝ) < t := ht; show 4 * Real.pi * t ≠ 0; positivity))
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun t ht => ?_
    have : (0:ℝ) < t := ht
    positivity

theorem sum_sq_eq (y : Fin d → ℝ) (m : Lattice d) :
    ‖(WithLp.toLp 2 (fun i => y i - (m i : ℝ)) : Euc d)‖ ^ 2 = ∑ i, (((m i : ℤ) : ℝ) - y i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Real.norm_eq_abs, sq_abs]
  ring

theorem heat_pointwise (y : Fin d → ℝ) (l : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-l * t) * (1 + psiFn (boxPt y) (4 * Real.pi ^ 2 * t)) =
      ∑' m : Lattice d, heatTerm d y m l t := by
  have hu : 0 < 4 * Real.pi ^ 2 * t := by positivity
  rw [← psi_eq (boxPt y) hu, theta_images y hu, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  unfold heatTerm
  have h1 : Real.sqrt (Real.pi / (4 * Real.pi ^ 2 * t)) ^ d = (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
    have e : Real.pi / (4 * Real.pi ^ 2 * t) = (4 * Real.pi * t)⁻¹ := by
      field_simp
    rw [e, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    congr 1; ring
  have h2 : -(Real.pi ^ 2 * ∑ i, (((m i : ℤ) : ℝ) - y i) ^ 2 / (4 * Real.pi ^ 2 * t)) =
      -‖(WithLp.toLp 2 (fun i => y i - (m i : ℝ)) : Euc d)‖ ^ 2 / (4 * t) := by
    rw [← Finset.sum_div, ← sum_sq_eq]
    have : Real.pi ^ 2 ≠ 0 := by positivity
    field_simp
  rw [h1, h2]

theorem summable_theta_terms (y : Fin d → ℝ) {u : ℝ} (hu : 0 < u) :
    Summable fun m : Lattice d => Real.exp (-(Real.pi ^ 2 * ∑ i, (((m i : ℤ) : ℝ) - y i) ^ 2 / u)) := by
  have hs : ∀ i, Summable fun n : ℤ => |Real.exp (-(Real.pi ^ 2 * ((n : ℝ) - y i) ^ 2 / u))| := by
    intro i
    simp_rw [abs_of_pos (Real.exp_pos _)]
    have : Summable fun n : ℤ => Real.exp (-(Real.pi ^ 2 / u) * ((n : ℝ) - y i) ^ 2) :=
      summable_shift_gauss (by positivity) _
    refine this.congr fun n => ?_
    congr 1; ring
  have h := (pi_hasSum_real d (fun i n => Real.exp (-(Real.pi ^ 2 * ((n : ℝ) - y i) ^ 2 / u))) hs).summable
  refine h.congr fun m => ?_
  rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc,
    Finset.sum_div]

theorem summable_heatTerm (y : Fin d → ℝ) (l : ℝ) {t : ℝ} (ht : 0 < t) :
    Summable fun m : Lattice d => heatTerm d y m l t := by
  have hu : 0 < 4 * Real.pi ^ 2 * t := by positivity
  have h := (summable_theta_terms y hu).mul_left
    (Real.exp (-l * t) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2))
  refine h.congr fun m => ?_
  unfold heatTerm
  have h2 : -(Real.pi ^ 2 * ∑ i, (((m i : ℤ) : ℝ) - y i) ^ 2 / (4 * Real.pi ^ 2 * t)) =
      -‖(WithLp.toLp 2 (fun i => y i - (m i : ℝ)) : Euc d)‖ ^ 2 / (4 * t) := by
    rw [← Finset.sum_div, ← sum_sq_eq]
    have : Real.pi ^ 2 ≠ 0 := by positivity
    field_simp
  rw [h2]; ring

theorem integrableOn_slice_psi {l : ℝ} (hl : 0 ≤ l) {x : Torus d} (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => Real.exp (-l * t) * psiFn x (4 * Real.pi ^ 2 * t)) (Ioi 0) := by
  have hb : 0 < 4 * Real.pi ^ 2 := by positivity
  obtain ⟨M0, hM00, hM0b⟩ := psi_bound x hx
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-(4 * Real.pi ^ 2 * t))) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -(4 * Real.pi ^ 2)) (by linarith) (0 : ℝ)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [neg_mul]
  have hc : ContinuousOn (fun t : ℝ => Real.exp (-l * t) * psiFn x (4 * Real.pi ^ 2 * t)) (Ioi 0) := by
    refine (by fun_prop : Continuous fun t : ℝ => Real.exp (-l * t)).continuousOn.mul ?_
    refine (psi_continuousOn _).comp (continuousOn_const.mul continuousOn_id) fun t ht => ?_
    have : (0:ℝ) < t := ht
    show 0 < 4 * Real.pi ^ 2 * t
    positivity
  refine Integrable.mono' (hexp.const_mul M0) (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  have ht' : (0:ℝ) < t := ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := hM0b (4 * Real.pi ^ 2 * t) (by positivity)
  have h2 : Real.exp (-l * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  calc Real.exp (-l * t) * |psiFn x (4 * Real.pi ^ 2 * t)|
      ≤ 1 * (M0 * Real.exp (-(4 * Real.pi ^ 2 * t))) := by gcongr
    _ = _ := by ring

/-- Periodisation of the slice kernel: `1/l + ∫ e^{-lt} Ψ(y,4π²t) dt = ∑_m ∫ e^{-lt} p_t(y-m) dt`. -/
theorem periodization_aux {l : ℝ} (hl : 0 < l) {y : Fin d → ℝ} (hy : y ∈ Box d) (hy0 : y ≠ 0) :
    1 / l + ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiFn (boxPt y) (4 * Real.pi ^ 2 * t) =
      ∑' m : Lattice d, ∫ t in Ioi (0 : ℝ), heatTerm d y m l t := by
  have hx : boxPt y ≠ 0 := boxPt_ne_zero hy hy0
  have hI := integrableOn_slice_psi hl.le hx
  have hE : IntegrableOn (fun t : ℝ => Real.exp (-l * t)) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -l) (by linarith) (0 : ℝ)
    exact this
  have hE' : ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) = 1 / l := by
    rw [integral_exp_mul_Ioi (by linarith : -l < 0)]
    simp
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-l * t) * (1 + psiFn (boxPt y) (4 * Real.pi ^ 2 * t)))
      (Ioi 0) := by
    have := hE.add hI
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  have hsplit : ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * (1 + psiFn (boxPt y) (4 * Real.pi ^ 2 * t)) =
      1 / l + ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiFn (boxPt y) (4 * Real.pi ^ 2 * t) := by
    rw [← hE', ← integral_add hE hI]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [← hsplit]
  have hpt : ∀ t ∈ Ioi (0 : ℝ), Real.exp (-l * t) * (1 + psiFn (boxPt y) (4 * Real.pi ^ 2 * t)) =
      ∑' m : Lattice d, heatTerm d y m l t := fun t ht => heat_pointwise y l ht
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hmeas : ∀ m : Lattice d, AEStronglyMeasurable (heatTerm d y m l) (volume.restrict (Ioi (0 : ℝ))) :=
    fun m => (continuousOn_heatTerm y m l).aestronglyMeasurable measurableSet_Ioi
  refine integral_tsum hmeas ?_
  -- finiteness
  have h1 : ∀ m : Lattice d, ∫⁻ t, ‖heatTerm d y m l t‖ₑ ∂(volume.restrict (Ioi (0 : ℝ))) =
      ∫⁻ t, ENNReal.ofReal (heatTerm d y m l t) ∂(volume.restrict (Ioi (0 : ℝ))) := by
    intro m
    refine lintegral_congr_ae ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    dsimp only
    rw [Real.enorm_of_nonneg (heatTerm_nonneg y m l ht)]
  simp_rw [h1]
  rw [← lintegral_tsum fun m => (hmeas m).aemeasurable.ennreal_ofReal]
  have h2 : ∫⁻ t, ∑' m : Lattice d, ENNReal.ofReal (heatTerm d y m l t)
        ∂(volume.restrict (Ioi (0 : ℝ))) =
      ∫⁻ t, ENNReal.ofReal (Real.exp (-l * t) * (1 + psiFn (boxPt y) (4 * Real.pi ^ 2 * t)))
        ∂(volume.restrict (Ioi (0 : ℝ))) := by
    refine lintegral_congr_ae ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    dsimp only
    rw [hpt t ht, ENNReal.ofReal_tsum_of_nonneg (fun m => heatTerm_nonneg y m l ht)
      (summable_heatTerm y l ht)]
  rw [h2]
  exact hg.lintegral_lt_top.ne

end Periodization

/-! ### The Euclidean heat profile and the Yukawa kernel -/

section Yukawa

open HRS HRS.KernelAux

variable {d : ℕ}

/-- the Gaussian profile `(4πt)^{-d/2} e^{-r²/4t}` -/
def gprof (d : ℕ) (t r : ℝ) : ℝ := (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * t))

theorem gprof_pos (d : ℕ) {t : ℝ} (ht : 0 < t) (r : ℝ) : 0 < gprof d t r := by
  unfold gprof; positivity

theorem kernel_bound {a : ℝ} (ha : 0 < a) {m : ℝ} (hm : 0 < (d : ℝ) / 2 + m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → ∀ r : ℝ, a ≤ r → t ^ (-m) * gprof d t r ≤ K := by
  set N : ℝ := (d : ℝ) / 2 + m with hN
  set θ : ℝ := a ^ 2 / 4 with hθ
  have hθ0 : 0 < θ := by positivity
  refine ⟨(4 * Real.pi) ^ (-(d : ℝ) / 2) * ((N ^ N * Real.exp (-N)) * θ ^ (-N)), by positivity,
    fun t ht r har => ?_⟩
  have h1 := t_pow_exp_bound hm hθ0 ht
  have h2 : Real.exp (-r ^ 2 / (4 * t)) ≤ Real.exp (-θ / t) := by
    apply Real.exp_le_exp.mpr
    have : a ^ 2 ≤ r ^ 2 := by nlinarith
    rw [hθ]
    have e : -(a ^ 2 / 4) / t = -a ^ 2 / (4 * t) := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  unfold gprof
  have e : t ^ (-m) * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * t))) =
      (4 * Real.pi) ^ (-(d : ℝ) / 2) * (t ^ (-N) * Real.exp (-r ^ 2 / (4 * t))) := by
    rw [Real.mul_rpow (by positivity) ht.le, hN]
    have : t ^ (-((d : ℝ) / 2 + m)) = t ^ (-m) * t ^ (-(d : ℝ) / 2) := by
      rw [← Real.rpow_add ht]; congr 1; ring
    rw [this]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans h1)
    (by positivity)

theorem exp_diff_bound {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {x : ℝ} (hx : 0 < x) :
    |Real.exp (-(A * x)) - Real.exp (-(B * x))| ≤ |A - B| * (x * Real.exp (-(min A B * x))) := by
  have key : ∀ A B : ℝ, A ≤ B → 0 < x →
      |Real.exp (-(A * x)) - Real.exp (-(B * x))| ≤ (B - A) * (x * Real.exp (-(A * x))) := by
    intro A B hAB hx
    have h1 : Real.exp (-(B * x)) ≤ Real.exp (-(A * x)) := Real.exp_le_exp.mpr (by nlinarith)
    rw [abs_of_nonneg (by linarith)]
    have h2 : Real.exp (-(B * x)) = Real.exp (-(A * x)) * Real.exp (-((B - A) * x)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : 1 - (B - A) * x ≤ Real.exp (-((B - A) * x)) := by
      have := Real.add_one_le_exp (-((B - A) * x)); linarith
    have h4 := Real.exp_pos (-(A * x))
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_left h3 h4.le]
  rcases le_total A B with h | h
  · have e1 : |A - B| = B - A := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [min_eq_left h, e1]; exact key A B h hx
  · have e1 : |A - B| = A - B := abs_of_nonneg (by linarith)
    rw [min_eq_right h, e1]
    have := key B A h hx
    rwa [abs_sub_comm] at this

theorem xside_integrable {s : ℝ} (hs0 : 0 ≤ s) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    IntegrableOn (fun x : ℝ => x ^ (s / 2 - 1) * (Real.exp (-(A * x)) - Real.exp (-(B * x)))) (Ioi 0) := by
  have hm : 0 < min A B := lt_min hA hB
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s / 2) (b := min A B)
    (by linarith) one_pos hm
  have h2 : IntegrableOn (fun x : ℝ => |A - B| * (x ^ (s / 2) * Real.exp (-(min A B * x)))) (Ioi 0) := by
    have this : IntegrableOn _ (Ioi (0:ℝ)) := h1.const_mul |A - B|
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]; ring_nf
  refine Integrable.mono' h2 ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)) ?_
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : (0 : ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx' _)]
    have := exp_diff_bound hA hB hx'
    have hxs : x ^ (s / 2 - 1) * x = x ^ (s / 2) := by
      rw [← Real.rpow_add_one hx'.ne']; ring_nf
    calc x ^ (s / 2 - 1) * |Real.exp (-(A * x)) - Real.exp (-(B * x))|
        ≤ x ^ (s / 2 - 1) * (|A - B| * (x * Real.exp (-(min A B * x)))) := by gcongr
      _ = |A - B| * (x ^ (s / 2) * Real.exp (-(min A B * x))) := by rw [← hxs]; ring

theorem xside_value {s : ℝ} (hs0 : 0 ≤ s) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫ x in Ioi (0 : ℝ), x ^ (s / 2 - 1) * (Real.exp (-(A * x)) - Real.exp (-(B * x))) =
      if s = 0 then Real.log (B / A) else Real.Gamma (s / 2) * (A ^ (-(s / 2)) - B ^ (-(s / 2))) := by
  split_ifs with h0
  · subst h0
    have hf : LocallyIntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) :=
      (Real.continuous_exp.comp continuous_neg).continuousOn.locallyIntegrableOn measurableSet_Ioi
    have := Frullani.integral_Ioi_eq (f := fun x : ℝ => Real.exp (-x)) (a := A) (b := B) hf hA hB
      (L := 1) (R := 0)
      (by
        have h : Tendsto (fun x : ℝ => Real.exp (-x)) (𝓝 0) (𝓝 (Real.exp (-0))) :=
          (by fun_prop : Continuous fun x : ℝ => Real.exp (-x)).tendsto 0
        rw [neg_zero, Real.exp_zero] at h
        exact h.mono_left nhdsWithin_le_nhds)
      (by simpa using Real.tendsto_exp_neg_atTop_nhds_zero)
      (by
        have := xside_integrable (le_refl (0:ℝ)) hA hB
        refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
        simp only [smul_eq_mul]
        simp [div_zero, Real.rpow_neg_one])
    simp only [smul_eq_mul, sub_zero, mul_one] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp [Real.rpow_neg_one]
  · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
    have ha : 0 < s / 2 := by linarith
    have hint : ∀ C : ℝ, 0 < C → IntegrableOn (fun x : ℝ => x ^ (s / 2 - 1) * Real.exp (-(C * x))) (Ioi 0) := by
      intro C hC
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s / 2 - 1) (b := C)
        (by linarith) one_pos hC
      refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
      simp only [Real.rpow_one]; ring_nf
    have e : ∀ x : ℝ, x ^ (s / 2 - 1) * (Real.exp (-(A * x)) - Real.exp (-(B * x))) =
        x ^ (s / 2 - 1) * Real.exp (-(A * x)) - x ^ (s / 2 - 1) * Real.exp (-(B * x)) := fun x => by ring
    simp_rw [e]
    rw [integral_sub (hint A hA) (hint B hB), Real.integral_rpow_mul_exp_neg_mul_Ioi ha hA,
      Real.integral_rpow_mul_exp_neg_mul_Ioi ha hB]
    simp only [one_div]
    rw [Real.inv_rpow hA.le, Real.inv_rpow hB.le,
      ← Real.rpow_neg hA.le, ← Real.rpow_neg hB.le]
    ring

theorem tside {s : ℝ} (hs0 : 0 ≤ s) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    IntegrableOn (fun t : ℝ => t ^ (-s / 2 - 1) * (Real.exp (-(A * t⁻¹)) - Real.exp (-(B * t⁻¹)))) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), t ^ (-s / 2 - 1) * (Real.exp (-(A * t⁻¹)) - Real.exp (-(B * t⁻¹))) =
      ∫ x in Ioi (0 : ℝ), x ^ (s / 2 - 1) * (Real.exp (-(A * x)) - Real.exp (-(B * x))) := by
  set g : ℝ → ℝ := fun t => t ^ (-s / 2 - 1) * (Real.exp (-(A * t⁻¹)) - Real.exp (-(B * t⁻¹))) with hg
  have hpt : ∀ x : ℝ, 0 < x → ((|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ))) =
      x ^ (s / 2 - 1) * (Real.exp (-(A * x)) - Real.exp (-(B * x))) := by
    intro x hx
    simp only [hg, smul_eq_mul, Real.rpow_neg_one, inv_inv, abs_neg, abs_one, one_mul]
    rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, ← mul_assoc, ← Real.rpow_add hx]
    congr 2; ring
  have hx := xside_integrable hs0 hA hB
  have hint : IntegrableOn (fun x : ℝ => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ))) (Ioi 0) := by
    refine hx.congr_fun (fun x hx' => (hpt x hx').symm) measurableSet_Ioi
  refine ⟨(integrableOn_Ioi_comp_rpow_iff g (p := -1) (by norm_num)).mp hint, ?_⟩
  rw [← integral_comp_rpow_Ioi g (p := -1) (by norm_num)]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx' => hpt x hx'

theorem integrableOn_yk {l : ℝ} (hl : 0 < l) (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => Real.exp (-l * t) * gprof d t r) (Ioi 0) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨K, hK0, hK⟩ := kernel_bound (d := d) hr (m := 0) (by simpa using (by positivity : (0:ℝ) < (d:ℝ) / 2))
  have hexp : IntegrableOn (fun t : ℝ => K * Real.exp (-l * t)) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -l) (by linarith) (0 : ℝ)
    exact this.const_mul K
  have hc : ContinuousOn (fun t : ℝ => Real.exp (-l * t) * gprof d t r) (Ioi 0) := by
    unfold gprof
    refine (by fun_prop : Continuous fun t : ℝ => Real.exp (-l * t)).continuousOn.mul
      (ContinuousOn.mul ?_ ?_)
    · exact ((continuousOn_const.mul continuousOn_id).rpow_const fun t ht =>
        Or.inl (by have : (0:ℝ) < t := ht; show 4 * Real.pi * t ≠ 0; positivity))
    · refine Real.continuous_exp.comp_continuousOn ?_
      refine continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun t ht => ?_
      have : (0:ℝ) < t := ht
      show 4 * t ≠ 0
      positivity
  refine Integrable.mono' hexp (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  have ht' : (0:ℝ) < t := ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (gprof_pos d ht' r).le)]
  have := hK t ht' r le_rfl
  simp only [neg_zero, Real.rpow_zero, one_mul] at this
  rw [mul_comm K]
  exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le

theorem continuousOn_gprof (d : ℕ) {r : ℝ} : ContinuousOn (fun t : ℝ => gprof d t r) (Ioi 0) := by
  unfold gprof
  refine ContinuousOn.mul ?_ ?_
  · exact ((continuousOn_const.mul continuousOn_id).rpow_const fun t ht =>
      Or.inl (by have : (0:ℝ) < t := ht; show 4 * Real.pi * t ≠ 0; positivity))
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun t ht => ?_
    have : (0:ℝ) < t := ht
    show 4 * t ≠ 0
    positivity

theorem yuk_stieltjes_aux {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ r η : ℝ, 0 < r → 0 < η →
      ∫ l in Ioi (0 : ℝ), l ^ (-(((d : ℝ) - s) / 2)) *
          ((∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * gprof d t r) -
            ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * gprof d t η) =
        c' * (if s = 0 then -Real.log r + Real.log η else r ^ (-s) - η ^ (-s)) := by
  set β : ℝ := ((d : ℝ) - s) / 2 with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hβ1 : β < 1 := by rw [hβ]; linarith
  have hG : 0 < Real.Gamma (1 - β) := Real.Gamma_pos_of_pos (by linarith)
  have hP : 0 < (4 * Real.pi) ^ (-(d : ℝ) / 2) := by positivity
  refine ⟨Real.Gamma (1 - β) * (4 * Real.pi) ^ (-(d : ℝ) / 2) *
    (if s = 0 then 2 else Real.Gamma (s / 2) * 2 ^ s), ?_, fun r η hr hη => ?_⟩
  · have : 0 < (if s = 0 then (2:ℝ) else Real.Gamma (s / 2) * 2 ^ s) := by
      split_ifs with h0
      · norm_num
      · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
        exact mul_pos (Real.Gamma_pos_of_pos (by linarith)) (by positivity)
    positivity
  set A : ℝ := r ^ 2 / 4 with hA
  set B : ℝ := η ^ 2 / 4 with hB
  have hA0 : 0 < A := by positivity
  have hB0 : 0 < B := by positivity
  set h : ℝ → ℝ := fun t => gprof d t r - gprof d t η with hh
  have hc : ContinuousOn h (Ioi 0) := (continuousOn_gprof d).sub (continuousOn_gprof d)
  have hrel : ∀ t : ℝ, 0 < t → t ^ (β - 1) * h t =
      (4 * Real.pi) ^ (-(d : ℝ) / 2) *
        (t ^ (-s / 2 - 1) * (Real.exp (-(A * t⁻¹)) - Real.exp (-(B * t⁻¹)))) := by
    intro t ht
    simp only [hh, gprof]
    have e1 : (4 * Real.pi * t) ^ (-(d : ℝ) / 2) = (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) :=
      Real.mul_rpow (by positivity) ht.le
    have e2 : t ^ (β - 1) * t ^ (-(d : ℝ) / 2) = t ^ (-s / 2 - 1) := by
      rw [← Real.rpow_add ht]; congr 1; rw [hβ]; ring
    have e3 : ∀ C : ℝ, -C ^ 2 / (4 * t) = -((C ^ 2 / 4) * t⁻¹) := fun C => by field_simp
    rw [e1, e3 r, e3 η]
    calc t ^ (β - 1) * ((4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) * Real.exp (-(r ^ 2 / 4 * t⁻¹)) -
          (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) * Real.exp (-(η ^ 2 / 4 * t⁻¹)))
        = (4 * Real.pi) ^ (-(d : ℝ) / 2) * ((t ^ (β - 1) * t ^ (-(d : ℝ) / 2)) *
            (Real.exp (-(r ^ 2 / 4 * t⁻¹)) - Real.exp (-(η ^ 2 / 4 * t⁻¹)))) := by ring
      _ = _ := by rw [e2]
  obtain ⟨hti, htv⟩ := tside hs0 hA0 hB0
  have hi : IntegrableOn (fun t : ℝ => t ^ (β - 1) * h t) (Ioi 0) := by
    have : IntegrableOn _ (Ioi (0:ℝ)) := hti.const_mul ((4 * Real.pi) ^ (-(d : ℝ) / 2))
    exact this.congr_fun (fun t ht => (hrel t ht).symm) measurableSet_Ioi
  obtain ⟨-, hB'⟩ := stieltjes_swap hβ1 hc hi
  have hin : ∀ l ∈ Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * h t =
      (∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * gprof d t r) -
        ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * gprof d t η := by
    intro l hl
    have hl' : (0:ℝ) < l := hl
    rw [← integral_sub (integrableOn_yk hl' hd hr) (integrableOn_yk hl' hd hη)]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp only [hh]; ring
  have e5 : ∫ l in Ioi (0 : ℝ), l ^ (-β) * ((∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * gprof d t r) -
            ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * gprof d t η) =
      ∫ l in Ioi (0 : ℝ), l ^ (-β) * ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * h t :=
    setIntegral_congr_fun measurableSet_Ioi fun l hl => by rw [hin l hl]
  rw [e5, ← hB']
  have e6 : ∫ t in Ioi (0 : ℝ), t ^ (β - 1) * h t =
      (4 * Real.pi) ^ (-(d : ℝ) / 2) * ∫ x in Ioi (0 : ℝ), x ^ (s / 2 - 1) *
        (Real.exp (-(A * x)) - Real.exp (-(B * x))) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hrel t ht), integral_const_mul, htv]
  rw [e6, xside_value hs0 hA0 hB0]
  split_ifs with h0
  · have : Real.log (B / A) = 2 * (-Real.log r + Real.log η) := by
      have : B / A = η ^ 2 / r ^ 2 := by rw [hA, hB]; field_simp
      rw [this, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      push_cast; ring
    rw [this]; ring
  · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
    have e7 : ∀ C : ℝ, 0 < C → (C ^ 2 / 4) ^ (-(s / 2)) = 2 ^ s * C ^ (-s) := by
      intro C hC
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast C 2, ← Real.rpow_mul hC.le,
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4), show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
        ← Real.rpow_mul (by norm_num)]
      have : (2 : ℝ) ^ (2 * (s / 2)) = 2 ^ s := by congr 1; ring
      rw [this]
      have : C ^ ((2 : ℕ) * -(s / 2) : ℝ) = C ^ (-s) := by congr 1; push_cast; ring
      rw [this]
      field_simp
    rw [hA, hB, e7 r hr, e7 η hη]
    ring

end Yukawa

section Ode
open HRS HRS.KernelAux

variable {d : ℕ}

/-- parametric differentiation -/
theorem deriv_under {l : ℝ} (hl : 0 < l) (F F' : ℝ → ℝ → ℝ) {r0 : ℝ} (hr0 : 0 < r0)
    (hc : ∀ r, 0 < r → ContinuousOn (F r) (Ioi 0)) (hc' : ContinuousOn (F' r0) (Ioi 0))
    (hint : IntegrableOn (F r0) (Ioi 0))
    (K : ℝ) (hbd : ∀ t : ℝ, 0 < t → ∀ r ∈ Ioo (r0 / 2) (2 * r0), |F' r t| ≤ K * Real.exp (-l * t))
    (hd : ∀ t : ℝ, 0 < t → ∀ r ∈ Ioo (r0 / 2) (2 * r0), HasDerivAt (fun r => F r t) (F' r t) r) :
    IntegrableOn (F' r0) (Ioi 0) ∧
    HasDerivAt (fun r => ∫ t in Ioi (0 : ℝ), F r t) (∫ t in Ioi (0 : ℝ), F' r0 t) r0 := by
  have hexp : IntegrableOn (fun t : ℝ => K * Real.exp (-l * t)) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -l) (by linarith) (0 : ℝ)
    exact this.const_mul K
  have hs : Ioo (r0 / 2) (2 * r0) ∈ 𝓝 r0 := Ioo_mem_nhds (by linarith) (by linarith)
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun r t => F r t) (F' := F') (bound := fun t => K * Real.exp (-l * t)) hs ?_ hint
    (hc'.aestronglyMeasurable measurableSet_Ioi) ?_ hexp ?_
  · filter_upwards [hs] with r hr
    exact (hc r (by linarith [hr.1])).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht r hr => ?_)
    rw [Real.norm_eq_abs]; exact hbd t ht r hr
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht r hr => ?_)
    exact hd t ht r hr

theorem hasDerivAt_F0 (d : ℕ) (l : ℝ) {t : ℝ} (ht : 0 < t) (r : ℝ) :
    HasDerivAt (fun r => Real.exp (-l * t) * gprof d t r)
      (-(r / (2 * t)) * (Real.exp (-l * t) * gprof d t r)) r := by
  unfold gprof
  have h1 : HasDerivAt (fun r : ℝ => -r ^ 2 / (4 * t)) (-(2 * r) / (4 * t)) r := by
    have := ((hasDerivAt_pow 2 r).neg).div_const (4 * t)
    convert this using 1
    simp
  have h2 := (h1.exp).const_mul ((4 * Real.pi * t) ^ (-(d : ℝ) / 2))
  have h3 := h2.const_mul (Real.exp (-l * t))
  convert h3 using 1
  field_simp
  ring

theorem continuousOn_F0 (d : ℕ) (l r : ℝ) :
    ContinuousOn (fun t : ℝ => Real.exp (-l * t) * gprof d t r) (Ioi 0) :=
  (by fun_prop : Continuous fun t : ℝ => Real.exp (-l * t)).continuousOn.mul (continuousOn_gprof d)

theorem gbound (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) {m : ℝ} (hm : 0 ≤ m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → ∀ r : ℝ, a ≤ r → t ^ (-m) * gprof d t r ≤ K := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  exact kernel_bound (d := d) ha (by positivity)

theorem hasDerivAt_yk (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {r0 : ℝ} (hr0 : 0 < r0) :
    IntegrableOn (fun t : ℝ => -(r0 / (2 * t)) * (Real.exp (-l * t) * gprof d t r0)) (Ioi 0) ∧
    HasDerivAt (fun r => ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * gprof d t r)
      (∫ t in Ioi (0 : ℝ), -(r0 / (2 * t)) * (Real.exp (-l * t) * gprof d t r0)) r0 := by
  obtain ⟨K1, hK1, hK⟩ := gbound hd (a := r0 / 2) (by linarith) (m := 1) zero_le_one
  refine deriv_under hl (fun r t => Real.exp (-l * t) * gprof d t r)
    (fun r t => -(r / (2 * t)) * (Real.exp (-l * t) * gprof d t r)) hr0
    (fun r _ => continuousOn_F0 d l r) ?_ (integrableOn_yk hl hd hr0) (r0 * K1) ?_ ?_
  · refine ContinuousOn.mul ?_ (continuousOn_F0 d l r0)
    refine ContinuousOn.neg (continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun t ht => ?_)
    have : (0:ℝ) < t := ht
    show 2 * t ≠ 0
    positivity
  · intro t ht r hr
    have h1 := hK t ht r hr.1.le
    rw [Real.rpow_neg_one] at h1
    have hg := gprof_pos d ht r
    have he := Real.exp_pos (-l * t)
    have hr1 : 0 < r := by linarith [hr.1]
    rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < r / (2 * t)), abs_of_pos (by positivity)]
    calc r / (2 * t) * (Real.exp (-l * t) * gprof d t r)
        = (r / 2) * Real.exp (-l * t) * (t⁻¹ * gprof d t r) := by field_simp
      _ ≤ r0 * Real.exp (-l * t) * K1 := by
          have : r / 2 ≤ r0 := by linarith [hr.2]
          gcongr
      _ = r0 * K1 * Real.exp (-l * t) := by ring
  · intro t ht r _
    exact hasDerivAt_F0 d l ht r

theorem pos_integral_of_pos {f : ℝ → ℝ} (hf : ∀ t : ℝ, 0 < t → 0 < f t)
    (hint : IntegrableOn f (Ioi 0)) : 0 < ∫ t in Ioi (0 : ℝ), f t := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => (hf t ht).le)) hint]
  have : Function.support f ∩ Ioi 0 = Ioi 0 := by
    ext t
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
    exact ⟨fun h => h.2, fun h => ⟨(hf t h).ne', h⟩⟩
  rw [this]
  simp

theorem yk_pos (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {r : ℝ} (hr : 0 < r) :
    0 < ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * gprof d t r :=
  pos_integral_of_pos (fun t ht => mul_pos (Real.exp_pos _) (gprof_pos d ht r)) (integrableOn_yk hl hd hr)

theorem yk_deriv_neg (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {r0 : ℝ} (hr0 : 0 < r0) :
    ∫ t in Ioi (0 : ℝ), -(r0 / (2 * t)) * (Real.exp (-l * t) * gprof d t r0) < 0 := by
  obtain ⟨hi, -⟩ := hasDerivAt_yk hd hl hr0
  have hi' : IntegrableOn (fun t : ℝ => (r0 / (2 * t)) * (Real.exp (-l * t) * gprof d t r0)) (Ioi 0) := by
    have := hi.neg
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp
  have := pos_integral_of_pos (f := fun t : ℝ => (r0 / (2 * t)) * (Real.exp (-l * t) * gprof d t r0))
    (fun t ht => mul_pos (by positivity) (mul_pos (Real.exp_pos _) (gprof_pos d ht r0))) hi'
  have e : ∫ t in Ioi (0 : ℝ), -(r0 / (2 * t)) * (Real.exp (-l * t) * gprof d t r0) =
      -∫ t in Ioi (0 : ℝ), (r0 / (2 * t)) * (Real.exp (-l * t) * gprof d t r0) := by
    rw [← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  rw [e]; linarith

theorem yk_strictAnti (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) :
    StrictAntiOn (fun r => ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * gprof d t r) (Ioi 0) := by
  have hdiff : ∀ r ∈ Ioi (0:ℝ), HasDerivAt (fun r => ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * gprof d t r)
      (∫ t in Ioi (0 : ℝ), -(r / (2 * t)) * (Real.exp (-l * t) * gprof d t r)) r :=
    fun r hr => (hasDerivAt_yk hd hl hr).2
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) (fun r hr => (hdiff r hr).continuousAt.continuousWithinAt) ?_
  intro r hr
  rw [interior_Ioi] at hr
  rw [(hdiff r hr).deriv]
  exact yk_deriv_neg hd hl hr

theorem pow_deriv_aux (n : ℕ) (r : ℝ) : (n : ℝ) * r ^ (n - 1) * r = n * r ^ n := by
  rcases n with _ | m
  · simp
  · simp [pow_succ]; ring

theorem hasDerivAt_FH (n : ℕ) (l : ℝ) {t : ℝ} (ht : 0 < t) (r : ℝ) :
    HasDerivAt (fun r => r ^ n * (-(r / (2 * t)) * (Real.exp (-l * t) * gprof (n + 1) t r)))
      (r ^ n * (Real.exp (-l * t) * gprof (n + 1) t r * (r ^ 2 / (4 * t ^ 2) - ((n : ℝ) + 1) / (2 * t)))) r := by
  have hu : HasDerivAt (fun r : ℝ => -(r / (2 * t))) (-(1 / (2 * t))) r :=
    ((hasDerivAt_id r).div_const (2 * t)).neg
  have hF := hasDerivAt_F0 (n + 1) l ht r
  have hg := hu.mul hF
  have hp := (hasDerivAt_pow n r).mul hg
  convert hp using 1
  have h := pow_deriv_aux n r
  simp only [Pi.mul_apply]
  set E := Real.exp (-l * t) * gprof (n + 1) t r with hE
  have key : (n : ℝ) * r ^ (n - 1) * (-(r / (2 * t)) * E) = -((n : ℝ) * r ^ n / (2 * t)) * E := by
    calc (n : ℝ) * r ^ (n - 1) * (-(r / (2 * t)) * E)
        = -(1 / (2 * t)) * ((n : ℝ) * r ^ (n - 1) * r) * E := by field_simp
      _ = _ := by rw [h]; field_simp
  rw [key]
  field_simp
  ring

theorem hasDerivAt_flux (n : ℕ) {l : ℝ} (hl : 0 < l) {r0 : ℝ} (hr0 : 0 < r0) :
    IntegrableOn (fun t : ℝ => r0 ^ n * (Real.exp (-l * t) * gprof (n + 1) t r0 *
      (r0 ^ 2 / (4 * t ^ 2) - ((n : ℝ) + 1) / (2 * t)))) (Ioi 0) ∧
    HasDerivAt (fun r => ∫ t in Ioi (0 : ℝ),
        r ^ n * (-(r / (2 * t)) * (Real.exp (-l * t) * gprof (n + 1) t r)))
      (∫ t in Ioi (0 : ℝ), r0 ^ n * (Real.exp (-l * t) * gprof (n + 1) t r0 *
        (r0 ^ 2 / (4 * t ^ 2) - ((n : ℝ) + 1) / (2 * t)))) r0 := by
  have hd1 : 1 ≤ n + 1 := by omega
  obtain ⟨K1, hK1, hK1b⟩ := gbound hd1 (a := r0 / 2) (by linarith) (m := 1) zero_le_one
  obtain ⟨K2, hK2, hK2b⟩ := gbound hd1 (a := r0 / 2) (by linarith) (m := 2) (by norm_num)
  have hF0c : ∀ r : ℝ, ContinuousOn (fun t : ℝ => -(r / (2 * t))) (Ioi 0) := by
    intro r
    refine ContinuousOn.neg (continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun t ht => ?_)
    have : (0:ℝ) < t := ht
    show 2 * t ≠ 0
    positivity
  refine deriv_under hl (fun r t => r ^ n * (-(r / (2 * t)) * (Real.exp (-l * t) * gprof (n + 1) t r)))
    (fun r t => r ^ n * (Real.exp (-l * t) * gprof (n + 1) t r *
      (r ^ 2 / (4 * t ^ 2) - ((n : ℝ) + 1) / (2 * t)))) hr0 ?_ ?_ ?_
    ((2 * r0) ^ n * (r0 ^ 2 * K2 + ((n : ℝ) + 1) / 2 * K1)) ?_ ?_
  · intro r _
    exact continuousOn_const.mul ((hF0c r).mul (continuousOn_F0 _ l r))
  · refine continuousOn_const.mul ((continuousOn_F0 _ l r0).mul ?_)
    refine ContinuousOn.sub (continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2)) fun t ht => ?_)
      (continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun t ht => ?_)
    · have : (0:ℝ) < t := ht
      show 4 * t ^ 2 ≠ 0
      positivity
    · have : (0:ℝ) < t := ht
      show 2 * t ≠ 0
      positivity
  · exact (hasDerivAt_yk hd1 hl hr0).1.const_mul (r0 ^ n)
  · intro t ht r hr
    have hr1 : 0 < r := by linarith [hr.1]
    have h1 := hK1b t ht r hr.1.le
    have h2 := hK2b t ht r hr.1.le
    rw [Real.rpow_neg_one] at h1
    rw [Real.rpow_neg ht.le, Real.rpow_two] at h2
    have hg := gprof_pos (n + 1) ht r
    have he := Real.exp_pos (-l * t)
    set e := Real.exp (-l * t) with he_def
    set g := gprof (n + 1) t r with hg_def
    have hpn : 0 ≤ r ^ n := by positivity
    have e1 : |r ^ 2 / (4 * t ^ 2) - ((n : ℝ) + 1) / (2 * t)| ≤
        r ^ 2 / (4 * t ^ 2) + ((n : ℝ) + 1) / (2 * t) := by
      have a1 : 0 ≤ r ^ 2 / (4 * t ^ 2) := by positivity
      have a2 : 0 ≤ ((n : ℝ) + 1) / (2 * t) := by positivity
      rw [abs_le]; constructor <;> linarith
    rw [abs_mul, abs_of_nonneg hpn, abs_mul, abs_of_pos (mul_pos he hg)]
    have e2 : r ^ n * (e * g * (r ^ 2 / (4 * t ^ 2) + ((n : ℝ) + 1) / (2 * t))) =
        r ^ n * e * ((r ^ 2 / 4) * ((t ^ 2)⁻¹ * g) + (((n : ℝ) + 1) / 2) * (t⁻¹ * g)) := by
      field_simp
    calc r ^ n * (e * g * |r ^ 2 / (4 * t ^ 2) - ((n : ℝ) + 1) / (2 * t)|)
        ≤ r ^ n * (e * g * (r ^ 2 / (4 * t ^ 2) + ((n : ℝ) + 1) / (2 * t))) := by gcongr
      _ = r ^ n * e * ((r ^ 2 / 4) * ((t ^ 2)⁻¹ * g) + (((n : ℝ) + 1) / 2) * (t⁻¹ * g)) := e2
      _ ≤ (2 * r0) ^ n * e * (r0 ^ 2 * K2 + ((n : ℝ) + 1) / 2 * K1) := by
          have hrn : r ^ n ≤ (2 * r0) ^ n := pow_le_pow_left₀ hr1.le hr.2.le n
          have hr2 : r ^ 2 / 4 ≤ r0 ^ 2 := by nlinarith [hr.2]
          gcongr
      _ = _ := by ring
  · intro t ht r _
    exact hasDerivAt_FH n l ht r

theorem hasDerivAt_gprof_t (d : ℕ) {t : ℝ} (ht : 0 < t) (r : ℝ) :
    HasDerivAt (fun t => gprof d t r) (gprof d t r * (-(d : ℝ) / (2 * t) + r ^ 2 / (4 * t ^ 2))) t := by
  have hf : HasDerivAt (fun t : ℝ => 4 * Real.pi * t) (4 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
  have h1 := hf.rpow_const (p := -(d : ℝ) / 2) (Or.inl (by positivity))
  have h2 : HasDerivAt (fun t : ℝ => -r ^ 2 / (4 * t)) (r ^ 2 / (4 * t ^ 2)) t := by
    have := (hasDerivAt_inv ht.ne').const_mul (-(r ^ 2 / 4))
    have e : (fun t : ℝ => -r ^ 2 / (4 * t)) = fun t => -(r ^ 2 / 4) * t⁻¹ := by
      funext t; ring
    rw [e]
    convert this using 1
    field_simp
  have h3 := h1.mul h2.exp
  unfold gprof
  convert h3 using 1
  have hp : (4 * Real.pi * t) ^ (-(d : ℝ) / 2 - 1) = (4 * Real.pi * t) ^ (-(d : ℝ) / 2) / (4 * Real.pi * t) :=
    Real.rpow_sub_one (by positivity) _
  rw [hp]
  field_simp

theorem hasDerivAt_Phi (d : ℕ) (l : ℝ) {t : ℝ} (ht : 0 < t) (r : ℝ) :
    HasDerivAt (fun t => Real.exp (-l * t) * gprof d t r)
      (Real.exp (-l * t) * gprof d t r * (-l - (d : ℝ) / (2 * t) + r ^ 2 / (4 * t ^ 2))) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-l * t)) (Real.exp (-l * t) * (-l)) t := by
    have := ((hasDerivAt_id t).const_mul (-l)).exp
    simpa using this
  have h := h1.mul (hasDerivAt_gprof_t d ht r)
  convert h using 1
  field_simp
  ring

theorem gprof_zero (n : ℕ) (r : ℝ) : gprof (n + 1) 0 r = 0 := by
  unfold gprof
  rw [mul_zero, Real.zero_rpow, zero_mul]
  have : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  intro h; linarith [h]

theorem Phi_integral_zero (n : ℕ) {l : ℝ} (hl : 0 < l) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => Real.exp (-l * t) * gprof (n + 1) t r *
      (-l - ((n : ℝ) + 1) / (2 * t) + r ^ 2 / (4 * t ^ 2))) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * gprof (n + 1) t r *
      (-l - ((n : ℝ) + 1) / (2 * t) + r ^ 2 / (4 * t ^ 2)) = 0 := by
  have hd1 : 1 ≤ n + 1 := by omega
  obtain ⟨K0, hK0, hK0b⟩ := gbound hd1 (a := r) hr (m := 0) le_rfl
  obtain ⟨K1, hK1, hK1b⟩ := gbound hd1 (a := r) hr (m := 1) zero_le_one
  obtain ⟨K2, hK2, hK2b⟩ := gbound hd1 (a := r) hr (m := 2) (by norm_num)
  obtain ⟨Kh, hKh, hKhb⟩ := gbound hd1 (a := r) hr (m := 1 / 2) (by norm_num)
  have hexp : IntegrableOn (fun t : ℝ => (l * K0 + ((n : ℝ) + 1) / 2 * K1 + r ^ 2 / 4 * K2) *
      Real.exp (-l * t)) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -l) (by linarith) (0 : ℝ)
    exact this.const_mul _
  have hcont : ContinuousOn (fun t : ℝ => Real.exp (-l * t) * gprof (n + 1) t r *
      (-l - ((n : ℝ) + 1) / (2 * t) + r ^ 2 / (4 * t ^ 2))) (Ioi 0) := by
    refine (continuousOn_F0 _ l r).mul ?_
    refine ContinuousOn.add (ContinuousOn.sub continuousOn_const
      (continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun t ht => ?_))
      (continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2)) fun t ht => ?_)
    · have : (0:ℝ) < t := ht
      show 2 * t ≠ 0
      positivity
    · have : (0:ℝ) < t := ht
      show 4 * t ^ 2 ≠ 0
      positivity
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-l * t) * gprof (n + 1) t r *
      (-l - ((n : ℝ) + 1) / (2 * t) + r ^ 2 / (4 * t ^ 2))) (Ioi 0) := by
    refine Integrable.mono' hexp (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : (0:ℝ) < t := ht
    have h0 := hK0b t ht' r le_rfl
    have h1 := hK1b t ht' r le_rfl
    have h2 := hK2b t ht' r le_rfl
    simp only [neg_zero, Real.rpow_zero, one_mul] at h0
    rw [Real.rpow_neg_one] at h1
    rw [Real.rpow_neg ht'.le, Real.rpow_two] at h2
    have hg := gprof_pos (n + 1) ht' r
    have he := Real.exp_pos (-l * t)
    set e := Real.exp (-l * t)
    set g := gprof (n + 1) t r
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos he hg)]
    have e1 : |-l - ((n : ℝ) + 1) / (2 * t) + r ^ 2 / (4 * t ^ 2)| ≤
        l + ((n : ℝ) + 1) / (2 * t) + r ^ 2 / (4 * t ^ 2) := by
      have a1 : 0 ≤ r ^ 2 / (4 * t ^ 2) := by positivity
      have a2 : 0 ≤ ((n : ℝ) + 1) / (2 * t) := by positivity
      rw [abs_le]; constructor <;> linarith
    calc e * g * |-l - ((n : ℝ) + 1) / (2 * t) + r ^ 2 / (4 * t ^ 2)|
        ≤ e * g * (l + ((n : ℝ) + 1) / (2 * t) + r ^ 2 / (4 * t ^ 2)) := by gcongr
      _ = e * (l * g + (((n : ℝ) + 1) / 2) * (t⁻¹ * g) + (r ^ 2 / 4) * ((t ^ 2)⁻¹ * g)) := by
          field_simp
      _ ≤ e * (l * K0 + (((n : ℝ) + 1) / 2) * K1 + (r ^ 2 / 4) * K2) := by gcongr
      _ = _ := by ring
  refine ⟨hint, ?_⟩
  -- fundamental theorem of calculus
  have hlim0 : ContinuousWithinAt (fun t : ℝ => Real.exp (-l * t) * gprof (n + 1) t r) (Ici 0) 0 := by
    have hz : Real.exp (-l * 0) * gprof (n + 1) 0 r = 0 := by rw [gprof_zero, mul_zero]
    unfold ContinuousWithinAt
    show Tendsto (fun t : ℝ => Real.exp (-l * t) * gprof (n + 1) t r) (𝓝[≥] 0)
      (𝓝 (Real.exp (-l * 0) * gprof (n + 1) 0 r))
    rw [hz]
    refine squeeze_zero_norm' (a := fun t : ℝ => Kh * t ^ (1 / 2 : ℝ)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rcases eq_or_lt_of_le (show (0:ℝ) ≤ t from ht) with h0 | h0
      · subst h0
        rw [gprof_zero]; simp
      · have h1 := hKhb t h0 r le_rfl
        have hg := gprof_pos (n + 1) h0 r
        have he := Real.exp_pos (-l * t)
        rw [Real.norm_eq_abs, abs_of_pos (mul_pos he hg)]
        have he1 : Real.exp (-l * t) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith
        have hth : t ^ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ)) = 1 := by
          rw [← Real.rpow_add h0]; simp
        have : gprof (n + 1) t r ≤ Kh * t ^ (1 / 2 : ℝ) := by
          have := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg h0.le (1 / 2 : ℝ))
          calc gprof (n + 1) t r = t ^ (1 / 2 : ℝ) * (t ^ (-(1 / 2 : ℝ)) * gprof (n + 1) t r) := by
                rw [← mul_assoc, hth, one_mul]
            _ ≤ t ^ (1 / 2 : ℝ) * Kh := this
            _ = _ := by ring
        calc Real.exp (-l * t) * gprof (n + 1) t r ≤ 1 * gprof (n + 1) t r := by gcongr
          _ ≤ _ := by linarith
    · have : Tendsto (fun t : ℝ => Kh * t ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 (Kh * 0 ^ (1 / 2 : ℝ))) :=
        (Real.continuousAt_rpow_const 0 (1 / 2 : ℝ) (Or.inr (by norm_num))).tendsto.const_mul Kh
      rw [Real.zero_rpow (by norm_num), mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun t : ℝ => Real.exp (-l * t) * gprof (n + 1) t r) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t : ℝ => K0 * Real.exp (-l * t)) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have h0 := hK0b t ht r le_rfl
      simp only [neg_zero, Real.rpow_zero, one_mul] at h0
      have hg := gprof_pos (n + 1) ht r
      have he := Real.exp_pos (-l * t)
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos he hg)]
      calc Real.exp (-l * t) * gprof (n + 1) t r ≤ Real.exp (-l * t) * K0 := by gcongr
        _ = _ := by ring
    · have : Tendsto (fun t : ℝ => Real.exp (-l * t)) atTop (𝓝 0) := by
        have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hl)
        refine h.congr fun t => ?_
        simp [neg_mul]
      simpa using this.const_mul K0
  have := integral_Ioi_of_hasDerivAt_of_tendsto hlim0
    (fun t ht => hasDerivAt_Phi (n + 1) l (show (0:ℝ) < t from ht) r |>.congr_deriv (by push_cast; ring)) hint hlim
  rw [this]
  have hz : Real.exp (-l * 0) * gprof (n + 1) 0 r = 0 := by rw [gprof_zero, mul_zero]
  rw [hz]; ring

theorem flux_identity (n : ℕ) {l : ℝ} (hl : 0 < l) {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), r ^ n * (Real.exp (-l * t) * gprof (n + 1) t r *
      (r ^ 2 / (4 * t ^ 2) - ((n : ℝ) + 1) / (2 * t))) =
      l * r ^ n * ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * gprof (n + 1) t r := by
  obtain ⟨hi1, hv1⟩ := Phi_integral_zero n hl hr
  have hi2 := integrableOn_yk (d := n + 1) hl (by omega) hr
  have e : ∀ t : ℝ, r ^ n * (Real.exp (-l * t) * gprof (n + 1) t r *
      (r ^ 2 / (4 * t ^ 2) - ((n : ℝ) + 1) / (2 * t))) =
      r ^ n * (Real.exp (-l * t) * gprof (n + 1) t r *
        (-l - ((n : ℝ) + 1) / (2 * t) + r ^ 2 / (4 * t ^ 2)) + l * (Real.exp (-l * t) * gprof (n + 1) t r)) := by
    intro t; ring
  simp_rw [e]
  rw [integral_const_mul, integral_add hi1 (hi2.const_mul l), hv1, integral_const_mul]
  ring

/-- the limiting profile of the flux -/
def Wfl (d : ℕ) (s : ℝ) : ℝ := (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * (1 / (2 * s)) * Real.exp (-(1 / (4 * s)))

theorem Wfl_eq (d : ℕ) {s : ℝ} (hs : 0 < s) :
    Wfl d s = ((4 * Real.pi) ^ (-(d : ℝ) / 2) / 2) *
      (s ^ (-(d : ℝ) / 2 - 1) * Real.exp (-((1 / 4) * s⁻¹))) := by
  unfold Wfl
  rw [Real.mul_rpow (by positivity) hs.le]
  have : s ^ (-(d : ℝ) / 2 - 1) = s ^ (-(d : ℝ) / 2) * s⁻¹ := by
    rw [Real.rpow_sub hs, Real.rpow_one]; field_simp
  rw [this]
  have e : -(1 / (4 * s)) = -((1 / 4) * s⁻¹) := by field_simp
  rw [e]
  field_simp

theorem Wfl_integral (hd : 1 ≤ d) :
    IntegrableOn (Wfl d) (Ioi 0) ∧
    ∫ s in Ioi (0 : ℝ), Wfl d s = Real.Gamma ((d : ℝ) / 2) / (2 * Real.pi ^ ((d : ℝ) / 2)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set g : ℝ → ℝ := fun y => y ^ ((d : ℝ) / 2 - 1) * Real.exp (-((1 / 4) * y)) with hg
  have hgi : IntegrableOn g (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (d : ℝ) / 2 - 1) (b := 1 / 4)
      (by linarith) one_pos (by norm_num)
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [hg, Real.rpow_one]; ring_nf
  have hpt : ∀ x : ℝ, 0 < x → ((|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ))) =
      x ^ (-(d : ℝ) / 2 - 1) * Real.exp (-((1 / 4) * x⁻¹)) := by
    intro x hx
    simp only [hg, smul_eq_mul, Real.rpow_neg_one, abs_neg, abs_one, one_mul]
    rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, ← mul_assoc, ← Real.rpow_add hx]
    congr 2; ring
  have hVi : IntegrableOn (fun x : ℝ => x ^ (-(d : ℝ) / 2 - 1) * Real.exp (-((1 / 4) * x⁻¹))) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_rpow_iff g (p := -1) (by norm_num)).mpr hgi
    exact this.congr_fun (fun x hx => hpt x hx) measurableSet_Ioi
  have hVv : ∫ x in Ioi (0 : ℝ), x ^ (-(d : ℝ) / 2 - 1) * Real.exp (-((1 / 4) * x⁻¹)) =
      4 ^ ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2) := by
    have h1 := integral_comp_rpow_Ioi g (p := -1) (by norm_num)
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hpt x hx)] at h1
    rw [h1]
    simp only [hg]
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (by norm_num)]
    norm_num
  constructor
  · have this : IntegrableOn _ (Ioi (0:ℝ)) := hVi.const_mul ((4 * Real.pi) ^ (-(d : ℝ) / 2) / 2)
    exact this.congr_fun (fun x hx => (Wfl_eq d hx).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => Wfl_eq d hx), integral_const_mul, hVv]
    rw [Real.mul_rpow (by norm_num) Real.pi_pos.le]
    have h4 : (0 : ℝ) < 4 ^ ((d : ℝ) / 2) := by positivity
    have h5 : (0 : ℝ) < Real.pi ^ ((d : ℝ) / 2) := by positivity
    have e : (4 : ℝ) ^ (-(d : ℝ) / 2) = ((4 : ℝ) ^ ((d : ℝ) / 2))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num)]; congr 1; ring
    have e' : Real.pi ^ (-(d : ℝ) / 2) = (Real.pi ^ ((d : ℝ) / 2))⁻¹ := by
      rw [← Real.rpow_neg Real.pi_pos.le]; congr 1; ring
    rw [e, e']
    field_simp

theorem flux_pointwise (n : ℕ) (l : ℝ) {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 < x) :
    r ^ 2 * (r ^ n * ((r / (2 * (r ^ 2 * x))) *
      (Real.exp (-l * (r ^ 2 * x)) * gprof (n + 1) (r ^ 2 * x) r))) =
      Real.exp (-l * (r ^ 2 * x)) * Wfl (n + 1) x := by
  unfold gprof Wfl
  have e1 : (4 * Real.pi * (r ^ 2 * x)) ^ (-((n + 1 : ℕ) : ℝ) / 2) =
      (r ^ (n + 1))⁻¹ * (4 * Real.pi * x) ^ (-((n + 1 : ℕ) : ℝ) / 2) := by
    have : 4 * Real.pi * (r ^ 2 * x) = r ^ 2 * (4 * Real.pi * x) := by ring
    rw [this, Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    have : ((2 : ℕ) : ℝ) * (-((n + 1 : ℕ) : ℝ) / 2) = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_neg hr.le, Real.rpow_natCast]
  have e2 : -r ^ 2 / (4 * (r ^ 2 * x)) = -(1 / (4 * x)) := by field_simp
  rw [e1, e2]
  field_simp
  ring

theorem flux_subst (n : ℕ) {l : ℝ} {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), r ^ n * ((r / (2 * t)) * (Real.exp (-l * t) * gprof (n + 1) t r)) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-l * (r ^ 2 * s)) * Wfl (n + 1) s := by
  have hb : 0 < r ^ 2 := by positivity
  have h := integral_comp_mul_left_Ioi (fun t : ℝ => r ^ n * ((r / (2 * t)) *
    (Real.exp (-l * t) * gprof (n + 1) t r))) 0 hb
  simp only [mul_zero, smul_eq_mul] at h
  have h' : ∫ t in Ioi (0 : ℝ), r ^ n * ((r / (2 * t)) * (Real.exp (-l * t) * gprof (n + 1) t r)) =
      r ^ 2 * ∫ x in Ioi (0 : ℝ), r ^ n * ((r / (2 * (r ^ 2 * x))) *
        (Real.exp (-l * (r ^ 2 * x)) * gprof (n + 1) (r ^ 2 * x) r)) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul]
  rw [h', ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => flux_pointwise n l hr hx

theorem Wfl_nonneg (d : ℕ) {s : ℝ} (hs : 0 < s) : 0 ≤ Wfl d s := by
  unfold Wfl; positivity

theorem continuousOn_Wfl (d : ℕ) : ContinuousOn (Wfl d) (Ioi 0) := by
  unfold Wfl
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · exact ((continuousOn_const.mul continuousOn_id).rpow_const fun t ht =>
      Or.inl (by have : (0:ℝ) < t := ht; show 4 * Real.pi * t ≠ 0; positivity))
  · exact continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun t ht => by
      have : (0:ℝ) < t := ht
      show 2 * t ≠ 0
      positivity
  · refine Real.continuous_exp.comp_continuousOn (ContinuousOn.neg ?_)
    exact continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun t ht => by
      have : (0:ℝ) < t := ht
      show 4 * t ≠ 0
      positivity

theorem flux_limit (n : ℕ) {l : ℝ} (hl : 0 < l) :
    Tendsto (fun r : ℝ => ∫ t in Ioi (0 : ℝ), r ^ n * ((r / (2 * t)) *
        (Real.exp (-l * t) * gprof (n + 1) t r))) (𝓝[>] 0)
      (𝓝 (Real.Gamma (((n + 1 : ℕ) : ℝ) / 2) / (2 * Real.pi ^ (((n + 1 : ℕ) : ℝ) / 2)))) := by
  obtain ⟨hWi, hWv⟩ := Wfl_integral (d := n + 1) (by omega)
  rw [← hWv]
  have hev : (fun r : ℝ => ∫ s in Ioi (0 : ℝ), Real.exp (-l * (r ^ 2 * s)) * Wfl (n + 1) s)
      =ᶠ[𝓝[>] 0] fun r : ℝ => ∫ t in Ioi (0 : ℝ), r ^ n * ((r / (2 * t)) *
        (Real.exp (-l * t) * gprof (n + 1) t r)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (flux_subst n (l := l) hr).symm
  refine Tendsto.congr' hev ?_
  refine tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
    (bound := Wfl (n + 1)) ?_ ?_ hWi ?_
  · refine Filter.Eventually.of_forall fun r => ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-l * (r ^ 2 * s))).continuousOn.mul
      (continuousOn_Wfl _)
  · refine Filter.Eventually.of_forall fun r => ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    have hs' : (0:ℝ) < s := hs
    have hw := Wfl_nonneg (n + 1) hs'
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hw)]
    have : Real.exp (-l * (r ^ 2 * s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ r ^ 2 * s := by positivity
      nlinarith
    calc Real.exp (-l * (r ^ 2 * s)) * Wfl (n + 1) s ≤ 1 * Wfl (n + 1) s := by gcongr
      _ = _ := one_mul _
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    have h : Tendsto (fun r : ℝ => Real.exp (-l * (r ^ 2 * s)) * Wfl (n + 1) s) (𝓝 0)
        (𝓝 (Real.exp (-l * (0 ^ 2 * s)) * Wfl (n + 1) s)) :=
      ((by fun_prop : Continuous fun r : ℝ => Real.exp (-l * (r ^ 2 * s))).mul
        continuous_const).tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero,
      Real.exp_zero, one_mul] at h
    exact h.mono_left nhdsWithin_le_nhds

end Ode

end SliceAux

end HRS.Commutator
