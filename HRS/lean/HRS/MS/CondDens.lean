import HRS.MS.CondDensAux2

/-!
# HRS.MS.CondDens -- S7.4 `conditional_density`

Packet S74, namespace `HRS.MS.Wr`, helper prefix `s74_`.  The statement proved is exactly
`HRS.Whole.conditional_density` (the tie file `CondDensTie.lean` restates it with `type_of%`).

Route (TeX S L5555-5640): `N = m + 2`, `n = m + 1` cavity particles, `λ = β/N`, `g = rieszKernel`.

1. `s74_G_close`: `|∫ g(y - Y_1) dP_n^0 - (g*μ)(y)| ≤ C N^{-τ}`.  The static inputs
   (`HasMarginalDensityBounds`, cavity total variation) bound `∫ ψ d(ν_n - μ)` for the truncation
   `ψ = min(g(y-·), H')` by `H'(TV + L²)`; the tails `g - g_{H'}` are controlled by `convolution_truncated`
   and the coordinate domination `ν_n ≤ e^{2βM_g} μ` (`s74_coord_marg`); `H' = N^{(p-1)/p}`.
   (This replaces the L¹/L^∞ convolution estimate of the TeX by a direct truncation; same exponent `τ`.)
2. `s74_potential`: `sup_y E|u_Y(y)| ≤ C N^{-τ}` (`S:eq:potential-uniform`): decomposition
   `u = V + R + c` (`s74_T_bound`), pole variance at `t = 0` for `V`, `H = N^{1/p}`.
3. `s74_prefactor`: the prefactor `A = s74_A` of Aux1 satisfies `|A - 1| ≤ C N^{-τ}` (`S:eq:prefactor-uniform`):
   `A(y) = ∫ e^{-u(tail Y, y)}/Zc(tail Y) d(poleLaw)(Y)`, `|ratio - 1| ≤ C(|u| + λ + ∫|u| dμ)`, joint pole
   domination `poleLaw ≤ K P` (`s74_pole_le`) and Fubini.
4. `conditional_density_proof`: assembly.

Statement adjustments: none.  Helper lemmas are stated for `N = m + 2` (`m = N - 2`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal BigOperators

noncomputable section

namespace HRS.MS.Wr

open HRS.Whole (rieszKernel EucConfig)

variable {d : ℕ} {s : ℝ}

/-! ### Exponent bookkeeping -/

theorem s74_deltaN (hs : (d : ℝ) / 2 < s) (N : ℕ) :
    HRS.deltaN d s N = (N : ℝ) ^ (1 - (d : ℝ) / s) := by
  unfold HRS.deltaN
  rw [if_neg (not_lt.2 hs.le), if_neg (ne_of_gt hs)]

theorem s74_p_bounds (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) :
    1 < (d : ℝ) / s ∧ (d : ℝ) / s < 2 := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  constructor
  · rw [lt_div_iff₀ hs0]; linarith
  · rw [div_lt_iff₀ hs0]; linarith

/-- `H^{1-p} = N^{-τ}` for `H = N^{(p-1)/p}`. -/
theorem s74_rpow_tau {p N : ℝ} (hp : 0 < p) (hN : 0 < N) :
    (N ^ ((p - 1) / p)) ^ (1 - p) = N ^ (-((p - 1) ^ 2 / p)) := by
  rw [← Real.rpow_mul hN.le]
  congr 1
  field_simp
  ring

theorem s74_rpow_tau' {p N : ℝ} (hp : 0 < p) (hN : 0 < N) :
    N ^ ((p - 1) / p) * N ^ (1 - p) = N ^ (-((p - 1) ^ 2 / p)) := by
  rw [← Real.rpow_add hN]
  congr 1
  field_simp
  ring

/-! ### The mean of the conditional potential -/

section Close2

theorem s74_G_close (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {β : ℝ} (hβ : 0 < β) (m : ℕ)
    (y : Euc d) {C0 Ctr : ℝ} (hSI : HRS.Whole.StaticInputConclusion d s (m + 2) β ρ C0)
    (htr : ∀ H : ℝ, 1 ≤ H →
      Integrable (fun z => rieszKernel d s (y - z) - HRS.Whole.truncKernel d s H (y - z))
        (HRS.Whole.withDensityReal ρ) ∧
      ∫ z, (rieszKernel d s (y - z) - HRS.Whole.truncKernel d s H (y - z))
        ∂(HRS.Whole.withDensityReal ρ) ≤ Ctr * H ^ (1 - HRS.Whole.biasP d s)) :
    |∫ Y : EucConfig d (m + 1), rieszKernel d s (y - Y 0)
        ∂(HRS.Whole.cavityLaw d s (m + 2) β (HRS.Whole.withDensityReal ρ)) -
      HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal ρ) y| ≤
    ((Real.exp (2 * β * HRS.Whole.potentialBound d s M) + 1) * |Ctr| + 2 * |C0|) *
      ((m + 2 : ℕ) : ℝ) ^ (-HRS.Whole.biasTau d s) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  obtain ⟨hp1, hp2⟩ := s74_p_bounds hd hs hsd
  haveI hμ := wr13a_isProb_density hρ
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  have hconv := wr13a_conv_le_density hd1 hs0 hsd hρ hM
  have hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ := fun z =>
    (wr13a_potential_bound hd1 hs0 hsd hρ hM z).1
  have hMg := wr13a_potentialBound_nonneg hd1 hs0 hsd hρ hM
  set Mg := HRS.Whole.potentialBound d s M with hMgdef
  set K0 : ℝ := Real.exp (2 * β * Mg) with hK0def
  have hK0 : 0 ≤ K0 := (Real.exp_pos _).le
  set Nr : ℝ := ((m + 2 : ℕ) : ℝ) with hNr
  have hN2 : (2 : ℝ) ≤ Nr := by rw [hNr]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hN0 : 0 < Nr := by linarith
  set p : ℝ := (d : ℝ) / s with hp
  have hp0 : 0 < p := by linarith
  have hbp : HRS.Whole.biasP d s = p := rfl
  have hbt : HRS.Whole.biasTau d s = (p - 1) ^ 2 / p := rfl
  haveI hP : IsProbabilityMeasure (HRS.Whole.cavityLaw d s (m + 2) β μ) :=
    wr13a_cavityLaw_isProb hs0 hconv hβ.le (m + 2)
  set P : Measure (EucConfig d (m + 1)) := HRS.Whole.cavityLaw d s (m + 2) β μ with hPdef
  set ν : Measure (Euc d) := P.map (fun Y : EucConfig d (m + 1) => Y 0) with hνdef
  haveI hνp : IsProbabilityMeasure ν := by rw [hνdef]; infer_instance
  have hνle : ν ≤ ENNReal.ofReal K0 • μ := s74_coord_marg hs0 hint hconv hMg hβ.le m 0
  obtain ⟨-, ⟨φ, hφm, hπ, hφb, -, hφn⟩, -, -, hTV⟩ := hSI
  set π : Measure (Euc d) :=
    HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) (m + 2) β μ) with hπdef
  haveI hQ := wr13c2_Q_isProb hs0 hconv hβ.le (by omega : 1 ≤ m + 2)
  haveI hπp : IsProbabilityMeasure π := by
    rw [hπdef]
    unfold HRS.Whole.firstMarginal
    rw [dif_pos (by omega : 0 < m + 2)]
    infer_instance
  have hcm : HRS.Whole.cavityMarginal d s (m + 2) β μ = ν := by
    unfold HRS.Whole.cavityMarginal HRS.Whole.firstMarginal
    rw [dif_pos (by omega : 0 < m + 2 - 1)]
    rfl
  rw [hcm] at hTV
  have hδ : HRS.deltaN d s (m + 2) = Nr ^ (1 - p) := s74_deltaN hs (m + 2)
  have hδ0 : 0 ≤ Nr ^ (1 - p) := Real.rpow_nonneg hN0.le _
  -- sqrt(δ/N) ≤ δ
  have hsq : Real.sqrt (HRS.deltaN d s (m + 2) / ((m + 2 : ℕ) : ℝ)) ≤ Nr ^ (1 - p) := by
    rw [hδ, ← hNr]
    refine Real.sqrt_le_iff.2 ⟨hδ0, ?_⟩
    have h1 : Nr ^ (1 - p) / Nr = Nr ^ (-p) := by
      have := hN0.ne'
      rw [Real.rpow_sub hN0, Real.rpow_one, Real.rpow_neg hN0.le]
      field_simp
    have h2 : (Nr ^ (1 - p)) ^ 2 = Nr ^ (2 - 2 * p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    rw [h1, h2]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  -- the truncation level
  set H : ℝ := Nr ^ ((p - 1) / p) with hH
  have hH1 : 1 ≤ H := Real.one_le_rpow (by linarith) (div_nonneg (by linarith) hp0.le)
  have hH0 : 0 < H := by linarith
  obtain ⟨htri, htrb⟩ := htr H hH1
  have hHpow : H ^ (1 - HRS.Whole.biasP d s) = Nr ^ (-HRS.Whole.biasTau d s) := by
    rw [hbp, hbt, hH]; exact s74_rpow_tau hp0 hN0
  have hψm : Measurable fun z : Euc d => rieszKernel d s (y - z) :=
    (wr13a_g_meas hs0).comp (measurable_const.sub measurable_id)
  have hl2 : Real.sqrt (∫ x, (φ x - 1) ^ 2 ∂μ) ≤ C0 * HRS.deltaN d s (m + 2) := hφn
  have hmain := s74_close_abstract (μ := μ) (ν := ν) (π := π) hK0 hνle hφm (fun x => hφb x) hπ hl2
    hTV (ψ := fun z => rieszKernel d s (y - z)) hψm (fun z => wr13a_g_nonneg hs0 _) hH0
    (E := |Ctr| * Nr ^ (-HRS.Whole.biasTau d s)) htri
    (by
      refine htrb.trans ?_
      rw [hHpow]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hN0.le _))
  obtain ⟨-, -, hfin⟩ := hmain
  have hG : ∫ Y : EucConfig d (m + 1), rieszKernel d s (y - Y 0) ∂P =
      ∫ z, rieszKernel d s (y - z) ∂ν :=
    (integral_map (μ := P) (φ := fun Y : EucConfig d (m + 1) => Y 0)
      (measurable_pi_apply 0).aemeasurable (f := fun z : Euc d => rieszKernel d s (y - z))
      hψm.aestronglyMeasurable).symm
  rw [hG]
  show |∫ z, rieszKernel d s (y - z) ∂ν - ∫ z, rieszKernel d s (y - z) ∂μ| ≤ _
  refine hfin.trans ?_
  have hHδ : H * Nr ^ (1 - p) = Nr ^ (-HRS.Whole.biasTau d s) := by
    rw [hbt, hH]; exact s74_rpow_tau' hp0 hN0
  have e1 : C0 * Real.sqrt (HRS.deltaN d s (m + 2) / ((m + 2 : ℕ) : ℝ)) ≤ |C0| * Nr ^ (1 - p) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hsq (abs_nonneg _))
  have e2 : C0 * HRS.deltaN d s (m + 2) ≤ |C0| * Nr ^ (1 - p) := by
    rw [hδ]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hδ0
  have h3 : H * (C0 * Real.sqrt (HRS.deltaN d s (m + 2) / ((m + 2 : ℕ) : ℝ)) +
      C0 * HRS.deltaN d s (m + 2)) ≤ 2 * |C0| * Nr ^ (-HRS.Whole.biasTau d s) := by
    calc _ ≤ H * (|C0| * Nr ^ (1 - p) + |C0| * Nr ^ (1 - p)) :=
          mul_le_mul_of_nonneg_left (add_le_add e1 e2) hH0.le
      _ = 2 * |C0| * (H * Nr ^ (1 - p)) := by ring
      _ = _ := by rw [hHδ]
  calc _ ≤ (K0 + 1) * (|Ctr| * Nr ^ (-HRS.Whole.biasTau d s)) + 2 * |C0| * Nr ^ (-HRS.Whole.biasTau d s) := by
        linarith
    _ = _ := by ring

end Close2

/-! ### The variance of the truncated potential -/

section Var

theorem s74_hvar (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {β : ℝ} (hβ : 0 < β) (m : ℕ)
    (y : Euc d) {C0 J : ℝ} (hSI : HRS.Whole.StaticInputConclusion d s (m + 2) β ρ C0) {H : ℝ}
    (hH : 0 < H)
    (hint2 : Integrable (fun z => (min (rieszKernel d s (y - z)) H) ^ 2) (HRS.Whole.withDensityReal ρ))
    (hI : ∫ z, (min (rieszKernel d s (y - z)) H) ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤ J) :
    ∫ Y : EucConfig d (m + 1), (∑ j : Fin (m + 1), min (rieszKernel d s (y - Y j)) H -
        ((m : ℝ) + 1) * ∫ Y' : EucConfig d (m + 1), min (rieszKernel d s (y - Y' 0)) H
          ∂(HRS.Whole.cavityLaw d s (m + 2) β (HRS.Whole.withDensityReal ρ))) ^ 2
      ∂(HRS.Whole.cavityLaw d s (m + 2) β (HRS.Whole.withDensityReal ρ)) ≤
    |C0| * ((m + 2 : ℕ) : ℝ) * |J| := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  haveI hμ := wr13a_isProb_density hρ
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  have hconv := wr13a_conv_le_density hd1 hs0 hsd hρ hM
  haveI hP : IsProbabilityMeasure (HRS.Whole.cavityLaw d s (m + 2) β μ) :=
    wr13a_cavityLaw_isProb hs0 hconv hβ.le (m + 2)
  set P : Measure (EucConfig d (m + 1)) := HRS.Whole.cavityLaw d s (m + 2) β μ with hPdef
  set f : Euc d → ℝ := fun z => min (rieszKernel d s (y - z)) H with hf
  have hfm : Measurable f := ((wr13a_g_meas hs0).comp (measurable_const.sub measurable_id)).min measurable_const
  have hf0 : ∀ z, 0 ≤ f z := fun z => le_min (wr13a_g_nonneg hs0 _) hH.le
  have hfH : ∀ z, f z ≤ H := fun z => min_le_right _ _
  have hmarg : ∀ j : Fin (m + 1), P.map (fun Y : EucConfig d (m + 1) => Y j) =
      P.map (fun Y : EucConfig d (m + 1) => Y 0) := fun j =>
    (wr13c2_cavityLaw_exchangeable hs0 hconv hβ.le (m + 2)).marginal_eq j ⟨0, by omega⟩
  have hm0 : Measurable (fun Y : EucConfig d (m + 1) => Y 0) := measurable_pi_apply 0
  have hfi0 : Integrable (fun Y : EucConfig d (m + 1) => f (Y 0)) P :=
    Integrable.of_bound (C := H) (hfm.comp hm0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]; exact hfH _)
  have hfj := fun j => s74_coord_int P hmarg hfm hfi0 j
  set cH : ℝ := ∫ Y : EucConfig d (m + 1), f (Y 0) ∂P with hcH
  have hint' : Integrable (fun z => |f z| ^ 2 * Real.exp (-(0 * (β / ((m + 2 : ℕ) : ℝ))) *
      rieszKernel d s ((0 : Euc d) - z))) μ := by
    simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, sq_abs]
    exact hint2
  have hpole := (hSI.2.2.2.1 (0 : Euc d) 0 ⟨le_rfl, zero_le_one⟩).2.2.2 f hfm hint'
  have hev : evariance (fun Y : EucConfig d (m + 1) => ∑ j : Fin (m + 1), f (Y j)) P ≤
      ENNReal.ofReal (C0 * (((m + 2 : ℕ) : ℝ) - 1) * ∫ z, |f z| ^ 2 * Real.exp
        (-(0 * (β / ((m + 2 : ℕ) : ℝ))) * rieszKernel d s ((0 : Euc d) - z)) ∂μ) := by
    have h := hpole
    rw [wr13c2_poleLaw_zero hs0 hconv hβ.le (m + 2) 0] at h
    exact h
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, sq_abs] at hev
  have hmean : ∫ Y, ∑ j : Fin (m + 1), f (Y j) ∂P = ((m : ℝ) + 1) * cH := by
    rw [integral_finsetSum _ fun j _ => (hfj j).1]
    have h : ∀ j : Fin (m + 1), ∫ Y, f (Y j) ∂P = cH := fun j => (hfj j).2
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hSm : Measurable fun Y : EucConfig d (m + 1) => ∑ j : Fin (m + 1), f (Y j) :=
    Finset.measurable_sum _ fun j _ => hfm.comp (measurable_pi_apply j)
  rw [evariance_eq_lintegral_ofReal] at hev
  simp only [hmean] at hev
  have hI0 : 0 ≤ ∫ z, f z ^ 2 ∂μ := integral_nonneg fun z => sq_nonneg _
  have hN1 : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) - 1 := by push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hbd : C0 * (((m + 2 : ℕ) : ℝ) - 1) * ∫ z, f z ^ 2 ∂μ ≤ |C0| * ((m + 2 : ℕ) : ℝ) * |J| := by
    have h1 : ∫ z, f z ^ 2 ∂μ ≤ |J| := hI.trans (le_abs_self _)
    have h2 : (((m + 2 : ℕ) : ℝ) - 1) ≤ ((m + 2 : ℕ) : ℝ) := by linarith
    calc C0 * (((m + 2 : ℕ) : ℝ) - 1) * ∫ z, f z ^ 2 ∂μ
        ≤ |C0| * (((m + 2 : ℕ) : ℝ) - 1) * ∫ z, f z ^ 2 ∂μ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hN1) hI0
      _ ≤ |C0| * ((m + 2 : ℕ) : ℝ) * |J| :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) h1 hI0 (by positivity)
  have hev2 : ∫⁻ Y, ENNReal.ofReal ((∑ j : Fin (m + 1), f (Y j) - ((m : ℝ) + 1) * cH) ^ 2) ∂P ≤
      ENNReal.ofReal (|C0| * ((m + 2 : ℕ) : ℝ) * |J|) :=
    hev.trans (ENNReal.ofReal_le_ofReal hbd)
  have hsqm : Measurable (fun Y : EucConfig d (m + 1) =>
      (∑ j : Fin (m + 1), f (Y j) - ((m : ℝ) + 1) * cH) ^ 2) := by
    have h := (hSm.sub (measurable_const (a := ((m : ℝ) + 1) * cH))).pow_const 2
    exact h
  show ∫ Y : EucConfig d (m + 1), (∑ j : Fin (m + 1), f (Y j) - ((m : ℝ) + 1) * cH) ^ 2 ∂P ≤ _
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun Y => sq_nonneg _)
    hsqm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hev2

end Var

/-! ### The uniform bound on the conditional potential -/

section Potential

theorem s74_exp1 {p N : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hN : 1 ≤ N) :
    N ^ (1 / p - 1) ≤ N ^ (-((p - 1) ^ 2 / p)) := by
  refine Real.rpow_le_rpow_of_exponent_le hN ?_
  have hp0 : 0 < p := by linarith
  have key : -((p - 1) ^ 2 / p) - (1 / p - 1) = (p - 1) * (2 - p) / p := by field_simp; ring
  have : 0 ≤ (p - 1) * (2 - p) / p := div_nonneg (mul_nonneg (by linarith) (by linarith)) hp0.le
  linarith

theorem s74_exp2 {p N : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hN : 1 ≤ N) :
    N ^ (-1 : ℝ) ≤ N ^ (-((p - 1) ^ 2 / p)) := by
  refine Real.rpow_le_rpow_of_exponent_le hN ?_
  have hp0 : 0 < p := by linarith
  have : (p - 1) ^ 2 / p ≤ 1 := (div_le_one hp0).2 (by nlinarith)
  linarith

theorem s74_potential (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (β M : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ (m : ℕ) (y : Euc d),
      Integrable (fun Y : EucConfig d (m + 1) =>
        |s74_u d s (HRS.Whole.withDensityReal ρ) (β / ((m + 2 : ℕ) : ℝ)) β (Fin.tail Y) y|)
        (HRS.Whole.cavityLaw d s (m + 2) β (HRS.Whole.withDensityReal ρ)) ∧
      ∫ Y : EucConfig d (m + 1),
          |s74_u d s (HRS.Whole.withDensityReal ρ) (β / ((m + 2 : ℕ) : ℝ)) β (Fin.tail Y) y|
        ∂(HRS.Whole.cavityLaw d s (m + 2) β (HRS.Whole.withDensityReal ρ)) ≤
      C * ((m + 2 : ℕ) : ℝ) ^ (-HRS.Whole.biasTau d s) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  obtain ⟨hp1, hp2⟩ := s74_p_bounds hd hs hsd
  obtain ⟨C0, hC0⟩ := static_input_proof hd hs hsd β M hβ
  obtain ⟨Ctr, hCtr⟩ := HRS.Whole.convolution_truncated hd hs hsd M
  set K0 : ℝ := Real.exp (2 * β * HRS.Whole.potentialBound d s M) with hK0def
  set Mg0 : ℝ := HRS.Whole.potentialBound d s M with hMg0def
  have hK0 : 0 ≤ K0 := (Real.exp_pos _).le
  refine ⟨β * (Real.sqrt (|C0| * |Ctr|) + 1) + 2 * β * (K0 * |Ctr|) +
    β * ((K0 + 1) * |Ctr| + 2 * |C0|) + 2 * β * (K0 * Mg0), fun ρ hρ hM m y => ?_⟩
  haveI hμ := wr13a_isProb_density hρ
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  have hconv := wr13a_conv_le_density hd1 hs0 hsd hρ hM
  have hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ := fun z =>
    (wr13a_potential_bound hd1 hs0 hsd hρ hM z).1
  have hMg := wr13a_potentialBound_nonneg hd1 hs0 hsd hρ hM
  set Nr : ℝ := ((m + 2 : ℕ) : ℝ) with hNr
  have hN2 : (2 : ℝ) ≤ Nr := by rw [hNr]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hN0 : 0 < Nr := by linarith
  have hN1 : 1 ≤ Nr := by linarith
  set p : ℝ := (d : ℝ) / s with hp
  have hp0 : 0 < p := by linarith
  have hbp : HRS.Whole.biasP d s = p := rfl
  have hbt : HRS.Whole.biasTau d s = (p - 1) ^ 2 / p := rfl
  set lam : ℝ := β / Nr with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hβ.le hN0.le
  have hlamN : lam * Nr = β := by rw [hlamdef]; field_simp
  have hlm : lam * m = β - 2 * lam := by
    have : (m : ℝ) = Nr - 2 := by rw [hNr]; push_cast; ring
    rw [this]; nlinarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  haveI hP : IsProbabilityMeasure (HRS.Whole.cavityLaw d s (m + 2) β μ) :=
    wr13a_cavityLaw_isProb hs0 hconv hβ.le (m + 2)
  set P : Measure (EucConfig d (m + 1)) := HRS.Whole.cavityLaw d s (m + 2) β μ with hPdef
  have hSI := hC0 ρ hρ hM (m + 2) (by omega)
  set H : ℝ := Nr ^ (1 / p) with hH
  have hH1 : 1 ≤ H := Real.one_le_rpow hN1 (by positivity)
  have hH0 : 0 < H := by linarith
  obtain ⟨hT2i, hT2b, hT1i, hT1b⟩ := hCtr ρ hρ hM H hH1 y
  have hψm : Measurable fun z : Euc d => rieszKernel d s (y - z) :=
    (wr13a_g_meas hs0).comp (measurable_const.sub measurable_id)
  have hψ0 : ∀ z : Euc d, 0 ≤ rieszKernel d s (y - z) := fun z => wr13a_g_nonneg hs0 _
  have hmarg : ∀ j : Fin (m + 1), P.map (fun Y : EucConfig d (m + 1) => Y j) =
      P.map (fun Y : EucConfig d (m + 1) => Y 0) := fun j =>
    (wr13c2_cavityLaw_exchangeable hs0 hconv hβ.le (m + 2)).marginal_eq j ⟨0, by omega⟩
  obtain ⟨hψi, hψbd⟩ := s74_coord_integral hs0 hint hconv hMg hβ.le m 0 hψm hψ0 (hint y)
  set G : ℝ := ∫ Y : EucConfig d (m + 1), rieszKernel d s (y - Y 0) ∂P with hG
  have hG0 : 0 ≤ G := integral_nonneg fun Y => hψ0 _
  have hGle : G ≤ K0 * Mg0 :=
    hψbd.trans (mul_le_mul_of_nonneg_left (hconv y) hK0)
  have hGc := s74_G_close hd hs hsd hρ hM hβ m y hSI (Ctr := Ctr)
    (fun H' hH' => ⟨(hCtr ρ hρ hM H' hH' y).2.2.1, (hCtr ρ hρ hM H' hH' y).2.2.2⟩)
  rw [← hG, hbt] at hGc
  have hvar := s74_hvar hd hs hsd hρ hM hβ m y hSI hH0 hT2i hT2b
  have hTb := s74_T_bound P hmarg hψm hψ0 hψi hH0 hlam
    (κ := β * HRS.Whole.convMeasure (rieszKernel d s) μ y) hvar
  refine ⟨hTb.1, hTb.2.trans ?_⟩
  rw [hbt]
  -- the tail term D
  have hD := (s74_coord_integral hs0 hint hconv hMg hβ.le m 0
    (ψ := fun z => rieszKernel d s (y - z) - min (rieszKernel d s (y - z)) H)
    (hψm.sub (hψm.min measurable_const)) (fun z => sub_nonneg.2 (min_le_left _ _)) hT1i).2
  have hHp : H ^ (1 - HRS.Whole.biasP d s) = Nr ^ (1 / p - 1) := by
    rw [hbp, hH, ← Real.rpow_mul hN0.le]; congr 1; field_simp
  have hHp0 : 0 ≤ Nr ^ (1 / p - 1) := Real.rpow_nonneg hN0.le _
  set X1 : ℝ := Nr ^ (1 / p - 1) with hX1
  set X : ℝ := Nr ^ (-((p - 1) ^ 2 / p)) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg hN0.le _
  have hX1X : X1 ≤ X := s74_exp1 hp1 hp2 hN1
  have hNinv : Nr ^ (-1 : ℝ) ≤ X := s74_exp2 hp1 hp2 hN1
  have hinv : 1 / Nr ≤ X := by
    have : Nr ^ (-1 : ℝ) = 1 / Nr := by rw [Real.rpow_neg_one, one_div]
    rw [← this]; exact hNinv
  set D : ℝ := ∫ Y : EucConfig d (m + 1), (rieszKernel d s (y - Y 0) -
    min (rieszKernel d s (y - Y 0)) H) ∂P with hDdef
  have hD0 : 0 ≤ D := integral_nonneg fun Y => by
    show (0 : ℝ) ≤ rieszKernel d s (y - Y 0) - min (rieszKernel d s (y - Y 0)) H
    exact sub_nonneg.2 (min_le_left _ _)
  have hDle : D ≤ K0 * (|Ctr| * X1) := by
    refine hD.trans (mul_le_mul_of_nonneg_left ?_ hK0)
    refine hT1b.trans ?_
    rw [hHp]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hHp0
  -- the variance term
  have hH2 : Nr * H ^ (2 - p) = H ^ 2 := by
    have h1 : H ^ p = Nr := by
      rw [hH, ← Real.rpow_mul hN0.le]; rw [one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
    calc Nr * H ^ (2 - p) = H ^ p * H ^ (2 - p) := by rw [h1]
      _ = H ^ (p + (2 - p)) := (Real.rpow_add hH0 _ _).symm
      _ = H ^ 2 := by rw [show p + (2 - p) = (2 : ℝ) by ring, Real.rpow_two]
  have hJ : |Ctr * H ^ (2 - HRS.Whole.biasP d s)| = |Ctr| * H ^ (2 - p) := by
    rw [hbp, abs_mul, abs_of_nonneg (Real.rpow_nonneg hH0.le _)]
  have hsqrt : Real.sqrt (|C0| * Nr * |Ctr * H ^ (2 - HRS.Whole.biasP d s)|) =
      Real.sqrt (|C0| * |Ctr|) * H := by
    rw [hJ]
    have : |C0| * Nr * (|Ctr| * H ^ (2 - p)) = (|C0| * |Ctr|) * H ^ 2 := by rw [← hH2]; ring
    rw [this, Real.sqrt_mul (mul_nonneg (abs_nonneg _) (abs_nonneg _)), Real.sqrt_sq hH0.le]
  have hlamH : lam * H = β * X1 := by
    rw [hlamdef, hX1, Real.rpow_sub_one hN0.ne', hH]; field_simp
  -- assemble
  rw [hsqrt]
  have hb1 : lam * (Real.sqrt (|C0| * |Ctr|) * H + H) = β * (Real.sqrt (|C0| * |Ctr|) + 1) * X1 := by
    have e : β * (Real.sqrt (|C0| * |Ctr|) + 1) * X1 = (Real.sqrt (|C0| * |Ctr|) + 1) * (β * X1) := by ring
    rw [e, ← hlamH]; ring
  have hb2 : 2 * (lam * m * D) ≤ 2 * β * (K0 * (|Ctr| * X1)) := by
    have h1 : lam * m ≤ β := by rw [hlm]; linarith
    have h2 : 0 ≤ lam * m := mul_nonneg hlam hm0
    calc 2 * (lam * m * D) ≤ 2 * (β * (K0 * (|Ctr| * X1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 hDle hD0 hβ.le) (by norm_num)
      _ = _ := by ring
  have hb3 : |lam * m * G - β * HRS.Whole.convMeasure (rieszKernel d s) μ y| ≤
      β * (((K0 + 1) * |Ctr| + 2 * |C0|) * X) + 2 * β * (K0 * Mg0) * X := by
    have e : lam * m * G - β * HRS.Whole.convMeasure (rieszKernel d s) μ y =
        β * (G - HRS.Whole.convMeasure (rieszKernel d s) μ y) - 2 * lam * G := by
      rw [hlm]; ring
    rw [e]
    have h1 : |β * (G - HRS.Whole.convMeasure (rieszKernel d s) μ y)| ≤
        β * (((K0 + 1) * |Ctr| + 2 * |C0|) * X) := by
      rw [abs_mul, abs_of_pos hβ]; exact mul_le_mul_of_nonneg_left hGc hβ.le
    have h2 : 2 * lam * G ≤ 2 * β * (K0 * Mg0) * X := by
      have : lam ≤ β * X := by
        have : lam = β * (1 / Nr) := by rw [hlamdef]; ring
        rw [this]; exact mul_le_mul_of_nonneg_left hinv hβ.le
      calc 2 * lam * G ≤ 2 * (β * X) * (K0 * Mg0) :=
            mul_le_mul (mul_le_mul_of_nonneg_left this (by norm_num)) hGle hG0 (by positivity)
        _ = _ := by ring
    have h3 : 0 ≤ 2 * lam * G := by positivity
    calc |β * (G - HRS.Whole.convMeasure (rieszKernel d s) μ y) - 2 * lam * G|
        ≤ |β * (G - HRS.Whole.convMeasure (rieszKernel d s) μ y)| + |2 * lam * G| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg h3]; exact add_le_add h1 h2
  have hs' : 0 ≤ Real.sqrt (|C0| * |Ctr|) := Real.sqrt_nonneg _
  calc lam * (Real.sqrt (|C0| * |Ctr|) * H + H) + 2 * (lam * m * D) +
        |lam * m * G - β * HRS.Whole.convMeasure (rieszKernel d s) μ y|
      ≤ β * (Real.sqrt (|C0| * |Ctr|) + 1) * X1 + 2 * β * (K0 * (|Ctr| * X1)) +
        (β * (((K0 + 1) * |Ctr| + 2 * |C0|) * X) + 2 * β * (K0 * Mg0) * X) := by
        rw [hb1]; linarith
    _ ≤ β * (Real.sqrt (|C0| * |Ctr|) + 1) * X + 2 * β * (K0 * (|Ctr| * X)) +
        (β * (((K0 + 1) * |Ctr| + 2 * |C0|) * X) + 2 * β * (K0 * Mg0) * X) := by
        have h1 : β * (Real.sqrt (|C0| * |Ctr|) + 1) * X1 ≤ β * (Real.sqrt (|C0| * |Ctr|) + 1) * X :=
          mul_le_mul_of_nonneg_left hX1X (by positivity)
        have h2 : 2 * β * (K0 * (|Ctr| * X1)) ≤ 2 * β * (K0 * (|Ctr| * X)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX1X
            (abs_nonneg _)) hK0) (by positivity)
        linarith
    _ = _ := by ring

end Potential

/-! ### The prefactor -/

section Prefactor

theorem s74_ofReal_mul_inv {Z : ℝ≥0∞} (hZ0 : Z ≠ 0) (hZt : Z ≠ ∞) {a : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal a * Z⁻¹ = ENNReal.ofReal (a / Z.toReal) := by
  have hz : 0 < Z.toReal := ENNReal.toReal_pos hZ0 hZt
  rw [div_eq_mul_inv, ENNReal.ofReal_mul ha, ENNReal.ofReal_inv_of_pos hz, ENNReal.ofReal_toReal hZt]

theorem s74_Zr_bounds {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg β t : ℝ} (hs0 : 0 < s)
    (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg)
    {lam : ℝ} (hlam : 0 ≤ lam) (hβ : 0 ≤ β) (ht : 0 ≤ t) (x : Euc d) {m : ℕ}
    (hK : lam * (t + m) ≤ β) (Y : EucConfig d m) :
    Real.exp (-(β * Mg)) ≤ (s74_Zc d s μ lam β t x Y).toReal ∧
      (s74_Zc d s μ lam β t x Y).toReal ≤ Real.exp (β * Mg) := by
  have h2 : s74_Zc d s μ lam β t x Y ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (s74_Zc_le hs0 hconv hlam hβ ht x Y)
  exact ⟨(ENNReal.ofReal_le_iff_le_toReal h2).1 (s74_Zc_ge hs0 hint hconv hMg hlam hβ ht x Y hK),
    ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le (s74_Zc_le hs0 hconv hlam hβ ht x Y)⟩

theorem s74_prefactor (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (β M : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ (m : ℕ) (x : Euc d),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Euc d,
        |s74_A d s (HRS.Whole.withDensityReal ρ) (β / ((m + 2 : ℕ) : ℝ)) β t x m y - 1| ≤
          C * ((m + 2 : ℕ) : ℝ) ^ (-HRS.Whole.biasTau d s) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  obtain ⟨hp1, hp2⟩ := s74_p_bounds hd hs hsd
  obtain ⟨Cu, hCu⟩ := s74_potential hd hs hsd β M hβ
  set Mg0 : ℝ := HRS.Whole.potentialBound d s M with hMg0def
  set K0 : ℝ := Real.exp (2 * β * Mg0) with hK0def
  set Kj : ℝ := Real.exp (β * (K0 * Mg0)) with hKjdef
  have hK0 : 0 ≤ K0 := (Real.exp_pos _).le
  have hKj : 0 ≤ Kj := (Real.exp_pos _).le
  refine ⟨Kj * K0 * (2 * |Cu| + β * Mg0), ?_⟩
  intro ρ hρ hM m x t ht y
  haveI hμ := wr13a_isProb_density hρ
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  have hconv := wr13a_conv_le_density hd1 hs0 hsd hρ hM
  have hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ := fun z =>
    (wr13a_potential_bound hd1 hs0 hsd hρ hM z).1
  have hMg := wr13a_potentialBound_nonneg hd1 hs0 hsd hρ hM
  set Nr : ℝ := ((m + 2 : ℕ) : ℝ) with hNr
  have hN2 : (2 : ℝ) ≤ Nr := by rw [hNr]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hN0 : 0 < Nr := by linarith
  have hN1 : 1 ≤ Nr := by linarith
  set p : ℝ := (d : ℝ) / s with hp
  have hp0 : 0 < p := by linarith
  have hbt : HRS.Whole.biasTau d s = (p - 1) ^ 2 / p := rfl
  rw [hbt]
  set X : ℝ := Nr ^ (-((p - 1) ^ 2 / p)) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg hN0.le _
  set lam : ℝ := β / Nr with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hβ.le hN0.le
  have hinv : 1 / Nr ≤ X := by
    have h : Nr ^ (-1 : ℝ) = 1 / Nr := by rw [Real.rpow_neg_one, one_div]
    rw [← h]; exact s74_exp2 hp1 hp2 hN1
  have hlamX : lam ≤ β * X := by
    have : lam = β * (1 / Nr) := by rw [hlamdef]; ring
    rw [this]; exact mul_le_mul_of_nonneg_left hinv hβ.le
  have hK : lam * (t + m) ≤ β := by
    have h := wr13a_lam_mul_le' (r := t + m) (c := 1) hβ.le (N := ((m + 2 : ℕ) : ℝ)) (by positivity)
      (by push_cast; linarith [ht.2])
    linarith
  haveI hP : IsProbabilityMeasure (HRS.Whole.cavityLaw d s (m + 2) β μ) :=
    wr13a_cavityLaw_isProb hs0 hconv hβ.le (m + 2)
  set P : Measure (EucConfig d (m + 1)) := HRS.Whole.cavityLaw d s (m + 2) β μ with hPdef
  haveI hPL : IsProbabilityMeasure (HRS.Whole.poleLaw d s (m + 2) β μ x t) :=
    wr13c2_poleLaw_isProb hs0 hconv hβ.le ht.1 (m + 2) x
  set PL : Measure (EucConfig d (m + 1)) := HRS.Whole.poleLaw d s (m + 2) β μ x t with hPLdef
  have hZ0 : ∀ Y : EucConfig d m, s74_Zc d s μ lam β t x Y ≠ 0 := fun Y => by
    have := s74_Zc_ge hs0 hint hconv hMg hlam hβ.le ht.1 x Y hK
    exact (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.exp_pos _)) this).ne'
  have hZt : ∀ Y : EucConfig d m, s74_Zc d s μ lam β t x Y ≠ ∞ := fun Y =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (s74_Zc_le hs0 hconv hlam hβ.le ht.1 x Y)
  have htail : Measurable (fun X : EucConfig d (m + 1) => (Fin.tail X : EucConfig d m)) :=
    measurable_pi_iff.2 fun j => measurable_pi_apply j.succ
  set r : EucConfig d (m + 1) → ℝ := fun X => Real.exp (-(s74_u d s μ lam β (Fin.tail X) y)) /
    (s74_Zc d s μ lam β t x (Fin.tail X)).toReal with hr
  have hu1 : Measurable (fun X : EucConfig d (m + 1) => s74_u d s μ lam β (Fin.tail X) y) := by
    have h := (s74_u_meas_Y hs0 μ lam β (m := m) y).comp htail
    exact h
  have hZm : Measurable (fun X : EucConfig d (m + 1) => (s74_Zc d s μ lam β t x (Fin.tail X)).toReal) := by
    have h := (s74_Zc_meas hs0 μ lam β t x m).comp htail
    exact h.ennreal_toReal
  have hrm : Measurable r := (Real.measurable_exp.comp hu1.neg).div hZm
  have hr0 : ∀ X, 0 ≤ r X := fun X => div_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  have hrb : ∀ X, r X ≤ K0 := by
    intro X
    obtain ⟨hlo, hup⟩ := s74_Zr_bounds hs0 hint hconv hMg hlam hβ.le ht.1 x hK (Fin.tail X)
    have hZpos : 0 < (s74_Zc d s μ lam β t x (Fin.tail X)).toReal := lt_of_lt_of_le (Real.exp_pos _) hlo
    simp only [hr]
    rw [div_le_iff₀ hZpos]
    have h1 : Real.exp (-(s74_u d s μ lam β (Fin.tail X) y)) ≤ Real.exp (β * Mg0) :=
      Real.exp_le_exp.2 (s74_neg_u_le hs0 hconv hlam hβ.le _ y)
    have h2 : Real.exp (β * Mg0) = K0 * Real.exp (-(β * Mg0)) := by
      rw [hK0def, ← Real.exp_add]; congr 1; ring
    calc Real.exp (-(s74_u d s μ lam β (Fin.tail X) y)) ≤ Real.exp (β * Mg0) := h1
      _ = K0 * Real.exp (-(β * Mg0)) := h2
      _ ≤ K0 * _ := mul_le_mul_of_nonneg_left hlo hK0
  have hri : ∀ κ : Measure (EucConfig d (m + 1)), IsFiniteMeasure κ → Integrable r κ := fun κ _ =>
    Integrable.of_bound (C := K0) hrm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hr0 X)]; exact hrb X)
  haveI : IsFiniteMeasure PL := inferInstance
  haveI : IsFiniteMeasure P := inferInstance
  -- A as an integral
  have hA : s74_A d s μ lam β t x m y = ∫ X, r X ∂PL := by
    have ha : s74_a d s μ lam β t x m y = ∫⁻ X : EucConfig d (m + 1),
        ENNReal.ofReal (Real.exp (-(s74_u d s μ lam β (Fin.tail X) y))) *
          (s74_Zc d s μ lam β t x (Fin.tail X))⁻¹ ∂PL :=
      s74_a_eq hs0 hint hconv hMg hβ.le ht.1 ht.2 m x y
    unfold s74_A
    rw [ha, lintegral_congr fun X => s74_ofReal_mul_inv (hZ0 _) (hZt _) (Real.exp_pos _).le]
    exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hr0)
      hrm.aestronglyMeasurable).symm
  -- domination
  have hle : PL ≤ ENNReal.ofReal Kj • P := s74_pole_le hs0 hint hconv hMg hβ.le ht.1 ht.2 m x
  have hrP : Integrable (fun X => |r X - 1|) P :=
    ((hri P inferInstance).sub (integrable_const 1)).abs
  have h1 : |s74_A d s μ lam β t x m y - 1| ≤ ∫ X, |r X - 1| ∂PL := by
    rw [hA]
    have : ∫ X, r X ∂PL - 1 = ∫ X, (r X - 1) ∂PL := by
      rw [integral_sub (hri PL inferInstance) (integrable_const 1)]; simp
    rw [this]
    exact abs_integral_le_integral_abs
  have h2 : ∫ X, |r X - 1| ∂PL ≤ Kj * ∫ X, |r X - 1| ∂P := by
    calc ∫ X, |r X - 1| ∂PL ≤ ∫ X, |r X - 1| ∂(ENNReal.ofReal Kj • P) :=
          integral_mono_measure hle (Filter.Eventually.of_forall fun X => abs_nonneg _)
            (hrP.smul_measure ENNReal.ofReal_ne_top)
      _ = Kj * ∫ X, |r X - 1| ∂P := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal hKj, smul_eq_mul]
  -- Fubini
  have hT : Measurable (fun q : EucConfig d (m + 1) × Euc d => ((Fin.tail q.1 : EucConfig d m), q.2)) :=
    (htail.comp measurable_fst).prodMk measurable_snd
  have hFm : Measurable (fun q : EucConfig d (m + 1) × Euc d =>
      |s74_u d s μ lam β (Fin.tail q.1) q.2|) := by
    have h := (s74_u_meas2 hs0 μ lam β (m := m)).comp hT
    exact h.abs
  have hcu : 0 ≤ |Cu| * X := mul_nonneg (abs_nonneg _) hX0
  have hCu' : ∀ z : Euc d, Integrable (fun Y : EucConfig d (m + 1) =>
      |s74_u d s μ lam β (Fin.tail Y) z|) P ∧ ∫ Y : EucConfig d (m + 1),
      |s74_u d s μ lam β (Fin.tail Y) z| ∂P ≤ |Cu| * X := fun z =>
    ⟨(hCu ρ hρ hM m z).1, (hCu ρ hρ hM m z).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)⟩
  obtain ⟨hUi, hUb⟩ := s74_fubini_bound P μ
    (fun (Y : EucConfig d (m + 1)) (z : Euc d) => |s74_u d s μ lam β (Fin.tail Y) z|) hFm
    (fun Y z => abs_nonneg _) hcu (fun z => (hCu' z).2) (fun z => (hCu' z).1)
    (fun Y => (s74_u_integrable hs0 hint hconv lam β (Fin.tail Y)).abs)
  have hpt : ∀ X : EucConfig d (m + 1), |r X - 1| ≤ K0 * (|s74_u d s μ lam β (Fin.tail X) y| +
      lam * Mg0 + ∫ z, |s74_u d s μ lam β (Fin.tail X) z| ∂μ) := fun X =>
    s74_ratio hs0 hint hconv hMg hlam hβ.le ht.1 ht.2 x hK (Fin.tail X) y
  have hRi : Integrable (fun X : EucConfig d (m + 1) => K0 * (|s74_u d s μ lam β (Fin.tail X) y| +
      lam * Mg0 + ∫ z, |s74_u d s μ lam β (Fin.tail X) z| ∂μ)) P :=
    (((hCu ρ hρ hM m y).1.add (integrable_const _)).add hUi).const_mul _
  have h3 : ∫ X, |r X - 1| ∂P ≤ K0 * (|Cu| * X + lam * Mg0 + |Cu| * X) := by
    calc ∫ X, |r X - 1| ∂P ≤ ∫ X : EucConfig d (m + 1), K0 * (|s74_u d s μ lam β (Fin.tail X) y| +
          lam * Mg0 + ∫ z, |s74_u d s μ lam β (Fin.tail X) z| ∂μ) ∂P :=
          integral_mono hrP hRi hpt
      _ = K0 * (∫ Y : EucConfig d (m + 1), |s74_u d s μ lam β (Fin.tail Y) y| ∂P + lam * Mg0 +
          ∫ X : EucConfig d (m + 1), ∫ z, |s74_u d s μ lam β (Fin.tail X) z| ∂μ ∂P) := by
          have hA1 : Integrable (fun X : EucConfig d (m + 1) =>
              |s74_u d s μ lam β (Fin.tail X) y|) P := (hCu ρ hρ hM m y).1
          have hA2 : Integrable (fun X : EucConfig d (m + 1) =>
              |s74_u d s μ lam β (Fin.tail X) y| + lam * Mg0) P := hA1.add (integrable_const _)
          rw [integral_const_mul, integral_add hA2 hUi, integral_add hA1 (integrable_const _)]
          simp
      _ ≤ K0 * (|Cu| * X + lam * Mg0 + |Cu| * X) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          have := (hCu' y).2
          linarith
  calc |s74_A d s μ lam β t x m y - 1| ≤ ∫ X, |r X - 1| ∂PL := h1
    _ ≤ Kj * ∫ X, |r X - 1| ∂P := h2
    _ ≤ Kj * (K0 * (|Cu| * X + lam * Mg0 + |Cu| * X)) := mul_le_mul_of_nonneg_left h3 hKj
    _ ≤ Kj * (K0 * (|Cu| * X + (β * X) * Mg0 + |Cu| * X)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hK0) hKj
        have := mul_le_mul_of_nonneg_right hlamX hMg
        linarith
    _ = _ := by ring

end Prefactor

/-! ### S7.4 -/

/-- **Proposition S7.4** (`HRS.Whole.conditional_density`). -/
theorem conditional_density_proof : type_of% @HRS.Whole.conditional_density := by
  intro d s hd hs hsd β M hβ
  obtain ⟨Cu, hCu⟩ := s74_potential hd hs hsd β M hβ
  obtain ⟨Cp, hCp⟩ := s74_prefactor hd hs hsd β M hβ
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  refine ⟨max Cu Cp, fun ρ hρ hM N hN => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  haveI hμ := wr13a_isProb_density hρ
  have hconv := wr13a_conv_le_density hd1 hs0 hsd hρ hM
  have hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) (HRS.Whole.withDensityReal ρ) :=
    fun z => (wr13a_potential_bound hd1 hs0 hsd hρ hM z).1
  have hMg := wr13a_potentialBound_nonneg hd1 hs0 hsd hρ hM
  have hX0 : 0 ≤ ((m + 2 : ℕ) : ℝ) ^ (-HRS.Whole.biasTau d s) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨fun y => ⟨?_, ?_⟩, fun x t ht => ?_⟩
  · refine (hCu ρ hρ hM m y).1.congr (Filter.Eventually.of_forall fun Y => ?_)
    show |s74_u d s (HRS.Whole.withDensityReal ρ) (β / ((m + 2 : ℕ) : ℝ)) β (Fin.tail Y) y| =
      |HRS.Whole.condPotential d s (m + 2) β (HRS.Whole.withDensityReal ρ) Y y|
    rw [s74_condPotential_eq]
  · have h := (hCu ρ hρ hM m y).2
    have e : ∫ Y : EucConfig d (m + 1), |HRS.Whole.condPotential d s (m + 2) β
        (HRS.Whole.withDensityReal ρ) Y y| ∂(HRS.Whole.cavityLaw d s (m + 2) β (HRS.Whole.withDensityReal ρ)) =
        ∫ Y : EucConfig d (m + 1), |s74_u d s (HRS.Whole.withDensityReal ρ) (β / ((m + 2 : ℕ) : ℝ)) β
          (Fin.tail Y) y| ∂(HRS.Whole.cavityLaw d s (m + 2) β (HRS.Whole.withDensityReal ρ)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
      show |HRS.Whole.condPotential d s (m + 2) β (HRS.Whole.withDensityReal ρ) Y y| = _
      rw [s74_condPotential_eq]
    exact (le_of_eq e).trans (h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0))
  · refine ⟨s74_A d s (HRS.Whole.withDensityReal ρ) (β / ((m + 2 : ℕ) : ℝ)) β t x m,
      s74_A_meas hs0 _ β t x m, ?_, Filter.Eventually.of_forall fun y => s74_A_nonneg _ β t x m y,
      Filter.Eventually.of_forall fun y => (hCp ρ hρ hM m x t ht y).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hX0)⟩
    exact s74_firstMarginal_A hs0 hint hconv hMg hβ.le ht.1 ht.2 m x

end HRS.MS.Wr
