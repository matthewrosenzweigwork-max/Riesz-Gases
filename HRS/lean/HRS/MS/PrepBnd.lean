import HRS.MS.PrepBndAux1
import HRS.Whole.HeadlineStatement

/-!
# HRS.MS.PrepBnd -- the preparation entropy bounds of Corollary S3.2 (packet PREP)

Packet PREP of `docs/SUPP_FOUND_PACKETS.md` (Track D), namespace `HRS.MS.Wr`.

* `prep_kl_pi_gibbs`: `H(μ^{⊗N} | Q_{N,b}) = ofReal (log K_b + b N E_{μ^N} F)` (exact, in `ℝ≥0∞`).
* `prep_kl_gibbs_gibbs`: `H(Q_{N,b₀} | Q_{N,b}) = ofReal (log K_b - log K_{b₀} + (b - b₀) N E_{Q_{b₀}} F)`.
* `prep_double_lower`: `-(1/2) ∬ g dμ² ≤ max L 0` (`g ≥ 0` for `s > 0`; the elementary bound
  `-log|x-y| ≥ -log(2+|x|) - log(2+|y|)` and the log moment for `s = 0`).
* `euclidean_preparations_bounds_proof : type_of% @HRS.Whole.euclidean_preparations_bounds`: the pressure
  bound (`euclidean_pressure_proof` at `θ = 0`, `h = 0`) on `[min(b,b₀), max(b,b₀)+1]`, the identity
  `E_{μ^N}[N F] = -(1/2) ∬ g` (`wr8_integral_mul_modEnergyE`) and `E_{Q_{b₀}}[N |F|] ≤ C N δ_N`
  (`euclidean_pair_entropy_self_proof` with `f = Q_{b₀}`, `H(Q_{b₀}|Q_{b₀}) = 0`).

Statement adjustments: none.  The finiteness of both relative entropies follows from the identities.
Helper lemmas carry the prefix `prep_`.  Tie in `HRS/MS/PrepBndTie.lean`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.Whole

variable {d N : ℕ}

/-! ### Identities for the relative entropies -/

theorem prep_kl_pi_gibbs {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ}
    {b : ℝ} (hGm : Measurable (Function.uncurry G)) (hW : GibbsWellDefined G N b μ)
    (hint : Integrable (fun X : EucConfig d N => pairEnergy G X μ) (Measure.pi fun _ : Fin N => μ)) :
    relEntropy (Measure.pi fun _ : Fin N => μ) (pairGibbs G N b μ) =
      ENNReal.ofReal (Real.log (pairNormalizer G N b μ) +
        b * N * ∫ X : EucConfig d N, pairEnergy G X μ ∂(Measure.pi fun _ : Fin N => μ)) := by
  have hF : Measurable (fun X : EucConfig d N => pairEnergy G X μ) :=
    wr9_measurable_pairEnergy hGm
  have h0 : ∫⁻ X : EucConfig d N, ENNReal.ofReal (Real.exp (0 * pairEnergy G X μ))
      ∂(Measure.pi fun _ : Fin N => μ) = ENNReal.ofReal 1 := by
    simp
  have key := prep_kl_gibbs (Measure.pi fun _ : Fin N => μ) hF (a0 := 0) (a1 := -b * N)
    (K0 := 1) (K1 := pairNormalizer G N b μ) one_pos hW.normalizer_pos h0
    (wr9_partition hW) (Measure.pi fun _ : Fin N => μ) (pairGibbs G N b μ)
    (by simp) rfl hint
  unfold relEntropy
  rw [key]
  congr 1
  rw [Real.log_one]
  ring

theorem prep_kl_gibbs_gibbs {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ}
    {b b0 : ℝ} (hGm : Measurable (Function.uncurry G)) (hW : GibbsWellDefined G N b μ)
    (hW0 : GibbsWellDefined G N b0 μ)
    (hint : Integrable (fun X : EucConfig d N => pairEnergy G X μ) (pairGibbs G N b0 μ)) :
    relEntropy (pairGibbs G N b0 μ) (pairGibbs G N b μ) =
      ENNReal.ofReal (Real.log (pairNormalizer G N b μ) - Real.log (pairNormalizer G N b0 μ) +
        (b - b0) * N * ∫ X : EucConfig d N, pairEnergy G X μ ∂(pairGibbs G N b0 μ)) := by
  have hF : Measurable (fun X : EucConfig d N => pairEnergy G X μ) :=
    wr9_measurable_pairEnergy hGm
  have key := prep_kl_gibbs (Measure.pi fun _ : Fin N => μ) hF (a0 := -b0 * N) (a1 := -b * N)
    hW0.normalizer_pos hW.normalizer_pos (wr9_partition hW0) (wr9_partition hW)
    (pairGibbs G N b0 μ) (pairGibbs G N b μ) rfl rfl hint
  unfold relEntropy
  rw [key]
  congr 1
  ring

/-! ### The diagonal term -/

theorem prep_riesz_nonneg {s : ℝ} (hs : s ≠ 0) (z : Euc d) : 0 ≤ rieszKernel d s z := by
  unfold rieszKernel
  rw [if_neg hs]
  exact Real.rpow_nonneg (norm_nonneg _) _

theorem prep_log_le (x y : Euc d) :
    Real.log ‖x - y‖ ≤ Real.log (2 + ‖x‖) + Real.log (2 + ‖y‖) := by
  have hx : 0 < 2 + ‖x‖ := by positivity
  have hy : 0 < 2 + ‖y‖ := by positivity
  have hx1 : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
  have hy1 : 0 ≤ Real.log (2 + ‖y‖) := Real.log_nonneg (by linarith [norm_nonneg y])
  rcases (norm_nonneg (x - y)).eq_or_lt with h | h
  · rw [← h, Real.log_zero]; linarith
  · rw [← Real.log_mul hx.ne' hy.ne']
    refine Real.log_le_log h ?_
    have := norm_sub_le x y
    nlinarith [norm_nonneg x, norm_nonneg y]

theorem prep_double_lower {s L : ℝ} (hs0 : 0 ≤ s) {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (hlog : s = 0 → HasLogMoment μ L)
    (hint : Integrable (fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2)) (μ.prod μ)) :
    -(1 / 2) * ∫ p : Euc d × Euc d, rieszKernel d s (p.1 - p.2) ∂(μ.prod μ) ≤ max L 0 := by
  by_cases hs : s = 0
  · obtain ⟨hai, hal⟩ := hlog hs
    set a : Euc d → ℝ := fun x => Real.log (2 + ‖x‖) with ha
    have hsum : Integrable (fun p : Euc d × Euc d => a p.1 + a p.2) (μ.prod μ) :=
      (hai.comp_fst μ).add (hai.comp_snd μ)
    have hpt : ∀ p : Euc d × Euc d, -(a p.1 + a p.2) ≤ rieszKernel d s (p.1 - p.2) := by
      intro p
      unfold rieszKernel
      rw [if_pos hs]
      have := prep_log_le p.1 p.2
      simp only [ha]
      linarith
    have hle : ∫ p : Euc d × Euc d, -(a p.1 + a p.2) ∂(μ.prod μ) ≤
        ∫ p : Euc d × Euc d, rieszKernel d s (p.1 - p.2) ∂(μ.prod μ) :=
      integral_mono hsum.neg hint hpt
    have hI : ∫ p : Euc d × Euc d, (a p.1 + a p.2) ∂(μ.prod μ) = 2 * ∫ x, a x ∂μ := by
      rw [integral_prod _ hsum]
      simp only
      have h1 : ∀ x, ∫ y, (a x + a y) ∂μ = a x + ∫ y, a y ∂μ := fun x => by
        rw [integral_add (integrable_const _) hai]; simp
      simp_rw [h1]
      rw [integral_add hai (integrable_const _)]
      simp; ring
    rw [integral_neg, hI] at hle
    have : 0 ≤ max L 0 - L := by linarith [le_max_left L 0]
    nlinarith [le_max_left L 0]
  · have h0 : 0 ≤ ∫ p : Euc d × Euc d, rieszKernel d s (p.1 - p.2) ∂(μ.prod μ) :=
      integral_nonneg fun p => prep_riesz_nonneg hs _
    nlinarith [le_max_right L 0]

/-! ### The theorem -/

theorem euclidean_preparations_bounds_proof :
    HRS.Whole.EuclideanPreparationsBoundsStatement := by
  intro d s hd hs0 hsd M L b b0 hb hb0
  set bm : ℝ := min b b0 with hbm
  set bp : ℝ := max b b0 + 1 with hbp
  have hbm0 : 0 < bm := lt_min hb hb0
  have hbmp : bm < bp := by
    have := min_le_max (a := b) (b := b0); simp only [hbm, hbp]; linarith
  have hbI : b ∈ Set.Icc bm bp := ⟨min_le_left _ _, by simp only [hbp]; linarith [le_max_left b b0]⟩
  have hb0I : b0 ∈ Set.Icc bm bp :=
    ⟨min_le_right _ _, by simp only [hbp]; linarith [le_max_right b b0]⟩
  obtain ⟨θ0, hθ0, C0, hP⟩ := euclidean_pressure_proof hd hs0 hsd M L bm bp 0 hbm0 hbmp
  obtain ⟨c, hc, C1, hS⟩ := euclidean_pair_entropy_self_proof hd hs0 hsd M L bm bp hbm0 hbmp
  have hhz : IsBoundedPairKernel s 0 (fun _ _ : Euc d => (0 : ℝ)) :=
    ⟨measurable_const, fun _ _ => rfl, fun x y _ => by simp⟩
  refine ⟨(max C0 0 * 3 + b * max L 0 + |b - b0| * max C1 0 + 1), ?_⟩
  intro ρ hρ hρM hlog N hN
  have hμprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set T : ℝ := (N : ℝ) * deltaN d s N with hT
  have hT1 : 1 ≤ T := wr8_one_le_mul_deltaN hs0 N (by omega)
  have hN1 : 1 ≤ N := by omega
  set G : Euc d → Euc d → ℝ := fun x y => rieszKernel d s (x - y) with hG
  have hGm : Measurable (Function.uncurry G) := wr9_rieszKernel_pair_meas s
  have key : ∀ b' ∈ Set.Icc bm bp, GibbsWellDefined G N b' μ ∧
      |Real.log (pairNormalizer G N b' μ)| ≤ C0 * T := by
    intro b' hb''
    obtain ⟨hW, hbd⟩ := hP ρ hρ hρM hlog (fun _ _ => 0) hhz N hN b' hb'' 0
      (by rw [abs_zero]; exact hθ0.le)
    simp only [zero_mul, sub_zero] at hW hbd
    exact ⟨hW, by simpa only [hT, mul_assoc] using hbd⟩
  obtain ⟨hW, hlogK⟩ := key b hbI
  obtain ⟨hW0, hlogK0⟩ := key b0 hb0I
  have hC0 : 0 ≤ C0 := wr9_nonneg_of_abs_le hlogK hT1
  have hok : Wr8Ok μ G := wr9_ok_of_gwd hGm hW
  -- first term
  have hint1 : Integrable (fun X : EucConfig d N => pairEnergy G X μ) (Measure.pi fun _ : Fin N => μ) :=
    wr8_integrable_modEnergyE hok
  have hmean : ∫ X : EucConfig d N, (N : ℝ) * pairEnergy G X μ ∂(Measure.pi fun _ : Fin N => μ) =
      -(1 / 2) * ∫ p : Euc d × Euc d, G p.1 p.2 ∂(μ.prod μ) :=
    wr8_integral_mul_modEnergyE hok hN1
  have hdl := prep_double_lower (L := L) hs0 hlog hok.prod
  have hE1 : (N : ℝ) * ∫ X : EucConfig d N, pairEnergy G X μ ∂(Measure.pi fun _ : Fin N => μ) ≤
      max L 0 := by
    rw [← integral_const_mul, hmean]; exact hdl
  have hK1 := (abs_le.1 hlogK).2
  have hK0u := abs_le.1 hlogK0
  have hK0u2 := abs_le.1 hlogK
  have hA : relEntropy (Measure.pi fun _ : Fin N => μ) (HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ) ≤
      ENNReal.ofReal ((max C0 0 + b * max L 0) * T) := by
    have := prep_kl_pi_gibbs hGm hW hint1
    show relEntropy _ (pairGibbs G N b μ) ≤ _
    rw [this]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : b * N * ∫ X : EucConfig d N, pairEnergy G X μ ∂(Measure.pi fun _ : Fin N => μ) =
        b * ((N : ℝ) * ∫ X : EucConfig d N, pairEnergy G X μ ∂(Measure.pi fun _ : Fin N => μ)) := by
      ring
    rw [e]
    have h1 : b * ((N : ℝ) * ∫ X : EucConfig d N, pairEnergy G X μ ∂(Measure.pi fun _ : Fin N => μ)) ≤
        b * max L 0 := mul_le_mul_of_nonneg_left hE1 hb.le
    have h2 : b * max L 0 ≤ b * max L 0 * T := by
      have : 0 ≤ b * max L 0 := mul_nonneg hb.le (le_max_right _ _)
      nlinarith
    have h3 : C0 * T ≤ max C0 0 * T :=
      mul_le_mul_of_nonneg_right (le_max_left C0 0) (by linarith)
    linarith
  -- second term
  obtain ⟨-, hSb⟩ := hS ρ hρ hρM hlog N hN b0 hb0I
  have hQprob : IsProbabilityMeasure (pairGibbs G N b0 μ) := wr9_gibbs_prob hW0
  obtain ⟨hi2, hb2⟩ := hSb (pairGibbs G N b0 μ) hQprob (by
    show relEntropy (pairGibbs G N b0 μ) (pairGibbs G N b0 μ) < ⊤
    unfold relEntropy; rw [InformationTheory.klDiv_self]; exact ENNReal.zero_lt_top)
  have hself : relEntropy (pairGibbs G N b0 μ) (HRS.Whole.modulatedGibbs (rieszKernel d s) N b0 μ) = 0 := by
    show relEntropy (pairGibbs G N b0 μ) (pairGibbs G N b0 μ) = 0
    unfold relEntropy; exact InformationTheory.klDiv_self _
  rw [hself] at hb2
  simp only [ENNReal.toReal_zero, zero_add] at hb2
  have hi2' : Integrable (fun X : EucConfig d N => (N : ℝ) * |pairEnergy G X μ|)
      (pairGibbs G N b0 μ) := hi2
  have hb2' : ∫ X : EucConfig d N, (N : ℝ) * |pairEnergy G X μ| ∂(pairGibbs G N b0 μ) ≤ C1 * T := hb2
  have hFi : Integrable (fun X : EucConfig d N => pairEnergy G X μ) (pairGibbs G N b0 μ) := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h1 : Integrable (fun X : EucConfig d N => |pairEnergy G X μ|) (pairGibbs G N b0 μ) :=
      (hi2'.const_mul (N : ℝ)⁻¹).congr (Filter.Eventually.of_forall fun X => by
        simp only; field_simp)
    exact (integrable_norm_iff (wr9_measurable_pairEnergy hGm).aestronglyMeasurable).1
      (by simpa only [Real.norm_eq_abs] using h1)
  have hB : |(N : ℝ) * ∫ X : EucConfig d N, pairEnergy G X μ ∂(pairGibbs G N b0 μ)| ≤ C1 * T := by
    have h1 : |∫ X : EucConfig d N, pairEnergy G X μ ∂(pairGibbs G N b0 μ)| ≤
        ∫ X : EucConfig d N, |pairEnergy G X μ| ∂(pairGibbs G N b0 μ) :=
      abs_integral_le_integral_abs
    have h2 : ∫ X : EucConfig d N, (N : ℝ) * |pairEnergy G X μ| ∂(pairGibbs G N b0 μ) =
        (N : ℝ) * ∫ X : EucConfig d N, |pairEnergy G X μ| ∂(pairGibbs G N b0 μ) :=
      integral_const_mul _ _
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [abs_mul, abs_of_nonneg hN0]
    refine le_trans (mul_le_mul_of_nonneg_left h1 hN0) ?_
    rw [← h2]
    exact hb2'
  have hC1 : 0 ≤ C1 := by
    have : 0 ≤ C1 * T := (abs_nonneg _).trans hB
    by_contra hneg
    push Not at hneg
    nlinarith
  have hBm : |(b - b0) * ((N : ℝ) * ∫ X : EucConfig d N, pairEnergy G X μ ∂(pairGibbs G N b0 μ))| ≤
      |b - b0| * C1 * T := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hB (abs_nonneg _)
  have hRB : relEntropy (pairGibbs G N b0 μ) (HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ) ≤
      ENNReal.ofReal ((2 * max C0 0 + |b - b0| * max C1 0) * T) := by
    have := prep_kl_gibbs_gibbs hGm hW hW0 hFi
    show relEntropy _ (pairGibbs G N b μ) ≤ _
    rw [this]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : (b - b0) * N * ∫ X : EucConfig d N, pairEnergy G X μ ∂(pairGibbs G N b0 μ) =
        (b - b0) * ((N : ℝ) * ∫ X : EucConfig d N, pairEnergy G X μ ∂(pairGibbs G N b0 μ)) := by
      ring
    rw [e]
    have hC0m : C0 ≤ max C0 0 := le_max_left _ _
    have hC1m : C1 ≤ max C1 0 := le_max_left _ _
    have h3 : |b - b0| * C1 * T ≤ |b - b0| * max C1 0 * T := by
      have : 0 ≤ |b - b0| * T := mul_nonneg (abs_nonneg _) (by linarith)
      calc |b - b0| * C1 * T = (|b - b0| * T) * C1 := by ring
        _ ≤ (|b - b0| * T) * max C1 0 := mul_le_mul_of_nonneg_left hC1m this
        _ = _ := by ring
    have h4 : C0 * T ≤ max C0 0 * T :=
      mul_le_mul_of_nonneg_right hC0m (by linarith)
    have h5 := (abs_le.1 hBm).2
    have h6 := (abs_le.1 hlogK).1
    have h7 := (abs_le.1 hlogK0)
    have h8 : Real.log (pairNormalizer G N b μ) - Real.log (pairNormalizer G N b0 μ) ≤ 2 * (C0 * T) := by
      linarith [h7.1, (abs_le.1 hlogK).2]
    linarith
  have hnn1 : 0 ≤ (max C0 0 + b * max L 0) * T := by
    have : 0 ≤ b * max L 0 := mul_nonneg hb.le (le_max_right _ _)
    have := le_max_right C0 0
    positivity
  have hnn2 : 0 ≤ (2 * max C0 0 + |b - b0| * max C1 0) * T := by
    have := le_max_right C0 0
    have := le_max_right C1 0
    positivity
  calc _ ≤ ENNReal.ofReal ((max C0 0 + b * max L 0) * T) +
        ENNReal.ofReal ((2 * max C0 0 + |b - b0| * max C1 0) * T) := add_le_add hA hRB
    _ = ENNReal.ofReal ((max C0 0 + b * max L 0) * T + (2 * max C0 0 + |b - b0| * max C1 0) * T) :=
        (ENNReal.ofReal_add hnn1 hnn2).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : (max C0 0 * 3 + b * max L 0 + |b - b0| * max C1 0 + 1) * (N : ℝ) *
            deltaN d s N = (max C0 0 * 3 + b * max L 0 + |b - b0| * max C1 0 + 1) * T := by
          rw [hT]; ring
        rw [this]
        linarith

end HRS.MS.Wr
