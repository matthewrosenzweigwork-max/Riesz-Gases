import HRS.MS.R2PolyAux1

/-!
# HRS.MS.R2PolyAux2 -- Step B of `round2_polynomial_moments` (S9.5): annular summation

Packet S95, namespace `HRS.MS.R2Poly`, helper prefix `s95_`.  Infrastructure statements (not manuscript rows).

* `s95_pe_smul`, `s95_pe_add`, `s95_pe_tendsto`: linearity of `pairEnergy` in the kernel and convergence along the
  annular partial sums `part g K = 1_{max(|x|,|y|) ≤ K} g`.
* `s95_F_main`: `‖N F^g‖_{L^r(P_N)} ≤ ∑_k ‖N F^{piece g k}‖` for a polynomial-envelope kernel, with the pieces controlled by
  `s95_F_small` and the annular `L²(μ⊗μ)` masses.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Poly

open HRS.Whole HRS.MS.Wr HRS.MS.R2Mt HRS.MS.PrepStat

variable {d N : ℕ}

/-! ### Linearity of `pairEnergy` in the kernel -/

theorem s95_pe_smul (c : ℝ) (k : Euc d → Euc d → ℝ) (X : EucConfig d N) (μ : Measure (Euc d)) :
    pairEnergy (fun x y => c * k x y) X μ = c * pairEnergy k X μ := by
  unfold pairEnergy
  simp only [← Finset.mul_sum, integral_const_mul]
  ring

theorem s95_pe_add {μ : Measure (Euc d)} {k1 k2 : Euc d → Euc d → ℝ} (h1 : ∀ x, Integrable (k1 x) μ)
    (h2 : ∀ x, Integrable (k2 x) μ) (H1 : Integrable (wr14a_Hc k1 μ) μ) (H2 : Integrable (wr14a_Hc k2 μ) μ)
    (X : EucConfig d N) :
    pairEnergy (fun x y => k1 x y + k2 x y) X μ = pairEnergy k1 X μ + pairEnergy k2 X μ := by
  unfold pairEnergy
  have e1 : ∀ x, ∫ y, (k1 x y + k2 x y) ∂μ = ∫ y, k1 x y ∂μ + ∫ y, k2 x y ∂μ :=
    fun x => integral_add (h1 x) (h2 x)
  simp only [e1, Finset.sum_add_distrib]
  have e2 : ∫ x, (∫ y, k1 x y ∂μ + ∫ y, k2 x y ∂μ) ∂μ =
      (∫ x, ∫ y, k1 x y ∂μ ∂μ) + ∫ x, ∫ y, k2 x y ∂μ ∂μ := integral_add H1 H2
  rw [e2]
  ring

/-! ### Annular parts and pieces -/

/-- `1_{max(|x|,|y|) ≤ K} g`. -/
def s95_part (g : Euc d → Euc d → ℝ) (K : ℕ) : Euc d → Euc d → ℝ := s95_cut (-1) K g

/-- `1_{k - 1 < max(|x|,|y|) ≤ k} g`. -/
def s95_piece (g : Euc d → Euc d → ℝ) (k : ℕ) : Euc d → Euc d → ℝ := s95_cut ((k : ℝ) - 1) k g

theorem s95_max_nonneg (x y : Euc d) : 0 ≤ max ‖x‖ ‖y‖ := le_max_of_le_left (norm_nonneg x)

theorem s95_part_succ (g : Euc d → Euc d → ℝ) (K : ℕ) (x y : Euc d) :
    s95_part g (K + 1) x y = s95_part g K x y + s95_piece g (K + 1) x y := by
  have hm := s95_max_nonneg x y
  have e : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
  unfold s95_part s95_piece s95_cut
  rw [e]
  have h0 : (-1 : ℝ) < max ‖x‖ ‖y‖ := by linarith
  by_cases h1 : max ‖x‖ ‖y‖ ≤ (K : ℝ)
  · rw [if_pos ⟨h0, by linarith⟩, if_pos ⟨h0, h1⟩, if_neg (fun h => by linarith [h.1])]
    ring
  · by_cases h2 : max ‖x‖ ‖y‖ ≤ (K : ℝ) + 1
    · rw [if_pos ⟨h0, h2⟩, if_neg (fun h => h1 h.2), if_pos ⟨by linarith [not_le.1 h1], h2⟩]
      ring
    · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h1 (by linarith [h.2])), if_neg (fun h => h2 h.2)]
      ring

theorem s95_part_zero (g : Euc d → Euc d → ℝ) : s95_part g 0 = s95_piece g 0 := by
  unfold s95_part s95_piece
  simp

theorem s95_part_eq (g : Euc d → Euc d → ℝ) {K : ℕ} {x y : Euc d} (h : max ‖x‖ ‖y‖ ≤ K) :
    s95_part g K x y = g x y := by
  unfold s95_part s95_cut
  rw [if_pos ⟨by linarith [s95_max_nonneg x y], h⟩]

theorem s95_cut_abs_le (lo hi : ℝ) (g : Euc d → Euc d → ℝ) (x y : Euc d) : ‖s95_cut lo hi g x y‖ ≤ ‖g x y‖ := by
  unfold s95_cut
  split_ifs
  · exact le_rfl
  · simp

theorem s95_part_tendsto (g : Euc d → Euc d → ℝ) (x y : Euc d) :
    Tendsto (fun K : ℕ => s95_part g K x y) atTop (𝓝 (g x y)) := by
  obtain ⟨K0, hK0⟩ := exists_nat_ge (max ‖x‖ ‖y‖)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop K0] with K hK
  exact (s95_part_eq g (hK0.trans (by exact_mod_cast hK))).symm


theorem s95_pe_tendsto {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {g : Euc d → Euc d → ℝ}
    (hm : Measurable (Function.uncurry g)) (hsec : ∀ x, Integrable (g x) μ)
    (hint : Integrable (Function.uncurry g) (μ.prod μ)) (X : EucConfig d N) :
    Tendsto (fun K : ℕ => pairEnergy (s95_part g K) X μ) atTop (𝓝 (pairEnergy g X μ)) := by
  have hmeas : ∀ K, Measurable (Function.uncurry (s95_part g K)) := fun K => s95_cut_meas hm _ _
  have T1 : Tendsto (fun K : ℕ => ∑ i, ∑ j ∈ Finset.univ.erase i, s95_part g K (X i) (X j)) atTop
      (𝓝 (∑ i, ∑ j ∈ Finset.univ.erase i, g (X i) (X j))) :=
    tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => s95_part_tendsto g _ _
  have T2 : ∀ x, Tendsto (fun K : ℕ => ∫ y, s95_part g K x y ∂μ) atTop (𝓝 (∫ y, g x y ∂μ)) := fun x =>
    tendsto_integral_of_dominated_convergence (fun y => ‖g x y‖)
      (fun K => ((hmeas K).comp measurable_prodMk_left).aestronglyMeasurable) (hsec x).norm
      (fun K => Eventually.of_forall fun y => s95_cut_abs_le _ _ g x y)
      (Eventually.of_forall fun y => s95_part_tendsto g x y)
  have hbd : Integrable (fun x => ∫ y, ‖g x y‖ ∂μ) μ := hint.norm.integral_prod_left
  have T3 : Tendsto (fun K : ℕ => ∫ x, ∫ y, s95_part g K x y ∂μ ∂μ) atTop (𝓝 (∫ x, ∫ y, g x y ∂μ ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ∫ y, ‖g x y‖ ∂μ)
      (fun K => (wr14a_measurable_Hc (hmeas K) μ).aestronglyMeasurable) hbd
      (fun K => Eventually.of_forall fun x => norm_integral_le_of_norm_le (hsec x).norm
        (Eventually.of_forall fun y => s95_cut_abs_le _ _ g x y))
      (Eventually.of_forall T2)
  unfold pairEnergy
  exact ((T1.const_mul _).sub ((tendsto_finset_sum _ fun i _ => T2 (X i)).const_mul _)).add (T3.const_mul _)


/-! ### Summation over annuli -/

theorem s95_lim_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℝ≥0∞} {f : ℕ → Ω → ℝ} {f₀ : Ω → ℝ}
    (hf : ∀ K, Measurable (f K)) (hf₀ : Measurable f₀) (hlim : ∀ x, Tendsto (fun K => f K x) atTop (𝓝 (f₀ x)))
    {E : ℝ≥0∞} (hE : ∀ K, eLpNorm (f K) p P ≤ E) : eLpNorm f₀ p P ≤ E :=
  (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun K => (hf K).aestronglyMeasurable) f₀ hf₀.aestronglyMeasurable
    (Eventually.of_forall hlim)).trans (Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hE))

theorem s95_bdd_scale {s B : ℝ} (hB : 0 < B) {k : Euc d → Euc d → ℝ} (hk : IsBoundedPairKernel s B k) :
    IsBoundedPairKernel s 1 (fun x y => B⁻¹ * k x y) where
  measurable := measurable_const.mul hk.measurable
  symm x y := by rw [hk.symm x y]
  bound x y hxy := by
    have h := hk.bound x y hxy
    rw [abs_mul, abs_of_pos (inv_pos.2 hB)]
    calc B⁻¹ * |k x y| ≤ B⁻¹ * (B * (1 + HRS.Whole.rieszWeight s (x - y))) := by gcongr
      _ = 1 * (1 + HRS.Whole.rieszWeight s (x - y)) := by field_simp

theorem s95_poly_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M C₀ c₀ : ℝ) (hc : 0 < c₀)
    {Pw : ℝ} (hP : 0 ≤ Pw) :
    ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) → (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) →
      ∀ B : ℝ, 0 ≤ B → ∀ g : Euc d → Euc d → ℝ, IsR2PolyPairKernel s Pw B g →
      (∀ x, Integrable (g x) (HRS.Whole.withDensityReal ρ)) ∧
      Integrable (Function.uncurry g) ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := by
  obtain ⟨A, hA, hpoly⟩ := s95_poly_int hd hs0 hs M C₀ c₀ hc hP
  intro ρ hρ hM hG B hB g hg
  obtain ⟨h1, h2⟩ := hpoly ρ hρ hM hG B hB g hg
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  refine ⟨fun x => ⟨((hg.measurable.comp measurable_prodMk_left) : Measurable (g x)).aestronglyMeasurable,
    (h1 x).trans_lt ENNReal.ofReal_lt_top⟩, ⟨hg.measurable.aestronglyMeasurable, ?_⟩⟩
  have : ∫⁻ p : Euc d × Euc d, ‖Function.uncurry g p‖ₑ ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) =
      ∫⁻ p : Euc d × Euc d, ‖g p.1 p.2‖ₑ ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := rfl
  show ∫⁻ p : Euc d × Euc d, ‖Function.uncurry g p‖ₑ ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) < ⊤
  rw [this]
  exact h2.trans_lt ENNReal.ofReal_lt_top


theorem s95_F_main (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L C₀ c₀ b p K r Pw : ℝ)
    (hc : 0 < c₀) (hb : 0 < b) (hp : 1 < p) (hr : 1 ≤ r) (hPw : 0 ≤ Pw) :
    ∃ Cr κ : ℝ, 0 ≤ Cr ∧ 0 < κ ∧ ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ →
      (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) → ∀ N : ℕ, 2 ≤ N → ∀ P : Measure (EucConfig d N),
      HasR2ActualDensity s b p K (HRS.Whole.withDensityReal ρ) P → ∀ B : ℝ, 0 < B → ∀ g : Euc d → Euc d → ℝ,
      IsR2PolyPairKernel s Pw B g → ∀ σ' : ℕ → ℝ, (∀ k, 0 < σ' k) →
      (∀ k : ℕ, ∫⁻ x, ∫⁻ y, ‖(B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw)⁻¹ * s95_piece g k x y‖ₑ ^ 2
          ∂(HRS.Whole.withDensityReal ρ) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal (σ' k)) →
      Summable (fun k : ℕ => B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cr * σ' k ^ κ)) →
      eLpNorm (fun X : EucConfig d N => (N : ℝ) * pairEnergy g X (HRS.Whole.withDensityReal ρ)) (ENNReal.ofReal r) P ≤
        ENNReal.ofReal (∑' k : ℕ, B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cr * σ' k ^ κ)) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cr, κ, hCr, hκ, hsmall⟩ := s95_F_small hd hs0 hs M L b p K r hb hp hr
  refine ⟨Cr, κ, hCr, hκ, fun ρ hρ hG N hN P hP B hB g hg σ' hσ' hL2 hsum => ?_⟩
  haveI hμ := s92_isProb_mu hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr
  have hBk : ∀ k : ℕ, 0 < B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw := fun k => by positivity
  have ha0 : ∀ k : ℕ, 0 ≤ B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cr * σ' k ^ κ) := fun k =>
    mul_nonneg (hBk k).le (mul_nonneg hCr (Real.rpow_nonneg (hσ' k).le κ))
  have hpieceB : ∀ k : ℕ, IsBoundedPairKernel s (B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw) (s95_piece g k) := fun k =>
    s95_cut_bounded hPw hg _ (Nat.cast_nonneg k) hB.le
  have hpartB : ∀ K : ℕ, IsBoundedPairKernel s (B * 2 ^ Pw * (1 + (K : ℝ)) ^ Pw) (s95_part g K) := fun K =>
    s95_cut_bounded hPw hg _ (Nat.cast_nonneg K) hB.le
  have hFm : ∀ k : Euc d → Euc d → ℝ, Measurable (Function.uncurry k) →
      Measurable (fun X : EucConfig d N => (N : ℝ) * pairEnergy k X μ) := fun k hk =>
    measurable_const.mul (wr9_measurable_pairEnergy hk)
  have hpiece : ∀ k : ℕ, eLpNorm (fun X : EucConfig d N => (N : ℝ) * pairEnergy (s95_piece g k) X μ)
      (ENNReal.ofReal r) P ≤ ENNReal.ofReal (B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cr * σ' k ^ κ)) := by
    intro k
    have hsm := hsmall ρ hρ N hN P hP _ (s95_bdd_scale (hBk k) (hpieceB k)) (σ' k) (hσ' k) (hL2 k)
    have hfun : (fun X : EucConfig d N => (N : ℝ) * pairEnergy (s95_piece g k) X μ) =
        (B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw) • (fun X : EucConfig d N => (N : ℝ) *
          pairEnergy (fun x y => (B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw)⁻¹ * s95_piece g k x y) X μ) := by
      funext X
      have := (hBk k).ne'
      simp only [Pi.smul_apply, smul_eq_mul, s95_pe_smul]
      field_simp
    rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal (hBk k).le]
    calc ENNReal.ofReal (B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw) * _ ≤ ENNReal.ofReal (B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw) *
          ENNReal.ofReal (Cr * σ' k ^ κ) := by gcongr
      _ = _ := (ENNReal.ofReal_mul (hBk k).le).symm
  have hadd : ∀ (K : ℕ) (X : EucConfig d N), pairEnergy (s95_part g (K + 1)) X μ =
      pairEnergy (s95_part g K) X μ + pairEnergy (s95_piece g (K + 1)) X μ := by
    intro K X
    have hk1 := s92_kernel_integrable hd1 hs0 hsd M hρ.prob hρ.bdd (hpartB K)
    have hk2 := s92_kernel_integrable hd1 hs0 hsd M hρ.prob hρ.bdd (hpieceB (K + 1))
    have e : s95_part g (K + 1) = fun x y => s95_part g K x y + s95_piece g (K + 1) x y :=
      funext fun x => funext fun y => s95_part_succ g K x y
    rw [e]
    exact s95_pe_add hk1.1 hk2.1 hk1.2.2 hk2.2.2 X
  have hpart : ∀ K : ℕ, eLpNorm (fun X : EucConfig d N => (N : ℝ) * pairEnergy (s95_part g K) X μ)
      (ENNReal.ofReal r) P ≤ ∑ k ∈ Finset.range (K + 1),
        ENNReal.ofReal (B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cr * σ' k ^ κ)) := by
    intro K
    induction K with
    | zero => rw [s95_part_zero]; simpa using hpiece 0
    | succ K ih =>
      have hfun : (fun X : EucConfig d N => (N : ℝ) * pairEnergy (s95_part g (K + 1)) X μ) =
          (fun X : EucConfig d N => (N : ℝ) * pairEnergy (s95_part g K) X μ) +
            (fun X : EucConfig d N => (N : ℝ) * pairEnergy (s95_piece g (K + 1)) X μ) := by
        funext X
        simp only [Pi.add_apply]
        rw [hadd K X]
        ring
      rw [hfun, Finset.sum_range_succ]
      exact (eLpNorm_add_le hr1).trans (add_le_add ih (hpiece (K + 1)))
  have hE : ∀ K : ℕ, eLpNorm (fun X : EucConfig d N => (N : ℝ) * pairEnergy (s95_part g K) X μ)
      (ENNReal.ofReal r) P ≤ ENNReal.ofReal (∑' k : ℕ, B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cr * σ' k ^ κ)) := by
    intro K
    refine (hpart K).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => ha0 k)]
    exact ENNReal.ofReal_le_ofReal (Summable.sum_le_tsum _ (fun k _ => ha0 k) hsum)
  obtain ⟨hsec, hint⟩ := s95_poly_integrable hd1 hs0 hs M C₀ c₀ hc hPw ρ hρ.prob hρ.bdd hG B hB.le g hg
  exact s95_lim_bound P (fun K => hFm _ (hpartB K).measurable) (hFm g hg.measurable)
    (fun X => (s95_pe_tendsto hg.measurable hsec hint X).const_mul _) hE


/-! ### Summability, the annular `L²` hypotheses, and the uncentered/centered bounds -/

theorem s95_summable_pe {P θ : ℝ} (hP : 0 ≤ P) (hθ : 0 < θ) :
    Summable (fun k : ℕ => (1 + (k : ℝ)) ^ P * Real.exp (-θ * k)) := by
  set j : ℕ := ⌈P⌉₊ with hj
  have h2 := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul j hθ)
  refine (h2.mul_left (Real.exp θ)).of_nonneg_of_le (fun k => by positivity) fun k => ?_
  have h1 : (1 + (k : ℝ)) ^ P ≤ (1 + (k : ℝ)) ^ j := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (Nat.le_ceil P)
  have e : Real.exp θ * (((k + 1 : ℕ) : ℝ) ^ j * Real.exp (-θ * ((k + 1 : ℕ) : ℝ))) =
      (1 + (k : ℝ)) ^ j * Real.exp (-θ * k) := by
    push_cast
    calc Real.exp θ * (((k : ℝ) + 1) ^ j * Real.exp (-θ * ((k : ℝ) + 1)))
        = ((k : ℝ) + 1) ^ j * (Real.exp θ * Real.exp (-θ * ((k : ℝ) + 1))) := by ring
      _ = ((k : ℝ) + 1) ^ j * Real.exp (-θ * k) := by
          rw [← Real.exp_add]; congr 2; ring
      _ = _ := by rw [add_comm]
  rw [e]
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le


theorem s95_poly_mono {s Pw B B' : ℝ} (hBB : B ≤ B') {g : Euc d → Euc d → ℝ} (hg : IsR2PolyPairKernel s Pw B g) :
    IsR2PolyPairKernel s Pw B' g where
  measurable := hg.measurable
  symm := hg.symm
  bound x y hxy := by
    have h := hg.bound x y hxy
    have hW := wr3_rieszWeight_nonneg (d := d) s (x - y)
    have h1 : 0 ≤ (jbracket x + jbracket y) ^ Pw :=
      Real.rpow_nonneg (by linarith [s95_one_le_jb x, s95_one_le_jb y]) _
    have := mul_nonneg (mul_nonneg (sub_nonneg.2 hBB) h1) (by linarith : (0 : ℝ) ≤ 1 + HRS.Whole.rieszWeight s (x - y))
    nlinarith

theorem s95_pos_to_nonneg {a : ℝ≥0∞} {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → a ≤ ENNReal.ofReal (C * (B + t))) : a ≤ ENNReal.ofReal (C * B) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < ε := NNReal.coe_pos.2 hε
  have ht : 0 < (ε : ℝ) / (C + 1) := by positivity
  refine (h _ ht).trans ?_
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (by positivity) hε'.le]
  refine ENNReal.ofReal_le_ofReal ?_
  have : C * ((ε : ℝ) / (C + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

theorem s95_piece_L2 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M C₀ c₀ : ℝ) (hc : 0 < c₀)
    {Pw : ℝ} (hPw : 0 ≤ Pw) :
    ∃ Aσ : ℝ, 0 < Aσ ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) → ∀ B : ℝ, 0 < B → ∀ g : Euc d → Euc d → ℝ,
      IsR2PolyPairKernel s Pw B g → ∀ k : ℕ,
      ∫⁻ x, ∫⁻ y, ‖(B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw)⁻¹ * s95_piece g k x y‖ₑ ^ 2
        ∂(HRS.Whole.withDensityReal ρ) ∂(HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal (Aσ * Real.exp (-(c₀ * k / 2))) := by
  obtain ⟨A0, hA0, hsig⟩ := s95_sigma hd hs0 hs M C₀ c₀ hc
  refine ⟨A0 + 1, by linarith, fun ρ hρ hM hG B hB g hg k => ?_⟩
  have hBk : 0 < B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw := by positivity
  have hpB : IsBoundedPairKernel s (B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw) (s95_piece g k) :=
    s95_cut_bounded hPw hg _ (Nat.cast_nonneg k) hB.le
  have hsc := s95_bdd_scale hBk hpB
  refine (hsig ρ hρ hM hG _ k ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · intro x y hxy
    by_cases h : (k : ℝ) - 1 < max ‖x‖ ‖y‖
    · rw [if_pos h]
      have := hsc.bound x y hxy
      rwa [one_mul] at this
    · rw [if_neg h]
      have : s95_piece g k x y = 0 := by
        unfold s95_piece s95_cut
        rw [if_neg (fun h' => h h'.1)]
      simp [this]
  · exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem s95_summable_main {Aσ κ c₀ Cr Pw B : ℝ} (hA : 0 < Aσ) (hκ : 0 < κ) (hc : 0 < c₀) (hPw : 0 ≤ Pw) :
    Summable (fun k : ℕ => B * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cr * (Aσ * Real.exp (-(c₀ * k / 2))) ^ κ)) := by
  refine ((s95_summable_pe hPw (θ := κ * c₀ / 2) (by positivity)).mul_left (B * 2 ^ Pw * Cr * Aσ ^ κ)).congr
    fun k => ?_
  rw [Real.mul_rpow hA.le (Real.exp_pos _).le, ← Real.exp_mul]
  have : -(c₀ * (k : ℝ) / 2) * κ = -(κ * c₀ / 2) * k := by ring
  rw [this]
  ring

theorem s95_conj1 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L C₀ c₀ b p K r Pw : ℝ)
    (hc : 0 < c₀) (hb : 0 < b) (hp : 1 < p) (hr : 1 ≤ r) (hPw : 0 ≤ Pw) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ →
      (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) → ∀ N : ℕ, 2 ≤ N → ∀ P : Measure (EucConfig d N),
      HasR2ActualDensity s b p K (HRS.Whole.withDensityReal ρ) P → ∀ B : ℝ, 0 ≤ B → ∀ g : Euc d → Euc d → ℝ,
      IsR2PolyPairKernel s Pw B g →
      eLpNorm (fun X : EucConfig d N => (N : ℝ) * pairEnergy g X (HRS.Whole.withDensityReal ρ))
        (ENNReal.ofReal r) P ≤ ENNReal.ofReal (C * B) ∧
      eLpNorm (fun X : EucConfig d N => (N : ℝ) * (pairEnergy g X (HRS.Whole.withDensityReal ρ) -
        ∫ Y, pairEnergy g Y (HRS.Whole.withDensityReal ρ) ∂P)) (ENNReal.ofReal r) P ≤ ENNReal.ofReal (C * B) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cr, κ, hCr, hκ, hmain⟩ := s95_F_main hd hs0 hs M L C₀ c₀ b p K r Pw hc hb hp hr hPw
  obtain ⟨Aσ, hAσ, hL2⟩ := s95_piece_L2 hd1 hs0 hs M C₀ c₀ hc hPw
  set S : ℝ := ∑' k : ℕ, 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cr * (Aσ * Real.exp (-(c₀ * k / 2))) ^ κ) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k => by positivity
  refine ⟨2 * S, by positivity, fun ρ hρ hG N hN P hP B hB g hg => ?_⟩
  haveI hμ := s92_isProb_mu hρ.prob
  haveI : IsProbabilityMeasure P := hP.1
  have key : ∀ B' : ℝ, 0 < B' → IsR2PolyPairKernel s Pw B' g →
      eLpNorm (fun X : EucConfig d N => (N : ℝ) * pairEnergy g X (HRS.Whole.withDensityReal ρ))
        (ENNReal.ofReal r) P ≤ ENNReal.ofReal (S * B') := by
    intro B' hB' hg'
    have h := hmain ρ hρ hG N hN P hP B' hB' g hg' (fun k => Aσ * Real.exp (-(c₀ * k / 2)))
      (fun k => by positivity) (fun k => hL2 ρ hρ.prob hρ.bdd hG B' hB' g hg' k)
      (s95_summable_main hAσ hκ hc hPw)
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [hS, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    ring
  have hunc : eLpNorm (fun X : EucConfig d N => (N : ℝ) * pairEnergy g X (HRS.Whole.withDensityReal ρ))
      (ENNReal.ofReal r) P ≤ ENNReal.ofReal (S * B) :=
    s95_pos_to_nonneg hS0 hB fun t ht => key (B + t) (by linarith) (s95_poly_mono (by linarith) hg)
  have hXm : Measurable (fun X : EucConfig d N => (N : ℝ) * pairEnergy g X (HRS.Whole.withDensityReal ρ)) :=
    measurable_const.mul (wr9_measurable_pairEnergy hg.measurable)
  refine ⟨hunc.trans (ENNReal.ofReal_le_ofReal (by nlinarith)), ?_⟩
  have hcen := s92_centered_le P hXm hr (by positivity) hunc
  have e : (fun X : EucConfig d N => (N : ℝ) * (pairEnergy g X (HRS.Whole.withDensityReal ρ) -
        ∫ Y, pairEnergy g Y (HRS.Whole.withDensityReal ρ) ∂P)) =
      fun X => (N : ℝ) * pairEnergy g X (HRS.Whole.withDensityReal ρ) -
        ∫ Y, (N : ℝ) * pairEnergy g Y (HRS.Whole.withDensityReal ρ) ∂P := by
    funext X
    rw [integral_const_mul, mul_sub]
  rw [e]
  refine hcen.trans (le_of_eq ?_)
  congr 1
  ring


/-! ### The tail -/

theorem s95_diff_poly {s Pw B : ℝ} {h h' : Euc d → Euc d → ℝ} (hh : IsR2PolyPairKernel s Pw B h)
    (hh' : IsR2PolyPairKernel s Pw B h') : IsR2PolyPairKernel s Pw (2 * B) (fun x y => h' x y - h x y) where
  measurable := hh'.measurable.sub hh.measurable
  symm x y := by rw [hh.symm x y, hh'.symm x y]
  bound x y hxy := by
    calc |h' x y - h x y| ≤ |h' x y| + |h x y| := abs_sub _ _
      _ ≤ B * (jbracket x + jbracket y) ^ Pw * (1 + HRS.Whole.rieszWeight s (x - y)) +
          B * (jbracket x + jbracket y) ^ Pw * (1 + HRS.Whole.rieszWeight s (x - y)) :=
          add_le_add (hh'.bound x y hxy) (hh.bound x y hxy)
      _ = _ := by ring

theorem s95_enorm_cut_le (c lo hi : ℝ) (g : Euc d → Euc d → ℝ) (x y : Euc d) :
    ‖c * s95_cut lo hi g x y‖ₑ ≤ ‖c * g x y‖ₑ := by
  unfold s95_cut
  split_ifs
  · exact le_rfl
  · simp

theorem s95_conj2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L C₀ c₀ b p K r Pw : ℝ)
    (hc : 0 < c₀) (hb : 0 < b) (hp : 1 < p) (hr : 1 ≤ r) (hPw : 0 ≤ Pw)
    (ρ : Euc d → ℝ) (hρ : IsRound2Density d s M L ρ) (hG : ∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2))
    (P : ∀ N, Measure (EucConfig d N))
    (hP : ∀ N, 2 ≤ N → HasR2ActualDensity s b p K (HRS.Whole.withDensityReal ρ) (P N))
    (B : ℝ) (hB : 0 ≤ B) (h : Euc d → Euc d → ℝ) (hj : ℕ → Euc d → Euc d → ℝ)
    (hh : IsR2PolyPairKernel s Pw B h) (hhj : ∀ j, IsR2PolyPairKernel s Pw B (hj j))
    (hconv : Tendsto (fun j => eLpNorm (fun q : Euc d × Euc d => hj j q.1 q.2 - h q.1 q.2) (ENNReal.ofReal 2)
      ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ))) atTop (𝓝 0)) :
    R2ActualFTail (ι := Unit) (fun _ => HRS.Whole.withDensityReal ρ) r h hj (fun _ => P) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cr, κ, hCr, hκ, hmain⟩ := s95_F_main hd hs0 hs M L C₀ c₀ b p K r Pw hc hb hp hr hPw
  obtain ⟨Aσ, hAσ, hL2⟩ := s95_piece_L2 hd1 hs0 hs M C₀ c₀ hc hPw
  haveI hμ := s92_isProb_mu hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  have hB2 : 0 < 2 * (B + 1) := by linarith
  have hgj : ∀ j, IsR2PolyPairKernel s Pw (2 * (B + 1)) (fun x y => hj j x y - h x y) := fun j =>
    s95_diff_poly (s95_poly_mono (by linarith) hh) (s95_poly_mono (by linarith) (hhj j))
  have hBk : ∀ k : ℕ, 0 < 2 * (B + 1) * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw := fun k => by positivity
  have hmeasj : ∀ j, Measurable (Function.uncurry fun x y => hj j x y - h x y) := fun j => (hgj j).measurable
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ≥0∞, D = fun j => eLpNorm (fun q : Euc d × Euc d => hj j q.1 q.2 - h q.1 q.2)
      (ENNReal.ofReal 2) (μ.prod μ) := ⟨_, rfl⟩
  have hDt : Tendsto D atTop (𝓝 0) := by rw [hD]; exact hconv
  have hS2 : ∀ j, ∫⁻ x, ∫⁻ y, ‖hj j x y - h x y‖ₑ ^ 2 ∂μ ∂μ = D j ^ 2 := fun j => by
    rw [hD]; exact s92_S2_eq (hmeasj j)
  obtain ⟨τ, hτ⟩ : ∃ τ : ℕ → ℕ → ℝ≥0∞, τ = fun (j k : ℕ) => min (ENNReal.ofReal (Aσ * Real.exp (-(c₀ * k / 2))))
      (ENNReal.ofReal ((2 * (B + 1) * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw)⁻¹ ^ 2) * D j ^ 2 +
        ENNReal.ofReal (1 / ((j : ℝ) + 1))) := ⟨_, rfl⟩
  have hτ1 : ∀ j k, τ j k ≤ ENNReal.ofReal (Aσ * Real.exp (-(c₀ * k / 2))) := fun j k => by
    rw [hτ]; exact min_le_left _ _
  have hτpos : ∀ j k, 0 < τ j k := fun j k => by
    rw [hτ]
    exact lt_min (ENNReal.ofReal_pos.2 (by positivity))
      (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) le_add_self)
  have hτne : ∀ j k, τ j k ≠ ⊤ := fun j k => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hτ1 j k)
  have hσpos : ∀ j k, 0 < (τ j k).toReal := fun j k => ENNReal.toReal_pos (hτpos j k).ne' (hτne j k)
  have hofr : ∀ j k, ENNReal.ofReal ((τ j k).toReal) = τ j k := fun j k => ENNReal.ofReal_toReal (hτne j k)
  have hσle : ∀ j k, (τ j k).toReal ≤ Aσ * Real.exp (-(c₀ * k / 2)) := fun j k => by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hτ1 j k)
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hL2' : ∀ j k : ℕ, ∫⁻ x, ∫⁻ y, ‖(2 * (B + 1) * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw)⁻¹ *
      s95_piece (fun x y => hj j x y - h x y) k x y‖ₑ ^ 2 ∂μ ∂μ ≤ ENNReal.ofReal ((τ j k).toReal) := by
    intro j k
    rw [hofr, hτ]
    refine le_min (hL2 ρ hρ.prob hρ.bdd hG _ hB2 _ (hgj j) k) ?_
    calc ∫⁻ x, ∫⁻ y, ‖(2 * (B + 1) * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw)⁻¹ *
          s95_piece (fun x y => hj j x y - h x y) k x y‖ₑ ^ 2 ∂μ ∂μ
        ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((2 * (B + 1) * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw)⁻¹ ^ 2) *
            ‖hj j x y - h x y‖ₑ ^ 2 ∂μ ∂μ := by
          refine lintegral_mono fun x => lintegral_mono fun y => ?_
          rw [← s92_enorm_mul_sq]
          exact pow_le_pow_left' (s95_enorm_cut_le _ _ _ _ x y) 2
      _ = ENNReal.ofReal ((2 * (B + 1) * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw)⁻¹ ^ 2) * D j ^ 2 := by
          rw [← hS2 j, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun x => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := le_self_add
  have hsumm : ∀ j, Summable (fun k : ℕ => 2 * (B + 1) * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cr * (τ j k).toReal ^ κ)) :=
    fun j => (s95_summable_main hAσ hκ hc hPw (B := 2 * (B + 1)) (Cr := Cr)).of_nonneg_of_le
      (fun k => mul_nonneg (hBk k).le (mul_nonneg hCr (Real.rpow_nonneg (hσpos j k).le κ)))
      (fun k => mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hσpos j k).le (hσle j k) hκ.le) hCr) (hBk k).le)
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ, A = fun j => ∑' k : ℕ,
      2 * (B + 1) * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cr * (τ j k).toReal ^ κ) := ⟨_, rfl⟩
  have hbound : ∀ j (N : ℕ), 2 ≤ N → eLpNorm (fun X : EucConfig d N => (N : ℝ) *
      pairEnergy (fun x y => hj j x y - h x y) X μ) (ENNReal.ofReal r) (P N) ≤ ENNReal.ofReal (A j) := by
    intro j N hN
    rw [hA]
    exact hmain ρ hρ hG N hN (P N) (hP N hN) _ hB2 _ (hgj j) (fun k => (τ j k).toReal) (hσpos j)
      (hL2' j) (hsumm j)
  have hA0 : ∀ j, 0 ≤ A j := fun j => by
    rw [hA]; exact tsum_nonneg fun k => mul_nonneg (hBk k).le (mul_nonneg hCr (Real.rpow_nonneg (hσpos j k).le κ))
  -- `τ j k → 0`
  have hτ0 : ∀ k, Tendsto (fun j => τ j k) atTop (𝓝 0) := by
    intro k
    have hD2 : Tendsto (fun j => D j ^ 2) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_pow 2).tendsto 0).comp hDt
      simpa [Function.comp_def] using this
    have hm := ENNReal.Tendsto.const_mul hD2
      (Or.inr (ENNReal.ofReal_ne_top (r := ((2 * (B + 1) * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw)⁻¹ ^ 2))))
    have hi : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this
    have hυ := hm.add hi
    rw [mul_zero, add_zero] at hυ
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hυ (fun j => zero_le')
      (fun j => by rw [hτ]; exact min_le_right _ _)
  have hσ0 : ∀ k, Tendsto (fun j => (τ j k).toReal) atTop (𝓝 0) := fun k => by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hτ0 k)
    simpa [Function.comp_def] using this
  have hAt : Tendsto A atTop (𝓝 0) := by
    have h1 := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun j (k : ℕ) => 2 * (B + 1) * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cr * (τ j k).toReal ^ κ))
      (g := fun _ => (0 : ℝ))
      (bound := fun k : ℕ => 2 * (B + 1) * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cr * (Aσ * Real.exp (-(c₀ * k / 2))) ^ κ))
      (s95_summable_main hAσ hκ hc hPw) (fun k => by
        have h0 : Tendsto (fun j => (τ j k).toReal ^ κ) atTop (𝓝 0) := by
          have := ((Real.continuous_rpow_const hκ.le).tendsto 0).comp (hσ0 k)
          simpa [Real.zero_rpow hκ.ne', Function.comp_def] using this
        simpa using (h0.const_mul Cr).const_mul (2 * (B + 1) * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw))
      (Eventually.of_forall fun j k => by
        rw [Real.norm_of_nonneg (mul_nonneg (hBk k).le (mul_nonneg hCr (Real.rpow_nonneg (hσpos j k).le κ)))]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hσpos j k).le (hσle j k) hκ.le) hCr) (hBk k).le)
    rw [hA]
    simpa using h1
  have hAe : Tendsto (fun j => ENNReal.ofReal (A j)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hAt
  have hAe2 : Tendsto (fun j => ENNReal.ofReal (2 * A j)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (hAt.const_mul 2)
  refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAe (fun j => zero_le')
    (fun j => iSup_le fun _ => iSup_le fun N => hbound j N.1 N.2), ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAe2 (fun j => zero_le')
    (fun j => iSup_le fun _ => iSup_le fun N => ?_)
  have hN := N.2
  haveI : IsProbabilityMeasure (P N.1) := (hP N.1 hN).1
  have hXm : Measurable (fun X : EucConfig d N.1 => (N.1 : ℝ) *
      pairEnergy (fun x y => hj j x y - h x y) X μ) :=
    measurable_const.mul (wr9_measurable_pairEnergy (hgj j).measurable)
  have hc2 := s92_centered_le (P N.1) hXm hr (hA0 j) (hbound j N.1 hN)
  have e : (fun X : EucConfig d N.1 => (N.1 : ℝ) *
      (pairEnergy (fun x y => hj j x y - h x y) X μ -
        ∫ Y, pairEnergy (fun x y => hj j x y - h x y) Y μ ∂(P N.1))) =
      fun X => (N.1 : ℝ) * pairEnergy (fun x y => hj j x y - h x y) X μ -
        ∫ Y, (N.1 : ℝ) * pairEnergy (fun x y => hj j x y - h x y) Y μ ∂(P N.1) := by
    funext X
    rw [integral_const_mul, mul_sub]
  show eLpNorm (fun X : EucConfig d N.1 => (N.1 : ℝ) *
      (pairEnergy (fun x y => hj j x y - h x y) X μ -
        ∫ Y, pairEnergy (fun x y => hj j x y - h x y) Y μ ∂(P N.1))) (ENNReal.ofReal r) (P N.1) ≤ _
  rw [e]
  exact hc2


/-! ### The linear statistic: small `L²(μ)` mass gives a small `L^r(P_N)` norm -/

theorem s95_lin_L2 {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : Euc d → ℝ} (ha : Measurable a)
    (hint : Integrable a μ) (hN : 0 < N) {σ : ℝ} (hσ : ∫⁻ x, ‖a x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal σ) :
    ∫⁻ X : EucConfig d N, ‖Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a)‖ₑ ^ 2
      ∂(Measure.pi fun _ : Fin N => μ) ≤ ENNReal.ofReal (4 * σ) := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ∫ x, a x ∂μ := ⟨_, rfl⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsq2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
  have hφ : Measurable (fun x => a x - m) := ha.sub_const _
  have h0 : ∫ x, (a x - m) ∂μ = 0 := by
    rw [integral_sub hint (integrable_const _), integral_const, ← hm]; simp
  have hlin2 : ∫⁻ X : EucConfig d N, ‖∑ j, (a (X j) - m)‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin N => μ) ≤
      (N : ℝ≥0∞) * ∫⁻ y, ‖a y - m‖ₑ ^ 2 ∂μ := by
    have := s92_lin2 μ hφ h0 (Finset.univ : Finset (Fin N))
    simpa [Finset.card_univ] using this
  have hφ2 : ∫⁻ x, ‖a x - m‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (4 * σ) := by
    calc ∫⁻ x, ‖a x - m‖ₑ ^ 2 ∂μ ≤ ∫⁻ x, (2 * ‖a x‖ₑ ^ 2 + 2 * ‖m‖ₑ ^ 2) ∂μ :=
          lintegral_mono fun x => s92_enorm_sq_sub_le _ _
      _ = 2 * ∫⁻ x, ‖a x‖ₑ ^ 2 ∂μ + 2 * ‖m‖ₑ ^ 2 := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by simp), lintegral_const,
            measure_univ, mul_one]
      _ ≤ 2 * ENNReal.ofReal σ + 2 * ENNReal.ofReal σ := by
          gcongr
          rw [hm]
          exact (s92_enorm_integral_sq_le μ a ha).trans hσ
      _ = ENNReal.ofReal (4 * σ) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num
          ring
  have hrel : ∀ X : EucConfig d N, Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a) =
      (Real.sqrt N)⁻¹ * ∑ j, (a (X j) - m) := by
    intro X
    rw [s32_linear_stat X ha hN, hm]
    field_simp
    rw [hsq2]
  simp_rw [hrel, s92_enorm_mul_sq]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hc : ENNReal.ofReal (((Real.sqrt N)⁻¹) ^ 2) = (N : ℝ≥0∞)⁻¹ := by
    rw [inv_pow, hsq2, ENNReal.ofReal_inv_of_pos hN0, ENNReal.ofReal_natCast]
  rw [hc]
  calc (N : ℝ≥0∞)⁻¹ * ∫⁻ X : EucConfig d N, ‖∑ j, (a (X j) - m)‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin N => μ)
      ≤ (N : ℝ≥0∞)⁻¹ * ((N : ℝ≥0∞) * ∫⁻ y, ‖a y - m‖ₑ ^ 2 ∂μ) := by gcongr
    _ = ∫⁻ y, ‖a y - m‖ₑ ^ 2 ∂μ := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N), one_mul]
    _ ≤ _ := hφ2


theorem s95_lin_small (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L b p K r : ℝ)
    (hb : 0 < b) (hp : 1 < p) (hr : 1 ≤ r) :
    ∃ Cl κ : ℝ, 0 ≤ Cl ∧ 0 < κ ∧ ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ → ∀ N : ℕ, 2 ≤ N →
      ∀ P : Measure (EucConfig d N), HasR2ActualDensity s b p K (HRS.Whole.withDensityReal ρ) P →
      ∀ a : Euc d → ℝ, Measurable a → (∀ x, |a x| ≤ 1) → ∀ σ : ℝ, 0 < σ →
      ∫⁻ x, ‖a x‖ₑ ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal σ →
      eLpNorm (fun X : EucConfig d N => Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) a))
        (ENNReal.ofReal r) P ≤ ENNReal.ofReal (Cl * σ ^ κ) := by
  have hcp : 1 < Real.conjExponent p := (Real.HolderConjugate.conjExponent hp).symm.lt
  set t : ℝ := r * Real.conjExponent p with ht
  have ht0 : 0 < t := mul_pos (by linarith) (by linarith)
  set m : ℕ := ⌈2 * t⌉₊ with hm
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_lt_of_le (by linarith) (Nat.le_ceil (2 * t))
    exact_mod_cast this
  obtain ⟨C0, hC0, hnorm⟩ := s92_normalizer_bounds hd hs0 hs M L b (2 * b) hb (by linarith)
  set K' : ℝ := max K 0 with hK'
  set C2 : ℝ := ((2 * m).factorial : ℝ) / (1 / (1 : ℝ)) ^ (2 * m) * (2 * Real.exp (1 / 2)) with hC2
  have hC2nn : 0 ≤ C2 := by positivity
  set Cg : ℝ := (1 + C2 + Real.sqrt C2 * Real.sqrt 1) * (4 : ℝ) ^ (1 / 8 : ℝ) with hCg
  have hCg0 : 0 ≤ Cg := by positivity
  refine ⟨K' ^ (1 / r) * (Real.exp (3 * C0 / 2) ^ (1 / t) * Cg ^ (1 / (m : ℝ))), 1 / (8 * (m : ℝ)),
    by positivity, by positivity, fun ρ hρ N hN P hP a ha hA σ hσ hS => ?_⟩
  haveI hμ := s92_isProb_mu hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  haveI hPprob : IsProbabilityMeasure P := hP.1
  have hN0 : 0 < N := by omega
  have hXm : Measurable (fun X : EucConfig d N => Real.sqrt N *
      (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a)) := by
    have : ∀ X : EucConfig d N, HRS.Whole.pair (HRS.Whole.empirical X) a = (N : ℝ)⁻¹ * ∑ i, a (X i) :=
      fun X => s32_pair_empirical X ha
    simp_rw [this]
    exact measurable_const.mul ((measurable_const.mul
      (Finset.measurable_sum _ fun i _ => ha.comp (measurable_pi_apply i))).sub measurable_const)
  have hint : Integrable a μ := Integrable.of_bound ha.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa using hA x)
  have hW := (hnorm ρ hρ N hN b ⟨le_rfl, by linarith⟩).1
  have hW2 := (hnorm ρ hρ N hN (2 * b) ⟨by linarith, le_rfl⟩).1
  have hl1 := (hnorm ρ hρ N hN b ⟨le_rfl, by linarith⟩).2
  have hl2 := (hnorm ρ hρ N hN (2 * b) ⟨by linarith, le_rfl⟩).2
  haveI hQ := s92_isProb_Q (N := N) hW
  set π : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hπ
  haveI hπp : IsProbabilityMeasure π := inferInstance
  have h2 := s95_lin_L2 (N := N) ha hint hN0 hS
  have hC2' : ∫⁻ X : EucConfig d N, ‖Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) a -
      HRS.Whole.pair μ a)‖ₑ ^ (2 * m) ∂(π.withDensity 1) ≤ ENNReal.ofReal C2 := by
    rw [withDensity_one]
    exact s92_lin_pi (μ := μ) ha one_pos hA hN0 (2 * m)
  haveI : IsProbabilityMeasure (π.withDensity (1 : EucConfig d N → ℝ≥0∞)) := by
    rw [withDensity_one]; exact hπp
  have hAψ : (∫⁻ X : EucConfig d N, (1 : EucConfig d N → ℝ≥0∞) X ^ (2 : ℝ) ∂π) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal 1 := by simp
  have hI := s95_interp π (ψ := 1) measurable_one hXm hm1 hC2nn zero_le_one (by positivity : 0 < 4 * σ)
    hC2' hAψ (by simpa using h2)
  rw [withDensity_one] at hI
  have hE : (1 + C2 + Real.sqrt C2 * Real.sqrt 1) * (4 * σ) ^ (1 / 8 : ℝ) = Cg * σ ^ (1 / 8 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hσ.le, hCg]; ring
  rw [hE] at hI
  have hE0 : 0 ≤ Cg * σ ^ (1 / 8 : ℝ) := by positivity
  have hpi := s92_eLpNorm_le_of_moment π hXm (by linarith : 0 < 2 * t) m (Nat.le_ceil (2 * t)) hE0 hI
  have hQeq : HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ =
      pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ := rfl
  have hQb : eLpNorm (fun X : EucConfig d N => Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a))
      (ENNReal.ofReal t) (HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ) ≤
      ENNReal.ofReal (Real.exp (3 * C0 / 2) ^ (1 / t) * (Cg * σ ^ (1 / 8 : ℝ)) ^ (1 / (m : ℝ))) := by
    rw [hQeq]
    exact s92_Q_to_pi (wr9_rieszKernel_pair_meas s) hW hW2 hl1 hl2 hXm ht0 hpi
  have hdens : eLpNorm (fun X => ((P.rnDeriv (HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ) X).toReal))
      (ENNReal.ofReal p) (HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ) ≤ ENNReal.ofReal K' :=
    hP.2.2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hPb := s92_transfer _ P hP.2.1 hp (le_max_right _ _) hdens hXm (by linarith : 0 < r) hQb
  refine hPb.trans (le_of_eq ?_)
  congr 1
  rw [Real.mul_rpow hCg0 (by positivity), ← Real.rpow_mul hσ.le]
  have : (1 / 8 : ℝ) * (1 / (m : ℝ)) = 1 / (8 * (m : ℝ)) := by field_simp
  rw [this]
  ring


/-! ### Annular cuts of test functions and linearity of the linear statistic -/

/-- `1_{lo < |x| ≤ hi} a`. -/
def s95_lcut (lo hi : ℝ) (a : Euc d → ℝ) (x : Euc d) : ℝ := if lo < ‖x‖ ∧ ‖x‖ ≤ hi then a x else 0

/-- `1_{|x| ≤ K} a` and `1_{k - 1 < |x| ≤ k} a`. -/
def s95_lpart (a : Euc d → ℝ) (K : ℕ) : Euc d → ℝ := s95_lcut (-1) K a

def s95_lpiece (a : Euc d → ℝ) (k : ℕ) : Euc d → ℝ := s95_lcut ((k : ℝ) - 1) k a

/-- The linear statistic `√N (μ_N(a) - μ(a))`. -/
def s95_lin (μ : Measure (Euc d)) (a : Euc d → ℝ) (X : EucConfig d N) : ℝ :=
  Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a)

theorem s95_lcut_meas {a : Euc d → ℝ} (ha : Measurable a) (lo hi : ℝ) : Measurable (s95_lcut lo hi a) := by
  unfold s95_lcut
  exact Measurable.ite ((measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)) ha measurable_const

theorem s95_lcut_abs_le (lo hi : ℝ) (a : Euc d → ℝ) (x : Euc d) : ‖s95_lcut lo hi a x‖ ≤ ‖a x‖ := by
  unfold s95_lcut
  split_ifs
  · exact le_rfl
  · simp

theorem s95_lcut_bound {a : Euc d → ℝ} {B Pw : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ Pw) (ha : ∀ x, |a x| ≤ B * jbracket x ^ Pw)
    (lo : ℝ) {hi : ℝ} (hhi : 0 ≤ hi) (x : Euc d) : |s95_lcut lo hi a x| ≤ B * (1 + hi) ^ Pw := by
  unfold s95_lcut
  split_ifs with h
  · calc |a x| ≤ B * jbracket x ^ Pw := ha x
      _ ≤ B * (1 + hi) ^ Pw := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (zero_le_one.trans (s95_one_le_jb x))
            (show jbracket x ≤ 1 + hi by linarith [s95_jb_le x, h.2]) hP) hB
  · simp only [abs_zero]; positivity

theorem s95_lpart_succ (a : Euc d → ℝ) (K : ℕ) (x : Euc d) :
    s95_lpart a (K + 1) x = s95_lpart a K x + s95_lpiece a (K + 1) x := by
  have hm := norm_nonneg x
  have e : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
  unfold s95_lpart s95_lpiece s95_lcut
  rw [e]
  have h0 : (-1 : ℝ) < ‖x‖ := by linarith
  by_cases h1 : ‖x‖ ≤ (K : ℝ)
  · rw [if_pos ⟨h0, by linarith⟩, if_pos ⟨h0, h1⟩, if_neg (fun h => by linarith [h.1])]
    ring
  · by_cases h2 : ‖x‖ ≤ (K : ℝ) + 1
    · rw [if_pos ⟨h0, h2⟩, if_neg (fun h => h1 h.2), if_pos ⟨by linarith [not_le.1 h1], h2⟩]
      ring
    · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h1 (by linarith [h.2])), if_neg (fun h => h2 h.2)]
      ring

theorem s95_lpart_zero (a : Euc d → ℝ) : s95_lpart a 0 = s95_lpiece a 0 := by
  unfold s95_lpart s95_lpiece
  simp

theorem s95_lpart_tendsto (a : Euc d → ℝ) (x : Euc d) :
    Tendsto (fun K : ℕ => s95_lpart a K x) atTop (𝓝 (a x)) := by
  obtain ⟨K0, hK0⟩ := exists_nat_ge ‖x‖
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop K0] with K hK
  unfold s95_lpart s95_lcut
  rw [if_pos ⟨by linarith [norm_nonneg x], hK0.trans (by exact_mod_cast hK)⟩]

theorem s95_lin_add {μ : Measure (Euc d)} {a1 a2 : Euc d → ℝ} (h1 : Measurable a1) (h2 : Measurable a2)
    (i1 : Integrable a1 μ) (i2 : Integrable a2 μ) (X : EucConfig d N) :
    s95_lin μ (fun x => a1 x + a2 x) X = s95_lin μ a1 X + s95_lin μ a2 X := by
  unfold s95_lin
  have hm : Measurable (fun x => a1 x + a2 x) := h1.add h2
  rw [s32_pair_empirical X hm, s32_pair_empirical X h1, s32_pair_empirical X h2]
  unfold HRS.Whole.pair
  rw [integral_add i1 i2, Finset.sum_add_distrib]
  ring

theorem s95_lin_smul {μ : Measure (Euc d)} {a : Euc d → ℝ} (ha : Measurable a) (c : ℝ) (X : EucConfig d N) :
    s95_lin μ (fun x => c * a x) X = c * s95_lin μ a X := by
  unfold s95_lin
  have hm : Measurable (fun x => c * a x) := measurable_const.mul ha
  rw [s32_pair_empirical X hm, s32_pair_empirical X ha]
  unfold HRS.Whole.pair
  rw [integral_const_mul, ← Finset.mul_sum]
  ring

theorem s95_lin_meas {μ : Measure (Euc d)} {a : Euc d → ℝ} (ha : Measurable a) :
    Measurable (fun X : EucConfig d N => s95_lin μ a X) := by
  unfold s95_lin
  have : ∀ X : EucConfig d N, HRS.Whole.pair (HRS.Whole.empirical X) a = (N : ℝ)⁻¹ * ∑ i, a (X i) :=
    fun X => s32_pair_empirical X ha
  simp_rw [this]
  exact measurable_const.mul ((measurable_const.mul
    (Finset.measurable_sum _ fun i _ => ha.comp (measurable_pi_apply i))).sub measurable_const)

theorem s95_lin_tendsto {μ : Measure (Euc d)} {a : Euc d → ℝ} (ha : Measurable a) (hint : Integrable a μ)
    (X : EucConfig d N) :
    Tendsto (fun K : ℕ => s95_lin μ (s95_lpart a K) X) atTop (𝓝 (s95_lin μ a X)) := by
  have hmeas : ∀ K, Measurable (s95_lpart a K) := fun K => s95_lcut_meas ha _ _
  have T1 : Tendsto (fun K : ℕ => ∑ i, s95_lpart a K (X i)) atTop (𝓝 (∑ i, a (X i))) :=
    tendsto_finsetSum _ fun i _ => s95_lpart_tendsto a _
  have T2 : Tendsto (fun K : ℕ => ∫ x, s95_lpart a K x ∂μ) atTop (𝓝 (∫ x, a x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖a x‖)
      (fun K => (hmeas K).aestronglyMeasurable) hint.norm
      (fun K => Eventually.of_forall fun x => s95_lcut_abs_le _ _ a x)
      (Eventually.of_forall fun x => s95_lpart_tendsto a x)
  have e : ∀ K : ℕ, s95_lin μ (s95_lpart a K) X = Real.sqrt N *
      ((N : ℝ)⁻¹ * ∑ i, s95_lpart a K (X i) - ∫ x, s95_lpart a K x ∂μ) := fun K => by
    unfold s95_lin
    rw [s32_pair_empirical X (hmeas K)]
    rfl
  have e0 : s95_lin μ a X = Real.sqrt N * ((N : ℝ)⁻¹ * ∑ i, a (X i) - ∫ x, a x ∂μ) := by
    unfold s95_lin
    rw [s32_pair_empirical X ha]
    rfl
  simp_rw [e]
  rw [e0]
  exact ((T1.const_mul _).sub T2).const_mul _


theorem s95_test_integrable (d : ℕ) (C₀ c₀ : ℝ) (hc : 0 < c₀) {Pw : ℝ} (hPw : 0 ≤ Pw) :
    ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) →
      ∀ B : ℝ, 0 ≤ B → ∀ a : Euc d → ℝ, Measurable a → (∀ x, |a x| ≤ B * jbracket x ^ Pw) →
      Integrable a (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨CM, hCM, hmom⟩ := s95_moment d C₀ c₀ hc hPw
  intro ρ hρ hG B hB a ha hab
  refine ⟨ha.aestronglyMeasurable, ?_⟩
  have h1 : ∫⁻ x, ‖a x‖ₑ ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (jbracket x ^ Pw) ∂(HRS.Whole.withDensityReal ρ) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hB]
    exact ENNReal.ofReal_le_ofReal (hab x)
  have h2 : ∫⁻ x, ENNReal.ofReal (jbracket x ^ Pw) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal CM :=
    le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (by
      have h1 : 1 ≤ jbracket x ^ Pw := Real.one_le_rpow (s95_one_le_jb x) hPw
      nlinarith)) (hmom ρ hρ hG)
  exact (h1.trans (mul_le_mul' le_rfl h2)).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

theorem s95_conj3 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L C₀ c₀ b p K r Pw : ℝ)
    (hc : 0 < c₀) (hb : 0 < b) (hp : 1 < p) (hr : 1 ≤ r) (hPw : 0 ≤ Pw) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ →
      (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) → ∀ N : ℕ, 2 ≤ N → ∀ P : Measure (EucConfig d N),
      HasR2ActualDensity s b p K (HRS.Whole.withDensityReal ρ) P → ∀ B : ℝ, 0 ≤ B → ∀ a : Euc d → ℝ, Measurable a →
      (∀ x, |a x| ≤ B * jbracket x ^ Pw) →
      eLpNorm (fun X : EucConfig d N => Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) a))
        (ENNReal.ofReal r) P ≤ ENNReal.ofReal (C * B) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cl, κ, hCl, hκ, hsmall⟩ := s95_lin_small hd hs0 hs M L b p K r hb hp hr
  obtain ⟨Gk, hGk, htail⟩ := s95_tail_k d C₀ c₀ hc
  have hGk0 : 0 < Gk := by linarith
  set S : ℝ := ∑' k : ℕ, 1 * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cl * (Gk * Real.exp (-(c₀ * k / 2))) ^ κ) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k => by positivity
  refine ⟨S, hS0, fun ρ hρ hG N hN P hP B hB a ha hab => ?_⟩
  haveI hμ := s92_isProb_mu hρ.prob
  haveI : IsProbabilityMeasure P := hP.1
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr
  have hinteg : ∀ (B' : ℝ), 0 ≤ B' → ∀ a' : Euc d → ℝ, Measurable a' → (∀ x, |a' x| ≤ B' * jbracket x ^ Pw) →
      Integrable a' μ := fun B' hB' a' ha' hab' => s95_test_integrable d C₀ c₀ hc hPw ρ hρ.prob hG B' hB' a' ha' hab'
  have key : ∀ B' : ℝ, 0 < B' → ∀ a' : Euc d → ℝ, Measurable a' → (∀ x, |a' x| ≤ B' * jbracket x ^ Pw) →
      eLpNorm (fun X : EucConfig d N => s95_lin μ a' X) (ENNReal.ofReal r) P ≤ ENNReal.ofReal (S * B') := by
    intro B' hB' a' ha' hab'
    have hAk : ∀ k : ℕ, 0 < B' * (1 + (k : ℝ)) ^ Pw := fun k => by positivity
    have hlb : ∀ (lo : ℝ) (k : ℕ) (x : Euc d), |s95_lcut lo k a' x| ≤ B' * (1 + (k : ℝ)) ^ Pw := fun lo k x =>
      s95_lcut_bound hB'.le hPw hab' lo (Nat.cast_nonneg k) x
    have hlint : ∀ (lo : ℝ) (k : ℕ), Integrable (s95_lcut lo k a') μ := fun lo k =>
      Integrable.of_bound (s95_lcut_meas ha' lo k).aestronglyMeasurable (B' * (1 + (k : ℝ)) ^ Pw)
        (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hlb lo k x)
    have hpiece : ∀ k : ℕ, eLpNorm (fun X : EucConfig d N => s95_lin μ (s95_lpiece a' k) X) (ENNReal.ofReal r) P ≤
        ENNReal.ofReal (B' * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cl * (Gk * Real.exp (-(c₀ * k / 2))) ^ κ)) := by
      intro k
      set Ak : ℝ := B' * (1 + (k : ℝ)) ^ Pw with hAkdef
      have hAk0 := hAk k
      have hat_meas : Measurable (fun x => Ak⁻¹ * s95_lpiece a' k x) :=
        measurable_const.mul (s95_lcut_meas ha' _ _)
      have hat_b : ∀ x, |Ak⁻¹ * s95_lpiece a' k x| ≤ 1 := fun x => by
        rw [abs_mul, abs_of_pos (inv_pos.2 hAk0)]
        calc Ak⁻¹ * |s95_lpiece a' k x| ≤ Ak⁻¹ * Ak := by gcongr; exact hlb _ k x
          _ = 1 := inv_mul_cancel₀ hAk0.ne'
      have hat_L2 : ∫⁻ x, ‖Ak⁻¹ * s95_lpiece a' k x‖ₑ ^ 2 ∂μ ≤
          ENNReal.ofReal (Gk * Real.exp (-(c₀ * k / 2))) := by
        refine le_trans (lintegral_mono fun x => ?_ :
          ∫⁻ x, ‖Ak⁻¹ * s95_lpiece a' k x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x, {x : Euc d | (k : ℝ) - 1 < ‖x‖}.indicator
            (fun _ => (1 : ℝ≥0∞)) x ∂μ) ?_
        · by_cases hx : (k : ℝ) - 1 < ‖x‖
          · rw [Set.indicator_of_mem (show x ∈ {x : Euc d | (k : ℝ) - 1 < ‖x‖} from hx)]
            have : ‖Ak⁻¹ * s95_lpiece a' k x‖ₑ ≤ 1 := by
              rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal (hat_b x)
            exact pow_le_one' this 2
          · have : s95_lpiece a' k x = 0 := by
              unfold s95_lpiece s95_lcut
              rw [if_neg (fun h => hx h.1)]
            simp [this]
        · rw [lintegral_indicator_const (measurableSet_lt measurable_const measurable_norm), one_mul]
          exact htail ρ hρ.prob hG k
      have hsm := hsmall ρ hρ N hN P hP _ hat_meas hat_b (Gk * Real.exp (-(c₀ * k / 2))) (by positivity) hat_L2
      have hfun : (fun X : EucConfig d N => s95_lin μ (s95_lpiece a' k) X) =
          Ak • (fun X : EucConfig d N => s95_lin μ (fun x => Ak⁻¹ * s95_lpiece a' k x) X) := by
        funext X
        have e : s95_lpiece a' k = fun x => Ak * (Ak⁻¹ * s95_lpiece a' k x) := by
          funext x; rw [← mul_assoc, mul_inv_cancel₀ hAk0.ne', one_mul]
        calc s95_lin μ (s95_lpiece a' k) X = s95_lin μ (fun x => Ak * (Ak⁻¹ * s95_lpiece a' k x)) X := by
              rw [← e]
          _ = Ak * s95_lin μ (fun x => Ak⁻¹ * s95_lpiece a' k x) X := s95_lin_smul hat_meas Ak X
          _ = _ := rfl
      rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal hAk0.le]
      calc ENNReal.ofReal Ak * _ ≤ ENNReal.ofReal Ak * ENNReal.ofReal (Cl * (Gk * Real.exp (-(c₀ * k / 2))) ^ κ) :=
            mul_le_mul' le_rfl hsm
        _ = ENNReal.ofReal (Ak * (Cl * (Gk * Real.exp (-(c₀ * k / 2))) ^ κ)) := (ENNReal.ofReal_mul hAk0.le).symm
        _ ≤ _ := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h2 : 1 ≤ (2 : ℝ) ^ Pw := Real.one_le_rpow (by norm_num) hPw
            have h3 : 0 ≤ Cl * (Gk * Real.exp (-(c₀ * k / 2))) ^ κ := by positivity
            have : Ak ≤ B' * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw := by
              rw [hAkdef]
              have : 0 ≤ (1 + (k : ℝ)) ^ Pw := by positivity
              nlinarith [mul_nonneg (mul_nonneg hB'.le this) (sub_nonneg.2 h2)]
            exact mul_le_mul_of_nonneg_right this h3
    have hpart : ∀ K : ℕ, eLpNorm (fun X : EucConfig d N => s95_lin μ (s95_lpart a' K) X) (ENNReal.ofReal r) P ≤
        ∑ k ∈ Finset.range (K + 1),
          ENNReal.ofReal (B' * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cl * (Gk * Real.exp (-(c₀ * k / 2))) ^ κ)) := by
      intro K
      induction K with
      | zero => rw [s95_lpart_zero]; simpa using hpiece 0
      | succ K ih =>
        have hfun : (fun X : EucConfig d N => s95_lin μ (s95_lpart a' (K + 1)) X) =
            (fun X : EucConfig d N => s95_lin μ (s95_lpart a' K) X) +
              (fun X : EucConfig d N => s95_lin μ (s95_lpiece a' (K + 1)) X) := by
          funext X
          have e : s95_lpart a' (K + 1) = fun x => s95_lpart a' K x + s95_lpiece a' (K + 1) x :=
            funext fun x => s95_lpart_succ a' K x
          simp only [Pi.add_apply]
          rw [e]
          exact s95_lin_add (s95_lcut_meas ha' _ _) (s95_lcut_meas ha' _ _) (hlint _ _) (hlint _ _) X
        rw [hfun, Finset.sum_range_succ]
        exact (eLpNorm_add_le hr1).trans (add_le_add ih (hpiece (K + 1)))
    have hsum := s95_summable_main (Aσ := Gk) (κ := κ) (c₀ := c₀) (Cr := Cl) (Pw := Pw) (B := B') hGk0 hκ hc hPw
    have ha0 : ∀ k : ℕ, 0 ≤ B' * 2 ^ Pw * (1 + (k : ℝ)) ^ Pw * (Cl * (Gk * Real.exp (-(c₀ * k / 2))) ^ κ) :=
      fun k => by positivity
    have hE : ∀ K : ℕ, eLpNorm (fun X : EucConfig d N => s95_lin μ (s95_lpart a' K) X) (ENNReal.ofReal r) P ≤
        ENNReal.ofReal (S * B') := by
      intro K
      refine (hpart K).trans ?_
      rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => ha0 k)]
      refine ENNReal.ofReal_le_ofReal ((Summable.sum_le_tsum _ (fun k _ => ha0 k) hsum).trans (le_of_eq ?_))
      rw [hS, ← tsum_mul_right]
      exact tsum_congr fun k => by ring
    exact s95_lim_bound P (fun K => s95_lin_meas (s95_lcut_meas ha' _ _)) (s95_lin_meas ha')
      (fun X => s95_lin_tendsto ha' (hinteg B' hB'.le a' ha' hab') X) hE
  refine s95_pos_to_nonneg hS0 hB fun t ht => key (B + t) (by linarith) a ha (fun x => ?_)
  have h0 : 0 ≤ jbracket x ^ Pw := Real.rpow_nonneg (zero_le_one.trans (s95_one_le_jb x)) _
  have := hab x
  nlinarith [mul_nonneg ht.le h0]

end HRS.MS.R2Poly
