import HRS.MS.CritWholePoleDual

/-!
# S8.1 XS, CR02: relative `L²` closeness of the cavity and pole marginals

Duality: a bounded density difference `a - b` has `‖a-b‖_{L²(μ)}² = ∫ (a-b) d(α - β)` for `f = a - b`, so a bound
`|∫ f dα - ∫ f dβ| ≤ K ‖f‖` gives `‖a-b‖ ≤ K` (`s81b_dual_l2`).  The input for `α = π_N`, `β = ν_n` is CR01 integrated
against the exact disintegration `wr13a_cavity_disintegration_density`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

/-- A measure dominated by `c μ` has a measurable density bounded by `c`. -/
theorem s81b_density_of_le {μ ν : Measure (Euc d)} [IsProbabilityMeasure μ] [IsFiniteMeasure ν] {c : ℝ}
    (hc : 0 ≤ c) (h : ν ≤ ENNReal.ofReal c • μ) :
    ∃ φ : Euc d → ℝ, Measurable φ ∧ ν = μ.withDensity (fun y => ENNReal.ofReal (φ y)) ∧
      ∀ y, 0 ≤ φ y ∧ φ y ≤ c := by
  haveI : ν.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_sigmaFinite ν μ
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul h
  have hm : Measurable (ν.rnDeriv μ) := Measure.measurable_rnDeriv ν μ
  have hle : ν.rnDeriv μ ≤ᵐ[μ] fun _ => ENNReal.ofReal c := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hm fun s hs _ => ?_
    rw [Measure.setLIntegral_rnDeriv hac, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter]
    have := Measure.le_iff.1 h s hs
    simpa [Measure.smul_apply, mul_comm] using this
  set φ : Euc d → ℝ := fun y => min (ν.rnDeriv μ y).toReal c with hφ
  have hφm : Measurable φ := hm.ennreal_toReal.min measurable_const
  refine ⟨φ, hφm, ?_, fun y => ⟨le_min ENNReal.toReal_nonneg hc, min_le_right _ _⟩⟩
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq ν μ hac]
  refine withDensity_congr_ae ?_
  filter_upwards [hle, Measure.rnDeriv_lt_top ν μ] with y hy hyt
  simp only [hφ]
  rw [min_eq_left, ENNReal.ofReal_toReal hyt.ne]
  exact ENNReal.toReal_le_of_le_ofReal hc hy

theorem s81b_integral_withDensity {μ : Measure (Euc d)} {a : Euc d → ℝ} (ha : Measurable a)
    (ha0 : ∀ y, 0 ≤ a y) (f : Euc d → ℝ) :
    ∫ y, f y ∂(μ.withDensity (fun y => ENNReal.ofReal (a y))) = ∫ y, a y * f y ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ (ha.ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (ha0 y)]

/-- Duality: bounded densities whose pairings against all bounded tests differ by `K ‖f‖` differ by `K` in `L²(μ)`. -/
theorem s81b_dual_l2 {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a b : Euc d → ℝ} (ha : Measurable a)
    (hb : Measurable b) {Cb : ℝ} (ha0 : ∀ y, 0 ≤ a y ∧ a y ≤ Cb) (hb0 : ∀ y, 0 ≤ b y ∧ b y ≤ Cb) {K : ℝ}
    (hK : 0 ≤ K)
    (h : ∀ f : Euc d → ℝ, Measurable f → ∀ B : ℝ, (∀ y, |f y| ≤ B) →
      |(∫ y, f y ∂(μ.withDensity (fun y => ENNReal.ofReal (a y)))) -
        ∫ y, f y ∂(μ.withDensity (fun y => ENNReal.ofReal (b y)))| ≤ K * l2Norm μ f) :
    MemLp (fun y => a y - b y) 2 μ ∧ l2Norm μ (fun y => a y - b y) ≤ K := by
  set g : Euc d → ℝ := fun y => a y - b y with hg
  have hgm : Measurable g := ha.sub hb
  have hgb : ∀ y, |g y| ≤ Cb := fun y => by
    rw [abs_le]; constructor <;> simp only [hg] <;> linarith [ha0 y, hb0 y]
  have hgint : Integrable (fun y => g y ^ 2) μ :=
    Integrable.of_bound (C := Cb ^ 2) (hgm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        calc g y ^ 2 = |g y| ^ 2 := (sq_abs _).symm
          _ ≤ Cb ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hgb y) 2)
  have hmem : MemLp g 2 μ := by
    refine (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 hgint
  refine ⟨hmem, ?_⟩
  have hpair := h g hgm Cb hgb
  rw [s81b_integral_withDensity ha (fun y => (ha0 y).1), s81b_integral_withDensity hb (fun y => (hb0 y).1)] at hpair
  have hI : ∀ (u : Euc d → ℝ), Measurable u → (∀ y, |u y| ≤ Cb) → Integrable (fun y => u y * g y) μ := by
    intro u hu hub
    refine Integrable.of_bound (C := Cb * Cb) (hu.mul hgm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hub y) (hgb y) (abs_nonneg _) (by linarith [abs_nonneg (u y), hub y])
  have hae : ∀ u, Measurable u → (∀ y, 0 ≤ u y ∧ u y ≤ Cb) → Integrable (fun y => u y * g y) μ := fun u hu hu0 =>
    hI u hu fun y => by rw [abs_of_nonneg (hu0 y).1]; exact (hu0 y).2
  have key : ∫ y, a y * g y ∂μ - ∫ y, b y * g y ∂μ = ∫ y, g y ^ 2 ∂μ := by
    rw [← integral_sub (hae a ha ha0) (hae b hb hb0)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hg]; ring
  rw [key, abs_of_nonneg (integral_nonneg fun y => sq_nonneg _)] at hpair
  have hl : l2Norm μ g ^ 2 = ∫ y, g y ^ 2 ∂μ := by
    unfold l2Norm; rw [Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)]
  rw [← hl] at hpair
  have hl0 : 0 ≤ l2Norm μ g := Real.sqrt_nonneg _
  by_contra hcon
  push Not at hcon
  nlinarith [mul_pos (lt_of_le_of_lt hK hcon) (lt_of_le_of_lt hK hcon)]

theorem s81b_lintegral_shift {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {g : α → Euc d} (hg : Measurable g) {f : Euc d → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ y, |f y| ≤ B) :
    ∫⁻ a, ENNReal.ofReal (f (g a) + B) ∂P = ENNReal.ofReal (∫ y, f y ∂(P.map g) + B) := by
  haveI : IsProbabilityMeasure (P.map g) := (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  have hnn : ∀ y, 0 ≤ f y + B := fun y => by linarith [(abs_le.1 (hB y)).1]
  have hint : Integrable (fun y => f y + B) (P.map g) :=
    Integrable.of_bound (C := 2 * |B|) (hf.add_const B).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn y)]
        have := (abs_le.1 (hB y)).2
        linarith [le_abs_self B])
  have hfint : Integrable f (P.map g) :=
    Integrable.of_bound (C := B) hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB y)
  rw [← lintegral_map (hf.add_const B).ennreal_ofReal hg,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn),
    integral_add hfint (integrable_const _)]
  simp

/-- `∫ f dπ_N` against `∫ f dν_n`: the first marginal of `Q_N` is a mixture of pole marginals. -/
theorem s81b_pi_vs_nu (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      ∀ f : Euc d → ℝ, Measurable f → ∀ B : ℝ, (∀ y, |f y| ≤ B) →
        |(∫ y, f y ∂(firstMarginal (modulatedGibbs (critG d) N D.beta (mu D)))) -
            ∫ y, f y ∂(firstMarginal (cavity D N))| ≤ C * l2Norm (mu D) f * rate N := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < ((d : ℝ) / 2) := by linarith
  have hsd : ((d : ℝ) / 2) < d := by linarith
  obtain ⟨C, hC0, hC⟩ := s81b_pole_dual hd M βm βp hβm hβ
  refine ⟨C, hC0, fun D N hN f hfm B hB => ?_⟩
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hprob : IsProbabilityMeasure (mu D) := Q34.isProbabilityMeasure_nu D.prob
  have hconv := wr13a_conv_le_density hd1 hs0 hsd D.prob D.bound
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  have hpos : 0 < n + 1 - 1 := hn
  set E : ℝ := C * l2Norm (mu D) f * rate (n + 1) with hE
  have hE0 : 0 ≤ E := by rw [hE]; unfold rate l2Norm; positivity
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  set Q := modulatedGibbs (critG d) (n + 1) D.beta (mu D) with hQ
  have hQp : IsProbabilityMeasure Q := wr13c2_Q_isProb hs0 hconv hβ0.le (by omega)
  have hex : HRS.External.Entropy.IsExchangeable Q :=
    modulatedGibbs_isExchangeable (rieszKernel d ((d : ℝ) / 2)) D.beta _ (fun z => rieszKernel_neg z)
  have hP0 : IsProbabilityMeasure (cavity D (n + 1)) := wr13a_cavityLaw_isProb hs0 hconv hβ0.le (n + 1)
  have hpos1 : 0 < n + 1 := Nat.succ_pos n
  have hπ : IsProbabilityMeasure (firstMarginal Q) := by
    unfold firstMarginal; simp only [hpos1, dite_true]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply _).aemeasurable).2 inferInstance
  have hνp : IsProbabilityMeasure (firstMarginal (cavity D (n + 1))) := by
    unfold firstMarginal; simp only [hpos, dite_true]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply _).aemeasurable).2 inferInstance
  set F : Euc d × EucConfig d n → ℝ≥0∞ := fun p => ENNReal.ofReal (f (p.2 i0) + B) with hF
  have hFm : Measurable F :=
    ((hfm.comp ((measurable_pi_apply i0).comp measurable_snd)).add_const B).ennreal_ofReal
  have key := wr13a_cavity_disintegration_density hd hs0 hsd D.prob D.bound hβ0.le n F hFm
  have hLHS : ∫⁻ X : EucConfig d (n + 1), F (X 0, Fin.tail X) ∂Q =
      ENNReal.ofReal (∫ y, f y ∂(firstMarginal Q) + B) := by
    have h1 : ∀ X : EucConfig d (n + 1), F (X 0, Fin.tail X) = ENNReal.ofReal (f (X (Fin.succ i0)) + B) :=
      fun X => rfl
    simp_rw [h1]
    refine (s81b_lintegral_shift (measurable_pi_apply (Fin.succ i0)) hfm hB).trans ?_
    have : firstMarginal Q = Q.map (fun X => X (Fin.succ i0)) := by
      unfold firstMarginal; simp only [hpos1, dite_true]
      exact (hex.marginal_eq (Fin.succ i0) 0).symm
    rw [this]
  have hinner : ∀ x : Euc d, ∫⁻ Y : EucConfig d n, F (x, Y) ∂(pole D (n + 1) x 1) =
      ENNReal.ofReal (∫ y, f y ∂(firstMarginal (pole D (n + 1) x 1)) + B) := by
    intro x
    have := wr13c2_poleLaw_isProb hs0 hconv hβ0.le zero_le_one (n + 1) x
    have h1 : ∀ Y : EucConfig d n, F (x, Y) = ENNReal.ofReal (f (Y i0) + B) := fun Y => rfl
    simp_rw [h1]
    refine (s81b_lintegral_shift (P := pole D (n + 1) x 1)
      (g := fun Y : EucConfig d (n + 1 - 1) => Y i0) (measurable_pi_apply i0) hfm hB).trans ?_
    unfold firstMarginal; simp only [hpos, dite_true]
    rfl
  set m : ℝ := ∫ y, f y ∂(firstMarginal (cavity D (n + 1))) with hm
  have hbd : ∀ (P : Measure (Euc d)) [IsProbabilityMeasure P], |∫ y, f y ∂P| ≤ B := by
    intro P _
    have := norm_integral_le_of_norm_le_const (μ := P) (f := f) (C := B)
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB y)
    simpa [Real.norm_eq_abs] using this
  have hmB : |m| ≤ B := hbd _
  have hπB : |∫ y, f y ∂(firstMarginal Q)| ≤ B := hbd _
  have hcl : ∀ x, |(∫ y, f y ∂(firstMarginal (pole D (n + 1) x 1))) - m| ≤ E := fun x =>
    hC D (n + 1) hN x 1 ⟨zero_le_one, le_rfl⟩ f hfm B hB
  rw [hLHS] at key
  simp_rw [hinner] at key
  have hup : ENNReal.ofReal (∫ y, f y ∂(firstMarginal Q) + B) ≤ ENNReal.ofReal (m + B + E) := by
    rw [key]
    calc _ ≤ ∫⁻ x, ENNReal.ofReal (m + B + E) ∂(firstMarginal Q) :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 (hcl x)).2])
      _ = _ := by simp
  have hlo : ENNReal.ofReal (m + B - E) ≤ ENNReal.ofReal (∫ y, f y ∂(firstMarginal Q) + B) := by
    rw [key]
    calc ENNReal.ofReal (m + B - E) = ∫⁻ x, ENNReal.ofReal (m + B - E) ∂(firstMarginal Q) := by simp
      _ ≤ _ := lintegral_mono fun x => ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 (hcl x)).1])
  rw [ENNReal.ofReal_le_ofReal_iff (by linarith [(abs_le.1 hmB).1, (abs_le.1 hmB).2])] at hup
  rw [ENNReal.ofReal_le_ofReal_iff (by linarith [(abs_le.1 hπB).1, (abs_le.1 hπB).2])] at hlo
  rw [abs_le]; constructor <;> linarith

theorem s81b_memLp_of_bdd {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {u : Euc d → ℝ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ y, |u y| ≤ B) : MemLp u 2 μ :=
  MemLp.of_bound hu.aestronglyMeasurable B (Filter.Eventually.of_forall fun y => by
    simpa [Real.norm_eq_abs] using hB y)

theorem s81b_eLp_l2 {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {u : Euc d → ℝ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ y, |u y| ≤ B) : eLpNorm u 2 μ = ENNReal.ofReal (l2Norm μ u) := by
  have hint : Integrable (fun y => u y ^ 2) μ :=
    (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).1 (s81b_memLp_of_bdd hu hB)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hu.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  have : ∫⁻ y, ‖u y‖ₑ ^ (2 : ℝ) ∂μ = ENNReal.ofReal (∫ y, u y ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.rpow_two, ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  rw [this, ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun y => sq_nonneg _) (by norm_num), l2Norm,
    Real.sqrt_eq_rpow]

theorem s81b_l2_triangle {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {u v w : Euc d → ℝ}
    (hu : Measurable u) (hv : Measurable v) (hw : Measurable w) {B : ℝ}
    (hub : ∀ y, |u y| ≤ B) (hvb : ∀ y, |v y| ≤ B) (hwb : ∀ y, |w y| ≤ B) :
    l2Norm μ (fun y => u y - w y) ≤ l2Norm μ (fun y => u y - v y) + l2Norm μ (fun y => v y - w y) := by
  have b1 : ∀ y, |u y - v y| ≤ 2 * B := fun y => by
    calc |u y - v y| ≤ |u y| + |v y| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hub y, hvb y]
  have b2 : ∀ y, |v y - w y| ≤ 2 * B := fun y => by
    calc |v y - w y| ≤ |v y| + |w y| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hvb y, hwb y]
  have b3 : ∀ y, |u y - w y| ≤ 2 * B := fun y => by
    calc |u y - w y| ≤ |u y| + |w y| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hub y, hwb y]
  have h := eLpNorm_add_le (p := 2) (μ := μ) (f := fun y => u y - v y) (g := fun y => v y - w y)
    (by norm_num)
  have e : (fun y => u y - v y) + (fun y => v y - w y) = fun y => u y - w y := by
    funext y; simp
  rw [e, s81b_eLp_l2 (u := fun y => u y - w y) (hu.sub hw) b3, s81b_eLp_l2 (u := fun y => u y - v y) (hu.sub hv) b1,
    s81b_eLp_l2 (u := fun y => v y - w y) (hv.sub hw) b2] at h
  have hl : ∀ f : Euc d → ℝ, 0 ≤ l2Norm μ f := fun f => Real.sqrt_nonneg _
  rw [← ENNReal.ofReal_add (hl _) (hl _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (hl _) (hl _))).1 h

theorem s81b_rate_le_delta (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) :
    rate N ≤ deltaN d ((d : ℝ) / 2) N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hδ : deltaN d ((d : ℝ) / 2) N = (N : ℝ)⁻¹ * Real.log (Real.exp 1 * N) := by
    simp only [deltaN, lt_self_iff_false, if_false, if_true]
  have hl : Real.log (Real.exp 1 * N) = 1 + Real.log N := by
    rw [Real.log_mul (Real.exp_pos _).ne' hN0.ne', Real.log_exp]
  rw [hδ, hl, rate, div_eq_mul_inv, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  nlinarith [Real.sq_sqrt hlogN, Real.sqrt_nonneg (Real.log N), sq_nonneg (Real.sqrt (Real.log N) - 1)]

theorem s81b_l2_symm {μ : Measure (Euc d)} (u v : Euc d → ℝ) :
    l2Norm μ (fun y => u y - v y) = l2Norm μ (fun y => v y - u y) := by
  unfold l2Norm
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only; ring

theorem s81b_pole_marginal_le (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      firstMarginal (pole D N x t) ≤ ENNReal.ofReal C • mu D := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < ((d : ℝ) / 2) := by linarith
  have hsd : ((d : ℝ) / 2) < d := by linarith
  obtain ⟨C, hC1, hb⟩ := wr13a_pole_bundle hd hs0 hsd (hβm.le.trans hβ) M
  refine ⟨C, hC1, fun D N hN x t ht => ?_⟩
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hle := (((hb D.rho D.prob D.bound D.beta hβ0.le D.beta_mem.2 N hN).2.2 x t ht).2.1)
  refine hle.trans ?_
  refine Measure.le_iff.2 fun s hs => ?_
  rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ y in s, ENNReal.ofReal (C * Real.exp (-(t * (D.beta / N)) * rieszKernel d ((d : ℝ) / 2) (x - y))) ∂(mu D)
      ≤ ∫⁻ y in s, ENNReal.ofReal C ∂(mu D) := by
        refine setLIntegral_mono' hs fun y _ => ENNReal.ofReal_le_ofReal ?_
        have : Real.exp (-(t * (D.beta / N)) * rieszKernel d ((d : ℝ) / 2) (x - y)) ≤ 1 :=
          Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.2 (mul_nonneg ht.1 (div_nonneg hβ0.le (Nat.cast_nonneg _)))) (wr13a_g_nonneg hs0 _))
        nlinarith [Real.exp_pos (-(t * (D.beta / N)) * rieszKernel d ((d : ℝ) / 2) (x - y))]
    _ = _ := by simp [mul_comm]

set_option maxHeartbeats 800000 in
theorem s81b_cavity_relative_L2 (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      ∃ q : Euc d → ℝ, Measurable q ∧
        firstMarginal (cavity D N) = (mu D).withDensity (fun y => ENNReal.ofReal (q y)) ∧
        (∀ y, 0 ≤ q y ∧ q y ≤ C) ∧
        MemLp (fun y => q y - 1) 2 (mu D) ∧
        l2Norm (mu D) (fun y => q y - 1) ≤ C * deltaN d ((d : ℝ) / 2) N ∧
        MemLp (fun y => theta D N y - q y) 2 (mu D) ∧
        l2Norm (mu D) (fun y => theta D N y - q y) ≤ C * rate N ∧
        ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          HasMarginalDensityBounds (firstMarginal (pole D N x t)) (mu D)
            C (C * deltaN d ((d : ℝ) / 2) N) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < ((d : ℝ) / 2) := by linarith
  have hsd : ((d : ℝ) / 2) < d := by linarith
  have hβp : 0 ≤ βp := (hβm.trans_le hβ).le
  obtain ⟨C', hC'1, hC'⟩ := wr13d_cavMarg_le hd hs0 hsd βp M hβp
  obtain ⟨C3, hC3⟩ := wr13d_marginal_density_bounds hd hs0 hsd hβm hβ M
  obtain ⟨Cp, hCp1, hCp⟩ := s81b_pole_marginal_le hd M βm βp hβm hβ
  obtain ⟨Cπ, hCπ0, hCπ⟩ := s81b_pi_vs_nu hd M βm βp hβm hβ
  obtain ⟨Cd, hCd0, hCd⟩ := s81b_pole_dual hd M βm βp hβm hβ
  set Cθ : ℝ := Real.exp (2 * βp * |potentialBound d ((d : ℝ) / 2) M|) with hCθ
  have hCθ1 : 1 ≤ Cθ := Real.one_le_exp (by positivity)
  set C3' : ℝ := max C3 0 with hC3'
  have hC30 : 0 ≤ C3' := le_max_right _ _
  refine ⟨1 + C' + Cp + Cπ + C3' + Cd, by linarith, fun D N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hββp : D.beta ≤ βp := D.beta_mem.2
  have hprob : IsProbabilityMeasure (mu D) := Q34.isProbabilityMeasure_nu D.prob
  have hconv := wr13a_conv_le_density hd1 hs0 hsd D.prob D.bound
  have hn1 : 1 ≤ n + 1 - 1 := by omega
  have hrate0 : 0 ≤ rate (n + 1) := by unfold rate; positivity
  have hrδ := s81b_rate_le_delta hd1 hN
  have hδ0 : 0 ≤ deltaN d ((d : ℝ) / 2) (n + 1) := hrate0.trans hrδ
  set μ : Measure (Euc d) := mu D with hμ
  -- the cavity marginal density
  have hνp : IsProbabilityMeasure (firstMarginal (cavity D (n + 1))) := by
    have : 0 < n + 1 - 1 := by omega
    unfold firstMarginal; simp only [this, dite_true]
    haveI := wr13a_cavityLaw_isProb hs0 hconv hβ0.le (n + 1)
    exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply _).aemeasurable).2 inferInstance
  have hνle : firstMarginal (cavity D (n + 1)) ≤ ENNReal.ofReal C' • μ := by
    have := hC' D.rho D.prob D.bound D.beta hβ0.le hββp (n + 1) hN
    exact this
  obtain ⟨q, hqm, hνq, hq0⟩ := s81b_density_of_le (μ := μ) (by linarith) hνle
  -- the full density θ
  have hθm : Measurable (theta D (n + 1)) := wr13d_theta_meas hd hs0 hsd D.prob D.bound hβ0.le (n + 1 - 1)
  have hθ0 : ∀ y, 0 ≤ theta D (n + 1) y ∧ theta D (n + 1) y ≤ Cθ := fun y => by
    refine ⟨(wr13d_theta_pos hd hs0 hsd D.prob D.bound hβ0.le hn1 y).le, ?_⟩
    refine (wr13d_theta_le hd hs0 hsd D.prob D.bound hβ0.le (n + 1 - 1) y).trans (Real.exp_le_exp.2 ?_)
    have : 0 ≤ 2 * D.beta := by positivity
    calc 2 * D.beta * potentialBound d ((d : ℝ) / 2) M ≤ 2 * D.beta * |potentialBound d ((d : ℝ) / 2) M| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) this
      _ ≤ 2 * βp * |potentialBound d ((d : ℝ) / 2) M| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have hπeq : firstMarginal (modulatedGibbs (critG d) (n + 1) D.beta μ) =
      μ.withDensity (fun y => ENNReal.ofReal (theta D (n + 1) y)) :=
    wr13d_firstMarginal_eq hd hs0 hsd D.prob D.bound hβ0.le (n + 1 - 1)
  have hπp : IsProbabilityMeasure (firstMarginal (modulatedGibbs (critG d) (n + 1) D.beta μ)) := by
    have hQp : IsProbabilityMeasure (modulatedGibbs (critG d) (n + 1) D.beta μ) :=
      wr13c2_Q_isProb hs0 hconv hβ0.le (by omega)
    have : 0 < n + 1 := Nat.succ_pos n
    unfold firstMarginal; simp only [this, dite_true]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply _).aemeasurable).2 inferInstance
  set Bd : ℝ := max Cθ (max C' 1) with hBd
  have hqb : ∀ y, |q y| ≤ Bd := fun y => by
    rw [abs_of_nonneg (hq0 y).1]
    exact (hq0 y).2.trans ((le_max_left C' 1).trans (le_max_right _ _))
  have hθb : ∀ y, |theta D (n + 1) y| ≤ Bd := fun y => by
    rw [abs_of_nonneg (hθ0 y).1]; exact (hθ0 y).2.trans (le_max_left _ _)
  have h1b : ∀ y : Euc d, |(1 : ℝ)| ≤ Bd := fun y => by
    rw [abs_one]; exact (le_max_right C' 1).trans (le_max_right _ _)
  -- θ versus q
  obtain ⟨hmem1, hl1⟩ := s81b_dual_l2 (μ := μ) (a := theta D (n + 1)) (b := q) hθm hqm (Cb := Bd)
    (fun y => ⟨(hθ0 y).1, (hθ0 y).2.trans (le_max_left _ _)⟩)
    (fun y => ⟨(hq0 y).1, (hq0 y).2.trans ((le_max_left C' 1).trans (le_max_right _ _))⟩)
    (K := Cπ * rate (n + 1)) (by positivity) (by
      intro f hf B hB
      rw [← hπeq, ← hνq]
      have := hCπ D (n + 1) hN f hf B hB
      calc _ ≤ Cπ * l2Norm μ f * rate (n + 1) := this
        _ = _ := by ring)
  -- θ minus 1
  obtain ⟨φ, hφm, hφeq, hφ0, hφL2, hφn⟩ := hC3 D.rho D.prob D.bound D.beta D.beta_mem (n + 1) hN
  have hθφ : theta D (n + 1) =ᵐ[μ] φ := by
    have hπφ : μ.withDensity (fun y => ENNReal.ofReal (theta D (n + 1) y)) =
        μ.withDensity (fun y => ENNReal.ofReal (φ y)) := hπeq.symm.trans hφeq
    have hfin : ∫⁻ y, ENNReal.ofReal (theta D (n + 1) y) ∂μ ≠ ⊤ := by
      have := measure_univ (μ := firstMarginal (modulatedGibbs (critG d) (n + 1) D.beta μ))
      rw [hπeq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
      rw [this]; exact ENNReal.one_ne_top
    have := (withDensity_eq_iff hθm.ennreal_ofReal.aemeasurable hφm.ennreal_ofReal.aemeasurable hfin).1 hπφ
    filter_upwards [this] with y hy
    exact (ENNReal.ofReal_eq_ofReal_iff (hθ0 y).1 (hφ0 y).1).1 hy
  have hθ1 : l2Norm μ (fun y => theta D (n + 1) y - 1) ≤ C3' * deltaN d ((d : ℝ) / 2) (n + 1) := by
    have : l2Norm μ (fun y => theta D (n + 1) y - 1) = l2Norm μ (fun y => φ y - 1) := by
      unfold l2Norm; congr 1
      refine integral_congr_ae ?_
      filter_upwards [hθφ] with y hy
      simp only [hy]
    rw [this]
    exact hφn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0)
  have hone : Measurable (fun _ : Euc d => (1 : ℝ)) := measurable_const
  have hq1 : l2Norm μ (fun y => q y - 1) ≤ (Cπ + C3') * deltaN d ((d : ℝ) / 2) (n + 1) := by
    have h := s81b_l2_triangle (μ := μ) (u := q) (v := theta D (n + 1)) (w := fun _ => 1) hqm hθm hone
      hqb hθb h1b
    have hs : l2Norm μ (fun y => q y - theta D (n + 1) y) = l2Norm μ (fun y => theta D (n + 1) y - q y) :=
      s81b_l2_symm _ _
    rw [hs] at h
    have hr : Cπ * rate (n + 1) ≤ Cπ * deltaN d ((d : ℝ) / 2) (n + 1) := mul_le_mul_of_nonneg_left hrδ hCπ0
    calc _ ≤ l2Norm μ (fun y => theta D (n + 1) y - q y) + l2Norm μ (fun y => theta D (n + 1) y - 1) := h
      _ ≤ Cπ * rate (n + 1) + C3' * deltaN d ((d : ℝ) / 2) (n + 1) := add_le_add hl1 hθ1
      _ ≤ _ := by nlinarith
  have hBq : ∀ y, |q y - 1| ≤ Bd + 1 := fun y => by
    calc |q y - 1| ≤ |q y| + |1| := abs_sub _ _
      _ ≤ Bd + 1 := by rw [abs_one]; linarith [hqb y]
  have hCfin : ∀ z, z ≤ C' ∨ z ≤ Cp ∨ z ≤ Cπ + C3' + Cd → z ≤ 1 + C' + Cp + Cπ + C3' + Cd := by
    intro z hz
    rcases hz with h | h | h <;> linarith
  refine ⟨q, hqm, hνq, fun y => ⟨(hq0 y).1, (hq0 y).2.trans (hCfin _ (Or.inl le_rfl))⟩,
    s81b_memLp_of_bdd (hqm.sub_const 1) hBq, ?_, hmem1, ?_, ?_⟩
  · refine hq1.trans (mul_le_mul_of_nonneg_right ?_ hδ0)
    linarith
  · exact hl1.trans (mul_le_mul_of_nonneg_right (by linarith) hrate0)
  · intro x t ht
    have hPp := wr13c2_poleLaw_isProb hs0 hconv hβ0.le ht.1 (n + 1) x
    have hppm : IsProbabilityMeasure (firstMarginal (pole D (n + 1) x t)) := by
      have : 0 < n + 1 - 1 := by omega
      unfold firstMarginal; simp only [this, dite_true]
      exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply _).aemeasurable).2 hPp
    obtain ⟨φx, hφxm, hφxeq, hφx0⟩ := s81b_density_of_le (μ := μ) (c := Cp) (by linarith)
      (hCp D (n + 1) hN x t ht)
    obtain ⟨hmemx, hlx⟩ := s81b_dual_l2 (μ := μ) (a := φx) (b := q) hφxm hqm (Cb := max Cp Bd)
      (fun y => ⟨(hφx0 y).1, (hφx0 y).2.trans (le_max_left _ _)⟩)
      (fun y => ⟨(hq0 y).1, (hq0 y).2.trans (((le_max_left C' 1).trans (le_max_right _ _)).trans
        (le_max_right _ _))⟩)
      (K := Cd * rate (n + 1)) (by positivity) (by
        intro f hf B hB
        rw [← hφxeq, ← hνq]
        have := hCd D (n + 1) hN x t ht f hf B hB
        calc _ ≤ Cd * l2Norm μ f * rate (n + 1) := this
          _ = _ := by ring)
    have hφxb : ∀ y, |φx y| ≤ max Cp Bd := fun y => by
      rw [abs_of_nonneg (hφx0 y).1]; exact (hφx0 y).2.trans (le_max_left _ _)
    have hqb' : ∀ y, |q y| ≤ max Cp Bd := fun y => (hqb y).trans (le_max_right _ _)
    have h1b' : ∀ y : Euc d, |(1 : ℝ)| ≤ max Cp Bd := fun y => (h1b y).trans (le_max_right _ _)
    have h := s81b_l2_triangle (μ := μ) (u := φx) (v := q) (w := fun _ => 1) hφxm hqm hone hφxb hqb' h1b'
    have hr : Cd * rate (n + 1) ≤ Cd * deltaN d ((d : ℝ) / 2) (n + 1) := mul_le_mul_of_nonneg_left hrδ hCd0
    have hBx : ∀ y, |φx y - 1| ≤ max Cp Bd + 1 := fun y => by
      calc |φx y - 1| ≤ |φx y| + |1| := abs_sub _ _
        _ ≤ max Cp Bd + 1 := by rw [abs_one]; linarith [hφxb y]
    refine ⟨φx, hφxm, hφxeq, fun y => ⟨(hφx0 y).1, (hφx0 y).2.trans (hCfin _ (Or.inr (Or.inl le_rfl)))⟩,
      s81b_memLp_of_bdd (hφxm.sub_const 1) hBx, ?_⟩
    calc _ ≤ l2Norm μ (fun y => φx y - q y) + l2Norm μ (fun y => q y - 1) := h
      _ ≤ Cd * rate (n + 1) + (Cπ + C3') * deltaN d ((d : ℝ) / 2) (n + 1) := add_le_add hlx hq1
      _ ≤ _ := by nlinarith

end HRS.Whole.S81b
