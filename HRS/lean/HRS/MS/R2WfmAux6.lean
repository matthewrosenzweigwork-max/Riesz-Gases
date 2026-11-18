import HRS.MS.R2WfmAux5

/-!
# HRS.MS.R2WfmAux6 -- `round2_weighted_field_moments` (S9.7), part 6: the core estimate

Packet S97.  `s97_core_one`: for every `N ≥ 2`, `E[‖√N(μ_N-μ)‖^r_{-m,P} + ‖𝓡_N‖^r_{-m,P}] ≤ C` and the centred version, for any
family of laws satisfying `HasR2ActualDensity` (and `IsRound2Density`, Gaussian upper bound), `m ≥ d/2 + 5/2`, `r ≥ 1`.
Per-`ξ` `L^r` bounds come from S9.5 (`round2_polynomial_moments_proof`, applied at `r' = max r 3`) for the weighted plane waves;
joint measurability in `(X,ξ)` from the explicit formulas; the rest is `s97_frame`.
-/

open MeasureTheory
open scoped FourierTransform ENNReal NNReal

noncomputable section
namespace HRS.MS.R2Wfm
open HRS.Whole HRS.MS.R2Poly HRS.MS.Wr
open HRS.PDE.ToolboxRd.FourierAux (wt wt_pos one_le_wt)

variable {d : ℕ}

/-- Joint measurability of `pairEnergy` in the configuration and a parameter. -/
theorem s97_pe_meas {N : ℕ} (μ : Measure (Euc d)) [SFinite μ]
    (k : Euc d → Euc d → Euc d → ℝ) (hk : Measurable (fun q : Euc d × Euc d × Euc d => k q.1 q.2.1 q.2.2)) :
    Measurable (fun q : EucConfig d N × Euc d => pairEnergy (k q.2) q.1 μ) := by
  unfold pairEnergy
  have hpt : ∀ (f g : EucConfig d N × Euc d → Euc d), Measurable f → Measurable g →
      Measurable (fun q : EucConfig d N × Euc d => k q.2 (f q) (g q)) := fun f g hf hg =>
    hk.comp (measurable_snd.prodMk (hf.prodMk hg))
  have hcoord : ∀ i : Fin N, Measurable (fun q : EucConfig d N × Euc d => q.1 i) := fun i =>
    (measurable_pi_apply i).comp measurable_fst
  have h1 : Measurable (fun q : EucConfig d N × Euc d => (1 / (2 * (N : ℝ) ^ 2)) *
      ∑ i, ∑ j ∈ Finset.univ.erase i, k q.2 (q.1 i) (q.1 j)) :=
    measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      hpt _ _ (hcoord i) (hcoord j))
  have h2 : Measurable (fun q : EucConfig d N × Euc d => (1 / (N : ℝ)) * ∑ i, ∫ y, k q.2 (q.1 i) y ∂μ) := by
    refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    have : StronglyMeasurable (fun q : EucConfig d N × Euc d => ∫ y, k q.2 (q.1 i) y ∂μ) := by
      refine StronglyMeasurable.integral_prod_right (f := fun (q : EucConfig d N × Euc d) (y : Euc d) => k q.2 (q.1 i) y) ?_
      exact (hk.comp ((measurable_snd.comp measurable_fst).prodMk
        (((hcoord i).comp measurable_fst).prodMk measurable_snd))).stronglyMeasurable
    exact this.measurable
  have h3 : Measurable (fun q : EucConfig d N × Euc d => (1 / 2 : ℝ) * ∫ x, ∫ y, k q.2 x y ∂μ ∂μ) := by
    refine measurable_const.mul ?_
    have hI2 : StronglyMeasurable (fun p : Euc d × Euc d => ∫ y, k p.1 p.2 y ∂μ) := by
      refine StronglyMeasurable.integral_prod_right (f := fun (p : Euc d × Euc d) (y : Euc d) => k p.1 p.2 y) ?_
      exact (hk.comp ((measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).stronglyMeasurable
    have hJ : StronglyMeasurable (fun ξ : Euc d => ∫ x, ∫ y, k ξ x y ∂μ ∂μ) := by
      refine StronglyMeasurable.integral_prod_right (f := fun (ξ : Euc d) (x : Euc d) => ∫ y, k ξ x y ∂μ) ?_
      exact hI2
    exact hJ.measurable.comp measurable_snd
  exact (h1.sub h2).add h3


theorem s97_pw_cont2' (Pw φ0 : ℝ) : Continuous (fun p : Euc d × Euc d => s97_pw Pw p.1 φ0 p.2) :=
  Continuous.comp (g := fun p : Euc d × Euc d => s97_pw Pw p.2 φ0 p.1) (s97_pw_cont2 Pw φ0)
    (f := Prod.swap) continuous_swap

theorem s97_emp_meas (μ : Measure (Euc d)) [SFinite μ] {N : ℕ} (hN : 0 < N) (Pw φ0 : ℝ) :
    Measurable (fun q : EucConfig d N × Euc d => r2EmpDistr μ q.1 (s97_pw Pw q.2 φ0)) := by
  unfold r2EmpDistr
  have h1 : Measurable (fun q : EucConfig d N × Euc d =>
      HRS.Whole.pair (HRS.Whole.empirical q.1) (s97_pw Pw q.2 φ0)) := by
    simp_rw [HRS.Whole.pair_empirical hN]
    refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    exact Measurable.comp (g := fun p : Euc d × Euc d => s97_pw Pw p.1 φ0 p.2) (s97_pw_cont2' Pw φ0).measurable
      (f := fun q : EucConfig d N × Euc d => (q.2, q.1 i)) (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))
  have h2 : Measurable (fun q : EucConfig d N × Euc d => HRS.Whole.pair μ (s97_pw Pw q.2 φ0)) := by
    have : StronglyMeasurable (fun ξ : Euc d => ∫ x, s97_pw Pw ξ φ0 x ∂μ) :=
      StronglyMeasurable.integral_prod_right (f := fun (ξ : Euc d) (x : Euc d) => s97_pw Pw ξ φ0 x)
        (s97_pw_cont2' Pw φ0).stronglyMeasurable
    exact this.measurable.comp measurable_snd
  exact measurable_const.mul (h1.sub h2)

theorem s97_comm_meas (s Pw φ0 : ℝ) (μ : Measure (Euc d)) [SFinite μ] {N : ℕ} :
    Measurable (fun q : EucConfig d N × Euc d => r2CommDistr d s μ q.1 (s97_pw Pw q.2 φ0)) := by
  unfold r2CommDistr
  exact measurable_const.mul (s97_pe_meas μ (fun ξ => s97_K s Pw ξ φ0) (s97_K_meas s Pw φ0))

theorem s97_rpow_le {x : ℝ≥0∞} {r r' : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ r') : x ^ r ≤ 1 + x ^ r' := by
  by_cases hx : x ≤ 1
  · exact (ENNReal.rpow_le_one hx hr0).trans le_self_add
  · exact (ENNReal.rpow_le_rpow_of_exponent_le (le_of_lt (not_le.1 hx)) hr).trans le_add_self

theorem s97_lint_one_add {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {G : Ω → ℝ≥0∞} (hG : Measurable G) : ∫⁻ ω, (1 + G ω) ∂P = 1 + ∫⁻ ω, G ω ∂P := by
  rw [lintegral_add_left measurable_const]
  simp

theorem s97_bu_emp (μ : Measure (Euc d)) {N : ℕ} (P : Measure (EucConfig d N)) {r' C5 κ Pw : ℝ} (hP : 0 ≤ Pw)
    (hκ : max C5 0 ≤ κ)
    (hc3 : ∀ a : Euc d → ℝ, Measurable a → (∀ x, |a x| ≤ 1 * jbracket x ^ Pw) →
      eLpNorm (fun X : EucConfig d N => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a))
        (ENNReal.ofReal r') P ≤ ENNReal.ofReal (C5 * 1)) (ξ : Euc d) (φ0 : ℝ) :
    eLpNorm (fun X : EucConfig d N => r2EmpDistr μ X (s97_pw Pw ξ φ0)) (ENNReal.ofReal r') P ≤
      ENNReal.ofReal (κ * wt ξ) := by
  have hcont : Continuous (fun x : Euc d => s97_pw Pw ξ φ0 x) :=
    Continuous.comp (g := fun p : Euc d × Euc d => s97_pw Pw p.1 φ0 p.2) (s97_pw_cont2' Pw φ0)
      (f := fun x : Euc d => (ξ, x)) (continuous_const.prodMk continuous_id)
  have := hc3 (s97_pw Pw ξ φ0) hcont.measurable (fun x => by simpa using s97_pw_abs Pw ξ φ0 x)
  refine this.trans (ENNReal.ofReal_le_ofReal ?_)
  have hw1 : 1 ≤ wt ξ := one_le_wt ξ
  have h1 : C5 * 1 ≤ max C5 0 := by simp
  have h0 : 0 ≤ max C5 0 := le_max_right _ _
  nlinarith

theorem s97_bu_comm {s : ℝ} (hs0 : 0 ≤ s) (μ : Measure (Euc d)) {N : ℕ} (P : Measure (EucConfig d N))
    {r' C5 κ Pw : ℝ} (hP : 0 ≤ Pw) (hκ : max C5 0 * (1 + 2 * s97_Kc s Pw) ≤ κ)
    (hc1 : ∀ B : ℝ, 0 ≤ B → ∀ h : Euc d → Euc d → ℝ, IsR2PolyPairKernel s Pw B h →
      eLpNorm (fun X : EucConfig d N => (N : ℝ) * pairEnergy h X μ) (ENNReal.ofReal r') P ≤ ENNReal.ofReal (C5 * B))
    (ξ : Euc d) (φ0 : ℝ) :
    eLpNorm (fun X : EucConfig d N => r2CommDistr d s μ X (s97_pw Pw ξ φ0)) (ENNReal.ofReal r') P ≤
      ENNReal.ofReal (κ * wt ξ) := by
  have hKc0 := s97_Kc_nonneg (s := s) Pw hP
  have hB : 0 ≤ s97_Kc s Pw * (1 + ‖ξ‖) ^ 2 := mul_nonneg hKc0 (by positivity)
  have := hc1 _ hB _ (s97_poly_kernel hs0 hP ξ φ0)
  refine this.trans (ENNReal.ofReal_le_ofReal ?_)
  have hw := s97_wt_ge ξ
  have hC0 : 0 ≤ max C5 0 := le_max_right _ _
  have h1 : C5 * (s97_Kc s Pw * (1 + ‖ξ‖) ^ 2) ≤ max C5 0 * (s97_Kc s Pw * (1 + ‖ξ‖) ^ 2) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hB
  have h2 : (1 + ‖ξ‖) ^ 2 ≤ 2 * wt ξ := by linarith
  have h3 : max C5 0 * (s97_Kc s Pw * (1 + ‖ξ‖) ^ 2) ≤ max C5 0 * (s97_Kc s Pw * (2 * wt ξ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hKc0) hC0
  have h4 : max C5 0 * (s97_Kc s Pw * (2 * wt ξ)) ≤ κ * wt ξ := by
    have : 1 ≤ wt ξ := one_le_wt ξ
    have hk : 0 ≤ κ := le_trans (mul_nonneg hC0 (by linarith)) hκ
    nlinarith [mul_nonneg hC0 hKc0, mul_nonneg (mul_nonneg hC0 hKc0) (sub_nonneg.2 this)]
  exact (h1.trans h3).trans h4

theorem s97_core_one (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (M L C₀ c₀ b p K Pw : ℝ) (hc : 0 < c₀) (hb : 0 < b) (hp : 1 < p) (hP : 0 ≤ Pw) (m : ℕ)
    (hm : (d : ℝ) / 2 + 5 / 2 ≤ m) (r : ℝ) (hr : 1 ≤ r) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ → ∀ P : ∀ N, Measure (EucConfig d N),
      (∀ N, 2 ≤ N → HasR2ActualDensity s b p K (HRS.Whole.withDensityReal ρ) (P N)) →
      (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) → ∀ N : ℕ, 2 ≤ N →
      ∫⁻ X, (r2NegSobNorm m Pw (r2EmpDistr (HRS.Whole.withDensityReal ρ) X) ^ r +
        r2NegSobNorm m Pw (r2CommDistr d s (HRS.Whole.withDensityReal ρ) X) ^ r) ∂(P N) ≤ ENNReal.ofReal C ∧
      ∫⁻ X, (r2NegSobNorm m Pw (fun φ => r2EmpDistr (HRS.Whole.withDensityReal ρ) X φ -
          ∫ Y, r2EmpDistr (HRS.Whole.withDensityReal ρ) Y φ ∂(P N)) ^ r +
        r2NegSobNorm m Pw (fun φ => r2CommDistr d s (HRS.Whole.withDensityReal ρ) X φ -
          ∫ Y, r2CommDistr d s (HRS.Whole.withDensityReal ρ) Y φ ∂(P N)) ^ r) ∂(P N) ≤ ENNReal.ofReal C := by
  set r' : ℝ := max r 3 with hr'
  have hr'2 : 2 < r' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hrr' : r ≤ r' := le_max_left _ _
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨C5, h5⟩ := @HRS.MS.R2Poly.round2_polynomial_moments_proof d hd s hs0 hs M L C₀ c₀ b p K Pw hb hp hP r'
    (by linarith)
  set κ : ℝ := max C5 0 * (1 + 2 * s97_Kc s Pw) with hκ
  have hKc0 := s97_Kc_nonneg (s := s) Pw hP
  have hκ0 : 0 ≤ κ := mul_nonneg (le_max_right _ _) (by linarith)
  obtain ⟨Cf, hCf⟩ := s97_frame d m hm (r := r') (κ := κ) hr'2 hκ0
  refine ⟨2 + 2 * max Cf 0, fun ρ hρ P hP' hG N hN => ?_⟩
  have hGauss : HasR2GaussianUpper C₀ c₀ ρ := ⟨hc, hG⟩
  have hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ.prob
  have hPN : IsProbabilityMeasure (P N) := (hP' N hN).1
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hN0 : 0 < N := by omega
  obtain ⟨c1, -, c3⟩ := h5 ρ hρ hGauss P hP'
  have hbu_e : ∀ ξ φ0, eLpNorm (fun X => r2EmpDistr μ X (s97_pw Pw ξ φ0)) (ENNReal.ofReal r') (P N) ≤
      ENNReal.ofReal (κ * wt ξ) := fun ξ φ0 =>
    s97_bu_emp μ (P N) hP (by rw [hκ]; nlinarith [le_max_right C5 0]) (fun a ha hab => c3 1 zero_le_one N hN a ha hab) ξ φ0
  have hbu_c : ∀ ξ φ0, eLpNorm (fun X => r2CommDistr d s μ X (s97_pw Pw ξ φ0)) (ENNReal.ofReal r') (P N) ≤
      ENNReal.ofReal (κ * wt ξ) := fun ξ φ0 =>
    s97_bu_comm hs0 μ (P N) hP (le_of_eq hκ.symm) (fun B hB h hh => ((c1 B hB h hh) () N hN).1) ξ φ0
  -- empirical part
  have e1 : Measurable (fun q : EucConfig d N × Euc d => r2EmpDistr μ q.1 (s97_pw Pw q.2 0)) := s97_emp_meas μ hN0 Pw 0
  have e2 : Measurable (fun q : EucConfig d N × Euc d => r2EmpDistr μ q.1 (s97_pw Pw q.2 (-(Real.pi / 2)))) := s97_emp_meas μ hN0 Pw _
  have e3 : ∀ (X : EucConfig d N) (ψ : SchwartzMap (Euc d) ℝ), sobolevNormE (m : ℝ) (fun x => ψ x) ≤ 1 →
      r2EmpDistr μ X (fun x => jbracket x ^ Pw * ψ x) = ∫ ξ, (s97_A ψ ξ * r2EmpDistr μ X (s97_pw Pw ξ 0) -
        s97_B ψ ξ * r2EmpDistr μ X (s97_pw Pw ξ (-(Real.pi / 2)))) :=
    fun X ψ _ => s97_emp_synth (by omega) hc hP hρ.prob hG hN0 X ψ
  have e4 := hCf (P N) Pw (fun X φ => r2EmpDistr μ X φ)
    (fun X ξ => r2EmpDistr μ X (s97_pw Pw ξ 0)) (fun X ξ => r2EmpDistr μ X (s97_pw Pw ξ (-(Real.pi / 2)))) e1 e2 e3
  have e5 := e4 (fun ξ => hbu_e ξ 0) (fun ξ => hbu_e ξ _)
  obtain ⟨Ge, Ge', hGe, hGe', hpe, hpe', hie, hie'⟩ := e5
  have f1 : Measurable (fun q : EucConfig d N × Euc d => r2CommDistr d s μ q.1 (s97_pw Pw q.2 0)) := s97_comm_meas s Pw 0 μ
  have f2 : Measurable (fun q : EucConfig d N × Euc d => r2CommDistr d s μ q.1 (s97_pw Pw q.2 (-(Real.pi / 2)))) := s97_comm_meas s Pw _ μ
  have f3 : ∀ (X : EucConfig d N) (ψ : SchwartzMap (Euc d) ℝ), sobolevNormE (m : ℝ) (fun x => ψ x) ≤ 1 →
      r2CommDistr d s μ X (fun x => jbracket x ^ Pw * ψ x) = ∫ ξ, (s97_A ψ ξ * r2CommDistr d s μ X (s97_pw Pw ξ 0) -
        s97_B ψ ξ * r2CommDistr d s μ X (s97_pw Pw ξ (-(Real.pi / 2)))) :=
    fun X ψ _ => s97_comm_synth (by omega) hs0 hs hc hP hρ.prob hρ.bdd hG X ψ
  have f4 := hCf (P N) Pw (fun X φ => r2CommDistr d s μ X φ)
    (fun X ξ => r2CommDistr d s μ X (s97_pw Pw ξ 0)) (fun X ξ => r2CommDistr d s μ X (s97_pw Pw ξ (-(Real.pi / 2)))) f1 f2 f3
  have f5 := f4 (fun ξ => hbu_c ξ 0) (fun ξ => hbu_c ξ _)
  obtain ⟨Gc, Gc', hGc, hGc', hpc, hpc', hic, hic'⟩ := f5
  have hCf0 : ENNReal.ofReal Cf ≤ ENNReal.ofReal (max Cf 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hfin : ENNReal.ofReal (2 + 2 * max Cf 0) = 2 + 2 * ENNReal.ofReal (max Cf 0) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp
  have key : ∀ (G1 G2 : EucConfig d N → ℝ≥0∞), Measurable G1 → Measurable G2 →
      ∫⁻ X, G1 X ∂(P N) ≤ ENNReal.ofReal Cf → ∫⁻ X, G2 X ∂(P N) ≤ ENNReal.ofReal Cf →
      ∫⁻ X, ((1 + G1 X) + (1 + G2 X)) ∂(P N) ≤ ENNReal.ofReal (2 + 2 * max Cf 0) := by
    intro G1 G2 h1 h2 i1 i2
    rw [lintegral_add_left (f := fun X => 1 + G1 X) (g := fun X => 1 + G2 X) (measurable_const.add h1), s97_lint_one_add (P N) h1, s97_lint_one_add (P N) h2, hfin]
    calc (1 + ∫⁻ X, G1 X ∂(P N)) + (1 + ∫⁻ X, G2 X ∂(P N))
        ≤ (1 + ENNReal.ofReal (max Cf 0)) + (1 + ENNReal.ofReal (max Cf 0)) := by
          gcongr
          · exact i1.trans hCf0
          · exact i2.trans hCf0
      _ = 2 + 2 * ENNReal.ofReal (max Cf 0) := by ring
  refine ⟨?_, ?_⟩
  · refine le_trans (lintegral_mono fun X => ?_) (key Ge Gc hGe hGc hie hic)
    exact add_le_add ((s97_rpow_le hr0 hrr').trans (add_le_add le_rfl (hpe X)))
      ((s97_rpow_le hr0 hrr').trans (add_le_add le_rfl (hpc X)))
  · refine le_trans (lintegral_mono fun X => ?_) (key Ge' Gc' hGe' hGc' hie' hic')
    exact add_le_add ((s97_rpow_le hr0 hrr').trans (add_le_add le_rfl (hpe' X)))
      ((s97_rpow_le hr0 hrr').trans (add_le_add le_rfl (hpc' X)))

end HRS.MS.R2Wfm
end
