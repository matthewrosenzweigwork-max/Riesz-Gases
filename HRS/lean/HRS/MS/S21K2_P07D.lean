import HRS.MS.S21K2_P07C

/-!
# S21K2 P07D -- covariance matrices of the increments, heat function as a Gaussian integral, additivity lemma (R26-T3.P07)

`Sm r = ∫_{[r,H]} A` is the covariance of `Gamma r`; `Sm s - Sm t = ∫_s^t A` is PSD (a.e. PSD density), with trace
`Fc t - Fc s`, `Fc r = ∫_0^r tr A`.  A centered Gaussian measure is `gam` of its covariance; the heat function and
its second derivative (for `Phi in C_b^3`) are the Gaussian integrals `U`, `hh` of `P07C`.  Abstract lemma: an additive
defect that is `eta`-small relative to an additive nonnegative mass at small scales vanishes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace HRS.MS.R26T3

section Cov
variable {n : ℕ} {H : ℝ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ}

/-- the covariance matrix `r ↦ ∫_{[r,H]} A` -/
def s21k2_p07_Sm (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (H r : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∫ t in Icc r H, A t i j

theorem s21k2_p07_intIcc {f : ℝ → ℝ} {H : ℝ} (hf : IntegrableOn f (Icc 0 H)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ H) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact hf.mono_set (Icc_subset_Icc ha hb)

theorem s21k2_p07_Sm_sub (hA : ∀ i j, IntegrableOn (fun v => A v i j) (Icc 0 H)) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t ≤ H) (i j : Fin n) :
    (s21k2_p07_Sm A H s - s21k2_p07_Sm A H t) i j = ∫ r in s..t, A r i j := by
  have h1 : IntervalIntegrable (fun r => A r i j) volume s t := s21k2_p07_intIcc (hA i j) hs hst ht
  have h2 : IntervalIntegrable (fun r => A r i j) volume t H :=
    s21k2_p07_intIcc (hA i j) (hs.trans hst) ht le_rfl
  simp only [s21k2_p07_Sm, Matrix.sub_apply, Matrix.of_apply]
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hst.trans ht),
    ← intervalIntegral.integral_of_le ht, ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  ring

theorem s21k2_p07_D_psd (hA : ∀ i j, IntegrableOn (fun v => A v i j) (Icc 0 H))
    (hpos : ∀ᵐ v ∂volume.restrict (Icc 0 H), Matrix.PosSemidef (A v)) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t ≤ H) : (s21k2_p07_Sm A H s - s21k2_p07_Sm A H t).PosSemidef := by
  have hpos' : ∀ᵐ v ∂volume.restrict (Ioc s t), Matrix.PosSemidef (A v) :=
    ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs ht)) hpos
  have hint : ∀ i j, IntervalIntegrable (fun r => A r i j) volume s t := fun i j =>
    s21k2_p07_intIcc (hA i j) hs hst ht
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hD : ∀ i j, (s21k2_p07_Sm A H s - s21k2_p07_Sm A H t) i j = ∫ r in s..t, A r i j :=
    s21k2_p07_Sm_sub hA hs hst ht
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    rw [Matrix.conjTranspose_apply, star_trivial, hD, hD, intervalIntegral.integral_of_le hst,
      intervalIntegral.integral_of_le hst]
    refine integral_congr_ae ?_
    filter_upwards [hpos'] with v hv
    have := hv.isHermitian.apply i j
    simpa using this
  · have hx : star x = x := by ext i; simp
    rw [hx]
    have hq : ∀ r, x ⬝ᵥ (A r *ᵥ x) = ∑ i, ∑ j, x i * x j * A r i j := fun r => by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have key : x ⬝ᵥ ((s21k2_p07_Sm A H s - s21k2_p07_Sm A H t) *ᵥ x) =
        ∫ r in s..t, x ⬝ᵥ (A r *ᵥ x) := by
      simp_rw [hq]
      have hint2 : ∀ i, IntervalIntegrable (fun r => ∑ j, x i * x j * A r i j) volume s t := fun i => by
        have := IntervalIntegrable.sum (μ := volume) (a := s) (b := t) Finset.univ
          (f := fun j r => x i * x j * A r i j) (fun j _ => (hint i j).const_mul (x i * x j))
        convert this using 1
        ext r; simp
      rw [intervalIntegral.integral_finsetSum fun i _ => hint2 i]
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_finsetSum fun j _ => (hint i j).const_mul (x i * x j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [intervalIntegral.integral_const_mul, hD]
      ring
    rw [key, intervalIntegral.integral_of_le hst]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hpos'] with v hv
    have := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hv).2 x
    rwa [hx] at this


/-- trace of the increment as an interval integral of the trace density -/
theorem s21k2_p07_trace_sub (hA : ∀ i j, IntegrableOn (fun v => A v i j) (Icc 0 H)) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ H) :
    (s21k2_p07_Sm A H s - s21k2_p07_Sm A H t).trace =
      (∫ r in (0 : ℝ)..t, ∑ i, A r i i) - ∫ r in (0 : ℝ)..s, ∑ i, A r i i := by
  have hi : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H → IntervalIntegrable (fun r => ∑ i, A r i i) volume a b :=
    fun a b ha hab hb => by
      have := IntervalIntegrable.sum (μ := volume) (a := a) (b := b) Finset.univ
        (f := fun i r => A r i i) (fun i _ => s21k2_p07_intIcc (hA i i) ha hab hb)
      convert this using 1
      ext r; simp
  have e1 : (∫ r in (0 : ℝ)..t, ∑ i, A r i i) - ∫ r in (0 : ℝ)..s, ∑ i, A r i i =
      ∫ r in s..t, ∑ i, A r i i :=
    intervalIntegral.integral_interval_sub_left (hi 0 t le_rfl (hs.trans hst) ht)
      (hi 0 s le_rfl hs (hst.trans ht))
  have e2 : ∫ r in s..t, ∑ i, A r i i = ∑ i, ∫ r in s..t, A r i i :=
    intervalIntegral.integral_finsetSum fun i _ => s21k2_p07_intIcc (hA i i) hs hst ht
  have e3 : (s21k2_p07_Sm A H s - s21k2_p07_Sm A H t).trace = ∑ i, ∫ r in s..t, A r i i := by
    simp only [Matrix.trace, Matrix.diag_apply]
    exact Finset.sum_congr rfl fun i _ => s21k2_p07_Sm_sub hA hs hst ht i i
  exact e3.trans (e2.symm.trans e1.symm)

theorem s21k2_p07_psd_of_cov {ν : Measure (HRS.Euc n)} [IsGaussian ν] (hm : ∀ i, ∫ w, w i ∂ν = 0)
    {S : Matrix (Fin n) (Fin n) ℝ} (hc : ∀ i j, ∫ w, w i * w j ∂ν = S i j) : S.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    rw [Matrix.conjTranspose_apply, star_trivial, ← hc, ← hc]
    exact integral_congr_ae (Eventually.of_forall fun w => mul_comm _ _)
  · have h := covarianceBilin_self_nonneg (μ := ν) (WithLp.toLp 2 x : HRS.Euc n)
    rw [s21k2_p07_cov_form ν hm] at h
    have hx : star x = x := by ext i; simp
    rw [hx]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    simp_rw [hc] at h
    refine le_of_le_of_eq h (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    show x i * x j * S i j = _
    ring

theorem s21k2_p07_law_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → HRS.Euc n} (hG : AEStronglyMeasurable G P ∧ HRS.IsCenteredGaussian (HRS.law P G))
    {S : Matrix (Fin n) (Fin n) ℝ} (hc : ∀ i j, ∫ ω, G ω i * G ω j ∂P = S i j) :
    S.PosSemidef ∧ HRS.law P G = s21k2_p07_gam S := by
  have : IsGaussian (HRS.law P G) := hG.2.1
  have hm : ∀ i, ∫ w, w.ofLp i ∂(HRS.law P G) = 0 := fun i =>
    hG.2.2 (EuclideanSpace.proj i : HRS.Euc n →L[ℝ] ℝ)
  have hc' : ∀ i j, ∫ w, w.ofLp i * w.ofLp j ∂(HRS.law P G) = S i j := fun i j => by
    rw [← hc i j]
    exact integral_map hG.1.aemeasurable
      ((by fun_prop : Continuous fun w : HRS.Euc n => w.ofLp i * w.ofLp j).aestronglyMeasurable)
  have hpsd := s21k2_p07_psd_of_cov hm hc'
  exact ⟨hpsd, s21k2_p07_eq_gam _ hm hpsd hc'⟩

end Cov

section Heat
open HRS
variable {n : ℕ} {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma s21k2_p07_iter_shift {Φ : B → ℝ} (z : B) (j : ℕ) (x : B) :
    iteratedFDeriv ℝ j (fun y => Φ (y + z)) x = iteratedFDeriv ℝ j Φ (x + z) :=
  iteratedFDeriv_comp_add_right j z x

lemma s21k2_p07_le_sup {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {j : ℕ} (hj : j ≤ 3) (y : B) :
    ‖iteratedFDeriv ℝ j Φ y‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖ :=
  le_ciSup (f := fun z => ‖iteratedFDeriv ℝ j Φ z‖) (hΦ.2 j hj) y

/-- Differentiation under the integral sign for `u(y) = ∫ Φ(y + z) dγ(z)`. -/
theorem s21k2_p07_heat_derivs3 [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    (γ : Measure B) [IsProbabilityMeasure γ] {Φ : B → ℝ} (hΦ : MemCb 3 Φ) :
    ContDiff ℝ 3 (fun y => ∫ z, Φ (y + z) ∂γ) ∧ ∀ j ≤ 3, ∀ y,
      iteratedFDeriv ℝ j (fun y => ∫ z, Φ (y + z) ∂γ) y = ∫ z, iteratedFDeriv ℝ j Φ (y + z) ∂γ ∧
      ‖iteratedFDeriv ℝ j (fun y => ∫ z, Φ (y + z) ∂γ) y‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖ := by
  have hcd : ∀ z : B, ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun y => Φ (y + z)) := fun z => by
    have := hΦ.1.comp (contDiff_id.add (contDiff_const (c := z)))
    simpa [Function.comp_def] using this
  have key := contDiff_integral_dominated (B := B) γ (fun z y => Φ (y + z)) 3 (by norm_num) hcd
    (fun x => by
      refine Integrable.of_bound (C := ⨆ z, ‖iteratedFDeriv ℝ 0 Φ z‖) ?_ ?_
      · exact (hΦ.1.continuous.comp (by fun_prop : Continuous fun z : B => x + z)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun z => ?_
        have := s21k2_p07_le_sup hΦ (j := 0) (by norm_num) (x + z)
        simpa using this)
    (fun j hj x => by
      have h : (fun z => iteratedFDeriv ℝ j (fun y => Φ (y + z)) x) =
          fun z => iteratedFDeriv ℝ j Φ (x + z) := by
        funext z; exact s21k2_p07_iter_shift z j x
      rw [h]
      have := hΦ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)
      exact (this.comp (by fun_prop : Continuous fun z : B => x + z)).aestronglyMeasurable)
    (fun j _ => ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) (fun j _ _ => integrable_const _)
    (fun j _ hj3 z x => by
      rw [s21k2_p07_iter_shift z j x]; exact s21k2_p07_le_sup hΦ hj3 _)
  refine ⟨by simpa using key.1, fun j hj y => ?_⟩
  have e := key.2 j hj y
  have e' : iteratedFDeriv ℝ j (fun y => ∫ z, Φ (y + z) ∂γ) y = ∫ z, iteratedFDeriv ℝ j Φ (y + z) ∂γ := by
    rw [e]
    congr 1; funext z; exact s21k2_p07_iter_shift z j y
  refine ⟨e', ?_⟩
  rw [e']
  refine (norm_integral_le_of_norm_le_const (C := ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖)
    (Filter.Eventually.of_forall fun z => s21k2_p07_le_sup hΦ hj _)).trans ?_
  simp


theorem s21k2_p07_heat_U {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {G : Ω → HRS.Euc n} (hG : AEStronglyMeasurable G P) {Φ : HRS.Euc n → ℝ} (hΦc : Continuous Φ)
    (y : HRS.Euc n) : r26t3_heat P G Φ y = ∫ x, Φ (y + x) ∂(HRS.law P G) := by
  unfold r26t3_heat
  exact (integral_map hG.aemeasurable
    (hΦc.comp (continuous_const.add continuous_id)).aestronglyMeasurable).symm

theorem s21k2_p07_heat_hh {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {G : Ω → HRS.Euc n} (hG : AEStronglyMeasurable G P) {Φ : HRS.Euc n → ℝ} (hΦ : MemCb 3 Φ)
    (y : HRS.Euc n) (i j : Fin n) :
    iteratedFDeriv ℝ 2 (r26t3_heat P G Φ) y ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] =
      ∫ x, iteratedFDeriv ℝ 2 Φ (y + x) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]
        ∂(HRS.law P G) := by
  have : IsProbabilityMeasure (HRS.law P G) :=
    (Measure.isProbabilityMeasure_map_iff hG.aemeasurable).2 inferInstance
  have hheat : r26t3_heat P G Φ = fun y => ∫ z, Φ (y + z) ∂(HRS.law P G) :=
    funext fun y => s21k2_p07_heat_U P hG hΦ.1.continuous y
  rw [hheat, (s21k2_p07_heat_derivs3 (HRS.law P G) hΦ).2 2 (by norm_num) y |>.1]
  obtain ⟨M, hM⟩ := hΦ.2 2 (by norm_num)
  have hint : Integrable (fun x : HRS.Euc n => iteratedFDeriv ℝ 2 Φ (y + x)) (HRS.law P G) :=
    Integrable.of_bound (C := M)
      (((hΦ.1.continuous_iteratedFDeriv (m := 2) (by exact_mod_cast (by norm_num : 2 ≤ 3))).comp
        (continuous_const.add continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun x => hM ⟨y + x, rfl⟩)
  exact ContinuousMultilinearMap.integral_apply hint _

theorem s21k2_p07_additive_zero {s t : ℝ} (hst : s ≤ t) (Δ m : ℝ → ℝ → ℝ)
    (hadd : ∀ a b c, s ≤ a → a ≤ b → b ≤ c → c ≤ t → Δ a c = Δ a b + Δ b c)
    (hmadd : ∀ a b c, s ≤ a → a ≤ b → b ≤ c → c ≤ t → m a c = m a b + m b c)
    (hm0 : ∀ a b, s ≤ a → a ≤ b → b ≤ t → 0 ≤ m a b)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ a b, s ≤ a → a ≤ b → b ≤ t → b - a ≤ δ →
      |Δ a b| ≤ η * m a b) : Δ s t = 0 := by
  have hΔ0 : Δ s s = 0 := by have := hadd s s s le_rfl le_rfl le_rfl hst; linarith
  have hm00 : m s s = 0 := by have := hmadd s s s le_rfl le_rfl le_rfl hst; linarith
  have key : ∀ η : ℝ, 0 < η → |Δ s t| ≤ η * m s t := by
    intro η hη
    obtain ⟨δ, hδ, hsm⟩ := hsmall η hη
    obtain ⟨N, hN⟩ := exists_nat_gt ((t - s) / δ)
    set N' : ℕ := N + 1 with hN'
    have hNpos : (0 : ℝ) < N' := by positivity
    set h : ℝ := (t - s) / N' with hh
    have hh0 : 0 ≤ h := div_nonneg (by linarith) hNpos.le
    have hhδ : h ≤ δ := by
      rw [hh, div_le_iff₀ hNpos]
      have := (div_lt_iff₀ hδ).1 hN
      have h2 : (N : ℝ) ≤ N' := by simp [hN']
      nlinarith
    have hNh : (N' : ℝ) * h = t - s := by rw [hh]; field_simp
    have hp : ∀ k : ℕ, k ≤ N' → |Δ s (s + k * h)| ≤ η * m s (s + k * h) := by
      intro k
      induction k with
      | zero => intro _; simp [hΔ0, hm00]
      | succ k ih =>
        intro hk
        have hk' : k ≤ N' := by omega
        have a1 := ih hk'
        have hk1 : ((k + 1 : ℕ) : ℝ) * h ≤ t - s := by
          rw [← hNh]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh0
        have hk0 : (0 : ℝ) ≤ k * h := by positivity
        have e1 : s ≤ s + k * h := by linarith
        have e2 : s + k * h ≤ s + ((k + 1 : ℕ) : ℝ) * h := by
          push_cast; nlinarith
        have e3 : s + ((k + 1 : ℕ) : ℝ) * h ≤ t := by linarith
        have a2 := hsm (s + k * h) (s + ((k + 1 : ℕ) : ℝ) * h) e1 e2 e3 (by push_cast; nlinarith)
        rw [hadd s (s + k * h) (s + ((k + 1 : ℕ) : ℝ) * h) le_rfl e1 e2 e3,
          hmadd s (s + k * h) (s + ((k + 1 : ℕ) : ℝ) * h) le_rfl e1 e2 e3]
        calc _ ≤ |Δ s (s + k * h)| + |Δ (s + k * h) (s + ((k + 1 : ℕ) : ℝ) * h)| := abs_add_le _ _
          _ ≤ η * m s (s + k * h) + η * m (s + k * h) (s + ((k + 1 : ℕ) : ℝ) * h) := add_le_add a1 a2
          _ = _ := by ring
    have := hp N' le_rfl
    have e : s + (N' : ℝ) * h = t := by rw [hNh]; ring
    rwa [e] at this
  by_contra hne
  have hpos : 0 < |Δ s t| := abs_pos.2 hne
  have hm := hm0 s t le_rfl hst le_rfl
  have := key (|Δ s t| / (m s t + 1)) (by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
  nlinarith

end Heat
end HRS.MS.R26T3
