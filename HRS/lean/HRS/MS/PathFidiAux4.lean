import HRS.MS.PathFidiAux3

/-!
# SA26 packet P4: the covariance replacement `E ∫_0^T ‖Σ_N - Σ̄_N‖_{S_1} ≤ C q_N 𝔴_N`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.PathFidi

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-! ### The time measure and product bounds -/

/-- the uniform probability measure on `[0,T]` -/
def sa26_μT (T : ℝ) : Measure ℝ := ENNReal.ofReal (1 / T) • volume.restrict (Set.Icc (0 : ℝ) T)

theorem sa26_μT_univ {T : ℝ} (hT : 0 < T) : sa26_μT T Set.univ = 1 := by
  simp only [sa26_μT, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc, sub_zero, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hT.ne']
  simp

theorem sa26_μT_prob {T : ℝ} (hT : 0 < T) : IsProbabilityMeasure (sa26_μT T) :=
  ⟨sa26_μT_univ hT⟩

theorem sa26_lintegral_μT {T : ℝ} (hT : 0 < T) (f : ℝ → ℝ≥0∞) :
    ∫⁻ r in Set.Icc (0 : ℝ) T, f r = ENNReal.ofReal T * ∫⁻ r, f r ∂(sa26_μT T) := by
  have h : ∫⁻ r, f r ∂(sa26_μT T) = ENNReal.ofReal (1 / T) * ∫⁻ r in Set.Icc (0 : ℝ) T, f r := by
    simp only [sa26_μT, lintegral_smul_measure, smul_eq_mul]
  rw [h, ← mul_assoc, ← ENNReal.ofReal_mul hT.le]
  have : T * (1 / T) = 1 := by field_simp
  rw [this, ENNReal.ofReal_one, one_mul]

theorem sa26_ae_μT {T : ℝ} {p : ℝ → Prop} (h : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), p r) :
    ∀ᵐ r ∂(sa26_μT T), p r := MeasureTheory.Measure.ae_smul_measure h _

theorem sa26_lintegral_prod_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T) (f : Ω × ℝ → ℝ≥0∞) (hf : Measurable f) (B : ℝ≥0∞)
    (h : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, f (ζ, r) ∂P ≤ B) :
    ∫⁻ q, f q ∂(P.prod (sa26_μT T)) ≤ B := by
  haveI := sa26_μT_prob hT
  rw [lintegral_prod_symm f hf.aemeasurable]
  have hae : ∀ᵐ r ∂(sa26_μT T), r ∈ Set.Icc (0 : ℝ) T :=
    sa26_ae_μT (ae_restrict_mem measurableSet_Icc)
  calc ∫⁻ r, ∫⁻ ζ, f (ζ, r) ∂P ∂(sa26_μT T) ≤ ∫⁻ _r, B ∂(sa26_μT T) :=
        lintegral_mono_ae (hae.mono fun r hr => h r hr)
    _ = B := by simp

theorem sa26_ae_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T) {A : Set (Ω × ℝ)} (hA : MeasurableSet A)
    (h : ∀ᵐ ζ ∂P, ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), (ζ, r) ∈ A) :
    ∀ᵐ q ∂(P.prod (sa26_μT T)), q ∈ A := by
  haveI := sa26_μT_prob hT
  have := (Measure.ae_prod_iff_ae_ae (μ := P) (ν := sa26_μT T) (p := fun q => q ∈ A) hA).2
    (by filter_upwards [h] with ζ hζ; exact sa26_ae_μT hζ)
  exact this

/-! ### The truncated gradients -/

section Cov

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ} {𝔈 : ℕ → ℝ}

/-- the gradient of the adjoint orbit, truncated to `r ∈ [0, t_a]` -/
def sa26_G (S : WholeMainData d) (N : ℕ) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (a : Fin p) :
    ℝ → Euc d → Euc d := fun r x =>
  if r ∈ Set.Icc (0 : ℝ) (ts a) then gradient (propagatorW (S.coeff N) r (ts a) (φ a)) x else 0

/-- the orbit itself, truncated (zero outside `[0, t_a]`) -/
def sa26_Uh (S : WholeMainData d) (N : ℕ) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (a : Fin p)
    (r : ℝ) : Euc d → ℝ :=
  if r ∈ Set.Icc (0 : ℝ) (ts a) then propagatorW (S.coeff N) r (ts a) (φ a) else fun _ => 0

theorem sa26_G_eq {N : ℕ} {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (a : Fin p) (r : ℝ) (x : Euc d) :
    sa26_G S N ts φ a r x = gradient (sa26_Uh S N ts φ a r) x := by
  unfold sa26_G sa26_Uh
  by_cases h : r ∈ Set.Icc (0 : ℝ) (ts a)
  · simp [h]
  · simp [h, gradient]

theorem sa26_G_meas {N : ℕ} {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (a : Fin p) (h0 : 0 ≤ ts a)
    (hex : ∃ f, IsClassicalAdjointW (S.coeff N) (ts a) (φ a) f) :
    Measurable fun q : ℝ × Euc d => sa26_G S N ts φ a q.1 q.2 := by
  have hf := (HRS.MS.Fcau.propagatorW_isClassical hex).isC12TestRd
  have hcont := HRS.MH.DualityRd.da3_continuous_gradient_clamp h0 hf
  have e : (fun q : ℝ × Euc d => sa26_G S N ts φ a q.1 q.2) = fun q => if q.1 ∈ Set.Icc (0 : ℝ) (ts a) then
      gradient (propagatorW (S.coeff N) (HRS.clampTI (ts a) q.1) (ts a) (φ a)) q.2 else 0 := by
    funext q
    unfold sa26_G
    by_cases h : q.1 ∈ Set.Icc (0 : ℝ) (ts a)
    · simp only [h, if_true, HRS.clampTI_of_mem h]
    · simp only [h, if_false]
  rw [e]
  exact Measurable.ite (measurableSet_Icc.preimage measurable_fst) hcont.measurable measurable_const

theorem sa26_Uh_props {N : ℕ} {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (a : Fin p) {Bd : ℝ}
    (hBd0 : 0 ≤ Bd)
    (hBd : ∀ r' ∈ Set.Icc (0 : ℝ) (ts a), ContDiff ℝ ((mStar d : ℕ) : WithTop ℕ∞)
      (propagatorW (S.coeff N) r' (ts a) (φ a)) ∧ ∀ l ≤ mStar d, ∀ x,
      ‖iteratedFDeriv ℝ l (propagatorW (S.coeff N) r' (ts a) (φ a)) x‖ ≤ Bd) (r' : ℝ) :
    ContDiff ℝ ((mStar d : ℕ) : WithTop ℕ∞) (sa26_Uh S N ts φ a r') ∧
      ∀ l ≤ mStar d, ∀ x, ‖iteratedFDeriv ℝ l (sa26_Uh S N ts φ a r') x‖ ≤ Bd := by
  unfold sa26_Uh
  by_cases h : r' ∈ Set.Icc (0 : ℝ) (ts a)
  · simpa only [h, if_true] using hBd r' h
  · simp only [h, if_false]
    refine ⟨contDiff_const, fun l hl x => ?_⟩
    simpa [iteratedFDeriv_zero_fun] using hBd0

end Cov


section Cov2

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ} {𝔈 : ℕ → ℝ}

theorem sa26_inner_euc (u v : Euc d) : inner ℝ u v = ∑ j, u j * v j := by
  simp [PiLp.inner_apply, mul_comm]

/-- the entries of `Σ_N - Σ̄_N` in terms of the pairing with the test `h_{ab}^r = ⟨G_a^r, G_b^r⟩` -/
theorem sa26_cov_entry {N : ℕ} (hN : 1 ≤ N) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ)
    {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) (a b : Fin p) (r' : ℝ)
    (hρ : HRS.Whole.IsProbDensity (S.ρ N (HRS.MP.RdRem.mrrClamp S.T r'))) :
    (killedCovMatrix (fun a => sa26_K S N ts φ X a) ts r' ζ -
      sa26SigBar ts (sa26_G S N ts φ) (fun r => S.ρ N (HRS.MP.RdRem.mrrClamp S.T r)) (2 * S.qN N) r') a b =
    if 0 ≤ r' ∧ r' < min (ts a) (ts b) then 2 * S.qN N *
      (HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal r') ζ))
          (fun x => inner ℝ (sa26_G S N ts φ a r' x) (sa26_G S N ts φ b r' x)) -
        HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T r')))
          (fun x => inner ℝ (sa26_G S N ts φ a r' x) (sa26_G S N ts φ b r' x))) else 0 := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hr : 0 ≤ r' ∧ r' < min (ts a) (ts b)
  · rw [if_pos hr]
    obtain ⟨hr0, hrm⟩ := hr
    have hra : r' ∈ Set.Icc (0 : ℝ) (ts a) := ⟨hr0, (lt_min_iff.1 hrm).1.le⟩
    have hrb : r' ∈ Set.Icc (0 : ℝ) (ts b) := ⟨hr0, (lt_min_iff.1 hrm).2.le⟩
    have hq : 0 ≤ S.invβ N := S.hinvβ N
    have hc2 : (S.sigma N * Real.sqrt (2 * S.invβ N) / N) ^ 2 = 2 * S.qN N / N := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), sa26_qN_eq]
      field_simp
    simp only [Matrix.sub_apply, killedCovMatrix, sa26SigBar, Matrix.of_apply, if_pos hrm,
      if_pos (And.intro hr0 hrm)]
    have hsum : ∑ k : Fin N × Fin d, sa26_K S N ts φ X a r' ζ k * sa26_K S N ts φ X b r' ζ k =
        (2 * S.qN N / N) * ∑ i, inner ℝ (sa26_G S N ts φ a r' (X (Real.toNNReal r') ζ i))
          (sa26_G S N ts φ b r' (X (Real.toNNReal r') ζ i)) := by
      rw [Fintype.sum_prod_type, ← hc2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sa26_inner_euc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [sa26_K, HRS.MH.DualityRd.truncGradIntegrand, if_pos hra, if_pos hrb, Pi.smul_apply,
        smul_eq_mul, sa26_G, sa26_f, HRS.Whole.gradComp]
      ring
    rw [hsum, HRS.Whole.pair_empirical hN]
    have hint : ∫ x, inner ℝ (sa26_G S N ts φ a r' x) (sa26_G S N ts φ b r' x) *
        S.ρ N (HRS.MP.RdRem.mrrClamp S.T r') x =
        HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T r')))
          (fun x => inner ℝ (sa26_G S N ts φ a r' x) (sa26_G S N ts φ b r' x)) := by
      unfold HRS.Whole.pair
      rw [HRS.MP.RdRem.mrr_integral_withDensityReal _ hρ.measurable hρ.nonneg]
      exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    rw [hint]
    field_simp
  · rw [if_neg hr]
    simp only [Matrix.sub_apply, killedCovMatrix, sa26SigBar, Matrix.of_apply, if_neg hr, sub_zero]
    by_cases hrm : r' < min (ts a) (ts b)
    · rw [if_pos hrm]
      have hr0 : r' < 0 := by
        by_contra h
        exact hr ⟨not_lt.1 h, hrm⟩
      refine Finset.sum_eq_zero fun k _ => ?_
      have : sa26_K S N ts φ X a r' ζ k = 0 := by
        have hn : r' ∉ Set.Icc (0 : ℝ) (ts a) := fun h => absurd h.1 (not_le.2 hr0)
        simp [sa26_K, HRS.MH.DualityRd.truncGradIntegrand, hn]
      rw [this, zero_mul]
    · rw [if_neg hrm]

/-- measurability in the time of the pairing against the density slices -/
theorem sa26_pair_rho_meas (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N)
    (g : ℝ → Euc d → ℝ) (hg : Measurable fun q : ℝ × Euc d => g q.1 q.2) :
    Measurable fun r' : ℝ => HRS.Whole.pair
      (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T r'))) (g r') := by
  have hρm := HRS.MP.RdRem.mrr_rho_meas hS hN
  have hprob : ∀ r' : ℝ, HRS.Whole.IsProbDensity (S.ρ N (HRS.MP.RdRem.mrrClamp S.T r')) := fun r' =>
    (hS.mean_field.solution N hN).density _ (HRS.MP.RdRem.mrrClamp_mem S.hT.le r')
  have e : (fun r' : ℝ => HRS.Whole.pair
      (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T r'))) (g r')) =
      fun r' => ∫ y, S.ρ N (HRS.MP.RdRem.mrrClamp S.T r') y * g r' y := by
    funext r'
    unfold HRS.Whole.pair
    exact HRS.MP.RdRem.mrr_integral_withDensityReal _ (hprob r').measurable (hprob r').nonneg _
  rw [e]
  have hsm : StronglyMeasurable fun q : ℝ × Euc d =>
      S.ρ N (HRS.MP.RdRem.mrrClamp S.T q.1) q.2 * g q.1 q.2 := (hρm.mul hg).stronglyMeasurable
  exact (hsm.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable

end Cov2


section Cov3

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ} {𝔈 : ℕ → ℝ}

/-- the test `h_{ab}^r = ⟨G_a^r, G_b^r⟩` -/
def sa26_hab (S : WholeMainData d) (N : ℕ) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (a b : Fin p)
    (r' : ℝ) : Euc d → ℝ := fun x => inner ℝ (sa26_G S N ts φ a r' x) (sa26_G S N ts φ b r' x)

/-- `⟨h_{ab}^r, μ_N^r - ρ_N^r⟩` as a function on `Ω × ℝ` -/
def sa26_Lab (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (N : ℕ) {p : ℕ} (ts : Fin p → ℝ)
    (φ : Fin p → Euc d → ℝ) (a b : Fin p) (q : (R N).Ω × ℝ) : ℝ :=
  HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T q.2)) q.1))
      (sa26_hab S N ts φ a b q.2) -
    HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T q.2)))
      (sa26_hab S N ts φ a b q.2)

theorem sa26_Lab_meas (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N) {p : ℕ}
    (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (hts : ∀ a, 0 ≤ ts a)
    (hex : ∀ a, ∃ f, IsClassicalAdjointW (S.coeff N) (ts a) (φ a) f)
    {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X)) (a b : Fin p) :
    Measurable (sa26_Lab S R N ts φ a b) := by
  have hN0 : 0 < N := by omega
  have hXq : Measurable fun q : (R N).Ω × ℝ => (R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T q.2)) q.1 :=
    (HRS.MP.RdRem.mrr_prog_meas ℱ (R N).X hprog S.hT.le).comp measurable_swap
  have hhab : Measurable fun q : ℝ × Euc d => sa26_hab S N ts φ a b q.1 q.2 :=
    (sa26_G_meas ts φ a (hts a) (hex a)).inner (sa26_G_meas ts φ b (hts b) (hex b))
  unfold sa26_Lab
  refine Measurable.sub ?_ ?_
  · have e : (fun q : (R N).Ω × ℝ => HRS.Whole.pair
        (HRS.Whole.empirical ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T q.2)) q.1))
        (sa26_hab S N ts φ a b q.2)) = fun q => (N : ℝ)⁻¹ * ∑ i,
          sa26_hab S N ts φ a b q.2 ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T q.2)) q.1 i) := by
      funext q
      exact HRS.Whole.pair_empirical hN0 _ _
    rw [e]
    refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    exact hhab.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp hXq))
  · exact (sa26_pair_rho_meas hS hN (fun r' x => sa26_hab S N ts φ a b r' x) hhab).comp measurable_snd


end Cov3

end HRS.MS.PathFidi
