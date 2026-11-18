import HRS.MS.SuppU1Aux7

/-!
# U1 aux 8: mollification by a bump on `E × E`: continuity, support, envelope, `L^r` convergence.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal ContDiff Convolution

namespace HRS.Whole.U1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- the mollifying bump of scale `1/(n+1)` on `E × E`. -/
def u1Bump (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) : ContDiffBump (0 : E × E) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity,
    one_div_lt_one_div_of_lt (by positivity) (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])⟩

/-- the mollification `ψ_n ⋆ f`. -/
def u1Mol (μ : Measure E) (n : ℕ) (f : E × E → ℝ) : E × E → ℝ :=
  fun p => ∫ t, (u1Bump E n).normed (μ.prod μ) t * f (p - t) ∂(μ.prod μ)

lemma u1Mol_eq_conv (n : ℕ) (f : E × E → ℝ) :
    u1Mol μ n f = ((u1Bump E n).normed (μ.prod μ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ.prod μ] f) := by
  funext p
  simp [u1Mol, convolution_def]

lemma u1Mol_continuous (n : ℕ) (f : E × E → ℝ) (hf : LocallyIntegrable f (μ.prod μ)) :
    Continuous (u1Mol μ n f) := by
  rw [u1Mol_eq_conv]
  have hcd : ContDiff ℝ ∞ (((u1Bump E n).normed (μ.prod μ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ.prod μ] f) :=
    (u1Bump E n).hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (u1Bump E n).contDiff_normed hf
  exact hcd.continuous

lemma u1Bump_supp (n : ℕ) (t : E × E) (ht : (u1Bump E n).normed (μ.prod μ) t ≠ 0) :
    ‖t.1‖ ≤ 1 / ((n : ℝ) + 1) ∧ ‖t.2‖ ≤ 1 / ((n : ℝ) + 1) := by
  have h1 : t ∈ Function.support ((u1Bump E n).normed (μ.prod μ)) := ht
  rw [ContDiffBump.support_normed_eq] at h1
  have h2 : ‖t‖ < 1 / ((n : ℝ) + 1) := by simpa [u1Bump] using h1
  exact ⟨(norm_fst_le t).trans h2.le, (norm_snd_le t).trans h2.le⟩

lemma u1Mol_support (n R : ℕ) (h : E → E → ℝ) (p : E × E) (hp : u1Mol μ n (u1Cut R h) p ≠ 0) :
    ‖p.1‖ ≤ R + 1 ∧ ‖p.2‖ ≤ R + 1 := by
  by_contra hcon
  apply hp
  unfold u1Mol
  have : ∀ t : E × E, (u1Bump E n).normed (μ.prod μ) t * u1Cut R h (p - t) = 0 := by
    intro t
    by_cases ht : (u1Bump E n).normed (μ.prod μ) t = 0
    · rw [ht, zero_mul]
    · obtain ⟨h1, h2⟩ := u1Bump_supp μ n t ht
      have hn : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have hnot : p - t ∉ closedBall (0:E) R ×ˢ closedBall (0:E) R := by
        intro hmem
        simp only [mem_prod, mem_closedBall, dist_zero_right, Prod.fst_sub, Prod.snd_sub] at hmem
        apply hcon
        constructor
        · calc ‖p.1‖ = ‖(p.1 - t.1) + t.1‖ := by rw [sub_add_cancel]
            _ ≤ ‖p.1 - t.1‖ + ‖t.1‖ := norm_add_le _ _
            _ ≤ R + 1 := by linarith [hmem.1]
        · calc ‖p.2‖ = ‖(p.2 - t.2) + t.2‖ := by rw [sub_add_cancel]
            _ ≤ ‖p.2 - t.2‖ + ‖t.2‖ := norm_add_le _ _
            _ ≤ R + 1 := by linarith [hmem.2]
      simp [u1Cut, indicator_of_notMem hnot]
  simp [this]

lemma u1_mol_envelope {s : ℝ} (hs : 0 ≤ s) (hsd : s < (Module.finrank ℝ E : ℝ)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (f : E × E → ℝ) (B : ℝ), 0 ≤ B →
      (∀ᵐ q ∂(μ.prod μ), |f q| ≤ B * u1Vs s ‖q.1 - q.2‖) → ∀ (n : ℕ) (p : E × E), p.1 ≠ p.2 →
      |u1Mol μ n f p| ≤ C₀ * B * u1Vs s ‖p.1 - p.2‖ := by
  obtain ⟨K, hK0, hK⟩ := u1_mollify_envelope μ hs hsd
  set mF : ℝ := (μ.prod μ).real (ball (0 : E × E) 1) with hmF
  have hmF0 : 0 < mF := ENNReal.toReal_pos (measure_ball_pos (μ.prod μ) 0 one_pos).ne'
    measure_ball_lt_top.ne
  set D : ℕ := Module.finrank ℝ E with hD
  refine ⟨2 ^ (D + D) * K ^ 2 / mF, by positivity, fun f B hB hf n p hp => ?_⟩
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hrIn : (u1Bump E n).rIn = ε / 2 := by simp only [u1Bump, hε]; field_simp
  have hball : (μ.prod μ).real (closedBall (0 : E × E) (ε / 2)) = (ε / 2) ^ (D + D) * mF := by
    rw [Measure.addHaar_real_closedBall _ _ (by positivity), Module.finrank_prod]
  set Cψ : ℝ := 1 / ((ε / 2) ^ (D + D) * mF) with hCψ
  have hCψ0 : 0 ≤ Cψ := by positivity
  have := hK ((u1Bump E n).normed (μ.prod μ)) f ε Cψ B hε0 hCψ0 hB
    (fun t => (u1Bump E n).nonneg_normed t) (u1Bump_supp μ n)
    (fun t => by
      have := (u1Bump E n).normed_le_div_measure_closedBall_rIn (μ.prod μ) t
      rw [hrIn, hball] at this; exact this) hf p hp
  refine this.trans (le_of_eq ?_)
  have hε' : ε ^ D ≠ 0 := by positivity
  have : Cψ * (K * ε ^ D) ^ 2 = 2 ^ (D + D) * K ^ 2 / mF := by
    rw [hCψ, div_pow, pow_add (ε : ℝ) D D, mul_pow, pow_add (2:ℝ) D D]
    field_simp
  rw [this]


lemma u1_mol_tendsto {s r M B C₀ : ℝ} (hs : 0 ≤ s) (hsd : s < (Module.finrank ℝ E : ℝ)) (hr : 0 < r)
    (hrs : r * s < (Module.finrank ℝ E : ℝ)) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (μ' : Measure E) [IsProbabilityMeasure μ'] (hle : μ' ≤ ENNReal.ofReal M • μ)
    (h : E → E → ℝ) (hm : Measurable fun p : E × E => h p.1 p.2)
    (hbd : ∀ x y, x ≠ y → |h x y| ≤ B * u1Vs s ‖x - y‖)
    (henv : ∀ (f : E × E → ℝ) (B : ℝ), 0 ≤ B →
      (∀ᵐ q ∂(μ.prod μ), |f q| ≤ B * u1Vs s ‖q.1 - q.2‖) → ∀ (n : ℕ) (p : E × E), p.1 ≠ p.2 →
      |u1Mol μ n f p| ≤ C₀ * B * u1Vs s ‖p.1 - p.2‖) (R : ℕ) :
    Tendsto (fun n : ℕ => eLpNorm (fun p : E × E => u1Mol μ n (u1Cut R h) p - u1Cut R h p)
      (ENNReal.ofReal r) (μ'.prod μ')) atTop (𝓝 0) := by
  have hd0 : (0:ℝ) < Module.finrank ℝ E := lt_of_le_of_lt hs hsd
  have hd : 1 ≤ Module.finrank ℝ E := by exact_mod_cast hd0
  have hμ'μ : μ' ≪ μ := Measure.absolutelyContinuous_of_le_smul hle
  have hPν : μ'.prod μ' ≪ μ.prod μ := Measure.AbsolutelyContinuous.prod hμ'μ hμ'μ
  have hoffν : ∀ᵐ q ∂(μ.prod μ), q.1 ≠ q.2 := u1_ae_offdiag μ hd
  have hoff : ∀ᵐ q ∂(μ'.prod μ'), q.1 ≠ q.2 := hPν.ae_le hoffν
  have hcutbd : ∀ q : E × E, q.1 ≠ q.2 → |u1Cut R h q| ≤ B * u1Vs s ‖q.1 - q.2‖ := by
    intro q hq
    by_cases hqS : q ∈ closedBall (0:E) R ×ˢ closedBall (0:E) R
    · simp only [u1Cut, indicator_of_mem hqS]; exact hbd q.1 q.2 hq
    · simp only [u1Cut, indicator_of_notMem hqS, abs_zero]
      exact mul_nonneg hB (by linarith [u1Vs_ge_one (s := s) (norm_nonneg (q.1 - q.2))])
  have hcutν : ∀ᵐ q ∂(μ.prod μ), |u1Cut R h q| ≤ B * u1Vs s ‖q.1 - q.2‖ :=
    hoffν.mono fun q hq => hcutbd q hq
  have hbdν : ∀ᵐ q ∂(μ.prod μ), |h q.1 q.2| ≤ B * u1Vs s ‖q.1 - q.2‖ :=
    hoffν.mono fun q hq => hbd q.1 q.2 hq
  have hcutm : Measurable (u1Cut R h) :=
    hm.indicator (measurableSet_closedBall.prod measurableSet_closedBall)
  have hloc : LocallyIntegrable (u1Cut R h) (μ.prod μ) :=
    (u1_integrable_cut μ hs hsd (fun p => h p.1 p.2) hm.aestronglyMeasurable B R hB
      (Nat.cast_nonneg R) hbdν).locallyIntegrable
  have hcont : ∀ n, Continuous (u1Mol μ n (u1Cut R h)) := fun n => u1Mol_continuous μ n _ hloc
  refine u1_tendsto_eLpNorm_of_dom (μ'.prod μ') hr (fun n => u1Mol μ n (u1Cut R h)) (u1Cut R h)
    (fun p => (C₀ + 1) * B * u1Vs s ‖p.1 - p.2‖) (fun n => (hcont n).aemeasurable)
    hcutm.aemeasurable ?_ (u1_bd_int μ hs hr hrs μ' hle (by positivity)) ?_
  · intro n
    filter_upwards [hoff] with q hq
    have h1 := henv (u1Cut R h) B hB hcutν n q hq
    have h2 := hcutbd q hq
    calc |u1Mol μ n (u1Cut R h) q - u1Cut R h q|
        ≤ |u1Mol μ n (u1Cut R h) q| + |u1Cut R h q| := abs_sub _ _
      _ ≤ (C₀ + 1) * B * u1Vs s ‖q.1 - q.2‖ := by nlinarith
  · have hφ : Tendsto (fun i : ℕ => (u1Bump E i).rOut) atTop (𝓝 0) := by
      simpa [u1Bump] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have h'φ : ∀ᶠ i : ℕ in atTop, (u1Bump E i).rOut ≤ 2 * (u1Bump E i).rIn := by
      refine Eventually.of_forall fun i => le_of_eq ?_
      simp only [u1Bump]; field_simp
    have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := μ.prod μ) (φ := u1Bump E) (l := atTop) (K := 2) hφ h'φ hloc
    filter_upwards [hPν.ae_le hae] with q hq
    exact hq.congr (fun i => (congrFun (u1Mol_eq_conv μ i (u1Cut R h)) q).symm)

end HRS.Whole.U1
