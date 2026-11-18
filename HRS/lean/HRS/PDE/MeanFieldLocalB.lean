import HRS.PDE.MeanFieldLocal
import HRS.PDE.Galerkin
import HRS.PDE.EnergyTorusDeriv
import HRS.PDE.MeanFieldSemigroup

/-!
# Mean-field equation: local existence and uniqueness in `H^K` (package MF-01, P5b)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE
namespace MFLocal

variable {d : ℕ}

/-! ### Elementary facts on `H^m` -/

theorem eq_zero_of_hsNorm_eq_zero {m : ℝ} {c : Coeff d} (hc : MemHs m c) (h : hsNorm m c = 0) :
    c = 0 := by
  funext k
  have h1 := norm_coeff_mul_sqrt_le m hc k
  have hw : 0 < Real.sqrt (sobWeight m k) := Real.sqrt_pos.mpr (sobWeight_pos m k)
  rw [h] at h1
  have : ‖c k‖ ≤ 0 := by
    by_contra hne
    push Not at hne
    have := mul_pos hne hw
    linarith
  simpa using this

theorem hsNorm_sub_comm (m : ℝ) (f g : Coeff d) : hsNorm m (f - g) = hsNorm m (g - f) := by
  unfold hsNorm hsNormSq
  simp only [Pi.sub_apply, norm_sub_rev (f _)]

theorem abs_hsNorm_sub_le {m : ℝ} {f g : Coeff d} (hf : MemHs m f) (hg : MemHs m g) :
    |hsNorm m f - hsNorm m g| ≤ hsNorm m (f - g) := by
  have h1 := memHs_add_le m hg (memHs_sub_aux hf hg)
  have h2 := memHs_add_le m hf (memHs_sub_aux hg hf)
  have e1 : g + (f - g) = f := by abel
  have e2 : f + (g - f) = g := by abel
  rw [e1] at h1
  rw [e2, hsNorm_sub_comm m g f] at h2
  rw [abs_le]
  constructor <;> linarith [h2.2, h1.2]

theorem continuousOn_hsNorm {m : ℝ} {F : ℝ → Coeff d} {S : Set ℝ} (h : ContinuousInHsOn m F S) :
    ContinuousOn (fun t => hsNorm m (F t)) S := by
  intro τ0 hτ0
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall fun σ hσ => ?_) (h.2 τ0 hτ0)
  rw [Real.norm_eq_abs]
  exact abs_hsNorm_sub_le (h.1 σ hσ) (h.1 τ0 hτ0)

theorem exists_bound_hsNorm {m : ℝ} {F : ℝ → Coeff d} {T : ℝ} (h : ContinuousInHsOn m F (Set.Icc 0 T)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc 0 T, hsNorm m (F t) ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_hsNorm h)
  exact ⟨|B|, abs_nonneg _, fun t ht =>
    (Real.le_norm_self _).trans ((hB t ht).trans (le_abs_self B))⟩

/-- Coordinatewise limits of a bounded sequence in `H^m` stay in the ball. -/
theorem limit_bound {m B : ℝ} {c : ℕ → Coeff d} {L : Coeff d}
    (hlim : ∀ k, Tendsto (fun n => c n k) atTop (𝓝 (L k))) (hmem : ∀ n, MemHs m (c n))
    (hb : ∀ n, hsNorm m (c n) ≤ B) : MemHs m L ∧ hsNorm m L ≤ B := by
  have hB : 0 ≤ B := (hsNorm_nonneg m (c 0)).trans (hb 0)
  obtain ⟨h1, h2⟩ : MemHs m L ∧ hsNormSq m L ≤ B ^ 2 := by
    refine memHs_of_sum_le fun S => ?_
    have ht : Tendsto (fun n => ∑ k ∈ S, sobWeight m k * ‖c n k‖ ^ 2) atTop
        (𝓝 (∑ k ∈ S, sobWeight m k * ‖L k‖ ^ 2)) := by
      refine tendsto_finsetSum _ fun k _ => ?_
      exact ((hlim k).norm.pow 2).const_mul _
    refine le_of_tendsto' ht fun n => (sum_le_hsNormSq (hmem n) S).trans ?_
    have := hb n
    calc hsNormSq m (c n) = hsNorm m (c n) ^ 2 := (Real.sq_sqrt (hsNormSq_nonneg _ _)).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (hsNorm_nonneg _ _) this 2
  exact ⟨h1, Real.sqrt_le_iff.mpr ⟨hB, h2⟩⟩

/-- A sequence in `H^m` which is Cauchy in `H^m` with an explicit modulus has an `H^m` limit
(which is also the coordinatewise limit). -/
theorem cauchy_limit {m : ℝ} (c : ℕ → Coeff d) (δ : ℕ → ℝ) (hmem : ∀ n, MemHs m (c n))
    (hδ : Tendsto δ atTop (𝓝 0)) (hc : ∀ n p, n ≤ p → hsNorm m (c p - c n) ≤ δ n) :
    ∃ L : Coeff d, MemHs m L ∧ (∀ k, Tendsto (fun n => c n k) atTop (𝓝 (L k))) ∧
      ∀ n, hsNorm m (L - c n) ≤ δ n := by
  have hδ0 : ∀ n, 0 ≤ δ n := fun n => (hsNorm_nonneg m _).trans (by simpa using hc n n le_rfl)
  have hcoord : ∀ k, ∃ l, Tendsto (fun n => c n k) atTop (𝓝 l) := by
    intro k
    have hw : 0 < Real.sqrt (sobWeight m k) := Real.sqrt_pos.mpr (sobWeight_pos m k)
    have hbd : ∀ n p, n ≤ p → ‖c p k - c n k‖ ≤ δ n / Real.sqrt (sobWeight m k) := by
      intro n p hnp
      rw [le_div_iff₀ hw]
      exact (norm_coeff_mul_sqrt_le m (memHs_sub_aux (hmem p) (hmem n)) k).trans (hc n p hnp)
    refine cauchySeq_tendsto_of_complete (cauchySeq_of_le_tendsto_0
      (fun N => 2 * (δ N / Real.sqrt (sobWeight m k))) (fun n p N hn hp => ?_) ?_)
    · rw [dist_eq_norm]
      have h1 := hbd N n hn
      have h2 := hbd N p hp
      calc ‖c n k - c p k‖ = ‖(c n k - c N k) - (c p k - c N k)‖ := by ring_nf
        _ ≤ ‖c n k - c N k‖ + ‖c p k - c N k‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    · simpa using (hδ.div_const (Real.sqrt (sobWeight m k))).const_mul 2
  choose L hL using hcoord
  have hsub : ∀ n, MemHs m (L - c n) ∧ hsNorm m (L - c n) ≤ δ n := by
    intro n
    refine limit_bound (c := fun j => c (n + j) - c n) (fun k => ?_) (fun j => ?_) (fun j => ?_)
    · have := ((hL k).comp (tendsto_add_atTop_nat n)).sub_const (c n k)
      simpa [add_comm] using this
    · exact memHs_sub_aux (hmem _) (hmem _)
    · exact hc n (n + j) (Nat.le_add_right n j)
  refine ⟨L, ?_, hL, fun n => (hsub n).2⟩
  have := memHs_add_le m (hsub 0).1 (hmem 0)
  simpa using this.1

/-! ### Continuity from modewise continuity and uniform tails -/

theorem hsNorm_neg' (m : ℝ) (g : Coeff d) : hsNorm m (-g) = hsNorm m g := by
  unfold hsNorm hsNormSq; simp

theorem hsNorm_sub_le {m : ℝ} {f g : Coeff d} (hf : MemHs m f) (hg : MemHs m g) :
    hsNorm m (f - g) ≤ hsNorm m f + hsNorm m g := by
  rw [sub_eq_add_neg]
  have := (memHs_add_le m hf (memHs_neg hg)).2
  rwa [hsNorm_neg'] at this

theorem memHs_truncCoeff (m : ℝ) (n : ℕ) (x : Coeff d) : MemHs m (truncCoeff n x) := by
  refine summable_of_ne_finset_zero (s := boxFinset d n) fun k hk => ?_
  have : ¬ InBox n k := fun h => hk (mem_boxFinset.mpr h)
  simp [truncCoeff, this]

theorem hsNormSq_truncCoeff (m : ℝ) (n : ℕ) (x : Coeff d) :
    hsNormSq m (truncCoeff n x) = ∑ k ∈ boxFinset d n, sobWeight m k * ‖x k‖ ^ 2 := by
  unfold hsNormSq
  rw [tsum_eq_sum (s := boxFinset d n)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    simp [truncCoeff, mem_boxFinset.mp hk]
  · intro k hk
    have : ¬ InBox n k := fun h => hk (mem_boxFinset.mpr h)
    simp [truncCoeff, this]

theorem contInHs_of_trunc {m : ℝ} {c : ℝ → Coeff d} {S : Set ℝ} (hmem : ∀ τ ∈ S, MemHs m (c τ))
    (hmode : ∀ k, ContinuousOn (fun τ => c τ k) S)
    (htail : ∀ ε > 0, ∃ n : ℕ, ∀ τ ∈ S, hsNorm m (c τ - truncCoeff n (c τ)) ≤ ε) :
    ContinuousInHsOn m c S := by
  refine ⟨hmem, fun τ0 hτ0 => ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := htail (ε / 4) (by positivity)
  -- finite part
  have hfin : Tendsto (fun τ => ∑ k ∈ boxFinset d n, sobWeight m k * ‖c τ k - c τ0 k‖ ^ 2)
      (𝓝[S] τ0) (𝓝 0) := by
    have : (0 : ℝ) = ∑ k ∈ boxFinset d n, sobWeight m k * ‖c τ0 k - c τ0 k‖ ^ 2 := by simp
    rw [this]
    refine tendsto_finsetSum _ fun k _ => ?_
    refine Tendsto.const_mul _ (Tendsto.pow (Tendsto.norm (Tendsto.sub (hmode k τ0 hτ0) tendsto_const_nhds)) 2)
  have hev := hfin.eventually (gt_mem_nhds (show (0 : ℝ) < (ε / 2) ^ 2 by positivity))
  filter_upwards [hev, self_mem_nhdsWithin] with τ hτ hτS
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNorm_nonneg _ _)]
  set a : Coeff d := c τ - c τ0 with ha
  have hdec : a = truncCoeff n a + ((c τ - truncCoeff n (c τ)) - (c τ0 - truncCoeff n (c τ0))) := by
    funext k
    by_cases hk : InBox n k <;> simp [ha, truncCoeff, hk]
  have h1 : hsNorm m (truncCoeff n a) < ε / 2 := by
    unfold hsNorm
    rw [hsNormSq_truncCoeff]
    refine Real.sqrt_lt' (by positivity) |>.mpr ?_
    simpa [ha] using hτ
  have hm1 : MemHs m (c τ - truncCoeff n (c τ)) := memHs_sub_aux (hmem τ hτS) (memHs_truncCoeff m n _)
  have hm2 : MemHs m (c τ0 - truncCoeff n (c τ0)) :=
    memHs_sub_aux (hmem τ0 hτ0) (memHs_truncCoeff m n _)
  have h2 := hsNorm_sub_le hm1 hm2
  have h3 := hn τ hτS
  have h4 := hn τ0 hτ0
  have h5 := (memHs_add_le m (memHs_truncCoeff m n a) (memHs_sub_aux hm1 hm2)).2
  rw [← hdec] at h5
  linarith

/-! ### The Duhamel operator -/

/-- The heat semigroup on coefficients. -/
def heatC (ν τ : ℝ) (c : Coeff d) : Coeff d := fun k => (heatMult ν τ k : ℂ) * c k

/-- The Duhamel integral `∫₀ᵗ e^{(t-σ)νΔ} f(σ) dσ`, mode by mode. -/
def duh (ν : ℝ) (f : ℝ → Coeff d) (t : ℝ) : Coeff d :=
  fun k => ∫ σ in (0 : ℝ)..t, (heatMult ν (t - σ) k : ℂ) * f σ k

/-- The kernel integral `∫₀ᵗ (1 + (ντ)^{-γ}) dτ`. -/
def Eker (ν γ t : ℝ) : ℝ := t + ν ^ (-γ) * t ^ (1 - γ) / (1 - γ)

theorem kappa_integral (ν : ℝ) (hν : 0 < ν) (γ : ℝ) (hγ1 : γ < 1) (t : ℝ)
    (ht : 0 ≤ t) :
    IntervalIntegrable (fun σ => 1 + (ν * (t - σ)) ^ (-γ)) volume 0 t ∧
      ∫ σ in (0 : ℝ)..t, (1 + (ν * (t - σ)) ^ (-γ)) = Eker ν γ t := by
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-γ)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h2 : IntervalIntegrable (fun x : ℝ => (t - x) ^ (-γ)) volume 0 t := by
    have := (h1.comp_sub_left t).symm
    simpa using this
  have hcongr : ∀ σ ∈ Set.uIcc 0 t, (ν * (t - σ)) ^ (-γ) = ν ^ (-γ) * (t - σ) ^ (-γ) := by
    intro σ hσ
    rw [Set.uIcc_of_le ht] at hσ
    exact Real.mul_rpow hν.le (by linarith [hσ.2])
  have h3 : IntervalIntegrable (fun σ => (ν * (t - σ)) ^ (-γ)) volume 0 t := by
    refine (h2.const_mul (ν ^ (-γ))).congr ?_
    intro σ hσ
    rw [Set.uIoc_of_le ht] at hσ
    exact (hcongr σ (by rw [Set.uIcc_of_le ht]; exact ⟨hσ.1.le, hσ.2⟩)).symm
  refine ⟨intervalIntegrable_const.add h3, ?_⟩
  rw [intervalIntegral.integral_add intervalIntegrable_const h3]
  have h4 : ∫ σ in (0 : ℝ)..t, (ν * (t - σ)) ^ (-γ) = ∫ σ in (0 : ℝ)..t, ν ^ (-γ) * (t - σ) ^ (-γ) :=
    intervalIntegral.integral_congr hcongr
  rw [h4, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left
    (fun x : ℝ => x ^ (-γ)) t, sub_self, sub_zero, integral_rpow (Or.inl (by linarith))]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  unfold Eker
  rw [Real.zero_rpow (by linarith : -γ + 1 ≠ 0)]
  have : -γ + 1 = 1 - γ := by ring
  rw [this]
  ring

theorem Eker_nonneg (ν γ t : ℝ) (hν : 0 < ν) (hγ1 : γ < 1) (ht : 0 ≤ t) : 0 ≤ Eker ν γ t := by
  unfold Eker
  have : 0 < 1 - γ := by linarith
  positivity

theorem Eker_mono (ν γ : ℝ) (hν : 0 < ν) (hγ1 : γ < 1) {t T : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) : Eker ν γ t ≤ Eker ν γ T := by
  unfold Eker
  have h1 : 0 < 1 - γ := by linarith
  have h2 : t ^ (1 - γ) ≤ T ^ (1 - γ) := Real.rpow_le_rpow ht htT h1.le
  have h3 : 0 < ν ^ (-γ) := Real.rpow_pos_of_pos hν _
  have : ν ^ (-γ) * t ^ (1 - γ) / (1 - γ) ≤ ν ^ (-γ) * T ^ (1 - γ) / (1 - γ) := by
    apply div_le_div_of_nonneg_right _ h1.le
    exact mul_le_mul_of_nonneg_left h2 h3.le
  linarith

theorem Eker_tendsto (ν γ : ℝ) (hγ1 : γ < 1) :
    Tendsto (Eker ν γ) (𝓝 0) (𝓝 0) := by
  unfold Eker
  have h1 : 0 < 1 - γ := by linarith
  have h2 : ContinuousAt (fun t : ℝ => t ^ (1 - γ)) 0 := Real.continuousAt_rpow_const 0 _ (Or.inr h1.le)
  have h3 : Tendsto (fun t : ℝ => t + ν ^ (-γ) * t ^ (1 - γ) / (1 - γ)) (𝓝 0)
      (𝓝 (0 + ν ^ (-γ) * (0 : ℝ) ^ (1 - γ) / (1 - γ))) :=
    (continuousAt_id.add ((continuousAt_const.mul h2).div_const _)).tendsto
  rwa [Real.zero_rpow h1.ne', mul_zero, zero_div, add_zero] at h3

/-- The ambient measurability fact: `σ ↦ ‖F σ‖_{H^m}` is a.e.-measurable on a measurable set
when all modes are. -/
theorem aemeasurable_hsNorm {m : ℝ} (F : ℝ → Coeff d) {S : Set ℝ} (hS : MeasurableSet S)
    (hmem : ∀ σ ∈ S, MemHs m (F σ)) (hmode : ∀ k, AEMeasurable (fun σ => F σ k) (volume.restrict S)) :
    AEMeasurable (fun σ => hsNorm m (F σ)) (volume.restrict S) := by
  set G : ℝ → ℝ≥0∞ := fun σ => ∑' k, ENNReal.ofReal (sobWeight m k * ‖F σ k‖ ^ 2) with hG
  have hGm : AEMeasurable G (volume.restrict S) := by
    refine AEMeasurable.tsum fun k => ?_
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (((hmode k).norm.pow_const 2).const_mul _)
  have hH : AEMeasurable (fun σ => Real.sqrt (G σ).toReal) (volume.restrict S) :=
    (hGm.ennreal_toReal).sqrt
  refine hH.congr ((ae_restrict_iff' hS).mpr (Eventually.of_forall fun σ hσ => ?_))
  have hs := hmem σ hσ
  simp only [hG]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (sobWeight_pos m k).le (sq_nonneg _)) hs,
    ENNReal.toReal_ofReal (tsum_nonneg fun k => mul_nonneg (sobWeight_pos m k).le (sq_nonneg _))]
  rfl

/-- Pointwise a.e. in `σ`: the endpoint `σ = t` is a null set. -/
theorem ae_ne_volume (t : ℝ) : ∀ᵐ σ : ℝ ∂volume, σ ≠ t := Measure.ae_ne volume t

theorem continuousOn_mode_mul_heat {a : ℝ} {f : ℝ → Coeff d} {T : ℝ}
    (hf : ContinuousInHsOn a f (Set.Icc 0 T)) (ν t : ℝ) (k : Lattice d) :
    ContinuousOn (fun σ => (heatMult ν (t - σ) k : ℂ) * f σ k) (Set.Icc 0 T) := by
  refine ContinuousOn.mul ?_ (continuousOn_mode hf k)
  unfold heatMult
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul (continuous_const.sub continuous_id)))).continuousOn

/-- **Duhamel estimate** (Minkowski plus heat smoothing). -/
theorem duh_bound (ν : ℝ) (hν : 0 < ν) (a b m : ℝ) (hb : 0 ≤ b) (hb2 : b < 2) (hm : a + b = m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → Coeff d) (T : ℝ), ContinuousInHsOn a f (Set.Icc 0 T) →
      ∀ t ∈ Set.Icc 0 T, MemHs m (duh ν f t) ∧
        hsNorm m (duh ν f t) ≤
          ∫ σ in (0 : ℝ)..t, C * (1 + (ν * (t - σ)) ^ (-(b / 2))) * hsNorm a (f σ) := by
  obtain ⟨C, hC0, hC⟩ := heatMult_smoothing (d := d) ν hν a b hb
  refine ⟨C, hC0, fun f T hf t ht => ?_⟩
  subst hm
  have hsubT : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  have hγ1 : b / 2 < 1 := by linarith
  obtain ⟨hκint, -⟩ := kappa_integral ν hν (b / 2) hγ1 t ht.1
  -- the modified family
  set F' : ℝ → Coeff d := fun σ => if σ < t then heatC ν (t - σ) (f σ) else 0 with hF'
  have hF'k : ∀ k σ, F' σ k = if σ < t then (heatMult ν (t - σ) k : ℂ) * f σ k else 0 := by
    intro k σ
    by_cases h : σ < t <;> simp [hF', h, heatC]
  have hmodeF : ∀ k, IntervalIntegrable (fun σ => F' σ k) volume 0 t := by
    intro k
    have h1 : IntervalIntegrable (fun σ => (heatMult ν (t - σ) k : ℂ) * f σ k) volume 0 t := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le ht.1]
      exact (continuousOn_mode_mul_heat hf ν t k).mono hsubT
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1] at h1 ⊢
    refine h1.congr_fun_ae ((ae_restrict_iff' measurableSet_Ioc).mpr
      ((ae_ne_volume t).mono fun σ hσ hmem => ?_))
    have hlt : σ < t := lt_of_le_of_ne hmem.2 hσ
    simp [hF'k, hlt]
  have hintk : ∀ k, ∫ σ in (0 : ℝ)..t, F' σ k = duh ν f t k := by
    intro k
    unfold duh
    refine intervalIntegral.integral_congr_ae ((ae_ne_volume t).mono fun σ hσ hmem => ?_)
    have hlt : σ < t := by
      rw [Set.uIoc_of_le ht.1] at hmem
      exact lt_of_le_of_ne hmem.2 hσ
    simp [hF'k, hlt]
  have hmemF : ∀ σ ∈ Set.Icc 0 t, MemHs (a + b) (F' σ) := by
    intro σ hσ
    by_cases hlt : σ < t
    · have := (hC (t - σ) (by linarith) (f σ) (hf.1 σ (hsubT hσ))).1.1
      simp only [hF', hlt, ite_true]
      exact this
    · simpa [hF', hlt] using memHs_zero_coeff (a + b)
  have hnormF : ∀ σ ∈ Set.Icc 0 t, hsNorm (a + b) (F' σ) ≤
      C * (1 + (ν * (t - σ)) ^ (-(b / 2))) * hsNorm a (f σ) := by
    intro σ hσ
    by_cases hlt : σ < t
    · have := (hC (t - σ) (by linarith) (f σ) (hf.1 σ (hsubT hσ))).1.2
      simp only [hF', hlt, ite_true]
      exact le_trans this (le_of_eq (by ring))
    · simp only [hF', hlt, ite_false]
      rw [hsNorm_zero_coeff]
      have : 0 ≤ (ν * (t - σ)) ^ (-(b / 2)) :=
        Real.rpow_nonneg (mul_nonneg hν.le (by linarith [hσ.2])) _
      exact mul_nonneg (mul_nonneg hC0 (by linarith)) (hsNorm_nonneg _ _)
  have hBd : IntervalIntegrable
      (fun σ => C * (1 + (ν * (t - σ)) ^ (-(b / 2))) * hsNorm a (f σ)) volume 0 t := by
    have h1 := (hκint.const_mul C).mul_continuousOn (g := fun σ => hsNorm a (f σ))
      (by rw [Set.uIcc_of_le ht.1]; exact (continuousOn_hsNorm hf).mono hsubT)
    exact h1
  have hnormInt : IntervalIntegrable (fun σ => hsNorm (a + b) (F' σ)) volume 0 t := by
    refine hBd.mono_fun' ?_ ?_
    · rw [Set.uIoc_of_le ht.1]
      refine (aemeasurable_hsNorm F' measurableSet_Ioc (fun σ hσ => hmemF σ ⟨hσ.1.le, hσ.2⟩) fun k => ?_).aestronglyMeasurable
      exact (hmodeF k).1.aemeasurable.mono_set (le_refl _) |>.mono_measure le_rfl
    · rw [Set.uIoc_of_le ht.1]
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun σ hσ => ?_)
      beta_reduce
      rw [Real.norm_eq_abs, abs_of_nonneg (hsNorm_nonneg _ _)]
      exact hnormF σ ⟨hσ.1.le, hσ.2⟩
  obtain ⟨h1, h2⟩ := hsNorm_intervalIntegral_le (a + b) F' ht.1 hmemF hmodeF hnormInt
  have hfun : (fun k => ∫ σ in (0 : ℝ)..t, F' σ k) = duh ν f t := funext hintk
  rw [hfun] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  exact intervalIntegral.integral_mono_on ht.1 hnormInt hBd hnormF

theorem duh_bound_const (ν : ℝ) (hν : 0 < ν) (a b m : ℝ) (hb : 0 ≤ b) (hb2 : b < 2) (hm : a + b = m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → Coeff d) (T : ℝ), ContinuousInHsOn a f (Set.Icc 0 T) →
      ∀ B : ℝ, (∀ σ ∈ Set.Icc 0 T, hsNorm a (f σ) ≤ B) →
      ∀ t ∈ Set.Icc 0 T, MemHs m (duh ν f t) ∧
        hsNorm m (duh ν f t) ≤ C * B * Eker ν (b / 2) t := by
  obtain ⟨C, hC0, hC⟩ := duh_bound (d := d) ν hν a b m hb hb2 hm
  refine ⟨C, hC0, fun f T hf B hB t ht => ?_⟩
  obtain ⟨h1, h2⟩ := hC f T hf t ht
  refine ⟨h1, h2.trans ?_⟩
  have hγ1 : b / 2 < 1 := by linarith
  obtain ⟨hκint, hκ⟩ := kappa_integral ν hν (b / 2) hγ1 t ht.1
  have hsubT : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  have hBd : IntervalIntegrable
      (fun σ => C * (1 + (ν * (t - σ)) ^ (-(b / 2))) * hsNorm a (f σ)) volume 0 t :=
    (hκint.const_mul C).mul_continuousOn (g := fun σ => hsNorm a (f σ))
      (by rw [Set.uIcc_of_le ht.1]; exact (continuousOn_hsNorm hf).mono hsubT)
  have hB' : IntervalIntegrable (fun σ => C * (1 + (ν * (t - σ)) ^ (-(b / 2))) * B) volume 0 t :=
    (hκint.const_mul C).mul_const B
  calc ∫ σ in (0 : ℝ)..t, C * (1 + (ν * (t - σ)) ^ (-(b / 2))) * hsNorm a (f σ)
      ≤ ∫ σ in (0 : ℝ)..t, C * (1 + (ν * (t - σ)) ^ (-(b / 2))) * B := by
        refine intervalIntegral.integral_mono_on ht.1 hBd hB' fun σ hσ => ?_
        have : 0 ≤ (ν * (t - σ)) ^ (-(b / 2)) :=
          Real.rpow_nonneg (mul_nonneg hν.le (by linarith [hσ.2])) _
        exact mul_le_mul_of_nonneg_left (hB σ (hsubT hσ)) (mul_nonneg hC0 (by linarith))
    _ = C * B * Eker ν (b / 2) t := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, hκ]; ring

/-! ### Continuity of the Duhamel integral and of the free evolution -/

theorem continuousOn_duh_mode (ν : ℝ) {a : ℝ} {f : ℝ → Coeff d} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousInHsOn a f (Set.Icc 0 T)) (k : Lattice d) :
    ContinuousOn (fun t => duh ν f t k) (Set.Icc 0 T) := by
  have hg : IntegrableOn (fun σ => f σ k) (Set.Icc 0 T) :=
    (continuousOn_mode hf k).integrableOn_Icc
  have := continuousOn_mildFn (ν * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)) 0 (fun σ => f σ k) T hT hg
  refine this.congr fun t _ => ?_
  rw [mildFn_eq]
  unfold duh
  simp only [heatMult_eq, mul_zero, zero_add]

theorem tail_bound (m η : ℝ) (hη : 0 ≤ η) (n : ℕ) (x : Coeff d) (hx : MemHs (m + η) x) :
    hsNorm m (x - truncCoeff n x) ≤
      Real.sqrt ((1 + 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) ^ (-η)) * hsNorm (m + η) x := by
  set X : ℝ := 1 + 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 with hX
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith [sq_nonneg Real.pi, sq_nonneg ((n : ℝ) + 1), Real.pi_pos]
  have hX0 : 0 < X := by linarith
  have hpt : ∀ k : Lattice d, sobWeight m k * ‖(x - truncCoeff n x) k‖ ^ 2 ≤
      X ^ (-η) * (sobWeight (m + η) k * ‖x k‖ ^ 2) := by
    intro k
    by_cases hk : InBox n k
    · simp only [Pi.sub_apply, truncCoeff, hk, ite_true, sub_self, norm_zero]
      have : 0 ≤ X ^ (-η) * (sobWeight (m + η) k * ‖x k‖ ^ 2) :=
        mul_nonneg (Real.rpow_nonneg hX0.le _) (mul_nonneg (sobWeight_pos _ k).le (sq_nonneg _))
      simpa using this
    · simp only [Pi.sub_apply, truncCoeff, hk, ite_false, sub_zero]
      have h2 := ET.sobWeight_two_ge_of_not_inBox hk
      have h5 : sobWeight (2 : ℝ) k = (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 := by
        unfold sobWeight; rw [Real.rpow_two]
      rw [h5] at h2
      have hXY : X ≤ 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 :=
        (pow_le_pow_iff_left₀ hX0.le (by positivity) two_ne_zero).mp h2
      have hη' : X ^ η ≤ sobWeight η k := Real.rpow_le_rpow hX0.le hXY hη
      have hw : sobWeight (m + η) k = sobWeight m k * sobWeight η k := sobWeight_add m η k
      have hXX : X ^ (-η) * X ^ η = 1 := by
        rw [← Real.rpow_add hX0]; simp
      have hwm := (sobWeight_pos m k).le
      calc sobWeight m k * ‖x k‖ ^ 2 = (X ^ (-η) * X ^ η) * (sobWeight m k * ‖x k‖ ^ 2) := by
            rw [hXX, one_mul]
        _ = X ^ (-η) * (X ^ η * (sobWeight m k * ‖x k‖ ^ 2)) := by ring
        _ ≤ X ^ (-η) * (sobWeight η k * (sobWeight m k * ‖x k‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hX0.le _)
            exact mul_le_mul_of_nonneg_right hη' (mul_nonneg hwm (sq_nonneg _))
        _ = X ^ (-η) * (sobWeight (m + η) k * ‖x k‖ ^ 2) := by rw [hw]; ring
  have hsum : Summable fun k : Lattice d => sobWeight m k * ‖(x - truncCoeff n x) k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_pos _ k).le (sq_nonneg _)) hpt
      (hx.mul_left _)
  have hle : hsNormSq m (x - truncCoeff n x) ≤ X ^ (-η) * hsNormSq (m + η) x := by
    unfold hsNormSq
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hpt hsum (hx.mul_left _)
  unfold hsNorm
  rw [← Real.sqrt_mul (Real.rpow_nonneg hX0.le _)]
  exact Real.sqrt_le_sqrt hle

theorem tendsto_tail_const (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n : ℕ => Real.sqrt ((1 + 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) ^ (-η))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 1 + 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    nlinarith [sq_nonneg Real.pi, sq_nonneg ((n : ℝ) + 1), Real.pi_pos, sq_nonneg (Real.pi * ((n : ℝ) + 1)),
      sq_nonneg (Real.pi * ((n : ℝ) + 1) - 1), Real.pi_gt_three]
  have h2 := (tendsto_rpow_neg_atTop hη).comp h1
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  rw [Real.sqrt_zero] at h3
  exact h3

theorem duh_cont (ν : ℝ) (hν : 0 < ν) (a b η : ℝ) (hb : 0 ≤ b) (hη : 0 < η) (hbη : b + η < 2)
    (f : ℝ → Coeff d) (T : ℝ) (hT : 0 ≤ T) (hf : ContinuousInHsOn a f (Set.Icc 0 T)) :
    ContinuousInHsOn (a + b) (duh ν f) (Set.Icc 0 T) := by
  obtain ⟨C, hC0, hC⟩ := duh_bound_const (d := d) ν hν a (b + η) (a + b + η) (by linarith) hbη
    (by ring)
  obtain ⟨B, hB0, hB⟩ := exists_bound_hsNorm hf
  set M : ℝ := C * B * Eker ν ((b + η) / 2) T with hMdef
  have hM : ∀ t ∈ Set.Icc 0 T, MemHs (a + b + η) (duh ν f t) ∧ hsNorm (a + b + η) (duh ν f t) ≤ M := by
    intro t ht
    obtain ⟨h1, h2⟩ := hC f T hf B hB t ht
    refine ⟨h1, h2.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (Eker_mono ν _ hν (by linarith) ht.1 ht.2) (mul_nonneg hC0 hB0)
  have hM0 : 0 ≤ M := (hsNorm_nonneg _ _).trans ((hM 0 ⟨le_rfl, hT⟩).2)
  refine contInHs_of_trunc (fun t ht => memHs_mono (by linarith) (hM t ht).1)
    (fun k => continuousOn_duh_mode ν hT hf k) ?_
  intro ε hε
  obtain ⟨n, hn⟩ := ((tendsto_tail_const η hη).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / (M + 1) by positivity))).exists
  refine ⟨n, fun t ht => ?_⟩
  have h1 := tail_bound (a + b) η hη.le n (duh ν f t) (hM t ht).1
  refine h1.trans ?_
  calc _ ≤ Real.sqrt ((1 + 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) ^ (-η)) * M :=
        mul_le_mul_of_nonneg_left (hM t ht).2 (Real.sqrt_nonneg _)
    _ ≤ ε / (M + 1) * M := mul_le_mul_of_nonneg_right hn.le hM0
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

theorem heatMult_pos (ν τ : ℝ) (k : Lattice d) : 0 < heatMult ν τ k := Real.exp_pos _

theorem heatMult_le_one {ν τ : ℝ} (hν : 0 ≤ ν) (hτ : 0 ≤ τ) (k : Lattice d) : heatMult ν τ k ≤ 1 := by
  unfold heatMult
  rw [Real.exp_le_one_iff]
  have : 0 ≤ ν * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * τ := by positivity
  nlinarith

theorem heatC_le {ν τ : ℝ} (hν : 0 ≤ ν) (hτ : 0 ≤ τ) {m : ℝ} {c : Coeff d} (hc : MemHs m c) :
    MemHs m (heatC ν τ c) ∧ hsNorm m (heatC ν τ c) ≤ hsNorm m c := by
  have hpt : ∀ k, sobWeight m k * ‖heatC ν τ c k‖ ^ 2 ≤ sobWeight m k * ‖c k‖ ^ 2 := by
    intro k
    refine mul_le_mul_of_nonneg_left ?_ (sobWeight_pos m k).le
    unfold heatC
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (heatMult_pos ν τ k)]
    have h1 := heatMult_le_one hν hτ k
    have h2 := heatMult_pos ν τ k
    have : (heatMult ν τ k * ‖c k‖) ^ 2 ≤ ‖c k‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right h1 (norm_nonneg (c k))
      nlinarith [norm_nonneg (c k), mul_nonneg h2.le (norm_nonneg (c k))]
    exact this
  have hs : MemHs m (heatC ν τ c) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_pos _ k).le (sq_nonneg _)) hpt hc
  refine ⟨hs, ?_⟩
  unfold hsNorm hsNormSq
  exact Real.sqrt_le_sqrt (Summable.tsum_le_tsum hpt hs hc)

theorem continuousOn_heatC_mode (ν : ℝ) (c : Coeff d) (k : Lattice d) :
    Continuous (fun t => heatC ν t c k) := by
  unfold heatC heatMult
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul continuous_id))).mul continuous_const

theorem heatC_cont {ν : ℝ} (hν : 0 ≤ ν) {m : ℝ} {c : Coeff d} (hc : MemHs m c) (T : ℝ) :
    ContinuousInHsOn m (fun t => heatC ν t c) (Set.Icc 0 T) := by
  refine contInHs_of_trunc (fun t ht => (heatC_le hν ht.1 hc).1)
    (fun k => (continuousOn_heatC_mode ν c k).continuousOn) ?_
  intro ε hε
  obtain ⟨n, hn⟩ := ((truncCoeff_tendsto m c hc).2.eventually
    (gt_mem_nhds hε)).exists
  refine ⟨n, fun t ht => ?_⟩
  have hdec : heatC ν t c - truncCoeff n (heatC ν t c) = heatC ν t (c - truncCoeff n c) := by
    funext k
    by_cases hk : InBox n k <;> simp [heatC, truncCoeff, hk]
  rw [hdec]
  exact ((heatC_le hν ht.1 (memHs_sub_aux hc (memHs_truncCoeff m n c))).2).trans hn.le

/-! ### The nonlinearity along a path -/

/-- Hypotheses of the local theory: `0 ≤ s < d`, `K > d/2 + 1`, a gain parameter
`0 < δ' < min (d - s) 1` and a potential with `V̂ ∈ H^{K+δ'}`. -/
structure LocalHyp (d : ℕ) (s K δ' : ℝ) (V : Torus d → ℝ) : Prop where
  hd : 1 ≤ d
  hs0 : 0 ≤ s
  hsd : s < d
  hK : (d : ℝ) / 2 + 1 < K
  hδ0 : 0 < δ'
  hδ : δ' < min ((d : ℝ) - s) 1
  hV : MemHs (K + δ') (coeffOf V)

theorem nlCoeff_zero (d : ℕ) (s : ℝ) (V : Torus d → ℝ) : nlCoeff d s V (0 : Coeff d) = 0 := by
  funext k
  simp [nlCoeff, mulCoeff, derivCoeff]

theorem contInHs_sub {m : ℝ} {f g : ℝ → Coeff d} {S : Set ℝ} (hf : ContinuousInHsOn m f S)
    (hg : ContinuousInHsOn m g S) : ContinuousInHsOn m (fun t => f t - g t) S := by
  refine ⟨fun τ hτ => memHs_sub_aux (hf.1 τ hτ) (hg.1 τ hτ), fun τ0 hτ0 => ?_⟩
  have h := (hf.2 τ0 hτ0).add (hg.2 τ0 hτ0)
  rw [add_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun _ => hsNorm_nonneg _ _)
    (eventually_nhdsWithin_of_forall fun τ hτ => ?_) h
  have e : f τ - g τ - (f τ0 - g τ0) = (f τ - f τ0) - (g τ - g τ0) := by abel
  rw [e]
  exact hsNorm_sub_le (memHs_sub_aux (hf.1 τ hτ) (hf.1 τ0 hτ0)) (memHs_sub_aux (hg.1 τ hτ) (hg.1 τ0 hτ0))

theorem contInHs_add {m : ℝ} {f g : ℝ → Coeff d} {S : Set ℝ} (hf : ContinuousInHsOn m f S)
    (hg : ContinuousInHsOn m g S) : ContinuousInHsOn m (fun t => f t + g t) S := by
  refine ⟨fun τ hτ => (memHs_add_le m (hf.1 τ hτ) (hg.1 τ hτ)).1, fun τ0 hτ0 => ?_⟩
  have h := (hf.2 τ0 hτ0).add (hg.2 τ0 hτ0)
  rw [add_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun _ => hsNorm_nonneg _ _)
    (eventually_nhdsWithin_of_forall fun τ hτ => ?_) h
  have e : f τ + g τ - (f τ0 + g τ0) = (f τ - f τ0) + (g τ - g τ0) := by abel
  rw [e]
  exact (memHs_add_le m (memHs_sub_aux (hf.1 τ hτ) (hf.1 τ0 hτ0))
    (memHs_sub_aux (hg.1 τ hτ) (hg.1 τ0 hτ0))).2

theorem nl_lip {s K δ' : ℝ} {V : Torus d → ℝ} (H : LocalHyp d s K δ' V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρc ρc' : Coeff d, MemHs K ρc → MemHs K ρc' →
      MemHs (K - 2 + δ') (nlCoeff d s V ρc - nlCoeff d s V ρc') ∧
      hsNorm (K - 2 + δ') (nlCoeff d s V ρc - nlCoeff d s V ρc') ≤
        C * (1 + hsNorm K ρc + hsNorm K ρc') * hsNorm K (ρc - ρc') :=
  exists_nl_lipschitz' H.hd s H.hs0 H.hsd K H.hK V δ' H.hδ0.le H.hδ H.hV

theorem nl_mem_bound {s K δ' : ℝ} {V : Torus d → ℝ} (H : LocalHyp d s K δ' V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρc : Coeff d, MemHs K ρc → ∀ B : ℝ, hsNorm K ρc ≤ B →
      MemHs (K - 2 + δ') (nlCoeff d s V ρc) ∧
        hsNorm (K - 2 + δ') (nlCoeff d s V ρc) ≤ C * (1 + B) * B := by
  obtain ⟨C, hC0, hC⟩ := nl_lip H
  refine ⟨C, hC0, fun ρ hρ B hB => ?_⟩
  have h := hC ρ 0 hρ (memHs_zero_coeff K)
  rw [nlCoeff_zero, sub_zero, sub_zero, hsNorm_zero_coeff, add_zero] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hB0 : 0 ≤ B := (hsNorm_nonneg _ _).trans hB
  have h1 : (1 + hsNorm K ρ) * hsNorm K ρ ≤ (1 + B) * B :=
    mul_le_mul (by linarith) hB (hsNorm_nonneg _ _) (by linarith)
  calc C * (1 + hsNorm K ρ) * hsNorm K ρ = C * ((1 + hsNorm K ρ) * hsNorm K ρ) := by ring
    _ ≤ C * ((1 + B) * B) := mul_le_mul_of_nonneg_left h1 hC0
    _ = _ := by ring

theorem nl_cont {s K δ' : ℝ} {V : Torus d → ℝ} (H : LocalHyp d s K δ' V) {ρ : ℝ → Coeff d}
    {S : Set ℝ} (hρ : ContinuousInHsOn K ρ S) :
    ContinuousInHsOn (K - 2 + δ') (fun t => nlCoeff d s V (ρ t)) S := by
  obtain ⟨C, hC0, hC⟩ := nl_lip H
  refine ⟨fun τ hτ => (nl_mem_bound H).choose_spec.2 (ρ τ) (hρ.1 τ hτ) _ le_rfl |>.1, fun τ0 hτ0 => ?_⟩
  set n0 := hsNorm K (ρ τ0) with hn0
  have hx : Tendsto (fun τ => hsNorm K (ρ τ - ρ τ0)) (𝓝[S] τ0) (𝓝 0) := hρ.2 τ0 hτ0
  have hup : Tendsto (fun τ => C * (1 + 2 * n0 + hsNorm K (ρ τ - ρ τ0)) * hsNorm K (ρ τ - ρ τ0))
      (𝓝[S] τ0) (𝓝 (C * (1 + 2 * n0 + 0) * 0)) :=
    (tendsto_const_nhds.mul (tendsto_const_nhds.add hx)).mul hx
  rw [mul_zero] at hup
  refine squeeze_zero' (Eventually.of_forall fun _ => hsNorm_nonneg _ _)
    (eventually_nhdsWithin_of_forall fun τ hτ => ?_) hup
  have h := (hC (ρ τ) (ρ τ0) (hρ.1 τ hτ) (hρ.1 τ0 hτ0)).2
  have h2 : hsNorm K (ρ τ) ≤ n0 + hsNorm K (ρ τ - ρ τ0) := by
    have := abs_hsNorm_sub_le (hρ.1 τ hτ) (hρ.1 τ0 hτ0)
    rw [abs_le] at this
    linarith [this.2]
  refine h.trans ?_
  have hz := hsNorm_nonneg K (ρ τ - ρ τ0)
  have : C * (1 + hsNorm K (ρ τ) + n0) ≤ C * (1 + 2 * n0 + hsNorm K (ρ τ - ρ τ0)) :=
    mul_le_mul_of_nonneg_left (by linarith) hC0
  exact mul_le_mul_of_nonneg_right this hz

theorem duh_sub (ν : ℝ) {a : ℝ} {f g : ℝ → Coeff d} {T : ℝ} (hf : ContinuousInHsOn a f (Set.Icc 0 T))
    (hg : ContinuousInHsOn a g (Set.Icc 0 T)) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    duh ν (fun σ => f σ - g σ) t = duh ν f t - duh ν g t := by
  funext k
  have hsub : Set.uIcc 0 t ⊆ Set.Icc 0 T := by
    rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
  have h1 : IntervalIntegrable (fun σ => (heatMult ν (t - σ) k : ℂ) * f σ k) volume 0 t :=
    ContinuousOn.intervalIntegrable ((continuousOn_mode_mul_heat hf ν t k).mono hsub)
  have h2 : IntervalIntegrable (fun σ => (heatMult ν (t - σ) k : ℂ) * g σ k) volume 0 t :=
    ContinuousOn.intervalIntegrable ((continuousOn_mode_mul_heat hg ν t k).mono hsub)
  unfold duh
  simp only [Pi.sub_apply, mul_sub]
  exact intervalIntegral.integral_sub h1 h2

/-- The three Duhamel estimates for the nonlinearity along `H^K` paths with constant `A`. -/
def DuhEst (d : ℕ) (s K δ' : ℝ) (V : Torus d → ℝ) (ν A : ℝ) : Prop :=
  ∀ (T : ℝ), 0 ≤ T → ∀ ρ ρ' : ℝ → Coeff d,
      ContinuousInHsOn K ρ (Set.Icc 0 T) → ContinuousInHsOn K ρ' (Set.Icc 0 T) →
      ContinuousInHsOn K (duh ν (fun σ => nlCoeff d s V (ρ σ))) (Set.Icc 0 T) ∧
      (∀ B : ℝ, (∀ σ ∈ Set.Icc 0 T, hsNorm K (ρ σ) ≤ B) → ∀ t ∈ Set.Icc 0 T,
        MemHs K (duh ν (fun σ => nlCoeff d s V (ρ σ)) t) ∧
        hsNorm K (duh ν (fun σ => nlCoeff d s V (ρ σ)) t) ≤
          A * (1 + B) * B * Eker ν ((2 - δ') / 2) t) ∧
      (∀ B D : ℝ, (∀ σ ∈ Set.Icc 0 T, hsNorm K (ρ σ) ≤ B) → (∀ σ ∈ Set.Icc 0 T, hsNorm K (ρ' σ) ≤ B) →
        (∀ σ ∈ Set.Icc 0 T, hsNorm K (ρ σ - ρ' σ) ≤ D) → ∀ t ∈ Set.Icc 0 T,
        MemHs K (duh ν (fun σ => nlCoeff d s V (ρ σ)) t - duh ν (fun σ => nlCoeff d s V (ρ' σ)) t) ∧
        hsNorm K (duh ν (fun σ => nlCoeff d s V (ρ σ)) t - duh ν (fun σ => nlCoeff d s V (ρ' σ)) t) ≤
          A * (1 + 2 * B) * D * Eker ν ((2 - δ') / 2) t)

theorem duh_nl_estimates {s K δ' : ℝ} {V : Torus d → ℝ} (H : LocalHyp d s K δ' V) (ν : ℝ)
    (hν : 0 < ν) : ∃ A : ℝ, 0 ≤ A ∧ DuhEst d s K δ' V ν A := by
  have hδ1 : δ' < 1 := lt_of_lt_of_le H.hδ (min_le_right _ _)
  have hδ0 := H.hδ0
  obtain ⟨C, hC0, hC⟩ := nl_lip H
  obtain ⟨Cb, hCb0, hCb⟩ := nl_mem_bound H
  have hKab : K - 2 + δ' + (2 - δ') = K := by ring
  obtain ⟨Ch, hCh0, hCh⟩ := duh_bound_const (d := d) ν hν (K - 2 + δ') (2 - δ') K
    (by linarith) (by linarith [H.hδ0]) hKab
  refine ⟨Ch * (max C Cb), by positivity, fun T hT ρ ρ' hρ hρ' => ⟨?_, ?_, ?_⟩⟩
  · have := duh_cont (d := d) ν hν (K - 2 + δ') (2 - δ') (δ' / 2) (by linarith) (by linarith [H.hδ0])
      (by linarith) (fun σ => nlCoeff d s V (ρ σ)) T hT (nl_cont H hρ)
    rwa [hKab] at this
  · intro B hB t ht
    have hB0 : 0 ≤ B := (hsNorm_nonneg _ _).trans (hB 0 ⟨le_rfl, hT⟩)
    have hbd : ∀ σ ∈ Set.Icc 0 T, hsNorm (K - 2 + δ') (nlCoeff d s V (ρ σ)) ≤ Cb * (1 + B) * B :=
      fun σ hσ => (hCb (ρ σ) (hρ.1 σ hσ) B (hB σ hσ)).2
    obtain ⟨h1, h2⟩ := hCh _ T (nl_cont H hρ) _ hbd t ht
    refine ⟨h1, h2.trans ?_⟩
    have hE := Eker_nonneg ν ((2 - δ') / 2) t hν (by linarith) ht.1
    have hCbm : Cb ≤ max C Cb := le_max_right _ _
    calc Ch * (Cb * (1 + B) * B) * Eker ν ((2 - δ') / 2) t
        ≤ Ch * (max C Cb * (1 + B) * B) * Eker ν ((2 - δ') / 2) t := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hCh0) hE
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbm (by linarith)) hB0
      _ = _ := by ring
  · intro B D hB hB' hD t ht
    have hB0 : 0 ≤ B := (hsNorm_nonneg _ _).trans (hB 0 ⟨le_rfl, hT⟩)
    have hcont : ContinuousInHsOn (K - 2 + δ') (fun σ => nlCoeff d s V (ρ σ)) (Set.Icc 0 T) := nl_cont H hρ
    have hcont' : ContinuousInHsOn (K - 2 + δ') (fun σ => nlCoeff d s V (ρ' σ)) (Set.Icc 0 T) := nl_cont H hρ'
    have hdiff := contInHs_sub hcont hcont'
    have hbd : ∀ σ ∈ Set.Icc 0 T, hsNorm (K - 2 + δ') (nlCoeff d s V (ρ σ) - nlCoeff d s V (ρ' σ)) ≤
        C * (1 + 2 * B) * D := by
      intro σ hσ
      have h := (hC (ρ σ) (ρ' σ) (hρ.1 σ hσ) (hρ'.1 σ hσ)).2
      refine h.trans ?_
      have hD0 : 0 ≤ D := (hsNorm_nonneg _ _).trans (hD σ hσ)
      have h1 : 1 + hsNorm K (ρ σ) + hsNorm K (ρ' σ) ≤ 1 + 2 * B := by
        linarith [hB σ hσ, hB' σ hσ]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC0) (hD σ hσ) (hsNorm_nonneg _ _)
        (mul_nonneg hC0 (by linarith))
    obtain ⟨h1, h2⟩ := hCh _ T hdiff _ hbd t ht
    rw [← duh_sub ν hcont hcont' ht]
    refine ⟨h1, h2.trans ?_⟩
    have hE := Eker_nonneg ν ((2 - δ') / 2) t hν (by linarith) ht.1
    have hD0 : 0 ≤ D := (hsNorm_nonneg _ _).trans (hD 0 ⟨le_rfl, hT⟩)
    have hCm : C ≤ max C Cb := le_max_left _ _
    calc Ch * (C * (1 + 2 * B) * D) * Eker ν ((2 - δ') / 2) t
        ≤ Ch * (max C Cb * (1 + 2 * B) * D) * Eker ν ((2 - δ') / 2) t := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hCh0) hE
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCm (by linarith)) hD0
      _ = _ := by ring

/-! ### The Picard map -/

/-- The Picard map `Φ(ρ)(t) = e^{tνΔ}ρ̂⁰ + ∫₀ᵗ e^{(t-σ)νΔ} nl(ρ(σ)) dσ`. -/
def phi (ν : ℝ) (s : ℝ) (V : Torus d → ℝ) (ρ₀ : Coeff d) (ρ : ℝ → Coeff d) (t : ℝ) : Coeff d :=
  heatC ν t ρ₀ + duh ν (fun σ => nlCoeff d s V (ρ σ)) t

/-- Membership in the ball `X_T`. -/
def Good (K R T : ℝ) (ρ : ℝ → Coeff d) : Prop :=
  ContinuousInHsOn K ρ (Set.Icc 0 T) ∧ ∀ t ∈ Set.Icc 0 T, hsNorm K (ρ t) ≤ 2 * R

section Picard

variable {s K δ' : ℝ} {V : Torus d → ℝ} {ν A R T : ℝ}

theorem phi_good (hν : 0 < ν) (hδ0 : 0 < δ') (hδ1 : δ' < 1) (hA0 : 0 ≤ A) (hA : DuhEst d s K δ' V ν A)
    (hR : 0 ≤ R) (hT : 0 ≤ T) (hsmall : A * (1 + 4 * R) * Eker ν ((2 - δ') / 2) T ≤ 1 / 2)
    {ρ₀ : Coeff d} (hρ₀ : MemHs K ρ₀) (hn : hsNorm K ρ₀ ≤ R) {ρ : ℝ → Coeff d}
    (hρ : Good K R T ρ) : Good K R T (phi ν s V ρ₀ ρ) := by
  have hγ : (2 - δ') / 2 < 1 := by linarith
  obtain ⟨hc, hb, -⟩ := hA T hT ρ ρ hρ.1 hρ.1
  refine ⟨contInHs_add (heatC_cont hν.le hρ₀ T) hc, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := heatC_le hν.le ht.1 hρ₀
  obtain ⟨h3, h4⟩ := hb (2 * R) hρ.2 t ht
  have h5 := (memHs_add_le K h1 h3).2
  have hE := Eker_nonneg ν _ t hν hγ ht.1
  have hEm := Eker_mono ν _ hν hγ ht.1 ht.2
  have hAE : 0 ≤ A * (1 + 4 * R) * Eker ν ((2 - δ') / 2) t := by positivity
  have h6 : A * (1 + 2 * R) * (2 * R) * Eker ν ((2 - δ') / 2) t ≤ R := by
    have : A * (1 + 2 * R) * (2 * R) * Eker ν ((2 - δ') / 2) t ≤
        (A * (1 + 4 * R) * Eker ν ((2 - δ') / 2) t) * (2 * R) := by
      have : A * (1 + 2 * R) * Eker ν ((2 - δ') / 2) t ≤ A * (1 + 4 * R) * Eker ν ((2 - δ') / 2) t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hA0) hE
      nlinarith
    have h7 : A * (1 + 4 * R) * Eker ν ((2 - δ') / 2) t ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left hEm (by positivity)).trans hsmall
    nlinarith
  show hsNorm K (heatC ν t ρ₀ + duh ν (fun σ => nlCoeff d s V (ρ σ)) t) ≤ 2 * R
  linarith

theorem phi_contract (hν : 0 < ν) (hδ0 : 0 < δ') (hA0 : 0 ≤ A)
    (hA : DuhEst d s K δ' V ν A)
    (hR : 0 ≤ R) (hT : 0 ≤ T) (hsmall : A * (1 + 4 * R) * Eker ν ((2 - δ') / 2) T ≤ 1 / 2)
    (ρ₀ : Coeff d) {ρ ρ' : ℝ → Coeff d} (hρ : Good K R T ρ) (hρ' : Good K R T ρ') {D : ℝ}
    (hD : ∀ σ ∈ Set.Icc 0 T, hsNorm K (ρ σ - ρ' σ) ≤ D) :
    ∀ t ∈ Set.Icc 0 T, MemHs K (phi ν s V ρ₀ ρ t - phi ν s V ρ₀ ρ' t) ∧
      hsNorm K (phi ν s V ρ₀ ρ t - phi ν s V ρ₀ ρ' t) ≤ D / 2 := by
  have hγ : (2 - δ') / 2 < 1 := by linarith
  intro t ht
  obtain ⟨-, -, hd⟩ := hA T hT ρ ρ' hρ.1 hρ'.1
  obtain ⟨h1, h2⟩ := hd (2 * R) D hρ.2 hρ'.2 hD t ht
  have e : phi ν s V ρ₀ ρ t - phi ν s V ρ₀ ρ' t =
      duh ν (fun σ => nlCoeff d s V (ρ σ)) t - duh ν (fun σ => nlCoeff d s V (ρ' σ)) t := by
    unfold phi; abel
  rw [e]
  refine ⟨h1, h2.trans ?_⟩
  have hD0 : 0 ≤ D := (hsNorm_nonneg _ _).trans (hD 0 ⟨le_rfl, hT⟩)
  have hE := Eker_nonneg ν _ t hν hγ ht.1
  have hEm := Eker_mono ν _ hν hγ ht.1 ht.2
  have h7 : A * (1 + 2 * (2 * R)) * Eker ν ((2 - δ') / 2) t ≤ 1 / 2 := by
    have : A * (1 + 2 * (2 * R)) * Eker ν ((2 - δ') / 2) t =
        A * (1 + 4 * R) * Eker ν ((2 - δ') / 2) t := by ring
    rw [this]
    exact (mul_le_mul_of_nonneg_left hEm (by positivity)).trans hsmall
  calc A * (1 + 2 * (2 * R)) * D * Eker ν ((2 - δ') / 2) t
      = (A * (1 + 2 * (2 * R)) * Eker ν ((2 - δ') / 2) t) * D := by ring
    _ ≤ 1 / 2 * D := mul_le_mul_of_nonneg_right h7 hD0
    _ = D / 2 := by ring

end Picard

theorem contInHs_of_unif {m : ℝ} {S : Set ℝ} (c : ℕ → ℝ → Coeff d) (L : ℝ → Coeff d)
    (δ : ℕ → ℝ) (hc : ∀ n, ContinuousInHsOn m (c n) S) (hL : ∀ τ ∈ S, MemHs m (L τ))
    (hδ : Tendsto δ atTop (𝓝 0)) (hLc : ∀ n, ∀ τ ∈ S, hsNorm m (L τ - c n τ) ≤ δ n) :
    ContinuousInHsOn m L S := by
  refine ⟨hL, fun τ0 hτ0 => ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := (hδ.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))).exists
  have hev := (Metric.tendsto_nhds.mp ((hc n).2 τ0 hτ0)) (ε / 2) (by positivity)
  filter_upwards [hev, self_mem_nhdsWithin] with τ hτ hτS
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNorm_nonneg _ _)] at hτ ⊢
  have e : L τ - L τ0 = ((L τ - c n τ) - (L τ0 - c n τ0)) + (c n τ - c n τ0) := by abel
  have m1 := memHs_sub_aux (hL τ hτS) ((hc n).1 τ hτS)
  have m2 := memHs_sub_aux (hL τ0 hτ0) ((hc n).1 τ0 hτ0)
  have m3 := memHs_sub_aux ((hc n).1 τ hτS) ((hc n).1 τ0 hτ0)
  have h1 := (memHs_add_le m (memHs_sub_aux m1 m2) m3).2
  have h2 := hsNorm_sub_le m1 m2
  rw [e]
  have := hLc n τ hτS
  have := hLc n τ0 hτ0
  linarith

/-- The Picard iterates. -/
def picardSeq (ν : ℝ) (s : ℝ) (V : Torus d → ℝ) (ρ₀ : Coeff d) : ℕ → ℝ → Coeff d
  | 0 => fun _ => ρ₀
  | n + 1 => phi ν s V ρ₀ (picardSeq ν s V ρ₀ n)

theorem contInHs_const {m : ℝ} {c : Coeff d} (hc : MemHs m c) (S : Set ℝ) :
    ContinuousInHsOn m (fun _ => c) S := by
  refine ⟨fun _ _ => hc, fun τ0 _ => ?_⟩
  simp only [sub_self, hsNorm_zero_coeff]
  exact tendsto_const_nhds

section Picard2

variable {s K δ' : ℝ} {V : Torus d → ℝ} {ν A R T : ℝ}

/-- **Picard iteration.**  Under the smallness condition, the Picard iterates converge in
`C([0,T]; H^K)` to a fixed point of `Φ`; a coordinatewise-closed property `P` of the values is
inherited. -/
theorem picard_exists (hν : 0 < ν) (hδ0 : 0 < δ') (hδ1 : δ' < 1) (hA0 : 0 ≤ A)
    (hA : DuhEst d s K δ' V ν A) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hsmall : A * (1 + 4 * R) * Eker ν ((2 - δ') / 2) T ≤ 1 / 2)
    {ρ₀ : Coeff d} (hρ₀ : MemHs K ρ₀) (hn : hsNorm K ρ₀ ≤ R) (P : Coeff d → Prop)
    (hP0 : P ρ₀)
    (hPphi : ∀ ρ : ℝ → Coeff d, Good K R T ρ → (∀ t ∈ Set.Icc 0 T, P (ρ t)) →
      ∀ t ∈ Set.Icc 0 T, P (phi ν s V ρ₀ ρ t))
    (hPlim : ∀ (c : ℕ → Coeff d) (L : Coeff d), (∀ k, Tendsto (fun n => c n k) atTop (𝓝 (L k))) →
      (∀ n, P (c n)) → P L) :
    ∃ ρ : ℝ → Coeff d, Good K R T ρ ∧ (∀ t ∈ Set.Icc 0 T, P (ρ t)) ∧
      ∀ t ∈ Set.Icc 0 T, phi ν s V ρ₀ ρ t = ρ t := by
  set seq := picardSeq ν s V ρ₀ with hseq
  have hgood : ∀ n, Good K R T (seq n) ∧ ∀ t ∈ Set.Icc 0 T, P (seq n t) := by
    intro n
    induction n with
    | zero =>
      refine ⟨⟨contInHs_const hρ₀ _, fun t _ => ?_⟩, fun t _ => hP0⟩
      show hsNorm K ρ₀ ≤ 2 * R
      linarith
    | succ n ih =>
      exact ⟨phi_good hν hδ0 hδ1 hA0 hA hR hT hsmall hρ₀ hn ih.1, hPphi _ ih.1 ih.2⟩
  have hstep : ∀ n, ∀ t ∈ Set.Icc 0 T, hsNorm K (seq (n + 1) t - seq n t) ≤ 4 * R * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have h := hsNorm_sub_le ((hgood 1).1.1.1 t ht) ((hgood 0).1.1.1 t ht)
      have h1 := (hgood 1).1.2 t ht
      have h0 := (hgood 0).1.2 t ht
      simp only [pow_zero, mul_one]
      linarith
    | succ n ih =>
      intro t ht
      have := (phi_contract hν hδ0 hA0 hA hR hT hsmall ρ₀ (hgood (n + 1)).1 (hgood n).1 ih t ht).2
      calc _ ≤ 4 * R * (1 / 2) ^ n / 2 := this
        _ = _ := by rw [pow_succ]; ring
  have hdist : ∀ n p, n ≤ p → ∀ t ∈ Set.Icc 0 T,
      hsNorm K (seq p t - seq n t) ≤ 8 * R * ((1 / 2) ^ n - (1 / 2) ^ p) := by
    intro n p hnp
    induction p, hnp using Nat.le_induction with
    | base => intro t ht; simp [hsNorm_zero_coeff]
    | succ p hnp ih =>
      intro t ht
      have e : seq (p + 1) t - seq n t = (seq (p + 1) t - seq p t) + (seq p t - seq n t) := by abel
      have m1 := memHs_sub_aux ((hgood (p + 1)).1.1.1 t ht) ((hgood p).1.1.1 t ht)
      have m2 := memHs_sub_aux ((hgood p).1.1.1 t ht) ((hgood n).1.1.1 t ht)
      rw [e]
      have h := (memHs_add_le K m1 m2).2
      have h1 := hstep p t ht
      have h2 := ih t ht
      calc _ ≤ _ := h
        _ ≤ 4 * R * (1 / 2) ^ p + 8 * R * ((1 / 2) ^ n - (1 / 2) ^ p) := add_le_add h1 h2
        _ = _ := by rw [pow_succ]; ring
  set δ : ℕ → ℝ := fun n => 8 * R * (1 / 2) ^ n with hδdef
  have hδt : Tendsto δ atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (8 * R)
    simpa [hδdef] using this
  have hlim : ∀ t ∈ Set.Icc 0 T, ∃ L : Coeff d, MemHs K L ∧
      (∀ k, Tendsto (fun n => seq n t k) atTop (𝓝 (L k))) ∧ ∀ n, hsNorm K (L - seq n t) ≤ δ n := by
    intro t ht
    refine cauchy_limit (fun n => seq n t) δ (fun n => (hgood n).1.1.1 t ht) hδt ?_
    intro n p hnp
    refine (hdist n p hnp t ht).trans ?_
    have : 0 ≤ 8 * R * (1 / 2) ^ p := by positivity
    simp only [hδdef]; linarith
  choose! L hLmem hLlim hLd using hlim
  have hLb : ∀ t ∈ Set.Icc 0 T, hsNorm K (L t) ≤ 2 * R := fun t ht =>
    (limit_bound (hLlim t ht) (fun n => (hgood n).1.1.1 t ht) (fun n => (hgood n).1.2 t ht)).2
  have hLc : ContinuousInHsOn K L (Set.Icc 0 T) :=
    contInHs_of_unif (fun n => seq n) L δ (fun n => (hgood n).1.1) hLmem hδt
      (fun n τ hτ => hLd τ hτ n)
  have hLgood : Good K R T L := ⟨hLc, hLb⟩
  refine ⟨L, hLgood, fun t ht => hPlim (fun n => seq n t) (L t) (hLlim t ht)
    (fun n => (hgood n).2 t ht), fun t ht => ?_⟩
  -- fixed point
  have hbound : ∀ n, hsNorm K (phi ν s V ρ₀ L t - L t) ≤ δ n / 2 + δ (n + 1) := by
    intro n
    have hc := phi_contract hν hδ0 hA0 hA hR hT hsmall ρ₀ hLgood (hgood n).1
      (D := δ n) (fun σ hσ => hLd σ hσ n) t ht
    have h5 : phi ν s V ρ₀ (seq n) t = seq (n + 1) t := rfl
    rw [h5] at hc
    have hm1 := hc.1
    have hm2 := hLd t ht (n + 1)
    have e : phi ν s V ρ₀ L t - L t = (phi ν s V ρ₀ L t - seq (n + 1) t) - (L t - seq (n + 1) t) := by
      abel
    rw [e]
    have hm3 : MemHs K (L t - seq (n + 1) t) := memHs_sub_aux (hLmem t ht) ((hgood (n + 1)).1.1.1 t ht)
    have := hsNorm_sub_le hm1 hm3
    linarith [hc.2]
  have hz : hsNorm K (phi ν s V ρ₀ L t - L t) ≤ 0 := by
    have ht0 : Tendsto (fun n => δ n / 2 + δ (n + 1)) atTop (𝓝 (0 / 2 + 0)) :=
      (hδt.div_const 2).add (hδt.comp (tendsto_add_atTop_nat 1))
    simp only [zero_div, add_zero] at ht0
    exact ge_of_tendsto' ht0 hbound
  have hmem : MemHs K (phi ν s V ρ₀ L t - L t) :=
    memHs_sub_aux ((phi_good hν hδ0 hδ1 hA0 hA hR hT hsmall hρ₀ hn hLgood).1.1 t ht) (hLmem t ht)
  have := eq_zero_of_hsNorm_eq_zero hmem (le_antisymm hz (hsNorm_nonneg _ _))
  exact sub_eq_zero.mp this

end Picard2

/-! ### Variation of constants on `[0,T]` -/

/-- Variation of constants for a scalar linear ODE on `[0,T]` with integrable forcing
(the `[0,T]` analogue of `mild_iff_aux`). -/
theorem mild_iff_Icc (lam : ℝ) (u0 : ℂ) (u f : ℝ → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hu : ContinuousOn u (Set.Icc 0 T)) (hf : IntegrableOn f (Set.Icc 0 T)) :
    (∀ t ∈ Set.Icc 0 T, u t = u0 + ∫ σ in (0 : ℝ)..t, (-(lam : ℂ) * u σ + f σ)) ↔
      ∀ t ∈ Set.Icc 0 T, u t = ((Real.exp (-lam * t) : ℝ) : ℂ) * u0 +
        ∫ σ in (0 : ℝ)..t, ((Real.exp (-lam * (t - σ)) : ℝ) : ℂ) * f σ := by
  set g : ℝ → ℂ := (Set.Icc (0 : ℝ) T).indicator f with hgdef
  have hgint : ∀ t, 0 ≤ t → IntegrableOn g (Set.Icc 0 t) := fun t _ =>
    ((integrable_indicator_iff measurableSet_Icc).mpr hf).integrableOn
  have hgf : ∀ σ ∈ Set.Icc 0 T, g σ = f σ := fun σ hσ => Set.indicator_of_mem hσ f
  have hmc : ContinuousOn (mildFn lam u0 g) (Set.Icc 0 T) :=
    continuousOn_mildFn lam u0 g T hT (hgint T hT)
  have hsubt : ∀ t ∈ Set.Icc (0 : ℝ) T, Set.uIcc 0 t ⊆ Set.Icc 0 T := by
    intro t ht
    rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
  constructor
  · intro h t0 ht0
    set w : ℝ → ℂ := fun t => u t - mildFn lam u0 g t with hw
    have hwc : ContinuousOn w (Set.Icc 0 T) := hu.sub hmc
    have key : ∀ t ∈ Set.Icc 0 T, w t = -(lam : ℂ) * ∫ σ in (0 : ℝ)..t, w σ := by
      intro t ht
      have hs := hsubt t ht
      have hIu : IntervalIntegrable u volume 0 t := ContinuousOn.intervalIntegrable (hu.mono hs)
      have hIm : IntervalIntegrable (mildFn lam u0 g) volume 0 t :=
        ContinuousOn.intervalIntegrable (hmc.mono hs)
      have hIf : IntervalIntegrable f volume 0 t :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
          (hf.mono_set (by rw [Set.uIcc_of_le ht.1] at hs; exact hs))
      have hIg : IntervalIntegrable g volume 0 t :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr (hgint t ht.1)
      have hA := (hIu.const_mul (-(lam : ℂ))).add hIf
      have hB := (hIm.const_mul (-(lam : ℂ))).add hIg
      have hut := h t ht
      have hmt := mildFn_integrated lam u0 g hgint t ht.1
      calc w t = (∫ σ in (0 : ℝ)..t, (-(lam : ℂ) * u σ + f σ)) -
            ∫ σ in (0 : ℝ)..t, (-(lam : ℂ) * mildFn lam u0 g σ + g σ) := by
            simp only [hw]; rw [hut, hmt]; ring
        _ = ∫ σ in (0 : ℝ)..t, ((-(lam : ℂ) * u σ + f σ) -
            (-(lam : ℂ) * mildFn lam u0 g σ + g σ)) := (intervalIntegral.integral_sub hA hB).symm
        _ = ∫ σ in (0 : ℝ)..t, -(lam : ℂ) * w σ := by
            refine intervalIntegral.integral_congr fun σ hσ => ?_
            have := hgf σ (hs hσ)
            simp only [hw]; rw [this]; ring
        _ = -(lam : ℂ) * ∫ σ in (0 : ℝ)..t, w σ := intervalIntegral.integral_const_mul _ _
    have h0 := ode_zero lam T hT w hwc key t0 ht0
    have h1 : u t0 = mildFn lam u0 g t0 := by simpa [hw, sub_eq_zero] using h0
    rw [h1, mildFn_eq]
    congr 1
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [hgf σ (hsubt t0 ht0 hσ)]
  · intro h t ht
    have hs := hsubt t ht
    have hall : ∀ σ ∈ Set.Icc (0 : ℝ) T, u σ = mildFn lam u0 g σ := by
      intro σ hσ
      have hs' := hsubt σ hσ
      rw [h σ hσ, mildFn_eq]
      congr 1
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [hgf τ (hs' hτ)]
    rw [hall t ht, mildFn_integrated lam u0 g hgint t ht.1]
    congr 1
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [hgf σ (hs hσ), hall σ (hs hσ)]

/-! ### The local analogue of `IsMFSolutionHK` and the mild form on `[0,T]` -/

/-- A solution of the integrated mean-field equation on `[0,T]` with initial coefficients
`ρ̂⁰`, continuous into `H^K` (the `[0,T]` analogue of `IsMFSolutionHK`). -/
structure IsMFSolutionHKOn (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (invβ K : ℝ) (ρ₀ : Coeff d)
    (ρc : ℝ → Coeff d) (T : ℝ) : Prop where
  init : ρc 0 = ρ₀
  cont : ContinuousInHsOn K ρc (Set.Icc 0 T)
  integrable : ∀ k, ∀ t ∈ Set.Icc 0 T,
    IntegrableOn (fun σ => mfRhsCoeff d s V invβ (ρc σ) k) (Set.Icc 0 t)
  eq : ∀ k, ∀ t ∈ Set.Icc 0 T,
    ρc t k = ρ₀ k + ∫ σ in (0 : ℝ)..t, mfRhsCoeff d s V invβ (ρc σ) k

/-- The mild equation on `[0,T]`. -/
def IsMildOn (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (ν : ℝ) (ρ₀ : Coeff d) (ρc : ℝ → Coeff d)
    (T : ℝ) : Prop :=
  ∀ k, ∀ t ∈ Set.Icc 0 T, ρc t k = (heatMult ν t k : ℂ) * ρ₀ k +
    ∫ σ in (0 : ℝ)..t, (heatMult ν (t - σ) k : ℂ) * nlCoeff d s V (ρc σ) k

/-- Integrated form `⇔` mild form on `[0,T]` (modewise variation of constants). -/
theorem integrated_iff_mild_Icc {s K : ℝ} {V : Torus d → ℝ} {ν T : ℝ} (hT : 0 ≤ T) {ρ₀ : Coeff d}
    {ρc : ℝ → Coeff d} (hcont : ContinuousInHsOn K ρc (Set.Icc 0 T))
    (hint : ∀ k, IntegrableOn (fun σ => nlCoeff d s V (ρc σ) k) (Set.Icc 0 T)) :
    (∀ k, ∀ t ∈ Set.Icc 0 T, ρc t k = ρ₀ k +
        ∫ σ in (0 : ℝ)..t, mfRhsCoeff d s V ν (ρc σ) k) ↔ IsMildOn d s V ν ρ₀ ρc T := by
  unfold IsMildOn
  refine forall_congr' fun k => ?_
  have := mild_iff_Icc (ν * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)) (ρ₀ k) (fun t => ρc t k)
    (fun σ => nlCoeff d s V (ρc σ) k) T hT (continuousOn_mode hcont k) (hint k)
  simp_rw [heatMult_eq]
  simp_rw [mfRhsCoeff_mode]
  exact this

/-! ### Realness -/

theorem isRealCoeff_add' {a b : Coeff d} (ha : IsRealCoeff a) (hb : IsRealCoeff b) :
    IsRealCoeff (a + b) := by
  rw [isRealCoeff_iff_reflConj] at *
  rw [reflConj_add, ha, hb]

theorem isRealCoeff_sum' {ι : Type*} (S : Finset ι) (f : ι → Coeff d)
    (hf : ∀ i ∈ S, IsRealCoeff (f i)) : IsRealCoeff (∑ i ∈ S, f i) := by
  rw [isRealCoeff_iff_reflConj, reflConj_sum]
  exact Finset.sum_congr rfl fun i hi => (isRealCoeff_iff_reflConj _).mp (hf i hi)

theorem heatMult_neg (ν τ : ℝ) (k : Lattice d) : heatMult ν τ (-k) = heatMult ν τ k := by
  unfold heatMult; rw [enorm_neg']

theorem isRealCoeff_heatC (ν τ : ℝ) {c : Coeff d} (hc : IsRealCoeff c) : IsRealCoeff (heatC ν τ c) := by
  intro k
  unfold heatC
  rw [heatMult_neg, hc k, map_mul, Complex.conj_ofReal]

theorem isRealCoeff_nl {s : ℝ} {V : Torus d → ℝ} (hV : IsRealCoeff (coeffOf V)) {c : Coeff d}
    (hc : IsRealCoeff c) : IsRealCoeff (nlCoeff d s V c) := by
  have h : nlCoeff d s V c = ∑ j : Fin d, derivCoeff j
      (mulCoeff c (derivCoeff j (coeffOf V) + gradRieszCoeff d s j c)) := by
    funext k
    simp only [nlCoeff, Finset.sum_apply]
    rfl
  rw [h]
  refine isRealCoeff_sum' _ _ fun j _ => isRealCoeff_derivCoeff j ?_
  have hw : IsRealCoeff (derivCoeff j (coeffOf V) + gradRieszCoeff d s j c) :=
    isRealCoeff_add' (isRealCoeff_derivCoeff j hV) (isRealCoeff_gradRieszCoeff s j hc)
  have := mulCoeff_reflConj c (derivCoeff j (coeffOf V) + gradRieszCoeff d s j c) hc
  rw [isRealCoeff_iff_reflConj] at hw ⊢
  rw [hw] at this
  exact this.symm

theorem isRealCoeff_duh (ν : ℝ) {f : ℝ → Coeff d} {T : ℝ}
    (hr : ∀ σ ∈ Set.Icc 0 T, IsRealCoeff (f σ))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : IsRealCoeff (duh ν f t) := by
  intro k
  unfold duh
  rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
  have hs : σ ∈ Set.Icc 0 T := ⟨hσ.1.le, hσ.2.trans ht.2⟩
  rw [heatMult_neg, hr σ hs k, map_mul, Complex.conj_ofReal]

theorem exists_small_time (ν γ : ℝ) (hγ : γ < 1) (M : ℝ) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ M * Eker ν γ T₀ ≤ 1 / 2 := by
  have h : Tendsto (fun x => M * Eker ν γ x) (𝓝 0) (𝓝 (M * 0)) :=
    (Eker_tendsto ν γ hγ).const_mul M
  rw [mul_zero] at h
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp
    (h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
  refine ⟨ε / 2, by positivity, (hεP ?_).le⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  linarith

/-- **Local existence (coefficient level).**  There is `T₀ > 0` depending only on `R` (and on
`d, s, K, δ', V, ν`) such that every `ρ̂⁰ ∈ H^K` with `‖ρ̂⁰‖_{H^K} ≤ R` has a mild solution on
`[0,T₀]`, continuous into `H^K` with `sup ‖ρ̂(t)‖_{H^K} ≤ 2R`; it solves the integrated equation
and is real if `ρ̂⁰` and `V̂` are. -/
theorem local_exists_coeff {s K δ' : ℝ} {V : Torus d → ℝ} (H : LocalHyp d s K δ' V) (ν : ℝ)
    (hν : 0 < ν) (R : ℝ) (hR : 0 ≤ R) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ ρ₀ : Coeff d, MemHs K ρ₀ → hsNorm K ρ₀ ≤ R →
      ∃ ρc : ℝ → Coeff d, IsMFSolutionHKOn d s V ν K ρ₀ ρc T₀ ∧ IsMildOn d s V ν ρ₀ ρc T₀ ∧
        (∀ t ∈ Set.Icc 0 T₀, hsNorm K (ρc t) ≤ 2 * R) ∧
        (IsRealCoeff (coeffOf V) → IsRealCoeff ρ₀ → ∀ t ∈ Set.Icc 0 T₀, IsRealCoeff (ρc t)) := by
  have hδ1 : δ' < 1 := lt_of_lt_of_le H.hδ (min_le_right _ _)
  obtain ⟨A, hA0, hA⟩ := duh_nl_estimates H ν hν
  obtain ⟨T₀, hT₀, hsmall⟩ := exists_small_time ν ((2 - δ') / 2) (by linarith [H.hδ0])
    (A * (1 + 4 * R))
  refine ⟨T₀, hT₀, fun ρ₀ hρ₀ hn => ?_⟩
  obtain ⟨ρ, hgood, hP, hfix⟩ := picard_exists hν H.hδ0 hδ1 hA0 hA hR hT₀.le
    (by simpa [mul_assoc] using hsmall) hρ₀ hn
    (fun c => IsRealCoeff (coeffOf V) → IsRealCoeff ρ₀ → IsRealCoeff c)
    (fun _ h => h)
    (fun ρ hρ hρP t ht hVr hr0 => by
      refine isRealCoeff_add' (isRealCoeff_heatC ν t hr0) ?_
      exact isRealCoeff_duh ν (fun σ hσ => isRealCoeff_nl hVr (hρP σ hσ hVr hr0)) ht)
    (fun c L hlim hc hVr hr0 k => by
      have h1 : Tendsto (fun n => c n (-k)) atTop (𝓝 (L (-k))) := hlim (-k)
      have h2 : Tendsto (fun n => c n (-k)) atTop (𝓝 (starRingEnd ℂ (L k))) := by
        have := (Complex.continuous_conj.tendsto _).comp (hlim k)
        refine this.congr fun n => ?_
        simp only [Function.comp_apply]
        exact (hc n hVr hr0 k).symm
      exact tendsto_nhds_unique h1 h2)
  have hint : ∀ k, IntegrableOn (fun σ => nlCoeff d s V (ρ σ) k) (Set.Icc 0 T₀) := fun k =>
    (continuousOn_mode (nl_cont H hgood.1) k).integrableOn_Icc
  have hmild : IsMildOn d s V ν ρ₀ ρ T₀ := by
    intro k t ht
    have := congrFun (hfix t ht) k
    rw [← this]
    simp only [phi, heatC, duh, Pi.add_apply]
  have hint' : ∀ k, ∀ t ∈ Set.Icc 0 T₀,
      IntegrableOn (fun σ => mfRhsCoeff d s V ν (ρ σ) k) (Set.Icc 0 t) := by
    intro k t ht
    have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T₀ := Set.Icc_subset_Icc le_rfl ht.2
    have : IntegrableOn (fun σ => -((ν * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) : ℝ) : ℂ) * ρ σ k +
        nlCoeff d s V (ρ σ) k) (Set.Icc 0 t) := by
      refine IntegrableOn.add ?_ ((hint k).mono_set hsub)
      exact (continuousOn_const.mul ((continuousOn_mode hgood.1 k).mono hsub)).integrableOn_Icc
    exact this.congr_fun (fun σ _ => (mfRhsCoeff_mode d s V ν (ρ σ) k).symm) measurableSet_Icc
  have h0 : ρ 0 = ρ₀ := by
    have h := hfix 0 ⟨le_rfl, hT₀.le⟩
    rw [← h]
    funext k
    simp [phi, heatC, duh, heatMult]
  refine ⟨ρ, ⟨h0, hgood.1, hint', ?_⟩, hmild, hgood.2, fun hVr hr0 t ht => hP t ht hVr hr0⟩
  exact (integrated_iff_mild_Icc hT₀.le hgood.1 hint).mpr hmild

/-! ### Uniqueness: an exponentially weighted singular Gronwall -/

theorem kappa_integrable_tau (ν γ : ℝ) (hν : 0 < ν) (hγ : γ < 1) (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun τ => 1 + (ν * τ) ^ (-γ)) volume 0 T := by
  have h := (kappa_integral ν hν γ hγ T hT).1
  have := h.comp_sub_left T
  simpa using this.symm

theorem exp_kernel_small (ν γ : ℝ) (hν : 0 < ν) (hγ : γ < 1) (T : ℝ) (hT : 0 ≤ T) (c : ℝ) :
    ∃ lam : ℝ, c * ∫ τ in (0 : ℝ)..T, (1 + (ν * τ) ^ (-γ)) * Real.exp (-lam * τ) ≤ 1 / 2 := by
  have hlim : Tendsto (fun n : ℕ => ∫ τ in (0 : ℝ)..T, (1 + (ν * τ) ^ (-γ)) * Real.exp (-(n : ℝ) * τ))
      atTop (𝓝 (∫ τ in (0 : ℝ)..T, (0 : ℝ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun τ => 1 + (ν * τ) ^ (-γ)) (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_)
      (kappa_integrable_tau ν γ hν hγ T hT) ?_
    · exact (by fun_prop : Measurable fun τ : ℝ => (1 + (ν * τ) ^ (-γ)) * Real.exp (-(n : ℝ) * τ)).aestronglyMeasurable
    · refine Eventually.of_forall fun τ hτ => ?_
      rw [Set.uIoc_of_le hT] at hτ
      have h1 : 0 ≤ (ν * τ) ^ (-γ) := Real.rpow_nonneg (mul_nonneg hν.le hτ.1.le) _
      have h2 : Real.exp (-(n : ℝ) * τ) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [hτ.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
        abs_of_pos (Real.exp_pos _)]
      calc _ ≤ (1 + (ν * τ) ^ (-γ)) * 1 := mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = _ := mul_one _
    · refine Eventually.of_forall fun τ hτ => ?_
      rw [Set.uIoc_of_le hT] at hτ
      have h3 : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * τ)) atTop (𝓝 0) := by
        have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_natCast_atTop_atTop.atTop_mul_const hτ.1)
        refine this.congr fun n => ?_
        simp only [Function.comp_apply]; ring_nf
      simpa using h3.const_mul (1 + (ν * τ) ^ (-γ))
  simp only [intervalIntegral.integral_zero] at hlim
  have h2 := hlim.const_mul c
  rw [mul_zero] at h2
  obtain ⟨n, hn⟩ := (h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  exact ⟨n, hn.le⟩

/-- Singular Gronwall inequality, in the form needed for uniqueness: a nonnegative continuous
`W` with `W(t) ≤ ∫₀ᵗ c (1 + (ν(t-σ))^{-γ}) W(σ) dσ` vanishes (`γ < 1`). -/
theorem weighted_gronwall (ν γ c : ℝ) (hν : 0 < ν) (hγ : γ < 1) (hc : 0 ≤ c) (T : ℝ) (hT : 0 ≤ T)
    (W : ℝ → ℝ) (hW : ContinuousOn W (Set.Icc 0 T)) (hW0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ W t)
    (h : ∀ t ∈ Set.Icc 0 T,
      W t ≤ ∫ σ in (0 : ℝ)..t, c * (1 + (ν * (t - σ)) ^ (-γ)) * W σ) :
    ∀ t ∈ Set.Icc 0 T, W t = 0 := by
  obtain ⟨lam, hlam⟩ := exp_kernel_small ν γ hν hγ T hT c
  have hexpc : Continuous fun σ : ℝ => Real.exp (-lam * σ) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hexpc' : Continuous fun σ : ℝ => Real.exp (lam * σ) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  obtain ⟨ts, hts, hmax⟩ := isCompact_Icc.exists_isMaxOn (⟨0, le_rfl, hT⟩ : (Set.Icc (0 : ℝ) T).Nonempty)
    (f := fun σ => Real.exp (-lam * σ) * W σ) (hexpc.continuousOn.mul hW)
  set M : ℝ := Real.exp (-lam * ts) * W ts with hM
  have hM0 : 0 ≤ M := mul_nonneg (Real.exp_pos _).le (hW0 ts hts)
  have hWM : ∀ σ ∈ Set.Icc 0 T, W σ ≤ M * Real.exp (lam * σ) := by
    intro σ hσ
    have h1 : Real.exp (-lam * σ) * W σ ≤ M := hmax hσ
    have h2 : W σ = Real.exp (lam * σ) * (Real.exp (-lam * σ) * W σ) := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [h2, mul_comm M]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have hsub : Set.Icc 0 ts ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl hts.2
  obtain ⟨hκ, -⟩ := kappa_integral ν hν γ hγ ts hts.1
  have hLint : IntervalIntegrable (fun σ => c * (1 + (ν * (ts - σ)) ^ (-γ)) * W σ) volume 0 ts :=
    (hκ.const_mul c).mul_continuousOn (g := W)
      (by rw [Set.uIcc_of_le hts.1]; exact hW.mono hsub)
  have hRint : IntervalIntegrable (fun σ => c * (1 + (ν * (ts - σ)) ^ (-γ)) * (M * Real.exp (lam * σ)))
      volume 0 ts :=
    (hκ.const_mul c).mul_continuousOn (g := fun σ => M * Real.exp (lam * σ))
      (continuous_const.mul hexpc').continuousOn
  have h1 : W ts ≤ ∫ σ in (0 : ℝ)..ts, c * (1 + (ν * (ts - σ)) ^ (-γ)) * (M * Real.exp (lam * σ)) := by
    refine (h ts hts).trans (intervalIntegral.integral_mono_on hts.1 hLint hRint fun σ hσ => ?_)
    have : 0 ≤ (ν * (ts - σ)) ^ (-γ) := Real.rpow_nonneg (mul_nonneg hν.le (by linarith [hσ.2])) _
    exact mul_le_mul_of_nonneg_left (hWM σ (hsub hσ)) (mul_nonneg hc (by linarith))
  set G : ℝ → ℝ := fun τ => (1 + (ν * τ) ^ (-γ)) * Real.exp (-lam * τ) with hG
  have hcalc : ∫ σ in (0 : ℝ)..ts, c * (1 + (ν * (ts - σ)) ^ (-γ)) * (M * Real.exp (lam * σ)) =
      (M * Real.exp (lam * ts) * c) * ∫ τ in (0 : ℝ)..ts, G τ := by
    have e1 : ∀ σ : ℝ, c * (1 + (ν * (ts - σ)) ^ (-γ)) * (M * Real.exp (lam * σ)) =
        (M * Real.exp (lam * ts) * c) * G (ts - σ) := by
      intro σ
      have : Real.exp (lam * σ) = Real.exp (lam * ts) * Real.exp (-lam * (ts - σ)) := by
        rw [← Real.exp_add]; congr 1; ring
      simp only [hG]
      rw [this]; ring
    simp_rw [e1]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left G ts,
      sub_self, sub_zero]
  have hGnn : ∀ τ ∈ Set.Ioc (0 : ℝ) T, 0 ≤ G τ := by
    intro τ hτ
    have : 0 ≤ (ν * τ) ^ (-γ) := Real.rpow_nonneg (mul_nonneg hν.le hτ.1.le) _
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  have hGint : IntervalIntegrable G volume 0 T :=
    (kappa_integrable_tau ν γ hν hγ T hT).mul_continuousOn (g := fun τ => Real.exp (-lam * τ))
      hexpc.continuousOn
  have hJ : ∫ τ in (0 : ℝ)..ts, G τ ≤ ∫ τ in (0 : ℝ)..T, G τ :=
    intervalIntegral.integral_mono_interval le_rfl hts.1 hts.2
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hGnn)) hGint
  have hcJ : c * ∫ τ in (0 : ℝ)..ts, G τ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hJ hc).trans hlam
  rw [hcalc] at h1
  have h2 : M ≤ M * (c * ∫ τ in (0 : ℝ)..ts, G τ) := by
    have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-lam * ts)).le
    calc M = Real.exp (-lam * ts) * W ts := hM
      _ ≤ Real.exp (-lam * ts) * (M * Real.exp (lam * ts) * c * ∫ τ in (0 : ℝ)..ts, G τ) := this
      _ = M * (c * ∫ τ in (0 : ℝ)..ts, G τ) := by
        have : Real.exp (-lam * ts) * Real.exp (lam * ts) = 1 := by
          rw [← Real.exp_add]; simp
        calc _ = (Real.exp (-lam * ts) * Real.exp (lam * ts)) * (M * (c * ∫ τ in (0 : ℝ)..ts, G τ)) := by ring
          _ = _ := by rw [this, one_mul]
  have hMle : M ≤ 0 := by nlinarith
  intro t ht
  have h3 : Real.exp (-lam * t) * W t ≤ M := hmax ht
  have h4 : Real.exp (-lam * t) * W t ≤ 0 := h3.trans hMle
  have h5 := hW0 t ht
  have h6 : 0 ≤ Real.exp (-lam * t) * W t := mul_nonneg (Real.exp_pos _).le h5
  have h7 : Real.exp (-lam * t) * W t = 0 := le_antisymm h4 h6
  rcases mul_eq_zero.mp h7 with h8 | h8
  · exact absurd h8 (Real.exp_pos _).ne'
  · exact h8

/-- **Uniqueness in `C([0,T]; H^K)`** (coefficient level): two solutions of the integrated
equation on `[0,T]`, continuous into `H^K`, with the same initial data coincide.  The proof reduces to
the mild equation (`integrated_iff_mild_Icc`), the Duhamel estimate and the exponentially weighted
singular Gronwall inequality `weighted_gronwall` (no restart/iteration in time is needed). -/
theorem unique_on_Icc_coeff {s K δ' : ℝ} {V : Torus d → ℝ} (H : LocalHyp d s K δ' V) (ν : ℝ)
    (hν : 0 < ν) (T : ℝ) (ρc ρc' : ℝ → Coeff d) (h : ContinuousInHsOn K ρc (Set.Icc 0 T))
    (h' : ContinuousInHsOn K ρc' (Set.Icc 0 T)) (h0 : ρc 0 = ρc' 0)
    (heq : ∀ k, ∀ t ∈ Set.Icc 0 T, ρc t k = ρc 0 k + ∫ σ in (0 : ℝ)..t, mfRhsCoeff d s V ν (ρc σ) k)
    (heq' : ∀ k, ∀ t ∈ Set.Icc 0 T,
      ρc' t k = ρc' 0 k + ∫ σ in (0 : ℝ)..t, mfRhsCoeff d s V ν (ρc' σ) k) :
    ∀ t ∈ Set.Icc 0 T, ρc t = ρc' t := by
  intro t0 ht0
  have hT : 0 ≤ T := ht0.1.trans ht0.2
  have hδ0 := H.hδ0
  have hδ1 : δ' < 1 := lt_of_lt_of_le H.hδ (min_le_right _ _)
  have hcn := nl_cont H h
  have hcn' := nl_cont H h'
  have hint : ∀ k, IntegrableOn (fun σ => nlCoeff d s V (ρc σ) k) (Set.Icc 0 T) := fun k =>
    (continuousOn_mode hcn k).integrableOn_Icc
  have hint' : ∀ k, IntegrableOn (fun σ => nlCoeff d s V (ρc' σ) k) (Set.Icc 0 T) := fun k =>
    (continuousOn_mode hcn' k).integrableOn_Icc
  have hm := (integrated_iff_mild_Icc hT h hint).mp heq
  have hm' := (integrated_iff_mild_Icc hT h' hint').mp heq'
  rw [← h0] at hm'
  set f : ℝ → Coeff d := fun σ => nlCoeff d s V (ρc σ) with hf
  set g : ℝ → Coeff d := fun σ => nlCoeff d s V (ρc' σ) with hg
  have hdiff : ∀ t ∈ Set.Icc 0 T, ρc t - ρc' t = duh ν (fun σ => f σ - g σ) t := by
    intro t ht
    rw [duh_sub ν hcn hcn' ht]
    funext k
    simp only [Pi.sub_apply, duh]
    rw [hm k t ht, hm' k t ht]
    simp only [hf, hg]
    ring
  -- bounds
  obtain ⟨B1, hB10, hB1⟩ := exists_bound_hsNorm h
  obtain ⟨B2, hB20, hB2⟩ := exists_bound_hsNorm h'
  obtain ⟨C, hC0, hC⟩ := nl_lip H
  have hKab : K - 2 + δ' + (2 - δ') = K := by ring
  obtain ⟨Ch, hCh0, hCh⟩ := duh_bound (d := d) ν hν (K - 2 + δ') (2 - δ') K
    (by linarith) (by linarith) hKab
  set W : ℝ → ℝ := fun σ => hsNorm K (ρc σ - ρc' σ) with hWdef
  have hdc : ContinuousInHsOn K (fun σ => ρc σ - ρc' σ) (Set.Icc 0 T) := contInHs_sub h h'
  have hWc : ContinuousOn W (Set.Icc 0 T) := continuousOn_hsNorm hdc
  have hfc : ContinuousInHsOn (K - 2 + δ') (fun σ => f σ - g σ) (Set.Icc 0 T) :=
    contInHs_sub hcn hcn'
  have hfb : ∀ σ ∈ Set.Icc 0 T, hsNorm (K - 2 + δ') (f σ - g σ) ≤ C * (1 + B1 + B2) * W σ := by
    intro σ hσ
    refine (hC (ρc σ) (ρc' σ) (h.1 σ hσ) (h'.1 σ hσ)).2.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (hsNorm_nonneg _ _)
    exact mul_le_mul_of_nonneg_left (by linarith [hB1 σ hσ, hB2 σ hσ]) hC0
  have hW : ∀ t ∈ Set.Icc 0 T, W t = 0 := by
    refine weighted_gronwall ν ((2 - δ') / 2) (Ch * (C * (1 + B1 + B2))) hν (by linarith)
      (by positivity) T hT W hWc (fun t _ => hsNorm_nonneg _ _) ?_
    intro t ht
    have hs : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
    obtain ⟨-, hbd⟩ := hCh _ T hfc t ht
    rw [← hdiff t ht] at hbd
    refine hbd.trans ?_
    obtain ⟨hκ, -⟩ := kappa_integral ν hν ((2 - δ') / 2) (by linarith) t ht.1
    have hI1 : IntervalIntegrable (fun σ => Ch * (1 + (ν * (t - σ)) ^ (-((2 - δ') / 2))) *
        hsNorm (K - 2 + δ') (f σ - g σ)) volume 0 t :=
      (hκ.const_mul Ch).mul_continuousOn (g := fun σ => hsNorm (K - 2 + δ') (f σ - g σ))
        (by rw [Set.uIcc_of_le ht.1]; exact (continuousOn_hsNorm hfc).mono hs)
    have hI2 : IntervalIntegrable (fun σ => Ch * (C * (1 + B1 + B2)) *
        (1 + (ν * (t - σ)) ^ (-((2 - δ') / 2))) * W σ) volume 0 t := by
      have := ((hκ.const_mul (Ch * (C * (1 + B1 + B2)))).mul_continuousOn (g := W)
        (by rw [Set.uIcc_of_le ht.1]; exact hWc.mono hs))
      exact this
    refine intervalIntegral.integral_mono_on ht.1 hI1 hI2 fun σ hσ => ?_
    have hk : 0 ≤ (ν * (t - σ)) ^ (-((2 - δ') / 2)) :=
      Real.rpow_nonneg (mul_nonneg hν.le (by linarith [hσ.2])) _
    have := hfb σ (hs hσ)
    calc Ch * (1 + (ν * (t - σ)) ^ (-((2 - δ') / 2))) * hsNorm (K - 2 + δ') (f σ - g σ)
        ≤ Ch * (1 + (ν * (t - σ)) ^ (-((2 - δ') / 2))) * (C * (1 + B1 + B2) * W σ) :=
          mul_le_mul_of_nonneg_left this (mul_nonneg hCh0 (by linarith))
      _ = _ := by ring
  have hz := hW t0 ht0
  have hmem : MemHs K (ρc t0 - ρc' t0) := memHs_sub_aux (h.1 t0 ht0) (h'.1 t0 ht0)
  exact sub_eq_zero.mp (eq_zero_of_hsNorm_eq_zero hmem hz)

/-! ### The plan-level statements -/

/-- `V ∈ C^{K+2}` (`K` natural) gives a `LocalHyp` with the gain `δ' = min (d - s) 1 / 2`. -/
theorem localHyp_of_isCk (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 1 < K) {V : Torus d → ℝ} (hV : Torus.IsCk (K + 2) V) :
    LocalHyp d s (K : ℝ) (min ((d : ℝ) - s) 1 / 2) V := by
  have hpos : 0 < min ((d : ℝ) - s) 1 := lt_min (by linarith) one_pos
  have hmin1 : min ((d : ℝ) - s) 1 ≤ 1 := min_le_right _ _
  refine ⟨hd, hs0, hsd, hK, by positivity, by linarith, ?_⟩
  have h2 : Torus.IsCk (((K + 2 : ℕ) : WithTop ℕ∞)) V := by
    have : (((K + 2 : ℕ) : WithTop ℕ∞)) = (K : WithTop ℕ∞) + 2 := by push_cast; rfl
    rw [this]; exact hV
  have := MFSemigroup.memHs_nat_of_isCk (K + 2) V h2
  exact memHs_mono (by push_cast; linarith) this

/-- **Local existence** (plan statement `local_exists`, with the extra conclusions `‖ρ̂(t)‖ ≤ 2R`
and the `[0,T₀]` solution structure): `T₀` depends only on an upper bound `R` for
`‖ρ̂⁰‖_{H^K}` (and on `d, s, K, V, ν`). -/
theorem local_exists (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 1 < K) (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ) (hν : 0 < ν)
    (R : ℝ) : ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ ρ₀ : Torus d → ℝ, MemSobolev K ρ₀ → hsNorm K (coeffOf ρ₀) ≤ R →
      ∃ ρc : ℝ → Coeff d, ρc 0 = coeffOf ρ₀ ∧ ContinuousInHsOn K ρc (Set.Icc 0 T₀) ∧
        (∀ t ∈ Set.Icc 0 T₀, IsRealCoeff (ρc t)) ∧
        (∀ k, ∀ t ∈ Set.Icc 0 T₀,
          ρc t k = coeffOf ρ₀ k + ∫ σ in (0 : ℝ)..t, mfRhsCoeff d s V ν (ρc σ) k) ∧
        (∀ t ∈ Set.Icc 0 T₀, hsNorm K (ρc t) ≤ 2 * R) ∧
        IsMFSolutionHKOn d s V ν K (coeffOf ρ₀) ρc T₀ := by
  have H := localHyp_of_isCk hd hs0 hsd K hK hV
  obtain ⟨T₀, hT₀, hex⟩ := local_exists_coeff H ν hν (max R 0) (le_max_right _ _)
  refine ⟨T₀, hT₀, fun ρ₀ hρ₀ hn => ?_⟩
  have hR0 : 0 ≤ R := (hsNorm_nonneg _ _).trans hn
  have hmem : MemHs (K : ℝ) (coeffOf ρ₀) := (hsNormSq_coeffOf (K : ℝ) ρ₀ hρ₀).1
  obtain ⟨ρc, hsol, -, hb, hreal⟩ := hex (coeffOf ρ₀) hmem (hn.trans (le_max_left _ _))
  have hVint : Integrable V := by
    have hVc : Continuous V := continuous_of_isCk (hV.of_le (by exact_mod_cast
      (show (1 : ℕ) ≤ K + 2 by omega)))
    exact hVc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hρint : Integrable ρ₀ := hρ₀.1.integrable one_le_two
  refine ⟨ρc, hsol.init, hsol.cont, hreal (isRealCoeff_coeffOf V hVint) (isRealCoeff_coeffOf ρ₀ hρint),
    hsol.eq, fun t ht => by rw [max_eq_left hR0] at hb; exact hb t ht, hsol⟩

/-- **Uniqueness in `C([0,T];H^K)`** (corrected variant of the plan's `unique_on_Icc`: the plan has
`V ∈ C²`, which does not put `∂_jV` in `H^{K-1+δ'}`; here `V ∈ C^{K+2}`, matching
`FiniteRegHyp.hV`).  Two solutions of the integrated equation on `[0,T]`, continuous into `H^K`,
with the same initial datum coincide. -/
theorem unique_on_Icc' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 1 < K) (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (ρc ρc' : ℝ → Coeff d) (h : ContinuousInHsOn K ρc (Set.Icc 0 T))
    (h' : ContinuousInHsOn K ρc' (Set.Icc 0 T)) (h0 : ρc 0 = ρc' 0)
    (heq : ∀ k, ∀ t ∈ Set.Icc 0 T, ρc t k = ρc 0 k + ∫ σ in (0 : ℝ)..t, mfRhsCoeff d s V ν (ρc σ) k)
    (heq' : ∀ k, ∀ t ∈ Set.Icc 0 T, ρc' t k = ρc' 0 k + ∫ σ in (0 : ℝ)..t, mfRhsCoeff d s V ν (ρc' σ) k) :
    ∀ t ∈ Set.Icc 0 T, ρc t = ρc' t :=
  unique_on_Icc_coeff (localHyp_of_isCk hd hs0 hsd K hK hV) ν hν T ρc ρc' h h' h0 heq heq'

/-! ### Time regularity of the local solution (the `H^{K-2}` clauses of `finite_reg_exists_unique`) -/

theorem hsNorm_smul (m : ℝ) (c : ℂ) (x : Coeff d) :
    hsNorm m (fun k => c * x k) = ‖c‖ * hsNorm m x := by
  unfold hsNorm hsNormSq
  have : ∀ k : Lattice d, sobWeight m k * ‖c * x k‖ ^ 2 = ‖c‖ ^ 2 * (sobWeight m k * ‖x k‖ ^ 2) := by
    intro k; rw [norm_mul]; ring
  simp_rw [this]
  rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem hsNorm_mono_idx {m n : ℝ} (hmn : m ≤ n) {c : Coeff d} (hc : MemHs n c) :
    hsNorm m c ≤ hsNorm n c := by
  unfold hsNorm
  exact Real.sqrt_le_sqrt (hsNormSq_mono hmn hc)

theorem contInHs_mono_idx {m n : ℝ} (hmn : m ≤ n) {F : ℝ → Coeff d} {S : Set ℝ}
    (hF : ContinuousInHsOn n F S) : ContinuousInHsOn m F S := by
  refine ⟨fun τ hτ => memHs_mono hmn (hF.1 τ hτ), fun τ0 hτ0 => ?_⟩
  refine squeeze_zero' (Eventually.of_forall fun _ => hsNorm_nonneg _ _)
    (eventually_nhdsWithin_of_forall fun τ hτ => ?_) (hF.2 τ0 hτ0)
  exact hsNorm_mono_idx hmn (memHs_sub_aux (hF.1 τ hτ) (hF.1 τ0 hτ0))

theorem contInHs_mono_set {m : ℝ} {F : ℝ → Coeff d} {S S' : Set ℝ} (hS : S' ⊆ S)
    (hF : ContinuousInHsOn m F S) : ContinuousInHsOn m F S' :=
  ⟨fun τ hτ => hF.1 τ (hS hτ), fun τ0 hτ0 => (hF.2 τ0 (hS hτ0)).mono_left (nhdsWithin_mono _ hS)⟩

/-- The scaled Laplacian `c ↦ (ν Δ c)^` loses two derivatives with norm `≤ |ν|`. -/
def lapν (ν : ℝ) (c : Coeff d) : Coeff d := fun k => (ν : ℂ) * laplaceCoeff c k

theorem hs_lapν (ν m : ℝ) (c : Coeff d) (hc : MemHs m c) :
    MemHs (m + -2) (lapν ν c) ∧ hsNorm (m + -2) (lapν ν c) ≤ |ν| * hsNorm m c := by
  have := hs_mult (fun k : Lattice d => (ν : ℂ) * (-((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ)))
    m (-2) |ν| (abs_nonneg ν) (fun k => ?_) c hc
  · have e : lapν ν c = fun k => ((ν : ℂ) * (-((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ))) * c k := by
      funext k; simp only [lapν, laplaceCoeff]; ring
    rw [e]
    exact ⟨this.1, this.2⟩
  · set x : ℝ := 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with hx
    have hx0 : 0 ≤ x := by positivity
    have h1 : ‖(ν : ℂ) * (-((x : ℝ) : ℂ))‖ ^ 2 = ν ^ 2 * x ^ 2 := by
      rw [norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, mul_pow, sq_abs, sq_abs]
    have h2 : sobWeight (-2) k = ((1 + x) ^ 2)⁻¹ := by
      unfold sobWeight
      rw [← hx, Real.rpow_neg (by linarith), Real.rpow_two]
    rw [h1, h2, sq_abs]
    have h3 : x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
    have h4 : 0 < (1 + x) ^ 2 := by positivity
    calc ((1 + x) ^ 2)⁻¹ * (ν ^ 2 * x ^ 2) = ν ^ 2 * (x ^ 2 / (1 + x) ^ 2) := by
          field_simp
      _ ≤ ν ^ 2 * 1 := mul_le_mul_of_nonneg_left ((div_le_one h4).mpr h3) (sq_nonneg _)
      _ = ν ^ 2 := mul_one _

theorem lapν_sub (ν : ℝ) (a b : Coeff d) : lapν ν a - lapν ν b = lapν ν (a - b) := by
  funext k; simp only [lapν, laplaceCoeff, Pi.sub_apply]; ring

theorem cont_lapν {K : ℝ} (ν : ℝ) {ρ : ℝ → Coeff d} {S : Set ℝ} (hρ : ContinuousInHsOn K ρ S) :
    ContinuousInHsOn (K - 2) (fun t => lapν ν (ρ t)) S := by
  refine ⟨fun τ hτ => by simpa [sub_eq_add_neg] using (hs_lapν ν K _ (hρ.1 τ hτ)).1, fun τ0 hτ0 => ?_⟩
  have hx := hρ.2 τ0 hτ0
  have h := hx.const_mul |ν|
  rw [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun _ => hsNorm_nonneg _ _)
    (eventually_nhdsWithin_of_forall fun τ hτ => ?_) h
  rw [lapν_sub]
  have := (hs_lapν ν K _ (memHs_sub_aux (hρ.1 τ hτ) (hρ.1 τ0 hτ0))).2
  simpa [sub_eq_add_neg] using this

theorem cont_mfRhs {s K δ' : ℝ} {V : Torus d → ℝ} (H : LocalHyp d s K δ' V) (ν : ℝ)
    {ρ : ℝ → Coeff d} {S : Set ℝ} (hρ : ContinuousInHsOn K ρ S) :
    ContinuousInHsOn (K - 2) (fun t => mfRhsCoeff d s V ν (ρ t)) S := by
  have h1 := cont_lapν ν hρ
  have h2 := contInHs_mono_idx (m := K - 2) (by linarith [H.hδ0]) (nl_cont H hρ)
  have e : (fun t => mfRhsCoeff d s V ν (ρ t)) = fun t => lapν ν (ρ t) + nlCoeff d s V (ρ t) := by
    funext t k; exact mfRhsCoeff_eq d s V ν (ρ t) k
  rw [e]
  exact contInHs_add h1 h2

theorem avg_norm_le (m : ℝ) (F' : ℝ → Coeff d) {a b e : ℝ} (hab : a < b)
    (hF' : ContinuousInHsOn m F' (Set.Icc a b)) (he : ∀ σ ∈ Set.Icc a b, hsNorm m (F' σ) ≤ e) :
    hsNorm m (fun k => (((1 / (b - a) : ℝ)) : ℂ) * ∫ σ in a..b, F' σ k) ≤ e := by
  have hba : 0 < b - a := by linarith
  rw [hsNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  obtain ⟨-, h2⟩ := hsNorm_intervalIntegral_le_of_cont m F' hab.le hF'
  have hnc : ContinuousOn (fun σ => hsNorm m (F' σ)) (Set.Icc a b) := continuousOn_hsNorm hF'
  have h3 : ∫ σ in a..b, hsNorm m (F' σ) ≤ ∫ σ in a..b, e :=
    intervalIntegral.integral_mono_on hab.le
      (hnc.intervalIntegrable_of_Icc hab.le) intervalIntegrable_const he
  rw [intervalIntegral.integral_const, smul_eq_mul] at h3
  calc 1 / (b - a) * hsNorm m (fun k => ∫ σ in a..b, F' σ k)
      ≤ 1 / (b - a) * ((b - a) * e) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
    _ = e := by field_simp

theorem diff_eq_integral {s K : ℝ} {V : Torus d → ℝ} {ν T : ℝ} {ρ₀ : Coeff d} {ρc : ℝ → Coeff d}
    (hsol : IsMFSolutionHKOn d s V ν K ρ₀ ρc T) {t t' : ℝ} (ht : t ∈ Set.Icc 0 T)
    (ht' : t' ∈ Set.Icc 0 T) (k : Lattice d) :
    ρc t' k - ρc t k = ∫ σ in t..t', mfRhsCoeff d s V ν (ρc σ) k := by
  have h1 : IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρc σ) k) volume 0 t' :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht'.1).mpr (hsol.integrable k t' ht')
  have h2 : IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρc σ) k) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr (hsol.integrable k t ht)
  rw [hsol.eq k t' ht', hsol.eq k t ht, add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left h1 h2

theorem quot_mode {s K : ℝ} {V : Torus d → ℝ} {ν T : ℝ} {ρ₀ : Coeff d} {ρc : ℝ → Coeff d}
    (hsol : IsMFSolutionHKOn d s V ν K ρ₀ ρc T) {t t' : ℝ} (ht : t ∈ Set.Icc 0 T)
    (ht' : t' ∈ Set.Icc 0 T) (hne : t' ≠ t) (k : Lattice d) :
    (ρc t' k - ρc t k) / ((t' - t : ℝ) : ℂ) - mfRhsCoeff d s V ν (ρc t) k =
      (((1 / (max t t' - min t t') : ℝ)) : ℂ) *
        ∫ σ in min t t'..max t t', (mfRhsCoeff d s V ν (ρc σ) k - mfRhsCoeff d s V ν (ρc t) k) := by
  have hT : T ∈ Set.Icc 0 T := ⟨ht.1.trans ht.2, le_rfl⟩
  have hu := hsol.integrable k T hT
  have hI : ∀ a b : ℝ, a ∈ Set.Icc 0 T → b ∈ Set.Icc 0 T →
      IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρc σ) k) volume a b := fun a b ha hb =>
    (hu.mono_set (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  have hsplit : ∀ a b : ℝ, a ∈ Set.Icc 0 T → b ∈ Set.Icc 0 T → a < b →
      (((1 / (b - a) : ℝ)) : ℂ) * ∫ σ in a..b, (mfRhsCoeff d s V ν (ρc σ) k - mfRhsCoeff d s V ν (ρc t) k) =
      ((((1 / (b - a) : ℝ)) : ℂ)) * (∫ σ in a..b, mfRhsCoeff d s V ν (ρc σ) k) -
        mfRhsCoeff d s V ν (ρc t) k := by
    intro a b ha hb hab
    rw [intervalIntegral.integral_sub (hI a b ha hb) intervalIntegrable_const,
      intervalIntegral.integral_const, Complex.real_smul]
    have hc : ((b - a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hab).ne'
    rw [one_div, Complex.ofReal_inv]
    set c : ℂ := ((b - a : ℝ) : ℂ) with hcdef
    have e2 : ((b - a : ℝ) • mfRhsCoeff d s V ν (ρc t) k) = c * mfRhsCoeff d s V ν (ρc t) k := by
      rw [Complex.real_smul]
    field_simp
  rcases lt_or_gt_of_ne hne with h | h
  · -- t' < t
    rw [min_eq_right h.le, max_eq_left h.le, hsplit t' t ht' ht h, diff_eq_integral hsol ht ht' k,
      intervalIntegral.integral_symm]
    have hc : ((t - t' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr h).ne'
    have e : ((t' - t : ℝ) : ℂ) = -((t - t' : ℝ) : ℂ) := by push_cast; ring
    rw [e, one_div, Complex.ofReal_inv]
    set c : ℂ := ((t - t' : ℝ) : ℂ) with hcdef
    field_simp
  · -- t < t'
    rw [min_eq_left h.le, max_eq_right h.le, hsplit t t' ht ht' h, diff_eq_integral hsol ht ht' k]
    have : (t' - t : ℝ) ≠ 0 := (sub_pos.mpr h).ne'
    push_cast
    field_simp

/-- Difference quotients of the local solution converge in `H^{K-2}` to `mfRhsCoeff (ρ̂(t))`. -/
theorem diffquot_tendsto {s K δ' : ℝ} {V : Torus d → ℝ} (H : LocalHyp d s K δ' V) {ν T : ℝ}
    {ρ₀ : Coeff d} {ρc : ℝ → Coeff d} (hsol : IsMFSolutionHKOn d s V ν K ρ₀ ρc T) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    Tendsto (fun t' => hsNorm (K - 2)
        (fun k => (ρc t' k - ρc t k) / ((t' - t : ℝ) : ℂ) - mfRhsCoeff d s V ν (ρc t) k))
      (𝓝[Set.Icc 0 T \ {t}] t) (𝓝 0) := by
  have hF := cont_mfRhs H ν hsol.cont
  set F : ℝ → Coeff d := fun σ => mfRhsCoeff d s V ν (ρc σ) with hFdef
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hηP⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hF.2 t ht) (ε / 2) (by positivity)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t hη), self_mem_nhdsWithin]
    with t' hball hmem
  obtain ⟨ht'T, ht'ne⟩ := hmem
  have ht'ne' : t' ≠ t := fun h => ht'ne h
  have hdist : |t' - t| < η := by simpa [Real.dist_eq] using hball
  set a := min t t' with ha
  set b := max t t' with hb
  have hab : a < b := by
    rcases lt_or_gt_of_ne ht'ne' with h | h
    · rw [ha, hb, min_eq_right h.le, max_eq_left h.le]; exact h
    · rw [ha, hb, min_eq_left h.le, max_eq_right h.le]; exact h
  have haT : a ∈ Set.Icc 0 T := by
    rcases le_total t t' with h | h
    · rw [ha, min_eq_left h]; exact ht
    · rw [ha, min_eq_right h]; exact ht'T
  have hbT : b ∈ Set.Icc 0 T := by
    rcases le_total t t' with h | h
    · rw [hb, max_eq_right h]; exact ht'T
    · rw [hb, max_eq_left h]; exact ht
  have hsub : Set.Icc a b ⊆ Set.Icc 0 T := Set.Icc_subset_Icc haT.1 hbT.2
  have hF' : ContinuousInHsOn (K - 2) (fun σ => F σ - F t) (Set.Icc a b) :=
    contInHs_sub (contInHs_mono_set hsub hF) (contInHs_const (hF.1 t ht) _)
  have hq : (fun k => (ρc t' k - ρc t k) / ((t' - t : ℝ) : ℂ) - mfRhsCoeff d s V ν (ρc t) k) =
      fun k => (((1 / (b - a) : ℝ)) : ℂ) * ∫ σ in a..b, (F σ - F t) k := by
    funext k
    exact quot_mode hsol ht ht'T ht'ne' k
  rw [hq, Real.dist_eq, sub_zero]
  have hle := avg_norm_le (K - 2) (fun σ => F σ - F t) (e := ε / 2) hab hF' (fun σ hσ => by
    have hσT := hsub hσ
    have hdσ : dist σ t < η := by
      rw [Real.dist_eq]
      refine lt_of_le_of_lt ?_ hdist
      rcases le_total t t' with h | h
      · rw [abs_of_nonneg (by linarith : 0 ≤ t' - t)]
        rw [ha, hb, min_eq_left h, max_eq_right h] at hσ
        rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2]
      · rw [abs_of_nonpos (by linarith : t' - t ≤ 0)]
        rw [ha, hb, min_eq_right h, max_eq_left h] at hσ
        rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2]
    have := hηP hσT hdσ
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNorm_nonneg _ _)] at this
    exact this.le)
  rw [abs_of_nonneg (hsNorm_nonneg _ _)]
  linarith

/-- **Time-regularity clauses on `[0,T]`** (local version of the last clauses of
`finite_reg_exists_unique`): `t ↦ 𝒩ρ̂(t)` is norm-continuous in `H^{K-2}` and the difference quotients
of `ρ̂` converge in `H^{K-2}` to `𝒩ρ̂(t)` at every `t ∈ [0,T]` (one-sided at the endpoints). -/
theorem local_time_reg {s K δ' : ℝ} {V : Torus d → ℝ} (H : LocalHyp d s K δ' V) {ν T : ℝ}
    {ρ₀ : Coeff d} {ρc : ℝ → Coeff d} (hsol : IsMFSolutionHKOn d s V ν K ρ₀ ρc T) :
    ContinuousInHsOn (K - 2) (fun t => mfRhsCoeff d s V ν (ρc t)) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, Tendsto (fun t' => hsNorm (K - 2)
        (fun k => (ρc t' k - ρc t k) / ((t' - t : ℝ) : ℂ) - mfRhsCoeff d s V ν (ρc t) k))
        (𝓝[Set.Icc 0 T \ {t}] t) (𝓝 0) :=
  ⟨cont_mfRhs H ν hsol.cont, fun _ ht => diffquot_tendsto H hsol ht⟩

/-- A global solution restricts to a solution on every `[0,T]`. -/
theorem IsMFSolutionHK.toOn {s K : ℝ} {V : Torus d → ℝ} {ν : ℝ} {ρ₀ : Torus d → ℝ}
    {ρc : ℝ → Coeff d} (h : IsMFSolutionHK d s V ν K ρ₀ ρc) {T : ℝ} :
    IsMFSolutionHKOn d s V ν K (coeffOf ρ₀) ρc T :=
  ⟨h.init, contInHs_mono_set (fun _ hx => hx.1) h.cont, fun k t ht => h.integrable k t ht.1,
    fun k t ht => h.eq k t ht.1⟩

/-- A path which is a solution on every `[0,T]` is a global solution. -/
theorem isMFSolutionHK_of_forall_on {s K : ℝ} {V : Torus d → ℝ} {ν : ℝ} {ρ₀ : Torus d → ℝ}
    {ρc : ℝ → Coeff d} (h : ∀ T, 0 ≤ T → IsMFSolutionHKOn d s V ν K (coeffOf ρ₀) ρc T) :
    IsMFSolutionHK d s V ν K ρ₀ ρc := by
  refine ⟨(h 0 le_rfl).init, ⟨fun τ hτ => (h τ hτ).cont.1 τ ⟨hτ, le_rfl⟩, fun τ0 hτ0 => ?_⟩,
    fun k t ht => (h t ht).integrable k t ⟨ht, le_rfl⟩, fun k t ht => (h t ht).eq k t ⟨ht, le_rfl⟩⟩
  have hmem : Set.Icc 0 (τ0 + 1) ∈ 𝓝[Set.Ici 0] τ0 :=
    mem_nhdsWithin.mpr ⟨Set.Iio (τ0 + 1), isOpen_Iio, by simp, fun x hx => ⟨hx.2, hx.1.le⟩⟩
  exact (((h (τ0 + 1) (by linarith [show (0 : ℝ) ≤ τ0 from hτ0])).cont.2 τ0
    ⟨hτ0, by linarith⟩)).mono_left (nhdsWithin_le_of_mem hmem)

end MFLocal
end HRS.PDE
