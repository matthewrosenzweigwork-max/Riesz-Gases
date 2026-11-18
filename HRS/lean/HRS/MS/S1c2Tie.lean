import HRS.MS.S1c2Aux3
import HRS.Whole.AppendixBEnergy

/-!
# S1C2 tie: S.A.1 claim 2 (`commutatorNorm_le`) from `fracLp_rep` and the Sobolev embedding

Statements of this file:

* `s1c2_params`: for `0 ≤ s < d - 2` and every `c : DecayingDensity d s`: `r_c > 0`, `p_c > 1`, and
  `⌊r_c⌋ + 2 ≤ m_c` (the central-difference order `ℓ = ⌊r_c⌋ + 1` is at most `m_c - 1`).
* `s1c2_transport_bound`: the transport bound for `v = M^T ∇f`, given the sup bound
  `‖D²f‖_∞ ≤ C₁ ‖f‖_{W^{m_c,p_c}}` as a hypothesis (the content of the Sobolev embedding, claim 1).
* `commutatorNorm_le_proof`: the statement of `HRS.Whole.DecayingDensity.commutatorNorm_le` with the Sobolev
  embedding `sobolev_embeds_cb` (claim 1) as hypothesis `hmorrey`; the orchestrator ties it after claim 1 lands.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace HRS.S1C2

open HRS.Whole HRS.U8

variable {d : ℕ}

theorem s1c2_params {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (c : DecayingDensity d s) :
    0 < c.regularity ∧ 1 < c.integrability ∧ ⌊c.regularity⌋₊ + 2 ≤ c.sobolevIndex := by
  have hd2 : (2 : ℝ) < d := by linarith
  have key : 0 < c.regularity ∧ 1 < c.integrability ∧ c.regularity < (d : ℝ) / 2 + 1 := by
    cases c with
    | sharp a ha =>
      obtain ⟨h1, h2⟩ := ha
      have h3 := (lt_min_iff.1 h2).1
      simp only [DecayingDensity.regularity, DecayingDensity.integrability]
      refine ⟨by linarith, ?_, by linarith⟩
      rw [lt_div_iff₀ (by linarith)]
      linarith
    | lower hs =>
      simp only [DecayingDensity.regularity, DecayingDensity.integrability]
      refine ⟨by linarith, ?_, by linarith⟩
      rw [lt_div_iff₀ (by linarith)]
      linarith
  obtain ⟨h1, h2, h3⟩ := key
  refine ⟨h1, h2, ?_⟩
  have hfl : ⌊c.regularity⌋₊ < d / 2 + 2 := by
    rw [Nat.floor_lt h1.le]
    have : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : d ≤ 2 * (d / 2) + 1)
    push_cast
    linarith
  unfold DecayingDensity.sobolevIndex mStar
  omega

/-- The operator norm of `v ↦ M^T v`. -/
def s1c2_TM (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M.transpose)‖

theorem s1c2_comp (M : Matrix (Fin d) (Fin d) ℝ) (g : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (Matrix.toEuclideanLin M.transpose g) i =
      inner ℝ g (Matrix.toEuclideanLin M (EuclideanSpace.single i 1)) := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.inner_apply,
    Matrix.transpose_apply]

theorem s1c2_vi_eq (M : Matrix (Fin d) (Fin d) ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    (Matrix.toEuclideanLin M.transpose (gradient f x)) i =
      fderiv ℝ f x (Matrix.toEuclideanLin M (EuclideanSpace.single i 1)) := by
  rw [s1c2_comp]
  unfold gradient
  exact InnerProductSpace.toDual_symm_apply

theorem s1c2_vi_norm_bound {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (a : EuclideanSpace ℝ (Fin d)) (k : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ f y a) x‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ (k + 1) f x‖ := by
  have hG : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h := norm_iteratedFDeriv_clm_apply_const (c := a) (hG.contDiffAt (x := x)) (n := k)
    (N := ∞) (by exact_mod_cast le_top)
  rwa [norm_iteratedFDeriv_fderiv] at h

theorem s1c2_vi_contDiff {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (a : EuclideanSpace ℝ (Fin d)) : ContDiff ℝ ∞ (fun y => fderiv ℝ f y a) := by
  have hG : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact (ContinuousLinearMap.apply ℝ ℝ a).contDiff.comp hG

theorem s1c2_lip {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (M : Matrix (Fin d) (Fin d) ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hD2 : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ B) :
    ∃ L : ℝ≥0, (L : ℝ) = s1c2_TM M * B ∧
      LipschitzWith L (fun x => Matrix.toEuclideanLin M.transpose (gradient f x)) := by
  set T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M.transpose) with hT
  have hG : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hGd : Differentiable ℝ (fderiv ℝ f) := hG.differentiable (by simp)
  have hGl : LipschitzWith B.toNNReal (fderiv ℝ f) := by
    refine lipschitzWith_of_nnnorm_fderiv_le hGd (fun x => ?_)
    have h1 : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B := by
      have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := x) (n := 1)
      rw [norm_iteratedFDeriv_one] at this
      rw [this]
      exact hD2 x
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hB]
    exact h1
  have hL : LipschitzWith (‖T‖₊ * (1 * B.toNNReal)) (T ∘ (InnerProductSpace.toDual ℝ
      (EuclideanSpace ℝ (Fin d))).symm ∘ fderiv ℝ f) :=
    T.lipschitz.comp ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.lipschitz.comp hGl)
  refine ⟨‖T‖₊ * (1 * B.toNNReal), ?_, hL⟩
  push_cast
  rw [Real.coe_toNNReal _ hB]
  unfold s1c2_TM
  ring

theorem s1c2_vi_lp {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (a : EuclideanSpace ℝ (Fin d)) (k : ℕ) {p : ℝ}
    (hk : MemLp (iteratedFDeriv ℝ (k + 1) f) (ENNReal.ofReal p) volume) :
    MemLp (iteratedFDeriv ℝ k (fun y => fderiv ℝ f y a)) (ENNReal.ofReal p) volume ∧
      eLpNorm (iteratedFDeriv ℝ k (fun y => fderiv ℝ f y a)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ‖a‖ * eLpNorm (iteratedFDeriv ℝ (k + 1) f) (ENNReal.ofReal p) volume := by
  have hc : Continuous (iteratedFDeriv ℝ k (fun y => fderiv ℝ f y a)) :=
    (s1c2_vi_contDiff hf a).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hle : eLpNorm (iteratedFDeriv ℝ k (fun y => fderiv ℝ f y a)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ‖a‖ * eLpNorm (iteratedFDeriv ℝ (k + 1) f) (ENNReal.ofReal p) volume := by
    have h1 := eLpNorm_mono (p := ENNReal.ofReal p) (μ := volume) hc.aestronglyMeasurable
      (g := fun x => ‖a‖ • iteratedFDeriv ℝ (k + 1) f x) (fun x => by
        rw [norm_smul, norm_norm]
        exact s1c2_vi_norm_bound hf a k x)
    have h2 := eLpNorm_const_smul ‖a‖ (iteratedFDeriv ℝ (k + 1) f) (ENNReal.ofReal p)
      (volume : Measure (EuclideanSpace ℝ (Fin d)))
    rw [Real.enorm_eq_ofReal (norm_nonneg _)] at h2
    exact h1.trans (le_of_eq h2)
  exact ⟨lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hk), hle⟩

theorem s1c2_eLpNorm_iter0 (g : EuclideanSpace ℝ (Fin d) → ℝ) (hg : Continuous g)
    (q : ℝ≥0∞) :
    eLpNorm (iteratedFDeriv ℝ 0 g) q volume = eLpNorm g q volume :=
  eLpNorm_congr_norm_ae
    ((contDiff_zero.2 hg).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
    hg.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => norm_iteratedFDeriv_zero))

theorem s1c2_transport_bound {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (c : DecayingDensity d s) (M : Matrix (Fin d) (Fin d) ℝ)
    (hD2 : ∃ C₁ : ℝ, ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ f →
      (∀ j ≤ c.sobolevIndex, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖ ^ c.integrability)) →
      ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C₁ * sobolevWNorm c.sobolevIndex c.integrability f) :
    ∃ C : ℝ, ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ f →
      (∀ j ≤ c.sobolevIndex, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖ ^ c.integrability)) →
      HasFracTransportBound c.regularity c.integrability
        (fun x => Matrix.toEuclideanLin M.transpose (gradient f x))
        (C * sobolevWNorm c.sobolevIndex c.integrability f) := by
  have hd : 1 ≤ d := by
    have : (2 : ℝ) < d := by linarith
    have : 2 < d := by exact_mod_cast this
    omega
  obtain ⟨hr, hp, hm⟩ := s1c2_params hs0 hsd c
  have hp0 : 0 < c.integrability := by linarith
  obtain ⟨C0, hC0, hrep⟩ := fracLp_rep hd hr hp
  obtain ⟨C1, hC1⟩ := hD2
  set a : Fin d → EuclideanSpace ℝ (Fin d) := fun i =>
    Matrix.toEuclideanLin M (EuclideanSpace.single i 1) with ha
  set Sa : ℝ := ∑ i, ‖a i‖ with hSa
  have hSa0 : 0 ≤ Sa := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  refine ⟨s1c2_TM M * C1 + C0 * Sa, ?_⟩
  intro f hf hint
  set r := c.regularity with hrdef
  set p := c.integrability with hpdef
  set m := c.sobolevIndex with hmdef
  set n : ℕ → ℝ := fun j => (∫ x, ‖iteratedFDeriv ℝ j f x‖ ^ p) ^ (1 / p) with hn
  have hn0 : ∀ j, 0 ≤ n j := fun j =>
    Real.rpow_nonneg (integral_nonneg (fun x => by positivity)) _
  have hsob : sobolevWNorm m p f = ∑ j ∈ Finset.range (m + 1), n j := rfl
  set sob := sobolevWNorm m p f with hsobdef
  have hsob0 : 0 ≤ sob := by rw [hsob]; exact Finset.sum_nonneg (fun j _ => hn0 j)
  have hMem : ∀ j ≤ m, MemLp (iteratedFDeriv ℝ j f) (ENNReal.ofReal p) volume ∧
      eLpNorm (iteratedFDeriv ℝ j f) (ENNReal.ofReal p) volume = ENNReal.ofReal (n j) := by
    intro j hj
    have hc : Continuous (iteratedFDeriv ℝ j f) :=
      hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    have hmem : MemLp (iteratedFDeriv ℝ j f) (ENNReal.ofReal p) volume := by
      rw [← integrable_norm_rpow_iff hc.aestronglyMeasurable (ENNReal.ofReal_pos.2 hp0).ne'
        ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
      exact hint j hj
    refine ⟨hmem, ?_⟩
    rw [hmem.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le]
    simp only [hn, one_div]
  have hℓm : ⌊r⌋₊ + 1 + 1 ≤ m := by omega
  have hpair : n 1 + n (⌊r⌋₊ + 1 + 1) ≤ sob := by
    rw [hsob, ← Finset.sum_pair (f := n) (by omega : (1 : ℕ) ≠ ⌊r⌋₊ + 1 + 1)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hn0 j)
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rw [Finset.mem_range]
    omega
  have hB0 : 0 ≤ C1 * sob := (norm_nonneg _).trans (hC1 f hf hint 0)
  obtain ⟨L, hL, hLip⟩ := s1c2_lip hf M (C1 * sob) hB0 (hC1 f hf hint)
  have hcomp : ∀ i, ∃ wi : EuclideanSpace ℝ (Fin d) → ℝ, AEStronglyMeasurable wi volume ∧
      IsFracDerivRep r (fun x => fderiv ℝ f x (a i)) wi ∧
        eLpNorm wi (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (C0 * ‖a i‖ * sob) := by
    intro i
    have hv0 := s1c2_vi_lp hf (a i) 0 (p := p) (hMem 1 (by omega)).1
    have hv1 := s1c2_vi_lp hf (a i) (⌊r⌋₊ + 1) (p := p) (hMem _ hℓm).1
    have hvcd : ContDiff ℝ ((⌊r⌋₊ + 1 : ℕ) : WithTop ℕ∞) (fun x => fderiv ℝ f x (a i)) :=
      (s1c2_vi_contDiff hf (a i)).of_le (by exact_mod_cast le_top)
    have hvc : Continuous (fun x => fderiv ℝ f x (a i)) := (s1c2_vi_contDiff hf (a i)).continuous
    have eq0 := s1c2_eLpNorm_iter0 (fun x => fderiv ℝ f x (a i)) hvc (ENNReal.ofReal p)
    have hv0m : MemLp (fun x => fderiv ℝ f x (a i)) (ENNReal.ofReal p) volume := by
      unfold MemLp; rw [← eq0]; exact hv0.1
    obtain ⟨w, hwm, hw, -, hwb⟩ := hrep _ hvcd hv0m hv1.1
    refine ⟨w, hwm, hw, hwb.trans ?_⟩
    have e0 : eLpNorm (fun x => fderiv ℝ f x (a i)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ‖a i‖ * ENNReal.ofReal (n 1) := by
      rw [← eq0]
      refine hv0.2.trans ?_
      rw [(hMem 1 (by omega)).2]
    have e1 : eLpNorm (iteratedFDeriv ℝ (⌊r⌋₊ + 1) (fun y => fderiv ℝ f y (a i)))
        (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ‖a i‖ * ENNReal.ofReal (n (⌊r⌋₊ + 1 + 1)) := by
      refine hv1.2.trans ?_
      rw [(hMem _ hℓm).2]
    have hA : 0 ≤ ‖a i‖ := norm_nonneg _
    calc ENNReal.ofReal C0 * (eLpNorm (fun x => fderiv ℝ f x (a i)) (ENNReal.ofReal p) volume +
          eLpNorm (iteratedFDeriv ℝ (⌊r⌋₊ + 1) (fun y => fderiv ℝ f y (a i)))
            (ENNReal.ofReal p) volume)
        ≤ ENNReal.ofReal C0 * (ENNReal.ofReal ‖a i‖ * ENNReal.ofReal (n 1) +
          ENNReal.ofReal ‖a i‖ * ENNReal.ofReal (n (⌊r⌋₊ + 1 + 1))) :=
          mul_le_mul_right (add_le_add e0 e1) _
      _ = ENNReal.ofReal (C0 * (‖a i‖ * n 1 + ‖a i‖ * n (⌊r⌋₊ + 1 + 1))) := by
          rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_add (mul_nonneg hA (hn0 _))
            (mul_nonneg hA (hn0 _)), ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hA]
      _ ≤ ENNReal.ofReal (C0 * ‖a i‖ * sob) := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc C0 * (‖a i‖ * n 1 + ‖a i‖ * n (⌊r⌋₊ + 1 + 1))
              = C0 * ‖a i‖ * (n 1 + n (⌊r⌋₊ + 1 + 1)) := by ring
            _ ≤ C0 * ‖a i‖ * sob := mul_le_mul_of_nonneg_left hpair (mul_nonneg hC0 hA)
  choose w hwm hw1 hw2 using hcomp
  have hsum : ∑ i, C0 * ‖a i‖ * sob = C0 * Sa * sob := by
    rw [hSa, Finset.mul_sum, Finset.sum_mul]
  have hmeas : AEMeasurable (fun x => (WithLp.toLp 2 (fun i => w i x) :
      EuclideanSpace ℝ (Fin d))) volume :=
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp_aemeasurable
      (aemeasurable_pi_iff.2 (fun i => (hwm i).aemeasurable))
  refine ⟨L, C0 * Sa * sob, by positivity, hLip,
    ⟨fun x => (WithLp.toLp 2 (fun i => w i x) : EuclideanSpace ℝ (Fin d)), ?_, ?_⟩, ?_⟩
  · intro i
    have : (fun x => (Matrix.toEuclideanLin M.transpose (gradient f x)) i) =
        fun x => fderiv ℝ f x (a i) := funext (fun x => s1c2_vi_eq M f i x)
    rw [this]
    exact hw1 i
  · have hpt : ∀ x, ‖(WithLp.toLp 2 (fun i => w i x) : EuclideanSpace ℝ (Fin d))‖ ≤
        ∑ i, ‖w i x‖ := fun x => by
      rw [EuclideanSpace.norm_eq]
      refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg (fun i _ => norm_nonneg _), ?_⟩
      simpa [PiLp.toLp_apply] using Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (f := fun i => ‖w i x‖) (fun i _ => norm_nonneg _)
    have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
    calc eLpNorm (fun x => ‖(WithLp.toLp 2 (fun i => w i x) : EuclideanSpace ℝ (Fin d))‖)
          (ENNReal.ofReal p) volume
        ≤ eLpNorm (fun x => ∑ i, ‖w i x‖) (ENNReal.ofReal p) volume :=
          eLpNorm_mono_real hmeas.norm.aestronglyMeasurable (fun x => by
            rw [norm_norm]; exact hpt x)
      _ = eLpNorm (∑ i, fun x => ‖w i x‖) (ENNReal.ofReal p) volume := by
          congr 1; funext x; simp [Finset.sum_apply]
      _ ≤ ∑ i, eLpNorm (fun x => ‖w i x‖) (ENNReal.ofReal p) volume := eLpNorm_sum_le hp1
      _ = ∑ i, eLpNorm (w i) (ENNReal.ofReal p) volume :=
          Finset.sum_congr rfl (fun i _ => eLpNorm_norm _ (hwm i))
      _ ≤ ∑ i, ENNReal.ofReal (C0 * ‖a i‖ * sob) := Finset.sum_le_sum (fun i _ => hw2 i)
      _ = ENNReal.ofReal (C0 * Sa * sob) := by
          rw [← hsum, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  · rw [hL]
    exact le_of_eq (by ring)

/-! ### Boundedness of `D²f` from the (junk-prone) Sobolev embedding, by a translated cutoff

`HRS.cbNorm` is a sum of *real* suprema, which are `0` for unbounded derivatives, so the inequality
`cbNorm (mStar d) f ≤ C ‖f‖_{W^{m,p}}` of claim 1 does not by itself bound `D²f`.  Applying it to the compactly
supported function `y ↦ ρ(y - x₀) f(y)` (all suprema are then genuine) recovers `‖D²f(x₀)‖ ≤ C' ‖f‖_{W^{m,p}}`. -/

theorem s1c2_lp_data {V : Type*} [NormedAddCommGroup V] {h : EuclideanSpace ℝ (Fin d) → V}
    {p : ℝ} (hp : 0 < p) (hh : MemLp h (ENNReal.ofReal p) volume) :
    Integrable (fun x => ‖h x‖ ^ p) ∧
      (∫ x, ‖h x‖ ^ p) ^ (1 / p) = (eLpNorm h (ENNReal.ofReal p) volume).toReal := by
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  refine ⟨?_, ?_⟩
  · have := (integrable_norm_rpow_iff hh.aestronglyMeasurable hq0 ENNReal.ofReal_ne_top).2 hh
    rwa [ENNReal.toReal_ofReal hp.le] at this
  · rw [hh.eLpNorm_eq_integral_rpow_norm hq0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => by positivity) _),
      one_div]

theorem s1c2_memLp_of_integrable {V : Type*} [NormedAddCommGroup V]
    {h : EuclideanSpace ℝ (Fin d) → V} {p : ℝ} (hp : 0 < p)
    (hc : AEStronglyMeasurable h volume) (hi : Integrable (fun x => ‖h x‖ ^ p)) :
    MemLp h (ENNReal.ofReal p) volume := by
  rw [← integrable_norm_rpow_iff hc (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  exact hi

theorem s1c2_nat_le_top (k : ℕ) : ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

set_option maxHeartbeats 1000000 in
theorem s1c2_cutoff_D2 {p : ℝ} (hp1' : 1 ≤ p) (m k0 : ℕ) (hk0 : 2 ≤ k0)
    (hmorrey : ∃ C₁ : ℝ, ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ g →
      (∀ j ≤ m, Integrable (fun x => ‖iteratedFDeriv ℝ j g x‖ ^ p)) →
      cbNorm k0 g ≤ C₁ * sobolevWNorm m p g) :
    ∃ C : ℝ, ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ f →
      (∀ j ≤ m, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖ ^ p)) →
      ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C * sobolevWNorm m p f := by
  have hp : 0 < p := by linarith
  obtain ⟨C₁, hC₁⟩ := hmorrey
  set ρb : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := ⟨1, 2, one_pos, one_lt_two⟩ with hρb
  set ρ : EuclideanSpace ℝ (Fin d) → ℝ := ⇑ρb with hρdef
  have hρ : ContDiff ℝ ∞ ρ := ρb.contDiff
  have hρc : HasCompactSupport ρ := ρb.hasCompactSupport
  have hρ1 : ∀ y, ‖y‖ ≤ 1 → ρ y = 1 := fun y hy =>
    ρb.one_of_mem_closedBall (by
      show y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
      simpa [Metric.mem_closedBall, dist_zero_right] using hy)
  have hB : ∀ k, ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖iteratedFDeriv ℝ k ρ y‖ ≤ B := by
    intro k
    obtain ⟨B, hB⟩ := (hρc.iteratedFDeriv k).exists_bound_of_continuous
      (hρ.continuous_iteratedFDeriv (s1c2_nat_le_top _))
    exact ⟨max B 0, le_max_right _ _, fun y => (hB y).trans (le_max_left _ _)⟩
  choose B hB0 hB using hB
  set K : ℝ := ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * B i with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ =>
    mul_nonneg (Nat.cast_nonneg _) (hB0 i)))
  refine ⟨max C₁ 0 * K, ?_⟩
  intro f hf hint x0
  set n : ℕ → ℝ := fun j => (∫ x, ‖iteratedFDeriv ℝ j f x‖ ^ p) ^ (1 / p) with hn
  have hn0 : ∀ j, 0 ≤ n j := fun j =>
    Real.rpow_nonneg (integral_nonneg (fun x => by positivity)) _
  have hsob : sobolevWNorm m p f = ∑ j ∈ Finset.range (m + 1), n j := rfl
  set sob := sobolevWNorm m p f with hsobdef
  have hsob0 : 0 ≤ sob := by rw [hsob]; exact Finset.sum_nonneg (fun j _ => hn0 j)
  have hnle : ∀ j ≤ m, n j ≤ sob := fun j hj => by
    rw [hsob]
    exact Finset.single_le_sum (f := n) (fun l _ => hn0 l) (Finset.mem_range.2 (by omega))
  have hMem : ∀ j ≤ m, MemLp (iteratedFDeriv ℝ j f) (ENNReal.ofReal p) volume ∧
      eLpNorm (iteratedFDeriv ℝ j f) (ENNReal.ofReal p) volume = ENNReal.ofReal (n j) := by
    intro j hj
    have hc : Continuous (iteratedFDeriv ℝ j f) :=
      hf.continuous_iteratedFDeriv (s1c2_nat_le_top _)
    have hmem := s1c2_memLp_of_integrable hp hc.aestronglyMeasurable (hint j hj)
    refine ⟨hmem, ?_⟩
    have := (s1c2_lp_data hp hmem).2
    rw [← ENNReal.ofReal_toReal hmem.ne, ← this]
  set g : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ρ (y - x0) * f y with hg
  have hρs : ContDiff ℝ ∞ (fun y => ρ (y - x0)) := hρ.comp (contDiff_id.sub contDiff_const)
  have hgd : ContDiff ℝ ∞ g := hρs.mul hf
  have hgpt : ∀ j y, ‖iteratedFDeriv ℝ j g y‖ ≤ ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * B i * ‖iteratedFDeriv ℝ (j - i) f y‖ := by
    intro j y
    refine (norm_iteratedFDeriv_mul_le hρs hf y (s1c2_nat_le_top _)).trans ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [iteratedFDeriv_comp_sub']
    have h1 := hB i (y - x0)
    have h2 : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
    have h3 : 0 ≤ ‖iteratedFDeriv ℝ (j - i) f y‖ := norm_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) h3
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp1'
  have hgLp : ∀ j ≤ m, MemLp (iteratedFDeriv ℝ j g) (ENNReal.ofReal p) volume ∧
      (eLpNorm (iteratedFDeriv ℝ j g) (ENNReal.ofReal p) volume).toReal ≤
        (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i) * sob := by
    intro j hj
    have hgc : Continuous (iteratedFDeriv ℝ j g) :=
      hgd.continuous_iteratedFDeriv (s1c2_nat_le_top _)
    set H : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * B i * ‖iteratedFDeriv ℝ (j - i) f y‖ with hH
    have h1 : eLpNorm (iteratedFDeriv ℝ j g) (ENNReal.ofReal p) volume ≤
        eLpNorm H (ENNReal.ofReal p) volume :=
      eLpNorm_mono_real hgc.aestronglyMeasurable (fun y => hgpt j y)
    have h2 : eLpNorm H (ENNReal.ofReal p) volume ≤
        ∑ i ∈ Finset.range (j + 1), ENNReal.ofReal ((j.choose i : ℝ) * B i * n (j - i)) := by
      have hHeq : H = ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℝ) * B i) •
          (fun y => ‖iteratedFDeriv ℝ (j - i) f y‖) := by
        funext y; simp [hH, Finset.sum_apply, smul_eq_mul]
      rw [hHeq]
      refine (eLpNorm_sum_le hp1).trans (Finset.sum_le_sum (fun i hi => ?_))
      have hi' : j - i ≤ m := by omega
      have hcf : Continuous (iteratedFDeriv ℝ (j - i) f) :=
        hf.continuous_iteratedFDeriv (s1c2_nat_le_top _)
      have hnn : 0 ≤ (j.choose i : ℝ) * B i := mul_nonneg (Nat.cast_nonneg _) (hB0 i)
      refine le_of_eq ?_
      calc eLpNorm (((j.choose i : ℝ) * B i) • (fun y => ‖iteratedFDeriv ℝ (j - i) f y‖))
            (ENNReal.ofReal p) volume
          = ‖((j.choose i : ℝ) * B i)‖ₑ * eLpNorm (fun y => ‖iteratedFDeriv ℝ (j - i) f y‖)
            (ENNReal.ofReal p) volume := eLpNorm_const_smul _ _ _ _
        _ = ENNReal.ofReal ((j.choose i : ℝ) * B i) * ENNReal.ofReal (n (j - i)) := by
            rw [Real.enorm_eq_ofReal hnn, eLpNorm_norm _ hcf.aestronglyMeasurable,
              (hMem (j - i) hi').2]
        _ = ENNReal.ofReal ((j.choose i : ℝ) * B i * n (j - i)) := by
            rw [← ENNReal.ofReal_mul hnn]
    have h3 : (∑ i ∈ Finset.range (j + 1), ENNReal.ofReal ((j.choose i : ℝ) * B i * n (j - i))) <
        ⊤ := ENNReal.sum_lt_top.2 (fun i _ => ENNReal.ofReal_lt_top)
    refine ⟨lt_of_le_of_lt (h1.trans h2) h3, ?_⟩
    calc (eLpNorm (iteratedFDeriv ℝ j g) (ENNReal.ofReal p) volume).toReal
        ≤ (∑ i ∈ Finset.range (j + 1),
            ENNReal.ofReal ((j.choose i : ℝ) * B i * n (j - i))).toReal :=
          ENNReal.toReal_mono h3.ne (h1.trans h2)
      _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * n (j - i) := by
          rw [ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)]
          exact Finset.sum_congr rfl (fun i _ => ENNReal.toReal_ofReal
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 i)) (hn0 _)))
      _ ≤ (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i) * sob := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum (fun i hi => ?_)
          have hi' : j - i ≤ m := by
            have := Finset.mem_range.1 hi; omega
          exact mul_le_mul_of_nonneg_left (hnle (j - i) hi')
            (mul_nonneg (Nat.cast_nonneg _) (hB0 i))
  have hgint : ∀ j ≤ m, Integrable (fun x => ‖iteratedFDeriv ℝ j g x‖ ^ p) := fun j hj =>
    (s1c2_lp_data hp (hgLp j hj).1).1
  have hsobg : sobolevWNorm m p g ≤ K * sob := by
    have : sobolevWNorm m p g = ∑ j ∈ Finset.range (m + 1),
        (eLpNorm (iteratedFDeriv ℝ j g) (ENNReal.ofReal p) volume).toReal := by
      unfold sobolevWNorm
      refine Finset.sum_congr rfl (fun j hj => ?_)
      exact (s1c2_lp_data hp (hgLp j (by have := Finset.mem_range.1 hj; omega)).1).2
    rw [this, hK, Finset.sum_mul]
    exact Finset.sum_le_sum (fun j hj => (hgLp j (by have := Finset.mem_range.1 hj; omega)).2)
  have hsobg0 : 0 ≤ sobolevWNorm m p g :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (integral_nonneg fun x => by positivity) _)
  have hgcs : HasCompactSupport g :=
    (hρc.comp_homeomorph (Homeomorph.subRight x0)).mul_right
  have hbdd : BddAbove (Set.range fun z => ‖iteratedFDeriv ℝ 2 g z‖) := by
    obtain ⟨C, hC⟩ := (hgcs.iteratedFDeriv 2).exists_bound_of_continuous
      (hgd.continuous_iteratedFDeriv (s1c2_nat_le_top _))
    exact ⟨C, by rintro _ ⟨z, rfl⟩; exact hC z⟩
  have hcb : ‖iteratedFDeriv ℝ 2 g x0‖ ≤ cbNorm k0 g := by
    unfold cbNorm
    calc ‖iteratedFDeriv ℝ 2 g x0‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ 2 g z‖ := le_ciSup hbdd x0
      _ ≤ ∑ j ∈ Finset.range (k0 + 1), ⨆ z, ‖iteratedFDeriv ℝ j g z‖ :=
          Finset.single_le_sum (f := fun j => ⨆ z, ‖iteratedFDeriv ℝ j g z‖)
            (fun j _ => Real.iSup_nonneg (fun z => norm_nonneg _))
            (Finset.mem_range.2 (by omega))
  have hev : g =ᶠ[nhds x0] f := by
    filter_upwards [Metric.ball_mem_nhds x0 one_pos] with y hy
    have : ‖y - x0‖ ≤ 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy.le
    simp only [hg]
    rw [hρ1 _ this, one_mul]
  have heq : iteratedFDeriv ℝ 2 g x0 = iteratedFDeriv ℝ 2 f x0 :=
    (Filter.EventuallyEq.iteratedFDeriv ℝ hev 2).eq_of_nhds
  rw [← heq]
  calc ‖iteratedFDeriv ℝ 2 g x0‖ ≤ cbNorm k0 g := hcb
    _ ≤ C₁ * sobolevWNorm m p g := hC₁ g hgd hgint
    _ ≤ max C₁ 0 * sobolevWNorm m p g :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hsobg0
    _ ≤ max C₁ 0 * (K * sob) := mul_le_mul_of_nonneg_left hsobg (le_max_right _ _)
    _ = max C₁ 0 * K * sob := by ring

end HRS.S1C2

namespace HRS.Whole.DecayingDensity

open HRS.S1C2

/-- **S.A.1, claim 2** (`HRS.Whole.DecayingDensity.commutatorNorm_le`), conditional on claim 1: the hypothesis
`hmorrey` is exactly the conclusion of `HRS.Whole.DecayingDensity.sobolev_embeds_cb hs0 hsd c`.  After claim 1 is proved the
frozen statement follows by
`fun hs0 hsd c M => commutatorNorm_le_proof hs0 hsd c M (sobolev_embeds_cb hs0 hsd c)`.
(The sup bound for `D²f` needed for the Lipschitz constant is extracted from `hmorrey` by a translated cutoff,
`s1c2_cutoff_D2`, because `cbNorm` is a sum of real suprema which are `0` for unbounded derivatives.) -/
theorem commutatorNorm_le_proof {d : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (c : DecayingDensity d s) (M : Matrix (Fin d) (Fin d) ℝ)
    (hmorrey : ∃ C₁ : ℝ, ∀ f : Euc d → ℝ, ContDiff ℝ ∞ f →
      (∀ j ≤ c.sobolevIndex, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖ ^ c.integrability)) →
      cbNorm (mStar d) f ≤ C₁ * sobolevWNorm c.sobolevIndex c.integrability f) :
    ∃ C : ℝ, ∀ f : Euc d → ℝ, ContDiff ℝ ∞ f →
      (∀ j ≤ c.sobolevIndex, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖ ^ c.integrability)) →
      HasFracTransportBound c.regularity c.integrability
        (fun x => Matrix.toEuclideanLin M.transpose (gradient f x))
        (C * sobolevWNorm c.sobolevIndex c.integrability f) := by
  obtain ⟨hr, hp, hm⟩ := s1c2_params hs0 hsd c
  have hD2 := s1c2_cutoff_D2 hp.le c.sobolevIndex (mStar d) (by unfold mStar; omega) hmorrey
  exact s1c2_transport_bound hs0 hsd c M hD2

end HRS.Whole.DecayingDensity
