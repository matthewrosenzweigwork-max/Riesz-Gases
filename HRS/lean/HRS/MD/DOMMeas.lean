/-
# HRS.MD.DOMMeas — measurability of the generator

For `Φ` measurable and `C²` along every particle slice at a.e. configuration, `𝓛Φ` is a.e. equal to a
measurable function (difference quotients of the slice, which converge off collisions).
-/
import HRS.MD.DOMLeib2

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.MD.DOMProof

open HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

/-- Displacement of particle `i` by `v` in the covering space. -/
def shiftX (X : Config d N) (i : Fin N) (v : Euc d) : Config d N :=
  Function.update X i (X i + Torus.mk v)

/-- The slice of `Φ` along particle `i`. -/
def slice (Φ : Config d N → ℝ) (X : Config d N) (i : Fin N) : Euc d → ℝ := fun u => Φ (shiftX X i u)

theorem domp_shiftX_zero (X : Config d N) (i : Fin N) : shiftX X i 0 = X := domp_update_zero X i

theorem domp_shiftX_shiftX (X : Config d N) (i : Fin N) (v w : Euc d) :
    shiftX (shiftX X i v) i w = shiftX X i (v + w) := by
  unfold shiftX
  rw [Function.update_idem, Function.update_self, Q84a.q84a_mk_add, add_assoc]

theorem domp_slice_shiftX (Φ : Config d N → ℝ) (X : Config d N) (i : Fin N) (v : Euc d) :
    slice Φ (shiftX X i v) i = fun u => slice Φ X i (v + u) := by
  funext u
  unfold slice
  rw [domp_shiftX_shiftX]

theorem domp_measurable_shiftX (i : Fin N) (v : Euc d) :
    Measurable (fun X : Config d N => shiftX X i v) := by
  unfold shiftX
  have h : Measurable (fun X : Config d N => X i + Torus.mk v) :=
    (measurable_pi_apply i).add_const _
  exact (measurable_update' (a := i)).comp (measurable_id.prodMk h)

theorem domp_continuous_shiftX (X : Config d N) (i : Fin N) :
    Continuous (fun v : Euc d => shiftX X i v) := by
  unfold shiftX
  exact continuous_const.update i (continuous_const.add Q84a.q84a_continuous_mk)

theorem domp_inner_gradient_vec (σ : Euc d → ℝ) (x v : Euc d) :
    inner ℝ (gradient σ x) v = fderiv ℝ σ x v := by
  rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]

theorem domp_tendsto_quot {σ : Euc d → ℝ} (hσ : DifferentiableAt ℝ σ 0) (k : Fin d) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      (σ (((n : ℝ) + 1)⁻¹ • EuclideanSpace.single k (1 : ℝ)) - σ 0)) atTop (𝓝 (dk σ k 0)) := by
  have hf : HasDerivAt (fun t : ℝ => t • EuclideanSpace.single k (1 : ℝ))
      (EuclideanSpace.single k (1 : ℝ)) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single k (1 : ℝ))
  have hl : HasFDerivAt σ (fderiv ℝ σ 0) ((fun t : ℝ => t • EuclideanSpace.single k (1 : ℝ)) 0) := by
    simpa using hσ.hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => σ (t • EuclideanSpace.single k (1 : ℝ)))
      (dk σ k 0) 0 := hl.comp_hasDerivAt (0 : ℝ) hf
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop),
      Eventually.of_forall fun n => by simp; positivity⟩
  have := (hasDerivAt_iff_tendsto_slope_zero.1 h1).comp ht
  refine this.congr fun n => ?_
  simp [smul_eq_mul]

theorem domp_measurable_dk_slice {Φ : Config d N → ℝ} (hΦ : Measurable Φ) {U : Set (Config d N)}
    (hU : IsOpen U) (i : Fin N) (hsm : ∀ X ∈ U, DifferentiableAt ℝ (slice Φ X i) 0) (k : Fin d) :
    Measurable (U.indicator (fun X => dk (slice Φ X i) k 0)) := by
  refine measurable_of_tendsto_metrizable (f := fun n : ℕ => U.indicator (fun X =>
    ((n : ℝ) + 1) * (Φ (shiftX X i (((n : ℝ) + 1)⁻¹ • EuclideanSpace.single k (1 : ℝ))) - Φ X)))
    (fun n => ?_) (tendsto_pi_nhds.2 fun X => ?_)
  · refine Measurable.indicator ?_ hU.measurableSet
    exact measurable_const.mul (((hΦ.comp (domp_measurable_shiftX i _))).sub hΦ)
  · by_cases hX : X ∈ U
    · simp only [Set.indicator_of_mem hX]
      have := domp_tendsto_quot (hsm X hX) k
      refine this.congr fun n => ?_
      simp only [slice, domp_shiftX_zero]
    · simp [Set.indicator_of_notMem hX]

theorem domp_dk_shift (Φ : Config d N → ℝ) (X : Config d N) (i : Fin N) (v : Euc d) (k : Fin d) :
    dk (slice Φ (shiftX X i v) i) k 0 = dk (slice Φ X i) k v := by
  rw [domp_slice_shiftX]
  unfold dk
  rw [fderiv_comp_add_left, add_zero]

theorem domp_measurable_ddk_slice {Φ : Config d N → ℝ} (hΦ : Measurable Φ) {U : Set (Config d N)}
    (hU : IsOpen U) (i : Fin N) (hsm : ∀ X ∈ U, ContDiffAt ℝ 2 (slice Φ X i) 0) (k : Fin d) :
    Measurable (U.indicator (fun X => ddk (slice Φ X i) k 0)) := by
  have hdiff : ∀ X ∈ U, DifferentiableAt ℝ (slice Φ X i) 0 := fun X hX =>
    (hsm X hX).differentiableAt (by simp)
  have hgA := domp_measurable_dk_slice hΦ hU i hdiff k
  refine measurable_of_tendsto_metrizable (f := fun n : ℕ => U.indicator (fun X =>
    ((n : ℝ) + 1) * (U.indicator (fun Y => dk (slice Φ Y i) k 0)
        (shiftX X i (((n : ℝ) + 1)⁻¹ • EuclideanSpace.single k (1 : ℝ))) -
      U.indicator (fun Y => dk (slice Φ Y i) k 0) X)))
    (fun n => ?_) (tendsto_pi_nhds.2 fun X => ?_)
  · refine Measurable.indicator ?_ hU.measurableSet
    exact measurable_const.mul ((hgA.comp (domp_measurable_shiftX i _)).sub hgA)
  · by_cases hX : X ∈ U
    · simp only [Set.indicator_of_mem hX]
      have hq : Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
          (dk (slice Φ X i) k (((n : ℝ) + 1)⁻¹ • EuclideanSpace.single k (1 : ℝ)) -
            dk (slice Φ X i) k 0)) atTop (𝓝 (ddk (slice Φ X i) k 0)) :=
        domp_tendsto_quot (domp_differentiableAt_dk (hsm X hX) k) k
      have hev : ∀ᶠ n : ℕ in atTop,
          shiftX X i (((n : ℝ) + 1)⁻¹ • EuclideanSpace.single k (1 : ℝ)) ∈ U := by
        have h0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • EuclideanSpace.single k (1 : ℝ)) atTop
            (𝓝 0) := by
          have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
            tendsto_inv_atTop_zero.comp
              (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
          simpa using hinv.smul_const (EuclideanSpace.single k (1 : ℝ))
        have hc : ContinuousAt (fun v : Euc d => shiftX X i v) 0 :=
          (domp_continuous_shiftX X i).continuousAt
        have hX0 : shiftX X i 0 ∈ U := by rw [domp_shiftX_zero]; exact hX
        exact h0.eventually (hc.eventually (hU.mem_nhds hX0))
      refine hq.congr' ?_
      filter_upwards [hev] with n hn
      rw [Set.indicator_of_mem hn, domp_dk_shift]
    · simp [Set.indicator_of_notMem hX]

/-- The drift of particle `i`. -/
def drift (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (X : Config d N) (i : Fin N) : Euc d :=
  Torus.grad V (X i) + (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, periodicRieszGrad d s (X i - X j)

theorem domp_measurable_particleGen (V : Torus d → ℝ) (β : ℝ) (hsd : s < d) {Φ : Config d N → ℝ}
    (hΦ : Measurable Φ) {U : Set (Config d N)} (hU : IsOpen U)
    (hsm : ∀ X ∈ U, ∀ i, ContDiffAt ℝ 2 (slice Φ X i) 0) :
    Measurable (U.indicator (particleGen d s V β Φ)) := by
  have hdr : ∀ i : Fin N, Measurable (fun X : Config d N => drift d s V X i) := fun i => by
    have hsum : Measurable (fun X : Config d N =>
        ∑ j ∈ Finset.univ.erase i, periodicRieszGrad d s (X i - X j)) :=
      Finset.measurable_sum _ fun j _ => (KernelGrad.measurable_periodicRieszGrad hsd).comp
        ((measurable_pi_apply i).sub (measurable_pi_apply j))
    exact ((q84d_measurable_grad V).comp (measurable_pi_apply i)).add
      (hsum.const_smul (1 / (N : ℝ)))
  have hdrk : ∀ (i : Fin N) (k : Fin d), Measurable (fun X : Config d N =>
      inner ℝ (drift d s V X i) (EuclideanSpace.single k (1 : ℝ))) := fun i k =>
    (continuous_id.inner continuous_const).measurable.comp (hdr i)
  have e : U.indicator (particleGen d s V β Φ) = fun X => ∑ i : Fin N,
      (β⁻¹ * ∑ k, U.indicator (fun Y => ddk (slice Φ Y i) k 0) X -
        ∑ k, inner ℝ (drift d s V X i) (EuclideanSpace.single k (1 : ℝ)) *
          U.indicator (fun Y => dk (slice Φ Y i) k 0) X) := by
    funext X
    by_cases hX : X ∈ U
    · simp only [Set.indicator_of_mem hX]
      unfold particleGen
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      · show β⁻¹ * Laplacian.laplacian (slice Φ X i) 0 = _
        rw [domp_lap_eq_sum_ddk (hsm X hX i)]
      · have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_inner_mul_inner (drift d s V X i)
          (configGrad Φ X i)
        show inner ℝ (drift d s V X i) (configGrad Φ X i) = _
        rw [← this]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [EuclideanSpace.basisFun_apply]
        show _ * inner ℝ _ (gradient (slice Φ X i) 0) = _ * dk (slice Φ X i) k 0
        rw [real_inner_comm (gradient (slice Φ X i) 0) (EuclideanSpace.single k (1 : ℝ)),
          domp_inner_gradient_vec]
        rfl
    · simp [Set.indicator_of_notMem hX]
  rw [e]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
    domp_measurable_ddk_slice hΦ hU i (fun X hX => hsm X hX i) k)).sub
    (Finset.measurable_sum _ fun k _ => (hdrk i k).mul
      (domp_measurable_dk_slice hΦ hU i (fun X hX => (hsm X hX i).differentiableAt (by simp)) k))

end HRS.MD.DOMProof
