import HRS.MS.QprepAux14
import HRS.MS.R2PolyTie
import HRS.MS.R2ScrAux2
import HRS.MS.SuppU1
import HRS.MS.Comm
import HRS.MS.WrEntAux2

/-!
# S9.9 `r2_static_edgeworth`, packet 1: the standing setup and the moment API

Worker S99.  Namespace `S99`, helper prefix `s99_`.  No existing file is edited.  The full per-row plan is in
`S99_PLAN.md` (scratch directory) and repeated here.

## Verdict (STEP 1)

The frozen statement `HRS.Whole.r2_static_edgeworth` is TRUE and non-vacuous as stated; no statement change is needed.
Junk-value audit.  `d ≥ 2`, `a, β, γ > 0`, `0 ≤ s < d/2` and `ρ = thermalDensity` (`mv0_rho_eq`), a smooth positive probability
density with Gaussian bounds (`S45.s45_thermal_data`).  `Q_{N,γ}(μ) = modulatedGibbs (rieszKernel d s) N γ μ` is an exchangeable
probability measure for `N ≥ 2` (`S46.s46_static_all`, `S46.s46_P_eq`) and `meanEmpirical Q = firstMarginal Q`.  `responseInverse`
is the honest a.e.-resolvent (every Hermite function lies in `C_b^J`, `J = 4d+40`, and has a response by `r2_screened`);
`responseRepW` is a bounded continuous representative; `OscDual.ofSeq` is never the junk `0` because
`∑_α λ_α^{-m} |a_α(x)|² < ∞` uniformly in `x` (`cbNorm J h_α ≲ λ_α^{J/2}`, `m > J + 2d`); `Real.log 0` and `0^(-s)` only occur on
the collision null set; `N ≥ 2` and `d ≥ 2` are in the statement; the Bochner integrals of the conclusion integrate bounded
continuous functions (`Φ ∈ CbUnitBall 5`).  The conclusion is uniform in `Φ` and is proved so (all estimates are uniform over the
Stein class `{f ∈ C⁵ : ‖D^i f‖_∞ ≤ 1}`).
For `s < d/2` one has `δ_N = 1/N` (`R2Mt.s92_mul_deltaN`), so the static estimates of S3.3/S3.5 give the mean bias
`|ν_N(w) - μ(w)| ≤ C‖w‖_∞/N` directly (`S46Static.marg`), the `L²` bound of linear statistics (`S46Static.linear`), and the `L¹`
bound of the quadratic remainder; the S9.5 moment transfer is used only for general kernels (finite-rank approximation) and
tails uniform in `N`.

## Content of this file

* `s99_env`: the thermal data and the calibrated static bundle for `Q_{N,γ}` (all `N ≥ 2`) with one constant;
* `s99_lp_bound`: `eLpNorm f r ≤ C` gives integrability and `∫|f|^r ≤ C^r`;
* `s99_round2_density`: the thermal density satisfies `IsRound2Density` and `HasR2GaussianUpper`;
* `s99_actual`: `HasR2ActualDensity` for `P = Q`;
* `s99_comm_isBounded`: the commutator kernel of a Lipschitz field is in `IsBoundedPairKernel s ((s+1)Λ)` (also `s = 0`);
* `s99_moments`: the S9.5 consequences used later (pair energy bounds, linear bounds, tails).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

/-! ### The environment -/

theorem s99_env (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hγ : 0 < γ) :
    ∃ C c BU Cs : ℝ, S45.ThermalData d s a β C c BU ∧ 0 ≤ Cs ∧
      ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨C, c, BU, hT⟩ := S46.s46_thermal_data_unif hd hs0 hsd ha hβ (le_refl a) (le_refl β)
  obtain ⟨Cs, hCs0, hS⟩ := S46.s46_static_all hd hs0 hsd ha hβ hγ (le_refl a) (le_refl β) (le_refl γ)
  exact ⟨C, c, BU, Cs, hT a ⟨le_rfl, le_rfl⟩ β ⟨le_rfl, le_rfl⟩, hCs0,
    fun N hN => hS a ⟨le_rfl, le_rfl⟩ β ⟨le_rfl, le_rfl⟩ γ ⟨le_rfl, le_rfl⟩ N hN⟩

/-! ### `L^r` bounds to integrals -/

theorem s99_lp_bound {α : Type*} [MeasurableSpace α] {P : Measure α} {f : α → ℝ} {r C : ℝ}
    (hr : 1 ≤ r) (hC : 0 ≤ C) (hf : AEStronglyMeasurable f P)
    (h : eLpNorm f (ENNReal.ofReal r) P ≤ ENNReal.ofReal C) :
    MemLp f (ENNReal.ofReal r) P ∧ ∫ x, |f x| ^ r ∂P ≤ C ^ r := by
  have hr0 : 0 < r := by linarith
  have hlt : eLpNorm f (ENNReal.ofReal r) P < ⊤ := h.trans_lt ENNReal.ofReal_lt_top
  have hmem : MemLp f (ENNReal.ofReal r) P := hlt
  refine ⟨hmem, ?_⟩
  have hp0 : ENNReal.ofReal r ≠ 0 := by simpa using hr0
  have hptop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 := hmem.eLpNorm_eq_integral_rpow_norm hp0 hptop
  rw [h1, ENNReal.toReal_ofReal hr0.le] at h
  have hI : 0 ≤ ∫ x, ‖f x‖ ^ r ∂P := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have h2 : (∫ x, ‖f x‖ ^ r ∂P) ^ r⁻¹ ≤ C := by
    have := (ENNReal.ofReal_le_ofReal_iff hC).1 h
    exact this
  have h3 : ∫ x, ‖f x‖ ^ r ∂P ≤ C ^ r := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hI _) h2 hr0.le
    rwa [← Real.rpow_mul hI, inv_mul_cancel₀ hr0.ne', Real.rpow_one] at this
  simpa [Real.norm_eq_abs] using h3

/-- `r = 1`. -/
theorem s99_l1_bound {α : Type*} [MeasurableSpace α] {P : Measure α} {f : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : AEStronglyMeasurable f P)
    (h : eLpNorm f 1 P ≤ ENNReal.ofReal C) : Integrable f P ∧ ∫ x, |f x| ∂P ≤ C := by
  have h' : eLpNorm f (ENNReal.ofReal 1) P ≤ ENNReal.ofReal C := by simpa using h
  obtain ⟨hm, hi⟩ := s99_lp_bound (r := 1) le_rfl hC hf h'
  refine ⟨?_, by simpa using hi⟩
  have : MemLp f 1 P := by simpa using hm
  exact memLp_one_iff_integrable.1 this

/-- `r = 2`. -/
theorem s99_l2_bound {α : Type*} [MeasurableSpace α] {P : Measure α} {f : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : AEStronglyMeasurable f P)
    (h : eLpNorm f 2 P ≤ ENNReal.ofReal C) : MemLp f 2 P ∧ ∫ x, (f x) ^ 2 ∂P ≤ C ^ 2 := by
  have h' : eLpNorm f (ENNReal.ofReal 2) P ≤ ENNReal.ofReal C := by simpa using h
  obtain ⟨hm, hi⟩ := s99_lp_bound (r := 2) (by norm_num) hC hf h'
  refine ⟨by simpa using hm, ?_⟩
  have e : ∀ x, |f x| ^ (2 : ℝ) = f x ^ 2 := fun x => by
    rw [Real.rpow_two, sq_abs]
  simp_rw [e] at hi
  simpa using hi

/-! ### The Round-2 data of the thermal density -/

theorem s99_round2_density {s a β C c BU : ℝ} (hT : S45.ThermalData d s a β C c BU) :
    ∃ L : ℝ, IsRound2Density d s C L (thermalDensity d s a β) ∧
      HasR2GaussianUpper C c (thermalDensity d s a β) := by
  have hμ : thermalMeasure d s a β = withDensityReal (thermalDensity d s a β) := rfl
  obtain ⟨L2, hL2⟩ := S45.s45_thermal_logmoment2 hT
  rw [hμ] at hL2
  haveI hprob : IsProbabilityMeasure (withDensityReal (thermalDensity d s a β)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  refine ⟨1 + L2, ⟨hT.prob, fun x => ?_, fun _ => ?_⟩, hT.hc, fun x => ?_⟩
  · have hx := (le_abs_self _).trans (hT.h0 x)
    have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hT.hc])
    nlinarith [hT.C0]
  · -- the first logarithmic moment
    have hbd : ∀ x : Euc d, Real.log (2 + ‖x‖) ≤ 1 + Real.log (2 + ‖x‖) ^ 2 := fun x => by
      nlinarith [sq_nonneg (Real.log (2 + ‖x‖) - 1)]
    have hlm : AEStronglyMeasurable (fun x : Euc d => Real.log (2 + ‖x‖)) (withDensityReal (thermalDensity d s a β)) :=
      (Real.measurable_log.comp (measurable_const.add measurable_norm)).aestronglyMeasurable
    have hint2 : Integrable (fun x : Euc d => 1 + Real.log (2 + ‖x‖) ^ 2)
        (withDensityReal (thermalDensity d s a β)) := (integrable_const (1 : ℝ)).add hL2.1
    have hint : Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (withDensityReal (thermalDensity d s a β)) := by
      refine Integrable.mono' hint2 hlm
        (Filter.Eventually.of_forall fun x => ?_)
      have h0 : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hbd x
    refine ⟨hint, ?_⟩
    calc ∫ x, Real.log (2 + ‖x‖) ∂(withDensityReal (thermalDensity d s a β))
        ≤ ∫ x, (1 + Real.log (2 + ‖x‖) ^ 2) ∂(withDensityReal (thermalDensity d s a β)) :=
          integral_mono hint hint2 hbd
      _ = 1 + ∫ x, Real.log (2 + ‖x‖) ^ 2 ∂(withDensityReal (thermalDensity d s a β)) := by
          rw [integral_add (integrable_const _) hL2.1]; simp
      _ ≤ 1 + L2 := by linarith [hL2.2]
  · exact (le_abs_self _).trans (hT.h0 x)

/-- `HasR2ActualDensity` for `P = Q` (density `1`, `p = 2`, `K = 1`). -/
theorem s99_actual {s γ : ℝ} {μ : Measure (Euc d)} {N : ℕ} (Q : Measure (EucConfig d N))
    [IsProbabilityMeasure Q] (hQ : Q = modulatedGibbs (rieszKernel d s) N γ μ) :
    HasR2ActualDensity s γ 2 1 μ Q := by
  refine ⟨inferInstance, hQ ▸ Measure.AbsolutelyContinuous.refl _, ?_⟩
  rw [← hQ]
  have h1 : (fun X => ((Q.rnDeriv Q) X).toReal) =ᵐ[Q] fun _ => (1 : ℝ) := by
    filter_upwards [Measure.rnDeriv_self Q] with X hX
    simp [hX]
  rw [eLpNorm_congr_ae h1, eLpNorm_const _ (by norm_num : ENNReal.ofReal 2 ≠ 0) (NeZero.ne Q)]
  simp

/-! ### The commutator kernel is in the bounded class (also `s = 0`) -/

theorem s99_comm_bound_zero (Λ : ℝ≥0) {v : Euc d → Euc d} (hv : LipschitzWith Λ v) (x y : Euc d)
    (hxy : x ≠ y) :
    |commutatorKernel d 0 v x y| ≤ (Λ : ℝ) * (1 + rieszWeight 0 (x - y)) := by
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hzpos : 0 < ‖x - y‖ := norm_pos_iff.mpr hz
  have hΛ : (0 : ℝ) ≤ (Λ : ℝ) := NNReal.coe_nonneg Λ
  have hG : ‖rieszKernelGrad d 0 (x - y)‖ = ‖x - y‖⁻¹ := by
    rw [movtr_rieszKernelGrad_norm 0 le_rfl hz]
    norm_num [movtr_sigma, Real.rpow_neg_one]
  have key : |commutatorKernel d 0 v x y| ≤ (Λ : ℝ) := by
    unfold commutatorKernel
    calc |inner ℝ (v x - v y) (rieszKernelGrad d 0 (x - y))|
        ≤ ‖v x - v y‖ * ‖rieszKernelGrad d 0 (x - y)‖ := abs_real_inner_le_norm _ _
      _ ≤ ((Λ : ℝ) * ‖x - y‖) * ‖x - y‖⁻¹ :=
          mul_le_mul (HRS.MS.Comm.comm_lip hv x y) hG.le (norm_nonneg _) (by positivity)
      _ = (Λ : ℝ) := by rw [mul_assoc, mul_inv_cancel₀ hzpos.ne', mul_one]
  have hw : 0 ≤ rieszWeight 0 (x - y) := by simp [rieszWeight]
  nlinarith [mul_nonneg hΛ hw]

theorem s99_isBoundedPairKernel_mono {s B B' : ℝ} {h : Euc d → Euc d → ℝ}
    (hh : IsBoundedPairKernel s B h) (hB : B ≤ B') (hs0 : 0 ≤ s) : IsBoundedPairKernel s B' h := by
  refine ⟨hh.measurable, hh.symm, fun x y hxy => (hh.bound x y hxy).trans ?_⟩
  have hw : 0 ≤ 1 + rieszWeight s (x - y) := by
    unfold rieszWeight
    split_ifs
    · have := le_max_right (-Real.log ‖x - y‖) 0; linarith
    · have := Real.rpow_nonneg (norm_nonneg (x - y)) (-s); linarith
  exact mul_le_mul_of_nonneg_right hB hw

/-- The commutator kernel of a `Λ`-Lipschitz field lies in `IsBoundedPairKernel s ((s+1)Λ)`. -/
theorem s99_comm_isBounded {s : ℝ} (hs0 : 0 ≤ s) (Λ : ℝ≥0) {v : Euc d → Euc d}
    (hv : LipschitzWith Λ v) : IsBoundedPairKernel s ((s + 1) * Λ) (commutatorKernel d s v) := by
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    refine ⟨HRS.MS.Comm.comm_meas v hv.continuous.measurable, HRS.MS.Comm.comm_symm v,
      fun x y hxy => ?_⟩
    have := s99_comm_bound_zero Λ hv x y hxy
    simpa using this
  · have := HRS.MS.Comm.commutatorKernel_isBounded_proof h0 Λ v hv
    refine s99_isBoundedPairKernel_mono this ?_ hs0
    have : (0 : ℝ) ≤ Λ := Λ.coe_nonneg
    nlinarith

/-! ### The particle law and the S9.5 moment bounds -/

theorem s99_P_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hγ : 0 < γ) (N : ℕ) :
    S46.s46_P d s a β γ N = modulatedGibbs (rieszKernel d s) N γ (thermalMeasure d s a β) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  exact S46.s46_P_eq hd hs0 hsd ha hβ hγ N

theorem s99_poly_of_bdd {s B : ℝ} {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h) :
    IsR2PolyPairKernel s 0 B h :=
  ⟨hh.measurable, hh.symm, fun x y hxy => by simpa using hh.bound x y hxy⟩

/-- The moment bounds of S9.5 (`Pw = 0`) for the particle law `Q = Q_{N,γ}(μ)`, thermal `μ`. -/
theorem s99_mom (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : S45.ThermalData d s a β C c BU)
    (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N) (r : ℝ) (hr : 1 ≤ r) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧
      (∀ N : ℕ, 2 ≤ N → ∀ B : ℝ, 0 ≤ B → ∀ h : Euc d → Euc d → ℝ, IsBoundedPairKernel s B h →
        eLpNorm (fun X : EucConfig d N => (N : ℝ) * pairEnergy h X (thermalMeasure d s a β))
            (ENNReal.ofReal r) (S46.s46_P d s a β γ N) ≤ ENNReal.ofReal (C₁ * B) ∧
        eLpNorm (fun X : EucConfig d N => (N : ℝ) * (pairEnergy h X (thermalMeasure d s a β) -
            ∫ Y, pairEnergy h Y (thermalMeasure d s a β) ∂(S46.s46_P d s a β γ N)))
            (ENNReal.ofReal r) (S46.s46_P d s a β γ N) ≤ ENNReal.ofReal (C₁ * B)) ∧
      (∀ N : ℕ, 2 ≤ N → ∀ B : ℝ, 0 ≤ B → ∀ u : Euc d → ℝ, Measurable u → (∀ x, |u x| ≤ B) →
        eLpNorm (fun X : EucConfig d N => Real.sqrt N *
            (pair (empirical X) u - pair (thermalMeasure d s a β) u))
            (ENNReal.ofReal r) (S46.s46_P d s a β γ N) ≤ ENNReal.ofReal (C₁ * B)) ∧
      (∀ B : ℝ, 0 ≤ B → ∀ (h : Euc d → Euc d → ℝ) (hj : ℕ → Euc d → Euc d → ℝ),
        IsBoundedPairKernel s B h → (∀ j, IsBoundedPairKernel s B (hj j)) →
        (∃ ε : ℝ, 0 < ε ∧ (2 + ε) * s < d ∧
          Tendsto (fun j => eLpNorm (fun q : Euc d × Euc d => hj j q.1 q.2 - h q.1 q.2)
            (ENNReal.ofReal (2 + ε)) ((thermalMeasure d s a β).prod (thermalMeasure d s a β))) atTop
            (𝓝 0)) →
        ∀ ε : ℝ, 0 < ε → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N : ℕ, 2 ≤ N →
          eLpNorm (fun X : EucConfig d N => (N : ℝ) *
              pairEnergy (fun x y => hj j x y - h x y) X (thermalMeasure d s a β))
            (ENNReal.ofReal r) (S46.s46_P d s a β γ N) ≤ ENNReal.ofReal ε ∧
          eLpNorm (fun X : EucConfig d N => (N : ℝ) * (pairEnergy (fun x y => hj j x y - h x y) X
              (thermalMeasure d s a β) - ∫ Y, pairEnergy (fun x y => hj j x y - h x y) Y
              (thermalMeasure d s a β) ∂(S46.s46_P d s a β γ N)))
            (ENNReal.ofReal r) (S46.s46_P d s a β γ N) ≤ ENNReal.ofReal ε) := by
  obtain ⟨L, hL, hG⟩ := s99_round2_density hT
  obtain ⟨C₁, hC⟩ := HRS.MS.R2Poly.round2_polynomial_moments_proof hd s hs0 hs C L C c γ 2 1 0 hγ
    (by norm_num) le_rfl r hr
  have hρ := hC (thermalDensity d s a β) hL hG (fun N => S46.s46_P d s a β γ N) (fun N hN => ?_)
  swap
  · haveI := (hS N hN).prob
    exact s99_actual (S46.s46_P d s a β γ N) (s99_P_eq hd hs0 hs ha hβ hγ N)
  obtain ⟨h1, h2, h3⟩ := hρ
  have hC0 : 0 ≤ max C₁ 0 := le_max_right _ _
  refine ⟨max C₁ 0, hC0, ?_, ?_, ?_⟩
  · intro N hN B hB h hh
    have := h1 B hB h (s99_poly_of_bdd hh) () N hN
    exact ⟨this.1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hB)),
      this.2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hB))⟩
  · intro N hN B hB u hu hub
    have := h3 B hB N hN u hu (fun x => by simpa using hub x)
    exact this.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hB))
  · intro B hB h hj hh hhj hconv ε hε
    have hT2 := h2 B hB h hj (s99_poly_of_bdd hh) (fun j => s99_poly_of_bdd (hhj j)) hconv
    obtain ⟨hA, hB'⟩ := hT2
    have hev1 := (hA.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε)))
    have hev2 := (hB'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε)))
    obtain ⟨j₀, hj₀⟩ := (hev1.and hev2).exists_forall_of_atTop
    refine ⟨j₀, fun j hj' N hN => ?_⟩
    obtain ⟨e1, e2⟩ := hj₀ j hj'
    exact ⟨le_trans (le_iSup₂_of_le () ⟨N, hN⟩ le_rfl) e1.le,
      le_trans (le_iSup₂_of_le () ⟨N, hN⟩ le_rfl) e2.le⟩

end S99

end
