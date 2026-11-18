import HRS.MS.PoisKolmAux2

/-!
# POIS-INV (part 1): infinitesimal invariance for `C^2` test functions

Supplement foundation packet POIS-INV (`docs/SUPP_FOUND_PACKETS.md`, Track C).  Setting: `q` real,
`B : ℝ^d → ℝ^d` continuous and bounded by `Mb`, `b x = -q x + B x`, `μ` with
`IsInvariantMeasure b μ` (`HRS/Whole/Thermal.lean`): a probability measure with
`∫ (Δφ + ⟨b, ∇φ⟩) dμ = 0` for every `φ ∈ C_c^∞`.  The generator is `kolmL q B h = Δh + ⟨b, ∇h⟩`
(`PoisKolmAux2`).

Main theorems.
* `HRS.MS.PoisInv.inv_compact_C2`: the identity `∫ L f dμ = 0` extends from `C_c^∞` to every
  `f ∈ C²` with compact support (mollification `f_n = η_n ⋆ f`: the derivatives of `η_n ⋆ f` are
  `η_n ⋆ D^j f`, `j ≤ 2`, which converge boundedly and pointwise, with supports in a fixed ball).
  Only `B` continuous is used.
* `HRS.MS.PoisInv.inv_generator`: for `g ∈ C²` with bounded `Dg`, `D²g` (`g` itself may grow
  linearly) and `∫ ‖x‖² dμ < ∞`, `L g` is `μ`-integrable and `∫ L g dμ = 0` (cutoff `g_R = φ(x/R) g`,
  with `‖Dg_R‖`, `‖D²g_R‖` bounded uniformly in `R ≥ 1`, hence `|L g_R| ≤ A (1 + ‖x‖)` uniformly,
  and dominated convergence; the second moment makes `1 + ‖x‖` integrable).

Statement adjustments relative to the packet sketch: `L g` is the explicit generator `kolmL q B g`;
the second derivative bound is stated for `fderiv ℝ (fderiv ℝ g)` (as in `PoisKolmAux2`).  Helper
lemmas carry the prefix `inv_`.
-/

open MeasureTheory Set Filter Topology
open scoped Convolution ContDiff
open HRS HRS.Whole HRS.MS.PoisKolm

noncomputable section

namespace HRS.MS.PoisInv

variable {d : ℕ}

/-- Normalised mollifier of radius `1/(n+1)`. -/
def invBump (n : ℕ) : ContDiffBump (0 : Euc d) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [one_div_lt_one_div (by positivity) h]; linarith⟩

def invMoll (n : ℕ) (f : Euc d → ℝ) : Euc d → ℝ :=
  ((invBump n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

theorem inv_loc (n : ℕ) : LocallyIntegrable ((invBump (d := d) n).normed volume) volume :=
  ((invBump (d := d) n).contDiff_normed (n := 0)).continuous.locallyIntegrable

theorem inv_moll_fderiv (n : ℕ) {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (x v : Euc d) :
    fderiv ℝ (invMoll n f) x v = invMoll n (fun a => fderiv ℝ f a v) x := by
  have h := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (inv_loc n) hf x
  unfold invMoll
  rw [h.fderiv, convolution_precompR_apply _ (inv_loc n) (hc.fderiv ℝ) (hf.continuous_fderiv one_ne_zero)]

theorem inv_fderiv2 {h : Euc d → ℝ} {x : Euc d} (hh : DifferentiableAt ℝ (fderiv ℝ h) x) (v w : Euc d) :
    fderiv ℝ (fderiv ℝ h) x v w = fderiv ℝ (fun y => fderiv ℝ h y w) x v := by
  have := ((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp x hh.hasFDerivAt)
  have e : (fun y => fderiv ℝ h y w) = (ContinuousLinearMap.apply ℝ ℝ w) ∘ fderiv ℝ h := rfl
  rw [e, this.fderiv]
  rfl

theorem inv_moll_contDiff (n : ℕ) {f : Euc d → ℝ} (hf : Continuous f) :
    ContDiff ℝ ∞ (invMoll n f) :=
  ((invBump (d := d) n).hasCompactSupport_normed).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) ((invBump (d := d) n).contDiff_normed) (hf.locallyIntegrable)

theorem inv_moll_compact (n : ℕ) {f : Euc d → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (invMoll n f) :=
  ((invBump (d := d) n).hasCompactSupport_normed).convolution _ hc

theorem inv_moll_support (n : ℕ) {f : Euc d → ℝ} {R : ℝ} (hR : ∀ y, f y ≠ 0 → ‖y‖ ≤ R) (x : Euc d)
    (hx : R + 1 < ‖x‖) : invMoll n f =ᶠ[𝓝 x] fun _ => 0 := by
  have hopen : IsOpen {y : Euc d | R + 1 < ‖y‖} := isOpen_lt continuous_const continuous_norm
  filter_upwards [hopen.mem_nhds hx] with y hy
  by_contra hne
  have hmem : y ∈ Function.support (invMoll n f) := hne
  have h1 := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hmem
  obtain ⟨z, hz, w, hw, hzw⟩ := h1
  have hz' : ‖z‖ < 1 := by
    have : z ∈ Metric.ball (0 : Euc d) (invBump (d := d) n).rOut := by
      rw [← (invBump (d := d) n).support_normed_eq (μ := volume)]; exact hz
    rw [mem_ball_zero_iff] at this
    refine this.trans_le ?_
    show 1 / ((n : ℝ) + 1) ≤ 1
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hw' : ‖w‖ ≤ R := hR w hw
  have : ‖y‖ ≤ ‖z‖ + ‖w‖ := by rw [← hzw]; exact norm_add_le _ _
  have hy' : R + 1 < ‖y‖ := hy
  linarith

theorem inv_conv_bound (n : ℕ) {g : Euc d → ℝ} (hg : Continuous g) {S : ℝ}
    (hS : ∀ y, |g y| ≤ S) (x : Euc d) :
    |invMoll n g x| ≤ 3 * S := by
  have h := ContDiffBump.dist_normed_convolution_le (φ := invBump (d := d) n) (μ := volume)
    (g := g) (x₀ := x) (ε := 2 * S) hg.aestronglyMeasurable (fun y _ => by
      rw [Real.dist_eq]
      have := hS y; have := hS x
      calc |g y - g x| ≤ |g y| + |g x| := abs_sub _ _
        _ ≤ 2 * S := by linarith)
  rw [Real.dist_eq] at h
  have := hS x
  have h2 : |invMoll n g x| ≤ |invMoll n g x - g x| + |g x| := by
    have := abs_sub_abs_le_abs_sub (invMoll n g x) (g x); linarith
  show |invMoll n g x| ≤ 3 * S
  unfold invMoll at *
  linarith

theorem inv_conv_tendsto {g : Euc d → ℝ} (hg : Continuous g) (x : Euc d) :
    Tendsto (fun n : ℕ => invMoll n g x) atTop (𝓝 (g x)) := by
  refine ContDiffBump.convolution_tendsto_right_of_continuous (φ := fun n : ℕ => invBump (d := d) n)
    (μ := volume) ?_ hg x
  show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem inv_fe {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (e : Euc d) :
    ContDiff ℝ 1 (fun a => fderiv ℝ f a e) ∧ HasCompactSupport (fun a => fderiv ℝ f a e) := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
    exact h1.clm_apply contDiff_const
  · exact (hc.fderiv ℝ).comp_left (g := fun T : Euc d →L[ℝ] ℝ => T e) (by simp)

theorem inv_moll_second {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (n : ℕ)
    (x e : Euc d) :
    fderiv ℝ (fderiv ℝ (invMoll n f)) x e e = invMoll n (fun a => fderiv ℝ (fderiv ℝ f) a e e) x := by
  have hψ := inv_moll_contDiff n hf.continuous
  have hψ1 : ContDiff ℝ 1 (fderiv ℝ (invMoll n f)) := hψ.fderiv_right (m := 1) (by norm_num)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  obtain ⟨hfe, hfec⟩ := inv_fe hf hc e
  rw [inv_fderiv2 (hψ1.differentiable one_ne_zero x)]
  have hfun : (fun y => fderiv ℝ (invMoll n f) y e) = invMoll n (fun a => fderiv ℝ f a e) :=
    funext fun y => inv_moll_fderiv n hf1 hc y e
  rw [hfun, inv_moll_fderiv n hfe hfec x e]
  congr 1
  funext a
  rw [inv_fderiv2 ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero a)]

theorem inv_moll_gen (q : ℝ) (B : Euc d → Euc d) {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (n : ℕ) (x : Euc d) :
    kolmL q B (invMoll n f) x =
      (∑ i : Fin d, invMoll n (fun a => fderiv ℝ (fderiv ℝ f) a (EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1)) x) +
        invMoll n (fun a => fderiv ℝ f a (-q • x + B x)) x := by
  rw [kl_L_eq]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => inv_moll_second hf hc n x _
  · exact inv_moll_fderiv n (hf.of_le (by norm_num)) hc x _

theorem inv_cont_second {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (e : Euc d) :
    Continuous (fun a => fderiv ℝ (fderiv ℝ f) a e e) := by
  have h2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  exact (h2.clm_apply continuous_const).clm_apply continuous_const

theorem inv_cont_first {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (e : Euc d) :
    Continuous (fun a => fderiv ℝ f a e) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem inv_moll_tendsto (q : ℝ) (B : Euc d → Euc d) {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (x : Euc d) :
    Tendsto (fun n : ℕ => kolmL q B (invMoll n f) x) atTop (𝓝 (kolmL q B f x)) := by
  simp_rw [inv_moll_gen q B hf hc]
  rw [kl_L_eq]
  refine Tendsto.add (tendsto_finsetSum _ fun i _ => ?_) ?_
  · exact inv_conv_tendsto (inv_cont_second hf _) x
  · exact inv_conv_tendsto (inv_cont_first hf _) x


theorem inv_bdd {u : Euc d → ℝ} (hu : Continuous u) (hc : HasCompactSupport u) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ y, |u y| ≤ S := by
  obtain ⟨S, hS⟩ := hu.norm.bounded_above_of_compact_support hc.norm
  exact ⟨max S 0, le_max_right _ _, fun y => le_trans (by simpa using hS y) (le_max_left _ _)⟩

theorem inv_second_compact {f : Euc d → ℝ} (hc : HasCompactSupport f) (e : Euc d) :
    HasCompactSupport (fun a => fderiv ℝ (fderiv ℝ f) a e e) := by
  have h2 : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) := (hc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)
  have h3 : HasCompactSupport (fun a => fderiv ℝ (fderiv ℝ f) a e) :=
    h2.comp_left (g := fun T : Euc d →L[ℝ] Euc d →L[ℝ] ℝ => T e) (by simp)
  exact h3.comp_left (g := fun T : Euc d →L[ℝ] ℝ => T e) (by simp)

theorem inv_S1 {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ∃ S1 : ℝ, 0 ≤ S1 ∧ ∀ y, ‖fderiv ℝ f y‖ ≤ S1 := by
  have h1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have h3 : Continuous fun y => ‖fderiv ℝ f y‖ := continuous_norm.comp h1
  have h4 : HasCompactSupport fun y => ‖fderiv ℝ f y‖ := (hc.fderiv (𝕜 := ℝ)).norm
  obtain ⟨S, hS⟩ := h3.bounded_above_of_compact_support h4
  exact ⟨max S 0, le_max_right _ _, fun y => le_trans (by simpa using hS y) (le_max_left _ _)⟩

/-- A uniform bound for the mollified generator. -/
theorem inv_moll_bound (q : ℝ) (B : Euc d → Euc d) {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    ∃ S1 S2 : ℝ, 0 ≤ S1 ∧ 0 ≤ S2 ∧ ∀ (n : ℕ) (x : Euc d),
      |kolmL q B (invMoll n f) x| ≤ 3 * S2 + 3 * (S1 * ‖-q • x + B x‖) := by
  obtain ⟨S1, hS10, hS1⟩ := inv_S1 hf hc
  have hS2 : ∀ i : Fin d, ∃ S : ℝ, 0 ≤ S ∧ ∀ y, |fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1)| ≤ S := fun i =>
    inv_bdd (inv_cont_second hf _) (inv_second_compact hc _)
  choose S2i hS2i0 hS2i using hS2
  refine ⟨S1, ∑ i, S2i i, hS10, Finset.sum_nonneg fun i _ => hS2i0 i, fun n x => ?_⟩
  rw [inv_moll_gen q B hf hc]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i : Fin d, |invMoll n (fun a => fderiv ℝ (fderiv ℝ f) a (EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1)) x| ≤ 3 * S2i i := fun i =>
      inv_conv_bound n (inv_cont_second hf _) (hS2i i) x
    refine (Finset.sum_le_sum fun i _ => this i).trans ?_
    rw [← Finset.mul_sum]
  · have := inv_conv_bound n (inv_cont_first hf (-q • x + B x)) (S := S1 * ‖-q • x + B x‖)
      (fun y => by
        rw [← Real.norm_eq_abs]
        refine ((fderiv ℝ f y).le_opNorm _).trans ?_
        exact mul_le_mul_of_nonneg_right (hS1 y) (norm_nonneg _)) x
    linarith

theorem inv_kolmL_congr (q : ℝ) (B : Euc d → Euc d) {h₁ h₂ : Euc d → ℝ} {x : Euc d}
    (h : h₁ =ᶠ[𝓝 x] h₂) : kolmL q B h₁ x = kolmL q B h₂ x := by
  rw [kl_L_eq, kl_L_eq, h.fderiv_eq, h.fderiv.fderiv_eq]

theorem inv_kolmL_zero (q : ℝ) (B : Euc d → Euc d) (x : Euc d) :
    kolmL q B (fun _ => (0 : ℝ)) x = 0 := by
  rw [kl_L_eq]
  simp

/-- Infinitesimal invariance extends from `C_c^∞` to `C_c^2`. -/
theorem inv_compact_C2 {q : ℝ} {B : Euc d → Euc d} (hB : Continuous B) {μ : Measure (Euc d)}
    (hμ : IsInvariantMeasure (fun x => -q • x + B x) μ) {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : ∫ x, kolmL q B f x ∂μ = 0 := by
  have : IsProbabilityMeasure μ := hμ.1
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  have hR' : ∀ y, f y ≠ 0 → ‖y‖ ≤ R + 0 := fun y hy => by
    have := hR (subset_tsupport f hy)
    simpa using this
  obtain ⟨S1, S2, hS1, hS2, hbd⟩ := inv_moll_bound q B hf hc
  obtain ⟨Bρ, hBρ⟩ := (isCompact_closedBall (0 : Euc d) (R + 1)).exists_bound_of_continuousOn
    ((continuous_id.const_smul (-q)).add hB).continuousOn
  set K : ℝ := 3 * S2 + 3 * (S1 * max Bρ 0) with hK
  have hK0 : 0 ≤ K := by positivity
  have hzero : ∀ n : ℕ, ∫ x, kolmL q B (invMoll n f) x ∂μ = 0 := fun n =>
    hμ.2 (invMoll n f) (inv_moll_contDiff n hf.continuous) (inv_moll_compact n hc)
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => K)
    (F := fun n x => kolmL q B (invMoll n f) x) (f := kolmL q B f)
    (fun n => (kl_L_continuous q hB ((inv_moll_contDiff n hf.continuous).of_le (by norm_num))).aestronglyMeasurable)
    (integrable_const K)
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      by_cases hx : ‖x‖ ≤ R + 1
      · refine (hbd n x).trans ?_
        have : ‖-q • x + B x‖ ≤ max Bρ 0 := by
          have := hBρ x (by simpa using hx)
          simp only [Pi.add_apply] at this
          exact this.trans (le_max_left _ _)
        have := mul_le_mul_of_nonneg_left this hS1
        linarith
      · rw [inv_kolmL_congr q B (inv_moll_support n (R := R) (by simpa using hR') x (not_le.1 hx)),
          inv_kolmL_zero]
        simpa using hK0)
    (Eventually.of_forall fun x => inv_moll_tendsto q B hf hc x)
  simp_rw [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-! ### The cutoff -/

/-- The fixed cutoff bump: `1` on the unit ball, supported in the ball of radius `2`. -/
def invCut : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The rescaled cutoff `φ_R(x) = φ(x / R)`. -/
def invCutR (R : ℝ) : Euc d → ℝ := fun x => (invCut (d := d)) (R⁻¹ • x)

theorem inv_cutR_contDiff (R : ℝ) : ContDiff ℝ ∞ (invCutR (d := d) R) :=
  (invCut (d := d)).contDiff.comp (contDiff_const_smul R⁻¹)

theorem inv_cutR_zero {R : ℝ} (hR : 0 < R) {x : Euc d} (hx : 2 * R ≤ ‖x‖) : invCutR R x = 0 := by
  have : R⁻¹ • x ∉ Function.support (invCut (d := d)) := by
    rw [(invCut (d := d)).support_eq]
    intro h
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)] at h
    have hr : (invCut (d := d)).rOut = 2 := rfl
    rw [hr, inv_mul_eq_div, div_lt_iff₀ hR] at h
    linarith
  exact Function.notMem_support.1 this

theorem inv_cutR_one {R : ℝ} (hR : 0 < R) {x : Euc d} (hx : ‖x‖ ≤ R) : invCutR R x = 1 := by
  apply (invCut (d := d)).one_of_mem_closedBall
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
  show R⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_eq_div, div_le_one hR]; exact hx

theorem inv_cutR_nonneg (R : ℝ) (x : Euc d) : 0 ≤ invCutR R x := (invCut (d := d)).nonneg

theorem inv_cutR_le_one (R : ℝ) (x : Euc d) : invCutR R x ≤ 1 := (invCut (d := d)).le_one

theorem inv_cutR_compact {R : ℝ} (hR : 0 < R) : HasCompactSupport (invCutR (d := d) R) :=
  (invCut (d := d)).hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne'))

theorem inv_cut_K (i : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ y, ‖iteratedFDeriv ℝ i (invCut (d := d)) y‖ ≤ K := by
  have h1 : Continuous fun y => ‖iteratedFDeriv ℝ i (invCut (d := d)) y‖ :=
    ((invCut (d := d)).contDiff.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).norm
  have h2 : HasCompactSupport fun y => ‖iteratedFDeriv ℝ i (invCut (d := d)) y‖ :=
    ((invCut (d := d)).hasCompactSupport.iteratedFDeriv i).norm
  obtain ⟨S, hS⟩ := h1.bounded_above_of_compact_support h2
  exact ⟨max S 0, le_max_right _ _, fun y => le_trans (by simpa using hS y) (le_max_left _ _)⟩

theorem inv_cutR_deriv {R : ℝ} (hR : 0 < R) (i : ℕ) {K : ℝ}
    (hK : ∀ y, ‖iteratedFDeriv ℝ i (invCut (d := d)) y‖ ≤ K) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (invCutR R) x‖ ≤ K * (R⁻¹) ^ i := by
  have h := iteratedFDeriv_comp_const_smul (i := i) (f := (invCut (d := d))) R⁻¹
    ((invCut (d := d)).contDiff.of_le (by exact_mod_cast le_top))
  have e : iteratedFDeriv ℝ i (invCutR (d := d) R) x =
      (R⁻¹) ^ i • iteratedFDeriv ℝ i (invCut (d := d)) (R⁻¹ • x) := congrFun h x
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (inv_pos.2 hR) i), mul_comm]
  exact mul_le_mul_of_nonneg_right (hK _) (pow_nonneg (inv_pos.2 hR).le i)

theorem inv_cutR_deriv_zero {R : ℝ} (hR : 0 < R) (i : ℕ) {x : Euc d} (hx : 2 * R < ‖x‖) :
    iteratedFDeriv ℝ i (invCutR (d := d) R) x = 0 := by
  have hx' : x ∉ tsupport (invCutR (d := d) R) := by
    intro h
    have hsub : tsupport (invCutR (d := d) R) ⊆ Metric.closedBall 0 (2 * R) := by
      refine closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall
      rw [mem_closedBall_zero_iff]
      by_contra hlt
      exact hy (inv_cutR_zero hR (not_le.1 hlt).le)
    have := hsub h
    rw [mem_closedBall_zero_iff] at this
    linarith
  exact image_eq_zero_of_notMem_tsupport (fun h => hx' (tsupport_iteratedFDeriv_subset i h))


theorem inv_cut_prod {R : ℝ} (hR : 1 ≤ R) {i : ℕ} (hi : 1 ≤ i) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ y, ‖iteratedFDeriv ℝ i (invCut (d := d)) y‖ ≤ K) {g : Euc d → ℝ} {a a' : ℝ}
    (ha : 0 ≤ a) (ha' : 0 ≤ a') (hga : ∀ y, |g y| ≤ a + a' * ‖y‖) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (invCutR R) x‖ * |g x| ≤ K * (a + 2 * a') := by
  have hR0 : 0 < R := by linarith
  by_cases hx : ‖x‖ ≤ 2 * R
  · have h1 := inv_cutR_deriv hR0 i hK x
    have hr1 : (R⁻¹) ^ i ≤ R⁻¹ := pow_le_of_le_one (inv_pos.2 hR0).le (inv_le_one_of_one_le₀ hR) (by omega)
    have hr0 : 0 ≤ (R⁻¹) ^ i := pow_nonneg (inv_pos.2 hR0).le i
    have hrR : R⁻¹ * R = 1 := inv_mul_cancel₀ hR0.ne'
    have hg : |g x| ≤ a + 2 * a' * R := by
      refine (hga x).trans ?_
      nlinarith
    have h2 : ‖iteratedFDeriv ℝ i (invCutR R) x‖ * |g x| ≤ K * (R⁻¹) ^ i * (a + 2 * a' * R) :=
      mul_le_mul h1 hg (abs_nonneg _) (by positivity)
    refine h2.trans ?_
    have h3 : (R⁻¹) ^ i * (a + 2 * a' * R) ≤ a + 2 * a' := by
      have : (R⁻¹) ^ i * (a + 2 * a' * R) = (R⁻¹) ^ i * a + 2 * a' * ((R⁻¹) ^ i * R) := by ring
      rw [this]
      have h4 : (R⁻¹) ^ i * a ≤ a := by
        have : (R⁻¹) ^ i ≤ 1 := pow_le_one₀ (inv_pos.2 hR0).le (inv_le_one_of_one_le₀ hR)
        nlinarith
      have h5 : (R⁻¹) ^ i * R ≤ 1 := by nlinarith
      nlinarith
    calc K * (R⁻¹) ^ i * (a + 2 * a' * R) = K * ((R⁻¹) ^ i * (a + 2 * a' * R)) := by ring
      _ ≤ K * (a + 2 * a') := mul_le_mul_of_nonneg_left h3 hK0
  · rw [inv_cutR_deriv_zero hR0 i (not_le.1 hx)]
    simp only [norm_zero, zero_mul]
    positivity

theorem inv_cut_small {R : ℝ} (hR : 1 ≤ R) {i : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ y, ‖iteratedFDeriv ℝ i (invCut (d := d)) y‖ ≤ K) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (invCutR R) x‖ ≤ K := by
  have hR0 : 0 < R := by linarith
  refine (inv_cutR_deriv hR0 i hK x).trans ?_
  have : (R⁻¹) ^ i ≤ 1 := pow_le_one₀ (inv_pos.2 hR0).le (inv_le_one_of_one_le₀ hR)
  nlinarith

/-- Uniform bounds for the cut-off function `φ_R g`. -/
theorem inv_cut_bounds {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) {M1 M2 : ℝ}
    (hM1 : ∀ y, ‖fderiv ℝ g y‖ ≤ M1) (hM2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ M2) :
    ∃ M1' M2' : ℝ, ∀ R : ℝ, 1 ≤ R →
      (∀ x, ‖fderiv ℝ (fun y => invCutR R y * g y) x‖ ≤ M1') ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ (fun y => invCutR R y * g y)) x‖ ≤ M2') := by
  have hM10 : 0 ≤ M1 := by
    have := hM1 0; have := norm_nonneg (fderiv ℝ g 0); linarith
  have hM20 : 0 ≤ M2 := by
    have := hM2 0; have := norm_nonneg (fderiv ℝ (fderiv ℝ g) 0); linarith
  obtain ⟨K1, hK10, hK1⟩ := inv_cut_K (d := d) 1
  obtain ⟨K2, hK20, hK2⟩ := inv_cut_K (d := d) 2
  set a : ℝ := |g 0| with ha
  have hga : ∀ y, |g y| ≤ a + M1 * ‖y‖ := fun y => kl_abs_le_lin hg hM1 y
  refine ⟨M1 + K1 * (a + 2 * M1), M2 + 2 * K1 * M1 + K2 * (a + 2 * M1), fun R hR => ⟨fun x => ?_, fun x => ?_⟩⟩
  · have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := invCutR (d := d) R) (g := g) (N := 2)
      ((inv_cutR_contDiff R).of_le (by norm_num)) hg x (n := 1) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_self, Nat.cast_one, one_mul, norm_iteratedFDeriv_zero, Nat.reduceSub] at hmul
    rw [norm_iteratedFDeriv_one (f := g)] at hmul
    rw [← norm_iteratedFDeriv_one]
    have h1 := inv_cut_prod hR (i := 1) le_rfl hK10 hK1 (abs_nonneg _) hM10 hga x
    have hφ1 : ‖invCutR (d := d) R x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_cutR_nonneg _ _)]; exact inv_cutR_le_one _ _
    have h2 : ‖invCutR (d := d) R x‖ * ‖fderiv ℝ g x‖ ≤ 1 * M1 :=
      mul_le_mul hφ1 (hM1 x) (norm_nonneg _) zero_le_one
    simp only [Real.norm_eq_abs] at hmul h2 hφ1
    linarith
  · have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := invCutR (d := d) R) (g := g) (N := 2)
      ((inv_cutR_contDiff R).of_le (by norm_num)) hg x (n := 2) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_one, one_mul,
      norm_iteratedFDeriv_zero, Nat.reduceSub, Nat.choose] at hmul
    rw [norm_iteratedFDeriv_one (f := g)] at hmul
    rw [kl_norm_fderiv_fderiv']
    rw [← kl_norm_fderiv_fderiv' (f := g)] at hmul
    have h1 := inv_cut_prod hR (i := 1) le_rfl hK10 hK1 (abs_nonneg _) hM10 hga x
    have h2 := inv_cut_prod hR (i := 2) (by norm_num) hK20 hK2 (abs_nonneg _) hM10 hga x
    have h3 := inv_cut_small hR (i := 1) hK10 hK1 x
    have hφ1 : ‖invCutR (d := d) R x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_cutR_nonneg _ _)]; exact inv_cutR_le_one _ _
    have h4 : ‖invCutR (d := d) R x‖ * ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ 1 * M2 :=
      mul_le_mul hφ1 (hM2 x) (norm_nonneg (fderiv ℝ (fderiv ℝ g) x)) zero_le_one
    have h5 : ‖iteratedFDeriv ℝ 1 (invCutR (d := d) R) x‖ * ‖fderiv ℝ g x‖ ≤ K1 * M1 :=
      mul_le_mul h3 (hM1 x) (norm_nonneg _) hK10
    simp only [Real.norm_eq_abs] at hmul h4 hφ1
    norm_num at hmul
    rw [← norm_iteratedFDeriv_one (f := invCutR (d := d) R)] at hmul
    linarith

theorem inv_integrable_norm {μ : Measure (Euc d)} [IsFiniteMeasure μ]
    (hμ2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) μ) : Integrable (fun x : Euc d => ‖x‖) μ := by
  refine ((hμ2.add (integrable_const (1 : ℝ))).mono' continuous_norm.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖x‖ - 1)]

theorem inv_integrable_lin {μ : Measure (Euc d)} [IsFiniteMeasure μ]
    (hμ2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) μ) {u : Euc d → ℝ} (hu : Continuous u) {A : ℝ}
    (hbd : ∀ y, |u y| ≤ A * (1 + ‖y‖)) : Integrable u μ := by
  refine ((((integrable_const (1 : ℝ)).add (inv_integrable_norm hμ2)).const_mul A)).mono'
    hu.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact hbd y

theorem inv_growth (q : ℝ) {B : Euc d → Euc d} {Mb : ℝ} (hBb : ∀ y, ‖B y‖ ≤ Mb) {h : Euc d → ℝ}
    {M1 M2 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M1) (hM2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ M2)
    (y : Euc d) :
    |kolmL q B h y| ≤ ((d * M2 + M1 * Mb) + M1 * |q|) * (1 + ‖y‖) := by
  have hM10 : 0 ≤ M1 := by
    have := hM1 0; have := norm_nonneg (fderiv ℝ h 0); linarith
  have hM20 : 0 ≤ M2 := by
    have := hM2 0; have := norm_nonneg (fderiv ℝ (fderiv ℝ h) 0); linarith
  have hMb : 0 ≤ Mb := (norm_nonneg (B 0)).trans (hBb 0)
  refine (kl_L_growth q hBb hM1 hM2 y).trans ?_
  have : 0 ≤ (d : ℝ) * M2 + M1 * Mb := by positivity
  nlinarith [mul_nonneg hM10 (abs_nonneg q), norm_nonneg y]

/-- **Infinitesimal invariance for `C²` functions with bounded first and second derivatives.** -/
theorem inv_generator {q Mb : ℝ} {B : Euc d → Euc d} (hB : Continuous B) (hBb : ∀ y, ‖B y‖ ≤ Mb)
    {μ : Measure (Euc d)} (hμ : IsInvariantMeasure (fun x => -q • x + B x) μ)
    (hμ2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) μ) {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g)
    {M1 M2 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ g y‖ ≤ M1) (hM2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ M2) :
    Integrable (kolmL q B g) μ ∧ ∫ x, kolmL q B g x ∂μ = 0 := by
  have : IsProbabilityMeasure μ := hμ.1
  obtain ⟨M1', M2', hbnd⟩ := inv_cut_bounds hg hM1 hM2
  set A : ℝ := ((d * M2' + M1' * Mb) + M1' * |q|) with hA
  have hf2 : ∀ n : ℕ, ContDiff ℝ 2 (fun y => invCutR ((n : ℝ) + 1) y * g y) := fun n =>
    ((inv_cutR_contDiff _).of_le (by norm_num)).mul hg
  have hfc : ∀ n : ℕ, HasCompactSupport (fun y => invCutR ((n : ℝ) + 1) y * g y) := fun n =>
    (inv_cutR_compact (by positivity)).mul_right
  have hzero : ∀ n : ℕ, ∫ x, kolmL q B (fun y => invCutR ((n : ℝ) + 1) y * g y) x ∂μ = 0 :=
    fun n => inv_compact_C2 hB hμ (hf2 n) (hfc n)
  have hR1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hbound : ∀ n : ℕ, ∀ x, |kolmL q B (fun y => invCutR ((n : ℝ) + 1) y * g y) x| ≤
      A * (1 + ‖x‖) := fun n x =>
    inv_growth q hBb (hbnd _ (hR1 n)).1 (hbnd _ (hR1 n)).2 x
  have hA0 : 0 ≤ A := by
    have h1 := hbnd 1 le_rfl
    have : 0 ≤ M1' := by
      have := h1.1 0; have := norm_nonneg (fderiv ℝ (fun y => invCutR 1 y * g y) 0); linarith
    have : 0 ≤ M2' := by
      have := h1.2 0
      have := norm_nonneg (fderiv ℝ (fderiv ℝ (fun y => invCutR 1 y * g y)) 0); linarith
    have hMb : 0 ≤ Mb := (norm_nonneg (B 0)).trans (hBb 0)
    positivity
  have hint : Integrable (fun x : Euc d => A * (1 + ‖x‖)) μ :=
    ((integrable_const (1 : ℝ)).add (inv_integrable_norm hμ2)).const_mul A
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ) (fun x => A * (1 + ‖x‖))
    (F := fun (n : ℕ) x => kolmL q B (fun y => invCutR ((n : ℝ) + 1) y * g y) x)
    (f := kolmL q B g)
    (fun n => (kl_L_continuous q hB (hf2 n)).aestronglyMeasurable) hint
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hbound n x)
    (Eventually.of_forall fun x => by
      obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
      refine (tendsto_const_nhds (x := kolmL q B g x)).congr' ?_
      refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have hxn : ‖x‖ < (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have hopen : IsOpen {y : Euc d | ‖y‖ < (n : ℝ) + 1} := isOpen_lt continuous_norm continuous_const
      have heq : (fun y => invCutR ((n : ℝ) + 1) y * g y) =ᶠ[𝓝 x] g := by
        filter_upwards [hopen.mem_nhds hxn] with y hy
        have hy' : ‖y‖ < (n : ℝ) + 1 := hy
        simp [inv_cutR_one (by positivity : (0 : ℝ) < (n : ℝ) + 1) hy'.le]
      exact (inv_kolmL_congr q B heq).symm)
  simp_rw [hzero] at hlim
  refine ⟨?_, tendsto_nhds_unique hlim tendsto_const_nhds⟩
  exact inv_integrable_lin hμ2 (kl_L_continuous q hB hg) (A := ((d * M2 + M1 * Mb) + M1 * |q|))
    (fun y => inv_growth q hBb hM1 hM2 y)

end HRS.MS.PoisInv
