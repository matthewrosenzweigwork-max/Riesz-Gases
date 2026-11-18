/-
# TRR (Lemma 4.18 `thermal_response_rates`) — chain plan and helper 1

Route (all in `C(T^d, ℝ)` with the sup norm; no Sobolev spaces needed):
* `E := C(Torus d, ℝ)`, `G v = g ⋆ v` (bounded, compact: Arzelà–Ascoli, L¹ translation modulus),
  `N w = exp∘w / ∫ exp∘w` (smooth, `D N(w) h = ρ (h - μ h)`, `ρ = N w`),
  `Λ w = w + β G (N w)` smooth `E → E`; the thermal equation for the potential `ψ` (`V = -ψ/β`)
  reads `Λ w = ψ`, `ρ = N w`.
* `D Λ(w) = I + A`, `A = β G ∘ (ρ(· - μ ·))` compact; `I + A` injective because a kernel element `h`
  gives `q = h - μ h ∈ C(T)` solving `IsResponse g (ρ dx) β 0 q` (unique solution `0`,
  `exists_unique_response`); Fredholm alternative (`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`)
  makes `D Λ(w)` a `ContinuousLinearEquiv`.  Inverse function theorem (`ContDiffAt.to_localInverse`).
* Uniqueness of continuous thermal densities (`MFThermal.thermal_unique`, `Q41.q41_thermal_pos_cont`)
  identifies the local branch `w(p)`, `p ∈ ℝ²`, `ψ(p) = a cos_k + b sin_k`, with the given `ρ`.
  Translation covariance `ρ_θ(x) = Φ(θ cos_k x, -θ sin_k x)(0)` gives joint `C^∞` in `(θ,x)`.

Chain (sizes in lines):
 TRRAux1 (~250) Banach setup: `E`, convolution CLM `G`, `‖G‖ ≤ ‖g‖₁`, compactness of `G`.
 TRRAux2 (~200) `N`, `Λ`: `ContDiff`, `HasFDerivAt`, formulas; `ρ`-density facts of `N w`.
 TRRAux3 (~250) invertibility of `D Λ(w)` (injectivity via IsResponse uniqueness + Fredholm).
 TRRAux4 (~250) thermal equation <-> `Λ w = ψ`; translation covariance of thermal densities.
 TRRAux5 (~300) IFT branch, identification, `θ ↦ ρ_θ ∈ E` is `ContDiff`, joint smoothness (clause 1).
 TRRAux6 (~300) derivative identities: `q = ∂_θρ/ρ` is `IsResponse` solution (clause 2); `M' = C` (clause 3).
 TRRAux7 (~300) self-adjointness of `R`, `B = c · ∫ρ ∂_θρ`, smoothness of `B`.
 TRRAux8 (~300) `θ = 0`: `ρ_0 = 1`, `g ⋆ cos_k = ĝ(k) cos_k`, `∫cos² = 1/2`, `B(0) = 0`, `B'(0)` value, `> 0`.
 TRRFinal (~80) `HRS.TRR.thermal_response_rates_proof` + `example`.
-/
import HRS.Equilibrium.Response
import HRS.Sections.Q41Aux14
import HRS.Equilibrium.Q32aAux1

noncomputable section

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace HRS.TRR

variable {d : ℕ}

/-- The Banach space `C(T^d, ℝ)` of continuous functions with the sup norm. -/
abbrev Cb (d : ℕ) := C(Torus d, ℝ)

section Conv

variable {g : Torus d → ℝ}

lemma trr_conv_integrable (hg : Integrable g) (v : Cb d) (x : Torus d) :
    Integrable fun y => g (x - y) * v y :=
  (hg.comp_sub_left x).mul_bdd v.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using
      (v.norm_coe_le_norm y))

lemma trr_integral_abs_shift (g : Torus d → ℝ) (x : Torus d) :
    ∫ y, |g (x - y)| = ∫ y, |g y| := by
  rw [← integral_sub_left_eq_self (fun y => |g y|) volume x]

lemma trr_convFun_bound (hg : Integrable g) (v : Cb d) (x : Torus d) :
    |convFun g v x| ≤ (∫ y, |g y|) * ‖v‖ := by
  unfold convFun
  rw [← Real.norm_eq_abs]
  have hi : Integrable fun y => |g (x - y)| := (hg.comp_sub_left x).abs
  calc ‖∫ y, g (x - y) * v y‖ ≤ ∫ y, |g (x - y)| * ‖v‖ :=
        norm_integral_le_of_norm_le (hi.mul_const _) (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using v.norm_coe_le_norm y)
            (abs_nonneg _))
    _ = (∫ y, |g y|) * ‖v‖ := by rw [integral_mul_const, trr_integral_abs_shift]

/-- Convolution with `g` as a continuous linear operator on `C(T^d, ℝ)`. -/
def convCLM (hg : Integrable g) : Cb d →L[ℝ] Cb d :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨convFun g v, PDE.MFAux.continuous_convFun hg v.continuous⟩
      map_add' := fun v w => by
        ext x
        simp only [ContinuousMap.add_apply, ContinuousMap.coe_mk]
        unfold convFun
        rw [← integral_add (trr_conv_integrable hg v x) (trr_conv_integrable hg w x)]
        congr 1; funext y; simp only [ContinuousMap.add_apply]; ring
      map_smul' := fun c v => by
        ext x
        simp only [ContinuousMap.smul_apply, ContinuousMap.coe_mk, RingHom.id_apply, smul_eq_mul]
        unfold convFun
        rw [← integral_const_mul]
        congr 1; funext y; simp only [ContinuousMap.smul_apply, smul_eq_mul]; ring }
    (∫ y, |g y|)
    (fun v => by
      refine (ContinuousMap.norm_le _ (mul_nonneg (integral_nonneg fun _ => abs_nonneg _)
        (norm_nonneg _))).2 fun x => ?_
      simpa [Real.norm_eq_abs] using trr_convFun_bound hg v x)

lemma convCLM_apply (hg : Integrable g) (v : Cb d) (x : Torus d) :
    convCLM hg v x = convFun g v x := rfl

/-- Translation modulus estimate. -/
lemma trr_conv_modulus (hg : Integrable g) (v : Cb d) (x x₀ : Torus d) :
    |convFun g v x - convFun g v x₀| ≤ ‖v‖ * ∫ w, |g (w - (x₀ - x)) - g w| := by
  have hdiff : convFun g v x - convFun g v x₀ = ∫ y, (g (x - y) - g (x₀ - y)) * v y := by
    unfold convFun
    rw [← integral_sub (trr_conv_integrable hg v x) (trr_conv_integrable hg v x₀)]
    congr 1; funext y; ring
  have iabs : Integrable fun y => |g (x - y) - g (x₀ - y)| :=
    ((hg.comp_sub_left x).sub (hg.comp_sub_left x₀)).abs
  have hsub : ∫ y, |g (x - y) - g (x₀ - y)| = ∫ w, |g (w - (x₀ - x)) - g w| := by
    rw [← integral_sub_left_eq_self (fun w => |g (w - (x₀ - x)) - g w|) volume x₀]
    congr 1; funext y
    have : x₀ - y - (x₀ - x) = x - y := by abel
    rw [this]
  rw [hdiff, ← Real.norm_eq_abs]
  calc ‖∫ y, (g (x - y) - g (x₀ - y)) * v y‖ ≤ ∫ y, |g (x - y) - g (x₀ - y)| * ‖v‖ :=
        norm_integral_le_of_norm_le (iabs.mul_const _) (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using v.norm_coe_le_norm y)
            (abs_nonneg _))
    _ = ‖v‖ * ∫ w, |g (w - (x₀ - x)) - g w| := by rw [integral_mul_const, hsub]; ring

/-- Compactness of the convolution operator on `C(T^d, ℝ)` (Arzelà–Ascoli). -/
theorem convCLM_isCompact (hg : Integrable g) : IsCompactOperator (convCLM hg) := by
  set e := ContinuousMap.equivBoundedOfCompact (Torus d) ℝ with he
  set A : Set (Torus d →ᵇ ℝ) := e '' (convCLM hg '' Metric.closedBall 0 1) with hA
  have hmod : ∀ x₀ : Torus d, Tendsto (fun x : Torus d => ∫ w, |g (w - (x₀ - x)) - g w|)
      (𝓝 x₀) (𝓝 0) := by
    intro x₀
    refine (PDE.MFThermalExist.l1_modulus hg).comp ?_
    have hc : Continuous fun x : Torus d => x₀ - x := continuous_const.sub continuous_id
    have := hc.tendsto x₀
    simp only [sub_self] at this
    exact this
  have hbdd : ∀ f : Torus d →ᵇ ℝ, ∀ x, f ∈ A → f x ∈ Set.Icc (-(∫ y, |g y|)) (∫ y, |g y|) := by
    intro f x hf
    obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := hf
    have hv1 : ‖v‖ ≤ 1 := by simpa using hv
    have := trr_convFun_bound hg v x
    have h0 : 0 ≤ ∫ y, |g y| := integral_nonneg fun _ => abs_nonneg _
    have : |convFun g v x| ≤ ∫ y, |g y| := this.trans (by nlinarith)
    exact abs_le.1 this
  have heq : Equicontinuous ((↑) : A → Torus d → ℝ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    have := (Metric.tendsto_nhds.1 (hmod x₀)) ε hε
    filter_upwards [this] with x hx f
    obtain ⟨_, ⟨v, hv, rfl⟩, hf⟩ := f.2
    have hv1 : ‖v‖ ≤ 1 := by simpa using hv
    have hfv : (f : Torus d → ℝ) = fun y => convFun g v y := by
      rw [← hf]; rfl
    rw [hfv, Real.dist_eq]
    simp only
    rw [abs_sub_comm]
    refine lt_of_le_of_lt (trr_conv_modulus hg v x x₀) ?_
    rw [Real.dist_eq, sub_zero] at hx
    have h0 : 0 ≤ ∫ w, |g (w - (x₀ - x)) - g w| := integral_nonneg fun _ => abs_nonneg _
    rw [abs_of_nonneg h0] at hx
    nlinarith
  have hcomp := BoundedContinuousFunction.arzela_ascoli _ isCompact_Icc A hbdd heq
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ one_pos, e ⁻¹' closure A, ?_, ?_⟩
  · have hind : Topology.IsInducing e :=
      (ContinuousMap.isUniformEmbedding_equivBoundedOfCompact (Torus d) ℝ).isInducing
    rw [hind.isCompact_iff]
    have : e '' (e ⁻¹' closure A) = closure A := Set.image_preimage_eq _ e.surjective
    rw [this]; exact hcomp
  · intro f hf
    obtain ⟨v, hv, rfl⟩ := hf
    exact subset_closure ⟨_, ⟨v, hv, rfl⟩, rfl⟩

end Conv

end HRS.TRR
