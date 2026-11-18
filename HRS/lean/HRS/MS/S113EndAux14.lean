import HRS.MS.S113EndAux13

/-!
# S11.3 endpoint (worker S11X), part 14: coordinate lines, kernel calculus, and the derivative of the modulated Gibbs density along a line

* `s113x_line Y i k τ`: the configuration with `Y_i` replaced by `Y_i + τ e_k` (the line of `movPartial`).
* `s113x_G_neg`, `s113x_g_hasFDerivAt`, `s113x_G_diffAt`: oddness of `∇g`, `D g = ⟨∇g, ·⟩` and differentiability of `∇g` off the origin.
* `s113x_Fm_line`: derivative of `τ ↦ F_N(line τ, μ)`, `= N⁻² ∑_{j≠i} (∇g)_k(Y_i - Y_j) - N⁻¹ (∇(g*μ))_k(Y_i)`.
* `s113x_Q_line`: derivative of `τ ↦ q_N(line τ)`, `= q_N(Y) Ψ`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113BD

open HRS HRS.Whole

variable {d N : ℕ}

section Kernel

theorem s113x_G_neg (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    rieszKernelGrad d s (-z) = -rieszKernelGrad d s z := by
  rw [movtr_rieszKernelGrad_eq s (neg_ne_zero.2 hz), movtr_rieszKernelGrad_eq s hz, norm_neg]
  simp [neg_smul, smul_neg]

theorem s113x_g_hasFDerivAt (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    HasFDerivAt (rieszKernel d s) (innerSL ℝ (rieszKernelGrad d s z)) z := by
  have hd : DifferentiableAt ℝ (rieszKernel d s) z :=
    (rieszKernel_contDiffOn.contDiffAt (isOpen_ne.mem_nhds hz)).differentiableAt (by simp)
  convert hd.hasFDerivAt using 1
  ext v
  rw [innerSL_apply_apply, real_inner_comm]
  exact HRS.MS.PoisKolm.kl_inner_gradient (rieszKernel d s) z v

theorem s113x_G_diffAt (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    DifferentiableAt ℝ (rieszKernelGrad d s) z := by
  have hev : (rieszKernelGrad d s) =ᶠ[𝓝 z] fun w => (-(movtr_sigma s * ‖w‖ ^ (-s - 2))) • w := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact movtr_rieszKernelGrad_eq s hw
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have h1 : DifferentiableAt ℝ (fun w : Euc d => ‖w‖) z := differentiableAt_id.norm ℝ hz
  have h2 : DifferentiableAt ℝ (fun w : Euc d => ‖w‖ ^ (-s - 2)) z :=
    h1.rpow_const (Or.inl (norm_ne_zero_iff.2 hz))
  exact ((h2.const_mul _).neg).smul differentiableAt_id

theorem s113x_hasDerivAt_line_comp {φ : Euc d → ℝ} {φ' : Euc d →L[ℝ] ℝ} {z w : Euc d}
    (h : HasFDerivAt φ φ' z) : HasDerivAt (fun τ : ℝ => φ (z + τ • w)) (φ' w) 0 := by
  have hline : HasDerivAt (fun τ : ℝ => z + τ • w) w 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
    simpa using this
  have h' : HasFDerivAt φ φ' (z + (0 : ℝ) • w) := by simpa using h
  exact h'.comp_hasDerivAt (0 : ℝ) hline

end Kernel

section Line

/-- The line through `Y` in direction `e_k` of particle `i`. -/
def s113x_line (Y : EucConfig d N) (i : Fin N) (k : Fin d) (τ : ℝ) : EucConfig d N :=
  Function.update Y i (Y i + τ • EuclideanSpace.single k (1 : ℝ))

theorem s113x_movPartial_eq (f : EucConfig d N → ℝ) (i : Fin N) (k : Fin d) (Y : EucConfig d N) :
    movPartial f i k Y = deriv (fun τ => f (s113x_line Y i k τ)) 0 := rfl

variable (Y : EucConfig d N) (i : Fin N) (k : Fin d)

theorem s113x_line_zero : s113x_line Y i k 0 = Y := by
  simp [s113x_line]

theorem s113x_line_shift (τ σ : ℝ) :
    s113x_line (s113x_line Y i k τ) i k σ = s113x_line Y i k (τ + σ) := by
  unfold s113x_line
  simp only [Function.update_idem, Function.update_self]
  congr 1
  rw [add_smul, add_assoc]

theorem s113x_line_apply_same (τ : ℝ) :
    s113x_line Y i k τ i = Y i + τ • EuclideanSpace.single k (1 : ℝ) := by
  simp [s113x_line]

theorem s113x_line_apply_ne {a : Fin N} (h : a ≠ i) (τ : ℝ) : s113x_line Y i k τ a = Y a := by
  simp [s113x_line, h]

theorem s113x_coll_closed : IsClosed (eucCollisionSet d N) := by
  have : eucCollisionSet d N = ⋃ i, ⋃ j, ⋃ _ : i ≠ j, {X : EucConfig d N | X i = X j} := by
    ext X; simp [eucCollisionSet]
  rw [this]
  exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => isClosed_eq (continuous_apply i) (continuous_apply j)

theorem s113x_line_continuous : Continuous (fun τ : ℝ => s113x_line Y i k τ) := by
  unfold s113x_line
  exact continuous_const.update i (continuous_const.add (continuous_id.smul continuous_const))

theorem s113x_line_noncoll (hY : Y ∉ eucCollisionSet d N) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), s113x_line Y i k τ ∉ eucCollisionSet d N := by
  have h0 : s113x_line Y i k 0 ∈ (eucCollisionSet d N)ᶜ := by
    rw [s113x_line_zero]; exact hY
  exact ((s113x_line_continuous Y i k).continuousAt).preimage_mem_nhds
    (s113x_coll_closed.isOpen_compl.mem_nhds h0)

theorem s113x_line_sub (a b : Fin N) (τ : ℝ) :
    s113x_line Y i k τ a - s113x_line Y i k τ b =
      (Y a - Y b) + τ • ((if a = i then EuclideanSpace.single k (1 : ℝ) else 0) -
        (if b = i then EuclideanSpace.single k (1 : ℝ) else 0)) := by
  by_cases ha : a = i <;> by_cases hb : b = i
  · subst ha; subst hb; simp
  · subst ha; simp [s113x_line_apply_same, s113x_line_apply_ne Y _ k hb, hb]; abel
  · subst hb; simp [s113x_line_apply_same, s113x_line_apply_ne Y _ k ha, ha]; abel
  · simp [s113x_line_apply_ne Y i k ha, s113x_line_apply_ne Y i k hb, ha, hb]

end Line


section Energy

theorem s113x_inner_single (v : Euc d) (k : Fin d) :
    inner ℝ v (EuclideanSpace.single k (1 : ℝ)) = v k := by
  simp [EuclideanSpace.inner_single_right]

theorem s113x_pair_sum (c : Fin N → Fin N → ℝ) (i : Fin N) :
    ∑ a, ∑ b ∈ Finset.univ.erase a, ((if a = i then c a b else 0) - (if b = i then c a b else 0)) =
      ∑ b ∈ Finset.univ.erase i, c i b - ∑ a ∈ Finset.univ.erase i, c a i := by
  simp only [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single i]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  · have : ∀ a : Fin N, ∑ b ∈ Finset.univ.erase a, (if b = i then c a b else 0) =
        if a ≠ i then c a i else 0 := by
      intro a
      rw [Finset.sum_ite_eq']
      by_cases ha : a = i
      · simp [ha]
      · simp [ha, Ne.symm ha]
    simp only [this]
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp

theorem s113x_Fm_line {s : ℝ} {μ : Measure (Euc d)} {Fv : Euc d → Euc d}
    (hΓ : ∀ x, HasFDerivAt (HRS.Whole.convMeasure (rieszKernel d s) μ) (innerSL ℝ (Fv x)) x)
    {Y : EucConfig d N} (hY : Y ∉ eucCollisionSet d N) (i : Fin N) (k : Fin d) :
    HasDerivAt (fun τ => rieszModulatedEnergy d s (s113x_line Y i k τ) μ)
      ((1 / (N : ℝ) ^ 2) * ∑ j ∈ Finset.univ.erase i, (rieszKernelGrad d s (Y i - Y j)) k -
        (1 / (N : ℝ)) * (Fv (Y i)) k) 0 := by
  set e : Euc d := EuclideanSpace.single k (1 : ℝ) with he
  have hpair : ∀ a ∈ (Finset.univ : Finset (Fin N)), ∀ b ∈ Finset.univ.erase a,
      HasDerivAt (fun τ => rieszKernel d s (s113x_line Y i k τ a - s113x_line Y i k τ b))
        ((if a = i then inner ℝ (rieszKernelGrad d s (Y a - Y b)) e else 0) -
          (if b = i then inner ℝ (rieszKernelGrad d s (Y a - Y b)) e else 0)) 0 := by
    intro a _ b hb
    have hne : Y a - Y b ≠ 0 := by
      intro h
      exact hY ⟨a, b, (Finset.ne_of_mem_erase hb).symm, sub_eq_zero.1 h⟩
    have h1 := s113x_hasDerivAt_line_comp
      (w := (if a = i then e else 0) - (if b = i then e else 0)) (s113x_g_hasFDerivAt s hne)
    simp only [innerSL_apply_apply] at h1
    have h2 : inner ℝ (rieszKernelGrad d s (Y a - Y b)) ((if a = i then e else 0) - (if b = i then e else 0)) =
        (if a = i then inner ℝ (rieszKernelGrad d s (Y a - Y b)) e else 0) -
          (if b = i then inner ℝ (rieszKernelGrad d s (Y a - Y b)) e else 0) := by
      split_ifs <;> simp [inner_sub_right]
    rw [h2] at h1
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
    simp only [s113x_line_sub, he]
  have hsum : HasDerivAt (fun τ => ∑ a, ∑ b ∈ Finset.univ.erase a,
      rieszKernel d s (s113x_line Y i k τ a - s113x_line Y i k τ b))
      (∑ a, ∑ b ∈ Finset.univ.erase a, ((if a = i then inner ℝ (rieszKernelGrad d s (Y a - Y b)) e else 0) -
          (if b = i then inner ℝ (rieszKernelGrad d s (Y a - Y b)) e else 0))) 0 :=
    HasDerivAt.fun_sum fun a ha => HasDerivAt.fun_sum fun b hb => hpair a ha b hb
  have hone : ∀ a ∈ (Finset.univ : Finset (Fin N)),
      HasDerivAt (fun τ => HRS.Whole.convMeasure (rieszKernel d s) μ (s113x_line Y i k τ a))
        (if a = i then (Fv (Y i)) k else 0) 0 := by
    intro a _
    by_cases ha : a = i
    · subst ha
      have h1 := s113x_hasDerivAt_line_comp (w := e) (hΓ (Y a))
      simp only [innerSL_apply_apply, he, s113x_inner_single] at h1
      simp only [ite_true]
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
      simp only [s113x_line_apply_same, he]
    · simp only [ha, ite_false]
      have : (fun τ => HRS.Whole.convMeasure (rieszKernel d s) μ (s113x_line Y i k τ a)) =
          fun _ => HRS.Whole.convMeasure (rieszKernel d s) μ (Y a) := by
        funext τ; rw [s113x_line_apply_ne Y i k ha]
      rw [this]
      exact hasDerivAt_const _ _
  have hS : HasDerivAt (fun τ => ∑ a, HRS.Whole.convMeasure (rieszKernel d s) μ (s113x_line Y i k τ a))
      (∑ a, (if a = i then (Fv (Y i)) k else 0)) 0 := HasDerivAt.fun_sum hone
  have hF := (((hsum.const_mul (1 / (2 * (N : ℝ) ^ 2))).sub (hS.const_mul (1 / (N : ℝ)))).add_const
    (1 / 2 * HRS.Whole.energyPairing (rieszKernel d s) μ μ))
  unfold rieszModulatedEnergy HRS.Whole.modulatedEnergy
  convert hF using 1
  -- the value
  have hc : ∀ a b : Fin N, a ≠ b → inner ℝ (rieszKernelGrad d s (Y b - Y a)) e = -inner ℝ (rieszKernelGrad d s (Y a - Y b)) e := by
    intro a b hab
    have hne : Y a - Y b ≠ 0 := fun h => hY ⟨a, b, hab, sub_eq_zero.1 h⟩
    rw [show Y b - Y a = -(Y a - Y b) by abel, s113x_G_neg s hne, inner_neg_left]
  rw [s113x_pair_sum (fun a b => inner ℝ (rieszKernelGrad d s (Y a - Y b)) e) i]
  have h2 : ∑ a ∈ Finset.univ.erase i, inner ℝ (rieszKernelGrad d s (Y a - Y i)) e =
      -∑ a ∈ Finset.univ.erase i, inner ℝ (rieszKernelGrad d s (Y i - Y a)) e := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    exact hc i a (Finset.ne_of_mem_erase ha).symm
  rw [h2]
  simp only [s113x_inner_single, he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hN : (N : ℝ) ≠ 0 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; exact (Fin.elim0 i)
    · exact_mod_cast h.ne'
  field_simp
  ring

end Energy


section Density

/-- Drift coordinate `b_{ik}(Y) = q Y_{ik} + N⁻¹ ∑_{j≠i} (∇g)_k(Y_i - Y_j)` (the one of `movFP`). -/
def s113x_drift (d : ℕ) (s q : ℝ) (N : ℕ) (i : Fin N) (k : Fin d) (Y : EucConfig d N) : ℝ :=
  q * Y i k + (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Y i - Y j) k

/-- `Ψ_{ik}(Y) = β (u_k(Y_i) - b_{ik}(Y))`, the logarithmic derivative `∂_{ik} log q_N`. -/
def s113x_Psi (d : ℕ) (s q β : ℝ) (N : ℕ) (u : Euc d → Euc d) (i : Fin N) (k : Fin d)
    (Y : EucConfig d N) : ℝ :=
  β * (u (Y i) k - s113x_drift d s q N i k Y)

theorem s113x_Q_line {s q β : ℝ} (hβ : β ≠ 0) {f : Euc d → ℝ} (hf : ∀ x, DifferentiableAt ℝ f x)
    (hpos : ∀ x, 0 < f x)
    (hΓ : ∀ x, HasFDerivAt (HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal f))
      (innerSL ℝ (movForce d s f x)) x)
    {Y : EucConfig d N} (hY : Y ∉ eucCollisionSet d N) (i : Fin N) (k : Fin d) :
    HasDerivAt (fun τ => movQDensity d s β N f (s113x_line Y i k τ))
      (movQDensity d s β N f Y * s113x_Psi d s q β N (movU d s q β f) i k Y) 0 := by
  have hN : (N : ℝ) ≠ 0 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; exact (Fin.elim0 i)
    · exact_mod_cast h.ne'
  set e : Euc d := EuclideanSpace.single k (1 : ℝ) with he
  set K : ℝ := HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal f) with hK
  set Fm' : ℝ := (1 / (N : ℝ) ^ 2) * ∑ j ∈ Finset.univ.erase i, (rieszKernelGrad d s (Y i - Y j)) k -
        (1 / (N : ℝ)) * (movForce d s f (Y i)) k with hFm'
  have hFm := s113x_Fm_line hΓ hY i k
  have hE : HasDerivAt (fun τ => Real.exp (-β * N * rieszModulatedEnergy d s (s113x_line Y i k τ)
      (HRS.Whole.withDensityReal f)))
      (Real.exp (-β * N * rieszModulatedEnergy d s Y (HRS.Whole.withDensityReal f)) * (-β * N * Fm')) 0 := by
    have h := (hFm.const_mul (-β * N)).exp
    simp only [s113x_line_zero] at h
    exact h
  set P : ℝ := ∏ a ∈ Finset.univ.erase i, f (Y a) with hP
  have hprod : ∀ τ : ℝ, ∏ a, f (s113x_line Y i k τ a) = f (Y i + τ • e) * P := by
    intro τ
    rw [← Finset.mul_prod_erase Finset.univ (fun a => f (s113x_line Y i k τ a)) (Finset.mem_univ i)]
    rw [s113x_line_apply_same]
    congr 1
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [s113x_line_apply_ne Y i k (Finset.ne_of_mem_erase ha)]
  have hB : HasDerivAt (fun τ : ℝ => f (Y i + τ • e) * P) (fderiv ℝ f (Y i) e * P) 0 := by
    have := s113x_hasDerivAt_line_comp (w := e) (hf (Y i)).hasFDerivAt
    simpa using this.mul_const P
  have hcomb := (hE.mul hB).const_mul K⁻¹
  have hfun : (fun τ => movQDensity d s β N f (s113x_line Y i k τ)) = fun τ =>
      K⁻¹ * (Real.exp (-β * N * rieszModulatedEnergy d s (s113x_line Y i k τ) (HRS.Whole.withDensityReal f)) *
        (f (Y i + τ • e) * P)) := by
    funext τ
    unfold movQDensity
    rw [hprod τ, mul_assoc]
  rw [hfun]
  convert hcomb using 1
  -- value
  have hpos0 := hpos (Y i)
  have hfk : fderiv ℝ f (Y i) e = f (Y i) * (gradient (fun z => Real.log (f z)) (Y i)) k := by
    have h1 := s113x_grad_eq_mul_log (hf (Y i)) hpos0
    have h2 := congrArg (fun v : Euc d => v k) h1
    simp only [PiLp.smul_apply, smul_eq_mul] at h2
    rw [he, ← movtr_gradient_apply, h2]
  have hu : (movU d s q β f (Y i)) k = β⁻¹ * (gradient (fun z => Real.log (f z)) (Y i)) k + q * Y i k +
      (movForce d s f (Y i)) k := by
    unfold movU
    simp [PiLp.add_apply, PiLp.smul_apply]
  unfold s113x_Psi s113x_drift
  rw [hu]
  unfold movQDensity
  simp only [s113x_line_zero, zero_smul, add_zero, hprod 0]
  rw [hfk]
  have hfi : f (Y i) ≠ 0 := hpos0.ne'
  rw [← hK]
  have e1 : ∏ a, f (Y a) = f (Y i) * P := by
    rw [← Finset.mul_prod_erase Finset.univ (fun a => f (Y a)) (Finset.mem_univ i)]
  rw [e1]
  rw [hFm']
  field_simp
  ring

end Density

end HRS.MS.S113BD

end
