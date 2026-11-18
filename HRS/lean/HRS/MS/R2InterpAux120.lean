import HRS.MS.R2InterpAux119
import HRS.MS.R2PolyAux2

/-!
# S10.2 (worker S10S), part 120 (packet M1a): algebra of the commutator kernels of weighted tests

For `f ∈ C^r` the pair kernel `h_f = commutatorKernel (∇f)` is additive and homogeneous in `f`, measurable, symmetric and dominated by
`c₁ ‖f‖_{E_{r,P}} g_P` with the polynomial envelope `g_P(x,y) = (⟨x⟩+⟨y⟩)^P (1 + W_s(x-y))` (valid also on the diagonal, where `h_f = 0`).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

theorem s102_gradient_add {f g : Euc d → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Euc d) :
    gradient (f + g) x = gradient f x + gradient g x := by
  apply (InnerProductSpace.toDual ℝ (Euc d)).injective
  rw [toDual_gradient, map_add, toDual_gradient, toDual_gradient]
  exact fderiv_add (hf x) (hg x)

theorem s102_gradient_smul (c : ℝ) {f : Euc d → ℝ} (hf : Differentiable ℝ f) (x : Euc d) :
    gradient (c • f) x = c • gradient f x := by
  apply (InnerProductSpace.toDual ℝ (Euc d)).injective
  rw [toDual_gradient, map_smul, toDual_gradient]
  exact fderiv_const_smul (hf x) c

theorem s102_gradient_continuous {f : Euc d → ℝ} {r : ℕ} (hf : ContDiff ℝ r f) (hr : 1 ≤ r) :
    Continuous (gradient f) := by
  have h : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by exact_mod_cast (by omega : r ≠ 0))
  have e : gradient f = fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ f x) := rfl
  rw [e]
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp h

theorem s102_comm_add {f g : Euc d → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (s : ℝ) (x y : Euc d) :
    commutatorKernel d s (fun z => gradient (f + g) z) x y =
      commutatorKernel d s (fun z => gradient f z) x y + commutatorKernel d s (fun z => gradient g z) x y := by
  unfold commutatorKernel
  beta_reduce
  rw [s102_gradient_add hf hg, s102_gradient_add hf hg]
  have : gradient f x + gradient g x - (gradient f y + gradient g y) =
      (gradient f x - gradient f y) + (gradient g x - gradient g y) := by abel
  rw [this, inner_add_left]

theorem s102_comm_smul (c : ℝ) {f : Euc d → ℝ} (hf : Differentiable ℝ f) (s : ℝ) (x y : Euc d) :
    commutatorKernel d s (fun z => gradient (c • f) z) x y =
      c * commutatorKernel d s (fun z => gradient f z) x y := by
  unfold commutatorKernel
  beta_reduce
  rw [s102_gradient_smul c hf, s102_gradient_smul c hf]
  have : c • gradient f x - c • gradient f y = c • (gradient f x - gradient f y) := by rw [smul_sub]
  rw [this, real_inner_smul_left]

/-- The polynomial envelope `g_P(x,y) = (⟨x⟩+⟨y⟩)^P (1 + W_s(x-y))`. -/
def s102_gk (s Pw : ℝ) (x y : Euc d) : ℝ := (jbracket x + jbracket y) ^ Pw * (1 + rieszWeight s (x - y))

theorem s102_gk_nonneg (s Pw : ℝ) (x y : Euc d) : 0 ≤ s102_gk s Pw x y := by
  unfold s102_gk
  have hjx : 0 ≤ jbracket x := by unfold jbracket; positivity
  have hjy : 0 ≤ jbracket y := by unfold jbracket; positivity
  have := HRS.MS.Wr.wr3_rieszWeight_nonneg (d := d) s (x - y)
  positivity

theorem s102_gk_meas (s Pw : ℝ) : Measurable fun p : Euc d × Euc d => s102_gk s Pw p.1 p.2 := by
  unfold s102_gk
  exact (((HRS.MS.R2Poly.s95_jb_meas.comp measurable_fst).add (HRS.MS.R2Poly.s95_jb_meas.comp measurable_snd)).pow_const
    Pw).mul (measurable_const.add ((HRS.MS.Wr.wr3_measurable_rieszWeight s).comp (measurable_fst.sub measurable_snd)))

theorem s102_gk_symm (s Pw : ℝ) (x y : Euc d) : s102_gk s Pw x y = s102_gk s Pw y x := by
  unfold s102_gk rieszWeight
  rw [add_comm (jbracket x), norm_sub_rev]

theorem s102_gk_poly (s Pw : ℝ) : IsR2PolyPairKernel s Pw 1 (s102_gk (d := d) s Pw) :=
  ⟨s102_gk_meas s Pw, s102_gk_symm s Pw, fun x y _ => by
    rw [abs_of_nonneg (s102_gk_nonneg s Pw x y)]
    unfold s102_gk
    rw [one_mul]⟩

theorem s102_comm_poly (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {Pw : ℝ} (hP0 : 0 ≤ Pw) (r : ℕ)
    (hr : (d : ℝ) / 2 + 2 < r) :
    ∃ c1 : ℝ, 0 ≤ c1 ∧ ∀ f : Euc d → ℝ, ContDiff ℝ r f → weightedSobolevE r Pw f < ⊤ →
      IsR2PolyPairKernel s Pw (c1 * (weightedSobolevE r Pw f).toReal) (commutatorKernel d s (fun z => gradient f z)) ∧
      ∀ x y, |commutatorKernel d s (fun z => gradient f z) x y| ≤
        (c1 * (weightedSobolevE r Pw f).toReal) * s102_gk s Pw x y := by
  obtain ⟨c1, hc1, hbd⟩ := s102_comm_envelope hd hs0 hP0 r hr
  refine ⟨c1, hc1, fun f hf hE => ?_⟩
  have hr1 : 1 ≤ r := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have h2 : (2 : ℝ) < r := by linarith
    have h3 : 2 < r := by exact_mod_cast h2
    omega
  have hB : 0 ≤ c1 * (weightedSobolevE r Pw f).toReal := mul_nonneg hc1 ENNReal.toReal_nonneg
  have hpoly : IsR2PolyPairKernel s Pw (c1 * (weightedSobolevE r Pw f).toReal)
      (commutatorKernel d s (fun z => gradient f z)) :=
    ⟨HRS.MS.Comm.comm_meas _ (s102_gradient_continuous hf hr1).measurable, HRS.MS.Comm.comm_symm _,
      fun x y hxy => hbd f hf hE x y hxy⟩
  refine ⟨hpoly, fun x y => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    unfold commutatorKernel
    simp only [sub_self, inner_zero_left, abs_zero]
    exact mul_nonneg hB (s102_gk_nonneg s Pw x x)
  · have := hpoly.bound x y hxy
    unfold s102_gk
    linarith [mul_assoc (c1 * (weightedSobolevE r Pw f).toReal) ((jbracket x + jbracket y) ^ Pw)
      (1 + rieszWeight s (x - y))]

end HRS.MS.R2Interp

end
