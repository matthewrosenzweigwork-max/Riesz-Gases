import HRS.MS.R26T8AL3c

/-!
# S8.2 observed-time layer, generic lemma L3d (part of L3): weak-derivative chains of `c · v`

For `c` smooth with bounded derivatives and `v` `SobSmooth`, the directional iterates `w_j = (∂_i)^[j] (c v)`
form a weak-derivative chain (WD), bounded, and in `L²`.  Used with Q09A `memSobolev_of_chains`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.Whole.Q09A LineDeriv

variable {d : ℕ}

/-- integration by parts with a bound on the directional derivative only (copy of L1a) -/
theorem r26t8a_l3d_ibp (u : Euc d → ℝ) (v : Euc d) (hu : ContDiff ℝ ∞ u) (C0 C1 : ℝ)
    (hC0 : ∀ x, |u x| ≤ C0) (hC1 : ∀ x, |fderiv ℝ u x v| ≤ C1)
    (ψ : SchwartzMap (Euc d) ℂ) :
    ∫ x, ((fderiv ℝ u x v : ℝ) : ℂ) * ψ x =
      -∫ x, ((u x : ℝ) : ℂ) * (LineDeriv.lineDerivOp v ψ) x := by
  have hd : ∀ x, DifferentiableAt ℝ u x := fun x => (hu.differentiable (by simp)) x
  set f : Euc d → ℂ := fun x => ((u x : ℝ) : ℂ) with hf
  have hfdiff : ∀ x, DifferentiableAt ℝ f x := fun x =>
    (Complex.ofRealCLM.differentiableAt).comp x (hd x)
  have hfd : ∀ x, fderiv ℝ f x v = ((fderiv ℝ u x v : ℝ) : ℂ) := fun x =>
    r26t8a_l1a_fderiv_ofReal u x (hd x) v
  have hbf : ∀ x, ‖f x‖ ≤ C0 := fun x => by
    simp only [hf, Complex.norm_real, Real.norm_eq_abs]
    exact hC0 x
  have hbd : ∀ x, ‖((fderiv ℝ u x v : ℝ) : ℂ)‖ ≤ C1 := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hC1 x
  have hcont : Continuous f := Complex.continuous_ofReal.comp hu.continuous
  have hcontd : Continuous (fun x => ((fderiv ℝ u x v : ℝ) : ℂ)) := by
    have : Continuous (fun x => fderiv ℝ u x v) :=
      (hu.continuous_fderiv (by simp)).clm_apply continuous_const
    exact Complex.continuous_ofReal.comp this
  have hψi : Integrable (fun x => ψ x) volume := ψ.integrable
  have hψdi : Integrable (fun x => (LineDeriv.lineDerivOp v ψ) x) volume :=
    (LineDeriv.lineDerivOp v ψ).integrable
  have I1 : Integrable (fun x => ((fderiv ℝ u x v : ℝ) : ℂ) * ψ x) volume :=
    hψi.bdd_mul (hcontd.aestronglyMeasurable) (Eventually.of_forall fun x => hbd x)
  have I2 : Integrable (fun x => f x * (LineDeriv.lineDerivOp v ψ) x) volume :=
    hψdi.bdd_mul hcont.aestronglyMeasurable (Eventually.of_forall fun x => hbf x)
  have I3 : Integrable (fun x => f x * ψ x) volume :=
    hψi.bdd_mul hcont.aestronglyMeasurable (Eventually.of_forall fun x => hbf x)
  have I4 : Integrable (fun x => fderiv ℝ f x v * ψ x) volume := by
    simp only [hfd]
    exact I1
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := f)
    (g := ψ) (v := v) I4 I2 I3 (fun x _ => hfdiff x) (fun x _ => ψ.differentiableAt)
  have hdef : (∫ x, ((u x : ℝ) : ℂ) * (LineDeriv.lineDerivOp v ψ) x) =
      ∫ x, f x * fderiv ℝ ψ x v := rfl
  rw [hdef, key, neg_neg]
  simp only [hfd]

/-- Sobolev norm of order zero is the `L²` norm (squared). -/
theorem r26t8a_l3d_sob0 (g : Euc d → ℝ) (hg : MemLp g 2 volume) :
    sobolevNormSq 0 g = ∫ x, g x ^ 2 := by
  unfold sobolevNormSq
  simp only [Real.rpow_zero, one_mul]
  exact (integral_sq_eq_norm_sq hg).symm

theorem r26t8a_l3d_sq_mono {s t : ℝ} (h : s ≤ t) (u : Euc d → ℝ)
    (hu : HRS.PDE.ToolboxRd.MemSobolev t u) : sobolevNormSq s u ≤ sobolevNormSq t u := by
  unfold sobolevNormSq
  refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => ?_) hu.2
    (Eventually.of_forall fun ξ => ?_)
  · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
  · have hw : (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ t :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (Real.pi), sq_nonneg ‖ξ‖]) h
    exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)

theorem r26t8a_l3d_bdd_iter (i : Fin d) (v : Euc d → ℝ) (hv : r26t8a_SobSmooth v) (l : ℕ) :
    ∃ B : ℝ, ∀ x, |(r26t8a_l3_D i)^[l] v x| ≤ B := by
  obtain ⟨C, hC, hb⟩ := HRS.MP.RdGen.rg_sobolev_embedding (d := d) 0
    (q := ((d + 2 : ℕ) : ℝ)) (by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  refine ⟨C * HRS.Whole.sobolevNorm ((d + 2 : ℕ) : ℝ) ((r26t8a_l3_D i)^[l] v), fun x => ?_⟩
  have h := hb _ (r26t8a_l3_contDiff_iter i v hv.1 l)
    ((r26t8a_l3_sob_iter v hv i l).2 (d + 2)) x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  exact h

theorem r26t8a_l3d_memLp_iter (i : Fin d) (c v : Euc d → ℝ) (hc : ContDiff ℝ ∞ c)
    (hv : r26t8a_SobSmooth v) (hcb : ∀ n : ℕ, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ n c x‖ ≤ B) (j : ℕ) :
    MemLp ((r26t8a_l3_D i)^[j] (fun x => c x * v x)) 2 volume := by
  choose Bc hBc using hcb
  rw [r26t8a_l3_leibniz i c v hc hv.1 j]
  refine memLp_finsetSum (Finset.range (j + 1)) (fun k _ => ?_)
  have hbnd : ∀ x, ‖(r26t8a_l3_D i)^[k] c x‖ ≤ Bc k := fun x => by
    rw [Real.norm_eq_abs]
    exact (r26t8a_l3_iter_bound i c hc k x).trans (hBc k x)
  have hmeas : AEStronglyMeasurable ((r26t8a_l3_D i)^[k] c) volume :=
    (r26t8a_l3_contDiff_iter i c hc k).continuous.aestronglyMeasurable
  have hinf : MemLp ((r26t8a_l3_D i)^[k] c) ⊤ volume :=
    memLp_top_of_bound hmeas (Bc k) (Eventually.of_forall hbnd)
  have hL2 : MemLp (fun x => (r26t8a_l3_D i)^[j - k] v x) 2 volume :=
    (r26t8a_l3_sob_iter v hv i (j - k)).2 0 |>.1
  have hprod : MemLp (fun x => (r26t8a_l3_D i)^[k] c x * (r26t8a_l3_D i)^[j - k] v x) 2 volume :=
    hinf.mul hL2
  exact hprod.const_mul _

end HRS.MS.R26T8A

end
