import HRS.MS.UniqT2
import HRS.MS.UniqT3

/-!
# N3a, part A: the Fourier bridge on Schwartz functions, for an arbitrary direction `q`

For the constant `c` of `kg_fourier_h_proof`, real Schwartz `u v` and any `q : Euc d`,
`symbolForm (c (2π ⟨ξ,q⟩)² ‖ξ‖^{s-d}) u v = - ∫ u (g * D_q² v)`, `D_q w = fderiv w · q`.
This is `UniqT2.t2_bridge` with the coordinate direction `e_l` replaced by `q`; the pointwise Riesz
Fourier formula is obtained for `D_q φ = Σ q_i D_i φ` from the coordinate version by linearity.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate SchwartzMap LineDeriv

namespace HRS.MS.UniqN3a
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UniqT2

variable {d : ℕ}

/-- `D_q v` as a real Schwartz function. -/
def dq (q : Euc d) (v : SchwartzMap (Euc d) ℝ) : SchwartzMap (Euc d) ℝ :=
  SchwartzMap.evalCLM ℝ (Euc d) ℝ q (SchwartzMap.fderivCLM ℝ (Euc d) ℝ v)

lemma dq_apply (q : Euc d) (v : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    dq q v x = fderiv ℝ v x q := rfl

lemma fourier_dq (q : Euc d) (v : SchwartzMap (Euc d) ℝ) (ξ : Euc d) :
    𝓕 (fun x : Euc d => ((dq q v x : ℝ) : ℂ)) ξ =
      (2 * Real.pi * Complex.I * ((inner ℝ ξ q : ℝ) : ℂ)) *
        𝓕 (fun x : Euc d => ((v x : ℝ) : ℂ)) ξ := by
  set V : SchwartzMap (Euc d) ℂ := v.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM with hV
  have h1 := SchwartzMap.fourier_lineDerivOp_eq V q
  have h2 : ⇑(∂_{q} V : SchwartzMap (Euc d) ℂ) = fun x : Euc d => ((dq q v x : ℝ) : ℂ) := by
    ext x
    show fderiv ℝ (⇑V) x _ = _
    have : ⇑V = fun x => ((v x : ℝ) : ℂ) := rfl
    rw [this, dq_apply]
    have hd : DifferentiableAt ℝ (⇑v) x := v.differentiableAt
    rw [show (fun x => ((v x : ℝ) : ℂ)) = Complex.ofRealCLM ∘ ⇑v from rfl,
      (Complex.ofRealCLM.hasFDerivAt.comp x hd.hasFDerivAt).fderiv]
    rfl
  have h3 : ⇑V = fun x => ((v x : ℝ) : ℂ) := rfl
  have hg : (fun x : Euc d => inner ℝ x q).HasTemperateGrowth :=
    ((innerSL ℝ).flip q).hasTemperateGrowth
  have e : 𝓕 (fun x : Euc d => ((dq q v x : ℝ) : ℂ)) ξ =
      (𝓕 (∂_{q} V : SchwartzMap (Euc d) ℂ)) ξ := by
    rw [SchwartzMap.fourier_coe, h2]
  rw [e, h1]
  simp only [smul_apply, smul_eq_mul]
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.fourier_coe, h3]
  simp
  ring

/-- Integrability of `t ↦ g(y-t) φ(t)` for a Schwartz function `φ`. -/
lemma conv_int_schwartz {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (φ : SchwartzMap (Euc d) ℝ)
    (y : Euc d) : Integrable (fun t : Euc d => rieszKernel d s (y - t) * φ t) := by
  obtain ⟨G0, hG0i, hG0n, hgG⟩ := HRS.MS.UniqT3.g_dom (d := d) hs0 hsd
  have hφ : Integrable (fun t : Euc d => φ t) volume := φ.integrable
  have hφ1 : Integrable (fun t : Euc d => ‖t‖ * φ t) volume := by
    have h := φ.integrable_pow_mul volume 1
    refine h.mono ((continuous_norm.mul φ.continuous).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    simp [norm_mul]
  obtain ⟨M, hM⟩ : ∃ M, ∀ t, |φ t| ≤ M := by
    obtain ⟨M, hM⟩ := φ.toBoundedContinuousFunction.isBounded_range.exists_norm_le
    exact ⟨M, fun t => by simpa using hM _ ⟨t, rfl⟩⟩
  have hb1 : Integrable (fun t : Euc d => G0 (y - t) * |φ t|) volume := by
    have := (hG0i.comp_sub_left y).mul_bdd (c := M) (g := fun t => |φ t|)
      (φ.continuous.abs.aestronglyMeasurable) (Eventually.of_forall fun t => by
        simpa [Real.norm_eq_abs] using hM t)
    exact this
  have hb : Integrable (fun t : Euc d =>
      G0 (y - t) * |φ t| + ‖y‖ * |φ t| + |‖t‖ * φ t|) volume :=
    (hb1.add (hφ.abs.const_mul ‖y‖)).add hφ1.abs
  refine hb.mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (((HRS.MS.UniqT3.g_meas s).comp (measurable_const.sub measurable_id)).mul
      φ.continuous.measurable).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    have h1 : ‖y - t‖ ≤ ‖y‖ + ‖t‖ := norm_sub_le _ _
    have h2 := hgG (y - t)
    have h3 : |rieszKernel d s (y - t)| ≤ G0 (y - t) + ‖y‖ + ‖t‖ := by linarith
    have h4 := abs_nonneg (φ t)
    calc |rieszKernel d s (y - t)| * |φ t| ≤ (G0 (y - t) + ‖y‖ + ‖t‖) * |φ t| :=
          mul_le_mul_of_nonneg_right h3 h4
      _ = G0 (y - t) * |φ t| + ‖y‖ * |φ t| + |‖t‖ * φ t| := by
          rw [abs_mul, abs_of_nonneg (norm_nonneg t)]; ring

/-- Direction-`q` version of `kg_fourier_h_proof`. -/
theorem kgq_fourier (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : Euc d) (φ : SchwartzMap (Euc d) ℝ) (y : Euc d),
      Integrable (fun ξ : Euc d => ((c * (2 * Real.pi * inner ℝ ξ q) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) *
        Complex.I * 𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ) ∧
      ((HRS.Whole.convFun (rieszKernel d s) (fun x => fderiv ℝ φ x q) y : ℝ) : ℂ) =
        ∫ ξ : Euc d, ((c * (2 * Real.pi * inner ℝ ξ q) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Complex.I *
          𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ *
          Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)) := by
  obtain ⟨c, hc, h⟩ := HRS.MH.Screened.kg_fourier_h_proof hd hs0 hsd
  refine ⟨c, hc, fun q φ y => ?_⟩
  set Hi : Fin d → Euc d → ℂ := fun i ξ => ((c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) *
    Complex.I * 𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ with hHi
  have hqs : ∀ ξ : Euc d, inner ℝ ξ q = ∑ i, q i * ξ i := by
    intro ξ
    simp [PiLp.inner_apply, mul_comm]
  have hsum : ∀ ξ : Euc d, ((c * (2 * Real.pi * inner ℝ ξ q) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) *
        Complex.I * 𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ =
      ∑ i, ((q i : ℝ) : ℂ) * Hi i ξ := by
    intro ξ
    rw [hqs]
    simp only [hHi, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  have hint : ∀ i, Integrable (Hi i) := fun i => (h i φ 0).1
  have hexp : ∀ i, Integrable (fun ξ => Hi i ξ *
      Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ))) := by
    intro i
    refine (hint i).bdd_mul (f := fun ξ : Euc d =>
      Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ))) (c := 1) ?_ ?_ |>.congr ?_
    · exact (by fun_prop : Continuous fun ξ : Euc d =>
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ))).aestronglyMeasurable
    · refine Eventually.of_forall fun ξ => ?_
      rw [show (2 * Real.pi * Complex.I * ((inner ℝ y ξ : ℝ) : ℂ)) =
        (((2 * Real.pi * (inner ℝ y ξ : ℝ) : ℝ)) : ℂ) * Complex.I by push_cast; ring]
      exact (Complex.norm_exp_ofReal_mul_I _).le
    · exact Eventually.of_forall fun ξ => mul_comm _ _
  constructor
  · simp_rw [hsum]
    exact integrable_finsetSum _ fun i _ => (hint i).const_mul _
  · simp_rw [hsum, Finset.sum_mul]
    rw [integral_finsetSum _ fun i _ => ((hexp i).const_mul ((q i : ℝ) : ℂ)).congr
      (Eventually.of_forall fun ξ => by simp only [mul_assoc])]
    -- the left side
    have hq : ∀ x, fderiv ℝ φ x q = ∑ i, q i * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      intro x
      conv_lhs => rw [show q = ∑ i, q i • (EuclideanSpace.single i (1 : ℝ) : Euc d) by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]
      simp [map_sum, smul_eq_mul]
    have hconv : HRS.Whole.convFun (rieszKernel d s) (fun x => fderiv ℝ φ x q) y =
        ∑ i, q i * HRS.Whole.convFun (rieszKernel d s)
          (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y := by
      unfold HRS.Whole.convFun
      simp_rw [hq, Finset.mul_sum]
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp only; ring
      · intro i _
        have := (conv_int_schwartz hs0 hsd (dl i φ) y).const_mul (q i)
        refine this.congr (Eventually.of_forall fun t => ?_)
        simp only [dl_apply]; ring
    rw [hconv]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(h i φ y).2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hHi]; ring

/-- **N3a, Schwartz level.**  For the constant of `kgq_fourier`, all `q` and real Schwartz `u v`,
`symbolForm (c (2π ⟨ξ,q⟩)² ‖ξ‖^{s-d}) u v = - ∫ u (g * D_q² v)`. -/
theorem n3a_schwartz (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : Euc d) (u v : SchwartzMap (Euc d) ℝ),
      symbolForm (fun ξ : Euc d => c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d)) u v =
        - ∫ x, u x * HRS.Whole.convFun (rieszKernel d s)
            (fun y => fderiv ℝ (fun z => fderiv ℝ v z q) y q) x := by
  obtain ⟨c, hc, h⟩ := kgq_fourier hd hs0 hsd
  refine ⟨c, hc, fun q u v => ?_⟩
  set φ : SchwartzMap (Euc d) ℝ := dq q v with hφ
  set Hf : Euc d → ℂ := fun ξ => ((c * (2 * Real.pi * inner ℝ ξ q) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) *
    Complex.I * 𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ with hHf
  have hHint : Integrable Hf := (h q φ 0).1
  have hw : ∀ y, ((HRS.Whole.convFun (rieszKernel d s)
      (fun y => fderiv ℝ (fun z => fderiv ℝ v z q) y q) y : ℝ) : ℂ) =
      ∫ ξ : Euc d, Hf ξ * Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)) :=
    fun y => (h q φ y).2
  set I0 : ℝ := ∫ x, u x * HRS.Whole.convFun (rieszKernel d s)
            (fun y => fderiv ℝ (fun z => fderiv ℝ v z q) y q) x with hI0
  have e1 : (I0 : ℂ) = ∫ ξ, Hf ξ * conj (𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ)) ξ) := by
    rw [hI0, ← integral_complex_ofReal, ← fubini_step u hHint]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [Complex.ofReal_mul, hw y]
  set m : Euc d → ℝ := fun ξ => c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d) with hm
  set T : ℂ := ∫ ξ, ((m ξ : ℝ) : ℂ) * (𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ)) ξ *
    conj (𝓕 (fun x : Euc d => ((v x : ℝ) : ℂ)) ξ)) with hT
  have e2 : (I0 : ℂ) = - conj T := by
    rw [e1, hT, ← integral_conj, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hHf, hφ, fourier_dq, hm, map_mul, Complex.conj_ofReal]
    push_cast
    simp only [Complex.conj_conj]
    ring_nf
    simp [Complex.I_sq]
  have e3 : symbolForm m u v = T.re := by
    unfold symbolForm
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [fourierL2_schwartz u, fourierL2_schwartz v] with ξ hu hv
    rw [hu, hv]
  rw [e3]
  have := congrArg Complex.re e2
  simp at this
  linarith

end HRS.MS.UniqN3a
