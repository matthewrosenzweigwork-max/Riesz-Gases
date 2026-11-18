import HRS.MS.MfeConfAux58

/-!
# S.B.1, packet F6 (part 21): the entropy inequality along the tilted reference (density level)

`sb1_level_ineq`: for the flow `μ_s` of `dY = b(Y) ds + √(2θ) dW` (`P4MolData` for the static Hamiltonian `H`, `∇H = -b`) and the
reference `Q_s = exp(-(H + Ψ_s)/θ) dx` (mass one), `∇Ψ_s = w_s`, with the source
`S = -div w - ⟨w,b⟩/θ + |w|²/θ + ∂_sΨ/θ`:
`H(μ_t | Q_t) ≤ H(μ_0 | Q_0) + ∫_0^t ∫ S_s dμ_s ds`,
the transplant of `p4_mollified_ineq` + `p4_initial_jensen` + `p4_mollify_lsc` with a signed time derivative of the reference
(Fisher information dropped).
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {θ T : ℝ} {b w : ℝ → EucConfig d N → EucConfig d N} {H : EucConfig d N → ℝ}
  {Ψ Wψ : ℝ → EucConfig d N → ℝ} {CΨ Bw Kw CS : ℝ → ℝ}
  {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B K M CV : ℝ}

theorem sb1_level_ineq (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hΨ : Sb1Tilt θ T b w Ψ Wψ CΨ Bw Kw CS) (hθ : 0 < θ) {DS : ℝ → ℝ} (hDS0 : ∀ s, 0 ≤ DS s)
    (hDSi : IntegrableOn DS (Set.Icc 0 T))
    (hSlip : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x y : EucConfig d N,
      |sb1S θ b w Wψ s x - sb1S θ b w Wψ s y| ≤ DS s * ‖x - y‖ * (1 + ‖x‖ + ‖y‖))
    (hZ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Real.exp (-θ⁻¹ * (H x + Ψ s x))) = 1)
    {Lw : ℝ≥0} (hLw : LipschitzWith Lw (w 0)) {C0 : ℝ} (hC0 : ∀ x, 0 ≤ H x + Ψ 0 x + C0)
    (hfin0 : klDiv (μ 0) (sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + Ψ 0 x)))) ≠ ⊤)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    klDiv (μ t) (sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + Ψ t x)))) ≠ ⊤ ∧
      (klDiv (μ t) (sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + Ψ t x))))).toReal ≤
        (klDiv (μ 0) (sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + Ψ 0 x))))).toReal +
          ∫ s in Set.Icc (0 : ℝ) t, ∫ y, sb1S θ b w Wψ s y ∂(μ s) := by
  have hT0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hCV := sb1_CV_nonneg hP
  have hM0 := sb1_M_nonneg hP
  haveI := hP.prob 0
  haveI := hP.prob t
  set wn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hwn
  have hwn_pos : ∀ n, 0 < wn n := fun n => by simp only [hwn]; positivity
  have hwn0 : Tendsto wn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- the initial Jensen bound
  have hH : ∀ x, HasFDerivAt H (-(p4InnerL (b 0 x))) x := fun x => hP.grad 0 x
  have hU0 : ∀ x, HasFDerivAt (fun x => H x + Ψ 0 x) (-(p4InnerL ((b 0 - w 0) x))) x := by
    intro x
    have h := (hH x).add (hΨ.Ψgrad 0 x)
    simp only [Pi.sub_apply, sb1_innerL_sub]
    convert h using 1
    abel
  have hb0 : LipschitzWith (Kl + Lw) (b 0 - w 0) := (hP.bl 0).sub hLw
  obtain ⟨e, he, hJ⟩ := sb1_init_jensen hθ hU0 hb0 (C0 := C0) hC0 (hZ 0 hT0) (hP.hm 0) hfin0
  have he' : Tendsto (fun n => e (wn n)) atTop (𝓝 0) :=
    he.comp (tendsto_nhdsWithin_iff.2 ⟨hwn0, Filter.Eventually.of_forall fun n => hwn_pos n⟩)
  -- the source limit
  obtain ⟨hsrc, hGint⟩ := sb1_src_limit hP hΨ hDS0 hDSi hSlip ht hwn_pos hwn0
  -- the mollified inequality and the identification of the free energies
  set c0 : ℕ → ℝ := fun n => t * (N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * wn n) / (4 * θ)) with hc0
  have hc0t : Tendsto c0 atTop (𝓝 0) := by
    have h := (hwn0.const_mul (((N * d : ℕ) : ℝ))).const_mul ((N : ℝ) * (Kl : ℝ) ^ 2)
    have h2 := (h.div_const (4 * θ)).const_mul t
    simp only [mul_zero, zero_div] at h2
    exact h2
  have hQ : ∀ s ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + Ψ s x)))) :=
    fun s hs => sb1Dm_prob (hZ s hs)
  have hfreeT : ∀ n, klDiv (sb1Dm (p4Mol (wn n) (μ t)))
      (sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + Ψ t x)))) ≠ ⊤ ∧
      (klDiv (sb1Dm (p4Mol (wn n) (μ t))) (sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + Ψ t x))))).toReal =
        ∫ x, (p4Mol (wn n) (μ t) x * Real.log (p4Mol (wn n) (μ t) x) +
          p4Mol (wn n) (μ t) x * (H x + Ψ t x) / θ) := by
    intro n
    have hΨt := (hΨ.nn t).1
    have hUc : Continuous (fun x => H x + Ψ t x) :=
      (hP.Vc.comp (Continuous.prodMk (continuous_const (y := t)) continuous_id)).add
        (hΨ.Ψc.comp (Continuous.prodMk (continuous_const (y := t)) continuous_id))
    exact sb1_free_klDiv (hwn_pos n) hθ (hP.hm t) (hP.hM t) hM0 (by linarith : 0 ≤ CV + CΨ t) hUc
      (fun x => sb1_V_bound hP hΨ t x) (hZ t ht)
  have hfree0 : ∀ n, (klDiv (sb1Dm (p4Mol (wn n) (μ 0)))
      (sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + Ψ 0 x))))).toReal =
        ∫ x, (p4Mol (wn n) (μ 0) x * Real.log (p4Mol (wn n) (μ 0) x) +
          p4Mol (wn n) (μ 0) x * (H x + Ψ 0 x) / θ) := by
    intro n
    have hΨt := (hΨ.nn 0).1
    have hUc : Continuous (fun x => H x + Ψ 0 x) :=
      (hP.Vc.comp (Continuous.prodMk (continuous_const (y := (0 : ℝ))) continuous_id)).add
        (hΨ.Ψc.comp (Continuous.prodMk (continuous_const (y := (0 : ℝ))) continuous_id))
    exact (sb1_free_klDiv (hwn_pos n) hθ (hP.hm 0) (hP.hM 0) hM0 (by linarith : 0 ≤ CV + CΨ 0) hUc
      (fun x => sb1_V_bound hP hΨ 0 x) (hZ 0 hT0)).2
  have hmol : ∀ n, (klDiv (sb1Dm (p4Mol (wn n) (μ t)))
      (sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + Ψ t x))))).toReal ≤
      ((klDiv (μ 0) (sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + Ψ 0 x))))).toReal + e (wn n)) +
        (∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4Mol (wn n) (μ s) x * sb1S θ b w Wψ s x) + c0 n := by
    intro n
    rw [(hfreeT n).2]
    have h1 := sb1_mol_ineq hP hΨ (hwn_pos n) hθ ht
    have h2 := hJ (wn n) (hwn_pos n)
    simp only [p4m_Phi] at h1
    simp only [hc0]
    linarith
  -- the limit of the right-hand side
  set R : ℝ := (klDiv (μ 0) (sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + Ψ 0 x))))).toReal +
    ∫ s in Set.Icc (0 : ℝ) t, ∫ y, sb1S θ b w Wψ s y ∂(μ s) with hR
  have hRlim : Tendsto (fun n => ((klDiv (μ 0) (sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + Ψ 0 x))))).toReal +
      e (wn n)) + (∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4Mol (wn n) (μ s) x * sb1S θ b w Wψ s x) + c0 n) atTop
      (𝓝 R) := by
    have h := (((tendsto_const_nhds (x := (klDiv (μ 0) (sb1Dm (fun x =>
      Real.exp (-θ⁻¹ * (H x + Ψ 0 x))))).toReal)).add he').add hsrc).add hc0t
    simp only [add_zero] at h
    exact h
  have hRnn : 0 ≤ R := by
    refine ge_of_tendsto hRlim (Filter.Eventually.of_forall fun n => ?_)
    exact (ENNReal.toReal_nonneg).trans (hmol n)
  -- lower semicontinuity
  haveI := hQ t ht
  have hlsc := sb1_lsc_mol (ν := μ t) (Q := sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + Ψ t x)))) hwn_pos hwn0
  have hle : klDiv (μ t) (sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + Ψ t x)))) ≤ ENNReal.ofReal R := by
    refine hlsc.trans ?_
    have h3 := (ENNReal.tendsto_ofReal hRlim).liminf_eq
    rw [← h3]
    refine liminf_le_liminf (Filter.Eventually.of_forall fun n => ?_)
    rw [← ENNReal.ofReal_toReal (hfreeT n).1]
    exact ENNReal.ofReal_le_ofReal (hmol n)
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle, ?_⟩
  exact ENNReal.toReal_le_of_le_ofReal hRnn hle

end

end HRS.MS.MfeConf
