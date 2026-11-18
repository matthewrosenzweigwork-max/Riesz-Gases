import HRS.MS.R2IidAux1

/-!
# Uniform iid initial corrections over an arbitrary observation family

Compiler-first continuation of the generic part of the PR #53 candidate
`ProClosureS21IidUniform.lean`. The two generic proofs below retain the
candidate's proof bodies. A common summable coordinate envelope supplies
one particle threshold for every member of the family and the full Cb5 ball.

This module proves an initial-law ingredient. It does not prove the original
moving-window S2.1(iii) theorem, a positive-coupling initial expansion, or a
physical dynamic identification. The pending physical-feature theorem in
PR #53 is not included or asserted here.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.ProClosureS21IidFamily

open HRS HRS.Whole HRS.StaticLimitAux

section UniformHilbert

variable {d : ℕ} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {ι : Type*}

/-- A summable coordinate envelope gives one tail cutoff for the entire
observation family.  The quantifier order is essential for shifted windows. -/
theorem iid_family_projection_tails
    (e : HilbertBasis ℕ ℝ H) (Y : ι → Euc d → H)
    (w : ℕ → ℝ) (hw : Summable w)
    (hYw : ∀ a n x, (inner ℝ (e n) (Y a x)) ^ 2 ≤ w n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ a x,
      ∑' n : {n : ℕ // n₀ ≤ n}, (inner ℝ (e n) (Y a x)) ^ 2 ≤ ε := by
  have ht := (tendsto_tsum_compl_atTop_zero w).comp tendsto_finset_range
  obtain ⟨n₀, hn₀⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨n₀, fun a x => ?_⟩
  have he : ∀ f : ℕ → ℝ,
      ∑' n : {n : ℕ // n₀ ≤ n}, f n.1 =
        ∑' n : {n : ℕ // n ∉ Finset.range n₀}, f n.1 :=
    fun f => (Equiv.tsum_eq
      (Equiv.subtypeEquivRight (fun n => by simp)) (fun b => f b.1)).symm
  rw [he (fun n => (inner ℝ (e n) (Y a x)) ^ 2)]
  refine le_trans ?_ hn₀.le
  refine Summable.tsum_le_tsum (fun n => hYw a n.1 x) ?_ (hw.subtype _)
  exact (Summable.of_nonneg_of_le (fun n => sq_nonneg _)
    (fun n => hYw a n x) hw).subtype _

/-- The actual iid expansion, uniform over the entire initial-observation
family and the original `C_b^5` ball. -/
theorem iid_family_Cb5
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (e : HilbertBasis ℕ ℝ H) (Y : ι → Euc d → H)
    (hYc : ∀ a, Continuous (Y a)) (C : ℝ)
    (hC : ∀ a x, ‖Y a x‖ ≤ C)
    (hcent : ∀ a, ∫ x, Y a x ∂μ = 0)
    (w : ℕ → ℝ) (hw : Summable w)
    (hYw : ∀ a n x, (inner ℝ (e n) (Y a x)) ^ 2 ≤ w n)
    (G : ι → Measure H) [∀ a, IsProbabilityMeasure (G a)]
    (hGg : ∀ a, IsCenteredGaussian (G a))
    (hcov : ∀ a x y, covarianceBilin (G a) x y =
      covarianceBilin (μ.map (Y a)) x y) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ a,
      ∀ Φ ∈ CbUnitBall H 5,
      |Real.sqrt N *
        (∫ z, Φ (Ssum (Y a) N z) ∂(Measure.pi fun _ : Fin N => μ) -
          ∫ F, Φ F ∂(G a)) -
        (1 / 6) * ∫ F, ∫ x,
          iteratedFDeriv ℝ 3 Φ F ![Y a x, Y a x, Y a x] ∂μ ∂(G a)| ≤ ε := by
  intro ε hε
  have hYm : ∀ a, Measurable (Y a) := fun a => (hYc a).measurable
  have hX0m : ∀ a, Measurable
      (fun ω : (ℕ → Euc d) × H => Y a (ω.1 0)) :=
    fun a => (hYm a).comp ((measurable_pi_apply 0).comp measurable_fst)
  have hcent' : ∀ a,
      ∫ ω, Y a ((ω : (ℕ → Euc d) × H).1 0) ∂(s11iid_P μ (G a)) = 0 := by
    intro a
    have hh := integral_map (μ := s11iid_P μ (G a)) measurable_fst.aemeasurable
      (measurable_Xi (hYm a) 0).aestronglyMeasurable
    rw [s11iid_map_fst] at hh
    show ∫ ω, Xi (Y a) 0 ω.1 ∂(s11iid_P μ (G a)) = 0
    rw [← hh]
    have hi := integral_map (μ := Pinf μ)
      (measurable_pi_apply (0 : ℕ)).aemeasurable (hYm a).aestronglyMeasurable
    rw [Measure.infinitePi_map_eval (μ := fun _ : ℕ => μ) 0] at hi
    show ∫ ω, Y a (ω 0) ∂(Pinf μ) = 0
    rw [← hi]
    exact hcent a
  have hint4 : ∀ a, Integrable
      (fun ω : (ℕ → Euc d) × H => ‖Y a (ω.1 0)‖ ^ 4) (s11iid_P μ (G a)) := by
    intro a
    refine Integrable.of_bound ((hX0m a).norm.pow_const 4).aestronglyMeasurable
      (C ^ 4) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC a _) 4
  have h4 : ∀ a,
      ∫ ω, ‖Y a ((ω : (ℕ → Euc d) × H).1 0)‖ ^ 4 ∂(s11iid_P μ (G a)) ≤ C ^ 4 := by
    intro a
    calc _ ≤ ∫ _ω, C ^ 4 ∂(s11iid_P μ (G a)) :=
        integral_mono (hint4 a) (integrable_const _)
          (fun ω => pow_le_pow_left₀ (norm_nonneg _) (hC a _) 4)
      _ = C ^ 4 := by simp
  have htail : ∀ ε' > 0, ∃ n₀ : ℕ, ∀ a,
      ∫ ω, ∑' n : {n : ℕ // n₀ ≤ n},
        (inner ℝ (e n) (Y a ((ω : (ℕ → Euc d) × H).1 0))) ^ 2
          ∂(s11iid_P μ (G a)) ≤ ε' := by
    intro ε' hε'
    obtain ⟨n₀, hn₀⟩ := iid_family_projection_tails e Y w hw hYw hε'
    refine ⟨n₀, fun a => ?_⟩
    calc _ ≤ ∫ _ω, ε' ∂(s11iid_P μ (G a)) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω => tsum_nonneg fun n => sq_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall fun ω => hn₀ a _)
      _ = ε' := by simp
  have hGrv : ∀ a, IsCenteredGaussianRV (s11iid_P μ (G a))
      (fun ω : (ℕ → Euc d) × H => ω.2)
      (fun x y => covarianceBilin
        (HRS.law (s11iid_P μ (G a))
          (fun ω : (ℕ → Euc d) × H => Y a (ω.1 0))) x y) := by
    intro a
    have hlaw : HRS.law (s11iid_P μ (G a))
        (fun ω : (ℕ → Euc d) × H => ω.2) = G a := by
      unfold HRS.law
      exact s11iid_map_snd μ (G a)
    refine ⟨measurable_snd.aemeasurable, ?_, fun x y => ?_⟩
    · rw [hlaw]
      exact hGg a
    · rw [hlaw, s11iid_law_X μ (G a) (hYm a) 0]
      exact hcov a x y
  obtain ⟨N₀, hN₀⟩ := hilbert_edgeworth_C4 e (ι := ι)
    (Ω := fun _ => (ℕ → Euc d) × H) (fun a => s11iid_P μ (G a))
    (fun a ω => Y a (ω.1 0)) (fun a => (hX0m a).aemeasurable)
    hcent' (C ^ 4) hint4 h4 htail (fun _ ω => ω.2) hGrv ε hε
  refine ⟨N₀, fun N hN hN1 a Φ hΦ => ?_⟩
  have hΦ4 : Φ ∈ CbUnitBall H 4 := cbUnitBall_anti (by norm_num) hΦ
  have hΦ3 : Φ ∈ CbUnitBall H 3 := cbUnitBall_anti (by norm_num) hΦ
  have hΦc : Continuous Φ := hΦ4.1.continuous
  have hiid : IsIIDCopies (s11iid_P μ (G a))
      (fun (i : Fin N) (ω : (ℕ → Euc d) × H) => Y a (ω.1 i)) := by
    obtain ⟨h1, -⟩ := s11iid_iid μ (G a) (hYm a)
    exact ⟨h1.precomp Fin.val_injective, fun i j => by
      rw [s11iid_law_X μ (G a) (hYm a), s11iid_law_X μ (G a) (hYm a)]⟩
  have h := hN₀ N hN a (fun i ω => Y a (ω.1 i))
    (fun i => ((hYm a).comp
      ((measurable_pi_apply (i : ℕ)).comp measurable_fst)).aemeasurable)
    hiid (fun i => by
      rw [s11iid_law_X μ (G a) (hYm a), s11iid_law_X μ (G a) (hYm a)]) Φ hΦ4
  rw [s11iid_integral_sum μ (G a) (hYm a) Φ hΦc N,
    s11iid_integral_snd μ (G a) Φ hΦc,
    s11iid_third μ (G a) (hYc a) (hC a) hΦ3] at h
  have hNpos : (0 : ℝ) < Real.sqrt N :=
    Real.sqrt_pos.mpr (by exact_mod_cast hN1)
  exact s11iid_alg _ _ _ _ _ hNpos h

end UniformHilbert

section CommonError

variable {d : ℕ} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {ι : Type*}

/-- One nonnegative error sequence is chosen before the observation-family
parameter and before every test in the entire Cb5 unit ball. -/
theorem iid_family_Cb5_error_sequence
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (e : HilbertBasis ℕ ℝ H) (Y : ι → Euc d → H)
    (hYc : ∀ a, Continuous (Y a)) (C : ℝ)
    (hC : ∀ a x, ‖Y a x‖ ≤ C)
    (hcent : ∀ a, ∫ x, Y a x ∂μ = 0)
    (w : ℕ → ℝ) (hw : Summable w)
    (hYw : ∀ a n x, (inner ℝ (e n) (Y a x)) ^ 2 ≤ w n)
    (G : ι → Measure H) [∀ a, IsProbabilityMeasure (G a)]
    (hGg : ∀ a, IsCenteredGaussian (G a))
    (hcov : ∀ a x y, covarianceBilin (G a) x y =
      covarianceBilin (μ.map (Y a)) x y) :
    ∃ η : ℕ → ℝ, (∀ N, 0 ≤ η N) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ (N : ℕ) (a : ι), ∀ Φ ∈ CbUnitBall H 5,
        |Real.sqrt N *
          (∫ z, Φ (Ssum (Y a) N z) ∂(Measure.pi fun _ : Fin N => μ) -
            ∫ F, Φ F ∂(G a)) -
          (1 / 6) * ∫ F, ∫ x,
            iteratedFDeriv ℝ 3 Φ F ![Y a x, Y a x, Y a x] ∂μ ∂(G a)| ≤ η N := by
  classical
  let E : ℕ → ι → (H → ℝ) → ℝ := fun N a Φ =>
    |Real.sqrt N *
      (∫ z, Φ (Ssum (Y a) N z) ∂(Measure.pi fun _ : Fin N => μ) -
        ∫ F, Φ F ∂(G a)) -
      (1 / 6) * ∫ F, ∫ x,
        iteratedFDeriv ℝ 3 Φ F ![Y a x, Y a x, Y a x] ∂μ ∂(G a)|
  have hb : ∀ N a Φ, Φ ∈ CbUnitBall H 5 →
      E N a Φ ≤ 2 * Real.sqrt N + (1 / 6) * |C| ^ 3 := by
    intro N a Φ hΦ
    have hΦb : ∀ z, ‖Φ z‖ ≤ 1 := fun z => by
      simpa only [norm_iteratedFDeriv_zero] using
        iteratedFDeriv_norm_le_of_mem hΦ (show 0 ≤ 5 by omega) z
    have hI : |∫ z, Φ (Ssum (Y a) N z) ∂(Measure.pi fun _ : Fin N => μ)| ≤ 1 := by
      simpa [Real.norm_eq_abs, Measure.real] using
        norm_integral_le_of_norm_le_const
          (μ := Measure.pi fun _ : Fin N => μ)
          (Filter.Eventually.of_forall fun z => hΦb (Ssum (Y a) N z))
    have hG : |∫ F, Φ F ∂(G a)| ≤ 1 := by
      simpa [Real.norm_eq_abs, Measure.real] using
        norm_integral_le_of_norm_le_const (μ := G a)
          (Filter.Eventually.of_forall hΦb)
    have hT : ∀ F x,
        ‖iteratedFDeriv ℝ 3 Φ F ![Y a x, Y a x, Y a x]‖ ≤ |C| ^ 3 := by
      intro F x
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      have hD := iteratedFDeriv_norm_le_of_mem hΦ (show 3 ≤ 5 by omega) F
      have hY : ‖Y a x‖ ≤ |C| := (hC a x).trans (le_abs_self C)
      have hprod : (∏ i, ‖(![Y a x, Y a x, Y a x] : Fin 3 → H) i‖) ≤ |C| ^ 3 := by
        simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        calc ‖Y a x‖ * ‖Y a x‖ * ‖Y a x‖ ≤ |C| * |C| * |C| := by gcongr
          _ = |C| ^ 3 := by ring
      calc _ ≤ 1 * |C| ^ 3 :=
          mul_le_mul hD hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hTx : ∀ F,
        ‖∫ x, iteratedFDeriv ℝ 3 Φ F ![Y a x, Y a x, Y a x] ∂μ‖ ≤ |C| ^ 3 := by
      intro F
      simpa [Measure.real] using norm_integral_le_of_norm_le_const (μ := μ)
        (Filter.Eventually.of_forall (hT F))
    have hTT : |∫ F, ∫ x,
        iteratedFDeriv ℝ 3 Φ F ![Y a x, Y a x, Y a x] ∂μ ∂(G a)| ≤ |C| ^ 3 := by
      simpa [Real.norm_eq_abs, Measure.real] using
        norm_integral_le_of_norm_le_const (μ := G a)
          (Filter.Eventually.of_forall hTx)
    have hdiff : |Real.sqrt N *
        (∫ z, Φ (Ssum (Y a) N z) ∂(Measure.pi fun _ : Fin N => μ) -
          ∫ F, Φ F ∂(G a))| ≤ 2 * Real.sqrt N := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc _ ≤ Real.sqrt N *
            (|∫ z, Φ (Ssum (Y a) N z) ∂(Measure.pi fun _ : Fin N => μ)| +
              |∫ F, Φ F ∂(G a)|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt N * (1 + 1) :=
          mul_le_mul_of_nonneg_left (add_le_add hI hG) (Real.sqrt_nonneg _)
        _ = _ := by ring
    dsimp only [E]
    refine (abs_sub _ _).trans (add_le_add hdiff ?_)
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)]
    exact mul_le_mul_of_nonneg_left hTT (by norm_num)
  let S : ℕ → Set ℝ := fun N => {0} ∪
    Set.range (fun z : ι × {Φ : H → ℝ // Φ ∈ CbUnitBall H 5} => E N z.1 z.2.1)
  have hne : ∀ N, (S N).Nonempty := fun _ => ⟨0, Or.inl rfl⟩
  have hbd : ∀ N, BddAbove (S N) := by
    intro N
    refine ⟨2 * Real.sqrt N + (1 / 6) * |C| ^ 3, ?_⟩
    intro x hx
    rcases hx with hx | ⟨z, rfl⟩
    · rcases hx with rfl
      positivity
    · exact hb N z.1 z.2.1 z.2.2
  have hnonneg : ∀ N, 0 ≤ sSup (S N) :=
    fun N => le_csSup (hbd N) (Or.inl rfl)
  refine ⟨fun N => sSup (S N), hnonneg, ?_, ?_⟩
  · refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := iid_family_Cb5 μ e Y hYc C hC hcent w hw hYw G hGg hcov
      (ε / 2) (by linarith)
    refine ⟨max N₀ 1, fun N hN => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg N)]
    have hs : sSup (S N) ≤ ε / 2 := by
      refine csSup_le (hne N) ?_
      intro x hx
      rcases hx with hx | ⟨z, rfl⟩
      · rcases hx with rfl
        linarith
      · exact hN₀ N ((le_max_left _ _).trans hN) ((le_max_right _ _).trans hN)
          z.1 z.2.1 z.2.2
    linarith
  · intro N a Φ hΦ
    exact le_csSup (hbd N) (Or.inr ⟨⟨a, ⟨Φ, hΦ⟩⟩, rfl⟩)

/-- The same uniform expansion under the actual zero-preparation Gibbs law.
Its actual first marginal is exactly the initial reference measure. -/
theorem iid_family_gibbs_zero_Cb5_error_sequence
    (g : Euc d → ℝ) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (e : HilbertBasis ℕ ℝ H) (Y : ι → Euc d → H)
    (hYc : ∀ a, Continuous (Y a)) (C : ℝ)
    (hC : ∀ a x, ‖Y a x‖ ≤ C)
    (hcent : ∀ a, ∫ x, Y a x ∂μ = 0)
    (w : ℕ → ℝ) (hw : Summable w)
    (hYw : ∀ a n x, (inner ℝ (e n) (Y a x)) ^ 2 ≤ w n)
    (G : ι → Measure H) [∀ a, IsProbabilityMeasure (G a)]
    (hGg : ∀ a, IsCenteredGaussian (G a))
    (hcov : ∀ a x y, covarianceBilin (G a) x y =
      covarianceBilin (μ.map (Y a)) x y) :
    ∃ η : ℕ → ℝ, (∀ N, 0 ≤ η N) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ (N : ℕ), 1 ≤ N →
        HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs g N 0 μ) = μ ∧
        ∀ a, ∀ Φ ∈ CbUnitBall H 5,
          |Real.sqrt N *
            (∫ z, Φ (Ssum (Y a) N z) ∂(HRS.Whole.modulatedGibbs g N 0 μ) -
              ∫ F, Φ F ∂(G a)) -
            (1 / 6) * ∫ F, ∫ x,
              iteratedFDeriv ℝ 3 Φ F ![Y a x, Y a x, Y a x] ∂μ ∂(G a)| ≤ η N := by
  obtain ⟨η, hη0, hηlim, hη⟩ :=
    iid_family_Cb5_error_sequence μ e Y hYc C hC hcent w hw hYw G hGg hcov
  refine ⟨η, hη0, hηlim, fun N hN => ?_⟩
  rw [s11iid_gibbs_zero]
  refine ⟨?_, hη N⟩
  unfold HRS.Whole.firstMarginal
  rw [dif_pos (by omega : 0 < N)]
  simpa using Measure.pi_map_eval (μ := fun _ : Fin N => μ) (⟨0, by omega⟩ : Fin N)

/-- The initial Gaussian laws, projective cubic tensors, and one common error
sequence are all constructed from the bounded centered observation family.
There is no Gaussian-law, cubic-tensor, or expansion premise. -/
theorem iid_family_gibbs_zero_Cb5_producer
    (g : Euc d → ℝ) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (e : HilbertBasis ℕ ℝ H) (Y : ι → Euc d → H)
    (hYc : ∀ a, Continuous (Y a)) (C : ℝ)
    (hC : ∀ a x, ‖Y a x‖ ≤ C)
    (hcent : ∀ a, ∫ x, Y a x ∂μ = 0)
    (w : ℕ → ℝ) (hw : Summable w)
    (hYw : ∀ a n x, (inner ℝ (e n) (Y a x)) ^ 2 ≤ w n) :
    ∃ (G : ι → Measure H) (K : ι → projTensor H 3) (η : ℕ → ℝ),
      (∀ a, IsProbabilityMeasure (G a)) ∧
      (∀ a, IsCenteredGaussian (G a)) ∧
      (∀ a x y, covarianceBilin (G a) x y = covarianceBilin (μ.map (Y a)) x y) ∧
      (∀ a, ∀ T : H [×3]→L[ℝ] ℝ,
        (K a : TensorDual H 3) T = ∫ x, T ![Y a x, Y a x, Y a x] ∂μ) ∧
      (∀ N, 0 ≤ η N) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ (N : ℕ), 1 ≤ N →
        HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs g N 0 μ) = μ ∧
        ∀ a, ∀ Φ ∈ CbUnitBall H 5,
          |Real.sqrt N *
            (∫ z, Φ (Ssum (Y a) N z) ∂(HRS.Whole.modulatedGibbs g N 0 μ) -
              ∫ F, Φ F ∂(G a)) -
            (1 / 6) * ∫ F,
              (K a : TensorDual H 3) (iteratedFDeriv ℝ 3 Φ F) ∂(G a)| ≤ η N := by
  classical
  have hYL : ∀ a, MemLp (Y a) 2 μ := fun a =>
    MemLp.of_bound (hYc a).aestronglyMeasurable C (Filter.Eventually.of_forall (hC a))
  have hGauss : ∀ a, ∃ G : Measure H, IsProbabilityMeasure G ∧
      IsCenteredGaussian G ∧
      ∀ x y, covarianceBilin G x y = covarianceBilin (μ.map (Y a)) x y := by
    intro a
    obtain ⟨htc, -⟩ := HRS.isTraceClassCov_covarianceBilin μ (Y a) (hYL a) (hcent a)
    exact HRS.exists_centeredGaussian_of_traceClass _ htc
  choose G hGp hGg hGcov using hGauss
  letI : ∀ a, IsProbabilityMeasure (G a) := hGp
  have hYi : ∀ a, Integrable (fun x => ‖Y a x‖ * ‖Y a x‖ * ‖Y a x‖) μ := by
    intro a
    refine Integrable.of_bound (C := C * C * C) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (((hYc a).norm.mul (hYc a).norm).mul (hYc a).norm).aestronglyMeasurable
    · have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC a x)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hbound := hC a x
      gcongr
  let K : ι → projTensor H 3 := fun a =>
    ⟨HRS.MC.E213T.bochTensor3 μ (Y a) (Y a) (Y a),
      HRS.MC.E213T.bochTensor3_mem (hYc a).aestronglyMeasurable
        (hYc a).aestronglyMeasurable (hYc a).aestronglyMeasurable (hYi a)⟩
  have hK : ∀ a, ∀ T : H [×3]→L[ℝ] ℝ,
      (K a : TensorDual H 3) T = ∫ x, T ![Y a x, Y a x, Y a x] ∂μ := by
    intro a T
    exact HRS.MC.E213T.bochTensor3_apply (hYc a).aestronglyMeasurable
      (hYc a).aestronglyMeasurable (hYc a).aestronglyMeasurable (hYi a) T
  obtain ⟨η, hη0, hηlim, hη⟩ :=
    iid_family_gibbs_zero_Cb5_error_sequence g μ e Y hYc C hC hcent w hw hYw G hGg hGcov
  refine ⟨G, K, η, hGp, hGg, hGcov, hK, hη0, hηlim, fun N hN => ?_⟩
  obtain ⟨hmarg, herr⟩ := hη N hN
  refine ⟨hmarg, fun a Φ hΦ => ?_⟩
  simp_rw [hK]
  exact herr a Φ hΦ

end CommonError

end HRS.MS.ProClosureS21IidFamily

#print axioms HRS.MS.ProClosureS21IidFamily.iid_family_projection_tails
#print axioms HRS.MS.ProClosureS21IidFamily.iid_family_Cb5
#print axioms HRS.MS.ProClosureS21IidFamily.iid_family_Cb5_error_sequence
#print axioms HRS.MS.ProClosureS21IidFamily.iid_family_gibbs_zero_Cb5_error_sequence
#print axioms HRS.MS.ProClosureS21IidFamily.iid_family_gibbs_zero_Cb5_producer

