import HRS.Sections.IIDAux5

/-!
# IID helper chain, part 6: the i.i.d. comparison for a finite mode set (see the chain plan in
`IIDAux1`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Convolution

namespace HRS.IID

section IidT

open HRS.InitialDataAux
open scoped Matrix

variable {d : ℕ}

/-- The Gaussian marginal on the modes of `T`. -/
lemma gauss_law_coordVec {m : ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {γ : Measure (NegSobolev d m)} [IsProbabilityMeasure γ]
    (hγ : IsCenteredGaussianWithCov m γ (iidCov μ)) (T : Finset (NonzeroLattice d)) {N : ℕ}
    (hN : 1 ≤ N) :
    γ.map (coordVec T) = multivariateGaussian (0 : EuclideanSpace ℝ (Fin T.card))
      (∑ _i : Fin N, Yurinskii.momentMatrix (μ.map (xiVec μ N (blk m T)))) := by
  have := negSobolev_secondCountable d m
  have hfc : ∀ a, Continuous (blk m T a) := fun a => continuous_scMode m _
  have hξc := continuous_xiVec μ N (blk m T) hfc
  have hξm : Measurable (xiVec μ N (blk m T)) := hξc.measurable
  set ρ0 := μ.map (xiVec μ N (blk m T)) with hρ0
  set S : ℝ := ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m)) with hS
  have hb : ∀ x, ‖xiVec μ N (blk m T) x‖ ^ 2 ≤ 8 * S / N := fun x => norm_xiBlk_sq_le hN T x S le_rfl
  have h2 : Integrable (fun y : EuclideanSpace ℝ (Fin T.card) => ‖y‖ ^ 2) ρ0 := by
    rw [hρ0, integrable_map_measure (by fun_prop) hξc.aemeasurable]
    refine Integrable.of_bound ((by fun_prop : Continuous fun x => ‖xiVec μ N (blk m T) x‖ ^ 2).aestronglyMeasurable)
      (8 * S / N) (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖xiVec μ N (blk m T) x‖ ^ 2)]
    exact hb x
  have hMpsd : (∑ _i : Fin N, Yurinskii.momentMatrix ρ0).PosSemidef :=
    Matrix.posSemidef_sum _ fun _ _ => Yurinskii.momentMatrix_posSemidef _ h2
  have hcov : ∀ a b, ∫ F, NegSobolev.eval F (blk m T a) * NegSobolev.eval F (blk m T b) ∂γ =
      (∑ _i : Fin N, Yurinskii.momentMatrix ρ0) a b := by
    intro a b
    rw [hγ.2 (blk m T a) (blk m T b) (isSmooth_scMode m (kOf T a)) (isSmooth_scMode m (kOf T b))]
    simp only [Matrix.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : Yurinskii.momentMatrix ρ0 a b = ∫ x, xiVec μ N (blk m T) x a * xiVec μ N (blk m T) x b ∂μ := by
      simp only [Yurinskii.momentMatrix, Matrix.of_apply, hρ0]
      rw [integral_map hξm.aemeasurable (by fun_prop)]
    rw [h1, integral_xiVec_mul hN (blk m T) hfc a b]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    field_simp
  have hlaw := gauss_law_of_cov m hγ.1 (blk m T) (fun a => memSobolev_scMode m m _) _ hMpsd hcov
  have hT'eq : (fun F : NegSobolev d m => (WithLp.toLp 2 fun a => NegSobolev.eval F (blk m T a) :
      EuclideanSpace ℝ (Fin T.card))) = coordVec T := by
    funext F; ext j; simp [coordVec, blk, eval_scMode]
  rw [hT'eq] at hlaw
  exact hlaw

/-- Setup shared by the `d₂` and `W₁` estimates. -/
lemma iid_setup {m : ℝ} {c : ℝ} (hc : 0 < c) {q : Torus d → ℝ} (hq : IsProbDensity q)
    (hqc : ∀ x, c ≤ q x) (T : Finset (NonzeroLattice d)) {N : ℕ} (hN : 1 ≤ N) :
    ∃ B binv : EuclideanSpace ℝ (Fin T.card) →L[ℝ] EuclideanSpace ℝ (Fin T.card),
      (∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) ∧ (∀ y, B (binv y) = y) ∧
      (∀ y, binv (B y) = y) ∧
      MomMatch B (N : ℝ)⁻¹ ((withDensityReal q).map (xiVec (withDensityReal q) N (blk m T))) ∧
      nuS B 1 = multivariateGaussian (0 : EuclideanSpace ℝ (Fin T.card))
        (∑ _i : Fin N, Yurinskii.momentMatrix
          ((withDensityReal q).map (xiVec (withDensityReal q) N (blk m T)))) ∧
      (∀ᵐ y ∂((withDensityReal q).map (xiVec (withDensityReal q) N (blk m T))),
        ‖y‖ ≤ Real.sqrt (8 * (∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m))) / N)) := by
  set μ := withDensityReal q with hμ
  haveI : IsProbabilityMeasure μ := isProb_withDensityReal hq
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hfc : ∀ a, Continuous (blk m T a) := fun a => continuous_scMode m _
  have hξc := continuous_xiVec μ N (blk m T) hfc
  have hξm : Measurable (xiVec μ N (blk m T)) := hξc.measurable
  set ρ0 := μ.map (xiVec μ N (blk m T)) with hρ0
  set S : ℝ := ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m)) with hS
  have hb : ∀ x, ‖xiVec μ N (blk m T) x‖ ^ 2 ≤ 8 * S / N := fun x => norm_xiBlk_sq_le hN T x S le_rfl
  have hb' : ∀ x, ‖xiVec μ N (blk m T) x‖ ≤ Real.sqrt (8 * S / N) := fun x =>
    Real.le_sqrt_of_sq_le (hb x)
  have h2 : Integrable (fun y : EuclideanSpace ℝ (Fin T.card) => ‖y‖ ^ 2) ρ0 := by
    rw [hρ0, integrable_map_measure (by fun_prop) hξc.aemeasurable]
    refine Integrable.of_bound ((by fun_prop : Continuous fun x => ‖xiVec μ N (blk m T) x‖ ^ 2).aestronglyMeasurable)
      (8 * S / N) (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖xiVec μ N (blk m T) x‖ ^ 2)]
    exact hb x
  have hSpd : (∑ _i : Fin N, Yurinskii.momentMatrix ρ0).PosSemidef :=
    Matrix.posSemidef_sum _ fun _ _ => Yurinskii.momentMatrix_posSemidef _ h2
  have hpos : ∀ w : EuclideanSpace ℝ (Fin T.card), w ≠ 0 →
      0 < w.ofLp ⬝ᵥ (∑ _i : Fin N, Yurinskii.momentMatrix ρ0) *ᵥ w.ofLp := fun w hw =>
    Sigma_quad_pos hq hc hqc T hN hw
  obtain ⟨B, binv, hBs, hBb, hbB, hBB, hnu⟩ := exists_whiten _ hSpd hpos
  refine ⟨B, binv, hBs, hBb, hbB, ?_, hnu, ?_⟩
  · refine momMatch_of_matrix h2 (fun c => ?_) hN hBB
    rw [hρ0, integral_map hξm.aemeasurable (by fun_prop)]
    exact integral_xiVec_coord N (blk m T) hfc c
  · rw [hρ0, ae_map_iff hξm.aemeasurable (measurableSet_le (by fun_prop) (by fun_prop))]
    exact Filter.Eventually.of_forall hb'

theorem iid_T_d2 {m : ℝ} (hm : (d : ℝ) < 2 * m) {c : ℝ} (hc : 0 < c) {ρ : Torus d → ℝ}
    (hρ : IsProbDensity ρ) (hρc : ∀ x, c ≤ ρ x) {γ : Measure (NegSobolev d m)}
    [IsProbabilityMeasure γ] (hγ : IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)))
    (T : Finset (NonzeroLattice d)) {N : ℕ} (hN : 1 ≤ N) :
    smoothDist 2 ((Measure.pi fun _ : Fin N => withDensityReal ρ).map (fld m N (withDensityReal ρ))) γ ≤
      8 * (∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m))) / N *
        (2 * Real.sqrt T.card * Real.sqrt N + 1) + 2 * Real.sqrt (tailR d m T) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  obtain ⟨B, binv, hBs, hBb, hbB, hMM, hnu, hbd⟩ := iid_setup (m := m) hc hρ hρc T hN
  set S : ℝ := ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m)) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (Torus.jp_pos _).le _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine fm_d2 hm hγ T hN (nuS B 1) (by rw [hnu]; exact gauss_law_coordVec hγ T hN) ?_
  intro Φ' hcd h0 h1 h2
  have := fd_C2 hBs hBb hbB hN hMM (Real.sqrt_nonneg _) hbd hcd h0 h1 h2
  rwa [Real.sq_sqrt (by positivity), one_mul] at this

theorem iid_T_coupling {m : ℝ} (hm : (d : ℝ) < 2 * m) {c : ℝ} (hc : 0 < c) {ρ : Torus d → ℝ}
    (hρ : IsProbDensity ρ) (hρc : ∀ x, c ≤ ρ x) {γ : Measure (NegSobolev d m)}
    [IsProbabilityMeasure γ] (hγ : IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)))
    (T : Finset (NonzeroLattice d)) {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η) :
    ∃ P : Measure (Config d N × NegSobolev d m), IsProbabilityMeasure P ∧
      P.map Prod.fst = Measure.pi (fun _ : Fin N => withDensityReal ρ) ∧ P.map Prod.snd = γ ∧
      ∫⁻ ω, ‖fld m N (withDensityReal ρ) ω.1 - ω.2‖ₑ ∂P ≤
        ENNReal.ofReal (Real.sqrt (8 * (∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m))) / N) *
          (T.card * Real.log (Real.exp 1 * N) + 2) + η + 2 * Real.sqrt (tailR d m T)) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  obtain ⟨B, binv, hBs, hBb, hbB, hMM, hnu, hbd⟩ := iid_setup (m := m) hc hρ hρc T hN
  set S : ℝ := ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m)) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (Torus.jp_pos _).le _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hw := w1_cpow_nuS hBs hBb hbB hN hMM (Real.sqrt_nonneg _) hbd
  have hlog : 0 ≤ Real.log (Real.exp 1 * N) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hNpos.ne', Real.log_exp]
    have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    linarith
  have hJ0 : 0 ≤ Real.sqrt (8 * S / N) * (T.card * Real.log (Real.exp 1 * N) + 2) := by positivity
  exact fm_coupling hm hγ T hN (nuS B 1) (by rw [hnu]; exact gauss_law_coordVec hγ T hN) hJ0 hw hη

end IidT

end HRS.IID

namespace HRS.IID

section Fourth

open HRS.HilbertCLTAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {α : Type*} [MeasurableSpace α]

/-- Fourth moment of a sum of independent centred bounded vectors (product measure). -/
theorem fourth_moment_pi (μ : Measure α) [IsProbabilityMeasure μ] (y : α → H) (hy : Measurable y)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ‖y x‖ ≤ B) (hy0 : ∫ x, y x ∂μ = 0) (N : ℕ) :
    ∫ X, ‖∑ i : Fin N, y (X i)‖ ^ 4 ∂(Measure.pi fun _ : Fin N => μ) ≤
      N * B ^ 4 + 3 * N * (N - 1) * (B ^ 2) ^ 2 := by
  set P : Measure (Fin N → α) := Measure.pi fun _ : Fin N => μ with hP
  set Yf : Fin N → (Fin N → α) → H := fun i X => y (X i) with hYf
  have hYm : ∀ i : Fin N, Measurable (Yf i) := fun i => hy.comp (measurable_pi_apply i)
  have hind : iIndepFun Yf P :=
    iIndepFun_pi (X := fun _ : Fin N => y) (μ := fun _ => μ) (fun i => hy.aemeasurable)
  have hmp : ∀ i : Fin N, MeasurePreserving (fun X : Fin N → α => X i) P μ := fun i =>
    measurePreserving_eval (fun _ : Fin N => μ) i
  have hmean : ∀ i : Fin N, ∫ X, Yf i X ∂P = 0 := fun i => by
    have := integral_map (μ := P) (φ := fun X : Fin N → α => X i) (hmp i).measurable.aemeasurable
      (f := y) hy.aestronglyMeasurable
    rw [(hmp i).map_eq] at this
    simp only [hYf]; rw [← this]; exact hy0
  have hint : ∀ (f : α → ℝ), Measurable f → ∀ i : Fin N, ∫ X, f (X i) ∂P = ∫ x, f x ∂μ := fun f hf i => by
    have := integral_map (μ := P) (φ := fun X : Fin N → α => X i) (hmp i).measurable.aemeasurable
      (f := f) hf.aestronglyMeasurable
    rw [(hmp i).map_eq] at this
    exact this.symm
  set m2 : ℝ := ∫ x, ‖y x‖ ^ 2 ∂μ with hm2
  set m4 : ℝ := ∫ x, ‖y x‖ ^ 4 ∂μ with hm4
  have hm2b : m2 ≤ B ^ 2 := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => ‖y x‖ ^ 2) (C := B ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hB x) 2)
    simpa using (le_abs_self _).trans (by simpa using this)
  have hm4b : m4 ≤ B ^ 4 := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => ‖y x‖ ^ 4) (C := B ^ 4)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hB x) 4)
    simpa using (le_abs_self _).trans (by simpa using this)
  have hm20 : 0 ≤ m2 := integral_nonneg fun x => by positivity
  have hY4 : ∀ i : Fin N, MemLp (Yf i) 4 P := fun i =>
    MemLp.of_bound (hYm i).aestronglyMeasurable B (Filter.Eventually.of_forall fun X => hB _)
  have hS4 : ∀ s : Finset (Fin N), MemLp (∑ i ∈ s, Yf i) 4 P := fun s =>
    memLp_finsetSum' s fun i _ => hY4 i
  have hS0 : ∀ s : Finset (Fin N), ∫ X, (∑ i ∈ s, Yf i) X ∂P = 0 := fun s => by
    have e : ∀ X, (∑ i ∈ s, Yf i) X = ∑ i ∈ s, Yf i X := fun X => Finset.sum_apply _ _ _
    simp_rw [e]
    rw [integral_finsetSum s fun i _ => (hY4 i).integrable (by norm_num)]
    exact Finset.sum_eq_zero fun i _ => hmean i
  have hclaim : ∀ s : Finset (Fin N), ∫ X, ‖(∑ i ∈ s, Yf i) X‖ ^ 2 ∂P = s.card * m2 ∧
      ∫ X, ‖(∑ i ∈ s, Yf i) X‖ ^ 4 ∂P ≤ s.card * m4 + 3 * s.card * (s.card - 1) * m2 ^ 2 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      have hs : (∑ i ∈ insert j s, Yf i) = (∑ i ∈ s, Yf i) + Yf j := by
        rw [Finset.sum_insert hj, add_comm]
      have hind' : IndepFun (∑ i ∈ s, Yf i) (Yf j) P :=
        hind.indepFun_finsetSum_of_notMem₀ (fun i => (hYm i).aemeasurable) hj
      have hy2 : ∫ X, ‖Yf j X‖ ^ 2 ∂P = m2 := hint (fun x => ‖y x‖ ^ 2) (by fun_prop) j
      have hy4 : ∫ X, ‖Yf j X‖ ^ 4 ∂P = m4 := hint (fun x => ‖y x‖ ^ 4) (by fun_prop) j
      have h2 := integral_sq_add hind' (hS4 s) (hY4 j) (hmean j)
      have h4 := integral_fourth_add_le hind' (hS4 s) (hY4 j) (hS0 s) (hmean j)
      rw [hs]
      simp only [Pi.add_apply]
      rw [Finset.card_insert_of_notMem hj]
      push_cast
      refine ⟨?_, ?_⟩
      · beta_reduce at h2
        rw [h2, ih.1, hy2]; ring
      · beta_reduce at h4
        refine h4.trans ?_
        rw [hy2, hy4, ih.1]
        have := ih.2
        nlinarith [this]
  have := (hclaim Finset.univ).2
  simp only [Finset.card_univ, Fintype.card_fin] at this
  have e : ∀ X, (∑ i ∈ (Finset.univ : Finset (Fin N)), Yf i) X = ∑ i : Fin N, y (X i) := fun X => by
    simp [Finset.sum_apply, hYf]
  simp_rw [e] at this
  refine this.trans ?_
  have hN0 : (0 : ℝ) ≤ N * (N - 1) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have : (1 : ℝ) ≤ N := by exact_mod_cast h
      nlinarith
  have h3 : 3 * (N : ℝ) * (N - 1) * m2 ^ 2 ≤ 3 * (N : ℝ) * (N - 1) * (B ^ 2) ^ 2 := by
    have : m2 ^ 2 ≤ (B ^ 2) ^ 2 := pow_le_pow_left₀ hm20 hm2b 2
    have h30 : 0 ≤ 3 * (N : ℝ) * (N - 1) := by nlinarith
    exact mul_le_mul_of_nonneg_left this h30
  have h1 : (N : ℝ) * m4 ≤ N * B ^ 4 := mul_le_mul_of_nonneg_left hm4b (Nat.cast_nonneg N)
  linarith

end Fourth

end HRS.IID
