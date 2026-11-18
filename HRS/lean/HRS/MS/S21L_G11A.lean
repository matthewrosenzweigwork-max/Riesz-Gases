import HRS.MS.R2ChaosAux13
import HRS.MS.S21G2_K11bB
import HRS.MC.E213U13k

/-!
# S21L G11A -- the linear field `eta` of `r26t3_vector_wick` (R26-T3.G11, first step)

Bundles the hypotheses of G11 on the first-chaos field `eta` (`S21LEta`), derives the Gaussian laws from `InFirstChaos`
(`s21l_inQ1_of_first`), and proves the linear facts used by the Wick calculus: finite linear combinations, centring,
joint Gaussianity of `eta(f_i)` (`S94GFam`) and the covariance bound for the coordinates `z_i = eta(a_i)` of an
orthonormal system (`S94GSeq`).  Helper prefix `s21l_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS.MC.E213U13 HRS.MS.R2Chaos

variable {d : ℕ}

structure S21LEta {Ω : Type} [MeasurableSpace Ω] (μ : Measure (HRS.Euc d)) (P : Measure Ω)
    (η : (HRS.Euc d → ℝ) → Ω → ℝ) (Λ : ℝ) : Prop where
  memLp : ∀ f, MemLp f 2 μ → MemLp (η f) 2 P
  gauss : ∀ f, MemLp f 2 μ → ∃ v : ℝ≥0, P.map (η f) = gaussianReal 0 v
  lin : ∀ (f g : HRS.Euc d → ℝ) (c : ℝ), MemLp f 2 μ → MemLp g 2 μ →
    η (f + c • g) =ᵐ[P] η f + c • η g
  const : η (fun _ => 1) =ᵐ[P] 0
  cov : ∀ f, MemLp f 2 μ → ∫ ω, η f ω ^ 2 ∂P ≤ Λ * ∫ x, f x ^ 2 ∂μ

section FirstChaos

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

theorem s21l_coeFn_poly (hξ : HRS.IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i)) (N : ℕ) (c : ℕ → ℝ) :
    ((∑ i : Fin N, c i • g1 hξ hm i : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun ω => ∑ i : Fin N, c i * ξ i ω := by
  have key : ∀ s : Finset (Fin N), ((∑ i ∈ s, c i • g1 hξ hm i : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
      fun ω => ∑ i ∈ s, c i * ξ i ω := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω h
      simpa using h
    | insert j s hj ih =>
      filter_upwards [Lp.coeFn_add (c j • g1 hξ hm j) (∑ i ∈ s, c i • g1 hξ hm i),
        Lp.coeFn_smul (c j) (g1 hξ hm j), coe_g1 hξ hm j, ih] with ω h1 h2 h3 h4
      rw [Finset.sum_insert hj, h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Finset.sum_insert hj,
        smul_eq_mul]
  exact key Finset.univ

theorem s21l_inQ1_of_first (hξ : HRS.IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i)) {W : Ω → ℝ}
    (h : HRS.InFirstChaos P ξ 2 W) : InQ1 hξ hm W := by
  obtain ⟨hW, n, c, hlim⟩ := h
  have hpm : ∀ m, MemLp (fun ω => ∑ i ∈ Finset.range (n m), ξ i ω • c m i) 2 P := fun m =>
    memLp_finsetSum _ fun i _ => (memLp_xi hξ hm i).mul_const (c m i)
  have hsub : ∀ m, AEStronglyMeasurable (fun ω => (∑ i ∈ Finset.range (n m), ξ i ω • c m i) - W ω) P :=
    fun m => (hpm m).aestronglyMeasurable.sub hW
  have h2 := (tendsto_lintegral_iff_eLpNorm hsub (by norm_num : (0 : ℝ) < 2)).1 hlim
  simp only [ENNReal.ofReal_ofNat] at h2
  have hfin : ∀ᶠ m in atTop, eLpNorm (fun ω => (∑ i ∈ Finset.range (n m), ξ i ω • c m i) - W ω) 2 P < ∞ :=
    h2.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  obtain ⟨m0, hm0⟩ := hfin.exists
  have hW2 : MemLp W 2 P := by
    have h1 : MemLp (fun ω => (∑ i ∈ Finset.range (n m0), ξ i ω • c m0 i) - W ω) 2 P := hm0
    have := (hpm m0).sub h1
    refine this.ae_eq (Eventually.of_forall fun ω => ?_)
    simp
  refine ⟨hW2, ?_⟩
  rw [mem_Qc_iff (K1_mono hξ hm)]
  intro ε hε
  have hev : ∀ᶠ m in atTop, eLpNorm (fun ω => (∑ i ∈ Finset.range (n m), ξ i ω • c m i) - W ω) 2 P <
      ENNReal.ofReal ε := h2.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))
  obtain ⟨m, hm'⟩ := hev.exists
  refine ⟨n m, ∑ i : Fin (n m), c m i • g1 hξ hm i, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have hco := s21l_coeFn_poly hξ hm (n m) (c m)
    have e1 : eLpNorm (((∑ i : Fin (n m), c m i • g1 hξ hm i : Lp ℝ 2 P) : Ω → ℝ) - W) 2 P =
        eLpNorm (fun ω => (∑ i ∈ Finset.range (n m), ξ i ω • c m i) - W ω) 2 P := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [hco] with ω h
      simp only [Pi.sub_apply, h, Finset.sum_range, smul_eq_mul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have e2 := eLpNorm_sub_eq_dist (∑ i : Fin (n m), c m i • g1 hξ hm i : Lp ℝ 2 P) hW2
    rw [e1] at e2
    rw [e2] at hm'
    exact (ENNReal.ofReal_lt_ofReal_iff hε).1 hm'

end FirstChaos

section Eta

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
  {P : Measure Ω} [IsProbabilityMeasure P] {η : (HRS.Euc d → ℝ) → Ω → ℝ} {Λ : ℝ}

theorem s21l_eta_of_contract {ξ : ℕ → Ω → ℝ} (hξ : HRS.IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    (hη : ∀ f, MemLp f 2 μ → HRS.InFirstChaos P ξ 2 (η f))
    (hlin : ∀ (f g : HRS.Euc d → ℝ) (c : ℝ), MemLp f 2 μ → MemLp g 2 μ → η (f + c • g) =ᵐ[P] η f + c • η g)
    (hconst : η (fun _ => 1) =ᵐ[P] 0)
    (hcov : ∀ f, MemLp f 2 μ → ∫ ω, η f ω ^ 2 ∂P ≤ Λ * ∫ x, f x ^ 2 ∂μ) : S21LEta μ P η Λ :=
  ⟨fun f hf => by simpa using InQ1.memLp hξ hm (s21l_inQ1_of_first hξ hm (hη f hf)) 2,
   fun f hf => InQ1.exists_gaussian hξ hm (s21l_inQ1_of_first hξ hm (hη f hf)), hlin, hconst, hcov⟩

theorem s21l_eta_zero (h : S21LEta μ P η Λ) : η (fun _ => 0) =ᵐ[P] 0 := by
  have h0 : MemLp (fun _ : HRS.Euc d => (0 : ℝ)) 2 μ := MemLp.zero
  have := h.lin _ _ 1 h0 h0
  have e : ((fun _ : HRS.Euc d => (0 : ℝ)) + (1 : ℝ) • (fun _ : HRS.Euc d => (0 : ℝ))) = fun _ => 0 := by
    funext x; simp
  rw [e] at this
  filter_upwards [this] with ω hω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul] at hω
  simp only [Pi.zero_apply]; linarith

theorem s21l_eta_sum (h : S21LEta μ P η Λ) {ι : Type*} (s : Finset ι) (α : ι → ℝ)
    (f : ι → HRS.Euc d → ℝ) (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    η (fun x => ∑ i ∈ s, α i * f i x) =ᵐ[P] fun ω => ∑ i ∈ s, α i * η (f i) ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [s21l_eta_zero h] with ω hω
    simpa using hω
  | insert j s hj ih =>
    have hfs : ∀ i ∈ s, MemLp (f i) 2 μ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hL : MemLp (fun x => ∑ i ∈ s, α i * f i x) 2 μ :=
      memLp_finsetSum _ fun i hi => (hfs i hi).const_mul (α i)
    have hj' : MemLp (f j) 2 μ := hf j (Finset.mem_insert_self j s)
    have e : (fun x => ∑ i ∈ insert j s, α i * f i x) =
        (fun x => ∑ i ∈ s, α i * f i x) + (α j) • f j := by
      funext x
      simp only [Finset.sum_insert hj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have := h.lin _ _ (α j) hL hj'
    rw [e]
    filter_upwards [this, ih hfs] with ω h1 h2
    rw [h1]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h2, Finset.sum_insert hj]
    ring

theorem s21l_eta_center (h : S21LEta μ P η Λ) {f : HRS.Euc d → ℝ} (hf : MemLp f 2 μ) :
    η (fun x => f x - ∫ y, f y ∂μ) =ᵐ[P] η f := by
  have h1 : MemLp (fun _ : HRS.Euc d => (1 : ℝ)) 2 μ := memLp_const 1
  have := h.lin f _ (-(∫ y, f y ∂μ)) hf h1
  have e : f + (-(∫ y, f y ∂μ)) • (fun _ : HRS.Euc d => (1 : ℝ)) = fun x => f x - ∫ y, f y ∂μ := by
    funext x; simp [sub_eq_add_neg]
  rw [e] at this
  filter_upwards [this, h.const] with ω h1 h2
  rw [h1]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h3 : η (fun _ => 1) ω = 0 := h2
  rw [h3]; ring

theorem s21l_gfam (h : S21LEta μ P η Λ) {N : ℕ} {f : Fin N → HRS.Euc d → ℝ} (hf : ∀ i, MemLp (f i) 2 μ) :
    S94GFam P (fun i : Fin N => η (f i)) := by
  refine ⟨fun i => (h.memLp _ (hf i)).aemeasurable, fun α => ?_⟩
  have hs := s21l_eta_sum h Finset.univ α f (fun i _ => hf i)
  obtain ⟨v, hv⟩ := h.gauss _ (memLp_finsetSum _ fun i _ => (hf i).const_mul (α i))
  refine ⟨v, ?_⟩
  rw [← hv]
  exact Measure.map_congr hs.symm

theorem s21l_test_memLp {a : HRS.Euc d → ℝ} (ha : HRS.Whole.IsR2Test a) : MemLp a 2 μ := by
  obtain ⟨C, hC⟩ := s94_test_bounded ha
  exact MemLp.of_bound (s94_test_continuous ha).aestronglyMeasurable C (ae_of_all _ fun x => by simpa using hC x)

theorem s21l_eta_test (h : S21LEta μ P η Λ) {a : HRS.Euc d → ℝ} (ha : HRS.Whole.IsR2Test a) :
    η (HRS.Whole.projMean μ a) =ᵐ[P] η a := by
  have := s21l_eta_center h (s21l_test_memLp (μ := μ) ha)
  exact this

theorem s21l_cov_test (h : S21LEta μ P η Λ) {a : HRS.Euc d → ℝ} (ha : HRS.Whole.IsR2Test a) :
    ∫ ω, η a ω ^ 2 ∂P ≤ Λ * ∫ x, (HRS.Whole.projMean μ a x) ^ 2 ∂μ := by
  have h1 := s21l_eta_test h ha
  have h2 : ∫ ω, η a ω ^ 2 ∂P = ∫ ω, η (HRS.Whole.projMean μ a) ω ^ 2 ∂P :=
    integral_congr_ae (by filter_upwards [h1] with ω hω; rw [hω])
  rw [h2]
  exact h.cov _ (s94_memLp_projMean ha)

theorem s21l_gseq (h : S21LEta μ P η Λ) {a : ℕ → HRS.Euc d → ℝ} (ha : ∀ i, HRS.Whole.IsR2Test (a i))
    (hon : ∀ i j, ∫ x, HRS.Whole.projMean μ (a i) x * HRS.Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0) :
    S94GSeq P (fun i ζ => η (a i) ζ) Λ := fun n => by
  refine ⟨s21l_gfam h (f := fun i : Fin n => a i) (fun i => s21l_test_memLp (ha i)), fun α => ?_⟩
  have hea : ∀ i : Fin n, MemLp (HRS.Whole.projMean μ (a i)) 2 μ := fun i => s94_memLp_projMean (ha i)
  have hs := s21l_eta_sum h Finset.univ α (fun i : Fin n => HRS.Whole.projMean μ (a i)) (fun i _ => hea i)
  have hF : MemLp (fun x => ∑ i : Fin n, α i * HRS.Whole.projMean μ (a i) x) 2 μ :=
    memLp_finsetSum _ fun i _ => (hea i).const_mul (α i)
  have h1 : s94q P (fun i : Fin n => η (a i)) α = ∫ ω, η (fun x => ∑ i : Fin n, α i * HRS.Whole.projMean μ (a i) x) ω ^ 2 ∂P := by
    unfold s94q s94lin
    refine integral_congr_ae ?_
    filter_upwards [hs, ae_all_iff.2 fun i : Fin n => s21l_eta_test h (ha i)] with ω h2 h3
    rw [h2]
    simp only [h3]
  rw [h1]
  refine (h.cov _ hF).trans ?_
  have e2 : ∫ x, (∑ i : Fin n, α i * HRS.Whole.projMean μ (a i) x) ^ 2 ∂μ = ∑ i, α i ^ 2 := by
    rw [← s94_projMean_sq_lincomb μ (a := fun i : Fin n => a i) (fun i => ha i)
      (fun i j => by simpa [Fin.ext_iff] using hon i j) α]
    exact integral_congr_ae (ae_of_all _ fun x => by
      beta_reduce
      rw [s94_projMean_lincomb μ (a := fun i : Fin n => a i) (fun i => ha i) α x])
  rw [e2]

end Eta

end HRS.MS.R26T3
