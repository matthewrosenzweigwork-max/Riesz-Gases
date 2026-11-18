import HRS.MS.R2ChaosAux41

/-!
# HRS.MS.R2ChaosAux42 -- (a): existence of an orthonormal basis `IsR2ZeroMeanONB`

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_exists_onb`: for `μ = ρ dx` (`IsRound2Density`, `d ≥ 2`) there is an `IsR2ZeroMeanONB μ a`.
Gram-Schmidt on a countable dense family of `{P_μ b : b ∈ C_c^∞}`; the nonzero normalised vectors are infinitely many
(`s94_poly_indep` + finite-dimensional subspaces are closed), enumerated by `Nat.nth`; completeness from
`s94_test_separates`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology ContDiff
open InnerProductSpace

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

theorem s94_coeFn_finsum {μ : Measure (Euc d)} {ι : Type*} (g : ι → ℝ) (w : ι → Lp ℝ 2 μ) (s : Finset ι) :
    ⇑(∑ j ∈ s, g j • w j) =ᵐ[μ] fun x => ∑ j ∈ s, g j * (w j : Euc d → ℝ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    simpa using hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (g a • w a) (∑ j ∈ s, g j • w j), Lp.coeFn_smul (g a) (w a), ih] with x h1 h2 h3
    rw [h1]
    simp only [Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul, Finset.sum_insert ha]

theorem s94_exists_onb {s M L : ℝ} {ρ : Euc d → ℝ} (hd : 2 ≤ d) (hρ : IsRound2Density d s M L ρ) :
    ∃ a : ℕ → Euc d → ℝ, IsR2ZeroMeanONB (Whole.withDensityReal ρ) a := by
  classical
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  set μ := Whole.withDensityReal ρ with hμ
  let T := s94TestSub μ
  have hsep : TopologicalSpace.IsSeparable (T : Set (Lp ℝ 2 μ)) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  obtain ⟨D, hDT, hDc, hDd⟩ := hsep.exists_countable_dense_subset
  have hDne : D.Nonempty := by
    have h0 : (0 : Lp ℝ 2 μ) ∈ closure D := hDd (T.zero_mem : (0 : Lp ℝ 2 μ) ∈ (T : Set (Lp ℝ 2 μ)))
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at h0
    exact h0
  obtain ⟨v, hv⟩ := hDc.exists_eq_range hDne
  have hvT : ∀ k, v k ∈ T := fun k => hDT (hv ▸ Set.mem_range_self k)
  have hspan : Submodule.span ℝ (Set.range v) ≤ T := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hvT k)
  let gs := gramSchmidtNormed ℝ v
  have hspgs : Submodule.span ℝ (Set.range gs) = Submodule.span ℝ (Set.range v) := by
    rw [span_gramSchmidtNormed_range, span_gramSchmidt]
  have hgsT : ∀ k, gs k ∈ T := by
    intro k
    have : gs k ∈ Submodule.span ℝ (Set.range gs) := Submodule.subset_span ⟨k, rfl⟩
    rw [hspgs] at this
    exact hspan this
  choose bb hbb hbbe using hgsT
  -- infinitely many nonzero vectors
  have hI : (setOf fun k => gs k ≠ 0).Infinite := by
    intro hfin
    let S : Finset (Lp ℝ 2 μ) := hfin.toFinset.image gs
    let W : Submodule ℝ (Lp ℝ 2 μ) := Submodule.span ℝ (S : Set (Lp ℝ 2 μ))
    have hgsW : ∀ k, gs k ∈ W := by
      intro k
      by_cases hk : gs k = 0
      · rw [hk]; exact W.zero_mem
      · exact Submodule.subset_span (by simp only [S, Finset.coe_image, Set.Finite.coe_toFinset]; exact ⟨k, hk, rfl⟩)
    have hvW : ∀ k, v k ∈ W := by
      intro k
      have : v k ∈ Submodule.span ℝ (Set.range v) := Submodule.subset_span ⟨k, rfl⟩
      rw [← hspgs] at this
      exact (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hgsW j)) this
    have hWc : IsClosed (W : Set (Lp ℝ 2 μ)) := Submodule.closed_of_finiteDimensional W
    have hTW : ∀ x ∈ T, x ∈ W := by
      intro x hx
      have h1 : x ∈ closure D := hDd hx
      have h2 : D ⊆ (W : Set (Lp ℝ 2 μ)) := by
        rw [hv]; rintro _ ⟨k, rfl⟩; exact hvW k
      exact (closure_minimal h2 hWc) h1
    obtain ⟨c, hc, hind⟩ := s94_poly_indep hd hρ (S.card + 1)
    let w : Fin (S.card + 1) → Lp ℝ 2 μ := fun j => s94tp μ (c j)
    have hwT : ∀ j, w j ∈ T := fun j => ⟨c j, hc j, rfl⟩
    have hli : LinearIndependent ℝ w := by
      rw [Fintype.linearIndependent_iff]
      intro g hg j
      refine hind g ?_ j
      have h1 := s94_coeFn_finsum g w Finset.univ
      rw [hg] at h1
      have hw : ∀ j, (w j : Euc d → ℝ) =ᵐ[μ] Whole.projMean μ (c j) := fun j => by
        simp only [w]; rw [s94tp_eq (hc j)]; exact MemLp.coeFn_toLp _
      have hw' : ∀ᵐ x ∂μ, ∀ j, (w j : Euc d → ℝ) x = Whole.projMean μ (c j) x := ae_all_iff.2 hw
      filter_upwards [h1, Lp.coeFn_zero ℝ 2 μ, hw'] with x hx h0 hwx
      have hx2 : (0 : ℝ) = ∑ j, g j * (w j : Euc d → ℝ) x := by
        have := h0.symm.trans hx
        simpa using this
      rw [hx2]
      exact Finset.sum_congr rfl fun j _ => by rw [hwx j]
    have hwW : ∀ j, w j ∈ W := fun j => hTW _ (hwT j)
    let w' : Fin (S.card + 1) → W := fun j => ⟨w j, hwW j⟩
    have hli' : LinearIndependent ℝ w' :=
      LinearIndependent.of_comp W.subtype (by simpa [Function.comp_def, w'] using hli)
    have h1 := hli'.fintype_card_le_finrank
    have h2 : Module.finrank ℝ W ≤ S.card := finrank_span_finset_le_card S
    simp only [Fintype.card_fin] at h1
    omega
  let kk : ℕ → ℕ := Nat.nth (fun k => gs k ≠ 0)
  have hkkmem : ∀ i, gs (kk i) ≠ 0 := Nat.nth_mem_of_infinite hI
  have hkkinj : Function.Injective kk := Nat.nth_injective hI
  have hkkrange : Set.range kk = setOf (fun k => gs k ≠ 0) := Nat.range_nth_of_infinite hI
  refine ⟨fun i => bb (kk i), fun i => hbb _, ?_, ?_⟩
  · intro i j
    have hi := hbb (kk i)
    have hj := hbb (kk j)
    have h1 := s94_inner_tp (μ := μ) (s94_projMean_memLp hi) hj
    rw [← s94tp_eq hi, hbbe, hbbe] at h1
    rw [← h1]
    have hon := orthonormal_iff_ite.1 (gramSchmidtNormed_orthonormal' v) ⟨kk i, hkkmem i⟩ ⟨kk j, hkkmem j⟩
    simp only at hon
    rw [hon]
    by_cases hij : i = j
    · simp [hij]
    · have : (⟨kk i, hkkmem i⟩ : {k | gs k ≠ 0}) ≠ ⟨kk j, hkkmem j⟩ := fun h => hij (hkkinj (Subtype.mk.inj h))
      simp [hij, this]
  · intro f hf hf0 hfa
    set F : Lp ℝ 2 μ := hf.toLp f with hF
    have hperp_gs : ∀ k, inner ℝ F (gs k) = 0 := by
      intro k
      by_cases hk : gs k = 0
      · simp [hk]
      · obtain ⟨i, rfl⟩ : k ∈ Set.range kk := by rw [hkkrange]; exact hk
        rw [← hbbe (kk i), hF, s94_inner_tp hf (hbb _)]
        have hb := hbb (kk i)
        obtain ⟨C, hC⟩ := s94_test_bounded hb
        have hint : Integrable (fun x => f x * bb (kk i) x) μ :=
          (hf.integrable one_le_two).mul_bdd (s94_test_continuous hb).aestronglyMeasurable
            (ae_of_all _ fun x => by simpa using hC x)
        have := hfa i
        simp only [Whole.projMean, Whole.pair, mul_sub]
        rw [integral_sub hint (by simpa using (hf.integrable one_le_two).mul_const (∫ x, bb (kk i) x ∂μ)),
          integral_mul_const, hf0, this]
        simp
    have hperp_v : ∀ k, inner ℝ F (v k) = 0 := by
      intro k
      have hmem : v k ∈ Submodule.span ℝ (Set.range gs) := by
        rw [hspgs]; exact Submodule.subset_span ⟨k, rfl⟩
      refine Submodule.span_induction (p := fun u _ => inner ℝ F u = 0) (fun u hu => ?_) (by simp)
        (fun u1 u2 _ _ h1 h2 => by rw [inner_add_right, h1, h2, add_zero])
        (fun c u _ h => by rw [inner_smul_right, h, mul_zero]) hmem
      obtain ⟨k', rfl⟩ := hu
      exact hperp_gs k'
    have hclosed : IsClosed {z : Lp ℝ 2 μ | inner ℝ F z = 0} :=
      isClosed_eq (by fun_prop) continuous_const
    have hperpT : ∀ x ∈ T, inner ℝ F x = 0 := by
      intro x hx
      have h2 : D ⊆ {z : Lp ℝ 2 μ | inner ℝ F z = 0} := by
        rw [hv]; rintro _ ⟨k, rfl⟩; exact hperp_v k
      exact (closure_minimal h2 hclosed) (hDd hx)
    refine s94_test_separates hρ.prob hf (fun b hb => ?_)
    have h1 := hperpT (s94tp μ b) ⟨b, hb, rfl⟩
    rw [hF, s94_inner_tp hf hb] at h1
    obtain ⟨C, hC⟩ := s94_test_bounded hb
    have hint : Integrable (fun x => f x * b x) μ :=
      (hf.integrable one_le_two).mul_bdd (s94_test_continuous hb).aestronglyMeasurable
        (ae_of_all _ fun x => by simpa using hC x)
    simp only [Whole.projMean, Whole.pair, mul_sub] at h1
    rw [integral_sub hint (by simpa using (hf.integrable one_le_two).mul_const (∫ x, b x ∂μ)),
      integral_mul_const, hf0] at h1
    simpa using h1

end HRS.MS.R2Chaos
