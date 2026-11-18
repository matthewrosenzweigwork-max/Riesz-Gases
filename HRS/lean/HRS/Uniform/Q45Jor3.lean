import HRS.Uniform.Q45Jor2

/-!
# Q45 (Lemma 3.20): Jordan decomposition, trace class and trace norm bound
-/

noncomputable section

open MeasureTheory Filter Topology HRS.HilbertCLTAux
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

section Trace

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- A basis adapted to the range of `Q` (when `QR = 0`): each vector is either in `(ker Q)ᗮ` (and then killed by `R`)
or killed by `Q`. -/
lemma trace_side {Q R : H →L[ℝ] H} (hQs : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (hRs : ∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) (hQR : Q * R = 0) :
    ∃ (w : Set H) (b : HilbertBasis w ℝ H), ⇑b = ((↑) : w → H) ∧
      ∀ e ∈ w, ((e ∈ (LinearMap.ker (Q : H →ₗ[ℝ] H))ᗮ ∧ R e = 0) ∨ Q e = 0) := by
  set K : Submodule ℝ H := LinearMap.ker (Q : H →ₗ[ℝ] H) with hK
  haveI : CompleteSpace K := (Q.isClosed_ker).completeSpace_coe
  haveI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  obtain ⟨w, b, hb, had⟩ := exists_adapted_basis (Kᗮ) (Submodule.isClosed_orthogonal K)
  refine ⟨w, b, hb, fun e he => ?_⟩
  rcases had e he with h | h
  · left
    refine ⟨h, ?_⟩
    refine ext_inner_right ℝ fun y => ?_
    rw [hRs, inner_zero_left]
    have : R y ∈ K := by
      show Q (R y) = 0
      have := congrArg (fun T : H →L[ℝ] H => T y) hQR
      simpa using this
    exact Submodule.inner_left_of_mem_orthogonal this h
  · right
    have : e ∈ K := by rwa [Submodule.orthogonal_orthogonal] at h
    exact this

lemma psd_diag_nonneg {Q : H →L[ℝ] H} (hQ : IsPSDOp Q) (e : H) : 0 ≤ inner ℝ (Q e) e := hQ.nonneg e

theorem jordan_trace {P N : H →L[ℝ] H} (hP : IsPSDOp P) (hN : IsPSDOp N) (hPN : P * N = 0)
    (hNP : N * P = 0) {D : H →L[ℝ] H →L[ℝ] ℝ} (hD : ∀ x y, D x y = inner ℝ ((P - N) x) y)
    (hb : BddAbove (Set.range fun p : OrthonormalPairs H => ∑ i, |D (p.1.2.1 i) (p.1.2.2 i)|)) :
    IsTraceClassCov (formOfOp P) ∧ IsTraceClassCov (formOfOp N) ∧
      traceNormForm (formOfOp P) + traceNormForm (formOfOp N) ≤ traceNormForm D := by
  classical
  obtain ⟨wP, bP, hbP, hadP⟩ := trace_side hP.symm hN.symm hPN
  obtain ⟨wN, bN, hbN, hadN⟩ := trace_side hN.symm hP.symm hNP
  have honP : Orthonormal ℝ ((↑) : wP → H) := hbP ▸ bP.orthonormal
  have honN : Orthonormal ℝ ((↑) : wN → H) := hbN ▸ bN.orthonormal
  -- classification of diagonal values
  have dP : ∀ e : wP, inner ℝ (P e) (e : H) = if (e : H) ∈ (LinearMap.ker (P : H →ₗ[ℝ] H))ᗮ then D e e else 0 := by
    intro e
    rcases hadP e e.2 with ⟨h1, h2⟩ | h
    · rw [if_pos h1, hD]
      simp [h2]
    · have : (e : H) ∉ (LinearMap.ker (P : H →ₗ[ℝ] H))ᗮ := by
        intro h1
        have hk : (e : H) ∈ LinearMap.ker (P : H →ₗ[ℝ] H) := h
        have := Submodule.inner_right_of_mem_orthogonal hk h1
        have h0 : (e : H) = 0 := by simpa using this
        have := honP.norm_eq_one e
        simp [h0] at this
      rw [if_neg this, h]; simp
  have dN : ∀ e : wN, inner ℝ (N e) (e : H) = if (e : H) ∈ (LinearMap.ker (N : H →ₗ[ℝ] H))ᗮ then -D e e else 0 := by
    intro e
    rcases hadN e e.2 with ⟨h1, h2⟩ | h
    · rw [if_pos h1, hD]
      simp [h2]
    · have : (e : H) ∉ (LinearMap.ker (N : H →ₗ[ℝ] H))ᗮ := by
        intro h1
        have hk : (e : H) ∈ LinearMap.ker (N : H →ₗ[ℝ] H) := h
        have := Submodule.inner_right_of_mem_orthogonal hk h1
        have h0 : (e : H) = 0 := by simpa using this
        have := honN.norm_eq_one e
        simp [h0] at this
      rw [if_neg this, h]; simp
  -- the joint bound
  have key : ∀ (F : Finset wP) (G : Finset wN),
      ∑ e ∈ F, inner ℝ (P e) (e : H) + ∑ e ∈ G, inner ℝ (N e) (e : H) ≤ traceNormForm D := by
    intro F G
    set F₁ := F.filter (fun e : wP => (e : H) ∈ (LinearMap.ker (P : H →ₗ[ℝ] H))ᗮ) with hF₁
    set G₁ := G.filter (fun e : wN => (e : H) ∈ (LinearMap.ker (N : H →ₗ[ℝ] H))ᗮ) with hG₁
    have e1 : ∑ e ∈ F, inner ℝ (P e) (e : H) = ∑ e ∈ F₁, D e e := by
      simp_rw [dP]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have e2 : ∑ e ∈ G, inner ℝ (N e) (e : H) = ∑ e ∈ G₁, -D e e := by
      simp_rw [dN]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [e1, e2]
    let h : (↥F₁ ⊕ ↥G₁) → H := Sum.elim (fun e => ((e : wP) : H)) (fun e => ((e : wN) : H))
    have hon : Orthonormal ℝ h := by
      rw [orthonormal_iff_ite]
      intro i j
      rcases i with i | i <;> rcases j with j | j
      · have := orthonormal_iff_ite.1 honP i.1 j.1
        have hiff : (i.1 = j.1) ↔ ((Sum.inl i : ↥F₁ ⊕ ↥G₁) = Sum.inl j) :=
          ⟨fun h' => congrArg Sum.inl (Subtype.ext h'), fun h' => congrArg Subtype.val (Sum.inl.inj h')⟩
        exact this.trans (if_congr hiff rfl rfl)
      · -- `e ∈ (ker P)ᗮ`, `e' ∈ (ker N)ᗮ` with `P e' = 0`
        have hx : ((i : wP) : H) ∈ (LinearMap.ker (P : H →ₗ[ℝ] H))ᗮ := (Finset.mem_filter.1 i.2).2
        have hy : ((j : wN) : H) ∈ LinearMap.ker (P : H →ₗ[ℝ] H) := by
          rcases hadN j j.1.2 with ⟨-, h2⟩ | h
          · exact h2
          · exfalso
            have hy' := (Finset.mem_filter.1 j.2).2
            have hk : ((j : wN) : H) ∈ LinearMap.ker (N : H →ₗ[ℝ] H) := h
            have := Submodule.inner_right_of_mem_orthogonal hk hy'
            have h0 : ((j : wN) : H) = 0 := by simpa using this
            have := honN.norm_eq_one j.1
            simp [h0] at this
        have := Submodule.inner_left_of_mem_orthogonal hy hx
        simp [h, this]
      · have hx : ((j : wP) : H) ∈ (LinearMap.ker (P : H →ₗ[ℝ] H))ᗮ := (Finset.mem_filter.1 j.2).2
        have hy : ((i : wN) : H) ∈ LinearMap.ker (P : H →ₗ[ℝ] H) := by
          rcases hadN i i.1.2 with ⟨-, h2⟩ | h
          · exact h2
          · exfalso
            have hy' := (Finset.mem_filter.1 i.2).2
            have hk : ((i : wN) : H) ∈ LinearMap.ker (N : H →ₗ[ℝ] H) := h
            have := Submodule.inner_right_of_mem_orthogonal hk hy'
            have h0 : ((i : wN) : H) = 0 := by simpa using this
            have := honN.norm_eq_one i.1
            simp [h0] at this
        have := Submodule.inner_right_of_mem_orthogonal hy hx
        simp [h, this]
      · have := orthonormal_iff_ite.1 honN i.1 j.1
        have hiff : (i.1 = j.1) ↔ ((Sum.inr i : ↥F₁ ⊕ ↥G₁) = Sum.inr j) :=
          ⟨fun h' => congrArg Sum.inr (Subtype.ext h'), fun h' => congrArg Subtype.val (Sum.inr.inj h')⟩
        exact this.trans (if_congr hiff rfl rfl)
    set s : (↥F₁ ⊕ ↥G₁) → ℝ := Sum.elim (fun _ => 1) (fun _ => -1) with hs
    have hs' : ∀ i, s i = 1 ∨ s i = -1 := by
      intro i; rcases i with i | i <;> simp [hs]
    have := signed_sum_le_traceNormForm hb h hon s hs'
    rw [Fintype.sum_sum_type] at this
    simp only [h, hs, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul] at this
    rw [Finset.sum_coe_sort F₁ (fun e => D (e : H) (e : H)),
      Finset.sum_coe_sort G₁ (fun e => -D (e : H) (e : H))] at this
    have e3 : ∑ e ∈ G₁, -D (e : H) (e : H) = ∑ e ∈ G₁, -D (e : H) (e : H) := rfl
    simpa [Finset.sum_neg_distrib, sub_eq_add_neg] using this
  -- summability and traces
  have hsP : Summable fun e : wP => inner ℝ (P e) (e : H) :=
    summable_of_sum_le (c := traceNormForm D) (fun e => hP.nonneg _) fun F => by
      have := key F ∅
      simpa [Finset.sum_empty] using this
  have hsN : Summable fun e : wN => inner ℝ (N e) (e : H) :=
    summable_of_sum_le (c := traceNormForm D) (fun e => hN.nonneg _) fun G => by
      have := key ∅ G
      simpa [Finset.sum_empty] using this
  have hTP : IsTraceClassCov (formOfOp P) :=
    ⟨fun x y => by simp only [formOfOp_apply]; rw [hP.symm, real_inner_comm],
     fun x => hP.nonneg x, ⟨wP, bP, by simpa [hbP, formOfOp_apply] using hsP⟩⟩
  have hTN : IsTraceClassCov (formOfOp N) :=
    ⟨fun x y => by simp only [formOfOp_apply]; rw [hN.symm, real_inner_comm],
     fun x => hN.nonneg x, ⟨wN, bN, by simpa [hbN, formOfOp_apply] using hsN⟩⟩
  refine ⟨hTP, hTN, ?_⟩
  have h1 := traceNormForm_le_basis_trace hTP bP
  have h2 := traceNormForm_le_basis_trace hTN bN
  simp only [hbP, hbN, formOfOp_apply] at h1 h2
  have h3 : ∑' e : wP, inner ℝ (P e) (e : H) ≤ traceNormForm D - ∑' e : wN, inner ℝ (N e) (e : H) := by
    refine hsP.tsum_le_of_sum_le fun F => ?_
    have h4 : ∀ G : Finset wN, ∑ e ∈ G, inner ℝ (N e) (e : H) ≤ traceNormForm D - ∑ e ∈ F, inner ℝ (P e) (e : H) :=
      fun G => by linarith [key F G]
    have h5 := hsN.tsum_le_of_sum_le h4
    linarith
  linarith

end Trace

end HRS.Uniform.Q45
