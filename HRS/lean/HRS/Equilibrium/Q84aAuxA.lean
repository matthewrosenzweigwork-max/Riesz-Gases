/-
# HRS.Equilibrium.Q84aAuxA — packet Q84a helpers (geometry, derivative bounds)

Helpers for the size bounds of Lemma 4.15 (`q84a_estimates`): torus geometry (centered lifts, the
periodic distance against Euclidean distance of lifts), the gradient bound
`‖∇_xψ(a,c)‖ ≤ K(1 + r^{1-s})`, and the gradient-difference bound along a segment (Hessian bound).
-/
import HRS.Equilibrium.PairCorrection

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84a

variable {d : ℕ} {s : ℝ}

/-! ### Elementary torus geometry -/

theorem q84a_mk_add (a b : Euc d) : Torus.mk (a + b) = Torus.mk a + Torus.mk b := by
  funext i; simp [Torus.mk]

theorem q84a_mk_sub (a b : Euc d) : Torus.mk (a - b) = Torus.mk a - Torus.mk b := by
  funext i; simp [Torus.mk]

theorem q84a_continuous_mk : Continuous (Torus.mk : Euc d → Torus d) := by
  unfold Torus.mk
  refine continuous_pi fun i => ?_
  exact (AddCircle.continuous_mk' _).comp (by fun_prop)

theorem q84a_isOpen_offDiag : IsOpen (offDiag d) :=
  isOpen_ne_fun (q84a_continuous_mk.comp continuous_fst) (q84a_continuous_mk.comp continuous_snd)

theorem q84a_eucDist_mk_le (u v : Euc d) :
    Torus.eucDist (Torus.mk u) (Torus.mk v) ≤ ‖u - v‖ := by
  unfold Torus.eucDist
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h1 : ‖(Torus.mk u : Torus d) i - (Torus.mk v : Torus d) i‖ ≤ ‖(u - v) i‖ := by
    have e : (Torus.mk u : Torus d) i - (Torus.mk v : Torus d) i = (((u - v) i : ℝ) : UnitAddCircle) := by
      simp [Torus.mk]
    rw [e]
    exact QuotientAddGroup.norm_mk_le_norm
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

theorem q84a_eucDist_le (hd : 1 ≤ d) (x y : Torus d) : Torus.eucDist x y ≤ d := by
  unfold Torus.eucDist
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : ∀ i, ‖x i - y i‖ ^ 2 ≤ 1 := by
    intro i
    have := AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := x i - y i) one_ne_zero
    rw [abs_one] at this
    have h0 := norm_nonneg (x i - y i)
    nlinarith
  calc ∑ i, ‖x i - y i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => h1 i
    _ = d := by simp
    _ ≤ (d : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith

theorem q84a_exists_centered (z : Torus d) :
    ∃ w : Euc d, Torus.mk w = z ∧ ∀ i, |w i| ≤ 1 / 2 := by
  refine ⟨WithLp.toLp 2 fun i => Torus.rep z i - (round (Torus.rep z i) : ℝ), ?_, fun i => ?_⟩
  · funext i
    have h1 : ((Torus.rep z i : ℝ) : UnitAddCircle) = z i := by
      have := congrFun (Torus.mk_rep z) i
      simpa [Torus.mk] using this
    have h2 : (((round (Torus.rep z i) : ℤ) : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨round (Torus.rep z i), by simp⟩
    show (((Torus.rep z i - (round (Torus.rep z i) : ℝ) : ℝ)) : UnitAddCircle) = z i
    rw [AddCircle.coe_sub, h2, sub_zero, h1]
  · simpa using abs_sub_round (Torus.rep z i)

theorem q84a_exists_lift_dist (x y : Torus d) :
    ∃ w : Euc d, Torus.mk w = x - y ∧ ‖w‖ = Torus.eucDist x y := by
  obtain ⟨w, hw, hw'⟩ := q84a_exists_centered (x - y)
  refine ⟨w, hw, ?_⟩
  rw [PairCorrAux.eucDist_sub_zero, ← hw]
  exact (PairCorrAux.eucDist_mk_zero' hw').symm

theorem q84a_seg_norm {A B u : Euc d} (hu : u ∈ segment ℝ A B) : ‖u - A‖ ≤ ‖B - A‖ := by
  rw [segment_eq_image'] at hu
  obtain ⟨t, ht, rfl⟩ := hu
  have : A + t • (B - A) - A = t • (B - A) := by abel
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2

/-! ### Gradient of the lift, in terms of the Fréchet derivative of `lift2 ψ` -/

theorem q84a_fderiv_lift2_congr (ψ : Torus d → Torus d → ℝ) {z z' : Euc d}
    (h : Torus.mk z' = Torus.mk z) (b : Euc d) :
    fderiv ℝ (lift2 ψ) (z', b) = fderiv ℝ (lift2 ψ) (z, b) := by
  have hδ : Torus.mk (z' - z) = 0 := by
    rw [q84a_mk_sub, h, sub_self]
  have hshift : (fun p : Euc d × Euc d => lift2 ψ (p + (z' - z, 0))) = lift2 ψ := by
    funext p
    simp only [lift2, Prod.fst_add, Prod.snd_add, add_zero]
    rw [q84a_mk_add, hδ, add_zero]
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := lift2 ψ) (z' - z, (0 : Euc d)) (x := (z, b))
  rw [hshift] at this
  rw [this]
  congr 1
  simp

theorem q84a_gradFst_eq {ψ : Torus d → Torus d → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d))
    {u v : Euc d} (hp : (u, v) ∈ offDiag d) :
    gradFst ψ (Torus.mk u) (Torus.mk v) = (InnerProductSpace.toDual ℝ (Euc d)).symm
      ((fderiv ℝ (lift2 ψ) (u, v)).comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))) := by
  have hp' : (Torus.rep (Torus.mk u), v) ∈ offDiag d := by
    show Torus.mk (Torus.rep (Torus.mk u)) ≠ Torus.mk v
    rw [Torus.mk_rep]; exact hp
  have hd : DifferentiableAt ℝ (lift2 ψ) (Torus.rep (Torus.mk u), v) :=
    (hsm.contDiffAt (q84a_isOpen_offDiag.mem_nhds hp')).differentiableAt (by simp)
  have hfun : Torus.lift (fun z => ψ z (Torus.mk v)) = lift2 ψ ∘ fun x : Euc d => (x, v) := by
    funext x; rfl
  have hf := hasFDerivAt_prodMk_left (𝕜 := ℝ) (Torus.rep (Torus.mk u)) v
  have hder := hd.hasFDerivAt.comp (Torus.rep (Torus.mk u)) hf
  have e1 : fderiv ℝ (lift2 ψ) (Torus.rep (Torus.mk u), v) = fderiv ℝ (lift2 ψ) (u, v) :=
    q84a_fderiv_lift2_congr ψ (by rw [Torus.mk_rep]) v
  unfold gradFst Torus.grad gradient
  rw [hfun, hder.fderiv, e1]

theorem q84a_norm_comp_inl (T : (Euc d × Euc d) →L[ℝ] ℝ) :
    ‖T.comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  have := T.le_opNorm (v, 0)
  simpa [Prod.norm_def] using this

theorem q84a_K_nonneg {ψ : Torus d → Torus d → ℝ} {K : ℝ} (hψ : PsiSize s K ψ) {a c : Torus d}
    (hac : a ≠ c) : 0 ≤ K := by
  have hp : (Torus.rep a, Torus.rep c) ∈ offDiag d := by
    show Torus.mk (Torus.rep a) ≠ Torus.mk (Torus.rep c)
    rw [Torus.mk_rep, Torus.mk_rep]; exact hac
  have h : ‖fderiv ℝ (lift2 ψ) (Torus.rep a, Torus.rep c)‖ ≤
      K * (1 + rTrunc (Torus.mk (Torus.rep a)) (Torus.mk (Torus.rep c)) ^ (1 - s)) := hψ.grad _ hp
  have h0 := norm_nonneg (fderiv ℝ (lift2 ψ) (Torus.rep a, Torus.rep c))
  have hpos : 0 < 1 + rTrunc (Torus.mk (Torus.rep a)) (Torus.mk (Torus.rep c)) ^ (1 - s) :=
    add_pos_of_pos_of_nonneg one_pos (Real.rpow_nonneg (PairCorrAux.rTrunc_nonneg _ _) _)
  by_contra hK
  have hK := not_le.mp hK
  have := mul_neg_of_neg_of_pos hK hpos
  linarith

/-- `‖∇_xψ(a,c)‖ ≤ K(1 + r(a,c)^{1-s})` for `a ≠ c`. -/
theorem q84a_grad_norm {ψ : Torus d → Torus d → ℝ} {K : ℝ} (hψ : PsiSize s K ψ) {a c : Torus d}
    (hac : a ≠ c) : ‖gradFst ψ a c‖ ≤ K * (1 + rTrunc a c ^ (1 - s)) := by
  have hp : (Torus.rep a, Torus.rep c) ∈ offDiag d := by
    show Torus.mk (Torus.rep a) ≠ Torus.mk (Torus.rep c)
    rw [Torus.mk_rep, Torus.mk_rep]; exact hac
  have e := q84a_gradFst_eq hψ.smooth hp
  rw [Torus.mk_rep, Torus.mk_rep] at e
  rw [e, LinearIsometryEquiv.norm_map]
  refine (q84a_norm_comp_inl _).trans ?_
  have h : ‖fderiv ℝ (lift2 ψ) (Torus.rep a, Torus.rep c)‖ ≤
      K * (1 + rTrunc (Torus.mk (Torus.rep a)) (Torus.mk (Torus.rep c)) ^ (1 - s)) := hψ.grad _ hp
  rw [Torus.mk_rep, Torus.mk_rep] at h
  exact h

/-- Gradient difference along a segment (`Q:eq:gradient-difference-bound`, near case). -/
theorem q84a_grad_diff {ψ : Torus d → Torus d → ℝ} {K : ℝ} (hψ : PsiSize s K ψ) (hs : 0 < s)
    {a b c : Torus d} (hac : a ≠ c) (h : Torus.eucDist a b ≤ Torus.eucDist a c / 2) :
    ‖gradFst ψ a c - gradFst ψ b c‖ ≤
      K * (1 + 2 ^ s * rTrunc a c ^ (-s)) * Torus.eucDist a b := by
  obtain ⟨w, hw, hwn⟩ := q84a_exists_lift_dist a b
  have hmA : Torus.mk (Torus.rep a) = a := Torus.mk_rep a
  have hmC : Torus.mk (Torus.rep c) = c := Torus.mk_rep c
  set A : Euc d := Torus.rep a with hA
  set C : Euc d := Torus.rep c with hC
  set B : Euc d := A - w with hB
  have hmB : Torus.mk B = b := by
    rw [hB, q84a_mk_sub, hmA, hw]; abel
  have hEpos : 0 < Torus.eucDist a c := by
    rcases (PairCorrAux.eucDist_nonneg' a c).lt_or_eq with h0 | h0
    · exact h0
    · exact absurd ((PairCorrAux.eucDist_eq_zero' a c).1 h0.symm) hac
  set E := Torus.eucDist a c with hE
  have hK : 0 ≤ K := q84a_K_nonneg hψ hac
  set S : Set (Euc d × Euc d) := segment ℝ A B ×ˢ ({C} : Set (Euc d)) with hS
  have hSconv : Convex ℝ S := (convex_segment A B).prod (convex_singleton C)
  have hmem : ∀ p ∈ S, E / 2 ≤ Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hv' : v = C := hv
    show E / 2 ≤ Torus.eucDist (Torus.mk u) (Torus.mk v)
    rw [hv', hmC]
    have h1 := q84a_seg_norm hu
    have h2 : B - A = -w := by rw [hB]; abel
    rw [h2, norm_neg, hwn] at h1
    have h3 : Torus.eucDist a (Torus.mk u) ≤ ‖u - A‖ := by
      have := q84a_eucDist_mk_le A u
      rw [hmA, norm_sub_rev] at this
      exact this
    have h4 := PairCorrAux.eucDist_triangle a (Torus.mk u) c
    linarith
  have hoff : ∀ p ∈ S, p ∈ offDiag d := by
    intro p hp
    show Torus.mk p.1 ≠ Torus.mk p.2
    intro hEq
    have := hmem p hp
    have h0 : Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) = 0 := by
      rw [hEq]; exact PairCorrAux.eucDist_self' _
    linarith
  have hxS : (A, C) ∈ S := ⟨left_mem_segment ℝ A B, rfl⟩
  have hyS : (B, C) ∈ S := ⟨right_mem_segment ℝ A B, rfl⟩
  have hf : ∀ p ∈ S, DifferentiableAt ℝ (fderiv ℝ (lift2 ψ)) p := by
    intro p hp
    have h1 := hψ.smooth.contDiffAt (q84a_isOpen_offDiag.mem_nhds (hoff p hp))
    exact (h1.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hR : 0 < rTrunc a c := PairCorrAux.rTrunc_pos hac
  have hbound : ∀ p ∈ S, ‖fderiv ℝ (fderiv ℝ (lift2 ψ)) p‖ ≤
      K * (1 + 2 ^ s * rTrunc a c ^ (-s)) := by
    intro p hp
    have h2 : ‖fderiv ℝ (fderiv ℝ (lift2 ψ)) p‖ = ‖iteratedFDeriv ℝ 2 (lift2 ψ) p‖ := by
      rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ (lift2 ψ)) (x := p)]
      exact norm_iteratedFDeriv_fderiv
    rw [h2]
    refine (hψ.hess p (hoff p hp)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hK
    have hlow : rTrunc a c / 2 ≤ rTrunc (Torus.mk p.1) (Torus.mk p.2) := by
      unfold rTrunc
      refine le_min ?_ ?_
      · have := PairCorrAux.rTrunc_le_one a c
        unfold rTrunc at this
        linarith
      · have := PairCorrAux.rTrunc_le_dist a c
        unfold rTrunc at this
        have hm := hmem p hp
        linarith
    have hrpow : rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (-s) ≤ (rTrunc a c / 2) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hlow (by linarith)
    have hval : (rTrunc a c / 2) ^ (-s) = 2 ^ s * rTrunc a c ^ (-s) := by
      rw [Real.div_rpow hR.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    linarith
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ (lift2 ψ)) hf hbound
    hSconv hxS hyS
  have hnorm : ‖((B, C) : Euc d × Euc d) - (A, C)‖ = Torus.eucDist a b := by
    rw [Prod.mk_sub_mk, sub_self, Prod.norm_def]
    have h2 : B - A = -w := by rw [hB]; abel
    simp [h2, hwn, PairCorrAux.eucDist_nonneg' a b]
  rw [hnorm] at hmv
  have e1 := q84a_gradFst_eq hψ.smooth (hoff _ hxS)
  have e2 := q84a_gradFst_eq hψ.smooth (hoff _ hyS)
  simp only [hmA, hmC, hmB] at e1 e2
  rw [e1, e2, ← map_sub, LinearIsometryEquiv.norm_map, ← ContinuousLinearMap.sub_comp]
  refine (q84a_norm_comp_inl _).trans ?_
  rw [norm_sub_rev]
  exact hmv

end HRS.Q84a
