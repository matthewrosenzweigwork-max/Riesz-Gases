import HRS.Sections.Q17Aux3
import HRS.Sections.Q17Aux7

/-!
# Packet piG5 (PI-G5), abstract core: Riemann-Stieltjes integrals against a Lipschitz cumulative tensor path

Pure functional analysis (no dynamics).  For a normed space `B`, the contractions `Pj L` of `B`, a cumulative tensor path
`Jc : ℝ → TensorDual B 2` (with `Jc b - Jc a ∈ projTensor B 2`, Lipschitz) and continuous families of bilinear forms
`M, ML L` with `ML L → M` uniformly, the Riemann-Stieltjes integrals of `(Jc b - Jc a) (M τ)` and
`(tensorPow 2 (Pj L) (Jc b - Jc a)) (ML L τ)` exist, and the second converge to the first (`S7PIG5_core`).
Route: `measure_projection_proof` with `E = projTensor B 2`.  Also an elementary bound for Riemann-Stieltjes integrals.
Namespace `HRS.MC.Sec7.S7PIG5`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIG5

open HRS HRS.Sec7

/-- Congruence for Riemann-Stieltjes integrals: only the values for `0 ≤ a ≤ τ ≤ b ≤ T` matter. -/
theorem S7PIG5_rs_congr {T : ℝ} {S S' : ℝ → ℝ → ℝ → ℝ} {I : ℝ} (h : IsRS T S I)
    (hS : ∀ τ a b, 0 ≤ a → a ≤ τ → τ ≤ b → b ≤ T → S τ a b = S' τ a b) : IsRS T S' I := by
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := h ε hε
  refine ⟨δ, hδ, fun n u τ hu h0 hTl hτ hmesh => ?_⟩
  have hH := H n u τ hu h0 hTl hτ hmesh
  have hsum : ∑ i : Fin n, S' (τ i) (u i.castSucc) (u i.succ) = ∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have ha : 0 ≤ u i.castSucc := by
      have := hu.monotone (Fin.zero_le i.castSucc)
      rwa [h0] at this
    have hb : u i.succ ≤ T := by
      have := hu.monotone (Fin.le_last i.succ)
      rwa [hTl] at this
    exact (hS _ _ _ ha (hτ i).1 (hτ i).2 hb).symm
  rw [hsum]
  exact hH

/-- Elementary bound: if the Riemann-Stieltjes terms are bounded by `C (b - a)`, then `|I| ≤ C T`. -/
theorem S7PIG5_rs_bound {T : ℝ} (hT : 0 < T) {S : ℝ → ℝ → ℝ → ℝ} {I C : ℝ} (h : IsRS T S I)
    (hS : ∀ τ a b, 0 ≤ a → a ≤ τ → τ ≤ b → b ≤ T → |S τ a b| ≤ C * (b - a)) : |I| ≤ C * T := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨δ, hδ, H⟩ := h ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (T / δ)
  have hn0 : 0 < n := by
    have : 0 < T / δ := div_pos hT hδ
    exact_mod_cast this.trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hTn : T / n < δ := by
    rw [div_lt_iff₀ hnR]
    rw [div_lt_iff₀ hδ] at hn
    linarith
  set u : Fin (n + 1) → ℝ := fun i => (i : ℝ) * T / n with hu_def
  have hstep : ∀ i : Fin n, u i.succ - u i.castSucc = T / n := by
    intro i
    simp only [hu_def, Fin.val_succ, Fin.val_castSucc]
    push_cast
    field_simp
    ring
  have hu : StrictMono u := by
    refine Fin.strictMono_iff_lt_succ.2 (fun i => ?_)
    have := hstep i
    have h2 : 0 < T / n := div_pos hT hnR
    have h3 : u i.succ - u (Fin.castSucc i) = T / n := hstep i
    have : u i.castSucc < u i.succ := by linarith
    simpa using this
  have hu0 : u 0 = 0 := by simp [hu_def]
  have huT : u (Fin.last n) = T := by
    simp only [hu_def, Fin.val_last]
    field_simp
  have hτ : ∀ i : Fin n, u i.castSucc ≤ u i.castSucc ∧ u i.castSucc ≤ u i.succ :=
    fun i => ⟨le_rfl, (hu (Fin.castSucc_lt_succ)).le⟩
  have hmesh : ∀ i : Fin n, u i.succ - u i.castSucc < δ := fun i => by rw [hstep i]; exact hTn
  have hlt := H n u (fun i => u i.castSucc) hu hu0 huT hτ hmesh
  have hbnd : |∑ i : Fin n, S (u i.castSucc) (u i.castSucc) (u i.succ)| ≤ C * T := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ i : Fin n, |S (u i.castSucc) (u i.castSucc) (u i.succ)| ≤ C * (T / n) := by
      intro i
      have ha : 0 ≤ u i.castSucc := by
        have := hu.monotone (Fin.zero_le i.castSucc)
        rwa [hu0] at this
      have hb : u i.succ ≤ T := by
        have := hu.monotone (Fin.le_last i.succ)
        rwa [huT] at this
      have := hS _ _ _ ha le_rfl (hu (Fin.castSucc_lt_succ)).le hb
      rwa [hstep i] at this
    calc ∑ i : Fin n, |S (u i.castSucc) (u i.castSucc) (u i.succ)|
        ≤ ∑ _i : Fin n, C * (T / n) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = C * T := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have h1 : |I| ≤ |∑ i : Fin n, S (u i.castSucc) (u i.castSucc) (u i.succ)| +
      |∑ i : Fin n, S (u i.castSucc) (u i.castSucc) (u i.succ) - I| := by
    have := abs_sub_abs_le_abs_sub I (∑ i : Fin n, S (u i.castSucc) (u i.castSucc) (u i.succ))
    rw [abs_sub_comm] at this
    linarith [abs_sub_comm I (∑ i : Fin n, S (u i.castSucc) (u i.castSucc) (u i.succ))]
  linarith

section Core

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

set_option maxSynthPendingDepth 3 in
/-- `tensorPow j P` preserves the projective tensor power. -/
theorem S7PIG5_tensorPow_mem (j : ℕ) (P : B →L[ℝ] B) {v : TensorDual B j} (hv : v ∈ projTensor B j) :
    tensorPow j P v ∈ projTensor B j := by
  have hspan : Submodule.span ℝ (Set.range (elemTensor (B := B) (k := j))) ≤
      (projTensor B j).comap (tensorPow j P).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    show tensorPow j P (elemTensor w) ∈ projTensor B j
    rw [q17_tensorPow_elem]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, rfl⟩)
  have hcl : IsClosed (((projTensor B j).comap (tensorPow j P).toLinearMap : Submodule ℝ (TensorDual B j)) :
      Set (TensorDual B j)) := by
    rw [Submodule.comap_coe]
    exact (Submodule.isClosed_topologicalClosure _).preimage (tensorPow j P).continuous
  exact Submodule.topologicalClosure_minimal _ hspan hcl hv

set_option maxSynthPendingDepth 3 in
/-- Evaluation at a bilinear form, as a bounded linear map into the dual of `projTensor B 2`. -/
def S7PIG5_evL (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] : (B [×2]→L[ℝ] ℝ) →L[ℝ] (projTensor B 2 →L[ℝ] ℝ) :=
  (ContinuousLinearMap.precomp ℝ (projTensor B 2).subtypeL).comp (ContinuousLinearMap.apply ℝ ℝ)

theorem S7PIG5_evL_apply (M : B [×2]→L[ℝ] ℝ) (e : projTensor B 2) :
    S7PIG5_evL B M e = (e : TensorDual B 2) M := rfl

theorem S7PIG5_evL_norm (M : B [×2]→L[ℝ] ℝ) : ‖S7PIG5_evL B M‖ ≤ ‖M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun e => ?_)
  rw [S7PIG5_evL_apply]
  calc ‖(e : TensorDual B 2) M‖ ≤ ‖(e : TensorDual B 2)‖ * ‖M‖ := (e : TensorDual B 2).le_opNorm M
    _ = ‖M‖ * ‖e‖ := by rw [mul_comm]; rfl

set_option maxSynthPendingDepth 3 in
/-- The abstract core. -/
theorem S7PIG5_core (T : ℝ) (hT : 0 < T) (Pj : ℕ → (B →L[ℝ] B)) (hP1 : ∀ L, ‖Pj L‖ ≤ 1)
    (hTconv : ∀ v : TensorDual B 2, v ∈ projTensor B 2 →
      Tendsto (fun L => tensorPow 2 (Pj L) v) atTop (𝓝 v))
    (Jc : ℝ → TensorDual B 2) (K : ℝ) (hJc0 : Jc 0 = 0)
    (hmem : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → Jc b - Jc a ∈ projTensor B 2)
    (hLip : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → ‖Jc b - Jc a‖ ≤ K * (b - a))
    (M : ℝ → B [×2]→L[ℝ] ℝ) (ML : ℕ → ℝ → B [×2]→L[ℝ] ℝ)
    (hM : ContinuousOn M (Set.Icc 0 T)) (hML : ∀ L, ContinuousOn (ML L) (Set.Icc 0 T))
    (hMu : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ τ ∈ Set.Icc (0 : ℝ) T, ‖ML L τ - M τ‖ ≤ ε) :
    ∃ I : ℝ, IsRS T (fun τ a b => (Jc b - Jc a) (M τ)) I ∧
      ∃ IL : ℕ → ℝ, (∀ L, IsRS T (fun τ a b => tensorPow 2 (Pj L) (Jc b - Jc a) (ML L τ)) (IL L)) ∧
        Tendsto IL atTop (𝓝 I) := by
  have : CompleteSpace (projTensor B 2) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hK0 : 0 ≤ K := by
    have h := hLip 0 T le_rfl hT.le le_rfl
    have : 0 ≤ K * (T - 0) := (norm_nonneg _).trans h
    rw [sub_zero] at this
    exact nonneg_of_mul_nonneg_left this hT
  have hJm : ∀ s : ℝ, 0 ≤ s → s ≤ T → Jc s ∈ projTensor B 2 := fun s hs hsT => by
    have := hmem 0 s le_rfl hs hsT
    rwa [hJc0, sub_zero] at this
  let F : ℝ → projTensor B 2 := fun s =>
    ⟨Jc (Set.projIcc 0 T hT.le s), hJm _ (Set.projIcc 0 T hT.le s).2.1 (Set.projIcc 0 T hT.le s).2.2⟩
  have hFc : ∀ s ∈ Set.Icc (0 : ℝ) T, ((F s : projTensor B 2) : TensorDual B 2) = Jc s := by
    intro s hs
    show Jc (Set.projIcc 0 T hT.le s) = Jc s
    rw [Set.projIcc_of_mem hT.le hs]
  have hF0 : F 0 = 0 := by
    apply Subtype.ext
    rw [hFc 0 ⟨le_rfl, hT.le⟩]
    exact hJc0
  have hFd : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) T → b ∈ Set.Icc (0 : ℝ) T →
      (((F b - F a : projTensor B 2)) : TensorDual B 2) = Jc b - Jc a := by
    intro a b ha hb
    rw [Submodule.coe_sub, hFc a ha, hFc b hb]
  have hLipF : LipschitzOnWith K.toNNReal F (Set.Icc 0 T) := by
    refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal K hK0]
    have h1 : ‖F x - F y‖ = ‖Jc x - Jc y‖ := by
      rw [← hFd y x hy hx]; rfl
    rw [h1]
    rcases le_total x y with hxy | hxy
    · rw [norm_sub_rev, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ y - x)]
      exact hLip x y hx.1 hxy hy.2
    · rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x - y)]
      exact hLip y x hy.1 hxy hx.2
  have hid : BoundedVariationOn (fun x : ℝ => x) (Set.Icc 0 T) := by
    have h := (monotoneOn_id (s := Set.Icc (0 : ℝ) T)).locallyBoundedVariationOn 0 T
      ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩
    rwa [Set.inter_self] at h
  have hBV : BoundedVariationOn F (Set.Icc 0 T) :=
    hLipF.comp_boundedVariationOn (g := fun x : ℝ => x) (fun x hx => hx) hid
  let Pj' : ℕ → (projTensor B 2 →L[ℝ] projTensor B 2) := fun L =>
    ((tensorPow 2 (Pj L)).comp (projTensor B 2).subtypeL).codRestrict (projTensor B 2)
      (fun e => S7PIG5_tensorPow_mem 2 (Pj L) e.2)
  have hK : ∀ L, ‖Pj' L‖ ≤ 1 := by
    intro L
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun e => ?_)
    have h1 : ‖Pj' L e‖ = ‖tensorPow 2 (Pj L) (e : TensorDual B 2)‖ := rfl
    rw [h1, one_mul]
    calc ‖tensorPow 2 (Pj L) (e : TensorDual B 2)‖ ≤ ‖tensorPow 2 (Pj L)‖ * ‖(e : TensorDual B 2)‖ :=
          (tensorPow 2 (Pj L)).le_opNorm _
      _ ≤ 1 * ‖(e : TensorDual B 2)‖ :=
          mul_le_mul_of_nonneg_right (q17_precomp_norm 2 (Pj L) (hP1 L)) (norm_nonneg _)
      _ = ‖e‖ := by rw [one_mul]; rfl
  have hconv' : ∀ e : projTensor B 2, Tendsto (fun L => Pj' L e) atTop (𝓝 e) := fun e =>
    tendsto_subtype_rng.2 (hTconv e e.2)
  have hA : ContinuousOn (fun τ => S7PIG5_evL B (M τ)) (Set.Icc 0 T) :=
    (S7PIG5_evL B).continuous.comp_continuousOn hM
  have hAL : ∀ L, ContinuousOn (fun τ => S7PIG5_evL B (ML L τ)) (Set.Icc 0 T) := fun L =>
    (S7PIG5_evL B).continuous.comp_continuousOn (hML L)
  have hAu : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ u ∈ Set.Icc (0 : ℝ) T,
      ‖S7PIG5_evL B (ML L u) - S7PIG5_evL B (M u)‖ ≤ ε := by
    intro ε hε
    obtain ⟨L₀, hL₀⟩ := hMu ε hε
    refine ⟨L₀, fun L hL u hu => ?_⟩
    rw [← map_sub]
    exact (S7PIG5_evL_norm _).trans (hL₀ L hL u hu)
  obtain ⟨I, hI, IL, hIL, hlim⟩ := measure_projection_proof Pj' 1 hK hconv' T hT F hBV hF0
    (fun τ => S7PIG5_evL B (M τ)) (fun L τ => S7PIG5_evL B (ML L τ)) hA hAL hAu
  refine ⟨I, S7PIG5_rs_congr hI ?_, IL, fun L => S7PIG5_rs_congr (hIL L) ?_, hlim⟩
  · intro τ a b ha haτ hτb hbT
    have hb : b ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans (haτ.trans hτb), hbT⟩
    have ha' : a ∈ Set.Icc (0 : ℝ) T := ⟨ha, (haτ.trans hτb).trans hbT⟩
    show (S7PIG5_evL B (M τ)) (F b - F a) = (Jc b - Jc a) (M τ)
    rw [S7PIG5_evL_apply, hFd a b ha' hb]
  · intro τ a b ha haτ hτb hbT
    have hb : b ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans (haτ.trans hτb), hbT⟩
    have ha' : a ∈ Set.Icc (0 : ℝ) T := ⟨ha, (haτ.trans hτb).trans hbT⟩
    show (S7PIG5_evL B (ML L τ)) (Pj' L (F b - F a)) = tensorPow 2 (Pj L) (Jc b - Jc a) (ML L τ)
    rw [S7PIG5_evL_apply]
    show tensorPow 2 (Pj L) (((F b - F a : projTensor B 2)) : TensorDual B 2) (ML L τ) = _
    rw [hFd a b ha' hb]

end Core

end HRS.MC.Sec7.S7PIG5

end
