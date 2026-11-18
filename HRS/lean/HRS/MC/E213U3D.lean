import HRS.MC.E213U3C
import HRS.MC.E213O1
import HRS.MC.E213D
import HRS.MC.E213G
import HRS.MC.E213F
import HRS.MC.L2C0

/-!
# Packet E213U3, part D: window infrastructure

`tensorPow'` on `prodForm`, preservation of `projTensor`, the generalised restriction `shiftRestr`
(`w ↦ w(s + ·)`), the evaluation CLM `evAt`, the propagation CLM `Θ` (existence form), the window evaluation
predicate `SJW` (transfer from `SJ`, union, uniqueness), translation of set integrals, and the shift identity of
the series `Fser`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U3

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDS HRS.MC.E213O

set_option maxSynthPendingDepth 3

variable {d : ℕ}

/-! ### `tensorPow'` and `prodForm` -/

theorem u3_tp_prodForm {B B' : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup B'] [NormedSpace ℝ B'] (P : B →L[ℝ] B') (J : TensorDual B 2)
    (l₁ l₂ : StrongDual ℝ B') :
    tensorPow' 2 P J (prodForm l₁ l₂) = J (prodForm (l₁.comp P) (l₂.comp P)) := by
  rw [tensorPow'_apply]
  congr 1

theorem u3_tp_mem {B B' : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup B'] [NormedSpace ℝ B'] (P : B →L[ℝ] B') {J : TensorDual B 2}
    (hJ : J ∈ projTensor B 2) : tensorPow' 2 P J ∈ projTensor B' 2 :=
  HRS.MC.E213T.e213t_map_projTensor_le (tensorPow' 2 P) (fun v => by
    rw [tensorPow'_elem]; exact HRS.MC.E213T.elemTensor_mem_projTensor _) J hJ

/-! ### The generalised window restriction and evaluation -/

/-- The point `s + t ∈ [0, G]` for `t ∈ [0,T]`. -/
def u3_tmap {T G : ℝ} (s : ℝ) (hs : 0 ≤ s) (hsG : s + T ≤ G) (t : Set.Icc (0 : ℝ) T) :
    Set.Icc (0 : ℝ) G :=
  ⟨s + t.1, by linarith [t.2.1], by linarith [t.2.2]⟩

theorem u3_tmap_cont {T G : ℝ} (s : ℝ) (hs : 0 ≤ s) (hsG : s + T ≤ G) :
    Continuous (u3_tmap (T := T) (G := G) s hs hsG) := by
  unfold u3_tmap
  exact Continuous.subtype_mk (by fun_prop) _

/-- `shiftRestr s : 𝒳_{m,G} →L 𝒳_{m,T}`, `w ↦ (t ↦ w(s + t))`, for `0 ≤ s`, `s + T ≤ G`. -/
def shiftRestr (m T G s : ℝ) (hs : 0 ≤ s) (hsG : s + T ≤ G) :
    PathSpace d m G →L[ℝ] PathSpace d m T :=
  LinearMap.mkContinuous
    { toFun := fun w => (show C(Set.Icc (0 : ℝ) G, NegSobolev d m) from w).comp
        ⟨u3_tmap s hs hsG, u3_tmap_cont s hs hsG⟩
      map_add' := fun w w' => e213o_ext (fun t => rfl)
      map_smul' := fun c w => e213o_ext (fun t => rfl) } 1 (fun w => by
    rw [one_mul]
    refine ContinuousMap.norm_le _ (norm_nonneg _) |>.2 (fun t => ?_)
    exact ContinuousMap.norm_coe_le_norm
      (show C(Set.Icc (0 : ℝ) G, NegSobolev d m) from w) (u3_tmap s hs hsG t))

theorem shiftRestr_norm_le (m T G s : ℝ) (hs : 0 ≤ s) (hsG : s + T ≤ G) :
    ‖shiftRestr (d := d) m T G s hs hsG‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem shiftRestr_pathAt (m T G s : ℝ) (hs : 0 ≤ s) (hsG : s + T ≤ G) (w : PathSpace d m G) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) : pathAt (shiftRestr m T G s hs hsG w) t = pathAt w (s + t) := by
  have h2 : s + t ∈ Set.Icc (0 : ℝ) G := (u3_tmap s hs hsG ⟨t, ht⟩).2
  unfold pathAt
  rw [dif_pos ht, dif_pos h2]
  rfl

/-- Evaluation of a path at a time `t ∈ [0,G]`. -/
def evAt (m G t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) G) : PathSpace d m G →L[ℝ] NegSobolev d m :=
  LinearMap.mkContinuous
    { toFun := fun w => (show C(Set.Icc (0 : ℝ) G, NegSobolev d m) from w) ⟨t, ht⟩
      map_add' := fun w w' => rfl
      map_smul' := fun c w => rfl } 1 (fun w => by
    rw [one_mul]
    exact ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) G, NegSobolev d m) from w) ⟨t, ht⟩)

theorem evAt_norm_le (m G t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) G) : ‖evAt (d := d) m G t ht‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem evAt_apply (m G t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) G) (w : PathSpace d m G) :
    evAt m G t ht w = pathAt w t := by
  unfold pathAt
  rw [dif_pos ht]
  rfl

/-- Existence of the propagation operator `Θ : E_m →L 𝒳_{m,T}`, `x ↦ (t ↦ V(a+t, s) x)`. -/
theorem u3_theta_exists (m T a s : ℝ) (hT : 0 ≤ T) (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (K : ℝ) (hcont : ∀ x : NegSobolev d m, Continuous fun t : Set.Icc (0 : ℝ) T => V (a + t) s x)
    (hK : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖V (a + t) s‖ ≤ K) :
    ∃ Θ : NegSobolev d m →L[ℝ] PathSpace d m T,
      (∀ x t, t ∈ Set.Icc (0 : ℝ) T → pathAt (Θ x) t = V (a + t) s x) ∧ ‖Θ‖ ≤ K := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, hT⟩)
  let L : NegSobolev d m →ₗ[ℝ] PathSpace d m T :=
    { toFun := fun x => (⟨fun t : Set.Icc (0 : ℝ) T => V (a + t) s x, hcont x⟩ :
        C(Set.Icc (0 : ℝ) T, NegSobolev d m))
      map_add' := fun x y => e213o_ext (fun t => by
        show V (a + t) s (x + y) = V (a + t) s x + V (a + t) s y
        rw [map_add])
      map_smul' := fun c x => e213o_ext (fun t => by
        show V (a + t) s (c • x) = c • V (a + t) s x
        rw [map_smul]) }
  refine ⟨LinearMap.mkContinuous L K (fun x => ?_), ?_, LinearMap.mkContinuous_norm_le _ hK0 _⟩
  · refine ContinuousMap.norm_le _ (by positivity) |>.2 (fun t => ?_)
    show ‖V (a + t) s x‖ ≤ K * ‖x‖
    exact ((V (a + t) s).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hK t t.2) (norm_nonneg _))
  · intro x t ht
    unfold pathAt
    rw [dif_pos ht]
    rfl

/-! ### Translation of set integrals -/

theorem u3_setIntegral_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : ℝ) (f : ℝ → E)
    (S : Set ℝ) : ∫ v in (fun x => b + x) ⁻¹' S, f (b + v) = ∫ u in S, f u :=
  (measurePreserving_add_left volume b).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft b).measurableEmbedding f S

/-! ### The window evaluation predicate -/

/-- The evaluation predicate of the window tensor (series form): observation times `a + t_i`. -/
def SJW (R : Regime d) (r m T a : ℝ) (z : ℝ → NegSobolev d r) (I : Set ℝ)
    (X : TensorDual (PathSpace d m T) 2) : Prop :=
  X ∈ projTensor (PathSpace d m T) 2 ∧
  ∀ (ta tb : ℝ) (φa φb : Torus d → ℝ) (l₁ l₂ : StrongDual ℝ (PathSpace d m T)),
    Torus.IsSmooth φa → Torus.IsSmooth φb → ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
    (∀ w, l₁ w = NegSobolev.eval (pathAt w ta) φa) → (∀ w, l₂ w = NegSobolev.eval (pathAt w tb) φb) →
    X (prodForm l₁ l₂) = 2 * R.D.invβ *
      ∫ u in I ∩ Set.Icc 0 (min (a + ta) (a + tb)), Fser R r m z (a + ta) (a + tb) φa φb u

/-- Transfer from the horizon `a + T` tensor to the window. -/
theorem u3_SJ_toSJW (R : Regime d) (r m T a : ℝ) (ha : 0 ≤ a) {z : ℝ → NegSobolev d r} {I : Set ℝ}
    {J : TensorDual (PathSpace d m (a + T)) 2} (h : SJ R r m (a + T) z I J) :
    SJW R r m T a z I (tensorPow' 2 (winRestr a ha) J) := by
  refine ⟨u3_tp_mem _ h.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [u3_tp_prodForm]
  have hta' : a + ta ∈ Set.Icc (0 : ℝ) (a + T) := ⟨by linarith [hta.1], by linarith [hta.2]⟩
  have htb' : a + tb ∈ Set.Icc (0 : ℝ) (a + T) := ⟨by linarith [htb.1], by linarith [htb.2]⟩
  exact h.2 (a + ta) (a + tb) φa φb _ _ hφa hφb hta' htb'
    (fun w => by
      show l₁ (winRestr a ha w) = _
      rw [hl₁, winRestr_pathAt a ha w hta])
    (fun w => by
      show l₂ (winRestr a ha w) = _
      rw [hl₂, winRestr_pathAt a ha w htb])

theorem u3_SJW_unique (R : Regime d) (r m T a : ℝ) {z : ℝ → NegSobolev d r} {I : Set ℝ}
    {X Y : TensorDual (PathSpace d m T) 2} (hX : SJW R r m T a z I X) (hY : SJW R r m T a z I Y) :
    X = Y := by
  refine u3_eq_of_eval R m T hX.1 hY.1 ?_
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [hX.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂, hY.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]

theorem u3_SJW_empty (R : Regime d) (r m T a : ℝ) (z : ℝ → NegSobolev d r) :
    SJW R r m T a z ∅ 0 := by
  refine ⟨Submodule.zero_mem _, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  simp

theorem u3_SJW_union (R : Regime d) (r m T a : ℝ) (ha : 0 ≤ a) {z : ℝ → NegSobolev d r} {I₁ I₂ : Set ℝ}
    (hd : Disjoint I₁ I₂) (h₂m : MeasurableSet I₂) {X₁ X₂ : TensorDual (PathSpace d m T) 2}
    (h₁ : SJW R r m T a z I₁ X₁) (h₂ : SJW R r m T a z I₂ X₂)
    (i₁ : IntOK R r m (a + T) z I₁) (i₂ : IntOK R r m (a + T) z I₂) :
    SJW R r m T a z (I₁ ∪ I₂) (X₁ + X₂) := by
  refine ⟨Submodule.add_mem (projTensor (PathSpace d m T) 2) h₁.1 h₂.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  have hta' : a + ta ∈ Set.Icc (0 : ℝ) (a + T) := ⟨by linarith [hta.1], by linarith [hta.2]⟩
  have htb' : a + tb ∈ Set.Icc (0 : ℝ) (a + T) := ⟨by linarith [htb.1], by linarith [htb.2]⟩
  rw [add_apply, h₁.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂,
    h₂.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂, ← mul_add, Set.union_inter_distrib_right,
    setIntegral_union (hd.mono Set.inter_subset_left Set.inter_subset_left)
      (h₂m.inter measurableSet_Icc) (i₁ _ _ φa φb hφa hφb hta' htb') (i₂ _ _ φa φb hφa hφb hta' htb')]

/-! ### Shift identity for the series -/

/-- `V` of the shifted regime. -/
theorem u3_vprop_shift (R : Regime d) (m b : ℝ) (hb : 0 ≤ b) {t u : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) :
    Vprop R.D (HRS.MC.E213F.shift R b hb).ρ m t u = Vprop R.D R.ρ m (b + t) (b + u) := by
  obtain ⟨Rg, MB, Λ, VB, ν₀, hbun⟩ := HRS.MC.E213F.adjointData_uniform R (PDE.mStar d)
  have hG : 0 < max t 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hA := hbun (b + max t 1) (by positivity) 0 le_rfl
  have hB := hbun (max t 1) hG b hb
  have hρ : (fun t => R.ρ (0 + t)) = R.ρ := funext fun t => by simp
  rw [hρ] at hA
  have hm1 : 1 ≤ PDE.mStar d := by unfold PDE.mStar; omega
  exact HRS.MC.E213G.vprop_shift R.hd hb hA hB le_rfl hm1 m hu hut (le_max_left _ _)

theorem u3_Fser_shift (R : Regime d) (r m b : ℝ) (hb : 0 ≤ b) (z : ℝ → NegSobolev d r) (ta tb : ℝ)
    (φa φb : Torus d → ℝ) {v : ℝ} (hv : 0 ≤ v) (hva : v ≤ ta) (hvb : v ≤ tb) :
    Fser (HRS.MC.E213F.shift R b hb) r m (fun v => z (b + v)) ta tb φa φb v =
      Fser R r m z (b + ta) (b + tb) φa φb (b + v) := by
  unfold Fser Fterm
  refine tsum_congr fun pr => ?_
  have e1 := u3_vprop_shift R m b hb hv hva
  have e2 := u3_vprop_shift R m b hb hv hvb
  have e3 : (HRS.MC.E213F.shift R b hb).D = R.D := rfl
  rw [e3, e1, e2]

end HRS.MC.E213U3

end
