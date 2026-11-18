import HRS.MS.FlowBAux1
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# MS-FLOW-B, the integral multilinear operator

For `B : ℝ → E[×r]→L E` strongly measurable and bounded, `Vop T r B : X[×r]→L X`, `X = ℝ →ᵇ E`,
is `γ ↦ (t ↦ ∫_0^{clampT T t} B s (γ_1 s, …, γ_r s) ds)`.
-/

open MeasureTheory Filter Topology Set
open scoped BoundedContinuousFunction

namespace HRS.MS.FlowB

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Clamp to `[0,T]`. -/
def clampT (T t : ℝ) : ℝ := max 0 (min t T)

theorem continuous_clampT (T : ℝ) : Continuous (clampT T) := by
  unfold clampT; fun_prop

theorem clampT_nonneg (T t : ℝ) : 0 ≤ clampT T t := le_max_left _ _

theorem clampT_le (T t : ℝ) : clampT T t ≤ |T| :=
  max_le (abs_nonneg T) ((min_le_right _ _).trans (le_abs_self T))

theorem clampT_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampT T t ∈ Icc (0 : ℝ) T :=
  ⟨clampT_nonneg T t, max_le hT (min_le_right _ _)⟩

theorem clampT_of_mem {T t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : clampT T t = t := by
  unfold clampT
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- Integrands: locally integrable and bounded. -/
structure GoodInt (f : ℝ → E) : Prop where
  integrable : ∀ a b : ℝ, IntervalIntegrable f volume a b
  bdd : ∃ C, ∀ s, ‖f s‖ ≤ C

theorem GoodInt.of_sm {f : ℝ → E} (hm : StronglyMeasurable f) (C : ℝ) (hC : ∀ s, ‖f s‖ ≤ C) :
    GoodInt f where
  integrable a b := by
    refine (intervalIntegrable_const (c := C)).mono_fun' hm.aestronglyMeasurable ?_
    exact Eventually.of_forall hC
  bdd := ⟨C, hC⟩

theorem GoodInt.add {f g : ℝ → E} (hf : GoodInt f) (hg : GoodInt g) :
    GoodInt (fun s => f s + g s) where
  integrable a b := (hf.integrable a b).add (hg.integrable a b)
  bdd := by
    obtain ⟨C, hC⟩ := hf.bdd
    obtain ⟨D, hD⟩ := hg.bdd
    exact ⟨C + D, fun s => (norm_add_le _ _).trans (add_le_add (hC s) (hD s))⟩

theorem GoodInt.smul {f : ℝ → E} (hf : GoodInt f) (c : ℝ) : GoodInt (fun s => c • f s) where
  integrable a b := (hf.integrable a b).smul c
  bdd := by
    obtain ⟨C, hC⟩ := hf.bdd
    refine ⟨|c| * C, fun s => ?_⟩
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC s) (abs_nonneg c)

theorem GoodInt.sub {f g : ℝ → E} (hf : GoodInt f) (hg : GoodInt g) :
    GoodInt (fun s => f s - g s) := by
  have := hf.add (hg.smul (-1))
  simpa [sub_eq_add_neg] using this

open Classical in
/-- The primitive `t ↦ ∫_0^{clampT T t} f` as a bounded continuous function. -/
noncomputable def primC (T : ℝ) (f : ℝ → E) : ℝ →ᵇ E :=
  if h : GoodInt f then
    BoundedContinuousFunction.ofNormedAddCommGroup (fun t => ∫ s in (0 : ℝ)..clampT T t, f s)
      ((intervalIntegral.continuous_primitive h.integrable 0).comp (continuous_clampT T))
      (h.bdd.choose * |T|) (fun t => by
        refine (intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => h.bdd.choose_spec s)).trans ?_
        rw [sub_zero, abs_of_nonneg (clampT_nonneg T t)]
        have h0 : 0 ≤ h.bdd.choose := (norm_nonneg _).trans (h.bdd.choose_spec 0)
        exact mul_le_mul_of_nonneg_left (clampT_le T t) h0)
  else 0

theorem primC_apply {T : ℝ} {f : ℝ → E} (h : GoodInt f) (t : ℝ) :
    primC T f t = ∫ s in (0 : ℝ)..clampT T t, f s := by
  simp [primC, h]

theorem primC_add {T : ℝ} {f g : ℝ → E} (hf : GoodInt f) (hg : GoodInt g) :
    primC T (fun s => f s + g s) = primC T f + primC T g := by
  ext t
  simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
  rw [primC_apply (hf.add hg), primC_apply hf, primC_apply hg,
    intervalIntegral.integral_add (hf.integrable _ _) (hg.integrable _ _)]

theorem primC_smul {T : ℝ} {f : ℝ → E} (hf : GoodInt f) (c : ℝ) :
    primC T (fun s => c • f s) = c • primC T f := by
  ext t
  simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply]
  rw [primC_apply (hf.smul c), primC_apply hf, intervalIntegral.integral_smul]

/-- Multilinear maps `E^r → E`. -/
abbrev ML (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin r => E) E

/-- Admissible kernels. -/
structure HasB {r : ℕ} (B : ℝ → ML E r) : Prop where
  sm : StronglyMeasurable B
  bdd : ∃ c, ∀ s, ‖B s‖ ≤ c

theorem HasB.sub {r : ℕ} {B B' : ℝ → ML E r} (h : HasB B) (h' : HasB B') :
    HasB (fun s => B s - B' s) where
  sm := h.sm.sub h'.sm
  bdd := by
    obtain ⟨c, hc⟩ := h.bdd
    obtain ⟨c', hc'⟩ := h'.bdd
    exact ⟨c + c', fun s => (norm_sub_le _ _).trans (add_le_add (hc s) (hc' s))⟩

/-- The integrand `s ↦ B s (γ_1 s, …, γ_r s)`. -/
def intg (r : ℕ) (B : ℝ → ML E r) (γ : Fin r → ℝ →ᵇ E) (s : ℝ) : E := B s (fun i => γ i s)

theorem HasB.goodInt {r : ℕ} {B : ℝ → ML E r} (h : HasB B) (γ : Fin r → ℝ →ᵇ E) :
    GoodInt (intg r B γ) := by
  obtain ⟨c, hc⟩ := h.bdd
  have hsm : StronglyMeasurable (intg r B γ) := by
    have h1 : Continuous fun s : ℝ => (fun i => γ i s) := by fun_prop
    have h2 := h.sm.prodMk h1.stronglyMeasurable
    exact (continuous_eval : Continuous fun p : ML E r × (Fin r → E) => p.1 p.2).comp_stronglyMeasurable h2
  refine GoodInt.of_sm hsm (c * ∏ i, ‖γ i‖) fun s => ?_
  refine ((B s).le_opNorm _).trans ?_
  have h0 : 0 ≤ ∏ i, ‖γ i s‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  calc ‖B s‖ * ∏ i, ‖γ i s‖ ≤ c * ∏ i, ‖γ i s‖ := mul_le_mul_of_nonneg_right (hc s) h0
    _ ≤ c * ∏ i, ‖γ i‖ := by
      refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
        fun i _ => (γ i).norm_coe_le_norm s) ((norm_nonneg _).trans (hc s))

theorem intg_update_add {r : ℕ} [DecidableEq (Fin r)] (B : ℝ → ML E r) (γ : Fin r → ℝ →ᵇ E) (i : Fin r) (x y : ℝ →ᵇ E)
    (s : ℝ) : intg r B (Function.update γ i (x + y)) s =
      intg r B (Function.update γ i x) s + intg r B (Function.update γ i y) s := by
  have key : ∀ z : ℝ →ᵇ E, (fun j => (Function.update γ i z j) s) =
      Function.update (fun j => γ j s) i (z s) := by
    intro z; funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp only [intg, key]
  rw [show (x + y) s = x s + y s from rfl, (B s).map_update_add]

theorem intg_update_smul {r : ℕ} [DecidableEq (Fin r)] (B : ℝ → ML E r) (γ : Fin r → ℝ →ᵇ E) (i : Fin r) (c : ℝ)
    (x : ℝ →ᵇ E) (s : ℝ) : intg r B (Function.update γ i (c • x)) s =
      c • intg r B (Function.update γ i x) s := by
  have key : ∀ z : ℝ →ᵇ E, (fun j => (Function.update γ i z j) s) =
      Function.update (fun j => γ j s) i (z s) := by
    intro z; funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp only [intg, key]
  rw [show (c • x) s = c • x s from rfl, (B s).map_update_smul]

open Classical in
/-- The integral multilinear operator. -/
noncomputable def Vop (T : ℝ) (r : ℕ) (B : ℝ → ML E r) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => ℝ →ᵇ E) (ℝ →ᵇ E) :=
  if hB : HasB B then
    MultilinearMap.mkContinuous
      { toFun := fun γ => primC T (intg r B γ)
        map_update_add' := fun γ i x y => by
          have e : intg r B (Function.update γ i (x + y)) = fun s =>
              intg r B (Function.update γ i x) s + intg r B (Function.update γ i y) s :=
            funext (intg_update_add B γ i x y)
          rw [e]
          exact primC_add (hB.goodInt _) (hB.goodInt _)
        map_update_smul' := fun γ i c x => by
          have e : intg r B (Function.update γ i (c • x)) = fun s =>
              c • intg r B (Function.update γ i x) s :=
            funext (intg_update_smul B γ i c x)
          rw [e]
          exact primC_smul (hB.goodInt _) c }
      (hB.bdd.choose * |T|) (fun γ => by
        simp only [MultilinearMap.coe_mk]
        refine (BoundedContinuousFunction.norm_le ?_).2 fun t => ?_
        · exact mul_nonneg (mul_nonneg ((norm_nonneg _).trans (hB.bdd.choose_spec 0)) (abs_nonneg _))
            (Finset.prod_nonneg fun i _ => norm_nonneg _)
        · rw [primC_apply (hB.goodInt γ)]
          have hP : 0 ≤ ∏ i, ‖γ i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
          have hc0 : 0 ≤ hB.bdd.choose := (norm_nonneg _).trans (hB.bdd.choose_spec 0)
          refine (intervalIntegral.norm_integral_le_of_norm_le_const
            (C := hB.bdd.choose * ∏ i, ‖γ i‖) (fun s _ => ?_)).trans ?_
          · refine ((B s).le_opNorm _).trans ?_
            have h0 : 0 ≤ ∏ i, ‖γ i s‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
            calc ‖B s‖ * ∏ i, ‖γ i s‖ ≤ hB.bdd.choose * ∏ i, ‖γ i s‖ :=
                  mul_le_mul_of_nonneg_right (hB.bdd.choose_spec s) h0
              _ ≤ hB.bdd.choose * ∏ i, ‖γ i‖ := by
                refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
                  fun i _ => (γ i).norm_coe_le_norm s) hc0
          · rw [sub_zero, abs_of_nonneg (clampT_nonneg T t)]
            calc (hB.bdd.choose * ∏ i, ‖γ i‖) * clampT T t
                ≤ (hB.bdd.choose * ∏ i, ‖γ i‖) * |T| :=
                  mul_le_mul_of_nonneg_left (clampT_le T t) (mul_nonneg hc0 hP)
              _ = hB.bdd.choose * |T| * ∏ i, ‖γ i‖ := by ring)
  else 0

theorem Vop_apply {T : ℝ} {r : ℕ} {B : ℝ → ML E r} (hB : HasB B) (γ : Fin r → ℝ →ᵇ E) (t : ℝ) :
    Vop T r B γ t = ∫ s in (0 : ℝ)..clampT T t, B s (fun i => γ i s) := by
  simp only [Vop, hB, dite_true, MultilinearMap.coe_mkContinuous, MultilinearMap.coe_mk]
  rw [primC_apply (hB.goodInt γ)]
  rfl

theorem Vop_sub {T : ℝ} {r : ℕ} {B B' : ℝ → ML E r} (hB : HasB B) (hB' : HasB B') :
    Vop T r (fun s => B s - B' s) = Vop T r B - Vop T r B' := by
  ext γ t
  simp only [ContinuousMultilinearMap.sub_apply, BoundedContinuousFunction.coe_sub, Pi.sub_apply]
  rw [Vop_apply (hB.sub hB'), Vop_apply hB, Vop_apply hB']
  simp only [ContinuousMultilinearMap.sub_apply]
  exact intervalIntegral.integral_sub (f := fun s => B s (fun i => γ i s))
    (g := fun s => B' s (fun i => γ i s)) ((hB.goodInt γ).integrable _ _)
    ((hB'.goodInt γ).integrable _ _)

theorem norm_Vop_le {T : ℝ} (hT : 0 ≤ T) {r : ℕ} {B : ℝ → ML E r} (hB : HasB B) :
    ‖Vop T r B‖ ≤ ∫ s in (0 : ℝ)..T, ‖B s‖ := by
  have hint : IntervalIntegrable (fun s => ‖B s‖) volume 0 T := by
    obtain ⟨c, hc⟩ := hB.bdd
    exact (intervalIntegrable_const (c := c)).mono_fun' hB.sm.norm.aestronglyMeasurable
      (Eventually.of_forall fun s => by simpa using hc s)
  have hI : 0 ≤ ∫ s in (0 : ℝ)..T, ‖B s‖ :=
    intervalIntegral.integral_nonneg hT fun s _ => norm_nonneg _
  refine ContinuousMultilinearMap.opNorm_le_bound hI fun γ => ?_
  have hP : 0 ≤ ∏ i, ‖γ i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  refine (BoundedContinuousFunction.norm_le (mul_nonneg hI hP)).2 fun t => ?_
  rw [Vop_apply hB]
  have ht := clampT_nonneg T t
  have htT : clampT T t ≤ T := (clampT_mem hT t).2
  refine (intervalIntegral.norm_integral_le_integral_norm ht).trans ?_
  have hpt : ∀ s, ‖B s (fun i => γ i s)‖ ≤ ‖B s‖ * ∏ i, ‖γ i‖ := by
    intro s
    refine ((B s).le_opNorm _).trans ?_
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      fun i _ => (γ i).norm_coe_le_norm s) (norm_nonneg _)
  calc ∫ s in (0 : ℝ)..clampT T t, ‖B s (fun i => γ i s)‖
      ≤ ∫ s in (0 : ℝ)..clampT T t, ‖B s‖ * ∏ i, ‖γ i‖ := by
        refine intervalIntegral.integral_mono_on ht ?_ ?_ fun s _ => hpt s
        · exact (hB.goodInt γ).integrable _ _ |>.norm
        · exact (hint.mono_set (by
            rw [uIcc_of_le ht, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl htT)).mul_const _
    _ = (∫ s in (0 : ℝ)..clampT T t, ‖B s‖) * ∏ i, ‖γ i‖ := by
        rw [intervalIntegral.integral_mul_const]
    _ ≤ (∫ s in (0 : ℝ)..T, ‖B s‖) * ∏ i, ‖γ i‖ := by
        refine mul_le_mul_of_nonneg_right ?_ hP
        refine intervalIntegral.integral_mono_interval (le_refl _) ht htT
          (Eventually.of_forall fun s => norm_nonneg _) hint

theorem norm_curryLeft_apply_le {r : ℕ} (f : ML E (r + 1)) (v : E) :
    ‖f.curryLeft v‖ ≤ ‖f‖ * ‖v‖ := by
  have h : ‖f.curryLeft‖ = ‖f‖ :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => E) E).norm_map f
  rw [← h]
  exact f.curryLeft.le_opNorm v

theorem HasB.curryLeft {r : ℕ} {B : ℝ → ML E (r + 1)} (hB : HasB B) (γ : ℝ →ᵇ E) :
    HasB (fun s => (B s).curryLeft (γ s)) where
  sm := by
    have h1 : StronglyMeasurable fun s => (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (r + 1) => E) E) (B s) :=
      (LinearIsometryEquiv.continuous _).comp_stronglyMeasurable hB.sm
    exact (Continuous.clm_apply continuous_fst continuous_snd :
      Continuous fun p : (E →L[ℝ] ML E r) × E => p.1 p.2).comp_stronglyMeasurable
      (h1.prodMk γ.continuous.stronglyMeasurable)
  bdd := by
    obtain ⟨c, hc⟩ := hB.bdd
    refine ⟨c * ‖γ‖, fun s => ?_⟩
    refine (norm_curryLeft_apply_le _ _).trans ?_
    exact mul_le_mul (hc s) (γ.norm_coe_le_norm s) (norm_nonneg _)
      ((norm_nonneg _).trans (hc s))

/-- Currying: `(Vop (r+1) B).curryLeft γ = Vop r (s ↦ (B s).curryLeft (γ s))`. -/
theorem Vop_curryLeft {T : ℝ} {r : ℕ} {B : ℝ → ML E (r + 1)} (hB : HasB B) (γ : ℝ →ᵇ E) :
    (Vop T (r + 1) B).curryLeft γ = Vop T r (fun s => (B s).curryLeft (γ s)) := by
  ext δ t
  rw [ContinuousMultilinearMap.curryLeft_apply, Vop_apply hB, Vop_apply (hB.curryLeft γ)]
  congr 1
  funext s
  rw [ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

end HRS.MS.FlowB
