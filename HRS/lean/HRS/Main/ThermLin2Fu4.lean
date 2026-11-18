import HRS.Main.ThermLin2Fu3

/-!
# THERMLIN2 Fu4: the vectors `a_σ`, `w(r,σ)` of the variance computation, their measurability, bounds and the weak identity
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c HRS.Uniform.Q45 Classical

variable {d : ℕ}

theorem tl2fu_pb_inner {m : ℝ} (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (t σ : ℝ)
    (ℓ : NegSobolev d m →L[ℝ] ℝ) (x : NegSobolev d m) :
    inner ℝ (pullbackVec (HRS.Uniform.Comp28.plainData V) t σ ℓ) x = ℓ (V t σ x) := by
  rw [pullback_inner]; rfl

/-- `a_σ = V^*(t,σ)ℓ_φ - W^*(t,σ)ℓ_φ` on `[0,t]` (zero elsewhere). -/
def tl2fuA {m : ℝ} (Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (t : ℝ) (φ : Torus d → ℝ)
    (σ : ℝ) : NegSobolev d m :=
  if σ ∈ Set.Icc (0 : ℝ) t then
    pullbackVec (HRS.Uniform.Comp28.plainData Vev) t σ (gfb4_ell m φ) -
      pullbackVec (HRS.Uniform.Comp28.plainData Wev) t σ (gfb4_ell m φ)
  else 0

/-- `w(r,σ) = W^*(r,σ)ℓ_{ψ_r}` for `0 ≤ σ ≤ r ≤ t` (zero elsewhere); the argument is the pair `(r,σ)`. -/
def tl2fuW {m : ℝ} (Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (t : ℝ) (ψ : ℝ → Torus d → ℝ)
    (p : ℝ × ℝ) : NegSobolev d m :=
  if 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ t then
    pullbackVec (HRS.Uniform.Comp28.plainData Wev) p.1 p.2 (gfb4_ell m (ψ p.1))
  else 0

/-- The test-function data of `tl2_dyson_fubini`. -/
structure Tl2FuTest {m : ℝ} (Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (t : ℝ)
    (φ : Torus d → ℝ) (ψ : ℝ → Torus d → ℝ) (B : ℝ) : Prop where
  hφ : MemSobolev m φ
  hψm : ∀ r ∈ Set.Icc (0 : ℝ) t, MemSobolev m (ψ r)
  hψB : ∀ r ∈ Set.Icc (0 : ℝ) t, ‖lpFun m (ψ r)‖ ≤ B
  hψmeas : Measurable fun r => lpFun m (ψ r)
  hweak : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ z : NegSobolev d m,
    NegSobolev.eval (Vev t σ z) φ - NegSobolev.eval (Wev t σ z) φ =
      ∫ r in σ..t, NegSobolev.eval (Wev r σ z) (ψ r)

section Facts

variable {m T' K : ℝ} {Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
  {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
  {G : ℝ → Ω → NegSobolev d m} {Cd : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ}
  {Zs Zw : ℝ → Ω → NegSobolev d m} {t : ℝ} {φ : Torus d → ℝ} {ψ : ℝ → Torus d → ℝ} {B : ℝ}

theorem tl2fu_meas_pb (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hVc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T'})
    (ht : t ∈ Set.Icc (0 : ℝ) T') (ℓ : NegSobolev d m →L[ℝ] ℝ) :
    Measurable (fun σ : ℝ => if σ ∈ Set.Icc (0 : ℝ) t then
      pullbackVec (HRS.Uniform.Comp28.plainData V) t σ ℓ else 0) := by
  refine gfb4_measurable_of_weak fun x => ?_
  have : (fun σ : ℝ => inner ℝ (if σ ∈ Set.Icc (0 : ℝ) t then
      pullbackVec (HRS.Uniform.Comp28.plainData V) t σ ℓ else 0) x) =
      Set.piecewise (Set.Icc (0 : ℝ) t) (fun σ => ℓ (V t σ x)) (fun _ => 0) := by
    funext σ
    by_cases h : σ ∈ Set.Icc (0 : ℝ) t
    · simp [Set.piecewise, h, tl2fu_pb_inner]
    · simp [Set.piecewise, h]
  rw [this]
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_Icc
  have := t25p_pullback_weak V hVc ht ℓ x
  refine this.congr fun σ _ => ?_
  exact (tl2fu_pb_inner V t σ ℓ x).symm

theorem tl2fu_A_meas (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) (ht : t ∈ Set.Icc (0 : ℝ) T')
    (φ : Torus d → ℝ) : Measurable (tl2fuA Vev Wev t φ) := by
  have h1 := tl2fu_meas_pb (T' := T') Vev D.hVc ht (gfb4_ell m φ)
  have h2 := tl2fu_meas_pb (T' := T') Wev D.hWc ht (gfb4_ell m φ)
  have e : tl2fuA Vev Wev t φ = fun σ => (if σ ∈ Set.Icc (0 : ℝ) t then
      pullbackVec (HRS.Uniform.Comp28.plainData Vev) t σ (gfb4_ell m φ) else 0) -
      (if σ ∈ Set.Icc (0 : ℝ) t then
      pullbackVec (HRS.Uniform.Comp28.plainData Wev) t σ (gfb4_ell m φ) else 0) := by
    funext σ
    by_cases h : σ ∈ Set.Icc (0 : ℝ) t <;> simp [tl2fuA, h]
  rw [e]
  exact h1.sub h2

theorem tl2fu_A_bound (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) (ht : t ∈ Set.Icc (0 : ℝ) T')
    (φ : Torus d → ℝ) {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) t) :
    ‖tl2fuA Vev Wev t φ σ‖ ≤ 2 * K * ‖gfb4_ell m φ‖ := by
  simp only [tl2fuA, if_pos hσ]
  have h1 := t25p_norm_pullback_le Vev D.hVb D.hK hσ.1 hσ.2 ht.2 (gfb4_ell m φ)
  have h2 := t25p_norm_pullback_le Wev D.hWb D.hK hσ.1 hσ.2 ht.2 (gfb4_ell m φ)
  calc _ ≤ ‖pullbackVec (HRS.Uniform.Comp28.plainData Vev) t σ (gfb4_ell m φ)‖ +
        ‖pullbackVec (HRS.Uniform.Comp28.plainData Wev) t σ (gfb4_ell m φ)‖ := norm_sub_le _ _
    _ ≤ K * ‖gfb4_ell m φ‖ + K * ‖gfb4_ell m φ‖ := add_le_add h1 h2
    _ = _ := by ring

theorem tl2fu_W_meas (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) (ht : t ∈ Set.Icc (0 : ℝ) T')
    (E : Tl2FuTest Vev Wev t φ ψ B) : Measurable (tl2fuW Wev t ψ) := by
  refine gfb4_measurable_of_weak fun x => ?_
  set Tri : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ t} with hTri
  have hTrim : MeasurableSet Tri :=
    (measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_fst).inter (measurableSet_le measurable_fst measurable_const))
  set h : ℝ × ℝ → NegSobolev d m := Tri.piecewise (fun p => Wev p.1 p.2 x) (fun _ => 0) with hh
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Wev p.1 p.2 x) Tri := by
    refine (D.hWc x).mono ?_
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans ht.2⟩
  have hhm : Measurable h := ContinuousOn.measurable_piecewise hcont continuousOn_const hTrim
  have e : (fun p : ℝ × ℝ => inner ℝ (tl2fuW Wev t ψ p) x) =
      fun p => inner ℝ (lpFun m (ψ p.1)) (h p) := by
    funext p
    by_cases hp : p ∈ Tri
    · have hp' : 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ t := hp
      simp only [tl2fuW, if_pos hp', hh, Set.piecewise_eq_of_mem _ _ _ hp, tl2fu_pb_inner, gfb4_ell,
        innerSL_apply_apply]
    · have hp' : ¬ (0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ t) := hp
      simp only [tl2fuW, if_neg hp', hh, Set.piecewise_eq_of_notMem _ _ _ hp, inner_zero_left, inner_zero_right]
  rw [e]
  exact (E.hψmeas.comp measurable_fst).inner hhm

theorem tl2fu_W_bound (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) (ht : t ∈ Set.Icc (0 : ℝ) T')
    (E : Tl2FuTest Vev Wev t φ ψ B) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) r) :
    ‖tl2fuW Wev t ψ (r, σ)‖ ≤ K * B := by
  have hcond : 0 ≤ σ ∧ σ ≤ r ∧ r ≤ t := ⟨hσ.1, hσ.2, hr.2⟩
  simp only [tl2fuW, if_pos hcond]
  have h1 := t25p_norm_pullback_le Wev D.hWb D.hK hσ.1 hσ.2 (hr.2.trans ht.2) (gfb4_ell m (ψ r))
  have h2 : ‖gfb4_ell m (ψ r)‖ ≤ B := by
    unfold gfb4_ell; rw [innerSL_apply_norm]; exact E.hψB r hr
  exact h1.trans (mul_le_mul_of_nonneg_left h2 D.hK)

theorem tl2fu_weak (E : Tl2FuTest Vev Wev t φ ψ B) {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) t)
    (l : NegSobolev d m →L[ℝ] ℝ) :
    l (tl2fuA Vev Wev t φ σ) = ∫ r in σ..t, l (tl2fuW Wev t ψ (r, σ)) := by
  set z := (InnerProductSpace.toDual ℝ (NegSobolev d m)).symm l with hz
  have hl : ∀ x, l x = inner ℝ x z := fun x => by
    rw [real_inner_comm, hz, InnerProductSpace.toDual_symm_apply]
  rw [hl, show tl2fuA Vev Wev t φ σ = pullbackVec (HRS.Uniform.Comp28.plainData Vev) t σ (gfb4_ell m φ) -
      pullbackVec (HRS.Uniform.Comp28.plainData Wev) t σ (gfb4_ell m φ) by simp [tl2fuA, hσ],
    inner_sub_left, tl2fu_pb_inner, tl2fu_pb_inner, gfb4_ell_apply E.hφ, gfb4_ell_apply E.hφ, E.hweak σ hσ z]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [Set.uIcc_of_le hσ.2] at hr
  have hrI : r ∈ Set.Icc (0 : ℝ) t := ⟨hσ.1.trans hr.1, hr.2⟩
  have hcond : 0 ≤ σ ∧ σ ≤ r ∧ r ≤ t := ⟨hσ.1, hr.1, hr.2⟩
  simp only [tl2fuW, hcond, and_self, ↓reduceIte]
  rw [hl, tl2fu_pb_inner, gfb4_ell_apply (E.hψm r hrI)]

end Facts

end HRS.ThermLin.Plan2
