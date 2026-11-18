import HRS.MS.SA16TransferT5

/-!
# S.A.16 T4: `bounded_ode_energy`

Existence of the integral solution of `v' = A v + f` (bounded strongly measurable `A`, `L¹` forcing) by the
Neumann series `v = ∑ vₙ`, `v₀ t = x₀ + ∫₀ᵗ f`, `vₙ₊₁ t = ∫₀ᵗ A (vₙ)`, and the energy bound by
`mild_energy_by_splitting` for the trivial propagator `S ≡ id`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Transfer
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16Evolution

section T4
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- continuity of the primitive on `[0,T]` -/
lemma sa16x_prim_cont {T : ℝ} (hT : 0 ≤ T) {g : ℝ → X} (hg : IntegrableOn g (Icc (0 : ℝ) T)) :
    ContinuousOn (fun t => ∫ r in Icc (0 : ℝ) t, g r) (Icc (0 : ℝ) T) := by
  have h := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T) (μ := volume)
    (f := g) (by rwa [uIcc_of_le hT])
  rw [uIcc_of_le hT] at h
  exact h.congr (fun t ht => by
    show _ = ∫ r in (0 : ℝ)..t, g r
    rw [intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc])

/-- existence of the integral solution of the bounded Volterra equation -/
lemma sa16x_ode_exists {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K) (A : ℝ → X →L[ℝ] X)
    (hA : ∀ x, AEStronglyMeasurable (fun r => A r x) (volume.restrict (Icc (0 : ℝ) T)))
    (hAb : ∀ r ∈ Icc (0 : ℝ) T, ‖A r‖ ≤ K) (f : ℝ → X) (hf : IntegrableOn f (Icc (0 : ℝ) T))
    (x₀ : X) :
    ∃ v : ℝ → X, ContinuousOn v (Icc (0 : ℝ) T) ∧
      ∀ t ∈ Icc (0 : ℝ) T, v t = x₀ + ∫ r in Icc (0 : ℝ) t, (A r (v r) + f r) := by
  classical
  set I : Set ℝ := Icc (0 : ℝ) T with hI
  set a : ℝ := ‖x₀‖ + ∫ r in I, ‖f r‖ with ha
  have hfn : 0 ≤ ∫ r in I, ‖f r‖ := setIntegral_nonneg measurableSet_Icc fun r _ => norm_nonneg _
  have ha0 : 0 ≤ a := add_nonneg (norm_nonneg _) hfn
  let v : ℕ → ℝ → X := fun n => Nat.rec (motive := fun _ => ℝ → X)
    (fun t => x₀ + ∫ r in Icc (0 : ℝ) t, f r)
    (fun _ vn t => ∫ r in Icc (0 : ℝ) t, A r (vn r)) n
  have hv0 : v 0 = fun t => x₀ + ∫ r in Icc (0 : ℝ) t, f r := rfl
  have hvs : ∀ n, v (n + 1) = fun t => ∫ r in Icc (0 : ℝ) t, A r (v n r) := fun n => rfl
  have key : ∀ n : ℕ, ContinuousOn (v n) I ∧
      ∀ t ∈ I, ‖v n t‖ ≤ a * (K * t) ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, fun t ht => ?_⟩
      · rw [hv0]
        exact continuousOn_const.add (sa16x_prim_cont hT hf)
      · rw [hv0]
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
        refine (norm_add_le _ _).trans ?_
        have h1 : ‖∫ r in Icc (0 : ℝ) t, f r‖ ≤ ∫ r in Icc (0 : ℝ) t, ‖f r‖ :=
          norm_integral_le_integral_norm _
        have h2 : ∫ r in Icc (0 : ℝ) t, ‖f r‖ ≤ ∫ r in I, ‖f r‖ :=
          setIntegral_mono_set hf.norm (Eventually.of_forall fun r => norm_nonneg _)
            (Icc_subset_Icc le_rfl ht.2).eventuallyLE
        simp only [ha]
        linarith
    | succ n ih =>
      obtain ⟨hc, hb⟩ := ih
      have hv_aesm : AEStronglyMeasurable (v n) (volume.restrict I) :=
        hc.aestronglyMeasurable measurableSet_Icc
      have hg_aesm : AEStronglyMeasurable (fun r => A r (v n r)) (volume.restrict I) :=
        sa16e_aesm_apply A hA hv_aesm
      obtain ⟨Cn, hCn⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
      have hgb : ∀ r ∈ I, ‖A r (v n r)‖ ≤ K * Cn := fun r hr =>
        ((A r).le_opNorm _).trans (mul_le_mul (hAb r hr) (hCn r hr) (norm_nonneg _) hK)
      have hgint : IntegrableOn (fun r => A r (v n r)) I :=
        Integrable.mono' (integrable_const (K * Cn)) hg_aesm
          ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hgb))
      rw [hvs n]
      refine ⟨sa16x_prim_cont hT hgint, fun t ht => ?_⟩
      have hbd : ∀ r ∈ Icc (0 : ℝ) t, ‖A r (v n r)‖ ≤
          K * (a * (K * r) ^ n / (n.factorial : ℝ)) := by
        intro r hr
        have hrI : r ∈ I := ⟨hr.1, hr.2.trans ht.2⟩
        exact ((A r).le_opNorm _).trans
          (mul_le_mul (hAb r hrI) (hb r hrI) (norm_nonneg _) hK)
      have hcont : Continuous (fun r : ℝ => K * (a * (K * r) ^ n / (n.factorial : ℝ))) := by
        fun_prop
      have h1 : ‖∫ r in Icc (0 : ℝ) t, A r (v n r)‖ ≤
          ∫ r in Icc (0 : ℝ) t, K * (a * (K * r) ^ n / (n.factorial : ℝ)) :=
        norm_integral_le_of_norm_le (hcont.continuousOn.integrableOn_Icc)
          ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hbd))
      refine h1.trans (le_of_eq ?_)
      have e : ∀ r : ℝ, K * (a * (K * r) ^ n / (n.factorial : ℝ)) =
          (K * (a * K ^ n / (n.factorial : ℝ))) * r ^ n := by
        intro r
        rw [mul_pow]
        ring
      simp_rw [e]
      rw [sa16e_int_pow t ht.1]
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
  have hcont : ∀ n, ContinuousOn (v n) I := fun n => (key n).1
  have hnorm : ∀ n, ∀ t ∈ I, ‖v n t‖ ≤ a * (K * t) ^ n / (n.factorial : ℝ) := fun n => (key n).2
  set B : ℕ → ℝ := fun n => a * (K * T) ^ n / (n.factorial : ℝ) with hB
  have hBsum : Summable B := by
    have := (Real.summable_pow_div_factorial (K * T)).mul_left a
    refine this.congr fun n => ?_
    simp only [hB]
    ring
  have hBb : ∀ n, ∀ t ∈ I, ‖v n t‖ ≤ B n := by
    intro n t ht
    refine (hnorm n t ht).trans ?_
    have h2 : (K * t) ^ n ≤ (K * T) ^ n :=
      pow_le_pow_left₀ (mul_nonneg hK ht.1) (mul_le_mul_of_nonneg_left ht.2 hK) n
    have hfac : (0 : ℝ) < n.factorial := Nat.cast_pos.2 (Nat.factorial_pos n)
    simp only [hB]
    rw [div_le_div_iff_of_pos_right hfac]
    exact mul_le_mul_of_nonneg_left h2 ha0
  set u : ℝ → X := fun t => ∑' n, v n t with hu
  have hsum : ∀ t ∈ I, HasSum (fun n => v n t) (u t) := fun t ht =>
    (Summable.of_norm_bounded hBsum (fun n => hBb n t ht)).hasSum
  have hu_cont : ContinuousOn u I := continuousOn_tsum hcont hBsum hBb
  refine ⟨u, hu_cont, ?_⟩
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ I := Icc_subset_Icc le_rfl ht.2
  have hu_aesm : AEStronglyMeasurable u (volume.restrict I) :=
    hu_cont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨Cu, hCu⟩ := isCompact_Icc.exists_bound_of_continuousOn hu_cont
  have hAu_aesm : AEStronglyMeasurable (fun r => A r (u r)) (volume.restrict I) :=
    sa16e_aesm_apply A hA hu_aesm
  have hAu : IntegrableOn (fun r => A r (u r)) I :=
    Integrable.mono' (integrable_const (K * Cu)) hAu_aesm
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr =>
        ((A r).le_opNorm _).trans (mul_le_mul (hAb r hr) (hCu r hr) (norm_nonneg _) hK)))
  have hmain : HasSum (fun n => ∫ r in Icc (0 : ℝ) t, A r (v n r))
      (∫ r in Icc (0 : ℝ) t, A r (u r)) := by
    refine hasSum_integral_of_dominated_convergence (fun n _ => K * B n)
      (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
    · have hvn_aesm : AEStronglyMeasurable (v n) (volume.restrict I) :=
        (hcont n).aestronglyMeasurable measurableSet_Icc
      exact (sa16e_aesm_apply A hA hvn_aesm).mono_measure (Measure.restrict_mono hsub le_rfl)
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
      exact ((A r).le_opNorm _).trans (mul_le_mul (hAb r (hsub hr)) (hBb n r (hsub hr))
        (norm_nonneg _) hK)
    · exact Eventually.of_forall fun r => hBsum.mul_left K
    · exact integrable_const _
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (A r).hasSum (hsum r (hsub hr))
  have h1 : ∑' n, v (n + 1) t = ∫ r in Icc (0 : ℝ) t, A r (u r) := by
    have := hmain.tsum_eq
    simpa only [← hvs] using this
  have h2 : u t = v 0 t + ∑' n, v (n + 1) t := (hsum t ht).summable.tsum_eq_zero_add
  have hiA : IntegrableOn (fun r => A r (u r)) (Icc (0 : ℝ) t) := hAu.mono_set hsub
  have hif : IntegrableOn f (Icc (0 : ℝ) t) := hf.mono_set hsub
  rw [integral_add hiA hif, h2, h1, hv0]
  simp only
  abel

theorem bounded_ode_energy
    (p T K C : ℝ) (hp : 2 ≤ p) (hT : 0 ≤ T) (hK : 0 ≤ K)
    (N : X → ℝ) (hN : IsSmoothNorm p N)
    (A : ℝ → X →L[ℝ] X)
    (hA : ∀ x, AEStronglyMeasurable (fun r => A r x) (volume.restrict (Icc (0 : ℝ) T)))
    (hAb : ∀ r ∈ Icc (0 : ℝ) T, ‖A r‖ ≤ K)
    (hdiss : ∀ r ∈ Icc (0 : ℝ) T, ∀ x,
      fderiv ℝ (fun y => (N y)^p) x (A r x) ≤ p*C*(N x)^p)
    (f : ℝ → X) (hf : IntegrableOn f (Icc (0 : ℝ) T)) (x₀ : X) :
    ∃ v : ℝ → X, ContinuousOn v (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Icc (0 : ℝ) T, v t=x₀+∫ r in Icc (0 : ℝ) t, A r (v r)+f r) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        N (v t) ≤ Real.exp (C*t)*N x₀+
          ∫ r in Icc (0 : ℝ) t, Real.exp (C*(t-r))*N (f r) := by
  obtain ⟨v, hvc, hv⟩ := sa16x_ode_exists hT hK A hA hAb f hf x₀
  refine ⟨v, hvc, hv, ?_⟩
  have H : sa16x_Data p T K 0 C N (fun _ _ => ContinuousLinearMap.id ℝ X) A f v x₀ :=
    { hp := hp, hT := hT, hK := hK, hN := hN
      hdiag := fun _ _ => rfl
      hcomp := fun _ _ _ _ _ _ _ => rfl
      hcont := fun x => continuousOn_const
      hSbound := fun r t _ _ _ x => by simp
      hA := hA, hAb := hAb, hdiss := hdiss, hf := hf, hu := hvc
      hmild := fun t ht => by simpa using hv t ht }
  intro t ht
  simpa using sa16x_main H t ht

end T4

end HRS.Whole.AppendixA.Phase2SA16Transfer
