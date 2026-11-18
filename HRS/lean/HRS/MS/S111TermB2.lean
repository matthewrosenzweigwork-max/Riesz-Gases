import HRS.Sections.IIDAux3
import HRS.Prob.Gaussian

/-!
# S11.1 continuation, T07: the cubic tensor coupling with Hölder exponents 2, 4, 4
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111K

open HRS

instance s111k_holder_442 : ENNReal.HolderTriple 4 4 2 :=
  ⟨by
    have h : (4 : ℝ≥0∞)⁻¹ = 2⁻¹ / 2 := by
      rw [div_eq_mul_inv, ← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    rw [h, ENNReal.add_halves]⟩

section Holder

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Hölder with exponents `2, 4, 4` for nonnegative functions. -/
theorem s111k_holder244 {a b c : Ω → ℝ} (ha0 : ∀ w, 0 ≤ a w) (hb0 : ∀ w, 0 ≤ b w) (hc0 : ∀ w, 0 ≤ c w)
    (ha : MemLp a 2 P) (hb : MemLp b 4 P) (hc : MemLp c 4 P)
    {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (h1 : ∫ w, a w ^ 2 ∂P ≤ α ^ 2) (h2 : ∫ w, b w ^ 4 ∂P ≤ β ^ 4) (h3 : ∫ w, c w ^ 4 ∂P ≤ γ ^ 4) :
    Integrable (fun w => a w * b w * c w) P ∧ ∫ w, a w * b w * c w ∂P ≤ α * β * γ := by
  have hbc : MemLp (b * c) 2 P := hb.mul hc
  have hbb : MemLp (b * b) 2 P := hb.mul hb
  have hcc : MemLp (c * c) 2 P := hc.mul hc
  have hint : Integrable (a * (b * c)) P := memLp_one_iff_integrable.1 (ha.mul hbc)
  have e : (fun w => a w * b w * c w) = a * (b * c) := by
    funext w; simp [mul_assoc]
  refine ⟨by rw [e]; exact hint, ?_⟩
  rw [e]
  -- fourth moments
  have hb4 : Integrable (fun w => b w ^ 4) P := by
    have := hb.integrable_norm_pow (p := 4) (by norm_num)
    simpa [Real.norm_of_nonneg (hb0 _)] using this
  have hc4 : Integrable (fun w => c w ^ 4) P := by
    have := hc.integrable_norm_pow (p := 4) (by norm_num)
    simpa [Real.norm_of_nonneg (hc0 _)] using this
  have hbsq : ∀ w, (b w ^ 2) ^ 2 = b w ^ 4 := fun w => by ring
  have hcsq : ∀ w, (c w ^ 2) ^ 2 = c w ^ 4 := fun w => by ring
  have cs1 : ∫ w, b w ^ 2 * c w ^ 2 ∂P ≤
      Real.sqrt (∫ w, (b w ^ 2) ^ 2 ∂P) * Real.sqrt (∫ w, (c w ^ 2) ^ 2 ∂P) := by
    refine HRS.IID.integral_mul_le_sqrt (fun w => sq_nonneg _) (fun w => sq_nonneg _) ?_ ?_ ?_ ?_
    · exact (hbb.aestronglyMeasurable.congr (Eventually.of_forall fun w => by simp [sq]))
    · exact (hcc.aestronglyMeasurable.congr (Eventually.of_forall fun w => by simp [sq]))
    · simpa only [hbsq] using hb4
    · simpa only [hcsq] using hc4
  simp only [hbsq, hcsq] at cs1
  have s1 : Real.sqrt (∫ w, b w ^ 4 ∂P) ≤ β ^ 2 := by
    calc Real.sqrt (∫ w, b w ^ 4 ∂P) ≤ Real.sqrt ((β ^ 2) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [← pow_mul]; exact h2)
      _ = β ^ 2 := Real.sqrt_sq (sq_nonneg _)
  have s2 : Real.sqrt (∫ w, c w ^ 4 ∂P) ≤ γ ^ 2 := by
    calc Real.sqrt (∫ w, c w ^ 4 ∂P) ≤ Real.sqrt ((γ ^ 2) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [← pow_mul]; exact h3)
      _ = γ ^ 2 := Real.sqrt_sq (sq_nonneg _)
  have hq : ∫ w, (b * c) w ^ 2 ∂P ≤ (β * γ) ^ 2 := by
    have : ∫ w, (b * c) w ^ 2 ∂P = ∫ w, b w ^ 2 * c w ^ 2 ∂P := by
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp [mul_pow]
    rw [this, mul_pow]
    refine cs1.trans ?_
    exact mul_le_mul s1 s2 (Real.sqrt_nonneg _) (sq_nonneg _)
  have hbcsq : Integrable (fun w => (b * c) w ^ 2) P := hbc.integrable_sq
  have cs2 := HRS.IID.integral_mul_le_sqrt (μ := P) (f := a) (g := b * c) ha0
    (fun w => mul_nonneg (hb0 w) (hc0 w)) ha.aestronglyMeasurable hbc.aestronglyMeasurable
    ha.integrable_sq hbcsq
  refine cs2.trans ?_
  have t1 : Real.sqrt (∫ w, a w ^ 2 ∂P) ≤ α := by
    calc Real.sqrt (∫ w, a w ^ 2 ∂P) ≤ Real.sqrt (α ^ 2) := Real.sqrt_le_sqrt h1
      _ = α := Real.sqrt_sq hα
  have t2 : Real.sqrt (∫ w, (b * c) w ^ 2 ∂P) ≤ β * γ := by
    calc Real.sqrt (∫ w, (b * c) w ^ 2 ∂P) ≤ Real.sqrt ((β * γ) ^ 2) := Real.sqrt_le_sqrt hq
      _ = β * γ := Real.sqrt_sq (mul_nonneg hβ hγ)
  calc Real.sqrt (∫ w, a w ^ 2 ∂P) * Real.sqrt (∫ w, (b * c) w ^ 2 ∂P) ≤ α * (β * γ) :=
        mul_le_mul t1 t2 (Real.sqrt_nonneg _) hα
    _ = α * β * γ := by ring

end Holder

section Main

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The telescoping identity for a trilinear form. -/
theorem s111k_telescope (M : B [×3]→L[ℝ] ℝ) (x y : Fin 3 → B) :
    M x - M y = M ![x 0 - y 0, x 1, x 2] + M ![y 0, x 1 - y 1, x 2] + M ![y 0, y 1, x 2 - y 2] := by
  classical
  have h0 := M.map_update_sub x 0 (x 0) (y 0)
  have h1 := M.map_update_sub (Function.update x 0 (y 0)) 1 (x 1) (y 1)
  have h2 := M.map_update_sub (Function.update (Function.update x 0 (y 0)) 1 (y 1)) 2 (x 2) (y 2)
  have e0 : Function.update x 0 (x 0) = x := Function.update_eq_self _ _
  have ea : Function.update x 0 (x 0 - y 0) = ![x 0 - y 0, x 1, x 2] := by
    funext i; fin_cases i <;> simp [Function.update]
  have eb : Function.update (Function.update x 0 (y 0)) 1 (x 1 - y 1) = ![y 0, x 1 - y 1, x 2] := by
    funext i; fin_cases i <;> simp [Function.update]
  have ec : Function.update (Function.update (Function.update x 0 (y 0)) 1 (y 1)) 2 (x 2 - y 2) =
      ![y 0, y 1, x 2 - y 2] := by
    funext i; fin_cases i <;> simp [Function.update]
  have f1 : Function.update (Function.update x 0 (y 0)) 1 (x 1) = Function.update x 0 (y 0) := by
    have : Function.update x 0 (y 0) 1 = x 1 := by simp [Function.update]
    rw [← this]; exact Function.update_eq_self _ _
  have f2 : Function.update (Function.update (Function.update x 0 (y 0)) 1 (y 1)) 2 (x 2) =
      Function.update (Function.update x 0 (y 0)) 1 (y 1) := by
    have : Function.update (Function.update x 0 (y 0)) 1 (y 1) 2 = x 2 := by simp [Function.update]
    rw [← this]; exact Function.update_eq_self _ _
  have f3 : Function.update (Function.update (Function.update x 0 (y 0)) 1 (y 1)) 2 (y 2) = y := by
    funext i; fin_cases i <;> simp [Function.update]
  rw [e0, ea] at h0
  rw [f1, eb] at h1
  rw [f2, ec, f3] at h2
  linarith

/-- One trilinear term: slot 0 in `L²`, slots 1, 2 in `L⁴`. -/
theorem s111k_term (M : B [×3]→L[ℝ] ℝ) {u0 u1 u2 : Ω → B}
    (h0 : MemLp u0 2 P) (h1 : MemLp u1 4 P) (h2 : MemLp u2 4 P)
    {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (m0 : ∫ w, ‖u0 w‖ ^ 2 ∂P ≤ α ^ 2) (m1 : ∫ w, ‖u1 w‖ ^ 4 ∂P ≤ β ^ 4)
    (m2 : ∫ w, ‖u2 w‖ ^ 4 ∂P ≤ γ ^ 4) :
    Integrable (fun w => M ![u0 w, u1 w, u2 w]) P ∧
      ∫ w, ‖M ![u0 w, u1 w, u2 w]‖ ∂P ≤ ‖M‖ * (α * β * γ) := by
  obtain ⟨hI, hV⟩ := s111k_holder244 (P := P) (a := fun w => ‖u0 w‖) (b := fun w => ‖u1 w‖)
    (c := fun w => ‖u2 w‖) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    h0.norm h1.norm h2.norm hα hβ hγ m0 m1 m2
  have hbd : ∀ w, ‖M ![u0 w, u1 w, u2 w]‖ ≤ ‖M‖ * (‖u0 w‖ * ‖u1 w‖ * ‖u2 w‖) := by
    intro w
    refine (M.le_opNorm _).trans ?_
    simp [Fin.prod_univ_three]
  have hmeas : AEStronglyMeasurable (fun w => M ![u0 w, u1 w, u2 w]) P := by
    refine M.cont.comp_aestronglyMeasurable ?_
    refine AEMeasurable.aestronglyMeasurable ?_
    refine aemeasurable_pi_iff.2 (fun i => ?_)
    fin_cases i
    · exact h0.aestronglyMeasurable.aemeasurable
    · exact h1.aestronglyMeasurable.aemeasurable
    · exact h2.aestronglyMeasurable.aemeasurable
  have hint : Integrable (fun w => M ![u0 w, u1 w, u2 w]) P :=
    Integrable.mono' (hI.const_mul ‖M‖) hmeas (Eventually.of_forall hbd)
  refine ⟨hint, ?_⟩
  calc ∫ w, ‖M ![u0 w, u1 w, u2 w]‖ ∂P ≤ ∫ w, ‖M‖ * (‖u0 w‖ * ‖u1 w‖ * ‖u2 w‖) ∂P :=
        integral_mono hint.norm (hI.const_mul ‖M‖) hbd
    _ = ‖M‖ * ∫ w, ‖u0 w‖ * ‖u1 w‖ * ‖u2 w‖ ∂P := integral_const_mul _ _
    _ ≤ ‖M‖ * (α * β * γ) := mul_le_mul_of_nonneg_left hV (norm_nonneg _)

/-- **T07 (cubic tensor coupling, exponents 2, 4, 4).** -/
theorem s111k_cubic_tensor_coupling [CompleteSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Fin 3 → Ω → B)
    (hX : ∀ i, MemLp (X i) (if i = 0 then 2 else 4) P)
    (hY : ∀ i, MemLp (Y i) (if i = 0 then 2 else 4) P)
    (C delta : ℝ) (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hmom : ∀ i : Fin 3,
      let p : ℕ := if i = 0 then 2 else 4
      (∫ w, ‖X i w‖ ^ p ∂P) ≤ C ^ p ∧
      (∫ w, ‖Y i w‖ ^ p ∂P) ≤ C ^ p ∧
      (∫ w, ‖X i w - Y i w‖ ^ p ∂P) ≤ delta ^ p)
    (kappa kappab : projTensor B 3)
    (hrep : ∀ M : B [×3]→L[ℝ] ℝ,
      (kappa : TensorDual B 3) M = ∫ w, M (fun i => X i w) ∂P)
    (hrepb : ∀ M : B [×3]→L[ℝ] ℝ,
      (kappab : TensorDual B 3) M = ∫ w, M (fun i => Y i w) ∂P) :
    ‖kappa - kappab‖ ≤ 3 * C ^ 2 * delta := by
  have hX0 : MemLp (X 0) 2 P := by simpa using hX 0
  have hX1 : MemLp (X 1) 4 P := by simpa using hX 1
  have hX2 : MemLp (X 2) 4 P := by simpa using hX 2
  have hY0 : MemLp (Y 0) 2 P := by simpa using hY 0
  have hY1 : MemLp (Y 1) 4 P := by simpa using hY 1
  have hY2 : MemLp (Y 2) 4 P := by simpa using hY 2
  obtain ⟨a0, b0, c0⟩ : (∫ w, ‖X 0 w‖ ^ 2 ∂P) ≤ C ^ 2 ∧ (∫ w, ‖Y 0 w‖ ^ 2 ∂P) ≤ C ^ 2 ∧
      (∫ w, ‖X 0 w - Y 0 w‖ ^ 2 ∂P) ≤ delta ^ 2 := by simpa using hmom 0
  obtain ⟨a1, b1, c1⟩ : (∫ w, ‖X 1 w‖ ^ 4 ∂P) ≤ C ^ 4 ∧ (∫ w, ‖Y 1 w‖ ^ 4 ∂P) ≤ C ^ 4 ∧
      (∫ w, ‖X 1 w - Y 1 w‖ ^ 4 ∂P) ≤ delta ^ 4 := by simpa using hmom 1
  obtain ⟨a2, b2, c2⟩ : (∫ w, ‖X 2 w‖ ^ 4 ∂P) ≤ C ^ 4 ∧ (∫ w, ‖Y 2 w‖ ^ 4 ∂P) ≤ C ^ 4 ∧
      (∫ w, ‖X 2 w - Y 2 w‖ ^ 4 ∂P) ≤ delta ^ 4 := by simpa using hmom 2
  have eX : ∀ w, (fun i => X i w) = ![X 0 w, X 1 w, X 2 w] := by
    intro w; funext i; fin_cases i <;> rfl
  have eY : ∀ w, (fun i => Y i w) = ![Y 0 w, Y 1 w, Y 2 w] := by
    intro w; funext i; fin_cases i <;> rfl
  have hunit : ∀ M : B [×3]→L[ℝ] ℝ, |(kappa : TensorDual B 3) M - (kappab : TensorDual B 3) M| ≤
      3 * C ^ 2 * delta * ‖M‖ := by
    intro M
    rw [hrep, hrepb]
    simp_rw [eX, eY]
    have tG := s111k_term (P := P) M hX0 hX1 hX2 hC hC hC a0 a1 a2
    have tH := s111k_term (P := P) M hY0 hY1 hY2 hC hC hC b0 b1 b2
    have t1 := s111k_term (P := P) M (u0 := fun w => X 0 w - Y 0 w) (u1 := X 1) (u2 := X 2)
      (hX0.sub hY0) hX1 hX2 hdelta hC hC c0 a1 a2
    have t2 := s111k_term (P := P) M (u0 := Y 0) (u1 := fun w => X 1 w - Y 1 w) (u2 := X 2)
      hY0 (hX1.sub hY1) hX2 hC hdelta hC b0 c1 a2
    have t3 := s111k_term (P := P) M (u0 := Y 0) (u1 := Y 1) (u2 := fun w => X 2 w - Y 2 w)
      hY0 hY1 (hX2.sub hY2) hC hC hdelta b0 b1 c2
    rw [← integral_sub tG.1 tH.1]
    have hpt : ∀ w, ‖M ![X 0 w, X 1 w, X 2 w] - M ![Y 0 w, Y 1 w, Y 2 w]‖ ≤
        ‖M ![X 0 w - Y 0 w, X 1 w, X 2 w]‖ + ‖M ![Y 0 w, X 1 w - Y 1 w, X 2 w]‖ +
          ‖M ![Y 0 w, Y 1 w, X 2 w - Y 2 w]‖ := by
      intro w
      have := s111k_telescope M ![X 0 w, X 1 w, X 2 w] ![Y 0 w, Y 1 w, Y 2 w]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at this
      rw [this]
      exact (norm_add₃_le).trans le_rfl
    calc |∫ w, (M ![X 0 w, X 1 w, X 2 w] - M ![Y 0 w, Y 1 w, Y 2 w]) ∂P|
        ≤ ∫ w, ‖M ![X 0 w, X 1 w, X 2 w] - M ![Y 0 w, Y 1 w, Y 2 w]‖ ∂P := by
          simpa using norm_integral_le_integral_norm
            (fun w => M ![X 0 w, X 1 w, X 2 w] - M ![Y 0 w, Y 1 w, Y 2 w])
      _ ≤ ∫ w, (‖M ![X 0 w - Y 0 w, X 1 w, X 2 w]‖ + ‖M ![Y 0 w, X 1 w - Y 1 w, X 2 w]‖ +
            ‖M ![Y 0 w, Y 1 w, X 2 w - Y 2 w]‖) ∂P :=
          integral_mono (tG.1.sub tH.1).norm ((t1.1.norm.add t2.1.norm).add t3.1.norm) hpt
      _ = (∫ w, ‖M ![X 0 w - Y 0 w, X 1 w, X 2 w]‖ ∂P) + (∫ w, ‖M ![Y 0 w, X 1 w - Y 1 w, X 2 w]‖ ∂P) +
            ∫ w, ‖M ![Y 0 w, Y 1 w, X 2 w - Y 2 w]‖ ∂P := by
          have i12 : Integrable (fun w => ‖M ![X 0 w - Y 0 w, X 1 w, X 2 w]‖ +
              ‖M ![Y 0 w, X 1 w - Y 1 w, X 2 w]‖) P := t1.1.norm.add t2.1.norm
          rw [integral_add i12 t3.1.norm, integral_add t1.1.norm t2.1.norm]
      _ ≤ ‖M‖ * (delta * C * C) + ‖M‖ * (C * delta * C) + ‖M‖ * (C * C * delta) :=
          add_le_add (add_le_add t1.2 t2.2) t3.2
      _ = 3 * C ^ 2 * delta * ‖M‖ := by ring
  have : ‖(kappa - kappab : projTensor B 3)‖ ≤ 3 * C ^ 2 * delta := by
    have hnn : 0 ≤ 3 * C ^ 2 * delta := by positivity
    show ‖((kappa - kappab : projTensor B 3) : TensorDual B 3)‖ ≤ _
    refine ContinuousLinearMap.opNorm_le_bound _ hnn fun M => ?_
    rw [Real.norm_eq_abs]
    have := hunit M
    simpa [mul_comm] using this
  exact this

end Main

end HRS.MS.S111K
