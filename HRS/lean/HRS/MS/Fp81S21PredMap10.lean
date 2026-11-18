import HRS.MS.Fp81S21PredMap9
import HRS.MS.R2InterpAux13

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

/-- Clip a source time to the available part of the recent prediction window. -/
def fp81s21_predSource {H S θ : ℝ} (hθ : 0 ≤ θ)
    (v : Icc (0 : ℝ) H) (τ : Icc (0 : ℝ) S) : Icc (0 : ℝ) H :=
  ⟨min (v : ℝ) (θ + τ), le_min v.2.1 (add_nonneg hθ τ.2.1),
    (min_le_left _ _).trans v.2.2⟩

/-- The recent clipped prediction is a bounded linear map on continuous chart
paths, with the bound inherited uniformly from the chart propagator. -/
theorem fp81s21_recentPred_exists
    {d r : ℕ} {Pw m T b H S θ : ℝ} {C : WholeCoeff d}
    {c : MultiIndex d → ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c)
    (hlin : S102Lin C m T) (E : r26t6_WeightedChart d r Pw)
    (hb : 0 ≤ b) (hθ : 0 ≤ θ) (hS : 0 ≤ S)
    (hgeo : θ + S ≤ H) (hT : b + H ≤ T) :
    ∃ P : C(Icc (0 : ℝ) H, r26t6_Coeff) →L[ℝ]
        C(Icc (0 : ℝ) H, OscPath d m S),
      ‖P‖ ≤ s102_KV d r Pw c ∧ ∀ x v τ,
        OscPath.at' (P x v) τ =
          let s := fp81s21_predSource hθ v τ
          r2Vprop C m (b + θ + τ) (b + s) (fp81s21_chartAction E (x s)) := by
  let D := Icc (0 : ℝ) H × Icc (0 : ℝ) S
  let src : D → Icc (0 : ℝ) H := fun p => fp81s21_predSource hθ p.1 p.2
  let start : D → ℝ := fun p => b + (src p : ℝ)
  let term : D → ℝ := fun p => b + θ + (p.2 : ℝ)
  have hsrcCont : Continuous src := by
    dsimp [D, src, fp81s21_predSource]
    refine Continuous.subtype_mk ?_ ?_
    · fun_prop
  have hstartCont : Continuous start :=
    continuous_const.add (continuous_subtype_val.comp hsrcCont)
  have htermCont : Continuous term := by
    dsimp [D, term]
    fun_prop
  have hsource (v : Icc (0 : ℝ) H) (τ : Icc (0 : ℝ) S) :
      b + (fp81s21_predSource hθ v τ : ℝ) ∈ Icc (0 : ℝ) T := by
    refine ⟨add_nonneg hb (fp81s21_predSource hθ v τ).2.1, ?_⟩
    calc
      b + (fp81s21_predSource hθ v τ : ℝ) ≤ b + H := by
        have hsH : (fp81s21_predSource hθ v τ : ℝ) ≤ H :=
          (min_le_left (v : ℝ) (θ + τ)).trans v.2.2
        linarith
      _ ≤ T := hT
  have hterminal (v : Icc (0 : ℝ) H) (τ : Icc (0 : ℝ) S) :
      b + θ + (τ : ℝ) ∈ Icc (b + (fp81s21_predSource hθ v τ : ℝ)) T := by
    refine ⟨?_, ?_⟩
    · have hs : (fp81s21_predSource hθ v τ : ℝ) ≤ θ + τ := min_le_right _ _
      linarith
    · calc
        b + θ + (τ : ℝ) ≤ b + θ + S := by linarith [τ.2.2]
        _ ≤ b + H := by linarith [hgeo]
        _ ≤ T := hT
  have hjoint := fp81s21_chartVprop_joint_cont hP hD hlin E
  let gamma (x : C(Icc (0 : ℝ) H, r26t6_Coeff)) :
      D → ((ℝ × ℝ) × r26t6_Coeff) := fun p =>
    ((start p, term p), x (src p))
  have hgammaCont (x : C(Icc (0 : ℝ) H, r26t6_Coeff)) : Continuous (gamma x) := by
    have hc : Continuous (fun p : D => x (src p)) := x.continuous.comp hsrcCont
    exact (hstartCont.prodMk htermCont).prodMk hc
  have hgammaMem (x : C(Icc (0 : ℝ) H, r26t6_Coeff)) (p : D) :
      gamma x p ∈ {y : (ℝ × ℝ) × r26t6_Coeff |
        0 ≤ y.1.1 ∧ y.1.1 ≤ y.1.2 ∧ y.1.2 ≤ T} := by
    change 0 ≤ start p ∧ start p ≤ term p ∧ term p ≤ T
    exact ⟨(hsource p.1 p.2).1,
      ⟨(hterminal p.1 p.2).1, (hterminal p.1 p.2).2⟩⟩
  have hrawCont (x : C(Icc (0 : ℝ) H, r26t6_Coeff)) : Continuous
      (fun p : D => r2Vprop C m (term p) (start p)
        (fp81s21_chartAction E (x (src p)))) := by
    have hh := hjoint.comp_continuous (f := gamma x) (hgammaCont x) (hgammaMem x)
    simpa [gamma, Function.comp_def] using hh
  let P₀ : C(Icc (0 : ℝ) H, r26t6_Coeff) →ₗ[ℝ]
      C(D, OscDual d m) :=
    { toFun := fun x =>
        ⟨fun p => fp81s21_chartVprop hP hD hlin E
          (hsource p.1 p.2) (hterminal p.1 p.2) (x (src p)),
          (hrawCont x).congr fun p => rfl⟩
      map_add' := by
        intro x y
        ext p
        let V := fp81s21_chartVprop hP hD hlin E
          (hsource p.1 p.2) (hterminal p.1 p.2)
        change V ((x + y) (src p)) = V (x (src p)) + V (y (src p))
        simp only [ContinuousMap.add_apply, map_add]
      map_smul' := by
        intro a x
        ext p
        let V := fp81s21_chartVprop hP hD hlin E
          (hsource p.1 p.2) (hterminal p.1 p.2)
        change V (a • x (src p)) = a • V (x (src p))
        simp only [ContinuousMap.smul_apply, map_smul] }
  let L : C(Icc (0 : ℝ) H, r26t6_Coeff) →ₗ[ℝ]
      C(Icc (0 : ℝ) H, OscPath d m S) :=
    { toFun := fun x => (P₀ x).curry
      map_add' := by
        intro x y
        ext v τ
        simp only [ContinuousMap.curry_apply]
        change (P₀ (x + y)) (v, τ) = (P₀ x) (v, τ) + (P₀ y) (v, τ)
        rw [map_add]
        simp only [ContinuousMap.add_apply]
      map_smul' := by
        intro a x
        ext v τ
        simp only [ContinuousMap.curry_apply]
        change (P₀ (a • x)) (v, τ) = a • (P₀ x) (v, τ)
        rw [map_smul]
        simp only [ContinuousMap.smul_apply] }
  have hLbound : ∀ x : C(Icc (0 : ℝ) H, r26t6_Coeff),
      ‖L x‖ ≤ s102_KV d r Pw c * ‖x‖ := by
    intro x
    have hk : 0 ≤ s102_KV d r Pw c * ‖x‖ :=
      mul_nonneg (s102_KV_nonneg d r Pw c) (norm_nonneg _)
    apply ((L x).norm_le hk).2
    intro v
    apply (((L x) v).norm_le hk).2
    intro τ
    let p : D := (v, τ)
    let V := fp81s21_chartVprop hP hD hlin E
      (hsource v τ) (hterminal v τ)
    change ‖V (x (src p))‖ ≤ s102_KV d r Pw c * ‖x‖
    calc
      ‖V (x (src p))‖ ≤ ‖V‖ * ‖x (src p)‖ := V.le_opNorm _
      _ ≤ s102_KV d r Pw c * ‖x (src p)‖ :=
        mul_le_mul_of_nonneg_right
          (fp81s21_chartVprop_norm_le hP hD hlin E (hsource v τ) (hterminal v τ))
          (norm_nonneg _)
      _ ≤ s102_KV d r Pw c * ‖x‖ :=
        mul_le_mul_of_nonneg_left (x.norm_coe_le_norm (src p))
          (s102_KV_nonneg d r Pw c)
  let P := L.mkContinuous (s102_KV d r Pw c) hLbound
  refine ⟨P, LinearMap.mkContinuous_norm_le L (s102_KV_nonneg d r Pw c) hLbound, ?_⟩
  intro x v τ
  change OscPath.at' (P x v) τ = _
  rfl

#print axioms HRS.Fp81.S21.fp81s21_recentPred_exists

end HRS.Fp81.S21
