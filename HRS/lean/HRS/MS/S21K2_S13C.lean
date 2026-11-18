import HRS.Whole.Basic

/-!
# S21K2 S13C -- coordinate pairs under the i.i.d. product `Measure.pi` (R26-T3.S13, third step)

For `P = Measure.pi (fun _ : Fin N => μ)` with `μ` a probability measure: the law of a pair of distinct coordinates is `μ ⊗ μ`
(`s21k2_s13_pair_law`), so integrals of pair functions transfer to `μ ⊗ μ`; and two pair functions on disjoint index pairs
are independent, so the second moment factorises (`s21k2_s13_disjoint_integral`).  Helper prefix `s21k2_s13_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory
noncomputable section
namespace HRS.MS.R26T3

variable {d N : ℕ}

theorem s21k2_s13_iIndep {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ] :
    iIndepFun (fun i (ω : Fin N → HRS.Euc d) => ω i) (Measure.pi fun _ : Fin N => μ) :=
  iIndepFun_pi (μ := fun _ : Fin N => μ) (X := fun _ => id) (fun _ => aemeasurable_id)

theorem s21k2_s13_coord_law {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ] (i : Fin N) :
    (Measure.pi fun _ : Fin N => μ).map (fun ω => ω i) = μ := by
  classical
  rw [show (fun ω : Fin N → HRS.Euc d => ω i) = Function.eval i from rfl, Measure.pi_map_eval]
  simp

theorem s21k2_s13_pair_law {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ] {i j : Fin N} (hij : i ≠ j) :
    (Measure.pi fun _ : Fin N => μ).map (fun ω => (ω i, ω j)) = μ.prod μ := by
  have hind := (s21k2_s13_iIndep (μ := μ) (N := N)).indepFun hij
  have hi : AEMeasurable (fun ω : Fin N → HRS.Euc d => ω i) (Measure.pi fun _ : Fin N => μ) :=
    (measurable_pi_apply i).aemeasurable
  have hj : AEMeasurable (fun ω : Fin N → HRS.Euc d => ω j) (Measure.pi fun _ : Fin N => μ) :=
    (measurable_pi_apply j).aemeasurable
  have h := (indepFun_iff_map_prod_eq_prod_map_map hi hj).1 hind
  rw [h, s21k2_s13_coord_law, s21k2_s13_coord_law]

theorem s21k2_s13_pair_ae {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ] {i j : Fin N} (hij : i ≠ j)
    {G : HRS.Euc d × HRS.Euc d → ℝ} (hG : AEStronglyMeasurable G (μ.prod μ)) :
    AEStronglyMeasurable (fun ω : Fin N → HRS.Euc d => G (ω i, ω j)) (Measure.pi fun _ : Fin N => μ) := by
  have hm : Measurable (fun ω : Fin N → HRS.Euc d => (ω i, ω j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have : AEStronglyMeasurable G ((Measure.pi fun _ : Fin N => μ).map (fun ω => (ω i, ω j))) := by
    rw [s21k2_s13_pair_law hij]; exact hG
  exact this.comp_aemeasurable hm.aemeasurable

theorem s21k2_s13_integral_pair {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ] {i j : Fin N} (hij : i ≠ j)
    {G : HRS.Euc d × HRS.Euc d → ℝ} (hG : AEStronglyMeasurable G (μ.prod μ)) :
    ∫ ω, G (ω i, ω j) ∂(Measure.pi fun _ : Fin N => μ) = ∫ z, G z ∂(μ.prod μ) := by
  have hm : Measurable (fun ω : Fin N → HRS.Euc d => (ω i, ω j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hG' : AEStronglyMeasurable G ((Measure.pi fun _ : Fin N => μ).map (fun ω => (ω i, ω j))) := by
    rw [s21k2_s13_pair_law hij]; exact hG
  rw [← s21k2_s13_pair_law hij, integral_map hm.aemeasurable hG']

theorem s21k2_s13_disjoint_integral {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    {G : HRS.Euc d × HRS.Euc d → ℝ} (hG : MemLp G 2 (μ.prod μ)) :
    ∫ ω, G (ω i, ω j) * G (ω k, ω l) ∂(Measure.pi fun _ : Fin N => μ) =
      (∫ z, G z ∂(μ.prod μ)) ^ 2 := by
  classical
  set S : Finset (Fin N) := {i, j} with hS
  set T : Finset (Fin N) := {k, l} with hT
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [hS, hT, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hik rfl
    · exact hil rfl
    · exact hjk rfl
    · exact hjl rfl
  have hIST := (s21k2_s13_iIndep (μ := μ) (N := N)).indepFun_finset S T hdisj
    (fun i => measurable_pi_apply i)
  have hφS : Measurable (fun v : S → HRS.Euc d => (v ⟨i, by simp [hS]⟩, v ⟨j, by simp [hS]⟩)) :=
    ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
  have hφT : Measurable (fun v : T → HRS.Euc d => (v ⟨k, by simp [hT]⟩, v ⟨l, by simp [hT]⟩)) :=
    ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
  have hpair := hIST.comp hφS hφT
  have hXm : Measurable (fun ω : Fin N → HRS.Euc d => (ω i, ω j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hYm : Measurable (fun ω : Fin N → HRS.Euc d => (ω k, ω l)) :=
    (measurable_pi_apply k).prodMk (measurable_pi_apply l)
  have hX : AEMeasurable (fun ω : Fin N → HRS.Euc d => (ω i, ω j)) (Measure.pi fun _ : Fin N => μ) :=
    hXm.aemeasurable
  have hY : AEMeasurable (fun ω : Fin N → HRS.Euc d => (ω k, ω l)) (Measure.pi fun _ : Fin N => μ) :=
    hYm.aemeasurable
  have hGX : AEMeasurable G ((Measure.pi fun _ : Fin N => μ).map (fun ω => (ω i, ω j))) := by
    rw [s21k2_s13_pair_law hij]; exact hG.aemeasurable
  have hGY : AEMeasurable G ((Measure.pi fun _ : Fin N => μ).map (fun ω => (ω k, ω l))) := by
    rw [s21k2_s13_pair_law hkl]; exact hG.aemeasurable
  have hsX : AEMeasurable (fun v : S → HRS.Euc d => (v ⟨i, by simp [hS]⟩, v ⟨j, by simp [hS]⟩))
      ((Measure.pi fun _ : Fin N => μ).map (fun a (s : S) => a s)) := hφS.aemeasurable
  have hsY : AEMeasurable (fun v : T → HRS.Euc d => (v ⟨k, by simp [hT]⟩, v ⟨l, by simp [hT]⟩))
      ((Measure.pi fun _ : Fin N => μ).map (fun a (t : T) => a t)) := hφT.aemeasurable
  have hind : IndepFun (fun ω => G (ω i, ω j)) (fun ω => G (ω k, ω l)) (Measure.pi fun _ : Fin N => μ) :=
    hpair.comp₀ hX hY hGX hGY
  have hIX : AEStronglyMeasurable (fun ω : Fin N → HRS.Euc d => G (ω i, ω j)) (Measure.pi fun _ : Fin N => μ) :=
    s21k2_s13_pair_ae hij hG.aestronglyMeasurable
  have hIY : AEStronglyMeasurable (fun ω : Fin N → HRS.Euc d => G (ω k, ω l)) (Measure.pi fun _ : Fin N => μ) :=
    s21k2_s13_pair_ae hkl hG.aestronglyMeasurable
  have hmul := hind.integral_mul_eq_mul_integral hIX hIY
  have h1 := s21k2_s13_integral_pair (μ := μ) (N := N) hij hG.aestronglyMeasurable
  have h2 := s21k2_s13_integral_pair (μ := μ) (N := N) hkl hG.aestronglyMeasurable
  rw [sq]
  calc _ = (∫ ω, G (ω i, ω j) ∂(Measure.pi fun _ : Fin N => μ)) *
        (∫ ω, G (ω k, ω l) ∂(Measure.pi fun _ : Fin N => μ)) := hmul
    _ = _ := by rw [h1, h2]

end HRS.MS.R26T3
