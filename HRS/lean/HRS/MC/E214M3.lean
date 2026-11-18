import HRS.MC.E214M1

/-!
# Packet e214m, file 3: Hölder glue for the Bochner product tensors

`m_holder333` (three factors, exponents `3,3,3`) and `m_holder22` (two factors, exponents `2,2`): finiteness of the
`eLpNorm`s gives integrability of the product of norms and the bound `∫ ≤ product of eLpNorms`.
`norm_bochTensor3_sub_le_holder` and `norm_bochTensor21_sub_le_holder` combine them with
`norm_bochTensor3_sub_le_proof` / `norm_bochTensor21_sub_le_proof` (these are the shapes used by `Kwin_relax`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

set_option maxSynthPendingDepth 3

namespace HRS.MC.E214M

open HRS HRS.Contr HRS.MC.E213T

section Holder

variable {Ω : Type*} [MeasurableSpace Ω] {E₁ E₂ E₃ : Type*}
  [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup E₃]

/-- the intermediate exponent `r = (3⁻¹ + 3⁻¹)⁻¹ = 3/2`. -/
def m_r32 : ℝ≥0∞ := ((3 : ℝ≥0∞)⁻¹ + (3 : ℝ≥0∞)⁻¹)⁻¹

theorem m_holderTriple_33 : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 m_r32 :=
  ENNReal.HolderTriple.of 3 3

theorem m_holderTriple_3r : ENNReal.HolderTriple (3 : ℝ≥0∞) m_r32 1 where
  inv_add_inv_eq_inv := by
    unfold m_r32
    rw [inv_inv, inv_one]
    have h : (3 : ℝ≥0∞)⁻¹ + ((3 : ℝ≥0∞)⁻¹ + (3 : ℝ≥0∞)⁻¹) = 3 * 3⁻¹ := by ring
    rw [h]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- Hölder for three real functions with exponents `3,3,3`. -/
theorem m_holder333_real {F G H : Ω → ℝ} {P : Measure Ω}
    (hF : MemLp F 3 P) (hG : MemLp G 3 P) (hH : MemLp H 3 P) :
    Integrable (fun ω => F ω * G ω * H ω) P ∧
    ∫ ω, ‖F ω * G ω * H ω‖ ∂P ≤
      (eLpNorm F 3 P * eLpNorm G 3 P * eLpNorm H 3 P).toReal := by
  haveI := m_holderTriple_33
  haveI := m_holderTriple_3r
  have hFG : MemLp (F * G) m_r32 P := MemLp.mul hF hG
  have hFGH : MemLp ((F * G) * H) 1 P := MemLp.mul hFG hH
  refine ⟨memLp_one_iff_integrable.1 hFGH, ?_⟩
  have h1 : eLpNorm (F * G) m_r32 P ≤ eLpNorm F 3 P * eLpNorm G 3 P := by
    simpa [smul_eq_mul] using
      (eLpNorm_smul_le_mul_eLpNorm hF.aestronglyMeasurable hG.aestronglyMeasurable (p := (3 : ℝ≥0∞)) (q := 3) (r := m_r32) (μ := P))
  have h2 : eLpNorm ((F * G) * H) 1 P ≤ eLpNorm (F * G) m_r32 P * eLpNorm H 3 P := by
    simpa [smul_eq_mul] using
      (eLpNorm_smul_le_mul_eLpNorm hFG.aestronglyMeasurable hH.aestronglyMeasurable (p := m_r32) (q := (3 : ℝ≥0∞)) (r := 1) (μ := P))
  have h3 : eLpNorm ((F * G) * H) 1 P ≤ eLpNorm F 3 P * eLpNorm G 3 P * eLpNorm H 3 P :=
    h2.trans (by gcongr)
  have hfin : eLpNorm F 3 P * eLpNorm G 3 P * eLpNorm H 3 P ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hF.eLpNorm_lt_top.ne hG.eLpNorm_lt_top.ne) hH.eLpNorm_lt_top.ne
  have hint := memLp_one_iff_integrable.1 hFGH
  have e1 : ∫ ω, ‖F ω * G ω * H ω‖ ∂P = (eLpNorm ((F * G) * H) 1 P).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable, ← integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable]
    rfl
  rw [e1]
  exact ENNReal.toReal_mono hfin h3

/-- Hölder for two real functions with exponents `2,2`. -/
theorem m_holder22_real {F G : Ω → ℝ} {P : Measure Ω} (hF : MemLp F 2 P) (hG : MemLp G 2 P) :
    Integrable (fun ω => F ω * G ω) P ∧
    ∫ ω, ‖F ω * G ω‖ ∂P ≤ (eLpNorm F 2 P * eLpNorm G 2 P).toReal := by
  have hFG : MemLp (F * G) 1 P := MemLp.mul hF hG
  have hint := memLp_one_iff_integrable.1 hFG
  refine ⟨hint, ?_⟩
  have h2 : eLpNorm (F * G) 1 P ≤ eLpNorm F 2 P * eLpNorm G 2 P := by
    simpa [smul_eq_mul] using
      (eLpNorm_smul_le_mul_eLpNorm hF.aestronglyMeasurable hG.aestronglyMeasurable
        (p := (2 : ℝ≥0∞)) (q := 2) (r := 1) (μ := P))
  have hfin : eLpNorm F 2 P * eLpNorm G 2 P ≠ ⊤ :=
    ENNReal.mul_ne_top hF.eLpNorm_lt_top.ne hG.eLpNorm_lt_top.ne
  have e1 : ∫ ω, ‖F ω * G ω‖ ∂P = (eLpNorm (F * G) 1 P).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable,
      ← integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable]
    rfl
  rw [e1]
  exact ENNReal.toReal_mono hfin h2

variable {P : Measure Ω}

theorem m_memLp_norm {E : Type*} [NormedAddCommGroup E] {f : Ω → E} {p : ℝ≥0∞}
    (hf : AEStronglyMeasurable f P) (hlt : eLpNorm f p P < ⊤) : MemLp (fun ω => ‖f ω‖) p P :=
  by rw [memLp_iff, eLpNorm_norm _ hf]; exact hlt

/-- Vector-valued Hölder `3,3,3`: with the bounds `eLpNorm ≤ ofReal` of the three factors. -/
theorem m_holder333 {f : Ω → E₁} {g : Ω → E₂} {h : Ω → E₃}
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P) (hh : AEStronglyMeasurable h P)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hfa : eLpNorm f 3 P ≤ ENNReal.ofReal a) (hgb : eLpNorm g 3 P ≤ ENNReal.ofReal b)
    (hhc : eLpNorm h 3 P ≤ ENNReal.ofReal c) :
    Integrable (fun ω => ‖f ω‖ * ‖g ω‖ * ‖h ω‖) P ∧
    ∫ ω, ‖f ω‖ * ‖g ω‖ * ‖h ω‖ ∂P ≤ a * b * c := by
  obtain ⟨hi, hle⟩ := m_holder333_real (m_memLp_norm hf (hfa.trans_lt ENNReal.ofReal_lt_top))
    (m_memLp_norm hg (hgb.trans_lt ENNReal.ofReal_lt_top))
    (m_memLp_norm hh (hhc.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hi, ?_⟩
  simp only [norm_mul, norm_norm] at hle
  refine hle.trans ?_
  rw [eLpNorm_norm _ hf, eLpNorm_norm _ hg, eLpNorm_norm _ hh]
  have hfin : ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  calc (eLpNorm f 3 P * eLpNorm g 3 P * eLpNorm h 3 P).toReal
      ≤ (ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c).toReal :=
        ENNReal.toReal_mono hfin (by gcongr)
    _ = a * b * c := by
        rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb),
          ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg ha hb) hc)]

/-- Vector-valued Hölder `2,2`. -/
theorem m_holder22 {f : Ω → E₁} {g : Ω → E₂}
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hfa : eLpNorm f 2 P ≤ ENNReal.ofReal a) (hgb : eLpNorm g 2 P ≤ ENNReal.ofReal b) :
    Integrable (fun ω => ‖f ω‖ * ‖g ω‖) P ∧ ∫ ω, ‖f ω‖ * ‖g ω‖ ∂P ≤ a * b := by
  obtain ⟨hi, hle⟩ := m_holder22_real (m_memLp_norm hf (hfa.trans_lt ENNReal.ofReal_lt_top))
    (m_memLp_norm hg (hgb.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hi, ?_⟩
  simp only [norm_mul, norm_norm] at hle
  refine hle.trans ?_
  rw [eLpNorm_norm _ hf, eLpNorm_norm _ hg]
  have hfin : ENNReal.ofReal a * ENNReal.ofReal b ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  calc (eLpNorm f 2 P * eLpNorm g 2 P).toReal
      ≤ (ENNReal.ofReal a * ENNReal.ofReal b).toReal :=
        ENNReal.toReal_mono hfin (by gcongr)
    _ = a * b := by
        rw [← ENNReal.ofReal_mul ha, ENNReal.toReal_ofReal (mul_nonneg ha hb)]

end Holder

section Combined

variable {Ω : Type*} [MeasurableSpace Ω] {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- **Cubic tensor difference with `L³` bounds** (the shape used by `Kwin_relax`):
`‖E[x⊗y⊗z] - E[x'⊗y'⊗z']‖ ≤ δx·My·Mz + Mx'·δy·Mz + Mx'·My'·δz` when
`‖x - x'‖₃ ≤ δx`, `‖y - y'‖₃ ≤ δy`, `‖z - z'‖₃ ≤ δz`, `‖y‖₃ ≤ My`, `‖z‖₃ ≤ Mz`, `‖x'‖₃ ≤ Mx'`, `‖y'‖₃ ≤ My'`. -/
theorem norm_bochTensor3_sub_le_holder (P : Measure Ω) {x y z x' y' z' : Ω → B}
    (hx : AEStronglyMeasurable x P) (hy : AEStronglyMeasurable y P) (hz : AEStronglyMeasurable z P)
    (hx' : AEStronglyMeasurable x' P) (hy' : AEStronglyMeasurable y' P) (hz' : AEStronglyMeasurable z' P)
    {δx δy δz My Mz Mx' My' : ℝ} (hδx : 0 ≤ δx) (hδy : 0 ≤ δy) (hδz : 0 ≤ δz)
    (hMy : 0 ≤ My) (hMz : 0 ≤ Mz) (hMx' : 0 ≤ Mx') (hMy' : 0 ≤ My')
    (hdx : eLpNorm (fun ω => x ω - x' ω) 3 P ≤ ENNReal.ofReal δx)
    (hdy : eLpNorm (fun ω => y ω - y' ω) 3 P ≤ ENNReal.ofReal δy)
    (hdz : eLpNorm (fun ω => z ω - z' ω) 3 P ≤ ENNReal.ofReal δz)
    (hy3 : eLpNorm y 3 P ≤ ENNReal.ofReal My) (hz3 : eLpNorm z 3 P ≤ ENNReal.ofReal Mz)
    (hx3' : eLpNorm x' 3 P ≤ ENNReal.ofReal Mx') (hy3' : eLpNorm y' 3 P ≤ ENNReal.ofReal My') :
    ‖bochTensor3 P x y z - bochTensor3 P x' y' z'‖ ≤
      δx * My * Mz + Mx' * δy * Mz + Mx' * My' * δz := by
  obtain ⟨i1, b1⟩ : Integrable (fun ω => ‖x ω - x' ω‖ * ‖y ω‖ * ‖z ω‖) P ∧
      ∫ ω, ‖x ω - x' ω‖ * ‖y ω‖ * ‖z ω‖ ∂P ≤ δx * My * Mz :=
    m_holder333 (f := fun ω => x ω - x' ω) (hx.sub hx') hy hz hδx hMy hMz hdx hy3 hz3
  obtain ⟨i2, b2⟩ : Integrable (fun ω => ‖x' ω‖ * ‖y ω - y' ω‖ * ‖z ω‖) P ∧
      ∫ ω, ‖x' ω‖ * ‖y ω - y' ω‖ * ‖z ω‖ ∂P ≤ Mx' * δy * Mz :=
    m_holder333 (g := fun ω => y ω - y' ω) hx' (hy.sub hy') hz hMx' hδy hMz hx3' hdy hz3
  obtain ⟨i3, b3⟩ : Integrable (fun ω => ‖x' ω‖ * ‖y' ω‖ * ‖z ω - z' ω‖) P ∧
      ∫ ω, ‖x' ω‖ * ‖y' ω‖ * ‖z ω - z' ω‖ ∂P ≤ Mx' * My' * δz :=
    m_holder333 (h := fun ω => z ω - z' ω) hx' hy' (hz.sub hz') hMx' hMy' hδz hx3' hy3' hdz
  refine (norm_bochTensor3_sub_le_proof P hx hy hz hx' hy' hz' i1 i2 i3).trans ?_
  have i12 : Integrable (fun ω => ‖x ω - x' ω‖ * ‖y ω‖ * ‖z ω‖ + ‖x' ω‖ * ‖y ω - y' ω‖ * ‖z ω‖) P :=
    i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2]
  linarith

/-- **Covariance-type tensor difference with `L²` bounds**:
`‖E[J⊗g] - E[J'⊗g']‖ ≤ δJ·Mg + MJ'·δg` when `‖J - J'‖₂ ≤ δJ`, `‖g‖₂ ≤ Mg`, `‖J'‖₂ ≤ MJ'`, `‖g - g'‖₂ ≤ δg`. -/
theorem norm_bochTensor21_sub_le_holder (P : Measure Ω) [IsProbabilityMeasure P]
    {J J' : Ω → TensorDual B 2} {g g' : Ω → B}
    (hJ : AEStronglyMeasurable J P) (hJ' : AEStronglyMeasurable J' P)
    (hg : AEStronglyMeasurable g P) (hg' : AEStronglyMeasurable g' P)
    {δJ δg Mg MJ' : ℝ} (hδJ : 0 ≤ δJ) (hδg : 0 ≤ δg) (hMg : 0 ≤ Mg) (hMJ' : 0 ≤ MJ')
    (hdJ : eLpNorm (fun ω => J ω - J' ω) 2 P ≤ ENNReal.ofReal δJ)
    (hdg : eLpNorm (fun ω => g ω - g' ω) 2 P ≤ ENNReal.ofReal δg)
    (hg2 : eLpNorm g 2 P ≤ ENNReal.ofReal Mg) (hJ2' : eLpNorm J' 2 P ≤ ENNReal.ofReal MJ') :
    ‖bochTensor21 P J g - bochTensor21 P J' g'‖ ≤ δJ * Mg + MJ' * δg := by
  obtain ⟨i1, b1⟩ : Integrable (fun ω => ‖J ω - J' ω‖ * ‖g ω‖) P ∧
      ∫ ω, ‖J ω - J' ω‖ * ‖g ω‖ ∂P ≤ δJ * Mg :=
    m_holder22 (f := fun ω => J ω - J' ω) (hJ.sub hJ') hg hδJ hMg hdJ hg2
  obtain ⟨i2, b2⟩ : Integrable (fun ω => ‖J' ω‖ * ‖g ω - g' ω‖) P ∧
      ∫ ω, ‖J' ω‖ * ‖g ω - g' ω‖ ∂P ≤ MJ' * δg :=
    m_holder22 (g := fun ω => g ω - g' ω) hJ' (hg.sub hg') hMJ' hδg hJ2' hdg
  refine (norm_bochTensor21_sub_le_proof P hJ hJ' hg hg' i1 i2).trans ?_
  rw [integral_add i1 i2]
  linarith

end Combined

end HRS.MC.E214M
end
