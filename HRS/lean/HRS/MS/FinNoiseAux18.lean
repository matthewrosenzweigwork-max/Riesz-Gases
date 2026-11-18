import HRS.MS.FinNoiseAux17
import HRS.MS.SpecAux10

/-!
# S8.6 `finite_noise`: symmetric roots against a diagonally bounded reference (S86)

`s86_root_cmp`: if `D ≥ c D₀` with `D₀` positive diagonal in the Hilbert basis `e₀`, `C, D` are trace-class forms
with symmetric nonnegative roots `S, Sb`, then
`‖S - Sb‖²_HS (computed along e₀) ≤ 4 c⁻¹ 𝒬_{D₀}(C - D)` (`𝒬_{D₀}` the reference-relative quadratic form).
Route: eigenbasis `b` of `D` (`s86_form_eigenbasis`), `s8p_psd_root_relative` in `b`, comparison
`relQuad_le_of_cmp`, and basis independence of the Hilbert-Schmidt norm of a symmetric operator.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS HRS.HilbertCLTAux HRS.Uniform

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem s86_hs_basis_change {ι κ : Type*} (b : HilbertBasis ι ℝ H) (e : HilbertBasis κ ℝ H)
    (T : H →L[ℝ] H) (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y)) :
    ∑' j, ENNReal.ofReal (‖T (b j)‖ ^ 2) = ∑' k, ENNReal.ofReal (‖T (e k)‖ ^ 2) := by
  have h1 : ∀ (b : HilbertBasis ι ℝ H) (e : HilbertBasis κ ℝ H) j,
      ENNReal.ofReal (‖T (b j)‖ ^ 2) = ∑' k, ENNReal.ofReal (inner ℝ (b j : H) (T (e k)) ^ 2) := by
    intro b e j
    have := hasSum_inner_sq e (T (b j))
    rw [← this.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) this.summable]
    refine tsum_congr fun k => ?_
    rw [real_inner_comm, ← hT, real_inner_comm]
  calc ∑' j, ENNReal.ofReal (‖T (b j)‖ ^ 2)
      = ∑' j, ∑' k, ENNReal.ofReal (inner ℝ (b j : H) (T (e k)) ^ 2) := tsum_congr (h1 b e)
    _ = ∑' k, ∑' j, ENNReal.ofReal (inner ℝ (b j : H) (T (e k)) ^ 2) := ENNReal.tsum_comm
    _ = ∑' k, ENNReal.ofReal (‖T (e k)‖ ^ 2) := by
        refine tsum_congr fun k => ?_
        have := hasSum_inner_sq b (T (e k))
        rw [← this.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) this.summable]
        refine tsum_congr fun j => ?_
        rw [real_inner_comm]

theorem s86_root_on_eigen {D : H →L[ℝ] H →L[ℝ] ℝ} {Sb : H →L[ℝ] H} (hSb : IsSqrtOfForm Sb D)
    {x : H} {lam : ℝ} (hlam : 0 < lam) (hx : ∀ y, D x y = lam * inner ℝ x y) :
    Sb x = Real.sqrt lam • x := by
  set e : ℝ := Real.sqrt lam with he
  have he0 : 0 < e := Real.sqrt_pos.2 hlam
  have hee : e * e = lam := Real.mul_self_sqrt hlam.le
  have h1 : Sb (Sb x) = lam • x := by
    refine ext_inner_right ℝ fun y => ?_
    rw [hSb.symm, hSb.sq, hx, inner_smul_left]; simp
  set v : H := Sb x - e • x with hv
  have h2 : Sb v = -e • v := by
    have : Sb v = Sb (Sb x) - e • Sb x := by simp [hv]
    rw [this, h1, hv, ← hee]
    module
  have h3 := hSb.nonneg v
  rw [h2, inner_smul_left, real_inner_self_eq_norm_sq] at h3
  simp only [conj_trivial] at h3
  have h4 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
  have : v = 0 := by simpa using h4
  exact sub_eq_zero.1 this


theorem s86_root_cmp {κ : Type*} (e₀ : HilbertBasis κ ℝ H) (dd₀ : κ → ℝ) (hdd₀ : ∀ i, 0 < dd₀ i)
    {D₀ C D : H →L[ℝ] H →L[ℝ] ℝ} (hD₀e : ∀ i y, D₀ (e₀ i) y = dd₀ i * inner ℝ (e₀ i : H) y)
    {c : ℝ} (hc : 0 < c) (hcD : ∀ x, c * D₀ x x ≤ D x x)
    (hC : IsTraceClassCov C) (hD : IsTraceClassCov D) {S Sb : H →L[ℝ] H}
    (hS : IsSqrtOfForm S C) (hSb : IsSqrtOfForm Sb D) :
    ∑' j, ENNReal.ofReal (‖(S - Sb) (e₀ j)‖ ^ 2) ≤
      4 * ENNReal.ofReal c⁻¹ * relQuad e₀ dd₀ (C - D) := by
  classical
  obtain ⟨ι, b, lam, hlam, hDb⟩ := s86_form_eigenbasis e₀ dd₀ hdd₀ hD₀e hc hcD hD
  set eb : ι → ℝ := fun i => Real.sqrt (lam i) with hebdef
  have heb : ∀ i, 0 < eb i := fun i => Real.sqrt_pos.2 (hlam i)
  have heb2 : ∀ i, eb i ^ 2 = lam i := fun i => Real.sq_sqrt (hlam i).le
  have hSbb : ∀ i, Sb (b i) = eb i • b i := fun i => s86_root_on_eigen hSb (hlam i) (hDb i)
  obtain ⟨tC, hCt, -⟩ := hC.hasSum_basis b
  obtain ⟨tD, hDt, -⟩ := hD.hasSum_basis b
  have hsq : Summable fun j => ‖S (b j)‖ ^ 2 := by
    refine hCt.summable.congr fun j => ?_
    rw [← real_inner_self_eq_norm_sq]; exact (hS.sq _ _).symm
  have heHS : Summable fun j => eb j ^ 2 := by
    refine hDt.summable.congr fun j => ?_
    rw [heb2, hDb j (b j)]
    have := b.orthonormal.1 j
    simp [real_inner_self_eq_norm_sq, this]
  have key := HRS.MS.Spec.s8p_psd_root_relative S hS.symm hS.nonneg eb heb b hsq heHS
  have hL : ∑' j, ENNReal.ofReal (‖(S - Sb) (b j)‖ ^ 2) =
      ∑' j, ENNReal.ofReal (‖S (b j) - eb j • b j‖ ^ 2) := by
    refine tsum_congr fun j => ?_
    simp only [sub_apply, hSbb]
  have hR : ∑' p : ι × ι, ENNReal.ofReal
      ((inner ℝ (S (b p.1)) (S (b p.2)) - (if p.1 = p.2 then eb p.1 ^ 2 else 0)) ^ 2 /
        (eb p.1 ^ 2 + eb p.2 ^ 2)) = relQuad b lam (C - D) := by
    unfold relQuad
    refine tsum_congr fun p => ?_
    congr 1
    rw [heb2, heb2, hS.sq]
    have hbo : inner ℝ (b p.1 : H) (b p.2) = if p.1 = p.2 then 1 else 0 :=
      orthonormal_iff_ite.1 b.orthonormal p.1 p.2
    have : (C - D) (b p.1) (b p.2) = C (b p.1) (b p.2) - (if p.1 = p.2 then lam p.1 else 0) := by
      simp only [_root_.sub_apply, hDb p.1 (b p.2), hbo]
      split_ifs <;> simp
    rw [this]
  have hsymm : ∀ x y, (C - D) x y = (C - D) y x := fun x y => by
    simp only [_root_.sub_apply, hC.symm x y, hD.symm x y]
  have hTs : ∀ x y, inner ℝ ((S - Sb) x) y = inner ℝ x ((S - Sb) y) := fun x y => by
    simp only [sub_apply, inner_sub_left, inner_sub_right, hS.symm, hSb.symm]
  rw [← s86_hs_basis_change b e₀ (S - Sb) hTs, hL]
  refine key.trans ?_
  rw [hR]
  have hcmp := HRS.Uniform.RelCov.relQuad_le_of_cmp b e₀ lam hlam D hDb dd₀ hdd₀ D₀ hD₀e c hc hcD (C - D) hsymm
  calc (4 : ℝ≥0∞) * relQuad b lam (C - D)
      ≤ 4 * (ENNReal.ofReal c⁻¹ * relQuad e₀ dd₀ (C - D)) := by gcongr
    _ = 4 * ENNReal.ofReal c⁻¹ * relQuad e₀ dd₀ (C - D) := by rw [mul_assoc]

end HRS.MS.FinNoise
