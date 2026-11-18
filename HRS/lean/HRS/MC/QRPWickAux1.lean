import HRS.MC.QRVocab
import HRS.Prob.Gaussian

/-!
# QRPWick, auxiliary file 1: fourth moments of Gaussian linear spaces (Wick pairing)

For a linear space `S` of real random variables in which every element is a centred real Gaussian, the fourth moment
`E[ABCD] = E[AB]E[CD] + E[AC]E[BD] + E[AD]E[BC]` (Isserlis) follows from `E W⁴ = 3 (E W²)²` by polarisation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MC.QRSpec.Wick

section Gauss

variable {Ω : Type} [MeasurableSpace Ω]

lemma qrpw_m4 (v : ℝ≥0) : ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  set c : ℝ := Real.sqrt v with hc
  have hmap : gaussianReal 0 v = (gaussianReal 0 1).map (c * ·) := by
    rw [gaussianReal_map_const_mul]
    have : (NNReal.mk (c ^ 2) (sq_nonneg _)) * 1 = v := by
      ext; simp [hc]
    simp [this]
  rw [hmap, integral_map (by fun_prop) (by fun_prop)]
  have : ∀ x : ℝ, (c * x) ^ 4 = c ^ 4 * x ^ 4 := fun x => by ring
  simp_rw [this]
  rw [integral_const_mul, HRS.gauss_m4]
  have h2 : c ^ 2 = (v : ℝ) := by simp [hc]
  have : c ^ 4 = ((v : ℝ)) ^ 2 := by rw [← h2]; ring
  rw [this]; ring

/-- A centred Gaussian real variable has `E Y⁴ = 3 (E Y²)²` and lies in `L⁴`. -/
lemma qrpw_gauss4 {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : HasGaussianLaw Y P)
    (h0 : ∫ ω, Y ω ∂P = 0) :
    MemLp Y 4 P ∧ ∫ ω, Y ω ^ 4 ∂P = 3 * (∫ ω, Y ω ^ 2 ∂P) ^ 2 := by
  have h4 : MemLp Y 4 P := hY.memLp (by norm_num)
  refine ⟨h4, ?_⟩
  have h2 : MemLp Y 2 P := hY.memLp_two
  have hmap := hY.map_eq_gaussianReal
  have hm : P[Y] = 0 := h0
  rw [hm] at hmap
  have hvar : ProbabilityTheory.variance Y P = ∫ ω, Y ω ^ 2 ∂P := by
    rw [variance_eq_sub h2, h0]; simp
  have hnn : 0 ≤ ProbabilityTheory.variance Y P := variance_nonneg _ _
  have e4 : ∫ ω, Y ω ^ 4 ∂P = ∫ x : ℝ, x ^ 4 ∂(P.map Y) := by
    rw [integral_map hY.aemeasurable (by fun_prop)]
  rw [e4, hmap, qrpw_m4, Real.coe_toNNReal _ hnn, hvar]

end Gauss

section Wick

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma qrpw_int4 {W : Ω → ℝ} (hW : MemLp W 4 P) : Integrable (fun ω => W ω ^ 4) P := by
  have := hW.integrable_norm_pow (by norm_num)
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs]
  exact (by norm_num : Even 4).pow_abs _

lemma qrpw_memLp2_mul {A B : Ω → ℝ} (hA : MemLp A 4 P) (hB : MemLp B 4 P) :
    MemLp (fun ω => A ω * B ω) 2 P := by
  have := hA.mul hB (r := 2)
  exact this

lemma qrpw_int_mul {A B : Ω → ℝ} (hA : MemLp A 4 P) (hB : MemLp B 4 P) :
    Integrable (fun ω => A ω * B ω) P :=
  (qrpw_memLp2_mul hA hB).integrable (by norm_num)

lemma qrpw_int_mul4 {A B C D : Ω → ℝ} (hA : MemLp A 4 P) (hB : MemLp B 4 P) (hC : MemLp C 4 P)
    (hD : MemLp D 4 P) : Integrable (fun ω => A ω * B ω * (C ω * D ω)) P :=
  (qrpw_memLp2_mul hA hB).integrable_mul (qrpw_memLp2_mul hC hD)

/-- Every element of the linear space `S` is in `L⁴` and has the Gaussian fourth moment. -/
def QrpwG4 (P : Measure Ω) (S : Submodule ℝ (Ω → ℝ)) : Prop :=
  ∀ W ∈ S, MemLp W 4 P ∧ ∫ ω, W ω ^ 4 ∂P = 3 * (∫ ω, W ω ^ 2 ∂P) ^ 2

lemma qrpw_int_sq {A : Ω → ℝ} (hA : MemLp A 4 P) : Integrable (fun ω => A ω ^ 2) P := by
  simpa [sq] using qrpw_int_mul hA hA

lemma qrpw_int_sqsq {U V : Ω → ℝ} (hU : MemLp U 4 P) (hV : MemLp V 4 P) :
    Integrable (fun ω => U ω ^ 2 * V ω ^ 2) P := by
  simpa [sq] using qrpw_int_mul4 hU hU hV hV

lemma qrpw_Bexp {X Y Z W : Ω → ℝ} (hX : MemLp X 4 P) (hY : MemLp Y 4 P) (hZ : MemLp Z 4 P)
    (hW : MemLp W 4 P) (s t : ℝ) :
    ∫ ω, (X ω + s * Y ω) * (Z ω + t * W ω) ∂P =
      ∫ ω, X ω * Z ω ∂P + t * ∫ ω, X ω * W ω ∂P + s * ∫ ω, Y ω * Z ω ∂P +
        s * t * ∫ ω, Y ω * W ω ∂P := by
  have e : (fun ω => (X ω + s * Y ω) * (Z ω + t * W ω)) =
      fun ω => X ω * Z ω + t * (X ω * W ω) + s * (Y ω * Z ω) + (s * t) * (Y ω * W ω) := by
    funext ω; ring
  rw [e, integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_const_mul]
  · exact qrpw_int_mul hX hZ
  · exact (qrpw_int_mul hX hW).const_mul _
  · exact (qrpw_int_mul hX hZ).add ((qrpw_int_mul hX hW).const_mul _)
  · exact (qrpw_int_mul hY hZ).const_mul _
  · exact ((qrpw_int_mul hX hZ).add ((qrpw_int_mul hX hW).const_mul _)).add
      ((qrpw_int_mul hY hZ).const_mul _)
  · exact (qrpw_int_mul hY hW).const_mul _

lemma qrpw_sq_sq {S : Submodule ℝ (Ω → ℝ)} (hS : QrpwG4 P S) {U V : Ω → ℝ} (hU : U ∈ S)
    (hV : V ∈ S) :
    ∫ ω, U ω ^ 2 * V ω ^ 2 ∂P =
      (∫ ω, U ω ^ 2 ∂P) * (∫ ω, V ω ^ 2 ∂P) + 2 * (∫ ω, U ω * V ω ∂P) ^ 2 := by
  have hp := hS _ (add_mem hU hV)
  have hm := hS _ (sub_mem hU hV)
  have h1 := hS _ hU
  have h2 := hS _ hV
  have iU2 := qrpw_int_sq h1.1
  have iV2 := qrpw_int_sq h2.1
  have iUV := qrpw_int_mul h1.1 h2.1
  have sp : ∫ ω, (U ω + V ω) ^ 2 ∂P =
      (∫ ω, U ω ^ 2 ∂P) + 2 * (∫ ω, U ω * V ω ∂P) + ∫ ω, V ω ^ 2 ∂P := by
    have e : (fun ω => (U ω + V ω) ^ 2) = fun ω => U ω ^ 2 + 2 * (U ω * V ω) + V ω ^ 2 := by
      funext ω; ring
    have i1 : Integrable (fun ω => U ω ^ 2 + 2 * (U ω * V ω)) P := iU2.add (iUV.const_mul 2)
    rw [e, integral_add i1 iV2, integral_add iU2 (iUV.const_mul 2), integral_const_mul]
  have sm : ∫ ω, (U ω - V ω) ^ 2 ∂P =
      (∫ ω, U ω ^ 2 ∂P) - 2 * (∫ ω, U ω * V ω ∂P) + ∫ ω, V ω ^ 2 ∂P := by
    have e : (fun ω => (U ω - V ω) ^ 2) = fun ω => U ω ^ 2 - 2 * (U ω * V ω) + V ω ^ 2 := by
      funext ω; ring
    have i1 : Integrable (fun ω => U ω ^ 2 - 2 * (U ω * V ω)) P := iU2.sub (iUV.const_mul 2)
    rw [e, integral_add i1 iV2, integral_sub iU2 (iUV.const_mul 2), integral_const_mul]
  have ip : Integrable (fun ω => (U ω + V ω) ^ 4) P := qrpw_int4 hp.1
  have im : Integrable (fun ω => (U ω - V ω) ^ 4) P := qrpw_int4 hm.1
  have iU4 := qrpw_int4 h1.1
  have iV4 := qrpw_int4 h2.1
  have key : (fun ω => 12 * (U ω ^ 2 * V ω ^ 2)) = fun ω =>
      ((U ω + V ω) ^ 4 + (U ω - V ω) ^ 4) - (2 * U ω ^ 4 + 2 * V ω ^ 4) := by
    funext ω; ring
  have hint : ∫ ω, 12 * (U ω ^ 2 * V ω ^ 2) ∂P =
      (∫ ω, (U ω + V ω) ^ 4 ∂P) + (∫ ω, (U ω - V ω) ^ 4 ∂P) -
        (2 * ∫ ω, U ω ^ 4 ∂P + 2 * ∫ ω, V ω ^ 4 ∂P) := by
    have j1 : Integrable (fun ω => (U ω + V ω) ^ 4 + (U ω - V ω) ^ 4) P := ip.add im
    have j2 : Integrable (fun ω => 2 * U ω ^ 4 + 2 * V ω ^ 4) P :=
      (iU4.const_mul 2).add (iV4.const_mul 2)
    rw [key, integral_sub j1 j2, integral_add ip im,
      integral_add (iU4.const_mul 2) (iV4.const_mul 2), integral_const_mul, integral_const_mul]
  rw [integral_const_mul] at hint
  have e4p : ∫ ω, (U ω + V ω) ^ 4 ∂P = 3 * (∫ ω, (U ω + V ω) ^ 2 ∂P) ^ 2 := hp.2
  have e4m : ∫ ω, (U ω - V ω) ^ 4 ∂P = 3 * (∫ ω, (U ω - V ω) ^ 2 ∂P) ^ 2 := hm.2
  rw [e4p, e4m, h1.2, h2.2, sp, sm] at hint
  linear_combination (1 / 12 : ℝ) * hint

lemma qrpw_Bsq {S : Submodule ℝ (Ω → ℝ)} (hS : QrpwG4 P S) {A B : Ω → ℝ} (hA : A ∈ S)
    (hB : B ∈ S) (s : ℝ) :
    ∫ ω, (A ω + s * B ω) ^ 2 ∂P =
      ∫ ω, A ω ^ 2 ∂P + 2 * s * ∫ ω, A ω * B ω ∂P + s ^ 2 * ∫ ω, B ω ^ 2 ∂P := by
  have h := qrpw_Bexp (hS _ hA).1 (hS _ hB).1 (hS _ hA).1 (hS _ hB).1 s s
  have e1 : ∫ ω, B ω * A ω ∂P = ∫ ω, A ω * B ω ∂P := by simp_rw [mul_comm (B _) (A _)]
  simp only [← sq] at h
  rw [e1] at h
  rw [h]; ring

lemma qrpw_pair {S : Submodule ℝ (Ω → ℝ)} (hS : QrpwG4 P S) {A B C D : Ω → ℝ} (hA : A ∈ S)
    (hB : B ∈ S) (hC : C ∈ S) (hD : D ∈ S) (s t : ℝ) :
    ∫ ω, (A ω + s * B ω) ^ 2 * (C ω + t * D ω) ^ 2 ∂P =
      (∫ ω, A ω ^ 2 ∂P + 2 * s * ∫ ω, A ω * B ω ∂P + s ^ 2 * ∫ ω, B ω ^ 2 ∂P) *
        (∫ ω, C ω ^ 2 ∂P + 2 * t * ∫ ω, C ω * D ω ∂P + t ^ 2 * ∫ ω, D ω ^ 2 ∂P) +
      2 * (∫ ω, A ω * C ω ∂P + t * ∫ ω, A ω * D ω ∂P + s * ∫ ω, B ω * C ω ∂P +
        s * t * ∫ ω, B ω * D ω ∂P) ^ 2 := by
  have hU : (fun ω => A ω + s * B ω) ∈ S := add_mem hA (Submodule.smul_mem S s hB)
  have hV : (fun ω => C ω + t * D ω) ∈ S := add_mem hC (Submodule.smul_mem S t hD)
  have h := qrpw_sq_sq hS hU hV
  rw [qrpw_Bsq hS hA hB s, qrpw_Bsq hS hC hD t,
    qrpw_Bexp (hS _ hA).1 (hS _ hB).1 (hS _ hC).1 (hS _ hD).1 s t] at h
  exact h

/-- Isserlis / Wick pairing in a Gaussian linear space. -/
lemma qrpw_wick4 {S : Submodule ℝ (Ω → ℝ)} (hS : QrpwG4 P S) {A B C D : Ω → ℝ} (hA : A ∈ S)
    (hB : B ∈ S) (hC : C ∈ S) (hD : D ∈ S) :
    ∫ ω, A ω * B ω * (C ω * D ω) ∂P =
      (∫ ω, A ω * B ω ∂P) * (∫ ω, C ω * D ω ∂P) + (∫ ω, A ω * C ω ∂P) * (∫ ω, B ω * D ω ∂P) +
        (∫ ω, A ω * D ω ∂P) * (∫ ω, B ω * C ω ∂P) := by
  have mem : ∀ (X Y : Ω → ℝ), X ∈ S → Y ∈ S → ∀ u : ℝ, (fun ω => X ω + u * Y ω) ∈ S :=
    fun X Y hX hY u => add_mem hX (Submodule.smul_mem S u hY)
  have I : ∀ (u v : ℝ), Integrable (fun ω => (A ω + u * B ω) ^ 2 * (C ω + v * D ω) ^ 2) P :=
    fun u v => qrpw_int_sqsq (hS _ (mem A B hA hB u)).1 (hS _ (mem C D hC hD v)).1
  have e : (fun ω => 16 * (A ω * B ω * (C ω * D ω))) = fun ω =>
      (((A ω + 1 * B ω) ^ 2 * (C ω + 1 * D ω) ^ 2 - (A ω + (-1) * B ω) ^ 2 * (C ω + 1 * D ω) ^ 2) -
        ((A ω + 1 * B ω) ^ 2 * (C ω + (-1) * D ω) ^ 2 -
          (A ω + (-1) * B ω) ^ 2 * (C ω + (-1) * D ω) ^ 2)) := by
    funext ω; ring
  have h16 : ∫ ω, 16 * (A ω * B ω * (C ω * D ω)) ∂P =
      ((∫ ω, (A ω + 1 * B ω) ^ 2 * (C ω + 1 * D ω) ^ 2 ∂P -
        ∫ ω, (A ω + (-1) * B ω) ^ 2 * (C ω + 1 * D ω) ^ 2 ∂P) -
      (∫ ω, (A ω + 1 * B ω) ^ 2 * (C ω + (-1) * D ω) ^ 2 ∂P -
        ∫ ω, (A ω + (-1) * B ω) ^ 2 * (C ω + (-1) * D ω) ^ 2 ∂P)) := by
    have j1 : Integrable (fun ω => (A ω + 1 * B ω) ^ 2 * (C ω + 1 * D ω) ^ 2 -
        (A ω + (-1) * B ω) ^ 2 * (C ω + 1 * D ω) ^ 2) P := (I 1 1).sub (I (-1) 1)
    have j2 : Integrable (fun ω => (A ω + 1 * B ω) ^ 2 * (C ω + (-1) * D ω) ^ 2 -
        (A ω + (-1) * B ω) ^ 2 * (C ω + (-1) * D ω) ^ 2) P := (I 1 (-1)).sub (I (-1) (-1))
    rw [e, integral_sub j1 j2, integral_sub (I 1 1) (I (-1) 1),
      integral_sub (I 1 (-1)) (I (-1) (-1))]
  rw [integral_const_mul, qrpw_pair hS hA hB hC hD, qrpw_pair hS hA hB hC hD,
    qrpw_pair hS hA hB hC hD, qrpw_pair hS hA hB hC hD] at h16
  have e1 : ∫ ω, B ω * A ω ∂P = ∫ ω, A ω * B ω ∂P := by simp_rw [mul_comm (B _) (A _)]
  linear_combination (1 / 16 : ℝ) * h16

end Wick

end HRS.MC.QRSpec.Wick

end
