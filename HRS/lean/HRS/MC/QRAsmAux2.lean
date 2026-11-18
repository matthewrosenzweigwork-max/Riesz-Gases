import HRS.MC.QRVocab
import HRS.MC.QRAsmAux1
import HRS.Equilibrium.FieldSingAux

/-!
# QRAsm, auxiliary file 2: the mode-level combination and Minkowski over Fourier modes
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace HRS.MC.QRSpec.Asm

variable {Ω : Type} [MeasurableSpace Ω]

/-- The mode-level estimate: `Q - Qs = (Q - sec X) - (Qs - sec Y) + (sec X - sec Y)`. -/
lemma asm_mode_gen {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type*} (A : ι → ι → ℝ)
    (F : Finset ι) (X Y : ι → Ω → ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hXm : ∀ a, AEStronglyMeasurable (X a) P) (hYm : ∀ a, AEStronglyMeasurable (Y a) P)
    (δ ξ ζ : ι → ℝ) (hδ0 : ∀ a, 0 ≤ δ a) (hξ0 : ∀ a, 0 ≤ ξ a) (hζ0 : ∀ a, 0 ≤ ζ a)
    (hδ : ∀ a, eLpNorm (fun ω => X a ω - Y a ω) (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal (δ a))
    (hξ : ∀ a, eLpNorm (X a) (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal (ξ a))
    (hζ : ∀ a, eLpNorm (Y a) (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal (ζ a))
    (Q Qs : Ω → ℝ) (T T' : ℝ) (hT : 0 ≤ T) (hT' : 0 ≤ T')
    (h1 : eLpNorm (fun ω => Q ω - asmSec P A X F ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal T)
    (h2 : eLpNorm (fun ω => Qs ω - asmSec P A Y F ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal T') :
    eLpNorm (fun ω => Q ω - Qs ω) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (T + T' + ∑ a ∈ F, ∑ b ∈ F, |A a b| * (δ a * ξ b + ζ a * δ b)) := by
  have h1p : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hS := asm_sec_diff_bound (P := P) A F X Y hp hXm hYm δ ξ ζ hδ0 hξ0 hζ0 hδ hξ hζ
  have hS0 : 0 ≤ ∑ a ∈ F, ∑ b ∈ F, |A a b| * (δ a * ξ b + ζ a * δ b) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => mul_nonneg (abs_nonneg _)
      (add_nonneg (mul_nonneg (hδ0 a) (hξ0 b)) (mul_nonneg (hζ0 a) (hδ0 b)))
  have e : (fun ω => Q ω - Qs ω) = fun ω => ((Q ω - asmSec P A X F ω) - (Qs ω - asmSec P A Y F ω)) +
      (asmSec P A X F ω - asmSec P A Y F ω) := by
    funext ω; ring
  rw [e, ENNReal.ofReal_add (add_nonneg hT hT') hS0, ENNReal.ofReal_add hT hT']
  refine (eLpNorm_add_le (f := fun ω => (Q ω - asmSec P A X F ω) - (Qs ω - asmSec P A Y F ω))
    (g := fun ω => asmSec P A X F ω - asmSec P A Y F ω) h1p).trans ?_
  refine add_le_add ?_ hS
  exact (eLpNorm_sub_le (f := fun ω => Q ω - asmSec P A X F ω)
    (g := fun ω => Qs ω - asmSec P A Y F ω) h1p).trans (add_le_add h1 h2)

section Er

variable {d : ℕ} {r : ℝ}

lemma asm_fc_abs_le (F : NegSobolev d r) (k : NonzeroLattice d) :
    |NegSobolev.fourierCoeff F k| ≤ Lattice.jp k.1 ^ r * ‖F‖ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (F : lp (fun _ : NonzeroLattice d => ℝ) 2) k
  have hj : 0 < Lattice.jp k.1 ^ r := Real.rpow_pos_of_pos (Torus.jp_pos k.1) r
  unfold NegSobolev.fourierCoeff
  rw [abs_mul, abs_of_pos hj]
  refine mul_le_mul_of_nonneg_left ?_ hj.le
  rw [Real.norm_eq_abs] at h
  exact h

lemma asm_meas_fc {Z : Ω → NegSobolev d r} (hZ : Measurable Z) (k : NonzeroLattice d) :
    Measurable fun ω => NegSobolev.fourierCoeff (Z ω) k :=
  ((HRS.FieldSingAux.coordCLM r k).continuous.measurable).comp hZ

/-- Minkowski in `L^{q/2}` over the Fourier modes: `‖ ‖Z‖_{E_r} ‖_{L^q} ≤ (∑_k w_k m_k²)^{1/2}` whenever
`‖Ẑ_k‖_{L^q} ≤ m_k`. -/
lemma asm_er_norm {P : Measure Ω} [IsProbabilityMeasure P] (Z : Ω → NegSobolev d r)
    (hZm : Measurable Z) {q : ℝ} (hq : 2 ≤ q) (m : NonzeroLattice d → ℝ) (hm0 : ∀ k, 0 ≤ m k)
    (hm : ∀ k, eLpNorm (fun ω => NegSobolev.fourierCoeff (Z ω) k) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal (m k))
    (hsum : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-2 * r) * m k ^ 2) :
    eLpNorm (fun ω => ‖Z ω‖) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal (Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * r) * m k ^ 2)) := by
  set w : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-2 * r) with hw
  set W : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * r) * m k ^ 2 with hW
  have hw0 : ∀ k, 0 ≤ w k := fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hW0 : 0 ≤ W := tsum_nonneg fun k => mul_nonneg (hw0 k) (sq_nonneg _)
  have hwZ : ∀ (F : NegSobolev d r) k, w k * NegSobolev.fourierCoeff F k ^ 2 =
      NegSobolev.coord F k ^ 2 := by
    intro F k
    have hj := Torus.jp_pos k.1
    simp only [hw, NegSobolev.fourierCoeff]
    rw [mul_pow, Torus.jp_rpow_sq, ← mul_assoc, ← Real.rpow_add hj]
    simp
  have hT : ∀ ω, HasSum (fun k => w k * NegSobolev.fourierCoeff (Z ω) k ^ 2) (‖Z ω‖ ^ 2) := by
    intro ω
    obtain ⟨h1, h2⟩ := NegSobolev.coord_sq (Z ω)
    rw [h2]
    simp only [hwZ]
    exact h1.hasSum
  have hTm : AEStronglyMeasurable (fun ω => ‖Z ω‖ ^ 2) P :=
    (hZm.norm.pow_const 2).aestronglyMeasurable
  have hNm : AEStronglyMeasurable (fun ω => ‖Z ω‖) P := hZm.norm.aestronglyMeasurable
  have hspos : 0 < q / 2 := by linarith
  have hs1 : 1 ≤ ENNReal.ofReal (q / 2) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hterm : ∀ k, eLpNorm (fun ω => w k * NegSobolev.fourierCoeff (Z ω) k ^ 2)
      (ENNReal.ofReal (q / 2)) P ≤ ENNReal.ofReal (w k * m k ^ 2) := by
    intro k
    have e : (fun ω => w k * NegSobolev.fourierCoeff (Z ω) k ^ 2) =
        w k • (fun ω => NegSobolev.fourierCoeff (Z ω) k ^ 2) := by
      funext ω; simp
    rw [e, eLpNorm_const_smul, GaussEr.qrpg_sq_eLpNorm (asm_meas_fc hZm k).aestronglyMeasurable hspos,
      show 2 * (q / 2) = q by ring, Real.enorm_eq_ofReal (hw0 k)]
    calc ENNReal.ofReal (w k) * eLpNorm (fun ω => NegSobolev.fourierCoeff (Z ω) k)
          (ENNReal.ofReal q) P ^ 2 ≤ ENNReal.ofReal (w k) * ENNReal.ofReal (m k) ^ 2 :=
          mul_le_mul' le_rfl (pow_le_pow_left' (hm k) 2)
      _ = ENNReal.ofReal (w k * m k ^ 2) := by
          rw [ENNReal.ofReal_mul (hw0 k), ENNReal.ofReal_pow (hm0 k)]
  have hmk : eLpNorm (fun ω => ‖Z ω‖ ^ 2) (ENNReal.ofReal (q / 2)) P ≤ ENNReal.ofReal W := by
    refine Lp.eLpNorm_le_of_ae_tendsto (u := Filter.atTop)
      (f := fun F : Finset (NonzeroLattice d) => fun ω =>
        ∑ k ∈ F, w k * NegSobolev.fourierCoeff (Z ω) k ^ 2)
      (Filter.Eventually.of_forall fun F => ?_) (fun F => ?_) hTm
      (Filter.Eventually.of_forall fun ω => hT ω)
    · refine (asm_eLpNorm_sum_le F _ hs1).trans ?_
      refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
      rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hw0 k) (sq_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (hsum.sum_le_tsum F fun k _ => mul_nonneg (hw0 k) (sq_nonneg _))
    · have e : (fun ω => ∑ k ∈ F, w k * NegSobolev.fourierCoeff (Z ω) k ^ 2) =
          ∑ k ∈ F, (fun ω => w k * NegSobolev.fourierCoeff (Z ω) k ^ 2) := by
        funext ω; simp [Finset.sum_apply]
      rw [e]
      exact Finset.aestronglyMeasurable_sum F fun k _ =>
        (((asm_meas_fc hZm k).pow_const 2).const_mul (w k)).aestronglyMeasurable
  have hsq := GaussEr.qrpg_sq_eLpNorm hNm (s := q / 2) hspos
  rw [show 2 * (q / 2) = q by ring] at hsq
  have hsq' : eLpNorm (fun ω => ‖Z ω‖) (ENNReal.ofReal q) P ^ 2 ≤
      ENNReal.ofReal (Real.sqrt W) ^ 2 := by
    rw [← hsq]
    refine hmk.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hW0]
  by_contra hcon
  rw [not_le] at hcon
  exact absurd hsq' (not_le.mpr (ENNReal.pow_lt_pow_left two_ne_zero hcon))

end Er

end HRS.MC.QRSpec.Asm

end
