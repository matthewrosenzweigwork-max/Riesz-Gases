import HRS.MC.E213U18b
import HRS.MC.QRPWickAux1
import HRS.Sections.IIDAux3

/-!
# Packet e213u18 (part c): the Wick pairing of a half-Wick quadratic field with two Gaussian variables

For a half-Wick field `Q = L²-lim ½ ∑_{S×S} w_{kl}(A_kA_l - E A_kA_l)` (`w` symmetric) and `X, Y` in a Gaussian
linear space containing the `A_k`, `E[Q X Y] = lim_S ∑_{S×S} w_{kl} E[A_kX] E[A_lY]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS HRS.Sec7 HRS.MC.QRSpec.Wick

variable {d : ℕ}

section WickProb

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The finite Wick section `½ ∑_{S×S} w_{kl}(A_kA_l - E[A_kA_l])`. -/
def u18_QS (P : Measure Ω) (A : NonzeroLattice d → Ω → ℝ) (w : NonzeroLattice d → NonzeroLattice d → ℝ)
    (S : Finset (NonzeroLattice d)) (ω : Ω) : ℝ :=
  (1 / 2) * ∑ k ∈ S, ∑ l ∈ S, w k l * (A k ω * A l ω - ∫ ω', A k ω' * A l ω' ∂P)

theorem u18_QS_integral {A : NonzeroLattice d → Ω → ℝ} {w : NonzeroLattice d → NonzeroLattice d → ℝ}
    (hw : ∀ k l, w k l = w l k) {𝒢 : Submodule ℝ (Ω → ℝ)} (hG : HRS.MC.QRSpec.Wick.QrpwG4 P 𝒢)
    (hA : ∀ k, A k ∈ 𝒢) {X Y : Ω → ℝ} (hX : X ∈ 𝒢) (hY : Y ∈ 𝒢) (S : Finset (NonzeroLattice d)) :
    ∫ ω, u18_QS P A w S ω * (X ω * Y ω) ∂P =
      ∑ k ∈ S, ∑ l ∈ S, w k l * ((∫ ω, A k ω * X ω ∂P) * (∫ ω, A l ω * Y ω ∂P)) := by
  set m : NonzeroLattice d → NonzeroLattice d → ℝ := fun k l => ∫ ω', A k ω' * A l ω' ∂P with hm
  have hkl : ∀ k l, ∫ ω, (A k ω * A l ω - m k l) * (X ω * Y ω) ∂P =
      (∫ ω, A k ω * X ω ∂P) * (∫ ω, A l ω * Y ω ∂P) +
        (∫ ω, A k ω * Y ω ∂P) * (∫ ω, A l ω * X ω ∂P) := by
    intro k l
    have h4 := qrpw_wick4 hG (hA k) (hA l) hX hY
    have i1 : Integrable (fun ω => A k ω * A l ω * (X ω * Y ω)) P :=
      qrpw_int_mul4 (hG _ (hA k)).1 (hG _ (hA l)).1 (hG _ hX).1 (hG _ hY).1
    have i2 : Integrable (fun ω => X ω * Y ω) P := qrpw_int_mul (hG _ hX).1 (hG _ hY).1
    have e : (fun ω => (A k ω * A l ω - m k l) * (X ω * Y ω)) =
        fun ω => A k ω * A l ω * (X ω * Y ω) - m k l * (X ω * Y ω) := by
      funext ω; ring
    rw [e, integral_sub i1 (i2.const_mul _), integral_const_mul, h4]
    simp only [hm]
    ring
  have hint : ∀ k l, Integrable (fun ω => (A k ω * A l ω - m k l) * (X ω * Y ω)) P := by
    intro k l
    have i1 : Integrable (fun ω => A k ω * A l ω * (X ω * Y ω)) P :=
      qrpw_int_mul4 (hG _ (hA k)).1 (hG _ (hA l)).1 (hG _ hX).1 (hG _ hY).1
    have i2 : Integrable (fun ω => X ω * Y ω) P := qrpw_int_mul (hG _ hX).1 (hG _ hY).1
    have e : (fun ω => (A k ω * A l ω - m k l) * (X ω * Y ω)) =
        fun ω => A k ω * A l ω * (X ω * Y ω) - m k l * (X ω * Y ω) := by
      funext ω; ring
    rw [e]
    exact i1.sub (i2.const_mul _)
  have e1 : (fun ω => u18_QS P A w S ω * (X ω * Y ω)) =
      fun ω => (1 / 2) * ∑ k ∈ S, ∑ l ∈ S, w k l * ((A k ω * A l ω - m k l) * (X ω * Y ω)) := by
    funext ω
    unfold u18_QS
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [hm]
    ring
  rw [e1, integral_const_mul, integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun l _ =>
    (hint k l).const_mul _)]
  have e2 : ∀ k ∈ S, ∫ ω, ∑ l ∈ S, w k l * ((A k ω * A l ω - m k l) * (X ω * Y ω)) ∂P =
      ∑ l ∈ S, w k l * ((∫ ω, A k ω * X ω ∂P) * (∫ ω, A l ω * Y ω ∂P) +
        (∫ ω, A k ω * Y ω ∂P) * (∫ ω, A l ω * X ω ∂P)) := by
    intro k _
    rw [integral_finsetSum _ (fun l _ => (hint k l).const_mul _)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, hkl]
  rw [Finset.sum_congr rfl e2]
  -- symmetrise
  have e3 : ∑ k ∈ S, ∑ l ∈ S, w k l * ((∫ ω, A k ω * Y ω ∂P) * (∫ ω, A l ω * X ω ∂P)) =
      ∑ k ∈ S, ∑ l ∈ S, w k l * ((∫ ω, A k ω * X ω ∂P) * (∫ ω, A l ω * Y ω ∂P)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hw l k]; ring
  have e4 : ∑ k ∈ S, ∑ l ∈ S, w k l * ((∫ ω, A k ω * X ω ∂P) * (∫ ω, A l ω * Y ω ∂P) +
        (∫ ω, A k ω * Y ω ∂P) * (∫ ω, A l ω * X ω ∂P)) =
      2 * ∑ k ∈ S, ∑ l ∈ S, w k l * ((∫ ω, A k ω * X ω ∂P) * (∫ ω, A l ω * Y ω ∂P)) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [e3]; ring
  rw [e4]
  ring


theorem u18_enorm_sq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem u18_QS_memLp {A : NonzeroLattice d → Ω → ℝ} {w : NonzeroLattice d → NonzeroLattice d → ℝ}
    {𝒢 : Submodule ℝ (Ω → ℝ)} (hG : HRS.MC.QRSpec.Wick.QrpwG4 P 𝒢)
    (hA : ∀ k, A k ∈ 𝒢) (S : Finset (NonzeroLattice d)) : MemLp (u18_QS P A w S) 2 P := by
  have hkl : ∀ k l : NonzeroLattice d, MemLp (fun ω => w k l * (A k ω * A l ω - ∫ ω', A k ω' * A l ω' ∂P)) 2 P := by
    intro k l
    exact (MemLp.sub (qrpw_memLp2_mul (hG _ (hA k)).1 (hG _ (hA l)).1) (memLp_const _)).const_mul _
  have h2 : MemLp (fun ω => ∑ k ∈ S, ∑ l ∈ S, w k l * (A k ω * A l ω - ∫ ω', A k ω' * A l ω' ∂P)) 2 P := by
    exact memLp_finsetSum (f := fun (k : NonzeroLattice d) (ω : Ω) =>
      ∑ l ∈ S, w k l * (A k ω * A l ω - ∫ ω', A k ω' * A l ω' ∂P)) S
      (fun k _ => memLp_finsetSum (f := fun (l : NonzeroLattice d) (ω : Ω) =>
        w k l * (A k ω * A l ω - ∫ ω', A k ω' * A l ω' ∂P)) S (fun l _ => hkl k l))
  exact h2.const_mul (1 / 2)

/-- The limit statement: `E[Q X Y] = lim_S ∑_{S×S} w_{kl} E[A_kX] E[A_lY]`. -/
theorem u18_wick_limit {A : NonzeroLattice d → Ω → ℝ} {w : NonzeroLattice d → NonzeroLattice d → ℝ}
    (hw : ∀ k l, w k l = w l k) {𝒢 : Submodule ℝ (Ω → ℝ)} (hG : HRS.MC.QRSpec.Wick.QrpwG4 P 𝒢)
    (hA : ∀ k, A k ∈ 𝒢) {X Y : Ω → ℝ} (hX : X ∈ 𝒢) (hY : Y ∈ 𝒢) {Q : Ω → ℝ}
    (hQm : AEStronglyMeasurable Q P)
    (hQ : Tendsto (fun S : Finset (NonzeroLattice d) => ∫⁻ ω, ‖Q ω - u18_QS P A w S ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun S : Finset (NonzeroLattice d) =>
      ∑ k ∈ S, ∑ l ∈ S, w k l * ((∫ ω, A k ω * X ω ∂P) * (∫ ω, A l ω * Y ω ∂P))) atTop
      (𝓝 (∫ ω, Q ω * (X ω * Y ω) ∂P)) := by
  have hXY2 : MemLp (fun ω => X ω * Y ω) 2 P := qrpw_memLp2_mul (hG _ hX).1 (hG _ hY).1
  have hfm : ∀ S, AEStronglyMeasurable (fun ω => Q ω - u18_QS P A w S ω) P :=
    fun S => hQm.sub (u18_QS_memLp hG hA S).aestronglyMeasurable
  have hDreal : ∀ S, ∫ ω, (Q ω - u18_QS P A w S ω) ^ 2 ∂P =
      (∫⁻ ω, ‖Q ω - u18_QS P A w S ω‖ₑ ^ 2 ∂P).toReal := by
    intro S
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => sq_nonneg _)
      ((hfm S).pow 2)]
    simp_rw [u18_enorm_sq]
  have hDlim : Tendsto (fun S => ∫ ω, (Q ω - u18_QS P A w S ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simp_rw [hDreal]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hQ
    simpa only [Function.comp_def, ENNReal.toReal_zero] using this
  have hDmem : ∀ᶠ S : Finset (NonzeroLattice d) in atTop, MemLp (fun ω => Q ω - u18_QS P A w S ω) 2 P := by
    filter_upwards [hQ.eventually (Iio_mem_nhds (ENNReal.zero_lt_top))] with S hS
    refine (memLp_two_iff_integrable_sq (hfm S)).2 ⟨(hfm S).pow 2, ?_⟩
    have : ∫⁻ ω, ‖(Q ω - u18_QS P A w S ω) ^ 2‖ₑ ∂P = ∫⁻ ω, ‖Q ω - u18_QS P A w S ω‖ₑ ^ 2 ∂P := by
      simp_rw [enorm_pow]
    unfold HasFiniteIntegral
    rw [this]
    exact hS
  set C : ℝ := ∫ ω, (X ω * Y ω) ^ 2 ∂P with hC
  have hbound : ∀ᶠ S : Finset (NonzeroLattice d) in atTop,
      ‖(∑ k ∈ S, ∑ l ∈ S, w k l * ((∫ ω, A k ω * X ω ∂P) * (∫ ω, A l ω * Y ω ∂P))) -
        ∫ ω, Q ω * (X ω * Y ω) ∂P‖ ≤
      Real.sqrt (∫ ω, (Q ω - u18_QS P A w S ω) ^ 2 ∂P) * Real.sqrt C := by
    filter_upwards [hDmem] with S hS
    have hQS2 := u18_QS_memLp (w := w) hG hA S
    have hQ2 : MemLp Q 2 P := by
      have := hS.add hQS2
      refine this.ae_eq (Filter.Eventually.of_forall fun ω => ?_)
      simp
    have iQ : Integrable (fun ω => Q ω * (X ω * Y ω)) P := hQ2.integrable_mul hXY2
    have iS : Integrable (fun ω => u18_QS P A w S ω * (X ω * Y ω)) P := hQS2.integrable_mul hXY2
    have iF : Integrable (fun ω => (Q ω - u18_QS P A w S ω) * (X ω * Y ω)) P := hS.integrable_mul hXY2
    rw [← u18_QS_integral hw hG hA hX hY S, norm_sub_rev, Real.norm_eq_abs,
      ← integral_sub iQ iS]
    have e : ∀ ω, Q ω * (X ω * Y ω) - u18_QS P A w S ω * (X ω * Y ω) =
        (Q ω - u18_QS P A w S ω) * (X ω * Y ω) := fun ω => by ring
    simp_rw [e]
    refine (abs_integral_le_integral_abs).trans ?_
    have h1 := HRS.IID.integral_mul_le_sqrt (μ := P) (f := fun ω => |Q ω - u18_QS P A w S ω|)
      (g := fun ω => |X ω * Y ω|) (fun ω => abs_nonneg _) (fun ω => abs_nonneg _)
      (by simpa using (hfm S).norm) (by simpa using hXY2.aestronglyMeasurable.norm)
      (by simpa only [sq_abs] using hS.integrable_sq) (by simpa only [sq_abs] using hXY2.integrable_sq)
    simp only [sq_abs] at h1
    calc ∫ ω, |(Q ω - u18_QS P A w S ω) * (X ω * Y ω)| ∂P
        = ∫ ω, |Q ω - u18_QS P A w S ω| * |X ω * Y ω| ∂P := by
          congr 1; funext ω; exact abs_mul _ _
      _ ≤ _ := h1
  have hlim : Tendsto (fun S : Finset (NonzeroLattice d) =>
      Real.sqrt (∫ ω, (Q ω - u18_QS P A w S ω) ^ 2 ∂P) * Real.sqrt C) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp hDlim).mul_const (Real.sqrt C)
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Filter.Eventually.of_forall fun S => norm_nonneg _) hbound hlim

end WickProb

end HRS.MC.E213U18

end
