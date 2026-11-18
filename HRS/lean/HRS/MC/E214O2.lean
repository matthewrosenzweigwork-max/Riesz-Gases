import Mathlib
import HRS.MC.E214O1

/-!
# Packet E214O, part 2: the abstract relaxation estimate (shared by `Dwin_relax` and `Jwin_relax`)

`o_relax`: if for every `a ≥ 0` the pointwise bound
`‖Φ_a ω‖ ≤ C₁ ∫_0^{a+T} e^{-c₁(a-v)} F(v,ω) dv + C₂ e^{c₂T} e^{-min(c₂,κ) a} Σ_{k<⌈a+T⌉} Y_k(ω)`
holds a.s., with `‖F(v)‖_{L^p} ≤ C_F e^{-c_F v}` and `‖Y_k‖_{L^p} ≤ M`, then `‖Φ_a‖_{L^p} ≤ C e^{-c a}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MC.E214O

theorem o_relax {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {V : Type*} [NormedAddCommGroup V] {p : ℝ} (hp : 1 ≤ p) {T : ℝ} (hT : 0 < T)
    {C₁ c₁ C₂ c₂ κ CF cF M : ℝ} (hC₁ : 0 ≤ C₁) (hc₁ : 0 < c₁) (hC₂ : 0 ≤ C₂) (hc₂ : 0 < c₂) (hκ : 0 < κ)
    (hCF : 0 ≤ CF) (hcF : 0 < cF) (hM : 0 ≤ M)
    (F : ℝ → Ω → ℝ) (hF0 : ∀ v ω, 0 ≤ F v ω)
    (hFm : ∀ n : ℝ, AEMeasurable (fun x : Ω × ℝ => F x.2 x.1) (P.prod (volume.restrict (Set.Ioc 0 n))))
    (hF : ∀ᵐ v ∂(volume.restrict (Set.Ici (0 : ℝ))),
      eLpNorm (F v) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (CF * Real.exp (-cF * v)))
    (Y : ℕ → Ω → ℝ) (hY : ∀ k, eLpNorm (Y k) (ENNReal.ofReal p) P ≤ ENNReal.ofReal M)
    (Φ : ℝ → Ω → V) (hΦ : ∀ a, 0 ≤ a → AEStronglyMeasurable (Φ a) P)
    (hpt : ∀ a, 0 ≤ a → ∀ᵐ ω ∂P, ‖Φ a ω‖ ≤
      C₁ * (∫ v in Set.Ioc 0 (a + T), Real.exp (-c₁ * (a - v)) * F v ω) +
        C₂ * (Real.exp (c₂ * T) * Real.exp (-(min c₂ κ) * a)) * ∑ k ∈ Finset.range ⌈a + T⌉₊, Y k ω) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a →
      eLpNorm (Φ a) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (C * Real.exp (-c * a)) := by
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  set κ₁ := min c₁ cF with hκ₁
  set κ₂ := min c₂ κ with hκ₂
  set κ₀ := min κ₁ κ₂ with hκ₀
  have hκ₁p : 0 < κ₁ := lt_min hc₁ hcF
  have hκ₂p : 0 < κ₂ := lt_min hc₂ hκ
  have hκ₀p : 0 < κ₀ := lt_min hκ₁p hκ₂p
  set A₁ := C₁ * CF * Real.exp (c₁ * T) with hA₁
  set A₂ := C₂ * Real.exp (c₂ * T) * M with hA₂
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  refine ⟨(A₁ + A₂) * (2 / κ₀ + T + 1) + 1, κ₀ / 2, by positivity, by positivity, fun a ha => ?_⟩
  set n := a + T with hn
  have hnpos : 0 < n := by linarith
  set N := ⌈n⌉₊ with hN
  have hNle : (N : ℝ) ≤ n + 1 := (Nat.ceil_lt_add_one hnpos.le).le
  -- the weighted-integral term
  set B := CF * Real.exp (c₁ * T) * Real.exp (-κ₁ * a) with hB
  have hB0 : 0 ≤ B := by positivity
  have hGB : ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 n)),
      eLpNorm (fun ω => Real.exp (-c₁ * (a - v)) * F v ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal B := by
    have h1 := ae_restrict_of_ae_restrict_of_subset (show Set.Ioc (0 : ℝ) n ⊆ Set.Ici 0 from fun v hv => hv.1.le) hF
    filter_upwards [h1, ae_restrict_mem measurableSet_Ioc] with v hv hvm
    have hv0 : 0 ≤ v := hvm.1.le
    have e1 : (fun ω => Real.exp (-c₁ * (a - v)) * F v ω) = Real.exp (-c₁ * (a - v)) • F v := rfl
    rw [e1, eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.exp_pos _).le]
    calc ENNReal.ofReal (Real.exp (-c₁ * (a - v))) * eLpNorm (F v) (ENNReal.ofReal p) P
        ≤ ENNReal.ofReal (Real.exp (-c₁ * (a - v))) * ENNReal.ofReal (CF * Real.exp (-cF * v)) :=
          mul_le_mul' le_rfl hv
      _ = ENNReal.ofReal (CF * (Real.exp (-c₁ * (a - v)) * Real.exp (-cF * v))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]; congr 1; ring
      _ ≤ ENNReal.ofReal B := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := o_exp_weight_le (c := c₁) (c' := cF) (a := a) (T := T) (v := v) hc₁.le hcF.le hT.le ha hv0
            hvm.2
          calc CF * (Real.exp (-c₁ * (a - v)) * Real.exp (-cF * v))
              ≤ CF * (Real.exp (c₁ * T) * Real.exp (-κ₁ * a)) := mul_le_mul_of_nonneg_left this hCF
            _ = B := by rw [hB]; ring
  have hGm : AEMeasurable (fun x : Ω × ℝ => Real.exp (-c₁ * (a - x.2)) * F x.2 x.1)
      (P.prod (volume.restrict (Set.Ioc 0 n))) :=
    (by fun_prop : Measurable fun x : Ω × ℝ => Real.exp (-c₁ * (a - x.2))).aemeasurable.mul (hFm n)
  have hX1 := o_eLpNorm_integral_le P hnpos hp (fun v ω => Real.exp (-c₁ * (a - v)) * F v ω)
    hGm hB0 hGB
  have hY2 : eLpNorm (fun ω => ∑ k ∈ Finset.range N, Y k ω) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (N * M) := by
    have h := eLpNorm_sum_le (f := Y) (s := Finset.range N) (μ := P) hp1
    have e : (fun ω => ∑ k ∈ Finset.range N, Y k ω) = ∑ k ∈ Finset.range N, Y k := by
      funext ω; simp [Finset.sum_apply]
    rw [e]
    refine h.trans ?_
    calc ∑ k ∈ Finset.range N, eLpNorm (Y k) (ENNReal.ofReal p) P
        ≤ ∑ k ∈ Finset.range N, ENNReal.ofReal M := Finset.sum_le_sum fun k _ => hY k
      _ = ENNReal.ofReal (N * M) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg N)]
          simp
  set K := C₂ * (Real.exp (c₂ * T) * Real.exp (-κ₂ * a)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hmain : eLpNorm (Φ a) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (C₁ * (n * B)) + ENNReal.ofReal (K * (N * M)) := by
    refine (eLpNorm_mono_ae_real (hΦ a ha) (hpt a ha)).trans ?_
    refine (eLpNorm_add_le hp1).trans (add_le_add ?_ ?_)
    · have e : (fun ω => C₁ * ∫ v in Set.Ioc 0 n, Real.exp (-c₁ * (a - v)) * F v ω) =
          C₁ • (fun ω => ∫ v in Set.Ioc 0 n, Real.exp (-c₁ * (a - v)) * F v ω) := rfl
      rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal hC₁]
      exact (mul_le_mul' le_rfl hX1).trans_eq (ENNReal.ofReal_mul hC₁).symm
    · have e : (fun ω => C₂ * (Real.exp (c₂ * T) * Real.exp (-κ₂ * a)) * ∑ k ∈ Finset.range N, Y k ω) =
          K • (fun ω => ∑ k ∈ Finset.range N, Y k ω) := rfl
      rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal hK0]
      exact (mul_le_mul' le_rfl hY2).trans_eq (ENNReal.ofReal_mul hK0).symm
  refine hmain.trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e0 : Real.exp (-κ₁ * a) ≤ Real.exp (-κ₀ * a) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left κ₁ κ₂])
  have e2 : Real.exp (-κ₂ * a) ≤ Real.exp (-κ₀ * a) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right κ₁ κ₂])
  have hlin := o_lin_exp_le (κ := κ₀) (T := T) (a := a) hκ₀p hT.le ha
  have hn1 : n + 1 = a + T + 1 := by rw [hn]
  have hx : C₁ * (n * B) ≤ A₁ * (n + 1) * Real.exp (-κ₀ * a) := by
    have : C₁ * (n * B) = A₁ * n * Real.exp (-κ₁ * a) := by rw [hB, hA₁]; ring
    rw [this]
    have h1 : A₁ * n * Real.exp (-κ₁ * a) ≤ A₁ * (n + 1) * Real.exp (-κ₁ * a) := by
      have : 0 ≤ A₁ * Real.exp (-κ₁ * a) := by positivity
      nlinarith
    exact h1.trans (mul_le_mul_of_nonneg_left e0 (by positivity))
  have hy : K * (N * M) ≤ A₂ * (n + 1) * Real.exp (-κ₀ * a) := by
    have : K * (N * M) = A₂ * N * Real.exp (-κ₂ * a) := by rw [hK, hA₂]; ring
    rw [this]
    have h1 : A₂ * N * Real.exp (-κ₂ * a) ≤ A₂ * (n + 1) * Real.exp (-κ₂ * a) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNle hA₂0) (Real.exp_pos _).le
    exact h1.trans (mul_le_mul_of_nonneg_left e2 (by positivity))
  calc C₁ * (n * B) + K * (N * M) ≤ (A₁ + A₂) * (a + T + 1) * Real.exp (-κ₀ * a) := by
        rw [← hn1]; nlinarith
    _ = (A₁ + A₂) * ((a + T + 1) * Real.exp (-κ₀ * a)) := by ring
    _ ≤ (A₁ + A₂) * ((2 / κ₀ + T + 1) * Real.exp (-(κ₀ / 2) * a)) :=
        mul_le_mul_of_nonneg_left hlin (by positivity)
    _ ≤ ((A₁ + A₂) * (2 / κ₀ + T + 1) + 1) * Real.exp (-(κ₀ / 2) * a) := by
        have := Real.exp_pos (-(κ₀ / 2) * a)
        nlinarith

end HRS.MC.E214O

end
