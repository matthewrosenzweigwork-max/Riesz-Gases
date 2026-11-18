import HRS.Commutator.Torus.TPOSAux6

/-!
# T-POS helpers, part 7: the coefficients `gTcoef`

`ĝ_η(k) = tScale · η^{d-s} ĝ_1(ηk)`, decay of `φ̂`, summability and the coefficient bounds
(`tr_coef_bounds`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

lemma tposW2_mul_gen (b : ℝ) {v : ℝ} (hv : 0 < v) :
    tposW2 d v * (Real.pi ^ 2 / v) ^ (-b / 2) =
      (Real.Gamma ((d : ℝ) + 2))⁻¹ * Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (-b) *
        (v ^ ((d : ℝ) + 1 - (d : ℝ) / 2 + b / 2) * Real.exp (-v)) := by
  unfold tposW2
  have hπ : 0 < Real.pi := Real.pi_pos
  have e1 : (Real.pi / v) ^ ((d : ℝ) / 2) = Real.pi ^ ((d : ℝ) / 2) * v ^ (-((d : ℝ) / 2)) := by
    rw [Real.div_rpow hπ.le hv.le, Real.rpow_neg hv.le, div_eq_mul_inv]
  have e2 : (Real.pi ^ 2 / v) ^ (-b / 2) = Real.pi ^ (-b) * v ^ (b / 2) := by
    rw [Real.div_rpow (by positivity) hv.le, ← Real.rpow_natCast Real.pi 2,
      ← Real.rpow_mul hπ.le, show -b / 2 = -(b / 2) by ring,
      Real.rpow_neg hv.le, div_inv_eq_mul]
    congr 2
    push_cast; ring
  have e3 : v ^ ((d : ℝ) + 1) * v ^ (-((d : ℝ) / 2)) * v ^ (b / 2) =
      v ^ ((d : ℝ) + 1 - (d : ℝ) / 2 + b / 2) := by
    rw [← Real.rpow_add hv, ← Real.rpow_add hv]; congr 1 <;> ring
  rw [e1, e2]
  calc (Real.Gamma ((d : ℝ) + 2))⁻¹ * (v ^ ((d : ℝ) + 1) * Real.exp (-v)) *
        (Real.pi ^ ((d : ℝ) / 2) * v ^ (-((d : ℝ) / 2))) * (Real.pi ^ (-b) * v ^ (b / 2))
      = (Real.Gamma ((d : ℝ) + 2))⁻¹ * Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (-b) *
        ((v ^ ((d : ℝ) + 1) * v ^ (-((d : ℝ) / 2)) * v ^ (b / 2)) * Real.exp (-v)) := by ring
    _ = _ := by rw [e3]

/-- `u^{b-1} φ̂(u)` is integrable on `(0,∞)` for every `b > 0`. -/
lemma tpos_Mint {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ (b - 1) * Whole.phiHatR d u) (Set.Ioi 0) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hint : IntegrableOn (fun v : ℝ => tposW2 d v * (fun v : ℝ => Real.pi ^ 2 / v) v ^ (-b / 2))
      (Set.Ioi 0) := by
    have : IntegrableOn (fun v : ℝ => (Real.Gamma ((d : ℝ) + 2))⁻¹ * Real.pi ^ ((d : ℝ) / 2) *
        Real.pi ^ (-b) * (v ^ ((d : ℝ) + 1 - (d : ℝ) / 2 + b / 2) * Real.exp (-v))) (Set.Ioi 0) :=
      (tpos_gamma_integrable (e := (d : ℝ) + 1 - (d : ℝ) / 2 + b / 2) (by linarith)).const_mul _
    refine this.congr_fun (fun v hv => ?_) measurableSet_Ioi
    exact (tposW2_mul_gen (d := d) b hv).symm
  have hcm : Measurable (fun v : ℝ => Real.pi ^ 2 / v) := by fun_prop
  obtain ⟨h1, _⟩ := tpos_mixture_mellin (a := b) hb (W := tposW2 d)
    (c := fun v => Real.pi ^ 2 / v) (fun v hv => tposW2_nonneg hv)
    (fun v hv => by positivity) tposW2_measurable hcm hint
  have e1 : ∀ r : ℝ, Whole.phiHatR d r = ∫ v in Set.Ioi (0 : ℝ), tposW2 d v *
      Real.exp (-(Real.pi ^ 2 / v) * r ^ 2) := tpos_phiHatR_mixture
  simp_rw [← e1] at h1
  exact h1

lemma tpos_integral_Ioc_rpow {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    ∫ u in Set.Ioc (0 : ℝ) x, u ^ (a - 1) = x ^ a / a := by
  rw [← intervalIntegral.integral_of_le hx.le, integral_rpow (Or.inl (by linarith))]
  simp [sub_add_cancel, Real.zero_rpow ha.ne']

lemma tpos_integrableOn_Ioc_rpow {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => u ^ (a - 1)) (Set.Ioc 0 x) := by
  have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := x) (r := a - 1) (by linarith)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).1 this

/-- Decay of `φ̂`: `φ̂(x) ≤ C x^{-b}` (from monotonicity and the integrability of `u^{b-1}φ̂`). -/
lemma tpos_phiHatR_decay {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → Whole.phiHatR d x ≤ C * x ^ (-b) := by
  have hI := tpos_Mint (d := d) hb
  set M : ℝ := ∫ u in Set.Ioi (0 : ℝ), u ^ (b - 1) * Whole.phiHatR d u with hM
  have hM0 : 0 ≤ M := setIntegral_nonneg measurableSet_Ioi (fun u hu => by
    have hu0 : 0 < u := hu
    have := Whole.phiHatR_pos (d := d) u
    positivity)
  refine ⟨b * M, by positivity, fun x hx => ?_⟩
  have h1 : ∫ u in Set.Ioc (0 : ℝ) x, u ^ (b - 1) * Whole.phiHatR d x ≤
      ∫ u in Set.Ioc (0 : ℝ) x, u ^ (b - 1) * Whole.phiHatR d u := by
    refine setIntegral_mono_on ((tpos_integrableOn_Ioc_rpow hb hx).mul_const _)
      (hI.mono_set Set.Ioc_subset_Ioi_self) measurableSet_Ioc (fun u hu => ?_)
    exact mul_le_mul_of_nonneg_left (Whole.phiHatR_anti hu.1.le hu.2) (Real.rpow_nonneg hu.1.le _)
  have h2 : ∫ u in Set.Ioc (0 : ℝ) x, u ^ (b - 1) * Whole.phiHatR d u ≤ M := by
    refine setIntegral_mono_set hI ?_ Set.Ioc_subset_Ioi_self.eventuallyLE
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
    have hu0 : 0 < u := hu
    have := Whole.phiHatR_pos (d := d) u
    positivity
  rw [integral_mul_const, tpos_integral_Ioc_rpow hb hx] at h1
  have h3 : x ^ b / b * Whole.phiHatR d x ≤ M := h1.trans h2
  have hxb : 0 < x ^ b := Real.rpow_pos_of_pos hx b
  have : Whole.phiHatR d x ≤ b * M / x ^ b := by
    rw [le_div_iff₀ hxb]
    have : x ^ b / b * Whole.phiHatR d x * b = x ^ b * Whole.phiHatR d x := by field_simp
    nlinarith [this, h3, hb]
  calc Whole.phiHatR d x ≤ b * M / x ^ b := this
    _ = b * M * x ^ (-b) := by rw [Real.rpow_neg hx.le, div_eq_mul_inv]

/-- `t ↦ t^{d-s-1} φ̂(tr)` is integrable on `(0,∞)`. -/
lemma tpos_F_integrable (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s - 1) * Whole.phiHatR d (t * r)) (Set.Ioi 0) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h := (tpos_Mval (d := d) (s := s) hsd hs0).1
  have h2 : IntegrableOn (fun x : ℝ => (r * x) ^ ((d : ℝ) - s - 1) * Whole.phiHatR d (r * x)) (Set.Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => u ^ ((d : ℝ) - s - 1) * Whole.phiHatR d u) 0 hr).2 (by rwa [mul_zero])
    exact this
  have h3 : IntegrableOn (fun x : ℝ => r ^ (-((d : ℝ) - s - 1)) *
      ((r * x) ^ ((d : ℝ) - s - 1) * Whole.phiHatR d (r * x))) (Set.Ioi 0) := h2.const_mul _
  refine h3.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := ht
  simp only
  rw [Real.mul_rpow hr.le ht0.le, mul_comm r t]
  have : r ^ (-((d : ℝ) - s - 1)) * r ^ ((d : ℝ) - s - 1) = 1 := by
    rw [← Real.rpow_add hr]; simp
  calc r ^ (-((d : ℝ) - s - 1)) * (r ^ ((d : ℝ) - s - 1) * t ^ ((d : ℝ) - s - 1) * Whole.phiHatR d (t * r))
      = (r ^ (-((d : ℝ) - s - 1)) * r ^ ((d : ℝ) - s - 1)) *
          (t ^ ((d : ℝ) - s - 1) * Whole.phiHatR d (t * r)) := by ring
    _ = _ := by rw [this, one_mul]

end HRS.Commutator.TorusNote
