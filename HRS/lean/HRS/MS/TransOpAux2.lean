import HRS.MS.TransOpAux1

/-!
# S611 packet P1b: the coefficient ODE of an `L²` function under axis translation

For `f ∈ L²(ℝ^d)`, `i : Fin d`, put `A_α(t) = ∫ f(y) h_α(y + t e_i) dy` (the Hermite coefficient of `f(· - t e_i)`).  Then
`A_α' = (√α_i/√2) A_{α - e_i} - (√(α_i+1)/√2) A_{α + e_i}` (`s611_hasDerivAt_A`, differentiation under the integral sign with the
Gaussian domination `|h_β(z)| ≤ C e^{-|z|²/8}`) and `∑_α A_α(t)² = ∫ f²` for all `t` (`s611_A_hasSum`, Parseval).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_norm_e (i : Fin d) : ‖s611_e i‖ = 1 := by
  simp [s611_e]

theorem s611_integrable_gauss {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Euc d => Real.exp (-(c * ‖x‖ ^ 2))) := by
  have h := integrable_prod_euc (d := d) (fun _ t => Real.exp (-(c * t ^ 2)))
    (fun _ => by simpa [neg_mul] using integrable_exp_neg_mul_sq hc)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← Real.exp_sum, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, ← Finset.sum_neg_distrib]

theorem s611_memLp_gauss (C : ℝ) :
    MemLp (fun y : Euc d => C * Real.exp (-(‖y‖ ^ 2 / 16))) 2 (volume : Measure (Euc d)) := by
  have hc : Continuous (fun y : Euc d => C * Real.exp (-(‖y‖ ^ 2 / 16))) := by fun_prop
  rw [memLp_two_iff_integrable_sq hc.aestronglyMeasurable]
  refine ((s611_integrable_gauss (d := d) (c := 1 / 8) (by norm_num)).const_mul (C ^ 2)).congr
    (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
  congr 2
  ring

theorem s611_memLp_translate {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) (v : Euc d) :
    MemLp (fun y => f (y + v)) 2 (volume : Measure (Euc d)) :=
  hf.comp_measurePreserving (measurePreserving_add_right volume v)

theorem s611_integral_translate (g : Euc d → ℝ) (v : Euc d) :
    ∫ y, g (y + v) = ∫ y, g y :=
  integral_add_right_eq_self g v

/-- `A_α(t) = ∫ f(y) h_α(y + t e_i) dy`. -/
def s611_A (f : Euc d → ℝ) (i : Fin d) (α : MultiIndex d) (t : ℝ) : ℝ :=
  ∫ y, f y * hermiteFunD α (y + t • s611_e i)

theorem s611_integrable_A {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) (α : MultiIndex d)
    (v : Euc d) : Integrable (fun y => f y * hermiteFunD α (y + v)) := by
  have h2 := s611_memLp_translate (memLp_hermiteFunD α) v
  exact hf.integrable_mul h2

theorem s611_hasDerivAt_A {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (α : MultiIndex d) (i : Fin d) (t₀ : ℝ) :
    HasDerivAt (s611_A f i α)
      (Real.sqrt (α i) / Real.sqrt 2 * s611_A f i (s611_dec α i) t₀ -
        Real.sqrt ((α i : ℝ) + 1) / Real.sqrt 2 * s611_A f i (s611_inc α i) t₀) t₀ := by
  set a : ℝ := Real.sqrt (α i) / Real.sqrt 2 with ha
  set b : ℝ := Real.sqrt ((α i : ℝ) + 1) / Real.sqrt 2 with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  obtain ⟨C1, hC10, hC1⟩ := s611_hermiteFunD_gauss_bound (s611_dec α i)
  obtain ⟨C2, hC20, hC2⟩ := s611_hermiteFunD_gauss_bound (s611_inc α i)
  set R : ℝ := (|t₀| + 1) ^ 2 with hR
  set Cm : ℝ := (a * C1 + b * C2) * Real.exp (R / 8) with hCm
  have hcont : ∀ β : MultiIndex d, Continuous (hermiteFunD β) := fun β =>
    (contDiff_hermiteFunD β).continuous
  have hF : ∀ t : ℝ, Integrable (fun y => f y * hermiteFunD α (y + t • s611_e i)) :=
    fun t => s611_integrable_A hf α _
  have hF' : ∀ t : ℝ, Integrable (fun y => f y * (a * hermiteFunD (s611_dec α i) (y + t • s611_e i) -
      b * hermiteFunD (s611_inc α i) (y + t • s611_e i))) := by
    intro t
    have h1 := (s611_integrable_A hf (s611_dec α i) (t • s611_e i)).const_mul a
    have h2 := (s611_integrable_A hf (s611_inc α i) (t • s611_e i)).const_mul b
    refine (h1.sub h2).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    ring
  have hCm0 : 0 ≤ Cm := by positivity
  set g : Euc d → ℝ := fun y => Cm * Real.exp (-(‖y‖ ^ 2 / 16)) with hg
  have hbound_int : Integrable (fun y => ‖f y * g y‖) :=
    (hf.integrable_mul (s611_memLp_gauss (d := d) Cm)).norm
  have hbound : ∀ y : Euc d, ∀ t ∈ Metric.ball t₀ 1,
      ‖f y * (a * hermiteFunD (s611_dec α i) (y + t • s611_e i) -
        b * hermiteFunD (s611_inc α i) (y + t • s611_e i))‖ ≤ ‖f y * g y‖ := by
    intro y t ht
    set z : Euc d := y + t • s611_e i with hz
    have ht1 : |t| ≤ |t₀| + 1 := by
      have : |t - t₀| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using ht
      have := abs_sub_abs_le_abs_sub t t₀
      linarith
    have htR : t ^ 2 ≤ R := by
      rw [hR, ← sq_abs t]
      exact pow_le_pow_left₀ (abs_nonneg _) ht1 2
    have hyz : ‖y‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * t ^ 2 := by
      have h1 : ‖y‖ ≤ ‖z‖ + |t| := by
        have : y = z - t • s611_e i := by rw [hz]; abel
        calc ‖y‖ = ‖z - t • s611_e i‖ := by rw [← this]
          _ ≤ ‖z‖ + ‖t • s611_e i‖ := norm_sub_le _ _
          _ = ‖z‖ + |t| := by rw [norm_smul, s611_norm_e, Real.norm_eq_abs, mul_one]
      calc ‖y‖ ^ 2 ≤ (‖z‖ + |t|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ 2 * ‖z‖ ^ 2 + 2 * t ^ 2 := by nlinarith [sq_nonneg (‖z‖ - |t|), sq_abs t]
    have hexp : Real.exp (-(‖z‖ ^ 2 / 8)) ≤ Real.exp (R / 8) * Real.exp (-(‖y‖ ^ 2 / 16)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith
    have h1 := hC1 z
    have h2 := hC2 z
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ Cm * Real.exp (-(‖y‖ ^ 2 / 16)))]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc |a * hermiteFunD (s611_dec α i) z - b * hermiteFunD (s611_inc α i) z|
        ≤ |a * hermiteFunD (s611_dec α i) z| + |b * hermiteFunD (s611_inc α i) z| := abs_sub _ _
      _ = a * |hermiteFunD (s611_dec α i) z| + b * |hermiteFunD (s611_inc α i) z| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hb0]
      _ ≤ a * (C1 * Real.exp (-(‖z‖ ^ 2 / 8))) + b * (C2 * Real.exp (-(‖z‖ ^ 2 / 8))) := by
          gcongr
      _ = (a * C1 + b * C2) * Real.exp (-(‖z‖ ^ 2 / 8)) := by ring
      _ ≤ (a * C1 + b * C2) * (Real.exp (R / 8) * Real.exp (-(‖y‖ ^ 2 / 16))) := by
          gcongr
      _ = Cm * Real.exp (-(‖y‖ ^ 2 / 16)) := by rw [hCm]; ring
  have hdiff : ∀ y : Euc d, ∀ t : ℝ,
      HasDerivAt (fun τ : ℝ => f y * hermiteFunD α (y + τ • s611_e i))
        (f y * (a * hermiteFunD (s611_dec α i) (y + t • s611_e i) -
          b * hermiteFunD (s611_inc α i) (y + t • s611_e i))) t := fun y t =>
    (s611_hasDerivAt_axis α i y t).const_mul (f y)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := (volume : Measure (Euc d)))
    (s := Metric.ball t₀ 1) (Metric.ball_mem_nhds t₀ one_pos)
    (F := fun t y => f y * hermiteFunD α (y + t • s611_e i)) (x₀ := t₀)
    (bound := fun y => ‖f y * g y‖)
    (Filter.Eventually.of_forall fun t => (hF t).aestronglyMeasurable) (hF t₀)
    (F' := fun t y => f y * (a * hermiteFunD (s611_dec α i) (y + t • s611_e i) -
      b * hermiteFunD (s611_inc α i) (y + t • s611_e i)))
    (hF' t₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y t ht => hbound y t ht) hbound_int
    (Filter.Eventually.of_forall fun y t _ => hdiff y t)
  obtain ⟨-, hd⟩ := key
  have hI : ∫ y, f y * (a * hermiteFunD (s611_dec α i) (y + t₀ • s611_e i) -
      b * hermiteFunD (s611_inc α i) (y + t₀ • s611_e i)) =
      a * s611_A f i (s611_dec α i) t₀ - b * s611_A f i (s611_inc α i) t₀ := by
    have h1 := (s611_integrable_A hf (s611_dec α i) (t₀ • s611_e i)).const_mul a
    have h2 := (s611_integrable_A hf (s611_inc α i) (t₀ • s611_e i)).const_mul b
    unfold s611_A
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  rw [hI] at hd
  exact hd

theorem s611_A_eq (f : Euc d → ℝ) (i : Fin d) (α : MultiIndex d) (t : ℝ) :
    s611_A f i α t = hermiteCoeff (fun x => f (x - t • s611_e i)) α := by
  unfold s611_A hermiteCoeff
  rw [← s611_integral_translate (fun x => f (x - t • s611_e i) * hermiteFunD α x) (t • s611_e i)]
  simp only [add_sub_cancel_right]

theorem s611_A_hasSum {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) (i : Fin d) (t : ℝ) :
    HasSum (fun α => s611_A f i α t ^ 2) (∫ x, f x ^ 2) := by
  have hg : MemLp (fun x => f (x - t • s611_e i)) 2 (volume : Measure (Euc d)) := by
    have := s611_memLp_translate hf (-(t • s611_e i))
    simpa [sub_eq_add_neg] using this
  obtain ⟨hs, hp⟩ := hermite_parseval_aux _ hg
  have e : (∫ x, (f (x - t • s611_e i)) ^ 2) = ∫ x, f x ^ 2 :=
    integral_sub_right_eq_self (fun x => f x ^ 2) (t • s611_e i)
  rw [← e, ← hp]
  have : (fun α => s611_A f i α t ^ 2) = fun α => hermiteCoeff (fun x => f (x - t • s611_e i)) α ^ 2 := by
    funext α; rw [s611_A_eq]
  rw [this]
  exact hs.hasSum

end HRS.MS.TransOp

end
