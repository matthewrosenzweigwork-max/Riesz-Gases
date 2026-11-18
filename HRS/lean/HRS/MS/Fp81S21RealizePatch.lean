import HRS.MS.S111TermAux4

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.S111T

private theorem fp81s21_enorm_fourth_real (x : ℝ) :
    ‖x‖ₑ ^ (4 : ℝ) = ENNReal.ofReal (x ^ 4) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg x) (by norm_num)]
  congr 1
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.norm_eq_abs]
  calc
    |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
    _ = (x ^ 2) ^ 2 := by rw [sq_abs]
    _ = x ^ 4 := by ring

private theorem fp81s21_coord_product_lintegral_le
    {d : ℕ} {m : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → OscDual d m} (hY : Measurable Y)
    (v : MultiIndex d → ℝ) (hv : ∀ α, 0 ≤ v α)
    (h4 : ∀ α, ∫⁻ ω, ‖OscDual.coord (Y ω) α‖ₑ ^ (4 : ℝ) ∂P ≤
      ENNReal.ofReal (3 * (v α) ^ 2))
    (α β : MultiIndex d) :
    ∫⁻ ω, ENNReal.ofReal ((OscDual.coord (Y ω) α) ^ 2) *
      ENNReal.ofReal ((OscDual.coord (Y ω) β) ^ 2) ∂P ≤
        ENNReal.ofReal (3 * v α * v β) := by
  have hcoord : ∀ γ, Measurable (fun ω => OscDual.coord (Y ω) γ) := by
    intro γ
    change Measurable (fun ω => s111t_coordCLM d m γ (Y ω))
    exact (s111t_coordCLM d m γ).continuous.measurable.comp hY
  let f : MultiIndex d → Ω → ℝ≥0∞ := fun γ ω =>
    ENNReal.ofReal (OscDual.coord (Y ω) γ ^ 2)
  have hfmeas : ∀ γ, AEMeasurable (f γ) P := by
    intro γ
    exact (ENNReal.measurable_ofReal.comp ((hcoord γ).pow_const 2)).aemeasurable
  have hf4 : ∀ γ, ∫⁻ ω, (f γ ω) ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal (3 * (v γ) ^ 2) := by
    intro γ
    calc ∫⁻ ω, (f γ ω) ^ (2 : ℝ) ∂P
        = ∫⁻ ω, ‖OscDual.coord (Y ω) γ‖ₑ ^ (4 : ℝ) ∂P := by
          refine lintegral_congr fun ω => ?_
          simp only [f]
          rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num)]
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          rw [fp81s21_enorm_fourth_real]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (3 * (v γ) ^ 2) := h4 γ
  have hroot : ∀ γ, (∫⁻ ω, (f γ ω) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (Real.sqrt 3 * v γ) := by
    intro γ
    calc (∫⁻ ω, (f γ ω) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))
        ≤ (ENNReal.ofReal (3 * (v γ) ^ 2)) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow (hf4 γ) (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt 3 * v γ) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num), Real.sqrt_sq (hv γ)]
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    (f := f α) (g := f β) (hfmeas α) (hfmeas β)
  calc ∫⁻ ω, f α ω * f β ω ∂P
      ≤ (∫⁻ ω, (f α ω) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) *
        (∫⁻ ω, (f β ω) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := hcs
    _ ≤ ENNReal.ofReal (Real.sqrt 3 * v α) *
        ENNReal.ofReal (Real.sqrt 3 * v β) :=
          mul_le_mul (hroot α) (hroot β) (by positivity) (by positivity)
    _ = ENNReal.ofReal (3 * v α * v β) := by
          rw [← ENNReal.ofReal_mul
            (mul_nonneg (Real.sqrt_nonneg 3) (hv α))]
          congr 1
          have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := by
            nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
          calc
            (Real.sqrt 3 * v α) * (Real.sqrt 3 * v β) =
                (Real.sqrt 3 * Real.sqrt 3) * v α * v β := by ring
            _ = 3 * v α * v β := by rw [hs]

/-- A coordinatewise fourth-moment bound controls the fourth moment of the `ℓ²` norm. -/
theorem fp81s21_coord_fourth_to_norm_fourth
    {d : ℕ} {m : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : Ω → OscDual d m) (hY : Measurable Y)
    (v : MultiIndex d → ℝ) (hv : ∀ α, 0 ≤ v α) (hvs : Summable v)
    (h4 : ∀ α, ∫⁻ ω, ‖OscDual.coord (Y ω) α‖ₑ ^ (4 : ℝ) ∂P ≤
      ENNReal.ofReal (3 * (v α) ^ 2)) :
    ∫⁻ ω, ‖Y ω‖ₑ ^ (4 : ℝ) ∂P ≤
      ENNReal.ofReal (3 * (∑' α, v α) ^ 2) := by
  obtain ⟨f, hf⟩ := exists_surjective_nat (MultiIndex d)
  let A : ℕ → Finset (MultiIndex d) := fun n => (Finset.range n).image f
  have hmono : Monotone A := fun n n' h => Finset.image_subset_image (Finset.range_mono h)
  have hcover : ∀ x : MultiIndex d, ∃ n, x ∈ A n := by
    intro x
    obtain ⟨k, rfl⟩ := hf x
    exact ⟨k + 1, Finset.mem_image.2 ⟨k, by simp, rfl⟩⟩
  have hcoord : ∀ α, Measurable (fun ω => OscDual.coord (Y ω) α) := by
    intro α
    change Measurable (fun ω => s111t_coordCLM d m α (Y ω))
    exact (s111t_coordCLM d m α).continuous.measurable.comp hY
  have hfinite : ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((∑ α ∈ A n, OscDual.coord (Y ω) α ^ 2) ^ 2) ∂P ≤
        ENNReal.ofReal (3 * (∑ α ∈ A n, v α) ^ 2) := by
    intro n
    have hsection : ∀ ω,
        ENNReal.ofReal ((∑ α ∈ A n, OscDual.coord (Y ω) α ^ 2) ^ 2) =
          ∑ α ∈ A n, ∑ β ∈ A n,
            ENNReal.ofReal (OscDual.coord (Y ω) α ^ 2) *
              ENNReal.ofReal (OscDual.coord (Y ω) β ^ 2) := by
      intro ω
      rw [ENNReal.ofReal_pow (by positivity : 0 ≤ ∑ α ∈ A n, OscDual.coord (Y ω) α ^ 2)]
      rw [ENNReal.ofReal_sum_of_nonneg (fun α _ => sq_nonneg _), pow_two,
        Finset.sum_mul_sum]
    have hmeasprod : ∀ α β, Measurable
        (fun ω => ENNReal.ofReal (OscDual.coord (Y ω) α ^ 2) *
          ENNReal.ofReal (OscDual.coord (Y ω) β ^ 2)) := by
      intro α β
      exact (ENNReal.measurable_ofReal.comp ((hcoord α).pow_const 2)).mul
        (ENNReal.measurable_ofReal.comp ((hcoord β).pow_const 2))
    have hmeasrow : ∀ α, Measurable (fun ω => ∑ β ∈ A n,
        ENNReal.ofReal (OscDual.coord (Y ω) α ^ 2) *
          ENNReal.ofReal (OscDual.coord (Y ω) β ^ 2)) := by
      intro α
      exact Finset.measurable_sum _ fun β _ => hmeasprod α β
    rw [show (fun ω => ENNReal.ofReal
        ((∑ α ∈ A n, OscDual.coord (Y ω) α ^ 2) ^ 2)) =
          fun ω => ∑ α ∈ A n, ∑ β ∈ A n,
            ENNReal.ofReal (OscDual.coord (Y ω) α ^ 2) *
              ENNReal.ofReal (OscDual.coord (Y ω) β ^ 2) from funext hsection]
    calc ∫⁻ ω, ∑ α ∈ A n, ∑ β ∈ A n,
          ENNReal.ofReal (OscDual.coord (Y ω) α ^ 2) *
            ENNReal.ofReal (OscDual.coord (Y ω) β ^ 2) ∂P
        = ∑ α ∈ A n, ∫⁻ ω, ∑ β ∈ A n,
            ENNReal.ofReal (OscDual.coord (Y ω) α ^ 2) *
              ENNReal.ofReal (OscDual.coord (Y ω) β ^ 2) ∂P :=
            lintegral_finsetSum _ fun α _ => hmeasrow α
      _ = ∑ α ∈ A n, ∑ β ∈ A n,
          ∫⁻ ω, ENNReal.ofReal (OscDual.coord (Y ω) α ^ 2) *
            ENNReal.ofReal (OscDual.coord (Y ω) β ^ 2) ∂P := by
          apply Finset.sum_congr rfl
          intro α hα
          exact lintegral_finsetSum _ fun β _ => hmeasprod α β
      _ ≤ ∑ α ∈ A n, ∑ β ∈ A n, ENNReal.ofReal (3 * v α * v β) := by
          apply Finset.sum_le_sum
          intro α hα
          apply Finset.sum_le_sum
          intro β hβ
          exact fp81s21_coord_product_lintegral_le hY v hv h4 α β
      _ = ENNReal.ofReal (3 * (∑ α ∈ A n, v α) ^ 2) := by
          calc ∑ α ∈ A n, ∑ β ∈ A n, ENNReal.ofReal (3 * v α * v β)
              = ∑ α ∈ A n, ENNReal.ofReal (∑ β ∈ A n, 3 * v α * v β) := by
                apply Finset.sum_congr rfl
                intro α hα
                rw [← ENNReal.ofReal_sum_of_nonneg (fun β _ =>
                  mul_nonneg (mul_nonneg (by norm_num) (hv α)) (hv β))]
            _ = ENNReal.ofReal (∑ α ∈ A n, ∑ β ∈ A n, 3 * v α * v β) := by
                rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ =>
                  Finset.sum_nonneg fun β _ =>
                    mul_nonneg (mul_nonneg (by norm_num) (hv α)) (hv β))]
            _ = _ := by
                congr 1
                have hsquare : (∑ α ∈ A n, v α) ^ 2 =
                    ∑ α ∈ A n, ∑ β ∈ A n, v α * v β := by
                  rw [pow_two, Finset.sum_mul_sum]
                rw [hsquare]
                calc ∑ α ∈ A n, ∑ β ∈ A n, 3 * v α * v β
                    = 3 * (∑ α ∈ A n, ∑ β ∈ A n, v α * v β) := by
                      calc
                        _ = ∑ α ∈ A n, ∑ β ∈ A n, 3 * (v α * v β) := by
                          apply Finset.sum_congr rfl
                          intro α hα
                          apply Finset.sum_congr rfl
                          intro β hβ
                          ring
                        _ = _ := by simp_rw [← Finset.mul_sum]
                  _ = _ := by ring
  have hfiniteBound : ∀ n,
      ∫⁻ ω, ENNReal.ofReal ((∑ α ∈ A n, OscDual.coord (Y ω) α ^ 2) ^ 2) ∂P ≤
        ENNReal.ofReal (3 * (∑' α, v α) ^ 2) := by
    intro n
    refine (hfinite n).trans (ENNReal.ofReal_le_ofReal ?_)
    have hpart : ∑ α ∈ A n, v α ≤ ∑' α, v α :=
      hvs.sum_le_tsum (A n) (fun α _ => hv α)
    have hpart0 : 0 ≤ ∑ α ∈ A n, v α := Finset.sum_nonneg fun α _ => hv α
    have htotal0 : 0 ≤ ∑' α, v α := tsum_nonneg hv
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hpart0 htotal0).2 hpart) (by norm_num)
  have hlim : ∀ ω, Tendsto
      (fun n => ENNReal.ofReal ((∑ α ∈ A n, OscDual.coord (Y ω) α ^ 2) ^ 2))
      atTop (𝓝 (‖Y ω‖ₑ ^ (4 : ℝ))) := by
    intro ω
    have hsum := lp_two_summable
      (ι := MultiIndex d) (show lp (fun _ : MultiIndex d => ℝ) 2 from Y ω)
    have hsection : Tendsto (fun n => ∑ α ∈ A n, OscDual.coord (Y ω) α ^ 2)
        atTop (𝓝 (‖Y ω‖ ^ 2)) := by
      have h := hsum.hasSum.comp (tendsto_atTop_finset_of_monotone hmono hcover)
      have hn : ‖Y ω‖ ^ 2 = ∑' α, OscDual.coord (Y ω) α ^ 2 := by
        exact lp_two_norm_sq (ι := MultiIndex d)
          (show lp (fun _ : MultiIndex d => ℝ) 2 from Y ω)
      rw [hn]
      exact h
    have h2 := ENNReal.tendsto_ofReal (hsection.pow 2)
    have he : ENNReal.ofReal ((‖Y ω‖ ^ 2) ^ 2) = ‖Y ω‖ₑ ^ (4 : ℝ) := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (Y ω)) (by norm_num)]
      congr 1
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    simpa only [he] using h2
  have hmeas : ∀ n, AEMeasurable
      (fun ω => ENNReal.ofReal ((∑ α ∈ A n, OscDual.coord (Y ω) α ^ 2) ^ 2)) P := by
    intro n
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (((Finset.measurable_sum _ fun α _ => (hcoord α).pow_const 2).pow_const 2).aemeasurable)
  calc ∫⁻ ω, ‖Y ω‖ₑ ^ (4 : ℝ) ∂P
      = ∫⁻ ω, liminf
          (fun n => ENNReal.ofReal ((∑ α ∈ A n, OscDual.coord (Y ω) α ^ 2) ^ 2)) atTop ∂P := by
        refine lintegral_congr fun ω => ?_
        exact ((hlim ω).liminf_eq).symm
    _ ≤ liminf (fun n => ∫⁻ ω,
          ENNReal.ofReal ((∑ α ∈ A n, OscDual.coord (Y ω) α ^ 2) ^ 2) ∂P) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ ENNReal.ofReal (3 * (∑' α, v α) ^ 2) :=
        liminf_le_of_frequently_le' (Filter.Eventually.of_forall hfiniteBound).frequently

#print axioms fp81s21_coord_fourth_to_norm_fourth

end HRS.Fp81.S21

end
