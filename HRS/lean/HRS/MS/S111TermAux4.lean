import HRS.MS.S111TermAux3

/-!
# S11.1 terminal wave, G01 part 2: fourth moment of an `ℓ²`-valued Gaussian series

For the `L²` limit `Y` of `Σ g_k ℓ_k` in `OscDual d m = ℓ²(ℕ^d)` with `Σ‖ℓ_k‖² ≤ σ²`, finite sections of the coordinates are
centered Gaussian vectors (`s111t_vector_law`), so `E(Σ_{α∈A}Y_α²)² ≤ 3σ⁴`; Fatou gives
`E‖Y‖⁴ ≤ 3σ⁴` (as an `ENNReal` lintegral with the real exponent used by Kolmogorov--Chentsov).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111T

open HRS.Whole

variable {d : ℕ} {m : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}

/-- The coordinate functional `u ↦ u_α` on `B_m = ℓ²(ℕ^d)`. -/
def s111t_coordCLM (d : ℕ) (m : ℝ) (α : MultiIndex d) : OscDual d m →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => OscDual.coord u α
      map_add' := fun u v => OscDual.coord_add u v α
      map_smul' := fun c u => OscDual.coord_smul c u α } 1 (fun u => by
    have h := lp.norm_apply_le_norm (p := 2) (E := fun _ : MultiIndex d => ℝ) (by simp)
      (show lp (fun _ : MultiIndex d => ℝ) 2 from u) α
    have hn : ‖u‖ = ‖(show lp (fun _ : MultiIndex d => ℝ) 2 from u)‖ := rfl
    rw [one_mul, hn]
    exact h)

theorem s111t_coordCLM_apply (α : MultiIndex d) (u : OscDual d m) :
    s111t_coordCLM d m α u = OscDual.coord u α := rfl

theorem s111t_sum_coord_le (u : OscDual d m) (A : Finset (MultiIndex d)) :
    ∑ α ∈ A, OscDual.coord u α ^ 2 ≤ ‖u‖ ^ 2 := by
  have h := lp_two_norm_sq (ι := MultiIndex d) (show lp (fun _ : MultiIndex d => ℝ) 2 from u)
  have hn : ‖u‖ = ‖(show lp (fun _ : MultiIndex d => ℝ) 2 from u)‖ := rfl
  rw [hn, h]
  exact (lp_two_summable (ι := MultiIndex d) (show lp (fun _ : MultiIndex d => ℝ) 2 from u)).sum_le_tsum A
    (fun _ _ => sq_nonneg _)

/-- Finite sections of the coordinates of a Gaussian series have fourth moment `≤ 3σ⁴`. -/
theorem s111t_finite_fourth (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (hind : iIndepFun g P)
    (ℓ : ℕ → OscDual d m) (hs : Summable fun k => ‖ℓ k‖ ^ 2) (Y : Ω → OscDual d m)
    (hY : S111tIsGSL P g ℓ Y) (A : Finset (MultiIndex d)) :
    ∫⁻ ω, ENNReal.ofReal ((∑ α ∈ A, OscDual.coord (Y ω) α ^ 2) ^ 2) ∂P ≤
      ENNReal.ofReal (3 * (∑' k, ‖ℓ k‖ ^ 2) ^ 2) := by
  set n := A.card with hn
  set α : Fin n → MultiIndex d := fun j => ((A.equivFin.symm j : A) : MultiIndex d) with hα
  set φ : Fin n → OscDual d m →L[ℝ] ℝ := fun j => s111t_coordCLM d m (α j) with hφ
  set a : Fin n → ℕ → ℝ := fun j k => φ j (ℓ k) with ha_def
  have ha : ∀ j, Summable fun k => a j k ^ 2 := fun j => s111t_summable_clm (φ j) ℓ hs
  have hQ := s111t_gram_psd a ha
  have hlaw := s111t_vector_law (ι := Fin n) hg hind (fun _ => Y) (fun _ => ℓ) (fun _ => hY)
    (fun _ => hs) φ
  have hYm : ∀ j, AEMeasurable (fun ω => φ j (Y ω)) P := fun j =>
    ((φ j).continuous.comp_aestronglyMeasurable hY.memLp.aestronglyMeasurable).aemeasurable
  have hVm : AEMeasurable (fun ω => (WithLp.toLp 2 fun j => φ j (Y ω) : EuclideanSpace ℝ (Fin n))) P := by
    have : Measurable (fun x : Fin n → ℝ => (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))) := by fun_prop
    exact this.comp_aemeasurable (aemeasurable_pi_iff.2 hYm)
  have hpt : ∀ ω, (∑ a ∈ A, OscDual.coord (Y ω) a ^ 2) ^ 2 =
      ‖(WithLp.toLp 2 fun j => φ j (Y ω) : EuclideanSpace ℝ (Fin n))‖ ^ 4 := by
    intro ω
    have h1 : ‖(WithLp.toLp 2 fun j => φ j (Y ω) : EuclideanSpace ℝ (Fin n))‖ ^ 2 =
        ∑ j, (φ j (Y ω)) ^ 2 := EuclideanSpace.real_norm_sq_eq _
    have h2 : ∑ j, (φ j (Y ω)) ^ 2 = ∑ a ∈ A, OscDual.coord (Y ω) a ^ 2 := by
      rw [← Finset.sum_coe_sort A (fun a => OscDual.coord (Y ω) a ^ 2)]
      exact Equiv.sum_comp A.equivFin.symm (fun a : A => OscDual.coord (Y ω) (a : MultiIndex d) ^ 2)
    calc (∑ a ∈ A, OscDual.coord (Y ω) a ^ 2) ^ 2 = (‖(WithLp.toLp 2 fun j => φ j (Y ω) :
          EuclideanSpace ℝ (Fin n))‖ ^ 2) ^ 2 := by rw [h1, h2]
      _ = _ := by ring
  simp_rw [hpt]
  rw [← lintegral_map' (by fun_prop : AEMeasurable (fun y : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (‖y‖ ^ 4)) _) hVm, hlaw]
  have hmem : MemLp id 4 (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      (Matrix.of fun j l => ∑' k, φ j (ℓ k) * φ l (ℓ k))) := IsGaussian.memLp_id _ 4 (by simp)
  have hint : Integrable (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 4) (multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin n)) (Matrix.of fun j l => ∑' k, φ j (ℓ k) * φ l (ℓ k))) := by
    simpa using hmem.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (HRS.Yurinskii.integral_norm_pow4_le hQ).trans ?_
  have hc4 : HRS.Yurinskii.c4 = 3 := HRS.gauss_m4
  rw [hc4]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have htr : ∑ c : Fin n, (Matrix.of fun j l => ∑' k, a j k * a l k : Matrix (Fin n) (Fin n) ℝ) c c ≤
      ∑' k, ‖ℓ k‖ ^ 2 := by
    simp only [Matrix.of_apply]
    rw [← Summable.tsum_finsetSum (fun c _ => (s111t_summable_mul (a c) (a c) (ha c) (ha c)))]
    refine Summable.tsum_le_tsum (fun k => ?_)
      (summable_sum fun c _ => s111t_summable_mul (a c) (a c) (ha c) (ha c)) hs
    have h2 : ∑ c : Fin n, a c k * a c k = ∑ b ∈ A, OscDual.coord (ℓ k) b ^ 2 := by
      rw [← Finset.sum_coe_sort A (fun a => OscDual.coord (ℓ k) a ^ 2)]
      rw [← Equiv.sum_comp A.equivFin.symm (fun a : A => OscDual.coord (ℓ k) (a : MultiIndex d) ^ 2)]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [ha_def, hφ, hα, s111t_coordCLM_apply, sq]
    rw [h2]
    exact s111t_sum_coord_le (ℓ k) A
  have htr0 : 0 ≤ ∑ c : Fin n, (Matrix.of fun j l => ∑' k, a j k * a l k : Matrix (Fin n) (Fin n) ℝ) c c :=
    Finset.sum_nonneg fun c _ => hQ.diag_nonneg
  exact pow_le_pow_left₀ htr0 htr 2

/-- **Fourth moment of an `ℓ²`-valued Gaussian series**: `E‖Y‖⁴ ≤ 3(Σ_k‖ℓ_k‖²)²` (lintegral form). -/
theorem s111t_gsl_fourth (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (hind : iIndepFun g P)
    (ℓ : ℕ → OscDual d m) (hs : Summable fun k => ‖ℓ k‖ ^ 2) (Y : Ω → OscDual d m)
    (hY : S111tIsGSL P g ℓ Y) :
    ∫⁻ ω, ‖Y ω‖ₑ ^ (4 : ℝ) ∂P ≤ ENNReal.ofReal (3 * (∑' k, ‖ℓ k‖ ^ 2) ^ 2) := by
  obtain ⟨f, hf⟩ := exists_surjective_nat (MultiIndex d)
  set A : ℕ → Finset (MultiIndex d) := fun n => (Finset.range n).image f with hA
  have hmono : Monotone A := fun n n' h => Finset.image_subset_image (Finset.range_mono h)
  have hcover : ∀ x, ∃ n, x ∈ A n := by
    intro x
    obtain ⟨k, rfl⟩ := hf x
    exact ⟨k + 1, Finset.mem_image.2 ⟨k, by simp, rfl⟩⟩
  have hYm : ∀ a, AEMeasurable (fun ω => OscDual.coord (Y ω) a) P := fun a => by
    have := ((s111t_coordCLM d m a).continuous.comp_aestronglyMeasurable hY.memLp.aestronglyMeasurable).aemeasurable
    exact this
  have hgm : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal ((∑ a ∈ A n, OscDual.coord (Y ω) a ^ 2) ^ 2)) P := by
    intro n
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact (Finset.aemeasurable_fun_sum _ fun a _ => (hYm a).pow_const 2).pow_const 2
  have hlim : ∀ ω, Tendsto (fun n => ENNReal.ofReal ((∑ a ∈ A n, OscDual.coord (Y ω) a ^ 2) ^ 2))
      atTop (𝓝 (‖Y ω‖ₑ ^ (4 : ℝ))) := by
    intro ω
    have h1 : Tendsto (fun n => ∑ a ∈ A n, OscDual.coord (Y ω) a ^ 2) atTop (𝓝 (‖Y ω‖ ^ 2)) := by
      have hsum := lp_two_summable (ι := MultiIndex d) (show lp (fun _ : MultiIndex d => ℝ) 2 from Y ω)
      have := hsum.hasSum.comp (tendsto_atTop_finset_of_monotone hmono hcover)
      have hn : ‖Y ω‖ ^ 2 = ∑' i, ((show lp (fun _ : MultiIndex d => ℝ) 2 from Y ω) i) ^ 2 :=
        lp_two_norm_sq (ι := MultiIndex d) (show lp (fun _ : MultiIndex d => ℝ) 2 from Y ω)
      rw [hn]
      exact this
    have h2 := ENNReal.tendsto_ofReal (h1.pow 2)
    have e : ENNReal.ofReal ((‖Y ω‖ ^ 2) ^ 2) = ‖Y ω‖ₑ ^ (4 : ℝ) := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      congr 1
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rwa [e] at h2
  calc ∫⁻ ω, ‖Y ω‖ₑ ^ (4 : ℝ) ∂P
      = ∫⁻ ω, liminf (fun n => ENNReal.ofReal ((∑ a ∈ A n, OscDual.coord (Y ω) a ^ 2) ^ 2)) atTop ∂P := by
        refine lintegral_congr fun ω => ?_
        exact ((hlim ω).liminf_eq).symm
    _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((∑ a ∈ A n, OscDual.coord (Y ω) a ^ 2) ^ 2) ∂P) atTop :=
        lintegral_liminf_le' hgm
    _ ≤ ENNReal.ofReal (3 * (∑' k, ‖ℓ k‖ ^ 2) ^ 2) :=
        liminf_le_of_frequently_le' (Filter.Eventually.of_forall fun n =>
          s111t_finite_fourth hg hind ℓ hs Y hY (A n)).frequently

end HRS.MS.S111T
