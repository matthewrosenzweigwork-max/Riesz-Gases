import HRS.Uniform.Q45Lind3

/-!
# Q45: the telescoped partition bound
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {p : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

theorem partition_bound_gen (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    {adm : ℝ → ℝ → Prop} (hM : CellIface P ℱ t M Sg adm)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t))
    (hsbpsd : ∀ σ ∈ Set.Icc 0 t, (sb σ).PosSemidef)
    {ν : Matrix (Fin p) (Fin p) ℝ → ℝ} {Cν : ℝ} (hν : PairNorm ν Cν)
    (ξ : Ω → ℝ^p) (hξ : StronglyMeasurable[ℱ 0] ξ)
    (h : (ℝ^p) → ℝ) (hh : ContDiff ℝ 2 h) (H L Hp B0 G1 : ℝ) (hHp : 0 ≤ Hp)
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H)
    (hL : ∀ x y, ‖iteratedFDeriv ℝ 2 h x - iteratedFDeriv ℝ 2 h y‖ ≤ L * ‖x - y‖)
    (hB0 : ∀ x, |h x| ≤ B0) (hG1 : ∀ x, ‖fderiv ℝ h x‖ ≤ G1)
    (hpair : ∀ x Q', |hessPair h x Q'| ≤ Hp * ν Q')
    (n : ℕ) (hn : 1 ≤ n) (hadm : ∀ k < n, adm (unifPart t n k) (unifPart t n (k + 1))) :
    |∫ ω, h (ξ ω + M t ω) ∂P - ∫ ω, gaussSmooth h (covBlock sb 0 t) (ξ ω) ∂P| ≤
      (1 / 2) * Hp * ∫ ω, (∫ σ in Set.Icc 0 t, ν (Sg σ ω - sb σ)) ∂P +
        ∑ k ∈ Finset.range n,
          (∫ ω, taylorRem H L (M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω) ∂P +
            ∫ y, taylorRem H L y ∂(multivariateGaussian 0
              (covBlock sb (unifPart t n k) (unifPart t n (k + 1))))) := by
  classical
  have hent := sb_entry_integrableOn hsbmeas hsbint hsbpsd
  set τ : ℕ → ℝ := unifPart t n with hτ
  have hτ0 : ∀ k, 0 ≤ τ k := unifPart_nonneg ht n
  have hτt : ∀ k, k ≤ n → τ k ≤ t := fun k hk => unifPart_le ht hk
  have hτm : ∀ k, τ k ≤ τ (k + 1) := fun k => unifPart_mono ht n (Nat.le_succ k)
  have hτn : τ n = t := unifPart_self t hn
  have hτz : τ 0 = 0 := by simp [hτ, unifPart]
  set Q : ℕ → Matrix (Fin p) (Fin p) ℝ := fun k => covBlock sb (τ k) t with hQ
  set u : ℕ → (ℝ^p) → ℝ := fun k => gaussSmooth h (Q k) with hu
  have hQpsd : ∀ k, (Q k).PosSemidef := fun k => covBlock_psd hsbpsd hent (hτ0 k) le_rfl
  have hQadd : ∀ k, k < n → Q k = covBlock sb (τ k) (τ (k + 1)) + Q (k + 1) := by
    intro k hk
    exact covBlock_add (hτm k) (hτt (k + 1) hk) (fun i j =>
      (hent i j).mono_set (Set.Icc_subset_Icc (hτ0 k) le_rfl))
  have hGpsd : ∀ k, k < n → (covBlock sb (τ k) (τ (k + 1))).PosSemidef := fun k hk =>
    covBlock_psd hsbpsd hent (hτ0 k) (hτt (k + 1) hk)
  have huprops := fun k => gaussSmooth_hessian (Q k) (hQpsd k) h hh H hH
  have hustep : ∀ k, k < n → ∀ x, u k x = gaussSmooth (u (k + 1))
      (covBlock sb (τ k) (τ (k + 1))) x := by
    intro k hk x
    have e := gaussSmooth_add (covBlock sb (τ k) (τ (k + 1))) (Q (k + 1)) (hGpsd k hk)
      (hQpsd (k + 1)) h hh H hH x
    rw [← hQadd k hk] at e
    exact e
  set D : ℕ → Ω → ℝ := fun k ω => u (k + 1) (ξ ω + M (τ (k + 1)) ω) -
    u k (ξ ω + M (τ k) ω) with hD
  have hstep : ∀ k, k < n → Integrable (D k) P ∧ |∫ ω, D k ω ∂P| ≤
      (1 / 2) * Hp * (∫ ω, (∫ σ in Set.Icc (τ k) (τ (k + 1)), ν (Sg σ ω - sb σ)) ∂P) +
      ∫ ω, taylorRem H L (M (τ (k + 1)) ω - M (τ k) ω) ∂P +
      ∫ y, taylorRem H L y ∂(multivariateGaussian (0 : ℝ^p) (covBlock sb (τ k) (τ (k + 1)))) := by
    intro k hk
    have := partition_step_gen P ℱ t M Sg hM sb hsbmeas hsbint hsbpsd hν ξ hξ (τ k) (τ (k + 1))
      (hτ0 k) (hτm k) (hτt (k + 1) hk) (hadm k hk) (u (k + 1)) (huprops (k + 1)).1 H L Hp B0 G1 hHp
      (huprops (k + 1)).2.1 ((huprops (k + 1)).2.2 L hL)
      (gs_abs_le hB0 (Q (k + 1))) (gs_fderiv_le hh hH hG1 (Q (k + 1)))
      (gs_hessPair_le hh hH hpair (Q (k + 1)))
    have hfe : (fun ω => u (k + 1) (ξ ω + M (τ (k + 1)) ω) -
        gaussSmooth (u (k + 1)) (covBlock sb (τ k) (τ (k + 1))) (ξ ω + M (τ k) ω)) = D k := by
      funext ω
      simp only [hD, hustep k hk]
    rw [hfe] at this
    exact this
  have iD : ∀ k ∈ Finset.range n, Integrable (D k) P := fun k hk =>
    (hstep k (Finset.mem_range.1 hk)).1
  have hun : u n = h := by
    have : Q n = 0 := by simp only [hQ, hτn, covBlock_self]
    simp only [hu, this, gaussSmooth_zero]
  have hξm : StronglyMeasurable ξ := hξ.mono (ℱ.le 0)
  have hMm : ∀ τ ∈ Set.Icc (0 : ℝ) t, StronglyMeasurable (M τ) := fun τ hτ =>
    (stronglyMeasurable_of_coord fun a => hM.adapted τ hτ a).mono (ℱ.le τ)
  have ih : Integrable (fun ω => h (ξ ω + M t ω)) P :=
    Integrable.of_bound (hh.continuous.comp_aestronglyMeasurable
      (hξm.add (hMm t ⟨ht, le_rfl⟩)).aestronglyMeasurable) B0
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB0 _)
  have i0 : Integrable (fun ω => u 0 (ξ ω)) P :=
    Integrable.of_bound ((huprops 0).1.continuous.comp_aestronglyMeasurable
      hξm.aestronglyMeasurable) B0
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact gs_abs_le hB0 (Q 0) _)
  have hsum : (fun ω => h (ξ ω + M t ω) - u 0 (ξ ω)) =ᵐ[P] fun ω => ∑ k ∈ Finset.range n, D k ω := by
    filter_upwards [hM.zero] with ω h0
    have := Finset.sum_range_sub (fun k => u k (ξ ω + M (τ k) ω)) n
    simp only [hD]
    rw [this, hun, hτn, hτz]
    have h00 : M 0 ω = 0 := h0
    rw [h00, add_zero]
  have hu0 : u 0 = gaussSmooth h (covBlock sb 0 t) := by
    simp only [hu, hQ, hτz]
  have key : ∫ ω, h (ξ ω + M t ω) ∂P - ∫ ω, gaussSmooth h (covBlock sb 0 t) (ξ ω) ∂P =
      ∑ k ∈ Finset.range n, ∫ ω, D k ω ∂P := by
    rw [← hu0, ← integral_sub ih i0, integral_congr_ae hsum, integral_finsetSum _ iD]
  have hI : ∀ k ∈ Finset.range n, Integrable
      (fun ω => ∫ σ in Set.Icc (τ k) (τ (k + 1)), ν (Sg σ ω - sb σ)) P := fun k hk =>
    Iblk_integrable_gen P ℱ hM hsbmeas hsbint hν (hτ0 k) (hτt (k + 1) (Finset.mem_range.1 hk))
  have hIsum : ∑ k ∈ Finset.range n, (∫ ω, (∫ σ in Set.Icc (τ k) (τ (k + 1)),
      ν (Sg σ ω - sb σ)) ∂P) = ∫ ω, (∫ σ in Set.Icc 0 t, ν (Sg σ ω - sb σ)) ∂P := by
    rw [← integral_finsetSum _ hI]
    refine integral_congr_ae ?_
    filter_upwards [s1_sub_intOn_gen P hM hsbmeas hsbint] with ω hω
    have hF : Measurable (fun σ => ν (Sg σ ω - sb σ)) := by
      have h1 : Measurable (fun σ => Sg σ ω) :=
        hM.sigma_meas.comp (measurable_id.prodMk measurable_const)
      exact hν.cont.measurable.comp (measurable_mat_sub h1 hsbmeas)
    have hint : IntegrableOn (fun σ => ν (Sg σ ω - sb σ)) (Set.Icc 0 t) := by
      refine Integrable.mono' (hω.const_mul Cν) hF.aestronglyMeasurable
        (ae_of_all _ fun σ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hν.nonneg _)]
      exact hν.le_s1 _
    exact sum_blocks_Icc ht hint hn
  rw [key]
  calc |∑ k ∈ Finset.range n, ∫ ω, D k ω ∂P|
      ≤ ∑ k ∈ Finset.range n, |∫ ω, D k ω ∂P| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, ((1 / 2) * Hp * (∫ ω, (∫ σ in Set.Icc (τ k) (τ (k + 1)),
          ν (Sg σ ω - sb σ)) ∂P) +
          (∫ ω, taylorRem H L (M (τ (k + 1)) ω - M (τ k) ω) ∂P +
          ∫ y, taylorRem H L y ∂(multivariateGaussian (0 : ℝ^p)
            (covBlock sb (τ k) (τ (k + 1)))))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have := (hstep k (Finset.mem_range.1 hk)).2
        linarith
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hIsum]

end HRS.Uniform.Q45
