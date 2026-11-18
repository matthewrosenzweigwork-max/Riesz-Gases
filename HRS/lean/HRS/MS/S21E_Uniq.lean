import HRS.Whole.HeadlineStatement
import HRS.MS.S21E_Dens

/-!
# S2.1(iii) packet G2: uniqueness of the cross-densities

Lemma cross, last paragraph: two signed densities with the same pairings against the oscillator tests (which contain `C_c^∞`) agree a.e. in space;
hence `cubicFormula` and `CubicFormulaIntegrable` do not depend on the representative, and the universal clause of the frozen statement reduces to
one constructed family.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21E

open HRS HRS.Whole

variable {d : ℕ}

/-- A smooth compactly supported function is an oscillator test (it is a Schwartz function). -/
theorem s21e_isOscTest_of_cc {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (m : ℝ) :
    IsOscTest m g := by
  refine ⟨hg, ?_⟩
  have := HRS.Whole.memOsc_schwartz m (hc.toSchwartzMap hg)
  exact this

/-- Locally integrable: from the integrable pairings with the oscillator tests (a bump function equal to one on a ball). -/
theorem s21e_locInt {χ : Euc d → ℝ} (m : ℝ) (h : ∀ ψ : Euc d → ℝ, IsOscTest m ψ → Integrable (fun x => ψ x * χ x)) :
    LocallyIntegrable χ := by
  intro x
  let f : ContDiffBump x := ⟨1, 2, one_pos, one_lt_two⟩
  have hosc : IsOscTest m (f : Euc d → ℝ) := s21e_isOscTest_of_cc f.contDiff f.hasCompactSupport m
  have hI := (h f hosc).integrableOn (s := Metric.closedBall x 1)
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
  refine hI.congr_fun (fun y hy => ?_) measurableSet_closedBall
  have : f y = 1 := f.one_of_mem_closedBall hy
  simp [this]

/-- **G2.**  Two densities with the same integrable oscillator pairings coincide a.e. -/
theorem s21e_chi_ae_eq {χ χ' : Euc d → ℝ} (m : ℝ)
    (h : ∀ ψ : Euc d → ℝ, IsOscTest m ψ → Integrable (fun x => ψ x * χ x))
    (h' : ∀ ψ : Euc d → ℝ, IsOscTest m ψ → Integrable (fun x => ψ x * χ' x))
    (hpair : ∀ ψ : Euc d → ℝ, IsOscTest m ψ → ∫ x, ψ x * χ x = ∫ x, ψ x * χ' x) :
    χ =ᵐ[volume] χ' := by
  refine ae_eq_of_integral_contDiff_smul_eq (s21e_locInt m h) (s21e_locInt m h') ?_
  intro g hg hc
  have := hpair g (s21e_isOscTest_of_cc hg hc m)
  simpa only [smul_eq_mul] using this

/-- Spatial integrals against an a.e.-equal density agree. -/
theorem s21e_int_congr {χ χ' : Euc d → ℝ} (hae : χ =ᵐ[volume] χ') (G : Euc d → ℝ) :
    ∫ x, G x * χ x = ∫ x, G x * χ' x := by
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

/-- Iterated integrals with a product of two densities. -/
theorem s21e_iter_congr {χ₁ χ₁' χ₂ χ₂' : Euc d → ℝ} (h₁ : χ₁ =ᵐ[volume] χ₁') (h₂ : χ₂ =ᵐ[volume] χ₂')
    (K : Euc d → Euc d → ℝ) :
    ∫ x, ∫ y, K x y * χ₁ x * χ₂ y = ∫ x, ∫ y, K x y * χ₁' x * χ₂' y := by
  refine integral_congr_ae ?_
  filter_upwards [h₁] with x hx
  refine integral_congr_ae ?_
  filter_upwards [h₂] with y hy
  rw [hx, hy]

/-- The product of two a.e.-equal densities is a.e. equal on the product space. -/
theorem s21e_prod_ae {χ₁ χ₁' χ₂ χ₂' : Euc d → ℝ} (h₁ : χ₁ =ᵐ[volume] χ₁') (h₂ : χ₂ =ᵐ[volume] χ₂')
    (K : Euc d → Euc d → ℝ) :
    (fun p : Euc d × Euc d => K p.1 p.2 * χ₁ p.1 * χ₂ p.2) =ᵐ[volume]
      (fun p : Euc d × Euc d => K p.1 p.2 * χ₁' p.1 * χ₂' p.2) := by
  have e1 : (fun p : Euc d × Euc d => χ₁ p.1) =ᵐ[(volume : Measure (Euc d × Euc d))] (fun p => χ₁' p.1) :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))).ae_eq_comp h₁
  have e2 : (fun p : Euc d × Euc d => χ₂ p.2) =ᵐ[(volume : Measure (Euc d × Euc d))] (fun p => χ₂' p.2) :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))).ae_eq_comp h₂
  filter_upwards [e1, e2] with p hp1 hp2
  rw [hp1, hp2]

theorem s21e_cfi_mono (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (β₀ : ℝ) (μ0 : Measure (Euc d))
    (t : Fin 3 → ℝ) (φ : Fin 3 → Euc d → ℝ) (χ χ' : Fin 3 → ℝ → Euc d → ℝ) (Tm : ℝ)
    (htm : ∀ i, t i ≤ Tm) (hae : ∀ i, ∀ r ∈ Set.Icc (0 : ℝ) Tm, χ i r =ᵐ[volume] χ' i r) :
    CubicFormulaIntegrable D ρ β₀ μ0 t φ χ → CubicFormulaIntegrable D ρ β₀ μ0 t φ χ' := by
  have hsub : ∀ i : Fin 3, ∀ r ∈ Set.Icc (0 : ℝ) (t i), r ∈ Set.Icc (0 : ℝ) Tm :=
    fun i r hr => ⟨hr.1, hr.2.trans (htm i)⟩
  have hsub2 : ∀ i : Fin 3, ∀ r ∈ Set.Icc (0 : ℝ) (min (t i) (t (i + 1))), r ∈ Set.Icc (0 : ℝ) (t i) :=
    fun i r hr => ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  intro h
  unfold CubicFormulaIntegrable at h ⊢
  simp only [] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, fun i r hr => ?_, fun i => ?_, fun i r hr => ?_, fun i => ?_⟩
  · exact (h2 i r hr).congr (s21e_prod_ae (hae _ r (hsub i r hr)) (hae _ r (hsub i r hr)) _)
  · refine (h3 i).congr_fun (fun r hr => ?_) measurableSet_Icc
    exact s21e_iter_congr (hae _ r (hsub i r hr)) (hae _ r (hsub i r hr)) _
  · refine (h4 i r hr).congr ?_
    filter_upwards [hae _ r (hsub i r (hsub2 i r hr))] with x hx
    rw [hx]
  · refine (h5 i).congr_fun (fun r hr => ?_) measurableSet_Icc
    exact s21e_int_congr (hae _ r (hsub i r (hsub2 i r hr))) _

/-- **Representative independence of the cubic formula.**  If two density families agree a.e. in space at every `r ∈ [0,Tm]`, with all observation times
`t_i ≤ Tm`, then `cubicFormula` and `CubicFormulaIntegrable` take the same value. -/
theorem s21e_cubicFormula_congr (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (β β₀ : ℝ) (μ0 : Measure (Euc d))
    (t : Fin 3 → ℝ) (φ : Fin 3 → Euc d → ℝ) (χ χ' : Fin 3 → ℝ → Euc d → ℝ) (Tm : ℝ)
    (htm : ∀ i, t i ≤ Tm) (hae : ∀ i, ∀ r ∈ Set.Icc (0 : ℝ) Tm, χ i r =ᵐ[volume] χ' i r) :
    cubicFormula D ρ β β₀ μ0 t φ χ = cubicFormula D ρ β β₀ μ0 t φ χ' ∧
      (CubicFormulaIntegrable D ρ β₀ μ0 t φ χ ↔ CubicFormulaIntegrable D ρ β₀ μ0 t φ χ') := by
  have hsub : ∀ i : Fin 3, ∀ r ∈ Set.Icc (0 : ℝ) (t i), r ∈ Set.Icc (0 : ℝ) Tm :=
    fun i r hr => ⟨hr.1, hr.2.trans (htm i)⟩
  have hsub2 : ∀ i : Fin 3, ∀ r ∈ Set.Icc (0 : ℝ) (min (t i) (t (i + 1))), r ∈ Set.Icc (0 : ℝ) (t i) :=
    fun i r hr => ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  set f : Fin 3 → ℝ → Euc d → ℝ := fun i r => propagatorW (D.coeff ρ) r (t i) (φ i) with hf
  have hA : ∀ i : Fin 3, ∀ r ∈ Set.Icc (0 : ℝ) (t i),
      (∫ x, ∫ y, commutatorKernel d D.s (fun z => gradient (f i r) z) x y * χ (i + 1) r x * χ (i + 2) r y) =
        ∫ x, ∫ y, commutatorKernel d D.s (fun z => gradient (f i r) z) x y * χ' (i + 1) r x * χ' (i + 2) r y :=
    fun i r hr => s21e_iter_congr (hae _ r (hsub i r hr)) (hae _ r (hsub i r hr)) _
  have hB : ∀ i : Fin 3, ∀ r ∈ Set.Icc (0 : ℝ) (min (t i) (t (i + 1))),
      (∫ x, inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x) =
        ∫ x, inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ' (i + 2) r x :=
    fun i r hr => s21e_int_congr (hae _ r (hsub i r (hsub2 i r hr))) _
  refine ⟨?_, ?_⟩
  · have e1 : (∑ i : Fin 3, ∫ r in Set.Icc (0 : ℝ) (t i), ∫ x, ∫ y,
          commutatorKernel d D.s (fun z => gradient (f i r) z) x y * χ (i + 1) r x * χ (i + 2) r y) =
        ∑ i : Fin 3, ∫ r in Set.Icc (0 : ℝ) (t i), ∫ x, ∫ y,
          commutatorKernel d D.s (fun z => gradient (f i r) z) x y * χ' (i + 1) r x * χ' (i + 2) r y :=
      Finset.sum_congr rfl fun i _ => setIntegral_congr_fun measurableSet_Icc fun r hr => hA i r hr
    have e2 : (∑ i : Fin 3, ∫ r in Set.Icc (0 : ℝ) (min (t i) (t (i + 1))), ∫ x,
          inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x) =
        ∑ i : Fin 3, ∫ r in Set.Icc (0 : ℝ) (min (t i) (t (i + 1))), ∫ x,
          inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ' (i + 2) r x :=
      Finset.sum_congr rfl fun i _ => setIntegral_congr_fun measurableSet_Icc fun r hr => hB i r hr
    unfold cubicFormula
    simp only []
    rw [e1, e2]
  · exact ⟨s21e_cfi_mono D ρ β₀ μ0 t φ χ χ' Tm htm hae, s21e_cfi_mono D ρ β₀ μ0 t φ χ' χ Tm htm (fun i r hr => (hae i r hr).symm)⟩

end HRS.MS.S21E
