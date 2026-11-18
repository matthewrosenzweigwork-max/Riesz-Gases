import HRS.MS.S111K4R5

/-!
# S11.1 / V02 (S11K4), Pro `R26-T6C.V07` (part): the abstract shift-split of the cubic formula
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole

variable {d : ℕ}

/-- The integrability clause of `CubicFormulaIntegrable`, with the orbit `f` and the initial response `r0` explicit. -/
def K4Cfi (s : ℝ) (μ0 : Measure (Euc d)) (t : Fin 3 → ℝ) (f : Fin 3 → ℝ → Euc d → ℝ)
    (r0 : Fin 3 → Euc d → ℝ) (χ : Fin 3 → ℝ → Euc d → ℝ) : Prop :=
  Integrable (fun x => r0 0 x * r0 1 x * r0 2 x) μ0 ∧
  (∀ i : Fin 3, ∀ r ∈ Set.Icc (0 : ℝ) (t i),
    Integrable (fun p : Euc d × Euc d =>
      commutatorKernel d s (fun z => gradient (f i r) z) p.1 p.2 * χ (i + 1) r p.1 * χ (i + 2) r p.2)) ∧
  (∀ i : Fin 3, IntegrableOn (fun r => ∫ x, ∫ y,
      commutatorKernel d s (fun z => gradient (f i r) z) x y * χ (i + 1) r x * χ (i + 2) r y)
    (Set.Icc (0 : ℝ) (t i))) ∧
  (∀ i : Fin 3, ∀ r ∈ Set.Icc (0 : ℝ) (min (t i) (t (i + 1))),
    Integrable (fun x => inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x)) ∧
  (∀ i : Fin 3, IntegrableOn (fun r => ∫ x,
      inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x)
    (Set.Icc (0 : ℝ) (min (t i) (t (i + 1)))))

/-- The value of `cubicFormula`, with the orbit `f` and the initial response `r0` explicit. -/
def K4Cf (s β : ℝ) (μ0 : Measure (Euc d)) (t : Fin 3 → ℝ) (f : Fin 3 → ℝ → Euc d → ℝ)
    (r0 : Fin 3 → Euc d → ℝ) (χ : Fin 3 → ℝ → Euc d → ℝ) : ℝ :=
  (∫ x, r0 0 x * r0 1 x * r0 2 x ∂μ0)
    - (∑ i : Fin 3, ∫ r in Set.Icc (0 : ℝ) (t i), ∫ x, ∫ y,
        commutatorKernel d s (fun z => gradient (f i r) z) x y * χ (i + 1) r x * χ (i + 2) r y)
    + (2 / β) * ∑ i : Fin 3, ∫ r in Set.Icc (0 : ℝ) (min (t i) (t (i + 1))), ∫ x,
        inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x

theorem k4_cfi_iff (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (β₀ : ℝ) (μ0 : Measure (Euc d)) (t : Fin 3 → ℝ)
    (φ : Fin 3 → Euc d → ℝ) (χ : Fin 3 → ℝ → Euc d → ℝ) :
    CubicFormulaIntegrable D ρ β₀ μ0 t φ χ ↔
      K4Cfi D.s μ0 t (fun i r => propagatorW (D.coeff ρ) r (t i) (φ i))
        (fun i => HRS.Whole.responseInverse (HRS.Whole.rieszKernel d D.s) μ0 β₀ (propagatorW (D.coeff ρ) 0 (t i) (φ i))) χ :=
  Iff.rfl

theorem k4_cf_eq (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (β β₀ : ℝ) (μ0 : Measure (Euc d)) (t : Fin 3 → ℝ)
    (φ : Fin 3 → Euc d → ℝ) (χ : Fin 3 → ℝ → Euc d → ℝ) :
    cubicFormula D ρ β β₀ μ0 t φ χ =
      K4Cf D.s β μ0 t (fun i r => propagatorW (D.coeff ρ) r (t i) (φ i))
        (fun i => HRS.Whole.responseInverse (HRS.Whole.rieszKernel d D.s) μ0 β₀ (propagatorW (D.coeff ρ) 0 (t i) (φ i))) χ :=
  rfl

theorem k4_iter_congr {F F' : Euc d → Euc d → ℝ}
    (hF : Integrable (fun p : Euc d × Euc d => F p.1 p.2) (volume.prod volume))
    (hF' : Integrable (fun p : Euc d × Euc d => F' p.1 p.2) (volume.prod volume))
    (h : (fun p : Euc d × Euc d => F p.1 p.2) =ᵐ[volume.prod volume] fun p => F' p.1 p.2) :
    (∫ x, ∫ y, F x y) = ∫ x, ∫ y, F' x y :=
  (integral_prod (fun p : Euc d × Euc d => F p.1 p.2) hF).symm.trans
    ((integral_congr_ae h).trans (integral_prod (fun p : Euc d × Euc d => F' p.1 p.2) hF'))

theorem k4_shift_core {s β : ℝ} {μ0 : Measure (Euc d)} {u : ℝ} (hu : 0 ≤ u) {T : ℝ} (τ : Fin 3 → ℝ)
    (hτ0 : ∀ i, 0 ≤ τ i) (hτT : ∀ i, τ i ≤ T)
    {f g : Fin 3 → ℝ → Euc d → ℝ} {χ χ0 : Fin 3 → ℝ → Euc d → ℝ} {r0 r0' : Fin 3 → Euc d → ℝ}
    (hf : ∀ i, ∀ a ∈ Icc (0 : ℝ) (τ i), f i (u + a) = g i a)
    (hχ : ∀ j, ∀ a ∈ Icc (0 : ℝ) T, χ j (u + a) =ᵐ[volume] χ0 j a)
    (Ct Dt : Fin 3 → ℝ → ℝ)
    (hlowC : ∀ i, ∀ r ∈ Icc (0 : ℝ) u,
      Integrable (fun p : Euc d × Euc d =>
        commutatorKernel d s (fun z => gradient (f i r) z) p.1 p.2 * χ (i + 1) r p.1 * χ (i + 2) r p.2) ∧
      (∫ x, ∫ y, commutatorKernel d s (fun z => gradient (f i r) z) x y * χ (i + 1) r x * χ (i + 2) r y) =
        Ct i r)
    (hlowD : ∀ i, ∀ r ∈ Icc (0 : ℝ) u,
      Integrable (fun x => inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x) ∧
      (∫ x, inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x) = Dt i r)
    (hCt : ∀ i, ContinuousOn (Ct i) (Icc 0 u)) (hDt : ∀ i, ContinuousOn (Dt i) (Icc 0 u))
    (hI0 : K4Cfi s μ0 τ g r0' χ0) (hA : Integrable (fun x => r0 0 x * r0 1 x * r0 2 x) μ0) :
    K4Cfi s μ0 (fun i => u + τ i) f r0 χ ∧
      K4Cf s β μ0 (fun i => u + τ i) f r0 χ - K4Cf s β μ0 τ g r0' χ0 =
        ((∫ x, r0 0 x * r0 1 x * r0 2 x ∂μ0) - ∫ x, r0' 0 x * r0' 1 x * r0' 2 x ∂μ0) -
          (∑ i : Fin 3, ∫ r in Icc (0 : ℝ) u, Ct i r) + (2 / β) * ∑ i : Fin 3, ∫ r in Icc (0 : ℝ) u, Dt i r := by
  obtain ⟨hA0, hP0, hQ0, hR0, hS0⟩ := hI0
  -- the shifted commutator integrand
  have hshiftC_int : ∀ i : Fin 3, ∀ a ∈ Icc (0 : ℝ) (τ i),
      Integrable (fun p : Euc d × Euc d =>
        commutatorKernel d s (fun z => gradient (f i (u + a)) z) p.1 p.2 * χ (i + 1) (u + a) p.1 *
          χ (i + 2) (u + a) p.2) := by
    intro i a ha
    have h1 := hP0 i a ha
    rw [← hf i a ha] at h1
    exact h1.congr (k4_ae_comm (κ := fun p : Euc d × Euc d =>
      commutatorKernel d s (fun z => gradient (f i (u + a)) z) p.1 p.2)
      (hχ (i + 1) a ⟨ha.1, ha.2.trans (hτT i)⟩).symm (hχ (i + 2) a ⟨ha.1, ha.2.trans (hτT i)⟩).symm)
  have hshiftC_eq : ∀ i : Fin 3, ∀ a ∈ Icc (0 : ℝ) (τ i),
      (∫ x, ∫ y, commutatorKernel d s (fun z => gradient (f i (u + a)) z) x y * χ (i + 1) (u + a) x *
          χ (i + 2) (u + a) y) =
        ∫ x, ∫ y, commutatorKernel d s (fun z => gradient (g i a) z) x y * χ0 (i + 1) a x * χ0 (i + 2) a y := by
    intro i a ha
    have h1 := hP0 i a ha
    refine k4_iter_congr (F := fun x y => commutatorKernel d s (fun z => gradient (f i (u + a)) z) x y *
        χ (i + 1) (u + a) x * χ (i + 2) (u + a) y)
      (F' := fun x y => commutatorKernel d s (fun z => gradient (g i a) z) x y *
        χ0 (i + 1) a x * χ0 (i + 2) a y) (hshiftC_int i a ha) h1 ?_
    have := k4_ae_comm (κ := fun p : Euc d × Euc d =>
      commutatorKernel d s (fun z => gradient (g i a) z) p.1 p.2)
      (hχ (i + 1) a ⟨ha.1, ha.2.trans (hτT i)⟩) (hχ (i + 2) a ⟨ha.1, ha.2.trans (hτT i)⟩)
    have hrw := hf i a ha
    simp only [hrw]
    exact this
  -- the shifted Dirichlet integrand
  have hmin : ∀ i : Fin 3, min (u + τ i) (u + τ (i + 1)) = u + min (τ i) (τ (i + 1)) := fun i =>
    min_add_add_left u _ _
  have hshiftD_int : ∀ i : Fin 3, ∀ a ∈ Icc (0 : ℝ) (min (τ i) (τ (i + 1))),
      Integrable (fun x => inner ℝ (gradient (f i (u + a)) x) (gradient (f (i + 1) (u + a)) x) *
        χ (i + 2) (u + a) x) := by
    intro i a ha
    have hai : a ∈ Icc (0 : ℝ) (τ i) := ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
    have hai1 : a ∈ Icc (0 : ℝ) (τ (i + 1)) := ⟨ha.1, ha.2.trans (min_le_right _ _)⟩
    have h1 := hR0 i a ha
    rw [← hf i a hai, ← hf (i + 1) a hai1] at h1
    refine h1.congr ?_
    filter_upwards [(hχ (i + 2) a ⟨ha.1, ha.2.trans ((min_le_left _ _).trans (hτT i))⟩).symm] with x hx
    rw [hx]
  have hshiftD_eq : ∀ i : Fin 3, ∀ a ∈ Icc (0 : ℝ) (min (τ i) (τ (i + 1))),
      (∫ x, inner ℝ (gradient (f i (u + a)) x) (gradient (f (i + 1) (u + a)) x) * χ (i + 2) (u + a) x) =
        ∫ x, inner ℝ (gradient (g i a) x) (gradient (g (i + 1) a) x) * χ0 (i + 2) a x := by
    intro i a ha
    have hai : a ∈ Icc (0 : ℝ) (τ i) := ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
    have hai1 : a ∈ Icc (0 : ℝ) (τ (i + 1)) := ⟨ha.1, ha.2.trans (min_le_right _ _)⟩
    rw [hf i a hai, hf (i + 1) a hai1]
    refine integral_congr_ae ?_
    filter_upwards [hχ (i + 2) a ⟨ha.1, ha.2.trans ((min_le_left _ _).trans (hτT i))⟩] with x hx
    rw [hx]
  -- integrability on the low windows
  have hCtI : ∀ i, IntegrableOn (Ct i) (Icc 0 u) := fun i => (hCt i).integrableOn_Icc
  have hDtI : ∀ i, IntegrableOn (Dt i) (Icc 0 u) := fun i => (hDt i).integrableOn_Icc
  -- the splits
  have hsplitC : ∀ i : Fin 3,
      IntegrableOn (fun r => ∫ x, ∫ y, commutatorKernel d s (fun z => gradient (f i r) z) x y *
          χ (i + 1) r x * χ (i + 2) r y) (Icc 0 (u + τ i)) ∧
      (∫ r in Icc 0 (u + τ i), ∫ x, ∫ y, commutatorKernel d s (fun z => gradient (f i r) z) x y *
          χ (i + 1) r x * χ (i + 2) r y) =
        (∫ r in Icc (0 : ℝ) u, Ct i r) + ∫ a in Icc 0 (τ i), ∫ x, ∫ y,
          commutatorKernel d s (fun z => gradient (g i a) z) x y * χ0 (i + 1) a x * χ0 (i + 2) a y := by
    intro i
    have hG : IntegrableOn (fun r => ∫ x, ∫ y, commutatorKernel d s (fun z => gradient (f i r) z) x y *
        χ (i + 1) r x * χ (i + 2) r y) (Icc 0 u) :=
      (hCtI i).congr_fun (fun r hr => (hlowC i r hr).2.symm) measurableSet_Icc
    have heq : ∀ r ∈ Ioc u (u + τ i), (∫ x, ∫ y, commutatorKernel d s (fun z => gradient (f i r) z) x y *
        χ (i + 1) r x * χ (i + 2) r y) =
        ∫ x, ∫ y, commutatorKernel d s (fun z => gradient (g i (r - u)) z) x y *
          χ0 (i + 1) (r - u) x * χ0 (i + 2) (r - u) y := by
      intro r hr
      have ha : r - u ∈ Icc (0 : ℝ) (τ i) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have := hshiftC_eq i (r - u) ha
      rwa [show u + (r - u) = r by ring] at this
    obtain ⟨h1, h2⟩ := k4_split_shift hu (hτ0 i) hG (hQ0 i) heq
    refine ⟨h1, ?_⟩
    rw [h2, setIntegral_congr_fun measurableSet_Icc (fun r hr => (hlowC i r hr).2)]
  have hsplitD : ∀ i : Fin 3,
      IntegrableOn (fun r => ∫ x, inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x)
        (Icc 0 (u + min (τ i) (τ (i + 1)))) ∧
      (∫ r in Icc 0 (u + min (τ i) (τ (i + 1))), ∫ x,
          inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x) =
        (∫ r in Icc (0 : ℝ) u, Dt i r) + ∫ a in Icc 0 (min (τ i) (τ (i + 1))), ∫ x,
          inner ℝ (gradient (g i a) x) (gradient (g (i + 1) a) x) * χ0 (i + 2) a x := by
    intro i
    have hG : IntegrableOn (fun r => ∫ x, inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) *
        χ (i + 2) r x) (Icc 0 u) :=
      (hDtI i).congr_fun (fun r hr => (hlowD i r hr).2.symm) measurableSet_Icc
    have heq : ∀ r ∈ Ioc u (u + min (τ i) (τ (i + 1))), (∫ x,
        inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x) =
        ∫ x, inner ℝ (gradient (g i (r - u)) x) (gradient (g (i + 1) (r - u)) x) * χ0 (i + 2) (r - u) x := by
      intro r hr
      have ha : r - u ∈ Icc (0 : ℝ) (min (τ i) (τ (i + 1))) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have := hshiftD_eq i (r - u) ha
      rwa [show u + (r - u) = r by ring] at this
    obtain ⟨h1, h2⟩ := k4_split_shift hu (le_min (hτ0 i) (hτ0 (i + 1))) hG (hS0 i) heq
    refine ⟨h1, ?_⟩
    rw [h2, setIntegral_congr_fun measurableSet_Icc (fun r hr => (hlowD i r hr).2)]
  refine ⟨⟨hA, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i r hr
    by_cases hru : r ≤ u
    · exact (hlowC i r ⟨hr.1, hru⟩).1
    · push_neg at hru
      have ha : r - u ∈ Icc (0 : ℝ) (τ i) := ⟨by linarith, by linarith [hr.2]⟩
      have := hshiftC_int i (r - u) ha
      rwa [show u + (r - u) = r by ring] at this
  · intro i
    exact (hsplitC i).1
  · intro i r hr
    have hr' : r ∈ Icc (0 : ℝ) (u + min (τ i) (τ (i + 1))) := by rw [← hmin i]; exact hr
    by_cases hru : r ≤ u
    · exact (hlowD i r ⟨hr'.1, hru⟩).1
    · push_neg at hru
      have ha : r - u ∈ Icc (0 : ℝ) (min (τ i) (τ (i + 1))) := ⟨by linarith, by linarith [hr'.2]⟩
      have := hshiftD_int i (r - u) ha
      rwa [show u + (r - u) = r by ring] at this
  · intro i
    have := (hsplitD i).1
    rw [← hmin i] at this
    exact this
  · unfold K4Cf
    have e1 : (∑ i : Fin 3, ∫ r in Icc (0 : ℝ) (u + τ i), ∫ x, ∫ y,
          commutatorKernel d s (fun z => gradient (f i r) z) x y * χ (i + 1) r x * χ (i + 2) r y) =
        (∑ i : Fin 3, ∫ r in Icc (0 : ℝ) u, Ct i r) + ∑ i : Fin 3, ∫ a in Icc (0 : ℝ) (τ i), ∫ x, ∫ y,
          commutatorKernel d s (fun z => gradient (g i a) z) x y * χ0 (i + 1) a x * χ0 (i + 2) a y := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (hsplitC i).2
    have e2 : (∑ i : Fin 3, ∫ r in Icc (0 : ℝ) (min (u + τ i) (u + τ (i + 1))), ∫ x,
          inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x) =
        (∑ i : Fin 3, ∫ r in Icc (0 : ℝ) u, Dt i r) + ∑ i : Fin 3, ∫ a in Icc (0 : ℝ) (min (τ i) (τ (i + 1))),
          ∫ x, inner ℝ (gradient (g i a) x) (gradient (g (i + 1) a) x) * χ0 (i + 2) a x := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hmin i]
      exact (hsplitD i).2
    simp only [e1, e2]
    ring

end HRS.MS.S111K4
