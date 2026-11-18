import HRS.MC.S7PIF6

/-!
# Packet piF6 (F7): `s7_PIF_ito_cyl_proof` (namespace `HRS.MC.Sec7.S7PIF6`)

Telescoping of the one-piece identity `S7PIF6_piece_aux` over the sorted breakpoints `{0, T} ∪ {t_i}`.  The statement is
copied verbatim from `HRS/MC/S7PIPlan.lean` (`HRS.MC.Sec7.PIPlan.s7_PIF_ito_cyl`); the tie is in `HRS/MC/S7PIF6Tie.lean`.
Route: the claim `Q(y)` (cylindrical identity on `[0,y]`) is proved for every breakpoint `y` by strong induction on the
number of breakpoints `≤ y`: the predecessor `x` of `y` among the breakpoints has no observation time in `(x,y)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.S7PIF6

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

variable {d : ℕ}

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

/-- **F7 (telescoping over the sorted observation times: the cylindrical Itô identity on `[0,T]`)**
(statement of `HRS.MC.Sec7.PIPlan.s7_PIF_ito_cyl`, copied verbatim). -/
theorem s7_PIF_ito_cyl_proof {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i))
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 4 G) :
    ∃ Mart : Ω → ℝ, Integrable Mart P ∧ ∫ ω, Mart ω ∂P = 0 ∧ ∀ᵐ ω ∂P,
      G (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) T)) -
        gaussHeat (obsCov R.D R.ρ t φ) G 0 (obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω))) =
      (∫ r in Set.Ioc 0 T, (-(Real.sqrt N)⁻¹ * cylA R m T P X t φ G ω r +
        (1 / (2 * Real.sqrt N)) * cylJ R m T P X t φ G ω r)) + Mart ω := by
  classical
  obtain ⟨bd, Φc, -, -, -, -, -, hid⟩ :=
    HRS.MC.Sec7.S7PIF5.s7_PIF_itoprocess_proof R m hm T hT N hN P X₀ W X hreal hF t φ ht hφ
  -- the claim on `[0,y]`
  let dens : Ω → ℝ → ℝ := fun ω r => -(Real.sqrt N)⁻¹ * cylA R m T P X t φ G ω r +
    (1 / (2 * Real.sqrt N)) * cylJ R m T P X t φ G ω r
  let Qp : ℝ → Prop := fun y => ∃ Mart : Ω → ℝ, Integrable Mart P ∧ ∫ ω, Mart ω ∂P = 0 ∧ ∀ᵐ ω ∂P,
    IntegrableOn (dens ω) (Set.Ioc 0 y) ∧
    gaussHeat (obsCov R.D R.ρ t φ) G y (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) y)) -
      gaussHeat (obsCov R.D R.ρ t φ) G 0
        (obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω))) =
      (∫ r in Set.Ioc 0 y, dens ω r) + Mart ω
  have base : Qp 0 := by
    refine ⟨fun _ => 0, integrable_zero _ _ _, by simp, ?_⟩
    filter_upwards [hid] with ω hω
    have h0 := hω 0 ⟨le_rfl, hT.le⟩
    rw [itoProcess_zero] at h0
    simp [h0]
  have hstep : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ T → (∀ i, ¬ (x < t i ∧ t i < y)) → Qp x → Qp y := by
    intro x y hx hxy hy hno ⟨M1, hM1i, hM10, hM1⟩
    obtain ⟨M2, hM2i, hM20, hM2⟩ :=
      S7PIF6_piece_aux R m hm T hT N hN P X₀ W X hreal hF t φ ht hφ G hG x y hx hxy hy hno
    refine ⟨fun ω => M1 ω + M2 ω, hM1i.add hM2i, by rw [integral_add hM1i hM2i, hM10, hM20, add_zero], ?_⟩
    filter_upwards [hM1, hM2] with ω ⟨hi1, he1⟩ ⟨hi2, he2⟩
    have hu : Set.Ioc 0 x ∪ Set.Ioc x y = Set.Ioc 0 y := Set.Ioc_union_Ioc_eq_Ioc hx hxy
    have hint : IntegrableOn (dens ω) (Set.Ioc 0 y) := by rw [← hu]; exact hi1.union hi2
    refine ⟨hint, ?_⟩
    have hsplit : ∫ r in Set.Ioc 0 y, dens ω r = (∫ r in Set.Ioc 0 x, dens ω r) + ∫ r in Set.Ioc x y, dens ω r := by
      rw [← hu, setIntegral_union (Set.disjoint_left.2 fun z hz hz' => absurd hz.2 (not_le.2 hz'.1))
        measurableSet_Ioc hi1 hi2]
    rw [hsplit]
    linarith
  -- the breakpoints
  let Z : Finset ℝ := insert 0 (insert T (Finset.univ.image t))
  have hZ0 : ∀ z ∈ Z, 0 ≤ z := by
    intro z hz
    simp only [Z, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with rfl | rfl | ⟨i, rfl⟩
    · exact le_rfl
    · exact hT.le
    · exact (ht i).1
  have hZT : ∀ z ∈ Z, z ≤ T := by
    intro z hz
    simp only [Z, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with rfl | rfl | ⟨i, rfl⟩
    · exact hT.le
    · exact le_rfl
    · exact (ht i).2
  have hZ0m : (0 : ℝ) ∈ Z := by simp [Z]
  have hZTm : T ∈ Z := by simp [Z]
  have hZtm : ∀ i, t i ∈ Z := fun i => by simp [Z]
  have key : ∀ n : ℕ, ∀ y ∈ Z, (Z.filter (fun z => z ≤ y)).card ≤ n → Qp y := by
    intro n
    induction n with
    | zero =>
      intro y hy hc
      exfalso
      have hmem : y ∈ Z.filter (fun z => z ≤ y) := Finset.mem_filter.2 ⟨hy, le_rfl⟩
      have := Finset.card_pos.2 ⟨y, hmem⟩
      omega
    | succ n ih =>
      intro y hy hc
      by_cases hy0 : y = 0
      · subst hy0; exact base
      · have hypos : 0 < y := lt_of_le_of_ne (hZ0 y hy) (Ne.symm hy0)
        have hne : (Z.filter (fun z => z < y)).Nonempty := ⟨0, Finset.mem_filter.2 ⟨hZ0m, hypos⟩⟩
        set x := (Z.filter (fun z => z < y)).max' hne with hxdef
        have hxmem : x ∈ Z.filter (fun z => z < y) := Finset.max'_mem _ _
        have hxZ : x ∈ Z := (Finset.mem_filter.1 hxmem).1
        have hxy : x < y := (Finset.mem_filter.1 hxmem).2
        have hcard : (Z.filter (fun z => z ≤ x)).card ≤ n := by
          have hsub : Z.filter (fun z => z ≤ x) ⊂ Z.filter (fun z => z ≤ y) := by
            refine ⟨fun z hz => ?_, fun hh => ?_⟩
            · have := Finset.mem_filter.1 hz
              exact Finset.mem_filter.2 ⟨this.1, this.2.trans hxy.le⟩
            · have := hh (Finset.mem_filter.2 ⟨hy, le_rfl⟩)
              exact absurd (Finset.mem_filter.1 this).2 (not_le.2 hxy)
          have := Finset.card_lt_card hsub
          omega
        refine hstep x y (hZ0 x hxZ) hxy.le (hZT y hy) (fun i h => ?_) (ih x hxZ hcard)
        obtain ⟨h1, h2⟩ := h
        have hti : t i ∈ Z.filter (fun z => z < y) := Finset.mem_filter.2 ⟨hZtm i, h2⟩
        exact absurd (Finset.le_max' _ _ hti) (not_le.2 h1)
  obtain ⟨Mart, hMi, hM0, hM⟩ := key _ T hZTm le_rfl
  refine ⟨Mart, hMi, hM0, ?_⟩
  filter_upwards [hM] with ω hω'
  have hω := hω'.2
  rw [S7PIF6_gaussHeat_T R t φ ht] at hω
  exact hω

end Prob

end HRS.MC.Sec7.S7PIF6

end
