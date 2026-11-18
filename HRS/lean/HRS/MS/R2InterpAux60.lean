import HRS.MS.R2InterpAux59

/-!
# S10.2 (worker S102), part 60 (packet F7): the cylindrical Itô identity on `[0,T]` by telescoping over the observation times
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}

/-- **F7**: `G(obs Y_T) - F(0, obs Y_0) = ∫_{(0,T]} (-N^{-1/2} cylA + (2√N)^{-1} cylJ) + Mart`. -/
theorem s102_ito_cyl (hs : S102Std C m T r c) (hT : 0 < T) (L : ℕ) (sQ : ℝ) (μ : Measure (Euc d))
    (hμ : ∀ u ∈ Icc (0 : ℝ) T, ∀ g : Euc d → ℝ, HRS.Whole.pair μ g = ∫ x, g x * C.ρ u x)
    (γ : ℝ → Measure (OscPath d m T)) (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {N : ℕ} (hN : 0 < N) {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW : IsBrownianFiltration P ℱ W')
    (bd : ℝ → Ω → EuclideanSpace ℝ (Fin (s102_q d L)))
    (Φc : ℝ → Ω → (Fin N × Fin d) → EuclideanSpace ℝ (Fin (s102_q d L)))
    (hbd : IsProgressiveLocL1 P ℱ bd) (hΦ : IsProgressiveLocL2E P ℱ Φc)
    (hX0 : ∀ t : ℝ, Measurable[ℱ t] (fun ζ => s102_obs (s102_tauk hT L) (s102_alk L) (s102_y0 C m T P X ζ)))
    (hbform : ∀ u ζ i, 0 ≤ u → bd u ζ i = -(Real.sqrt N)⁻¹ *
      s102_hh C m (s102_tauk hT L) (s102_alk L) (fun v => r2QuadField sQ μ P X v ζ) i u)
    (hΦform : ∀ u ζ k i, 0 ≤ u → Φc u ζ k i = s102_Phic C m hT L X u ζ k i)
    (hid : ∀ᵐ ζ ∂P, ∀ u ∈ Icc (0 : ℝ) T, s102_obs (s102_tauk hT L) (s102_alk L) (s102_Y C m T P X ζ u) =
      itoProcess P ℱ W' (fun ζ => s102_obs (s102_tauk hT L) (s102_alk L) (s102_y0 C m T P X ζ)) bd Φc u ζ)
    {G : EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ} (hG4 : MemCb 4 G) :
    ∃ Mart : Ω → ℝ, Integrable Mart P ∧ ∫ ζ, Mart ζ ∂P = 0 ∧ ∀ᵐ ζ ∂P,
      IntegrableOn (fun u => -(Real.sqrt N)⁻¹ * s102_cylA C m T sQ μ P X (s102_tauk hT L) (s102_alk L) G ζ u +
        (1 / (2 * Real.sqrt N)) * s102_cylJ C m T μ P X (s102_tauk hT L) (s102_alk L) G ζ u) (Ioc 0 T) ∧
      G (s102_obs (s102_tauk hT L) (s102_alk L) (s102_Y C m T P X ζ T)) -
        gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G 0
          (s102_obs (s102_tauk hT L) (s102_alk L) (s102_y0 C m T P X ζ)) =
      (∫ u in Ioc 0 T, (-(Real.sqrt N)⁻¹ * s102_cylA C m T sQ μ P X (s102_tauk hT L) (s102_alk L) G ζ u +
        (1 / (2 * Real.sqrt N)) * s102_cylJ C m T μ P X (s102_tauk hT L) (s102_alk L) G ζ u)) + Mart ζ := by
  classical
  set τ := s102_tauk hT L
  set α := s102_alk L
  set dens : Ω → ℝ → ℝ := fun ζ u => -(Real.sqrt N)⁻¹ * s102_cylA C m T sQ μ P X τ α G ζ u +
    (1 / (2 * Real.sqrt N)) * s102_cylJ C m T μ P X τ α G ζ u with hdens
  set Qp : ℝ → Prop := fun y => ∃ Mart : Ω → ℝ, Integrable Mart P ∧ ∫ ζ, Mart ζ ∂P = 0 ∧ ∀ᵐ ζ ∂P,
    IntegrableOn (dens ζ) (Ioc 0 y) ∧
    gaussHeat (s102_obsCov C m τ α) G y (s102_obs τ α (s102_Y C m T P X ζ y)) -
      gaussHeat (s102_obsCov C m τ α) G 0 (s102_obs τ α (s102_y0 C m T P X ζ)) =
      (∫ u in Ioc 0 y, dens ζ u) + Mart ζ with hQp
  have base : Qp 0 := by
    refine ⟨fun _ => 0, integrable_zero _ _ _, by simp, ?_⟩
    filter_upwards [hid] with ζ hζ
    have h0 := hζ 0 ⟨le_rfl, hT.le⟩
    rw [itoProcess_zero] at h0
    simp [h0]
  have hstep : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ T → (∀ k : Fin (s102_q d L), ¬ (x < s102_tk hT L k ∧ s102_tk hT L k < y)) →
      Qp x → Qp y := by
    intro x y hx hxy hy hno ⟨M1, hM1i, hM10, hM1⟩
    obtain ⟨M2, hM2i, hM20, hM2⟩ := s102_ito_piece hs hT L sQ μ hμ γ hγ hN P X hW bd Φc hbd hΦ hX0 hbform hΦform hid
      hx hxy hy hno hG4
    refine ⟨fun ζ => M1 ζ + M2 ζ, hM1i.add hM2i, by rw [integral_add hM1i hM2i, hM10, hM20, add_zero], ?_⟩
    filter_upwards [hM1, hM2] with ζ ⟨hi1, he1⟩ ⟨hi2, he2⟩
    have hu : Ioc 0 x ∪ Ioc x y = Ioc 0 y := Ioc_union_Ioc_eq_Ioc hx hxy
    have hint : IntegrableOn (dens ζ) (Ioc 0 y) := by rw [← hu]; exact hi1.union hi2
    refine ⟨hint, ?_⟩
    have hsplit : ∫ u in Ioc 0 y, dens ζ u = (∫ u in Ioc 0 x, dens ζ u) + ∫ u in Ioc x y, dens ζ u := by
      rw [← hu, setIntegral_union (Set.disjoint_left.2 fun z hz hz' => absurd hz.2 (not_le.2 hz'.1))
        measurableSet_Ioc hi1 hi2]
    rw [hsplit]
    linarith
  let Z : Finset ℝ := insert 0 (insert T ((Finset.univ : Finset (Fin (s102_q d L))).image (s102_tk (d := d) hT L)))
  have hZ0 : ∀ z ∈ Z, 0 ≤ z := by
    intro z hz
    simp only [Z, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with rfl | rfl | ⟨i, rfl⟩
    · exact le_rfl
    · exact hT.le
    · exact (s102_tauk hT L i).2.1
  have hZT : ∀ z ∈ Z, z ≤ T := by
    intro z hz
    simp only [Z, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with rfl | rfl | ⟨i, rfl⟩
    · exact hT.le
    · exact le_rfl
    · exact (s102_tauk hT L i).2.2
  have hZ0m : (0 : ℝ) ∈ Z := by simp [Z]
  have hZTm : T ∈ Z := by simp [Z]
  have hZtm : ∀ i : Fin (s102_q d L), s102_tk hT L i ∈ Z := fun i => by simp [Z]
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
        refine hstep x y (hZ0 x hxZ) hxy.le (hZT y hy) (fun k h => ?_) (ih x hxZ hcard)
        obtain ⟨h1, h2⟩ := h
        have hti : s102_tk hT L k ∈ Z.filter (fun z => z < y) := Finset.mem_filter.2 ⟨hZtm k, h2⟩
        exact absurd (Finset.le_max' _ _ hti) (not_le.2 h1)
  obtain ⟨Mart, hMi, hM0, hM⟩ := key _ T hZTm le_rfl
  refine ⟨Mart, hMi, hM0, ?_⟩
  filter_upwards [hM] with ζ hζ'
  obtain ⟨hint, hζ⟩ := hζ'
  rw [s102_gaussHeat_T C τ α G] at hζ
  exact ⟨hint, hζ⟩

end HRS.MS.R2Interp

end
