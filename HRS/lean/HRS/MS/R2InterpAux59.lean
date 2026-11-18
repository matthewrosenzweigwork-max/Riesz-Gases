import HRS.MS.R2InterpAux58

/-!
# S10.2 (worker S102), part 59 (packet F6): Itô's formula for the cylindrical heat function on one piece
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}

/-- **F6**: Itô's formula on a piece `[a,b]` without observation times in `(a,b)`, given the Itô-process representation of the observations. -/
theorem s102_ito_piece (hs : S102Std C m T r c) (hT : 0 < T) (L : ℕ) (sQ : ℝ) (μ : Measure (Euc d))
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
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hno : ∀ k : Fin (s102_q d L), ¬ (a < s102_tk hT L k ∧ s102_tk hT L k < b))
    {G : EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ} (hG4 : MemCb 4 G) :
    ∃ Mart : Ω → ℝ, Integrable Mart P ∧ ∫ ζ, Mart ζ ∂P = 0 ∧ ∀ᵐ ζ ∂P,
      IntegrableOn (fun u => -(Real.sqrt N)⁻¹ * s102_cylA C m T sQ μ P X (s102_tauk hT L) (s102_alk L) G ζ u +
        (1 / (2 * Real.sqrt N)) * s102_cylJ C m T μ P X (s102_tauk hT L) (s102_alk L) G ζ u) (Ioc a b) ∧
      gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G b
          (s102_obs (s102_tauk hT L) (s102_alk L) (s102_Y C m T P X ζ b)) -
        gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G a
          (s102_obs (s102_tauk hT L) (s102_alk L) (s102_Y C m T P X ζ a)) =
      (∫ u in Ioc a b, (-(Real.sqrt N)⁻¹ * s102_cylA C m T sQ μ P X (s102_tauk hT L) (s102_alk L) G ζ u +
        (1 / (2 * Real.sqrt N)) * s102_cylJ C m T μ P X (s102_tauk hT L) (s102_alk L) G ζ u)) + Mart ζ := by
  classical
  obtain ⟨f, hf, hfeq, hfd⟩ := s102_c12 hs hT L γ hγ ha hab hb hno hG4
  obtain ⟨Cn, hCn0, hCn⟩ := s102_Phic_bound hs hT L X
  set K1 : ℝ := ⨆ z, ‖iteratedFDeriv ℝ 1 G z‖ with hK1
  have hK10 : 0 ≤ K1 := Real.iSup_nonneg fun z => norm_nonneg _
  set X0f : Ω → EuclideanSpace ℝ (Fin (s102_q d L)) :=
    fun ζ => s102_obs (s102_tauk hT L) (s102_alk L) (s102_y0 C m T P X ζ) with hX0f
  set Z : ℝ → Ω → EuclideanSpace ℝ (Fin (s102_q d L)) := itoProcess P ℱ W' X0f bd Φc with hZdef
  have hbound : ∀ u ∈ Ioc a b, ∀ ζ k, |fderiv ℝ (f u) (Z u ζ) (Φc u ζ k)| ≤ (s102_q d L : ℝ) * Cn * K1 := by
    intro u hu ζ k
    have huT : u ∈ Icc (0 : ℝ) T := ⟨ha.trans hu.1.le, hu.2.trans hb⟩
    rw [hfeq u ⟨hu.1.le, hu.2⟩, S7PIF6_lin_expand]
    calc |∑ i, (Φc u ζ k) i * fderiv ℝ (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G u) (Z u ζ)
            (EuclideanSpace.single i 1)|
        ≤ ∑ i, |(Φc u ζ k) i * fderiv ℝ (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G u)
            (Z u ζ) (EuclideanSpace.single i 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (s102_q d L), Cn * K1 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          refine mul_le_mul ?_ ?_ (abs_nonneg _) hCn0
          · rw [hΦform u ζ k i huT.1]; exact hCn u huT ζ k i
          · have h2 := S7PIF6_heat_fderiv_bound (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) hG4 u (Z u ζ)
              (EuclideanSpace.single i 1)
            have h3 : ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin (s102_q d L)))‖ = 1 := by simp
            rw [h3, mul_one] at h2
            exact h2
      _ = (s102_q d L : ℝ) * Cn * K1 := by simp [Finset.sum_const, mul_assoc]
  obtain ⟨Mart, hMi, hM0, hMeq⟩ := s102_ito_piece_abs P hW hT.le f hf X0f hX0 bd hbd Φc hΦ ha hab hb hbound
  refine ⟨Mart, hMi, hM0, ?_⟩
  filter_upwards [hMeq, hid] with ζ hM hidζ
  obtain ⟨hint, hident⟩ := hM
  have hZ : ∀ u ∈ Icc (0 : ℝ) T, Z u ζ = s102_obs (s102_tauk hT L) (s102_alk L) (s102_Y C m T P X ζ u) :=
    fun u hu => (hidζ u hu).symm
  have hsubT : Ioc a b ⊆ Icc 0 T := fun u hu => ⟨ha.trans hu.1.le, hu.2.trans hb⟩
  have hpt : ∀ u ∈ Ioc a b, itoDrift T f Z bd Φc u ζ =
      -(Real.sqrt N)⁻¹ * s102_cylA C m T sQ μ P X (s102_tauk hT L) (s102_alk L) G ζ u +
        (1 / (2 * Real.sqrt N)) * s102_cylJ C m T μ P X (s102_tauk hT L) (s102_alk L) G ζ u := by
    intro u hu
    have huT := hsubT hu
    have h := s102_drift_pt (C := C) (m := m) (mΩ := mΩ) hT L u N G f (hfeq u ⟨hu.1.le, hu.2⟩) (hfd u hu) Z ζ bd Φc
      (fun v => r2QuadField sQ μ P X v ζ) (s102_etaf μ X ζ) (fun i => hbform u ζ i huT.1)
      (fun i j => by
        simp only [hΦform _ _ _ _ huT.1]
        exact s102_bracket_grid hs.hν hT L μ (hμ u huT) hN X ζ i j)
    rw [h, hZ u huT]
    rfl
  refine ⟨(hint.mono_set hsubT).congr_fun hpt measurableSet_Ioc, ?_⟩
  have hZ' : ∀ u ∈ Icc (0 : ℝ) T, itoProcess P ℱ W' X0f bd Φc u ζ =
      s102_obs (s102_tauk hT L) (s102_alk L) (s102_Y C m T P X ζ u) := fun u hu => (hidζ u hu).symm
  rw [hfeq b ⟨hab, le_rfl⟩, hZ' b ⟨ha.trans hab, hb⟩] at hident
  rw [hfeq a ⟨le_rfl, hab⟩, hZ' a ⟨ha, hab.trans hb⟩] at hident
  rw [hident]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioc hpt

end HRS.MS.R2Interp

end
