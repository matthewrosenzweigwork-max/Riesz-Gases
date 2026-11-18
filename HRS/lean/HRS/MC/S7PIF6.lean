import HRS.MC.S7PIF6E
import HRS.MC.S7PIF6Mart
import HRS.MC.S7PIF5

/-!
# Packet piF6 (F6): `s7_PIF_ito_piece_proof` (namespace `HRS.MC.Sec7.S7PIF6`)

Itô's formula on one interval `[a,b]` without observation time in `(a,b)`.  The statement is copied verbatim from
`HRS/MC/S7PIPlan.lean` (`HRS.MC.Sec7.PIPlan.s7_PIF_ito_piece`); the tie is in `HRS/MC/S7PIF6Tie.lean`.
Route: the `C^{1,2}` extension `f` of `gaussHeat obsCov G` (`S7PIF6_c12`, from H1b), `ito_formula` for the Itô process
`obsVec(𝖳_u ζ_N)` (F5), the pointwise identification of the drift on `(a,b]` (`S7PIF6_drift_pt`, F3 and the heat equation),
and the increment of the local integral (`S7PIF6_mart_incr`): the integrand is bounded on `(a,b]` since `G ∈ C_b^1` and
`∇U` is bounded.  The lemma `S7PIF6_piece_aux` also records the integrability of the drift density on `(a,b]`
(needed for the telescoping in F7).
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

/-- the piece with the integrability of the density -/
theorem S7PIF6_piece_aux {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i))
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 4 G) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hno : ∀ i, ¬ (a < t i ∧ t i < b)) :
    ∃ Mart : Ω → ℝ, Integrable Mart P ∧ ∫ ω, Mart ω ∂P = 0 ∧ ∀ᵐ ω ∂P,
      IntegrableOn (fun r => (-(Real.sqrt N)⁻¹ * cylA R m T P X t φ G ω r +
        (1 / (2 * Real.sqrt N)) * cylJ R m T P X t φ G ω r)) (Set.Ioc a b) ∧
      gaussHeat (obsCov R.D R.ρ t φ) G b (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) b)) -
        gaussHeat (obsCov R.D R.ρ t φ) G a (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) a)) =
      (∫ r in Set.Ioc a b, (-(Real.sqrt N)⁻¹ * cylA R m T P X t φ G ω r +
        (1 / (2 * Real.sqrt N)) * cylJ R m T P X t φ G ω r)) + Mart ω := by
  classical
  have hW := hF.brownian
  obtain ⟨f, hf, hfeq, hfd⟩ := S7PIF6_c12 R hT t φ ht hφ G hG a b ha hab hb hno
  obtain ⟨bd, Φc, hbd, hΦ, hX0, hbform, hΦform, hid⟩ :=
    HRS.MC.Sec7.S7PIF5.s7_PIF_itoprocess_proof R m hm T hT N hN P X₀ W X hreal hF t φ ht hφ
  set X0f : Ω → EuclideanSpace ℝ (Fin q) :=
    fun ω => obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) with hX0f
  set Z : ℝ → Ω → EuclideanSpace ℝ (Fin q) := itoProcess P ℱ W' X0f bd Φc with hZdef
  have hito : ∀ᵐ ω ∂P, IntegrableOn (fun s => itoDrift T f Z bd Φc s ω) (Set.Icc 0 T) ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T, f τ (Z τ ω) = f 0 (X0f ω) +
        (∫ s in Set.Icc 0 τ, itoDrift T f Z bd Φc s ω) +
        localItoIntegral P ℱ W' (itoIntegrand T Set.univ f Z Φc) τ ω :=
    ito_formula hW hT.le f hf X0f hX0 bd hbd Φc hΦ
  -- the integrand of the stochastic integral is bounded on `(a,b]`
  have hZprog : IsProgressive ℱ Z := isProgressive_itoProcess X0f hX0 bd hbd.prog Φc
  have hZc : ∀ᵐ ω ∂P, Continuous fun τ => Z τ ω := continuous_itoProcess X0f bd hbd Φc (P := P) (W := W')
  have hΨ : IsProgressiveLocL2 P ℱ (itoIntegrand T Set.univ f Z Φc) :=
    isProgressiveLocL2_itoIntegrand Set.univ isClosed_univ Set.univ (Set.Subset.refl _) f hf Z
      hZprog hZc Φc hΦ
  obtain ⟨Cn, hCn0, hCn⟩ := S7PIF6_noise_bound R X t φ (fun i => (ht i).1) hφ
  have hbound : ∀ s ∈ Set.Ioc a b, ∀ ω k, |itoIntegrand T Set.univ f Z Φc s ω k| ≤
      (q : ℝ) * (Real.sqrt N * Cn) * (⨆ z, ‖iteratedFDeriv ℝ 1 G z‖) := by
    intro s hs ω k
    have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans hs.1.le, hs.2.trans hb⟩
    have hK : 0 ≤ ⨆ z, ‖iteratedFDeriv ℝ 1 G z‖ := Real.iSup_nonneg fun z => norm_nonneg _
    have hΨeq : itoIntegrand T Set.univ f Z Φc s ω k = fderiv ℝ (f s) (Z s ω) (Φc s ω k) := by
      simp [itoIntegrand, hsT]
    rw [hΨeq, hfeq s ⟨hs.1.le, hs.2⟩, S7PIF6_lin_expand]
    calc |∑ i, (Φc s ω k) i * fderiv ℝ (gaussHeat (obsCov R.D R.ρ t φ) G s) (Z s ω)
            (EuclideanSpace.single i 1)|
        ≤ ∑ i, |(Φc s ω k) i * fderiv ℝ (gaussHeat (obsCov R.D R.ρ t φ) G s) (Z s ω)
            (EuclideanSpace.single i 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin q, (Real.sqrt N * Cn) * (⨆ z, ‖iteratedFDeriv ℝ 1 G z‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
          · rw [hΦform, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
            exact mul_le_mul_of_nonneg_left (hCn s ω k i) (Real.sqrt_nonneg _)
          · have := S7PIF6_heat_fderiv_bound (obsCov R.D R.ρ t φ) hG s (Z s ω) (EuclideanSpace.single i 1)
            simpa using this
      _ = (q : ℝ) * (Real.sqrt N * Cn) * (⨆ z, ‖iteratedFDeriv ℝ 1 G z‖) := by
          simp [Finset.sum_const, mul_assoc]
  obtain ⟨Mart, hMi, hM0, hMeq⟩ := S7PIF6_mart_incr hW hΨ hab hbound
  refine ⟨Mart, hMi, hM0, ?_⟩
  filter_upwards [hito, hid, hMeq] with ω hit hidω hMω
  obtain ⟨hint, hfor⟩ := hit
  have hZ : ∀ s ∈ Set.Icc (0 : ℝ) T, Z s ω = obsVec m T t φ
      (predicted R.D R.ρ (zetaWin m T 0 P X ω) s) := fun s hs => (hidω s hs).symm
  have hsubT : Set.Ioc a b ⊆ Set.Icc 0 T := fun s hs => ⟨ha.trans hs.1.le, hs.2.trans hb⟩
  have hpt : ∀ s ∈ Set.Ioc a b, itoDrift T f Z bd Φc s ω =
      -(Real.sqrt N)⁻¹ * cylA R m T P X t φ G ω s + (1 / (2 * Real.sqrt N)) * cylJ R m T P X t φ G ω s :=
    fun s hs => S7PIF6_drift_pt R m hm T N hN P X ω t φ ht hφ G f bd Φc Z a b hfeq hfd hbform hΦform hs
      (hsubT hs) (hZ s (hsubT hs))
  have hIoc : IntegrableOn (fun r => (-(Real.sqrt N)⁻¹ * cylA R m T P X t φ G ω r +
        (1 / (2 * Real.sqrt N)) * cylJ R m T P X t φ G ω r)) (Set.Ioc a b) :=
    (hint.mono_set hsubT).congr_fun hpt measurableSet_Ioc
  refine ⟨hIoc, ?_⟩
  have hbT : b ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans hab, hb⟩
  have haT : a ∈ Set.Icc (0 : ℝ) T := ⟨ha, hab.trans hb⟩
  have e1 := hfor b hbT
  have e2 := hfor a haT
  rw [hfeq b ⟨hab, le_rfl⟩, hZ b hbT] at e1
  rw [hfeq a ⟨le_rfl, hab⟩, hZ a haT] at e2
  have hsplit : ∫ s in Set.Icc 0 b, itoDrift T f Z bd Φc s ω = (∫ s in Set.Icc 0 a, itoDrift T f Z bd Φc s ω) +
      ∫ s in Set.Ioc a b, itoDrift T f Z bd Φc s ω := by
    rw [← Set.Icc_union_Ioc_eq_Icc ha hab, setIntegral_union ?_ measurableSet_Ioc
      (hint.mono_set (Set.Icc_subset_Icc le_rfl (hab.trans hb)))
      (hint.mono_set hsubT)]
    exact Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'.1)
  have hcongr : ∫ s in Set.Ioc a b, itoDrift T f Z bd Φc s ω = ∫ s in Set.Ioc a b,
      (-(Real.sqrt N)⁻¹ * cylA R m T P X t φ G ω s + (1 / (2 * Real.sqrt N)) * cylJ R m T P X t φ G ω s) :=
    setIntegral_congr_fun measurableSet_Ioc hpt
  rw [e1, e2, hsplit, hcongr]
  linarith

/-- **F6 (Itô's formula on one interval between observation times)** (statement of
`HRS.MC.Sec7.PIPlan.s7_PIF_ito_piece`, copied verbatim). -/
theorem s7_PIF_ito_piece_proof {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i))
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 4 G) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hno : ∀ i, ¬ (a < t i ∧ t i < b)) :
    ∃ Mart : Ω → ℝ, Integrable Mart P ∧ ∫ ω, Mart ω ∂P = 0 ∧ ∀ᵐ ω ∂P,
      gaussHeat (obsCov R.D R.ρ t φ) G b (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) b)) -
        gaussHeat (obsCov R.D R.ρ t φ) G a (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) a)) =
      (∫ r in Set.Ioc a b, (-(Real.sqrt N)⁻¹ * cylA R m T P X t φ G ω r +
        (1 / (2 * Real.sqrt N)) * cylJ R m T P X t φ G ω r)) + Mart ω := by
  obtain ⟨Mart, h1, h2, h3⟩ := S7PIF6_piece_aux R m hm T hT N hN P X₀ W X hreal hF t φ ht hφ G hG a b ha hab hb hno
  exact ⟨Mart, h1, h2, h3.mono fun ω hω => hω.2⟩

end Prob

end HRS.MC.Sec7.S7PIF6

end
