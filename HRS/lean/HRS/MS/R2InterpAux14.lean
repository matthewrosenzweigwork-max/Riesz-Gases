import HRS.MS.R2InterpAux13
import HRS.MC.S7PIF6Mart

/-!
# S10.2 (worker S102), part 14 (packet F6, abstract core): Itô's formula on one interval with a bounded martingale integrand

Abstract version of the torus `S7PIF6_piece_aux`: for an `ℝ^q`-valued Itô process `Z = X₀ + ∫ b + ∫ Φ dW'` of a Brownian filtration, a
`C^{1,2}` function `f` and a bound `B` for the integrand `D_xf(s,Z_s)[Φ_s^k]` on `(a,b]`, there is an integrable centred `Mart` with
`f(b,Z_b) - f(a,Z_a) = ∫_{(a,b]} itoDrift + Mart` a.s., the drift being integrable on `[0,T]`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.MC.Sec7.S7PIF6

theorem s102_ito_piece_abs {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type} [Fintype ι] {q : ℕ} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → ι → ℝ}
    (hW : IsBrownianFiltration P ℱ W') {T : ℝ} (hT : 0 ≤ T)
    (f : ℝ → EuclideanSpace ℝ (Fin q) → ℝ) (hf : IsC12On T Set.univ f)
    (X0f : Ω → EuclideanSpace ℝ (Fin q)) (hX0 : ∀ t : ℝ, Measurable[ℱ t] X0f)
    (bd : ℝ → Ω → EuclideanSpace ℝ (Fin q)) (hbd : IsProgressiveLocL1 P ℱ bd)
    (Φc : ℝ → Ω → ι → EuclideanSpace ℝ (Fin q)) (hΦ : IsProgressiveLocL2E P ℱ Φc)
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hbound : ∀ s ∈ Set.Ioc a b, ∀ ω k,
      |fderiv ℝ (f s) (itoProcess P ℱ W' X0f bd Φc s ω) (Φc s ω k)| ≤ B) :
    ∃ Mart : Ω → ℝ, Integrable Mart P ∧ ∫ ω, Mart ω ∂P = 0 ∧ ∀ᵐ ω ∂P,
      IntegrableOn (fun s => itoDrift T f (itoProcess P ℱ W' X0f bd Φc) bd Φc s ω) (Set.Icc 0 T) ∧
      f b (itoProcess P ℱ W' X0f bd Φc b ω) - f a (itoProcess P ℱ W' X0f bd Φc a ω) =
        (∫ s in Set.Ioc a b, itoDrift T f (itoProcess P ℱ W' X0f bd Φc) bd Φc s ω) + Mart ω := by
  classical
  set Z : ℝ → Ω → EuclideanSpace ℝ (Fin q) := itoProcess P ℱ W' X0f bd Φc with hZdef
  have hito : ∀ᵐ ω ∂P, IntegrableOn (fun s => itoDrift T f Z bd Φc s ω) (Set.Icc 0 T) ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T, f τ (Z τ ω) = f 0 (X0f ω) +
        (∫ s in Set.Icc 0 τ, itoDrift T f Z bd Φc s ω) +
        localItoIntegral P ℱ W' (itoIntegrand T Set.univ f Z Φc) τ ω :=
    ito_formula hW hT f hf X0f hX0 bd hbd Φc hΦ
  have hZprog : IsProgressive ℱ Z := isProgressive_itoProcess X0f hX0 bd hbd.prog Φc
  have hZc : ∀ᵐ ω ∂P, Continuous fun τ => Z τ ω := continuous_itoProcess X0f bd hbd Φc (P := P) (W := W')
  have hΨ : IsProgressiveLocL2 P ℱ (itoIntegrand T Set.univ f Z Φc) :=
    isProgressiveLocL2_itoIntegrand Set.univ isClosed_univ Set.univ (Set.Subset.refl _) f hf Z
      hZprog hZc Φc hΦ
  have hbound' : ∀ s ∈ Set.Ioc a b, ∀ ω k, |itoIntegrand T Set.univ f Z Φc s ω k| ≤ B := by
    intro s hs ω k
    have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans hs.1.le, hs.2.trans hb⟩
    have : itoIntegrand T Set.univ f Z Φc s ω k = fderiv ℝ (f s) (Z s ω) (Φc s ω k) := by
      simp [itoIntegrand, hsT]
    rw [this]
    exact hbound s hs ω k
  obtain ⟨Mart, hMi, hM0, hMeq⟩ := S7PIF6_mart_incr hW hΨ hab hbound'
  refine ⟨Mart, hMi, hM0, ?_⟩
  filter_upwards [hito, hMeq] with ω hit hMω
  obtain ⟨hint, hfor⟩ := hit
  refine ⟨hint, ?_⟩
  have hsubT : Set.Ioc a b ⊆ Set.Icc 0 T := fun s hs => ⟨ha.trans hs.1.le, hs.2.trans hb⟩
  have hbT : b ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans hab, hb⟩
  have haT : a ∈ Set.Icc (0 : ℝ) T := ⟨ha, hab.trans hb⟩
  have e1 := hfor b hbT
  have e2 := hfor a haT
  have hsplit : ∫ s in Set.Icc 0 b, itoDrift T f Z bd Φc s ω = (∫ s in Set.Icc 0 a, itoDrift T f Z bd Φc s ω) +
      ∫ s in Set.Ioc a b, itoDrift T f Z bd Φc s ω := by
    rw [← Set.Icc_union_Ioc_eq_Icc ha hab, setIntegral_union ?_ measurableSet_Ioc
      (hint.mono_set (Set.Icc_subset_Icc le_rfl (hab.trans hb)))
      (hint.mono_set hsubT)]
    exact Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'.1)
  rw [e1, e2, hsplit]
  linarith

end HRS.MS.R2Interp

end
