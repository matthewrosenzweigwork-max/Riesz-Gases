import HRS.Uniform.Q54cAux39

/-!
# Q54c, part 40: lifting a Hilbert martingale to a product with an independent factor
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

open HRS

section ProdLift

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
  {ℱ₁ : Filtration ℝ m₁}

theorem martingale_fst' (ℱ₂ : Filtration ℝ m₂) {F : ℝ → Ω₁ → ℝ} (hF : Martingale F ℱ₁ P₁) :
    Martingale (fun t (p : Ω₁ × Ω₂) => F t p.1) (prodFiltration P₁ P₂ ℱ₁ ℱ₂) (P₁.prod P₂) := by
  have := martingale_mul_prod (P₁ := P₁) (P₂ := P₂) ℱ₁ ℱ₂ hF (martingale_const ℱ₂ P₂ (1 : ℝ))
  convert this using 2 with t p
  simp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {N : ℝ → Ω₁ → H} {Sg : ℝ → Ω₁ → (H →L[ℝ] H →L[ℝ] ℝ)} {t : ℝ}

theorem _root_.HRS.IsHilbertMartingaleWithCovariation.comp_fst' (ℱ₂ : Filtration ℝ m₂)
    (hM : IsHilbertMartingaleWithCovariation P₁ ℱ₁ t N Sg) :
    IsHilbertMartingaleWithCovariation (P₁.prod P₂) (prodFiltration P₁ P₂ ℱ₁ ℱ₂) t
      (fun τ p => N τ p.1) (fun r p => Sg r p.1) := by
  have hπp : MeasurePreserving (Prod.fst : Ω₁ × Ω₂ → Ω₁) (P₁.prod P₂) P₁ := measurePreserving_fst
  have hπm : ∀ s, Measurable[prodFiltration P₁ P₂ ℱ₁ ℱ₂ s, ℱ₁ s]
      (Prod.fst : Ω₁ × Ω₂ → Ω₁) := fun s =>
    Measurable.of_comap_le (le_sup_of_le_left le_sup_left)
  refine ⟨fun x => martingale_fst' ℱ₂ (F := fun τ ω => inner ℝ (N τ ω) x) (hM.martingale x),
    hπp.quasiMeasurePreserving.ae hM.zero, hπp.quasiMeasurePreserving.ae hM.cont,
    fun τ hτ => (hM.sq_int τ hτ).comp_measurePreserving hπp, fun x y => ?_, fun σ x y => ?_,
    hπp.quasiMeasurePreserving.ae hM.sigma_traceClass, ?_,
    hπp.quasiMeasurePreserving.ae hM.sigma_pathint,
    hπp.quasiMeasurePreserving.ae hM.sigma_entry_int, fun x y => ?_⟩
  · exact (hM.sigma_meas x y).comp (measurable_fst.prodMk (measurable_snd.fst))
  · exact (hM.sigma_adapted σ x y).comp (hπm σ)
  · exact hπp.integrable_comp_of_integrable (g := fun ω => ∫ σ in Set.Icc 0 t, traceNormForm (Sg σ ω))
      hM.sigma_int
  · exact martingale_fst' ℱ₂
      (F := fun τ ω => inner ℝ (N τ ω) x * inner ℝ (N τ ω) y - ∫ σ in Set.Icc 0 τ, Sg σ ω x y)
      (hM.covariation x y)

end ProdLift

end HRS.Uniform.Q54c
