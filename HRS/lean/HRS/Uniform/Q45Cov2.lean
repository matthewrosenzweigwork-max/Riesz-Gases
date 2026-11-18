import HRS.Uniform.Q45Cov1

/-!
# Q45 (Lemma 3.20): covariance of increments over the same interval
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

lemma integral_Icc_split {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : IntegrableOn f (Set.Icc 0 b)) :
    ∫ σ in Set.Icc 0 b, f σ = (∫ σ in Set.Icc 0 a, f σ) + ∫ σ in Set.Icc a b, f σ := by
  have hi0a : IntegrableOn f (Set.Icc 0 a) := hf.mono_set (Set.Icc_subset_Icc_right hab)
  have hiab : IntegrableOn f (Set.Ioc a b) := hf.mono_set (fun σ hσ => ⟨ha.trans hσ.1.le, hσ.2⟩)
  have hdisj : Disjoint (Set.Icc 0 a) (Set.Ioc a b) := by
    rw [Set.disjoint_left]
    intro σ h1 h2
    exact absurd h1.2 (not_le.2 h2.1)
  have := setIntegral_union hdisj measurableSet_Ioc hi0a hiab
  rw [Set.Icc_union_Ioc_eq_Icc ha hab] at this
  have e2 : ∫ σ in Set.Icc a b, f σ = ∫ σ in Set.Ioc a b, f σ := integral_Icc_eq_integral_Ioc
  rw [this, e2]

section Same

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {T : ℝ} {M : ℝ → Ω → H} {Dd : ℝ → H →L[ℝ] H →L[ℝ] ℝ}

lemma HM_entry_integrable (hM : IsHilbertMartingaleWithCovariation P ℱ T M (fun r _ => Dd r))
    (x y : H) : IntegrableOn (fun σ => Dd σ x y) (Set.Icc 0 T) MeasureTheory.volume := by
  obtain ⟨ω, hω⟩ := hM.sigma_entry_int.exists
  exact hω x y

/-- Covariance of the increments over the same interval. -/
lemma HM_incr_same (hM : IsHilbertMartingaleWithCovariation P ℱ T M (fun r _ => Dd r))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) (x y : H) :
    ∫ ω, (inner ℝ (M b ω) x - inner ℝ (M a ω) x) * (inner ℝ (M b ω) y - inner ℝ (M a ω) y) ∂P =
      ∫ σ in Set.Icc a b, Dd σ x y := by
  have hbm : b ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans hab, hbT⟩
  have ham : a ∈ Set.Icc (0 : ℝ) T := ⟨ha, hab.trans hbT⟩
  set Xb : Ω → ℝ := fun ω => inner ℝ (M b ω) x with hXb
  set Xa : Ω → ℝ := fun ω => inner ℝ (M a ω) x with hXa
  set Yb : Ω → ℝ := fun ω => inner ℝ (M b ω) y with hYb
  set Ya : Ω → ℝ := fun ω => inner ℝ (M a ω) y with hYa
  have mXb : MemLp Xb 2 P := HM_memLp hM hbm x
  have mXa : MemLp Xa 2 P := HM_memLp hM ham x
  have mYb : MemLp Yb 2 P := HM_memLp hM hbm y
  have mYa : MemLp Ya 2 P := HM_memLp hM ham y
  have iXbYb : Integrable (fun ω => Xb ω * Yb ω) P := mXb.integrable_mul mYb
  have iXaYa : Integrable (fun ω => Xa ω * Ya ω) P := mXa.integrable_mul mYa
  have o1 : ∫ ω, Xa ω * (Yb ω - Ya ω) ∂P = 0 :=
    martingale_orth (hM.martingale y) hab (HM_adapted hM x a) mXa mYb mYa
  have o2 : ∫ ω, Ya ω * (Xb ω - Xa ω) ∂P = 0 :=
    martingale_orth (hM.martingale x) hab (HM_adapted hM y a) mYa mXb mXa
  have e1 : ∀ ω, (Xb ω - Xa ω) * (Yb ω - Ya ω) =
      Xb ω * Yb ω - Xa ω * Ya ω - Xa ω * (Yb ω - Ya ω) - Ya ω * (Xb ω - Xa ω) := by
    intro ω; ring
  have iXaYb : Integrable (fun ω => Xa ω * Yb ω) P := mXa.integrable_mul mYb
  have iYaXb : Integrable (fun ω => Ya ω * Xb ω) P := mYa.integrable_mul mXb
  have iYaXa : Integrable (fun ω => Ya ω * Xa ω) P := mYa.integrable_mul mXa
  have iA : Integrable (fun ω => Xa ω * (Yb ω - Ya ω)) P := by
    have e : (fun ω => Xa ω * (Yb ω - Ya ω)) = fun ω => Xa ω * Yb ω - Xa ω * Ya ω := by
      funext ω; ring
    rw [e]; exact iXaYb.sub iXaYa
  have iB : Integrable (fun ω => Ya ω * (Xb ω - Xa ω)) P := by
    have e : (fun ω => Ya ω * (Xb ω - Xa ω)) = fun ω => Ya ω * Xb ω - Ya ω * Xa ω := by
      funext ω; ring
    rw [e]; exact iYaXb.sub iYaXa
  have i12 : Integrable (fun ω => Xb ω * Yb ω - Xa ω * Ya ω) P := iXbYb.sub iXaYa
  have i123 : Integrable
      (fun ω => Xb ω * Yb ω - Xa ω * Ya ω - Xa ω * (Yb ω - Ya ω)) P := i12.sub iA
  have h1 : ∫ ω, (Xb ω - Xa ω) * (Yb ω - Ya ω) ∂P =
      ∫ ω, Xb ω * Yb ω ∂P - ∫ ω, Xa ω * Ya ω ∂P := by
    simp_rw [e1]
    rw [integral_sub i123 iB, integral_sub i12 iA, integral_sub iXbYb iXaYa, o1, o2]
    ring
  -- covariation martingale
  have hN := (hM.covariation x y).setIntegral_eq hab (MeasurableSet.univ)
  simp only [Measure.restrict_univ] at hN
  have hcb : Integrable (fun ω => ∫ σ in Set.Icc 0 b, Dd σ x y) P := integrable_const _
  have hca : Integrable (fun ω => ∫ σ in Set.Icc 0 a, Dd σ x y) P := integrable_const _
  rw [integral_sub iXaYa hca, integral_sub iXbYb hcb] at hN
  simp only [integral_const, probReal_univ, one_smul] at hN
  -- integrals over intervals
  have hint : IntegrableOn (fun σ => Dd σ x y) (Set.Icc 0 T) MeasureTheory.volume :=
    HM_entry_integrable hM x y
  have hi0b : IntegrableOn (fun σ => Dd σ x y) (Set.Icc 0 b) :=
    hint.mono_set (Set.Icc_subset_Icc_right hbT)
  have hsplit := integral_Icc_split (f := fun σ => Dd σ x y) ha hab hi0b
  beta_reduce at hsplit
  rw [h1]
  rw [hsplit] at hN
  linarith

end Same

end HRS.Uniform.Q45
