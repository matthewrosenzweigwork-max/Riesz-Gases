import HRS.Commutator.Torus.TLOWVAux7

/-!
# T-INHOM helpers, part 1: convolutions, the adjoint identity and the pairing identity
`𝒞_F(v,f) = 2 ∑_i ∫ f v_i (F_i * f)` for an odd kernel `F`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tinhom_conv_meas {K g : Torus d → ℝ} (hK : Measurable K) (hg : Measurable g) :
    Measurable (textConv K g) := by
  have h : StronglyMeasurable (fun q : Torus d × Torus d => K (q.1 - q.2) * g q.2) :=
    ((hK.comp (measurable_fst.sub measurable_snd)).mul (hg.comp measurable_snd)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := volume)).measurable

lemma tinhom_conv_bdd {K g : Torus d → ℝ} (hK : Integrable K) {M : ℝ} (hM : ∀ y, |g y| ≤ M)
    (x : Torus d) : |textConv K g x| ≤ (∫ z, |K z|) * M := by
  unfold textConv
  rw [← Real.norm_eq_abs]
  have hK' : Integrable (fun y => K (x - y)) := hK.comp_sub_left x
  calc ‖∫ y, K (x - y) * g y‖ ≤ ∫ y, |K (x - y)| * M := by
        refine norm_integral_le_of_norm_le (hK'.norm.mul_const M) (ae_of_all _ fun y => ?_)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hM y) (abs_nonneg _)
    _ = (∫ z, |K z|) * M := by
        rw [integral_mul_const, integral_sub_left_eq_self (fun z => |K z|) volume x]

lemma tinhom_int_prod3 {K f g : Torus d → ℝ} (hK : Integrable K) (hf : Measurable f) (hg : Measurable g)
    {Mf Mg : ℝ} (hMf : ∀ x, |f x| ≤ Mf) (hMg : ∀ x, |g x| ≤ Mg) :
    Integrable (fun p : Torus d × Torus d => K (p.1 - p.2) * f p.1 * g p.2) (volume.prod volume) := by
  have hgi : Integrable g := ten_integrable_of_bdd (μ := volume) hg Mg (fun x => by
    rw [Real.norm_eq_abs]; exact hMg x)
  have h1 := text_integrable_prod hK hgi
  have h2 := h1.bdd_mul (c := Mf) ((hf.comp measurable_fst).aestronglyMeasurable)
    (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hMf p.1)
  refine h2.congr (ae_of_all _ fun p => ?_)
  show f p.1 * (K (p.1 - p.2) * g p.2) = K (p.1 - p.2) * f p.1 * g p.2
  ring

/-- Adjoint identity for an odd `L¹` kernel. -/
lemma tinhom_adjoint {K f g : Torus d → ℝ} (hK : Integrable K) (hodd : ∀ z, K (-z) = -K z)
    (hf : Measurable f) (hg : Measurable g) {Mf Mg : ℝ} (hMf : ∀ x, |f x| ≤ Mf) (hMg : ∀ x, |g x| ≤ Mg) :
    ∫ x, f x * textConv K g x = -∫ x, g x * textConv K f x := by
  have hJ := tinhom_int_prod3 hK hf hg hMf hMg
  have hH := tinhom_int_prod3 hK hg hf hMg hMf
  have e1 : ∫ x, f x * textConv K g x =
      ∫ p : Torus d × Torus d, K (p.1 - p.2) * f p.1 * g p.2 ∂(volume.prod volume) := by
    rw [integral_prod _ hJ]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show f x * textConv K g x = ∫ y, K (x - y) * f x * g y
    unfold textConv
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  have e2 : ∫ x, g x * textConv K f x =
      ∫ p : Torus d × Torus d, K (p.1 - p.2) * g p.1 * f p.2 ∂(volume.prod volume) := by
    rw [integral_prod _ hH]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show g x * textConv K f x = ∫ y, K (x - y) * g x * f y
    unfold textConv
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  have e3 := integral_prod_swap (μ := (volume : Measure (Torus d))) (ν := (volume : Measure (Torus d)))
    (fun p : Torus d × Torus d => K (p.1 - p.2) * g p.1 * f p.2)
  have e4 : ∫ z : Torus d × Torus d, K (z.swap.1 - z.swap.2) * g z.swap.1 * f z.swap.2
      ∂(volume.prod volume) = -∫ p : Torus d × Torus d, K (p.1 - p.2) * f p.1 * g p.2
        ∂(volume.prod volume) := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [Prod.fst_swap, Prod.snd_swap]
    have : K (p.2 - p.1) = -K (p.1 - p.2) := by
      rw [← hodd, neg_sub]
    rw [this]; ring
  rw [e1, e2, ← e3, e4]
  ring

lemma tinhom_commKernel_sum (F V : Torus d → Euc d) (x y : Torus d) :
    commKernel F V x y = ∑ i, (V x i - V y i) * F (x - y) i := by
  unfold commKernel
  split_ifs with h
  · subst h; simp
  · rw [tlowv_inner_eq]
    exact Finset.sum_congr rfl fun i _ => by simp [PiLp.sub_apply]

/-- The pairing identity `𝒞_F(V,f) = 2 ∑_i ∫ f V_i (F_i * f)`. -/
theorem tinhom_pairing {F V : Torus d → Euc d} {f : Torus d → ℝ} {L : ℝ}
    (hFm : Measurable F) (hodd : ∀ z, F (-z) = -F z) (hW : Integrable (tlowvW F))
    (hFi : ∀ i, Integrable (fun x => F x i)) (hL : 0 ≤ L) (hV : IsLipschitzVF L V)
    (hVc : Continuous V) (hfc : Continuous f) :
    CcommFunT F V f = 2 * ∑ i, ∫ x, f x * (V x i * textConv (fun z => F z i) f x) := by
  obtain ⟨Bf, hBf⟩ := ten_bound_of_continuous hfc
  have hBf' : ∀ x, |f x| ≤ Bf := fun x => by simpa using hBf x
  have hVic : ∀ i : Fin d, Continuous fun x => V x i := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hVc
  have hVb : ∀ i : Fin d, ∃ B, ∀ x, |V x i| ≤ B := fun i => by
    obtain ⟨B, hB⟩ := ten_bound_of_continuous (hVic i)
    exact ⟨B, fun x => by simpa using hB x⟩
  have hFim : ∀ i : Fin d, Measurable fun z : Torus d => F z i := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).measurable.comp hFm
  have hFodd : ∀ i : Fin d, ∀ z, F (-z) i = -F z i := fun i z => by rw [hodd]; simp
  have ha2 : Integrable (fun x => f x ^ 2) := (HRS.PDE.R2Aux.memLp_of_continuous_real hfc).integrable_sq
  have hform := (tlowv_L2_form hFm hodd hW hL hV hVc hfc.aestronglyMeasurable hfc.aestronglyMeasurable
    ha2 ha2 one_pos).1
  have hcv_b : ∀ i (g : Torus d → ℝ), Measurable g → ∀ {M : ℝ}, (∀ y, |g y| ≤ M) →
      ∃ B, ∀ x, |textConv (fun z => F z i) g x| ≤ B := fun i g hg M hM =>
    ⟨(∫ z, |F z i|) * M, fun x => tinhom_conv_bdd (hFi i) hM x⟩
  -- the inner integrals
  have hinner : ∀ x : Torus d, ∫ y, commKernel F V x y * f x * f y =
      ∑ i, (f x * (V x i * textConv (fun z => F z i) f x) -
        f x * textConv (fun z => F z i) (fun y => V y i * f y) x) := by
    intro x
    have hpt : ∀ y, commKernel F V x y * f x * f y =
        ∑ i, (f x * V x i * (F (x - y) i * f y) - f x * (F (x - y) i * (V y i * f y))) := by
      intro y
      rw [tinhom_commKernel_sum, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [hpt]
    have hA : ∀ i, Integrable (fun y => f x * V x i * (F (x - y) i * f y)) := fun i => by
      have h1 : Integrable (fun y => F (x - y) i * f y) := by
        have := ((hFi i).comp_sub_left x).bdd_mul (c := Bf) hfc.aestronglyMeasurable
          (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hBf' y)
        exact this.congr (ae_of_all _ fun y => by simp [mul_comm])
      exact h1.const_mul _
    have hB : ∀ i, Integrable (fun y => f x * (F (x - y) i * (V y i * f y))) := fun i => by
      obtain ⟨BV, hBV⟩ := hVb i
      have hgc : Continuous fun y => V y i * f y := (hVic i).mul hfc
      have h1 : Integrable (fun y => F (x - y) i * (V y i * f y)) := by
        have := ((hFi i).comp_sub_left x).bdd_mul (c := BV * Bf)
          hgc.aestronglyMeasurable
          (ae_of_all _ fun y => by
            show ‖V y i * f y‖ ≤ BV * Bf
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul (hBV y) (hBf' y) (abs_nonneg _) ((abs_nonneg _).trans (hBV y)))
        exact this.congr (ae_of_all _ fun y => by simp [mul_comm])
      exact h1.const_mul _
    have hAB : ∀ i, Integrable (fun y => f x * V x i * (F (x - y) i * f y) -
        f x * (F (x - y) i * (V y i * f y))) := fun i => (hA i).sub (hB i)
    rw [integral_finset_sum _ (fun i _ => hAB i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_sub (hA i) (hB i), integral_const_mul, integral_const_mul]
    unfold textConv
    rw [mul_assoc]
  unfold CcommFunT
  simp_rw [hinner]
  -- the outer integrals
  have hmeas_cv : ∀ i (g : Torus d → ℝ), Measurable g → Measurable (textConv (fun z => F z i) g) :=
    fun i g hg => tinhom_conv_meas (hFim i) hg
  have hAi : ∀ i, Integrable (fun x => f x * (V x i * textConv (fun z => F z i) f x)) := fun i => by
    obtain ⟨BV, hBV⟩ := hVb i
    obtain ⟨Bc, hBc⟩ := hcv_b i f hfc.measurable hBf'
    refine ten_integrable_of_bdd (μ := volume)
      (hfc.measurable.mul ((hVic i).measurable.mul (hmeas_cv i f hfc.measurable)))
      (Bf * (BV * Bc)) (fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (hBf' x) (mul_le_mul (hBV x) (hBc x) (abs_nonneg _) ((abs_nonneg _).trans (hBV x)))
      (by positivity) ((abs_nonneg _).trans (hBf' x))
  have hBi : ∀ i, Integrable (fun x => f x * textConv (fun z => F z i) (fun y => V y i * f y) x) :=
    fun i => by
    obtain ⟨BV, hBV⟩ := hVb i
    have hg : Measurable fun y => V y i * f y := (hVic i).measurable.mul hfc.measurable
    obtain ⟨Bc, hBc⟩ := hcv_b i (fun y => V y i * f y) hg (M := BV * Bf) (fun y => by
      rw [abs_mul]; exact mul_le_mul (hBV y) (hBf' y) (abs_nonneg _) ((abs_nonneg _).trans (hBV y)))
    refine ten_integrable_of_bdd (μ := volume) (hfc.measurable.mul (hmeas_cv i _ hg)) (Bf * Bc)
      (fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hBf' x) (hBc x) (abs_nonneg _) ((abs_nonneg _).trans (hBf' x))
  have hABi : ∀ i, Integrable (fun x => f x * (V x i * textConv (fun z => F z i) f x) -
      f x * textConv (fun z => F z i) (fun y => V y i * f y) x) := fun i => (hAi i).sub (hBi i)
  rw [integral_finset_sum _ (fun i _ => hABi i)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_sub (hAi i) (hBi i)]
  obtain ⟨BV, hBV⟩ := hVb i
  have hg : Measurable fun y => V y i * f y := (hVic i).measurable.mul hfc.measurable
  have hadj := tinhom_adjoint (hFi i) (hFodd i) hfc.measurable hg hBf'
    (g := fun y => V y i * f y) (Mg := BV * Bf) (fun y => by
      rw [abs_mul]; exact mul_le_mul (hBV y) (hBf' y) (abs_nonneg _) ((abs_nonneg _).trans (hBV y)))
  have hadj' : ∫ x, f x * textConv (fun z => F z i) (fun y => V y i * f y) x =
      -∫ x, f x * (V x i * textConv (fun z => F z i) f x) := by
    rw [hadj]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    ring
  rw [hadj']
  ring

end HRS.Commutator.TorusNote
