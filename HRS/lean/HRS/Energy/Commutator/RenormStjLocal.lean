import HRS.Energy.Commutator.RenormStjTerm

/-!
# Route S, packet STJ: the local field energy, `l`-integrated
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

variable {d : ℕ}

theorem measurable_tdist_to (a : Torus d) : Measurable fun x : Torus d => KernelGrad.tdist x a := by
  have h := EnergyAux.measurable_tdist_zero (d := d)
  have e1 : (fun x : Torus d => KernelGrad.tdist x a) = fun x => KernelGrad.tdist (x - a) 0 := by
    funext x; exact EnergyAux.tdist_def x a
  rw [e1]; exact h.comp (measurable_id.sub_const _)

theorem measurable_Wloc {N : ℕ} (X : Fin N → Torus d) (μ : Measure (Torus d)) [IsFiniteMeasure μ]
    (i : Fin N) (r : ℝ) :
    Measurable fun l : ℝ => ∫⁻ x : Torus d,
      (if KernelGrad.tdist x (X i) < r then ENNReal.ofReal (‖fieldF l X μ i x‖ ^ 2) else 0) := by
  have hK : Measurable fun p : ℝ × Torus d =>
      (if KernelGrad.tdist p.2 (X i) < r then ENNReal.ofReal (‖fieldF p.1 X μ i p.2‖ ^ 2) else 0) := by
    refine Measurable.ite ?_ ((measurable_fieldF_uncurry X μ i).norm.pow_const 2).ennreal_ofReal measurable_const
    exact measurableSet_lt ((measurable_tdist_to (X i)).comp measurable_snd) measurable_const
  exact hK.lintegral_prod_right' (ν := (volume : Measure (Torus d)))

theorem sumY_le (hd : 1 ≤ d) (s : ℝ) {N : ℕ} (hN : N ≠ 0) {X : Config d N} {r : Fin N → ℝ}
    (hr0 : ∀ i, 0 < r i) (hr8 : ∀ i, r i ≤ 1 / 8)
    (hsep : ∀ i j, i ≠ j → r i + r j < KernelGrad.tdist (X i) (X j))
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d))) (hμ1 : μ Set.univ = 1) :
    ∑ i, Yloc d s (r i) (X i) (fun l => fieldF l X μ i) ≤
      ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
        ENNReal.ofReal (2 * Ebar d X (fun i => r i / 4) μ Λ l + 2 * Ubar d (fun i => r i / 4) Λ l) := by
  set η0 : Fin N → ℝ := fun i => r i / 4 with hη0def
  have hη0 : ∀ i, 0 < η0 i ∧ η0 i ≤ 1 / 8 := fun i => ⟨by have := hr0 i; simp only [hη0def]; positivity,
    by have := hr8 i; simp only [hη0def]; linarith⟩
  have hη02 : ∀ i, 0 < η0 i ∧ η0 i < 1 / 2 := fun i => ⟨(hη0 i).1, by linarith [(hη0 i).2]⟩
  have hdisj0 : ∀ i j, i ≠ j → η0 i + η0 j < KernelGrad.tdist (X i) (X j) := fun i j hij => by
    have := hsep i j hij; have := hr0 i; have := hr0 j; simp only [hη0def]; linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hc : ENNReal.ofReal Λ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeas : ∀ i, Measurable fun l : ℝ => ENNReal.ofReal (l ^ (-bexp d s)) * ∫⁻ x : Torus d,
      (if KernelGrad.tdist x (X i) < r i then ENNReal.ofReal (‖fieldF l X μ i x‖ ^ 2) else 0) := fun i =>
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul (measurable_Wloc X μ i (r i))
  -- the pointwise bound in `l`
  have hpt : ∀ l : ℝ, 0 < l → ∑ i, ∫⁻ x : Torus d,
      (if KernelGrad.tdist x (X i) < r i then ENNReal.ofReal (‖fieldF l X μ i x‖ ^ 2) else 0) ≤
      ENNReal.ofReal (2 * Ebar d X η0 μ Λ l + 2 * Ubar d η0 Λ l) := by
    intro l hl
    have hS := sliceCharges_stj hd hl hη02 hdisj0
    obtain ⟨hint, hsum⟩ := local_field_energy hd hN hl.le hS (r := r)
      (fun i => by simp only [hη0def]; linarith [hr0 i]) hsep hc hμ hμ1
    have h1 : ∀ i, ∫⁻ x : Torus d,
        (if KernelGrad.tdist x (X i) < r i then ENNReal.ofReal (‖fieldF l X μ i x‖ ^ 2) else 0) =
        ENNReal.ofReal (∫ x : Torus d, (if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0)) := by
      intro i
      rw [ofReal_integral_eq_lintegral_ofReal (hint i)]
      · refine lintegral_congr fun x => ?_
        by_cases hx : KernelGrad.tdist x (X i) < r i
        · simp only [if_pos hx]
        · simp only [if_neg hx, ENNReal.ofReal_zero]
      · exact Filter.Eventually.of_forall fun x => by dsimp only; split_ifs <;> positivity
    simp_rw [h1]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg fun x => by dsimp only; split_ifs <;> positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    refine hsum.trans ?_
    have hE := energy_le_Ebar hd hN hl hη0 hdisj0 hΛ0 hμ hμ1
    have hq : ∀ i, quadForm (fun x y => sliceGfull d l (x - y)) (chS d l (η0 i) (X i))
        (ENNReal.ofReal ((chS d l (η0 i) (X i)).real Set.univ) • (volume : Measure (Torus d))) = Self d l (η0 i) :=
      fun i => quadForm_chS_eq hd hl (hη02 i).1 (hη02 i).2 (X i)
    simp_rw [hq]
    have h2 : ∑ i, Self d l (η0 i) ≤
        ∑ i, ((∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d (η0 i))).toReal + Fint d l (η0 i)) :=
      Finset.sum_le_sum fun i _ => Self_le_dom hd hl (hη0 i).1 (hη0 i).2
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * (1 / (N : ℝ)) ^ 2)
    have h4 : 0 ≤ (2 * Λ / N) * ∑ i, Fint d l (η0 i) :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Fint_nonneg d l (η0 i))
    unfold Ebar Ubar
    unfold Ebar Ubar at hE
    nlinarith [h3, h4, hE]
  calc ∑ i, ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ∫⁻ x : Torus d,
        (if KernelGrad.tdist x (X i) < r i then ENNReal.ofReal (‖fieldF l X μ i x‖ ^ 2) else 0)
      = ∫⁻ l in Ioi (0 : ℝ), ∑ i, ENNReal.ofReal (l ^ (-bexp d s)) * ∫⁻ x : Torus d,
        (if KernelGrad.tdist x (X i) < r i then ENNReal.ofReal (‖fieldF l X μ i x‖ ^ 2) else 0) :=
        (lintegral_finset_sum _ (fun i _ => hmeas i)).symm
    _ ≤ _ := by
        refine setLIntegral_mono' measurableSet_Ioi fun l hl => ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul' le_rfl (hpt l hl)

end HRS.Commutator.Stj
