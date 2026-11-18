import HRS.PDE.MeanFieldAprioriClassicalOn
import HRS.PDE.MeanFieldAprioriPhi
import HRS.PDE.MeanFieldAprioriSubord

/-!
# A priori bounds for the finite-regularity mean-field equation, packet AP3
(positivity on finite intervals; package MF-01, plan `MeanFieldAprioriPlan.md`, amended by
`MeanFieldAprioriAmendment.md` §2.5)

Both main theorems are stated for a real solution on `[0,T]` (`MFSolRealOn … T`).

* `lower_bound_of_laplacian_ge`: if `ΔW ≥ -G` on `[0,T]`, then `ρ^t ≥ m₀ e^{-Gt}`;
  Step A (`lower_bound_of_pos_on`, conditional on `ρ ≥ η > 0` on `[0,T']`): the functional
  `Y_p(t) = ∫ ρ^{-p}` satisfies `Y_p' ≤ (p+1) G Y_p`, Gronwall, and `abs_le_of_integral_pow_le`
  for `p → ∞`; Step B: continuation (`sSup` argument).
* `exists_pos_on_Icc`: positivity on every compact interval (no uniformity), from the first.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFApriori

variable {d : ℕ}
open Aux

/-! ### Section 1: an integration by parts on the torus -/

theorem integral_deriv_comp_grad_mul (Φ : ℝ → ℝ) (I : Set ℝ) (hI : IsOpen I)
    (hΦ : ContDiffOn ℝ 1 Φ I) (u W : Torus d → ℝ) (hu : Torus.IsCk 1 u) (hW : Torus.IsCk 2 W)
    (hrange : ∀ x, u x ∈ I) :
    ∫ x, deriv Φ (u x) * inner ℝ (Torus.grad u x) (Torus.grad W x) =
      -∫ x, Φ (u x) * Torus.laplacian W x := by
  have hW1 : Torus.IsCk 1 W := hW.of_le (by norm_num)
  have hpW1 : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j W) := fun j => isCk_one_partialDeriv j _ hW
  have hA : Torus.IsCk 1 (fun x => Φ (u x)) := isCk_comp Φ I hΦ u hu hrange
  have hdA : ∀ j x, Torus.partialDeriv j (fun y => Φ (u y)) x =
      deriv Φ (u x) * Torus.partialDeriv j u x := fun j x =>
    partialDeriv_comp j Φ I hI hΦ u hu hrange x
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlap : ∀ x, Torus.laplacian W x =
      ∑ j, Torus.partialDeriv j (Torus.partialDeriv j W) x := fun x => laplacian_eq_sum _ hW x
  have hΦc : Continuous fun x => Φ (u x) :=
    hΦ.continuousOn.comp_continuous (continuous_of_isCk' hu le_rfl) hrange
  have e1 : ∀ x, deriv Φ (u x) * inner ℝ (Torus.grad u x) (Torus.grad W x) =
      ∑ j, Torus.partialDeriv j (fun y => Φ (u y)) x * Torus.partialDeriv j W x := by
    intro x
    rw [inner_grad_grad, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hdA j x]; ring
  simp_rw [e1]
  rw [integral_finsetSum (μ := volume) (f := fun (j : Fin d) (x : Torus d) =>
      Torus.partialDeriv j (fun y => Φ (u y)) x * Torus.partialDeriv j W x) Finset.univ
    (fun j _ => hint _
      ((continuous_partialDeriv j _ hA).mul (continuous_partialDeriv j _ hW1)))]
  have e2 : ∀ j, ∫ x, Torus.partialDeriv j (fun y => Φ (u y)) x * Torus.partialDeriv j W x =
      -∫ x, Φ (u x) * Torus.partialDeriv j (Torus.partialDeriv j W) x := fun j =>
    integral_partialDeriv_mul j _ _ hA (hpW1 j)
  simp_rw [e2]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← integral_finsetSum (μ := volume) (f := fun (j : Fin d) (x : Torus d) =>
      Φ (u x) * Torus.partialDeriv j (Torus.partialDeriv j W) x) Finset.univ
    (fun j _ => hint _ (hΦc.mul (continuous_partialDeriv j _ (hpW1 j))))]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [hlap x, Finset.mul_sum]

/-! ### Section 2: the differential inequality for `∫ Φ(ρ)` -/

/-- If `Φ` is convex-like (`Φ'' ≥ 0`, `Φ ≥ 0`) on an open set `I` containing the range, with
`rΦ''(r) = -aΦ'(r)`, and `ΔW ≥ -G`, then
`∫ Φ'(ρ)(νΔρ + Div(ρ∇W)) ≤ a G ∫ Φ(ρ)`. -/
theorem integral_deriv_mul_rhs_le (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 2 V)
    (hVK : MemHs K (coeffOf V)) (ν : ℝ) (hν : 0 ≤ ν)
    (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c) (Φ : ℝ → ℝ) (I : Set ℝ) (hI : IsOpen I)
    (hΦ : ContDiffOn ℝ 2 Φ I) (hrange : ∀ x, toFun c x ∈ I) (a G : ℝ) (ha : 0 ≤ a)
    (hΦ2 : ∀ r ∈ I, 0 ≤ deriv (deriv Φ) r) (hΦ0 : ∀ r ∈ I, 0 ≤ Φ r)
    (hrel : ∀ r ∈ I, deriv (deriv Φ) r * r = -a * deriv Φ r)
    (hΔ : ∀ x, -G ≤ Torus.laplacian (Wpot d s V c) x) :
    ∫ x, deriv Φ (toFun c x) * toFun (mfRhsCoeff d s V ν c) x ≤
      a * G * ∫ x, Φ (toFun c x) := by
  rw [integral_deriv_mul_rhs' hd s hs0 hsd K hK V hV hVK ν c hc hreal Φ I hI hΦ hrange]
  obtain ⟨C₂, -, hC₂⟩ := exists_mfPath_isCk (d := d) 2 K (by simpa using hK)
  have hρ2 : Torus.IsCk 2 (toFun c) := (hC₂ c hc hreal).1
  have hρ1 : Torus.IsCk 1 (toFun c) := hρ2.of_le (by norm_num)
  have hW2 := isCk_two_Wpot hd s hs0 hsd K hK V hV c hc hreal
  have hρc : Continuous (toFun c) := continuous_of_isCk' hρ1 le_rfl
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hΦc : Continuous fun x => Φ (toFun c x) :=
    hΦ.continuousOn.comp_continuous hρc hrange
  have hWlap : Continuous (Torus.laplacian (Wpot d s V c)) := by
    have : Torus.laplacian (Wpot d s V c) = fun x => ∑ j, Torus.partialDeriv j
        (Torus.partialDeriv j (Wpot d s V c)) x := by
      funext x; exact laplacian_eq_sum _ hW2 x
    rw [this]
    exact continuous_finsetSum _ fun j _ =>
      continuous_partialDeriv j _ (isCk_one_partialDeriv j _ hW2)
  have hA : 0 ≤ ∫ x, deriv (deriv Φ) (toFun c x) * ‖Torus.grad (toFun c) x‖ ^ 2 :=
    integral_nonneg fun x => mul_nonneg (hΦ2 _ (hrange x)) (sq_nonneg _)
  have hibp := integral_deriv_comp_grad_mul Φ I hI (hΦ.of_le (by norm_num)) (toFun c)
    (Wpot d s V c) hρ1 hW2 hrange
  have hB : ∫ x, deriv (deriv Φ) (toFun c x) * toFun c x *
      inner ℝ (Torus.grad (toFun c) x) (Torus.grad (Wpot d s V c) x) =
      -a * (-∫ x, Φ (toFun c x) * Torus.laplacian (Wpot d s V c) x) := by
    rw [← hibp, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [hrel _ (hrange x)]; ring
  rw [hB]
  have hJ : -∫ x, Φ (toFun c x) * Torus.laplacian (Wpot d s V c) x ≤
      G * ∫ x, Φ (toFun c x) := by
    rw [← integral_neg, ← integral_const_mul]
    refine integral_mono (hint _ (hΦc.mul hWlap).neg) (hint _ (continuous_const.mul hΦc)) fun x => ?_
    have h0 := hΦ0 _ (hrange x)
    have h1 := hΔ x
    simp only
    nlinarith
  have := mul_le_mul_of_nonneg_left hJ ha
  have h2 : 0 ≤ ν * ∫ x, deriv (deriv Φ) (toFun c x) * ‖Torus.grad (toFun c) x‖ ^ 2 :=
    mul_nonneg hν hA
  nlinarith

/-! ### Section 3: the functional `Φ_p(r) = r^{-p}` -/

theorem negPow_contDiffOn (p : ℕ) :
    ContDiffOn ℝ 2 (fun r : ℝ => r ^ (-(p : ℤ))) (Ioi 0) := by
  have : (fun r : ℝ => r ^ (-(p : ℤ))) = fun r => (r ^ p)⁻¹ := by
    funext r; simp [zpow_neg]
  rw [this]
  exact ((contDiff_id.pow p).contDiffOn).inv (fun r hr => (pow_pos hr p).ne')

theorem deriv_negPow (p : ℕ) :
    deriv (fun r : ℝ => r ^ (-(p : ℤ))) = fun r => (((-(p : ℤ) : ℤ)) : ℝ) * r ^ (-(p : ℤ) - 1) :=
  deriv_zpow' _

theorem deriv_deriv_negPow (p : ℕ) :
    deriv (deriv (fun r : ℝ => r ^ (-(p : ℤ)))) =
      fun r => (((-(p : ℤ) : ℤ)) : ℝ) * ((((-(p : ℤ) - 1 : ℤ)) : ℝ) * r ^ (-(p : ℤ) - 1 - 1)) := by
  rw [deriv_negPow]
  funext r
  rw [deriv_const_mul_field']
  simp only
  rw [deriv_zpow]

theorem negPow_deriv2_nonneg (p : ℕ) {r : ℝ} (hr : 0 < r) :
    0 ≤ deriv (deriv (fun r : ℝ => r ^ (-(p : ℤ)))) r := by
  rw [deriv_deriv_negPow]
  have h : (((-(p : ℤ) : ℤ)) : ℝ) * ((((-(p : ℤ) - 1 : ℤ)) : ℝ) * r ^ (-(p : ℤ) - 1 - 1)) =
      (p : ℝ) * ((p : ℝ) + 1) * r ^ (-(p : ℤ) - 1 - 1) := by
    push_cast; ring
  simp only
  rw [h]
  positivity

theorem negPow_rel (p : ℕ) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (fun r : ℝ => r ^ (-(p : ℤ)))) r * r =
      -((p : ℝ) + 1) * deriv (fun r : ℝ => r ^ (-(p : ℤ))) r := by
  rw [deriv_deriv_negPow, deriv_negPow]
  have e : r ^ (-(p : ℤ) - 1) = r ^ (-(p : ℤ) - 1 - 1) * r := by
    rw [← zpow_add_one₀ hr.ne']; congr 1; ring
  simp only
  rw [e]
  push_cast
  ring

/-! ### Section 4: continuity of a parameter integral on a compact time interval -/

theorem continuousOn_integral_comp (u : ℝ → Torus d → ℝ) (Φ : ℝ → ℝ) (I : Set ℝ)
    (hΦ : ContinuousOn Φ I) {a b : ℝ}
    (hu : ContinuousOn (fun p : ℝ × Torus d => u p.1 p.2) (Icc a b ×ˢ univ))
    (hrange : ∀ τ ∈ Icc a b, ∀ x, u τ x ∈ I) :
    ContinuousOn (fun τ => ∫ x, Φ (u τ x)) (Icc a b) := by
  have hmaps : MapsTo (fun p : ℝ × Torus d => u p.1 p.2) (Icc a b ×ˢ univ) I :=
    fun p hp => hrange p.1 hp.1 p.2
  have hcomp := hΦ.comp hu hmaps
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hcomp
  refine continuousOn_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const C) ?_
  · intro τ hτ
    have : Continuous fun x : Torus d => Φ (u τ x) :=
      hcomp.comp_continuous (Continuous.prodMk_right τ) (fun x => ⟨hτ, mem_univ _⟩)
    exact this.aestronglyMeasurable
  · intro τ hτ
    exact Eventually.of_forall fun x => hC (τ, x) ⟨hτ, mem_univ _⟩
  · refine Eventually.of_forall fun x => ?_
    exact hcomp.comp (continuousOn_id.prodMk continuousOn_const)
      (fun τ hτ => ⟨hτ, mem_univ x⟩)

/-! ### Section 5: Step A, the minimum principle under an a-priori positivity assumption -/

/-- Step A: if `ρ ≥ η > 0` on `[0,T'] × 𝕋` (`T' ≤ T`), then `ρ^t ≥ m₀ e^{-Gt}` on `[0,T']`. -/
theorem lower_bound_of_pos_on (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (hν : 0 < ν) (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hρ₀ : ∀ x, m₀ ≤ mfPath ρc 0 x) (G : ℝ) (_hG : 0 ≤ G)
    (hΔ : ∀ t ∈ Set.Icc 0 T, ∀ x, -G ≤ Torus.laplacian (Wpot d s V (ρc t)) x)
    {T' : ℝ} (hT'T : T' ≤ T) {η : ℝ} (hη : 0 < η)
    (hρη : ∀ t ∈ Set.Icc 0 T', ∀ x, η ≤ mfPath ρc t x) :
    ∀ t ∈ Set.Icc 0 T', ∀ x, m₀ * Real.exp (-G * t) ≤ mfPath ρc t x := by
  intro t ht
  rcases ht.1.eq_or_lt with h0 | htpos
  · subst h0; intro x; simpa using hρ₀ x
  have hT'pos : 0 < T' := lt_of_lt_of_le htpos ht.2
  have hV2 : Torus.IsCk 2 V := hV.of_le (by exact_mod_cast (by omega : 2 ≤ K + 2))
  have hVK := memHs_of_isCk_nat K V hV
  have hmemT : ∀ τ ∈ Icc (0 : ℝ) T', τ ∈ Icc (0 : ℝ) T := fun τ hτ => ⟨hτ.1, hτ.2.trans hT'T⟩
  obtain ⟨h1, -⟩ := continuousOn_mfPath_prod_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H
  have h1' : ContinuousOn (fun p : ℝ × Torus d => mfPath ρc p.1 p.2) (Icc 0 T' ×ˢ univ) :=
    h1.mono (prod_mono (fun τ hτ => hmemT τ hτ) subset_rfl)
  have hpos : ∀ τ ∈ Icc (0 : ℝ) T', ∀ x, 0 < mfPath ρc τ x := fun τ hτ x =>
    lt_of_lt_of_le hη (hρη τ hτ x)
  have hYc : ∀ p : ℕ, ContinuousOn (fun τ => ∫ x, (mfPath ρc τ x) ^ (-(p : ℤ))) (Icc 0 T') :=
    fun p => continuousOn_integral_comp (mfPath ρc) (fun r : ℝ => r ^ (-(p : ℤ))) (Ioi 0)
      (negPow_contDiffOn p).continuousOn h1' hpos
  have hYd : ∀ p : ℕ, ∀ τ ∈ Ioo (0 : ℝ) T', ∃ Y' : ℝ,
      HasDerivAt (fun τ => ∫ x, (mfPath ρc τ x) ^ (-(p : ℤ))) Y' τ ∧
        Y' ≤ ((p : ℝ) + 1) * G * ∫ x, (mfPath ρc τ x) ^ (-(p : ℤ)) := by
    intro p τ hτ
    have hτI : τ ∈ Icc (0 : ℝ) T := hmemT τ (Ioo_subset_Icc_self hτ)
    refine ⟨_, hasDerivAt_integral_comp hd s hs0 hsd K hK V ρ₀ hV ν ρc H
      (fun r : ℝ => r ^ (-(p : ℤ))) (Ioi 0) isOpen_Ioi (negPow_contDiffOn p) (a := 0) (b := T')
      le_rfl hT'pos hT'T (fun τ' hτ' x => hpos τ' hτ' x) hτ, ?_⟩
    exact integral_deriv_mul_rhs_le hd s hs0 hsd K hK V hV2 hVK ν hν.le (ρc τ)
      (H.sol.cont.1 τ hτI) (H.real τ hτI) (fun r : ℝ => r ^ (-(p : ℤ))) (Ioi 0) isOpen_Ioi
      (negPow_contDiffOn p) (fun x => hpos τ (Ioo_subset_Icc_self hτ) x) ((p : ℝ) + 1) G
      (by positivity) (fun r hr => negPow_deriv2_nonneg p hr)
      (fun r hr => (zpow_pos hr _).le) (fun r hr => negPow_rel p hr) (hΔ τ hτI)
  -- Gronwall: `Y_p(τ) e^{-(p+1)Gτ}` is non-increasing
  have hgron : ∀ p : ℕ, ∀ τ ∈ Icc (0 : ℝ) T',
      (∫ x, (mfPath ρc τ x) ^ (-(p : ℤ))) ≤
        (∫ x, (mfPath ρc 0 x) ^ (-(p : ℤ))) * Real.exp (((p : ℝ) + 1) * G * τ) := by
    intro p τ hτ
    set Y : ℝ → ℝ := fun τ => ∫ x, (mfPath ρc τ x) ^ (-(p : ℤ)) with hYdef
    set Z : ℝ → ℝ := fun τ => Y τ * Real.exp (-(((p : ℝ) + 1) * G * τ)) with hZdef
    have hZc : ContinuousOn Z (Icc 0 T') :=
      (hYc p).mul (by fun_prop)
    have hZd : ∀ τ ∈ interior (Icc (0 : ℝ) T'), ∃ Z' : ℝ, HasDerivAt Z Z' τ ∧ Z' ≤ 0 := by
      intro τ hτ
      rw [interior_Icc] at hτ
      obtain ⟨Y', hY', hle⟩ := hYd p τ hτ
      refine ⟨Y' * Real.exp (-(((p : ℝ) + 1) * G * τ)) +
        Y τ * (Real.exp (-(((p : ℝ) + 1) * G * τ)) * (-(((p : ℝ) + 1) * G))), ?_, ?_⟩
      · have hE : HasDerivAt (fun τ : ℝ => Real.exp (-(((p : ℝ) + 1) * G * τ)))
            (Real.exp (-(((p : ℝ) + 1) * G * τ)) * (-(((p : ℝ) + 1) * G))) τ := by
          have := ((hasDerivAt_id τ).const_mul (((p : ℝ) + 1) * G)).neg.exp
          simpa using this
        exact hY'.mul hE
      · have he := Real.exp_pos (-(((p : ℝ) + 1) * G * τ))
        have : Y' * Real.exp (-(((p : ℝ) + 1) * G * τ)) +
            Y τ * (Real.exp (-(((p : ℝ) + 1) * G * τ)) * (-(((p : ℝ) + 1) * G))) =
            (Y' - ((p : ℝ) + 1) * G * Y τ) * Real.exp (-(((p : ℝ) + 1) * G * τ)) := by ring
        rw [this]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) he.le
    have hanti : AntitoneOn Z (Icc 0 T') := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T') hZc ?_ ?_
      · intro τ hτ
        obtain ⟨Z', hZ', -⟩ := hZd τ hτ
        exact hZ'.differentiableAt.differentiableWithinAt
      · intro τ hτ
        obtain ⟨Z', hZ', hle⟩ := hZd τ hτ
        rw [hZ'.deriv]; exact hle
    have h := hanti ⟨le_rfl, hT'pos.le⟩ hτ hτ.1
    simp only [hZdef] at h
    have hexp := Real.exp_pos (((p : ℝ) + 1) * G * τ)
    have e1 : Real.exp (-(((p : ℝ) + 1) * G * τ)) * Real.exp (((p : ℝ) + 1) * G * τ) = 1 := by
      rw [← Real.exp_add]; simp
    have h0 : Real.exp (-(((p : ℝ) + 1) * G * 0)) = 1 := by simp
    rw [h0, mul_one] at h
    calc Y τ = Y τ * Real.exp (-(((p : ℝ) + 1) * G * τ)) * Real.exp (((p : ℝ) + 1) * G * τ) := by
          rw [mul_assoc, e1, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right h hexp.le
  -- conclusion by `abs_le_of_integral_pow_le`
  have hρt : Continuous (mfPath ρc t) :=
    h1'.comp_continuous (Continuous.prodMk_right t) (fun x => ⟨ht, mem_univ _⟩)
  have hρtpos : ∀ x, 0 < mfPath ρc t x := hpos t ht
  have hu : Continuous fun x => (mfPath ρc t x)⁻¹ := hρt.inv₀ fun x => (hρtpos x).ne'
  have hΛ : 0 ≤ m₀⁻¹ * Real.exp (G * t) := by positivity
  have hM : 0 ≤ Real.exp (G * t) := (Real.exp_pos _).le
  have habs := abs_le_of_integral_pow_le hu (m₀⁻¹ * Real.exp (G * t)) (Real.exp (G * t)) hΛ hM 0
    (fun p _ => by
      have hy := hgron p t ht
      have hint0 : ∫ x, (mfPath ρc 0 x) ^ (-(p : ℤ)) ≤ (m₀ ^ p)⁻¹ := by
        calc ∫ x, (mfPath ρc 0 x) ^ (-(p : ℤ)) ≤ ∫ _x : Torus d, (m₀ ^ p)⁻¹ := by
              refine integral_mono ?_ (integrable_const _) fun x => ?_
              · have hc0 : Continuous (mfPath ρc 0) :=
                  h1'.comp_continuous (Continuous.prodMk_right 0)
                    (fun x => ⟨⟨le_rfl, hT'pos.le⟩, mem_univ _⟩)
                have : Continuous fun x => (mfPath ρc 0 x) ^ (-(p : ℤ)) :=
                  (negPow_contDiffOn p).continuousOn.comp_continuous hc0
                    (fun x => hpos 0 ⟨le_rfl, hT'pos.le⟩ x)
                exact this.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
              · simp only [zpow_neg, zpow_natCast]
                exact inv_anti₀ (pow_pos hm₀ p) (pow_le_pow_left₀ hm₀.le (hρ₀ x) p)
          _ = (m₀ ^ p)⁻¹ := by simp
      have e2 : ∫ x, |(mfPath ρc t x)⁻¹| ^ p = ∫ x, (mfPath ρc t x) ^ (-(p : ℤ)) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [abs_of_pos (inv_pos.mpr (hρtpos x))]
        simp [zpow_neg]
      rw [e2]
      refine hy.trans ?_
      have hexp : Real.exp (((p : ℝ) + 1) * G * t) =
          Real.exp (G * t) * Real.exp (G * t) ^ p := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
      calc (∫ x, (mfPath ρc 0 x) ^ (-(p : ℤ))) * Real.exp (((p : ℝ) + 1) * G * t)
          ≤ (m₀ ^ p)⁻¹ * Real.exp (((p : ℝ) + 1) * G * t) :=
            mul_le_mul_of_nonneg_right hint0 (Real.exp_pos _).le
        _ = Real.exp (G * t) * (m₀⁻¹ * Real.exp (G * t)) ^ p := by
            rw [hexp, mul_pow, inv_pow]; ring)
  intro x
  have hx := habs x
  rw [abs_of_pos (inv_pos.mpr (hρtpos x))] at hx
  have h3 : (m₀⁻¹ * Real.exp (G * t))⁻¹ ≤ ((mfPath ρc t x)⁻¹)⁻¹ :=
    inv_anti₀ (inv_pos.mpr (hρtpos x)) hx
  rw [inv_inv, mul_inv, inv_inv, ← Real.exp_neg] at h3
  simpa [neg_mul] using h3

/-! ### Section 6: Step B, continuation, and the main theorems -/

/-- Quantitative minimum principle on `[0,T]`: if `ΔW ≥ -G` on `[0,T]` and `ρ⁰ ≥ m₀ > 0`, then
`ρ^t ≥ m₀ e^{-Gt}` on `[0,T]`. (Amended statement, `MeanFieldAprioriAmendment.md` §2.5.) -/
theorem lower_bound_of_laplacian_ge (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (hν : 0 < ν) (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hρ₀ : ∀ x, m₀ ≤ mfPath ρc 0 x) (G : ℝ) (hG : 0 ≤ G)
    (hΔ : ∀ t ∈ Set.Icc 0 T, ∀ x, -G ≤ Torus.laplacian (Wpot d s V (ρc t)) x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x, m₀ * Real.exp (-G * t) ≤ mfPath ρc t x := by
  obtain ⟨h1, -⟩ := continuousOn_mfPath_prod_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H
  by_cases hT : T < 0
  · intro t ht
    exact absurd ht.2 (by linarith [ht.1])
  push Not at hT
  set S : Set ℝ := {a | a ∈ Icc (0 : ℝ) T ∧
    ∀ τ ∈ Icc (0 : ℝ) a, ∀ y, m₀ * Real.exp (-G * τ) ≤ mfPath ρc τ y} with hS
  have hP0 : ∀ τ ∈ Icc (0 : ℝ) 0, ∀ y, m₀ * Real.exp (-G * τ) ≤ mfPath ρc τ y := by
    intro τ hτ y
    have : τ = 0 := le_antisymm hτ.2 hτ.1
    subst this
    simpa using hρ₀ y
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hT⟩, hP0⟩
  have hbdd : BddAbove S := ⟨T, fun a ha => ha.1.2⟩
  have hne : S.Nonempty := ⟨0, h0S⟩
  have haT : sSup S ≤ T := csSup_le hne (fun b hb => hb.1.2)
  have ha0 : 0 ≤ sSup S := le_csSup hbdd h0S
  -- extension past a point of `S` below `T`
  have hext : ∀ b ∈ S, b < T → ∃ ε : ℝ, 0 < ε ∧ b + ε ∈ S := by
    intro b hbS hbT
    obtain ⟨⟨hb0, -⟩, hPb⟩ := hbS
    set η₀ : ℝ := m₀ * Real.exp (-G * b) / 2 with hη₀
    have hη₀pos : 0 < η₀ := by positivity
    obtain ⟨v, hv, hvb⟩ := IsCompact.mem_uniformity_of_prod
      (f := fun (τ : ℝ) (y : Torus d) => mfPath ρc τ y) (s := Icc 0 T) (k := univ) (q := b)
      (u := {pr : ℝ × ℝ | dist pr.1 pr.2 < η₀}) isCompact_univ h1 ⟨hb0, hbT.le⟩
      (Metric.dist_mem_uniformity hη₀pos)
    obtain ⟨δ, hδ, hδv⟩ := Metric.mem_nhdsWithin_iff.mp hv
    set ε : ℝ := min (δ / 2) (T - b) with hε
    have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
    have hεδ : ε ≤ δ / 2 := min_le_left _ _
    have hεT : b + ε ≤ T := by have := min_le_right (δ / 2) (T - b); linarith
    refine ⟨ε, hεpos, ⟨⟨by linarith, hεT⟩, ?_⟩⟩
    set η : ℝ := min η₀ (m₀ * Real.exp (-G * T)) with hη
    have hηpos : 0 < η := lt_min hη₀pos (by positivity)
    have hlow : ∀ t ∈ Icc (0 : ℝ) (b + ε), ∀ y, η ≤ mfPath ρc t y := by
      intro t ht y
      by_cases htb : t ≤ b
      · have h2 := hPb t ⟨ht.1, htb⟩ y
        refine (min_le_right _ _).trans (le_trans ?_ h2)
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hm₀.le
        have : t ≤ T := htb.trans hbT.le
        nlinarith
      · push Not at htb
        have htv : mfPath ρc t y ∈ Set.univ := mem_univ _
        have hmem : t ∈ Metric.ball b δ ∩ Icc 0 T := by
          refine ⟨?_, ⟨ht.1, ht.2.trans hεT⟩⟩
          rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
          linarith [ht.2]
        have hd1 := hvb t (hδv hmem) y (mem_univ _)
        simp only [Set.mem_ofPred_eq, Real.dist_eq] at hd1
        have h3 := hPb b ⟨hb0, le_rfl⟩ y
        have h4 := (abs_lt.mp hd1).1
        refine (min_le_left _ _).trans ?_
        rw [hη₀] at *
        linarith
    have hT'T : b + ε ≤ T := hεT
    have hη' : 0 < η := hηpos
    exact lower_bound_of_pos_on hd s hs0 hsd K hK V ρ₀ hV ν hν ρc H m₀ hm₀ hρ₀ G hG hΔ hT'T hη' hlow
  -- `sSup S ∈ S`
  have haS : sSup S ∈ S := by
    refine ⟨⟨ha0, haT⟩, fun τ hτ y => ?_⟩
    rcases hτ.2.lt_or_eq with hlt | heq
    · obtain ⟨b, hbS, hτb⟩ := exists_lt_of_lt_csSup hne hlt
      exact hbS.2 τ ⟨hτ.1, hτb.le⟩ y
    · by_cases hz : τ = 0
      · subst hz; exact hP0 0 ⟨le_rfl, le_rfl⟩ y
      · have hτpos : 0 < τ := lt_of_le_of_ne hτ.1 (Ne.symm hz)
        have hτT : τ ≤ T := hτ.2.trans haT
        have hcl : τ ∈ closure (Ico (0 : ℝ) τ) := by
          rw [closure_Ico (Ne.symm hz)]; exact ⟨hτ.1, le_rfl⟩
        have hcy : ContinuousWithinAt (fun σ => mfPath ρc σ y) (Ico 0 τ) τ := by
          have hcy0 : ContinuousOn (fun σ => mfPath ρc σ y) (Icc 0 T) :=
            h1.comp (continuousOn_id.prodMk continuousOn_const) (fun σ hσ => ⟨hσ, mem_univ y⟩)
          exact (hcy0 τ ⟨hτ.1, hτT⟩).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hτT))
        have hcf : ContinuousWithinAt (fun σ : ℝ => m₀ * Real.exp (-G * σ)) (Ico 0 τ) τ :=
          (by fun_prop : Continuous fun σ : ℝ => m₀ * Real.exp (-G * σ)).continuousWithinAt
        refine hcf.closure_le hcl hcy fun σ hσ => ?_
        obtain ⟨b, hbS, hσb⟩ := exists_lt_of_lt_csSup hne (lt_of_lt_of_le hσ.2 hτ.2)
        exact hbS.2 σ ⟨hσ.1, hσb.le⟩ y
  have hTeq : sSup S = T := by
    by_contra hne'
    have hlt : sSup S < T := lt_of_le_of_ne haT hne'
    obtain ⟨ε, hε, hεS⟩ := hext _ haS hlt
    have := le_csSup hbdd hεS
    linarith
  intro t ht
  exact haS.2 t ⟨ht.1, hTeq ▸ ht.2⟩

/-! ### Section 7: positivity on every compact interval -/

/-- An `L²` function and a continuous function with the same Fourier coefficients agree a.e. -/
theorem ae_eq_of_funFourierCoeff_eq_of_memLp {u v : Torus d → ℝ} (hu : MemLp u 2 volume)
    (hv : Continuous v)
    (h : ∀ k, Torus.funFourierCoeff (fun x => (u x : ℂ)) k =
      Torus.funFourierCoeff (fun x => (v x : ℂ)) k) : u =ᵐ[volume] v := by
  set w : Torus d → ℝ := fun x => u x - v x with hw
  have hv2 : MemLp v 2 volume := hv.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hw2 : MemLp w 2 volume := hu.sub hv2
  have hwi : Integrable w := hw2.integrable one_le_two
  have hui : Integrable u := hu.integrable one_le_two
  have hvi : Integrable v := hv2.integrable one_le_two
  have hs := Torus.hasSum_sq_coeff hw2
  have hz : ∀ n : Lattice d, Torus.cosCoeff w n ^ 2 + Torus.sinCoeff w n ^ 2 = 0 := by
    intro n
    rw [← Torus.norm_sq_coeff hwi]
    have h1 := h n
    rw [funFourierCoeff_eq_int, funFourierCoeff_eq_int] at h1
    have h2 : ∫ x, Torus.mode (-n) x * (w x : ℂ) = 0 := by
      have : ∀ x, Torus.mode (-n) x * (w x : ℂ) =
          Torus.mode (-n) x * (u x : ℂ) - Torus.mode (-n) x * (v x : ℂ) := by
        intro x; simp only [hw]; push_cast; ring
      simp_rw [this]
      rw [integral_sub]
      · exact sub_eq_zero.mpr h1
      · exact (MFAux.integrable_mode_mul_real' (-n) hui)
      · exact (MFAux.integrable_mode_mul_real' (-n) hvi)
    rw [h2]; simp
  have hs0 : HasSum (fun n : Lattice d => Torus.cosCoeff w n ^ 2 + Torus.sinCoeff w n ^ 2) 0 := by
    simp [hz]
  have hint : ∫ x, w x ^ 2 = 0 := hs.unique hs0
  have hae : (fun x => w x ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hw2.integrable_sq).mp hint
  filter_upwards [hae] with x hx
  simp only [Pi.zero_apply, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at hx
  simpa [hw, sub_eq_zero] using hx

/-- The path at time `0` is the continuous representative of `ρ⁰`; pointwise lower bounds of `ρ⁰`
(which is only an `H^K` function) pass to it. -/
theorem le_mfPath_zero {K : ℝ} (hK : (d : ℝ) / 2 < K) {ρ₀ : Torus d → ℝ} (hρ₀ : MemSobolev K ρ₀)
    {c : ℝ} (hc : ∀ x, c ≤ ρ₀ x) {ρc : ℝ → Coeff d} (h0 : ρc 0 = coeffOf ρ₀) :
    ∀ x, c ≤ mfPath ρc 0 x := by
  have hL2 := hρ₀.1
  have hmem := (hsNormSq_coeffOf K ρ₀ hρ₀).1
  have hsum := summable_norm_of_memHs K hK _ hmem
  have hreal := isRealCoeff_coeffOf ρ₀ (hL2.integrable one_le_two)
  have hg : mfPath ρc 0 = toFun (coeffOf ρ₀) := by
    funext x; simp [mfPath, h0]
  have hgc : Continuous (toFun (coeffOf ρ₀)) := MFProduct.continuous_toFun _ hsum
  have hco := coeffOf_toFun _ hreal hsum
  have hae : ρ₀ =ᵐ[volume] toFun (coeffOf ρ₀) :=
    ae_eq_of_funFourierCoeff_eq_of_memLp hL2 hgc (fun k => (congrFun hco k).symm)
  rw [hg]
  by_contra hex
  push Not at hex
  obtain ⟨x, hx⟩ := hex
  have hUo : IsOpen {y | toFun (coeffOf ρ₀) y < c} := isOpen_lt hgc continuous_const
  have hpos : 0 < volume {y | toFun (coeffOf ρ₀) y < c} := hUo.measure_pos volume ⟨x, hx⟩
  have hnull : volume {y | toFun (coeffOf ρ₀) y < c} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with y hy
    simp only [not_lt]
    rw [← hy]; exact hc y
  exact hpos.ne' hnull

/-- Positivity on every compact interval (no uniformity in `T`).
(Amended statement, `MeanFieldAprioriAmendment.md` §2.5.) -/
theorem exists_pos_on_Icc (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (hν : 0 < ν) (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T)
    (hρ₀ : MemSobolev K ρ₀) (hpos : ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ ρ₀ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc 0 T, ∀ x, δ ≤ mfPath ρc t x := by
  obtain ⟨c, hc0, hc⟩ := hpos
  by_cases hT : T < 0
  · exact ⟨1, one_pos, fun t ht => absurd ht.2 (by linarith [ht.1])⟩
  push Not at hT
  have hKd : (d : ℝ) / 2 < K := by linarith
  have hρ0 := le_mfPath_zero hKd hρ₀ hc H.sol.init
  have hV2 : Torus.IsCk 2 V := hV.of_le (by exact_mod_cast (by omega : 2 ≤ K + 2))
  obtain ⟨C, hC0, hC⟩ := exists_Wpot_bounds hd s hs0 hsd (K : ℝ) hK V hV2
  obtain ⟨B, hB⟩ := exists_bound_of_continuousInHsOn_Icc (K : ℝ) ρc T H.sol.cont
  set G : ℝ := C * (1 + max B 0) with hGdef
  have hG : 0 ≤ G := by positivity
  have hΔ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, -G ≤ Torus.laplacian (Wpot d s V (ρc t)) x := by
    intro t ht x
    have h := (hC (ρc t) (H.sol.cont.1 t ht) (H.real t ht) x).1
    have h2 := (abs_le.mp h).1
    have hb : hsNorm (K : ℝ) (ρc t) ≤ max B 0 := (hB t ht).trans (le_max_left _ _)
    have : C * (1 + hsNorm (K : ℝ) (ρc t)) ≤ G := by
      rw [hGdef]; exact mul_le_mul_of_nonneg_left (by linarith) hC0
    linarith
  refine ⟨c * Real.exp (-G * T), by positivity, fun t ht x => ?_⟩
  have key := lower_bound_of_laplacian_ge hd s hs0 hsd K hK V ρ₀ hV ν hν ρc H c hc0 hρ0 G hG hΔ
    t ht x
  refine le_trans ?_ key
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc0.le
  nlinarith [ht.2]

end HRS.PDE.MFApriori
