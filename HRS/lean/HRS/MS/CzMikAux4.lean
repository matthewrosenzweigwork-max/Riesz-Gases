import HRS.MS.CzMikAux3

/-!
# MIK-1, part 4: degree-zero homogeneous symbols are Mikhlin; regression check with the Riesz transform

* `mik1_isMikhlin_of_homog`: a function on `𝔼 = ℝ^d` that is smooth off `0` and invariant under positive
  dilations satisfies `mik1_IsMikhlin d A g` for some `A ≥ 0` (compactness of the unit sphere + scaling).
* `mik1_isMikhlin_xbbRm`: the Riesz symbol `xbbRm a` is Mikhlin.
* `mikhlin_localised_xbb`: `mikhlin_localised` recovers the statement of
  `HRS.Commutator.Whole.XBB.xbb_riesz_lintegral` (regression check that the generalisation agrees).
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.CZ.Mik
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS HRS.Commutator.Whole.XBB
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma mik1_isMikhlin_of_homog {g : 𝔼 → ℂ} (hg : ∀ ξ : 𝔼, ξ ≠ 0 → ContDiffAt ℝ ∞ g ξ)
    (hh : ∀ c : ℝ, 0 < c → ∀ y : 𝔼, g (c • y) = g y) :
    ∃ A : ℝ, 0 ≤ A ∧ mik1_IsMikhlin d A g := by
  have hs : IsOpen ({0}ᶜ : Set 𝔼) := isOpen_compl_singleton
  have hgs : ContDiffOn ℝ ∞ g ({0}ᶜ : Set 𝔼) := fun x hx => (hg x hx).contDiffWithinAt
  have hsph : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ Metric.sphere (0 : 𝔼) 1, ‖iteratedFDeriv ℝ i g x‖ ≤ K := by
    intro i
    have h1 : ContinuousOn (iteratedFDerivWithin ℝ i g ({0}ᶜ : Set 𝔼)) ({0}ᶜ : Set 𝔼) :=
      hgs.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hs.uniqueDiffOn
    have h2 : ContinuousOn (iteratedFDeriv ℝ i g) ({0}ᶜ : Set 𝔼) :=
      h1.congr (iteratedFDerivWithin_of_isOpen i hs).symm
    have hsub : Metric.sphere (0 : 𝔼) 1 ⊆ ({0}ᶜ : Set 𝔼) := fun x hx => by
      intro h0
      rw [Set.mem_singleton_iff] at h0
      subst h0
      simp at hx
    have hcont : ContinuousOn (fun x => ‖iteratedFDeriv ℝ i g x‖) (Metric.sphere (0 : 𝔼) 1) :=
      (h2.mono hsub).norm
    obtain ⟨K, hK⟩ := (isCompact_sphere (0 : 𝔼) 1).exists_bound_of_continuousOn hcont
    refine ⟨max K 0, le_max_right _ _, fun x hx => ?_⟩
    have := hK x hx
    rw [norm_norm] at this
    exact this.trans (le_max_left _ _)
  choose K hK0 hK using hsph
  refine ⟨∑ i ∈ Finset.range (d + 2), K i, Finset.sum_nonneg fun i _ => hK0 i, hg, ?_⟩
  intro i hi ξ hξ
  have hKA : K i ≤ ∑ j ∈ Finset.range (d + 2), K j :=
    Finset.single_le_sum (f := K) (fun j _ => hK0 j) (Finset.mem_range.2 (by omega))
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set c : ℝ := ‖ξ‖⁻¹ with hc
  have hcpos : 0 < c := inv_pos.2 hn
  set ℓ : 𝔼 →L[ℝ] 𝔼 := c • ContinuousLinearMap.id ℝ 𝔼 with hℓ
  have hℓy : ∀ y, ℓ y = c • y := fun y => by simp [hℓ]
  have hsg : IsOpen (ℓ ⁻¹' ({0}ᶜ : Set 𝔼)) := hs.preimage ℓ.continuous
  have hℓξ : ℓ ξ ∈ ({0}ᶜ : Set 𝔼) := by
    rw [hℓy]; simpa [hcpos.ne'] using hξ
  have hle : (i : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  have h1 := ℓ.iteratedFDerivWithin_comp_right hgs hs.uniqueDiffOn hsg.uniqueDiffOn hℓξ hle
  have hcomp : (g ∘ ⇑ℓ) = g := by funext y; simp [hℓy, hh c hcpos]
  rw [hcomp, iteratedFDerivWithin_of_isOpen i hsg (show ξ ∈ ℓ ⁻¹' ({0}ᶜ : Set 𝔼) from hℓξ),
    iteratedFDerivWithin_of_isOpen i hs hℓξ] at h1
  rw [h1]
  have hℓn : ‖ℓ‖ ≤ c := by
    calc ‖ℓ‖ = ‖c‖ * ‖ContinuousLinearMap.id ℝ 𝔼‖ := norm_smul _ _
      _ ≤ ‖c‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ = c := by rw [mul_one, Real.norm_of_nonneg hcpos.le]
  have h2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ i g (ℓ ξ)) (fun _ : Fin i => ℓ)
  have h3 : ∏ _j : Fin i, ‖ℓ‖ ≤ c ^ i := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) hℓn _
  have hsph1 : ℓ ξ ∈ Metric.sphere (0 : 𝔼) 1 := by
    rw [mem_sphere_iff_norm, sub_zero, hℓy, norm_smul, Real.norm_of_nonneg hcpos.le, hc]
    exact inv_mul_cancel₀ hn.ne'
  have h4 := hK i (ℓ ξ) hsph1
  have hpow : ‖ξ‖ ^ (-(i : ℝ)) = c ^ i := by
    rw [Real.rpow_neg hn.le, Real.rpow_natCast, hc, inv_pow]
  rw [hpow]
  calc ‖(iteratedFDeriv ℝ i g (ℓ ξ)).compContinuousLinearMap fun _ => ℓ‖
      ≤ ‖iteratedFDeriv ℝ i g (ℓ ξ)‖ * ∏ _j : Fin i, ‖ℓ‖ := h2
    _ ≤ ‖iteratedFDeriv ℝ i g (ℓ ξ)‖ * c ^ i := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ ≤ K i * c ^ i := mul_le_mul_of_nonneg_right h4 (pow_nonneg hcpos.le _)
    _ ≤ (∑ j ∈ Finset.range (d + 2), K j) * c ^ i :=
        mul_le_mul_of_nonneg_right hKA (pow_nonneg hcpos.le _)

lemma mik1_isMikhlin_xbbRm (a : Fin d) : ∃ A : ℝ, 0 ≤ A ∧ mik1_IsMikhlin d A (xbbRm a : 𝔼 → ℂ) := by
  refine mik1_isMikhlin_of_homog (fun η hη => ?_) (fun c hc y => xbbRm_smul a hc y)
  have hn : 0 < ‖η‖ := norm_pos_iff.2 hη
  have h1 : ContDiffAt ℝ ∞ (fun η : 𝔼 => (η a : ℝ)) η :=
    ((EuclideanSpace.proj a : 𝔼 →L[ℝ] ℝ).contDiff).contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun η : 𝔼 => ‖η‖) η := contDiffAt_norm ℝ hη
  unfold xbbRm
  exact contDiffAt_const.mul
    ((Complex.ofRealCLM.contDiff.contDiffAt).comp η (h1.div h2 hn.ne'))

/-- regression check: `mikhlin_localised` applied to the Riesz symbol gives `xbb_riesz_lintegral` -/
theorem mikhlin_localised_xbb (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) (a : Fin d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (u R : 𝓢(𝔼, ℂ)) (ε Rr : ℝ), 0 < ε →
      (∀ ξ : 𝔼, (‖ξ‖ < ε ∨ Rr < ‖ξ‖) → 𝓕 (⇑u) ξ = 0) →
      (∀ ξ : 𝔼, 𝓕 (⇑R) ξ = xbbRm a ξ * 𝓕 (⇑u) ξ) →
      ∫⁻ x, ‖R x‖ₑ ^ p ≤ C * ∫⁻ x, ‖u x‖ₑ ^ p := by
  obtain ⟨C, hC, hmain⟩ := mikhlin_localised hd hp
  obtain ⟨A, hA, hm⟩ := mik1_isMikhlin_xbbRm (d := d) a
  refine ⟨C * ENNReal.ofReal A ^ p, ENNReal.mul_ne_top hC
    (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top), ?_⟩
  intro u R ε Rr hε hu hR
  exact hmain A (xbbRm a) hA hm u R ε Rr hε hu hR

end HRS.CZ.Mik
