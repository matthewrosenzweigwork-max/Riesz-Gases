import HRS.Commutator.Whole.XLIAux26

/-!
# X-LI part 27: the fractional Leibniz rule, conditional on the Carleson and `p < 2` square function bounds
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

section Main

variable (α : ℝ)

/-- the low-frequency symbol of `J^α` -/
def thLow' (η : 𝔼) : ℂ := bsymX α η * cutC η

lemma thLow'_contDiff : ContDiff ℝ ∞ (thLow' α : 𝔼 → ℂ) :=
  (bsymX_temperate α).1.mul cutC_contDiff

lemma thLow'_cs : HasCompactSupport (thLow' α : 𝔼 → ℂ) := cutC_cs.mul_left

lemma Pm0_Fm_cv (h : SchwartzMap 𝔼 ℂ) :
    ⇑(Pm 0 (Fm α h)) = cv (symK (thLow' α) 0) ⇑h := by
  funext x
  have h1 := congrFun (cv_symK_eq_mulS (thLow'_contDiff α) (thLow'_cs α) h 0) x
  rw [h1]
  unfold Pm Fm
  rw [mulS_mulS _ _ (temperate_symbol cutC_contDiff cutC_cs 0) (bsymX_temperate α)
    ((temperate_symbol cutC_contDiff cutC_cs 0).mul (bsymX_temperate α))]
  have hsym : (fun ξ : 𝔼 => cutC (((2 : ℝ) ^ (0 : ℤ))⁻¹ • ξ) * bsymX α ξ) =
      fun ξ : 𝔼 => thLow' α (((2 : ℝ) ^ (0 : ℤ))⁻¹ • ξ) := by
    funext ξ
    simp [thLow', mul_comm]
  exact (congrFun (congrArg (⇑) (mulS_congr hsym
    ((temperate_symbol cutC_contDiff cutC_cs 0).mul (bsymX_temperate α))
    (temperate_symbol (thLow'_contDiff α) (thLow'_cs α) 0) h)) x).trans rfl

lemma rep_Dm (k : ℤ) (φ : SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    Dm k φ x = cv (symK (rhoT : 𝔼 → ℂ) k) ⇑(Dm k φ) x := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ y, ‖φ y‖ ≤ B := by
    obtain ⟨C, _, hC⟩ := sch_bdd φ
    exact ⟨C, hC⟩
  have := symK_rep rho_contDiff rho_cs rhoT_contDiff rhoT_cs rhoT_mul_rho
    φ.continuous.measurable hB k x
  rw [← congrFun (cv_rho_eq_Dm k φ) x, ← cv_rho_eq_Dm k φ]
  exact this

/-- **the fractional Leibniz rule**, conditional on the Carleson endpoint and the `p < 2` square
function estimates -/
theorem main_cond (hd : 1 ≤ d) (hα : 0 < α) {r p₁ q₁ p₂ q₂ : ℝ≥0∞}
    (hr : 1 < r) (hr' : r < ⊤) (hp₁ : 1 < p₁) (hq₁ : 1 < q₁) (hp₂ : 1 < p₂) (hq₂ : 1 < q₂)
    (h1 : p₁⁻¹ + q₁⁻¹ = r⁻¹) (h2 : p₂⁻¹ + q₂⁻¹ = r⁻¹)
    (hE : ∀ u : ℝ, 1 < u → E1At (fun j => dK (Ths (-α) : ℤ → 𝔼 → ℂ) j) (u / 2))
    (hEρ : ∀ s : ℝ, 1 / 2 < s → E1At (fun j => symK (rhoT : 𝔼 → ℂ) j) s)
    (hC : ∀ r' : ℝ, 1 < r' → E4At (d := d) α r') :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f g : SchwartzMap 𝔼 ℂ,
      eLpNorm (⇑(Fm α (prodS f g))) r volume ≤
        C * (eLpNorm (⇑(Fm α f)) p₁ volume * eLpNorm (⇑g) q₁ volume +
          eLpNorm (⇑(Fm α g)) p₂ volume * eLpNorm (⇑f) q₂ volume) := by
  haveI : Nontrivial 𝔼 := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    exact inferInstance
  have hrne : r ≠ ⊤ := hr'.ne
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hr; simp at hr
  have hrr : 1 < r.toReal := by
    have := ENNReal.toReal_strict_mono hrne hr
    simpa using this
  have hrr0 : 0 < r.toReal := by linarith
  set rr : ℝ := r.toReal with hrrdef
  have hs : 1 / 2 < rr / 2 := by linarith
  obtain ⟨CP1, hCP1, hP1⟩ := PAIR α hd hr hr' hp₁ hq₁ h1 hE (hC rr hrr)
  obtain ⟨CP2, hCP2, hP2⟩ := PAIR α hd hr hr' hp₂ hq₂ h2 hE (hC rr hrr)
  obtain ⟨CH, hCH, hHIGH⟩ := HIGH α hd hα hs
  have hconj1 : 1 < rr.conjExponent := by
    have hconj : rr.HolderConjugate rr.conjExponent := Real.HolderConjugate.conjExponent hrr
    exact (Real.holderConjugate_iff.1 hconj.symm).1
  obtain ⟨CS, hSYN⟩ := SYN hd hrr (hEρ (rr.conjExponent / 2) (by linarith))
  obtain ⟨CBP, hCBP, hBP⟩ := BP α hα
  set κ0 : 𝔼 → ℂ := symK (thLow' α : 𝔼 → ℂ) 0 with hκ0
  have hκ0i : Integrable κ0 := symK_integrable (d := d) (thLow'_contDiff α) (thLow'_cs α) 0
  have hκ0m : Measurable κ0 := (symK_continuous (d := d) (thLow'_contDiff α) (thLow'_cs α) 0).measurable
  set N0 : ℝ≥0∞ := ∫⁻ z, ‖κ0 z‖ₑ with hN0
  have hN0ne : N0 ≠ ⊤ := hκ0i.hasFiniteIntegral.ne
  have hp1' : 1 ≤ p₁ := hp₁.le
  have hrone : 1 ≤ r := hr.le
  haveI hT1 : ENNReal.HolderTriple p₁ q₁ r := ⟨h1⟩
  set Chi : ℝ≥0∞ := ((CS : ℝ≥0∞) * CH) ^ (1 / rr) with hChi
  have hChine : Chi ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hCH)
  have key : ∀ A Y : ℝ≥0∞, A ^ (1 / rr) ≤ Y → A ≤ Y ^ rr := by
    intro A Y h
    have := ENNReal.rpow_le_rpow h hrr0.le
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hrr0.ne', ENNReal.rpow_one] at this
  refine ⟨N0 * CBP + Chi * (CP1 + CP2),
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hN0ne hCBP,
      ENNReal.mul_ne_top hChine (ENNReal.add_ne_top.2 ⟨hCP1, hCP2⟩)⟩, fun f g => ?_⟩
  set H : SchwartzMap 𝔼 ℂ := Fm α (prodS f g) with hH
  set X1 : ℝ≥0∞ := eLpNorm (⇑(Fm α f)) p₁ volume * eLpNorm (⇑g) q₁ volume with hX1
  set X2 : ℝ≥0∞ := eLpNorm (⇑(Fm α g)) p₂ volume * eLpNorm (⇑f) q₂ volume with hX2
  -- the low-frequency part
  have hlow : eLpNorm (⇑(Pm 0 H)) r volume ≤ N0 * CBP * (X1 + X2) := by
    rw [hH, Pm0_Fm_cv α (prodS f g)]
    have hcv := eLpNorm_cv_le hκ0m (prodS f g).continuous.measurable hrone
    refine hcv.trans ?_
    have hfg : eLpNorm (⇑(prodS f g)) r volume ≤ eLpNorm (⇑f) p₁ volume * eLpNorm (⇑g) q₁ volume := by
      have := eLpNorm_smul_le_mul_eLpNorm (μ := volume) (p := p₁) (q := q₁) (r := r)
        f.continuous.aestronglyMeasurable g.continuous.aestronglyMeasurable
      have e : (⇑(prodS f g) : 𝔼 → ℂ) = (⇑f) • (⇑g) := by
        funext x; simp [prodS_apply]
      rw [e]
      exact this
    have hfp := hBP f p₁ hp1'
    calc N0 * eLpNorm (⇑(prodS f g)) r volume
        ≤ N0 * (eLpNorm (⇑f) p₁ volume * eLpNorm (⇑g) q₁ volume) := mul_le_mul_right hfg _
      _ ≤ N0 * ((CBP * eLpNorm (⇑(Fm α f)) p₁ volume) * eLpNorm (⇑g) q₁ volume) :=
          mul_le_mul_right (mul_le_mul_left hfp _) _
      _ = N0 * CBP * X1 := by rw [hX1]; ring
      _ ≤ N0 * CBP * (X1 + X2) := mul_le_mul_right le_self_add _
  -- the high-frequency part
  have hAle : ∫⁻ x, QQ α f g x ^ (rr / 2) ≤ (CP1 * X1) ^ rr :=
    key _ _ (by simpa [hX1, mul_assoc] using hP1 f g)
  have hBle : ∫⁻ x, QQ α g f x ^ (rr / 2) ≤ (CP2 * X2) ^ rr :=
    key _ _ (by simpa [hX2, mul_assoc] using hP2 g f)
  have hhigh : ∀ K : ℕ, eLpNorm (fun x => ∑ k ∈ Finset.range K, Dm ((k : ℤ) + 1) H x) r volume ≤
      Chi * (CP1 + CP2) * (X1 + X2) := by
    intro K
    set S : Finset ℤ := (Finset.range K).image (fun k : ℕ => (k : ℤ) + 1) with hS
    have hinj : Set.InjOn (fun k : ℕ => (k : ℤ) + 1) (Finset.range K : Set ℕ) :=
      fun a _ b _ h => by simpa using h
    have hsum_eq : (fun x => ∑ k ∈ Finset.range K, Dm ((k : ℤ) + 1) H x) =
        fun x => ∑ k ∈ S, Dm k H x := by
      funext x
      rw [hS, Finset.sum_image hinj]
    have hS1 : ∀ k ∈ S, 1 ≤ k := by
      intro k hk
      rw [hS, Finset.mem_image] at hk
      obtain ⟨a, _, rfl⟩ := hk
      omega
    have hSYN' := hSYN S (fun k => Dm k H) (fun k x => rep_Dm k H x)
    simp only [sum_apply_schwartz] at hSYN'
    have hpt : ∀ x, (∑ k ∈ S, ‖Dm k H x‖ₑ ^ 2) ≤ ∑' k : ℤ, if 1 ≤ k then
        ‖cv (symK rho k) ⇑(Fm α (prodS f g)) x‖ₑ ^ 2 else 0 := by
      intro x
      calc (∑ k ∈ S, ‖Dm k H x‖ₑ ^ 2)
          = ∑ k ∈ S, (if 1 ≤ k then ‖cv (symK rho k) ⇑(Fm α (prodS f g)) x‖ₑ ^ 2 else 0) := by
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [if_pos (hS1 k hk), cv_rho_eq_Dm k H]
        _ ≤ _ := ENNReal.sum_le_tsum S
    have hI : ∫⁻ x, ‖∑ k ∈ S, Dm k H x‖ₑ ^ rr ≤
        (CS : ℝ≥0∞) * (CH * ((CP1 * X1) ^ rr + (CP2 * X2) ^ rr)) := by
      refine hSYN'.trans (mul_le_mul_right ?_ _)
      calc ∫⁻ x, (∑ k ∈ S, ‖Dm k H x‖ₑ ^ 2) ^ (rr / 2)
          ≤ ∫⁻ x, (∑' k : ℤ, if 1 ≤ k then
              ‖cv (symK rho k) ⇑(Fm α (prodS f g)) x‖ₑ ^ 2 else 0) ^ (rr / 2) :=
            lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) (by positivity)
        _ ≤ CH * ((∫⁻ x, QQ α f g x ^ (rr / 2)) + ∫⁻ x, QQ α g f x ^ (rr / 2)) := hHIGH f g
        _ ≤ _ := mul_le_mul_right (add_le_add hAle hBle) _
    rw [hsum_eq, eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrne
      (by
        refine (Finset.aestronglyMeasurable_fun_sum S fun k _ => ?_)
        exact (Dm k H).continuous.aestronglyMeasurable)]
    have h2 := ENNReal.rpow_le_rpow hI (show (0 : ℝ) ≤ 1 / rr by positivity)
    refine h2.trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    have h3 := ENNReal.rpow_add_le_add_rpow ((CP1 * X1) ^ rr) ((CP2 * X2) ^ rr)
      (show (0 : ℝ) ≤ 1 / rr by positivity) (by rw [div_le_one hrr0]; linarith)
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_one_div_cancel hrr0.ne', ENNReal.rpow_one,
      ENNReal.rpow_one] at h3
    calc (CS : ℝ≥0∞) ^ (1 / rr) * (CH ^ (1 / rr) * ((CP1 * X1) ^ rr + (CP2 * X2) ^ rr) ^ (1 / rr))
        ≤ (CS : ℝ≥0∞) ^ (1 / rr) * (CH ^ (1 / rr) * (CP1 * X1 + CP2 * X2)) :=
          mul_le_mul_right (mul_le_mul_right h3 _) _
      _ = Chi * (CP1 * X1 + CP2 * X2) := by
          rw [hChi, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]; ring
      _ ≤ Chi * ((CP1 + CP2) * (X1 + X2)) := by
          refine mul_le_mul_right ?_ _
          calc CP1 * X1 + CP2 * X2 ≤ CP1 * (X1 + X2) + CP2 * (X1 + X2) :=
                add_le_add (mul_le_mul_right le_self_add _) (mul_le_mul_right le_add_self _)
            _ = _ := (add_mul _ _ _).symm
      _ = _ := by ring
  have hK : ∀ K : ℕ, eLpNorm (⇑(Pm (K : ℤ) H)) r volume ≤
      (N0 * CBP + Chi * (CP1 + CP2)) * (X1 + X2) := by
    intro K
    have heq : ⇑(Pm (K : ℤ) H) = ⇑(Pm 0 H) + fun x => ∑ k ∈ Finset.range K, Dm ((k : ℤ) + 1) H x := by
      funext x
      rw [Pm_range]
      rfl
    rw [heq, add_mul]
    exact (eLpNorm_add_le hrone).trans (add_le_add hlow (hhigh K))
  exact Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun K : ℕ => ⇑(Pm (K : ℤ) H))
    (Eventually.of_forall hK) (fun K => (Pm (K : ℤ) H).continuous.aestronglyMeasurable)
    H.continuous.aestronglyMeasurable (Eventually.of_forall fun x => tendsto_Pm_top H x)

end Main

end HRS.Commutator.Whole.XLI
