import HRS.MS.WadAux35
import HRS.Whole.CriticalNoise

/-!
# S8.3, packet D7 (Route A), part 1: toolkit for classical backward solutions

* `s85_gen_add_const`: `generatorW (critCoeff …)` kills additive constants (it only sees `fderiv`).
* `s85_cl_to_G`, `s85_G_to_cl`: `IsClassicalAdjointW C = IsAdjointSolutionG (generatorW C)`.
* `s85_transfer`: adding a `C¹` function `κ(r)` of time to an `IsAdjointSolutionG` and changing the
  generator accordingly.
* `s85_G_shift`, `s85_G_restrict`: time shift (time independent generator) and restriction to a shorter
  horizon.
* `s85_apriori_sub_classical`, `s85_cl_unique`, `s85_propagator_eq`: Lipschitz dependence on the datum and
  uniqueness of the frozen classical solutions.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s85_gen_add_const (a β : ℝ) (ρβ : Euc d → ℝ) (r : ℝ) (h : Euc d → ℝ) (c : ℝ) (x : Euc d) :
    generatorW (critCoeff d a β ρβ) r (fun y => h y + c) x = generatorW (critCoeff d a β ρβ) r h x := by
  have hf : fderiv ℝ (fun y => h y + c) = fderiv ℝ h := by
    funext y; exact fderiv_add_const c
  have hg : gradient (fun y => h y + c) = gradient h := by
    funext y; unfold gradient; rw [hf]
  rw [s83_generator_decomp, s83_generator_decomp]
  unfold s83_L0 s83_lap
  simp only [hf, hg]

theorem s85_gen_time (a β : ℝ) (ρβ : Euc d → ℝ) (r r' : ℝ) (h : Euc d → ℝ) (x : Euc d) :
    generatorW (critCoeff d a β ρβ) r h x = generatorW (critCoeff d a β ρβ) r' h x := by
  unfold generatorW critCoeff WholeDyn.coeff
  rfl

theorem s85_cl_to_G {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (h : IsClassicalAdjointW C t φ f) : IsAdjointSolutionG (generatorW C) t φ f :=
  ⟨h.c2, h.bdd, h.cont_c2, h.terminal, h.time_deriv, h.cont_time_deriv, h.bdd_time_deriv⟩

theorem s85_G_to_cl {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (h : IsAdjointSolutionG (generatorW C) t φ f) : IsClassicalAdjointW C t φ f :=
  ⟨h.c2, h.bdd, h.cont_c2, h.terminal, h.time_deriv, h.cont_time_deriv, h.bdd_time_deriv⟩

theorem s85_ifd_add_const {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) {j : ℕ} (hj : j ≤ 2) (hj0 : j ≠ 0)
    (x : Euc d) : iteratedFDeriv ℝ j (fun y => f y + c) x = iteratedFDeriv ℝ j f x := by
  have h1 : ContDiffAt ℝ (j : ℕ) f x := hf.contDiffAt.of_le (by exact_mod_cast hj)
  have := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := j) (f := f) (g := fun _ : Euc d => c) (x := x)
    h1 contDiffAt_const
  rw [show (fun y => f y + c) = f + fun _ => c from rfl, this, iteratedFDeriv_const_of_ne hj0 c]
  simp

/-- Adding a `C¹` function of time `κ(r)` to an `IsAdjointSolutionG` and changing the generator. -/
theorem s85_transfer {G G' : ℝ → (Euc d → ℝ) → Euc d → ℝ} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsAdjointSolutionG G t φ f) {κ κ' : ℝ → ℝ}
    (hκ : ContinuousOn κ (Set.Icc 0 t)) (hκ' : ContinuousOn κ' (Set.Icc 0 t))
    (hκd : ∀ r ∈ Set.Ioo 0 t, HasDerivAt κ (κ' r) r)
    (hG : ∀ r ∈ Set.Icc 0 t, ∀ x, G' r (fun y => f r y + κ r) x = G r (f r) x - κ' r) :
    IsAdjointSolutionG G' t (fun y => φ y + κ t) (fun r y => f r y + κ r) := by
  obtain ⟨Bκ, hBκ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hκ
  obtain ⟨Bκ', hBκ'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hκ'
  have hκc : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => κ p.1.1 :=
    hκ.comp_continuous (continuous_subtype_val.comp continuous_fst) (fun p => p.1.2)
  have hκc' : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => κ' p.1.1 :=
    hκ'.comp_continuous (continuous_subtype_val.comp continuous_fst) (fun p => p.1.2)
  refine ⟨fun r hr => (hf.c2 r hr).add contDiff_const, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨B, hB⟩ := hf.bdd j hj
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨B + Bκ, fun r hr x => ?_⟩
      have h1 := hB r hr x
      rw [norm_iteratedFDeriv_zero] at h1 ⊢
      have h2 := hBκ r hr
      calc ‖f r x + κ r‖ ≤ ‖f r x‖ + ‖κ r‖ := norm_add_le _ _
        _ ≤ B + Bκ := add_le_add h1 h2
    · refine ⟨B, fun r hr x => ?_⟩
      rw [s85_ifd_add_const (hf.c2 r hr) (κ r) hj hj0]
      exact hB r hr x
  · intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      have h0 := hf.cont_c2 0 (by norm_num)
      have hc0 : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1.1 p.2 :=
        s84_cont_D0 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1) (x := fun p => p.2) h0
      have hs : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1.1 p.2 + κ p.1.1 := hc0.add hκc
      have : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d =>
          (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm (f p.1.1 p.2 + κ p.1.1) :=
        (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.continuous.comp hs
      refine this.congr fun p => ?_
      rw [iteratedFDeriv_zero_eq_comp]
      rfl
    · refine (hf.cont_c2 j hj).congr fun p => ?_
      exact (s85_ifd_add_const (hf.c2 p.1.1 p.1.2) (κ p.1.1) hj hj0 p.2).symm
  · show (fun y => f t y + κ t) = fun y => φ y + κ t
    rw [hf.terminal]
  · intro x r hr
    have := (hf.time_deriv x r hr).add (hκd r hr)
    have hr' : r ∈ Set.Icc 0 t := ⟨hr.1.le, hr.2.le⟩
    convert this using 1
    rw [hG r hr' x]; ring
  · refine (hf.cont_time_deriv.sub hκc').congr fun p => ?_
    exact (hG p.1.1 p.1.2 p.2).symm
  · obtain ⟨B, hB⟩ := hf.bdd_time_deriv
    refine ⟨max B 0 + max Bκ' 0, fun r hr x => ?_⟩
    rw [hG r hr x]
    have h1 := hB r hr x
    have h2 := hBκ' r hr
    rw [Real.norm_eq_abs] at h2
    have hx : 0 ≤ ‖x‖ := norm_nonneg x
    have h4 : |G r (f r) x - κ' r| ≤ |G r (f r) x| + |κ' r| := abs_sub _ _
    have h5 : |κ' r| ≤ max Bκ' 0 := h2.trans (le_max_left _ _)
    nlinarith [le_max_right B 0, le_max_left B 0, mul_nonneg (le_max_right B 0) hx,
      le_max_right Bκ' 0, mul_nonneg (le_max_right Bκ' 0) hx]

/-- Time shift of an `IsAdjointSolutionG` for a time independent generator. -/
theorem s85_G_shift {G : ℝ → (Euc d → ℝ) → Euc d → ℝ} (hG : ∀ r r' h x, G r h x = G r' h x)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsAdjointSolutionG G (t + s) φ f) : IsAdjointSolutionG G s φ (fun r => f (r + t)) := by
  have hmem : ∀ r ∈ Set.Icc (0 : ℝ) s, r + t ∈ Set.Icc (0 : ℝ) (t + s) := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hmap : Continuous fun p : Set.Icc (0 : ℝ) s × Euc d =>
      ((⟨p.1.1 + t, hmem p.1.1 p.1.2⟩ : Set.Icc (0 : ℝ) (t + s)), p.2) :=
    ((continuous_subtype_val.comp continuous_fst).add continuous_const |>.subtype_mk _).prodMk continuous_snd
  refine ⟨fun r hr => hf.c2 _ (hmem r hr), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨B, hB⟩ := hf.bdd j hj
    exact ⟨B, fun r hr x => hB _ (hmem r hr) x⟩
  · intro j hj
    exact (hf.cont_c2 j hj).comp hmap
  · show f (s + t) = φ
    rw [add_comm s t]; exact hf.terminal
  · intro x r hr
    have h1 : r + t ∈ Set.Ioo (0 : ℝ) (t + s) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have := (hf.time_deriv x (r + t) h1).comp_add_const r t
    simpa [hG r (r + t)] using this
  · have := hf.cont_time_deriv.comp hmap
    refine this.congr fun p => ?_
    simp only [Function.comp]
    exact hG _ _ _ _
  · obtain ⟨B, hB⟩ := hf.bdd_time_deriv
    exact ⟨B, fun r hr x => by rw [hG r (r + t)]; exact hB _ (hmem r hr) x⟩

/-- Restriction to a shorter horizon. -/
theorem s85_G_restrict {G : ℝ → (Euc d → ℝ) → Euc d → ℝ} {T t : ℝ} (htT : t ≤ T) {φ : Euc d → ℝ}
    {f : ℝ → Euc d → ℝ} (hf : IsAdjointSolutionG G T φ f) : IsAdjointSolutionG G t (f t) f := by
  have hmem : ∀ r ∈ Set.Icc (0 : ℝ) t, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans htT⟩
  have hmap : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d =>
      ((⟨p.1.1, hmem p.1.1 p.1.2⟩ : Set.Icc (0 : ℝ) T), p.2) :=
    ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
  refine ⟨fun r hr => hf.c2 r (hmem r hr), ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨B, hB⟩ := hf.bdd j hj
    exact ⟨B, fun r hr x => hB r (hmem r hr) x⟩
  · intro j hj
    exact (hf.cont_c2 j hj).comp hmap
  · intro x r hr
    exact hf.time_deriv x r ⟨hr.1, hr.2.trans_le htT⟩
  · exact hf.cont_time_deriv.comp hmap
  · obtain ⟨B, hB⟩ := hf.bdd_time_deriv
    exact ⟨B, fun r hr x => hB r (hmem r hr) x⟩

theorem s85_cl_wt {M : ℝ} (hM : 0 ≤ M) {C : WholeCoeff d} {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f) : ∃ Φ, Wt M Φ φ := by
  obtain ⟨B, hB⟩ := hf.bdd 0 (by norm_num)
  refine ⟨|B|, fun x => ?_⟩
  have h := hB t ⟨ht, le_rfl⟩ x
  rw [norm_iteratedFDeriv_zero, hf.terminal, Real.norm_eq_abs] at h
  rw [Real.norm_eq_abs]
  have h1 : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s83_one_le_jb x) hM
  calc |φ x| ≤ B := h
    _ ≤ |B| := le_abs_self B
    _ ≤ |B| * jbracket x ^ M := le_mul_of_one_le_right (abs_nonneg B) h1

/-- **Lipschitz dependence of the frozen classical solutions on the datum.** -/
theorem s85_apriori_sub_classical (hd : 2 ≤ d) {a β T M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T)
    (hM : 0 ≤ M) {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t Φ : ℝ} {φ₁ φ₂ : Euc d → ℝ} {f₁ f₂ : ℝ → Euc d → ℝ}, 0 < t → t ≤ T →
      IsClassicalAdjointW (critCoeff d a β ρβ) t φ₁ f₁ → IsClassicalAdjointW (critCoeff d a β ρβ) t φ₂ f₂ →
      Wt M Φ (fun y => φ₁ y - φ₂ y) →
      ∀ r ∈ Set.Icc 0 t, ∀ y : Euc d, |f₁ r y - f₂ r y| ≤ K * Φ * jbracket y ^ M := by
  obtain ⟨K, hK0, hK⟩ := s84_apriori_sub hd ha (inv_pos.2 hβ) hT hM (s84_thermal_gaussReg hd ha hβ hρ)
  refine ⟨K, hK0, fun {t Φ φ₁ φ₂ f₁ f₂} ht htT h₁ h₂ hΦ r hr y => ?_⟩
  obtain ⟨Φ₁, hΦ₁⟩ := s85_cl_wt hM ht.le h₁
  obtain ⟨Φ₂, hΦ₂⟩ := s85_cl_wt hM ht.le h₂
  refine hK ht htT (s84_sol_of_classical a β ha hβ ρβ ht h₁ hΦ₁) (s84_sol_of_classical a β ha hβ ρβ ht h₂ hΦ₂)
    ?_ r hr y
  rw [h₁.terminal, h₂.terminal]
  exact hΦ

/-- **Uniqueness of the frozen classical solutions.** -/
theorem s85_cl_unique (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    {f₁ f₂ : ℝ → Euc d → ℝ} (h₁ : IsClassicalAdjointW (critCoeff d a β ρβ) t φ f₁)
    (h₂ : IsClassicalAdjointW (critCoeff d a β ρβ) t φ f₂) {r : ℝ} (hr : r ∈ Set.Icc 0 t) :
    f₁ r = f₂ r := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    have hr0 : r = 0 := le_antisymm hr.2 hr.1
    subst hr0
    have e1 := h₁.terminal
    have e2 := h₂.terminal
    rw [e1, e2]
  · obtain ⟨K, hK0, hK⟩ := s85_apriori_sub_classical hd ha hβ hpos (M := 0) le_rfl hρ
    funext y
    have := hK (Φ := 0) hpos le_rfl h₁ h₂ (fun y => by simp) r hr y
    have h3 : |f₁ r y - f₂ r y| ≤ 0 := by simpa using this
    have := abs_nonneg (f₁ r y - f₂ r y)
    have h4 : |f₁ r y - f₂ r y| = 0 := le_antisymm h3 this
    exact sub_eq_zero.1 (abs_eq_zero.1 h4)

theorem s85_propagator_eq (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW (critCoeff d a β ρβ) t φ f) {r : ℝ}
    (hr : r ∈ Set.Icc 0 t) : propagatorW (critCoeff d a β ρβ) r t φ = f r := by
  have hex : ∃ f, IsClassicalAdjointW (critCoeff d a β ρβ) t φ f := ⟨f, hf⟩
  unfold propagatorW
  rw [dif_pos hex]
  exact s85_cl_unique hd ha hβ hρ ht hex.choose_spec hf hr

end HRS.MS.Wad
