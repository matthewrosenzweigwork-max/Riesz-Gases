import HRS.Commutator.Whole.XLIAux15

/-!
# X-LI part 16: the seven-term decomposition of `a_m` and the pointwise bound for `Δ_k J^α (f g)`
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma Pm_two (m : ℤ) (f : SchwartzMap 𝔼 ℂ) (y : 𝔼) :
    Pm (m - 1) f y = Pm (m - 3) f y + Dm (m - 2) f y + Dm (m - 1) f y := by
  have h2 : Pm (m - 1) f y = Pm (m - 1 - 1) f y + Dm (m - 1) f y := by
    rw [Pm_succ (m - 1) f]; rfl
  have h3 : Pm (m - 1 - 1) f y = Pm (m - 1 - 1 - 1) f y + Dm (m - 1 - 1) f y := by
    rw [Pm_succ (m - 1 - 1) f]; rfl
  have e2 : m - 1 - 1 = m - 2 := by ring
  have e3 : m - 1 - 1 - 1 = m - 3 := by ring
  rw [e3, e2] at h3
  rw [e2] at h2
  rw [h2, h3]

lemma Pm_three (m : ℤ) (f : SchwartzMap 𝔼 ℂ) (y : 𝔼) :
    Pm m f y = Pm (m - 3) f y + Dm (m - 2) f y + Dm (m - 1) f y + Dm m f y := by
  have h1 : Pm m f y = Pm (m - 1) f y + Dm m f y := by
    rw [Pm_succ m f]; rfl
  rw [h1, Pm_two]

/-- the seven-term decomposition of `a_m` (as Schwartz functions) -/
lemma aterm_decomp (f g : SchwartzMap 𝔼 ℂ) (m : ℤ) :
    prodS (Dm m f) (Pm m g) + prodS (Pm (m - 1) f) (Dm m g) =
      (prodS (Dm m f) (Pm (m - 3) g) + prodS (Dm m f) (Dm (m - 2) g) +
        prodS (Dm m f) (Dm (m - 1) g) + prodS (Dm m f) (Dm m g)) +
      (prodS (Pm (m - 3) f) (Dm m g) + prodS (Dm (m - 2) f) (Dm m g) +
        prodS (Dm (m - 1) f) (Dm m g)) := by
  ext y
  simp only [SchwartzMap.add_apply, prodS_apply]
  rw [Pm_three m g y, Pm_two m f y]
  ring

lemma aterm_eq_coe (f g : SchwartzMap 𝔼 ℂ) (m : ℤ) :
    aterm f g m = ⇑(prodS (Dm m f) (Pm m g) + prodS (Pm (m - 1) f) (Dm m g)) := by
  funext y
  simp only [aterm, SchwartzMap.add_apply, prodS_apply]

section Bounds

variable (α : ℝ)

lemma cv_aterm_eq (f g : SchwartzMap 𝔼 ℂ) {k : ℤ} (hk : -2 ≤ k) (m : ℤ) (x : 𝔼) :
    cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) (aterm f g m) x =
      (cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) ⇑(prodS (Dm m f) (Pm (m - 3) g)) x +
        cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) ⇑(prodS (Dm m f) (Dm (m - 2) g)) x +
        cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) ⇑(prodS (Dm m f) (Dm (m - 1) g)) x +
        cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) ⇑(prodS (Dm m f) (Dm m g)) x) +
      (cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) ⇑(prodS (Pm (m - 3) f) (Dm m g)) x +
        cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) ⇑(prodS (Dm (m - 2) f) (Dm m g)) x +
        cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) ⇑(prodS (Dm (m - 1) f) (Dm m g)) x) := by
  rw [aterm_eq_coe, aterm_decomp]
  simp only [cv_dK_Ths_add α hk]

/-- vanishing of the output pieces of `a_m` above the frequency `2^{m+2}` -/
lemma cv_aterm_zero (f g : SchwartzMap 𝔼 ℂ) {k m : ℤ} (hk : -2 ≤ k) (hkm : m + 3 ≤ k) (x : 𝔼) :
    cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) (aterm f g m) x = 0 := by
  rw [cv_aterm_eq α f g hk]
  have hA : ∀ (u v : SchwartzMap 𝔼 ℂ), mulS (symR α k) (symR_temperate α k) (prodS u v) x = 0 →
      cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) ⇑(prodS u v) x = 0 := by
    intro u v h
    rw [cv_dK_Ths_apply α hk, h, mul_zero]
  rw [hA _ _ (classA_vanish m k f g (Or.inl hkm) x),
    hA _ _ (classC_vanish m k m (m - 2) le_rfl (by omega) f g hkm x),
    hA _ _ (classC_vanish m k m (m - 1) le_rfl (by omega) f g hkm x),
    hA _ _ (classC_vanish m k m m le_rfl le_rfl f g hkm x),
    hA _ _ (classB_vanish m k f g (Or.inl hkm) x),
    hA _ _ (classC_vanish m k (m - 2) m (by omega) le_rfl f g hkm x),
    hA _ _ (classC_vanish m k (m - 1) m (by omega) le_rfl f g hkm x)]
  simp

lemma Gc_le_Gs (ψ : SchwartzMap 𝔼 ℂ) (m : ℤ) {l : ℤ} (hl : l = m - 3 ∨ l = m - 2 ∨ l = m - 1 ∨ l = m)
    (y : 𝔼) : Gc ψ l y ≤ Gs ψ m y := by
  unfold Gs
  rcases hl with h | h | h | h <;> subst h
  · exact (le_self_add.trans le_self_add).trans le_self_add
  · exact (le_add_self.trans le_self_add).trans le_self_add
  · exact le_add_self.trans le_self_add
  · exact le_add_self

lemma fterm_bound {k m : ℤ} (hm : -2 ≤ m) {AΘ Av : ℝ≥0∞}
    (hΘ : DecK AΘ k (dK (Ths α : ℤ → 𝔼 → ℂ) k)) (hAv : Av ≠ ⊤)
    (f g v : SchwartzMap 𝔼 ℂ) {l : ℤ} (hl : l = m - 3 ∨ l = m - 2 ∨ l = m - 1 ∨ l = m)
    (hv : ∀ y, ‖v y‖ₑ ≤ Av * Gc g l y) (x : 𝔼) :
    ‖cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) ⇑(prodS (Dm m f) v) x‖ₑ ≤
      AΘ * ((ENNReal.ofReal (((2 : ℝ) ^ m) ^ (-α)) * Av) * XX α f g k m x) := by
  have h := term_bound α hΘ (Dm m f) v (a := ENNReal.ofReal (((2 : ℝ) ^ m) ^ (-α))) (b := Av)
    (fun y => ‖Fj α f m y‖ₑ) (Gc g l) (fun y => (enorm_Dm_eq α hm f y).le) hv
    ENNReal.ofReal_ne_top hAv x
  refine h.trans ?_
  refine mul_le_mul_right (mul_le_mul_right ?_ _) _
  exact CvP_mono k (fun y => mul_le_mul_right (Gc_le_Gs g m hl y) _) x

lemma gterm_bound {k m : ℤ} (hm : -2 ≤ m) {AΘ Au : ℝ≥0∞}
    (hΘ : DecK AΘ k (dK (Ths α : ℤ → 𝔼 → ℂ) k)) (hAu : Au ≠ ⊤)
    (f g u : SchwartzMap 𝔼 ℂ) {l : ℤ} (hl : l = m - 3 ∨ l = m - 2 ∨ l = m - 1 ∨ l = m)
    (hu : ∀ y, ‖u y‖ₑ ≤ Au * Gc f l y) (x : 𝔼) :
    ‖cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) ⇑(prodS u (Dm m g)) x‖ₑ ≤
      AΘ * ((Au * ENNReal.ofReal (((2 : ℝ) ^ m) ^ (-α))) * XX α g f k m x) := by
  have h := term_bound α hΘ u (Dm m g) (a := Au) (b := ENNReal.ofReal (((2 : ℝ) ^ m) ^ (-α)))
    (Gc f l) (fun y => ‖Fj α g m y‖ₑ) hu (fun y => (enorm_Dm_eq α hm g y).le)
    hAu ENNReal.ofReal_ne_top x
  refine h.trans ?_
  refine mul_le_mul_right (mul_le_mul_right ?_ _) _
  refine CvP_mono k (fun y => ?_) x
  rw [mul_comm]
  exact mul_le_mul_right (Gc_le_Gs f m hl y) _

lemma enorm_add3_le (a b c : ℂ) : ‖a + b + c‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ := by
  refine (enorm_add_le _ _).trans ?_
  gcongr
  exact enorm_add_le _ _

lemma enorm_add4_le (a b c d : ℂ) : ‖a + b + c + d‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ + ‖d‖ₑ := by
  refine (enorm_add_le _ _).trans ?_
  gcongr
  exact enorm_add3_le _ _ _

lemma cv_aterm_bound {k m : ℤ} (hk : 0 ≤ k) (hkm : k ≤ m + 2) {AΘ Ac Aρ : ℝ≥0∞}
    (hΘ : DecK AΘ k (dK (Ths α : ℤ → 𝔼 → ℂ) k))
    (hc : ∀ j, DecK Ac j (symK (cutC : 𝔼 → ℂ) j)) (hρ : ∀ j, DecK Aρ j (symK (rho : 𝔼 → ℂ) j))
    (hAc : Ac ≠ ⊤) (hAρ : Aρ ≠ ⊤) (f g : SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    ‖cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) (aterm f g m) x‖ₑ ≤
      (4 * (AΘ * (Ac + Aρ))) * ENNReal.ofReal (((2 : ℝ) ^ m) ^ (-α)) *
        (XX α f g k m x + XX α g f k m x) := by
  have hm : -2 ≤ m := by omega
  rw [cv_aterm_eq α f g (by omega) m x]
  have hle1 : Ac ≤ Ac + Aρ := le_self_add
  have hle2 : Aρ ≤ Ac + Aρ := le_add_self
  have ex : ∀ (c a X : ℝ≥0∞), a ≤ Ac + Aρ →
      AΘ * ((c * a) * X) ≤ (AΘ * (c * (Ac + Aρ))) * X := by
    intro c a X ha
    calc AΘ * ((c * a) * X) ≤ AΘ * ((c * (Ac + Aρ)) * X) := by gcongr
      _ = _ := by ring
  have ex' : ∀ (c a X : ℝ≥0∞), a ≤ Ac + Aρ →
      AΘ * ((a * c) * X) ≤ (AΘ * (c * (Ac + Aρ))) * X := by
    intro c a X ha
    rw [mul_comm a c]
    exact ex c a X ha
  have b1 := (fterm_bound α hm hΘ hAc f g (Pm (m - 3) g) (l := m - 3) (Or.inl rfl)
      (fun y => enorm_Pm_le (hc _) g y) x).trans (ex _ _ _ hle1)
  have b2 := (fterm_bound α hm hΘ hAρ f g (Dm (m - 2) g) (l := m - 2) (Or.inr (Or.inl rfl))
      (fun y => enorm_Dm_le (hρ _) g y) x).trans (ex _ _ _ hle2)
  have b3 := (fterm_bound α hm hΘ hAρ f g (Dm (m - 1) g) (l := m - 1)
      (Or.inr (Or.inr (Or.inl rfl))) (fun y => enorm_Dm_le (hρ _) g y) x).trans (ex _ _ _ hle2)
  have b4 := (fterm_bound α hm hΘ hAρ f g (Dm m g) (l := m)
      (Or.inr (Or.inr (Or.inr rfl))) (fun y => enorm_Dm_le (hρ _) g y) x).trans (ex _ _ _ hle2)
  have b5 := (gterm_bound α hm hΘ hAc f g (Pm (m - 3) f) (l := m - 3) (Or.inl rfl)
      (fun y => enorm_Pm_le (hc _) f y) x).trans (ex' _ _ _ hle1)
  have b6 := (gterm_bound α hm hΘ hAρ f g (Dm (m - 2) f) (l := m - 2) (Or.inr (Or.inl rfl))
      (fun y => enorm_Dm_le (hρ _) f y) x).trans (ex' _ _ _ hle2)
  have b7 := (gterm_bound α hm hΘ hAρ f g (Dm (m - 1) f) (l := m - 1)
      (Or.inr (Or.inr (Or.inl rfl))) (fun y => enorm_Dm_le (hρ _) f y) x).trans (ex' _ _ _ hle2)
  set L : ℝ≥0∞ := AΘ * (ENNReal.ofReal (((2 : ℝ) ^ m) ^ (-α)) * (Ac + Aρ)) with hL
  set X1 := XX α f g k m x with hX1
  set X2 := XX α g f k m x with hX2
  calc _ ≤ (L * X1 + L * X1 + L * X1 + L * X1) + (L * X2 + L * X2 + L * X2) := by
        refine (enorm_add_le _ _).trans (add_le_add ((enorm_add4_le _ _ _ _).trans ?_)
          ((enorm_add3_le _ _ _).trans ?_))
        · exact add_le_add (add_le_add (add_le_add b1 b2) b3) b4
        · exact add_le_add (add_le_add b5 b6) b7
    _ = 4 * L * X1 + 3 * L * X2 := by ring
    _ ≤ 4 * L * X1 + 4 * L * X2 := by
        gcongr
        norm_num
    _ = _ := by rw [hL]; ring

/-- the weight `2^{-nα}` for `n ≥ -2` -/
def wgt (n : ℤ) : ℝ≥0∞ := if -2 ≤ n then ENNReal.ofReal (((2 : ℝ) ^ n) ^ (-α)) else 0

/-- the majorant of the output piece at frequency `2^k` -/
def YY (φ ψ : SchwartzMap 𝔼 ℂ) (k : ℤ) (x : 𝔼) : ℝ≥0∞ :=
  ∑' n : ℤ, wgt α n * XX α φ ψ k (k + n) x

lemma rpow_shift (k n : ℤ) :
    ENNReal.ofReal (((2 : ℝ) ^ k) ^ α) * ENNReal.ofReal (((2 : ℝ) ^ (k + n)) ^ (-α)) =
      ENNReal.ofReal (((2 : ℝ) ^ n) ^ (-α)) := by
  have hk : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hn : 0 < (2 : ℝ) ^ n := zpow_pos (by norm_num) n
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hk.le _)]
  congr 1
  rw [zpow_add₀ (by norm_num), Real.mul_rpow hk.le hn.le, ← mul_assoc, ← Real.rpow_add hk]
  simp

lemma PB [Nontrivial 𝔼] : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (f g : SchwartzMap 𝔼 ℂ) (k : ℤ), 1 ≤ k → ∀ x : 𝔼,
    ‖cv (symK rho k) ⇑(Fm α (prodS f g)) x‖ₑ ≤ C * (YY α f g k x + YY α g f k x) := by
  obtain ⟨AΘ, hAΘ, hdecΘ⟩ := dK_dec (symFam_Ths (d := d) α)
  obtain ⟨Ac, hAc, hdecc⟩ := symK_dec (d := d) cutC_contDiff cutC_cs
  obtain ⟨Aρ, hAρ, hdecρ⟩ := symK_dec (d := d) rho_contDiff rho_cs
  set C₀ : ℝ≥0∞ := 4 * (AΘ * (Ac + Aρ)) with hC₀
  have hC₀' : C₀ ≠ ⊤ := ENNReal.mul_ne_top (by simp)
    (ENNReal.mul_ne_top hAΘ (ENNReal.add_ne_top.2 ⟨hAc, hAρ⟩))
  refine ⟨C₀, hC₀', fun f g k hk x => ?_⟩
  have hk2 : -2 ≤ k := by omega
  have hpos : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hr : ‖((((2 : ℝ) ^ k) ^ α : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (((2 : ℝ) ^ k) ^ α) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)]
  have h1 : ‖cv (symK rho k) ⇑(Fm α (prodS f g)) x‖ₑ =
      ENNReal.ofReal (((2 : ℝ) ^ k) ^ α) *
        ‖cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) ⇑(prodS f g) x‖ₑ := by
    unfold Fm
    rw [delta_bessel_eq α hk2 (prodS f g) x, enorm_mul, hr]
  have h2 : ‖cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) ⇑(prodS f g) x‖ₑ ≤
      ∑' m : ℤ, ‖cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) (aterm f g m) x‖ₑ := by
    have e : ⇑(prodS f g) = fun y => f y * g y := funext (prodS_apply f g)
    rw [e]
    exact cv_fg_le_tsum (dK_integrable (symFam_Ths (d := d) α) k)
      (dK_continuous (symFam_Ths (d := d) α) k).measurable f g x
  have h3 : ∀ m : ℤ, ‖cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) (aterm f g m) x‖ₑ ≤
      if k ≤ m + 2 then C₀ * ENNReal.ofReal (((2 : ℝ) ^ m) ^ (-α)) *
        (XX α f g k m x + XX α g f k m x) else 0 := by
    intro m
    split_ifs with h
    · exact cv_aterm_bound α (by omega) h (hdecΘ k) hdecc hdecρ hAc hAρ f g x
    · push Not at h
      rw [cv_aterm_zero α f g hk2 (by omega) x]; simp
  have key : ∀ n : ℤ, ENNReal.ofReal (((2 : ℝ) ^ k) ^ α) *
      (if k ≤ (k + n) + 2 then C₀ * ENNReal.ofReal (((2 : ℝ) ^ (k + n)) ^ (-α)) *
        (XX α f g k (k + n) x + XX α g f k (k + n) x) else 0) =
      C₀ * (wgt α n * XX α f g k (k + n) x + wgt α n * XX α g f k (k + n) x) := by
    intro n
    by_cases hn : -2 ≤ n
    · have hc : k ≤ (k + n) + 2 := by omega
      rw [if_pos hc]
      unfold wgt
      rw [if_pos hn, ← rpow_shift α k n]
      ring
    · have hc : ¬ k ≤ (k + n) + 2 := by omega
      rw [if_neg hc]
      unfold wgt
      rw [if_neg hn]
      simp
  calc ‖cv (symK rho k) ⇑(Fm α (prodS f g)) x‖ₑ
      ≤ ENNReal.ofReal (((2 : ℝ) ^ k) ^ α) *
        ∑' m : ℤ, (if k ≤ m + 2 then C₀ * ENNReal.ofReal (((2 : ℝ) ^ m) ^ (-α)) *
          (XX α f g k m x + XX α g f k m x) else 0) := by
        rw [h1]
        exact mul_le_mul_right (h2.trans (ENNReal.tsum_le_tsum h3)) _
    _ = ENNReal.ofReal (((2 : ℝ) ^ k) ^ α) *
        ∑' n : ℤ, (if k ≤ (k + n) + 2 then C₀ * ENNReal.ofReal (((2 : ℝ) ^ (k + n)) ^ (-α)) *
          (XX α f g k (k + n) x + XX α g f k (k + n) x) else 0) := by
        congr 1
        exact ((Equiv.addLeft k).tsum_eq (fun m : ℤ => if k ≤ m + 2 then
          C₀ * ENNReal.ofReal (((2 : ℝ) ^ m) ^ (-α)) *
            (XX α f g k m x + XX α g f k m x) else 0)).symm
    _ = ∑' n : ℤ, C₀ * (wgt α n * XX α f g k (k + n) x + wgt α n * XX α g f k (k + n) x) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr key
    _ = C₀ * (YY α f g k x + YY α g f k x) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
        rfl

end Bounds

end HRS.Commutator.Whole.XLI
