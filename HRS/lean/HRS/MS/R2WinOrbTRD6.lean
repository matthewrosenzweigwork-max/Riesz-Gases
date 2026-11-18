import HRS.MS.R2WinOrbTRD5

/-!
# S10.3 packet [C], part 6: the O(h) terminal layer

Prefix `s103c_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103c_ftc`: for a classical adjoint solution `f` on `[0,l]`, `f_e(y) - f_l(y) = ∫_e^l L_σ f_σ(y) dσ`.
* `s103c_rho_lip'`: the two-sided time-Lipschitz bound `ρ_σ - ρ_t ∈ U2Dec` with constant `C |σ-t|`.
* `s103c_layer1` (**the layer estimate**): for the datum `ψ ∈ DatD (N0+4)` and a classical adjoint solution `f` with terminal datum `ψ` at `l`, all
  `e < l` and `t ∈ [e,l]`:
  `(f_e - ψ)/(l-e) - L_tψ ∈ Bd N0` with bound `Cl (...) (l-e)`.  Here `(f_e - ψ)/(l-e)` is the terminal datum, at the time `e`, of the
  difference quotient of the orbit (`l = t+h`, `e = t` for `h > 0`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul HRS.MS.Who HRS.MS.BreakdownS67 HRS.MS.MovLin

variable {d : ℕ}

theorem s103c_ftc {s a β : ℝ} {ρ : ℝ → Euc d → ℝ} {t : ℝ} {ψ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t ψ f) {e l : ℝ} (he : 0 ≤ e)
    (hel : e ≤ l) (hlt : l ≤ t) (y : Euc d) :
    f e y - f l y = ∫ σ in e..l, generatorW ((quadraticGradientDyn d s a β).coeff ρ) σ (f σ) y ∧
    IntervalIntegrable (fun σ => generatorW ((quadraticGradientDyn d s a β).coeff ρ) σ (f σ) y) volume e l := by
  have hsub : Set.Icc e l ⊆ Set.Icc (0 : ℝ) t := fun σ hσ => ⟨he.trans hσ.1, hσ.2.trans hlt⟩
  have hwc : ContinuousOn (fun q : ℝ × Euc d => f q.1 q.2) (Set.Icc 0 t ×ˢ Set.univ) :=
    s84_contOn_of_subtype (s84_cont_D0 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1)
      (x := fun p => p.2) (hf.cont_c2 0 (by norm_num)))
  have hGc : ContinuousOn (fun q : ℝ × Euc d =>
      generatorW ((quadraticGradientDyn d s a β).coeff ρ) q.1 (f q.1) q.2) (Set.Icc 0 t ×ˢ Set.univ) :=
    s84_contOn_of_subtype hf.cont_time_deriv
  have hmaps : Set.MapsTo (fun σ : ℝ => (σ, y)) (Set.Icc e l) (Set.Icc 0 t ×ˢ Set.univ) :=
    fun σ hσ => ⟨hsub hσ, Set.mem_univ _⟩
  have hpair : ContinuousOn (fun σ : ℝ => (σ, y)) (Set.Icc e l) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hc1 : ContinuousOn (fun σ => f σ y) (Set.Icc e l) :=
    ContinuousOn.comp (g := fun q : ℝ × Euc d => f q.1 q.2) hwc hpair hmaps
  have hc2' := hGc.comp hpair hmaps
  have hc2 : ContinuousOn (fun σ => generatorW ((quadraticGradientDyn d s a β).coeff ρ) σ (f σ) y)
      (Set.Icc e l) := hc2'
  have hint : IntervalIntegrable (fun σ => generatorW ((quadraticGradientDyn d s a β).coeff ρ) σ (f σ) y)
      volume e l := hc2.intervalIntegrable_of_Icc hel
  refine ⟨?_, hint⟩
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hel hc1
    (f' := fun σ => -(generatorW ((quadraticGradientDyn d s a β).coeff ρ) σ (f σ) y))
    (fun σ hσ => (hf.time_deriv y σ ⟨he.trans_lt hσ.1, hσ.2.trans_le hlt⟩).hasDerivWithinAt) hint.neg
  rw [intervalIntegral.integral_neg] at hftc
  linarith

theorem s103c_U2Dec_neg {K : ℕ} {L A : ℝ} {h : Euc d → ℝ} (hh : U2Dec K L A h) :
    U2Dec K L A (fun y => -h y) := by
  refine ⟨hh.1.neg, fun m hm y => ?_⟩
  have e : (fun y => -h y) = -h := rfl
  rw [e, iteratedFDeriv_neg_apply, norm_neg]
  exact hh.2 m hm y

theorem s103c_rho_lip' {K L : ℕ} {A : ℝ} (hA : 0 ≤ A) {ρ ρ' : ℝ → Euc d → ℝ}
    (hder : ∀ t, 0 ≤ t → ∀ x, HasDerivWithinAt (fun τ => ρ τ x) (ρ' t x) (Set.Ici t) t)
    (hcont : ∀ x, ContinuousOn (fun τ => ρ τ x) (Set.Ici 0))
    (hC : ∀ t, 0 ≤ t → ContDiff ℝ (K : WithTop ℕ∞) (ρ t))
    (hD : ∀ t, 0 ≤ t → U2Dec K (L : ℝ) A (ρ' t)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    U2Dec K (L : ℝ) (((max 1 (d : ℝ)) ^ K * ((5 / 4 : ℝ) ^ L) ^ K) * A * |b - a|) (fun y => ρ b y - ρ a y) := by
  rcases le_total a b with hab | hab
  · rw [abs_of_nonneg (sub_nonneg.2 hab)]
    exact s103c_rho_lip hA hder hcont hC hD ha hab
  · rw [abs_of_nonpos (sub_nonpos.2 hab)]
    have := s103c_U2Dec_neg (s103c_rho_lip hA hder hcont hC hD hb hab)
    have e : (fun y => ρ b y - ρ a y) = fun y => -(ρ a y - ρ b y) := by funext y; ring
    rw [e, show ((max 1 (d : ℝ)) ^ K * ((5 / 4 : ℝ) ^ L) ^ K * A * -(b - a)) =
      (max 1 (d : ℝ)) ^ K * ((5 / 4 : ℝ) ^ L) ^ K * A * (a - b) by ring]
    exact this

theorem s103c_layer1 {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (N0 Lnat : ℕ) (hL : (d : ℝ) + ((N0 + 2 : ℕ) : ℝ) + s + 3 < (Lnat : ℝ)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ (ρ ρ' : ℝ → Euc d → ℝ) (Aρ Ad : ℝ), 0 ≤ Aρ → 0 ≤ Ad →
      (∀ τ, 0 ≤ τ → U2Dec (N0 + 3) (Lnat : ℝ) Aρ (ρ τ)) →
      (∀ τ, 0 ≤ τ → U2Dec (N0 + 1) (Lnat : ℝ) Ad (ρ' τ)) →
      (∀ τ, 0 ≤ τ → ∀ x, HasDerivWithinAt (fun σ => ρ σ x) (ρ' τ x) (Set.Ici τ) τ) →
      (∀ x, ContinuousOn (fun σ => ρ σ x) (Set.Ici 0)) →
      ∀ (ψ : Euc d → ℝ) (Aψ : ℝ), DatD (N0 + 4) Aψ ψ → ∀ (G l : ℝ) (f : ℝ → Euc d → ℝ), l ∈ Set.Icc (0 : ℝ) T →
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) l ψ f →
        (∀ τ ∈ Set.Icc (0 : ℝ) l, ContDiff ℝ ((N0 + 4 : ℕ) : WithTop ℕ∞) (f τ) ∧
          ∀ i, 1 ≤ i → i ≤ N0 + 4 → ∀ y, ‖iteratedFDeriv ℝ i (f τ) y‖ ≤ G) →
        ∀ e t : ℝ, 0 ≤ e → e < l → e ≤ t → t ≤ l →
          Bd N0 (Cl * (Ad * G + (1 + Aρ) * (Aψ + Aρ * G)) * (l - e))
            (fun y => (f e y - ψ y) / (l - e) - generatorW ((quadraticGradientDyn d s a β).coeff ρ) t ψ y) := by
  have hdL : (d : ℝ) < (Lnat : ℝ) := by
    have : (0 : ℝ) ≤ ((N0 + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hL0 : (d : ℝ) + N0 + s + 3 < (Lnat : ℝ) := by
    have : (N0 : ℝ) ≤ ((N0 + 2 : ℕ) : ℝ) := by push_cast; linarith
    linarith
  obtain ⟨KW, hKW0, hKW⟩ := s103c_layer_wt hd hs0 hsd a β ha hβ (N0 + 2) hL T hT
  obtain ⟨KB, hKB0, hKB⟩ := s103c_gen_bd_dec hd hs0 hsd a β ha N0 hL0
  obtain ⟨Cq, hCq0, hCq⟩ := s103b_q_sy hd hs0 hsd N0 hL0
  set Crl : ℝ := (max 1 (d : ℝ)) ^ (N0 + 1) * ((5 / 4 : ℝ) ^ Lnat) ^ (N0 + 1) with hCrl
  have hCrl0 : 0 ≤ Crl := by positivity
  refine ⟨(max 1 (d : ℝ)) ^ N0 * (Cq * Crl + 2 * (KB * KW)), by positivity, ?_⟩
  intro ρ ρ' Aρ Ad hAρ hAd hU hD hder hcont ψ Aψ hψ G l f hl hf hfb e t he hel het htl
  have hAψ : 0 ≤ Aψ := hψ.nonneg
  have hl0 : 0 ≤ l := hl.1
  have hG : 0 ≤ G := by
    have := (hfb l ⟨hl0, le_rfl⟩).2 1 le_rfl (by omega) 0
    exact (norm_nonneg _).trans this
  have hle : 0 < l - e := sub_pos.2 hel
  have hU' : ∀ τ ∈ Set.Icc (0 : ℝ) T, U2Dec (N0 + 2 + 1) (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ => hU τ hτ.1
  have hUm : ∀ τ, 0 ≤ τ → U2Dec (N0 + 1) (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ =>
    ult_U2Dec_mono (hU τ hτ) (by omega)
  have hU1 : ∀ τ, 0 ≤ τ → U2Dec 1 (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ =>
    ult_U2Dec_mono (hU τ hτ) (by omega)
  -- the Lipschitz bound of the density
  have hlip := fun σ (hσ : 0 ≤ σ) => s103c_rho_lip' (K := N0 + 1) (L := Lnat) hAd hder hcont
    (fun τ hτ => (hU τ hτ).1.of_le (by exact_mod_cast (by omega : N0 + 1 ≤ N0 + 3))) hD (a := t) (b := σ) (he.trans het) hσ
  -- the bound of the integrand
  have hg : ∀ σ ∈ Set.Icc e l, Bd N0 ((Cq * Crl * Ad * G + 2 * (KB * KW) * ((1 + Aρ) * (Aψ + Aρ * G))) * (l - e))
      (fun y => (generatorW ((quadraticGradientDyn d s a β).coeff ρ) σ (f σ) y -
        generatorW ((quadraticGradientDyn d s a β).coeff ρ) t ψ y)) := by
    intro σ hσ
    have hσ0 : 0 ≤ σ := he.trans hσ.1
    have hσl : σ ∈ Set.Icc (0 : ℝ) l := ⟨hσ0, hσ.2⟩
    -- the decay of `f_σ - ψ`
    have hW := hKW ρ Aρ hAρ hU' l hl ψ f Aψ G hf (hψ.mono_N (by omega)) hfb σ hσl
    set Ae : ℝ := KW * (Aψ + Aρ * G) * (l - σ) with hAe
    have hAe0 : 0 ≤ Ae := by
      have : 0 ≤ l - σ := sub_nonneg.2 hσ.2
      positivity
    have hecd : ContDiff ℝ ((N0 + 2 : ℕ) : WithTop ℕ∞) (fun y => f σ y - ψ y) :=
      ((hfb σ hσl).1.of_le (by exact_mod_cast (by omega : N0 + 2 ≤ N0 + 4))).sub
        (hψ.1.of_le (by exact_mod_cast (by omega : N0 + 2 ≤ N0 + 4)))
    have hdec : ∀ i, 1 ≤ i → i ≤ N0 + 1 → ∀ y, ‖iteratedFDeriv ℝ i (fun y => f σ y - ψ y) y‖ ≤
        Ae * (1 + ‖y‖)⁻¹ := fun i h1 h2 y => hW i h1 (by omega) y
    have hbd : ∀ i, 1 ≤ i → i ≤ N0 + 2 → ∀ y, ‖iteratedFDeriv ℝ i (fun y => f σ y - ψ y) y‖ ≤ Ae := by
      intro i h1 h2 y
      refine (hW i h1 h2 y).trans ?_
      have : (1 + ‖y‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg y])
      have h3 : 0 ≤ KW * (Aψ + Aρ * G) * (l - σ) := hAe0
      calc KW * (Aψ + Aρ * G) * (l - σ) * (1 + ‖y‖)⁻¹ ≤ KW * (Aψ + Aρ * G) * (l - σ) * 1 :=
            mul_le_mul_of_nonneg_left this h3
        _ = Ae := by rw [mul_one]
    have hT2 := hKB ρ Aρ t hAρ (hUm t (he.trans het)) (fun y => f σ y - ψ y) Ae Ae hecd hdec hbd
    -- the density difference
    have hδ := hlip σ hσ0
    have hδ' : U2Dec (N0 + 1) (Lnat : ℝ) (Crl * Ad * |σ - t|) (fun y => ρ σ y - ρ t y) := by
      have := hδ
      rwa [show (max 1 (d : ℝ)) ^ (N0 + 1) * ((5 / 4 : ℝ) ^ Lnat) ^ (N0 + 1) * Ad * |σ - t| =
        Crl * Ad * |σ - t| by rw [hCrl]] at this
    have hT1 := hCq (Crl * Ad * |σ - t|) (fun y => ρ σ y - ρ t y) (by positivity) hδ' G (f σ)
      ((hfb σ hσl).1.of_le (by exact_mod_cast (by omega : N0 + 2 ≤ N0 + 4)))
      (fun i h1 h2 y => (hfb σ hσl).2 i h1 (by omega) y)
    -- the decomposition
    have hdec' : (fun y => generatorW ((quadraticGradientDyn d s a β).coeff ρ) σ (f σ) y -
        generatorW ((quadraticGradientDyn d s a β).coeff ρ) t ψ y) = fun y =>
        s103bQ d s (fun y => ρ σ y - ρ t y) (f σ) y +
          generatorW ((quadraticGradientDyn d s a β).coeff ρ) t (fun y => f σ y - ψ y) y := by
      funext y
      exact s103c_gen_decomp hd hs0 hsd hdL ρ σ t (hU1 σ hσ0) (hU1 t (he.trans het))
        (B := max G Aψ) ((hfb σ hσl).1.of_le (by exact_mod_cast (by omega : 2 ≤ N0 + 4)))
        (fun i h1 h2 y => ((hfb σ hσl).2 i h1 (by omega) y).trans (le_max_left _ _))
        (hψ.1.of_le (by exact_mod_cast (by omega : 2 ≤ N0 + 4)))
        (fun i h1 h2 y => by
          have := hψ.2.1 i (by omega) y
          exact this.trans (le_max_right _ _)) y
    rw [hdec']
    have hsum := hT1.bd.add hT2
    refine hsum.mono_A ?_
    have hσt : |σ - t| ≤ l - e := by
      rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2]
    have hlσ : l - σ ≤ l - e := by linarith [hσ.1]
    have hlσ0 : 0 ≤ l - σ := sub_nonneg.2 hσ.2
    have h1 : Cq * (Crl * Ad * |σ - t|) * G ≤ Cq * Crl * Ad * G * (l - e) := by
      have : Crl * Ad * |σ - t| ≤ Crl * Ad * (l - e) := mul_le_mul_of_nonneg_left hσt (by positivity)
      calc Cq * (Crl * Ad * |σ - t|) * G ≤ Cq * (Crl * Ad * (l - e)) * G := by gcongr
        _ = _ := by ring
    have h2 : KB * (Ae + (1 + Aρ) * Ae) ≤ 2 * (KB * KW) * ((1 + Aρ) * (Aψ + Aρ * G)) * (l - e) := by
      have hP : 0 ≤ Aψ + Aρ * G := by positivity
      have hAe' : Ae ≤ KW * (Aψ + Aρ * G) * (l - e) := by
        rw [hAe]; exact mul_le_mul_of_nonneg_left hlσ (by positivity)
      calc KB * (Ae + (1 + Aρ) * Ae) = KB * ((2 + Aρ) * Ae - Ae) + KB * Ae * 1 := by ring
        _ ≤ KB * ((2 + Aρ) * Ae) := by nlinarith [mul_nonneg hKB0 hAe0]
        _ ≤ KB * ((2 + Aρ) * (KW * (Aψ + Aρ * G) * (l - e))) := by gcongr
        _ ≤ KB * ((2 * (1 + Aρ)) * (KW * (Aψ + Aρ * G) * (l - e))) := by
            gcongr; nlinarith
        _ = _ := by ring
    nlinarith [h1, h2]
  -- the average
  set B0 : ℝ := Cq * Crl * Ad * G + 2 * (KB * KW) * ((1 + Aρ) * (Aψ + Aρ * G)) with hB0
  have hB00 : 0 ≤ B0 := by positivity
  set Lψ : Euc d → ℝ := generatorW ((quadraticGradientDyn d s a β).coeff ρ) t ψ with hLψ
  have hLψbd : Bd N0 (KB * (Aψ + (1 + Aρ) * Aψ)) Lψ :=
    hKB ρ Aρ t hAρ (hUm t (he.trans het)) ψ Aψ Aψ
      (hψ.1.of_le (by exact_mod_cast (by omega : N0 + 2 ≤ N0 + 4)))
      (fun i h1 h2 y => (hψ.mono_N (by omega : N0 + 2 ≤ N0 + 4)).decay1 i h1 (by omega) y)
      (fun i h1 h2 y => hψ.2.1 i (by omega) y)
  set Gfun : Euc d → ℝ := fun y => (f e y - ψ y) / (l - e) - Lψ y with hGfun
  have hfe : ContDiff ℝ ((N0 + 4 : ℕ) : WithTop ℕ∞) (f e) := (hfb e ⟨he, hel.le⟩).1
  have hGcd : ContDiff ℝ (N0 : WithTop ℕ∞) Gfun := by
    have h1 : ContDiff ℝ (N0 : WithTop ℕ∞) (fun y => (f e y - ψ y) / (l - e)) :=
      ((hfe.of_le (by exact_mod_cast (by omega : N0 ≤ N0 + 4))).sub
        (hψ.1.of_le (by exact_mod_cast (by omega : N0 ≤ N0 + 4)))).div_const _
    exact h1.sub hLψbd.1
  have hints : ∀ y, IntervalIntegrable (fun σ => (l - e)⁻¹ * (generatorW ((quadraticGradientDyn d s a β).coeff ρ) σ (f σ) y -
      Lψ y)) volume e l := fun y =>
    ((s103c_ftc hf he hel.le le_rfl y).2.sub intervalIntegrable_const).const_mul _
  have hGeq : ∀ y, Gfun y = ∫ σ in e..l, (l - e)⁻¹ * (generatorW ((quadraticGradientDyn d s a β).coeff ρ) σ (f σ) y -
      Lψ y) := by
    intro y
    obtain ⟨hF, hI⟩ := s103c_ftc hf he hel.le le_rfl y
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hI intervalIntegrable_const,
      ← hF]
    simp only [intervalIntegral.integral_const, smul_eq_mul, hGfun]
    rw [hf.terminal]
    field_simp
  have hgs : ∀ σ ∈ Set.Icc e l, Bd N0 (B0) (fun y => (l - e)⁻¹ * (generatorW ((quadraticGradientDyn d s a β).coeff ρ) σ (f σ) y -
      Lψ y)) := by
    intro σ hσ
    have := (hg σ hσ).smul ((l - e)⁻¹)
    refine this.mono_A (le_of_eq ?_)
    rw [abs_of_pos (inv_pos.2 hle)]
    field_simp
  have := s103c_avg_bd (N := N0) hel.le hB00 hints hgs hGcd hGeq
  refine this.mono_A ?_
  have hX : 0 ≤ (1 + Aρ) * (Aψ + Aρ * G) := by positivity
  have hAG : 0 ≤ Ad * G := mul_nonneg hAd hG
  have hm : (max 1 (d : ℝ)) ^ N0 ≥ 0 := by positivity
  calc (max 1 (d : ℝ)) ^ N0 * B0 * (l - e) ≤
      (max 1 (d : ℝ)) ^ N0 * (Cq * Crl + 2 * (KB * KW)) * (Ad * G + (1 + Aρ) * (Aψ + Aρ * G)) * (l - e) := by
        refine mul_le_mul_of_nonneg_right ?_ hle.le
        have : B0 ≤ (Cq * Crl + 2 * (KB * KW)) * (Ad * G + (1 + Aρ) * (Aψ + Aρ * G)) := by
          rw [hB0]
          nlinarith [mul_nonneg hCq0 (mul_nonneg hCrl0 hX), mul_nonneg (mul_nonneg hKB0 hKW0) hAG,
            mul_nonneg hCq0 (mul_nonneg hCrl0 hAG)]
        calc (max 1 (d : ℝ)) ^ N0 * B0 ≤ (max 1 (d : ℝ)) ^ N0 * ((Cq * Crl + 2 * (KB * KW)) *
              (Ad * G + (1 + Aρ) * (Aψ + Aρ * G))) := mul_le_mul_of_nonneg_left this hm
          _ = _ := by ring
    _ = _ := by ring

end HRS.MS.R2WinOrbNL

end
