/-
# HRS.Equilibrium.CavityPsi — the prefactor `E[e^{-v_Y(y)}/Z_Y]` is `1 + O(√δ_N)`

Continuation of `CavityField.lean` (Lemma 4.6, `R:eq:prefactor`).
-/
import HRS.Equilibrium.CavityField

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace CavResp

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer

theorem abs_exp_sub_one_le {M u : ℝ} (hM : 0 ≤ M) (hu : u ≤ M) :
    |Real.exp u - 1| ≤ Real.exp M * |u| := by
  have hEM : 1 ≤ Real.exp M := Real.one_le_exp hM
  by_cases h0 : 0 ≤ u
  · have h1 : 1 ≤ Real.exp u := Real.one_le_exp h0
    rw [abs_of_nonneg (by linarith), abs_of_nonneg h0]
    have h2 := Real.add_one_le_exp (-u)
    have h3 : (1 - u) * Real.exp u ≤ 1 := by
      calc (1 - u) * Real.exp u ≤ Real.exp (-u) * Real.exp u :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have h4 : Real.exp u ≤ Real.exp M := Real.exp_le_exp.2 hu
    nlinarith
  · push_neg at h0
    have h2 := Real.add_one_le_exp u
    have h1 : Real.exp u ≤ 1 := by rw [Real.exp_le_one_iff]; exact h0.le
    rw [abs_of_nonpos (by linarith), abs_of_neg h0]
    nlinarith [abs_nonneg u, neg_nonneg.2 h0.le]

section Psi

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc

theorem gPlus_even (z : Torus d) : gPlus d s c (-z) = gPlus d s c z := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  unfold gPlus
  rw [hK.even]

theorem G_shift_int (z : Torus d) :
    Integrable (fun y' => gPlus d s c (y' - z)) (withDensityReal ρ) ∧
      ∫ y', gPlus d s c (y' - z) ∂(withDensityReal ρ) =
        convMeasure (gPlus d s c) (withDensityReal ρ) z := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have h : ∀ y', gPlus d s c (y' - z) = gPlus d s c (z - y') := fun y' => by
    rw [← gPlus_even hd hcrit hβ hρ hc (z - y'), neg_sub]
  simp_rw [h]
  exact ⟨gPlus_int hd hcrit hβ hρ hc hs0 hsd z, rfl⟩

theorem measurable_field_joint {n : ℕ} (N : ℕ) (i : Fin n) :
    Measurable fun q : Torus d × Config d n => cavityField d s c β ρ N i q.2 q.1 := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  unfold cavityField
  refine ((Finset.measurable_sum _ fun j _ => hgm.comp (measurable_fst.sub
      ((measurable_pi_apply j).comp measurable_snd))).const_mul _).sub
      (((measurable_convMeasure hgm _).comp measurable_fst).const_mul β)

theorem measurable_field_slice {n : ℕ} (N : ℕ) (i : Fin n) (X : Config d n) :
    Measurable fun y' : Torus d => cavityField d s c β ρ N i X y' := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  unfold cavityField
  exact ((Finset.measurable_sum _ fun j _ => hgm.comp (measurable_id.sub measurable_const)).const_mul _).sub
      ((measurable_convMeasure hgm _).const_mul β)

theorem measurable_field_joint' {n : ℕ} (N : ℕ) (i : Fin n) :
    Measurable fun q : Config d n × Torus d => cavityField d s c β ρ N i q.1 q.2 := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  unfold cavityField
  refine ((Finset.measurable_sum _ fun j _ => hgm.comp (measurable_snd.sub
      ((measurable_pi_apply j).comp measurable_fst))).const_mul _).sub
      (((measurable_convMeasure hgm _).comp measurable_snd).const_mul β)

theorem measurable_field_slice_X {n : ℕ} (N : ℕ) (i : Fin n) (y : Torus d) :
    Measurable fun X : Config d n => cavityField d s c β ρ N i X y := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hgm := measurable_gPlus hd hs0 hsd c
  unfold cavityField
  exact ((Finset.measurable_sum _ fun j _ =>
    hgm.comp (measurable_const.sub (measurable_pi_apply j))).const_mul _).sub measurable_const

theorem neg_field_le {Cg : ℝ} (hCg : ∀ y, 0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
      convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg)
    {N : ℕ} (hN : 2 ≤ N) {n : ℕ} (i : Fin n) (X : Config d n) (y : Torus d) :
    -cavityField d s c β ρ N i X y ≤ β * Cg := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have h2 : 0 ≤ (β / N) * ∑ j ∈ Finset.univ.erase i, gPlus d s c (y - X j) :=
    mul_nonneg hlam (Finset.sum_nonneg fun j _ => hc _)
  have h3 : β * convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ β * Cg :=
    mul_le_mul_of_nonneg_left (hCg y).2 hβ.le
  unfold cavityField
  linarith

theorem v_integral {Cg : ℝ} (hCg : ∀ y, 0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
      convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg)
    {N : ℕ} (hN : 2 ≤ N) (X : Config d (N - 1)) (i : Fin (N - 1)) :
    Integrable (fun y' => cavityField d s c β ρ N i X y') (withDensityReal ρ) ∧
    Integrable (fun y' => |cavityField d s c β ρ N i X y'|) (withDensityReal ρ) ∧
      ∫ y', |cavityField d s c β ρ N i X y'| ∂(withDensityReal ρ) ≤ 2 * (β * Cg) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hgm := measurable_gPlus hd hs0 hsd c
  have hhm : Measurable (convMeasure (gPlus d s c) (withDensityReal ρ)) := measurable_convMeasure hgm _
  have hCg0 : 0 ≤ Cg := (hCg 0).1.trans (hCg 0).2
  have hhi : Integrable (convMeasure (gPlus d s c) (withDensityReal ρ)) (withDensityReal ρ) :=
    Integrable.of_bound (C := Cg) hhm.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hCg y).1]; exact (hCg y).2)
  have hSi : Integrable (fun y' => ∑ j ∈ Finset.univ.erase i, gPlus d s c (y' - X j)) (withDensityReal ρ) :=
    integrable_finset_sum _ fun j _ => (G_shift_int hd hcrit hβ hρ hc (X j)).1
  have hvi : Integrable (fun y' => cavityField d s c β ρ N i X y') (withDensityReal ρ) := by
    unfold cavityField
    exact (hSi.const_mul _).sub (hhi.const_mul _)
  have hbound : ∀ y', |cavityField d s c β ρ N i X y'| ≤
      (β / N) * ∑ j ∈ Finset.univ.erase i, gPlus d s c (y' - X j) +
        β * convMeasure (gPlus d s c) (withDensityReal ρ) y' := by
    intro y'
    have h1 : 0 ≤ (β / N) * ∑ j ∈ Finset.univ.erase i, gPlus d s c (y' - X j) :=
      mul_nonneg hlam (Finset.sum_nonneg fun j _ => hc _)
    have h2 : 0 ≤ β * convMeasure (gPlus d s c) (withDensityReal ρ) y' :=
      mul_nonneg hβ.le (hCg y').1
    unfold cavityField
    rw [abs_le]; constructor <;> linarith
  refine ⟨hvi, hvi.abs, ?_⟩
  have hint : Integrable (fun y' => (β / N) * ∑ j ∈ Finset.univ.erase i, gPlus d s c (y' - X j) +
        β * convMeasure (gPlus d s c) (withDensityReal ρ) y') (withDensityReal ρ) :=
    (hSi.const_mul _).add (hhi.const_mul _)
  refine (integral_mono hvi.abs hint hbound).trans ?_
  rw [integral_add (hSi.const_mul _) (hhi.const_mul _), integral_const_mul, integral_const_mul,
    integral_finset_sum _ fun j _ => (G_shift_int hd hcrit hβ hρ hc (X j)).1]
  have e1 : ∀ j ∈ Finset.univ.erase i, ∫ y', gPlus d s c (y' - X j) ∂(withDensityReal ρ) ≤ Cg :=
    fun j _ => by rw [(G_shift_int hd hcrit hβ hρ hc (X j)).2]; exact (hCg _).2
  have e2 : ∑ j ∈ Finset.univ.erase i, ∫ y', gPlus d s c (y' - X j) ∂(withDensityReal ρ) ≤
      ((N - 2 : ℕ) : ℝ) * Cg := by
    calc _ ≤ ∑ _j ∈ Finset.univ.erase i, Cg := Finset.sum_le_sum e1
      _ = _ := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          congr 2
  have e3 : ∫ y', convMeasure (gPlus d s c) (withDensityReal ρ) y' ∂(withDensityReal ρ) ≤ Cg := by
    calc _ ≤ ∫ _y', Cg ∂(withDensityReal ρ) :=
          integral_mono hhi (integrable_const _) fun y => (hCg y).2
      _ = Cg := by simp
  have e4 : (β / N) * (((N - 2 : ℕ) : ℝ) * Cg) ≤ β * Cg := by
    have : ((N - 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N - 2 ≤ N)
    calc (β / N) * (((N - 2 : ℕ) : ℝ) * Cg) ≤ (β / N) * ((N : ℝ) * Cg) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hCg0) hlam
      _ = β * Cg := by field_simp
  have := mul_le_mul_of_nonneg_left e2 hlam
  have := mul_le_mul_of_nonneg_left e3 hβ.le
  linarith

set_option maxHeartbeats 400000 in
theorem Z_bounds {Cg : ℝ} (hCg : ∀ y, 0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
      convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg)
    {N : ℕ} (hN : 2 ≤ N) (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (X : Config d (N - 1)) (i : Fin (N - 1)) (a : Torus d → ℝ)
    (ha : ∀ y', a y' = -(t * (β / N)) * gPlus d s c (x - y') - cavityField d s c β ρ N i X y') :
    (∀ y', a y' ≤ β * Cg) ∧ Integrable a (withDensityReal ρ) ∧
      Integrable (fun y' => |a y'|) (withDensityReal ρ) ∧
      ∫ y', |a y'| ∂(withDensityReal ρ) ≤ (β / N) * Cg + 2 * (β * Cg) ∧
      Real.exp (-(3 * (β * Cg))) ≤ ∫ y', Real.exp (a y') ∂(withDensityReal ρ) ∧
      ∫ y', Real.exp (a y') ∂(withDensityReal ρ) ≤ Real.exp (β * Cg) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hlam1 : β / N ≤ β := by
    rw [div_le_iff₀ hN0]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hgm := measurable_gPlus hd hs0 hsd c
  have hCg0 : 0 ≤ Cg := (hCg 0).1.trans (hCg 0).2
  have htl : 0 ≤ t * (β / N) := mul_nonneg ht.1 hlam
  obtain ⟨hvi, hvai, hvI⟩ := v_integral hd hcrit hβ hρ hc hCg hN X i
  have hGi := gPlus_int hd hcrit hβ hρ hc hs0 hsd x
  have hai : Integrable a (withDensityReal ρ) := by
    have : a = fun y' => -(t * (β / N)) * gPlus d s c (x - y') - cavityField d s c β ρ N i X y' :=
      funext ha
    rw [this]; exact (hGi.const_mul _).sub hvi
  -- upper bound on `a`
  have hup : ∀ y', a y' ≤ β * Cg := by
    intro y'
    rw [ha]
    have h1 : 0 ≤ (t * (β / N)) * gPlus d s c (x - y') := mul_nonneg htl (hc _)
    have h2 : 0 ≤ (β / N) * ∑ j ∈ Finset.univ.erase i, gPlus d s c (y' - X j) :=
      mul_nonneg hlam (Finset.sum_nonneg fun j _ => hc _)
    have h3 : β * convMeasure (gPlus d s c) (withDensityReal ρ) y' ≤ β * Cg :=
      mul_le_mul_of_nonneg_left (hCg y').2 hβ.le
    unfold cavityField
    nlinarith
  have habs : ∫ y', |a y'| ∂(withDensityReal ρ) ≤ (β / N) * Cg + 2 * (β * Cg) := by
    have hint : Integrable (fun y' => (t * (β / N)) * gPlus d s c (x - y') +
        |cavityField d s c β ρ N i X y'|) (withDensityReal ρ) := (hGi.const_mul _).add hvai
    have hle : ∀ y', |a y'| ≤ (t * (β / N)) * gPlus d s c (x - y') +
        |cavityField d s c β ρ N i X y'| := by
      intro y'
      rw [ha]
      have h1 : 0 ≤ (t * (β / N)) * gPlus d s c (x - y') := mul_nonneg htl (hc _)
      calc _ ≤ |-(t * (β / N)) * gPlus d s c (x - y')| + |cavityField d s c β ρ N i X y'| :=
            abs_sub _ _
        _ = _ := by
            rw [neg_mul, abs_neg, abs_of_nonneg h1]
    refine (integral_mono hai.abs hint hle).trans ?_
    rw [integral_add (hGi.const_mul _) hvai, integral_const_mul]
    have e1 : ∫ y', gPlus d s c (x - y') ∂(withDensityReal ρ) ≤ Cg := (hCg x).2
    have e2 : (t * (β / N)) * ∫ y', gPlus d s c (x - y') ∂(withDensityReal ρ) ≤ (β / N) * Cg := by
      have : t * (β / N) ≤ β / N := by nlinarith [ht.1, ht.2]
      calc _ ≤ (β / N) * ∫ y', gPlus d s c (x - y') ∂(withDensityReal ρ) :=
            mul_le_mul_of_nonneg_right this (integral_nonneg fun y' => hc _)
        _ ≤ _ := mul_le_mul_of_nonneg_left e1 hlam
    linarith
  have hamm : Measurable a := by
    have : a = fun y' => -(t * (β / N)) * gPlus d s c (x - y') - cavityField d s c β ρ N i X y' :=
      funext ha
    rw [this]
    exact ((hgm.comp (measurable_const.sub measurable_id)).const_mul _).sub
      (measurable_field_slice hd hcrit hβ hρ hc N i X)
  have hem : Measurable fun y' => Real.exp (a y') := Real.measurable_exp.comp hamm
  have hexpb : ∀ y', ‖Real.exp (a y')‖ ≤ Real.exp (β * Cg) := fun y' => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (hup y')
  have hexpi : Integrable (fun y' => Real.exp (a y')) (withDensityReal ρ) :=
    Integrable.mono' (integrable_const (Real.exp (β * Cg))) hem.aestronglyMeasurable
      (Eventually.of_forall hexpb)
  refine ⟨hup, hai, hai.abs, habs, ?_, ?_⟩
  · -- Jensen via the tangent line
    set abar : ℝ := ∫ y', a y' ∂(withDensityReal ρ) with habar
    have hab : -(3 * (β * Cg)) ≤ abar := by
      have h1 : -∫ y', |a y'| ∂(withDensityReal ρ) ≤ abar := by
        rw [← integral_neg]
        exact integral_mono hai.abs.neg hai (fun y => neg_abs_le _)
      have h2 : (β / N) * Cg ≤ β * Cg := mul_le_mul_of_nonneg_right hlam1 hCg0
      linarith
    have hi1 : Integrable (fun y' => a y' - abar) (withDensityReal ρ) := hai.sub (integrable_const _)
    have hi2 : Integrable (fun y' => 1 + (a y' - abar)) (withDensityReal ρ) :=
      (integrable_const (1 : ℝ)).add hi1
    have hmono : ∫ y', Real.exp abar * (1 + (a y' - abar)) ∂(withDensityReal ρ) ≤
        ∫ y', Real.exp (a y') ∂(withDensityReal ρ) := by
      refine integral_mono (hi2.const_mul _) hexpi fun y => ?_
      have := Real.add_one_le_exp (a y - abar)
      calc Real.exp abar * (1 + (a y - abar)) ≤ Real.exp abar * Real.exp (a y - abar) :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
        _ = Real.exp (a y) := by rw [← Real.exp_add]; congr 1; ring
    have hval : ∫ y', Real.exp abar * (1 + (a y' - abar)) ∂(withDensityReal ρ) = Real.exp abar := by
      rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hi1,
        integral_sub hai (integrable_const _)]
      simp [habar]
    rw [hval] at hmono
    exact (Real.exp_le_exp.2 hab).trans hmono
  · calc ∫ y', Real.exp (a y') ∂(withDensityReal ρ) ≤ ∫ _y', Real.exp (β * Cg) ∂(withDensityReal ρ) :=
          integral_mono hexpi (integrable_const _) fun y => Real.exp_le_exp.2 (hup y)
      _ = _ := by simp

set_option maxHeartbeats 1600000 in
theorem psi_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Torus d,
      |∫ X, Real.exp (-cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) X y) /
          (∫ y', Real.exp (-(t * (β / N)) * gPlus d s c (x - y') -
            cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) X y') ∂(withDensityReal ρ))
          ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) - 1| ≤
        C * Real.sqrt (deltaN d s N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cg, hCg0, hCg⟩ := conv_gPlus hd hs0 hsd hρ hc
  obtain ⟨C1, hC10, hC1⟩ := field_L1' hd hcrit hβ hρ hc
  refine ⟨Real.exp (4 * (β * Cg)) * (2 * C1 + β * Cg), by positivity, fun N hN x t ht y => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn : 0 < N - 1 := by omega
  have hlam : 0 ≤ β / N := by positivity
  haveI := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  obtain ⟨u1, -⟩ := small_facts hd hcrit hβ hρ hc hs0 hN
  have hC1' := hC1 N hN x t ht y
  set u : ℝ := Real.sqrt (deltaN d s N) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hM0 : 0 ≤ β * Cg := by positivity
  set M : ℝ := β * Cg with hM
  set P := poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t with hP
  set V : Config d (N - 1) → Torus d → ℝ := fun X y' =>
    cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) X y' with hV
  have hgm := measurable_gPlus hd hs0 hsd c
  have hVj : Measurable fun q : Config d (N - 1) × Torus d => V q.1 q.2 :=
    measurable_field_joint' hd hcrit hβ hρ hc N ⟨0, hn⟩
  have hVs : ∀ y', Measurable fun X : Config d (N - 1) => V X y' := fun y' =>
    measurable_field_slice_X hd hcrit hβ hρ hc N ⟨0, hn⟩ y'
  have hVv : ∀ X, Integrable (fun y' => V X y') (withDensityReal ρ) ∧
      Integrable (fun y' => |V X y'|) (withDensityReal ρ) ∧
      ∫ y', |V X y'| ∂(withDensityReal ρ) ≤ 2 * M :=
    fun X => v_integral hd hcrit hβ hρ hc hCg hN X ⟨0, hn⟩
  have hZb := fun X : Config d (N - 1) => Z_bounds hd hcrit hβ hρ hc hCg hN x ht X ⟨0, hn⟩
    (fun y' => -(t * (β / N)) * gPlus d s c (x - y') - V X y') (fun y' => rfl)
  -- the normaliser
  obtain ⟨Z, hZdef⟩ : ∃ Z : Config d (N - 1) → ℝ, ∀ X, Z X =
      ∫ y', Real.exp (-(t * (β / N)) * gPlus d s c (x - y') - V X y') ∂(withDensityReal ρ) :=
    ⟨_, fun _ => rfl⟩
  have hZlo : ∀ X, Real.exp (-(3 * M)) ≤ Z X := fun X => by rw [hZdef]; exact (hZb X).2.2.2.2.1
  have hZhi : ∀ X, Z X ≤ Real.exp M := fun X => by rw [hZdef]; exact (hZb X).2.2.2.2.2
  have hZpos : ∀ X, 0 < Z X := fun X => (Real.exp_pos _).trans_le (hZlo X)
  have hAm : Measurable fun q : Config d (N - 1) × Torus d =>
      -(t * (β / N)) * gPlus d s c (x - q.2) - V q.1 q.2 :=
    ((hgm.comp (measurable_const.sub measurable_snd)).const_mul _).sub hVj
  have hZm : Measurable Z := by
    have h1 : StronglyMeasurable fun q : Config d (N - 1) × Torus d =>
        Real.exp (-(t * (β / N)) * gPlus d s c (x - q.2) - V q.1 q.2) :=
      (Real.measurable_exp.comp hAm).stronglyMeasurable
    have h2 := h1.integral_prod_right' (ν := withDensityReal ρ)
    have : Z = fun X => ∫ y', Real.exp (-(t * (β / N)) * gPlus d s c (x - y') - V X y')
        ∂(withDensityReal ρ) := funext hZdef
    rw [this]; exact h2.measurable
  -- the integrand
  obtain ⟨g, hgdef⟩ : ∃ g : Config d (N - 1) → ℝ, ∀ X, g X = Real.exp (-V X y) / Z X :=
    ⟨_, fun _ => rfl⟩
  have hgm' : Measurable g := by
    have : g = fun X => Real.exp (-V X y) / Z X := funext hgdef
    rw [this]; exact (Real.measurable_exp.comp (hVs y).neg).div hZm
  have hnegV : ∀ X, -V X y ≤ M := fun X => neg_field_le hd hcrit hβ hρ hc hCg hN ⟨0, hn⟩ X y
  have hexpV : ∀ X, Real.exp (-V X y) ≤ Real.exp M := fun X => Real.exp_le_exp.2 (hnegV X)
  have hg0 : ∀ X, 0 ≤ g X := fun X => by
    rw [hgdef]; exact div_nonneg (Real.exp_pos _).le (hZpos X).le
  have hgb : ∀ X, g X ≤ Real.exp (4 * M) := fun X => by
    rw [hgdef, div_le_iff₀ (hZpos X)]
    calc Real.exp (-V X y) ≤ Real.exp M := hexpV X
      _ = Real.exp (4 * M) * Real.exp (-(3 * M)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (4 * M) * Z X := mul_le_mul_of_nonneg_left (hZlo X) (Real.exp_pos _).le
  have hgi : Integrable g P :=
    Integrable.of_bound (C := Real.exp (4 * M)) hgm'.aestronglyMeasurable
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 X)]; exact hgb X)
  have hψ : (∫ X, Real.exp (-cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) X y) /
          (∫ y', Real.exp (-(t * (β / N)) * gPlus d s c (x - y') -
            cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) X y') ∂(withDensityReal ρ)) ∂P) =
      ∫ X, g X ∂P := by
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    rw [hgdef, hZdef]
  rw [hψ]
  have hint1 : ∫ X, g X ∂P - 1 = ∫ X, (g X - 1) ∂P := by
    rw [integral_sub hgi (integrable_const _)]; simp
  rw [hint1]
  refine (abs_integral_le_integral_abs).trans ?_
  obtain ⟨W, hWdef⟩ : ∃ W : Config d (N - 1) → ℝ, ∀ X, W X = ∫ y', |V X y'| ∂(withDensityReal ρ) :=
    ⟨_, fun _ => rfl⟩
  have hW0 : ∀ X, 0 ≤ W X := fun X => by rw [hWdef]; exact integral_nonneg fun _ => abs_nonneg _
  have hW2 : ∀ X, W X ≤ 2 * M := fun X => by rw [hWdef]; exact (hVv X).2.2
  have hZ1 : ∀ X, |Z X - 1| ≤ Real.exp M * ((β / N) * Cg + W X) := by
    intro X
    obtain ⟨a, ha⟩ : ∃ a : Torus d → ℝ, ∀ y', a y' =
        -(t * (β / N)) * gPlus d s c (x - y') - V X y' := ⟨_, fun _ => rfl⟩
    obtain ⟨hup, hai, haia, -, -, -⟩ := Z_bounds hd hcrit hβ hρ hc hCg hN x ht X ⟨0, hn⟩ a ha
    have hGi := gPlus_int hd hcrit hβ hρ hc hs0 hsd x
    have hexpi : Integrable (fun y' => Real.exp (a y')) (withDensityReal ρ) :=
      Integrable.mono' (integrable_const (Real.exp M))
        (Real.measurable_exp.comp_aemeasurable hai.aemeasurable).aestronglyMeasurable
        (Eventually.of_forall fun y' => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (hup y'))
    have e1 : Z X - 1 = ∫ y', (Real.exp (a y') - 1) ∂(withDensityReal ρ) := by
      have : Z X = ∫ y', Real.exp (a y') ∂(withDensityReal ρ) := by
        rw [hZdef]; exact integral_congr_ae (Eventually.of_forall fun y' => by
          show Real.exp (-(t * (β / N)) * gPlus d s c (x - y') - V X y') = Real.exp (a y')
          rw [ha])
      rw [this, integral_sub hexpi (integrable_const _)]; simp
    have htl : 0 ≤ t * (β / N) := mul_nonneg ht.1 hlam
    have hle : ∀ y', |Real.exp (a y') - 1| ≤
        Real.exp M * ((t * (β / N)) * gPlus d s c (x - y') + |V X y'|) := by
      intro y'
      refine (abs_exp_sub_one_le hM0 (hup y')).trans
        (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
      rw [ha]
      have h1 : 0 ≤ (t * (β / N)) * gPlus d s c (x - y') := mul_nonneg htl (hc _)
      calc _ ≤ |-(t * (β / N)) * gPlus d s c (x - y')| + |V X y'| := abs_sub _ _
        _ = _ := by rw [neg_mul, abs_neg, abs_of_nonneg h1]
    have hrint : Integrable (fun y' => Real.exp M * ((t * (β / N)) * gPlus d s c (x - y') +
        |V X y'|)) (withDensityReal ρ) :=
      ((hGi.const_mul _).add (hVv X).2.1).const_mul _
    rw [e1]
    refine (abs_integral_le_integral_abs).trans
      ((integral_mono_of_nonneg (Eventually.of_forall fun y' => abs_nonneg _) hrint
        (Eventually.of_forall hle)).trans ?_)
    rw [integral_const_mul, integral_add (hGi.const_mul _) (hVv X).2.1, integral_const_mul,
      ← hWdef X]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have e2 : (t * (β / N)) * ∫ y', gPlus d s c (x - y') ∂(withDensityReal ρ) ≤ (β / N) * Cg := by
      have : t * (β / N) ≤ β / N := by nlinarith [ht.1, ht.2]
      calc _ ≤ (β / N) * ∫ y', gPlus d s c (x - y') ∂(withDensityReal ρ) :=
            mul_le_mul_of_nonneg_right this (integral_nonneg fun y' => hc _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (hCg x).2 hlam
    linarith
  have hpt : ∀ X, |g X - 1| ≤
      Real.exp (3 * M) * (Real.exp M * |V X y| + Real.exp M * ((β / N) * Cg + W X)) := by
    intro X
    have hz := hZpos X
    have e1 : g X - 1 = (Real.exp (-V X y) - Z X) / Z X := by
      rw [hgdef]; field_simp
    rw [e1, abs_div, abs_of_pos hz, div_le_iff₀ hz]
    have h1 : |Real.exp (-V X y) - 1| ≤ Real.exp M * |V X y| := by
      have := abs_exp_sub_one_le hM0 (hnegV X)
      rwa [abs_neg] at this
    have h2 := hZ1 X
    have h3 : |Real.exp (-V X y) - Z X| ≤ |Real.exp (-V X y) - 1| + |Z X - 1| := by
      have := abs_sub_le (Real.exp (-V X y)) 1 (Z X)
      rwa [abs_sub_comm 1 (Z X)] at this
    have hK : 0 ≤ Real.exp M * |V X y| + Real.exp M * ((β / N) * Cg + W X) := by
      have := hW0 X
      positivity
    calc |Real.exp (-V X y) - Z X| ≤ Real.exp M * |V X y| + Real.exp M * ((β / N) * Cg + W X) := by
          linarith
      _ = Real.exp (3 * M) * (Real.exp M * |V X y| + Real.exp M * ((β / N) * Cg + W X)) *
            Real.exp (-(3 * M)) := by
          rw [mul_comm (Real.exp (3 * M)), mul_assoc, ← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hZlo X) (by positivity)
  have hWm : Measurable W := by
    have h1 : StronglyMeasurable fun q : Config d (N - 1) × Torus d => |V q.1 q.2| :=
      hVj.abs.stronglyMeasurable
    have h2 := h1.integral_prod_right' (ν := withDensityReal ρ)
    have : W = fun X => ∫ y', |V X y'| ∂(withDensityReal ρ) := funext hWdef
    rw [this]; exact h2.measurable
  have hWint : Integrable W P :=
    Integrable.of_bound (C := 2 * M) hWm.aestronglyMeasurable (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hW0 X)]; exact hW2 X)
  have hFm : Measurable fun q : Config d (N - 1) × Torus d => |V q.1 q.2| := hVj.abs
  have hFi : Integrable (fun q : Config d (N - 1) × Torus d => |V q.1 q.2|)
      (P.prod (withDensityReal ρ)) := by
    refine (integrable_prod_iff hFm.aestronglyMeasurable).2
      ⟨Eventually.of_forall fun X => (hVv X).2.1, ?_⟩
    have : (fun X => ∫ y', ‖|V X y'|‖ ∂(withDensityReal ρ)) = W := by
      funext X; rw [hWdef]; simp only [Real.norm_eq_abs, abs_abs]
    rw [this]; exact hWint
  have hWP : ∫ X, W X ∂P ≤ C1 * u := by
    have e1 : ∫ X, W X ∂P = ∫ q, |V q.1 q.2| ∂(P.prod (withDensityReal ρ)) := by
      rw [integral_prod _ hFi]
      refine integral_congr_ae (Eventually.of_forall fun X => ?_)
      show W X = ∫ y', |V X y'| ∂(withDensityReal ρ)
      exact hWdef X
    have e2 : ∫ q, |V q.1 q.2| ∂(P.prod (withDensityReal ρ)) =
        ∫ y', ∫ X, |V X y'| ∂P ∂(withDensityReal ρ) := integral_prod_symm _ hFi
    rw [e1, e2]
    calc _ ≤ ∫ _y', C1 * u ∂(withDensityReal ρ) :=
          integral_mono hFi.integral_prod_right (integrable_const _)
            fun y' => (hC1 N hN x t ht y').2
      _ = C1 * u := by simp
  have i1 : Integrable (fun X => Real.exp M * |V X y|) P := hC1'.1.const_mul _
  have i2 : Integrable (fun X => Real.exp M * ((β / N) * Cg + W X)) P :=
    ((integrable_const _).add hWint).const_mul _
  have hBint : Integrable (fun X => Real.exp (3 * M) *
      (Real.exp M * |V X y| + Real.exp M * ((β / N) * Cg + W X))) P := (i1.add i2).const_mul _
  refine (integral_mono_of_nonneg (Eventually.of_forall fun X => abs_nonneg _) hBint
    (Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_add (integrable_const _) hWint]
  simp only [integral_const, probReal_univ, one_smul]
  have hI1 : ∫ X, |V X y| ∂P ≤ C1 * u := hC1'.2
  have hlamC : (β / N) * Cg ≤ M * u := by
    calc (β / N) * Cg = (β * Cg) * (1 / (N : ℝ)) := by ring
      _ ≤ (β * Cg) * u := mul_le_mul_of_nonneg_left u1 hM0
  have hsum : ∫ X, |V X y| ∂P + ((β / N) * Cg + ∫ X, W X ∂P) ≤ (2 * C1 + β * Cg) * u := by
    have : M = β * Cg := rfl
    nlinarith
  have e3 : Real.exp (4 * M) = Real.exp (3 * M) * Real.exp M := by rw [← Real.exp_add]; congr 1; ring
  rw [e3]
  calc Real.exp (3 * M) * (Real.exp M * ∫ X, |V X y| ∂P + Real.exp M * ((β / N) * Cg + ∫ X, W X ∂P))
      = Real.exp (3 * M) * Real.exp M * (∫ X, |V X y| ∂P + ((β / N) * Cg + ∫ X, W X ∂P)) := by ring
    _ ≤ Real.exp (3 * M) * Real.exp M * ((2 * C1 + β * Cg) * u) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring



theorem pole_prefactor :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      firstMarginal (critPole d s c β ρ N x t) ≪ withDensityReal ρ ∧
        ∀ᵐ y ∂(withDensityReal ρ),
          |((firstMarginal (critPole d s c β ρ N x t)).rnDeriv (withDensityReal ρ) y).toReal -
              Real.exp (-(t * (β / N)) * gPlus d s c (x - y))| ≤
            C * Real.sqrt (deltaN d s N) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨C, hC0, hC⟩ := psi_bound hd hcrit hβ hρ hc
  refine ⟨C, hC0, fun N hN x t ht => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  obtain ⟨hac, hae⟩ := critPole_formula hd hs0 hsd β hβ hρ hc m x ht.1
  refine ⟨hac, ?_⟩
  filter_upwards [hae] with y hy
  rw [hy]
  have hψ := hC (m + 2) hN x t ht y
  rw [critPole_eq_poleLaw hd hs0 hsd β hβ hρ hN x t]
  have key : ∀ (E ψ B : ℝ), 0 < E → |ψ - 1| ≤ B → |E * ψ - E| ≤ B * E := fun E ψ B hE h => by
    rw [show E * ψ - E = E * (ψ - 1) by ring, abs_mul, abs_of_pos hE, mul_comm]
    exact mul_le_mul_of_nonneg_right h hE.le
  exact key _ _ _ (Real.exp_pos _) hψ

end Psi

end CavResp

end HRS

end
