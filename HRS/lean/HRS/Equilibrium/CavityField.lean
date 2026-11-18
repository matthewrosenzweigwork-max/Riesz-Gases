/-
# HRS.Equilibrium.CavityField — the cavity field `v_Y` and the prefactor of the pole marginal

Continuation of `CavityPrefactor.lean` (Lemma 4.6, `R:eq:prefactor`).
-/
import HRS.Equilibrium.CavityPrefactor

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace CavResp

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer

theorem integ_of_lint {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hm : Measurable f) (h0 : ∀ a, 0 ≤ f a) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≤ ENNReal.ofReal C) :
    Integrable f μ ∧ ∫ a, f a ∂μ ≤ C := by
  have hfin : ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hC
  have hi : Integrable f μ :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).2 hfin.lt_top⟩
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hm.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hC).trans (by rw [ENNReal.toReal_ofReal hC0])

theorem rnDeriv_ae_le {μ ν : Measure (Torus d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : ν ≪ μ) {M : ℝ}
    (h : ν ≤ ENNReal.ofReal M • μ) : ∀ᵐ y ∂μ, ν.rnDeriv μ y ≤ ENNReal.ofReal M := by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv _ _) fun A hA _ => ?_
  rw [Measure.setLIntegral_rnDeriv hac]
  calc ν A ≤ (ENNReal.ofReal M • μ) A := h A
    _ = ∫⁻ _ in A, ENNReal.ofReal M ∂μ := by simp [Measure.smul_apply]

theorem alg_bound (L n' a b G : ℝ) (hL : 0 ≤ L) (hn : 0 ≤ n') (hb : 0 ≤ b) (hG : 0 ≤ G) :
    |L * n' * a - L * G - L * n' * b| ≤ L * n' * |a| + L * G + L * n' * b := by
  have h1 : 0 ≤ L * n' * (|a| + a) := mul_nonneg (mul_nonneg hL hn) (by linarith [neg_abs_le a])
  have h2 : 0 ≤ L * n' * (|a| - a) := mul_nonneg (mul_nonneg hL hn) (by linarith [le_abs_self a])
  have h3 := mul_nonneg hL hG
  have h4 := mul_nonneg (mul_nonneg hL hn) hb
  rw [abs_le]; constructor <;> nlinarith

theorem alg_eq (L β n' Nn a b G : ℝ) (hβ : β = L * Nn) (hN : Nn = n' + 1) :
    L * n' * (a + (G - b)) - β * G = L * n' * a - L * G - L * n' * b := by
  rw [hβ, hN]; ring

theorem l1_le_sqrt_var {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ∫ ω, |X ω - ∫ ω', X ω' ∂P| ∂P ≤ Real.sqrt (Var[X; P]) := by
  have hZ : MemLp (fun ω => X ω - ∫ ω', X ω' ∂P) 2 P := hX.sub (memLp_const _)
  have hA : MemLp (fun ω => |X ω - ∫ ω', X ω' ∂P|) 2 P := hZ.abs
  have h1 := variance_nonneg (fun ω => |X ω - ∫ ω', X ω' ∂P|) P
  rw [variance_eq_sub hA] at h1
  have h2 : P[(fun ω => |X ω - ∫ ω', X ω' ∂P|) ^ 2] = Var[X; P] := by
    rw [variance_eq_integral hX.aemeasurable]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp [sq_abs]
  rw [h2] at h1
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  linarith

section Field

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc

theorem gTrunc_bounds (H : ℝ) (hH : 0 ≤ H) (z : Torus d) :
    0 ≤ gTrunc d s c H z ∧ gTrunc d s c H z ≤ H ∧ gTrunc d s c H z ≤ gPlus d s c z := by
  unfold gTrunc
  exact ⟨le_min (hc z) hH, min_le_right _ _, min_le_left _ _⟩

theorem var_trunc :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Torus d,
      ∀ H : ℝ, 2 ≤ H →
      Var[fracF (n := N - 1) (fun z => gTrunc d s c H (y - z));
        poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t] ≤
        Cv * Real.log H / ((N - 1 : ℕ) : ℝ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨C1, hC1, hvar⟩ := PoleCavityAux.pole_variance_clause hd hs0 hsd β hβ ρ hρ
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  obtain ⟨Cc, h1, -, -, -, -, -⟩ := critical_integrals hd hcrit β hβ ρ hρ c hc
  refine ⟨C1 * Real.exp (β * max B 0) * |Cc|, by positivity, fun N hN x t ht y H hH => ?_⟩
  have hgm := measurable_gPlus hd hs0 hsd c
  have hfm : Measurable fun z => gTrunc d s c H (y - z) :=
    (hgm.comp (measurable_const.sub measurable_id)).min measurable_const
  have hfb : ∀ z, |gTrunc d s c H (y - z)| ≤ H := fun z => by
    obtain ⟨a, b, -⟩ := gTrunc_bounds hd hcrit hβ hρ hc H (by linarith) (y - z)
    rwa [abs_of_nonneg a]
  have hv := var_fracF_le hd hs0 hsd hβ hρ hC1 hvar (le_max_right B 0)
    (fun z => (neg_le_neg (le_max_left B 0)).trans (hB z)) hN x ht hfm hfb
  have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - 1)
  have hI : ∫ z, gTrunc d s c H (y - z) ^ 2 ∂(withDensityReal ρ) ≤ |Cc| * Real.log H := by
    have := (integ_of_lint (μ := withDensityReal ρ) (f := fun z => gTrunc d s c H (y - z) ^ 2)
      (hfm.pow_const 2) (fun z => sq_nonneg _) (by positivity)
      ((h1 H hH y).1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) hlog)))).2
    exact this
  refine hv.trans ?_
  have hE := Real.exp_pos (β * max B 0)
  calc C1 * Real.exp (β * max B 0) * (∫ z, gTrunc d s c H (y - z) ^ 2 ∂(withDensityReal ρ)) / ((N - 1 : ℕ) : ℝ)
      ≤ C1 * Real.exp (β * max B 0) * (|Cc| * Real.log H) / ((N - 1 : ℕ) : ℝ) := by
        gcongr
    _ = _ := by ring

theorem gPlus_int (hs0 : 0 ≤ s) (hsd : s < d) (y : Torus d) :
    Integrable (fun z => gPlus d s c (y - z)) (withDensityReal ρ) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  exact (hK.int y).add (integrable_const c)

theorem conv_abs_bound (M : ℝ) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ h : Torus d → ℝ, Measurable h → (∀ y, |h y| ≤ M) →
      ∀ e : ℝ, 0 ≤ e → ∫ y, |h y| ∂(withDensityReal ρ) ≤ e → ∀ x : Torus d,
        ∫ y, gPlus d s c (x - y) * |h y| ∂(withDensityReal ρ) ≤ C' * Real.sqrt e := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨CM, hCM0, hCM⟩ := gplus_abs_conv_small hd hcrit hβ hρ hc M
  obtain ⟨Cg, hCg0, hCg⟩ := conv_gPlus hd hs0 hsd hρ hc
  refine ⟨max CM (|M| * Cg), by positivity, fun h hm hb e he hl x => ?_⟩
  by_cases he1 : e ≤ 1
  · exact (hCM h hm hb e he he1 hl x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  · push_neg at he1
    have hs1 : 1 ≤ Real.sqrt e := by rw [Real.one_le_sqrt]; exact he1.le
    have hgi := gPlus_int hd hcrit hβ hρ hc hs0 hsd x
    calc ∫ y, gPlus d s c (x - y) * |h y| ∂(withDensityReal ρ)
        ≤ ∫ y, |M| * gPlus d s c (x - y) ∂(withDensityReal ρ) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => mul_nonneg (hc _) (abs_nonneg _))
            (hgi.const_mul _) (Eventually.of_forall fun y => ?_)
          have := hb y
          have h2 := hc (x - y)
          calc gPlus d s c (x - y) * |h y| ≤ gPlus d s c (x - y) * |M| :=
                mul_le_mul_of_nonneg_left (this.trans (le_abs_self _)) h2
            _ = _ := by ring
      _ = |M| * convMeasure (gPlus d s c) (withDensityReal ρ) x := by
          rw [integral_const_mul]; rfl
      _ ≤ |M| * Cg := mul_le_mul_of_nonneg_left (hCg x).2 (abs_nonneg _)
      _ ≤ max CM (|M| * Cg) * 1 := by rw [mul_one]; exact le_max_right _ _
      _ ≤ max CM (|M| * Cg) * Real.sqrt e :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)

theorem mean_trunc :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Torus d,
      ∀ H : ℝ, 2 ≤ H →
      |(β / N) * ((N - 1 : ℕ) : ℝ) * ∫ z, gTrunc d s c H (y - z)
          ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) -
        β * convMeasure (gPlus d s c) (withDensityReal ρ) y| ≤
      Cm * (Real.sqrt (deltaN d s N) + 1 / (N : ℝ) + 1 / H) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Ce, hCe0, hCe⟩ := pole_marginal_l1 hd hcrit hβ hρ
  obtain ⟨M1, hM1, hMarg⟩ := pole_marg_le hd hs0 hsd hβ hρ
  obtain ⟨Cg, hCg0, hCg⟩ := conv_gPlus hd hs0 hsd hρ hc
  obtain ⟨Cc, h1, -, -, -, -, -⟩ := critical_integrals hd hcrit β hβ ρ hρ c hc
  obtain ⟨C', hC'0, hC'⟩ := conv_abs_bound hd hcrit hβ hρ hc (M1 + 1)
  refine ⟨β * C' * Real.sqrt Ce + β * Cg + β * |Cc|, by positivity, fun N hN x t ht y H hH => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn : 0 < N - 1 := by omega
  have hlam : 0 ≤ β / N := by positivity
  haveI := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  haveI hνp := isProb_firstMarginal hn (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)
  obtain ⟨hac, hmap⟩ := hMarg N hN x t ht
  have hfm : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) =
      (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
        (fun Y : Config d (N - 1) => Y ⟨0, hn⟩) := by
    unfold firstMarginal; rw [dif_pos hn]
  have hbd : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
      ENNReal.ofReal M1 • withDensityReal ρ := by rw [hfm]; exact hmap ⟨0, hn⟩
  obtain ⟨hqi, hq1, hqeq⟩ := dens_facts hac
  have hqM : ∀ᵐ z ∂(withDensityReal ρ),
      ((firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
        (withDensityReal ρ) z).toReal ≤ M1 := by
    filter_upwards [rnDeriv_ae_le hac hbd] with z hz
    exact ENNReal.toReal_le_of_le_ofReal hM1.le hz
  have hδ0 : 0 ≤ deltaN d s N := (inv_nonneg.2 hN0.le).trans (inv_le_deltaN (d := d) hs0 N (by omega))
  set q : Torus d → ℝ := fun z =>
    ((firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
      (withDensityReal ρ) z).toReal with hq
  have hqm : Measurable q := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hq0 : ∀ z, 0 ≤ q z := fun z => ENNReal.toReal_nonneg
  have hgm := measurable_gPlus hd hs0 hsd c
  have hH0 : 0 ≤ H := by linarith
  set f : Torus d → ℝ := fun z => gTrunc d s c H (y - z) with hf
  have hfm' : Measurable f := (hgm.comp (measurable_const.sub measurable_id)).min measurable_const
  have hf0 : ∀ z, 0 ≤ f z := fun z => (gTrunc_bounds hd hcrit hβ hρ hc H hH0 (y - z)).1
  have hfH : ∀ z, f z ≤ H := fun z => (gTrunc_bounds hd hcrit hβ hρ hc H hH0 (y - z)).2.1
  have hfG : ∀ z, f z ≤ gPlus d s c (y - z) := fun z => (gTrunc_bounds hd hcrit hβ hρ hc H hH0 (y - z)).2.2
  have hfi : Integrable f (withDensityReal ρ) :=
    Integrable.of_bound (C := H) hfm'.aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]; exact hfH z)
  have hGi := gPlus_int hd hcrit hβ hρ hc hs0 hsd y
  have hGm : Measurable fun z => gPlus d s c (y - z) := hgm.comp (measurable_const.sub measurable_id)
  -- the marginal expectation
  have hint : ∫ z, f z ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) =
      ∫ z, q z * f z ∂(withDensityReal ρ) := by
    calc _ = ∫ z, f z ∂((withDensityReal ρ).withDensity fun z => ENNReal.ofReal (q z)) := by
          rw [← hqeq]
      _ = _ := integral_withDensity_real hqm hq0 f
  have hqfi : Integrable (fun z => q z * f z) (withDensityReal ρ) :=
    Integrable.mono' (hqi.mul_const H) (hqm.mul hfm').aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 z) (hf0 z))]
        exact mul_le_mul_of_nonneg_left (hfH z) (hq0 z) |>.trans (by rw [mul_comm]))
  -- the truncation tail
  set r : Torus d → ℝ := fun z => gPlus d s c (y - z) - f z with hr
  have hr0 : ∀ z, 0 ≤ r z := fun z => sub_nonneg.2 (hfG z)
  have hrm : Measurable r := hGm.sub hfm'
  have hH0' : 0 < H := by linarith
  have hrI : ∫ z, r z ∂(withDensityReal ρ) ≤ |Cc| / H := by
    refine (integ_of_lint hrm hr0 (by positivity) ((h1 H hH y).2.trans (ENNReal.ofReal_le_ofReal ?_))).2
    exact div_le_div_of_nonneg_right (le_abs_self _) hH0'.le
  have hrInt : ∫ z, r z ∂(withDensityReal ρ) =
      convMeasure (gPlus d s c) (withDensityReal ρ) y - ∫ z, f z ∂(withDensityReal ρ) := by
    show ∫ z, (gPlus d s c (y - z) - f z) ∂(withDensityReal ρ) = _
    rw [integral_sub hGi hfi]; rfl
  have hr0' : 0 ≤ ∫ z, r z ∂(withDensityReal ρ) := integral_nonneg hr0
  -- the fluctuation part
  have hint1 : Integrable (fun z => (q z - 1) * f z) (withDensityReal ρ) := by
    refine (hqfi.sub hfi).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]; ring
  have hsplit : ∫ z, q z * f z ∂(withDensityReal ρ) =
      ∫ z, (q z - 1) * f z ∂(withDensityReal ρ) + ∫ z, f z ∂(withDensityReal ρ) := by
    rw [← integral_add hint1 hfi]
    exact integral_congr_ae (Eventually.of_forall fun z => by simp only; ring)
  set hh : Torus d → ℝ := fun z => max (-1) (min (q z - 1) M1) with hhdef
  have hhm : Measurable hh := measurable_const.max ((hqm.sub measurable_const).min measurable_const)
  have hhb : ∀ z, |hh z| ≤ M1 + 1 := fun z => by
    rw [abs_le]
    refine ⟨?_, max_le (by linarith) ((min_le_right _ _).trans (by linarith))⟩
    exact (by linarith : -(M1 + 1) ≤ -1).trans (le_max_left _ _)
  have hhq : ∀ᵐ z ∂(withDensityReal ρ), hh z = q z - 1 := by
    filter_upwards [hqM] with z hz
    simp only [hhdef]
    rw [min_eq_left (by linarith), max_eq_right (by linarith [hq0 z])]
  have hab : ∫ z, |hh z| ∂(withDensityReal ρ) ≤ Ce * deltaN d s N := by
    have := hCe N hN x t ht
    refine le_trans (le_of_eq ?_) this
    exact integral_congr_ae (hhq.mono fun z hz => by show |hh z| = |q z - 1|; rw [hz])
  have hCC := hC' hh hhm hhb (Ce * deltaN d s N) (by positivity) hab y
  have hGhh : Integrable (fun z => gPlus d s c (y - z) * |hh z|) (withDensityReal ρ) :=
    Integrable.mono' (hGi.mul_const (M1 + 1)) (hGm.mul hhm.abs).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        have h0 : 0 ≤ gPlus d s c (y - z) * |hh z| := mul_nonneg (hc _) (abs_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        exact mul_le_mul_of_nonneg_left (hhb z) (hc _))
  have ha : |∫ z, (q z - 1) * f z ∂(withDensityReal ρ)| ≤ C' * Real.sqrt (Ce * deltaN d s N) := by
    have e1 : ∫ z, (q z - 1) * f z ∂(withDensityReal ρ) = ∫ z, hh z * f z ∂(withDensityReal ρ) :=
      integral_congr_ae (hhq.mono fun z hz => by show (q z - 1) * f z = hh z * f z; rw [hz])
    rw [e1]
    refine (abs_integral_le_integral_abs).trans ((integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _)
      hGhh (Eventually.of_forall fun z => ?_)).trans hCC)
    show |hh z * f z| ≤ gPlus d s c (y - z) * |hh z|
    rw [abs_mul, abs_of_nonneg (hf0 z), mul_comm]
    exact mul_le_mul_of_nonneg_right (hfG z) (abs_nonneg _)
  rw [Real.sqrt_mul hCe0] at ha
  -- assemble
  have hGI : 0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y := (hCg y).1
  have hGC : convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg := (hCg y).2
  have hn' : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hint, hsplit]
  have hfeq : ∫ z, f z ∂(withDensityReal ρ) =
      convMeasure (gPlus d s c) (withDensityReal ρ) y - ∫ z, r z ∂(withDensityReal ρ) := by
    rw [hrInt]; ring
  rw [hfeq]
  have hkey := alg_eq (β / N) β ((N - 1 : ℕ) : ℝ) (N : ℝ) (∫ z, (q z - 1) * f z ∂(withDensityReal ρ))
    (∫ z, r z ∂(withDensityReal ρ)) (convMeasure (gPlus d s c) (withDensityReal ρ) y)
    (by field_simp) (by rw [hn']; ring)
  rw [hkey]
  refine (alg_bound _ _ _ _ _ hlam (by positivity) hr0' hGI).trans ?_
  have hLn : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [hn', div_mul_eq_mul_div, div_le_iff₀ hN0]; nlinarith
  have hLn0 : 0 ≤ β / N * ((N - 1 : ℕ) : ℝ) := by positivity
  have p1 : β / N * ((N - 1 : ℕ) : ℝ) * |∫ z, (q z - 1) * f z ∂(withDensityReal ρ)| ≤
      β * (C' * (Real.sqrt Ce * Real.sqrt (deltaN d s N))) :=
    mul_le_mul hLn ha (abs_nonneg _) hβ.le
  have p2 : β / N * convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ β * Cg * (1 / (N : ℝ)) := by
    calc _ ≤ β / N * Cg := mul_le_mul_of_nonneg_left hGC hlam
      _ = _ := by ring
  have p3 : β / N * ((N - 1 : ℕ) : ℝ) * ∫ z, r z ∂(withDensityReal ρ) ≤ β * |Cc| * (1 / H) :=
    calc _ ≤ β * (|Cc| / H) := mul_le_mul hLn hrI hr0' hβ.le
      _ = _ := by ring
  have hX := Real.sqrt_nonneg (deltaN d s N)
  have hY : 0 ≤ 1 / (N : ℝ) := by positivity
  have hZ : 0 ≤ 1 / H := by positivity
  have hq1 : 0 ≤ β * C' * Real.sqrt Ce := by positivity
  have hq2 : 0 ≤ β * Cg := by positivity
  have hq3 : 0 ≤ β * |Cc| := by positivity
  nlinarith [mul_nonneg hq1 hY, mul_nonneg hq1 hZ, mul_nonneg hq2 hX, mul_nonneg hq2 hZ,
    mul_nonneg hq3 hX, mul_nonneg hq3 hY]

theorem tail_bound :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Torus d,
      ∀ H : ℝ, 2 ≤ H →
      Integrable (fun Y : Config d (N - 1) => (β / N) * ∑ j, (gPlus d s c (y - Y j) - gTrunc d s c H (y - Y j)))
          (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ∧
        ∫ Y, (β / N) * ∑ j, (gPlus d s c (y - Y j) - gTrunc d s c H (y - Y j))
          ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤ Ct / H := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨M1, hM1, hMarg⟩ := pole_marg_le hd hs0 hsd hβ hρ
  obtain ⟨Cc, h1, -, -, -, -, -⟩ := critical_integrals hd hcrit β hβ ρ hρ c hc
  refine ⟨β * M1 * |Cc|, by positivity, fun N hN x t ht y H hH => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn : 0 < N - 1 := by omega
  have hlam : 0 ≤ β / N := by positivity
  haveI := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  obtain ⟨-, hmap⟩ := hMarg N hN x t ht
  have hgm := measurable_gPlus hd hs0 hsd c
  have hH0 : 0 ≤ H := by linarith
  have hH0' : 0 < H := by linarith
  set r : Torus d → ℝ := fun z => gPlus d s c (y - z) - gTrunc d s c H (y - z) with hr
  have hr0 : ∀ z, 0 ≤ r z := fun z =>
    sub_nonneg.2 (gTrunc_bounds hd hcrit hβ hρ hc H hH0 (y - z)).2.2
  have hrm : Measurable r :=
    (hgm.comp (measurable_const.sub measurable_id)).sub
      ((hgm.comp (measurable_const.sub measurable_id)).min measurable_const)
  have hRm : Measurable fun Y : Config d (N - 1) => (β / N) * ∑ j, r (Y j) :=
    (Finset.measurable_sum _ fun j _ => hrm.comp (measurable_pi_apply j)).const_mul _
  have hR0 : ∀ Y : Config d (N - 1), 0 ≤ (β / N) * ∑ j, r (Y j) := fun Y =>
    mul_nonneg hlam (Finset.sum_nonneg fun j _ => hr0 _)
  have hrint : ∫⁻ z, ENNReal.ofReal (r z) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (|Cc| / H) :=
    (h1 H hH y).2.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_abs_self _) hH0'.le))
  have hlint : ∫⁻ Y, ENNReal.ofReal ((β / N) * ∑ j, r (Y j))
      ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
      ENNReal.ofReal (β * M1 * |Cc| / H) := by
    have e1 : ∀ Y : Config d (N - 1), ENNReal.ofReal ((β / N) * ∑ j, r (Y j)) =
        ∑ j, ENNReal.ofReal ((β / N) * r (Y j)) := fun Y => by
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg hlam (hr0 _)]
    have hφm : Measurable fun z => ENNReal.ofReal ((β / N) * r z) :=
      ENNReal.measurable_ofReal.comp (hrm.const_mul _)
    have e2 : ∀ j : Fin (N - 1), ∫⁻ Y, ENNReal.ofReal ((β / N) * r (Y j))
        ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
        ENNReal.ofReal M1 * (ENNReal.ofReal (β / N) * ENNReal.ofReal (|Cc| / H)) := fun j => by
      rw [← lintegral_map hφm (measurable_pi_apply j)]
      calc _ ≤ ∫⁻ z, ENNReal.ofReal ((β / N) * r z) ∂(ENNReal.ofReal M1 • withDensityReal ρ) :=
            lintegral_mono' (hmap j) le_rfl
        _ = ENNReal.ofReal M1 * ∫⁻ z, ENNReal.ofReal ((β / N) * r z) ∂(withDensityReal ρ) :=
            lintegral_smul_measure _ _
        _ ≤ _ := by
            refine mul_le_mul' le_rfl ?_
            simp_rw [ENNReal.ofReal_mul hlam]
            rw [lintegral_const_mul _ (show Measurable fun z => ENNReal.ofReal (r z) from ENNReal.measurable_ofReal.comp hrm)]
            exact mul_le_mul' le_rfl hrint
    calc _ = ∫⁻ Y, ∑ j, ENNReal.ofReal ((β / N) * r (Y j))
          ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) :=
          lintegral_congr e1
      _ = ∑ j, ∫⁻ Y, ENNReal.ofReal ((β / N) * r (Y j))
          ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) :=
          lintegral_finset_sum _ fun j _ => hφm.comp (measurable_pi_apply j)
      _ ≤ ∑ _j : Fin (N - 1), ENNReal.ofReal M1 * (ENNReal.ofReal (β / N) * ENNReal.ofReal (|Cc| / H)) :=
          Finset.sum_le_sum fun j _ => e2 j
      _ = ENNReal.ofReal (((N - 1 : ℕ) : ℝ) * (M1 * ((β / N) * (|Cc| / H)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_mul hM1.le, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hLn : ((N - 1 : ℕ) : ℝ) * (β / N) ≤ β := by
            have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
            rw [this, mul_div_assoc', div_le_iff₀ hN0]; nlinarith
          have hq : 0 ≤ M1 * (|Cc| / H) := by positivity
          calc ((N - 1 : ℕ) : ℝ) * (M1 * ((β / N) * (|Cc| / H)))
              = (((N - 1 : ℕ) : ℝ) * (β / N)) * (M1 * (|Cc| / H)) := by ring
            _ ≤ β * (M1 * (|Cc| / H)) := mul_le_mul_of_nonneg_right hLn hq
            _ = _ := by ring
  exact integ_of_lint hRm hR0 (by positivity) hlint

theorem small_facts (hs0 : 0 ≤ s) {N : ℕ} (hN : 2 ≤ N) :
    1 / (N : ℝ) ≤ Real.sqrt (deltaN d s N) ∧ 1 / Real.sqrt (N : ℝ) ≤ Real.sqrt (deltaN d s N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hδ : (N : ℝ)⁻¹ ≤ deltaN d s N := inv_le_deltaN (d := d) hs0 N (by omega)
  have h2 : 1 / Real.sqrt (N : ℝ) ≤ Real.sqrt (deltaN d s N) := by
    rw [one_div, ← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt hδ
  refine ⟨?_, h2⟩
  refine le_trans ?_ h2
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.2 hN1
  have hsp : 0 < Real.sqrt (N : ℝ) := by linarith
  refine one_div_le_one_div_of_le hsp ?_
  nlinarith [Real.sq_sqrt hN0.le]

set_option maxHeartbeats 1600000 in
theorem field_L1' :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Torus d,
      Integrable (fun Y => |cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) Y y|)
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ∧
      ∫ Y, |cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) Y y|
        ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
        C * Real.sqrt (deltaN d s N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cv, hCv0, hCv⟩ := var_trunc hd hcrit hβ hρ hc
  obtain ⟨Cm, hCm0, hCm⟩ := mean_trunc hd hcrit hβ hρ hc
  obtain ⟨Ct, hCt0, hCt⟩ := tail_bound hd hcrit hβ hρ hc
  refine ⟨β * Real.sqrt (2 * Cv) + 3 * Cm + 3 * β + Ct, by positivity, fun N hN x t ht y => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : 0 < N - 1 := by omega
  have hn' : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by rw [hn']; linarith
  have hlam : 0 ≤ β / N := by positivity
  haveI := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  have hsq0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 hN0
  set H : ℝ := 2 + Real.sqrt N with hHdef
  have hH2 : 2 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  have hgm := measurable_gPlus hd hs0 hsd c
  set f : Torus d → ℝ := fun z => gTrunc d s c H (y - z) with hf
  have hfm : Measurable f := (hgm.comp (measurable_const.sub measurable_id)).min measurable_const
  have hf0 : ∀ z, 0 ≤ f z := fun z => (gTrunc_bounds hd hcrit hβ hρ hc H hH0.le (y - z)).1
  have hfH : ∀ z, f z ≤ H := fun z => (gTrunc_bounds hd hcrit hβ hρ hc H hH0.le (y - z)).2.1
  have hfb : ∀ z, |f z| ≤ H := fun z => by rw [abs_of_nonneg (hf0 z)]; exact hfH z
  set r : Torus d → ℝ := fun z => gPlus d s c (y - z) - gTrunc d s c H (y - z) with hr
  have hr0 : ∀ z, 0 ≤ r z := fun z => sub_nonneg.2 (gTrunc_bounds hd hcrit hβ hρ hc H hH0.le (y - z)).2.2
  have hGfr : ∀ z, gPlus d s c (y - z) = f z + r z := fun z => by simp only [hf, hr]; ring
  set P := poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t with hP
  set ν := firstMarginal P with hν
  set h := convMeasure (gPlus d s c) (withDensityReal ρ) y with hh
  set EA : ℝ := (β / N) * ((N - 1 : ℕ) : ℝ) * ∫ z, f z ∂ν with hEA
  set A : Config d (N - 1) → ℝ := fun Y => (β / N) * ((N - 1 : ℕ) : ℝ) * fracF f Y with hA
  set R : Config d (N - 1) → ℝ := fun Y => (β / N) * ∑ j, (gPlus d s c (y - Y j) - gTrunc d s c H (y - Y j))
    with hR
  have hrm : Measurable r :=
    (hgm.comp (measurable_const.sub measurable_id)).sub
      ((hgm.comp (measurable_const.sub measurable_id)).min measurable_const)
  -- pointwise bound
  have hpt : ∀ Y : Config d (N - 1), |cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y| ≤
      |A Y - EA| + |EA - β * h| + (β / N) * H + R Y := by
    intro Y
    have e1 : ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), gPlus d s c (y - Y j) =
        (∑ j, f (Y j)) - f (Y ⟨0, hn⟩) + ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) := by
      rw [Finset.sum_congr rfl (fun j _ => hGfr (Y j)), Finset.sum_add_distrib,
        Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    have e2 : A Y = (β / N) * ∑ j, f (Y j) := by
      simp only [hA]; unfold fracF
      have : ((N - 1 : ℕ) : ℝ) ≠ 0 := hn0.ne'
      field_simp
    have e3 : cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y =
        (A Y - EA) + (EA - β * h) - (β / N) * f (Y ⟨0, hn⟩) +
          (β / N) * ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) := by
      unfold cavityField
      rw [e1, ← hh, e2]; ring
    rw [e3]
    have hr1 : 0 ≤ ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) :=
      Finset.sum_nonneg fun j _ => hr0 _
    have hr2 : ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) ≤ ∑ j, r (Y j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ => hr0 _
    have h3 : (β / N) * f (Y ⟨0, hn⟩) ≤ (β / N) * H := mul_le_mul_of_nonneg_left (hfH _) hlam
    have h3' : 0 ≤ (β / N) * f (Y ⟨0, hn⟩) := mul_nonneg hlam (hf0 _)
    have h4 : (β / N) * ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) ≤ R Y :=
      mul_le_mul_of_nonneg_left hr2 hlam
    have h4' : 0 ≤ (β / N) * ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) :=
      mul_nonneg hlam hr1
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (A Y - EA), neg_abs_le (EA - β * h), le_abs_self (A Y - EA),
      le_abs_self (EA - β * h)]
  have hRm : Measurable R :=
    (Finset.measurable_sum _ fun j _ => hrm.comp (measurable_pi_apply j)).const_mul _
  have hRint : Integrable R P := (hCt N hN x t ht y H hH2).1
  have hRle : ∫ Y, R Y ∂P ≤ Ct / H := (hCt N hN x t ht y H hH2).2
  have hR0 : ∀ Y, 0 ≤ R Y := fun Y => mul_nonneg hlam (Finset.sum_nonneg fun j _ => hr0 _)
  have hfrm : Measurable (fracF (n := N - 1) f) := measurable_fracF hfm
  have hmem : MemLp (fracF (n := N - 1) f) 2 P :=
    MemLp.of_bound hfrm.aestronglyMeasurable H (Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs]; exact abs_fracF_le hn hfb Y)
  have hfrint : Integrable (fracF (n := N - 1) f) P := hmem.integrable (by norm_num)
  have hEF : ∫ Y, fracF f Y ∂P = ∫ z, f z ∂ν :=
    integral_fracF hn hfm hfb P (poleLaw_exchangeable hd hs0 hsd β hρ (N - 1) (β / N) hlam x t)
  have hAEA : ∀ Y, A Y - EA = (β / N) * ((N - 1 : ℕ) : ℝ) * (fracF f Y - ∫ Y', fracF f Y' ∂P) := by
    intro Y; rw [hEF]; simp only [hA, hEA]; ring
  have hδ0 : 0 ≤ deltaN d s N := (inv_nonneg.2 hN0.le).trans (inv_le_deltaN (d := d) hs0 N (by omega))
  have hc0 : 0 ≤ (β / N) * ((N - 1 : ℕ) : ℝ) := by positivity
  have hc1 : (β / N) * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [hn', div_mul_eq_mul_div, div_le_iff₀ hN0]; nlinarith
  have hI1 : Integrable (fun Y => |A Y - EA|) P :=
    (((hfrint.const_mul ((β / N) * ((N - 1 : ℕ) : ℝ))).sub (integrable_const EA))).abs
  have hT1 : ∫ Y, |A Y - EA| ∂P ≤ β * Real.sqrt (2 * Cv) * Real.sqrt (deltaN d s N) := by
    have e1 : ∫ Y, |A Y - EA| ∂P =
        (β / N) * ((N - 1 : ℕ) : ℝ) * ∫ Y, |fracF f Y - ∫ Y', fracF f Y' ∂P| ∂P := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun Y => ?_)
      show |A Y - EA| = _
      rw [hAEA Y, abs_mul, abs_of_nonneg hc0]
    have e2 := l1_le_sqrt_var hmem
    have hvar := hCv N hN x t ht y H hH2
    have hlogH : Real.log H ≤ (N : ℝ) * deltaN d s N := by
      have hN1 : 1 ≤ N := by omega
      have h2N : H ≤ 2 * N := by
        have : Real.sqrt N ≤ N := by nlinarith [Real.sq_sqrt hN0.le, Real.sqrt_nonneg (N : ℝ),
          (Real.one_le_sqrt.2 (by exact_mod_cast hN1 : (1 : ℝ) ≤ N))]
        simp only [hHdef]; linarith
      calc Real.log H ≤ Real.log (2 * N) := Real.log_le_log hH0 h2N
        _ = Real.log 2 + Real.log N := Real.log_mul (by norm_num) hN0.ne'
        _ ≤ 1 + Real.log N := by
            have := Real.log_two_lt_d9
            linarith
        _ = _ := (N_mul_deltaN_crit hcrit hN1).symm
    have hvar2 : Var[fracF (n := N - 1) f; P] ≤ 2 * Cv * deltaN d s N := by
      refine hvar.trans ?_
      rw [div_le_iff₀ hn0]
      have h1 : Cv * Real.log H ≤ Cv * ((N : ℝ) * deltaN d s N) := mul_le_mul_of_nonneg_left hlogH hCv0
      have h2 : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by rw [hn']; linarith
      nlinarith [mul_nonneg hCv0 hδ0]
    have e3 : Real.sqrt (Var[fracF (n := N - 1) f; P]) ≤
        Real.sqrt (2 * Cv) * Real.sqrt (deltaN d s N) := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by linarith [hvar2])
    rw [e1]
    calc (β / N) * ((N - 1 : ℕ) : ℝ) * ∫ Y, |fracF f Y - ∫ Y', fracF f Y' ∂P| ∂P
        ≤ β * (Real.sqrt (2 * Cv) * Real.sqrt (deltaN d s N)) :=
          mul_le_mul hc1 (e2.trans e3) (integral_nonneg fun Y => abs_nonneg _) hβ.le
      _ = _ := by ring
  have hvm : Measurable fun Y : Config d (N - 1) =>
      cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y := by
    unfold cavityField
    exact ((Finset.measurable_sum _ fun j _ =>
      hgm.comp (measurable_const.sub (measurable_pi_apply j))).const_mul _).sub measurable_const
  have hvint : Integrable (fun Y => |cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y|) P :=
    Integrable.mono' ((((hI1.add (integrable_const _)).add (integrable_const _)).add hRint))
      hvm.abs.aestronglyMeasurable (Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs, abs_abs]; exact hpt Y)
  refine ⟨hvint, ?_⟩
  have hbd : ∫ Y, |cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y| ∂P ≤
      ∫ Y, (|A Y - EA| + |EA - β * h| + (β / N) * H + R Y) ∂P := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun Y => abs_nonneg _)
      ((((hI1.add (integrable_const _)).add (integrable_const _)).add hRint))
      (Eventually.of_forall hpt)
  have hsumint : ∫ Y, (|A Y - EA| + |EA - β * h| + (β / N) * H + R Y) ∂P =
      ∫ Y, |A Y - EA| ∂P + |EA - β * h| + (β / N) * H + ∫ Y, R Y ∂P := by
    have i2 : Integrable (fun Y => |A Y - EA| + |EA - β * h|) P := hI1.add (integrable_const _)
    have i3 : Integrable (fun Y => |A Y - EA| + |EA - β * h| + (β / N) * H) P :=
      i2.add (integrable_const _)
    rw [integral_add i3 hRint, integral_add i2 (integrable_const _), integral_add hI1 (integrable_const _)]
    simp
  obtain ⟨u1, u2⟩ := small_facts hd hcrit hβ hρ hc hs0 hN
  set u : ℝ := Real.sqrt (deltaN d s N) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hH1 : 1 / H ≤ u := by
    refine le_trans ?_ u2
    refine one_div_le_one_div_of_le hsq0 ?_
    simp only [hHdef]; linarith
  have hmean := hCm N hN x t ht y H hH2
  have hmean' : |EA - β * h| ≤ Cm * (u + 1 / (N : ℝ) + 1 / H) := hmean
  have hLH : (β / N) * H ≤ 3 * β * u := by
    have e1 : (β / N) * H = 2 * β * (1 / (N : ℝ)) + β * (1 / Real.sqrt N) := by
      simp only [hHdef]
      have : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
      field_simp
      nlinarith [this]
    rw [e1]
    linarith only [mul_le_mul_of_nonneg_left u1 hβ.le, mul_le_mul_of_nonneg_left u2 hβ.le]
  have hRu : Ct / H ≤ Ct * u := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hH1 hCt0
  have hmu : Cm * (u + 1 / (N : ℝ) + 1 / H) ≤ 3 * Cm * u := by
    linarith only [mul_le_mul_of_nonneg_left u1 hCm0, mul_le_mul_of_nonneg_left hH1 hCm0]
  calc ∫ Y, |cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y| ∂P
      ≤ _ := hbd
    _ = _ := hsumint
    _ ≤ β * Real.sqrt (2 * Cv) * u + 3 * Cm * u + 3 * β * u + Ct * u := by linarith
    _ = _ := by ring

end Field

end CavResp

end HRS

end
