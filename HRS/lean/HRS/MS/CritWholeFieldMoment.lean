import HRS.MS.CritWholeRows
import HRS.MS.CritWholePoleCmp

/-!
# S8.1 XS, TT05 (part 1): `L^{4q}(μ^n)` moment of the truncated conditional field, uniformly in `y`

Whole-space port of the torus `HRS.TaylorAux.taylor_field_moment`: the centered capped row is a bounded iid sum
(`taylor_bernstein_pi`); its variance is `≤ C log H` and the deterministic mean error is `O(H⁻¹ + N⁻¹)` by TT01.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr HRS.TaylorAux

namespace HRS.Whole.S81b

variable {d : ℕ}

theorem s81b_pow_sum (a e : ℝ) (q : ℕ) (hq : 1 ≤ q) :
    (a + e) ^ (4 * q) ≤ 2 ^ (4 * q - 1) * (a ^ (4 * q) + e ^ (4 * q)) :=
  taylor_pow_sum a e q hq

set_option maxHeartbeats 1600000 in
theorem s81b_field_moment (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) (q : ℕ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N → ∀ H : ℝ, 2 ≤ H → ∀ i : Fin (N - 1), ∀ y : Euc d,
      ∫ Y, (fieldH D N i H Y y) ^ (4 * q) ∂(product D (N - 1)) ≤
        C * (Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2) ^ (2 * q) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < ((d : ℝ) / 2) := by linarith
  have hsd : ((d : ℝ) / 2) < d := by linarith
  obtain ⟨C2, hC20, hC2⟩ := s81b_critical_truncation_rows hd M
  set Ch : ℝ := max (potentialBound d ((d : ℝ) / 2) M) 0 with hChdef
  have hCh0 : 0 ≤ Ch := le_max_right _ _
  set c1 : ℝ := βp ^ 2 * (C2 + 1) with hc1
  set c2 : ℝ := 8 * βp ^ 2 * (C2 ^ 2 + Ch ^ 2) with hc2
  have hβp : 0 < βp := hβm.trans_le hβ
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  refine ⟨2 ^ (4 * q - 1) * (taylor_kb (2 * q) * c1 ^ (2 * q) + c2 ^ (2 * q)), by
    have := taylor_kb_one_le (2 * q); positivity, fun D N hN H hH i y => ?_⟩
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hββp : D.beta ≤ βp := D.beta_mem.2
  have hββ2 : D.beta ^ 2 ≤ βp ^ 2 := pow_le_pow_left₀ hβ0.le hββp 2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hH0 : 0 < H := by linarith
  have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hprob : IsProbabilityMeasure (mu D) := Q34.isProbabilityMeasure_nu D.prob
  have hkern : ∀ z : Euc d, 0 ≤ critG d z := fun z => by
    rw [critG, Q34.rieszKernel_eq hs0.ne']; exact Real.rpow_nonneg (norm_nonneg _) _
  have hCh : ∀ y, Integrable (fun a => critG d (y - a)) (mu D) ∧ 0 ≤ convMeasure (critG d) (mu D) y ∧
      convMeasure (critG d) (mu D) y ≤ Ch := fun y => by
    obtain ⟨h1, h2, h3⟩ := wr13a_potential_bound hd1 hs0 hsd D.prob D.bound y
    exact ⟨h1, h2, h3.trans (le_max_left _ _)⟩
  set μ : Measure (Euc d) := mu D with hμdef
  set Pm : Measure (EucConfig d (N - 1)) := product D (N - 1) with hPm
  set J : Finset (Fin (N - 1)) := Finset.univ.erase i with hJ
  have hJcard : (J.card : ℝ) = N - 2 := by
    rw [hJ, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  set mH : ℝ := ∫ a, truncKernel d ((d : ℝ) / 2) H (y - a) ∂μ with hmH
  set f : Euc d → ℝ := fun a => truncKernel d ((d : ℝ) / 2) H (y - a) - mH with hf
  have hgm : Measurable fun a => truncKernel d ((d : ℝ) / 2) H (y - a) :=
    ((Q34.measurable_rieszKernel hs0.ne').min measurable_const).comp (measurable_const.sub measurable_id)
  have hg0 : ∀ a, 0 ≤ truncKernel d ((d : ℝ) / 2) H (y - a) := fun a => le_min (hkern _) (by linarith)
  have hgH : ∀ a, truncKernel d ((d : ℝ) / 2) H (y - a) ≤ H := fun a => min_le_right _ _
  have hgint : Integrable (fun a => truncKernel d ((d : ℝ) / 2) H (y - a)) μ :=
    taylor_integrable_of_bdd hgm (B := H) fun a => by rw [abs_of_nonneg (hg0 a)]; exact hgH a
  have hmH0 : 0 ≤ mH := integral_nonneg hg0
  have hmHH : mH ≤ H := by
    calc mH ≤ ∫ a, H ∂μ := integral_mono hgint (integrable_const _) hgH
      _ = H := by simp
  have hfm : Measurable f := hgm.sub_const _
  have hfb : ∀ a, |f a| ≤ H := fun a => by
    rw [abs_le]; constructor <;> simp only [hf] <;> linarith [hg0 a, hgH a]
  have hf0 : ∫ a, f a ∂μ = 0 := by
    simp only [hf]
    rw [integral_sub hgint (integrable_const _)]; simp [hmH]
  obtain ⟨hTailI, hSqI, hTail, hSq⟩ := hC2 D.rho D.prob D.bound H hH y
  have hfv : ∫ a, f a ^ 2 ∂μ ≤ C2 * Real.log H := by
    have h1 : ∫ a, f a ^ 2 ∂μ = ∫ a, truncKernel d ((d : ℝ) / 2) H (y - a) ^ 2 ∂μ - mH ^ 2 := by
      have e : ∀ a, f a ^ 2 = truncKernel d ((d : ℝ) / 2) H (y - a) ^ 2 -
          2 * mH * truncKernel d ((d : ℝ) / 2) H (y - a) + mH ^ 2 := fun a => by simp only [hf]; ring
      have hlin : Integrable (fun a => 2 * mH * truncKernel d ((d : ℝ) / 2) H (y - a)) μ := hgint.const_mul _
      have hsub : Integrable (fun a => truncKernel d ((d : ℝ) / 2) H (y - a) ^ 2 -
          2 * mH * truncKernel d ((d : ℝ) / 2) H (y - a)) μ := hSqI.sub hlin
      simp_rw [e]
      rw [integral_add hsub (integrable_const _), integral_sub hSqI hlin, integral_const_mul]
      simp [hmH]; ring
    rw [h1]
    exact (sub_le_self _ (sq_nonneg _)).trans hSq
  have hbern := taylor_bernstein_pi μ (N - 1) f hfm (M := H) (σ2 := C2 * Real.log H) hH0
    (mul_nonneg hC20 hlog) hfb hf0 hfv (2 * q) J
  set S : EucConfig d (N - 1) → ℝ := fun Y => ∑ j ∈ J, f (Y j) with hS
  set lam : ℝ := D.beta / N with hlam
  set hy : ℝ := convMeasure (critG d) μ y with hhy
  set e : ℝ := lam * J.card * mH - D.beta * hy with he
  have hfield : ∀ Y, fieldH D N i H Y y = lam * S Y + e := by
    intro Y
    simp only [fieldH, hS, hf, he]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← hJ]
    ring
  have hhy_int : Integrable (fun a => critG d (y - a)) μ := (hCh y).1
  have hdH : hy - mH = ∫ a, tailG d H (y - a) ∂μ := by
    simp only [hhy, hmH, convMeasure, tailG]
    rw [integral_sub hhy_int hgint]
  have hdH0 : 0 ≤ hy - mH := by
    rw [hdH]; exact integral_nonneg fun a => by
      show (0 : ℝ) ≤ tailG d H (y - a)
      simp only [tailG, truncKernel, critG]; linarith [min_le_left (rieszKernel d ((d : ℝ) / 2) (y - a)) H]
  have hdH1 : hy - mH ≤ C2 / H := by rw [hdH]; exact hTail
  have hhyCh : hy ≤ Ch := (hCh y).2.2
  have he_eq : e = -(D.beta * (hy - mH)) - (2 * D.beta / N) * mH := by
    simp only [he, hlam]
    have : (J.card : ℝ) = N - 2 := hJcard
    rw [this]; field_simp; ring
  have hebound : e ^ 2 ≤ c2 * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2) := by
    have h1 : |e| ≤ D.beta * (C2 / H) + 2 * D.beta / N * Ch := by
      rw [he_eq, abs_le]; constructor
      · have : D.beta * (hy - mH) ≤ D.beta * (C2 / H) := mul_le_mul_of_nonneg_left hdH1 hβ0.le
        have : 2 * D.beta / N * mH ≤ 2 * D.beta / N * Ch :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have : 0 ≤ 2 * D.beta / N * mH := by positivity
        have : 0 ≤ D.beta * (hy - mH) := mul_nonneg hβ0.le hdH0
        linarith
      · have : 0 ≤ D.beta * (hy - mH) := mul_nonneg hβ0.le hdH0
        have : 0 ≤ 2 * D.beta / N * mH := by positivity
        have : 0 ≤ D.beta * (C2 / H) := by positivity
        have : 0 ≤ 2 * D.beta / N * Ch := by positivity
        linarith
    have h2 : e ^ 2 ≤ (D.beta * (C2 / H) + 2 * D.beta / N * Ch) ^ 2 := by
      rw [← sq_abs e]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h2.trans ?_
    have h3 : (D.beta * (C2 / H) + 2 * D.beta / N * Ch) ^ 2 ≤
        2 * (D.beta * (C2 / H)) ^ 2 + 2 * (2 * D.beta / N * Ch) ^ 2 := by
      nlinarith [sq_nonneg (D.beta * (C2 / H) - 2 * D.beta / N * Ch)]
    refine h3.trans ?_
    have e1 : 2 * (D.beta * (C2 / H)) ^ 2 = 2 * D.beta ^ 2 * C2 ^ 2 * (1 / H ^ 2) := by field_simp
    have e2 : 2 * (2 * D.beta / N * Ch) ^ 2 = 8 * D.beta ^ 2 * Ch ^ 2 * (1 / (N : ℝ) ^ 2) := by
      field_simp; ring
    rw [e1, e2, hc2]
    have a1 : 0 ≤ 1 / H ^ 2 := by positivity
    have a2 : 0 ≤ 1 / (N : ℝ) ^ 2 := by positivity
    have b1 : 0 ≤ C2 ^ 2 := by positivity
    have b2 : 0 ≤ Ch ^ 2 := by positivity
    have s1 : 2 * D.beta ^ 2 * C2 ^ 2 * (1 / H ^ 2) ≤ 2 * βp ^ 2 * C2 ^ 2 * (1 / H ^ 2) := by gcongr
    have s2 : 8 * D.beta ^ 2 * Ch ^ 2 * (1 / (N : ℝ) ^ 2) ≤ 8 * βp ^ 2 * Ch ^ 2 * (1 / (N : ℝ) ^ 2) := by gcongr
    have key : 8 * βp ^ 2 * (C2 ^ 2 + Ch ^ 2) * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2) -
        (2 * βp ^ 2 * C2 ^ 2 * (1 / H ^ 2) + 8 * βp ^ 2 * Ch ^ 2 * (1 / (N : ℝ) ^ 2)) =
        6 * (βp ^ 2 * C2 ^ 2) * (1 / H ^ 2) + 8 * (βp ^ 2 * C2 ^ 2) * (1 / (N : ℝ) ^ 2) +
          8 * (βp ^ 2 * Ch ^ 2) * (1 / H ^ 2) := by ring
    have hk0 : 0 ≤ 6 * (βp ^ 2 * C2 ^ 2) * (1 / H ^ 2) + 8 * (βp ^ 2 * C2 ^ 2) * (1 / (N : ℝ) ^ 2) +
          8 * (βp ^ 2 * Ch ^ 2) * (1 / H ^ 2) := by positivity
    linarith
  have hlam2 : lam ^ 2 * (J.card * (C2 * Real.log H) + H ^ 2) ≤
      c1 * (Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2) := by
    have hl2 : lam ^ 2 = D.beta ^ 2 / (N : ℝ) ^ 2 := by rw [hlam]; ring
    rw [hl2]
    have hCl : 0 ≤ C2 * Real.log H := mul_nonneg hC20 hlog
    have hJle : (J.card : ℝ) ≤ N := by rw [hJcard]; linarith
    have h1 : D.beta ^ 2 / (N : ℝ) ^ 2 * (J.card * (C2 * Real.log H)) ≤
        D.beta ^ 2 / (N : ℝ) ^ 2 * (N * (C2 * Real.log H)) := by gcongr
    have h2 : D.beta ^ 2 / (N : ℝ) ^ 2 * (N * (C2 * Real.log H)) + D.beta ^ 2 / (N : ℝ) ^ 2 * H ^ 2 =
        D.beta ^ 2 * (C2 * (Real.log H / N) + H ^ 2 / (N : ℝ) ^ 2) := by field_simp
    have a1 : 0 ≤ Real.log H / N := by positivity
    have a2 : 0 ≤ H ^ 2 / (N : ℝ) ^ 2 := by positivity
    have a3 : 0 ≤ 1 / H ^ 2 := by positivity
    have a4 : 0 ≤ 1 / (N : ℝ) ^ 2 := by positivity
    calc D.beta ^ 2 / (N : ℝ) ^ 2 * (J.card * (C2 * Real.log H) + H ^ 2)
        = D.beta ^ 2 / (N : ℝ) ^ 2 * (J.card * (C2 * Real.log H)) + D.beta ^ 2 / (N : ℝ) ^ 2 * H ^ 2 := by ring
      _ ≤ D.beta ^ 2 * (C2 * (Real.log H / N) + H ^ 2 / (N : ℝ) ^ 2) := by linarith
      _ ≤ βp ^ 2 * (C2 * (Real.log H / N) + H ^ 2 / (N : ℝ) ^ 2) := by
          gcongr
      _ ≤ _ := by
        rw [hc1]
        have key : βp ^ 2 * (C2 + 1) * (Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2) -
            βp ^ 2 * (C2 * (Real.log H / N) + H ^ 2 / (N : ℝ) ^ 2) =
            βp ^ 2 * (Real.log H / N + C2 * (H ^ 2 / (N : ℝ) ^ 2) +
              (C2 + 1) * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2)) := by ring
        have hk0 : 0 ≤ βp ^ 2 * (Real.log H / N + C2 * (H ^ 2 / (N : ℝ) ^ 2) +
              (C2 + 1) * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2)) := by positivity
        linarith
  set Θ : ℝ := Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2 with hΘ
  have hΘ0 : 0 ≤ Θ := by positivity
  have hSm : Measurable S := Finset.measurable_sum _ fun j _ => hfm.comp (measurable_pi_apply j)
  have hSb : ∀ Y, |S Y| ≤ J.card * H := fun Y => by
    simp only [hS]
    calc |∑ j ∈ J, f (Y j)| ≤ ∑ j ∈ J, |f (Y j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ J, H := Finset.sum_le_sum fun j _ => hfb _
      _ = _ := by simp
  have hSint : Integrable (fun Y => S Y ^ (4 * q)) Pm :=
    taylor_integrable_of_bdd (hSm.pow_const _) (B := (J.card * H) ^ (4 * q)) fun Y => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hSb Y) _
  have hev : Even (4 * q) := ⟨2 * q, by ring⟩
  have hRHS : Integrable (fun Y => 2 ^ (4 * q - 1) * ((lam * S Y) ^ (4 * q) + e ^ (4 * q))) Pm := by
    refine Integrable.const_mul (Integrable.add ?_ (integrable_const _)) _
    simp_rw [mul_pow]
    exact hSint.const_mul _
  have hS4 : ∫ Y, S Y ^ (4 * q) ∂Pm ≤ taylor_kb (2 * q) * (J.card * (C2 * Real.log H) + H ^ 2) ^ (2 * q) := by
    have : 4 * q = 2 * (2 * q) := by ring
    rw [this]; exact hbern
  have he4 : e ^ (4 * q) ≤ (c2 * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2)) ^ (2 * q) := by
    have : e ^ (4 * q) = (e ^ 2) ^ (2 * q) := by rw [← pow_mul]; ring_nf
    rw [this]
    exact pow_le_pow_left₀ (sq_nonneg _) hebound _
  have hstep1 : ∫ Y, (fieldH D N i H Y y) ^ (4 * q) ∂Pm ≤
      ∫ Y, 2 ^ (4 * q - 1) * ((lam * S Y) ^ (4 * q) + e ^ (4 * q)) ∂Pm := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun Y => hev.pow_nonneg _) hRHS
      (Filter.Eventually.of_forall fun Y => ?_)
    simp only [hfield]
    exact s81b_pow_sum _ _ q hq
  have hstep2 : ∫ Y, 2 ^ (4 * q - 1) * ((lam * S Y) ^ (4 * q) + e ^ (4 * q)) ∂Pm =
      2 ^ (4 * q - 1) * (lam ^ (4 * q) * ∫ Y, S Y ^ (4 * q) ∂Pm + e ^ (4 * q)) := by
    rw [integral_const_mul]
    congr 1
    simp_rw [mul_pow]
    rw [integral_add (hSint.const_mul _) (integrable_const _), integral_const_mul]
    simp
  have hk := taylor_kb_one_le (2 * q)
  have hlamq : lam ^ (4 * q) * (taylor_kb (2 * q) * (J.card * (C2 * Real.log H) + H ^ 2) ^ (2 * q)) =
      taylor_kb (2 * q) * (lam ^ 2 * (J.card * (C2 * Real.log H) + H ^ 2)) ^ (2 * q) := by
    rw [mul_pow, ← pow_mul]; ring_nf
  have hstep3 : 2 ^ (4 * q - 1) * (lam ^ (4 * q) * ∫ Y, S Y ^ (4 * q) ∂Pm + e ^ (4 * q)) ≤
      2 ^ (4 * q - 1) * (taylor_kb (2 * q) * (c1 * Θ) ^ (2 * q) + (c2 * Θ) ^ (2 * q)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hlam4 : 0 ≤ lam ^ (4 * q) := by positivity
    have h1 : lam ^ (4 * q) * ∫ Y, S Y ^ (4 * q) ∂Pm ≤ taylor_kb (2 * q) * (c1 * Θ) ^ (2 * q) := by
      refine (mul_le_mul_of_nonneg_left hS4 hlam4).trans ?_
      rw [hlamq]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlam2 _) (by linarith)
    have h2 : e ^ (4 * q) ≤ (c2 * Θ) ^ (2 * q) := by
      refine he4.trans (pow_le_pow_left₀ (by positivity) ?_ _)
      refine mul_le_mul_of_nonneg_left ?_ hc20
      have : 0 ≤ Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 := by positivity
      rw [hΘ]; linarith
    linarith
  refine hstep1.trans (hstep2.le.trans (hstep3.trans (le_of_eq ?_)))
  rw [mul_pow, mul_pow]
  ring

end HRS.Whole.S81b
