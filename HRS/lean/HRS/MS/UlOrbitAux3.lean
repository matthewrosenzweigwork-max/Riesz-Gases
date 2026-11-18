import HRS.MS.UlOrbitAux2

/-!
# UL-6 (S5.1 part 2, orbit data), part 3: the time-integral identity `u_a(r) = g_a + ∫_r^T u_{a+1}`

Infrastructure packet UL-6; not a manuscript row.  Helper lemmas carry the prefix `ul6_`.

For `g ∈ UlClosure K` and the level-`K` evolution `w` with terminal time `T` and datum `L g`
(`L = generatorW (fixedViscosityCoeff ..) 0`), the family `Φ(r) = g + ∫_r^T w(τ) dτ` is an `IsUlBackwardEvolution`
with terminal datum `g` (`ul6_Phi_evolution`); by uniqueness it equals the evolution of `g`
(`ul6_duhamel_time`).  The only non-routine point is the commutation `L ∫_r^T w = ∫_r^T L w` (differentiation
under the integral for the local part, Fubini for the nonlocal term).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.Ul

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqN2a

variable {d : ℕ}

section Reg
variable {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ρ : Euc d → ℝ} {c : Euc d → Euc d} {ν : ℝ} {k : ℕ}
  {θ : Euc d → ℝ}

/-- A strongly continuous closure-valued family with the classical time derivative is an evolution. -/
theorem ul6_evol_of_reg (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) {t : ℝ}
    {f : Euc d → ℝ} {u : ℝ → Euc d → ℝ} (hu : UlReg k θ t u) (hterm : u t = f)
    (htd : ∀ x : Euc d, ∀ r ∈ Ioo (0 : ℝ) t, HasDerivAt (fun r' => u r' x)
      (-(generatorW (fixedViscosityCoeff s M Q ν c ρ) r (u r) x)) r) :
    IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ρ) t f u := by
  have huU : UlUReg k θ t u := ul4b_unif_of_reg H.hθ hu
  refine ⟨⟨?_, ?_, ?_, hterm, htd, ?_, ?_⟩, hu.mem, hu.cont⟩
  · exact fun r hr => (hu.mem r hr).1
  · intro j hj
    obtain ⟨B, hB0, hB⟩ := ul5_ureg_bdd H.hθ hu (j := 4) H.hk
    exact ⟨B, fun r hr x => (ul3_cb_apply (hB r hr).1 (hj.trans (by norm_num)) x).trans (hB r hr).2⟩
  · intro j hj
    exact ul5_ureg_joint H.hθ huU (j := 4) H.hk (i := j) (hj.trans (by norm_num))
  · have e : (fun p : Icc (0 : ℝ) t × Euc d => generatorW (fixedViscosityCoeff s M Q ν c ρ) p.1
        (u p.1) p.2) = fun p => ul5A Q ν (u p.1) p.2 + ulPert s M ρ c (u p.1) p.2 := by
      funext p; exact ul5_gen_fixed s M Q ν c ρ p.1 _ p.2
    show Continuous (fun p : Icc (0 : ℝ) t × Euc d => generatorW (fixedViscosityCoeff s M Q ν c ρ) p.1
        (u p.1) p.2)
    rw [e]
    exact (ul5_A_joint Q ν H.hθ (a := u) huU H.hk2).add (ul5_pert_joint H (a := u) huU)
  · obtain ⟨B, hB0, hB⟩ := ul5_ureg_bdd H.hθ hu (j := 4) H.hk
    obtain ⟨Cp, hCp0, hpcb⟩ := ul4_pert_cb H.hs0 H.hsd M ρ H.hρ H.hc
    obtain ⟨K, hK0, hK⟩ := ul5_matVec_le Q
    refine ⟨|ν| * (d * B) + Cp * B + B * K, fun r hr x => ?_⟩
    rw [ul5_gen_fixed]
    have h1 : ‖iteratedFDeriv ℝ 1 (u r) x‖ ≤ B :=
      (ul3_cb_apply (hB r hr).1 (by norm_num) x).trans (hB r hr).2
    have h2 : ‖iteratedFDeriv ℝ 2 (u r) x‖ ≤ B :=
      (ul3_cb_apply (hB r hr).1 (by norm_num) x).trans (hB r hr).2
    have hA := ul5_A_bound Q ν x h1 h2
    have hp : |ulPert s M ρ c (u r) x| ≤ Cp * B :=
      ((hpcb _ (hB r hr).1).2 x).trans (mul_le_mul_of_nonneg_left (hB r hr).2 hCp0)
    have hQ : B * ‖Torus.matVec Q x‖ ≤ B * K * ‖x‖ := by
      calc B * ‖Torus.matVec Q x‖ ≤ B * (K * ‖x‖) := mul_le_mul_of_nonneg_left (hK x) hB0
        _ = B * K * ‖x‖ := by ring
    have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
    have hν0 : 0 ≤ |ν| * (d * B) := by positivity
    have hCB : 0 ≤ Cp * B := by positivity
    have hBK : 0 ≤ B * K := by positivity
    calc |ul5A Q ν (u r) x + ulPert s M ρ c (u r) x|
        ≤ |ul5A Q ν (u r) x| + |ulPert s M ρ c (u r) x| := abs_add_le _ _
      _ ≤ |ν| * (d * B) + B * ‖Torus.matVec Q x‖ + Cp * B := add_le_add hA hp
      _ ≤ (|ν| * (d * B) + Cp * B + B * K) * (1 + ‖x‖) := by
        nlinarith [mul_nonneg hν0 hx0, mul_nonneg hCB hx0]

/-- the `ulNormE` of a short time integral -/
theorem ul6_int_small (hθ : IsUlCutoff θ) (hk0 : (d : ℝ) / 2 < k) {T : ℝ} (hT : 0 ≤ T)
    {w : ℝ → Euc d → ℝ} (hw : UlReg k θ T w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r₁ ∈ Icc (0 : ℝ) T, ∀ r₂ ∈ Icc (0 : ℝ) T, r₁ ≤ r₂ →
      ulNormE k θ (fun y => ∫ τ in r₁..r₂, w τ y) ≤ ENNReal.ofReal (C * (r₂ - r₁)) := by
  obtain ⟨χ, hχ⟩ := ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := ul_equiv k θ χ hθ hχ
  obtain ⟨C0, hC0, htb⟩ := ul4_time_bound k χ hχ
  obtain ⟨W, hW⟩ := ul4_bdd hθ hw
  obtain ⟨Bv, hBv⟩ := ul5_val_bdd hθ hw hk0
  have hjoint := ul5_ureg_val hθ (ul4b_unif_of_reg hθ hw) hk0
  set N : ℝ := Ce * max W 0 + 1 with hN
  have hN0 : 0 < N := by positivity
  refine ⟨Ce * (C0 * N), by positivity, fun r₁ h1 r₂ h2 h12 => ?_⟩
  rcases h12.eq_or_lt with heq | hlt
  · subst heq
    simp only [intervalIntegral.integral_same, sub_self, mul_zero, ENNReal.ofReal_zero]
    rw [ul4b_norm_zero]
  · set τ : ℝ := r₂ - r₁ with hτ
    have hτ0 : 0 < τ := sub_pos.2 hlt
    set F : ℝ → Euc d → ℝ := fun σ y => w (ul4bCl T (r₁ + σ)) y with hF
    have hFc : Continuous (Function.uncurry F) := by
      have hmap : Continuous (fun p : ℝ × Euc d =>
          ((⟨ul4bCl T (r₁ + p.1), ul4bCl_mem hT _⟩ : Icc (0 : ℝ) T), p.2)) :=
        (Continuous.subtype_mk ((ul4bCl_cont T).comp (continuous_const.add continuous_fst)) _).prodMk
          continuous_snd
      exact hjoint.comp hmap
    have hid : ∀ σ ∈ Ioo (0 : ℝ) τ, r₁ + σ ∈ Icc (0 : ℝ) T := fun σ hσ =>
      ⟨by linarith [h1.1, hσ.1], by linarith [h2.2, hσ.2]⟩
    have hFbd : ∀ σ ∈ Ioo (0 : ℝ) τ, ∀ x, |F σ x| ≤ Bv := fun σ hσ x =>
      hBv _ (ul4bCl_mem hT _) x
    have hFn : ∀ σ ∈ Ioo (0 : ℝ) τ, ulocNormE k χ (F σ) ≤ ENNReal.ofReal N := by
      intro σ hσ
      have e : F σ = w (r₁ + σ) := by
        funext y; simp only [hF, ul4bCl_eq (hid σ hσ)]
      rw [e]
      refine ((hequ _).2).trans ?_
      calc ENNReal.ofReal Ce * ulNormE k θ (w (r₁ + σ)) ≤ ENNReal.ofReal Ce * ENNReal.ofReal W :=
            mul_le_mul' le_rfl (hW _ (hid σ hσ))
        _ = ENNReal.ofReal (Ce * W) := (ENNReal.ofReal_mul hCe.le).symm
        _ ≤ ENNReal.ofReal N := by
            apply ENNReal.ofReal_le_ofReal
            have : W ≤ max W 0 := le_max_left _ _
            nlinarith
    have hmain := htb hτ0 F hFc.measurable Bv hFbd (fun _ => N) measurable_const
      intervalIntegrable_const N hN0 (fun _ _ => le_rfl) hFn
    have hconv : (fun y => ∫ τ' in r₁..r₂, w τ' y) = fun y => ∫ σ in (0 : ℝ)..τ, F σ y := by
      funext y
      have e1 : ∫ σ in (0 : ℝ)..τ, F σ y = ∫ σ in (0 : ℝ)..τ, w (r₁ + σ) y := by
        refine intervalIntegral.integral_congr fun σ hσ => ?_
        rw [uIcc_of_le hτ0.le] at hσ
        have : r₁ + σ ∈ Icc (0 : ℝ) T := ⟨by linarith [h1.1, hσ.1], by linarith [h2.2, hσ.2]⟩
        simp only [hF, ul4bCl_eq this]
      rw [e1, intervalIntegral.integral_comp_add_left (fun x => w x y) r₁]
      simp [hτ]
    rw [hconv]
    refine ((hequ _).1).trans ?_
    calc ENNReal.ofReal Ce * ulocNormE k χ (fun y => ∫ σ in (0 : ℝ)..τ, F σ y)
        ≤ ENNReal.ofReal Ce * ENNReal.ofReal (C0 * ∫ σ in (0 : ℝ)..τ, N) := mul_le_mul' le_rfl hmain
      _ = ENNReal.ofReal (Ce * (C0 * ∫ σ in (0 : ℝ)..τ, N)) := (ENNReal.ofReal_mul hCe.le).symm
      _ = ENNReal.ofReal (Ce * (C0 * N) * (r₂ - r₁)) := by
          congr 1
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
          ring

end Reg

/-! ### The cancellation integral: Fubini in a time parameter -/

section Swap
variable {s : ℝ}

/-- the integrand of the `j`-th component of the cancellation convolution -/
def ul6I (s : ℝ) (j : Fin d) (x : Euc d) (F : Euc d → ℝ) (y : Euc d) : ℝ :=
  if ‖x - y‖ ≤ 1 / 4 then (F y - F x) * kap d s j (x - y) else F y * kap d s j (x - y)

lemma ul6I_bound (hs0 : 0 ≤ s) (j : Fin d) (x : Euc d) {L : ℝ} (hL : 0 ≤ L) {F : Euc d → ℝ}
    {b : Euc d → ℝ} (hF : ∀ y, ‖x - y‖ ≤ 1 / 4 → |F y - F x| ≤ L * ‖x - y‖)
    (hb : ∀ y, |F y| ≤ b y) (y : Euc d) :
    |ul6I s j x F y| ≤ max 1 s * L * ballF (d := d) s (x - y) + b y * (max 1 s * 8 ^ (s + 1)) := by
  have hb0 : 0 ≤ b y := (abs_nonneg _).trans (hb y)
  have hball : 0 ≤ ballF (d := d) s (x - y) := ballF_nonneg s _
  have hm1 : 0 ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
  have hfar0 : 0 ≤ b y * (max 1 s * 8 ^ (s + 1)) := by positivity
  have hnear0 : 0 ≤ max 1 s * L * ballF (d := d) s (x - y) := by positivity
  unfold ul6I
  by_cases hy : ‖x - y‖ ≤ 1 / 4
  · simp only [hy, if_true]
    by_cases hy0 : x - y = 0
    · have hyx : y = x := by rw [sub_eq_zero] at hy0; exact hy0.symm
      have h0 : |(F y - F x) * kap d s j (x - y)| = 0 := by rw [hyx]; simp
      rw [h0]
      exact add_nonneg hnear0 hfar0
    · have hn : 0 < ‖x - y‖ := norm_pos_iff.2 hy0
      have hb' := kap_bound hs0 j hy0
      have h1 : ‖x - y‖ ^ (-s - 1) * ‖x - y‖ = ‖x - y‖ ^ (-s) := by
        rw [← Real.rpow_add_one hn.ne']; congr 1; ring
      have hballe : ballF (d := d) s (x - y) = ‖x - y‖ ^ (-s) := by
        simp [ballF, show ‖x - y‖ < 1 by linarith]
      rw [hballe, abs_mul]
      have : |F y - F x| * |kap d s j (x - y)| ≤ max 1 s * L * ‖x - y‖ ^ (-s) := by
        calc |F y - F x| * |kap d s j (x - y)|
            ≤ (L * ‖x - y‖) * (max 1 s * ‖x - y‖ ^ (-s - 1)) :=
              mul_le_mul (hF y hy) hb' (abs_nonneg _) (by positivity)
          _ = max 1 s * L * ‖x - y‖ ^ (-s) := by rw [← h1]; ring
      rw [hballe] at hnear0
      linarith
  · simp only [hy, if_false]
    have hy' : 1 / 8 ≤ ‖x - y‖ := by linarith [not_le.1 hy]
    rw [abs_mul]
    have : |F y| * |kap d s j (x - y)| ≤ b y * (max 1 s * 8 ^ (s + 1)) :=
      mul_le_mul (hb y) (ul1_kap_far_bound hs0 j hy') (abs_nonneg _) hb0
    linarith

/-- Fubini for the cancellation integral against a time average -/
theorem ul6_swap (hs0 : 0 ≤ s) (j : Fin d) (x : Euc d) {μ : Measure ℝ} [IsFiniteMeasure μ]
    {F : ℝ → Euc d → ℝ} (hFc : Continuous (fun p : ℝ × Euc d => F p.1 p.2)) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ τ y, ‖x - y‖ ≤ 1 / 4 → |F τ y - F τ x| ≤ L * ‖x - y‖) {b : Euc d → ℝ}
    (hbi : Integrable b) (hb : ∀ τ y, |F τ y| ≤ b y) (hballi : Integrable (ballF (d := d) s)) :
    Integrable (fun τ => ∫ y, ul6I s j x (F τ) y) μ ∧
    ∫ y, ul6I s j x (fun y => ∫ τ, F τ y ∂μ) y = ∫ τ, (∫ y, ul6I s j x (F τ) y) ∂μ := by
  have hint : ∀ y, Integrable (fun τ => F τ y) μ := fun y =>
    Integrable.mono' (integrable_const (b y))
      (hFc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => by rw [Real.norm_eq_abs]; exact hb τ y)
  have step1 : ∀ y, ul6I s j x (fun y => ∫ τ, F τ y ∂μ) y = ∫ τ, ul6I s j x (F τ) y ∂μ := by
    intro y
    unfold ul6I
    by_cases hy : ‖x - y‖ ≤ 1 / 4
    · simp only [hy, if_true]
      rw [← integral_sub (hint y) (hint x), ← integral_mul_const]
    · simp only [hy, if_false]
      rw [integral_mul_const]
  simp_rw [step1]
  set M : Euc d → ℝ := fun y => max 1 s * L * ballF (d := d) s (x - y) +
    b y * (max 1 s * 8 ^ (s + 1)) with hM
  have hMi : Integrable M := by
    refine Integrable.add ?_ (hbi.mul_const _)
    exact (hballi.comp_sub_left x).const_mul _
  have hmeasI : MeasurableSet {y : Euc d | ‖x - y‖ ≤ 1 / 4} :=
    measurableSet_le (measurable_const.sub measurable_id).norm measurable_const
  have hk : Measurable (fun y : Euc d => kap d s j (x - y)) :=
    (kap_measurable s j).comp (measurable_const.sub measurable_id)
  have hFm : Measurable (fun q : Euc d × ℝ => F q.2 q.1) :=
    (hFc.comp (continuous_snd.prodMk continuous_fst)).measurable
  have hFx : Measurable (fun q : Euc d × ℝ => F q.2 x) :=
    (hFc.comp (continuous_snd.prodMk continuous_const)).measurable
  have hmeas : Measurable (fun q : Euc d × ℝ => ul6I s j x (F q.2) q.1) := by
    unfold ul6I
    refine Measurable.ite (hmeasI.preimage measurable_fst) ?_ ?_
    · exact (hFm.sub hFx).mul (hk.comp measurable_fst)
    · exact hFm.mul (hk.comp measurable_fst)
  have hprod : Integrable (fun q : Euc d × ℝ => ul6I s j x (F q.2) q.1) (volume.prod μ) := by
    have hM' : Integrable (fun q : Euc d × ℝ => M q.1 * (1 : ℝ)) (volume.prod μ) :=
      Integrable.mul_prod hMi (integrable_const (1 : ℝ))
    refine hM'.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, mul_one]
    exact ul6I_bound hs0 j x hL0 (hL q.2) (hb q.2) q.1
  refine ⟨?_, ?_⟩
  · exact hprod.integral_prod_right
  · exact integral_integral_swap (f := fun y τ => ul6I s j x (F τ) y) hprod

end Swap

/-! ### Differentiation under the time integral and commutation with the generator -/

section Fam
variable {μ : Measure ℝ} [IsFiniteMeasure μ]

theorem ul6_jets (G : ℝ → Euc d → ℝ) (n : ℕ) {B : ℝ} (hG : ∀ τ, ContDiff ℝ (n : WithTop ℕ∞) (G τ))
    (hbd : ∀ i ≤ n, ∀ τ y, ‖iteratedFDeriv ℝ i (G τ) y‖ ≤ B)
    (hjc : ∀ i ≤ n, Continuous (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2)) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun y => ∫ τ, G τ y ∂μ) ∧
      ∀ i ≤ n, ∀ y, iteratedFDeriv ℝ i (fun y => ∫ τ, G τ y ∂μ) y =
        ∫ τ, iteratedFDeriv ℝ i (G τ) y ∂μ :=
  HRS.MS.Lc.lc4_iteratedFDeriv_integral G n hG (Φ := fun _ => B) (integrable_const B) hbd
    (fun i hi y => ((hjc i hi).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)

theorem ul6_jet_int (G : ℝ → Euc d → ℝ) {B : ℝ}
    (hbd : ∀ i ≤ 4, ∀ τ y, ‖iteratedFDeriv ℝ i (G τ) y‖ ≤ B)
    (hjc : ∀ i ≤ 4, Continuous (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2))
    {i : ℕ} (hi : i ≤ 4) (y : Euc d) :
    Integrable (fun τ => iteratedFDeriv ℝ i (G τ) y) μ :=
  Integrable.mono' (integrable_const B)
    ((hjc i hi).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => hbd i hi τ y)

theorem ul6_eval_integral {n : ℕ} (v : Fin n → Euc d)
    {φ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => Euc d) ℝ} (hφ : Integrable φ μ) :
    (∫ τ, φ τ ∂μ) v = ∫ τ, φ τ v ∂μ :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ v).integral_comp_comm hφ).symm

theorem ul6_memCb (G : ℝ → Euc d → ℝ) {B : ℝ} (hG : ∀ τ, ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) (G τ))
    (hbd : ∀ i ≤ 4, ∀ τ y, ‖iteratedFDeriv ℝ i (G τ) y‖ ≤ B)
    (hjc : ∀ i ≤ 4, Continuous (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2)) :
    HRS.MemCb 4 (fun y => ∫ τ, G τ y ∂μ) := by
  obtain ⟨hΨ, hj⟩ := ul6_jets (μ := μ) G 4 hG hbd hjc
  refine ⟨hΨ, fun i hi => ⟨B * μ.real univ, ?_⟩⟩
  rintro _ ⟨y, rfl⟩
  simp only
  rw [hj i hi y]
  exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun τ => hbd i hi τ y)

/-- the local part of the generator commutes with the time integral -/
theorem ul6_loc_integral (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (c : Euc d → Euc d)
    (G : ℝ → Euc d → ℝ) {B : ℝ} (hG : ∀ τ, ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) (G τ))
    (hbd : ∀ i ≤ 4, ∀ τ y, ‖iteratedFDeriv ℝ i (G τ) y‖ ≤ B)
    (hjc : ∀ i ≤ 4, Continuous (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2)) (y : Euc d) :
    Integrable (fun τ => ul5A Q ν (G τ) y + fderiv ℝ (G τ) y (c y)) μ ∧
    ul5A Q ν (fun y => ∫ τ, G τ y ∂μ) y + fderiv ℝ (fun y => ∫ τ, G τ y ∂μ) y (c y) =
      ∫ τ, (ul5A Q ν (G τ) y + fderiv ℝ (G τ) y (c y)) ∂μ := by
  obtain ⟨hΨ, hj⟩ := ul6_jets (μ := μ) G 4 hG hbd hjc
  have hi1 := ul6_jet_int (μ := μ) G hbd hjc (i := 1) (by norm_num) y
  have hi2 := ul6_jet_int (μ := μ) G hbd hjc (i := 2) (by norm_num) y
  have hI1 : ∀ v : Fin 1 → Euc d, Integrable (fun τ => iteratedFDeriv ℝ 1 (G τ) y v) μ := fun v =>
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ v).integrable_comp hi1
  have hI2 : ∀ v : Fin 2 → Euc d, Integrable (fun τ => iteratedFDeriv ℝ 2 (G τ) y v) μ := fun v =>
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ v).integrable_comp hi2
  have hfd : ∀ (u : Euc d → ℝ), fderiv ℝ u y (c y) = iteratedFDeriv ℝ 1 u y (fun _ => c y) := fun u =>
    (iteratedFDeriv_one_apply (m := fun _ : Fin 1 => c y)).symm
  have hL : ul5A Q ν (fun y => ∫ τ, G τ y ∂μ) y + fderiv ℝ (fun y => ∫ τ, G τ y ∂μ) y (c y) =
      ν * ∑ i : Fin d, ∫ τ, iteratedFDeriv ℝ 2 (G τ) y
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] ∂μ -
      (∫ τ, iteratedFDeriv ℝ 1 (G τ) y (fun _ => Torus.matVec Q y) ∂μ) +
      ∫ τ, iteratedFDeriv ℝ 1 (G τ) y (fun _ => c y) ∂μ := by
    rw [ul5_A_eq, hfd, hj 1 (by norm_num) y]
    simp only [ul5G]
    rw [hj 2 (by norm_num) y]
    simp only [ul6_eval_integral _ hi1, ul6_eval_integral _ hi2]
  have hR : ∀ τ, ul5A Q ν (G τ) y + fderiv ℝ (G τ) y (c y) =
      ν * ∑ i : Fin d, iteratedFDeriv ℝ 2 (G τ) y
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] -
      iteratedFDeriv ℝ 1 (G τ) y (fun _ => Torus.matVec Q y) +
      iteratedFDeriv ℝ 1 (G τ) y (fun _ => c y) := by
    intro τ
    rw [ul5_A_eq, hfd]
    simp only [ul5G]
  have hsum : Integrable (fun τ => ∑ i : Fin d, iteratedFDeriv ℝ 2 (G τ) y
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]) μ :=
    integrable_finsetSum _ fun i _ => hI2 _
  have hAi : Integrable (fun τ => ν * ∑ i : Fin d, iteratedFDeriv ℝ 2 (G τ) y
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]) μ := hsum.const_mul ν
  have hBi : Integrable (fun τ => iteratedFDeriv ℝ 1 (G τ) y (fun _ => Torus.matVec Q y)) μ := hI1 _
  have hCi : Integrable (fun τ => iteratedFDeriv ℝ 1 (G τ) y (fun _ => c y)) μ := hI1 _
  have hfun : (fun τ => ul5A Q ν (G τ) y + fderiv ℝ (G τ) y (c y)) = fun τ =>
      ν * ∑ i : Fin d, iteratedFDeriv ℝ 2 (G τ) y
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] -
      iteratedFDeriv ℝ 1 (G τ) y (fun _ => Torus.matVec Q y) +
      iteratedFDeriv ℝ 1 (G τ) y (fun _ => c y) := funext hR
  have hAB : Integrable (fun τ => ν * ∑ i : Fin d, iteratedFDeriv ℝ 2 (G τ) y
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] -
      iteratedFDeriv ℝ 1 (G τ) y (fun _ => Torus.matVec Q y)) μ := hAi.sub hBi
  refine ⟨by rw [hfun]; exact hAB.add hCi, ?_⟩
  rw [hL, hfun, integral_add hAB hCi, integral_sub hAi hBi, integral_const_mul,
    integral_finset_sum _ fun i _ => hI2 _]

lemma ul6_norm_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Euc d → F) (x : Euc d) :
    ‖fderiv ℝ f x‖ = ‖iteratedFDeriv ℝ 1 f x‖ := by
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]

/-- uniform Lipschitz bound of `ψ ∂_v G_τ` -/
theorem ul6_F_lip (ψ : SchwartzMap (Euc d) ℝ) (v : Euc d) (G : ℝ → Euc d → ℝ) {B : ℝ}
    (hG : ∀ τ, ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) (G τ))
    (hbd : ∀ i ≤ 4, ∀ τ y, ‖iteratedFDeriv ℝ i (G τ) y‖ ≤ B) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ y z, |ψ y * fderiv ℝ (G τ) y v - ψ z * fderiv ℝ (G τ) z v| ≤ L * ‖y - z‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbd 0 (by norm_num) 0 0)
  set C0 : ℝ := SchwartzMap.seminorm ℝ 0 0 ψ with hC0
  set C1 : ℝ := SchwartzMap.seminorm ℝ 0 1 ψ with hC1
  have hC00 : 0 ≤ C0 := apply_nonneg _ _
  have hC10 : 0 ≤ C1 := apply_nonneg _ _
  refine ⟨C0 * (‖v‖ * B) + (‖v‖ * B) * C1, by positivity, fun τ y z => ?_⟩
  have hg4 : ContDiff ℝ 4 (G τ) := by exact_mod_cast hG τ
  have hfd : ContDiff ℝ 3 (fderiv ℝ (G τ)) := hg4.fderiv_right (by norm_num)
  have hh : ContDiff ℝ 3 (fun y => fderiv ℝ (G τ) y v) := hfd.clm_apply contDiff_const
  have hhd : Differentiable ℝ (fun y => fderiv ℝ (G τ) y v) := hh.differentiable (by norm_num)
  have hψd : Differentiable ℝ ψ := (ψ.smooth 1).differentiable (by norm_num)
  have hnorm1 : ∀ y, |fderiv ℝ (G τ) y v| ≤ ‖v‖ * B := fun y => by
    have h1 := (fderiv ℝ (G τ) y).le_opNorm v
    rw [ul6_norm_fderiv] at h1
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (G τ) y v‖ ≤ ‖iteratedFDeriv ℝ 1 (G τ) y‖ * ‖v‖ := h1
      _ ≤ B * ‖v‖ := mul_le_mul_of_nonneg_right (hbd 1 (by norm_num) τ y) (norm_nonneg _)
      _ = ‖v‖ * B := by ring
  have hnorm2 : ∀ y, ‖fderiv ℝ (fun y => fderiv ℝ (G τ) y v) y‖ ≤ ‖v‖ * B := fun y => by
    have hd1 : DifferentiableAt ℝ (fderiv ℝ (G τ)) y := (hfd.differentiable (by norm_num)) y
    have hcomp := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp y hd1.hasFDerivAt
    have e : (fun y => fderiv ℝ (G τ) y v) = (ContinuousLinearMap.apply ℝ ℝ v) ∘ (fderiv ℝ (G τ)) := rfl
    rw [e, hcomp.fderiv]
    have hv : ‖(ContinuousLinearMap.apply ℝ ℝ v : (Euc d →L[ℝ] ℝ) →L[ℝ] ℝ)‖ ≤ ‖v‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun f => by
        simpa [mul_comm] using f.le_opNorm v
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h2 : ‖fderiv ℝ (fderiv ℝ (G τ)) y‖ ≤ B := by
      rw [ul6_norm_fderiv, norm_iteratedFDeriv_fderiv]
      exact hbd 2 (by norm_num) τ y
    exact mul_le_mul hv h2 (norm_nonneg _) (norm_nonneg _)
  have hnormψ : ∀ y, |ψ y| ≤ C0 := fun y => by
    have := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ ψ 0 y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hnormψ1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ C1 := fun y => by
    have := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ ψ 1 y
    rwa [← ul6_norm_fderiv] at this
  have hderiv : ∀ y, ‖fderiv ℝ (fun y => ψ y * fderiv ℝ (G τ) y v) y‖ ≤
      C0 * (‖v‖ * B) + (‖v‖ * B) * C1 := fun y => by
    rw [fderiv_fun_mul (hψd y) (hhd y)]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hnormψ y) (hnorm2 y) (norm_nonneg _) hC00
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hnorm1 y) (hnormψ1 y) (norm_nonneg _) (by positivity)
  have hdiff : ∀ y ∈ (univ : Set (Euc d)), DifferentiableAt ℝ (fun y => ψ y * fderiv ℝ (G τ) y v) y := by
    intro y _
    exact (hψd y).mul (hhd y)
  rw [← Real.norm_eq_abs]
  exact (convex_univ : Convex ℝ (univ : Set (Euc d))).norm_image_sub_le_of_norm_fderiv_le hdiff
    (fun y _ => hderiv y) (mem_univ z) (mem_univ y)

/-- the nonlocal term commutes with the time integral -/
theorem ul6_nl_integral {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (M : Matrix (Fin d) (Fin d) ℝ)
    (ψ : SchwartzMap (Euc d) ℝ) (G : ℝ → Euc d → ℝ) {B : ℝ}
    (hG : ∀ τ, ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) (G τ))
    (hbd : ∀ i ≤ 4, ∀ τ y, ‖iteratedFDeriv ℝ i (G τ) y‖ ≤ B)
    (hjc : ∀ i ≤ 4, Continuous (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2)) (x : Euc d) :
    Integrable (fun τ => ulNL s M ψ (G τ) x) μ ∧
    ulNL s M ψ (fun y => ∫ τ, G τ y ∂μ) x = ∫ τ, ulNL s M ψ (G τ) x ∂μ := by
  obtain ⟨hΨ, hj⟩ := ul6_jets (μ := μ) G 4 hG hbd hjc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbd 0 (by norm_num) 0 0)
  have hmemΨ : HRS.MemCb 4 (fun y => ∫ τ, G τ y ∂μ) := ul6_memCb G hG hbd hjc
  have hmemG : ∀ τ, HRS.MemCb 4 (G τ) := fun τ =>
    ⟨hG τ, fun i hi => ⟨B, by rintro _ ⟨y, rfl⟩; exact hbd i hi τ y⟩⟩
  have hi1 := ul6_jet_int (μ := μ) G hbd hjc (i := 1) (by norm_num)
  have hfd : ∀ y (v : Euc d), fderiv ℝ (fun y => ∫ τ, G τ y ∂μ) y v = ∫ τ, fderiv ℝ (G τ) y v ∂μ := by
    intro y v
    have e1 : fderiv ℝ (fun y => ∫ τ, G τ y ∂μ) y v =
        iteratedFDeriv ℝ 1 (fun y => ∫ τ, G τ y ∂μ) y (fun _ => v) :=
      (iteratedFDeriv_one_apply (m := fun _ : Fin 1 => v)).symm
    rw [e1, hj 1 (by norm_num) y, ul6_eval_integral _ (hi1 y)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun τ => iteratedFDeriv_one_apply (fun _ : Fin 1 => v))
  unfold ulNL
  simp only [ul1_matVec]
  have key : ∀ j : Fin d, Integrable (fun τ => (convGradConvW (rieszKernelGrad d s)
        (fun y => ψ y * fderiv ℝ (G τ) y (ul1w M j)) x) j) μ ∧
      (convGradConvW (rieszKernelGrad d s)
        (fun y => ψ y * fderiv ℝ (fun y => ∫ τ, G τ y ∂μ) y (ul1w M j)) x) j =
        ∫ τ, (convGradConvW (rieszKernelGrad d s)
          (fun y => ψ y * fderiv ℝ (G τ) y (ul1w M j)) x) j ∂μ := by
    intro j
    set v : Euc d := ul1w M j with hv
    set F : ℝ → Euc d → ℝ := fun τ y => ψ y * fderiv ℝ (G τ) y v with hF
    have hFc : Continuous (fun p : ℝ × Euc d => F p.1 p.2) := by
      have h1 : Continuous (fun p : ℝ × Euc d => iteratedFDeriv ℝ 1 (G p.1) p.2 (fun _ => v)) :=
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ (fun _ => v)).continuous.comp
          (hjc 1 (by norm_num))
      have e : (fun p : ℝ × Euc d => F p.1 p.2) = fun p => ψ p.2 * iteratedFDeriv ℝ 1 (G p.1) p.2 (fun _ => v) := by
        funext p; simp only [hF]; rw [iteratedFDeriv_one_apply]
      rw [e]
      exact (ψ.continuous.comp continuous_snd).mul h1
    obtain ⟨L, hL0, hL⟩ := ul6_F_lip ψ v G hG hbd
    have hbi : Integrable (fun y => |ψ y| * (‖v‖ * B)) := ψ.integrable.abs.mul_const _
    have hb : ∀ τ y, |F τ y| ≤ |ψ y| * (‖v‖ * B) := fun τ y => by
      simp only [hF]
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have h1 := (fderiv ℝ (G τ) y).le_opNorm v
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ (G τ) y v‖ ≤ ‖iteratedFDeriv ℝ 1 (G τ) y‖ * ‖v‖ := by
            rw [← ul6_norm_fderiv]; exact h1
        _ ≤ B * ‖v‖ := mul_le_mul_of_nonneg_right (hbd 1 (by norm_num) τ y) (norm_nonneg _)
        _ = ‖v‖ * B := by ring
    have hswap := ul6_swap (μ := μ) hs0 j x hFc hL0 (fun τ y _ => by
      have := hL τ y x
      rwa [← norm_neg (y - x), neg_sub] at this) hbi hb (ul1_ball_majorant hs0 hsd)
    have hC1τ : ∀ τ, ContDiff ℝ 1 (F τ) := fun τ => by
      have := ul1_F_contDiff ψ M (m := 4) (by norm_num) (by exact_mod_cast hG τ) j
      exact this.of_le (by norm_num)
    have hIτ : ∀ τ, Integrable (F τ) := fun τ => (ul1_L1_cb ψ M (m := 4) (by norm_num) (hmemG τ) j).1
    have hΨF : (fun y => ψ y * fderiv ℝ (fun y => ∫ τ, G τ y ∂μ) y v) = fun y => ∫ τ, F τ y ∂μ := by
      funext y; rw [hfd y v, ← integral_const_mul]
    have hC1Ψ : ContDiff ℝ 1 (fun y => ψ y * fderiv ℝ (fun y => ∫ τ, G τ y ∂μ) y v) := by
      have := ul1_F_contDiff ψ M (m := 4) (by norm_num) (by exact_mod_cast hΨ) j
      exact this.of_le (by norm_num)
    have hIΨ : Integrable (fun y => ψ y * fderiv ℝ (fun y => ∫ τ, G τ y ∂μ) y v) :=
      (ul1_L1_cb ψ M (m := 4) (by norm_num) hmemΨ j).1
    have hcτ : ∀ τ, (convGradConvW (rieszKernelGrad d s) (fun y => ψ y * fderiv ℝ (G τ) y v) x) j =
        ∫ y, ul6I s j x (F τ) y := fun τ => ul1_conv_comp hs0 hsd j (hC1τ τ) (hIτ τ) x
    have hcΨ' : (convGradConvW (rieszKernelGrad d s)
        (fun y => ψ y * fderiv ℝ (fun y => ∫ τ, G τ y ∂μ) y v) x) j =
        ∫ y, ul6I s j x (fun y => ψ y * fderiv ℝ (fun y => ∫ τ, G τ y ∂μ) y v) y := by
      exact ul1_conv_comp hs0 hsd j hC1Ψ hIΨ x
    have hcΨ : (convGradConvW (rieszKernelGrad d s)
        (fun y => ψ y * fderiv ℝ (fun y => ∫ τ, G τ y ∂μ) y v) x) j =
        ∫ y, ul6I s j x (fun y => ∫ τ, F τ y ∂μ) y := by
      rw [hcΨ', hΨF]
    refine ⟨?_, ?_⟩
    · simp only [hcτ]; exact hswap.1
    · rw [hcΨ, hswap.2]
      simp only [hcτ]
  refine ⟨integrable_finsetSum _ fun j _ => (key j).1, ?_⟩
  rw [integral_finset_sum _ fun j _ => (key j).1]
  exact Finset.sum_congr rfl fun j _ => (key j).2

end Fam

/-! ### The generator of `g + ∫_r^T w` -/

section Gen
variable {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ρ : Euc d → ℝ} {c : Euc d → Euc d} {ν : ℝ}

theorem ul6_memCb_zero : HRS.MemCb 4 (fun _ : Euc d => (0 : ℝ)) := by
  refine ⟨contDiff_const, fun j _ => ⟨0, ?_⟩⟩
  rintro _ ⟨y, rfl⟩
  simp only
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [iteratedFDeriv_const_of_ne hj.ne']; simp

theorem ul6_pert_zero (x : Euc d) : ulPert s M ρ c (fun _ => (0 : ℝ)) x = 0 := by
  unfold ulPert ulNL
  simp [gradient, Torus.matVec, convGradConvW]

theorem ul6_pert_add (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    {u v : Euc d → ℝ} (hu : HRS.MemCb 4 u) (hv : HRS.MemCb 4 v) (x : Euc d) :
    ulPert s M ρ c (fun y => u y + v y) x = ulPert s M ρ c u x + ulPert s M ρ c v x := by
  have h1 := ul4_pert_sub hs0 hsd M ρ hρ c (u := u) (v := fun y => 0 - v y) hu
    (ul1_memCb_sub ul6_memCb_zero hv) x
  have h2 := ul4_pert_sub hs0 hsd M ρ hρ c (u := fun _ => 0) (v := v) ul6_memCb_zero hv x
  have h0 := ul6_pert_zero (s := s) (M := M) (ρ := ρ) (c := c) x
  have e : (fun y => u y - (0 - v y)) = fun y => u y + v y := by funext y; ring
  rw [e] at h1
  linarith

theorem ul6_gen_add (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    (Q : Matrix (Fin d) (Fin d) ℝ) {u v : Euc d → ℝ} (hu : HRS.MemCb 4 u) (hv : HRS.MemCb 4 v) (x : Euc d) :
    generatorW (fixedViscosityCoeff s M Q ν c ρ) 0 (fun y => u y + v y) x =
      generatorW (fixedViscosityCoeff s M Q ν c ρ) 0 u x + generatorW (fixedViscosityCoeff s M Q ν c ρ) 0 v x := by
  rw [ul5_gen_fixed, ul5_gen_fixed, ul5_gen_fixed,
    ul5_A_add Q ν (hu.1.of_le (by exact_mod_cast (by norm_num : 2 ≤ 4)))
      (hv.1.of_le (by exact_mod_cast (by norm_num : 2 ≤ 4))) x, ul6_pert_add hs0 hsd hρ hu hv x]
  ring

end Gen

section PhiReg
variable {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ρ : Euc d → ℝ} {c : Euc d → Euc d} {ν : ℝ} {k : ℕ}
  {θ : Euc d → ℝ}

theorem ul6_Phi_reg (H : UlHyp s M ρ c ν k θ) {T : ℝ} (hT : 0 ≤ T) {w : ℝ → Euc d → ℝ}
    (hw : UlReg k θ T w) {g : Euc d → ℝ} (hg : UlClosure k θ g) :
    UlReg k θ T (fun r y => g y + ∫ τ in r..T, w τ y) := by
  have hwU : UlUReg k θ T w := ul4b_unif_of_reg H.hθ hw
  have hval := ul5_ureg_val H.hθ hwU H.hk0
  have hcn : ∀ x, ContinuousOn (fun τ => w τ x) (Icc 0 T) := fun x => ul5_contOn_of_joint hval x
  have hii : ∀ x, ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun τ => w τ x) volume a b := by
    intro x a ha b hb
    exact ((hcn x).mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  have hmem : ∀ r ∈ Icc (0 : ℝ) T, UlClosure k θ (fun y => g y + ∫ τ in r..T, w τ y) := by
    intro r hr
    rcases hr.2.eq_or_lt with heq | hlt
    · have : (fun y => g y + ∫ τ in r..T, w τ y) = g := by
        funext y; rw [heq]; simp
      rw [this]; exact hg
    · have hpos : 0 < T - r := sub_pos.2 hlt
      have hreg : UlReg k θ (T - r) (fun σ => w (σ + r)) :=
        ul4b_reg_shift hr.1 (by rwa [sub_add_cancel])
      have hpt : ∀ x, ContinuousOn (fun σ => w (σ + r) x) (Icc 0 (T - r)) := fun x =>
        (hcn x).comp (continuousOn_id.add continuousOn_const)
          (fun σ hσ => ⟨by linarith [hσ.1, hr.1], by linarith [hσ.2]⟩)
      have hint := ul4b_int_mem H.hk2 H.hθ hpos (ul4b_unif_of_reg H.hθ hreg) hpt
      have e : (fun y => ∫ τ in r..T, w τ y) = fun y => ∫ σ in (0 : ℝ)..(T - r), w (σ + r) y := by
        funext y
        rw [intervalIntegral.integral_comp_add_right (fun τ => w τ y) r]
        simp
      rw [← e] at hint
      exact ul4_closure_add hg hint
  obtain ⟨C, hC0, hC⟩ := ul6_int_small H.hθ H.hk0 hT hw
  obtain ⟨Cn, hCn, hneg⟩ := ul4_neg (k := k) (d := d) H.hθ
  have hone : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a ≤ b →
      b - a < δ → ulNormE k θ (fun x => (g x + ∫ τ in b..T, w τ x) - (g x + ∫ τ in a..T, w τ x)) ≤
        ENNReal.ofReal ε := by
    intro ε hε
    refine ⟨ε / (Cn * C + 1), by positivity, fun a ha b hb hab hd => ?_⟩
    have e : (fun x => (g x + ∫ τ in b..T, w τ x) - (g x + ∫ τ in a..T, w τ x)) =
        fun x => -(∫ τ in a..b, w τ x) := by
      funext x
      have := intervalIntegral.integral_add_adjacent_intervals (hii x a ha b hb) (hii x b hb T ⟨hT, le_rfl⟩)
      linarith
    rw [e]
    refine (hneg _).trans ?_
    calc ENNReal.ofReal Cn * ulNormE k θ (fun y => ∫ τ in a..b, w τ y)
        ≤ ENNReal.ofReal Cn * ENNReal.ofReal (C * (b - a)) := mul_le_mul' le_rfl (hC a ha b hb hab)
      _ = ENNReal.ofReal (Cn * (C * (b - a))) := (ENNReal.ofReal_mul hCn.le).symm
      _ ≤ ENNReal.ofReal ε := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : Cn * (C * (b - a)) ≤ Cn * C * (ε / (Cn * C + 1)) := by
            have : C * (b - a) ≤ C * (ε / (Cn * C + 1)) := mul_le_mul_of_nonneg_left hd.le hC0
            nlinarith [mul_le_mul_of_nonneg_left this hCn.le]
          refine h1.trans ?_
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith [mul_nonneg hCn.le hC0]
  have hun := ul4b_unif_of_oneside H.hθ (F := fun r y => g y + ∫ τ in r..T, w τ y) hone
  exact ⟨hmem, fun r₀ h0 ε hε => by
    obtain ⟨δ, hδ, h⟩ := hun ε hε
    exact ⟨δ, hδ, fun r hr hd => h r hr r₀ h0 hd⟩⟩

end PhiReg

section Phi
variable {s : ℝ} {ρ : Euc d → ℝ} {c : Euc d → Euc d} {ν : ℝ} {k : ℕ} {θ : Euc d → ℝ}

/-- `ul6_nl_integral` and `ul6_loc_integral` give the commutation of the full generator with the time integral -/
theorem ul6_gen_integral (H : UlHyp s (-1 : Matrix (Fin d) (Fin d) ℝ) ρ c ν k θ)
    (Q : Matrix (Fin d) (Fin d) ℝ) {μ : Measure ℝ} [IsFiniteMeasure μ] (G : ℝ → Euc d → ℝ) {B : ℝ}
    (hG : ∀ τ, ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) (G τ))
    (hbd : ∀ i ≤ 4, ∀ τ y, ‖iteratedFDeriv ℝ i (G τ) y‖ ≤ B)
    (hjc : ∀ i ≤ 4, Continuous (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2)) (x : Euc d) :
    generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 (fun y => ∫ τ, G τ y ∂μ) x =
      ∫ τ, generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 (G τ) x ∂μ := by
  obtain ⟨ψ, hψ⟩ := H.hρ
  have hgen : ∀ u : Euc d → ℝ, generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 u x =
      (ul5A Q ν u x + fderiv ℝ u x (c x)) - ulNL s (-1) ρ u x := by
    intro u
    rw [ul5_gen_fixed]
    unfold ulPert
    rw [ul4_inner_eq]
    ring
  obtain ⟨hI, hE⟩ := ul6_loc_integral (μ := μ) Q ν c G hG hbd hjc x
  have hN := ul6_nl_integral (μ := μ) H.hs0 H.hsd (-1) ψ G hG hbd hjc x
  rw [hψ] at hN
  simp only [hgen]
  rw [integral_sub hI hN.1, ← hE, ← hN.2]



/-- **the identity `L(g + ∫_r^T w) = w r`** -/
theorem ul6_gen_Phi (H : UlHyp s (-1 : Matrix (Fin d) (Fin d) ℝ) ρ c ν k θ)
    (Q : Matrix (Fin d) (Fin d) ℝ) {T : ℝ} (hT : 0 ≤ T) {g : Euc d → ℝ} (hg : UlClosure k θ g)
    {w : ℝ → Euc d → ℝ}
    (hw : IsUlBackwardEvolution θ k (fixedViscosityCoeff s (-1) Q ν c ρ) T
      (fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x) w)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) (x : Euc d) :
    generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) r (fun y => g y + ∫ τ in r..T, w τ y) x = w r x := by
  have hureg : UlReg k θ T w := ⟨hw.mem, hw.cont⟩
  have hwU := ul4b_unif_of_reg H.hθ hureg
  obtain ⟨B, hB0, hB⟩ := ul5_ureg_bdd H.hθ hureg (j := 4) H.hk
  set G : ℝ → Euc d → ℝ := fun τ => w (ul4bCl T τ) with hGdef
  have hG : ∀ τ, ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) (G τ) := fun τ => (hB _ (ul4bCl_mem hT τ)).1.1
  have hbd : ∀ i ≤ 4, ∀ τ y, ‖iteratedFDeriv ℝ i (G τ) y‖ ≤ B := fun i hi τ y =>
    (ul3_cb_apply (hB _ (ul4bCl_mem hT τ)).1 hi y).trans (hB _ (ul4bCl_mem hT τ)).2
  have hjc : ∀ i ≤ 4, Continuous (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2) := fun i hi =>
    (ul5_ureg_joint H.hθ hwU (j := 4) H.hk (i := i) hi).comp
      ((Continuous.subtype_mk ((ul4bCl_cont T).comp continuous_fst)
        (fun p => ul4bCl_mem hT p.1)).prodMk continuous_snd)
  set μ : Measure ℝ := volume.restrict (Ioc r T) with hμ
  have : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hΨ : (fun y => g y + ∫ τ in r..T, w τ y) = fun y => g y + ∫ τ, G τ y ∂μ := by
    funext y
    congr 1
    rw [intervalIntegral.integral_of_le hr.2]
    refine setIntegral_congr_fun measurableSet_Ioc fun τ hτ => ?_
    simp only [hGdef, ul4bCl_eq (show τ ∈ Icc (0 : ℝ) T from ⟨hr.1.trans hτ.1.le, hτ.2⟩)]
  have hmemg : HRS.MemCb 4 g := by
    obtain ⟨C, hC, hcb⟩ := ulClosure_cb k 4 H.hk θ H.hθ
    exact (hcb g hg).1
  have hmemΨ : HRS.MemCb 4 (fun y => ∫ τ, G τ y ∂μ) := ul6_memCb (μ := μ) G hG hbd hjc
  rw [hΨ, ul6_gen_const s (-1) Q ν c ρ r 0, ul6_gen_add H.hs0 H.hsd H.hρ Q hmemg hmemΨ x,
    ul6_gen_integral H Q (μ := μ) G hG hbd hjc x]
  -- the fundamental theorem of calculus
  have hcontw : ContinuousOn (fun τ => w τ x) (Icc 0 T) :=
    ul5_contOn_of_joint (ul5_ureg_val H.hθ hwU H.hk0) x
  have hcontg : ContinuousOn (fun τ => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) τ (w τ) x) (Icc 0 T) :=
    ul5_contOn_of_joint hw.classicalSol.cont_time_deriv x
  have hsub : Icc r T ⊆ Icc 0 T := Icc_subset_Icc hr.1 le_rfl
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hr.2 (hcontw.mono hsub)
    (f' := fun τ => -(generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) τ (w τ) x))
    (fun τ hτ => (hw.classicalSol.time_deriv x τ ⟨hr.1.trans_lt hτ.1, hτ.2.trans_le le_rfl⟩).hasDerivWithinAt)
    (((hcontg.mono hsub).intervalIntegrable_of_Icc hr.2).neg)
  rw [intervalIntegral.integral_neg] at hFTC
  have hterm : w T x = generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x :=
    congrFun hw.classicalSol.terminal x
  have hset : ∫ τ, generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 (G τ) x ∂μ =
      ∫ τ in r..T, generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) τ (w τ) x := by
    rw [intervalIntegral.integral_of_le hr.2]
    refine setIntegral_congr_fun measurableSet_Ioc fun τ hτ => ?_
    simp only [hGdef, ul4bCl_eq (show τ ∈ Icc (0 : ℝ) T from ⟨hr.1.trans hτ.1.le, hτ.2⟩)]
    exact ul6_gen_const s (-1) Q ν c ρ 0 τ _ x
  rw [hset]
  linarith

end Phi

section Duh
variable {s ν : ℝ} {ρ : Euc d → ℝ} {σ c : Euc d → Euc d} {θ : Euc d → ℝ}

/-- the family `g + ∫_r^T w` is an evolution -/
theorem ul6_Phi_evolution {k : ℕ} (H : UlHyp s (-1 : Matrix (Fin d) (Fin d) ℝ) ρ c ν k θ)
    (Q : Matrix (Fin d) (Fin d) ℝ) {T : ℝ} (hT : 0 ≤ T) {g : Euc d → ℝ} (hg : UlClosure k θ g)
    {w : ℝ → Euc d → ℝ}
    (hw : IsUlBackwardEvolution θ k (fixedViscosityCoeff s (-1) Q ν c ρ) T
      (fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x) w) :
    IsUlBackwardEvolution θ k (fixedViscosityCoeff s (-1) Q ν c ρ) T g
      (fun r y => g y + ∫ τ in r..T, w τ y) := by
  have hureg : UlReg k θ T w := ⟨hw.mem, hw.cont⟩
  have hwU := ul4b_unif_of_reg H.hθ hureg
  have hval := ul5_ureg_val H.hθ hwU H.hk0
  refine ul6_evol_of_reg H Q (ul6_Phi_reg H hT hureg hg) ?_ ?_
  · funext y; simp
  · intro x r hr
    have hcontw : ContinuousOn (fun τ => w τ x) (Icc 0 T) := ul5_contOn_of_joint hval x
    have hrI : r ∈ Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
    have hint : IntervalIntegrable (fun τ => w τ x) volume r T :=
      (hcontw.mono (Icc_subset_Icc hr.1.le le_rfl)).intervalIntegrable_of_Icc hr.2.le
    have hmeas : StronglyMeasurableAtFilter (fun τ => w τ x) (𝓝 r) volume :=
      (hcontw.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo r hr
    have hca : ContinuousAt (fun τ => w τ x) r := hcontw.continuousAt (Icc_mem_nhds hr.1 hr.2)
    have hd := (intervalIntegral.integral_hasDerivAt_left hint hmeas hca).const_add (g x)
    rw [ul6_gen_Phi H Q hT hg hw hrI x]
    exact hd

end Duh


/-! ### Short time integrals in `C_b^k` and the difference quotient -/

section Dq
variable {s ν : ℝ} {ρ : Euc d → ℝ} {c : Euc d → Euc d} {θ : Euc d → ℝ} {K : ℕ}

lemma ul6_iter_const_mul (a : ℝ) {F : Euc d → ℝ} {x : Euc d} {j : ℕ} (hF : ContDiffAt ℝ j F x) :
    iteratedFDeriv ℝ j (fun y => a * F y) x = a • iteratedFDeriv ℝ j F x := by
  have e : (fun y => a * F y) = fun y => a • F y := rfl
  rw [e]; exact iteratedFDeriv_const_smul_apply' hF

/-- `‖D^j ∫_a^b (w τ - w r) dτ‖ ≤ ε (b - a)` for `a ≤ r ≤ b`, `b - a` small -/
theorem ul6_short_int (H : UlHyp s (-1 : Matrix (Fin d) (Fin d) ℝ) ρ c ν K θ) {T : ℝ} (hT : 0 ≤ T)
    {w : ℝ → Euc d → ℝ} (hw : UlReg K θ T w) {k : ℕ} (hkK : (k : ℝ) + (d : ℝ) / 2 < K) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, ∀ r ∈ Icc a b,
      b - a < δ → ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (fun y => ∫ τ in a..b, (w τ y - w r y)) ∧
        ∀ j ≤ k, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (fun y => ∫ τ in a..b, (w τ y - w r y)) x‖ ≤ ε * (b - a) := by
  intro ε hε
  have hwU : UlUReg K θ T w := ul4b_unif_of_reg H.hθ hw
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb K k hkK θ H.hθ
  obtain ⟨δ, hδ, hδw⟩ := hwU.unif (ε / Ccb) (by positivity)
  obtain ⟨B, hB0, hB⟩ := ul5_ureg_bdd H.hθ hw (j := k) hkK
  refine ⟨δ, hδ, fun a ha b hb r hr hba => ?_⟩
  have hab : a ≤ b := hr.1.trans hr.2
  have hrT : r ∈ Icc (0 : ℝ) T := ⟨ha.1.trans hr.1, hr.2.trans hb.2⟩
  set G : ℝ → Euc d → ℝ := fun τ y => w (ul4bCl T τ) y - w r y with hG
  have hG1 : ∀ τ, ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (G τ) := fun τ =>
    (hB _ (ul4bCl_mem hT τ)).1.1.sub (hB _ hrT).1.1
  have hGd : ∀ τ i, i ≤ k → ∀ y, iteratedFDeriv ℝ i (G τ) y =
      iteratedFDeriv ℝ i (w (ul4bCl T τ)) y - iteratedFDeriv ℝ i (w r) y := fun τ i hi y =>
    iteratedFDeriv_sub_apply ((hB _ (ul4bCl_mem hT τ)).1.1.of_le (by exact_mod_cast hi)).contDiffAt
      ((hB _ hrT).1.1.of_le (by exact_mod_cast hi)).contDiffAt
  have hbd : ∀ i ≤ k, ∀ τ y, ‖iteratedFDeriv ℝ i (G τ) y‖ ≤ B + B := fun i hi τ y => by
    rw [hGd τ i hi y]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact (ul3_cb_apply (hB _ (ul4bCl_mem hT τ)).1 hi y).trans (hB _ (ul4bCl_mem hT τ)).2
    · exact (ul3_cb_apply (hB _ hrT).1 hi y).trans (hB _ hrT).2
  have hjc : ∀ i ≤ k, Continuous (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2) := fun i hi => by
    have e : (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2) = fun p =>
        iteratedFDeriv ℝ i (w (ul4bCl T p.1)) p.2 - iteratedFDeriv ℝ i (w r) p.2 := by
      funext p; exact hGd p.1 i hi p.2
    rw [e]
    refine Continuous.sub ?_ (((hB _ hrT).1.1.continuous_iteratedFDeriv (by exact_mod_cast hi)).comp
      continuous_snd)
    exact (ul5_ureg_joint H.hθ hwU (j := k) hkK (i := i) hi).comp
      ((Continuous.subtype_mk ((ul4bCl_cont T).comp continuous_fst)
        (fun p => ul4bCl_mem hT p.1)).prodMk continuous_snd)
  set μ : Measure ℝ := volume.restrict (Ioc a b) with hμ
  have : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  obtain ⟨hcd, hj'⟩ := ul6_jets (μ := μ) G k hG1 hbd hjc
  have hΨ : (fun y => ∫ τ in a..b, (w τ y - w r y)) = fun y => ∫ τ, G τ y ∂μ := by
    funext y
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_congr_fun measurableSet_Ioc fun τ hτ => ?_
    simp only [hG, ul4bCl_eq (show τ ∈ Icc (0 : ℝ) T from ⟨ha.1.trans hτ.1.le, hτ.2.trans hb.2⟩)]
  rw [hΨ]
  refine ⟨hcd, fun j hj x => ?_⟩
  rw [hj' j hj x]
  have hpt : ∀ τ ∈ Ioc a b, ‖iteratedFDeriv ℝ j (G τ) x‖ ≤ ε := by
    intro τ hτ
    have hτT : τ ∈ Icc (0 : ℝ) T := ⟨ha.1.trans hτ.1.le, hτ.2.trans hb.2⟩
    have hd : |τ - r| < δ := by
      rw [abs_lt]; constructor <;> linarith [hτ.1, hτ.2, hr.1, hr.2]
    have hcl := ul4_closure_sub H.hθ (hw.mem τ hτT) (hw.mem r hrT)
    obtain ⟨hm, hn⟩ := hcb _ hcl
    have h1 : ‖iteratedFDeriv ℝ j (fun y => w τ y - w r y) x‖ ≤ ε := by
      refine (ul3_cb_apply hm hj x).trans (hn.trans ?_)
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hδw τ hτT r hrT hd)
      rw [ENNReal.toReal_ofReal (by positivity)] at this
      calc Ccb * (ulNormE K θ (fun y => w τ y - w r y)).toReal ≤ Ccb * (ε / Ccb) :=
            mul_le_mul_of_nonneg_left this hCcb.le
        _ = ε := by field_simp
    have e : G τ = fun y => w τ y - w r y := by
      funext y; simp only [hG, ul4bCl_eq hτT]
    rw [e]; exact h1
  have hle := norm_integral_le_of_norm_le_const (μ := μ) (C := ε)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hpt))
  have hμr : μ.real univ = b - a := by
    simp [hμ, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]
  rw [hμr] at hle
  exact hle

theorem ul6_dq (H : UlHyp s (-1 : Matrix (Fin d) (Fin d) ℝ) ρ c ν K θ) {T : ℝ} (hT : 0 ≤ T)
    {u w : ℝ → Euc d → ℝ} {g : Euc d → ℝ} (hw : UlReg K θ T w)
    (Duh : ∀ r ∈ Icc (0 : ℝ) T, ∀ y, u r y = g y + ∫ τ in r..T, w τ y) {k : ℕ}
    (hkK : (k : ℝ) + (d : ℝ) / 2 < K) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Icc (0 : ℝ) T, ∀ r' ∈ Icc (0 : ℝ) T, |r - r'| < δ →
      r' ≠ r → ∀ j ≤ k, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (fun y => (r - r')⁻¹ * (u r' y - u r y) - w r y) x‖ ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := ul6_short_int H hT hw hkK ε hε
  have hwU : UlUReg K θ T w := ul4b_unif_of_reg H.hθ hw
  have hval := ul5_ureg_val H.hθ hwU H.hk0
  have hcn : ∀ y, ContinuousOn (fun τ => w τ y) (Icc 0 T) := fun y => ul5_contOn_of_joint hval y
  have hii : ∀ y, ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun τ => w τ y) volume a b := fun y a ha b hb =>
    ((hcn y).mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  refine ⟨δ, hδ, fun r hr r' hr' hd hne j hj x => ?_⟩
  have hrT : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hE : (fun y => (r - r')⁻¹ * (u r' y - u r y) - w r y) =
      fun y => (r - r')⁻¹ * ∫ τ in r'..r, (w τ y - w r y) := by
    funext y
    rw [Duh r' hr' y, Duh r hr y]
    have h1 := intervalIntegral.integral_add_adjacent_intervals (hii y r' hr' r hr) (hii y r hr T hrT)
    have h2 : ∫ τ in r'..r, (w τ y - w r y) = (∫ τ in r'..r, w τ y) - (r - r') * w r y := by
      rw [intervalIntegral.integral_sub (hii y r' hr' r hr) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
    rw [h2]
    have hne' : r - r' ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    field_simp
    linarith
  rw [hE]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- r' < r
    have hd' : r - r' < δ := by rw [abs_lt] at hd; linarith [hd.2]
    obtain ⟨hcd, hb⟩ := hs r' hr' r hr r ⟨hlt.le, le_rfl⟩ hd'
    rw [ul6_iter_const_mul _ ((hcd.of_le (by exact_mod_cast hj)).contDiffAt), norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos (sub_pos.2 hlt)]
    calc (r - r')⁻¹ * ‖iteratedFDeriv ℝ j (fun y => ∫ τ in r'..r, (w τ y - w r y)) x‖
        ≤ (r - r')⁻¹ * (ε * (r - r')) :=
          mul_le_mul_of_nonneg_left (hb j hj x) (inv_nonneg.2 (sub_pos.2 hlt).le)
      _ = ε := by field_simp
  · -- r < r'
    have hlt : r < r' := hgt
    have hd' : r' - r < δ := by rw [abs_lt] at hd; linarith [hd.1]
    obtain ⟨hcd, hb⟩ := hs r hr r' hr' r ⟨le_rfl, hlt.le⟩ hd'
    have e : (fun y => (r - r')⁻¹ * ∫ τ in r'..r, (w τ y - w r y)) =
        fun y => (r' - r)⁻¹ * ∫ τ in r..r', (w τ y - w r y) := by
      funext y
      rw [intervalIntegral.integral_symm, show r - r' = -(r' - r) by ring, inv_neg]
      ring
    rw [e, ul6_iter_const_mul _ ((hcd.of_le (by exact_mod_cast hj)).contDiffAt), norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos (sub_pos.2 hlt)]
    calc (r' - r)⁻¹ * ‖iteratedFDeriv ℝ j (fun y => ∫ τ in r..r', (w τ y - w r y)) x‖
        ≤ (r' - r)⁻¹ * (ε * (r' - r)) :=
          mul_le_mul_of_nonneg_left (hb j hj x) (inv_nonneg.2 (sub_pos.2 hlt).le)
      _ = ε := by field_simp

end Dq

section Duhamel
variable {s ν : ℝ} {ρ : Euc d → ℝ} {σ c : Euc d → Euc d} {θ : Euc d → ℝ}

/-- **the time-integral identity**: `u_a(r) = g_a + ∫_r^T u_{a+1}` -/
theorem ul6_duhamel_time (O : UlOrb d s ν ρ σ c θ) (Q : Matrix (Fin d) (Fin d) ℝ) {K : ℕ}
    (hK : (4 : ℝ) + (d : ℝ) / 2 < K) {T : ℝ} (hT : 0 ≤ T) {g : Euc d → ℝ} (hg : UlClosure K θ g)
    {u w : ℝ → Euc d → ℝ}
    (hu : IsUlBackwardEvolution θ K (fixedViscosityCoeff s (-1) Q ν c ρ) T g u)
    (hw : IsUlBackwardEvolution θ K (fixedViscosityCoeff s (-1) Q ν c ρ) T
      (fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x) w) :
    ∀ r ∈ Icc (0 : ℝ) T, ∀ y, u r y = g y + ∫ τ in r..T, w τ y := by
  have hΦ := ul6_Phi_evolution (O.hyp hK) Q hT hg hw
  intro r hr y
  have := ul_evolution_unique O.hs0 O.hsd θ O.hθ K hK ν O.hν Q (-1) ρ O.hρ c O.smooth hT hu hΦ r hr
  exact congrFun this y

end Duhamel

end HRS.MS.Ul
