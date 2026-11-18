import HRS.MC.CepE5bAux18
import HRS.MC.CepE5cAux1
import HRS.MC.CepE5a

/-!
# Packet CEPE5C, auxiliary 2: the concrete pair estimate and integrability of the defect integrals
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5c

open HRS HRS.MC.Cepa HRS.MC.CepE4 HRS.MC.CepE5b

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- The pathwise integral `∫_0^T |G_n(Z^n_s)|² ds`. -/
def e5c_h (J : ℝ → Ch N → Ch N) (Z : ℕ → ℝ → Ω → Ch N) (T : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..T, ‖(n : ℝ) • (Z n s ω - J n (Z n s ω))‖ ^ 2

theorem e5c_h_nonneg {J : ℝ → Ch N → Ch N} {Z : ℕ → ℝ → Ω → Ch N} {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (ω : Ω) :
    0 ≤ e5c_h J Z T n ω :=
  intervalIntegral.integral_nonneg hT fun s _ => by positivity

theorem e5c_h_integrable [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} {R : ℝ} (hR : ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) {T : ℝ} (hT : 0 ≤ T)
    {n : ℕ} (hn : 1 ≤ n) : Integrable (e5c_h J Z T n) P := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hZc, hZF, heq⟩ := hZ n hn
  have hGc : Continuous (e5b_G J (n : ℝ)) := e5b_G_cont hJ hnpos
  have hFc : Continuous F := hF.continuous
  have hGb : ∀ z, ‖e5b_G J (n : ℝ) z‖ ≤ ‖e5b_G J (n : ℝ) 0‖ + (n : ℝ) * ‖z‖ := e5b_G_growth hJ hnpos
  have hFb : ∀ z, ‖F z‖ ≤ ‖F 0‖ + (L : ℝ) * ‖z‖ := e4_lip_growth hF
  have hLp : (0 : ℝ) ≤ L := L.2
  have hBc : Continuous fun z => -((n : ℝ) • (z - J n z)) + F z := hGc.neg.add hFc
  have hBb : ∀ z, ‖-((n : ℝ) • (z - J n z)) + F z‖ ≤ (‖e5b_G J (n : ℝ) 0‖ + ‖F 0‖) + ((n : ℝ) + L) * ‖z‖ :=
    fun z => by
    have h1 := norm_add_le (-((n : ℝ) • (z - J n z))) (F z)
    rw [norm_neg] at h1
    have h2 : ‖(n : ℝ) • (z - J n z)‖ ≤ ‖e5b_G J (n : ℝ) 0‖ + (n : ℝ) * ‖z‖ := hGb z
    have h3 := hFb z
    nlinarith
  obtain ⟨A, hS⟩ := e4_setup_of_solution hW' hπ (σ' := σ') hR hBc (by positivity) (by positivity) hBb
    (Z := Z n) hZc hZF heq hT
  have qGG : E4Quad fun z => ‖e5b_G J (n : ℝ) z‖ ^ 2 := e5b_quad_sqnorm hGc (norm_nonneg _) hnpos.le hGb
  have hI := e4Q_int_inner hS hT le_rfl qGG
  refine hI.congr (Eventually.of_forall fun ω => ?_)
  simp only [e5c_h]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le hT] at hs
  simp [e4_clamp, max_eq_left hs.1, e5b_G]

theorem e5c_X_eq {J : ℝ → Ch N → Ch N} {Z : ℕ → ℝ → Ω → Ch N} {T : ℝ} (n : ℕ) :
    (∫ ω, (∫ s in (0 : ℝ)..T, (1 / (n : ℝ)) * ‖(n : ℝ) • (Z n s ω - J n (Z n s ω))‖ ^ 2) ∂P) =
      (1 / (n : ℝ)) * ∫ ω, e5c_h J Z T n ω ∂P := by
  simp_rw [intervalIntegral.integral_const_mul]
  rw [integral_const_mul]
  rfl

/-- The pair estimate (almost surely, for all pairs and times simultaneously). -/
theorem e5c_pair_ae [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    {π : Ω → Equiv.Perm (Fin N)}
    {a : ℝ} {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N}
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ (m n : ℕ) (t : ℝ), 1 ≤ m → 1 ≤ n → 0 ≤ t → t ≤ T →
      ‖Z m t ω - Z n t ω‖ ^ 2 ≤ Real.exp (2 * L * T) *
        ((1 / (m : ℝ) + 1 / (n : ℝ)) * (e5c_h J Z T m ω + e5c_h J Z T n ω)) := by
  have hae : ∀ᵐ ω ∂P, ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t → Z n t ω = z₀ ω +
      (∫ s in (0 : ℝ)..t, (-((n : ℝ) • (Z n s ω - J n (Z n s ω))) + F (Z n s ω))) +
        σ' • cep_noise π W' t ω := by
    rw [ae_all_iff]
    intro n
    by_cases hn : 1 ≤ n
    · filter_upwards [(hZ n hn).2.2] with ω h _
      exact h
    · exact Eventually.of_forall fun ω h => absurd h hn
  filter_upwards [hae] with ω hω m n t hm hn ht0 htT
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hGm : Continuous fun z : Ch N => (m : ℝ) • (z - J m z) := (hJ.lip m hm').continuous
  have hGn : Continuous fun z : Ch N => (n : ℝ) • (z - J n z) := (hJ.lip n hn').continuous
  have hZmc : Continuous fun s => Z m s ω := (hZ m hm).1 ω
  have hZnc : Continuous fun s => Z n s ω := (hZ n hn).1 ω
  have h5a := HRS.MC.CepE5a.cep_E5a_pathwise_yosida_proof hJ hF hm' hn' (z₀ := z₀ ω)
    (Zm := fun s => Z m s ω) (Zn := fun s => Z n s ω) (noise := fun t => σ' • cep_noise π W' t ω)
    hZmc hZnc (hω m hm) (hω n hn) t ht0
  set gm : ℝ → Ch N := fun s => (m : ℝ) • (Z m s ω - J m (Z m s ω)) with hgm
  set gn : ℝ → Ch N := fun s => (n : ℝ) • (Z n s ω - J n (Z n s ω)) with hgn
  have cm : Continuous gm := hGm.comp hZmc
  have cn : Continuous gn := hGn.comp hZnc
  have hI1 : (∫ s in (0 : ℝ)..t, |inner ℝ (gm s) (gn s)|) ≤ ∫ s in (0 : ℝ)..T, |inner ℝ (gm s) (gn s)| := by
    refine intervalIntegral.integral_mono_interval le_rfl ht0 htT
      (Eventually.of_forall fun s => abs_nonneg _) ?_
    exact (continuous_abs.comp (cm.inner cn)).intervalIntegrable _ _
  have hI2 : (∫ s in (0 : ℝ)..T, |inner ℝ (gm s) (gn s)|) ≤
      ∫ s in (0 : ℝ)..T, ((1 / 2) * ‖gm s‖ ^ 2 + (1 / 2) * ‖gn s‖ ^ 2) := by
    refine intervalIntegral.integral_mono_on hT ((continuous_abs.comp (cm.inner cn)).intervalIntegrable _ _)
      ((((cm.norm.pow 2).const_mul _).add ((cn.norm.pow 2).const_mul _)).intervalIntegrable _ _) fun s _ => ?_
    have h1 := abs_real_inner_le_norm (gm s) (gn s)
    nlinarith [sq_nonneg (‖gm s‖ - ‖gn s‖), norm_nonneg (gm s), norm_nonneg (gn s)]
  have hI3 : (∫ s in (0 : ℝ)..T, ((1 / 2) * ‖gm s‖ ^ 2 + (1 / 2) * ‖gn s‖ ^ 2)) =
      (1 / 2) * (e5c_h J Z T m ω + e5c_h J Z T n ω) := by
    have hA : IntervalIntegrable (fun s => (1 / 2 : ℝ) * ‖gm s‖ ^ 2) volume 0 T :=
      ((cm.norm.pow 2).const_mul _).intervalIntegrable _ _
    have hB : IntervalIntegrable (fun s => (1 / 2 : ℝ) * ‖gn s‖ ^ 2) volume 0 T :=
      ((cn.norm.pow 2).const_mul _).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hA hB, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    simp only [e5c_h, hgm, hgn]
    ring
  have hexp : Real.exp (2 * L * t) ≤ Real.exp (2 * L * T) :=
    Real.exp_le_exp.2 (by have := (L.2 : (0 : ℝ) ≤ L); nlinarith)
  have hnn : 0 ≤ (1 / (m : ℝ) + 1 / (n : ℝ)) := by positivity
  have hE := Real.exp_nonneg (2 * (L : ℝ) * T)
  have hh : 0 ≤ e5c_h J Z T m ω + e5c_h J Z T n ω :=
    add_nonneg (e5c_h_nonneg hT m ω) (e5c_h_nonneg hT n ω)
  have hint : (∫ s in (0 : ℝ)..t, |inner ℝ (gm s) (gn s)|) ≤ (1 / 2) * (e5c_h J Z T m ω + e5c_h J Z T n ω) :=
    hI1.trans (hI2.trans hI3.le)
  have hint0 : 0 ≤ ∫ s in (0 : ℝ)..t, |inner ℝ (gm s) (gn s)| :=
    intervalIntegral.integral_nonneg ht0 fun s _ => abs_nonneg _
  calc ‖Z m t ω - Z n t ω‖ ^ 2 ≤ Real.exp (2 * L * t) * (2 * (1 / (m : ℝ) + 1 / (n : ℝ))) *
        ∫ s in (0 : ℝ)..t, |inner ℝ (gm s) (gn s)| := h5a
    _ ≤ Real.exp (2 * L * T) * (2 * (1 / (m : ℝ) + 1 / (n : ℝ))) *
        ((1 / 2) * (e5c_h J Z T m ω + e5c_h J Z T n ω)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hexp (by positivity)) hint hint0 (by positivity)
    _ = _ := by ring

end HRS.MC.CepE5c
