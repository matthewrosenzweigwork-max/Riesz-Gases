import HRS.MC.S7PIRA
import HRS.MC.S7PIB1
import HRS.MC.S7PIS1Drift
import HRS.MC.S7PIS1Eval
import HRS.MC.S7PIDKEval

/-!
# Packet F8 (piR): Riemann-Stieltjes sums for the drift of a cylindrical functional

Proof of `HRS.MC.Sec7.PIPlan.s7_PIF_RS_drift` (statement copied verbatim).  By `s7_PIF_heat_obs_proof` (c) the derivative of the
heat function applied to `𝒟_b((a,b'])` is `∑_i ∂_iF(τ, obs y) obs_i(𝒟_b((a,b']))`; by `s7_PIS_drift_facts_proof` (a) and
`s7_PIS_V_eval_proof`, `obs_i(𝒟_b((a,b'])) = ∫_{(a,b']} eval(b u)(obsTest_i u) du`; the tag coefficients are continuous
(`S7PIR_heat_deriv_cont`) and the densities integrable, so `s7_PIS_RS_basic_proof` (b) applies.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIR

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- integrability of `u ↦ V^{t,u} b(u)` on `(a, c] ⊆ [0,t]` -/
lemma S7PIR_Vint (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    {b : ℝ → NegSobolev d m} (hb : MemLp b 1 (volume.restrict (Set.Icc (0 : ℝ) T)))
    {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {a c : ℝ} (ha : 0 ≤ a) (hct : c ≤ t) :
    IntegrableOn (fun u => Vprop R.D R.ρ m t u (b u)) (Set.Ioc a c) := by
  obtain ⟨J, k, hk, hJ, hm0, hm1, H⟩ := HRS.MC.Sec7.S7PIS1.S7PIS1_data R m hm T hT
  have P : HRS.MC.Sec7.PIE.PIEData J R.D R.ρ T m (k + 1) :=
    ⟨H, by omega, by omega, by push_cast; linarith, by push_cast; linarith⟩
  obtain ⟨CV, hCV0, hCV⟩ := HRS.MC.Sec7.PIE.pie_Vbound H m (k + 1) (by omega) (by omega)
    (by push_cast; linarith) (by push_cast; linarith)
  exact HRS.MC.Sec7.S7PIS1.S7PIS1_intOn P hCV hb ht ha hct

/-- the evaluation against the zero test function vanishes -/
lemma S7PIR_eval_zero_test {m : ℝ} (F : NegSobolev d m) : NegSobolev.eval F (0 : Torus d → ℝ) = 0 :=
  HRS.A33.a33_eval_const F 0

/-- the density of the drift against the `i`-th observation vanishes beyond `t_i` -/
lemma S7PIR_h_zero {m : ℝ} (R : Regime d) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (i : Fin q)
    (F : NegSobolev d m) {u : ℝ} (hu : t i < u) :
    NegSobolev.eval F (obsTest R.D R.ρ t φ i u) = 0 := by
  have : ¬ u ≤ t i := not_le.2 hu
  simp only [obsTest, if_neg this]
  exact S7PIR_eval_zero_test F

/-- the density `u ↦ b(u)(obsTest_i u)` is integrable on `[0,T]` -/
lemma S7PIR_hInt (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    {b : ℝ → NegSobolev d m} (hb : MemLp b 1 (volume.restrict (Set.Icc (0 : ℝ) T)))
    {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T)
    (hφ : ∀ i, Torus.IsSmooth (φ i)) (i : Fin q) :
    IntegrableOn (fun u => NegSobolev.eval (b u) (obsTest R.D R.ρ t φ i u)) (Set.Icc 0 T) := by
  have hVe := HRS.MC.Sec7.S7PIS1.s7_PIS_V_eval_proof R m hm T hT
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  rcases (ht i).1.eq_or_lt with h0 | hpos
  · refine (integrableOn_zero).congr_fun (fun u hu => ?_) measurableSet_Ioc
    exact (S7PIR_h_zero R t φ i (b u) (by rw [← h0]; exact hu.1)).symm
  · have htI : t i ∈ Set.Ioc 0 T := ⟨hpos, (ht i).2⟩
    have hf : IntegrableOn (fun u => S7PIR_evalCLM m (hφ i) (Vprop R.D R.ρ m (t i) u (b u)))
        (Set.Ioc 0 (t i)) :=
      (S7PIR_evalCLM m (hφ i)).integrable_comp (S7PIR_Vint R m hm T hT hb htI le_rfl le_rfl)
    have hind := (hf.integrable_indicator measurableSet_Ioc).integrableOn (s := Set.Ioc 0 T)
    refine hind.congr_fun (fun u hu => ?_) measurableSet_Ioc
    by_cases hut : u ≤ t i
    · rw [Set.indicator_of_mem (show u ∈ Set.Ioc 0 (t i) from ⟨hu.1, hut⟩)]
      simp only [obsTest, if_pos hut]
      rw [S7PIR_evalCLM_apply]
      exact hVe u (t i) hu.1.le hut (ht i).2 (b u) (φ i) (hφ i)
    · rw [Set.indicator_of_notMem (show u ∉ Set.Ioc 0 (t i) from fun h => hut h.2)]
      exact (S7PIR_h_zero R t φ i (b u) (not_le.1 hut)).symm

/-- the `i`-th observation of the drift increment is the integral of the density -/
lemma S7PIR_drift_coord (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    {b : ℝ → NegSobolev d m} (hb : MemLp b 1 (volume.restrict (Set.Icc (0 : ℝ) T)))
    {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T)
    (hφ : ∀ i, Torus.IsSmooth (φ i)) (i : Fin q) (a b' : ℝ) (ha : 0 ≤ a) (hab : a ≤ b') (hbT : b' ≤ T) :
    NegSobolev.eval (pathAt (driftInc R.D R.ρ m T b a b') (t i)) (φ i) =
      ∫ u in Set.Ioc a b', NegSobolev.eval (b u) (obsTest R.D R.ρ t φ i u) := by
  obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7PIS1.s7_PIS_drift_facts_proof R m hm T hT
  have hVe := HRS.MC.Sec7.S7PIS1.s7_PIS_V_eval_proof R m hm T hT
  rw [(hC b hb).1 a b' ha hab hbT (t i) (ht i)]
  -- the integral over `Ioc a b'` of the density reduces to `Ioc a (min b' t_i)`
  have hred : ∫ u in Set.Ioc a b', NegSobolev.eval (b u) (obsTest R.D R.ρ t φ i u) =
      ∫ u in Set.Ioc a (min b' (t i)), NegSobolev.eval (b u) (obsTest R.D R.ρ t φ i u) := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioc
      (Set.Ioc_subset_Ioc_right (min_le_left _ _)) (fun u hu => ?_)
    refine S7PIR_h_zero R t φ i (b u) ?_
    have h1 : ¬ u ≤ min b' (t i) := fun h => hu.2 ⟨hu.1.1, h⟩
    have h2 : u ≤ b' := hu.1.2
    by_contra hcon
    exact h1 (le_min h2 (not_lt.1 hcon))
  rw [hred]
  rcases (ht i).1.eq_or_lt with h0 | hpos
  · have hempty : Set.Ioc a (min b' (t i)) = ∅ :=
      Set.Ioc_eq_empty (not_lt.2 ((min_le_right _ _).trans (by rw [← h0]; exact ha)))
    rw [hempty, Measure.restrict_empty, integral_zero_measure, integral_zero_measure]
    exact HRS.MC.Sec7.S7PIDK.S7PIDK_eval_zero (φ i)
  · have htI : t i ∈ Set.Ioc 0 T := ⟨hpos, (ht i).2⟩
    have hint := S7PIR_Vint R m hm T hT hb htI ha (min_le_right b' (t i))
    have := (S7PIR_evalCLM m (hφ i)).integral_comp_comm hint
    rw [S7PIR_evalCLM_apply] at this
    simp only [S7PIR_evalCLM_apply] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    have hut : u ≤ t i := hu.2.trans (min_le_right _ _)
    simp only [obsTest, if_pos hut]
    exact hVe u (t i) (ha.trans hu.1.le) hut (ht i).2 (b u) (φ i) (hφ i)

/-- **F8 (Riemann-Stieltjes drift integral of a cylindrical functional; deterministic)**. -/
theorem s7_PIF_RS_drift_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (γ : ℝ → Measure (PathSpace d m T)) (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T)
    (hφ : ∀ i, Torus.IsSmooth (φ i)) (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 2 G)
    (w : PathSpace d m T) (b : ℝ → NegSobolev d m) (hb : MemLp b 1 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    IsRS T (fun τ a b' => fderiv ℝ (heatFn γ (fun x => G (obsVec m T t φ x)) τ) (predicted R.D R.ρ w τ)
        (driftInc R.D R.ρ m T b a b'))
      (∫ r in Set.Ioc 0 T, ∑ i, fderiv ℝ (gaussHeat (obsCov R.D R.ρ t φ) G r)
          (obsVec m T t φ (predicted R.D R.ρ w r)) (EuclideanSpace.single i 1) *
        NegSobolev.eval (b r) (obsTest R.D R.ρ t φ i r)) := by
  classical
  have hHO := HRS.MC.Sec7.S7PIB.s7_PIF_heat_obs_proof R m T hT γ hγ t φ ht hφ G hG
  obtain ⟨O, hO⟩ := HRS.MC.Sec7.S7PIS2.s7_PIS_obs_clm_proof m T t φ ht hφ
  have hgc : ∀ i : Fin q, ContinuousOn (fun τ => fderiv ℝ (gaussHeat (obsCov R.D R.ρ t φ) G τ)
      (obsVec m T t φ (predicted R.D R.ρ w τ)) (EuclideanSpace.single i 1)) (Set.Icc 0 T) := by
    intro i
    have h1 := S7PIR_heat_deriv_cont R m hm T hT γ hγ t φ ht hφ G hG w 1 (by norm_num)
    have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => EuclideanSpace ℝ (Fin q)) ℝ
      (fun _ => EuclideanSpace.single i 1)).continuous.comp_continuousOn h1
    refine h2.congr (fun τ _ => ?_)
    simp [iteratedFDeriv_one_apply]
  have hRS := (HRS.MC.Sec7.S7PIS2.s7_PIS_RS_basic_proof T hT).2 (ι := Fin q)
    (fun i τ => fderiv ℝ (gaussHeat (obsCov R.D R.ρ t φ) G τ)
      (obsVec m T t φ (predicted R.D R.ρ w τ)) (EuclideanSpace.single i 1))
    (fun i u => NegSobolev.eval (b u) (obsTest R.D R.ρ t φ i u)) hgc
    (fun i => S7PIR_hInt R m hm T hT hb t φ ht hφ i)
  refine S7PIR_isRS_congr hRS (fun τ a b' ha haτ hτb hbT => ?_)
  have hτ : τ ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans haτ, hτb.trans hbT⟩
  rw [(hHO.2.2 O hO τ hτ _).1]
  simp only [ContinuousLinearMap.comp_apply]
  rw [S7PIR_clm_expand]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hi : (O (driftInc R.D R.ρ m T b a b')) i =
      ∫ u in Set.Ioc a b', NegSobolev.eval (b u) (obsTest R.D R.ρ t φ i u) := by
    rw [hO]
    exact S7PIR_drift_coord R m hm T hT hb t φ ht hφ i a b' ha (haτ.trans hτb) hbT
  rw [hi, mul_comm]

end HRS.MC.Sec7.S7PIR

end
