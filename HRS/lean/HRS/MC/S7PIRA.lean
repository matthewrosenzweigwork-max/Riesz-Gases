import HRS.MC.S7PIDefs
import HRS.MC.S7PIS2Obs
import HRS.MC.S7PIS2RS
import HRS.MC.S7PIS3Heat
import HRS.MC.S7PIS3Law
import HRS.MC.S7PIS3Cov3
import HRS.MC.S7PIS1Path2
import HRS.Main.A33Aux14

/-!
# Packets F8, F9 (piR), part A: shared helpers for the Riemann-Stieltjes sums of cylindrical functionals

* `S7PIR_isRS_congr`: `IsRS` only depends on the summand for tags in their intervals;
* `S7PIR_evalCLM`: `F ↦ F(φ)` is a continuous linear functional on `E_m` for smooth `φ`;
* finite-dimensional expansions of a continuous linear / bilinear form on `ℝ^q` in the standard basis;
* continuity in the tag of `τ ↦ D^j gaussHeat obsCov G τ (obs (𝖳_τ w))` on `[0,T]` (`s7_PIH_heat_cont_proof`, `s7_PIS_path_facts_proof`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIR

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- `IsRS` only sees the summand at tags in their intervals inside `[0,T]`. -/
lemma S7PIR_isRS_congr {T : ℝ} {S S' : ℝ → ℝ → ℝ → ℝ} {I : ℝ} (h : IsRS T S I)
    (hSS : ∀ τ a b : ℝ, 0 ≤ a → a ≤ τ → τ ≤ b → b ≤ T → S τ a b = S' τ a b) : IsRS T S' I := by
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := h ε hε
  refine ⟨δ, hδ, fun n u τ hu hu0 huT htag hmesh => ?_⟩
  have key := H n u τ hu hu0 huT htag hmesh
  have e : ∑ i : Fin n, S' (τ i) (u i.castSucc) (u i.succ) = ∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    symm
    apply hSS
    · rw [← hu0]; exact hu.monotone (Fin.zero_le _)
    · exact (htag i).1
    · exact (htag i).2
    · rw [← huT]; exact hu.monotone (Fin.le_last _)
  rw [e]; exact key

/-- `F ↦ F(φ)` as a continuous linear functional on `E_m` (smooth `φ`). -/
def S7PIR_evalCLM (m : ℝ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : NegSobolev d m →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun F => NegSobolev.eval F φ
      map_add' := fun F F' => HRS.A33.a33_eval_add_left F F' (HRS.A33.a33_ws_smooth m hφ)
      map_smul' := fun c F => HRS.MC.Sec7.S7PIS2.S7PIS2_eval_smul c F φ }
    (sobolevNorm m φ) (fun F => by
      have := HRS.A33.a33_abs_eval_le F (HRS.A33.a33_ws_smooth m hφ)
      simpa [Real.norm_eq_abs, mul_comm] using this)

lemma S7PIR_evalCLM_apply (m : ℝ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (F : NegSobolev d m) :
    S7PIR_evalCLM m hφ F = NegSobolev.eval F φ := rfl

/-- A continuous linear functional on `ℝ^q` expanded in the standard basis. -/
lemma S7PIR_clm_expand {q : ℕ} (L : EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin q)) :
    L v = ∑ i, v i * L (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin q) ℝ).sum_repr v]
  simp [map_sum, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]

/-- A continuous bilinear form on `ℝ^q` expanded in the standard basis. -/
lemma S7PIR_cmm2_expand {q : ℕ}
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin q)) ℝ)
    (v : Fin 2 → EuclideanSpace ℝ (Fin q)) :
    B v = ∑ i, ∑ j, v 0 i * v 1 j * B ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] := by
  have hv : v = fun k => ∑ i, (v k i) • (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin q)) := by
    funext k
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin q) ℝ).sum_repr (v k)]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
  have h := MultilinearMap.map_sum B.toMultilinearMap
    (fun (k : Fin 2) (i : Fin q) => (v k i) • (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin q)))
  have h2 : B v = ∑ r : Fin 2 → Fin q, B (fun k => (v k (r k)) • (EuclideanSpace.single (r k) (1 : ℝ) : EuclideanSpace ℝ (Fin q))) := by
    conv_lhs => rw [hv]
    exact h
  rw [h2]
  simp_rw [B.map_smul_univ]
  refine Eq.trans ((finTwoArrowEquiv (Fin q)).symm.sum_comp _).symm ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [finTwoArrowEquiv, Fin.prod_univ_two]
  left
  congr 1
  funext k
  fin_cases k <;> rfl

/-- `τ ↦ obsVec (𝖳_τ w)` is continuous on `[0,T]`. -/
lemma S7PIR_obs_pred_cont (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T)
    (hφ : ∀ i, Torus.IsSmooth (φ i)) (w : PathSpace d m T) :
    ContinuousOn (fun τ => obsVec m T t φ (predicted R.D R.ρ w τ)) (Set.Icc 0 T) := by
  obtain ⟨O, hO⟩ := HRS.MC.Sec7.S7PIS2.s7_PIS_obs_clm_proof m T t φ ht hφ
  have hc := (HRS.MC.Sec7.S7PIS1.s7_PIS_path_facts_proof R m hm T hT).2.2 w
  rw [continuousOn_iff_continuous_domRestrict]
  have : Continuous fun u : Set.Icc (0 : ℝ) T => O (predicted R.D R.ρ w u) := O.continuous.comp hc
  refine this.congr (fun u => ?_)
  simp [Set.domRestrict, hO]

/-- The tag dependence of the integrands: `τ ↦ D^j F(τ, obs(𝖳_τ w))` is continuous on `[0,T]`, `j ≤ 2`. -/
lemma S7PIR_heat_deriv_cont (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (γ : ℝ → Measure (PathSpace d m T)) (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T)
    (hφ : ∀ i, Torus.IsSmooth (φ i)) (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 2 G)
    (w : PathSpace d m T) (j : ℕ) (hj : j ≤ 2) :
    ContinuousOn (fun τ => iteratedFDeriv ℝ j (gaussHeat (obsCov R.D R.ρ t φ) G τ)
      (obsVec m T t φ (predicted R.D R.ρ w τ))) (Set.Icc 0 T) := by
  have law := HRS.MC.Sec7.S7PIS3.s7_PIS_obs_law_proof R m T hT γ hγ t φ ht hφ
  have hcov := HRS.MC.Sec7.S7PIS3.s7_PIS_cov_struct_proof' R T hT t φ ht hφ
  have hS : ∀ i j, ContinuousOn (fun u => obsCov R.D R.ρ t φ u i j) (Set.Icc 0 T) := hcov.2.2.2.2
  have hpsd : ∀ u ∈ Set.Icc (0 : ℝ) T, (obsCov R.D R.ρ t φ u).PosSemidef := fun u hu => (law u hu).1
  have H3 := HRS.MC.Sec7.S7PIS3.s7_PIH_heat_cont_proof T (obsCov R.D R.ρ t φ) hS hpsd G 2 hG j hj
  have hp : ContinuousOn (fun τ => (τ, obsVec m T t φ (predicted R.D R.ρ w τ))) (Set.Icc 0 T) :=
    continuousOn_id.prodMk (S7PIR_obs_pred_cont R m hm T hT t φ ht hφ w)
  have hmaps : Set.MapsTo (fun τ => (τ, obsVec m T t φ (predicted R.D R.ρ w τ))) (Set.Icc 0 T)
      (Set.Icc 0 T ×ˢ Set.univ) := fun τ hτ => ⟨hτ, Set.mem_univ _⟩
  have hcomp := H3.comp hp hmaps
  exact hcomp.congr (fun τ _ => rfl)

end HRS.MC.Sec7.S7PIR

end
