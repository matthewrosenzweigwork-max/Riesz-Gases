import HRS.MS.WsStatAux5
import HRS.MS.UlWitTie

/-!
# S9.10, packet 1: continuity in time of the stationary adjoint orbit (the missing `hcont` of the path row)

Worker S910, namespace `HRS.MS.R2Obs`, helper prefix `s910_`.  The full per-row plan is in `S910_PLAN.md` (scratch) and is repeated here.

## Verdict (STEP 1)

Both frozen statements `HRS.Whole.r2_static_observation_family` and `HRS.Whole.r2_static_observation_path` are TRUE and non-vacuous
as stated; no statement change is needed.

* *Family.*  `H` a real Hilbert space with `HilbertBasis e`, `ψ_j ∈ C_b^{4d+40}` (`= J1 d` of S99) with summable norms.  The `tsum`s of
  `r2EllH`, `r2FieldH` are norm-summable (`|a_j(x)| ≤ K w_j`, `|coef_j| ≤ 2√N w_j`, `e` orthonormal), so no junk `0`;
  `G` is an honest centered Gaussian (S99 `exists_gaussian_feature_proof` on `ℓ²`, transported by `e.repr.symm`); the covariance clause is
  `IsCenteredGaussianSeq`; the Edgeworth clause follows from `S99.s99_main_l2` and `Φ ∘ e.repr.symm` in the Stein class exactly as in
  `round2_static_edgeworth_proof` (R2SeAux48/49, with `Ψ = e.repr` instead of `s45_Psi`).
* *Path.*  The hypotheses (adjoint existence, `MemCb k`, summability of the cosine orbit tests) are inhabited (S5.1).  The conclusion
  `R2InitPathEdgeworth` contains continuity of `t ↦ ℓ_x^0(t)` and of the initial orbit field, which for the iid row needed the extra
  hypothesis `hcont` (continuity of `t ↦ propagatorW C 0 t φ_α x`).  The frozen path row has no `hcont`; it is DERIVABLE here: the
  coefficients are stationary quadratic with a thermal (Schwartz) density, uniqueness of classical adjoint solutions is available
  (`ulw_unique`: `ν = β⁻¹ > 0`, `Q = a·1`), and the hypothesis "a classical adjoint solution for terminal time `T` exists" together with
  shift invariance gives `propagatorW C 0 t φ = f (T - t)`, continuous.  This file proves exactly that (`s910_hcont`).
  The rest of the path row follows the iid route (`HRS/MS/R2IidPath*`): `H = s11p_K d`, `e = s11p_basis σ`, features
  `ψ_n = f_{σ n}` (cosine orbit tests), the FAMILY row giving the Gaussian and the expansion in `H`, transported by the bounded linear
  map `J` of `R2IidPathAux2`; new ingredients are the series linearity of the response and the covariance identity (later files).

## Files

`R2ObsAux1` hcont; `R2ObsAux2`/`R2ObsAux3` the family row (`r2_static_observation_family_proof`); `R2ObsAux4` series linearity of the response;
`R2ObsAux5` covariance of series; `R2ObsAux6` covariance of the path Gaussian; `R2ObsAux7`/`R2ObsAux8` identification of the path objects as
images under `J`; `R2ObsAux9` the path row (`r2_static_observation_path_proof`); `R2ObsTie` the `type_of%` ties.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace HRS.MS.R2Obs

open HRS HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s910_stat_gen (D : WholeDyn d) (ρ : Euc d → ℝ) (r r' : ℝ) (g : Euc d → ℝ) (x : Euc d) :
    generatorW (D.coeff (fun _ => ρ)) r g x = generatorW (D.coeff (fun _ => ρ)) r' g x := rfl

/-- Shift invariance of classical adjoint solutions for the stationary coefficient. -/
theorem s910_shift (D : WholeDyn d) (ρ : Euc d → ℝ) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {φ : Euc d → ℝ}
    {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW (D.coeff (fun _ => ρ)) T φ f) :
    IsClassicalAdjointW (D.coeff (fun _ => ρ)) t φ (fun r => f (r + (T - t))) := by
  have hδ : 0 ≤ T - t := by linarith
  have hmem : ∀ r ∈ Set.Icc (0 : ℝ) t, r + (T - t) ∈ Set.Icc (0 : ℝ) T := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  let sh : Set.Icc (0 : ℝ) t → Set.Icc (0 : ℝ) T := fun r => ⟨(r : ℝ) + (T - t), hmem r r.2⟩
  have hsh : Continuous sh :=
    Continuous.subtype_mk (continuous_subtype_val.add continuous_const) _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    exact hf.c2 _ (hmem r hr)
  · intro j hj
    obtain ⟨B, hB⟩ := hf.bdd j hj
    exact ⟨B, fun r hr x => hB _ (hmem r hr) x⟩
  · intro j hj
    have h := hf.cont_c2 j hj
    exact h.comp ((hsh.comp continuous_fst).prodMk continuous_snd)
  · show f (t + (T - t)) = φ
    rw [show t + (T - t) = T by ring]
    exact hf.terminal
  · intro x r hr
    have h1 := hf.time_deriv x (r + (T - t)) ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have h2 := h1.comp_add_const r (T - t)
    rw [s910_stat_gen D ρ r (r + (T - t)) (f (r + (T - t))) x]
    exact h2
  · have h := (hf.cont_time_deriv).comp ((hsh.comp continuous_fst).prodMk continuous_snd)
    refine h.congr fun p => ?_
    exact (s910_stat_gen D ρ _ _ _ _).symm
  · obtain ⟨B, hB⟩ := hf.bdd_time_deriv
    exact ⟨B, fun r hr x => hB _ (hmem r hr) x⟩

theorem s910_cont_f {C : WholeCoeff d} {T : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C T φ f) (x : Euc d) :
    ContinuousOn (fun r => f r x) (Set.Icc (0 : ℝ) T) := by
  have h := hf.cont_c2 0 (by norm_num)
  have h2 : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => f p.1 p.2 := by
    have := h.eval (continuous_const : Continuous fun _ : Set.Icc (0 : ℝ) T × Euc d => (0 : Fin 0 → Euc d))
    refine this.congr fun p => ?_
    simp [iteratedFDeriv_zero_apply]
  have h3 : Continuous fun r : Set.Icc (0 : ℝ) T => f r x := h2.comp (continuous_id.prodMk continuous_const)
  exact continuousOn_iff_continuous_restrict.2 h3

/-- **`hcont` for the thermal stationary coefficient**: `t ↦ U^{0,t} φ (x)` is continuous on `[0,T]`, given a classical adjoint
solution with terminal time `T`. -/
theorem s910_hcont (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (T : ℝ) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {φ : Euc d → ℝ}
    (hex : ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) T φ f)
    (x : Euc d) :
    ContinuousOn (fun t => propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 t φ x)
      (Set.Icc (0 : ℝ) T) := by
  obtain ⟨f, hf⟩ := hex
  have hρeq := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  have hSch : IsSchwartzDensity ρ := by
    rw [hρeq]; exact HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    unfold Matrix.IsSymm; simp
  have hdyn := HRS.MS.S21.s21_dyn_eq (d := d) s a β
  rw [hdyn] at hf ⊢
  have key : ∀ t ∈ Set.Icc (0 : ℝ) T,
      propagatorW (((⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d)).coeff (fun _ => ρ))
        0 t φ = f (T - t) := by
    intro t ht
    have hs := s910_shift (⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d) ρ ht.1 ht.2 hf
    have := HRS.MS.UlW.ulw_unique hd hs0 hsd (-1) (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hQ 0 (inv_pos.2 hβ)
      hSch.1 hSch.2 T ht hs 0 ⟨le_rfl, ht.1⟩
    rw [this]
    show f (0 + (T - t)) = f (T - t)
    rw [zero_add]
  have hc : ContinuousOn (fun t => f (T - t) x) (Set.Icc (0 : ℝ) T) := by
    have h1 := s910_cont_f hf x
    refine h1.comp (continuousOn_const.sub continuousOn_id) fun t ht => ?_
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine hc.congr fun t ht => ?_
  simp only [key t ht]

end HRS.MS.R2Obs

end
