import HRS.MD.EQLZLevelStat
import HRS.MD.EQLZLevelCore
import HRS.MD.EQLZSgSmooth
import HRS.MD.EQLZSgSemigroup
import HRS.MD.EQLZSgSymm
import HRS.MD.EQLZSgInvariant
import HRS.MD.EQLZSgEnergy
import HRS.MD.EQLZMkMarkov
import HRS.MD.EQLZMkFdd
import HRS.MD.EQLZStat
import HRS.MD.EQLZRev
import HRS.MD.EQLZCmp
import HRS.MD.EQLZDl

/-!
# EQ-LZ packet LN: the level-`lev` maximal inequality (`eqlz_level`), proof

`LevelMaximal` from the proved pieces.  A stationary level flow `Y*` with `Law(Z*_0) = π_lev` is built in
`HRS.MD.EQLZLevelStat`; `eqlz_mk_fdd` gives `HasFDD` for `Y` (initial law `ρ π_lev`) and `Y*` (initial law `π_lev`);
the grid bound for the stationary process is `HRS.MD.EQLZLevelCore.lzlc_grid_bound` (discrete Lyons-Zheng lemma,
`eqlz_stat`, `eqlz_rev`, `eqlz_sg_energy`, `eqlz_mk_markov`); `eqlz_cmp` transfers it to `Y` with the factor `c`.
The hypotheses are the types of the PROVED `_proof` theorems of the pieces.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal
open HRS HRS.MD.EQLZ HRS.MD.EQLZLevelStat HRS.MD.EQLZLevelCore

namespace HRS.MD.EQLZLevel

theorem lzl_const_le (c T δ x : ℝ) (m : ℕ) (hm : 1 ≤ m) (hT : 0 ≤ T) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hδ : δ = T / m) :
    c * (18 * ((m : ℝ) * (2 * (δ * x))) + 2 * ((m : ℝ) + 1) * (δ * x)) ≤ c * (40 * T * x) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmδ : (m : ℝ) * δ = T := by rw [hδ]; field_simp
  have hδT : δ ≤ T := by
    rw [hδ, div_le_iff₀ hm0]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have e : 18 * ((m : ℝ) * (2 * (δ * x))) + 2 * ((m : ℝ) + 1) * (δ * x) =
      38 * ((m : ℝ) * δ) * x + 2 * δ * x := by ring
  rw [e, hmδ]
  apply mul_le_mul_of_nonneg_left _ hc
  nlinarith [mul_nonneg (sub_nonneg.2 hδT) hx]

theorem eqlz_level_proof
    (hsg_smooth : type_of% @HRS.MD.EQLZSgSmooth.eqlz_sg_smooth_proof)
    (hsg_semigroup : type_of% @HRS.MD.EQLZSgSemigroup.eqlz_sg_semigroup_proof)
    (hsg_symm : type_of% @HRS.MD.EQLZSgSymm.eqlz_sg_symm_proof)
    (hsg_invariant : type_of% @HRS.MD.EQLZSgInvariant.eqlz_sg_invariant_proof)
    (hsg_energy : type_of% @HRS.MD.EQLZSgEnergy.eqlz_sg_energy_proof)
    (hmk_markov : type_of% @HRS.MD.EQLZMk.eqlz_mk_markov_proof)
    (hmk_fdd : type_of% @HRS.MD.EQLZMk.eqlz_mk_fdd_proof)
    (hstat : type_of% @HRS.MD.EQLZStat.eqlz_stat_proof) (hrev : type_of% @HRS.MD.EQLZRev.eqlz_rev_proof)
    (hcmp : type_of% @HRS.MD.EQLZCmp.eqlz_cmp_proof)
    (hdl : type_of% @HRS.MD.EQLZDl.eqlz_dl_proof) :
    LevelMaximal := by
  intro d N hNd D hM hV hβ lev Ω mΩ P hP ℱ W' Y₀ Y hY c ρ hρ hρb hlaw F hF a T ha hT m hm
  have hU := b15d_U_isSmooth_proof (N := N) D hV lev
  set π := d1_gibbsMeasure D.invβ (b15d_U (N := N) D lev) with hπ
  haveI hπp : IsProbabilityMeasure π := d3a_gibbs_isProb hU
  have hsm : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus (N * d) → ℝ, Torus.IsSmooth φ →
      Torus.IsSmooth (d1_P hNd hβ hU t φ) := fun t ht φ hφ => hsg_smooth hNd hβ hU ht hφ
  have hsemi : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ φ : Torus (N * d) → ℝ, Torus.IsSmooth φ →
      d1_P hNd hβ hU (s + t) φ = d1_P hNd hβ hU s (d1_P hNd hβ hU t φ) :=
    fun s t hs ht φ hφ => hsg_semigroup hNd hβ hU hs ht hφ
  have hsymm : ∀ t : ℝ, 0 ≤ t → ∀ φ ψ : Torus (N * d) → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
      ∫ x, ψ x * d1_P hNd hβ hU t φ x ∂π = ∫ x, φ x * d1_P hNd hβ hU t ψ x ∂π :=
    fun t ht φ ψ hφ hψ => hsg_symm hNd hβ hU ht hφ hψ
  have hinv : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus (N * d) → ℝ, Torus.IsSmooth φ →
      ∫ x, d1_P hNd hβ hU t φ x ∂π = ∫ x, φ x ∂π :=
    fun t ht φ hφ => hsg_invariant hNd hβ hU ht hφ
  have hen : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus (N * d) → ℝ, Torus.IsSmooth φ →
      ∫ x, φ x * (φ x - d1_P hNd hβ hU t φ x) ∂π ≤ t * (D.invβ * ∫ x, ‖Torus.grad φ x‖ ^ 2 ∂π) ∧
        ∫ x, (φ x - d1_P hNd hβ hU t φ x) ^ 2 ∂π ≤ ∫ x, φ x * (φ x - d1_P hNd hβ hU t φ x) ∂π :=
    fun t ht φ hφ => hsg_energy hNd hβ hU ht hφ
  -- the stationary level flow
  obtain ⟨Ω', mΩ', P', hP', ℱ', W'', Y₀', Y', hY', hlaw'⟩ := lzl_exists_stationary (N := N) D hV lev π
  have hfdd' : HasFDD hNd hβ hU P' (levelProc Y') π := by
    have := hmk_fdd hNd D hM hV hβ lev hsm P' ℱ' W'' Y₀' Y' hY'
    rwa [hlaw'] at this
  have hfdd : HasFDD hNd hβ hU P (levelProc Y) (π.withDensity fun x => ENNReal.ofReal (ρ x)) := by
    have := hmk_fdd hNd D hM hV hβ lev hsm P ℱ W' Y₀ Y hY
    rwa [hlaw] at this
  have hZℱ' : ∀ r, Measurable[ℱ' r] (levelProc Y' r) := fun r =>
    HRS.MD.EQLZMk.lzmk_levelProc_meas hY'.sol.adapted r
  have hZℱ : ∀ r, Measurable[ℱ r] (levelProc Y r) := fun r =>
    HRS.MD.EQLZMk.lzmk_levelProc_meas hY.sol.adapted r
  have hZ' : ∀ t : ℝ, 0 ≤ t → Measurable (levelProc Y' t) := fun t _ => (hZℱ' t).mono (ℱ'.le t) le_rfl
  have hZ : ∀ t : ℝ, 0 ≤ t → Measurable (levelProc Y t) := fun t _ => (hZℱ t).mono (ℱ.le t) le_rfl
  have hmarkov' : ∀ φ : Torus (N * d) → ℝ, Torus.IsSmooth φ → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      P'[fun ω => φ (levelProc Y' t ω) | ℱ' s] =ᵐ[P'] fun ω => d1_P hNd hβ hU (t - s) φ (levelProc Y' s ω) :=
    fun φ hφ s t hs hst => hmk_markov hNd D hM hV hβ lev P' ℱ' W'' Y₀' Y' hY' hφ hs hst
  set δ : ℝ := T / m with hδdef
  have hδ : 0 ≤ δ := by positivity
  set I : ℝ := ∫ x, ‖Torus.grad F x‖ ^ 2 ∂π with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
  have hstar := lzlc_grid_bound hNd hβ hU hsm hsemi hsymm hinv hen hstat hrev hdl P' ℱ' (levelProc Y') hZℱ'
    hmarkov' hfdd' hF a δ ha hδ m
  -- comparison
  have ht0 : ∀ i : Fin (m + 1), 0 ≤ a + ((i : ℕ) : ℝ) * δ := fun i => by positivity
  have htm : Monotone (fun i : Fin (m + 1) => a + ((i : ℕ) : ℝ) * δ) := by
    intro i j hij
    have : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
    simp only
    nlinarith
  have hc : 0 ≤ c := le_trans (hρb 0).1 (hρb 0).2
  have hcmpl := hcmp hNd hβ hU P P' (levelProc Y) (levelProc Y') hZ hZ' c ρ hρ (fun x => (hρb x).1)
    (fun x => (hρb x).2) hfdd hfdd' (m + 1) (fun i : Fin (m + 1) => a + ((i : ℕ) : ℝ) * δ) htm ht0
  set Ψ : (Fin (m + 1) → Torus (N * d)) → ℝ≥0∞ := fun z =>
    ⨆ j : Fin (m + 1), ENNReal.ofReal ((F (z j) - F (z 0)) ^ 2) with hΨ
  have hFc : Continuous F := HRS.MD.EQLZDet.lzdet_continuous hF
  have hΨm : Measurable Ψ :=
    Measurable.iSup fun j => ENNReal.measurable_ofReal.comp
      (((lzlc_ev hFc j).sub (lzlc_ev hFc 0)).pow_const 2)
  have hGm : Measurable (fun ω => (levelProc Y 0 ω, fun i : Fin (m + 1) => levelProc Y (a + ((i : ℕ) : ℝ) * δ) ω)) :=
    (hZ 0 le_rfl).prodMk (measurable_pi_iff.2 fun i => hZ _ (ht0 i))
  have hGm' : Measurable (fun ω => (levelProc Y' 0 ω, fun i : Fin (m + 1) => levelProc Y' (a + ((i : ℕ) : ℝ) * δ) ω)) :=
    (hZ' 0 le_rfl).prodMk (measurable_pi_iff.2 fun i => hZ' _ (ht0 i))
  have e1 : ∫⁻ ω, ⨆ j : Fin (m + 1),
        ENNReal.ofReal ((F (levelProc Y (a + (j : ℕ) * δ) ω) - F (levelProc Y a ω)) ^ 2) ∂P =
      ∫⁻ p, Ψ p.2 ∂(P.map (fun ω => (levelProc Y 0 ω,
        fun i : Fin (m + 1) => levelProc Y (a + ((i : ℕ) : ℝ) * δ) ω))) := by
    rw [lintegral_map (f := fun p : Torus (N * d) × (Fin (m + 1) → Torus (N * d)) => Ψ p.2)
      (hΨm.comp measurable_snd) hGm]
    simp [hΨ]
  have e6 : ∫⁻ p, Ψ p.2 ∂(P'.map (fun ω => (levelProc Y' 0 ω,
        fun i : Fin (m + 1) => levelProc Y' (a + ((i : ℕ) : ℝ) * δ) ω))) =
      ∫⁻ ω, ⨆ j : Fin (m + 1),
        ENNReal.ofReal ((F (levelProc Y' (a + (j : ℕ) * δ) ω) - F (levelProc Y' a ω)) ^ 2) ∂P' := by
    rw [lintegral_map (f := fun p : Torus (N * d) × (Fin (m + 1) → Torus (N * d)) => Ψ p.2)
      (hΨm.comp measurable_snd) hGm']
    simp [hΨ]
  have hρm : Measurable fun p : Torus (N * d) × (Fin (m + 1) → Torus (N * d)) => ENNReal.ofReal (ρ p.1) :=
    ENNReal.measurable_ofReal.comp (hρ.comp measurable_fst)
  calc ∫⁻ ω, ⨆ j : Fin (m + 1),
        ENNReal.ofReal ((F (levelProc Y (a + (j : ℕ) * δ) ω) - F (levelProc Y a ω)) ^ 2) ∂P
      = ∫⁻ p, Ψ p.2 ∂(P'.map (fun ω => (levelProc Y' 0 ω,
          fun i : Fin (m + 1) => levelProc Y' (a + ((i : ℕ) : ℝ) * δ) ω))).withDensity
            (fun p => ENNReal.ofReal (ρ p.1)) := by rw [e1, hcmpl]
    _ = ∫⁻ p, ENNReal.ofReal (ρ p.1) * Ψ p.2 ∂(P'.map (fun ω => (levelProc Y' 0 ω,
          fun i : Fin (m + 1) => levelProc Y' (a + ((i : ℕ) : ℝ) * δ) ω))) :=
        lintegral_withDensity_eq_lintegral_mul _ hρm (hΨm.comp measurable_snd)
    _ ≤ ∫⁻ p, ENNReal.ofReal c * Ψ p.2 ∂(P'.map (fun ω => (levelProc Y' 0 ω,
          fun i : Fin (m + 1) => levelProc Y' (a + ((i : ℕ) : ℝ) * δ) ω))) :=
        lintegral_mono fun p => by gcongr; exact (hρb p.1).2
    _ = ENNReal.ofReal c * ∫⁻ p, Ψ p.2 ∂(P'.map (fun ω => (levelProc Y' 0 ω,
          fun i : Fin (m + 1) => levelProc Y' (a + ((i : ℕ) : ℝ) * δ) ω))) :=
        lintegral_const_mul _ (hΨm.comp measurable_snd)
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (18 * ((m : ℝ) * (2 * (δ * (D.invβ * I)))) +
          2 * ((m : ℝ) + 1) * (δ * (D.invβ * I))) := by
        rw [e6]; gcongr
    _ = ENNReal.ofReal (c * (18 * ((m : ℝ) * (2 * (δ * (D.invβ * I)))) +
          2 * ((m : ℝ) + 1) * (δ * (D.invβ * I)))) := (ENNReal.ofReal_mul hc).symm
    _ ≤ ENNReal.ofReal (c * (40 * T * D.invβ * I)) := by
        apply ENNReal.ofReal_le_ofReal
        have := lzl_const_le c T δ (D.invβ * I) m hm hT hc (mul_nonneg hβ.le hI0) hδdef
        calc _ ≤ c * (40 * T * (D.invβ * I)) := this
          _ = _ := by ring

end HRS.MD.EQLZLevel

end
