import HRS.MS.R26T8AA02f

/-!
# S8.2 T8A A02: `r26t8a_canonical_triple_and_bounds` (Pro contract, verbatim)
`G` = `tripleG` off collisions, `0` on collisions.  Symmetry (A02a), measurability (A02e), integrable zero rows (A01),
envelope (A01b) and the `repeatedB` bound (A02f); constants uniform in `ρ` by uniqueness of the thermal density.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

set_option maxHeartbeats 6400000 in
theorem r26t8a_canonical_triple_and_bounds (d : ℕ) (hd : 2 ≤ d)
    (a beta M : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) :
    ∃ C M' : ℝ, 0 ≤ C ∧ 0 ≤ M' ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      ∀ Q : Euc d → Euc d → ℝ, PairCorrector a beta rho M A f Q →
      ∃ G : Euc d → Euc d → Euc d → ℝ,
        Measurable (fun p : Euc d × Euc d × Euc d => G p.1 p.2.1 p.2.2) ∧
        CanonicalTriple (HRS.Whole.withDensityReal rho) G ∧
        (∀ x y z, x ≠ y → x ≠ z → y ≠ z →
          G x y z = tripleG (critCoeff d a beta rho) rho Q x y z ∧
          |G x y z| ≤ C * A * jbracket x ^ M' * jbracket y ^ M' *
            jbracket z ^ M' * triplePole x y z) ∧
        ∀ x y, x ≠ y →
          |repeatedB rho Q x y| ≤ C * A * HRS.MS.Phase2S82.pairWeight M' x y * pole x y ^ 2 := by
  classical
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta ρ0
  swap
  · exact ⟨0, 0, le_rfl, le_rfl, fun rho hrho => absurd ⟨rho, hrho⟩ hex⟩
  obtain ⟨ρ0, h0⟩ := hex
  obtain ⟨hFs, hFb⟩ := r26t8a_thermal_force d hd a beta ha hbeta ρ0 h0
  obtain ⟨BF0, hBF00, hBF0⟩ := hFb 0
  have hBF : ∀ u, ‖forceMean ρ0 u‖ ≤ BF0 := fun u => by
    have := hBF0 u
    rw [norm_iteratedFDeriv_zero] at this
    linarith [norm_nonneg (fderiv ℝ (iteratedFDeriv ℝ 0 (forceMean ρ0)) u u)]
  obtain ⟨K, M', hK0, hMM', hEnv⟩ := r26t8a_a01_env d hd a beta M hM
  have hM'0 : 0 ≤ M' := le_trans hM hMM'
  refine ⟨K * (1 + BF0) + (2 * criticalS d + 4 * BF0), M', by positivity, hM'0, ?_⟩
  intro rho hrho f A hA Q hQ
  have hρeq : rho = ρ0 :=
    (critical_thermal_eq d hd a beta ha hbeta hrho).trans (critical_thermal_eq d hd a beta ha hbeta h0).symm
  subst hρeq
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  set μ : Measure (Euc d) := HRS.Whole.withDensityReal rho with hμ
  have hsymm := hQ.symmetric
  set Gf : Euc d → Euc d → Euc d → ℝ := fun x y z =>
    if (x ≠ y ∧ x ≠ z ∧ y ≠ z) then tripleG (critCoeff d a beta rho) rho Q x y z else 0 with hGf
  have hKC : K * (1 + BF0) ≤ K * (1 + BF0) + (2 * criticalS d + 4 * BF0) := by
    have : 0 ≤ 2 * criticalS d + 4 * BF0 := by positivity
    linarith
  refine ⟨Gf, r26t8a_a02_G_meas d hd a beta M A ha hbeta hM hA hrho hQ, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- symmetries
    intro x y z
    constructor
    · by_cases h : (x ≠ y ∧ x ≠ z ∧ y ≠ z)
      · have h' : (y ≠ x ∧ y ≠ z ∧ x ≠ z) := ⟨h.1.symm, h.2.2, h.2.1⟩
        simp only [hGf, if_pos h, if_pos h']
        exact r26t8a_a02_tripleG_symm_xy hsymm x y z
      · have h' : ¬ (y ≠ x ∧ y ≠ z ∧ x ≠ z) := fun h'' => h ⟨h''.1.symm, h''.2.2, h''.2.1⟩
        simp only [hGf, if_neg h, if_neg h']
    · by_cases h : (x ≠ y ∧ x ≠ z ∧ y ≠ z)
      · have h' : (x ≠ z ∧ x ≠ y ∧ z ≠ y) := ⟨h.2.1, h.1, h.2.2.symm⟩
        simp only [hGf, if_pos h, if_pos h']
        exact r26t8a_a02_tripleG_symm_yz hsymm x y z
      · have h' : ¬ (x ≠ z ∧ x ≠ y ∧ z ≠ y) := fun h'' => h ⟨h''.2.1, h''.1, h''.2.2.symm⟩
        simp only [hGf, if_neg h, if_neg h']
  · -- integrable rows with zero integral
    intro x y hxy
    obtain ⟨hI, hz⟩ := r26t8a_triple_zero_row d hd a beta M ha hbeta hM rho hrho f A hA Q hQ x y hxy
    have hae : ∀ᵐ z : Euc d ∂μ, z ≠ x ∧ z ≠ y := by
      haveI : Nontrivial (Euc d) := ⟨⟨x, y, hxy⟩⟩
      have hx : ∀ᵐ t : Euc d ∂volume, t ≠ x := compl_mem_ae_iff.mpr (measure_singleton x)
      have hy : ∀ᵐ t : Euc d ∂volume, t ≠ y := compl_mem_ae_iff.mpr (measure_singleton y)
      exact (withDensity_absolutelyContinuous volume (fun x => ENNReal.ofReal (rho x))).ae_le
        (by filter_upwards [hx, hy] with t h1 h2 using (⟨h1, h2⟩ : t ≠ x ∧ t ≠ y))
    have hEq : (fun z => Gf x y z) =ᵐ[μ] fun z => tripleG (critCoeff d a beta rho) rho Q x y z := by
      filter_upwards [hae] with z ⟨hzx, hzy⟩
      simp only [hGf]
      rw [if_pos ⟨hxy, hzx.symm, hzy.symm⟩]
    exact ⟨hI.congr hEq.symm, by rw [integral_congr_ae hEq]; exact hz⟩
  · -- pointwise identity and bound
    intro x y z hxy hxz hyz
    have hD : (x ≠ y ∧ x ≠ z ∧ y ≠ z) := ⟨hxy, hxz, hyz⟩
    refine ⟨by simp only [hGf, if_pos hD], ?_⟩
    simp only [hGf, if_pos hD]
    have hb := hEnv rho f A hA Q hQ BF0 hBF00 hBF x y z hxy hxz hyz
    refine hb.trans ?_
    have hz0 : 0 ≤ A * (jbracket x ^ M' * jbracket y ^ M' * jbracket z ^ M') * triplePole x y z := by
      have := Real.rpow_nonneg (s83_jb_pos x).le M'
      have := Real.rpow_nonneg (s83_jb_pos y).le M'
      have := Real.rpow_nonneg (s83_jb_pos z).le M'
      have : 0 ≤ triplePole x y z := by
        unfold triplePole
        have := r26t8a_a01_pole_ge_one x y; have := r26t8a_a01_pole_ge_one x z; have := r26t8a_a01_pole_ge_one y z
        positivity
      positivity
    calc K * (1 + BF0) * A * (jbracket x ^ M' * jbracket y ^ M' * jbracket z ^ M') * triplePole x y z
        = K * (1 + BF0) * (A * (jbracket x ^ M' * jbracket y ^ M' * jbracket z ^ M') * triplePole x y z) := by ring
      _ ≤ (K * (1 + BF0) + (2 * criticalS d + 4 * BF0)) *
            (A * (jbracket x ^ M' * jbracket y ^ M' * jbracket z ^ M') * triplePole x y z) :=
          mul_le_mul_of_nonneg_right hKC hz0
      _ = _ := by ring
  · -- repeatedB
    intro x y hxy
    have hb := r26t8a_a02_repeatedB_bound d hd (M := M) (M' := M') hMM' hA hQ hBF00 hBF hxy
    refine hb.trans ?_
    have hpp : 0 ≤ A * HRS.MS.Phase2S82.pairWeight M' x y * pole x y ^ 2 := by
      have : 0 ≤ HRS.MS.Phase2S82.pairWeight M' x y :=
        mul_nonneg (Real.rpow_nonneg (s83_jb_pos x).le _) (Real.rpow_nonneg (s83_jb_pos y).le _)
      positivity
    have hc : 2 * criticalS d + 4 * BF0 ≤ K * (1 + BF0) + (2 * criticalS d + 4 * BF0) := by
      have : 0 ≤ K * (1 + BF0) := by positivity
      linarith
    calc (2 * criticalS d + 4 * BF0) * A * HRS.MS.Phase2S82.pairWeight M' x y * pole x y ^ 2
        = (2 * criticalS d + 4 * BF0) * (A * HRS.MS.Phase2S82.pairWeight M' x y * pole x y ^ 2) := by ring
      _ ≤ (K * (1 + BF0) + (2 * criticalS d + 4 * BF0)) * (A * HRS.MS.Phase2S82.pairWeight M' x y * pole x y ^ 2) :=
          mul_le_mul_of_nonneg_right hc hpp
      _ = _ := by ring

end HRS.MS.R26T8A
