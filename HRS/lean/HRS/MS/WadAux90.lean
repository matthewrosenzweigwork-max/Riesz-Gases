import HRS.MS.WadAux89

/-!
# S8.3, packet S8E-5, part 1: the weighted kernel `Q = ⟨x⟩^{-M}⟨y⟩^{-M} R` of a pair in `C_M^{pair}`

For `R` with `MemCMpair M 0 R`, `Q(x,y) = ⟨x⟩^{-M}⟨y⟩^{-M} R(x,y)` is continuous and tends to `0` at infinity of
`ℝ^d × ℝ^d`; hence it is bounded and uniformly continuous (`s8e_Qa_*`), each section `R(x',·)` is in `C_M`
(`s8e_R_cm`), and `sup_y |Q(x',y)| → 0` as `|x'| → ∞` (`s8e_Q_sup_decay`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- The weighted kernel `⟨x⟩^{-M}⟨y⟩^{-M} R(x,y)`. -/
def s8e_Qa (M : ℝ) (R : Euc d → Euc d → ℝ) (p : Euc d × Euc d) : ℝ :=
  jbracket p.1 ^ (-M) * jbracket p.2 ^ (-M) * R p.1 p.2

theorem s8e_R_eq (M : ℝ) (R : Euc d → Euc d → ℝ) (x y : Euc d) :
    R x y = jbracket x ^ M * jbracket y ^ M * s8e_Qa M R (x, y) := by
  unfold s8e_Qa
  have h1 : jbracket x ^ M * jbracket x ^ (-M) = 1 := by
    rw [← Real.rpow_add (s83_jb_pos x)]; simp
  have h2 : jbracket y ^ M * jbracket y ^ (-M) = 1 := by
    rw [← Real.rpow_add (s83_jb_pos y)]; simp
  calc R x y = (jbracket x ^ M * jbracket x ^ (-M)) * (jbracket y ^ M * jbracket y ^ (-M)) * R x y := by
        rw [h1, h2]; ring
    _ = _ := by ring

theorem s8e_Qa_cont {M : ℝ} {R : Euc d → Euc d → ℝ} (hR : Continuous (Function.uncurry R)) :
    Continuous (s8e_Qa M R) := by
  unfold s8e_Qa
  exact (((s85_jb_rpow_continuous (-M)).comp continuous_fst).mul
    ((s85_jb_rpow_continuous (-M)).comp continuous_snd)).mul hR

theorem s8e_Qa_tendsto {M : ℝ} {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R) :
    Tendsto (s8e_Qa M R) (cocompact (Euc d × Euc d)) (𝓝 0) := by
  have h := hR.2 0 le_rfl
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h.congr fun z => ?_
  rw [norm_iteratedFDeriv_zero]
  unfold s8e_Qa
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _)]
  rfl

theorem s8e_Qa_unif {M : ℝ} {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R) :
    UniformContinuous (s8e_Qa M R) :=
  (s8e_Qa_cont (contDiff_zero.1 hR.1)).uniformContinuous_of_tendsto_cocompact (s8e_Qa_tendsto hR)

theorem s8e_Q_sup_decay {M : ℝ} {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, ∀ x y : Euc d, ρ < ‖x‖ → |s8e_Qa M R (x, y)| ≤ ε := by
  have hev : ∀ᶠ z in cocompact (Euc d × Euc d), |s8e_Qa M R z| < ε := by
    have h := (s8e_Qa_tendsto hR).abs
    rw [abs_zero] at h
    exact h.eventually (gt_mem_nhds hε)
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 hev
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall (0 : Euc d × Euc d)
  refine ⟨ρ, fun x y hx => ?_⟩
  have hnot : (x, y) ∉ K := fun h => by
    have := hρ h
    rw [mem_closedBall_zero_iff, Prod.norm_def] at this
    have h1 : ‖x‖ ≤ max ‖x‖ ‖y‖ := le_max_left _ _
    linarith
  exact (hKs hnot).le

theorem s8e_Qa_bdd {M : ℝ} {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ z, |s8e_Qa M R z| ≤ N := by
  have hev : ∀ᶠ z in cocompact (Euc d × Euc d), |s8e_Qa M R z| < 1 := by
    have h := (s8e_Qa_tendsto hR).abs
    rw [abs_zero] at h
    exact h.eventually (gt_mem_nhds one_pos)
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 hev
  have hcont := s8e_Qa_cont (M := M) (contDiff_zero.1 hR.1)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 1, le_max_of_le_right zero_le_one, fun z => ?_⟩
  by_cases hz : z ∈ K
  · have h1 : |s8e_Qa M R z| ≤ B := by simpa [Real.norm_eq_abs] using hB z hz
    exact h1.trans (le_max_left _ _)
  · exact (hKs hz).le.trans (le_max_right _ _)

/-- Each section `R(x',·)` of a pair in `C_M^{pair}` lies in `C_M`. -/
theorem s8e_R_cm {M : ℝ} {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R) (x' : Euc d) : MemCM M (R x') := by
  have hc : Continuous (Function.uncurry R) := contDiff_zero.1 hR.1
  refine ⟨hc.comp (continuous_const.prodMk continuous_id), ?_⟩
  have hx : Tendsto (fun y : Euc d => (x', y)) (cocompact (Euc d)) (cocompact (Euc d × Euc d)) := by
    rw [← Filter.coprod_cocompact, Filter.coprod]
    exact (tendsto_comap_iff.2 (by simpa using tendsto_id)).mono_right le_sup_right
  have h := ((s8e_Qa_tendsto hR).comp hx).const_mul (jbracket x' ^ M)
  rw [mul_zero] at h
  refine h.congr fun y => ?_
  simp only [Function.comp, s8e_Qa]
  have h1 : jbracket x' ^ M * jbracket x' ^ (-M) = 1 := by
    rw [← Real.rpow_add (s83_jb_pos x')]; simp
  rw [Real.rpow_neg (s83_jb_pos y).le, div_eq_mul_inv]
  calc _ = (jbracket x' ^ M * jbracket x' ^ (-M)) * ((jbracket y ^ M)⁻¹ * R x' y) := by ring
    _ = _ := by rw [h1]; ring

end HRS.MS.Wad
