import HRS.MS.WadAux156

/-!
# S8.3, packet S8G-8: the section of a kernel `R ∈ C_M^{pair}` and the identification of `tensorU`

For `R` with `MemCMpair M 0 R`, `s8g_qsec M R x' = Q(x',·) ∈ C_0` with `Q = ⟨x⟩^{-M}⟨y⟩^{-M}R` is a section in the sense of `S8gSec`
(`s8g_qsec_sec`).  For a doubly centered `R` and `t ≥ 1`, `tensorU U t R x y` equals the pairing `s8g_Phi hT hs m (x,y)`
(`s8g_tensor_eq`) with `m = ∫ ⟨·⟩^M · dμ`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- The section `x' ↦ Q(x',·)`. -/
def s8g_qsec (M : ℝ) {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R) (x' : Euc d) : S8gV d :=
  s8g_mk (fun y => s8e_Qa M R (x', y))
    ((s8e_Qa_cont (contDiff_zero.1 hR.1)).comp (continuous_const.prodMk continuous_id)) (by
      have hx : Tendsto (fun y : Euc d => (x', y)) (cocompact (Euc d)) (cocompact (Euc d × Euc d)) := by
        rw [← Filter.coprod_cocompact, Filter.coprod]
        exact (tendsto_comap_iff.2 (by simpa using tendsto_id)).mono_right le_sup_right
      exact (s8e_Qa_tendsto hR).comp hx)

theorem s8g_qsec_apply (M : ℝ) {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R) (x' y : Euc d) :
    s8g_qsec M hR x' y = s8e_Qa M R (x', y) := rfl

theorem s8g_qsec_sec (M : ℝ) {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R) {N0 : ℝ}
    (hN0 : ∀ z, |s8e_Qa M R z| ≤ N0) : S8gSec (s8g_qsec M hR) N0 := by
  have hnn : 0 ≤ N0 := (abs_nonneg _).trans (hN0 (0, 0))
  refine ⟨?_, fun x' => s8g_norm_le hnn fun y => hN0 (x', y), ?_⟩
  · rw [Metric.continuous_iff]
    intro b ε hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.1 (s8e_Qa_unif hR) (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun a ha => ?_⟩
    rw [dist_eq_norm]
    have : ‖s8g_qsec M hR a - s8g_qsec M hR b‖ ≤ ε / 2 := by
      refine s8g_norm_le (by positivity) fun y => ?_
      have h1 : dist ((a, y) : Euc d × Euc d) (b, y) < δ := by
        rw [Prod.dist_eq]; simpa using ha
      have := hδ' h1
      rw [Real.dist_eq] at this
      exact this.le
    linarith
  · rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨ρ, hρ⟩ := s8e_Q_sup_decay hR (show 0 < ε / 2 by positivity)
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop ρ] with x' hx'
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    have : ‖s8g_qsec M hR x'‖ ≤ ε / 2 := s8g_norm_le (by positivity) fun y => hρ x' y hx'
    linarith

theorem s8g_tensor_eq (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R) (hdc : IsDoublyCentered (HRS.Whole.withDensityReal ρβ) R)
    {t : ℝ} (ht : 1 ≤ t) {J : ℕ} {A : ℝ}
    (hT : S8gOp M (fun f => U t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) J A) {N0 : ℝ}
    (hN0 : ∀ z, |s8e_Qa M R z| ≤ N0)
    (hint : Integrable (fun y : Euc d => jbracket y ^ M) (HRS.Whole.withDensityReal ρβ)) (x y : Euc d) :
    tensorU U t R x y = s8g_Phi hT (s8g_qsec_sec M hR hN0) (s8g_meanF hint) (x, y) := by
  have ht0 : 0 ≤ t := by linarith
  set μ := HRS.Whole.withDensityReal ρβ with hμ
  set hs := s8g_qsec_sec M hR hN0 with hshs
  set qy : S8gV d := s8g_psi hs (s8g_ell hT y) with hqy
  set G : Euc d → ℝ := fun x' => U t (R x') y with hG
  have hGeq : G = fun x' => s85_Ulim a β ρβ M t (R x') y := funext fun x' => by
    simp only [hG]
    rw [s85_semigroup_unique hd ha hβ hρ hMpos hU ht0 (s8e_R_cm hR x')]
  have hGM : MemCM M G := by
    obtain ⟨Cd, c, hCd, hc, h2a⟩ := s8e_2a_pt hd ha hβ hρ hMpos
    rw [hGeq]
    exact s8e_G_cm hd ha hβ hρ hMpos hCd h2a hR hdc ht y
  have claim1 : ∀ x', qy x' = jbracket x' ^ (-M) * G x' := by
    intro x'
    have hι : s8g_ι M (s8g_qsec M hR x') = (jbracket x' ^ (-M)) • R x' := by
      funext y'
      simp only [s8g_ι, s8g_qsec_apply, s8e_Qa, Pi.smul_apply, smul_eq_mul]
      have h1 : jbracket y' ^ M * jbracket y' ^ (-M) = 1 := by
        rw [← Real.rpow_add (s83_jb_pos y')]; simp
      calc jbracket y' ^ M * (jbracket x' ^ (-M) * jbracket y' ^ (-M) * R x' y')
          = jbracket x' ^ (-M) * ((jbracket y' ^ M * jbracket y' ^ (-M)) * R x' y') := by ring
        _ = _ := by rw [h1]; ring
    have e1 : qy x' = U t (HRS.Whole.projMean μ (s8g_ι M (s8g_qsec M hR x'))) y := rfl
    rw [e1, hι, s8g_projMean_smul, s8e_projMean_centered (hdc.2 x'),
      hU.smul t ht0 _ _ (s8e_R_cm hR x')]
    rfl
  have claim2 : s8g_ι M qy = G := by
    funext x'
    simp only [s8g_ι, claim1]
    have h1 : jbracket x' ^ M * jbracket x' ^ (-M) = 1 := by
      rw [← Real.rpow_add (s83_jb_pos x')]; simp
    calc jbracket x' ^ M * (jbracket x' ^ (-M) * G x') = (jbracket x' ^ M * jbracket x' ^ (-M)) * G x' := by ring
      _ = _ := by rw [h1]; ring
  have hdecomp : U t G x = U t (HRS.Whole.projMean μ G) x + HRS.Whole.pair μ G := by
    rw [s85_semigroup_unique hd ha hβ hρ hMpos hU ht0 hGM,
      s85_semigroup_unique hd ha hβ hρ hMpos hU ht0 (s8d_memCM_projMean hMpos hGM)]
    exact s8e_Ulim_projMean hd ha hβ hρ hMpos ht hGM x
  have lhs : tensorU U t R x y = U t G x := rfl
  rw [lhs, hdecomp]
  unfold s8g_Phi
  simp only
  rw [ContinuousLinearMap.add_apply, s8g_ell_apply, s8g_meanF_apply, claim2]
  rfl

end HRS.MS.Wad
