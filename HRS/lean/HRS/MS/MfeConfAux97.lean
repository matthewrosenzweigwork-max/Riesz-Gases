import HRS.MS.MfeConfAux96

/-!
# S.B.1, packet F8 (part 29): the level-`k` entropy inequality for the trajectory of `WholeMFEHyp` (all one-body hypotheses discharged)

`sb1_lv_ineq`: for the trajectory bundle `Sb1Tr3` (consequence of `WholeMFEHyp`, `sb1_tr3_of_hyp`), a truncated kernel `k`
(`IsP4Kernel`), the integrable Lipschitz bound `Kf` of the exact transport, and the laws `μ` of the regularised solution
(`P4MolData`, from `sb1_flow_hyp` and `sb1_molData_regularised`), the relative entropy with respect to the moving reference
`modulatedGibbs k N θ⁻¹ ρ_t` satisfies `H(μ_t|Q^k_t) ≤ H(μ_0|Q^k_0) + ∫_0^t ∫ S^k_s dμ_s ds`, `S^k` the explicit source
(`sb1_lv_S_eq`: `S^k = Src` with the exact one-body decomposition `Θ = θ div(∇G-F) + ⟨∇G-F, u-∇V⟩ + (⟨∇G,v⟩-Ġ)`).
Only the finiteness of the initial entropy is assumed.
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_lv_affine_integrable {T : ℝ} {Kc : ℝ → ℝ} (hK : IntegrableOn Kc (Set.Icc 0 T)) {g : ℝ → ℝ}
    (hg : ∀ Kv, g Kv = g 0 + (g 1 - g 0) * Kv) : IntegrableOn (fun s => g (Kc s)) (Set.Icc 0 T) := by
  have := (integrableOn_const (C := g 0) (s := Set.Icc (0 : ℝ) T) (by simp)).add (hK.const_mul (g 1 - g 0))
  exact this.congr_fun (fun s _ => (hg (Kc s)).symm) measurableSet_Icc

theorem sb1_lv_rb_mem {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    sb1_lv_rb hT ρ t = ρ t := by
  unfold sb1_lv_rb; rw [Set.projIcc_of_mem hT ht]

theorem sb1_lv_rb_cl {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ) :
    sb1_lv_rb hT ρ (sb1_lv_cl' hT s) = sb1_lv_rb hT ρ s := by
  have h := Set.projIcc_val hT (Set.projIcc (0 : ℝ) T hT s)
  simp only [sb1_lv_rb, sb1_lv_cl']
  rw [h]

theorem sb1_lv_cl'_of_mem {T : ℝ} (hT : 0 ≤ T) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) : sb1_lv_cl' hT s = s := by
  unfold sb1_lv_cl'; rw [Set.projIcc_of_mem hT hs]

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

set_option maxHeartbeats 6400000 in
theorem sb1_lv_ineq (hθ : 0 < D.invβ) (hN : 1 ≤ N) (hk4 : IsP4Kernel d D.s r₀ k)
    (Kf : ℝ → ℝ) (hKi : IntegrableOn Kf (Set.Icc 0 T))
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (Kf t))
    {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B' K' M' CV' : ℝ}
    (hP : P4MolData D.invβ T (fun _ => sb1DriftM D k N) (fun _ => sb1Hs D k N) (fun _ _ => 0) μ Kl B' K' M' CV')
    (hfin0 : relEntropy (μ 0) (Whole.modulatedGibbs k N D.invβ⁻¹ (Whole.withDensityReal (ρ 0))) ≠ ⊤)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    relEntropy (μ t) (Whole.modulatedGibbs k N D.invβ⁻¹ (Whole.withDensityReal (ρ t))) ≠ ⊤ ∧
      (relEntropy (μ t) (Whole.modulatedGibbs k N D.invβ⁻¹ (Whole.withDensityReal (ρ t)))).toReal ≤
        (relEntropy (μ 0) (Whole.modulatedGibbs k N D.invβ⁻¹ (Whole.withDensityReal (ρ 0)))).toReal +
          ∫ s in Set.Icc (0 : ℝ) t, ∫ y, sb1S D.invβ (fun _ => sb1DriftM D k N)
            (fun r => sb1wOne (sb1_lv_U D k hT ρ r))
            (fun s Z => ∑ i, sb1_lv_W D k hT ρ s (Z i) + sb1_lv_kappa' D k N hT ρ s) s y ∂(μ s) := by
  have hd := H.tr.hd
  have hs0 := H.tr.hs0
  have hsd := H.tr.hsd
  have hk := sb1KerU_of_p4 hs0 hk4
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 hs0
  have hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg := hRg.gbd
  have hLg : 0 ≤ Lg := (norm_nonneg _).trans (hL 0)
  obtain ⟨Lf, hLl⟩ := sb1_lv_lip_fderiv hk4
  set L2 : ℝ := (Lf : ℝ) with hL2def
  have hL2 : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2 := fun z => norm_fderiv_le_of_lipschitz ℝ hLl
  have hL20 : 0 ≤ L2 := Lf.2
  have hgk : ∀ z, ‖gradient k z‖ ≤ Lg := fun z => by rw [← sb1_lv_norm_fderiv]; exact hL z
  have hgl : ∀ z z', ‖gradient k z - gradient k z'‖ ≤ L2 * ‖z - z'‖ := by
    intro z z'
    have e : gradient k z - gradient k z' = (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ k z - fderiv ℝ k z') := by
      unfold gradient; simp
    rw [e, LinearIsometryEquiv.norm_map, ← dist_eq_norm, ← dist_eq_norm]
    exact hLl.dist_le_mul z z'
  have hβ : 0 ≤ D.invβ⁻¹ := (inv_pos.2 hθ).le
  set BF := sb1BF d D.s C with hBFdef
  have hBF : 0 ≤ BF := sb1BF_nonneg hs0 H.tr.hC
  have hB : 0 ≤ B := H.tr.V.B_nonneg
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- the Lipschitz bound of the exact transport along the clamped time
  set Kc : ℝ → ℝ := fun s => Kf (sb1_lv_cl' hT s) with hKcdef
  have hKc : ∀ s, 0 ≤ Kc s ∧ ∀ x y, ‖Whole.mfeTransportW D (sb1_lv_rb hT ρ s) x - Whole.mfeTransportW D (sb1_lv_rb hT ρ s) y‖ ≤
      Kc s * ‖x - y‖ := fun s => sb1_lip_of_hasLip (hLip _ (sb1_lv_cl'_mem hT s))
  have hKcI : IntegrableOn Kc (Set.Icc 0 T) :=
    hKi.congr_fun (fun s hs => by simp only [hKcdef]; rw [sb1_lv_cl'_of_mem hT hs]) measurableSet_Icc
  -- uniform bounds
  have hUc : Continuous fun s => ‖sb1_lv_U D k hT ρ s 0‖ :=
    ((sb1_lv_U_cont H hT hk4).comp (Continuous.prodMk_left (0 : Euc d))).norm
  obtain ⟨Umax, hUm0, hUm⟩ := sb1_lv_bdd_of_cont hT hUc (fun s => by
    simp only [sb1_lv_U, sb1_lv_rb_cl])
  have hlc : Continuous fun s => Real.log (sb1_lv_rb hT ρ s 0) :=
    continuous_iff_continuousAt.2 fun s =>
      (((sb1_lv_rb_cont H hT).comp (Continuous.prodMk_left (0 : Euc d))).continuousAt).log
        (sb1_lv_rb_pos H hT s 0).ne'
  obtain ⟨Λ0, hΛ00, hΛ0⟩ := sb1_lv_bdd_of_cont hT hlc (fun s => by simp only [sb1_lv_rb_cl])
  set V0 : ℝ := Umax + d * (Lg + BF) with hV0def
  have hV00 : 0 ≤ V0 := by positivity
  have hV0 : ∀ s, ‖Whole.mfeTransportW D (sb1_lv_rb hT ρ s) 0‖ ≤ V0 := by
    intro s
    have h1 := sb1_lv_e_norm H hT hk4 hRg s 0
    have h2 := norm_sub_le (sb1_lv_U D k hT ρ s 0) (sb1_lv_U D k hT ρ s 0 - Whole.mfeTransportW D (sb1_lv_rb hT ρ s) 0)
    have h3 := hUm s
    rw [sub_sub_cancel] at h2
    rw [abs_of_nonneg (norm_nonneg _)] at h3
    linarith
  obtain ⟨Ck, hCk0, hCk⟩ := sb1_lv_kappa_bound H hT hk4 hθ hN (N := N)
  obtain ⟨Cd, hCd0, hCd⟩ := sb1_lv_kappa'_bound H hT hk4 hθ hN (N := N)
  set G0 := ‖fderiv ℝ D.V 0‖ with hG0
  set G1 := sb1CGd d D.s (sb1CA D B C C3) with hG1def
  have hG1 : 0 ≤ G1 := sb1CGd_nonneg D.s H.CA_nonneg
  set W2 := ∫ z : Euc d, sb1w ((d : ℝ) + 2) z with hW2
  have hW20 : 0 ≤ W2 := integral_nonneg fun z => (sb1w_pos _ _).le
  set LG := Lg * (sb1CA D B C C3 * W2) with hLGdef
  have hLG : 0 ≤ LG := mul_nonneg hLg (mul_nonneg H.CA_nonneg hW20)
  set I1 := C3 * W2 with hI1def
  -- per-time bounds of the one-body source
  have hper : ∀ s, (∀ x, |sb1_lv_Th D k hT ρ s x| ≤
        sb1_lv_cTheta d D C B Lg L2 V0 G0 G1 (Kc s) * (1 + ‖x‖ ^ 2)) ∧
      Sb1WL (sb1_lv_Th D k hT ρ s) (sb1_lv_DTheta d D C B Lg L2 V0 G0 LG I1 (Kc s)) := by
    intro s
    exact sb1_lv_Theta_bounds hθ H.tr.V hk4 hd hs0 hsd hRg hL hL2 (sb1_lv_rb_rho H hT s) (sb1_lv_rb_slice H hT s)
      (sb1_lv_rb_pos H hT s) (hKc s).1 (hKc s).2 (hV0 s) hG1 hLG (sb1_lv_gd_bound H hT hk4 s)
      (fun x y => by have := sb1_lv_gd_lip H hT hk4 hL s x y; rw [hLGdef]; linarith)
      (fun j => (sb1_lv_dh_facts H hT s j).1) (fun j => (sb1_lv_dh_facts H hT s j).2.1)
      (fun j => (sb1_lv_dh_facts H hT s j).2.2)
  have hUb : ∀ s, (∀ x, ‖sb1_lv_U D k hT ρ s x‖ ≤ sb1_lv_B1 d D C Lg V0 + Kc s * ‖x‖) ∧
      (∀ x y, ‖sb1_lv_U D k hT ρ s x - sb1_lv_U D k hT ρ s y‖ ≤ (Kc s + d * (L2 + BF)) * ‖x - y‖) := by
    intro s
    obtain ⟨h1, h2⟩ := sb1_lv_u_bounds hk4 hd hs0 hsd hRg hL hL2 H.tr.V (sb1_lv_rb_rho H hT s)
      (sb1_lv_rb_slice H hT s) (sb1_lv_rb_pos H hT s) (hKc s).2
    refine ⟨fun x => (h1 x).trans ?_, h2⟩
    have := hV0 s
    unfold sb1_lv_B1
    linarith
  -- the explicit time-dependent constants (affine in `Kc s`)
  set B1c := sb1_lv_B1 d D C Lg V0 with hB1cdef
  have hB1c : 0 ≤ B1c := by simp only [hB1cdef, sb1_lv_B1]; positivity
  have hCG := sb1CG_nonneg (d := d) (s := D.s) (sb1_lv_rb_rho H hT 0)
  set gψ : ℝ → ℝ := fun Kv => D.invβ * Λ0 + sb1CG d D.s C3 (C3 * W2) + |D.V 0| +
    (d * (V0 + BF + G0) + 1 + G0 + d * (Kv + B) + B) with hgψ
  set gCS : ℝ → ℝ := fun Kv => (N * (sb1_lv_cTheta d D C B Lg L2 V0 G0 G1 Kv + Lg * (B1c + Kv)) + Cd) / D.invβ with hgCS
  set gDS : ℝ → ℝ := fun Kv => N * (sb1_lv_DTheta d D C B Lg L2 V0 G0 LG I1 Kv + (Kv + d * (L2 + BF)) * Lg +
    2 * L2 * (B1c + Kv)) / D.invβ with hgDS
  have aψ : ∀ Kv, gψ Kv = gψ 0 + (gψ 1 - gψ 0) * Kv := fun Kv => by simp only [hgψ]; ring
  have aCS : ∀ Kv, gCS Kv = gCS 0 + (gCS 1 - gCS 0) * Kv := fun Kv => by
    simp only [hgCS, sb1_lv_cTheta]; ring
  have aDS : ∀ Kv, gDS Kv = gDS 0 + (gDS 1 - gDS 0) * Kv := fun Kv => by
    simp only [hgDS, sb1_lv_DTheta]; ring
  have hcΘ : ∀ s, 0 ≤ sb1_lv_cTheta d D C B Lg L2 V0 G0 G1 (Kc s) := fun s => by
    have := (hKc s).1; simp only [sb1_lv_cTheta, sb1_lv_B1]; positivity
  have hDΘ : ∀ s, 0 ≤ sb1_lv_DTheta d D C B Lg L2 V0 G0 LG I1 (Kc s) := fun s => by
    have := (hKc s).1
    have hI : 0 ≤ I1 := mul_nonneg H.C3nn hW20
    have := sb1_lv_cdF_nonneg (d := d) hs0 H.tr.hC
    simp only [sb1_lv_DTheta, sb1_lv_B1]; positivity
  have hCSn : ∀ s, 0 ≤ gCS (Kc s) := fun s => by
    have := (hKc s).1; have := hcΘ s
    simp only [hgCS]; positivity
  have hDSn : ∀ s, 0 ≤ gDS (Kc s) := fun s => by
    have := (hKc s).1; have := hDΘ s
    simp only [hgDS]; positivity
  have hψn : ∀ s, 0 ≤ gψ (Kc s) := fun s => by
    have := (hKc s).1
    simp only [hgψ]; positivity
  obtain ⟨C0, hC0⟩ := sb1_lv_hC0 H hT hk4 hθ hN (N := N)
  have hρd : ∀ s, Whole.IsProbDensity (sb1_lv_rb hT ρ s) := fun s => (sb1_lv_rb_slice H hT s).dens
  have hKp : ∀ s, 0 < Whole.gibbsNormalizer k N D.invβ⁻¹ (Whole.withDensityReal (sb1_lv_rb hT ρ s)) :=
    fun s => sb1_lv_Kb_pos H hT hk hβ hN s
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have key := sb1_level_ineq_onebody (θ := D.invβ) (T := T) hθ hN D (k := k) (continuous_iff_continuousAt.2 fun x =>
      hk4.smooth.continuous.continuousAt).measurable (ρ := sb1_lv_rb hT ρ) hρd (sb1_lv_rb_pos H hT) hKp hP
    (ψ := sb1_lv_Psi D k hT ρ) (wψ1 := sb1_lv_W D k hT ρ) (u := sb1_lv_U D k hT ρ)
    (κ := sb1_lv_kappa D k N hT ρ) (κ' := sb1_lv_kappa' D k N hT ρ) (fun s x => rfl) (fun s => rfl)
    (sb1_lv_psi_cont H hT hk4) (sb1_lv_kappa_cont H hT hk4 hθ hN) (sb1_lv_Psi_grad H hT hk4)
    (sb1_lv_U_cont H hT hk4) (sb1_lv_U_contDiff H hT hk4) (sb1_lv_divU_cont H hT hk4)
    (sb1_lv_W_cont H hT hk4) (sb1_lv_kappa'_cont H hT hk4 hθ hN) (fun s hs x => sb1_lv_Psi_dt H hT hk4 hs x)
    (fun s hs => sb1_lv_kappa_dt H hT hk4 hθ hN hs)
    (Cψ := fun s => gψ (Kc s)) (Ck := fun _ => Ck) (B1 := fun _ => B1c) (K1 := Kc) (CS := fun s => gCS (Kc s))
    hψn (fun _ => hCk0) (fun _ => hB1c) (fun s => (hKc s).1) hCSn
    (fun s x => by
      have := sb1_lv_psi_growth hθ H.tr.V hk hd hs0 hsd (sb1_lv_rb_rho H hT s) (sb1_lv_rb_slice H hT s)
        (sb1_lv_rb_pos H hT s) (hKc s).1 (hKc s).2 (hV0 s) (hΛ0 s) x
      simpa [sb1_lv_Psi] using this)
    (fun s => hCk s) (fun s x => (hUb s).1 x)
    (fun r Z => by
      rw [sb1_lv_S_eq H hT hk4 hθ r Z]
      have hb := sb1_lv_Src_bound hθ (gk := gradient k) (u := sb1_lv_U D k hT ρ r) (Θ := sb1_lv_Th D k hT ρ r)
        (c := sb1_lv_kappa' D k N hT ρ r / D.invβ) hLg hB1c (hKc r).1 (hcΘ r) hgk (hUb r).1 (hper r).1 Z
      refine hb.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (by have := p4m_q_nonneg Z; linarith)
      simp only [hgCS]
      refine div_le_div_of_nonneg_right ?_ hθ.le
      have hc : |sb1_lv_kappa' D k N hT ρ r / D.invβ| * D.invβ ≤ Cd := by
        rw [abs_div, abs_of_pos hθ, div_mul_cancel₀ _ hθ.ne']; exact hCd r
      linarith)
    (sb1_lv_affine_integrable hKcI aψ) (integrableOn_const (by simp)) (integrableOn_const (by simp)) hKcI
    (sb1_lv_affine_integrable hKcI aCS) (DS := fun s => gDS (Kc s)) hDSn (sb1_lv_affine_integrable hKcI aDS)
    (fun r _ Z Z' => by
      rw [sb1_lv_S_eq H hT hk4 hθ r Z, sb1_lv_S_eq H hT hk4 hθ r Z']
      have hKu : 0 ≤ Kc r + d * (L2 + BF) := by have := (hKc r).1; positivity
      have := sb1_lv_Src_lip hθ (gk := gradient k) (u := sb1_lv_U D k hT ρ r) (Θ := sb1_lv_Th D k hT ρ r)
        (c := sb1_lv_kappa' D k N hT ρ r / D.invβ) hLg hL20 hB1c (hKc r).1 hKu (hDΘ r) hgk hgl (hUb r).1
        (hUb r).2 (fun x y => (hper r).2 x y) Z Z'
      simpa [hgDS] using this)
    (Lw := Real.toNNReal (Kc 0 + d * (L2 + BF))) (sb1_lv_wOne_lip (by have := (hKc 0).1; positivity) (hUb 0).2)
    (C0 := C0) hC0 (by rw [sb1_lv_rb_mem hT ρ h0]; exact hfin0) ht
  rw [sb1_lv_rb_mem hT ρ ht, sb1_lv_rb_mem hT ρ h0] at key
  exact key

end Main

end HRS.MS.MfeConf
