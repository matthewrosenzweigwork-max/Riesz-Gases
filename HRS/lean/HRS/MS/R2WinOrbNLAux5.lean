import HRS.MS.R2WinOrbNLAux4
import HRS.MS.S67NlBD25
import HRS.MS.S67NlBD47
import HRS.MS.S67NlBD66A
import HRS.MS.TransOpAux26

/-!
# S10.3 (nonlinear branch), part 5: bounds for the generator perturbation `P_t u = L_t u - L_β u`

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.  `s103n_const_class`: the constant trajectory `ρ ≡ ρ_β` is in the small class (radius `1`).
`s103n_cb_of_jets`: jets up to order `n+1` bounded by `E` give `‖∇w‖_{C_b^n} ≤ (n+1)E`.  `s103n_P_data`: for `u` with jets up to order
`4d+46` bounded by `B` and `√ρ_β Πu ∈ Σ^{M_o+2}` of norm `≤ B`, the perturbation `P_t u` is `C^{4d+45}` with jets `≤ C_P B` and
`‖√ρ_β ΠP_tu‖_{Σ^{M_o}} ≤ C_P B`, with `C_P` independent of the trajectory (radius `r ≤ 1`), `t`, `u`.  Proof: `L_t u - L_β u = (J(ρ_t) - J(ρ_β))u
- F[v]·∇u` (S6.7nl.47, 66A for the jets) and `√ρ_β P_t u = K(v,ψ_u)` with the projected source bound of S6.7nl.25 for the `Σ`-norm.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.BreakdownS67 HRS.MS.Mov63 HRS.MS.MovLin HRS.MS.MovAdj HRS.MS.MovOsc
open HRS.MS.MovForce HRS.MS.MovC2

variable {d : ℕ}

/-- The perturbation `P_t u = L_t u - L_β u` of the generator at time `t`. -/
def s103nP (d : ℕ) (s a β : ℝ) (ρβ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ) (t : ℝ) (u : Euc d → ℝ) :
    Euc d → ℝ := fun x => generatorW ((quadraticGradientDyn d s a β).coeff ρ) t u x -
  generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) t u x

theorem s103n_const_class {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) :
    ∃ f0 : Euc d → ℝ, MovInSmallClass d s a β ρβ (102 * d + 1020) 1 1 f0 (fun _ => ρβ) := by
  have h := HRS.MS.TransOp.s611_resulting_const H.hd H.hs0 H.hsd H.hq H.hβ H.hρ (εstar := 1) one_pos
    (fun _ => 0)
  exact ⟨_, s103n_small_class h (by norm_num)⟩

theorem s103n_cb_of_jets {w : Euc d → ℝ} {n : ℕ} {E : ℝ}
    (hw : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) w)
    (h : ∀ l ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ l w x‖ ≤ E) :
    cbNormVecE n (fun x => gradient w x) ≤ ENNReal.ofReal ((n + 1) * E) := by
  unfold cbNormVecE
  calc ∑ j ∈ Finset.range (n + 1), ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun y => gradient w y) x‖
      ≤ ∑ j ∈ Finset.range (n + 1), ENNReal.ofReal E := by
        refine Finset.sum_le_sum fun j hj => iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
        have hj' : j + 1 ≤ n + 1 := by have := Finset.mem_range.1 hj; omega
        rw [s67_norm_iter_grad (hw.of_le (by exact_mod_cast hj') : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) w) x]
        exact h (j + 1) hj' x
    _ = ENNReal.ofReal ((n + 1) * E) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1; push_cast; ring

theorem s103n_jets_sub {f g : Euc d → ℝ} {n : ℕ} (hf : ContDiff ℝ (n : WithTop ℕ∞) f)
    (hg : ContDiff ℝ (n : WithTop ℕ∞) g) {E1 E2 : ℝ}
    (h1 : ∀ l ≤ n, ∀ x, ‖iteratedFDeriv ℝ l f x‖ ≤ E1) (h2 : ∀ l ≤ n, ∀ x, ‖iteratedFDeriv ℝ l g x‖ ≤ E2) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun x => f x - g x) ∧
    ∀ l ≤ n, ∀ x, ‖iteratedFDeriv ℝ l (fun x => f x - g x) x‖ ≤ E1 + E2 := by
  refine ⟨hf.sub hg, fun l hl x => ?_⟩
  have e : (fun x => f x - g x) = f - g := rfl
  rw [e, iteratedFDeriv_sub_apply (hf.of_le (by exact_mod_cast hl)).contDiffAt
    (hg.of_le (by exact_mod_cast hl)).contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add (h1 l hl x) (h2 l hl x))

theorem s103n_psi_dL2 {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) {u : Euc d → ℝ}
    (hu : MemCb 2 u) (i : Fin d) :
    ContDiff ℝ 2 (s67psi ρβ u) ∧ MemLp (s67bd_D i (s67psi ρβ u)) 2 (volume : Measure (Euc d)) := by
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  have hu2 : ContDiff ℝ 2 u := hu.1
  obtain ⟨B0, hB0⟩ := hu.2 0 (by norm_num)
  obtain ⟨B1, hB1⟩ := hu.2 1 (by norm_num)
  set c : ℝ := ∫ y, u y * ρβ y with hc
  have hψfun : s67psi ρβ u = fun y => Real.sqrt (ρβ y) * (u y - c) := rfl
  have hsq2 : ContDiff ℝ 2 (fun y => Real.sqrt (ρβ y)) := by
    rw [← hψs]; exact (ψs.smooth 2)
  refine ⟨by rw [hψfun]; exact hsq2.mul (hu2.sub contDiff_const), ?_⟩
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  have hder : ∀ x, s67bd_D i (s67psi ρβ u) x =
      fderiv ℝ ψs x e * (u x - c) + Real.sqrt (ρβ x) * fderiv ℝ u x e := by
    intro x
    have h1 : HasFDerivAt (fun y => Real.sqrt (ρβ y)) (fderiv ℝ ψs x) x := by
      have : (fun y => Real.sqrt (ρβ y)) = ⇑ψs := hψs.symm
      rw [this]
      exact (ψs.differentiableAt).hasFDerivAt
    have h2 : HasFDerivAt (fun y => u y - c) (fderiv ℝ u x) x :=
      ((hu2.differentiable (by norm_num)) x).hasFDerivAt.sub_const c
    have h3 : HasFDerivAt (fun y => Real.sqrt (ρβ y) * (u y - c))
        (Real.sqrt (ρβ x) • fderiv ℝ u x + (u x - c) • fderiv ℝ ψs x) x := h1.mul h2
    unfold s67bd_D
    rw [hψfun, h3.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hsx : Real.sqrt (ρβ x) = ψs x := (congrFun hψs x).symm
    rw [hsx]; ring
  have hfun : s67bd_D i (s67psi ρβ u) = fun x => fderiv ℝ ψs x e * (u x - c) + Real.sqrt (ρβ x) * fderiv ℝ u x e :=
    funext hder
  rw [hfun]
  have hL : MemLp (fun x => fderiv ℝ ψs x e) 2 (volume : Measure (Euc d)) := by
    have := (memOsc_schwartz 0 (LineDeriv.lineDerivOp e ψs)).1
    have hf : (fun x => fderiv ℝ ψs x e) = ⇑(LineDeriv.lineDerivOp e ψs) := by
      funext x; exact (SchwartzMap.lineDerivOp_apply_eq_fderiv e ψs x).symm
    rwa [← hf] at this
  have hS : MemLp (fun x => Real.sqrt (ρβ x)) 2 (volume : Measure (Euc d)) := by
    have := (memOsc_schwartz 0 ψs).1
    rwa [hψs] at this
  have hcu : Continuous (fun x => u x - c) := hu2.continuous.sub continuous_const
  have hcD : Continuous (fun x => fderiv ℝ u x e) :=
    (hu2.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hu0 : ∀ x, |u x| ≤ B0 := fun x => by
    have h : ‖iteratedFDeriv ℝ 0 u x‖ ≤ B0 := hB0 ⟨x, rfl⟩
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  have hu1 : ∀ x, |fderiv ℝ u x e| ≤ B1 := fun x => by
    have h1 := (fderiv ℝ u x).le_opNorm e
    have h2 : ‖e‖ = 1 := by simp [he]
    rw [h2, mul_one, ← norm_iteratedFDeriv_one] at h1
    rw [← Real.norm_eq_abs]
    exact h1.trans (hB1 ⟨x, rfl⟩)
  refine MemLp.add ?_ ?_
  · refine hL.of_le_mul (c := |B0| + |c|) (hL.aestronglyMeasurable.mul hcu.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add ((hu0 x).trans (le_abs_self _)) le_rfl)
  · refine hS.of_le_mul (c := |B1|) (hS.aestronglyMeasurable.mul hcD.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [Real.norm_eq_abs]
    exact (hu1 x).trans (le_abs_self _)

set_option maxHeartbeats 3200000 in
theorem s103n_P_data {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (Mo : ℕ)
    (hMo : (d : ℝ) / 2 + ((4 * d + 45 : ℕ) : ℝ) + 5 < Mo)
    (hMom : (Mo : ℝ) + 2 + 4 < ((102 * d + 1020 : ℕ) : ℝ)) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ (r c₁ : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ c₁ →
      ∀ (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      MovInSmallClass d s a β ρβ (102 * d + 1020) r c₁ f0 ρ →
      ∀ (t : ℝ), 0 ≤ t → ∀ (u : Euc d → ℝ) (B : ℝ), 0 ≤ B →
        ContDiff ℝ ((4 * d + 46 : ℕ) : WithTop ℕ∞) u →
        (∀ l ≤ 4 * d + 46, ∀ x, ‖iteratedFDeriv ℝ l u x‖ ≤ B) →
        MemOsc ((Mo + 2 : ℕ) : ℝ) (s67psi ρβ u) → oscNorm ((Mo + 2 : ℕ) : ℝ) (s67psi ρβ u) ≤ B →
        ContDiff ℝ ((4 * d + 45 : ℕ) : WithTop ℕ∞) (s103nP d s a β ρβ ρ t u) ∧
        (∀ l ≤ 4 * d + 45, ∀ x, ‖iteratedFDeriv ℝ l (s103nP d s a β ρβ ρ t u) x‖ ≤ CP * B) ∧
        MemOsc (Mo : ℝ) (s67psi ρβ (s103nP d s a β ρβ ρ t u)) ∧
        oscNorm (Mo : ℝ) (s67psi ρβ (s103nP d s a β ρβ ρ t u)) ≤ CP * B := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm7 : (d : ℝ) / 2 + 7 < ((102 * d + 1020 : ℕ) : ℝ) := by push_cast at hMom ⊢; linarith
  have hMoJ : (d : ℝ) / 2 + ((4 * d + 43 : ℕ) : ℝ) + 5 < Mo := by
    push_cast at hMo ⊢; linarith
  have hMo4 : (Mo : ℝ) + 4 < ((102 * d + 1020 : ℕ) : ℝ) := by linarith
  have hMo2 : (2 : ℝ) ≤ Mo := by push_cast at hMo; linarith
  obtain ⟨CJ, hCJ0, hJ⟩ := s67bd_J_bound H (4 * d + 43) Mo (102 * d + 1020) hMoJ hm7 hMo4
  obtain ⟨CF, hCF0, hF⟩ := s67bd_transport_source_jets H (4 * d + 45) Mo (102 * d + 1020) hMo hm7 hMo4
  have ha1 : 1 ≤ movA d s := le_max_left _ _
  have ha2 : movA d s < 2 := by
    unfold movA; exact max_lt (by norm_num) (by linarith [H.hsd])
  obtain ⟨C25, hC250, h25⟩ := s67bd_projected_source_bound H (102 * d + 1020) ((Mo : ℝ) + movA d s)
    hm7 (by linarith) (by linarith)
  obtain ⟨f1, hconst⟩ := s103n_const_class H
  refine ⟨2 * CJ + CF * (((4 * d + 45 : ℕ) : ℝ) + 1) + C25, by positivity, ?_⟩
  intro r c₁ hr0 hr1 hc₁ f0 ρ hρ t ht u B hB hu hjet hψ hψB
  have hu1 : ContDiff ℝ ((4 * d + 45 + 1 : ℕ) : WithTop ℕ∞) u := hu
  have hcb : MemCb 2 u :=
    ⟨hu.of_le (by exact_mod_cast (by omega : 2 ≤ 4 * d + 46)), fun j hj => ⟨B, by
      rintro _ ⟨x, rfl⟩; exact hjet j (by omega) x⟩⟩
  have hψMo : MemOsc (Mo : ℝ) (s67psi ρβ u) ∧ oscNorm (Mo : ℝ) (s67psi ρβ u) ≤ B := by
    have := mo_mono (r := (Mo : ℝ)) (r' := ((Mo + 2 : ℕ) : ℝ)) (by push_cast; linarith) hψ
    exact ⟨this.1, this.2.trans hψB⟩
  -- the classical bounds
  have hP : s103nP d s a β ρβ ρ t u = fun x =>
      ((s67J d s (ρ t) u x - s67J d s ρβ u x) -
        inner ℝ (s67bd_F d s ρβ (movV ρβ ρ t) x) (gradient u x)) := by
    funext x
    exact s103n_gen_diff H hm7 hρ ht u x
  obtain ⟨hJt1, hJt2⟩ := hJ r c₁ hr0 hr1 hc₁ f0 ρ hρ t ht u hcb hψMo.1
  obtain ⟨hJb1, hJb2⟩ := hJ 1 1 zero_le_one le_rfl zero_le_one f1 (fun _ => ρβ) hconst t ht u hcb hψMo.1
  have hcbfin : cbNormVecE (4 * d + 45) (fun x => gradient u x) ≤
      ENNReal.ofReal (((4 * d + 45 : ℕ) + 1 : ℝ) * B) :=
    s103n_cb_of_jets hu1 (fun l hl x => hjet l (by omega) x)
  have hcbtop : cbNormVecE (4 * d + 45) (fun x => gradient u x) < ⊤ :=
    lt_of_le_of_lt hcbfin ENNReal.ofReal_lt_top
  have hcbr : (cbNormVecE (4 * d + 45) (fun x => gradient u x)).toReal ≤ ((4 * d + 45 : ℕ) + 1 : ℝ) * B := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcbfin
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  obtain ⟨hFt1, hFt2⟩ := hF r c₁ hr0 hr1 hc₁ f0 ρ hρ t ht u hu1 hcbtop
  have hN0 : 0 ≤ oscNorm (Mo : ℝ) (s67psi ρβ u) := Real.sqrt_nonneg _
  have hJ1 : ∀ l ≤ 4 * d + 45, ∀ x, ‖iteratedFDeriv ℝ l (s67J d s (ρ t) u) x‖ ≤ CJ * B := fun l hl x =>
    (hJt2 l hl x).trans (mul_le_mul_of_nonneg_left hψMo.2 hCJ0)
  have hJ2 : ∀ l ≤ 4 * d + 45, ∀ x, ‖iteratedFDeriv ℝ l (s67J d s ρβ u) x‖ ≤ CJ * B := fun l hl x =>
    (hJb2 l hl x).trans (mul_le_mul_of_nonneg_left hψMo.2 hCJ0)
  obtain ⟨hS1, hS2⟩ := s103n_jets_sub (n := 4 * d + 45) hJt1 hJb1 hJ1 hJ2
  have hF1 : ∀ l ≤ 4 * d + 45, ∀ x, ‖iteratedFDeriv ℝ l
      (fun y => inner ℝ (s67bd_F d s ρβ (movV ρβ ρ t) y) (gradient u y)) x‖ ≤
        CF * (((4 * d + 45 : ℕ) + 1 : ℝ) * B) := fun l hl x =>
    (hFt2 l hl x).trans (by
      calc CF * r * (cbNormVecE (4 * d + 45) (fun x => gradient u x)).toReal ≤ CF * 1 * (((4 * d + 45 : ℕ) + 1 : ℝ) * B) := by
            gcongr
        _ = _ := by ring)
  obtain ⟨hT1, hT2⟩ := s103n_jets_sub (n := 4 * d + 45) hS1 hFt1 hS2 hF1
  -- the weighted part
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  have hsqsm : ContDiff ℝ ∞ (fun x => Real.sqrt (ρβ x)) := by
    rw [← hψs]; exact ψs.smooth _
  set v : Euc d → ℝ := movV ρβ ρ t with hvdef
  have hvcont : Continuous v := by
    show Continuous (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x))
    refine ((hρ.regular t ht).sub hρsm.continuous).div hsqsm.continuous
      (fun x => (Real.sqrt_pos.2 (hρpos x)).ne')
  obtain ⟨hvm, hvn⟩ := hρ.weighted t ht
  have hvn1 : oscNorm ((102 * d + 1020 : ℕ) : ℝ) v ≤ 1 := by
    refine hvn.trans ?_
    have : Real.exp (-c₁ * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith
  have hKid : ∀ x, Real.sqrt (ρβ x) * s103nP d s a β ρβ ρ t u x =
      s67bd_K d s ρβ v (s67psi ρβ u) x := fun x => s103n_gen_diff_K H hm7 hρ ht u hcb x
  have hR : s67psi ρβ (s103nP d s a β ρβ ρ t u) = s67bd_R d s ρβ v (s67psi ρβ u) := by
    funext x
    have e1 : s67psi ρβ (s103nP d s a β ρβ ρ t u) x = Real.sqrt (ρβ x) *
        (s103nP d s a β ρβ ρ t u x - ∫ y, s103nP d s a β ρβ ρ t u y * ρβ y) := rfl
    have e2 : s67bd_R d s ρβ v (s67psi ρβ u) x = s67bd_K d s ρβ v (s67psi ρβ u) x -
        Real.sqrt (ρβ x) * ∫ y, Real.sqrt (ρβ y) * s67bd_K d s ρβ v (s67psi ρβ u) y := rfl
    have hint : ∫ y, Real.sqrt (ρβ y) * s67bd_K d s ρβ v (s67psi ρβ u) y =
        ∫ y, s103nP d s a β ρβ ρ t u y * ρβ y := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show Real.sqrt (ρβ y) * s67bd_K d s ρβ v (s67psi ρβ u) y = _
      rw [← hKid y]
      have := Real.mul_self_sqrt (hρpos y).le
      calc Real.sqrt (ρβ y) * (Real.sqrt (ρβ y) * s103nP d s a β ρβ ρ t u y) =
          (Real.sqrt (ρβ y) * Real.sqrt (ρβ y)) * s103nP d s a β ρβ ρ t u y := by ring
        _ = _ := by rw [this]; ring
    rw [e1, e2, hint, ← hKid x]
    ring
  obtain ⟨hψC2, hψL2⟩ : ContDiff ℝ 2 (s67psi ρβ u) ∧
      ∀ i : Fin d, MemLp (s67bd_D i (s67psi ρβ u)) 2 (volume : Measure (Euc d)) :=
    ⟨(s103n_psi_dL2 H hcb ⟨0, by have := H.hd; omega⟩).1,
      fun i => (s103n_psi_dL2 H hcb i).2⟩
  have hσ := mo_mono (r := (Mo : ℝ) + movA d s) (r' := ((Mo + 2 : ℕ) : ℝ))
    (by push_cast; linarith) hψ
  obtain ⟨h1, -, -, h4⟩ := h25 v (s67psi ρβ u) hvcont hvm hψC2 hσ.1 hψL2
  have e : (Mo : ℝ) + movA d s - movA d s = Mo := by ring
  rw [e] at h1 h4
  have hSig : MemOsc (Mo : ℝ) (s67psi ρβ (s103nP d s a β ρβ ρ t u)) ∧
      oscNorm (Mo : ℝ) (s67psi ρβ (s103nP d s a β ρβ ρ t u)) ≤ C25 * B := by
    rw [hR]
    refine ⟨h1, h4.trans ?_⟩
    have hn2 : 0 ≤ oscNorm ((Mo : ℝ) + movA d s) (s67psi ρβ u) := Real.sqrt_nonneg _
    have hn3 : 0 ≤ oscNorm ((102 * d + 1020 : ℕ) : ℝ) v := Real.sqrt_nonneg _
    calc C25 * oscNorm ((102 * d + 1020 : ℕ) : ℝ) v * oscNorm ((Mo : ℝ) + movA d s) (s67psi ρβ u)
        ≤ C25 * 1 * B := by
          gcongr
          exact hσ.2.trans hψB
      _ = C25 * B := by ring
  have hnum : CJ * B + CJ * B + CF * (((4 * d + 45 : ℕ) + 1 : ℝ) * B) ≤
      (2 * CJ + CF * (((4 * d + 45 : ℕ) : ℝ) + 1) + C25) * B := by
    nlinarith [mul_nonneg hC250 hB]
  have hnum2 : C25 * B ≤ (2 * CJ + CF * (((4 * d + 45 : ℕ) : ℝ) + 1) + C25) * B := by
    nlinarith [mul_nonneg hCJ0 hB, mul_nonneg hCF0 hB,
      mul_nonneg (mul_nonneg hCF0 hB) (Nat.cast_nonneg (4 * d + 45) : (0:ℝ) ≤ ((4 * d + 45 : ℕ) : ℝ))]
  refine ⟨by rw [hP]; exact hT1, fun l hl x => ?_, hSig.1, hSig.2.trans hnum2⟩
  rw [hP]
  exact (hT2 l hl x).trans hnum

end HRS.MS.R2WinOrbNL

end
