import HRS.MS.FixEqP2Aux6

/-!
# S5.7 `fixed_equation` (worker S57P), part 10: the difference of two generators

For two coefficient families `fixedEqCoeff s M Q ν c ρ` and `fixedEqCoeff s M Q νN cN ρN` (same `s, M, Q`), and `φ ∈ C^{N+2}`
bounded in `C^{N+2}` by `B_φ`, the difference of the generators is a bounded `C^N` function with
`‖D^i (𝓛_τ - 𝓛^N_τ) φ‖ ≤ C_g (D_ν + D_c + D_ρ) B_φ`, `i ≤ N`
(`s57p_gen_diff`): `D_ν ≥ |ν - νN|`, `D_c ≥ sup ‖c - cN‖_{C_b^K}`, `D_ρ ≥ sup max_{|α|≤K} ⟨x⟩^{L'}|D^α(ρN-ρ)|`, `K ≥ N+2`,
`L' ≥ d+3`.  Pieces: `rg_laplacian`, `RgW.mul`, `rg_T3` (`HRS/MP/RdGenerator.lean`).
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

theorem s57p_wsup_mono_L {r : ℕ} {L L' : ℝ} (hL : L ≤ L') (f : Euc d → ℝ) :
    weightedSupE r L f ≤ weightedSupE r L' f := by
  unfold weightedSupE derivSupE
  refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ?_
  refine le_iSup_of_le j (le_iSup_of_le i (le_iSup_of_le x ?_))
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (HRS.MS.Adj.ad1_one_le_jb x) hL)
    (abs_nonneg _)

theorem s57p_wsup_mono_r {r r' : ℕ} (hr : r ≤ r') (L : ℝ) (f : Euc d → ℝ) :
    weightedSupE r L f ≤ weightedSupE r' L f :=
  fcau_weightedSupE_mono hr L f

/-- decay class from a weighted sup bound -/
theorem s57p_rgdecay_of_wsup (hd : 1 ≤ d) {r : ℕ} {L Λ : ℝ} (hL : (d : ℝ) + 3 ≤ L) {ρ : Euc d → ℝ}
    (hρ : ContDiff ℝ r ρ) (hw : weightedSupE r L ρ ≤ ENNReal.ofReal Λ) :
    RgDecay r (fun _ => (d : ℝ) ^ r * max Λ 0 * 2 ^ ((d : ℝ) + 3)) ρ := by
  have hΛ0 : 0 ≤ max Λ 0 := le_max_right _ _
  have hw' : weightedSupE r L ρ ≤ ENNReal.ofReal (max Λ 0) :=
    hw.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hw3 : weightedSupE r ((d : ℝ) + 3) ρ ≤ ENNReal.ofReal (max Λ 0) := (s57p_wsup_mono_L hL ρ).trans hw'
  have hfin : weightedSupE r ((d : ℝ) + 3) ρ < ⊤ := lt_of_le_of_lt hw3 ENNReal.ofReal_lt_top
  have hΛ : (weightedSupE r ((d : ℝ) + 3) ρ).toReal ≤ max Λ 0 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hw3
    rwa [ENNReal.toReal_ofReal hΛ0] at this
  have hcb : MemCb r ρ := by
    refine ⟨hρ, fun j hj => ⟨(d : ℝ) ^ j * max Λ 0, ?_⟩⟩
    rintro _ ⟨x, rfl⟩
    have hp : ∀ i : Fin j → Fin d, |iteratedFDeriv ℝ j ρ x (fun p => EuclideanSpace.single (i p) 1)| ≤ max Λ 0 := by
      intro i
      have h1 := rg_partial_weight_bound hfin hj i x
      have h2 : 1 ≤ jbracket x ^ ((d : ℝ) + 3) :=
        Real.one_le_rpow (HRS.MS.Adj.ad1_one_le_jb x) (by positivity)
      have e : |iteratedFDeriv ℝ j ρ x (fun p => EuclideanSpace.single (i p) 1)| = |partialDeriv i ρ x| := rfl
      rw [e]
      nlinarith [abs_nonneg (partialDeriv i ρ x)]
    exact rg_norm_le_of_partial hd _ hp
  exact rg_rho_decay hd hcb hfin hΛ

theorem s57p_rgdecay_mono_const {n : ℕ} {c c' : ℝ} (h : c ≤ c') {f : Euc d → ℝ} (hf : RgDecay n (fun _ => c) f) :
    RgDecay n (fun _ => c') f := by
  refine ⟨hf.1, fun l hl y => (hf.2 l hl y).trans ?_⟩
  exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (by positivity) _)

theorem s57p_comp_RgW1 {N : ℕ} {Λ : ℝ} {g : Euc d → Euc d} (hg : ContDiff ℝ N g)
    (hb : ∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ Λ) (j : Fin d) :
    RgW (fun _ : Euc d => (1 : ℝ)) N Λ (fun x => g x j) := by
  let P : Euc d →L[ℝ] ℝ := EuclideanSpace.proj j
  have hP : ‖P‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    simpa [P] using PiLp.norm_apply_le y j
  have e : (fun x => g x j) = fun x => P (g x) := rfl
  rw [e]
  refine ⟨P.contDiff.comp hg, fun n hn x => ?_⟩
  have := P.norm_iteratedFDeriv_comp_left (f := g) (x := x) (n := n) (N := (N : ℕ∞ω)) hg.contDiffAt
    (by exact_mod_cast hn)
  calc ‖iteratedFDeriv ℝ n (fun x => P (g x)) x‖ ≤ ‖P‖ * ‖iteratedFDeriv ℝ n g x‖ := this
    _ ≤ 1 * Λ := mul_le_mul hP (hb n hn x) (norm_nonneg _) zero_le_one
    _ = Λ * 1 := by ring

/-! ### Optimal order for the cancellation-convention convolution (`C^m` output from `C^{m+1}` input) -/

theorem s57p_rgT_continuous (hd : 1 ≤ d) {s σ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ}
    (hκ : RgKer d s σ κ) {Fb : Type*} [NormedAddCommGroup Fb] [NormedSpace ℝ Fb] [CompleteSpace Fb]
    {g : Euc d → Fb} (hg : Differentiable ℝ g) {a0 a1 : ℝ} (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1)
    (b0 : ∀ y, ‖g y‖ ≤ a0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) (b1 : ∀ y, ‖fderiv ℝ g y‖ ≤ a1) :
    Continuous (rgT κ g) := by
  refine continuous_iff_seqContinuous.2 fun xs x₀ hx => ?_
  unfold rgT
  refine tendsto_integral_filter_of_dominated_convergence (rgMaj d s σ (a0 * 2 ^ ((d : ℝ) + 1)) a1 x₀)
    (Eventually.of_forall fun i => rg_aesm hκ.meas hg.continuous (xs i)) ?_
    (rg_maj_integrable hd hsd σ _ a1 x₀) ?_
  · have hxn : ∀ᶠ i in atTop, ‖xs i - x₀‖ < 1 :=
      (tendsto_iff_norm_sub_tendsto_zero.1 hx).eventually (gt_mem_nhds (zero_lt_one))
    filter_upwards [hxn] with i hi
    filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
    have := rg_norm_le hs0 hκ hg ha0 ha1 b0 b1 (xs i) z hz
    refine this.trans ?_
    unfold rgMaj
    apply mul_le_mul_of_nonneg_left _ hκ.sigma_nonneg
    refine add_le_add_right ?_ _
    have hp := rg_peetre (d := d) z hi
    have h4 : (0 : ℝ) ≤ 4 ^ (s + 1) * a0 := by positivity
    calc 4 ^ (s + 1) * a0 * (1 + ‖xs i - z‖) ^ (-((d : ℝ) + 1))
        ≤ 4 ^ (s + 1) * a0 * (2 ^ ((d : ℝ) + 1) * (1 + ‖x₀ - z‖) ^ (-((d : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hp h4
      _ = 4 ^ (s + 1) * (a0 * 2 ^ ((d : ℝ) + 1)) * (1 + ‖x₀ - z‖) ^ (-((d : ℝ) + 1)) := by ring
  · refine Eventually.of_forall fun z => ?_
    refine Tendsto.const_smul ?_ _
    unfold rgR
    by_cases hz : ‖z‖ ≤ 1 / 4
    · simp only [hz, ite_true]
      exact ((hg.continuous.tendsto _).comp (hx.sub_const z)).sub ((hg.continuous.tendsto _).comp hx)
    · simp only [hz, ite_false]
      exact (hg.continuous.tendsto _).comp (hx.sub_const z)

theorem s57p_Tdiff (hd : 1 ≤ d) {s σ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ}
    (hκ : RgKer d s σ κ) : ∀ (m : ℕ) {Fb : Type} [NormedAddCommGroup Fb] [NormedSpace ℝ Fb]
      [CompleteSpace Fb] (a : ℕ → ℝ), (∀ l, 0 ≤ a l) → ∀ f : Euc d → Fb, RgDecay (m + 1) a f →
      ContDiff ℝ m (rgT κ f) ∧ ∀ l, l ≤ m → ∀ x : Euc d,
        ‖iteratedFDeriv ℝ l (rgT κ f) x‖ ≤
          σ * (a (l + 1) * rgNear d s + 4 ^ (s + 1) * a l * rgW d) := by
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  intro m
  induction m with
  | zero =>
    intro Fb _ _ _ a ha f h
    obtain ⟨hc, hb⟩ := h
    have hf1 : ContDiff ℝ 1 f := by simpa using hc
    have hfd : Differentiable ℝ f := hf1.differentiable (by norm_num)
    have h0 : ∀ y, ‖f y‖ ≤ a 0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := fun y => by
      have := hb 0 (by omega) y
      rwa [norm_iteratedFDeriv_zero] at this
    have h1 : ∀ y, ‖fderiv ℝ f y‖ ≤ a 1 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := fun y => by
      have := hb 1 (by omega) y
      rwa [norm_iteratedFDeriv_one] at this
    have h1' : ∀ y, ‖fderiv ℝ f y‖ ≤ a 1 := fun y =>
      (h1 y).trans (by calc a 1 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ a 1 * 1 :=
                            mul_le_mul_of_nonneg_left (hw y) (ha 1)
                        _ = a 1 := mul_one _)
    refine ⟨contDiff_zero.2 (s57p_rgT_continuous hd hs0 hsd hκ hfd (ha 0) (ha 1) h0 h1'), fun l hl x => ?_⟩
    have : l = 0 := by omega
    subst this
    rw [norm_iteratedFDeriv_zero]
    exact rg_norm_T_le hd hs0 hsd hκ hfd (ha 0) (ha 1) h0 h1' x
  | succ m ih =>
    intro Fb _ _ _ a ha f h
    have hd1 : ∀ x, HasFDerivAt (rgT κ f) (rgT κ (fderiv ℝ f) x) x := fun x =>
      rg_hasFDerivAt_decay hd hs0 hsd hκ (by omega) ha h x
    have hfd : fderiv ℝ (rgT κ f) = rgT κ (fderiv ℝ f) := by
      funext x; exact (hd1 x).fderiv
    have hdf : RgDecay (m + 1) (fun l => a (l + 1)) (fderiv ℝ f) := by
      obtain ⟨hc, hb⟩ := h
      refine ⟨hc.fderiv_right (m := (m + 1 : ℕ)) (by push_cast; ring_nf; exact le_rfl), fun l hl y => ?_⟩
      have := hb (l + 1) (by omega) y
      rwa [← norm_iteratedFDeriv_fderiv] at this
    obtain ⟨hc, hb⟩ := ih (fun l => a (l + 1)) (fun l => ha (l + 1)) (fderiv ℝ f) hdf
    refine ⟨?_, fun l hl x => ?_⟩
    · push_cast
      refine contDiff_succ_iff_fderiv.2 ⟨fun x => (hd1 x).differentiableAt, ?_, ?_⟩
      · intro h; exact absurd h (by simp)
      · rw [hfd]; exact hc
    · rcases l with _ | l
      · rw [norm_iteratedFDeriv_zero]
        exact rg_bound0 hd hs0 hsd hκ (by omega) ha h x
      · rw [← norm_iteratedFDeriv_fderiv, hfd]
        exact hb l (by omega) x

theorem s57p_conv_comp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {k : ℕ} {A : ℝ} (hA : 0 ≤ A)
    {h : Euc d → ℝ} (hh : RgDecay (k + 1) (fun _ => A) h) (j : Fin d) :
    RgW (fun _ => 1) k (movtr_sigma s * (A * rgNear d s + 4 ^ (s + 1) * A * rgW d))
      (fun x => (convGradConvW (rieszKernelGrad d s) h x) j) := by
  have hκ := rgKerComp_ok (d := d) hs0 j
  obtain ⟨hc, hb⟩ := s57p_Tdiff hd hs0 hsd hκ k (fun _ => A) (fun _ => hA) h hh
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have h1c : ContDiff ℝ 1 h := by
    have := hh.1
    exact this.of_le (by exact_mod_cast (by omega : 1 ≤ k + 1))
  have h0 : ∀ y, ‖h y‖ ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := fun y => by
    have := hh.2 0 (by omega) y
    rwa [norm_iteratedFDeriv_zero] at this
  have h1 : ∀ y, ‖fderiv ℝ h y‖ ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := fun y => by
    have := hh.2 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  have h1' : ∀ y, ‖fderiv ℝ h y‖ ≤ A := fun y =>
    (h1 y).trans (by calc A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ A * 1 :=
                          mul_le_mul_of_nonneg_left (hw y) hA
                      _ = A := mul_one _)
  have hfun : (fun x => (convGradConvW (rieszKernelGrad d s) h x) j) = rgT (fun z => (rieszKernelGrad d s z) j) h := by
    funext x
    exact rg_force_comp hd hs0 hsd (h1c.differentiable (by norm_num)) hA hA h0 h1' x j
  rw [hfun]
  exact ⟨hc, fun n hn x => by simpa using hb n hn x⟩

/-- the nonlocal term, optimal order: `C^k` output from `C^{k+1}` density and `C^{k+1}` vector field -/
theorem s57p_T3 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {k : ℕ} {Aρ Bg : ℝ} (hAρ : 0 ≤ Aρ)
    (hBg : 0 ≤ Bg) {ρ : Euc d → ℝ} (hρ : RgDecay (k + 1) (fun _ => Aρ) ρ)
    {g : Fin d → Euc d → ℝ} (hg : ∀ j, RgW (fun _ => 1) (k + 1) Bg (g j)) :
    RgW (fun _ => 1) k
      (d * (movtr_sigma s * ((2 ^ (k + 1) * Aρ * Bg) * rgNear d s +
        4 ^ (s + 1) * (2 ^ (k + 1) * Aρ * Bg) * rgW d)))
      (fun x => ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s) (fun y => ρ y * g j y) x) j) := by
  have hw0 : ∀ y : Euc d, 0 ≤ (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := fun y =>
    Real.rpow_nonneg (by positivity) _
  have hcf : 0 ≤ 2 ^ (k + 1) * Aρ * Bg := by positivity
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      RgW (fun _ => (1 : ℝ)) k (movtr_sigma s * ((2 ^ (k + 1) * Aρ * Bg) * rgNear d s +
        4 ^ (s + 1) * (2 ^ (k + 1) * Aρ * Bg) * rgW d))
      (fun x => (convGradConvW (rieszKernelGrad d s) (fun y => ρ y * g j y) x) j) := by
    intro j _
    have hmul := RgW.mul (w := fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) (k := k + 1) hw0 hAρ hBg hρ (hg j)
    exact s57p_conv_comp hd hs0 hsd hcf hmul j
  have hs := RgW.sum (w := fun _ : Euc d => (1 : ℝ)) (k := k) Finset.univ hterm
  simpa [Finset.sum_const] using hs

/-- the constant of `s57p_gen_diff` (depends on `d, s, M, N'` only) -/
def s57pCg (d : ℕ) (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (N' : ℕ) : ℝ :=
  d + d * 2 ^ (N' + 1) + d * (movtr_sigma s * ((2 ^ (N' + 1 + 1) * ((d : ℝ) ^ (N' + 2) * 1 * 2 ^ ((d : ℝ) + 3)) *
      ((d : ℝ) * (∑ i, ∑ j, |M i j|))) * rgNear d s +
    4 ^ (s + 1) * (2 ^ (N' + 1 + 1) * ((d : ℝ) ^ (N' + 2) * 1 * 2 ^ ((d : ℝ) + 3)) *
      ((d : ℝ) * (∑ i, ∑ j, |M i j|))) * rgW d))

theorem s57pCg_nonneg {s : ℝ} (hs0 : 0 ≤ s) (M : Matrix (Fin d) (Fin d) ℝ) (N' : ℕ) : 0 ≤ s57pCg d s M N' := by
  unfold s57pCg
  have hσ : 0 ≤ movtr_sigma s := rg_sigma_nonneg hs0
  have hnear := rg_near_nonneg (d := d) s
  have hW := rg_W_nonneg (d := d)
  have hMB0 : 0 ≤ ∑ i, ∑ j, |M i j| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  positivity

/-- **The difference of two generators**: output order `N'+1`, input `φ ∈ C^{N'+3}`. -/
theorem s57p_gen_diff {s : ℝ} (M Q : Matrix (Fin d) (Fin d) ℝ) {ν νN : ℝ} {c cN : ℝ → Euc d → Euc d}
    {ρ ρN : ℝ → Euc d → ℝ} {T : ℝ} (hD : S57pFeData s Q ν c ρ T) (hDN : S57pFeData s Q νN cN ρN T)
    (N' : ℕ) {K' : ℕ} (hK' : N' + 3 ≤ K') {L' : ℝ} (hL' : (d : ℝ) + 3 ≤ L') {Dν Dc Dρ : ℝ}
    (hν : |ν - νN| ≤ Dν)
    (hc : ∀ τ ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ K' (c τ) ∧ ContDiff ℝ K' (cN τ) ∧
      cbNormVecE K' (fun x => c τ x - cN τ x) ≤ ENNReal.ofReal Dc)
    (hρ : ∀ τ ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ K' (ρ τ) ∧ ContDiff ℝ K' (ρN τ) ∧
      weightedSupE K' L' (fun x => ρN τ x - ρ τ x) ≤ ENNReal.ofReal Dρ) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ (B : ℝ) (φ : Euc d → ℝ), 0 ≤ B →
      ContDiff ℝ (N' + 3 : ℕ) φ → (∀ i ≤ N' + 3, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ B) →
      RgW (fun _ : Euc d => (1 : ℝ)) (N' + 1) (s57pCg d s M N' * (max Dν 0 + max Dc 0 + max Dρ 0) * B)
        (fun x => generatorW (fixedEqCoeff s M Q ν c ρ) τ φ x - generatorW (fixedEqCoeff s M Q νN cN ρN) τ φ x) := by
  have hd1 := hD.hd
  have hMB := s55f_matBound M
  set MB : ℝ := ∑ i, ∑ j, |M i j| with hMBdef
  have hMB0 : 0 ≤ MB := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hσ : 0 ≤ movtr_sigma s := rg_sigma_nonneg hD.hs0
  have hnear := rg_near_nonneg (d := d) s
  have hW := rg_W_nonneg (d := d)
  set A' : ℝ := (d : ℝ) ^ (N' + 2) * 1 * 2 ^ ((d : ℝ) + 3) with hA'
  -- the constant of the nonlocal part per unit of `D_ρ B`
  set Cn : ℝ := d * (movtr_sigma s * ((2 ^ (N' + 1 + 1) * A' * ((d : ℝ) * MB)) * rgNear d s +
      4 ^ (s + 1) * (2 ^ (N' + 1 + 1) * A' * ((d : ℝ) * MB)) * rgW d)) with hCn
  have hCn0 : 0 ≤ Cn := by rw [hCn, hA']; positivity
  intro τ hτ B φ hB hφ hb
  obtain ⟨hcτ, hcNτ, hcbτ⟩ := hc τ hτ
  obtain ⟨hρτ, hρNτ, hwτ⟩ := hρ τ hτ
  set D1 : ℝ := max Dν 0 with hD1
  set D2 : ℝ := max Dc 0 with hD2
  set D3 : ℝ := max Dρ 0 with hD3
  have hD10 : 0 ≤ D1 := le_max_right _ _
  have hD20 : 0 ≤ D2 := le_max_right _ _
  have hD30 : 0 ≤ D3 := le_max_right _ _
  -- jets of `φ`
  have hφ' : ∀ k ≤ N' + 3, ContDiff ℝ k φ := fun k hk => hφ.of_le (by exact_mod_cast hk)
  -- the pieces
  have P1 : RgW (fun _ : Euc d => (1 : ℝ)) (N' + 1) (|ν - νN| * (d * B)) (fun x => (ν - νN) * Laplacian.laplacian φ x) :=
    (rg_laplacian (k := N' + 1) hφ (fun n hn x => hb n (by omega) x)).const_mul (ν - νN)
  have hcd : ContDiff ℝ (N' + 1 : ℕ) (fun x => c τ x - cN τ x) :=
    (hcτ.sub hcNτ).of_le (by exact_mod_cast (by omega : N' + 1 ≤ K'))
  have hcdb : ∀ i ≤ N' + 1, ∀ x, ‖iteratedFDeriv ℝ i (fun x => c τ x - cN τ x) x‖ ≤ D2 := fun i hi x =>
    s57p_cbVec_bound hcbτ (by omega) x
  have P2j : ∀ j : Fin d, RgW (fun _ : Euc d => (1 : ℝ)) (N' + 1) (2 ^ (N' + 1) * D2 * B)
      (fun x => (c τ x - cN τ x) j * gradient φ x j) := fun j =>
    RgW.mul (w := fun _ : Euc d => (1 : ℝ)) (k := N' + 1) (fun _ => zero_le_one) hD20 hB
      (s57p_comp_RgW1 hcd hcdb j) (rg_grad_comp (k := N' + 1) (hφ' (N' + 1 + 1) (by omega)) (fun n hn x => hb n (by omega) x) j)
  have P2 := RgW.sum (w := fun _ : Euc d => (1 : ℝ)) (k := N' + 1) Finset.univ (fun j _ => P2j j)
  -- the nonlocal part
  set ρ' : Euc d → ℝ := fun x => ρN τ x - ρ τ x with hρ'
  have hρ'c : ContDiff ℝ (N' + 2 : ℕ) ρ' := (hρNτ.sub hρτ).of_le (by exact_mod_cast (by omega : N' + 2 ≤ K'))
  have hρ'w : weightedSupE (N' + 2) L' ρ' ≤ ENNReal.ofReal Dρ :=
    (s57p_wsup_mono_r (by omega : N' + 2 ≤ K') L' ρ').trans hwτ
  have hρ'd : RgDecay (N' + 2) (fun _ => (d : ℝ) ^ (N' + 2) * D3 * 2 ^ ((d : ℝ) + 3)) ρ' :=
    s57p_rgdecay_of_wsup hd1 hL' hρ'c hρ'w
  have hgj : ∀ j : Fin d, RgW (fun _ : Euc d => (1 : ℝ)) (N' + 1 + 1) ((d : ℝ) * MB * B)
      (fun y => Torus.matVec M.transpose (gradient φ y) j) := fun j =>
    rg_matgrad (k := N') hMB hφ (fun n hn x => hb n (by omega) x) j
  have hAρ' : 0 ≤ (d : ℝ) ^ (N' + 2) * D3 * 2 ^ ((d : ℝ) + 3) := by positivity
  have P3 := s57p_T3 hd1 hD.hs0 hD.hsd (k := N' + 1) hAρ' (by positivity : 0 ≤ (d : ℝ) * MB * B) hρ'd hgj
  -- identity of functions
  obtain ⟨A, hA, hdec, -⟩ := hD.rho
  obtain ⟨AN, hAN, hdecN, -⟩ := hDN.rho
  set Am : ℝ := max A AN with hAm
  have hAm0 : 0 ≤ Am := le_max_of_le_left hA
  have hρ2 : RgDecay 2 (fun _ => Am) (ρ τ) :=
    s57p_rgdecay_mono_const (le_max_left _ _) (rg_decay_mono (by norm_num) (hdec τ hτ))
  have hρN2 : RgDecay 2 (fun _ => Am) (ρN τ) :=
    s57p_rgdecay_mono_const (le_max_right _ _) (rg_decay_mono (by norm_num) (hdecN τ hτ))
  have hρ'2 : RgDecay 2 (fun _ => (d : ℝ) ^ (N' + 2) * D3 * 2 ^ ((d : ℝ) + 3)) ρ' :=
    rg_decay_mono (by omega) hρ'd
  have hb3 : ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ B := fun i hi x => hb i (by omega) x
  have hφ3 : ContDiff ℝ 3 φ := hφ' 3 (by omega)
  have hnlj : ∀ x, ∀ j : Fin d,
      (convGradConvW (rieszKernelGrad d s) (fun y => ρ τ y * (Torus.matVec M.transpose (gradient φ y)) j) x) j -
        (convGradConvW (rieszKernelGrad d s) (fun y => ρN τ y * (Torus.matVec M.transpose (gradient φ y)) j) x) j =
      -(convGradConvW (rieszKernelGrad d s) (fun y => ρ' y * (Torus.matVec M.transpose (gradient φ y)) j) x) j := by
    intro x j
    have hc0 : 0 ≤ 2 ^ 2 * Am * ((d : ℝ) * MB * B) := by positivity
    have hd1' : RgDecay 2 (fun _ => 2 ^ 2 * Am * ((d : ℝ) * MB * B))
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient φ y)) j) :=
      s55m_nl_decay hMB hMB0 hAm0 hB hρ2 hφ3 hb3 j
    have hd2' : RgDecay 2 (fun _ => 2 ^ 2 * Am * ((d : ℝ) * MB * B))
        (fun y => ρN τ y * (Torus.matVec M.transpose (gradient φ y)) j) :=
      s55m_nl_decay hMB hMB0 hAm0 hB hρN2 hφ3 hb3 j
    have hd3' : RgDecay 2 (fun _ => 2 ^ 2 * ((d : ℝ) ^ (N' + 2) * D3 * 2 ^ ((d : ℝ) + 3)) * ((d : ℝ) * MB * B))
        (fun y => ρ' y * (Torus.matVec M.transpose (gradient φ y)) j) :=
      s55m_nl_decay hMB hMB0 hAρ' hB hρ'2 hφ3 hb3 j
    rw [s57p_conv_eq hD.hd hD.hs0 hD.hsd hc0 hd1', s57p_conv_eq hD.hd hD.hs0 hD.hsd hc0 hd2',
      s57p_conv_eq hD.hd hD.hs0 hD.hsd (by positivity) hd3']
    have hfun : (fun y => ρ' y * (Torus.matVec M.transpose (gradient φ y)) j) =
        fun y => ρN τ y * (Torus.matVec M.transpose (gradient φ y)) j -
          ρ τ y * (Torus.matVec M.transpose (gradient φ y)) j := by
      funext y; simp only [hρ']; ring
    rw [hfun, s57p_rgT_sub hD.hd hD.hs0 hD.hsd (rgKerComp_ok hD.hs0 j) hc0 hd2' hd1' x]
    ring
  have hid : ∀ x, generatorW (fixedEqCoeff s M Q ν c ρ) τ φ x - generatorW (fixedEqCoeff s M Q νN cN ρN) τ φ x =
      (ν - νN) * Laplacian.laplacian φ x + ∑ j : Fin d, (c τ x - cN τ x) j * gradient φ x j +
        ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s) (fun y => ρ' y * (Torus.matVec M.transpose (gradient φ y)) j) x) j := by
    intro x
    show ν * Laplacian.laplacian φ x + inner ℝ (-(Torus.matVec Q x) + c τ x) (gradient φ x) -
        ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
          (fun y => ρ τ y * (Torus.matVec M.transpose (gradient φ y)) j) x) j -
        (νN * Laplacian.laplacian φ x + inner ℝ (-(Torus.matVec Q x) + cN τ x) (gradient φ x) -
        ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
          (fun y => ρN τ y * (Torus.matVec M.transpose (gradient φ y)) j) x) j) = _
    have e1 : inner ℝ (-(Torus.matVec Q x) + c τ x) (gradient φ x) - inner ℝ (-(Torus.matVec Q x) + cN τ x) (gradient φ x) =
        ∑ j : Fin d, (c τ x - cN τ x) j * gradient φ x j := by
      rw [← inner_sub_left, HRS.Whole.Q09B.q09b_inner_euc]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp
    have e2 : ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
          (fun y => ρN τ y * (Torus.matVec M.transpose (gradient φ y)) j) x) j -
        ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
          (fun y => ρ τ y * (Torus.matVec M.transpose (gradient φ y)) j) x) j =
        ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s) (fun y => ρ' y * (Torus.matVec M.transpose (gradient φ y)) j) x) j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := hnlj x j
      linarith
    linarith
  have hfinal := (P1.add P2).add P3
  have hfun : (fun x => generatorW (fixedEqCoeff s M Q ν c ρ) τ φ x - generatorW (fixedEqCoeff s M Q νN cN ρN) τ φ x) =
      fun x => (ν - νN) * Laplacian.laplacian φ x + ∑ j : Fin d, (c τ x - cN τ x) j * gradient φ x j +
        ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s) (fun y => ρ' y * (Torus.matVec M.transpose (gradient φ y)) j) x) j :=
    funext hid
  rw [hfun]
  have hCg : s57pCg d s M N' = d + d * 2 ^ (N' + 1) + Cn := by simp only [s57pCg, hCn, hA', hMBdef]
  rw [hCg]
  refine hfinal.mono (fun _ => zero_le_one) ?_
  have e3 : (d : ℝ) * (movtr_sigma s * ((2 ^ (N' + 1 + 1) * ((d : ℝ) ^ (N' + 2) * D3 * 2 ^ ((d : ℝ) + 3)) * ((d : ℝ) * MB * B)) * rgNear d s +
      4 ^ (s + 1) * (2 ^ (N' + 1 + 1) * ((d : ℝ) ^ (N' + 2) * D3 * 2 ^ ((d : ℝ) + 3)) * ((d : ℝ) * MB * B)) * rgW d)) =
      D3 * B * Cn := by
    simp only [hCn, hA']; ring
  have e2 : ∑ j : Fin d, 2 ^ (N' + 1) * D2 * B = (d : ℝ) * (2 ^ (N' + 1) * D2 * B) := by simp
  have h1 : |ν - νN| * ((d : ℝ) * B) ≤ D1 * ((d : ℝ) * B) :=
    mul_le_mul_of_nonneg_right (hν.trans (le_max_left _ _)) (by positivity)
  rw [e3, e2]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hp : (0 : ℝ) ≤ 2 ^ (N' + 1) := by positivity
  nlinarith [h1, mul_nonneg (mul_nonneg hd0 hB) hD20, mul_nonneg (mul_nonneg hd0 hB) hD30,
    mul_nonneg (mul_nonneg (mul_nonneg hd0 hp) hB) hD10, mul_nonneg (mul_nonneg (mul_nonneg hd0 hp) hB) hD30,
    mul_nonneg (mul_nonneg hCn0 hB) hD10, mul_nonneg (mul_nonneg hCn0 hB) hD20]

end HRS.MS.FixEq
