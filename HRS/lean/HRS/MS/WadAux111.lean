import HRS.MS.WadAux110

/-!
# S8.3, packet S8F-11: mollification commutes with derivatives; density of `C_c^∞` in the weighted jet norm

`s8f_Mol ψ g x = ∫ ψ_normed(t) • g (x - t) dt`.  `s8f_Mol_hasFDerivAt`: `D(ψ ⋆ g) = ψ ⋆ Dg` for `g ∈ C^1_c`.
`s8f_Mol_err`: if the oscillation of `D^i g` at scale `ψ.rOut` is at most `ε` then `‖D^i(ψ ⋆ g) - D^i g‖ ≤ ε`.
`s8f_jet_approx`: if `f ∈ C^k` and `D^i f / ⟨·⟩^M → 0` at infinity (`i ≤ k`), then for every `ε > 0` there is `φ ∈ C_c^∞` with
`‖D^i(φ - f)(y)‖ ≤ ε ⟨y⟩^M` for all `i ≤ k`, `y` (cutoff, then mollification).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff Convolution

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

def s8f_Mol {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (ψ : ContDiffBump (0 : Euc d))
    (g : Euc d → F) : Euc d → F :=
  fun x => ∫ t, ψ.normed volume t • g (x - t)

theorem s8f_Mol_eq {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (ψ : ContDiffBump (0 : Euc d))
    (g : Euc d → F) :
    s8f_Mol ψ g = (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g : Euc d → F) := rfl

theorem s8f_norm_iter0_pts {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : Euc d → F) (x y : Euc d) :
    ‖iteratedFDeriv ℝ 0 g x - iteratedFDeriv ℝ 0 g y‖ = ‖g x - g y‖ := by
  rw [iteratedFDeriv_zero_eq_comp]
  simp only [Function.comp_apply]
  rw [← dist_eq_norm, ← dist_eq_norm, LinearIsometryEquiv.dist_map]

theorem s8f_Mol_hasFDerivAt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (ψ : ContDiffBump (0 : Euc d))
    {g : Euc d → F} (hc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (x : Euc d) :
    HasFDerivAt (s8f_Mol ψ g) (s8f_Mol ψ (fderiv ℝ g) x) x := by
  have hli : LocallyIntegrable (ψ.normed (volume : Measure (Euc d))) volume :=
    (ψ.continuous_normed (μ := (volume : Measure (Euc d)))).locallyIntegrable
  have := hc.hasFDerivAt_convolution_right (μ := (volume : Measure (Euc d)))
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F) hli hg x
  refine this.congr_fderiv ?_
  unfold s8f_Mol
  simp only [convolution_def, ContinuousLinearMap.precompR_apply]
  congr 1

theorem s8f_Mol_err (ψ : ContDiffBump (0 : Euc d)) : ∀ (i : ℕ) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (g : Euc d → F), HasCompactSupport g → ContDiff ℝ i g → ∀ {ε : ℝ},
    (∀ x y, dist x y < ψ.rOut → ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ ≤ ε) → ∀ y,
    ‖iteratedFDeriv ℝ i (s8f_Mol ψ g) y - iteratedFDeriv ℝ i g y‖ ≤ ε := by
  intro i
  induction i with
  | zero =>
    intro F _ _ _ g hc hg ε hmod y
    rw [s8f_norm_iter0_sub, ← dist_eq_norm]
    rw [s8f_Mol_eq]
    refine ψ.dist_normed_convolution_le (μ := volume) hg.continuous.aestronglyMeasurable (fun x hx => ?_)
    have := hmod x y (by rw [mem_ball] at hx; exact hx)
    rwa [s8f_norm_iter0_pts, ← dist_eq_norm] at this
  | succ i ih =>
    intro F _ _ _ g hc hg ε hmod y
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_cast; omega)
    have hDg : ContDiff ℝ i (fderiv ℝ g) := hg.fderiv_right (by norm_cast)
    have hfd : fderiv ℝ (s8f_Mol ψ g) = s8f_Mol ψ (fderiv ℝ g) :=
      funext fun x => (s8f_Mol_hasFDerivAt ψ hc hg1 x).fderiv
    rw [← s8f_norm_iter_sub', hfd]
    refine ih (F := Euc d →L[ℝ] F) (fderiv ℝ g) (hc.fderiv ℝ) hDg (fun x x' hxx => ?_) y
    rw [s8f_norm_iter_sub]
    exact hmod x x' hxx

theorem s8f_jet_approx {M : ℝ} (hM : 0 ≤ M) {k : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ k f)
    (hdec : ∀ i ≤ k, Tendsto (fun x => ‖iteratedFDeriv ℝ i f x‖ / jbracket x ^ M) (cocompact (Euc d)) (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Euc d → ℝ, S85Cc φ ∧
      ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i (fun x => φ x - f x) y‖ ≤ ε * jbracket y ^ M := by
  obtain ⟨χ, hχd, hχc, hχe⟩ := s8f_cutoff_error hM hf hdec (half_pos hε)
  set g : Euc d → ℝ := fun y => χ y * f y with hg
  have hgk : ContDiff ℝ k g := (hχd.of_le (by exact_mod_cast le_top)).mul hf
  have hgc : HasCompactSupport g := hχc.mul_right
  have hunif : ∀ i : Fin (k + 1), ∃ δ > 0, ∀ x y : Euc d, dist x y < δ →
      ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ ≤ ε / 2 := by
    intro i
    have hcont : Continuous (iteratedFDeriv ℝ i g) :=
      hgk.continuous_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_iff.1 i.2)
    have hcs : HasCompactSupport (iteratedFDeriv ℝ i g) := hgc.iteratedFDeriv i
    obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1 (hcs.uniformContinuous_of_continuous hcont)
      (ε / 2) (half_pos hε)
    exact ⟨δ, hδ, fun x y hxy => by rw [← dist_eq_norm]; exact (h hxy).le⟩
  choose δ hδ hδ' using hunif
  have hne : (Finset.univ : Finset (Fin (k + 1))).Nonempty := Finset.univ_nonempty
  set r : ℝ := Finset.univ.inf' hne δ with hr
  have hr0 : 0 < r := by
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' hne δ
    rw [hr, hj]
    exact hδ j
  have hrδ : ∀ i : Fin (k + 1), r ≤ δ i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  set ψ : ContDiffBump (0 : Euc d) := ⟨r / 2, r, half_pos hr0, half_lt_self hr0⟩ with hψ
  have hψr : ψ.rOut = r := rfl
  have hgloc : LocallyIntegrable g volume := hgk.continuous.locallyIntegrable
  have hφd : ContDiff ℝ ∞ (s8f_Mol ψ g) := by
    rw [s8f_Mol_eq]
    exact ψ.hasCompactSupport_normed.contDiff_convolution_left _ ψ.contDiff_normed hgloc
  have hφc : HasCompactSupport (s8f_Mol ψ g) := by
    rw [s8f_Mol_eq]
    exact ψ.hasCompactSupport_normed.convolution _ hgc
  refine ⟨s8f_Mol ψ g, ⟨hφd, hφc⟩, fun i hi y => ?_⟩
  have hφi : ContDiff ℝ i (s8f_Mol ψ g) := hφd.of_le (by exact_mod_cast le_top)
  have hfi : ContDiff ℝ i f := hf.of_le (by exact_mod_cast hi)
  have hgi : ContDiff ℝ i g := hgk.of_le (by exact_mod_cast hi)
  have e1 : iteratedFDeriv ℝ i (fun x => s8f_Mol ψ g x - f x) y =
      iteratedFDeriv ℝ i (s8f_Mol ψ g) y - iteratedFDeriv ℝ i f y := by
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := y) (i := i) hφi.contDiffAt hfi.contDiffAt
    simpa [Pi.sub_def] using this
  have e2 : iteratedFDeriv ℝ i (fun x => g x - f x) y = iteratedFDeriv ℝ i g y - iteratedFDeriv ℝ i f y := by
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := y) (i := i) hgi.contDiffAt hfi.contDiffAt
    simpa [Pi.sub_def] using this
  have h1 := s8f_Mol_err ψ i g hgc hgi (ε := ε / 2) (fun x x' hxx => hδ' ⟨i, by omega⟩ x x'
    (lt_of_lt_of_le hxx (hψr ▸ hrδ ⟨i, by omega⟩))) y
  have h2 := hχe i hi y
  rw [e1]
  have hJ : 1 ≤ jbracket y ^ M := Real.one_le_rpow (s83_one_le_jb y) hM
  have hsplit : iteratedFDeriv ℝ i (s8f_Mol ψ g) y - iteratedFDeriv ℝ i f y =
      (iteratedFDeriv ℝ i (s8f_Mol ψ g) y - iteratedFDeriv ℝ i g y) +
        iteratedFDeriv ℝ i (fun x => g x - f x) y := by
    rw [e2]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h2' : ‖iteratedFDeriv ℝ i (fun x => g x - f x) y‖ ≤ ε / 2 * jbracket y ^ M := h2
  nlinarith

end HRS.MS.Wad
