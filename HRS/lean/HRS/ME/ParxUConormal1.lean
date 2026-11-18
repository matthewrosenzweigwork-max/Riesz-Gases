import HRS.ME.ParxU
import HRS.Equilibrium.Parametrix.PX2AuxB
import HRS.Equilibrium.Parametrix.PX3aAuxW

/-!
# Packet P1a (part 1): uniform row bounds for conormal kernels

Uniform versions (constants chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.conormal_row_smooth_aux` and `HRS.Parx.conormal_row_int`.

The only quantitative input on `ρ` in the old proofs was the sup of the iterated derivatives
of `Torus.lift ρ` (`bdd_iteratedFDeriv_lift`, resp. `exists_density_bound`). Here it is replaced by
`‖iteratedFDeriv ℝ n (lift ρ)‖ ≤ cbNorm N ρ ≤ Λ₀ ≤ |Λ₀|` (`n ≤ N`) and `ρ ≤ |Λ₀|`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- Uniform `C^n` bound of `lift ρ` for `n ≤ N`, from the bundle. -/
theorem iter_lift_le_unif {β : ℝ} {V ρ : Torus d → ℝ} (U : ParxU d s N νm νp c₀ Λ₀ β V ρ)
    {n : ℕ} (hn : n ≤ N) (y : Euc d) :
    ‖iteratedFDeriv ℝ n (Torus.lift ρ) y‖ ≤ |Λ₀| :=
  (HRS.PDE.MFPair.norm_iter_le_cb_ps (L := N) U.F.hρC (i := n) hn y).trans
    ((U.cbNorm_rho_le le_rfl).trans (le_abs_self _))

/-- **Uniform version of `conormal_row_smooth_aux`.** The constant depends only on
`(d, σ, b, m, Λ₀)`; it is chosen before `β, V, ρ`. -/
theorem conormal_row_smooth_aux_unif (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) (b m : ℕ) (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      Torus.IsCk (m : WithTop ℕ∞) (fun x => ∫ y, F x y ∂(withDensityReal ρ)) ∧
      Torus.cbNorm m (fun x => ∫ y, F x y ∂(withDensityReal ρ)) ≤ C * B := by
  set S : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |Λ₀| with hS
  have hS0 : ∀ k, 0 ≤ S k := fun k =>
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  set ν : Measure (Euc d) := (volume : Measure (Euc d)).restrict (LocalDivAux.cube d) with hν
  set Cint : ℝ := ∫ w, envW d σ b w ∂ν with hCint
  have hCint0 : 0 ≤ Cint :=
    integral_nonneg fun w => (show (0 : ℝ) ≤ envW d σ b w by linarith [one_le_envW (d := d) σ b w])
  have henv : Integrable (envW d σ b) ν := integrableOn_cube_envW hd hσ b
  refine ⟨∑ k ∈ Finset.range (m + 1), S k * Cint,
    Finset.sum_nonneg fun k _ => mul_nonneg (hS0 k) hCint0, fun β V ρ U B F hB hF => ?_⟩
  have hρ : SmoothPosDensity ρ := U.H.rho_smooth
  have hρs : ContDiff ℝ ∞' (Torus.lift ρ) := hρ.smooth
  set K : Euc d → Euc d → ℝ := fun x' w => lift2 F (x', x' - w) * Torus.lift ρ (x' - w) with hK
  have hH : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 F) (offDiag d) := hF.smooth
  have hKfull : ContDiffOn ℝ (m : WithTop ℕ∞)
      (fun p : Euc d × Euc d => lift2 F p * Torus.lift ρ p.2) (offDiag d) :=
    hH.mul ((hρs.of_le (by exact_mod_cast le_top)).comp contDiff_snd).contDiffOn
  -- smoothness of the slices
  have hPsm : ∀ w : Euc d, Torus.mk w ≠ 0 → ContDiff ℝ (m : WithTop ℕ∞) (fun x' : Euc d => lift2 F (x', x' - w)) := by
    intro w hw
    have hA : ContDiff ℝ (m : WithTop ℕ∞) (fun x' : Euc d => (x', x' - w)) :=
      contDiff_id.prodMk (contDiff_id.sub contDiff_const)
    have := hH.comp (hA.contDiffOn (s := Set.univ)) (fun x' _ => by
      show (x', x' - w) ∈ offDiag d
      rw [px2_mem_offDiag_iff]; simp only [sub_sub_cancel]; exact hw)
    exact contDiffOn_univ.mp this
  have hQsm : ∀ w : Euc d, ContDiff ℝ (m : WithTop ℕ∞) (fun x' : Euc d => Torus.lift ρ (x' - w)) := fun w =>
    ((hρs.of_le (by exact_mod_cast le_top)).comp (contDiff_id.sub contDiff_const))
  -- pointwise bound (the derivatives of ρ are bounded by the uniform constant `|Λ₀|`)
  have hbound : ∀ k : ℕ, k ≤ m → ∀ᵐ w ∂ν, ∀ x, ‖iteratedFDeriv ℝ k (fun x' => K x' w) x‖ ≤
      B * S k * envW d σ b w := by
    intro k hk
    filter_upwards [ae_restrict_mem LocalDivAux.measurableSet_cube, ae_cube_mk_ne_zero hd] with w hwc hw
    intro x
    have hwb : ∀ i, |w i| ≤ 1 / 2 := fun i => LocalDivAux.abs_le_half_of_cube hwc i
    have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (hPsm w hw) (hQsm w) x (n := k) (by exact_mod_cast hk)
    refine h1.trans ?_
    calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x' : Euc d => lift2 F (x', x' - w)) x‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun x' : Euc d => Torus.lift ρ (x' - w)) x‖
        ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (B * envW d σ b w) * |Λ₀| := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
          have e1 := norm_slice_le hB hF hw hwb x hi'
          have e2 : ‖iteratedFDeriv ℝ (k - i) (fun x' : Euc d => Torus.lift ρ (x' - w)) x‖ ≤ |Λ₀| := by
            rw [iteratedFDeriv_comp_sub (f := Torus.lift ρ) (k - i) w x]
            exact iter_lift_le_unif U (by omega) _
          have hc : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
          have hE : 0 ≤ B * envW d σ b w := mul_nonneg hB (by linarith [one_le_envW (d := d) σ b w])
          exact mul_le_mul (mul_le_mul_of_nonneg_left e1 hc) e2 (norm_nonneg _) (mul_nonneg hc hE)
      _ = B * S k * envW d σ b w := by
          rw [hS]; simp only
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  -- hypotheses of the parametric lemma
  have hparam : ParamHyp m K ν := by
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [ae_cube_mk_ne_zero hd] with w hw
      exact (hPsm w hw).mul (hQsm w)
    · intro k hk x
      -- continuity on the open set `{mk w ≠ 0}`
      have hU : IsOpen {w : Euc d | Torus.mk w ≠ 0} := isOpen_mk_ne_zero'
      have hcont : ContinuousOn (fun w : Euc d => iteratedFDeriv ℝ k (fun x' => K x' w) x)
          {w : Euc d | Torus.mk w ≠ 0} := by
        have h1 : ContinuousOn (iteratedFDeriv ℝ k (fun p : Euc d × Euc d => lift2 F p * Torus.lift ρ p.2))
            (offDiag d) := by
          have := hKfull.continuousOn_iteratedFDerivWithin (m := k) (by exact_mod_cast hk)
            px2_isOpen_offDiag.uniqueDiffOn
          exact this.congr (iteratedFDerivWithin_of_isOpen k px2_isOpen_offDiag).symm
        have h2 : ContinuousOn (fun w : Euc d => iteratedFDeriv ℝ k
            (fun p : Euc d × Euc d => lift2 F p * Torus.lift ρ p.2) (x, x - w))
            {w : Euc d | Torus.mk w ≠ 0} := by
          refine h1.comp (continuous_const.prodMk (continuous_const.sub continuous_id)).continuousOn ?_
          intro w hw
          show (x, x - w) ∈ offDiag d
          rw [px2_mem_offDiag_iff]; simp only [sub_sub_cancel]; exact hw
        have h3 := (ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin k => diagCLM d) : ContinuousMultilinearMap ℝ (fun _ : Fin k => Euc d × Euc d) ℝ →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin k => Euc d) ℝ).continuous.comp_continuousOn h2
        refine h3.congr fun w hw => ?_
        have := iteratedFDeriv_slice (H := fun p : Euc d × Euc d => lift2 F p * Torus.lift ρ p.2)
          hKfull (w := w) (x := x) hw (i := k) (by exact_mod_cast hk)
        simpa [hK] using this
      have hmeas : AEStronglyMeasurable (fun w : Euc d => iteratedFDeriv ℝ k (fun x' => K x' w) x)
          (ν.restrict {w : Euc d | Torus.mk w ≠ 0}) :=
        hcont.aestronglyMeasurable hU.measurableSet
      have hres : ν.restrict {w : Euc d | Torus.mk w ≠ 0} = ν :=
        Measure.restrict_eq_self_of_ae_mem (ae_cube_mk_ne_zero hd)
      rwa [hres] at hmeas
    · intro k hk
      refine ⟨fun w => B * S k * envW d σ b w, henv.const_mul _, hbound k hk⟩
  obtain ⟨hcd, hform⟩ := contDiff_integral_param_aux m K hparam
  have hrow : (fun x₀ : Euc d => ∫ y, F (Torus.mk x₀) y ∂(withDensityReal ρ)) =
      fun x₀ => ∫ w, K x₀ w ∂ν := by
    funext x₀
    exact row_eq_cube hρ.density.measurable hρ.density.nonneg F x₀
  have hlift : Torus.lift (fun x => ∫ y, F x y ∂(withDensityReal ρ)) =
      fun x₀ => ∫ w, K x₀ w ∂ν := hrow
  refine ⟨?_, ?_⟩
  · unfold Torus.IsCk
    rw [hlift]; exact hcd
  · unfold Torus.cbNorm
    rw [hlift]
    have hk : ∀ k ∈ Finset.range (m + 1), ⨆ x : Euc d, ‖iteratedFDeriv ℝ k (fun x₀ => ∫ w, K x₀ w ∂ν) x‖ ≤
        B * (S k * Cint) := by
      intro k hk'
      have hkm : k ≤ m := by have := Finset.mem_range.mp hk'; omega
      refine ciSup_le fun x => ?_
      rw [hform k hkm x]
      have hint : ∫ w, B * S k * envW d σ b w ∂ν = B * (S k * Cint) := by
        rw [integral_const_mul, hCint]; ring
      rw [← hint]
      exact norm_integral_le_of_norm_le (henv.const_mul _) ((hbound k hkm).mono fun w hw => hw x)
    calc _ ≤ ∑ k ∈ Finset.range (m + 1), B * (S k * Cint) := Finset.sum_le_sum hk
      _ = (∑ k ∈ Finset.range (m + 1), S k * Cint) * B := by
          rw [← Finset.mul_sum]; ring

/-- **Uniform version of `conormal_row_int`.** The constant is `|Λ₀| · ∫_cube envW` and depends only on
`(d, σ, b, Λ₀)`; it is chosen before `β, V, ρ`. -/
theorem conormal_row_int_unif (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) (b : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (H : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b 0 B H →
      (∀ x, H x x = 0) → ∀ x, Integrable (fun y => H x y) (withDensityReal ρ) ∧
        ∫ y, |H x y| ∂(withDensityReal ρ) ≤ K * B := by
  have hI0 : 0 ≤ ∫ w in LocalDivAux.cube d, envW d σ b w :=
    setIntegral_nonneg LocalDivAux.measurableSet_cube fun w _ => by
      linarith [one_le_envW (d := d) σ b w]
  refine ⟨|Λ₀| * ∫ w in LocalDivAux.cube d, envW d σ b w, mul_nonneg (abs_nonneg _) hI0,
    fun β V ρ U B H hB hH hdiag x => ?_⟩
  have hρ : SmoothPosDensity ρ := U.H.rho_smooth
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hRm : ∀ y, ρ y ≤ |Λ₀| := fun y => (U.rho_le y).trans (le_abs_self _)
  have hmeas : Measurable fun p : Torus d × Torus d => H p.1 p.2 := measurable_of_conormal hH hdiag
  set g : ℝ → ℝ := fun t => B * (1 + t ^ (-σ) * (1 + |Real.log t|) ^ b) with hg
  have hgi : IntegrableOn (fun w : Euc d => g ‖w‖) (LocalDivAux.cube d) :=
    (integrableOn_cube_envW hd hσ b).const_mul B
  have hbd : ∀ x y, |H x y| ≤ g (Torus.eucDist x y) :=
    fun x y => abs_le_envW_of_conormal hB hH hdiag x y
  obtain ⟨hint, _⟩ := LocalDivAux.kernel_int hρ hRm hmeas hbd hgi x
  refine ⟨hint, ?_⟩
  have hmeas' : Measurable fun p : Torus d × Torus d => |H p.1 p.2| := hmeas.abs
  have hbd' : ∀ x y, |(fun x y => |H x y|) x y| ≤ g (Torus.eucDist x y) := by
    intro x y; simpa using hbd x y
  obtain ⟨_, hb'⟩ := LocalDivAux.kernel_int hρ hRm hmeas' hbd' hgi x
  refine (le_abs_self _).trans (hb'.trans (le_of_eq ?_))
  have : ∫ w in LocalDivAux.cube d, g ‖w‖ = B * ∫ w in LocalDivAux.cube d, envW d σ b w := by
    rw [← integral_const_mul]; rfl
  rw [this]
  ring

end HRS.ME.ParxU

end
