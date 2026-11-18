import HRS.MS.CritForceFeat2

/-!
# S8.2 core X1, part 3: the weighted semigroup fixes constants; classical solutions equal the
semigroup up to an additive constant

* `s82_U_const`: `s85_Ulim … t 1 = 1`.
* `s82_classical_eq_Ulim`: if `w` is a classical adjoint solution on `[0,v]` with datum `φ ∈ C_M`, then for
  `r ∈ [0,v]` the function `w r` equals `U_{v-r} φ` plus a constant, where `U = s85_Ulim` (the unique
  weighted semigroup).  Hence all derivatives of order `≥ 1` of `w r` and of `U_{v-r}φ` agree.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82BD

open HRS HRS.Whole

variable {d : ℕ}

theorem s82_gen_zero (a β : ℝ) (ρ : Euc d → ℝ) (r : ℝ) (x : Euc d) :
    generatorW (critCoeff d a β ρ) r (fun _ => (0 : ℝ)) x = 0 := by
  simp [generatorW, gradient, Torus.matVec, convGradConvW]

theorem s82_gen_const (a β : ℝ) (ρ : Euc d → ℝ) (r c : ℝ) (x : Euc d) :
    generatorW (critCoeff d a β ρ) r (fun _ => c) x = 0 := by
  have h := HRS.MS.Wad.s85_gen_add_const a β ρ r (fun _ => (0 : ℝ)) c x
  simp only [zero_add] at h
  rw [h]
  exact s82_gen_zero a β ρ r x

theorem s82_const_memCM {M : ℝ} (hM : 0 < M) (c : ℝ) : MemCM M (fun _ : Euc d => c) := by
  refine ⟨continuous_const, ?_⟩
  have h1 : Tendsto (fun x : Euc d => ‖x‖ ^ M) (cocompact (Euc d)) atTop :=
    (tendsto_rpow_atTop hM).comp tendsto_norm_cocompact_atTop
  have h2 : Tendsto (fun x : Euc d => jbracket x ^ M) (cocompact (Euc d)) atTop := by
    refine tendsto_atTop_mono (fun x => ?_) h1
    refine Real.rpow_le_rpow (norm_nonneg _) ?_ hM.le
    unfold jbracket
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖x‖])
  exact tendsto_const_nhds.div_atTop h2

theorem s82_const_classical (a β : ℝ) (ρ : Euc d → ℝ) (t c : ℝ) :
    IsClassicalAdjointW (critCoeff d a β ρ) t (fun _ => c) (fun _ _ => c) := by
  refine ⟨fun r _ => contDiff_const, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro j _
    refine ⟨|c|, fun r _ x => ?_⟩
    rcases j with _ | j
    · simp [norm_iteratedFDeriv_zero]
    · rw [iteratedFDeriv_const_of_ne (by omega)]
      simp
  · intro j _
    exact (contDiff_const.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).comp
      continuous_snd
  · intro x r _
    simp only [s82_gen_const a β ρ r c x, neg_zero]
    exact hasDerivAt_const r c
  · simp only [s82_gen_const]
    exact continuous_const
  · exact ⟨0, fun r _ x => by simp [s82_gen_const]⟩

theorem s82_U_const (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) {M : ℝ} (hM : 0 < M) {t : ℝ} (ht : 0 ≤ t)
    (c : ℝ) (x : Euc d) : HRS.MS.Wad.s85_Ulim a β ρ M t (fun _ => c) x = c := by
  have H : HRS.MS.Wad.S85Hyp d a β (t + 1) M ρ := ⟨hd, ha, hβ, by linarith, hM.le, hρ⟩
  rw [HRS.MS.Wad.s85_Ulim_ext H ht (by linarith) (s82_const_classical a β ρ t c)
    (s82_const_memCM hM c) x]
  unfold HRS.MS.Wad.s85_V HRS.Whole.pair
  ring

theorem s82_classical_eq_Ulim (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) {M : ℝ} (hM : 0 < M) {v : ℝ} (hv : 0 ≤ v)
    {φ : Euc d → ℝ} (hφ : MemCM M φ) {w : ℝ → Euc d → ℝ}
    (hw : IsClassicalAdjointW (critCoeff d a β ρ) v φ w) {r : ℝ} (hr : r ∈ Set.Icc 0 v) :
    ∃ c : ℝ, ∀ x, w r x = HRS.MS.Wad.s85_Ulim a β ρ M (v - r) φ x + c := by
  have hs : 0 ≤ v - r := by linarith [hr.2]
  have hsol : IsAdjointSolutionG (generatorW (critCoeff d a β ρ)) (r + (v - r)) φ w := by
    have e : r + (v - r) = v := by ring
    rw [e]; exact HRS.MS.Wad.s85_cl_to_G hw
  have hshift := HRS.MS.Wad.s85_G_shift (G := generatorW (critCoeff d a β ρ))
    (fun r r' h x => HRS.MS.Wad.s85_gen_time a β ρ r r' h x) hr.1 hs hsol
  have hcl : IsClassicalAdjointW (critCoeff d a β ρ) (v - r) φ (fun s => w (s + r)) :=
    HRS.MS.Wad.s85_G_to_cl hshift
  have H : HRS.MS.Wad.S85Hyp d a β (v - r + 1) M ρ := ⟨hd, ha, hβ, by linarith, hM.le, hρ⟩
  refine ⟨∫ z, w (0 + r) z ∂(HRS.Whole.withDensityReal ρ) -
    HRS.Whole.pair (HRS.Whole.withDensityReal ρ) φ, fun x => ?_⟩
  have h := HRS.MS.Wad.s85_Ulim_ext H hs (by linarith) hcl hφ x
  rw [h]
  unfold HRS.MS.Wad.s85_V
  simp only [zero_add]
  ring

end HRS.MS.S82BD
