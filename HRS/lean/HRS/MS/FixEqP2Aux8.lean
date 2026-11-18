import HRS.MS.FixEqP2Aux7

/-!
# S5.7 `fixed_equation` (worker S57P), part 11: the difference of two orbits from the Duhamel formula (P1, abstract part)

`s57p_diff_of_orb`: `f` classical for `C` and `f_N` classical for `C_N` with the same datum `ψ` on `[0,t]`, both bounded in `C^4`;
if the source `g_u = (𝓛_u - 𝓛^N_u) f_u` has `C_N`-orbits that are classical and bounded in `C^{n+1}` by `B_orb` (`S57pOrbFam`),
then `‖D^i (f_r - f^N_r)‖_∞ ≤ t B_orb` for `i ≤ n`.  (`h = f - f_N` satisfies `-∂_r h = 𝓛^N_r h + g_r`, `h_t = 0`; apply
`s57p_duhamel`.)
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

/-- the generator of any coefficient along a classical family is jointly continuous -/
theorem s57p_gen_family_cont {C C' : WholeCoeff d} {t : ℝ} (ht : 0 ≤ t) (G' : S57pGen C' t)
    {ψ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t ψ f) {Bf : ℝ}
    (hf4 : ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 4 (f r) ∧ ∀ i ≤ 4, ∀ x, ‖iteratedFDeriv ℝ i (f r) x‖ ≤ Bf) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => generatorW C' p.1 (f p.1) p.2 := by
  obtain ⟨K, hK0, hgen⟩ := G'.bound
  obtain ⟨Bt, hBt⟩ := hf.bdd_time_deriv
  have hBf0 : 0 ≤ Bf := le_trans (norm_nonneg _) ((hf4 0 ⟨le_rfl, ht⟩).2 0 (by norm_num) 0)
  set BL : ℝ := max Bt 0 with hBL
  have hBL0 : 0 ≤ BL := le_max_right _ _
  set fc : ℝ → Euc d → ℝ := fun r => f (max 0 (min r t)) with hfc
  have hcl : ∀ r, max 0 (min r t) ∈ Set.Icc (0 : ℝ) t := fun r => ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩
  have hG : ∀ r', ContDiff ℝ 4 (fc r') ∧ ∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (fc r') x‖ ≤ Bf := fun r' =>
    ⟨(hf4 _ (hcl r')).1, fun j hj x => (hf4 _ (hcl r')).2 j hj x⟩
  have hgr : ∀ r r' x, |fc r x - fc r' x| ≤ BL * (1 + ‖x‖) * |r - r'| := by
    intro r r' x
    have h1 := s55m_lip_r_abs hf (BL := BL) (fun τ hτ y => (hBt τ hτ y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) hBL0 (hcl r) (hcl r') x
    refine h1.trans (mul_le_mul_of_nonneg_left (s55m_clip_abs t r r') (by positivity))
  have key := s57p_cont_gen G' hBf0 hK0 (fun τ hτ u hu hub => hgen τ hτ Bf u hBf0 hu hub) hG hgr
  refine key.congr fun p => ?_
  have : max 0 (min (p.1 : ℝ) t) = p.1 := by rw [min_eq_left p.1.2.2, max_eq_right p.1.2.1]
  simp [hfc, this]

theorem s57p_diff_of_orb {C CN : WholeCoeff d} {t : ℝ} (ht : 0 ≤ t) (GN : S57pGen CN t) (LinN : S57pLin CN t)
    (huniqN : HRS.MS.S52B.S52bUniq CN t) {ψ : Euc d → ℝ} {f fN : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t ψ f) (hfN : IsClassicalAdjointW CN t ψ fN) {Bf BfN : ℝ}
    (hf4 : ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 4 (f r) ∧ ∀ i ≤ 4, ∀ x, ‖iteratedFDeriv ℝ i (f r) x‖ ≤ Bf)
    (hfN4 : ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 4 (fN r) ∧ ∀ i ≤ 4, ∀ x, ‖iteratedFDeriv ℝ i (fN r) x‖ ≤ BfN)
    {n : ℕ} (hn4 : 4 ≤ n) {Borb : ℝ} (hB0 : 0 ≤ Borb)
    (hOrb : S57pOrbFam CN t n Borb (fun u x => generatorW C u (f u) x - generatorW CN u (f u) x)) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ i ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ i (fun y => f r y - fN r y) x‖ ≤ t * Borb := by
  obtain ⟨K, hK0, hgen⟩ := GN.bound
  have hBf0 : 0 ≤ Bf := le_trans (norm_nonneg _) ((hf4 0 ⟨le_rfl, ht⟩).2 0 (by norm_num) 0)
  have hBfN0 : 0 ≤ BfN := le_trans (norm_nonneg _) ((hfN4 0 ⟨le_rfl, ht⟩).2 0 (by norm_num) 0)
  have hjsub : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ i ≤ 3, ∀ x,
      iteratedFDeriv ℝ i (fun y => f r y - fN r y) x = iteratedFDeriv ℝ i (f r) x - iteratedFDeriv ℝ i (fN r) x :=
    fun r hr i hi x => iteratedFDeriv_sub_apply (((hf4 r hr).1.of_le (by exact_mod_cast (by omega : i ≤ 4))).contDiffAt)
      (((hfN4 r hr).1.of_le (by exact_mod_cast (by omega : i ≤ 4))).contDiffAt)
  have hsubN : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, generatorW CN r (fun y => f r y - fN r y) x =
      generatorW CN r (f r) x - generatorW CN r (fN r) x := fun r hr x =>
    LinN.sub r hr (max Bf BfN) (f r) (fN r) ((hf4 r hr).1.of_le (by norm_num)) ((hfN4 r hr).1.of_le (by norm_num))
      (fun i hi y => ((hf4 r hr).2 i (by omega) y).trans (le_max_left _ _))
      (fun i hi y => ((hfN4 r hr).2 i (by omega) y).trans (le_max_right _ _)) x
  have hfcont := s57p_gen_family_cont ht GN hf hf4
  have key := s57p_duhamel GN LinN huniqN hn4 hB0 hOrb ht (h := fun r x => f r x - fN r x) (Bh := Bf + BfN)
    (fun r hr => ⟨((hf4 r hr).1.of_le (by norm_num)).sub ((hfN4 r hr).1.of_le (by norm_num)), fun i hi x => by
      rw [hjsub r hr i hi x]
      exact (norm_sub_le _ _).trans (add_le_add ((hf4 r hr).2 i (by omega) x) ((hfN4 r hr).2 i (by omega) x))⟩)
    (fun i hi => by
      have e : (fun p : Set.Icc (0 : ℝ) t × Euc d => iteratedFDeriv ℝ i (fun y => f p.1 y - fN p.1 y) p.2) =
          fun p => iteratedFDeriv ℝ i (f p.1) p.2 - iteratedFDeriv ℝ i (fN p.1) p.2 := by
        funext p; exact hjsub p.1 p.1.2 i (by omega) p.2
      rw [e]
      exact (hf.cont_c2 i hi).sub (hfN.cont_c2 i hi))
    (by funext x; simp [hf.terminal, hfN.terminal])
    (fun x r hr => by
      have hrI : r ∈ Set.Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le⟩
      have := (hf.time_deriv x r hr).sub (hfN.time_deriv x r hr)
      refine this.congr_deriv ?_
      simp only [hsubN r hrI x]
      ring)
    (by
      have e : (fun p : Set.Icc (0 : ℝ) t × Euc d => generatorW CN p.1 (fun y => f p.1 y - fN p.1 y) p.2) =
          fun p => generatorW CN p.1 (f p.1) p.2 - generatorW CN p.1 (fN p.1) p.2 := by
        funext p; exact hsubN p.1 p.1.2 p.2
      rw [e]
      exact hfcont.sub hfN.cont_time_deriv)
    (by
      refine ⟨Bf * K + BfN * K, fun r hr x => ?_⟩
      rw [hsubN r hr x]
      have h1 := (hgen r hr Bf (f r) hBf0 (hf4 r hr).1 (fun j hj y => (hf4 r hr).2 j hj y)).2 0 (by norm_num) x
      have h2 := (hgen r hr BfN (fN r) hBfN0 (hfN4 r hr).1 (fun j hj y => (hfN4 r hr).2 j hj y)).2 0 (by norm_num) x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1 h2
      calc |generatorW CN r (f r) x - generatorW CN r (fN r) x|
          ≤ |generatorW CN r (f r) x| + |generatorW CN r (fN r) x| := abs_sub _ _
        _ ≤ Bf * K * (1 + ‖x‖) + BfN * K * (1 + ‖x‖) := add_le_add h1 h2
        _ = (Bf * K + BfN * K) * (1 + ‖x‖) := by ring)
  intro r hr i hi x
  rw [key r hr i hi x]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Borb) (fun u hu => ?_)).trans ?_
  · rw [Set.uIoc_of_le hr.2] at hu
    exact (hOrb.bound u ⟨hr.1.trans hu.1.le, hu.2⟩ r ⟨hr.1, hu.1.le⟩).2 i (by omega) x
  · have : |t - r| ≤ t := by rw [abs_of_nonneg (sub_nonneg.2 hr.2)]; linarith [hr.1]
    have := mul_le_mul_of_nonneg_left this hB0
    linarith [mul_comm Borb t]

end HRS.MS.FixEq
