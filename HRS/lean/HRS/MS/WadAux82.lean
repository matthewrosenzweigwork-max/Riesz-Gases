import HRS.MS.WadAux81

/-!
# S8.3, packet S8E-3, part 3: the flow-shifted difference is an `S8eSol`; decomposition of its source

`s8e_shift_sol`: `u_s(y) = w_s(y + z_s) - w_s(y)` is an `S8eSol` with source `qu_s(y) = 𝓑 w_s (y + z_s) - 𝓑 w_s (y)`.
`s8e_qu_decomp`: `qu_s = 𝓑_ρ u_s + 𝓑_{ρ(·+z) - ρ} (w_s(·+z))` (translation covariance of `𝓑` and bilinearity).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_C2b_shift {h : Euc d → ℝ} {B : ℝ} (hh : s84_C2b h B) (z : Euc d) :
    s84_C2b (fun y => h (y + z)) B := by
  refine ⟨hh.1.comp (contDiff_id.add contDiff_const), fun y => ?_⟩
  have e1 : fderiv ℝ (fun y => h (y + z)) = fun y => fderiv ℝ h (y + z) := by
    funext y; rw [fderiv_comp_add_right]
  have e2 : fderiv ℝ (fderiv ℝ (fun y => h (y + z))) y = fderiv ℝ (fderiv ℝ h) (y + z) := by
    rw [e1, fderiv_comp_add_right (f := fderiv ℝ h)]
  exact ⟨by rw [e1]; exact (hh.2 (y + z)).1, by rw [e2]; exact (hh.2 (y + z)).2⟩

theorem s8e_qu_decomp (hd : 2 ≤ d) {ρ : Euc d → ℝ} (hg : s84_GaussReg ρ) {h : Euc d → ℝ} {B : ℝ}
    (hh : s84_C2b h B) {z : Euc d} (hz : ‖z‖ ≤ 1) (y : Euc d) :
    s84_Bop ρ h (y + z) - s84_Bop ρ h y =
      s84_Bop ρ (fun y => h (y + z) - h y) y +
        s84_Bop (fun y => ρ (y + z) - ρ y) (fun y => h (y + z)) y := by
  have hs := s8e_gaussReg_shift hg hz
  have hh' := s8e_C2b_shift hh z
  have e1 := s8e_Bop_shift ρ h z y
  have e2 := s8e_Bop_rho_sub hd hs hg hh' y
  have e3 := s84_Bop_sub hd hg hh' hh y
  rw [← e1]
  linarith

theorem s8e_fderiv_shift_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Euc d → E}
    (hF : Differentiable ℝ F) (Δ y : Euc d) :
    fderiv ℝ (fun y => F (y + Δ) - F y) y = fderiv ℝ F (y + Δ) - fderiv ℝ F y := by
  have h1 : DifferentiableAt ℝ (fun y => F (y + Δ)) y := (hF (y + Δ)).comp y (differentiableAt_id.add_const Δ)
  have e : (fun y => F (y + Δ) - F y) = (fun y => F (y + Δ)) - F := rfl
  rw [e, fderiv_sub h1 (hF y), fderiv_comp_add_right]

theorem s8e_shift_sol {ρ : Euc d → ℝ} {a ν t M Φ Φu : ℝ} {w : ℝ → Euc d → ℝ} (ha : 0 < a) (hν : 0 < ν)
    (hM : 0 ≤ M) (ht : 0 < t) (sol : S84Sol ρ a ν t M Φ w) {ζ : Euc d} (hζ : ‖ζ‖ < 1 / 4)
    (hΦu : Wt M Φu (s8e_u a ζ w t)) :
    S8eSol (fun s y => s84_Bop ρ (w s) (y + s8e_zs a ζ s) - s84_Bop ρ (w s) y) a ν t M Φu (s8e_u a ζ w) := by
  have hzs : ∀ s, 0 ≤ s → ‖s8e_zs a ζ s‖ < 1 / 4 := fun s hs =>
    lt_of_le_of_lt (s8e_zs_norm ha.le hs ζ) hζ
  have hcz : ∀ s : ℝ, Continuous fun y : Euc d => y + s8e_zs a ζ s := fun s =>
    continuous_id.add continuous_const
  have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht.le⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hΦu, ?_⟩
  · intro r hr
    exact ((sol.c2 r hr).comp (contDiff_id.add contDiff_const)).sub (sol.c2 r hr)
  · have hmaps : Set.MapsTo (fun p : ℝ × Euc d => (p.1, p.2 + s8e_zs a ζ p.1))
        (Set.Icc 0 t ×ˢ Set.univ) (Set.Icc 0 t ×ˢ Set.univ) := fun p hp => ⟨hp.1, Set.mem_univ _⟩
    have hcont : Continuous fun p : ℝ × Euc d => (p.1, p.2 + s8e_zs a ζ p.1) := by
      refine continuous_fst.prodMk (continuous_snd.add ?_)
      unfold s8e_zs
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).smul continuous_const
    exact (sol.hqc.comp hcont.continuousOn hmaps).sub sol.hqc
  · obtain ⟨K, p, hK⟩ := sol.hqb
    have hK0 : 0 ≤ K := by
      have := (abs_nonneg (s84_Bop ρ (w 0) 0)).trans (hK 0 h0I 0)
      simpa using this
    refine ⟨K * (2 ^ p + 1), p, fun s hs y => ?_⟩
    have hz1 : ‖s8e_zs a ζ s‖ ≤ 1 := ((s8e_zs_norm ha.le hs.1 ζ).trans hζ.le).trans (by norm_num)
    have h1 : 1 + ‖y + s8e_zs a ζ s‖ ≤ 2 * (1 + ‖y‖) := by
      have := norm_add_le y (s8e_zs a ζ s)
      linarith [norm_nonneg y]
    have h2 : |s84_Bop ρ (w s) (y + s8e_zs a ζ s)| ≤ K * (2 ^ p * (1 + ‖y‖) ^ p) := by
      refine (hK s hs _).trans ?_
      calc K * (1 + ‖y + s8e_zs a ζ s‖) ^ p ≤ K * (2 * (1 + ‖y‖)) ^ p :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 p) hK0
        _ = _ := by rw [mul_pow]
    have h3 := hK s hs y
    have h4 : 0 ≤ (1 + ‖y‖) ^ p := by positivity
    calc |s84_Bop ρ (w s) (y + s8e_zs a ζ s) - s84_Bop ρ (w s) y|
        ≤ |s84_Bop ρ (w s) (y + s8e_zs a ζ s)| + |s84_Bop ρ (w s) y| := abs_sub _ _
      _ ≤ K * (2 ^ p * (1 + ‖y‖) ^ p) + K * (1 + ‖y‖) ^ p := add_le_add h2 h3
      _ = K * (2 ^ p + 1) * (1 + ‖y‖) ^ p := by ring
  · intro r hr x
    exact s8e_shift_mild ha hν hM sol hζ hr x
  · exact (sol.term_cont.comp (hcz t)).sub sol.term_cont
  · obtain ⟨B1, B2, hB⟩ := sol.bdd
    refine ⟨B1 + B1, B2 + B2, fun r hr y => ?_⟩
    have hd1 : Differentiable ℝ (w r) := (sol.c2 r hr).differentiable (by norm_num)
    have hd2 : Differentiable ℝ (fderiv ℝ (w r)) :=
      ((sol.c2 r hr).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    have e1 : fderiv ℝ (s8e_u a ζ w r) = fun y => fderiv ℝ (w r) (y + s8e_zs a ζ r) - fderiv ℝ (w r) y := by
      funext y; exact s8e_fderiv_shift_sub hd1 _ y
    refine ⟨?_, ?_⟩
    · rw [e1]
      exact (norm_sub_le _ _).trans (add_le_add (hB r hr (y + s8e_zs a ζ r)).1 (hB r hr y).1)
    · rw [e1, s8e_fderiv_shift_sub hd2]
      have h1 := (hB r hr (y + s8e_zs a ζ r)).2
      have h2 := (hB r hr y).2
      calc _ ≤ ‖fderiv ℝ (fderiv ℝ (w r)) (y + s8e_zs a ζ r)‖ + ‖fderiv ℝ (fderiv ℝ (w r)) y‖ :=
            norm_sub_le (fderiv ℝ (fderiv ℝ (w r)) (y + s8e_zs a ζ r)) (fderiv ℝ (fderiv ℝ (w r)) y)
        _ ≤ B2 + B2 := add_le_add h1 h2

end HRS.MS.Wad
