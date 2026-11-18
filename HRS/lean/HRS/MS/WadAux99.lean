import HRS.MS.WadAux98

/-!
# S8.3, packet S8E-6, part 3: higher-order enabling lemmas

`s8e_shift_sol_gen`: the flow-shifted difference of an `S8eSol` (for an arbitrary jointly continuous source `q` of polynomial
growth) is an `S8eSol` with source `q_s(· + z_s) - q_s` (iteration of this step gives the higher differences of a mild
solution).  `s8e_Bop_diff`: the bilinear difference identity
`𝓑_{σ'} h' - 𝓑_σ h = 𝓑_{σ'}(h' - h) + 𝓑_{σ' - σ} h` for densities with Gaussian bounds and `h, h' ∈ C²_b`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_shift_mild_gen {q : ℝ → Euc d → ℝ} {a ν t M Φ : ℝ} {w : ℝ → Euc d → ℝ} (ha : 0 < a) (hν : 0 < ν)
    (hM : 0 ≤ M) (sol : S8eSol q a ν t M Φ w) {ζ : Euc d} (hζ : ‖ζ‖ < 1 / 4) {r : ℝ}
    (hr : r ∈ Set.Icc 0 t) (x : Euc d) :
    s8e_u a ζ w r x = s83_P a ν (t - r) (s8e_u a ζ w t) x +
      ∫ s in r..t, s83_P a ν (s - r) (fun y => q s (y + s8e_zs a ζ s) - q s y) x := by
  have hzs : ∀ s, 0 ≤ s → ‖s8e_zs a ζ s‖ < 1 / 4 := fun s hs =>
    lt_of_le_of_lt (s8e_zs_norm ha.le hs ζ) hζ
  have hr0 := hr.1
  have hrt := hr.2
  obtain ⟨Kq, pq, hKq⟩ := sol.hqb
  have hKq0 : 0 ≤ Kq := by
    have := (abs_nonneg (q 0 0)).trans (hKq 0 ⟨le_rfl, hr0.trans hrt⟩ 0)
    simpa using this
  have hqmem : ∀ s ∈ Set.Icc 0 t, s ∈ Set.Icc 0 t := fun s hs => hs
  -- the two shifted pieces
  have hP1 : s83_P a ν (t - r) (w t) (x + s8e_zs a ζ r) =
      s83_P a ν (t - r) (fun y => w t (y + s8e_zs a ζ t)) x := by
    rw [s8e_P_shift]; simp only [s8e_zs_flow]
  have hP2 : ∀ s : ℝ, s83_P a ν (s - r) (q s) (x + s8e_zs a ζ r) =
      s83_P a ν (s - r) (fun y => q s (y + s8e_zs a ζ s)) x := fun s => by
    rw [s8e_P_shift]; simp only [s8e_zs_flow]
  have hint2 := s8e_hint ha hν sol hr x
  have hint1 : IntervalIntegrable (fun s => s83_P a ν (s - r)
      (fun y => q s (y + s8e_zs a ζ s)) x) volume r t := by
    refine (s8e_hint ha hν sol hr (x + s8e_zs a ζ r)).congr ?_
    exact fun s _ => hP2 s
  -- additivity of `P` inside the integral
  have hsub : ∀ s ∈ Set.Icc r t, s83_P a ν (s - r) (fun y => q s (y + s8e_zs a ζ s) -
      q s y) x = s83_P a ν (s - r) (fun y => q s (y + s8e_zs a ζ s)) x -
      s83_P a ν (s - r) (q s) x := fun s hs => by
    have hs' : s ∈ Set.Icc 0 t := ⟨hr0.trans hs.1, hs.2⟩
    have hc := s8e_qcont sol hs'
    have hw0 : Wt (pq : ℝ) (Kq * 2 ^ pq) (q s) := s8e_wt_poly hKq0 (hKq s hs')
    have hw1 := s8e_wt_shift (Nat.cast_nonneg pq) hw0 (hzs s (hr0.trans hs.1))
    exact s8e_P_sub (hc.comp (continuous_id.add continuous_const)) hc (Nat.cast_nonneg pq) hw1 hw0 ha hν.le
      (by linarith [hs.1]) x
  have hdt : s83_P a ν (t - r) (s8e_u a ζ w t) x = s83_P a ν (t - r) (fun y => w t (y + s8e_zs a ζ t)) x -
      s83_P a ν (t - r) (w t) x := by
    have hwt := sol.term_wt
    have hw1 := s8e_wt_shift hM hwt (hzs t (hr0.trans hrt))
    exact s8e_P_sub (sol.term_cont.comp (continuous_id.add continuous_const)) sol.term_cont hM hw1 hwt ha hν.le
      (by linarith) x
  rw [hdt, intervalIntegral.integral_congr (g := fun s => s83_P a ν (s - r) (fun y => q s
    (y + s8e_zs a ζ s)) x - s83_P a ν (s - r) (q s) x)
    (fun s hs => hsub s (by rwa [Set.uIcc_of_le hrt] at hs)), intervalIntegral.integral_sub hint1 hint2]
  unfold s8e_u
  rw [sol.mild r hr (x + s8e_zs a ζ r), sol.mild r hr x, hP1]
  rw [intervalIntegral.integral_congr (g := fun s => s83_P a ν (s - r) (fun y => q s
    (y + s8e_zs a ζ s)) x) (fun s _ => hP2 s)]
  ring


theorem s8e_shift_sol_gen {q : ℝ → Euc d → ℝ} {a ν t M Φ Φu : ℝ} {w : ℝ → Euc d → ℝ} (ha : 0 < a) (hν : 0 < ν)
    (hM : 0 ≤ M) (ht : 0 < t) (sol : S8eSol q a ν t M Φ w) {ζ : Euc d} (hζ : ‖ζ‖ < 1 / 4)
    (hΦu : Wt M Φu (s8e_u a ζ w t)) :
    S8eSol (fun s y => q s (y + s8e_zs a ζ s) - q s y) a ν t M Φu (s8e_u a ζ w) := by
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
      have := (abs_nonneg (q 0 0)).trans (hK 0 h0I 0)
      simpa using this
    refine ⟨K * (2 ^ p + 1), p, fun s hs y => ?_⟩
    have hz1 : ‖s8e_zs a ζ s‖ ≤ 1 := ((s8e_zs_norm ha.le hs.1 ζ).trans hζ.le).trans (by norm_num)
    have h1 : 1 + ‖y + s8e_zs a ζ s‖ ≤ 2 * (1 + ‖y‖) := by
      have := norm_add_le y (s8e_zs a ζ s)
      linarith [norm_nonneg y]
    have h2 : |q s (y + s8e_zs a ζ s)| ≤ K * (2 ^ p * (1 + ‖y‖) ^ p) := by
      refine (hK s hs _).trans ?_
      calc K * (1 + ‖y + s8e_zs a ζ s‖) ^ p ≤ K * (2 * (1 + ‖y‖)) ^ p :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 p) hK0
        _ = _ := by rw [mul_pow]
    have h3 := hK s hs y
    have h4 : 0 ≤ (1 + ‖y‖) ^ p := by positivity
    calc |q s (y + s8e_zs a ζ s) - q s y|
        ≤ |q s (y + s8e_zs a ζ s)| + |q s y| := abs_sub _ _
      _ ≤ K * (2 ^ p * (1 + ‖y‖) ^ p) + K * (1 + ‖y‖) ^ p := add_le_add h2 h3
      _ = K * (2 ^ p + 1) * (1 + ‖y‖) ^ p := by ring
  · intro r hr x
    exact s8e_shift_mild_gen ha hν hM sol hζ hr x
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


theorem s8e_Bop_diff (hd : 2 ≤ d) {σ σ' : Euc d → ℝ} (g : s84_GaussReg σ) (g' : s84_GaussReg σ')
    {h h' : Euc d → ℝ} {B B' : ℝ} (hh : s84_C2b h B) (hh' : s84_C2b h' B') (x : Euc d) :
    s84_Bop σ' h' x - s84_Bop σ h x =
      s84_Bop σ' (fun y => h' y - h y) x + s84_Bop (fun y => σ' y - σ y) h x := by
  have e1 := s84_Bop_sub hd g' hh' hh x
  have e2 := s8e_Bop_rho_sub hd g' g hh x
  linarith

end HRS.MS.Wad
