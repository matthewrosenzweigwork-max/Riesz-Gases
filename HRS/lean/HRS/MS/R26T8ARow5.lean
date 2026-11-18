import HRS.MS.R26T8ARow4
import HRS.MS.LcEngAux2
import HRS.MS.R26T8AP06

/-!
# S8.2 ROW LEMMA (shared with P08 and P17)
`r26t8a_row_lemma`: for `F` conormal of order `sigma < d` with weight `pairWeight M` and a smooth density `rho` with jets
`‖D^i rho(y)‖ <= K (1+|y|)^(-(M+d+1))` (`i <= k`), the row `x |-> ∫ rho(y) F(x,y) dy` is `C^k` and
`‖D^j row(x)‖ <= C A <x>^M` for `j <= k`, with `C` depending only on `d, k, b, M, sigma, K`.
(Derivatives fall on the centre variable via `y = x - u`; localisation by a bump in `x` makes `lc4_iteratedFDeriv_integral` applicable.)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_row_rowG (hd : 2 ≤ d) (ρ : Euc d → ℝ) (F : Euc d → Euc d → ℝ) (x : Euc d) :
    ∫ y, ρ y * F x y = ∫ u, r26t8a_row_Gd ρ F u x := by
  rw [← integral_sub_left_eq_self (fun y => ρ y * F x y) volume x]
  refine integral_congr_ae ?_
  filter_upwards [r26t8a_ae_ne_zero hd] with u hu
  simp [r26t8a_row_Gd, hu]

set_option maxHeartbeats 6400000 in
theorem r26t8a_row_lemma (hd : 2 ≤ d) (k b : ℕ) (M σ : ℝ) (hM : 0 ≤ M) (hσd : σ < d) (K : ℝ) (hK0 : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, ContDiff ℝ (k : WithTop ℕ∞) ρ →
      (∀ i ≤ k, ∀ y : Euc d, ‖iteratedFDeriv ℝ i ρ y‖ ≤ K * (1 + ‖y‖) ^ (-(M + (d : ℝ) + 1))) →
      ∀ (F : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal k b M σ A F →
      ContDiff ℝ (k : WithTop ℕ∞) (fun x => ∫ y, ρ y * F x y) ∧
      ∀ j ≤ k, ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fun x => ∫ y, ρ y * F x y) x‖ ≤ C * A * jbracket x ^ M := by
  obtain ⟨chi, hchi⟩ := r26t8a_p06_exists_cutoff d
  obtain ⟨B, hB0, hB⟩ := r26t8a_chi_jets hchi k
  obtain ⟨s, cE, Cint, hs0, hsd, hcE, hCint0, hmaj⟩ := r26t8a_row_maj hd b σ hσd
  refine ⟨2 ^ k * K * Cint, by positivity, ?_⟩
  intro ρ hρ hK F A hA hF
  set row : Euc d → ℝ := fun x => ∫ y, ρ y * F x y with hrow
  have hlocal : ∀ x0 : Euc d, ContDiffAt ℝ (k : WithTop ℕ∞) row x0 ∧
      ∀ j ≤ k, ‖iteratedFDeriv ℝ j row x0‖ ≤ 2 ^ k * K * Cint * A * jbracket x0 ^ M := by
    intro x0
    set θ : Euc d → ℝ := fun x => chi (x - x0) with hθ
    set Gt : Euc d → Euc d → ℝ := fun u x => θ x * r26t8a_row_Gd ρ F u x with hGt
    have hchik : ContDiff ℝ (k : WithTop ℕ∞) chi := contDiff_infty.1 hchi.1 k
    have hθc : ContDiff ℝ (k : WithTop ℕ∞) θ := hchik.comp (contDiff_id.sub contDiff_const)
    have hGdc := r26t8a_row_Gd_contDiff k hρ hF.1
    have hGtc : ∀ u, ContDiff ℝ (k : WithTop ℕ∞) (Gt u) := fun u => hθc.mul (hGdc u)
    set W : Euc d → ℝ := fun u => 2 * (1 + ‖x0 - u‖) ^ (-((d : ℝ) + 1)) +
      cE * (closedBall (0 : Euc d) 2).indicator (fun u => ‖u‖ ^ (-s)) u with hW
    obtain ⟨hWi, hWint, hWdom⟩ := hmaj x0
    have hW0 : ∀ u, 0 ≤ W u := fun u => by
      simp only [hW]
      have h1 : 0 ≤ (1 + ‖x0 - u‖) ^ (-((d : ℝ) + 1)) := Real.rpow_nonneg (by positivity) _
      have h2 : 0 ≤ (closedBall (0 : Euc d) 2).indicator (fun u => ‖u‖ ^ (-s)) u :=
        Set.indicator_nonneg (fun u _ => Real.rpow_nonneg (norm_nonneg u) _) u
      positivity
    set P : ℝ := 2 ^ k * K * 4 ^ M * jbracket x0 ^ M * A * 3 ^ ((d : ℝ) + 1) with hP
    have hP0 : 0 ≤ P := by rw [hP]; have := (s83_jb_pos x0).le; positivity
    -- pointwise bound of Gd near x0
    have hpt : ∀ u : Euc d, u ≠ 0 → ∀ x : Euc d, ‖x - x0‖ ≤ 2 → ∀ l ≤ k,
        ‖iteratedFDeriv ℝ l (r26t8a_row_Gd ρ F u) x‖ ≤ P * W u := by
      intro u hu x hx l hl
      have h1 := r26t8a_row_Gd_bound hM k b σ A K hA hρ hK hF hu x l hl
      have hjbx : jbracket x ^ M ≤ 4 ^ M * jbracket x0 ^ M := by
        have e : x = x0 + (x - x0) := by abel
        have hj : jbracket x ≤ 4 * jbracket x0 := by
          have := r26t8a_jb_shift' x0 (x - x0)
          rw [← e] at this
          nlinarith [s83_jb_pos x0]
        calc jbracket x ^ M ≤ (4 * jbracket x0) ^ M := Real.rpow_le_rpow (s83_jb_pos x).le hj hM
          _ = 4 ^ M * jbracket x0 ^ M := Real.mul_rpow (by norm_num) (s83_jb_pos x0).le
      have hrx : (1 + ‖x - u‖) ^ (-((d : ℝ) + 1)) ≤ 3 ^ ((d : ℝ) + 1) * (1 + ‖x0 - u‖) ^ (-((d : ℝ) + 1)) := by
        have h3 : 1 + ‖x0 - u‖ ≤ 3 * (1 + ‖x - u‖) := by
          have := norm_sub_le_norm_sub_add_norm_sub x0 x u
          rw [norm_sub_rev x0 x] at this
          linarith [norm_nonneg (x - u)]
        have hpos : 0 < 1 + ‖x - u‖ := by positivity
        calc (1 + ‖x - u‖) ^ (-((d : ℝ) + 1))
            = 3 ^ ((d : ℝ) + 1) * (3 * (1 + ‖x - u‖)) ^ (-((d : ℝ) + 1)) := by
              rw [Real.mul_rpow (by norm_num) hpos.le, ← mul_assoc, ← Real.rpow_add (by norm_num)]
              simp
          _ ≤ 3 ^ ((d : ℝ) + 1) * (1 + ‖x0 - u‖) ^ (-((d : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) h3 (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])) (by positivity)
      have h2l : (2 : ℝ) ^ l ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hl
      have hEnv : 0 ≤ 1 + (min 1 ‖u‖) ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖u‖)|) ^ b := by
        have : 0 ≤ (min 1 ‖u‖) ^ (-(σ + ((0 : ℕ) : ℝ))) := Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
        positivity
      have hdom := hWdom u (norm_pos_iff.2 hu)
      have hjb0 : 0 ≤ jbracket x ^ M := Real.rpow_nonneg (s83_jb_pos x).le _
      have hjb00 : 0 ≤ jbracket x0 ^ M := Real.rpow_nonneg (s83_jb_pos x0).le _
      set q1 : ℝ := (1 + ‖x - u‖) ^ (-((d : ℝ) + 1)) with hq1
      set q0 : ℝ := (1 + ‖x0 - u‖) ^ (-((d : ℝ) + 1)) with hq0
      set En : ℝ := 1 + (min 1 ‖u‖) ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖u‖)|) ^ b with hEn
      have hq1' : q1 * En ≤ 3 ^ ((d : ℝ) + 1) * W u := by
        calc q1 * En ≤ (3 ^ ((d : ℝ) + 1) * q0) * En := mul_le_mul_of_nonneg_right hrx hEnv
          _ = 3 ^ ((d : ℝ) + 1) * (q0 * En) := by ring
          _ ≤ 3 ^ ((d : ℝ) + 1) * W u := mul_le_mul_of_nonneg_left hdom (by positivity)
      calc ‖iteratedFDeriv ℝ l (r26t8a_row_Gd ρ F u) x‖
          ≤ 2 ^ l * K * jbracket x ^ M * (A * (q1 * En)) := h1
        _ ≤ 2 ^ k * K * (4 ^ M * jbracket x0 ^ M) * (A * (3 ^ ((d : ℝ) + 1) * W u)) := by
            refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right h2l hK0) hjbx hjb0 (by positivity))
              (mul_le_mul_of_nonneg_left hq1' hA) (by positivity) (by positivity)
        _ = P * W u := by rw [hP]; ring
    set CΦ : ℝ := 2 ^ k * B * P with hCΦ
    have hΦint : Integrable (fun u => CΦ * W u) := hWi.const_mul _
    have hbd : ∀ i ≤ k, ∀ u x, ‖iteratedFDeriv ℝ i (Gt u) x‖ ≤ CΦ * W u := by
      intro i hi u x
      have hCΦ0 : 0 ≤ CΦ * W u := by rw [hCΦ]; have := hW0 u; positivity
      by_cases hu : u = 0
      · have : Gt u = fun _ => 0 := by funext x'; simp [hGt, r26t8a_row_Gd, hu]
        rw [this]; simpa using hCΦ0
      · by_cases hx : 2 < ‖x - x0‖
        · have hev : Gt u =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
            filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).mem_nhds hx]
              with y hy
            simp [hGt, hθ, hchi.2.2.2.2 (y - x0) (le_of_lt hy)]
          rw [(hev.iteratedFDeriv ℝ i).self_of_nhds]
          simpa using hCΦ0
        · push Not at hx
          have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hθc (hGdc u) x (n := i) (by exact_mod_cast hi)
          refine hmul.trans ?_
          calc ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l θ x‖ *
                ‖iteratedFDeriv ℝ (i - l) (r26t8a_row_Gd ρ F u) x‖
              ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * B * (P * W u) := by
                refine Finset.sum_le_sum fun l hl' => ?_
                have hl2 : l ≤ i := by have := Finset.mem_range.1 hl'; omega
                have h1 : ‖iteratedFDeriv ℝ l θ x‖ ≤ B := by
                  simp only [hθ]
                  rw [iteratedFDeriv_comp_sub (f := chi) l x0 x]
                  exact hB l (by omega) _
                have h2 := hpt u hu x hx (i - l) (by omega)
                exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
                  (mul_nonneg (Nat.cast_nonneg _) hB0)
            _ = 2 ^ i * (B * (P * W u)) := by
                simp_rw [mul_assoc]
                rw [← Finset.sum_mul, show ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) = 2 ^ i by exact_mod_cast Nat.sum_range_choose i]
            _ ≤ CΦ * W u := by
                have h2i : (2 : ℝ) ^ i ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hi
                have : 0 ≤ B * (P * W u) := by have := hW0 u; positivity
                rw [hCΦ]; nlinarith
    -- measurability of the slice jets
    have hmeas : ∀ i ≤ k, ∀ x, AEStronglyMeasurable (fun u => iteratedFDeriv ℝ i (Gt u) x) volume := by
      intro i hi x
      set ψ : ℕ → Euc d → ℝ := fun n u => r26t8a_psiCut chi (1 / ((n : ℝ) + 1)) u with hψ
      set Ψ : ℕ → Euc d × Euc d → ℝ := fun n p => θ p.1 * ρ (p.1 - p.2) *
        (ψ n p.2 * midPair F (p.1 - (1 / 2 : ℝ) • p.2) p.2) with hΨ
      have hΨc : ∀ n, ContDiff ℝ (i : WithTop ℕ∞) (Ψ n) := by
        intro n
        have hR : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        have hg := (r26t8a_gtilde_contDiff hchi hR hF.1).of_le (by exact_mod_cast hi : (i : WithTop ℕ∞) ≤ (k : WithTop ℕ∞))
        have hl : ContDiff ℝ (i : WithTop ℕ∞) (fun p : Euc d × Euc d => (p.1 - (1 / 2 : ℝ) • p.2, p.2)) :=
          (contDiff_fst.sub (contDiff_snd.const_smul _)).prodMk contDiff_snd
        have h3 := hg.comp hl
        have h1 : ContDiff ℝ (i : WithTop ℕ∞) (fun p : Euc d × Euc d => θ p.1) :=
          (hθc.of_le (by exact_mod_cast hi : (i : WithTop ℕ∞) ≤ (k : WithTop ℕ∞))).comp contDiff_fst
        have h2 : ContDiff ℝ (i : WithTop ℕ∞) (fun p : Euc d × Euc d => ρ (p.1 - p.2)) :=
          (hρ.of_le (by exact_mod_cast hi : (i : WithTop ℕ∞) ≤ (k : WithTop ℕ∞))).comp (contDiff_fst.sub contDiff_snd)
        exact (h1.mul h2).mul h3
      refine r26t8a_row_slice_meas hd i Gt Ψ hΨc (fun u hu => ?_) x
      have hun : 0 < ‖u‖ := norm_pos_iff.2 hu
      have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) / 4 ≤ ‖u‖ := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ‖u‖))
        filter_upwards [this] with n hn
        linarith [(by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))]
      filter_upwards [hev] with n hn x'
      have hR : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simp only [hΨ, hψ, hGt, r26t8a_row_Gd, if_neg hu, r26t8a_psiCut_one hchi hR hn, one_mul]
      unfold midPair
      have h1 : x' - (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • u = x' := by module
      have h2 : x' - (1 / 2 : ℝ) • u - (1 / 2 : ℝ) • u = x' - u := by module
      rw [h1, h2]; ring
    obtain ⟨hcd, hjets⟩ := HRS.MS.Lc.lc4_iteratedFDeriv_integral (μ := (volume : Measure (Euc d))) Gt k hGtc hΦint hbd hmeas
    -- local identification
    have hnb : IsOpen {x : Euc d | ‖x - x0‖ < 1} := isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
    have hGt1 : ∀ x : Euc d, ‖x - x0‖ < 1 → ∀ u, Gt u x = r26t8a_row_Gd ρ F u x := fun x hx u => by
      simp [hGt, hθ, hchi.2.2.2.1 (x - x0) hx.le]
    have hloc : row =ᶠ[𝓝 x0] fun x => ∫ u, Gt u x := by
      filter_upwards [hnb.mem_nhds (show ‖x0 - x0‖ < 1 by simp)] with x hx
      simp only [hrow]
      rw [r26t8a_row_rowG hd]
      exact integral_congr_ae (Eventually.of_forall fun u => (hGt1 x hx u).symm)
    refine ⟨hcd.contDiffAt.congr_of_eventuallyEq hloc, fun j hj => ?_⟩
    have hGtd : ∀ u, Gt u =ᶠ[𝓝 x0] r26t8a_row_Gd ρ F u := fun u => by
      filter_upwards [hnb.mem_nhds (show ‖x0 - x0‖ < 1 by simp)] with x hx using hGt1 x hx u
    have e1 : iteratedFDeriv ℝ j row x0 = ∫ u, iteratedFDeriv ℝ j (r26t8a_row_Gd ρ F u) x0 := by
      rw [(hloc.iteratedFDeriv ℝ j).self_of_nhds, hjets j hj x0]
      exact integral_congr_ae (Eventually.of_forall fun u => ((hGtd u).iteratedFDeriv ℝ j).self_of_nhds)
    rw [e1]
    have hgi : Integrable (fun u => 2 ^ k * K * jbracket x0 ^ M * A * W u) := hWi.const_mul _
    refine (norm_integral_le_of_norm_le hgi ?_).trans ?_
    · filter_upwards [r26t8a_ae_ne_zero hd] with u hu
      have h1 := r26t8a_row_Gd_bound hM k b σ A K hA hρ hK hF hu x0 j hj
      have hdom := hWdom u (norm_pos_iff.2 hu)
      have h2j : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
      have hjb0 : 0 ≤ jbracket x0 ^ M := Real.rpow_nonneg (s83_jb_pos x0).le _
      refine h1.trans ?_
      calc 2 ^ j * K * jbracket x0 ^ M * (A * ((1 + ‖x0 - u‖) ^ (-((d : ℝ) + 1)) *
            (1 + (min 1 ‖u‖) ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖u‖)|) ^ b)))
          ≤ 2 ^ k * K * jbracket x0 ^ M * (A * W u) :=
            mul_le_mul (mul_le_mul_of_nonneg_right h2j hK0 |> fun h => mul_le_mul h le_rfl hjb0 (by positivity))
              (mul_le_mul_of_nonneg_left hdom hA) (by positivity) (by positivity)
        _ = 2 ^ k * K * jbracket x0 ^ M * A * W u := by ring
    · have hjb0 : 0 ≤ jbracket x0 ^ M := Real.rpow_nonneg (s83_jb_pos x0).le _
      rw [integral_const_mul]
      have hc : 0 ≤ 2 ^ k * K * jbracket x0 ^ M * A := by positivity
      calc 2 ^ k * K * jbracket x0 ^ M * A * ∫ u, W u ≤ 2 ^ k * K * jbracket x0 ^ M * A * Cint :=
            mul_le_mul_of_nonneg_left hWint hc
        _ = 2 ^ k * K * Cint * A * jbracket x0 ^ M := by ring
  exact ⟨contDiff_iff_contDiffAt.2 fun x0 => (hlocal x0).1, fun j hj x => (hlocal x).2 j hj⟩

end HRS.MS.R26T8A
