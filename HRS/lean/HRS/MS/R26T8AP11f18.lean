import HRS.MS.R26T8AP11f17

/-!
# S8.2 T8A P11f (part 18): centre jets of `y ↦ Stil ρ Q (y+v) y` are `|v|^(-s)`-bounded
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_f18_env_pole (b : ℕ) {e0 s : ℝ} (he : e0 < s) (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      1 + r ^ (-e0) * (1 + |Real.log r|) ^ b ≤ C * r ^ (-s) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_p10a_env b he hs
  refine ⟨2 * C, by positivity, fun r hr hr1 => ?_⟩
  have h1 := hC r hr
  rw [min_eq_right hr1] at h1
  have h2 : 1 ≤ r ^ (-s) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
  nlinarith

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem r26t8a_f18_Sg_jets {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (hd : 2 ≤ d) (k b : ℕ) (M σ' c : ℝ)
    (hM : 0 ≤ M) (hc : 0 < c) (hσ : σ' + 2 < d) :
    ∃ s : ℝ, ∃ B1 : ℝ, 0 < s ∧ s < d ∧ 0 ≤ B1 ∧ ∀ (A : ℝ), 0 ≤ A → ∀ {Q : Euc d → Euc d → ℝ},
      Conormal (k + 2) b M σ' A Q → ∀ {ρ : Euc d → ℝ}, ContDiff ℝ ∞ ρ → ∀ {Cρ : ℝ}, 0 ≤ Cρ →
      (∀ j ≤ k + 1, ∀ u : Euc d, ‖iteratedFDeriv ℝ j ρ u‖ ≤ Cρ * Real.exp (-c * ‖u‖ ^ 2)) →
      ∀ v y : Euc d, 0 < ‖v‖ → ‖v‖ ≤ 1 / 2 → ∀ m ≤ k,
        ‖iteratedFDeriv ℝ m (fun y' : Euc d => r26t8a_Stil ρ Q (y' + v) y') y‖ ≤
          B1 * Cρ * A * jbracket y ^ M * ‖v‖ ^ (-s) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨sp, hsp⟩ : ∃ sp : ℝ, sp = max (σ' + 2) 0 := ⟨_, rfl⟩
  have hsp0 : 0 ≤ sp := by rw [hsp]; exact le_max_right _ _
  have hsp1 : σ' + 2 ≤ sp := by rw [hsp]; exact le_max_left _ _
  have hspd : sp < d := by rw [hsp]; exact max_lt hσ (by linarith)
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (sp + d) / 2 := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have hss : σ' + 2 < s := by rw [hs]; linarith
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_f18_env_pole b (e0 := σ' + 1 + ((0 : ℕ) : ℝ)) (s := s)
    (by simp only [Nat.cast_zero, add_zero]; linarith) hs0
  obtain ⟨C2, hC20, hC2⟩ := r26t8a_f18_env_pole b (e0 := σ' + 1 + 1 + ((0 : ℕ) : ℝ)) (s := s)
    (by simp only [Nat.cast_zero, add_zero]; linarith) hs0
  obtain ⟨Cp, hCp0, hCp⟩ := r26t8a_p10a_poly_gauss M hc
  refine ⟨s, 2 ^ k * d * (2 * C1 + 4 * C2) * Cp, hs0, hsd, by positivity, ?_⟩
  intro A hA Q hQ ρ hρ Cρ hCρ hρb v y hv hv2 m hm
  have hv0 : v ≠ 0 := norm_pos_iff.1 hv
  have hQ' : Conormal ((k + 1) + 1) b M σ' A Q := hQ
  have hJ1 : ∀ i : Fin d, Conormal (k + 1) b M (σ' + 1) (2 * A) (r26t8a_dx i Q) :=
    fun i => r26t8a_f8_dx_conormal hchi hA hQ' i
  have hJ2 : ∀ i : Fin d, Conormal k b M (σ' + 1 + 1) (2 * (2 * A)) (r26t8a_dx i (r26t8a_dx i Q)) :=
    fun i => r26t8a_f8_dx_conormal hchi (by positivity) (hJ1 i) i
  set pw : ℝ := HRS.MS.Phase2S82.pairWeight M (y + v) y with hpw
  have hpw0 : 0 ≤ pw := by
    rw [hpw]; unfold HRS.MS.Phase2S82.pairWeight
    exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hv1 : ‖v‖ ≤ 1 := by linarith
  have hrs0 : 0 ≤ ‖v‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg _) _
  -- centre jets of the two pair functions
  have cj1 : ∀ (i : Fin d), ∀ n ≤ k, ‖iteratedFDeriv ℝ n (fun y' : Euc d => r26t8a_dx i Q (y' + v) y') y‖ ≤
      (2 * A) * pw * (C1 * ‖v‖ ^ (-s)) := by
    intro i n hn
    have h1 := r26t8a_f17_center_jet (hJ1 i) (m := n) (by omega) hv0 hv1 y
    refine h1.trans ?_
    have h2 := hC1 ‖v‖ hv hv1
    have h2' : (1 + ‖v‖ ^ (-(σ' + 1 + ((0 : ℕ) : ℝ))) * (1 + |Real.log ‖v‖|) ^ b) ≤ C1 * ‖v‖ ^ (-s) := h2
    exact mul_le_mul_of_nonneg_left h2' (by positivity)
  have cj2 : ∀ (i : Fin d), ∀ n ≤ k, ‖iteratedFDeriv ℝ n (fun y' : Euc d => r26t8a_dx i (r26t8a_dx i Q) (y' + v) y') y‖ ≤
      (2 * (2 * A)) * pw * (C2 * ‖v‖ ^ (-s)) := by
    intro i n hn
    have h1 := r26t8a_f17_center_jet (hJ2 i) (m := n) hn hv0 hv1 y
    refine h1.trans ?_
    have h2 := hC2 ‖v‖ hv hv1
    have h2' : (1 + ‖v‖ ^ (-(σ' + 1 + 1 + ((0 : ℕ) : ℝ))) * (1 + |Real.log ‖v‖|) ^ b) ≤ C2 * ‖v‖ ^ (-s) := h2
    exact mul_le_mul_of_nonneg_left h2' (by positivity)
  have hρk : ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) ρ := fun n => hρ.of_le (by exact_mod_cast le_top)
  set g' : ℝ := Real.exp (-c * ‖y + v‖ ^ 2) with hg'
  have hg'0 : 0 ≤ g' := (Real.exp_pos _).le
  set fa : Euc d → ℝ := fun y' => ρ (y' + v) with hfa
  set fb : Fin d → Euc d → ℝ := fun i y' => fderiv ℝ ρ (y' + v) (EuclideanSpace.single i 1) with hfb
  set g1 : Fin d → Euc d → ℝ := fun i y' => r26t8a_dx i Q (y' + v) y' with hg1
  set g2 : Fin d → Euc d → ℝ := fun i y' => r26t8a_dx i (r26t8a_dx i Q) (y' + v) y' with hg2
  have hmaps : Set.MapsTo (fun y' : Euc d => (y' + v, y')) Set.univ {p : Euc d × Euc d | p.1 ≠ p.2} := by
    intro y' _
    show y' + v ≠ y'
    intro h; apply hv0; simpa using h
  have hlin : ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) (fun y' : Euc d => (y' + v, y')) := fun n =>
    (contDiff_id.add contDiff_const).prodMk contDiff_id
  have hg1c : ∀ i : Fin d, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (g1 i) := fun i =>
    contDiffOn_univ.1 (((hJ1 i).1.comp (hlin (k + 1)).contDiffOn hmaps))
  have hg2c : ∀ i : Fin d, ContDiff ℝ (k : WithTop ℕ∞) (g2 i) := fun i =>
    contDiffOn_univ.1 (((hJ2 i).1.comp (hlin k).contDiffOn hmaps))
  have hfac : ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) fa := fun n => (hρk n).comp (contDiff_id.add contDiff_const)
  have hfbc : ∀ (n : ℕ) (i : Fin d), ContDiff ℝ (n : WithTop ℕ∞) (fb i) := fun n i =>
    ((hρ.fderiv_right (m := n) (by exact_mod_cast le_top)).clm_apply contDiff_const).comp
      (contDiff_id.add contDiff_const)
  have ba : ∀ n ≤ k, ‖iteratedFDeriv ℝ n fa y‖ ≤ Cρ * g' := by
    intro n hn
    have : iteratedFDeriv ℝ n fa y = iteratedFDeriv ℝ n ρ (y + v) :=
      iteratedFDeriv_comp_add_right (f := ρ) n v y
    rw [this]; exact hρb n (by omega) (y + v)
  have bb : ∀ (i : Fin d), ∀ n ≤ k, ‖iteratedFDeriv ℝ n (fb i) y‖ ≤ Cρ * g' := by
    intro i n hn
    have hc : ContDiff ℝ (n : WithTop ℕ∞) (fun w : Euc d => fderiv ℝ ρ w (EuclideanSpace.single i 1)) :=
      (hρ.fderiv_right (m := n) (by exact_mod_cast le_top)).clm_apply contDiff_const
    have : iteratedFDeriv ℝ n (fb i) y =
        iteratedFDeriv ℝ n (fun w : Euc d => fderiv ℝ ρ w (EuclideanSpace.single i 1)) (y + v) :=
      iteratedFDeriv_comp_add_right (f := fun w : Euc d => fderiv ℝ ρ w (EuclideanSpace.single i 1)) n v y
    rw [this]
    refine (r26t8a_f13_dirderiv_jet ρ (EuclideanSpace.single i 1) n (hρk (n + 1)) (y + v)).trans ?_
    have hen : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
    rw [hen, one_mul]
    exact hρb (n + 1) (by omega) (y + v)
  have heq : (fun y' : Euc d => r26t8a_Stil ρ Q (y' + v) y') =
      fun y' => fa y' * (∑ i : Fin d, g2 i y') + ∑ i : Fin d, fb i y' * g1 i y' := rfl
  have hLapc : ContDiff ℝ (k : WithTop ℕ∞) (fun y' => ∑ i : Fin d, g2 i y') :=
    ContDiff.sum fun i _ => hg2c i
  have hLap : ∀ n ≤ k, ‖iteratedFDeriv ℝ n (fun y' => ∑ i : Fin d, g2 i y') y‖ ≤
      d * ((2 * (2 * A)) * pw * (C2 * ‖v‖ ^ (-s))) := by
    intro n hn
    rw [iteratedFDeriv_fun_sum_apply (fun i _ => ((hg2c i).of_le (by exact_mod_cast hn)).contDiffAt)]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : Fin d, ‖iteratedFDeriv ℝ n (g2 i) y‖ ≤ ∑ _i : Fin d, (2 * (2 * A)) * pw * (C2 * ‖v‖ ^ (-s)) :=
          Finset.sum_le_sum fun i _ => cj2 i n hn
      _ = d * ((2 * (2 * A)) * pw * (C2 * ‖v‖ ^ (-s))) := by simp
  have hprod1 : ∀ n ≤ k, ‖iteratedFDeriv ℝ n (fun y' => fa y' * ∑ i : Fin d, g2 i y') y‖ ≤
      2 ^ n * ((Cρ * g') * (d * ((2 * (2 * A)) * pw * (C2 * ‖v‖ ^ (-s))))) := fun n hn =>
    r26t8a_f10_jet_mul_on isOpen_univ ((hfac k).contDiffOn.of_le (by exact_mod_cast hn))
      (hLapc.contDiffOn.of_le (by exact_mod_cast hn)) (Set.mem_univ y)
      (fun j hj => ba j (hj.trans hn)) (fun j hj => hLap j (hj.trans hn))
  have hprod2 : ∀ (i : Fin d), ∀ n ≤ k, ‖iteratedFDeriv ℝ n (fun y' => fb i y' * g1 i y') y‖ ≤
      2 ^ n * ((Cρ * g') * ((2 * A) * pw * (C1 * ‖v‖ ^ (-s)))) := fun i n hn =>
    r26t8a_f10_jet_mul_on isOpen_univ ((hfbc k i).contDiffOn.of_le (by exact_mod_cast hn))
      (((hg1c i).of_le (by exact_mod_cast (by omega : n ≤ k + 1))).contDiffOn) (Set.mem_univ y)
      (fun j hj => bb i j (hj.trans hn)) (fun j hj => cj1 i j (hj.trans hn))
  have cd1 : ContDiffAt ℝ (m : WithTop ℕ∞) (fun y' => fa y' * ∑ i : Fin d, g2 i y') y :=
    (hfac m).contDiffAt.mul ((hLapc.of_le (by exact_mod_cast hm)).contDiffAt)
  have cd2 : ∀ i : Fin d, ContDiffAt ℝ (m : WithTop ℕ∞) (fun y' => fb i y' * g1 i y') y := fun i =>
    (hfbc m i).contDiffAt.mul (((hg1c i).of_le (by exact_mod_cast (by omega : m ≤ k + 1))).contDiffAt)
  rw [heq, fun_iteratedFDeriv_add_apply cd1 (ContDiffAt.sum fun i _ => cd2 i)]
  have hsum2 := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin d)))
    (f := fun i y' => fb i y' * g1 i y') (n := m) (x := y) (fun i _ => cd2 i)
  rw [hsum2]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (hprod1 m hm) ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ => hprod2 i m hm))).trans ?_
  have h2m : (2 : ℝ) ^ m ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hm
  have hX : 0 ≤ Cρ * g' * A * pw * ‖v‖ ^ (-s) := by positivity
  have hgp : g' * pw ≤ Cp * jbracket y ^ M := by
    rw [hpw]; unfold HRS.MS.Phase2S82.pairWeight
    have h1 : jbracket (y + v) ^ M * Real.exp (-c * ‖y + v‖ ^ 2) ≤ Cp * Real.exp (-(c / 2) * ‖y + v‖ ^ 2) :=
      le_trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (s83_jb_pos _).le (s83_jb_le_one_add _) hM) (Real.exp_pos _).le)
        (hCp ‖y + v‖ (norm_nonneg _))
    have h2 : Cp * Real.exp (-(c / 2) * ‖y + v‖ ^ 2) ≤ Cp := by
      have : Real.exp (-(c / 2) * ‖y + v‖ ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y + v‖])
      nlinarith
    have hjy : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos y).le _
    calc g' * (jbracket (y + v) ^ M * jbracket y ^ M) = (jbracket (y + v) ^ M * g') * jbracket y ^ M := by ring
      _ ≤ Cp * jbracket y ^ M := mul_le_mul_of_nonneg_right (h1.trans h2) hjy
  calc 2 ^ m * ((Cρ * g') * (d * ((2 * (2 * A)) * pw * (C2 * ‖v‖ ^ (-s))))) +
        ∑ _i : Fin d, 2 ^ m * ((Cρ * g') * ((2 * A) * pw * (C1 * ‖v‖ ^ (-s))))
      = 2 ^ m * (d * (4 * C2 + 2 * C1)) * (Cρ * A * (g' * pw) * ‖v‖ ^ (-s)) := by simp; ring
    _ ≤ 2 ^ k * (d * (4 * C2 + 2 * C1)) * (Cρ * A * (Cp * jbracket y ^ M) * ‖v‖ ^ (-s)) := by
        have hY : 0 ≤ Cρ * A * (g' * pw) * ‖v‖ ^ (-s) := by positivity
        calc 2 ^ m * (d * (4 * C2 + 2 * C1)) * (Cρ * A * (g' * pw) * ‖v‖ ^ (-s))
            ≤ 2 ^ k * (d * (4 * C2 + 2 * C1)) * (Cρ * A * (g' * pw) * ‖v‖ ^ (-s)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2m (by positivity)) hY
          _ ≤ _ := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgp (by positivity)) hrs0
    _ = 2 ^ k * d * (2 * C1 + 4 * C2) * Cp * Cρ * A * jbracket y ^ M * ‖v‖ ^ (-s) := by ring

end HRS.MS.R26T8A
