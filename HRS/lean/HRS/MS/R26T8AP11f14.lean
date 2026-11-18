import HRS.MS.R26T8AP11f13

/-!
# S8.2 T8A P11f (part 14): joint jets of `Stil ρ Q` for `|u-y| ≥ 1/4`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem r26t8a_f14_Stil_jets {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k b : ℕ) (M σ' c : ℝ) :
    ∃ BS : ℝ, 0 ≤ BS ∧ ∀ (A : ℝ), 0 ≤ A → ∀ {Q : Euc d → Euc d → ℝ}, Conormal (k + 2) b M σ' A Q →
      ∀ {ρ : Euc d → ℝ}, ContDiff ℝ ∞ ρ → ∀ {Cρ : ℝ}, 0 ≤ Cρ →
      (∀ j ≤ k + 1, ∀ u : Euc d, ‖iteratedFDeriv ℝ j ρ u‖ ≤ Cρ * Real.exp (-c * ‖u‖ ^ 2)) →
      ∀ j ≤ k, ∀ u y : Euc d, 1 / 4 ≤ ‖u - y‖ →
        ‖iteratedFDeriv ℝ j (Function.uncurry (r26t8a_Stil ρ Q)) (u, y)‖ ≤
          BS * Cρ * A * Real.exp (-c * ‖u‖ ^ 2) * HRS.MS.Phase2S82.pairWeight M u y := by
  obtain ⟨CJ1, hCJ10, hCJ1⟩ := r26t8a_f11_joint_far hchi (k + 1) b M (σ' + 1) (d := d)
  obtain ⟨CJ2, hCJ20, hCJ2⟩ := r26t8a_f11_joint_far hchi k b M (σ' + 1 + 1) (d := d)
  refine ⟨2 ^ k * d * (4 * CJ2 + 2 * CJ1), by positivity, ?_⟩
  intro A hA Q hQ ρ hρ Cρ hCρ hρb j hj u y huy
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hp : (u, y) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} := by
    show u ≠ y
    intro h; rw [h, sub_self, norm_zero] at huy; linarith
  have hQ1 : ContDiffOn ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (Function.uncurry Q) {p | p.1 ≠ p.2} := hQ.1
  have hQ' : Conormal ((k + 1) + 1) b M σ' A Q := hQ
  have hJ1 : ∀ i : Fin d, Conormal (k + 1) b M (σ' + 1) (2 * A) (r26t8a_dx i Q) :=
    fun i => r26t8a_f8_dx_conormal hchi hA hQ' i
  have hJ2 : ∀ i : Fin d, Conormal k b M (σ' + 1 + 1) (2 * (2 * A)) (r26t8a_dx i (r26t8a_dx i Q)) :=
    fun i => r26t8a_f8_dx_conormal hchi (by positivity) (hJ1 i) i
  set pw : ℝ := HRS.MS.Phase2S82.pairWeight M u y with hpw
  set g : ℝ := Real.exp (-c * ‖u‖ ^ 2) with hg
  have hg0 : 0 ≤ g := (Real.exp_pos _).le
  have hpw0 : 0 ≤ pw := by
    rw [hpw]; unfold HRS.MS.Phase2S82.pairWeight
    exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  -- component functions
  set r0 : Euc d × Euc d → ℝ := fun q => ρ q.1 with hr0
  set r1 : Fin d → Euc d × Euc d → ℝ := fun i q => fderiv ℝ ρ q.1 (EuclideanSpace.single i 1) with hr1
  set j1 : Fin d → Euc d × Euc d → ℝ := fun i => Function.uncurry (r26t8a_dx i Q) with hj1
  set j2 : Fin d → Euc d × Euc d → ℝ := fun i => Function.uncurry (r26t8a_dx i (r26t8a_dx i Q)) with hj2
  have hρk : ∀ m : ℕ, ContDiff ℝ (m : WithTop ℕ∞) ρ := fun m => hρ.of_le (by exact_mod_cast le_top)
  have hr0c : ∀ m : ℕ, ContDiff ℝ (m : WithTop ℕ∞) r0 := fun m => (hρk m).comp contDiff_fst
  have hr1c : ∀ (m : ℕ) (i : Fin d), ContDiff ℝ (m : WithTop ℕ∞) (r1 i) := fun m i =>
    ((hρ.fderiv_right (m := m) (by exact_mod_cast le_top)).clm_apply contDiff_const).comp contDiff_fst
  have hj1c : ∀ i : Fin d, ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (j1 i) {p | p.1 ≠ p.2} :=
    fun i => (hJ1 i).1
  have hj2c : ∀ i : Fin d, ContDiffOn ℝ (k : WithTop ℕ∞) (j2 i) {p | p.1 ≠ p.2} := fun i => (hJ2 i).1
  have hUn : ∀ i : ℕ, ∀ n : ℕ, n ≤ i → ((n : ℕ) : WithTop ℕ∞) ≤ ((i : ℕ) : WithTop ℕ∞) :=
    fun i n h => by exact_mod_cast h
  -- the pointwise bounds
  have b0 : ∀ m ≤ k, ‖iteratedFDeriv ℝ m r0 (u, y)‖ ≤ Cρ * g := fun m hm =>
    (r26t8a_f13_jet_fst (hρk m) (u, y)).trans (hρb m (by omega) u)
  have b1 : ∀ (i : Fin d), ∀ m ≤ k, ‖iteratedFDeriv ℝ m (r1 i) (u, y)‖ ≤ Cρ * g := by
    intro i m hm
    have hc : ContDiff ℝ (m : WithTop ℕ∞) (fun w : Euc d => fderiv ℝ ρ w (EuclideanSpace.single i 1)) :=
      (hρ.fderiv_right (m := m) (by exact_mod_cast le_top)).clm_apply contDiff_const
    refine (r26t8a_f13_jet_fst hc (u, y)).trans ?_
    refine (r26t8a_f13_dirderiv_jet ρ (EuclideanSpace.single i 1) m (hρk (m + 1)) u).trans ?_
    have hen : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
    rw [hen, one_mul]
    exact hρb (m + 1) (by omega) u
  have c1 : ∀ (i : Fin d), ∀ m ≤ k, ‖iteratedFDeriv ℝ m (j1 i) (u, y)‖ ≤ CJ1 * (2 * A) * pw := fun i m hm =>
    hCJ1 (2 * A) (by positivity) (hJ1 i) m (by omega) u y huy
  have c2 : ∀ (i : Fin d), ∀ m ≤ k, ‖iteratedFDeriv ℝ m (j2 i) (u, y)‖ ≤ CJ2 * (2 * (2 * A)) * pw := fun i m hm =>
    hCJ2 (2 * (2 * A)) (by positivity) (hJ2 i) m hm u y huy
  have heq : Function.uncurry (r26t8a_Stil ρ Q) =
      fun q => r0 q * (∑ i : Fin d, j2 i q) + ∑ i : Fin d, r1 i q * j1 i q := by
    funext q; rfl
  have cdA : ∀ (m : ℕ), m ≤ k → ∀ i : Fin d, ContDiffAt ℝ (m : WithTop ℕ∞) (j2 i) (u, y) := fun m hm i =>
    ((hj2c i).contDiffAt (hopen.mem_nhds hp)).of_le (hUn k m hm)
  have cdB : ∀ (m : ℕ), m ≤ k → ∀ i : Fin d, ContDiffAt ℝ (m : WithTop ℕ∞) (j1 i) (u, y) := fun m hm i =>
    ((hj1c i).contDiffAt (hopen.mem_nhds hp)).of_le (hUn (k + 1) m (by omega))
  have hLapOn : ContDiffOn ℝ (k : WithTop ℕ∞) (fun q => ∑ i : Fin d, j2 i q) {p | p.1 ≠ p.2} :=
    ContDiffOn.sum fun i _ => hj2c i
  have hLap : ∀ m ≤ k, ‖iteratedFDeriv ℝ m (fun q => ∑ i : Fin d, j2 i q) (u, y)‖ ≤
      d * (CJ2 * (2 * (2 * A)) * pw) := by
    intro m hm
    rw [iteratedFDeriv_fun_sum_apply (fun i _ => cdA m hm i)]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : Fin d, ‖iteratedFDeriv ℝ m (j2 i) (u, y)‖ ≤ ∑ _i : Fin d, CJ2 * (2 * (2 * A)) * pw :=
          Finset.sum_le_sum fun i _ => c2 i m hm
      _ = d * (CJ2 * (2 * (2 * A)) * pw) := by simp
  have hprod1 : ∀ n ≤ k, ‖iteratedFDeriv ℝ n (fun q => r0 q * ∑ i : Fin d, j2 i q) (u, y)‖ ≤
      2 ^ n * ((Cρ * g) * (d * (CJ2 * (2 * (2 * A)) * pw))) := fun n hn =>
    r26t8a_f10_jet_mul_on hopen ((hr0c k).contDiffOn.of_le (hUn k n hn))
      (hLapOn.of_le (hUn k n hn)) hp (fun m hm => b0 m (hm.trans hn)) (fun m hm => hLap m (hm.trans hn))
  have hprod2 : ∀ (i : Fin d), ∀ n ≤ k, ‖iteratedFDeriv ℝ n (fun q => r1 i q * j1 i q) (u, y)‖ ≤
      2 ^ n * ((Cρ * g) * (CJ1 * (2 * A) * pw)) := fun i n hn =>
    r26t8a_f10_jet_mul_on hopen ((hr1c k i).contDiffOn.of_le (hUn k n hn))
      (((hj1c i).of_le (hUn (k + 1) n (by omega)))) hp (fun m hm => b1 i m (hm.trans hn))
      (fun m hm => c1 i m (hm.trans hn))
  have cd1 : ContDiffAt ℝ (j : WithTop ℕ∞) (fun q => r0 q * ∑ i : Fin d, j2 i q) (u, y) :=
    ((hr0c j).contDiffAt).mul ((hLapOn.contDiffAt (hopen.mem_nhds hp)).of_le (hUn k j hj))
  have cd2 : ∀ i : Fin d, ContDiffAt ℝ (j : WithTop ℕ∞) (fun q => r1 i q * j1 i q) (u, y) := fun i =>
    ((hr1c j i).contDiffAt).mul (cdB j hj i)
  rw [heq, fun_iteratedFDeriv_add_apply cd1 (ContDiffAt.sum fun i _ => cd2 i)]
  have hsum2 := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin d)))
    (f := fun i q => r1 i q * j1 i q) (n := j) (x := (u, y)) (fun i _ => cd2 i)
  rw [hsum2]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (hprod1 j hj) ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hprod2 i j hj))).trans ?_
  have h2j : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
  have hX : 0 ≤ Cρ * g * A * pw := by positivity
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  calc 2 ^ j * (Cρ * g * (d * (CJ2 * (2 * (2 * A)) * pw))) +
        ∑ _i : Fin d, 2 ^ j * (Cρ * g * (CJ1 * (2 * A) * pw))
      = 2 ^ j * (d * (4 * CJ2 + 2 * CJ1)) * (Cρ * g * A * pw) := by simp; ring
    _ ≤ 2 ^ k * (d * (4 * CJ2 + 2 * CJ1)) * (Cρ * g * A * pw) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2j (by positivity)) hX
    _ = 2 ^ k * d * (4 * CJ2 + 2 * CJ1) * Cρ * A * g * pw := by ring

end HRS.MS.R26T8A
