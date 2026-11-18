import HRS.MS.R26T8AP11f20

/-!
# S8.2 T8A P11f (part 21): the model `D̃` is `C^k` with joint jets `≤ B Cρ A jb(y)^M`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem r26t8a_f21_model_jets {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (hd : 2 ≤ d) (k b : ℕ)
    (M σ' c : ℝ) (hM : 0 ≤ M) (hc : 0 < c) (hσ : σ' + 2 < d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (A : ℝ), 0 ≤ A → ∀ {Q : Euc d → Euc d → ℝ}, Conormal (k + 2) b M σ' A Q →
      ∀ {ρ : Euc d → ℝ}, ContDiff ℝ ∞ ρ → ∀ {Cρ : ℝ}, 0 ≤ Cρ →
      (∀ j ≤ k + 1, ∀ u : Euc d, ‖iteratedFDeriv ℝ j ρ u‖ ≤ Cρ * Real.exp (-c * ‖u‖ ^ 2)) →
      ContDiff ℝ (k : WithTop ℕ∞) (r26t8a_f20_model chi ((d : ℝ) / 2) ((d : ℝ) / 2) ρ Q) ∧
      ∀ j ≤ k, ∀ p : Euc d × Euc d,
        ‖iteratedFDeriv ℝ j (r26t8a_f20_model chi ((d : ℝ) / 2) ((d : ℝ) / 2) ρ Q) p‖ ≤
          B * Cρ * A * jbracket p.2 ^ M := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < (d : ℝ) / 2 := by linarith
  have hsd : (d : ℝ) / 2 < d := by linarith
  obtain ⟨hψ, hθ1, hθ2, hψ1, hψ0, hθ10, hθ20, ⟨Cθ1, hCθ10, hCθ1⟩, ⟨Cθ2, hCθ20, hCθ2⟩, ⟨Cc, hCc0, hCc⟩,
    ⟨Cc1, hCc10, hCc1⟩⟩ := r26t8a_f20_cutoffs hchi k
  obtain ⟨B0, hB00, hB0⟩ := r26t8a_f15_Stheta hchi k b M σ' c hM hc
  obtain ⟨C6, hC60, hC6⟩ := r26t8a_f6_pot_smooth d hd k (s := (d : ℝ) / 2) hs0 hsd (M := M) (c := c / 2) hM
    (by linarith)
  obtain ⟨s', B1, hs'0, hs'd, hB10, hB1⟩ := r26t8a_f18_Sg_jets hchi hd k b M σ' c hM hc hσ
  obtain ⟨C5, hC50, hC5⟩ := r26t8a_f5_pot_sing d hd k hs'0 hs'd hM
  obtain ⟨BK, hBK0, hBK⟩ := r26t8a_f16_Kc_global d hd ((d : ℝ) / 2) hs0 hsd chi hchi k
  refine ⟨C6 * B0 * Cθ1 + 4 ^ k * Cc * C6 * B0 * Cθ2 + 4 ^ k * Cc1 * C5 * BK * B1, by positivity, ?_⟩
  intro A hA Q hQ ρ hρ Cρ hCρ hρb
  have hQ1 : ContDiffOn ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (Function.uncurry Q) {p | p.1 ≠ p.2} := hQ.1
  have hSt := r26t8a_f12_Stil_contDiffOn hQ1 hρ
  have hρ0 : 0 ≤ B0 * Cθ1 * Cρ * A := by positivity
  have hρ0' : 0 ≤ B0 * Cθ2 * Cρ * A := by positivity
  -- the two smooth potentials
  obtain ⟨hH1c, hH1j⟩ := hB0 A hA hQ hρ hCρ hρb (hθ1.of_le (by exact_mod_cast le_top)) hCθ10 hCθ1 hθ10
  obtain ⟨hH2c, hH2j⟩ := hB0 A hA hQ hρ hCρ hρb (hθ2.of_le (by exact_mod_cast le_top)) hCθ20 hCθ2 hθ20
  obtain ⟨X1c, X1j⟩ := hC6 (B0 * Cθ1 * Cρ * A) (fun u y => r26t8a_f20_th1 chi (u - y) * r26t8a_Stil ρ Q u y)
    hρ0 hH1c hH1j
  obtain ⟨X2c, X2j⟩ := hC6 (B0 * Cθ2 * Cρ * A) (fun u y => r26t8a_f20_th2 chi (u - y) * r26t8a_Stil ρ Q u y)
    hρ0' hH2c hH2j
  -- the singular-source potential with the smooth kernel
  have hKcs : ContDiff ℝ (k : WithTop ℕ∞) (r26t8a_Kc ((d : ℝ) / 2) chi (1 / 2 : ℝ)) :=
    (r26t8a_Kc_contDiff d hd ((d : ℝ) / 2) hs0 hsd chi hchi (δ := 1 / 2) (by norm_num)).of_le
      (by exact_mod_cast le_top)
  have hSgc : ContDiffOn ℝ (k : WithTop ℕ∞)
      (Function.uncurry (fun v y : Euc d => r26t8a_Stil ρ Q (y + v) y)) {q : Euc d × Euc d | q.1 ≠ 0} := by
    have hlin : ContDiff ℝ (k : WithTop ℕ∞) (fun q : Euc d × Euc d => (q.2 + q.1, q.2)) :=
      (contDiff_snd.add contDiff_fst).prodMk contDiff_snd
    have hmaps : Set.MapsTo (fun q : Euc d × Euc d => (q.2 + q.1, q.2)) {q : Euc d × Euc d | q.1 ≠ 0}
        {p : Euc d × Euc d | p.1 ≠ p.2} := by
      intro q hq
      show q.2 + q.1 ≠ q.2
      intro h; apply hq; simpa using h
    exact hSt.comp hlin.contDiffOn hmaps
  obtain ⟨Yc, Yj⟩ := hC5 chi hchi (r26t8a_Kc ((d : ℝ) / 2) chi (1 / 2 : ℝ)) BK hKcs hBK
    (r26t8a_f20_psi chi) (hψ.of_le (by exact_mod_cast le_top)) hψ1 hψ0
    (fun v y => r26t8a_Stil ρ Q (y + v) y) (B1 * Cρ * A) (by positivity) hSgc
    (fun v y hv hv2 m hm => hB1 A hA hQ hρ hCρ hρb v y hv hv2 m hm)
  -- the cutoff factors
  have hchl : ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => chi (p.1 - p.2)) :=
    (hchi.1.of_le (by exact_mod_cast le_top)).comp (contDiff_fst.sub contDiff_snd)
  have hch1l : ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => 1 - chi (p.1 - p.2)) :=
    contDiff_const.sub hchl
  have jc : ∀ j ≤ k, ∀ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j (fun q : Euc d × Euc d => chi (q.1 - q.2)) p‖ ≤
      Cc * 2 ^ k := by
    intro j hj p
    have h1 := r26t8a_f4_jet_kernel (K := chi) (i := j) (hchi.1.of_le (by exact_mod_cast le_top)) (B := Cc)
      (fun v => hCc j hj v) 0 p
    have e : (fun q : Euc d × Euc d => chi (q.1 - q.2)) = fun q : Euc d × Euc d => chi (q.1 - q.2 - 0) := by
      funext q; simp
    rw [e]
    exact h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) hCc0)
  have jc1 : ∀ j ≤ k, ∀ p : Euc d × Euc d,
      ‖iteratedFDeriv ℝ j (fun q : Euc d × Euc d => 1 - chi (q.1 - q.2)) p‖ ≤ Cc1 * 2 ^ k := by
    intro j hj p
    have hK1 : ContDiff ℝ (j : WithTop ℕ∞) (fun v : Euc d => 1 - chi v) :=
      (contDiff_const.sub (hchi.1.of_le (by exact_mod_cast le_top)))
    have h1 := r26t8a_f4_jet_kernel (K := fun v : Euc d => 1 - chi v) (i := j) hK1 (B := Cc1)
      (fun v => hCc1 j hj v) 0 p
    have e : (fun q : Euc d × Euc d => 1 - chi (q.1 - q.2)) =
        fun q : Euc d × Euc d => (fun v : Euc d => 1 - chi v) (q.1 - q.2 - 0) := by
      funext q; simp
    rw [e]
    exact h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) hCc10)
  set Kc : Euc d → ℝ := r26t8a_Kc ((d : ℝ) / 2) chi (1 / 2 : ℝ) with hKc
  set X1 : Euc d × Euc d → ℝ := fun p => ∫ w, ‖w‖ ^ (-((d : ℝ) / 2)) *
    (fun u y : Euc d => r26t8a_f20_th1 chi (u - y) * r26t8a_Stil ρ Q u y) (p.1 - w) p.2 with hX1
  set X2 : Euc d × Euc d → ℝ := fun p => ∫ w, ‖w‖ ^ (-((d : ℝ) / 2)) *
    (fun u y : Euc d => r26t8a_f20_th2 chi (u - y) * r26t8a_Stil ρ Q u y) (p.1 - w) p.2 with hX2
  set Y : Euc d × Euc d → ℝ := fun p => ∫ v, r26t8a_f5_G Kc (r26t8a_f20_psi chi)
    (fun v y => r26t8a_Stil ρ Q (y + v) y) v p with hY
  have hmodel : r26t8a_f20_model chi ((d : ℝ) / 2) ((d : ℝ) / 2) ρ Q =
      fun p : Euc d × Euc d => (X1 p - chi (p.1 - p.2) * X2 p) + (1 - chi (p.1 - p.2)) * Y p := rfl
  rw [hmodel]
  refine ⟨(X1c.sub (hchl.mul X2c)).add (hch1l.mul Yc), fun j hj p => ?_⟩
  have hjk : (j : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hj
  have cdX1 : ContDiffAt ℝ (j : WithTop ℕ∞) X1 p := (X1c.of_le hjk).contDiffAt
  have cdX2 : ContDiffAt ℝ (j : WithTop ℕ∞) X2 p := (X2c.of_le hjk).contDiffAt
  have cdY : ContDiffAt ℝ (j : WithTop ℕ∞) Y p := (Yc.of_le hjk).contDiffAt
  have cdc : ContDiffAt ℝ (j : WithTop ℕ∞) (fun q : Euc d × Euc d => chi (q.1 - q.2)) p :=
    (hchl.of_le hjk).contDiffAt
  have cdc1 : ContDiffAt ℝ (j : WithTop ℕ∞) (fun q : Euc d × Euc d => 1 - chi (q.1 - q.2)) p :=
    (hch1l.of_le hjk).contDiffAt
  have hjbp : 0 ≤ jbracket p.2 ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
  have pa : ‖iteratedFDeriv ℝ j (fun q => chi (q.1 - q.2) * X2 q) p‖ ≤
      2 ^ j * (Cc * 2 ^ k * (C6 * (B0 * Cθ2 * Cρ * A) * jbracket p.2 ^ M)) :=
    r26t8a_f10_jet_mul_on isOpen_univ ((hchl.of_le hjk).contDiffOn) ((X2c.of_le hjk).contDiffOn)
      (Set.mem_univ p) (fun m hm => jc m (hm.trans hj) p) (fun m hm => X2j m (hm.trans hj) p)
  have pb : ‖iteratedFDeriv ℝ j (fun q => (1 - chi (q.1 - q.2)) * Y q) p‖ ≤
      2 ^ j * (Cc1 * 2 ^ k * (C5 * BK * (B1 * Cρ * A) * jbracket p.2 ^ M)) :=
    r26t8a_f10_jet_mul_on isOpen_univ ((hch1l.of_le hjk).contDiffOn) ((Yc.of_le hjk).contDiffOn)
      (Set.mem_univ p) (fun m hm => jc1 m (hm.trans hj) p) (fun m hm => Yj m (hm.trans hj) p)
  rw [fun_iteratedFDeriv_add_apply (cdX1.sub (cdc.mul cdX2)) (cdc1.mul cdY),
    fun_iteratedFDeriv_sub_apply cdX1 (cdc.mul cdX2)]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
  have h1 := X1j j hj p
  have h2j : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
  have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  have hXa : 0 ≤ Cc * (C6 * (B0 * Cθ2 * Cρ * A) * jbracket p.2 ^ M) := by positivity
  have hXb : 0 ≤ Cc1 * (C5 * BK * (B1 * Cρ * A) * jbracket p.2 ^ M) := by positivity
  calc ‖iteratedFDeriv ℝ j X1 p‖ + ‖iteratedFDeriv ℝ j (fun q => chi (q.1 - q.2) * X2 q) p‖ +
        ‖iteratedFDeriv ℝ j (fun q => (1 - chi (q.1 - q.2)) * Y q) p‖
      ≤ C6 * (B0 * Cθ1 * Cρ * A) * jbracket p.2 ^ M +
        2 ^ k * (Cc * 2 ^ k * (C6 * (B0 * Cθ2 * Cρ * A) * jbracket p.2 ^ M)) +
        2 ^ k * (Cc1 * 2 ^ k * (C5 * BK * (B1 * Cρ * A) * jbracket p.2 ^ M)) := by
        refine add_le_add (add_le_add h1 (pa.trans ?_)) (pb.trans ?_)
        · exact mul_le_mul_of_nonneg_right h2j (by positivity)
        · exact mul_le_mul_of_nonneg_right h2j (by positivity)
    _ = (C6 * B0 * Cθ1 + 4 ^ k * Cc * C6 * B0 * Cθ2 + 4 ^ k * Cc1 * C5 * BK * B1) * Cρ * A * jbracket p.2 ^ M := by
        rw [h4]; ring

end HRS.MS.R26T8A
