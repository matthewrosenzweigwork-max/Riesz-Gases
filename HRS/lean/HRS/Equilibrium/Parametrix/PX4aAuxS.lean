import HRS.Equilibrium.Parametrix.PX4aAuxR

/-!
# Packet PX4a auxiliaries S: bounds for the smooth parts of the divergence form
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- `∫ srcMaj = |A| · I0`. -/
def srcI0 (d : ℕ) (σ : ℝ) (b : ℕ) : ℝ :=
  ∫ w in Metric.ball (0 : Euc d) (1 / 8), (1 + ‖w‖ ^ (-σ) * (1 + |Real.log ‖w‖|) ^ b)

lemma srcI0_nonneg (σ : ℝ) (b : ℕ) : 0 ≤ srcI0 d σ b :=
  setIntegral_nonneg measurableSet_ball (fun w _ => by positivity)

lemma srcMaj_integral (σ : ℝ) (b : ℕ) (A : ℝ) : ∫ w, srcMaj d σ b A w = |A| * srcI0 d σ b := by
  unfold srcMaj srcI0
  rw [integral_indicator measurableSet_ball, integral_const_mul]

set_option maxHeartbeats 1600000 in
lemma kPot_Lam_bounds (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {σ : ℝ} (hσ : σ < d) (b M : ℕ) :
    ∃ NL : ℝ, 0 ≤ NL ∧ ∀ {A : ℝ} {g : Euc d × Euc d → ℝ}, SrcCls d σ b M A g → 0 ≤ A →
      ContDiff ℝ (M : WithTop ℕ∞) (kPot d (Lam d s) g) ∧
      ∀ j ≤ M, ∀ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j (kPot d (Lam d s) g) p‖ ≤ NL * A := by
  have hd1 : 1 ≤ d := by omega
  have hΛ : ContDiff ℝ (M : WithTop ℕ∞) (Lam d s) := by
    exact_mod_cast Lam_contDiff hd hs0 hsd (M : ℕ∞)
  have hbd : ∀ c : ℕ, ∃ Mc : ℝ, 0 ≤ Mc ∧ ∀ y, ‖iteratedFDeriv ℝ c (Lam d s) y‖ ≤ Mc :=
    fun c => Lam_bdd hd hs0 hsd c
  choose Mc hMc0 hMc using hbd
  set MΛ : ℝ := ∑ c ∈ Finset.range (M + 1), Mc c with hMΛ
  have hMΛ0 : 0 ≤ MΛ := Finset.sum_nonneg fun c _ => hMc0 c
  have hMle : ∀ c ≤ M, Mc c ≤ MΛ := fun c hc =>
    Finset.single_le_sum (f := Mc) (fun i _ => hMc0 i) (Finset.mem_range.mpr (by omega))
  have hΛb : ∀ i ≤ M, ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ i (Lam d s) y‖ ≤ B := fun i _ => ⟨Mc i, hMc i⟩
  refine ⟨2 ^ M * (MΛ * srcI0 d σ b), by have := srcI0_nonneg (d := d) σ b; positivity, ?_⟩
  intro A g h hA
  obtain ⟨hcd, -, -⟩ := kPot_far_FL hd1 hΛ hΛb hσ h
  refine ⟨hcd, fun j hj p => ?_⟩
  set W : ℝ := MΛ * (A * srcI0 d σ b) with hW
  have hW0 : 0 ≤ W := by have := srcI0_nonneg (d := d) σ b; positivity
  have hT : ∀ a c, a + c = j → TB (kPot d (Lam d s) g) p a c W := by
    intro a c hac u v
    have hb := kPot_far_bound hd1 hΛ hΛb hσ h (a := a) (c := c) (by omega) (hMc c) p.1 p.2 u v
    rw [srcMaj_integral, abs_of_nonneg hA] at hb
    refine hb.trans ?_
    have hP : 0 ≤ (∏ i, ‖u i‖) * ∏ j, ‖v j‖ :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    have h1 : |Mc c| = Mc c := abs_of_nonneg (hMc0 c)
    rw [h1]
    have h2 : Mc c * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) * (A * srcI0 d σ b) ≤ W * (∏ i, ‖u i‖) * ∏ j, ‖v j‖ := by
      have h3 : Mc c ≤ MΛ := hMle c (by omega)
      have h4 : 0 ≤ A * srcI0 d σ b := by have := srcI0_nonneg (d := d) σ b; positivity
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hP) h4
      calc Mc c * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) * (A * srcI0 d σ b)
          ≤ MΛ * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) * (A * srcI0 d σ b) := this
        _ = _ := by simp only [hW]; ring
    exact h2
  have hfull := full_of_tb j (kPot d (Lam d s) g) W hW0 (hcd.contDiffAt.of_le (by exact_mod_cast hj)) hT
  have hnorm : ‖iteratedFDeriv ℝ j (kPot d (Lam d s) g) p‖ ≤ 2 ^ j * W := by
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun w => ?_
    have := hfull w
    rw [Real.norm_eq_abs]
    linarith
  refine hnorm.trans ?_
  have h2j : (2 : ℝ) ^ j ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hj
  have : 0 ≤ W := hW0
  calc 2 ^ j * W ≤ 2 ^ M * W := mul_le_mul_of_nonneg_right h2j hW0
    _ = _ := by simp only [hW]; ring

lemma sf_bounds {ρ : Torus d → ℝ} {Ψ : Torus d → Torus d → ℝ} {m : ℕ}
    (hFs : ∀ i, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Fsrc (Psii ρ Ψ i))) {Kf : ℝ}
    (hK : ∀ i, ∀ j ≤ m + 1, ∀ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j (Fsrc (Psii ρ Ψ i)) p‖ ≤ Kf) :
    ContDiff ℝ (m : WithTop ℕ∞) (SFsrc ρ Ψ) ∧
    ∀ j ≤ m, ∀ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j (SFsrc ρ Ψ) p‖ ≤ d * Kf := by
  have hcd : ∀ i : Fin d, ContDiff ℝ (m : WithTop ℕ∞) (Ssrc (Fsrc (Psii ρ Ψ i)) i) := by
    intro i
    unfold Ssrc dirD
    exact ((hFs i).fderiv_right (m := m) (by norm_cast)).clm_apply contDiff_const
  have hsum : ContDiff ℝ (m : WithTop ℕ∞) (SFsrc ρ Ψ) := by
    unfold SFsrc
    exact ContDiff.sum fun i _ => hcd i
  refine ⟨hsum, fun j hj p => ?_⟩
  have hcdj : ∀ i ∈ (Finset.univ : Finset (Fin d)), ContDiff ℝ (j : WithTop ℕ∞) (Ssrc (Fsrc (Psii ρ Ψ i)) i) :=
    fun i _ => (hcd i).of_le (by exact_mod_cast hj)
  have e : iteratedFDeriv ℝ j (SFsrc ρ Ψ) = ∑ i ∈ (Finset.univ : Finset (Fin d)),
      iteratedFDeriv ℝ j (Ssrc (Fsrc (Psii ρ Ψ i)) i) := by
    unfold SFsrc
    exact iteratedFDeriv_sum hcdj
  rw [e]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      ‖iteratedFDeriv ℝ j (Ssrc (Fsrc (Psii ρ Ψ i)) i) p‖ ≤ Kf := by
    intro i _
    unfold Ssrc
    have hat : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (Fsrc (Psii ρ Ψ i)) p :=
      ((hFs i).of_le (by exact_mod_cast (by omega : j + 1 ≤ m + 1))).contDiffAt
    refine (norm_iteratedFDeriv_dirD_le hat _).trans ?_
    have : ‖((0 : Euc d), eVec d i)‖ = 1 := by
      rw [Prod.norm_def]; simp [norm_eVec]
    rw [this, mul_one]
    exact hK i (j + 1) (by omega) p
  rw [Finset.sum_apply]
  calc ‖∑ i ∈ (Finset.univ : Finset (Fin d)), iteratedFDeriv ℝ j (Ssrc (Fsrc (Psii ρ Ψ i)) i) p‖
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin d)), ‖iteratedFDeriv ℝ j (Ssrc (Fsrc (Psii ρ Ψ i)) i) p‖ := by
        have := norm_sum_le (Finset.univ : Finset (Fin d)) (fun i => iteratedFDeriv ℝ j (Ssrc (Fsrc (Psii ρ Ψ i)) i) p)
        simpa using this
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin d)), Kf := Finset.sum_le_sum hterm
    _ = d * Kf := by simp

end HRS.Parx

end
