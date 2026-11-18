import HRS.Equilibrium.Parametrix.PX4bAuxJ
import HRS.PDE.EnergyTorusSqrt
import HRS.PDE.Toolbox.CoeffBounds

/-!
# Packet PX4b auxiliaries K: smooth kernels, vanishing near the diagonal, relaxing the order
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma px4b_norm_chartT_pat_le {a c : ℕ} (u : Fin a → Euc d) (v : Fin c → Euc d) :
    ∏ j, ‖chartT d (pat u v j)‖ ≤ (∏ i, ‖u i‖) * ∏ j, ‖v j‖ := by
  rw [Fin.prod_univ_add]
  have h1 : ∏ i : Fin a, ‖chartT d (pat u v (Fin.castAdd c i))‖ = ∏ i, ‖u i‖ := by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [pat, Fin.append_left, chartT_apply, smul_zero, add_zero, sub_zero, Prod.norm_def,
      max_self]
  have h2 : ∏ j : Fin c, ‖chartT d (pat u v (Fin.natAdd a j))‖ ≤ ∏ j, ‖v j‖ := by
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
    simp only [pat, Fin.append_right, chartT_apply, zero_add, zero_sub, Prod.norm_def, norm_neg,
      norm_smul, max_self, Real.norm_eq_abs]
    have hv := norm_nonneg (v j)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith
  rw [h1]
  exact mul_le_mul_of_nonneg_left h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _)

/-- A `C^m` kernel on `𝕋^d × 𝕋^d` with `‖D^j‖ ≤ M` (`j ≤ m`) belongs to every conormal class. -/
theorem px4b_conormal_ckM (σ : ℝ) (b : ℕ → ℕ) {m : ℕ} {k : Torus d → Torus d → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hk : PDE.IsCk2 m k)
    (hb : ∀ j ≤ m, ∀ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j (lift2 k) p‖ ≤ M) :
    ConormalL σ b m M k where
  smooth := hk.contDiffOn
  near := by
    intro a c hac X z hz hzr
    have hq : (X, z) ∈ Uc d := mem_Uc hz hzr
    have hcd : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (toChart k) := by
      rw [toChart_eq]
      exact (show ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (lift2 k) from
        hk.of_le (by exact_mod_cast hac)).comp (chartT d).contDiff
    have hTB : TB (toChart k) (X, z) a c M := by
      intro u v
      have hkf : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (lift2 k) :=
        hk.of_le (by exact_mod_cast hac)
      rw [toChart_eq, ContinuousLinearMap.iteratedFDeriv_comp_right (chartT d) hkf (X, z) le_rfl]
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      rw [← Real.norm_eq_abs]
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      have h1 : ‖iteratedFDeriv ℝ (a + c) (lift2 k) (chartT d (X, z))‖ ≤ M := hb _ hac _
      have h2 := px4b_norm_chartT_pat_le u v
      have hp : 0 ≤ ∏ j : Fin (a + c), ‖chartT d (pat u v j)‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
      calc ‖iteratedFDeriv ℝ (a + c) (lift2 k) (chartT d (X, z))‖ * ∏ j, ‖chartT d (pat u v j)‖
          ≤ M * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := mul_le_mul h1 h2 hp hM0
        _ = _ := by ring
    have := norm_le_of_tb isOpen_Uc hcd.contDiffOn hq hM0 hTB
    refine this.trans ?_
    have hw : 0 ≤ ‖z‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖z‖|) ^ b c :=
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
    nlinarith
  far := fun k' hk' p _ _ => hb k' hk' p

theorem px4b_conormal_ck (σ : ℝ) (b : ℕ → ℕ) {m : ℕ} {k : Torus d → Torus d → ℝ}
    (hk : PDE.IsCk2 m k) : ConormalL σ b m (PDE.cbNorm2 m k) k :=
  px4b_conormal_ckM σ b (PDE.MFPair.cbNorm2_nonneg m k) hk
    (fun j hj p => PDE.MFPair.norm_iteratedFDeriv_le_cbNorm2 hk hj p)

theorem px4b_isCk2_fst {k : ℕ} {q : Torus d → ℝ} (hq : Torus.IsCk (k : WithTop ℕ∞) q) :
    PDE.IsCk2 k (fun x _ => q x) := by
  show ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => q (Torus.mk p.1))
  exact (show ContDiff ℝ (k : WithTop ℕ∞) (Torus.lift q) from hq).comp contDiff_fst

theorem px4b_isCk2_snd {k : ℕ} {q : Torus d → ℝ} (hq : Torus.IsCk (k : WithTop ℕ∞) q) :
    PDE.IsCk2 k (fun _ y => q y) := by
  show ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => q (Torus.mk p.2))
  exact (show ContDiff ℝ (k : WithTop ℕ∞) (Torus.lift q) from hq).comp contDiff_snd

/-- A `C^m` function of the first variable is in every conormal class (constant `cbNorm m`). -/
theorem px4b_conormal_fst (σ : ℝ) (b : ℕ → ℕ) {m : ℕ} {f : Torus d → ℝ}
    (hf : Torus.IsCk (m : WithTop ℕ∞) f) : ConormalL σ b m (Torus.cbNorm m f) (fun x _ => f x) := by
  refine px4b_conormal_ckM σ b (PDE.cbNorm_nonneg'C m f) (px4b_isCk2_fst hf) ?_
  intro j hj p
  have hfc : ContDiff ℝ (j : WithTop ℕ∞) (Torus.lift f) :=
    (show ContDiff ℝ (m : WithTop ℕ∞) (Torus.lift f) from hf).of_le (by exact_mod_cast hj)
  have e : lift2 (fun x (_ : Torus d) => f x) = Torus.lift f ∘ (ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) := rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hfc p le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin j, ‖ContinuousLinearMap.fst ℝ (Euc d) (Euc d)‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le _ _ _)
  calc _ ≤ ‖iteratedFDeriv ℝ j (Torus.lift f) (ContinuousLinearMap.fst ℝ (Euc d) (Euc d) p)‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ Torus.cbNorm m f := by
        rw [mul_one]
        exact PDE.ET.norm_iteratedFDeriv_le_cbNorm hj hf _

theorem px4b_conormal_snd (σ : ℝ) (b : ℕ → ℕ) {m : ℕ} {f : Torus d → ℝ}
    (hf : Torus.IsCk (m : WithTop ℕ∞) f) : ConormalL σ b m (Torus.cbNorm m f) (fun _ y => f y) := by
  refine px4b_conormal_ckM σ b (PDE.cbNorm_nonneg'C m f) (px4b_isCk2_snd hf) ?_
  intro j hj p
  have hfc : ContDiff ℝ (j : WithTop ℕ∞) (Torus.lift f) :=
    (show ContDiff ℝ (m : WithTop ℕ∞) (Torus.lift f) from hf).of_le (by exact_mod_cast hj)
  have e : lift2 (fun (_ : Torus d) y => f y) = Torus.lift f ∘ (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) := rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hfc p le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin j, ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le _ _ _)
  calc _ ≤ ‖iteratedFDeriv ℝ j (Torus.lift f) (ContinuousLinearMap.snd ℝ (Euc d) (Euc d) p)‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ Torus.cbNorm m f := by
        rw [mul_one]
        exact PDE.ET.norm_iteratedFDeriv_le_cbNorm hj hf _

/-- Constant of `px4b_conormal_vanish`. -/
def px4b_Cvan (σ : ℝ) (b : ℕ → ℕ) (m : ℕ) (δ0 : ℝ) : ℝ :=
  ∑ c ∈ Finset.range (m + 1), (1 + (δ0 ^ (-(σ + (c : ℝ))) + 1) * (1 + |Real.log δ0|) ^ b c)

lemma px4b_Cvan_ge_one (σ : ℝ) (b : ℕ → ℕ) (m : ℕ) {δ0 : ℝ} (hδ0 : 0 < δ0) :
    1 ≤ px4b_Cvan σ b m δ0 := by
  unfold px4b_Cvan
  have hnn : ∀ c ∈ Finset.range (m + 1), 0 ≤ (1 + (δ0 ^ (-(σ + (c : ℝ))) + 1) * (1 + |Real.log δ0|) ^ b c) :=
    fun c _ => by positivity
  have h0 := Finset.single_le_sum hnn (Finset.mem_range.mpr (Nat.succ_pos m))
  refine le_trans ?_ h0
  have : 0 ≤ (δ0 ^ (-(σ + ((0 : ℕ) : ℝ))) + 1) * (1 + |Real.log δ0|) ^ b 0 := by positivity
  linarith

lemma px4b_mixedDeriv_zero_of_eq {G : Euc d × Euc d → ℝ} (a c : ℕ) (X z : Euc d)
    {U : Set (Euc d)} (hU : U ∈ 𝓝 z) (h : ∀ X' z', z' ∈ U → G (X', z') = 0) :
    mixedDeriv a c G X z = 0 := by
  have := mixedDeriv_congr (G₁ := G) (G₂ := fun _ : Euc d × Euc d => (0 : ℝ)) a c X z hU h
  rw [this]
  unfold mixedDeriv
  simp [iteratedFDeriv_zero_fun]

/-- A conormal kernel whose chart function vanishes for `0 < |z| < δ0` belongs to every class
(of any order). -/
theorem px4b_conormal_vanish {σ σ' : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {K : Torus d → Torus d → ℝ}
    {δ0 : ℝ} (hδ0 : 0 < δ0) (hB : 0 ≤ B) (hK : ConormalL σ b m B K)
    (hvan : ∀ X z : Euc d, z ≠ 0 → ‖z‖ < δ0 → toChart K (X, z) = 0) :
    ConormalL σ' b m (px4b_Cvan σ b m δ0 * B) K where
  smooth := hK.smooth
  near := by
    intro a c hac X z hz hzr
    have hC1 := px4b_Cvan_ge_one σ b m hδ0
    have hw : 0 ≤ ‖z‖ ^ (-(σ' + (c : ℝ))) * (1 + |Real.log ‖z‖|) ^ b c :=
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
    have hCB : 0 ≤ px4b_Cvan σ b m δ0 * B := mul_nonneg (by linarith) hB
    by_cases hr : ‖z‖ < δ0
    · have hU : {z' : Euc d | z' ≠ 0 ∧ ‖z'‖ < δ0} ∈ 𝓝 z := by
        refine (isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hz, hr⟩
      have h0 : mixedDeriv a c (toChart K) X z = 0 :=
        px4b_mixedDeriv_zero_of_eq a c X z (U := {z' : Euc d | z' ≠ 0 ∧ ‖z'‖ < δ0}) hU
          (fun X' z' hz' => hvan X' z' hz'.1 hz'.2)
      have h00 : ‖mixedDeriv a c (toChart K) X z‖ = 0 := by
        rw [h0]
        exact norm_zero (E := ContinuousMultilinearMap ℝ (fun _ : Fin a => Euc d)
          (ContinuousMultilinearMap ℝ (fun _ : Fin c => Euc d) ℝ))
      rw [h00]
      positivity
    · push Not at hr
      have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hr1 : ‖z‖ ≤ 1 := by unfold r0 at hzr; linarith
      refine (hK.near a c hac X z hz hzr).trans ?_
      have hc : c ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
      have hterm : (1 + (δ0 ^ (-(σ + (c : ℝ))) + 1) * (1 + |Real.log δ0|) ^ b c) ≤
          px4b_Cvan σ b m δ0 := by
        unfold px4b_Cvan
        exact Finset.single_le_sum (f := fun c : ℕ => (1 + (δ0 ^ (-(σ + (c : ℝ))) + 1) *
          (1 + |Real.log δ0|) ^ b c)) (fun c _ => by positivity) hc
      have hpow : ‖z‖ ^ (-(σ + (c : ℝ))) ≤ δ0 ^ (-(σ + (c : ℝ))) + 1 := by
        by_cases he : 0 ≤ σ + (c : ℝ)
        · have := Real.rpow_le_rpow_of_nonpos hδ0 hr (by linarith : -(σ + (c : ℝ)) ≤ 0)
          linarith
        · have := Real.rpow_le_one hr0.le hr1 (by linarith : 0 ≤ -(σ + (c : ℝ)))
          have : 0 ≤ δ0 ^ (-(σ + (c : ℝ))) := Real.rpow_nonneg hδ0.le _
          linarith
      have hlog : 1 + |Real.log ‖z‖| ≤ 1 + |Real.log δ0| := by
        have h1 : Real.log δ0 ≤ Real.log ‖z‖ := Real.log_le_log hδ0 hr
        have h2 : Real.log ‖z‖ ≤ 0 := Real.log_nonpos hr0.le hr1
        rw [abs_of_nonpos h2, abs_of_nonpos (by linarith)]
        linarith
      have hL : (1 + |Real.log ‖z‖|) ^ b c ≤ (1 + |Real.log δ0|) ^ b c :=
        pow_le_pow_left₀ (by positivity) hlog _
      have hmain : 1 + ‖z‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖z‖|) ^ b c ≤ px4b_Cvan σ b m δ0 := by
        refine le_trans ?_ hterm
        have : ‖z‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖z‖|) ^ b c ≤
            (δ0 ^ (-(σ + (c : ℝ))) + 1) * (1 + |Real.log δ0|) ^ b c :=
          mul_le_mul hpow hL (by positivity) (by positivity)
        linarith
      calc B * (1 + ‖z‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖z‖|) ^ b c) ≤
            B * px4b_Cvan σ b m δ0 := mul_le_mul_of_nonneg_left hmain hB
        _ ≤ px4b_Cvan σ b m δ0 * B * (1 + ‖z‖ ^ (-(σ' + (c : ℝ))) * (1 + |Real.log ‖z‖|) ^ b c) := by
            nlinarith
  far := by
    intro k hk p hp hr
    have hC1 := px4b_Cvan_ge_one σ b m hδ0
    refine (hK.far k hk p hp hr).trans ?_
    nlinarith

/-- Relaxing the order (a gain `σ₂ - σ₁ > 0` absorbs every power of the logarithm). -/
theorem px4b_conormal_relax {σ1 σ2 : ℝ} (b1 b2 : ℕ → ℕ) (m : ℕ) (h : σ1 < σ2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (B : ℝ) (K : Torus d → Torus d → ℝ), 0 ≤ B →
      ConormalL σ1 b1 m B K → ConormalL σ2 b2 m (C * B) K := by
  have hε : 0 < σ2 - σ1 := by linarith
  have hlp : ∀ c : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      (1 + |Real.log t|) ^ (b1 c) ≤ C * t ^ (-(σ2 - σ1)) := fun c =>
    log_pow_le (b1 c) hε le_rfl
  choose Cc hCc0 hCc using hlp
  refine ⟨1 + ∑ c ∈ Finset.range (m + 1), Cc c, ?_, fun B K hB hK => ?_⟩
  · have : 0 ≤ ∑ c ∈ Finset.range (m + 1), Cc c := Finset.sum_nonneg fun c _ => hCc0 c
    linarith
  have hS : 0 ≤ ∑ c ∈ Finset.range (m + 1), Cc c := Finset.sum_nonneg fun c _ => hCc0 c
  refine ⟨hK.smooth, ?_, ?_⟩
  · intro a c hac X z hz hzr
    have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hr1 : ‖z‖ ≤ 1 := by unfold r0 at hzr; linarith
    refine (hK.near a c hac X z hz hzr).trans ?_
    have hc : c ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    have hCle : Cc c ≤ ∑ c ∈ Finset.range (m + 1), Cc c :=
      Finset.single_le_sum (f := Cc) (fun c _ => hCc0 c) hc
    set w : ℝ := ‖z‖ ^ (-(σ2 + (c : ℝ))) with hw
    have hw0 : 0 ≤ w := Real.rpow_nonneg hr0.le _
    have hL2 : 1 ≤ (1 + |Real.log ‖z‖|) ^ b2 c :=
      one_le_pow₀ (by linarith [abs_nonneg (Real.log ‖z‖)])
    have h1 : ‖z‖ ^ (-(σ1 + (c : ℝ))) * (1 + |Real.log ‖z‖|) ^ b1 c ≤ Cc c * w := by
      have := mul_le_mul_of_nonneg_left (hCc c ‖z‖ hr0 hr1) (Real.rpow_nonneg hr0.le (-(σ1 + (c : ℝ))))
      refine this.trans (le_of_eq ?_)
      rw [hw, ← mul_assoc, mul_comm (‖z‖ ^ (-(σ1 + (c : ℝ)))) (Cc c), mul_assoc,
        ← Real.rpow_add hr0]
      congr 2
      ring
    have h2 : Cc c * w ≤ (∑ c ∈ Finset.range (m + 1), Cc c) * (w * (1 + |Real.log ‖z‖|) ^ b2 c) := by
      have := mul_le_mul hCle (le_mul_of_one_le_right hw0 hL2) hw0 hS
      exact this
    have hwL : 0 ≤ w * (1 + |Real.log ‖z‖|) ^ b2 c := mul_nonneg hw0 (by positivity)
    have : B * (1 + ‖z‖ ^ (-(σ1 + (c : ℝ))) * (1 + |Real.log ‖z‖|) ^ b1 c) ≤
        (1 + ∑ c ∈ Finset.range (m + 1), Cc c) * B * (1 + w * (1 + |Real.log ‖z‖|) ^ b2 c) := by
      nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hB]
    exact this
  · intro k hk p hp hr
    refine (hK.far k hk p hp hr).trans ?_
    nlinarith

end HRS.Parx
end
