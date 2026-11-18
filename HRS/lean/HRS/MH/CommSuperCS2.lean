import HRS.MH.CommSuperDefs

/-!
# CS2: periodic Lipschitz cutoff of a Euclidean Lipschitz field (packet `periodic_cutoff`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MH.CommSuper

variable {d N : ℕ} {s : ℝ}

/-- The cutoff `χ(z) = min 1 (max 0 (2 - 16 tdist z 0))`. -/
def cs2_chi (z : Torus d) : ℝ := min 1 (max 0 (2 - 16 * KernelGrad.tdist z 0))

/-- The periodic field `w z = χ(z) (v (centeredRep z) - v 0)`. -/
def cs2_W (v : Euc d → Euc d) (z : Torus d) : Euc d :=
  cs2_chi z • (v (KernelGrad.centeredRep z) - v 0)

theorem cs2_mk_sub (x y : Euc d) : Torus.mk (x - y) = Torus.mk x - Torus.mk y := by
  funext i
  simp [Torus.mk]

theorem cs2_tdist_symm (a b : Torus d) : KernelGrad.tdist b a = KernelGrad.tdist a b := by
  have h := KernelGrad.tdist_neg (a - b)
  rw [neg_sub] at h
  rw [HRS.Commutator.EnergyAux.tdist_def b a, HRS.Commutator.EnergyAux.tdist_def a b]
  exact h

theorem cs2_abs_tdist_sub (a b : Torus d) :
    |KernelGrad.tdist a 0 - KernelGrad.tdist b 0| ≤ KernelGrad.tdist a b := by
  have h1 := HRS.Commutator.Renorm.tdist_tri a b 0
  have h2 := HRS.Commutator.Renorm.tdist_tri b a 0
  rw [cs2_tdist_symm a b] at h2
  rw [abs_le]
  constructor <;> linarith

theorem cs2_chi_nonneg (z : Torus d) : 0 ≤ cs2_chi z ∧ cs2_chi z ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem cs2_chi_le_one (z : Torus d) : cs2_chi z ≤ 1 := min_le_left _ _

theorem cs2_chi_pos_imp {z : Torus d} (h : 0 < cs2_chi z) : KernelGrad.tdist z 0 < 1 / 8 := by
  by_contra hc
  push_neg at hc
  have hM : 0 < max 0 (2 - 16 * KernelGrad.tdist z 0) := lt_of_lt_of_le h (min_le_right _ _)
  have : max 0 (2 - 16 * KernelGrad.tdist z 0) ≤ 0 := max_le (le_refl 0) (by linarith)
  linarith

theorem cs2_chi_lip (a b : Torus d) : |cs2_chi a - cs2_chi b| ≤ 16 * KernelGrad.tdist a b := by
  have h := cs2_abs_tdist_sub a b
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  rw [abs_le]
  unfold cs2_chi
  constructor <;> simp only [min_def, max_def] <;> split_ifs <;> linarith

theorem cs2_chi_mul_le (z : Torus d) : cs2_chi z * KernelGrad.tdist z 0 ≤ 1 / 8 := by
  rcases (cs2_chi_nonneg z).1.eq_or_lt with h | h
  · rw [← h, zero_mul]; norm_num
  · have hp := cs2_chi_pos_imp h
    calc cs2_chi z * KernelGrad.tdist z 0 ≤ 1 * KernelGrad.tdist z 0 :=
          mul_le_mul_of_nonneg_right (cs2_chi_le_one z) (KernelGrad.tdist_nonneg _ _)
      _ ≤ 1 / 8 := by linarith

theorem cs2_f_bound {v : Euc d → Euc d} {K : ℝ≥0} (hv : LipschitzWith K v) (z : Torus d) :
    ‖v (KernelGrad.centeredRep z) - v 0‖ ≤ (K : ℝ) * KernelGrad.tdist z 0 := by
  have h := hv.dist_le_mul (KernelGrad.centeredRep z) 0
  rw [dist_zero_right, ← KernelGrad.tdist_zero_right, dist_eq_norm] at h
  exact h

theorem cs2_W_norm_le {v : Euc d → Euc d} {K : ℝ≥0} (hv : LipschitzWith K v) (z : Torus d) :
    ‖cs2_W v z‖ ≤ (K : ℝ) / 8 := by
  have hK : (0 : ℝ) ≤ K := K.2
  unfold cs2_W
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cs2_chi_nonneg z).1]
  calc cs2_chi z * ‖v (KernelGrad.centeredRep z) - v 0‖
      ≤ cs2_chi z * ((K : ℝ) * KernelGrad.tdist z 0) :=
        mul_le_mul_of_nonneg_left (cs2_f_bound hv z) (cs2_chi_nonneg z).1
    _ = (K : ℝ) * (cs2_chi z * KernelGrad.tdist z 0) := by ring
    _ ≤ (K : ℝ) * (1 / 8) := mul_le_mul_of_nonneg_left (cs2_chi_mul_le z) hK
    _ = (K : ℝ) / 8 := by ring

theorem cs2_mk_centered_eq (x : Euc d) (hx : ∀ i, |x.ofLp i| ≤ 1 / 16) :
    KernelGrad.centeredRep (Torus.mk x) = x := by
  ext i
  have h := congrFun (KernelGrad.mk_centeredRep (Torus.mk x)) i
  have h2 : (((KernelGrad.centeredRep (Torus.mk x)).ofLp i - x.ofLp i : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, sub_eq_zero]
    exact h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h2
  have hc := abs_le.mp (KernelGrad.abs_centeredRep_le (Torus.mk x) i)
  have hxi := abs_le.mp (hx i)
  simp only [zsmul_eq_mul, mul_one] at hn
  have hn1 : (n : ℝ) < 1 := by linarith [hc.1, hc.2, hxi.1, hxi.2]
  have hn2 : (-1 : ℝ) < n := by linarith [hc.1, hc.2, hxi.1, hxi.2]
  have hn0 : n = 0 := by
    have h1 : n < 1 := by exact_mod_cast hn1
    have h2' : -1 < n := by exact_mod_cast hn2
    omega
  rw [hn0] at hn
  simp only [Int.cast_zero] at hn
  linarith

theorem cs2_norm_centered_sub (a b : Torus d) (ha : KernelGrad.tdist a 0 < 1 / 8)
    (hb : KernelGrad.tdist b 0 < 1 / 8) :
    ‖KernelGrad.centeredRep a - KernelGrad.centeredRep b‖ = KernelGrad.tdist a b := by
  have ha' : ‖KernelGrad.centeredRep a‖ < 1 / 8 := by rwa [KernelGrad.tdist_zero_right] at ha
  have hb' : ‖KernelGrad.centeredRep b‖ < 1 / 8 := by rwa [KernelGrad.tdist_zero_right] at hb
  have hbound : ∀ i, |(KernelGrad.centeredRep a - KernelGrad.centeredRep b).ofLp i| ≤ 1 / 2 := by
    intro i
    have h1 := PiLp.norm_apply_le (KernelGrad.centeredRep a) i
    have h2 := PiLp.norm_apply_le (KernelGrad.centeredRep b) i
    rw [Real.norm_eq_abs] at h1 h2
    rw [PiLp.sub_apply, abs_le]
    obtain ⟨h1a, h1b⟩ := abs_le.mp (h1.trans ha'.le)
    obtain ⟨h2a, h2b⟩ := abs_le.mp (h2.trans hb'.le)
    constructor <;> linarith
  have hab : a - b = Torus.mk (KernelGrad.centeredRep a - KernelGrad.centeredRep b) := by
    rw [cs2_mk_sub, KernelGrad.mk_centeredRep, KernelGrad.mk_centeredRep]
  rw [HRS.Commutator.EnergyAux.tdist_def a b, hab, KernelGrad.tdist_mk hbound]

theorem cs2_key {v : Euc d → Euc d} {K : ℝ≥0} (hv : LipschitzWith K v) (a b : Torus d)
    (ha : 0 < cs2_chi a) (hδ : KernelGrad.tdist a b < 1 / 8) :
    ‖cs2_W v a - cs2_W v b‖ ≤ 3 * (K : ℝ) * KernelGrad.tdist a b := by
  have hK : (0 : ℝ) ≤ K := K.2
  have hδ0 := KernelGrad.tdist_nonneg a b
  have hpa := cs2_chi_pos_imp ha
  have hchi := cs2_chi_lip a b
  have hχa := cs2_chi_nonneg a
  rcases (cs2_chi_nonneg b).1.eq_or_lt with hb | hb
  · -- χ b = 0, so w b = 0
    have hWb : cs2_W v b = 0 := by unfold cs2_W; rw [← hb, zero_smul]
    rw [hWb, sub_zero]
    have hχa16 : cs2_chi a ≤ 16 * KernelGrad.tdist a b := by
      have := (abs_le.mp hchi).2
      rw [← hb] at this
      linarith
    have hFa := cs2_f_bound hv a
    unfold cs2_W
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hχa.1]
    have hKp : (K : ℝ) * KernelGrad.tdist a 0 ≤ (K : ℝ) * (1 / 8) :=
      mul_le_mul_of_nonneg_left hpa.le hK
    calc cs2_chi a * ‖v (KernelGrad.centeredRep a) - v 0‖
        ≤ cs2_chi a * ((K : ℝ) * KernelGrad.tdist a 0) :=
          mul_le_mul_of_nonneg_left hFa hχa.1
      _ ≤ (16 * KernelGrad.tdist a b) * ((K : ℝ) * (1 / 8)) :=
          mul_le_mul hχa16 hKp (mul_nonneg hK (KernelGrad.tdist_nonneg _ _)) (by linarith)
      _ ≤ 3 * (K : ℝ) * KernelGrad.tdist a b := by nlinarith [mul_nonneg hK hδ0]
  · -- χ b > 0, so both points are in the plateau-or-slope region
    have hpb := cs2_chi_pos_imp hb
    have hnorm := cs2_norm_centered_sub a b hpa hpb
    have hsplit : cs2_W v a - cs2_W v b =
        cs2_chi a • ((v (KernelGrad.centeredRep a) - v 0) - (v (KernelGrad.centeredRep b) - v 0)) +
          (cs2_chi a - cs2_chi b) • (v (KernelGrad.centeredRep b) - v 0) := by
      unfold cs2_W
      simp only [sub_smul, smul_sub]
      abel
    have hFab : ‖(v (KernelGrad.centeredRep a) - v 0) - (v (KernelGrad.centeredRep b) - v 0)‖
        ≤ (K : ℝ) * KernelGrad.tdist a b := by
      rw [sub_sub_sub_cancel_right]
      have h := hv.dist_le_mul (KernelGrad.centeredRep a) (KernelGrad.centeredRep b)
      simp only [dist_eq_norm] at h
      rw [hnorm] at h
      exact h
    have hFb := cs2_f_bound hv b
    have hpbK : ‖v (KernelGrad.centeredRep b) - v 0‖ ≤ (K : ℝ) / 8 :=
      hFb.trans (by have := mul_le_mul_of_nonneg_left hpb.le hK; linarith)
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hχa.1]
    have e1 : cs2_chi a * ‖(v (KernelGrad.centeredRep a) - v 0) - (v (KernelGrad.centeredRep b) - v 0)‖
        ≤ (K : ℝ) * KernelGrad.tdist a b := by
      calc _ ≤ 1 * ‖(v (KernelGrad.centeredRep a) - v 0) - (v (KernelGrad.centeredRep b) - v 0)‖ :=
            mul_le_mul_of_nonneg_right (cs2_chi_le_one a) (norm_nonneg _)
        _ = _ := one_mul _
        _ ≤ _ := hFab
    have e2 : |cs2_chi a - cs2_chi b| * ‖v (KernelGrad.centeredRep b) - v 0‖
        ≤ (16 * KernelGrad.tdist a b) * ((K : ℝ) / 8) :=
      mul_le_mul hchi hpbK (norm_nonneg _) (mul_nonneg (by norm_num) hδ0)
    nlinarith [mul_nonneg hK hδ0]

theorem periodic_cutoff_proof (v : Euc d → Euc d) (K : ℝ≥0) (hv : LipschitzWith K v) :
    ∃ w : Torus d → Euc d, IsLipschitzVF (3 * (K : ℝ)) w ∧
      ∀ x : Euc d, ‖x‖ ≤ 1 / 16 → w (Torus.mk x) = v x - v 0 := by
  have hK : (0 : ℝ) ≤ K := K.2
  refine ⟨cs2_W v, ?_, ?_⟩
  · intro a b
    rcases lt_or_ge (KernelGrad.tdist a b) (1 / 8) with hδ | hδ
    · rcases (cs2_chi_nonneg a).1.eq_or_lt with ha | ha
      · rcases (cs2_chi_nonneg b).1.eq_or_lt with hb | hb
        · have hWa : cs2_W v a = 0 := by unfold cs2_W; rw [← ha, zero_smul]
          have hWb : cs2_W v b = 0 := by unfold cs2_W; rw [← hb, zero_smul]
          rw [hWa, hWb, sub_zero, norm_zero]
          exact mul_nonneg (mul_nonneg (by norm_num) hK) (KernelGrad.tdist_nonneg _ _)
        · have h := cs2_key hv b a hb (by rw [cs2_tdist_symm]; exact hδ)
          rw [norm_sub_rev, cs2_tdist_symm] at h
          exact h
      · exact cs2_key hv a b ha hδ
    · have h1 := cs2_W_norm_le hv a
      have h2 := cs2_W_norm_le hv b
      have h3 : 3 * (K : ℝ) * (1 / 8) ≤ 3 * (K : ℝ) * KernelGrad.tdist a b :=
        mul_le_mul_of_nonneg_left hδ (mul_nonneg (by norm_num) hK)
      calc ‖cs2_W v a - cs2_W v b‖ ≤ ‖cs2_W v a‖ + ‖cs2_W v b‖ := norm_sub_le _ _
        _ ≤ (K : ℝ) / 8 + (K : ℝ) / 8 := add_le_add h1 h2
        _ ≤ 3 * (K : ℝ) * KernelGrad.tdist a b := by linarith
  · intro x hx
    have hxi : ∀ i, |x.ofLp i| ≤ 1 / 16 := fun i => by
      have h := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at h
      linarith
    have hp : KernelGrad.tdist (Torus.mk x) 0 = ‖x‖ :=
      KernelGrad.tdist_mk (fun i => by linarith [hxi i])
    have hχ : cs2_chi (Torus.mk x) = 1 := by
      unfold cs2_chi
      rw [hp]
      exact min_eq_left (le_max_of_le_right (by linarith))
    unfold cs2_W
    rw [hχ, one_smul, cs2_mk_centered_eq x hxi]

end HRS.MH.CommSuper
