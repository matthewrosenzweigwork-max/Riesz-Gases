import HRS.MS.Fp81S21WeightedGen3
import HRS.MS.WhoTie

/-!
# S2.1(iii), packet 32b B3: weighted local estimate

This file develops the local differential estimate for the actual local
operator of `generatorW`. The output weight is one power larger because the
drift jets have linear growth.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The sum of operator derivative norms through order `r`. -/
def fp81s21_b3_jetSum {d : ℕ} (r : ℕ) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ k ∈ Finset.range (r + 1), ‖iteratedFDeriv ℝ k f x‖

/-- The local operator's derivative jets are controlled by the input jets with
one power of spatial growth. -/
theorem fp81s21_b3_local_jet_bound (p : Parameters) (B : ℝ) (hB : 0 ≤ B)
    (b : Euc p.d → Euc p.d) (f : Euc p.d → ℝ)
    (hb : ContDiff ℝ (2 * p.d + 6) b)
    (hjet : ∀ j ≤ 2 * p.d + 6, ∀ x,
      ‖iteratedFDeriv ℝ j b x‖ ≤ B * jbracket x)
    (hf : ContDiff ℝ (2 * p.d + 8) f) :
    ∀ j ≤ 2 * p.d + 6, ∀ x,
      ‖iteratedFDeriv ℝ j (fp81s21_b3_local p b f) x‖ ≤
        (|fp81s21_b3_viscosity p| * (p.d : ℝ) +
          B * ((2 * p.d + 7 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * p.d + 6)) *
        jbracket x * fp81s21_b3_jetSum (2 * p.d + 8) f x := by
  let q : ℕ := 2 * p.d + 6
  let S : Euc p.d → ℝ := fp81s21_b3_jetSum (q + 2) f
  let C : ℝ := |fp81s21_b3_viscosity p| * (p.d : ℝ) +
    B * ((q + 1 : ℕ) : ℝ) * (2 : ℝ) ^ q
  have hqf : ContDiff ℝ ((q + 2 : ℕ) : WithTop ℕ∞) f := by
    change ContDiff ℝ (2 * p.d + 8) f
    exact hf
  have hbq : ContDiff ℝ (q : WithTop ℕ∞) b := by simpa [q] using hb
  have hfd : ContDiff ℝ (2 * p.d + 7) (fderiv ℝ f) := by
    exact hf.fderiv_right (m := (2 * p.d + 7 : ℕ)) (by norm_cast)
  have hfdq : ContDiff ℝ (q : WithTop ℕ∞) (fderiv ℝ f) :=
    hfd.of_le (by
      have hn : q ≤ 2 * p.d + 7 := by dsimp [q]; omega
      exact_mod_cast hn)
  have hT : ContDiff ℝ (q : WithTop ℕ∞)
      (fun x => fderiv ℝ f x (b x)) := hfdq.clm_apply hbq
  have hT_eq : (fun x => fderiv ℝ f x (b x)) =
      fun x => inner ℝ (b x) (gradient f x) := by
    funext x
    symm
    rw [real_inner_comm]
    exact inner_gradient_left
  have hD : ContDiff ℝ (q : WithTop ℕ∞)
      (fun x => fp81s21_b3_viscosity p * Laplacian.laplacian f x) := by
    have hLap := HRS.MS.Who.who_lap_iter (i := q) hqf
    exact contDiff_const.mul hLap.1
  have hlocal : ContDiff ℝ (q : WithTop ℕ∞) (fp81s21_b3_local p b f) := by
    have h := fp81s21_b3_local_contDiff p b f hb hf
    simpa [q] using h
  have hsumEq : fp81s21_b3_local p b f =
      (fun x => fp81s21_b3_viscosity p * Laplacian.laplacian f x +
        fderiv ℝ f x (b x)) := by
    funext x
    simp only [fp81s21_b3_local]
    congr 1
    exact (congrFun hT_eq x).symm
  have hSnonneg : ∀ x, 0 ≤ S x := by
    intro x
    dsimp [S, fp81s21_b3_jetSum]
    exact Finset.sum_nonneg fun k _ => norm_nonneg (iteratedFDeriv ℝ k f x)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have htransport : ∀ j ≤ q, ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ f x (b x)) x‖ ≤
        B * jbracket x * (((j + 1 : ℕ) : ℝ) * (2 : ℝ) ^ q * S x) := by
    intro j hj x
    have hclm := norm_iteratedFDeriv_clm_apply
      (N := (q : WithTop ℕ∞)) hfdq hbq x (by exact_mod_cast hj)
    calc ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ f x (b x)) x‖
        ≤ ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) *
            ‖iteratedFDeriv ℝ l (fderiv ℝ f) x‖ *
            ‖iteratedFDeriv ℝ (j - l) b x‖ := hclm
      _ ≤ ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) *
            ‖iteratedFDeriv ℝ (l + 1) f x‖ * (B * jbracket x) := by
          refine Finset.sum_le_sum fun l hl => ?_
          have hl' : l ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
          have hnorm : ‖iteratedFDeriv ℝ l (fderiv ℝ f) x‖ =
              ‖iteratedFDeriv ℝ (l + 1) f x‖ := norm_iteratedFDeriv_fderiv
          have hbnd := hjet (j - l) (by omega) x
          have hleft : (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fderiv ℝ f) x‖ ≤
              (j.choose l : ℝ) * ‖iteratedFDeriv ℝ (l + 1) f x‖ := by rw [hnorm]
          exact mul_le_mul hleft hbnd (norm_nonneg _) (by positivity)
      _ = B * jbracket x *
            ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) *
              ‖iteratedFDeriv ℝ (l + 1) f x‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro l hl
          ring
      _ ≤ B * jbracket x * (((j + 1 : ℕ) : ℝ) * (2 : ℝ) ^ q * S x) := by
          have hsumle :
              ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) *
                ‖iteratedFDeriv ℝ (l + 1) f x‖ ≤
              ((j + 1 : ℕ) : ℝ) * (2 : ℝ) ^ q * S x := by
            calc _ ≤ ∑ l ∈ Finset.range (j + 1), (2 : ℝ) ^ q * S x := by
                  refine Finset.sum_le_sum fun l hl => ?_
                  have hl' : l ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
                  have hchooseN : j.choose l ≤ ∑ k ∈ Finset.range (j + 1), j.choose k :=
                    Finset.single_le_sum (f := fun k => j.choose k)
                      (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
                  have hchoose : (j.choose l : ℝ) ≤ (2 : ℝ) ^ q := by
                    calc (j.choose l : ℝ) ≤ (2 : ℝ) ^ j := by
                          have hchooseN' : j.choose l ≤ 2 ^ j := by
                            simpa [Nat.sum_range_choose] using hchooseN
                          exact_mod_cast hchooseN'
                      _ ≤ (2 : ℝ) ^ q := pow_le_pow_right₀ (by norm_num) hj
                  have hsingle : ‖iteratedFDeriv ℝ (l + 1) f x‖ ≤ S x := by
                    dsimp [S, fp81s21_b3_jetSum]
                    exact Finset.single_le_sum
                      (f := fun k => ‖iteratedFDeriv ℝ k f x‖)
                      (fun k hk => norm_nonneg (iteratedFDeriv ℝ k f x))
                      (Finset.mem_range.2 (by omega))
                  exact mul_le_mul hchoose hsingle (norm_nonneg _) (by positivity)
              _ = ((j + 1 : ℕ) : ℝ) * (2 : ℝ) ^ q * S x := by
                  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                  push_cast
                  ring
          exact mul_le_mul_of_nonneg_left hsumle
            (mul_nonneg hB (le_trans (by norm_num) (HRS.MS.Who.who_one_le_jb x)))
  intro j hj x
  have hjq : j ≤ q := by simpa [q] using hj
  have hsumD := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := j)
    (f := fun x => fp81s21_b3_viscosity p * Laplacian.laplacian f x)
    (g := fun x => fderiv ℝ f x (b x)) (x := x)
    ((hD.of_le (by exact_mod_cast hjq)).contDiffAt)
    ((hT.of_le (by exact_mod_cast hjq)).contDiffAt)
  have hlocalDeriv :
      iteratedFDeriv ℝ j (fp81s21_b3_local p b f) x =
        iteratedFDeriv ℝ j (fun x => fp81s21_b3_viscosity p * Laplacian.laplacian f x) x +
          iteratedFDeriv ℝ j (fun x => fderiv ℝ f x (b x)) x := by
    rw [hsumEq]
    change iteratedFDeriv ℝ j ((fun x => fp81s21_b3_viscosity p * Laplacian.laplacian f x) +
      (fun x => fderiv ℝ f x (b x))) x = _
    exact hsumD
  have hsum_norm :
      ‖iteratedFDeriv ℝ j (fp81s21_b3_local p b f) x‖ ≤
        |fp81s21_b3_viscosity p| *
            ‖iteratedFDeriv ℝ j (Laplacian.laplacian f) x‖ +
          ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ f x (b x)) x‖ := by
    rw [hlocalDeriv]
    calc _ ≤
          ‖iteratedFDeriv ℝ j (fun x => fp81s21_b3_viscosity p * Laplacian.laplacian f x) x‖ +
            ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ f x (b x)) x‖ := norm_add_le _ _
      _ = _ := by
        rw [HRS.MS.Who.who_iter_const_mul
          ((HRS.MS.Who.who_lap_iter (i := q) hqf).1.of_le (by exact_mod_cast hjq))
          (fp81s21_b3_viscosity p) x]
        simp only [norm_smul, Real.norm_eq_abs]
  have hlap : ‖iteratedFDeriv ℝ j (Laplacian.laplacian f) x‖ ≤
      (p.d : ℝ) * ‖iteratedFDeriv ℝ (j + 2) f x‖ := by
    obtain ⟨_, hbound⟩ := HRS.MS.Who.who_lap_iter
      (i := j) (hqf.of_le (by exact_mod_cast (show j + 2 ≤ q + 2 by omega)))
    exact hbound x
  have hdiffBound : |fp81s21_b3_viscosity p| *
        ‖iteratedFDeriv ℝ j (Laplacian.laplacian f) x‖ ≤
      |fp81s21_b3_viscosity p| * (p.d : ℝ) * jbracket x * S x := by
    have hsingle : ‖iteratedFDeriv ℝ (j + 2) f x‖ ≤ S x := by
      dsimp [S, fp81s21_b3_jetSum]
      exact Finset.single_le_sum
        (f := fun k => ‖iteratedFDeriv ℝ k f x‖)
        (fun k hk => norm_nonneg (iteratedFDeriv ℝ k f x))
        (Finset.mem_range.2 (by omega))
    have hjb : 1 ≤ jbracket x := HRS.MS.Who.who_one_le_jb x
    calc _ ≤ |fp81s21_b3_viscosity p| *
          ((p.d : ℝ) * ‖iteratedFDeriv ℝ (j + 2) f x‖) :=
            mul_le_mul_of_nonneg_left hlap (abs_nonneg _)
      _ ≤ _ := by
            have hd0 : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg _
            have hS := hSnonneg x
            have hsmall : ‖iteratedFDeriv ℝ (j + 2) f x‖ ≤ jbracket x * S x := by
              calc _ ≤ S x := hsingle
                _ = 1 * S x := by ring
                _ ≤ jbracket x * S x := mul_le_mul_of_nonneg_right hjb hS
            calc _ ≤ |fp81s21_b3_viscosity p| * ((p.d : ℝ) * (jbracket x * S x)) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsmall hd0) (abs_nonneg _)
              _ = _ := by ring
  have htranBound : ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ f x (b x)) x‖ ≤
      B * jbracket x * (((q + 1 : ℕ) : ℝ) * (2 : ℝ) ^ q * S x) := by
    have hqj : ((j + 1 : ℕ) : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ hjq)
    have hfactor : 0 ≤ B * jbracket x :=
      mul_nonneg hB (le_trans (by norm_num) (HRS.MS.Who.who_one_le_jb x))
    have htail : 0 ≤ (2 : ℝ) ^ q * S x :=
      mul_nonneg (pow_nonneg (by norm_num) q) (hSnonneg x)
    calc
      _ ≤ B * jbracket x * (((j + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ q * S x)) := by
        simpa [mul_assoc] using htransport j hjq x
      _ ≤ B * jbracket x * (((q + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ q * S x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqj htail) hfactor
      _ = _ := by ring
  have hfinal :
      ‖iteratedFDeriv ℝ j (fp81s21_b3_local p b f) x‖ ≤
        (|fp81s21_b3_viscosity p| * (p.d : ℝ) +
          B * ((q + 1 : ℕ) : ℝ) * (2 : ℝ) ^ q) * jbracket x * S x := by
    calc
      _ ≤ |fp81s21_b3_viscosity p| * ‖iteratedFDeriv ℝ j (Laplacian.laplacian f) x‖ +
          ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ f x (b x)) x‖ := hsum_norm
      _ ≤ |fp81s21_b3_viscosity p| * (p.d : ℝ) * jbracket x * S x +
          B * jbracket x * (((q + 1 : ℕ) : ℝ) * (2 : ℝ) ^ q * S x) :=
            add_le_add hdiffBound htranBound
      _ = _ := by ring

  have hqplus : ((q + 1 : ℕ) : ℝ) = ((2 * p.d + 7 : ℕ) : ℝ) := by
    exact_mod_cast (show q + 1 = 2 * p.d + 7 by dsimp [q])
  have hqplus2 : q + 2 = 2 * p.d + 8 := by
    dsimp [q]
  have hqexp : q = 2 * p.d + 6 := rfl
  simp only [S] at hfinal
  rw [hqplus, hqplus2, hqexp] at hfinal
  simpa only [fp81s21_b3_jetSum] using hfinal
/-- Multiplication by one bracket factor shifts the weighted square norm by one. -/
theorem fp81s21_b3_wSq_shift {d : ℕ} (P : ℝ) (G : Euc d → ℝ) :
    HRS.MS.Who.wSq (P + 1) (fun x => jbracket x * G x) = HRS.MS.Who.wSq P G := by
  unfold HRS.MS.Who.wSq
  refine lintegral_congr fun x => ?_
  apply congrArg ENNReal.ofReal
  simp only [HRS.MS.Who.wt]
  have hx : 0 < jbracket x := HRS.MS.Who.who_jb_pos x
  rw [mul_pow, ← Real.rpow_natCast]
  calc
    jbracket x ^ (-2 * (P + 1)) * (jbracket x ^ (2 : ℝ) * G x ^ 2) =
        (jbracket x ^ (-2 * (P + 1)) * jbracket x ^ (2 : ℝ)) * G x ^ 2 := by ring
    _ = jbracket x ^ (-2 * (P + 1) + 2) * G x ^ 2 := by
      rw [← Real.rpow_add hx]
    _ = jbracket x ^ (-2 * P) * G x ^ 2 := by
      rw [show -2 * (P + 1) + 2 = -2 * P by ring]

/-- The square norm of the finite sum of input jets is bounded by the input `Nsq`. -/
theorem fp81s21_b3_jetSum_wSq_le {d r : ℕ} {P : ℝ} {f : Euc d → ℝ}
    (hf : ContDiff ℝ r f) :
    HRS.MS.Who.wSq P (fp81s21_b3_jetSum r f) ≤
      ENNReal.ofReal ((r + 1 : ℕ) : ℝ) * HRS.MS.Who.Nsq r P f := by
  let G : ℕ → Euc d → ℝ := fun k x =>
    if k ≤ r then ‖iteratedFDeriv ℝ k f x‖ else 0
  have hGmeas : ∀ k, Measurable (G k) := by
    intro k
    by_cases hk : k ≤ r
    · simp only [G, if_pos hk]
      exact HRS.MS.Who.who_iter_meas hf hk
    · simp [G, hk]
  have hjetEq : fp81s21_b3_jetSum r f = fun x =>
      ∑ k ∈ Finset.range (r + 1), G k x := by
    funext x
    dsimp [fp81s21_b3_jetSum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk' : k ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    simp [G, hk']
  have hsum := HRS.MS.Who.who_wSq_sum_le (d := d)
    (S := Finset.range (r + 1)) (P := P) (G := G) hGmeas
  have hN : (∑ k ∈ Finset.range (r + 1), HRS.MS.Who.wSq P (G k)) =
      HRS.MS.Who.Nsq r P f := by
    unfold HRS.MS.Who.Nsq
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk' : k ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    simp [G, hk']
  calc HRS.MS.Who.wSq P (fp81s21_b3_jetSum r f)
      = HRS.MS.Who.wSq P (fun x => ∑ k ∈ Finset.range (r + 1), G k x) := by rw [hjetEq]
    _ ≤ ((Finset.range (r + 1)).card : ℝ≥0∞) *
        ∑ k ∈ Finset.range (r + 1), HRS.MS.Who.wSq P (G k) := hsum
    _ = ENNReal.ofReal ((r + 1 : ℕ) : ℝ) * HRS.MS.Who.Nsq r P f := by
      rw [Finset.card_range, hN, ENNReal.ofReal_natCast]

/-- The uniform operator-norm constant for the local weighted estimate. -/
def fp81s21_b3_local_NsqConstant (p : Parameters) (B : ℝ) : ℝ :=
  let q : ℕ := 2 * p.d + 6
  let r : ℕ := 2 * p.d + 8
  let C : ℝ := |fp81s21_b3_viscosity p| * (p.d : ℝ) +
    B * ((2 * p.d + 7 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * p.d + 6)
  ((q + 1 : ℕ) : ℝ) * (C ^ 2 * ((r + 1 : ℕ) : ℝ))

/-- Transfer the pointwise local jet estimate to the operator square norm. -/
theorem fp81s21_b3_local_Nsq_bound (p : Parameters) (B : ℝ) (hB : 0 ≤ B)
    (b : Euc p.d → Euc p.d) (f : Euc p.d → ℝ)
    (hb : ContDiff ℝ (2 * p.d + 6) b)
    (hjet : ∀ j ≤ 2 * p.d + 6, ∀ x,
      ‖iteratedFDeriv ℝ j b x‖ ≤ B * jbracket x)
    (hf : ContDiff ℝ (2 * p.d + 8) f) :
      HRS.MS.Who.Nsq (2 * p.d + 6) ((p.d : ℝ) + 3) (fp81s21_b3_local p b f) ≤
        ENNReal.ofReal (fp81s21_b3_local_NsqConstant p B) *
          HRS.MS.Who.Nsq (2 * p.d + 8) ((p.d : ℝ) + 2) f := by
  let q : ℕ := 2 * p.d + 6
  let r : ℕ := 2 * p.d + 8
  let P : ℝ := (p.d : ℝ) + 2
  let C : ℝ := |fp81s21_b3_viscosity p| * (p.d : ℝ) +
    B * ((2 * p.d + 7 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * p.d + 6)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hPshift : P + 1 = (p.d : ℝ) + 3 := by dsimp [P]; ring
  have hjetOut := fp81s21_b3_local_jet_bound p B hB b f hb hjet hf
  have hper : ∀ j ≤ q, HRS.MS.Who.wSq ((p.d : ℝ) + 3)
      (fun x => ‖iteratedFDeriv ℝ j (fp81s21_b3_local p b f) x‖) ≤
        ENNReal.ofReal (C ^ 2 * ((r + 1 : ℕ) : ℝ)) *
          HRS.MS.Who.Nsq r P f := by
    intro j hj
    have hj' : j ≤ 2 * p.d + 6 := by simpa [q] using hj
    calc HRS.MS.Who.wSq ((p.d : ℝ) + 3)
          (fun x => ‖iteratedFDeriv ℝ j (fp81s21_b3_local p b f) x‖)
        ≤ HRS.MS.Who.wSq (P + 1)
            (fun x => C * (jbracket x * fp81s21_b3_jetSum r f x)) := by
              rw [← hPshift]
              apply HRS.MS.Who.who_wSq_mono
              intro x
              have hpoint := hjetOut j hj' x
              have hpoint' : ‖iteratedFDeriv ℝ j (fp81s21_b3_local p b f) x‖ ≤
                  C * (jbracket x * fp81s21_b3_jetSum r f x) := by
                calc _ ≤ C * jbracket x * fp81s21_b3_jetSum r f x := by
                       simpa [C, r, fp81s21_b3_jetSum, Nat.add_assoc, Nat.add_comm,
                         Nat.add_left_comm] using hpoint
                  _ = _ := by ring
              exact pow_le_pow_left₀ (norm_nonneg _) hpoint' 2
        _ = ENNReal.ofReal (C ^ 2) *
            HRS.MS.Who.wSq (P + 1) (fun x => jbracket x * fp81s21_b3_jetSum r f x) := by
              rw [HRS.MS.Who.who_wSq_smul]
        _ = ENNReal.ofReal (C ^ 2) *
            HRS.MS.Who.wSq P (fp81s21_b3_jetSum r f) := by
              rw [fp81s21_b3_wSq_shift]
        _ ≤ ENNReal.ofReal (C ^ 2) *
            (ENNReal.ofReal ((r + 1 : ℕ) : ℝ) * HRS.MS.Who.Nsq r P f) := by
              exact mul_le_mul' le_rfl (fp81s21_b3_jetSum_wSq_le hf)
        _ = ENNReal.ofReal (C ^ 2 * ((r + 1 : ℕ) : ℝ)) *
            HRS.MS.Who.Nsq r P f := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hsum : HRS.MS.Who.Nsq q ((p.d : ℝ) + 3)
        (fp81s21_b3_local p b f) ≤
      ENNReal.ofReal (((q + 1 : ℕ) : ℝ) * (C ^ 2 * ((r + 1 : ℕ) : ℝ))) *
        HRS.MS.Who.Nsq r P f := by
    unfold HRS.MS.Who.Nsq
    calc ∑ j ∈ Finset.range (q + 1),
          HRS.MS.Who.wSq ((p.d : ℝ) + 3)
            (fun x => ‖iteratedFDeriv ℝ j (fp81s21_b3_local p b f) x‖)
        ≤ ∑ j ∈ Finset.range (q + 1),
            ENNReal.ofReal (C ^ 2 * ((r + 1 : ℕ) : ℝ)) * HRS.MS.Who.Nsq r P f := by
              refine Finset.sum_le_sum fun j hj => ?_
              exact hper j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
      _ = ENNReal.ofReal (((q + 1 : ℕ) : ℝ) * (C ^ 2 * ((r + 1 : ℕ) : ℝ))) *
            HRS.MS.Who.Nsq r P f := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                ← ENNReal.ofReal_natCast, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  simpa [q, r, P, C, fp81s21_b3_local_NsqConstant] using hsum

/-- Convert an operator-norm estimate into the ordered-tuple weighted norm,
allowing different input and output weights. -/
theorem fp81s21_b3_Nsq_to_E {d r r' : ℕ} {Pout Pin K : ℝ} (hd : 1 ≤ d)
    (hK : 0 ≤ K) {u f : Euc d → ℝ} (hf : ContDiff ℝ r' f)
    (h : HRS.MS.Who.Nsq r Pout u ≤ ENNReal.ofReal K * HRS.MS.Who.Nsq r' Pin f) :
    weightedSobolevE r Pout u ≤
      ENNReal.ofReal (Real.sqrt (K * (d : ℝ) ^ (r + r'))) * weightedSobolevE r' Pin f := by
  rw [HRS.MS.Who.who_E_eq, HRS.MS.Who.who_E_eq,
    ← HRS.MS.Who.who_E_mul _ (by positivity)]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  calc HRS.MS.Who.Esq r Pout u ≤ ((d : ℝ≥0∞) ^ r) * HRS.MS.Who.Nsq r Pout u :=
        HRS.MS.Who.who_Esq_le hd
    _ ≤ ((d : ℝ≥0∞) ^ r) *
          (ENNReal.ofReal K * (((d : ℝ≥0∞) ^ r') * HRS.MS.Who.Esq r' Pin f)) :=
        mul_le_mul' le_rfl (h.trans (mul_le_mul' le_rfl (HRS.MS.Who.who_Nsq_le hd hf)))
    _ = ENNReal.ofReal (K * (d : ℝ) ^ (r + r')) * HRS.MS.Who.Esq r' Pin f := by
        rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_pow (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, pow_add]
        ring

/-- The local generator maps one extra polynomial weight into two extra
input derivatives, with a uniform weighted Sobolev bound. -/
theorem fp81s21_b3_local_estimate (p : Parameters) (B : ℝ) (hB : 0 ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ b : Euc p.d → Euc p.d, ContDiff ℝ (2 * p.d + 6) b →
        (∀ j ≤ 2 * p.d + 6, ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ B * jbracket x) →
        ∀ f : Euc p.d → ℝ,
          IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f →
          IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 3)
            (fp81s21_b3_local p b f) ∧
          weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 3)
              (fp81s21_b3_local p b f) ≤
            ENNReal.ofReal A * weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2) f := by
  let q : ℕ := 2 * p.d + 6
  let r : ℕ := 2 * p.d + 8
  let K : ℝ := fp81s21_b3_local_NsqConstant p B
  let A : ℝ := Real.sqrt (K * (p.d : ℝ) ^ (q + r))
  have hK : 0 ≤ K := by
    dsimp [K, fp81s21_b3_local_NsqConstant]
    positivity
  have hA : 0 ≤ A := by dsimp [A]; exact Real.sqrt_nonneg _
  refine ⟨A, hA, ?_⟩
  intro b hb hjet f hf
  have hN := fp81s21_b3_local_Nsq_bound p B hB b f hb hjet hf.1
  have hE := fp81s21_b3_Nsq_to_E (Nat.le_trans (by decide) p.hd) hK hf.1 hN
  have hbound : weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 3)
      (fp81s21_b3_local p b f) ≤
        ENNReal.ofReal A * weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2) f := by
    simpa [A, K, q, r] using hE
  have hfinite : weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 3)
      (fp81s21_b3_local p b f) < ⊤ :=
    lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2)
  have hcd := fp81s21_b3_local_contDiff p b f hb hf.1
  exact ⟨⟨hcd, hfinite⟩, hbound⟩

#print axioms fp81s21_b3_local_jet_bound
#print axioms fp81s21_b3_wSq_shift
#print axioms fp81s21_b3_jetSum_wSq_le
#print axioms fp81s21_b3_local_Nsq_bound
#print axioms fp81s21_b3_Nsq_to_E
#print axioms fp81s21_b3_local_estimate

end HRS.Fp81.S21
