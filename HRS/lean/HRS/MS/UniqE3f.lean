import HRS.MS.UniqE3e

/-!
# E3 of `UniqPlan.md`, part 6: the transport term (T)

* `transRem d ε b P i := [η_ε*, ∂_i b_i] P + [η_ε*, b_i] ∂_i P` (sum of two commutators).
* `e3_trans_split`: `fpTrans b u (η_ε * P) = ∫ z_ε ∑_i ∂_i(b_i P) - ∑_i ∫ u · transRem i`.
* `e3_transport_identity`: for `P = ς z_ε`
  `2 (-fpTrans) + ∫ (b·∇ς) z_ε² = -∫ (div b) ς z_ε² + 2 ∑_i ∫ u · transRem i`.
* `e3_rem_i_bound`: `|∫ u · transRem i| ≤ ε Cb (½ M + ½ ∫_S P²) + ε Cb (½ M + ½ ∫_S (∂_i P)²)`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3

variable {d : ℕ}

/-- The commutator remainder `[η_ε*, ∂_i b_i] P + [η_ε*, b_i] ∂_i P`. -/
def transRem (d : ℕ) (ε : ℝ) (b : Euc d → Euc d) (P : Euc d → ℝ) (i : Fin d) (y : Euc d) : ℝ :=
  comm d ε (D1 i (fun y => b y i)) P y + comm d ε (fun y => b y i) (D1 i P) y

theorem e3_comm_continuous {ε : ℝ} (hε : 0 < ε) {a F : Euc d → ℝ} (ha : Continuous a)
    (hF : Continuous F) : Continuous (comm d ε a F) :=
  (e3_moll_continuous hε (ha.mul hF).locallyIntegrable).sub
    (ha.mul (e3_moll_continuous hε hF.locallyIntegrable))

theorem e3_comm_hasCompactSupport {ε : ℝ} (hε : 0 < ε) {a F : Euc d → ℝ}
    (hFc : HasCompactSupport F) : HasCompactSupport (comm d ε a F) :=
  (e3_moll_hasCompactSupport hε (hFc.mul_left (f := a))).sub
    ((e3_moll_hasCompactSupport hε hFc).mul_left (f := a))

theorem e3_trans_split {b : Euc d → Euc d} (hbs : ∀ i, ContDiff ℝ 2 (fun y => b y i)) {ε : ℝ}
    (hε : 0 < ε) {B : ℝ} {u : Euc d → ℝ} (hu : LocMass B u) {P : Euc d → ℝ}
    (hP : ContDiff ℝ 1 P) (hPc : HasCompactSupport P) :
    fpTrans b u (moll d ε P) =
      (∫ x, moll d ε u x * ∑ i, (D1 i (fun y => b y i) x * P x + b x i * D1 i P x)) -
        ∑ i, ∫ x, u x * transRem d ε b P i x := by
  have hb1 : ∀ i, ContDiff ℝ 1 (fun y => b y i) := fun i => (hbs i).of_le (by norm_num)
  have hDb : ∀ i, Continuous (D1 i (fun y => b y i)) := fun i => e3_continuous_D1 (hb1 i) i
  have hDP : ∀ i, Continuous (D1 i P) := fun i => e3_continuous_D1 hP i
  have hDPc : ∀ i, HasCompactSupport (D1 i P) := fun i => D1_supp hPc i
  have hPcont := hP.continuous
  set G : Fin d → Euc d → ℝ := fun i x => D1 i (fun y => b y i) x * P x + b x i * D1 i P x
    with hG
  have hGc : ∀ i, Continuous (G i) := fun i =>
    ((hDb i).mul hPcont).add ((hb1 i).continuous.mul (hDP i))
  have hGcs : ∀ i, HasCompactSupport (G i) := fun i =>
    (hPc.mul_left (f := D1 i (fun y => b y i))).add ((hDPc i).mul_left (f := fun x => b x i))
  have hφ1 : ContDiff ℝ 1 (moll d ε P) :=
    (moll_contDiff hε hPcont.locallyIntegrable).of_le (by norm_num)
  have hA : ∀ i x, fderiv ℝ (fun y => b y i * moll d ε P y) x (EuclideanSpace.single i 1) =
      moll d ε (G i) x - transRem d ε b P i x := by
    intro i x
    have h1 : fderiv ℝ (fun y => b y i * moll d ε P y) x (EuclideanSpace.single i 1) =
        D1 i (fun y => b y i * moll d ε P y) x := rfl
    rw [h1, e3_D1_mul ((hb1 i).differentiable (by simp)) (hφ1.differentiable (by simp)),
      e3_D1_moll hε hP hPc i]
    have hadd := e3_moll_add hε (a := fun y => D1 i (fun y => b y i) y * P y)
      (b := fun y => b y i * D1 i P y) (((hDb i).mul hPcont).locallyIntegrable)
      (((hb1 i).continuous.mul (hDP i)).locallyIntegrable) x
    simp only [transRem, UniqM3.comm, hG]
    rw [hadd]
    ring
  have hRem_c : ∀ i, Continuous (transRem d ε b P i) := fun i =>
    (e3_comm_continuous hε (hDb i) hPcont).add (e3_comm_continuous hε (hb1 i).continuous (hDP i))
  have hRem_cs : ∀ i, HasCompactSupport (transRem d ε b P i) := fun i =>
    (e3_comm_hasCompactSupport hε hPc).add (e3_comm_hasCompactSupport hε (hDPc i))
  have hmG_c : ∀ i, Continuous (moll d ε (G i)) := fun i =>
    e3_moll_continuous hε (hGc i).locallyIntegrable
  have hmG_cs : ∀ i, HasCompactSupport (moll d ε (G i)) := fun i =>
    e3_moll_hasCompactSupport hε (hGcs i)
  have hli := hu.locallyIntegrable
  unfold fpTrans
  simp_rw [hA]
  have hint : ∀ i, Integrable (fun x => u x * (moll d ε (G i) x - transRem d ε b P i x)) volume :=
    fun i => e3_integrable_mul hli ((hmG_c i).sub (hRem_c i)) ((hmG_cs i).sub (hRem_cs i))
  rw [e3_integral_mul_sum hint]
  have hi : ∀ i, ∫ x, u x * (moll d ε (G i) x - transRem d ε b P i x) =
      (∫ x, moll d ε u x * G i x) - ∫ x, u x * transRem d ε b P i x := by
    intro i
    simp_rw [mul_sub]
    rw [integral_sub (e3_integrable_mul hli (hmG_c i) (hmG_cs i))
      (e3_integrable_mul hli (hRem_c i) (hRem_cs i)), e3_integral_mul_moll hε hu (hGc i) (hGcs i)]
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, e3_integral_mul_sum (fun i =>
    ((e3_moll_continuous hε hli).mul (hGc i)).integrable_of_hasCompactSupport ((hGcs i).mul_left))]

theorem e3_transport_identity {b : Euc d → Euc d} (hbs : ∀ i, ContDiff ℝ 2 (fun y => b y i))
    {ε : ℝ} (hε : 0 < ε) {B : ℝ} {u : Euc d → ℝ} (hu : LocMass B u) {ς : Euc d → ℝ}
    (hς : ContDiff ℝ 1 ς) (hςc : HasCompactSupport ς) :
    2 * (-fpTrans b u (moll d ε (fun x => ς x * moll d ε u x))) +
        ∫ x, (∑ i, b x i * D1 i ς x) * moll d ε u x ^ 2 =
      -(∫ x, (∑ i, D1 i (fun y => b y i) x) * ς x * moll d ε u x ^ 2) +
        2 * ∑ i, ∫ x, u x * transRem d ε b (fun x => ς x * moll d ε u x) i x := by
  have hb1 : ∀ i, ContDiff ℝ 1 (fun y => b y i) := fun i => (hbs i).of_le (by norm_num)
  have hz1 : ContDiff ℝ 1 (moll d ε u) :=
    (moll_contDiff hε hu.locallyIntegrable).of_le (by norm_num)
  have hsplit := e3_trans_split hbs hε hu (P := fun x => ς x * moll d ε u x) (hς.mul hz1)
    hςc.mul_right
  have hexact := e3_transport_exact b hb1 hς hςc hz1
  rw [hsplit]
  beta_reduce
  rw [hexact]
  -- split the integral on the right
  have hc := hz1.continuous
  have i1 : Integrable (fun x => (∑ i, D1 i (fun y => b y i) x) * ς x * moll d ε u x ^ 2) volume :=
    e3_integrable_cs hςc
      (((continuous_finsetSum _ fun i _ => e3_continuous_D1 (hb1 i) i).mul hς.continuous).mul
        (hc.pow 2)) (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have i2 : Integrable (fun x => (∑ i, b x i * D1 i ς x) * moll d ε u x ^ 2) volume :=
    e3_integrable_cs hςc
      ((continuous_finsetSum _ fun i _ => (hb1 i).continuous.mul (e3_continuous_D1 hς i)).mul
        (hc.pow 2)) (fun x hx => by
          have : ∑ i, b x i * D1 i ς x = 0 :=
            Finset.sum_eq_zero fun i _ => by simp [(e3_zero_off hx i).2]
          simp [this])
  have e : ∫ x, ((∑ i, D1 i (fun y => b y i) x) * ς x + ∑ i, b x i * D1 i ς x) *
        moll d ε u x ^ 2 =
      (∫ x, (∑ i, D1 i (fun y => b y i) x) * ς x * moll d ε u x ^ 2) +
        ∫ x, (∑ i, b x i * D1 i ς x) * moll d ε u x ^ 2 := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [e]
  ring

end HRS.MS.UniqE3
