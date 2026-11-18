import HRS.MS.SA12C16

/-!
# S.A.12(c), packet E7.04 (part 1): Cauchy-Schwarz and the period-`L` Young inequality

`sa12c_cs`: `(∫ a b)² ≤ ∫ a² ∫ b²` (discriminant argument).
`sa12c_young`: for a kernel `ρ` with `ρ² ∈ L¹(W)`, `W = (-L/2, L/2]^d`, and a continuous `L`-periodic `f`,
`∫_{Q_L} (∫_W ρ(z) f(x-z) dz)² dx ≤ (∫_W ρ²) (∫_{Q_L}|f|)²`  (unnormalised measure, constant `1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12c_cs {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : α → ℝ}
    (ha : Integrable (fun x => a x ^ 2) μ) (hb : Integrable (fun x => b x ^ 2) μ)
    (hab : Integrable (fun x => a x * b x) μ) :
    (∫ x, a x * b x ∂μ) ^ 2 ≤ (∫ x, a x ^ 2 ∂μ) * ∫ x, b x ^ 2 ∂μ := by
  have key : ∀ t : ℝ, 0 ≤ (∫ x, b x ^ 2 ∂μ) * (t * t) + (-2 * ∫ x, a x * b x ∂μ) * t + ∫ x, a x ^ 2 ∂μ := by
    intro t
    have h : 0 ≤ ∫ x, (a x - t * b x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have e : ∫ x, (a x - t * b x) ^ 2 ∂μ =
        ∫ x, ((a x ^ 2 - 2 * t * (a x * b x)) + t ^ 2 * b x ^ 2) ∂μ := by
      congr 1; funext x; ring
    rw [e] at h
    have hrewrite : (∫ x, (a x ^ 2 - 2 * t * (a x * b x)) + t ^ 2 * b x ^ 2 ∂μ) =
        (∫ x, a x ^ 2 ∂μ) - 2 * t * (∫ x, a x * b x ∂μ) +
        t ^ 2 * (∫ x, b x ^ 2 ∂μ) := by
      have h1 := integral_add (ha.sub (hab.const_mul (2 * t))) (hb.const_mul (t ^ 2))
      have h2 := integral_sub ha (hab.const_mul (2 * t))
      have h2' : (∫ x, ((fun x => a x ^ 2) - fun x => 2 * t * (a x * b x)) x ∂μ) =
          (∫ x, a x ^ 2 ∂μ) - (∫ x, 2 * t * (a x * b x) ∂μ) := by
        simpa only [Pi.sub_apply] using h2
      have h1' : (∫ x, (a x ^ 2 - 2 * t * (a x * b x)) + t ^ 2 * b x ^ 2 ∂μ) =
          (∫ x, ((fun x => a x ^ 2) - fun x => 2 * t * (a x * b x)) x ∂μ) +
          (∫ x, t ^ 2 * b x ^ 2 ∂μ) := by
        simpa only [Pi.sub_apply] using h1
      rw [h1', h2', integral_const_mul, integral_const_mul]
    rw [hrewrite] at h
    nlinarith [h]
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

/-- The half-open centred cell `(-L/2, L/2]^d`. -/
def sa12cWcell (d : ℕ) (L : ℝ) : Set (Euc d) := {z : Euc d | ∀ i, -(L / 2) < z i ∧ z i ≤ L / 2}

theorem sa12c_W_meas (L : ℝ) : MeasurableSet (sa12cWcell d L) := by
  have : sa12cWcell d L = ⋂ i : Fin d, ({z : Euc d | -(L / 2) < z i} ∩ {z : Euc d | z i ≤ L / 2}) := by
    ext z; simp [sa12cWcell]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  have hm : Measurable fun z : Euc d => z i := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable
  exact (measurableSet_lt measurable_const hm).inter (measurableSet_le hm measurable_const)

theorem sa12c_W_sub_cube (L : ℝ) : sa12cWcell d L ⊆ sa12cCube d L :=
  fun z hz i => abs_le.2 ⟨(hz i).1.le, (hz i).2⟩

theorem sa12c_W_fin {L : ℝ} (hL : 0 ≤ L) : volume (sa12cWcell d L) ≠ ⊤ :=
  ((measure_mono ((sa12c_W_sub_cube (d := d) L).trans (sa12c_cube_subset L hL))).trans_lt
    measure_closedBall_lt_top).ne

/-- Reflected shift of a periodic function over the cell `W`. -/
theorem sa12c_shift_W {L : ℝ} (hL : 0 < L) {φ : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (k : Fin d → ℤ), φ (x + L • latticePt k) = φ x) (x : Euc d) :
    ∫ z in sa12cWcell d L, φ (x - z) = ∫ y in periodBox d L, φ y := by
  set a : Euc d := x - (WithLp.toLp 2 fun _ : Fin d => L / 2) with ha
  set S : Set (Euc d) := {y : Euc d | ∀ i, a i ≤ y i ∧ y i < a i + L} with hS
  have h2 := ((volume : Measure (Euc d)).measurePreserving_sub_left x).setIntegral_preimage_emb
    (MeasurableEquiv.subLeft x).measurableEmbedding φ S
  have hpre : (fun z : Euc d => x - z) ⁻¹' S = sa12cWcell d L := by
    ext z
    simp only [hS, ha, sa12cWcell, Set.mem_preimage, Set.mem_ofPred_eq, PiLp.sub_apply]
    refine forall_congr' fun i => ?_
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have h3 := sa12c20_cell_shift L hL hper a
  rw [hpre] at h2
  rw [← h3]
  exact h2

theorem sa12c_young {L : ℝ} (hL : 0 < L) {ρ f : Euc d → ℝ}
    (hρm : AEStronglyMeasurable ρ (volume.restrict (sa12cWcell d L)))
    (hρ : IntegrableOn (fun z => ρ z ^ 2) (sa12cWcell d L))
    (hf : Continuous f) (hfp : ∀ (x : Euc d) (k : Fin d → ℤ), f (x + L • latticePt k) = f x) :
    ∫ x in periodBox d L, (∫ z in sa12cWcell d L, ρ z * f (x - z)) ^ 2 ≤
      (∫ z in sa12cWcell d L, ρ z ^ 2) * (∫ y in periodBox d L, |f y|) ^ 2 := by
  obtain ⟨B, hB⟩ := sa12v_bdd L hL f hf hfp
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hfb : ∀ y, |f y| ≤ B := fun y => by simpa [Real.norm_eq_abs] using hB y
  have hWm := sa12c_W_meas (d := d) L
  have hWfin := sa12c_W_fin (d := d) hL.le
  have hQm := sa12c20_box_meas (d := d) L
  set K : ℝ := ∫ y in periodBox d L, |f y| with hK
  have hK0 : 0 ≤ K := setIntegral_nonneg hQm fun y _ => abs_nonneg _
  have hfap : ∀ (x : Euc d) (k : Fin d → ℤ), |f (x + L • latticePt k)| = |f x| := fun x k => by rw [hfp]
  have hρ1 : IntegrableOn ρ (sa12cWcell d L) volume := by
    refine Integrable.mono' ((integrableOn_const (C := (1 : ℝ)) hWfin).add hρ) hρm
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    show |ρ z| ≤ 1 + ρ z ^ 2
    nlinarith [sq_abs (ρ z), abs_nonneg (ρ z), sq_nonneg (|ρ z| - 1)]
  have hfx : ∀ x : Euc d, Continuous fun z => f (x - z) := fun x =>
    hf.comp (continuous_const.sub continuous_id)
  -- pointwise Cauchy-Schwarz
  have hA : ∀ x : Euc d, (∫ z in sa12cWcell d L, ρ z * f (x - z)) ^ 2 ≤
      (∫ z in sa12cWcell d L, ρ z ^ 2 * |f (x - z)|) * K := by
    intro x
    have hfxm := (hfx x).aestronglyMeasurable (μ := volume.restrict (sa12cWcell d L))
    have hsq : Continuous fun z => Real.sqrt |f (x - z)| := ((hfx x).abs).sqrt
    have hsqb : ∀ z, Real.sqrt |f (x - z)| ≤ Real.sqrt B := fun z => Real.sqrt_le_sqrt (hfb _)
    have hab : ∀ z, (|ρ z| * Real.sqrt |f (x - z)|) * Real.sqrt |f (x - z)| = |ρ z| * |f (x - z)| := by
      intro z; rw [mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
    have ha2 : ∀ z, (|ρ z| * Real.sqrt |f (x - z)|) ^ 2 = ρ z ^ 2 * |f (x - z)| := by
      intro z; rw [mul_pow, sq_abs, Real.sq_sqrt (abs_nonneg _)]
    have hb2 : ∀ z, (Real.sqrt |f (x - z)|) ^ 2 = |f (x - z)| := fun z => Real.sq_sqrt (abs_nonneg _)
    have hint1 : IntegrableOn (fun z => ρ z ^ 2 * |f (x - z)|) (sa12cWcell d L) volume := by
      refine Integrable.mono' (hρ.const_mul B) ((hρm.pow 2).mul (hfxm.norm))
        (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _))]
      calc ρ z ^ 2 * |f (x - z)| ≤ ρ z ^ 2 * B := mul_le_mul_of_nonneg_left (hfb _) (sq_nonneg _)
        _ = B * ρ z ^ 2 := mul_comm _ _
    have hint2 : IntegrableOn (fun z => |f (x - z)|) (sa12cWcell d L) volume := by
      refine Integrable.mono' (integrableOn_const (C := B) hWfin) hfxm.norm (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_abs]; exact hfb _
    have hint3 : IntegrableOn (fun z => |ρ z| * |f (x - z)|) (sa12cWcell d L) volume := by
      refine Integrable.mono' (hρ1.norm.const_mul B) (hρm.norm.mul hfxm.norm) (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)), mul_comm]
      simpa only [Real.norm_eq_abs, mul_comm] using
        (mul_le_mul_of_nonneg_left (hfb (x - z)) (abs_nonneg (ρ z)))
    have hcs := sa12c_cs (μ := volume.restrict (sa12cWcell d L))
      (a := fun z => |ρ z| * Real.sqrt |f (x - z)|) (b := fun z => Real.sqrt |f (x - z)|)
      (by simp_rw [ha2]; exact hint1) (by simp_rw [hb2]; exact hint2) (by simp_rw [hab]; exact hint3)
    simp_rw [hab, ha2, hb2] at hcs
    have hshift : ∫ z in sa12cWcell d L, |f (x - z)| = K :=
      sa12c_shift_W hL (φ := fun y => |f y|) hfap x
    rw [hshift] at hcs
    have h1 : |∫ z in sa12cWcell d L, ρ z * f (x - z)| ≤ ∫ z in sa12cWcell d L, |ρ z| * |f (x - z)| := by
      refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
      congr 1; funext z; rw [abs_mul]
    calc (∫ z in sa12cWcell d L, ρ z * f (x - z)) ^ 2 = |∫ z in sa12cWcell d L, ρ z * f (x - z)| ^ 2 :=
          (sq_abs _).symm
      _ ≤ (∫ z in sa12cWcell d L, |ρ z| * |f (x - z)|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ _ := hcs
  -- Fubini
  have hprod : Integrable (fun p : Euc d × Euc d => ρ p.2 ^ 2 * |f (p.1 - p.2)|)
      ((volume.restrict (periodBox d L)).prod (volume.restrict (sa12cWcell d L))) := by
    haveI : IsFiniteMeasure (volume.restrict (periodBox d L)) := sa12v_box_fin L
    have hdom : Integrable (fun p : Euc d × Euc d => B * ρ p.2 ^ 2)
        ((volume.restrict (periodBox d L)).prod (volume.restrict (sa12cWcell d L))) :=
      (hρ.const_mul B).comp_snd (μ := volume.restrict (periodBox d L))
    refine Integrable.mono' hdom ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : AEStronglyMeasurable (fun p : Euc d × Euc d => ρ p.2 ^ 2)
          ((volume.restrict (periodBox d L)).prod (volume.restrict (sa12cWcell d L))) :=
        (hρm.pow 2).comp_snd
      have h2 : Continuous fun p : Euc d × Euc d => |f (p.1 - p.2)| :=
        (hf.comp (continuous_fst.sub continuous_snd)).abs
      exact h1.mul h2.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _))]
      calc ρ p.2 ^ 2 * |f (p.1 - p.2)| ≤ ρ p.2 ^ 2 * B := mul_le_mul_of_nonneg_left (hfb _) (sq_nonneg _)
        _ = B * ρ p.2 ^ 2 := mul_comm _ _
  have hswap := integral_integral_swap (f := fun x z => ρ z ^ 2 * |f (x - z)|) hprod
  have hinner : ∀ z : Euc d, ∫ x in periodBox d L, ρ z ^ 2 * |f (x - z)| = ρ z ^ 2 * K := by
    intro z
    rw [integral_const_mul]
    congr 1
    set S : Set (Euc d) := {y : Euc d | ∀ i, (-z) i ≤ y i ∧ y i < (-z) i + L} with hS
    have h2 := (measurePreserving_sub_right (volume : Measure (Euc d)) z).setIntegral_preimage_emb
      (MeasurableEquiv.subRight z).measurableEmbedding (fun y => |f y|) S
    have hpre : (fun x : Euc d => x - z) ⁻¹' S = periodBox d L := by
      ext x
      simp only [hS, periodBox, Set.mem_preimage, Set.mem_ofPred_eq, PiLp.sub_apply, PiLp.neg_apply]
      refine forall_congr' fun i => ?_
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    have h4 : ((fun x : Euc d => x - z) ⁻¹' S) = periodBox d L := hpre
    rw [h4] at h2
    rw [h2]
    exact sa12c20_cell_shift L hL (Φ := fun y => |f y|) hfap (-z)
  calc ∫ x in periodBox d L, (∫ z in sa12cWcell d L, ρ z * f (x - z)) ^ 2
      ≤ ∫ x in periodBox d L, (∫ z in sa12cWcell d L, ρ z ^ 2 * |f (x - z)|) * K :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
          (hprod.integral_prod_left.mul_const K) (Eventually.of_forall hA)
    _ = (∫ x in periodBox d L, ∫ z in sa12cWcell d L, ρ z ^ 2 * |f (x - z)|) * K :=
        integral_mul_const _ _
    _ = (∫ z in sa12cWcell d L, ∫ x in periodBox d L, ρ z ^ 2 * |f (x - z)|) * K := by rw [hswap]
    _ = (∫ z in sa12cWcell d L, ρ z ^ 2 * K) * K := by simp_rw [hinner]
    _ = (∫ z in sa12cWcell d L, ρ z ^ 2) * K ^ 2 := by rw [integral_mul_const]; ring

end HRS.MH.AdjointRd.Phase2SA12C
