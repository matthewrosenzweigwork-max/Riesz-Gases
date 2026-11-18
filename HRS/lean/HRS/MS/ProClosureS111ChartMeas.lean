import HRS.MS.S111K4J01D
import HRS.MS.FixEqP1Aux1
import HRS.MS.PoisSgAux1

/-!
Measurability of a weighted chart follows from its frozen isometry and
density fields. This proof is independent of how the chart is constructed.
Jointly measurable spatial jets give measurable weighted distances to
every compact smooth test. Those test images are dense in the separable
coefficient space, so the encoded family is strongly measurable.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.FixEq HRS.MS.S111K4J01

/-- Distances to a dense family determine measurability in a separable
metric target. The family of centers need not be countable. -/
theorem measurable_of_dist_dense_range {A Y J : Type*} [MeasurableSpace A]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (e : J → Y) (he : DenseRange e) (f : A → Y)
    (hf : ∀ j, Measurable (fun a => dist (f a) (e j))) : Measurable f := by
  let B : Set (Set Y) := {U | ∃ j : J, ∃ r : ℝ, U = Metric.ball (e j) r}
  have hB : TopologicalSpace.IsTopologicalBasis B := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨j, r, rfl⟩
      exact Metric.isOpen_ball
    · intro y U hy hU
      obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.1 hU y hy
      obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 he y (eps / 2) (by linarith)
      refine ⟨Metric.ball (e j) (eps / 2), ⟨j, eps / 2, rfl⟩, hj, ?_⟩
      intro z hz
      apply hball
      change dist z y < eps
      have ht := dist_triangle z (e j) y
      have hzy : dist z (e j) < eps / 2 := hz
      rw [dist_comm (e j) y] at ht
      linarith
  rw [(inferInstance : BorelSpace Y).measurable_eq, hB.borel_eq_generateFrom]
  refine measurable_generateFrom ?_
  rintro _ ⟨j, r, rfl⟩
  exact measurableSet_lt (hf j) measurable_const

variable {d r : ℕ} {Pw : ℝ}

theorem chart_derivative_le_cbNorm {f : Euc d → ℝ} (hf : MemCb r f)
    {j : ℕ} (hj : j ≤ r) (x : Euc d) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ cbNorm r f := by
  refine (le_ciSup (hf.2 j hj) x).trans ?_
  exact Finset.single_le_sum
    (f := fun l => ⨆ y, ‖iteratedFDeriv ℝ l f y‖)
    (fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)
    (Finset.mem_range.2 (by omega))

theorem chart_memCb_mono {k : ℕ} (hkr : k ≤ r) {f : Euc d → ℝ}
    (hf : MemCb r f) : MemCb k f :=
  ⟨hf.1.of_le (by exact_mod_cast hkr), fun j hj => hf.2 j (hj.trans hkr)⟩

theorem chart_memCb_sub {f g : Euc d → ℝ} (hf : MemCb r f) (hg : MemCb r g) :
    MemCb r (f - g) := by
  refine ⟨hf.1.sub hg.1, fun j hj => ?_⟩
  refine ⟨cbNorm r f + cbNorm r g, ?_⟩
  rintro _ ⟨x, rfl⟩
  dsimp only
  rw [iteratedFDeriv_sub_apply
    (hf.1.of_le (by exact_mod_cast hj)).contDiffAt
    (hg.1.of_le (by exact_mod_cast hj)).contDiffAt]
  exact (norm_sub_le _ _).trans
    (add_le_add (chart_derivative_le_cbNorm hf hj x) (chart_derivative_le_cbNorm hg hj x))

theorem chart_memCb_smul (c : ℝ) {f : Euc d → ℝ} (hf : MemCb r f) :
    MemCb r (c • f) := by
  refine ⟨hf.1.const_smul c, fun j hj => ?_⟩
  refine ⟨|c| * cbNorm r f, ?_⟩
  rintro _ ⟨x, rfl⟩
  dsimp only
  rw [iteratedFDeriv_const_smul_apply
    (a := c) (i := j) (f := f) (hf.1.of_le (by exact_mod_cast hj)).contDiffAt,
    norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (chart_derivative_le_cbNorm hf hj x) (abs_nonneg c)

theorem chart_memCb_of_test {f : Euc d → ℝ} (hf : IsR2Test f) : MemCb r f := by
  obtain ⟨B, hB, hb⟩ := hf.2.exists_bound_iteratedFDeriv hf.1 r
  exact ⟨hf.1.of_le (by exact_mod_cast le_top), fun j hj =>
    ⟨B, by rintro _ ⟨x, rfl⟩; exact hb j hj x⟩⟩

theorem chart_weighted_of_memCb (hP : (d : ℝ) < 2 * Pw)
    {f : Euc d → ℝ} (hf : MemCb r f) : IsR2WeightedTest r Pw f := by
  refine ⟨hf.1, s57p_E_lt_top_of_bound hP (B := cbNorm r f) ?_⟩
  intro j hj i x
  exact (s57p_abs_partialDeriv_le i f x).trans (chart_derivative_le_cbNorm hf hj x)

theorem chart_encode_sub (E : WeightedChart d r Pw) (hP : (d : ℝ) < 2 * Pw)
    {f g : Euc d → ℝ} (hf : MemCb r f) (hg : MemCb r g) :
    E.encode (f - g) = E.encode f - E.encode g := by
  have hfE := chart_weighted_of_memCb hP hf
  have hgE := chart_weighted_of_memCb hP hg
  have hnegE := chart_weighted_of_memCb hP (chart_memCb_smul (-1) hg)
  calc
    E.encode (f - g) = E.encode (f + (-1 : ℝ) • g) := by
      congr 1
      simp only [neg_one_smul, sub_eq_add_neg]
    _ = E.encode f + E.encode ((-1 : ℝ) • g) := E.add _ _ hfE hnegE
    _ = E.encode f + (-1 : ℝ) • E.encode g := by rw [E.smul _ _ hgE]
    _ = _ := by simp only [neg_one_smul, sub_eq_add_neg]

theorem weightedSobolev_family_measurable {A : Type*} [MeasurableSpace A]
    (F : A → Euc d → ℝ)
    (hF : StronglyMeasurable (fun p : A × Euc d => F p.1 p.2))
    (hreg : ∀ a, ContDiff ℝ r (F a)) :
    Measurable (fun a => weightedSobolevE r Pw (F a)) := by
  have hw : Continuous (fun x : Euc d => jbracket x ^ (-2 * Pw)) := by
    apply Continuous.rpow_const
    · unfold jbracket
      fun_prop
    · intro x
      exact Or.inl (s57p_jbracket_pos x).ne'
  have hjet : ∀ j ≤ r, ∀ i : Fin j → Fin d,
      Measurable (fun p : A × Euc d => partialDeriv i (F p.1) p.2) := by
    intro j hj i
    have hD := HRS.MS.PoisSg.sg_stronglyMeasurable_iteratedFDeriv F hF j
      (fun a => (hreg a).of_le (by exact_mod_cast hj))
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
      (fun l => EuclideanSpace.single (i l) (1 : ℝ))).continuous.comp_stronglyMeasurable hD).measurable
  have hS : Measurable (fun a => s57pS d r Pw (F a)) := by
    unfold s57pS
    refine Finset.measurable_fun_sum _ fun j hj => ?_
    refine Finset.measurable_fun_sum _ fun i _ => ?_
    have hm : Measurable (fun p : A × Euc d =>
        ENNReal.ofReal (jbracket p.2 ^ (-2 * Pw) * (partialDeriv i (F p.1) p.2) ^ 2)) :=
      ((hw.measurable.comp measurable_snd).mul
        ((hjet j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) i).pow_const 2)).ennreal_ofReal
    exact hm.lintegral_prod_right' (ν := (volume : Measure (Euc d)))
  exact (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).measurable.comp hS

/-- Joint spatial measurability and bounded finite jets suffice to encode
a family in any chart satisfying the exact frozen chart axioms. -/
theorem chart_encode_stronglyMeasurable {A : Type*} [MeasurableSpace A]
    (E : WeightedChart d r Pw) (hP : (d : ℝ) < 2 * Pw)
    (F : A → Euc d → ℝ)
    (hF : StronglyMeasurable (fun p : A × Euc d => F p.1 p.2))
    (hreg : ∀ a, MemCb r (F a)) : StronglyMeasurable (fun a => E.encode (F a)) := by
  let : TopologicalSpace.SeparableSpace Coeff := HRS.StaticLimitAux.separable_lp
  let : SecondCountableTopology Coeff := UniformSpace.secondCountable_of_separable _
  apply Measurable.stronglyMeasurable
  refine measurable_of_dist_dense_range
    (fun f : {f : Euc d → ℝ // IsR2Test f} => E.encode f) E.dense _ ?_
  intro f
  have hf := chart_memCb_of_test (r := r) f.property
  have hsub : StronglyMeasurable (fun p : A × Euc d => (F p.1 - (f : Euc d → ℝ)) p.2) :=
    hF.sub (f.property.1.continuous.measurable.comp measurable_snd).stronglyMeasurable
  have hm := (weightedSobolev_family_measurable
    (fun a => F a - (f : Euc d → ℝ)) hsub (fun a => (chart_memCb_sub (hreg a) hf).1)
      (Pw := Pw)).ennreal_toReal
  convert hm using 1
  funext a
  rw [dist_eq_norm, ← chart_encode_sub E hP (hreg a) hf,
    E.norm _ (chart_weighted_of_memCb hP (chart_memCb_sub (hreg a) hf))]

theorem chart_memCb_gradient_inner {f g : Euc d → ℝ}
    (hf : MemCb (r + 1) f) (hg : MemCb (r + 1) g) :
    MemCb r (fun x => inner ℝ (gradient f x) (gradient g x)) := by
  -- The coordinate proof is the accepted argument of CovMeasAux5 and
  -- S111K4ATF, specialized here to avoid importing unrelated path proofs.
  let D : (Euc d → ℝ) → Fin d → Euc d → ℝ := fun h k x =>
    fderiv ℝ h x (EuclideanSpace.single k (1 : ℝ))
  have hD : ∀ h : Euc d → ℝ, MemCb (r + 1) h → ∀ k : Fin d,
      ContDiff ℝ r (D h k) := by
    intro h hh k
    exact (hh.1.fderiv_right (m := r) (by push_cast; exact le_rfl)).clm_apply contDiff_const
  have hbD : ∀ h : Euc d → ℝ, MemCb (r + 1) h → ∀ k : Fin d,
      ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (D h k) x‖ ≤ cbNorm (r + 1) h := by
    intro h hh k j hj x
    have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ h)
      (c := EuclideanSpace.single k (1 : ℝ)) (x := x) (N := (r : WithTop ℕ∞)) (n := j)
      ((hh.1.fderiv_right (m := r) (by push_cast; exact le_rfl)).contDiffAt)
      (by exact_mod_cast hj)
    rw [norm_iteratedFDeriv_fderiv] at h1
    have h2 : ‖(EuclideanSpace.single k (1 : ℝ) : Euc d)‖ = 1 := by simp
    rw [h2, one_mul] at h1
    exact h1.trans (chart_derivative_le_cbNorm hh (by omega) x)
  have he : (fun x => inner ℝ (gradient f x) (gradient g x)) =
      fun x => ∑ k : Fin d, D f k x * D g k x := by
    funext x
    have hc : ∀ h : Euc d → ℝ, ∀ k : Fin d, gradient h x k = D h k x := by
      intro h k
      have h1 : inner ℝ (gradient h x) (EuclideanSpace.single k (1 : ℝ)) =
          fderiv ℝ h x (EuclideanSpace.single k 1) := by
        unfold gradient
        rw [InnerProductSpace.toDual_symm_apply]
      have h2 : inner ℝ (gradient h x) (EuclideanSpace.single k (1 : ℝ)) =
          gradient h x k := by
        rw [EuclideanSpace.inner_single_right]
        simp
      exact h2.symm.trans h1
    simp only [PiLp.inner_apply, hc]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]
  rw [he]
  refine ⟨ContDiff.sum (fun k _ => (hD f hf k).mul (hD g hg k)), fun j hj => ?_⟩
  refine ⟨(d : ℝ) * (2 ^ r * (cbNorm (r + 1) f * cbNorm (r + 1) g)), ?_⟩
  rintro _ ⟨x, rfl⟩
  dsimp only
  have hbf0 : 0 ≤ cbNorm (r + 1) f :=
    (norm_nonneg _).trans (chart_derivative_le_cbNorm hf (Nat.zero_le _) x)
  have hbg0 : 0 ≤ cbNorm (r + 1) g :=
    (norm_nonneg _).trans (chart_derivative_le_cbNorm hg (Nat.zero_le _) x)
  have hterm : ∀ k : Fin d,
      ‖iteratedFDeriv ℝ j (fun y => D f k y * D g k y) x‖ ≤
        2 ^ r * (cbNorm (r + 1) f * cbNorm (r + 1) g) := by
    intro k
    have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (hD f hf k) (hD g hg k) x
      (n := j) (by exact_mod_cast hj)
    refine h1.trans ?_
    calc
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (D f k) x‖ * ‖iteratedFDeriv ℝ (j - i) (D g k) x‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            (cbNorm (r + 1) f * cbNorm (r + 1) g) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ j := by simpa [Nat.lt_succ_iff] using hi
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (hbD f hf k i (hi'.trans hj) x)
              (hbD g hg k (j - i) ((Nat.sub_le _ _).trans hj) x) (norm_nonneg _) hbf0)
            (Nat.cast_nonneg _)
      _ = 2 ^ j * (cbNorm (r + 1) f * cbNorm (r + 1) g) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose j
      _ ≤ 2 ^ r * (cbNorm (r + 1) f * cbNorm (r + 1) g) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj)
            (mul_nonneg hbf0 hbg0)
  rw [iteratedFDeriv_fun_sum_apply (fun k _ =>
    ((hD f hf k).mul (hD g hg k)).contDiffAt.of_le (by exact_mod_cast hj))]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ k : Fin d, ‖iteratedFDeriv ℝ j (fun y => D f k y * D g k y) x‖
      ≤ ∑ _k : Fin d, 2 ^ r * (cbNorm (r + 1) f * cbNorm (r + 1) g) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = (d : ℝ) * (2 ^ r * (cbNorm (r + 1) f * cbNorm (r + 1) g)) := by simp

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.chart_encode_stronglyMeasurable

