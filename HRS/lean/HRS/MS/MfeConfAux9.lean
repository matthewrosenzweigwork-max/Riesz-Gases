import HRS.MS.MfeConfAux8

/-!
# S.B.1, packet F1 (part 4): measurability of the trajectory, the weak interval identity, time-Lipschitz continuity

`Sb1Traj D T C B ρ` bundles the data used for the whole-space classical regularity (F1): `1 ≤ d`, `0 ≤ s < d`, `M = -1`,
`V ∈ C³` with `‖D²V‖ ≤ B`, the weak solution `ρ` (`IsWholeMeanFieldSolution`) and the uniform density slices.

* `sb1_gen_bound`: `|mfGen D ψ ρ_r| ≤ K_A ∫|ψ|` for a `C²` compactly supported `ψ` (from `sb1_weak_eq_pde` and `sb1A_bound`).
* `sb1_rho_joint`: `(r,x) ↦ ρ_{clamp r}(x)` is jointly measurable (the weak form with the bump tests and the junk-value trick
  `db1_meas_of_weak`: the Bochner integral in the weak form is *not assumed* to be of an integrable function).
* `sb1_weak_interval`: the integrand `mfGen` is integrable and `⟨ρ_b,ψ⟩ - ⟨ρ_a,ψ⟩ = ∫_a^b mfGen`.
* `sb1_rho_lip_time`: `|ρ_b(x) - ρ_a(x)| ≤ K_A |b - a|` uniformly in `x`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

open HRS.MP.RdGen HRS.MH.DualityRd

variable {d : ℕ}

/-- The data of the classical regularity packet. -/
structure Sb1Traj (D : Whole.WholeDyn d) (T C B : ℝ) (ρ : ℝ → Euc d → ℝ) : Prop where
  hC : 0 ≤ C
  hd : 1 ≤ d
  hs0 : 0 ≤ D.s
  hsd : D.s < d
  hM : D.M = -1
  V : Sb1Pot D.V B
  mf : Whole.IsWholeMeanFieldSolution D T ρ
  slice : ∀ r ∈ Set.Icc (0 : ℝ) T, Sb1Slice d C (ρ r)
  reg : ∀ r ∈ Set.Icc (0 : ℝ) T, RegSliceRd (ρ r)

variable {D : Whole.WholeDyn d} {T C B : ℝ} {ρ : ℝ → Euc d → ℝ}

/-- The uniform bound constant of `A`. -/
def Sb1Traj.KA (_H : Sb1Traj D T C B ρ) : ℝ :=
  sb1KA d D.invβ C B ‖fderiv ℝ D.V 0‖ (sb1BF d D.s C)

theorem Sb1Traj.KA_nonneg (H : Sb1Traj D T C B ρ) : 0 ≤ H.KA := by
  have hB := H.V.B_nonneg
  have hBF := sb1BF_nonneg (d := d) H.hs0 H.hC
  have hG := norm_nonneg (fderiv ℝ D.V 0)
  unfold Sb1Traj.KA sb1KA
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hC := H.hC
  have h1 : 0 ≤ |D.invβ| * (d * C) := mul_nonneg (abs_nonneg _) (mul_nonneg hdd hC)
  have h2 : 0 ≤ (d : ℝ) * (C * (‖fderiv ℝ D.V 0‖ + sb1BF d D.s C + B) + C * (B + sb1BF d D.s C)) :=
    mul_nonneg hdd (add_nonneg (mul_nonneg hC (by linarith)) (mul_nonneg hC (by linarith)))
  exact add_nonneg h1 h2

theorem sb1_gen_bound (H : Sb1Traj D T C B ρ) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) :
    ∀ r ∈ Set.Icc (0 : ℝ) T, |mfGen D ψ (ρ r)| ≤ H.KA * ∫ x, |ψ x| := by
  intro r hr
  rw [sb1_weak_eq_pde D H.V H.hd H.hs0 H.hsd H.hM (H.slice r hr) (H.reg r hr) hψ hψc]
  have hint : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
  rw [← Real.norm_eq_abs]
  calc ‖∫ x, ψ x * sb1A D (ρ r) x‖ ≤ ∫ x, ‖ψ x‖ * H.KA :=
        norm_integral_le_of_norm_le (hint.norm.mul_const _) (Eventually.of_forall fun x => by
          rw [norm_mul, Real.norm_eq_abs (sb1A D (ρ r) x)]
          exact mul_le_mul_of_nonneg_left (sb1A_bound D H.V H.hd H.hs0 H.hsd (H.slice r hr) x)
            (norm_nonneg _))
    _ = H.KA * ∫ x, |ψ x| := by
        rw [integral_mul_const, mul_comm]
        simp only [Real.norm_eq_abs]

theorem Sb1Traj.cont (H : Sb1Traj D T C B ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) : Continuous (ρ r) :=
  (H.slice r hr).decay.1.continuous

theorem sb1_clamp_mem {T : ℝ} (hT : 0 ≤ T) (r : ℝ) : max 0 (min r T) ∈ Set.Icc (0 : ℝ) T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

/-! ### Measurability -/

theorem sb1_pair_meas (H : Sb1Traj D T C B ρ) (hT : 0 ≤ T) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) :
    Measurable (fun r => Whole.pair (Whole.withDensityReal (ρ (max 0 (min r T)))) ψ) := by
  obtain ⟨K, hK⟩ : ∃ K, ∀ r ∈ Set.Icc (0 : ℝ) T, |mfGen D ψ (ρ r)| ≤ K :=
    ⟨_, sb1_gen_bound H hψ hψc⟩
  refine db1_meas_of_weak (g := fun r => mfGen D ψ (ρ r))
    (F := fun t => Whole.pair (Whole.withDensityReal (ρ t)) ψ) (K := K) hT hK ?_
  intro t ht
  have hw := H.mf.weak ψ (db1_memCb_of_compact hψ hψc) t ht
  have e : ∫ r in Set.Icc (0 : ℝ) t, mfGen D ψ (ρ r) = ∫ r in Set.Icc (0 : ℝ) t,
      (Whole.pair (Whole.withDensityReal (ρ r)) (fun x => D.invβ * Laplacian.laplacian ψ x -
          inner ℝ (gradient D.V x) (gradient ψ x)) +
        Whole.interactionPairingW D ψ (Whole.withDensityReal (ρ r)) (Whole.withDensityReal (ρ r))) := rfl
  show Whole.pair (Whole.withDensityReal (ρ t)) ψ = Whole.pair (Whole.withDensityReal (ρ 0)) ψ +
      ∫ r in Set.Icc (0 : ℝ) t, mfGen D ψ (ρ r)
  rw [e]
  linarith [hw]

/-- the bump tests `y ↦ η_n(x - y)` -/
theorem sb1_bump_test (n : ℕ) (x : Euc d) :
    ContDiff ℝ 2 (fun y => ((db1_bump d n).normed volume) (x - y)) ∧
      HasCompactSupport (fun y => ((db1_bump d n).normed volume) (x - y)) :=
  ⟨(ContDiffBump.contDiff_normed (f := db1_bump d n) (μ := volume)).comp (contDiff_const.sub contDiff_id),
    (ContDiffBump.hasCompactSupport_normed (f := db1_bump d n) (μ := volume)).comp_homeomorph
      (Homeomorph.subLeft x)⟩

theorem sb1_rho_meas (H : Sb1Traj D T C B ρ) (hT : 0 ≤ T) (x : Euc d) :
    Measurable (fun r => ρ (max 0 (min r T)) x) := by
  refine measurable_of_tendsto_metrizable
    (f := fun (n : ℕ) (r : ℝ) => Whole.pair (Whole.withDensityReal (ρ (max 0 (min r T))))
      (fun y => ((db1_bump d n).normed volume) (x - y))) (g := fun r => ρ (max 0 (min r T)) x)
    (fun n => sb1_pair_meas H hT (sb1_bump_test n x).1 (sb1_bump_test n x).2) ?_
  refine tendsto_pi_nhds.2 fun r => ?_
  exact db1_approx (H.mf.density _ (sb1_clamp_mem hT r)) (H.cont (sb1_clamp_mem hT r)) x

theorem sb1_rho_joint (H : Sb1Traj D T C B ρ) (hT : 0 ≤ T) :
    Measurable (fun p : ℝ × Euc d => ρ (max 0 (min p.1 T)) p.2) := by
  have hu := measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Euc d) (r : ℝ) => ρ (max 0 (min r T)) x)
    (fun r => H.cont (sb1_clamp_mem hT r)) (fun x => sb1_rho_meas H hT x)
  exact hu.comp measurable_swap

theorem sb1_gen_meas (H : Sb1Traj D T C B ρ) (hT : 0 ≤ T) {ψ : Euc d → ℝ} (hψC : ContDiff ℝ 2 ψ) :
    Measurable (fun r => mfGen D ψ (ρ (max 0 (min r T)))) := by
  have hmem := sb1_clamp_mem hT
  have hV2 : ContDiff ℝ 2 D.V := H.V.c3.of_le (by norm_num)
  have hJ := sb1_rho_joint H hT
  have hgT : Measurable (fun x => D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x)) :=
    Measurable.sub (Measurable.const_mul (db1_laplacian_continuous hψC).measurable _)
      (Measurable.inner (db1_gradient_continuous hV2).measurable (db1_gradient_continuous hψC).measurable)
  have hF1 : Measurable (fun r => ∫ x, ρ (max 0 (min r T)) x *
      (D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x))) := by
    have hf : Measurable (fun p : ℝ × Euc d => ρ (max 0 (min p.1 T)) p.2 *
        (D.invβ * Laplacian.laplacian ψ p.2 - inner ℝ (gradient D.V p.2) (gradient ψ p.2))) :=
      hJ.mul (hgT.comp measurable_snd)
    exact (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable
  have hF2 : Measurable (fun q : ℝ × Euc d => ∫ y, ρ (max 0 (min q.1 T)) y * pairKernelRd D ψ q.2 y) := by
    have hf : Measurable (fun p : (ℝ × Euc d) × Euc d =>
        ρ (max 0 (min p.1.1 T)) p.2 * pairKernelRd D ψ p.1.2 p.2) :=
      (hJ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
        ((db1_pK_measurable hψC).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable
  have hF3 : Measurable (fun r => ∫ x, ρ (max 0 (min r T)) x *
      ∫ y, ρ (max 0 (min r T)) y * pairKernelRd D ψ x y) := by
    have hf : Measurable (fun p : ℝ × Euc d => ρ (max 0 (min p.1 T)) p.2 *
        ∫ y, ρ (max 0 (min p.1 T)) y * pairKernelRd D ψ p.2 y) := hJ.mul hF2
    exact (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable
  have e : (fun r => mfGen D ψ (ρ (max 0 (min r T)))) = fun r =>
      (∫ x, ρ (max 0 (min r T)) x *
        (D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x)))
      + (1 / 2 : ℝ) * ∫ x, ρ (max 0 (min r T)) x * ∫ y, ρ (max 0 (min r T)) y * pairKernelRd D ψ x y :=
    funext fun r => db1_mfGen_eq D (H.mf.density _ (hmem r))
  rw [e]
  exact hF1.add (measurable_const.mul hF3)

/-! ### The weak interval identity -/

theorem sb1_weak_interval (H : Sb1Traj D T C B ρ) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) :
    IntegrableOn (fun r => mfGen D ψ (ρ r)) (Set.Icc (0 : ℝ) T) ∧
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
      Whole.pair (Whole.withDensityReal (ρ b)) ψ - Whole.pair (Whole.withDensityReal (ρ a)) ψ
        = ∫ r in a..b, mfGen D ψ (ρ r) := by
  by_cases hT : 0 ≤ T
  swap
  · have hempty : Set.Icc (0 : ℝ) T = ∅ := Set.Icc_eq_empty hT
    refine ⟨?_, fun a b ha hab hb => absurd (ha.trans (hab.trans hb)) hT⟩
    rw [hempty]
    exact integrableOn_empty
  obtain ⟨K, hbd⟩ : ∃ K, ∀ r ∈ Set.Icc (0 : ℝ) T, |mfGen D ψ (ρ r)| ≤ K := ⟨_, sb1_gen_bound H hψ hψc⟩
  have hcl : ∀ r ∈ Set.Icc (0 : ℝ) T, max 0 (min r T) = r := fun r hr => by
    rw [min_eq_left hr.2, max_eq_right hr.1]
  have hIcc : IntegrableOn (fun r => mfGen D ψ (ρ (max 0 (min r T)))) (Set.Icc (0 : ℝ) T) := by
    refine Integrable.of_bound (μ := volume.restrict (Set.Icc (0 : ℝ) T)) (C := K) ?_ ?_
    · exact (sb1_gen_meas H hT hψ).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      rw [Real.norm_eq_abs, hcl r hr]
      exact hbd r hr
  have hIcc' : IntegrableOn (fun r => mfGen D ψ (ρ r)) (Set.Icc (0 : ℝ) T) :=
    hIcc.congr_fun (fun r hr => by simp only [hcl r hr]) measurableSet_Icc
  refine ⟨hIcc', fun a b ha hab hb => ?_⟩
  have hbT : b ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans hab, hb⟩
  have haT : a ∈ Set.Icc (0 : ℝ) T := ⟨ha, hab.trans hb⟩
  have hsplit : Set.Icc (0 : ℝ) b = Set.Icc 0 a ∪ Set.Ioc a b := (Set.Icc_union_Ioc_eq_Icc ha hab).symm
  have hdisj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a b) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.2 hx'.1)
  have hi1 : IntegrableOn (fun r => mfGen D ψ (ρ r)) (Set.Icc 0 a) :=
    hIcc'.mono_set (Set.Icc_subset_Icc_right (hab.trans hb))
  have hi2 : IntegrableOn (fun r => mfGen D ψ (ρ r)) (Set.Ioc a b) :=
    hIcc'.mono_set (fun r hr => ⟨ha.trans hr.1.le, hr.2.trans hb⟩)
  have h1 : Whole.pair (Whole.withDensityReal (ρ b)) ψ - Whole.pair (Whole.withDensityReal (ρ 0)) ψ
      = ∫ r in Set.Icc (0 : ℝ) b, mfGen D ψ (ρ r) := H.mf.weak ψ (db1_memCb_of_compact hψ hψc) b hbT
  have h2 : Whole.pair (Whole.withDensityReal (ρ a)) ψ - Whole.pair (Whole.withDensityReal (ρ 0)) ψ
      = ∫ r in Set.Icc (0 : ℝ) a, mfGen D ψ (ρ r) := H.mf.weak ψ (db1_memCb_of_compact hψ hψc) a haT
  rw [hsplit, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hi1 hi2] at h1
  rw [intervalIntegral.integral_of_le hab]
  linarith

end HRS.MS.MfeConf
