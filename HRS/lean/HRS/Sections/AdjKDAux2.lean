import HRS.Sections.AdjKDAux1
import HRS.Energy.StaticLimitTiltedGauss

/-!
# ADJKD, part 2: finite-dimensional uniqueness on `C([0,T];E_m)` (ingredient of packet F)

Coordinates `⟨e_k, ·⟩` are pairings with `realMode k`; they separate points and generate the Borel
σ-algebra of `E_m`, so cylinder sets (smooth tests, times in `[0,T]`) generate the Borel σ-algebra of
`PathSpace` and form a π-system.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ}

/-- A function into `E_m` with measurable coordinates is measurable. -/
theorem adjkd_measurable_of_coord {α : Type*} {mα : MeasurableSpace α} {m : ℝ}
    (F : α → NegSobolev d m) (hc : ∀ k, Measurable fun a => NegSobolev.coord (F a) k) :
    Measurable F := by
  have hlim : ∀ X : α, Tendsto
      (fun s : Finset (NonzeroLattice d) => (∑ k ∈ s,
        (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k
          (NegSobolev.coord (F X) k))))
      atTop (𝓝 (F X)) := by
    intro X
    exact lp.hasSum_single (p := 2) (by simp) (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F X)
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset (NonzeroLattice d)))
    (f := fun (s : Finset (NonzeroLattice d)) (X : α) =>
      (∑ k ∈ s, (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k
        (NegSobolev.coord (F X) k)))) (fun s => ?_) (tendsto_pi_nhds.2 hlim)
  refine Finset.measurable_sum _ fun k _ => ?_
  have hcont : Continuous (fun a : ℝ => (show NegSobolev d m from
      lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k a)) :=
    (lp.isometry_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) k).continuous
  exact hcont.measurable.comp (hc k)

theorem adjkd_isSmooth_realMode (k : NonzeroLattice d) : Torus.IsSmooth (Torus.realMode k) :=
  StaticLimitAux.isSmooth_realMode' k

/-- Pairing with the real mode `e_k` is the Fourier coefficient. -/
theorem adjkd_eval_realMode {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.eval F (Torus.realMode k) = NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.eval
  rw [tsum_eq_single k]
  · have : Torus.funRealCoeff (Torus.realMode k) k = 1 := by
      unfold Torus.funRealCoeff
      simpa using Torus.realMode_orthonormal k k
    rw [this, mul_one]
  · intro l hl
    have : Torus.funRealCoeff (Torus.realMode k) l = 0 := by
      unfold Torus.funRealCoeff
      have := Torus.realMode_orthonormal l k
      rw [if_neg hl] at this
      exact this
    rw [this, mul_zero]

theorem adjkd_eval_continuous {m : ℝ} {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Continuous fun F : NegSobolev d m => NegSobolev.eval F φ := by
  have hs := GF.gfb1_smooth_sq hφ m
  set C : ℝ := Real.sqrt (∑' k : NonzeroLattice d,
      Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) with hC
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal C) fun F G => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm, ← GF.gf_eval_sub_proof F G hφ]
  refine (NegSobolev.abs_eval_le (F - G) φ hs).trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (norm_nonneg _)

/-- The finite-dimensional functional: pairings with smooth tests at given times. -/
def adjkdG {m T : ℝ} {p : ℕ} (ts : Fin p → Set.Icc (0 : ℝ) T) (φ : Fin p → Torus d → ℝ)
    (w : PathSpace d m T) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun a => NegSobolev.eval (w.at' (ts a)) (φ a)

theorem adjkd_at_continuous {m T : ℝ} (t : Set.Icc (0 : ℝ) T) :
    Continuous fun w : PathSpace d m T => w.at' t := by
  have : Continuous fun w : C(Set.Icc (0 : ℝ) T, NegSobolev d m) => w t :=
    continuous_eval_const t
  exact this

theorem adjkdG_continuous {m T : ℝ} {p : ℕ} (ts : Fin p → Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    Continuous (adjkdG (m := m) ts φ) := by
  unfold adjkdG
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun a => ?_)
  exact (adjkd_eval_continuous (hφ a)).comp (adjkd_at_continuous (ts a))


/-- Cylinder sets of `PathSpace`: preimages of Borel sets under finite-dimensional pairings with smooth tests. -/
def adjkdCyl (d : ℕ) (m T : ℝ) : Set (Set (PathSpace d m T)) :=
  {S | ∃ (p : ℕ) (ts : Fin p → Set.Icc (0 : ℝ) T) (φ : Fin p → Torus d → ℝ)
      (B : Set (EuclideanSpace ℝ (Fin p))),
    (∀ a, Torus.IsSmooth (φ a)) ∧ MeasurableSet B ∧ S = adjkdG ts φ ⁻¹' B}

theorem adjkd_proj_continuous {n : ℕ} (p : ℕ) (f : Fin p → Fin n) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) =>
      (WithLp.toLp 2 fun a => x (f a) : EuclideanSpace ℝ (Fin p)) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun a => ?_)
  exact (EuclideanSpace.proj (f a)).continuous

theorem adjkdCyl_isPiSystem {m T : ℝ} : IsPiSystem (adjkdCyl d m T) := by
  rintro S1 ⟨p, ts, φ, B, hφ, hB, rfl⟩ S2 ⟨q, ts', φ', B', hφ', hB', rfl⟩ -
  let π1 : EuclideanSpace ℝ (Fin (p + q)) → EuclideanSpace ℝ (Fin p) :=
    fun x => WithLp.toLp 2 fun a => x (Fin.castAdd q a)
  let π2 : EuclideanSpace ℝ (Fin (p + q)) → EuclideanSpace ℝ (Fin q) :=
    fun x => WithLp.toLp 2 fun a => x (Fin.natAdd p a)
  have h1 : Measurable π1 := (adjkd_proj_continuous p (Fin.castAdd q)).measurable
  have h2 : Measurable π2 := (adjkd_proj_continuous q (Fin.natAdd p)).measurable
  refine ⟨p + q, Fin.append ts ts', Fin.append φ φ', π1 ⁻¹' B ∩ π2 ⁻¹' B', ?_, ?_, ?_⟩
  · intro a
    refine Fin.addCases (fun i => ?_) (fun i => ?_) a
    · simpa using hφ i
    · simpa using hφ' i
  · exact (h1 hB).inter (h2 hB')
  · ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, π1, π2, adjkdG]
    simp [Fin.append_left, Fin.append_right]

/-- Type synonym carrying the σ-algebra generated by the cylinder sets. -/
def AdjkdCylSpace (d : ℕ) (m T : ℝ) : Type := PathSpace d m T

instance adjkdCylSpace_ms {m T : ℝ} : MeasurableSpace (AdjkdCylSpace d m T) :=
  MeasurableSpace.generateFrom (adjkdCyl d m T)

theorem adjkd_cyl_measurable {m T : ℝ} {p : ℕ} (ts : Fin p → Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    Measurable (fun w : AdjkdCylSpace d m T => adjkdG (m := m) ts φ (show PathSpace d m T from w)) := by
  intro B hB
  exact MeasurableSpace.measurableSet_generateFrom ⟨p, ts, φ, B, hφ, hB, rfl⟩

theorem adjkd_borel_eq_generateFrom {m T : ℝ} :
    (inferInstance : MeasurableSpace (PathSpace d m T)) =
      MeasurableSpace.generateFrom (adjkdCyl d m T) := by
  refine le_antisymm ?_ ?_
  · -- Borel ≤ σ(cylinders)
    have hid : Measurable (fun w : AdjkdCylSpace d m T => (show PathSpace d m T from w)) := by
      refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
      refine adjkd_measurable_of_coord _ fun k => ?_
      have hk : ∀ w : AdjkdCylSpace d m T,
          NegSobolev.coord ((show PathSpace d m T from w).at' t) k =
            (Lattice.jp k.1 ^ m)⁻¹ * (adjkdG (m := m) (fun _ : Fin 1 => t)
              (fun _ => Torus.realMode k) (show PathSpace d m T from w)) 0 := by
        intro w
        have e : (adjkdG (m := m) (fun _ : Fin 1 => t) (fun _ => Torus.realMode k)
            (show PathSpace d m T from w)) 0 =
            NegSobolev.fourierCoeff ((show PathSpace d m T from w).at' t) k := by
          simp [adjkdG, adjkd_eval_realMode]
        rw [e]
        unfold NegSobolev.fourierCoeff
        have hp : Lattice.jp k.1 ^ m ≠ 0 := (Real.rpow_pos_of_pos (Torus.jp_pos _) _).ne'
        field_simp
      have hmeas : Measurable fun w : AdjkdCylSpace d m T => (Lattice.jp k.1 ^ m)⁻¹ *
          (adjkdG (m := m) (fun _ : Fin 1 => t) (fun _ => Torus.realMode k)
            (show PathSpace d m T from w)) 0 := by
        refine Measurable.const_mul ?_ _
        have := adjkd_cyl_measurable (m := m) (fun _ : Fin 1 => t) (fun _ => Torus.realMode k)
          (fun _ => adjkd_isSmooth_realMode k)
        exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.measurable.comp this
      convert hmeas using 1
      funext w
      exact hk w
    intro s hs
    exact hid hs
  · refine MeasurableSpace.generateFrom_le ?_
    rintro S ⟨p, ts, φ, B, hφ, hB, rfl⟩
    exact (adjkdG_continuous ts φ hφ).measurable hB

theorem adjkd_ext_of_fidi {m T : ℝ} (μ ν : Measure (PathSpace d m T)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (h : ∀ (p : ℕ) (ts : Fin p → Set.Icc (0 : ℝ) T) (φ : Fin p → Torus d → ℝ),
      (∀ a, Torus.IsSmooth (φ a)) → μ.map (adjkdG ts φ) = ν.map (adjkdG ts φ)) : μ = ν := by
  refine ext_of_generate_finite (adjkdCyl d m T) adjkd_borel_eq_generateFrom adjkdCyl_isPiSystem ?_
    (by simp)
  rintro S ⟨p, ts, φ, B, hφ, hB, rfl⟩
  have hm := (adjkdG_continuous (m := m) ts φ hφ).measurable
  have := congrArg (fun κ => κ B) (h p ts φ hφ)
  simpa [Measure.map_apply hm hB] using this

end HRS.AdjK
