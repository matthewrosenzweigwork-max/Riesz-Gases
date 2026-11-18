import HRS.Uniform.Q54cAux10

/-!
# Q54c, part 11: the process `Ŷ` built from a Gaussian martingale

`PathData.Ypath` is the clamped (in time) pathwise process; `Ypath_continuous`, `Yproc_measurable`,
`noiseVec_measurable'`, initial value.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.Uniform.Q54c

open HRS HRS.Uniform.Q07c HRS.HilbertCLTAux

variable {d : ℕ}

theorem measurable_of_coord {Z : Type*} [MeasurableSpace Z] {m : ℝ} {f : Z → NegSobolev d m}
    (hf : ∀ k, Measurable fun z => NegSobolev.coord (f z) k) : Measurable f := by
  let hb0 : HilbertBasis (NonzeroLattice d) ℝ (NegSobolev d m) :=
    (show HilbertBasis (NonzeroLattice d) ℝ (lp (fun _ : NonzeroLattice d => ℝ) 2) from default)
  refine measurable_of_inner_basis (ι := NonzeroLattice d) hb0 (fun k => ?_)
  have : (fun z => inner ℝ (hb0 k) (f z)) = fun z => NegSobolev.coord (f z) k := by
    funext z
    have h := hb0.repr_apply_apply (f z) k
    rw [← h]
    rfl
  rw [this]
  exact hf k

section Meas

variable {Ω : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {G : ℝ → Ω → H} {T : ℝ}

theorem measurable_isum' {m : MeasurableSpace Ω} (hGm : ∀ τ ∈ Set.Icc 0 T, Measurable[m] (G τ))
    (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (y : ℝ → H) (N : ℕ) :
    Measurable[m] (fun ω => isum (fun σ => G σ ω) y T t N) := by
  letI : MeasurableSpace Ω := m
  simp_rw [isum]
  refine Finset.measurable_sum _ fun i hi => ?_
  have hi' : i ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 : min (gridPt T N (i + 1)) t ∈ Set.Icc 0 T :=
    ⟨le_min (gridPt_nonneg hT N _) ht.1, (min_le_left _ _).trans (gridPt_le hT N (Nat.succ_le_succ hi'))⟩
  have h2 : min (gridPt T N i) t ∈ Set.Icc 0 T :=
    ⟨le_min (gridPt_nonneg hT N _) ht.1, (min_le_left _ _).trans (gridPt_le hT N (hi'.trans (Nat.le_succ N)))⟩
  exact ((hGm _ h1).sub (hGm _ h2)).inner measurable_const

end Meas


/-! ### the process -/

section Yproc

variable {a : ℝ}

/-- The pathwise process `t ↦ Ŷ_t` (time clamped to `[0,T]`). -/
def PathData.Ypath (P : PathData d a) (T A : ℝ) (η : NegSobolev d (a + 2)) (G : ℝ → NegSobolev d a)
    (t : ℝ) : NegSobolev d (a + 4) :=
  P.Yelt A η G (max 0 (min t T))

theorem continuous_clamp01 (T : ℝ) : Continuous fun t : ℝ => max 0 (min t T) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clamp01_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : max 0 (min t T) ∈ Set.Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem clamp01_of_mem {T t : ℝ} (ht : t ∈ Set.Icc 0 T) : max 0 (min t T) = t := by
  rw [min_eq_left ht.2, max_eq_right ht.1]

theorem Ypath_continuous {P : PathData d a} {T K : ℝ} (hP : P.Spec T K) {G : ℝ → NegSobolev d a}
    (hG : ContinuousOn G (Set.Icc 0 T)) (A : ℝ) (η : NegSobolev d (a + 2)) :
    Continuous (P.Ypath T A η G) := by
  have hT := hP.hT
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hG
  set c : ℝ := (3 + T) * M * K + |A| * (‖η‖ * K) with hc
  have hGc : Continuous fun t : ℝ => G (max 0 (min t T)) :=
    hG.comp_continuous (continuous_clamp01 T) (clamp01_mem hT)
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ t : ℝ, ‖P.Ypath T A η G t - P.Ypath T A η G t₀‖ ≤
      K * ‖G (max 0 (min t T)) - G (max 0 (min t₀ T))‖ +
        c * |max 0 (min t T) - max 0 (min t₀ T)| := fun t =>
    Yelt_sub_norm_le hP hG hM A η (clamp01_mem hT t) (clamp01_mem hT t₀)
  have hlim : Tendsto (fun t : ℝ => K * ‖G (max 0 (min t T)) - G (max 0 (min t₀ T))‖ +
      c * |max 0 (min t T) - max 0 (min t₀ T)|) (𝓝 t₀) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => ‖G (max 0 (min t T)) - G (max 0 (min t₀ T))‖) (𝓝 t₀) (𝓝 0) := by
      have := (hGc.tendsto t₀)
      have := (this.sub_const (G (max 0 (min t₀ T)))).norm
      simpa using this
    have h2 : Tendsto (fun t : ℝ => |max 0 (min t T) - max 0 (min t₀ T)|) (𝓝 t₀) (𝓝 0) := by
      have := ((continuous_clamp01 T).tendsto t₀).sub_const (max 0 (min t₀ T))
      have := this.abs
      simpa using this
    simpa using (h1.const_mul K).add (h2.const_mul c)
  exact squeeze_zero (fun t => norm_nonneg _) hb hlim

theorem coord_embed {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.embed m' F) k = Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k := by
  have hcoord : ∀ k, |Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k| ≤ |NegSobolev.coord F k| := by
    intro k
    have hj := Torus.jp_pos k.1
    have : Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k =
        Lattice.jp k.1 ^ (m - m') * NegSobolev.coord F k := by
      unfold NegSobolev.fourierCoeff
      rw [← mul_assoc, ← Real.rpow_add hj]
      ring_nf
    rw [this, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hj _)]
    have h1 : Lattice.jp k.1 ^ (m - m') ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (Torus.jp_ge_one _) (by linarith)
    exact mul_le_of_le_one_left (abs_nonneg _) h1
  obtain ⟨h3, h4⟩ := NegSobolev.coord_sq F
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k) 2 := by
    rw [Torus.memℓp_two_iff]
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) h3
    calc _ = |Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k| ^ 2 := (sq_abs _).symm
      _ ≤ |NegSobolev.coord F k| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hcoord k) 2
      _ = _ := sq_abs _
  exact NegSobolev.coord_ofSeq_of_mem _ hmem k

theorem fourierCoeff_embed {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (NegSobolev.embed m' F) k = NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.fourierCoeff
  rw [coord_embed hmm', ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp [NegSobolev.fourierCoeff]

theorem fourierCoeff_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (c • F) k = c * NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.fourierCoeff
  have : NegSobolev.coord (c • F) k = c * NegSobolev.coord F k := rfl
  rw [this]; ring

theorem eval_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (φ : Torus d → ℝ) :
    NegSobolev.eval (c • F) φ = c * NegSobolev.eval F φ := by
  unfold NegSobolev.eval
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [fourierCoeff_smul]; ring

theorem eval_embed {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) (φ : Torus d → ℝ) :
    NegSobolev.eval (NegSobolev.embed m' F) φ = NegSobolev.eval F φ := by
  unfold NegSobolev.eval
  exact tsum_congr fun k => by rw [fourierCoeff_embed hmm']

theorem eval_realMode {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.eval F (Torus.realMode k) = NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.eval
  rw [tsum_eq_single k]
  · have : Torus.funRealCoeff (Torus.realMode k) k = 1 := by
      unfold Torus.funRealCoeff
      rw [Torus.realMode_orthonormal]; simp
    rw [this, mul_one]
  · intro l hl
    have : Torus.funRealCoeff (Torus.realMode k) l = 0 := by
      unfold Torus.funRealCoeff
      rw [Torus.realMode_orthonormal]
      simp [hl]
    rw [this, mul_zero]

end Yproc

end HRS.Uniform.Q54c
