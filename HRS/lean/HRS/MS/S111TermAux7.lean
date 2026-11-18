import HRS.MS.S111TermAux6

/-!
# S11.1 terminal wave, G01 (`gaussian_paths_of_features`): a continuous Gaussian path pair from a common iid sequence

One iid Gaussian sequence drives all features (both sides, all times); Kolmogorov--Chentsov (`HRS.MP.KC`) with the
fourth moment `E‖X_t - X_s‖⁴ ≤ 3L²|t-s|²` gives continuous versions; the pushforward to the pair path space has the
exact mixed finite-dimensional laws with the feature Gram covariance.

Defect of the skeleton, fixed here: Pro's `pairedProcess` applies an `OscPath` (a `def`, not a function type) as a function;
this does not elaborate.  The same statement is obtained with `OscPath.at'`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111T

open HRS.Whole

abbrev PathPair (d : ℕ) (m H : ℝ) := OscPath d m H × OscPath d m H

def clippedTime (H : ℝ) (hH : 0 ≤ H) (t : ℝ) : Set.Icc (0 : ℝ) H :=
  ⟨max 0 (min t H), le_max_left _ _, max_le hH (min_le_right _ _)⟩

/-- The `i`-th component process of a path pair at time `t` (clamped to `[0,H]`). -/
def pairedProcess (d : ℕ) (m H : ℝ) (hH : 0 ≤ H) (i : Fin 2) (t : ℝ) (w : PathPair d m H) : OscDual d m :=
  OscPath.at' (if i = 0 then w.1 else w.2) (clippedTime H hH t)

theorem s111t_clip_mem {H : ℝ} (hH : 0 ≤ H) (t : ℝ) : max 0 (min t H) ∈ Set.Icc (0 : ℝ) H :=
  ⟨le_max_left _ _, max_le hH (min_le_right _ _)⟩

theorem s111t_clip_of_mem {H t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) H) : max 0 (min t H) = t := by
  rw [min_eq_left ht.2, max_eq_right ht.1]

theorem s111t_clip_lip (H t v : ℝ) : |max 0 (min t H) - max 0 (min v H)| ≤ |t - v| := by
  have h1 := abs_sub_abs_le_abs_sub t v
  rw [abs_le]
  constructor
  · rcases abs_cases (t - v) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    simp only [max_def, min_def] <;> split_ifs <;> linarith
  · rcases abs_cases (t - v) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    simp only [max_def, min_def] <;> split_ifs <;> linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **G01.** One common iid Gaussian series on all times and both sides, continuous versions by Kolmogorov--Chentsov
(fourth increments), pushed forward to the pair path space; every mixed finite-dimensional law is the Gaussian with the
Gram covariance of the features. -/
theorem s111t_gaussian_paths_of_features (d : ℕ) (m H : ℝ) (hH : 0 < H)
    (e : HilbertBasis ℕ ℝ E) (F : Fin 2 → ℝ → MultiIndex d → E)
    (hF : ∀ i, ∀ t ∈ Set.Icc 0 H, Summable (fun α => ‖F i t α‖ ^ 2))
    (L : ℝ) (hL : 0 ≤ L)
    (hinc : ∀ i, ∀ t v : ℝ, t ∈ Set.Icc 0 H → v ∈ Set.Icc 0 H →
      Summable (fun α => ‖F i t α - F i v α‖ ^ 2) ∧
        (∑' α, ‖F i t α - F i v α‖ ^ 2) ≤ L * |t - v|) :
    ∃ P : Measure (PathPair d m H), IsProbabilityMeasure P ∧
      ∀ n : ℕ, ∀ side : Fin n → Fin 2, ∀ ts : Fin n → ℝ,
      ∀ alpha : Fin n → MultiIndex d, (∀ j, ts j ∈ Set.Icc 0 H) →
        P.map (fun w => (WithLp.toLp 2 fun j =>
          OscDual.coord (pairedProcess d m H hH.le (side j) (ts j) w) (alpha j) :
            EuclideanSpace ℝ (Fin n))) =
          multivariateGaussian 0 (Matrix.of fun j k =>
            inner ℝ (F (side j) (ts j) (alpha j)) (F (side k) (ts k) (alpha k))) := by
  set Fc : Fin 2 → ℝ → MultiIndex d → E := fun i t => F i (max 0 (min t H)) with hFc_def
  have hFc : ∀ i t, Summable fun α => ‖Fc i t α‖ ^ 2 := fun i t => hF i _ (s111t_clip_mem hH.le t)
  have hincc : ∀ i t v, Summable (fun α => ‖Fc i t α - Fc i v α‖ ^ 2) ∧
      (∑' α, ‖Fc i t α - Fc i v α‖ ^ 2) ≤ L * |t - v| := by
    intro i t v
    obtain ⟨h1, h2⟩ := hinc i _ _ (s111t_clip_mem hH.le t) (s111t_clip_mem hH.le v)
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (s111t_clip_lip H t v) hL)⟩
  obtain ⟨Ω, mΩ, P0, hP0, g, X, hg, hind, hXm, hXg, hmom⟩ := s111t_family m e Fc hFc L hL hincc
  obtain ⟨r, q, hr0, hr1, hq0, hq1, hqr⟩ := HRS.MP.KC.mkc_consts (β := 1) (p := 4) one_pos (by norm_num)
  have hmom' : ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) H, ∀ t ∈ Set.Icc (0 : ℝ) H,
      ∫⁻ ζ, ‖X i t ζ - X i s ζ‖ₑ ^ (4 : ℝ) ∂P0 ≤ ENNReal.ofReal (3 * L ^ 2 * |t - s| ^ ((1 : ℝ) + 1)) :=
    fun i s _ t _ => hmom i s t
  set Z : Fin 2 → ℝ → Ω → OscDual d m := fun i => HRS.MP.KC.mkc_Zc (X i) H r with hZ
  have hZc : ∀ i ω, Continuous fun t : Set.Icc (0 : ℝ) H => Z i t ω := fun i ω =>
    HRS.MP.KC.mkc_continuous (X i) H r hH hr0.le hr1 ω
  have hZm : ∀ i t, Measurable (Z i t) := fun i t =>
    HRS.MP.KC.mkc_Zc_meas (X i) H r hH hr0.le hr1 (hXm i) t
  have hZae : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) H, Z i t =ᵐ[P0] X i t := fun i t ht =>
    HRS.MP.KC.mkc_Zc_ae_eq (X i) H r P0 (hXm i) hH (p := 4) (β := 1) (C := 3 * L ^ 2) (q := q)
      (by norm_num) one_pos (hmom' i) hr0 hr1 hq0 hq1 hqr ht
  set path : Fin 2 → Ω → OscPath d m H := fun i ω =>
    (HRS.Whole.AppendixALemmas.contPathOf H (fun t => Z i t ω) : C(Set.Icc (0 : ℝ) H, OscDual d m)) with hpath
  have hpath_at : ∀ i ω (s : Set.Icc (0 : ℝ) H), OscPath.at' (path i ω) s = Z i s ω := fun i ω s =>
    HRS.MP.KC.mkc_contPathOf_apply (X i) hH hr0.le hr1 ω s
  have hpath_meas : ∀ i, Measurable (path i) := by
    intro i
    refine ContinuousMap.measurable_iff_eval.2 fun s => ?_
    have : (fun ω => (show C(Set.Icc (0 : ℝ) H, OscDual d m) from path i ω) s) = fun ω => Z i s ω := by
      funext ω; exact hpath_at i ω s
    rw [this]
    exact hZm i s
  set Φ : Ω → PathPair d m H := fun ω => (path 0 ω, path 1 ω) with hΦ
  have hΦm : Measurable Φ := (hpath_meas 0).prodMk (hpath_meas 1)
  refine ⟨P0.map Φ, inferInstance, ?_⟩
  intro n side ts alpha hts
  set Ψ : PathPair d m H → EuclideanSpace ℝ (Fin n) := fun w =>
    WithLp.toLp 2 fun j => OscDual.coord (pairedProcess d m H hH.le (side j) (ts j) w) (alpha j) with hΨ
  have hevm : ∀ (i : Fin 2) (τ : Set.Icc (0 : ℝ) H),
      Measurable fun w : PathPair d m H => OscPath.at' (if i = 0 then w.1 else w.2) τ := by
    intro i τ
    have h1 : Measurable fun w : C(Set.Icc (0 : ℝ) H, OscDual d m) => w τ :=
      ContinuousMap.measurable_eval τ
    have h2 : Measurable fun w : PathPair d m H => (if i = 0 then w.1 else w.2) := by
      by_cases hi : i = 0
      · simpa [hi] using measurable_fst
      · simpa [hi] using measurable_snd
    exact h1.comp h2
  have hΨm : Measurable Ψ := by
    refine (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp (measurable_pi_iff.2 fun j => ?_)
    exact (s111t_coordCLM d m (alpha j)).continuous.measurable.comp (hevm (side j) _)
  rw [Measure.map_map hΨm hΦm]
  have hpt : ∀ ω, (Ψ ∘ Φ) ω = WithLp.toLp 2 fun j => OscDual.coord (Z (side j) (ts j) ω) (alpha j) := by
    intro ω
    simp only [Function.comp, hΨ]
    congr 1; funext j
    congr 1
    have hc : clippedTime H hH.le (ts j) = ⟨ts j, hts j⟩ := Subtype.ext (s111t_clip_of_mem (hts j))
    have hif : (if side j = 0 then (Φ ω).1 else (Φ ω).2) = path (side j) ω := by
      generalize side j = i
      fin_cases i <;> simp [hΦ]
    simp only [pairedProcess, hc, hif]
    exact hpath_at (side j) ω ⟨ts j, hts j⟩
  have hae : (Ψ ∘ Φ) =ᵐ[P0] fun ω => (WithLp.toLp 2 fun j => OscDual.coord (X (side j) (ts j) ω) (alpha j) :
      EuclideanSpace ℝ (Fin n)) := by
    have hall : ∀ᵐ ω ∂P0, ∀ j, Z (side j) (ts j) ω = X (side j) (ts j) ω :=
      ae_all_iff.2 fun j => hZae (side j) (ts j) (hts j)
    filter_upwards [hall] with ω hω
    rw [hpt]
    congr 1; funext j
    rw [hω j]
  rw [Measure.map_congr hae]
  have hFcF : ∀ j, Fc (side j) (ts j) = F (side j) (ts j) := fun j => by
    funext α
    simp only [hFc_def, s111t_clip_of_mem (hts j)]
  have hlaw := s111t_vector_law (P := P0) (ι := Fin n) hg hind
    (fun j => X (side j) (ts j)) (fun j k => s111t_vec m e (Fc (side j) (ts j)) k)
    (fun j => hXg (side j) (ts j))
    (fun j => (s111t_vec_norm_sq_summable e (Fc (side j) (ts j)) (hFc _ _)).1)
    (fun j => s111t_coordCLM d m (alpha j))
  have hmat : (Matrix.of fun j k => inner ℝ (F (side j) (ts j) (alpha j)) (F (side k) (ts k) (alpha k)) :
      Matrix (Fin n) (Fin n) ℝ) = Matrix.of fun j l => ∑' k,
        (s111t_coordCLM d m (alpha j)) (s111t_vec m e (Fc (side j) (ts j)) k) *
          (s111t_coordCLM d m (alpha l)) (s111t_vec m e (Fc (side l) (ts l)) k) := by
    ext j l
    simp only [Matrix.of_apply, s111t_coordCLM_apply]
    have hcj : ∀ k, OscDual.coord (s111t_vec m e (Fc (side j) (ts j)) k) (alpha j) =
        inner ℝ (F (side j) (ts j) (alpha j)) (e k) := fun k => by
      rw [s111t_coord_vec e _ (hFc _ _), hFcF]
    have hcl : ∀ k, OscDual.coord (s111t_vec m e (Fc (side l) (ts l)) k) (alpha l) =
        inner ℝ (F (side l) (ts l) (alpha l)) (e k) := fun k => by
      rw [s111t_coord_vec e _ (hFc _ _), hFcF]
    simp_rw [hcj, hcl]
    rw [← e.tsum_inner_mul_inner]
    refine tsum_congr fun k => ?_
    rw [real_inner_comm (F (side l) (ts l) (alpha l)) (e k)]
  rw [hmat]
  exact hlaw

end HRS.MS.S111T
