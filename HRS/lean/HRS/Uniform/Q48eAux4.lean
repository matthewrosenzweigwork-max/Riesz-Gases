import HRS.Uniform.Q48eAux3

/-!
# Q48e, part 4: plain-evolution properties and quasi-contractivity of the frozen dual evolution

For every `Vev` with `IsDualEvolution` for the frozen thermal coefficient at a level `m ≥ m_* + d`:

* `vev_self`, `vev_comp`: `Vev t t = 1` and the cocycle property (from duality, `frozen_self_pos`, `frozen_smooth`,
  `frozen_semigroup` and `negSobolev_ext`);
* `vev_quasi`: `‖Vev t u‖ ≤ e^{c (t-u)}` with `c` independent of `Vev`;
* `vev_cont`: strong continuity on the simplex (coordinatewise continuity from `frozen_coeff_cont`, tail control from
  the weighted bound at level `m - d`, `continuousOn_of_tail`, density of finite vectors).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q48e

open HRS HRS.PDE HRS.Uniform.Q48b

variable {d : ℕ}

theorem vev_self (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρ : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) {m : ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev)
    (t : ℝ) (ht : 0 ≤ t) : Vev t t = 1 := by
  refine ContinuousLinearMap.ext fun z => negSobolev_ext fun φ hφ => ?_
  rw [hdual t t ht le_rfl z φ hφ, frozen_self_pos hd s hs0 hsd β hβ V hV ρβ hprob hρ hpos φ hφ t ht]
  rfl

theorem vev_comp (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρ : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) {m : ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev)
    (a r t : ℝ) (ha : 0 ≤ a) (har : a ≤ r) (hrt : r ≤ t) :
    (Vev t r).comp (Vev r a) = Vev t a := by
  have hr0 : 0 ≤ r := ha.trans har
  refine ContinuousLinearMap.ext fun z => negSobolev_ext fun φ hφ => ?_
  show NegSobolev.eval (Vev t r (Vev r a z)) φ = NegSobolev.eval (Vev t a z) φ
  rw [hdual r t hr0 hrt (Vev r a z) φ hφ,
    hdual a r ha har z _ (frozen_smooth hd s hs0 hsd β hβ V hV ρβ hprob hρ hpos φ hφ r t hr0 hrt),
    hdual a t ha (har.trans hrt) z φ hφ,
    ← frozen_semigroup hd s hs0 hsd β hβ V hV ρβ hprob hρ hpos φ hφ a r t ha har hrt]

theorem vev_quasi (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρ : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) (m : ℝ) (hm : (mStar d : ℝ) ≤ m) :
    ∃ c : ℝ, ∀ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
      IsDualEvolution (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev →
      ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp (c * (t - u)) := by
  obtain ⟨c, hc⟩ := q48e_level hd s hs0 hsd β hβ V hV ρβ hprob hρ hpos m hm
  refine ⟨c, fun Vev hdual u t hu hut => ?_⟩
  exact q48b_opNorm_le (Vev t u) _ (Real.exp_pos _).le
    (hc m u t hu hut (Vev t u) (fun z φ hφ => hdual u t hu hut z φ hφ))

theorem tendsto_truncE {m : ℝ} (x : NegSobolev d m) :
    Tendsto (fun G : Finset (NonzeroLattice d) => truncE m G (fun l => NegSobolev.coord x l)) atTop (𝓝 x) := by
  classical
  have hs := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by norm_num)
    (x : lp (fun _ : NonzeroLattice d => ℝ) 2)
  have heq : ∀ G : Finset (NonzeroLattice d), truncE m G (fun l => NegSobolev.coord x l) =
      ∑ k ∈ G, lp.single 2 k (NegSobolev.coord x k) := by
    intro G
    refine lp.ext (funext fun l => ?_)
    have h1 : NegSobolev.coord (truncE m G (fun l => NegSobolev.coord x l)) l =
        if l ∈ G then NegSobolev.coord x l else 0 := coord_truncE _ _ _ _
    have h2 : ((∑ k ∈ G, lp.single 2 k (NegSobolev.coord x k) :
        lp (fun _ : NonzeroLattice d => ℝ) 2) : NonzeroLattice d → ℝ) l =
        if l ∈ G then NegSobolev.coord x l else 0 := by
      rw [lp.coeFn_sum, Finset.sum_apply]
      simp [lp.single_apply, Pi.single_apply]
    exact h1.trans h2.symm
  have hs' : Tendsto (fun G : Finset (NonzeroLattice d) =>
      ∑ k ∈ G, lp.single 2 k (NegSobolev.coord x k)) atTop
      (𝓝 (x : lp (fun _ : NonzeroLattice d => ℝ) 2)) := hs
  exact hs'.congr fun G => (heq G).symm

theorem truncE_eq_fin {m : ℝ} (x : NegSobolev d m) (G : Finset (NonzeroLattice d)) :
    truncE m G (fun l => NegSobolev.coord x l) =
      q48bFin m G (fun l => q48bW l ^ m * NegSobolev.coord x l) := by
  unfold truncE q48bFin
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [← mul_assoc, q48b_rpow_neg_mul (q48bW_pos l) m, one_mul]

theorem weight_identity {w : ℝ} (hw : 0 < w) (e m fc : ℝ) :
    w ^ (2 * e) * (w ^ (-m) * fc) ^ 2 = w ^ (-2 * (m - e)) * fc ^ 2 := by
  rw [mul_pow, q48b_rpow_sq hw, ← mul_assoc, ← Real.rpow_add hw]
  congr 2
  ring

theorem vev_cont (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρ : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) (m : ℝ) (hm : (mStar d : ℝ) + d ≤ m)
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev)
    (T : ℝ) (hT : 0 ≤ T) (x : NegSobolev d m) :
    ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 x) {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} := by
  classical
  set Sset : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} with hSset
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmS : (mStar d : ℝ) ≤ m := by linarith
  obtain ⟨c, hc⟩ := vev_quasi hd s hs0 hsd β hβ V hV ρβ hprob hρ hpos m hmS
  obtain ⟨c', hc'⟩ := q48e_level hd s hs0 hsd β hβ V hV ρβ hprob hρ hpos (m - d) (by linarith)
  have hexp : ∀ (c₀ : ℝ) (p : ℝ × ℝ), p ∈ Sset → Real.exp (c₀ * (p.1 - p.2)) ≤ Real.exp (|c₀| * T) := by
    intro c₀ p hp
    refine Real.exp_le_exp.2 ?_
    have h1 : c₀ * (p.1 - p.2) ≤ |c₀| * (p.1 - p.2) :=
      mul_le_mul_of_nonneg_right (le_abs_self c₀) (by linarith [hp.2.1])
    have h2 : |c₀| * (p.1 - p.2) ≤ |c₀| * T :=
      mul_le_mul_of_nonneg_left (by linarith [hp.1, hp.2.2]) (abs_nonneg c₀)
    linarith
  have hBm : ∀ p ∈ Sset, ‖Vev p.1 p.2‖ ≤ Real.exp (|c| * T) := fun p hp =>
    (hc Vev hdual p.2 p.1 hp.1 hp.2.1).trans (hexp c p hp)
  -- finite vectors
  have hfin : ∀ (G : Finset (NonzeroLattice d)) (ζ : NonzeroLattice d → ℝ),
      ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 (q48bFin m G ζ)) Sset := by
    intro G ζ
    set z := q48bFin m G ζ with hz
    refine continuousOn_of_tail hd (F := fun p : ℝ × ℝ => Vev p.1 p.2 z) (S := Sset) ?_
      (Real.exp (|c'| * T) * Real.sqrt (∑ k ∈ G, q48bW k ^ (-2 * (m - d)) * ζ k ^ 2)) ?_
    · intro l
      have key : ∀ p ∈ Sset, NegSobolev.coord (Vev p.1 p.2 z) l = q48bW l ^ (-m) *
          ∑ k ∈ G, ζ k * Torus.funRealCoeff
            (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) p.2 p.1
              (q48bTest {l} fun _ => 1)) k := by
        intro p hp
        rw [q48b_coord_eq_fourier, fourierCoeff_eq_eval,
          hdual p.2 p.1 hp.1 hp.2.1 z _ (q48bTest_smooth _ _), hz, q48b_eval_fin]
      refine ContinuousOn.congr (f := fun p : ℝ × ℝ => q48bW l ^ (-m) *
          ∑ k ∈ G, ζ k * Torus.funRealCoeff
            (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) p.2 p.1
              (q48bTest {l} fun _ => 1)) k) ?_ key
      refine continuousOn_const.mul (continuousOn_finsetSum G fun k _ => continuousOn_const.mul ?_)
      exact frozen_coeff_cont hd s hs0 hsd β hβ V hV ρβ hprob hρ hpos _ (q48bTest_smooth _ _) k T hT
    · intro p hp H
      have hW := hc' m p.2 p.1 hp.1 hp.2.1 (Vev p.1 p.2) (fun z φ hφ => hdual p.2 p.1 hp.1 hp.2.1 z φ hφ) G H ζ
      have hM2 : Real.exp (c' * (p.1 - p.2)) ^ 2 ≤ Real.exp (|c'| * T) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos _).le (hexp c' p hp) 2
      have hN0 : 0 ≤ ∑ k ∈ G, q48bW k ^ (-2 * (m - d)) * ζ k ^ 2 :=
        Finset.sum_nonneg fun k _ => mul_nonneg (Real.rpow_nonneg (q48bW_pos k).le _) (sq_nonneg _)
      have heq : ∀ l, q48bW l ^ (2 * (d : ℝ)) * NegSobolev.coord (Vev p.1 p.2 z) l ^ 2 =
          q48bW l ^ (-2 * (m - d)) * (∑ k ∈ G, q48bMat m (Vev p.1 p.2) l k * ζ k) ^ 2 := by
        intro l
        rw [q48b_coord_eq_fourier, hz, q48bFin_V]
        exact weight_identity (q48bW_pos l) _ _ _
      simp_rw [heq]
      refine hW.trans ?_
      rw [mul_pow, Real.sq_sqrt hN0]
      exact mul_le_mul_of_nonneg_right hM2 hN0
  -- general vectors
  have hx : ∀ G : Finset (NonzeroLattice d), ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2
      (truncE m G (fun l => NegSobolev.coord x l))) Sset := fun G => by
    rw [truncE_eq_fin]; exact hfin G _
  have hunif : TendstoUniformlyOn (fun G (p : ℝ × ℝ) => Vev p.1 p.2
      (truncE m G (fun l => NegSobolev.coord x l))) (fun p => Vev p.1 p.2 x) atTop Sset := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set Bm : ℝ := Real.exp (|c| * T) with hBmdef
    have hBm0 : 0 < Bm := Real.exp_pos _
    have hlim := Metric.tendsto_nhds.1 (tendsto_truncE x) (ε / (Bm + 1)) (by positivity)
    filter_upwards [hlim] with G hG p hp
    rw [dist_eq_norm, ← map_sub]
    have h1 : ‖Vev p.1 p.2 (x - truncE m G (fun l => NegSobolev.coord x l))‖ ≤
        Bm * ‖x - truncE m G (fun l => NegSobolev.coord x l)‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hBm p hp) (norm_nonneg _))
    have h2 : ‖x - truncE m G (fun l => NegSobolev.coord x l)‖ < ε / (Bm + 1) := by
      rw [dist_eq_norm] at hG; rwa [norm_sub_rev]
    calc _ ≤ Bm * ‖x - truncE m G (fun l => NegSobolev.coord x l)‖ := h1
      _ ≤ Bm * (ε / (Bm + 1)) := mul_le_mul_of_nonneg_left h2.le hBm0.le
      _ < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
  exact hunif.continuousOn (Filter.Eventually.of_forall hx).frequently

end HRS.Uniform.Q48e
