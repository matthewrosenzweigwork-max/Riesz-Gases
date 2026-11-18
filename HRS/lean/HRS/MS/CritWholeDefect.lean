import HRS.MS.CritWholeVarComp
import HRS.Equilibrium.L49Aux14
import HRS.Equilibrium.L49Aux12

/-!
# S8.1 XS (S81d), CR09: reduction of the insertion defect to the diagonal `(N-1) ∫ H(λ g(x-y)) dμ`

Whole-space port of the torus `L49.l49_tonelli` / `l49_time_integral`.
`defect = cgf X P0 1 - P0[X]` (`wr13c2_insertionDefect_eq`), the generic Taylor identity gives
`ofReal defect = ∫⁻_{(0,1]} ofReal((1-t) λ² Var(∑ g(x-Y_i); pole t)) dt`; the pointwise comparison of CR08 (variance against
`n · squareRow`) is integrated against `∫_0^1 |log t| dt = 1`, Tonelli (`l49_lintegral_H`) identifies the diagonal,
`l49_AB_bound` does the compact-beta arithmetic.  Measurability of `defect` from `wr13d_log_theta`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

/-- Tonelli: `∫_0^1 (1-t) λ² n squareRow(t) dt = n ∫ H(λ g(x-y)) dμ` (in `ℝ≥0∞`). -/
theorem s81d_tonelli (hd : 2 ≤ d) (D : Data d M βm βp) (N : ℕ) (hN : 0 < N) (hβ0 : 0 < D.beta) {n : ℝ}
    (hn : 0 ≤ n) (x : Euc d)
    (hI : Integrable (fun y => taylorH ((D.beta / N) * critG d (x - y))) (mu D)) :
    ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * (D.beta / N) ^ 2 * (n * squareRow D N x t)) =
      ENNReal.ofReal (n * ∫ y, taylorH ((D.beta / N) * critG d (x - y)) ∂(mu D)) := by
  obtain ⟨Csl, hCsl0, hsl⟩ := s81c_sqRow_le (βm := βm) (βp := βp) (d := d) hd M
  have hd1 : 1 ≤ d := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set lam : ℝ := D.beta / N with hlam
  have hlam0 : 0 < lam := by positivity
  have hgm := s81b_critG_meas hd1
  set g : Euc d → ℝ := fun y => critG d (x - y) with hg
  have hgm' : Measurable g := hgm.comp (measurable_const.sub measurable_id)
  have hg0 : ∀ y, 0 ≤ g y := fun y => s81b_critG_nonneg hd1 _
  have h1 : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * lam ^ 2 * (n * squareRow D N x t)) =
      ∫⁻ y, ENNReal.ofReal (n * ((1 - t) * (lam * g y) ^ 2 * Real.exp (-t * (lam * g y)))) ∂(mu D) := by
    intro t ht
    obtain ⟨hint, -⟩ := hsl D N x t ht.1 hβ0 hN
    have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    have hc0 : 0 ≤ (1 - t) * lam ^ 2 * n := by positivity
    have e1 : (1 - t) * lam ^ 2 * (n * squareRow D N x t) = ((1 - t) * lam ^ 2 * n) * squareRow D N x t := by ring
    rw [e1, ENNReal.ofReal_mul hc0]
    unfold squareRow
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => by
      have := Real.exp_pos (-(t * (D.beta / N) * critG d (x - y)))
      unfold poleFactor
      positivity),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_mul hc0]
    congr 1
    have e2 : poleFactor D N x t y = Real.exp (-t * (lam * g y)) := by
      unfold poleFactor; congr 1; simp only [hg, hlam]; ring
    rw [e2]
    simp only [hg, hlam]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioc h1]
  have hFm : Measurable (Function.uncurry fun (t : ℝ) (y : Euc d) =>
      ENNReal.ofReal (n * ((1 - t) * (lam * g y) ^ 2 * Real.exp (-t * (lam * g y))))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (((measurable_const.sub measurable_fst).mul
        ((measurable_const.mul (hgm'.comp measurable_snd)).pow_const 2)).mul
        (Real.measurable_exp.comp ((measurable_neg.comp measurable_fst).mul
          (measurable_const.mul (hgm'.comp measurable_snd))))))
  haveI := s81c_prob D
  rw [lintegral_lintegral_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (ν := mu D)
    (f := fun (t : ℝ) (y : Euc d) =>
      ENNReal.ofReal (n * ((1 - t) * (lam * g y) ^ 2 * Real.exp (-t * (lam * g y)))))
    hFm.aemeasurable]
  have h2 : ∀ y, ∫⁻ t in Set.Ioc (0 : ℝ) 1,
      ENNReal.ofReal (n * ((1 - t) * (lam * g y) ^ 2 * Real.exp (-t * (lam * g y)))) =
      ENNReal.ofReal n * ENNReal.ofReal (taylorH (lam * g y)) := by
    intro y
    have hv : 0 ≤ lam * g y := mul_nonneg hlam0.le (hg0 y)
    have e : ∀ t : ℝ, ENNReal.ofReal (n * ((1 - t) * (lam * g y) ^ 2 * Real.exp (-t * (lam * g y)))) =
        ENNReal.ofReal n * ENNReal.ofReal ((1 - t) * (lam * g y) ^ 2 * Real.exp (-t * (lam * g y))) :=
      fun t => ENNReal.ofReal_mul hn
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, L49.l49_lintegral_H hv]
  simp_rw [h2]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hH0 : ∀ y, 0 ≤ taylorH (lam * g y) := fun y => L49.l49_H_nonneg _
  have hIg : Integrable (fun y => taylorH (lam * g y)) (mu D) := hI
  rw [← ofReal_integral_eq_lintegral_ofReal hIg (Eventually.of_forall hH0), ← ENNReal.ofReal_mul hn]

/-- The diagonal integrand `H(λ g(x - ·))` is `μ`-integrable (`H(v) ≤ v`). -/
theorem s81d_H_integrable (hd : 2 ≤ d) (D : Data d M βm βp) (N : ℕ) (hN : 0 < N) (hβ0 : 0 < D.beta) (x : Euc d) :
    Integrable (fun y => taylorH ((D.beta / N) * critG d (x - y))) (mu D) := by
  have hd1 : 1 ≤ d := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlam0 : 0 < D.beta / N := by positivity
  have hgi : Integrable (fun y => critG d (x - y)) (mu D) :=
    (wr13a_potential_bound hd1 (s81c_hs0 hd1) (s81c_hsd hd1) D.prob D.bound x).1
  have hgm : Measurable fun y => critG d (x - y) := (s81b_critG_meas hd1).comp (measurable_const.sub measurable_id)
  have hHm : Measurable fun v : ℝ => taylorH v := by unfold taylorH; fun_prop
  refine Integrable.mono' (hgi.const_mul (D.beta / N)) ((hHm.comp (hgm.const_mul _)).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  have hv : 0 ≤ (D.beta / N) * critG d (x - y) := mul_nonneg hlam0.le (s81b_critG_nonneg hd1 _)
  rw [Real.norm_eq_abs, abs_of_nonneg (L49.l49_H_nonneg _)]
  exact L49.l49_H_le_self hv

/-- `defect D N` is measurable (from the exact cavity equation). -/
theorem s81d_defect_meas (hd : 2 ≤ d) (D : Data d M βm βp) (hβ0 : 0 < D.beta) (N : ℕ) (hN : 2 ≤ N) :
    Measurable (defect D N) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  haveI := s81c_prob D
  have hs0 := s81c_hs0 hd1
  have hsd := s81c_hsd hd1
  have hlogθ : ∀ y, defect D (m + 2) y = Real.log (theta D (m + 2) y) -
      D.beta * convMeasure (critG d) (mu D) y +
      (D.beta / ((m + 2 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ) *
        convMeasure (critG d) (firstMarginal (cavity D (m + 2))) y +
      Real.log (wr13d_Z d ((d : ℝ) / 2) (m + 1) D.beta (mu D)) := by
    intro y
    have h := wr13d_log_theta hd hs0 hsd D.prob D.bound hβ0.le (n := m + 1) (by omega) y
    have h' : Real.log (theta D (m + 2) y) = D.beta * convMeasure (critG d) (mu D) y +
        (defect D (m + 2) y + -(D.beta / ((m + 2 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ) *
          convMeasure (critG d) (firstMarginal (cavity D (m + 2))) y) -
        Real.log (wr13d_Z d ((d : ℝ) / 2) (m + 1) D.beta (mu D)) := h
    linarith
  have hθm : Measurable (theta D (m + 2)) := wr13d_theta_meas hd hs0 hsd D.prob D.bound hβ0.le (m + 1)
  have hcm : Measurable (convMeasure (critG d) (mu D)) := s81b_conv_meas hd1 D
  have hνprob : IsProbabilityMeasure (firstMarginal (cavity D (m + 2))) := by
    have := wr13d_cavMarg_isProb hd hs0 hsd D.prob D.bound hβ0.le (n := m + 1) (by omega)
    exact this
  have hAm : Measurable (convMeasure (critG d) (firstMarginal (cavity D (m + 2)))) :=
    (((s81b_critG_meas hd1).comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.integral_prod_right'
      (ν := firstMarginal (cavity D (m + 2)))).measurable
  have : defect D (m + 2) = fun y => Real.log (theta D (m + 2) y) -
      D.beta * convMeasure (critG d) (mu D) y +
      (D.beta / ((m + 2 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ) *
        convMeasure (critG d) (firstMarginal (cavity D (m + 2))) y +
      Real.log (wr13d_Z d ((d : ℝ) / 2) (m + 1) D.beta (mu D)) := funext hlogθ
  rw [this]
  exact ((hθm.log.sub (hcm.const_mul _)).add (hAm.const_mul _)).add measurable_const

set_option maxHeartbeats 6400000 in
/-- **CR09** `interacting_diagonal_reduction` (statement = Pro skeleton, copied). -/
theorem s81d_interacting_diagonal_reduction (hd : 2 ≤ d) (M βm βp : ℝ)
    (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      Measurable (defect D N) ∧ ∀ x : Euc d,
        Integrable (fun t => (1 - t) * (D.beta / N) ^ 2 *
          Var[poleSum d N x; pole D N x t]) (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
        defect D N x = ∫ t in Set.Ioc (0 : ℝ) 1,
          (1 - t) * (D.beta / N) ^ 2 * Var[poleSum d N x; pole D N x t] ∧
        Integrable (fun y => taylorH ((D.beta / N) * critG d (x - y))) (mu D) ∧
        |defect D N x - ((N - 1 : ℕ) : ℝ) *
            (∫ y, taylorH ((D.beta / N) * critG d (x - y)) ∂(mu D))| ≤ C * rate N := by
  have hd1 : 1 ≤ d := by omega
  have hs0 := s81c_hs0 hd1
  have hsd := s81c_hsd hd1
  obtain ⟨C8, hC80, hC8⟩ := s81c_pole_variance_comparison hd M βm βp hβm hβ
  have hb : 0 ≤ max |Real.log βm| |Real.log βp| := (abs_nonneg _).trans (le_max_left _ _)
  obtain ⟨K, hK0, hK⟩ := L49.l49_AB_bound (d := d) (s := (d : ℝ) / 2) rfl (K₁ := C8) (K₂ := C8) (K₃ := C8)
    hC80 hC80 hC80 hb
  refine ⟨βp ^ 2 * K, by positivity, fun D N hN => ⟨?_, fun x => ?_⟩⟩
  · exact s81d_defect_meas hd D (hβm.trans_le D.beta_mem.1) N hN
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hββp : D.beta ≤ βp := D.beta_mem.2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  haveI := s81c_prob D
  have hconv := s81c_conv_le hd1 D
  haveI hP0 : IsProbabilityMeasure (cavity D N) := wr13a_cavityLaw_isProb hs0 hconv hβ0.le N
  set lam : ℝ := D.beta / N with hlam
  have hlam0 : 0 < lam := by positivity
  set n : ℝ := ((N - 1 : ℕ) : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hI := s81d_H_integrable hd D N (by omega) hβ0 x
  have hδ0 : 0 ≤ Real.sqrt (deltaN d ((d : ℝ) / 2) N) := Real.sqrt_nonneg _
  set a : ℝ := |Real.log lam| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  set A₀ : ℝ := C8 + C8 * Real.sqrt (1 + a) + C8 * Real.sqrt (deltaN d ((d : ℝ) / 2) N) * (1 + a) with hA₀
  set B₀ : ℝ := C8 + C8 * Real.sqrt (deltaN d ((d : ℝ) / 2) N) with hB₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  have hB₀0 : 0 ≤ B₀ := by positivity
  set I : ℝ := ∫ y, taylorH (lam * critG d (x - y)) ∂(mu D) with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun y => L49.l49_H_nonneg _
  -- the exponent and the Taylor identity
  have hXm := wr13c2_X_meas (d := d) (s := (d : ℝ) / 2) hs0 N D.beta x
  have hXb := wr13c2_X_le_zero (d := d) (s := (d : ℝ) / 2) hs0 hβ0.le N x
  have hXi := wr13c2_integrable_X hd hs0 hsd D.prob D.bound hβ0.le hN x
  have hTay := HRS.CavResp.taylor_identity (P := cavity D N) hXm hXb hXi
  obtain ⟨-, hdefeq⟩ := wr13c2_insertionDefect_eq hd hs0 hsd D.prob D.bound hβ0.le hN x
  have hD0 : 0 ≤ defect D N x := by
    show 0 ≤ insertionDefect d ((d : ℝ) / 2) N D.beta (mu D) x
    rw [hdefeq]
    linarith [HRS.MarginalAux.EF.ef_cgf_ge (P := cavity D N) hXm hXb hXi]
  have hVX : ∀ P : Measure (EucConfig d (N - 1)),
      Var[wr13c2_X d ((d : ℝ) / 2) N D.beta x; P] = lam ^ 2 * Var[poleSum d N x; P] := by
    intro P
    have := variance_const_mul (-(D.beta / N)) (poleSum d N x) P
    rw [neg_sq] at this
    exact this
  have hVt : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Var[wr13c2_X d ((d : ℝ) / 2) N D.beta x; (cavity D N).tilted (fun Y => t * wr13c2_X d ((d : ℝ) / 2) N D.beta x Y)] =
        lam ^ 2 * Var[poleSum d N x; pole D N x t] := by
    intro t ht
    rw [← wr13c2_poleLaw_eq_tilted hs0 hconv hβ0.le ht.1.le N x]
    exact hVX _
  have hDe : ENNReal.ofReal (defect D N x) =
      ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * lam ^ 2 * Var[poleSum d N x; pole D N x t]) := by
    have e1 : defect D N x = cgf (wr13c2_X d ((d : ℝ) / 2) N D.beta x) (cavity D N) 1 -
        ∫ Y, wr13c2_X d ((d : ℝ) / 2) N D.beta x Y ∂(cavity D N) := hdefeq
    rw [e1, hTay]
    refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [hVt t ht]; congr 1; ring
  set F : ℝ → ℝ := fun t => (1 - t) * lam ^ 2 * Var[poleSum d N x; pole D N x t] with hF
  have hF0 : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ F t := fun t ht =>
    mul_nonneg (mul_nonneg (by linarith [ht.2]) (sq_nonneg _)) (variance_nonneg _ _)
  have hFc : ContinuousOn F (Set.Ioc (0 : ℝ) 1) := by
    have hc := HRS.MarginalAux.EF.continuousOn_var (P := cavity D N) hXm hXb
    have hG : ContinuousOn (fun t : ℝ => (1 - t) * Var[wr13c2_X d ((d : ℝ) / 2) N D.beta x;
        (cavity D N).tilted (fun ω => t * wr13c2_X d ((d : ℝ) / 2) N D.beta x ω)]) (Set.Ioc (0 : ℝ) 1) :=
      (continuousOn_const.sub continuousOn_id).mul (hc.mono Set.Ioc_subset_Ioi_self)
    refine hG.congr fun t ht => ?_
    simp only [hF]; rw [hVt t ht]; ring
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] F :=
    (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hF0)
  have hFint : Integrable F (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨hFc.aestronglyMeasurable measurableSet_Ioc,
      (hasFiniteIntegral_iff_ofReal hnn).2 (by rw [← hDe]; exact ENNReal.ofReal_lt_top)⟩
  have hFeq : defect D N x = ∫ t in Set.Ioc (0 : ℝ) 1, F t := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn hFint.aestronglyMeasurable, ← hDe,
      ENNReal.toReal_ofReal hD0]
  refine ⟨hFint, hFeq, hI, ?_⟩
  -- the comparison with the diagonal
  have hRm : Measurable fun t : ℝ => ENNReal.ofReal (lam ^ 2 * n * (A₀ + B₀ * |Real.log t|)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (measurable_const.add (measurable_const.mul (Real.measurable_log.abs))))
  have hRint : ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (lam ^ 2 * n * (A₀ + B₀ * |Real.log t|)) =
      ENNReal.ofReal (lam ^ 2 * n * (A₀ + B₀)) := by
    have e : ∀ t : ℝ, lam ^ 2 * n * (A₀ + B₀ * |Real.log t|) =
        (lam ^ 2 * n * A₀) + (lam ^ 2 * n * B₀) * |Real.log t| := fun t => by ring
    simp_rw [e]
    rw [L49.l49_lintegral_log _ _ (by positivity) (by positivity)]
    congr 1; ring
  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ENNReal.ofReal (F t) ≤ ENNReal.ofReal ((1 - t) * lam ^ 2 * (n * squareRow D N x t)) +
        ENNReal.ofReal (lam ^ 2 * n * (A₀ + B₀ * |Real.log t|)) ∧
      ENNReal.ofReal ((1 - t) * lam ^ 2 * (n * squareRow D N x t)) ≤ ENNReal.ofReal (F t) +
        ENNReal.ofReal (lam ^ 2 * n * (A₀ + B₀ * |Real.log t|)) := by
    intro t ht
    obtain ⟨-, hbd⟩ := hC8 D N hN x t ht
    have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    set V : ℝ := Var[poleSum d N x; pole D N x t] with hV
    have hlogb : |Real.log (t * lam)| ≤ |Real.log t| + a := by
      have := L49.l49_log_mul_bound ht.1 hlam0
      simpa [ha] using this
    have hE := L49.l49_E_bound (K₁ := C8) (K₂ := C8) (K₃ := C8) (δs := Real.sqrt (deltaN d ((d : ℝ) / 2) N))
      (a := a) (ℓ := |Real.log t|) (L := |Real.log (t * lam)|)
      hC80 hC80 hδ0 ha0 (abs_nonneg (Real.log t)) (abs_nonneg _) (by linarith)
    have hbd' : |V - n * squareRow D N x t| ≤ n * (A₀ + B₀ * |Real.log t|) := by
      refine hbd.trans ?_
      have e : C8 * n * (1 + Real.sqrt (logMajorant D N t) +
          Real.sqrt (deltaN d ((d : ℝ) / 2) N) * logMajorant D N t) =
          n * (C8 + C8 * Real.sqrt (1 + |Real.log (t * lam)|) +
            C8 * Real.sqrt (deltaN d ((d : ℝ) / 2) N) * (1 + |Real.log (t * lam)|)) := by
        unfold logMajorant; rw [← hlam]; ring_nf
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ hn0
      have := hE
      simp only [hA₀, hB₀]
      linarith
    have hw0 : 0 ≤ (1 - t) * lam ^ 2 := by positivity
    have hw1 : (1 - t) * lam ^ 2 ≤ lam ^ 2 := by nlinarith [ht.1.le, sq_nonneg lam]
    have hRn : 0 ≤ n * (A₀ + B₀ * |Real.log t|) := by positivity
    have hwR : (1 - t) * lam ^ 2 * (n * (A₀ + B₀ * |Real.log t|)) ≤ lam ^ 2 * n * (A₀ + B₀ * |Real.log t|) := by
      have := mul_le_mul_of_nonneg_right hw1 hRn
      nlinarith
    have hRn' : 0 ≤ lam ^ 2 * n * (A₀ + B₀ * |Real.log t|) := by positivity
    have hFt : F t = (1 - t) * lam ^ 2 * V := rfl
    have hup : F t ≤ (1 - t) * lam ^ 2 * (n * squareRow D N x t) + lam ^ 2 * n * (A₀ + B₀ * |Real.log t|) := by
      have := (abs_le.1 hbd').2
      rw [hFt]
      nlinarith [mul_le_mul_of_nonneg_left (show V ≤ n * squareRow D N x t + n * (A₀ + B₀ * |Real.log t|) by linarith) hw0]
    have hlo : (1 - t) * lam ^ 2 * (n * squareRow D N x t) ≤ F t + lam ^ 2 * n * (A₀ + B₀ * |Real.log t|) := by
      have := (abs_le.1 hbd').1
      rw [hFt]
      nlinarith [mul_le_mul_of_nonneg_left (show n * squareRow D N x t ≤ V + n * (A₀ + B₀ * |Real.log t|) by linarith) hw0]
    constructor
    · exact (ENNReal.ofReal_le_ofReal hup).trans ENNReal.ofReal_add_le
    · exact (ENNReal.ofReal_le_ofReal hlo).trans ENNReal.ofReal_add_le
  have hT := s81d_tonelli hd D N (by omega) hβ0 hn0 x hI
  have hup : ENNReal.ofReal (defect D N x) ≤
      ENNReal.ofReal (n * I) + ENNReal.ofReal (lam ^ 2 * n * (A₀ + B₀)) := by
    rw [hDe, ← hT, ← hRint, ← lintegral_add_right _ hRm]
    exact setLIntegral_mono' measurableSet_Ioc fun t ht => (hpt t ht).1
  have hlo : ENNReal.ofReal (n * I) ≤
      ENNReal.ofReal (defect D N x) + ENNReal.ofReal (lam ^ 2 * n * (A₀ + B₀)) := by
    rw [hDe, ← hRint, ← lintegral_add_right _ hRm, ← hT]
    exact setLIntegral_mono' measurableSet_Ioc fun t ht => (hpt t ht).2
  have hErr0 : 0 ≤ lam ^ 2 * n * (A₀ + B₀) := by positivity
  have hnI0 : 0 ≤ n * I := mul_nonneg hn0 hI0
  rw [← ENNReal.ofReal_add hnI0 hErr0] at hup
  rw [← ENNReal.ofReal_add hD0 hErr0] at hlo
  have h1 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hup
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hlo
  have hlog : |Real.log D.beta| ≤ max |Real.log βm| |Real.log βp| := by
    rw [abs_le]
    constructor
    · have h1 : Real.log βm ≤ Real.log D.beta := Real.log_le_log hβm D.beta_mem.1
      have h2 : -|Real.log βm| ≤ Real.log βm := neg_abs_le _
      have h3 : |Real.log βm| ≤ max |Real.log βm| |Real.log βp| := le_max_left _ _
      linarith
    · have h1 : Real.log D.beta ≤ Real.log βp := Real.log_le_log hβ0 hββp
      have h2 : Real.log βp ≤ |Real.log βp| := le_abs_self _
      have h3 : |Real.log βp| ≤ max |Real.log βm| |Real.log βp| := le_max_right _ _
      linarith
  have hAB : A₀ + B₀ ≤ K * Real.sqrt (Real.log N) := hK N hN D.beta hβ0 hlog
  have hnN : n ≤ N := by
    simp only [hn]; exact_mod_cast Nat.sub_le N 1
  have hlam2 : lam ^ 2 * n ≤ βp ^ 2 / N := by
    calc lam ^ 2 * n ≤ lam ^ 2 * N := mul_le_mul_of_nonneg_left hnN (sq_nonneg _)
      _ = D.beta ^ 2 / N := by simp only [hlam]; field_simp
      _ ≤ βp ^ 2 / N := div_le_div_of_nonneg_right (pow_le_pow_left₀ hβ0.le hββp 2) hN0.le
  have hfin : lam ^ 2 * n * (A₀ + B₀) ≤ βp ^ 2 * K * rate N := by
    calc lam ^ 2 * n * (A₀ + B₀) ≤ (βp ^ 2 / N) * (K * Real.sqrt (Real.log N)) :=
          mul_le_mul hlam2 hAB (by positivity) (by positivity)
      _ = βp ^ 2 * K * rate N := by unfold rate; ring
  rw [abs_le]
  constructor <;> linarith

end HRS.Whole.S81b
