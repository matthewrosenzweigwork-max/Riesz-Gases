import HRS.MS.UlMildAux3

/-!
# UL-4b (S5.1 infrastructure, supplement foundation packet): admissibility `G1` of the Duhamel operator, part 1

Not a manuscript row.  Files `UlMildAux4` (this file: closure toolkit, closed-limit lemma `ul4b_lim`,
`ulPert` and `P_t ulPert` on the closure, Riemann sums in `E_k`) and `UlMildAux5` (continuity of the
Duhamel integral, closure membership, `UlDuhamelAdm`, unconditional `ul_mild_exists`).
Helper lemmas carry the prefix `ul4b_`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.Ul
open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW
open HRS.MS.Lc HRS.MD.EQLawPath

variable {d : ℕ}

section Basic
variable {k : ℕ} {θ : Euc d → ℝ}

/-- pointwise strong continuity on a compact interval is uniform -/
theorem ul4b_unif_of_reg (hθ : IsUlCutoff θ) {T : ℝ} {w : ℝ → Euc d → ℝ}
    (hw : UlReg k θ T w) : UlUReg k θ T w := by
  obtain ⟨Cn, hCn, hneg⟩ := ul4_neg (k := k) hθ
  refine ⟨hw.mem, fun ε hε => ?_⟩
  have hε' : 0 < ε / (1 + Cn) := by positivity
  have hex : ∀ σ0 : Icc (0 : ℝ) T, ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Icc (0 : ℝ) T, |σ - σ0| < δ →
      ulNormE k θ (fun x => w σ x - w σ0 x) ≤ ENNReal.ofReal (ε / (1 + Cn)) :=
    fun σ0 => hw.cont σ0 σ0.2 _ hε'
  choose δ hδ hδ' using hex
  obtain ⟨r, hr, hball⟩ := lebesgue_number_lemma_of_metric (s := Icc (0 : ℝ) T)
    (ι := Icc (0 : ℝ) T) (c := fun i => Metric.ball (i : ℝ) (δ i)) isCompact_Icc
    (fun i => Metric.isOpen_ball)
    (fun σ hσ => mem_iUnion.2 ⟨⟨σ, hσ⟩, Metric.mem_ball_self (hδ ⟨σ, hσ⟩)⟩)
  refine ⟨r, hr, fun σ hσ σ' hσ' hd => ?_⟩
  obtain ⟨i, hi⟩ := hball σ' hσ'
  have h1 : σ ∈ Metric.ball (i : ℝ) (δ i) := hi (by rw [Metric.mem_ball, Real.dist_eq]; exact hd)
  have h2 : σ' ∈ Metric.ball (i : ℝ) (δ i) := hi (Metric.mem_ball_self hr)
  have a1 := hδ' i σ hσ (by simpa [Real.dist_eq] using h1)
  have a2 := hδ' i σ' hσ' (by simpa [Real.dist_eq] using h2)
  have e : (fun x => w σ x - w σ' x) = fun x => (w σ x - w i x) + (-(w σ' x - w i x)) := by
    funext x; ring
  rw [e]
  refine (ul0_ulNormE_add k θ _ _).trans ?_
  calc _ ≤ ENNReal.ofReal (ε / (1 + Cn)) + ENNReal.ofReal Cn * ENNReal.ofReal (ε / (1 + Cn)) :=
        add_le_add a1 ((hneg _).trans (mul_le_mul' le_rfl a2))
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul hCn.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; field_simp

theorem ul4b_closure_of_ccc (k : ℕ) (θ : Euc d → ℝ) {g : Euc d → ℝ} (hg : IsCcInftyPlusConst g) :
    UlClosure k θ g := by
  refine ⟨contDiff_infty.1 (ul4_ccc_props hg).1 2, fun ε hε => ⟨g, hg, ?_⟩⟩
  have : ulNormE k θ (fun x => g x - g x) = 0 := by simp [ulNormE, HRS.MS.UlocCut.uc_zero]
  rw [this]; exact bot_le

/-- **A closed-limit lemma.**  A pointwise limit of closure elements converging fast in `ulNormE`
lies in `UlClosure`. -/
theorem ul4b_lim (hk : (2 : ℝ) + (d : ℝ) / 2 < k) (hθ : IsUlCutoff θ) {f : Euc d → ℝ}
    {a : ℕ → Euc d → ℝ} (ha : ∀ n, UlClosure k θ (a n))
    (hn : ∀ n, ulNormE k θ (fun x => f x - a n x) ≤ ENNReal.ofReal (1 / 2 ^ n))
    (hp : ∀ x, Tendsto (fun n => a n x) atTop (𝓝 (f x))) : UlClosure k θ f := by
  obtain ⟨Ct, hCt, htsum⟩ := ul4_closure_tsum hk hθ
  obtain ⟨Cn, hCn, hneg⟩ := ul4_neg (k := k) hθ
  have hk0 : ((0 : ℕ) : ℝ) + (d : ℝ) / 2 < k := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    push_cast; linarith
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 0 hk0 θ hθ
  set b : ℕ → Euc d → ℝ := fun n => match n with
    | 0 => a 0
    | n + 1 => fun x => a (n + 1) x - a n x with hb
  have hbm : ∀ n, UlClosure k θ (b n) := by
    intro n; cases n with
    | zero => exact ha 0
    | succ n => exact ul4_closure_sub hθ (ha (n + 1)) (ha n)
  have hbn : ∀ n : ℕ, (ulNormE k θ (b (n + 1))).toReal ≤ (1 + Cn) * (1 / 2) ^ n := by
    intro n
    have e : b (n + 1) = fun x => (f x - a n x) + (-(f x - a (n + 1) x)) := by
      funext x; simp only [hb]; ring
    have h1 : ulNormE k θ (b (n + 1)) ≤ ENNReal.ofReal ((1 + Cn) * (1 / 2) ^ n) := by
      rw [e]
      refine (ul0_ulNormE_add k θ _ _).trans ?_
      calc _ ≤ ENNReal.ofReal (1 / 2 ^ n) + ENNReal.ofReal Cn * ENNReal.ofReal (1 / 2 ^ (n + 1)) :=
            add_le_add (hn n) ((hneg _).trans (mul_le_mul' le_rfl (hn (n + 1))))
        _ ≤ ENNReal.ofReal (1 / 2 ^ n) + ENNReal.ofReal Cn * ENNReal.ofReal (1 / 2 ^ n) := by
            exact add_le_add le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
              (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 ^ n)
                (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ n)))))
        _ = ENNReal.ofReal ((1 + Cn) * (1 / 2) ^ n) := by
            rw [← ENNReal.ofReal_mul hCn.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; rw [one_div, one_div, inv_pow]; ring
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hsum : Summable fun n => (ulNormE k θ (b n)).toReal := by
    rw [← summable_nat_add_iff 1]
    exact Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) hbn
      (summable_geometric_two.mul_left (1 + Cn))
  have hpt : ∀ n x, |b n x| ≤ Ccb * (ulNormE k θ (b n)).toReal := fun n x => by
    have := ul3_cb_apply (hcb _ (hbm n)).1 (Nat.zero_le 0) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans (hcb _ (hbm n)).2
  have hsx : ∀ x, Summable fun n => b n x := fun x =>
    Summable.of_norm_bounded (hsum.mul_left Ccb) fun n => by rw [Real.norm_eq_abs]; exact hpt n x
  have hps : ∀ N x, ∑ i ∈ Finset.range (N + 1), b i x = a N x := by
    intro N x
    induction N with
    | zero => simp [hb]
    | succ N ih => rw [Finset.sum_range_succ, ih]; simp only [hb]; ring
  have hfx : ∀ x, ∑' n, b n x = f x := fun x => by
    refine tendsto_nhds_unique ((hsx x).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)) ?_
    exact (hp x).congr fun N => (hps N x).symm
  obtain ⟨h1, -⟩ := htsum b hbm hsum
  have e : f = fun x => ∑' n, b n x := funext fun x => (hfx x).symm
  rw [e]; exact h1

/-! ### `ulPert` of `C_c^∞ + const` lies in the closure -/

theorem ul4b_decay_of_sym {p : ℝ} (hp : p ≤ -1) {g : Euc d → ℝ} (hg : UlSym p g) (m : ℕ) {ε : ℝ}
    (hε : 0 < ε) : ∃ R : ℝ, ∀ x : Euc d, R ≤ ‖x‖ → ‖iteratedFDeriv ℝ m g x‖ ≤ ε := by
  obtain ⟨C, hC0, hC⟩ := hg.2 m
  refine ⟨C / ε, fun x hx => ?_⟩
  have hpos : 0 < 1 + ‖x‖ := ult_w_pos x
  have h1 : (1 + ‖x‖) ^ (p - (m : ℝ)) ≤ (1 + ‖x‖)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x])
      (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  calc ‖iteratedFDeriv ℝ m g x‖ ≤ C * (1 + ‖x‖) ^ (p - (m : ℝ)) := hC x
    _ ≤ C * (1 + ‖x‖)⁻¹ := mul_le_mul_of_nonneg_left h1 hC0
    _ ≤ ε := by
        rw [← div_eq_mul_inv, div_le_iff₀ hpos]
        calc C = (C / ε) * ε := by field_simp
          _ ≤ (1 + ‖x‖) * ε := mul_le_mul_of_nonneg_right (by linarith [norm_nonneg x]) hε.le
          _ = ε * (1 + ‖x‖) := by ring

theorem ul4b_closure_of_sym (k : ℕ) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) {p : ℝ} (hp : p ≤ -1)
    {g : Euc d → ℝ} (hg : UlSym p g) : UlClosure k θ g := by
  refine ulClosure_of_decay k θ hθ g 0 hg.1 (fun ε hε => ?_)
    (fun j _ _ ε hε => ul4b_decay_of_sym hp hg j hε)
  obtain ⟨R, hR⟩ := ul4b_decay_of_sym hp hg 0 hε
  refine ⟨R, fun x hx => ?_⟩
  have := hR x hx
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs, ← sub_zero (g x)] at this

theorem ul4b_nl_ccc {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) {ρ : Euc d → ℝ}
    (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) (k : ℕ) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ)
    {e : Euc d → ℝ} (he : IsCcInftyPlusConst e) : UlClosure k θ (ulNL s M ρ e) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : ulNL s M ρ e = fun _ => 0 := by funext x; simp [ulNL]
    rw [this]; exact ul4_closure_zero
  obtain ⟨ψ, rfl⟩ := hρ
  obtain ⟨hE, -, hfc⟩ := ul4_ccc_props he
  have hfd : ContDiff ℝ ∞ (fderiv ℝ e) := (contDiff_infty_iff_fderiv.1 hE).2
  have hrap : ∀ j : Fin d, UlRapid (fun y => ψ y * (Torus.matVec M.transpose (gradient e y)) j) := by
    intro j
    have hGe : (fun y => (Torus.matVec M.transpose (gradient e y)) j) =
        fun y => ∑ l : Fin d, M.transpose j l * fderiv ℝ e y (EuclideanSpace.single l (1 : ℝ)) := by
      funext y
      simp only [Torus.matVec, ← ult_grad_apply]
      simp [Matrix.mulVec, dotProduct]
    have hsm : ContDiff ℝ ∞ (fun y => (Torus.matVec M.transpose (gradient e y)) j) := by
      rw [hGe]
      exact ContDiff.sum fun l _ => contDiff_const.mul (hfd.clm_apply contDiff_const)
    have hcs : HasCompactSupport (fun y => (Torus.matVec M.transpose (gradient e y)) j) := by
      rw [hGe]
      exact ul4_hcs_sum Finset.univ _ fun l _ =>
        hfc.comp_left (g := fun L : Euc d →L[ℝ] ℝ => M.transpose j l * L (EuclideanSpace.single l (1 : ℝ)))
          (by simp)
    have hS := ult_schwartz_rapid (hcs.toSchwartzMap hsm)
    refine ult_sym_rapid fun q => ?_
    have := ult_sym_mul (ult_rapid_sym (ult_schwartz_rapid ψ) q) (ult_rapid_sym hS 0)
    simpa using this
  have hsym : UlSym (-(s + 1)) (ulNL s M ψ e) := by
    have := ult_sym_sum (p := -(s + 1)) Finset.univ _ fun j _ =>
      ult_K_comp_sym hd hs0 hsd (hrap j) j
    exact this
  exact ul4b_closure_of_sym k θ hθ (by linarith) hsym

theorem ul4b_pert_ccc {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) {ρ : Euc d → ℝ}
    (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) {c : Euc d → Euc d} (hc : IsSmoothBounded c)
    (k : ℕ) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) {e : Euc d → ℝ} (he : IsCcInftyPlusConst e) :
    UlClosure k θ (ulPert s M ρ c e) := by
  obtain ⟨hE, -, hfc⟩ := ul4_ccc_props he
  have hfd : ContDiff ℝ ∞ (fderiv ℝ e) := (contDiff_infty_iff_fderiv.1 hE).2
  have hA : ContDiff ℝ ∞ (fun x => fderiv ℝ e x (c x)) := hfd.clm_apply hc.1
  have hAc : HasCompactSupport (fun x => fderiv ℝ e x (c x)) :=
    hfc.mono' fun x hx => subset_closure (by
      intro h0; apply hx; simp [h0])
  have hpe : ulPert s M ρ c e = fun x => fderiv ℝ e x (c x) - ulNL s M ρ e x := by
    funext x; simp only [ulPert, ul4_inner_eq]
  rw [hpe]
  exact ul4_closure_sub hθ (ul4b_closure_of_ccc k θ ⟨_, 0, hA, hAc, by funext x; simp⟩)
    (ul4b_nl_ccc hs0 hsd M hρ k θ hθ he)

end Basic

/-- the standing hypotheses of the packet -/
structure UlHyp (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (c : Euc d → Euc d) (ν : ℝ)
    (k : ℕ) (θ : Euc d → ℝ) : Prop where
  hs0 : 0 ≤ s
  hsd : s < d
  hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ
  hc : IsSmoothBounded c
  hν : 0 < ν
  hk : (4 : ℝ) + (d : ℝ) / 2 < k
  hθ : IsUlCutoff θ

section Pert
variable {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ρ : Euc d → ℝ} {c : Euc d → Euc d} {ν : ℝ} {k : ℕ}
  {θ : Euc d → ℝ}

theorem UlHyp.hk2 (H : UlHyp s M ρ c ν k θ) : (2 : ℝ) + (d : ℝ) / 2 < k := by
  have := H.hk; have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  linarith

theorem UlHyp.hk0 (H : UlHyp s M ρ c ν k θ) : (d : ℝ) / 2 < k := by
  have := H.hk; have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  linarith

/-- `P_t ∘ ulPert` is additive on `C_b^4` -/
theorem ul4b_P_pert_sub (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    {u v : Euc d → ℝ} (hu : MemCb 4 u) (hv : MemCb 4 v) :
    ouSg Q ν t (ulPert s M ρ c (fun y => u y - v y)) =
      fun x => ouSg Q ν t (ulPert s M ρ c u) x - ouSg Q ν t (ulPert s M ρ c v) x := by
  obtain ⟨Cp, hCp0, hpcb⟩ := ul4_pert_cb H.hs0 H.hsd M ρ H.hρ H.hc
  obtain ⟨B1, hB1⟩ := ul3C_bdd_of_cb (hpcb _ hu).1
  obtain ⟨B2, hB2⟩ := ul3C_bdd_of_cb (hpcb _ hv).1
  have e : ulPert s M ρ c (fun y => u y - v y) = fun y => ulPert s M ρ c u y - ulPert s M ρ c v y := by
    funext y; exact ul4_pert_sub H.hs0 H.hsd M ρ H.hρ c hu hv y
  rw [e]
  exact ul3C_sub_lin Q ν t (hpcb _ hu).1.1.continuous.measurable (hpcb _ hv).1.1.continuous.measurable hB1 hB2

/-- `P_t ulPert` maps the closure into the closure for `t > 0` -/
theorem ul4b_P_pert_mem (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) (T : ℝ) {t : ℝ}
    (ht : 0 < t) (htT : t ≤ T) {u : Euc d → ℝ} (hu : UlClosure k θ u) :
    UlClosure k θ (ouSg Q ν t (ulPert s M ρ c u)) := by
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 4 H.hk θ H.hθ
  obtain ⟨Cp, hCp0, hpcb⟩ := ul4_pert_cb H.hs0 H.hsd M ρ H.hρ H.hc
  obtain ⟨K, hK, hest⟩ := ul4_pert_est H.hs0 H.hsd M ρ H.hρ H.hc Q H.hν T k H.hk θ H.hθ
  have hu4 := (hcb u hu).1
  have hG := (hpcb u hu4).1
  have hC2 : ContDiff ℝ 2 (ouSg Q ν t (ulPert s M ρ c u)) := by
    have := (ul3C_smooth Q ν t 2 hG.1 (M := cbNorm 2 (ulPert s M ρ c u))
      (fun i hi y => ul3_cb_apply hG hi y)).1
    exact_mod_cast this
  refine ul4_closure_approx hC2 fun ε hε => ?_
  set A : ℝ := K * t ^ (-ul4gam d s) with hA
  have hA0 : 0 ≤ A := by have := Real.rpow_nonneg ht.le (-ul4gam d s); positivity
  obtain ⟨e', he', hle⟩ := hu.2 (ε / (A + 1)) (by positivity)
  refine ⟨ouSg Q ν t (ulPert s M ρ c e'), ouSg_mem_ulClosure Q H.hν ht.le k θ H.hθ H.hk2
    (ul4b_pert_ccc H.hs0 H.hsd M H.hρ H.hc k θ H.hθ he'), ?_⟩
  have hd := ul0_closure_sub_ccc k θ hu he'
  have e := ul4b_P_pert_sub H Q t hu4 ((ul4_ccc_props he').2.1 4)
  have e2 : (fun x => ouSg Q ν t (ulPert s M ρ c u) x - ouSg Q ν t (ulPert s M ρ c e') x) =
      ouSg Q ν t (ulPert s M ρ c (fun x => u x - e' x)) := e.symm
  rw [e2]
  refine (hest t ⟨ht, htT⟩ _ hd).trans ?_
  calc ENNReal.ofReal A * ulNormE k θ (fun x => u x - e' x)
      ≤ ENNReal.ofReal A * ENNReal.ofReal (ε / (A + 1)) := mul_le_mul' le_rfl hle
    _ = ENNReal.ofReal (A * (ε / (A + 1))) := (ENNReal.ofReal_mul hA0).symm
    _ ≤ ENNReal.ofReal ε := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith

end Pert

/-! ### Riemann sums of a uniformly strongly continuous family -/

section Riemann
variable {k : ℕ} {θ : Euc d → ℝ}

/-- the clamp to `[0,a]` -/
def ul4bCl (a σ : ℝ) : ℝ := max 0 (min σ a)

theorem ul4bCl_cont (a : ℝ) : Continuous (ul4bCl a) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem ul4bCl_mem {a : ℝ} (ha : 0 ≤ a) (σ : ℝ) : ul4bCl a σ ∈ Icc 0 a :=
  ⟨le_max_left _ _, max_le ha (min_le_right _ _)⟩

theorem ul4bCl_eq {a σ : ℝ} (hσ : σ ∈ Icc 0 a) : ul4bCl a σ = σ := by
  simp only [ul4bCl, min_eq_left hσ.2, max_eq_right hσ.1]

/-- **Riemann sums.**  For a uniformly strongly continuous closure-valued family `Ψ` on `[0,a]`,
pointwise continuous in `σ`, the Riemann sums approximate `∫_0^a Ψ σ dσ` in `ulNormE` and pointwise,
with constants independent of the mesh. -/
theorem ul4b_riemann (hk2 : (2 : ℝ) + (d : ℝ) / 2 < k) (hθ : IsUlCutoff θ) {a : ℝ} (ha : 0 < a)
    {Ψ : ℝ → Euc d → ℝ} (hΨ : UlUReg k θ a Ψ) (hpt : ∀ x, ContinuousOn (fun σ => Ψ σ x) (Icc 0 a)) :
    ∃ Cs C2 : ℝ, 0 < Cs ∧ 0 ≤ C2 ∧ ∀ ε : ℝ, 0 < ε → ∃ R : Euc d → ℝ, UlClosure k θ R ∧
      ulNormE k θ (fun x => (∫ σ in (0 : ℝ)..a, Ψ σ x) - R x) ≤ ENNReal.ofReal (Cs * ε) ∧
      ∀ x, |(∫ σ in (0 : ℝ)..a, Ψ σ x) - R x| ≤ C2 * ε := by
  obtain ⟨χ, hχ⟩ := ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := ul_equiv k θ χ hθ hχ
  obtain ⟨C0, hC0, htb⟩ := ul4_time_bound k χ hχ
  have hk0 : ((0 : ℕ) : ℝ) + (d : ℝ) / 2 < k := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    push_cast; linarith
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 0 hk0 θ hθ
  obtain ⟨W, hW⟩ := ul4_bdd hθ hΨ.toReg
  set B : ℝ := Ccb * max W 0 with hB
  have hB0 : 0 ≤ B := by positivity
  have hbd : ∀ σ ∈ Icc (0 : ℝ) a, ∀ x, |Ψ σ x| ≤ B := by
    intro σ hσ x
    obtain ⟨hmem, hnorm⟩ := hcb _ (hΨ.mem σ hσ)
    have h1 := ul3_cb_apply hmem (Nat.zero_le 0) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
    have h2 : (ulNormE k θ (Ψ σ)).toReal ≤ max W 0 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top
        ((hW σ hσ).trans (ENNReal.ofReal_le_ofReal (le_max_left W 0)))
      rwa [ENNReal.toReal_ofReal (le_max_right _ _)] at this
    exact h1.trans (hnorm.trans (mul_le_mul_of_nonneg_left h2 hCcb.le))
  have hdiff : ∀ {ε : ℝ} {σ σ' : ℝ}, 0 ≤ ε → σ ∈ Icc (0 : ℝ) a → σ' ∈ Icc (0 : ℝ) a →
      ulNormE k θ (fun x => Ψ σ x - Ψ σ' x) ≤ ENNReal.ofReal ε → ∀ x, |Ψ σ x - Ψ σ' x| ≤ Ccb * ε := by
    intro ε σ σ' hε0 hσ hσ' hle x
    obtain ⟨hmem, hnorm⟩ := hcb _ (ul4_closure_sub hθ (hΨ.mem σ hσ) (hΨ.mem σ' hσ'))
    have h1 := ul3_cb_apply hmem (Nat.zero_le 0) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
    have h2 : (ulNormE k θ (fun x => Ψ σ x - Ψ σ' x)).toReal ≤ ε := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      rwa [ENNReal.toReal_ofReal hε0] at this
    exact h1.trans (hnorm.trans (mul_le_mul_of_nonneg_left h2 hCcb.le))
  refine ⟨Ce * C0 * Ce * a, Ccb * a, by positivity, by positivity, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hδΨ⟩ := hΨ.unif ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (a / δ)
  have hNpos : 0 < (N : ℝ) := lt_trans (by positivity) hN
  set Δ : ℝ := a / N with hΔ
  have hΔ0 : 0 < Δ := by positivity
  have hΔδ : Δ < δ := by
    rw [hΔ, div_lt_iff₀ hNpos]; rwa [div_lt_iff₀ hδ, mul_comm] at hN
  have hNΔ : (N : ℝ) * Δ = a := by rw [hΔ]; field_simp
  have hmesh : ∀ i : ℕ, i < N → (i : ℝ) * Δ ∈ Icc (0 : ℝ) a := fun i hi => ⟨by positivity, by
      rw [← hNΔ]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) hΔ0.le⟩
  have hmesh' : ∀ i : ℕ, i < N → ∀ σ' ∈ Icc (0 : ℝ) Δ, (i : ℝ) * Δ + σ' ∈ Icc (0 : ℝ) a :=
    fun i hi σ' hσ' => ⟨by have := (hmesh i hi).1; linarith [hσ'.1], by
      have h1 : ((i : ℝ) + 1) * Δ ≤ N * Δ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hΔ0.le
      have h2 : ((i : ℝ) + 1) * Δ = i * Δ + Δ := by ring
      linarith [hσ'.2]⟩
  set Ψc : ℝ → Euc d → ℝ := fun σ x => Ψ (ul4bCl a σ) x with hΨc
  have hΨc_cont : ∀ x, Continuous fun σ => Ψc σ x := fun x =>
    (hpt x).comp_continuous (ul4bCl_cont a) (ul4bCl_mem ha.le)
  have hΨc_meas : ∀ σ, Measurable (Ψc σ) := fun σ =>
    (hΨ.mem _ (ul4bCl_mem ha.le σ)).1.continuous.measurable
  set F : ℕ → ℝ → Euc d → ℝ := fun i σ' x => Ψc ((i : ℝ) * Δ + σ') x - Ψc ((i : ℝ) * Δ) x with hF
  have hFmeas : ∀ i, Measurable (Function.uncurry (F i)) := fun i =>
    measurable_uncurry_of_continuous_of_measurable
      (fun x => ((hΨc_cont x).comp (continuous_const.add continuous_id)).sub continuous_const)
      (fun σ' => (hΨc_meas _).sub (hΨc_meas _))
  have hFe : ∀ i < N, ∀ σ' ∈ Icc (0 : ℝ) Δ, F i σ' =
      fun x => Ψ ((i : ℝ) * Δ + σ') x - Ψ ((i : ℝ) * Δ) x := by
    intro i hi σ' hσ'
    funext x
    simp only [hF, hΨc, ul4bCl_eq (hmesh' i hi σ' hσ'), ul4bCl_eq (hmesh i hi)]
  have hFnorm : ∀ i < N, ∀ σ' ∈ Icc (0 : ℝ) Δ,
      ulNormE k θ (F i σ') ≤ ENNReal.ofReal ε := by
    intro i hi σ' hσ'
    rw [hFe i hi σ' hσ']
    exact hδΨ _ (hmesh' i hi σ' hσ') _ (hmesh i hi) (by
      rw [add_sub_cancel_left, abs_of_nonneg hσ'.1]; exact lt_of_le_of_lt hσ'.2 hΔδ)
  have hFloc : ∀ i < N, ∀ σ' ∈ Ioo (0 : ℝ) Δ, ulocNormE k χ (F i σ') ≤ ENNReal.ofReal (Ce * ε) := by
    intro i hi σ' hσ'
    refine (hequ _).2.trans ?_
    rw [ENNReal.ofReal_mul hCe.le]
    exact mul_le_mul' le_rfl (hFnorm i hi σ' (Ioo_subset_Icc_self hσ'))
  have hFbd : ∀ i < N, ∀ σ' ∈ Ioo (0 : ℝ) Δ, ∀ x, |F i σ' x| ≤ 2 * B := by
    intro i hi σ' hσ' x
    rw [hFe i hi σ' (Ioo_subset_Icc_self hσ')]
    have h1 := hbd _ (hmesh' i hi σ' (Ioo_subset_Icc_self hσ')) x
    have h2 := hbd _ (hmesh i hi) x
    exact (abs_sub _ _).trans (by linarith)
  have hEi : ∀ i < N, ulocNormE k χ (fun x => ∫ σ' in (0 : ℝ)..Δ, F i σ' x) ≤
      ENNReal.ofReal (C0 * (Ce * ε * Δ)) := by
    intro i hi
    have := htb hΔ0 (F i) (hFmeas i) (2 * B) (hFbd i hi) (fun _ => Ce * ε) measurable_const
      intervalIntegrable_const (Ce * ε) (by positivity) (fun _ _ => le_rfl) (hFloc i hi)
    refine this.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring
  have hI : ∀ x, ∫ σ in (0 : ℝ)..a, Ψ σ x = ∫ σ in (0 : ℝ)..a, Ψc σ x := fun x =>
    intervalIntegral.integral_congr fun σ hσ => by
      rw [uIcc_of_le ha.le] at hσ; simp only [hΨc, ul4bCl_eq hσ]
  have hsplit : ∀ x, ∫ σ in (0 : ℝ)..a, Ψc σ x =
      ∑ i ∈ Finset.range N, ∫ σ in ((i : ℝ) * Δ)..(((i + 1 : ℕ) : ℝ) * Δ), Ψc σ x := by
    intro x
    have := intervalIntegral.sum_integral_adjacent_intervals (f := fun σ => Ψc σ x) (μ := volume)
      (a := fun i : ℕ => (i : ℝ) * Δ) (n := N) (fun i _ => (hΨc_cont x).intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_mul, hNΔ] at this
    exact this.symm
  have hpiece : ∀ (i : ℕ) x, ∫ σ in ((i : ℝ) * Δ)..(((i + 1 : ℕ) : ℝ) * Δ), Ψc σ x =
      ∫ σ' in (0 : ℝ)..Δ, Ψc ((i : ℝ) * Δ + σ') x := by
    intro i x
    have := intervalIntegral.integral_comp_add_left (f := fun σ => Ψc σ x) (a := 0) (b := Δ)
      ((i : ℝ) * Δ)
    rw [this]
    congr 1 <;> push_cast <;> ring
  have hdecomp : ∀ x, (∫ σ in (0 : ℝ)..a, Ψ σ x) -
      (∑ i ∈ Finset.range N, Δ * Ψ ((i : ℝ) * Δ) x) = ∑ i ∈ Finset.range N, ∫ σ' in (0 : ℝ)..Δ, F i σ' x := by
    intro x
    rw [hI, hsplit, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h1 : IntervalIntegrable (fun σ' => Ψc ((i : ℝ) * Δ + σ') x) volume 0 Δ :=
      ((hΨc_cont x).comp (continuous_const.add continuous_id)).intervalIntegrable _ _
    rw [hpiece i x, intervalIntegral.integral_sub (g := fun _ => Ψc ((i : ℝ) * Δ) x) h1
      intervalIntegrable_const]
    simp [hF, hΨc, ul4bCl_eq (hmesh i (Finset.mem_range.1 hi))]
  have hRmem : UlClosure k θ (fun x => ∑ i ∈ Finset.range N, Δ * Ψ ((i : ℝ) * Δ) x) :=
    ul4_closure_sum (Finset.range N) (fun i x => Δ * Ψ ((i : ℝ) * Δ) x) fun i hi =>
      ul4_closure_smul hθ Δ (hΨ.mem _ (hmesh i (Finset.mem_range.1 hi)))
  refine ⟨_, hRmem, ?_, ?_⟩
  · have e : (fun x => (∫ σ in (0 : ℝ)..a, Ψ σ x) - ∑ i ∈ Finset.range N, Δ * Ψ ((i : ℝ) * Δ) x) =
        fun x => ∑ i ∈ Finset.range N, ∫ σ' in (0 : ℝ)..Δ, F i σ' x := funext hdecomp
    rw [e]
    refine ((hequ _).1).trans ?_
    have hsum := (ul4_uloc_sum k χ (Finset.range N) (fun i x => ∫ σ' in (0 : ℝ)..Δ, F i σ' x)).trans
      (Finset.sum_le_sum fun i hi => hEi i (Finset.mem_range.1 hi))
    calc ENNReal.ofReal Ce * _ ≤ ENNReal.ofReal Ce * ∑ i ∈ Finset.range N,
          ENNReal.ofReal (C0 * (Ce * ε * Δ)) := mul_le_mul' le_rfl hsum
      _ = ENNReal.ofReal (Ce * C0 * Ce * a * ε) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hCe.le]
        congr 1; rw [← hNΔ]; ring
  · intro x
    rw [hdecomp x]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range N, |∫ σ' in (0 : ℝ)..Δ, F i σ' x| ≤ ∑ i ∈ Finset.range N, Δ * (Ccb * ε) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := Δ)
            (f := fun σ' => F i σ' x) (C := Ccb * ε) fun σ' hσ' => by
              rw [uIoc_of_le hΔ0.le] at hσ'
              have hσ'' : σ' ∈ Icc (0 : ℝ) Δ := ⟨hσ'.1.le, hσ'.2⟩
              rw [Real.norm_eq_abs, hFe i hi' σ' hσ'']
              exact hdiff hε.le (hmesh' i hi' σ' hσ'') (hmesh i hi') (hδΨ _ (hmesh' i hi' σ' hσ'') _
                (hmesh i hi') (by
                  rw [add_sub_cancel_left, abs_of_nonneg hσ''.1]; exact lt_of_le_of_lt hσ''.2 hΔδ)) x
          rw [Real.norm_eq_abs, sub_zero, abs_of_pos hΔ0] at this
          linarith
      _ = Ccb * a * ε := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hNΔ]; ring

/-- **Closure of time integrals.**  The integral of a uniformly strongly continuous closure-valued
family lies in `UlClosure`. -/
theorem ul4b_int_mem (hk2 : (2 : ℝ) + (d : ℝ) / 2 < k) (hθ : IsUlCutoff θ) {a : ℝ} (ha : 0 < a)
    {Ψ : ℝ → Euc d → ℝ} (hΨ : UlUReg k θ a Ψ) (hpt : ∀ x, ContinuousOn (fun σ => Ψ σ x) (Icc 0 a)) :
    UlClosure k θ (fun x => ∫ σ in (0 : ℝ)..a, Ψ σ x) := by
  obtain ⟨Cs, C2, hCs, hC2, hR⟩ := ul4b_riemann hk2 hθ ha hΨ hpt
  have hex : ∀ n : ℕ, ∃ R : Euc d → ℝ, UlClosure k θ R ∧
      ulNormE k θ (fun x => (∫ σ in (0 : ℝ)..a, Ψ σ x) - R x) ≤ ENNReal.ofReal (1 / 2 ^ n) ∧
      ∀ x, |(∫ σ in (0 : ℝ)..a, Ψ σ x) - R x| ≤ C2 * (1 / 2) ^ n := by
    intro n
    obtain ⟨R, hRm, hRn, hRp⟩ := hR (1 / (2 ^ n * (Cs + 1))) (by positivity)
    refine ⟨R, hRm, hRn.trans (ENNReal.ofReal_le_ofReal ?_), fun x => (hRp x).trans ?_⟩
    · rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_pos (two_pos : (0:ℝ) < 2) n]
    · have h2 : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ n * (Cs + 1) := by nlinarith [pow_pos (two_pos : (0:ℝ) < 2) n]
      have : 1 / ((2 : ℝ) ^ n * (Cs + 1)) ≤ (1 / 2) ^ n := by
        rw [one_div_pow]; exact one_div_le_one_div_of_le (by positivity) h2
      exact mul_le_mul_of_nonneg_left this hC2
  choose R hRm hRn hRp using hex
  refine ul4b_lim hk2 hθ hRm hRn fun x => ?_
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul C2
  rw [mul_zero] at ht
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg) (fun n => ?_) ht)
  rw [Real.dist_eq, abs_sub_comm]; exact hRp n x

end Riemann

end HRS.MS.Ul
