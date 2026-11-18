import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovOscAux5
import HRS.MS.Mov63Aux1
import HRS.MP.RdGenSob
import HRS.MS.S67NlBD08
import HRS.MS.S67NlBD10

/-!
# S6.7 nonlinear breakdown, packet 11: integer mixed product, completion and a.e. agreement

`s67bd_product_integer`.  Route: Hermite partial sums `u_k, w_k` (Schwartz) of both factors.
The sup bound `‖u_k‖_∞ ≤ M ‖u‖_{Σ^b}` comes from packet 08 and the Sobolev embedding; an `L²`-convergent
subsequence of `u_k` converges a.e., so `u` is essentially bounded by the same `M`.  The Hermite
coefficients of the products `u_k w_k` converge to those of `u w` (Cauchy-Schwarz for the `w`-factor,
dominated convergence for the `u`-factor), and the core estimate (packet 10) passes to the limit
coefficientwise, finite sets first.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- A Hermite coefficient is bounded by the `L²` norm. -/
theorem s67bd11_coeff_le {G : Euc d → ℝ} (hG : MemLp G 2 (volume : Measure (Euc d)))
    (α : MultiIndex d) :
    |hermiteCoeff G α| ≤ (eLpNorm G 2 (volume : Measure (Euc d))).toReal := by
  obtain ⟨b, hb⟩ := exists_hermiteHilbertBasisD (d := d)
  rw [← OscSpace.inner_hermiteLpD_toLp G hG α]
  have h1 : ‖hermiteLpD α‖ = 1 := by rw [← hb α]; exact b.orthonormal.1 α
  have h2 : ‖hG.toLp G‖ = (eLpNorm G 2 (volume : Measure (Euc d))).toReal := by
    rw [Lp.norm_toLp]
  calc |inner ℝ (hermiteLpD α) (hG.toLp G)| ≤ ‖hermiteLpD α‖ * ‖hG.toLp G‖ :=
        abs_real_inner_le_norm _ _
    _ = _ := by rw [h1, h2, one_mul]

theorem s67bd11_coeff_add {f g : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hg : MemLp g 2 (volume : Measure (Euc d))) (α : MultiIndex d) :
    hermiteCoeff (fun x => f x + g x) α = hermiteCoeff f α + hermiteCoeff g α := by
  unfold hermiteCoeff
  simp_rw [add_mul]
  exact integral_add (hf.integrable_mul (memLp_hermiteFunD α))
    (hg.integrable_mul (memLp_hermiteFunD α))

/-- Uniform sup bound on Schwartz functions by the oscillator norm of order `b > d/2`. -/
theorem s67bd11_sup_bound (d : ℕ) (b : ℝ) (hb : (d : ℝ) / 2 < b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v : SchwartzMap (Euc d) ℝ, ∀ x : Euc d, |v x| ≤ M * oscNorm b v := by
  have hb0 : 0 ≤ b := le_trans (by positivity) hb.le
  obtain ⟨C8, hC8, h8⟩ := s67bd_osc_sobolev d b hb0
  obtain ⟨C1, hC1, h1⟩ := HRS.MP.RdGen.rg_sobolev_embedding (d := d) 0 (q := b) (by simpa using hb)
  refine ⟨C1 * C8, mul_nonneg hC1 hC8, fun v x => ?_⟩
  obtain ⟨hmem, hH⟩ := h8 v (memOsc_schwartz b v)
  have := h1 v (v.smooth ⊤) hmem x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  calc |v x| ≤ C1 * HRS.Whole.sobolevNorm b v := this
    _ ≤ C1 * (C8 * oscNorm b v) := mul_le_mul_of_nonneg_left hH hC1
    _ = _ := by ring

theorem s67bd11_pSum_L2 {f : Euc d → ℝ} (hf0 : MemOsc 0 f) :
    Tendsto (fun k : ℕ => eLpNorm (mo_pSum f k - f) 2 (volume : Measure (Euc d))) atTop (𝓝 0) := by
  have e : ∀ n : ℕ, eLpNorm (mo_pSum f n - f) 2 (volume : Measure (Euc d)) =
      ENNReal.ofReal (oscNorm 0 (fun x => f x - mo_pSum f n x)) := fun n => by
    rw [eLpNorm_sub_comm]
    exact mova2_eLpNorm_two (hf0.1.sub (mova2_hsum_memLp _ _))
  simp_rw [e]
  simpa using ENNReal.tendsto_ofReal (mo_hsum_tail 0 hf0)

theorem s67bd_product_integer (d : ℕ) (b : ℝ) (n : ℕ)
    (hb : (d : ℝ) / 2 < b) (hn : (n : ℝ) ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u w : Euc d → ℝ, MemOsc b u → MemOsc (n : ℝ) w →
      MemOsc (n : ℝ) (fun x => u x * w x) ∧
      oscNorm (n : ℝ) (fun x => u x * w x) ≤ C * oscNorm b u * oscNorm (n : ℝ) w := by
  obtain ⟨C0, hC0, hcore⟩ := s67bd_product_integer_core d b n hb hn
  obtain ⟨M0, hM0, hM⟩ := s67bd11_sup_bound d b hb
  refine ⟨C0, hC0, fun u w hu hw => ?_⟩
  have hb0 : 0 ≤ b := le_trans (by positivity) hb.le
  have hu0 : MemOsc 0 u := (mo_mono hb0 hu).1
  have hw0 : MemOsc 0 w := (mo_mono (Nat.cast_nonneg n) hw).1
  have ou : 0 ≤ oscNorm b u := Real.sqrt_nonneg _
  have ow : 0 ≤ oscNorm (n : ℝ) w := Real.sqrt_nonneg _
  choose U hU using fun k => mn_pSum_schwartz u k
  choose W hW using fun k => mn_pSum_schwartz w k
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (s67bd11_pSum_L2 hu0)).exists_seq_tendsto_ae
  set M : ℝ := M0 * oscNorm b u with hMdef
  have hM0' : 0 ≤ M := mul_nonneg hM0 ou
  have hbd : ∀ (k : ℕ) (x : Euc d), |mo_pSum u k x| ≤ M := by
    intro k x
    have h1 := hM (U k) x
    rw [hU k] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (mo_pSum_oscNorm_le b hu k).2 hM0)
  have hubd : ∀ᵐ x ∂(volume : Measure (Euc d)), |u x| ≤ M := by
    filter_upwards [hae] with x hx
    exact le_of_tendsto hx.abs (Eventually.of_forall fun k => hbd (ns k) x)
  have hQ : MemLp (fun x => u x * w x) 2 (volume : Measure (Euc d)) := by
    refine hw.1.of_le_mul (c := M)
      (hu.1.aestronglyMeasurable.mul hw.1.aestronglyMeasurable) ?_
    filter_upwards [hubd] with x hx
    simpa [Real.norm_eq_abs, abs_mul] using mul_le_mul_of_nonneg_right hx (abs_nonneg (w x))
  -- convergence of the `w`-partial sums in `L²`
  have hwconv : Tendsto (fun k : ℕ => eLpNorm (mo_pSum w (ns k) - w) 2 (volume : Measure (Euc d)))
      atTop (𝓝 0) := (s67bd11_pSum_L2 hw0).comp hns.tendsto_atTop
  have hwconv' : Tendsto (fun k : ℕ =>
      (eLpNorm (mo_pSum w (ns k) - w) 2 (volume : Measure (Euc d))).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hwconv
    simpa [Function.comp_def] using this
  -- coefficientwise convergence of the products
  have hcoef : ∀ α : MultiIndex d, Tendsto (fun k : ℕ =>
      hermiteCoeff (fun x => mo_pSum u (ns k) x * mo_pSum w (ns k) x) α) atTop
      (𝓝 (hermiteCoeff (fun x => u x * w x) α)) := by
    intro α
    have hpu : ∀ k, MemLp (mo_pSum u k) 2 (volume : Measure (Euc d)) :=
      fun k => mova2_hsum_memLp _ _
    have hpw : ∀ k, MemLp (mo_pSum w k) 2 (volume : Measure (Euc d)) :=
      fun k => mova2_hsum_memLp _ _
    have hG : ∀ k, MemLp (fun x => mo_pSum u (ns k) x * (mo_pSum w (ns k) x - w x)) 2
        (volume : Measure (Euc d)) := by
      intro k
      refine ((hpw (ns k)).sub hw.1).of_le_mul (c := M)
        ((hpu (ns k)).aestronglyMeasurable.mul
          ((hpw (ns k)).aestronglyMeasurable.sub hw.1.aestronglyMeasurable)) ?_
      refine Eventually.of_forall fun x => ?_
      simpa [Real.norm_eq_abs, abs_mul] using
        mul_le_mul_of_nonneg_right (hbd (ns k) x) (abs_nonneg (mo_pSum w (ns k) x - w x))
    have hH : ∀ k, MemLp (fun x => (mo_pSum u (ns k) x - u x) * w x) 2
        (volume : Measure (Euc d)) := by
      intro k
      refine hw.1.of_le_mul (c := 2 * M)
        (((hpu (ns k)).aestronglyMeasurable.sub hu.1.aestronglyMeasurable).mul
          hw.1.aestronglyMeasurable) ?_
      filter_upwards [hubd] with x hx
      have h1 : |mo_pSum u (ns k) x - u x| ≤ 2 * M := by
        have := hbd (ns k) x
        rw [abs_le] at this hx ⊢
        constructor <;> linarith [this.1, this.2, hx.1, hx.2]
      simpa [Real.norm_eq_abs, abs_mul] using mul_le_mul_of_nonneg_right h1 (abs_nonneg (w x))
    have hsplit : ∀ k, hermiteCoeff (fun x => mo_pSum u (ns k) x * mo_pSum w (ns k) x) α =
        hermiteCoeff (fun x => u x * w x) α +
          hermiteCoeff (fun x => mo_pSum u (ns k) x * (mo_pSum w (ns k) x - w x)) α +
          hermiteCoeff (fun x => (mo_pSum u (ns k) x - u x) * w x) α := by
      intro k
      have hQG : MemLp (fun x => u x * w x + mo_pSum u (ns k) x * (mo_pSum w (ns k) x - w x))
          2 (volume : Measure (Euc d)) := hQ.add (hG k)
      have e1 := s67bd11_coeff_add hQ (hG k) α
      have e2 := s67bd11_coeff_add hQG (hH k) α
      have eP : (fun x => mo_pSum u (ns k) x * mo_pSum w (ns k) x) = fun x =>
          (u x * w x + mo_pSum u (ns k) x * (mo_pSum w (ns k) x - w x)) +
            (mo_pSum u (ns k) x - u x) * w x := by
        funext x; ring
      rw [eP, e2, e1]
    -- the `G` part
    have hGt : Tendsto (fun k : ℕ =>
        hermiteCoeff (fun x => mo_pSum u (ns k) x * (mo_pSum w (ns k) x - w x)) α)
        atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) (by simpa using hwconv'.const_mul M)
      rw [Real.norm_eq_abs]
      refine (s67bd11_coeff_le (hG k) α).trans ?_
      have h1 : eLpNorm (fun x => mo_pSum u (ns k) x * (mo_pSum w (ns k) x - w x)) 2
          (volume : Measure (Euc d)) ≤
          ENNReal.ofReal M * eLpNorm (mo_pSum w (ns k) - w) 2 (volume : Measure (Euc d)) :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hG k).aestronglyMeasurable
          (Eventually.of_forall fun x => by
            simpa [Real.norm_eq_abs, abs_mul] using
              mul_le_mul_of_nonneg_right (hbd (ns k) x) (abs_nonneg (mo_pSum w (ns k) x - w x))) 2
      have h2 : eLpNorm (mo_pSum w (ns k) - w) 2 (volume : Measure (Euc d)) ≠ ⊤ :=
        ((hpw (ns k)).sub hw.1).eLpNorm_ne_top
      have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2) h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0'] at h3
    -- the `H` part, by dominated convergence
    have hHt : Tendsto (fun k : ℕ =>
        hermiteCoeff (fun x => (mo_pSum u (ns k) x - u x) * w x) α) atTop (𝓝 0) := by
      have hwh : Integrable (fun x => w x * hermiteFunD α x) (volume : Measure (Euc d)) :=
        hw.1.integrable_mul (memLp_hermiteFunD α)
      have hdom := tendsto_integral_of_dominated_convergence
        (μ := (volume : Measure (Euc d)))
        (F := fun (k : ℕ) (x : Euc d) => (mo_pSum u (ns k) x - u x) * w x * hermiteFunD α x)
        (f := fun _ => (0 : ℝ))
        (bound := fun x => 2 * M * ‖w x * hermiteFunD α x‖)
        (fun k => (((hpu (ns k)).aestronglyMeasurable.sub hu.1.aestronglyMeasurable).mul
          hw.1.aestronglyMeasurable).mul
          (contDiff_hermiteFunD α).continuous.aestronglyMeasurable)
        (hwh.norm.const_mul (2 * M))
        (fun k => by
          filter_upwards [hubd] with x hx
          have h1 : |mo_pSum u (ns k) x - u x| ≤ 2 * M := by
            have := hbd (ns k) x
            rw [abs_le] at this hx ⊢
            constructor <;> linarith [this.1, this.2, hx.1, hx.2]
          rw [mul_assoc, norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
        (by
          filter_upwards [hae] with x hx
          have : Tendsto (fun k => mo_pSum u (ns k) x - u x) atTop (𝓝 0) := by
            simpa using hx.sub_const (u x)
          simpa using (this.mul_const (w x)).mul_const (hermiteFunD α x))
      simpa [hermiteCoeff] using hdom
    have := (tendsto_const_nhds (x := hermiteCoeff (fun x => u x * w x) α)).add hGt |>.add hHt
    simpa [hsplit] using this
  -- the uniform bound on the products' oscillator norms
  set B : ℝ := C0 * oscNorm b u * oscNorm (n : ℝ) w with hB
  have hB0 : 0 ≤ B := by positivity
  have hP : ∀ k : ℕ, MemOsc (n : ℝ) (fun x => mo_pSum u (ns k) x * mo_pSum w (ns k) x) ∧
      oscNorm (n : ℝ) (fun x => mo_pSum u (ns k) x * mo_pSum w (ns k) x) ≤ B := by
    intro k
    have h := hcore (U (ns k)) (W (ns k))
    rw [hU (ns k), hW (ns k)] at h
    refine ⟨h.1, h.2.trans ?_⟩
    have o1 := (mo_pSum_oscNorm_le b hu (ns k)).2
    have o2 := (mo_pSum_oscNorm_le (n : ℝ) hw (ns k)).2
    have o3 : 0 ≤ oscNorm b (mo_pSum u (ns k)) := Real.sqrt_nonneg _
    have o4 : 0 ≤ oscNorm (n : ℝ) (mo_pSum w (ns k)) := Real.sqrt_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left o1 hC0) o2 o4 (by positivity)
  have hnn : ∀ (f : Euc d → ℝ) (α : MultiIndex d),
      0 ≤ oscEigenvalue d α ^ (n : ℝ) * hermiteCoeff f α ^ 2 := fun f α =>
    mul_nonneg (Real.rpow_nonneg (oscEigenvalue_pos α).le _) (sq_nonneg _)
  have hfin : ∀ S : Finset (MultiIndex d),
      ∑ α ∈ S, oscEigenvalue d α ^ (n : ℝ) * hermiteCoeff (fun x => u x * w x) α ^ 2 ≤ B ^ 2 := by
    intro S
    have hlim : Tendsto (fun k : ℕ => ∑ α ∈ S, oscEigenvalue d α ^ (n : ℝ) *
        hermiteCoeff (fun x => mo_pSum u (ns k) x * mo_pSum w (ns k) x) α ^ 2) atTop
        (𝓝 (∑ α ∈ S, oscEigenvalue d α ^ (n : ℝ) *
          hermiteCoeff (fun x => u x * w x) α ^ 2)) :=
      tendsto_finsetSum _ fun α _ => ((hcoef α).pow 2).const_mul _
    refine le_of_tendsto' hlim fun k => ?_
    obtain ⟨hm, hk⟩ := hP k
    calc ∑ α ∈ S, oscEigenvalue d α ^ (n : ℝ) *
          hermiteCoeff (fun x => mo_pSum u (ns k) x * mo_pSum w (ns k) x) α ^ 2
        ≤ ∑' α, oscEigenvalue d α ^ (n : ℝ) *
          hermiteCoeff (fun x => mo_pSum u (ns k) x * mo_pSum w (ns k) x) α ^ 2 :=
          hm.2.sum_le_tsum S fun α _ => hnn _ α
      _ = oscNorm (n : ℝ) (fun x => mo_pSum u (ns k) x * mo_pSum w (ns k) x) ^ 2 := by
          unfold oscNorm
          rw [Real.sq_sqrt (tsum_nonneg fun α => hnn _ α)]
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hk 2
  have hsum : Summable fun α : MultiIndex d =>
      oscEigenvalue d α ^ (n : ℝ) * hermiteCoeff (fun x => u x * w x) α ^ 2 :=
    summable_of_sum_le (fun α => hnn _ α) hfin
  refine ⟨⟨hQ, hsum⟩, ?_⟩
  unfold oscNorm
  calc Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ (n : ℝ) *
        hermiteCoeff (fun x => u x * w x) α ^ 2) ≤ Real.sqrt (B ^ 2) :=
        Real.sqrt_le_sqrt (Real.tsum_le_of_sum_le (fun α => hnn _ α) hfin)
    _ = B := Real.sqrt_sq hB0

end HRS.MS.BreakdownS67
