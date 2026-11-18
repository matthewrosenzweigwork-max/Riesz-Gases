import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovOscAux3
import HRS.MS.MovOscAux5
import HRS.MS.MovOscAux9
import HRS.MS.ThCorrSAux2
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD08
import HRS.MS.S67NlBD09

/-!
# S6.7 nonlinear breakdown, packet 10: integer mixed product on the Schwartz core

`s67bd_product_integer_core`.  All polynomial weights are placed on `w`: `x^a (u w) = u (x^a w)`.
Packet 09 is re-run in the "weights inside the jet" form (`s67bd_integer_converse_in`), whose closure
under `x_i` and `D_i` is simpler.  The jets of `u V` (`V = x^a w`) are bounded in `L²` by the `H^k` norm of
`u V` (Fourier symbol of a mixed jet), the mixed Sobolev algebra `H^b × H^k → H^k` (`mova4_sobolev_algebra`),
packet 08 and the integer-ladder bound for `x^a w`.
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

/-! ### Derivative of a monomial -/

theorem s67bd_hasFDeriv_xpow (a : MultiIndex d) (y : Euc d) :
    HasFDerivAt (fun z : Euc d => s67bd_xpow a z)
      (∑ l : Fin d, (∏ j ∈ Finset.univ.erase l, y j ^ a j) •
        ((a l • y l ^ (a l - 1)) • (EuclideanSpace.proj (𝕜 := ℝ) l : Euc d →L[ℝ] ℝ))) y := by
  have hg : ∀ l ∈ (Finset.univ : Finset (Fin d)),
      HasFDerivAt (fun z : Euc d => z l ^ a l)
        ((a l • y l ^ (a l - 1)) • (EuclideanSpace.proj (𝕜 := ℝ) l : Euc d →L[ℝ] ℝ)) y :=
    fun l _ => (EuclideanSpace.proj (𝕜 := ℝ) l : Euc d →L[ℝ] ℝ).hasFDerivAt.pow (a l)
  exact HasFDerivAt.finsetProd hg

theorem s67bd_fderiv_xpow (a : MultiIndex d) (i : Fin d) (y : Euc d) :
    fderiv ℝ (fun z : Euc d => s67bd_xpow a z) y (EuclideanSpace.single i (1 : ℝ)) =
      (a i : ℝ) * s67bd_xpow (a - Pi.single i 1) y := by
  rw [(s67bd_hasFDeriv_xpow a y).fderiv]
  simp only [sum_apply, smul_apply]
  rw [Finset.sum_eq_single i]
  · have : s67bd_xpow (a - Pi.single i 1) y =
        (∏ j ∈ Finset.univ.erase i, y j ^ a j) * y i ^ (a i - 1) := by
      unfold s67bd_xpow
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      congr 1
      · refine Finset.prod_congr rfl fun j hj => ?_
        simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
      · simp
    rw [this]
    simp [smul_eq_mul, nsmul_eq_mul]
    ring
  · intro l _ hl
    simp [hl]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem s67bd_D_xpow_mul (a : MultiIndex d) (i : Fin d) {u : Euc d → ℝ} (hu : Differentiable ℝ u)
    (y : Euc d) :
    s67bd_D i (fun z => s67bd_xpow a z * u z) y =
      s67bd_xpow a y * s67bd_D i u y + (a i : ℝ) * s67bd_xpow (a - Pi.single i 1) y * u y := by
  have h : HasFDerivAt (fun z : Euc d => s67bd_xpow a z * u z) _ y :=
    (s67bd_hasFDeriv_xpow a y).mul (hu y).hasFDerivAt
  unfold s67bd_D
  rw [h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  have := s67bd_fderiv_xpow a i y
  rw [(s67bd_hasFDeriv_xpow a y).fderiv] at this
  rw [this]
  ring

theorem s67bd_degree_sub_le (a : MultiIndex d) (i : Fin d) :
    MultiIndex.degree (a - Pi.single i 1) ≤ MultiIndex.degree a := by
  unfold MultiIndex.degree
  exact Finset.sum_le_sum fun j _ => by simp

theorem s67bd_le_degree (a : MultiIndex d) (i : Fin d) : a i ≤ MultiIndex.degree a := by
  unfold MultiIndex.degree
  exact Finset.single_le_sum (f := fun j => a j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

/-! ### Closure of the weighted-jet hypothesis, weights inside -/

theorem s67bd_hyp_in_xmul (n : ℕ) (i : Fin d) (u : Euc d → ℝ) (A : ℝ)
    (h : ∀ (k : ℕ) (a : MultiIndex d) (γ : Fin k → Fin d), MultiIndex.degree a + k ≤ n + 1 →
      MemLp (s67bd_jet k γ (fun x => s67bd_xpow a x * u x)) 2 (volume : Measure (Euc d)) ∧
        (eLpNorm (s67bd_jet k γ (fun x => s67bd_xpow a x * u x)) 2
          (volume : Measure (Euc d))).toReal ≤ A) :
    ∀ (k : ℕ) (a : MultiIndex d) (γ : Fin k → Fin d), MultiIndex.degree a + k ≤ n →
      MemLp (s67bd_jet k γ (fun x => s67bd_xpow a x * (x i * u x))) 2 (volume : Measure (Euc d)) ∧
        (eLpNorm (s67bd_jet k γ (fun x => s67bd_xpow a x * (x i * u x))) 2
          (volume : Measure (Euc d))).toReal ≤ A := by
  intro k a γ hk
  have e : (fun x : Euc d => s67bd_xpow a x * (x i * u x)) =
      fun x => s67bd_xpow (a + Pi.single i 1) x * u x := by
    funext x
    rw [s67bd_xpow_add]
    ring
  rw [e]
  exact h k (a + Pi.single i 1) γ (by rw [s67bd_degree_add]; omega)

theorem s67bd_hyp_in_D (n : ℕ) (i : Fin d) (u : Euc d → ℝ)
    (hu : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) u) (A : ℝ) (hA : 0 ≤ A)
    (h : ∀ (k : ℕ) (a : MultiIndex d) (γ : Fin k → Fin d), MultiIndex.degree a + k ≤ n + 1 →
      MemLp (s67bd_jet k γ (fun x => s67bd_xpow a x * u x)) 2 (volume : Measure (Euc d)) ∧
        (eLpNorm (s67bd_jet k γ (fun x => s67bd_xpow a x * u x)) 2
          (volume : Measure (Euc d))).toReal ≤ A) :
    ∀ (k : ℕ) (a : MultiIndex d) (γ : Fin k → Fin d), MultiIndex.degree a + k ≤ n →
      MemLp (s67bd_jet k γ (fun x => s67bd_xpow a x * s67bd_D i u x)) 2
        (volume : Measure (Euc d)) ∧
        (eLpNorm (s67bd_jet k γ (fun x => s67bd_xpow a x * s67bd_D i u x)) 2
          (volume : Measure (Euc d))).toReal ≤ ((n : ℝ) + 1) * A := by
  intro k a γ hk
  have hpoly : ∀ b : MultiIndex d, ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞)
      (fun y : Euc d => s67bd_xpow b y * u y) := by
    intro b
    have hx : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun y : Euc d => s67bd_xpow b y) := by
      unfold s67bd_xpow
      exact contDiff_prod fun l _ => ((EuclideanSpace.proj (𝕜 := ℝ) l : Euc d →L[ℝ] ℝ).contDiff).pow _
    exact hx.mul hu
  set F : Euc d → ℝ := fun y => s67bd_xpow a y * u y with hF
  have hFc := hpoly a
  have hf1 : ContDiff ℝ (k : WithTop ℕ∞) (fun y : Euc d => s67bd_xpow (a - Pi.single i 1) y * u y) :=
    (hpoly _).of_le (by norm_cast; omega)
  have hg1 : ContDiff ℝ (k : WithTop ℕ∞) (s67bd_D i F) := by
    have : ContDiff ℝ (n : WithTop ℕ∞) (s67bd_D i F) :=
      (hFc.fderiv_right (by norm_cast)).clm_apply contDiff_const
    exact this.of_le (by norm_cast; omega)
  have e : (fun x : Euc d => s67bd_xpow a x * s67bd_D i u x) =
      fun x => (-(a i : ℝ)) * (s67bd_xpow (a - Pi.single i 1) x * u x) + s67bd_D i F x := by
    funext x
    rw [hF, s67bd_D_xpow_mul a i (hu.differentiable (by norm_cast)) x]
    ring
  have e2 : s67bd_jet k γ (fun x : Euc d => s67bd_xpow a x * s67bd_D i u x) =
      fun x => (-(a i : ℝ)) * s67bd_jet k γ (fun y => s67bd_xpow (a - Pi.single i 1) y * u y) x +
        s67bd_jet k γ (s67bd_D i F) x := by
    rw [e]
    funext x
    exact s67bd_jet_lin k γ _ hf1 hg1 x
  have e3 : s67bd_jet k γ (s67bd_D i F) =
      s67bd_jet (k + 1) (Fin.snoc (α := fun _ => Fin d) γ i) F := by
    funext x
    exact s67bd_jet_D k i F (hFc.of_le (by norm_cast; omega)) γ x
  rw [e2, e3]
  have h1 := h k (a - Pi.single i 1) γ (by have := s67bd_degree_sub_le a i; omega)
  have h2 := h (k + 1) a (Fin.snoc (α := fun _ => Fin d) γ i) (by omega)
  have h3 := s67bd_good_add (s67bd_good_mul (-(a i : ℝ)) h1) h2
  refine ⟨h3.1, h3.2.trans ?_⟩
  have hai : (a i : ℝ) ≤ n := by
    have := s67bd_le_degree a i
    exact_mod_cast (by omega : a i ≤ n)
  rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
  nlinarith [mul_le_mul_of_nonneg_right hai hA]

theorem s67bd_integer_converse_in (d n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Euc d → ℝ) (A : ℝ), 0 ≤ A →
      ContDiff ℝ (n : WithTop ℕ∞) u →
      (∀ (k : ℕ) (a : MultiIndex d) (γ : Fin k → Fin d), MultiIndex.degree a + k ≤ n →
        MemLp (s67bd_jet k γ (fun x => s67bd_xpow a x * u x)) 2 (volume : Measure (Euc d)) ∧
          (eLpNorm (s67bd_jet k γ (fun x => s67bd_xpow a x * u x)) 2
            (volume : Measure (Euc d))).toReal ≤ A) →
      MemOsc (n : ℝ) u ∧ oscNorm (n : ℝ) u ≤ C * A := by
  induction n with
  | zero =>
    refine ⟨1, zero_le_one, fun u A hA hu h => ?_⟩
    have h0 := h 0 0 (fun l => l.elim0) (by simp [MultiIndex.degree])
    have e : s67bd_jet 0 (fun l => l.elim0) (fun x => s67bd_xpow (0 : MultiIndex d) x * u x) = u := by
      funext x
      simp [s67bd_xpow, s67bd_jet_zero]
    rw [e] at h0
    have hmem : MemOsc ((0 : ℕ) : ℝ) u := by
      refine ⟨h0.1, ?_⟩
      simpa using (hermite_parseval_aux u h0.1).1
    refine ⟨hmem, ?_⟩
    have h1 := mova2_eLpNorm_two h0.1
    have h2 : oscNorm 0 u = (eLpNorm u 2 (volume : Measure (Euc d))).toReal := by
      rw [h1, ENNReal.toReal_ofReal (by unfold oscNorm; exact Real.sqrt_nonneg _)]
    simpa [h2] using h0.2
  | succ n ih =>
    obtain ⟨Cn, hCn, hIH⟩ := ih
    obtain ⟨C3, hC3, h3⟩ := s67bd_ladder_converse d (n : ℝ)
    refine ⟨C3 * (Cn + d * (Cn * ((n : ℝ) + 2))), by positivity, fun u A hA hu h => ?_⟩
    have hun : ContDiff ℝ (n : WithTop ℕ∞) u := hu.of_le (by norm_cast; omega)
    have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast; omega)
    obtain ⟨hm0, hn0⟩ := hIH u A hA hun (fun k a γ hk => h k a γ (by omega))
    have hX : ∀ i : Fin d, MemOsc (n : ℝ) (fun x => x i * u x) ∧
        oscNorm (n : ℝ) (fun x => x i * u x) ≤ Cn * A := by
      intro i
      refine hIH _ _ hA ?_ (s67bd_hyp_in_xmul n i u A h)
      exact ((EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ).contDiff.mul hun)
    have hDD : ∀ i : Fin d, MemOsc (n : ℝ) (s67bd_D i u) ∧
        oscNorm (n : ℝ) (s67bd_D i u) ≤ Cn * (((n : ℝ) + 1) * A) := by
      intro i
      refine hIH _ _ (by positivity) ?_ (s67bd_hyp_in_D n i u hu A hA h)
      exact (hu.fderiv_right (by norm_cast)).clm_apply contDiff_const
    obtain ⟨hm3, hn3⟩ := h3 u hu1 hm0 (fun i => (hX i).1) (fun i => (hDD i).1)
    push_cast
    refine ⟨hm3, hn3.trans ?_⟩
    have hs : ∑ i : Fin d, (oscNorm (n : ℝ) (fun x => x i * u x) + oscNorm (n : ℝ) (s67bd_D i u)) ≤
        ∑ _i : Fin d, (Cn * A + Cn * (((n : ℝ) + 1) * A)) :=
      Finset.sum_le_sum fun i _ => add_le_add (hX i).2 (hDD i).2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have hb : oscNorm (n : ℝ) u + ∑ i : Fin d, (oscNorm (n : ℝ) (fun x => x i * u x) +
        oscNorm (n : ℝ) (s67bd_D i u)) ≤ (Cn + d * (Cn * ((n : ℝ) + 2))) * A := by
      nlinarith [hs, hn0]
    calc C3 * (oscNorm (n : ℝ) u + ∑ i : Fin d, (oscNorm (n : ℝ) (fun x => x i * u x) +
          oscNorm (n : ℝ) (s67bd_D i u))) ≤ C3 * ((Cn + d * (Cn * ((n : ℝ) + 2))) * A) :=
          mul_le_mul_of_nonneg_left hb hC3
      _ = _ := by ring

/-! ### Fourier symbol of a mixed jet -/

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
theorem s67bd_jet_fourier (k : ℕ) : ∀ (γ : Fin k → Fin d) (g : SchwartzMap (Euc d) ℝ),
    MemLp (s67bd_jet k γ ⇑g) 2 (volume : Measure (Euc d)) ∧
      ∀ᵐ ξ ∂(volume : Measure (Euc d)), ‖fourierL2 (s67bd_jet k γ ⇑g) ξ‖ =
        (∏ l : Fin k, (2 * Real.pi * |ξ (γ l)|)) * ‖fourierL2 (⇑g) ξ‖ := by
  induction k with
  | zero =>
    intro γ g
    have e : s67bd_jet 0 γ ⇑g = ⇑g := funext (s67bd_jet_zero γ ⇑g)
    rw [e]
    exact ⟨g.memLp 2, Eventually.of_forall fun ξ => by simp⟩
  | succ k ih =>
    intro γ g
    obtain ⟨j, hj⟩ : ∃ j, j = γ (Fin.last k) := ⟨_, rfl⟩
    have hDj : s67bd_D j ⇑g = ⇑(mova1_D j g) := funext fun x => (mova1_D_apply j g x).symm
    have e : s67bd_jet (k + 1) γ ⇑g = s67bd_jet k (Fin.init γ) ⇑(mova1_D j g) := by
      funext x
      rw [s67bd_jet_succ k γ ⇑g (g.smooth _) x, ← hj, hDj]
    rw [e]
    obtain ⟨hm, hae⟩ := ih (Fin.init γ) (mova1_D j g)
    refine ⟨hm, ?_⟩
    have hDj' : (fun x => fderiv ℝ ⇑g x (EuclideanSpace.single j (1 : ℝ))) = ⇑(mova1_D j g) := hDj
    have hmD : MemLp (fun x => fderiv ℝ ⇑g x (EuclideanSpace.single j (1 : ℝ))) 2
        (volume : Measure (Euc d)) := by
      rw [hDj']; exact (mova1_D j g).memLp 2
    have hp := HRS.MS.TcS.tcs_fourier_partial j (g.smooth 1) (g.memLp 2) hmD
    filter_upwards [hae, hp] with ξ h1 h2
    rw [h1, Fin.prod_univ_castSucc, ← hj]
    have h3 : ‖fourierL2 ⇑(mova1_D j g) ξ‖ = 2 * Real.pi * |ξ j| * ‖fourierL2 (⇑g) ξ‖ := by
      rw [← hDj', h2, norm_mul]
      have : ‖(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))‖ = 2 * Real.pi * |ξ j| := by
        simp [abs_of_pos Real.pi_pos]
      rw [this]
    rw [h3]
    simp only [Fin.init]
    ring

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
/-- The `L²` norm of a mixed jet is bounded by the `H^k` norm. -/
theorem s67bd_jet_le_sobolev (k : ℕ) (γ : Fin k → Fin d) (g : SchwartzMap (Euc d) ℝ)
    (hg : HRS.PDE.ToolboxRd.MemSobolev (k : ℝ) ⇑g) :
    (eLpNorm (s67bd_jet k γ ⇑g) 2 (volume : Measure (Euc d))).toReal ≤ s67bd_Hnorm (k : ℝ) ⇑g := by
  obtain ⟨hJ, hae⟩ := s67bd_jet_fourier k γ g
  have h1 : (eLpNorm (s67bd_jet k γ ⇑g) 2 (volume : Measure (Euc d))).toReal =
      Real.sqrt (∫ x, (s67bd_jet k γ ⇑g x) ^ 2) := by
    rw [mova2_eLpNorm_two hJ, ENNReal.toReal_ofReal (by unfold oscNorm; exact Real.sqrt_nonneg _),
      oscNorm_zero _ hJ]
  rw [h1]
  unfold s67bd_Hnorm
  refine Real.sqrt_le_sqrt ?_
  unfold HRS.PDE.ToolboxRd.sobolevNormSq
  rw [← integral_norm_sq_fourierL2 hJ]
  have hint : Integrable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (k : ℝ) *
      ‖fourierL2 (⇑g) ξ‖ ^ 2) volume := hg.2
  refine integral_mono_ae (integrable_norm_sq_fourierL2 hJ) hint ?_
  filter_upwards [hae] with ξ hξ
  rw [hξ, Real.rpow_natCast, mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [← Finset.prod_pow]
  calc ∏ l : Fin k, (2 * Real.pi * |ξ (γ l)|) ^ 2 ≤ ∏ _l : Fin k, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) := by
        refine Finset.prod_le_prod₀ (fun l _ => sq_nonneg _) (fun l _ => ?_)
        have h2 : |ξ (γ l)| ≤ ‖ξ‖ := by
          have := PiLp.norm_apply_le ξ (γ l)
          rwa [Real.norm_eq_abs] at this
        have h3 : |ξ (γ l)| ^ 2 ≤ ‖ξ‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
        calc (2 * Real.pi * |ξ (γ l)|) ^ 2 = 4 * Real.pi ^ 2 * |ξ (γ l)| ^ 2 := by ring
          _ ≤ 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by gcongr
          _ ≤ _ := by linarith
    _ = (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ k := by simp

/-! ### Monomial multiples of a Schwartz function -/

theorem s67bd_xpow_schwartz (m : ℕ) : ∀ r : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : MultiIndex d),
    MultiIndex.degree a = m → ∀ w : SchwartzMap (Euc d) ℝ, ∃ V : SchwartzMap (Euc d) ℝ,
      (⇑V = fun x => s67bd_xpow a x * w x) ∧ oscNorm r ⇑V ≤ C * oscNorm (r + m) ⇑w := by
  induction m with
  | zero =>
    intro r
    refine ⟨1, zero_le_one, fun a ha w => ⟨w, ?_, by simp⟩⟩
    have ha0 : ∀ i, a i = 0 := fun i => by
      have := Finset.sum_eq_zero_iff.1 ha i (Finset.mem_univ i)
      exact this
    funext x
    simp [s67bd_xpow, ha0]
  | succ m ih =>
    intro r
    obtain ⟨C1, hC1, hx⟩ := mo_xmul (d := d) r
    obtain ⟨C2, hC2, hih⟩ := ih (r + 1)
    refine ⟨C1 * C2, mul_nonneg hC1 hC2, fun a ha w => ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, 1 ≤ a j := by
      by_contra hcon
      push Not at hcon
      have : MultiIndex.degree a = 0 :=
        Finset.sum_eq_zero fun i _ => by have := hcon i; omega
      omega
    set a' : MultiIndex d := a - Pi.single j 1 with ha'
    have haa : a = a' + Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl; simp [ha']; omega
      · simp [ha', Pi.single_eq_of_ne hl]
    have hdeg : MultiIndex.degree a' = m := by
      have := s67bd_degree_add a' j
      rw [← haa] at this
      omega
    obtain ⟨V', hV1, hV2⟩ := hih a' hdeg w
    refine ⟨mova1_X j V', ?_, ?_⟩
    · funext x
      rw [mova1_X_apply, hV1, haa, s67bd_xpow_add]
      ring
    · have e : (⇑(mova1_X j V') : Euc d → ℝ) = fun x => x j * V' x := funext fun x => mova1_X_apply j V' x
      rw [e]
      refine (hx j V').2.trans ?_
      calc C1 * oscNorm (r + 1) ⇑V' ≤ C1 * (C2 * oscNorm (r + 1 + m) ⇑w) :=
            mul_le_mul_of_nonneg_left hV2 hC1
        _ = C1 * C2 * oscNorm (r + ((m + 1 : ℕ) : ℝ)) ⇑w := by
            have hr : r + 1 + (m : ℝ) = r + ((m + 1 : ℕ) : ℝ) := by push_cast; ring
            rw [hr]; ring

/-! ### The weighted jet bound for a product -/

theorem s67bd_jet_product (d : ℕ) (b : ℝ) (hb : (d : ℝ) / 2 < b) (k m : ℕ) (hk : (k : ℝ) ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u w : SchwartzMap (Euc d) ℝ) (a : MultiIndex d),
      MultiIndex.degree a = m → ∀ γ : Fin k → Fin d,
      MemLp (s67bd_jet k γ (fun x => s67bd_xpow a x * (u x * w x))) 2 (volume : Measure (Euc d)) ∧
        (eLpNorm (s67bd_jet k γ (fun x => s67bd_xpow a x * (u x * w x))) 2
          (volume : Measure (Euc d))).toReal ≤ C * oscNorm b ⇑u * oscNorm ((k : ℝ) + m) ⇑w := by
  have hb0 : 0 ≤ b := le_trans (by positivity) hb.le
  obtain ⟨Ca, hCa, halg⟩ := HRS.MS.MovA4.mova4_sobolev_algebra (d := d) (m := b) (ρ := (k : ℝ))
    hb (Nat.cast_nonneg k) hk
  obtain ⟨C8b, hC8b, h8b⟩ := s67bd_osc_sobolev d b hb0
  obtain ⟨C8k, hC8k, h8k⟩ := s67bd_osc_sobolev d (k : ℝ) (Nat.cast_nonneg k)
  obtain ⟨Cx, hCx, hxp⟩ := s67bd_xpow_schwartz (d := d) m (k : ℝ)
  refine ⟨Ca * C8b * C8k * Cx, by positivity, fun u w a hdeg γ => ?_⟩
  obtain ⟨V, hV1, hV2⟩ := hxp a hdeg w
  set P : SchwartzMap (Euc d) ℝ := SchwartzMap.smulLeftCLM ℝ (⇑u) V with hPdef
  have hP : ⇑P = fun x => u x * V x := by
    rw [hPdef, SchwartzMap.smulLeftCLM_apply u.hasTemperateGrowth]
    funext x; simp
  have e : (fun x => s67bd_xpow a x * (u x * w x)) = ⇑P := by
    rw [hP]; funext x
    have := congrFun hV1 x
    rw [this]; ring
  rw [e]
  obtain ⟨hu1, hu2⟩ := h8b ⇑u (memOsc_schwartz b u)
  obtain ⟨hV1', hV2'⟩ := h8k ⇑V (memOsc_schwartz (k : ℝ) V)
  obtain ⟨hPm, hPn⟩ := halg ⇑u ⇑V hu1 hV1'
  have hPs : HRS.PDE.ToolboxRd.MemSobolev (k : ℝ) ⇑P := by rw [hP]; exact hPm
  refine ⟨(s67bd_jet_fourier k γ P).1, ?_⟩
  refine (s67bd_jet_le_sobolev k γ P hPs).trans ?_
  unfold s67bd_Hnorm at hu2 hV2' ⊢
  have h1 : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (k : ℝ) ⇑P) ≤
      Ca * (Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq b ⇑u) *
        Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (k : ℝ) ⇑V)) := by
    rw [hP]
    calc Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (k : ℝ) fun x => u x * V x)
        ≤ Real.sqrt (Ca ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq b ⇑u *
            HRS.PDE.ToolboxRd.sobolevNormSq (k : ℝ) ⇑V) := Real.sqrt_le_sqrt hPn
      _ = _ := by
        have hnb : 0 ≤ HRS.PDE.ToolboxRd.sobolevNormSq b ⇑u :=
          integral_nonneg fun η => mul_nonneg
            (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + 4 * Real.pi ^ 2 * ‖η‖ ^ 2) _)
            (sq_nonneg _)
        rw [Real.sqrt_mul (mul_nonneg (sq_nonneg Ca) hnb), Real.sqrt_mul (sq_nonneg Ca),
          Real.sqrt_sq hCa.le]
        ring
  refine h1.trans ?_
  have ou : 0 ≤ oscNorm b ⇑u := by unfold oscNorm; exact Real.sqrt_nonneg _
  have ow : 0 ≤ oscNorm ((k : ℝ) + m) ⇑w := by unfold oscNorm; exact Real.sqrt_nonneg _
  have hVk : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (k : ℝ) ⇑V) ≤
      C8k * (Cx * oscNorm ((k : ℝ) + m) ⇑w) :=
    hV2'.trans (mul_le_mul_of_nonneg_left hV2 hC8k)
  calc Ca * (Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq b ⇑u) *
        Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (k : ℝ) ⇑V))
      ≤ Ca * ((C8b * oscNorm b ⇑u) * (C8k * (Cx * oscNorm ((k : ℝ) + m) ⇑w))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hu2 hVk (Real.sqrt_nonneg _)
          (mul_nonneg hC8b ou)) hCa.le
    _ = _ := by ring

theorem s67bd_product_integer_core (d : ℕ) (b : ℝ) (n : ℕ)
    (hb : (d : ℝ) / 2 < b) (hn : (n : ℝ) ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u w : SchwartzMap (Euc d) ℝ,
      MemOsc (n : ℝ) (fun x => u x * w x) ∧
      oscNorm (n : ℝ) (fun x => u x * w x) ≤ C * oscNorm b u * oscNorm (n : ℝ) w := by
  obtain ⟨C9, hC9, h9⟩ := s67bd_integer_converse_in d n
  have hall : ∀ k m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ((k : ℝ) ≤ b →
      ∀ (u w : SchwartzMap (Euc d) ℝ) (a : MultiIndex d),
      MultiIndex.degree a = m → ∀ γ : Fin k → Fin d,
      MemLp (s67bd_jet k γ (fun x => s67bd_xpow a x * (u x * w x))) 2 (volume : Measure (Euc d)) ∧
        (eLpNorm (s67bd_jet k γ (fun x => s67bd_xpow a x * (u x * w x))) 2
          (volume : Measure (Euc d))).toReal ≤ C * oscNorm b ⇑u * oscNorm ((k : ℝ) + m) ⇑w) := by
    intro k m
    by_cases h : (k : ℝ) ≤ b
    · obtain ⟨C, hC, hP⟩ := s67bd_jet_product d b hb k m h
      exact ⟨C, hC, fun _ => hP⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' h⟩
  choose Cf hCf0 hCf using hall
  set Ctot : ℝ := ∑ k ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1), Cf k m with hCtot
  have hCtot0 : 0 ≤ Ctot := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun m _ => hCf0 k m
  have hle : ∀ k m : ℕ, k ≤ n → m ≤ n → Cf k m ≤ Ctot := by
    intro k m hk hm
    have h1 : Cf k m ≤ ∑ m' ∈ Finset.range (n + 1), Cf k m' :=
      Finset.single_le_sum (f := fun m' => Cf k m') (fun m' _ => hCf0 k m') (Finset.mem_range.2 (by omega))
    have h2 : ∑ m' ∈ Finset.range (n + 1), Cf k m' ≤ Ctot :=
      Finset.single_le_sum (f := fun k' => ∑ m' ∈ Finset.range (n + 1), Cf k' m')
        (fun k' _ => Finset.sum_nonneg fun m' _ => hCf0 k' m') (Finset.mem_range.2 (by omega))
    exact h1.trans h2
  refine ⟨C9 * Ctot, mul_nonneg hC9 hCtot0, fun u w => ?_⟩
  have ou : 0 ≤ oscNorm b ⇑u := by unfold oscNorm; exact Real.sqrt_nonneg _
  have ow : 0 ≤ oscNorm (n : ℝ) ⇑w := by unfold oscNorm; exact Real.sqrt_nonneg _
  have hA : 0 ≤ Ctot * oscNorm b ⇑u * oscNorm (n : ℝ) ⇑w := by positivity
  have hfc : ContDiff ℝ (n : WithTop ℕ∞) (fun x => u x * w x) :=
    by exact_mod_cast (u.smooth (n : ℕ∞)).mul (w.smooth (n : ℕ∞))
  have hyp : ∀ (k : ℕ) (a : MultiIndex d) (γ : Fin k → Fin d), MultiIndex.degree a + k ≤ n →
      MemLp (s67bd_jet k γ (fun x => s67bd_xpow a x * (u x * w x))) 2 (volume : Measure (Euc d)) ∧
        (eLpNorm (s67bd_jet k γ (fun x => s67bd_xpow a x * (u x * w x))) 2
          (volume : Measure (Euc d))).toReal ≤ Ctot * oscNorm b ⇑u * oscNorm (n : ℝ) ⇑w := by
    intro k a γ hk
    have hkb : (k : ℝ) ≤ b := le_trans (by exact_mod_cast (by omega : k ≤ n)) hn
    obtain ⟨hmem, hnorm⟩ := hCf k (MultiIndex.degree a) hkb u w a rfl γ
    refine ⟨hmem, hnorm.trans ?_⟩
    have hwm : oscNorm ((k : ℝ) + (MultiIndex.degree a : ℕ)) ⇑w ≤ oscNorm (n : ℝ) ⇑w :=
      (mo_mono (by exact_mod_cast (by omega : k + MultiIndex.degree a ≤ n)) (memOsc_schwartz (n : ℝ) w)).2
    have hC := hle k (MultiIndex.degree a) (by omega) (by omega)
    have h1 : Cf k (MultiIndex.degree a) * oscNorm b ⇑u ≤ Ctot * oscNorm b ⇑u :=
      mul_le_mul_of_nonneg_right hC ou
    have h2 : 0 ≤ Cf k (MultiIndex.degree a) * oscNorm b ⇑u := mul_nonneg (hCf0 _ _) ou
    exact mul_le_mul h1 hwm (Real.sqrt_nonneg _) (mul_nonneg hCtot0 ou)
  obtain ⟨hm, hnn⟩ := h9 (fun x => u x * w x) _ hA hfc hyp
  refine ⟨hm, hnn.trans (le_of_eq ?_)⟩
  ring

end HRS.MS.BreakdownS67
