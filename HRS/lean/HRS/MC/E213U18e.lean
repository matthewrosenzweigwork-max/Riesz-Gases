import HRS.MC.E213U18d
import HRS.PDE.MeanFieldTransientB
import HRS.Sections.AdjKDAux2

/-!
# Packet e213u18 (part e): the Gaussian space of a centred Gaussian random element

For `Z : Ω → B` with centred Gaussian law, `𝒢(Z) = {W | ∃ L ∈ B', W = L∘Z a.e.}` is a linear space of
functions satisfying the hypotheses `QrpwG4` of the Wick pairing.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS HRS.Sec7 HRS.MC.QRSpec.Wick

section Gspace

variable {Ω : Type} [MeasurableSpace Ω] {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [MeasurableSpace B] [BorelSpace B]

/-- The linear functionals of `Z`, as a linear space of functions (up to a.e. equality). -/
def u18_gspace (P : Measure Ω) (Z : Ω → B) : Submodule ℝ (Ω → ℝ) where
  carrier := {W | ∃ L : StrongDual ℝ B, W =ᵐ[P] fun ω => L (Z ω)}
  add_mem' := by
    rintro W W' ⟨L, hL⟩ ⟨L', hL'⟩
    refine ⟨L + L', ?_⟩
    filter_upwards [hL, hL'] with ω h1 h2
    simp only [Pi.add_apply, h1, h2, ContinuousLinearMap.add_apply]
  zero_mem' := ⟨0, Eventually.of_forall fun ω => by simp⟩
  smul_mem' := by
    rintro c W ⟨L, hL⟩
    refine ⟨c • L, ?_⟩
    filter_upwards [hL] with ω h1
    simp only [Pi.smul_apply, h1, ContinuousLinearMap.smul_apply]

theorem u18_mem_gspace {P : Measure Ω} (Z : Ω → B) (L : StrongDual ℝ B) :
    (fun ω => L (Z ω)) ∈ u18_gspace P Z := ⟨L, Eventually.of_forall fun _ => rfl⟩

theorem u18_gspace_G4 {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → B} (hZ : AEMeasurable Z P)
    (hG : IsCenteredGaussian (law P Z)) : QrpwG4 P (u18_gspace P Z) := by
  rintro W ⟨L, hL⟩
  have hgl : HasGaussianLaw Z P := ⟨hZ, hG.1⟩
  have hLg : HasGaussianLaw (fun ω => L (Z ω)) P := hgl.map_fun L
  have h0 : ∫ ω, L (Z ω) ∂P = 0 := by
    have := integral_map (μ := P) hZ L.continuous.aestronglyMeasurable
    rw [← this]
    exact hG.2 L
  obtain ⟨h1, h2⟩ := qrpw_gauss4 hLg h0
  refine ⟨h1.ae_eq hL.symm, ?_⟩
  have e1 : ∫ ω, W ω ^ 4 ∂P = ∫ ω, L (Z ω) ^ 4 ∂P :=
    integral_congr_ae (hL.mono fun ω h => by simp only [h])
  have e2 : ∫ ω, W ω ^ 2 ∂P = ∫ ω, L (Z ω) ^ 2 ∂P :=
    integral_congr_ae (hL.mono fun ω h => by simp only [h])
  rw [e1, e2, h2]

end Gspace

section Kernels

variable {d : ℕ}

theorem u18_continuous_grad {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : Continuous (Torus.grad f) :=
  PDE.MFLinear.continuous_grad (PDE.MFTransient.isCk_of_isSmooth hf 1)

theorem u18_norm_grad_realMode (k : NonzeroLattice d) (x : Torus d) :
    ‖Torus.grad (Torus.realMode k) x‖ ≤ Real.sqrt 2 * Lattice.jp k.1 := by
  unfold Torus.grad gradient
  rw [LinearIsometryEquiv.norm_map]
  exact u18_norm_fderiv_lift_realMode k (Torus.rep x)

/-- A pair kernel `(g x - g y)·∇g_s(x-y)` of a bounded continuous vector field is dominated by `2c‖∇g_s(x-y)‖`. -/
theorem u18_pairKer_of_bound {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) {g : Torus d → Euc d}
    (hg : Continuous g) {c : ℝ} (hc : ∀ x, ‖g x‖ ≤ c) :
    PairKer (fun z => ‖periodicRieszGrad d s z‖) (HRS.Main.hKernel d s g) (2 * c) := by
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc (Classical.arbitrary _))
  have hsd : s < d := by linarith
  refine ⟨?_, by linarith, u18_K_integrable hd hs0 hs1, fun z => norm_nonneg _, fun x y => ?_⟩
  · unfold HRS.Main.hKernel
    exact Measurable.inner ((hg.measurable.comp measurable_fst).sub (hg.measurable.comp measurable_snd))
      ((KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd))
  · unfold HRS.Main.hKernel
    calc |inner ℝ (g x - g y) (periodicRieszGrad d s (x - y))|
        ≤ ‖g x - g y‖ * ‖periodicRieszGrad d s (x - y)‖ := abs_real_inner_le_norm _ _
      _ ≤ (2 * c) * ‖periodicRieszGrad d s (x - y)‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          calc ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
            _ ≤ c + c := add_le_add (hc x) (hc y)
            _ = 2 * c := by ring

theorem u18_pairKer_realMode {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (k : NonzeroLattice d) :
    PairKer (fun z => ‖periodicRieszGrad d s z‖) (HRS.Main.hKernel d s (Torus.grad (Torus.realMode k)))
      (2 * (Real.sqrt 2 * Lattice.jp k.1)) :=
  u18_pairKer_of_bound hd hs0 hs1 (u18_continuous_grad (HRS.AdjK.adjkd_isSmooth_realMode k))
    (fun x => u18_norm_grad_realMode k x)

theorem u18_hKernel_symm {s : ℝ} (hsd : s < d) (g : Torus d → Euc d) (x y : Torus d) :
    HRS.Main.hKernel d s g x y = HRS.Main.hKernel d s g y x := by
  unfold HRS.Main.hKernel
  rw [← neg_sub x y, ← neg_sub (g x) (g y), KernelGrad.periodicRieszGrad_neg_of_lt hsd, inner_neg_neg]

end Kernels

section Series

variable {d : ℕ} {ι : Type*} [Countable ι]

theorem u18_series_pair {G : Torus d → ℝ} (hGi : Integrable G) (hGn : ∀ z, 0 ≤ G z) {hk : ι → Torus d → Torus d → ℝ} {ak : ι → ℝ}
    (Hk : ∀ i, PairKer G (hk i) (ak i)) (c : ι → ℝ) (hsum : Summable fun i => |c i| * ak i)
    {h : Torus d → Torus d → ℝ} (hlim : ∀ x y, HasSum (fun i => c i * hk i x y) (h x y))
    {χ χ' : Torus d → ℝ} (hχm : Measurable χ) (hχ'm : Measurable χ') {M M' : ℝ}
    (hM : ∀ x, |χ x| ≤ M) (hM' : ∀ x, |χ' x| ≤ M') :
    HasSum (fun i => c i * ∫ x, ∫ y, hk i x y * χ x * χ' y) (∫ x, ∫ y, h x y * χ x * χ' y) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Classical.arbitrary _))
  have hM0' : 0 ≤ M' := (abs_nonneg _).trans (hM' (Classical.arbitrary _))
  set g : ℝ := ∫ z, G z with hg
  have hg0 : 0 ≤ g := integral_nonneg hGn
  -- inner integral
  have inner : ∀ x, HasSum (fun i => c i * ∫ y, hk i x y * χ x * χ' y) (∫ y, h x y * χ x * χ' y) := by
    intro x
    have hb := hasSum_integral_of_dominated_convergence (μ := (volume : Measure (Torus d)))
      (F := fun i y => c i * (hk i x y * χ x * χ' y)) (f := fun y => h x y * χ x * χ' y)
      (fun i y => (|c i| * ak i) * (G (x - y) * (M * M')))
      (fun i => ((((Hk i).row_meas x).mul_const (χ x)).mul hχ'm).const_mul (c i) |>.aestronglyMeasurable)
      (fun i => Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
        have h1 := (Hk i).bound x y
        have h2 := hM x
        have h3 := hM' y
        calc |c i| * (|hk i x y| * |χ x| * |χ' y|) ≤ |c i| * ((ak i * G (x - y)) * M * M') := by
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (((abs_nonneg _).trans h1))) h3 (abs_nonneg _)
                (mul_nonneg ((abs_nonneg _).trans h1) hM0)
          _ = (|c i| * ak i) * (G (x - y) * (M * M')) := by ring)
      (Eventually.of_forall fun y => (hsum.mul_right (G (x - y) * (M * M'))))
      (by
        simp_rw [tsum_mul_right]
        exact (hGi.comp_sub_left x).mul_const _ |>.const_mul _)
      (Eventually.of_forall fun y => by
        have := (hlim x y).mul_right (χ x * χ' y)
        have e : (fun i => c i * (hk i x y * χ x * χ' y)) = fun i => c i * hk i x y * (χ x * χ' y) := by
          funext i; ring
        rw [e, show h x y * χ x * χ' y = h x y * (χ x * χ' y) by ring]
        exact this)
    simp_rw [integral_const_mul] at hb
    exact hb
  -- outer integral
  have hmeas : ∀ i, Measurable fun x => ∫ y, hk i x y * χ x * χ' y := by
    intro i
    have e : (fun x => ∫ y, hk i x y * χ x * χ' y) = fun x => χ x * ∫ y, hk i x y * χ' y := by
      funext x; rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun y => by simp only []; ring)
    rw [e]
    exact hχm.mul ((Hk i).rowInt_meas hχ'm)
  have hbd : ∀ i x, |∫ y, hk i x y * χ x * χ' y| ≤ ak i * g * (M * M') := by
    intro i x
    have e : ∫ y, hk i x y * χ x * χ' y = χ x * ∫ y, hk i x y * χ' y := by
      rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun y => by simp only []; ring)
    rw [e, abs_mul]
    have h1 := (Hk i).rowInt_bound hχ'm hM' x
    have hak : 0 ≤ ak i := (Hk i).ha
    calc |χ x| * |∫ y, hk i x y * χ' y| ≤ M * (ak i * g * M') :=
          mul_le_mul (hM x) h1 (abs_nonneg _) hM0
      _ = ak i * g * (M * M') := by ring
  have hb := hasSum_integral_of_dominated_convergence (μ := (volume : Measure (Torus d)))
    (F := fun i x => c i * ∫ y, hk i x y * χ x * χ' y) (f := fun x => ∫ y, h x y * χ x * χ' y)
    (fun i _ => (|c i| * ak i) * (g * (M * M')))
    (fun i => ((hmeas i).const_mul (c i)).aestronglyMeasurable)
    (fun i => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |c i| * |∫ y, hk i x y * χ x * χ' y| ≤ |c i| * (ak i * g * (M * M')) :=
            mul_le_mul_of_nonneg_left (hbd i x) (abs_nonneg _)
        _ = (|c i| * ak i) * (g * (M * M')) := by ring)
    (Eventually.of_forall fun x => hsum.mul_right _)
    (by simp_rw [tsum_mul_right]; exact integrable_const _)
    (Eventually.of_forall inner)
  simp_rw [integral_const_mul] at hb
  exact hb

end Series

section PairBasis

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Wick pairing of the basis component `B(e_k)` with two Gaussian variables. -/
theorem u18_pair_basis {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d)
    {r : ℝ} {η : Ω → NegSobolev d r} {Q : Ω → ℝ} (hQm : AEStronglyMeasurable Q P)
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d))) (k : NonzeroLattice d)
    (hW : IsHalfWick P η μ (HRS.Main.hKernel d s (Torus.grad (Torus.realMode k))) Q)
    {𝒢 : Submodule ℝ (Ω → ℝ)} (hG : QrpwG4 P 𝒢)
    (hA : ∀ l, (fun ω => NegSobolev.fourierCoeff (η ω) l) ∈ 𝒢)
    {X Y : Ω → ℝ} (hX : X ∈ 𝒢) (hY : Y ∈ 𝒢)
    {χ χ' : Torus d → ℝ} (hχc : Continuous χ) (hχc' : Continuous χ')
    (hs : Summable fun l : Lattice d => ‖Torus.fcoef χ l‖)
    (hs' : Summable fun l : Lattice d => ‖Torus.fcoef χ' l‖)
    (hm : Torus.mean χ = 0) (hm' : Torus.mean χ' = 0)
    (hEX : ∀ l, ∫ ω, NegSobolev.fourierCoeff (η ω) l * X ω ∂P = Torus.funRealCoeff χ l)
    (hEY : ∀ l, ∫ ω, NegSobolev.fourierCoeff (η ω) l * Y ω ∂P = Torus.funRealCoeff χ' l) :
    ∫ ω, Q ω * (X ω * Y ω) ∂P =
      ∫ x, ∫ y, HRS.Main.hKernel d s (Torus.grad (Torus.realMode k)) x y * χ x * χ' y := by
  have H := u18_pairKer_realMode hd hs0 hs1 k
  have hsymm : ∀ x y, HRS.Main.hKernel d s (Torus.grad (Torus.realMode k)) x y =
      HRS.Main.hKernel d s (Torus.grad (Torus.realMode k)) y x := fun x y =>
    u18_hKernel_symm (by linarith) _ x y
  have hw : ∀ a b, wickCoeff μ (HRS.Main.hKernel d s (Torus.grad (Torus.realMode k))) a b =
      wickCoeff μ (HRS.Main.hKernel d s (Torus.grad (Torus.realMode k))) b a :=
    fun a b => H.wickCoeff_symm hsymm hΛ hμ a b
  have h1 := u18_wick_limit (A := fun l ω => NegSobolev.fourierCoeff (η ω) l) hw hG hA hX hY hQm hW
  simp only [PairKer.wickCoeff_eq H hΛ hμ, hEX, hEY] at h1
  have h2 := PairKer.pair_limit H hχc hχc' hs hs' hm hm'
  exact tendsto_nhds_unique h1 h2

end PairBasis

section PairGeneral

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem u18_abs_fourierCoeff_le {r : ℝ} (F : NegSobolev d r) (k : NonzeroLattice d) :
    |NegSobolev.fourierCoeff F k| ≤ Lattice.jp k.1 ^ r * ‖F‖ := by
  unfold NegSobolev.fourierCoeff
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (Torus.jp_pos k.1) r)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Torus.jp_pos k.1).le _)
  have := lp.norm_apply_le_norm (p := (2 : ℝ≥0∞)) (by norm_num)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) k
  calc |NegSobolev.coord F k| = ‖(show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) k‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖(show lp (fun _ : NonzeroLattice d => ℝ) 2 from F)‖ := this
    _ = ‖F‖ := rfl

theorem u18_abs_fourierCoeff_le_nat {r : ℝ} {N : ℕ} (hN : r ≤ N) (F : NegSobolev d r) (k : NonzeroLattice d) :
    |NegSobolev.fourierCoeff F k| ≤ Lattice.jp k.1 ^ N * ‖F‖ := by
  refine (u18_abs_fourierCoeff_le F k).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one _) hN

theorem u18_eval_hasSum {r : ℝ} {N : ℕ} (hN : r ≤ N) {f : Torus d → ℝ} (hf : Torus.IsSmooth f)
    (F : NegSobolev d r) :
    HasSum (fun k => NegSobolev.fourierCoeff F k * Torus.funRealCoeff f k) (NegSobolev.eval F f) := by
  have hsw := u18_summable_weighted hf N
  have hs : Summable fun k : NonzeroLattice d => NegSobolev.fourierCoeff F k * Torus.funRealCoeff f k := by
    refine Summable.of_norm_bounded (hsw.mul_left ‖F‖) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc |NegSobolev.fourierCoeff F k| * |Torus.funRealCoeff f k|
        ≤ (Lattice.jp k.1 ^ N * ‖F‖) * |Torus.funRealCoeff f k| :=
          mul_le_mul_of_nonneg_right (u18_abs_fourierCoeff_le_nat hN F k) (abs_nonneg _)
      _ = ‖F‖ * (|Torus.funRealCoeff f k| * Lattice.jp k.1 ^ N) := by ring
  exact hs.hasSum

theorem u18_kernel_hasSum {s : ℝ} {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (x y : Torus d) :
    HasSum (fun k : NonzeroLattice d => Torus.funRealCoeff f k *
      HRS.Main.hKernel d s (Torus.grad (Torus.realMode k)) x y) (HRS.Main.hKernel d s (Torus.grad f) x y) := by
  have hx := u18_hasSum_grad hf x
  have hy := u18_hasSum_grad hf y
  have h := (innerSL ℝ (periodicRieszGrad d s (x - y))).hasSum (hx.sub hy)
  unfold HRS.Main.hKernel
  convert h using 1
  · funext k
    simp only [innerSL_apply_apply, ← smul_sub, real_inner_smul_right]
    rw [real_inner_comm]
  · simp only [innerSL_apply_apply, real_inner_comm (periodicRieszGrad d s (x - y))]

end PairGeneral

section PairFormula

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `E[B(f) X Y] = ∬ h_f χ χ'` for a Wick-quadratic field `B`, smooth `f`, and Gaussian `X, Y`. -/
theorem u18_pair_formula {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d)
    {r : ℝ} {η B : Ω → NegSobolev d r} (hBm : Measurable B)
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)))
    (hW : IsWickQuadraticField s P η μ B)
    {𝒢 : Submodule ℝ (Ω → ℝ)} (hG : QrpwG4 P 𝒢)
    (hA : ∀ l, (fun ω => NegSobolev.fourierCoeff (η ω) l) ∈ 𝒢)
    {X Y : Ω → ℝ} (hX : X ∈ 𝒢) (hY : Y ∈ 𝒢)
    {χ χ' : Torus d → ℝ} (hχ : Torus.IsSmooth χ) (hχ' : Torus.IsSmooth χ')
    (hm : Torus.mean χ = 0) (hm' : Torus.mean χ' = 0)
    (hEX : ∀ l, ∫ ω, NegSobolev.fourierCoeff (η ω) l * X ω ∂P = Torus.funRealCoeff χ l)
    (hEY : ∀ l, ∫ ω, NegSobolev.fourierCoeff (η ω) l * Y ω ∂P = Torus.funRealCoeff χ' l)
    {f : Torus d → ℝ} (hf : Torus.IsSmooth f)
    (hint : Integrable (fun ω => ‖B ω‖ * |X ω * Y ω|) P) :
    ∫ ω, NegSobolev.eval (B ω) f * (X ω * Y ω) ∂P =
      ∫ x, ∫ y, HRS.Main.hKernel d s (Torus.grad f) x y * χ x * χ' y := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, r ≤ N := ⟨⌈r⌉₊, Nat.le_ceil r⟩
  set c : NonzeroLattice d → ℝ := fun k => Torus.funRealCoeff f k with hc
  have hsw := u18_summable_weighted hf N
  have hsw1 := u18_summable_weighted hf 1
  have hdχ : ∀ n : ℕ, ContDiff ℝ n (Torus.lift χ) := fun n =>
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift χ) from hχ).of_le (by exact_mod_cast le_top)
  have hdχ' : ∀ n : ℕ, ContDiff ℝ n (Torus.lift χ') := fun n =>
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift χ') from hχ').of_le (by exact_mod_cast le_top)
  have hcχ : Continuous χ := Torus.continuous_of_continuous_lift (hdχ 0).continuous
  have hcχ' : Continuous χ' := Torus.continuous_of_continuous_lift (hdχ' 0).continuous
  have hsχ := Torus.summable_fcoef_of_contDiff hdχ
  have hsχ' := Torus.summable_fcoef_of_contDiff hdχ'
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hcχ.continuousOn
  obtain ⟨M', hM'⟩ := isCompact_univ.exists_bound_of_continuousOn hcχ'.continuousOn
  have hMb : ∀ x, |χ x| ≤ M := fun x => by simpa [Real.norm_eq_abs] using hM x (Set.mem_univ x)
  have hMb' : ∀ x, |χ' x| ≤ M' := fun x => by simpa [Real.norm_eq_abs] using hM' x (Set.mem_univ x)
  have hQ : ∀ k : NonzeroLattice d, Measurable fun ω => NegSobolev.eval (B ω) (Torus.realMode k) := by
    intro k
    have : (fun ω => NegSobolev.eval (B ω) (Torus.realMode k)) =
        fun ω => HRS.FieldSingAux.coordCLM r k (B ω) := by
      funext ω; exact HRS.AdjK.adjkd_eval_realMode (B ω) k
    rw [this]
    exact (HRS.FieldSingAux.coordCLM r k).continuous.measurable.comp hBm
  have hXm : AEStronglyMeasurable X P := (hG _ hX).1.aestronglyMeasurable
  have hYm : AEStronglyMeasurable Y P := (hG _ hY).1.aestronglyMeasurable
  have hXYm : AEStronglyMeasurable (fun ω => X ω * Y ω) P := hXm.mul hYm
  -- the basis pairing
  have hbasis : ∀ k : NonzeroLattice d, ∫ ω, NegSobolev.eval (B ω) (Torus.realMode k) * (X ω * Y ω) ∂P =
      ∫ x, ∫ y, HRS.Main.hKernel d s (Torus.grad (Torus.realMode k)) x y * χ x * χ' y := fun k =>
    u18_pair_basis hd hs0 hs1 (hQ k).aestronglyMeasurable hΛ hμ k (hW k) hG hA hX hY hcχ hcχ'
      hsχ hsχ' hm hm' hEX hEY
  -- the series in `k`
  have hb := hasSum_integral_of_dominated_convergence (μ := P)
    (F := fun (k : NonzeroLattice d) ω => (c k * NegSobolev.eval (B ω) (Torus.realMode k)) * (X ω * Y ω))
    (f := fun ω => NegSobolev.eval (B ω) f * (X ω * Y ω))
    (fun k ω => (|c k| * Lattice.jp k.1 ^ N) * (‖B ω‖ * |X ω * Y ω|))
    (fun k => (((hQ k).const_mul (c k)).aestronglyMeasurable).mul hXYm)
    (fun k => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, HRS.AdjK.adjkd_eval_realMode]
      calc |c k| * |NegSobolev.fourierCoeff (B ω) k| * |X ω * Y ω|
          ≤ |c k| * (Lattice.jp k.1 ^ N * ‖B ω‖) * |X ω * Y ω| := by
            gcongr
            exact u18_abs_fourierCoeff_le_nat hN (B ω) k
        _ = (|c k| * Lattice.jp k.1 ^ N) * (‖B ω‖ * |X ω * Y ω|) := by ring)
    (Eventually.of_forall fun ω => hsw.mul_right _)
    (by
      simp_rw [tsum_mul_right]
      exact hint.const_mul _)
    (Eventually.of_forall fun ω => by
      have h1 := (u18_eval_hasSum hN hf (B ω)).mul_right (X ω * Y ω)
      have e : (fun k : NonzeroLattice d => (c k * NegSobolev.eval (B ω) (Torus.realMode k)) * (X ω * Y ω)) =
          fun k => NegSobolev.fourierCoeff (B ω) k * Torus.funRealCoeff f k * (X ω * Y ω) := by
        funext k; rw [HRS.AdjK.adjkd_eval_realMode]; simp only [hc]; ring
      rw [e]; exact h1)
  have hser := u18_series_pair (G := fun z => ‖periodicRieszGrad d s z‖) (u18_K_integrable hd hs0 hs1)
    (fun z => norm_nonneg _) (hk := fun k => HRS.Main.hKernel d s (Torus.grad (Torus.realMode k)))
    (ak := fun k => 2 * (Real.sqrt 2 * Lattice.jp k.1))
    (fun k => u18_pairKer_realMode hd hs0 hs1 k) c
    (by
      refine (hsw1.mul_left (2 * Real.sqrt 2)).congr fun k => ?_
      simp only [pow_one]; ring)
    (fun x y => u18_kernel_hasSum hf x y) hcχ.measurable hcχ'.measurable hMb hMb'
  have hb' : HasSum (fun k : NonzeroLattice d => c k * ∫ x, ∫ y,
      HRS.Main.hKernel d s (Torus.grad (Torus.realMode k)) x y * χ x * χ' y)
      (∫ ω, NegSobolev.eval (B ω) f * (X ω * Y ω) ∂P) := by
    have hterm : ∀ k : NonzeroLattice d, ∫ ω, (c k * NegSobolev.eval (B ω) (Torus.realMode k)) * (X ω * Y ω) ∂P =
        c k * ∫ x, ∫ y, HRS.Main.hKernel d s (Torus.grad (Torus.realMode k)) x y * χ x * χ' y := by
      intro k
      have e : (fun ω => (c k * NegSobolev.eval (B ω) (Torus.realMode k)) * (X ω * Y ω)) =
          fun ω => c k * (NegSobolev.eval (B ω) (Torus.realMode k) * (X ω * Y ω)) := by
        funext ω; ring
      rw [e, integral_const_mul, hbasis k]
    simp_rw [hterm] at hb
    exact hb
  exact hb'.unique hser

end PairFormula

end HRS.MC.E213U18

end
