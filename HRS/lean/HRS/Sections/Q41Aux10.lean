import Mathlib
import HRS.Sections.Q41Aux9

/-!
# Packet Q41, helper 10: the Gaussian family on dyadic times and Fourier modes
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Matrix RealInnerProductSpace

namespace HRS.Q41

open HRS

variable {d : ℕ} {r : ℝ → ℝ → NonzeroLattice d → NonzeroLattice d → ℝ}

/-- The nonnegative dyadic rationals. -/
def q41_D : Set ℝ := Set.range fun p : ℕ × ℕ => (p.2 : ℝ) / 2 ^ p.1

lemma q41_D_nonneg {q : ℝ} (hq : q ∈ q41_D) : 0 ≤ q := by
  obtain ⟨⟨n, j⟩, rfl⟩ := hq
  positivity

lemma q41_D_mem (n j : ℕ) : (j : ℝ) / 2 ^ n ∈ q41_D := ⟨(n, j), rfl⟩

instance q41_D_countable : Countable q41_D := (Set.countable_range _).to_subtype

/-- A centred Gaussian family indexed by dyadic times and modes with covariance `r`. -/
lemma q41_gp_family (hd : 1 ≤ d) (hr : ModeKernel d r) :
    ∃ Y : q41_D × NonzeroLattice d → (ℕ → ℝ) → ℝ, (∀ i, Measurable (Y i)) ∧
      IsGaussianProcess Y gpP ∧ (∀ i, ∫ ω, Y i ω ∂gpP = 0) ∧
      ∀ i j, cov[Y i, Y j; gpP] = r i.1.1 j.1.1 i.2 j.2 := by
  classical
  haveI : Nonempty (NonzeroLattice d) := ⟨⟨Pi.single ⟨0, by omega⟩ 1, by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this⟩⟩
  haveI : Nonempty q41_D := ⟨⟨(0 : ℕ) / 2 ^ (0 : ℕ), q41_D_mem 0 0⟩⟩
  obtain ⟨en, hen⟩ := exists_surjective_nat (q41_D × NonzeroLattice d)
  set K : ℕ → ℕ → ℝ := fun n n' => r (en n).1.1 (en n').1.1 (en n).2 (en n').2 with hK
  have hsymm : ∀ i j, K i j = K j i := fun i j => hr.symm _ _ _ _
  have hpsd : ∀ n (c : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, c i * c j * K i j := by
    intro n c
    have := (hr.psd (Fin n) (fun a => (en a).1.1) (fun a => (en a).2)
      (fun a => q41_D_nonneg (en a).1.2)).dotProduct_mulVec_nonneg c
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, Finset.mul_sum] at this
    refine le_of_le_of_eq this ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hK]; ring
  obtain ⟨X, hXm, hXg, hXmean, hXcov⟩ := q41_exists_gaussian_process K hsymm hpsd
  refine ⟨fun i => X (Function.surjInv hen i), fun i => hXm _, ?_, fun i => hXmean _, ?_⟩
  · exact hXg.comp_right (Function.surjInv hen)
  · intro i j
    rw [hXcov, hK]
    simp only [Function.surjInv_eq hen]

/-- A centred Gaussian family on the dyadic times and modes, with covariance `r`. -/
structure Q41Fam (d : ℕ) (r : ℝ → ℝ → NonzeroLattice d → NonzeroLattice d → ℝ) where
  Y : q41_D × NonzeroLattice d → (ℕ → ℝ) → ℝ
  meas : ∀ i, Measurable (Y i)
  gauss : IsGaussianProcess Y gpP
  mean : ∀ i, ∫ ω, Y i ω ∂gpP = 0
  cov : ∀ i j, cov[Y i, Y j; gpP] = r i.1.1 j.1.1 i.2 j.2

lemma Q41Fam.memLp (F : Q41Fam d r) (i) : MemLp (F.Y i) 2 gpP :=
  (F.gauss.hasGaussianLaw_eval i).memLp_two

/-- Law of a centred Gaussian combination `Y i - Y j` (or `Y i` via `a = 0`). -/
lemma Q41Fam.law_sub (F : Q41Fam d r) (i j : q41_D × NonzeroLattice d) :
    gpP.map (fun ω => F.Y i ω - F.Y j ω) =
      gaussianReal 0 (r i.1.1 i.1.1 i.2 i.2 + r j.1.1 j.1.1 j.2 j.2 - 2 * r i.1.1 j.1.1 i.2 j.2).toNNReal := by
  have hg : HasGaussianLaw (fun ω => F.Y i ω - F.Y j ω) gpP := F.gauss.hasGaussianLaw_fun_sub
  rw [hg.map_eq_gaussianReal]
  congr 1
  · rw [integral_sub ((F.memLp i).integrable (by norm_num)) ((F.memLp j).integrable (by norm_num)),
      F.mean, F.mean]; simp
  · congr 1
    have := variance_fun_sub (μ := gpP) (F.memLp i) (F.memLp j)
    rw [this, ← covariance_self (F.meas i).aemeasurable, ← covariance_self (F.meas j).aemeasurable,
      F.cov, F.cov, F.cov]
    ring

lemma Q41Fam.law_single (F : Q41Fam d r) (i : q41_D × NonzeroLattice d) :
    gpP.map (F.Y i) = gaussianReal 0 (r i.1.1 i.1.1 i.2 i.2).toNNReal := by
  have hg : HasGaussianLaw (F.Y i) gpP := F.gauss.hasGaussianLaw_eval i
  rw [hg.map_eq_gaussianReal, F.mean]
  congr 1
  rw [← covariance_self (F.meas i).aemeasurable, F.cov]

lemma q41_summable_of_tsum_ofReal_ne_top {ι : Type*} (f : ι → ℝ) (hf : ∀ k, 0 ≤ f k)
    (h : ∑' k, ENNReal.ofReal (f k) ≠ ⊤) : Summable f := by
  have e : ∀ k, ENNReal.ofReal (f k) = (((f k).toNNReal : ℝ≥0) : ℝ≥0∞) := fun k => rfl
  simp_rw [e] at h
  rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe] at h
  simpa only [Real.coe_toNNReal _ (hf _)] using h

lemma q41_ae_summable_sq {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (P : Measure Ω)
    (g : ι → Ω → ℝ) (w : ι → ℝ) (hw : ∀ k, 0 ≤ w k) (hg : ∀ k, Measurable (g k)) (v : ι → ℝ≥0)
    (hlaw : ∀ k, P.map (g k) = gaussianReal 0 (v k))
    (hfin : ∑' k, ENNReal.ofReal (w k * (v k : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, Summable fun k => w k * g k ω ^ 2 := by
  have hmom := q41_weighted_sq_moment P g w hw hg v hlaw
  set S : Ω → ℝ≥0∞ := fun ω => ∑' k, ENNReal.ofReal (w k * g k ω ^ 2) with hS
  have hSm : Measurable S :=
    Measurable.ennreal_tsum fun k => ENNReal.measurable_ofReal.comp (((hg k).pow_const 2).const_mul _)
  have hfin2 : ∫⁻ ω, S ω ^ 2 ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hfin)) hmom
  filter_upwards [ae_lt_top (hSm.pow_const 2) hfin2] with ω hω
  have hS' : S ω ≠ ⊤ := fun h => by simp [h] at hω
  exact q41_summable_of_tsum_ofReal_ne_top _ (fun k => mul_nonneg (hw k) (sq_nonneg _)) hS'

/-- the weights `⟨k⟩^{-2m}` -/
def q41_w (d : ℕ) (m : ℝ) (k : NonzeroLattice d) : ℝ := Lattice.jp k.1 ^ (-(2 * m))

lemma q41_w_nonneg (m : ℝ) (k : NonzeroLattice d) : 0 ≤ q41_w d m k :=
  Real.rpow_nonneg (Torus.jp_pos k.1).le _

lemma q41_w_eq_sq (m : ℝ) (k : NonzeroLattice d) :
    (Lattice.jp k.1 ^ (-m)) ^ 2 = q41_w d m k := by
  unfold q41_w
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Torus.jp_pos k.1).le]
  congr 1; push_cast; ring

lemma q41_w_mul_jp_sq (m : ℝ) (k : NonzeroLattice d) :
    q41_w d m k * Lattice.jp k.1 ^ 2 = Lattice.jp k.1 ^ (-(2 * (m - 1))) := by
  unfold q41_w
  rw [show Lattice.jp k.1 ^ 2 = Lattice.jp k.1 ^ ((2 : ℝ)) by rw [Real.rpow_two],
    ← Real.rpow_add (Torus.jp_pos k.1)]
  congr 1; ring

lemma q41_tsum_ofReal_ne_top_of_le {ι : Type*} (f g : ι → ℝ) (hg0 : ∀ k, 0 ≤ g k)
    (hg : Summable g) (hf : ∀ k, f k ≤ g k) : ∑' k, ENNReal.ofReal (f k) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hf k))
  rw [← ENNReal.ofReal_tsum_of_nonneg hg0 hg]
  exact ENNReal.ofReal_ne_top

lemma Q41Fam.ae_memℓp (F : Q41Fam d r) {m : ℝ} (hm : (d : ℝ) < 2 * m) {B : ℝ}
    (hB : ∀ (q : q41_D) (k : NonzeroLattice d), r q q k k ≤ B) (q : q41_D) :
    ∀ᵐ ω ∂gpP, Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * F.Y (q, k) ω) 2 := by
  have hS0 : Summable (q41_w d m) := summable_jp_rpow m hm
  have hfin : ∑' k, ENNReal.ofReal (q41_w d m k * (((r q q k k).toNNReal : ℝ≥0) : ℝ)) ≠ ⊤ := by
    refine q41_tsum_ofReal_ne_top_of_le _ (fun k => |B| * q41_w d m k)
      (fun k => mul_nonneg (abs_nonneg _) (q41_w_nonneg m k)) (hS0.mul_left _) fun k => ?_
    have h1 : (((r q q k k).toNNReal : ℝ≥0) : ℝ) ≤ |B| := by
      rw [Real.coe_toNNReal']
      exact max_le ((hB q k).trans (le_abs_self B)) (abs_nonneg B)
    nlinarith [q41_w_nonneg m k]
  have := q41_ae_summable_sq gpP (fun k => F.Y (q, k)) (q41_w d m) (q41_w_nonneg m)
    (fun k => F.meas _) (fun k => (r q q k k).toNNReal) (fun k => F.law_single (q, k)) hfin
  filter_upwards [this] with ω hω
  rw [Torus.memℓp_two_iff]
  refine hω.congr fun k => ?_
  rw [mul_pow, q41_w_eq_sq]

lemma q41_exists_enum (hd : 1 ≤ d) : ∃ e : ℕ → NonzeroLattice d, Function.Surjective e := by
  haveI : Nonempty (NonzeroLattice d) := ⟨⟨Pi.single ⟨0, by omega⟩ 1, by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this⟩⟩
  exact exists_surjective_nat _

/-- The `E_m`-valued coordinate process at dyadic times. -/
def Q41Fam.Zd (F : Q41Fam d r) (m : ℝ) (q : q41_D) (ω : ℕ → ℝ) : NegSobolev d m :=
  NegSobolev.ofSeq m (fun k => F.Y (q, k) ω)

/-- Extension by `0` to all real times. -/
def Q41Fam.Zbar (F : Q41Fam d r) (m : ℝ) (t : ℝ) (ω : ℕ → ℝ) : NegSobolev d m :=
  open Classical in if h : t ∈ q41_D then F.Zd m ⟨t, h⟩ ω else 0

lemma Q41Fam.measurable_Zd (F : Q41Fam d r) (hd : 1 ≤ d) (m : ℝ) (q : q41_D) :
    Measurable (F.Zd m q) := by
  obtain ⟨e, he⟩ := q41_exists_enum hd
  exact q41_measurable_ofSeq e he (fun k => F.Y (q, k)) (fun k => F.meas _)

lemma Q41Fam.measurable_Zbar (F : Q41Fam d r) (hd : 1 ≤ d) (m : ℝ) (t : ℝ) :
    Measurable (F.Zbar m t) := by
  unfold Q41Fam.Zbar
  by_cases h : t ∈ q41_D
  · simp only [dif_pos h]; exact F.measurable_Zd hd m _
  · simp only [dif_neg h]; exact measurable_const

/-- Fourth moment of increments of the `E_m`-valued dyadic process. -/
lemma Q41Fam.moment (F : Q41Fam d r) (hd : 1 ≤ d) {m : ℝ} (hm : (d : ℝ) + 2 < 2 * m) {B Bi : ℝ}
    (hB : ∀ (q : q41_D) (k : NonzeroLattice d), r q q k k ≤ B)
    (hBi : ∀ (q q' : q41_D) (k : NonzeroLattice d),
      r q' q' k k + r q q k k - 2 * r q' q k k ≤ Bi * Lattice.jp k.1 ^ 2 * |(q' : ℝ) - q|)
    (q q' : q41_D) :
    ∫⁻ ω, ENNReal.ofReal (‖F.Zd m q' ω - F.Zd m q ω‖ ^ 4) ∂gpP ≤
      ENNReal.ofReal (48 * Real.exp (1 / 2) *
        (|Bi| * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - 1)))) ^ 2 *
        |(q' : ℝ) - q| ^ 2) := by
  have hm0 : (d : ℝ) < 2 * m := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hS1 : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(2 * (m - 1))) :=
    summable_jp_rpow (m - 1) (by linarith)
  set S1 := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - 1))) with hS1def
  set h := |(q' : ℝ) - q| with hh
  set g : NonzeroLattice d → (ℕ → ℝ) → ℝ := fun k ω => F.Y (q', k) ω - F.Y (q, k) ω with hg
  set v : NonzeroLattice d → ℝ≥0 := fun k =>
    (r q' q' k k + r q q k k - 2 * r q' q k k).toNNReal with hv
  have hlaw : ∀ k, gpP.map (g k) = gaussianReal 0 (v k) := fun k => F.law_sub (q', k) (q, k)
  have hvle : ∀ k, (v k : ℝ) ≤ |Bi| * Lattice.jp k.1 ^ 2 * h := by
    intro k
    simp only [hv]
    rw [Real.coe_toNNReal']
    refine max_le ?_ (by positivity)
    refine (hBi q q' k).trans ?_
    have : 0 ≤ Lattice.jp k.1 ^ 2 * |(q' : ℝ) - q| := by positivity
    nlinarith [le_abs_self Bi, mul_nonneg this (abs_nonneg Bi)]
  have hfin : ∑' k, ENNReal.ofReal (q41_w d m k * (v k : ℝ)) ≤
      ENNReal.ofReal (|Bi| * h * S1) := by
    have h1 : ∀ k, ENNReal.ofReal (q41_w d m k * (v k : ℝ)) ≤
        ENNReal.ofReal (|Bi| * h * Lattice.jp k.1 ^ (-(2 * (m - 1)))) := by
      intro k
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← q41_w_mul_jp_sq m k]
      calc q41_w d m k * (v k : ℝ) ≤ q41_w d m k * (|Bi| * Lattice.jp k.1 ^ 2 * h) :=
            mul_le_mul_of_nonneg_left (hvle k) (q41_w_nonneg m k)
        _ = _ := by ring
    refine (ENNReal.tsum_le_tsum h1).trans ?_
    have hnn : ∀ k : NonzeroLattice d, 0 ≤ |Bi| * h * Lattice.jp k.1 ^ (-(2 * (m - 1))) :=
      fun k => by have := Torus.jp_pos k.1; positivity
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn (hS1.mul_left _), tsum_mul_left]
  have hmom := q41_weighted_sq_moment gpP g (q41_w d m) (q41_w_nonneg m) (fun k => (F.meas _).sub (F.meas _))
    v hlaw
  -- almost sure identification
  have hae : ∀ᵐ ω ∂gpP, ENNReal.ofReal (‖F.Zd m q' ω - F.Zd m q ω‖ ^ 4) =
      (∑' k, ENNReal.ofReal (q41_w d m k * g k ω ^ 2)) ^ 2 := by
    filter_upwards [F.ae_memℓp hm0 hB q, F.ae_memℓp hm0 hB q'] with ω h1 h2
    have hsub : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (F.Y (q', k) ω - F.Y (q, k) ω)) 2 := by
      have := h2.sub h1
      convert this using 1
      funext k
      simp [mul_sub]
    have hsum : Summable fun k : NonzeroLattice d => (Lattice.jp k.1 ^ (-m) * (F.Y (q', k) ω - F.Y (q, k) ω)) ^ 2 :=
      (Torus.memℓp_two_iff _).1 hsub
    have hnorm := q41_norm_sq_sub (m := m) (c := fun k => F.Y (q', k) ω) (c' := fun k => F.Y (q, k) ω) h2 h1
    have hfk : ∀ k, (Lattice.jp k.1 ^ (-m) * (F.Y (q', k) ω - F.Y (q, k) ω)) ^ 2 =
        q41_w d m k * g k ω ^ 2 := fun k => by rw [mul_pow, q41_w_eq_sq]
    have e1 : ‖F.Zd m q' ω - F.Zd m q ω‖ ^ 4 = (‖F.Zd m q' ω - F.Zd m q ω‖ ^ 2) ^ 2 := by ring
    rw [e1, ENNReal.ofReal_pow (by positivity)]
    unfold Q41Fam.Zd
    rw [hnorm, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hsum]
    simp_rw [hfk]
  calc ∫⁻ ω, ENNReal.ofReal (‖F.Zd m q' ω - F.Zd m q ω‖ ^ 4) ∂gpP
      = ∫⁻ ω, (∑' k, ENNReal.ofReal (q41_w d m k * g k ω ^ 2)) ^ 2 ∂gpP := lintegral_congr_ae hae
    _ ≤ ENNReal.ofReal (48 * Real.exp (1 / 2)) *
          (∑' k, ENNReal.ofReal (q41_w d m k * (v k : ℝ))) ^ 2 := hmom
    _ ≤ ENNReal.ofReal (48 * Real.exp (1 / 2)) * (ENNReal.ofReal (|Bi| * h * S1)) ^ 2 := by
        gcongr
    _ = ENNReal.ofReal (48 * Real.exp (1 / 2) * (|Bi| * S1) ^ 2 * h ^ 2) := by
        have hS1nn : 0 ≤ S1 := tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
        have hh0 : 0 ≤ h := abs_nonneg _
        have hx : 0 ≤ |Bi| * h * S1 := by positivity
        rw [← ENNReal.ofReal_pow hx, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

lemma Q41Fam.Zbar_of_mem (F : Q41Fam d r) (m : ℝ) (q : q41_D) (ω : ℕ → ℝ) :
    F.Zbar m (q : ℝ) ω = F.Zd m q ω := by
  unfold Q41Fam.Zbar
  rw [dif_pos q.2]

/-- the constant `ρ = 1 / (2 c⁴)` for `c = 9/10` -/
def q41_rho : ℝ := 10000 / 13122

lemma q41_rho_lt_one : q41_rho < 1 := by unfold q41_rho; norm_num

lemma q41_rho_pos : 0 < q41_rho := by unfold q41_rho; norm_num

lemma q41_rho_identity (n : ℕ) :
    (1 / (2 : ℝ) ^ n) ^ 2 / ((9 / 10 : ℝ) ^ n) ^ 4 = (q41_rho / 2) ^ n := by
  unfold q41_rho
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (10000 / 13122 / 2 : ℝ), ← ih]
    rw [pow_succ (2 : ℝ), pow_succ (9 / 10 : ℝ)]
    field_simp
    ring

/-- Tail bound for one dyadic increment. -/
lemma Q41Fam.tail_bound (F : Q41Fam d r) (hd : 1 ≤ d) {m : ℝ} (hm : (d : ℝ) + 2 < 2 * m) {B Bi : ℝ}
    (hB : ∀ (q : q41_D) (k : NonzeroLattice d), r q q k k ≤ B)
    (hBi : ∀ (q q' : q41_D) (k : NonzeroLattice d),
      r q' q' k k + r q q k k - 2 * r q' q k k ≤ Bi * Lattice.jp k.1 ^ 2 * |(q' : ℝ) - q|)
    (n j : ℕ) :
    gpP {ω | (9 / 10 : ℝ) ^ n < ‖F.Zbar m (((j : ℝ) + 1) / 2 ^ n) ω - F.Zbar m ((j : ℝ) / 2 ^ n) ω‖} ≤
      ENNReal.ofReal (48 * Real.exp (1 / 2) *
        (|Bi| * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - 1)))) ^ 2 *
          (q41_rho / 2) ^ n) := by
  set q : q41_D := ⟨(j : ℝ) / 2 ^ n, q41_D_mem n j⟩ with hq
  set q' : q41_D := ⟨((j + 1 : ℕ) : ℝ) / 2 ^ n, q41_D_mem n (j + 1)⟩ with hq'
  have e1 : (((j : ℝ) + 1) / 2 ^ n) = (q' : ℝ) := by simp [hq']
  have e2 : ((j : ℝ) / 2 ^ n) = (q : ℝ) := by simp [hq]
  rw [e1, e2]
  simp only [F.Zbar_of_mem]
  set M := 48 * Real.exp (1 / 2) * (|Bi| * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - 1)))) ^ 2
    with hM
  have hmom := F.moment hd hm hB hBi q q'
  have hh : |(q' : ℝ) - q| = 1 / 2 ^ n := by
    simp only [hq, hq']
    rw [show (((j + 1 : ℕ) : ℝ) / 2 ^ n - (j : ℝ) / 2 ^ n) = 1 / 2 ^ n by push_cast; ring,
      abs_of_nonneg (by positivity)]
  rw [hh] at hmom
  have hc : (0 : ℝ) < ((9 / 10 : ℝ) ^ n) ^ 4 := by positivity
  have hsub : {ω | (9 / 10 : ℝ) ^ n < ‖F.Zd m q' ω - F.Zd m q ω‖} ⊆
      {ω | ENNReal.ofReal (((9 / 10 : ℝ) ^ n) ^ 4) ≤ ENNReal.ofReal (‖F.Zd m q' ω - F.Zd m q ω‖ ^ 4)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hω.le 4)
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (‖F.Zd m q' ω - F.Zd m q ω‖ ^ 4)) gpP :=
    (ENNReal.measurable_ofReal.comp
      (((F.measurable_Zd hd m q').sub (F.measurable_Zd hd m q)).norm.pow_const 4)).aemeasurable
  calc gpP {ω | (9 / 10 : ℝ) ^ n < ‖F.Zd m q' ω - F.Zd m q ω‖}
      ≤ gpP {ω | ENNReal.ofReal (((9 / 10 : ℝ) ^ n) ^ 4) ≤
          ENNReal.ofReal (‖F.Zd m q' ω - F.Zd m q ω‖ ^ 4)} := measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal (‖F.Zd m q' ω - F.Zd m q ω‖ ^ 4) ∂gpP) /
          ENNReal.ofReal (((9 / 10 : ℝ) ^ n) ^ 4) :=
        meas_ge_le_lintegral_div hmeas (by simpa using hc) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (M * (1 / 2 ^ n) ^ 2) / ENNReal.ofReal (((9 / 10 : ℝ) ^ n) ^ 4) := by
        gcongr
    _ = ENNReal.ofReal (M * (1 / 2 ^ n) ^ 2 / ((9 / 10 : ℝ) ^ n) ^ 4) := by
        rw [← ENNReal.ofReal_div_of_pos hc]
    _ = ENNReal.ofReal (M * (q41_rho / 2) ^ n) := by
        congr 1
        have : (1 / (2 : ℝ) ^ n) ^ 2 / ((9 / 10 : ℝ) ^ n) ^ 4 = (q41_rho / 2) ^ n :=
          q41_rho_identity n
        rw [mul_div_assoc, this]

end HRS.Q41
