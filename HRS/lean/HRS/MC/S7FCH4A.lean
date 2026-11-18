import HRS.MC.S7FCW12G
import HRS.MC.S7FCH1A

/-!
# S7FCH4A: the `E_r`-level maps of the finite-rank pair (H4, part A)

For a finite set of modes `S` and kernels `K k` (`FRKernel`): the basis elements `e_k`, the finite sum representation
`ofSeq r (1_S x) = ∑_{k∈S} x_k e_k`, and the maps `g(F) = ∑_{k∈S} Φ_{K_k}(F) e_k` (quadratic) and
`h(F) = ∑_{k∈S} lin_{K_k}(F) e_k` (linear, the `N^{-1/2}` diagonal correction of H1a) with their local Lipschitz bounds.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace HRS.MC.Sec7.S7FCH4
open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan
open Classical
variable {d : ℕ}

/-- The basis element of `E_r` with unweighted coefficient sequence `δ_k`. -/
def S7FCH4_e (r : ℝ) (k : NonzeroLattice d) : NegSobolev d r :=
  NegSobolev.ofSeq r (fun l => if l = k then 1 else 0)

theorem S7FCH4_ext {r : ℝ} {F G : NegSobolev d r} (h : ∀ l, NegSobolev.coord F l = NegSobolev.coord G l) :
    F = G := Subtype.ext (funext h)

theorem S7FCH4_memlp_finite (r : ℝ) (S : Finset (NonzeroLattice d)) (x : NonzeroLattice d → ℝ) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) * (if k ∈ S then x k else 0)) 2 := by
  rw [Torus.memℓp_two_iff]
  apply summable_of_hasFiniteSupport
  refine (S.finite_toSet).subset ?_
  intro k hk
  by_contra hkS
  simp only [Function.mem_support] at hk
  simp [hkS] at hk
  exact hkS hk.1

theorem S7FCH4_memlp_single (r : ℝ) (k : NonzeroLattice d) :
    Memℓp (fun l : NonzeroLattice d => Lattice.jp l.1 ^ (-r) * (if l = k then (1:ℝ) else 0)) 2 := by
  have := S7FCH4_memlp_finite r {k} (fun _ => 1)
  simpa using this

theorem S7FCH4_coord_e (r : ℝ) (k l : NonzeroLattice d) :
    NegSobolev.coord (S7FCH4_e r k) l = Lattice.jp l.1 ^ (-r) * (if l = k then (1:ℝ) else 0) := by
  unfold S7FCH4_e
  exact NegSobolev.coord_ofSeq_of_mem _ (S7FCH4_memlp_single r k) l

theorem S7FCH4_ofSeq_sum (r : ℝ) (S : Finset (NonzeroLattice d)) (x : NonzeroLattice d → ℝ) :
    NegSobolev.ofSeq r (fun k => if k ∈ S then x k else 0) = ∑ k ∈ S, x k • S7FCH4_e r k := by
  apply S7FCH4_ext
  intro l
  rw [NegSobolev.coord_ofSeq_of_mem _ (S7FCH4_memlp_finite r S x) l]
  have hsum : ∀ T : Finset (NonzeroLattice d), NegSobolev.coord (∑ k ∈ T, x k • S7FCH4_e r k) l =
      ∑ k ∈ T, x k * NegSobolev.coord (S7FCH4_e r k) l := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp; rfl
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      rfl
  rw [hsum S]
  simp only [S7FCH4_coord_e]
  by_cases hl : l ∈ S
  · rw [Finset.sum_eq_single l]
    · simp [hl]; ring
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd hl h
  · rw [Finset.sum_eq_zero]
    · simp [hl]
    · intro b hb
      have : l ≠ b := fun h => hl (h ▸ hb)
      simp [this]

/-! ### Evaluation against smooth test functions -/

/-- The dual-norm constant of a test function: `|F(f)| ≤ ‖F‖ cf f`. -/
def S7FCH4_cf (r : ℝ) (f : Torus d → ℝ) : ℝ :=
  Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * r) * Torus.funRealCoeff f k ^ 2)

theorem S7FCH4_cf_nonneg (r : ℝ) (f : Torus d → ℝ) : 0 ≤ S7FCH4_cf r f := Real.sqrt_nonneg _

theorem S7FCH4_abs_eval_le {r : ℝ} {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (F : NegSobolev d r) :
    |NegSobolev.eval F f| ≤ ‖F‖ * S7FCH4_cf r f :=
  NegSobolev.abs_eval_le F f (HRS.StaticLimitAux.summable_weighted_smooth r hf)

theorem S7FCH4_eval_sub {r : ℝ} {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (F G : NegSobolev d r) :
    NegSobolev.eval (F - G) f = NegSobolev.eval F f - NegSobolev.eval G f :=
  HRS.MC.Sec7.S7FCW12.s7fcw12_eval_sub F G f (HRS.StaticLimitAux.summable_weighted_smooth r hf)

theorem S7FCH4_abs_eval_sub_le {r : ℝ} {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (F G : NegSobolev d r) :
    |NegSobolev.eval F f - NegSobolev.eval G f| ≤ ‖F - G‖ * S7FCH4_cf r f := by
  rw [← S7FCH4_eval_sub hf]
  exact S7FCH4_abs_eval_le hf _

theorem S7FCH4_smooth_mul {f g : Torus d → ℝ} (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) :
    Torus.IsSmooth (fun x => f x * g x) := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift g) := hg
  exact hF.mul hG

/-! ### The quadratic and linear parts of a finite-rank kernel -/

/-- Lipschitz constant of the quadratic functional `Φ_K`. -/
def S7FCH4_qC (r : ℝ) (K : FRKernel d) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, |K.c i j| * S7FCH4_cf r (K.f i) * S7FCH4_cf r (K.f j)

theorem S7FCH4_qC_nonneg (r : ℝ) (K : FRKernel d) : 0 ≤ S7FCH4_qC r K := by
  unfold S7FCH4_qC
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (S7FCH4_cf_nonneg _ _)) (S7FCH4_cf_nonneg _ _)

theorem S7FCH4_quad_sub_le {r : ℝ} (K : FRKernel d) (F G : NegSobolev d r) :
    |K.quad F - K.quad G| ≤ S7FCH4_qC r K * ((‖F‖ + ‖G‖) * ‖F - G‖) := by
  have hbd : ∀ i j, |NegSobolev.eval F (K.f i) * NegSobolev.eval F (K.f j) -
      NegSobolev.eval G (K.f i) * NegSobolev.eval G (K.f j)| ≤
      S7FCH4_cf r (K.f i) * S7FCH4_cf r (K.f j) * ((‖F‖ + ‖G‖) * ‖F - G‖) := by
    intro i j
    set a := NegSobolev.eval F (K.f i)
    set b := NegSobolev.eval F (K.f j)
    set aa := NegSobolev.eval G (K.f i)
    set bb := NegSobolev.eval G (K.f j)
    have h1 : |a| ≤ ‖F‖ * S7FCH4_cf r (K.f i) := S7FCH4_abs_eval_le (K.smooth i) F
    have h2 : |bb| ≤ ‖G‖ * S7FCH4_cf r (K.f j) := S7FCH4_abs_eval_le (K.smooth j) G
    have h3 : |b - bb| ≤ ‖F - G‖ * S7FCH4_cf r (K.f j) := S7FCH4_abs_eval_sub_le (K.smooth j) F G
    have h4 : |a - aa| ≤ ‖F - G‖ * S7FCH4_cf r (K.f i) := S7FCH4_abs_eval_sub_le (K.smooth i) F G
    have e : a * b - aa * bb = a * (b - bb) + (a - aa) * bb := by ring
    have ci := S7FCH4_cf_nonneg r (K.f i)
    have cj := S7FCH4_cf_nonneg r (K.f j)
    calc |a * b - aa * bb| ≤ |a| * |b - bb| + |a - aa| * |bb| := by
          rw [e]; exact (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
      _ ≤ (‖F‖ * S7FCH4_cf r (K.f i)) * (‖F - G‖ * S7FCH4_cf r (K.f j)) +
          (‖F - G‖ * S7FCH4_cf r (K.f i)) * (‖G‖ * S7FCH4_cf r (K.f j)) := by
          gcongr
      _ = S7FCH4_cf r (K.f i) * S7FCH4_cf r (K.f j) * ((‖F‖ + ‖G‖) * ‖F - G‖) := by ring
  unfold FRKernel.quad S7FCH4_qC
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have : ∀ i, ∑ j, K.c i j * (NegSobolev.eval F (K.f i) * NegSobolev.eval F (K.f j)) -
      ∑ j, K.c i j * (NegSobolev.eval G (K.f i) * NegSobolev.eval G (K.f j)) =
      ∑ j, K.c i j * (NegSobolev.eval F (K.f i) * NegSobolev.eval F (K.f j) -
        NegSobolev.eval G (K.f i) * NegSobolev.eval G (K.f j)) := by
    intro i; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [this]
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul]
  calc |K.c i j| * |NegSobolev.eval F (K.f i) * NegSobolev.eval F (K.f j) -
        NegSobolev.eval G (K.f i) * NegSobolev.eval G (K.f j)|
      ≤ |K.c i j| * (S7FCH4_cf r (K.f i) * S7FCH4_cf r (K.f j) * ((‖F‖ + ‖G‖) * ‖F - G‖)) :=
        mul_le_mul_of_nonneg_left (hbd i j) (abs_nonneg _)
    _ = _ := by ring


theorem S7FCH4_eval_zero {r : ℝ} {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    NegSobolev.eval (0 : NegSobolev d r) f = 0 := by
  have := S7FCH4_abs_eval_le hf (0 : NegSobolev d r)
  simp at this
  exact this

theorem S7FCH4_quad_zero {r : ℝ} (K : FRKernel d) : K.quad (0 : NegSobolev d r) = 0 := by
  unfold FRKernel.quad
  simp [S7FCH4_eval_zero (K.smooth _)]

theorem S7FCH4_quad_abs_le {r : ℝ} (K : FRKernel d) (F : NegSobolev d r) :
    |K.quad F| ≤ S7FCH4_qC r K * (‖F‖ * ‖F‖) := by
  have := S7FCH4_quad_sub_le K F 0
  simpa [S7FCH4_quad_zero] using this

/-- The linear part `F ↦ ½ ∑ c_ij F(f_i f_j)` (the `N^{-1/2}`-correction of H1a). -/
def S7FCH4_lin {r : ℝ} (K : FRKernel d) (F : NegSobolev d r) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, K.c i j * NegSobolev.eval F (fun x => K.f i x * K.f j x)

def S7FCH4_linC (r : ℝ) (K : FRKernel d) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, |K.c i j| * S7FCH4_cf r (fun x => K.f i x * K.f j x)

theorem S7FCH4_linC_nonneg (r : ℝ) (K : FRKernel d) : 0 ≤ S7FCH4_linC r K := by
  unfold S7FCH4_linC
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (abs_nonneg _) (S7FCH4_cf_nonneg _ _))

theorem S7FCH4_lin_sub_le {r : ℝ} (K : FRKernel d) (F G : NegSobolev d r) :
    |S7FCH4_lin K F - S7FCH4_lin K G| ≤ S7FCH4_linC r K * ‖F - G‖ := by
  unfold S7FCH4_lin S7FCH4_linC
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have : ∀ i, ∑ j, K.c i j * NegSobolev.eval F (fun x => K.f i x * K.f j x) -
      ∑ j, K.c i j * NegSobolev.eval G (fun x => K.f i x * K.f j x) =
      ∑ j, K.c i j * (NegSobolev.eval F (fun x => K.f i x * K.f j x) -
        NegSobolev.eval G (fun x => K.f i x * K.f j x)) := by
    intro i; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [this]
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul]
  have h := S7FCH4_abs_eval_sub_le (S7FCH4_smooth_mul (K.smooth i) (K.smooth j)) F G
  calc |K.c i j| * |NegSobolev.eval F (fun x => K.f i x * K.f j x) -
        NegSobolev.eval G (fun x => K.f i x * K.f j x)|
      ≤ |K.c i j| * (‖F - G‖ * S7FCH4_cf r (fun x => K.f i x * K.f j x)) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by ring

theorem S7FCH4_lin_zero {r : ℝ} (K : FRKernel d) : S7FCH4_lin K (0 : NegSobolev d r) = 0 := by
  unfold S7FCH4_lin
  simp [S7FCH4_eval_zero (S7FCH4_smooth_mul (K.smooth _) (K.smooth _))]

theorem S7FCH4_lin_abs_le {r : ℝ} (K : FRKernel d) (F : NegSobolev d r) :
    |S7FCH4_lin K F| ≤ S7FCH4_linC r K * ‖F‖ := by
  have := S7FCH4_lin_sub_le K F 0
  simpa [S7FCH4_lin_zero] using this

theorem S7FCH4_lin_continuous {r : ℝ} (K : FRKernel d) : Continuous (S7FCH4_lin (r := r) K) := by
  have : LipschitzWith (S7FCH4_linC r K).toNNReal (S7FCH4_lin (r := r) K) := by
    refine LipschitzWith.of_dist_le_mul fun F G => ?_
    rw [Real.dist_eq, Real.coe_toNNReal _ (S7FCH4_linC_nonneg r K), dist_eq_norm]
    exact S7FCH4_lin_sub_le K F G
  exact this.continuous

/-! ### The `E_r`-valued maps `g` and `h` -/

/-- `g(F) = ∑_{k∈S} Φ_{K_k}(F) e_k`: the quadratic part of the finite-rank pair. -/
def S7FCH4_gq (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    (F : NegSobolev d r) : NegSobolev d r :=
  ∑ k ∈ S, (K k).quad F • S7FCH4_e r k

/-- `h(F) = ∑_{k∈S} lin_{K_k}(F) e_k`: the linear (diagonal) correction. -/
def S7FCH4_hq (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    (F : NegSobolev d r) : NegSobolev d r :=
  ∑ k ∈ S, S7FCH4_lin (K k) F • S7FCH4_e r k

def S7FCH4_Lg (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) : ℝ :=
  ∑ k ∈ S, S7FCH4_qC r (K k) * ‖S7FCH4_e r k‖

def S7FCH4_Lh (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) : ℝ :=
  ∑ k ∈ S, S7FCH4_linC r (K k) * ‖S7FCH4_e r k‖

theorem S7FCH4_Lg_nonneg (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) :
    0 ≤ S7FCH4_Lg r S K :=
  Finset.sum_nonneg fun k _ => mul_nonneg (S7FCH4_qC_nonneg _ _) (norm_nonneg _)

theorem S7FCH4_Lh_nonneg (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) :
    0 ≤ S7FCH4_Lh r S K :=
  Finset.sum_nonneg fun k _ => mul_nonneg (S7FCH4_linC_nonneg _ _) (norm_nonneg _)

theorem S7FCH4_gq_sub_le (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    (F G : NegSobolev d r) :
    ‖S7FCH4_gq r S K F - S7FCH4_gq r S K G‖ ≤ S7FCH4_Lg r S K * ((‖F‖ + ‖G‖) * ‖F - G‖) := by
  unfold S7FCH4_gq S7FCH4_Lg
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  calc |(K k).quad F - (K k).quad G| * ‖S7FCH4_e r k‖
      ≤ (S7FCH4_qC r (K k) * ((‖F‖ + ‖G‖) * ‖F - G‖)) * ‖S7FCH4_e r k‖ :=
        mul_le_mul_of_nonneg_right (S7FCH4_quad_sub_le (K k) F G) (norm_nonneg _)
    _ = _ := by ring

theorem S7FCH4_hq_sub_le (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    (F G : NegSobolev d r) :
    ‖S7FCH4_hq r S K F - S7FCH4_hq r S K G‖ ≤ S7FCH4_Lh r S K * ‖F - G‖ := by
  unfold S7FCH4_hq S7FCH4_Lh
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  calc |S7FCH4_lin (K k) F - S7FCH4_lin (K k) G| * ‖S7FCH4_e r k‖
      ≤ (S7FCH4_linC r (K k) * ‖F - G‖) * ‖S7FCH4_e r k‖ :=
        mul_le_mul_of_nonneg_right (S7FCH4_lin_sub_le (K k) F G) (norm_nonneg _)
    _ = _ := by ring

theorem S7FCH4_gq_zero (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) :
    S7FCH4_gq r S K 0 = 0 := by
  unfold S7FCH4_gq; simp [S7FCH4_quad_zero]

theorem S7FCH4_hq_zero (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) :
    S7FCH4_hq r S K 0 = 0 := by
  unfold S7FCH4_hq; simp [S7FCH4_lin_zero]

theorem S7FCH4_gq_continuous (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) :
    Continuous (S7FCH4_gq r S K) := by
  unfold S7FCH4_gq
  exact continuous_finsetSum _ fun k _ =>
    (HRS.MC.Sec7.S7FCW12.s7fcw12_quad_continuous (K k)).smul continuous_const

theorem S7FCH4_hq_continuous (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) :
    Continuous (S7FCH4_hq r S K) := by
  unfold S7FCH4_hq
  exact continuous_finsetSum _ fun k _ => (S7FCH4_lin_continuous (K k)).smul continuous_const

end HRS.MC.Sec7.S7FCH4
