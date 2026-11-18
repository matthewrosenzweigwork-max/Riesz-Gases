import HRS.Commutator.Whole.LOWVAux2

/-!
# CMX-LOWV auxiliary 3: Fourier support of the commutator kernel `K(x,y) = (V x - V y)·F(x-y)`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem lowv_int_schwartz {k : Euc d → ℝ} (hk : Continuous k) (C : ℝ)
    (hC : ∀ x, |k x| ≤ C * (1 + ‖x‖)) (ψ : SchwartzMap (Euc d) ℂ) :
    Integrable (fun x => ((k x : ℝ) : ℂ) * ψ x) := by
  have h1 := cmxFB_integrable_pow_mul ψ 1
  have h0 := (ψ.integrable (μ := (volume : Measure (Euc d)))).norm
  refine ((h1.add h0).const_mul (|C| + 1)).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (Complex.continuous_ofReal.comp hk |>.mul ψ.continuous).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 : |k x| ≤ (|C| + 1) * (1 + ‖x‖) := by
      calc |k x| ≤ C * (1 + ‖x‖) := hC x
        _ ≤ |C| * (1 + ‖x‖) := by gcongr; exact le_abs_self _
        _ ≤ (|C| + 1) * (1 + ‖x‖) := by gcongr; linarith
    calc |k x| * ‖ψ x‖ ≤ (|C| + 1) * (1 + ‖x‖) * ‖ψ x‖ := by gcongr
      _ = (|C| + 1) * ((1 + ‖x‖) ^ 1 * ‖ψ x‖ + ‖ψ x‖) - (|C| + 1) * ‖ψ x‖ := by ring
      _ ≤ (|C| + 1) * ((1 + ‖x‖) ^ 1 * ‖ψ x‖ + ‖ψ x‖) := by
          have : 0 ≤ (|C| + 1) * ‖ψ x‖ := by positivity
          linarith

theorem lowv_fs_add {R : ℝ} {u w : Euc d → ℝ} (hu : FourierSuppIn R u) (hw : FourierSuppIn R w)
    (hui : ∀ φ : SchwartzMap (Euc d) ℂ, Integrable (fun x => ((u x : ℝ) : ℂ) * φ x))
    (hwi : ∀ φ : SchwartzMap (Euc d) ℂ, Integrable (fun x => ((w x : ℝ) : ℂ) * φ x)) :
    FourierSuppIn R (fun x => u x + w x) := by
  intro φ hφ
  have e : ∀ x, ((u x + w x : ℝ) : ℂ) * φ x = ((u x : ℝ) : ℂ) * φ x + ((w x : ℝ) : ℂ) * φ x :=
    fun x => by push_cast; ring
  simp_rw [e]
  rw [integral_add (hui φ) (hwi φ), hu φ hφ, hw φ hφ, add_zero]

theorem lowv_fs_sum {ι : Type*} (S : Finset ι) {R : ℝ} (u : ι → Euc d → ℝ)
    (h : ∀ i ∈ S, FourierSuppIn R (u i))
    (hi : ∀ i ∈ S, ∀ φ : SchwartzMap (Euc d) ℂ, Integrable (fun x => ((u i x : ℝ) : ℂ) * φ x)) :
    FourierSuppIn R (fun x => ∑ i ∈ S, u i x) := by
  intro φ hφ
  have e : ∀ x, ((∑ i ∈ S, u i x : ℝ) : ℂ) * φ x = ∑ i ∈ S, ((u i x : ℝ) : ℂ) * φ x :=
    fun x => by push_cast; rw [Finset.sum_mul]
  simp_rw [e]
  rw [integral_finset_sum S (fun i hi' => hi i hi' φ)]
  exact Finset.sum_eq_zero fun i hi' => h i hi' φ hφ

/-- The commutator kernel, without the diagonal clause. -/
def lowv_K (F V : Euc d → Euc d) (x y : Euc d) : ℝ := inner ℝ (V x - V y) (F (x - y))

theorem lowv_commKer_eq (F V : Euc d → Euc d) (x y : Euc d) :
    commKer F V x y = lowv_K F V x y := by
  unfold commKer lowv_K
  split_ifs with h
  · subst h; simp
  · rfl

theorem lowv_K_symm {F : Euc d → Euc d} (hodd : ∀ x, F (-x) = -F x) (V : Euc d → Euc d)
    (x y : Euc d) : lowv_K F V y x = lowv_K F V x y := by
  unfold lowv_K
  have : y - x = -(x - y) := by abel
  rw [this, hodd, ← neg_sub (V x) (V y), inner_neg_neg]

theorem lowv_K_bound {F V : Euc d → Euc d} {B Lv : ℝ} (hB : ∀ x, ‖F x‖ ≤ B)
    (hV : ∀ x y, ‖V x - V y‖ ≤ Lv * ‖x - y‖) (hLv : 0 ≤ Lv) (x y : Euc d) :
    |lowv_K F V x y| ≤ Lv * B * (‖x‖ + ‖y‖) := by
  unfold lowv_K
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  calc |inner ℝ (V x - V y) (F (x - y))| ≤ ‖V x - V y‖ * ‖F (x - y)‖ := abs_real_inner_le_norm _ _
    _ ≤ (Lv * ‖x - y‖) * B := by
        gcongr
        · exact hV x y
        · exact hB _
    _ ≤ (Lv * (‖x‖ + ‖y‖)) * B := by gcongr; exact norm_sub_le _ _
    _ = Lv * B * (‖x‖ + ‖y‖) := by ring

theorem lowv_K_continuous {F V : Euc d → Euc d} (hF : Continuous F) (hV : Continuous V) :
    Continuous fun p : Euc d × Euc d => lowv_K F V p.1 p.2 := by
  unfold lowv_K
  fun_prop


theorem lowv_K_fsupp {F V : Euc d → Euc d}
    (hVi : ∀ i, FourierSuppIn 2 (fun x => V x i)) (hFi : ∀ i, FourierSuppIn 2 (fun x => F x i))
    (hFt : ∀ i, Function.HasTemperateGrowth (fun x => F x i))
    (hVc : Continuous V) (hFc : Continuous F) {LV B : ℝ} (hVg : ∀ x, ‖V x‖ ≤ LV * (1 + ‖x‖))
    (hB : ∀ x, ‖F x‖ ≤ B) (y : Euc d) :
    FourierSuppIn 4 (fun x => lowv_K F V x y) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have e : ∀ x, lowv_K F V x y =
      ∑ i, (V x i * F (x - y) i + (-(V y i)) * F (x - y) i) := by
    intro x
    unfold lowv_K
    simp only [PiLp.inner_apply, PiLp.sub_apply, RCLike.inner_apply, conj_trivial]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hVic : ∀ i, Continuous fun x => V x i := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hVc
  have hFic : ∀ i, Continuous fun x => F x i := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hFc
  have hcomp : ∀ (G : Euc d → Euc d) (i : Fin d) (x : Euc d), |G x i| ≤ ‖G x‖ := fun G i x => by
    simpa using PiLp.norm_apply_le (G x) i
  have hLV : 0 ≤ LV := by
    have := hVg 0
    simp at this
    exact (norm_nonneg _).trans this
  have h4 : (2 : ℝ) + 2 = 4 := by norm_num
  have hsum : FourierSuppIn (2 + 2) (fun x => ∑ i, (V x i * F (x - y) i + (-(V y i)) * F (x - y) i)) := by
    refine lowv_fs_sum Finset.univ _ (fun i _ => ?_) (fun i _ φ => ?_)
    · have hg : Function.HasTemperateGrowth (fun x : Euc d => F (x - y) i) :=
        (hFt i).comp (by fun_prop : Function.HasTemperateGrowth fun x : Euc d => x - y)
      have hA := lowv_prod_fsupp (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) ≤ 2) hg
        (hVi i) (lowv_fs_translate (hFi i) y)
      have hBB := lowv_fs_mono (lowv_fs_smul (lowv_fs_translate (hFi i) y) (-(V y i)))
        (by norm_num : (2:ℝ) ≤ 2 + 2)
      refine lowv_fs_add hA hBB (fun φ => ?_) (fun φ => ?_)
      · refine lowv_int_schwartz (C := LV * B) ?_ ?_ φ
        · exact (hVic i).mul (hFic i |>.comp (continuous_id.sub continuous_const))
        · intro x
          rw [abs_mul]
          calc |V x i| * |F (x - y) i| ≤ ‖V x‖ * B := by
                gcongr
                · exact hcomp V i x
                · exact (hcomp F i _).trans (hB _)
            _ ≤ (LV * (1 + ‖x‖)) * B := by gcongr; exact hVg x
            _ = LV * B * (1 + ‖x‖) := by ring
      · refine lowv_int_schwartz (C := |V y i| * B) ?_ ?_ φ
        · exact continuous_const.mul (hFic i |>.comp (continuous_id.sub continuous_const))
        · intro x
          rw [abs_mul, abs_neg]
          calc |V y i| * |F (x - y) i| ≤ |V y i| * B := by
                gcongr; exact (hcomp F i _).trans (hB _)
            _ ≤ |V y i| * B * (1 + ‖x‖) := by
                have : 0 ≤ |V y i| * B := by positivity
                nlinarith [norm_nonneg x]
    · have hg : Function.HasTemperateGrowth (fun x : Euc d => F (x - y) i) :=
        (hFt i).comp (by fun_prop : Function.HasTemperateGrowth fun x : Euc d => x - y)
      refine lowv_int_schwartz (C := LV * B + |V y i| * B) ?_ ?_ φ
      · exact ((hVic i).mul (hFic i |>.comp (continuous_id.sub continuous_const))).add
          (continuous_const.mul (hFic i |>.comp (continuous_id.sub continuous_const)))
      · intro x
        have h1 : |V x i| * |F (x - y) i| ≤ LV * B * (1 + ‖x‖) := by
          calc |V x i| * |F (x - y) i| ≤ ‖V x‖ * B := by
                gcongr
                · exact hcomp V i x
                · exact (hcomp F i _).trans (hB _)
            _ ≤ (LV * (1 + ‖x‖)) * B := by gcongr; exact hVg x
            _ = LV * B * (1 + ‖x‖) := by ring
        have h2 : |V y i| * |F (x - y) i| ≤ |V y i| * B * (1 + ‖x‖) := by
          calc |V y i| * |F (x - y) i| ≤ |V y i| * B := by
                gcongr; exact (hcomp F i _).trans (hB _)
            _ ≤ |V y i| * B * (1 + ‖x‖) := by
                have : 0 ≤ |V y i| * B := by positivity
                nlinarith [norm_nonneg x]
        calc |V x i * F (x - y) i + (-(V y i)) * F (x - y) i|
            ≤ |V x i * F (x - y) i| + |(-(V y i)) * F (x - y) i| := abs_add_le _ _
          _ = |V x i| * |F (x - y) i| + |V y i| * |F (x - y) i| := by
              rw [abs_mul, abs_mul, abs_neg]
          _ ≤ (LV * B + |V y i| * B) * (1 + ‖x‖) := by linarith
  rw [h4] at hsum
  intro φ hφ
  have := hsum φ hφ
  simp_rw [e]
  exact this

end HRS.Commutator.Whole
