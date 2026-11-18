import HRS.Commutator.Whole.PRODAux5

/-!
# CMX-PROD helper file 6: Schwartz approximation of `(f, ⟨∇⟩^α f)`

If `f, W ∈ L^p` and `W = ⟨∇⟩^α f` in the sense of distributions, there are Schwartz functions `g_n`
with `g_n → f` and `⟨∇⟩^α g_n → W` in `L^p`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.PROD

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

lemma prod_err_bound {p : ℝ} (hp : 1 < p) (Kn s : SchwartzMap (Euc d) ℂ) {h T : Euc d → ℂ}
    (hh : MemLp h (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => prod_conv Kn s x - T x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (∫ t, ‖Kn t‖) * eLpNorm (fun x => s x - h x) (ENNReal.ofReal p) volume +
        eLpNorm (fun x => prod_conv Kn h x - T x) (ENNReal.ofReal p) volume := by
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hs : MemLp (⇑s) (ENNReal.ofReal p) volume := s.memLp _ _
  have hsub := prod_conv_sub Kn hp hs hh
  have e : (fun x => prod_conv Kn s x - T x) =
      prod_conv Kn (⇑s - h) + (fun x => prod_conv Kn h x - T x) := by
    funext x
    rw [Pi.add_apply, hsub]
    ring
  rw [e]
  refine (eLpNorm_add_le hP1).trans ?_
  gcongr
  exact prod_eLpNorm_conv_le hp Kn.integrable (s.continuous.aestronglyMeasurable.sub hh.aestronglyMeasurable)

theorem prod_approx {p : ℝ} (hp : 1 < p) {α : ℝ} {f W : Euc d → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) volume) (hW : MemLp W (ENNReal.ofReal p) volume)
    (hrep : ProdBes α f W) :
    ∃ g : ℕ → SchwartzMap (Euc d) ℂ,
      Tendsto (fun n => eLpNorm (fun x => g n x - f x) (ENNReal.ofReal p) volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun x => besselS α (g n) x - W x) (ENNReal.ofReal p) volume)
        atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  set B : ℕ → ℝ := fun n => ∫ t, ‖prod_J α (prod_ker d n) t‖ with hB
  have hB0 : ∀ n, 0 ≤ B n := fun n => integral_nonneg fun t => norm_nonneg _
  set e : ℕ → ℝ := fun n => 1 / (((n : ℝ) + 1) * (B n + 1)) with he
  have he0 : ∀ n, 0 < e n := fun n => by
    have := hB0 n
    simp only [he]; positivity
  choose s hs using fun n : ℕ => prod_schwartz_dense hp hf (he0 n)
  have hKe : ∀ n, ENNReal.ofReal (∫ t, ‖prod_ker d n t‖) * ENNReal.ofReal (e n) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n => by
    rw [prod_ker_norm_integral, ENNReal.ofReal_one, one_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hB0 n
    simp only [he]
    gcongr
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n + 1) this]
  have hMe : ∀ n, ENNReal.ofReal (B n) * ENNReal.ofReal (e n) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n => by
    rw [← ENNReal.ofReal_mul (hB0 n)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hB0 n
    simp only [he]
    rw [show B n * (1 / (((n : ℝ) + 1) * (B n + 1))) = (1 / ((n : ℝ) + 1)) * (B n / (B n + 1)) by
      field_simp]
    have h1 : B n / (B n + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h2 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    nlinarith
  have hsmall : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  refine ⟨fun n => prod_sconv (prod_ker d n) (s n), ?_, ?_⟩
  · have hδ := prod_ker_conv_Lp hp hf
    have hlim := hsmall.add hδ
    rw [add_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      hlim (fun n => bot_le) (fun n => ?_)
    have := prod_err_bound hp (prod_ker d n) (s n) (h := f) (T := f) hf
    refine (le_of_eq_of_le ?_ this).trans ?_
    · congr 1
      funext x
      rw [prod_sconv_apply]
    · have h3 : ENNReal.ofReal (∫ t, ‖prod_ker d n t‖) *
          eLpNorm (fun x => s n x - f x) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
        (mul_le_mul_right (hs n) _).trans (hKe n)
      exact add_le_add h3 le_rfl
  · have hδ := prod_ker_conv_Lp hp hW
    have hlim := hsmall.add hδ
    rw [add_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      hlim (fun n => bot_le) (fun n => ?_)
    have := prod_err_bound hp (prod_J α (prod_ker d n)) (s n) (h := f) (T := W) hf
    have h1 : eLpNorm (fun x => prod_conv (prod_J α (prod_ker d n)) f x - W x)
        (ENNReal.ofReal p) volume =
        eLpNorm (fun x => prod_conv (prod_ker d n) W x - W x) (ENNReal.ofReal p) volume := by
      refine eLpNorm_congr_ae ?_
      have h2 := prod_cor_identity hp hf hW hrep (prod_ker d n)
      filter_upwards [h2] with x hx
      rw [← prod_cor_eq_conv (K := prod_J α (prod_ker d n)) (prod_J_even α (prod_ker_neg n)),
        ← prod_cor_eq_conv (K := prod_ker d n) (prod_ker_neg n), hx]
    refine (le_of_eq_of_le ?_ this).trans ?_
    · congr 1
      funext x
      rw [prod_besselS_eq, prod_J_sconv, prod_sconv_apply]
    · rw [h1]
      have h3 : ENNReal.ofReal (∫ t, ‖prod_J α (prod_ker d n) t‖) *
          eLpNorm (fun x => s n x - f x) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
        (mul_le_mul_right (hs n) _).trans (hMe n)
      exact add_le_add h3 le_rfl

end HRS.Commutator.Whole.PROD
