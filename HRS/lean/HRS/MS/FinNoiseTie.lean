import HRS.MS.FinNoiseAux44

/-!
# S8.6 tie: `HRS.Whole.finite_noise`

`finite_noise_proof` has the statement of the frozen `HRS.Whole.finite_noise`
(`HRS/Whole/CriticalNoise.lean`; sorried there, so the warning of the `example` is expected).  It is
`s86_finite_noise_of_cost` (the features, `IsHSIntegrand`, `Cdet`, the adapted polar coupling and the reconstruction
estimate) applied to `s86_cost` (the covariance-root cost, proved through the chart system, the Fourier synthesis of the
localised features and Araki-Yamagami).
-/

namespace HRS.MS.FinNoise

theorem finite_noise_proof : type_of% @HRS.Whole.finite_noise :=
  s86_finite_noise_of_cost (fun {_} hd a β ha hβ m hm Hz hHz Cin => s86_cost hd a β ha hβ m hm Hz hHz Cin)

end HRS.MS.FinNoise

example := (@HRS.MS.FinNoise.finite_noise_proof : type_of% @HRS.Whole.finite_noise)
