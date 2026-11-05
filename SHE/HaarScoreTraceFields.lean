module

public import SHE.FiniteHaarScoreTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

namespace SHE.HaarScoreTraceFields
open MeasureTheory FiniteHaar GaussianIncrement MeasurableGaussianScores

/-- Literal full Haar score trace of a measurable covariance and
measurable full directions, including singular covariance matrices. -/
theorem measurable {X:Type*}[MeasurableSpace X]{n:ℕ}
    (A:X→Matrix (Fin n) (Fin n) ℝ)(D:X→HaarNode→State n)
    (hA:Measurable A)(hD:∀l,Measurable (fun x=>D x l)):
    Measurable (fun x=>∑'l:HaarNode,scoreVariance (A x) (D x l)):=by
  have hs (l:HaarNode):Measurable (fun x=>scoreVariance (A x) (D x l)):=by
    have hm:=scoreVariance_measurable.comp (hA.prodMk (hD l))
    exact hm
  exact Measurable.tsum hs

end SHE.HaarScoreTraceFields
