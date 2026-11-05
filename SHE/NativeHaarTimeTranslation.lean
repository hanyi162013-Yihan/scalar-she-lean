module

public import SHE.NativeClippedHaarDirection
public import SHE.CommonHaarDefectTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SHE.NativeHaarTimeTranslation
open FiniteHaar StoppedFourier GaussianIncrement
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

theorem row {m W:ℝ}(hm:0<m)(f:EllipticField m W)
    (T q v:ℝ)(x:HeatCircle):
    NativeObservationCovariance.row hm f (T-v) (q-v) x=
      NativeObservationCovariance.row hm f T q x:=by
  unfold NativeObservationCovariance.row
  rw [sub_sub_sub_cancel_right]

theorem clipped {n:ℕ}{m W:ℝ}(hm:0<m)(f g:EllipticField m W)
    (σ target:Fin n→ℝ)(a:Fin n→AddCircle (1:ℝ))(q v Λ:ℝ)(l:HaarNode):
    NativeClippedHaarDirection.column hm f g (fun i=>σ i-v) (fun i=>target i-v) a (q-v) Λ l=
      NativeClippedHaarDirection.column hm f g σ target a q Λ l:=by
  apply PiLp.ext
  intro i
  change (1-Real.exp (-Λ*((σ i-v)-(q-v))))*
    (NativeObservationCovariance.row hm f (target i-v) (q-v) _ l-
      NativeObservationCovariance.row hm g (target i-v) (q-v) _ l)=_
  rw [sub_sub_sub_cancel_right,row,row]
  rfl

theorem current {n:ℕ}{m W:ℝ}(hm:0<m)(f:EllipticField m W)
    (target:Fin n→ℝ)(a:Fin n→HeatCircle)(q v:ℝ)(l:HaarNode):
    CommonHaarDefectTrace.direction (fun i=>NativeObservationCovariance.row hm f (target i-v) (q-v) (a i)) l=
      CommonHaarDefectTrace.direction (fun i=>NativeObservationCovariance.row hm f (target i) q (a i)) l:=by
  simp only [row]

end SHE.NativeHaarTimeTranslation
