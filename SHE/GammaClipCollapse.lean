module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
@[expose] public section
set_option autoImplicit false
namespace SHE.GammaClipCollapse
/-- Structural coefficients inside a clipped energy can be absorbed
without moving the clipping ahead of the actual energy average. -/
theorem clip {K x:ℝ} (hx:0≤x):min 1 (K*x)≤max 1 K*min 1 x:=by
  rcases le_total x 1 with h|h
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx)
  · rw [min_eq_left h,mul_one]
    exact (min_le_left _ _).trans (le_max_left _ _)

/-- The six proved slot caps collapse to one structural constant.
All variables here are numerical energies, not operator-norm inputs. -/
theorem sum {Cs Cl Cg K0 K1 X Y L e:ℝ}
    (hCs:0≤Cs) (hCl:0≤Cl) (hCg:0≤Cg)
    (hX:0≤X) (hY:0≤Y) (hL:0≤L) (he:0≤e):
    6*(Cs*X+Cl*Y*L+Cg*Y*(min 1 (K0*e)+min 1 (K1*e)))≤
      (6*(Cs+Cl+Cg*(max 1 K0+max 1 K1)))*(X+Y*(L+min 1 e)):=by
  let K:=max 1 K0+max 1 K1
  have hK:0≤K:=add_nonneg (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans (le_max_left _ _))
  have hc:0≤min 1 e:=le_min zero_le_one he
  have hclip:min 1 (K0*e)+min 1 (K1*e)≤K*min 1 e:=by
    simpa only [K,add_mul] using add_le_add (clip (K:=K0) he) (clip (K:=K1) he)
  have hfirst:6*(Cs*X+Cl*Y*L+Cg*Y*(min 1 (K0*e)+min 1 (K1*e)))≤
      6*(Cs*X+Cl*Y*L+Cg*Y*(K*min 1 e)):=by
    gcongr
  have hrest:0≤(Cl+Cg*K)*X+Cs*Y*L+Cs*Y*min 1 e+Cl*Y*min 1 e+Cg*K*Y*L:=by positivity
  have hid:(Cs+Cl+Cg*K)*(X+Y*(L+min 1 e))-
      (Cs*X+Cl*Y*L+Cg*Y*(K*min 1 e))=
      (Cl+Cg*K)*X+Cs*Y*L+Cs*Y*min 1 e+Cl*Y*min 1 e+Cg*K*Y*L:=by ring
  have hsecond:Cs*X+Cl*Y*L+Cg*Y*(K*min 1 e)≤(Cs+Cl+Cg*K)*(X+Y*(L+min 1 e)):=by linarith
  exact hfirst.trans (by nlinarith)
end SHE.GammaClipCollapse
