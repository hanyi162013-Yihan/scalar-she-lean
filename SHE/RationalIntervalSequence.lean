module
public import SHE.CanonicalConditionalRationalDriver
public import Mathlib.Topology.Order.IsLUB
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
namespace SHE.RationalIntervalSequence
open Set Filter
open scoped Topology NNReal

/-- Every actual bounded clock has a rational approximation staying
inside the SAME interval, including zero and an irrational endpoint. -/
theorem exists_sequence(h:ℝ≥0) (s:Icc (0:ℝ) (h:ℝ)):
    ∃q:ℕ→CanonicalConditionalRationalDriver.Times h,
      Tendsto (fun n=>CanonicalConditionalRationalDriver.time (q n)) atTop (𝓝 s):=by
  by_cases hs:s.val=0
  · let q:CanonicalConditionalRationalDriver.Times h:=⟨0,le_rfl,by exact_mod_cast (show (0:ℝ≥0)≤h from zero_le)⟩
    refine ⟨fun _=>q,?_⟩
    have he:CanonicalConditionalRationalDriver.time q=s:=by
      apply Subtype.ext
      simpa only[CanonicalConditionalRationalDriver.time,q,Rat.cast_zero] using hs.symm

    simpa only[he] using tendsto_const_nhds
  · have hs':(0:ℝ)<s.val:=lt_of_le_of_ne s.property.1 (Ne.symm hs)
    obtain ⟨q,hqmono,hqI,hqt⟩:=Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt Rat.cast_strictMono.monotone hs'
    let Q:ℕ→CanonicalConditionalRationalDriver.Times h:=fun n=>
      ⟨q n,by exact_mod_cast (hqI n).1.le,((hqI n).2.le.trans s.property.2)⟩
    refine ⟨Q,?_⟩
    exact tendsto_subtype_rng.mpr hqt
end SHE.RationalIntervalSequence
