module
public import SHE.PredictableL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.NativeFinitePrefixVersionTransfer
open MeasureTheory PredictableL2
open scoped NNReal
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable (μ:Measure Ω)[SFinite μ](H:ℝ≥0)

/-- Equal sectional versions of an arbitrary raw target are equal in
the native product measure. Only the two genuine versions are Borel;
the raw stochastic target need not be jointly measurable. -/
theorem of_sections(F G Raw:ℕ→ℝ≥0×Ω→E)
    (hF:∀j,Measurable (F j))(hG:∀j,Measurable (G j))
    (hf:∀j,∀ᵐt∂timeMeasure H,(fun ω=>F j (t,ω))=ᵐ[μ] (fun ω=>Raw j (t,ω)))
    (hg:∀j,∀ᵐt∂timeMeasure H,(fun ω=>G j (t,ω))=ᵐ[μ] (fun ω=>Raw j (t,ω))):
    ∀j,F j=ᵐ[energyMeasure μ H] G j:=by
  intro j
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (hF j) (hG j))).mpr
  filter_upwards [hf j,hg j] with t ht hu
  exact ht.trans hu.symm

/-- Genuine finite-prefix moments and their RMS bounds transfer
between actual Borel versions before taking any upper-cutoff limit. -/
theorem prefixes(F G:ℕ→ℝ≥0×Ω→E)(he:∀j,F j=ᵐ[energyMeasure μ H] G j)
    (cap:ℕ→ℝ)
    (hG:∀L:ℕ,Integrable (fun z=>‖∑j∈Finset.range L,G j z‖^2) (energyMeasure μ H) ∧
      Real.sqrt (∫z,‖∑j∈Finset.range L,G j z‖^2 ∂energyMeasure μ H)≤cap L):
    ∀L:ℕ,Integrable (fun z=>‖∑j∈Finset.range L,F j z‖^2) (energyMeasure μ H) ∧
      Real.sqrt (∫z,‖∑j∈Finset.range L,F j z‖^2 ∂energyMeasure μ H)≤cap L:=by
  have hall:∀ᵐz∂energyMeasure μ H,∀j,F j z=G j z:=by
    rw [ae_all_iff]
    exact he
  intro L
  have hs:(fun z=>‖∑j∈Finset.range L,F j z‖^2)=ᵐ[energyMeasure μ H]
      (fun z=>‖∑j∈Finset.range L,G j z‖^2):=hall.mono (fun z hz=>
        congrArg (fun e:E=>‖e‖^2) (Finset.sum_congr rfl (fun j _=>hz j)))
  refine ⟨(hG L).1.congr hs.symm,?_⟩
  rw [integral_congr_ae hs]
  exact (hG L).2

end SHE.NativeFinitePrefixVersionTransfer
