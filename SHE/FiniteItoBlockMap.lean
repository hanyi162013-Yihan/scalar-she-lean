module

public import SHE.ObservationBlockMaps
public import SHE.StandardFiniteIto
public import SHE.StoppedInputAlgebra
public import SHE.TwoChannelItoRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.FiniteItoBlockMap
open MeasureTheory GaussianIncrement PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {n : ℕ}

def blockMap (c : Fin n→ℝ) : State (n+n)→L[ℝ]State n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => PiLp.proj 2 (fun _ : Fin (n+n) => ℝ) (Fin.castAdd n i)+
      c i • PiLp.proj 2 (fun _ : Fin (n+n) => ℝ) (Fin.natAdd n i)))

@[simp] theorem blockMap_apply (c : Fin n→ℝ) (z : State (n+n)) (i : Fin n) :
    blockMap c z i=z (Fin.castAdd n i)+c i*z (Fin.natAdd n i) := rfl

variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)

def rows (c : Fin n→ℝ) (R : Fin (n+n)→Process (E := C) 𝓕 μ H) :
    Fin n→Process (E := C) 𝓕 μ H := fun i => R (Fin.castAdd n i)+c i • R (Fin.natAdd n i)

/-- A constant block-diagonal observation map commutes with the genuine
finite vector Itô integral, by its actual scalar linearity and stops. -/
theorem vectorIntegral_map (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ H)
    (c : Fin n→ℝ) (z : State (n+n)) (R : Fin (n+n)→Process (E := C) 𝓕 μ H) (t : ℝ≥0) :
    (fun ω => blockMap c (StandardFiniteIto.vectorIntegral 𝓕 μ H J z R t ω))=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J (blockMap c z) (rows 𝓕 μ H c R) t := by
  have he (i : Fin n) : J.integral (stop 𝓕 μ H (t:ℝ) (rows 𝓕 μ H c R i))=
      J.integral (stop 𝓕 μ H (t:ℝ) (R (Fin.castAdd n i)))+
        c i • J.integral (stop 𝓕 μ H (t:ℝ) (R (Fin.natAdd n i))) := by
    rw [rows,TwoChannelItoRows.stop_add,StoppedInputAlgebra.stop_smul,map_add,map_smul]
  have ha (i : Fin n) := Lp.coeFn_add
    (J.integral (stop 𝓕 μ H (t:ℝ) (R (Fin.castAdd n i))))
    (c i • J.integral (stop 𝓕 μ H (t:ℝ) (R (Fin.natAdd n i))))
  have hs (i : Fin n) := Lp.coeFn_smul (c i)
    (J.integral (stop 𝓕 μ H (t:ℝ) (R (Fin.natAdd n i))))
  filter_upwards [ae_all_iff.mpr ha,ae_all_iff.mpr hs] with ω ha hs
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at ha hs
  apply PiLp.ext
  intro i
  simp only [blockMap_apply,StandardFiniteIto.vectorIntegral,WithLp.ofLp_toLp]
  rw [he,ha i,hs i]
  change z (Fin.castAdd n i)+_+c i*(z (Fin.natAdd n i)+_)=z (Fin.castAdd n i)+c i*z (Fin.natAdd n i)+(_+c i*_)
  ring

end SHE.FiniteItoBlockMap
