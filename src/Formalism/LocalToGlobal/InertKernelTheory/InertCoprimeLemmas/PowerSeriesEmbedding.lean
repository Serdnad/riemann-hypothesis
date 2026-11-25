module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceExtendsToIso
public import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
public import Mathlib.RingTheory.Algebraic.Cardinality
public import ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlaceB

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions

theorem lattice_extension : LamExt := by
  apply _root_.GlobalTheory.ThLoc.place_extends_to_iso <;> assumption

theorem lattice_embedding : LamCIota := by
  intro p _ lam ι h
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · unfold Formalism.MainNotions.TaylorLogMetric.lamC
    rw [dite_eq_left hx]
    exact (h ⟨x, hx⟩).symm
  · unfold Formalism.MainNotions.TaylorLogMetric.lamC
    rw [dite_eq_right hx]

theorem power_series_embedding : PSerIota := by
  intro D N N' p _ lam ι h G hG
  ext α
  rw [MvPowerSeries.coeff_map]
  change Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.taylor D G α) = ι (Formalism.MainNotions.TaylorLogMetric.taylor D G α)
  exact (lattice_embedding p lam ι h).1 _ (hG α)

end Formalism.L2.KerInert
