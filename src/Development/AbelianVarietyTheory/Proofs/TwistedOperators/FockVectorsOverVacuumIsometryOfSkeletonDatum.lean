module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VacuumFockVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockFromSquareIntegrability

@[expose] public section

open Formalism.BasicNotions

namespace GlobalTheory

theorem vacuumFock_all_records : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := GlobalTheory.VacuumFockLaws.vacuumFock_onObjects

end GlobalTheory
