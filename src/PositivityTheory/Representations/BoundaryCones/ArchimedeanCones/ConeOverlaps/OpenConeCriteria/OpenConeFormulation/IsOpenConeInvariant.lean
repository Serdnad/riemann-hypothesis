module


import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeIsOpenStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer
import Mathlib.Analysis.Matrix.Hermitian
@[expose] public section

noncomputable section

open Matrix Finset Filter Topology
open scoped ContDiff ComplexOrder

namespace PositivityTheory.KcHalf2₂

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat hb)

theorem isOpen_cone_of_hbFacts {n : ℕ} (hH : HbFacts) : IsOpen (cone n) := by
  apply @_root_.GlobalTheory.CompanionTheory.ConeHaar.isOpen_cone <;> assumption

end PositivityTheory.KcHalf2₂
