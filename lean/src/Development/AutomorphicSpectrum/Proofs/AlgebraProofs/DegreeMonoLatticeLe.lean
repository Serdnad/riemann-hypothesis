import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.WeilBound.CoreStatements.HodgeTatePoints.DegLeOfEquiv

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem deg_le_deg_of_le : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L L' : C.I → AddSubgroup V), IsBun C L → IsBun C L' → (∀ i, L i ≤ L' i) → deg C L ≤ deg C L' :=
  @PositivityTheory.HtPt.Ch.deg_mono

end GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.degree_mono_lattice_le : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.Crv.deg_le_deg_of_le :=
  @_root_.GlobalTheory.CompanionTheory.Ar.Crv.deg_le_deg_of_le
