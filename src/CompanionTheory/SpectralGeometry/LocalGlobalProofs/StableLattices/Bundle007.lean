module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AnisotropicOfHenselAndSandwich
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle003
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfFrameWittTorus
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistenceOfSandwichStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FrameOfAnisotropicPlaneSplitting
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneOfHenselAndPairing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SplittingOfSandwichAndPairing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.anisotropic_of_hensel_and_sandwich : StHensel → StSandwich → StAniso := by
  first | exact @GlobalTheory.CompanionTheory.HermAniso.aniso | exact GlobalTheory.CompanionTheory.HermAniso.aniso | (intros; apply GlobalTheory.CompanionTheory.HermAniso.aniso <;> assumption)
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.DeltaStatement : StDelta := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stDelta | exact GlobalTheory.CompanionTheory.RgFl.stDelta | (intros; apply GlobalTheory.CompanionTheory.RgFl.stDelta <;> assumption)
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.HenselStatement : StHensel := by
  first | exact @GlobalTheory.CompanionTheory.LocalHensel.stHensel_holds | exact GlobalTheory.CompanionTheory.LocalHensel.stHensel_holds | (intros; apply GlobalTheory.CompanionTheory.LocalHensel.stHensel_holds <;> assumption)
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.hermitian_adjoint_exists : ∀ {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V] [FiniteDimensional L V] (s : L →+* L), IsInv s → ∀ h : V → V → L, IsHerm s h → ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y) := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.exists_adjoint_herm | exact GlobalTheory.CompanionTheory.Iwahori.exists_adjoint_herm | (intros; apply GlobalTheory.CompanionTheory.Iwahori.exists_adjoint_herm <;> assumption)
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.SandwichStatement : StSandwich := by
  first | exact @GlobalTheory.CompanionTheory.Lattice.stSandwich | exact GlobalTheory.CompanionTheory.Lattice.stSandwich | (intros; apply GlobalTheory.CompanionTheory.Lattice.stSandwich <;> assumption)
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.pairing_of_sandwich_statement : StSandwich → StPairing := by
  first | exact @GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich | exact GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich | (intros; apply GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich <;> assumption)
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.TorusStatement : StTor := by
  first | exact @GlobalTheory.CompanionTheory.FrameTorus.stTor | exact GlobalTheory.CompanionTheory.FrameTorus.stTor | (intros; apply GlobalTheory.CompanionTheory.FrameTorus.stTor <;> assumption)
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.decomposition_of_frame_witt_torus : StFrame → StWitt → StTor → StDecomp := by
  first | exact @GlobalTheory.CompanionTheory.FlDecomp.stDecomp_of_frame_witt_tor | exact GlobalTheory.CompanionTheory.FlDecomp.stDecomp_of_frame_witt_tor | (intros; apply GlobalTheory.CompanionTheory.FlDecomp.stDecomp_of_frame_witt_tor <;> assumption)
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.existence_of_sandwich_statement : StSandwich → StExists := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich | exact GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich | (intros; apply GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich <;> assumption)
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.frame_of_anisotropic_plane_splitting : StAniso → StPlane → StSplit → StFrame := by
  first | exact @GlobalTheory.CompanionTheory.HermFrame.stFrame_of | exact GlobalTheory.CompanionTheory.HermFrame.stFrame_of | (intros; apply GlobalTheory.CompanionTheory.HermFrame.stFrame_of <;> assumption)
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.plane_of_hensel_and_pairing : StHensel → StPairing → StPlane := by
  first | exact @GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing | exact GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing | (intros; apply GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing <;> assumption)
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.splitting_of_sandwich_and_pairing : StSandwich → StPairing → StSplit := by
  first | exact @GlobalTheory.CompanionTheory.RgSplit.stSplit | exact GlobalTheory.CompanionTheory.RgSplit.stSplit | (intros; apply GlobalTheory.CompanionTheory.RgSplit.stSplit <;> assumption)
end
