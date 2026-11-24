module

import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.HfinExistsMat
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.Style
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct Topology

namespace GlobalTheory.RationalDiscrete

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nhds_zero_inclR :
    ∃ U ∈ 𝓝 (0 : AF F ⊗[F] E), ∀ x : E, inclR (F := F) (AF F) x ∈ U → x = 0 := by
  obtain ⟨U, hU, h⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isModTop (F := F) (E := E)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have hc : ∀ k, Continuous (B.coord k) := fun k => IsModuleTopology.continuous_of_linearMap _
  refine ⟨⋂ k, B.coord k ⁻¹' U, Filter.iInter_mem.2 fun k => ?_, fun x hx => ?_⟩
  · exact (hc k).continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU)
  · refine b.ext_elem fun k => ?_
    rw [map_zero, Finsupp.zero_apply]
    refine h _ ?_
    have hk : B.repr ((1 : AF F) ⊗ₜ[F] x) k ∈ U := Set.mem_iInter.1 hx k
    rw [Algebra.TensorProduct.basis_repr_tmul] at hk
    simpa using hk

theorem discreteTopology_HFinIn (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    DiscreteTopology (HFinIn (AF F) σ J) := by
  first | exact _root_.Formalism.IndefR.Eqv.G5.hfin_disc | exact @_root_.Formalism.IndefR.Eqv.G5.hfin_disc | apply _root_.Formalism.IndefR.Eqv.G5.hfin_disc <;> assumption

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem discreteTopology_GQ : ∀ (D : D7) (V : HSp D), DiscreteTopology (GQ V) :=
  fun D V => discreteTopology_HFinIn D.sp.cm.sig V.gram

end GlobalTheory.RationalDiscrete
