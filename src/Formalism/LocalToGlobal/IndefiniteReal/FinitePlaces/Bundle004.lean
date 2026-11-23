module

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetNormOne
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LinIndepOneDelta
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.Bundle001
import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction NumberField IsDedekindDomain
  Topology Filter
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin.U1

section Places

variable {F : Type} [Field F] [NumberField F]

theorem exists_finset_norm_one (x : F) (hx : x ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ‖algebraMap F (v.adicCompletion F) x‖ = 1 := by
  apply GlobalTheory.HeckeSplitAll.Approx.exists_finset_norm_one <;> assumption

end Places

section Main

variable {D : D7} (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)



end Main

variable {D : D7}

end Formalism.IndefR.Fin.U1

namespace Formalism.IndefR.Fin

end Formalism.IndefR.Fin

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin.U1

variable {D : D7}

theorem sig_sig (D : D7) (e : D.host.E) : D.sp.cm.sig (D.sp.cm.sig e) = e := star_star e

theorem sig_fix (D : D7) (e : D.host.E) : D.sp.cm.sig e = e ↔ e ∈ (algebraMap D.host.F D.host.E).range :=
  D.sp.cm.fixed e

theorem exists_delta_D (D : D7) : ∃ δ : D.host.E, D.sp.cm.sig δ = -δ ∧ δ ≠ 0 :=
  exists_delta D.sp.cm.sig (sig_sig D) (sig_fix D) D.sp.cm.deg2

theorem exists_Delta (D : D7) (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) :
    ∃ Δ : D.host.F, algebraMap D.host.F D.host.E Δ = δ * δ := by
  have : D.sp.cm.sig (δ * δ) = δ * δ := by rw [map_mul, hδ, neg_mul_neg]
  obtain ⟨Δ, hΔ⟩ := (sig_fix D _).1 this
  exact ⟨Δ, hΔ⟩

theorem isModTop (D : D7) : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩

section Pts

variable (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)

abbrev pt (a b : AF D.host.F) : AE D := mkE (F := D.host.F) δ (AF D.host.F) a b

abbrev DA (Δ : D.host.F) : AF D.host.F := algebraMap D.host.F (AF D.host.F) Δ


include hΔ in
theorem pt_mul (a b a' b' : AF D.host.F) :
    pt δ a b * pt δ a' b' = pt δ (a * a' + DA Δ * (b * b')) (a * b' + b * a') :=
  mkE_mul δ Δ hΔ (AF D.host.F) a b a' b'


theorem pt_one : pt (D := D) δ 1 0 = 1 := mkE_one δ (AF D.host.F)

abbrev coA : AE D →ₗ[AF D.host.F] AF D.host.F := cP D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F)
abbrev coB : AE D →ₗ[AF D.host.F] AF D.host.F := cQ D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F)

theorem pt_co (x : AE D) : pt δ (coA δ hδ hδ0 x) (coB δ hδ hδ0 x) = x :=
  mkE_cP_cQ D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F) x

include hδ hδ0 in
theorem pt_inj {a b a' b' : AF D.host.F} (h : pt (D := D) δ a b = pt δ a' b') : a = a' ∧ b = b' :=
  mkE_inj D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F) h

theorem pt_eq_smul (a b : AF D.host.F) :
    pt (D := D) δ a b = a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) + b • ((1 : AF D.host.F) ⊗ₜ[D.host.F] δ) := by
  simp only [pt, mkE, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem continuous_pt : Continuous fun p : AF D.host.F × AF D.host.F => pt (D := D) δ p.1 p.2 := by
  have := isModTop D
  have hA : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  have hS : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  simp only [pt_eq_smul]
  exact ((continuous_fst (X := AF D.host.F) (Y := AF D.host.F)).smul
    (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E))))).add
    ((continuous_snd (X := AF D.host.F) (Y := AF D.host.F)).smul
    (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] δ))))

end Pts

section Unit

variable (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)




theorem incA_eq_pt (α β : D.host.F) :
    incA D (algebraMap D.host.F D.host.E α + algebraMap D.host.F D.host.E β * δ) =
      pt δ (algebraMap D.host.F (AF D.host.F) α) (algebraMap D.host.F (AF D.host.F) β) :=
  incl_eq_mkE δ (AF D.host.F) α β

end Unit

end Formalism.IndefR.Fin.U1

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC Formalism.IndefR.Eqv
open scoped TensorProduct



namespace Formalism.IndefR.Fin.VacEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

end Gen

variable {D : D7}

theorem AF_ext' {p q : AF D.host.F} (h1 : fstA D.host.F p = fstA D.host.F q) (h2 : sndA D.host.F p = sndA D.host.F q) :
    p = q :=
  Prod.ext h1 h2

theorem expand_cE (z : AE D) :
    z = ∑ k, (cE D.host.F D.host.E z k) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) := by
  conv_lhs => rw [← (bA D.host.F D.host.E).sum_equivFun z]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

def Ps (m n : ℕ) (p : Fin m → Fin n → Fin (nE D) → AF D.host.F) : Mx D m n :=
  Matrix.of fun i j => (cE D.host.F D.host.E).symm (p i j)

theorem continuous_Ps {m n : ℕ} : Continuous (Ps (D := D) m n) :=
  continuous_matrix fun i j =>
    (cE D.host.F D.host.E).symm.continuous.comp ((continuous_apply j).comp (continuous_apply i))

def boxB (D : D7) (m n : ℕ) : Set (Mx D m n) :=
  Ps m n '' Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
    (fun a : Af D.host.F => pairA D.host.F 0 a) '' Ohat D.host.F

theorem isCompact_boxB (m n : ℕ) : IsCompact (boxB D m n) := by
  have hc : Continuous fun a : Af D.host.F => pairA D.host.F 0 a := by
    unfold pairA; exact continuous_const.prodMk continuous_id
  exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    (isCompact_Ohat D.host.F).image hc).image continuous_Ps

theorem nsmul_pairA (N : ℕ) (a : Af D.host.F) : N • pairA D.host.F 0 a = pairA D.host.F 0 (N • a) := by
  refine AF_ext' ?_ ?_
  · rw [map_nsmul]; show N • (0 : Ainf D.host.F) = 0; exact nsmul_zero N
  · rw [map_nsmul]; rfl

end Formalism.IndefR.Fin.VacEx
end
end
