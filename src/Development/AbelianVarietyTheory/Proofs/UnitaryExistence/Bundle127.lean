module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle074
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle076
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle042
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle040
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOneStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle210
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle101
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle117
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle118
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle110
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle057
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle209
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle126
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle085
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocalDataAtConcretePointsExist
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle028
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
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.UnifFamily

theorem dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : FD.Data E r) :
    X.dom.Nonempty := by
  choose P _ hP using X.signature
  exact ⟨fun τ => P τ, ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm
    X.Gm_herm).2.1 (fun τ => P τ) hP).1⟩

theorem exists_unf_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∃ U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ) ∧ Nonempty (U σ).Comp ∧ (∀ k, ((U σ).X k).dom.Nonempty) ∧ (∀ k la γ, ((U σ).X k).χ la γ = 1) ∧ ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x)) ∧ Formalism.L2.PjFree.CuspFD Xo c U ∧ Formalism.L2.PjFree.CuspMul Xo c U ∧ Formalism.L2.PjFree.SupDef Xo c U ∧ ((∀ p : ℕ, p.Prime → l.GoodAt p) → Formalism.L2.PjFree.regular₂ Xo c U) := by
  intro E _ _ _ H Dw l Xo c hpq
  classical
  have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨ξ₀, hcc, hne, him⟩ := GlobalTheory.IsUnfEx.exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ :=
    GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  have key : ∀ σ : c.F →+* ℂ, ∃ U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), Formalism.L2.PjFree.GoodEmb c σ →
      Formalism.L2.PjFree.IsUnf U ∧ Nonempty U.Comp ∧ (∀ k, (U.X k).dom.Nonempty) ∧
      (∀ k la γ, (U.X k).χ la γ = 1) ∧
      ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x) := by
    intro σ
    by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · obtain ⟨U, h1, h2, h3, -, h5, -⟩ := GlobalTheory.T.exists_frameUniformisation_prescribedSpace GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.T.hasse_norm_theorem_quadratic_extension hB hT
        E H Dw l Xo c σ (Dw.p + Dw.q) ξ₀ Gm φ hpq hσ hcc him hφ
      exact ⟨U, fun _ => ⟨h1, h2, fun k => dom_nonempty _, h3, h5⟩⟩
    · obtain ⟨U, -⟩ := GlobalTheory.T.exists_uniformisationData_nonempty_component E H Dw l Xo c hpq σ
      exact ⟨U, fun h => absurd h hσ⟩
  choose U hU using key
  have h₀ : Formalism.L2.PjFree.GoodEmb c (c.F.val : c.F →+* ℂ) := by
    exact rfl
  refine ⟨U, hU, GlobalTheory.T.cuspForms_dominantWeight_finiteDimensional hB E H Dw l Xo c _ U _ h₀ (hU _ h₀).1,
    GlobalTheory.CuspProduct.cuspMul_holds E H Dw l Xo c _ U,
    GlobalTheory.T.supNorm_definite_on_cuspForms_goodEmbedding E H Dw l Xo c _ U (fun σ h => (hU σ h).1), fun hg => ?_⟩
  exact (GlobalTheory.Reg.sCharts_and_transfer_of_good_level GlobalTheory.T.compactifiedModuli_partOne GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level E H Dw l Xo c hpq hg).2.1 _ U

end GlobalTheory.UnifFamily
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Member

theorem exists_completion_of_core_satisfying_laws : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Core D), LawsCore T → (∀ j, 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q) → (∀ j, InR D j → KPsiIn (Dw := T.Q.Dw j) T.Q.c) → (∀ j, InR D j → ∀ (_ : StarRing (𝓞 D.host.E)) (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab → ThInCusp (T.Q.Xo j) T.Q.c nab (T.cuspA j) ∧ (j < D.R.m → ThNe0 (T.Q.Xo j) T.Q.c nab)) → ∃ T' : Top D, LawsP T' ∧ T'.toCore = T := by
  intro hC D T hT hpq hK hth
  obtain ⟨G, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.localDataAtConcretePoints_exist D T.Q hT.pins hpq
  have hnab := fun j => GlobalTheory.CanonConn.exists_isNab_uncond D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  choose st nab hN using hnab
  have hgood := (GlobalTheory.T.level_good_and_half_eq_prime_product D T.Q.H T.Q.l hT.pins.1.2.1 hT.pins.2.1.1).1
  have hreg := fun j => GlobalTheory.Reg.sCharts_and_transfer_of_good_level GlobalTheory.T.compactifiedModuli_partOne GlobalTheory.Moduli.moduli_scheme_exists
    D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (hpq j) hgood
  refine ⟨{ toCore := T, G := G, nab := nab,
            dδ := fun j n => noDelta (T.Q.Xo j) T.Q.c (nab j) (GlobalTheory.ObjLower.sabId (T.Q.Xo j).univ.t) n }, ?_, rfl⟩
  exact
    { toLawsCore := hT
      allTest := fun j _ => GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange D.host.E T.Q.H (T.Q.Dw j)
        T.Q.l (T.Q.Xo j) T.Q.c
      reg := fun j _ => (Formalism.L2.PjFree.regP_ofPj (T.U j)).1 ((hreg j).2.1 D.R.r _)
      datum_condition := h1
      tower := h2
      hasData_condition := h3
      points_condition := h4
      lattice_condition := h5
      bc66 := h6
      datIndep := fun j _ _ => GlobalTheory.T.latticePeriodForm_independent_of_models D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
      nabPin := fun j _ => ⟨st j, hN j⟩
      nabUniq := fun j _ => Formalism.MainNotions.ModuliIntegralCharts.H1.nabUniq_of_chartIndep2 hC (T.Q.Xo j) T.Q.c
      thTot := fun j _ => @GlobalTheory.thValTot_of_chartIndep GlobalTheory.firstFiveLaws.1 hC D.host.E _ _ _ T.Q.H (T.Q.Dw j) T.Q.l
        (T.Q.Xo j) T.Q.c (st j) (nab j) (hN j)
      thCusp := fun j hj => (hth j hj (st j) (nab j) (hN j)).1
      thNe := fun j h1 h2 => (hth j ⟨h1, h2.le⟩ (st j) (nab j) (hN j)).2 h2
      kPsi := hK }

end GlobalTheory.Member
end
