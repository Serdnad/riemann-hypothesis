module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ClassMapD
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle793
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.IsIrreducibleOfIsIrrRep
public import Development.DiscreteGroups.GlobalIrreducibility.LocTypeOfSerParamLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle177
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace UpperTheory.One.M

open GlobalTheory GlobalTheory.SerSys GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil

theorem mapsToProd_tw {g : ℕ} [Fact g.Prime] {n a b : ℕ} {V W W' W'' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup W''] [Module ℂ W'']
    {π : Representation ℂ (GL (Fin n) ℚ_[g]) V} {σ : Representation ℂ (GL (Fin a) ℚ_[g]) W}
    {ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W'} {ρ' : Representation ℂ (GL (Fin b) ℚ_[g]) W''} (μ : ℚ_[g]ˣ →* ℂˣ)
    (hμ : Supp.IsUnram μ) (e : W' ≃ₗ[ℂ] W'')
    (he : ∀ y v, ρ' y (e v) = ((μ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • e (ρ y v)) (h : Supp.MapsToProd π σ ρ) :
    Supp.MapsToProd π σ ρ' := by
  obtain ⟨hn, ν₁, ν₂, Λ, h₁, h₂, h0, H⟩ := h
  refine ⟨hn, ν₁, ν₂ * μ⁻¹, (TensorProduct.congr (LinearEquiv.refl ℂ W) e).toLinearMap ∘ₗ Λ, h₁, fun u => ?_, fun h => h0 (LinearMap.ext fun v => ?_),
    fun p x y hp hx hy v => ?_⟩
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h₂ u, hμ u, inv_one, mul_one]
  · exact (TensorProduct.congr (LinearEquiv.refl ℂ W) e).map_eq_zero_iff.1 (LinearMap.congr_fun h v)
  · have key : ∀ z, TensorProduct.map (σ x) (ρ' y) (TensorProduct.congr (LinearEquiv.refl ℂ W) e z) =
        ((μ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
          TensorProduct.congr (LinearEquiv.refl ℂ W) e (TensorProduct.map (σ x) (ρ y) z) := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul s t => simp [he, TensorProduct.tmul_smul]
      | add s t hs ht => simp only [map_add (f := _), hs, ht, smul_add]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [H p x y hp hx hy v, key, map_smul, smul_smul]
    congr 1
    simp [mul_assoc]

theorem inInd_reps {g : ℕ} [Fact g.Prime] {π : Supp.GLRep g} {L : List (Supp.GLRep g)} (h : Supp.InInd π L) :
    ∀ y : List (IrrGL (k := ℚ_[g])), List.Forall₂ (fun (ρ : Supp.GLRep g) (x : IrrGL (k := ℚ_[g])) =>
      ∃ (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible), (IrrGL.of ρ.2.ρ hs hi).Inert x) L y →
      Supp.InInd π (y.map fun x => ⟨x.1, Rep.of x.rep⟩) := by
  induction h with
  | nil π h0 hi =>
    intro y hy
    cases hy
    exact .nil π h0 hi
  | cons π σ ρ S hπ hρ _ hM ih =>
    intro y hy
    cases hy with
    | cons h1 h2 =>
      obtain ⟨hs, hi, μ, hμ, rfl⟩ := h1
      let φ := (GlobalTheory.TypeRec.TwistInert.twistEquiv (IrrGL.equivOf ρ.2.ρ hs hi) (detChar (Fin ρ.1) μ)).trans
        (IrrGL.twEquiv (IrrGL.of ρ.2.ρ hs hi) μ (isSmoothChar_of_isUnram hμ))
      refine .cons π σ _ _ hπ (Ysupp.IrreducibleSupport.isIrrRep_of_isIrreducible (IrrRep.irr _)) (ih _ h2)
        (mapsToProd_tw μ (fun u => hμ _ ?_) φ.toLinearEquiv (fun y v => ?_) hM)
      · have hn : ‖((u : ℤ_[g]) : ℚ_[g])‖ = 1 := PadicInt.norm_units u
        have a1 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g ((u : ℤ_[g]) : ℚ_[g]) 1
        have a2 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 ((u : ℤ_[g]) : ℚ_[g])
        rw [hn, map_one, norm_one] at a1 a2
        exact le_antisymm (not_lt.1 fun h => lt_irrefl _ (a2.1 h)) (not_lt.1 fun h => lt_irrefl _ (a1.1 h))
      · rw [← map_smul]
        exact (LinearMap.congr_fun (φ.isIntertwining' y) v).symm

end UpperTheory.One.M
end

section

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.PrimeDegreeVariant GlobalTheory.TypeLeaf
namespace DiscreteGroups.sglob.DzType.Rt

theorem good_of_vector_row_m : ∀ (D : D7) (Rw : GlobalTheory.HeightCounting.RowSide D) (L : ∀ k, LabelDatum (D.host.g k)) (rc : GlobalTheory.SerSys.Corr D) (cp : GlobalTheory.GoodTypes.Comp D), LabTie D L → DiscreteGroups.sglob.DzType.Rt.LabParamLe D.R.nV D L rc → (∀ k v, GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v)) → GlobalTheory.GoodTypes.SeriesConj D → (∀ σ k v, IrrSm (cp σ k v) ∧ Rw.locR σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (σ : D.what₂.FT), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) → ∀ x : V, x ≠ 0 → (∀ a, ρ.asAlgebraHom a x ∈ W) → ρ.asAlgebraHom D.ntypes.e0 x = x → D.nd.goodRow σ := by
  intro D Rw L rc cp hT hLP hCl hC hP V _ _ ρ W σ hW x hx hxW he
  obtain ⟨t, a, ht, h0, hfix⟩ := GlobalTheory.GoodTypes.exists_good D ρ hx he
  have key : ∀ k v, GlobalTheory.SeriesSupportTest.dualFun D k (t k v) = D.nd.lab k σ v := by
    intro k v
    have hl : IsLabel D k (t k v) := (ht k).1.1 v
    have h1 := hfix k v
    rw [GlobalTheory.GoodTypes.act_atPlace] at h1
    have h2 := (hW k v).act_ne _ (D.ntypes.eSer k (dualLab D k (t k v))) (fun y => by
      rw [← GlobalTheory.GoodTypes.labAct_conj D k hl, ← hC k _ hl, Finsupp.mapRange_apply]; rfl) (hxW a) h0 h1
    obtain ⟨p1, p3⟩ := hP σ k v
    have q1 := ((hCl k v) _ _ p1).1
    rw [(hT k).2] at h2
    have h3 := hLP k v D.R.r (DiscreteGroups.sglob.DzType.Rt.r_le_nV D) (cp σ k v) p1 _ h2
    rw [(hT k).1] at h3
    simp only [] at h3
    rw [← p3] at h3 q1
    rw [D.ntypes.inertiaCharpoly_type k v _ (by rw [← Rw.lab_eq, q1, (D.nd.lab_monic k σ v).2]), ← Rw.lab_eq] at h3
    rw [GlobalTheory.SeriesSupportTest.dualFun, if_pos hl]
    exact GlobalTheory.GoodTypes.eq_of_teich _ (GlobalTheory.Compare.TeichmullerRoots.teich_injective _ (D.ntypes.teichC_inj k))
      (GlobalTheory.SeriesSupportTest.label_dual D k hl).1 (D.nd.lab_monic k σ v).1 h3.symm
  have hd := GlobalTheory.SeriesSupportTest.good_dualFun D t ht
  simp only [key] at hd
  exact hd

end DiscreteGroups.sglob.DzType.Rt
end
end
