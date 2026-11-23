module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

section Relabel

variable {K K' : Type} {ι : K → Type} {ι' : K' → Type} {κ : K → K'}
  {v : (Σ k, ι k) → (Σ k', ι' k')}

def blockVar (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) (p : Σ k, ι k) : Σ k, ι' (κ k) :=
  ⟨p.1, cast (congrArg ι' (hb.2.2.1 p)) (v p).2⟩

theorem blockIncl_blockVar (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) (p : Σ k, ι k) :
    blockIncl ⟨κ, hb.1⟩ ι' (blockVar hb p) = v p := by
  refine Sigma.ext (hb.2.2.1 p).symm ?_
  exact (cast_heq _ _)

def blockVarEquiv (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) : (Σ k, ι k) ≃ (Σ k, ι' (κ k)) :=
  Equiv.ofBijective (blockVar hb) (by
    have hI : Function.Injective (blockIncl ⟨κ, hb.1⟩ ι') := by
      rintro ⟨a, x⟩ ⟨b, y⟩ h
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
      cases hb.1 h1
      cases eq_of_heq h2
      rfl
    refine ⟨fun p q h => hb.2.1 ?_, fun ⟨k, a⟩ => ?_⟩
    · rw [← blockIncl_blockVar hb p, ← blockIncl_blockVar hb q, h]
    · obtain ⟨p, hp⟩ := hb.2.2.2 ⟨κ k, a⟩ ⟨k, rfl⟩
      exact ⟨p, hI ((blockIncl_blockVar hb p).trans hp)⟩)

theorem imageVar_eq_comap {F : Type u} [Field F] (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v)
    (V' : Ideal (MRing ι' F)) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.imageVar F v V' =
      (contractPrime ⟨κ, hb.1⟩ V').comap (rename (blockVarEquiv hb)) := by
  ext f
  unfold ReciprocityTheory.ChartRestriction.G.AI.I1.imageVar contractPrime
  simp only [Ideal.mem_comap]
  have hfun : (blockIncl ⟨κ, hb.1⟩ ι' ∘ blockVarEquiv hb) = v := funext (blockIncl_blockVar hb)
  have e : rename (blockIncl ⟨κ, hb.1⟩ ι') (rename (blockVarEquiv hb) f) = rename v f := by
    rw [rename_rename, hfun]
  exact iff_of_eq (congrArg (· ∈ V') e.symm)

end Relabel

theorem ProjDeg.of_found (hPF : ProjectionFormulaDegree.Statement.{u})
    (hFn : FnDegRelDeg.Statement.{u}) {K K' : Type} [Fintype K] [Fintype K'] (F : Type u) [Field F]
    (ι : K → Type) [∀ k, Fintype (ι k)] (ι' : K' → Type) [∀ k, Fintype (ι' k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι' := by
  classical
  intro I I' hI hI' κ v V' e L i' hb hV' hV hc
  have hA' := Numbers.agree_of IntNumBase.full CutRational.full ExistsForm.full
    DivCycleSupport.full I' hI' V' e (fun j => ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg κ (L j)) hV'
  have hA := Numbers.agree_of IntNumBase.full CutRational.full ExistsForm.full
    DivCycleSupport.full I hI _ e L hV
  rw [hA', hA]
  set j : K ↪ K' := ⟨κ, hb.1⟩
  have hP' : IsMultiProjPrime V' := (Objects.isMultiProjPrime_iff V').mpr hV'.1
  have := hP'.isPrime
  have himg := imageVar_eq_comap (F := F) hb V'

  have hRen := RenameIntNum.full F K K (fun k => ι k) (fun k => ι' (κ k)) (Equiv.refl K)
    (blockVarEquiv hb) (fun _ => rfl) (contractPrime j V') e L
  have hdimP : relDim (contractPrime j V') = (e : WithBot (WithTop ℤ)) := by
    refine relDim_eq_of_ringKrullDim _ e ?_
    have eq : MRing ι F ⧸ (contractPrime j V').comap (rename (blockVarEquiv hb)) ≃+*
        MRing (fun k => ι' (κ k)) F ⧸ contractPrime j V' :=
      Ideal.quotientEquiv _ _ (renameEquiv F (blockVarEquiv hb)).toRingEquiv
        (Ideal.map_comap_of_surjective _ (renameEquiv F (blockVarEquiv hb)).surjective _).symm
    have h2 : ringKrullDim (MRing ι F ⧸ (contractPrime j V').comap (rename (blockVarEquiv hb))) =
        ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [← himg]
      exact hV.2
    exact (ringKrullDim_eq_of_ringEquiv eq).symm.trans h2
  obtain ⟨-, hPFe⟩ := hPF F K K' j ι' V' hP' e (relDim_eq_of_ringKrullDim V' e hV'.2) hdimP L
  have hfn := hFn F K K' ι ι' κ v hb V' hP' i' hc
  rw [himg, hRen, hfn]
  exact hPFe

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ArithIntersectionSystem

theorem multilin_of_isFamily {I : AllFam} (hI : I.IsFamily) : IsMultilinFam I := by
  intro K _ ι _ P n L j A B hP hL hA hB
  cases n with
  | zero => exact j.elim0
  | succ m =>
    obtain ⟨hsym, hadd, -⟩ := hI K ι
    have e : ∀ X : HermLine ι, IsSmoothHerm X →
        I K ι P (m + 1) (Function.update L j X) =
          I K ι P (m + 1)
            (Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X) := by
      intro X hX
      rw [← GroundTheory.Heights₂.Heights.Inter.ThmIMultilin.update_comp_swap]
      exact (hsym P (m + 1) _ _ hP
        (GroundTheory.Heights₂.Heights.Inter.ThmIMultilin.smooth_update hL j hX)).symm
    rw [e _ (isSmoothHerm_tensor hA hB), e A hA, e B hB]
    exact hadd P m _ A B hP (fun i => hL _) hA hB

theorem of_found (hE : GroundTheory.Heights₂.Heights.Inter.ThmIExists.Statement) (hPF : PFCoordStatement)
    (hCM : ContractMixedStatement) : ArithIntersectionSystemStatement := by
  obtain ⟨I, hI⟩ := (hE : ExistsStatement)
  exact ⟨I, hI, multilin_of_isFamily hI, hPF I hI, hCM I hI⟩

end ArithIntersectionSystem

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj sheetDensity fibre pot PBlk oneLine
  isSmoothHerm_oneLine)

def ptsPosDens {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ) : ℝ :=
  ∑ᶠ w ∈ fibre P Ψ y, max (sheetDensity P Ψ φ g y w) 0

def PtsPosPartProjIndep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι)
    (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsGoodProj P Ψ' → (∀ j, IsSmoothHerm (L j)) →
    Measurable g → (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
      ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) g y) = ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ' (pot L) g y)

end GroundTheory.Heights₂.Heights
end
end
