module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHatMxHomLatIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle276
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle278
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle127
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightLeOfNoShortVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle267
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle279
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle280
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FderivConjFrameToRealLieLoweringOperatorEqZero
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Function.Bijective (diagH σ J F) ∧ ∀ γ : GRat σ J, Irreducible γ.1.1.charpoly → ∃ P : PPol σ n, γ.1.1.charpoly = P.1 ∧ ∃ q, HasCls P F J (diagH σ J F γ) q := by
  first | exact @GlobalTheory.TrEll.RatEll.exists_cls_of_irreducible | exact GlobalTheory.TrEll.RatEll.exists_cls_of_irreducible | (intros; apply GlobalTheory.TrEll.RatEll.exists_cls_of_irreducible <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.HatFrame

section General

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P Formalism.L2.DIV GlobalTheory.NormSum.AdLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ}

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem approx_of_mem_genGrp {Λ : Submodule (𝓞 E) (Fin n → E)} {Λ' : Submodule (𝓞 E) (Fin m → E)}
    {β : GL (Fin n) 𝒜} {β' : GL (Fin m) 𝒜} (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ')
    {H : Submodule (𝓞 E) (Matrix (Fin m) (Fin n) E)} (hH : ∀ x ∈ H, ∀ y ∈ Λ, x *ᵥ y ∈ Λ')
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    ∀ w ∈ genGrp F H, ∃ x₀ ∈ H, x₀.map ι - w ∈ frGrp β β' (idS F I) := by
  intro w hw
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    have hα' : (1 : E) ⊗ₜ[F] α ∈ 𝒮 := Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    obtain ⟨q, hr⟩ := cmpS_surj (F := F) I hI (Ideal.Quotient.mk _ ⟨_, hα'⟩)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hr' : oToS F E r - ⟨_, hα'⟩ ∈ idS F I := by
      rw [← Ideal.Quotient.eq]
      rw [← hr]
      rfl
    refine ⟨r • x, H.smul_mem r hx, ?_⟩
    have e : (r • x).map ι - (Matrix.of fun i j => x i j ⊗ₜ[F] α : Matrix (Fin m) (Fin n) 𝒜) =
        ((oToS F E r - ⟨_, hα'⟩ : 𝒮) : 𝒜) • x.map ι := by
      ext i j
      show ((algebraMap (𝓞 E) E r * x i j) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) - x i j ⊗ₜ[F] α =
        ((algebraMap (𝓞 E) E r ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) - ((1 : E) ⊗ₜ[F] α)) *
          (x i j ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
      rw [sub_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one]
    rw [e]
    exact smul_mem_frGrp β β' hr' (fun i j => frame_int hβ hβ' (hH x hx) i j)
  | zero => exact ⟨0, zero_mem _, by rw [Matrix.map_zero _ (map_zero _), sub_zero]; exact zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, hxa⟩ := ha
    obtain ⟨y, hy, hyb⟩ := hb
    refine ⟨x + y, add_mem hx hy, ?_⟩
    rw [Matrix.map_add _ (map_add _), add_sub_add_comm]
    exact add_mem hxa hyb
  | neg a _ ha =>
    obtain ⟨x, hx, hxa⟩ := ha
    refine ⟨-x, neg_mem hx, ?_⟩
    rw [Matrix.map_neg _ (map_neg _), neg_sub_neg, ← neg_sub]
    exact neg_mem hxa

theorem approx_general {Λ : Submodule (𝓞 E) (Fin n → E)} {Λ' : Submodule (𝓞 E) (Fin m → E)}
    {β : GL (Fin n) 𝒜} {β' : GL (Fin m) 𝒜} (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ')
    {H : Submodule (𝓞 E) (Matrix (Fin m) (Fin n) E)} (hH : ∀ x ∈ H, ∀ y ∈ Λ, x *ᵥ y ∈ Λ')
    (hH' : ∀ x, (∀ y ∈ Λ, x *ᵥ y ∈ Λ') → x ∈ H) (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (N : Matrix (Fin m) (Fin n) 𝒮) :
    ∃ x₀ ∈ H, ∀ i j, ∃ s ∈ idS F I,
      (s : 𝒜) = HMul.hMul (HMul.hMul (β'⁻¹).val (x₀.map ι)) β.val i j - (N i j : 𝒜) := by
  set Nc : Matrix (Fin m) (Fin n) 𝒜 := Matrix.of fun i j => (N i j : 𝒜) with hNc
  set z : Matrix (Fin m) (Fin n) 𝒜 := HMul.hMul (HMul.hMul β'.val Nc) (β⁻¹).val with hz
  have hfr : HMul.hMul (HMul.hMul (β'⁻¹).val z) β.val = Nc := by
    rw [hz, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  have hz1 : z ∈ frGrp β β' (idS F ⊤) := by
    intro i j
    refine ⟨N i j, by rw [idS, Ideal.map_top]; trivial, ?_⟩
    rw [hfr]
    rfl
  have hz2 := frGrp_le_genGrp hβ hβ' hH' ⊤ hz1
  rw [Submodule.top_smul] at hz2
  obtain ⟨x₀, hx₀, hd⟩ := approx_of_mem_genGrp hβ hβ' hH I hI z hz2
  refine ⟨x₀, hx₀, fun i j => ?_⟩
  obtain ⟨s, hs, e⟩ := hd i j
  refine ⟨s, hs, ?_⟩
  rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, hfr]
  rfl

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem homLat_approx_mod : ∀ {D : D7} {m n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)), Formalism.L2.DIV.IsFrame β Λ → Formalism.L2.DIV.IsFrame β' Λ' → ∀ (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ (N : Matrix (Fin m) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)), ∃ x₀ ∈ GlobalTheory.ChiGrid.homLat Λ Λ', ∀ i j, ∃ s ∈ Formalism.L2.DIV.idS D.host.F I, (s : EAf D) = HMul.hMul (HMul.hMul (β'⁻¹).val (x₀.map (eToEAf D))) β.val i j - (N i j : EAf D) := by
  intro D m n Λ Λ' β β' hβ hβ' I hI N
  exact approx_general hβ hβ' (H := GlobalTheory.ChiGrid.homLat Λ Λ') (fun _ hx => hx) (fun _ hx => hx) I hI N

end GlobalTheory.FunObj.HatFrame

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteAdeleTensorCoords_mul_denominator_bound : ∀ (D : D7), ∃ c : ℕ, 0 < c ∧ ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E), (∀ k, (e₁ : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D a k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → (∀ k, (e₂ : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D b k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → ∀ k, ((c * e₁ * e₂ : ℕ) : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (a * b) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  first | exact @GlobalTheory.CoordDenom.finCoord_mul_denom | exact GlobalTheory.CoordDenom.finCoord_mul_denom | (intros; apply GlobalTheory.CoordDenom.finCoord_mul_denom <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eq_sum_finiteCoords_of_infinitePart_zero : ∀ (D : D7) (z : AE D), infPart D z = 0 → z = ∑ k, pairA D.host.F 0 (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (GlobalTheory.HolDict.ShortVec.finPr D z) k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k := by
  first | exact @GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero | exact GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero | (intros; apply GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_natMul_integralMatrices_subset_openAddSubgroup : ∀ (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)), IsOpen (U : Set (WO V W)) → ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ a : Fin W.rank → Fin V.rank → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F, (∀ i j k, a i j k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : WO V W) ∈ U := by
  first | exact @GlobalTheory.OpenSubAdele.exists_nat_mul_mem_openAddSubgroup | exact GlobalTheory.OpenSubAdele.exists_nat_mul_mem_openAddSubgroup | (intros; apply GlobalTheory.OpenSubAdele.exists_nat_mul_mem_openAddSubgroup <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.typePlaces_over_norm_and_cover_with_conjugates : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → (∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ R.Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP := by
  first | exact @GlobalTheory.SeeConjRead.places_over_g | exact GlobalTheory.SeeConjRead.places_over_g | (intros; apply GlobalTheory.SeeConjRead.places_over_g <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryQuotientHeight_le_of_no_short_vector : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (b : ℕ), ∀ (g : GA D V) (t : ℝ), 0 < t → t ≤ 1 → (∀ ξ : Fin V.rank → D.host.E, ξ ≠ 0 → t ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ)) → GlobalTheory.Grow.quotHeight V g * t ^ b ≤ C := by
  first | exact @GlobalTheory.HtMahler.quotHeight_le_of_no_short | exact GlobalTheory.HtMahler.quotHeight_le_of_no_short | (intros; apply GlobalTheory.HtMahler.quotHeight_le_of_no_short <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realPlaceDeterminantPower_mul_compactTorusElement : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (m : D.what₂.Tau → ℤ) (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (g : GA D T), detPow C.θ T m (g * torAt C.θ T B ρ t) = cexp (((∑ a, ((m ρ : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) * detPow C.θ T m g := by
  first | exact @GlobalTheory.AdSpan.DetTor.detPow_mul_torAt | exact GlobalTheory.AdSpan.DetTor.detPow_mul_torAt | (intros; apply GlobalTheory.AdSpan.DetTor.detPow_mul_torAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weightedTrace_conjFrameToRealLie_loweringOperator : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ (m : D.what₂.Tau → ℤ) (ρ : D.what₂.Tau) (c d : Fin T.rank), c < d → ∀ (Z Z' : Frame C.X.Ψ T.rank), Z ∈ GlobalTheory.HolRead.unitLie C.X → Z' ∈ GlobalTheory.HolRead.unitLie C.X → Z + I • Z' = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d → GlobalTheory.AdSpan.ConjHol.trLin T m (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z) + I * GlobalTheory.AdSpan.ConjHol.trLin T m (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z') = 0 := by
  first | exact @GlobalTheory.AdSpan.ConjHol.trLin_toLieC_unitFr | exact GlobalTheory.AdSpan.ConjHol.trLin_toLieC_unitFr | (intros; apply GlobalTheory.AdSpan.ConjHol.trLin_toLieC_unitFr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.compactTorusProductRealPlaces_spec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (s : D.what₂.Tau → Fin T.rank → ℝ), GlobalTheory.AdSpan.ConjHol.torProd C.θ T B s ∈ GinfC T ∧ ∀ ρ, compAt C.θ ρ (Formalism.L2.Theta.mt T (GlobalTheory.AdSpan.ConjHol.torProd C.θ T B s)) = B ρ * diagonal (fun c => cexp ((s ρ c : ℂ) * I)) * (B ρ)⁻¹ := by
  first | exact @GlobalTheory.AdSpan.ConjHol.torProd_spec | exact GlobalTheory.AdSpan.ConjHol.torProd_spec | (intros; apply GlobalTheory.AdSpan.ConjHol.torProd_spec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjFrameToRealLieAlgebra_spec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ Z ∈ GlobalTheory.HolRead.unitLie C.X, (∀ ρ, (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z ρ).1 = B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹) ∧ GlobalTheory.AdSpan.ConjHol.toLieC C R B (I • Z) = 0 := by
  first | exact @GlobalTheory.AdSpan.ConjHol.ToLie.toLieC_spec | exact GlobalTheory.AdSpan.ConjHol.ToLie.toLieC_spec | (intros; apply GlobalTheory.AdSpan.ConjHol.ToLie.toLieC_spec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fderiv_conjFrameToRealLie_loweringOperator_eq_zero : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ (φ : GA D T → ℂ), LowKilled C.θ T B φ → ∀ (g : GA D T) (ρ : D.what₂.Tau) (c d : Fin T.rank), c < d → ∀ (Z Z' : Frame C.X.Ψ T.rank), Z ∈ GlobalTheory.HolRead.unitLie C.X → Z' ∈ GlobalTheory.HolRead.unitLie C.X → Z + I • Z' = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d → fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0 (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z) + I * fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0 (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z') = 0 := by
  first | exact @GlobalTheory.AdSpan.ConjHol.fderiv_toLieC_eq_zero | exact GlobalTheory.AdSpan.ConjHol.fderiv_toLieC_eq_zero | (intros; apply GlobalTheory.AdSpan.ConjHol.fderiv_toLieC_eq_zero <;> assumption)
end
