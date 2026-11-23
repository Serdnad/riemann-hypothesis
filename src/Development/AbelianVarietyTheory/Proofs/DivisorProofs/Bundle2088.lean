module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingInvMixPairKunnethIsogeny
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle754
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalSetConjFiniteIndexSubgroup
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle886
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2043
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle431
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport
namespace PrimFrameTr

section Fields
variable {k k' : Type} [Field k] [Field k']

theorem rank_map_le {A D : Type} [Fintype A] [Fintype D] [DecidableEq D] (f : k →+* k') (Z : Matrix A D k) :
    (Z.map f).rank ≤ Z.rank := by
  classical
  let M := LinearMap.range Z.mulVecLin
  let b := Module.finBasis k M
  have hc : ∀ y : D, (fun x => Z x y) ∈ M := fun y => ⟨Pi.single y 1, by ext x; simp⟩
  let P : Matrix A (Fin (Module.finrank k M)) k := Matrix.of fun x l => (b l : A → k) x
  let Q : Matrix (Fin (Module.finrank k M)) D k := Matrix.of fun l y => b.repr ⟨fun x => Z x y, hc y⟩ l
  have hPQ : Z = P * Q := by
    ext x y
    have h := congrArg (fun z : M => (z : A → k) x) (b.sum_repr ⟨fun x => Z x y, hc y⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply]
    simp only [P, Q, Matrix.of_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have h : Z.map f = P.map f * Q.map f := by rw [hPQ, Matrix.map_mul]
  rw [h]
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans ?_)
  simpa only [Fintype.card_fin] using (Matrix.finrank_range_mulVecLin Z).le

theorem rank_map_equiv {A D : Type} [Fintype A] [Fintype D] [DecidableEq D] (j : k ≃+* k') (Z : Matrix A D k) :
    (Z.map j).rank = Z.rank := by
  refine le_antisymm (rank_map_le (j : k →+* k') Z) ?_
  have := rank_map_le (j.symm : k' →+* k) (Z.map j)
  have e : (Z.map j).map (j.symm : k' →+* k) = Z := by ext; simp
  rwa [e] at this

theorem rank_trM {A D A₂ D₂ : Type} [Fintype A] [Fintype D] [DecidableEq D] [Fintype D₂]
    (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) : (trM j rA cD Z).rank = Z.rank := by
  have : trM j rA cD Z = (Z.map j).submatrix rA cD := by ext; rfl
  rw [this, Matrix.rank_submatrix, rank_map_equiv]

theorem row_trM {A D A₂ D₂ : Type} (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) (r : A₂) :
    (trM j rA cD Z).row r = fun c => j (Z.row (rA r) (cD c)) := rfl

theorem read_sum {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (c : A → k) :
    (fun d => j ((∑ a, c a • Z.row a) (cD d))) = ∑ r, j (c (rA r)) • (trM j rA cD Z).row r := by
  funext d

  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, row_trM]
  exact (Fintype.sum_equiv rA _ _ fun r => rfl).symm

theorem mem_spanK_of {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) {x : D → k} (hx : x ∈ Submodule.span k (Set.range Z.row)) :
    (fun d => j (x (cD d))) ∈ Submodule.span k' (Set.range (trM j rA cD Z).row) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
  rw [read_sum j rA cD Z c]
  exact (Submodule.mem_span_range_iff_exists_fun k').2 ⟨_, rfl⟩

end Fields

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}

theorem isLocIso_symm (hj : IsLocIso j) : IsLocIso j.symm :=
  ⟨hj.2.1, by simpa using hj.1, fun x => by rw [← hj.2.2 (j.symm x)]; simp⟩

theorem mem_spanO_of (hj : IsLocIso j) {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) {x : D → k} (hx : x ∈ Submodule.span 𝒪[k] (Set.range Z.row)) :
    (fun d => j (x (cD d))) ∈ Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 hx
  have h := read_sum j rA cD Z (fun a => (c a : k))
  have e : (∑ a, c a • Z.row a) = ∑ a, (c a : k) • Z.row a := Finset.sum_congr rfl fun a _ => rfl
  rw [e, h]
  exact (Submodule.mem_span_range_iff_exists_fun 𝒪[k']).2
    ⟨fun r => ⟨j (c (rA r)), (hj.2.2 _).2 (c (rA r)).2⟩, rfl⟩

theorem read_symm {D D₂ : Type} (cD : D₂ ≃ D) (x : D → k) :
    (fun d => j.symm ((fun c => j (x (cD c))) (cD.symm d))) = x := by
  funext d; simp

theorem trM_symm {A D A₂ D₂ : Type} (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) :
    trM j.symm rA.symm cD.symm (trM j rA cD Z) = Z := trM_symm_trM j rA cD Z

def readEquiv (j : k ≃+* k') {D D₂ : Type} (cD : D₂ ≃ D) : (D → k) ≃ (D₂ → k') where
  toFun x d := j (x (cD d))
  invFun y d := j.symm (y (cD.symm d))
  left_inv x := by funext d; simp
  right_inv y := by funext d; simp

theorem memK_iff {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (x : D → k) :
    (fun d => j (x (cD d))) ∈ Submodule.span k' (Set.range (trM j rA cD Z).row) ↔
      x ∈ Submodule.span k (Set.range Z.row) := by
  refine ⟨fun h => ?_, mem_spanK_of j rA cD Z⟩
  have := mem_spanK_of j.symm rA.symm cD.symm _ h
  rwa [read_symm, trM_symm] at this

theorem memO_iff (hj : IsLocIso j) {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (x : D → k) :
    (fun d => j (x (cD d))) ∈ Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) ↔
      x ∈ Submodule.span 𝒪[k] (Set.range Z.row) := by
  refine ⟨fun h => ?_, mem_spanO_of hj rA cD Z⟩
  have := mem_spanO_of (isLocIso_symm hj) rA.symm cD.symm _ h
  rwa [read_symm, trM_symm] at this

end PrimFrameTr


open PrimFrameTr in
theorem isPrimFrame_trM_iff {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    {j : k ≃+* k'} {A D A₂ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype A₂]
    [DecidableEq A₂] [Fintype D₂] [DecidableEq D₂] (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (hL : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) :
    IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := by
  have hc : Fintype.card A₂ = Fintype.card A := Fintype.card_congr rA
  have hm : trM j rA cD Z ∈ matLat A₂ Λ₂ ↔ Z ∈ matLat A Λ := by
    rw [mem_matLat, mem_matLat]
    refine (forall_congr' fun r => ?_).trans (rA.forall_congr_right (q := fun a => Z.row a ∈ Λ))
    exact hL (Z.row (rA r))
  have hs : (Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) =
        (Submodule.span k' (Set.range (trM j rA cD Z).row)).restrictScalars 𝒪[k'] ⊓ Λ₂) ↔
      (Submodule.span 𝒪[k] (Set.range Z.row) =
        (Submodule.span k (Set.range Z.row)).restrictScalars 𝒪[k] ⊓ Λ) := by
    rw [SetLike.ext_iff, SetLike.ext_iff]
    refine ((readEquiv j cD).forall_congr_right).symm.trans (forall_congr' fun x => ?_)
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
    change ((fun d => j (x (cD d))) ∈ _ ↔ (fun d => j (x (cD d))) ∈ _ ∧ (fun d => j (x (cD d))) ∈ Λ₂) ↔ _
    rw [memO_iff hj, memK_iff, hL]
  unfold IsPrimFrame
  rw [rank_trM, hc, hm, hs]
end GlobalTheory.PureMatch.Transport
end
end

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch.Transport

theorem dualLat_latCorr {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
    {D D₂ : Type} [Fintype D] [Fintype D₂] (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) : LatCorr j cD (dualLat Λ) (dualLat Λ₂) := by
  have key : ∀ y x : D → k, (fun c => j (y (cD c))) ⬝ᵥ (fun c => j (x (cD c))) = j (y ⬝ᵥ x) := by
    intro y x

    simp only [dotProduct, map_sum, map_mul]
    exact Fintype.sum_equiv cD _ _ fun c => rfl
  intro y
  rw [mem_dualLat, mem_dualLat]
  constructor
  · intro H x hx
    have := H _ ((h x).2 hx)
    rw [key] at this
    exact (hj.2.2 _).1 this
  · intro H x₂ hx₂
    set x : D → k := fun d => j.symm (x₂ (cD.symm d)) with hxdef
    have hx : (fun c => j (x (cD c))) = x₂ := by
      funext c; simp [x]
    rw [← hx] at hx₂ ⊢
    rw [key]
    exact (hj.2.2 _).2 (H x ((h x).1 hx₂))

end GlobalTheory.PureMatch.Transport
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw


theorem _root_.GlobalTheory.T.movedStaircaseTensor_periodic_uniformizerPow : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s)
    (ϖ : kˣ), IsUnif ϖ → ∀ (e : ℕ) (T : G.Args → ℂ), G.IsTensor ϖ e (oppositePath G.m) T → ∀ (J : G.Level) (keep : Bool)
    (x : ColArgs G) (y : RowArgs G) (v l : Vars G), l ∈ varLat G ϖ (G.m * e) →
    moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y (v + l)) =
      moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y v) := by
  first | exact @GlobalTheory.UnfoldLoss.moved_stair_periodic | exact GlobalTheory.UnfoldLoss.moved_stair_periodic | (intros; apply GlobalTheory.UnfoldLoss.moved_stair_periodic <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw


theorem _root_.GlobalTheory.T.addChar_neg_unfoldingPhase_mul_uniformizerPowLattice : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k)
    (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ (ϖ : kˣ), IsUnif ϖ → ∀ (n : ℕ) (x : ColArgs G) (v l l' : Vars G),
    l ∈ varLat G ϖ n → l' ∈ varLat G ϖ n →
    (ψ (-phase x (v + l + l')) : ℂ) * (ψ (-phase x v) : ℂ) = (ψ (-phase x (v + l)) : ℂ) * (ψ (-phase x (v + l')) : ℂ) := by
  first | exact @GlobalTheory.UnfoldLoss.PhaseQuad.psi_phase_mul | exact GlobalTheory.UnfoldLoss.PhaseQuad.psi_phase_mul | (intros; apply GlobalTheory.UnfoldLoss.PhaseQuad.psi_phase_mul <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.cech_nonvanishing_invMix_pair_kunneth_isogeny : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ α β γ δ : ℤ, α * β + γ * δ = 0 → ((α * δ - β * γ : ℤ) : K) ≠ 0 → ∀ L : LB A.left, L.IsLB → ∀ a b j : ℕ, NV A (mix A L a b) j → ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (a * tri α + b * tri (-α) + a * tri γ + b * tri (-γ)) (a * tri (-α) + b * tri α + a * tri (-γ) + b * tri γ)) j₁ ∧ NV A (mix A L (a * tri β + b * tri (-β) + a * tri δ + b * tri (-δ)) (a * tri (-β) + b * tri β + a * tri (-δ) + b * tri δ)) j₂ := by
  first | exact @GlobalTheory.AmpleGen.nv_mix_pair_of_nv | exact GlobalTheory.AmpleGen.nv_mix_pair_of_nv | (intros; apply GlobalTheory.AmpleGen.nv_mix_pair_of_nv <;> assumption)
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

namespace GlobalTheory.FundFrames

open scoped Pointwise

theorem isFundamentalDomain_satFrames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {c : ℝ≥0∞}, HaarChart X c → ∀ {x0 : Frame X.Ψ r}, IsOrth X x0 → ∀ {FF : Set (V (nd X))}, IsFundSet X x0 FF → ∀ (Λ : Subgroup (RealGrp X)), (∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) → IsFundamentalDomain Λ (frameOf X ⁻¹' GlobalTheory.Unfold.satFrames X x0 FF) (haarR X) := by
  intro E _ _ _ r X c hH x0 ho FF hF Λ hΛ
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  set S := GlobalTheory.Unfold.satFrames X x0 FF with hSdef
  have hS : MeasurableSet S := GlobalTheory.Unfold.measurableSet_satFrames X ho hF.1 hF.2.1

  have hmemT : ∀ (s : Λ) (g : RealGrp X) (γ : GL (Fin r) E), lact γ (baseFr X) = frameOf X s →
      (g ∈ s • (frameOf X ⁻¹' S) ↔ lact γ⁻¹ (frameOf X g) ∈ S) := by
    intro s g γ e
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_preimage]
    have h1 : lact γ (frameOf X (s⁻¹ • g)) = frameOf X g := by
      rw [GlobalTheory.PeterssonCompare.lact_frameOf X e, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv,
        mul_inv_cancel_left]
    have h2 : frameOf X (s⁻¹ • g) = lact γ⁻¹ (frameOf X g) := by
      rw [← h1, FundSetPf.lact_inv]
    rw [h2]
  refine ⟨(GlobalTheory.PeterssonCompare.measurable_frameOf X hS).nullMeasurableSet, ?_, ?_⟩
  ·
    set G' : Set (Frame X.Ψ r) := ⋃ γ : X.Γ, (fun y => lact (γ.1)⁻¹ y) ⁻¹' S with hG'def
    have hG' : MeasurableSet G' :=
      MeasurableSet.iUnion fun γ => (GlobalTheory.Unfold.continuous_lact X _).measurable hS
    have hmemG : ∀ y, y ∈ G' ↔ ∃ γ ∈ X.Γ, lact γ⁻¹ y ∈ S := by
      intro y
      simp only [G', Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨γ, hy⟩; exact ⟨γ.1, γ.2, hy⟩
      · rintro ⟨γ, hγ, hy⟩; exact ⟨⟨γ, hγ⟩, hy⟩
    have hGB : ∀ y, ∀ b ∈ Bor X.Ψ r, rmul y b ∈ G' ↔ y ∈ G' := by
      intro y b hb
      simp only [hmemG, FundSetPf.lact_rmul, hSdef, GlobalTheory.Unfold.rmul_mem_satFrames_iff X x0 FF _ hb]
    set φ : Frame X.Ψ r → ℝ≥0∞ := G'ᶜ.indicator 1 with hφdef
    have hφm : Measurable φ := measurable_const.indicator hG'.compl
    have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x := by
      intro x _ b hb
      have hiff : rmul x b ∈ G'ᶜ ↔ x ∈ G'ᶜ := by
        simp only [Set.mem_compl_iff, hGB x b hb]
      by_cases hx : x ∈ G'ᶜ
      · rw [hφdef, Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]; rfl
      · rw [hφdef, Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hiff.1 h'))]
    have hbo : IsOrth X (baseFr X) := fun τ => baseFr_mem X τ
    have h1 : GlobalTheory.SubgroupUnfold.IsIsom X.Gm (1 : GL (Fin r) E) := by
      intro v w; simp
    have hae := GlobalTheory.SubgroupUnfold.ae_mem_orbit_satFrames X ho hF hbo h1
    have hz : ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) = 0 := by
      rw [← lintegral_zero (μ := muF X (baseFr X))]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with z hz
      obtain ⟨γ, hγ, hm⟩ := hz
      rw [mul_one] at hm
      have : cpt X (baseFr X) z ∉ G'ᶜ := by
        rw [Set.mem_compl_iff, not_not, hmemG]; exact ⟨γ, hγ, hm⟩
      show φ _ = 0
      rw [hφdef, Set.indicator_of_notMem this]
    have hint := hH φ hφm hφB
    rw [hz, mul_zero] at hint
    have hae2 := (lintegral_eq_zero_iff (hφm.comp (GlobalTheory.PeterssonCompare.measurable_frameOf X))).1 hint
    filter_upwards [hae2] with g hg
    have hg' : φ (frameOf X g) = 0 := hg
    have hn : frameOf X g ∉ G'ᶜ := fun hm => by
      rw [hφdef, Set.indicator_of_mem hm] at hg'; exact one_ne_zero hg'
    rw [Set.mem_compl_iff, not_not, hmemG] at hn
    obtain ⟨γ, hγ, hm⟩ := hn
    obtain ⟨s, hs⟩ := GlobalTheory.PeterssonCompare.exists_translation X (X.Γ.inv_mem hγ)
    refine ⟨⟨s, (hΛ s).2 ⟨γ⁻¹, X.Γ.inv_mem hγ, hs⟩⟩, ?_⟩
    show frameOf X (s * g) ∈ S
    rw [← GlobalTheory.PeterssonCompare.lact_frameOf X hs]
    exact hm
  ·
    intro s t hst
    refine Disjoint.aedisjoint (Set.disjoint_left.2 fun g hgs hgt => hst ?_)
    obtain ⟨γ, hγ, e⟩ := (hΛ s).1 s.2
    obtain ⟨γ', hγ', e'⟩ := (hΛ t).1 t.2
    have h1 := (hmemT s g γ e).1 hgs
    have h2 := (hmemT t g γ' e').1 hgt
    obtain rfl := GlobalTheory.Unfold.unique_translate X hF hγ hγ' h1 h2
    exact Subtype.ext (GlobalTheory.PeterssonCompare.frameOf_injective X (e.symm.trans e'))

end GlobalTheory.FundFrames
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.exists_cutOperators_mirabolic_finitePlaces : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (n : ℕ) (h : Fin n → GA E (m + 1)) (c : Fin n → ℂ), (∀ i, h i ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∑ i, c i * W (p * h i) = (GlobalTheory.JSW.MirPatch.cell K q).indicator W p := by
  first
  | exact @GlobalTheory.JSW.MirPatch.cut_operators
  | exact GlobalTheory.JSW.MirPatch.cut_operators
  | (intros; apply GlobalTheory.JSW.MirPatch.cut_operators <;> assumption)
end

section

open NumberField


theorem _root_.GlobalTheory.T.invDifferentLatticeProductHermitian_isSelfDual : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ), cc ≠ ⊥ → GlobalTheory.NormExact.IsScale D cc r → Formalism.MainNotions.StandardLatticesGL3.SD D (GlobalTheory.VacRead.lsB D cc r a) := by
  first | exact @GlobalTheory.VacRead.lsB_selfDual | exact GlobalTheory.VacRead.lsB_selfDual | (intros; apply GlobalTheory.VacRead.lsB_selfDual <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.box_product_diagonal_functional_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)), ∃ φ₀ ∈ SB (κ → Fv F v), boxFun φ₀ φ₀ ∈ SB (κ ⊕ κ → Fv F v) ∧
    ∃ R R' : (κ → AF F) → ℂ, (∀ φ ∈ SB (κ → Fv F v), Rest (evFin F v) φ R ∧ Rest (evFin F v) φ R') ∧
      GlobalTheory.DiagForm.lDiag F κ (boxFun (tens (evFin F v) φ₀ R) (tens (evFin F v) φ₀ R')) ≠ 0 := by
  first | exact @GlobalTheory.DiagTens.lDiag_box_tens_ne | exact GlobalTheory.DiagTens.lDiag_box_tens_ne | (intros; apply GlobalTheory.DiagTens.lDiag_box_tens_ne <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.hasSum_diagonalIntegral_rationalHeisenberg : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ schA F (κ ⊕ κ), HasSum (fun uv : (κ → F) × (κ → F) => GlobalTheory.DiagForm.lDiag F κ (schr ψ (Sum.elim (fun i => algebraMap F (AF F) (uv.1 i)) 0, Sum.elim (fun i => algebraMap F (AF F) (uv.2 i)) 0) φ)) (c * thetaSum F φ) := by
  first | exact @GlobalTheory.ThetaRatSum.hasSum_lDiag_schr_rat | exact GlobalTheory.ThetaRatSum.hasSum_lDiag_schr_rat | (intros; apply GlobalTheory.ThetaRatSum.hasSum_lDiag_schr_rat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adjugateSubstLinearEquiv_symm_mem_nabla : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n : ℕ} (σ : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsLattice E M → ∀ (v : VV K fun τ => (σ τ).dual),
    v ∈ nabAtr emb (fun τ => (σ τ).dual) M → (GlobalTheory.FunObj.funEquiv σ).symm v ∈ nabAt emb σ M := by
  first | exact @GlobalTheory.funEquiv_symm_mem_nabAt_of_nabAtr | exact GlobalTheory.funEquiv_symm_mem_nabAt_of_nabAtr | (intros; apply GlobalTheory.funEquiv_symm_mem_nabAt_of_nabAtr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hermitianFockNorm_adjugateSubst_symm_le : ∀ {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → DomWeight n) (w : VV ℂ fun τ => (σ τ).dual),
    (pairK σ (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) ((GlobalTheory.FunObj.funEquiv σ).symm w) ((GlobalTheory.FunObj.funEquiv σ).symm w)).re ≤
      (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) w w).re := by
  first | exact @GlobalTheory.FunIsom.pairK_funEquiv_symm_le | exact GlobalTheory.FunIsom.pairK_funEquiv_symm_le | (intros; apply GlobalTheory.FunIsom.pairK_funEquiv_symm_le <;> assumption)
end
