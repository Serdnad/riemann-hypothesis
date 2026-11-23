module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle380
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle363
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle375
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle377
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle378
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009

@[expose] public section

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX.PushEq

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

instance eOsurjOneX : RingHomSurjective (D.nbr i w hw).eO.toRingHom := ⟨(D.nbr i w hw).eO.surjective⟩

instance eOinvOneX : RingHomInvPair (D.nbr i w hw).eO.toRingHom (D.nbr i w hw).eO.symm.toRingHom :=
  ⟨by ext; simp, by ext; simp⟩

instance eOinvOneX' : RingHomInvPair (D.nbr i w hw).eO.symm.toRingHom (D.nbr i w hw).eO.toRingHom :=
  ⟨by ext; simp, by ext; simp⟩

theorem vecL_add {a : ℕ} (u v : Fin a → Fin D.R.nV → KK D.nd i) :
    vecL i w hw (u + v) = vecL i w hw u + vecL i w hw v := by
  funext j m; simp [vecL]

theorem vecL_smul {a : ℕ} (c : D.nd.O i) (u : Fin a → Fin D.R.nV → KK D.nd i) :
    vecL i w hw (c • u) = (D.nbr i w hw).eO c • vecL i w hw u := by
  funext j m
  simp only [vecL, Pi.smul_apply, Algebra.smul_def, map_mul, Br.toLLK_alg]

theorem vecL_inj {a : ℕ} : Function.Injective (vecL (D := D) i w hw (a := a)) := by
  intro u v h
  funext j m
  exact (Br.toLLK (D.nbr i w hw)).injective (congrFun (congrFun h j) m)

section Y
variable {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))

def toY : ↥Y →ₛₗ[(D.nbr i w hw).eO.toRingHom] ↥(spanL i w hw Y) where
  toFun y := ⟨vecL i w hw y.1, Submodule.subset_span ⟨y.1, y.2, rfl⟩⟩
  map_add' u v := Subtype.ext (vecL_add i w hw u.1 v.1)
  map_smul' c u := Subtype.ext (vecL_smul i w hw c u.1)

theorem toY_inj : Function.Injective (toY i w hw Y) := fun u v h =>
  Subtype.ext (vecL_inj i w hw (congrArg (fun z : ↥(spanL i w hw Y) => (z : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw)) h))

theorem range_toY : LinearMap.range (toY i w hw Y) = latY i w hw Y := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    exact Submodule.subset_span ⟨y.1, y.2, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro u ⟨y, hy, hu⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hu⟩

def eY : ↥Y ≃ₛₗ[(D.nbr i w hw).eO.toRingHom] ↥(LinearMap.range (toY i w hw Y)) :=
  LinearEquiv.ofInjective _ (toY_inj i w hw Y)

variable {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
  (T : Submodule (Br.OLL D.nbr i w hw) ↥(spanL i w hw Y)) (hT : T = latY i w hw Y)

def phiL (φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k) :
    ↥T →ₗ[Br.OLL D.nbr i w hw] ((Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) :=
  ((Br.phi (D.nbr i w hw) k).comp φ).comp
    ((eY i w hw Y).symm.toLinearMap.comp
      (LinearEquiv.ofEq _ _ (hT.trans (range_toY i w hw Y).symm)).toLinearMap)

theorem phiL_eq (φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k) (v : ↥T) (y : ↥Y)
    (hv : (v : ↥(spanL i w hw Y)) = toY i w hw Y y) :
    phiL i w hw Y M T hT φ v = Br.phi (D.nbr i w hw) k (φ y) := by
  have e : (eY i w hw Y).symm (LinearEquiv.ofEq _ _ (hT.trans (range_toY i w hw Y).symm) v) = y :=
    (eY i w hw Y).symm_apply_eq.2 (Subtype.ext hv)
  change Br.phi (D.nbr i w hw) k (φ ((eY i w hw Y).symm (LinearEquiv.ofEq _ _ (hT.trans (range_toY i w hw Y).symm) v))) = _
  rw [e]

end Y

theorem phi_WKG {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (z : KOG (D.nd.O i) k) :
    Br.phi (D.nbr i w hw) k (WKG M (gl i w hw g) z) =
      repD (Br.locLat D.nbr i w hw M) g (Br.phi (D.nbr i w hw) k z) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change Submodule.Quotient.mk (Br.vecS (D.nbr i w hw) k ((matRep (mapM (toK D.nd i) M) _) u)) =
    Submodule.Quotient.mk ((matRep (Br.loc D.nbr i w hw M) g) (Br.vecS (D.nbr i w hw) k u))
  congr 1
  exact (loc_mulVec i w hw M g u).symm

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (E : Fin a → Fin D.R.nV → KK D.nd i)
    (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ), LY.T = latY i w hw Y →
    ∀ φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k, (∀ (γ : GE D.nd) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = WKG M γ (φ y)) →
    ∃ φ' : ↥LY.T →ₗ[Br.OLL D.nbr i w hw] ((Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    BlochKatoDuality.IsGMapD LY (Br.locLat D.nbr i w hw M) φ' ∧
    ∀ y : ↥(latticeCocycles LY), (y : Br.G D.nbr i w hw → (XG i w hw r Xs hr x Y hst).V) = yfun i w hw r Xs x Y E hE →
    BlochKatoDuality.pushD LY (Br.locLat D.nbr i w hw M) φ' y =
    fun g => Br.phi (D.nbr i w hw) k (φ ⟨_, hE (gl i w hw g)⟩) := by
  intro D i w hw r Xs hr a x Y hst E hE k M LY hT φ hφ
  refine ⟨phiL i w hw Y M LY.T hT φ, ?_, ?_⟩
  · intro g v
    obtain ⟨v, hv⟩ := v
    have hm : (show ↥(spanL i w hw Y) from v) ∈ LinearMap.range (toY i w hw Y) := by
      rw [range_toY, ← hT]; exact hv
    obtain ⟨y, rfl⟩ := hm
    have h1 : (show ↥(spanL i w hw Y) from (actT LY g ⟨toY i w hw Y y, hv⟩).1) =
        toY i w hw Y ⟨_, hst (gl i w hw g) y.1 y.2⟩ :=
      Subtype.ext (sumG_vecL i w hw r Xs hr x g y.1)
    refine (phiL_eq i w hw Y M LY.T hT φ _ _ h1).trans ?_
    refine Eq.trans ?_ (congrArg (repD (Br.locLat D.nbr i w hw M) g)
      (phiL_eq i w hw Y M LY.T hT φ ⟨_, hv⟩ y rfl).symm)
    rw [hφ]
    exact phi_WKG i w hw M g (φ y)
  · intro y hy
    funext g
    have h2 : (show ↥(spanL i w hw Y) from (evT LY g y).1) = toY i w hw Y ⟨_, hE (gl i w hw g)⟩ := by
      change (y : Br.G D.nbr i w hw → (XG i w hw r Xs hr x Y hst).V) g = _
      rw [hy]
      rfl
    exact phiL_eq i w hw Y M LY.T hT φ (evT LY g y) _ h2

end GlobalTheory.Pass.LocDual.OneX.PushEq

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.SplitAdelic

open TensorProduct GlobalTheory.InertUmax GlobalTheory.SplitLift

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem exists_imag (L : Type) [Field L] [NumberField L] [IsCMField L] :
    ∃ δ : L, IsCMField.complexConj L δ = -δ ∧ δ ≠ 0 := by
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  refine ⟨y - IsCMField.complexConj L y, ?_, sub_ne_zero.2 (Ne.symm hy)⟩
  rw [map_sub, IsCMField.complexConj_apply_apply]; ring

theorem linIndep_one_imag (δ : L) (hδ : IsCMField.complexConj L δ = -δ) (hδ0 : δ ≠ 0) :
    LinearIndependent L⁺ ![(1 : L), δ] := by
  rw [LinearIndependent.pair_iff]
  intro a t h
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
  have h2 := congrArg (IsCMField.complexConj L) h
  rw [map_add (f := _), map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hδ, map_zero] at h2
  have ht : algebraMap L⁺ L t * δ = 0 := by linear_combination (h - h2) / 2
  have ht' : algebraMap L⁺ L t = 0 := (mul_eq_zero.mp ht).resolve_right hδ0
  have hs : algebraMap L⁺ L a = 0 := by linear_combination (h + h2) / 2
  exact ⟨(algebraMap L⁺ L).injective (hs.trans (map_zero _).symm),
    (algebraMap L⁺ L).injective (ht'.trans (map_zero _).symm)⟩

theorem compAt_eq_zero_of_proj (s : SplitPlace L) (a : AL L) (h1 : s.proj a = 0)
    (h2 : s.proj (conjAL L a) = 0) : compAt L s.v a = 0 := by
  obtain ⟨δ, hδ, hδ0⟩ := exists_imag L
  let b : Module.Basis (Fin 2) L⁺ L := basisOfLinearIndependentOfCardEqFinrank
    (linIndep_one_imag δ hδ hδ0)
    (by rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = δ := by simp [b]
  obtain ⟨A, B, hAB⟩ := tensor_decomp b a
  rw [hb0, hb1] at hAB
  subst hAB
  rw [map_add (f := _), proj_tmul, proj_tmul, map_one, one_mul] at h1
  rw [map_add (f := _), conjAL_tmul, conjAL_tmul, map_one, hδ, map_add (f := _), proj_tmul, proj_tmul, map_one, one_mul,
    map_neg] at h2
  have hr : s.i δ ≠ 0 := (_root_.map_ne_zero _).2 hδ0
  have hA2 : 2 * A s.v = 0 := by linear_combination h1 + h2
  have hA : A s.v = 0 := (mul_eq_zero.mp hA2).resolve_left (two_ne s)
  have hB2 : 2 * (s.i δ * B s.v) = 0 := by linear_combination h1 - h2
  have hB : s.i δ * B s.v = 0 := (mul_eq_zero.mp hB2).resolve_left (two_ne s)
  have hB' : B s.v = 0 := (mul_eq_zero.mp hB).resolve_left hr
  rw [map_add (f := _), compAt_tmul, compAt_tmul, hA, hB', tmul_zero, tmul_zero, add_zero]

theorem loc_apply (s : SplitPlace L) {n : ℕ} (x : GAf L n) (i j : Fin n) :
    ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) _) i j =
      s.proj (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j) := rfl

theorem conj_entry {n : ℕ} (x : GAf L n) (i j : Fin n) :
    conjAL L (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hm := x.2
  simp only [GA, UGroup, Subgroup.mem_mk] at hm
  have h1 : (((x : GL (Fin n) (AL L))⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      conjT (conjAL L) (x : GL (Fin n) (AL L)) :=
    Units.inv_eq_of_mul_eq_one_right hm
  rw [InvMemClass.coe_inv, h1]
  simp [conjT]

theorem compAt_entries_eq (s : SplitPlace L) {n : ℕ} (x g : GAf L n) (h : s.loc n x = s.loc n g)
    (i j : Fin n) :
    compAt L s.v (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j) =
      compAt L s.v (((g : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j) := by
  rw [← sub_eq_zero, ← map_sub]
  apply compAt_eq_zero_of_proj
  · rw [map_sub, sub_eq_zero, ← loc_apply, ← loc_apply, h]
  · have hinv : s.loc n x⁻¹ = s.loc n g⁻¹ := by rw [map_inv, map_inv, h]
    rw [map_sub, map_sub, sub_eq_zero, conj_entry, conj_entry, ← loc_apply, ← loc_apply, hinv]

theorem mat_ext {n : ℕ} (M N : Matrix (Fin n) (Fin n) (AL L))
    (h : ∀ w, M.map (compAt L w) = N.map (compAt L w)) : M = N := by
  ext i j
  rw [← sub_eq_zero]
  apply eq_zero_of_compAt
  intro w
  rw [map_sub, sub_eq_zero]
  exact congrFun (congrFun (h w) i) j

theorem ext_of_loc (s : SplitPlace L) {n : ℕ} (x y : GAf L n) (hx : TrivOutside {s.v} x)
    (hy : TrivOutside {s.v} y) (h : s.loc n x = s.loc n y) : x = y := by
  apply Subtype.ext; apply Units.ext
  apply mat_ext
  intro w
  obtain rfl | hw := eq_or_ne w s.v
  · ext i j
    exact compAt_entries_eq s x y h i j
  · rw [hx w hw, hy w hw]

theorem mul_coe {n : ℕ} (x y : GAf L n) :
    (((x * y : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
        ((y : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := rfl

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L),
    (∀ g : GAf L n, ∃ x y : GAf L n, TrivOutside {s.v} x ∧ TrivOutside {s.v}ᶜ y ∧ g = x * y) ∧
    (∀ x y : GAf L n, TrivOutside {s.v} x → TrivOutside {s.v}ᶜ y → Commute x y) ∧
    (∀ A : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      ∃! x : GAf L n, TrivOutside {s.v} x ∧ s.loc n x = A) := by
  intro L _ _ _ n s
  refine ⟨fun g => ?_, fun x y hx hy => ?_, fun A => ?_⟩
  · obtain ⟨x, hx, hxg⟩ := exists_trivOutside_loc_eq n s (s.loc n g)
    refine ⟨x, x⁻¹ * g, hx, ?_, (mul_inv_cancel_left x g).symm⟩
    intro w hw
    have hw' : w = s.v := by simpa using hw
    subst hw'
    rw [mul_coe, Matrix.map_mul]
    have hg : (((g : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L s.v) =
        (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L s.v) := by
      ext i j
      exact (compAt_entries_eq s x g hxg i j).symm
    rw [hg, ← Matrix.map_mul, ← mul_coe, inv_mul_cancel]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · show x * y = y * x
    apply Subtype.ext; apply Units.ext
    change (((x * y : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (((y * x : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
    apply mat_ext
    intro w
    rw [mul_coe, mul_coe, Matrix.map_mul, Matrix.map_mul]
    obtain rfl | hw := eq_or_ne w s.v
    · rw [hy _ (by simp), mul_one, one_mul]
    · rw [hx w hw, mul_one, one_mul]
  · obtain ⟨x, hx, hxA⟩ := exists_trivOutside_loc_eq n s A
    exact ⟨x, ⟨hx, hxA⟩, fun y ⟨hy, hyA⟩ => ext_of_loc s y x hy hx (hyA.trans hxA.symm)⟩

end GlobalTheory.SplitAdelic
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedDdR

theorem ddR_finrank_le : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) ρ) ∧
        Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) ≤ Module.finrank ℚ_[l] ↥K.1 * Module.finrank ↥LL.1 V := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ
  haveI := LL.2
  exact GlobalTheory.Per.FontaineBound.ddR_finite_le (P.PD K) (GlobalTheory.Per.FontaineBound.isField_of_tied T) ρ

end GlobalTheory.Per.TiedDdR
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory

theorem finrank_le_of_subset_closure_range {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (J : E →+* PadicAlgCl l) (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hdense : (K : Set (PadicAlgCl l)) ⊆ closure (Set.range J)) :
    finrank ℚ_[l] ↥K ≤ finrank ℚ E := by
  classical
  let b := Module.finBasis ℚ E
  let S : Submodule ℚ_[l] (PadicAlgCl l) := Submodule.span ℚ_[l] (Set.range fun k => J (b k))
  have hfd : FiniteDimensional ℚ_[l] S := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hcl : IsClosed (S : Set (PadicAlgCl l)) := Submodule.closed_of_finiteDimensional S
  have hsub : Set.range J ⊆ S := by
    rintro _ ⟨x, rfl⟩

    rw [← b.sum_repr x, map_sum]
    refine S.sum_mem fun k _ => ?_
    have e : J (b.repr x k • b k) = ((b.repr x k : ℚ) : ℚ_[l]) • J (b k) := by
      rw [Rat.smul_def, map_mul, map_ratCast, Algebra.smul_def, map_ratCast]
    rw [e]
    exact S.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
  have hle : K.toSubalgebra.toSubmodule ≤ S := fun x hx => closure_minimal hsub hcl (hdense hx)
  have h1 : finrank ℚ_[l] ↥K.toSubalgebra.toSubmodule ≤ finrank ℚ_[l] S := Submodule.finrank_mono hle
  have h2 : finrank ℚ_[l] S ≤ finrank ℚ E := by
    have := finrank_range_le_card (R := ℚ_[l]) (fun k => J (b k))
    simpa [Set.finrank] using this
  exact le_trans h1 h2

theorem bridge_finrank_le (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 ≤ 4 * D.R.n := by
  have h1 : finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h2 := finrank_le_of_subset_closure_range
    ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) (D.nbr i w hw).Kw.1 (D.nbr i w hw).j_dense
  have h3 : D.R.n = D.R.ord := rfl
  have h4 : finrank ℚ D.host.E = 4 * D.R.n := by rw [h1, h3]
  exact le_trans h2 h4.le

end GlobalTheory
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

theorem _root_.GlobalTheory.T.isSplitPlace_of_over_type_prime : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k), IsSplitPl D.host w := by
  first | exact @GlobalTheory.TypeSplit.main | exact GlobalTheory.TypeSplit.main | (intros; apply GlobalTheory.TypeSplit.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

theorem _root_.GlobalTheory.T.qVal_pullback_mul_ramification_complete_dvr : ∀ (T T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (D : DegPre T.V) (D' : DegPre T'.V) (hD : IsPullDeg g D D') (ϖ : T.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g → Irreducible ϖ → Irreducible ϖ' → Associated (g ϖ) (ϖ' ^ e) → ∀ (y : D'.X) (n : ℤ), QVal D ϖ (hD.xe y) n → QVal D' ϖ' y (e * n) := by
  first | exact @GlobalTheory.QValPull.main | exact GlobalTheory.QValPull.main | (intros; apply GlobalTheory.QValPull.main <;> assumption)
end

section

namespace GlobalTheory.SpanMulInertiaEigenvalues

open NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem span_mul_mem {a b : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E}
    (ha : a ∈ Formalism.L2.SG.LocVol.OEv v) (hb : b ∈ Formalism.L2.SG.LocVol.OEv v) :
    a * b ∈ Formalism.L2.SG.LocVol.OEv v := by
  unfold Formalism.L2.SG.LocVol.OEv at *
  rw [SetLike.mem_coe] at *
  set S := (fun x : 𝓞 E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (x : E)) '' Set.univ
    with hS
  have hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    refine ⟨x * y, Set.mem_univ _, ?_⟩
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR _ (algebraMap (𝓞 E) E (x * y)) = _
    rw [map_mul, map_mul]
  have key : ∀ x ∈ S, ∀ y ∈ Submodule.span (v.adicCompletionIntegers F) S,
      x * y ∈ Submodule.span (v.adicCompletionIntegers F) S := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (hSmul x hx y hy)
    | zero => simp
    | add y z _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  induction ha using Submodule.span_induction with
  | mem x hx => exact key x hx b hb
  | zero => simp
  | add x z _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {a b : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E}, a ∈ Formalism.L2.SG.LocVol.OEv v → b ∈ Formalism.L2.SG.LocVol.OEv v → a * b ∈ Formalism.L2.SG.LocVol.OEv v :=
  fun v _ _ ha hb => span_mul_mem v ha hb

end GlobalTheory.SpanMulInertiaEigenvalues
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.lowJumps_and_cloud_in_windows_along_family : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ), Fm.x1 < x → ∀ (a : Fm.Ix x) (j : ℕ), 1 ≤ j → j ≤ (Fm.D x a).R.m →
    ∀ (up : Bool) (ρ : (Fm.D x a).what₂.Tau),
    (∀ z : ℤ, (z : ℚ) ∈ AdmissibleParameterJ.lowT (Fm.D x a) up j ρ →
      |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2| ≤ (Fm.L x a).etaSz ∧
      2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤
        |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2|) ∧
    ∃ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a), ∀ z : ℤ, (z : ℚ) ∈ AdmissibleParameterJ.cloudT (Fm.D x a) up j ρ →
      W0 ≤ (if up then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ≤
        W0 + (Fm.L x a).Sc + (Fm.L x a).etaSz + 1 := by
  first | exact @GlobalTheory.LetterWindows.lows_cloud_windows | exact GlobalTheory.LetterWindows.lows_cloud_windows | (intros; apply GlobalTheory.LetterWindows.lows_cloud_windows <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.decomposition_local_above : ∀ (D : D7) (L : SizeData₂ D) (ep : Bool), AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → AdmissibleParameterJ.CloudCentreDistance L → AdmissibleParameterJ.jcCondition L → AdmissibleParameterJ.JumpAbsoluteBound L → AdmissibleParameterJ.DualCloudSizes L → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1), ∀ M : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i), (M = WpO D.nd i ρ π ∨ M = T2O D.nd i ρ π) → (∃ U : Finset ℤ, U.card ≤ D.R.r ∧ (∀ u ∈ U, -((⌊2 * L.sc.b⌋₊ + 1 : ℕ) : ℤ) ≤ u ∧ u ≤ (⌊2 * L.sc.b⌋₊ + 1 : ℕ)) ∧ ∀ a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a → a ∈ U) ∧ ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ 0 := by
  first | exact @GlobalTheory.jumps_WpO_T2O_window | exact GlobalTheory.jumps_WpO_T2O_window | (intros; apply GlobalTheory.jumps_WpO_T2O_window <;> assumption)
end
