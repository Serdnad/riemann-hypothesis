module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormQuotientClassEqOfRelDifferences
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle006
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle158
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers TrivSqZeroExt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm
open GlobalTheory.CrysConn

namespace GlobalTheory.PDForm.Nbhd

open GlobalTheory.SmoothLift

attribute [local instance] opK isCentral_K isTower_K



theorem exists_retraction : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R), ∃ (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S)
    (r1 : ∀ T, (KK κ t).M1.obj (S.obj T) →+ (KK κ t).M1.obj T)
    (r2 : ∀ T, (KK κ t).M2.obj (S.obj T) →+ (KK κ t).M2.obj T)
    (r3 : ∀ T, (KK κ t).M3.obj (S.obj T) →+ (KK κ t).M3.obj T),
    ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r1 T' ((KK κ t).M1.map (S.map φ) x) = (KK κ t).M1.map φ (r1 T x)) ∧
      (∀ T x, r1 T ((KK κ t).M1.map (u.app T) x) = 0) ∧ (∀ T x, r1 T ((KK κ t).M1.map (v.app T) x) = x)) ∧
    ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r2 T' ((KK κ t).M2.map (S.map φ) x) = (KK κ t).M2.map φ (r2 T x)) ∧
      (∀ T x, r2 T ((KK κ t).M2.map (u.app T) x) = 0) ∧ (∀ T x, r2 T ((KK κ t).M2.map (v.app T) x) = x)) ∧
    (∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r3 T' ((KK κ t).M3.map (S.map φ) x) = (KK κ t).M3.map φ (r3 T x)) ∧
      (∀ T x, r3 T ((KK κ t).M3.map (u.app T) x) = 0) ∧ (∀ T x, r3 T ((KK κ t).M3.map (v.app T) x) = x) := by
  intro R _ I κ X t
  have hr : ∀ T : Thick κ t, ∀ x ∈ rel R T.δ, ∀ y, x * y ∈ rel R T.δ := fun T ↦ (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base.1 R T.B T.J T.δ).1
  have H := fun T : Thick κ t ↦ GlobalTheory.T.exists_formsMap_of_dividedPowerDerivation R T.B T.J T.δ (ER T) (nb T).J (nb T).δ (fstA T) (sndA T)
    (sndA_mul T) (sndA_algebraMap T) (fun n a ha ↦ sndA_dpow T n a ha)
  choose ρ ha hm h0 h1 hrel hone hdeg using H
  have natK : ∀ (j : ℕ) (T T' : Thick κ t) (φ : T ⟶ T') (x : K R (nb T).δ j),
      rK (nb T').δ (ha T') (hrel T') (hdeg T') j (km (SemiHom.of_algHom (nbAlg φ)) (nbF.map φ).dp j x) =
        km (SemiHom.of_algHom φ.φ) φ.dp j (rK (nb T).δ (ha T) (hrel T) (hdeg T) j x) := by
    intro j T T' φ x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx : (x : DR R (ER T)) ∈ ⋀[ER T]^j Ω[ER T⁄R] := x.2
    have hd := hdeg T j _ hx
    let y := hd.choose
    have hy : y ∈ ⋀[T.B]^j Ω[T.B⁄R] := hd.choose_spec.1
    have hρy : ρ T x - y ∈ rel R T.δ := hd.choose_spec.2
    rw [rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (y := ⟨y, hy⟩) hρy, km_mk]
    have e := add_mem (natAgree hr φ (ρ T) (ρ T') (ha T) (hm T) (h0 T) (h1 T) (ha T') (hm T') (h0 T') (h1 T') x)
      (mDR_mem_rel (SemiHom.of_algHom φ.φ) φ.dp hρy)
    rw [map_sub, sub_add_sub_cancel] at e
    exact rK_spec (nb T').δ (ha T') (hrel T') (hdeg T') (x := (SemiHom.of_algHom (nbAlg φ)).mOm j x)
      (y := (SemiHom.of_algHom φ.φ).mOm j ⟨y, hy⟩) e
  have uK : ∀ (j : ℕ), j ≠ 0 → ∀ (T : Thick κ t) (x : K R T.δ j),
      rK (nb T).δ (ha T) (hrel T) (hdeg T) j (km (SemiHom.of_algHom (inlMap T).φ) (inlMap T).dp j x) = 0 := by
    intro j hj T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := uAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) x
    rw [algebraMapInv_eq_zero hj x.2, map_zero] at e
    have e' : ρ T ((SemiHom.of_algHom (inlMap T).φ).mDR x) - ((0 : Om R T.B j) : DR R T.B) ∈ rel R T.δ := by
      rw [ZeroMemClass.coe_zero]; exact e
    exact (rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (x := (SemiHom.of_algHom (inlMap T).φ).mOm j x) e').trans
      (Submodule.Quotient.mk_zero _)
  have vK : ∀ (j : ℕ) (T : Thick κ t) (x : K R T.δ j),
      rK (nb T).δ (ha T) (hrel T) (hdeg T) j (km (SemiHom.of_algHom (difMap T).φ) (difMap T).dp j x) = x := by
    intro j T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (x := (SemiHom.of_algHom (difMap T).φ).mOm j x) (y := x)
      (vAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) x)
  refine ⟨nbF, uN, vN, fun T ↦ r1 (nb T).δ (ha T) (hrel T) (hone T), fun T ↦ rK (nb T).δ (ha T) (hrel T) (hdeg T) 2,
    fun T ↦ rK (nb T).δ (ha T) (hrel T) (hdeg T) 3, ⟨?_, ?_, ?_⟩, ⟨fun T T' φ x ↦ natK 2 T T' φ x,
      fun T x ↦ uK 2 (by norm_num) T x, fun T x ↦ vK 2 T x⟩, fun T T' φ x ↦ natK 3 T T' φ x,
      fun T x ↦ uK 3 (by norm_num) T x, fun T x ↦ vK 3 T x⟩
  · intro T T' φ x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hd := hone T x
    let ω := hd.choose
    have hω : ρ T (ι1 x) - ι1 ω ∈ rel R T.δ := hd.choose_spec
    have e := add_mem (natAgree hr φ (ρ T) (ρ T') (ha T) (hm T) (h0 T) (h1 T) (ha T') (hm T') (h0 T') (h1 T') (ι1 x))
      (mDR_mem_rel (SemiHom.of_algHom φ.φ) φ.dp hω)
    rw [map_sub, sub_add_sub_cancel, SemiHom.mDR_ι, SemiHom.mDR_ι] at e
    have l := divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := x) hω
    exact (divPowerCompatOneForm_retraction_spec (nb T').δ (ha T') (hrel T') (hone T') (x := (SemiHom.of_algHom (nbAlg φ)).m1 x)
      (ω := (SemiHom.of_algHom φ.φ).m1 ω) e).trans (congrArg (km1 (SemiHom.of_algHom φ.φ) φ.dp) l).symm
  · intro T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := uAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) (ι1 x)
    have z : ExteriorAlgebra.algebraMapInv (ι1 x) = 0 := by simp [ExteriorAlgebra.algebraMapInv]
    rw [z, map_zero, SemiHom.mDR_ι] at e
    have e' : ρ T (ι1 ((SemiHom.of_algHom (inlMap T).φ).m1 x)) - ι1 (0 : Ω[T.B⁄R]) ∈ rel R T.δ := by
      rw [map_zero]; exact e
    exact (divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := (SemiHom.of_algHom (inlMap T).φ).m1 x) e').trans
      (Submodule.Quotient.mk_zero _)
  · intro T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := vAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) (ι1 x)
    rw [SemiHom.mDR_ι] at e
    exact divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := (SemiHom.of_algHom (difMap T).φ).m1 x) (ω := x) e

end GlobalTheory.PDForm.Nbhd
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_semiAbelianMap_model_of_integralFramedPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y : FrPt Xo c T.Fr) (x : Sp T.V ⟶ Y.X), spMap (algebraMap T.V T.Fr) ≫ x = GlobalTheory.FlagMod.frX y ≫ Y.j → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t y.x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), ∃ (ψ : SABMap G Y.t x) (ρ : t'.G.left ⟶ Y.oF.t.G.left), ρ ≫ Y.m0.toSABMap.φ = m1.φ ∧ ρ ≫ Y.oF.t.G.hom = t'.G.hom ≫ GlobalTheory.FlagMod.frX y ∧ ρ ≫ Y.m.φ = m2.φ ≫ ψ.φ := by
  first | exact @GlobalTheory.exists_sabMap_model_of_integral_frPt | exact GlobalTheory.exists_sabMap_model_of_integral_frPt | (intros; apply GlobalTheory.exists_sabMap_model_of_integral_frPt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isEigenvector_integral_of_tangentPullback_mem : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (x : Sp T.V ⟶ Y.X) (x' : Sp T.Fr ⟶ Y.X) (e : spMap (algebraMap T.V T.Fr) ≫ x = x'), Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) → ∀ (G : SAB H (Sp T.V)) (ψ : SABMap G Y.t x) (τ : E →+* ℂ) (w : epsOver T.V T.V ⟶ G.G) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ → GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e v ∈ GlobalTheory.FlagMod.eigLie c x' τ → IsEigV c io G τ w := by
  first | exact @GlobalTheory.TanEigInt.isEigV_of_tanPull_mem | exact GlobalTheory.TanEigInt.isEigV_of_tanPull_mem | (intros; apply GlobalTheory.TanEigInt.isEigV_of_tanPull_mem <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulIsogeny

theorem bcMap_natCast_smul_id (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : AbVar K) (n : ℕ) :
    bcMap L ((n : ℤ) • 𝟙 A) = (n : ℤ) • 𝟙 (baseChange L A) := by
  apply Subtype.ext
  simp only [bcMap, mk_hom, zsmul_hom, id_hom, zpow_natCast]
  exact GlobalTheory.MulFiniteFlat.pullback_map_mulA _ A.X n

theorem natCast_algClosed (k : Type) [Field k] [IsAlgClosed k] (A : AbVar k) (n : ℕ) (hn : n ≠ 0) :
    IsIsogeny ((n : ℤ) • 𝟙 A) ∧ deg ((n : ℤ) • 𝟙 A) = n ^ (2 * A.dim) := by
  have e : ((n : ℤ) • 𝟙 A).hom = (𝟙 A.X ^ n : A.X ⟶ A.X) := by
    rw [zsmul_hom, id_hom, zpow_natCast]
  obtain ⟨hfin, hfl⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul (Sp k) A.X A.ab n (Nat.one_le_iff_ne_zero.2 hn)
  have hmon : IsMonHom (𝟙 A.X ^ n : A.X ⟶ A.X) := e ▸ inferInstanceAs (IsMonHom ((n : ℤ) • 𝟙 A).hom)
  have hsurj : Surjective (𝟙 A.X ^ n : A.X ⟶ A.X).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k A.X A.ab _ inferInstance hfin).2
  have hiso : IsIsogeny ((n : ℤ) • 𝟙 A) := by
    unfold IsIsogeny
    rw [e]
    exact ⟨hfin, hsurj⟩
  refine ⟨hiso, ?_⟩
  unfold deg
  rw [if_pos hiso, e]
  exact GlobalTheory.UU.MulDegree.finrank_mul_eq k A.X A.dim n A.ab A.smooth hn _

theorem natCast (K : Type) [Field K] (A : AbVar K) (n : ℕ) (hn : n ≠ 0) :
    IsIsogeny ((n : ℤ) • 𝟙 A) ∧ deg ((n : ℤ) • 𝟙 A) = n ^ (2 * A.dim) := by
  obtain ⟨h1, h2⟩ := natCast_algClosed (AlgebraicClosure K) (baseChange (AlgebraicClosure K) A) n hn
  obtain ⟨e1, e2⟩ := GlobalTheory.T.isogeny_baseChange_iff_and_degree_eq K (AlgebraicClosure K) A A ((n : ℤ) • 𝟙 A)
  rw [bcMap_natCast_smul_id] at e1 e2
  exact ⟨e1.1 h1, e2.symm.trans h2⟩

theorem neg_one (K : Type) [Field K] (A : AbVar K) : IsIsogeny (-𝟙 A) ∧ deg (-𝟙 A) = 1 := by
  have hsq : (-𝟙 A) ≫ (-𝟙 A) = 𝟙 A := by simp
  have hsq' : (-𝟙 A).hom.left ≫ (-𝟙 A).hom.left = 𝟙 A.X.left := by
    rw [← Over.comp_left, ← comp_hom, hsq, id_hom, Over.id_left]
  haveI : IsIso (-𝟙 A).hom.left := ⟨⟨(-𝟙 A).hom.left, hsq', hsq'⟩⟩
  have hiso : IsIsogeny (-𝟙 A) := ⟨inferInstance, inferInstance⟩
  refine ⟨hiso, ?_⟩
  unfold deg
  rw [if_pos hiso]
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso _) _

theorem mul_isogeny : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℤ), n ≠ 0 → IsIsogeny (n • 𝟙 A) ∧ deg (n • 𝟙 A) = n.natAbs ^ (2 * A.dim) := by
  intro K _ A n hn
  rcases Int.natAbs_eq n with h | h
  · rw [h]
    exact natCast K A n.natAbs (Int.natAbs_ne_zero.2 hn)
  · have e : n • 𝟙 A = ((n.natAbs : ℤ) • 𝟙 A) ≫ (-𝟙 A) := by
      rw [Preadditive.comp_neg, Category.comp_id, ← neg_smul, ← h]
    obtain ⟨h1, h2⟩ := natCast K A n.natAbs (Int.natAbs_ne_zero.2 hn)
    obtain ⟨h3, h4⟩ := neg_one K A
    obtain ⟨h5, h6⟩ := GlobalTheory.T.isogeny_comp_and_degree_mul K A A A _ _ h1 h3
    rw [e]
    exact ⟨h5, by rw [h6, h2, h4, _root_.mul_one]⟩

end GlobalTheory.MulIsogeny
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.localRing_graph_generic_point_of_injective : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  Function.Injective π → (∀ g : K, ∃ a b : R, (b : K) ≠ 0 ∧ g * b = a) →
  IsLocModel (algebraMap ℂ K) R → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → 1 ≤ k →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin k → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) = (q : L) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  first | exact @GlobalTheory.FieldPair.localRing_graph_of_injective | exact GlobalTheory.FieldPair.localRing_graph_of_injective | (intros; apply GlobalTheory.FieldPair.localRing_graph_of_injective <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.squareFlip_reaches_localQuotient_classes : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t)
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v, w.under (𝓞 D.host.F) = v → ∀ φ₀ ∈ GlobalTheory.WeilM.SB _,
    ∃ n Φ φ₂ g φ₃, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧ IsLocFn W B t e Γ w v (flipAt W t i j w n Φ) φ₂ ∧
      φ₃ ∈ GlobalTheory.WeilM.SB _ ∧ Acts (evFin D.host.F v) (om (1, blkU _ _ e h.JWW g)) φ₂ φ₃ ∧ Rf.p v φ₃ = Rf.p v φ₀ := by
  first | exact @GlobalTheory.SquareFlipReach.flip_reach | exact GlobalTheory.SquareFlipReach.flip_reach | (intros; apply GlobalTheory.SquareFlipReach.flip_reach <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField

namespace GlobalTheory.BigTop.Fun.ThbTie

theorem sqRank_half {D : D7} (ij : Sq D) : sqRank D ij / 2 = GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by
  unfold sqRank GlobalTheory.FunObj.SqNum.halfRank GlobalTheory.ChiGrid.rankV
  congr 1
  ring

theorem htLe_nonneg {K : Type} [Field K] [NumberField K] [StarRing K] {g : Formalism.PairingDivisionLocalBalance.Pl K → ℤ} {z : K} {B : ℝ}
    (h : Formalism.PairingDivisionLocalBalance.HtLe g z B) : 0 ≤ B :=
  (finsum_nonneg fun w => mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (abs_nonneg _)).trans h.2

theorem htLe_one_zero {K : Type} [Field K] [NumberField K] [StarRing K] {B : ℝ} (hB : 0 ≤ B) :
    Formalism.PairingDivisionLocalBalance.HtLe (fun _ => (0 : ℤ)) (1 : K) B := by
  have e : (fun w : Formalism.PairingDivisionLocalBalance.Pl K => Formalism.DivisionValues.lw w * |((Formalism.DivisionValues.vw w (1 : K) + 0 : ℤ) : ℝ)|) = fun _ => 0 := by
    funext w
    simp [Formalism.DivisionValues.ValuationRepresentative.vw_one]
  refine ⟨?_, ?_⟩
  · rw [e]
    simp
  · rw [e, finsum_zero]
    exact hB

end GlobalTheory.BigTop.Fun.ThbTie


end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop

namespace GlobalTheory.BigTop.Fun

theorem halfRank_eq_sqRank_div (D : D7) (ij : Sq D) :
    GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 = sqRank D ij / 2 := by
  unfold GlobalTheory.FunObj.SqNum.halfRank sqRank
  congr 1
  simp only [GlobalTheory.ChiGrid.rankV]
  ring

end GlobalTheory.BigTop.Fun

end
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)

noncomputable section

namespace GlobalTheory.ThmAUpper

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem xiH_base : p.R.toRealDat.toLevCh.xiH p.P.A3.A.μ0 = 1 := by
  have h0 : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 := by
    rw [← p.P.div.tup.mu0]; exact p.tupT_tup _
  rw [← h0, p.tupXi _ (Or.inl rfl), p.Tp.trueColumnChoices_heckeChar_reference_eq_one]

theorem xiH_twisted (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hw : p.R.mu w ≠ p.P.A3.A.μ0) :
    TwistedAt D (D.plEq.symm w) ∧ p.R.toRealDat.toLevCh.xiH (p.R.mu w) =
      p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w)) * p.Tp.psi (D.plEq.symm w) := by
  have h0 : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 := by
    rw [← p.P.div.tup.mu0]; exact p.tupT_tup _
  have e1 : p.R.mu w = p.tupT (D.what₂.muAt (D.plEq.symm w)) := by rw [p.tupAt]; simp
  have htw : D.what₂.muAt (D.plEq.symm w) ≠ D.what₂.mu0 := fun e => hw (by rw [e1, e, h0])
  have hmt : D.what₂.muAt (D.plEq.symm w) = D.what₂.muTw (D.plEq.symm w) := (D.what₂.muAt_or _).resolve_left htw
  refine ⟨htw, ?_⟩
  rw [e1, p.tupXi _ (Or.inr ⟨_, rfl⟩), hmt, p.Tp.xi_tw]

end

theorem resChar_eq {D : D7} (w : D.what₂.places.Pl) {l : ℕ} (hl : l.Prime)
    (h : ((l : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal) : D.what₂.places.resChar w = l := by
  by_contra hq
  have hq' := D.what₂.places.resChar_prime w
  have hnot : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal := by
    intro hin
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (l : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq' hl).2 hq)
    apply (D.plEq w).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 D.what₂.LL) = (a : 𝓞 D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) +
        (b : 𝓞 D.what₂.LL) * ((l : ℕ) : 𝓞 D.what₂.LL) := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hab.symm
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hin) (Ideal.mul_mem_left _ _ h)
  have h1 : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hnot
  have h2 := D.what₂.places.val_resChar w
  rw [D.val_eq w _ (Nat.cast_ne_zero.2 hq'.ne_zero)] at h2
  have h3 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℕ) := by
    exact_mod_cast h2
  have h4 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = 0 := by
    unfold vAdd
    rw [show ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) =
      algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) by simp, h1]
    simp
  have := D.what₂.places.ramIdx_pos w
  omega

theorem nuH_twisted {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) {CF : ℝ} (G : Grid p CF) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hw : p.R.mu w ≠ p.P.A3.A.μ0)
    (i j : Fin D.R.m) : nuH G (p.R.mu w) i j = nuH G p.P.A3.A.μ0 i j *
      p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w)) * p.Tp.psi (D.plEq.symm w) := by
  unfold nuH
  rw [(xiH_twisted p w hw).2, xiH_base p, mul_one, div_eq_mul_inv, div_eq_mul_inv]
  ac_rfl

end GlobalTheory.ThmAUpper
end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.arithmeticHilbertSamuelBound : Quoted → GeoBound := by
  first | exact @GlobalTheory.HSShort.geoBound_of_quoted' | exact GlobalTheory.HSShort.geoBound_of_quoted' | (intros; apply GlobalTheory.HSShort.geoBound_of_quoted' <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockJet_vacuum_eq_const_mul_periodScaledJet : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D (G.pT (.top t j)).rank (G.pS (.top t j)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.top t j) f (MvPolynomial.monomial k 1) 0 = c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  first | exact @GlobalTheory.FunObj.TopJet.fockIn_vacuum_eq | exact GlobalTheory.FunObj.TopJet.fockIn_vacuum_eq | (intros; apply GlobalTheory.FunObj.TopJet.fockIn_vacuum_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fockJets_unitVacuum_eq_unit_mul_periodJets : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO ψ θ S T sS sT (colLat frS : Set _) (colLat frT : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ)) (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 = c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  first | exact @GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets | exact GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets | (intros; apply GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets <;> assumption)
end
