module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle032
public import Mathlib.RingTheory.Flat.TorsionFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompOfIsMonHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3331
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrder
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle089
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3330
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2508
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle023
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusCharOfLabelOrthogonalDividing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMembersLatticesIsoOfSpecializesDvr
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.OActDeg

def endHom {k : Type} [Field k] (X : GlobalTheory.AV.AbVar k) (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) X.X) :
    𝓞 F →+* CategoryTheory.End X where
  toFun c := End.of (GlobalTheory.AV.AbVar.Hom.mk (A := X) (B := X) (ρ.act c) (h := ρ.hom c))
  map_one' := by
    refine End.ext (Subtype.ext ?_)
    exact ρ.one
  map_mul' a b := by
    refine End.ext (Subtype.ext ?_)
    change ρ.act (a * b) = ρ.act b ≫ ρ.act a
    rw [mul_comm, ρ.mul]
  map_zero' := by
    refine End.ext (Subtype.ext ?_)
    change ρ.act 0 = 1
    have h := ρ.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  map_add' a b := by
    refine End.ext (Subtype.ext ?_)
    exact ρ.add a b

open Polynomial GlobalTheory.AV.AbVar in
theorem isFinite_and_finrank_eq_norm_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) A) (l d : ℕ), l.Prime → (l : k) ≠ 0 →
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ l = 1} = l ^ (d * Module.finrank ℚ F) →
    ∀ c : 𝓞 F, c ≠ 0 → IsFinite (ρ.act c).left ∧
      (ρ.act c).left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) =
        (Algebra.norm ℤ c).natAbs ^ d := by
  intro k _ _ A _ hA F _ _ ρ l d hl hl0 hcard c hc
  let X : GlobalTheory.AV.AbVar k := GlobalTheory.TateHondaBridge.toAbVar A hA
  have h2 := GlobalTheory.abMulN_holds k A X.dim l hA X.smooth hl0
  rw [hcard] at h2
  have hdim : 2 * X.dim = d * Module.finrank ℚ F :=
    (Nat.pow_right_injective hl.two_le h2).symm
  let actionHom := endHom X F ρ
  let f := actionHom c
  let m := minpoly ℤ c
  have hi : IsIntegral ℤ c := NumberField.RingOfIntegers.isIntegral c
  have hm : m.Monic := minpoly.monic hi
  have hp : Prime m := (minpoly.irreducible hi).prime
  have hf : aeval f m = 0 := by
    have h := Polynomial.hom_eval₂ m (algebraMap ℤ (𝓞 F)) actionHom c
    rw [← aeval_def, show aeval c m = 0 from minpoly.aeval ℤ c, map_zero,
      Subsingleton.elim (actionHom.comp (algebraMap ℤ (𝓞 F))) (algebraMap ℤ _), ← aeval_def] at h
    exact h.symm
  have ⟨e, he, hdeg⟩ : ∃ e : ℕ, e * m.natDegree = 2 * X.dim ∧
      (deg f.asHom : ℤ) = m.coeff 0 ^ e := by
    have : Fact l.Prime := ⟨hl⟩
    obtain ⟨-, -, -, hfin, hrank⟩ := tl_free_finrank k l hl0 X
    have hchar (g : End X) :
        (charpoly g).map (algebraMap ℤ ℚ_[l]) = (vmap l g.asHom).charpoly := by
      obtain ⟨⟨hmonic, hdegree, heval⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec k X g
      have h := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate
        k l hl0 X g ((charpoly g).map (algebraMap ℤ ℚ)) (hmonic.map _)
        (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hdegree])
        (fun n => by simpa using congrArg (algebraMap ℤ ℚ) (heval n))
      rw [← h, Polynomial.map_map,
        show (algebraMap ℚ ℚ_[l]).comp (algebraMap ℤ ℚ) = algebraMap ℤ ℚ_[l] from Subsingleton.elim _ _]
    have hdet : LinearMap.det (vmap l f.asHom) = (deg f.asHom : ℚ_[l]) := by
      have hneg : (-f).asHom = -f.asHom := map_neg (End.addEquiv (X := X)) f
      have hv : vmap l f.asHom = (-1 : ℚ_[l]) • vmap l (-f).asHom := by
        simp only [hneg, vmap, map_neg, LinearMap.baseChange_neg, neg_one_smul, neg_neg]
      have hev := (GlobalTheory.T.abelianVarietyEndCharpoly_spec k X (-f)).1.2.2 0
      rw [Int.cast_zero, zero_sub, neg_neg] at hev
      rw [hv, LinearMap.det_smul, LinearMap.det_eq_sign_charpoly_coeff, ← hchar (-f),
        Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, hev, hrank, pow_mul, neg_one_sq, one_pow]
      simp
    have hinj : Function.Injective (algebraMap ℤ ℚ_[l]) := RingHom.injective_int _
    let ψ : End X →+* Module.End ℚ_[l] (Vl l X) :=
      (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l X)).toRingHom.comp (tend l X)
    have hT : aeval (vmap l f.asHom) m = 0 := by
      change aeval (ψ f) m = 0
      have h := Polynomial.hom_eval₂ m (algebraMap ℤ (End X)) ψ f
      rw [← aeval_def, hf, map_zero,
        Subsingleton.elim (ψ.comp (algebraMap ℤ (End X))) (algebraMap ℤ _), ← aeval_def] at h
      exact h.symm
    have hdvd := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank (vmap l f.asHom) (m.map (algebraMap ℤ ℚ_[l]))
      (by rw [aeval_map_algebraMap]; exact hT)
    rw [← hchar f, ← Polynomial.map_pow] at hdvd
    obtain ⟨⟨hmonic, hdegree, -⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec k X f
    rw [Polynomial.map_dvd_map _ hinj hmonic] at hdvd
    obtain ⟨i, -, hassociated⟩ := (dvd_prime_pow hp _).1 hdvd
    have hpow : charpoly f = m ^ i := Polynomial.eq_of_monic_of_associated hmonic (hm.pow i) hassociated
    refine ⟨i, ?_, ?_⟩
    · rw [← hdegree, hpow, hm.natDegree_pow]
    · have h := LinearMap.det_eq_sign_charpoly_coeff (vmap l f.asHom)
      rw [hdet, ← hchar f, coeff_map, hrank, pow_mul, neg_one_sq, one_pow, _root_.one_mul, hpow,
        coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero] at h
      apply Int.cast_injective (α := ℚ_[l])
      rw [Int.cast_natCast, h, eq_intCast, Int.cast_pow]
  obtain ⟨r, hr, hnorm⟩ := norm_natAbs_eq_minpoly_coeff_zero_pow c
  have hpos : 0 < m.natDegree := minpoly.natDegree_pos hi
  have her : e = d * r := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [he, hdim, ← hr, _root_.mul_assoc]
  have hdeg' : deg f.asHom = (m.coeff 0).natAbs ^ e := by
    have h := congrArg Int.natAbs hdeg
    rwa [Int.natAbs_natCast, Int.natAbs_pow] at h
  have hval : deg f.asHom = (Algebra.norm ℤ c).natAbs ^ d := by
    rw [hdeg', hnorm, ← pow_mul, her, mul_comm]
  have hiso : IsIsogeny f.asHom := by
    classical
    by_contra h
    have hzero : deg f.asHom = 0 := by rw [deg, ite_eq_right h]
    rw [hdeg'] at hzero
    exact minpoly_int_coeff_zero_ne_zero c hc (Int.natAbs_eq_zero.1 (pow_eq_zero_iff'.1 hzero).1)
  refine ⟨hiso.1, ?_⟩
  classical
  rw [← hval]
  unfold GlobalTheory.AV.AbVar.deg
  rw [ite_eq_left hiso]
  rfl

end GlobalTheory.AV.OActDeg

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.endCharpoly_tate_det_degree_trace : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A), (∀ [Module.Finite ℚ_[l] (Vl l A)], (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l (A := A) (B := A) f.asHom).charpoly) ∧ (∀ [Module.Free ℤ_[l] (Tl l A)] [Module.Finite ℤ_[l] (Tl l A)], (charpoly f).map (algebraMap ℤ ℤ_[l]) = (tend l A f).charpoly) ∧ LinearMap.det (vmap l (A := A) (B := A) f.asHom) = (deg (A := A) (B := A) f.asHom : ℚ_[l]) ∧ LinearMap.trace ℚ_[l] _ (vmap l (A := A) (B := A) f.asHom) = (trace f : ℚ_[l]) := by
  intro K _ l _ hl A f
  have hcharpoly [Module.Finite ℚ_[l] (Vl l A)] (g : End A) :
      (charpoly g).map (algebraMap ℤ ℚ_[l]) = (vmap l g.asHom).charpoly := by
    obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A g
    have h := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate
      K l hl A g ((charpoly g).map (algebraMap ℤ ℚ)) (hm.map _)
      (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hd])
      (fun n => by simpa using congrArg (algebraMap ℤ ℚ) (hev n))
    rw [← h, Polynomial.map_map, show (algebraMap ℚ ℚ_[l]).comp (algebraMap ℤ ℚ) =
      algebraMap ℤ ℚ_[l] from Subsingleton.elim _ _]
  refine ⟨fun {_} => hcharpoly f, fun {_ _} => ?_, ?_, ?_⟩
  · apply Polynomial.map_injective (algebraMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [Polynomial.map_map, ← LinearMap.charpoly_baseChange,
      show (algebraMap ℤ_[l] ℚ_[l]).comp (algebraMap ℤ ℤ_[l]) =
        algebraMap ℤ ℚ_[l] from Subsingleton.elim _ _]
    exact hcharpoly f
  · obtain ⟨-, -, -, hfin, hrk⟩ := tl_free_finrank K l hl A
    have hneg : vmap l f.asHom = (-1 : ℚ_[l]) • vmap l (-f).asHom := by
      simp [vmap, LinearMap.baseChange_neg]
    have hev : (charpoly (-f)).eval 0 = (deg f.asHom : ℤ) := by
      simpa using (GlobalTheory.T.abelianVarietyEndCharpoly_spec K A (-f)).1.2.2 0
    rw [hneg, LinearMap.det_smul, LinearMap.det_eq_sign_charpoly_coeff, ← hcharpoly (-f),
      Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, hev, hrk, pow_mul, neg_one_sq, one_pow]
    simp
  · obtain ⟨-, -, -, hfin, -⟩ := tl_free_finrank K l hl A
    rw [linTrace_eq_neg_nextCoeff, ← hcharpoly f,
      Polynomial.nextCoeff_map (RingHom.injective_int (algebraMap ℤ ℚ_[l])), trace]
    simp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory.UPoinc.TraitCompare

theorem exists_trait_lattice_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) → (∀ z : Y.Z, r z ∈ Set.range C.i → z ∈ abLocus out.G) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ r = T.y ≫ C.i → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) → ∀ (x : Y.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : Y.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ out.G.left), IsSemiAbelian G → IsGrpPullback G out.G (spMap j ≫ Y.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (out.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ Y.Z.fromSpecStalk x) ⁻¹' abLocus out.G)) → ∀ m : 𝓞 E → (D.toPre.X →+ D.toPre.X), (∀ a, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧ EndChar U fR (m a)) → ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i → ∃ ρT : D.toPre.X ≃+ T.P.D.toPre.X, (∀ y s, PsiCoord D.toPre y s → 0 ≤ T.be (ρT y) (ρT y) ∧ Associated (ψ s ^ 2) (T.ϖ ^ (T.be (ρT y) (ρT y)).toNat)) ∧ ∀ a y, ρT (m a y) = H.bar a • ρT y := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r _hOver _hpt f _hf habl hT x R _ _ _ j hR _hj G _ _ gm hG hgm D A U hLB
    hPsi m hm T ψ hψ hTy
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI : CharZero T.V := T.cdvr.2.2
  have hTV : GlobalTheory.Mum.Base T.V := ⟨GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR T.cdvr, inferInstance⟩
  have hξT : spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x = spMap ψ ≫ (spMap j ≫ Y.Z.fromSpecStalk x) := by
    rw [spMap_comp, Category.assoc]
  have hid : spMap (RingHom.id T.V) = 𝟙 _ := by
    simp [spMap]
  obtain ⟨tW, mW, PW, e, he⟩ := GlobalTheory.UPoinc.TraitPull.exists_pull_unif E H Dw l Xo c T T.V hTV inferInstance (RingHom.id T.V)
    (fun _ _ h => h) inferInstance
  obtain ⟨βT, hβT, hLT, hactT⟩ := hT T _ hTy
  have hβ' : IsGrpPullback tW.G out.G (spMap ψ ≫ (spMap j ≫ Y.Z.fromSpecStalk x)) (mW.φ ≫ βT) :=
    (mW.cart.comp hβT).congr (by rw [hid, Category.id_comp, hξT]) rfl
  have w : (mW.φ ≫ βT) ≫ out.G.hom = (tW.G.hom ≫ spMap ψ) ≫ (spMap j ≫ Y.Z.fromSpecStalk x) := by
    rw [hβ'.1.w, Category.assoc]
  let β : tW.G.left ⟶ G.left := hgm.1.lift (mW.φ ≫ βT) (tW.G.hom ≫ spMap ψ) w
  have hβgm : β ≫ gm = mW.φ ≫ βT := hgm.1.lift_fst _ _ _
  have hβG : β ≫ G.hom = tW.G.hom ≫ spMap ψ := hgm.1.lift_snd _ _ _
  have hβ : IsGrpPullback tW.G G (spMap ψ) β := hgm.cancel (by rw [hβgm]; exact hβ') hβG
  have hLBW : LBIso PW.U.LG.L (U.LG.L.pull β) := by
    rw [PW.bundle]
    exact LBIso.trans tW.PP.isLB (LB.isLB_pull out.L.isLB _) (LB.isLB_pull U.LG.isLB _)
      (LBIso.trans tW.PP.isLB (LB.isLB_pull T.t.PP.isLB _) (LB.isLB_pull out.L.isLB _)
        (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap mW) (GlobalTheory.LN.GenericPoint.lbIso_pull hLT mW.φ rfl))
      (GlobalTheory.LN.GenericPoint.lbIso_pull hLB β hβgm.symm).symm

  have hab : ∀ z, (spMap j ≫ Y.Z.fromSpecStalk x) z ∈ abLocus out.G ↔ z ∈ abLocus G :=
    abLocus_pullback abLocusOne out.semi hgm.1
  have hTy' : jK T.V ≫ (spMap ψ ≫ (spMap j ≫ Y.Z.fromSpecStalk x)) ≫ r = T.y ≫ C.i := by
    rw [← hξT]; exact hTy
  have hgen : spMap ψ (genericPoint (Sp T.V)) ∈
      (⟨abLocus G, GlobalTheory.AbLocusOpen.isOpen_abLocus_local G hG⟩ : (Sp R).Opens) := by
    show _ ∈ abLocus G
    rw [← hab]
    apply habl
    let pt : Sp (FractionRing T.V) := ⟨⊥, Ideal.isPrime_bot⟩
    have hpt : jK T.V pt = genericPoint (Sp T.V) := by
      rw [genericPoint_eq_bot_of_affine]
      refine PrimeSpectrum.ext (Ideal.ext fun s => ?_)
      change algebraMap T.V (FractionRing T.V) s ∈ (⊥ : Ideal (FractionRing T.V)) ↔ s ∈ (⊥ : Ideal T.V)
      rw [Ideal.mem_bot, Ideal.mem_bot, IsFractionRing.to_map_eq_zero_iff]
    rw [← hpt]
    exact ⟨T.y pt, (congrArg (fun g : Sp (FractionRing T.V) ⟶ C.Z => g pt) hTy').symm⟩

  have hPsi' : ∀ y, PsiUnitOn D.toPre y (⟨abLocus G, GlobalTheory.AbLocusOpen.isOpen_abLocus_local G hG⟩ : (Sp R).Opens) := by
    intro y
    have hs : (⇑(spMap j ≫ Y.Z.fromSpecStalk x) ⁻¹' abLocus out.G) = abLocus G := Set.ext hab
    have := hPsi y
    rw [hs] at this
    exact this

  let bc : tW.G ≅ (Over.pullback (specOf ψ)).obj G :=
    Over.isoMk hβ.1.isoPullback (by simp)
  have hbcβ : β = bc.hom.left ≫ pullback.fst G.hom (specOf ψ) := by
    simp [bc]
  have hbc : IsMonHom bc.hom := GlobalTheory.Mum.isMonHom_of_isGrpPullback_fst bc (hβ.congr rfl hbcβ)
  obtain ⟨D₂, A₂, hD, U₂, hU⟩ := GlobalTheory.Mum.unif_baseChange_of_psiUnitOn R hR D A G hG U T.V hTV.1 ψ hψ _ hPsi' hgen tW.G bc hbc
  obtain ⟨hL₁, hC₁, hE₁⟩ := PullUnif.main R hR G hG D A U T.V hTV tW.G tW.semi D₂ A₂ U₂ ψ β hψ bc hbc hbcβ hD hU

  have hid' : IsGrpPullback tW.G tW.G (spMap (RingHom.id T.V)) (𝟙 tW.G.left) :=
    GlobalTheory.LN.SelfCmp.isGrpPullback_of_eq_id tW.G hid
  obtain ⟨ρ, hρ⟩ := GlobalTheory.SpreadTrait.exists_spread T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A PW.U
    (RingHom.id T.V) (𝟙 _) hid'
  have hρs := GlobalTheory.TorusOntoSpread.restrict_surjective T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A
    PW.U (RingHom.id T.V) (𝟙 _) hid' ρ hρ
  have hρT := GlobalTheory.SpreadTorMatch.torMatch_of_spread T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A
    PW.U (RingHom.id T.V) (𝟙 _) hid' ρ hρ
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.SpreadTrait.exists_spread T.V hTV tW.G tW.semi PW.D PW.A PW.U T.V hTV tW.G tW.semi D₂ A₂ U₂
    (RingHom.id T.V) (𝟙 _) hid'
  have hρ's := GlobalTheory.TorusOntoSpread.restrict_surjective T.V hTV tW.G tW.semi PW.D PW.A PW.U T.V hTV tW.G tW.semi D₂ A₂
    U₂ (RingHom.id T.V) (𝟙 _) hid' ρ' hρ'
  have hL₂ : LBIso PW.U.LG.L (U₂.LG.L.pull (𝟙 _)) :=
    LBIso.trans PW.U.LG.isLB (LB.isLB_pull U.LG.isLB _) (LB.isLB_pull U₂.LG.isLB _) hLBW
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL₁ (𝟙 _) (Category.id_comp β).symm).symm
  have hC₂ := TorCoord.coordMap_of_torMatch T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV inferInstance tW.G tW.semi PW.D PW.A
    PW.U (RingHom.id _) (𝟙 _) (fun _ _ h => h) hid' hL₂ ρ hρT
  have hE₂ := equivMap_of_torMatch T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A PW.U (RingHom.id _)
    (𝟙 _) (fun _ _ h => h) ρ hρT
  obtain ⟨-, -, -, -, n, ⟨eZ⟩⟩ := GlobalTheory.UPoinc.UTrait.balanced_posDef_lattice E H Dw l Xo c T
  haveI : Module.Finite ℤ T.P.D.toPre.X := Module.Finite.equiv eZ.symm
  haveI : Module.Finite ℤ PW.D.toPre.X := Module.Finite.equiv e.toAddEquiv.toIntLinearEquiv.symm
  have hρ'i : Function.Injective ρ' := by
    have h := OrzechProperty.injective_of_surjective_endomorphism (ρ.comp ρ').toIntLinearMap (hρs.comp hρ's)
    exact Function.Injective.of_comp (f := ⇑ρ) (g := ⇑ρ') h
  haveI : Module.Finite ℤ D₂.toPre.X := Module.Finite.of_surjective ρ'.toIntLinearMap hρ's
  have hρi : Function.Injective ρ := by
    have h := OrzechProperty.injective_of_surjective_endomorphism (ρ'.comp ρ).toIntLinearMap (hρ's.comp hρs)
    exact Function.Injective.of_comp (f := ⇑ρ') (g := ⇑ρ) h
  let ρE : D₂.toPre.X ≃+ PW.D.toPre.X := AddEquiv.ofBijective ρ ⟨hρi, hρs⟩
  refine ⟨(hD.xe.symm.trans ρE).trans e.toAddEquiv, ?_, ?_⟩
  · intro y s hs
    obtain ⟨r₂, hr₂⟩ := GlobalTheory.BetaAdd.exists_coord D₂ (hD.xe.symm y)
    obtain ⟨h0, r', hr', hass⟩ := he (ρ (hD.xe.symm y))
    refine ⟨h0, ?_⟩
    have h1 : Associated (ψ s) r' := (hC₁ y s r₂ hs hr₂).trans (hC₂ _ r₂ r' hr₂ hr' : Associated r₂ r')
    exact (h1.pow_pow (n := 2)).trans hass
  · intro a y
    obtain ⟨fR, hfRmon, hfRgm, hfRchar⟩ := hm a
    have hcompat : (tW.act.act a).left ≫ β = β ≫ fR.left := by
      apply hgm.1.hom_ext
      · calc ((tW.act.act a).left ≫ β) ≫ gm = (tW.act.act a).left ≫ mW.φ ≫ βT := by rw [Category.assoc, hβgm]
          _ = mW.φ ≫ (T.t.act.act a).left ≫ βT := by rw [← Category.assoc, mW.act a, Category.assoc]
          _ = mW.φ ≫ βT ≫ (f a).left := by rw [hactT a]
          _ = (β ≫ fR.left) ≫ gm := by rw [Category.assoc, hfRgm, reassoc_of% hβgm]
      · rw [Category.assoc, hβG, Category.assoc, Over.w fR, hβG, ← Category.assoc, Over.w (tW.act.act a)]
    obtain ⟨m₂, hm₂⟩ := endChar_exists_of_isMonHom T.V hTV tW.G tW.semi D₂ A₂ U₂ (tW.act.act a) (tW.act.hom a)
    have h1 := hE₁ fR (tW.act.act a) hfRmon (tW.act.hom a) hcompat (m a) m₂ hfRchar hm₂ y
    have h2 := hE₂ (tW.act.act a) (tW.act.act a) (tW.act.hom a) (tW.act.hom a) (by simp) m₂ _ hm₂
      (GlobalTheory.UPoinc.endChar_act E H T.V hTV tW PW a) (hD.xe.symm y)
    show e (ρ (hD.xe.symm (m a y))) = H.bar a • e (ρ (hD.xe.symm y))
    have h1' : hD.xe.symm (m a y) = m₂ (hD.xe.symm y) := h1
    rw [h1', h2]
    exact e.map_smul _ _

end GlobalTheory.UPoinc.TraitCompare
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.classical_trait_periods_bounded_below_closed_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ K : ℝ, ∀ (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X), x ≠ 0 → ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  first | exact @GlobalTheory.UPoinc.lam_of_closed | exact GlobalTheory.UPoinc.lam_of_closed | (intros; apply GlobalTheory.UPoinc.lam_of_closed <;> assumption)
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.pic_generic_fibre_quotient_strictHenselisation_no_torsion_alt : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ c : CommRing.Pic (TensorProduct T (FractionRing T) A), c ^ q = 1 → c = 1 := by
  first | (exact @GlobalTheory.pic_generic_fibre_quotient_strictHenselisation_no_torsion) | (exact GlobalTheory.pic_generic_fibre_quotient_strictHenselisation_no_torsion) | (intros; apply GlobalTheory.pic_generic_fibre_quotient_strictHenselisation_no_torsion  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.Heat.exists_polynomial_defect_of_isMonomial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∃ (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) :=
  GlobalTheory.T.heatOperator_defect_polynomial_monomial_periods
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.heatOperators_symbol_zero_torsion_points_horizontal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ y : P.D.toPre.X, ∃ c' : Sp (DualNumber k) ⟶ B'.left, c' ≫ B'.hom = 𝟙 _ ∧ c' ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left := by
  first | exact @GlobalTheory.HeatPts.exists_horizontal_section | exact GlobalTheory.HeatPts.exists_horizontal_section | (intros; apply GlobalTheory.HeatPts.exists_horizontal_section <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.thetaMember_exists_integral_terms_unit_shift : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∃ u : X → C → V, 𝔪.Terms x₀ lab (fun mu c => u mu c * t mu) ∧ (∀ mu, ∃ c, IsUnit (u mu c)) ∧ ∀ c, lab c = x₀ → IsUnit (u 0 c) := by
  first | exact @GlobalTheory.GSep.IntTerm.exists_terms | exact GlobalTheory.GSep.IntTerm.exists_terms | (intros; apply GlobalTheory.GSep.IntTerm.exists_terms <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.thetaMember_twist_weight_wellDefined_lattice : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (sg : ℤˣ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ wt : Y1 → ZMod (X₁.S.r * X₁.S.N), ∀ a mu, 𝔪1.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a := by
  first | exact @GlobalTheory.GSep.WtWd.wt_wd | exact GlobalTheory.GSep.WtWd.wt_wd | (intros; apply GlobalTheory.GSep.WtWd.wt_wd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.exists_torus_char_of_label_orthogonal_dividing : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) := by
  first | exact @GlobalTheory.GSep.TorPt.exists_torus_char | exact GlobalTheory.GSep.TorPt.exists_torus_char | (intros; apply GlobalTheory.GSep.TorPt.exists_torus_char <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.thetaMembers_lattices_iso_of_specializes_dvr : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), GlobalTheory.GSep.ZHAbove X₁ Y πY → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] [IsDiscreteValuationRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (X₀ : Type) [AddCommGroup X₀] (t₁ : X₀ → V₁) (δ₁ : I → X₀ → X₀) (𝔫₁ : GlobalTheory.GSep.GMem X₁ z₁ act V₁ ev₁ X₀ t₁ δ₁) (ξ₁ : Sp V₁ ⟶ Y.Z) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] [IsDiscreteValuationRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (X : Type) [AddCommGroup X] (t₂ : X → V₂) (δ₂ : I → X → X) (𝔫₂ : GlobalTheory.GSep.GMem X₁ z₁ act V₂ ev₂ X t₂ δ₂) (ξ₂ : Sp V₂ ⟶ Y.Z), ξ₁ ≫ πY = spMap ev₁ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₂ ≫ πY = spMap ev₂ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → GlobalTheory.GSep.GMem.LatTo 𝔫₁ 𝔫₂ := by
  first | exact @GlobalTheory.GSep.Spz.latTo_of_specializes | exact GlobalTheory.GSep.Spz.latTo_of_specializes | (intros; apply GlobalTheory.GSep.Spz.latTo_of_specializes <;> assumption)
end
