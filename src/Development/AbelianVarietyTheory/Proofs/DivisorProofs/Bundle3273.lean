module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3245
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModuliObjectSpreadNormalDomain
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle078
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3246
public import Mathlib.RingTheory.Flat.TorsionFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNormProdAevalEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3247
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3216
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.normalisedThetaConstant_eq_scalar_root_mul_unit : ∀ (n : ℕ), n.Prime → Odd n → ∀ j : ℕ, 1 ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (n : V₁) →
  ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen →
  ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th →
  ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K),
    GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  first | exact @GlobalTheory.USep.thetaConst_eq_lam_root_mul_unit | exact GlobalTheory.USep.thetaConst_eq_lam_root_mul_unit | (intros; apply GlobalTheory.USep.thetaConst_eq_lam_root_mul_unit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.sharp_refinement_odd_prime_localization : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.eighthPowerFibre_thetaObj | exact GlobalTheory.Poinc.Sep.E8Fibration.eighthPowerFibre_thetaObj | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.eighthPowerFibre_thetaObj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_toricChartRing_factorisation_localHom : ∀ (W : Type) [CommRing W] [IsRegularLocalRing W], Nonempty (ℚ →+* W) → ∀ (m N : ℕ) (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ ψV : MvPolynomial (Fin m ⊕ Fin N) W →+* V, IsLocalHom (ψV.comp MvPolynomial.C) → (∀ i, ψV (MvPolynomial.X (.inl i)) ∈ maximalIdeal V) → ∃ (k : Type) (_ : Field k) (e : ℕ) (ψ : MvPolynomial (Fin m ⊕ Fin N) W →+* ChartRing k m e) (θ : ChartRing k m e →+* V), GlobalTheory.TChart.IsComplAt ψ ∧ IsLocalHom θ ∧ θ.comp ψ = ψV ∧ IsLocalHom (ψ.comp MvPolynomial.C) ∧ ∀ i, ψ (MvPolynomial.X (.inl i)) = bdParam k m e i := by
  first | exact @GlobalTheory.TChart.exists_chartRing_factor | exact GlobalTheory.TChart.exists_chartRing_factor | (intros; apply GlobalTheory.TChart.exists_chartRing_factor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem exists_periods_of_pull : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → LBIso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') → (∀ a : Fin L.T.r → ℤ, ∃ x : Sp V₁ ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ x ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∃ q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ, (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V₁, w ≠ 0 ∧ (q a a : FractionRing V₁) = algebraMap V₁ _ w) ∧ ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)), IsCN V₂ → Function.Injective f₂ → f₂.Finite → IsLocalHom f₂ → (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegData V₂ (maximalIdeal V₂)) (hD : IsPullDeg (f₂.comp f₁) D.toPre D'.toPre), DegFrom L.T (f₂.comp κ₁) s ε n D'.toPre (hD.xe.trans (e₀.symm.trans e.symm)) := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ lb pts
  choose x hx using pts
  let y : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B') := fun a => Over.homMk (x a) (hx a).1
  have hy : ∀ a, (y a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧
      (y a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left := fun a => ⟨(hx a).2.1, (hx a).2.2⟩
  obtain ⟨w₁, q, hg, hn, hP⟩ :=
    GlobalTheory.T.exists_normalised_iso_pulledBack_period_relation n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ lb y hy
  exact ⟨q, GlobalTheory.T.pulledBack_period_constants_symmetric n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP hn,
    GlobalTheory.T.pulledBack_period_constants_multiplicative n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP hn,
    GlobalTheory.T.pulled_back_period_constants_diag_mem_maximal n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP,
    GlobalTheory.T.degData_from_lowerBase_after_monomial_extension n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP⟩

end GlobalTheory.TChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unitaryModuliObject_spread_normal_domain : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (b : c.F →+* A) (t : SAB H (Sp A)), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → GlobalTheory.TChart.TorsRat t.G l.M' → ∀ (K : Type) [Field K] (g : A →+* K) (sK : Sp K ⟶ Sp (KA l)) (oK : Obj D l (baseKA l) sK), sK = spMap g ≫ spMap (b.comp (IntermediateField.inclusion c.le).toRingHom) → SABMap oK.t t (spMap g) → ∃ o : Obj D l (baseKA l) (spMap (b.comp (IntermediateField.inclusion c.le).toRingHom)), o.t = t ∧ Nonempty (ObjMap oK o (spMap g)) := by
  first | exact @GlobalTheory.ObjSpread.exists_obj | exact GlobalTheory.ObjSpread.exists_obj | (intros; apply GlobalTheory.ObjSpread.exists_obj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.trait_equivariant_bijection_transport_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), Eqv T.D'.toPre T.A F (C.n ^ j) lab' E' → ∃ (lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A)) (E : Fam D.toPre F (C.n ^ j) → SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)) (Φ : Fam D.toPre F (C.n ^ j) → Fam T.D'.toPre F (C.n ^ j)), LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ (∀ (s : Fam D.toPre F (C.n ^ j)) (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)), F₀.Over s → (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((Φ s).s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1)) ∧ ∀ (s : Fam D.toPre F (C.n ^ j)) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' (Φ s)) q z Jt := by
  first | exact @GlobalTheory.Mum.trait_transport | exact GlobalTheory.Mum.trait_transport | (intros; apply GlobalTheory.Mum.trait_transport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.divisionPoints_correspond_matched_pullbacks : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (D₀ : DegPre R) (D₁ D₂ : DegPre V), D₀.TauBimult → D₂.TauBimult → ∀ (f₁ f₂ : R →+* V) (hD₁ : IsPullDeg f₁ D₀ D₁) (hD₂ : IsPullDeg f₂ D₀ D₂) (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j₁ j₂ : F₀ →+* F) (b : D₁.P.A ⟶ D₂.P.A) (φ' : D₁.X ≃+ D₂.X) (k : ℕ), 1 ≤ k → (∀ p₀ : QkPt D₀ F₀ k, ∃ (p₁ : QkPt D₁ F k) (p₂ : QkPt D₂ F k), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → (∀ y : D₀.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y) → ∀ (y : D₀.X) (x : TF (R := R) F₀ ⟶ D₀.P.A), x ^ k = DegPre.cF D₀ F₀ y → ∃ z : TF (R := V) F ⟶ D₁.P.A, z.left ≫ hD₁.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₁) = spMap j₁ ≫ x.left ∧ z.left ≫ b.left ≫ hD₂.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₂) = spMap j₂ ≫ x.left := by
  first | exact @GlobalTheory.TInj.divPt_match_of_pairs | exact GlobalTheory.TInj.divPt_match_of_pairs | (intros; apply GlobalTheory.TInj.divPt_match_of_pairs <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.divisionPoint_characters_galoisFixed_of_rational_basePoint : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p₀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → (∃ b : TF (R := R) (FractionRing R) ⟶ D'.toPre.P.A, p.g.b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ b.left) → ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (p.g.s χ) (LB.pullGen D'.toPre.P.L _ _ (p.g.s χ) (spMap σ.toAlgHom.toRingHom)) := by
  first | exact @GlobalTheory.Mum.RatChar.charFixed | exact GlobalTheory.Mum.RatChar.charFixed | (intros; apply GlobalTheory.Mum.RatChar.charFixed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_levelPoint_lift_zero_first_coordinate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw (mulDeg L.D l.M') (GlobalTheory.PolDeg.rescale Q g)), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivBy L Q oQ iw s ε e g hD → ∀ a : D'.La, ∃ p : QkPt Q (FractionRing V) l.M', IsLevPt L iw hD a p := by
  first | exact @GlobalTheory.UCanon.exists_levPt | exact GlobalTheory.UCanon.exists_levPt | (intros; apply GlobalTheory.UCanon.exists_levPt <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_posDef_quadraticForm_hom : ∀ (K : Type) [Field K] (A B : AbVar K), ∃ Q : (A ⟶ B) → ℤ, (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) ∧ (∀ f, 0 ≤ Q f) ∧ ∀ f, Q f = 0 → f = 0 := by
  first | (exact @GlobalTheory.AV.AbVar.exists_posDef_quadratic_hom) | (exact GlobalTheory.AV.AbVar.exists_posDef_quadratic_hom) | (intros; apply GlobalTheory.AV.AbVar.exists_posDef_quadratic_hom  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

theorem map_eq_charpoly_vmap : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A : AbVar K) [Module.Finite ℚ_[l] (Vl l A)] (f : End A) (P : Polynomial ℚ),
    P.Monic → P.natDegree = 2 * A.dim →
    (∀ n : ℤ, P.eval (n : ℚ) = (deg (A := A) (B := A) ((n : End A) - f).asHom : ℚ)) →
    P.map (algebraMap ℚ ℚ_[l]) = (vmap l (A := A) (B := A) f.asHom).charpoly := by
  intro K _ l _ hl A _ f P hPm hPd hP
  obtain ⟨hfree, hfin, -, -, hrkV⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  let δ : Polynomial ℤ → ℚ := fun F => (deg (A := A) (B := A) (Polynomial.aeval f F).asHom : ℚ)
  have hmul : ∀ F G, δ (F * G) = δ F * δ G := by
    intro F G
    simp only [δ, map_mul]
    rw [End.mul_asHom, (GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K A A A _ _ rfl rfl).2]
    push_cast
    exact mul_comm _ _
  have hpoly : ∀ (n : ℕ) (u : Fin n → Polynomial ℤ), ∃ Φ : MvPolynomial (Fin n) ℚ, Φ.IsHomogeneous (2 * A.dim) ∧
      ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) Φ = δ (∑ i, m i • u i) := by
    intro n u
    obtain ⟨Φ, hΦ, hΦe⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl n (fun i => (Polynomial.aeval f (u i)).asHom)
    refine ⟨Φ, hΦ, fun m => ?_⟩
    rw [hΦe m]
    have hz (k : ℤ) (g : End A) : (k • g).asHom = k • g.asHom :=
      map_zsmul End.addEquiv k g

    simp only [δ, map_sum, map_zsmul, End.sum_asHom, hz]
  have hPn : ∀ n : ℤ, P.eval (n : ℚ) = δ (Polynomial.C n - Polynomial.X) := by
    intro n
    rw [hP n]
    simp only [δ, map_sub, map_intCast, Polynomial.aeval_X, eq_intCast]
  have hroots := GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm (PadicAlgCl l) A.dim δ P hmul hpoly hPm hPd hPn
  apply GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq l
  · exact hPm.map _
  · exact LinearMap.charpoly_monic _
  · rw [Polynomial.natDegree_map, hPd, LinearMap.charpoly_natDegree, hrkV]
  · intro F
    have h1 : (P.map (algebraMap ℚ ℚ_[l])).aroots (PadicAlgCl l) = P.aroots (PadicAlgCl l) := by
      simp only [Polynomial.aroots, Polynomial.map_map]
      congr 2
    rw [h1]
    refine (congrArg norm (hroots F)).symm.trans ?_
    have h2 := GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' ℚ_[l] (PadicAlgCl l) (Vl l A) (vmap l f.asHom) (F.map (algebraMap ℤ ℚ_[l]))
    simp only [Polynomial.aeval_map_algebraMap] at h2
    rw [← h2]
    let t : End A →+* Module.End ℤ_[l] (Tl l A) :=
      { toFun := fun g => tmap l A A g.asHom
        map_one' := tmap_id l A
        map_mul' := fun g h => tmap_comp l h.asHom g.asHom
        map_zero' := map_zero (tmap l A A)
        map_add' := fun g h => map_add (tmap l A A) g.asHom h.asHom }
    let ψ : End A →+* Module.End ℚ_[l] (Vl l A) :=
      (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)).toRingHom.comp t
    have hψ : vmap l (A := A) (B := A) f.asHom = ψ f := rfl
    have hev : ∀ G : Polynomial ℤ, Polynomial.aeval (ψ f) G = ψ (Polynomial.aeval f G) := by
      intro G
      induction G using Polynomial.induction_on with
      | C a => simp
      | add p q hp hq => simp only [map_add (f := _), hp, hq]
      | monomial n a _ => simp only [map_mul, map_pow, Polynomial.aeval_X, eq_intCast, map_intCast]
    rw [hψ, hev F]
    have h3 : ψ (Polynomial.aeval f F) = (tmap l A A (Polynomial.aeval f F).asHom).baseChange ℚ_[l] := rfl
    rw [h3, LinearMap.det_baseChange, PadicAlgCl.norm_extends]
    have h4 (g : A ⟶ A) : ‖(deg g : ℤ_[l])‖ = ‖LinearMap.det (tmap l A A g)‖ := by
      by_cases hg : IsIsogeny g
      · obtain ⟨-, -, hpos, -⟩ := isogeny_flat_finrank K A A g hg
        obtain ⟨-, hcard⟩ := GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny K l hl A A g hg
        rw [GlobalTheory.T.norm_det_eq_inv_card_coker l (Tl l A) (tmap l A A g) _ hcard,
          norm_natCast_padicInt l hpos.ne']
      · have hdeg : deg g = 0 := by simp [deg, hg]
        rw [hdeg, Nat.cast_zero, norm_zero, eq_comm, norm_eq_zero]
        by_contra hne
        apply hg
        rw [(GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff K l hl A A g).2]
        have hu : IsUnit (LinearMap.det (vmap l g)) := by
          rw [vmap, LinearMap.det_baseChange]
          exact (isUnit_iff_ne_zero).2
            ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).2 hne)
        rw [← LinearMap.isUnit_iff_isUnit_det] at hu
        exact (Module.End.isUnit_iff _).1 hu
    have h5 : algebraMap ℚ (PadicAlgCl l) (δ F) = algebraMap ℚ_[l] (PadicAlgCl l) ((deg (A := A) (B := A) (Polynomial.aeval f F).asHom : ℕ) : ℚ_[l]) := by
      simp only [δ, map_natCast]
    rw [h5, PadicAlgCl.norm_extends]
    simpa only [PadicInt.norm_def, PadicInt.coe_natCast, PadicInt.algebraMap_apply] using
      h4 (Polynomial.aeval f F).asHom

end GlobalTheory.AV.AbVar
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate :
    ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
      ∀ (A : AbVar K) [Module.Finite ℚ_[l] (Vl l A)] (f : End A) (P : Polynomial ℚ),
        P.Monic → P.natDegree = 2 * A.dim →
          (∀ n : ℤ, P.eval (n : ℚ) = (deg ((n : End A) - f).asHom : ℚ)) →
            P.map (algebraMap ℚ ℚ_[l]) = (vmap l f.asHom).charpoly := by
  intro K _ l _ hl A _ f P hPm hPd hP
  have hCharpoly : P.map (algebraMap ℚ ℚ_[l]) = (vmap l f.asHom).charpoly := by
    obtain ⟨hfree, hfin, -, -, hrkV⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
    let δ : Polynomial ℤ → ℚ := fun F => (deg (A := A) (B := A) (Polynomial.aeval f F).asHom : ℚ)
    have hmul : ∀ F G, δ (F * G) = δ F * δ G := by
      intro F G
      simp only [δ, map_mul]
      rw [End.mul_asHom, (GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K A A A _ _ rfl rfl).2]
      push_cast
      exact mul_comm _ _
    have hpoly : ∀ (n : ℕ) (u : Fin n → Polynomial ℤ), ∃ Φ : MvPolynomial (Fin n) ℚ, Φ.IsHomogeneous (2 * A.dim) ∧
        ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) Φ = δ (∑ i, m i • u i) := by
      intro n u
      obtain ⟨Φ, hΦ, hΦe⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl n (fun i => (Polynomial.aeval f (u i)).asHom)
      refine ⟨Φ, hΦ, fun m => ?_⟩
      rw [hΦe m]
      have hz (k : ℤ) (g : End A) : (k • g).asHom = k • g.asHom :=
        map_zsmul (End.addEquiv (X := A)) k g

      simp only [δ, map_sum, map_zsmul, End.sum_asHom, hz]
    have hPn : ∀ n : ℤ, P.eval (n : ℚ) = δ (Polynomial.C n - Polynomial.X) := by
      intro n
      rw [hP n]
      simp only [δ, map_sub, map_intCast, Polynomial.aeval_X, eq_intCast]
    have hroots := GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm (PadicAlgCl l) A.dim δ P hmul hpoly hPm hPd hPn
    apply GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq l
    · exact hPm.map _
    · exact LinearMap.charpoly_monic _
    · rw [Polynomial.natDegree_map, hPd, LinearMap.charpoly_natDegree, hrkV]
    · intro F
      have h1 : (P.map (algebraMap ℚ ℚ_[l])).aroots (PadicAlgCl l) = P.aroots (PadicAlgCl l) := by
        simp only [Polynomial.aroots, Polynomial.map_map]
        congr 2
      rw [h1]
      refine (congrArg norm (hroots F)).symm.trans ?_
      have h2 := GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' ℚ_[l] (PadicAlgCl l) (Vl l A) (vmap l f.asHom) (F.map (algebraMap ℤ ℚ_[l]))
      simp only [Polynomial.aeval_map_algebraMap] at h2
      rw [← h2]
      let t : End A →+* Module.End ℤ_[l] (Tl l A) :=
        { toFun := fun g => tmap l A A g.asHom
          map_one' := tmap_id l A
          map_mul' := fun g h => tmap_comp l h.asHom g.asHom
          map_zero' := map_zero (tmap l A A)
          map_add' := fun g h => map_add (tmap l A A) g.asHom h.asHom }
      let ψ : End A →+* Module.End ℚ_[l] (Vl l A) :=
        (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)).toRingHom.comp t
      have hψ : vmap l f.asHom = ψ f := rfl
      have hev (G : Polynomial ℤ) : Polynomial.aeval (ψ f) G = ψ (Polynomial.aeval f G) := by
        induction G using Polynomial.induction_on with
        | C a => simp
        | add p q hp hq => simp only [map_add, hp, hq]
        | monomial n a _ => simp only [map_mul, map_pow, Polynomial.aeval_X, eq_intCast, map_intCast]
      rw [hψ, hev F]
      let g := (Polynomial.aeval f F).asHom
      have h3 : ψ (Polynomial.aeval f F) = (tmap l A A g).baseChange ℚ_[l] := rfl
      rw [h3, LinearMap.det_baseChange, PadicAlgCl.norm_extends]
      have hnorm : ‖(deg g : ℤ_[l])‖ = ‖LinearMap.det (tmap l A A g)‖ := by
        by_cases hg : IsIsogeny g
        · obtain ⟨-, -, hpos, -⟩ := isogeny_flat_finrank K A A g hg
          obtain ⟨-, hcard⟩ :=
            GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny K l hl A A g hg
          have hdet := GlobalTheory.T.norm_det_eq_inv_card_coker l (Tl l A) (tmap l A A g)
            (padicValNat l (deg g)) hcard
          rw [hdet, norm_natCast_padicInt l hpos.ne']
        · have hdeg : deg g = 0 := by rw [deg, ite_eq_right hg]
          rw [hdeg, Nat.cast_zero, norm_zero, eq_comm, norm_eq_zero]
          by_contra hdet
          apply hg
          rw [(GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff K l hl A A g).2]
          have hu : IsUnit (LinearMap.det (vmap l g)) := by
            rw [vmap, LinearMap.det_baseChange]
            exact (isUnit_iff_ne_zero).2
              ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).2 hdet)
          rw [← LinearMap.isUnit_iff_isUnit_det] at hu
          exact (Module.End.isUnit_iff _).1 hu
      have hcast : algebraMap ℚ (PadicAlgCl l) (δ F) =
          algebraMap ℚ_[l] (PadicAlgCl l) (deg g : ℚ_[l]) := by
        simp only [δ, g, map_natCast]
      rw [hcast, PadicAlgCl.norm_extends]
      rw [PadicInt.norm_def] at hnorm
      simpa using hnorm
  exact hCharpoly
end
