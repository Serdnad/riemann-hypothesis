module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle068
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3272
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3236
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTwistOfLowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3224
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3235
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem traitInv_eqv_value : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ lab E, LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s : Fam D.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), F₀.Over s → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J J', Good C.P.L.L z J → Good C.A.L z J' → sval σ p z J = (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (J (p ≫ T.β)) (J' (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z J' := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ em hem
  obtain ⟨f, hfi, hf1, hf2⟩ := GlobalTheory.T.exists_fibre_iso_genericFibre_cover R hR D C W T F hem
  obtain ⟨lab', hq, hm⟩ := GlobalTheory.T.exists_torsionLabels_genericFibre_trait R hR D C j W T F em hem f hfi hf1 hf2
  have hW := T.cdvr
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have : CharZero R := hR.2
  have hcW : CharZero W := charZero_of_injective_ringHom T.inj
  have hsemi : IsSemiAbelian T.G := GlobalTheory.isSemiAbelian_of_unifPre_dvr W T.D' T.A T.G T.U.toUnifPre
  obtain ⟨w₀, hw₀⟩ := T.U.ext
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  obtain ⟨E', hE', hx⟩ := GlobalTheory.T.exists_equivariant_inverse_thetaExpansion W (maximalIdeal W) hW' hcW T.D' T.A T.G T.U hsemi F (C.n ^ j) hodd w₀ hw₀ lab' hq
  obtain ⟨lab, E, Φ, hlab, hE, hΦ, hrel⟩ := GlobalTheory.T.trait_equivariant_bijection_transport_cover R hR D C j wA hwA W T F em hem f hfi hf1 hf2 w₀ hw₀ lab' hm E' hE'
  refine ⟨lab, E, hlab, hE, ?_⟩
  intro F₀ s σ hs hσ Z p p' hβ hG z J J' hJ hJ'
  obtain ⟨JG, hJG⟩ := GlobalTheory.UU.exists_good_pt T.U.LG.isLB z
  obtain ⟨Jt, hJt⟩ := GlobalTheory.UU.exists_good_pt T.A.isLB z
  have hq1 : (p' ≫ inv f) ≫ f = p' := by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hG' : p ≫ T.G.hom = (p' ≫ inv f) ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    rw [hG, ← hf1]; simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  have hβ' : p ≫ T.β = (p' ≫ inv f) ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
    rw [hβ, ← hf2, Category.assoc, IsIso.inv_hom_id_assoc]
  exact (GlobalTheory.T.traitSection_integralExpansion_mem_range_inverseExpansion R hR D C j W T F w₀ hw₀ E' hx F₀ (Φ s) σ (hΦ s F₀ hs) hσ Z p (p' ≫ inv f) hβ' hG' z J JG Jt hJ hJG hJt).trans
    (hrel s Z p p' (p' ≫ inv f) hq1 hβ hG' z J J' JG Jt hJ hJ' hJG hJt).symm

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.nonempty_of_tensorData_posDef_unimodular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
  {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → 1 ≤ r →
  ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → Nonempty (IsLimit (Fan.mk D'.toPre.P.A pr)) →
    (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    Nonempty (PFactor Q D'.toPre) := by
  first | exact @GlobalTheory.Mum.PFactor.nonempty_of_tens | exact GlobalTheory.Mum.PFactor.nonempty_of_tens | (intros; apply GlobalTheory.Mum.PFactor.nonempty_of_tens <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.mumfordBundleIso_additive_cubicalStructure : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (Z : Over (Sp V)) (x x' y : Z ⟶ D.P.A) (x₀ x₀' y₀ : Over.mk (Z.hom ≫ spMap ω) ⟶ T.B), x.left ≫ β = x₀.left → x'.left ≫ β = x₀'.left → y.left ≫ β = y₀.left → ∀ (z : Z.left) J J', Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (x * x') y).left z J J' * cubV D.cub z J' x x' y = lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' * @id (Z.left.presheaf.stalk z)ˣ (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J x₀ x₀' y₀) ∧ lamVal w (lift y (x * x')).left z J J' * cubV D.cub z J' y x x' = lamVal w (lift y x).left z J J' * lamVal w (lift y x').left z J J' * @id (Z.left.presheaf.stalk z)ˣ (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J y₀ x₀ x₀') := by
  first | exact @GlobalTheory.TInj.lamVal_add_cub | exact GlobalTheory.TInj.lamVal_add_cub | (intros; apply GlobalTheory.TInj.lamVal_add_cub <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.mumfordBundleIso_comparison_normalisedGenerator : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A), D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → IsMonHom b → b.left ≫ β₂ = β₁ → ∀ (χ₁ : D₁.X) (χ₂ : D₂.X), e₁ χ₁ = e₂ χ₂ → ∀ u : LB.Gen (CmpLB D₁ D₂ b χ₁ χ₂), Nrm u → ∀ (Z : Over (Sp V)) (x : Z ⟶ D₁.P.A) (z : Z.left) (J : (Z.left ⟶ (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0})) → (JN D₁ D₂).ι) J₀, Good (JN D₁ D₂) z J → Good T.M.L z J₀ → lamVal w₂ (lift (toUnit Z ≫ D₂.c χ₂) (x ≫ b)).left z J₀ (rr J) = lamVal w₁ (lift (toUnit Z ≫ D₁.c χ₁) x).left z J₀ (rl J) * val u x.left z J := by
  first | exact @GlobalTheory.TInj.lamVal_cmp | exact GlobalTheory.TInj.lamVal_cmp | (intros; apply GlobalTheory.TInj.lamVal_cmp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.tautologicalPoint_transport_fieldMap : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D) ββ' w', Function.Injective f → D.TauBimult → From T ω s ε n D₀.toPre e β ββ w → From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' → ∀ (F₀ : Type) [Field F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → ∀ (a : Fin T.r → ℤ) (g₀ : GtPtF D₀.toPre F₀) (g : GtPtF D F), TautPt T ω s ε n D₀.toPre e β ββ w F₀ a g₀ → Tr f hD j g₀ g → TautPt T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' F a g := by
  first | exact @GlobalTheory.TautTransport.tautPt_tr | exact GlobalTheory.TautTransport.tautPt_tr | (intros; apply GlobalTheory.TautTransport.tautPt_tr <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.tautologicalPoint_zero_and_period : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (g : GtPtF D F), (TautPt T ω s ε n D e β ββ w F 0 g → g.IsZero) ∧ ∀ y : D.X, TautPt T ω s ε n D e β ββ w F ((n : ℤ) • e y) g → GtPtF.IsIota y g := by
  first | exact @GlobalTheory.TInj.tautPt_zero_iota | exact GlobalTheory.TInj.tautPt_zero_iota | (intros; apply GlobalTheory.TInj.tautPt_zero_iota <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.EpsObj

theorem act_comm_eps : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → ∀ (u : G' ⟶ G') [IsMonHom u] (v : G ⟶ G) [IsMonHom v], u.left ≫ φ₁ = φ₁ ≫ v.left → u.left ≫ φ₂ = φ₂ ≫ v.left := GlobalTheory.T.commutes_of_commutes_dualNumber_agree_closed

theorem sec_eps : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₁ g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₁ = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₂ → ∀ (n : ℕ), (n : k) ≠ 0 → ∀ (σ : 𝟙_ (Over S) ⟶ G), σ ^ n = 1 → ∀ (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ G'), x ^ n = 1 → x.left ≫ φ₁ = g₁ ≫ σ.left → x.left ≫ φ₂ = g₂ ≫ σ.left := GlobalTheory.T.dualNumber_torsionSection_lies_over_second_map

theorem spMap_comp_eps {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eta_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) (n : ℕ) :
    p.eta a ^ n = p.eta (n • a) := by
  induction n with
  | zero =>
    have h := p.eta_add 0 0
    rw [add_zero] at h
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | succ n ih => rw [pow_succ, ih, succ_nsmul, p.eta_add]

theorem etaA_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) (n : ℕ) :
    p.etaA a ^ n = p.etaA (n • a) := by
  induction n with
  | zero =>
    have h := p.etaA_add 0 0
    rw [add_zero] at h
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | succ n ih => rw [pow_succ, ih, succ_nsmul, p.etaA_add]

theorem eta_pow_M {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) :
    p.eta a ^ l.M = 1 := by
  rw [eta_pow]
  apply p.eta_ker
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at this
    first | exact Ideal.mul_le_left this | exact Ideal.mul_le_right this
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hM Submodule.mem_top

theorem etaA_pow_A {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) :
    p.etaA a ^ l.A = 1 := by
  rw [etaA_pow]
  exact p.etaA_ker a

theorem exists_objMaps : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (W : Type) [CommRing W] (b : c.F →+* W) (o : LowObj D' c b) (k : Type) [Field k] (f : W →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ o.t.G.left), IsGrpPullback B' o.t.G (spMap f) π₁ → IsGrpPullback B' o.t.G (spMap (GlobalTheory.RigChart.constHom f)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → LBIso (o.t.PP.L.pull π₁) (o.t.PP.L.pull π₂) → ∃ (o' : LowObj D' c (f.comp b)) (m₁ : ObjMap o' o (spMap f)) (m₂ : ObjMap o' o (spMap (GlobalTheory.RigChart.constHom f))) (io : o'.t.G.left ≅ B'.left), io.hom ≫ B'.hom = o'.t.G.hom ∧ m₁.toSABMap.φ = io.hom ≫ π₁ ∧ m₂.toSABMap.φ = io.hom ≫ π₂ := by
  intro E _ _ _ H D' l c W _ b o k _ f B' _ π₁ π₂ h₁ h₂ h0 hL
  have hlow : lowMap c (f.comp b) = spMap f ≫ lowMap c b := by
    unfold lowMap
    rw [RingHom.comp_assoc, spMap_comp_eps]
  obtain ⟨o', ⟨m₀⟩⟩ : ∃ o' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (lowMap c (f.comp b)),
      Nonempty (ObjMap o' o (spMap f)) := by
    rw [hlow]
    exact GlobalTheory.LevelGroup.pull_univ o (spMap f)
  let io : o'.t.G.left ≅ B'.left := IsPullback.isoIsPullback _ _ m₀.cart.1 h₁.1
  have io₁ : io.hom ≫ π₁ = m₀.toSABMap.φ := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have io₂ : io.hom ≫ B'.hom = o'.t.G.hom := IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hio : IsGrpPullback o'.t.G B' (𝟙 _) io.hom :=
    IsGrpPullback.cancel h₁ (by rw [Category.id_comp, io₁]; exact m₀.cart) (by rw [io₂, Category.comp_id])
  have hψc : IsGrpPullback o'.t.G o.t.G (spMap (GlobalTheory.RigChart.constHom f)) (io.hom ≫ π₂) := by
    have := hio.comp h₂
    rwa [Category.id_comp] at this
  have h0' : ∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k),
      x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom →
        x ≫ m₀.toSABMap.φ = x ≫ io.hom ≫ π₂ := by
    intro Z x y hx
    rw [← io₁, ← Category.assoc, ← Category.assoc]
    exact h0 Z (x ≫ io.hom) y (by rw [Category.assoc, io₂, hx])
  have hA' : IsAbelianScheme o'.t.G :=
    ⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩
  have hact : ∀ a, (o'.t.act.act a).left ≫ io.hom ≫ π₂ = (io.hom ≫ π₂) ≫ (o.t.act.act a).left := fun a => by
    haveI := o'.t.act.hom a
    haveI := o.t.act.hom a
    exact act_comm_eps k o'.t.G hA' o.t.G _ _ _ hψc h0' (o'.t.act.act a) (o.t.act.act a) (m₀.act a)
  have hLB : LBIso o'.t.PP.L (o.t.PP.L.pull (io.hom ≫ π₂)) := by
    obtain ⟨w, hw, -⟩ := m₀.lin
    have e₁ : LBIso o'.t.PP.L (o.t.PP.L.pull (io.hom ≫ π₁)) := by
      rw [io₁]
      exact ⟨w, hw⟩
    have e₂ : LBIso (o.t.PP.L.pull (io.hom ≫ π₁)) (o.t.PP.L.pull (io.hom ≫ π₂)) :=
      GlobalTheory.GenSpread.lbIso_pull_comp io.hom rfl rfl hL
    exact LBIso.trans o'.t.PP.isLB (pull_isLB o.t.PP.isLB _) (pull_isLB o.t.PP.isLB _) e₁ e₂
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_sabMap_of_grpPullback_respecting_action_bundle o'.t o.t (spMap (GlobalTheory.RigChart.constHom f)) (io.hom ≫ π₂) o.proper hψc hact hLB
  have hg : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap f =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (GlobalTheory.RigChart.constHom f) := by
    rw [← spMap_comp_eps, ← spMap_comp_eps]
    congr 1
  have hunit : ∀ n : ℕ, 0 < n → (n : k) ≠ 0 := by
    intro n hn
    have := ((baseKA (LowDat.lowLevel l)).unit n hn).map
      (((TrivSqZeroExt.fstHom k k k).toRingHom.comp (f.comp b)).comp
        (IntermediateField.inclusion (LowDat.ka_le l c)).toRingHom)
    rw [map_natCast] at this
    exact this.ne_zero
  have hsec : ∀ (σ : 𝟙_ (Over (Sp W)) ⟶ o.t.G) (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G) (n : ℕ), 0 < n →
      σ ^ n = 1 → x ^ n = 1 → x.left ≫ m₀.toSABMap.φ = spMap f ≫ σ.left →
        x.left ≫ io.hom ≫ π₂ = spMap (GlobalTheory.RigChart.constHom f) ≫ σ.left :=
    fun σ x n hn hσ hx hx₁ => sec_eps k o'.t.G hA' o.t.G _ _ _ _ hψc h0' hg n (hunit n hn) σ hσ x hx hx₁
  have hMpos : 0 < (LowDat.lowLevel l).M := by have := (LowDat.lowLevel l).three_le; omega
  let m₂ : ObjMap o' o (spMap (GlobalTheory.RigChart.constHom f)) :=
    { toSABMap := m
      eta := fun a => by
        show (o'.eta a).left ≫ m.φ = _
        rw [hm]
        exact hsec _ _ _ hMpos (eta_pow_M o a) (eta_pow_M o' a) (m₀.eta a)
      etaA := fun a => by
        show (o'.etaA a).left ≫ m.φ = _
        rw [hm]
        exact hsec _ _ _ (LowDat.lowLevel l).A_pos (etaA_pow_A o a) (etaA_pow_A o' a) (m₀.etaA a) }
  exact ⟨o', m₀, m₂, io, io₂, io₁.symm, hm⟩

end GlobalTheory.UCanon.EpsObj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorRigid

open GlobalTheory.RigChart GlobalTheory.ToricData

theorem commGroup_fourfold_cancellation {G : Type*} [CommGroup G] (a1 a2 a3 a4 b1 b2 b3 b4 U V : G) :
    a1 * a2⁻¹ * a3⁻¹ * a4 * V = ((b1⁻¹ * (U * a1)) * (b2⁻¹ * (U * a2))⁻¹ * (b3⁻¹ * (U * a3))⁻¹ * (b4⁻¹ * (U * a4))) *
      (b1 * b2⁻¹ * b3⁻¹ * b4 * V) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem val_const_of_fromBase : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k), ρ.comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) → ∀ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ Q.P.A.left) (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)), GlobalTheory.TautRigid.AbConst Q ρ B' π₁ π₂ w c' → ∀ (y z : Q.X) (zz : Sp (DualNumber k)) (J : (Sp (DualNumber k) ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L zz J → val (τ₀ y z) (spMap ρ) zz J = GlobalTheory.TautRigid.lamC Q w c' y z zz J * val (τ₀ y z) (spMap (GlobalTheory.RigChart.constHom ρ)) zz J := by
  intro R _ _ Q τ₀ W₀ _ ιb hFB k _ ρ hρ B' iG π₁ π₂ w c' hA y z zz J hJ
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hA
  obtain ⟨B₀, iB₀, M₀, c₀, τ₁, β, wF, hB₀, hM₀, hβ, hwF, hc₀, hτ₁, hpt⟩ := GlobalTheory.T.fromBase_identity_along_morphism Q τ₀ ιb hFB
  have hπ : π₁ ≫ β = π₂ ≫ β := GlobalTheory.T.abelianPart_identifications_agree_constant_tangent Q ιb B₀ β hβ k ρ hρ B' π₁ π₂ h₁ h₂ h₃
  have hB'ab : IsAbelianScheme B' := GlobalTheory.T.isAbelianScheme_of_grpPullback' π₁ h₁ Q.P.isAb
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_constant_unit_pulledBack_bundle_automorphism (DualNumber k) B' hB'ab Q.P.L M₀ β wF π₁ π₂ w Q.P.isLB hM₀ hwF h₄ hπ
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.UU.exists_good_pt hM₀ zz
  have e1 := hpt _ (spMap ρ) y z zz J J₀ hJ hJ₀
  have e2 := hpt _ (spMap (GlobalTheory.RigChart.constHom ρ)) y z zz J J₀ hJ hJ₀
  have hιb : spMap ρ ≫ spMap ιb = spMap (GlobalTheory.RigChart.constHom ρ) ≫ spMap ιb := by
    have h' : (GlobalTheory.RigChart.constHom ρ).comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) := by
      exact RingHom.ext fun x => rfl
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (hρ.trans h'.symm)
  rw [hιb] at e1
  have q1 : ∀ x, spMap ρ ≫ cpt Q x = c' x ≫ π₁ := fun x => ((h₅ x).2.1).symm
  have q2 : ∀ x, spMap (GlobalTheory.RigChart.constHom ρ) ≫ cpt Q x = c' x ≫ π₂ := fun x => ((h₅ x).2.2).symm
  have q1' : ∀ x, spMap ρ ≫ cpt Q x ≫ β = c' x ≫ π₁ ≫ β := fun x => by
    rw [← Category.assoc, q1, Category.assoc]
  have q2' : ∀ x, spMap (GlobalTheory.RigChart.constHom ρ) ≫ cpt Q x ≫ β = c' x ≫ π₂ ≫ β := fun x => by
    rw [← Category.assoc, q2, Category.assoc]
  rw [q1', q1', q1', q1', q1, q1, q1, q1] at e1
  rw [q2', q2', q2', q2', q2, q2, q2, q2] at e2
  have hW : ∀ x, gm (c' x) zz _ (w.s (fun _ => J (c' x ≫ π₂), fun _ => J (c' x ≫ π₁))) =
      (gm (c' x ≫ π₂) zz _ (wF.s (fun _ => J₀ (c' x ≫ π₂ ≫ β), J (c' x ≫ π₂))))⁻¹ *
        (gm (𝟙 _) zz ⊤ (unitOn u) * gm (c' x ≫ π₁) zz _ (wF.s (fun _ => J₀ (c' x ≫ π₁ ≫ β), J (c' x ≫ π₁)))) :=
    fun x => eq_inv_mul_of_mul_eq (hu (c' x) (h₅ x).1 zz J J₀ hJ hJ₀)
  unfold GlobalTheory.TautRigid.lamC
  rw [e1, e2, hW, hW, hW, hW]
  exact commGroup_fourfold_cancellation _ _ _ _ _ _ _ _ _ _

theorem snd_eq_zero_of_isConstAlong : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) → ∀ j, (ρ (Cn.ψ (MvPolynomial.X (.inr j)))).snd = 0 := by
  classical
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn k _ ρ a hC hconst j
  obtain ⟨ε', τ₀, hε', hFB, hτ⟩ := GlobalTheory.T.canonicalFamily_periods_in_coordinates Xo c φ R hB C Cn
  obtain ⟨B', iG, π₁, π₂, w, c', h₁, h₂, h₃, h₄, h₅, h₆⟩ := hC
  have hA : GlobalTheory.TautRigid.AbConst C.P.D.toPre ρ B' π₁ π₂ w c' := ⟨h₁, h₂, h₃, h₄, h₅⟩
  have hB1 := val_const_of_fromBase C.P.D.toPre τ₀ (Cn.ψ.comp MvPolynomial.C) hFB k ρ hconst B' iG π₁ π₂ w c' hA
  haveI : CharZero k := by
    let f : c.F →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom.comp (ρ.comp C.b)
    exact (f.charZero_iff f.injective).1 inferInstance
  set M : ℕ := l.M' with hMdef
  have hM : 0 < M := level_pos l
  let Q := C.P.D.toPre
  let u : Fin Cn.N → Rˣ := fun j => (Cn.tor j).unit
  have hu : ∀ j, (u j : R) = Cn.ψ (MvPolynomial.X (.inr j)) := fun j => IsUnit.unit_spec _
  let δ : Fin C.m → LinearMap.BilinForm ℤ Q.X := C.δ
  let ε : Fin Cn.N → LinearMap.BilinForm ℤ Q.X := fun j => (ε' (.inr j) : LinearMap.BilinForm ℤ Q.X)
  have hδ : ∀ i, (ε' (.inl i) : LinearMap.BilinForm ℤ Q.X) = C.δ i := fun i => by
    rw [hε', Cn.cone i]
  have hli : LinearIndependent ℤ (Sum.elim δ ε) := by
    have h0 : LinearIndependent ℤ (fun κ => (ε' κ : LinearMap.BilinForm ℤ Q.X)) :=
      ε'.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
    have hEq : Sum.elim δ ε = fun κ => (ε' κ : LinearMap.BilinForm ℤ Q.X) := by
      funext κ; rcases κ with i | i
      · exact (hδ i).symm
      · rfl
    rw [hEq]; exact h0
  have key : ∀ y z, ∑ j, ((M : ℤ) * ε j y z) • Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) =
      ∑ i, a i * ((((M : ℤ) • δ i) y z : ℤ) : k) := by
    intro y z
    set v : Rˣ := ∏ j, u j ^ ((M : ℤ) * ε j y z) with hvdef
    let f : Rˣ →* (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom
    obtain ⟨hg, kk, hk, hv⟩ := hτ y z
    have hU' : GlobalTheory.RigChart.IsUnitTau Q C.s (fun i => (M : ℤ) • C.δ i) y z (GlobalTheory.UU.scaleGen (unitOn v) (τ₀ y z)) := by
      refine ⟨GlobalTheory.UU.scaleGen_isGen _ hg, kk * (f v)⁻¹, ?_, fun zz J hJ => ?_⟩
      · have hfv : ((f v : (FractionRing R)ˣ) : FractionRing R) =
            ∏ j, algebraMap R (FractionRing R) (u j : R) ^ ((M : ℤ) * ε j y z) := by
          simp only [f, v, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map,
            MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
        have hne : ((f v : (FractionRing R)ˣ) : FractionRing R) ≠ 0 := (f v).ne_zero
        rw [Units.val_mul, hk, Units.val_inv_eq_inv_val, Fin.prod_univ_add]
        simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, LinearMap.smul_apply, smul_eq_mul,
          Cn.bd, hδ, ← hu]
        rw [← hfv, mul_inv_cancel_right₀ hne]
      · have e : gm (toUnit (TK R)).left zz ⊤ (unitOn v) = gm (𝟙 (TK R).left) zz ⊤ (unitOn (f v)) := by
          rw [GlobalTheory.UU.gm_top]
          exact congrArg _ (pullTop_unitOn (algebraMap R (FractionRing R)) _)
        rw [hv zz J hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, e, ← _root_.mul_assoc, ← map_mul, ← unitOn_mul,
          inv_mul_cancel_right]
    set s : k := ∑ i, a i * ((((M : ℤ) • δ i) y z : ℤ) : k) with hs
    have hE : ∀ zz : Sp (DualNumber k), gm (𝟙 _) zz ⊤ (unitOn (Units.map ρ.toMonoidHom v)) =
        gm (𝟙 _) zz ⊤ (unitOn (GlobalTheory.TautRigid.onePlus s * Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) := by
      intro zz
      obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt C.P.D.toPre.P.isLB zz
      have hp := h₆ y z _ hU' (GlobalTheory.TautRigid.onePlus s) rfl zz J hJ
      have hb := hB1 y z zz J hJ
      have e₁ : gm (spMap ρ) zz ⊤ (unitOn v) = gm (𝟙 _) zz ⊤ (unitOn (Units.map ρ.toMonoidHom v)) := by
        rw [GlobalTheory.UU.gm_top]; exact congrArg _ (pullTop_unitOn ρ v)
      have e₂ : gm (spMap (GlobalTheory.RigChart.constHom ρ)) zz ⊤ (unitOn v) =
          gm (𝟙 _) zz ⊤ (unitOn (Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) := by
        rw [GlobalTheory.UU.gm_top]; exact congrArg _ (pullTop_unitOn (GlobalTheory.RigChart.constHom ρ) v)
      rw [GlobalTheory.UU.val_scaleGen _ _ _ hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, e₁, e₂, hb] at hp
      change _ = GlobalTheory.TautRigid.lamC Q w c' y z zz J * _ * _ at hp
      rw [unitOn_mul, map_mul]
      exact mul_right_cancel (hp.trans ((congrArg (· * _) (_root_.mul_comm _ _)).trans (mul_mul_mul_comm _ _ _ _)))
    have hv2 := unitOn_inj.1 (unit_ext fun x _ => hE x)
    have h3 := congrArg (fun x => Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k x)) hv2
    rw [map_mul, toAdd_mul, GlobalTheory.TautRigid.dlog_onePlus] at h3
    have hc0 : Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) = 0 := by
      have hs0 : ∀ r : R, (GlobalTheory.RigChart.constHom ρ r).snd = 0 := fun r => by
        simp only [GlobalTheory.RigChart.constHom, RingHom.comp_apply]
        rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
      rw [GlobalTheory.TautRigid.dlog_apply, Units.coe_map]
      erw [hs0, zero_div]
    rw [hc0, add_zero] at h3
    rw [← h3, hvdef, map_prod, map_prod, toAdd_prod]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zpow, map_zpow, toAdd_zpow]
  set L : Fin Cn.N → k := fun j => Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) with hL
  let F : Fin C.m ⊕ Fin Cn.N → Q.X × Q.X → ℤ := fun κ p => Sum.elim δ ε κ p.1 p.2
  have hF : LinearIndependent ℤ F := by
    let e : LinearMap.BilinForm ℤ Q.X →ₗ[ℤ] (Q.X × Q.X → ℤ) :=
      { toFun := fun β p => β p.1 p.2
        map_add' := fun β β' => by funext p; rfl
        map_smul' := fun n β => by funext p; rfl }
    have he : LinearMap.ker e = ⊥ := LinearMap.ker_eq_bot.mpr fun β β' h =>
      LinearMap.ext fun y => LinearMap.ext fun z => congrFun h (y, z)
    have hEq : F = e ∘ Sum.elim δ ε := by
      funext κ p
      rcases κ with i | j <;> rfl
    rw [hEq]
    exact hli.map' e he
  have hz := GlobalTheory.PolFan.eq_zero_of_linearIndependent_int hF k
    (Sum.elim (fun i => a i * (M : k)) (fun j => -(L j * (M : k)))) fun p => by
      rw [Fintype.sum_sum_type]
      have hk := key p.1 p.2
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, LinearMap.smul_apply, smul_eq_mul] at hk
      simp only [Sum.elim_inl, Sum.elim_inr, F]
      have e1 : ∑ i, a i * (M : k) * ((δ i p.1 p.2 : ℤ) : k) = ∑ i, a i * ((M : k) * ((δ i p.1 p.2 : ℤ) : k)) :=
        Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ j, -(L j * (M : k)) * ((ε j p.1 p.2 : ℤ) : k) =
          -∑ j, (M : k) * ((ε j p.1 p.2 : ℤ) : k) * L j := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e1, e2, ← hk]
      ring
  have h1 := congrFun hz (Sum.inr j)
  simp only [Sum.elim_inr, Pi.zero_apply, neg_eq_zero, mul_eq_zero, Nat.cast_eq_zero] at h1
  have hLj : Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) = 0 := h1.resolve_right hM.ne'
  rw [GlobalTheory.TautRigid.dlog_apply, Units.coe_map] at hLj
  have := (div_eq_zero_iff.1 hLj).resolve_right (by
    have := GlobalTheory.TautRigid.fst_ne_zero (Units.map ρ.toMonoidHom (u j))
    rwa [Units.coe_map] at this)
  rw [← hu]
  exact this

end GlobalTheory.TorRigid
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasSiegelChart_of_polarisedMonomialPeriodChart : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] {G : Over S} [GrpObj G] (e : F.univ.A.left ⟶ G.left) (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S), n ≠ 0 → HasPolChart F s j e φ BD d x → HasChart F s j e φ BD d x := by
  first | exact @GlobalTheory.PolDeg.hasChart_of_hasPolChart | exact GlobalTheory.PolDeg.hasChart_of_hasPolChart | (intros; apply GlobalTheory.PolDeg.hasChart_of_hasPolChart <;> assumption)
end
