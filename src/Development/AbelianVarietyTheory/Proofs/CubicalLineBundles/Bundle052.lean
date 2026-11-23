module

import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle049
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle027
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle067
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle050
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbedding
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle011
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle047
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle051
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.DerivZero

theorem exists_lift_isMonHom {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H]
    [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hG : IsGrpPullback G' G j φ)
    (hH : IsGrpPullback H' H j ψ) (f : G ⟶ H) [IsMonHom f] :
    ∃ f' : G' ⟶ H', IsMonHom f' ∧ f'.left ≫ ψ = φ ≫ f.left := by
  apply GlobalTheory.NormHom.exists_monHom_lift <;> assumption

end GlobalTheory.DerivZero
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FamDescent

theorem lamEq_descend {R k : Type} [CommRing R] [IsDedekindDomain R] [Field k] (f : R →+* k)
    (hf : Function.Injective f) {X Y A B : Over (Sp R)} {X' Y' A' B' : Over (Sp k)} [GrpObj X] [GrpObj Y]
    [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj A'] [IsCommMonObj A'] [GrpObj B'] [IsCommMonObj B']
    (hX : IsAbelianScheme X) (hY : IsAbelianScheme Y)
    {x : X'.left ⟶ X.left} {y : Y'.left ⟶ Y.left} {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left}
    (hx : IsPullback x X'.hom X.hom (spMap f)) (hy : IsPullback y Y'.hom Y.hom (spMap f))
    (hA : IsGrpPullback A' A (spMap f) a) (hB : IsGrpPullback B' B (spMap f) b)
    {L : LB A.left} {M : LB B.left} {L' : LB A'.left} {M' : LB B'.left}
    (hL : L.IsLB) (hM : M.IsLB) (hL' : L'.IsLB) (hM' : M'.IsLB) (iL : LBIso (L.pull a) L') (iM : LBIso (M.pull b) M')
    {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B} [IsMonHom f₁] [IsMonHom f₂] [IsMonHom g₁] [IsMonHom g₂]
    {f₁' : X' ⟶ A'} {f₂' : Y' ⟶ A'} {g₁' : X' ⟶ B'} {g₂' : Y' ⟶ B'}
    (e₁ : f₁'.left ≫ a = x ≫ f₁.left) (e₂ : f₂'.left ≫ a = y ≫ f₂.left)
    (e₃ : g₁'.left ≫ b = x ≫ g₁.left) (e₄ : g₂'.left ≫ b = y ≫ g₂.left)
    (H : LamEq L' f₁' f₂' M' g₁' g₂') : LamEq L f₁ f₂ M g₁ g₂ := by
  obtain ⟨Pic, _, cl, pl, hiso, -, -, hcomp, hlin, -⟩ := CechPicMul.exists_picardGroup
  have hpull : ∀ {U V : Scheme.{0}} (N : LB U), N.IsLB → ∀ g : V ⟶ U, (N.pull g).IsLB ∧ cl (N.pull g) = pl g (cl N) :=
    fun N hN g => ⟨(hlin _ _ N hN _ _ _).1, (hlin _ _ N hN _ _ _).2.trans (by simp)⟩
  let π := pullback.fst (X ⊗ Y).hom (spMap f)
  let p := pullback.snd (X ⊗ Y).hom (spMap f)
  have hπ : π ≫ (X ⊗ Y).hom = p ≫ spMap f := pullback.condition
  let u : Over.mk p ⟶ X' := Over.homMk (hx.lift (π ≫ (fst X Y).left) p (by rw [Category.assoc, Over.w, hπ]))
    (hx.lift_snd _ _ _)
  let v : Over.mk p ⟶ Y' := Over.homMk (hy.lift (π ≫ (snd X Y).left) p (by rw [Category.assoc, Over.w, hπ]))
    (hy.lift_snd _ _ _)
  have hu : u.left ≫ x = π ≫ (fst X Y).left := hx.lift_fst _ _ _
  have hv : v.left ≫ y = π ≫ (snd X Y).left := hy.lift_fst _ _ _
  let U : Over.mk ((Over.mk p).hom ≫ spMap f) ⟶ X ⊗ Y := Over.homMk π hπ
  have gen : ∀ {C : Over (Sp R)} {C' : Over (Sp k)} [GrpObj C] [GrpObj C'] {c : C'.left ⟶ C.left}
      (hC : IsGrpPullback C' C (spMap f) c) {N : LB C.left} {N' : LB C'.left}, N.IsLB → N'.IsLB →
      LBIso (N.pull c) N' → ∀ (s : X ⟶ C) (t : Y ⟶ C) (s' : X' ⟶ C') (t' : Y' ⟶ C'),
      s'.left ≫ c = x ≫ s.left → t'.left ≫ c = y ≫ t.left →
      cl ((cubeLB C ![fst X Y ≫ s, snd X Y ≫ t] N).pull π) = cl (cubeLB C' ![u ≫ s', v ≫ t'] N') := by
    intro C C' _ _ c hC N N' hN hN' iN s t s' t' hs ht
    have e : pl c (cl N) = cl N' := (hpull N hN c).2.symm.trans ((hiso _ _ _ (hpull N hN c).1 hN').2 iN)
    refine (hpull _ (LamCalc.cubeLB_isLB hN _) π).2.trans ?_
    refine (congrArg (pl π) (hlin _ _ N hN _ _ _).2).trans (Eq.trans ?_ (hlin _ _ N' hN' _ _ _).2.symm)
    rw [map_prod]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [map_zpow, ← hcomp, ← e, ← hcomp]
    refine congrArg (fun z => pl z (cl N) ^ _) (Eq.symm ?_)
    refine lamBC_psum_push hC _ _ U (fun i => ?_) I.down
    fin_cases i
    · refine Over.OverMorphism.ext ?_
      show (u.left ≫ s'.left) ≫ c = π ≫ (fst X Y).left ≫ s.left
      rw [Category.assoc, hs, ← Category.assoc, hu, Category.assoc]
    · refine Over.OverMorphism.ext ?_
      show (v.left ≫ t'.left) ≫ c = π ≫ (snd X Y).left ≫ t.left
      rw [Category.assoc, ht, ← Category.assoc, hv, Category.assoc]
  have zero : ∀ {C : Over (Sp R)} [GrpObj C] [IsCommMonObj C] {N : LB C.left}, N.IsLB →
      ∀ (s : X ⟶ C) (t : Y ⟶ C), IsMonHom s → IsMonHom t →
      cl ((cubeLB C ![fst X Y ≫ s, snd X Y ≫ t] N).pull (eSec (X ⊗ Y))) = 1 := by
    intro C _ _ N hN s t _ _
    refine (hpull _ (LamCalc.cubeLB_isLB hN _) _).2.trans ?_
    rw [LamCalc.class_cubeLB cl (fun z => pl z (cl N)) (fun I _ φ ε => (hlin _ _ N hN I φ ε).2)]
    have w : ∀ z : X ⊗ Y ⟶ C, η[X ⊗ Y] ≫ z = 1 →
        pl (eSec (X ⊗ Y)) (pl z.left (cl N)) = pl (1 : 𝟙_ (Over (Sp R)) ⟶ C).left (cl N) := fun z hz => by
      rw [← hcomp, ← hz]; rfl
    have o : (1 : 𝟙_ (Over (Sp R)) ⟶ C) = η[C] := by simp [Hom.one_def]
    have h₁ : η[X ⊗ Y] ≫ fst X Y ≫ s = 1 := by rw [o]; exact IsMonHom.one_hom _
    have h₂ : η[X ⊗ Y] ≫ snd X Y ≫ t = 1 := by rw [o]; exact IsMonHom.one_hom _
    simp only [map_mul, map_inv]
    rw [w _ h₁, w _ h₂, w 1 (MonObj.comp_one _), w _ (by rw [MonObj.comp_mul, h₁, h₂, _root_.mul_one])]
    simp
  have cL := LamCalc.cubeLB_isLB hL ![fst X Y ≫ f₁, snd X Y ≫ f₂]
  have cM := LamCalc.cubeLB_isLB hM ![fst X Y ≫ g₁, snd X Y ≫ g₂]
  refine GlobalTheory.T.lineBundleIso_descends_field_to_dedekindDomain R k f hf (X ⊗ Y) (AbelianSchemeGerms.isAbelianScheme_tensor X Y hX hY) _ π p (IsPullback.of_hasPullback _ _)
    _ _ cL cM ?_ ?_
  · exact (hiso _ _ _ (hpull _ cL _).1 (hpull _ cM _).1).1
      ((zero hL f₁ f₂ ‹_› ‹_›).trans (zero hM g₁ g₂ ‹_› ‹_›).symm)
  · refine (hiso _ _ _ (hpull _ cL _).1 (hpull _ cM _).1).1
      ((gen hA hL hL' iL _ _ _ _ e₁ e₂).trans (Eq.trans ?_ (gen hB hM hM' iM _ _ _ _ e₃ e₄).symm))
    exact (hiso _ _ _ (LamCalc.cubeLB_isLB hL' _) (LamCalc.cubeLB_isLB hM' _)).2 (LamCalc.lbIso_of_lamEq H u v)

theorem isFam_descend : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDedekindDomain R] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (k : Type) [Field k] (ω' : k) (C' : Ell H k ω') (f : R →+* k) (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp k)) (m : SABMap T'.t T.t (spMap f)) (ψ' : L → (C'.P.A ⟶ T'.t.G)), Function.Injective f → EllMap C' C f φ → (∀ a, (ψ' a).left ≫ m.φ = φ ≫ (ψ a).left) → IsFam C' T' h L ψ' → IsFam C T h L ψ := by
  intro _ E _ _ _ H R _ _ ω C D h T L ψ k _ ω' C' f φ T' m ψ' hf hE hψ hF
  obtain ⟨-, ⟨-, hC, iC⟩, -, hact⟩ := hE
  obtain ⟨hlin, hadd, hsm, hlam⟩ := hF
  have : IsSchemeTheoreticallyDominant (spMap f) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom f) hf
  have : QuasiCompact (spMap f) := inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom f)))
  have := C.P.isAb.smooth
  have : Flat C.P.A.hom := inferInstance
  have : IsSeparated T.t.G.hom := T.t.semi.separated
  have hm : ∀ a, IsMonHom (ψ a) := fun a =>
    have := (hlin a).isMonHom
    ExtUnique.isMonHom_of_isGrpPullback hC m.cart (ψ' a) (ψ a) (hψ a)
  refine ⟨fun a => ⟨hm a, fun c => ?_⟩, fun a b => ?_, fun s a => ?_, fun a b => ?_⟩
  · refine ExtUnique.over_hom_ext_of_isPullback (j := spMap f) hC.1 ?_
    have e := congrArg (fun z => z.left ≫ m.φ) ((hlin a).comm c)
    simp only [Over.comp_left, Category.assoc, Serre.comapAct_act] at e ⊢
    rw [hψ, m.act, ← Category.assoc, ← Category.assoc, hact, hψ, Category.assoc, Category.assoc] at e
    exact e
  · refine ExtUnique.over_hom_ext_of_isPullback (j := spMap f) hC.1 ?_
    let φ₀ : Over.mk (C'.P.A.hom ≫ spMap f) ⟶ C.P.A := Over.homMk φ hC.1.w
    have e := m.cart.2 C'.P.A (ψ' a) (ψ' b) (φ₀ ≫ ψ a) (φ₀ ≫ ψ b) (hψ a).symm (hψ b).symm
    rw [← MonObj.comp_mul] at e
    rw [← hψ, hadd, ← e]
    rfl
  · refine ExtUnique.over_hom_ext_of_isPullback (j := spMap f) hC.1 ?_
    rw [← hψ, hsm, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hψ, Category.assoc]
  · have := hm a
    have := hm b
    have := C.act.hom (h a b)
    exact lamEq_descend f hf C.P.isAb C.P.isAb hC.1 hC.1 m.cart hC T.t.PP.isLB C.P.isLB T'.t.PP.isLB C'.P.isLB
      (LBIso.symm (show LBIso T'.t.PP.L (T.t.PP.L.pull m.φ) from m.lin.imp fun _ h => h.1))
      iC (hψ a) (hψ b) (hact _) (by simp) (hlam a b)

end GlobalTheory.FamDescent

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.exists_tensorProduct_hom_of_cmCurveHomFamily : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D₁ D : Datum H) (ε : ℤˣ) (h₁ : D₁.La → D₁.La → OK H) (h : D.La → D.La → OK H) (T₁ T : PAT H (Sp R)) (t : IsTen C D₁ h₁ T₁) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (f : D₁.La →ₗ[𝓞 E] L) (c : 𝓞 E), IsKForm D₁ ε h₁ → IsKForm D ε h → (∀ a b, D.EF (f a) (f b) = D₁.EF (c • a) b) → IsFam C T h L ψ →
  ∃ Φ : T₁.t.G ⟶ T.t.G, Serre.IsLinearHom T₁.t.act T.t.act Φ ∧ (∀ a, t.ten.tmul a ≫ Φ = ψ (f a)) ∧ LamEq T.t.PP.L Φ Φ T₁.t.PP.L (T₁.t.act.act c) (𝟙 T₁.t.G) := by
  first | exact @GlobalTheory.CM.exists_famLift | exact GlobalTheory.CM.exists_famLift | (intros; apply GlobalTheory.CM.exists_famLift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.exists_inverse_isogeny_of_surjective_points : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp (𝓞 K))) (Φ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom Φ → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P'.A, ∃ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P.A, y = x ≫ Φ) → ∃ (N : ℕ) (ψ : P'.A ⟶ P.A), 0 < N ∧ IsMonHom ψ ∧ Φ ≫ ψ = 𝟙 P.A ^ N ∧ ψ ≫ Φ = 𝟙 P'.A ^ N := by
  first | exact @GlobalTheory.LamF.exists_inverse_isogeny_ringOfIntegers | exact GlobalTheory.LamF.exists_inverse_isogeny_ringOfIntegers | (intros; apply GlobalTheory.LamF.exists_inverse_isogeny_ringOfIntegers <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem hom_deriv_baseChange : ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (R₀ : Type) [CommRing R₀] (ρ : R →+* R₀) (P₀ Q₀ : Out.PolAV (Sp R₀)) (φ : P₀.A.left ⟶ P.A.left) (ψ : Q₀.A.left ⟶ Q.A.left) (v₀ : epsR R₀ ⟶ P₀.A) (t₀ : epsR R₀ ⟶ Q₀.A) (f : P₀.A ⟶ Q₀.A) (a : R₀), IsPolFibre ρ P P₀ φ → IsPolFibre ρ Q Q₀ ψ → IsVecOver ρ φ v v₀ → IsVecOver ρ ψ t t₀ → IsMonHom f → IsLieComb ![a] ![t₀] (v₀ ≫ f) → ∀ (R₁ : Type) [CommRing R₁] (g : R₀ →+* R₁), (∀ (P₁ Q₁ : Out.PolAV (Sp R₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR R₁ ⟶ P₁.A) (t₁ : epsR R₁ ⟶ Q₁.A), IsPolFibre (g.comp ρ) P P₁ φ₁ → IsPolFibre (g.comp ρ) Q Q₁ ψ₁ → IsVecOver (g.comp ρ) φ₁ v v₁ → IsVecOver (g.comp ρ) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![g a] ![t₁] (v₁ ≫ f₁)) := by
  intro R _ P Q v t R₀ _ ρ P₀ Q₀ φ ψ v₀ t₀ f a hP hQ hv ht hf hlie R₁ _ g P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP₁ hQ₁ hv₁ ht₁

  obtain ⟨φ', hφ', hφφ⟩ := PolFibre.cancel hP hP₁
  obtain ⟨ψ', hψ', hψψ⟩ := PolFibre.cancel hQ hQ₁
  have hv' : IsVecOver g φ' v₀ v₁ :=
    (PolFibre.vec_iff hP.2.1.1 hφ'.2.1.1.w hv).mpr (by rw [hφφ]; exact hv₁)
  have ht' : IsVecOver g ψ' t₀ t₁ :=
    (PolFibre.vec_iff hQ.2.1.1 hψ'.2.1.1.w ht).mpr (by rw [hψψ]; exact ht₁)

  have hsq : (φ' ≫ f.left) ≫ Q₀.A.hom = P₁.A.hom ≫ spMap g := by
    rw [Category.assoc, Over.w f]
    exact hφ'.2.1.1.w
  let f₁ : P₁.A ⟶ Q₁.A :=
    Over.homMk (hψ'.2.1.1.lift (φ' ≫ f.left) P₁.A.hom hsq) (hψ'.2.1.1.lift_snd _ _ _)
  have hf₁ : f₁.left ≫ ψ' = φ' ≫ f.left := hψ'.2.1.1.lift_fst _ _ _
  have : IsMonHom f := hf
  refine ⟨f₁, GlobalTheory.UU.isMonHom_of_over_isMonHom hφ'.2.1 hψ'.2.1 f f₁ hf₁, ?_⟩

  have hw : (v₁ ≫ f₁).left ≫ ψ' = spMap (Chart.dualMapR g) ≫ (v₀ ≫ f).left := by
    have e : v₁.left ≫ φ' = spMap (Chart.dualMapR g) ≫ v₀.left := hv'
    simp only [Over.comp_left, Category.assoc, hf₁]
    rw [← Category.assoc, e, Category.assoc]
  have key := (lieComb_baseChange R₀ R₁ g Q₀.A Q₁.A ψ' hψ'.2.1 1 ![t₀] (v₀ ≫ f) ![a] ![t₁] (v₁ ≫ f₁)
    (by intro j; fin_cases j; exact ht') hlie).mp hw
  convert key using 1
  funext i
  fin_cases i
  rfl

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem exists_polAV_latticeFamily : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) ∧ ∀ s : R →+* ℂ, s W.c₄ = 12 * (Lf s).g₂ ∧ s W.c₆ = 216 * (Lf s).g₃ ∧ s W.Δ = (Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) := by
  intro hU hB R _ W hΔ
  obtain ⟨P, v, hg, hv, hbc, hs⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_lieBasis_invariants R W hΔ
  have hex : ∀ s : R →+* ℂ, ∃ L : PeriodPair, s W.c₄ = 12 * L.g₂ ∧ s W.c₆ = 216 * L.g₃ ∧
      s W.Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := fun s => by
    obtain ⟨P', φ, h⟩ := exists_isPolFibre hB s P
    obtain ⟨v', hv', -⟩ := existsUnique_isVecOver h.2.1.1 v
    obtain ⟨rig, hrig⟩ := P'.rigid
    obtain ⟨u, Hm, χ, -, -, -, hd, -⟩ := hU P' rig hrig
    obtain ⟨w, hw, -⟩ := hd v' (hv'.isTangent h.2.1 (hv.1 0))
    obtain ⟨-, L, -, hL⟩ := hs s P' φ v' u w h hv' hw
    exact ⟨L, hL⟩
  choose Lf hLf using hex
  refine ⟨P, v, Lf, ⟨hg, hv, hbc, fun s P' φ v' u w h hv' hw => ?_⟩, hLf⟩
  obtain ⟨hw0, L, hL, h4, h6, -⟩ := hs s P' φ v' u w h hv' hw
  have e : (Lf s).lattice = L.lattice :=
    lattice_eq_of_g₂_eq_of_g₃_eq
      (mul_left_cancel₀ (by norm_num : (12 : ℂ) ≠ 0) ((hLf s).1.symm.trans h4))
      (mul_left_cancel₀ (by norm_num : (216 : ℂ) ≠ 0) ((hLf s).2.1.symm.trans h6))
  exact ⟨hw0, fun z => e ▸ hL z⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

private lemma mem_range_algebraMap_iff_valV_le_one (T : CDVR) (x : T.Fr) :
    x ∈ Set.range (algebraMap T.V T.Fr) ↔ valV T.V x ≤ 1 := by
  unfold valV
  constructor
  · rintro ⟨r, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one r
  · intro h
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h
    exact ⟨a, ha⟩

private lemma withZero_le_one_iff_log_nonpos {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) : x ≤ 1 ↔ WithZero.log x ≤ 0 := by
  conv_lhs => rw [← WithZero.exp_log hx, ← WithZero.exp_zero]
  exact WithZero.exp_le_exp

theorem exists_cdvr_completion_integral_iff :
    ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)),
      ∃ (T : CDVR) (iK : K →+* T.Fr), T.FinRes ∧
        ∀ y : K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation K y ≤ 1 := by
  intro K _ _ p

  obtain ⟨T, k, e, hO, hfin⟩ := locFld K K (RingHom.id K) p
  unfold OverLa vV vLa at hO
  obtain ⟨he, hv⟩ := hO
  simp only [RingHom.comp_id] at hv
  refine ⟨T, k, hfin, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, map_zero]
    exact ⟨fun _ => zero_le, fun _ => ⟨0, map_zero _⟩⟩
  · have hky : k y ≠ 0 := (map_ne_zero k).2 hy
    have ha : valV T.V (k y) ≠ 0 := by
      unfold valV
      exact (Valuation.ne_zero_iff _).2 hky
    have hb : p.valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy

    rw [mem_range_algebraMap_iff_valV_le_one, withZero_le_one_iff_log_nonpos ha, withZero_le_one_iff_log_nonpos hb]
    have h := hv y
    have he' : (0 : ℤ) < e := by exact_mod_cast he
    constructor <;> intro h' <;> nlinarith

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.exists_cmPoint_lattice_data_of_adapted_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), IsUnf U → 0 < r → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (W : PullbackSections.UnfAt U k x₀) (Xx : FD.DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → ∀ (La : ℝ) (lam : Fin r → Fin r → E), FD.LamBasis Xx La (hX ▸ x₀.1) lam → ∃ Z : CMLat W.per Dw.p Dw.q, ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ La ^ 2 := by
  first | exact @GlobalTheory.LamT.CMBasis.exists_cmLat_unfAt | exact GlobalTheory.LamT.CMBasis.exists_cmLat_unfAt | (intros; apply GlobalTheory.LamT.CMBasis.exists_cmLat_unfAt <;> assumption)
end
