module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle078
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3119
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3382
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finExt_cubicalSymmetric_even_factor : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (A₀ : PolAV (Sp (FractionRing R₀))) (gen₀ : (Over.pullback (jK R₀)).obj G₀ ≅ A₀.A), FinExt ρ₀ ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P ∧ IsMonHom gen₀.hom ∧ LBIso (A₀.L.pull gen₀.hom.left) (P.L.L.pull (pullback.fst G₀.hom (jK R₀)))) := by
  first | exact @GlobalTheory.Mum.exists_finExt_cp_factor_even | exact GlobalTheory.Mum.exists_finExt_cp_factor_even | (intros; apply GlobalTheory.Mum.exists_finExt_cp_factor_even <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsion_theta_values_abelianPart_defined_over : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ') (lam : Sp V ⟶ F'.X) (β : Q.B.left ⟶ F'.univ.A.left) (β₂ : (G2 Q.B).left ⟶ (G2 F'.univ.A).left), 1 ≤ n' → DefOver k₀ (spMap (ev.comp ρ) ≫ lam ≫ F'.s) → IsGrpPullback Q.B F'.univ.A lam β → IsSquare β β₂ → LBIso (abelian₂ Q.B Q.M.L) (F'.univ.P.pull β₂) → ∀ a, DefOver k₀ (spMap (ev.comp ρ) ≫ (Q.c a).left ≫ β) := by
  first | exact @GlobalTheory.Poinc.Sep.torsion_theta_points_defOver | exact GlobalTheory.Poinc.Sep.torsion_theta_points_defOver | (intros; apply GlobalTheory.Poinc.Sep.torsion_theta_points_defOver <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (z₁ : X₁.M.Z) (x₀ : X₁.S.Gam), x₀ ∈ X₁.S.supI X₁.M z₁ → ∀ (z' : D.X.M.Z), D.q z' = z₁ → D.X.M.Div D.X.S.th (D.lab x₀) z' := by
  first | exact @GlobalTheory.Poinc.DivDeep.main | exact GlobalTheory.Poinc.DivDeep.main | (intros; apply GlobalTheory.Poinc.DivDeep.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.AbLevel

theorem torsRat_of_isGrpPullback {R O : Type} [CommRing R] [IsDomain R] [CommRing O] [IsDomain O] (ρ : R →+* O)
    (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] {A : Over (Sp O)} [GrpObj A] {π : A.left ⟶ G.left}
    (hπ : IsGrpPullback A G (spMap ρ) π) {n : ℕ} (h : TorsRat G n) : TorsRat A n := by
  intro K _ _ κ x hx
  have hj : Function.Injective ((algebraMap O (FractionRing O)).comp ρ) :=
    (IsFractionRing.injective O (FractionRing O)).comp hρ
  let i : FractionRing R →+* FractionRing O := IsFractionRing.lift hj
  have hsq : spMap i ≫ jK R = jK O ≫ spMap ρ := by
    show spMap i ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap O (FractionRing O)) ≫ spMap ρ
    rw [← spMap_comp, ← spMap_comp]
    have hi : ∀ r, i (algebraMap R (FractionRing R) r) = algebraMap O (FractionRing O) (ρ r) := fun r =>
      IsFractionRing.lift_algebraMap (K := FractionRing R) hj r
    exact congrArg spMap (RingHom.ext hi)
  let x0 := GlobalTheory.ObjPull.pushEquiv hπ _ x
  have hx0 : x0 ^ n = 1 := by simp only [x0, ← map_pow, hx, map_one]
  have hT : spMap (κ.comp i) ≫ jK R = (Over.mk (spMap κ ≫ jK O)).hom ≫ spMap ρ := by
    show _ = (spMap κ ≫ jK O) ≫ spMap ρ
    rw [spMap_comp, Category.assoc, hsq, Category.assoc]
  let e : Over.mk (spMap (κ.comp i) ≫ jK R) ⟶ Over.mk ((Over.mk (spMap κ ≫ jK O)).hom ≫ spMap ρ) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hT.symm)
  obtain ⟨y, hy⟩ := h K (κ.comp i) (e ≫ x0) (by rw [← MonObj.comp_pow, hx0, MonObj.comp_one])
  have hy' : x.left ≫ π = spMap κ ≫ spMap i ≫ y.left := by
    have e₁ : x.left ≫ π = (e ≫ x0).left := (Category.id_comp _).symm
    exact e₁.trans (hy.trans ((congrArg (· ≫ y.left) (spMap_comp i κ)).trans (Category.assoc _ _ _)))
  have hz : (spMap i ≫ y.left) ≫ G.hom = jK O ≫ spMap ρ := by
    rw [Category.assoc, Over.w y]
    exact hsq
  refine ⟨Over.homMk (hπ.1.lift _ (jK O) hz) (hπ.1.lift_snd _ _ _), hπ.1.hom_ext ?_ ?_⟩
  · show x.left ≫ π = (spMap κ ≫ hπ.1.lift _ (jK O) hz) ≫ π
    rw [Category.assoc, hπ.1.lift_fst, hy']
  · show x.left ≫ A.hom = (spMap κ ≫ hπ.1.lift _ (jK O) hz) ≫ A.hom
    rw [Category.assoc, hπ.1.lift_snd]
    exact Over.w x

theorem exists_factor {S S' T : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] {H : Over T} [GrpObj H]
    {f : S' ⟶ S} {t : T ⟶ S'} {u : T ⟶ S} (hu : t ≫ f = u) {π : A.left ⟶ G.left} {π₂ : (A ⊗ A).left ⟶ (G ⊗ G).left}
    (hπ : IsGrpPullback A G f π) (sπ : IsSquare π π₂) {a : H.left ⟶ G.left} {a₂ : (H ⊗ H).left ⟶ (G ⊗ G).left}
    (ha : IsGrpPullback H G u a) (sa : IsSquare a a₂) :
    ∃ (ψ : H.left ⟶ A.left) (ψ₂ : (H ⊗ H).left ⟶ (A ⊗ A).left), IsGrpPullback H A t ψ ∧ IsSquare ψ ψ₂ ∧ a₂ = ψ₂ ≫ π₂ := by
  let ψ := hπ.1.lift a (H.hom ≫ t) (by rw [Category.assoc, hu]; exact ha.1.w)
  have hψ : ψ ≫ π = a := hπ.1.lift_fst _ _ _
  have hpb : IsGrpPullback H A t ψ := hπ.cancel (ha.congr hu.symm hψ.symm) (hπ.1.lift_snd _ _ _)
  have sψ := GlobalTheory.LamPull.exists_isSquare hpb.1.w
  exact ⟨ψ, _, hpb, sψ, GlobalTheory.LamPull.isSquare_unique sa (hψ ▸ AbPol.isSquare_comp sψ sπ)⟩

theorem sameFib_factor {S₁ S₂ S₁' S₂' T : Scheme.{0}} {G₁ : Over S₁} [GrpObj G₁] [IsCommMonObj G₁] {P₁ : LB (G2 G₁).left}
    {G₂ : Over S₂} [GrpObj G₂] [IsCommMonObj G₂] {P₂ : LB (G2 G₂).left} (h₁ : P₁.IsLB) (h₂ : P₂.IsLB)
    {A₁ : Over S₁'} [GrpObj A₁] [IsCommMonObj A₁] {A₂ : Over S₂'} [GrpObj A₂] [IsCommMonObj A₂]
    {f₁ : S₁' ⟶ S₁} {t₁ : T ⟶ S₁'} {u₁ : T ⟶ S₁} (e₁ : t₁ ≫ f₁ = u₁)
    {f₂ : S₂' ⟶ S₂} {t₂ : T ⟶ S₂'} {u₂ : T ⟶ S₂} (e₂ : t₂ ≫ f₂ = u₂)
    {π₁ : A₁.left ⟶ G₁.left} {q₁ : (G2 A₁).left ⟶ (G2 G₁).left} (p₁ : IsGrpPullback A₁ G₁ f₁ π₁) (s₁ : IsSquare π₁ q₁)
    {π₂ : A₂.left ⟶ G₂.left} {q₂ : (G2 A₂).left ⟶ (G2 G₂).left} (p₂ : IsGrpPullback A₂ G₂ f₂ π₂) (s₂ : IsSquare π₂ q₂)
    (h : SameFib G₁ P₁ u₁ G₂ P₂ u₂) : SameFib A₁ (P₁.pull q₁) t₁ A₂ (P₂.pull q₂) t₂ := by
  obtain ⟨H, _, _, a, a₂, a', a₂', ha, sa, ha', sa', e⟩ := h
  obtain ⟨ψ, ψ₂, hψ, sψ, rfl⟩ := exists_factor e₁ p₁ s₁ ha sa
  obtain ⟨χ, χ₂, hχ, sχ, rfl⟩ := exists_factor e₂ p₂ s₂ ha' sa'
  refine ⟨H, inferInstance, inferInstance, ψ, ψ₂, χ, χ₂, hψ, sψ, hχ, sχ, ?_⟩
  have c := (CechPic.cls_eq_iff (pull_isLB h₁ _) (pull_isLB h₂ _)).2 e
  apply (CechPic.cls_eq_iff (pull_isLB (pull_isLB h₁ _) _) (pull_isLB (pull_isLB h₂ _) _)).1
  rw [CechPic.cls_pull (pull_isLB h₁ _), CechPic.cls_pull (pull_isLB h₂ _), CechPic.cls_pull h₁, CechPic.cls_pull h₂,
    ← CechPic.pull_comp, ← CechPic.pull_comp]
  rwa [CechPic.cls_pull h₁, CechPic.cls_pull h₂] at c

theorem lbIso_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {N : LB Z} (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    {a : Y ⟶ X} {b : Z ⟶ Y} (e : LBIso M (L.pull a)) (e' : LBIso N (M.pull b)) : LBIso N (L.pull (b ≫ a)) := by
  have c := (CechPic.cls_eq_iff hM (pull_isLB hL _)).2 e
  have c' := (CechPic.cls_eq_iff hN (pull_isLB hM _)).2 e'
  apply (CechPic.cls_eq_iff hN (pull_isLB hL _)).1
  rw [c', CechPic.cls_pull hM, c, CechPic.cls_pull hL, CechPic.cls_pull hL,
    CechPic.pull_comp]

theorem siegPB_trans {h n : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    {s'' : S'' ⟶ Sp B} {u : SiegPre h n ζ s} {c : SiegPre h n ζ s'} {c' : SiegPre h n ζ s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (m' : SiegPB c' c f') (m : SiegPB c u f) : SiegPB c' u (f' ≫ f) := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨ψ, ψ₂, hψ, hs', hw', hl'⟩ := m'
  exact ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hψ.comp hφ, AbPol.isSquare_comp hs' hs, lbIso_comp u.isLB c.isLB c'.isLB hw hw', fun a =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))⟩

theorem exists_level : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → TorsRat G₁ n → ∀ (K : Type) [Field K] (κ : Localization.Away (∏ k, C.t k) →+* K) (x₀ : Sp K ⟶ F.X), x₀ ≫ F.s = spMap ((κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k)))).comp C.b) → SameFib F.univ.A F.univ.P x₀ G₁ P (spMap (κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))))) → ∃ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal ∧ (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) ∧ ∀ yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X, SiegPB c F.univ yU → yU ≫ F.s = spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b) → spMap κ ≫ yU = x₀ := by
  intro g n φ hn hodd F C G₁ _ _ P hM hab hT K _ κ x₀ hx₀ hsf
  obtain ⟨A, _, _, π₀, π₂, hπ, sπ, hA, hP⟩ := AbPol.exists_isPPol_away g n φ hn C G₁ P hM hab
  have hCN := hM.1
  have hPG := hM.2.2.2.1.1
  let t := ∏ k, C.t k
  let O := Localization.Away t
  have ht0 : t ≠ 0 := fun h0 => by
    have hu := (IsLocalization.Away.algebraMap_isUnit (S := O) t).map κ
    have : algebraMap C.R O t = 0 := (congrArg (algebraMap C.R O) h0).trans (map_zero _)
    rw [this, map_zero] at hu
    exact not_isUnit_zero hu
  haveI := hCN.1
  haveI := hCN.2.1
  have hle : Submonoid.powers t ≤ nonZeroDivisors C.R := powers_le_nonZeroDivisors_of_noZeroDivisors ht0
  haveI : IsDomain O := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing (Submonoid.powers t) _ inferInstance
  haveI : IsIntegrallyClosed O := isIntegrallyClosed_of_isLocalization O (Submonoid.powers t) hle
  have hTA : TorsRat A n := torsRat_of_isGrpPullback _ (IsLocalization.injective O hle) hπ hT
  let b : cycAway n →+* O := (algebraMap C.R O).comp C.b
  let c₀ : SiegPre g n (zetaAway n) (spMap (κ.comp b)) := GlobalTheory.LowChart.siegPull F.univ x₀ _ hx₀
  have pb₀ : SiegPB c₀ F.univ x₀ := GlobalTheory.LowChart.siegPB_siegPull _ _ _ _
  have hs₀ : SameFib c₀.A c₀.P (𝟙 _) A (P.pull π₂) (spMap κ) := by
    dsimp only [c₀, GlobalTheory.LowChart.siegPull]
    exact sameFib_factor F.univ.isLB hPG (Category.id_comp x₀) (spMap_comp _ _).symm
      (Pdiv.PullbackComparison.isGrpPullback x₀ F.univ.A) (Pdiv.PullbackComparison.isSquare x₀ F.univ.A) hπ sπ hsf
  obtain ⟨c, hc, hcc, a, a₂, ha, sa, ea⟩ := GlobalTheory.LevSpread.level_spreads n hn hodd O b A (P.pull π₂) hA hP hTA g K κ c₀
    (GlobalTheory.LowChart.principal_siegPull _ _ _ _ F.princ) hs₀
  refine ⟨c, hc, ⟨a ≫ π₀, a₂ ≫ π₂, (ha.comp hπ).congr (Category.id_comp _) rfl, AbPol.isSquare_comp sa sπ,
    lbIso_comp hPG (pull_isLB hPG _) c.isLB (GlobalTheory.lbIso_refl (pull_isLB hPG _)) ea⟩, fun yU hy hys => ?_⟩
  refine F.inj K _ _ _ c₀ ?_ (siegPB_trans hcc hy) pb₀
  rw [Category.assoc, hys, hx₀, ← spMap_comp, RingHom.comp_assoc]

end GlobalTheory.TChart.AbLevel
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.inj_of_canon : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R), Canon C → Inj C := by
  intro E _ _ _ H Dw l Xo c φ h₁ h₂ h₃ R _ _ _ hR C Cn R' _ _ _ hR' θ₁ θ₂ i₁ i₂ l₁ l₂ κ₁ κ₂ e₁ e₂ e
  have : IsNoetherianRing R' := hR'.1.1
  refine GlobalTheory.TChart.cuniq _ R R' Cn.ψ Cn.compl θ₁ θ₂ l₁ l₂ (MvPolynomial.ringHom_ext (fun w => ?_) (fun k => ?_))
  · exact RingHom.congr_fun
      (GlobalTheory.T.canonicalFamily_base_injections_agree Xo c φ h₁ h₂ h₃ R hR C Cn R' hR' θ₁ θ₂ i₁ i₂ l₁ l₂ κ₁ κ₂ e₁ e₂ e) w
  · exact GlobalTheory.T.localInjections_agree_canonicalFamily_coordinates Xo c φ h₁ h₂ h₃ R hR C Cn R' hR' θ₁ θ₂ i₁ i₂ l₁ l₂ κ₁ κ₂ e₁ e₂ e k
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


theorem _root_.GlobalTheory.T.twistedSum_exponents_differ_affine_two_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∃ ε1 ε2 : X₁.S.Gam → X₁.S.Gam → ℕ, (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ (ε1 (lab c) τ)) ∧ (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y2 → C → V2, 𝔪2.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪2 lab T sg c τ (ε2 (lab c) τ)) ∧ ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((ε1 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((ε2 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  first | exact @GlobalTheory.GSep.twistSum_exp_affine | exact GlobalTheory.GSep.twistSum_exp_affine | (intros; apply GlobalTheory.GSep.twistSum_exp_affine <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_isAdj : ∀ (K : Type) [Field K] (A B : AbVar K) (c : Pic A.X.left) (d : Pic B.X.left),
    IsAmpleCls c → ∀ f : A ⟶ B, ∃ (n : ℕ) (h : B ⟶ A), 0 < n ∧ IsAdj c d f n h := by
  intro K _ A B c d hc f
  obtain ⟨A', P, ⟨hP, -⟩, hdim⟩ := GlobalTheory.T.abelianVariety_exists_dual_pair K A
  obtain ⟨φ, hφ, hiso⟩ := GlobalTheory.T.exists_hom_to_dual_of_mumfordClass K A A' P hP hdim c
  obtain ⟨n, v, hn, -, -, hvφ⟩ := exists_quasiInverse_isogeny K A A' φ (hiso hc)
  have hadd : ∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ B.X),
      CechPic.pull (lift (a * a') t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) =
      CechPic.pull (lift a t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) +
      CechPic.pull (lift a' t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) := by
    intro Y a a' t
    simp only [lam_eq, CechPic.pull_lam, lift_fst_assoc, lift_snd, MonObj.mul_comp]
    simp only [← lam_eq]
    exact GlobalTheory.T.abelianVarietyMumfordClass_mul_left K B d Y _ _ t
  have hzero : CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ B.X)).left
      (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) = 0 := by
    rw [lam_eq, CechPic.pull_lam, lift_snd, CechPic.lam_one_right]
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom K A A' B P hP _ hadd hzero
  have hpow : ∀ (Y : Over (Sp K)) (a : Y ⟶ A.X) (b : Y ⟶ A'.X) (m : ℕ),
      AbDual.evc hP.isLB a (b ^ m) = m • AbDual.evc hP.isLB a b := by
    intro Y a b m
    induction m with
    | zero => rw [pow_zero, zero_smul, AbDual.evc_one_right hP.isLB hP.zero a]
    | succ m ih => rw [pow_succ, GlobalTheory.T.poincareClass_additive_in_dual_variable K A A' P hP Y a, ih, succ_nsmul]
  refine ⟨n, ψ ≫ v, hn, ?_⟩
  have e1 := congrArg (CechPic.pull (lift (fst A.X B.X) (snd A.X B.X ≫ (ψ ≫ v).hom)).left) hφ
  rw [lam_eq, CechPic.pull_lam, AbDual.pull_evc, lift_fst, lift_snd_assoc, lift_snd, ← lam_eq] at e1
  unfold IsAdj
  rw [e1]
  simp only [comp_hom, Category.assoc]
  rw [← comp_hom v φ, hvφ, nsmul_hom, id_hom, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, hpow, ← hψ,
    natCast_zsmul]

end GlobalTheory.AV.AbVar
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatV

theorem heat_values_of_isKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ → ∃ (iota : Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) →+* (FractionRing Ω)) (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, iota (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = (algebraMap Ω (FractionRing Ω)) (φ r)) ∧ (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑dt (fun a => ⇑(δL a)) (iota.mapMatrix Θ₁) u' p p' k s)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hab n v' D Ω _ _ _ φ x' δ dd' hcomp hx' hinv hδ hdd hinj g hg δL hδL
    Θ₁ DV hDV hKS
  have hc : (∏ i, tt i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => htt i
  obtain ⟨iota, hiota⟩ := GlobalTheory.T.exists_fractionField_map_basicOpen_formalPoint E H R t (∏ i, tt i) hc Ω φ x' hx' hinj
  obtain ⟨J, W, j, d, u, pf, pf', hW, hcov, hle, hfld, hlift, hglue⟩ :=
    GlobalTheory.T.exists_local_heatOperators_abelianLocus E H R t P m tt gam hmon htt hab _ rfl n v' D dd' hinv Θ₁ DV hDV hKS
  obtain ⟨dt, u', p, p', hdt, hval⟩ := GlobalTheory.T.local_heat_operator_values_ring_operator_fraction_field E H R t _ hc n v' D Ω φ x' δ dd' hcomp hx' hinv hδ hdd hinj g hg δL hδL Θ₁ DV hDV
    iota hiota J W j d u pf pf' hW hcov hle hfld hlift hglue
  refine ⟨iota, dt, u', p, p', hiota, hdt, ?_⟩
  rintro k hk s ⟨r0, σ, ω, hr0, hv, hω⟩
  obtain ⟨r, σ', hr, hσ'⟩ := GlobalTheory.T.glued_heat_operators_preserve_sections_up_to_constant E H R t _ hc n dd' (fun a => (hinv a).1) D Θ₁ DV hDV J W j d u pf pf' hW hcov hle hfld
    hlift hglue k σ r0
  obtain ⟨ω', hv', hω'⟩ := hval k hk σ σ' r r0 ω hσ' hv
  refine ⟨r * r0 ^ 2, σ', ω', mul_ne_zero hr (pow_ne_zero _ hr0), hv', ?_⟩
  have hz : ∀ a, δL a ((algebraMap Ω (FractionRing Ω)) (φ r0)) = 0 := fun a => by rw [hδL, hδ, map_zero]
  have hdc := hdt r0
  rw [hω', hω]
  simp only [map_mul, map_pow]
  generalize (algebraMap Ω (FractionRing Ω)) (φ r0) = c at hz hdc ⊢
  have h1 : ∀ a x, δL a (c * x) = c * δL a x := fun a x => by
    rw [Derivation.leibniz, hz, smul_zero, add_zero, smul_eq_mul]
  have h2 : dt (c * s) = c * dt s + s * dt c := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  simp only [ringOp, h1, h2, hdc, Finset.mul_sum]
  have e1 : ∀ a b, iota.mapMatrix Θ₁ a b * (c * δL a (δL b s)) = c * (iota.mapMatrix Θ₁ a b * δL a (δL b s)) :=
    fun a b => by ring
  have e2 : ∀ a, u' a * (c * δL a s) = c * (u' a * δL a s) := fun a => by ring
  simp only [e1, e2, ← Finset.mul_sum]
  ring

end GlobalTheory.HeatV
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.DeepDivG

variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

end GlobalTheory.GSep.DeepDivG

namespace GlobalTheory.GSep.DeepDivG

theorem tower_same {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) :
    GlobalTheory.Poinc.Same X₁.ρ (fun _ => 𝟙 _) 𝔗.X₂.ρ (fun _ => 𝟙 _) 𝔗.lam (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁) := by
  let f₂ : Sp 𝔗.X₂.Ω₁ ⟶ Sp 𝔗.X₂.S.R := spMap 𝔗.X₂.S.R.val.toRingHom
  let polPull {S S' : Scheme.{0}} (P : PolAV S) (f : S' ⟶ S) : PolAV S' := by
    exact {
      A := (Over.pullback f).obj P.A,
      isAb := TLinPf.isAb_pullback f P.A P.isAb,
      g := P.g,
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (isGrpPullback_pullback P.A f).1 P.smoothDim,
      L := P.L.pull (pullback.fst P.A.hom f),
      isLB := LB.isLB_pull P.isLB _,
      rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid,
      sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym,
      ample := by
        haveI := P.isAb.proper
        exact AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
      ktriv := by
        obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (LB.isLB_pull P.isLB (pullback.fst P.A.hom f))
        exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (LB.isLB_pull P.isLB _) ((isGen_iff w).1 hw) P.ktriv } 
  let P₀ := polPull 𝔗.X₂.ρ.P f₂
  let a' : P₀.A.left ⟶ 𝔗.X₂.ρ.P.A.left := pullback.fst 𝔗.X₂.ρ.P.A.hom f₂
  have hring : (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom = 𝔗.X₂.S.R.val.toRingHom.comp 𝔗.om := by
    ext x; exact (𝔗.om_eq x).symm
  have hsp : spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) = f₂ ≫ spMap 𝔗.om := by
    rw [hring]; exact Spec.map_comp (CommRingCat.ofHom 𝔗.om) (CommRingCat.ofHom 𝔗.X₂.S.R.val.toRingHom)
  have ha' : IsGrpPullback P₀.A 𝔗.X₂.ρ.P.A f₂ a' := isGrpPullback_pullback _ _
  have hr : LBIso P₀.L (𝔗.X₂.ρ.P.L.pull a') := ⟨idIso _, idIso_isGen P₀.isLB⟩
  refine ⟨P₀, a' ≫ 𝔗.φ, a', fun _ => 𝟙 _, ?_, ha', ?_, hr, ?_, ?_⟩
  · exact (ha'.comp 𝔗.cart).congr hsp.symm rfl
  · exact LBIso.trans P₀.isLB (pull_isLB 𝔗.X₂.ρ.P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hr (lbIso_pull_comp 𝔗.lb a')
  · intro E
    exact ⟨by simp, by simp⟩
  · intro x
    have hc : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ ≫ f₂ := by
      rw [Category.assoc, Over.w (𝔗.X₂.ρ.pt (𝔗.lam x))]
      simp [baseOver]
    refine ⟨pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc, ?_, ?_⟩
    · have hw : pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc ≫ a' = f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left :=
        pullback.lift_fst _ _ _
      have h3 : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.φ =
          spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) ≫ (X₁.ρ.pt x).left := by
        rw [Category.assoc, 𝔗.lam_pt, hsp, Category.assoc]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔗.φ) hw).trans h3)
    · exact pullback.lift_fst _ _ _

end GlobalTheory.GSep.DeepDivG


open GlobalTheory.GSep.DeepDivG in
theorem GlobalTheory.GSep.DeepDivG.div_lam : (∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → (∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁)) → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂) := by
  intro I X₁ z₁ act hact hunit 𝔗 z₂ hz₂ x₀ hx V _ _ _ ev X _ t δ _
  have hk : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  have hdvd : X₁.S.r * X₁.S.N ∣ 𝔗.X₂.S.r * 𝔗.X₂.S.N := ⟨𝔗.d, 𝔗.lev⟩
  obtain ⟨a, ha, hdv⟩ := GlobalTheory.GSep.exists_div_torsion 𝔗.X₂ z₂ _ (X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)) hdvd
  have hL : 0 < 𝔗.X₂.S.r * 𝔗.X₂.S.N := Nat.mul_pos 𝔗.X₂.S.r_pos (by have := 𝔗.X₂.S.N_ge; omega)
  choose x hxa using fun s => DivDeep.exists_eq_smul_of_smul_eq_zero hL hdvd (a s) (congrFun ha s)
  have hd : 𝔗.X₂.S.r * 𝔗.X₂.S.N / (X₁.S.r * X₁.S.N) = 𝔗.d := by
    rw [𝔗.lev]; exact Nat.mul_div_cancel_left _ hk
  rw [hd] at hxa
  obtain ⟨b, hb⟩ := 𝔗.lam_range x
  obtain rfl : 𝔗.lam b = a := hb.trans (funext hxa)
  obtain ⟨k, hk, e⟩ := DivDeep.same_ratio (GlobalTheory.GSep.DeepDivG.tower_same 𝔗) x₀ b
  set φ := algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁
  have h₁ : φ (X₁.S.th x₀) ≠ 0 := (map_ne_zero φ).2 hx.1
  have h₂ := hdv.1
  have h₃ : 𝔗.X₂.S.th (𝔗.lam x₀) * φ (X₁.S.th b) ≠ 0 := fun h => by
    rw [h, zero_pow hk.ne'] at e
    exact pow_ne_zero k (mul_ne_zero h₂ h₁) e.symm
  have h₄ := left_ne_zero_of_mul h₃
  have h₅ := right_ne_zero_of_mul h₃
  have hN : IsIntegrallyClosed (𝔗.X₂.M.O z₂) := RatModel.isIntegrallyClosed_O (fun z => by
    haveI := 𝔗.X₂.normal
    exact ⟨𝔗.X₂.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩) z₂
  have m₁ : 𝔗.X₂.S.th (𝔗.lam b) * φ (X₁.S.th x₀) / (𝔗.X₂.S.th (𝔗.lam x₀) * φ (X₁.S.th b)) ∈ 𝔗.X₂.M.O z₂ :=
    DivDeep.root_mem_O hN hk (by rw [div_pow, e, div_self (pow_ne_zero k (mul_ne_zero h₂ h₁))])
  have m₂ : φ (X₁.S.th b / X₁.S.th x₀) ∈ 𝔗.X₂.M.O z₂ := by
    obtain ⟨U, f, hU, hf⟩ := hx.2 b
    refine ⟨𝔗.p ⁻¹ᵁ U, 𝔗.p.app U f, show 𝔗.p z₂ ∈ U from hz₂ ▸ hU, ?_⟩
    refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
    rw [𝔗.p_pt, ← hf]
    exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hU⟩) f
  refine ⟨h₄, fun j => ?_⟩
  have := mul_mem (hdv.2 j) (mul_mem m₁ m₂)
  convert this using 1
  rw [map_div₀]
  field_simp
end
end
