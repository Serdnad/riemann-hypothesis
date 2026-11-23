module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle027
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem hasType_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap f)) (ρ : R) (p q : ℕ), (Function.Injective f → HasType H t.act ρ p q → HasType H t'.act (f ρ) p q) ∧ ((∀ (k : Type) [Field k] (β : R →+* k), Function.Injective β → ∃ β' : R' →+* k, β'.comp f = β ∧ Function.Injective β') → HasType H t'.act (f ρ) p q → HasType H t.act ρ p q) := by
  intro E _ _ _ H R R' _ _ f t t' m ρ p q
  have key : ∀ (k : Type) [Field k] (β' : R' →+* k) (τ : 𝓞 E →+* k) (n : ℕ),
      LieMult t'.act (spMap β') τ n ↔ LieMult t.act (spMap (β'.comp f)) τ n := fun k _ β' τ n => by
    have e : spMap β' ≫ spMap f = spMap (β'.comp f) := (Spec.map_comp _ _).symm
    rw [← e]
    exact LiePull.lieMult_pull _ _ _ t.G t'.G (spMap f) m.cm.F t.act t'.act m.cart m.act k _ τ n
  refine ⟨fun hf h k _ _ β' hβ' τ => ?_, fun hext h k _ _ β hβ τ => ?_⟩
  · rw [key, key]
    exact h k (β'.comp f) (hβ'.comp hf) τ
  · obtain ⟨β', rfl, hβ'⟩ := hext k β hβ
    rw [← key, ← key]
    exact h k β' hβ' τ

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_pat_of_obj :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), ∃ T : PAT H S, T.t = o.t ∧ T.g = Module.finrank ℚ E / 2 * (D.p + D.q) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ o =>
    ⟨⟨o.t, ObjDim.isAbelianScheme o, _, ObjDim.smoothOfRelativeDimension o, ObjDim.sym, o.ample, o.ktriv⟩, rfl, rfl⟩

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

theorem lamBC_psum_hom {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {T : Over S}
    {T' : Over S'} (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (x : Fin n → (T' ⟶ G'))
    (I : Finset (Fin n)) : ρ (psum G' x I) = psum G (fun i => ρ (x i)) I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact map_one ρ
  | cons k l ih => exact (map_mul ρ _ _).trans (congrArg (ρ (x k) * ·) ih)

theorem lamBC_psum_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ}
    (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T)
    (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) (I : Finset (Fin n)) :
    (psum G' x' I).left ≫ φ = U.left ≫ (psum G x I).left := by
  have e : pushPt h.1.w (psum G' x' I) = U ≫ psum G x I :=
    (lamBC_psum_hom (pushHom h T') x' I).trans ((congrArg (fun z => psum G z I) (funext hx)).trans
      (lamBC_psum_hom (preHom U) x I).symm)
  exact congrArg (fun z => z.left) e

theorem lamEq_baseChange : ∀ (S S' : Scheme.{0}) (s : S' ⟶ S) (X Y A B : Over S) (X' Y' A' B' : Over S') [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] (x : X'.left ⟶ X.left) (y : Y'.left ⟶ Y.left) (a : A'.left ⟶ A.left) (b : B'.left ⟶ B.left),
  x ≫ X.hom = X'.hom ≫ s → y ≫ Y.hom = Y'.hom ≫ s → IsGrpPullback A' A s a → IsGrpPullback B' B s b → ∀ (L : LB A.left) (M : LB B.left) (L' : LB A'.left) (M' : LB B'.left), L.IsLB → M.IsLB → L'.IsLB → M'.IsLB → LBIso (L.pull a) L' → LBIso (M.pull b) M' →
  ∀ (f₁ : X ⟶ A) (f₂ : Y ⟶ A) (g₁ : X ⟶ B) (g₂ : Y ⟶ B) (f₁' : X' ⟶ A') (f₂' : Y' ⟶ A') (g₁' : X' ⟶ B') (g₂' : Y' ⟶ B'),
  f₁'.left ≫ a = x ≫ f₁.left → f₂'.left ≫ a = y ≫ f₂.left → g₁'.left ≫ b = x ≫ g₁.left → g₂'.left ≫ b = y ≫ g₂.left → LamEq L f₁ f₂ M g₁ g₂ → LamEq L' f₁' f₂' M' g₁' g₂' := by
  intro S S' s X Y A B X' Y' A' B' _ _ _ _ x y a b hx hy hA hB L M L' M' hL hM hL' hM' iL iM
    f₁ f₂ g₁ g₂ f₁' f₂' g₁' g₂' e₁ e₂ e₃ e₄ H
  let p : Over.mk ((X' ⊗ Y').hom ≫ s) ⟶ X := Over.homMk ((fst X' Y').left ≫ x) (by
    show ((fst X' Y').left ≫ x) ≫ X.hom = (X' ⊗ Y').hom ≫ s
    rw [Category.assoc, hx, ← Category.assoc, Over.w])
  let q : Over.mk ((X' ⊗ Y').hom ≫ s) ⟶ Y := Over.homMk ((snd X' Y').left ≫ y) (by
    show ((snd X' Y').left ≫ y) ≫ Y.hom = (X' ⊗ Y').hom ≫ s
    rw [Category.assoc, hy, ← Category.assoc, Over.w])
  let U : Over.mk ((X' ⊗ Y').hom ≫ s) ⟶ X ⊗ Y := lift p q
  have key : ∀ {C : Over S} {C' : Over S'} [GrpObj C] [GrpObj C'] {c : C'.left ⟶ C.left}
      (hC : IsGrpPullback C' C s c) (u : X ⟶ C) (v : Y ⟶ C) (u' : X' ⟶ C') (v' : Y' ⟶ C'),
      u'.left ≫ c = x ≫ u.left → v'.left ≫ c = y ≫ v.left → ∀ I : Finset (Fin 2),
      (psum C' ![fst X' Y' ≫ u', snd X' Y' ≫ v'] I).left ≫ c =
        U.left ≫ (psum C ![fst X Y ≫ u, snd X Y ≫ v] I).left := by
    intro C C' _ _ c hC u v u' v' hu hv I
    refine lamBC_psum_push hC _ _ U (fun i => ?_) I
    fin_cases i
    · show pushPt hC.1.w (fst X' Y' ≫ u') = lift p q ≫ fst X Y ≫ u
      rw [lift_fst_assoc]
      refine Over.OverMorphism.ext ?_
      show ((fst X' Y').left ≫ u'.left) ≫ c = ((fst X' Y').left ≫ x) ≫ u.left
      rw [Category.assoc, hu, Category.assoc]
    · show pushPt hC.1.w (snd X' Y' ≫ v') = lift p q ≫ snd X Y ≫ v
      rw [lift_snd_assoc]
      refine Over.OverMorphism.ext ?_
      show ((snd X' Y').left ≫ v'.left) ≫ c = ((snd X' Y').left ≫ y) ≫ v.left
      rw [Category.assoc, hv, Category.assoc]
  have H₁ : LBIso (cubeLB A' ![fst X' Y' ≫ f₁', snd X' Y' ≫ f₂'] (L.pull a))
      (cubeLB B' ![fst X' Y' ≫ g₁', snd X' Y' ≫ g₂'] (M.pull b)) :=
    LBIso.chartPull
      (chartPullLinComb L a _ _ _ U.left fun I => key hA f₁ f₂ f₁' f₂' e₁ e₂ I.down)
      (chartPullLinComb M b _ _ _ U.left fun I => key hB g₁ g₂ g₁' g₂' e₃ e₄ I.down) H
  have hLa : (L.pull a).IsLB := DVR.linComb_isLB _ hL _ _
  have hMb : (M.pull b).IsLB := DVR.linComb_isLB _ hM _ _
  exact LBIso.trans (DVR.linComb_isLB _ hL' _ _) (DVR.linComb_isLB _ hLa _ _) (DVR.linComb_isLB _ hM' _ _)
    (PowPrimitive.lbIso_linComb iL.symm _ _)
    (LBIso.trans (DVR.linComb_isLB _ hLa _ _) (DVR.linComb_isLB _ hMb _ _) (DVR.linComb_isLB _ hM' _ _) H₁
      (PowPrimitive.lbIso_linComb iM _ _))

end GlobalTheory.CM

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.LieChar

variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G']

theorem isLieComb_one_iff (c : R) (v w : epsR R ⟶ G) :
    IsLieComb ![c] ![v] w ↔ w.left = spMap (epsScaleR c) ≫ v.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro h
    exact ⟨![w], fun i => by fin_cases i; exact h, by simp⟩

theorem isLieComb_comp {c : R} {v w : epsR R ⟶ G} (h : IsLieComb ![c] ![v] w) (f : G ⟶ G') :
    IsLieComb ![c] ![v ≫ f] (w ≫ f) := by
  rw [isLieComb_one_iff] at h ⊢
  simp [h]

theorem isTangent_comp {v : epsR R ⟶ G} (h : IsTangent v) (f : G ⟶ G') [IsMonHom f] :
    IsTangent (v ≫ f) := by
  unfold IsTangent at h ⊢
  rw [Over.comp_left, ← Category.assoc, h, ← Over.comp_left, IsMonHom.one_hom]

theorem spMap_epsScaleR_one : spMap (epsScaleR (1 : R)) = 𝟙 _ := by
  have : epsScaleR (1 : R) = RingHom.id _ := by
    ext x <;> simp [epsScaleR]
  rw [this]
  exact Spec.map_id _

theorem isLieComb_mul (x y : epsR R ⟶ G) : IsLieComb ![(1 : R), 1] ![x, y] (x * y) :=
  ⟨![x, y], fun i => by fin_cases i <;> simp [spMap_epsScaleR_one], by simp⟩

theorem exists_char [IsCommMonObj G] {O : Type} [CommRing O] (act : OAct O G) {v : epsR R ⟶ G}
    (hv : IsLieBasis ![v]) :
    ∃ τ : O →+* R, (∀ c, IsLieComb ![τ c] ![v] (v ≫ act.act c)) ∧
      ∀ c r, IsLieComb ![r] ![v] (v ≫ act.act c) → τ c = r := by
  have ht : ∀ c, IsTangent (v ≫ act.act c) := fun c => by
    haveI := act.hom c
    exact isTangent_comp (hv.1 0) _
  have e1 : ∀ d : Fin 1 → R, d = ![d 0] := fun d => by
    funext i; fin_cases i; rfl
  choose d hd hu using fun c => hv.2 _ (ht c)
  have hτ : ∀ c, IsLieComb ![d c 0] ![v] (v ≫ act.act c) := fun c => by
    rw [← e1]; exact hd c
  have huq : ∀ c r, IsLieComb ![r] ![v] (v ≫ act.act c) → d c 0 = r := fun c r h => by
    rw [← hu c _ h]; rfl
  obtain ⟨-, -, hcomp, -, -⟩ := GlobalTheory.LieComb.lieComb_algebra R G 1 ![v] hv.1
  have hone : d 1 0 = 1 := huq _ _ (by
    rw [isLieComb_one_iff, act.one, spMap_epsScaleR_one]; simp)
  have hmul : ∀ a b, d (a * b) 0 = d a 0 * d b 0 := fun a b => huq _ _ (by
    have := hcomp 1 ![![d b 0]] ![v ≫ act.act b] ![d a 0] _
      (fun i => by fin_cases i; exact hτ b) (isLieComb_comp (hτ a) (act.act b))
    rw [act.mul, ← Category.assoc]
    convert this using 1
    funext i; fin_cases i; simp)
  have hadd : ∀ a b, d (a + b) 0 = d a 0 + d b 0 := fun a b => huq _ _ (by
    have := hcomp 2 ![![d a 0], ![d b 0]] ![v ≫ act.act a, v ≫ act.act b] ![1, 1] _
      (fun i => by
        fin_cases i
        · exact hτ a
        · exact hτ b) (isLieComb_mul _ _)
    rw [act.add, MonObj.comp_mul]
    convert this using 1
    funext i; fin_cases i; simp)
  exact ⟨RingHom.mk' ⟨⟨fun c => d c 0, hone⟩, hmul⟩ hadd, hτ, huq⟩

theorem ell_char : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R)
    (C : Ell H R ω), ∃ τ₀ : OK H →+* R, τ₀ (wK H) = ω ∧ ∀ c, IsLieComb ![τ₀ c] ![C.v] (C.v ≫ C.act.act c) := by
  intro E _ _ _ H R _ ω C
  obtain ⟨τ, h, hu⟩ := exists_char C.act C.basis
  exact ⟨τ, hu _ _ C.eig, h⟩

end GlobalTheory.CM.LieChar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.LamCalc

open GlobalTheory.PrimNorm

section Tensor

variable {X X' Y : Scheme.{0}}

theorem exists_gen_tensor {C A B : LB Y} (a : C.ι → A.ι) (b : C.ι → B.ι) (la : ∀ i, C.U i ≤ A.U (a i))
    (lb : ∀ i, C.U i ≤ B.U (b i))
    (hg : ∀ (y : Y) i j, y ∈ C.U i → y ∈ C.U j → gm (𝟙 Y) y (C.U i ⊓ C.U j) (C.g i j) =
      gm (𝟙 Y) y (A.U (a i) ⊓ A.U (a j)) (A.g (a i) (a j)) * gm (𝟙 Y) y (B.U (b i) ⊓ B.U (b j)) (B.g (b i) (b j)))
    (s : LB.Gen A) (hs : s.IsGen) (t : LB.Gen B) (ht : t.IsGen) : ∃ u : LB.Gen C, u.IsGen := by
  refine ⟨⟨fun i => res (la i) (s.s (a i)) * res (lb i) (t.s (b i))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have ma : (𝟙 Y : Y ⟶ Y) y ∈ A.U (a i) ⊓ A.U (a j) := ⟨la i hy.1, la j hy.2⟩
  have mb : (𝟙 Y : Y ⟶ Y) y ∈ B.U (b i) ⊓ B.U (b j) := ⟨lb i hy.1, lb j hy.2⟩
  have ea := (gm_res _ y _ ma _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hs (a i) (a j))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gm_res _ y _ ma _))))
  have eb := (gm_res _ y _ mb _).symm.trans ((congrArg (gm (𝟙 Y) y _) (ht (b i) (b j))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gm_res _ y _ mb _))))
  have v : ∀ i, y ∈ C.U i → gm (𝟙 Y) y (C.U i) (res (la i) (s.s (a i)) * res (lb i) (t.s (b i))) =
      gm (𝟙 Y) y (A.U (a i)) (s.s (a i)) * gm (𝟙 Y) y (B.U (b i)) (t.s (b i)) := fun i hi =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hi _) (gm_res _ y _ hi _))
  refine ((gm_res _ y _ hy _).trans ((v i hy.1).trans (congrArg₂ (· * ·) ea eb))).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hg y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans (v j hy.2)))).trans ?_
  exact mul_mul_mul_comm _ _ _ _

theorem lbIso_sum {L : LB X} {M : LB X'} {K K' J J' : Type} [Fintype K] [Fintype K'] [Fintype J] [Fintype J']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {ψ : J → (Y ⟶ X')} {δ : J → ℤ} {ψ' : J' → (Y ⟶ X')} {δ' : J' → ℤ}
    (h : LBIso (LB.LinComb L φ ε) (LB.LinComb M ψ δ)) (h' : LBIso (LB.LinComb L φ' ε') (LB.LinComb M ψ' δ')) :
    LBIso (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')) (LB.LinComb M (Sum.elim ψ ψ') (Sum.elim δ δ')) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  have l₁ : ∀ p : (J ⊕ J' → M.ι) × (K ⊕ K' → L.ι),
      LB.wchart M (Sum.elim ψ ψ') p.1 ⊓ LB.wchart L (Sum.elim φ φ') p.2 ≤
        LB.wchart M ψ (p.1 ∘ Sum.inl) ⊓ LB.wchart L φ (p.2 ∘ Sum.inl) := fun p y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (.inl k)⟩
  have l₂ : ∀ p : (J ⊕ J' → M.ι) × (K ⊕ K' → L.ι),
      LB.wchart M (Sum.elim ψ ψ') p.1 ⊓ LB.wchart L (Sum.elim φ φ') p.2 ≤
        LB.wchart M ψ' (p.1 ∘ Sum.inr) ⊓ LB.wchart L φ' (p.2 ∘ Sum.inr) := fun p y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (.inr k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (.inr k)⟩
  refine exists_gen_tensor (C := LB.div (LB.LinComb M (Sum.elim ψ ψ') (Sum.elim δ δ'))
    (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε'))) (A := LB.div (LB.LinComb M ψ δ) (LB.LinComb L φ ε))
    (B := LB.div (LB.LinComb M ψ' δ') (LB.LinComb L φ' ε')) (fun p => (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl))
    (fun p => (p.1 ∘ Sum.inr, p.2 ∘ Sum.inr)) l₁ l₂ (fun y p q hp hq => ?_) w hw w' hw'
  refine ((gm_div _ _ (𝟙 Y) y p q ⟨hp, hq⟩).trans (congrArg₂ (fun a b => a * b⁻¹)
    (gm_linComb M _ _ (𝟙 Y) y p.1 q.1 hp.1 hq.1) (gm_linComb L _ _ (𝟙 Y) y p.2 q.2 hp.2 hq.2))).trans (Eq.symm ?_)
  refine (congrArg₂ (· * ·)
    ((gm_div (LB.LinComb L φ ε) (LB.LinComb M ψ δ) (𝟙 Y) y (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl) (q.1 ∘ Sum.inl, q.2 ∘ Sum.inl)
      ⟨l₁ p hp, l₁ q hq⟩).trans (congrArg₂ (fun a b => a * b⁻¹)
      (gm_linComb M ψ δ (𝟙 Y) y _ _ (l₁ p hp).1 (l₁ q hq).1) (gm_linComb L φ ε (𝟙 Y) y _ _ (l₁ p hp).2 (l₁ q hq).2)))
    ((gm_div (LB.LinComb L φ' ε') (LB.LinComb M ψ' δ') (𝟙 Y) y (p.1 ∘ Sum.inr, p.2 ∘ Sum.inr)
      (q.1 ∘ Sum.inr, q.2 ∘ Sum.inr) ⟨l₂ p hp, l₂ q hq⟩).trans (congrArg₂ (fun a b => a * b⁻¹)
      (gm_linComb M ψ' δ' (𝟙 Y) y _ _ (l₂ p hp).1 (l₂ q hq).1)
      (gm_linComb L φ' ε' (𝟙 Y) y _ _ (l₂ p hp).2 (l₂ q hq).2)))).trans ?_
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

end Tensor

section Cube

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  {L : LB A.left} {M : LB B.left} {T : Over S}

omit [IsCommMonObj A] in
theorem cubeLB_isLB (hL : L.IsLB) {n : ℕ} (x : Fin n → (T ⟶ A)) : (cubeLB A x L).IsLB :=
  DVR.linComb_isLB _ hL _ _

theorem class_cubeLB {U : Type*} [CommGroup U] (cl : LB T.left → U) (m : (T.left ⟶ A.left) → U)
    (h : ∀ (I : Type) [Fintype I] (φ : I → (T.left ⟶ A.left)) (ε : I → ℤ), cl (LB.LinComb L φ ε) = ∏ k, m (φ k) ^ ε k)
    (x y : T ⟶ A) :
    cl (cubeLB A ![x, y] L) = m (x * y).left * (m x.left)⁻¹ * (m y.left)⁻¹ * m (1 : T ⟶ A).left := by
  have e := congrArg (FreeGroup.lift m |> Abelianization.lift)
    (prod_square_id x y (fun q => Abelianization.of (FreeGroup.of q)))
  have hm (q : T.left ⟶ A.left) :
      (Abelianization.lift (FreeGroup.lift m)) (Abelianization.of (FreeGroup.of q)) = m q := by
    exact (Group.Abelianization.lift_apply_of _ _).trans FreeGroup.lift_apply_of
  simp only [diff₂, map_prod, map_zpow, map_mul, map_inv, hm] at e
  exact (h _ _ _).trans e

theorem lbIso_cubeLB_swap (hL : L.IsLB) (x y : T ⟶ A) : LBIso (cubeLB A ![x, y] L) (cubeLB A ![y, x] L) :=
  (lbIso_iff hL _ _ _ _).2 ((prod_square_id x y (cls L)).trans ((diff₂_comm _ _).trans
    (prod_square_id y x (cls L)).symm))

def cubeProd (L : LB A.left) (x y x' y' : T ⟶ A) : LB T.left :=
  LB.LinComb L (K := ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)))
    (Sum.elim (fun I => (psum A ![x, y] I.down).left) (fun I => (psum A ![x', y'] I.down).left))
    (Sum.elim (fun I => (-1) ^ (2 - I.down.card)) (fun I => (-1) ^ (2 - I.down.card)))

theorem lbIso_cubeLB_mul_left (hL : L.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen) (x x' y : T ⟶ A) :
    LBIso (cubeLB A ![x * x', y] L) (cubeProd L x y x' y) := by
  refine (lbIso_iff hL _ _ _ _).2 ((prod_square_id _ _ (cls L)).trans ?_)
  rw [Fintype.prod_sum_type]
  exact (diff₂_mul_left (diff₃_ptCls hL hT) x x' y).trans
    (congrArg₂ (· * ·) (prod_square_id x y (cls L)).symm (prod_square_id x' y (cls L)).symm)

theorem lbIso_cubeLB_mul_right (hL : L.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen) (x y y' : T ⟶ A) :
    LBIso (cubeLB A ![x, y * y'] L) (cubeProd L x y x y') := by
  refine (lbIso_iff hL _ _ _ _).2 ((prod_square_id _ _ (cls L)).trans ?_)
  rw [Fintype.prod_sum_type]
  exact (diff₂_mul_right (diff₃_ptCls hL hT) x y y').trans
    (congrArg₂ (· * ·) (prod_square_id x y (cls L)).symm (prod_square_id x y' (cls L)).symm)

theorem lbIso_cubeLB_mul_left_of (hL : L.IsLB) (hM : M.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen)
    (hT' : ∃ t : LB.Gen (Theta B M), t.IsGen) {x x' y : T ⟶ A} {u u' v : T ⟶ B}
    (h : LBIso (cubeLB A ![x, y] L) (cubeLB B ![u, v] M)) (h' : LBIso (cubeLB A ![x', y] L) (cubeLB B ![u', v] M)) :
    LBIso (cubeLB A ![x * x', y] L) (cubeLB B ![u * u', v] M) :=
  have a : (cubeProd L x y x' y).IsLB := DVR.linComb_isLB _ hL _ _
  have b : (cubeProd M u v u' v).IsLB := DVR.linComb_isLB _ hM _ _
  LBIso.trans (cubeLB_isLB hL _) a (cubeLB_isLB hM _) (lbIso_cubeLB_mul_left hL hT x x' y)
    (LBIso.trans a b (cubeLB_isLB hM _) (lbIso_sum h h') (lbIso_cubeLB_mul_left hM hT' u u' v).symm)

theorem lbIso_cubeLB_mul_right_of (hL : L.IsLB) (hM : M.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen)
    (hT' : ∃ t : LB.Gen (Theta B M), t.IsGen) {x y y' : T ⟶ A} {u v v' : T ⟶ B}
    (h : LBIso (cubeLB A ![x, y] L) (cubeLB B ![u, v] M)) (h' : LBIso (cubeLB A ![x, y'] L) (cubeLB B ![u, v'] M)) :
    LBIso (cubeLB A ![x, y * y'] L) (cubeLB B ![u, v * v'] M) :=
  have a : (cubeProd L x y x y').IsLB := DVR.linComb_isLB _ hL _ _
  have b : (cubeProd M u v u v').IsLB := DVR.linComb_isLB _ hM _ _
  LBIso.trans (cubeLB_isLB hL _) a (cubeLB_isLB hM _) (lbIso_cubeLB_mul_right hL hT x y y')
    (LBIso.trans a b (cubeLB_isLB hM _) (lbIso_sum h h') (lbIso_cubeLB_mul_right hM hT' u v v').symm)

theorem lbIso_cubeLB_hom (ψ : A ⟶ B) [IsMonHom ψ] (h : LBIso L (M.pull ψ.left)) (x y : T ⟶ A) :
    LBIso (cubeLB A ![x, y] L) (cubeLB B ![x ≫ ψ, y ≫ ψ] M) := by
  obtain ⟨w, hw⟩ := h
  let ρ : (T ⟶ A) →* (T ⟶ B) := MonoidHom.mk' (· ≫ ψ) fun x y => MonObj.mul_comp x y ψ
  refine (iso_linComb ((isGen_iff w).1 hw) _ _).chartPull (chartPullId _)
    (chartPullSame M _ _ _ (𝟙 _) fun I => ?_)
  have e : (fun i => ρ (![x, y] i)) = ![x ≫ ψ, y ≫ ψ] := funext fun i => by fin_cases i <;> rfl
  rw [Category.id_comp, ← e, ← psum_hom ρ]
  rfl

variable {X Y : Over S} {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}

theorem lbIso_of_lamEq (h : LamEq L f₁ f₂ M g₁ g₂) (x : T ⟶ X) (y : T ⟶ Y) :
    LBIso (cubeLB A ![x ≫ f₁, y ≫ f₂] L) (cubeLB B ![x ≫ g₁, y ≫ g₂] M) :=
  LBIso.chartPull (chartSquare L (lift x y) (by simp) (by simp)) (chartSquare M (lift x y) (by simp) (by simp)) h

end Cube

theorem lamEq_calculus : ∀ (S : Scheme.{0}) (X Y A B C : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C] (L : LB A.left) (M : LB B.left) (N : LB C.left), L.IsLB → M.IsLB → N.IsLB →
  ∀ (f₁ f₁' : X ⟶ A) (f₂ f₂' : Y ⟶ A) (g₁ g₁' : X ⟶ B) (g₂ g₂' : Y ⟶ B) (k₁ : X ⟶ C) (k₂ : Y ⟶ C),
  LamEq L f₁ f₂ L f₁ f₂ ∧ (LamEq L f₁ f₂ M g₁ g₂ → LamEq M g₁ g₂ L f₁ f₂ ∧ LamEq L f₂ f₁ M g₂ g₁ ∧ (LamEq M g₁ g₂ N k₁ k₂ → LamEq L f₁ f₂ N k₁ k₂) ∧
    (∀ (X' Y' : Over S) (a : X' ⟶ X) (b : Y' ⟶ Y), LamEq L (a ≫ f₁) (b ≫ f₂) M (a ≫ g₁) (b ≫ g₂)) ∧
    ∀ (T : Over S) (x : T ⟶ X) (y : T ⟶ Y), LBIso (cubeLB A ![x ≫ f₁, y ≫ f₂] L) (cubeLB B ![x ≫ g₁, y ≫ g₂] M)) ∧
  ((∃ t : LB.Gen (Theta A L), t.IsGen) → (∃ t : LB.Gen (Theta B M), t.IsGen) → LamEq L f₁ f₂ M g₁ g₂ → (LamEq L f₁' f₂ M g₁' g₂ → LamEq L (f₁ * f₁') f₂ M (g₁ * g₁') g₂) ∧ (LamEq L f₁ f₂' M g₁ g₂' → LamEq L f₁ (f₂ * f₂') M g₁ (g₂ * g₂'))) ∧
  ∀ ψ : A ⟶ B, IsMonHom ψ → LBIso L (M.pull ψ.left) → LamEq L f₁ f₂ M (f₁ ≫ ψ) (f₂ ≫ ψ) := by
  intro S X Y A B C _ _ _ _ _ _ L M N hL hM hN f₁ f₁' f₂ f₂' g₁ g₁' g₂ g₂' k₁ k₂
  refine ⟨(lbIso_iff hL _ _ _ _).2 rfl, fun h => ⟨LBIso.symm h, ?_, fun h' => ?_, fun X' Y' a b => ?_,
    fun T x y => lbIso_of_lamEq h x y⟩, fun hT hT' h => ⟨fun h' => ?_, fun h' => ?_⟩, fun ψ hψ h => ?_⟩
  · exact LBIso.trans (cubeLB_isLB hL _) (cubeLB_isLB hL _) (cubeLB_isLB hM _) (lbIso_cubeLB_swap hL _ _)
      (LBIso.trans (cubeLB_isLB hL _) (cubeLB_isLB hM _) (cubeLB_isLB hM _)
        (lbIso_of_lamEq h (snd Y X) (fst Y X)) (lbIso_cubeLB_swap hM _ _))
  · exact LBIso.trans (cubeLB_isLB hL _) (cubeLB_isLB hM _) (cubeLB_isLB hN _) h h'
  · have e := lbIso_of_lamEq h (fst X' Y' ≫ a) (snd X' Y' ≫ b)
    simp only [Category.assoc] at e
    exact e
  · unfold LamEq
    rw [MonObj.comp_mul, MonObj.comp_mul]
    exact lbIso_cubeLB_mul_left_of hL hM hT hT' h h'
  · unfold LamEq
    rw [MonObj.comp_mul, MonObj.comp_mul]
    exact lbIso_cubeLB_mul_right_of hL hM hT hT' h h'
  · have e := lbIso_cubeLB_hom ψ h (fst X Y ≫ f₁) (snd X Y ≫ f₂)
    simp only [Category.assoc] at e
    exact e

end GlobalTheory.LamCalc
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.HermTensorLB

open GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G A T : Over S} [GrpObj G] [GrpObj A]

theorem lam_sum {I : Type} (s : Finset I) (c : I → Pic A.left) (x y : T ⟶ A) :
    lam (∑ i ∈ s, c i) x y = ∑ i ∈ s, lam (c i) x y := by

  simp only [lam, map_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

variable [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

theorem lam_mul_right (x y z : T ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]

theorem lam_lam (u v : A ⟶ G) [IsMonHom u] [IsMonHom v] (x y : T ⟶ A) :
    lam (lam (cls L hL) u v) x y =
      lam (cls L hL) (x ≫ u) (y ≫ v) + lam (cls L hL) (y ≫ u) (x ≫ v) := by
  rw [lam.eq_1 (lam (cls L hL) u v)]
  simp only [pull_lam, MonObj.mul_comp, MonObj.one_comp, lam_one_left, lam_mul_left hL hΘ,
    lam_mul_right hL hΘ]
  abel

end Pairing

end GlobalTheory.HermTensorLB
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane
theorem _root_.GlobalTheory.T.curve_hom_ext_of_derivative_lieBasis : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (k : Type) [Field k] (s : k →+* ℂ) (P Q : Out.PolAV (Sp k)) (v : epsR k ⟶ P.A) (f f' : P.A ⟶ Q.A), (∀ (R' : Type) [CommRing R'] (f' : k →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) → IsMonHom f → IsMonHom f' → v ≫ f = v ≫ f' → f = f' := by
  first | exact @GlobalTheory.HomUnique.hom_ext_of_lieBasis | exact GlobalTheory.HomUnique.hom_ext_of_lieBasis | (intros; apply GlobalTheory.HomUnique.hom_ext_of_lieBasis <;> assumption)
end
