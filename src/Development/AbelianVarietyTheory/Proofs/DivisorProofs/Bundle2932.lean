module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle097
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLaws
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.Mum.TensTor

section Values

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

def GtRelV (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F)
    (v' : N'.Gt) (vs : Fin r → N.Gt) : Prop :=
  (∀ j, φ v'.b j = (vs j).b) ∧ ∀ χ' : N'.X,
    (v'.s χ' : F) * wv (N'.c χ') * wv v'.b =
      ((∏ i, ∏ j, ((vs j).s (e χ' i) * (vs i).s (e χ' j) /
          (N.θ (N.c (e χ' j)) (vs j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (vs j).b (vs i).b *
            N.θ (N.c (e χ' i)) (vs i).b (N.c (e χ' j) * (vs j).b))) ^ W i j : Fˣ) : F) *
        wv (N'.c χ' * v'.b) * wv 1

def QRelV (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F) {k : ℕ}
    (q' : N'.QT k) (qs : Fin r → N.QT k) : Prop :=
  (∀ i, e q'.1.1.toAdd i = (qs i).1.1.toAdd) ∧ GtRelV W φ e wv q'.1.2 (fun j => (qs j).1.2)

end Values

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

def cmp (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) (j : Fin r) : N.A :=
  ν.eA.symm (ν'.eA x ≫ T.pr j)

def chi (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ : N'.X) (i : Fin r) : N.X :=
  ν.eX.symm (T.xe (ν'.eX χ) i)

def wv (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) : F :=
  valF (ν'.eA x).left _
    (T.w.s (fun k => ν.J ((ν'.eA x).left ≫ tensφ T.pr k), ν'.J (ν'.eA x).left)).val

def GtRel (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (v' : N'.Gt) (vs : Fin r → N.Gt) : Prop :=
  GtRelV W (cmp T ν ν') (chi T ν ν') (wv T ν ν') v' vs

def PtRel (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') {k : ℕ} (p' : QkPt D' F k)
    (ps : Fin r → QkPt D F k) : Prop :=
  ∃ (q' : N'.QT k) (qs : Fin r → N.QT k), ν'.QPt p' q' ∧ (∀ i, ν.QPt (ps i) (qs i)) ∧
    QRelV W (cmp T ν ν') (chi T ν ν') (wv T ν ν') q' qs

end GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

section Facts

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

def TensFacts (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F) :
    Prop :=
  (∀ x y j, φ (x * y) j = φ x j * φ y j) ∧ Function.Bijective φ ∧
  (∀ χ χ' i, e (χ + χ') i = e χ i + e χ' i) ∧ Function.Bijective e ∧
  (∀ χ' j, φ (N'.c χ') j = N.c (e χ' j)) ∧ (∀ x, wv x ≠ 0) ∧
  (∀ x y u, (N'.θ x y u : F) * wv (x * y * u) * wv x * wv y * wv u =
    ((∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) /
        (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j : Fˣ) : F) *
      wv (x * y) * wv (x * u) * wv (y * u) * wv 1) ∧
  ∀ χ', (N'.ψ χ' : F) * wv 1 = wv (N'.c χ') * ((∏ i, ∏ j, N.τ (e χ' i) (e χ' j) ^ W i j : Fˣ) : F)

end Facts

end GlobalTheory.Mum.TensTor
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumFam

def GAdj {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    (L₁ : LB G₁.left) (L₂ : LB G₂.left) (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁) : Prop :=
  LBIso (cubeLB G₂ ![fst G₁ G₂ ≫ u, snd G₁ G₂] L₂) (cubeLB G₁ ![fst G₁ G₂, snd G₁ G₂ ≫ u'] L₁)

def adjVal {S : Scheme.{0}} {T G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} {x₁ : Fin 2 → (T ⟶ G₁)} {x₂ : Fin 2 → (T ⟶ G₂)}
    (w : LB.Iso (cubeLB G₂ x₂ L₂) (cubeLB G₁ x₁ L₁)) {Z : Scheme.{0}} (p : Z ⟶ T.left) (z : Z)
    (J₁ : (Z ⟶ G₁.left) → L₁.ι) (J₂ : (Z ⟶ G₂.left) → L₂.ι) : (Z.presheaf.stalk z)ˣ :=
  gm p z _ (w.s (fun I => J₁ (p ≫ (psum G₁ x₁ I.down).left), fun I => J₂ (p ≫ (psum G₂ x₂ I.down).left)))

variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R']

def Adj (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a' : Q₂.B ⟶ Q₁.B) (h : Q₁.X →+ Q₂.X) (h' : Q₂.X →+ Q₁.X) : Prop :=
  IsMonHom a ∧ IsMonHom a' ∧ (∀ y, Q₂.c (h y) = Q₁.c y ≫ a) ∧ (∀ z, Q₁.c (h' z) = Q₂.c z ≫ a') ∧
  ∃ w : LB.Iso (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L)
      (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L), w.IsGen ∧
    ∀ y y' z J₁ J₂, Good Q₁.M.L z J₁ → Good Q₂.M.L z J₂ →
      val (Q₂.tau (h y) y') (𝟙 _) z J₂ =
        adjVal w (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left z J₁ J₂ * val (Q₁.tau y (h' y')) (𝟙 _) z J₁

abbrev pol {I : Ideal R} (D : DegData R I) : Data R := Wit.ofDeg D.toPre D.tau_bimult

def RefAt (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (β : D.P.A.left ⟶ Q.B.left) : Prop :=
  letI := D.P.isAb.comm
  ∃ (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)),
    IsGrpPullback D.P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) ∧
    ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.tau a b) (𝟙 _) z J' =
        lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J

def IsTens (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B))
    (xe : D'.X ≃+ (Fin r → Q.X)) : Prop :=
  (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk D'.P.A pr)) ∧ (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) ∧
  ∃ w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)), w.IsGen ∧
    ∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' →
      val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j

def TorusHomOf {S : Scheme.{0}} {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂] (h : X₂ → X₁)
    (t : splitTorus S X₁ ⟶ splitTorus S X₂) : Prop :=
  ∀ χ : X₂, res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X₂ χ)) = charUnit S X₁ (h χ)

variable {I : Ideal R} {D₁ D₂ D₃ : DegData R I} {A₁ A₂ A₃ : PolAV (Sp (FractionRing R))} {G₁ G₂ G₃ : Over (Sp R)}
  [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] [GrpObj G₃] [IsCommMonObj G₃]

def LinHom (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : D₁.toPre.P.A ⟶ D₂.toPre.P.A)
    (h' : D₂.toPre.X →+ D₁.toPre.X) (g : G₁ ⟶ G₂) : Prop :=
  IsMonHom g ∧ (∀ e, (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map a) ∧
    ∀ e, ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
      TorusHomOf h' t ∧ (U₁.gt e).i ≫ (Over.pullback (thick R I e)).map g = t ≫ (U₂.gt e).i

theorem TorusHomOf.comp {S : Scheme.{0}} {X₁ X₂ X₃ : Type} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    {h : X₂ → X₁} {k : X₃ → X₂} {t : splitTorus S X₁ ⟶ splitTorus S X₂} {s : splitTorus S X₂ ⟶ splitTorus S X₃}
    (ht : TorusHomOf h t) (hs : TorusHomOf k s) : TorusHomOf (fun χ => h (k χ)) (t ≫ s) := fun χ => by
  rw [← ht (k χ), ← hs χ]
  refine unit_ext fun z _ => ?_
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_
  refine Eq.symm (((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_)
  refine ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull _ _ z ⊤ trivial _)).trans ?_
  rfl

theorem TorusHomOf.id {S : Scheme.{0}} (X : Type) [AddCommGroup X] : TorusHomOf (fun χ : X => χ) (𝟙 (splitTorus S X)) :=
  fun χ => unit_ext fun z _ =>
    ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans rfl

theorem LinHom.id (U : UnifPre I D₁ A₁ G₁) : LinHom U U (𝟙 _) (AddMonoidHom.id _) (𝟙 G₁) :=
  ⟨inferInstance, fun e => by simp, fun e => ⟨𝟙 _, TorusHomOf.id _, by simp⟩⟩

theorem LinHom.comp {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂} {U₃ : UnifPre I D₃ A₃ G₃} {a h' g b k' f}
    (hg : LinHom U₁ U₂ a h' g) (hf : LinHom U₂ U₃ b k' f) : LinHom U₁ U₃ (a ≫ b) (h'.comp k') (g ≫ f) := by
  obtain ⟨g₁, g₂, g₃⟩ := hg
  obtain ⟨f₁, f₂, f₃⟩ := hf
  refine ⟨inferInstance, fun e => ?_, fun e => ?_⟩
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, f₂, ← Category.assoc, g₂, Category.assoc]
  · obtain ⟨t, ht, hi⟩ := g₃ e
    obtain ⟨s, hs, hj⟩ := f₃ e
    refine ⟨t ≫ s, ht.comp hs, ?_⟩
    rw [Functor.map_comp, ← Category.assoc, hi, Category.assoc, hj, Category.assoc]

theorem linHom_iff_linEnd {U : UnifPre I D₁ A₁ G₁} {a h' g} : LinHom U U a h' g ↔ LinEnd U a h' g := by
  refine ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, fun e => inferInstance, fun e => ?_, h₂, h₃⟩, fun ⟨h₁, _, _, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩
  apply pullback.hom_ext
  · simp only [thickMap, Over.pullback_map_left, Category.assoc, pullback.map]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id, pullback.lift_fst]
  · simp only [thickMap, Over.pullback_map_left, Category.assoc, pullback.map]
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd_assoc]

end GlobalTheory.MumFam
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

open MonObj

namespace GlobalTheory.Poinc.DeepLab

theorem epi_spMap_field {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  letI := f.toAlgebra
  haveI : Flat (spMap f) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (show Module.Flat K L from inferInstance)
  haveI : Surjective (spMap f) := ⟨fun z => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

section Push
variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem pushHom_injective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Injective (pushHom h T) :=
  fun _ _ e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem pushHom_surjective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Surjective (pushHom h T) :=
  fun x₀ => ⟨Over.homMk (h.1.lift x₀.left T.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

end Push

theorem exists_lab {Γ₁ Γ₂ H : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂] [Group H] (L : ℕ)
    (f : Multiplicative Γ₂ →* H) (s : Multiplicative Γ₁ →* H)
    (uniq : ∀ z : H, z ^ L = 1 → ∃! b : Γ₂, f (Multiplicative.ofAdd b) = z)
    (hsL : ∀ a : Γ₁, s (Multiplicative.ofAdd a) ^ L = 1) :
    ∃ lab : Γ₁ →+ Γ₂, ∀ a, f (Multiplicative.ofAdd (lab a)) = s (Multiplicative.ofAdd a) := by
  choose l hl hu using fun a => uniq _ (hsL a)
  refine ⟨AddMonoidHom.mk' l fun a b => (hu (a + b) _ ?_).symm, hl⟩
  simp only [ofAdd_add, map_mul, hl]

theorem nsmul_self_eq_zero {κ : Type} (L : ℕ) (a : κ → ZMod L) : L • a = 0 := by
  funext i
  rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]

theorem map_pow_self {κ H : Type} [Group H] (L : ℕ) (p : Multiplicative (κ → ZMod L) →* H) (a : κ → ZMod L) :
    p (Multiplicative.ofAdd a) ^ L = 1 := by
  rw [← map_pow, ← ofAdd_nsmul, nsmul_self_eq_zero, ofAdd_zero, map_one]

end GlobalTheory.Poinc.DeepLab

namespace GlobalTheory.Poinc.DeepLab

theorem exists_lab_same : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₁.P.A ⟶ ρ₁.P.A)) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)) (φ : Ω₁ →+* Ω₂) (h : S₁.R →+* S₂.R) (ψ : ρ₂.P.A.left ⟶ ρ₁.P.A.left), (∀ a, ((h a : S₂.R) : Ω₂) = φ a) → IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap h) ψ → LBIso ρ₂.P.L (ρ₁.P.L.pull ψ) → (∀ E, (ε₂ E).left ≫ ψ = ψ ≫ (ε₁ E).left) → S₁.r * S₁.N ∣ S₂.r * S₂.N → ∃ lab : S₁.Gam →+ S₂.Gam, Same ρ₁ ε₁ ρ₂ ε₂ lab φ ∧ ∀ x : S₂.Gam, ∃ a, lab a = (S₂.r * S₂.N / (S₁.r * S₁.N)) • x := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ S₁ S₂ ρ₁ ρ₂ ε₁ ε₂ φ h ψ hh hpb hL hε hd
  have hcomp : S₂.R.val.toRingHom.comp h = φ.comp S₁.R.val.toRingHom := RingHom.ext fun a => hh a
  have hsp : spMap (φ.comp S₁.R.val.toRingHom) = spMap S₂.R.val.toRingHom ≫ spMap h := by
    rw [← hcomp, spMap_comp]
  let K := AlgebraicClosure Ω₂
  let x₀ : Sp K ⟶ Sp S₂.R := spMap (algebraMap Ω₂ K) ≫ spMap S₂.R.val.toRingHom
  let U : Over.mk ((baseOver (Sp S₂.R)).hom ≫ spMap h) ⟶ baseOver (Sp S₁.R) := Over.homMk (spMap h) (by simp)
  let V₂ : Over.mk x₀ ⟶ baseOver (Sp S₂.R) := Over.homMk x₀ (by simp)
  let p₁ : Multiplicative S₁.Gam →* (baseOver (Sp S₁.R) ⟶ ρ₁.P.A) :=
    MonoidHom.mk' (fun a => ρ₁.pt (Multiplicative.toAdd a)) fun a b => ρ₁.pt_add _ _
  let p₂ : Multiplicative S₂.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) :=
    MonoidHom.mk' (fun a => ρ₂.pt (Multiplicative.toAdd a)) fun a b => ρ₂.pt_add _ _
  have hbij : Function.Bijective (pushHom hpb (baseOver (Sp S₂.R))) :=
    ⟨pushHom_injective hpb _, pushHom_surjective hpb _⟩
  let e := MulEquiv.ofBijective (pushHom hpb (baseOver (Sp S₂.R))) hbij
  let σ : Multiplicative S₁.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) := e.symm.toMonoidHom.comp ((preHom U).comp p₁)
  have hσ : ∀ a, pushHom hpb _ (σ a) = U ≫ ρ₁.pt (Multiplicative.toAdd a) := fun a =>
    e.apply_symm_apply (U ≫ ρ₁.pt (Multiplicative.toAdd a))
  have hσl : ∀ a, (σ a).left ≫ ψ = spMap h ≫ (ρ₁.pt (Multiplicative.toAdd a)).left := fun a =>
    congrArg (fun q => q.left) (hσ a)
  have uniq : ∀ z : Over.mk x₀ ⟶ ρ₂.P.A, z ^ (S₂.r * S₂.N) = 1 →
      ∃! b : S₂.Gam, (preHom V₂).comp p₂ (Multiplicative.ofAdd b) = z := fun z hz =>
    ρ₂.pt_bij K x₀ z hz
  have hσL : ∀ a : S₁.Gam, σ (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := by
    intro a
    obtain ⟨c, hc⟩ := hd
    rw [hc, pow_mul, map_pow_self, one_pow]
  have hsL : ∀ a : S₁.Gam, (preHom V₂).comp σ (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := by
    intro a
    rw [MonoidHom.comp_apply, ← map_pow, hσL, map_one]
  obtain ⟨lab, hlab⟩ := exists_lab _ _ _ uniq hsL
  have hlabl : ∀ a : S₁.Gam, x₀ ≫ (ρ₂.pt (lab a)).left = x₀ ≫ (σ (Multiplicative.ofAdd a)).left := fun a =>
    congrArg (fun q => q.left) (hlab a)
  haveI := epi_spMap_field (algebraMap Ω₂ K)
  refine ⟨lab, ?_, ?_⟩
  · let P₀ := GlobalTheory.StrictPull.polPull ρ₂.P (spMap S₂.R.val.toRingHom)
    refine ⟨P₀, pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom) ≫ ψ,
      pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom),
      fun E => (Over.pullback (spMap S₂.R.val.toRingHom)).map (ε₂ E), ?_, isGrpPullback_pullback _ _, ?_,
      GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB, ?_, ?_⟩
    · rw [hsp]; exact IsGrpPullback.comp (isGrpPullback_pullback _ _) hpb
    · exact GlobalTheory.PolDeg.lbIso_pull_comp hL _ rfl
    · intro E
      have e₁ : ((Over.pullback (spMap S₂.R.val.toRingHom)).map (ε₂ E)).left ≫
          pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom) =
          pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom) ≫ (ε₂ E).left := pullback.lift_fst _ _ _
      refine ⟨?_, e₁⟩
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) e₁).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (hε E)).trans (Category.assoc _ _ _).symm)))
    · intro x
      refine ⟨pullback.lift (spMap S₂.R.val.toRingHom ≫ (ρ₂.pt (lab x)).left) (𝟙 _) ?_, ?_,
        pullback.lift_fst _ _ _⟩
      · rw [Category.assoc, Over.w]; simp
      · refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) (pullback.lift_fst _ _ _)).trans ?_)
        rw [hsp, ← cancel_epi (spMap (algebraMap Ω₂ K))]
        have e₂ := congrArg (· ≫ ψ) (hlabl x)
        simp only [x₀, Category.assoc] at e₂ ⊢
        rw [e₂, hσl]
        rfl
  · intro x
    set y := (S₂.r * S₂.N / (S₁.r * S₁.N)) • x with hy
    have hyL : p₂ (Multiplicative.ofAdd y) ^ (S₁.r * S₁.N) = 1 := by
      rw [← map_pow, ← ofAdd_nsmul, hy, smul_smul, Nat.mul_div_cancel' hd, nsmul_self_eq_zero, ofAdd_zero, map_one]
    let T₀ : Over (Sp S₂.R) := Over.mk x₀
    let V₁ : Over.mk (x₀ ≫ spMap h) ⟶ baseOver (Sp S₁.R) := Over.homMk (x₀ ≫ spMap h) (by simp)
    let z₁ : Over.mk (x₀ ≫ spMap h) ⟶ ρ₁.P.A := pushHom hpb T₀ (V₂ ≫ ρ₂.pt y)
    have hz₁ : z₁ ^ (S₁.r * S₁.N) = 1 := by
      have h0 : (V₂ ≫ ρ₂.pt y) ^ (S₁.r * S₁.N) = 1 := by
        have h3 := congrArg (preHom V₂) hyL
        rwa [map_pow, map_one] at h3
      show (pushHom hpb T₀) _ ^ _ = 1
      rw [← map_pow, h0, map_one]
    obtain ⟨a, ha, -⟩ := ρ₁.pt_bij K (x₀ ≫ spMap h) z₁ hz₁
    refine ⟨a, ?_⟩
    have hpush : pushHom hpb T₀ (V₂ ≫ σ (Multiplicative.ofAdd a)) = V₁ ≫ ρ₁.pt a := by
      apply Over.OverMorphism.ext
      show (V₂ ≫ σ _).left ≫ ψ = (V₁ ≫ ρ₁.pt a).left
      simp only [Over.comp_left, Category.assoc, V₂, V₁, Over.homMk_left]
      rw [hσl]
      rfl
    have h1 : V₂ ≫ σ (Multiplicative.ofAdd a) = V₂ ≫ ρ₂.pt y := pushHom_injective hpb T₀ (hpush.trans ha)
    have h2 : (V₂ ≫ ρ₂.pt y) ^ (S₂.r * S₂.N) = 1 := by
      have h3 := congrArg (preHom V₂) (map_pow_self _ p₂ y)
      rwa [map_pow, map_one] at h3
    exact (uniq _ h2).unique ((hlab a).trans h1) rfl

end GlobalTheory.Poinc.DeepLab
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TensRig

theorem oneGen_isGen' {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

theorem eta_eq_one {S : Scheme.{0}} (B : Over S) [GrpObj B] : (η[B] : 𝟙_ (Over S) ⟶ B) = 1 := by
  show _ = toUnit _ ≫ η[B]
  rw [toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _), Category.id_comp]

theorem eSec_tensφ {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {r : ℕ} (pr : Fin r → (A ⟶ B))
    (hpr : ∀ i, IsMonHom (pr i)) (k : (Fin r × Fin r) × Fin 4) : eSec A ≫ tensφ pr k = eSec B := by
  obtain ⟨⟨i, j⟩, m⟩ := k
  have hi : η[A] ≫ pr i = η[B] := IsMonHom.one_hom _
  have hj : η[A] ≫ pr j = η[B] := IsMonHom.one_hom _
  have key : ∀ x : A ⟶ B, η[A] ≫ x = η[B] → eSec A ≫ x.left = eSec B := fun x hx => by
    rw [eSec, eSec, ← Over.comp_left, hx]
  fin_cases m
  · refine key _ ?_
    rw [MonObj.comp_mul, hi, hj, eta_eq_one, _root_.mul_one]
  · exact key _ hi
  · exact key _ hj
  · refine key _ ?_
    rw [MonObj.comp_one, eta_eq_one]

end GlobalTheory.Mum.TensRig

open GlobalTheory.Mum.TensRig in
theorem GlobalTheory.Mum.TensRig.rig_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (A' : Over (Spec (CommRingCat.of R))) [GrpObj A'] (L' : LB A'.left), L'.IsLB → ∀ (pr : Fin r → (A' ⟶ D.P.A)), (∀ i, IsMonHom (pr i)) → ∀ (w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))), w.IsGen → ∃ rig : LB.Gen (L'.pull (eSec A')), rig.IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ A'.left) → L'.ι), Good D.P.L z J → Good L' z J' → val (LB.pullGen L' _ _ rig (toUnit (TK R)).left) (𝟙 _) z J' * gm (ptK η[A']) z _ (w.s (fun k => J (ptK η[A'] ≫ tensφ pr k), J' (ptK η[A']))) = 1 := by
  intro R _ _ D r W A' _ L' hL' pr hpr w hw
  have hform : FormEq (X := D.P.A.left) (Y := (𝟙_ (Over (Spec (CommRingCat.of R)))).left)
      (PEmpty.elim : PEmpty → _) PEmpty.elim
      (GlobalTheory.LamBiext.flatφ (tensφ pr) (fun _ : PUnit => eSec A'))
      (GlobalTheory.LamBiext.flatε (tensε W) (fun _ : PUnit => (1 : ℤ))) := by
    intro U _ h
    simp only [GlobalTheory.LamBiext.flatφ, GlobalTheory.LamBiext.flatε, eSec_tensφ pr hpr, _root_.one_mul, Finset.univ_eq_empty,
      Finset.prod_empty, Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε]
    simp
  obtain ⟨t, ht, htv⟩ := exists_gen D.P.isLB hform (LB.oneGen D.P.L) (oneGen_isGen' _)
  obtain ⟨a, ha, hmaps⟩ := Transport.exists_transport
    (DVR.linComb_isLB L' hL' (fun _ : PUnit => eSec A') (fun _ => 1))
    (DVR.linComb_isLB _ (DVR.linComb_isLB D.P.L D.P.isLB (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A') (fun _ => 1))
    (LB.linCombIso w (fun _ : PUnit => eSec A') (fun _ => 1)) (DVR.linCombIso_isGen w hw _ _)
    (GlobalTheory.LamBiext.nest D.P.L (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') (fun _ => 1) t)
    (GlobalTheory.LamBiext.nest_isGen ht)
  refine ⟨a, ha, fun z J J' hJ hJ' => ?_⟩
  have hPM := (GlobalTheory.GtCubeCompare.maps_iff_pm w (fun _ : PUnit => eSec A') (fun _ => 1) a _).1 hmaps
  have hp : (toUnit (TK R)).left z ∈ LB.wchart (LB.LinComb D.P.L (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A')
      (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k)) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => hJ (ptK η[A'] ≫ tensφ pr k)
  have hq : (toUnit (TK R)).left z ∈ LB.wchart L' (fun _ : PUnit => eSec A') (fun _ => J' (ptK η[A'])) :=
    Set.mem_iInter.2 fun _ => hJ' (ptK η[A'])
  have E := hPM _ (toUnit (TK R)).left z _ _ hp hq
  have L1 : gm (toUnit (TK R)).left z (LB.wchart (LB.LinComb D.P.L (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A')
      (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k)))
      ((GlobalTheory.LamBiext.nest D.P.L (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') (fun _ => 1) t).s
        (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k))) = 1 := by
    refine (gm_res _ z (GlobalTheory.LamBiext.nest_le D.P.L (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') _) hp _).trans ?_
    exact (val_of t (toUnit (TK R)).left z J (fun p => J (ptK η[A'] ≫ tensφ pr p.2))
      (fun x => congrArg J (Category.assoc _ _ _).symm)).symm.trans ((htv _ _ z J hJ).trans (val_one _))
  rw [L1, Fintype.prod_unique, zpow_one] at E
  rw [val_pull hJ' a (toUnit (TK R)).left (𝟙 _),
    val_of a _ z J' (fun _ => J' (ptK η[A'])) (fun _ => by rw [Category.id_comp]; rfl), Category.id_comp, mul_comm]
  exact E.symm
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abVar_surjective_iff_ptMap_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B), Surjective p.hom.left ↔ Function.Surjective (ptMap p) := by
  first | exact @GlobalTheory.AV.AbVar.surjective_iff_ptMap_surjective | exact GlobalTheory.AV.AbVar.surjective_iff_ptMap_surjective | (intros; apply GlobalTheory.AV.AbVar.surjective_iff_ptMap_surjective <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.chernMeasurePart_preimage_covering_field : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ (ε : ℤˣ) (U : Set (CxPts p σ)), IsOpen U → ∀ n : ℕ, (∀ y ∈ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (n : ℕ∞)) → (∀ y ∈ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) → (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → (φ.pull π hπ).chernPart D ε (PtsOver.map π hπ (spMap σ) ⁻¹' U) = (n : ENNReal) * φ.chernPart D ε U := by
  first | exact @GlobalTheory.CoverChernField.chernPart_preimage_of_cover | exact GlobalTheory.CoverChernField.chernPart_preimage_of_cover | (intros; apply GlobalTheory.CoverChernField.chernPart_preimage_of_cover <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_arithmeticCover_over_modification : ∀ (k : Type) [CommRing k] (X X' Y : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral Y] (p : X ⟶ Sp k) (D E : ℕ) (ρ : X' ⟶ X) (π : Y ⟶ X), IsArithVar p D → IsArithVar (ρ ≫ p) D → IsArithVar (π ≫ p) E → ρ (genericPoint X') = genericPoint X → ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (g : Y' ⟶ Y) (π' : Y' ⟶ X'), π' ≫ ρ = g ≫ π ∧ IsArithVar (g ≫ π ≫ p) E ∧ g (genericPoint Y') = genericPoint Y ∧ g.residueDegree (genericPoint Y') ≠ 0 := by
  first | exact @GlobalTheory.CoverLift.exists_cover_over_modification | exact GlobalTheory.CoverLift.exists_cover_over_modification | (intros; apply GlobalTheory.CoverLift.exists_cover_over_modification <;> assumption)
end
