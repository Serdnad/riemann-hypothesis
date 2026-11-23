module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UPel.HT.Gen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped TensorProduct

structure GDatum where
  F : Type
  [fld : Field F]
  [nf : NumberField F]
  [cm : IsCMField F]
  bar : 𝓞 F ≃+* 𝓞 F
  bar_eq : ∀ a : 𝓞 F, ((bar a : 𝓞 F) : F) = IsCMField.complexConj F (a : F)
  ω : 𝓞 F
  tr : ℤ
  nm : ℤ
  tr_eq : ω + bar ω = (tr : 𝓞 F)
  nm_eq : ω * bar ω = (nm : 𝓞 F)
  disc_neg : tr ^ 2 - 4 * nm < 0
  O : Type
  [rng : Ring O]
  [alg : Algebra (𝓞 F) O]
  freeO : Module.Free ℤ O
  finO : Module.Finite ℤ O
  m : ℕ
  m_pos : 0 < m
  rankO : Module.finrank ℤ O = m ^ 2 * Module.finrank ℚ F
  central : ∀ x : O, (∀ y, x * y = y * x) → ∃ c : 𝓞 F, ∃ e : ℤ, e ≠ 0 ∧ e • x = algebraMap (𝓞 F) O c
  star : O ≃+* Oᵐᵒᵖ
  star_star : ∀ x, (star (star x).unop).unop = x
  star_F : ∀ c : 𝓞 F, star (algebraMap (𝓞 F) O c) = MulOpposite.op (algebraMap (𝓞 F) O (bar c))

  splitSome : ∃ (q : ℕ) (_ : Fact q.Prime),
    Nonempty ((O ⊗[ℤ] ℤ_[q]) ≃ₐ[𝓞 F] Matrix (Fin m) (Fin m) (𝓞 F ⊗[ℤ] ℤ_[q]))
  La : Type
  [acg : AddCommGroup La]
  [modO : Module O La]
  freeLa : Module.Free ℤ La
  finLa : Module.Finite ℤ La
  n : ℕ
  n_pos : 1 ≤ n
  rankLa : Module.finrank ℤ La = m * n * Module.finrank ℚ F
  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  nondeg : Function.Injective EF
  adj : ∀ (b : O) x y, EF (b • x) y = EF x ((star b).unop • y)
  a : ℕ
  ρc : ℂ
  ρc_root : ρc ^ 2 - tr * ρc + nm = 0
  tau : Fin a ↪ (F →+* ℂ)
  tau_ω : ∀ i, tau i (ω : F) = ρc
  dom : ∃ J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La, (∀ x, J (J x) = -x) ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    (∀ (b : O) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La), (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (b • x)) → J ∘ₗ A = A ∘ₗ J) ∧
    ∀ (c : 𝓞 F) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La), (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (algebraMap (𝓞 F) O c • x)) →
      let S : ℂ := (m : ℂ) * (∑ i, tau i (c : F) +
        ∑ τ ∈ Finset.univ.filter (fun τ : F →+* ℂ => τ (ω : F) = (starRingEnd ℂ) ρc), (n : ℂ) * τ (c : F) -
        ∑ i, (starRingEnd ℂ) (tau i (c : F)))
      LinearMap.trace ℝ _ A = 2 * S.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * S.im

attribute [instance] GDatum.fld GDatum.nf GDatum.cm GDatum.rng GDatum.alg GDatum.acg GDatum.modO

def _root_.GlobalTheory.UPel.HT.Datum.toG {p : ℕ} [Fact p.Prime] (D : Datum p) : GDatum where
  F := D.F
  bar := D.bar
  bar_eq := D.bar_eq
  ω := D.ω
  tr := D.tr
  nm := D.nm
  tr_eq := D.tr_eq
  nm_eq := D.nm_eq
  disc_neg := D.disc_neg
  O := D.O
  freeO := D.freeO
  finO := D.finO
  m := D.m
  m_pos := D.m_pos
  rankO := D.rankO
  central := D.central
  star := D.star
  star_star := D.star_star
  star_F := D.star_F
  splitSome := ⟨p, inferInstance, D.splitP⟩
  La := D.La
  freeLa := D.freeLa
  finLa := D.finLa
  n := D.n
  n_pos := D.n_pos
  rankLa := D.rankLa
  EF := D.EF
  alt := D.alt
  nondeg := D.nondeg
  adj := D.adj
  a := D.a
  ρc := D.ρc
  ρc_root := D.ρc_root
  tau := D.tau
  tau_ω := D.tau_ω
  dom := D.dom

structure GBase (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] where
  ρ : R
  ρ_root : ρ ^ 2 - G.tr * ρ + G.nm = 0
  t : Fin G.a → (𝓞 G.F →+* R)
  t_ω : ∀ i, t i G.ω = ρ
  comax : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤

variable {S : Scheme.{0}}

structure GTateIso (G : GDatum) (k : Type) [Field k] (Q : Type) [Group Q] (act : G.O → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) where
  ζ : ℕ → kˣ
  ζ_prim : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n
  ζ_pow : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n
  ev : ℕ → G.La → Q
  add : ∀ n x y, ev n (x + y) = ev n x * ev n y
  lin : ∀ n (b : G.O) x, ev n (b • x) = act b (ev n x)
  ker : ∀ n, 0 < n → ∀ x, ev n x = 1 ↔ ∃ y, x = n • y
  onto : ∀ n, 0 < n → ∀ q, q ^ n = 1 ↔ ∃ x, ev n x = q
  tower : ∀ n m, 0 < n → 0 < m → ∀ x, ev (n * m) x ^ m = ev n x
  isom : ∀ n, 0 < n → ∀ x y, e n (ev n x) (ev n y) (ζ n ^ (2 * G.EF x y))

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

def actF {A : Over S} [GrpObj A] (act : OActN G.O A) : OAct (𝓞 G.F) A where
  act c := act.act (algebraMap (𝓞 G.F) G.O c)
  hom c := act.hom _
  one := by rw [map_one]; exact act.one
  mul b c := by rw [← act.mul, ← map_mul, mul_comm]
  add b c := by rw [map_add (f := _)]; exact act.add _ _

structure GObj (b : GBase G R) (N : ℕ) (s : S ⟶ Sp R) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  act : OActN G.O A
  P : LB (G2 A).left
  isLB : P.IsLB
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)
  ample : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)
  rosati : ∀ c : G.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
    (P.pull (lift (fst A A) (snd A A ≫ act.act (G.star c).unop)).left)
  lie : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β →
    ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 G.F) G.O G.ω) (β b.ρ) v →
      ∃ w : Fin G.a → (epsPtR x ⟶ A),
        (∀ i, ∀ c : 𝓞 G.F, IsTanScal act x (algebraMap (𝓞 G.F) G.O c) (β (b.t i c)) (w i)) ∧
        v = (List.ofFn w).prod
  lieRank : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β →
    ∀ i, LieMult (actF act) x (β.comp (b.t i)) G.m
  eta : G.La → (𝟙_ (Over S) ⟶ A)
  eta_add : ∀ x y, eta (x + y) = eta x * eta y
  eta_lin : ∀ (c : G.O) x, eta (c • x) = eta x ≫ act.act c
  eta_ker : ∀ x, eta (N • x) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β →
    ∃ I : GTateIso G k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c)
        (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ eta y = I.ev N y

attribute [instance] GObj.grp GObj.comm

structure GObjMap {b : GBase G R} {N : ℕ} {S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R}
    (o' : GObj b N s') (o : GObj b N s) (f : S' ⟶ S) where
  φ : o'.A.left ⟶ o.A.left
  φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left
  cart : IsGrpPullback o'.A o.A f φ
  sq : IsSquare φ φ₂
  act : ∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left
  pol : LBIso o'.P (o.P.pull φ₂)
  eta : ∀ y, (o'.eta y).left ≫ φ = f ≫ (o.eta y).left

structure GenModel (b : GBase G R) (N : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp R
  univ : GObj b N s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : GObj b N s'), ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (GObjMap o univ f)

end GlobalTheory.UPel.HT.Gen
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

namespace GlobalTheory.LBObs

section Frames

variable {X : Scheme.{0}} {C : Type} [Category.{0} C]

def IsBas (V : C → X.Opens) : Prop :=
  (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C, x ∈ V t ∧ V t ≤ U) ∧
    ∀ (t₁ t₂ : C) (x : X) (U : X.Opens), x ∈ U → x ∈ V t₁ → x ∈ V t₂ →
      ∃ t₃ : C, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ V t₃ ∧ V t₃ ≤ U

def IsGenOn (L : LB X) (W : X.Opens) (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ) : Prop :=
  ∀ m m' : L.ι, res (inf_le_left : W ⊓ L.U m ⊓ L.U m' ≤ W ⊓ L.U m) (τ m) =
    res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W ⊓ L.U m ⊓ L.U m' ≤ L.U m ⊓ L.U m') (L.g m m') *
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W ⊓ L.U m ⊓ L.U m' ≤ W ⊓ L.U m') (τ m')

def IsFrame (L : LB X) (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T)
    (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) : Prop :=
  ∃ τ : ∀ (T : C) (m : L.ι), Γ(X, V T ⊓ L.U m)ˣ, (∀ T, IsGenOn L (V T) (τ T)) ∧
    ∀ (T T' : C) (a : T ⟶ T') (m : L.ι), res (inf_le_inf_right (L.U m) (hV a)) (τ T m) =
      res (inf_le_left : V T' ⊓ L.U m ≤ V T') (u T T' a) * τ T' m

def IsCoc (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T)
    (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) : Prop :=
  ∀ ⦃T T' T'' : C⦄ (a : T ⟶ T') (b : T' ⟶ T''), u T T'' (a ≫ b) = res (hV b) (u T T' a) * u T' T'' b

abbrev opOf (G : C ⥤ AffOp X) (T : C) : X.Opens := (G.obj T).unop.1

theorem opOf_le (G : C ⥤ AffOp X) ⦃T T' : C⦄ (a : T ⟶ T') : opOf G T' ≤ opOf G T := leOfHom (G.map a).unop

end Frames

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R₀}

def UCoc (F : C ⥤ CommAlgCat.{0} R₀) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) : Prop :=
  ∀ ⦃T T' T'' : C⦄ (a : T ⟶ T') (b : T' ⟶ T''),
    (u T T'' (a ≫ b) : F.obj T'') = mp F b (u T T' a : F.obj T') * (u T' T'' b : F.obj T'')

def IsObU (L : Pre I π F) (α : Aug I π R₁) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ)
    (c : CatCoh.H2 (ext R₁ F)) : Prop :=
  ∃ (v : ∀ (T T' : C) (_ : T ⟶ T'), (L.B T')ˣ) (σ : ∀ T, R₁ ⊗[R₀] F.obj T →+ L.B T) (z : Z2 (ext R₁ F)),
    (∀ T T' a, L.p T' (v T T' a : L.B T') = (u T T' a : F.obj T')) ∧ (∀ T, α.IsSig (L.p T) (σ T)) ∧ c = H2.mk _ z ∧
      ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), α.KerQ (B₀ := F.obj T'') (z.1 T T' T'' a b) ∧
        L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') = (1 + σ T'' (z.1 T T' T'' a b)) * (v T T'' (a ≫ b) : L.B T'')

variable {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀}

def ObAt (S : Sys I π s₀) (α : Aug I π R₁) (L : LB X₀) (G : C ⥤ AffOp X₀) (d : CatCoh.H2 (ext R₁ (G ⋙ OAff s₀))) : Prop :=
  ∃ u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X₀, opOf G T')ˣ,
    IsFrame L (opOf G) (opOf_le G) u ∧ IsObU ((ofSys S).restrict G) α u d

def IsObL (S : Sys I π s₀) (α : Aug I π R₁) (L : LB X₀) (c : CatCoh.H2 (ext R₁ (OAff s₀))) : Prop :=
  ∃ (C' : Type) (_ : Category.{0} C') (_ : Quiver.IsThin C') (G : C' ⥤ AffOp X₀), IsBas (opOf G) ∧
    ObAt S α L G ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c)

end GlobalTheory.LBObs
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZM
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLev

def SRelBy {h n' n : ℕ} {B' B : Type} [CommRing B'] [CommRing B] {ζ' : B'} {ζ : B} {S' S : Scheme.{0}} {s' : S' ⟶ Sp B'}
    {s : S ⟶ Sp B} (c' : SiegPre h n' ζ' s') (c : SiegPre h n ζ s) (d' d : ℕ) (f : S' ⟶ S) (φ : c'.A.left ⟶ c.A.left) :
    Prop :=
  IsGrpPullback c'.A c.A f φ ∧ (∃ φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left, IsSquare φ φ₂ ∧ LBIso c'.P (c.P.pull φ₂)) ∧
    ∀ a, (c'.lev a ^ d').left ≫ φ = f ≫ (c.lev a ^ d).left

def SRel {h n' n : ℕ} {B' B : Type} [CommRing B'] [CommRing B] {ζ' : B'} {ζ : B} {S' S : Scheme.{0}} {s' : S' ⟶ Sp B'}
    {s : S ⟶ Sp B} (c' : SiegPre h n' ζ' s') (c : SiegPre h n ζ s) (d' d : ℕ) (f : S' ⟶ S) : Prop :=
  ∃ φ, SRelBy c' c d' d f φ

theorem sRel_one_one_iff {h n : ℕ} {B' B : Type} [CommRing B'] [CommRing B] {ζ' : B'} {ζ : B} {S' S : Scheme.{0}}
    {s' : S' ⟶ Sp B'} {s : S ⟶ Sp B} (c' : SiegPre h n ζ' s') (c : SiegPre h n ζ s) (f : S' ⟶ S) :
    SRel c' c 1 1 f ↔ SiegPB c' c f := by
  unfold SRel SRelBy SiegPB
  simp only [pow_one]
  constructor
  · rintro ⟨φ, hpb, ⟨φ₂, hsq, hiso⟩, hlev⟩
    exact ⟨φ, φ₂, hpb, hsq, hiso, hlev⟩
  · rintro ⟨φ, φ₂, hpb, hsq, hiso, hlev⟩
    exact ⟨φ, hpb, ⟨φ₂, hsq, hiso⟩, hlev⟩

structure SQuot {h N : ℕ} {o' : Type} [CommRing o'] {ζ' : o'} (F : SFam h N ζ') (n : ℕ) {o : Type} [CommRing o] (ζ : o)
    (j : o →+* o') where

  X : Scheme.{0}

  s : X ⟶ Sp o

  smooth : SmoothOfRelativeDimension (h * (h + 1) / 2) s

  qproj : IsQProjOver s

  univ : SiegPre h n ζ s

  princ : univ.Principal

  π : F.X ⟶ X

  base : π ≫ s = F.s ≫ spMap j

  fin : IsFinite π

  etale : Etale π

  onto : Surjective π

  low : SRel F.univ univ (N / n) 1 π

  fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y y' : Sp R ⟶ F.X) (s' : Sp R ⟶ Sp o) (c : SiegPre h n ζ s'),
    y ≫ F.s ≫ spMap j = y' ≫ F.s ≫ spMap j → SRel c F.univ 1 (N / n) y → SRel c F.univ 1 (N / n) y' → y ≫ π = y' ≫ π

end GlobalTheory.SiegLev
end
end
