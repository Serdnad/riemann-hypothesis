module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZJ

structure Charts (X : Scheme.{0}) where
  I : Type
  [fin : Finite I]
  Cl : Type
  [finC : Finite Cl]
  wt : I → Cl
  c₀ : Cl
  W : {i // wt i = c₀} → X.Opens
  aff : ∀ i, IsAffineOpen (W i)
  cover : ⨆ i, W i = ⊤
  r : ∀ i, I → Γ(X, W i)
  r_self : ∀ i, r i i.1 = 1
  inter : ∀ i i', W i ⊓ W i' = X.basicOpen (r i i'.1)
  trans : ∀ i i' j, resG X (inf_le_left : W i ⊓ W i' ≤ W i) (r i j) =
    resG X (inf_le_left : W i ⊓ W i' ≤ W i) (r i i'.1) * resG X (inf_le_right : W i ⊓ W i' ≤ W i') (r i' j)

attribute [instance] Charts.fin Charts.finC

def Charts.pull {X Y : Scheme.{0}} (C : Charts X) (φ : Y ⟶ X) [IsAffineHom φ] : Charts Y where
  I := C.I
  Cl := C.Cl
  wt := C.wt
  c₀ := C.c₀
  W := fun i => φ ⁻¹ᵁ C.W i
  aff := fun i => (C.aff i).preimage φ
  cover := by rw [← Scheme.Hom.preimage_iSup, C.cover, Scheme.Hom.preimage_top]
  r := fun i j => (φ.app (C.W i)).hom (C.r i j)
  r_self := fun i => by rw [C.r_self, map_one]
  inter := fun i i' => by rw [← Scheme.preimage_basicOpen, ← C.inter, Scheme.Hom.preimage_inf]
  trans := fun i i' j => by
    have key : ∀ (V : X.Opens) (h : C.W i ⊓ C.W i' ≤ V) (h' : φ ⁻¹ᵁ C.W i ⊓ φ ⁻¹ᵁ C.W i' ≤ φ ⁻¹ᵁ V) (u : Γ(X, V)),
        resG Y h' ((φ.app V).hom u) =
          (φ.appLE (C.W i ⊓ C.W i') (φ ⁻¹ᵁ C.W i ⊓ φ ⁻¹ᵁ C.W i') φ.preimage_inf.ge).hom (resG X h u) := by
      intro V h h' u
      change (φ.app V ≫ Y.presheaf.map (homOfLE h').op).hom u =
        (X.presheaf.map (homOfLE h).op ≫ φ.appLE _ _ _).hom u
      rw [Scheme.Hom.map_appLE]
      rfl
    rw [key _ inf_le_left, key _ inf_le_left, key _ inf_le_right, C.trans i i' j, map_mul]

variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]

def Stable (i : splitTorus S X ⟶ H) (V : H.left.Opens) : Prop :=
  ∀ (Y : Over S) (t : Y ⟶ splitTorus S X) (g : Y ⟶ H), ⊤ ≤ g.left ⁻¹ᵁ V → ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V

def HasWt (i : splitTorus S X ⟶ H) (V : H.left.Opens) (u : Γ(H.left, V)) (χ : X) : Prop :=
  ∀ (Y : Over S) (t : Y ⟶ splitTorus S X) (g : Y ⟶ H) (h : ⊤ ≤ g.left ⁻¹ᵁ V) (h' : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V),
    (((t ≫ i) * g).left.appLE V ⊤ h').hom u = t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE V ⊤ h).hom u

structure Charts.Torus (C : Charts H.left) {d : ℕ} (c : Fin d → C.Cl) (i : splitTorus S (Fin d → ℤ) ⟶ H) : Prop where
  hom : IsMonHom i
  stable : ∀ a, Stable i (C.W a)
  inv : ∀ a j, C.wt j = C.c₀ → HasWt i (C.W a) (C.r a j) 0
  wt : ∀ a j k, C.wt j = c k → HasWt i (C.W a) (C.r a j) (Pi.single k 1)
  bpf : ∀ k (x : H.left), ∃ a j, C.wt j = c k ∧ x ∈ H.left.basicOpen (C.r a j)
  gen : ∀ a (u : Γ(H.left, C.W a)), HasWt i (C.W a) u 0 →
    u ∈ Subring.closure (Set.range (H.hom.appLE ⊤ (C.W a) le_top).hom ∪ {v | ∃ j, C.wt j = C.c₀ ∧ v = C.r a j})

def Charts.Split (C : Charts H.left) {d : ℕ} (c : Fin d → C.Cl) : Prop :=
  GeometricallyConnected H.hom ∧ ∃ i : splitTorus S (Fin d → ℤ) ⟶ H, C.Torus c i

def Charts.SplitOn {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (C : Charts G.left) {d : ℕ}
    (c : Fin d → C.Cl) (Sg : Set (Sp R)) : Prop :=
  ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R) (_ : IsAffineHom (pullback.fst G.hom t)), Set.range t = {x} ∧
    Charts.Split (H := (Over.pullback t).obj G) (C.pull (pullback.fst G.hom t)) c

def Core.HasCharts (C : Core) : Prop :=
  ∀ z : C.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (t : Sp R ⟶ C.Z) (_ : IsImmersion t),
    t (⊥ : PrimeSpectrum R) = z ∧ ∃ Ch : Charts (pullback C.GG.hom t),
    ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y) (x : Sp (kb p) ⟶ Sp R), x ≫ t = rPt p ≫ y →
      ∀ (h : pullback τ.H.hom (rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom t) [IsAffineHom h],
        h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f → h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ x →
        ∃ d ≤ C.g, ∃ c : Fin d → Ch.Cl,
          Charts.Split (H := (Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) (Ch.pull h) c

def SplitAll {Z : Scheme.{0}} (G : Over Z) [GrpObj G] : Prop :=
  ∀ z : Z, ∃ E : SplitExt (Sp (Z.residueField z)), E.IsGt ((Over.pullback (Z.fromSpecResidueField z)).obj G)

theorem isUnit_resG_basicOpen (X : Scheme.{0}) (s : Γ(X, ⊤)) :
    IsUnit (resG X (le_top : X.basicOpen s ≤ ⊤) s) := by
  exact X.toRingedSpace.isUnit_res_basicOpen s

def Charts.ofSections (X : Scheme.{0}) [IsAffine X] {I Cl : Type} [Finite I] [Finite Cl] (wt : I → Cl) (c₀ : Cl)
    (s : I → Γ(X, ⊤)) (hs : ⨆ i : {i // wt i = c₀}, X.basicOpen (s i.1) = ⊤) : Charts X where
  I := I
  Cl := Cl
  wt := wt
  c₀ := c₀
  W := fun i => X.basicOpen (s i.1)
  aff := fun i => (isAffineOpen_top X).basicOpen (s i.1)
  cover := hs
  r := fun i j => resG X le_top (s j) * ↑(isUnit_resG_basicOpen X (s i.1)).unit⁻¹
  r_self := fun i => (isUnit_resG_basicOpen X (s i.1)).mul_val_inv
  inter := fun i i' => by
    rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (Units.isUnit _)]
    erw [X.basicOpen_res (s i'.1) (homOfLE le_top).op]
    exact (inf_eq_left.2 inf_le_left).symm
  trans := fun i i' j => by
    have h := congrArg (resG X (inf_le_right : X.basicOpen (s i.1) ⊓ X.basicOpen (s i'.1) ≤ _))
      (isUnit_resG_basicOpen X (s i'.1)).mul_val_inv
    have e : ∀ (V : X.Opens) (h : X.basicOpen (s i.1) ⊓ X.basicOpen (s i'.1) ≤ V) (u : Γ(X, ⊤)),
        resG X h (resG X le_top u) = resG X le_top u := by
      intro V h u
      change (X.presheaf.map _ ≫ X.presheaf.map _).hom u = _
      rw [← X.presheaf.map_comp]
      rfl
    rw [map_mul, map_one, e] at h
    simp only [map_mul, e]
    linear_combination (-(resG X le_top (s j)) * resG X inf_le_left
      ↑(isUnit_resG_basicOpen X (s i.1)).unit⁻¹) * h

def Charts.single (X : Scheme.{0}) [IsAffine X] {J : Type} [Finite J] (f : J → Γ(X, ⊤)) : Charts X where
  I := Option J
  Cl := Option J
  wt := id
  c₀ := none
  W := fun _ => ⊤
  aff := fun _ => isAffineOpen_top X
  cover := by
    have : Nonempty {i : Option J // id i = none} := ⟨⟨none, rfl⟩⟩
    exact iSup_const
  r := fun _ j => j.elim 1 f
  r_self := by
    rintro ⟨i, hi⟩
    obtain rfl : i = none := hi
    rfl
  inter := by
    rintro i ⟨i', hi⟩
    obtain rfl : i' = none := hi
    exact (inf_idem _).trans (X.basicOpen_of_isUnit isUnit_one).symm
  trans := by
    rintro i ⟨i', hi⟩ j
    obtain rfl : i' = none := hi
    change _ = resG X _ 1 * _
    rw [map_one, _root_.one_mul]

theorem charUnit_zero_val (S : Scheme.{0}) (X : Type) [AddCommGroup X] : (charUnit S X 0).val = 1 := by
  rw [charUnit_val_eq_appTop, ← AddMonoidAlgebra.one_def, map_one]
  exact map_one _

theorem hasWt_one (i : splitTorus S X ⟶ H) (V : H.left.Opens) : HasWt i V 1 0 := by
  intro Y t g h h'
  simp only [charUnit_zero_val, map_one, _root_.one_mul]

instance isAffine_splitTorus_left (S : Scheme.{0}) [IsAffine S] (d : ℕ) :
    IsAffine (splitTorus S (Fin d → ℤ)).left :=
  have := ((splitTorus_properties S).1 (Fin d → ℤ)).1
  isAffine_of_isAffineHom (splitTorus S (Fin d → ℤ)).hom

def Charts.ofTorus (S : Scheme.{0}) [IsAffine S] (d : ℕ) : Charts (splitTorus S (Fin d → ℤ)).left :=
  Charts.single _ fun k : Fin d => (charUnit S (Fin d → ℤ) (Pi.single k 1)).val

end GlobalTheory.ZJ
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.ZH
open Classical

def eStd (g n : ℕ) (a b : Fin g ⊕ Fin g → ZMod n) : ZMod n := ∑ i, (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i))

structure ThetaSys (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] where
  g : ℕ
  N : ℕ
  r : ℕ
  N_ge : 2 ≤ N
  r_pos : 1 ≤ r
  ζ : o
  prim : IsPrimitiveRoot ζ ((r * N) ^ 2)
  unit : IsUnit ((r * N : ℕ) : o)
  J : Type
  [fin : Fintype J]
  [ne : Nonempty J]
  ρ : (Fin g ⊕ Fin g → ZMod (r * N)) → Matrix J J o
  ρ_one : ∀ a, r • a = 0 → ρ a = 1
  ρ_mul : ∀ a b, ∃ k : ℕ, ρ a * ρ b = ζ ^ k • ρ (a + b)
  ρ_add : ∀ a b, r • eStd g _ a b = 0 → ρ a * ρ b = ρ (a + b)
  th : (Fin g ⊕ Fin g → ZMod (r * N)) → Ω
  ev : (Fin g ⊕ Fin g → ZMod (r * N)) → J → Ω
  R : Subalgebra o Ω
  fg : R.FG
  frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b
  th_mem : ∀ x, th x ∈ R
  ev_mem : ∀ x i, ev x i ∈ R
  supp : AddSubgroup.closure {x | th x ≠ 0} = ⊤
  th_ne : ∃ x, th x ≠ 0
attribute [instance] ThetaSys.fin ThetaSys.ne
namespace ThetaSys
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

abbrev Gam : Type := Fin S.g ⊕ Fin S.g → ZMod (S.r * S.N)

def perp (H : AddSubgroup S.Gam) : AddSubgroup S.Gam where
  carrier := {a | ∀ h ∈ H, eStd S.g _ a h = 0}
  add_mem' := by
    intro a b ha hb h hh
    have h1 := ha h hh
    have h2 := hb h hh
    simp only [eStd, Pi.add_apply] at h1 h2 ⊢
    rw [← add_zero (0 : ZMod (S.r * S.N))]
    nth_rewrite 1 [← h1]
    rw [← h2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  zero_mem' := by
    intro h _
    simp [eStd]
  neg_mem' := by
    intro a ha h hh
    have h1 := ha h hh
    simp only [eStd, Pi.neg_apply] at h1 ⊢
    rw [← neg_zero, ← h1, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

def IsoFree (T : AddSubgroup S.Gam) : Prop := T ≤ S.perp T ∧ ∃ d : ℕ, Nonempty (T ≃+ (Fin d → ZMod (S.r * S.N)))

def ζN : o := S.ζ ^ (S.r ^ 2 * S.N)

def proj (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) : Matrix S.J S.J o :=
  Ring.inverse (Nat.card T : o) • ∑ᶠ t : T, S.ζN ^ (-(c t)).val • S.ρ t

def FF (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) : Ω :=
  ∑ᶠ t : T, algebraMap o Ω (S.ζ ^ (k.2 t).val) * ∑ j, algebraMap o Ω (S.proj T c j k.1) * S.ev t j

structure Test (p : ℕ) [Fact p.Prime] (y : S.R →+* PadicAlgCl p) where
  X : Type
  [add : AddCommGroup X]
  [free : Module.Free ℤ X]
  [finite : Module.Finite ℤ X]
  q : QuadraticMap ℤ X ℝ
  pos : Filter.Tendsto q Filter.cofinite Filter.atTop
  yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range
  yy_onto : Function.Surjective yy
  isoFree : S.IsoFree (S.perp yy.ker)
  wt : X →+ (S.perp yy.ker →+ ZMod S.N)
  wt_eq : ∀ (x : S.Gam) (α : X), yy x = QuotientAddGroup.mk α → ∀ t : S.perp yy.ker,
    wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x)
  δ : ℝ
  δ_max : IsGreatest (Set.range fun x => ‖y ⟨S.th x, S.th_mem x⟩‖) δ
  δ_pos : 0 < δ
  supp : AddSubgroup.closure {x | ‖y ⟨S.th x, S.th_mem x⟩‖ = δ} = yy.ker
  tx : ∀ x, y ⟨S.th x, S.th_mem x⟩ ≠ 0 → ∃ w : X, yy x = QuotientAddGroup.mk w ∧
    ‖y ⟨S.th x, S.th_mem x⟩‖ ≤ δ * Real.exp (-(q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))
  le : ∀ (α : X), (∀ v0, q α ≤ q (α + S.N • v0)) → ∀ h ∈ yy.ker, ∀ i,
    ‖∑ j, y (algebraMap o S.R (S.proj _ (wt α) j i)) * y ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ δ * Real.exp (-(q α / S.N))
  eq : ∀ (α : X), (∀ v0, q α ≤ q (α + S.N • v0)) → ∃ (k : _) (hk : S.FF _ (wt α) k ∈ S.R),
    ‖y ⟨S.FF _ (wt α) k, hk⟩‖ = δ * Real.exp (-(q α / S.N))
  unit0 : ∀ h ∈ yy.ker, ∃ i, ‖∑ j, y (algebraMap o S.R (S.proj _ (wt 0) j i)) * y ⟨S.ev h j, S.ev_mem h j⟩‖ = δ
attribute [instance] Test.add Test.free Test.finite

def HasTests : Prop := ∀ (p : ℕ) [Fact p.Prime] (y : S.R →+* PadicAlgCl p),
  (∀ a : o, ‖y (algebraMap o S.R a)‖ ≤ 1) → Nonempty (S.Test p y)
variable (M : RatModel o Ω)

def supI (z : M.Z) : Set S.Gam := {x | M.Div S.th x z}

def HH (z : M.Z) : AddSubgroup S.Gam := AddSubgroup.closure (S.supI M z)

def TT (z : M.Z) : AddSubgroup S.Gam := S.perp (S.HH M z)

structure Over₀ (U₀ : M.Z.Opens) : Prop where
  normal : IsNormalScheme M.Z
  proj : IsProjOver M.s
  div : M.HasDiv S.th
  ne : (U₀ : Set M.Z).Nonempty
  le : S.R ≤ M.ringOn U₀
  th_unit : ∀ x, S.th x ≠ 0 → (S.th x)⁻¹ ∈ M.ringOn U₀
  FF_unit : ∀ T c k, S.IsoFree T → S.FF T c k ≠ 0 → (S.FF T c k)⁻¹ ∈ M.ringOn U₀

def admitted (U₀ : M.Z.Opens) : Prop :=
  S.Over₀ M U₀ ∧ ∀ T c, S.IsoFree T → S.FF T c ≠ 0 → M.HasDiv (S.FF T c)

def At {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) : Prop :=
  ∀ a : S.R, y₀ a = M.val (gPt p ≫ y) a

def Test.E {S : ThetaSys o Ω} {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y) :
    Submodule (OO p) (S.J → PadicAlgCl p) :=
  Submodule.span (OO p) {v | ∃ (α : τ.X) (l : PadicAlgCl p) (i : S.J), (∀ v0, τ.q α ≤ τ.q (α + S.N • v0)) ∧
    ‖l‖ ≤ Real.exp (τ.q α / S.N) ∧ v = fun j => l * y (algebraMap o S.R (S.proj _ (τ.wt α) j i))}

def IsEE (U₀ : M.Z.Opens) (EE : M.Lat S.J) : Prop :=
  (∀ z ∈ U₀, EE.E z = Submodule.span (M.O z) (Set.range fun i => Pi.single i (1 : Ω))) ∧
  ∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀),
    M.Cen U₀ z y → S.At M y y₀ →
    Submodule.span (OO p) ((fun (v : S.J → Ω) j => M.val (gPt p ≫ y) (v j)) '' (EE.E z)) = τ.E
end ThetaSys

class ArithBase (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] : Prop where
  ded : IsDedekindDomain o
  ft : Algebra.FiniteType ℤ o
  char : CharZero Ω
  inj : Function.Injective (algebraMap o Ω)
end GlobalTheory.ZH
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH

abbrev kb (p : ℕ) [Fact p.Prime] : Type := IsLocalRing.ResidueField (OO p)

abbrev rPt (p : ℕ) [Fact p.Prime] : Sp (kb p) ⟶ Sp (OO p) := spMap (IsLocalRing.residue (OO p))

def Ser {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (N : ℕ) {J : Type} (cls : J → X) {C : Type} [NormedField C]
    (w : J → C) (ν : X →+ ℝ) : Prop :=
  ∃ (t : X → J → C) (κ : ℝ), 0 < κ ∧ (∀ i, HasSum (fun α => t α i) (w i)) ∧
    (∀ α i, t α i ≠ 0 → ∃ m, α = cls i + N • m) ∧
    ∀ α, (∀ i, ‖t α i‖ ≤ κ * Real.exp (-((q α - q (cls i)) / N + ν α))) ∧
      ∃ i, ‖t α i‖ = κ * Real.exp (-((q α - q (cls i)) / N + ν α))
attribute [local instance] SplitExt.free SplitExt.finite

structure Mod (p : ℕ) [Fact p.Prime] {V : Type} [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G]
    (g N : ℕ) {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) {J : Type} [Fintype J]
    (σ : J → H.Sec) (cls : J → X) where
  isLB : H.IsLB
  smooth : SmoothOfRelativeDimension g G.hom
  Φ : FibPre (kb p)
  r : Φ.G.left ⟶ G.left
  cart : IsGrpPullback Φ.G G (rPt p ≫ spMap j) r
  xe : Φ.E.X ≃+ X
  F : J → (Φ.H 1).Sec
  good : Φ.Good N (q.comp xe.toIntLinearEquiv.toLinearMap) (fun i => xe.symm (cls i)) F
  pol : Φ.Pol N
  dim : pol.PB.g + Module.finrank ℤ Φ.E.X = g
  red : ∀ (x : Φ.Pt) (v : J → kb p), Crd (Φ.H 1) F x.left v → Crd H σ (x.left ≫ r) v
  ser : ∀ a : Sp (PadicAlgCl p) ⟶ G.left, a ≫ G.hom = gPt p ≫ spMap j → ∀ w, Crd H σ a w →
    ∃ ν : X →+ ℝ, Ser q N cls w ν ∧ ((∃ m, ∀ α, ν α = QuadraticMap.polar q m α) →
      ∃ c : Sp (OO p) ⟶ G.left, c ≫ G.hom = spMap j ∧ gPt p ≫ c = a)
end GlobalTheory.ZH
end
end
