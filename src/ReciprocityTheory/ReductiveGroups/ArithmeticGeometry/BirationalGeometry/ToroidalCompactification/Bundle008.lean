module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.MetricSpace.Ultra.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

def eigLat {O : Type} (act : O → (G ⟶ G)) [∀ a, IsMonHom (act a)] (χ : O → R) : Submodule R (Fin n → R) :=
  ⨅ a, LinearMap.ker (tmap hx (act a) - χ a • LinearMap.id)

def dualMapR {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') : DualNumber R →+* DualNumber R' where
  toFun a := TrivSqZeroExt.inl (φ a.fst) + TrivSqZeroExt.inr (φ a.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp


end ReciprocityTheory.ChartRestriction.G.Chart
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

theorem mul_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x y : Over.mk a ⟶ G) (x' y' : Over.mk b ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left) :
    (x * y).left = (x' * y').left := by
  subst h
  have e1 : x = x' := Over.OverMorphism.ext hx
  have e2 : y = y' := Over.OverMorphism.ext hy
  subst e1 e2
  rfl

def pushPt {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) {T : Over S'} (x : T ⟶ G') : Over.mk (T.hom ≫ f) ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    show (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, w, ← Category.assoc, Over.w x])

theorem IsGrpPullback.comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (h' : IsGrpPullback G'' G' g φ') (h : IsGrpPullback G' G f φ) : IsGrpPullback G'' G (g ≫ f) (φ' ≫ φ) := by
  refine ⟨h'.1.paste_horiz h.1, ?_⟩
  intro T x y x₀ y₀ hx hy
  have w' : φ' ≫ G'.hom = G''.hom ≫ g := h'.1.w
  have h1 := h'.2 T x y (pushPt w' x) (pushPt w' y) rfl rfl
  let T' : Over S' := Over.mk (T.hom ≫ g)
  let x₁ : Over.mk (T'.hom ≫ f) ⟶ G := Over.homMk x₀.left (by rw [Over.w x₀]; simp [T'])
  let y₁ : Over.mk (T'.hom ≫ f) ⟶ G := Over.homMk y₀.left (by rw [Over.w y₀]; simp [T'])
  have h2 := h.2 T' (pushPt w' x) (pushPt w' y) x₁ y₁ (by simp [x₁, pushPt, hx]) (by simp [y₁, pushPt, hy])
  have h3 := mul_left_congr (G := G) (Category.assoc T.hom g f) x₁ y₁ x₀ y₀ rfl rfl
  rw [← h3, h2, h1, Category.assoc]

theorem IsGrpPullback.cancel {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (h : IsGrpPullback G' G f φ) (n : IsGrpPullback G'' G (g ≫ f) (φ' ≫ φ)) (w : φ' ≫ G'.hom = G''.hom ≫ g) :
    IsGrpPullback G'' G' g φ' := by
  refine ⟨IsPullback.of_right n.1 w h.1, ?_⟩
  intro T x y x₀ y₀ hx hy
  have hw : φ ≫ G.hom = G'.hom ≫ f := h.1.w
  have hn : (φ' ≫ φ) ≫ G.hom = G''.hom ≫ (g ≫ f) := n.1.w
  have h1 := h.2 (Over.mk (T.hom ≫ g)) x₀ y₀ (pushPt hw x₀) (pushPt hw y₀) rfl rfl
  have h2 := n.2 T x y (pushPt hn x) (pushPt hn y) rfl rfl
  have h3 := mul_left_congr (G := G) (Category.assoc T.hom g f) (pushPt hw x₀) (pushPt hw y₀)
    (pushPt hn x) (pushPt hn y) (by simp [pushPt, hx]) (by simp [pushPt, hy])
  apply h.1.hom_ext
  · rw [← h1, h3, h2, Category.assoc]
  · have a1 := Over.w (x₀ * y₀)
    have a2 := Over.w (x * y)
    rw [a1, Category.assoc, w, ← Category.assoc, a2]
    rfl

theorem psum_single {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (x : Fin 3 → (T ⟶ G))
    (i : Fin 3) : psum G x {i} = x i := by
  have e : (List.finRange 3).filter (· ∈ ({i} : Finset (Fin 3))) = [i] := by
    fin_cases i <;> decide
  simp only [psum, e, List.foldr_cons, List.foldr_nil, padd, pzero]
  first
    | simp
    | exact MonObj.lift_comp_one_right _ _

theorem hom_ext_triple {S : Scheme.{0}} (G : Over S) {X : Scheme.{0}} {a b : X ⟶ (G3 G).left}
    (h : ∀ i, a ≫ (x3 G i).left = b ≫ (x3 G i).left) : a = b := by
  have w : b ≫ (G3 G).hom = a ≫ (G3 G).hom := by
    have h0 := h 0
    have k := Over.w (x3 G 0)
    rw [← k, ← Category.assoc, ← Category.assoc, h0]
  let T : Over S := Over.mk (a ≫ (G3 G).hom)
  let A : T ⟶ G3 G := Over.homMk a rfl
  let B : T ⟶ G3 G := Over.homMk b w
  have hAB : A = B := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa [A, B, x3] using h 0
    · apply CartesianMonoidalCategory.hom_ext
      · ext
        simpa [A, B, x3] using h 1
      · ext
        simpa [A, B, x3] using h 2
  exact congrArg CommaMorphism.left hAB

theorem cubeMap_comp_proj_three {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (i : Fin 3) : m.F3 ≫ (x3 G i).left = (x3 G' i).left ≫ m.F := by
  have k := m.psum_comm {i}
  rw [psum_single, psum_single] at k
  exact k.symm

theorem sabComp (hC : PullCubCompSt) : SABCompSt := by
  intro E _ _ _ H S S' S'' t t' t'' f g m m'
  let cm : CubeMap t''.G t.G :=
    { F := m'.cm.F ≫ m.cm.F
      F3 := m'.cm.F3 ≫ m.cm.F3
      e := m'.cm.e ≫ m.cm.e
      e_comm := by
        rw [← Category.assoc, m'.cm.e_comm]
        simp only [Category.assoc, m.cm.e_comm]
      psum_comm := fun I => by
        rw [← Category.assoc, m'.cm.psum_comm I]
        simp only [Category.assoc, m.cm.psum_comm I] }
  refine ⟨{ cm := cm, cart := IsGrpPullback.comp m'.cart m.cart, base := ?_, act := ?_, lin := ?_ }, rfl⟩
  · show m'.cm.e ≫ m.cm.e = g ≫ f
    rw [m'.base, m.base]
  · intro a
    show _ ≫ (m'.cm.F ≫ m.cm.F) = (m'.cm.F ≫ m.cm.F) ≫ _
    rw [← Category.assoc, m'.act a]
    simp only [Category.assoc, m.act a]
  · exact hC S S' S'' t.G t'.G t''.G m.cm m'.cm cm t.PP t'.PP t''.PP t.cub t'.cub t''.cub rfl rfl rfl
      m.lin m'.lin

theorem sabCancel (hC : PullCubCancelSt) : SABCancelSt := by
  intro E _ _ _ H S S' S'' t t' t'' f g m n
  have hP := m.cart.1
  have hn : n.cm.F ≫ t.G.hom = t''.G.hom ≫ (g ≫ f) := n.cart.1.w
  let F' : t''.G.left ⟶ t'.G.left := hP.lift n.cm.F (t''.G.hom ≫ g) (by rw [hn, Category.assoc])
  have hF1 : F' ≫ m.cm.F = n.cm.F := hP.lift_fst _ _ _
  have hF2 : F' ≫ t'.G.hom = t''.G.hom ≫ g := hP.lift_snd _ _ _
  have hF1' : ∀ {Z : Scheme.{0}} (k : t.G.left ⟶ Z), F' ≫ m.cm.F ≫ k = n.cm.F ≫ k := by
    intro Z k; rw [← Category.assoc, hF1]
  have hF2' : ∀ {Z : Scheme.{0}} (k : S' ⟶ Z), F' ≫ t'.G.hom ≫ k = t''.G.hom ≫ g ≫ k := by
    intro Z k; rw [← Category.assoc, hF2, Category.assoc]
  let T : Over S' := Over.mk ((G3 t''.G).hom ≫ g)
  let p : Fin 3 → (T ⟶ t'.G) := fun i => Over.homMk ((x3 t''.G i).left ≫ F') (by
      show ((x3 t''.G i).left ≫ F') ≫ t'.G.hom = (G3 t''.G).hom ≫ g
      rw [Category.assoc, hF2, ← Category.assoc, Over.w (x3 t''.G i)])
  let L3 : T ⟶ G3 t'.G := lift (p 0) (lift (p 1) (p 2))
  let F3' : (G3 t''.G).left ⟶ (G3 t'.G).left := L3.left
  have hF3x : ∀ i, F3' ≫ (x3 t'.G i).left = (x3 t''.G i).left ≫ F' := by
    intro i
    show L3.left ≫ (x3 t'.G i).left = _
    rw [← Over.comp_left]
    fin_cases i <;> simp [L3, x3, p]
  have hF3 : F3' ≫ m.cm.F3 = n.cm.F3 := by
    apply hom_ext_triple t.G
    intro i
    rw [Category.assoc, cubeMap_comp_proj_three m.cm i, ← Category.assoc, hF3x i, Category.assoc, hF1,
      cubeMap_comp_proj_three n.cm i]
  have hT : F3' ≫ (G3 t'.G).hom = (G3 t''.G).hom ≫ g := Over.w L3
  let cm : CubeMap t''.G t'.G :=
    { F := F'
      F3 := F3'
      e := g
      e_comm := by
        apply hP.hom_ext
        · simp only [Category.assoc, hF1]
          rw [n.cm.e_comm, m.cm.e_comm, n.base, m.base, Category.assoc]
        · simp only [Category.assoc, hF2]
          have k1 := Over.w (η[t''.G] : 𝟙_ (Over S'') ⟶ t''.G)
          have k2 := Over.w (η[t'.G] : 𝟙_ (Over S') ⟶ t'.G)
          simp only [eSec]
          rw [← Category.assoc, k1, k2]
          simp
      psum_comm := fun I => by
        apply hP.hom_ext
        · simp only [Category.assoc, hF1, m.cm.psum_comm I]
          rw [n.cm.psum_comm I, ← Category.assoc, hF3]
        · have a1 := Over.w (psum t''.G (x3 t''.G) I)
          have a2 := Over.w (psum t'.G (x3 t'.G) I)
          rw [Category.assoc, hF2, ← Category.assoc, a1, Category.assoc, a2, hT] }
  have hcart : IsGrpPullback t''.G t.G (g ≫ f) (F' ≫ m.cm.F) := by
    have k := n.cart
    rw [← hF1] at k
    exact k
  refine ⟨{ cm := cm, cart := IsGrpPullback.cancel m.cart hcart hF2, base := rfl, act := ?_, lin := ?_ },
    hF1.symm⟩
  · intro a
    show (t''.act.act a).left ≫ F' = F' ≫ (t'.act.act a).left
    apply hP.hom_ext
    · simp only [Category.assoc, hF1, m.act a, hF1']
      rw [n.act a]
    · have a1 := Over.w (t''.act.act a)
      have a2 := Over.w (t'.act.act a)
      rw [Category.assoc, hF2, ← Category.assoc, a1, Category.assoc, a2, hF2]
  · exact hC S S' S'' t.G t'.G t''.G m.cm cm n.cm t.PP t'.PP t''.PP t.cub t'.cub t''.cub
      hF1.symm hF3.symm (by show n.cm.e = g ≫ m.cm.e; rw [n.base, m.base]) m.lin n.lin

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

section Siegel

variable {S : Scheme.{0}}

def omegaStd {h : ℕ} (a b : Fin h ⊕ Fin h → ℤ) : ℤ := ∑ i, (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i))

structure SiegPre (h M₁ : ℕ) {B : Type} [CommRing B] (ζ : B) (s : S ⟶ Sp B) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  P : LB (G2 A).left
  isLB : P.IsLB
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)
  lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)
  lev_add : ∀ a b, lev (a + b) = lev a * lev b
  lev_tors : ∀ a, lev a ^ M₁ = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (z : kˣ), x ≫ s = spMap β → (z : k) = β ζ →
    (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M₁ • b)) ∧
    (∀ g : Over.mk x ⟶ A, g ^ M₁ = 1 → ∃ a, toUnit _ ≫ lev a = g) ∧
    ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) M₁ (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b)
      (unitOn (z ^ (2 * omegaStd a b)))

attribute [instance] SiegPre.grp SiegPre.comm

variable {h M₁ : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {s : S ⟶ Sp B}

def SiegPre.diag (o : SiegPre h M₁ ζ s) : LB o.A.left := o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left

def SiegPre.Principal (o : SiegPre h M₁ ζ s) : Prop :=
  Out.RelAmple o.A o.diag ∧
    ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x = 1

def IsSquare {S' : Scheme.{0}} {G' : Over S'} {G : Over S} (φ : G'.left ⟶ G.left)
    (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left) : Prop :=
  φ₂ ≫ (fst G G).left = (fst G' G').left ≫ φ ∧ φ₂ ≫ (snd G G).left = (snd G' G').left ≫ φ

def SiegPB {S' : Scheme.{0}} {s' : S' ⟶ Sp B'} (o' : SiegPre h M₁ ζ' s') (o : SiegPre h M₁ ζ s) (f : S' ⟶ S) : Prop :=
  ∃ (φ : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left),
    IsGrpPullback o'.A o.A f φ ∧ IsSquare φ φ₂ ∧ LBIso o'.P (o.P.pull φ₂) ∧
      ∀ a, (o'.lev a).left ≫ φ = f ≫ (o.lev a).left

def ZP (p M : ℕ) : Subring ℂ := Subring.closure ({zeta M} ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹})

def zetaZP (p M : ℕ) : ZP p M := ⟨zeta M, Subring.subset_closure (Or.inl rfl)⟩

def IsUnitBall (O C : Type) [CommRing O] [NormedField C] [Algebra O C] : Prop :=
  Function.Injective (algebraMap O C) ∧ ∀ x : C, x ∈ Set.range (algebraMap O C) ↔ ‖x‖ ≤ 1

structure SiegelFamily (h p M₁ : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp (ZP p M₁)
  smooth : SmoothOfRelativeDimension (h * (h + 1) / 2) s
  qc : QuasiCompact s
  univ : SiegPre h M₁ (zetaZP p M₁) s
  princ : univ.Principal

  points : ∀ (C O : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
    [CommRing O] [IsLocalRing O] [Algebra O C], IsUnitBall O C → ‖(p : C)‖ < 1 →
    ∀ (β : ZP p M₁ →+* O) (o : SiegPre h M₁ (zetaZP p M₁) (spMap β)),
      (∃ o' : SiegPre h M₁ (zetaZP p M₁) (spMap (algebraMap O C) ≫ spMap β),
        SiegPB o' o (spMap (algebraMap O C)) ∧ o'.Principal) →
      Out.RelAmple (Over.mk (pullback.snd o.A.hom (spMap (IsLocalRing.residue O))))
        (o.diag.pull (pullback.fst o.A.hom (spMap (IsLocalRing.residue O)))) →
      ∃ x : Sp O ⟶ X, x ≫ s = spMap β ∧ SiegPB o univ x

  unram : ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ X) (o : SiegPre h M₁ (zetaZP p M₁) (x ≫ s)),
    SiegPB o univ x → SiegPB o univ (constPt x) → x = constPt x

def N0 : Prop :=
  ∀ h p n : ℕ, 1 ≤ h → p.Prime → n.Prime → Odd n → n ≠ p →
    ∃ j : ℕ, 3 ≤ n ^ j ∧ Nonempty (SiegelFamily h p (n ^ j))

end Siegel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

structure Idx (H : Host E) (p : ℕ) where
  l : Level H
  c : Coeff l
  good : l.GoodAt p

abbrev Coeff.V {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) : ValuationSubring c.F :=
  W.comap c.F.val.toRingHom

abbrev LocalSystem (Xo : ∀ l : Level H, Moduli D l) (p : ℕ) (W : ValuationSubring ℂ) :=
  ∀ i : Idx H p, Model (Xo i.l) i.c (i.c.V W).subtype

section Local

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def Model.GoodRedExt (Y : Model Xo c β) (V K : Type) [CommRing V] [Field K] [Algebra V K] : Prop :=
  ∀ (b : O →+* V) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j ≫ Y.s = spMap (algebraMap V K) ≫ spMap b →
    (∃ (𝒜 : Over (Sp V)) (_ : GrpObj 𝒜) (𝓛 : LB 𝒜.left) (A : Over (Sp K)) (_ : GrpObj A)
      (φ₁ : A.left ⟶ 𝒜.left) (φ₂ : A.left ⟶ Y.oF.t.G.left),
      IsAbelianScheme 𝒜 ∧ 𝓛.IsLB ∧ Out.RelAmple 𝒜 𝓛 ∧ IsGrpPullback A 𝒜 (spMap (algebraMap V K)) φ₁ ∧
      IsGrpPullback A Y.oF.t.G y φ₂ ∧ LBIso (𝓛.pull φ₁) (Y.oF.t.PP.L.pull φ₂)) →
    ∃ y' : Sp V ⟶ Y.X, y' ≫ Y.s = spMap b ∧ spMap (algebraMap V K) ≫ y' = y ≫ Y.j ∧
      Set.range y' ⊆ abLocus Y.t.G

def Model.LevelStructureConditions (Y : Model Xo c β) (p : ℕ) : Prop :=
  Y.LevelActs ∧ (l.A = 1 → Y.Descends) ∧ PushInvertible Y.t.G Y.t.PP.L ∧
  (∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ ∀ (a : D.La) (n : ℕ), n.Coprime p →
    (Y.oF.eta a ^ n = 1 → Y.Extends U (Y.oF.eta a)) ∧ (Y.oF.etaA a ^ n = 1 → Y.Extends U (Y.oF.etaA a))) ∧
  (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [Field K] [Algebra V K] [IsFractionRing V K], Y.GoodRedExt V K) ∧
  ∀ (V C : Type) [CommRing V] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [CharZero C] [Algebra V C], IsUnitBall V C → ‖(p : C)‖ < 1 → Y.GoodRedExt V C

def SiegelCompare {l₁ : Level H} {Xo₁ : Moduli D l₁} {c₁ : Coeff l₁} {O₁ : Type} [CommRing O₁] {β₁ : O₁ →+* c₁.F}
    (Y : Model Xo c β) (Y₁ : Model Xo₁ c₁ β₁) (b : O →+* O₁) (π : Y₁.X ⟶ Y.X) {g p M₁ : ℕ}
    (Ag : SiegelFamily g p M₁) (z : ZP p M₁ →+* O₁) : Prop :=
  ∀ (U : Y.X.Opens) (U₁ : Y₁.X.Opens), (U : Set Y.X) = abLocus Y.t.G → (U₁ : Set Y₁.X) = abLocus Y₁.t.G →
    (∃ e : U₁.toScheme ⟶ pullback (U.ι ≫ Y.s) (spMap b),
      e ≫ pullback.fst _ _ ≫ U.ι = U₁.ι ≫ π ∧ e ≫ pullback.snd _ _ = U₁.ι ≫ Y₁.s ∧
      IsFinite e ∧ Etale e ∧ Surjective e) ∧
    ∃ (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (cl : U₁.toScheme ⟶ pullback Ag.s (spMap z))
      (o : SiegPre g M₁ (zetaZP p M₁) (U₁.ι ≫ Y₁.s ≫ spMap z)) (φ : o.A.left ⟶ Y₁.t.G.left)
      (φ₂ : (G2 o.A).left ⟶ (G2 Y₁.t.G).left),
      (∀ u v, D.EF (bas u) (bas v) = omegaStd u v) ∧
      IsGrpPullback o.A Y₁.t.G U₁.ι φ ∧ IsSquare φ φ₂ ∧ LBIso o.P ((abelian₂ Y₁.t.G Y₁.t.PP.L).pull φ₂) ∧
      (∀ u (j' : Xo₁.XF c₁ ⟶ U₁.toScheme), j' ≫ U₁.ι = Y₁.j →
        j' ≫ (o.lev u).left ≫ φ = (Y₁.oF.etaA (bas u) ^ (l₁.A / M₁)).left ≫ Y₁.m.φ) ∧
      cl ≫ pullback.snd _ _ = U₁.ι ≫ Y₁.s ∧ SiegPB o Ag.univ (cl ≫ pullback.fst _ _) ∧ IsFinite cl ∧
      (¬ p ∣ l.M' →
        ∃ (XX : Scheme.{0}) (u : U₁.toScheme ⟶ XX) (w : XX ⟶ pullback Ag.s (spMap z)) (W : XX.Opens)
          (t : SAB H XX) (t₁ : SAB H U₁.toScheme) (m₁ : SABMap t₁ Y₁.t U₁.ι) (m₂ : SABMap t₁ t u)
          (η' ηA' : D.La → (𝟙_ (Over XX) ⟶ t.G)),
          u ≫ w = cl ∧ IsFinite u ∧ Surjective u ∧ Dense (W : Set XX) ∧ IsIso (u ∣_ W) ∧
          Dense ((u ⁻¹ᵁ W : U₁.toScheme.Opens) : Set U₁.toScheme) ∧
          IsAbelianScheme t.G ∧ IsReduced XX ∧ Flat (w ≫ pullback.snd _ _) ∧ IsFinite w ∧ FormallyUnramified w ∧
          ∀ (a : D.La) (j' : Xo₁.XF c₁ ⟶ U₁.toScheme) (g₁ : Xo₁.XF c₁ ⟶ t₁.G.left), j' ≫ U₁.ι = Y₁.j →
            (g₁ ≫ m₁.φ = (Y₁.oF.eta a).left ≫ Y₁.m.φ → g₁ ≫ m₂.φ = j' ≫ u ≫ (η' a).left) ∧
            (g₁ ≫ m₁.φ = (Y₁.oF.etaA a).left ≫ Y₁.m.φ → g₁ ≫ m₂.φ = j' ≫ u ≫ (ηA' a).left))

end Local

def IsIncl {l l₂ : Level H} {c : Coeff l} {c₂ : Coeff l₂} {W : ValuationSubring ℂ} (b : c.V W →+* c₂.V W) : Prop :=
  ∀ x : c.V W, (((b x : c₂.V W) : c₂.F) : ℂ) = ((x : c.F) : ℂ)

def N2 {Xo : ∀ l : Level H, Moduli D l} {p : ℕ} {W : ValuationSubring ℂ} (Y : LocalSystem Xo p W) : Prop :=
  (∀ i, (Y i).LevelStructureConditions p) ∧
  ∃ π : ∀ i i₂ : Idx H p, i.l.Dvd i₂.l → i.c.F ≤ i₂.c.F → ((Y i₂).X ⟶ (Y i).X),
    (∀ i i₂ hl hc (b : i.c.V W →+* i₂.c.V W), IsIncl b → IsTransition (Y i) (Y i₂) b (π i i₂ hl hc)) ∧
    ∃ (n j : ℕ) (Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p (n ^ j)),
      n.Prime ∧ Odd n ∧ n ≠ p ∧ 3 ≤ n ^ j ∧ (∀ l : Level H, n.Coprime l.M) ∧
      ∀ i i₁ hl hc (b : i.c.V W →+* i₁.c.V W) (z : ZP p (n ^ j) →+* i₁.c.V W), IsIncl b →
        (∀ x, (((z x : i₁.c.V W) : i₁.c.F) : ℂ) = (x : ℂ)) →
        i₁.l.M = i.l.M → i₁.l.Mb = i.l.Mb → i₁.l.A = Nat.lcm i.l.A (n ^ j) →
        i₁.c.F = i.c.F ⊔ IntermediateField.adjoin ℚ {zeta (n ^ j)} →
        SiegelCompare (Y i) (Y i₁) b (π i i₁ hl hc) Ag z

def N6 {Xo : ∀ l : Level H, Moduli D l}
    (Y : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W) : Prop :=
  ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p), l.A = 1 →
    ∃ Ygl : Model (Xo l) c (algebraMap (𝓞 c.F) c.F), Ygl.Descends ∧
      ∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W),
        (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → Dominates Ygl (Y p W hp hW ⟨l, c, hg p hp⟩) b

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
