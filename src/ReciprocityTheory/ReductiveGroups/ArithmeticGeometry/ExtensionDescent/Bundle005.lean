module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

namespace GeneratorPullback

section Lin

variable {X Y Y' : Scheme.{0}} (L : LB X) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

def SecLin (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) {n : ℕ} (s₂ : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂))
    (h : Y' ⟶ Y) (c : Fin n → Γ(Y', ⊤)) : Prop :=
  ∀ (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι),
    LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim j₁ j₂) →
    (Y'.presheaf.map (homOfLE (inf_le_left :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤ LB.wchart L φ₁ j₁)).op).hom
        (s₁.f j₁) =
      ∑ i, resTop _ (c i) *
        (Y'.presheaf.map (homOfLE (inf_le_right.trans
          (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
          LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤
            h ⁻¹ᵁ LB.wchart L φ₂ j₂)).op).hom ((h.app (LB.wchart L φ₂ j₂)).hom ((s₂ i).f j₂))

end Lin

section IsoRel

variable {Y Y' X₁ X₂ Z₁ Z₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂)

abbrev isoW (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (m : Y' ⟶ Y) (g₁ : Z₁ ⟶ X₁) (h₁ : Y' ⟶ Z₁)
    (g₂ : Z₂ ⟶ X₂) (h₂ : Y' ⟶ Z₂) (p : (PUnit.{1} → L₂.ι) × (PUnit.{1} → L₁.ι))
    (j₁ : Fin 1 → L₁.ι) (j₂ : Fin 1 → L₂.ι) : Y'.Opens :=
  m ⁻¹ᵁ (LB.div (L₂.pull f₂) (L₁.pull f₁)).U p ⊓
    h₁ ⁻¹ᵁ LB.wchart L₁ (fun _ : Fin 1 => g₁) j₁ ⊓ h₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => g₂) j₂

def IsoRelM (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (m : Y' ⟶ Y)
    (k : ℕ) (g₁ : Z₁ ⟶ X₁) (h₁ : Y' ⟶ Z₁)
    (a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ))))
    (g₂ : Z₂ ⟶ X₂) (h₂ : Y' ⟶ Z₂)
    (b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ)))) : Prop :=
  h₁ ≫ g₁ = m ≫ f₁ ∧ h₂ ≫ g₂ = m ≫ f₂ ∧
  ∀ (p : (PUnit.{1} → L₂.ι) × (PUnit.{1} → L₁.ι)) (j₁ : Fin 1 → L₁.ι) (j₂ : Fin 1 → L₂.ι),
    j₁ 0 = p.2 PUnit.unit → j₂ 0 = p.1 PUnit.unit →
    (Y'.presheaf.map (homOfLE (inf_le_right :
        isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ p j₁ j₂ ≤ h₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => g₂) j₂)).op).hom
        ((h₂.app _).hom (b.f j₂)) =
      (res (inf_le_left.trans inf_le_left :
          isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ p j₁ j₂ ≤ m ⁻¹ᵁ (LB.div (L₂.pull f₂) (L₁.pull f₁)).U p)
          (pullU m _ (w.s p))).val ^ k *
      (Y'.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
        isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ p j₁ j₂ ≤ h₁ ⁻¹ᵁ LB.wchart L₁ (fun _ : Fin 1 => g₁) j₁)).op).hom
        ((h₁.app _).hom (a.f j₁))

end IsoRel

end GeneratorPullback

section ExpansionF

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

namespace UnifPre

variable (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]

abbrev GF : Over (TK R).left := TFK (R := R) F ⊗ (Over.pullback (jK R)).obj G

abbrev gFK : (GF (G := G) F).left ⟶ G.left :=
  (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.fst G.hom (jK R)

abbrev genF : GF (G := G) F ⟶ TFK (R := R) F ⊗ A.A :=
  lift (fst _ _) (snd _ _ ≫ U.gen.hom)

abbrev SecGF (k : ℕ) : Type :=
  LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => gFK (G := G) F) (fun _ => (k : ℤ)))

def ExpandsG (k : ℕ) (σ' : U.SecGF F k) (s : Fam D.toPre F k) : Prop :=
  ∃ (n : ℕ) (c : Fin n → F)
    (σ : Fin n → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : Fin n → ∀ α : D.toPre.X, D.toPre.SecB k α),
    (∀ i e, U.ExpandsAt e k (σ i) (f i)) ∧
    GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => gFK (G := G) F) (fun _ => (k : ℤ)) σ'
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (gFK (G := G) F)
      (fun i => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c i)) ∧
    ∀ α : D.toPre.X,
      GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
        (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left
        (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i))

def ExpandsF (k : ℕ)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))))
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s : Fam D.toPre F k) : Prop :=
  ∃ σ' : U.SecGF F k,
    GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k
      (snd (TFK (R := R) F) A.A).left (U.genF F).left t
      (gFK (G := G) F) (𝟙 _) σ' ∧
    U.ExpandsG F k σ' s

end UnifPre

end ExpansionF

end ReciprocityTheory.ChartRestriction.G.Out
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

namespace GeneratorPullback

variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

def finProdGen {J : Type} [Fintype J] (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) :
    LB.Gen (LB.LinComb L (K := J × K) (fun p => φ p.1 p.2) (fun p => ε p.1 p.2)) where
  s := fun j => ∏ i, res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)) :
      LB.wchart L (fun p : J × K => φ p.1 p.2) j ≤ LB.wchart L (φ i) (fun k => j (i, k)))
    ((t i).s _)

variable {X' : Scheme.{0}} (L' : LB X') {J : Type} [Fintype J]

lemma mapsAt_le_b (pr : J → (X' ⟶ X)) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr (fun _ => 1)) L').U (jN, jL) ≤
      LB.wchart L (fun i => p ≫ pr i) jN := by
  intro x hx
  first
  | exact Set.mem_iInter.2 fun i => Set.mem_iInter.1 hx.2 i
  | exact Set.mem_iInter.2 fun i => Set.mem_iInter.1 hx.1 i

lemma mapsAt_le_a (pr : J → (X' ⟶ X)) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr (fun _ => 1)) L').U (jN, jL) ≤
      LB.wchart L' (fun _ : PUnit => p) (fun _ => jL) := by
  intro x hx
  first
  | exact Set.mem_iInter.2 fun _ => hx.1
  | exact Set.mem_iInter.2 fun _ => hx.2

def MapsAt (pr : J → (X' ⟶ X)) (w : LB.Iso L' (LB.LinComb L pr (fun _ => 1))) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun _ => n))) : Prop :=
  ∀ (jN : J → L.ι) (jL : L'.ι),
    res (mapsAt_le_b L L' pr p jN jL) (b.s jN) =
      (pullU p _ (w.s (jN, jL))) ^ n * res (mapsAt_le_a L L' pr p jN jL) (a.s (fun _ => jL))

end GeneratorPullback

section Pow

variable {S : Scheme.{0}}

structure IsPowPolAV (P' P : PolAV S) (j : ℕ) extends IsPowGrp P'.A P.A j where
  w : LB.Iso P'.L (boxLB P.L pr)
  w_gen : w.IsGen

end Pow

section PowDeg

variable {R : Type} [CommRing R] [IsDomain R]

structure IsPowDeg (D' D : DegPre R) (j : ℕ) where
  pw : IsPowGrp D'.P.A D.P.A j
  w : LB.Iso D'.P.L (boxLB D.P.L pw.pr)
  w_gen : w.IsGen
  w_rig : ∃ b : LB.Gen (LB.LinComb D.P.L (K := Fin j)
      (fun i => eSec D'.P.A ≫ (pw.pr i).left) (fun _ => 1)),
    GeneratorPullback.MapsAt D.P.L D'.P.L (fun i => (pw.pr i).left) w (eSec D'.P.A) 1 D'.rig b ∧
    LB.Gen.Corr D.P.L _ _ _ _ b
      (GeneratorPullback.finProdGen D.P.L (J := Fin j) (fun _ _ => eSec D.P.A) (fun _ _ => 1) (fun _ => D.rig))
  xe : D'.X ≃+ (Fin j → D.X)
  c_pr : ∀ (x : D'.X) (i : Fin j), D'.c x ≫ pw.pr i = D.c (xe x i)
  w_psi : ∀ x : D'.X, ∃ b : LB.Gen (LB.LinComb D.P.L (K := Fin j)
      (fun i => D'.xK x ≫ (pw.pr i).left) (fun _ => -1)),
    GeneratorPullback.MapsAt D.P.L D'.P.L (fun i => (pw.pr i).left) w (D'.xK x) (-1) (D'.psi x) b ∧
    LB.Gen.Corr D.P.L _ _ _ _ b
      (GeneratorPullback.finProdGen D.P.L (J := Fin j) (fun i _ => D.xK (xe x i)) (fun _ _ => -1)
        (fun i => D.psi (xe x i)))

end PowDeg

section UnifPow

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

structure UnifPowOf {j : ℕ} {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j)
    (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) where
  gen_pr : ∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom
  wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)
  wL_gen : wL.IsGen
  wL_rig : ∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j)
      (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)),
    GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧
    LB.Gen.Corr U.LG.L _ _ _ _ b
      (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))
  q_pr : ∀ (e : ℕ) (i : Fin j),
    (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) =
      (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q

end UnifPow

end ReciprocityTheory.ChartRestriction.G.Out
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def SecBaseChangeAnySt : Prop :=
  ∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), 1 ≤ n →
    ∀ p : S, ∃ V : S.Opens, p ∈ V ∧ ∃ b : Fin (n ^ P.g) → LB.Sec (LPow P.A P.L n (overRes (T := baseOver S) V)),
      ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left)
        (b' : Fin (n ^ P.g) → LB.Sec (LPow P.A P.L n (baseAt t))),
        (∀ i, IsPullSec P.A P.L n (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i) (b' i)) →
        LinearIndependent Γ((baseAt t).left, ⊤)
            (fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))) ∧
          Submodule.span Γ((baseAt t).left, ⊤)
            (Set.range fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))) = ⊤

def twistLB {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (q : ℕ) {T : Over S}
    (c : T ⟶ A) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(snd T A).left, (translPt A c).left] ![(q : ℤ) - 1, 1]

def IsSecBasis {S : Scheme.{0}} {A : Over S} {T : Over S} (N : LB (T ⊗ A).left) {m : ℕ}
    (b : Fin m → LB.Sec N) : Prop :=
  ∀ s : LB.Sec N, ∃! r : Fin m → Γ(T.left, ⊤), ∀ j,
    s.f j = ∑ i, ((T ⊗ A).left.presheaf.map (homOfLE le_top).op).hom
      ((fst T A).left.appTop.hom (r i)) * (b i).f j

theorem wchart_comp_le {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (h : Y' ⟶ Y) (j : K → L.ι) : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j := by
  intro y hy
  have hy' := Set.mem_iInter.1 hy
  show h.base y ∈ (⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X))
  exact Set.mem_iInter.2 fun k => by simpa [Scheme.Hom.comp_base] using hy' k

def IsPullSecLC {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε)) :
    Prop :=
  ∀ j, s'.f j = (Y'.presheaf.map (homOfLE (wchart_comp_le L φ h j)).op).hom ((h.app _).hom (s.f j))

def SecTwistSt : Prop :=
  ∀ (S : Scheme.{0}) (P : PolAV S) (q : ℕ), 1 ≤ q →
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : Spec (CommRingCat.of R) ⟶ S)
      (c : Over.mk t ⟶ P.A),
      (∃ b : Fin (q ^ P.g) → LB.Sec (twistLB P.A P.L q c), IsSecBasis _ b) ∧
      ∀ sbar : LB.Sec (LB.LinComb P.L (K := Fin 2)
          (fun k => ((Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) rfl :
            Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ t) ⟶ Over.mk t) ▷ P.A).left ≫
              ![(snd (Over.mk t) P.A).left, (translPt P.A c).left] k) ![(q : ℤ) - 1, 1]),
        ∃ s : LB.Sec (twistLB P.A P.L q c), IsPullSecLC P.L _ _ _ s sbar

def CharPairSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (N : ℕ), (N : K) ≠ 0 →
    ∀ χ : {x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ N = 1} →
        Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ,
      (∀ x y, χ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, _root_.one_mul]⟩ = χ x * χ y) →
      ∃! b : baseOver (Spec (CommRingCat.of K)) ⟶ P.A, b ^ N = 1 ∧
        ∀ x, WeilIs P.A P.L N x.1 b (χ x)

def SmoothDenseSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsReduced X → LocallyOfFiniteType f →
    Dense {x : X | ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)}

structure Laws2 : Prop where
  secBaseChangeAny : SecBaseChangeAnySt
  secTwist : SecTwistSt
  charPair : CharPairSt
  smoothDense : SmoothDenseSt

end ReciprocityTheory.ChartRestriction.G.Out
end
end
