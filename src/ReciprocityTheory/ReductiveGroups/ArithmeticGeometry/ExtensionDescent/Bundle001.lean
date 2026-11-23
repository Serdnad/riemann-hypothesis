module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.NNReal.Defs

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def stdSymp (g : ℕ) (i j : Fin (2 * g)) : ℤ :=
  if (i : ℕ) < g ∧ (j : ℕ) = (i : ℕ) + g then 1
  else if (j : ℕ) < g ∧ (i : ℕ) = (j : ℕ) + g then -1 else 0

variable {S : Scheme.{0}}

abbrev baseOver (S : Scheme.{0}) : Over S := Over.mk (𝟙 S)

def linComb {A : Over S} [GrpObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) :
    T ⟶ A :=
  (List.ofFn fun i => y i ^ a i).prod

structure Level (P : PolAV S) (k : ℕ) (ze : Γ(S, ⊤)ˣ) where

  pt : Fin (2 * P.g) → (baseOver S ⟶ P.A)

  prim : IsPrimitiveRoot ze k

  torsion : ∀ i, pt i ^ k = 1

  indep : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (c c' : Fin (2 * P.g) → Fin k),
    linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c i : ℕ)) =
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c' i : ℕ)) →
    c = c'

  span : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (y : Over.mk s ⟶ P.A), y ^ k = 1 →
    ∃ c : Fin (2 * P.g) → Fin k,
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c i : ℕ)) = y

  pairing : ∀ i j, WeilIs P.A P.L k (pt i) (pt j) (ze ^ stdSymp P.g i j)

def Level.toPt {P : PolAV S} {k : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P k ze)
    (a : Fin (2 * P.g) → ZMod k) : baseOver S ⟶ P.A :=
  linComb lev.pt (fun i => (a i).val)

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

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def negT (T : Over S) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A ≫ (GrpObj.inv : A ⟶ A))

def negLB (L : LB A.left) (k : ℤ) (T : Over S) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k]

def powφ {T : Over S} (x : T ⟶ A) (n : ℕ) : Fin n × Fin 2 → ((T ⊗ A).left ⟶ A.left) :=
  fun p => (translT A (x ^ (p.1 : ℕ))).left ≫ (![(snd T A).left, (translPt A x).left] p.2)

def powε (k : ℤ) (n : ℕ) : Fin n × Fin 2 → ℤ := fun p => ![k, -k] p.2

def powGen (L : LB A.left) (k : ℤ) {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) :
    LB.Gen (LB.LinComb L (powφ A θ.pt n) (powε k n)) where
  s := fun j => ∏ j₀ : Fin n,
    res ((fun _ hy => Set.mem_iInter.2 fun b => Set.mem_iInter.1 hy (j₀, b)) :
        LB.wchart L (powφ A θ.pt n) j ≤
          LB.wchart L (fun b => (translT A (θ.pt ^ (j₀ : ℕ))).left ≫
            (![(snd T A).left, (translPt A θ.pt).left] b)) (fun b => j (j₀, b)))
      ((LB.pullGen L _ _ θ.φ (translT A (θ.pt ^ (j₀ : ℕ))).left).s (fun b => j (j₀, b)))

def symGen (L : LB A.left) (k : ℤ) {T : Over S} (θ : ThetaGrp A L k T)
    (nu : LB.Gen (negLB A L k T)) :=
  LB.mulGen L _ _ _ _
    (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ θ.φ (translT A θ.pt⁻¹).left) nu)
    (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ θ.φ (negT A T).left)
      (LB.invGen L _ _ (LB.pullGen L _ _ nu (translT A θ.pt⁻¹).left)))

structure SymLift (L : LB A.left) (k : ℤ) (n : ℕ) {T : Over S} (x : T ⟶ A)
    (θ : ThetaGrp A L k T) : Prop where

  pt_eq : θ.pt = x

  pow_eq : LB.Gen.Corr L _ _ _ _ (powGen A L k θ n) (LB.oneGen L)

  sym : ∃ nu : LB.Gen (negLB A L k T), nu.IsGen ∧ LB.Gen.Corr L _ _ _ _ (symGen A L k θ nu) (LB.oneGen L)

def LPow (L : LB A.left) (a : ℤ) (T : Over S) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 1) (fun _ => (snd T A).left) (fun _ => a)

def liftFun {T : Over S} (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤)) : Γ((T ⊗ A).left, W) :=
  ((T ⊗ A).left.presheaf.map (homOfLE le_top).op).hom ((fst T A).left.appTop.hom r)

theorem chart_le_zero (L : LB A.left) {T : Over S} (m : T ⊗ A ⟶ A) (j : Fin 2 → L.ι) :
    LB.wchart L ![(snd T A).left, m.left] j ≤ LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0) :=
  fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0

theorem chart_le_pull (L : LB A.left) {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A)
    (hm : ψ ≫ snd T A = m) (j : Fin 2 → L.ι) :
    LB.wchart L ![(snd T A).left, m.left] j ≤
      ψ.left ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1) := by
  intro y hy
  have h1 : m.left.base y ∈ (L.U (j 1) : Set A.left) := Set.mem_iInter.1 hy 1
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  rw [← e] at h1
  exact Set.mem_iInter.2 fun _ => h1

def IsTwistPull (L : LB A.left) {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A)
    (hm : ψ ≫ snd T A = m) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b]))
    (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)) : Prop :=
  ∀ j : Fin 2 → L.ι,
    ((T ⊗ A).left.presheaf.map (homOfLE (chart_le_zero A L m j)).op).hom (s'.f (fun _ => j 0)) =
      (show Γ((T ⊗ A).left, LB.wchart L ![(snd T A).left, m.left] j) from (α.s j).val) *
        ((T ⊗ A).left.presheaf.map (homOfLE (chart_le_pull A L ψ m hm j)).op).hom
          ((ψ.left.app _).hom (s.f (fun _ => j 1)))

def IsActOf (L : LB A.left) (k : ℤ) {T : Over S} (θ : ThetaGrp A L k T) (s s' : LB.Sec (LPow A L k T)) : Prop :=
  IsTwistPull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) k k θ.φ s s'

def IsGenSec (L : LB A.left) (a : ℤ) {T : Over S} (th : LB.Sec (LPow A L a T)) : Prop :=
  ∀ s : LB.Sec (LPow A L a T), ∃ r : Γ(T.left, ⊤), ∀ j, s.f j = liftFun A _ r * th.f j

def ptSecT {T : Over S} (z : T ⟶ A) : T ⟶ T ⊗ A := lift (𝟙 T) z

theorem val_le (L : LB A.left) {T : Over S} (z : T ⟶ A) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => z.left) j ≤
      (ptSecT A z).left ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => (snd T A).left) j := by
  intro y hy
  have h1 : z.left.base y ∈ (L.U (j 0) : Set A.left) := Set.mem_iInter.1 hy 0
  have e : (ptSecT A z).left ≫ (snd T A).left = z.left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  rw [← e] at h1
  exact Set.mem_iInter.2 fun i => by
    rw [Subsingleton.elim i 0]; exact h1

def IsValueAt (L : LB A.left) (a : ℤ) {T : Over S} (s : LB.Sec (LPow A L a T)) (z : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)))
    (v : Γ(T.left, ⊤)) : Prop :=
  ∀ j : Fin 1 → L.ι,
    (T.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (s.f j)) =
      (T.left.presheaf.map (homOfLE le_top).op).hom v * (show Γ(T.left, LB.wchart L (fun _ : Fin 1 => z.left) j) from (τ.s j).val)

def mulT (T : Over S) (k : ℕ) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A ^ k)

def IsThetaPtOver (P : PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (v : I → Γ(T.left, ⊤)) : Prop :=
  ∃ (th : LB.Sec (LPow P.A P.L 1 T)) (s1 : LB.Sec (LPow P.A P.L ((k : ℤ) ^ 2) T))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![(k : ℤ) ^ 2, -1]))
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left)
      (fun _ => (k : ℤ) ^ 2)))
    (U : I → ThetaGrp P.A P.L ((k : ℤ) ^ 2) T) (s2 : I → LB.Sec (LPow P.A P.L ((k : ℤ) ^ 2) T))
    (w : I → Γ(T.left, ⊤)) (u : Γ(T.left, ⊤)ˣ),
    IsGenSec P.A P.L 1 th ∧ α.IsGen ∧ τ.IsGen ∧
    IsTwistPull P.A P.L (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _) ((k : ℤ) ^ 2) 1 α th s1 ∧
    (∀ i, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) (U i)) ∧
    (∀ i, IsActOf P.A P.L ((k : ℤ) ^ 2) (U i) s1 (s2 i)) ∧
    (∀ i, IsValueAt P.A P.L ((k : ℤ) ^ 2) (s2 i) 1 τ (w i)) ∧
    ∀ i, v i = (u : Γ(T.left, ⊤)) * w i

def IsThetaPt (P : PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (v : I → Γ(T.left, ⊤)) : Prop :=
  Odd k ∧ IsUnit (k : Γ(T.left, ⊤)) ∧ ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
    IsThetaPtOver P k (fun i => overResι V ≫ x i) (fun i => V.ι.appTop.hom (v i))

def IsVVGen (P : PolAV S) (N m : ℕ) {T : Over S} (t : LB.Sec (LPow P.A P.L N T)) : Prop :=
  ∃ (th : LB.Sec (LPow P.A P.L 1 T)) (s1 : LB.Sec (LPow P.A P.L N T))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]))
    (U : ThetaGrp P.A P.L N T),
    α.IsGen ∧ IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) N 1 α th s1 ∧
    IsActOf P.A P.L N U s1 t

def InVVOver (P : PolAV S) (N m : ℕ) {T : Over S} (s : LB.Sec (LPow P.A P.L N T)) : Prop :=
  ∃ (n : ℕ) (r : Fin n → Γ(T.left, ⊤)) (t : Fin n → LB.Sec (LPow P.A P.L N T)),
    (∀ l, IsVVGen P N m (t l)) ∧ ∀ j, s.f j = ∑ l, liftFun P.A _ (r l) * (t l).f j

theorem chart_le_res (L : LB A.left) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A)
    (a : ℤ) (j : Fin 1 → L.ι) :
    (LPow A L a T').U j ≤ h.left ⁻¹ᵁ (LPow A L a T).U j := by
  intro y hy
  have h1 : (snd T' A).left.base y ∈ (L.U (j 0) : Set A.left) := Set.mem_iInter.1 hy 0
  have e : h.left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, hh]
  rw [← e] at h1
  exact Set.mem_iInter.2 fun i => by
    rw [Subsingleton.elim i 0]; exact h1

def IsPullSec (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A)
    (hh : h ≫ snd T A = snd T' A) (s : LB.Sec (LPow A L a T)) (s' : LB.Sec (LPow A L a T')) : Prop :=
  ∀ j, s'.f j = ((T' ⊗ A).left.presheaf.map (homOfLE (chart_le_res A L h hh a j)).op).hom
    ((h.left.app _).hom (s.f j))

def InVV (P : PolAV S) (N m : ℕ) {T : Over S} (s : LB.Sec (LPow P.A P.L N T)) : Prop :=
  ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ sV : LB.Sec (LPow P.A P.L N (overRes V)),
    IsPullSec P.A P.L N (overResι V ▷ P.A) (whiskerRight_snd _ _) s sV ∧ InVVOver P N m sV

def IsEvT (P : PolAV S) (N : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (τ : ∀ i, LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (x i).left) (fun _ => (N : ℤ))))
    (s : LB.Sec (LPow P.A P.L N T)) (w : I → Γ(T.left, ⊤)) : Prop :=
  ∀ i, IsValueAt P.A P.L N s (x i) (τ i) (w i)

end ReciprocityTheory.ChartRestriction.G.Out
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.Inh

open Semi

instance geomConn_id (S : Scheme.{0}) : GeometricallyConnected (𝟙 S) := by
  rw [geometricallyConnected_iff]
  intro K _ y Z fst snd h
  have h' : IsPullback y (𝟙 _) (𝟙 S) y := IsPullback.of_vert_isIso ⟨by simp⟩
  let e : Z ≅ Spec (CommRingCat.of K) := h.isoIsPullback _ _ h'
  exact (Scheme.homeoOfIso e.symm).surjective.connectedSpace (Scheme.homeoOfIso e.symm).continuous

def trivLB (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

theorem trivLB_isLB (X : Scheme.{0}) : (trivLB X).IsLB := by
  refine ⟨?_, ?_, ?_⟩
  · simp [trivLB]
  · intro i
    exact (res _).map_one
  · intro i j k
    refine (congrArg₂ (· * ·) (res _).map_one (res _).map_one).trans ?_
    exact (_root_.one_mul _).trans (res _).map_one.symm

theorem linComb_triv_g {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (j j' : (LB.LinComb (trivLB X) φ ε).ι) : (LB.LinComb (trivLB X) φ ε).g j j' = 1 := by
  have hg : ∀ a b, (trivLB X).g a b = 1 := fun _ _ => rfl
  apply Finset.prod_eq_one
  intro k _
  rw [hg, map_one]
  first
    | exact (congrArg (· ^ ε k) (map_one _)).trans (one_zpow _)
    | (erw [map_one, one_zpow])

theorem powOver_triv_g {S : Scheme.{0}} (A : Over S) (U : S.Opens) (N : ℕ)
    (j j' : (powOver A (trivLB A.left) U N).ι) : (powOver A (trivLB A.left) U N).g j j' = 1 :=
  linComb_triv_g _ _ j j'

theorem surj_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (D : X.Opens) (hD : D = ⊤)
    (e : D ≤ f ⁻¹ᵁ ⊤) : Function.Surjective (f.appLE ⊤ D e).hom := by
  subst hD
  have h1 : IsIso (homOfLE e) := ⟨⟨homOfLE le_top, rfl, rfl⟩⟩
  have h2 : IsIso (f.appLE ⊤ ⊤ e) := by
    first
      | (rw [Scheme.Hom.appLE]; infer_instance)
      | (show IsIso (f.app ⊤ ≫ X.presheaf.map (homOfLE e).op); infer_instance)
  first
    | exact (ConcreteCategory.bijective_of_isIso (f.appLE ⊤ ⊤ e)).2
    | exact (asIso (f.appLE ⊤ ⊤ e)).commRingCatIsoToRingEquiv.surjective

variable (S : Scheme.{0})

def zeroPolAV : PolAV S where
  A := 𝟙_ (Over S)
  isAb :=
    { comm := inferInstance
      smooth := by show Smooth (𝟙 S); infer_instance
      proper := by show IsProper (𝟙 S); infer_instance
      geomConnected := by show GeometricallyConnected (𝟙 S); infer_instance }
  g := 0
  smoothDim := by show SmoothOfRelativeDimension 0 (𝟙 S); infer_instance
  L := trivLB _
  isLB := trivLB_isLB _
  rigid := ⟨⟨fun _ => 1⟩, by
    intro i j; rw [linComb_triv_g, _root_.one_mul]; dsimp only; repeat erw [map_one]
    all_goals rfl⟩
  sym := fun _ => ⟨⊤, trivial, ⟨fun _ => 1⟩, by
    intro i j; rw [linComb_triv_g, _root_.one_mul]; dsimp only; repeat erw [map_one]
    all_goals rfl⟩
  ample := by
    intro U hU
    haveI : IsIso (𝟙_ (Over S)).hom := by show IsIso (𝟙 S); infer_instance
    let Y := ((𝟙_ (Over S)).hom ⁻¹ᵁ U).toScheme
    let s0 : LB.Sec (powOver (𝟙_ (Over S)) (trivLB _) U 1) :=
      ⟨fun _ => 1, by
        intro i j; rw [powOver_triv_g, Units.val_one, _root_.one_mul]; repeat erw [map_one]
        all_goals rfl⟩
    have hD : nonzeroLocus s0 = ⊤ := by
      apply top_unique
      intro x _
      simp only [nonzeroLocus, s0, Scheme.basicOpen_one]
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => PUnit.unit, by
        simp only [powOver, LB.LinComb, LB.wchart, trivLB]
        exact Set.mem_iInter.2 fun _ => trivial⟩
    refine ⟨1, le_rfl, 0, fun _ => s0, by simp only [iSup_const]; exact hD,
      fun _ => ⟨?_, fun _ => 1, ?_, ?_⟩⟩
    · rw [hD]
      have : IsAffine Y := hU
      exact isAffineOpen_top Y
    · intro j k
      erw [map_one]; (try erw [map_one]); (try erw [map_one]); exact (_root_.mul_one _).symm
    · intro p
      obtain ⟨a, rfl⟩ := surj_appLE ((𝟙_ (Over S)).hom ∣_ U) _ hD le_top p
      exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
  ktriv := fun _ _ _ x _ => toUnit_unique x _

end ReciprocityTheory.ChartRestriction.G.Out.Inh
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def HomExtDvrSt : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (G G' : Over (Spec (CommRingCat.of T))) [GrpObj G] [GrpObj G'],
    IsSemiAbelian G → IsSemiAbelian G' →
    ∀ φ : genFibre T G ⟶ genFibre T G', IsMonHom φ →
      ∃! ψ : G ⟶ G', IsMonHom ψ ∧ (Over.pullback (specMap T (FractionRing T))).map ψ = φ

structure Laws7 : Prop where
  homExtDvr : HomExtDvrSt

end ReciprocityTheory.ChartRestriction.G.Out
end
end
