module

public import Development.EtaleCohomology.KummerTheory.InjSlice
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Comma.LocallySmall
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

abbrev SlShv (Λ : Type) [CommRing Λ] (S : Scheme.{0}) : Type 2 :=
  Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} Λ))

instance (Λ : Type) [CommRing Λ] (S : Scheme.{0}) : HasSheafify (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} Λ)) := by
  have : EssentiallySmall.{1} (Over S) := inferInstance
  infer_instance

instance (Λ : Type) [CommRing Λ] (S : Scheme.{0}) : IsGrothendieckAbelian.{1} (SlShv Λ S) := by
  have : EssentiallySmall.{1} (Over S) := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ (ModuleCat.{1} (ULift.{1} Λ))

def rst {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) : pullback p V.hom ⟶ pullback p U.hom :=
  pullback.map _ _ _ _ (𝟙 X) g.left (𝟙 S) (by simp) (by simp)

def Nbhd {S : Scheme.{0}} {V U : Over S} (g : V ⟶ U) (u : U.left) : Prop := Etale g.left ∧ ∃ v : V.left, g.left v = u

section Cone
variable {Λ : Type} [CommRing Λ] {I : Cx Λ} {X S : Scheme.{0}}

abbrev FinalTheorems (J : Cx Λ) (r : ℕ → ℕ) (M : ℕ) (n : ℤ) (U : Scheme.{0}) : Type 1 :=
  ∀ a : Fin (M + 1), Fin (r a) → Sec (J.X (n - ((a : ℕ) : ℤ))) U

abbrev Cone (J K : Cx Λ) (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ) (j : ℤ) (U : Over S) : Type 1 :=
  FinalTheorems J r M (j + 1) U.left × Sec (K.X j) (pullback p U.hom)

variable {J K : Cx Λ} {r : ℕ → ℕ} {M : ℕ}

def dS (n m : ℤ) {U : Scheme.{0}} (b : FinalTheorems J r M n U) : FinalTheorems J r M m U :=
  fun a s => ((a : ℕ) : ℤ).negOnePow • Sec.map (J.d (n - ((a : ℕ) : ℤ)) (m - ((a : ℕ) : ℤ))) (b a s)

def cres {p : X ⟶ S} {j : ℤ} {V U : Over S} (g : V ⟶ U) (x : Cone J K p r M j U) : Cone J K p r M j V :=
  (fun a s => Sec.res g.left (x.1 a s), Sec.res (rst p g) x.2)

variable (μ : Pair I J K) (p : X ⟶ S) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X)

def Phi (n w : ℤ) (h : n = w) (U : Over S) (b : FinalTheorems J r M n U.left) : Sec (K.X w) (pullback p U.hom) :=
  ∑ a : Fin (M + 1), ∑ s : Fin (r a), μ.mul _ ((a : ℕ) : ℤ) (n - ((a : ℕ) : ℤ)) w (by omega)
    (Sec.res (pullback.fst p U.hom) (γ a s)) (Sec.res (pullback.snd p U.hom) (b a s))

def cD (j j' : ℤ) (h : j + 1 = j') (U : Over S) (x : Cone J K p r M j U) : Cone J K p r M j' U :=
  (dS (j + 1) (j' + 1) x.1, Phi μ p γ (j + 1) j' h U x.1 - Sec.map (K.d j j') x.2)

variable (M)

def ConeEx (N : ℕ) (j : ℤ) (U : Over S) : Prop := ∀ x : Cone J K p r M j U, cD μ p γ j (j + 1) rfl U x = 0 →
  ∃ y : Cone J K p r M (j - 1) U, cD μ p γ (j - 1) j (by omega) U y = N • x

def ConeLoc (N : ℕ) (j : ℤ) : Prop := ∀ (U : Over S) (x : Cone J K p r M j U), cD μ p γ j (j + 1) rfl U x = 0 →
  ∀ u : U.left, ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧
    ∃ y : Cone J K p r M (j - 1) V, cD μ p γ (j - 1) j (by omega) V y = N • cres g x

end Cone

def Closed {Λ : Type} [CommRing Λ] {I : Cx Λ} {X : Scheme.{0}} {r : ℕ → ℕ} (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X) : Prop :=
  ∀ (a : ℕ) (s : Fin (r a)), Sec.map (I.d a (a + 1)) (γ a s) = 0

def InjPos {Λ : Type} [CommRing Λ] (J : Cx Λ) : Prop := (∀ n, Injective (J.X n)) ∧ ∀ n : ℤ, n < 0 → IsZero (J.X n)

def mu (q : ℕ) (i : ℤ) : Pair (res _ (tw q i)) (res _ (tw q 0)) (res _ (tw q i)) :=
  cast (congrArg (fun w => Pair (res _ (tw q i)) (res _ (tw q 0)) (res _ (tw q w))) (add_zero i)) (twPair q i 0)

section Cls
variable (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ) (n : ℤ)

def KerLoc : Prop := ∀ (U : Over S) (u : U.left) y, lh q p U.hom i r c M n y = 0 →
  ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧ ∀ a s, N • pull _ (sch.map g.left) _ _ (y a s) = 0

def CokLoc : Prop := ∀ (U : Over S) (u : U.left) (x : Ht q (sch.obj (pullback p U.hom)) n i),
  ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧ ∃ y, lh q p V.hom i r c M n y = N • pull _ (sch.map (rst p g)) _ _ x

end Cls

def ClsMore : Prop := ∀ (Λ : Type) [CommRing Λ] (I : Cx Λ) (X : Scheme.{0}) (n : ℤ),
  IsCls (0 : CohomologyClass ((chains Λ).obj (sch.obj X)) I n) 0 ∧
  (∀ (N : ℕ) x (a : Sec (I.X n) X), IsCls x a → IsCls (N • x) (N • a)) ∧
  (∀ (ι : Type) [Fintype ι] (x : ι → CohomologyClass ((chains Λ).obj (sch.obj X)) I n) (a : ι → Sec (I.X n) X),
    (∀ t, IsCls (x t) (a t)) → IsCls (∑ t, x t) (∑ t, a t)) ∧
  ∀ (m : ℤ), m + 1 = n → ∀ x x' (a a' : Sec (I.X n) X), IsCls x a → IsCls x' a' →
    (x = x' ↔ ∃ b : Sec (I.X m) X, Sec.map (I.d m n) b = a - a')

def LhSec : Prop := ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
  (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X), (∀ a s, IsCls (c a s) (γ a s)) →
  ∀ (M : ℕ) (n : ℤ) (U : Over S) y (b : FinalTheorems (res _ (tw q 0)) r M n U.left), (∀ a s, IsCls (y a s) (b a s)) →
  IsCls (lh q p U.hom i r c M n y) (Phi (mu q i) p γ n n rfl U b)

def LhNat : Prop := DivisorNaturality → ∀ (q : ℕ) [NeZero q] {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ)
  (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M : ℕ) (n : ℤ) {V U : Over S} (g : V ⟶ U) y,
  pull _ (sch.map (rst p g)) _ _ (lh q p U.hom i r c M n y) =
    lh q p V.hom i r c M n (fun a s => pull _ (sch.map g.left) _ _ (y a s))

def ConeAlg : Prop := ∀ (Λ : Type) [CommRing Λ] {I J K : Cx Λ} (μ : Pair I J K) {X S : Scheme.{0}} (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ)
  (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X), Closed γ → ∀ (j j' : ℤ) (h : j + 1 = j') (U : Over S),
  IsLinearMap (ULift.{1} Λ) (cD (M := M) μ p γ j j' h U) ∧
  (∀ (j'' : ℤ) (h' : j' + 1 = j'') (x : Cone J K p r M j U), cD μ p γ j' j'' h' U (cD μ p γ j j' h U x) = 0) ∧
  ∀ (V : Over S) (g : V ⟶ U), IsLinearMap (ULift.{1} Λ) (cres g : Cone J K p r M j U → _) ∧
    (∀ x : Cone J K p r M j U, cres g (cD μ p γ j j' h U x) = cD μ p γ j j' h V (cres g x)) ∧
    ∀ (W : Over S) (g' : W ⟶ V) (x : Cone J K p r M j U), cres (g' ≫ g) x = cres g' (cres g x)

def LocKer : Prop := DivisorNaturality → B1 → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R), IsUnit (q : R) →
  ∀ (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ) (n : ℤ),
  (∀ (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsoUpTo N (lh q p (Spec.map s) i r c M n)) → KerLoc q p i r c M N n

def LocCok : Prop := A2 → DivisorNaturality → B1 → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R)
  [QuasiCompact p] [IsSeparated p], IsUnit (q : R) →
  ∀ (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ) (n : ℤ),
  (∀ (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsoUpTo N (lh q p (Spec.map s) i r c M n)) → CokLoc q p i r c M N n

def LocCone : Prop := ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
  (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X), (∀ a s, IsCls (c a s) (γ a s)) → ∀ (M N : ℕ) (j : ℤ),
  KerLoc q p i r c M N (j + 1) → CokLoc q p i r c M N j → ConeLoc M (mu q i) p γ (N ^ 2) j

def ExIso : Prop := ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
  (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X), (∀ a s, IsCls (c a s) (γ a s)) → ∀ (M N : ℕ) (j : ℤ) (U : Over S),
  ConeEx M (mu q i) p γ N j U → ConeEx M (mu q i) p γ N (j + 1) U → IsoUpTo N (lh q p U.hom i r c M (j + 1))

def Corep : Prop := ∀ (Λ : Type) [CommRing Λ] (S : Scheme.{0}) (U : Over S), ∃ (P : SlShv Λ S) (z : P.obj.obj (op U)),
  ∀ F : SlShv Λ S, Function.Bijective fun φ : P ⟶ F => (φ.hom.app (op U)).hom z

def CxLoc {Λ : Type} [CommRing Λ] {S : Scheme.{0}} (C : CochainComplex (SlShv Λ S) ℤ) (N : ℕ) (j : ℤ) : Prop :=
  ∀ (U : Over S) (x : (C.X j).obj.obj (op U)), ((C.d j (j + 1)).hom.app (op U)).hom x = 0 → ∀ u : U.left,
    ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧ ∃ y : (C.X (j - 1)).obj.obj (op V),
      ((C.d (j - 1) j).hom.app (op V)).hom y = N • ((C.X j).obj.map g.op).hom x

def HomKill : Prop := ∀ (Λ : Type) [CommRing Λ] (S : Scheme.{0}) (C : CochainComplex (SlShv Λ S) ℤ) (N : ℕ) (j : ℤ),
  CxLoc C N j → N • 𝟙 (C.homology j) = 0

def GhostSec : Prop := ∀ (Λ : Type) [CommRing Λ] (S : Scheme.{0}) (C : CochainComplex (SlShv Λ S) ℤ), (∀ j, Injective (C.X j)) →
  (∀ j : ℤ, j < -1 → IsZero (C.X j)) → ∀ N m : ℕ, (∀ j : ℤ, j < m → CxLoc C N j) → ∀ j : ℤ, j < m →
  ∀ (U : Over S) (x : (C.X j).obj.obj (op U)), ((C.d j (j + 1)).hom.app (op U)).hom x = 0 →
    ∃ y : (C.X (j - 1)).obj.obj (op U), ((C.d (j - 1) j).hom.app (op U)).hom y = N ^ (m + 1) • x

def ConeObj : Prop := ∀ (Λ : Type) [CommRing Λ] (J K : Cx Λ), (∀ n, Injective (J.X n)) → (∀ n, Injective (K.X n)) →
  ∀ {X S : Scheme.{0}} (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ) (j : ℤ), ∃ T : SlShv Λ S, Injective T ∧
    ∃ e : ∀ U : Over S, T.obj.obj (op U) ≃ₗ[ULift.{1} Λ] Cone J K p r M j U,
      ∀ (V U : Over S) (g : V ⟶ U) x, e V ((T.obj.map g.op).hom x) = cres g (e U x)

def ConeCx : Prop := ∀ (Λ : Type) [CommRing Λ] {I J K : Cx Λ} (μ : Pair I J K), InjPos J → InjPos K →
  ∀ {X S : Scheme.{0}} (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X), Closed γ →
  ∃ C : CochainComplex (SlShv Λ S) ℤ, (∀ j, Injective (C.X j)) ∧ (∀ j : ℤ, j < -1 → IsZero (C.X j)) ∧
    ∃ e : ∀ (j : ℤ) (U : Over S), (C.X j).obj.obj (op U) ≃+ Cone J K p r M j U,
      (∀ (j : ℤ) (V U : Over S) (g : V ⟶ U) x, e j V (((C.X j).obj.map g.op).hom x) = cres g (e j U x)) ∧
      ∀ (j j' : ℤ) (h : j + 1 = j') (U : Over S) x, e j' U (((C.d j j').hom.app (op U)).hom x) = cD μ p γ j j' h U (e j U x)

def Glob : Prop := ∀ (Λ : Type) [CommRing Λ] {I J K : Cx Λ} (μ : Pair I J K), InjPos J → InjPos K →
  ∀ {X S : Scheme.{0}} (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X), Closed γ →
  ∀ N m : ℕ, (∀ j : ℤ, j < m → ConeLoc M μ p γ N j) → ∀ j : ℤ, j < m → ∀ U : Over S, ConeEx M μ p γ (N ^ (m + 1)) j U

theorem injPos_res (Λ : Type) [CommRing Λ] (F : Shv Λ) : InjPos (res Λ F) :=
  ⟨fun n => by unfold res; infer_instance,
   fun n hn => (injectiveResolution F).cochainComplex.isZero_of_isStrictlyGE 0 n hn⟩

theorem goal_of (hD : Dict) (h1 : LocKer) (h2 : LocCok) (h3 : LocCone) (h4 : Glob) (h5 : ExIso) : LH := by
  intro a2 a6 b1
  refine ⟨fun M => 2 * (M + 1), ?_⟩
  intro q _ X R p _ _ hq i r c M N hS Y pY n hn
  choose γ hγ using fun (a : ℕ) (s : Fin (r a)) => (hD _ (res _ (tw q i)) X a).2.1 (c a s)
  have hc : Closed γ := fun a s => ((hD _ (res _ (tw q i)) X a).2.2.1 _ _ (hγ a s)).1
  have hl : ∀ j : ℤ, j < M → ConeLoc M (mu q i) p γ (N ^ 2) j := fun j hj =>
    h3 q p i r c γ hγ M N j (h1 a6 b1 q p hq i r c M N _ fun A s hA => hS A s hA _ (by omega))
      (h2 a2 a6 b1 q p hq i r c M N _ fun A s hA => hS A s hA _ (by omega))
  have hg := h4 _ (mu q i) (injPos_res _ _) (injPos_res _ _) p r M γ hc (N ^ 2) M hl
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have := h5 q p i r c γ hγ M _ j (Over.mk pY) (hg j (by omega) _) (hg (j + 1) hn _)
  rw [← pow_mul] at this
  exact this

end LateralTheory.KummerTheory.LHCut

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def ForgetInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) [Injective F] (S : Scheme.{0}),
  ∃ h : Presheaf.IsSheaf (Scheme.etaleTopology.over S) ((Over.forget S).op ⋙ F.obj),
    Injective (⟨_, h⟩ : Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R)))

theorem pushPullback_inj {R : Type} [CommRing R] {X S : Scheme.{0}} (p : X ⟶ S)
    (G : Sheaf (Scheme.etaleTopology.over X) (ModuleCat.{1} (ULift.{1} R))) [Injective G] :
    Injective (((Over.pullback p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over S) (Scheme.etaleTopology.over X)).obj G) := by
  have adj := (Over.mapPullbackAdj p).sheafPushforwardContinuous (E := ModuleCat.{1} (ULift.{1} R))
    (Scheme.etaleTopology.over X) (Scheme.etaleTopology.over S)
  have : ((Over.map p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over X) (Scheme.etaleTopology.over S)).PreservesMonomorphisms := inferInstance
  exact Injective.injective_of_adjoint adj G

theorem InjSlice_of (hF : ForgetInj) : InjSlice := by
  intro R _ F _ X S p
  obtain ⟨hX, iX⟩ := hF R F X
  refine ⟨?_, hF R F S⟩
  let G : Sheaf (Scheme.etaleTopology.over X) (ModuleCat.{1} (ULift.{1} R)) := ⟨_, hX⟩
  exact ⟨(((Over.pullback p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over S) (Scheme.etaleTopology.over X)).obj G).2, pushPullback_inj p G⟩

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.KummerTheory

theorem stalk_neg (h9 : A9) (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R)
    (A : CommRingCat.{0}) (s : R ⟶ A) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ)
    (n : ℤ) (hn : n < 0) : IsoUpTo N (lh q p (Spec.map s) i r c M n) := by
  have : Subsingleton (Ht q (sch.obj (pullback p (Spec.map s))) n i) := (h9 (ZMod q) (tw q i)).1 _ n hn
  haveI : ∀ a : Fin (M + 1), Subsingleton (Ht q (sch.obj (Spec A)) (n - ((a : ℕ) : ℤ)) 0) :=
    fun a => (h9 (ZMod q) (tw q 0)).1 _ _ (by omega)
  refine ⟨fun y _ => ?_, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  funext a t
  exact Subsingleton.elim _ _

def ExtOne : Prop := DivisorNaturality → DivisorRingCompatibility → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R A : CommRingCat.{0}} (p : X ⟶ Spec R)
  (s : R ⟶ A), IsUnit (q : A) → ∀ (a i : ℤ) (x : Ht q (sch.obj X) a i) (t : ZMod q),
    ext q p (Spec.map s) a a i x ((t • one q (sch.obj (Spec A))).cast (by ring) rfl) =
      t • pull _ (sch.map (pullback.fst p (Spec.map s))) _ _ x

def StalkTop : Prop := DivisorNaturality → DivisorRingCompatibility → A9 → B2 → H0 → ExtOne → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}}
  {R : CommRingCat.{0}} (p : X ⟶ Spec R) (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsUnit (q : R) → ∀ (i : ℤ) (r : ℕ → ℕ)
  (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ), Eqv _ (sch.map (pullback.fst p (Spec.map s))) (tw q i) →
  (∀ a ≤ M, IsoUpTo N (comb q (c a))) → ∀ n : ℤ, 0 ≤ n → n ≤ M → IsoUpTo N (lh q p (Spec.map s) i r c M n)

theorem inv_sch (q : ℕ) {X : Scheme.{0}} (hq : IsUnit (q : Γ(X, ⊤))) : Inv q (sch.obj X) := by
  intro U ⟨g⟩
  have g' : U ⟶ X := g
  simpa using hq.map g'.appTop.hom

theorem unit_spec (q : ℕ) {A : CommRingCat.{0}} (hq : IsUnit (q : A)) : IsUnit (q : Γ(Spec A, ⊤)) := by
  simpa using hq.map (Scheme.ΓSpecIso A).inv.hom

theorem pull_zsmul {E E' : Spc} (f : E ⟶ E') (q : ℕ) [NeZero q] {n i : ℤ} (t : ZMod q) (x : Ht q E' n i) :
    pull _ f _ _ (t • x) = t • pull _ f _ _ x := by
  rw [← ZMod.natCast_zmod_val t, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem cast_cast' (q : ℕ) {E : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'')
    (x : Ht q E n i) : (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

theorem pull_cast (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (x : Ht q E' n i) : pull _ f _ _ (x.cast h1 h2) = Ht.cast h1 h2 (pull _ f _ _ x : Ht q E n i) := by
  subst h1 h2; rfl

theorem cast_smul' (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (t : ZMod q) (x : Ht q E n i) :
    (t • x).cast h1 h2 = t • x.cast h1 h2 := by
  subst h1 h2; rfl

theorem cup_cast_r (q : ℕ) {E : Spc} {n m i j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (a : Ht q E n i)
    (y : Ht q E m j) : cup q a (y.cast h1 h2) = (cup q a y).cast (by rw [h1]) (by rw [h2]) := by
  subst h1 h2; rfl

theorem cup_smul_r (q : ℕ) [NeZero q] {E : Spc} {n m i j : ℤ} (t : ZMod q) (a : Ht q E n i) (y : Ht q E m j) :
    cup q a (t • y) = t • cup q a y := by
  rw [← ZMod.natCast_zmod_val t, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem unit_map (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) (hq : IsUnit (q : Γ(X, ⊤))) : IsUnit (q : Γ(Y, ⊤)) := by
  simpa using hq.map f.appTop.hom

theorem extOne_pf : ExtOne := by
  intro h6n h6r q _ X R A p s hq a i x t
  have hI := inv_sch q (unit_spec q hq)
  have hP := inv_sch q (unit_map q (pullback.snd p (Spec.map s)) (unit_spec q hq))
  unfold ext
  rw [pull_cast, pull_zsmul, (h6n q).2.1 _ hI, cup_cast_r, cup_smul_r, (h6r q _).2.2, (h6r q _).1 hP]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, cast_smul', cast_cast']
  rfl

theorem cast_zero' (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    (0 : Ht q E n i).cast h1 h2 = 0 := by
  subst h1 h2; rfl

theorem cast_nsmul' (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (N : ℕ) (x : Ht q E n i) :
    (N • x).cast h1 h2 = N • x.cast h1 h2 := by
  subst h1 h2; rfl

theorem ext_zero (q : ℕ) [NeZero q] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (x : Ht q (sch.obj X) a i) :
    ext q pX pY a n i x 0 = 0 := by
  unfold ext; rw [map_zero, map_zero, cast_zero']

theorem stalkTop_pf : StalkTop := by
  intro h6n h6r h9 hb2 h0 hE q _ X R p A s hA hq i r c M N he hc n hn0 hnM
  lift n to ℕ using hn0
  have hnM' : n ≤ M := by exact_mod_cast hnM
  have hqA : IsUnit (q : A) := by simpa using hq.map s.hom
  let a : Fin (M + 1) := ⟨n, by omega⟩
  have hsub : ∀ b : Fin (M + 1), b ≠ a → Subsingleton (Ht q (sch.obj (Spec A)) ((n : ℤ) - ((b : ℕ) : ℤ)) 0) := by
    intro b hb
    have hb' : (b : ℕ) ≠ n := fun h => hb (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hb' with h | h
    · exact hb2 (ZMod q) A hA (tw q 0) _ (by omega)
    · exact (h9 (ZMod q) (tw q 0)).1 _ _ (by omega)
  have hH := h0 h9 q A hA hqA
  have hex : ∀ z : Ht q (sch.obj (Spec A)) ((n : ℤ) - (n : ℤ)) 0, ∃ t : ZMod q,
      z = (t • one q (sch.obj (Spec A))).cast (by ring) rfl := by
    intro z
    obtain ⟨t, ht⟩ := hH.2 (z.cast (by ring) rfl)
    refine ⟨t, ?_⟩
    rw [show t • one q (sch.obj (Spec A)) = _ from ht, cast_cast']; rfl
  have hform : ∀ (y : ∀ b : Fin (M + 1), Fin (r b) → Ht q (sch.obj (Spec A)) ((n : ℤ) - ((b : ℕ) : ℤ)) 0)
      (t : Fin (r n) → ZMod q), (∀ u, y a u = (t u • one q (sch.obj (Spec A))).cast (by ring) rfl) →
      lh q p (Spec.map s) i r c M n y = pull _ (sch.map (pullback.fst p (Spec.map s))) _ _ (comb q (c n) t) := by
    intro y t hy
    unfold lh comb
    rw [Fintype.sum_eq_single a]
    · rw [map_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hy u, pull_zsmul]
      exact hE h6n h6r q p s hqA n i (c n u) (t u)
    · intro b hb
      haveI := hsub b hb
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [Subsingleton.elim (y b u) 0, ext_zero]
  have hbij := he (n : ℤ)
  refine ⟨fun y hy0 => ?_, fun b => ?_⟩
  · choose t ht using fun u => hex (y a u)
    rw [hform y t ht] at hy0
    have hc0 : comb q (c n) t = 0 := hbij.1 (by rw [hy0, map_zero])
    have hNt := (hc n hnM').1 t hc0
    funext b u
    by_cases hb : b = a
    · subst hb
      show N • y a u = 0
      rw [ht u]
      have e1 : N • t u = 0 := by simpa using congrFun hNt u
      rw [← cast_nsmul', ← smul_assoc, e1, zero_smul, cast_zero']
    · haveI := hsub b hb
      exact Subsingleton.elim _ _
  · obtain ⟨w, rfl⟩ := hbij.2 b
    obtain ⟨t, ht⟩ := (hc n hnM').2 w
    refine ⟨Pi.single a (fun u => (t u • one q (sch.obj (Spec A))).cast (by ring) rfl), ?_⟩
    rw [hform _ t (fun u => by rw [Pi.single_eq_same]), ht, map_nsmul]

theorem Stalk_of (h0 : H0) : Stalk := by
  intro h6n h6r h9 hb2 q _ X R p A s hA hq i r c M N he hc n hn
  by_cases hneg : n < 0
  · exact stalk_neg h9 q p A s i r c M N n hneg
  · exact stalkTop_pf h6n h6r h9 hb2 h0 extOne_pf q p A s hA hq i r c M N he hc n (by omega) hn
end KummerTheory
end LateralTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def Cls0 : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
  (α β : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0),
  ev α.1 0 0 (by simp) X (𝟙 X) = ev β.1 0 0 (by simp) X (𝟙 X) → CohomologyClass.mk α = CohomologyClass.mk β

def OneEx : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
  ∃ c : Ht q (sp A) 0 0, ∃ α : Cocycle ((chains (ZMod q)).obj (sp A)) (res (ZMod q) (tw q 0)) 0,
    CohomologyClass.mk α = c ∧
    ∀ (U : Scheme.{0}) (x : Sx (sp A) 0 U) (ζ : Prim q Γ(U, ⊤)),
      ev α.1 0 0 (by simp) U x = resGen 0 ζ

theorem etale_kummer_degree_zero_cohomology_of_twist_section_class_and_root_ex (hT : TwSec) (hC : Cls0) (hO : OneEx) : H0 := by
  intro h9 q _ A _ hA hq
  obtain ⟨hne, hb⟩ := hT q A hA hq
  obtain ⟨ζ⟩ := hne
  have hb0 := hb 0 ζ
  obtain ⟨_, e, -, he⟩ := h9 (ZMod q) (tw q 0)
  have hone : one q (sp A) = e (Spec (CommRingCat.of A)) (twGen 0 ζ) := by
    obtain ⟨α, hα, hv⟩ := pick_spec (hO q A hA hq)
    have hα' : CohomologyClass.mk α = one q (sp A) := hα
    obtain ⟨β, hβ, hβv⟩ := he (Spec (CommRingCat.of A)) (twGen 0 ζ)
    rw [← hα', ← hβ]
    exact hC _ _ _ α β ((hv _ (𝟙 _) ζ).trans hβv.symm)
  have hlin : ∀ t : ZMod q, t • one q (sp A) =
      e (Spec (CommRingCat.of A)) ((ULift.up t : ULift.{1} (ZMod q)) • twGen 0 ζ) := by
    intro t
    rw [hone]
    have h1 : t = ((t.val : ℕ) : ZMod q) := (ZMod.natCast_zmod_val t).symm
    have h2 : (ULift.up t : ULift.{1} (ZMod q)) = ((t.val : ℕ) : ULift.{1} (ZMod q)) := by
      apply ULift.ext
      rw [ULift.down_natCast]; exact h1
    rw [h2, Nat.cast_smul_eq_nsmul, map_nsmul]
    conv_lhs => rw [h1]
    rw [Nat.cast_smul_eq_nsmul]
  have hfun : (fun t : ZMod q => t • one q (sp A)) =
      (e (Spec (CommRingCat.of A))) ∘ (fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • twGen 0 ζ) := funext hlin
  rw [hfun]
  exact (e _).bijective.comp hb0

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def PlaceEx : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K],
  ∃ (T : ValuationSubring K) (σ : k →+* T), (∀ x, (σ x : K) = algebraMap k K x) ∧
    Function.Surjective ((IsLocalRing.residue T).comp σ)

def ValAIC : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] (T : ValuationSubring K), AIC T ∧ HenselianLocalRing T

theorem Place_of (h1 : PlaceEx) (h2 : ValAIC) : Place := by
  intro k K _ _ _ _ _
  obtain ⟨T, σ, hσ, hs⟩ := h1 k K
  obtain ⟨hA, hH⟩ := h2 K T
  have hb : Function.Bijective ((IsLocalRing.residue T).comp σ) := ⟨RingHom.injective _, hs⟩
  refine ⟨T, σ, hσ, hb, hA, hH, ?_⟩
  have : IsAlgClosed (IsLocalRing.ResidueField T) := IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective _ hb)
  infer_instance

end LateralTheory.KummerTheory
end
end
