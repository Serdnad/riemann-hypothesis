module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle008
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
theorem _root_.GlobalTheory.T.abelianVariety_lineBundle_sections_finite : (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M)) → (∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)), (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧ ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0 := by
  first | exact @GlobalTheory.AbLaw.sections_finite_of_perf | exact GlobalTheory.AbLaw.sections_finite_of_perf | (intros; apply GlobalTheory.AbLaw.sections_finite_of_perf <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.formallyUnramified_mul_invertible_integer : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ), IsUnit (n : Γ(S, ⊤)) → FormallyUnramified (mulA G n).left := by
  first | exact @GlobalTheory.formallyUnramified_mulA | exact GlobalTheory.formallyUnramified_mulA | (intros; apply GlobalTheory.formallyUnramified_mulA <;> assumption)
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull unit_ext exists_chart gm_cocycle gm_self)

namespace GlobalTheory.GtCubeCompare

section General

variable {X Y Z : Scheme.{0}}

variable {A B : LB X}

def gw (w : LB.Iso A B) (f : Y ⟶ X) (y : Y) (p : B.ι) (q : A.ι) : (Y.presheaf.stalk y)ˣ :=
  gm f y (B.U p ⊓ A.U q) (w.s (p, q))

theorem gm_linCombIso (w : LB.Iso A B) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (p : K → B.ι) (q : K → A.ι) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ LB.wchart B φ p ⊓ LB.wchart A φ q) :
    gm r z (LB.wchart B φ p ⊓ LB.wchart A φ q) ((LB.linCombIso w φ ε).s (p, q)) =
      ∏ a, gw w (r ≫ φ a) z (p a) (q a) ^ ε a := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have hm : (φ a) (r z) ∈ B.U (p a) ⊓ A.U (q a) :=
    ⟨LB.wchart_le B φ p a hz.1, LB.wchart_le A φ q a hz.2⟩
  exact (gm_res r z _ hz _).trans (gm_pull r (φ a) z (B.U (p a) ⊓ A.U (q a)) hm _)

def PM (w : LB.Iso A B) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb A φ ε)) (b : LB.Gen (LB.LinComb B φ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → B.ι) (q : K → A.ι),
    r z ∈ LB.wchart B φ p → r z ∈ LB.wchart A φ q →
    gm r z (LB.wchart B φ p) (b.s p) =
      (∏ k, gw w (r ≫ φ k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart A φ q) (a.s q)

theorem maps_iff_pm (w : LB.Iso A B) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb A φ ε)) (b : LB.Gen (LB.LinComb B φ ε)) :
    LB.Gen.Maps (LB.linCombIso w φ ε) a b ↔ PM w φ ε a b := by
  constructor
  · intro H Z r z p q hp hq
    have hm : r z ∈ LB.wchart B φ p ⊓ LB.wchart A φ q := ⟨hp, hq⟩
    have := congrArg (gm r z (LB.wchart B φ p ⊓ LB.wchart A φ q)) (H (p, q))
    rw [← gm_linCombIso w φ ε p q r z hm]
    exact (gm_res r z _ hm _).symm.trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res r z _ hm _))))
  · rintro H ⟨p, q⟩
    apply unit_ext
    intro x hx
    have := H _ (𝟙 Y) x p q hx.1 hx.2
    rw [← gm_linCombIso w φ ε p q (𝟙 Y) x hx] at this
    exact (gm_res _ x _ hx _).trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

variable {w : LB.Iso A B} {K K' : Type} [Fintype K] [Fintype K']

end General

section Group

variable {S S' : Scheme.{0}}

end Group

end GlobalTheory.GtCubeCompare

end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace MulLaw

theorem natCard_eq_of_equiv_pi_field {R : Type} [Field R] {U V : Type} [AddCommGroup U]
    [Module R U] [AddCommGroup V] [Module R V] {X : Type} (e : U ≃ₗ[R] (X → V)) {m : ℕ}
    (hm : 0 < m) (hU : Module.finrank R U = m) (hV : Module.finrank R V = 1) :
    Nat.card X = m := by
  classical
  haveI : Module.Finite R U := Module.finite_of_finrank_pos (hU ▸ hm)
  haveI : Module.Finite R V := Module.finite_of_finrank_pos (hV ▸ Nat.one_pos)
  have e₁ : V ≃ₗ[R] R := LinearEquiv.ofFinrankEq V R (by rw [hV, Module.finrank_self])
  have e₂ : U ≃ₗ[R] (X → R) := e.trans (LinearEquiv.piCongrRight fun _ => e₁)
  haveI : Module.Finite R (X → R) := Module.Finite.equiv e₂
  haveI : Finite X := (Pi.linearIndependent_single_one X R).finite
  haveI := Fintype.ofFinite X
  rw [← hU, e₂.finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem natCard_eq_of_equiv_pi {R : Type} [CommRing R] (hR : IsField R) {U V : Type}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] {X : Type}
    (e : U ≃ₗ[R] (X → V)) {m : ℕ}
    (hm : 0 < m) (hU : Module.finrank R U = m) (hV : Module.finrank R V = 1) :
    Nat.card X = m := by
  letI := hR.toField
  exact natCard_eq_of_equiv_pi_field e hm hU hV

noncomputable def basePointsEquiv {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'}
    [GrpObj A] [GrpObj A'] {g : A'.left ⟶ A.left} (hg : IsPullback g A'.hom A.hom f)
    (hmul : ∀ (T : Over S') (x y : T ⟶ A'),
      toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) (T : Over S') :
    (T ⟶ A') ≃* (Over.mk (T.hom ≫ f) ⟶ A) where
  toFun x := toBase hg.w x
  invFun y := Over.homMk (hg.lift y.left T.hom (Over.w y)) (hg.lift_snd _ _ _)
  left_inv x := by
    apply Over.OverMorphism.ext
    apply hg.hom_ext
    · exact hg.lift_fst _ _ _
    · exact (hg.lift_snd _ _ _).trans (Over.w x).symm
  right_inv y := by
    apply Over.OverMorphism.ext
    exact hg.lift_fst _ _ _
  map_mul' x y := hmul T x y

end MulLaw

theorem mulN_of_decomposition :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n j : ℕ), (n : K) ≠ 0 → 1 ≤ j → Nonempty (SecM P.A P.L ((n ^ 2 * j : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K))) ≃ₗ[Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)] ({x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ n = 1} → SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K)))))) → GlobalSectionsRankAlgClosed → PolBaseChangeSt → MulNSt := by
  intro hQ hRel hH hBC S _ P n hn
  obtain ⟨h1, h2, h3, h4⟩ := hQ S P n hn
  refine ⟨h1, h2, h3, h4, fun k _ _ t hk => ?_⟩
  obtain ⟨P', g, hg, hdim, hmul, -⟩ := hBC S _ t P
  obtain ⟨e⟩ := hRel k P' n 1 hk le_rfl
  have hn2 : 1 ≤ n ^ 2 * 1 := by
    rw [Nat.mul_one]; exact Nat.one_le_pow _ _ hn
  have hU := hH k P' (n ^ 2 * 1) hn2
  have hV := hH k P' 1 le_rfl
  rw [one_pow] at hV
  have hF : IsField Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)
  have hcard := MulLaw.natCard_eq_of_equiv_pi hF e (Nat.pow_pos hn2) hU hV
  have φ : (baseOver (Spec (CommRingCat.of k)) ⟶ P'.A) ≃* (Over.mk t ⟶ P.A) := by
    have ψ := MulLaw.basePointsEquiv hg hmul (baseOver (Spec (CommRingCat.of k)))
    have ht : (baseOver (Spec (CommRingCat.of k))).hom ≫ t = t := Category.id_comp t
    rw [ht] at ψ
    exact ψ
  rw [← Nat.card_congr (φ.toEquiv.subtypeEquiv
    (p := fun x => x ^ n = 1) (q := fun x => x ^ n = 1) (fun x => by
      show x ^ n = 1 ↔ φ x ^ n = 1
      rw [← map_pow, map_eq_one_iff φ φ.injective])), hcard, hdim, Nat.mul_one, ← pow_mul]

end GlobalTheory
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem heis_irred_of_isField
    (H : ∀ (K G V : Type) [Field K] [CommGroup G] [Finite G] [AddCommGroup V] [Module K V] [Module.Finite K V] (U : G → V ≃ₗ[K] V) (e : G → G →* Kˣ), (∀ x y v, U x (U y v) = (e x y : K) • U y (U x v)) → Function.Injective e → Module.finrank K V ^ 2 ≤ Nat.card G → ∀ W : Submodule K V, (∀ x v, v ∈ W → U x v ∈ W) → W = ⊥ ∨ W = ⊤)
    (R G V : Type) [CommRing R] (hR : IsField R) [CommGroup G] [Finite G] [AddCommGroup V]
    [Module R V] (hpos : 0 < Module.finrank R V) (U : G → V ≃ₗ[R] V) (e : G → G →* Rˣ)
    (h1 : ∀ x y v, U x (U y v) = (e x y : R) • U y (U x v)) (h2 : Function.Injective e)
    (h3 : Module.finrank R V ^ 2 ≤ Nat.card G) (W : Submodule R V)
    (hW : ∀ x v, v ∈ W → U x v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  letI := hR.toField
  haveI : Module.Finite R V := Module.finite_of_finrank_pos hpos
  exact H R G V U e h1 h2 h3 W hW

theorem isField_globalFns_spec (K : Type) [Field K] :
    IsField Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
  MulEquiv.isField (Field.toIsField K)
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv

theorem irredSt_of_heis : (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ ρ : ThetaGrp P.A P.L k T → (SecM P.A P.L k T ≃ₗ[Γ(T.left, ⊤)] SecM P.A P.L k T), (∀ θ s s', IsActOf P.A P.L k θ s s' ↔ ρ θ (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧ (∀ θx θy c, CommIsOf P.A P.L k θx θy c → ∀ v, ρ θx (ρ θy v) = (c : Γ(T.left, ⊤)) • ρ θy (ρ θx v)) ∧ (∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v) ∧ ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v)) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ (θx θy : ThetaGrp P.A P.L k T) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k θx.pt θy.pt c ↔ CommIsOf P.A P.L k θx θy c) ∧ (∀ x : T ⟶ P.A, x ^ k = 1 → Subsingleton T.left → ∃ θ : ThetaGrp P.A P.L k T, θ.pt = x ∧ (Odd k → SymLift P.A P.L k k x θ))) → (∀ (K G V : Type) [Field K] [CommGroup G] [Finite G] [AddCommGroup V] [Module K V] [Module.Finite K V] (U : G → V ≃ₗ[K] V) (e : G → G →* Kˣ), (∀ x y v, U x (U y v) = (e x y : K) • U y (U x v)) → Function.Injective e → Module.finrank K V ^ 2 ≤ Nat.card G → ∀ W : Submodule K V, (∀ x v, v ∈ W → U x v ∈ W) → W = ⊥ ∨ W = ⊤) → WeilSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c)) → WeilNondegSt → MulNSt → GlobalSectionsRankAlgClosed → IrredSt := by
  intro hρ hWC hH hW hW3 hND hM hH0 K _ _ P k hk hkK W hstab
  have hk1 : 1 ≤ k := by omega
  obtain ⟨ρ, hact, hcomm, -, -⟩ := hρ _ P k (baseOver (Spec (CommRingCat.of K)))
  obtain ⟨hwc, hlift⟩ := hWC _ P k (baseOver (Spec (CommRingCat.of K)))
  obtain ⟨hex, hmul, -, -⟩ := hW _ P k (baseOver (Spec (CommRingCat.of K)))
  obtain ⟨-, hskew, -⟩ := hW3 _ P k (baseOver (Spec (CommRingCat.of K)))
  have hsub : Subsingleton (baseOver (Spec (CommRingCat.of K))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let G : Subgroup (baseOver (Spec (CommRingCat.of K)) ⟶ P.A) := (powMonoidHom k).ker
  have hG : ∀ x : G, x.1 ^ k = 1 := fun x => x.2
  have hcard : Nat.card G = k ^ (2 * P.g) :=
    (hM _ P k hk1).2.2.2.2 K (𝟙 _) hkK
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  choose θ hθ using fun x : G => hlift x.1 (hG x) hsub
  choose c hc hcu using fun x y : G => hex x.1 y.1 (hG x) (hG y)
  have hcmul : ∀ x x' y : G, c (x * x') y = c x y * c x' y := fun x x' y =>
    (hcu (x * x') y _ (hmul _ _ _ _ _ (hc x y) (hc x' y))).symm
  have hcskew : ∀ x y : G, c y x = (c x y)⁻¹ := fun x y =>
    (hcu y x _ (hskew _ _ _ (hc x y))).symm
  let e : G → G →* Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ := fun x =>
    MonoidHom.mk' (fun y => c x y) (fun y y' => by
      rw [hcskew (y * y') x, hcmul, hcskew y x, hcskew y' x, mul_inv])
  have hfr := hH0 K P k hk1
  refine heis_irred_of_isField hH _ G _ (isField_globalFns_spec K)
    (by rw [hfr]; positivity) (fun x => ρ (θ x)) e ?_ ?_ ?_ W ?_
  · intro x y v
    refine hcomm _ _ _ ((hwc _ _ _).1 ?_) v
    rw [(hθ x).1, (hθ y).1]
    exact hc x y
  · intro x x' hxx
    have hone : ∀ y : G, c 1 y = 1 := fun y => by
      have := hcmul 1 1 y
      rw [_root_.mul_one] at this
      exact left_eq_mul.1 this
    have h : (x * x'⁻¹).1 = 1 := by
      refine hND K P k hkK _ (hG _) fun y hy => ?_
      have h1 : c x ⟨y, hy⟩ = c x' ⟨y, hy⟩ := DFunLike.congr_fun hxx ⟨y, hy⟩
      have h2 : c (x * x'⁻¹) ⟨y, hy⟩ = 1 := by
        rw [hcmul, h1, ← hcmul, mul_inv_cancel, hone]
      have := hc (x * x'⁻¹) ⟨y, hy⟩
      rwa [h2] at this
    exact mul_inv_eq_one.1 (Subtype.ext h)
  · rw [hfr, hcard, ← pow_mul, mul_comm]
  · intro x v hv
    exact hstab (θ x) (SecM.toSec P.A v) (SecM.toSec P.A (ρ (θ x) v)) ((hact _ _ _).2 rfl) hv

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem weilSt_of_parts :
    (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (x y : T ⟶ P.A), x ^ k = 1 → y ^ k = 1 → ∃! c : Γ(T.left, ⊤)ˣ, WeilIs P.A P.L k x y c) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (x x' y : T ⟶ P.A) (c c' : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k x' y c' → WeilIs P.A P.L k (x * x') y (c * c')) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c)) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (l : ℕ) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), IsUnit ((k * l : ℕ) : Γ(T.left, ⊤)) → x ^ (k * l) = 1 → y ^ k = 1 → (WeilIs P.A P.L (k * l) x y c ↔ WeilIs P.A P.L k (x ^ l) y c)) → WeilSt := by
  intro h₁ h₂ h₃ h₄ S _ P k T
  exact ⟨h₁ S P k T, h₂ S P k T, (h₃ S P k T).1, h₄ S P k T⟩

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SplitTorusHom

variable {S : Scheme.{0}}

theorem appTop_comp {A B C : Over S} (a : A ⟶ B) (b : B ⟶ C) (r : Γ(C.left, ⊤)) :
    (a ≫ b).left.appTop.hom r = a.left.appTop.hom (b.left.appTop.hom r) := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

theorem appTop_id {A : Over S} (r : Γ(A.left, ⊤)) : (𝟙 A : A ⟶ A).left.appTop.hom r = r := by
  rw [Over.id_left, Scheme.Hom.id_appTop]
  rfl

variable {X X' : Type} [AddCommGroup X] [AddCommGroup X']

theorem appTop_mul_charUnit {Z : Over S} (a b : Z ⟶ splitTorus S X) (χ : X) :
    (a * b).left.appTop.hom (charUnit S X χ).val =
      a.left.appTop.hom (charUnit S X χ).val * b.left.appTop.hom (charUnit S X χ).val := by
  rw [← splitTorusPointsEquiv_val, ← splitTorusPointsEquiv_val, ← splitTorusPointsEquiv_val,
    map_mul]
  rfl

theorem charUnit_add (x y : X) :
    (charUnit S X (x + y)).val = (charUnit S X x).val * (charUnit S X y).val := by
  have h (z : X) := (splitTorusPointsEquiv_val S X _ (𝟙 _) z).trans (appTop_id _)
  rw [← h, ← h, ← h, ofAdd_add, map_mul, Units.val_mul]

theorem existsUnique_pullback_charUnit [ConnectedSpace S]
    (f : splitTorus S X' ⟶ splitTorus S X) [IsMonHom f] (χ : X) :
    ∃! x : X', f.left.appTop.hom (charUnit S X χ).val = (charUnit S X' x).val := by
  haveI : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›
  obtain ⟨x, hx, hu⟩ := existsUnique_character_of_mul S X' (𝟙_ (Over S))
    (splitTorusPointsEquiv S X _ (fst (splitTorus S X') (𝟙_ (Over S)) ≫ f)
      (Multiplicative.ofAdd χ)) (fun Z t t' y => by
        rw [splitTorusPointsEquiv_val, ← appTop_comp, ← appTop_comp, ← appTop_comp,
          lift_fst_assoc, lift_fst_assoc, lift_fst_assoc, MonObj.mul_comp, appTop_mul_charUnit])
  refine ⟨x, ?_, fun x' hx' => hu x' ?_⟩
  · have := congrArg (lift (𝟙 (splitTorus S X')) (toUnit _)).left.appTop.hom hx
    rwa [splitTorusPointsEquiv_val, ← appTop_comp, ← appTop_comp, lift_fst_assoc, lift_fst,
      Category.id_comp, appTop_id] at this
  · beta_reduce at hx' ⊢
    rw [splitTorusPointsEquiv_val, appTop_comp, hx']

theorem charUnit_injective [ConnectedSpace S] {x y : X}
    (h : (charUnit S X x).val = (charUnit S X y).val) : x = y :=
  (existsUnique_pullback_charUnit (𝟙 (splitTorus S X)) x).unique (appTop_id _)
    ((appTop_id _).trans h)

theorem exists_addMonoidHom [ConnectedSpace S]
    (f : splitTorus S X' ⟶ splitTorus S X) [IsMonHom f] :
    ∃ φ : X →+ X', ∀ χ, f.left.appTop.hom (charUnit S X χ).val = (charUnit S X' (φ χ)).val := by
  choose c hc using fun χ => (existsUnique_pullback_charUnit f χ).exists
  refine ⟨AddMonoidHom.mk' c fun a b => charUnit_injective (S := S) ?_, hc⟩
  rw [← hc, charUnit_add, charUnit_add, map_mul, hc, hc]

end SplitTorusHom


open SplitTorusHom in
theorem exists_addEquiv_of_splitTorus_iso :
    ∀ (S : Scheme.{0}) [ConnectedSpace S] (X X' : Type) [AddCommGroup X] [AddCommGroup X']
      (θ : splitTorus S X' ≅ splitTorus S X), IsMonHom θ.hom →
      ∃ xe : X' ≃+ X, ∀ x : X',
        θ.hom.left.appTop.hom (charUnit S X (xe x)).val = (charUnit S X' x).val := by
  intro S _ X X' _ _ θ hθ
  letI : IsMonHom θ.hom := hθ
  obtain ⟨φ, hφ⟩ := SplitTorusHom.exists_addMonoidHom θ.hom
  obtain ⟨ψ, hψ⟩ := SplitTorusHom.exists_addMonoidHom θ.inv
  have h1 (x : X') : φ (ψ x) = x := SplitTorusHom.charUnit_injective (S := S) (by
    rw [← hφ, ← hψ, ← SplitTorusHom.appTop_comp, Iso.hom_inv_id,
      SplitTorusHom.appTop_id])
  have h2 (x : X) : ψ (φ x) = x := SplitTorusHom.charUnit_injective (S := S) (by
    rw [← hψ, ← hφ, ← SplitTorusHom.appTop_comp, Iso.inv_hom_id,
      SplitTorusHom.appTop_id])
  refine ⟨{ ψ with invFun := φ, left_inv := h1, right_inv := h2 }, fun x => ?_⟩
  rw [hφ]
  exact congrArg (fun z => (charUnit S X' z).val) (h1 x)

end GlobalTheory
end
