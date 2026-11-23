module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle143
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle144
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def wz {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T) (I : Fin j → Fin d) (s : ComposableArrows C j) :
    Φ.A.obj (s.obj (Fin.last j)) :=
  ∏ k : Fin j, (Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
    (u (I k) (s.obj k.succ) -
      (Φ.A.map (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))).hom (u (I k) (s.obj k.castSucc)))

theorem wz_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    (I : Fin j → Fin d) (s : ComposableArrows C j) : wz u I s ∈ (Fil j).S _ := by
  have key : ∀ (S : Finset (Fin j)) (f : Fin j → Φ.A.obj (s.obj (Fin.last j))),
      (∀ k, f k ∈ (Fil 1).S _) → ∏ k ∈ S, f k ∈ (Fil ((S.card : ℕ) : ℤ)).S _ := by
    classical
    intro S f hf
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.card_empty]
      rw [hF.top _ (by simp)]
      trivial
    | insert a S ha ih =>
      have e : (insert a S).card = 1 + S.card := by rw [Finset.card_insert_of_notMem ha, Nat.add_comm]
      rw [Finset.prod_insert ha, e]
      exact hF.mul 1 S.card _ (by simpa using hf a) ih
  have := key Finset.univ (fun k => (Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
    (u (I k) (s.obj k.succ) -
      (Φ.A.map (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))).hom (u (I k) (s.obj k.castSucc))))
    (fun k => by
      rw [hF.one]
      exact Φ.J.map_mem _ (hu _ _))
  simpa [wz] using this

variable {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))

abbrev LL : (nlBase O ⊥ (dividedPowersBot O) 0).Fun := nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)

abbrev GF (r : ℕ) : Thick (LL q) ⥤ ModuleCat.{0} O := sq (thFil (LL q) r) (thFil (LL q) ((r : ℤ) + 1))

abbrev SS (l s : ℕ) (W : X.Opens) : ObjectProperty (Thick (LL q)) :=
  St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {W}

variable {q}

theorem ev_nat {W : X.Opens} {T T' : Thick (LL q)} (φ : T ⟶ T') (h : InU W T) (h' : InU W T') (f : Γ(X, W)) :
    ev T' h' f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
  have e : pt T' = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T := by
    have := φ.pt
    unfold pt
    rw [← this]
    rfl
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X) (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ W), GlobalTheory.Cris.evalAt y W hh f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
    intro y hy hh
    subst hy
    exact evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (pt T) h hh f
  exact key _ e h'

theorem ev_res {W W' : X.Opens} (hW : W' ≤ W) (T : Thick (LL q)) (h : InU W T) (h' : InU W' T) (f : Γ(X, W)) :
    ev T h' (rs hW f) = ev T h f := evalAt_res (pt T) hW h h' f

theorem ev_str {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (a : O) :
    ev T h (strV q W a) = Ideal.Quotient.mk T.J (T.i a) :=
  (evalAt_base q (Ideal.Quotient.mk ⊥) (show PtOver X q (Ideal.Quotient.mk (⊥ : Ideal O)) (T.B ⧸ T.J) from T.y).1.1 (pt T)
    (show PtOver X q (Ideal.Quotient.mk (⊥ : Ideal O)) (T.B ⧸ T.J) from T.y).2 h a).trans (T.w a)


open Classical in
def lft (W : X.Opens) (T : Thick (LL q)) (f : Γ(X, W)) : T.B :=
  if h : InU W T then Function.surjInv Ideal.Quotient.mk_surjective (ev T h f) else 0

theorem lft_spec {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f : Γ(X, W)) :
    Ideal.Quotient.mk T.J (lft W T f) = ev T h f := by
  rw [lft, dite_eq_left h]
  exact Function.surjInv_eq _ _

def IsLift (W : X.Opens) {d : ℕ} (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) : Prop :=
  ∀ i (T : Thick (LL q)) (h : InU W T), Ideal.Quotient.mk T.J (u i T) = ev T h (t i)

def Rp {W : X.Opens} (P : ObjectProperty (Thick (LL q))) {d r : ℕ} (u : Fin d → ∀ T : Thick (LL q), T.B)
    (x : Idx r d → Γ(X, W)) (c : HU (GF q r) P r) : Prop :=
  CrystallineSemistableComparison.Pb.Rep (sFil P r) (sFil P ((r : ℤ) + 1)) (fun s => ∑ I : Idx r d,
    wz (Φ := sP P) (fun i T => u i T.obj) I.1 s *
      (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I))) c

end GlobalTheory.CompanionTheory.GrForm

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

def StCocycle : Prop := ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    (y : ∀ T : C, Φ.A.obj T) (hy : ∀ {T T' : C} (φ : T ⟶ T'), y T' - (Φ.A.map φ).hom (y T) ∈ Φ.J.S T')
    (I : Fin j → Fin d),
    ∃ f : CH.Cn (sq (Fil j) (Fil ((j : ℤ) + 1))) j, CH.d _ j f = 0 ∧
      ∀ s, (show sqM (Fil j) (Fil ((j : ℤ) + 1)) _ from f s).1 = Ideal.Quotient.mk _ (wz u I s * y _)

def StExists : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens) {d : ℕ}
    (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W t u)
    (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (x : Idx r d → Γ(X, W)),
    ∃ c, Rp (W := W) P u x c

def StAdd : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens) {d : ℕ}
    (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W t u)
    (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (x x' : Idx r d → Γ(X, W))
    (c c' : HU (GF q r) P r), Rp (W := W) P u x c → Rp (W := W) P u x' c' →
      Rp (W := W) P u (x + x') (c + c') ∧ Rp (W := W) P u (-x) (-c)

def StSmul : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens) {d : ℕ}
    (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W t u)
    (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (x : Idx r d → Γ(X, W))
    (c : HU (GF q r) P r) (a : O), Rp (W := W) P u x c → Rp (W := W) P u (fun I => strV q W a * x I) (a • c)

def StRes : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W W' : X.Opens) (hW : W' ≤ W)
    {d : ℕ} (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W t u)
    (P P' : ObjectProperty (Thick (LL q))) (hPP : P' ≤ P) (hP : ∀ T, P T → InU W T) (hP' : ∀ T, P' T → InU W' T)
    (r : ℕ) (x : Idx r d → Γ(X, W)) (c : HU (GF q r) P r), Rp (W := W) P u x c →
      Rp (W := W') P' u (fun I => rs hW (x I)) ((resU (GF q r) hPP).pull r c)

def StAct : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens)
    (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (z : Γ(X, W)),
    ∃ m : HU (GF q r) P r →+ HU (GF q r) P r, ∀ {d : ℕ} (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B),
      IsLift W t u → ∀ (x : Idx r d → Γ(X, W)) (c : HU (GF q r) P r), Rp (W := W) P u x c →
        Rp (W := W) P u (fun I => z * x I) (m c)

def StFrame : Prop := ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {W : X.Opens} {d : ℕ} (c : Coord q W d)
    (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W c.t u),
    ∃ (E : Frame (sP (SS q l s W)) d) (σ : ∀ T, E.D ⟶ T) (θ : Γ(X, W) ≃+* (sP (SS q l s W)).A.obj E.D),
      E.GrConst (sFil (SS q l s W)) ∧ (∀ n : ℕ, n ≠ 0 → (sFil (SS q l s W) n).S E.D = ⊥) ∧
      E.Coords (fun i => θ (c.t i)) ∧
      (∀ i T, ((sP (SS q l s W)).A.map (σ T)).hom (θ (c.t i)) = u i T.obj) ∧
      ∀ (T : (SS q l s W).FullSubcategory) (h : InU W T.obj) (f : Γ(X, W)),
        Ideal.Quotient.mk T.obj.J (show T.obj.B from ((sP (SS q l s W)).A.map (σ T)).hom (θ f)) = ev T.obj h f

def StLoc : Prop := ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {W : X.Opens} {d : ℕ} (c : Coord q W d)
    (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W c.t u) (r : ℕ) (hr : r < s),
    (∀ cl : HU (GF q r) (SS q l s W) r, ∃ x, Rp (W := W) (SS q l s W) u x cl) ∧
      ∀ x : Idx r d → Γ(X, W), Rp (W := W) (SS q l s W) u x 0 → x = 0

def StVan : Prop := ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (r j : ℕ), r < s → j ≠ r →
    Subsingleton (HU (GF q r) (SS q l s W) j)

def StVB : Prop := ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {ι : Type} [Fintype ι] (U : ι → X.Opens) (d : ι → ℕ)
    (c : ∀ α, Coord q (U α) (d α)) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)) (r : ℕ), r < s →
    Nonempty (VB (strV q) U (CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) r))

def StCover : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [Smooth q]
    (V : X.Opens), IsAffineOpen V → ∃ (ι : Type) (_ : Fintype ι) (U : ι → X.Opens) (d : ι → ℕ)
      (_ : ∀ α, Coord q (U α) (d α)), (⨆ α, U α) = V ∧ ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)

end GlobalTheory.CompanionTheory.GrForm
end
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.coordinates_restrict_affine_open : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {V W : X.Opens} {d : ℕ}
    (c : Coord q V d) (h : W ≤ V) (hW : IsAffineOpen W), ∃ c' : Coord q W d, ∀ i, c'.t i = rs h (c.t i) := by
  first | exact @GlobalTheory.CompanionTheory.CoordRes.main | exact GlobalTheory.CompanionTheory.CoordRes.main | (intros; apply GlobalTheory.CompanionTheory.CoordRes.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.thickening_graded_vanish_negative : ∀ {b : Base} (L : b.Fun) (Q : ObjectProperty (Thick L)) (r : ℤ), r < 0 → ∀ j : ℕ,
    Subsingleton (HU (gr (Φ := thP L) (thFil L) r) Q j) := by
  first | exact @GlobalTheory.CompanionTheory.Cone.HU_gr_neg | exact GlobalTheory.CompanionTheory.Cone.HU_gr_neg | (intros; apply GlobalTheory.CompanionTheory.Cone.HU_gr_neg <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoCoord

theorem exists_coord_basicOpen {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W)) {d : ℕ} (s : Fin d → Γ(X, W)) :
    letI := (strV q W).toAlgebra
    (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k)) :
        MvPolynomial (Fin d) K →+* Localization.Away g).Etale →
    ∃ c : Coord q (X.basicOpen g) d, ∀ k, c.t k = resO (X.basicOpen_le g) (s k) := by
  letI := (strV q W).toAlgebra
  intro h
  haveI := hW.isLocalization_basicOpen g
  let φ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, X.basicOpen g)
  have hφ : ∀ x, φ (algebraMap Γ(X, W) (Localization.Away g) x) = resO (X.basicOpen_le g) x :=
    fun x => φ.commutes x
  refine ⟨⟨hW.basicOpen g, fun k => resO (X.basicOpen_le g) (s k), ?_⟩, fun _ => rfl⟩
  have h2 := RingHom.Etale.stableUnderComposition _ _ h
    (RingHom.Etale.of_bijective (f := (φ : Localization.Away g →+* Γ(X, X.basicOpen g))) φ.bijective)
  have e : (MvPolynomial.eval₂Hom (strV q (X.basicOpen g)) (fun k => resO (X.basicOpen_le g) (s k)) :
        MvPolynomial (Fin d) K →+* Γ(X, X.basicOpen g)) =
      (φ : Localization.Away g →+* Γ(X, X.basicOpen g)).comp
        (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
          (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k))) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)
    · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.comp_apply]
      rw [strV_res q (X.basicOpen_le g), RingHom.comp_apply, IsScalarTower.algebraMap_apply K Γ(X, W) (Localization.Away g)]
      exact (hφ _).symm
    · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, RingHom.comp_apply]
      exact (hφ _).symm
  rw [e]
  exact h2

end GlobalTheory.CompanionTheory.GeoCoord
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeUnit

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem pt_of_hom {T T' : Thick (smFun X q)} (φ : T ⟶ T') :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T = pt T' := by
  have := φ.pt
  unfold pt
  rw [← this]
  rfl

theorem spec_comp {C : Type 1} [Category.{0} C] (g : C ⥤ Thick (smFun X q)) {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ (g.map (a ≫ b)).hle)) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) := by
  have hφ : (g.map (a ≫ b)).φ = (g.map b).φ.comp (g.map a).φ := by rw [g.map_comp]; rfl
  rw [← Spec.map_comp]
  congr 1
  ext x
  show Ideal.Quotient.mk _ ((g.map (a ≫ b)).φ x) = Ideal.Quotient.mk _ ((g.map b).φ ((g.map a).φ x))
  rw [hφ]
  rfl

theorem u_points (D : E.LineData X) {V : Scheme.{0}} {a a' b : V ⟶ D.Y} (ha : a = a')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b ≫ D.f) : D.u a b h = D.u a' b h' := by
  subst ha
  rfl

theorem gamma_nat {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom y) =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y) :=
  congrArg (fun k => k.hom y) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem r_sub_mem {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D)
    {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) (c : c₀ ⟶ c₂) (hc : c = a ≫ b) :
    ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) * Λ.w b * (Λ.w c)⁻¹ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈
      (g.obj c₂).J := by
  subst hc
  have ea := pt_of_hom (g.map a)
  have eb := pt_of_hom (g.map b)
  have ec := pt_of_hom (g.map (a ≫ b))
  have h1 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) ≫ Λ.p c₀) ≫ D.f =
      Λ.p c₁ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, ea]
  have h2 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ Λ.p c₁) ≫ D.f =
      Λ.p c₂ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, eb]
  have h3 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ (g.map (a ≫ b)).hle)) ≫ Λ.p c₀) ≫ D.f =
      Λ.p c₂ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, ec]
  have wa := Λ.hw a h1
  have wb := Λ.hw b h2
  have wc := Λ.hw (a ≫ b) h3
  have nat := D.nat (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle))) _ _ h1
  have h12 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) ≫ Λ.p c₀) ≫ D.f =
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ Λ.p c₁) ≫ D.f := by
    simpa only [Category.assoc] using
      congrArg (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ ·) h1
  have coc := D.coc _ _ _ h12 h2
  have uc := u_points D (show Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ
      (g.map (a ≫ b)).hle)) ≫ Λ.p c₀ = _ by rw [spec_comp, Category.assoc]) h3 (h12.trans h2)
  have A : Ideal.Quotient.mk (g.obj c₂).J ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) : (g.obj c₂).Bˣ) : (g.obj c₂).B) =
      (Scheme.ΓSpecIso (CommRingCat.of ((g.obj c₂).B ⧸ (g.obj c₂).J))).hom.hom
        (D.u _ _ h12).1 := by
    show Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle (Ideal.Quotient.mk (g.obj c₁).J (Λ.w a)) = _
    rw [wa, nat, ← gamma_nat]
    rfl
  have B : Ideal.Quotient.mk (g.obj c₂).J ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) : (g.obj c₂).Bˣ) : (g.obj c₂).B) *
      Ideal.Quotient.mk (g.obj c₂).J (Λ.w b) = Ideal.Quotient.mk (g.obj c₂).J (Λ.w (a ≫ b)) := by
    rw [A, wb, wc, ← map_mul, ← Units.val_mul, coc, uc]
  rw [← Ideal.Quotient.eq, map_one, Units.val_mul, Units.val_mul, map_mul, map_mul, B, ← map_mul, Units.mul_inv, map_one]

theorem r_sub_one : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (σ : ComposableArrows C 2), ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1) ∈ (g.obj (σ.obj (Fin.last 2))).J := by
  intro K _ _ X q C _ g D Λ σ
  exact r_sub_mem Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) (by
    rw [← Functor.map_comp]
    rfl)

end GlobalTheory.CompanionTheory.ConeUnit
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GeoNetop

attribute [local instance] MvPolynomial.gradedAlgebra

theorem irrelevant_le_spanX (K : Type) [Field K] (N : ℕ) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K)) := by
  intro x hx
  have h0 := (HomogeneousIdeal.mem_irrelevant_iff _ _).1 hx
  rw [GradedRing.proj_apply] at h0
  have h1 : MvPolynomial.homogeneousComponent 0 x = 0 := by
    rw [← MvPolynomial.decomposition.decompose'_apply]
    exact h0
  rw [MvPolynomial.homogeneousComponent_zero, MvPolynomial.C_eq_zero] at h1
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (MvPolynomial.mem_support_iff.1 hm) h1
  obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hm0
  exact ⟨a, Set.mem_univ _, ha⟩

theorem exists_chart {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (x : X) :
    ∃ j : Fin (N + 1), x ∈ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) := by
  have h := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) MvPolynomial.X
    (irrelevant_le_spanX K N)
  have hx : i x ∈ ⨆ j, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X j) := by
    rw [h]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨j, hj⟩

theorem mk_C_mul_inv {K : Type} [Field K] {N : ℕ} (j : Fin (N + 1)) (c : K) (hc : c ≠ 0)
    (ha : MvPolynomial.C c ∈ grK K N (0 • 1)) (hb : MvPolynomial.C c⁻¹ ∈ grK K N (0 • 1)) :
    HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) 0 (MvPolynomial.C c) ha *
      HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) 0 (MvPolynomial.C c⁻¹) hb = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk, Localization.mk_mul, ← map_mul, mul_inv_cancel₀ hc]

theorem constantCoeff_gen {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (hX : Nonempty X)
    {f : MvPolynomial (Fin (N + 1)) K} (d : ℕ) (hf : f ∈ grK K N (d • 1))
    (h0 : ∀ j : Fin (N + 1), evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf) = 0) :
    MvPolynomial.constantCoeff f = 0 := by
  have hc := MvPolynomial.homogeneousComponent_of_mem (m := 0) hf
  rw [MvPolynomial.homogeneousComponent_zero] at hc
  rw [MvPolynomial.constantCoeff_eq]
  by_cases hd : 0 = d • 1
  · rw [if_pos hd] at hc
    have hd0 : d = 0 := by simpa using hd.symm
    subst hd0
    obtain ⟨c, rfl⟩ : ∃ c, f = MvPolynomial.C c := ⟨_, hc.symm⟩
    rw [MvPolynomial.coeff_zero_C]
    by_contra hne
    obtain ⟨x⟩ := hX
    obtain ⟨j, hj⟩ := exists_chart i x
    haveI : Nonempty (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) := ⟨⟨x, hj⟩⟩
    haveI := Scheme.component_nontrivial X (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j))
    have hb : MvPolynomial.C c⁻¹ ∈ grK K N (0 • 1) := by
      simpa using MvPolynomial.isHomogeneous_C (Fin (N + 1)) c⁻¹
    have e := congrArg (evV i (MvPolynomial.X j) _ le_rfl) (mk_C_mul_inv j c hne hf hb)
    rw [map_mul, map_one, h0 j, zero_mul] at e
    exact zero_ne_one e
  · rw [if_neg hd, MvPolynomial.C_eq_zero] at hc
    exact hc

theorem homIdeal_ne_top : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N),
    Nonempty X → homIdeal i ≠ ⊤ := by
  intro K _ X N i hX htop
  have hle : homIdeal i ≤ RingHom.ker (MvPolynomial.constantCoeff (σ := Fin (N + 1)) (R := K)) := by
    refine Ideal.span_le.2 ?_
    rintro f ⟨d, hf, h0⟩
    exact (RingHom.mem_ker).2 (constantCoeff_gen i hX d hf h0)
  have h1 : (1 : MvPolynomial (Fin (N + 1)) K) ∈ RingHom.ker (MvPolynomial.constantCoeff (σ := Fin (N + 1)) (R := K)) :=
    hle (htop ▸ Submodule.mem_top)
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1
end GlobalTheory.CompanionTheory.GeoNetop
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

theorem evV_surjective : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), IsClosedImmersion i → ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (hg : g ∈ grK K N e), 0 < e → Function.Surjective (evV i g (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl) := by
  intro K _ X N i hi g e hg he
  have hU : IsAffineOpen (Proj.basicOpen (grK K N) g) := Proj.isAffineOpen_basicOpen (grK K N) g hg he
  have hiso : IsIso (Proj.awayToSection (grK K N) g) := (Proj.basicOpenIsoAway (grK K N) g hg he).isIso_hom
  have h1 : Function.Surjective (Proj.awayToSection (grK K N) g).hom :=
    (ConcreteCategory.bijective_of_isIso (Proj.awayToSection (grK K N) g)).2
  have h2 : Function.Surjective (i.appLE _ (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact i.app_surjective _ hU
  exact h2.comp h1

end GlobalTheory.CompanionTheory.Geo
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

theorem homIdeal_homog {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) :
    ∀ f ∈ homIdeal i, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ homIdeal i := by
  intro f hf n
  have hI : (homIdeal i).IsHomogeneous (grK K N) := by
    refine Ideal.homogeneous_span (grK K N) _ ?_
    rintro g ⟨d, hg, -⟩
    exact ⟨d • 1, hg⟩
  have h := hI n hf
  have e : ((DirectSum.decompose (grK K N) f n : grK K N n) : MvPolynomial (Fin (N + 1)) K) =
      MvPolynomial.homogeneousComponent n f :=
    MvPolynomial.decomposition.decompose'_apply f n
  exact e ▸ h

end GlobalTheory.CompanionTheory.Geo
end
