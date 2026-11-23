module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Lemmata.GeneralBFactFurther.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen

variable {V : Type} [CommRing V] [IsDomain V]

theorem isLocalization_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    IsLocalization.Away ϖ (FractionRing V) := by
  first | exact Bl.general_b_fact_further.goal1 .. | (apply Bl.general_b_fact_further.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_further.goal1 <;> assumption)

theorem isOpenImmersion_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    IsOpenImmersion (spMap (algebraMap V (FractionRing V))) := by
  have := isLocalization_frac hϖ
  let e := IsLocalization.algEquiv (Submonoid.powers ϖ) (Localization.Away ϖ) (FractionRing V)
  have he : algebraMap V (FractionRing V) =
      (e : Localization.Away ϖ →+* FractionRing V).comp (algebraMap V (Localization.Away ϖ)) :=
    RingHom.ext fun x => (e.commutes x).symm
  have : IsIso (CommRingCat.ofHom (e : Localization.Away ϖ →+* FractionRing V)) :=
    ⟨⟨CommRingCat.ofHom (e.symm : FractionRing V →+* Localization.Away ϖ), by ext x; simp, by ext x; simp⟩⟩
  show IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  rw [he, CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

theorem opensRange_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    haveI := isOpenImmersion_frac hϖ
    (spMap (algebraMap V (FractionRing V))).opensRange =
      (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ϖ) := by
  have := isLocalization_frac hϖ
  rw [basicOpen_eq_of_affine]
  ext1
  exact PrimeSpectrum.localization_away_comap_range (FractionRing V) ϖ

theorem eq_zero_of_mul {X : Scheme.{0}} (p : X ⟶ Sp V) [Flat p] {r : V} (hr : r ≠ 0) (f : Γ(X, ⊤))
    (h : p.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv r) * f = 0) : f = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ f 0 fun x hx => ?_
  show X.presheaf.germ ⊤ x hx f = X.presheaf.germ ⊤ x hx 0
  set r' := (Scheme.ΓSpecIso (CommRingCat.of V)).inv r with hr'def
  have hr' : r' ≠ 0 := by
    intro h0
    apply hr
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of V)).hom h0
    rwa [hr'def, Iso.inv_hom_id_apply, map_zero] at this
  set g := (Sp V).presheaf.germ ⊤ (p.base x) trivial r' with hgdef
  have hg : g ≠ 0 := fun h0 =>
    hr' (germ_injective_of_isIntegral (Sp V) (U := ⊤) (p.base x) trivial (h0.trans (map_zero _).symm))
  let := (p.stalkMap x).hom.toAlgebra
  have : Module.Flat _ (X.presheaf.stalk x) := Flat.stalkMap p x
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := X.presheaf.stalk x)
    (mem_nonZeroDivisors_of_ne_zero hg)
  have key : (p.stalkMap x).hom g * X.presheaf.germ ⊤ x hx f = 0 := by
    have h1 : (p.stalkMap x).hom g = X.presheaf.germ ⊤ x hx (p.appTop r') :=
      Scheme.Hom.germ_stalkMap_apply p ⊤ x trivial r'
    rw [h1]
    show X.presheaf.germ ⊤ x hx (p.appTop r') * X.presheaf.germ ⊤ x hx f = 0
    rw [← map_mul, h, map_zero]
  have h2 : g • X.presheaf.germ ⊤ x hx f = g • 0 := by
    rw [smul_zero, Algebra.smul_def]
    exact key
  rw [hreg h2, map_zero]

theorem restrict_basicOpen_injective {X : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X]
    (s : Γ(X, ⊤)) (hs : ∀ f : Γ(X, ⊤), s * f = 0 → f = 0) :
    Function.Injective (X.presheaf.map (homOfLE (le_top : X.basicOpen s ≤ ⊤)).op) := by
  have := isLocalization_basicOpen_of_qcqs (X := X) (U := ⊤) (by simpa using isCompact_univ)
    (by simpa using isQuasiSeparated_univ) s
  have hM : Submonoid.powers s ≤ nonZeroDivisors Γ(X, ⊤) :=
    Submonoid.powers_le.2 (mem_nonZeroDivisors_iff_right.2 fun f hf => hs f (by rwa [mul_comm] at hf))
  exact IsLocalization.injective (Γ(X, X.basicOpen s)) hM

theorem appTop_fst_injective [IsDiscreteValuationRing V] {X : Scheme.{0}} (p : X ⟶ Sp V) [Flat p]
    [QuasiCompact p] [QuasiSeparated p] :
    haveI := isOpenImmersion_frac (IsDiscreteValuationRing.exists_irreducible V).choose_spec
    Function.Injective (pullback.fst p (spMap (algebraMap V (FractionRing V)))).appTop := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  haveI := isOpenImmersion_frac hϖ
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p
  set s := p.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ϖ) with hs
  have hrange : (pullback.fst p (spMap (algebraMap V (FractionRing V)))) ''ᵁ ⊤ = X.basicOpen s := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_pullbackFst, opensRange_frac hϖ,
      Scheme.preimage_basicOpen_top]
  have hfac : (pullback.fst p (spMap (algebraMap V (FractionRing V)))).appTop =
      X.presheaf.map (homOfLE le_top : (pullback.fst p (spMap (algebraMap V (FractionRing V)))) ''ᵁ ⊤ ⟶ ⊤).op ≫
        ((pullback.fst p (spMap (algebraMap V (FractionRing V)))).appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    exact Scheme.Hom.app_eq_appLE _
  have hinj := restrict_basicOpen_injective s (fun f hf => eq_zero_of_mul p hϖ.ne_zero f hf)
  have hW : ∀ (W : X.Opens), W = X.basicOpen s →
      Function.Injective (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) := by
    rintro W rfl
    exact hinj
  rw [hfac]
  intro a b hab
  simp only [CategoryTheory.comp_apply] at hab
  exact hW _ hrange ((ConcreteCategory.bijective_of_isIso _).1 hab)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R : Type} [CommRing R] {d : ℕ}

lemma hasSubst_ev {m n : ℕ} (a : Fin m → Pt R n d) (h : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => h p.1 p.2)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => h p.1 p.2)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [h p.1 p.2]; exact IsNilpotent.zero)

lemma ev_X {m n : ℕ} (a : Fin m → Pt R n d) (h : ∀ j i, constantCoeff (a j i) = 0)
    (j : Fin m) (i : Fin d) : ev a (X (j, i) : PS R m d) = a j i := by
  unfold ev
  rw [MvPowerSeries.subst_X (hasSubst_ev a h)]

lemma ev_add {m n : ℕ} (a : Fin m → Pt R n d) (h : ∀ j i, constantCoeff (a j i) = 0)
    (f g : PS R m d) : ev a (f + g) = ev a f + ev a g := by
  unfold ev
  exact MvPowerSeries.subst_add (hasSubst_ev a h) f g

lemma ev_mul {m n : ℕ} (a : Fin m → Pt R n d) (h : ∀ j i, constantCoeff (a j i) = 0)
    (f g : PS R m d) : ev a (f * g) = ev a f * ev a g := by
  unfold ev
  exact MvPowerSeries.subst_mul (hasSubst_ev a h) f g

lemma ev_C {m n : ℕ} (a : Fin m → Pt R n d) (r : R) : ev a (C r : PS R m d) = C r := by
  unfold ev MvPowerSeries.subst
  letI : UniformSpace R := ⊥
  first
  | (open MvPowerSeries.WithPiTopology in rw [MvPowerSeries.eval₂_C])
  | erw [MvPowerSeries.eval₂_C]
  all_goals first
    | rfl
    | simp [MvPowerSeries.algebraMap_apply]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

abbrev JetR (R : Type) [CommRing R] (κ : Type) (m : ℕ) : Type :=
  MvPolynomial κ R ⧸ (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))) ^ (m + 1)

abbrev algOver (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] : Over (Sp R) :=
  Over.mk (spMap (algebraMap R A))

def algOverHom {R : Type} [CommRing R] {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (ψ : A →ₐ[R] B) : algOver R B ⟶ algOver R A :=
  Over.homMk (spMap (ψ : A →+* B)) (by
    dsimp
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap)

def jetTruncR (R : Type) [CommRing R] (κ : Type) (m : ℕ) : JetR R κ (m + 1) →ₐ[R] JetR R κ m :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))

def jetZeroR (R : Type) [CommRing R] (κ : Type) (m : ℕ) : JetR R κ m →ₐ[R] JetR R κ 0 :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))

abbrev zR {R : Type} [CommRing R] {κ : Type} (m : ℕ) (j : κ) : JetR R κ m := Ideal.Quotient.mk _ (MvPolynomial.X j)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi

variable {S X : Scheme.{0}}

def abLocus (G : Over S) : Set S :=
  {s | ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S), s ∈ Set.range t → IsProper (pullback.snd G.hom t)}

structure OAct (O : Type) [CommRing O] (G : Over S) [GrpObj G] where

  act : O → (G ⟶ G)
  hom : ∀ a, IsMonHom (act a)
  one : act 1 = 𝟙 G
  mul : ∀ a b, act (a * b) = act a ≫ act b
  add : ∀ a b, act (a + b) = act a * act b

def IsGrpPullback {S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S)
    (φ : G'.left ⟶ G.left) : Prop :=
  IsPullback φ G'.hom G.hom f ∧
    ∀ (T : Over S') (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G),
      x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ → (x₀ * y₀).left = (x * y).left ≫ φ

abbrev resG (X : Scheme.{0}) {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

def secOn (L : LB X) (V : X.Opens) : Set (∀ i, Γ(X, V ⊓ L.U i)) :=
  {s | ∀ i j,
    resG X (inf_le_left : V ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U i) (s i) =
      resG X (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          V ⊓ L.U i ⊓ L.U j ≤ L.U i ⊓ L.U j) (L.g i j : Γ(X, L.U i ⊓ L.U j)) *
        resG X (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          V ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U j) (s j)}

def LBIso (L M : LB X) : Prop := ∃ w : LB.Iso L M, w.IsGen

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

def isoInv {X : Scheme.{0}} {L M : LB X} (t : LB.Iso L M) : LB.Iso M L :=
  ⟨fun p => (res (fun _ hx => ⟨hx.2, hx.1⟩ : L.U p.1 ⊓ M.U p.2 ≤ M.U p.2 ⊓ L.U p.1) (t.s (p.2, p.1)))⁻¹⟩

private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V)
    (x : Γ(X, U)ˣ) : res h2 (res h1 x) = res (h2.trans h1) x := by
  ext
  change (X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op).hom (x : Γ(X, U)) = _
  rw [← Functor.map_comp]
  rfl

private theorem inv_of_eq_mul_inv_mul {G : Type*} [CommGroup G] {a b l m : G} (e : a = m * l⁻¹ * b) :
    a⁻¹ = l * m⁻¹ * b⁻¹ := by
  subst e
  rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_comm]

theorem isoInv_isGen {X : Scheme.{0}} {L M : LB X} {t : LB.Iso L M} (ht : t.IsGen) : (isoInv t).IsGen := by
  unfold LB.Gen.IsGen at ht ⊢
  rintro (p : L.ι × M.ι) (q : L.ι × M.ι)
  have key : ∀ (a : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) (b : Γ(X, M.U q.2 ⊓ L.U q.1)ˣ),
      res (inf_le_left : M.U p.2 ⊓ L.U p.1 ⊓ (M.U q.2 ⊓ L.U q.1) ≤ M.U p.2 ⊓ L.U p.1) a =
        res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
            M.U p.2 ⊓ L.U p.1 ⊓ (M.U q.2 ⊓ L.U q.1) ≤ M.U p.2 ⊓ M.U q.2) (M.g p.2 q.2) *
          (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
            M.U p.2 ⊓ L.U p.1 ⊓ (M.U q.2 ⊓ L.U q.1) ≤ L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1))⁻¹ *
        res (inf_le_right : M.U p.2 ⊓ L.U p.1 ⊓ (M.U q.2 ⊓ L.U q.1) ≤ M.U q.2 ⊓ L.U q.1) b →
      res (inf_le_left : L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ L.U p.1 ⊓ M.U p.2)
          (res (inf_comm (L.U p.1) (M.U p.2)).le a)⁻¹ =
        res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
            L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1) *
          (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
            L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ M.U p.2 ⊓ M.U q.2) (M.g p.2 q.2))⁻¹ *
        res (inf_le_right : L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ L.U q.1 ⊓ M.U q.2)
          (res (inf_comm (L.U q.1) (M.U q.2)).le b)⁻¹ := by
    intro a b e
    have hW : L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ M.U p.2 ⊓ L.U p.1 ⊓ (M.U q.2 ⊓ L.U q.1) :=
      fun _ hx => ⟨⟨hx.1.2, hx.1.1⟩, ⟨hx.2.2, hx.2.1⟩⟩
    have e' := congrArg (res hW) e
    simp only [map_mul, map_inv, res_res_lemma] at e' ⊢
    exact inv_of_eq_mul_inv_mul e'
  exact key _ _ (ht (p.2, p.1) (q.2, q.1))

def pullGenLB {X Y : Scheme.{0}} {L : LB X} (c : LB.Gen L) (h : Y ⟶ X) : LB.Gen (L.pull h) :=
  ⟨fun j => res (fun _ hy => Set.mem_iInter.1 hy PUnit.unit : (L.pull h).U j ≤ h ⁻¹ᵁ L.U (j PUnit.unit))
    (pullU h _ (c.s (j PUnit.unit)))⟩

private theorem pullU_res_lemma_2 {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U)
    (x : Γ(X, U)ˣ) : pullU f V (res h x) = res ((TopologicalSpace.Opens.map f.base).monotone h : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (pullU f U x) := by
  ext
  change (X.presheaf.map (homOfLE h).op ≫ f.app V).hom (x : Γ(X, U)) =
    (f.app U ≫ Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map f.base).monotone h : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U)).op).hom (x : Γ(X, U))
  rw [f.naturality]
  rfl

theorem pullGenLB_isGen {X Y : Scheme.{0}} {L : LB X} {c : LB.Gen L} (hc : c.IsGen) (h : Y ⟶ X) :
    (pullGenLB c h).IsGen := by
  unfold LB.Gen.IsGen at hc ⊢
  rintro (j : PUnit → L.ι) (j' : PUnit → L.ι)
  have key : ∀ (a : Γ(X, L.U (j PUnit.unit))ˣ) (b : Γ(X, L.U (j' PUnit.unit))ˣ),
      res (inf_le_left : L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) ≤ L.U (j PUnit.unit)) a =
        L.g (j PUnit.unit) (j' PUnit.unit) *
          res (inf_le_right : L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) ≤ L.U (j' PUnit.unit)) b →
      res (inf_le_left : LB.wchart L (fun _ : PUnit => h) j ⊓ LB.wchart L (fun _ : PUnit => h) j' ≤ LB.wchart L (fun _ : PUnit => h) j)
          (res (LB.wchart_le L (fun _ : PUnit => h) j PUnit.unit : LB.wchart L (fun _ : PUnit => h) j ≤ h ⁻¹ᵁ L.U (j PUnit.unit))
            (pullU h (L.U (j PUnit.unit)) a)) =
        (∏ k : PUnit, (res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => h) j k))
            (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => h) j' k)) :
              LB.wchart L (fun _ : PUnit => h) j ⊓ LB.wchart L (fun _ : PUnit => h) j' ≤ h ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
            (pullU h (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)))) ^ (1 : ℤ)) *
        res (inf_le_right : LB.wchart L (fun _ : PUnit => h) j ⊓ LB.wchart L (fun _ : PUnit => h) j' ≤ LB.wchart L (fun _ : PUnit => h) j')
          (res (LB.wchart_le L (fun _ : PUnit => h) j' PUnit.unit : LB.wchart L (fun _ : PUnit => h) j' ≤ h ⁻¹ᵁ L.U (j' PUnit.unit))
            (pullU h (L.U (j' PUnit.unit)) b)) := by
    intro a b e
    have hW : LB.wchart L (fun _ : PUnit => h) j ⊓ LB.wchart L (fun _ : PUnit => h) j' ≤ h ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
      fun _ hx => ⟨LB.wchart_le L (fun _ : PUnit => h) j PUnit.unit hx.1,
        LB.wchart_le L (fun _ : PUnit => h) j' PUnit.unit hx.2⟩
    have e' := congrArg (fun x => res hW (pullU h (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) x)) e
    simp only [map_mul, pullU_res_lemma_2, res_res_lemma] at e'
    simp only [res_res_lemma, Fintype.prod_unique, zpow_one]
    exact e'
  exact key _ _ (hc (j PUnit.unit) (j' PUnit.unit))

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
