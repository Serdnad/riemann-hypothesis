module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle066
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.UnitVal

section Values
variable {C : Type} [Field C] {X Y : Scheme.{0}}

theorem valF_appLE' {F : Type} [Field F] {x : Sp F ⟶ X} {U : X.Opens} (f : X ⟶ Y) (W : Y.Opens) (e : U ≤ f ⁻¹ᵁ W)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, W)) : valF x U ((f.appLE W U e).hom a) = valF (x ≫ f) W a := by
  have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ W := fun q hq => e (h hq)
  rw [valF, valF, dite_eq_left h, dite_eq_left h', ← Scheme.Hom.appLE_comp_appLE x f W U ⊤ e h]
  rfl

theorem valF_res' {F : Type} [Field F] {x : Sp F ⟶ X} {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dite_eq_left h, dite_eq_left h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem exists_valHom (S : ValuationSubring C) (t : Sp S ⟶ X) (U : X.Opens) (ht : ⊤ ≤ t ⁻¹ᵁ U) :
    ∃ g : Γ(X, U) →+* S, ∀ a, valF (spMap S.subtype ≫ t) U a = g a := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp (t.appLE U ⊤ ht).hom, fun a => ?_⟩
  have h' : ⊤ ≤ (spMap S.subtype ≫ t) ⁻¹ᵁ U := fun q _ => ht (Set.mem_univ (spMap S.subtype q))
  rw [valF, dite_eq_left h']
  have e : (spMap S.subtype ≫ t).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom =
      t.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫ CommRingCat.ofHom S.subtype := by
    rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap S.subtype) t U ⊤ ⊤ ht le_rfl,
      Category.assoc]
    rfl
  exact congrArg (fun g => g.hom a) e

theorem val_valF_le {S : ValuationSubring C} (t : Sp S ⟶ X) (U : X.Opens)
    (ht : ⊤ ≤ t ⁻¹ᵁ U) (a : Γ(X, U)) : valF (spMap S.subtype ≫ t) U a ∈ S := by
  obtain ⟨g, hg⟩ := exists_valHom S t U ht
  rw [hg]
  exact (g a).2

theorem val_valF_unit {S : ValuationSubring C} (t : Sp S ⟶ X) (U : X.Opens)
    (ht : ⊤ ≤ t ⁻¹ᵁ U) (a : Γ(X, U)) (ha : IsUnit a) : S.valuation (valF (spMap S.subtype ≫ t) U a) = 1 := by
  obtain ⟨g, hg⟩ := exists_valHom S t U ht
  rw [hg]
  exact (S.valuation_eq_one_iff (g a)).1 (ha.map g)
end Values

section Geo
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C] [Algebra (FractionRing R) C]
  {N : NumD C} {ν : NumOf D C N} {S : ValuationSubring C} {s : Sp S ⟶ Sp R}

theorem exists_base (h : ∀ r : R, algebraMap (FractionRing R) C (algebraMap R _ r) ∈ S) :
    ∃ s : Sp S ⟶ Sp R, spMap S.subtype ≫ s = (TF (R := R) C).hom := by
  refine ⟨spMap (((algebraMap (FractionRing R) C).comp (algebraMap R _)).codRestrict S.toSubring h), ?_⟩
  change _ = jFK (R := R) C ≫ jK R
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem base_ext {a b : Sp S ⟶ Sp R} (h : spMap S.subtype ≫ a = spMap S.subtype ≫ b) : a = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have := Spec.map_injective h
  congr 1
  ext r
  exact congrArg (fun g => g.hom r) this

theorem isDominant_sub : IsDominant (spMap S.subtype) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 S.subtype_injective]; exact bot_le)⟩

theorem chart_int (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) (y : Sp S ⟶ D.P.A.left)
    (hy : y ≫ D.P.A.hom = s) : ⊤ ≤ y ⁻¹ᵁ D.P.L.U (ν.J (spMap S.subtype ≫ y)) := by
  obtain ⟨x₀, e, h⟩ := hν (Over.homMk (spMap S.subtype ≫ y) (by rw [Category.assoc, hy, hs]))
  have := D.P.isAb.proper
  have := isDominant_sub (S := S)
  have e' : spMap S.subtype ≫ x₀ = spMap S.subtype ≫ y := e
  obtain rfl : x₀ = y := ext_of_isDominant_of_isSeparated D.P.A.hom
    (base_ext (by rw [← Category.assoc, e', Category.assoc])) _ e'
  exact h

theorem wchart_int (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) {Y : Scheme.{0}} {K : Type}
    [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) :
    ⊤ ≤ r ⁻¹ᵁ LB.wchart D.P.L φ fun k => ν.J ((spMap S.subtype ≫ r) ≫ φ k) := fun q hq =>
  Set.mem_iInter.2 fun k => by
    beta_reduce
    rw [Category.assoc]
    exact chart_int hν hs (r ≫ φ k) (by rw [Category.assoc, h]) hq

theorem val_vF (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε))
    (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) {r' : Sp C ⟶ Y} (e : spMap S.subtype ≫ r = r') :
    S.valuation (vF t r' ν.J) = 1 := by
  subst e
  exact val_valF_unit r _ (wchart_int hν hs φ r h) _ (Units.isUnit _)

theorem val_sF (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Sec (LB.LinComb D.P.L φ ε))
    (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) {r' : Sp C ⟶ Y} (e : spMap S.subtype ≫ r = r') :
    sF t r' ν.J ∈ S := by
  subst e
  exact val_valF_le r _ (wchart_int hν hs φ r h) _

theorem exists_ext (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) (x : TF (R := R) C ⟶ D.P.A) :
    ∃ x₀ : Over.mk s ⟶ D.P.A, (Over.homMk (spMap S.subtype) hs : TF (R := R) C ⟶ Over.mk s) ≫ x₀ = x := by
  obtain ⟨x₀, e, -⟩ := hν x
  refine ⟨Over.homMk x₀ (base_ext ?_), Over.OverMorphism.ext e⟩
  rw [← Category.assoc, e, Over.w x]
  exact hs.symm

theorem val_rig (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) :
    S.valuation (vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) C).hom ν.J) = 1 :=
  val_vF hν hs _ s (fun _ => by
    have : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
    exact (congrArg (s ≫ ·) this).trans (Category.comp_id _)) hs

theorem val_θ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x y u : N.A) : S.valuation ((N.θ x y u : C)) = 1 := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  obtain ⟨y₀, hy⟩ := exists_ext hν hs (ν.eA y)
  obtain ⟨u₀, hu⟩ := exists_ext hν hs (ν.eA u)
  rw [ν.θ_eq]
  refine val_vF hν hs _ (lift x₀ (lift y₀ u₀)).left (fun k => ?_) ?_
  · exact (congrArg (_ ≫ ·) (Over.w (psum D.P.A (x3 D.P.A) k.down))).trans (Over.w (lift x₀ (lift y₀ u₀)))
  · rw [← hx, ← hy, ← hu, ← comp_lift, ← comp_lift]
    rfl

theorem val_σ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x : N.A) : S.valuation ((N.σ x : C)) = 1 := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  rw [ν.σ_eq]
  refine val_vF hν hs _ x₀.left (fun k => ?_) (congrArg (·.left) hx)
  fin_cases k
  · exact (congrArg (_ ≫ ·) (Over.w ι[D.P.A])).trans (Over.w x₀)
  · exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w x₀)

theorem val_th (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x : N.A) : N.th x ∈ S := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  have h := congrArg S.valuation (ν.th_eq x)
  rw [map_mul, val_rig hν hs, _root_.mul_one] at h
  rw [← S.valuation_le_one_iff, h, S.valuation_le_one_iff]
  exact val_sF hν hs _ x₀.left (fun _ => (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w x₀))
    (congrArg (·.left) hx)

theorem val_psi (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (χ : D.X) (hχ : PsiUnitOn D χ Set.univ) : S.valuation (vF (D.psi χ) (jFK (R := R) C) ν.J) = 1 := by
  have e : jFK (R := R) C ≫ D.xK χ = spMap S.subtype ≫ s ≫ (D.c χ).left := by
    rw [← Category.assoc, hs]
    exact (Category.assoc _ _ _).symm
  have h1 := chart_int hν hs (s ≫ (D.c χ).left)
    ((Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (Over.w (D.c χ))).trans (Category.comp_id _)))
  rw [← e] at h1
  have h2 : s (IsLocalRing.closedPoint S) ∈ ((D.c χ).left ⁻¹ᵁ D.P.L.U (ν.J (jFK (R := R) C ≫ D.xK χ)) : (Sp R).Opens) :=
    h1 (Set.mem_univ _)
  obtain ⟨_, ⟨V, hV, rfl⟩, hy, hle⟩ := (Sp R).isBasis_affineOpens.exists_subset_of_mem_open h2 (TopologicalSpace.Opens.isOpen _)
  have h3 : ⊤ ≤ s ⁻¹ᵁ V := ((IsLocalRing.closedPoint_mem_iff (s ⁻¹ᵁ V)).1 hy).ge
  have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U
      (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) := fun y hy => Set.mem_iInter.2 fun _ => hle hy
  obtain ⟨r, hr, er⟩ := hχ (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) V hV (Set.subset_univ _) hle h
  have hs' : jFK (R := R) C ≫ jK R = spMap S.subtype ≫ s := hs.symm
  have h4 : ⊤ ≤ jFK (R := R) C ⁻¹ᵁ (jK R ⁻¹ᵁ V) := by
    change ⊤ ≤ (jFK (R := R) C ≫ jK R) ⁻¹ᵁ V
    rw [hs']
    exact fun q _ => h3 (Set.mem_univ (spMap S.subtype q))
  have a := valF_res' h h4 ((D.psi χ).s _).val
  rw [Scheme.Hom.app_eq_appLE] at er
  refine (congrArg S.valuation (a.symm.trans ((congrArg (valF _ _) er.symm).trans
    (valF_appLE' (jK R) V le_rfl h4 r)))).trans ?_
  exact (congrArg (fun q => S.valuation (valF q V r)) hs').trans (val_valF_unit s V h3 r hr)

theorem val_ψ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (χ : N.X) (hχ : PsiUnitOn D (ν.eX χ) Set.univ) : S.valuation ((N.ψ χ : C)) = 1 := by
  rw [ν.ψ_eq, map_mul, val_rig hν hs, val_psi hν hs _ hχ, _root_.mul_one]
end Geo

theorem integral_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∀ (N : NumD F) (ν : NumOf D F N), ν.Integral S → (∀ x y u, S.valuation (N.θ x y u : F) = 1) ∧ (∀ x, S.valuation (N.σ x : F) = 1) ∧ (∀ x, N.th x ∈ S) ∧ ((∀ y, PsiUnitOn D y Set.univ) → ∀ χ, S.valuation (N.ψ χ : F) = 1) := by
  intro R _ _ D F _ _ S hR N ν hν
  obtain ⟨s, hs⟩ := exists_base (R := R) (S := S) hR
  exact ⟨val_θ hν hs, val_σ hν hs, val_th hν hs, fun h χ => val_ψ hν hs χ (h _)⟩

end GlobalTheory.Ex.UnitVal
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.AbPartIso
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N N' : NumD F}

def HomF (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A) : Prop :=
  φ.hom ≫ fst _ _ = fst _ _ ∧ ∀ (Z : Over (Sp R)) (t : Z ⟶ TF (R := R) F) (x y : Z ⟶ D.P.A),
    lift t (x * y) ≫ φ.hom ≫ snd _ _ = (lift t x ≫ φ.hom ≫ snd _ _) * (lift t y ≫ φ.hom ≫ snd _ _)

abbrev BunIso (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A) : Type :=
  LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left)

def Carries (ν : NumOf D F N) (ν' : NumOf D' F N') (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A)
    (x : N.A) (x' : N'.A) : Prop :=
  lift (𝟙 _) (ν.eA x) ≫ φ.hom = lift (𝟙 _) (ν'.eA x')

def wVal (ν : NumOf D F N) (ν' : NumOf D' F N') {φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A} (w : BunIso φ)
    (f : N.A → N'.A) (x : N.A) : F :=
  valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _
    (w.s (fun _ => ν'.J (ν'.eA (f x)).left, fun _ => ν.J (ν.eA x).left)).val

def AllIso (P : ∀ {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N N' : NumD F} (_ : NumOf D F N) (_ : NumOf D' F N') {φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A},
    BunIso φ → (N.A → N'.A) → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A)
    (w : BunIso φ) (f : N.A → N'.A), HomF φ → w.IsGen → (∀ x, Carries ν ν' φ x (f x)) → P ν ν' w f

def TorsMap {O : Type} [CommRing O] (B B' : NumB O) (m : ℕ) (c : O) (ρ : B.A → B'.A) : Prop :=
  (∀ b b', b ^ m ^ 2 = 1 → b' ^ m ^ 2 = 1 →
    ρ (b * b') = ρ b * ρ b' ∧ B'.weil (m ^ 2) (ρ b) (ρ b') = B.weil (m ^ 2) b b') ∧
  ∀ b, b ^ m ^ 2 = 1 → ρ b ^ m ^ 2 = 1 ∧ B'.uth m (ρ b) 1 = c * B.uth m b 1

def IsFib (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (Q : PolAV (Sp F))
    (Φ : Q.A.left ⟶ D.P.A.left) : Prop :=
  IsGrpPullback Q.A D.P.A (TF (R := R) F).hom Φ ∧ LBIso Q.L (D.P.L.pull Φ) ∧ Q.g = D.P.g

theorem exists_isFib (hB : PolBaseChangeSt) (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    ∃ Q Φ, IsFib D F Q Φ := by
  obtain ⟨P', φ, hφ, hg, hm, ht⟩ := hB _ _ (TF (R := R) F).hom D.P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ht, hg⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

end GlobalTheory.Ex.AbPartIso
end
end

section

open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.AdicNormSum

open Filter Topology in
private lemma exists_norm_le_mul_of_mem_ideal_smul_fg {R C : Type} [CommRing R] [NormedField C]
    [IsUltrametricDist C] {_ : Module R C} (φ : R →+* C) (hφ : ∀ r, ‖φ r‖ ≤ 1)
    (hsmul : ∀ (r : R) (y : C), r • y = φ r * y) {N : Submodule R C} (hN : N.FG) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (J : Ideal R) (t : ℝ), 0 ≤ t → (∀ r ∈ J, ‖φ r‖ ≤ t) →
      ∀ y ∈ J • N, ‖y‖ ≤ t * M := by
  obtain ⟨G, rfl⟩ := hN
  have hbound : ∀ y ∈ Submodule.span R (G : Set C), ‖y‖ ≤ (G.sup fun g => ‖g‖₊ : NNReal) := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro g hg
      exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun g => ‖g‖₊) hg)
    · simp
    · intro a b _ _ ha hb
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    · intro a b _ hb
      rw [hsmul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hφ a)).trans hb
  refine ⟨(G.sup fun g => ‖g‖₊ : NNReal), NNReal.coe_nonneg _, ?_⟩
  intro J t ht hJ y hy
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr z hz
    rw [hsmul, norm_mul]
    exact mul_le_mul (hJ r hr) (hbound z hz) (norm_nonneg _) ht
  · intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

open Filter Topology in
private lemma exists_uniform_norm_bound_lt_one_of_fg {R C : Type} [CommRing R] [NormedField C]
    [IsUltrametricDist C] (φ : R →+* C) (hφ : ∀ r, ‖φ r‖ ≤ 1) {I : Ideal R} (hfg : I.FG)
    (hI : ∀ r ∈ I, ‖φ r‖ < 1) : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ r ∈ I, ‖φ r‖ ≤ c := by
  obtain ⟨G, rfl⟩ := hfg
  refine ⟨(G.sup fun g => ‖φ g‖₊ : NNReal), NNReal.coe_nonneg _, ?_, ?_⟩
  · have h : G.sup (fun g => ‖φ g‖₊) < 1 := by
      rw [Finset.sup_lt_iff (by simp)]
      intro g hg
      have hg' := hI g (Ideal.subset_span hg)
      exact_mod_cast hg'
    exact_mod_cast h
  · intro r hr
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hr
    · intro g hg
      exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun g => ‖φ g‖₊) hg)
    · simp
    · intro a b _ _ ha hb
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    · intro a b _ hb
      rw [smul_eq_mul, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hφ a)).trans hb

open Filter Topology in
private lemma hasSum_of_norm_sub_le_geometric {Ix E : Type} [NormedAddCommGroup E]
    {x : Ix → E} {s : E} {c M : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (h : ∀ n : ℕ, ∃ S : Finset Ix, ∀ T : Finset Ix, S ⊆ T → ‖s - ∑ i ∈ T, x i‖ ≤ c ^ n * M) :
    HasSum x s := by
  show Tendsto (fun T : Finset Ix => ∑ i ∈ T, x i) atTop (𝓝 s)
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hlim : Tendsto (fun n : ℕ => c ^ n * M) atTop (𝓝 (0 * M)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const M
  rw [zero_mul] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  obtain ⟨S, hS⟩ := h n
  refine Filter.eventually_atTop.2 ⟨S, fun T hT => ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact (hS T hT).trans_lt hn

open Filter Topology in
private lemma norm_le_pow_of_mem_ideal_pow {R C : Type} [CommRing R] [NormedField C]
    [IsUltrametricDist C] (φ : R →+* C) (hφ : ∀ r, ‖φ r‖ ≤ 1) {I : Ideal R} {c : ℝ}
    (hc0 : 0 ≤ c) (hI : ∀ r ∈ I, ‖φ r‖ ≤ c) : ∀ n : ℕ, ∀ r ∈ I ^ n, ‖φ r‖ ≤ c ^ n := by
  intro n
  induction n with
  | zero => intro r _; simpa using hφ r
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro a ha b hb
      rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih a ha) (hI b hb) (norm_nonneg _) (pow_nonneg hc0 n)
    · intro a b ha hb
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)


open Filter Topology in
theorem _root_.GlobalTheory.Ex.AdicNormSum.main : ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (I : Ideal R) (C : Type) [NormedField C] [IsUltrametricDist C]
    [Algebra (FractionRing R) C], _root_.GlobalTheory.Ex.CExt R I C → ∀ (Ix : Type) (x : Ix → C)
    (s : C), _root_.GlobalTheory.UT.SumF I C x s → HasSum x s := by
  intro R _ _ _ I C _ _ _ hC Ix x s hs
  obtain ⟨hle, hlt⟩ := hC
  letI : Module R C := Module.compHom C (algebraMap R (FractionRing R))
  have hs' : _root_.GlobalTheory.UT.SumI I x s := hs
  unfold _root_.GlobalTheory.UT.SumI at hs'
  obtain ⟨N, hNfg, -, -, hconv⟩ := hs'
  let φ : R →+* C := (algebraMap (FractionRing R) C).comp (algebraMap R (FractionRing R))
  have hφ : ∀ r, ‖φ r‖ ≤ 1 := hle
  obtain ⟨M, -, hM⟩ := exists_norm_le_mul_of_mem_ideal_smul_fg (N := N) φ hφ
    (fun r y => Algebra.smul_def (algebraMap R (FractionRing R) r) y) hNfg
  obtain ⟨c, hc0, hc1, hcI⟩ := exists_uniform_norm_bound_lt_one_of_fg φ hφ (IsNoetherian.noetherian I) hlt
  exact hasSum_of_norm_sub_le_geometric hc0 hc1 fun n => (hconv n).imp fun S hS T hT =>
    hM (I ^ n) (c ^ n) (pow_nonneg hc0 n) (norm_le_pow_of_mem_ideal_pow φ hφ hc0 hcI n) _ (hS T hT)

end GlobalTheory.Ex.AdicNormSum
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex.RootSum

def scaleForm {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) : N.Form n where
  be := (n : ℤ) • β.be
  symm y z := congrArg ((n : ℤ) * ·) (β.symm y z)
  pos y hy := mul_pos (Int.natCast_pos.2 hn) (β.pos y hy)
  dvd y z := by
    obtain ⟨a, ha⟩ := β.dvd y z
    exact ⟨k * a, by change (n : ℤ) * β.be y z = _; rw [ha]; ring⟩

def pullForm {O O' : Type} [CommRing O] [CommRing O'] {N₀ : NumD O} {N : NumD O'} {k : ℕ} (β : N.Form k)
    (e : N₀.X ≃+ N.X) (be₀ : LinearMap.BilinForm ℤ N₀.X) (h : ∀ y z, β.be (e y) (e z) = be₀ y z) : N₀.Form k where
  be := be₀
  symm y z := by rw [← h, ← h, β.symm]
  pos y hy := by rw [← h]; exact β.pos _ (fun h0 => hy (e.map_eq_zero_iff.1 h0))
  dvd y z := h y z ▸ β.dvd _ _

def idHom {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) (t u : Oˣ)
    (h : t ^ n = u) : NumD.Hom (RingHom.id O) (N.twist (scaleForm β n hn) t) (N.twist β u) where
  φ := MonoidHom.id _
  h _ := 1
  h_one := rfl
  θ_eq _ _ _ := by simp only [mul_one]; rfl
  σ_eq _ := by simp only [mul_one]; rfl
  lam := 1
  th_eq _ := by simp only [mul_one, Units.val_one, one_mul]; rfl
  e := AddEquiv.refl N.X
  c_eq _ := rfl
  ψ_eq (χ : N.X) := by
    rw [mul_one]
    change N.ψ χ * u ^ (β.be χ χ / 2) = N.ψ χ * t ^ ((n : ℤ) * β.be χ χ / 2)
    rw [Int.mul_ediv_assoc _ ((Dvd.intro _ rfl : (2 : ℤ) ∣ 2 * k).trans (β.dvd χ χ)), zpow_mul, zpow_natCast, h]

theorem idHom_rel {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) (t u r : Oˣ)
    (h : t ^ n = u) {i : ℕ} (a : ℕ) (hi : i * a = n) (hd : i ∣ n) (hr : t ^ a = r) (p₁ : N.QT i)
    (p : (N.twist β u).QT i) (hp : TwRel β u r p₁ p) :
    p.1.1.toAdd = (idHom β n hn t u h).e (N.twQ (scaleForm β n hn) t hd p₁).1.1.toAdd ∧
      (idHom β n hn t u h).Rel (N.twQ (scaleForm β n hn) t hd p₁).1.2 p.1.2 := by
  refine ⟨congrArg Multiplicative.toAdd hp.1, hp.2.1, fun (χ : N.X) => ?_⟩
  change p.1.2.s χ * 1 = p₁.1.2.s χ * t ^ ((n : ℤ) * β.be p₁.1.1.toAdd χ / i) * 1 * 1
  have hi0 : (i : ℤ) ≠ 0 := by
    rintro h0
    rw [Int.natCast_eq_zero.1 h0, zero_mul] at hi
    omega
  rw [hp.2.2, ← hi, Nat.cast_mul, mul_assoc (i : ℤ), Int.mul_ediv_cancel_left _ hi0, zpow_mul, zpow_natCast, hr,
    mul_one, mul_one]

theorem twist_tx_ev_eq_map_arc_root : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (t u rm rj : Cˣ) (m j : ℕ), Odd m → 0 < j → (t : C) = φ PowerSeries.X → t ^ j = rm → t ^ (m ^ 2) = rj → rm ^ (m ^ 2) = u → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (be₀ : LinearMap.BilinForm ℤ N₀.X) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = be₀ y z) → ∀ (p₀ : N₀.QT (m ^ 2)) (p₁ : N.QT (m ^ 2)) (p : (N.twist β u).QT (m ^ 2)), p₁.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p₁.1.2 → TwRel β u rm p₁ p → (N.twist β u).tx m p = I.lam * φ (N₀.arcTx (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀) ∧ ∀ (q₀ : N₀.QT j) (q₁ : N.QT j) (q : (N.twist β u).QT j), q₁.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q₁.1.2 → TwRel β u rj q₁ q → ∀ s : ℕ, (m : ℤ) ^ 2 * (((m ^ 2 * j : ℕ) : ℤ) * be₀ q₀.1.1.toAdd q₀.1.1.toAdd) ≤ s → (t : C) ^ s * (N.twist β u).ev m p q.1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀ q₀ s) := by
  intro O C _ _ _ _ φ h1 h2 t u rm rj m j hm hj ht hrm hrj hu N₀ N I k be₀ β hβ p₀ p₁ p hp1 hp2 hp
  have hn : 0 < m ^ 2 * j := Nat.mul_pos (pow_pos hm.pos 2) hj
  have htu : t ^ (m ^ 2 * j) = u := by rw [mul_comm, pow_mul, hrm, hu]
  have hd : m ^ 2 ∣ m ^ 2 * j := Dvd.intro _ rfl
  have key := GlobalTheory.T.twist_tx_ev_eq_map_arc_alt O C φ h1 h2 t ht N₀ N I (m ^ 2 * j) (scaleForm (pullForm β I.e be₀ hβ) _ hn)
    (scaleForm β _ hn) (fun y z => congrArg (((m ^ 2 * j : ℕ) : ℤ) * ·) (hβ y z)) m hd hm p₀ p₁ hp1 hp2
  have hr := idHom_rel β _ hn t u rm htu j rfl hd hrm p₁ p hp
  have tr := (NumD.hom_transport C C _ _ _ (idHom β _ hn t u htu)).2.2.2.2 m hm _ p hr.1 hr.2
  refine ⟨Eq.trans (tsum_congr fun χ => ?_) key.1, fun q₀ q₁ q hq1 hq2 hq s hs => ?_⟩
  · exact (tr χ).1.trans (one_mul _)
  · have hd' : j ∣ m ^ 2 * j := Dvd.intro_left _ rfl
    have hr' := idHom_rel β _ hn t u rj htu (m ^ 2) (mul_comm _ _) hd' hrj q₁ q hq
    refine Eq.trans (congrArg _ (tsum_congr fun χ => ?_)) (key.2 j hd' q₀ q₁ hj.ne' hq1 hq2 s hs)
    refine ((tr χ).2 _ _ hr'.2).trans ?_
    change ((1 * 1 ^ (m ^ 2) : Cˣ) : C) * _ = _
    rw [one_pow, mul_one, Units.val_one, one_mul]
    rfl

end GlobalTheory.Ex.RootSum
end
end
