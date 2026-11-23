module

public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle017
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.ringOfIntegersAction_injective_on_abelianScheme : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), 1 ≤ P.g → Function.Injective act.act := by
  first | exact @GlobalTheory.LamF.Faithful.act_injective | exact GlobalTheory.LamF.Faithful.act_injective | (intros; apply GlobalTheory.LamF.Faithful.act_injective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem etale_pullback_torsion {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] {n : ℕ} (hn : IsUnit (n : Γ(S', ⊤))) :
    Etale ((Over.pullback f).obj (torsion G n)).hom := by
  have hs : Smooth ((Over.pullback f).obj G).hom := inferInstanceAs (Smooth (pullback.snd G.hom f))
  have he : Etale ((Over.pullback f).map (mulN G n)).left := by
    rw [GrpTangent.pullback_map_mulN]
    exact GrpTangent.etale_mulN _ hn
  have h := ((IsPullback.of_hasPullback (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).map (Over.pullback f)).map
    (Over.forget S')
  have h1 : Etale ((Over.pullback f).map (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G))).left :=
    MorphismProperty.of_isPullback (P := @Etale) h he
  have h2 : Etale ((Over.pullback f).obj (𝟙_ (Over S))).hom :=
    inferInstanceAs (Etale (pullback.snd (𝟙 S) f))
  have e := Over.w ((Over.pullback f).map (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)))
  have h3 : Etale (((Over.pullback f).map (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G))).left ≫
    ((Over.pullback f).obj (𝟙_ (Over S))).hom) := inferInstance
  rw [e] at h3
  exact h3

theorem etale_pullback_tensor {S S' : Scheme.{0}} (f : S' ⟶ S) (A B : Over S)
    (hA : Etale ((Over.pullback f).obj A).hom) (hB : Etale ((Over.pullback f).obj B).hom) :
    Etale ((Over.pullback f).obj (A ⊗ B)).hom := by
  have h : Etale ((Over.pullback f).obj A ⊗ (Over.pullback f).obj B).hom :=
    inferInstanceAs (Etale (pullback.fst ((Over.pullback f).obj A).hom ((Over.pullback f).obj B).hom ≫
      ((Over.pullback f).obj A).hom))
  rw [← Over.w (Functor.Monoidal.μIso (Over.pullback f) A B).inv]
  have : IsIso (Functor.Monoidal.μIso (Over.pullback f) A B).inv.left :=
    inferInstanceAs (IsIso ((Over.forget S').map (Functor.Monoidal.μIso (Over.pullback f) A B).inv))
  infer_instance

theorem torsion_universal {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) :
    torsion.ι G n ^ n = 1 ∧ ∀ (T : Over S) (x : T ⟶ G), x ^ n = 1 → ∃ t : T ⟶ torsion G n, t ≫ torsion.ι G n = x := by
  refine ⟨?_, fun T x hx => ⟨pullback.lift x (toUnit T) ?_, pullback.lift_fst _ _ _⟩⟩
  · rw [← GrpTangent.comp_mulN]
    refine pullback.condition.trans ?_
    rw [Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  · rw [GrpTangent.comp_mulN, hx, Hom.one_def]

theorem exists_universal_torsion_pair :
    Out.Laws → ∀ (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] (X Y : Out.PolAV (Sp R)) (k : ℕ), 0 < k → ∃ (T₀ : Over (Sp R)) (x₀ : T₀ ⟶ X.A) (y₀ : T₀ ⟶ Y.A), x₀ ^ k = 1 ∧ y₀ ^ k = 1 ∧ (∀ (T : Over (Sp R)) (x : T ⟶ X.A) (y : T ⟶ Y.A), x ^ k = 1 → y ^ k = 1 → ∃ t : T ⟶ T₀, x = t ≫ x₀ ∧ y = t ≫ y₀) ∧ ∀ a b : Γ(T₀.left, ⊤), (∀ (k' : Type) [Field k'] [IsAlgClosed k'] [CharZero k'] (β : R →+* k') (t : Over.mk (spMap β) ⟶ T₀), t.left.appTop.hom a = t.left.appTop.hom b) → a = b := by
  intro hL R _ _ _ X Y k hk
  have fin : ∀ P : Out.PolAV (Sp R), IsFinite (torsion P.A k).hom ∧ Flat (torsion P.A k).hom := fun P => by
    obtain ⟨h1, h2, -⟩ := hL.mulN (Sp R) P k hk
    rw [Out.mulA, ← GrpTangent.mulN_eq_pow] at h1 h2
    exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) (GrpTangent.isPullback_torsion P.A k) h1,
      MorphismProperty.of_isPullback (P := @Flat) (GrpTangent.isPullback_torsion P.A k) h2⟩
  haveI : CharZero (FractionRing R) := algebraRat.charZero _
  have hu : IsUnit (k : Γ(Sp (FractionRing R), ⊤)) := by
    have : IsUnit (k : FractionRing R) := (Nat.cast_ne_zero.mpr hk.ne').isUnit
    simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
  have et : ∀ P : Out.PolAV (Sp R),
      Etale ((Over.pullback (spMap (algebraMap R (FractionRing R)))).obj (torsion P.A k)).hom := fun P => by
    have := P.isAb.comm
    have := P.isAb.smooth
    exact etale_pullback_torsion _ P.A hu
  obtain ⟨hX, uX⟩ := torsion_universal X.A k
  obtain ⟨hY, uY⟩ := torsion_universal Y.A k
  refine ⟨torsion X.A k ⊗ torsion Y.A k, fst _ _ ≫ torsion.ι X.A k, snd _ _ ≫ torsion.ι Y.A k, ?_, ?_, ?_, ?_⟩
  · rw [← comp_pow, hX, comp_one]
  · rw [← comp_pow, hY, comp_one]
  · intro T x y hx hy
    obtain ⟨s, hs⟩ := uX T x hx
    obtain ⟨t, ht⟩ := uY T y hy
    exact ⟨lift s t, by rw [lift_fst_assoc, hs], by rw [lift_snd_assoc, ht]⟩
  · obtain ⟨f1, f2⟩ := fin X
    obtain ⟨g1, g2⟩ := fin Y
    refine GlobalTheory.LamF.eq_of_geomPoints R (FractionRing R) _ ?_ ?_ (etale_pullback_tensor _ _ _ (et X) (et Y))
    · exact inferInstanceAs (IsFinite (pullback.fst (torsion X.A k).hom (torsion Y.A k).hom ≫ (torsion X.A k).hom))
    · exact inferInstanceAs (Flat (pullback.fst (torsion X.A k).hom (torsion Y.A k).hom ≫ (torsion X.A k).hom))

end GlobalTheory.LamF
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem existsUnique_hom_of_isGrpPullback :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G G₁ : Over S) (G' G₁' : Over S') [GrpObj G] [GrpObj G'] [GrpObj G₁] [GrpObj G₁'] (φ : G'.left ⟶ G.left) (φ₁ : G₁'.left ⟶ G₁.left), IsGrpPullback G' G f φ → IsGrpPullback G₁' G₁ f φ₁ → ∀ F : G ⟶ G₁, (∃! F' : G' ⟶ G₁', F'.left ≫ φ₁ = φ ≫ F.left) ∧ ∀ F' : G' ⟶ G₁', F'.left ≫ φ₁ = φ ≫ F.left → IsMonHom F → IsMonHom F' := by
  intro S S' f G G₁ G' G₁' _ _ _ _ φ φ₁ h h₁ F
  refine ⟨⟨Over.homMk (h₁.1.lift (φ ≫ F.left) G'.hom ?_) (h₁.1.lift_snd _ _ _),
    h₁.1.lift_fst _ _ _, fun F' hF' => ?_⟩, fun F' hF' hF => ?_⟩
  · rw [Category.assoc, Over.w F]
    exact h.1.w
  · apply Over.OverMorphism.ext
    apply h₁.1.hom_ext
    · exact hF'.trans (h₁.1.lift_fst _ _ _).symm
    · exact (Over.w F').trans (h₁.1.lift_snd _ _ _).symm
  · have hmul : ∀ (T : Over S') (x y : T ⟶ G'), (x * y) ≫ F' = (x ≫ F') * (y ≫ F') := by
      intro T x y
      obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h T
      obtain ⟨Φ₁, hΦ₁⟩ := exists_mulEquiv_points_of_isGrpPullback S S' f G₁ G₁' φ₁ h₁ T
      have key : ∀ z : T ⟶ G', Φ₁ (z ≫ F') = Φ z ≫ F := fun z => by
        apply Over.OverMorphism.ext
        rw [hΦ₁, Over.comp_left, Over.comp_left, hΦ, Category.assoc, Category.assoc, hF']
      apply Φ₁.injective
      rw [map_mul, key, key, key, map_mul, MonObj.mul_comp]
    have hone : (1 : 𝟙_ (Over S') ⟶ G') ≫ F' = 1 := by
      have h1 := hmul (𝟙_ (Over S')) 1 1
      rw [_root_.mul_one] at h1
      exact _root_.left_eq_mul.mp h1
    refine ⟨?_, ?_⟩
    · simpa [Hom.one_def] using hone
    · have h2 := hmul (G' ⊗ G') (fst G' G') (snd G' G')
      simpa [Hom.mul_def] using h2

end GlobalTheory.LamF
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.LieCombHom

variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G'] {n : ℕ}
  {v : Fin n → (epsR R ⟶ G)}

theorem isLieComb_zero [IsCommMonObj G] (hv : ∀ i, IsTangent (v i)) : IsLieComb 0 v 1 :=
  (LieComb.isLieComb_iff_tanExp _ _).2
    (congrArg Additive.toMul (map_zero (LieComb.combHom hv))).symm

theorem isLieComb_add [IsCommMonObj G] (hv : ∀ i, IsTangent (v i)) {c c' : Fin n → R}
    {w w' : epsR R ⟶ G} (h : IsLieComb c v w) (h' : IsLieComb c' v w') :
    IsLieComb (c + c') v (w * w') := by
  rw [LieComb.isLieComb_iff_tanExp] at h h' ⊢
  rw [h, h']
  exact (congrArg Additive.toMul (map_add (LieComb.combHom hv) c c')).symm

theorem isLieComb_nsmul [IsCommMonObj G] (hv : ∀ i, IsTangent (v i)) {c : Fin n → R}
    {w : epsR R ⟶ G} (h : IsLieComb c v w) (N : ℕ) : IsLieComb (N • c) v (w ^ N) := by
  induction N with
  | zero => rw [zero_smul, pow_zero]; exact isLieComb_zero hv
  | succ N ih => rw [succ_nsmul, pow_succ]; exact isLieComb_add hv ih h

theorem isTangent_comp (f : G ⟶ G') [IsMonHom f] {x : epsR R ⟶ G} (hx : IsTangent x) :
    IsTangent (x ≫ f) := by
  unfold IsTangent at hx ⊢
  rw [Over.comp_left, ← Category.assoc, hx, ← Over.comp_left, IsMonHom.one_hom]

theorem list_prod_comp (f : G ⟶ G') [IsMonHom f] (l : List (epsR R ⟶ G)) :
    l.prod ≫ f = (l.map (· ≫ f)).prod := by
  induction l with
  | nil => simpa using MonObj.one_comp f
  | cons a l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, MonObj.mul_comp, ih]

theorem isLieComb_comp (f : G ⟶ G') [IsMonHom f] {c : Fin n → R} {w : epsR R ⟶ G}
    (h : IsLieComb c v w) : IsLieComb c (fun i => v i ≫ f) (w ≫ f) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => u i ≫ f, fun i => ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left, hu i, Category.assoc]
  · rw [list_prod_comp, List.map_ofFn]
    rfl

theorem lieComb_add_pow_map : ∀ (R : Type) [CommRing R] (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] (n : ℕ) (v : Fin n → (epsR R ⟶ G)), (∀ i, IsTangent (v i)) → IsLieComb 0 v 1 ∧ (∀ c c' w w', IsLieComb c v w → IsLieComb c' v w' → IsLieComb (c + c') v (w * w')) ∧ (∀ c w (N : ℕ), IsLieComb c v w → IsLieComb (N • c) v (w ^ N)) ∧ ∀ f : G ⟶ G', IsMonHom f → (∀ i, IsTangent (v i ≫ f)) ∧ ∀ c w, IsLieComb c v w → IsLieComb c (fun i => v i ≫ f) (w ≫ f) := by
  intro R _ G G' _ _ _ n v hv
  exact ⟨isLieComb_zero hv, fun _ _ _ _ h h' => isLieComb_add hv h h',
    fun _ _ N h => isLieComb_nsmul hv h N,
    fun f _ => ⟨fun i => isTangent_comp f (hv i), fun _ _ h => isLieComb_comp f h⟩⟩

end GlobalTheory.LieCombHom
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.exists_universal_torsion_pair_polAV : Out.Laws → ∀ (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] (X Y : Out.PolAV (Sp R)) (k : ℕ), 0 < k → ∃ (T₀ : Over (Sp R)) (x₀ : T₀ ⟶ X.A) (y₀ : T₀ ⟶ Y.A), x₀ ^ k = 1 ∧ y₀ ^ k = 1 ∧ (∀ (T : Over (Sp R)) (x : T ⟶ X.A) (y : T ⟶ Y.A), x ^ k = 1 → y ^ k = 1 → ∃ t : T ⟶ T₀, x = t ≫ x₀ ∧ y = t ≫ y₀) ∧ ∀ a b : Γ(T₀.left, ⊤), (∀ (k' : Type) [Field k'] [IsAlgClosed k'] [CharZero k'] (β : R →+* k') (t : Over.mk (spMap β) ⟶ T₀), t.left.appTop.hom a = t.left.appTop.hom b) → a = b := by
  first | exact @GlobalTheory.LamF.exists_universal_torsion_pair | exact GlobalTheory.LamF.exists_universal_torsion_pair | (intros; apply GlobalTheory.LamF.exists_universal_torsion_pair <;> assumption)

end
end
