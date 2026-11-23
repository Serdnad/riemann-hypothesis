module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle236
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle230
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle187
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle079
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle203
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle235
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle108
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
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem tw_hopf_main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] [IsLocalRing O] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La), ∃ (U : ∀ n, (X.Γ n).G.left.Opens) (H : ∀ n, Subgroup (LevGrp La p n)), (∀ n, (X.Γ n).IsFinOpenSub (U n)) ∧ (∀ n (g : (X.Γ n).G.left), (X.Γ n).G.hom g = IsLocalRing.closedPoint O → g ∈ U n) ∧ (∀ n t, t ∈ H n ↔ ∀ z, ((X.Γ n).pt t).left z ∈ U n) ∧ (∀ n, IsHopfOrder ((X.Γ n).btOrder ⊤)) ∧ (∀ n, IsHopfOrder (resOrder (H n).subtype ((X.Γ n).btOrder ⊤))) ∧ (∀ n, (X.Γ n).btOrder ⊤ = indOrder (H n).subtype (resOrder (H n).subtype ((X.Γ n).btOrder ⊤))) ∧ (∀ n (a : La), lev p n a ∈ H n ↔ lev p (n + 1) (p • a) ∈ H (n + 1)) ∧ ∀ n (a : La), lev p n a ∈ H n → ∃ b : La, lev p (n + 1) b ∈ H (n + 1) ∧ lev p n b = lev p n a :=
  PositivityTheory.HtPt.Twhopf.tw_hopf

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.BT.RatKer

theorem exists_section_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (H : Type) [CommGroup H] (Γf : QFGroup R H) (A E : Over (Spec (CommRingCat.of R))) (a : A ⟶ Γf.G) (b : Γf.G ⟶ E) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ E), IsClosedImmersion a.left → IsPullback a (toUnit A) b e → ∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g := by
  intro R _ _ H _ Γf A E a b e ha hP g hg
  have hwa : Γf.G.hom (a.left g) = A.hom g := by
    rw [← Scheme.Hom.comp_apply, Over.w]
  obtain ⟨t, x, hx⟩ := Γf.11 (a.left g) (by rw [hwa]; exact hg)
  have hgen : (GlobalTheory.CompanionTheory.Ar.BT.genPt R).hom x = A.hom g := by
    rw [← Over.w (Γf.9 t), Scheme.Hom.comp_apply, hx, hwa]
  have hab := congrArg (fun φ => φ.left g) hP.w
  simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.toUnit_left] at hab
  have hpt : Γf.9 t ≫ b = toUnit (GlobalTheory.CompanionTheory.Ar.BT.genPt R) ≫ e := by
    apply Over.OverMorphism.ext
    apply GlobalTheory.CompanionTheory.Ar.BT.Tors.eq_of_same_point E.hom _ _ (Over.w _) (Over.w _) x x
    simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.toUnit_left]
    rw [hx, hab, hgen]
  refine ⟨hP.lift (Γf.9 t) (toUnit _) hpt, x, ?_⟩
  apply a.left.isClosedEmbedding.injective
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hP.lift_fst, hx]

end GlobalTheory.CompanionTheory.Ar.BT.RatKer
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.FinPart

theorem thick_apply (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ)
    (q : Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)))) :
    thick R (IsLocalRing.maximalIdeal R) e q = IsLocalRing.closedPoint R := by
  apply PrimeSpectrum.ext
  show Ideal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))) q.asIdeal =
    IsLocalRing.maximalIdeal R
  have hp : (Ideal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))) q.asIdeal).IsPrime :=
    q.isPrime.comap _
  have hle : IsLocalRing.maximalIdeal R ≤
      Ideal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))) q.asIdeal := by
    intro a ha
    have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1)) (a ^ (e + 1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow ha _)
    have h1 : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1)) a) ^ (e + 1) ∈ q.asIdeal := by
      rw [← map_pow, h0]
      exact zero_mem _
    exact q.isPrime.mem_of_pow_mem _ h1
  exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hp.ne_top hle).symm

section Points
variable {R : Type} [CommRing R] [IsDomain R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] {N : ℕ} {T : Type} [CommGroup T] {Γ : QFGroup R T} {i : Γ.G.left ⟶ G.left}

def unitIso (Y : Over (Spec (CommRingCat.of R))) : Over.mk (Y.hom ≫ 𝟙 _) ≅ Y :=
  Over.isoMk (Iso.refl _) (by simp)

theorem mul_left_eq (ht : Γ.IsTorsionAlong G (𝟙 _) N i) {Y : Over (Spec (CommRingCat.of R))}
    (y z : Y ⟶ Γ.G) (a b : Y ⟶ G) (ha : a.left = y.left ≫ i) (hb : b.left = z.left ≫ i) :
    (a * b).left = (y * z).left ≫ i := by
  have h := ht.mul Y y z ((unitIso Y).hom ≫ a) ((unitIso Y).hom ≫ b)
    (by simpa [unitIso] using ha) (by simpa [unitIso] using hb)
  rw [← MonObj.comp_mul] at h
  simpa [unitIso] using h

theorem pow_eq_one_iff (ht : Γ.IsTorsionAlong G (𝟙 _) N i) {Y : Over (Spec (CommRingCat.of R))}
    (g : Y ⟶ G) : g ^ N = 1 ↔ ∃ y : Y ⟶ Γ.G, y.left ≫ i = g.left := by
  have h := ht.kernel Y ((unitIso Y).hom ≫ g)
  have e : ((unitIso Y).hom ≫ g) ^ N = (unitIso Y).hom ≫ g ^ N := by
    rw [← GlobalTheory.CompanionTheory.Ar.BT.Tors.comp_pow_id, Category.assoc, GlobalTheory.CompanionTheory.Ar.BT.Tors.comp_pow_id]
  have e1 : (unitIso Y).hom ≫ g ^ N = 1 ↔ g ^ N = 1 := by
    constructor
    · intro h1
      have := congrArg (fun w => (unitIso Y).inv ≫ w) h1
      simpa [MonObj.comp_one] using this
    · intro h1
      rw [h1, MonObj.comp_one]
  rw [e, e1] at h
  rw [h]
  simp [unitIso]

end Points

section Pow
universe v₁ u₁
variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

theorem comp_pow_id' {B Y : C} [MonObj B] (y : Y ⟶ B) (n : ℕ) : y ≫ (𝟙 B) ^ n = y ^ n := by
  induction n with
  | zero => simp [Hom.one_def]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

end Pow

section Main
variable {R : Type} [CommRing R] [IsDomain R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] {N : ℕ} {T : Type} [CommGroup T] {Γ : QFGroup R T} {i : Γ.G.left ⟶ G.left}
  {H : Type} [CommGroup H] {Γf : QFGroup R H} {u : Γf.G ⟶ Γ.G} [IsMonHom u]

def finMap (ht : Γ.IsTorsionAlong G (𝟙 _) N i) (u : Γf.G ⟶ Γ.G) : Γf.G ⟶ G :=
  Over.homMk (u.left ≫ i) (by
    have h := ht.isOver
    have hu := Over.w u
    simp only [Category.comp_id] at h
    simp [h, hu])

theorem finMap_left (ht : Γ.IsTorsionAlong G (𝟙 _) N i) : (finMap ht u).left = u.left ≫ i := rfl

theorem comp_finMap_mul (ht : Γ.IsTorsionAlong G (𝟙 _) N i) {Y : Over (Spec (CommRingCat.of R))}
    (a b : Y ⟶ Γf.G) : (a * b) ≫ finMap ht u = (a ≫ finMap ht u) * (b ≫ finMap ht u) := by
  ext1
  have h := mul_left_eq ht (a ≫ u) (b ≫ u) (a ≫ finMap ht u) (b ≫ finMap ht u)
    (by simp [finMap_left]) (by simp [finMap_left])
  rw [h, ← MonObj.mul_comp]
  simp [finMap_left]

instance isMonHom_finMap (ht : Γ.IsTorsionAlong G (𝟙 _) N i) : IsMonHom (finMap ht u) := by
  have hone : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γf.G) ≫ finMap ht u = 1 := by
    have h := comp_finMap_mul (u := u) ht (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γf.G) 1
    rw [_root_.mul_one] at h
    exact left_eq_mul.1 h
  refine ⟨?_, ?_⟩
  · simpa [Hom.one_def] using hone
  · have h := comp_finMap_mul (u := u) ht (fst Γf.G Γf.G) (snd Γf.G Γf.G)
    rw [Hom.mul_def, Hom.mul_def] at h
    simpa using h

theorem mono_finMap (ht : Γ.IsTorsionAlong G (𝟙 _) N i) [IsOpenImmersion u.left] : Mono (finMap ht u) := by
  have hu : Mono u := by
    constructor
    intro Z a b h
    ext1
    rw [← cancel_mono u.left]
    simpa using congrArg (fun w => w.left) h
  constructor
  intro Z a b h
  rw [← cancel_mono u]
  apply ht.inj
  simpa [finMap_left] using congrArg (fun w => w.left) h

theorem finMap_pow (ht : Γ.IsTorsionAlong G (𝟙 _) N i) : finMap ht u ^ N = 1 :=
  (pow_eq_one_iff ht _).2 ⟨u, rfl⟩

theorem isPullback_thick (ht : Γ.IsTorsionAlong G (𝟙 _) N i) [IsLocalRing R] [IsOpenImmersion u.left]
    (hcl : ∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ Set.range u.left) (e : ℕ) :
    IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map (finMap ht u)) (toUnit _)
      ((𝟙 (thickObj R (IsLocalRing.maximalIdeal R) e G)) ^ N)
      η[thickObj R (IsLocalRing.maximalIdeal R) e G] := by
  set x := thick R (IsLocalRing.maximalIdeal R) e with hx
  letI : (Over.pullback x).Monoidal := (Over.instBraidedPullback (f := x)).toMonoidal
  have := mono_finMap (u := u) ht
  have hF : (𝟙 (thickObj R (IsLocalRing.maximalIdeal R) e G)) ^ N = (Over.pullback x).map ((𝟙 G) ^ N) :=
    (GlobalTheory.CompanionTheory.Ar.BT.Tors.map_pow_id (Over.pullback x) G N).symm
  refine GlobalTheory.Diag.isPullback_toUnit_of_lift _ ?_ ?_ ?_
  · rw [hF, ← Functor.map_comp, GlobalTheory.CompanionTheory.Ar.BT.Tors.comp_pow_id, finMap_pow, Functor.map_one, ← Hom.one_def]
  · intro Z a b h
    exact (cancel_mono _).1 h
  · intro Z t h
    have htN : t ^ N = 1 := by
      rw [← Hom.one_def] at h
      rw [← comp_pow_id', h]
    let g := GlobalTheory.CompanionTheory.Ar.BT.Tors.ofPull x G t
    have hg : GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull x G g = t := GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull_ofPull x G t
    have hgN : g ^ N = 1 := by
      apply (GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull_inj (x := x) (G := G))
      have h1 := map_pow (GlobalTheory.CompanionTheory.Ar.BT.Tors.toPullHom x G Z) g N
      have h2 : GlobalTheory.CompanionTheory.Ar.BT.Tors.toPullHom x G Z g = GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull x G g := rfl
      have h3 := map_one (GlobalTheory.CompanionTheory.Ar.BT.Tors.toPullHom x G Z)
      exact h1.trans ((by rw [h2, hg, htN]; exact h3.symm))
    obtain ⟨y, hy⟩ := (pow_eq_one_iff ht g).1 hgN
    have hrange : Set.range y.left ⊆ Set.range u.left := by
      rintro _ ⟨z, rfl⟩
      apply hcl
      rw [← Scheme.Hom.comp_apply, Over.w y]
      show x (Z.hom z) = _
      exact thick_apply R e _
    let l := IsOpenImmersion.lift u.left y.left hrange
    have hl : l ≫ u.left = y.left := IsOpenImmersion.lift_fac _ _ _
    let w : Over.mk (Z.hom ≫ x) ⟶ Γf.G := Over.homMk l (by
      have hu := Over.w u
      have hyw := Over.w y
      rw [← hu, ← Category.assoc, hl, hyw])
    refine ⟨GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull x Γf.G w, ?_⟩
    apply GlobalTheory.CompanionTheory.Ar.BT.Tors.hom_ext_pull
    have h1 : ((Over.pullback x).map (finMap ht u)).left ≫ pullback.fst G.hom x =
        pullback.fst _ x ≫ (finMap ht u).left := pullback.lift_fst _ _ _
    rw [Over.comp_left, Category.assoc, h1, ← Category.assoc, GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull_fst]
    show l ≫ u.left ≫ i = g.left
    rw [← Category.assoc, hl, hy]

end Main

theorem finite_part_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (N : ℕ) (T : Type) [CommGroup T] (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G (𝟙 _) N i → ∀ (H : Type) [CommGroup H] (Γf : QFGroup R H) (u : Γf.G ⟶ Γ.G) [IsMonHom u], IsOpenImmersion u.left → (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ Set.range u.left) → ∃ v : Γf.G ⟶ G, v.left = u.left ≫ i ∧ IsMonHom v ∧ Mono v ∧ ∀ e, IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map v) (toUnit _) ((𝟙 (thickObj R (IsLocalRing.maximalIdeal R) e G)) ^ N) η[thickObj R (IsLocalRing.maximalIdeal R) e G] := by
  intro R _ _ _ G _ _ N T _ Γ i ht H _ Γf u _ hu hcl
  have := hu
  exact ⟨finMap ht u, rfl, inferInstance, mono_finMap ht, isPullback_thick ht hcl⟩

end GlobalTheory.CompanionTheory.Ar.BT.FinPart
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.Tors

section Identity
variable {R : Type} [CommRing R]

def toIdMk (Y : Over (Spec (CommRingCat.of R))) : Y ⟶ Over.mk (Y.hom ≫ 𝟙 _) :=
  Over.homMk (𝟙 _) (by simp)

def ofIdMk (Y : Over (Spec (CommRingCat.of R))) : Over.mk (Y.hom ≫ 𝟙 _) ⟶ Y :=
  Over.homMk (𝟙 _) (by simp)

theorem ofIdMk_toIdMk (Y : Over (Spec (CommRingCat.of R))) : ofIdMk Y ≫ toIdMk Y = 𝟙 _ := by
  ext
  simp [ofIdMk, toIdMk]

end Identity

theorem exists_qfGroup_kernel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsSemiAbelian B → ∀ (N : ℕ), 1 ≤ N → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] [IsCommMonObj A] (j : A ⟶ B) [IsMonHom j], IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B] → (∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g) → ∃ (C : Type) (_ : CommGroup C) (Γ : QFGroup R C) (φ : Γ.G ≅ A), IsMonHom φ.hom ∧ Γ.IsTorsionAlong B (𝟙 _) N (φ.hom.left ≫ j.left) := by
  intro R _ _ _ _ B _ hB N hN A _ _ j _ hp hpt
  have := hB.smooth
  have := hB.separated
  have := hB.quasiCompact
  have := hB.comm
  have := GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian (Spec (CommRingCat.of R)) B hB N hN
  have := GlobalTheory.CompanionTheory.Ar.BT.locallyQuasiFinite_pow_semiAbelian (Spec (CommRingCat.of R)) B hB N hN
  have hm := mono_of_pullback hp
  obtain ⟨h1, h2, h3, h4, h5⟩ := kernel_props hp
  have := kernel_base_etale (genPt R).hom hp (isUnit_natCast_generic hN)
  haveI : IsReduced (genPt R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
  have hred := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd A.hom (genPt R).hom)
  have hv : ∀ {Y : Over (Spec (CommRingCat.of R))} (g : Over.mk (Y.hom ≫ 𝟙 _) ⟶ B) (y : Y ⟶ A),
      y.left ≫ j.left = g.left → y ≫ j = toIdMk Y ≫ g := fun {Y} g y h => by
    ext
    simpa [toIdMk] using h
  refine ⟨genPt R ⟶ A, inferInstance,
    { G := A, flat := h1, quasiFinite := h2, separated := h3, quasiCompact := h4, finPres := h5,
      pt := MonoidHom.id _, pt_inj := ?_, pt_onto := hpt, gen_reduced := hred }, Iso.refl _, ?_, ?_⟩
  · intro s t u v h
    exact Over.OverMorphism.ext (eq_of_same_point A.hom _ _ (Over.w _) (Over.w _) u v h)
  · show IsMonHom (𝟙 A)
    infer_instance
  · refine { isOver := ?_, mul := ?_, inj := ?_, kernel := ?_ }
    · show (𝟙 _ ≫ j.left) ≫ B.hom = A.hom ≫ 𝟙 _
      simpa using Over.w j
    · intro Y y z y₀ z₀ hy hz
      have hy' : y ≫ j = toIdMk Y ≫ y₀ := hv y₀ y (by rw [hy]; simp)
      have hz' : z ≫ j = toIdMk Y ≫ z₀ := hv z₀ z (by rw [hz]; simp)
      have e : (y * z) ≫ j = toIdMk Y ≫ (y₀ * z₀) := by
        rw [MonObj.mul_comp, hy', hz', MonObj.comp_mul]
      have e' := congrArg (fun w => w.left) e
      simpa [toIdMk] using e'.symm
    · intro Y y z h
      rw [← cancel_mono j]
      ext
      simpa using h
    · intro Y g
      constructor
      · intro h
        have h' : (toIdMk Y ≫ g) ^ N = 1 := by
          rw [← MonObj.comp_pow, h, MonObj.comp_one]
        obtain ⟨y, hy⟩ := lift_of_torsion hp _ h'
        refine ⟨y, ?_⟩
        have e := congrArg (fun w => w.left) hy
        simpa [toIdMk] using e
      · rintro ⟨y, hy⟩
        have e : y ≫ j = toIdMk Y ≫ g := hv g y (by rw [← hy]; simp)
        have h' : (toIdMk Y ≫ g) ^ N = 1 := by rw [← e]; exact torsion_of_comp hp y
        have e2 : ofIdMk Y ≫ toIdMk Y ≫ g = g := by
          rw [← Category.assoc, ofIdMk_toIdMk, Category.id_comp]
        rw [← e2, ← MonObj.comp_pow, h', MonObj.comp_one]

end GlobalTheory.CompanionTheory.Ar.BT.Tors
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.IntFrameSpan

theorem span_eq_eigSub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (y : Sp K ⟶ Xo.XF c) (z : Sp V ⟶ Y.X) (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (h₂ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre z)
    (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K) (g : ℕ) (ℓ : Fin g → Z.V) (ρK : 𝓞 E →+* Module.End K (Fin g → K))
    (MU : LieModel Xo.univ.t.G (under y) (Fin g → K)) (MY : LieModel Y.t.G (y ≫ Y.j) (Fin g → K))
    (T : SAB H (Sp V)) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y))
    (m' : SABMap tK T (spMap (algebraMap V K))) (n : ℕ) (σ : E →+* K) (σi : 𝓞 E →+* K) (b : Fin n → Fin g → K),
    spMap (algebraMap V K) ≫ z = y ≫ Y.j → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ ≤ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →
    (∀ (a : Z.Ω) (h : a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩), a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) →
    Z.M.lat.IsFrameAt ℓ ⟨_, h₂⟩ → Z.M.lat.IsFrameAt ℓ ⟨_, h₁⟩ → (∀ e, SameVec Y y (MU.pt e) (MY.pt e)) →
    (∀ x : Fin g → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, Z.M.ValAt (y ≫ Y.j) (comb ℓ x) (MY.pt (fun i => ψ (x i)))) →
    MU.IsActOf Xo.univ.t.act.act ρK → (∀ a : 𝓞 E, σi a = σ (a : E)) →
    IsIntFrame m m' σi (fun i => MU.pt (b i)) → LinearIndependent K b →
    Submodule.span V (Set.range b) = HT.eigSub ρK σ (stdLat V K g) := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z V K _ _ _ _ _ _ y z h₁ h₂ ψ g ℓ ρK MU MY T tK m m' n σ σi b hz hreg hint hfr₂ hfr₁ hsame hval hact hσ hif hli
  obtain ⟨ML, hML⟩ := (LieMove.main K Xo.X (under y) Xo.univ.t.G tK.G m.φ (Fin g → K) m.cart).1 MU
  obtain ⟨φ₁, hφ₁, htr⟩ := GlobalTheory.T.semiabelian_pullback_tangent_map E H D l Xo c O β Y K y tK m
  obtain ⟨σV, vV, hσV, hfr, hu⟩ := hif
  have hρ : ML.IsActOf tK.act.act ρK := by
    intro r e
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [hML, hact r e, Over.comp_left, Over.comp_left, Category.assoc, m.act r, ← Category.assoc, hML]
    · rw [Over.w (ML.pt (ρK r e)), Over.comp_left, Category.assoc, Over.w (tK.act.act r), Over.w (ML.pt e)]
  have hepi : Epi (CommRingCat.ofHom (algebraMap V K)) := IsLocalization.epi (nonZeroDivisors V) K
  have hmono : Mono (spMap (algebraMap V K)) := by
    exact Functor.map_mono Scheme.Spec (CommRingCat.ofHom (algebraMap V K)).op
  have hb : ∀ i, (ML.pt (b i)).left ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (vV i).left := by
    intro i
    obtain ⟨u, hu1, hu2⟩ := hu i
    have hw : u ≫ tK.G.hom = (ML.pt (b i)).left ≫ tK.G.hom := by
      rw [← cancel_mono (spMap (algebraMap V K)), Category.assoc, ← m'.cart.1.w, ← Category.assoc, hu2,
        Category.assoc, Over.w (vV i), Over.w (ML.pt (b i))]
      exact (LieTangent.spec_dual_alg _ |>.trans (by simp))
    have : u = (ML.pt (b i)).left := m.cart.1.hom_ext (hu1.trans (hML _).symm) hw
    rw [← this]; exact hu2
  have key := GlobalTheory.T.dvr_eigen_tangent_extension V K T.G tK.G m'.φ (𝓞 E) T.act tK.act g n ML ρK σV vV b m'.cart m'.act hρ hfr hb
  have cast : ∀ (x x' : Sp K ⟶ Y.X) (_ : x = x') (M : LieModel Y.t.G x' (Fin g → K)),
      ∃ MC : LieModel Y.t.G x (Fin g → K), ∀ e, (MC.pt e).left = (M.pt e).left := by
    rintro _ _ rfl M
    exact ⟨M, fun _ => rfl⟩
  obtain ⟨MC, hMC⟩ := cast _ _ hz MY
  have hfib := GlobalTheory.T.dvr_specialization_lie_lattice Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M V K (y ≫ Y.j) z h₁ h₂ ψ g ℓ MY MC hz hMC Z.gen hreg hint hfr₂ hval
  have hsm := Y.t.semi.smooth
  have h₁' : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z) := by
    have : Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z = y ≫ Y.j := hz
    rw [this]; exact h₁
  have hL : ∀ w, w ∈ stdLat V K g ↔ ∃ a : epsAt (𝟙 (Sp V)) ⟶ T.G, IsTanAt T.G (𝟙 _) a ∧
      (ML.pt w).left ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ a.left := by
    intro w
    have hA := GlobalTheory.T.semiabelian_extension_over_dvr V K Y.X Y.t.G T.G tK.G z m'.φ φ₁ Y.t.semi T.semi m'.cart (by rw [hz]; exact hφ₁) (ML.pt w) (ML.tan w)
    have hF := GlobalTheory.T.lie_lattice_eval_fraction_field Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M V z K (Fin g → K) MC Z.gen hsm h₂ h₁' w
    rw [hfib] at hF
    rw [hF, hA]
    have e : (ML.pt w).left ≫ φ₁ = (MC.pt w).left := by
      rw [hMC]; exact htr _ _ _ (hsame w) (hML w)
    rw [e]
  ext w
  rw [key w, ← hL w]
  show _ ↔ w ∈ stdLat V K g ⊓ (HT.eigSp ρK σ).restrictScalars V
  rw [Submodule.mem_inf]
  refine and_congr Iff.rfl ?_
  have : ∀ r, algebraMap V K (σV r) = σ (r : E) := fun r => by
    rw [← hσ r, ← hσV]; rfl
  simp [HT.eigSp, Submodule.mem_iInf, sub_eq_zero, this]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.IntFrameSpan
end

section

open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

theorem _root_.GlobalTheory.T.local_index_frame_log_det : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (v : FinitePlace L) (T : Matrix (Fin n) (Fin n) L), T.det ≠ 0 → gIdx (locAt v (frame T)).toAddSubgroup (locAt v (frame (1 : Matrix (Fin n) (Fin n) L))).toAddSubgroup = Real.log (v T.det) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_locAt_frame | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_locAt_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_locAt_frame <;> assumption)
end

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.semiabelian_adic_torsion_one : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] [IsLocalRing O] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La), ∃ (U : ∀ n, (X.Γ n).G.left.Opens) (H : ∀ n, Subgroup (LevGrp La p n)), (∀ n, (X.Γ n).IsFinOpenSub (U n)) ∧ (∀ n (g : (X.Γ n).G.left), (X.Γ n).G.hom g = IsLocalRing.closedPoint O → g ∈ U n) ∧ (∀ n t, t ∈ H n ↔ ∀ z, ((X.Γ n).pt t).left z ∈ U n) ∧ (∀ n, IsHopfOrder ((X.Γ n).btOrder ⊤)) ∧ (∀ n, IsHopfOrder (resOrder (H n).subtype ((X.Γ n).btOrder ⊤))) ∧ (∀ n, (X.Γ n).btOrder ⊤ = indOrder (H n).subtype (resOrder (H n).subtype ((X.Γ n).btOrder ⊤))) ∧ (∀ n (a : La), lev p n a ∈ H n ↔ lev p (n + 1) (p • a) ∈ H (n + 1)) ∧ ∀ n (a : La), lev p n a ∈ H n → ∃ b : La, lev p (n + 1) b ∈ H (n + 1) ∧ lev p n b = lev p n a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.tw_hopf_main | exact GlobalTheory.CompanionTheory.Ar.HT.tw_hopf_main | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.tw_hopf_main <;> assumption)

end
end
