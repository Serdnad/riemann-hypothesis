module

import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullCubicalOfIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SymmetricBundle

open Geo.Tor

theorem isSymmetric_of_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (sy : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hsy : sy.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sy (eSec G)) (LB.oneGen L.L)) : L.IsSymmetric := by
  apply GlobalTheory.isSymmetric_of_symmetry_generator <;> assumption

theorem gen_of_isSymmetric {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (h : L.IsSymmetric) :
    ∃ s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧
      LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec G)) (LB.oneGen L.L) := by
  obtain ⟨he, w, hw, hm⟩ := h
  have oi : eSec G ≫ (ι[G]).left = eSec G := he.trans (Category.id_comp _)
  have pg := (isGen_iff w).1 hw
  have pm := (maps_iff w (K := PUnit) (fun _ => eSec G) (fun _ => eSec G) (fun _ => 1) L.rig L.rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) he L.L j) (fun _ => rfl)).1 hm
  have m₀ : ∀ (j : Fin 2 → L.L.ι) (x : G.left), x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      (ι[G]).left x ∈ L.L.U (j 0) := fun j x hx => Set.mem_iInter.1 hx 0
  have m₁ : ∀ (j : Fin 2 → L.L.ι) (x : G.left), x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      x ∈ L.L.U (j 1) := fun j x hx => Set.mem_iInter.1 hx 1
  have le : ∀ j : Fin 2 → L.L.ι, LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j ≤
      (L.L.pull (ι[G]).left).U (fun _ => j 0) ⊓ L.L.U (j 1) := fun j x hx => ⟨mem_pull.2 (m₀ j x hx), m₁ j x hx⟩
  let s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]) :=
    ⟨fun j => res (le j) (w.s (fun _ => j 0, j 1))⟩
  have hs : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (j : Fin 2 → L.L.ι),
      f y ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      gm f y (LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j) (s.s j) = gw w f y (j 0) (j 1) :=
    fun Y f y j hj => gm_res f y (le j) hj _
  refine ⟨s, fun j j' => unit_ext fun x hx => ?_, corr_of_val L.isLB fun y J hJ => ?_⟩
  · refine ((gm_res (𝟙 G.left) x _ hx _).trans (hs _ (𝟙 G.left) x j hx.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linComb L.L _ _ (𝟙 _) x j j' hx.1 hx.2)
        ((gm_res (𝟙 G.left) x _ hx _).trans (hs _ (𝟙 G.left) x j' hx.2)))).symm)
    rw [pg _ (𝟙 _) x (j 0) (j' 0) (j 1) (j' 1) (m₀ _ _ hx.1) (m₀ _ _ hx.2) (m₁ _ _ hx.1) (m₁ _ _ hx.2),
      Fin.prod_univ_two]
    congr 1
    show _ = gm (𝟙 _ ≫ (ι[G]).left) x _ (L.L.g (j 0) (j' 0)) ^ (1 : ℤ) *
      gm (𝟙 _ ≫ 𝟙 _) x _ (L.L.g (j 1) (j' 1)) ^ (-1 : ℤ)
    rw [Category.comp_id, zpow_one, zpow_neg_one]
  · have ri : (𝟙 _ ≫ eSec G) ≫ (ι[G]).left = 𝟙 _ ≫ eSec G := by rw [Category.assoc, oi]
    have hq₀ : (𝟙 _ ≫ eSec G) y ∈ L.L.U (J (𝟙 _ ≫ eSec G)) := hJ _
    have hq₁ : (ι[G]).left ((𝟙 _ ≫ eSec G) y) ∈ L.L.U (J (𝟙 _ ≫ eSec G)) := by
      have := hJ ((𝟙 _ ≫ eSec G) ≫ (ι[G]).left)
      rw [congrArg J ri] at this
      exact this
    rw [val_pull hJ, val_one, val_of s (𝟙 _ ≫ eSec G) y J ![J (𝟙 _ ≫ eSec G), J (𝟙 _ ≫ eSec G)] (fun k => by
      fin_cases k
      · exact congrArg J ri
      · exact congrArg J (Category.comp_id _)), hs _ _ _ _ (Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [hq₁, hq₀])]
    have a := pm _ (𝟙 _) y (fun _ => J (𝟙 _ ≫ eSec G)) (fun _ => J (𝟙 _ ≫ eSec G)) (fun _ => hq₁) (fun _ => hq₀)
    rw [Category.comp_id, Fintype.prod_unique, zpow_one] at a
    exact mul_eq_right.1 a.symm

end SymmetricBundle

theorem isSymmetric_iff_exists_gen : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), L.IsSymmetric ↔ ∃ s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec G)) (LB.oneGen L.L) :=
  fun _ _ _ _ L => ⟨SymmetricBundle.gen_of_isSymmetric L,
    fun ⟨s, hs, hr⟩ => SymmetricBundle.isSymmetric_of_gen L s hs hr⟩

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem veryAmpleBy_pw_of_affine_loci : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (H : LB X) (n : ℕ) (t : Fin (n + 1) → LB.Sec H), H.IsLB → (⨆ i, nonzeroLocus (t i) = ⊤) → (∀ i, IsAffineOpen (nonzeroLocus (t i))) → ∃ d : ℕ, 1 ≤ d ∧ ∃ (n' : ℕ) (s : Fin (n' + 1) → LB.Sec (pw H d)), VeryAmpleBy f (pw H d) s := by
  intro R _ X f _ H n t hH hc ha
  have h : IsAmpleLB H :=
    isAmpleLB_of_cover hH le_rfl (fun i => secToPow (t i) 1)
      (by simp only [nonzeroLocus_secToPow _ le_rfl, hc])
      fun i => (nonzeroLocus_secToPow (t i) le_rfl).symm ▸ ha i
  have : IsProper (Over.mk f).hom := ‹IsProper f›
  exact (Unif.relAmple_iff_veryAmpleBy R (Over.mk f) H hH).1
    ((relAmple_iff_isAmpleLB_of_isAffine (Over.mk f) hH).2 h)

end GlobalTheory.AbLaw
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.locallyQuasiFinite_of_cubical_pow_iso_pull : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L) (r n : ℕ), n.Prime → (n : K) ≠ 0 → ¬ n ∣ r → (∀ x : baseOver _ ⟶ B, x ^ n = 1 → Triv (translDiff B L.L x) → x = 1) → ∀ (Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z) (H : LB Z.left), H.IsLB → LBIso (pw L.L r) (H.pull φ.left) → LocallyQuasiFinite φ.left := by
  first | exact @GlobalTheory.CubicalQuasiFinite.locallyQuasiFinite_of_pow_iso_pull | exact GlobalTheory.CubicalQuasiFinite.locallyQuasiFinite_of_pow_iso_pull | (intros; apply GlobalTheory.CubicalQuasiFinite.locallyQuasiFinite_of_pow_iso_pull <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace ArcObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sabMap_of_iso (hG : GlobalFnsSt) {S S' : Scheme.{0}} {t t' : SAB H S} {u u' : SAB H S'} {f : S' ⟶ S}
    (n : SABMap u t f) (n' : SABMap u' t' f) (hA : IsAbelianScheme u.G) (ψ : t.G ≅ t'.G) [IsMonHom ψ.hom]
    (hact : ∀ x, t.act.act x ≫ ψ.hom = ψ.hom ≫ t'.act.act x) (hL : LBIso t.PP.L (t'.PP.L.pull ψ.hom.left)) :
    ∃ m : SABMap u u' (𝟙 _), m.φ ≫ n'.φ = n.φ ≫ ψ.hom.left := by
  have c := n.cart.comp (isGrpPullback_of_iso ψ)
  rw [Category.comp_id] at c
  obtain ⟨α, hα, hφ⟩ := grpPullback_iso c n'.cart
  have ha : ∀ x, (u.act.act x).left ≫ α.hom.left = α.hom.left ≫ (u'.act.act x).left := fun x => by
    have e : (t.act.act x).left ≫ ψ.hom.left = ψ.hom.left ≫ (t'.act.act x).left := congrArg (fun q => q.left) (hact x)
    apply n'.cart.1.hom_ext
    · rw [Category.assoc, hφ, Category.assoc, n'.act, ← Category.assoc, n.act, ← Category.assoc, hφ, Category.assoc,
        Category.assoc, e]
    · simp only [Category.assoc, Over.w]
  have hb : LBIso u.PP.L (u'.PP.L.pull α.hom.left) := by
    obtain ⟨w, hw⟩ := hL
    obtain ⟨w₁, g₁, -⟩ := (isPullCubical_iff n.cm t.cub u.cub).1 n.lin
    obtain ⟨w₂, g₂, -⟩ := (isPullCubical_iff n'.cm t'.cub u'.cub).1 n'.lin
    have hw' := (isGen_iff w).1 hw
    obtain ⟨w₃, T⟩ := exists_comp t.PP.isLB w w₁ hw' g₁ t'.PP.isLB u.PP.isLB
    obtain ⟨w₄, g₄⟩ : ∃ w₄ : LB.Iso u.PP.L (t'.PP.L.pull (α.hom.left ≫ n'.cm.F)), PGen w₄ := by
      rw [hφ]; exact ⟨w₃, T.pgen_comp t.PP.isLB hw' g₁⟩
    obtain ⟨w₅, T'⟩ := exists_cancel t'.PP.isLB w₂ w₄ g₂ g₄ u'.PP.isLB u.PP.isLB
    exact ⟨w₅, (isGen_iff w₅).2 (T'.pgen_cancel t'.PP.isLB g₂ g₄)⟩
  exact ⟨⟨CubeMap.ofHom α.hom, isGrpPullback_of_iso α, rfl, ha,
    HeckePoint.isPullCubical_of_iso hG hA α.hom u.cub u'.cub hb⟩, hφ⟩

theorem exists_sab_fac {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (e : h = g ≫ f) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact ObjMaps.exists_sab_cancel m n

variable {D : Datum H} {l : Level H}

theorem objMap_eq (hS : SerreSt) {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {F : Type} [Field F]
    {s : S ⟶ Sp B} {s' : Sp F ⟶ Sp B} {o : Obj D l b s} {o₁ : Obj D l b s'} {y y' : Sp F ⟶ S} (e : y = y')
    (m : ObjMap o₁ o y) (m' : ObjMap o₁ o y') : m.toSABMap.φ = m'.toSABMap.φ := by
  subst e
  exact objMap_unique_of_field hS m m'

theorem point_eq (hL : Laws) {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O']
    {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'} {S : Scheme.{0}} {χ : S ⟶ Y.X}
    {χ' : S ⟶ Y'.X} {t t' : SAB H S} (m : SABMap t Y.t χ) (m' : SABMap t' Y'.t χ') (ψ : t.G ≅ t'.G) [IsMonHom ψ.hom]
    (hact : ∀ x, t.act.act x ≫ ψ.hom = ψ.hom ≫ t'.act.act x) (hb : LBIso t.PP.L (t'.PP.L.pull ψ.hom.left))
    {K : Type} [Field K] (j : Sp K ⟶ S) (y y' : Sp K ⟶ Xo.XF c) (hy : y ≫ Y.j = j ≫ χ) (hy' : y' ≫ Y'.j = j ≫ χ')
    (hs : y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _)
    (hlev : ∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G),
      ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) →
      ∀ g : Sp K ⟶ t.G.left, g ≫ t.G.hom = j → g ≫ m.φ = y ≫ σ.left ≫ Y.m.φ →
        g ≫ ψ.hom.left ≫ m'.φ = y' ≫ σ'.left ≫ Y'.m.φ) :
    y = y' ∧ ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left) (τ : T ⟶ Sp K),
      g ≫ t.G.hom = τ ≫ j → g₁ ≫ Y.oF.t.G.hom = τ ≫ y → g ≫ m.φ = g₁ ≫ Y.m.φ →
      g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom →
      g ≫ ψ.hom.left ≫ m'.φ = g₂ ≫ Y'.m.φ := by
  have hid : spMap (RingHom.id (KA l)) = 𝟙 _ := Spec.map_id _
  have hs' : y' ≫ pullback.fst _ _ ≫ Xo.s = y ≫ pullback.fst _ _ ≫ Xo.s := by
    rw [pullback.condition, reassoc_of% hs]
  obtain ⟨o, ⟨m₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ (y ≫ pullback.fst _ _ ≫ Xo.s) y
    rfl rfl (by rw [hid, Category.comp_id]) Y.oF
  obtain ⟨o', ⟨m₂⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ (y ≫ pullback.fst _ _ ≫ Xo.s) y'
    rfl rfl (by rw [hid, Category.comp_id, hs']) Y'.oF
  obtain ⟨k₁, e₁⟩ := ObjMaps.exists_sab_comp Y.m m₁.toSABMap
  obtain ⟨k₂, e₂⟩ := ObjMaps.exists_sab_comp Y'.m m₂.toSABMap
  obtain ⟨n, hn⟩ := exists_sab_fac m k₁ hy
  obtain ⟨n', hn'⟩ := exists_sab_fac m' k₂ hy'
  obtain ⟨ν, hν⟩ := exists_sabMap_of_iso hL.globalFns n n'
    ⟨inferInstance, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩ ψ hact hb
  have hνw : ν.φ ≫ o'.t.G.hom = o.t.G.hom := ν.cart.1.w.trans (Category.comp_id _)
  have hψ : n.φ ≫ ψ.hom.left ≫ m'.φ = ν.φ ≫ m₂.toSABMap.φ ≫ Y'.m.φ := by
    rw [← e₂, hn', reassoc_of% hν]
  have key : ∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G)
      (x : 𝟙_ (Over (Sp K)) ⟶ o.t.G) (x' : 𝟙_ (Over (Sp K)) ⟶ o'.t.G),
      ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) →
      x.left ≫ m₁.toSABMap.φ = y ≫ σ.left → x'.left ≫ m₂.toSABMap.φ = y' ≫ σ'.left →
      x.left ≫ ν.φ = 𝟙 _ ≫ x'.left := by
    intro σ σ' x x' h hx hx'
    have b : x.left ≫ o.t.G.hom = 𝟙 _ := Over.w x
    have b' : x'.left ≫ o'.t.G.hom = 𝟙 _ := Over.w x'
    have q := hlev σ σ' h (x.left ≫ n.φ) (by rw [Category.assoc, n.cart.1.w, reassoc_of% b])
      (by rw [Category.assoc, ← hn, e₁, reassoc_of% hx])
    rw [Category.id_comp]
    apply k₂.cart.1.hom_ext
    · show (_ ≫ _) ≫ k₂.φ = _ ≫ k₂.φ
      rw [e₂, Category.assoc, ← hψ, reassoc_of% hx', ← q, Category.assoc]
    · rw [Category.assoc, hνw, b, b']
  let ν' : ObjMap o o' (𝟙 _) :=
    ⟨ν, fun a => key _ _ _ _ (Or.inr ⟨a, rfl, rfl⟩) (m₁.eta a) (m₂.eta a),
      fun a => key _ _ _ _ (Or.inl ⟨a, rfl, rfl⟩) (m₁.etaA a) (m₂.etaA a)⟩
  obtain ⟨p₁, f₁⟩ := ObjComp.objMap_comp Y.m0 m₁
  obtain ⟨p₀, f₀⟩ := ObjComp.objMap_comp m₂ ν'
  obtain ⟨p₂, f₂⟩ := ObjComp.objMap_comp Y'.m0 p₀
  have hf := (Xo.rep _ _ inferInstance o).unique ⟨Category.assoc _ _ _, ⟨p₁⟩⟩
    ⟨by rw [Category.id_comp, Category.assoc, hs'], ⟨p₂⟩⟩
  have hp : m₁.toSABMap.φ ≫ Y.m0.toSABMap.φ = (ν.φ ≫ m₂.toSABMap.φ) ≫ Y'.m0.toSABMap.φ :=
    f₁.symm.trans ((objMap_eq hL.serre hf p₁ p₂).trans (f₂.trans (congrArg (· ≫ _) f₀)))
  rw [Category.id_comp] at hf
  obtain rfl : y = y' := pullback.hom_ext hf hs
  refine ⟨rfl, fun T g g₁ g₂ τ h₁ h₂ h₃ h₄ h₅ => ?_⟩
  obtain ⟨u, u₁, u₂⟩ : ∃ u : T ⟶ o.t.G.left, u ≫ m₁.toSABMap.φ = g₁ ∧ u ≫ o.t.G.hom = τ :=
    ⟨m₁.cart.1.lift g₁ τ h₂, m₁.cart.1.lift_fst _ _ _, m₁.cart.1.lift_snd _ _ _⟩
  have a₁ : u ≫ n.φ = g := by
    apply m.cart.1.hom_ext
    · show (_ ≫ _) ≫ m.φ = _ ≫ m.φ
      rw [Category.assoc, ← hn, e₁, reassoc_of% u₁, h₃]
    · rw [Category.assoc, n.cart.1.w, reassoc_of% u₂, h₁]
  have a₂ : u ≫ ν.φ ≫ m₂.toSABMap.φ = g₂ := by
    apply Y'.m0.cart.1.hom_ext
    · show (_ ≫ _) ≫ Y'.m0.toSABMap.φ = _ ≫ Y'.m0.toSABMap.φ
      rw [Category.assoc, ← hp, reassoc_of% u₁, h₄]
    · rw [Category.assoc, Category.assoc, m₂.cart.1.w, reassoc_of% hνw, reassoc_of% u₂, ← h₅, h₂]
  rw [← a₁, ← a₂, Category.assoc, hψ, Category.assoc, Category.assoc]

end ArcObj

end GlobalTheory
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isProper_and_relAmple_lPow :
    ∀ (F : Type) [CommRing F] (S : Scheme.{0}) (P : PolAV S) (t : Spec (CommRingCat.of F) ⟶ S) [IsLocalRing F] (N : ℕ), 1 ≤ N → IsProper (fst (Over.mk t) P.A).left ∧ RelAmple (S := Spec (CommRingCat.of F)) (Over.mk (fst (Over.mk t) P.A).left) (LPow P.A P.L (N : ℤ) (Over.mk t)) := by
  intro F _ S P t _ N hN
  have hP := P.isAb.proper
  have H : IsPullback (snd (Over.mk t) P.A).left (fst (Over.mk t) P.A).left P.A.hom t :=
    (IsPullback.of_hasPullback t P.A.hom).flip
  have hp : IsProper (fst (Over.mk t) P.A).left := MorphismProperty.of_isPullback (P := @IsProper) H hP
  refine ⟨hp, ?_⟩
  have hp' : IsProper (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left).hom := hp
  have hL := LB.isLB_pull P.isLB (snd (Over.mk t) P.A).left
  have hM : (LPow P.A P.L (N : ℤ) (Over.mk t)).IsLB := LB.isLB_linComb P.isLB _ _
  have h₁ := (relAmple_iff_isAmpleLB_of_isAffine
    (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left) hL).1
    (AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample H)
  refine (relAmple_iff_isAmpleLB_of_isAffine
    (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left) hM).2
    (((isAmpleLB_pow_iff hL hN).2 h₁).of_lbIso hM ?_)
  exact LBIso.chartPull (CoprimeTorsion.chartPullLPow P.A P.L (Over.mk t) N) (chartPullPowPull P.L _ N)
    (lbIso_refl (isLB_lbPow P.isLB N))

end GlobalTheory
end
end
