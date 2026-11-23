module

import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle095
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle050
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

@[expose] public section

section

noncomputable section

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace CubTransport

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

section Down

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem exists_down_units {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  apply GlobalTheory.PrimDown.exists_down_all <;> assumption

theorem exists_pmaps {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ PMaps w φ' φ ε a t h := by
  have key : ∀ (ψ : K → (Y' ⟶ X)) (_ : ∀ k, φ' k ≫ F = ψ k) (t₀ : LB.Gen (LB.LinComb L ψ ε)), t₀.IsGen →
      ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L ψ p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L ψ p) (t₀.s p) = pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
    intro ψ hψ t₀ h₀
    obtain rfl : (fun k => φ' k ≫ F) = ψ := funext hψ
    exact exists_down_units hw hL hL' t₀ h₀
  obtain ⟨a, ha, hv⟩ := key _ hc (LB.pullGen L φ ε t h) (pullGen_isGen _ _ _ _ ht h)
  refine ⟨a, ha, fun Z r z p q hp hq => ?_⟩
  have hm : r z ∈ LB.wchart L (fun k => h ≫ φ k) p := Set.mem_iInter.2 fun k => by
    show φ k (h (r z)) ∈ L.U (p k)
    rw [pt_eq hc]; exact hp k
  refine Eq.trans ?_ (hv Z r z p q hm (Set.mem_iInter.2 hq))
  exact ((gm_res r z _ hm _).trans (gm_pull r h z (LB.wchart L φ p)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) _)).symm

theorem val_pmaps {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)}
    (H : PMaps w φ' φ ε a t h) (r : Z ⟶ Y') {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t (r ≫ h) z J = (∏ k, gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k) * val a r z J' := by
  rw [val_of t (r ≫ h) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hc])]
  exact H Z r z _ _ (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))

end Down

theorem isCub_of_twist {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] {θ : A → A → A → U}
    (hθ : IsCub θ) (β : A' →* A) (Ω : A' → U) {θ' : A' → A' → A' → U}
    (h : ∀ a b c, θ (β a) (β b) (β c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b *
      Ω c * (Ω 1)⁻¹ * θ' a b c) : IsCub θ' := by
  refine ⟨fun x y => ?_, fun x y z => ?_, fun x y z => ?_, fun x x' x'' y => ?_⟩
  · have e := h 1 x y
    rw [map_one, hθ.face] at e
    simp only [_root_.one_mul] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hθ.s01 (β x) (β y) (β z)
    rw [h, h, mul_comm y x] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  · have e := hθ.s12 (β x) (β y) (β z)
    rw [h, h, mul_comm z y, mul_right_comm x z y] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  · have e := hθ.coc (β x) (β x') (β x'') (β y)
    rw [← map_mul, ← map_mul, h, h, h, h] at e
    simp only [← _root_.mul_assoc x] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'

section Cub

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}

def thV (t : LB.Gen (Theta G L.L)) {T : Over S} (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι) (x x' y : T ⟶ G) :
    (T.left.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t (lift x (lift x' y)).left z J

theorem val_thV (t : LB.Gen (Theta G L.L)) {T : Over S} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι}
    (hJ : Good L.L z J) (x x' y : T ⟶ G) :
    val (LB.pullGen L.L (thφ G (x3 G)) thε t (lift x (lift x' y)).left) (𝟙 T.left) z J = thV t z J x x' y := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [Category.id_comp]; rfl

theorem val_id_thV (t : LB.Gen (Theta G L.L)) {z : (G3 G).left} {J : ((G3 G).left ⟶ G.left) → L.L.ι} :
    val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t (𝟙 (G3 G).left) z J = thV t z J (x3 G 0) (x3 G 1) (x3 G 2) := by
  have e : lift (x3 G 0) (lift (x3 G 1) (x3 G 2)) = 𝟙 (G3 G) := by
    ext <;> simp [x3]
  rw [thV, e]; rfl

def cubicalOfVal (t : LB.Gen (Theta G L.L)) (ht : t.IsGen)
    (h : ∀ (T : Over S) (z : T.left) (J), Good L.L z J → IsCub (thV t z J)) : CubicalStr G L where
  t := t
  isGen := ht
  face i := corr_of_val L.isLB fun y J hJ => by
    refine Eq.trans ?_ (val_one _).symm
    have C := h (G2 G) y J hJ
    fin_cases i
    · exact (val_thV t hJ _ _ _).trans (C.face _ _)
    · exact (val_thV t hJ _ _ _).trans (C.face₂ _ _)
    · exact (val_thV t hJ _ _ _).trans (C.face₃ _ _)
  cubeSymmetric_swap_first := corr_of_val L.isLB fun y J hJ =>
    (val_id_thV t).trans (((h (G3 G) y J hJ).s01 _ _ _).trans (val_thV t hJ _ _ _).symm)
  cubeSymmetric_swap_last := corr_of_val L.isLB fun y J hJ =>
    (val_id_thV t).trans (((h (G3 G) y J hJ).s12 _ _ _).trans (val_thV t hJ _ _ _).symm)
  cocycle := corr_of_val L.isLB fun y J hJ =>
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_thV t hJ _ _ _) (val_thV t hJ _ _ _))).trans
      (((h (G4 G) y J hJ).coc _ _ _ _).trans
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_thV t hJ _ _ _) (val_thV t hJ _ _ _))).symm)

end Cub

end CubTransport


open CubTransport ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem cubical_symmetry_transport : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (Ψ : G'.left ⟶ G.left) (hgp : Geo.Tor.IsGrpPullback G' G f Ψ) (L : RigLB G) (L' : RigLB G') (wL : LB.Iso L'.L (L.L.pull Ψ)) (he : eSec G' ≫ Ψ = f ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf Ψ f he L.L L.rig) → ∀ (c : CubicalStr G L) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen → LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec G)) (LB.oneGen L.L) → ∃ (c' : CubicalStr G' L') (s' : LB.Gen (LB.LinComb L'.L (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1])), s'.IsGen ∧ LB.Gen.Corr L'.L _ _ _ _ (LB.pullGen L'.L _ _ s' (eSec G')) (LB.oneGen L'.L) ∧ Geo.Tor.PMaps wL (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (Geo.Tor.cubeMapOf hgp).F3 ∧ Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] s' s Ψ := by
  intro S S' f G _ _ G' _ _ Ψ hgp L L' wL he hw _ c s hs hs1
  have hw' := (isGen_iff wL).1 hw
  have good : ∀ {Z : Scheme.{0}} (z : Z), ∃ J, Good L.L z J := fun {Z} z => by
    choose I hI using fun χ : Z ⟶ G.left => exists_chart L.isLB (χ z)
    exact ⟨I, hI⟩
  have hc : ∀ I : thK.{0}, thφ G' (x3 G') I ≫ Ψ = (cubeMapOf hgp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf hgp).psum_comm I.down
  obtain ⟨t', ht', Ht⟩ := exists_pmaps hw' L.isLB L'.isLB (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε)
    (cubeMapOf hgp).F3 hc c.t c.isGen
  have hι : (ι[G']).left ≫ Ψ = Ψ ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom hgp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ Ψ) ≫ _ = _
    rw [Category.id_comp]
  have hc₂ : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ Ψ = Ψ ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s', hs', Hs⟩ := exists_pmaps hw' L.isLB L'.isLB Ψ hc₂ s hs
  refine ⟨cubicalOfVal t' ht' fun T z J' hJ' => ?_, s', hs', corr_of_val L'.isLB fun y J' hJ' => ?_, Ht, Hs⟩
  · obtain ⟨J, hJ⟩ := good z
    refine isCub_of_twist (isCub_cubV c (T := Over.mk (T.hom ≫ f)) hJ) (pushHom hgp T)
      (fun x => gw wL x.left z (J (x.left ≫ Ψ)) (J' x.left)) fun a b d => ?_
    have q : (lift a (lift b d)).left ≫ (cubeMapOf hgp).F3 =
        (lift (pushHom hgp T a) (lift (pushHom hgp T b) (pushHom hgp T d))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    have e := val_pmaps hc Ht (lift a (lift b d)).left hJ hJ'
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b d (fun q => gw wL q z (J (q ≫ Ψ)) (J' q))) rfl)
  · obtain ⟨J, hJ⟩ := good y
    have e := val_pmaps hc₂ Hs (eSec G') hJ hJ'
    have e₁ : val s (eSec G' ≫ Ψ) y J = 1 := by
      rw [he]
      exact (val_pull hJ s (eSec G) f).symm.trans ((val_corr hJ hs1 f).trans (val_one _))
    have e₂ : eSec G' ≫ (ι[G']).left = eSec G' := by
      rw [eSec, ← Over.comp_left, GrpObj.one_inv]
    rw [e₁, Fin.prod_univ_two] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₂, Category.comp_id, zpow_one, zpow_neg,
      mul_inv_cancel, _root_.one_mul] at e
    refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [Category.id_comp]
    exact e.symm

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CubeFree

section General
variable {X Y : Scheme.{0}} {L : LB X}

theorem gs_g_single (φ : Y ⟶ X) (n : ℤ) (j j' : Fin 1 → L.ι) (y : Y)
    (h : y ∈ LB.wchart L (fun _ : Fin 1 => φ) j) (h' : y ∈ LB.wchart L (fun _ : Fin 1 => φ) j') :
    (trF (L := L) (fun _ : Fin 1 => φ) (fun _ => n) (𝟙 Y) y j j').val =
      gs (𝟙 Y ≫ φ) y (L.U (j 0) ⊓ L.U (j' 0)) ((pw L n).g (j 0) (j' 0)).val := by
  have hm : (𝟙 Y ≫ φ) y ∈ L.U (j 0) ⊓ L.U (j' 0) := ⟨Set.mem_iInter.1 h 0, Set.mem_iInter.1 h' 0⟩
  refine Eq.trans ?_ (gs_unit _ y _ hm _).symm
  rw [trF, Fin.prod_univ_one]
  exact congrArg Units.val (map_zpow _ _ n).symm

theorem unitAt_of_pw {n : ℤ} (s : LB.Sec (pw L n)) (φ : Y ⟶ X) (y : Y) (i : L.ι)
    (h : φ y ∈ X.basicOpen (s.f i)) : UnitAt L (K := Fin 1) (fun _ => φ) (fun _ => n) y := by
  have l : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ L.U (j 0) :=
    fun j => LB.wchart_le L _ j 0
  have v : ∀ (j : Fin 1 → L.ι) (z : Y), z ∈ LB.wchart L (fun _ : Fin 1 => φ) j →
      gs (𝟙 Y) z _ ((Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))) =
        gs (𝟙 Y ≫ φ) z (L.U (j 0)) (s.f (j 0)) := fun j z hj =>
    (gs_res _ z _ hj _).trans (gs_pull _ φ z _ (l j hj) _)
  let s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => n)) :=
    { f := fun j => (Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))
      compat := fun j j' => fn_ext fun z hz => by
        have hm : (𝟙 Y ≫ φ) z ∈ L.U (j 0) ⊓ L.U (j' 0) := ⟨l j hz.1, l j' hz.2⟩
        refine ((gs_res (𝟙 Y) z _ hz _).trans (v j z hz.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
          (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) z _ hz _).trans
            ((congrArg Units.val (gm_linComb L _ _ (𝟙 Y) z j j' hz.1 hz.2)).trans
              (gs_g_single φ n j j' z hz.1 hz.2))) ((gs_res (𝟙 Y) z _ hz _).trans (v j' z hz.2)))).symm)
        exact (gs_res _ z _ hm _).symm.trans ((congrArg (gs _ z _) (s.compat (j 0) (j' 0))).trans
          ((gs_mul _ z _ hm _ _).trans (congrArg _ (gs_res _ z _ hm _)))) }
  refine ⟨s', fun J hJ => isUnit_sval s' (𝟙 Y) y hJ (fun _ => i) ?_⟩
  have hi : y ∈ LB.wchart L (fun _ : Fin 1 => φ) (fun _ => i) :=
    Set.mem_iInter.2 fun _ => X.basicOpen_le _ h
  change y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (l fun _ => i)).op).hom ((φ.app _).hom (s.f i)))
  rw [Scheme.basicOpen_res]
  exact ⟨hi, (SetLike.ext_iff.1 (Scheme.preimage_basicOpen φ (s.f i)) y).1 h⟩

theorem exists_sec_of_unitAt (hL : L.IsLB) {n : ℤ} {x : X}
    (h : UnitAt L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => n) x) :
    ∃ t : LB.Sec (pw L n), x ∈ nonzeroLocus t := by
  apply GlobalTheory.SquareGenerated.exists_sec_pw <;> assumption

theorem unitAt_of_triv (hL : L.IsLB) {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} {ε : I → ℤ}
    (h : Triv (LB.LinComb L φ ε)) {Y' : Scheme.{0}} (e : Y' ⟶ Y) (k : ℕ) (y : Y') :
    UnitAt L (fun i => e ≫ φ i) (fun i => k * ε i) y := by
  obtain ⟨t, ht⟩ := h
  refine UnitAt.congr hL ?_ ⟨powSec (I := Fin k) fun _ => pullSec (genSec t ht) e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_smul, natCast_zsmul]
  · rw [sval_powSec _ _ _ hJ]
    refine IsUnit.prod_univ_iff.2 fun _ => ?_
    rw [sval_pullSec _ _ _ _ hJ, sval_genSec _ _ _ _ hJ]
    exact Units.isUnit _

end General

theorem exists_cover_nonzeroLocus : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L) (k : ℕ) (s : LB.Sec (pw L.L k)), (∃ j, s.f j ≠ 0) → ∃ (n : ℕ) (t : Fin (n + 1) → LB.Sec (pw L.L (2 * k : ℕ))), ⨆ i, nonzeroLocus (t i) = ⊤ := by
  intro K _ _ B _ _ hB L c k s ⟨j, hj⟩
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  let T : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 _)
  have : IsIntegral (T ⊗ B).left :=
    GeometricallyIntegral.geometrically_isIntegral (𝟙 _) _ _ (IsPullback.of_hasPullback (𝟙 _) B.hom).flip
  have : IsIntegral B.left :=
    GeometricallyIntegral.geometrically_isIntegral (f := B.hom) (𝟙 _) _ _ (IsPullback.id_horiz B.hom)
  let q : B ⟶ T := Over.homMk B.hom (Category.comp_id _)
  let e : B ⟶ T ⊗ B := lift q (𝟙 B)
  have he : e ≫ snd T B = 𝟙 B := lift_snd _ _
  have hD : ((((snd T B).left ⁻¹ᵁ B.left.basicOpen (s.f j)) : (T ⊗ B).left.Opens) : Set (T ⊗ B).left).Nonempty := by
    obtain ⟨d, hd⟩ : ((B.left.basicOpen (s.f j) : B.left.Opens) : Set B.left).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
    refine ⟨e.left d, ?_⟩
    show (snd T B).left (e.left d) ∈ B.left.basicOpen (s.f j)
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, he]
    exact hd
  have key : ∀ (x : T ⟶ B) (p : T.left), ∃ t : LB.Sec (pw L.L (2 * k : ℕ)), x.left p ∈ nonzeroLocus t := by
    intro x p
    have hq : x ≫ q = 𝟙 T := Over.OverMorphism.ext (Over.w x)
    have good : ∀ a : T ⟶ B, (ptSecT B (a * x)).left p ∈ (snd T B).left ⁻¹ᵁ B.left.basicOpen (s.f j) →
        UnitAt L.L (K := Fin 1) (fun _ => e.left ≫ (translPt B a).left) (fun _ => (k : ℤ)) (x.left p) := by
      intro a ha
      refine unitAt_of_pw s _ _ j ?_
      have E : x ≫ e ≫ translPt B a = ptSecT B (a * x) ≫ snd T B := by
        simp [e, ptSecT, NoBasePoint.translPt_eq, MonObj.comp_mul, reassoc_of% hq]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, E]
      exact ha
    obtain ⟨a, h₁, h₂⟩ := NoBasePoint.exists_two_points (𝟙 _) _ hD x x
    have sq := unitAt_of_triv L.isLB (Square.triv_square c a a⁻¹) e.left k (x.left p)
    have e1 : translPt B (1 : T ⟶ B) = snd _ _ := by
      rw [NoBasePoint.translPt_eq, MonObj.comp_one, _root_.one_mul]
    have e2 : e.left ≫ (snd T B).left = 𝟙 _ := by rw [← Over.comp_left, he]; rfl
    refine exists_sec_of_unitAt L.isLB (UnitAt.congr L.isLB (formEq_of_add fun U _ hh => ?_)
      (((good a (h₁ p)).mul (good a⁻¹ (h₂ p))).mul sq))
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one, Fin.sum_univ_four,
      Matrix.cons_val, _root_.mul_inv_cancel]
    rw [e1, e2]
    push_cast
    module
  have top : ⨆ t : LB.Sec (pw L.L (2 * k : ℕ)), nonzeroLocus t = ⊤ := by
    have : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
    by_contra h
    have hne : ((⨆ t : LB.Sec (pw L.L (2 * k : ℕ)), nonzeroLocus t : B.left.Opens) : Set B.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h' => h (SetLike.coe_injective h')
    obtain ⟨z, hz, hc⟩ := nonempty_inter_closedPoints hne
      (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed
    obtain ⟨t, ht⟩ := key (Over.homMk (pointOfClosedPoint B.hom z hc) (pointOfClosedPoint_comp B.hom z hc))
      (IsLocalRing.closedPoint K)
    exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨t,
      (congrArg (· ∈ nonzeroLocus t) (pointOfClosedPoint_apply B.hom z hc _)).mp ht⟩)
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun t : LB.Sec (pw L.L (2 * k : ℕ)) => (nonzeroLocus t : Set B.left)) (fun t => (nonzeroLocus t).isOpen)
    (fun z _ => by
      have : z ∈ (⨆ t : LB.Sec (pw L.L (2 * k : ℕ)), nonzeroLocus t) := by rw [top]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 this))
  refine ⟨F.card, Fin.cons (secZero _) (fun i => (F.equivFin.symm i).1), top_unique fun z _ => ?_⟩
  obtain ⟨t, ht, hz⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ z))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨(F.equivFin ⟨t, ht⟩).succ, ?_⟩
  rw [Fin.cons_succ, Equiv.symm_apply_apply]
  exact hz

end GlobalTheory.CubeFree
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbLaw

theorem cechLB_exactAt_of_dim_lt :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (Y : Scheme.{0}) [IsIntegral Y] (f : Y ⟶ Spec (CommRingCat.of K)) (g : ℕ) (M : LB Y), SmoothOfRelativeDimension g f → IsProjBy f → IsSeparated f → M.IsLB → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ n, g < n → (cechLB f M D).ExactAt n := by
  intro K _ _ Y _ f g M hf hp hs hM κ _ _ D hD hc n hn
  obtain ⟨E, hE, hEc⟩ := GlobalTheory.AffineCover.exists_cover_of_isProjBy K Y f g hf hp
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_cechLB_homology_equiv_of_affine_covers K Y f M κ D (Fin (g + 1)) E hM hs hD hc hE hEc n
  have hz : IsZero ((cechLB f M E).X n) := isZero_cechLB_X f M E (by simpa using hn)
  have hE0 : IsZero ((cechLB f M E).homology n) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (HomologicalComplex.ExactAt.of_isZero hz)
  have : Subsingleton ((cechLB f M E).homology n) := ModuleCat.isZero_iff_subsingleton.1 hE0
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (ModuleCat.isZero_iff_subsingleton.2 e.toEquiv.subsingleton)

end GlobalTheory.AbLaw
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open LBGerm

theorem IsAmpleLB.exists_sec_succ {X : Scheme.{0}} {L : LB X} (h : IsAmpleLB L) (x : X) :
    ∃ n, 1 ≤ n ∧ ∃ (a : (lbPow L n).Sec) (b : (lbPow L (n + 1)).Sec), x ∈ nonzeroLocus a ∧ x ∈ nonzeroLocus b := by
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  have hL := h.isLB
  obtain ⟨i, hi⟩ := exists_chart hL x
  obtain ⟨n, hn, s, hs, hr, -⟩ := h.exists_affine_le hi
  have le : ∀ J : PUnit → L.ι, nonzeroLocus s ⊓ powChart L J ≤ L.U (J PUnit.unit) ⊓ L.U i :=
    fun J y hy => ⟨mem_powChart.1 hy.2, hr hy.1⟩
  have hg : ∀ (J : PUnit → L.ι) (y : X), y ∈ nonzeroLocus s ⊓ powChart L J →
      gs (𝟙 X) y _ (resG X (le J) (L.g (J PUnit.unit) i).val) =
        (gm (𝟙 X) y (L.U (J PUnit.unit) ⊓ L.U i) (L.g (J PUnit.unit) i)).val := fun J y hy =>
    (gs_res (𝟙 X) y _ hy _).trans (gs_unit (𝟙 X) y _ (le J hy) _)
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul (m := 1) hL s (fun J => resG X (le J) (L.g (J PUnit.unit) i).val)
    (mem_secOn_of_germ (M := lbPow L 1) _ fun y J J' h hJ hJ' => by
      rw [gm_lbPow_g 1 (𝟙 X) y J J' hJ hJ', pow_one]
      refine (hg J y ⟨h, hJ⟩).trans (Eq.trans ?_ (congrArg _ (hg J' y ⟨h, hJ'⟩)).symm)
      rw [← Units.val_mul, gm_cocycle hL (𝟙 X) y (mem_powChart.1 hJ) (mem_powChart.1 hJ') (hr h)])
  obtain ⟨u, hu⟩ := hN (N + 1) (Nat.le_succ N)
  refine ⟨n * (N + 1), Nat.mul_pos hn (Nat.succ_pos N), secPow s (N + 1), secCast (Nat.add_comm _ _) u, ?_, ?_⟩
  · rwa [nonzeroLocus_secPow s (Nat.succ_pos N)]
  · have hJ : x ∈ powChart L (fun _ => i) := mem_powChart.2 hi
    have hy : x ∈ nonzeroLocus s ⊓ powChart L (fun _ => i) := ⟨hs, hJ⟩
    have e := congrArg (gs (𝟙 X) x _) (hu fun _ => i)
    rw [gs_res _ x _ hy, gs_mul _ x _ hy, gs_pow _ x _ hy, gs_res _ x _ hy, hg _ x hy] at e
    rw [nonzeroLocus_secCast, mem_nonzeroLocus_iff_powFn u hJ, e]
    exact (((mem_nonzeroLocus_iff_powFn s hJ).1 hs).pow _).mul (Units.isUnit _)

theorem exists_sec_succ_of_relAmple : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] (L : LB X.left), L.IsLB → RelAmple X L → ∀ x : X.left, ∃ (n : ℕ) (_ : 1 ≤ n) (a : H0 L n) (b : H0 L (n + 1)), x ∈ nonzeroLocus a ∧ x ∈ nonzeroLocus b := by
  intro R _ X _ L hL hA x
  obtain ⟨n, hn, a, b, ha, hb⟩ := (isAmpleLB_of_relAmple_of_isAffine X hL hA).exists_sec_succ x
  obtain ⟨a', ha', -⟩ := exists_sec_oneTerm L (K' := Fin 1) (e' := ((n : ℕ) : ℤ)) rfl a
  obtain ⟨b', hb', -⟩ := exists_sec_oneTerm L (K' := Fin 1) (e' := ((n + 1 : ℕ) : ℤ)) rfl b
  exact ⟨n, hn, a', b', ha'.ge ha, hb'.ge hb⟩

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.uniformisation_trivialisations_correspond : GlobalFnsSt → SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → U.ExpBij 1 → U'.ExpBij 1 → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ.hom.left)), (w.IsGen ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL')) → (IsMonHom Φ.hom ∧ Geo.Tor.PMaps w (K := PUnit) (fun _ => eSec D'.toPre.P.A) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D'.toPre.rig D.toPre.rig (𝟙 _)) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, ((∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x)) ∧ ∀ e : ℕ, ((U'.gt e).pG.left ≫ Φ.hom.left = (𝟙 _) ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ Φ.hom.left = (𝟙 _) ≫ D.toPre.Oφ (U.gt e).pG (xe x) κ) ∧ Geo.Tor.PMaps w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (xe x)) (𝟙 _))) → ∀ x, Geo.Tor.PMaps w (K := PUnit) (fun _ => D'.toPre.xK x) (fun _ => D.toPre.xK (xe x)) (fun _ => -1) (D'.toPre.psi x) (D.toPre.psi (xe x)) (𝟙 _) := by
  first | exact @GlobalTheory.unifPre_psi_correspond | exact GlobalTheory.unifPre_psi_correspond | (intros; apply GlobalTheory.unifPre_psi_correspond <;> assumption)
end
