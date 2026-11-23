module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle060
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle209
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HermitianLattice
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelLocalizationAtPrime
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle172
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle207
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle208
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.CubIso

section Local
variable {X Y Z : Scheme.{0}} {A B : LB X}

def isoGerm (w : LB.Iso A B) (f : Y ⟶ X) (y : Y) (j : B.ι) (k : A.ι) : (Y.presheaf.stalk y)ˣ :=
  gm f y (B.U j ⊓ A.U k) (w.s (j, k))

theorem isoGerm_trans {w : LB.Iso A B} (hw : w.IsGen) (f : Y ⟶ X) (y : Y) {j j' : B.ι} {k k' : A.ι}
    (hj : f y ∈ B.U j) (hj' : f y ∈ B.U j') (hk : f y ∈ A.U k) (hk' : f y ∈ A.U k') :
    isoGerm w f y j k = gm f y _ (B.g j j') * (gm f y _ (A.g k k'))⁻¹ * isoGerm w f y j' k' := by
  have hm : f y ∈ B.U j ⊓ A.U k ⊓ (B.U j' ⊓ A.U k') := ⟨⟨hj, hk⟩, hj', hk'⟩
  have h := congrArg (gm f y (B.U j ⊓ A.U k ⊓ (B.U j' ⊓ A.U k'))) (hw (j, k) (j', k'))
  have e : gm f y (B.U j ⊓ A.U k ⊓ (B.U j' ⊓ A.U k')) ((LB.div B A).g (j, k) (j', k')) =
      gm f y _ (B.g j j') * (gm f y _ (A.g k k'))⁻¹ := by
    show gm f y _ (res _ (B.g j j') * (res _ (A.g k k'))⁻¹) = _
    rw [map_mul, map_inv, gm_res f y _ hm, gm_res f y _ hm]
  exact (gm_res f y _ hm _).symm.trans (h.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) e (gm_res f y _ hm _))))

variable {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem prod_isoGerm_trans {w : LB.Iso A B} (hw : w.IsGen) (r : Z ⟶ Y) (z : Z) {p p' : K → B.ι} {q q' : K → A.ι}
    (hp : r z ∈ LB.wchart B φ p) (hp' : r z ∈ LB.wchart B φ p') (hq : r z ∈ LB.wchart A φ q)
    (hq' : r z ∈ LB.wchart A φ q') :
    ∏ k, isoGerm w (r ≫ φ k) z (p k) (q k) ^ ε k =
      trF (L := B) φ ε r z p p' * (trF (L := A) φ ε r z q q')⁻¹ * ∏ k, isoGerm w (r ≫ φ k) z (p' k) (q' k) ^ ε k := by
  rw [trF, trF, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [isoGerm_trans hw (r ≫ φ k) z (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k)
    (Set.mem_iInter.1 hq' k), mul_zpow, mul_zpow, _root_.inv_zpow]

theorem exists_ratio (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : w.IsGen) {a : LB.Gen (LB.LinComb A φ ε)}
    {b : LB.Gen (LB.LinComb B φ ε)} (ha : a.IsGen) (hb : b.IsGen) :
    ∃ v : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → B.ι) (q : K → A.ι),
      r z ∈ LB.wchart B φ p → r z ∈ LB.wchart A φ q →
      gm r z (LB.wchart B φ p) (b.s p) = gm r z ⊤ v * (∏ k, isoGerm w (r ≫ φ k) z (p k) (q k) ^ ε k) *
        gm r z (LB.wchart A φ q) (a.s q) := by
  let Wc : (K → B.ι) × (K → A.ι) → Y.Opens := fun P => LB.wchart B φ P.1 ⊓ LB.wchart A φ P.2
  have le : ∀ P k, Wc P ≤ φ k ⁻¹ᵁ (B.U (P.1 k) ⊓ A.U (P.2 k)) := fun P k =>
    le_inf (inf_le_left.trans (LB.wchart_le B φ P.1 k)) (inf_le_right.trans (LB.wchart_le A φ P.2 k))
  let I : ∀ P, Γ(Y, Wc P)ˣ := fun P => res (inf_le_left : Wc P ≤ LB.wchart B φ P.1) (b.s P.1) *
    (res (inf_le_right : Wc P ≤ LB.wchart A φ P.2) (a.s P.2))⁻¹ *
    (∏ k, res (le P k) (pullU (φ k) _ (w.s (P.1 k, P.2 k))) ^ ε k)⁻¹
  have hI : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) P, r z ∈ Wc P → gm r z (Wc P) (I P) =
      gm r z (LB.wchart B φ P.1) (b.s P.1) * (gm r z (LB.wchart A φ P.2) (a.s P.2))⁻¹ *
        (∏ k, isoGerm w (r ≫ φ k) z (P.1 k) (P.2 k) ^ ε k)⁻¹ := by
    intro Z r z P hz
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv _ _ ).trans (congrArg _ (gm_res r z _ hz _))))) ((map_inv _ _).trans (congrArg _ ?_)))
    refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
    exact (gm_res r z (le P k) hz _).trans (gm_pull r (φ k) z _ (le P k hz) _)
  obtain ⟨v, hv⟩ := glue_unit ⊤ Wc (fun _ => le_top) (fun x _ => by
      choose p hp using fun k => exists_chart hB (φ k x)
      choose q hq using fun k => exists_chart hA (φ k x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(p, q), Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩) I (fun P Q x hx => by
      rw [hI _ _ x P hx.1, hI _ _ x Q hx.2, gen_trans hb (𝟙 Y) x hx.1.1 hx.2.1, gen_trans ha (𝟙 Y) x hx.1.2 hx.2.2,
        prod_isoGerm_trans hw (𝟙 Y) x hx.1.1 hx.2.1 hx.1.2 hx.2.2]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨v, fun Z r z p q hp hq => ?_⟩
  have hz : r z ∈ Wc (p, q) := ⟨hp, hq⟩
  have e := (gm_res r z (le_top : Wc (p, q) ≤ ⊤) hz v).symm.trans ((congrArg (gm r z (Wc (p, q))) (hv (p, q))).trans
    (hI Z r z (p, q) hz))
  rw [e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem appTop_eq_one (r : Z ⟶ Y) (v : Γ(Y, ⊤)ˣ) (h : ∀ z, gm r z ⊤ v = 1) : r.appTop.hom v.val = 1 := by
  have e : Units.map r.appTop.hom.toMonoidHom v = 1 :=
    unit_ext fun z _ => by rw [← gm_top r z v, h z, map_one]
  exact congrArg Units.val e

end Local

section Cube
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L₁ L₂ : RigLB G}

theorem exists_cube_ratio {w : LB.Iso L₁.L L₂.L} (hw : w.IsGen) (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂) :
    ∃ v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ, ∀ (T : Over S) (z : T.left) (J₁ : (T.left ⟶ G.left) → L₁.L.ι)
      (J₂ : (T.left ⟶ G.left) → L₂.L.ι), Good L₁.L z J₁ → Good L₂.L z J₂ →
      ∀ (W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ), (∀ x, W x = isoGerm w x.left z (J₂ x.left) (J₁ x.left)) →
      ∀ a b d : T ⟶ G, cubV c₂ z J₂ a b d * W (a * b) * W (a * d) * W (b * d) * W 1 =
        gm (lift a (lift b d)).left z ⊤ v * (W (a * b * d) * W a * W b * W d) * cubV c₁ z J₁ a b d := by
  obtain ⟨v, hv⟩ := exists_ratio (φ := thφ G (x3 G)) (ε := thε) (a := c₁.t) (b := c₂.t) L₁.isLB L₂.isLB hw
    c₁.isGen c₂.isGen
  refine ⟨v, fun T z J₁ J₂ h₁ h₂ W hW a b d => ?_⟩
  have e := hv T.left (lift a (lift b d)).left z (fun I => J₂ ((lift a (lift b d)).left ≫ thφ G (x3 G) I))
    (fun I => J₁ ((lift a (lift b d)).left ≫ thφ G (x3 G) I)) (h₂.mem _ _) (h₁.mem _ _)
  have f := prod_cub a b d (fun q => isoGerm w q z (J₂ q) (J₁ q))
  have e' : cubV c₂ z J₂ a b d = gm (lift a (lift b d)).left z ⊤ v *
      (∏ I : thK.{0}, isoGerm w ((lift a (lift b d)).left ≫ thφ G (x3 G) I) z
        (J₂ ((lift a (lift b d)).left ≫ thφ G (x3 G) I)) (J₁ ((lift a (lift b d)).left ≫ thφ G (x3 G) I)) ^ thε I) *
      cubV c₁ z J₁ a b d := e
  rw [e', f, hW, hW, hW, hW, hW, hW, hW, hW]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem cube_ratio_faces {w : LB.Iso L₁.L L₂.L} (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂)
    {v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ}
    (hv : ∀ (T : Over S) (z : T.left) (J₁ : (T.left ⟶ G.left) → L₁.L.ι)
      (J₂ : (T.left ⟶ G.left) → L₂.L.ι), Good L₁.L z J₁ → Good L₂.L z J₂ →
      ∀ (W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ), (∀ x, W x = isoGerm w x.left z (J₂ x.left) (J₁ x.left)) →
      ∀ a b d : T ⟶ G, cubV c₂ z J₂ a b d * W (a * b) * W (a * d) * W (b * d) * W 1 =
        gm (lift a (lift b d)).left z ⊤ v * (W (a * b * d) * W a * W b * W d) * cubV c₁ z J₁ a b d)
    (T : Over S) (x y : T ⟶ G) :
    (lift (1 : T ⟶ G) (lift x y)).left.appTop.hom v.val = 1 ∧
      (lift x (lift (1 : T ⟶ G) y)).left.appTop.hom v.val = 1 ∧
      (lift x (lift y (1 : T ⟶ G))).left.appTop.hom v.val = 1 := by
  refine ⟨appTop_eq_one _ v fun z => ?_, appTop_eq_one _ v fun z => ?_, appTop_eq_one _ v fun z => ?_⟩
  all_goals
    obtain ⟨J₁, h₁⟩ := exists_good_pt L₁.isLB z
    obtain ⟨J₂, h₂⟩ := exists_good_pt L₂.isLB z
  · have e := hv T z J₁ J₂ h₁ h₂ _ (fun _ => rfl) 1 x y
    rw [(isCub_cubV c₁ (T := T) h₁).face x y, (isCub_cubV c₂ (T := T) h₂).face x y] at e
    simp only [_root_.one_mul, _root_.mul_one] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hv T z J₁ J₂ h₁ h₂ _ (fun _ => rfl) x 1 y
    rw [(isCub_cubV c₁ (T := T) h₁).face₂ x y, (isCub_cubV c₂ (T := T) h₂).face₂ x y] at e
    simp only [_root_.one_mul, _root_.mul_one] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hv T z J₁ J₂ h₁ h₂ _ (fun _ => rfl) x y 1
    rw [(isCub_cubV c₁ (T := T) h₁).face₃ x y, (isCub_cubV c₂ (T := T) h₂).face₃ x y] at e
    simp only [_root_.one_mul, _root_.mul_one] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'

end Cube

theorem cubWeil_of_lbIso : ∀ (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → TorusExtension G → ∀ (L₁ L₂ : RigLB G) (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂), LBIso L₁.L L₂.L → ∀ (N : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ G) (ζ : Γ(Sp ℂ, ⊤)ˣ), CubWeil c₁ N x y ζ → CubWeil c₂ N x y ζ := by
  intro G _ _ hs te L₁ L₂ c₁ c₂ hiso N x y ζ h
  obtain ⟨w, hw⟩ := hiso
  obtain ⟨v, hv⟩ := exists_cube_ratio hw c₁ c₂
  have hone := GlobalTheory.T.cubical_triple_trivial ℂ G hs te v (cube_ratio_faces c₁ c₂ hv)
  refine ⟨h.1, h.2.1, fun z J₂ h₂ => ?_⟩
  obtain ⟨J₁, h₁⟩ := exists_good_pt L₁.isLB z
  let W : (𝟙_ (Over (Sp ℂ)) ⟶ G) → _ := fun a => isoGerm w a.left z (J₂ a.left) (J₁ a.left)
  refine cubN_ratio_twist (MonoidHom.id _) W (fun a b d => ?_) h.1 h.2.1 (h.2.2 z J₁ h₁)
  have e := hv _ z J₁ J₂ h₁ h₂ W (fun _ => rfl) a b d
  have g : gm (lift a (lift b d)).left z ⊤ v = 1 := by
    rw [gm_top]
    have : Units.map (lift a (lift b d)).left.appTop.hom.toMonoidHom v = 1 := Units.ext (hone a b d)
    rw [this, map_one]
  rw [g, _root_.one_mul] at e
  exact e

end GlobalTheory.CompanionTheory.Ar.CubIso
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.group_points_equiv_common_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S₁ S₂ V : Scheme.{0}) (t₁ : SAB H S₁) (t₂ : SAB H S₂) (tV : SAB H V) (f₁ : V ⟶ S₁) (f₂ : V ⟶ S₂) (m₁ : SABMap tV t₁ f₁) (m₂ : SABMap tV t₂ f₂) (x : Sp ℂ ⟶ V) (y₁ : Sp ℂ ⟶ S₁) (y₂ : Sp ℂ ⟶ S₂), x ≫ f₁ = y₁ → x ≫ f₂ = y₂ → ∃ Φ : (Over.mk y₂ ⟶ t₂.G) ≃ (Over.mk y₁ ⟶ t₁.G), (∀ q q', Φ (q * q') = Φ q * Φ q') ∧ (∀ q, ∃ w : Sp ℂ ⟶ tV.G.left, w ≫ tV.G.hom = x ∧ w ≫ m₂.φ = q.left ∧ w ≫ m₁.φ = (Φ q).left) ∧ ∀ (N : ℕ) (q q' : Over.mk y₂ ⟶ t₂.G) (ζ : (Γ(Sp ℂ, ⊤))ˣ), GlobalTheory.UU.CubWeil t₁.cub N (Φ q) (Φ q') ζ → GlobalTheory.UU.CubWeil t₂.cub N q q' ζ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.MarkFibre.exists_fibre_equiv | exact GlobalTheory.CompanionTheory.Ar.MarkFibre.exists_fibre_equiv | (intros; apply GlobalTheory.CompanionTheory.Ar.MarkFibre.exists_fibre_equiv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.lie_model_localization_at_prime : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L]
    (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra (𝓞 L) A]
    [IsLocalization.AtPrime A 𝔭] [Algebra A L] [IsScalarTower (𝓞 L) A L] (z : Sp (𝓞 L) ⟶ X)
    (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier) (f : Module.Dual Ω Li)
    (h : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) A) ≫ z)), IsCptGen ξ →
    (∀ e ∈ M.lat ⟨_, h⟩, f e ∈ regAt ξ ⟨_, h⟩) →
    (∀ h' : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z), ∀ e ∈ M.lat ⟨_, h'⟩, f e ∈ regAt ξ ⟨_, h'⟩) →
    ∃ g : B.carrier →ₗ[𝓞 L] A,
      (∀ (x : B.carrier) (e : Li) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G) (u : L),
        M.ValAt _ e v → (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left) →
        ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (f e) u → algebraMap A L (g x) = u) ∧
      ∀ (e : Li) (u : A), e ∈ M.lat ⟨_, h⟩ → ValAt ξ (spMap (algebraMap (𝓞 L) A) ≫ z) (f e) u →
        ∃ (d : 𝓞 L) (n : ℕ) (x x' : B.carrier) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
          d ∉ 𝔭 ∧ n ≠ 0 ∧ g x = algebraMap (𝓞 L) A d * u ∧ M.ValAt _ ((n : Ω) • e) v ∧
          (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x').left) ∧ (n : 𝓞 L) • x = d • x' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.FinLie.exists_integral_form | exact GlobalTheory.CompanionTheory.Ar.RootHt.FinLie.exists_integral_form | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.FinLie.exists_integral_form <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_local_subring_point : ∀ (S X : Scheme.{0}) (G : Over S) [GrpObj G] (Gx : Over X) [GrpObj Gx] [IsCommMonObj Gx] [Smooth Gx.hom] (φ : Gx.left ⟶ G.left) (Ω₁ : Type) [Field Ω₁] (ξ : Spec (CommRingCat.of Ω₁) ⟶ X), IsCptGen ξ → ∀ (Li : Type) [AddCommGroup Li] [Module Ω₁ Li] (M : LieModel Gx ξ Li) (F : Type) [Field F] (θ : Ω₁ →+* F) (A : Subring F) [IsLocalRing A] (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z), (∀ s : X.presheaf.stalk (centre z), (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) → ∀ (ER : Type) [AddCommGroup ER] [Module A ER] (MR : LieModel Gx z ER) (xF : Spec (CommRingCat.of F) ⟶ S) (V : Type) [AddCommGroup V] [Module F V] (MV : LieModel G xF V) (io : ER → V) (Lm : Li → V), (∀ x, (MV.pt (io x)).left = Spec.map (CommRingCat.ofHom (dualMap A.subtype)) ≫ (MR.pt x).left ≫ φ) → (∀ e, (MV.pt (Lm e)).left = Spec.map (CommRingCat.ofHom (dualMap θ)) ≫ (M.pt e).left ≫ φ) → ∀ (r : ℕ) (b : Fin r → Li) (π : Fin r → Module.Dual Ω₁ Li) (m : ℕ), (∀ i, (m : Ω₁) • b i ∈ M.lat ⟨centre z, h⟩) → (∀ i j, π i (b j) = if i = j then 1 else 0) → (∀ i, ∀ e ∈ M.lat ⟨centre z, h⟩, (m : Ω₁) * π i e ∈ regAt ξ ⟨centre z, h⟩) → ∃ (β : Fin r → ER) (g : Fin r → ER →ₗ[A] A), (∀ k, io (β k) = Lm ((m : Ω₁) • b k)) ∧ ∀ i k, ((g i (β k) : A) : F) = if k = i then (m : F) ^ 2 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameDual.exists_frame_dual_sq | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameDual.exists_frame_dual_sq | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameDual.exists_frame_dual_sq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_frame_spans_generic : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] (zL : Sp L ⟶ X) (T : Type) [AddCommGroup T] [Module L T] (TL : LieModel G zL T) (h : genPt ξ ⤳ centre zL) (Ix : Type) [Fintype Ix] (f : Ix → Li), IsCptGen ξ → LinearIndependent Ω f → Submodule.span Ω (Set.range f) = ⊤ → M.lat ⟨centre zL, h⟩ = Submodule.span (regAt ξ ⟨centre zL, h⟩) (Set.range f) → ∃ w : Ix → T, (∀ i, M.ValAt zL (f i) (TL.pt (w i))) ∧ LinearIndependent L w ∧ Submodule.span L (Set.range w) = ⊤ ∧ ∀ (A : Set Ix) (e : Li) (u : T), e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' A) → M.ValAt zL e (TL.pt u) → u ∈ Submodule.span L (w '' A) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_valFrame | exact GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_valFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_valFrame <;> assumption)
end

section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.root_flat_pushforward_geoFun : PtsIntegrableStatement → MetricLocalStatement → DegreeStatement → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ) (R : RootFlat M τ) (Q : RP Ψ N), IsIntersectionSystem II → M.Converges II → Q.IsHomogeneous (dimFl Ψ N) → M.PP II (toA (pk τ 1 * Q)) = R.ht * M.geoFun (toA Q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq | exact GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

section Comb

variable {S : Scheme.{0}} {R : Type} [CommRing R]

theorem epsMul_zero_eq : GlobalTheory.CompanionTheory.Ar.epsMul (0 : R) =
    (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  apply RingHom.ext
  intro x
  apply TrivSqZeroExt.ext <;> simp [GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem epsMul_one_eq : GlobalTheory.CompanionTheory.Ar.epsMul (1 : R) = RingHom.id (DualNumber R) := by
  apply RingHom.ext
  intro x
  apply TrivSqZeroExt.ext <;> simp [GlobalTheory.CompanionTheory.Ar.epsMul]

theorem comp_one_over {Y Z M : Over S} [GrpObj M] (f : Y ⟶ Z) : f ≫ (1 : Z ⟶ M) = 1 := by
  exact MonObj.comp_one f

theorem prod_ofFn_single {M : Type*} [Monoid M] : ∀ {n : ℕ} (u : Fin n → M) (j : Fin n),
    (∀ i, i ≠ j → u i = 1) → (List.ofFn u).prod = u j := by
  intro n
  induction n with
  | zero => intro u j; exact j.elim0
  | succ n ih =>
    intro u j hu
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hj : j = 0
    · subst hj
      have h1 : (List.ofFn fun i : Fin n => u i.succ).prod = 1 := List.prod_eq_one fun x hx => by
        simp only [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact hu _ (Fin.succ_ne_zero i)
      rw [h1, _root_.mul_one]
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
      rw [hu 0 (Fin.succ_ne_zero j').symm, _root_.one_mul]
      exact ih (fun i => u i.succ) j' fun i hi => hu _ fun h => hi (Fin.succ_injective _ h)

theorem isComb_single {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {n : ℕ} (w : Fin n → (epsAt x ⟶ G))
    (hw : ∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G x (w i)) (j : Fin n) : GlobalTheory.CompanionTheory.Ar.Fl.IsComb (Pi.single j 1) w (w j) := by
  classical
  refine ⟨fun i => if i = j then w i else 1, fun i => ?_, ?_⟩
  · show Over.Hom.left (if i = j then w i else 1) = _
    by_cases hij : i = j
    · subst hij
      simp [epsMul_one_eq, spMap]
    · rw [if_neg hij, Pi.single_eq_of_ne hij, epsMul_zero_eq]
      have h1 := comp_one_over (M := G)
        (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R)))) rfl :
          GlobalTheory.CompanionTheory.Ar.epsAt x ⟶ Over.mk x)
      rw [← h1, Over.comp_left, ← hw i]
      simp [spMap]
  · rw [prod_ofFn_single _ j fun i hi => if_neg hi, if_pos rfl]

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem eq_mul_of_frames {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ φ₀ : FrameFn Xo c} (hφ : IsLineFn U τ φ)
    (hφ₀ : IsLineFn U τ φ₀) {F : Type} [Field F] {β : c.F →+* F} {y : Sp F ⟶ Xo.XF c} {v v' : Vecs y D.p}
    {w w' : Vecs y D.q} (h : IsFramed U τ β y v w) (h' : IsFramed U τ β y v' w') {b : F}
    (hb : φ F y v' w' = b * φ₀ F y v' w') : φ F y v w = b * φ₀ F y v w := by
  have hv := h.2.2.1
  have hw := h.2.2.2
  have hv' := h'.2.2.1
  have hw' := h'.2.2.2
  have hvw' : IsFramed U τ β y v w' := ⟨h.1, h.2.1, hv, hw'⟩
  let A : Matrix (Fin D.p) (Fin D.p) F := fun a => (hv.2 (v' a) (hv'.1 a)).exists.choose
  have hA : ∀ a, IsComb (A a) v (v' a) := fun a => (hv.2 (v' a) (hv'.1 a)).exists.choose_spec
  let B : Matrix (Fin D.q) (Fin D.q) F := fun b => (hw.2 (w' b) (hw'.1 b)).exists.choose
  have hB : ∀ b, IsComb (B b) w (w' b) := fun b => (hw.2 (w' b) (hw'.1 b)).exists.choose_spec
  have hIv : ∀ a, IsComb ((1 : Matrix (Fin D.p) (Fin D.p) F) a) v (v a) := fun a => by
    have h1 : (1 : Matrix (Fin D.p) (Fin D.p) F) a = Pi.single a 1 :=
      funext fun b => Matrix.one_eq_pi_single
    rw [h1]
    exact isComb_single v (fun i => (hv.1 i).1) a
  have hIw : ∀ b, IsComb ((1 : Matrix (Fin D.q) (Fin D.q) F) b) w' (w' b) := fun b => by
    have h1 : (1 : Matrix (Fin D.q) (Fin D.q) F) b = Pi.single b 1 :=
      funext fun b' => Matrix.one_eq_pi_single
    rw [h1]
    exact isComb_single w' (fun i => (hw'.1 i).1) b
  have e1 := hφ.chg F β y v w v w' 1 B h hvw' hIv hB
  have e1₀ := hφ₀.chg F β y v w v w' 1 B h hvw' hIv hB
  have e2 := hφ.chg F β y v w' v' w' A 1 hvw' h' hA hIw
  have e2₀ := hφ₀.chg F β y v w' v' w' A 1 hvw' h' hA hIw
  rw [Matrix.det_one, _root_.mul_one] at e1 e1₀ e2 e2₀
  have hBne : B.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e1
    exact hφ.ne F β y v w' hvw' e1
  apply mul_right_cancel₀ hBne
  calc φ F y v w * B.det = φ F y v w' := e1.symm
    _ = φ F y v' w' * A.det := e2.symm
    _ = b * (φ₀ F y v' w' * A.det) := by rw [hb, _root_.mul_assoc]
    _ = b * φ₀ F y v w * B.det := by rw [e2₀, e1₀, _root_.mul_assoc]

theorem ratio_at {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ φ₀ : FrameFn Xo c} (hφ : IsLineFn U τ φ)
    (hφ₀ : IsLineFn U τ φ₀) {a : ℂ}
    (ha : ∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ ℂ y v w = a * φ₀ ℂ y v w)
    {k : Type} [Field k] {β₀ : c.F →+* k} {y₀ : Sp k ⟶ Xo.XF c} {v₀ : Vecs y₀ D.p} {w₀ : Vecs y₀ D.q}
    (h₀ : IsFramed U τ β₀ y₀ v₀ w₀)
    (hb : ∀ (F' : Type) [Field F'] (f' : k →+* F'), ∃ (v' : Vecs (spMap f' ≫ y₀) D.p)
      (w' : Vecs (spMap f' ≫ y₀) D.q), IsFramed U τ (f'.comp β₀) (spMap f' ≫ y₀) v' w' ∧
        (∀ a, (v' a).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f') ≫ (v₀ a).left) ∧
        ∀ b, (w' b).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f') ≫ (w₀ b).left)
    (j : k →+* ℂ) (hj : j.comp β₀ = algebraMap c.F ℂ) : j (φ k y₀ v₀ w₀) = a * j (φ₀ k y₀ v₀ w₀) := by
  obtain ⟨v', w', hfr, hv', hw'⟩ := hb ℂ j
  have hfr' : IsFramed U τ (algebraMap c.F ℂ) (spMap j ≫ y₀) v' w' := by
    rw [← hj]
    exact hfr
  have e := ha _ v' w' hfr'
  rw [hφ.nat k ℂ j β₀ y₀ v₀ w₀ _ v' w' h₀ rfl hv' hw',
    hφ₀.nat k ℂ j β₀ y₀ v₀ w₀ _ v' w' h₀ rfl hv' hw'] at e
  exact e

theorem flatGen_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ₀ : FrameFn Xo c) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → IsFlatGen U τ φ FU i → IsFlatGen U τ φ₀ FU i → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → ∃ a : c.F, a ≠ 0 ∧ ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ F y v w = β a * φ₀ F y v w := by
  intro E _ _ _ H D l Xo c U τ φ φ₀ g ty FU i hty hφ hφ₀ hper
  obtain ⟨a, ha⟩ := GlobalTheory.T.flat_gen_frame_independent E H D l Xo c U τ φ φ₀ g ty FU i hty hφ hφ₀ hper
  have hL := hφ.line
  have hL₀ := hφ₀.line
  by_cases hex : ∃ (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q),
      IsFramed U τ (algebraMap c.F ℂ) y v w
  · obtain ⟨y1, v1, w1, h1⟩ := hex
    obtain ⟨k, _, β₀, y₀, v₀, w₀, f, j, h₀, -, hj, -, hb⟩ :=
      GlobalTheory.T.framed_point_descends E H D l Xo c U τ ℂ (algebraMap c.F ℂ) y1 v1 w1 h1
    have hr := ratio_at hL hL₀ ha h₀ hb j hj
    have hne₀ : j (φ₀ k y₀ v₀ w₀) ≠ 0 := (map_ne_zero j).2 (hL₀.ne k β₀ y₀ v₀ w₀ h₀)
    have hfix : ∀ σ' : ℂ ≃+* ℂ, (∀ x ∈ c.F, σ' x = x) → σ' a = a := by
      intro σ' hσ'
      have hj' : (σ'.toRingHom.comp j).comp β₀ = algebraMap c.F ℂ := by
        refine RingHom.ext fun x => ?_
        have hx := RingHom.congr_fun hj x
        simp only [RingHom.comp_apply] at hx ⊢
        rw [hx]
        exact hσ' _ x.2
      have hr' := ratio_at hL hL₀ ha h₀ hb _ hj'
      simp only [RingHom.comp_apply] at hr'
      rw [hr, map_mul] at hr'
      exact mul_right_cancel₀ ((map_ne_zero _).2 hne₀) hr'
    have haF : a ∈ c.F := GlobalTheory.T.fixed_by_automorphisms_mem_field c.F a c.fin hfix
    refine ⟨⟨a, haF⟩, ?_, ?_⟩
    · intro h0
      have ha0 : a = 0 := congrArg Subtype.val h0
      apply hL.ne k β₀ y₀ v₀ w₀ h₀
      apply j.injective
      rw [hr, map_zero, ha0, zero_mul]
    · intro F _ β y v w hfr
      obtain ⟨k', _, β₀', y₀', v₀', w₀', f', j', h₀', hfβ', hj'', hy', hb'⟩ :=
        GlobalTheory.T.framed_point_descends E H D l Xo c U τ F β y v w hfr
      subst hy'
      subst hfβ'
      have hr2 := ratio_at hL hL₀ ha h₀' hb' j' hj''
      have hk : φ k' y₀' v₀' w₀' = β₀' ⟨a, haF⟩ * φ₀ k' y₀' v₀' w₀' := by
        apply j'.injective
        rw [map_mul, hr2]
        congr 1
        have hx := RingHom.congr_fun hj'' ⟨a, haF⟩
        simp only [RingHom.comp_apply] at hx
        rw [hx]
        rfl
      obtain ⟨v', w', hfr', hv', hw'⟩ := hb' F f'
      have n1 := hL.nat k' F f' β₀' y₀' v₀' w₀' _ v' w' h₀' rfl hv' hw'
      have n2 := hL₀.nat k' F f' β₀' y₀' v₀' w₀' _ v' w' h₀' rfl hv' hw'
      refine eq_mul_of_frames hL hL₀ hfr hfr' (b := f' (β₀' ⟨a, haF⟩)) ?_
      rw [n1, n2, hk, map_mul]
  · refine ⟨1, one_ne_zero, fun F _ β y v w hfr => ?_⟩
    exfalso
    obtain ⟨k, _, β₀, y₀, v₀, w₀, f, j, h₀, -, hj, -, hb⟩ :=
      GlobalTheory.T.framed_point_descends E H D l Xo c U τ F β y v w hfr
    obtain ⟨v', w', hfr', -, -⟩ := hb ℂ j
    rw [hj] at hfr'
    exact hex ⟨_, v', w', hfr'⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.constants_compatible_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (cst₀ : c.F →+* 𝔐.Ω₀) (y₁ : Sp 𝔐.Ω₀ ⟶ Xo.XF c), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → 𝔐.ξ₀ = y₁ ≫ Y.j → 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) → 𝔐.fn.comp cst₀ = 𝔐.cst → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li₀), (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) ∧ (∀ (a : 𝔐.Ω₀) e, j (a • e) = 𝔐.fn a • j e) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) ∧ (∀ s, LinearIndependent 𝔐.Ω₀ (b s) ∧ Submodule.span 𝔐.Ω₀ (Set.range (b s)) = V₀ s) ∧ (∀ s, LinearIndependent Ω fun k => j (b s k)) ∧ ∀ s, Submodule.span Ω (Set.range fun k => j (b s k)) = 𝔐.Vgen s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HcLie.exists_lie_eig | exact GlobalTheory.CompanionTheory.Ar.HcLie.exists_lie_eig | (intros; apply GlobalTheory.CompanionTheory.Ar.HcLie.exists_lie_eig <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.frame_functions_flat_agree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → Z.IsGeom → IsLineFn U τ φ → FlatOnModel Z τ φ → IsLineFn U τ φ' → FlatOnModel Z τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_const_of_flatOnModel | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_const_of_flatOnModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_const_of_flatOnModel <;> assumption)
end
