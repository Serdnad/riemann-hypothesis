module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle081
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle082
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.abelian_sections_irreducible_theta_group : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), (N : F) ≠ 0 → (∀ x : Over.mk p ⟶ P.A, x ^ N = 1 → ∃ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt = x) ∧ ∀ U : Submodule F (EA P p N), (∀ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt ^ N = 1 → ∀ v v' : EA P p N, IsActOf P.A P.L (N : ℤ) θ v.sec v'.sec → v ∈ U → v' ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first | exact @GlobalTheory.ThetaIrred.main | exact GlobalTheory.ThetaIrred.main | (intros; apply GlobalTheory.ThetaIrred.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_cp_of_isSymmetric :
    Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (L : RigLB G) (c : CubicalStr G L), L.IsSymmetric → ∃ P : CP G, P.L = L ∧ HEq P.c c := by
  intro hL R _ _ _ A G _ _ hS gen _ L c hsym
  obtain ⟨s, hs, hr⟩ := GlobalTheory.SymmetricBundle.gen_of_isSymmetric L hsym
  have := hS.smooth
  have : Flat (G3 G).hom := by
    show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
    infer_instance
  exact ⟨⟨L, c, s, hs, hr, GlobalTheory.ValueForm.sym_cub_of_baseChange (jK R) (GlobalTheory.ValueForm.app_generic_injective _)
    (GlobalTheory.ValueForm.surjective_cube_baseChange hL.globalFns _ A.isAb gen) c s hs hr⟩, rfl, HEq.rfl⟩

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.locallyTrivial_torusQuotient_flat_surjective_cosets : (∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G B : Over S) [GrpObj G] (i : splitTorus S X ⟶ G) (q : G ⟶ B), IsMonHom i → IsAffineHom q.left → (∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧ (∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧ Function.Injective (q.left.app V).hom ∧ (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ∧ ∃ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ) → Mono i ∧ Flat q.left ∧ Surjective q.left ∧ (Smooth G.hom → Smooth B.hom) ∧ ∀ (Z : Over S) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ splitTorus S X, g' = (t ≫ i) * g) := by
  first | exact @GlobalTheory.LocTriv.main | exact GlobalTheory.LocTriv.main | (intros; apply GlobalTheory.LocTriv.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.UU.IntGen

theorem exists_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ a.val * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      have := h U f
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, this, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have key : (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ (res le (t.s PEmpty.elim)).val := by
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm)
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem prod_famT {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T ⊗ D.P.A) (α : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ famφT D T α i) ^ DegPre.famε k i =
      h (ρ ≫ snd _ _).left ^ ((k : ℤ) - 1) * h (cP D T' α * (ρ ≫ snd _ _)).left * (h (cP D T' α).left)⁻¹ *
        h (1 : T' ⟶ D.P.A).left := by
  have e₁ : ρ.left ≫ famφT D T α 1 = (cP D T' α * (ρ ≫ snd _ _)).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (snd T D.P.A) (cP D _ α)).trans (by rw [comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ famφT D T α 2 = (cP D T' α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₃ : ρ.left ≫ famφT D T α 3 = (1 : T' ⟶ D.P.A).left :=
    congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

def basePts (T : Over (Spec (CommRingCat.of R))) (α mu : D.X) : Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(cP D T α * cP D T mu).left, (cP D T α).left, (cP D T mu).left, (1 : T ⟶ D.P.A).left]

def baseExp (k : ℕ) : Fin 4 → ℤ := ![-1, 1, 1 - k, k - 1]

theorem prod_base {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (α mu : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ basePts D T α mu i) ^ baseExp k i =
      (h (cP D T' α * cP D T' mu).left)⁻¹ * h (cP D T' α).left * h (cP D T' mu).left ^ (1 - (k : ℤ)) *
        h (1 : T' ⟶ D.P.A).left ^ ((k : ℤ) - 1) := by
  have e₀ : ρ.left ≫ basePts D T α mu 0 = (cP D T' α * cP D T' mu).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (cP D _ α) (cP D _ mu)).trans (by rw [comp_cP, comp_cP]))
  have e₁ : ρ.left ≫ basePts D T α mu 1 = (cP D T' α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₂ : ρ.left ≫ basePts D T α mu 2 = (cP D T' mu).left := congrArg (fun q => q.left) (comp_cP D ρ mu)
  have e₃ : ρ.left ≫ basePts D T α mu 3 = (1 : T' ⟶ D.P.A).left :=
    congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₀, e₁, e₂, e₃]
  show _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ (1 - (k : ℤ)) * _ ^ ((k : ℤ) - 1) = _
  rw [zpow_one, zpow_neg_one]

theorem exists_genT (T S : Over (Spec (CommRingCat.of R))) (π : T ⊗ D.P.A ⟶ S) (k : ℕ) (α mu : D.X)
    (v : LB.Gen (LB.LinComb D.P.L (basePts D S α mu) (baseExp k))) (hv : v.IsGen) :
    ∃ u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (DegPre.deltaε k)), u₀.IsGen ∧
      ∀ (T' : Over (Spec (CommRingCat.of R))) (ρ : T' ⟶ T ⊗ D.P.A) (z : T'.left) (J), Good D.P.L z J →
        val u₀ ρ.left z J = cubN (th D z J) k (cP D T' α) (cP D T' mu) (ρ ≫ snd _ _) *
          (th D z J (cP D T' α) (ρ ≫ snd _ _) (cP D T' mu))⁻¹ * val v (ρ ≫ π).left z J := by
  let a : T ⊗ D.P.A ⟶ D.P.A := cP D _ α
  let mm : T ⊗ D.P.A ⟶ D.P.A := cP D _ mu
  let x : T ⊗ D.P.A ⟶ D.P.A := snd _ _
  have hα' : cP D (T ⊗ D.P.A) (α + k • mu) = a * mm ^ k := by rw [cPoint_add, cPoint_nsmul]
  have htr : trT D (toUnit T ≫ D.c mu) ≫ snd _ _ = x * mm :=
    (lift_snd _ _).trans (congrArg (x * ·) (comp_cP D (fst T D.P.A) mu))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.P.isLB (φ' := deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu))
      (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := prod_base D π α mu k h
      have p₃ := prod_famT D (𝟙 (T ⊗ D.P.A)) (α + k • mu) k h
      have p₄ := prod_famT D (trT D (toUnit T ≫ D.c mu)) α k h
      simp only [Over.id_left, Category.id_comp] at p₃
      rw [hα'] at p₃
      rw [htr] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := Fin 4) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      rw [← _root_.mul_assoc (cP D _ α), mul_comm mm x]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.P.L _ _ v π.left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _)))
      (pullGen_isGen _ _ _ _ hv _))
  refine ⟨u₀, hu₀, fun T' ρ z J hJ => ?_⟩
  refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (vN T' ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _)))).trans ?_))
    (val_pull hJ _ _ _)))
  rw [← comp_cP D ρ α, ← comp_cP D ρ mu]

def multK (k : ℕ) (mu α : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi mu) k) (D.tau mu α))
    (GeneratorPullback.powGen D.P.L _ _ D.rigK k)

theorem gs_spec {Z : Scheme.{0}} (σ : Z ⟶ (TK R).left) (z : Z) (c : R) :
    gs (σ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) =
      gs σ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) c)) := by
  refine (gs_pull σ (jK R) z ⊤ trivial _).symm.trans (congrArg (gs σ z ⊤) ?_)
  exact (congrArg (fun f => (CommRingCat.Hom.hom f) c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm

theorem multK_frac (k : ℕ) (α mu : D.X)
    (v : LB.Gen (LB.LinComb D.P.L (basePts D (𝟙_ _) α mu) (baseExp k))) (hv : v.IsGen) :
    ∃ r₁ r₂ : R, r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ ∀ (Z : Scheme.{0}) (σ : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J →
      gs (σ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r₂) * (val (multK D k mu α) σ z J).val =
      gs (σ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r₁) *
        (val v (σ ≫ (toUnit (TK R)).left) z J).val := by
  obtain ⟨a, ha⟩ := exists_ratio D.P.isLB (u := multK D k mu α)
    (u' := LB.pullGen D.P.L _ _ v (toUnit (TK R)).left) (fun U _ h => by
      refine Eq.trans ?_ (prod_base D (toUnit (TK R)) α mu k h).symm
      have a₁ : ∀ χ, D.xK χ = (cP D (TK R) χ).left := fun χ => rfl
      have a₂ : (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TK R ⟶ D.P.A).left := rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [add_comm mu α, cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (powGen_isGen _ _ _ _ (D.psi_gen mu) k) (tau_isGen D mu α))
      (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) k)) (pullGen_isGen _ _ _ _ hv _)
  let c : FractionRing R := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val
  have hc : (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom c = a.val :=
    Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))) a.val
  have hc0 : c ≠ 0 :=
    (a.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom).ne_zero
  obtain ⟨r₁, r₂, h₂, e⟩ := IsFractionRing.div_surjective (A := R) c
  have h₂' : r₂ ≠ 0 := nonZeroDivisors.ne_zero h₂
  have h₂K : algebraMap R (FractionRing R) r₂ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 h₂'
  refine ⟨r₁, r₂, fun h => hc0 (by rw [← e, h, map_zero, zero_div]), h₂', fun Z σ z J hJ => ?_⟩
  have e' : algebraMap R (FractionRing R) r₁ = algebraMap R (FractionRing R) r₂ * c := by
    rw [← e, mul_div_cancel₀ _ h₂K]
  rw [ha Z σ z J hJ, val_pull hJ, gs_spec, gs_spec, e', map_mul, hc, ← _root_.mul_assoc]
  exact congrArg (· * _) (gs_mul σ z ⊤ trivial _ _).symm

theorem frac_mul {M : Type} [CommMonoid M] {g₁ g₂ : M} {u u₀ w m v : Mˣ} (h₁ : u = w * m) (h₂ : u₀ = w * v)
    (h : g₂ * m.val = g₁ * v.val) : g₂ * u.val = g₁ * u₀.val := by
  rw [h₁, h₂, Units.val_mul, Units.val_mul, mul_left_comm, h, mul_left_comm]

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (α mu : D.X), ∃ (u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (DegPre.deltaε k))) (r₁ r₂ : R), u₀.IsGen ∧ r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : TF (R := R) F ⟶ T) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F k mu α) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J → gs r z ⊤ (scal (DegPre.BF D F).hom r₂) * (val u r z J).val = gs r z ⊤ (scal (DegPre.BF D F).hom r₁) * (val u₀ (r ≫ (φ ▷ D.P.A).left) z J).val := by
  intro hG R _ _ _ D T k α mu
  obtain ⟨v, hv⟩ := exists_gen_of_local (V := R) D.P.L D.P.isLB (basePts D (𝟙_ _) α mu) (baseExp k)
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_genT D T (𝟙_ _) (toUnit _) k α mu v hv
  obtain ⟨r₁, r₂, h₁, h₂, hr⟩ := multK_frac D k α mu v hv
  refine ⟨u₀, r₁, r₂, hu₀, h₁, h₂, fun F _ _ φ u hu hc Z r z J hJ => ?_⟩
  let T' : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (DegPre.BF D F).hom)
  let ρ : T' ⟶ DegPre.BF D F := Over.homMk r rfl
  let κ : T' ⟶ TK R := Over.homMk ((ρ ≫ fst _ _).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (ρ ≫ fst _ _)))
  have e₁ := (gen_fe (D := D) (F := F) hG k mu α).2 u hu hc T' ρ z J hJ
  have e₂ := vu₀ T' (ρ ≫ φ ▷ D.P.A) z J hJ
  have e₃ : val (DegPre.famMult D F k mu α) (ρ ≫ fst _ _).left z J = val (multK D k mu α) κ.left z J :=
    val_pull hJ _ _ _
  have e₄ := hr _ κ.left z J hJ
  have e₅ : κ.left ≫ jK R = r ≫ (DegPre.BF D F).hom := Over.w κ
  have e₆ : κ.left ≫ (toUnit (TK R)).left = ((ρ ≫ φ ▷ D.P.A) ≫ toUnit _).left :=
    congrArg (fun q => q.left) (toUnit_unique (κ ≫ toUnit (TK R)) _)
  have e₇ : (ρ ≫ φ ▷ D.P.A) ≫ snd _ _ = ρ ≫ DegPre.prB D F := by rw [Category.assoc, whiskerRight_snd]
  have g : ∀ c : R, gs r z ⊤ (scal (DegPre.BF D F).hom c) =
      gs (r ≫ (DegPre.BF D F).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := fun c =>
    gs_pull r (DegPre.BF D F).hom z ⊤ trivial _
  rw [e₅, e₆] at e₄
  rw [e₃, uVal, ← Category.assoc, comp_cP] at e₁
  rw [e₇] at e₂
  rw [g, g]
  exact frac_mul e₁ e₂ e₄

end GlobalTheory.UU.IntGen
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

namespace GlobalTheory.UU

theorem finsum_rel {A : Type*} [CommRing A] {Ix Ix' : Type*} (σ : Ix ≃ Ix') (f : Ix → A) (g : Ix' → A)
    (a b v : A) (s : Finset Ix) (s' : Finset Ix') (hf : ∀ i ∉ s, f i = 0) (hg : ∀ i ∉ s', g i = 0)
    (h : ∀ i, a * g (σ i) = b * (f i * v)) :
    a * ∑ i ∈ s', g i = b * ((∑ i ∈ s, f i) * v) := by
  classical
  have h1 : ∑ i ∈ s, f i = ∑ i ∈ s ∪ s'.map σ.symm.toEmbedding, f i :=
    Finset.sum_subset Finset.subset_union_left (fun i _ hi => hf i hi)
  have h2 : ∑ i ∈ s', g i = ∑ i ∈ s'.map σ.symm.toEmbedding, g (σ i) := by
    rw [Finset.sum_map]; simp
  have h3 : ∑ i ∈ s'.map σ.symm.toEmbedding, g (σ i) = ∑ i ∈ s ∪ s'.map σ.symm.toEmbedding, g (σ i) :=
    Finset.sum_subset Finset.subset_union_right (fun i _ hi => hg _ (fun hm => hi (by
      rw [Finset.mem_map]; exact ⟨σ i, hm, by simp⟩)))
  rw [h1, h2, h3, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => h i)

theorem adicSum_rel : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y Y₂ : Over (Spec (CommRingCat.of R))) (τ : Y ⟶ Y₂) (X : Scheme.{0}) (L : LB X) (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂.left ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y.left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → (Y.left ⟶ X)) (εu : K'' → ℤ) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ(Y.left, ⊤)) (Ix Ix' : Type) (σ : Ix ≃ Ix') (p : Ix → LB.Sec (LB.LinComb L φ ε)) (p' : Ix' → LB.Sec (LB.LinComb L φ' ε')) (S S'), AdicSum I p S → AdicSum I p' S' → (∀ i (Z : Scheme.{0}) (r : Z ⟶ Y.left) (z : Z) (J), Good L z J → gs r z ⊤ c' * sval (p' (σ i)) r z J = gs r z ⊤ c * (sval (p i) (r ≫ τ.left) z J * (val u r z J).val)) → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Y.left), Lvl I e (r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval S' r z J = gs r z ⊤ c * (sval S (r ≫ τ.left) z J * (val u r z J).val) := by
  intro R _ I Y Y₂ τ X L K K' K'' _ _ _ φ ε φ' ε' φu εu u c c' Ix Ix' σ p p' S S' hS hS' h e Z r hr z J hJ
  obtain ⟨s, hs⟩ := hS e
  obtain ⟨s', hs'⟩ := hS' e
  have hr2 : Lvl I e ((r ≫ τ.left) ≫ Y₂.hom) := by
    rw [Category.assoc, Over.w τ]; exact hr
  obtain ⟨a1, a2⟩ := hs Z (r ≫ τ.left) hr2 z J hJ
  obtain ⟨b1, b2⟩ := hs' Z r hr z J hJ
  rw [a2, b2]
  exact finsum_rel σ _ _ _ _ _ s s' a1 b1 (fun i => h i Z r z J hJ)

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem prod_famT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (α : D.X) (k : ℕ) {U : Type} [CommGroup U] (h : ((T ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ i, h (famφT D T α i) ^ DegPre.famε k i =
      h (snd T D.P.A).left ^ ((k : ℤ) - 1) * h (DVR.cP D (T ⊗ D.P.A) α * snd T D.P.A).left *
        (h (DVR.cP D (T ⊗ D.P.A) α).left)⁻¹ * h (1 : T ⊗ D.P.A ⟶ D.P.A).left := by
  have e₁ : famφT D T α 1 = (DVR.cP D (T ⊗ D.P.A) α * snd T D.P.A).left :=
    congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (mul_comm (snd T D.P.A) (DVR.cP D (T ⊗ D.P.A) α))
  have e₂ : famφT D T α 2 = (DVR.cP D (T ⊗ D.P.A) α).left := rfl
  have e₃ : famφT D T α 3 = (1 : T ⊗ D.P.A ⟶ D.P.A).left := rfl
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

theorem exists_isProdB : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (k l : ℕ) (β ga α : D.X), β + ga = α → ∀ (f : SecBT D T k β) (g : SecBT D T l ga),
    ∃ h : SecBT D T (k + l) α, IsProdB f g h := by
  intro R _ _ D T k l β ga α hα f g
  subst hα
  let a : T ⊗ D.P.A ⟶ D.P.A := DVR.cP D _ β
  let b : T ⊗ D.P.A ⟶ D.P.A := DVR.cP D _ ga
  let x : T ⊗ D.P.A ⟶ D.P.A := snd T D.P.A
  have hu := DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift a (lift b x)).left
  obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := famφT D T (β + ga)) (ε' := DegPre.famε (k + l)) (fun U _ h => by
      have p₁ := prod_cub a b x h
      have p₂ := prod_famT D T β k h
      have p₃ := prod_famT D T ga l h
      have p₄ := prod_famT D T (β + ga) (k + l) h
      rw [DVR.cPoint_add] at p₄
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₂ p₃) p₁) (Eq.trans ?_ p₄.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, a, b, x]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec f g) (genSec (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift a (lift b x)).left) hu))
  refine ⟨t, fun Z r z J hJ => ?_⟩
  refine (ht _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ) ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val
      ((val_cub D.cub r hJ a b x).trans ?_)))))
  rw [DVR.comp_cP, DVR.comp_cP]; rfl

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_pullSec_sval {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (hφ : ∀ k, h ≫ φ k = φ' k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext hφ
  refine ⟨DVR.pullSec L φ ε s h, fun Z r z J hJ => ?_⟩
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm := hJ.mem (fun k => h ≫ φ k) r
  exact (gs_res r z _ hm _).trans
    (gs_pull r h z (LB.wchart L φ (fun k => J (r ≫ h ≫ φ k))) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) _)

theorem whisker_famφT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T' : Over (Spec (CommRingCat.of R))}
    (ρ : T' ⟶ T) (α : D.X) (i : Fin 4) : (ρ ▷ D.P.A).left ≫ famφT D T α i = famφT D T' α i := by
  have hu : ρ ▷ D.P.A ≫ toUnit _ = toUnit _ := toUnit_unique _ _
  fin_cases i
  · show (ρ ▷ D.P.A ≫ snd T D.P.A).left = (snd T' D.P.A).left
    rw [whiskerRight_snd]
  · show (ρ ▷ D.P.A ≫ padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left =
      (padd D.P.A (snd T' D.P.A) (toUnit _ ≫ D.c α)).left
    congr 1
    unfold padd
    rw [← Category.assoc, comp_lift, whiskerRight_snd, ← Category.assoc, hu]
  · show (ρ ▷ D.P.A ≫ toUnit _ ≫ D.c α).left = (toUnit (T' ⊗ D.P.A) ≫ D.c α).left
    rw [← Category.assoc, hu]
  · show (ρ ▷ D.P.A ≫ toUnit _ ≫ η[D.P.A]).left = (toUnit (T' ⊗ D.P.A) ≫ η[D.P.A]).left
    rw [← Category.assoc, hu]

theorem expT_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T T' : Over (Spec (CommRingCat.of R))) (ρ : T' ⟶ T) (k : ℕ) (σ : U.SecGT T k) (f : ∀ α, SecBT D T k α), U.ExpT T k σ f → ∃ (σ' : U.SecGT T' k) (f' : ∀ α, SecBT D T' k α), U.ExpT T' k σ' f' ∧ PullT ρ f f' ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : TF (R := R) F ⟶ T') (s : Raw D F k), PullB D F φ k f' s ↔ PullB D F (φ ≫ ρ) k f s := by
  intro R _ _ I D A G _ _ U T T' ρ k σ f H
  obtain ⟨σ', hσ⟩ := exists_pullSec_sval σ (ρ ▷ G).left (fun _ => (snd T' G).left) (fun _ => by
    show (ρ ▷ G ≫ snd T G).left = _
    rw [whiskerRight_snd])
  choose f' hf using fun α => exists_pullSec_sval (f α) (ρ ▷ D.P.A).left (famφT D T' α) (whisker_famφT D ρ α)
  have s1 : ∀ B : Over (Spec (CommRingCat.of R)), (ρ ▷ B).left ≫ (snd T B).left = (snd T' B).left := fun B => by
    show (ρ ▷ B ≫ snd T B).left = _
    rw [whiskerRight_snd]
  have s2 : ∀ B : Over (Spec (CommRingCat.of R)), (ρ ▷ B).left ≫ (fst T B).left = (fst T' B).left ≫ ρ.left := fun B => by
    show (ρ ▷ B ≫ fst T B).left = (fst T' B ≫ ρ).left
    rw [whiskerRight_fst]
  refine ⟨σ', f', fun e => ?_, fun α Z r z J hJ => hf α Z r z J hJ, fun F _ _ φ s => ?_⟩
  · obtain ⟨s, hs⟩ := H e
    refine ⟨s, fun Z x rG rB h1 h2 h3 z JG J hG hJ => ?_⟩
    have := hs Z x (rG ≫ (ρ ▷ G).left) (rB ≫ (ρ ▷ D.P.A).left) (by rw [Category.assoc, s1, h1])
      (by rw [Category.assoc, s1, h2])
      (by rw [Category.assoc, s2, Category.assoc, s2, ← Category.assoc, h3, Category.assoc]) z JG J hG hJ
    refine ⟨fun α hα => (hf α Z rB z J hJ).trans (this.1 α hα), ?_⟩
    rw [hσ Z rG z JG hG, this.2]
    exact Finset.sum_congr rfl fun α _ => by rw [hf α Z rB z J hJ]
  · have e : (φ ▷ D.P.A).left ≫ (ρ ▷ D.P.A).left = ((φ ≫ ρ) ▷ D.P.A).left := by
      rw [comp_whiskerRight]; rfl
    have key : ∀ α (z : (DegPre.BF D F).left) J, Good D.P.L z J →
        sval (f' α) (φ ▷ D.P.A).left z J = sval (f α) ((φ ≫ ρ) ▷ D.P.A).left z J := fun α z J hJ =>
      (hf α _ (φ ▷ D.P.A).left z J hJ).trans (congrArg (fun q => sval (f α) q z J) e)
    exact ⟨fun h α z J hJ => (h α z J hJ).trans (key α z J hJ), fun h α z J hJ => (h α z J hJ).trans (key α z J hJ).symm⟩

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformisation_polarised_abelianSchemes_iso : GlobalFnsSt → SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ.hom.left)), (w.IsGen ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL')) := by
  first | exact @GlobalTheory.unifPre_polarised_iso | exact GlobalTheory.unifPre_polarised_iso | (intros; apply GlobalTheory.unifPre_polarised_iso <;> assumption)
end
