module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle150
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubstitutionBilinearFormTransform
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle154
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle160
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle159
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle158
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle005
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle033
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import GroundTheory.FunctionField.PlaceDefs
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle161
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricNumberZeroFinrank
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.exists_snc_model_of_patches : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (B : Set (Cpt ξ)), CoordTie ℤ ξ x → (∀ p ∈ B, Char0 ξ p) → (∀ p, Char0 ξ p → ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A), IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p)) → ∃ bd : Ideal (MRing (fun _ : Unit => Fin (N + 1))), Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) z w → (w ∈ mcPts bd ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.exists_isSncModel_of_patches | exact GlobalTheory.CompanionTheory.Ar.SncBase.exists_isSncModel_of_patches | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.exists_isSncModel_of_patches <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.substitution_bilinear_form_transform : ∀ (R : Type) [CommRing R] (d d' : ℕ) (Qs : Fin d' → PS R 1 d) (f : PS R 2 d'), (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → AxOne f → AxOne (subQ Qs f) ∧ bil (subQ Qs f) 1 1 = (linQ Qs).transpose * bil f 1 1 * linQ Qs := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ.bil_axOne_subQ | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ.bil_axOne_subQ | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ.bil_axOne_subQ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem exists_sec_cleared : ∀ {R Rm : Type} [CommRing R] [CommRing Rm] [Algebra R Rm] (Mn : Submonoid R) [IsLocalization Mn Rm] {X X' Y : Scheme.{0}} {π : X' ⟶ Spec (CommRingCat.of R)} {π' : Y ⟶ Spec (CommRingCat.of Rm)} {κ : Y ⟶ X'}, IsPullback κ π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))) → ∀ [CompactSpace X'] [QuasiSeparatedSpace X'] {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}, PGen w → L.IsLB → L'.IsLB → ∀ (th : Out.H0 L 1) (ψ : Y ⟶ X) (n : ℕ) (u : FG L Y), (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), u.sum U h = h ψ * (h (κ ≫ F) ^ n)⁻¹) → ∃ (s : Out.H0 L' n), ∃ t ∈ Mn, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' → (gw w (r ≫ κ) z (J ((r ≫ κ) ≫ F)) (J' (r ≫ κ)) ^ n).val * sval s (r ≫ κ) z J' = GlobalTheory.TwistLoc.gc (r ≫ κ ≫ π) z t * (sval th (r ≫ ψ) z J * ((u.v r z J)⁻¹).val) := by
  intro R Rm _ _ _ Mn _ X X' Y π π' κ H _ _ L L' F w hw hL hL' th ψ n u hu
  have fe : FormEq (Sum.elim (fun k : Fin 1 => ψ ≫ (fun _ : Fin 1 => 𝟙 X) k) u.inv.φ)
      (Sum.elim (fun _ : Fin 1 => ((1 : ℕ) : ℤ)) u.inv.ε)
      (fun _ : Fin 1 => κ ≫ 𝟙 X' ≫ F) (fun _ : Fin 1 => (n : ℤ)) := fun U _ h => by
    have e := FG.sum_inv U u h
    rw [hu U h] at e
    have e' : ∏ k, h (u.inv.φ k) ^ u.inv.ε k = (h ψ * (h (κ ≫ F) ^ n)⁻¹)⁻¹ := e
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, e', Fintype.prod_unique, Category.comp_id, Category.id_comp, Nat.cast_one,
      zpow_one, zpow_natCast, mul_inv, inv_inv, mul_inv_cancel_left]
  obtain ⟨s', hs'⟩ := exists_sec hL fe (pullMulSec th ψ u.inv.t u.inv.ht)
  obtain ⟨t, ht, σ, hσ⟩ := GlobalTheory.TwistLoc.exists_clear_denominator Mn H hL (fun _ : Fin 1 => 𝟙 X' ≫ F)
    (fun _ => (n : ℤ)) s'
  obtain ⟨a, ha⟩ := GlobalTheory.SecPull.exists_down_sec hw hL hL' (fun _ : Fin 1 => 𝟙 X') (fun _ : Fin 1 => 𝟙 X' ≫ F)
    (fun _ => (n : ℤ)) (𝟙 X') (fun _ => by simp) σ
  refine ⟨a, t, ht, fun Z r z J J' hJ hJ' => ?_⟩
  let p : Fin 1 → L.ι := fun _ => J ((r ≫ κ) ≫ F)
  let q : Fin 1 → L'.ι := fun _ => J' (r ≫ κ)
  have m₁ : (r ≫ κ) z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X' ≫ F) p :=
    Set.mem_iInter.2 fun _ => hJ ((r ≫ κ) ≫ F)
  have m₂ : (r ≫ κ) z ∈ LB.wchart L' (fun _ : Fin 1 => 𝟙 X') q := Set.mem_iInter.2 fun _ => hJ' (r ≫ κ)
  have m₃ : r z ∈ LB.wchart L (fun _ : Fin 1 => κ ≫ 𝟙 X' ≫ F) p :=
    Set.mem_iInter.2 fun _ => hJ ((r ≫ κ) ≫ F)
  have e₁ := ha Z (r ≫ κ) z p q m₁ m₂
  rw [Category.comp_id] at e₁
  have e₂ := hσ Z r z p m₃
  have e₃ : pw w (fun _ : Fin 1 => 𝟙 X') (fun _ => (n : ℤ)) (r ≫ κ) z p q = gw w (r ≫ κ) z (J ((r ≫ κ) ≫ F)) (J' (r ≫ κ)) ^ n := by
    simp only [pw, Fintype.prod_unique, Category.comp_id, zpow_natCast, p, q]
  have e₄ : sval s' r z J = gs r z (LB.wchart L (fun _ : Fin 1 => κ ≫ 𝟙 X' ≫ F) p) (s'.f p) := sval_of s' r z J p fun _ => by
    simp only [p, Category.assoc, Category.id_comp]
  rw [sval_of a (r ≫ κ) z J' q (fun _ => by simp only [q, Category.comp_id]), ← e₃, e₁, ← _root_.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, _root_.one_mul, e₂, ← e₄, hs' Z r z J hJ,
    sval_pullMulSec _ _ _ _ r z hJ, show val u.inv.t r z J = (u.v r z J)⁻¹ from FG.v_inv u r]

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem exists_lin_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    {T : Over S} (x a : T ⟶ G) (m : ℕ) (hx : x ^ m = 1) :
    ∃ v : FG L.L T.left, (∀ (U : Type) [CommGroup U] (h : (T.left ⟶ G.left) → U),
        v.sum U h = h (x * a ^ m).left * (h (a ^ m).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left) ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → ρ ≫ a = 1 → v.v ρ.left z J = 1 := by
  obtain ⟨t₂, ht₂, v₂⟩ := exists_cubN c (1 : T ⟶ G) a x m
  obtain ⟨t₁, ht₁, v₁⟩ := exists_cubN c (1 : T ⟶ G) x a m
  refine ⟨FG.mul ⟨Fin 8, _, _, t₂, ht₂⟩ (FG.inv ⟨Fin 8, _, _, t₁, ht₁⟩), fun U _ h => ?_, fun T' ρ z J hJ hρ => ?_⟩
  · rw [FG.sum_mul, FG.sum_inv]
    simp only [FG.sum, Fin.prod_univ_succ, Fin.prod_univ_zero]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, hx,
      _root_.one_mul, _root_.mul_one, mul_comm a x, mul_comm (a ^ m) x]
    apply Additive.ofMul.injective
    simp [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  · rw [FG.v_mul hJ, FG.v_inv]
    show val t₂ ρ.left z J * (val t₁ ρ.left z J)⁻¹ = 1
    rw [v₂ T' ρ z J hJ, v₁ T' ρ z J hJ, hρ, (isCub_cubV c hJ).N_one]
    have : cubN (cubV c z J) m (ρ ≫ (1 : T ⟶ G)) 1 (ρ ≫ x) = 1 :=
      Finset.prod_eq_one fun _ _ => (isCub_cubV c hJ).face₂ _ _ |>.symm ▸ rfl
    rw [this]
    simp

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

theorem _root_.GlobalTheory.T.intersection_second : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (R S : Type) [CommRing R] [Nontrivial R] [CommRing S] (f : R →+* S) (d r : ℕ) (B : Germ.FB R d (𝓞 E)) (B₂ : Germ.FB S d (𝓞 E)) (x : Fin r → (Fin d → R) × (Fin d → R)), IsMapOf f B B₂ → IsHBasis B x → IsHBasis B₂ (fun j => vmap f (x j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isHBasis_map | exact GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isHBasis_map | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isHBasis_map <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

theorem _root_.GlobalTheory.T.hodge_lattice_germ_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (σ : E →+* Ω) (u : Fin r → (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)), IsCptGen ξ → S.Gives 𝓗 → (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → ∀ p : Cpt ξ, ∃ (x : Fin r → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) (A : Matrix (Fin r) (Fin r) Ω), IsHBasis (S.g p).B x ∧ (𝓗.quot σ).IsFrameAt (fun j => ∑ l, A j l • u l) p ∧ ∀ j, HT.eigProj 𝓗.ρH σ (toH S p (x j)) = ∑ l, A j l • u l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame.exists_basis_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame.exists_basis_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame.exists_basis_frame <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sandwich

open NumberField Polynomial GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E]

theorem exists_uniform_factor (w : 𝓞 E) :
    ∃ x : 𝓞 E, x ≠ 0 ∧ ∀ (Ω : Type) [Field Ω] (V : Type) [AddCommGroup V] [Module Ω V]
      (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω),
      ∃ T ∈ opRing ρ σ, (ρ w - scal V σ w) * T = 0 ∧ ∀ v, ρ w v = σ w • v → T v = σ x • v := by
  obtain ⟨f, -, hroot, hder⟩ := exists_sep_poly w
  have key : ∀ p : ℤ[X], eval₂ (Int.castRingHom (𝓞 E)) w p = aeval w p := fun p => by
    rw [aeval_def, algebraMap_int_eq]
  have hF : (f.map (Int.castRingHom (𝓞 E))).IsRoot w := by
    rw [IsRoot, eval_map, key]
    exact hroot
  set g := f.map (Int.castRingHom (𝓞 E)) /ₘ (X - C w) with hg
  have hfac : (X - C w) * g = f.map (Int.castRingHom (𝓞 E)) :=
    (mul_divByMonic_eq_iff_isRoot).2 hF
  refine ⟨g.eval w, ?_, ?_⟩
  · have hd : (derivative (f.map (Int.castRingHom (𝓞 E)))).eval w = g.eval w := by
      rw [← hfac, derivative_mul]
      simp
    rw [← hd, derivative_map, eval_map, key]
    exact hder
  · intro Ω _ V _ _ ρ σ
    refine ⟨eval₂ (scal V σ) (ρ w) g, eval₂_mem_opRing ρ σ w g, ?_, ?_⟩
    · have hcomm : ∀ k, Commute (scal V σ (g.coeff k)) (ρ w) :=
        fun k => commute_scal σ (g.coeff k) (ρ w)
      have h1 : ρ w - scal V σ w = eval₂ (scal V σ) (ρ w) (X - C w) := by
        simp [eval₂_sub]
      rw [h1, ← eval₂_mul_noncomm _ _ hcomm, hfac, eval₂_map]
      have hc : (scal V σ).comp (Int.castRingHom (𝓞 E)) = ρ.comp (Int.castRingHom (𝓞 E)) :=
        RingHom.ext_int _ _
      rw [hc, ← hom_eval₂, key, hroot, map_zero]
    · intro v hv
      exact eval₂_apply_of_eigen ρ σ w hv g

private theorem mem_eigSp_iff_geometry {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω) (v : V) :
    v ∈ eigSp ρ σ ↔ ∀ a, ρ a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem exists_uniform_product (W : Finset (𝓞 E)) :
    ∃ x : 𝓞 E, x ≠ 0 ∧ ∀ (Ω : Type) [Field Ω] (V : Type) [AddCommGroup V] [Module Ω V]
      (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω),
      ∃ T ∈ opRing ρ σ, (∀ w ∈ W, (ρ w - scal V σ w) * T = 0) ∧ ∀ v ∈ eigSp ρ σ, T v = σ x • v := by
  classical
  induction W using Finset.induction_on with
  | empty =>
    refine ⟨1, one_ne_zero, ?_⟩
    intro Ω _ V _ _ ρ σ
    exact ⟨1, (opRing ρ σ).one_mem, by simp, fun v _ => by simp⟩
  | @insert a W' ha ih =>
    obtain ⟨x', hx', hT'⟩ := ih
    obtain ⟨xa, hxa, hTa⟩ := exists_uniform_factor a
    refine ⟨xa * x', mul_ne_zero hxa hx', ?_⟩
    intro Ω _ V _ _ ρ σ
    obtain ⟨T', hT'm, hT'k, hT'e⟩ := hT' Ω V ρ σ
    obtain ⟨Ta, hTam, hTak, hTae⟩ := hTa Ω V ρ σ
    refine ⟨Ta * T', (opRing ρ σ).mul_mem hTam hT'm, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw'
      · rw [← mul_assoc, hTak, zero_mul]
      · have hc : Commute (ρ w - scal V σ w) Ta :=
          (commute_opRing hTam w).symm.sub_left (commute_scal σ w Ta)
        rw [← mul_assoc, hc.eq, mul_assoc, hT'k w hw', mul_zero]
    · intro v hv
      have hva : ρ a v = σ a • v := (mem_eigSp_iff_geometry ρ σ v).1 hv a
      change Ta (T' v) = _
      rw [hT'e v hv, map_smul, hTae v hva, smul_smul, map_mul, mul_comm (σ xa)]

theorem exists_eigen_op_uniform : ∀ (E : Type) [Field E] [NumberField E], ∃ D : ℕ, 0 < D ∧
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] (V : Type) [AddCommGroup V] [Module Ω V]
      (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω),
      ∃ T ∈ opRing ρ σ, (∀ v, T v ∈ eigSp ρ σ) ∧ ∀ v ∈ eigSp ρ σ, T v = (D : Ω) • v := by
  intro E _ _
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  obtain ⟨x, hx, hT⟩ := exists_uniform_product S
  have hint : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
  have hbot := Ideal.comap_ne_bot_of_integral_mem hx (Ideal.mem_span_singleton_self x) hint
  obtain ⟨c, hcmem, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, algebraMap_int_eq, eq_intCast] at hcmem
  obtain ⟨y0, hy0⟩ := hcmem
  obtain ⟨n, hn0, y, hy⟩ : ∃ n : ℕ, 0 < n ∧ ∃ y : 𝓞 E, x * y = (n : 𝓞 E) := by
    rcases Int.natAbs_eq c with h | h
    · refine ⟨c.natAbs, Int.natAbs_pos.2 hc0, y0, ?_⟩
      rw [← hy0]
      conv_lhs => rw [h]
      simp
    · refine ⟨c.natAbs, Int.natAbs_pos.2 hc0, -y0, ?_⟩
      rw [mul_neg, ← hy0]
      conv_lhs => rw [h]
      simp
  refine ⟨n, hn0, ?_⟩
  intro Ω _ _ V _ _ ρ σ
  obtain ⟨T, hTm, hTk, hTe⟩ := hT Ω V ρ σ
  have hall : ∀ v, ∀ a : 𝓞 E, ρ a (T v) = σ a • T v := by
    intro v a
    have ha : a ∈ Submodule.span ℤ (S : Set (𝓞 E)) := by
      rw [hS]
      trivial
    induction ha using Submodule.span_induction with
    | mem w hw =>
      have h := congrArg (fun U : Module.End Ω V => U v) (hTk w hw)
      change (ρ w - scal V σ w) (T v) = 0 at h
      rw [LinearMap.sub_apply, scal_apply, sub_eq_zero] at h
      exact h
    | zero => simp
    | add a b _ _ iha ihb =>
      rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, iha, ihb, add_smul]
    | smul m a _ ih =>
      rw [map_zsmul, map_zsmul, LinearMap.smul_apply, ih, smul_assoc]
  have hs : scal V σ y ∈ opRing ρ σ := by
    simpa using eval₂_mem_opRing ρ σ 0 (C y)
  refine ⟨scal V σ y * T, (opRing ρ σ).mul_mem hs hTm, ?_, ?_⟩
  · intro v
    change scal V σ y (T v) ∈ eigSp ρ σ
    rw [scal_apply]
    exact Submodule.smul_mem _ _ ((mem_eigSp_iff_geometry ρ σ (T v)).2 (hall v))
  · intro v hv
    change scal V σ y (T v) = _
    rw [scal_apply, hTe v hv, smul_smul, ← map_mul, mul_comm y x, hy, map_natCast]

end GlobalTheory.CompanionTheory.Ar.Sandwich
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)


theorem _root_.GlobalTheory.T.positive_homogeneous_potential : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P ⊤ D) (a : K → ℤ) (φ : ((Σ k, J k) → ℂ) → ℝ), (∀ z ∈ mcPts P, 0 < φ z) → (∀ z ∈ mcPts P, φ (fun p => starRingEnd ℂ (z p)) = φ z) → (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) → ∃ T : HermLine J, T.a = a ∧ IsSmoothHerm T ∧ IsConjInvariantH T ∧ (∀ z ∈ mcPts P, T.h z = φ z) ∧ IsFlatOn R T := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.FlatExt.exists_flat_line | exact GlobalTheory.CompanionTheory.Ar.Chg.FlatExt.exists_flat_line | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.FlatExt.exists_flat_line <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

theorem _root_.GlobalTheory.T.exists_multihomog_prime_of_place : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K) (v : Place (ZMod p) K) (c : ∀ k, J k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩)) → ∃ W : Ideal (MRing J), W.IsPrime ∧ IsMultiHomogIdeal W ∧ mCoordIdeal w ≤ W ∧ (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) ∧ Dom v w W ∧ ∀ (e : B → ℕ) (g : MRing J), IsMultiHomog g e → (g ∈ W ↔ v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre.exists_centre | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre.exists_centre | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre.exists_centre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem linked_two_levels : GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → HodgeLatticeFlagBound → TrivFlagOnHodge → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S S₀ : Finset ℕ) [Fintype (CMType H)] [DecidableEq (CMType H)] (M : RootModel (CMType H) (D.p + D.q)) [DecidableEq M.K] (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (R : SecondRoots M), Fl.TwoLevels S₀ R.pairs → (∀ p ∈ S, p ∉ S₀ → HT.HTFree 𝔐 p ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ NumberField.discr E) → ∀ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), (∀ p ∈ S, p ∉ S₀ → IsFrobLabels c p (φ p)) → R.pairs.IsVertOff M.P ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) ∧ R.LocalAtPlaces D.p ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) φ := by
  intro hseg hM3 hTriv E _ _ _ H D l Xo c O₀ _ β Y S S₀ _ _ M instK 𝔐 Fl R hTL hloc φ hφ
  obtain rfl : instK = (fun a b => Classical.propDecidable (a = b) : DecidableEq M.K) := Subsingleton.elim _ _
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, _, _, hvert⟩ := hTL
    exact hvert
  · obtain ⟨hded, hfin, hinj, hcst, -⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S M.Ω M.K M.ι M.y 𝔐 (dimFl (CMType H) (D.p + D.q)) M.arith (integralClosure ℤ M.Ω)
    refine ⟨integralClosure ℤ M.Ω, inferInstance, hded, hfin, inferInstance, hinj, hcst, ?_⟩
    intro p hp m _ hpm O _ _ _ _ _ _ _
    have hp' : (p : ℕ) ∈ S ∧ (p : ℕ) ∉ S₀ := Finset.mem_sdiff.1 (Finset.mem_preimage.1 hp)
    obtain ⟨hHT, h2, hd⟩ := hloc p hp'.1 hp'.2
    obtain ⟨_, _, _, e₀, e, _, hrl, _, _⟩ := id hTL
    refine ⟨?_, ?_⟩
    · exact hM3 E H D l Xo c O₀ β Y S M.Ω M.K M.ι M.y 𝔐 _ M.arith Fl S₀ R.pairs hTL p hp'.1 hp'.2 hHT h2 hd (φ p) (hφ p hp'.1 hp'.2) (integralClosure ℤ M.Ω) m hpm O
    · intro τ
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
      have hmod := (GlobalTheory.T.localization_model_over_place M.K M.ι M.Ω M.y (integralClosure ℤ M.Ω) hinj hcst _ M.arith m O).2.1
      exact GlobalTheory.T.power_sums_vanish_of_trivial_flags hseg O ϖ hϖ M.K M.ι _ _ hmod _ _ fun W hW =>
        hTriv E H D l Xo c O₀ β Y S M.Ω M.K M.ι M.y 𝔐 _ M.arith Fl R.pairs.x' e hrl p hp'.1 hHT (integralClosure ℤ M.Ω) m hpm O τ W hW

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

theorem _root_.GlobalTheory.T.geometric_number_zero_finrank : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 → ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ (b : Fin 0 → B → ℤ) [IsLocalRing (locRing (mCoordIdeal w) W)] [Algebra (ZMod p) (locRing (mCoordIdeal w) W)], geoNum 0 W b = (Module.finrank (ZMod p) (ResidueField (locRing (mCoordIdeal w) W)) : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg.geoNum_zero_eq_finrank | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg.geoNum_zero_eq_finrank | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg.geoNum_zero_eq_finrank <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

theorem _root_.GlobalTheory.T.multihomog_prime_mem_divisor_support : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (W : Ideal (MRing J)) (c : ∀ k, J k), W.IsPrime → IsMultiHomogIdeal W → mCoordIdeal w ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) → ∀ (k : B) (c₀ : J k), w ⟨k, c₀⟩ ≠ 0 → (X ⟨k, c₀⟩ : MRing J) ∈ W → W ∈ (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c₀⟩ : MRing J)}).minimalPrimes := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin.mem_minimalPrimes_of_coord | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin.mem_minimalPrimes_of_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin.mem_minimalPrimes_of_coord <;> assumption)
end
