module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

private theorem eta_comp_mul_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : η[G] ≫ (𝟙 G * 𝟙 G) = η[G] := by
  rw [Hom.mul_def, ← Category.assoc, comp_lift, Category.comp_id]
  simpa using lift_comp_one_left (𝟙 _) η[G]

private theorem unitSec_comp_sqr {S : Scheme.{0}} (G : Over S) [GrpObj G] : unitSec G ≫ sqr G = unitSec G :=
  congrArg (·.left) (eta_comp_mul_self G)

theorem sqr_sub_two_mem : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], QuasiSeparated G.hom → ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2 := by
  intro S G _ hqs s π ε m hd f hf
  haveI := hqs
  obtain ⟨hπ, hε, hm⟩ := GlobalTheory.T.groupSchemeUnitStalkData_germ S G s π ε m hd
  have he : unitSec G ≫ G.hom = 𝟙 S := sec_hom η[G]
  obtain ⟨U₀, hU₀, g, rfl⟩ := G.left.presheaf.germ_exist f
  have hsq : sqr G (unitSec G s) = unitSec G s := by rw [← Scheme.Hom.comp_apply, unitSec_comp_sqr]
  have hb : G.hom (unitSec G s) = s := by rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨U₁, hU₁, hs₁, -⟩ := QCoh.exists_affine_mem_le (U := (⊤ : S.Opens)) s trivial
  obtain ⟨W₁, hW₁, hx₁, k₁⟩ := QCoh.exists_affine_mem_le
    (U := U₀ ⊓ sqr G ⁻¹ᵁ U₀ ⊓ G.hom ⁻¹ᵁ U₁) (unitSec G s)
    ⟨⟨hU₀, show sqr G (unitSec G s) ∈ U₀ by rw [hsq]; exact hU₀⟩,
      show G.hom (unitSec G s) ∈ U₁ by rw [hb]; exact hs₁⟩
  obtain ⟨U, hsU, -, -, c⟩ := GlobalTheory.Conormal.exists_isChart_inf he hU₁ hW₁ (k₁.trans inf_le_right) hx₁
    (show s ∈ (⊤ : S.Opens) from trivial)
  have kW : W₁ ⊓ G.hom ⁻¹ᵁ U ≤ U₀ := inf_le_left.trans (k₁.trans (inf_le_left.trans inf_le_left))
  have kS : W₁ ⊓ G.hom ⁻¹ᵁ U ≤ sqr G ⁻¹ᵁ U₀ :=
    inf_le_left.trans (k₁.trans (inf_le_left.trans inf_le_right))
  have hxW : unitSec G s ∈ W₁ ⊓ G.hom ⁻¹ᵁ U := c.le hsU
  have hU0 : U ≤ unitSec G ⁻¹ᵁ U₀ := c.le.trans ((unitSec G).preimage_mono kW)

  have a1 := cotMap_d (𝟙 G * 𝟙 G) (eta_comp_mul_self G) hU0 c.le kS g
  have a2 := cotMap_d (𝟙 G) (Category.comp_id _) hU0 c.le kW g
  have hmul := cotMap_mul (x := 𝟙 G) (y := 𝟙 G) (Category.comp_id η[G]) (Category.comp_id η[G]) (eta_comp_mul_self G)
  have key : GlobalTheory.Conormal.d he c.le ((sqr G).appLE U₀ _ kS g) =
      GlobalTheory.Conormal.d he c.le (resG G.left kW g) + GlobalTheory.Conormal.d he c.le (resG G.left kW g) := by
    have := congrArg (fun φ => φ.app U (GlobalTheory.Conormal.d he hU0 g)) hmul
    simp only at this
    exact (a1.symm.trans this).trans (congrArg₂ (· + ·) a2 a2)
  letI := c.algebra
  let h : Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) := (sqr G).appLE U₀ _ kS g - (resG G.left kW g + resG G.left kW g)
  have hz : AugCot.d (c.aug he) h = 0 := (c.augCotEquiv he).injective (by
    rw [c.augCotEquiv_d he, map_zero, map_sub, map_add (f := _), key, sub_self])
  rw [AugCot.d_eq_zero_iff] at hz
  let gW := G.left.presheaf.germ (W₁ ⊓ G.hom ⁻¹ᵁ U) (unitSec G s) hxW
  have g1 : gW ((sqr G).appLE U₀ _ kS g) = m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) :=
    (hm U₀ hU₀ _ hxW kS g).symm
  have g2 : gW (resG G.left kW g) = G.left.presheaf.germ U₀ (unitSec G s) hU₀ g :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have gh : gW h = m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) -
      2 * G.left.presheaf.germ U₀ (unitSec G s) hU₀ g := by
    simp only [h, map_sub, map_add (f := _), g1, g2, two_mul]
  have hf0 : ε (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) = 0 := hf
  have hker : ∀ x, c.aug he x = 0 → ε (gW x) = 0 := by
    intro x hx
    have hx' : (unitSec G).appLE _ U c.le x = 0 := hx
    rw [hε _ hxW U hsU c.le x, hx', map_zero]
  have hmap : ∀ y ∈ RingHom.ker (c.aug he) ^ 2, gW y ∈ RingHom.ker ε ^ 2 := by
    intro y hy
    have := Ideal.mem_map_of_mem (ConcreteCategory.hom gW) hy
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (RingHom.mem_ker.2 (hker x (RingHom.mem_ker.1 hx)))) 2 this
  have hεm : ε (m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g)) = 0 := by
    rw [← g1, hε _ hxW U hsU c.le, GlobalTheory.Conormal.appLE_appLE (unitSec_comp_sqr G) kS c.le hU0,
      ← hε U₀ hU₀ U hsU hU0 g, hf0]
  have hεh : ε (gW h) = 0 := by rw [gh, map_sub, map_mul, hεm, hf0, mul_zero, sub_zero]
  have halg : gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) = 0 := by
    have e1 : gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) =
        π (S.presheaf.germ U s hsU (c.aug he h)) := (hπ U hsU _ hxW c.le_base _).symm
    have e2 : S.presheaf.germ U s hsU (c.aug he h) = ε (gW h) := (hε _ hxW U hsU c.le h).symm
    rw [e1, e2, hεh, map_zero]
  rw [← gh, show gW h = gW (h - algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) +
      gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) by rw [← map_add (f := _), sub_add_cancel],
    halg, add_zero]
  exact hmap _ hz
end GlobalTheory.Nef
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_pushoutTorsorSection_every_point :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
      GlobalTheory.PtExt.HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b →
        ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ s : RootFn A D, IsSec n b x s :=
  @GlobalTheory.PtExt.PushSec.exists_isSec
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pDivGroup_cocycle_mem_cob_range_of_diagonalSum_zero : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (G : PDivGroup p R) (z : G.cocycles), diagSum R (G.A N) (p ^ N) (z.1 N) = 0 → z ∈ LinearMap.range G.cob := by
  first | exact @GlobalTheory.PtExt.cocycle_mem_range_cob_of_diagSum_eq_zero | exact GlobalTheory.PtExt.cocycle_mem_range_cob_of_diagSum_eq_zero | (intros; apply GlobalTheory.PtExt.cocycle_mem_range_cob_of_diagSum_eq_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem _root_.GlobalTheory.T.dualWeyl_gramDeterminant_le_dim_pow_dim : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → (onMat la).det ≠ 0 ∧ ‖(onMat la).det‖ ^ 2 ≤ (dim la : ℝ) ^ dim la := by
  first | exact @GlobalTheory.OnMatGram.norm_det_onMat_sq_le | exact GlobalTheory.OnMatGram.norm_det_onMat_sq_le | (intros; apply GlobalTheory.OnMatGram.norm_det_onMat_sq_le <;> assumption)
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.TSup

theorem evalAt_intVec {n : ℕ} (la : Fin n → ℕ) (y : Matrix (Fin n) (Fin n) ℂ) (j : Idx la) :
    evalAt y (map (Int.castRingHom ℂ) (intVec la j)) =
      ∑ i, onMat la i j * evalAt y (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ) := by
  rw [← coe_basis]
  have h : basis la ℂ j = ∑ i, onMat la i j • (toSpace la).symm (onBasis la i) := by
    apply (toSpace la).injective

    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply, onMat, Matrix.of_apply]
    exact ((onBasis la).sum_repr _).symm

  rw [h, Submodule.coe_sum, map_sum]
  simp [Submodule.coe_smul, map_smul]

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ}

theorem tval_eq_onb (la : ∀ t, Fin (N t) → ℕ) (z : TIdx la → ℂ) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) :
    tval la z y = ∑ J : TIdx la, ((kron fun t => onMat (la t)) *ᵥ z) J *
      ∏ t, evalAt (y t) (((toSpace (la t)).symm (onBasis (la t) (J t)) : nabla (la t) ℂ) : Pol (N t) ℂ) := by
  unfold tval
  simp_rw [evalAt_intVec, Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [Matrix.mulVec, dotProduct, kron, Matrix.of_apply, Finset.sum_mul, Finset.prod_mul_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  ring

theorem norm_sum_mul_le {ι : Type} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ i, a i * b i‖ ≤ Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  calc ‖∑ i, a i * b i‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp [norm_mul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem mul_norm_tval_le_fibNorm : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (x : TIdx la → ℂ) (X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) (u : ∀ t, UN (N t)) (s : ℝ), 0 ≤ s → s * ‖tval la x (fun t => X t * (u t).1)‖ ≤ Real.sqrt (∑ I, ‖(fibY la s X *ᵥ x) I‖ ^ 2) := by
  intro T _ _ N la hla x X u s hs
  have h1 : tval la x (fun t => X t * (u t).1) =
      tval la ((kron fun t => rhoMat (la t) (X t)) *ᵥ x) (fun t => (u t).1) := by
    have h := GlobalTheory.T.dualWeylTensorEvaluation_translate_kronecker T N la ℂ ℂ (RingHom.id ℂ) x X (fun t => (u t).1)
    simpa only [RingHom.id_apply, RingHom.coe_id, Matrix.map_id] using h
  have hk := (GlobalTheory.T.kroneckerProductFamily_mul_one_det T (fun t => Idx (la t)) ℂ (fun t => onMat (la t)) (fun t => rhoMat (la t) (X t))).1
  set E : TIdx la → ℂ := fun J => ∏ t, evalAt (u t).1
    (((toSpace (la t)).symm (onBasis (la t) (J t)) : nabla (la t) ℂ) : Pol (N t) ℂ) with hE
  have h2 : (s : ℂ) * tval la x (fun t => X t * (u t).1) = ∑ J, (fibY la s X *ᵥ x) J * E J := by
    rw [h1, tval_eq_onb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    have hsm : ∀ (M : Matrix (TIdx la) (TIdx la) ℂ) (v : TIdx la → ℂ), ((s : ℂ) • M) *ᵥ v = (s : ℂ) • (M *ᵥ v) := by
      intro M v
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [fibY, hsm, ← hk, ← Matrix.mulVec_mulVec, Pi.smul_apply, smul_eq_mul]
    ring
  have h3 : ∑ J, ‖E J‖ ^ 2 ≤ 1 := by
    have : ∑ J, ‖E J‖ ^ 2 = ∏ t, ∑ i, ‖evalAt (u t).1
        (((toSpace (la t)).symm (onBasis (la t) i) : nabla (la t) ℂ) : Pol (N t) ℂ)‖ ^ 2 := by
      rw [Fintype.prod_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      simp only [hE, norm_prod, Finset.prod_pow]
    rw [this]
    exact Finset.prod_le_one₀ (fun t _ => Finset.sum_nonneg fun _ _ => by positivity)
      (fun t _ => GlobalTheory.T.dualWeyl_orthonormal_basis_values_at_unitary_sum_sq_le_one (N t) (la t) (hla t) (u t))
  have h4 : s * ‖tval la x (fun t => X t * (u t).1)‖ = ‖(s : ℂ) * tval la x (fun t => X t * (u t).1)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  rw [h4, h2]
  refine (norm_sum_mul_le _ _).trans ?_
  calc _ ≤ Real.sqrt (∑ I, ‖(fibY la s X *ᵥ x) I‖ ^ 2) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        rw [Real.sqrt_le_one]
        exact h3
    _ = _ := mul_one _

end GlobalTheory.TSup

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge
namespace GlobalTheory.MBLow.TanGauge

theorem top_le_of_redE : ∀ (C : Type) [Field C] {X : Scheme.{0}} (y : Sp (DualNumber C) ⟶ X) (U : X.Opens),
    ⊤ ≤ (redE C ≫ y) ⁻¹ᵁ U → ⊤ ≤ y ⁻¹ᵁ U := by
  intro C _ X y U h q _
  have key : ∃ p : (Sp C : Scheme.{0}), (redE C) p = q := by
    have hsub : Subsingleton (PrimeSpectrum (DualNumber C)) := by
      refine ⟨fun a b => ?_⟩
      have aux : ∀ a : PrimeSpectrum (DualNumber C), ∀ x, x ∈ a.asIdeal ↔ x.fst = 0 := by
        intro a x
        constructor
        · intro hx
          by_contra hne
          exact a.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
            (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 hne)))
        · intro hx
          refine a.2.mem_of_pow_mem 2 ?_
          have : x ^ 2 = 0 := by
            ext <;> simp [sq, hx]
          rw [this]; exact zero_mem _
      ext x; rw [aux, aux]
    exact ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C), hsub.elim _ _⟩
  obtain ⟨p, rfl⟩ := key
  exact h (x := p) trivial
end GlobalTheory.MBLow.TanGauge
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.dualPointOverOrigin_lifts_tangentVector_uniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left), IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ →
    eSec x.P.A ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A →
    ∀ b : TE R ℂ ⟶ D.P.A, redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left →
      ∃ b' : epsR ℂ ⟶ x.P.A, IsTangent b' ∧ b'.left ≫ φ = b.left := by
  first | exact @GlobalTheory.MBLow.Cl.tangent_lift_of_pullback | exact GlobalTheory.MBLow.Cl.tangent_lift_of_pullback | (intros; apply GlobalTheory.MBLow.Cl.tangent_lift_of_pullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.powerSeriesDeformation_of_boundedLatticeSeries : ∀ (κ : Rule) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [CharZero C] (e : C →+* ℂ) (x : KeyIn C) (g : ℕ) (hg : x.P.g = g) (m : ℕ) (ζ : Cˣ)
    (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) (X : Type) (n : X → ℕ) (π : C) (B : ℝ)
    (a : (Fin (2 * g) → ZMod (m ^ 2)) → X → C) (b : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → X → C),
    π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ i α, ‖a i α‖ ≤ B * ‖π‖ ^ n α) →
    (∀ i j α, ‖b i j α‖ ≤ B * ‖π‖ ^ n α) →
    ThJet x hg m (levelPoint lev hg) (fun i => ∑' α, a i α) (fun i j => ∑' α, b i j α) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      ((∀ i, Summable fun α => ‖e (a i α) * u ^ n α‖) ∧ ∀ i j, Summable fun α => ‖e (b i j α) * u ^ n α‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun i => ∑' α, e (a i α) * u ^ n α)
          (fun i j => ∑' α, e (b i j α) * u ^ n α) ∧ (κ ℂ x₀ : ℂ) = e k) →
    Deform κ e x hg m ζ lev k := by
  first | exact @GlobalTheory.MBLow.deform_of_lattice_series | exact GlobalTheory.MBLow.deform_of_lattice_series | (intros; apply GlobalTheory.MBLow.deform_of_lattice_series <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.section_value_eq_at_first_order_of_tangents : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (P : PolAV (Sp K))
    (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))))
    (i₀ : P.L.ι), ⊤ ≤ (spMap (algebraMap K C) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ →
    ∀ (v w : epsR K ⟶ P.A), IsTangent v → IsTangent w →
    ∀ (yv yw : Sp (DualNumber C) ⟶ (Over.mk (spMap (algebraMap K C)) ⊗ P.A).left),
      yv ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yv ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ v.left →
      yw ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yw ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ w.left →
    ∀ (a b a' b' : C),
      valR yv ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) →
      valR yw ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a' + TrivSqZeroExt.inr b') → a = a' := by
  intro K C hK hC hKC P ρ k t i₀ hi v w hv hw yv yw hv1 hv2 hw1 hw2 a b a' b' ev ew
  exact @GlobalTheory.TangentFirstOrder.fst_eq_of_tangent K C hK hC hKC P ρ k t i₀ hi v w hv hw yv yw hv1 hv2 hw1 hw2 a b a' b' ev ew
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_abelianKeyValue_norm_one : ∀ κ : Rule, Rule4 κ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] (D : DegPre V) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D C N), ν.IntN → ∀ vB : Fin D.P.g → (epsR V ⟶ D.P.A), IsLieBasis vB → ∃ k : C, BKey κ ν vB k ∧ ‖k‖ = 1 := by
  first | exact @GlobalTheory.MBLow.AbKey.exists_bKey | exact GlobalTheory.MBLow.AbKey.exists_bKey | (intros; apply GlobalTheory.MBLow.AbKey.exists_bKey <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianKeyValue_adaptedVectors_fieldIso : ∀ κ : Rule, Funct κ → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Field F'] [CharZero F] [CharZero F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (e : F ≃+* F'), (∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ (N : NumD F) (ν : NumOf D F N) (N' : NumD F') (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N'), (∀ x, I.h x = 1) → I.lam = 1 → (∀ χ, ν'.eX (I.e χ) = ν.eX χ) → ν'.th = ν.th → (∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J)) → ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ k, BKey κ ν vB k → BKey κ ν' vB (e k)) ∧ ∀ (r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R F)), Adapted ν vB bX σ gm → ∃ gm' : Fin g → GtPt D (TE R F'), (∀ j, GtPt.IsPull (spMap (dualMap (e : F →+* F'))) (gm j) (gm' j)) ∧ Adapted ν' vB (bX.map I.e.toIntLinearEquiv) σ gm' := by
  exact @GlobalTheory.MBLow.bKey_adapted_map
end
