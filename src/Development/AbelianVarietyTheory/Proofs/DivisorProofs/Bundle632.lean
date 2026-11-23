module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.TangentStalk

theorem ker_eq_maximalIdeal {k R : Type} [Field k] [CommRing R] [IsLocalRing R] (j : k →+* R)
    (g : R →+* k) (hg : g.comp j = RingHom.id k) : RingHom.ker g = IsLocalRing.maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g
    (fun c => ⟨j c, RingHom.congr_fun hg c⟩))

theorem ringHom_eq_of_comp_eq_id {k R : Type} [Field k] [CommRing R] [IsLocalRing R] (j : k →+* R)
    (g₁ g₂ : R →+* k) (h₁ : g₁.comp j = RingHom.id k) (h₂ : g₂.comp j = RingHom.id k) : g₁ = g₂ := by
  ext a
  have hm : a - j (g₁ a) ∈ RingHom.ker g₂ := by
    rw [ker_eq_maximalIdeal j g₂ h₂, ← ker_eq_maximalIdeal j g₁ h₁, RingHom.mem_ker, map_sub,
      show g₁ (j (g₁ a)) = g₁ a from RingHom.congr_fun h₁ (g₁ a), sub_self]
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
  rw [hm]
  exact (RingHom.congr_fun h₂ (g₁ a)).symm

theorem tangent_eq_stalk_dual : ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (x₀ : A.left), x₀ ∈ Set.range (η[A]).left.base →
    ∃ jk : k →+* A.left.presheaf.stalk x₀,
      (∀ a : A.left.presheaf.stalk x₀, ∃ c : k, a - jk c ∈ IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀)) ∧
      (∀ ψ : A.left.presheaf.stalk x₀ →+* DualNumber k, ψ.comp jk = algebraMap k (DualNumber k) →
        ∃ v : epsR k ⟶ A, IsTangent v ∧ v.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ∧
      (∀ ψ₁ ψ₂ : A.left.presheaf.stalk x₀ →+* DualNumber k, ψ₁.comp jk = algebraMap k (DualNumber k) →
        ψ₂.comp jk = algebraMap k (DualNumber k) →
        Spec.map (CommRingCat.ofHom ψ₁) ≫ A.left.fromSpecStalk x₀ = Spec.map (CommRingCat.ofHom ψ₂) ≫ A.left.fromSpecStalk x₀ →
        ψ₁ = ψ₂) := by
  intro k _ A _ x₀ hx
  obtain ⟨pt, rfl⟩ := hx
  have hpt : pt = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
  subst hpt
  let s : Sp k ⟶ A.left := (η[A]).left
  have hsA : s ≫ A.hom = 𝟙 _ := (η[A]).w.trans rfl
  have hr : Spec.map (Scheme.stalkClosedPointTo s) ≫ A.left.fromSpecStalk _ = s :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk s
  have hJ := Spec.map_preimage (A.left.fromSpecStalk (s.base (IsLocalRing.closedPoint k)) ≫ A.hom)

  set r := Scheme.stalkClosedPointTo s with hrdef
  set J := Spec.preimage (A.left.fromSpecStalk (s.base (IsLocalRing.closedPoint k)) ≫ A.hom) with hJdef
  have hrJ : J ≫ r = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hJ, ← Category.assoc, hr, hsA, Spec.map_id]
  have hcomp : r.hom.comp J.hom = RingHom.id k := congrArg CommRingCat.Hom.hom hrJ
  have hfst : ∀ ψ : A.left.presheaf.stalk (s.base (IsLocalRing.closedPoint k)) →+* DualNumber k,
      ψ.comp J.hom = algebraMap k (DualNumber k) →
      ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ψ).comp J.hom = RingHom.id k := by
    intro ψ hψ
    rw [RingHom.comp_assoc, hψ]
    ext c
    simp
  refine ⟨J.hom, fun a => ⟨r.hom a, ?_⟩, fun ψ hψ => ?_, fun ψ₁ ψ₂ h₁ h₂ h => ?_⟩
  · rw [← ker_eq_maximalIdeal J.hom r.hom hcomp, RingHom.mem_ker, map_sub,
      show r.hom (J.hom (r.hom a)) = r.hom a from RingHom.congr_fun hcomp _, sub_self]
  · refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _) ?_, ?_, rfl⟩
    · show Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _ ≫ A.hom =
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
      rw [← hJ, ← Spec.map_comp, ← hψ]
      rfl
    · show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
        Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _ = s
      rw [← Category.assoc, ← Spec.map_comp, ← hr]
      congr 2
      ext1
      exact ringHom_eq_of_comp_eq_id J.hom _ _ (hfst ψ hψ) hcomp
  · have hloc : ∀ ψ : A.left.presheaf.stalk (s.base (IsLocalRing.closedPoint k)) →+* DualNumber k,
        ψ.comp J.hom = algebraMap k (DualNumber k) → IsLocalHom ψ := by
      intro ψ hψ
      refine ⟨fun a ha => ?_⟩
      by_contra hna
      have hm : a ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hna)
      rw [← ker_eq_maximalIdeal J.hom _ (hfst ψ hψ), RingHom.mem_ker] at hm
      have hu := TrivSqZeroExt.isUnit_iff_isUnit_fst.1 ha
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        TrivSqZeroExt.fstHom_apply] at hm
      rw [hm] at hu
      exact not_isUnit_zero hu
    have e1 := hloc ψ₁ h₁
    have e2 := hloc ψ₂ h₂
    have hinj := (SpecToEquivOfLocalRing A.left (CommRingCat.of (DualNumber k))).symm.injective
      (a₁ := ⟨_, CommRingCat.ofHom ψ₁, e1⟩) (a₂ := ⟨_, CommRingCat.ofHom ψ₂, e2⟩) h
    have := eq_of_heq (Sigma.mk.inj_iff.mp hinj).2
    exact congrArg (fun f => f.1.hom) this
end GlobalTheory.TangentStalk
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace PullUnifHom

open GlobalTheory.PullHermitian

variable {X Y : Scheme.{0}}

lemma chart_pull_iff' (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (j : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull f).U j ↔ ⊤ ≤ (x ≫ f) ⁻¹ᵁ L.U (j PUnit.unit) :=
  ⟨fun h _ hp => Set.mem_iInter.1 (h hp) PUnit.unit, fun h _ hp => Set.mem_iInter.2 fun _ => h hp⟩

lemma le_left' {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ U :=
  h.trans (fun _ hp => And.left hp)

lemma le_right' {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ V :=
  h.trans (fun _ hp => And.right hp)

lemma valAt'_pull_g' (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (i j : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.pull f).U i ⊓ (L.pull f).U j)) :
    valAt' x ((L.pull f).U i ⊓ (L.pull f).U j) ((L.pull f).g i j).val =
      valAt' (x ≫ f) (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))
        (L.g (i PUnit.unit) (j PUnit.unit)).val := by
  have hi := (chart_pull_iff' x L f i).1 (le_left' h)
  have hj := (chart_pull_iff' x L f j).1 (le_right' h)
  rw [valAt'_eq_unitVal x h, valAt'_eq_unitVal _ (inf_of _ hi hj)]
  have := unitVal_linComb x L f 1 (i PUnit.unit) (j PUnit.unit) h (inf_of _ hi hj)
  exact congrArg Units.val (this.trans (zpow_one _))

theorem exists_holUnif_pull_hom : ∀ (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B] (φ : A ⟶ B) (L : LB B.left) (g : ℕ) (u' : HolUnif B L g)
    (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ' : u'.Λ → ℂ),
    (∀ z w, ex (z + w) = ex z * ex w) → Function.Surjective ex → (∀ z, ex z = 1 ↔ z ∈ Λ) →
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (ex z).left U f) {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U}) →
    (∀ z, ex z ≫ φ = u'.ex z) → Λ ≤ u'.Λ → u'.IsAH Hm χ' →
    ∃ (u : HolUnif A (L.pull φ.left) g) (χ : u.Λ → ℂ), (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧ u.IsAH Hm χ := by
  intro A B _ _ φ L g u' ex Λ Hm χ' hadd honto hker hdisc hfull hhol hφ hΛ hAH
  have keyl : ∀ z, (ex z).left ≫ φ.left = (u'.ex z).left := fun z => by rw [← Over.comp_left, hφ]
  have hch : ∀ (j : (L.pull φ.left).ι) z, (⊤ ≤ (ex z).left ⁻¹ᵁ (L.pull φ.left).U j ↔
      ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)) := fun j z =>
    (chart_pull_iff' _ L _ j).trans (iff_of_eq (by rw [keyl z]))
  let u : HolUnif A (L.pull φ.left) g :=
    ⟨ex, hadd, honto, Λ, hker, hdisc, hfull, hhol, fun j z => u'.fr (j PUnit.unit) z,
     fun j => (u'.fr_hol (j PUnit.unit)).mono (fun z hz => (hch j z).1 hz),
     fun j z hz => u'.fr_ne _ _ ((hch j z).1 hz),
     fun i j z h => by
        have hi := (hch i z).1 (le_left' h)
        have hj := (hch j z).1 (le_right' h)
        show u'.fr (i PUnit.unit) z = _ * u'.fr (j PUnit.unit) z
        rw [valAt'_pull_g' _ L _ i j h, keyl z]
        exact u'.fr_compat _ _ _ (inf_of _ hi hj)⟩
  refine ⟨u, fun l => χ' ⟨l.1, hΛ l.2⟩, fun w => Iff.rfl, ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hAH
  exact ⟨h1, h2, fun l => h3 _, fun l i z hz => h4 ⟨l.1, hΛ l.2⟩ (i PUnit.unit) z ((hch i z).1 hz)⟩

end PullUnifHom
end GlobalTheory
end
end

section

open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PosOpen

theorem hermForm_smul_real {g : ℕ} (N : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (z : Fin g → ℂ) :
    hermForm N ((r : ℂ) • z) ((r : ℂ) • z) = ((r * r : ℝ) : ℂ) * hermForm N z z := by
  simp only [hermForm, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  simp [Complex.conj_ofReal]
  ring

theorem posopen : ∀ {g : ℕ} (M₀ : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M₀ z z).re) →
    ∀ᶠ C in nhds (0 : Matrix (Fin g) (Fin g) ℂ), (1 - C.map star * C).det ≠ 0 ∧ (1 - C * C.map star).det ≠ 0 ∧
      ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (M₀ * (1 - C.map star * C)⁻¹) z z).re := by
  intro g M₀ hM
  have cA : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => 1 - C.map star * C :=
    continuous_const.sub ((continuous_id.matrix_map continuous_star).matrix_mul continuous_id)
  have cB : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => 1 - C * C.map star :=
    continuous_const.sub (continuous_id.matrix_mul (continuous_id.matrix_map continuous_star))
  have dA : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => (1 - C.map star * C).det := cA.matrix_det
  have dB : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => (1 - C * C.map star).det := cB.matrix_det
  have dA0 : (1 - (0 : Matrix (Fin g) (Fin g) ℂ).map star * 0).det ≠ 0 := by simp
  have dB0 : (1 - (0 : Matrix (Fin g) (Fin g) ℂ) * (0 : Matrix (Fin g) (Fin g) ℂ).map star).det ≠ 0 := by simp
  have e1 := dA.continuousAt.eventually_ne dA0
  have e2 := dB.continuousAt.eventually_ne dB0

  have cInv : ContinuousAt (fun C : Matrix (Fin g) (Fin g) ℂ => M₀ * (1 - C.map star * C)⁻¹) 0 := by
    have h1 : (fun C : Matrix (Fin g) (Fin g) ℂ => M₀ * (1 - C.map star * C)⁻¹) =
        fun C => M₀ * (((1 - C.map star * C).det)⁻¹ • (1 - C.map star * C).adjugate) := by
      funext C
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h1]
    refine continuousAt_const.mul (ContinuousAt.smul (dA.continuousAt.inv₀ dA0) cA.matrix_adjugate.continuousAt)
  have cH : Continuous fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (hermForm p.1 p.2 p.2).re :=
    Complex.continuous_re.comp (continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd.star))
  have tube : ∀ᶠ C in nhds (0 : Matrix (Fin g) (Fin g) ℂ), ∀ y ∈ Metric.sphere (0 : Fin g → ℂ) 1,
      0 < (hermForm (M₀ * (1 - C.map star * C)⁻¹) y y).re := by
    refine (isCompact_sphere (0 : Fin g → ℂ) 1).eventually_forall_of_forall_eventually fun y hy => ?_
    have cF : ContinuousAt (fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) =>
        (hermForm (M₀ * (1 - p.1.map star * p.1)⁻¹) p.2 p.2).re) (0, y) := by
      have : ContinuousAt (fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) =>
          (M₀ * (1 - p.1.map star * p.1)⁻¹, p.2)) (0, y) :=
        (ContinuousAt.comp (x := ((0 : Matrix (Fin g) (Fin g) ℂ), y))
          (f := (Prod.fst : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) → Matrix (Fin g) (Fin g) ℂ)) cInv
          continuousAt_fst).prodMk continuousAt_snd
      exact ContinuousAt.comp (x := ((0 : Matrix (Fin g) (Fin g) ℂ), y))
        (g := fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (hermForm p.1 p.2 p.2).re)
        (f := fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (M₀ * (1 - p.1.map star * p.1)⁻¹, p.2))
        cH.continuousAt this
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have v0 : 0 < (hermForm (M₀ * (1 - (0 : Matrix (Fin g) (Fin g) ℂ).map star * 0)⁻¹) y y).re := by
      simpa using hM y hy0
    exact cF.eventually (lt_mem_nhds v0)
  filter_upwards [e1, e2, tube] with C h1 h2 h3
  refine ⟨h1, h2, fun z hz => ?_⟩
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu : ((‖z‖⁻¹ : ℝ) : ℂ) • z ∈ Metric.sphere (0 : Fin g → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have := h3 _ hu
  rw [hermForm_smul_real, Complex.re_ofReal_mul] at this
  exact pos_of_mul_pos_right this (by positivity)

end GlobalTheory.PosOpen
end

section

open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PeriodCoord

private theorem inv_mul_eq_mul_inv_of_intertwine {n : Type} [Fintype n] [DecidableEq n]
    (A B D : Matrix n n ℂ) (hA : A.det ≠ 0) (hD : D.det ≠ 0) (h : B * D = A * B) :
    A⁻¹ * B = B * D⁻¹ := by
  have hA' : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hD' : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  calc A⁻¹ * B = A⁻¹ * (B * D) * D⁻¹ := by
          rw [Matrix.mul_assoc A⁻¹, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hD', Matrix.mul_one]
    _ = A⁻¹ * A * B * D⁻¹ := by rw [h, Matrix.mul_assoc A⁻¹ A B]
    _ = B * D⁻¹ := by rw [Matrix.nonsing_inv_mul _ hA', Matrix.one_mul]

private theorem star_dot_mulVec {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    star (x ⬝ᵥ A *ᵥ y) = star x ⬝ᵥ A.map star *ᵥ star y := by
  simp [dotProduct, mulVec, star_sum, Finset.mul_sum]

private theorem star_mulVec' {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (y : Fin g → ℂ) :
    star (A *ᵥ y) = A.map star *ᵥ star y := by
  funext i
  simp [mulVec, dotProduct, star_sum]

private theorem dot_left {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ Aᵀ *ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

private theorem map_star_mul' {g : ℕ} (A B : Matrix (Fin g) (Fin g) ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum]

private theorem map_star_map_star' {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) : (A.map star).map star = A := by
  ext i j; simp

private theorem conj_transpose_intertwine {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ) (hH : M₀ᴴ = M₀)
    (hS : (Cᵀ * M₀)ᵀ = Cᵀ * M₀) : (C.map star)ᵀ * Cᵀ * M₀ = M₀ * C.map star * C := by
  have f0 : M₀.map star = M₀ᵀ := by
    ext i j
    have := congrFun (congrFun hH j) i
    simpa [conjTranspose_apply] using this
  have f1 : M₀ᵀ * C = Cᵀ * M₀ := by rw [transpose_mul, transpose_transpose] at hS; exact hS
  have f1' : M₀ * C.map star = (C.map star)ᵀ * M₀ᵀ := by
    have := congrArg (fun A => A.map star) f1
    simp only [map_star_mul'] at this
    have e1 : (M₀ᵀ).map star = M₀ := by rw [transpose_map, f0, transpose_transpose]
    have e2 : (Cᵀ).map star = (C.map star)ᵀ := by rw [transpose_map]
    rw [e1, e2, f0] at this
    exact this
  rw [Matrix.mul_assoc, ← f1, ← Matrix.mul_assoc, ← f1']

theorem riemann_converse {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ) (hH : M₀ᴴ = M₀) (_hdet : M₀.det ≠ 0)
    (hS : (Cᵀ * M₀)ᵀ = Cᵀ * M₀) (hY : (1 - C.map star * C).det ≠ 0) :
    (M₀ * (1 - C.map star * C)⁻¹)ᴴ = M₀ * (1 - C.map star * C)⁻¹ ∧
      ∀ z w : Fin g → ℂ, (hermForm (M₀ * (1 - C.map star * C)⁻¹) (z + C *ᵥ star z) (w + C *ᵥ star w)).im =
        (hermForm M₀ z w).im := by
  set Y := 1 - C.map star * C with hYdef
  set M := M₀ * Y⁻¹ with hMdef
  have f2 := conj_transpose_intertwine M₀ C hH hS
  have f1 : M₀ᵀ * C = Cᵀ * M₀ := by rw [transpose_mul, transpose_transpose] at hS; exact hS
  have hYh : Yᴴ = 1 - (C.map star)ᵀ * Cᵀ := by
    rw [hYdef, conjTranspose_sub, conjTranspose_one, conjTranspose_mul]
    congr 2
    · ext i j; simp
  have hYt : Yᵀ = 1 - Cᵀ * (C.map star)ᵀ := by
    rw [hYdef, transpose_sub, transpose_one, transpose_mul]

  have ha : Mᴴ = M := by
    rw [hMdef, conjTranspose_mul, conjTranspose_nonsing_inv, hH]
    apply inv_mul_eq_mul_inv_of_intertwine _ _ _ _ hY
    · rw [hYh, hYdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, f2, Matrix.mul_assoc]
    · rw [det_conjTranspose]; exact star_ne_zero.mpr hY

  have hMbar : M.map star = Mᵀ := by
    ext i j
    have := congrFun (congrFun ha j) i
    simpa [conjTranspose_apply] using this
  have hb : M.map star * C = Cᵀ * M := by
    rw [hMbar, hMdef, transpose_mul, transpose_nonsing_inv, Matrix.mul_assoc, f1, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc]
    apply inv_mul_eq_mul_inv_of_intertwine _ _ _ _ hY
    · rw [hYt, hYdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_assoc Cᵀ (C.map star)ᵀ, ← Matrix.mul_assoc (C.map star)ᵀ, f2]
      simp only [Matrix.mul_assoc]
    · rw [det_transpose]; exact hY

  have hc : M = M₀ + (C.map star)ᵀ * M.map star * C := by
    have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, hMdef, ← Matrix.mul_assoc, f2]
    have h0 : M₀ = M₀ * Y * Y⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hYu, Matrix.mul_one]
    calc M₀ * Y⁻¹ = (M₀ * Y + M₀ * C.map star * C) * Y⁻¹ := by
          rw [Matrix.mul_assoc M₀ (C.map star), ← Matrix.mul_add, hYdef, sub_add_cancel, Matrix.mul_one]
      _ = M₀ * Y * Y⁻¹ + M₀ * C.map star * C * Y⁻¹ := Matrix.add_mul _ _ _
      _ = _ := by rw [← h0]
  refine ⟨ha, fun z w => ?_⟩
  have e : hermForm M (z + C *ᵥ star z) (w + C *ᵥ star w) =
      z ⬝ᵥ M *ᵥ star w + z ⬝ᵥ (M * C.map star) *ᵥ w + star z ⬝ᵥ (Cᵀ * M) *ᵥ star w
        + star z ⬝ᵥ (Cᵀ * M * C.map star) *ᵥ w := by
    simp only [hermForm, star_add, star_mulVec', star_star, add_dotProduct, mulVec_add, dotProduct_add,
      dot_left, mulVec_mulVec, Matrix.mul_assoc]
    ring
  have e2 : star (z ⬝ᵥ (M * C.map star) *ᵥ w) = star z ⬝ᵥ (Cᵀ * M) *ᵥ star w := by
    rw [star_dot_mulVec, map_star_mul', map_star_map_star', hb]
  have e4 : star (star z ⬝ᵥ (Cᵀ * M * C.map star) *ᵥ w) = z ⬝ᵥ ((C.map star)ᵀ * M.map star * C) *ᵥ star w := by
    rw [star_dot_mulVec, map_star_mul', map_star_mul', map_star_map_star', star_star, transpose_map]
  have e1 : z ⬝ᵥ M *ᵥ star w = hermForm M₀ z w + z ⬝ᵥ ((C.map star)ᵀ * M.map star * C) *ᵥ star w := by
    conv_lhs => rw [hc]
    rw [hermForm, add_mulVec, dotProduct_add]
  rw [e, e1, ← e2, ← e4]
  simp only [Complex.add_im, Complex.star_def, Complex.conj_im]
  ring

end GlobalTheory.PeriodCoord
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.HermImNondeg

theorem hermForm_add_right' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_smul_right' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z (a • w) = star a * hermForm Hm z w := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hermForm_self_star {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z : Fin g → ℂ) :
    star (hermForm Hm z z) = hermForm Hm z z := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, h.apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem im_hermForm_alternating_nondegenerate (La : Type) [AddCommGroup La] (g : ℕ) (P : La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La) (hP : Function.Injective P)
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) :
    (∀ x, EF x x = 0) ∧ ∀ x, (∀ y, EF x y = 0) → x = 0 := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · have hc : ((EF x x : ℤ) : ℝ) = 0 := by
      rw [← hEF]
      have h1 := congrArg Complex.im (hermForm_self_star hH (P x))
      have h2 : (star (hermForm Hm (P x) (P x))).im = -(hermForm Hm (P x) (P x)).im := Complex.conj_im _
      linarith
    exact_mod_cast hc
  · set z := P x with hz
    have key : ∀ w : Fin g → ℂ, (hermForm Hm z w).im = 0 := by
      intro w
      have hw : w ∈ Submodule.span ℝ (Set.range P) := hspan ▸ Submodule.mem_top
      induction hw using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨y, rfl⟩ := ha
        rw [hEF, hx y]; simp
      | zero => simp [hermForm]
      | add a b _ _ h1 h2 => rw [hermForm_add_right', Complex.add_im, h1, h2, add_zero]
      | smul r a _ h1 =>
        rw [← Complex.coe_smul, hermForm_smul_right']
        simp [h1]
    have hI := key (Complex.I • z)
    rw [hermForm_smul_right'] at hI
    have hre : (hermForm Hm z z).re = 0 := by
      have : (star Complex.I * hermForm Hm z z).im = -(hermForm Hm z z).re := by
        simp [Complex.mul_im]
      linarith
    by_contra hne
    have hz0 : z ≠ 0 := by
      intro h0; apply hne; apply hP; rw [← hz, h0, map_zero]
    have := hpos z hz0
    linarith

end GlobalTheory.HermImNondeg
end
