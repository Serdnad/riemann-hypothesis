module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle464
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaTraceValuesAtComplexPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle038
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle429
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle465
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle431
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle467
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle157
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

theorem _root_.GlobalTheory.T.finite_classes_rational_isometries_bounded_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ), 0 < N → ∃ S : Finset (GL (Fin r) E), (∀ s ∈ S, QMatch X X' N s) ∧ ∀ a, QMatch X X' N a → ∃ s ∈ S, ∃ b ∈ X'.Γ, a = b * s := by
  first | exact @GlobalTheory.HeckeEx.QFin.finite_reps | exact GlobalTheory.HeckeEx.QFin.finite_reps | (intros; apply GlobalTheory.HeckeEx.QFin.finite_reps <;> assumption)
end

section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
noncomputable section

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeLiftScalar

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.MoveValues GlobalTheory.HeckeValues



theorem hkPtC_values_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (p : ℕ) (y z : FrPt Xo c (CAt σ)) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)),
  HkPtC p y C z →
  ∃ (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk y.x ⟶ Xo.univ.t.G) →* (Over.mk z.x ⟶ Xo.univ.t.G)) (n : ℕ)
    (cr : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk y.x ⟶ Xo.univ.t.G) → ℂ),
    @IsHkIsog E _ _ _ H Dw l Xo (CAt σ) (fieldCAt σ) (algClosedCAt σ) p y.x z.x C ψ ψp ∧
    (∀ τ j, @IsLieImageH E _ _ _ H Dw l Xo (CAt σ) (fieldCAt σ) p y.x z.x ψ (y.u τ j) (z.u τ j)) ∧ GlobalTheory.ThetaTrace.IsRepsModTors C p cr ∧
    (∀ i j (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) ∧
    (∀ i j i' j' (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
      ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
        valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) ∧
    (∀ i j, ⊤ ≤ (1 : Over.mk z.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      ⊤ ≤ (1 : Over.mk y.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' z.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
        b i j 1 * valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    (∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y.x ⟶ Xo.univ.t.G)), IsHolTo Set.univ (fun w => (e w).left) →
      ∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
        {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ (a : Over.mk y.x ⟶ Xo.univ.t.G) i (jm : Fin n → Xo.univ.t.PP.L.ι), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      (∀ m, ⊤ ≤ ((cr m * a) ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U (jm m)) →
      valAt' (lift (𝟙 (Over.mk z.x)) (ψp a)).left ((PPx z.x).U (fun _ => i)) (z.s.f (fun _ => i)) =
        ∑ m, b i (jm m) (cr m * a) *
          valAt' (lift (𝟙 (Over.mk y.x)) ((cr m * a) ^ p)).left ((PPx y.x).U (fun _ => jm m)) (y.s.f (fun _ => jm m))) := by
  intro E _ _ _ H Dw l Xo c σ p y z C hk
  letI := fieldCAt σ
  haveI := algClosedCAt σ
  obtain ⟨ψ, ψp, hiso, hL, htr⟩ := hk
  obtain ⟨β, s₁, n, cr, hβ, hs, hr, hv⟩ := isThetaTrace_iff.1 htr
  obtain ⟨β₀, hβ₀, hc₀⟩ := hs.exists_isRigIso
  have hK := transKer_of_isHkIsog hiso
  have hΨ : ∀ a, rpt a ≫ conj y.x z.x ψ = rpt (ψp a) := fun a => (sends_conj_iff ψ _ _).2 (hiso.2.2.1 a)
  refine ⟨ψ, ψp, n, cr, fun i j a => bv Xo.univ.t.PP β β₀ i j a, hiso, hL, hK ▸ hr, fun i j a _ _ => bv_ne i j a,
    fun i j i' j' a hi hj => ?_, fun i j hi hj => ?_, fun g e he i j => ?_, fun a i jm hi hj => ?_⟩
  · have mi := (mem_iff _ _).2 hi
    have mj := (mem_iff _ _).2 hj
    exact bv_trans hβ.2.1 hβ₀.2.1 a (ψp a) (hΨ a) mi.1 mi.2 mj.1 mj.2
  · have h1 : rpt (1 : Over.mk y.x ⟶ Xo.univ.t.G) ≫ conj y.x z.x ψ = rpt (1 : Over.mk z.x ⟶ Xo.univ.t.G) := by
      exact (hΨ 1).trans (congrArg (fun q => rpt q) (map_one ψp))
    exact bv_rig hβ hβ₀ h1 i j ((mem_iff _ _).2 hi) ((mem_iff _ _).2 hj)
  · have hfun : (fun w => rpt (e w)) = fun w => fibPt Xo.univ.t.G (e w) ≫ (swap y.x).inv :=
      funext fun w => (Iso.eq_comp_inv _).2 (fibPt_swap (e w))
    have hh : IsHolTo Set.univ (fun w => rpt (e w)) := by
      rw [hfun]
      exact (GlobalTheory.HolFibre.isHolTo_fibPt_and_comp _ Xo.univ.t.G y.x g e he).2 _ (swap y.x).inv
    exact bv_hol hβ.2.1 hβ₀.2.1 ψp hΨ e hh i j
  · exact bv_values hβ.2.1 hβ₀.2.1 hc₀ cr (fun m => hr.1 m) hv a (ψp a) (hΨ a) i jm ((mem_iff _ _).2 hi)
      (fun m => (mem_iff _ _).2 (hj m))

end GlobalTheory.HeckeLiftScalar
end
end

section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

theorem _root_.GlobalTheory.T.heckeThetaTrace_values_at_complexPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (p : ℕ) (y z : FrPt Xo c (CAt σ)) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)),
  HkPtC p y C z →
  ∃ (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk y.x ⟶ Xo.univ.t.G) →* (Over.mk z.x ⟶ Xo.univ.t.G)) (n : ℕ)
    (cr : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk y.x ⟶ Xo.univ.t.G) → ℂ),
    @IsHkIsog E _ _ _ H Dw l Xo (CAt σ) (fieldCAt σ) (algClosedCAt σ) p y.x z.x C ψ ψp ∧ GlobalTheory.ThetaTrace.IsRepsModTors C p cr ∧
    (∀ i j (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) ∧
    (∀ i j i' j' (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
      ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
        valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) ∧
    (∀ i j, ⊤ ≤ (1 : Over.mk z.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      ⊤ ≤ (1 : Over.mk y.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' z.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
        b i j 1 * valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    (∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y.x ⟶ Xo.univ.t.G)), IsHolTo Set.univ (fun w => (e w).left) →
      ∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
        {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ (a : Over.mk y.x ⟶ Xo.univ.t.G) i (jm : Fin n → Xo.univ.t.PP.L.ι), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      (∀ m, ⊤ ≤ ((cr m * a) ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U (jm m)) →
      valAt' (lift (𝟙 (Over.mk z.x)) (ψp a)).left ((PPx z.x).U (fun _ => i)) (z.s.f (fun _ => i)) =
        ∑ m, b i (jm m) (cr m * a) *
          valAt' (lift (𝟙 (Over.mk y.x)) ((cr m * a) ^ p)).left ((PPx y.x).U (fun _ => jm m)) (y.s.f (fun _ => jm m))) := by
  first | exact @GlobalTheory.HeckeValues.hkPtC_values | exact GlobalTheory.HeckeValues.hkPtC_values | (intros; apply GlobalTheory.HeckeValues.hkPtC_values <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem fmR_coordX_self {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank) :
    fmR A B (Formalism.L2.Ker.coordX l) l.1 = unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2 := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  rw [Finset.sum_eq_single l.2.1, Finset.sum_eq_single l.2.2]
  · simp; rfl
  · intro j _ hj; simp [hj]
  · simp
  · intro i _ hi; refine Finset.sum_eq_zero fun j _ => ?_; simp [hi]
  · simp

theorem fmR_coordX_ne {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (τ' : D.what₂.Tau) (h : τ' ≠ l.1) : fmR A B (Formalism.L2.Ker.coordX l) τ' = 0 := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp [h]; rfl

theorem fmR_I_coordX_self {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank) :
    fmR A B (I • Formalism.L2.Ker.coordX l) l.1 =
      cplxO (A.cart l.1) (B.cart l.1) (unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2) := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  rw [Finset.sum_eq_single l.2.1, Finset.sum_eq_single l.2.2]
  · simp; rfl
  · intro j _ hj; simp [hj]
  · simp
  · intro i _ hi; refine Finset.sum_eq_zero fun j _ => ?_; simp [hi]
  · simp

theorem fmR_I_coordX_ne {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (τ' : D.what₂.Tau) (h : τ' ≠ l.1) : fmR A B (I • Formalism.L2.Ker.coordX l) τ' = 0 := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp [h]; rfl

theorem gq_add_smul {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) (z e : VCx ι a b) (t : ℝ) :
    gq c (z + t • e) = gq c z + t * gD c z e + t ^ 2 * gq c e := by
  have key : ∀ (k : ℝ) (p q : ℂ), k * ‖p + t • q‖ ^ 2 =
      k * ‖p‖ ^ 2 + t * (2 * (k * (p * conj q).re)) + t ^ 2 * (k * ‖q‖ ^ 2) := by
    intro k p q
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  unfold gq gD
  simp only [Pi.add_apply, Pi.smul_apply, key, Finset.sum_add_distrib, Finset.mul_sum]

theorem heisO_eq_exp_rd (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) {S T : HSp D}
    (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (w : VCx D.what₂.Tau S.rank T.rank) :
    heisO ψ S T (fockPt σ A B w) h x = Complex.exp (-((gq (fw D) w : ℂ) / 2)) * rd ψ σ A B h x w := by
  unfold rd
  rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf
  simp

theorem heis_dRho_fock_eval (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D)
    (hψ : IsStdChar D ψ (-1)) (hC : GlobalTheory.FockCompare.Chart θ σ) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S)
    (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (z e : VCx D.what₂.Tau S.rank T.rank) (τ : D.what₂.Tau)
    (v : Matrix (Fin T.rank) (Fin S.rank) ℂ) (hv : fmR A B e τ = v) (h0 : ∀ τ', τ' ≠ τ → fmR A B e τ' = 0)
    (hd : DifferentiableAt ℝ (rd ψ σ A B h x) z) :
    heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ v h) x =
      Complex.exp (-((gq (fw D) z : ℂ) / 2)) *
        ((-((Real.pi : ℂ) * I) * (omF A B z e : ℂ) - (gD (fw D) z e : ℂ) / 2) * rd ψ σ A B h x z +
          fderiv ℝ (rd ψ σ A B h x) z e) := by
  rw [heis_dRho_fock D ψ θ σ hψ hC S T A B h x z e τ v hv h0]
  have hfun : (fun t : ℝ => Complex.exp (-((Real.pi : ℂ) * I) * ((t * omF A B z e : ℝ) : ℂ)) *
      heisO ψ S T (fockPt σ A B (z + t • e)) h x) = fun t : ℝ =>
      Complex.exp (-((Real.pi : ℂ) * I) * ((t : ℂ) * (omF A B z e : ℂ)) - ((gq (fw D) z : ℂ) +
        (t : ℂ) * (gD (fw D) z e : ℂ) + (t : ℂ) ^ 2 * (gq (fw D) e : ℂ)) / 2) * rd ψ σ A B h x (z + t • e) := by
    funext t
    rw [heisO_eq_exp_rd, gq_add_smul, ← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [hfun]
  have hline : HasDerivAt (fun t : ℝ => z + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z
  have hRd : HasDerivAt (fun t : ℝ => rd ψ σ A B h x (z + t • e)) (fderiv ℝ (rd ψ σ A B h x) z e) 0 := by
    have := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    exact this
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hP : HasDerivAt (fun t : ℝ => -((Real.pi : ℂ) * I) * ((t : ℂ) * (omF A B z e : ℂ)) - ((gq (fw D) z : ℂ) +
        (t : ℂ) * (gD (fw D) z e : ℂ) + (t : ℂ) ^ 2 * (gq (fw D) e : ℂ)) / 2)
      (-((Real.pi : ℂ) * I) * (omF A B z e : ℂ) - (gD (fw D) z e : ℂ) / 2) 0 := by
    have h1 := (hid.mul_const (omF A B z e : ℂ)).const_mul (-((Real.pi : ℂ) * I))
    have h2 := ((hid.mul_const (gD (fw D) z e : ℂ)).const_add (gq (fw D) z : ℂ)).add
      ((hid.pow 2).mul_const (gq (fw D) e : ℂ))
    have h3 := h1.sub (h2.div_const 2)
    convert h3 using 1
    all_goals first | rfl | (funext t; rfl) | simp
  have hD : HasDerivAt (fun t : ℝ => Complex.exp (-((Real.pi : ℂ) * I) * ((t : ℂ) * (omF A B z e : ℂ)) -
      ((gq (fw D) z : ℂ) + (t : ℂ) * (gD (fw D) z e : ℂ) + (t : ℂ) ^ 2 * (gq (fw D) e : ℂ)) / 2) *
        rd ψ σ A B h x (z + t • e)) _ 0 := hP.cexp.mul hRd
  rw [hD.deriv]
  simp
  ring

theorem rd_aPlusAll : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (l : FVar D T.rank S.rank) (z : VCx D.what₂.Tau S.rank T.rank), DifferentiableAt ℝ (rd ψ σ A B h x) z → rd ψ σ A B (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x z = (2 / (fockScale D l.1 : ℂ)) * GlobalTheory.FockTransl.Jet.crOp A B l (rd ψ σ A B h x) z := by
  intro D ψ θ σ hψ hC S T A B h x l z hd
  have h1 := heis_dRho_fock_eval D ψ θ σ hψ hC S T A B h x z (Formalism.L2.Ker.coordX l) l.1 _
    (fmR_coordX_self A B l) (fmR_coordX_ne A B l) hd
  have h2 := heis_dRho_fock_eval D ψ θ σ hψ hC S T A B h x z (I • Formalism.L2.Ker.coordX l) l.1 _
    (fmR_I_coordX_self A B l) (fmR_I_coordX_ne A B l) hd
  have hlin : heisO ψ S T (fockPt σ A B z)
      (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x =
      (fockScale D l.1 : ℂ)⁻¹ *
        (heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ l.1
            (unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2) h) x -
          I * heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ l.1
            (cplxO (A.cart l.1) (B.cart l.1) (unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2)) h) x) := by
    simp only [aPlusAll, aPlus, crea, heisO, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hexp : (Real.exp (gq (fw D) z / 2) : ℂ) * Complex.exp (-((gq (fw D) z : ℂ) / 2)) = 1 := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    simp
  have hrd : rd ψ σ A B (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x z =
      (Real.exp (gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z)
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x := rfl
  rw [hrd, hlin, h1, h2]
  unfold crOp lamF
  linear_combination (↑(fockScale D l.1))⁻¹ *
    ((-((Real.pi : ℂ) * I) * (omF A B z (Formalism.L2.Ker.coordX l) : ℂ) - (gD (fw D) z (Formalism.L2.Ker.coordX l) : ℂ) / 2) *
        rd ψ σ A B h x z + fderiv ℝ (rd ψ σ A B h x) z (Formalism.L2.Ker.coordX l) -
      I * ((-((Real.pi : ℂ) * I) * (omF A B z (I • Formalism.L2.Ker.coordX l) : ℂ) -
        (gD (fw D) z (I • Formalism.L2.Ker.coordX l) : ℂ) / 2) * rd ψ σ A B h x z +
        fderiv ℝ (rd ψ σ A B h x) z (I • Formalism.L2.Ker.coordX l))) * hexp +
    (↑(fockScale D l.1))⁻¹ * (Real.pi : ℂ) * (omF A B z (I • Formalism.L2.Ker.coordX l) : ℂ) * rd ψ σ A B h x z * I_sq

end GlobalTheory.FockTransl.Jet

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct BigOperators
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF GlobalTheory.XCharBF.DiagCoord

theorem _root_.GlobalTheory.T.besselStep_diagonalCoordinates_mem_complementIdeal :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : GlobalTheory.Asc.Frames G}, Std F →
    ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m)
      (u : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))),
    u ∈ latO _ _ (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) →
    ∀ p : Fin ρ, ((F.dJ ρ h).pY * u * (F.dB ρ h).jY) p p ∈ complId (D.host.AA * G.pl.stAbar sc) := by
  intro D T L sc G F hF ρ h u hu p
  have rat_tmul_entry {m n k l : ℕ} (q : Matrix (Fin k) (Fin m) D.host.E)
      (C : Matrix (Fin m) (Fin n) D.host.E)
      (e : Matrix (Fin n) (Fin l) D.host.E) (X : AF D.host.F) (p : Fin k) (p' : Fin l) :
      (rat q * (Matrix.of fun i j => X ⊗ₜ[D.host.F] C i j : Mx D m n) * rat e) p p' = X ⊗ₜ[D.host.F] (q * C * e) p p' := by
    have hinc : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun _ => rfl
    simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, hinc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, ← TensorProduct.tmul_sum]
  obtain ⟨hcJ, heJ, -⟩ := hF.hJ ρ h
  obtain ⟨hcB, heB, sB, he'B⟩ := hF.hB ρ h
  set aJ := G.colDec (2 * ρ + 1) (by omega) (by omega) with haJ
  set aB := G.colDec (2 * ρ + 2) (by omega) h with haB
  obtain ⟨hAA, -⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hAb : G.pl.stAbar sc ≠ 0 := by
    intro h0
    apply hA
    rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
    intro y hy
    have h1 : star y ∈ G.pl.stAbar sc := (hconj _).2 (by rwa [star_star])
    have h2 := h0 _ h1
    rwa [star_eq_zero] at h2

  have hJ : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).qY *ᵥ t) p =
      star ((-D.host.xi0) ^ (p.1 + 1)) * ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) := by
    intro t _
    simp only [HypDec.qY, heJ, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, colsOf, star_mul', Finset.mul_sum,
      Finset.sum_mul, mul_assoc]
  have hJmem : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) ∈
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p).rev := by
    intro t ht
    have ht' : t ∈ aJ.lat (G.sp.P (2 * ρ + 1)).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := by
      rw [haJ, ← G.sp.colLat (2 * ρ + 1) (by omega) (by omega)]; exact ht
    exact auxiliaryCoordinate_mem_staircaseIdeal aJ _ _ ht' _ (by simp only [Fin.val_castLE]; omega)

  have hBmem : ∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0),
      star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev) ∈
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev)⁻¹ := by
    intro s hs
    have hs' : s ∈ aB.lat (G.sp.P (2 * ρ + 2)).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := by
      rw [haB, ← G.sp.colLat (2 * ρ + 2) (by omega) h]; exact hs
    have h1 := auxiliaryCoordinate_mem_staircaseIdeal aB _ _ hs' (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev
      (by simp only [Fin.val_rev, Fin.val_castLE]; omega)
    exact ((GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj _ _).2 _).1 h1

  have hsc : star ((-D.host.xi0) ^ (p.1 + 1)) * sB p = 1 := by
    have h1 := congrFun (congrFun (F.dB ρ h).e'e p) p
    rw [he'B, heB, colsOf_gram, Matrix.one_apply_eq] at h1
    have h2 : (aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * aB.a) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev
        (Fin.castLE (by omega) p) = 1 := by
      rw [show aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * aB.a = antiDiagonalSignGramMatrix (2 * ρ + 2 - 1) (-1) from aB.gram]
      simp only [antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE]
      rw [ite_eq_left (by omega), ite_eq_right (fun e => by rw [Fin.ext_iff, Fin.val_rev, Fin.val_castLE] at e; omega)]
    rw [h2, mul_one] at h1
    have h3 := congrArg star h1
    rw [star_mul', star_star, star_one] at h3
    rw [mul_comm]; exact h3
  have hGB : ∀ i j, star ((G.V (.grid (2 * ρ + 2) 0)).gram j i) = (G.V (.grid (2 * ρ + 2) 0)).gram i j := fun i j =>
    (G.V (.grid (2 * ρ + 2) 0)).herm.eq ((G.V (.grid (2 * ρ + 2) 0)).frame j) ((G.V (.grid (2 * ρ + 2) 0)).frame i)

  have keyE : ∀ a ∈ D.host.AA, ∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0), ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0),
      ((F.dJ ρ h).qY * Matrix.of (fun i j => a * t i * ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j) *
        (F.dB ρ h).e') p p ∈ D.host.AA * G.pl.stAbar sc := by
    intro a ha s hs t ht
    rw [entry_rankOne _ _ a t (fun j => ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j), hJ t ht, he'B,
      negSp_gram, negPair_colsOf _ hGB]
    have e : a * (star ((-D.host.xi0) ^ (p.1 + 1)) *
          ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p)) *
        -(sB p * star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev)) =
        -(a * (((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) *
          star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev))) := by
      linear_combination (-(a * ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) *
          star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev))) * hsc
    rw [e]
    refine Submodule.neg_mem _ (FractionalIdeal.mul_mem_mul ha ?_)
    rw [← stairId_mul_inv_succ (G.pl.stA sc) (G.pl.stAbar sc) hA hAb (Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev
      (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev (by omega) (by simp only [Fin.val_rev, Fin.val_castLE]; omega)]
    exact FractionalIdeal.mul_mem_mul (hJmem t ht) (hBmem s hs)
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    have key : ((F.dJ ρ h).pY * (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (a * t i * ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j)) * (F.dB ρ h).jY) p p =
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] ((F.dJ ρ h).qY * Matrix.of (fun i j => a * t i * ∑ k, star (s k) *
          (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j) * (F.dB ρ h).e') p p :=
      rat_tmul_entry _ _ _ _ _ _
    rw [key]
    exact tmul_mem_complId hα (keyE a ha s hs t ht)
  | zero => simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]; exact neg_mem hx
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.FinTransJet

theorem inV_stdL_eq_colLat {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E) :
    GlobalTheory.MovedDict.inV B (Formalism.MainNotions.StandardLatticesGL3.stdL D n) = (Formalism.L2.DIV.colLat B : Set (Fin n → D.host.E)) := by
  have hc := GlobalTheory.ColStd.colLat_comap_eq_stdLat B
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Formalism.L2.Pj.stdLat D.host.E n := hy
    rw [← hc] at hy'
    exact hy'
  · intro hx
    refine ⟨(B⁻¹ : GL (Fin n) D.host.E).1.mulVec x, ?_, ?_⟩
    · show _ ∈ Formalism.L2.Pj.stdLat D.host.E n
      rw [← hc, Submodule.mem_comap]
      simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [show (B.1 * (B⁻¹).1) = 1 from B.mul_inv, Matrix.one_mulVec]
      exact hx
    · simp only [Matrix.mulVec_mulVec]
      rw [show (B.1 * (B⁻¹).1) = 1 from B.mul_inv, Matrix.one_mulVec]

end GlobalTheory.FinTransJet

namespace GlobalTheory.FinTransJet

end GlobalTheory.FinTransJet
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaRestriction_complement_translates_locallyConstant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ e, IsSplitIdem D e → ∀ f, IsThetaFunO ψ V W f → ∃ (L : AddSubgroup (halfMx (cA D e) W.rank r)) (Kc : Set (halfMx (cA D e) W.rank r)), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ IsCompact Kc ∧ (∀ t, t ∉ Kc → res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f) = 0) ∧ ∀ t, ∀ l ∈ L, heisO ψ V W (restEmb V W K (t + l : halfMx (cA D e) W.rank r)) f = heisO ψ V W (restEmb V W K t) f := by
  first | exact @GlobalTheory.HalfSupport.supp_locConst | exact GlobalTheory.HalfSupport.supp_locConst | (intros; apply GlobalTheory.HalfSupport.supp_locConst <;> assumption)
end
