module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

@[expose] public section

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem _root_.GlobalTheory.T.mul_norm_dualWeylTensorEvaluation_le_fibreNorm : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (x : TIdx la → ℂ) (X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) (u : ∀ t, UN (N t)) (s : ℝ), 0 ≤ s → s * ‖tval la x (fun t => X t * (u t).1)‖ ≤ Real.sqrt (∑ I, ‖(fibY la s X *ᵥ x) I‖ ^ 2) := by
  first | exact @GlobalTheory.TSup.mul_norm_tval_le_fibNorm | exact GlobalTheory.TSup.mul_norm_tval_le_fibNorm | (intros; apply GlobalTheory.TSup.mul_norm_tval_le_fibNorm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

theorem _root_.GlobalTheory.T.dualNumber_field_point_mem_open_of_reduction : ∀ (C : Type) [Field C] {X : Scheme.{0}} (y : Sp (DualNumber C) ⟶ X) (U : X.Opens),
    ⊤ ≤ (redE C ≫ y) ⁻¹ᵁ U → ⊤ ≤ y ⁻¹ᵁ U := by
  first | exact @GlobalTheory.MBLow.TanGauge.top_le_of_redE | exact GlobalTheory.MBLow.TanGauge.top_le_of_redE | (intros; apply GlobalTheory.MBLow.TanGauge.top_le_of_redE <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O
open GlobalTheory.CxPts Topology Set

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}

theorem isRatSec_tens {A B : LB Z} {r : A.ι → Z.functionFieldˣ} {s : B.ι → Z.functionFieldˣ}
    (hr : IsRatSec A r) (hs : IsRatSec B s) :
    IsRatSec (CechPic.tens A B) fun c : A.ι × B.ι => r c.1 * s c.2 := fun (c c' : A.ι × B.ι) h => by
  have h₁ : genericPoint Z ∈ A.U c.1 ⊓ A.U c'.1 := ⟨h.1.1, h.2.1⟩
  have h₂ : genericPoint Z ∈ B.U c.2 ⊓ B.U c'.2 := ⟨h.1.2, h.2.2⟩
  have e : fnOf _ h ((CechPic.tens A B).g c c' : Γ(Z, _)) =
      fnOf _ h₁ (A.g c.1 c'.1 : Γ(Z, _)) * fnOf _ h₂ (B.g c.2 c'.2 : Γ(Z, _)) := by
    change fnOf _ h ((res _ (A.g c.1 c'.1)).val * (res _ (B.g c.2 c'.2)).val) = _
    exact (map_mul (fnOf _ h) _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ h _) (fnOf_resG _ h _))
  rw [Units.val_mul, Units.val_mul, hr c.1 c'.1 h₁, hs c.2 c'.2 h₂, e]
  ring

theorem div_tens (M N : HermLB q) {r : M.B.ι → Z.functionFieldˣ} {s : N.B.ι → Z.functionFieldˣ}
    (hr : IsRatSec M.B r) (hs : IsRatSec N.B s) :
    (M.tens N).div (isRatSec_tens hr hs) = M.div hr + N.div hs :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨a, ha⟩ := exists_chart M.isLB z
    obtain ⟨b, hb⟩ := exists_chart N.isLB z
    exact ⟨_, (presents_divOfRatSec (M.tens N).isLB (isRatSec_tens hr hs)).isEqn (a, b) z ⟨ha, hb⟩,
      ((presents_divOfRatSec M.isLB hr).isEqn a z ha).add ((presents_divOfRatSec N.isLB hs).isEqn b z hb)⟩

end GlobalTheory.PtHtComb

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}

theorem curveDeg_tens [IsLocallyNoetherian Z] (hZ : IsArithVar q 0)
    (hc : CharZero (Z.residueField (genericPoint Z))) (M N : HermLB q) {r : M.B.ι → Z.functionFieldˣ}
    {s : N.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) (hs : IsRatSec N.B s) :
    (M.tens N).curveDeg (isRatSec_tens hr hs) = M.curveDeg hr + N.curveDeg hs := by
  have := hZ.isNoetherian
  have hfin (D : CartierDiv Z) : (Function.support fun z =>
      (D.mult z : ℝ) * Real.log (Nat.card (Z.residueField z))).Finite :=
    D.finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  have h₂ (σ) (y : CxPts q σ) : logNorm ((M.tens N).φ σ) (fun c : M.B.ι × N.B.ι => r c.1 * s c.2) y =
      logNorm (M.φ σ) r y + logNorm (N.φ σ) s y := by
    have hy : under y = genericPoint Z := hZ.under_eq_genericPoint y
    have ho (D : CartierDiv Z) : y ∈ offSupp q σ D := mem_offSupp.2 (hy ▸ D.genericPoint_notMem_supp)
    have ha := mem_pick (M.φ σ).isLB y
    have hb := mem_pick (N.φ σ).isLB y
    have hu (g : Z.functionFieldˣ) : ‖ratVal (g : Z.functionField) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero (hy ▸ unitAt_genericPoint g.ne_zero))
    refine (logNorm_eq ((M.tens N).φ σ) (isRatSec_tens hr hs) (ho _) (i := (pick (M.φ σ).isLB y, pick (N.φ σ).isLB y))
      (mem_ptsIn_inf.2 ⟨ha, hb⟩)).trans ?_
    change Real.log ‖ratVal ((r (pick (M.φ σ).isLB y) * s (pick (N.φ σ).isLB y) : Z.functionFieldˣ) : Z.functionField) y‖ -
      ((M.φ σ).φ (pick (M.φ σ).isLB y) y + (N.φ σ).φ (pick (N.φ σ).isLB y) y) / 2 = _
    rw [logNorm, logNorm, Units.val_mul,
      ratVal_mul (hy ▸ regAt_genericPoint _) (hy ▸ regAt_genericPoint _), norm_mul, Real.log_mul (hu _) (hu _)]
    ring
  have := SmallSecHeight.numberField hZ hc
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ (SmallSecHeight.ptsEquiv hZ).symm
  have (σ : k →+* ℂ) : Finite (CxPts q σ) := .of_injective _ (sigma_mk_injective (i := σ))
  have := hZ.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  unfold HermLB.curveDeg
  rw [div_tens M N hr hs]
  simp only [CartierDiv.mult_add, Int.cast_add, add_mul]
  rw [finsum_add_distrib (hfin _) (hfin _)]
  simp only [finsum_eq_sum_of_fintype, h₂, Finset.sum_add_distrib]
  ring

end GlobalTheory.PtHtComb

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem height_tens (hX : IsArithVar p D) {L M : HermLB p} {h h' h'' : X → ℝ} (H : L.IsArithHeight h)
    (H' : M.IsArithHeight h') (H'' : (L.tens M).IsArithHeight h'') {x : X} (hx : IsAlgPt x) :
    h'' x = h x + h' x := by
  obtain ⟨hc, hd⟩ := hx
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have := hX.isNoetherian_sub i
  have hr : range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr] at hd
  have hbij : Function.Bijective (i.residueFieldMap (genericPoint Z)).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  have hc' : CharZero (Z.residueField (genericPoint Z)) := (RingHom.charZero_iff hbij.1).1 hc
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hcΓ hd
  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr i).isLB
  obtain ⟨s, hs⟩ := exists_isRatSec (M.restr i).isLB
  obtain ⟨t, ht, h₁, h₂⟩ := (HermLB.isometric_pull_tens (L := L) (M := M) i rfl).symm.exists_isRatSec
    (isRatSec_tens hr hs)
  rw [H''.point Z i hcΓ hd t ht, H.point Z i hcΓ hd r hr, H'.point Z i hcΓ hd s hs,
    ← curveDeg_tens hZ hc' (L.restr i) (M.restr i) hr hs, HermLB.curveDeg, h₁]
  refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => h₂ σ (mem_offSupp.2 ?_))
  rw [hZ.under_eq_genericPoint]
  exact CartierDiv.genericPoint_notMem_supp _

end GlobalTheory.PtHtComb
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.HessKer

open ReciprocityTheory.L2DbarEstimates (V cHess bas)

theorem exists_vecMul_eq_zero {D D' : ℕ} (h : D' < D) (P : Matrix (Fin D) (Fin D') ℂ) :
    ∃ ξ : Fin D → ℂ, ξ ≠ 0 ∧ Matrix.vecMul ξ P = 0 := by
  have hk : LinearMap.ker P.vecMulLinear ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using h)
  obtain ⟨ξ, hξ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨ξ, h0, by simpa using hξ⟩

theorem exists_common_kernel : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D D' : ℕ), D' < D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (c : AlgChart p σ D') (c' : AlgChart q σ D) (w : CxPts q σ), w ∈ c'.e.source → ptMap π hπ σ w ∈ c.e.source → ∃ ξ : Fin D → ℂ, ξ ≠ 0 ∧ ∀ (A : MLine p σ) (i : (A.pull π hπ).B.ι), w ∈ ptsIn q σ ((A.pull π hπ).B.U i) → Matrix.vecMul ξ (c'.hess (A.pull π hπ).φ i w) = 0 := by
  intro k _ X Y p q σ D D' hD π hπ c c' y hy hy0
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  set F : V D → V D' := c.e ∘ m ∘ c'.e.symm with hFdef
  set U := c'.e.target ∩ c'.e.symm ⁻¹' (m ⁻¹' c.e.source)
  have hU : IsOpen U := isOpen_over c'.e (c.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c'.e y ∈ U := mem_over c'.e hy hy0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c' c
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c'.e y) = c.e (m y) := by
    simp only [hFdef, Function.comp_apply, c'.e.left_inv hy]
  obtain ⟨ξ, hξ, hP⟩ := exists_vecMul_eq_zero hD (Matrix.of fun j b => fderiv ℂ F (c'.e y) (bas D j) b)
  refine ⟨ξ, hξ, fun A i hi => ?_⟩
  have him : m y ∈ ptsIn p σ (A.B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hi PUnit.unit
  set g : V D' → ℂ := fun v => (A.φ.φ (i PUnit.unit) (c.e.symm v) : ℂ)
  have hg : ContDiffAt ℝ 2 g (F (c'.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (A.cInf.contDiffAt c hy0 him)
  have e : (fun v => ((A.pull π hπ).φ.φ i (c'.e.symm v) : ℂ)) =ᶠ[𝓝 (c'.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ A.φ π hπ i (c'.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c.e.left_inv hv.2]
    exact congrArg _ this
  have key : c'.hess (A.pull π hπ).φ i y =
      (Matrix.of fun j b => fderiv ℂ F (c'.e y) (bas D j) b) * (cHess D' g (F (c'.e y)) *
        Matrix.of fun a l => (starRingEnd ℂ) (fderiv ℂ F (c'.e y) (bas D l) a)) := by
    show cHess D _ (c'.e y) = _
    rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e, ← Matrix.mul_assoc]
    ext j l
    rw [GlobalTheory.HessPull.cHess_comp_apply D D' g F U hU _ hyU hF hg j l, Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [key, ← Matrix.vecMul_vecMul, hP, Matrix.zero_vecMul]

end GlobalTheory.HessKer
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.FrameAut

theorem eq_zero_of_entire_mul_eq_zero {g : ℕ} {θ D : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    {S : Set (Fin g → ℂ)} (hS : IsOpen S) (hD : ContinuousOn D S) (h : ∀ w ∈ S, θ w * D w = 0)
    {z : Fin g → ℂ} (hz : z ∈ S) : D z = 0 := by
  by_contra hne
  have hc : ContinuousAt D z := hD.continuousAt (hS.mem_nhds hz)
  have he : θ =ᶠ[nhds z] 0 := by
    filter_upwards [hc.eventually_ne hne, hS.mem_nhds hz] with w hw hwS
    exact (mul_eq_zero.1 (h w hwS)).resolve_right hw
  have ha : AnalyticOnNhd ℂ θ Set.univ := SCV.analyticOnNhd_of_differentiable hθ Set.univ
  exact h0 (funext fun w =>
    ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) he (Set.mem_univ w))

end GlobalTheory.MBLow.Cl.FrameAut

namespace GlobalTheory.MBLow.Cl

theorem frame_eq_autV_mul : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ M N (i : x.P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → u.fr i z = autV τ a b M N z * u.fr i (z + perV τ M N) := by
  intro g x hg u τ a b c W hNF M N i z hz
  obtain ⟨hs, hp, ha, hb, hc, hΛ, _, hth, _⟩ := hNF
  obtain ⟨hd, ⟨z₀, hz₀⟩, hlaw⟩ := GlobalTheory.T.thetaChar_differentiable_ne_zero_automorphy g τ a b hs hp ha hb
  have hdc : Differentiable ℂ (fun w => c * thetaChar τ a b w) := (differentiable_const c).mul hd
  have h0 : (fun w => c * thetaChar τ a b w) ≠ 0 := fun h => by
    have := congrFun h z₀
    simp only [Pi.zero_apply, mul_eq_zero] at this
    exact this.elim hc hz₀
  have hl : u.ex (perV τ M N) = 1 := (u.ker _).2 ((hΛ _).2 ⟨M, N, rfl⟩)
  have he : ∀ w, u.ex (w + perV τ M N) = u.ex w := fun w => by rw [u.ex_add, hl, _root_.mul_one]
  have hS : IsOpen {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i} := (u.hol _ 0).1
  have htr : ∀ w, ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i → ⊤ ≤ (u.ex (w + perV τ M N)).left ⁻¹ᵁ x.P.L.U i :=
    fun w hw => by rw [he]; exact hw
  have hcf := (u.fr_hol i).continuousOn
  have haut : Continuous (autV τ a b M N) := by
    unfold autV dotProduct
    fun_prop
  have hD : ContinuousOn (fun w => u.fr i w - autV τ a b M N w * u.fr i (w + perV τ M N))
      {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i} :=
    hcf.sub (haut.continuousOn.mul (hcf.comp (continuous_add_const _).continuousOn fun w hw => htr w hw))
  refine sub_eq_zero.1 (FrameAut.eq_zero_of_entire_mul_eq_zero hdc h0 hS hD (fun w hw => ?_) hz)
  have h1 := hth i w hw
  have h2 := hth i _ (htr w hw)
  beta_reduce at h1 h2 ⊢
  rw [he, h1, hlaw] at h2
  linear_combination h2

end GlobalTheory.MBLow.Cl

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubeJet

theorem cube_jet : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (G : Geo ν d),
    (∀ (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
      (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
      valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
        (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I) →
    ∀ (W : Fin g → ℂ) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    IsD ν d W gm.b → ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      1 + TrivSqZeroExt.inr
        (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex (x + y))).left)) (x + y) W / G.frG (ν.J (ν.eA (d.ex (x + y))).left) (x + y) +
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W / G.frG (ν.J (ν.eA (d.ex 0)).left) 0 -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex x)).left)) x W / G.frG (ν.J (ν.eA (d.ex x)).left) x -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex y)).left)) y W / G.frG (ν.J (ν.eA (d.ex y)).left) y) := by
  intro R _ _ D _ N g ν d G hprod W gm h0 hD χ χ' x y hx hy
  obtain ⟨U, f, hv, hU0, hUz⟩ := GlobalTheory.T.cubeValue_constPoints_tangent_eq_dualFibreValue ν d gm h0 χ χ' x y hx hy
  rw [hv, hD U f hU0]
  have hO : IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} := (G.hol U f).1
  have hFeq : (fun z => valF (ptB ν d z) U f) =ᶠ[nhds 0] fun z => ∏ I : thK.{0},
      G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I := by
    filter_upwards [hO.mem_nhds hU0] with z hz
    obtain ⟨hI, hval⟩ := hUz z hz
    rw [hval]
    exact hprod x y z _ hI
  have hopen : ∀ i, IsOpen {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ D.P.L.U i} := fun i => by
    have e : ∀ z, (ν.eA (d.ex z)).left = ptB ν d z ≫ (DegPre.prB D ℂ).left := fun z => by
      rw [ptB, DegPre.prB, ← Over.comp_left, lift_snd]
    have := (G.hol ((DegPre.prB D ℂ).left ⁻¹ᵁ D.P.L.U i) 0).1
    simpa only [e, Scheme.Hom.comp_preimage] using this
  have hd : ∀ I : thK.{0}, DifferentiableAt ℂ (G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
      (∑ i ∈ I.down, ![x, y, 0] i) := fun I =>
    (G.fr_hol _).differentiableAt ((hopen _).mem_nhds (ν.good _))
  have hn : ∀ I : thK.{0}, G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)
      (∑ i ∈ I.down, ![x, y, 0] i) ≠ 0 := fun I => by
    rw [← G.fr_eq]
    exact mul_ne_zero (Units.ne_zero _) (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  have hpair : ∀ I : thK.{0}, 2 ∉ I.down →
      G.frG (ν.J (ν.eA (d.ex (∑ i ∈ (insert 2 I.down), ![x, y, 0] i))).left) =
        G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left) := fun I h2 => by
    rw [Finset.sum_insert h2]
    simp
  obtain ⟨h1, h2⟩ := GlobalTheory.T.alternatingCubeProduct_value_fderiv_at_zero x y W (fun I : thK.{0} => G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) _
    hFeq hd hn hpair
  rw [h1, h2]
  simp [Finset.sum_insert]

end GlobalTheory.MBLow.Cl.CubeJet
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.mixedChernFormSignedPartMeasure_chart_apply : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ) (ε : ℤˣ) (c : AlgChart p σ D) (S : Set (CxPts p σ)), MeasurableSet S → S ⊆ c.e.source → part L ε S = ∫⁻ v in c.e '' S, ENNReal.ofReal ((ε : ℤ) * dens L c (c.e.symm v)) := by
  first | exact @GlobalTheory.Mix.part_apply | exact GlobalTheory.Mix.part_apply | (intros; apply GlobalTheory.Mix.part_apply <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem archF_of_arch : ∀ κ : Rule, Funct κ → Arch κ → ArchF κ := by
  intro κ hF hA R _ _ _ _ D hP hT F _ _ _ e N ν g r m k hg hm hk β ζ q hq s hs vB bX σ gm hAd k₀ hK
  letI : Algebra (FractionRing R) ℂ := ((e : F →+* ℂ).comp (algebraMap (FractionRing R) F)).toAlgebra
  have he : ∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) ℂ x := fun _ => rfl
  obtain ⟨N', ν', I, hb, hh, hl, heX, hth, hrg, hvE, hfam⟩ := GlobalTheory.T.degenerationValues_transport_fieldIso R D F ℂ e he N ν
  obtain ⟨hform, hlev⟩ := GlobalTheory.T.degenerationDataValuesIso_transport_formsLevelsFamilies F ℂ e N N' I hb hh hl
  obtain ⟨β', hβ⟩ := hform k β
  obtain ⟨q', hq', hev⟩ := hlev m g hm ζ q hq
  obtain ⟨hBK, hadp⟩ := GlobalTheory.T.abelianKeyValue_adaptedVectors_fieldIso κ hF R D F ℂ e he N ν N' ν' I hh hl heX hth hvE vB
  obtain ⟨gm', hpull, hAd'⟩ := hadp r g bX σ gm hAd
  choose s' hs1 hs2 using fun a => hfam (m ^ 2) (s a)
  have hs' : ∀ a, ∃ f, ν'.FamV (s' a) f ∧ IsEvFam N' m (q' a) f := by
    intro a
    obtain ⟨f, hf, hf2⟩ := hs a
    obtain ⟨f', hf', hff⟩ := hs1 a f hf
    exact ⟨f', hf', hev a f f' hf2 hff⟩
  obtain ⟨ε, hε, H⟩ := hA R D hP hT N' ν' g r m k hg hm hk β' _ q' hq' s' hs' vB _ σ gm' hAd' _ (hBK k₀ hK)
  have h1 : ∀ a j α, (jc ν' (s' a) (gm' j) (I.e α)).fst = e (jc ν (s a) (gm j) α).fst := by
    intro a j α
    rw [hs2 a _ _ (hpull j) α]
    simp [dualMap]
  have h2 : ∀ a j α, (jc ν' (s' a) (gm' j) (I.e α)).snd = e (jc ν (s a) (gm j) α).snd := by
    intro a j α
    rw [hs2 a _ _ (hpull j) α]
    simp [dualMap]
  refine ⟨ε, hε, fun u hu hu' => ?_⟩
  obtain ⟨hsum, x₀, hg₀, lev₀, ϑ, hϑ, hJ, hκ⟩ := H u hu hu'
  refine ⟨fun a j => ⟨?_, ?_⟩, x₀, hg₀, lev₀, ϑ, fun a j => ?_, ?_, hκ⟩
  · have := ((I.e.toEquiv.summable_iff.2 (hsum a j).1)).mul_left ‖(e (ν.rg ^ (m ^ 2)))⁻¹‖
    refine this.congr fun α => ?_
    simp only [Function.comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h1, hβ]
    rw [← norm_mul, map_div₀, div_eq_inv_mul, _root_.mul_assoc]
  · have := ((I.e.toEquiv.summable_iff.2 (hsum a j).2)).mul_left ‖(e (ν.rg ^ (m ^ 2)))⁻¹‖
    refine this.congr fun α => ?_
    simp only [Function.comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, hβ]
    rw [← norm_mul, map_div₀, div_eq_inv_mul, _root_.mul_assoc]
  · rw [hϑ a j, ← I.e.toEquiv.tsum_eq]
    refine tsum_congr fun α => ?_
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h1, hβ, hrg, map_div₀, map_pow]
  · convert hJ using 3 with a j
    rw [← I.e.toEquiv.tsum_eq]
    refine tsum_congr fun α => ?_
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, hβ, hrg, map_div₀, map_pow]

end GlobalTheory.MBLow
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

theorem _root_.GlobalTheory.T.curveDegree_nonneg_zmodFibre_of_nefOnFiniteFieldFibres : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (L : HermLB q) (p : ℕ) [Fact p.Prime], ArInt.NefFib L → ∀ (Z : Scheme.{0}) (i : Z ⟶ pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod p) ((L.B.pull (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))).pull i) 1 := by
  first | exact @GlobalTheory.NefFibPrime.topSelf_nonneg_of_nefFib | exact GlobalTheory.NefFibPrime.topSelf_nonneg_of_nefFib | (intros; apply GlobalTheory.NefFibPrime.topSelf_nonneg_of_nefFib <;> assumption)
end

section

open Filter Topology
open GlobalTheory GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.seminormBallFamily_pow_le_encard_of_linearIndependent : ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (r Q : ℕ) (R : ℝ) (v : Fin r → G), 0 ≤ R → LinearIndependent ℤ v → (∀ j, v j ∈ B R) → ((Q ^ r : ℕ) : ℕ∞) ≤ (B (r * Q * R)).encard := by
  first | exact @GlobalTheory.VolBr.isBallFam_pow_le_encard | exact GlobalTheory.VolBr.isBallFam_pow_le_encard | (intros; apply GlobalTheory.VolBr.isBallFam_pow_le_encard <;> assumption)
end
