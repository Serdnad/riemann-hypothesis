module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle230
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle239
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle233
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.GaloisValuations.GlobalB
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ExtConj
variable {F : Type} [Field F] [NumberField F]

theorem valuation_lt_one_iff {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgebraicClosure F) :
    e.O.valuation y < 1 ↔ e.w y < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', e.mem_O, e.mem_O, map_inv₀]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h0 : 0 < e.w y := e.w.pos hy
    simp only [hy, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem lies_over {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (x : 𝓞 F) :
    e.O.valuation (algebraMap F (AlgebraicClosure F) (x : F)) < 1 ↔ x ∈ v.asIdeal := by
  rw [valuation_lt_one_iff, e.w_alg, ← FinitePlace.norm_embedding]
  exact FinitePlace.norm_lt_one_iff_mem F v x

theorem conj (v : HeightOneSpectrum (𝓞 F)) (e e' : Ext v) :
    ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ x, e'.w x = e.w (g x) := by
  obtain ⟨g, hg⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_over (lies_over e) (lies_over e')
  refine ⟨g⁻¹, ?_⟩
  let u : AbsoluteValue (AlgebraicClosure F) ℝ :=
    e.w.comp (f := (g⁻¹ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toRingEquiv.toRingHom) (g⁻¹).injective
  have hu (x) : u x = e.w (g⁻¹ x) := rfl
  have he : u.IsEquiv e'.w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun x => by
    rw [hu, ← valuation_lt_one_iff, ← valuation_lt_one_iff, ← hg, ReciprocityTheory.Gal.smul_valuation_lt_one_iff]
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have h1 : e'.w (algebraMap F _ (a : F)) < 1 := (valuation_lt_one_iff e' _).1 ((lies_over e' a).2 ha)
  have h0 : 0 < e'.w (algebraMap F _ (a : F)) := e'.w.pos (by simpa using ha0)
  have h2 : u (algebraMap F _ (a : F)) = e'.w (algebraMap F _ (a : F)) := by
    rw [hu, AlgEquiv.commutes, e.w_alg, e'.w_alg]
  have h3 := congrFun hce (algebraMap F _ (a : F))
  simp only [h2] at h3
  have hc1 : c = 1 := by
    have h4 := congrArg Real.log h3
    rw [Real.log_rpow h0] at h4
    have := (Real.log_neg h0 h1).ne
    exact mul_right_cancel₀ this (by rw [h4, one_mul])
  intro x
  rw [← hu, ← hce, hc1]
  simp

theorem factor {K : Type} [Field K] {X : Scheme.{0}} (y : Sp K ⟶ X) (x : X) (h : below y = x) :
    ∃ ψ : X.residueField x ⟶ CommRingCat.of K, Spec.map ψ ≫ X.fromSpecResidueField x = y := by
  subst h
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X y⟩

theorem below_comp {K : Type} [Field K] {X : Scheme.{0}} (x : X) (ψ : X.residueField x ⟶ CommRingCat.of K) :
    below (K := K) (Spec.map ψ ≫ X.fromSpecResidueField x) = x :=
  (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply x _)

theorem closed_point_geometric_fibres_finite {k K : Type} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] {X : Scheme.{0}} (s : X ⟶ Sp k)
    [LocallyOfFiniteType s] (x : X) (hx : IsClosed ({x} : Set X)) :
    Nonempty {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} ∧
      Finite {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ s)
  have hfin : IsFinite (Spec.map φ) := by
    rw [hφ]
    exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  letI : Algebra k (X.residueField x) := φ.hom.toAlgebra
  haveI : Module.Finite k (X.residueField x) := (IsFinite.SpecMap_iff φ).1 hfin
  have hP (ψ : X.residueField x →ₐ[k] K) :
      (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x) ≫ s = spMap (algebraMap k K) := by
    have h : φ ≫ CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom (algebraMap k K) :=
      CommRingCat.hom_ext ψ.comp_algebraMap
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    exact congrArg Spec.map h
  let P : (X.residueField x →ₐ[k] K) → {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} :=
    fun ψ => ⟨⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x, hP ψ⟩,
      below_comp x _⟩
  refine ⟨⟨P IsAlgClosed.lift⟩, Finite.of_surjective P ?_⟩
  rintro ⟨⟨y, hy⟩, hyx⟩
  obtain ⟨ψ, h⟩ := factor y x hyx
  have h2 : Spec.map (φ ≫ ψ) = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [Spec.map_comp, hφ, ← Category.assoc, h]
    exact hy
  have h3 := Spec.map_injective h2
  exact ⟨⟨ψ.hom, fun a => congrArg (fun t => t.hom a) h3⟩, Subtype.ext (Subtype.ext h)⟩

theorem pts (Y : Var F) (x : Y.X) (hx : IsClosed ({x} : Set Y.X)) :
    Nonempty {y : AlgPt Y // below y.1 = x} ∧ Finite {y : AlgPt Y // below y.1 = x} :=
  closed_point_geometric_fibres_finite Y.str x hx

theorem main : ∀ (F : Type) [Field F] [NumberField F] , (∀ v : HeightOneSpectrum (𝓞 F), Nonempty (Ext v)) ∧ (∀ Y : Var F, ∀ x : Y.X, IsClosed ({x} : Set Y.X) → Nonempty {y : AlgPt Y // below y.1 = x} ∧ Finite {y : AlgPt Y // below y.1 = x}) ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (e e' : Ext v), ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ x, e'.w x = e.w (g x) :=
  fun _ _ _ => ⟨GlobalTheory.TrueGeoModel.nonempty_ext, pts, conj⟩

end GlobalTheory.TrueGeo.ExtConj
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_isUnitaryAdelicVolumeMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → ∃ μ, IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ := by
  first | exact @GlobalTheory.Mem.VolExists.exists_isVolMeasF | exact GlobalTheory.Mem.VolExists.exists_isVolMeasF | (intros; apply GlobalTheory.Mem.VolExists.exists_isVolMeasF <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL


theorem _root_.GlobalTheory.T.haar_infiniteGL_lt_top_of_infiniteGLHaarMeasure_lt_top : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) [MeasurableSpace (GL (Fin j) (Cinf E))] [BorelSpace (GL (Fin j) (Cinf E))] (ν : Measure (GL (Fin j) (Cinf E))) [ν.IsHaarMeasure] (D : Set (GlobalTheory.FlagMeas.MatInf E j)), MeasurableSet D → GlobalTheory.FlagMeas.haarGL E j D < ⊤ → ν {y | (fun w a b => (y : Matrix (Fin j) (Fin j) (Cinf E)) a b w : GlobalTheory.FlagMeas.MatInf E j) ∈ D} < ⊤ := by
  first | exact @GlobalTheory.haarGL_finite_pullback | exact GlobalTheory.haarGL_finite_pullback | (intros; apply GlobalTheory.haarGL_finite_pullback <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL


theorem _root_.GlobalTheory.T.covolume_unitDetNormSlab_latticeAut_lt_top : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → GlobalTheory.FlagMeas.covol (GlobalTheory.FlagMeas.autGL E j Λ) (GlobalTheory.FlagMeas.haarGL E j) {x | 1 ≤ GlobalTheory.FlagMeas.detNorm E j x ∧ GlobalTheory.FlagMeas.detNorm E j x < Real.exp 1} < ⊤ := by
  intro E _ _ hE j hj Λ hΛ
  letI : Submodule.IsFullLattice E Λ := hΛ
  apply GlobalTheory.SlabFinVol.covol_unitSlab_lt_top <;> first | assumption | infer_instance
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


theorem _root_.GlobalTheory.T.adm_apply_mul_ren_eq_zero_of_mem_J : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ), GlobalTheory.Schubert.admitted H Dw Θ → ∀ (τ : GlobalTheory.AllWt.Psi H) (j : MvPolynomial (Bool × ℕ) ℝ), j ∈ GlobalTheory.GrassTop.J Dw.p Dw.q → ∀ r : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (r * GlobalTheory.GrassTop.ren τ j) = 0 := by
  first | exact @GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies | exact GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies | (intros; apply GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


theorem _root_.GlobalTheory.T.admissibleChernForm_prod_grassmannianBasisCopies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ), (∀ τ, g τ ∈ GlobalTheory.GrassTop.basis Dw.p Dw.q) → ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ → Θ (∏ τ, GlobalTheory.GrassTop.ren τ (g τ)) = (if ∀ τ, g τ = X (true, Dw.p) ^ Dw.q then (-1 : ℝ) ^ (Dw.p * Dw.q * Fintype.card (GlobalTheory.AllWt.Psi H)) else 0) * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  first | exact @GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly | exact GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly | (intros; apply GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.colLieOperator_eq_sum_colUnitaryAction_bddDegree : ∀ (ι : Type) [Fintype ι] (m n d : ℕ) (τ : ι) (k l : Fin n), ∃ (s : Finset (Matrix.unitaryGroup (Fin n) ℂ)) (c : Matrix.unitaryGroup (Fin n) ℂ → ℂ), ∀ P : Pol ι m n, P.totalDegree ≤ d → ∑ g ∈ s, c g • colSub m τ g P = colLie m τ k l P := by
  first | exact @GlobalTheory.DefLift.colLie_eq_sum_colSub | exact GlobalTheory.DefLift.colLie_eq_sum_colSub | (intros; apply GlobalTheory.DefLift.colLie_eq_sum_colSub <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open scoped Matrix

namespace GlobalTheory.PointChernRel

open GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointChern GlobalTheory.GrassModel MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

theorem chernPoly_reindex {n m p : ℕ} (h : p = m) (K : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin p) (Fin p) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) :
    chernPoly (fun u => Matrix.reindex (finCongr h) (finCongr h) (K u)) v k = chernPoly K v k := by
  subst h
  simp

theorem curvPoly_model {n r s : ℕ} (f g : Fin r → Fin s → Fin n) :
    curvPoly (fun u : ReciprocityTheory.L2DbarEstimates.V n =>
      (1 - (Matrix.of fun i j => u (f i j)).map (starRingEnd ℂ) * (Matrix.of fun i j => u (g i j))ᵀ)⁻¹) 0 =
      -Matrix.of fun i j => ∑ c, X (g i c, f j c) := by
  refine Matrix.ext fun i j => ?_

  simp only [curvPoly, Matrix.of_apply, GlobalTheory.T.chernCurvature_inv_one_sub_conj_mul_transpose_at_zero, Matrix.neg_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
  coordVec, PiLp.single_apply, apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero, map_neg, map_sum,
  neg_mul, Finset.sum_neg_distrib, Finset.sum_mul, neg_inj]
  have h (x y : Fin n) (c : Fin s) : C (if f j c = y then if g i c = x then (1 : ℂ) else 0 else 0) * X (x, y) =
      if (g i c, f j c) = (x, y) then X (g i c, f j c) else (0 : MvPolynomial (Fin n × Fin n) ℂ) := by
    by_cases h1 : f j c = y <;> by_cases h2 : g i c = x <;> simp [h1, h2]
  simp only [h]
  rw [← Fintype.sum_prod_type' (f := fun x y => ∑ c, if (g i c, f j c) = (x, y) then X (g i c, f j c) else 0), Finset.sum_comm]
  simp

theorem coeff_comp_neg_X' {R : Type} [CommRing R] (p : Polynomial R) (b : ℕ) :
    (p.comp (-Polynomial.X)).coeff b = (-1) ^ b * p.coeff b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.add_comp, hp, hq, mul_add]
  | monomial m a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, neg_pow,
      ← mul_assoc, show ((-1 : Polynomial R)) ^ m = Polynomial.C ((-1) ^ m) by simp, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

theorem coeff_neg_charpolyRev {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (b : ℕ) :
    (-M).charpolyRev.coeff b = (-1) ^ b * M.charpolyRev.coeff b := by
  have h : (-M).charpolyRev = M.charpolyRev.comp (-Polynomial.X) := by
    rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_compRingHom_apply, RingHom.map_det]
    congr 1
    ext a c : 2
    by_cases h : a = c <;> simp [h]
  rw [h, coeff_comp_neg_X']

theorem charpolyRev_map' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ} (M : Matrix (Fin m) (Fin m) R) :
    M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

theorem relation_top_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k → ∀ P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, chernTop (relPoly τ k * P) (fun u => modelGram H Dw (coordOf ix u)) 0 = 0 := by
  intro E _ _ _ H Dw n ix τ k hk P
  set e : Fin Dw.p × Fin Dw.q → Fin n := fun x => ix.symm (τ, x.1, x.2) with he
  have hL : ∀ j, chernPoly (fun u => modelGram H Dw (coordOf ix u) τ.1) 0 j = (blockPoly e).charpolyRev.coeff j := by
    intro j
    have h1 : (fun u => modelGram H Dw (coordOf ix u) τ.1) = fun u =>
        Matrix.reindex (finCongr (mult_of_mem Dw τ.2).symm) (finCongr (mult_of_mem Dw τ.2).symm)
          ((1 - (Matrix.of fun i c => u (e (i, c))).map (starRingEnd ℂ) * (Matrix.of fun i c => u (e (i, c)))ᵀ)⁻¹) := by
      funext u
      simp only [modelGram, dif_pos τ.2]
      rfl
    rw [h1, chernPoly_reindex, chernPoly, curvPoly_model (fun i c => e (i, c)) (fun i c => e (i, c)), neg_neg]
    rfl
  have hc1 : ¬ conjEmb τ.1 (H.rt : E) = H.rt0 := GlobalTheory.AllWt.conj_not_mem τ
  have hc2 : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0 := by rw [GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2
  have hD : ∀ j, chernPoly (fun u => modelGram H Dw (coordOf ix u) (conjEmb τ.1)) 0 j =
      (blockPolyBar e).charpolyRev.coeff j := by
    intro j
    have hτ : (⟨conjEmb (conjEmb τ.1), hc2⟩ : GlobalTheory.AllWt.Psi H) = τ := Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
    have h1 : (fun u => modelGram H Dw (coordOf ix u) (conjEmb τ.1)) = fun u =>
        Matrix.reindex (finCongr (mult_of_not_mem Dw hc1).symm) (finCongr (mult_of_not_mem Dw hc1).symm)
          ((1 - (Matrix.of fun b i => u (e (i, b))).map (starRingEnd ℂ) * (Matrix.of fun b i => u (e (i, b)))ᵀ)⁻¹) := by
      funext u
      simp only [modelGram, dif_neg hc1, dif_pos hc2, hτ]
      rfl
    rw [h1, chernPoly_reindex, chernPoly, curvPoly_model (fun b i => e (i, b)) (fun b i => e (i, b)), neg_neg]
    rfl
  have hrel : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) (relPoly τ k) =
      ((blockPoly e).charpolyRev * (-blockPolyBar e).charpolyRev).coeff k := by

    simp only [relPoly, map_sum, map_mul, aeval_X, aeval_C, hL, hD, Polynomial.coeff_mul, coeff_neg_charpolyRev]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [map_pow, map_neg, map_one]
    ring
  have hzero : toEven n (((blockPoly e).charpolyRev * (-blockPolyBar e).charpolyRev).coeff k) = 0 := by
    have h2 := GlobalTheory.T.charpolyRev_mul_eq_one_of_trace_pow_add_eq_zero (K := ℂ) _ _ (GlobalTheory.T.trace_pow_grassmannBlockCurvature_supertrace_zero e)
    have e1 : ((blockPoly e).map (toEven n)).charpolyRev = (blockPoly e).charpolyRev.map (toEven n).toRingHom :=
      (charpolyRev_map' _ _).symm
    have e2 : ((-blockPolyBar e).map (toEven n)).charpolyRev =
        (-blockPolyBar e).charpolyRev.map (toEven n).toRingHom := (charpolyRev_map' _ _).symm
    rw [e1, e2, ← Polynomial.map_mul] at h2
    have h3 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f k) h2
    simp only [Polynomial.coeff_map, Polynomial.coeff_one, if_neg (show k ≠ 0 by omega)] at h3
    exact h3
  rw [chernTop, map_mul, hrel, GlobalTheory.T.topDegreeFormCoeff_eq_tensorSquareTopCoefficient, map_mul, hzero, zero_mul]
  simp

end GlobalTheory.PointChernRel
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle.ClosedPt

variable {ι : Type} {m : ι → ℕ}

theorem par_zero_top {K : Type} [Field K] {g : Mat m K} (h : ∀ τ, (g τ).det ≠ 0) : Par 0 ⊤ g := fun τ =>
  ⟨fun _ _ => trivial, h τ, trivial, fun _ _ hi _ => absurd hi (Nat.not_lt_zero _)⟩

theorem map_mul_inv {R K : Type} [CommRing R] [Field K] (g : R →+* K) (N₁ N₂ : Mat m R) (τ : ι)
    (hu : IsUnit (N₂ τ).det) : (N₁.map g * (N₂.map g)⁻¹) τ = (N₁ τ * (N₂ τ)⁻¹).map g := by
  have e : (N₂ τ).map g * ((N₂ τ)⁻¹).map g = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ g.map_zero g.map_one]
  show (N₁ τ).map g * ((N₂ τ).map g)⁻¹ = _
  rw [Matrix.map_mul, Matrix.inv_eq_right_inv e]

theorem descend {R L : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field L] [Algebra R L]
    [IsFractionRing R L] (N₁ N₂ : Mat m R)
    (h₁ : ∀ τ, (N₁.map (IsLocalRing.residue R) τ).det ≠ 0)
    (h₂ : ∀ τ, (N₂.map (IsLocalRing.residue R) τ).det ≠ 0)
    (hL : Par m ⊤ (N₁.map (algebraMap R L) * (N₂.map (algebraMap R L))⁻¹)) :
    Par m ⊤ (N₁.map (IsLocalRing.residue R) * (N₂.map (IsLocalRing.residue R))⁻¹) := by
  have hu : ∀ τ, IsUnit (N₂ τ).det := fun τ => by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    exact h₂ τ
  have hP := (par_zero_top h₁).mul (par_zero_top h₂).inv
  intro τ
  refine ⟨fun _ _ => trivial, hP.det_ne τ, trivial, fun i j hi hij => ?_⟩
  have h0 := (hL τ).2.2.2 i j hi hij
  rw [map_mul_inv _ _ _ τ (hu τ)] at h0
  rw [map_mul_inv _ _ _ τ (hu τ)]
  have h0' : algebraMap R L ((N₁ τ * (N₂ τ)⁻¹) i j) = 0 := h0
  show IsLocalRing.residue R ((N₁ τ * (N₂ τ)⁻¹) i j) = 0
  rw [(map_eq_zero_iff _ (IsFractionRing.injective R L)).1 h0', map_zero]

variable {F : Type} [Field F]

noncomputable def vals {Y : Var F} {R : Type} [CommRing R] [IsLocalRing R] (v : Sp R ⟶ Y.X) (M : Mat m Y.Fn)
    (hM : ∀ τ a b, M τ a b ∈ (ratOf Y).O (v (IsLocalRing.closedPoint R))) : Mat m R :=
  fun τ a b => RatModel.valLoc (M := ratOf Y) v _ specializes_rfl ⟨M τ a b, hM τ a b⟩

theorem map_val {Y : Var F} {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (σ : R →+* K) (v : Sp R ⟶ Y.X)
    (M : Mat m Y.Fn) (hM : ∀ τ a b, M τ a b ∈ (ratOf Y).O (v (IsLocalRing.closedPoint R))) :
    M.map ((ratOf Y).val (spMap σ ≫ v)) = (vals v M hM).map σ := by
  funext τ
  ext a b
  have := RatModel.val_spMap_comp (M := ratOf Y) σ v specializes_rfl ⟨M τ a b, hM τ a b⟩
  exact this

theorem par_val {Y : Var F} {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (σ : R →+* K) (v : Sp R ⟶ Y.X)
    {M : Mat m Y.Fn} (hM : Par 0 ((ratOf Y).O (v (IsLocalRing.closedPoint R))).toSubring M) :
    Par 0 ⊤ (M.map ((ratOf Y).val (spMap σ ≫ v))) :=
  Par.map_of hM _ (σ.comp (RatModel.valLoc (M := ratOf Y) v _ specializes_rfl))
    (fun x => RatModel.val_spMap_comp (M := ratOf Y) σ v specializes_rfl x)

end GlobalTheory.FlagBundle.ClosedPt

namespace GlobalTheory.FlagBundle.ClosedPt

theorem closedPt_comp {R : Type} [CommRing R] [IsLocalRing R] {Z : Scheme.{0}} (v : Sp R ⟶ Z) :
    (spMap (IsLocalRing.residue R) ≫ v) (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
      v (IsLocalRing.closedPoint R) := by
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  exact congrArg v (IsLocalRing.comap_closedPoint (IsLocalRing.residue R))

theorem gen_specializes {R L : Type} [CommRing R] [IsLocalRing R] [Field L] [Algebra R L] {Z : Scheme.{0}}
    (v : Sp R ⟶ Z) (w : Sp L) : (spMap (algebraMap R L) ≫ v) w ⤳ v (IsLocalRing.closedPoint R) := by
  have h := (IsLocalRing.specializes_closedPoint (spMap (algebraMap R L) w)).map v.continuous
  convert h using 1
  exact Scheme.Hom.comp_apply _ _ _

end GlobalTheory.FlagBundle.ClosedPt


open GlobalTheory.FlagBundle.ClosedPt in
theorem GlobalTheory.FlagBundle.coBear_closedPoint : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (L : Type) [Field L] [Algebra R L] [IsFractionRing R L] (v₁ : Sp R ⟶ Y₁.X) (v₂ : Sp R ⟶ Y₂.X), v₁ ≫ f₁ = v₂ ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (algebraMap R L) ≫ v₁ ≫ f₁) (spMap (algebraMap R L) ≫ v₁) (spMap (algebraMap R L) ≫ v₂) → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (IsLocalRing.residue R) ≫ v₁ ≫ f₁) (spMap (IsLocalRing.residue R) ≫ v₁) (spMap (IsLocalRing.residue R) ≫ v₂) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ R _ _ _ L _ _ _ v₁ v₂ e hgen
  have sub₁ := hR₁.2.1
  have sub₂ := hR₂.2.1
  have hf₁ : f₁ (v₁ (IsLocalRing.closedPoint R)) = (v₁ ≫ f₁) (IsLocalRing.closedPoint R) :=
    (Scheme.Hom.comp_apply _ _ _).symm
  have hf₂ : f₂ (v₂ (IsLocalRing.closedPoint R)) = (v₁ ≫ f₁) (IsLocalRing.closedPoint R) := by
    rw [e]; exact (Scheme.Hom.comp_apply _ _ _).symm
  obtain ⟨A, hA⟩ := Eb.nonempty ((v₁ ≫ f₁) (IsLocalRing.closedPoint R))
  obtain ⟨A₁, hA₁⟩ := S₁.nonempty (v₁ (IsLocalRing.closedPoint R))
  obtain ⟨A₂, hA₂⟩ := S₂.nonempty (v₂ (IsLocalRing.closedPoint R))
  have hM₁ := sub₁ _ A₁ hA₁ A (by rw [hf₁]; exact hA)
  have hM₂ := sub₂ _ A₂ hA₂ A (by rw [hf₂]; exact hA)

  obtain ⟨B, hB, hg, hgP, hb1, hb2⟩ := hgen
  have hA₁g : A₁ ∈ S₁.S ((spMap (algebraMap R L) ≫ v₁) (IsLocalRing.closedPoint L)) :=
    Fr.mem_of_specializes hA₁ (gen_specializes v₁ _)
  have hA₂g : A₂ ∈ S₂.S ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L)) :=
    Fr.mem_of_specializes hA₂ (gen_specializes v₂ _)
  have hAg : A ∈ Eb.S (((spMap (algebraMap R L) ≫ v₁) ≫ f₁) (IsLocalRing.closedPoint L)) := by
    rw [Category.assoc]
    exact Fr.mem_of_specializes hA (gen_specializes (v₁ ≫ f₁) _)
  have hBg : B ∈ Eb.S (((spMap (algebraMap R L) ≫ v₁) ≫ f₁) (IsLocalRing.closedPoint L)) := by
    rw [Category.assoc]
    exact hB
  have heq : (spMap (algebraMap R L) ≫ v₁) ≫ f₁ = (spMap (algebraMap R L) ≫ v₂) ≫ f₂ := by
    rw [Category.assoc, Category.assoc, e]
  have hH := par_val (algebraMap R L) v₁ hM₁
  have hself : Bears S₁ φ₁ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (algebraMap R L) ≫ v₁)))
      (spMap (algebraMap R L) ≫ v₁) :=
    ⟨A₁, hA₁g, by rw [Mat.mul_inv hH.det_ne]; exact Par.one⟩
  obtain ⟨A₂', hA₂', hpar⟩ := GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ L _ _ heq A hAg B hBg
    _ hg hself hb1 hb2

  have hsp₂ := gen_specializes (L := L) v₂ (IsLocalRing.closedPoint L)
  have hG := (Fr.mem_iff hA₂g).1 hA₂'
  have hM₂g : Par 0 ((ratOf Y₂).O ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L))).toSubring
      (A₂ * (A.map φ₂)⁻¹) :=
    hM₂.mono le_rfl fun _ hx => RatModel.O_le_of_specializes hsp₂ hx
  set ψ := RatModel.valHom (M := ratOf Y₂) (spMap (algebraMap R L) ≫ v₂) _
    (RatModel.range_eq_singleton _ (IsLocalRing.closedPoint L))
  have hv : ∀ x : ((ratOf Y₂).O ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L))).toSubring,
      (ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂) x = ψ x := fun _ => rfl
  have heqM : A₂' * (A.map φ₂)⁻¹ = (A₂' * A₂⁻¹) * (A₂ * (A.map φ₂)⁻¹) := by
    rw [mul_assoc, ← mul_assoc A₂⁻¹, Mat.inv_mul (Fr.det_ne hA₂), one_mul]
  have hmap : (A₂' * (A.map φ₂)⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) =
      (A₂' * A₂⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) *
        (A₂ * (A.map φ₂)⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) := by
    rw [heqM]
    exact Par.map_mul_of hG hM₂g ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) ψ hv
  have hGv := Par.map_of hG ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) ψ hv
  have hpar2 := hpar
  erw [hmap] at hpar2
  rw [Mat.mul_inv_rev] at hpar2
  clear hpar
  have hL := hpar2.mul hGv
  rw [mul_assoc, mul_assoc, Mat.inv_mul hGv.det_ne, mul_one] at hL
  rw [map_val (algebraMap R L) v₁ _ (fun τ a b => (hM₁ τ).1 a b),
    map_val (algebraMap R L) v₂ _ (fun τ a b => (hM₂ τ).1 a b)] at hL

  have hk₁ := par_val (IsLocalRing.residue R) v₁ hM₁
  have hk₂ := par_val (IsLocalRing.residue R) v₂ hM₂
  have hD := descend _ _ (by rw [← map_val]; exact hk₁.det_ne) (by rw [← map_val]; exact hk₂.det_ne) hL
  rw [← map_val, ← map_val] at hD
  have hAk : A ∈ Eb.S ((spMap (IsLocalRing.residue R) ≫ v₁ ≫ f₁)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) :=
    (congrArg (fun z => A ∈ Eb.S z) (closedPt_comp (v₁ ≫ f₁))).mpr hA
  have hb₁ : Bears S₁ φ₁ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (IsLocalRing.residue R) ≫ v₁)))
      (spMap (IsLocalRing.residue R) ≫ v₁) :=
    ⟨A₁, (congrArg (fun z => A₁ ∈ S₁.S z) (closedPt_comp v₁)).mpr hA₁, by
      rw [Mat.mul_inv hk₁.det_ne]; exact Par.one⟩
  have hb₂ : Bears S₂ φ₂ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (IsLocalRing.residue R) ≫ v₁)))
      (spMap (IsLocalRing.residue R) ≫ v₂) :=
    ⟨A₂, (congrArg (fun z => A₂ ∈ S₂.S z) (closedPt_comp v₂)).mpr hA₂, hD⟩
  exact ⟨A, hAk, _, hk₁, hb₁, hb₂⟩
end
