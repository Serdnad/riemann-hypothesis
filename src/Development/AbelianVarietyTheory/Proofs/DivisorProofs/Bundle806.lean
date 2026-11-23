module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCoboundaryOfDegreeTwoImageCoboundaryAl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetTwoCocycleEqCechImageAddCoboundary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle754
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle769
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.exists_cech_primitive_of_image_coboundary : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (z : CC F 1), δ F 1 z = 0 → ∀ g : C0 F, e1 F z = d0 F g → ∃ c : CC F 0, δ F 0 c = z := by
  first | exact @GlobalTheory.CechHOneInj.exists_cech_primitive | exact GlobalTheory.CechHOneInj.exists_cech_primitive | (intros; apply GlobalTheory.CechHOneInj.exists_cech_primitive <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.orderedCechDifferential_zero_const_one : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R), δ F 0 (fun _ => 1) = 0 := by
  first | exact @GlobalTheory.CechPoset.δ_zero_one | exact GlobalTheory.CechPoset.δ_zero_one | (intros; apply GlobalTheory.CechPoset.δ_zero_one <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.orderedCech_cochainsOne_coboundary_comm : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 1), d1 F (e1 F c) = e2 F (δ F 1 c) := by
  first | exact @GlobalTheory.CechPosetDegreeOne.orderedCechToCatCochainsOne_coboundary_comm | exact GlobalTheory.CechPosetDegreeOne.orderedCechToCatCochainsOne_coboundary_comm | (intros; apply GlobalTheory.CechPosetDegreeOne.orderedCechToCatCochainsOne_coboundary_comm <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.exists_cech_coboundary_of_degreeTwo_image_coboundary' : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (y : CC F 2), δ F 2 y = 0 → ∀ f : C1 F, e2 F y = d1 F f → ∃ c : CC F 1, δ F 1 c = y := by
  first | exact @GlobalTheory.CechPoset.exists_cech_coboundary_of_degreeTwo_image_coboundary | exact GlobalTheory.CechPoset.exists_cech_coboundary_of_degreeTwo_image_coboundary | (intros; apply GlobalTheory.CechPoset.exists_cech_coboundary_of_degreeTwo_image_coboundary <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.exists_cocycle_sub_e2_eq_d1 : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (w : Z2 F), ∃ y : CC F 2, δ F 2 y = 0 ∧ ∃ f : C1 F, w.1 - e2 F y = d1 F f := by
  first | exact @GlobalTheory.CechPoset.posetTwoCocycle_eq_cechImage_add_coboundary | exact GlobalTheory.CechPoset.posetTwoCocycle_eq_cechImage_add_coboundary | (intros; apply GlobalTheory.CechPoset.posetTwoCocycle_eq_cechImage_add_coboundary <;> assumption)
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

namespace GlobalTheory.FlagQuotHaar

theorem secondCountable_GL_complex (r : ℕ) : SecondCountableTopology (GL (Fin r) ℂ) := by
  have : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → ℂ))
  have : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem secondCountable_Upq (r p : ℕ) : SecondCountableTopology (Upq r p) := by
  have := secondCountable_GL_complex r
  exact TopologicalSpace.Subtype.secondCountableTopology _

theorem sigmaFinite_haarU (r p : ℕ) : SigmaFinite (haarU r p) := by
  have := secondCountable_Upq r p
  unfold haarU
  infer_instance

theorem lintegral_pi_haarU_reindex {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') (r p q : ℕ) (h : p = q)
    (F : (ι' → Matrix (Fin r) (Fin r) ℂ) → ℝ≥0∞) :
    ∫⁻ g : ι → Upq r p, F (fun i' => ((g (e.symm i') : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))
        ∂Measure.pi (fun _ => haarU r p) =
      ∫⁻ g : ι' → Upq r q, F (fun i' => ((g i' : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))
        ∂Measure.pi (fun _ => haarU r q) := by
  subst h
  have := sigmaFinite_haarU r p
  have hmp := measurePreserving_piCongrLeft (fun _ : ι' => haarU r p) e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  congr 1
  funext g
  congr 1
  funext i'
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

theorem trF_frameOf {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E'] [NumberField E']
    [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ) (g : RealGrp X) :
    trF X X' e (frameOf X g) = rmul (baseFr X')
      (fun τ' => (((g (e.symm τ') : Upq r X.p0) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  funext τ'
  have h : (mat (baseFr X) (e.symm τ')).det ≠ 0 := (X.signature (e.symm τ')).choose_spec.1
  show mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ *
      (mat (baseFr X) (e.symm τ') * (((g (e.symm τ') : Upq r X.p0) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) =
    mat (baseFr X') τ' * (((g (e.symm τ') : Upq r X.p0) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (mat (baseFr X) (e.symm τ')), Matrix.nonsing_inv_mul _ h.isUnit,
    Matrix.one_mul]

theorem lintegral_trF_frameOf : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E']
    [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ), X.p0 = X'.p0 →
    ∀ (φ : Frame X'.Ψ r → ℝ≥0∞), Measurable φ →
      ∫⁻ g, φ (trF X X' e (frameOf X g)) ∂haarR X = ∫⁻ g, φ (frameOf X' g) ∂haarR X' := by
  intro E _ _ _ r E' _ _ _ X X' e hp φ _
  simp_rw [trF_frameOf]
  exact lintegral_pi_haarU_reindex e r X.p0 X'.p0 hp (fun M => φ (rmul (baseFr X') M))

end GlobalTheory.FlagQuotHaar
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
open scoped Matrix
namespace GlobalTheory.FlagTransport
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {E' : Type} [Field E'] [NumberField E'] [IsCMField E']

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_mul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M N : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (M * N) = Nᵀ * gram τ G M * N.map (starRingEnd ℂ) := by
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

variable (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ)

def entEquiv : Ent X ≃ Ent X' := Equiv.prodCongr e (Equiv.refl _)

def idxEquiv : Fin (nd X) ≃ Fin (nd X') :=
  (Fintype.equivFin (Ent X)).symm.trans ((entEquiv X X' e).trans (Fintype.equivFin (Ent X')))

def coordIso : V (nd X) ≃ₗᵢ[ℂ] V (nd X') := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (idxEquiv X X' e)

theorem coordIso_apply (z : V (nd X)) (k : Fin (nd X')) :
    coordIso X X' e z k = z ((idxEquiv X X' e).symm k) := rfl

theorem idxEquiv_symm_equivFin (τ' : X'.Ψ) (p : {p : Fin r × Fin r // p.2 < p.1}) :
    (idxEquiv X X' e).symm (Fintype.equivFin (Ent X') (τ', p)) = Fintype.equivFin (Ent X) (e.symm τ', p) := by
  show Fintype.equivFin (Ent X) ((entEquiv X X' e).symm
    ((Fintype.equivFin (Ent X')).symm (Fintype.equivFin (Ent X') (τ', p)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem nmat_coordIso (z : V (nd X)) (τ' : X'.Ψ) :
    nmat X' (coordIso X X' e z) τ' = nmat X z (e.symm τ') := by
  funext a b
  unfold nmat
  split_ifs with h
  · refine (coordIso_apply X X' e z _).trans ?_
    exact congrArg (fun k : Fin (nd X) => z k) (idxEquiv_symm_equivFin X X' e τ' _)
  · rfl
  · rfl

def coordIsoR : V (nd X) ≃ₗᵢ[ℝ] V (nd X') :=
  { (coordIso X X' e).toLinearEquiv.restrictScalars ℝ with norm_map' := (coordIso X X' e).norm_map }

theorem coordIso_mp : MeasurePreserving (coordIso X X' e) := (coordIsoR X X' e).measurePreserving

theorem map_restrict_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} (S : α ≃ᵐ β) (hS : MeasurePreserving S μ ν) {Ω : Set α} {Ω' : Set β}
    (hΩ : S ⁻¹' Ω' = Ω) {d : α → ℝ≥0∞} {d' : β → ℝ≥0∞} (hd : ∀ x, d' (S x) = d x) :
    Measure.map S ((μ.restrict Ω).withDensity d) = (ν.restrict Ω').withDensity d' := by
  ext A hA
  rw [S.map_apply, withDensity_apply _ hA, withDensity_apply _ (S.measurable hA), ← hS.map_eq,
    S.restrict_map, S.restrict_map, lintegral_map_equiv, hΩ]
  simp_rw [hd]

theorem trF_cpt (z : V (nd X)) :
    trF X X' e (cpt X (baseFr X) z) = cpt X' (baseFr X') (coordIso X X' e z) := by
  funext τ'
  have hB : IsUnit (mat (baseFr X) (e.symm τ')).det :=
    isUnit_iff_ne_zero.2 (X.signature (e.symm τ')).choose_spec.1
  have h1 : mat (cpt X (baseFr X) z) (e.symm τ') =
      mat (baseFr X) (e.symm τ') * mat (nmat X z) (e.symm τ') := rfl
  have h2 : mat (nmat X' (coordIso X X' e z)) τ' = mat (nmat X z) (e.symm τ') := by
    unfold mat; rw [nmat_coordIso]
  show (mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * mat (cpt X (baseFr X) z) (e.symm τ') :
      Matrix (Fin r) (Fin r) ℂ) = (mat (baseFr X') τ' * mat (nmat X' (coordIso X X' e z)) τ' : Matrix (Fin r) (Fin r) ℂ)
  rw [h1, h2, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hB]

theorem gram_cpt_base {F : Type} [Field F] [NumberField F] [IsCMField F] (Y : Data F r) (z : V (nd Y)) (τ : Y.Ψ) :
    gram τ.1 Y.Gm (mat (cpt Y (baseFr Y) z) τ) =
      (mat (nmat Y z) τ)ᵀ * sgnMat r Y.p0 * (mat (nmat Y z) τ).map (starRingEnd ℂ) := by
  have h1 : mat (cpt Y (baseFr Y) z) τ = mat (baseFr Y) τ * mat (nmat Y z) τ := rfl
  rw [h1, gram_mul_right, baseFr_mem Y τ]

variable {X X'} in
theorem dmin_coordIso (hp : X.p0 = X'.p0) (z : V (nd X)) (τ' : X'.Ψ) (i : Fin (r + 1)) :
    dmin X'.Gm (cpt X' (baseFr X') (coordIso X X' e z)) τ' i = dmin X.Gm (cpt X (baseFr X) z) (e.symm τ') i := by
  have h2 : mat (nmat X' (coordIso X X' e z)) τ' = mat (nmat X z) (e.symm τ') := by
    unfold mat; rw [nmat_coordIso]
  unfold dmin
  rw [gram_cpt_base, gram_cpt_base, h2, hp]

theorem det_cpt_base_ne {F : Type} [Field F] [NumberField F] [IsCMField F] (Y : Data F r) (z : V (nd Y)) (τ : Y.Ψ) :
    (mat (cpt Y (baseFr Y) z) τ).det ≠ 0 ↔ (mat (nmat Y z) τ).det ≠ 0 := by
  have h1 : mat (cpt Y (baseFr Y) z) τ = mat (baseFr Y) τ * mat (nmat Y z) τ := rfl
  have hB : (mat (baseFr Y) τ).det ≠ 0 := (Y.signature τ).choose_spec.1
  rw [h1, Matrix.det_mul, mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨hB, h⟩⟩

variable {X X'} in
theorem mem_dom_coordIso (hp : X.p0 = X'.p0) (z : V (nd X)) :
    cpt X' (baseFr X') (coordIso X X' e z) ∈ X'.dom ↔ cpt X (baseFr X) z ∈ X.dom := by
  show (∀ τ' : X'.Ψ, _ ∧ _) ↔ (∀ τ : X.Ψ, _ ∧ _)
  refine Iff.trans ?_ e.symm.forall_congr_right
  refine forall_congr' fun τ' => ?_
  have h2 : mat (nmat X' (coordIso X X' e z)) τ' = mat (nmat X z) (e.symm τ') := by
    unfold mat; rw [nmat_coordIso]
  rw [det_cpt_base_ne, det_cpt_base_ne, h2, hp]
  simp only [dmin_coordIso e hp]

variable {X X'} in
theorem densF_coordIso (hp : X.p0 = X'.p0) (z : V (nd X)) :
    densF X' (baseFr X') (coordIso X X' e z) = densF X (baseFr X) z := by
  unfold densF
  simp only [dmin_coordIso e hp]
  exact (Fintype.prod_equiv e.symm _ _ fun _ => rfl)

variable {X X'} in
theorem map_muF (hp : X.p0 = X'.p0) :
    Measure.map (coordIso X X' e).toHomeomorph.toMeasurableEquiv (muF X (baseFr X)) = muF X' (baseFr X') := by
  unfold muF
  refine map_restrict_withDensity _ (coordIso_mp X X' e) ?_ ?_
  · ext z
    exact mem_dom_coordIso e hp z
  · intro z
    exact congrArg ENNReal.ofReal (densF_coordIso e hp z)

end

theorem lintegral_trF_cpt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E']
    [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ), X.p0 = X'.p0 →
    ∀ (φ : Frame X'.Ψ r → ℝ≥0∞), Measurable φ →
      ∫⁻ z, φ (trF X X' e (cpt X (baseFr X) z)) ∂muF X (baseFr X) =
        ∫⁻ z, φ (cpt X' (baseFr X') z) ∂muF X' (baseFr X') := by
  intro E _ _ _ r E' _ _ _ X X' e hp φ _
  rw [← map_muF e hp, lintegral_map_equiv]
  simp_rw [trF_cpt]
  rfl

end GlobalTheory.FlagTransport
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem cechFG_of_transfer {Z Z' : Scheme.{0}} {J : Type} (W : J → Z.Opens) (W' : J → Z'.Opens)
    (R : Type) [CommRing R]
    (act : ∀ i i' : J, R →+* Γ(Z, W i ⊓ W i')) (act' : ∀ i i' : J, R →+* Γ(Z', W' i ⊓ W' i'))
    (φ1 : ∀ i, Γ(Z, W i) →+* Γ(Z', W' i))
    (φ2 : ∀ i i', Γ(Z, W i ⊓ W i') →+* Γ(Z', W' i ⊓ W' i'))
    (φ3 : ∀ i i' i'', Γ(Z, W i ⊓ W i' ⊓ W i'') →+* Γ(Z', W' i ⊓ W' i' ⊓ W' i''))
    (h1 : ∀ i, Function.Surjective (φ1 i))
    (h2 : ∀ i i', Function.Bijective (φ2 i i'))
    (h3 : ∀ i i' i'', Function.Injective (φ3 i i' i''))
    (hl : ∀ i i' x, φ2 i i' (resG Z inf_le_left x) = resG Z' inf_le_left (φ1 i x))
    (hr : ∀ i i' x, φ2 i i' (resG Z inf_le_right x) = resG Z' inf_le_right (φ1 i' x))
    (ha : ∀ i i' i'' x, φ3 i i' i'' (resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') x) =
      resG Z' (inf_le_left : W' i ⊓ W' i' ⊓ W' i'' ≤ W' i ⊓ W' i') (φ2 i i' x))
    (hb : ∀ i i' i'' x, φ3 i i' i'' (resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') x) =
      resG Z' (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        W' i ⊓ W' i' ⊓ W' i'' ≤ W' i' ⊓ W' i'') (φ2 i' i'' x))
    (hc : ∀ i i' i'' x, φ3 i i' i'' (resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') x) =
      resG Z' (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W' i ⊓ W' i' ⊓ W' i'' ≤ W' i ⊓ W' i'') (φ2 i i'' x))
    (hact : ∀ i i' r, φ2 i i' (act i i' r) = act' i i' r) :
    CechFG W' R act' → CechFG W R act := by
  rintro ⟨N, e', he', hc'⟩
  choose g hg using fun (k : Fin N) (i i' : J) => (h2 i i').2 (e' k i i')
  refine ⟨N, g, ?_, ?_⟩
  · intro k i i' i''
    apply h3 i i' i''
    have := he' k i i' i''
    rw [map_add (f := _), ha, hb, hc, hg, hg, hg]
    exact this
  · intro c hcoc
    obtain ⟨r, h', hh⟩ := hc' (fun i i' => φ2 i i' (c i i')) (by
      intro i i' i''
      have := congrArg (φ3 i i' i'') (hcoc i i' i'')
      rw [map_add (f := _), ha, hb, hc] at this
      exact this)
    choose h hh1 using fun i => h1 i (h' i)
    refine ⟨r, h, fun i i' => (h2 i i').1 ?_⟩
    have e1 := hh i i'

    rw [map_add (f := _), map_sub, map_sum, hl, hr, hh1, hh1]
    simp only [map_mul, hact, hg]
    exact e1

theorem appLE_resG {X Y : Scheme.{0}} (f : X ⟶ Y) {O₁ O₂ : Y.Opens} {V₁ V₂ : X.Opens} (hO : O₂ ≤ O₁)
    (hV : V₂ ≤ V₁) (e₁ : V₁ ≤ f ⁻¹ᵁ O₁) (e₂ : V₂ ≤ f ⁻¹ᵁ O₂) (x : Γ(Y, O₁)) :
    (f.appLE O₂ V₂ e₂).hom (resG Y hO x) = resG X hV ((f.appLE O₁ V₁ e₁).hom x) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem appLE_bijective {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] {O : Y.Opens}
    (hO : O ≤ f.opensRange) {V : X.Opens} (hV : V = f ⁻¹ᵁ O) (e : V ≤ f ⁻¹ᵁ O) :
    Function.Bijective (f.appLE O V e).hom := by
  subst hV
  rw [Scheme.Hom.appLE_eq_app]
  haveI := f.isIso_app O hO
  exact (asIso (f.app O)).commRingCatIsoToRingEquiv.bijective

end GlobalTheory.CechTr

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem preimage_inf' {X Y : Scheme.{0}} (f : X ⟶ Y) (A B : Y.Opens) :
    f ⁻¹ᵁ (A ⊓ B) = f ⁻¹ᵁ A ⊓ f ⁻¹ᵁ B := by
  ext x; simp

theorem appLE_act {G X : Scheme.{0}} (p : G ⟶ X) (U : X.Opens) (hU : IsAffineOpen U) (O : G.Opens)
    (V : (pullback p hU.fromSpec).Opens) (hO : O ≤ p ⁻¹ᵁ U)
    (e : V ≤ pullback.fst p hU.fromSpec ⁻¹ᵁ O) (r : Γ(X, U)) :
    ((pullback.fst p hU.fromSpec).appLE O V e).hom ((p.appLE U O hO).hom r) =
      (secMap (R := Γ(X, U)) (pullback.snd p hU.fromSpec) V).hom r := by
  have e' : V ≤ (pullback.snd p hU.fromSpec ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [← pullback.condition]; exact e.trans (Scheme.Hom.preimage_mono _ hO)
  have key : (pullback.snd p hU.fromSpec ≫ hU.fromSpec).appLE U V e' =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (pullback.snd p hU.fromSpec).appLE ⊤ V le_top := by
    rw [Scheme.Hom.comp_appLE, hU.fromSpec_app_self, Category.assoc]
    exact congrArg ((Scheme.ΓSpecIso Γ(X, U)).inv ≫ ·) (Scheme.Hom.map_appLE _ _ _)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq pullback.condition _ _ _ e', key]
  rfl

end GlobalTheory.CechTr

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem cechFG_of_baseChange_affineOpen (G X : Scheme.{0}) (p : G ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (J : Type) (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U) :
    CechFG (fun i => pullback.fst p hU.fromSpec ⁻¹ᵁ W i) Γ(X, U)
        (fun i i' => (secMap (R := Γ(X, U)) (pullback.snd p hU.fromSpec) _).hom) →
      CechFG W Γ(X, U) (fun i i' => (p.appLE U (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) := by
  have hR : ∀ O : G.Opens, O ≤ p ⁻¹ᵁ U → O ≤ (pullback.fst p hU.fromSpec).opensRange := by
    intro O hO
    rw [Scheme.Hom.opensRange_pullbackFst, IsAffineOpen.opensRange_fromSpec]
    exact hO
  have h2e : ∀ A B : G.Opens, pullback.fst p hU.fromSpec ⁻¹ᵁ A ⊓ pullback.fst p hU.fromSpec ⁻¹ᵁ B =
      pullback.fst p hU.fromSpec ⁻¹ᵁ (A ⊓ B) := fun A B => (preimage_inf' _ A B).symm
  refine cechFG_of_transfer W _ _ _ _
    (fun i => ((pullback.fst p hU.fromSpec).appLE (W i) _ le_rfl).hom)
    (fun i i' => ((pullback.fst p hU.fromSpec).appLE (W i ⊓ W i') _ (h2e _ _).le).hom)
    (fun i i' i'' => ((pullback.fst p hU.fromSpec).appLE (W i ⊓ W i' ⊓ W i'') _
      (by rw [h2e, h2e])).hom)
    (fun i => (appLE_bijective _ (hR _ (hWU i)) rfl _).2)
    (fun i i' => appLE_bijective _ (hR _ (inf_le_left.trans (hWU i))) (h2e _ _) _)
    (fun i i' i'' => (appLE_bijective _ (hR _ (inf_le_left.trans (inf_le_left.trans (hWU i))))
      (by rw [h2e, h2e]) _).1)
    (fun i i' x => appLE_resG _ _ _ _ _ x)
    (fun i i' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' r => appLE_act p U hU _ _ _ _ r)

theorem cechFG_of_baseChange_affine (G X : Scheme.{0}) (p : G ⟶ X) (U : X.affineOpens) (J : Type)
    (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1) :
    CechFG (fun i => pullback.fst p U.2.fromSpec ⁻¹ᵁ W i) Γ(X, U.1)
        (fun i i' => (secMap (R := Γ(X, U.1)) (pullback.snd p U.2.fromSpec) _).hom) →
      CechFG W Γ(X, U.1) (fun i i' => (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) :=
  cechFG_of_baseChange_affineOpen G X p U.1 U.2 J W hWU

end GlobalTheory.CechTr
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem cechOneCochainToPosetCochain_coboundary_exists : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R)
    (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)),
    ∀ c : GlobalTheory.KS.C1 U, IsCob U c → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf c := by
  intro I _ X R _ s U hU hinf c hc
  obtain ⟨b, hb⟩ := hc
  refine ⟨fun T => (cv s U hU hinf T).symm (rsT (b T.unop.pt) (cap U T.unop)), ?_⟩
  funext T T' φ
  apply (cv s U hU hinf T').injective
  have hTT' : cap U T'.unop ≤ cap U T.unop := cap_mono U (leOfHom φ.unop)
  have hp : cap U T.unop ≤ U T.unop.pt := cap_le U T.unop.pt_mem
  have hp' : cap U T'.unop ≤ U T'.unop.pt := cap_le U T'.unop.pt_mem
  have hle : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt := le_inf (hTT'.trans hp) hp'
  rw [amitsur_d0_apply, map_sub, cv_mp, cv_toPos, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hb,
    GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_rsT inf_le_right hle, GlobalTheory.KS.rsT_rsT inf_le_left hle, GlobalTheory.KS.rsT_rsT hp hTT']

end GlobalTheory.CechCmp
end
end
