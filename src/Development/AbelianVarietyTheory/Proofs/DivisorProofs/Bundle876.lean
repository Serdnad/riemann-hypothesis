module

public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle026
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle847
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle123
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Smooth.IntegralClosure
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_finite_affine_cover_infClosed : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    IsSeparated s → QuasiCompact s → ∃ (J : Type) (_ : Finite J) (_ : SemilatticeInf J)
      (U : J → X.affineOpens), Monotone U ∧ (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) ∧
        ⨆ i, (U i).1 = ⊤ := by
  intro R _ X s hsep hqc
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have hdiag : IsAffineHom (pullback.diagonal s) := inferInstance
  have hinf : ∀ U V : X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
    fun U V hU hV => isAffineHom_diagonal_iff.mp hdiag ⊤ (isAffineOpen_top _) U (by simp) V
      (by simp) hU hV
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
    (by simpa using isCompact_univ)
  set A : Set X.Opens := infClosure ((fun i : X.affineOpens => i.1) '' S) with hAdef
  have hA : ∀ U ∈ A, IsAffineOpen U :=
    infClosure_min (t := {U | IsAffineOpen U}) (by rintro _ ⟨i, -, rfl⟩; exact i.2)
      (fun a ha b hb => hinf a b ha hb)
  letI inst : SemilatticeInf A :=
    Subtype.semilatticeInf (fun _ _ ha hb => infClosed_infClosure ha hb)
  haveI hfin : Finite A := ((hS.image _).infClosure).to_subtype
  refine ⟨A, hfin, inst, fun j => ⟨j.1, hA j.1 j.2⟩, fun a b h => h, fun i j => rfl, ?_⟩
  apply top_le_iff.mp
  rw [e]
  exact iSup₂_le fun i hi => le_iSup_of_le (⟨i.1, subset_infClosure ⟨i, hi, rfl⟩⟩ : A) le_rfl

end GlobalTheory
end

section

open IsLocalRing Polynomial

namespace GlobalTheory.PurityLoc

noncomputable def integralClosureEquiv (R C : Type) [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.IsIntegral R C] (M : Submonoid R)
    (h : IsIntegrallyClosedIn C (Localization (Algebra.algebraMapSubmonoid C M))) :
    C ≃ₐ[R] integralClosure R (Localization (Algebra.algebraMapSubmonoid C M)) :=
  AlgEquiv.ofBijective
    ((IsScalarTower.toAlgHom R C _).codRestrict _ fun c =>
      (Algebra.IsIntegral.isIntegral (R := R) c).map (IsScalarTower.toAlgHom R C _))
    (by
      obtain ⟨hinj, hcl⟩ := isIntegrallyClosedIn_iff.mp h
      refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun ⟨x, hx⟩ => ?_⟩
      obtain ⟨c, hc⟩ := hcl (hx.tower_top (A := C))
      exact ⟨c, Subtype.ext hc⟩)

theorem isReduced_isArtinianRing_localization (R C : Type) [CommRing R] [IsDomain R] [CommRing C]
    [Algebra R C] [Module.Finite R C]
    (h : Algebra.Etale (Localization.AtPrime (⊥ : Ideal R))
      (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C)) :
    IsReduced (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) ∧
      IsArtinianRing (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) := by
  haveI := h
  haveI hKfr : IsFractionRing R (Localization.AtPrime (⊥ : Ideal R)) := by
    exact (congrArg (fun M : Submonoid R => IsLocalization M (Localization.AtPrime (⊥ : Ideal R)))
      (Ideal.primeCompl_bot (α := R))).mp inferInstance
  letI : Field (Localization.AtPrime (⊥ : Ideal R)) := IsFractionRing.toField R
  haveI : IsReduced (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) :=
    Algebra.FormallyUnramified.isReduced_of_field (Localization.AtPrime (⊥ : Ideal R)) _
  haveI : IsArtinianRing (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) :=
    IsArtinianRing.of_finite (Localization.AtPrime (⊥ : Ideal R)) _
  letI : Algebra C (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) :=
    Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))
      (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) := by
    exact (congrArg (fun M : Submonoid R => IsLocalization (Algebra.algebraMapSubmonoid C M)
      (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C)) (Ideal.primeCompl_bot (α := R))).mp
      (IsLocalization.tensorRight (S := C) (Localization.AtPrime (⊥ : Ideal R)) (⊥ : Ideal R).primeCompl)
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))
    (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))
    (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C)
  exact ⟨isReduced_of_injective e.toRingHom e.injective, e.toRingEquiv.symm.isArtinianRing⟩

theorem etale_atPrime_of_isIntegrallyClosedIn : ∀ (R C : Type) [CommRing R] [IsDomain R] [CommRing C] [Algebra R C] [Module.Finite R C],
    IsIntegrallyClosedIn C (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) →
    ∀ (P : Ideal R) [P.IsPrime], IsRegularLocalRing (Localization.AtPrime P) →
    (∀ (P' : Ideal R) [P'.IsPrime], P' ≤ P → P'.height ≤ 1 →
      Algebra.Etale (Localization.AtPrime P') (TensorProduct R (Localization.AtPrime P') C)) →
    Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  intro R C _ _ _ _ _ hC P _ hreg hP
  haveI := hreg
  obtain ⟨hred, hart⟩ := isReduced_isArtinianRing_localization R C (hP ⊥ bot_le (by simp))
  let iC := integralClosureEquiv R C (nonZeroDivisors R) hC
  have hb := TensorProduct.toIntegralClosure_bijective_of_isLocalization (R := R)
    (S := Localization.AtPrime P)
    (B := Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl
  let Φ : TensorProduct R (Localization.AtPrime P) C ≃ₐ[Localization.AtPrime P]
      integralClosure (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl iC).trans (AlgEquiv.ofBijective _ hb)
  have hRE : IsReduced (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) ∧
      IsArtinianRing (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) := by
    letI : Algebra (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))
        (TensorProduct R (Localization.AtPrime P)
          (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) :=
      Algebra.TensorProduct.rightAlgebra
    haveI : IsLocalization (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl)
        (TensorProduct R (Localization.AtPrime P)
          (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) :=
      IsLocalization.tensorRight (Localization.AtPrime P) P.primeCompl
    haveI := hred
    haveI := hart
    let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl)
      (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))
      (Localization (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl))
    exact ⟨isReduced_of_injective e.toRingHom e.injective,
      IsArtinianRing.localization_artinian (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl) _⟩
  have hunit : ∀ s : Localization.AtPrime P, s ≠ 0 → IsUnit (algebraMap (Localization.AtPrime P)
      (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) s) := by
    intro s hs
    obtain ⟨⟨r, u⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl s
    have hr : r ≠ 0 := by rintro rfl; exact hs (by simp)
    have h0 : IsUnit (algebraMap R (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) r) := by
      rw [IsScalarTower.algebraMap_apply R C (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))]
      exact IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))
        (⟨algebraMap R C r, Algebra.mem_algebraMapSubmonoid_of_mem
          (⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩ : nonZeroDivisors R)⟩ :
            Algebra.algebraMapSubmonoid C (nonZeroDivisors R))
    have h1 : IsUnit (algebraMap (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) (algebraMap R _ r)) := by
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime P),
        ← (Algebra.TensorProduct.includeRight (R := R) (A := Localization.AtPrime P)
          (B := Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))).commutes r]
      exact h0.map _
    have h2 : algebraMap (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))
          (IsLocalization.mk' (Localization.AtPrime P) r u) *
        algebraMap (Localization.AtPrime P) _ (algebraMap R (Localization.AtPrime P) u) =
        algebraMap (Localization.AtPrime P) _ (algebraMap R (Localization.AtPrime P) r) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    rw [← h2] at h1
    exact isUnit_of_mul_isUnit_left h1
  have hnz : NoZeroSMulDivisors (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) := ⟨fun {s x} h => by
    by_cases hs : s = 0
    · exact Or.inl hs
    · right
      rw [Algebra.smul_def] at h
      exact (hunit s hs).mul_right_eq_zero.mp h⟩
  haveI hfin : Module.Finite (Localization.AtPrime P) (integralClosure (Localization.AtPrime P)
      (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))) :=
    Module.Finite.equiv Φ.toLinearEquiv
  have hq : ∀ (q : Ideal (Localization.AtPrime P)) [q.IsPrime], q.height ≤ 1 →
      Algebra.Etale (Localization.AtPrime q) (TensorProduct (Localization.AtPrime P)
        (Localization.AtPrime q) (integralClosure (Localization.AtPrime P)
          (TensorProduct R (Localization.AtPrime P)
            (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))))) := by
    intro q _ hq1
    have hle : q.comap (algebraMap R (Localization.AtPrime P)) ≤ P := by
      have := Ideal.comap_mono (f := algebraMap R (Localization.AtPrime P))
        (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹q.IsPrime›))
      exact this.trans (Localization.AtPrime.under_maximalIdeal (I := P)).le
    have hh : (q.comap (algebraMap R (Localization.AtPrime P))).height ≤ 1 :=
      (le_of_eq (IsLocalization.height_under P.primeCompl q)).trans hq1
    haveI h1 := GlobalTheory.OffDivisor.etale_localization_of_comap R (Localization.AtPrime P) C _ q rfl
      (hP _ hle hh)
    exact Algebra.Etale.of_equiv ((Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P)
      (Localization.AtPrime q) (Localization.AtPrime q) C).symm.trans
        (Algebra.TensorProduct.congr AlgEquiv.refl Φ))
  haveI := GlobalTheory.PurityProd.etale_integralClosure_of_isArtinianRing (Localization.AtPrime P) _
    hRE.1 hRE.2 hnz hfin hq
  exact Algebra.Etale.of_equiv Φ.symm

end GlobalTheory.PurityLoc
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SaturationClosed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


omit [NumberField E] [IsCMField E] in
def adjEnt {Ψ : Finset (E →+* ℂ)} (k w : Frame Ψ r) (τ : Ψ) (a c : Fin r) : ℂ :=
  (Matrix.adjugate (mat k τ) * mat w τ) a c

omit [NumberField E] [IsCMField E] in
theorem lact_lact {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact a (lact b x) = lact (a * b) x := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
    Matrix (Fin r) (Fin r) ℂ) = (((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl


omit [NumberField E] [IsCMField E] in
theorem adjEnt_rmul {Ψ : Finset (E →+* ℂ)} (k b : Frame Ψ r) (hb : b ∈ Bor Ψ r) (τ : Ψ) (a c : Fin r)
    (hca : c < a) : adjEnt k (rmul k b) τ a c = 0 := by
  have h1 : mat (rmul k b) τ = mat k τ * mat b τ := rfl
  rw [adjEnt, h1, ← Matrix.mul_assoc, Matrix.adjugate_mul]
  simp [Matrix.smul_mul, mat, (hb τ).2 a c hca]


omit [NumberField E] [IsCMField E] in
theorem exists_of_adjEnt {Ψ : Finset (E →+* ℂ)} (k w : Frame Ψ r) (hk : ∀ τ, (mat k τ).det ≠ 0)
    (hw : ∀ τ, (mat w τ).det ≠ 0) (h0 : ∀ τ a c, c < a → adjEnt k w τ a c = 0) :
    ∃ b ∈ Bor Ψ r, w = rmul k b := by
  refine ⟨fun τ => ((mat k τ)⁻¹ * mat w τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩, ?_⟩
  · show ((mat k τ)⁻¹ * mat w τ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero (hk τ)) (hw τ)
  · show ((mat k τ)⁻¹ * mat w τ) a c = 0
    rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply]
    have := h0 τ a c hca
    rw [adjEnt] at this
    rw [this, smul_zero]
  · funext τ
    show mat w τ = mat k τ * ((mat k τ)⁻¹ * mat w τ)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (hk τ))]

omit [NumberField E] [IsCMField E] in
theorem continuous_mat {α : Type} [TopologicalSpace α] {Ψ : Finset (E →+* ℂ)} {f : α → Frame Ψ r}
    (hf : Continuous f) (τ : Ψ) : Continuous fun p => mat (f p) τ :=
  (continuous_apply τ).comp hf

omit [NumberField E] [IsCMField E] in
theorem continuous_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) :
    Continuous (lact (Ψ := Ψ) γ) := by
  refine continuous_pi fun τ => ?_
  exact continuous_const.matrix_mul (continuous_mat continuous_id τ)

omit [NumberField E] [IsCMField E] in
theorem continuous_adjEnt {α : Type} [TopologicalSpace α] {Ψ : Finset (E →+* ℂ)} {f g : α → Frame Ψ r}
    (hf : Continuous f) (hg : Continuous g) (τ : Ψ) (a c : Fin r) :
    Continuous fun p => adjEnt (f p) (g p) τ a c :=
  (((continuous_mat hf τ).matrix_adjugate).matrix_mul (continuous_mat hg τ)).matrix_elem a c

theorem eventually_not_mem_saturation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (x : Frame X.Ψ r) (ρ : ℝ), (∀ z : V (nd X), ‖z‖ ≤ ρ → z ∈ OmF X x) →
    ∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) →
    ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y' = lact γ (rmul (cpt X x z) b) := by
  intro E _ _ _ r X x ρ hΩ y hy hny
  have hcpt : Continuous (cpt X x) := (GlobalTheory.InterpCompare.differentiable_chart X x).continuous
  have hK : IsCompact (Metric.closedBall (0 : V (nd X)) ρ) := isCompact_closedBall 0 ρ
  have key : ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ, ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z),
      ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, p.1 ≠ lact γ (rmul (cpt X x p.2) b) := by
    intro z hz
    have hz' : ‖z‖ ≤ ρ := by simpa using hz
    have hk : cpt X x z ∈ X.dom := hΩ z hz'
    obtain ⟨U, hU, U', hU', hfin⟩ := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X y hy _ hk
    have h1 : ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z), p.1 ∈ U ∧ cpt X x p.2 ∈ U' := by
      refine Filter.Eventually.and (continuous_fst.continuousAt.preimage_mem_nhds hU) ?_
      exact (hcpt.comp continuous_snd).continuousAt.preimage_mem_nhds hU'
    have h2 : ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z),
        ∀ δ ∈ {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r, lact γ u = rmul u' b},
          ∃ τ : X.Ψ, ∃ a c : Fin r, c < a ∧ adjEnt (cpt X x p.2) (lact δ p.1) τ a c ≠ 0 := by
      refine (Filter.eventually_all_finite hfin).2 fun δ hδ => ?_
      have hopen : IsOpen {p : Frame X.Ψ r × V (nd X) |
          ∃ τ : X.Ψ, ∃ a c : Fin r, c < a ∧ adjEnt (cpt X x p.2) (lact δ p.1) τ a c ≠ 0} := by
        simp only [Set.setOf_exists]
        refine isOpen_iUnion fun τ => isOpen_iUnion fun a => isOpen_iUnion fun c => ?_
        by_cases hca : c < a
        · simp only [hca, true_and]
          exact isOpen_ne_fun (continuous_adjEnt (hcpt.comp continuous_snd)
            ((continuous_lact δ).comp continuous_fst) τ a c) continuous_const
        · simp [hca]
      refine hopen.mem_nhds ?_
      by_contra hcon
      simp only [Set.mem_setOf_eq, not_exists, not_and, not_not] at hcon
      have hdk : ∀ τ, (mat (cpt X x z) τ).det ≠ 0 := fun τ => (hk τ).1
      have hdw : ∀ τ, (mat (lact δ y) τ).det ≠ 0 := by
        intro τ h0
        have e : y = lact δ⁻¹ (lact δ y) := by rw [lact_lact, inv_mul_cancel, lact_one]
        have : (mat y τ).det = 0 := by
          rw [e]
          show (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat (lact δ y) τ).det = 0
          rw [Matrix.det_mul, h0, mul_zero]
        exact (hy τ).1 this
      obtain ⟨b, hb, hwb⟩ := exists_of_adjEnt _ _ hdk hdw hcon
      refine hny ⟨δ⁻¹, X.Γ.inv_mem hδ.1, b, hb, z, hz', ?_⟩
      rw [← hwb, lact_lact, inv_mul_cancel, lact_one]
    filter_upwards [h1, h2] with p hp1 hp2
    intro γ hγ b hb he
    have hδ : γ⁻¹ ∈ {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r, lact γ u = rmul u' b} := by
      refine ⟨X.Γ.inv_mem hγ, p.1, hp1.1, cpt X x p.2, hp1.2, b, hb, ?_⟩
      rw [he, lact_lact, inv_mul_cancel, lact_one]
    obtain ⟨τ, a, c, hca, hne⟩ := hp2 _ hδ
    apply hne
    rw [he, lact_lact, inv_mul_cancel, lact_one]
    exact adjEnt_rmul _ _ hb τ a c hca
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun y' z => ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, y' ≠ lact γ (rmul (cpt X x z) b)) key] with y' hy'
  rintro ⟨γ, hγ, b, hb, z, hz, he⟩
  exact hy' z (by simpa using hz) γ hγ b hb he

end GlobalTheory.SaturationClosed
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

theorem _root_.GlobalTheory.T.leviForms_transport_to_orthonormal_chart_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x1 b : Frame X.Ψ r) (z : V (nd X)), IsOrth X x1 → z ∈ OmF X x0 → b ∈ Bor X.Ψ r → cpt X x0 z = rmul x1 b → ∀ ξ : Fin (nd X) → ℂ, ∃ ξ' : Fin (nd X) → ℂ, (∀ la : Wt X.Ψ r, leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 ξ') ∧ ∃ B : Frame X.Ψ r, (∀ τ (a c : Fin r), c < a → B τ a c = 0) ∧ ∀ τ, mat x0 τ * (mat (nmat X (WithLp.toLp 2 ξ)) τ - 1) = mat x1 τ * ((mat (nmat X (WithLp.toLp 2 ξ')) τ - 1) * mat b τ + mat B τ) := by
  first | exact @GlobalTheory.LeviWeightChart.levi_transport_origin | exact GlobalTheory.LeviWeightChart.levi_transport_origin | (intros; apply GlobalTheory.LeviWeightChart.levi_transport_origin <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.OActPull

theorem exists_oAct_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    (b : OAct O G) {f : S' ⟶ S} {G' : Over S'} [GrpObj G'] {φ : G'.left ⟶ G.left}
    (hg : IsGrpPullback G' G f φ) : ∃ a : OAct O G', ∀ z, (a.act z).left ≫ φ = φ ≫ (b.act z).left := by
  have inj : ∀ {T : Over S'} {x y : T ⟶ G'}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act : O → (G' ⟶ G') := fun a => Over.homMk (hg.1.lift (φ ≫ (b.act a).left) G'.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act a).left ≫ φ = φ ≫ (b.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G') a, pushPt hg.1.w (x ≫ act a) = pushPt hg.1.w x ≫ b.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ G'), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  refine ⟨⟨act, fun a => isMonHom_of_mul _ fun T x y => inj ?_, inj ?_, fun a c => inj ?_, fun a c => inj ?_⟩, ha⟩
  · have := b.hom a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp]
  · rw [← Category.id_comp (act 1), pa, b.one, Category.comp_id]
  · rw [← Category.id_comp (act (a * c)), pa, pa, ← Category.id_comp (act a), pa, b.mul, Category.assoc]
  · refine Eq.trans ?_ (pm (act a) (act c)).symm
    rw [← Category.id_comp (act (a + c)), ← Category.id_comp (act a), ← Category.id_comp (act c), pa, pa, pa, b.add]
    exact MonObj.comp_mul _ _ _

end GlobalTheory.OActPull
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def IsFactorAH (u : HolUnif A L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) : Prop :=
  Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧
    ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
      u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l)

theorem isFactorAH_of_isAH {u : HolUnif A L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) : IsFactorAH u Hm χ :=
  ⟨h.1, h.2.2.1, h.2.2.2⟩

theorem isAH_of_isFactorAH {u : HolUnif A L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : IsFactorAH u Hm χ) (pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) : u.IsAH Hm χ :=
  ⟨h.1, pos, h.2.1, h.2.2⟩

end GlobalTheory.TorusRM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegel_level_sections_spread_to_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → (∀ a, (e.lev a).left ≫ j = spMap R₀.subtype ≫ (d₀.lev a).left) → (∀ a, (e.lev a).left ≫ (j ≫ ψ) = (spMap R₀.subtype ≫ h₀) ≫ (u.lev a).left) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left), IsGrpPullback d₁.A u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) → (∀ a, (d₁.lev a).left ≫ φ₁ = spMap (Subring.inclusion hle) ≫ (d₀.lev a).left) → ∀ a, (d₁.lev a).left ≫ (φ₁ ≫ ψ) = (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev a).left := by
  first | exact @GlobalTheory.siegel_levels_spread_to_subring | exact GlobalTheory.siegel_levels_spread_to_subring | (intros; apply GlobalTheory.siegel_levels_spread_to_subring; all_goals assumption)
end
