module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameReflTransGenCyclicChain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem etale_of_killed_tangent_trivial : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Flat H.hom → (∀ c ∈ w0 ^ r, i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1) → Etale H.hom := by
  intro p _ D R _ b N w0 r S _ s o H i hfin hflat hkill hrep htan
  haveI := hfin
  haveI := hflat
  haveI : LocallyOfFinitePresentation H.hom := inferInstance
  have hinv : ∀ {T : Over S} (a : T ⟶ o.A) (f : o.A ⟶ o.A) [IsMonHom f], a⁻¹ ≫ f = (a ≫ f)⁻¹ := by
    intro T a f _
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← mul_comp, inv_mul_cancel, one_comp]
  haveI : FormallyUnramified H.hom := by
    refine TangentCrit.formallyUnramified_of_tangent H.hom fun k _ _ w hw => ?_
    let x : Sp k ⟶ S := TangentCrit.dualPt k ≫ w ≫ H.hom
    let W : epsPtR x ⟶ H := Over.homMk w hw
    let U : epsPtR x ⟶ H := Over.homMk (TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w)
      (by simp only [Category.assoc]; rfl)
    let e : Over.mk x ⟶ epsPtR x := Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
      (TangentCrit.dualPt_dualBase_assoc k _)
    have heU : e ≫ W = e ≫ U := by
      ext1
      exact (TangentCrit.dualPt_dualBase_assoc k (TangentCrit.dualPt k ≫ w)).symm
    have hv : (W ≫ i) * (U ≫ i)⁻¹ = 1 := by
      refine htan k x _ ?_ ?_
      · have h1 : e ≫ ((W ≫ i) * (U ≫ i)⁻¹) = 1 := by
          rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, heU, mul_inv_cancel]
        exact congrArg (fun q => q.left) h1
      · intro c hc
        haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
        rw [mul_comp, hinv, Category.assoc, Category.assoc, hkill c hc, comp_one, comp_one, inv_one, _root_.mul_one]
    have hWU : W ≫ i = U ≫ i := mul_inv_eq_one.1 hv
    have hk : ∀ c ∈ w0 ^ r, (W ≫ i) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro c hc
      rw [Category.assoc, hkill c hc, comp_one]
    obtain ⟨y, -, hy⟩ := hrep _ (W ≫ i) hk
    have hW := hy W rfl
    have hU := hy U hWU.symm
    exact congrArg (fun q => q.left) (hW.trans hU.symm)
  exact Etale.of_formallyUnramified_of_flat H.hom

end GlobalTheory.UPel.HT.EtLev
end

section

noncomputable section

namespace GlobalTheory.UPel.HT.SplitC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix TensorProduct
open GlobalTheory.UPel.HT

theorem span_embeddings_eq_top (K : Type) [Field K] [NumberField K] :
    Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K)) = ⊤ := by
  rw [eq_top_iff, ← (canonicalEmbedding.latticeBasis K).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨RingOfIntegers.basis K i, ?_⟩
  rw [canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
  rfl

theorem mem_of_embeddings {K : Type} [Field K] [NumberField K] {W : Type} [AddCommGroup W] [Module ℂ W]
    (V : Submodule ℂ W) (L : ((K →+* ℂ) → ℂ) → W) (hadd : ∀ f g, L (f + g) = L f + L g)
    (hsmul : ∀ (a : ℂ) f, L (a • f) = a • L f) (h : ∀ c : 𝓞 K, L (fun τ => τ (c : K)) ∈ V)
    (f : (K →+* ℂ) → ℂ) : L f ∈ V := by
  let Ll : ((K →+* ℂ) → ℂ) →ₗ[ℂ] W := { toFun := L, map_add' := hadd, map_smul' := hsmul }
  have hf : f ∈ Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K)) := by
    rw [span_embeddings_eq_top]; trivial
  have : Ll f ∈ (Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K))).map Ll :=
    Submodule.mem_map_of_mem hf
  have hle : (Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K))).map Ll ≤ V := by
    rw [Submodule.map_span_le]
    rintro _ ⟨c, rfl⟩
    exact h c
  exact hle this

variable {p : ℕ} [Fact p.Prime]

def padicToComplex (j : PadicAlgCl p ≃+* ℂ) : ℤ_[p] →+* ℂ :=
  j.toRingHom.comp ((algebraMap ℚ_[p] (PadicAlgCl p)).comp PadicInt.Coe.ringHom)

def evalTensor (F : Type) [Field F] (κ : ℤ_[p] →+* ℂ) (τ : F →+* ℂ) : 𝓞 F ⊗[ℤ] ℤ_[p] →+* ℂ :=
  (Algebra.TensorProduct.lift (τ.comp (algebraMap (𝓞 F) F)).toIntAlgHom κ.toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

theorem evalTensor_tmul (F : Type) [Field F] (κ : ℤ_[p] →+* ℂ) (τ : F →+* ℂ) (c : 𝓞 F) (z : ℤ_[p]) :
    evalTensor F κ τ (c ⊗ₜ z) = τ (c : F) * κ z := by
  simp [evalTensor]

def bigPhi (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) :
    (D.O ⊗[ℤ] ℤ_[p]) →+* ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) :=
  Pi.ringHom fun τ => (evalTensor D.F κ τ).mapMatrix.comp e.toRingHom

theorem bigPhi_algebraMap (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (c : 𝓞 D.F) (τ : D.F →+* ℂ) :
    bigPhi D κ e (algebraMap (𝓞 D.F) D.O c ⊗ₜ 1) τ = Matrix.scalar (Fin D.m) (τ (c : D.F)) := by
  have h1 : (algebraMap (𝓞 D.F) D.O c ⊗ₜ[ℤ] (1 : ℤ_[p])) = algebraMap (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p]) c := rfl
  rw [h1]
  show (evalTensor D.F κ τ).mapMatrix (e (algebraMap (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p]) c)) = _
  rw [e.commutes c, Matrix.algebraMap_eq_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.scalar_apply, Algebra.TensorProduct.algebraMap_apply, evalTensor_tmul]
  split_ifs <;> simp [evalTensor_tmul]

theorem tmul_one_comm {A : Type} [Ring A] (z : ℤ_[p]) (a : A ⊗[ℤ] ℤ_[p]) :
    a * ((1 : A) ⊗ₜ z) = ((1 : A) ⊗ₜ z) * a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]

theorem bigPhi_one_tmul (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (z : ℤ_[p]) :
    ∃ w : 𝓞 D.F ⊗[ℤ] ℤ_[p], bigPhi D κ e ((1 : D.O) ⊗ₜ z) = fun τ => Matrix.scalar (Fin D.m) (evalTensor D.F κ τ w) := by
  have hc : e ((1 : D.O) ⊗ₜ z) ∈ Set.center (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) := by
    rw [Semigroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, tmul_one_comm]
  rw [Matrix.center_eq_range] at hc
  obtain ⟨w, hw⟩ := hc
  refine ⟨w, funext fun τ => ?_⟩
  show (evalTensor D.F κ τ).mapMatrix (e ((1 : D.O) ⊗ₜ z)) = _
  rw [← hw]
  ext i j
  simp only [Matrix.scalar_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem mem_span_bigPhi (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (y : D.O ⊗[ℤ] ℤ_[p]) :
    bigPhi D κ e y ∈ Submodule.span ℂ (Set.range ((bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom)) := by
  set V := Submodule.span ℂ (Set.range ((bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom))
  have hφ : ∀ x : D.O, bigPhi D κ e (x ⊗ₜ 1) ∈ V := fun x => Submodule.subset_span ⟨x, rfl⟩
  have hL : ∀ (x : D.O) (f : (D.F →+* ℂ) → ℂ),
      (fun τ => Matrix.scalar (Fin D.m) (f τ)) * bigPhi D κ e (x ⊗ₜ 1) ∈ V := by
    intro x
    apply mem_of_embeddings V (fun f => (fun τ => Matrix.scalar (Fin D.m) (f τ)) * bigPhi D κ e (x ⊗ₜ 1))
    · intro f g
      funext τ
      simp only [Pi.mul_apply, Pi.add_apply, map_add (f := _), _root_.add_mul]
    · intro a f
      funext τ
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_mul, _root_.mul_assoc]
    · intro c
      have : (fun τ : D.F →+* ℂ => Matrix.scalar (Fin D.m) (τ (c : D.F))) =
          bigPhi D κ e (algebraMap (𝓞 D.F) D.O c ⊗ₜ 1) := funext fun τ => (bigPhi_algebraMap D κ e c τ).symm
      rw [this, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
      exact hφ _
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x z =>
    obtain ⟨w, hw⟩ := bigPhi_one_tmul D κ e z
    have : x ⊗ₜ[ℤ] z = ((1 : D.O) ⊗ₜ z) * (x ⊗ₜ 1) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]
    rw [this, map_mul, hw]
    exact hL x _
  | add a b ha hb => rw [map_add (f := _)]; exact V.add_mem ha hb

theorem bigPhi_symm_single (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (i j : Fin D.m) (c : 𝓞 D.F) :
    bigPhi D κ e (e.symm (Matrix.single i j (c ⊗ₜ 1))) = fun τ => Matrix.single i j (τ (c : D.F)) := by
  funext τ
  show (evalTensor D.F κ τ).mapMatrix (e (e.symm _)) = _
  rw [e.apply_symm_apply]
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp [evalTensor_tmul]

theorem exists_ringHom_pi_matrix : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p),
    ∃ φ : D.O →+* ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ),
      (∀ (c : 𝓞 D.F) τ, φ (algebraMap (𝓞 D.F) D.O c) τ = Matrix.scalar (Fin D.m) (τ (c : D.F))) ∧
        Submodule.span ℂ (Set.range φ) = ⊤ := by
  intro p _ D
  obtain ⟨e⟩ := D.splitP
  obtain ⟨j⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex p
  set κ := padicToComplex j
  refine ⟨(bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom, fun c τ => bigPhi_algebraMap D κ e c τ, ?_⟩
  rw [eq_top_iff]
  intro X _
  have hX : X = ∑ i, ∑ k, (fun τ => Matrix.single i k (X τ i k)) := by
    funext τ
    simp only [Finset.sum_apply]
    exact Matrix.matrix_eq_sum_single (X τ)
  rw [hX]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k _ => ?_
  apply mem_of_embeddings _ (fun f => fun τ => Matrix.single i k (f τ)) (f := fun τ => X τ i k)
  · intro f g; funext τ; simp [Matrix.single_add]
  · intro a f; funext τ; simp [Matrix.smul_single]
  · intro c
    rw [← bigPhi_symm_single D κ e i k c]
    exact mem_span_bigPhi D κ e _

end GlobalTheory.UPel.HT.SplitC
end
end

section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal

namespace GlobalTheory

theorem glueMeas_univ_ne_top_of_compact {M : Type} [TopologicalSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] {n : ℕ} {ι : Type}
    (e : ι → OpenPartialHomeomorph M (V n)) (hcov : ∀ y, ∃ i, y ∈ (e i).source)
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' (e j).source))
    (r : ι → V n → ℝ) (hr : ∀ i, ContinuousOn (r i) (e i).target)
    (hc : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      r i (e i y) = ‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2 * r j (e j y)) :
    GlobalTheory.ChartGlue.glueMeas e (fun i y => ENNReal.ofReal (r i (e i y))) univ ≠ ∞ := by
  classical
  set μ := GlobalTheory.ChartGlue.glueMeas e (fun i y => ENNReal.ofReal (r i (e i y))) with hμ
  have hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ENNReal.ofReal (r i (e i y)) =
        ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ENNReal.ofReal (r j (e j y)) := by
    intro i j y hi hj
    rw [← ENNReal.ofReal_mul (sq_nonneg _), hc i j y hi hj]
  have hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ μ U < ∞ := by
    intro y
    obtain ⟨i, hi⟩ := hcov y
    have hT : (e i).target ∈ nhds ((e i) y) := (e i).open_target.mem_nhds ((e i).map_source hi)
    obtain ⟨δ, hδ, hδs⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hT
    set U := (e i).source ∩ (e i) ⁻¹' Metric.ball ((e i) y) δ with hUdef
    have hUo : IsOpen U :=
      (e i).continuousOn.isOpen_inter_preimage (e i).open_source Metric.isOpen_ball
    have hUs : U ⊆ (e i).source := inter_subset_left
    have himg : (e i) '' U ⊆ Metric.closedBall ((e i) y) δ := by
      rintro _ ⟨z, hz, rfl⟩
      exact Metric.ball_subset_closedBall hz.2
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall ((e i) y) δ).exists_bound_of_continuousOn ((hr i).mono hδs)
    refine ⟨U, hUo, ⟨hi, Set.mem_preimage.mpr (Metric.mem_ball_self hδ)⟩, ?_⟩
    have hm := GlobalTheory.ChartGlue.measurableSet_image (e i) hUo.measurableSet hUs
    rw [hμ, GlobalTheory.ChartGlue.glueMeas_apply e _ hd hρ i hUo.measurableSet hUs,
      GlobalTheory.ChartGlue.chartMeas_apply_of_subset _ _ hUo.measurableSet hUs]
    calc ∫⁻ v in (e i) '' U, ENNReal.ofReal (r i ((e i) ((e i).symm v)))
        ≤ ∫⁻ _ in (e i) '' U, ENNReal.ofReal C := by
          refine setLIntegral_mono' hm fun v hv => ENNReal.ofReal_le_ofReal ?_
          rw [(e i).right_inv (hδs (himg hv))]
          have := hC v (himg hv)
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans this
      _ = ENNReal.ofReal C * volume ((e i) '' U) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal C * volume (Metric.closedBall ((e i) y) δ) := by
          gcongr
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  choose U hUo hyU hUf using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun y _ => mem_iUnion.2 ⟨y, hyU y⟩)
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ht) ?_)
  exact (measure_biUnion_finset_le t U).trans_lt (ENNReal.sum_lt_top.2 fun y _ => hUf y)

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

namespace GlobalTheory.GlueCover

open GlobalTheory.ChartGlue

variable {n : ℕ}

section Null

variable {X ι : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

end Null

section Cover

variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}


set_option autoImplicit false in
open MeasureTheory Set Topology in
open scoped ENNReal in
variable {n : ℕ} in
variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A} in
omit [T2Space A] [T2Space B] in
theorem _root_.GlobalTheory.GlueCover.exists_sheet
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (_root_.ReciprocityTheory.L2DbarEstimates.Y.ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖_root_.GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (_root_.ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖_root_.GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {z : B}
    (hch : ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {U : Set B} (hUo : IsOpen U) (hzU : z ∈ U) :
    ∃ M : Set B, M ⊆ U ∧ IsOpen M ∧ z ∈ M ∧ IsOpen (m '' M) ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ m '' M →
        _root_.GlobalTheory.ChartGlue.glueMeas e' ρ' (M ∩ m ⁻¹' Q) = _root_.GlobalTheory.ChartGlue.glueMeas e ρ Q := by
  obtain ⟨i, j, hzj, hzi, hcompat⟩ := hch
  have hMo : IsOpen (U ∩ (e' j).source ∩ m ⁻¹' (e i).source) :=
    (hUo.inter (e' j).open_source).inter ((e i).open_source.preimage hm)
  refine ⟨U ∩ (e' j).source ∩ m ⁻¹' (e i).source, fun w hw => hw.1.1, hMo,
    ⟨⟨hzU, hzj⟩, hzi⟩, ?_, ?_⟩
  · have hm_eq : ∀ w ∈ U ∩ (e' j).source ∩ m ⁻¹' (e i).source,
        (e i).symm (e' j w) = m w := by
      intro w hw
      rw [(hcompat w hw.1.2 hw.2).1, (e i).left_inv hw.2]
    have himage : m '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source) =
        (e i).symm '' (e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source)) := by
      rw [Set.image_image]
      exact (Set.image_congr hm_eq).symm
    rw [himage]
    have hS : IsOpen (e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source)) :=
      (e' j).isOpen_image_of_subset_source hMo (fun w hw => hw.1.2)
    refine (e i).symm.isOpen_image_of_subset_source hS ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [OpenPartialHomeomorph.symm_source, (hcompat w hw.1.2 hw.2).1]
    exact (e i).map_source hw.2
  · intro Q hQ hQM
    have hQi : Q ⊆ (e i).source := by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := hQM hq
      exact hw.2
    have hPm : MeasurableSet (U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q) :=
      hMo.measurableSet.inter (hm.measurable hQ)
    have hPj : U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q ⊆ (e' j).source :=
      fun w hw => hw.1.1.2
    rw [_root_.GlobalTheory.ChartGlue.glueMeas_apply e' ρ' hd' hρ' j hPm hPj,
      _root_.GlobalTheory.ChartGlue.glueMeas_apply e ρ hd hρ i hQ hQi,
      _root_.GlobalTheory.ChartGlue.chartMeas_apply_of_subset _ _ hPm hPj,
      _root_.GlobalTheory.ChartGlue.chartMeas_apply_of_subset _ _ hQ hQi]
    have himg : e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q) = e i '' Q := by
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨m w, hw.2, ((hcompat w hw.1.1.2 hw.1.2).1).symm⟩
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨w, hw, rfl⟩ := hQM hq
        exact ⟨w, ⟨hw, hq⟩, (hcompat w hw.1.2 hw.2).1⟩
    rw [himg]
    refine setLIntegral_congr_fun (_root_.GlobalTheory.ChartGlue.measurableSet_image _ hQ hQi) ?_
    rintro v ⟨q, hq, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hQM hq
    beta_reduce
    rw [(e i).left_inv hw.2, ← (hcompat w hw.1.2 hw.2).1, (e' j).left_inv hw.1.2]
    exact (hcompat w hw.1.2 hw.2).2

end Cover

end GlobalTheory.GlueCover
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_square_affine_h1_vanish : ∀ (R : Type) [CommRing R], (∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme (A ⊗ A) ∧ SmoothOfRelativeDimension (g + g) (A ⊗ A).hom) ∧ ∀ (X : Scheme.{0}) [IsAffine X] (s : X ⟶ Sp R) (c : HO1 s), c = 0 := by
  first | exact @GlobalTheory.Obs.sq_abelian_and_affine_H1 | exact GlobalTheory.Obs.sq_abelian_and_affine_H1 | (intros; apply GlobalTheory.Obs.sq_abelian_and_affine_H1 <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleCohomology_coefficient_longExactSequence : GlobalTheory.EtC.A7 := by
  first | (exact @GlobalTheory.EtC.coefSeq_exact) | (exact GlobalTheory.EtC.coefSeq_exact) | (intros; apply GlobalTheory.EtC.coefSeq_exact  <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.ainfSquareZeroFrame_reflTransGen_cyclic_chain : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, Relation.ReflTransGen (fun N N' : Ideal F.B => IsStep p F.θ N' N) ⊤ (Ideal.span {(p : F.B)}) := by
  first | exact @GlobalTheory.BChain.reflTransGen_isStep | exact GlobalTheory.BChain.reflTransGen_isStep | (intros; apply GlobalTheory.BChain.reflTransGen_isStep <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog


open MvPowerSeries in
theorem _root_.GlobalTheory.QLog.hasPeriod_reduce : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : _root_.GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), ∀ F : _root_.GlobalTheory.QLog.BFrame ε, ∀ (G : _root_.GlobalTheory.PDivGroup p O) (d : ℕ) (c : _root_.GlobalTheory.QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), _root_.GlobalTheory.QLog.IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (E : Type) [CommRing E] [Algebra O E], _root_.GlobalTheory.QLog.IsFrame p E (RingHom.id O) → ∀ Θ : F.Q →+* E, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O E (F.θ b)) → ∀ (f : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y : F.B), _root_.GlobalTheory.QLog.QL μ' ⊤ f → c.HasPeriod F.θ t f y → c.HasPeriod (RingHom.id O) t (map Θ f) (F.θ y) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F G d c μ' _ _ E _ _ hE Θ hΘ f t y _ hy
  have hF := F.frame
  rw [_root_.GlobalTheory.QLog.Chart.hasPeriod_iff c hF] at hy
  rw [_root_.GlobalTheory.QLog.Chart.hasPeriod_iff c hE]
  intro n z hz
  choose w hw using fun i => hF.surj (z i)
  obtain ⟨q, hq, b, hb⟩ := hy n w (fun i => by rw [hw]; exact hz i)
  refine ⟨Θ q, ?_, F.θ b, ?_⟩
  · have hmap := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF _ w f f q q
      hq).2.2 O E F.θ Θ hΘ
    simpa [hw] using hmap
  · have h2 := congrArg Θ hb
    rw [map_mul, map_pow, map_natCast, hΘ, map_add (f := _), map_mul, map_pow, map_natCast] at h2
    exact h2

end GlobalTheory.QLog
end
