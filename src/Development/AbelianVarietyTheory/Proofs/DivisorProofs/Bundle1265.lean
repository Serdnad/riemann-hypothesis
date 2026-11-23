module

public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle744
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFPreservesIsThetaFunction
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.exists_ramification_completeDVR_valuation_eq_mul : ∀ (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∃ e : ℕ, 0 < e ∧ ∀ z : K, vV T.V (iK z) = (e : ℤ) * vAdd 𝔓 z := by
  first | exact @GlobalTheory.CdvrPlaceVal.vV_eq_mul_vAdd | exact GlobalTheory.CdvrPlaceVal.vV_eq_mul_vAdd | (intros; apply GlobalTheory.CdvrPlaceVal.vV_eq_mul_vAdd <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
open GlobalTheory.FockAlg (genSub)

noncomputable section

namespace GlobalTheory.CommonQuot

variable {p q : ℕ}

section General

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem mem_hwSub' (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v - ((μ a : ℚ) : ℂ) • v = 0) ∧
      ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]

theorem isKC_diag' (a : Ix p q) : IsKC (Eab a a) := by
  intro c d h
  rw [Eab, Matrix.single_apply, ite_eq_right]
  rintro ⟨rfl, rfl⟩
  cases a <;> simp [sameBlock] at h

theorem isKC_pos' {a b : Ix p q} (hab : posC a b) : IsKC (Eab a b) := by
  intro c d h
  rw [Eab, Matrix.single_apply, ite_eq_right]
  rintro ⟨rfl, rfl⟩
  cases a <;> cases b <;> simp_all [sameBlock, posC]

theorem map_hw {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z v, g (a Z v) = b Z (g v)) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ hwSub a μ) : g v ∈ hwSub b μ := by
  rw [mem_hwSub'] at hv ⊢
  refine ⟨fun c => ?_, fun c d h => ?_⟩
  · rw [← hg, ← map_smul, ← map_sub, hv.1 c, map_zero]
  · rw [← hg, hv.2 c d h, map_zero]

theorem map_wts {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z v, g (a Z v) = b Z (g v)) {x : V}
    (hx : x ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ) : g x ∈ ⨆ μ : Ix p q → ℚ, wtSub b μ := by
  refine Submodule.iSup_induction _ (motive := fun v => g v ∈ _) hx ?_ (by simp) ?_
  · intro μ y hy
    refine Submodule.mem_iSup_of_mem μ ?_
    simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
    intro c
    rw [← hg, ← map_smul, ← map_sub, hy c, map_zero]
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

end General

section Constructions

end Constructions

section Max

end Max

section Main

end Main

end GlobalTheory.CommonQuot
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open Formalism.BasicNotions.TH

namespace GlobalTheory.FockQuot

variable (P Q R S : ℕ)

def rel (x : ℚ) : Submodule ℂ (Pol P Q R S) :=
  Submodule.span ℂ {g | ∃ (X : Mat P Q) (f : Pol P Q R S), g = fockAct1 P Q R S X f - ((x : ℂ) * X.trace) • f}

def act2 (t : ℚ) : Mat R S →ₗ[ℂ] Module.End ℂ (Pol P Q R S) :=
  fockAct2 P Q R S + (Matrix.traceLinearMap (Ix R S) ℂ ℂ).smulRight ((t : ℂ) • (1 : Module.End ℂ (Pol P Q R S)))

theorem fockSecondActionTraceShift_apply (t : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    act2 P Q R S t Y f = fockAct2 P Q R S Y f + ((t : ℂ) * Y.trace) • f := by
  simp [act2, mul_comm, smul_smul]

theorem fockTraceCharacterRelations_le_comap_secondAction (x t : ℚ) (Y : Mat R S) : rel P Q R S x ≤ (rel P Q R S x).comap (act2 P Q R S t Y) := by
  refine Submodule.span_le.2 ?_
  rintro g ⟨X, f, rfl⟩
  have hc : fockAct2 P Q R S Y (fockAct1 P Q R S X f) = fockAct1 P Q R S X (fockAct2 P Q R S Y f) :=
    (LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.2 X Y) f).symm
  refine Submodule.subset_span ⟨X, act2 P Q R S t Y f, ?_⟩
  simp only [fockSecondActionTraceShift_apply, map_sub, map_add (f := _), map_smul, hc]

theorem isLieAct_fockSecondActionTraceShift (t : ℚ) : IsLieAct (act2 P Q R S t) := by
  intro X Y
  refine LinearMap.ext fun f => ?_
  have h := LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.1 X Y) f
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, fockSecondActionTraceShift_apply, map_add (f := _), map_smul, h, Matrix.trace_sub,
    Matrix.trace_mul_comm X Y, sub_self, mul_zero, zero_smul, add_zero]
  module

def actQ (x t : ℚ) : Mat R S →ₗ[ℂ] Module.End ℂ (Pol P Q R S ⧸ rel P Q R S x) where
  toFun Y := (rel P Q R S x).mapQ (rel P Q R S x) (act2 P Q R S t Y) (fockTraceCharacterRelations_le_comap_secondAction P Q R S x t Y)
  map_add' Y Z := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp [Submodule.mapQ_apply]
  map_smul' c Y := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp [Submodule.mapQ_apply]

theorem actQ_mk (x t : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    actQ P Q R S x t Y (Submodule.Quotient.mk f) = Submodule.Quotient.mk (act2 P Q R S t Y f) := rfl

theorem actQ_lie (x t : ℚ) : IsLieAct (actQ P Q R S x t) := by
  intro X Y
  refine LinearMap.ext fun v => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have h := LinearMap.congr_fun (isLieAct_fockSecondActionTraceShift P Q R S t X Y) f
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h ⊢
  simp only [actQ_mk, h, Submodule.Quotient.mk_sub]

theorem actQ_kfin (x t : ℚ) (v : Pol P Q R S ⧸ rel P Q R S x) :
    ∃ W : Submodule ℂ (Pol P Q R S ⧸ rel P Q R S x), FiniteDimensional ℂ W ∧ v ∈ W ∧
      KStable (actQ P Q R S x t) W := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨W₀, hW₀, hf, hst⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).1
  refine ⟨W₀.map (rel P Q R S x).mkQ, inferInstance, ⟨f, hf, rfl⟩, ?_⟩
  rintro X hX _ ⟨w, hw, rfl⟩
  refine ⟨act2 P Q R S t X w, ?_, rfl⟩
  rw [fockSecondActionTraceShift_apply]
  exact W₀.add_mem (hst X hX w hw) (W₀.smul_mem _ hw)

theorem actQ_wt (x t : ℚ) (μ : Ix R S → ℚ) (g : Pol P Q R S) (hg : g ∈ wtSub (fockAct2 P Q R S) μ) :
    (Submodule.Quotient.mk g : Pol P Q R S ⧸ rel P Q R S x) ∈ wtSub (actQ P Q R S x t) (fun a => μ a + t) := by
  simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hg ⊢
  intro a
  rw [actQ_mk, fockSecondActionTraceShift_apply, hg a]
  simp [Eab, Matrix.trace_single_eq_same, add_smul]

theorem actQ_wts (x t : ℚ) (v : Pol P Q R S ⧸ rel P Q R S x) :
    v ∈ ⨆ μ : Ix R S → ℚ, wtSub (actQ P Q R S x t) μ := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have hf := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).2
  refine Submodule.iSup_induction (fun μ => wtSub (fockAct2 P Q R S) μ)
    (motive := fun g => (Submodule.Quotient.mk g : Pol P Q R S ⧸ rel P Q R S x) ∈
      ⨆ μ : Ix R S → ℚ, wtSub (actQ P Q R S x t) μ) hf ?_ ?_ ?_
  · intro μ g hg
    exact Submodule.mem_iSup_of_mem _ (actQ_wt P Q R S x t μ g hg)
  · simp
  · intro g h hg hh
    rw [Submodule.Quotient.mk_add]
    exact Submodule.add_mem _ hg hh

def gkQ (x t : ℚ) : GKMod R S where
  V := Pol P Q R S ⧸ rel P Q R S x
  act := actQ P Q R S x t
  lie := actQ_lie P Q R S x t
  kfin := actQ_kfin P Q R S x t
  wts := actQ_wts P Q R S x t

theorem mk_fockFirstAction_eq_trace_smul (x : ℚ) (X : Mat P Q) (f : Pol P Q R S) :
    (Submodule.Quotient.mk (fockAct1 P Q R S X f) : Pol P Q R S ⧸ rel P Q R S x) =
      ((x : ℂ) * X.trace) • Submodule.Quotient.mk f := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨X, f, rfl⟩

end GlobalTheory.FockQuot
end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.smoothVectors_unitaryRep_stable_conj_skewAdjoint : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → (∀ g ∈ Formalism.QuantumDeterminants.UH J, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (π g v)) ∧ (∀ w, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π w → ∀ c : ℂ, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (v + c • w)) ∧ ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (dRep π X v) ∧ HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH J, π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v)) ∧ (∀ c : ℝ, dRep π (c • X) v = (c : ℂ) • dRep π X v) ∧ ∀ w, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π w → ⟪dRep π X v, w⟫_ℂ = -⟪v, dRep π X w⟫_ℂ ∧ ∀ c : ℂ, dRep π X (v + c • w) = dRep π X v + c • dRep π X w := by
  first | exact @GlobalTheory.SmVecCalc.smooth_calculus | exact GlobalTheory.SmVecCalc.smooth_calculus | (intros; apply GlobalTheory.SmVecCalc.smooth_calculus <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.DecoClassCount


open scoped TensorProduct in
theorem exists_span_quot {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    ∃ v : Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N),
      Submodule.span R (Set.range v) = ⊤ := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  refine ⟨(TensorProduct.quotTensorEquivQuotSMul N I) ∘ b, ?_⟩
  have h1 : Submodule.span R (Set.range b) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, b.span_eq,
      Submodule.restrictScalars_top]
  have h2 := congrArg (Submodule.map (TensorProduct.quotTensorEquivQuotSMul N I).toLinearMap) h1
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h2
  rw [Set.range_comp]
  exact h2

theorem exists_determining {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    ∃ v : Fin (Module.finrank R N) → N, ∀ f g : N →ₗ[R] R ⧸ I, (∀ i, f (v i) = g (v i)) → f = g := by
  obtain ⟨v, hv⟩ := exists_span_quot (R := R) (N := N) I
  choose u hu using fun i => Submodule.Quotient.mk_surjective _ (v i)
  have hk : ∀ f : N →ₗ[R] R ⧸ I, (I • ⊤ : Submodule R N) ≤ LinearMap.ker f := by
    intro f
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
  refine ⟨u, fun f g hfg => ?_⟩
  have : Submodule.liftQ _ f (hk f) = Submodule.liftQ _ g (hk g) :=
    LinearMap.ext_on_range hv fun i => by
      rw [← hu i]
      exact hfg i
  ext x
  simpa using LinearMap.congr_fun this (Submodule.Quotient.mk x)

theorem finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : Submodule (𝓞 K) V)
    (h : Submodule.span K (p : Set V) = ⊤) : Module.finrank (𝓞 K) p = Module.finrank K V := by
  have : IsLocalizedModule (nonZeroDivisors (𝓞 K)) p.subtype := by
    refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
    · have := isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
      exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s
    · have hy : y ∈ Submodule.span K (p : Set V) := h ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 K)) p.subtype le_rfl,
    IsFractionRing.finrank_right_eq (𝓞 K) K V]

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def IsLocForm (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (φ : Sp E n → 𝓞 E ⧸ P.asIdeal) : Prop :=
  (∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, ∀ y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, φ (x + y) = φ x + φ y) ∧
  ∀ (a : 𝓞 E), ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, φ (a • x) = Ideal.Quotient.mk P.asIdeal a * φ x


omit [StarRing E] in
theorem exists_determining_lattice (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (hN : Submodule.IsLattice E N) :
    ∃ v : Fin n → Sp E n, ∀ φ ψ, IsLocForm P N φ → IsLocForm P N ψ → (∀ i, φ (v i) = ψ (v i)) →
      ∀ x ∈ N, φ x = ψ x := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN))
  have : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 E) N := inferInstance
  have : Module.Projective (𝓞 E) N := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hr : Module.finrank (𝓞 E) N ≤ n := by
    letI : Submodule.IsLattice E N := hN
    rw [← Submodule.IsLattice.finrank_span_eq_finrank E N]
    simpa using Submodule.finrank_le (Submodule.span E (N : Set (Sp E n)))
  obtain ⟨v, hv⟩ := exists_determining (R := 𝓞 E) (N := N) P.asIdeal
  have hle : N ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := fun x hx =>
    ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hx⟩
  let lin : ∀ φ, IsLocForm P N φ → (N →ₗ[𝓞 E] 𝓞 E ⧸ P.asIdeal) := fun φ hφ =>
    { toFun := fun x => φ x
      map_add' := fun x y => hφ.1 x (hle x.2) y (hle y.2)
      map_smul' := fun a x => hφ.2 a x (hle x.2) }
  classical
  refine ⟨fun i => if hi : i.val < Module.finrank (𝓞 E) N then v ⟨i.val, hi⟩ else 0,
    fun φ ψ hφ hψ h x hx => ?_⟩
  have := hv (lin φ hφ) (lin ψ hψ) fun i => by
    change φ (v i) = ψ (v i)
    simpa using h ⟨i.val, lt_of_lt_of_le i.isLt hr⟩
  exact LinearMap.congr_fun this ⟨x, hx⟩

theorem card_fibre_le (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) :
    {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) | d.1.N = N}.Finite ∧ {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) | d.1.N = N}.ncard ≤
      (∏ P ∈ ST, Ideal.absNorm P.asIdeal ^ n) * ∏ w ∈ SG, Ideal.absNorm w.asIdeal ^ (n ^ 2) := by
  classical
  rcases Set.eq_empty_or_nonempty {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) | d.1.N = N} with he | ⟨d0, hd0⟩
  · rw [he]; simp
  have hlat : Submodule.IsLattice E N := by
    have := d0.2.lat
    rwa [show d0.1.N = N from hd0] at this
  choose v hv using fun P => exists_determining_lattice P N hlat
  haveI hfin : ∀ P : HeightOneSpectrum (𝓞 E), Finite (𝓞 E ⧸ P.asIdeal) := fun P =>
    Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  let Φ : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) →
      (∀ P : ST, Fin n → 𝓞 E ⧸ P.1.asIdeal) × (∀ w : SG, Fin n → Fin n → 𝓞 E ⧸ w.1.asIdeal) :=
    fun d => (fun P i => d.1.f P (v P.1 i), fun w i => d.1.be w (v w.1 i))
  have hinj : Set.InjOn Φ {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) | d.1.N = N} := by
    intro d hd d' hd' hdd
    replace hd : d.1.N = N := hd
    replace hd' : d'.1.N = N := hd'
    have hf : ∀ e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG), e.1.N = N → ∀ P : ST, IsLocForm P.1 N (e.1.f P) := by
      rintro e rfl P
      exact ⟨e.2.f_add P, e.2.f_smul P⟩
    have hb : ∀ e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG), e.1.N = N → ∀ (w : SG) (j : Fin n),
        IsLocForm w.1 N fun x => e.1.be w x j := by
      rintro e rfl w j
      exact ⟨fun x hx y hy => congrFun (e.2.be_add w x hx y hy) j,
        fun a x hx => congrFun (e.2.be_smul w a x hx) j⟩
    apply Subtype.ext
    refine d.2.ext_on d'.2 (hd.trans hd'.symm) (fun P x hx => ?_) (fun w x hx => ?_)
    · exact hv P.1 _ _ (hf d hd P) (hf d' hd' P)
        (fun i => congrFun (congrFun (congrArg Prod.fst hdd) P) i) x (hd ▸ hx)
    · funext j
      exact hv w.1 _ _ (hb d hd w j) (hb d' hd' w j)
        (fun i => congrFun (congrFun (congrFun (congrArg Prod.snd hdd) w) i) j) x (hd ▸ hx)
  refine ⟨Set.Finite.of_finite_image (Set.toFinite _) hinj, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn Φ (t := Set.univ) (fun _ _ => Set.mem_univ _) hinj
    (Set.toFinite _)
  refine hle.trans (le_of_eq ?_)
  have hc : ∀ P : HeightOneSpectrum (𝓞 E), Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal :=
    fun P => by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Set.ncard_univ, Nat.card_prod, Nat.card_pi, Nat.card_pi]
  simp only [Nat.card_fun, hc, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, ← sq]
  rw [Finset.prod_coe_sort ST (fun P => Ideal.absNorm P.asIdeal ^ n),
    Finset.prod_coe_sort SG (fun P => Ideal.absNorm P.asIdeal ^ (n ^ 2))]

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
theorem card_classes_le : ∀ (X : Fields), X.Ok → ∀ (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 X.E))), Finite (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG (E := X.E) (n := n) (SG := SG)))) (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) ∧ (Nat.card (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG (E := X.E) (n := n) (SG := SG)))) (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) : ℝ) ≤ (3 * ((Module.finrank ℚ X.E : ℝ) ^ 2 * (n : ℝ) ^ 4 * (|(discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ))) ^ 2)) ^ (3 * Module.finrank ℚ X.E * n ^ 2) * (∏ P ∈ ST, (Ideal.absNorm P.asIdeal : ℝ) ^ n) * ∏ w ∈ SG, (Ideal.absNorm w.asIdeal : ℝ) ^ (n ^ 2) := by
  intro X hX n ST SG
  classical
  have hΓ : ∀ g : UF X.E n, (g, (1 : GLG (E := X.E) (n := n) (SG := SG))) ∈
      (⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG (E := X.E) (n := n) (SG := SG))) := fun g =>
    ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩
  refine ⟨DecoSet.finite_orbits (posStar_of_conj hX.conjE) _ hΓ, ?_⟩
  have := hX.realF
  have := hX.cplxE
  have : Algebra.IsQuadraticExtension X.F X.E := ⟨hX.rankE⟩
  have : IsCMField X.E := IsCMField.ofCMExtension X.F X.E
  have hs : ∀ x : X.E, star x = IsCMField.complexConj X.E x := by
    intro x
    let φ : X.E →+* ℂ := (IsAlgClosed.lift : X.E →ₐ[ℚ] ℂ).toRingHom
    apply φ.injective
    rw [hX.conjE, IsCMField.complexEmbedding_complexConj]
  obtain ⟨Rs, hR, H⟩ := GlobalTheory.exists_finset_decoSet_lattice_reps X.E hs n
  let fib : Submodule (𝓞 X.E) (Sp X.E n) → Finset (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) := fun N =>
    (card_fibre_le ST SG N).1.toFinset
  let B : ℕ := (∏ P ∈ ST, Ideal.absNorm P.asIdeal ^ n) * ∏ w ∈ SG, Ideal.absNorm w.asIdeal ^ (n ^ 2)
  have hfib : ∀ N, (fib N).card ≤ B := fun N => by
    rw [← Set.ncard_eq_toFinset_card _ (card_fibre_le ST SG N).1]
    exact (card_fibre_le ST SG N).2
  have hS : (Rs.biUnion fib).card ≤ Rs.card * B := Finset.card_biUnion_le_card_mul _ _ _ fun N _ => hfib N
  have hsurj : Function.Surjective (fun d : ↥(Rs.biUnion fib) => (Quotient.mk'' d.1 :
      MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG (E := X.E) (n := n) (SG := SG))))
        (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)))) := by
    intro c
    induction c using Quotient.inductionOn' with
    | h d =>
      obtain ⟨g, hg⟩ := H ST SG d
      refine ⟨⟨(g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d, Finset.mem_biUnion.2 ⟨_, hg, ?_⟩⟩, ?_⟩
      · exact (Set.Finite.mem_toFinset _).2 rfl
      · apply Quotient.sound'
        rw [MulAction.orbitRel_apply]
        exact ⟨⟨(g, 1), hΓ g⟩, rfl⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := ↥(Rs.biUnion fib)), Fintype.card_coe] at h1
  have h2 : ((Rs.card * B : ℕ) : ℝ) = Rs.card * (∏ P ∈ ST, (Ideal.absNorm P.asIdeal : ℝ) ^ n) *
      ∏ w ∈ SG, (Ideal.absNorm w.asIdeal : ℝ) ^ (n ^ 2) := by
    simp only [B]
    push_cast
    ring
  refine (Nat.cast_le.2 (h1.trans hS)).trans (h2.le.trans ?_)
  gcongr

end GlobalTheory.DecoClassCount
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory


theorem _root_.GlobalTheory.T.heisenbergOperatorF_preserves_isThetaFunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ),
    Continuous ψ → ∀ (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ ψ f →
      IsThetaFunOF σ JS JT ξ₀ ψ (heisOF σ JS JT ξ₀ ψ w₀ f) := by
  first | exact @GlobalTheory.HeisKeepF.isThetaFunOF_heisOF | exact GlobalTheory.HeisKeepF.isThetaFunOF_heisOF | (intros; apply GlobalTheory.HeisKeepF.isThetaFunOF_heisOF <;> assumption)
end
