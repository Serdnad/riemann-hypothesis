module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import GroundTheory.HeightsAndTheta.Heights.ArithDegree
public import Mathlib.Order.CompletePartialOrder
public import Development.WeilBound.CoreStatements.AmpleLineBundles.SpanLeOfMem
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.NefFibresCombination
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle007
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle001
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle039
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

theorem _root_.GlobalTheory.T.multihomogeneous_value_well_defined : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (a : K → ℤ) (s : Ω) (z : (Σ k, ι k) → 𝕜) (w : 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → HasVal y a s z w → (∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h) ∧ ∀ w', HasVal y a s z w' → w' = w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.hasVal_read_of_rep | exact GlobalTheory.CompanionTheory.Ar.Small.hasVal_read_of_rep | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.hasVal_read_of_rep <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

def tz {I : Type} [Fintype I] (Z : Matrix I I ℂ) (z : I → ℂ) : I → ℂ := z - Z *ᵥ star z

abbrev Ix (Ψ : Type) (j j' : ℕ) : Type := (Fin j' ⊕ Fin j) × Ψ

def emb {E : Type} [Field E] [NumberField E] {Ψ : Type} {j j' : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (i : Ix Ψ j j') : 𝓞 E →+* ℂ :=
  Sum.elim (fun _ => σ i.2) (fun _ => (starRingEnd ℂ).comp (σ i.2)) i.1

def bigZ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ :=
  blockDiagonal fun τ => fromBlocks 0 (ballMat q t τ)ᵀ (ballMat q t τ) 0

def bigZe {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (t : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (bigZ q t).submatrix e.symm e.symm

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.continuous_hermitian_matrix_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ) (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ), (∀ x, (R x).form = form) → (∀ v, Continuous fun x => (R x).P v) → Continuous fun x => (R x).Hm := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_Hm | exact GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_Hm | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_Hm <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.gram_det_pos_iff_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u : Fin m → Fin g → ℂ), (LinearIndependent ℂ u → 0 < (R.gram u).det.re ∧ (R.gram u).det.im = 0) ∧ ((R.gram u).det ≠ 0 → LinearIndependent ℂ u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.GramPos.gram_det_pos_iff | exact GlobalTheory.CompanionTheory.Ar.Cusp.GramPos.gram_det_pos_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.GramPos.gram_det_pos_iff <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.riemannLattice_quotient_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R₁ : RiemLat E g' Λ') (D : AddSubgroup Λ) (π : Λ → Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (Hm' : Matrix (Fin g') (Fin g') ℂ) (B' : 𝓞 E →+* Module.End ℂ (Fin g' → ℂ)), (∀ x', ∃ x ∈ D, π x = x') → (∀ x ∈ D, ∀ y ∈ D, π (x + y) = π x + π y) → (∀ (a : 𝓞 E), ∀ x ∈ D, a • x ∈ D ∧ π (a • x) = a • π x) → (∀ x ∈ D, π x = 0 → q (R.P x) = 0) → (∀ a z, B' a (q z) = q (R.B a z)) → Hm'.IsHermitian → (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm' *ᵥ star z).re) → (∀ x ∈ D, ∀ y ∈ D, (q (R.P x) ⬝ᵥ Hm' *ᵥ star (q (R.P y))).im = R₁.form (π x) (π y)) → ∃ R' : RiemLat E g' Λ', R'.form = R₁.form ∧ R'.Hm = Hm' ∧ ∀ x ∈ D, R'.P (π x) = q (R.P x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_assemble_of_quot | exact GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_assemble_of_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_assemble_of_quot <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section Diag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ}

def diagAct (ty : Fin g → (E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) :=
  (Algebra.lmul ℂ (Fin g → ℂ)).toRingHom.comp (Pi.ringHom fun i => (ty i).comp (algebraMap (𝓞 E) E))

theorem diagAct_apply (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (x : Fin g → ℂ) (i : Fin g) :
    diagAct ty a x i = ty i (a : E) * x i := rfl

theorem embedding_eq_of_integers {s t : E →+* ℂ} (h : ∀ a : 𝓞 E, s (a : E) = t (a : E)) : s = t :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem mem_eigSp_diagAct (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) (x : Fin g → ℂ) :
    x ∈ eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E)) ↔ ∀ i, ty i ≠ s → x i = 0 := by
  have key : ∀ (a : 𝓞 E) (i : Fin g),
      ((diagAct ty a - (s.comp (algebraMap (𝓞 E) E)) a • LinearMap.id : Module.End ℂ (Fin g → ℂ)) x) i = (ty i (a : E) - s (a : E)) * x i := by
    intro a i
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      diagAct_apply, RingHom.comp_apply]
    ring_nf
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i hi
    by_contra hx
    refine hi (embedding_eq_of_integers fun a => ?_)
    have h1 := congrFun (h a) i
    rw [key] at h1
    simpa [hx, sub_eq_zero] using h1
  · intro h a
    funext i
    rw [key]
    by_cases hi : ty i = s
    · simp [hi]
    · simp [h i hi]

def eigSpDiagEquiv (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) :
    eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E)) ≃ₗ[ℂ] ({i // ty i = s} → ℂ) where
  toFun x j := x.1 j.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨fun i => open Classical in if h : ty i = s then f ⟨i, h⟩ else 0,
    (mem_eigSp_diagAct ty s _).2 fun i hi => by simp [hi]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases h : ty i = s
    · simp [h]
    · simp [h, (mem_eigSp_diagAct ty s x.1).1 x.2 i h]
  right_inv f := by
    funext j
    simp [j.2]

theorem finrank_eigSp_diagAct (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) :
    Module.finrank ℂ (eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E))) = Nat.card {i // ty i = s} := by
  classical
  rw [(eigSpDiagEquiv ty s).finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Diag

theorem free_of_period {Λ : Type} [AddCommGroup Λ] {g : ℕ} (P : Λ →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    Module.Free ℤ Λ ∧ Module.Finite ℤ Λ ∧ Module.finrank ℤ Λ = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by
    have : ((L : Set (Fin g → ℂ))) = Set.range P := by
      ext x; simp [L]
    rw [this, hs]⟩
  let e : Λ ≃ₗ[ℤ] L := (AddMonoidHom.ofInjective hi).toIntLinearEquiv
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, ZLattice.rank ℝ L, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem riemLat_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod D ty P → ∃ R : RiemLat E g D.La, R.P = P ∧ R.form = D.EF ∧ (∀ a x i, R.B a x i = ty i (a : E) * x i) ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q := by
  intro E _ _ _ H D g ty P hty hP
  obtain ⟨hact, hinj, hdisc, hspan, Hm, hherm, hpos, him⟩ := hP
  obtain ⟨hfree, hfin, hrank⟩ := free_of_period P hinj hdisc hspan
  refine ⟨{ free := hfree, fin := hfin, rank := hrank, form := D.EF, alt := D.alt, unimod := D.unimod
            adj := ?_, P := P, Hm := Hm, herm := hherm, pos := hpos, im := him, B := diagAct ty, act := ?_ },
    rfl, rfl, fun a x i => diagAct_apply ty a x i, fun s => ?_⟩
  · intro a a' h x y
    have : a' = H.bar a := by
      apply RingOfIntegers.ext
      rw [H.bar_eq a]
      exact h
    rw [this]
    exact D.adj a x y
  · intro a x
    funext i
    exact hact a x i
  · show Module.finrank ℂ (eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E))) = _
    rw [finrank_eigSp_diagAct]
    by_cases h : s (H.rt : E) = H.rt0
    · rw [if_pos h]
      exact (hty s).1 h
    · rw [if_neg h]
      exact (hty s).2 h

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.OrthSum

variable {K : Type} [Field K] [NumberField K]

theorem disjoint_of_orth (E : HermitianBundle.{0} K) {F G : Submodule (𝓞 K) E.carrier}
    (h : OrthAt E F G) : Disjoint F G := by
  rw [Submodule.disjoint_def]
  intro x hxF hxG
  by_contra hx
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hli : LinearIndependent (𝓞 K) (fun _ : Unit => x) := linearIndependent_unique_iff.mpr hx
  have hpos := gramDet_pos E.metric σ hli
  have h0 := h σ x hxF x hxG
  rw [← FibreSpace.inner_equiv E.metric σ] at h0
  have h0' : inner ℂ (fibreVec E.metric σ x) (fibreVec E.metric σ x) = 0 := h0
  have hz : GroundTheory.Heights₂.Heights.gramDet E.metric σ (fun _ : Unit => x) = 0 := by
    unfold GroundTheory.Heights₂.Heights.gramDet
    rw [Matrix.det_unique, Matrix.gram_apply, h0', Complex.zero_re]
  linarith

theorem gramDet_sumElim (E : HermitianBundle.{0} K) (σ : K →+* ℂ) {a b : ℕ}
    {s : Fin a → E.carrier} {t : Fin b → E.carrier} (hs : LinearIndependent (𝓞 K) s)
    (ht : LinearIndependent (𝓞 K) t)
    (h : ∀ i j, inner ℂ (fibreVec E.metric σ (s i)) (fibreVec E.metric σ (t j)) = 0) :
    gramDet E.metric σ (Sum.elim s t) = gramDet E.metric σ s * gramDet E.metric σ t := by
  have hconj : ∀ i j, inner ℂ (fibreVec E.metric σ (t j)) (fibreVec E.metric σ (s i)) = 0 := by
    intro i j
    rw [← inner_conj_symm, h i j, map_zero]
  have hM : (Matrix.gram ℂ fun k => fibreVec E.metric σ (Sum.elim s t k)) =
      Matrix.fromBlocks (Matrix.gram ℂ fun i => fibreVec E.metric σ (s i)) 0 0
        (Matrix.gram ℂ fun j => fibreVec E.metric σ (t j)) := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.gram_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, h, hconj]
  have him : ∀ {n : ℕ} (v : Fin n → FibreSpace E.metric σ), (Matrix.gram ℂ v).det.im = 0 := by
    intro n v
    have hA : (Matrix.gram ℂ v).conjTranspose = Matrix.gram ℂ v := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.gram_apply]
      exact inner_conj_symm _ _
    have hdet := Matrix.det_conjTranspose (Matrix.gram ℂ v)
    rw [hA] at hdet
    exact Complex.conj_eq_iff_im.mp hdet.symm
  unfold GroundTheory.Heights₂.Heights.gramDet
  rw [hM, Matrix.det_fromBlocks_zero₂₁, Complex.mul_re, him, him, mul_zero, sub_zero]

theorem degree_sup (E : HermitianBundle.{0} K) {F G : Submodule (𝓞 K) E.carrier}
    (h : OrthAt E F G) : E.degree (F ⊔ G) = E.degree F + E.degree G := by
  have hd : Disjoint F G := disjoint_of_orth E h
  obtain ⟨s, hs, hsF⟩ := CoverDenseAlt.exists_fam E F
  obtain ⟨t, ht, htG⟩ := CoverDenseAlt.exists_fam E G
  have hNs : Submodule.span (𝓞 K) (Set.range s) ≤ F := CoverDenseAlt.span_le_of_mem hsF
  have hNt : Submodule.span (𝓞 K) (Set.range t) ≤ G := CoverDenseAlt.span_le_of_mem htG
  have hst : LinearIndependent (𝓞 K) (Sum.elim s t) := hs.sum_type ht (hd.mono hNs hNt)
  have hmem : ∀ i, Sum.elim s t i ∈ F ⊔ G := by
    rintro (i | i)
    · exact Submodule.mem_sup_left (hsF i)
    · exact Submodule.mem_sup_right (htG i)
  have hcard : Fintype.card (Fin (E.rank F) ⊕ Fin (E.rank G)) = E.rank (F ⊔ G) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, CoverDenseAlt.rank_sup E hd]
  obtain ⟨hiF, hF⟩ := CoverDenseAlt.deg_eq E F hs hsF (Fintype.card_fin _)
  obtain ⟨hiG, hG⟩ := CoverDenseAlt.deg_eq E G ht htG (Fintype.card_fin _)
  obtain ⟨-, hFG⟩ := CoverDenseAlt.deg_eq E (F ⊔ G) hst hmem hcard
  have hidx : CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range (Sum.elim s t))) (F ⊔ G) =
      CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range s)) F * CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range t)) G := by
    rw [Set.Sum.elim_range, Submodule.span_union,
      ← CoverDenseAlt.idx_mul (sup_le_sup_right hNs _) (sup_le_sup_left hNt F)]
    congr 1
    · exact CoverDenseAlt.idx_sup hNs (hd.mono_right hNt)
    · rw [sup_comm F, sup_comm F G]
      exact CoverDenseAlt.idx_sup hNt hd.symm
  have hlog : ∀ σ : K →+* ℂ, Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ (Sum.elim s t)) =
      Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ s) + Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ t) := by
    intro σ
    have hgram := gramDet_sumElim E σ hs ht (fun i j => by
      have h1 := h σ _ (hsF i) _ (htG j)
      rw [← FibreSpace.inner_equiv E.metric σ] at h1
      exact h1)
    rw [hgram, Real.log_mul (gramDet_pos E.metric σ hs).ne' (gramDet_pos E.metric σ ht).ne']
  rw [hFG, hF, hG, hidx, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hiF) (Nat.cast_ne_zero.mpr hiG)]
  simp only [hlog, Finset.sum_add_distrib]
  ring

theorem degree_bot (E : HermitianBundle.{0} K) : E.degree ⊥ = 0 := by
  have hrk : Fintype.card (Fin 0) = E.rank ⊥ := by
    unfold GroundTheory.Heights₂.Heights.HermitianBundle.rank
    simp
  obtain ⟨-, hdeg⟩ := CoverDenseAlt.deg_eq E ⊥ (s := (Fin.elim0 : Fin 0 → E.carrier)) linearIndependent_empty_type
    (fun i => i.elim0) hrk
  have h1 : CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range (Fin.elim0 : Fin 0 → E.carrier))) ⊥ = 1 := by
    rw [CoverDenseAlt.idx_eq_card]
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨0⟩⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Subsingleton.elim a b]
  have hg : ∀ σ : K →+* ℂ, GroundTheory.Heights₂.Heights.gramDet E.metric σ (Fin.elim0 : Fin 0 → E.carrier) = 1 := by
    intro σ
    unfold GroundTheory.Heights₂.Heights.gramDet
    rw [Matrix.det_isEmpty, Complex.one_re]
  rw [hdeg, h1]
  simp only [hg, Real.log_one, Nat.cast_one, Finset.sum_const_zero, mul_zero, sub_zero]

theorem orth_biSup (E : HermitianBundle.{0} K) {F : Submodule (𝓞 K) E.carrier} {I : Type}
    (G : I → Submodule (𝓞 K) E.carrier) (S : Finset I) (h : ∀ b ∈ S, OrthAt E F (G b)) :
    OrthAt E F (⨆ b ∈ S, G b) := by
  classical
  intro σ x hx y hy
  obtain ⟨μ, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum G y).mp hy
  rw [← FibreSpace.inner_equiv E.metric σ]
  have hfv : fibreVec E.metric σ (∑ b ∈ S, (μ b : E.carrier)) = ∑ b ∈ S, fibreVec E.metric σ (μ b) := by
    simpa using fibreVec_sum E.metric σ S (fun _ => 1) (fun b => (μ b : E.carrier))
  change inner ℂ (fibreVec E.metric σ x) (fibreVec E.metric σ (∑ b ∈ S, (μ b : E.carrier))) = 0
  rw [hfv, inner_sum]
  refine Finset.sum_eq_zero fun b hb => ?_
  have h1 := h b hb σ x hx _ (μ b).2
  rw [← FibreSpace.inner_equiv E.metric σ] at h1
  exact h1

theorem degree_rank_biSup (E : HermitianBundle.{0} K) {I : Type}
    (F : I → Submodule (𝓞 K) E.carrier) (h : ∀ a b, a ≠ b → OrthAt E (F a) (F b)) (S : Finset I) :
    E.degree (⨆ a ∈ S, F a) = ∑ a ∈ S, E.degree (F a) ∧
      E.rank (⨆ a ∈ S, F a) = ∑ a ∈ S, E.rank (F a) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · have hb : (⨆ a ∈ (∅ : Finset I), F a) = ⊥ := by simp
    rw [hb, Finset.sum_empty, Finset.sum_empty]
    refine ⟨degree_bot E, ?_⟩
    unfold GroundTheory.Heights₂.Heights.HermitianBundle.rank
    simp
  · intro a S ha ih
    rw [Finset.iSup_insert, Finset.sum_insert ha, Finset.sum_insert ha]
    have horth : OrthAt E (F a) (⨆ b ∈ S, F b) :=
      orth_biSup E F S fun b hb => h a b fun hab => ha (hab ▸ hb)
    refine ⟨?_, ?_⟩
    · rw [degree_sup E horth, ih.1]
    · rw [CoverDenseAlt.rank_sup E (disjoint_of_orth E horth), ih.2]

theorem normDegree_rank_iSup : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (I : Type) [Fintype I] (F : I → Submodule (𝓞 K) E.carrier), (∀ a b, a ≠ b → OrthAt E (F a) (F b)) → E.normDegree (⨆ a, F a) = ∑ a, E.normDegree (F a) ∧ E.rank (⨆ a, F a) = ∑ a, E.rank (F a) := by
  intro K _ _ E I _ F h
  have hU : (⨆ a, F a) = ⨆ a ∈ (Finset.univ : Finset I), F a := by simp
  obtain ⟨hd, hr⟩ := degree_rank_biSup E F h Finset.univ
  rw [hU]
  refine ⟨?_, hr⟩
  unfold GroundTheory.Heights₂.Heights.HermitianBundle.normDegree
  rw [hd, Finset.sum_div]

end GlobalTheory.CompanionTheory.Ar.OrthSum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.nef_on_fibres_add_nonneg : PB.Inputs → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (a a' : K → ℤ) (p q : ℕ), NefOnFibres P a → (∀ k, 0 ≤ a' k) → NefOnFibres P ((q : ℤ) • a + (p : ℤ) • a') := by
  first | exact @LevelTowerAlt.nef_fibres_combination | exact LevelTowerAlt.nef_fibres_combination
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.realisation_pullback_compatible : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k', ι' k') → Ω) (S' : AnSys D σ) (Re' : Realis S' (mCoordIdeal y)) (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')), IsBlockMap κ v → imageZ v (mCoordIdeal y) = P → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a, IsPullHerm κ v (Re.line a t) (Re'.line a t)) → Re'.deg = IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * Re.deg → Re'.PB II = Re.PB II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.pb_indep_cover | exact GlobalTheory.CompanionTheory.Ar.PB.pb_indep_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.pb_indep_cover <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.weight_transform_injective_linear : (∀ (D : ℕ) (κ : ℕ → ℝ) (v : ℝ) (Q : Polynomial ℝ), tsgPoly D κ (Polynomial.C v * Q) = Polynomial.C v * tsgPoly D κ Q) ∧ (∀ (σ : Type) (c : σ → ℝ) (e : σ → ℤ) (v : ℝ) (Q : MvPolynomial σ ℝ), linePoly c e (C v * Q) = Polynomial.C v * linePoly c e Q) ∧ ∀ (Ψ : Type) (N : ℕ), Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective | exact GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

theorem _root_.GlobalTheory.T.word_coefficient_second_derivative : ∀ (d k i : ℕ), i < k → 2 * k ≤ d + 2 → ∀ n₀ n₁ : Fin 3 → ℝ,
    evalW n₀ n₁ (pderiv (some 1) (pderiv (some 0) (∏ r : Fin (d + 2),
      rowW (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0)
        (if (r : ℕ) < 2 * k then 0 else 1)))) =
    rename some (aeval ![lin3 n₀, lin3 n₁]
      (pderiv 0 (pderiv 1 (wwLinProd k (DiagonalFibreFubini.wordCoef i))))) * X none ^ (d + 2 - 2 * k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.WordProd.evalW_pderiv_prod_rows_word | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.WordProd.evalW_pderiv_prod_rows_word | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.WordProd.evalW_pderiv_prod_rows_word <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.minimal_primes_of_multihomog_sup : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)), IsMultiHomogIdeal P → IsMultiHomogIdeal D → ∀ Q ∈ (P ⊔ D).minimalPrimes, IsMultiHomogIdeal Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup | exact GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup <;> assumption)
end
