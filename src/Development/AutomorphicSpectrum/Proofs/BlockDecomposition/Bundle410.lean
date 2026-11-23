module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReflectionRootDiagonalConj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantElementsGlValued
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle104
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle397
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle396
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Matrix.Normed
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub

@[expose] public section

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

theorem _root_.GlobalTheory.T.reflection_root_diagonal_conj : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2)), i.val = a → j.val = a + 1 → ∀ t : GU σ n, PositivityTheory.SphericalProduct.IsDiagM (t : GL (Fin n) L) →
    ∃ c : L, c ≠ 0 ∧ ∃ t' : GU σ n, IsBorelU t' ∧
      (∀ x : L, sR σ hU.1 a h * uR σ hU.1 a h x * t = t' * (sR σ hU.1 a h * uR σ hU.1 a h (c * x))) ∧
      chiDeltaU q (fun k => (χ k : ℂ)) t' * (q : ℂ) ^ (2 * ordL c) =
        chiDeltaU q (fun k => ((χ ∘ Equiv.swap i j) k : ℂ)) t := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.Torus.torus_step | exact GlobalTheory.CompanionTheory.SwapRoot.Torus.torus_step | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.Torus.torus_step <;> assumption)
end

section

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

variable {n : ℕ}

theorem locallyCompact_GL (n : ℕ) : LocallyCompactSpace (GL (Fin n) ℂ) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountable_GL (n : ℕ) : SecondCountableTopology (GL (Fin n) ℂ) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem isClosed_nilrad (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    IsClosed (nilrad W₁ W₂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  haveI : FiniteDimensional ℂ (Matrix (Fin n) (Fin n) ℂ) := inferInstance
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  exact Submodule.closed_of_finiteDimensional (nilrad W₁ W₂)

theorem nil_mul_mem {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ nilrad W₁ W₂) (hY : Y ∈ nilrad W₁ W₂) :
    X * Y ∈ nilrad W₁ W₂ := by
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [← Matrix.mulVec_mulVec]; exact hW (hX.2.1 _ (hY.1 y))
  · rw [← Matrix.mulVec_mulVec, hX.2.2 _ (hY.2.1 y hy)]; exact W₁.zero_mem
  · rw [← Matrix.mulVec_mulVec, hY.2.2 y hy, Matrix.mulVec_zero]

def nmul {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) (Y X : nilrad W₁ W₂) : nilrad W₁ W₂ :=
  ⟨Y.1 + X.1 + Y.1 * X.1, (nilrad W₁ W₂).add_mem ((nilrad W₁ W₂).add_mem Y.2 X.2) (nil_mul_mem hW Y.2 X.2)⟩

theorem isClosed_twCent (d : GL (Fin n) ℂ) :
    IsClosed (twCent (thC n) d : Set (GL (Fin n) ℂ)) := by
  have h : Continuous fun g : GL (Fin n) ℂ => g⁻¹ * d * thC n g :=
    (continuous_inv.mul continuous_const).mul continuous_thC
  exact isClosed_eq h continuous_const

theorem locallyCompact_twCent (d : GL (Fin n) ℂ) : LocallyCompactSpace (twCent (thC n) d) := by
  haveI := locallyCompact_GL n
  exact (isClosed_twCent d).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem sigmaFinite_twCent [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (d : GL (Fin n) ℂ) (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] : SigmaFinite μd := by
  haveI := locallyCompact_twCent d
  haveI := secondCountable_GL n
  haveI : SecondCountableTopology (twCent (thC n) d) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  infer_instance

theorem invInvariant_twCent [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (d : GL (Fin n) ℂ) (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure]
    (hc : ∀ a ∈ twCent (thC n) d, ∀ b ∈ twCent (thC n) d, a * b = b * a) : μd.IsInvInvariant := by
  haveI := locallyCompact_twCent d
  haveI := secondCountable_GL n
  letI : CommGroup (twCent (thC n) d) :=
    { (inferInstance : Group (twCent (thC n) d)) with
      mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }
  haveI : SecondCountableTopology (twCent (thC n) d) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular μd

end GlobalTheory.CompanionTheory.LocVan
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.DomGLVal
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.DomUnitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {σ : L →+* L}
variable (D : CassData (GU σ n))

theorem mem_J_iff (hJ : D.J = IwU σ n) (x : GU σ n) : x ∈ D.J ↔ (x : GL (Fin n) L) ∈ IwGL L n := by
  rw [hJ, IwU, Subgroup.mem_subgroupOf]

theorem upper_facts (hJ : D.J = IwU σ n) (hN : ∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L))
    {x : GU σ n} (hx : x ∈ D.J ⊓ D.N) :
    IsUniM (x : GL (Fin n) L) ∧ IsUniM (x : GL (Fin n) L)⁻¹ ∧ Integ (x : GL (Fin n) L) ∧
      Integ (x : GL (Fin n) L)⁻¹ := by
  have h := (mem_IwGL_iff _).1 ((mem_J_iff D hJ x).1 hx.1)
  exact ⟨(hN _).1 hx.2, (hN _).1 (inv_mem hx.2), h.1, h.2⟩

theorem lower_facts (hJ : D.J = IwU σ n) (hNm : ∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L))
    {x : GU σ n} (hx : x ∈ D.J ⊓ D.Nm) :
    IsLowUniM (x : GL (Fin n) L) ∧ IsLowUniM (x : GL (Fin n) L)⁻¹ ∧ Integ (x : GL (Fin n) L) ∧
      Integ (x : GL (Fin n) L)⁻¹ := by
  have h := (mem_IwGL_iff _).1 ((mem_J_iff D hJ x).1 hx.1)
  exact ⟨(hNm _).1 hx.2, (hNm _).1 (inv_mem hx.2), h.1, h.2⟩

theorem dom_core (hJ : D.J = IwU σ n) (hN : ∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L))
    (hNm : ∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L))
    (hT : ∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L)) (τ : GU σ n) (hτ : τ ∈ D.T)
    (hmono : ∀ i j : Fin n, i ≤ j → ordL (((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) ≤
      ordL (((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)) :
    (∀ x ∈ D.J ⊓ D.N, τ * x * τ⁻¹ ∈ D.J ⊓ D.N) ∧ (∀ x ∈ D.J ⊓ D.Nm, τ⁻¹ * x * τ ∈ D.J ⊓ D.Nm) ∧
      ∀ x ∈ D.J ⊓ D.T, τ * x * τ⁻¹ ∈ D.J ⊓ D.T ∧ τ⁻¹ * x * τ ∈ D.J ⊓ D.T := by
  obtain ⟨d, hd, hne, hdd⟩ : ∃ d : Fin n → L, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d ∧
      (∀ i, d i ≠ 0) ∧ ∀ i, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = d i :=
    ⟨_, (diag_data ((hT _).1 hτ)).1, (diag_data ((hT _).1 hτ)).2, fun _ => rfl⟩
  have hmono' : ∀ i j, i ≤ j → ordL (d j) ≤ ordL (d i) := by simpa only [hdd] using hmono
  have hle : ∀ i j, i ≤ j → Valued.v (d i) * Valued.v (d j)⁻¹ ≤ 1 := fun i j hij =>
    ratio_le (hne j) (v_le_of_ordL_le (hne j) (hne i) (hmono' i j hij))
  have hle' : ∀ i j, j ≤ i → Valued.v (d i)⁻¹ * Valued.v ((d j)⁻¹)⁻¹ ≤ 1 := fun i j hij => by
    rw [inv_inv, mul_comm]
    exact hle j i hij
  have hs' := val_inv_diag hne hd
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨u1, u2, i1, i2⟩ := upper_facts D hJ hN hx
    have := up_mem hne hd u1 u2 (fun i j hij => valuation_triple_mul_le (hle i j hij.le) (i1.1 i j))
      (fun i j hij => valuation_triple_mul_le (hle i j hij.le) (i2.1 i j))
    exact ⟨(mem_J_iff D hJ _).2 this.1, (hN _).2 this.2⟩
  · obtain ⟨l1, l2, i1, i2⟩ := lower_facts D hJ hNm hx
    have := low_mem (fun i => inv_ne_zero (hne i)) hs' l1 l2
      (fun i j hij => valuation_triple_mul_lt_one (hle' i j hij.le) (i1.2 i j hij))
      (fun i j hij => valuation_triple_mul_lt_one (hle' i j hij.le) (i2.2 i j hij))
    rw [inv_inv] at this
    exact ⟨(mem_J_iff D hJ _).2 this.1, (hNm _).2 this.2⟩
  · obtain ⟨hdx, -⟩ := diag_data ((hT _).1 hx.2)
    have hc : τ * x = x * τ := by
      apply Subtype.ext
      apply Units.ext
      show ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        ((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
      rw [hd, hdx, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    have e1 : τ * x * τ⁻¹ = x := by rw [hc, mul_inv_cancel_right]
    have e2 : τ⁻¹ * x * τ = x := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    rw [e1, e2]
    exact ⟨hx, hx⟩

theorem strict_core (hJ : D.J = IwU σ n) (hN : ∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L))
    (hNm : ∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L))
    (hT : ∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L)) (τ : GU σ n) (hτ : τ ∈ D.T)
    (hst : IsStrictDom (τ : GL (Fin n) L)) :
    (∀ x ∈ D.N, ∃ j : ℕ, τ ^ j * x * (τ ^ j)⁻¹ ∈ D.J ⊓ D.N) ∧
      ∀ U : Set (GU σ n), IsOpen U → (1 : GU σ n) ∈ U →
        ∃ j : ℕ, ∀ x ∈ D.J ⊓ D.Nm, (τ ^ j)⁻¹ * x * τ ^ j ∈ U := by
  obtain ⟨d, hd, hne, hdd⟩ : ∃ d : Fin n → L, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d ∧
      (∀ i, d i ≠ 0) ∧ ∀ i, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = d i :=
    ⟨_, (diag_data ((hT _).1 hτ)).1, (diag_data ((hT _).1 hτ)).2, fun _ => rfl⟩
  have hst' : ∀ i j, i < j → ordL (d j) < ordL (d i) := by
    intro i j hij
    have := hst i j hij
    rwa [hdd, hdd] at this
  have hr : ∀ i j, i < j → ∀ m : ℕ, Valued.v (d i ^ m) * Valued.v (d j ^ m)⁻¹ ≤ cc ^ m := fun i j hij m =>
    ratio_pow_le (hne j) (v_le_of_ordL_lt (hne j) (hne i) (hst' i j hij)) m
  have hpow : ∀ m : ℕ, (((τ ^ m : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => d i ^ m) := fun m => by
    rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, hd, Matrix.diagonal_pow]
    rfl
  have hnep : ∀ m : ℕ, ∀ i, d i ^ m ≠ 0 := fun m i => pow_ne_zero _ (hne i)
  refine ⟨fun x hx => ?_, fun U hU h1 => ?_⟩
  · have u1 : IsUniM (x : GL (Fin n) L) := (hN _).1 hx
    have u2 : IsUniM (x : GL (Fin n) L)⁻¹ := (hN _).1 (inv_mem hx)
    choose f hf using fun p : Fin n × Fin n =>
      exists_pow_mul_le (Valued.v (((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.1 p.2))
    choose f' hf' using fun p : Fin n × Fin n =>
      exists_pow_mul_le (Valued.v ((((x : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.1 p.2))
    have hM : ∀ p, f p ≤ Finset.univ.sup f ⊔ Finset.univ.sup f' := fun p =>
      le_sup_of_le_left (Finset.le_sup (Finset.mem_univ p))
    have hM' : ∀ p, f' p ≤ Finset.univ.sup f ⊔ Finset.univ.sup f' := fun p =>
      le_sup_of_le_right (Finset.le_sup (Finset.mem_univ p))
    generalize Finset.univ.sup f ⊔ Finset.univ.sup f' = M at hM hM'
    have key : ∀ (y : L) (i j : Fin n), i < j → cc ^ M * Valued.v y ≤ 1 →
        Valued.v (d i ^ M * y * (d j ^ M)⁻¹) ≤ 1 := by
      intro y i j hij hy
      rw [map_mul, map_mul, mul_right_comm]
      have h2 := hr i j hij M
      calc Valued.v (d i ^ M) * Valued.v (d j ^ M)⁻¹ * Valued.v y ≤ cc ^ M * Valued.v y := by gcongr
        _ ≤ 1 := hy
    have := up_mem (hnep M) (hpow M) u1 u2
      (fun i j hij => key _ i j hij (hf (i, j) M (hM _)))
      (fun i j hij => key _ i j hij (hf' (i, j) M (hM' _)))
    exact ⟨M, (mem_J_iff D hJ _).2 this.1, (hN _).2 this.2⟩
  · obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hU
    obtain ⟨m, hm⟩ := open_shrink W hW h1
    refine ⟨m, fun x hx => ?_⟩
    obtain ⟨l1, l2, i1, i2⟩ := lower_facts D hJ hNm hx
    have hs := val_inv_diag (hnep m) (hpow m)
    have hes : ∀ i, (d i ^ m)⁻¹ ≠ 0 := fun i => inv_ne_zero (hnep m i)
    have hb : ∀ a b, b < a → Valued.v (d a ^ m)⁻¹ * Valued.v ((d b ^ m)⁻¹)⁻¹ ≤ cc ^ m := fun a b hab => by
      rw [inv_inv, mul_comm]
      exact hr b a hab m
    have c1 := low_close hes hs l1 (B := cc ^ m) (fun a b hab => valuation_triple_mul_le (hb a b hab) (i1.1 a b))
    have c2 := low_close hes hs l2 (B := cc ^ m) (fun a b hab => valuation_triple_mul_le (hb a b hab) (i2.1 a b))
    have := hm _ c1 (by rw [GlobalTheory.CompanionTheory.DomGLVal.conj_inv]; exact c2)
    rw [inv_inv] at this
    exact this

theorem domU : PositivityTheory.SphericalProduct.DomU := by
  intro L _ _ _ ϖ σ q _ n D hJ hN hNm hT t
  refine ⟨fun h => dom_core D hJ hN hNm hT t t.2 h, fun h => ⟨?_, strict_core D hJ hN hNm hT t t.2 h⟩⟩
  exact dom_core D hJ hN hNm hT t t.2 fun i j hij => by
    rcases hij.lt_or_eq with hij | rfl
    · exact (h i j hij).le
    · exact le_rfl

end GlobalTheory.CompanionTheory.DomUnitary
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

section Lim

variable {T : Type} [CommRing T] (ϖ : T)

def Tends (x : ℕ → T) (L : T) : Prop := ∀ k, ∃ M, ∀ m, M ≤ m → x m - L ∈ Ideal.span {ϖ ^ k}

variable {ϖ}

theorem smodEq_iff {a b : T} {k : ℕ} :
    a ≡ b [SMOD ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule T T)] ↔ a - b ∈ Ideal.span {ϖ ^ k} := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]

theorem Tends.unique [IsHausdorff (Ideal.span {ϖ}) T] {x : ℕ → T} {L L' : T} (h : Tends ϖ x L)
    (h' : Tends ϖ x L') : L = L' := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ϖ}) T) _ fun k => ?_
  have h0 : L - L' ∈ Ideal.span {ϖ ^ k} := by
    obtain ⟨M, hM⟩ := h k
    obtain ⟨M', hM'⟩ := h' k
    have := sub_mem (hM' (max M M') (le_max_right _ _)) (hM (max M M') (le_max_left _ _))
    simpa using this
  have : L - L' ≡ 0 [SMOD ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule T T)] :=
    smodEq_iff.2 (by simpa using h0)
  exact this

theorem exists_tends [IsAdicComplete (Ideal.span {ϖ}) T] (x : ℕ → T)
    (h : ∀ k, ∃ M, ∀ m, M ≤ m → x m - x M ∈ Ideal.span {ϖ ^ k}) : ∃ L, Tends ϖ x L := by
  choose M hM using h
  let N : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup M
  have hN : ∀ k, M k ≤ N k := fun k => Finset.le_sup (Finset.self_mem_range_succ k)
  have hmono : Monotone N := fun a b hab =>
    Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ hab))
  have hc : ∀ k m, N k ≤ m → x m - x (N k) ∈ Ideal.span {ϖ ^ k} := fun k m hm => by
    have := sub_mem (hM k m ((hN k).trans hm)) (hM k (N k) (hN k))
    simpa using this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {ϖ}) T)
    (f := fun k => x (N k)) (fun {a b} hab => smodEq_iff.2 (by
      have := hc a (N b) (hmono hab)
      rw [← neg_sub]
      exact neg_mem this))
  refine ⟨L, fun k => ⟨N k, fun m hm => ?_⟩⟩
  have := add_mem (hc k m hm) (smodEq_iff.1 (hL k))
  simpa using this

theorem Tends.add {x y : ℕ → T} {a b : T} (hx : Tends ϖ x a) (hy : Tends ϖ y b) :
    Tends ϖ (fun m => x m + y m) (a + b) := fun k => by
  obtain ⟨M, hM⟩ := hx k
  obtain ⟨M', hM'⟩ := hy k
  refine ⟨max M M', fun m hm => ?_⟩
  have := add_mem (hM m ((le_max_left _ _).trans hm)) (hM' m ((le_max_right _ _).trans hm))
  convert this using 1; ring

theorem Tends.mul {x y : ℕ → T} {a b : T} (hx : Tends ϖ x a) (hy : Tends ϖ y b) :
    Tends ϖ (fun m => x m * y m) (a * b) := fun k => by
  obtain ⟨M, hM⟩ := hx k
  obtain ⟨M', hM'⟩ := hy k
  refine ⟨max M M', fun m hm => ?_⟩
  have := add_mem (Ideal.mul_mem_right (y m) _ (hM m ((le_max_left _ _).trans hm)))
    (Ideal.mul_mem_left _ a (hM' m ((le_max_right _ _).trans hm)))
  convert this using 1; ring

theorem tends_const (a : T) : Tends ϖ (fun _ => a) a := fun k => ⟨0, fun _ _ => by simp⟩

theorem exists_lim_hom {S : Type} [CommRing S] [IsAdicComplete (Ideal.span {ϖ}) T] (a : ℕ → S →+* T)
    (h : ∀ f k, ∃ M, ∀ m, M ≤ m → a m f - a M f ∈ Ideal.span {ϖ ^ k}) :
    ∃ ψ : S →+* T, ∀ f, Tends ϖ (fun m => a m f) (ψ f) := by
  choose L hL using fun f => exists_tends (ϖ := ϖ) (fun m => a m f) (h f)
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hL⟩
  · exact (hL 1).unique (by simpa using tends_const (ϖ := ϖ) (1 : T))
  · intro f g
    exact (hL (f * g)).unique (by simpa using (hL f).mul (hL g))
  · exact (hL 0).unique (by simpa using tends_const (ϖ := ϖ) (0 : T))
  · intro f g
    exact (hL (f + g)).unique (by simpa using (hL f).add (hL g))

end Lim

variable {l : ℕ} [Fact l.Prime]

theorem exists_period (A : PAlg l) (f : (A.cont ℤ_[l]).A) (k : ℕ) :
    ∃ M : ℕ, ∀ z z' : ℤ_[l], PadicInt.toZModPow M z = PadicInt.toZModPow M z' →
      Hom.f (A.evCont z) f - Hom.f (A.evCont z') f ∈ Ideal.span {A.pi ^ k} := by
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.PadicShift.exists_period l _ (f.2 k)
  refine ⟨M, fun z z' h => Ideal.Quotient.eq.1 (hM z z' ?_)⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h, sub_self]

end GlobalTheory.CompanionTheory.ContUniv
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.ClozelPurity

theorem EopV_val (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (τ : E →+* ℂ) (i j : Fin a) (φ : π.V) : (EopV π τ i j φ).1 = Eop τ i j φ.1 := by
  simp [EopV, Eop, lieS_apply, CuspSub.op_val, act]

end GlobalTheory.CompanionTheory.ClozelPurity

end
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.centred_segment_square_integrable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zls.CasselmanSuffSq k → GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → Zz.CentredSegSqInt k := by
  first | exact @GlobalTheory.CompanionTheory.SegLink.centredSegSqInt | exact GlobalTheory.CompanionTheory.SegLink.centredSegSqInt | (intros; apply GlobalTheory.CompanionTheory.SegLink.centredSegSqInt <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.local_langlands_of_irreducible_admissible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k := by
  first | exact @GlobalTheory.CompanionTheory.GKLocalProof.gkLocal | exact GlobalTheory.CompanionTheory.GKLocalProof.gkLocal | (intros; apply GlobalTheory.CompanionTheory.GKLocalProof.gkLocal <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.ChainSum

theorem sdot_measurable {m : ℕ} (e : Fin m → SignType) : Measurable (sdot e) := by
  unfold sdot
  exact Finset.measurable_fun_sum _ fun i _ => (measurable_pi_apply i).const_mul _

theorem sdot_add' {m : ℕ} (e : Fin m → SignType) (a b : Fin m → ℝ) :
    sdot e (a + b) = sdot e a + sdot e b := by
  simp [sdot, mul_add, Finset.sum_add_distrib]

theorem chainSum_rest : ∀ m : ℕ, (∀ y : (Fin m → SignType) → ℝ, Measurable (gam y)) ∧
    (∀ (y : (Fin m → SignType) → ℝ) a b, gam (fun e => y e + sdot e b) (a + b) = gam y a) ∧
    ∀ (y y' : (Fin m → SignType) → ℝ) e s t a, (∀ e', SLe e e' ∨ SLe e' e → y e' = y' e') →
      gam (Function.update y e s) a - gam (Function.update y e t) a =
        gam (Function.update y' e s) a - gam (Function.update y' e t) a := by
  intro m
  refine ⟨fun y => ?_, fun y a b => ?_, fun y y' e s t a h => ?_⟩
  · unfold gam gamOn
    refine Finset.measurable_fun_sum _ fun c _ => ?_
    refine Measurable.const_mul (Finset.measurable_fun_prod _ fun e _ => ?_) _
    exact Measurable.ite (measurableSet_lt measurable_const (sdot_measurable e))
      measurable_const measurable_const
  · unfold gam gamOn
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun e _ => ?_
    have hiff : (y e + sdot e b < sdot e (a + b)) ↔ y e < sdot e a := by
      rw [sdot_add']
      exact add_lt_add_iff_right _
    exact if_congr hiff rfl rfl
  · unfold gam gamOn
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hchain : IsChain SLe (↑c : Set (Fin m → SignType)) := by
      simp only [Finset.mem_filter] at hc
      exact hc.2.2.1
    by_cases hec : e ∈ c
    · have key : ∀ u : ℝ, (∏ e' ∈ c, if Function.update y e u e' < sdot e' a then (1 : ℝ) else 0) =
          ∏ e' ∈ c, if Function.update y' e u e' < sdot e' a then (1 : ℝ) else 0 := by
        intro u
        refine Finset.prod_congr rfl fun e' he' => ?_
        by_cases hne : e' = e
        · subst hne
          simp only [Function.update_self]
        · have hcmp : SLe e e' ∨ SLe e' e :=
            hchain (Finset.mem_coe.2 hec) (Finset.mem_coe.2 he') (Ne.symm hne)
          simp only [Function.update_of_ne hne, h e' hcmp]
      rw [key s, key t]
    · have key : ∀ (z : (Fin m → SignType) → ℝ) (u v : ℝ),
          (∏ e' ∈ c, if Function.update z e u e' < sdot e' a then (1 : ℝ) else 0) =
            ∏ e' ∈ c, if Function.update z e v e' < sdot e' a then (1 : ℝ) else 0 := by
        intro z u v
        refine Finset.prod_congr rfl fun e' he' => ?_
        have hne : e' ≠ e := fun hh => hec (hh ▸ he')
        simp only [Function.update_of_ne hne]
      rw [key y s t, key y' s t, sub_self, sub_self]

end GlobalTheory.CompanionTheory.ChainSum
end
