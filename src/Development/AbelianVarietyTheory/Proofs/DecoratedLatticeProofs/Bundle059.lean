module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyConstantSupportInvarianceOfDenseRational
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle027
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle056
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.HermitianLattices.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.OpenPr

theorem continuous_embX {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {A : Type} [Fintype A] [DecidableEq A] (c : ℕ) :
    Continuous (embX c : GL A k → GL (A ⊕ Fin c) k) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GL A k => (fromBlocks (x : Matrix A A k) 0 0 1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k)
    exact (Units.continuous_val).matrix_fromBlocks continuous_const continuous_const continuous_const
  · change Continuous fun x : GL A k => (fromBlocks ((x⁻¹ : GL A k) : Matrix A A k) 0 0 1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k)
    exact (Units.continuous_coe_inv).matrix_fromBlocks continuous_const continuous_const continuous_const

theorem isOpen_prX : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A] {c : ℕ} (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (1 : GL (A ⊕ Fin c) k) ∈ O → (∀ z ∈ R k A c 1, z ∈ O → z ∈ Ck) → IsOpen (prX Ck : Set (GL A k)) := by
  intro k _ _ _ _ A _ _ c Ck O hO h1 hCk
  have hc : Continuous (embX c : GL A k → GL (A ⊕ Fin c) k) := continuous_embX c
  have hU : IsOpen ((embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O) := hO.preimage hc
  have h1U : (1 : GL A k) ∈ (embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O := by
    simp only [Set.mem_preimage, map_one]; exact h1
  have hsub : (embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O ⊆ (prX Ck : Set (GL A k)) := by
    intro x hx
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul]
    exact hCk _ (Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨x, rfl⟩)) hx
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU.mem_nhds h1U) hsub)

end GlobalTheory.OpenPr
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.locallyConstant_support_invariance_of_dense_rational : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (E : Type) [Field E] (ι : E →+* k), DenseRange ι →
  ∀ (A B : Type) [Fintype A] [Fintype B] (f : Matrix A B k → (A → k) → ℂ), IsLocallyConstant (fun p : Matrix A B k × (A → k) => f p.1 p.2) →
  ∀ (c : kˣ), (∀ (x : Matrix A B E) (y : A → E), f (x.map ι) (fun a => ι (y a)) ≠ 0 → (fun a => ι (y a)) ∈ box A c⁻¹) →
    (∀ (x : Matrix A B E) (y z : A → E), (fun a => ι (z a)) ∈ box A c → f (x.map ι) (fun a => ι (y a + z a)) = f (x.map ι) (fun a => ι (y a))) →
    ∀ x y, (f x y ≠ 0 → y ∈ box A c⁻¹) ∧ ∀ z ∈ box A c, f x (y + z) = f x y := by
  first | exact @GlobalTheory.DenseBox.support_invariance_of_dense | exact GlobalTheory.DenseBox.support_invariance_of_dense | (intros; apply GlobalTheory.DenseBox.support_invariance_of_dense <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.UnipLevelTopo

theorem isOpen_inf_isCompact : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A] {c : ℕ} (J : Subgroup (GL (A ⊕ Fin c) k)) (g : GL (A ⊕ Fin c) k), IsOpen (J : Set (GL (A ⊕ Fin c) k)) → IsCompact (J : Set (GL (A ⊕ Fin c) k)) → IsOpen ((((Cgrp J g).subgroupOf (N k A c 1)) ⊓ ((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1)) : Subgroup (N k A c 1)) : Set (N k A c 1)) ∧ IsCompact (((Cgrp J g).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) ∧ IsCompact (((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) := by
  intro k _ _ _ _ A _ _ c J g hJo hJc
  obtain ⟨h1, h2⟩ := isOpen_isCompact_conj g hJo hJc
  have hemb : Topology.IsClosedEmbedding (Subtype.val : N k A c 1 → GL (A ⊕ Fin c) k) :=
    (GlobalTheory.RootEx.VolN.isClosed_N (k := k) (n := A) (c := c) 1).isClosedEmbedding_subtypeVal
  have eC : (((Cgrp J g).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) =
      Subtype.val ⁻¹' (J.comap (MulAut.conj g⁻¹).toMonoidHom : Set (GL (A ⊕ Fin c) k)) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage, Cgrp, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨Subgroup.mem_sup_right x.2, h⟩⟩
  have eK : (((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) =
      Subtype.val ⁻¹' (KO k (A ⊕ Fin c) : Set (GL (A ⊕ Fin c) k)) := by
    ext x; simp [Subgroup.mem_subgroupOf]
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf, eC, eK]
    exact (h1.inter GlobalTheory.SplitFlip.isOpen_KO).preimage continuous_subtype_val
  · rw [eC]; exact hemb.isCompact_preimage h2
  · rw [eK]; exact hemb.isCompact_preimage GlobalTheory.SplitFlip.isCompact_KO

end GlobalTheory.UnipLevelTopo
end

section

namespace GlobalTheory.FullLatticeOfSpan

open NumberField

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V]
    [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (N : Submodule (𝓞 E) V) {x : V}
    (hx : x ∈ Submodule.span E (N : Set V)) : ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ hay
    · rw [mul_smul]; exact N.smul_mem _ hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hsE : algebraMap (𝓞 E) E s ≠ 0 := by
      intro h
      exact hs0 (IsFractionRing.injective (𝓞 E) E (by rw [h, map_zero]))
    refine ⟨a * s, mul_ne_zero ha hs0, ?_⟩
    have : (a * s) • ((algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s) • y) = r • (a • y) := by
      rw [← algebraMap_smul E (a * s), ← algebraMap_smul E r, ← algebraMap_smul E a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact N.smul_mem _ hay

theorem exists_nat_dvd {E : Type} [Field E] [NumberField E] (d : 𝓞 E) (hd : d ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ d ∣ (m : 𝓞 E) := by
  refine ⟨Ideal.absNorm (Ideal.span {d}), ?_, ?_⟩
  · apply Nat.pos_of_ne_zero
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd
  · exact Ideal.mem_span_singleton.mp (Ideal.absNorm_mem _)

theorem full_of_span_eq_top : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (N : Submodule (NumberField.RingOfIntegers E) (Formalism.L2.Col.Sp E n)),
    Submodule.span E (↑N : Set (Formalism.L2.Col.Sp E n)) = ⊤ → GlobalTheory.ThetaMove.Full N := by
  intro E _ _ n N hN x
  obtain ⟨d, hd, hdx⟩ := exists_smul_mem N (x := x) (by rw [hN]; trivial)
  obtain ⟨m, hm, c, hc⟩ := exists_nat_dvd d hd
  refine ⟨m, hm, ?_⟩
  rw [hc, mul_comm, mul_smul]
  exact N.smul_mem _ hdx

end GlobalTheory.FullLatticeOfSpan
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

noncomputable section

namespace GlobalTheory.CoeffEab

variable {p q n : ℕ}

open scoped Matrix.Norms.Operator in
theorem reindex_exp (e : Ix p q ≃ Fin n) (A : Mat p q) :
    Matrix.reindex e e (NormedSpace.exp A) = NormedSpace.exp (Matrix.reindex e e A) := by
  exact NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (continuous_id.matrix_reindex e e) A

theorem mem_upq_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (Y : Mat p q) :
    Y ∈ upq p q ↔ Formalism.REAL.inG ε (Matrix.reindex e e Y) := by
  unfold Formalism.REAL.inG
  rw [← h.reindex_Jm, Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  have := (Matrix.reindex e e).injective.eq_iff (a := Yᴴ * Jm p q + Jm p q * Y) (b := 0)
  exact this.symm

theorem Jm_herm (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

theorem inG_of_J {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε = -X) : Formalism.REAL.inG ε X := by
  unfold Formalism.REAL.inG
  have : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := by
    calc Xᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) := by
          rw [← mul_assoc, ← mul_assoc, Formalism.REAL.Jm_mul_self, one_mul]
      _ = -(Formalism.REAL.Jm ε * X) := by rw [h, mul_neg]
  rw [this, neg_add_cancel]

theorem inG_cpart1 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inG ε (Formalism.REAL.cpart1 ε Z) := by
  apply inG_of_J
  unfold Formalism.REAL.cpart1
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Jm_herm,
    conjTranspose_conjTranspose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_assoc]
  rw [← mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), Formalism.REAL.Jm_mul_self, one_mul, mul_one]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_neg, neg_sub]

theorem inG_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inG ε (Formalism.REAL.cpart2 ε Z) := by
  apply inG_of_J
  unfold Formalism.REAL.cpart2
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, Jm_herm,
    conjTranspose_conjTranspose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, mul_assoc]
  rw [← mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), Formalism.REAL.Jm_mul_self, one_mul, mul_one]
  have : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [show star (1 / (2 * Complex.I)) = (starRingEnd ℂ) (1 / (2 * Complex.I)) from rfl]
    simp only [map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat]
    rw [mul_neg, div_neg]
  rw [this, neg_smul, add_comm]

theorem cpart_sum (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.cpart1 ε Z + Complex.I • Formalism.REAL.cpart2 ε Z = Z := by
  unfold Formalism.REAL.cpart1 Formalism.REAL.cpart2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp]
  module

theorem Rd_coeff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} {T : GrpData p q} (R : DSRep T)
    {σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)} (h : BlockOrd e ε) (hF : Factors R.U e σ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inG ε X) (v : R.HK.V) (w : R.U.H)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    Formalism.REAL.Rd X (fun x => inner ℂ w (σ x (R.ι v))) g =
      inner ℂ w (σ g (R.ι (R.HK.act ((Matrix.reindex e e).symm X) v))) := by
  obtain ⟨Y, rfl⟩ := (Matrix.reindex e e).surjective X
  rw [Equiv.symm_apply_apply]
  have hY : Y ∈ upq p q := (mem_upq_iff h Y).2 hX
  obtain ⟨x, rfl⟩ := h.cov_surj T hg
  have hs : ∀ t : ℝ, t • Y ∈ upq p q := by
    intro t
    have h0 : Yᴴ * Jm p q + Jm p q * Y = 0 := hY
    show (t • Y)ᴴ * Jm p q + Jm p q * (t • Y) = 0
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h0, smul_zero]
  have key : ∀ t : ℝ, σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) *
      NormedSpace.exp ((t : ℂ) • Matrix.reindex e e Y)) = R.U.π x * R.U.π (T.expt (t • Y)) := by
    intro t
    rw [← map_mul, hF (x * _), map_mul, Units.val_mul, T.expt_cov _ (hs t)]
    congr 1
    have : (t : ℂ) • Matrix.reindex e e Y = Matrix.reindex e e (t • Y) := by
      ext i j; simp
    rw [this, ← reindex_exp]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  unfold Formalism.REAL.Rd
  simp only [key, ← hF x]
  have hd := R.der Y hY v
  have hl := (((innerSL ℂ w).comp (R.U.π x)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  exact hl.deriv

theorem eab_coeff : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ (a b : Ix p q) (v : R.HK.V) (w : R.U.H), ∀ g ∈ UJset ε, Formalism.REAL.Eab ε (e a) (e b) (fun x => inner ℂ w (σ x (R.ι v))) g = inner ℂ w (σ g (R.ι (R.HK.act (Eab a b) v))) := by
  intro p q n e ε T R σ h hF a b v w g hg
  unfold Formalism.REAL.Eab Formalism.REAL.Ec
  rw [Rd_coeff R h hF (inG_cpart1 ε _) v w hg, Rd_coeff R h hF (inG_cpart2 ε _) v w hg]
  have hE : Eab a b = (Matrix.reindex e e).symm (Formalism.REAL.cpart1 ε (Matrix.single (e a) (e b) 1)) +
      Complex.I • (Matrix.reindex e e).symm (Formalism.REAL.cpart2 ε (Matrix.single (e a) (e b) 1)) := by
    ext i j
    have := congrFun (congrFun (cpart_sum ε (Matrix.single (e a) (e b) (1 : ℂ))) (e i)) (e j)
    simp only [Matrix.add_apply, Matrix.smul_apply] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.reindex_symm, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_symm]
    rw [this]
    simp [Eab, Matrix.single_apply]
  rw [hE]
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, inner_add_right, inner_smul_right]

end GlobalTheory.CoeffEab

end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverExhaust

variable {p q n : ℕ}

theorem blockOrd_std (p q : ℕ) :
    BlockOrd (finSumFinEquiv : Ix p q ≃ Fin (p + q)) fun i => (finSumFinEquiv.symm i).isLeft := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · exact hab
  · exact hab.elim
  · exact hab.elim
  · exact Nat.add_lt_add_left hab p

theorem blockOrd_perm {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (s : Equiv.Perm (Fin n))
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) : BlockOrd (e.trans s.symm) (ε ∘ s) := by
  refine ⟨fun i => by simpa using h.1 i, fun j => by simpa using h.2.1 j, ?_⟩
  intro a b hab
  obtain ⟨hlt, hε⟩ := (h.posC_iff a b).1 hab
  simp only [Equiv.trans_apply]
  rcases lt_trichotomy (s.symm (e a)) (s.symm (e b)) with h1 | h1 | h1
  · exact h1
  · exact absurd (s.symm.injective h1) (ne_of_lt hlt)
  · have h2 := hs _ _ h1 (by simp only [Equiv.apply_symm_apply]; exact hε.symm)
    simp only [Equiv.apply_symm_apply] at h2
    exact absurd h2 (not_lt.2 hlt.le)

theorem exists_param_of_trivial (hE : GlobalTheory.Dec.DSExhaust) {T : GrpData p q} (R : DSRep T)
    (k : ∀ x, T.cov x = 1 → R.U.π x = 1) :
    ∃ (P : SignedPar (p + q)) (e : Ix p q ≃ Fin (p + q)), BlockOrd e P.sgn ∧ HasParam R (blockPar P e) := by
  obtain ⟨σ, hF⟩ := exists_factors R.U (finSumFinEquiv : Ix p q ≃ Fin (p + q)) k
  have hB0 := blockOrd_std p q
  have hIrr : GlobalTheory.Dec.IsSqIntIrr (fun i : Fin (p + q) => (finSumFinEquiv.symm i).isLeft) σ :=
    ⟨R.U.cs, R.nontriv,
      (GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q (p + q) _ _ T R σ hB0 hF).1,
      (GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q (p + q) _ _ T R σ hB0 hF).2,
      GlobalTheory.T.block_ordered_square_integrable p q (p + q) _ _ T R σ hB0 hF⟩
  obtain ⟨s, mu, hc, hs, hDS⟩ := hE (p + q) _ R.U.H σ hIrr
  let P : SignedPar (p + q) := ⟨mu, (fun i : Fin (p + q) => (finSumFinEquiv.symm i).isLeft) ∘ s, hc⟩
  have hB : BlockOrd ((finSumFinEquiv : Ix p q ≃ Fin (p + q)).trans s.symm) P.sgn := blockOrd_perm hB0 s hs
  have hF' : Factors R.U ((finSumFinEquiv : Ix p q ≃ Fin (p + q)).trans s.symm)
      (fun g => σ (g.submatrix s.symm s.symm)) := by
    intro x
    rw [hF x]
    congr 1
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact ⟨P, _, hB, (hasParam_iff_isDSPar R P hB hF').2 hDS⟩

theorem exists_param : GlobalTheory.Dec.DSExhaust → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T), ∃ lam, IsParam lam ∧ HasParam R lam := by
  intro hE p q _ T R
  rcases Cover.trivial_or_twist R with k | k
  · obtain ⟨P, e, h1, h2⟩ := exists_param_of_trivial hE R k
    exact ⟨_, isParam_blockPar P h1, h2⟩
  · obtain ⟨P, e, h1, h2⟩ := exists_param_of_trivial hE (Cover.twist R) k
    exact ⟨_, isParam_half P h1, (Cover.hasParam_twist R _).1 h2⟩

end GlobalTheory.CoverExhaust
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjMovesResidue

theorem exists_sub_star_notMem : ∀ (D : D7) (Q : Pl D.host.E), IsConjPl (D := D) Q Q →
    ∃ δ δ' : 𝓞 D.host.E, (δ' : D.host.E) = star (δ : D.host.E) ∧ δ - δ' ∉ Q.asIdeal := by
  intro D Q _
  obtain ⟨θ, t, h1, h2⟩ := Formalism.BasicNotions.Examples₂.unram_at D.host Q.asIdeal Q.isMaximal
  refine ⟨θ, t, ?_, h2⟩
  change algebraMap (𝓞 D.host.E) D.host.E t = _
  rw [h1, Formalism.BasicNotions.Examples₂.star_eq_conj]

end GlobalTheory.ConjMovesResidue
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.BlockPoly

variable (ι σ : Type) [Fintype ι] [DecidableEq ι]

noncomputable def blockMul :
    (ι → MvPolynomial σ ℂ) →ₘₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
    (fun τ => (rename (Prod.mk τ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (ι × σ) ℂ).toLinearMap)

theorem blockMul_apply (f : ι → MvPolynomial σ ℂ) :
    blockMul ι σ f = ∏ τ, rename (Prod.mk τ) (f τ) := by
  simp [blockMul]

noncomputable def expEquiv : (ι → σ →₀ ℕ) ≃ (ι × σ →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm.trans Finsupp.curryEquiv.symm

theorem expEquiv_apply (d : ι → σ →₀ ℕ) (a : ι) (b : σ) : expEquiv ι σ d (a, b) = d a b := by
  simp [expEquiv]

theorem sum_mapDomain_eq (d : ι → σ →₀ ℕ) :
    ∑ τ, (d τ).mapDomain (Prod.mk τ) = expEquiv ι σ d := by
  ext ⟨a, b⟩
  rw [expEquiv_apply, Finset.sum_apply', Finset.sum_eq_single a]
  · exact Finsupp.mapDomain_apply_of_injective (fun x y h => by simpa using h) _ _
  · intro τ _ hτ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨c, hc⟩
    exact hτ (congrArg Prod.fst hc)
  · intro h; exact absurd (Finset.mem_univ a) h

theorem prod_rename_monomial (d : ι → σ →₀ ℕ) :
    ∏ τ, rename (Prod.mk τ) (monomial (d τ) (1 : ℂ)) = monomial (expEquiv ι σ d) 1 := by
  simp only [rename_monomial]
  rw [← monomial_sum_one, sum_mapDomain_eq]

noncomputable def blockEquiv :
    PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
  (Basis.piTensorProduct (fun _ : ι => basisMonomials σ ℂ)).equiv
    (basisMonomials (ι × σ) ℂ) (expEquiv ι σ)

theorem blockEquiv_toLinearMap :
    (blockEquiv ι σ).toLinearMap = PiTensorProduct.lift (blockMul ι σ) := by
  refine (Basis.piTensorProduct (fun _ : ι => basisMonomials σ ℂ)).ext (fun p => ?_)
  rw [LinearEquiv.coe_coe, blockEquiv, Module.Basis.equiv_apply, Basis.piTensorProduct_apply,
    PiTensorProduct.lift.tprod, blockMul_apply]
  simp only [coe_basisMonomials]
  rw [prod_rename_monomial]

theorem blockEquiv_tprod (f : ι → MvPolynomial σ ℂ) :
    blockEquiv ι σ (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  rw [← LinearEquiv.coe_coe, blockEquiv_toLinearMap, PiTensorProduct.lift.tprod, blockMul_apply]

theorem map_subtype_injective (U : ι → Submodule ℂ (MvPolynomial σ ℂ)) :
    Function.Injective (PiTensorProduct.map fun τ => (U τ).subtype) := by
  choose g hg using fun τ => LinearMap.exists_leftInverse_of_injective (U τ).subtype (U τ).ker_subtype
  have h : (PiTensorProduct.map g) ∘ₗ (PiTensorProduct.map fun τ => (U τ).subtype) =
      LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [hg]
    exact PiTensorProduct.map_id
  exact Function.LeftInverse.injective (g := PiTensorProduct.map g)
    (fun x => by simpa using LinearMap.congr_fun h x)

theorem exists_blockEquiv :
    ∀ (ι σ : Type) [Fintype ι] [DecidableEq ι], ∃ e : PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ, (∀ f : ι → MvPolynomial σ ℂ, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ)) ∧ ∀ U : ι → Submodule ℂ (MvPolynomial σ ℂ), Function.Injective (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) ∧ LinearMap.range (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) = Submodule.span ℂ {p | ∃ f : ι → MvPolynomial σ ℂ, (∀ τ, f τ ∈ U τ) ∧ p = ∏ τ, rename (Prod.mk τ) (f τ)} := by
  intro ι σ _ _
  refine ⟨blockEquiv ι σ, blockEquiv_tprod ι σ, fun U => ⟨?_, ?_⟩⟩
  · exact (blockEquiv ι σ).injective.comp (map_subtype_injective ι σ U)
  · rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span]
    congr 1
    ext p
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨fun τ => (g τ : MvPolynomial σ ℂ), fun τ => (g τ).2, ?_⟩
      simp [PiTensorProduct.map_tprod, blockEquiv_tprod]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨PiTensorProduct.tprod ℂ (fun τ => (⟨f τ, hf τ⟩ : U τ)), ⟨_, rfl⟩, ?_⟩
      simp [PiTensorProduct.map_tprod, blockEquiv_tprod]

end GlobalTheory.BlockPoly
end
