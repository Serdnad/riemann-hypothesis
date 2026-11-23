module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle265
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle274
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.THProvA
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle280
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle291
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacProj

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem coords {m : ℕ} (v : Mx D S.rank m) :
    v = d.jX ⬝ (d.pX ⬝ v) + d.j0 ⬝ (d.p0 ⬝ v) + d.jY ⬝ (d.pY ⬝ v) := by
  conv_lhs => rw [← Matrix.one_mul v, ← d.sum_eq_one]
  simp only [Matrix.add_mul, Matrix.mul_assoc]

theorem pY_inv (g : GA D S) : d.pY ⬝ mt S g⁻¹ = adj (mt S g ⬝ d.jX) ⬝ gA S := by
  rw [mt_inv, d.pY_eq, adj_mul]
  simp only [Matrix.mul_assoc, gA_giA_cancel]

theorem witt_anisotropic_projection_unitary_inv_eq (g : GA D S) : d.p0 ⬝ mt S g⁻¹ = giA S₀ ⬝ (adj (mt S g ⬝ d.j0) ⬝ gA S) := by
  rw [mt_inv, d.p0_eq, adj_mul]
  simp only [Matrix.mul_assoc, gA_giA_cancel]

def Keeps (g : GA D S) : Prop :=
  d.p0 ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.j0) = 0

theorem expand {k m : ℕ} (Q : Mx D k S.rank) (A B : Mx D S.rank S.rank) (v : Mx D S.rank m) :
    Q ⬝ ((A * B) ⬝ v) = Q ⬝ (A ⬝ d.jX) ⬝ (d.pX ⬝ (B ⬝ v)) + Q ⬝ (A ⬝ d.j0) ⬝ (d.p0 ⬝ (B ⬝ v)) +
      Q ⬝ (A ⬝ d.jY) ⬝ (d.pY ⬝ (B ⬝ v)) := by
  conv_lhs => rw [← Matrix.mul_one A, ← d.sum_eq_one]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem keeps_jX {g : GA D S} (h : Keeps d g) : mt S g ⬝ d.jX = d.jX ⬝ (d.pX ⬝ (mt S g ⬝ d.jX)) := by
  have e := coords d (mt S g ⬝ d.jX)
  rw [h.1, h.2.1] at e
  simpa only [Matrix.mul_zero, add_zero] using e

theorem preserves_flag_anisotropic_action {g : GA D S} (h : Keeps d g) :
    mt S g ⬝ d.j0 = d.jX ⬝ (d.pX ⬝ (mt S g ⬝ d.j0)) + d.j0 ⬝ (d.p0 ⬝ (mt S g ⬝ d.j0)) := by
  have e := coords d (mt S g ⬝ d.j0)
  rw [h.2.2] at e
  simpa only [Matrix.mul_zero, add_zero] using e

theorem keeps_unitary {g : GA D S} (h : Keeps d g) :
    adj (d.p0 ⬝ (mt S g ⬝ d.j0)) ⬝ (gA S₀ ⬝ (d.p0 ⬝ (mt S g ⬝ d.j0))) = gA S₀ := by
  have hXX : ∀ {k : ℕ} (M : Mx D ρ k), adj d.jX ⬝ (gA S ⬝ (d.jX ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_XX, Matrix.zero_mul]
  have hX0 : ∀ {k : ℕ} (M : Mx D S₀.rank k), adj d.jX ⬝ (gA S ⬝ (d.j0 ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, Matrix.zero_mul]
  have h0X : ∀ {k : ℕ} (M : Mx D ρ k), adj d.j0 ⬝ (gA S ⬝ (d.jX ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_0X, Matrix.zero_mul]
  have h00 : ∀ {k : ℕ} (M : Mx D S₀.rank k), adj d.j0 ⬝ (gA S ⬝ (d.j0 ⬝ M)) = gA S₀ ⬝ M := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_00]
  have hu : adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S₀ := by
    calc adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0))
        = adj d.j0 ⬝ ((adj (mt S g) * (gA S * mt S g)) ⬝ d.j0) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = gA S₀ := by rw [mt_unitary, d.gram_00]
  rw [preserves_flag_anisotropic_action d h] at hu
  generalize d.pX ⬝ (mt S g ⬝ d.j0) = P at hu
  generalize d.p0 ⬝ (mt S g ⬝ d.j0) = C at hu ⊢
  simpa only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, hX0, h0X, h00,
    Matrix.mul_zero, zero_add, add_zero] using hu

theorem keeps_mul {g g' : GA D S} (h : Keeps d g) (h' : Keeps d g') : Keeps d (g * g') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mt_mul, expand, h.1, h'.1, h'.2.1]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · rw [mt_mul, expand, h.2.1, h'.1, h'.2.1]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · rw [mt_mul, expand, h.2.1, h.2.2, h'.2.2]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem keeps_inv {g : GA D S} (h : Keeps d g) : Keeps d g⁻¹ := by
  obtain ⟨P, hP⟩ : ∃ P : Mx D ρ ρ, mt S g ⬝ d.jX = d.jX ⬝ P := ⟨_, keeps_jX d h⟩
  obtain ⟨P', C, hC⟩ : ∃ (P' : Mx D ρ S₀.rank) (C : Mx D S₀.rank S₀.rank), mt S g ⬝ d.j0 = d.jX ⬝ P' + d.j0 ⬝ C := ⟨_, _, preserves_flag_anisotropic_action d h⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, witt_anisotropic_projection_unitary_inv_eq, hC]
    simp only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, d.gram_XX, d.gram_0X,
      Matrix.mul_zero, add_zero]
  · rw [← Matrix.mul_assoc, pY_inv, hP]
    simp only [adj_mul, Matrix.mul_assoc, d.gram_XX, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, pY_inv, hP]
    simp only [adj_mul, Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, Matrix.mul_zero]

theorem preserves_flag_anisotropic_block_one_inv {g : GA D S} (h : Keeps d g) (h1 : d.p0 ⬝ (mt S g ⬝ d.j0) = 1) : d.p0 ⬝ (mt S g⁻¹ ⬝ d.j0) = 1 := by
  have e := preserves_flag_anisotropic_action d h
  rw [h1, Matrix.mul_one] at e
  obtain ⟨P, hP⟩ : ∃ P : Mx D ρ S₀.rank, mt S g ⬝ d.j0 = d.jX ⬝ P + d.j0 := ⟨_, e⟩
  rw [← Matrix.mul_assoc, witt_anisotropic_projection_unitary_inv_eq, hP]
  simp only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, d.gram_00,
    Matrix.mul_zero, zero_add]
  exact giA_mul_gA S₀

theorem keeps_one : Keeps d 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [mt_one, Matrix.one_mul]
  · exact d.p0_jX
  · exact d.pY_jX
  · exact d.pY_j0

def keepSub : Subgroup (GA D S) where
  carrier := {g | Keeps d g}
  one_mem' := keeps_one d
  mul_mem' := keeps_mul d
  inv_mem' := keeps_inv d

def keepSub1 : Subgroup (GA D S) where
  carrier := {g | Keeps d g ∧ d.p0 ⬝ (mt S g ⬝ d.j0) = 1}
  one_mem' := ⟨keeps_one d, by rw [mt_one, Matrix.one_mul, HypDec.p0_j0]⟩
  mul_mem' := fun {a b} ha hb => ⟨keeps_mul d ha.1 hb.1, by
    rw [mt_mul, expand, ha.1.1, ha.2, hb.1.2.2, hb.2]
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.one_mul]⟩
  inv_mem' := fun {a} ha => ⟨keeps_inv d ha.1, preserves_flag_anisotropic_block_one_inv d ha.1 ha.2⟩

theorem flag_le : flagN d ≤ keepSub1 d := by
  intro n hn
  obtain ⟨T, b, -, hX, h0⟩ := exists_blocks d hn
  have eX : ∀ {k : ℕ} (Q : Mx D k S.rank), Q ⬝ (mt S n ⬝ d.jX) = Q ⬝ d.jX + Q ⬝ d.jX ⬝ T := fun Q => by
    rw [hX, Matrix.mul_add, Matrix.mul_assoc]
  have e0 : ∀ {k : ℕ} (Q : Mx D k S.rank), Q ⬝ (mt S n ⬝ d.j0) = Q ⬝ d.j0 + Q ⬝ d.jX ⬝ b := fun Q => by
    rw [h0, Matrix.mul_add, Matrix.mul_assoc]
  show (_ ∧ _ ∧ _) ∧ _
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [eX, d.p0_jX, Matrix.zero_mul, add_zero]
  · rw [eX, d.pY_jX, Matrix.zero_mul, add_zero]
  · rw [e0, d.pY_j0, d.pY_jX, Matrix.zero_mul, add_zero]
  · rw [e0, d.p0_j0, d.p0_jX, Matrix.zero_mul, add_zero]

theorem range_le : d.emb0.range ≤ keepSub d := by
  rintro _ ⟨h, rfl⟩
  show _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [d.wittDecomp_anisotropicEmbedding_inclX, d.p0_jX]
  · rw [d.wittDecomp_anisotropicEmbedding_inclX, d.pY_jX]
  · rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, d.pY_j0, Matrix.zero_mul]

theorem jac_le : (flagN d ⊔ d.emb0.range : Subgroup (GA D S)) ≤ keepSub d :=
  sup_le (fun _ hg => (flag_le d hg).1) (range_le d)

theorem witt_anisotropic_block_flag_mul_embedded {n : GA D S} (hn : n ∈ flagN d) (h : GA D S₀) :
    d.p0 ⬝ (mt S (n * d.emb0 h) ⬝ d.j0) = mt S₀ h := by
  have h1 : d.p0 ⬝ (mt S n ⬝ d.j0) = 1 := (flag_le d hn).2
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt S n), ← Matrix.mul_assoc d.p0, h1,
    Matrix.one_mul]

def proj (g : (flagN d ⊔ d.emb0.range : Subgroup (GA D S))) : GA D S₀ :=
  ofMat S₀ (d.p0 ⬝ (mt S g.1 ⬝ d.j0)) (keeps_unitary d (jac_le d g.2))

theorem continuous_proj : Continuous (proj d) := by
  apply continuous_of_mt
  simp only [proj, mt_ofMat]
  exact continuous_const.matrix_mul (((continuous_mt S).comp continuous_subtype_val).matrix_mul continuous_const)

theorem proj_mul (h : GA D S₀) (n : flagN d) :
    proj d ⟨n.1 * d.emb0 h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h := by
  apply mt_injective S₀
  simp only [proj, mt_ofMat]
  exact witt_anisotropic_block_flag_mul_embedded d n.2 h

theorem exists_continuous_proj : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ),
    ∃ p : (flagN d ⊔ d.emb0.range : Subgroup (GA D S)) → GA D S₀, Continuous p ∧
      ∀ (h : GA D S₀) (n : flagN d),
        p ⟨n.1 * d.emb0 h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h := by
  intro D S S₀ ρ d
  exact ⟨proj d, continuous_proj d, proj_mul d⟩

end GlobalTheory.JacProj
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixPer

theorem witt_anisotropic_group_normalizes_flag_unipotent : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∀ n ∈ flagN d, ∀ h : GA D S₀,
    d.emb0 h * n * (d.emb0 h)⁻¹ ∈ flagN d := by
  intro D S S₀ ρ d n hn h
  have he : Formalism.L2.Theta.mt S (d.emb0 h) ⬝ d.e.map (incA D) = d.e.map (incA D) := d.wittDecomp_anisotropicEmbedding_inclX h
  have he' := GlobalTheory.BesselChar.inv_fix_cols (GlobalTheory.BesselChar.mt_inv_mul S (d.emb0 h)) he
  unfold flagN at hn ⊢
  rw [GlobalTheory.BesselChar.mem_NFlag_iff S d.e (isIsoSub_e d).1] at hn ⊢
  rw [GlobalTheory.BesselChar.mt_mul, GlobalTheory.BesselChar.mt_mul]
  exact hn.conj he he' (GlobalTheory.BesselChar.mt_mul_inv S _) (GlobalTheory.BesselChar.perp_fixed d.e _ he')

end GlobalTheory.MixPer
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjAdjoint

theorem inner_eq_integral {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hH : R.models_HW)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : ∀ ρ, lowT (R.MW i σ) ρ)
    (hv : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) (a b : (R.HW i σ).H) :
    inner ℂ a b = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) *
      ∫ g in R.fdW i, star ((R.HW i σ).e a (fun ρ => v ρ) g) * (R.HW i σ).e b (fun ρ => v ρ) g ∂(R.νW i) := by
  obtain ⟨-, -, hip⟩ := hH i σ
  have hc := ipM_spec (R.MW i σ) (R.νW i) (R.fdW i) _ _
    (GlobalTheory.LiftLower.IsMultIP₂ (R.HW i σ) (N := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) hip a b)
  rw [hip, ipAt, (hc (fun ρ => v ρ) (fun ρ => v ρ)).2]
  congr 1
  rw [Finset.prod_eq_one, mul_one]
  intro ρ _
  rw [inner_self_eq_norm_sq_to_K, hv ρ]
  simp

end GlobalTheory.ConjAdjoint

namespace GlobalTheory.ConjAdjoint

theorem integrableOn_theta {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hI : GlobalTheory.LiftRows.InnerProductFormulaC R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (hL : GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io)
    (hM : IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0))
    (U : MMap (R.MW i σ)) (hU : U ∈ R.Wall i σ) (v : ∀ ρ, lowT (R.MW i σ) ρ) (h : GA D (Vc D i))
    (Q : PolF D (Wc D i).rank (Vc D i).rank) :
    IntegrableOn (fun g => Datum.thetaKO ω h g (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f Q) * starRingEnd ℂ (U (fun ρ => v ρ) g))
      (R.fdW i) (R.νW i) := by
  obtain ⟨μ, 𝓧, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)
  obtain ⟨⟨Fr, hFr⟩, h2⟩ := (hL.1.models.νW i).1.2.2 R.θ hL.1.models.inf
  obtain ⟨mR, hmR⟩ := (h2 Fr hFr).1
  exact (hI i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hL _ _ hM μ 𝓧 hμ Fr hFr mR hmR U hU U hU v v Q Q).1 h

end GlobalTheory.ConjAdjoint

namespace GlobalTheory.ConjAdjoint
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues



theorem adjoint_eq_upLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) (th : H.H →ₗ[ℂ] (R.HW i σ).H),
  Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f) io (LinearMap.range (c.ext ∘ₗ H.e)) thP →
  GlobalTheory.GalLift.IsProjOf R i σ thP th →
  ∀ (y : (R.HW i σ).H) (h : GA D (Vc D i)) (w : c.W),
    inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w =
      (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) fun ρ => v ρ) h := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hX hS hI hF hZ hR i σ s m μ' η' ω B f₀ f c io H hL hM hy hH v hv thP th hT hP y h w

  have hC : GlobalTheory.Hk3.Core R F := hL.1
  have hω := hL.2.2.2.2.2.1
  have hpt := hL.2.2.2.2.2.2.2.2.1
  have hc : c.Is := hL.2.2.2.2.2.2.2.2.2.1
  have hio := hL.2.2.2.2.2.2.2.2.2.2
  have hKc : starRingEnd ℂ (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _
  let φ : c.W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) := GlobalTheory.AdelicScalar.ptL R i σ B f (io (PiTensorProduct.tprod ℂ v))
  have hφ : ∀ w, Datum.IsThetaFunO R.ψ (Vc D i) (Wc D i) (φ w) := fun w => hpt _
  have hinf : ∀ u ∈ GinfC (Vc D i), ∀ w, ω (u, 1) (φ w) = φ (c.ρ u w) := fun u hu w => hio.1 u hu _ w
  have hlev : ∀ κ ∈ Lev.levA (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)), ∀ w,
      ω (κ, 1) (φ w) = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) κ)⁻¹ • φ w :=
    fun κ hκ w => hS i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hL κ hκ _
  have hWall : ∀ y' : (R.HW i σ).H, (R.HW i σ).e y' ∈ R.Wall i σ := fun y' =>
    GlobalTheory.AdelicScalar.HMod_mem (hC.models.HW i σ) y'
  have hth : ∀ y' : (R.HW i σ).H, ∀ w h, IntegrableOn (fun g => Datum.thetaKO ω h g (φ w) *
      starRingEnd ℂ ((R.HW i σ).e y' (fun ρ => v ρ) g)) (R.fdW i) (R.νW i) := fun y' w h =>
    integrableOn_theta R F hI i σ s m μ' η' ω B f₀ f c io hL hM _ (hWall y') v h (io (PiTensorProduct.tprod ℂ v) w)
  have hth' : ∀ y' : (R.HW i σ).H, ∀ w h, IntegrableOn (fun g => star (Datum.thetaKO ω h g (φ w)) *
      (R.HW i σ).e y' (fun ρ => v ρ) g) (R.fdW i) (R.νW i) := fun y' w h => by
    have h1 := hth y' w h
    have h2 : IntegrableOn (fun g => starRingEnd ℂ (Datum.thetaKO ω h g (φ w) *
        starRingEnd ℂ ((R.HW i σ).e y' (fun ρ => v ρ) g))) (R.fdW i) (R.νW i) :=
      h1.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable h1.1) (Filter.Eventually.of_forall fun x => by simp)
    refine Integrable.congr h2 (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.star_def]
  have hcls : ∀ u g, thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g =
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹ *
        Datum.thetaKO ω (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j)) g
          (φ (H.e u ((R.B.L i A.μ0).pres.y j))) := by
    intro u g
    refine (hT.eq _ _ _).trans ?_
    exact GlobalTheory.AdelicScalar.theta_classSum hω c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) φ hφ hinf hlev hM hy (GlobalTheory.AdelicScalar.HMod_mem hH u) g
  have hφw : ∀ w, φ w = ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w) := fun w => rfl
  clear_value φ
  have hex := GlobalTheory.AdelicScalar.exists_upVec hω c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) φ hφ hinf hlev (R.νW i) (R.fdW i)
    ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ)) (hth _)
  have hΨ := hex.choose_spec.1
  have hlaw := hex.choose_spec.2
  have hzex := GlobalTheory.AdelicScalar.HMod_onto hH (GlobalTheory.AdelicScalar.upVec_mem c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) hex.choose hlaw)
  have hz := hzex.choose_spec
  have hinv : ∀ u, ∀ γ ∈ GQ (Wc D i), ∀ g, thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) (γ * g) =
      thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g := by
    intro u γ hγ g
    refine (hcls u (γ * g)).trans (Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (hcls u g).symm)
    exact congrArg _ (GlobalTheory.T.thetaKO_mul_left_invariant_of_mem_GQ R i _ _ ω hω _ (hφ _) _ γ hγ g)
  have eF : ∀ u (y' : (R.HW i σ).H), (fun g => star (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g) *
      (R.HW i σ).e y' (fun ρ => v ρ) g) = fun g =>
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹ *
        (star (Datum.thetaKO ω (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j)) g
          (φ (H.e u ((R.B.L i A.μ0).pres.y j)))) * (R.HW i σ).e y' (fun ρ => v ρ) g) := by
    intro u y'
    funext g
    refine (congrArg (fun t => star t * (R.HW i σ).e y' (fun ρ => v ρ) g) (hcls u g)).trans ?_
    simp only [star_sum, Finset.sum_mul, star_mul', star_inv₀, star_natCast]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hintF : ∀ u (y' : (R.HW i σ).H), IntegrableOn (fun g => star (thP ((c.ext ∘ₗ H.e).rangeRestrict u)
      (PiTensorProduct.tprod ℂ v) g) * (R.HW i σ).e y' (fun ρ => v ρ) g) (R.fdW i) (R.νW i) := by
    intro u y'
    have hsum := integrable_finsetSum (μ := (R.νW i).restrict (R.fdW i)) Finset.univ fun j _ =>
      (hth' y' (H.e u ((R.B.L i A.μ0).pres.y j)) (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j))).const_mul
        ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹
    exact hsum.congr (Filter.Eventually.of_forall fun g => (congrFun (eF u y') g).symm)
  have hpair : ∀ u, ∫ g in R.fdW i, star (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g) *
      (R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ) g ∂(R.νW i) = inner ℂ u hzex.choose := by
    intro u
    refine (congrArg (fun F => ∫ g in R.fdW i, F g ∂(R.νW i)) (eF u (GlobalTheory.LiftLower.projH R i σ y))).trans ?_
    refine (integral_finsetSum _ fun j _ => (hth' _ _ _).const_mul _).trans ?_
    refine Eq.trans ?_ (hH.2.2 u hzex.choose).symm
    refine Eq.trans ?_ (congrArg (Bridge.adInner _ _ _ (H.e u)) hz).symm
    unfold Bridge.adInner
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (integral_const_mul _ _).trans (congrArg _ ?_)
    refine Eq.trans ?_ (inner_conj_symm _ _)
    refine Eq.trans ?_ (congrArg (starRingEnd ℂ) (hΨ _ _)).symm
    unfold GlobalTheory.AdelicScalar.l2 Lift.pet
    refine Eq.trans ?_ integral_conj
    refine congrArg (fun F : GA D (Wc D i) → ℂ => ∫ g in R.fdW i, F g ∂(R.νW i)) (funext fun g => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.star_def]
  have hadj : LinearMap.adjoint th y = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) • hzex.choose := by
    refine ext_inner_left ℂ fun u => ?_
    have e1 : (fun g => star ((R.HW i σ).e (th u) (fun ρ => v ρ) g) * (R.HW i σ).e y (fun ρ => v ρ) g) =
        fun g => star (R.eWf i σ (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v)) g) *
          (R.HW i σ).e y (fun ρ => v ρ) g :=
      funext fun g => congrArg (fun t : GA D (Wc D i) → ℂ => star (t g) * (R.HW i σ).e y (fun ρ => v ρ) g) (hP u v)
    refine (LinearMap.adjoint_inner_right th u y).trans ?_
    refine (inner_eq_integral R hC.models.HW i σ v hv (th u) y).trans ?_
    refine Eq.trans ?_ (inner_smul_right _ _ _).symm
    refine congrArg _ (Eq.trans ?_ (hpair u))
    refine (congrArg (fun F : GA D (Wc D i) → ℂ => ∫ g in R.fdW i, F g ∂(R.νW i)) e1).trans ?_
    exact GlobalTheory.T.integral_goodProjector_move_petersson R F hC hX i σ v _ (hinv u) (hintF u) y
  have e3 : c.ext (H.e (LinearMap.adjoint th y)) h = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) • hex.choose h := by
    refine (congrArg (fun x => c.ext (H.e x) h) hadj).trans ?_
    simp only [map_smul, Pi.smul_apply]
    exact congrArg _ ((congrArg (fun x => c.ext x h) hz).trans
      (GlobalTheory.T.extend_restriction_finitePoints_eq c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) hex.choose hlaw h))
  refine (congrArg (fun a => inner ℂ a w) e3).trans ?_
  refine (inner_smul_left _ _ _).trans ?_
  refine congrArg₂ (· * ·) hKc ?_
  exact (hΨ h w).trans (congrArg (fun p => GlobalTheory.AdelicScalar.l2 (R.νW i) (R.fdW i) (fun g => Datum.thetaKO ω h g p)
    ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ))) (hφw w))

end GlobalTheory.ConjAdjoint
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

theorem detPow_mul_ne_zero_exp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (m : D.what₂.Tau → ℤ), (∀ a b, detPow θ V m (a * b) = detPow θ V m a * detPow θ V m b) ∧ (∀ a, detPow θ V m a ≠ 0) ∧ (∀ Y : GlobalTheory.SmoothForms.LieN V, detPow θ V m (GlobalTheory.SmoothForms.expInf θ V Y) = cexp (GlobalTheory.AdSpan.ConjHol.trLin V m Y)) := by
  intro D θ hθ V m
  have R : GlobalTheory.SmoothForms.RealPoints θ V := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hd : ∀ a, detPow θ V m a = ∏ ρ, (infMat D.sp.cm.sig V.gram (θ ρ) a).det ^ (m ρ) := fun a => rfl
  refine ⟨fun a b => ?_, fun a => ?_, fun Y => ?_⟩
  · rw [hd, hd, hd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [R.2.2.2.1, det_mul, mul_zpow]
  · rw [hd]
    refine Finset.prod_ne_zero_iff.2 fun ρ _ => zpow_ne_zero _ fun h0 => ?_
    have h : (infMat D.sp.cm.sig V.gram (θ ρ) a)ᴴ * gramAt D V ρ * infMat D.sp.cm.sig V.gram (θ ρ) a = gramAt D V ρ :=
      GlobalTheory.RealLift.archM_mem hθ V a ρ
    have h2 := congrArg det h
    rw [det_mul, h0, mul_zero] at h2
    exact (R.1 ρ).2.ne_zero h2.symm
  · rw [hd]
    change _ = cexp (∑ ρ, (m ρ : ℂ) * trace (Y ρ).1)
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [(GlobalTheory.SmoothForms.isExpFam_expInf R Y).2 ρ, Formalism.MainNotions.DIV.Inh.det_exp, Complex.exp_int_mul]

end GlobalTheory.AdSpan.ConjHol
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adjointFrameRowReduction_conjLinear_integers : ∀ (D : D7) (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) (u v : Fin T.rank → D.host.E), IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e u) → IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e v) → ∀ c : 𝓞 D.host.E, IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v)) ∧ GlobalTheory.LiftDat.rowRed T βT a e PP ((c : D.host.E) • u + v) = fun j => Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) * GlobalTheory.LiftDat.rowRed T βT a e PP u j + GlobalTheory.LiftDat.rowRed T βT a e PP v j := by
  first | exact @GlobalTheory.RowLin.rowRed_smul_add | exact GlobalTheory.RowLin.rowRed_smul_add | (intros; apply GlobalTheory.RowLin.rowRed_smul_add <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.residue_conjugatePlace_hermitian_dualBasis_stabiliser_eq_zero : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ PP : Pl D.host.E, GlobalTheory.SeeConjChar.sideAt X h PP = true → ∀ M ∈ St β, ∀ i j : Fin D.R.k, GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j))) = 0 := by
  first | exact @GlobalTheory.SeeConjChar.resT_cP_hT_bwd_eq_zero | exact GlobalTheory.SeeConjChar.resT_cP_hT_bwd_eq_zero | (intros; apply GlobalTheory.SeeConjChar.resT_cP_hT_bwd_eq_zero <;> assumption)
end
