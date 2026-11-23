module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle127
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle091
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle092
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped NNReal

noncomputable section
namespace GlobalTheory.RootEx.ConjVol

section Abstract
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def cj (U : Subgroup G) (g : Subgroup.normalizer (U : Set G)) : U ≃ₜ* U where
  toMulEquiv := U.normalizerMonoidHom g
  continuous_toFun := Continuous.subtype_mk
    (f := fun u : U => (g : G) * u * (g : G)⁻¹) (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk
    (f := fun u : U => ((g⁻¹ : Subgroup.normalizer (U : Set G)) : G) * u *
      ((g⁻¹ : Subgroup.normalizer (U : Set G)) : G)⁻¹) (by fun_prop) _

theorem cj_coe (U : Subgroup G) (g : Subgroup.normalizer (U : Set G)) (u : U) :
    (cj U g u : G) = g * u * (g : G)⁻¹ := rfl

variable (U : Subgroup G) [MeasurableSpace U] [BorelSpace U] [LocallyCompactSpace U]

def md : Subgroup.normalizer (U : Set G) →* ℝ≥0 where
  toFun g := mulEquivHaarChar (cj U g)
  map_one' := by
    have : cj U 1 = ContinuousMulEquiv.refl U := by ext u; simp [cj_coe]
    simp only [this, mulEquivHaarChar_refl]
  map_mul' a b := by
    have : cj U (a * b) = (cj U b).trans (cj U a) := by ext u; simp [cj_coe, mul_assoc]
    simp only [this, mulEquivHaarChar_trans, mul_comm]

theorem md_ne_zero (g : Subgroup.normalizer (U : Set G)) : md U g ≠ 0 := (mulEquivHaarChar_pos _).ne'

theorem md_conj (x g : Subgroup.normalizer (U : Set G)) : md U (x * g * x⁻¹) = md U g := by
  rw [map_mul, map_mul, mul_right_comm, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem integral_conj_of_md (μ : Measure U) [μ.IsHaarMeasure] [μ.Regular]
    (g : Subgroup.normalizer (U : Set G)) (hg : md U g = 1) (f : G → ℂ) :
    ∫ u : U, f (g * (u : G) * (g : G)⁻¹) ∂μ = ∫ u : U, f u ∂μ := by
  have h := mulEquivHaarChar_smul_map μ (cj U g)
  rw [show mulEquivHaarChar (cj U g) = 1 from hg, one_smul] at h
  have h3 := integral_map_equiv (μ := μ) (cj U g).toHomeomorph.toMeasurableEquiv (fun u : U => f u)
  rw [show ⇑(cj U g).toHomeomorph.toMeasurableEquiv = ⇑(cj U g) from rfl, h] at h3
  exact h3.symm

end Abstract

section Alg
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem conj_mem_of_tri {p : ℕ} {g u : GL (n ⊕ Fin c) k} (hg : g.val.BlockTriangular (lev p))
    (hg' : (g⁻¹).val.BlockTriangular (lev p)) (hu : u ∈ N k n c p) : g * u * g⁻¹ ∈ N k n c p := by
  rw [Model.mem_N_iff] at hu ⊢
  intro r s hrs
  have e : (g * u * g⁻¹).val = 1 + g.val * (u.val - 1) * (g⁻¹).val := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv, Units.val_mul, Units.val_mul]
    abel
  rw [e, Matrix.add_apply, add_eq_left, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases ht : lev p s < lev p t
  · rw [hg' ht, mul_zero]
  rw [Matrix.mul_apply]
  refine mul_eq_zero_of_left (Finset.sum_eq_zero fun v _ => ?_) _
  by_cases hv : lev p v < lev p r
  · rw [hg hv, zero_mul]
  rw [Matrix.sub_apply, hu v t (by omega), sub_self, mul_zero]

theorem mem_normalizer_of_tri {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g.val.BlockTriangular (lev p))
    (hg' : (g⁻¹).val.BlockTriangular (lev p)) :
    g ∈ Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) := by
  rw [Subgroup.mem_normalizer_iff]
  refine fun u => ⟨conj_mem_of_tri hg hg', fun h => ?_⟩
  have := conj_mem_of_tri hg' (by rwa [inv_inv]) h
  simpa [mul_assoc] using this

theorem embX_tri (p : ℕ) (x : GL n k) : (embX c x).val.BlockTriangular (lev p) := by
  rintro (r | r) (s | s) h
  · simp [lev] at h
  · simp [VolN.val_embX]
  · simp [VolN.val_embX]
  · have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [VolN.val_embX, this]

theorem colE_tri (p : ℕ) (β : n → k) : (colE c p β).val.BlockTriangular (lev p) := by
  rintro (r | r) (s | s) h
  · simp [lev] at h
  · have : s.val + 1 ≠ p := by simp [lev] at h; omega
    simp [colE, upU, this]
  · simp [colE, upU]
  · have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [colE, upU, this]

theorem embX_mem (p : ℕ) (x : GL n k) :
    embX c x ∈ Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) :=
  mem_normalizer_of_tri (embX_tri p x) (by rw [← map_inv]; exact embX_tri p _)

theorem colE_mem (p : ℕ) (β : n → k) :
    colE c p β ∈ Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) :=
  mem_normalizer_of_tri (colE_tri p β) (by
    rw [inv_eq_of_mul_eq_one_right (QuotStep.colE_neg p β)]; exact colE_tri p _)

theorem colE_add (p : ℕ) (u w : n → k) : colE c p (u + w) = colE c p u * colE c p w := by
  apply Units.ext
  simp only [colE, upU, Units.val_mul, fromBlocks_multiply]
  congr 1 <;> simp
  ext r i
  by_cases h : i.val + 1 = p <;> simp [h, add_comm]

end Alg

section Meas
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem exists_ne_zero_one [ValuativeRel.IsNontrivial k] : ∃ a : k, a ≠ 0 ∧ a ≠ 1 := by
  obtain ⟨γ, h0, h1⟩ := ValuativeRel.IsNontrivial.condition (R := k)
  obtain ⟨a, rfl⟩ := ValuativeRel.valuation_surjective γ
  exact ⟨a, by rintro rfl; simp at h0, by rintro rfl; simp at h1⟩

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem integral_conj_colE' (p : ℕ) (β : n → k) (f : GL (n ⊕ Fin c) k → ℂ) :
    ∫ u : N k n c p, f (colE c p β * (u : GL (n ⊕ Fin c) k) * (colE c p β)⁻¹) ∂(volN ν n c p) =
      ∫ u : N k n c p, f u ∂(volN ν n c p) := by
  haveI := secondCountable k
  haveI := t2Space k
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := _root_.GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (N k n c p) := Subtype.borelSpace _
  haveI : LocallyCompactSpace (N k n c p) := (VolN.isClosed_N p).locallyCompactSpace
  haveI : (volN ν n c p).IsHaarMeasure := VolN.isHaarMeasure_volN ν p
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  let E : (n → k) → Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) := fun b => ⟨_, colE_mem p b⟩
  have hs : ∀ a : k, a ≠ 0 → md (N k n c p) (E (a • β)) = md (N k n c p) (E β) := fun a ha => by
    let x : GL n k := Matrix.GeneralLinearGroup.scalar n (Units.mk0 a ha)
    rw [← md_conj (N k n c p) ⟨_, embX_mem p x⟩ (E β)]
    congr 1
    apply Subtype.ext
    refine Eq.trans ?_ (QuotStep.conj_colE p x β).symm
    change colE c p (a • β) = _
    congr 1
    funext i
    simp [x, Matrix.mulVec_diagonal]
  obtain ⟨a, h0, h1⟩ := exists_ne_zero_one (k := k)
  have e : E β = E (a • β) * E ((1 - a) • β) := by
    apply Subtype.ext
    change colE c p β = colE c p (a • β) * colE c p ((1 - a) • β)
    rw [← colE_add, ← add_smul, add_sub_cancel, one_smul]
  have h := congrArg (md (N k n c p)) e
  rw [map_mul, hs a h0, hs _ (sub_ne_zero.2 h1.symm)] at h
  exact integral_conj_of_md (N k n c p) (volN ν n c p) (E β)
    (mul_left_cancel₀ (md_ne_zero _ (E β)) (h.symm.trans (mul_one _).symm)) f

end Meas

theorem integral_conj_colE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (β : n → k) (f : GL (n ⊕ Fin c) k → ℂ), ∫ u : N k n c (ρ + 1), f (colE c (ρ + 1) β * (u : GL (n ⊕ Fin c) k) * (colE c (ρ + 1) β)⁻¹) ∂(volN ν n c (ρ + 1)) = ∫ u : N k n c (ρ + 1), f u ∂(volN ν n c (ρ + 1)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ ρ _ _ ν _ β f => integral_conj_colE' ν (ρ + 1) β f

end GlobalTheory.RootEx.ConjVol
end
end

section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition

namespace GlobalTheory.ParahoricConjugateOpen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_conj_inf {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (g : G) :
    IsOpen ((H.map (MulAut.conj g).toMonoidHom ⊓ H : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]
  refine IsOpen.inter ?_ hH
  have : ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
  rw [this]
  exact hH.preimage (by fun_prop)

theorem isOpen_KO (n : Type) [Fintype n] [DecidableEq n] : IsOpen (KO k n : Set (GL n k)) :=
  Subgroup.isOpen_mono StepData.KOne_le_KO StepData.isOpen_KOne

theorem isOpen_parahoric (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] :
    IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  refine Subgroup.isOpen_mono (H₁ := KOne k (A ⊕ D)) (fun g hg => ?_) StepData.isOpen_KOne
  refine mem_parahoric.2 ⟨StepData.KOne_le_KO hg, fun i j => ?_⟩
  simpa using StepData.mem_KOne.1 hg (.inr i) (.inl j)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem torusElt_zero (n : Type) [Fintype n] [DecidableEq n] (ϖ : kˣ) :
    torusElt k n ϖ (fun _ => 0) = 1 := by
  refine Units.ext ?_
  rw [val_torusElt]
  simp

theorem conj_one_inf {G : Type} [Group G] (H : Subgroup G) :
    (H.map (MulAut.conj (1 : G)).toMonoidHom ⊓ H : Subgroup G) = H := by
  have : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [this, Subgroup.map_id, inf_idem]

theorem vol_conj_inf [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ)
    (hϖ : valuation k (ϖ : k) = uniformizer k)
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ) :
    (volM ν (A ⊕ D) (A ⊕ D) (Units.val ''
      (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom ⊓ parahoric k A D :
        Subgroup (GL (A ⊕ D) k)) : Set (GL (A ⊕ D) k)))).toReal =
      (volM ν A A (Units.val '' (KO k A : Set (GL A k)))).toReal *
        (ν (𝒪[k] : Set k)).toReal ^ (2 * (Fintype.card A * Fintype.card D)) *
        (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e))) *
        (volM ν D D (Units.val '' (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom ⊓ KO k D :
          Subgroup (GL D k)) : Set (GL D k)))).toReal := by
  have hq : (0 : ℝ) < resCard k := Nat.cast_pos.2 Nat.card_pos
  have h1 := GlobalTheory.T.matrixEntrywiseProductMeasure_uniformizer_power_box k ν ϖ hϖ A D (fun _ j => max 0 (-e j))
  have h2 := GlobalTheory.T.matrixEntrywiseProductMeasure_uniformizer_power_box k ν ϖ hϖ D A (fun i _ => 1 + max 0 (e i))
  rw [GlobalTheory.T.val_twoBlockParahoric_inf_torusConj_blockwise k ϖ hϖ A D e, GlobalTheory.T.volM_blocks_eq_mul, h1, h2]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (zpow_pos hq _).le]
  have hs : -((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e)) =
      (-∑ _i : A, ∑ j : D, max 0 (-e j)) + (-∑ i : D, ∑ _j : A, (1 + max 0 (e i))) := by
    have : sumAbs e = ∑ j : D, max 0 (-e j) + ∑ j : D, max 0 (e j) := by
      rw [sumAbs, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases le_total 0 (e j) with h | h
      · rw [abs_of_nonneg h, max_eq_left (by omega), max_eq_right h]; ring
      · rw [abs_of_nonpos h, max_eq_right (by omega), max_eq_left h]; ring
    rw [this, Finset.sum_comm (s := (Finset.univ : Finset D))]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_add_distrib]
    ring
  rw [hs, zpow_add₀ hq.ne', mul_comm (Fintype.card D) (Fintype.card A)]
  ring

theorem relIndex_conj_parahoric (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k)
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ) :
    ((((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom).relIndex (parahoric k A D) : ℕ) : ℝ) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        ((((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom).relIndex (KO k D) : ℕ) : ℝ) := by
  borelize k
  let ν : Measure k := Measure.addHaar
  have hq : (0 : ℝ) < resCard k := Nat.cast_pos.2 Nat.card_pos
  obtain ⟨hp, hJ⟩ := GlobalTheory.T.relIndex_mul_matrixVolume_open_subgroup_integralGL k ν (A ⊕ D) _ (parahoric k A D) inf_le_right
    (fun g hg => (mem_parahoric.1 hg).1) (isOpen_conj_inf _ (isOpen_parahoric A D) (mtor (A := A) ϖ e))
  obtain ⟨-, hK⟩ := GlobalTheory.T.relIndex_mul_matrixVolume_open_subgroup_integralGL k ν D _ (KO k D) inf_le_right le_rfl
    (isOpen_conj_inf _ (isOpen_KO D) (torusElt k D ϖ e))
  rw [Subgroup.inf_relIndex_right] at hJ hK
  have h0 := vol_conj_inf ν ϖ hϖ A D (fun _ => 0)
  have hm : mtor (A := A) ϖ (fun _ : D => 0) = 1 := by
    rw [← torusElt_zero (A ⊕ D) ϖ, mtor]
    congr 1
    funext x
    cases x <;> rfl
  rw [hm, torusElt_zero, conj_one_inf, conj_one_inf] at h0
  refine mul_right_cancel₀ hp.ne' ?_
  rw [hJ, h0, ← hK, vol_conj_inf ν ϖ hϖ A D e]
  have hs : sumAbs (fun _ : D => (0 : ℤ)) = 0 := by simp [sumAbs]
  have hz : (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs (fun _ : D => (0 : ℤ))))) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e))) := by
    rw [← zpow_add₀ hq.ne', hs]
    congr 1
    ring
  rw [hz]
  ring

end GlobalTheory.ParahoricConjugateOpen
end
end

section

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.SmGL.Exponents.Additive

section General

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem exists_mem_twKer {ρ : Representation F G V} {σ : Representation F G W}
    (p : ρ.IntertwiningMap σ) (hp : Function.Surjective p) (N : Subgroup G) {w : W}
    (hw : w ∈ twKer σ N 1) : ∃ v ∈ twKer ρ N 1, p v = w := by
  have : twKer σ N 1 ≤ (twKer ρ N 1).map p.toLinearMap := Submodule.span_le.2 (by
    rintro _ ⟨n, w, rfl⟩
    obtain ⟨v, rfl⟩ := hp w
    refine ⟨_, Submodule.subset_span ⟨n, v, rfl⟩, ?_⟩
    simp [p.isIntertwining])
  exact this hw

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem wordMult_exact {π : Representation ℂ (GL (Fin n) k) V}
    {π₁ : Representation ℂ (GL (Fin n) k) W} {π₂ : Representation ℂ (GL (Fin n) k) U}
    (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂) (hπ : IsSmooth π)
    (hι : Function.Injective ι) (hp : Function.Surjective p) (he : Function.Exact ι p)
    (w : List ℂˣ) : wordMult π w = wordMult π₁ w + wordMult π₂ w := by
  unfold wordMult
  split_ifs
  swap
  · simp
  refine jhMult_exact (compMap (jacMap (points _) ι) _) (compMap (jacMap (points _) p) _)
    (isIrreducible_ofChar _) (GlobalTheory.T.jacquetModule_map_injective_of_injective k _ _ _ (points _) W V π₁ π ι hπ hι) (fun x => ?_)
    (fun x => ?_) (fun x hx => ?_)
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨v, rfl⟩ := hp u
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (p (ι u)) = 0
    rw [he.apply_apply_eq_zero]
    rfl
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : p v ∈ twKer π₂ (unipRad k (points (Fin n))) 1 :=
      (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨v', hv', h2⟩ := exists_mem_twKer p hp _ h1
    obtain ⟨u, hu⟩ := (he (v - v')).1 (by rw [map_sub, h2, sub_self])
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v
    rw [hu]
    exact (Submodule.Quotient.eq _).2 (by simpa using hv')

theorem wordMult_of_subsingleton [Subsingleton V] (π : Representation ℂ (GL (Fin n) k) V)
    (w : List ℂˣ) : wordMult π w = 0 := by
  unfold wordMult
  split_ifs
  · have : Subsingleton (Jacquet π (unipB k (Fin n))) :=
      (Submodule.Quotient.mk_surjective _).subsingleton
    exact jhMult_of_subsingleton (isIrreducible_ofChar _) _
  · rfl

theorem sum_add {I : Type 1} (f : I → ℕ∞) (x y : I →₀ ℤ) (hx : ∀ c, 0 ≤ x c) (hy : ∀ c, 0 ≤ y c) :
    ((x + y).sum fun c a => (a.toNat : ℕ∞) * f c) =
      (x.sum fun c a => (a.toNat : ℕ∞) * f c) + y.sum fun c a => (a.toNat : ℕ∞) * f c := by
  classical
  rw [Finsupp.sum_of_support_subset (x + y) Finsupp.support_add _ (by simp),
    Finsupp.sum_of_support_subset x Finset.subset_union_left _ (by simp),
    Finsupp.sum_of_support_subset y Finset.subset_union_right _ (by simp),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finsupp.add_apply, Int.toNat_add (hx c) (hy c), Nat.cast_add, add_mul]

theorem wordMult_eq_sum (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π)
    (hπ : IsSmooth π) (w : List ℂˣ) :
    wordMult π w = (cls π h).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  have hfl : ∀ S : Subrepresentation π, HasFiniteLength S.toRepresentation := fun S =>
    IsFiniteLength.of_injective h
      (f := Representation.IntertwiningMap.equivLinearMapAsModule S.toRepresentation π
        ⟨S.toSubmodule.subtype, fun _ => rfl⟩) Subtype.val_injective
  have hsm : ∀ S : Subrepresentation π, IsSmooth S.toRepresentation := fun S =>
    (IsSubquotient.of_injective (σ := S.toRepresentation) (ρ := π)
      ⟨S.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective).isSmooth hπ
  have key : ∀ S : Subrepresentation π, wordMult S.toRepresentation w =
      (cls S.toRepresentation (hfl S)).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    rcases eq_or_ne S ⊥ with rfl | hS
    · have : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
      have h0 : cls (⊥ : Subrepresentation π).toRepresentation (hfl ⊥) = 0 := by
        ext c
        simp [cls_apply, jhMult_of_subsingleton (IrrRep.irr _)]
      rw [h0, wordMult_of_subsingleton, Finsupp.sum_zero_index]
    obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hS)
    let ι : T.toRepresentation.IntertwiningMap S.toRepresentation :=
      ⟨Submodule.inclusion hT.le, fun _ => rfl⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hι : Function.Injective ι := Submodule.inclusion_injective hT.le
    have hps : Function.Surjective p := Submodule.Quotient.mk_surjective _
    have he : Function.Exact ι p := fun v =>
      ⟨fun hv => ⟨⟨v.1, (hp v).1 hv⟩, rfl⟩, by
        rintro ⟨u, rfl⟩
        exact (hp _).2 u.2⟩
    let σ : IrrRep (GL (Fin n) k) :=
      ⟨_, subQuot S T, (IsSubquotient.of_surjective p hps).isSmooth (hsm S),
        isIrreducible_subQuot hT⟩
    have hσ : cls (subQuot S T) σ.hasFiniteLength = Finsupp.single σ.cl 1 := cls_irr σ _
    obtain ⟨ψ⟩ := σ.nonempty_equiv_rep
    rw [wordMult_exact ι p (hsm S) hι hps he, cls_exact ι p hι hps he _ (hfl T) σ.hasFiniteLength,
      sum_add _ _ _ (fun c => by simp [cls_apply]) (fun c => by simp [cls_apply]), ih T hT.lt, hσ,
      Finsupp.sum_single_index (by simp), wordMult_congr ψ]
    simp [σ]
  rw [← wordMult_congr (topEquiv π), key ⊤, cls_congr (topEquiv π) _ h]

theorem wordMult_additive : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π), IsSmooth π → ∀ w : List ℂˣ, wordMult π w = (cls π h).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w :=
  fun _ _ _ _ _ _ _ _ _ π h hπ w => wordMult_eq_sum π h hπ w

end GlobalTheory.SmGL.Exponents.Additive
end
end
