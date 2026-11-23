module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle045
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MonomialOfClean
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle081
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Aesop.Main
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HermCoord
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Formalism.HermitianLattices.Bundle001
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem diagT_mem_parahoric (c : A ⊕ D → kˣ) (hc : ∀ i, valuation k (c i : k) = 1) :
    diagT k (A ⊕ D) c ∈ parahoric k A D := by
  rw [mem_parahoric]
  refine ⟨(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [val_diagT, diagonal_apply]
    split_ifs
    · exact (Valuation.mem_integer_iff _ _).2 (hc i).le
    · exact zero_mem _
  · rw [← map_inv, val_diagT, diagonal_apply]
    split_ifs
    · refine (Valuation.mem_integer_iff _ _).2 ?_
      simp [map_inv₀, hc i]
    · exact zero_mem _
  · rw [val_diagT, diagonal_apply_ne _ (by simp)]
    simp

theorem det_lower_diagT (c : A ⊕ D → kˣ) :
    ((diagT k (A ⊕ D) c : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det =
      ((∏ i, c (.inr i) : kˣ) : k) := by
  have : ((diagT k (A ⊕ D) c : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂ =
      diagonal fun i => (c (.inr i) : k) := by
    ext i j
    simp [toBlocks₂₂, val_diagT, diagonal_apply]
  rw [this, det_diagonal, Units.coe_prod]

theorem prod_mulSingle_inr (p : A ⊕ D) (u : kˣ) :
    (∏ i : D, (Pi.mulSingle p u : A ⊕ D → kˣ) (.inr i)) = if p.isRight then u else 1 := by
  rcases p with a | d
  · simp [Pi.mulSingle_apply]
  · simp [Pi.mulSingle_apply]

end GlobalTheory.ParHeckeSupp

namespace GlobalTheory.ParHeckeSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem eq_zero_of_mixed (ξ : kˣ →* ℂˣ) (hξ : ¬ IsUnram ξ) (φ : GL (A ⊕ D) k → ℂ) (hφ : IsBiType ξ φ)
    (m : GL (A ⊕ D) k) (τ : Equiv.Perm (A ⊕ D)) (hm : ∀ x y, y ≠ τ x → (m : Matrix (A ⊕ D) (A ⊕ D) k) x y = 0)
    (p : A ⊕ D) (hp : (τ p).isRight ≠ p.isRight) : φ m = 0 := by
  obtain ⟨u, hu1, hu⟩ : ∃ u : kˣ, valuation k (u : k) = 1 ∧ ξ u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hξ h
  have hv : ∀ q : A ⊕ D, ∀ i, valuation k ((Pi.mulSingle q u : A ⊕ D → kˣ) i : k) = 1 := fun q i => by
    rw [Pi.mulSingle_apply]
    split_ifs <;> simp [hu1]
  have hcomm : diagT k (A ⊕ D) (Pi.mulSingle p u) * m = m * diagT k (A ⊕ D) (Pi.mulSingle (τ p) u) := by
    ext x y
    simp only [Units.val_mul, val_diagT, diagonal_mul, mul_diagonal]
    by_cases hy : y = τ x
    · subst hy
      simp [Pi.mulSingle_apply, mul_comm]
    · simp [hm x y hy]
  have h1 := (hφ _ (diagT_mem_parahoric _ (hv p)) _ (det_lower_diagT _).symm m).1
  have h2 := (hφ _ (diagT_mem_parahoric _ (hv (τ p))) _ (det_lower_diagT _).symm m).2
  rw [hcomm, h2, prod_mulSingle_inr, prod_mulSingle_inr] at h1
  have hu' : (ξ u : ℂ) ≠ 1 := fun h => hu (Units.ext (by simpa using h))
  by_contra h0
  have h3 := mul_right_cancel₀ h0 h1
  cases h₁ : (τ p).isRight <;> cases h₂ : p.isRight <;> simp only [h₁, h₂] at h3 hp
  · exact hp rfl
  · exact hu' (by simpa using h3.symm)
  · exact hu' (by simpa using h3)
  · exact hp rfl

theorem exists_emb₂ (m : GL (A ⊕ D) k) (τ : Equiv.Perm (A ⊕ D))
    (hm : ∀ x y, y ≠ τ x → (m : Matrix (A ⊕ D) (A ⊕ D) k) x y = 0) (hτ : ∀ p, (τ p).isRight = p.isRight) :
    ∃ x y, m = emb₂ k (Equiv.refl (A ⊕ D)) (x, y) := by
  have h12 : (m : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₁₂ = 0 := by
    ext a d
    refine hm _ _ fun h => ?_
    have := hτ (.inl a)
    rw [← h] at this
    simp at this
  have h21 : (m : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₁ = 0 := by
    ext d a
    refine hm _ _ fun h => ?_
    have := hτ (.inr d)
    rw [← h] at this
    simp at this
  have hdet : (m : Matrix (A ⊕ D) (A ⊕ D) k).det =
      (m : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₁₁.det * (m : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det := by
    conv_lhs => rw [← fromBlocks_toBlocks (m : Matrix (A ⊕ D) (A ⊕ D) k), h12]
    exact det_fromBlocks_zero₁₂ _ _ _
  have hm0 : (m : Matrix (A ⊕ D) (A ⊕ D) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero
  rw [hdet] at hm0
  refine ⟨nonsingInvUnit _ (isUnit_iff_ne_zero.2 (left_ne_zero_of_mul hm0)),
    nonsingInvUnit _ (isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hm0)), Units.ext ?_⟩
  rw [val_emb₂]
  simp only [reindex_refl_refl]
  conv_lhs => rw [← fromBlocks_toBlocks (m : Matrix (A ⊕ D) (A ⊕ D) k), h12, h21]
  rfl

end GlobalTheory.ParHeckeSupp

namespace GlobalTheory.ParHeckeSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def numE : A ⊕ D ≃ Fin (Fintype.card A + Fintype.card D) :=
  (Equiv.sumCongr (Fintype.equivFin A) (Fintype.equivFin D)).trans finSumFinEquiv

theorem numE_lt (a : A) (d : D) : numE (A := A) (D := D) (.inl a) < numE (.inr d) := by
  simp only [numE, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_iff_val_lt_val, Fin.coe_castAdd,
    Fin.coe_natAdd]
  omega


variable (k A D) in
def toAD : GL (Fin (Fintype.card A + Fintype.card D)) k →* GL (A ⊕ D) k :=
  Units.map (reindexAlgEquiv k k (numE (A := A) (D := D)).symm).toMonoidHom

theorem toAD_val (g : GL (Fin (Fintype.card A + Fintype.card D)) k) (x y : A ⊕ D) :
    (toAD k A D g : Matrix (A ⊕ D) (A ⊕ D) k) x y = (g : Matrix _ _ k) (numE x) (numE y) := by
  simp [toAD, reindexAlgEquiv_apply, reindex_apply]

theorem toAD_surj (g : GL (A ⊕ D) k) : ∃ g₀, toAD k A D g₀ = g :=
  ⟨Units.map (reindexAlgEquiv k k (numE (A := A) (D := D))).toMonoidHom g,
    Units.ext (Matrix.ext fun x y => by rw [toAD_val]; simp [reindexAlgEquiv_apply, reindex_apply])⟩

theorem toAD_incl_mem (u : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.unipLevel k (Fintype.card A + Fintype.card D)) :
    toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u) ∈ parahoric k A D := by
  rw [mem_parahoric]
  refine ⟨⟨Units.map (reindexAlgEquiv 𝒪[k] 𝒪[k] (numE (A := A) (D := D)).symm).toMonoidHom u.1, ?_⟩,
    fun i j => ?_⟩
  · ext x y
    rw [toAD_val, GlobalTheory.TypeDim.incl_val]
    simp [reindexAlgEquiv_apply, reindex_apply]
    rfl
  · rw [toAD_val, GlobalTheory.TypeDim.incl_val]
    have h := ((mem_unipB _).1 (Subgroup.mem_comap.1 u.2)).1 _ _ (numE_lt j i)
    rw [GlobalTheory.TypeDim.red_val] at h
    exact (GlobalTheory.ParahoricLowerBlock.residue_eq_zero_iff_val _).1 h

theorem support_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ →
    ∀ φ : GL (A ⊕ D) k → ℂ, IsBiType ξ φ → ∀ g, φ g ≠ 0 → ∃ x y, ∃ j ∈ parahoric k A D,
      ∃ j' ∈ parahoric k A D, g = j * emb₂ k (Equiv.refl (A ⊕ D)) (x, y) * j' := by
  intro k _ _ _ _ A D _ _ _ _ ξ hξt hξ φ hφ g hg
  obtain ⟨g₀, rfl⟩ := toAD_surj g
  obtain ⟨u, u', w, c, e⟩ := GlobalTheory.TypeDim.IwahoriBruhat.iwahori_bruhat k _ g₀
  have hj := toAD_incl_mem (A := A) (D := D) u
  have hj' := toAD_incl_mem (A := A) (D := D) u'
  have hgm : toAD k A D g₀ = toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u) *
      toAD k A D (GlobalTheory.Parabolic.permGL k w * diagT k _ c) * toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u') := by
    rw [e]
    simp only [map_mul]
  generalize toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u) = j at hj hgm
  generalize toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u') = j' at hj' hgm
  let τ : Equiv.Perm (A ⊕ D) := numE.trans (w.symm.trans numE.symm)
  have hm : ∀ x y, y ≠ τ x →
      (toAD k A D (GlobalTheory.Parabolic.permGL k w * diagT k _ c) : Matrix (A ⊕ D) (A ⊕ D) k) x y = 0 := by
    intro x y h
    rw [toAD_val, Units.val_mul, val_diagT, mul_diagonal, GlobalTheory.Parabolic.permGL_apply, if_neg, zero_mul]
    intro h'
    apply h
    simp [τ, h']
  generalize toAD k A D (GlobalTheory.Parabolic.permGL k w * diagT k _ c) = m at hm hgm
  have hφm : φ m ≠ 0 := by
    intro h0
    apply hg
    obtain ⟨hd, -⟩ := GlobalTheory.ParahoricLowerBlock.lower_block_tame k A D ξ hξt j hj
    obtain ⟨hd', -⟩ := GlobalTheory.ParahoricLowerBlock.lower_block_tame k A D ξ hξt j' hj'
    rw [hgm, (hφ j' hj' (Units.mk0 _ hd') rfl _).2, (hφ j hj (Units.mk0 _ hd) rfl _).1, h0]
    simp
  have hτ : ∀ p, (τ p).isRight = p.isRight := by
    by_contra h
    push_neg at h
    obtain ⟨p, hp⟩ := h
    exact hφm (eq_zero_of_mixed ξ hξ φ hφ m τ hm p hp)
  obtain ⟨x, y, hxy⟩ := exists_emb₂ m τ hm hτ
  exact ⟨x, y, j, hj, j', hj', by rw [hgm, hxy]⟩

end GlobalTheory.ParHeckeSupp
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.PeriodicIntegral

theorem exists_irreducible_of_isUnif {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ϖ : kˣ} (h : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) :
    ∃ p : 𝒪[k], Irreducible p ∧ (p : k) = ϖ := by
  have hmem : (ϖ : k) ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff]; exact ((h ϖ).2 le_rfl).le
  refine ⟨⟨ϖ, hmem⟩, ?_, rfl⟩
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext y
  rw [Ideal.mem_span_singleton, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one, h]
  exact Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k)) (x := y) (y := ⟨(ϖ : k), hmem⟩)

theorem integral_eq_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (ϖ : kˣ), GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (A B : ℕ) (T : Finset k), (∀ t ∈ T, valuation k t ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k)) → (∀ x : k, valuation k x ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) → ∃! t, t ∈ T ∧ valuation k (x - t) ≤ valuation k ((ϖ : k) ^ B)) → ∀ (I : Type) [Fintype I] [DecidableEq I] (F : (I → k) → ℂ), (∀ x, F x ≠ 0 → ∀ i, valuation k (x i) ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k)) → (∀ x y, (∀ i, valuation k (y i) ≤ valuation k ((ϖ : k) ^ B)) → F (x + y) = F x) → ∫ x, F x ∂(Measure.pi fun _ : I => ν) = (((resCard k : ℂ) ^ B)⁻¹) ^ Fintype.card I * ∑ t ∈ Fintype.piFinset (fun _ : I => T), F t := by
  intro k _ _ _ _ _ _ ν hν ϖ hϖ A B T hT hU I _ _ F hF hper
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨p, hp, hpϖ⟩ := exists_irreducible_of_isUnif hϖ
  have hnabs : nabs k ϖ = (resCard k : ℝ)⁻¹ := nabs_uniformiser hp hpϖ.symm
  set u : kˣ := ϖ ^ B with hu
  let S : k → Set k := fun t => (fun x => -t + x) ⁻¹' cball u
  let box : (I → k) → Set (I → k) := fun t => Set.univ.pi fun i => S (t i)
  let P := Fintype.piFinset fun _ : I => T
  have hmemS : ∀ t x, x ∈ S t ↔ valuation k (x - t) ≤ valuation k ((ϖ : k) ^ B) := by
    intro t x; simp [S, cball, u, sub_eq_neg_add]
  have hmemBox : ∀ t x, x ∈ box t ↔ ∀ i, valuation k (x i - t i) ≤ valuation k ((ϖ : k) ^ B) := by
    intro t x; simp only [box, Set.mem_univ_pi, hmemS]
  have hshift : ∀ x t, x ∈ box t → F t = F x := by
    intro x t hx
    have := hper x (t - x) (fun i => by
      rw [Pi.sub_apply, ← Valuation.map_neg, neg_sub]; exact (hmemBox t x).1 hx i)
    simpa using this
  have hdec : ∀ x, F x = ∑ t ∈ P, (box t).indicator (fun _ => F t) x := by
    intro x
    by_cases h0 : F x = 0
    · rw [h0]; symm
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases hx : x ∈ box t
      · rw [Set.indicator_of_mem hx, hshift x t hx, h0]
      · rw [Set.indicator_of_notMem hx]
    · have hbig := hF x h0
      have hex := fun i => hU (x i) (hbig i)
      choose s hs hsu using hex
      have hsP : s ∈ P := Fintype.mem_piFinset.2 fun i => (hs i).1
      have hxs : x ∈ box s := (hmemBox s x).2 fun i => (hs i).2
      rw [Finset.sum_eq_single s, Set.indicator_of_mem hxs, hshift x s hxs]
      · intro t htP hts
        rw [Set.indicator_of_notMem]
        intro hxt
        apply hts
        funext i
        exact hsu i (t i) ⟨Fintype.mem_piFinset.1 htP i, (hmemBox t x).1 hxt i⟩
      · intro h; exact absurd hsP h
  have hmeasS : ∀ t, MeasurableSet (S t) := fun t =>
    measurable_const_add (-t) (isOpen_cball u).measurableSet
  have hmeasBox : ∀ t, MeasurableSet (box t) := fun t => MeasurableSet.univ_pi fun i => hmeasS (t i)
  have hνS : ∀ t, ν (S t) = (distribHaarChar k u : ℝ≥0∞) := by
    intro t; simp only [S]; rw [measure_preimage_add, measure_cball, hν.2, mul_one]
  have hμbox : ∀ t, (Measure.pi fun _ : I => ν) (box t) = (distribHaarChar k u : ℝ≥0∞) ^ Fintype.card I := by
    intro t; simp only [box]; rw [Measure.pi_pi]; simp [hνS]
  have hnu : nabs k u = nabs k ϖ ^ B := by simp [u, nabs, map_pow]
  have hreal : ∀ t, (Measure.pi fun _ : I => ν).real (box t) = ((resCard k : ℝ)⁻¹ ^ B) ^ Fintype.card I := by
    intro t
    rw [Measure.real, hμbox, ENNReal.toReal_pow, ENNReal.coe_toReal, ← hnabs, ← hnu]
    rfl
  calc ∫ x, F x ∂(Measure.pi fun _ : I => ν)
        = ∫ x, ∑ t ∈ P, (box t).indicator (fun _ => F t) x ∂(Measure.pi fun _ : I => ν) := by
          congr 1; funext x; exact hdec x
    _ = ∑ t ∈ P, ∫ x, (box t).indicator (fun _ => F t) x ∂(Measure.pi fun _ : I => ν) := by
          refine integral_finsetSum P fun t _ => ?_
          refine IntegrableOn.integrable_indicator ?_ (hmeasBox t)
          exact integrableOn_const (by rw [hμbox]; simp)
    _ = ∑ t ∈ P, (Measure.pi fun _ : I => ν).real (box t) • F t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          exact integral_indicator_const (F t) (hmeasBox t)
    _ = _ := by
          simp only [hreal, Complex.real_smul, ← Finset.mul_sum]
          push_cast
          rw [inv_pow]

end GlobalTheory.PeriodicIntegral
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.SymBridge

theorem iter_lam_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : (P.iter t μ hμ j).J), ∃ (g₀ : P.J) (D : Fin j → GL t k), (g₀ : GL r k).val = (g : GL (Ix r t j) k).val.submatrix Sum.inl Sum.inl ∧ (∀ i, D i ∈ KO k t ∧ (D i).val = Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val i) ∧ (P.iter t μ hμ j).lam g = P.lam g₀ * ∏ i : Fin j, μ (i.val + 1) (Matrix.GeneralLinearGroup.det (D i)) := by
  intro k _ _ _ _ r t _ _ _ _ P μ hμ j
  induction j with
  | zero =>
    intro g
    refine ⟨⟨(reGL (ixZero r t)).symm (g : GL (Ix r t 0) k), g.2⟩, fun i => i.elim0, rfl, fun i => i.elim0, ?_⟩
    rw [Fin.prod_univ_zero, mul_one]
    rfl
  | succ j ih =>
    intro g
    let h : (P.iter t μ hμ j).stepJ t := ⟨(reGL (ixSucc r t j)).symm g, g.2⟩
    obtain ⟨D, hD, eD⟩ := h.2.2.2.2.2
    have eu := TypeDatum.corner_val _ h
    have e := TypeDatum.step_lam_eq _ (μ (j + 1)) (hμ _) h _ eu D eD
    obtain ⟨g₀, D', e0, hD', el⟩ := ih (TypeDatum.corner _ h)
    refine ⟨g₀, Fin.snoc (α := fun _ => GL t k) D' D, ?_, ?_, ?_⟩
    · rw [e0, eu]; rfl
    · intro i
      induction i using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; exact ⟨hD, by rw [eD]; rfl⟩
      | cast i =>
        simp only [Fin.snoc_castSucc]
        refine ⟨(hD' i).1, ?_⟩
        rw [(hD' i).2, eu]; rfl
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
      rw [← mul_assoc, ← el]
      exact e

end GlobalTheory.SymBridge
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
open GlobalTheory.SWC GlobalTheory.HermSD

noncomputable section

namespace GlobalTheory.HermCoordEquiv

open GlobalTheory.GaussMean.OneVec

theorem sum_sum_split {M : Type} [AddCommMonoid M] {n : ℕ} (f : Fin n → Fin n → M) :
    ∑ a, ∑ b, f a b = ∑ a, f a a + ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (f p.1.1 p.1.2 + f p.1.2 p.1.1) := by
  classical
  have h1 : ∀ a b, f a b = (if a < b then f a b else 0) + (if a = b then f a b else 0) +
      (if b < a then f a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.2 h.le]
  have hsub : ∀ g : Fin n → Fin n → M, ∑ p : {p : Fin n × Fin n // p.1 < p.2}, g p.1.1 p.1.2 =
      ∑ a, ∑ b, if a < b then g a b else 0 := by
    intro g
    rw [← Fintype.sum_prod_type' (f := fun a b => if a < b then g a b else 0), ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) (fun a : Fin n × Fin n => g a.1 a.2)).symm
  rw [Finset.sum_add_distrib, hsub (fun a b => f a b), hsub (fun a b => f b a)]
  conv_lhs => enter [2, a, 2, b]; rw [h1 a b]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun a b => if b < a then f a b else 0)]
  abel

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  (R : Type) [CommRing R] [Algebra F R]

theorem pair_eq (h : IsCMExt F E σ) {n : ℕ} (S T : HermR R σ n) :
    pairHerm R σ n S T = coordPair R σ n (hermCoord R σ S) (hermCoord R σ T) := by
  unfold pairHerm coordPair
  rw [sum_sum_split (fun a b => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * (T : Matrix (Fin n) (Fin n) _) b a)]
  beta_reduce

  rw [map_add (f := _), map_sum, map_sum, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have := half_trace R h (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S.1 a a) *
      (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (T.1 a a)))
    rw [map_mul, fixed_eq R h (S.2 a a), fixed_eq R h (T.2 a a)] at this
    simpa [hermCoord] using this
  · refine Finset.sum_congr rfl fun p _ => ?_
    have hT : T.1 p.1.2 p.1.1 = sigR R σ (T.1 p.1.1 p.1.2) := (T.2 p.1.2 p.1.1).symm
    have hS : S.1 p.1.2 p.1.1 = sigR R σ (S.1 p.1.1 p.1.2) := (S.2 p.1.2 p.1.1).symm
    simp only [hermCoord]
    rw [hT, hS]
    have hw : S.1 p.1.1 p.1.2 * sigR R σ (T.1 p.1.1 p.1.2) + sigR R σ (S.1 p.1.1 p.1.2) * T.1 p.1.1 p.1.2 =
        algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) (sigR R σ (S.1 p.1.1 p.1.2) * T.1 p.1.1 p.1.2)) := by
      rw [← add_sigR R h, add_comm, map_mul, sigR_sigR R h]
    rw [hw, half_trace R h]

variable [TopologicalSpace R] [IsTopologicalRing R]

end Main

end GlobalTheory.HermCoordEquiv
end
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.Corev.ThCLin

open Formalism.L2.Ker Formalism.L2.Th1.H

theorem hatS_mul_left {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (vol : ℝ) (SA : Finset V)
    (Φ : V → ℂ) (p : ℂ) (y : V) :
    hatS H vol SA (fun s => p * Φ s) y = p * hatS H vol SA Φ y := by
  simp only [hatS, mul_assoc, ← Finset.mul_sum]
  ring

theorem thC_smul_move : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA : Submodule (𝓞 E) E) (SS : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ) (p : ℂ) (Ξ : Formalism.L2.Col.HomE E a b → ℂ) (θ : Formalism.L2.Ker.VV ι a b → ℂ), Formalism.L2.Ker.thC emb δ d sc AA SS N N' c (fun x => p * Ξ x) θ = Formalism.L2.Ker.thC emb δ d sc AA SS N N' c Ξ (fun z => p * θ z) := by
  intro E _ _ _ ι _ a b emb δ d sc AA SS N N' c p Ξ θ
  have hon : onV emb δ (fun x => p * Ξ x) = fun v => p * onV emb δ Ξ v := by
    funext v
    unfold onV
    split_ifs <;> simp
  funext z
  simp only [thC, xiV, xiL, xiS, hon, hatS_mul_left, sumU, opU]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring

end GlobalTheory.Corev.ThCLin
end
