module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwise
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelDoubleStepOfFlatColumnFlatRow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle031
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.ParHeckeCap

theorem val_mul_lt_left {k : Type} [Field k] [ValuativeRel k] {X Y Z : Type} [Fintype Y] (c : Matrix X Y k)
    (w : Matrix Y Z k) (hc : ∀ i j, valuation k (c i j) < 1) (hw : ∀ i j, valuation k (w i j) ≤ 1) :
    ∀ i j, valuation k ((c * w) i j) < 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (hw l j)) (hc i l)

theorem val_mul_lt_right {k : Type} [Field k] [ValuativeRel k] {X Y Z : Type} [Fintype Y] (w : Matrix X Y k)
    (c : Matrix Y Z k) (hw : ∀ i j, valuation k (w i j) ≤ 1) (hc : ∀ i j, valuation k (c i j) < 1) :
    ∀ i j, valuation k ((w * c) i j) < 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hw i l)) (hc l j)

theorem toBlocks₂₁_mul_mul {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (P E Q : Matrix (A ⊕ D) (A ⊕ D) k) (hP : P.toBlocks₂₁ = 0) (hE : E.toBlocks₂₁ = 0)
    (hQ : Q.toBlocks₂₁ = 0) : (P * E * Q).toBlocks₂₁ = 0 := by
  rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks E, ← fromBlocks_toBlocks Q, hP, hE, hQ]
  simp [fromBlocks_multiply]

theorem lowUni_mul_toBlocks₂₁ {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (X : Matrix D A k) (M : Matrix (A ⊕ D) (A ⊕ D) k) :
    (fromBlocks 1 0 X 1 * M).toBlocks₂₁ = X * M.toBlocks₁₁ + M.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [fromBlocks_multiply]

theorem mul_lowUni_toBlocks₂₁ {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (X : Matrix D A k) (M : Matrix (A ⊕ D) (A ⊕ D) k) :
    (M * fromBlocks 1 0 X 1).toBlocks₂₁ = M.toBlocks₂₁ + M.toBlocks₂₂ * X := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [fromBlocks_multiply]

theorem lowerUni_mem_cap : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (g : GL (A ⊕ D) k) (ν : Matrix D A k)
    (m : GL D k), g.1 = fromBlocks 1 0 ν m.1 →
    (∃ x y, ∃ j ∈ parahoric k A D, ∃ j' ∈ parahoric k A D, g = j * emb₂ k (Equiv.refl (A ⊕ D)) (x, y) * j') →
    ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧
      ν = ν₁ + m.1 * ν₂ := by
  intro k _ _ _ _ A D _ _ _ _ g ν m hg ⟨x, y, j, hj, j', hj', he⟩
  obtain ⟨⟨u, hu, hua⟩, -, hc, -⟩ := (GlobalTheory.ParahoricConjBlocks.mem_parahoric_val_iff j.1).1 ⟨j, hj, rfl⟩
  obtain ⟨-, -, hc', ⟨u', hu', hud⟩⟩ := (GlobalTheory.ParahoricConjBlocks.mem_parahoric_val_iff j'.1).1 ⟨j', hj', rfl⟩
  have hui := ((GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff (u⁻¹).1).1 ⟨u⁻¹, inv_mem hu, rfl⟩).1
  have hui' := ((GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff (u'⁻¹).1).1 ⟨u'⁻¹, inv_mem hu', rfl⟩).1
  set ν₁ := j.1.toBlocks₂₁ * (u⁻¹).1
  set ν₂ := (u'⁻¹).1 * j'.1.toBlocks₂₁
  refine ⟨ν₁, ν₂, val_mul_lt_left _ _ hc hui, val_mul_lt_right _ _ hui' hc', ?_⟩
  have hP : (fromBlocks 1 0 (-ν₁) 1 * j.1).toBlocks₂₁ = 0 := by
    have e1 : ν₁ * u.1 = j.1.toBlocks₂₁ := by simp only [ν₁, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [lowUni_mul_toBlocks₂₁, ← hua, Matrix.neg_mul, e1, neg_add_cancel]
  have hQ : (j'.1 * fromBlocks 1 0 (-ν₂) 1).toBlocks₂₁ = 0 := by
    have e2 : u'.1 * ν₂ = j'.1.toBlocks₂₁ := by simp only [ν₂, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [mul_lowUni_toBlocks₂₁, ← hud, Matrix.mul_neg, e2, add_neg_cancel]
  have hE : (emb₂ k (Equiv.refl (A ⊕ D)) (x, y)).1.toBlocks₂₁ = 0 := by
    rw [val_emb₂]
    simp
  have key := toBlocks₂₁_mul_mul _ _ _ hP hE hQ
  have h2 : fromBlocks 1 0 (-ν₁) 1 * j.1 * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y)).1 *
      (j'.1 * fromBlocks 1 0 (-ν₂) 1) = fromBlocks 1 0 (-ν₁) 1 * g.1 * fromBlocks 1 0 (-ν₂) 1 := by
    rw [he]
    simp only [Units.val_mul, Matrix.mul_assoc]
  rw [h2, hg] at key
  simp [fromBlocks_multiply] at key
  rw [← sub_eq_zero, ← key]
  abel

end GlobalTheory.ParHeckeCap
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symData_oneIndex_of_oneClass_of_supportOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneClass t ν → S.SupportOne t → S.OneIndex t ν := by
  first | exact @GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne | exact GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne | (intros; apply GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.flatColumnSupport_of_oneIndexAt_symPosition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneIndexAt t ν → GlobalTheory.LocFlat.SuppCol S t ν := by
  first | exact @GlobalTheory.LocFlat.suppCol_of_oneIndexAt | exact GlobalTheory.LocFlat.suppCol_of_oneIndexAt | (intros; apply GlobalTheory.LocFlat.suppCol_of_oneIndexAt <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.flatRowIndicator_of_symLevelExchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν → GlobalTheory.LocFlat.PureRow S t ν := by
  first | exact @GlobalTheory.LocFlat.pureRow_of_exchange | exact GlobalTheory.LocFlat.pureRow_of_exchange | (intros; apply GlobalTheory.LocFlat.pureRow_of_exchange <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symLevel_doubleStep_of_flatColumn_flatRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.OneIndexAt t ν → GlobalTheory.LocFlat.PureCol S t ν → GlobalTheory.LocFlat.PureRow S t ν → GlobalTheory.LocFlat.DoubleStep S t ν := by
  first | exact @GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow | exact GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow | (intros; apply GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.linearMap_kills_partialEvalIntegralKernel_of_laws : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it : Finset (m × m')), Disjoint ev it → (∀ (b : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (∑ e ∈ ev, b e * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ (a : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + ∑ e ∈ it, Matrix.single e.1 e.2 (a e))) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev it β l := by
  first | exact @GlobalTheory.FlatFactor.KerEngine.kerRed_of_laws | exact GlobalTheory.FlatFactor.KerEngine.kerRed_of_laws | (intros; apply GlobalTheory.FlatFactor.KerEngine.kerRed_of_laws <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ZonalBi

theorem zonalInt_biInvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ κ ∈ KO k (Fin N), ∀ m, zonalInt μK ψ (κ * m) = zonalInt μK ψ m ∧ zonalInt μK ψ (m * κ) = zonalInt μK ψ m := by
  intro k _ _ _ _ N _ _ μK _ hK ψ hψ κ₀ hκ₀ m
  have hKo : IsOpen (KO k (Fin N) : Set (GL (Fin N) k)) := GlobalTheory.SplitFlip.isOpen_KO
  have hKc : IsCompact (KO k (Fin N) : Set (GL (Fin N) k)) := GlobalTheory.SplitFlip.isCompact_KO
  have hKcl : IsClosed (KO k (Fin N) : Set (GL (Fin N) k)) := Subgroup.isClosed_of_isOpen _ hKo
  have hKfr : frontier (KO k (Fin N) : Set (GL (Fin N) k)) = ∅ := (IsClopen.frontier_eq ⟨hKcl, hKo⟩)
  have hKm : MeasurableSet (KO k (Fin N) : Set (GL (Fin N) k)) := hKo.measurableSet
  have hψc : Continuous ψ := by
    refine continuous_iff_continuousAt.2 fun g => ?_
    have hmem : (fun y => g⁻¹ * y) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k)) ∈ nhds g :=
      (hKo.preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp [one_mem])
    have hev : ∀ᶠ y in nhds g, ψ y = ψ g := by
      filter_upwards [hmem] with y hy
      have := hψ g (g⁻¹ * y) hy
      rwa [mul_inv_cancel_left] at this
    exact tendsto_nhds_of_eventually_eq hev
  refine ⟨?_, ?_⟩
  · set ν : Measure (GL (Fin N) k) := Measure.map (· * κ₀) μK with hν
    set c := Measure.haarScalarFactor ν μK with hc
    have L : ∀ f : GL (Fin N) k → ℝ, Continuous f → HasCompactSupport f →
        ∫ x, f x ∂ν = ∫ x, f x ∂(c • μK) := fun f hf hs =>
      Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport ν μK hf hs
    have hpre : (· * κ₀) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k)) = KO k (Fin N) := by
      ext x; simp [Subgroup.mul_mem_cancel_right _ hκ₀]
    have hc1 : c = 1 := by
      have h1 := L ((KO k (Fin N) : Set (GL (Fin N) k)).indicator 1)
        (continuous_indicator (by simp [hKfr]) continuous_one.continuousOn)
        (HasCompactSupport.intro hKc fun x hx => by simp [hx])
      rw [integral_indicator_one hKm, integral_indicator_one hKm] at h1
      simp only [Measure.real, hν, Measure.map_apply (measurable_mul_const κ₀) hKm, hpre, Measure.smul_apply, hK] at h1
      simpa using h1.symm
    set F : GL (Fin N) k → ℂ := (KO k (Fin N) : Set (GL (Fin N) k)).indicator fun x => ψ (x * m) with hFdef
    have hF : Continuous F :=
      continuous_indicator (by simp [hKfr]) (hψc.comp (continuous_mul_const m)).continuousOn
    have hFs : HasCompactSupport F := HasCompactSupport.intro hKc fun x hx => by simp [F, hx]
    have e1 : zonalInt μK ψ (κ₀ * m) = ∫ x, F (x * κ₀) ∂μK := by
      unfold zonalInt
      rw [← integral_indicator hKm]
      congr 1; funext x
      by_cases hx : x ∈ KO k (Fin N)
      · have hx' : x * κ₀ ∈ KO k (Fin N) := mul_mem hx hκ₀
        rw [hFdef, Set.indicator_of_mem (SetLike.mem_coe.2 hx), Set.indicator_of_mem (SetLike.mem_coe.2 hx'), mul_assoc]
      · have hx' : x * κ₀ ∉ KO k (Fin N) := fun h => hx ((Subgroup.mul_mem_cancel_right _ hκ₀).1 h)
        rw [hFdef, Set.indicator_of_notMem (fun h => hx (SetLike.mem_coe.1 h)),
          Set.indicator_of_notMem (fun h => hx' (SetLike.mem_coe.1 h))]
    have e2 : zonalInt μK ψ m = ∫ x, F x ∂μK := by
      unfold zonalInt; rw [← integral_indicator hKm]
    have e3 : ∫ x, F (x * κ₀) ∂μK = ∫ x, F x ∂ν :=
      (integral_map (measurable_mul_const κ₀).aemeasurable hF.aestronglyMeasurable).symm
    have hIν : Integrable F ν := hF.integrable_of_hasCompactSupport hFs
    have hIμ : Integrable F μK := hF.integrable_of_hasCompactSupport hFs
    have Lre := L (fun x => (F x).re) (Complex.continuous_re.comp hF) (hFs.comp_left Complex.zero_re)
    have Lim := L (fun x => (F x).im) (Complex.continuous_im.comp hF) (hFs.comp_left Complex.zero_im)
    rw [hc1, one_smul] at Lre Lim
    have e4 : ∫ x, F x ∂ν = ∫ x, F x ∂μK := by
      apply Complex.ext
      · have a := integral_re hIν
        have b := integral_re hIμ
        simp only [RCLike.re_to_complex] at a b
        rw [← a, ← b, Lre]
      · have a := integral_im hIν
        have b := integral_im hIμ
        simp only [RCLike.im_to_complex] at a b
        rw [← a, ← b, Lim]
    rw [e1, e3, e4, e2]
  · unfold zonalInt
    congr 1; funext κ
    rw [← mul_assoc, hψ _ _ hκ₀]

end GlobalTheory.ZonalBi
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ZonalEig

theorem zonalInt_eig : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ (R : Finset (GL (Fin N) k)) (c : ℂ), (∀ m, ∑ g ∈ R, ψ (m * g) = c * ψ m) → ∀ m, ∑ g ∈ R, zonalInt μK ψ (m * g) = c * zonalInt μK ψ m := by
  intro k _ _ _ _ N _ _ μK _ hμ ψ hψ R c hR m
  have hKo := (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin N))
  have hcont : Continuous ψ := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_)
    have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k))) := hKo.preimage (by fun_prop)
    filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ (KO k (Fin N) : Set (GL (Fin N) k)) by
      rw [inv_mul_cancel]; exact one_mem _)] with x hx
    have := hψ g _ hx
    rwa [mul_inv_cancel_left] at this
  have hint : ∀ y, IntegrableOn (fun κ => ψ (κ * y)) (KO k (Fin N) : Set (GL (Fin N) k)) μK := fun y =>
    (hcont.comp (continuous_mul_const y)).continuousOn.integrableOn_compact GlobalTheory.SplitFlip.isCompact_KO
  simp only [zonalInt]
  rw [← integral_finsetSum _ (fun g _ => hint (m * g)), ← integral_const_mul]
  congr 1
  funext κ
  have := hR (κ * m)
  simpa only [mul_assoc] using this

end GlobalTheory.ZonalEig
end
end

section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.LatticePair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def IsInt (A : GL (Fin n) k) : Prop := ∀ i j, A.1 i j ∈ 𝒪[k]

theorem isInt_mul {A B : GL (Fin n) k} (hA : IsInt A) (hB : IsInt B) : IsInt (A * B) := fun i j => by
  rw [Units.val_mul, Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem isInt_mul_KO_iff {A κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) : IsInt (A * κ) ↔ IsInt A := by
  have h := (SplitFlip.mem_KO_iff κ).1 hκ
  refine ⟨fun hA => ?_, fun hA => isInt_mul hA h.1⟩
  have := isInt_mul hA h.2
  rwa [mul_inv_cancel_right] at this

theorem isInt_KO_mul_iff {A κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) : IsInt (κ * A) ↔ IsInt A := by
  have h := (SplitFlip.mem_KO_iff κ).1 hκ
  refine ⟨fun hA => ?_, fun hA => isInt_mul h.1 hA⟩
  have := isInt_mul h.2 hA
  rwa [inv_mul_cancel_left] at this

theorem ord_det_of_mem_KO {κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) :
    ord k (Matrix.GeneralLinearGroup.det κ) = 0 := by
  obtain ⟨u, rfl⟩ := hκ
  apply ord_eq_zero
  have h1 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) =
      algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det u : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

theorem ord_det_mul (a b : GL (Fin n) k) : ord k (Matrix.GeneralLinearGroup.det (a * b)) =
    ord k (Matrix.GeneralLinearGroup.det a) + ord k (Matrix.GeneralLinearGroup.det b) := by
  rw [map_mul, ord_mul]

theorem ord_det_inv (a : GL (Fin n) k) : ord k (Matrix.GeneralLinearGroup.det a⁻¹) =
    -ord k (Matrix.GeneralLinearGroup.det a) := by
  have := ord_det_mul a a⁻¹
  rw [mul_inv_cancel, map_one, ord_eq_zero (x := 1) (by simp)] at this
  omega

theorem valuation_det_le_one {A : GL (Fin n) k} (hA : IsInt A) :
    valuation k ((Matrix.GeneralLinearGroup.det A : kˣ) : k) ≤ 1 := by
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨A.1 i j, hA i j⟩
  have hB : (algebraMap 𝒪[k] k).mapMatrix B = A.1 := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← hB, ← RingHom.map_det]
  exact B.det.2

theorem ord_nonneg_of_le_one {x : kˣ} (hx : valuation k (x : k) ≤ 1) : 0 ≤ ord k x := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (x : k)) ≠ 0 := by simp
  have h1 : φ (valuation k (x : k)) ≤ φ 1 := φ.strictMono.monotone hx
  rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  show 0 ≤ -WithZero.log (φ (valuation k (x : k)))
  omega

theorem ord_det_torusElt {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin n → ℤ) :
    ord k (Matrix.GeneralLinearGroup.det (torusElt k (Fin n) ϖ e)) = ∑ i, e i := by
  have h1 : Matrix.GeneralLinearGroup.det (torusElt k (Fin n) ϖ e) = ϖ ^ ∑ i, e i := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, val_torusElt, Matrix.det_diagonal, Units.val_zpow_eq_zpow_val]
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp
    | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ ϖ.ne_zero, ih]
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have := map_zpow o ϖ (∑ i, e i)
  rw [show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd (ord_eq_one hϖ), ← ofAdd_zsmul,
    smul_eq_mul, mul_one, ← h1] at this
  exact this

theorem isInt_and_mul_torus_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (A : GL (Fin n) k)
    (e : Fin n → ℤ) : IsInt A ∧ IsInt (A * torusElt k (Fin n) ϖ e) ↔
      IsInt (A * torusElt k (Fin n) ϖ fun i => min (e i) 0) := by
  have hle : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  have hpow : ∀ m : ℤ, 0 ≤ m → (ϖ : k) ^ m ∈ 𝒪[k] := fun m hm => by
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [zpow_natCast]
    exact pow_mem hle m
  have hent : ∀ (f : Fin n → ℤ) i j, (A * torusElt k (Fin n) ϖ f).1 i j = A.1 i j * (ϖ : k) ^ f j :=
    fun f i j => by rw [Units.val_mul, val_torusElt, Matrix.mul_diagonal]
  have key : ∀ (x : k) (m : ℤ), (x ∈ 𝒪[k] ∧ x * (ϖ : k) ^ m ∈ 𝒪[k]) ↔ x * (ϖ : k) ^ min m 0 ∈ 𝒪[k] := by
    intro x m
    have hz : (ϖ : k) ≠ 0 := ϖ.ne_zero
    rcases le_total m 0 with h | h
    · rw [min_eq_left h]
      refine ⟨And.right, fun h2 => ⟨?_, h2⟩⟩
      have : x = x * (ϖ : k) ^ m * (ϖ : k) ^ (-m) := by
        rw [mul_assoc, ← zpow_add₀ hz, add_neg_cancel, zpow_zero, mul_one]
      rw [this]
      exact mul_mem h2 (hpow _ (by omega))
    · rw [min_eq_right h, zpow_zero, mul_one]
      exact ⟨And.left, fun h2 => ⟨h2, mul_mem h2 (hpow _ h)⟩⟩
  simp only [IsInt, hent]
  constructor
  · rintro ⟨h1, h2⟩ i j
    exact (key _ _).1 ⟨h1 i j, h2 i j⟩
  · intro h
    exact ⟨fun i j => ((key _ _).2 (h i j)).1, fun i j => ((key _ _).2 (h i j)).2⟩

theorem out_eq_mul {r : GL (Fin n) k} {c : GL (Fin n) k ⧸ KO k (Fin n)}
    (h : (r : GL (Fin n) k ⧸ KO k (Fin n)) = c) : ∃ κ ∈ KO k (Fin n), c.out = r * κ := by
  subst h
  obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) r
  exact ⟨κ, κ.2, hκ⟩

theorem smul_out (u : GL (Fin n) k) (c : GL (Fin n) k ⧸ KO k (Fin n)) :
    ∃ κ ∈ KO k (Fin n), (u • c).out = u * c.out * κ := by
  apply out_eq_mul
  conv_rhs => rw [← QuotientGroup.out_eq' c]
  rfl

theorem hasSum_pair (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin n → ℤ) (g : GL (Fin n) k)
    (hg : g ∈ cell k (Fin n) ϖ e) (X : ℂ) (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1) :
    HasSum (fun h : {h : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
        (∀ i j, (h.out⁻¹ * g : GL (Fin n) k).1 i j ∈ 𝒪[k])} =>
      X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.1.out)).toNat +
        (ord k (Matrix.GeneralLinearGroup.det (h.1.out⁻¹ * g))).toNat))
      (X ^ (∑ i, |e i|).toNat * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) := by
  obtain ⟨x, hx, y, hy, hgxy⟩ := DoubleCoset.mem_doubleCoset.1 hg
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin n) k, u = x * torusElt k (Fin n) ϖ fun i => min (e i) 0 := ⟨_, rfl⟩
  have hP : ∀ h : GL (Fin n) k, (IsInt h⁻¹ ∧ IsInt (h⁻¹ * g)) ↔ IsInt (h⁻¹ * u) := fun h => by
    rw [hgxy, hu, ← mul_assoc, ← mul_assoc, ← mul_assoc, isInt_mul_KO_iff hy, ← isInt_and_mul_torus_iff hϖ,
      isInt_mul_KO_iff hx]
  let E : {c : GL (Fin n) k ⧸ KO k (Fin n) // ∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]} ≃
      {h : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
        (∀ i j, (h.out⁻¹ * g : GL (Fin n) k).1 i j ∈ 𝒪[k])} :=
    (MulAction.toPerm u).subtypeEquiv fun c => by
      obtain ⟨κ, hκ, h⟩ := smul_out u c
      refine Iff.trans ?_ (hP (u • c).out).symm
      have : (u * c.out * κ)⁻¹ * u = κ⁻¹ * c.out⁻¹ := by group
      rw [h, this, isInt_KO_mul_iff (inv_mem hκ)]
      rfl
  have hN := (GlobalTheory.T.hasSum_hecke_series_spherical_integral_inverse k n (fun _ => 1) (fun _ => 1) (isBorelSph_one k) (fun _ => one_ne_zero) (X ^ 2)
    fun i => by simpa only [inv_one, mul_one] using hX i).mul_left (X ^ (∑ i, |e i|).toNat)
  simp only [inv_one, mul_one] at hN
  rw [← E.hasSum_iff]
  refine (congrArg (HasSum · _) (funext fun c => ?_)).mpr hN
  obtain ⟨κ, hκ, h⟩ := smul_out u c.1
  have hE : (E c).1.out = u * c.1.out * κ := h
  have hj := ord_nonneg_of_le_one (valuation_det_le_one (A := c.1.out⁻¹) c.2)
  have habs : ∑ i, |e i| = ∑ i, e i - 2 * ∑ i, min (e i) 0 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_eq_max_neg]
    omega
  have h1 : ∑ i, min (e i) 0 ≤ 0 := Finset.sum_nonpos fun i _ => min_le_right _ _
  have h2 : ∑ i, min (e i) 0 ≤ ∑ i, e i := Finset.sum_le_sum fun i _ => min_le_left _ _
  have hou : ord k (Matrix.GeneralLinearGroup.det u) = ∑ i, min (e i) 0 := by
    rw [hu, ord_det_mul, ord_det_of_mem_KO hx, ord_det_torusElt hϖ, zero_add]
  have hog : ord k (Matrix.GeneralLinearGroup.det g) = ∑ i, e i := by
    rw [hgxy, ord_det_mul, ord_det_mul, ord_det_of_mem_KO hx, ord_det_of_mem_KO hy, ord_det_torusElt hϖ,
      zero_add, add_zero]
  rw [ord_det_inv] at hj
  simp only [Function.comp_apply]
  rw [ord_det_mul, ord_det_inv, hE, ord_det_mul, ord_det_mul, ord_det_of_mem_KO hκ, hou, hog,
    ← pow_mul, ← pow_add, habs]
  congr 1
  omega

end GlobalTheory.LatticePair
end
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory

theorem omegaK_quadratic : ∀ d : ℕ, d % 4 = 3 → omegaK d ^ 2 - omegaK d + (((d + 1) / 4 : ℕ) : ℂ) = 0 := by
  intro d hd
  have h4 : 4 ∣ d + 1 := by omega
  obtain ⟨k, hk⟩ := h4
  have hk' : (d + 1) / 4 = k := by omega
  rw [hk']
  have hdk : (d : ℂ) = 4 * k - 1 := by
    have : ((d + 1 : ℕ) : ℂ) = ((4 * k : ℕ) : ℂ) := by rw [hk]
    push_cast at this
    linear_combination this
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  unfold omegaK
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-(1:ℂ)/4) * hs + ((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4 * hI - (1/4 : ℂ) * hdk
end GlobalTheory
end
