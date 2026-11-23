module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveHermitianPolynomial
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalFormL2Mem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDiagUnit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle481
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle587
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle576
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle483
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdmissibleLinearFunctional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle588
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle589
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle596
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle403

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

theorem _root_.GlobalTheory.T.exists_polynomial_chinese_remainder : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q, ∃ m : E[X], ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → (AdjoinRoot.mk Q.1 m : Fld Q) = g r Q := by
  first | exact @GlobalTheory.CompanionTheory.EllCRT.main | exact GlobalTheory.CompanionTheory.EllCRT.main | (intros; apply GlobalTheory.CompanionTheory.EllCRT.main <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

theorem _root_.GlobalTheory.T.involution_compatible_polynomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m) := by
  first | exact @GlobalTheory.CompanionTheory.HermFixed.main | exact GlobalTheory.CompanionTheory.HermFixed.main | (intros; apply GlobalTheory.CompanionTheory.HermFixed.main <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

theorem _root_.GlobalTheory.T.positive_hermitian_polynomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ u : InfinitePlace (maximalRealSubfield E), ∃ z : (u.Completion ⊗[(maximalRealSubfield E)] Fld Q)ˣ, (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q u.Completion (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : Fld Q)) → ∀ τ : E →+* ℂ, ∃ Q' : Matrix (Fin n) (Fin n) ℂ, Q'.det ≠ 0 ∧ (H₀ * aeval γ₀.val m).map τ = cT (starRingEnd ℂ) Q' * Q' := by
  first | exact @GlobalTheory.CompanionTheory.PosDefNorm.main | exact GlobalTheory.CompanionTheory.PosDefNorm.main | (intros; apply GlobalTheory.CompanionTheory.PosDefNorm.main <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.irreducible_cuspidal_form_l2_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ W : Submodule ℂ (Sm E a), _root_.GlobalTheory.CuspRep.IsStable W → (∀ φ ∈ W, IsAutForm φ ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) → (classes W μ).topologicalClosure = H → ∀ φ : Sm E a, IsAutForm φ → ∀ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H → φ ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.IrredMod.mem_of_toL2_mem | exact GlobalTheory.CompanionTheory.IrredMod.mem_of_toL2_mem | (intros; apply GlobalTheory.CompanionTheory.IrredMod.mem_of_toL2_mem <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.UnitaryContraction

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_zpow (x : Lˣ) (k : ℤ) : ordL ((x ^ k : Lˣ) : L) = k * ordL (x : L) := by
  have h0 : Valued.v (x : L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.1 h0
  have hk : Valued.v ((x ^ k : Lˣ) : L) = ((a ^ k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← ha, WithZero.coe_zpow]
  rw [UnitaryCorrection.ordL_of_eq hk, UnitaryCorrection.ordL_of_eq ha.symm, toAdd_zpow]
  simp

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem diagT_mem_iwGL (w : Pl E) (n : ℕ) (s : Fin n → (w.adicCompletion E)ˣ)
    (hs : ∀ i, Valued.v (s i : w.adicCompletion E) = 1) :
    GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s ∈ iwGL n w := by
  have hle : ∀ t : Fin n → (w.adicCompletion E)ˣ, (∀ i, Valued.v (t i : w.adicCompletion E) = 1) →
      ∀ i j, Valued.v ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) t).val i j) ≤ 1 := by
    intro t ht i j
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, ht]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero]
      exact zero_le_one
  rw [(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1]
  refine ⟨hle s hs, ?_, ?_⟩
  · rw [← map_inv]
    refine hle _ fun i => ?_
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hs, inv_one]
  · intro i j hij
    rw [GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_ne _ (ne_of_gt hij), map_zero]
    exact zero_lt_one

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → (∀ (y : Fin n → ℤ), StrictAnti y → ∀ δ : GLw n w, dcos n w (tdiag ϖ y) δ ≠ 0 → ∃ m ∈ iwGL n w, ∃ τ : GLw n w, ((∀ i j : Fin n, i ≠ j → τ.val i j = 0) ∧ ∀ i, Valued.v (τ.val i i) = 1) ∧ m⁻¹ * δ * m = tdiag ϖ y * τ) → ∀ γ : UL n w, fU n w b ϖ l γ ≠ 0 → ∃ m ∈ iwU n w b, ∃ u : Fin n → (w.adicCompletion E)ˣ, (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) ∧ (m⁻¹ * γ * m).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl hyp γ hγ
  obtain ⟨-, hcc, hcv, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨hW1, hW2, -, -⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  obtain ⟨hanti, hrev⟩ := GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl
  have hγ' : ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b,
      γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 := by
    by_contra h
    exact hγ (if_neg h)
  obtain ⟨x, hx, z, hz, e⟩ := hγ'
  obtain ⟨δ, hδ⟩ : ∃ δ : GLw n w, δ = b⁻¹ * γ.1 * b := ⟨_, rfl⟩
  have hγδ : γ.1 = b * δ * b⁻¹ := by rw [hδ]; group
  have hδd : dcos n w (tdiag ϖ (wexp n l)) δ ≠ 0 := by
    have h : ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, δ = x * tdiag ϖ (wexp n l) * z :=
      ⟨_, (hW2 x).1 hx, _, (hW2 z).1 hz, by rw [hδ, e]; group⟩
    simp only [dcos, if_pos h]
    exact one_ne_zero
  have hδU : δ ∈ UJ (cj w) (antiJ (w.adicCompletion E) n) :=
    (hW1 δ).1 (by rw [← hγδ]; exact γ.2)
  obtain ⟨m0, hm0, τ, ⟨hτ0, hτ1⟩, hmτ⟩ := hyp (wexp n l) hanti δ hδd
  have hne : ∀ i, τ.val i i ≠ 0 := fun i h => by
    have := hτ1 i
    rw [h, map_zero] at this
    exact zero_ne_one this
  obtain ⟨v, hv⟩ : ∃ v : Fin n → (w.adicCompletion E)ˣ, ∀ i, (v i : w.adicCompletion E) = τ.val i i :=
    ⟨fun i => Units.mk0 _ (hne i), fun i => rfl⟩
  have hτv : τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) v := by
    apply Units.ext
    rw [GlobalTheory.SmGL.val_diagT]
    ext i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, hv]
    · rw [Matrix.diagonal_apply_ne _ h, hτ0 i j h]
  obtain ⟨u, hu⟩ : ∃ u : Fin n → (w.adicCompletion E)ˣ, u = fun i => ϖ ^ wexp n l i * v i := ⟨_, rfl⟩
  have htu : tdiag ϖ (wexp n l) * τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by
    rw [hτv, hu, tdiag, ← map_mul]
    rfl
  have hord : ∀ i, ordL (u i : w.adicCompletion E) = wexp n l i := by
    intro i
    rw [hu]
    simp only [Units.val_mul]
    rw [UnitaryCorrection.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _), ordL_zpow, hϖ.1,
      UnitaryCorrection.ordL_congr (b := (1 : w.adicCompletion E)) (by rw [hv, hτ1, map_one]),
      UnitaryCorrection.ordL_one]
    simp
  have hm0e := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n m0).1.1 hm0
  have hδe : m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * m0⁻¹ = δ := by
    rw [← htu, ← hmτ]
    group
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.CompanionTheory.UnitaryCorrection.main (w.adicCompletion E) (cj w) hcc hcv
    (GlobalTheory.T.norm_one_unit_hilbert_ninety E hU w hw) n (wexp n l) hanti.injective hrev u hord m0 hm0e.1 hm0e.2.1
    (by rw [hδe]; exact hδU)
  have hm1 : m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s ∈ iwGL n w :=
    mul_mem hm0 (diagT_mem_iwGL w n s hs1)
  have hcomm : (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s)⁻¹ *
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s =
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    funext i
    simp [mul_comm]
  refine ⟨⟨b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹, (hW1 _).2 hs2⟩,
    (hW2 _).2 ?_, u, hord, ?_⟩
  · have : b⁻¹ * (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) * b =
        m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s := by group
    change b⁻¹ * (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) * b ∈ iwGL n w
    rw [this]
    exact hm1
  · change (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹)⁻¹ * γ.1 *
      (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) = _
    rw [hγδ]
    have hd : m0⁻¹ * δ * m0 = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by rw [hmτ, htu]
    calc _ = b * ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s)⁻¹ * (m0⁻¹ * δ * m0) *
          GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹ := by group
      _ = _ := by rw [hd, hcomm]

end GlobalTheory.CompanionTheory.UnitaryContraction
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitary_iwahori_orbital_support : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → ∀ (γ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) → γ.1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ → ∀ x ∈ iwU n w b, ∀ z ∈ iwU n w b, fU n w b ϖ l (x * γ * z) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.DiagCoset.fU_diag | exact GlobalTheory.CompanionTheory.DiagCoset.fU_diag | (intros; apply GlobalTheory.CompanionTheory.DiagCoset.fU_diag <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitary_level_subgroup_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ), IsUnifAt ϖ → Cone l → IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ IsLevel (MonoidHom.id _) (KL n w) (iwU n w b) ∧ (iwU n w b).relIndex (KL n w) ≠ 0 ∧ IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  exact @GlobalTheory.CompanionTheory.IwLevels.levels_unitary
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS

theorem blk_val_det {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val.det = m.1.val.det * m.2.val.det := by
  have hdet : (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)).det = m.1.val.det * m.2.val.det := by
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  have h1 : IsUnit m.1.val.det := (Matrix.isUnit_iff_isUnit_det _).1 m.1.isUnit
  have h2 : IsUnit m.2.val.det := (Matrix.isUnit_iff_isUnit_det _).1 m.2.isUnit
  have hu : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (hdet ▸ h1.mul h2)
  simp only [blk]
  rw [dite_eq_left hu, IsUnit.unit_spec]
  exact hdet

theorem ordL_blk_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)),
    ordL (blk h w m X).val.det = ordL m.1.val.det + ordL m.2.val.det := by
  intro E _ _ _ n a b h w m X
  have h1 : IsUnit m.1.val.det := (Matrix.isUnit_iff_isUnit_det _).1 m.1.isUnit
  have h2 : IsUnit m.2.val.det := (Matrix.isUnit_iff_isUnit_det _).1 m.2.isUnit
  rw [blk_val_det, GlobalTheory.CompanionTheory.SwapInt.ordL_mul_of_ne h1.ne_zero h2.ne_zero]

end GlobalTheory.CompanionTheory.CtS
end
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS.NuVal

theorem ord_eq_ordL_unit {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : (w.adicCompletion E)ˣ) : GlobalTheory.SmGL.ord (w.adicCompletion E) x = ordL (x : w.adicCompletion E) := by
  have h : Valued.v (x : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion]
  unfold ordL
  rw [dite_eq_right h]
  congr 1
  conv_lhs => rw [← WithZero.coe_unzero h]
  first | rfl | simp [WithZero.log]

theorem unrChar_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (c : ℂˣ) (i j : ℕ) (m : GLw a w × GLw b w), ordL m.1.val.det = (i : ℤ) → ordL m.2.val.det = (j : ℤ) → (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) = (c : ℂ) ^ (i * b + j * a) := by
  intro E _ _ _ a b w c i j m h1 h2
  have hneg : GlobalTheory.SmGL.unrChar (w.adicCompletion E) c (-1) = 1 := by
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.ord_eq_zero (by simp), zpow_zero]
  have hd1 : GlobalTheory.SmGL.unrChar (w.adicCompletion E) c (GeneralLinearGroup.det m.1) = c ^ i := by
    rw [GlobalTheory.SmGL.unrChar_apply, ord_eq_ordL_unit]
    erw [h1]
    simp
  have hd2 : GlobalTheory.SmGL.unrChar (w.adicCompletion E) c (GeneralLinearGroup.det m.2) = c ^ j := by
    rw [GlobalTheory.SmGL.unrChar_apply, ord_eq_ordL_unit]
    erw [h2]
    simp
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, hneg, hd1, hd2, one_pow, one_mul, ← pow_mul, ← pow_mul,
    ← pow_add]
  simp

end GlobalTheory.CompanionTheory.CtS.NuVal
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.twCent_comm_of_charpoly_separable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E),
  (δ * thE E n δ).val.charpoly.Separable →
  ∀ a ∈ twCent (thF E n) (ratF E n δ), ∀ b ∈ twCent (thF E n) (ratF E n δ), a * b = b * a := by
  first | exact @GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm | exact GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm | (intros; apply GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.twisted_centralizer_unitary_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E) (H : Matrix (Fin n) (Fin n) E),
  (δ * thE E n δ).val.charpoly.Separable → IsUnit H.det →
  δ * thE E n δ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H →
  ∀ g : GL (Fin n) (Af E), g ∈ twCent (thF E n) (ratF E n δ) ↔
    g ∈ UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) ∧
      g * ratF E n (δ * thE E n δ) = ratF E n (δ * thE E n δ) * g := by
  first | exact @GlobalTheory.CompanionTheory.TwCentNorm.mem_twCent_ratF_iff | exact GlobalTheory.CompanionTheory.TwCentNorm.mem_twCent_ratF_iff | (intros; apply GlobalTheory.CompanionTheory.TwCentNorm.mem_twCent_ratF_iff <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

theorem _root_.GlobalTheory.T.k_finite_irreducible_fixed_vectors : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ F ∈ H, IsKFinL2 μ F → ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧ ∃ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X ∧ F ∈ X ∧ X ≤ H ∧ (∀ (k : Kinf E a), ∀ v ∈ X, R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v ∈ X) ∧ (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) ∧ ∀ B : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ, (∀ (k : Kinf E a) v, B (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (B v)) → (∀ v ∈ H, (∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) → B v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (B v) = B v) → ∀ v ∈ X, B v ∈ X := by
  first | exact @GlobalTheory.CompanionTheory.TypeSpace.exists_typeSpace | exact GlobalTheory.CompanionTheory.TypeSpace.exists_typeSpace | (intros; apply GlobalTheory.CompanionTheory.TypeSpace.exists_typeSpace <;> assumption)
end
