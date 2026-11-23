module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle612
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.ThetaFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.IwFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.TlContrOf
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem charpoly_conj_diagT {L : Type} [Field L] {n : ℕ} (g p : GL (Fin n) L) (u : Fin n → Lˣ)
    (h : g = p * GlobalTheory.SmGL.diagT L (Fin n) u * p⁻¹) : g.val.charpoly = ∏ i, (X - C (u i : L)) := by
  rw [h, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, GlobalTheory.SmGL.val_diagT, Matrix.charpoly_diagonal]

theorem s2raw (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (l : Fin (n / 2) → ℤ) (hl : Cone l) (γ : UL n w)
    (hγ : ∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0) :
    ∃ (p₀ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ),
      (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) ∧
      (p₀⁻¹ * γ * p₀).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ ∧
      (∀ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0 ↔
        ∃ z ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ i ∈ iwU n w b, p = z * p₀ * i) ∧
      cptPart (twCent (MonoidHom.id (UL n w)) γ) =
        twCent (MonoidHom.id (UL n w)) γ ⊓ (iwU n w b).map (MulAut.conj p₀).toMonoidHom ∧
      γ.1.val.charpoly = ∏ i, (X - C (u i : w.adicCompletion E)) := by
  obtain ⟨p₀, u, h1, h2, h3, h4⟩ := GlobalTheory.T.dominant_coset_twisted_conjugacy E hU w hw n b hb ϖ hϖ l hl
    (fun y hy δ hδ => contr_id_pf w ϖ hϖ n y hy δ hδ) γ hγ
  refine ⟨p₀, u, h1, h2, h3, h4, charpoly_conj_diagT _ (p₀.1 * b) u ?_⟩
  have : γ.1 = p₀.1 * (p₀⁻¹ * γ * p₀).1 * p₀.1⁻¹ := by simp [mul_assoc]
  rw [this, h2]
  group

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
end
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem iwahori_unitary_involution_admissible (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) :
    PositivityTheory.Lbc.admitted (w.adicCompletion E) n (iwGL n w) (thLAut w hw n) 2 :=
  ⟨iw_isOpen n, iw_isCompact n, iw_hasIwahoriFact n, continuous_thLAut w hw n, two_pos, thLAut_sq w hw n,
    thLAut_map_iwGL w hw n, thLAut_map_Nup w hw n, thLAut_map_Nlo w hw n, thLAut_map_Tor w hw n⟩

theorem contr_tw_tl (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (n : ℕ)
    (y : Fin n → ℤ) (hy : StrictAnti y) (δ : GLw n w) (hδ : dcos n w (tdiag ϖ y) δ ≠ 0) :
    ∃ m ∈ iwGL n w, ∃ τ ∈ TO n w, m⁻¹ * δ * thL n w m = tdiag ϖ y * τ :=
  tl_contr_of w ϖ hϖ.1 n (thLAut w hw n) (iwahori_unitary_involution_admissible w hw n) y hy (thL_tdiag w hw ϖ hϖ.2 n y) δ hδ

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
end
end
