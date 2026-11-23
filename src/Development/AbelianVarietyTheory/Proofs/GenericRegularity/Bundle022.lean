module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle016
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle019
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle014
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
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

theorem _root_.GlobalTheory.T.cabs_frBor_eq_one_of_unitFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ k k' (x : (U.X k).dom) (x' : (U.X k').dom) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → FrBor t (U.un k x) (U.un k' x') → ∀ j, cabs (t (some j) : CAt σ) = 1 := by
  first | exact @GlobalTheory.FrameNormLie.cabs_diag_eq_one | exact GlobalTheory.FrameNormLie.cabs_diag_eq_one | (intros; apply GlobalTheory.FrameNormLie.cabs_diag_eq_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.exists_refined_covering_chart_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (J : Type) [Finite J] (P : J → PChart Xo c β), Covers P → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ (J' : Type) (_ : Finite J') (P' : J' → PChart Xo c β), Covers P' ∧ ∀ j, (P' j).Fam ws := by
  first | exact @GlobalTheory.Reg.exists_covers_fam | exact GlobalTheory.Reg.exists_covers_fam | (intros; apply GlobalTheory.Reg.exists_covers_fam <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.FlagDim

theorem finrank_host_div_two (D : D7) : Module.finrank ℚ D.host.E / 2 = D.R.f := by
  have h : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    push_cast
    ring
  have h' : Module.finrank ℚ D.host.E = 2 * D.R.f := by exact_mod_cast h
  omega

theorem fnFG_fnTrdeg_record : ∀ (D : D7) (Q : Par D), Q.PinDat → ∀ j, InR D j → FnFG (Q.Xo j) Q.c ∧ FnTrdeg (Q.Xo j) Q.c (WeightFamilies.dimY D j) := by
  intro D Q hP j hj
  obtain ⟨hp, hq, -⟩ := hP j hj
  have h := fnFG_fnTrdeg D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c
  rw [finrank_host_div_two] at h
  have e : WeightFamilies.dimY D j = D.R.f * ((Q.Dw j).p * (Q.Dw j).q + (Q.Dw j).p * ((Q.Dw j).p - 1) / 2 +
      (Q.Dw j).q * ((Q.Dw j).q - 1) / 2) := by
    rw [hp, hq]; rfl
  rw [e]
  exact h

end GlobalTheory.FlagDim
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

theorem _root_.GlobalTheory.T.subalgebra_eq_integralClosure_of_values_residues : ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] (ϖ : O), IsUnif A ϖ → ∀ [∀ ζ : Pts O A, IsDVRAt ζ] [Finite (Pts O A)] [Module.Finite O ↥(As O A)] (C : Subalgebra O A), C ≤ As O A → (∀ n : Pts O A → ℕ, ∃ c ∈ C, ∀ ζ, ord ϖ ζ c = (((n ζ : ℕ) : ℤ) : WithTop ℤ)) → (∀ (ζ : Pts O A), ∀ b ∈ As O A, ∃ c ∈ C, ∃ d ∈ C, ord ϖ ζ d = 0 ∧ 0 < ord ϖ ζ (d * b - c)) → As O A ≤ C := by
  first | exact @GlobalTheory.LocStructNak.as_le_of_val_of_residue | exact GlobalTheory.LocStructNak.as_le_of_val_of_residue | (intros; apply GlobalTheory.LocStructNak.as_le_of_val_of_residue <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem cuspForm_of_integral_over_cuspForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ (la : Wt X.Ψ r) (N k m : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (cf : ℕ → MvPolynomial (Fin N) ℂ) (g : Frame X.Ψ r → ℂ), (∀ i, w i ∈ X.SS la) → 0 < k → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → X.IsSec (k • la) g → (∀ x ∈ X.dom, g x * g x ^ m + ∑ i ∈ Finset.range m, (g x * MvPolynomial.eval (fun s => w s x) (cf i)) * g x ^ i = 0) → g ∈ X.SS (k • la) := by
  intro E _ _ _ r X la N k m w cf g hw hk hcf hg heq
  have hb : X.IsBddSec (k • la) g :=
    isBddSec_of_integral E r X la N k m w cf g (fun i => (hw i).1) hcf hg heq
  obtain ⟨⟨h0, hadd, hsmul⟩, -⟩ :=
    siegelSpaceAlgebra_holds (E := E) r X ((m + 1) • (k • la)) ((m + 1) • (k • la)) 0
  have hterm : ∀ i ∈ Finset.range m,
      (fun x => MvPolynomial.eval (fun s => w s x) (cf i)) * g ^ (i + 1) ∈
        X.SS ((m + 1) • (k • la)) := by
    intro i hi
    have hi' : i < m := Finset.mem_range.1 hi
    have h1 := eval_isHomogeneous_mem_cuspForms E r X la N ((m - i) * k) w (cf i) hw
      (Nat.mul_pos (Nat.sub_pos_of_lt hi') hk) (hcf i hi')
    have h2 := (bddSec_pow_succ_and_constTerm_pow_succ E r X (k • la) g hb i).1
    have h3 := (siegelSpaceAlgebra_holds (E := E) r X (((m - i) * k) • la) ((i + 1) • (k • la)) 0).2.1 _ h1 _ h2
    have e : ((m - i) * k) • la + (i + 1) • (k • la) = (m + 1) • (k • la) := by
      rw [mul_smul, ← add_smul]
      congr 1
      omega
    rwa [e] at h3
  have hsum := Finset.sum_induction _ (fun P => P ∈ X.SS ((m + 1) • (k • la)))
    (fun a b ha hb => hadd a ha b hb) h0 hterm
  have hneg := hsmul (-1) _ hsum
  refine cuspForm_of_bddSec_of_pow_succ E r X (k • la) g m hb
    ((DomCongr.bddSec_cusp_congr E r X _ _ _ fun x hx => ?_).2 hneg)
  have h := heq x hx
  have e : ∑ i ∈ Finset.range m, (g x * MvPolynomial.eval (fun s => w s x) (cf i)) * g x ^ i =
      ∑ i ∈ Finset.range m, MvPolynomial.eval (fun s => w s x) (cf i) * g x ^ (i + 1) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e] at h
  simp only [Pi.smul_apply, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  linear_combination -h

end GlobalTheory
end
