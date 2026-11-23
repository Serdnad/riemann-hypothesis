module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle001
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.WildA.prime_eq_of_mem_prime_ideal {R : Type} [CommRing R] {I : Ideal R} (hI : I.IsPrime) {a b : ℕ} (ha : a.Prime)
    (hb : b.Prime) (hai : (a : R) ∈ I) (hbi : (b : R) ∈ I) : a = b := by
  by_contra hne
  have h : Nat.Coprime a b := (Nat.coprime_primes ha hb).2 hne
  obtain ⟨u, v, e⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom R)
  apply hI.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hai) (Ideal.mul_mem_left _ _ hbi)

private theorem UpperTheory.WildA.split_of_split_class {D : D7} {p : ℕ} (h : D.host.cls p = .splitK) : GlobalTheory.NormSum.SplitIn D p := by
  right
  unfold Formalism.BasicNotions.Host.cls primeClass at h
  split_ifs at h with h1 h2 h3 h4 <;> first | exact h4 | cases h

theorem UpperTheory.WildA.small_set_primes_split :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ v ∈ G.pl.S0, ∀ l : ℕ, l.Prime → ((l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      GlobalTheory.NormSum.SplitIn D l := by
  intro D T L sc G large₂ hS v hv l hl hlv
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hS
  have key : ∀ p : ℕ, p.Prime → p ∈ D.host.levelPrimes → ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      GlobalTheory.NormSum.SplitIn D l := fun p hp hm h => by
    rw [UpperTheory.WildA.prime_eq_of_mem_prime_ideal v.isPrime hl hp hlv h]
    exact UpperTheory.WildA.split_of_split_class (Pm.level_split p hm)
  rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | h1
  · rw [UpperTheory.WildA.prime_eq_of_mem_prime_ideal G.pl.v0.isPrime hl (Formalism.L2.Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1 hlv G.pl.basePlace_over_qZero]
    exact Or.inr (Formalism.L2.Host.split_prime_jacobi_neg_d D)
  · rcases (S1_mem_OmF D).1 h1 with h | h | h | h
    · exact key _ (D.host.g_prime 0) (D.host.g_level 0) h
    · exact key _ (D.host.g_prime 1) (D.host.g_level 1) h
    · exact key _ D.host.pde_prime D.host.pde_level.1 h
    · exact key _ D.host.pde'_prime D.host.pde_level.2 h
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.halfUnit :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (p : GlobalTheory.ChiGrid.Pair T) (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P →
      ∀ c : ℕ, (∀ w ∈ P, ((c : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) →
      ∀ u ∈ pairLat G p, IsHalf e u → ∃ u' ∈ pairLat G p, IsHalf e u' ∧ c • u' = u := by
  intro D T L sc G p P e he c hc u hu hhalf
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  by_cases hc0 : c = 0
  · subst hc0
    have hS : ∑ PP ∈ P, es PP = 0 :=
      Finset.sum_eq_zero fun PP hPP => (hc PP hPP (by simp)).elim
    have hu0 : u = 0 := by
      ext i j
      have h := hhalf i j
      rw [hS, zero_mul] at h
      exact h.symm
    subst hu0
    exact ⟨0, (pairLat G p).zero_mem, fun i j => by simp, by simp⟩
  · have hx : ((c : 𝓞 D.host.E)) ≠ 0 := by exact_mod_cast hc0
    let w : AE D := (∑ PP ∈ P, es PP) * incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹
    have hw : finPart D w ∈ intAE D := by

      simp only [w, Finset.sum_mul, map_sum]
      refine AddSubgroup.sum_mem _ ?_
      intro PP hPP
      by_contra hn
      exact hc PP hPP (((hes PP hPP).2 _ hx).mpr hn)
    have h1 : incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹ * (c : AE D) = 1 := by
      rw [← map_natCast (incA D) c, ← map_mul]
      have hce : (((c : 𝓞 D.host.E) : D.host.E)) = (c : D.host.E) := by simp
      rw [hce, inv_mul_cancel₀ (by exact_mod_cast hc0), map_one]
    have hcw : (c : AE D) * w = ∑ PP ∈ P, es PP := by
      calc (c : AE D) * w
          = (∑ PP ∈ P, es PP) * (incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹ * (c : AE D)) := by
            simp only [w]; ring
        _ = ∑ PP ∈ P, es PP := by rw [h1, mul_one]
    refine ⟨w • u, GlobalTheory.LatticeStable.smul_mem_latO _ _ _ _ _ _ w hw u hu, ?_, ?_⟩
    · intro i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm _ w, mul_assoc, hhalf i j]
    · ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      rw [← mul_assoc, hcw, hhalf i j]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem lin_rat {ι κ V W : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Subfield ℂ) (b : Module.Basis ι ℂ V) (c : Module.Basis κ ℂ W) (f : V →ₗ[ℂ] W)
    (hf : ∀ i j, c.repr (f (b j)) i ∈ A) (v : V) (hv : ∀ j, b.repr v j ∈ A) (i : κ) : c.repr (f v) i ∈ A := by
  rw [← b.sum_repr v]

  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact sum_mem fun j _ => mul_mem (hv j) (hf i j)

private theorem rho_rat {ι E : Type} [Fintype ι] [Field E] {n : ℕ} (A : Subfield ℂ) (emb : ι → E →+* ℂ)
    (hA : ∀ τ x, emb τ x ∈ A) (lam : ι → DomWeight n) (g : GL (Fin n) E) (i j : VVIdx lam) :
    (bVV ℂ lam).repr (rhoVr emb lam g (bVV ℂ lam j)) i ∈ A := by
  refine actionRational_holds ℂ ι n lam A (invTrK (embGL emb g)) (fun τ a b => ?_) i j
  show ((((Formalism.UG.bc (emb τ) g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) b a ∈ A
  rw [← map_inv]
  exact hA τ _

theorem UpperTheory.WildA.ratMove :
    ∀ (D : D7) {n n' : ℕ} (lam : D.what₂.Tau → DomWeight n) (lam' : D.what₂.Tau → DomWeight n') (f f' : VV ℂ lam →ₗ[ℂ] VV ℂ lam')
      (g : GL (Fin n) D.host.E) (g' : GL (Fin n') D.host.E), f' ∘ₗ rhoVr (tauE D) lam g = rhoVr (tauE D) lam' g' ∘ₗ f →
      (∀ i j, (bVV ℂ lam').repr (f (bVV ℂ lam j)) i ∈ Set.range D.what₂.embLL) →
      ∀ i j, (bVV ℂ lam').repr (f' (bVV ℂ lam j)) i ∈ Set.range D.what₂.embLL := by
  intro D n n' lam lam' f f' g g' h hf i j
  have hlab : ∀ τ x, tauE D τ x ∈ D.what₂.embLL.fieldRange := fun τ x =>
    ⟨labLL D τ x, DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x⟩
  have e : f' (bVV ℂ lam j) = rhoVr (tauE D) lam' g' (f (rhoVr (tauE D) lam g⁻¹ (bVV ℂ lam j))) := by
    have h1 := LinearMap.congr_fun h (rhoVr (tauE D) lam g⁻¹ (bVV ℂ lam j))
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at h1
    exact h1
  rw [e]
  exact lin_rat D.what₂.embLL.fieldRange _ _ _ (rho_rat _ _ hlab lam' g') _
    (lin_rat D.what₂.embLL.fieldRange _ _ f hf _ fun k => rho_rat _ _ hlab lam g⁻¹ k j) i
end
