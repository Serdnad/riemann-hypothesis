module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLevelTypePrimeDatumLocallySmall
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle097
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PositiveTwistAverage
public import Mathlib.Algebra.Module.Lattice.Full
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
public import Mathlib.CategoryTheory.Category.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfOpENeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle047
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle051
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrbitLocallyConstant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle134
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle075
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle074
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle042
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.IndexCountS

open Formalism.L2.Col.Loc Formalism.L2.Col.LocE GlobalTheory.RowTypeInv GlobalTheory.SymLevelDatum GlobalTheory.IndexCount

theorem card_index_le_sharp : ∃ C : ℝ, 0 ≤ C ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ j, j + 2 ≤ N.R.m → (Fintype.card (I.β j) : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H j hj
  obtain ⟨hvG, -, -, hprod, -⟩ := BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  obtain ⟨⟨-, -, -, -, -, -, hX, -, -, hPr, -, -, hg, -⟩, -, -, -, -, hsh, hI, -⟩ := H
  have hq : ∀ P : HeightOneSpectrum (𝓞 X.E), Formalism.L2.Col.qOf P ≠ 0 := fun P h =>
    P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hgg : 0 < Pr.g 0 * Pr.g 1 := Nat.mul_pos (hPr.g_prime 0).pos (hPr.g_prime 1).pos
  have h1 : Fintype.card (I.β j) ≤ (Pr.g 0 * Pr.g 1) ^ (N.R.f * N.Nm ^ 2) := by
    rcases j with _ | i
    · obtain ⟨b, hb⟩ := hI.zero_uniq
      exact (Fintype.card_le_one_iff.2 fun a a' => (hb a).trans (hb a').symm).trans (Nat.one_le_pow _ _ hgg)
    · set n := N.R.N (i + 1) + cOf N.R (i + 1) with hn
      haveI : ∀ P : rowSG Pr sel mu, Finite (𝓞 X.E ⧸ P.1.asIdeal) := fun P => finite_res P.1
      let φ : I.β (i + 1) → ∀ P : rowSG Pr sel mu, Fin n × Fin n → 𝓞 X.E ⧸ P.1.asIdeal := fun b P =>
        resMat P.1 (Formalism.L2.Col.qOf P.1) (scE (N.R.N (i + 1)) fun i => i + 1) (I.h (i + 1) b P)
      have hφ : Function.Injective φ := by
        intro b b' hbb
        refine hI.inj i (by omega) b b' fun P => ?_
        have hP := hvG P.1 P.2
        have s1 := hI.stabG _ b P hP
        have s2 := hI.stabG _ b' P hP
        unfold lamYat at s1 s2
        rw [if_pos hP] at s1 s2
        refine ⟨1, Subgroup.one_mem _, (I.h (i + 1) b P)⁻¹ * I.h (i + 1) b' P, ?_, by group⟩
        unfold Jat
        rw [if_pos hP, hsh, if_pos rfl]
        exact mem_JGsym_of_cong _ _ (hq _) _ _ _ _ _ _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ s1) s2)
          (cong_of_resMat_eq _ _ (hq _) (GlobalTheory.TypePrimeUnif.intAt_div_qOf X Pr hX.ok hPr P.1 hP) s1 s2 (congrFun hbb P))
      have h2 := Nat.card_le_card_of_injective φ hφ
      have h3 : ∀ P : rowSG Pr sel mu, Nat.card (Fin n × Fin n → 𝓞 X.E ⧸ P.1.asIdeal) = Formalism.L2.Col.qOf P.1 ^ (n * n) := fun P => by
        rw [Nat.card_fun, Nat.card_prod, Nat.card_fin, Formalism.L2.Col.qOf,
          Ideal.absNorm_eq_natCard]
      rw [Nat.card_eq_fintype_card, Nat.card_pi, Finset.prod_congr rfl fun P _ => h3 P, Finset.prod_pow, hprod, ← pow_mul] at h2
      refine h2.trans (Nat.pow_le_pow_right hgg (Nat.mul_le_mul_left _ ?_))
      have h4 : n ≤ N.Nm := by
        rw [hn]
        unfold NumDatum.Nm Ranks.N cOf
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ N.R.m by omega)
        rw [hd]
        have : i + 1 + d - 1 - (i + 1) ≤ d := by omega
        nlinarith [Nat.zero_le (d * N.R.t)]
      rw [sq]
      exact Nat.mul_le_mul h4 h4
  rw [hg 0, hg 1] at h1
  have g0 : (1 : ℝ) ≤ N.g 0 := by rw [← hg 0]; exact_mod_cast (hPr.g_prime 0).one_le
  have g1 : (1 : ℝ) ≤ N.g 1 := by rw [← hg 1]; exact_mod_cast (hPr.g_prime 1).one_le
  have hT : (1 : ℝ) ≤ Pr.T u := by exact_mod_cast (hPr.T_prime u).one_le
  have gg : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 := one_le_mul_of_one_le_of_one_le g0 g1
  have ggT : (N.g 0 : ℝ) * N.g 1 ≤ (N.g 0 : ℝ) * N.g 1 * Pr.T u := le_mul_of_one_le_right (by linarith) hT
  have he : N.R.f * N.Nm ^ 2 ≤ N.R.f * (N.R.m ^ 2 * N.Nm ^ 2) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))
  calc (Fintype.card (I.β j) : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (N.R.f * N.Nm ^ 2) := by exact_mod_cast h1
    _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (N.R.f * N.Nm ^ 2) := pow_le_pow_left₀ (by linarith) ggT _
    _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (N.R.f * (N.R.m ^ 2 * N.Nm ^ 2)) := pow_le_pow_right₀ (gg.trans ggT) he
    _ = Real.exp (1 * errUnit N (Pr.T u)) := by
      rw [← Real.exp_log (show 0 < (N.g 0 : ℝ) * N.g 1 * Pr.T u by linarith), ← Real.exp_nat_mul, Real.exp_eq_exp]
      unfold errUnit
      push_cast
      ring

end GlobalTheory.Core.Ht2.IndexCountS
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open Filter Topology

noncomputable section
namespace GlobalTheory.PosOne.UniformComb
open GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage GlobalTheory.RootEx.UniformLattices

theorem comb_sum {G ι : Type} (T : Finset ι) (g : ι → G) (a : ℂ) (f : G → ℂ) :
    comb (∑ t ∈ T, Finsupp.single (g t) a) f = a * ∑ t ∈ T, f (g t) := by
  unfold comb
  rw [← Finsupp.sum_finsetSum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finsupp.sum_single_index (zero_mul _)]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem exists_comb {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure]
    (g : (n → k) → GL (n ⊕ Fin c) k) (hg : Continuous g) (hg1 : g 0 = 1)
    (hadd : ∀ a b, g (a + b) = g a * g b) (U : Subgroup (GL (n ⊕ Fin c) k)) (hU : IsOpen (U : Set (GL (n ⊕ Fin c) k)))
    (W : Submodule 𝒪[k] (n → k)) (hW : W.IsFullLattice k) :
    ∃ e : GL (n ⊕ Fin c) k →₀ ℂ, ∀ f : GL (n ⊕ Fin c) k → ℂ,
      (∀ x b, g b ∈ U → f (g x * g b) = f (g x)) → (∀ x, x ∉ perp ψ W → f (g x) = 0) →
      ∫ x, f (g x) ∂(Measure.pi fun _ => ν) = comb e f := by
  have := secondCountable k
  have := t2Space k
  have hV : {b : n → k | g b ∈ U} ∈ 𝓝 (0 : n → k) :=
    hg.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simp [hg1, U.one_mem]))
  obtain ⟨t, ht⟩ := exists_ballLat_subset (inter_mem hV (perp_mem_nhds hψ W hW))
  have hBl : (ballLat n t).IsFullLattice k := ballLat_isLattice t
  letI : (ballLat n t).IsFullLattice k := hBl
  have hBopen := (LatPair.isClopen_lattice (ballLat n t)).2
  obtain ⟨T, hT⟩ := exists_isReps (perp ψ W) (ballLat n t).toAddSubgroup (isCompact_perp hψ hψ1 W hW) hBopen
  refine ⟨∑ x ∈ T, Finsupp.single (g x)
    ((((Measure.pi fun _ : n => ν).real ((ballLat n t).toAddSubgroup : Set (n → k)) : ℝ) : ℂ)), fun f h1 h0 => ?_⟩
  rw [comb_sum]
  refine integral_eq_sum_reps (Measure.pi fun _ : n => ν) (fun x hx => (ht hx).2)
    hBopen (isCompact_lattice _ hBl) hT (fun x => f (g x)) h0
    fun x b hb => ?_
  simp only [hadd]
  exact h1 x b (ht hb).1

end GlobalTheory.PosOne.UniformComb

namespace GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage GlobalTheory.RootEx.UniformLattices GlobalTheory.PosOne.UniformComb

theorem exchange_eq_comb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (U : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (U : Set (GL (n ⊕ Fin c) k))), ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ, ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (∀ u ∈ U, σ u v = v) → (IsNEquiv ψ (p + 1) σ l → exDown ν p σ l v = comb e fun g => l (σ g v)) ∧ (IsNEquiv ψ p σ l → exUp ν p σ l v = comb e' fun g => l (σ g v)) := by
  intro k _ _ _ _ _ _ n _ _ c p hp hc ψ hψ hψ1 ν _ U hU
  have hrowN : {u : n → k | rowE c p u ∈ U} ∈ 𝓝 (0 : n → k) :=
    ExchangeSupport.continuous_rowE.continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by simp [ExchangeSupport.rowE_zero, U.one_mem]))
  have hcolN : {β : n → k | colE c (p + 1) β ∈ U} ∈ 𝓝 (0 : n → k) :=
    ExchangeSupport.continuous_colE.continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by simp [ExchangeSupport.colE_zero, U.one_mem]))
  obtain ⟨s, hs⟩ := exists_ballLat_subset hrowN
  obtain ⟨s', hs'⟩ := exists_ballLat_subset hcolN
  obtain ⟨e, he⟩ := exists_comb hψ hψ1 ν (colE c (p + 1)) ExchangeSupport.continuous_colE
    ExchangeSupport.colE_zero ExchangeSupport.colE_add U hU (ballLat n s) (ballLat_isLattice s)
  obtain ⟨e', he'⟩ := exists_comb hψ hψ1 ν (rowE c p) ExchangeSupport.continuous_rowE
    ExchangeSupport.rowE_zero ExchangeSupport.rowE_add U hU (ballLat n s') (ballLat_isLattice s')
  refine ⟨e, e', fun A _ _ σ hσ l v hv => ⟨fun hl => ?_, fun hl => ?_⟩⟩
  · refine he (fun g => l (σ g v)) (fun x b hb => ?_) (fun x hx => ?_)
    · simp only [map_mul, mul_apply_eq_comp, hv _ hb]
    · by_contra hne
      refine hx fun u hu => ?_
      have := ((ExchangeSupport.exchange_support k n c p hp hc ψ hψ hψ1 ν A σ hσ l v).2 hl).2 u x
      rw [hv _ (hs hu)] at this
      have h4 : (ψ (-(u ⬝ᵥ x)) : ℂ) = 1 := mul_right_cancel₀ hne (by rw [one_mul]; exact this.symm)
      rw [← inv_eq_one, ← AddChar.map_neg_eq_inv]
      exact Circle.ext (by simpa only [Circle.coe_one] using h4)
  · refine he' (fun g => l (σ g v)) (fun x b hb => ?_) (fun x hx => ?_)
    · simp only [map_mul, mul_apply_eq_comp, hv _ hb]
    · by_contra hne
      refine hx fun β hβ => ?_
      have := ((ExchangeSupport.exchange_support k n c p hp hc ψ hψ hψ1 ν A σ hσ l v).1 hl).2.1 x β
      rw [hv _ (hs' hβ)] at this
      have h4 : (ψ (x ⬝ᵥ β) : ℂ) = 1 := mul_right_cancel₀ hne (by rw [one_mul]; exact this.symm)
      rw [dotProduct_comm]
      exact Circle.ext (by simpa only [Circle.coe_one] using h4)

end GlobalTheory.PosOne
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem _root_.GlobalTheory.T.invariantIntegral_succ_position_eq_exchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B B₁ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ p σ B) (_ : ∀ Ψ v, B₁ Ψ v = exUp ν p σ (B Ψ) v) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ) (_ : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) (Rr Φ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), IsQuotInt ν μX μG (p + 1) (tInt ψ ν μ (p + 1) σ B₁ F Φ.1) (exUp ν p ρ' Rr Φ) := by
  first | exact @GlobalTheory.PosOne.RrStep.rr_step | exact GlobalTheory.PosOne.RrStep.rr_step | (intros; apply GlobalTheory.PosOne.RrStep.rr_step <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open Filter Topology

noncomputable section
namespace GlobalTheory.PosOne.FJTarget
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL)

theorem exists_isQuotInt_tInt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c p : ℕ} (hp : 1 ≤ p) (hpc : p ≤ c) {ψ : AddChar k Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (ν : Measure k) [hν : ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ))
    (μX : Measure (GL n k)) [hμX : μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [hμG : μG.IsHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} (hσ : IsSmoothRep σ)
    {B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hB : BilPos ψ μ p σ B) (F : A)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    ∃ z, IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) z := by
  have hE := (opE_SB_and_linear k n n' c p ψ hψ ν).1
  let E : GL (n ⊕ Fin c) k → SB (Matrix n n' k) := fun h =>
    ⟨opE ψ ν p (om μ 1 h Φ.1), hE _ (om_mem_SB μ 1 h Φ.2)⟩
  have hfE : ∀ h, tInt ψ ν μ p σ B F Φ.1 h = B (E h) (σ h F) := fun h => by
    unfold tInt
    rw [show opE ψ ν p (om μ 1 h Φ.1) = ((E h : SB (Matrix n n' k)) : Matrix n n' k → ℂ) from rfl,
      GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe]
  have hmul : ∀ (g h : GL (n ⊕ Fin c) k) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ),
      om μ 1 (g * h) Ψ = om μ 1 g (om μ 1 h Ψ) := fun g h Ψ => by
    rw [← om_mul, one_mul]
  refine (@GlobalTheory.QuotInt.quotInt_unique_exists k _ _ _ _ _ _ n _ _ c p hp hpc ν hν μX hμX μG hμG _).2 ?_ ?_ ?_
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro h
    have hU : IsOpen ({u : GL (n ⊕ Fin c) k | om μ 1 u Φ.1 = Φ.1} ∩ {u | σ u F = F}) :=
      ((isOpen_stabilizer_om hμ Φ.2).preimage (Continuous.prodMk_right 1)).inter (hσ F)
    have ht : Filter.Tendsto (fun y : GL (n ⊕ Fin c) k => h⁻¹ * y) (𝓝 h) (𝓝 1) := by
      simpa using (continuous_const_mul h⁻¹).tendsto h
    filter_upwards [ht.eventually (hU.mem_nhds ⟨om_one μ _, by simp⟩)] with y hy
    obtain ⟨u, rfl⟩ : ∃ u, y = h * u := ⟨h⁻¹ * y, by simp⟩
    rw [inv_mul_cancel_left] at hy
    have h1 : om μ 1 u Φ.1 = Φ.1 := hy.1
    have h2 : σ u F = F := hy.2
    unfold tInt
    rw [hmul, h1, map_mul, Module.End.mul_apply, h2]
  · obtain ⟨Λ, hΛ, hΛ'⟩ := GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup k _ _ Φ.1 Φ.2
    obtain ⟨Ω, hΩ, H⟩ := opE_support_compact_mod_R k n n' c p hp hpc ψ hψ hψ1 ν (tsupport Φ.1)
      Φ.2.2 Λ hΛ
    refine ⟨Ω, hΩ, fun h hh => ?_⟩
    have hne : E h ≠ 0 := fun h0 => hh (by rw [hfE, h0]; simp)
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, opE ψ ν p (om μ 1 h Φ.1) x₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (Subtype.ext (funext hc))
    exact H μ Φ.1 (subset_tsupport _) hΛ' (fun _ => 1) (IsLocallyConstant.const 1) h x₀
      (by simpa using hx₀)
  · intro x u hu h
    set a : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) with ha
    let Ψ : SB (Matrix n n' k) := ⟨om μ 1 x (E h).1, om_mem_SB μ 1 x (E h).2⟩
    have h1 : E (embX c x * u * h) = (a * (ψ (-simpleSum u) : ℂ)) • Ψ := by
      apply Subtype.ext
      show opE ψ ν p (om μ 1 (embX c x * u * h) Φ.1) =
        (a * (ψ (-simpleSum u) : ℂ)) • om μ 1 x (opE ψ ν p (om μ 1 h Φ.1))
      rw [mul_assoc, hmul, (opE_om_embX k n n' c p hp hpc ψ ν μ _).1, hmul,
        opE_om_target_unipotent k n n' c p hp hpc ψ ν μ _ u hu]
      funext y
      simp only [om, Pi.smul_apply, smul_eq_mul, ha]
      ring
    have h3 : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; simp
    have h4 : a * a =
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) := by
      rw [ha, ← Complex.ofReal_mul, ← Real.rpow_add (nabs_pos _ _)]
      congr 2
      ring
    have h5 := hB.1 (E h) u hu (σ h F)
    have h6 := hB.2 x (E h) Ψ (σ u (σ h F)) rfl
    rw [hfE, hfE, h1, map_smul, LinearMap.smul_apply, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, h6, h5, ← h4, ← ha, smul_eq_mul]
    linear_combination (a * a * B (E h) (σ h F)) * h3

theorem target_bilinear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : c = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (fj : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : Represents ψ ν ρ σ fj B) (_ : BilPos ψ μ (ρ + 1) σ B) (F : A) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (z : ℂ), IsQuotInt ν μX μG (ρ + 1) (tInt ψ ν μ (ρ + 1) σ B F Φ.1) z ↔ FJInt ψ ν μX μG μ ρ (fun h Ψ Φ₀ => fj Ψ (σ h F) Φ₀) Φ.1 z := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ρ h1 hc ψ hψ hψ1 ν hν μ hμ μX _ μG _ A _ _ σ hσ fj B hb hp F Φ z
  have h2 : ρ < c := by omega
  have := hν.1
  have := secondCountable k
  have := t2Space k
  have e : ∀ h β, app B (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F)) =
      tInt ψ ν μ (ρ + 1) σ B F Φ.1 (colE c (ρ + 1) β * h) := by
    intro h β
    have := om_mul μ 1 1 (colE c (ρ + 1) β) h Φ.1
    rw [one_mul] at this
    unfold tInt
    rw [this, map_mul]
    rfl
  obtain ⟨z₀, hz₀⟩ := exists_isQuotInt_tInt (p := ρ + 1) (by omega) (by omega) hψ hψ1 ν μ hμ μX μG hσ hp F Φ
  have W := GlobalTheory.T.weil_formula_rootExchange_parabolic_quotient k n c ρ h1 h2 ν μX μG (tInt ψ ν μ (ρ + 1) σ B F Φ.1)
  have val : ∀ h w, HasTensorVal (fun Ψ Φ₀ => fj Ψ (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) w ↔
      w = ∫ β : n → k, app B (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
        ∂(Measure.pi fun _ => ν) := by
    intro h
    have v1 : ∀ w, HasTensorVal (fun Ψ Φ₀ => fj Ψ (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) w →
        w = ∫ β : n → k, app B (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
          ∂(Measure.pi fun _ => ν) := by
      rintro w ⟨m, Ψ, Φ₀, hd, rfl⟩
      simp only [(hb.2 _ _ _).2]
      rw [← MeasureTheory.integral_finsetSum _ fun i _ => (hb.2 _ _ _).1]
      congr 1; funext β
      have : (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) = (∑ i, (Φ₀ i).1 β • Ψ i : SB (Matrix n n' k)).1 := by
        funext x₀
        simp [hd, mul_comm]
      rw [this, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe]
      simp
    let T : (n → k) → SB (Matrix n n' k) := fun β =>
      opL hψ ν (ρ + 1) (omR μ (1, colE c (ρ + 1) β) (omR μ (1, h) Φ))
    have hT : IsLocallyConstant T :=
      ((orbit_locallyConstant (omR_smooth hμ) (omR μ (1, h) Φ)).comp_continuous
        (continuous_const.prodMk ExchangeSupport.continuous_colE)).comp fun Ψ => opL hψ ν (ρ + 1) Ψ
    obtain ⟨K, hK, HK⟩ := ColumnSupport.opE_colE_eq_zero k n n' c ρ h2 ψ ν μ _ (omR μ (1, h) Φ).2
    obtain ⟨m, Ψ, Φ₀, hd⟩ := GlobalTheory.T.exists_sum_smul_of_locallyConstant_compactSupport (n → k) _ T hT K hK fun β hβ => Subtype.ext (by
      have := HK β hβ fun _ => 1
      simp only [one_mul] at this
      exact this)
    have v2 : HasTensorVal (fun Ψ Φ₀ => fj Ψ (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) _ :=
      ⟨m, Ψ, Φ₀, fun x y => by
        have := congrArg (fun t : SB (Matrix n n' k) => t.1 x) (hd y)
        refine Eq.trans this ?_
        simp [mul_comm], rfl⟩
    exact fun w => ⟨v1 w, fun hw => by rw [hw, ← v1 _ v2]; exact v2⟩
  have i1 : IsQuotInt ν μX μG (ρ + 1) (tInt ψ ν μ (ρ + 1) σ B F Φ.1) z ↔
        IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k,
          app B (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
            ∂(Measure.pi fun _ => ν)) z := by
    simp only [e]
    exact ⟨fun hz => (W z hz).2, fun hz => GlobalTheory.T.eq_of_isQuotIntFJ_of_isQuotIntFJ k n c ρ h1 h2 ν μX μG _ _ _ (W z₀ hz₀).2 hz ▸ hz₀⟩
  refine i1.trans ⟨fun hz => ⟨_, fun h => (val h _).2 rfl, hz⟩, ?_⟩
  rintro ⟨f, hf, hz⟩
  rwa [show f = _ from funext fun h => (val h _).1 (hf h)] at hz

end GlobalTheory.PosOne.FJTarget
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orthProjHyperbolicNegativeSpan_fixes_basis_and_idempotent : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), (∀ a, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.eV X a) = GlobalTheory.ScalW.eV X a ∧ GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.fV X a) = GlobalTheory.ScalW.fV X a) ∧ GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.zV X u) = GlobalTheory.ScalW.zV X u ∧ ∀ y, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.prj X u y) = GlobalTheory.ScalW.prj X u y := by
  first | exact @GlobalTheory.ScalW.prj_fix_idem | exact GlobalTheory.ScalW.prj_fix_idem | (intros; apply GlobalTheory.ScalW.prj_fix_idem <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orthProjHyperbolicNegativeSpan_selfAdjoint : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (x y : VA X.B.I), hA X.B.I (GlobalTheory.ScalW.prj X u x) y = hA X.B.I x (GlobalTheory.ScalW.prj X u y) := by
  first | exact @GlobalTheory.ScalW.prj_selfAdjoint | exact GlobalTheory.ScalW.prj_selfAdjoint | (intros; apply GlobalTheory.ScalW.prj_selfAdjoint <;> assumption)
end

section

open ValuativeRel NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.card_residueField_of_ringEquiv_adicCompletion : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → Nat.card 𝓀[k] = Ideal.absNorm v.asIdeal := by
  first | exact @GlobalTheory.LocalResidue.card_residue_of_ringEquiv | exact GlobalTheory.LocalResidue.card_residue_of_ringEquiv | (intros; apply GlobalTheory.LocalResidue.card_residue_of_ringEquiv <;> assumption)
end
