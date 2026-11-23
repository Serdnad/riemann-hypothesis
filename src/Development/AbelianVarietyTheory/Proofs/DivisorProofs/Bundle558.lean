module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle511
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem hasDatum_biconn_of (hfr : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), Nonempty (BFrame ε))
    (hmat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, IsConn G → IsConn G.dual → ∀ F : BFrame ε, ∃ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin G.height) F.B) (Gm : Matrix (Fin G.height) (Fin d ⊕ Fin k) F.B) (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie), d + k = G.height ∧ IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin G.height) (Fin G.height) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) ∧ (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) ∧ (∀ j m, F.θ (Y (Sum.inr j) m) = lb j (hodgeTate G (tb m))) ∧ ∀ m, dlog G (χ m) = ∑ i, F.θ (Gm m (Sum.inl i)) • w i)
    (hlift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B), IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin h) (Fin h) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → ∃ (Fa : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)) (Ga : Matrix (Fin h) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) ∧ Fa = Ψ * Fa.map (phiInv p O) ∧ Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) ∧ (∀ i m, WittVector.fontaineTheta O p (Fa i m) = F.θ (Y i m)) ∧ ∀ m i, WittVector.fontaineTheta O p (Ga m i) = F.θ (Gm m i))
    (hfin : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O) (d k : ℕ), d + k = G.height → ∀ (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie) (Fa : Matrix (Fin d ⊕ Fin k) (Fin G.height) (Ainf p O)) (Ga : Matrix (Fin G.height) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin G.height) (Fin G.height) (Ainf p O)) → Fa = Ψ * Fa.map (phiInv p O) → Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) → (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) → (∀ i m, WittVector.fontaineTheta O p (Fa (Sum.inl i) m) = 0) → (∀ j m, WittVector.fontaineTheta O p (Fa (Sum.inr j) m) = lb j (hodgeTate G (tb m))) → (∀ m j, WittVector.fontaineTheta O p (Ga m (Sum.inr j)) = 0) → (∀ m, dlog G (χ m) = ∑ i, WittVector.fontaineTheta O p (Ga m (Sum.inl i)) • w i) → HasDatum hε G) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, IsConn G → IsConn G.dual → HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG hD
  obtain ⟨F⟩ := hfr p C v O hv ε hε
  obtain ⟨d, k, U, Y, Gm, tb, χ, w, lb, hdk, hU, hY, hGm, hGY, hY0, hG0, hn1, hn2, hpair, hYl, hdl⟩ :=
    hmat p C v O hv ε hε G hG hD F
  obtain ⟨Fa, Ga, Ψ, Ψ', h1, h2, h3, h4, h5⟩ :=
    hlift p C v O hv ε hε F d k G.height U Y Gm ⟨hU, hY, hGm, hGY, hY0, hG0, hn1, hn2⟩
  refine hfin p C v O hv ε hε G d k hdk tb χ w lb Fa Ga Ψ Ψ' h1 h2 h3 hpair
    (fun i m => (h4 _ _).trans (hY0 i m)) (fun j m => (h4 _ _).trans (hYl j m))
    (fun m j => (h5 _ _).trans (hG0 m j)) (fun m => ?_)
  rw [hdl m]
  exact Finset.sum_congr rfl fun i _ => by rw [h5]

end GlobalTheory.PDivLat
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.KatzPull

open GlobalTheory.Katz

theorem lift_X (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type} (s : σ) :
    Katz.lift p (X s : MvPowerSeries σ k) = X s := by
  classical
  ext α
  rw [coeff_lift, coeff_X, coeff_X]
  split_ifs
  · rw [map_one, map_one]
  · rw [WittVector.teichmuller_zero, map_zero]

theorem lin_subst {R : Type} [CommRing R] {d e : ℕ} (a : Fin e → MvPowerSeries (Fin d) R)
    (ha : ∀ j, constantCoeff (a j) = 0) (f : MvPowerSeries (Fin e) R) :
    lin (subst a f) = pullLin a (lin f) := by
  classical
  have ha' := hasSubst_of_constantCoeff_zero ha
  have hcard : ∀ α : Fin e →₀ ℕ, Multiset.card (Finsupp.toMultiset α) = α.degree := fun α => by
    rw [Finsupp.card_toMultiset, Finsupp.degree]; rfl
  have inj : Function.Injective (Finsupp.toMultiset : (Fin e →₀ ℕ) → Multiset (Fin e)) :=
    fun x y hxy => by simpa using congrArg Multiset.toFinsupp hxy
  set f1 : MvPowerSeries (Fin e) R := C (constantCoeff f) + ∑ j, C (lin f j) * X j with hf1
  have hf2 : ∀ α : Fin e →₀ ℕ, α.degree < 2 → coeff α (f - f1) = 0 := by
    intro α hα
    rcases (show α.degree = 0 ∨ α.degree = 1 by omega) with h | h
    · have h0 : α = 0 := by
        apply inj
        rw [map_zero, ← Multiset.card_eq_zero, hcard, h]
      subst h0
      simp [hf1, coeff_X]
    · obtain ⟨j, hj⟩ := Multiset.card_eq_one.1 ((hcard α).trans h)
      have h1 : α = Finsupp.single j 1 := by
        apply inj
        rw [hj, Finsupp.toMultiset_single, one_smul]
      subst h1
      simp [hf1, coeff_X, coeff_C, lin, Finsupp.single_eq_single_iff]
  funext i
  have key := (GlobalTheory.T.coeff_subst_leading_of_agree_degree_one R (Fin e) (Fin d) a a 2 (f - f1) ha ha (fun _ _ _ => rfl) hf2
    (Finsupp.single i 1)).1 (by rw [Finsupp.degree_single]; norm_num)
  rw [subst_sub ha', map_sub, sub_eq_zero] at key
  unfold lin pullLin

  rw [key, hf1, subst_add ha', subst_C, map_add (f := _), coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero),
  zero_add, ← coe_substAlgHom ha', map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coe_substAlgHom ha', subst_C, subst_X ha', coeff_C_mul]
  rfl

theorem quasiLog_pull : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k), IsHom μ ν φ → ∀ f ∈ quasiLog p hν, subst (fun j => Katz.lift p (φ j)) f ∈ quasiLog p hμ ∧ (∀ c, Red p (cob1 (fun j => Katz.lift p (ν j)) f) c → Red p (cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f)) (pull2 φ c)) ∧ ∀ w, RedV p (lin f) w → RedV p (lin (subst (fun j => Katz.lift p (φ j)) f)) (pullLin φ w) := by
  intro p _ k _ _ _ d e μ ν hμ hν φ hφ f hf
  obtain ⟨hf1, hf2⟩ := hf
  have hΦ0 : ∀ j, constantCoeff (Katz.lift p (φ j)) = 0 := fun j => constantCoeff_lift p (hφ.const j)
  have hΦs : HasSubst (fun j => Katz.lift p (φ j)) := hasSubst_of_constantCoeff_zero hΦ0
  have hLμ0 : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  have hLμs : HasSubst (fun i => Katz.lift p (μ i)) := hasSubst_of_constantCoeff_zero hLμ0
  have hLν0 : ∀ i, constantCoeff (Katz.lift p (ν i)) = 0 := fun i => constantCoeff_lift p (hν.const i)
  have hXl0 : ∀ i : Fin d, constantCoeff (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
    fun _ => constantCoeff_X _
  have hXr0 : ∀ i : Fin d, constantCoeff (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
    fun _ => constantCoeff_X _
  have hXls := hasSubst_of_constantCoeff_zero hXl0
  have hXrs := hasSubst_of_constantCoeff_zero hXr0
  have RR := fun σ => GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k σ
  have hRedΦ : ∀ j, Red p (Katz.lift p (φ j)) (φ j) := fun j => (RR _).2.2.1 (φ j)
  have redX : ∀ {σ : Type} (s : σ), Red p (X s : MvPowerSeries σ (Fr p k)) (X s) := fun s => by
    simpa [lift_X] using (RR _).2.2.1 (X s : MvPowerSeries _ k)
  have hIL := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inl i)) (fun i => X (Sum.inl i))
    hXl0 (fun i => redX _)
  have hIR := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inr i)) (fun i => X (Sum.inr i))
    hXr0 (fun i => redX _)

  set U : Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    Sum.elim (fun j => inL (Katz.lift p (φ j))) (fun j => inR (Katz.lift p (φ j))) with hU
  set U' : Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) k :=
    Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j)) with hU'
  have hinL0 : ∀ j, constantCoeff (inL (Katz.lift p (φ j))) = 0 := fun j =>
    constantCoeff_subst_eq_zero hXls hXl0 (hΦ0 j)
  have hinR0 : ∀ j, constantCoeff (inR (Katz.lift p (φ j))) = 0 := fun j =>
    constantCoeff_subst_eq_zero hXrs hXr0 (hΦ0 j)
  have hU0 : ∀ s, constantCoeff (U s) = 0 := by
    rintro (j | j)
    · exact hinL0 j
    · exact hinR0 j
  have hRedU : ∀ s, Red p (U s) (U' s) := by
    rintro (j | j)
    · exact hIL.1 _ _ (hRedΦ j)
    · exact hIR.1 _ _ (hRedΦ j)
  have hIU := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin e ⊕ Fin e) (Fin d ⊕ Fin d) U U' hU0 hRedU
  have C6 := GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) e (Fin d ⊕ Fin d) (Fin d ⊕ Fin d)
    (fun j => inL (Katz.lift p (φ j))) (fun j => inR (Katz.lift p (φ j))) hinL0 hinR0

  set A : Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    fun j => subst (fun i => Katz.lift p (μ i)) (Katz.lift p (φ j)) with hA
  set B : Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    fun j => subst U (Katz.lift p (ν j)) with hB
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => constantCoeff_subst_eq_zero hLμs hLμ0 (hΦ0 j)
  have hB0 : ∀ j, constantCoeff (B j) = 0 := fun j =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hU0) hU0 (hLν0 j)
  have hRA : ∀ j, Red p (A j) (subst μ (φ j)) := fun j =>
    (GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d ⊕ Fin d) _ μ hLμ0 (fun i => (RR _).2.2.1 (μ i))).1 _ _ (hRedΦ j)
  have hRB : ∀ j, Red p (B j) (subst μ (φ j)) := fun j => by
    rw [hφ.hom j]
    exact hIU.1 _ _ ((RR _).2.2.1 (ν j))
  have hD := GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin e) (Fin d ⊕ Fin d) A B (fun j => subst μ (φ j)) f hA0 hB0 hRA hRB hf1

  have hid : cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f) =
      (subst A f - subst B f) + subst U (cob1 (fun j => Katz.lift p (ν j)) f) := by
    have e1 : subst U (cob1 (fun j => Katz.lift p (ν j)) f) =
        subst B f - subst (fun j => inL (Katz.lift p (φ j))) f - subst (fun j => inR (Katz.lift p (φ j))) f := by
      change at2 (cob1 (fun j => Katz.lift p (ν j)) f) _ _ = _
      unfold cob1
      rw [(C6.2.2.1 _ _).2, (C6.2.2.1 _ _).2, C6.1, C6.2.1, C6.2.2.2.2.2.1 e _ hLν0]
      rfl
    rw [e1]
    unfold cob1 inL inR
    rw [subst_comp_subst_apply hΦs hLμs, subst_comp_subst_apply hΦs hXls,
      subst_comp_subst_apply hΦs hXrs]
    abel
  have part2 : ∀ c, Red p (cob1 (fun j => Katz.lift p (ν j)) f) c →
      Red p (cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f)) (pull2 φ c) := by
    intro c hc
    rw [hid]
    have h1 := ((RR _).2.2.2.2.2.1 _).1 hD
    have h2 := hIU.1 _ _ hc
    have := ((RR _).2.2.2.1 _ _ _ _ h1 h2).1
    rwa [zero_add] at this
  refine ⟨⟨GlobalTheory.T.subst_mem_integralDifferentialSubmodule p k (Fin e) (Fin d) _ f hΦ0
      (fun j => ((RR _).1 _).2 ⟨φ j, hRedΦ j⟩) hf1, ?_⟩, part2, ?_⟩
  · obtain ⟨c, hc⟩ := ((RR _).1 _).1 hf2
    exact ((RR _).1 _).2 ⟨_, part2 c hc⟩
  · intro w hw i
    rw [lin_subst _ hΦ0]
    choose a ha ha' using hw
    refine ⟨∑ j, a j * WittVector.teichmuller p (lin (φ j) i), ?_, ?_⟩
    · simp only [pullLin, map_sum, map_mul, ha]
      simp only [lin, coeff_lift]
    · simp only [pullLin, ← WittVector.constantCoeff_apply, map_sum, map_mul,
        WittVector.constantCoeff_apply, ha', WittVector.teichmuller_coeff_zero]

end GlobalTheory.KatzPull
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.BoxMonomials

variable {d : ℕ}

noncomputable def boxPt {q : ℕ} (a : Fin d → Fin q) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))

theorem boxPt_apply {q : ℕ} (a : Fin d → Fin q) (i : Fin d) : boxPt a i = a i := by
  simp [boxPt]

theorem boxPt_injective {q : ℕ} : Function.Injective (boxPt (d := d) (q := q)) := by
  intro a b h
  funext i
  exact Fin.ext (by simpa [boxPt_apply] using DFunLike.congr_fun h i)

theorem exists_boxPt {q : ℕ} (β : Fin d →₀ ℕ) (h : ∀ i, β i < q) :
    ∃ a : Fin d → Fin q, boxPt a = β :=
  ⟨fun i => ⟨β i, h i⟩, by ext i; simp [boxPt_apply]⟩

end GlobalTheory.BoxMonomials


open GlobalTheory.BoxMonomials in
theorem GlobalTheory.coeff_eq_zero_of_evA_eq_zero_of_le_finrank :
    ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (d q : ℕ)
      (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)) (J : Ideal A),
      Function.Surjective (MvPolynomial.aeval (R := K) x) → (∀ i, x i ^ q ∈ J) →
      q ^ d ≤ Module.finrank K (A ⧸ J) → ∀ f : MvPowerSeries (Fin d) K, evA K x hx f = 0 →
      ∀ α : Fin d →₀ ℕ, α.degree < q → coeff α f = 0 := by
  intro K A _ _ _ _ d q x hx J hsurj hJ hdim f hf α hα
  classical
  set E : MvPowerSeries (Fin d) K →ₐ[K] A ⧸ J := (Ideal.Quotient.mkₐ K J).comp (evA K x hx)
    with hE
  have hEapp : ∀ y, E y = Ideal.Quotient.mk J (evA K x hx y) := fun y => rfl
  have hEX : ∀ i, evA K x hx (X i) = x i := fun i => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate K (Fin d) A x hx i
  have hEXq : ∀ i g, E (X i ^ q * g) = 0 := by
    intro i g
    rw [hEapp, Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, hEX]
    exact J.mul_mem_right _ (hJ i)
  have hmono : ∀ β : Fin d →₀ ℕ, ∀ i, q ≤ β i → ∀ c : K, E (monomial β c) = 0 := by
    intro β i hi c
    have : monomial β c = X i ^ q * monomial (β - Finsupp.single i q) c := by
      rw [X_pow_eq, monomial_mul_monomial, one_mul,
        add_tsub_cancel_of_le (Finsupp.single_le_iff.2 hi)]
    rw [this]
    exact hEXq i _
  set v : (Fin d → Fin q) → A ⧸ J := fun a => E (monomial (boxPt a) 1) with hv
  have hcoe : ∀ P : MvPolynomial (Fin d) K,
      Ideal.Quotient.mk J (MvPolynomial.aeval x P) = E (P : MvPowerSeries (Fin d) K) := by
    intro P
    have : (Ideal.Quotient.mkₐ K J).comp (MvPolynomial.aeval x) =
        E.comp (MvPolynomial.coeToMvPowerSeries.algHom K) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [hEapp, hEX]
    exact DFunLike.congr_fun this P
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    rintro y -
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨P, rfl⟩ := hsurj a'
    rw [hcoe]
    induction P using MvPolynomial.induction_on' with
    | monomial β c =>
      rw [MvPolynomial.coe_monomial]
      by_cases hb : ∀ i, β i < q
      · obtain ⟨a, rfl⟩ := exists_boxPt β hb
        have : monomial (boxPt a) c = c • monomial (boxPt a) (1 : K) := by
          rw [← map_smul, smul_eq_mul, mul_one]
        rw [this, map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      · push_neg at hb
        obtain ⟨i, hi⟩ := hb
        rw [hmono β i hi c]
        exact Submodule.zero_mem _
    | add P Q hP hQ =>
      rw [MvPolynomial.coe_add, map_add (f := _)]
      exact Submodule.add_mem _ hP hQ
  have hcard : Fintype.card (Fin d → Fin q) = Module.finrank K (A ⧸ J) := by
    apply le_antisymm
    · simpa [Fintype.card_fun] using hdim
    · have h1 := finrank_range_le_card (R := K) v
      have h2 : Set.finrank K (Set.range v) = Module.finrank K (A ⧸ J) := by
        unfold Set.finrank
        rw [eq_top_iff.2 hspan, finrank_top]
      omega
  have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard
  set P : MvPowerSeries (Fin d) K :=
    ∑ a : Fin d → Fin q, coeff (boxPt a) f • monomial (boxPt a) (1 : K) with hP
  have hPcoeff : ∀ a : Fin d → Fin q, coeff (boxPt a) P = coeff (boxPt a) f := by
    intro a

    rw [hP, map_sum, Finset.sum_eq_single a]
    · simp [coeff_monomial]
    · intro b _ hb
      simp [coeff_monomial, boxPt_injective.ne (Ne.symm hb)]
    · simp
  set h : MvPowerSeries (Fin d) K := f - P with hh
  let hi : Fin d → MvPowerSeries (Fin d) K := fun i β =>
    if q ≤ β i ∧ ∀ j < i, β j < q then coeff β h else 0
  have hic : ∀ i β, coeff β (hi i) = if q ≤ β i ∧ ∀ j < i, β j < q then coeff β h else 0 :=
    fun i β => by rw [coeff_apply]
  have hdiv : ∀ i, X i ^ q ∣ hi i := by
    intro i
    rw [X_pow_dvd_iff]
    intro m hm
    rw [hic, if_neg]
    omega
  have hsum : h = ∑ i, hi i := by
    ext β

    rw [map_sum]
    simp only [hic]
    by_cases hb : ∀ i, β i < q
    · obtain ⟨a, rfl⟩ := exists_boxPt β hb
      have : coeff (boxPt a) h = 0 := by rw [hh, map_sub, hPcoeff, sub_self]
      rw [this]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      have := hb i
      omega
    · push_neg at hb
      obtain ⟨i0, hi0mem, hmin⟩ := (Finset.univ.filter (fun i => q ≤ β i)).exists_min_image id
        (by obtain ⟨i, hi⟩ := hb; exact ⟨i, by simp [hi]⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, id] at hi0mem hmin
      rw [Finset.sum_eq_single i0]
      · rw [if_pos]
        refine ⟨hi0mem, fun j hj => ?_⟩
        by_contra hc
        exact absurd (hmin j (by omega)) (not_le.2 hj)
      · intro j _ hj
        rw [if_neg]
        rintro ⟨hjq, hjlt⟩
        rcases lt_or_gt_of_ne hj with hlt | hlt
        · exact absurd (hmin j hjq) (not_le.2 hlt)
        · have := hjlt i0 hlt
          omega
      · simp
  have hEh : E h = 0 := by

    rw [hsum, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨g, hg⟩ := hdiv i
    rw [hg]
    exact hEXq i g
  have hEf : E f = 0 := by rw [hEapp, hf, map_zero]
  have hfP : f = P + h := by rw [hh]; ring
  have hzero : ∑ a : Fin d → Fin q, coeff (boxPt a) f • v a = 0 := by
    have : E P = ∑ a : Fin d → Fin q, coeff (boxPt a) f • v a := by

      rw [hP, map_sum]
      simp only [map_smul, hv]
    rw [← this, ← hEf, hfP, map_add (f := _), hEh, add_zero]
  have hall := Fintype.linearIndependent_iff.1 hli _ hzero
  obtain ⟨a, rfl⟩ := exists_boxPt α (fun i => lt_of_le_of_lt (Finsupp.le_degree i α) hα)
  exact hall a
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_mayerVietoris_connecting_exact : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∀ n : ℤ, H R (pullback f g) F n →+ H R E F (n + 1), (∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) (n : ℤ), (∀ a b, pull R (pullback.fst f g) F n a = pull R (pullback.snd f g) F n b ↔ ∃ x, pull R f F n x = a ∧ pull R g F n x = b) ∧ (∀ c, d f g h n c = 0 ↔ ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) ∧ ∀ x, (pull R f F (n + 1) x = 0 ∧ pull R g F (n + 1) x = 0) ↔ ∃ c, d f g h n c = x) ∧ ∀ {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E') (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (h : Cover2 R f g) (h' : Cover2 R f' g') (n : ℤ) c, pull R p F (n + 1) (d f' g' h' n c) = d f g h n (pull R (pullback.map f g f' g' u v p hu hv) F n c) := by
  first | (exact @GlobalTheory.EtC.mayerVietoris) | (exact GlobalTheory.EtC.mayerVietoris) | (intros; apply GlobalTheory.EtC.mayerVietoris  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive : ∀ (R : Type) [CommRing R] (K : Cx R) (n : ℤ), (∀ (F : Shv R) x, HK.post R K (𝟙 F) n x = x) ∧ (∀ {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) x, HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x)) ∧ (∀ {F G : Shv R} (φ ψ : F ⟶ G), HK.post R K (φ + ψ) n = HK.post R K φ n + HK.post R K ψ n) ∧ (∀ {F G : Shv R} (φ : F ⟶ G) (c : ℤ) x, HK.post R K (c • φ) n x = c • HK.post R K φ n x) ∧ ∀ {L : Cx R} (f : L ⟶ K) {F G : Shv R} (φ : F ⟶ G) x, HK.pull R f G n (HK.post R K φ n x) = HK.post R L φ n (HK.pull R f F n x) := by
  first | (exact @GlobalTheory.EtC.PostFun.main) | (exact GlobalTheory.EtC.PostFun.main) | (intros; apply GlobalTheory.EtC.PostFun.main  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.shortExact_mappingCone_resolution_homotopyEquiv : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact → ∃ e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃), Nonempty (Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g)) := by
  first | (exact @GlobalTheory.EtC.cone_resMap_homotopyEquiv) | (exact GlobalTheory.EtC.cone_resMap_homotopyEquiv) | (intros; apply GlobalTheory.EtC.cone_resMap_homotopyEquiv  <;> assumption)
end

section

open MeasureTheory Matrix

namespace GlobalTheory.HeisUnit

theorem exists_unitary_factor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
      (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∃ ν : kˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧ ∀ g : GL (Fin n) k,
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) = ν (Matrix.GeneralLinearGroup.det g) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) ((d : ℂ) / 2) := by
  intro k _ _ _ _ n d ψ0 hψc hψ1 ι hι Tr Mu hTr hMu hTrI hMuI S hS hSI χ hχ
  let ν : kˣ →* ℂˣ := χ *
    { toFun := fun x => Units.mk0 (GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))) (GlobalTheory.SplitFlip.apow_ne_zero _ _)
      map_one' := Units.ext (GlobalTheory.SplitFlip.apow_one _)
      map_mul' := fun x y => Units.ext (GlobalTheory.SplitFlip.apow_mul x y _) }
  have hν : ∀ x : kˣ, (ν x : ℂ) = (χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)) := fun x => rfl
  have hfac : ∀ x : kˣ, (χ x : ℂ) = ν x * GlobalTheory.SplitFlip.apow x ((d : ℂ) / 2) := fun x => by
    rw [hν, mul_assoc, ← GlobalTheory.SplitFlip.apow_add, neg_add_cancel, GlobalTheory.SplitFlip.apow_zero, mul_one]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, fun x => by simp, fun g => ?_⟩
    have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    simp
  · refine ⟨ν, fun x => ?_, fun g => hfac _⟩
    let i0 : Fin n := ⟨0, hn⟩
    obtain ⟨φ0, hφ0, hιφ0⟩ := hι.surjOn (GlobalTheory.HeisUnit.intInd_mem_SB (k := k) n d)
    have hne : φ0 ≠ 0 := by
      rintro rfl
      have h := congrFun hιφ0 0
      rw [map_zero, GlobalTheory.HeisUnit.intInd_zero] at h
      exact zero_ne_one h
    have hN : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ 0 ∧ ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ ⊤ := fun μ hμ =>
      ⟨(GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0).2.2.1 hne, (GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0).1⟩
    have hU := GlobalTheory.T.norm_character_unit_eq_one_heisenberg ι hι.injOn S hS hSI χ hχ φ0 hφ0 hιφ0 hN i0
    obtain ⟨ϖ, hϖ⟩ := GlobalTheory.SplitFlip.exists_isUnif (k := k)
    have hP := GlobalTheory.T.normSq_uniformizer_character_mul_residueCard_pow_eq_one ι hι.injOn Tr hTr hTrI S hS hSI χ hχ φ0 hφ0 hιφ0 hne ϖ hϖ i0
      (fun μ hμ T T' h => GlobalTheory.T.heisenbergCosetRepTranslates_orthogonal ψ0 hψc hψ1 ι hι.injOn Tr hTr Mu hMu hMuI φ0 hφ0 hιφ0 ϖ hϖ i0 T T' h μ hμ)
    rw [hν]
    exact GlobalTheory.T.norm_mul_normalisedAbsPow_half_eq_one d χ hU ϖ hϖ hP x

end GlobalTheory.HeisUnit
end
