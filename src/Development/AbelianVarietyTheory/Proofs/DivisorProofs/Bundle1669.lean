module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameReflTransGenCyclicChain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisLiftPdThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle860
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecondTangent

theorem tangent_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∃ lb : Module.Basis (Fin k) O G.dual.Lie, ∀ j, c.IsLie (map Θ (e (Sum.inr j))) (lb j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hμ k e he hadapt Θ hΘ
  have hF : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hμeq : (fun i => map F.θ (μ' i)) = c.μ := funext hμ
  obtain ⟨k', es, lbs, hbs, -, hcobs, hlies⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c C hF

  have hlift1 : ∀ m, ∃ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f ∧ map Θ f = es m := by
    intro m
    have hq : QL (fun i => map F.θ (μ' i)) ⊤ (es m) := hμeq ▸ hbs.1 m
    choose b _ hb using hq.2.1
    choose w hw using fun i => F.frame.surj (b i)
    obtain ⟨f, hf, hf', -⟩ := GlobalTheory.QLog.KLift.lift_quasiLog p F.B O F.Q F.θ F.frame d μ' hlift C hF
      Θ hΘ (es m) w hq (fun i => by rw [hb, hw])
    exact ⟨f, hf, hf'⟩
  choose f hfq hfm using hlift1
  have hfb : IsBasis μ' f := by
    refine GlobalTheory.basis_lift p F.B O F.Q F.θ F.frame d μ' hlift C hF Θ hΘ _ f hfq ?_
      (GlobalTheory.BChain.reflTransGen_isStep p C v O hv ε hε F)
    have : (fun i => map Θ (f i)) = es := funext hfm
    rw [this, hμeq]; exact hbs

  choose P hP using fun i => (hfb.2 (e i) (he.1 i)).exists
  choose P' hP' using fun j => (he.2 (f j) (hfq j)).exists
  obtain ⟨h1, h2⟩ := GlobalTheory.T.quasiLogarithmBasis_transitionMatrices_inverse μ' e f he hfb P P' hP hP'

  let Ls : Fin d ⊕ Fin k' → G.dual.Lie := Sum.elim 0 lbs
  have hLs : ∀ m, c.IsLie (es m) (Ls m) := by
    rintro (i | j)
    · obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c C hF (es (Sum.inl i)) (hbs.1 _)
      have := (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF _ _ l l 0 hl hl).2.2 (hcobs i)
      subst this; exact hl
    · exact hlies j
  have hμc : ∀ i, constantCoeff (μ' i) = 0 := hlift.const
  have hg : ∀ i, QL c.μ ⊤ (map Θ (e i)) := fun i => by
    rw [← hμeq]; exact GlobalTheory.SmallSecond.ql_map hΘ μ' hμc (he.1 i)
  have hrow : ∀ i, c.IsLie (map Θ (e i)) (∑ m, F.θ (P i m) • Ls m) := by
    intro i
    refine GlobalTheory.T.tangentVector_quasiLogarithm_of_congruent_combination p C v O hv G d c es (hbs.1) Ls hLs _ (hg i) _ ?_
    intro α
    obtain ⟨b, -, hb⟩ := hP i α
    refine ⟨F.θ b, trivial, ?_⟩
    have : map Θ (e i) - comb (fun m => F.θ (P i m)) es = map Θ (e i - comb (P i) f) := by
      rw [map_sub, GlobalTheory.SmallSecond.map_comb hΘ, funext hfm]
    rw [this, coeff_map, hb, hΘ]

  have hzero : ∀ i j, F.θ (P (Sum.inl i) (Sum.inr j)) = 0 := by
    intro i
    have hc : cob1 (up C c.μ) (map Θ (e (Sum.inl i))) = 0 := by
      rw [← hμeq]; exact GlobalTheory.SmallSecond.formalGroupLawCoboundaryOne_map_eq_zero hΘ μ' hμc (hadapt i).1
    have h0 := (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF _ _ _ _ 0 (hrow (Sum.inl i)) (hrow (Sum.inl i))).2.2 hc
    simp only [Fintype.sum_sum_type, Ls, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, smul_zero,
      Finset.sum_const_zero, zero_add] at h0
    exact (Fintype.linearIndependent_iff.1 lbs.linearIndependent) _ h0
  obtain ⟨lb, hlb⟩ := GlobalTheory.T.exists_basis_of_blockLowerTriangular_inv' O G.dual.Lie d k k' lbs ((Matrix.of P).map F.θ)
    ((Matrix.of P').map F.θ) (by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]) hzero
  refine ⟨lb, fun j => ?_⟩
  have := hrow (Sum.inr j)
  simp only [Fintype.sum_sum_type, Ls, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, smul_zero,
    Finset.sum_const_zero, zero_add] at this
  rw [hlb]; exact this

end GlobalTheory.SmallSecondTangent
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReduceBasis

section Ring

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_zero : In (⊤ : Ideal B) (0 : MvPowerSeries σ Q) :=
  fun _ => ⟨0, trivial, by simp⟩

theorem in_neg {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) : In (⊤ : Ideal B) (-f) := by
  simpa using KLift.in_sub in_zero hf

theorem in_smul (r : B) {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (⊤ : Ideal B) (algebraMap B Q r • f) := fun α => by
  obtain ⟨b, -, hb⟩ := hf α
  exact ⟨r * b, trivial, by rw [coeff_smul, hb, map_mul]⟩

theorem in_sum {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ Q)
    (hf : ∀ i, In (⊤ : Ideal B) (f i)) : In (⊤ : Ideal B) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (in_zero : In (⊤ : Ideal B) (0 : MvPowerSeries σ Q))
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact KLift.in_add (hf a) ih

variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem comb_sub (x y : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb x e - comb y e = comb (x - y) e := by
  simp only [comb, ← Finset.sum_sub_distrib, Pi.sub_apply, map_sub, sub_smul]

theorem comb_single [DecidableEq ι] (l : ι) (e : ι → MvPowerSeries σ Q) :
    comb (Pi.single l (1 : B)) e = e l := by
  rw [comb, Finset.sum_eq_single l (fun j _ hj => by simp [Pi.single_apply, hj])
    (fun h => absurd (Finset.mem_univ l) h)]
  simp

theorem comb_comb (M : κ → B) (N : κ → ι → B) (e : ι → MvPowerSeries σ Q) :
    ∑ m, algebraMap B Q (M m) • comb (N m) e = comb (fun l => ∑ m, M m * N m l) e := by

  simp only [comb, Finset.smul_sum, smul_smul, ← map_mul, map_sum, Finset.sum_smul]
  exact Finset.sum_comm

theorem mul_eq_single [DecidableEq ι] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {e : ι → MvPowerSeries (Fin d) Q} {f : κ → MvPowerSeries (Fin d) Q} (he : IsBasis μ e)
    (M : ι → κ → B) (N : κ → ι → B) (hM : ∀ l, In (⊤ : Ideal B) (e l - comb (M l) f))
    (hN : ∀ m, In (⊤ : Ideal B) (f m - comb (N m) e)) (l : ι) :
    (fun l' => ∑ m, M l m * N m l') = Pi.single l 1 := by
  refine (he.2 (e l) (he.1 l)).unique ?_ ?_
  · have hs : e l - comb (fun l' => ∑ m, M l m * N m l') e =
        (e l - comb (M l) f) + ∑ m, algebraMap B Q (M l m) • (f m - comb (N m) e) := by
      simp only [smul_sub, Finset.sum_sub_distrib, comb_comb]
      simp only [comb]; abel
    rw [hs]
    exact KLift.in_add (hM l) (in_sum _ _ fun m => in_smul _ (hN m))
  · rw [comb_single, sub_self]; exact in_zero

end Ring

section Map

variable {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
  [Algebra O C] {σ : Type} {θ : B →+* O} {Θ : Q →+* C}
  (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))

include hΘ in
theorem in_map {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (⊤ : Ideal O) (map Θ f) := fun α => by
  obtain ⟨b, -, hb⟩ := hf α
  exact ⟨θ b, trivial, by rw [coeff_map, hb, hΘ]⟩

theorem map_smul_series (c : Q) (f : MvPowerSeries σ Q) : map Θ (c • f) = Θ c • map Θ f := by
  ext α
  simp [coeff_map, coeff_smul]

include hΘ in
theorem map_comb {ι : Type} [Fintype ι] (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    map Θ (comb b e) = comb (fun i => θ (b i)) (fun i => map Θ (e i)) := by

  simp only [comb, map_sum, map_smul_series, hΘ]

end Map

end GlobalTheory.ReduceBasis

namespace GlobalTheory.ReduceBasis

theorem isBasis_map : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → IsBasis c.μ (fun l => map Θ (e l)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hμ k e he Θ hΘ
  classical
  have hC : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hcμ : (fun i => map F.θ (μ' i)) = c.μ := funext hμ
  have hμQ : ∀ i, constantCoeff (up F.Q μ' i) = 0 := KLift.const_map _ μ' hL.const
  have hμC : ∀ i, constantCoeff (up C c.μ i) = 0 := KLift.const_map _ _ c.isLaw.const
  have hΘμ : (fun i => map Θ (up F.Q μ' i)) = up C c.μ := by
    have hc : Θ.comp (algebraMap F.B F.Q) = (algebraMap O C).comp F.θ := RingHom.ext hΘ
    funext i
    unfold up
    rw [← hμ i, ← RingHom.comp_apply (map Θ), ← map_comp,
      ← RingHom.comp_apply (map (algebraMap O C)), ← map_comp, hc]
  have hQL : ∀ f, QL μ' ⊤ f → QL c.μ ⊤ (map Θ f) := by
    rintro f ⟨h0, h1, h2⟩
    refine ⟨?_, fun i => ?_, ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
        map_zero]
    · obtain ⟨b, -, hb⟩ := h1 i
      refine ⟨F.θ b, trivial, ?_⟩
      simp only [lin, coeff_map] at hb ⊢
      rw [hb, hΘ]
    · rw [← hΘμ, ← KLift.map_formalGroupLawCoboundaryOne_eq Θ _ hμQ]
      exact in_map hΘ h2

  have hlift : ∀ g, QL c.μ ⊤ g → ∃ f, QL μ' ⊤ f ∧ map Θ f = g := by
    intro g hg
    choose o _ ho using hg.2.1
    choose w hw using fun i => F.frame.surj (o i)
    obtain ⟨f, hf, hfg, -⟩ := KLift.lift_quasiLog p F.B O F.Q F.θ F.frame d μ' hL C hC Θ hΘ g w
      (by rw [hcμ]; exact hg) (fun i => by rw [ho, hw])
    exact ⟨f, hf, hfg⟩
  have key : ∀ x : Fin d ⊕ Fin k → O, In (⊤ : Ideal O) (comb x fun l => map Θ (e l)) → x = 0 := by
    intro x hx
    obtain ⟨k0, e0, -, he0, -⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c C hC
    choose f hf hfe using fun m => hlift (e0 m) (he0.1 m)
    have hfB : IsBasis μ' f := GlobalTheory.basis_lift p F.B O F.Q F.θ F.frame d μ' hL C hC Θ hΘ _ f hf
      (by rw [hcμ]; simpa only [hfe] using he0) (GlobalTheory.BChain.reflTransGen_isStep p C v O hv ε hε F)
    choose M hM _ using fun l => hfB.2 (e l) (he.1 l)
    choose N hN _ using fun m => he.2 (f m) (hf m)
    have hMN := mul_eq_single he M N hM hN
    set y : Fin d ⊕ Fin k0 → O := fun m => ∑ l, x l * F.θ (M l m) with hydef
    have hy : In (⊤ : Ideal O) (comb y e0) := by
      have hs : comb y e0 = comb x (fun l => map Θ (e l)) -
          ∑ l, algebraMap O C (x l) • map Θ (e l - comb (M l) f) := by
        simp only [map_sub, map_comb hΘ, hfe, smul_sub, Finset.sum_sub_distrib, comb_comb, hydef]
        simp only [comb]
        abel
      rw [hs]
      exact KLift.in_sub hx (in_sum _ _ fun l => in_smul _ (in_map hΘ (hM l)))
    have h0 : QL c.μ ⊤ (0 : MvPowerSeries (Fin d) C) := by
      refine ⟨by simp, fun i => ⟨0, trivial, by simp [lin]⟩, ?_⟩
      have : cob1 (up C c.μ) (0 : MvPowerSeries (Fin d) C) = 0 := by
        simpa using formalCoboundary_smul hμC (0 : C) (0 : MvPowerSeries (Fin d) C)
      rw [this]
      exact in_zero
    have hy0 : y = 0 := by
      refine (he0.2 0 h0).unique ?_ ?_
      · simpa using in_neg hy
      · have : comb (0 : Fin d ⊕ Fin k0 → O) e0 = 0 := by simp [comb]
        rw [this, sub_zero]
        exact in_zero
    funext l'
    have e1 : ∀ l, F.θ (∑ m, M l m * N m l') = if l' = l then 1 else 0 := fun l => by
      have h1 := congrFun (hMN l) l'
      rw [h1, Pi.single_apply]
      split_ifs <;> simp
    have s1 : x l' = ∑ l, x l * F.θ (∑ m, M l m * N m l') := by
      simp only [e1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have s2 : ∑ l, x l * F.θ (∑ m, M l m * N m l') = ∑ m, y m * F.θ (N m l') := by

      simp only [hydef, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
    rw [s1, s2, hy0]
    simp
  refine ⟨fun l => hQL _ (he.1 l), fun g hg => ?_⟩
  obtain ⟨f, hf, hfg⟩ := hlift g hg
  obtain ⟨b, hb, -⟩ := he.2 f hf
  have hx0 : In (⊤ : Ideal O) (g - comb (fun l => F.θ (b l)) fun l => map Θ (e l)) := by
    have := in_map hΘ hb
    rwa [map_sub, hfg, map_comb hΘ] at this
  refine ⟨fun l => F.θ (b l), hx0, fun y hy => ?_⟩
  have h := key ((fun l => F.θ (b l)) - y) (by
    rw [← comb_sub]
    convert KLift.in_sub hy hx0 using 1
    abel)
  exact (sub_eq_zero.1 h).symm

end GlobalTheory.ReduceBasis
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBasisChange

open GlobalTheory.QLog

variable {d : ℕ} {O E : Type} [CommRing O] [CommRing E] [Algebra O E]

def intMap : MvPowerSeries (Fin d) O →ₗ[O] MvPowerSeries (Fin d) E where
  toFun := map (algebraMap O E)
  map_add' := map_add _
  map_smul' a s := by
    ext α
    change algebraMap O E (a * s α) = a • algebraMap O E (s α)
    rw [map_mul, Algebra.smul_def]

theorem in_top_iff (f : MvPowerSeries (Fin d) E) :
    In (⊤ : Ideal O) f ↔ f ∈ LinearMap.range (intMap (d := d) (O := O) (E := E)) := by
  rw [In.top_iff]; rfl

theorem comb_eq {ι : Type} [Fintype ι] (b : ι → O) (e : ι → MvPowerSeries (Fin d) E) :
    comb b e = Fintype.linearCombination O e b := by
  simp [comb, Fintype.linearCombination_apply, algebraMap_smul]

theorem defect_add_smul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (f g : MvPowerSeries (Fin d) E) (a : O) :
    defect μ n (f + a • g) = defect μ n f + a • defect μ n g := by
  have hs := hasSubst_up_nmul (Q := E) hμ n
  simp only [defect, ← coe_substAlgHom hs, ← algebraMap_smul E a, map_add (f := _), map_smul]
  module

theorem isLie_add_smul {p : ℕ} {G : PDivGroup p O} (c : QLog.Chart G d)
    (hinj : Function.Injective (algebraMap O E)) {f g : MvPowerSeries (Fin d) E}
    {l l' : G.dual.Lie} (a : O) (hf : c.IsLie f l) (hg : c.IsLie g l') :
    c.IsLie (f + a • g) (l + a • l') := by
  rw [QLog.Chart.isLie_iff c hinj] at hf hg ⊢
  intro n
  obtain ⟨s, hs, H⟩ := hf n
  obtain ⟨s', hs', H'⟩ := hg n
  refine ⟨s + a • s', ?_, fun w φ hφ => ?_⟩
  · rw [defect_add_smul c.isLaw.const, ← hs, ← hs']
    have := (intMap (d := d) (O := O) (E := E)).map_add s (a • s')
    rw [LinearMap.map_smul] at this
    exact this
  · have := dvd_add (H w φ hφ) (dvd_mul_of_dvd_right (H' w φ hφ) a)
    rw [LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul, map_add (f := _), map_smul,
      smul_eq_mul, smul_eq_mul]
    convert this using 1
    ring

theorem isLie_sum {p : ℕ} {G : PDivGroup p O} (c : QLog.Chart G d)
    (hinj : Function.Injective (algebraMap O E)) {ι : Type} [Fintype ι]
    (e : ι → MvPowerSeries (Fin d) E) (L : ι → G.dual.Lie) (hL : ∀ i, c.IsLie (e i) (L i))
    (b : ι → O) : c.IsLie (comb b e) (∑ i, b i • L i) := by
  classical
  rw [comb_eq, Fintype.linearCombination_apply]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using c.isLie_zero hinj
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, add_comm, add_comm (b i • L i)]
    exact isLie_add_smul c hinj (b i) ih (hL i)

theorem mul_eq_one {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} {ι κ : Type} [Fintype ι]
    [Fintype κ] [DecidableEq ι] {f : ι → MvPowerSeries (Fin d) E} {g : κ → MvPowerSeries (Fin d) E}
    (hf : IsBasis μ f) (P : ι → κ → O) (R : κ → ι → O)
    (hP : ∀ l, In (⊤ : Ideal O) (f l - comb (P l) g))
    (hR : ∀ m, In (⊤ : Ideal O) (g m - comb (R m) f)) :
    Matrix.of P * Matrix.of R = 1 := by
  ext l l'
  have h1 : In (⊤ : Ideal O) (f l - comb (Pi.single l (1 : O)) f) := by
    rw [in_top_iff, comb_eq, Fintype.linearCombination_apply_single, one_smul, sub_self]
    exact zero_mem _
  have h2 : In (⊤ : Ideal O) (f l - comb (∑ m, P l m • R m) f) := by
    have e1 : f l - comb (∑ m, P l m • R m) f =
        (f l - comb (P l) g) + ∑ m, P l m • (g m - comb (R m) f) := by

      simp only [comb_eq, map_sum, map_smul]
      simp only [Fintype.linearCombination_apply, smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e1, in_top_iff]
    simp only [in_top_iff] at hP hR
    exact add_mem (hP l) (Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hR m))
  have := congrFun ((hf.2 (f l) (hf.1 l)).unique h2 h1) l'
  simpa [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, Finset.sum_apply, eq_comm] using this

theorem card_eq [Nontrivial O] {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (P : Matrix ι κ O) (R : Matrix κ ι O) (h1 : P * R = 1) (h2 : R * P = 1) :
    Fintype.card ι = Fintype.card κ := by
  have e : (κ → O) ≃ₗ[O] (ι → O) := LinearEquiv.ofLinear (Matrix.toLin' P) (Matrix.toLin' R)
    (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have := e.finrank_eq
  rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, eq_comm] at this

theorem lie_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E), IsBasis c.μ e → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → ∃ lb : Module.Basis (Fin k) O G.dual.Lie, ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ h k e he hlog
  classical
  obtain ⟨k0, e0, lb0, he0, -, -, hlie0⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c E h
  have hinj : Function.Injective (algebraMap O E) := h.inj
  have hex := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E h
  have hlin := GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E h
  choose L hL using fun l => (hex _ (he.1 l)).exists
  have hL0 : ∀ i, L (Sum.inl i) = 0 := fun i =>
    (hlin _ _ _ _ 0 (hL (Sum.inl i)) (hL (Sum.inl i))).2.2 (hlog i)
  have hspan : ⊤ ≤ Submodule.span O (Set.range (L ∘ Sum.inr)) := by
    rw [← lb0.span_eq, Submodule.span_le]
    rintro _ ⟨j', rfl⟩
    obtain ⟨b, hb, -⟩ := he.2 (e0 (Sum.inr j')) (he0.1 (Sum.inr j'))
    have h1 : c.IsLie (e0 (Sum.inr j') + (-1 : O) • comb b e)
        (lb0 j' + (-1 : O) • ∑ l, b l • L l) :=
      isLie_add_smul c hinj (-1) (hlie0 j') (isLie_sum c hinj e L hL b)
    rw [neg_one_smul, neg_one_smul, ← sub_eq_add_neg, ← sub_eq_add_neg] at h1
    have h2 := (hlin _ _ _ _ 0 h1 h1).2.1 ((In.top_iff.1 hb).imp fun s hs => hs.symm)
    rw [sub_eq_zero, Fintype.sum_sum_type] at h2
    simp only [hL0, smul_zero, Finset.sum_const_zero, zero_add] at h2
    rw [SetLike.mem_coe, h2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  choose P hP using fun l => (he0.2 (e l) (he.1 l)).exists
  choose R hR using fun m => (he.2 (e0 m) (he0.1 m)).exists
  have hk := card_eq (Matrix.of P) (Matrix.of R) (mul_eq_one he P R hP hR)
    (mul_eq_one he0 R P hR hP)
  simp only [Fintype.card_sum, Fintype.card_fin] at hk
  obtain rfl : k0 = k := by omega
  have hsurj : Function.Surjective (Fintype.linearCombination O (L ∘ Sum.inr)) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact eq_top_iff.2 hspan
  have hinj2 : Function.Injective (Fintype.linearCombination O (L ∘ Sum.inr)) :=
    Function.Injective.of_comp (f := ⇑lb0.equivFun)
      (OrzechProperty.injective_of_surjective_endomorphism
        (lb0.equivFun.toLinearMap ∘ₗ Fintype.linearCombination O (L ∘ Sum.inr))
        (lb0.equivFun.surjective.comp hsurj))
  have hli : LinearIndependent O (L ∘ Sum.inr) :=
    linearIndependent_iff_injective_fintypeLinearCombination.2 hinj2
  exact ⟨Module.Basis.mk hli hspan, fun j => by rw [Module.Basis.mk_apply]; exact hL (Sum.inr j)⟩

end GlobalTheory.LieBasisChange
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem map_F1prim_eq_range_rigOfOmega (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ)
    (hN : (p : R) ^ N = 0) (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A)
    (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))))
    (hL : Function.Surjective L) (hc : ∀ c, IsCan t c (L c)) :
    (PrimitiveSubmodule A).map L = LinearMap.range G.rigOfOmega := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap p R N hN A hA G t
  apply le_antisymm
  · rintro _ ⟨c, hcF, rfl⟩
    refine ⟨ψ ⟨c, hcF⟩, ?_⟩
    exact GlobalTheory.PtExt.isCan_unique R A p G t c hA _ _ (hψ ⟨c, hcF⟩) (hc c)
  · rintro _ ⟨w, rfl⟩
    obtain ⟨c, hcw⟩ := hL (G.rigOfOmega w)
    refine ⟨c, GlobalTheory.T.mem_primitiveSubmodule_of_isCan_of_rigToExt_eq_zero p R N hN A hA G t c (L c) (hc c) ?_, hcw⟩
    rw [hcw]
    exact G.exact_rigOfOmega_rigToExt.apply_apply_eq_zero w

end GlobalTheory.PtExt
end
