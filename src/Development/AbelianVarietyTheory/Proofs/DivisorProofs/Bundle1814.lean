module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnBaseKer


open Classical in
theorem kerDat_of_isBaseKernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → ∀ ω φ, IsBaseKernel R i v (ownAt D v) ω φ → ∃ χ ξR, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i v hv hmu ω φ hK
  obtain ⟨χ, ξR, hchr, hres, hweil, hvec⟩ := hK
  have hD := GlobalTheory.BigOn.isDelta_delAt_ownAt R.C v
  obtain ⟨ψ, Qw, hψ, hxi⟩ := hmu v hv
  have hL := hC.lev
  have hmem : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), ((n : 𝓞 D.host.E) ∈ P.asIdeal ↔ Formalism.EigenvalueLevelCeiling.plc P ∣ n) :=
    fun P n => by
      unfold Formalism.EigenvalueLevelCeiling.plc
      rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  have hstar : ∀ (n : ℕ) (c : 𝓞 D.host.E), (c : D.host.E) = star ((n : 𝓞 D.host.E) : D.host.E) → c = n := by
    intro n c h
    apply RingOfIntegers.coe_injective
    refine h.trans ?_
    simp
  refine ⟨χ, ξR, ⟨hchr, hD.fin, hD.triv, hD.tame, ?_, ?_, ?_, hres, hweil, hvec⟩⟩
  · intro PP hP
    have hP' := (Finset.mem_filter.1 hP).1
    exact ⟨(hL.Q_pl _ PP hP').1, fun PP' hP'' => (hL.Q_pl _ PP hP').2 PP' (Finset.mem_filter.1 hP'').1⟩
  · intro PP hP
    exact (hL.Q_off _ PP (Finset.mem_filter.1 hP).1).1
  · intro PP
    constructor
    · intro hnu
      have hover : ((ownAt D v : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
        by_contra h
        exact hnu (hD.unr PP h)
      have hram : ¬ (R.xiH (R.mu v)).UnrAt PP := by
        rw [hxi]
        intro hu
        obtain ⟨a, ha⟩ := hψ.ord
        have h15 : 15 ∣ Formalism.EigenvalueLevelCeiling.plc v ^ a := by
          refine (hD.ine PP hover _).1 fun x hx => ?_
          have h1 := hu x hx
          have loc_mul (a b : Formalism.L2.Host.HChar D.host.E) :
              (a * b).loc PP x = a.loc PP x * b.loc PP x := rfl
          rw [loc_mul] at h1
          have h2 : ψ.loc PP x ^ (Formalism.EigenvalueLevelCeiling.plc v ^ a) = 1 := by
            have h3 := congrArg (fun χ' : Formalism.L2.Host.HChar D.host.E => χ'.loc PP x) ha
            exact h3
          rw [eq_inv_of_mul_eq_one_left h1, inv_pow, h2, inv_one]
        have hl := Formalism.EigenvalueLevelCeiling.plc_prime v
        have h3 : 3 = Formalism.EigenvalueLevelCeiling.plc v := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1
          (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
        have h5 : 5 = Formalism.EigenvalueLevelCeiling.plc v := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hl).1
          (Nat.prime_five.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
        omega
      rcases (hL.Q_ram _ PP).1 hram with h | ⟨PP', h, hc⟩
      · exact Or.inl (Finset.mem_filter.2 ⟨h, hover⟩)
      · refine Or.inr ⟨PP', Finset.mem_filter.2 ⟨h, ?_⟩, hc⟩
        obtain ⟨c', hc', he⟩ := hc _ ((hmem PP' _).2 dvd_rfl)
        rw [hstar _ _ he, hmem] at hc'
        have heq := (Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime PP) (Formalism.EigenvalueLevelCeiling.plc_prime PP')).1 hc'
        rw [hmem] at hover ⊢
        exact heq ▸ hover
    · intro h hu
      have hover : ((ownAt D v : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
        rcases h with h | ⟨PP', h, hc⟩
        · exact (Finset.mem_filter.1 h).2
        · obtain ⟨c', hc', he⟩ := hc _ (Finset.mem_filter.1 h).2
          rwa [hstar _ _ he] at hc'
      have h1 := (hD.ine PP hover 1).1 fun x hx => by rw [pow_one]; exact hu x hx
      norm_num at h1

end GlobalTheory.OnBaseKer

end
end

section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem isNil_frobenius_chart : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hmap k e hbas hadp U hU
  set M := U * blk d k (p : F.B) 1 with hM
  let T : (Fin d ⊕ Fin k → F.B) → (Fin d ⊕ Fin k → F.B) := fun w => M.mulVec fun j => F.σ (w j)
  have hp : ¬IsUnit (p : O) := Fact.out
  have hθp : F.θ (p : F.B) = (p : O) := map_natCast _ _
  have nu_iff : ∀ x : O, ¬IsUnit x ↔ v (algebraMap O C x) < 1 := fun x => by
    rw [hv.isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne (hv.map_le_one x) h, fun h => h.ne⟩
  have nu_add : ∀ x y : O, ¬IsUnit x → ¬IsUnit y → ¬IsUnit (x + y) := by
    intro x y hx hy
    rw [nu_iff] at hx hy ⊢
    rw [map_add (f := _)]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  have nu_sum : ∀ (s : Finset (Fin d ⊕ Fin k)) (f : Fin d ⊕ Fin k → O),
      (∀ i ∈ s, ¬IsUnit (f i)) → ¬IsUnit (∑ i ∈ s, f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using not_isUnit_zero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact nu_add _ _ (hf a (Finset.mem_insert_self _ _))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  have stepA : ∀ w : Fin d ⊕ Fin k → F.B, (∀ j, ¬IsUnit (F.θ (w (Sum.inr j)))) →
      ∀ i, ¬IsUnit (F.θ (T w i)) := by
    intro w hw i
    show ¬IsUnit (F.θ (∑ l, M i l * F.σ (w l)))

    rw [map_sum]
    apply nu_sum
    intro l _
    rw [hM, blk, Matrix.mul_diagonal]
    cases l with
    | inl l =>
      simp only [Sum.elim_inl, map_mul, hθp]
      exact fun h => hp (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h))
    | inr j =>
      simp only [Sum.elim_inr, mul_one, map_mul]
      obtain ⟨c', hc'⟩ := F.σ_pow (w (Sum.inr j))
      have hs : F.θ (F.σ (w (Sum.inr j))) = F.θ (w (Sum.inr j)) ^ p + p * F.θ c' := by
        have := congrArg F.θ hc'
        rw [map_sub, map_mul, map_pow, hθp] at this
        linear_combination this
      rw [hs]
      refine fun h => nu_add _ _ ?_ ?_ (isUnit_of_mul_isUnit_right h)
      · exact fun h' => hw j ((isUnit_pow_iff (Fact.out : p.Prime).ne_zero).1 h')
      · exact fun h' => hp (isUnit_of_mul_isUnit_left h')
  have hQL : ∀ w : Fin d ⊕ Fin k → F.B, QL μ' ⊤ (comb w e) := fun w => GlobalTheory.T.isQuasiLogarithmModIdeal_top_linearCombination _ _ _ F.θ d μ' hlift _ e hbas.1 w
  have hstep : ∀ w : Fin d ⊕ Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (comb w e) - comb (T w) e) :=
    fun w => GlobalTheory.T.powerSeriesFrobeniusTwist_linearCombination_mod_integral p F.B F.Q F.σ F.s F.s_alg d _ e M hU w
  have hlf : ∀ w : Fin d ⊕ Fin k → F.B, ∃ a : MvPowerSeries (Fin d) F.B,
      map (algebraMap F.B F.Q) a = defect μ' p (comb w e) := by
    intro w
    have h := (QLogDefect.main p F.B O F.Q F.θ F.frame d μ' hlift ⊤ _ (hQL w) p).1
    choose b _ hb using h
    refine ⟨(fun α => b α : MvPowerSeries (Fin d) F.B), MvPowerSeries.ext fun α => ?_⟩
    exact (hb α).symm
  choose A hA using hlf
  let δ : (Fin d ⊕ Fin k → F.B) → G.A 1 := fun w => c.ev 1 (map F.θ (A w))
  set I := Ideal.span (algebraMap O (G.A 1) '' {o | ¬IsUnit o}) with hI
  have hδstep : ∀ w : Fin d ⊕ Fin k → F.B, δ (T w) - δ w ^ p ∈ I := fun w =>
    GlobalTheory.T.quasiLogarithm_levelOne_defect_frobenius_pow p C v O hv ε hε F G d c μ' hlift hmap _ _ _ _ (hQL w) (hQL (T w)) (hstep w) (hA w) (hA (T w))
  have hδit : ∀ n w, δ (T^[n] w) - δ w ^ (p ^ n) ∈ I := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', pow_succ, pow_mul]
      have h1 := hδstep (T^[n] w)
      have h2 : δ (T^[n] w) ^ p - (δ w ^ p ^ n) ^ p ∈ I :=
        I.mem_of_dvd (sub_dvd_pow_sub_pow _ _ p) (ih w)
      have := I.add_mem h1 h2
      rwa [sub_add_sub_cancel] at this
  have hconst : ∀ w : Fin d ⊕ Fin k → F.B, constantCoeff (map F.θ (A w)) = 0 := by
    intro w
    have h0 := GlobalTheory.T.constantCoeff_quasiLogarithmMultiplicationDefect p F.B O F.Q F.θ F.frame d μ' hlift _ (hQL w) p
    rw [← hA w, MvPowerSeries.constantCoeff_map] at h0
    have h2 : constantCoeff (A w) = 0 := F.frame.inj (by rw [h0, map_zero])
    rw [MvPowerSeries.constantCoeff_map, h2, map_zero]
  obtain ⟨N0, hN0⟩ := GlobalTheory.T.exists_pDivGroupChart_level_one_nilpotent_mod_p p O G d c
  have hsmallp : ∀ x : G.A 1, (p : G.A 1) ∣ x → x ∈ I := by
    rintro x ⟨y, rfl⟩
    apply I.mul_mem_right
    apply Ideal.subset_span
    exact ⟨(p : O), hp, map_natCast _ _⟩
  have hδ0 : ∀ w : Fin d ⊕ Fin k → F.B, δ w ^ (p ^ N0) ∈ I := by
    intro w
    apply hsmallp
    have hle : N0 ≤ p ^ N0 := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    rw [← Nat.sub_add_cancel hle, pow_add]
    exact Dvd.dvd.mul_left (hN0 _ (hconst w)) _
  refine ⟨N0 + 1, fun w i => ?_⟩
  rw [Function.iterate_succ_apply']
  apply stepA
  intro j
  apply GlobalTheory.T.levelOne_defects_independent_mod_maximal p C v O hv ε hε F G d c μ' hlift hmap k e hbas hadp _ (A _) (hA _)
  have := I.add_mem (hδit N0 w) (hδ0 w)
  rwa [sub_add_cancel] at this

end GlobalTheory.QLog
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FrobUnit

theorem isUnit_of_isUnit_map {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q] [CommRing O]
    [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) (b : B) (hb : IsUnit (θ b)) : IsUnit b := by
  obtain ⟨u, hu⟩ := hb
  obtain ⟨b', hb'⟩ := hF.surj (↑u⁻¹ : O)
  have hx0 : θ (b * b' - 1) = 0 := by
    rw [map_sub, map_mul, hb', ← hu, map_one, Units.mul_inv, sub_self]
  obtain ⟨y, -, hy⟩ := hF.pd _ hx0
  haveI := hF.complete
  have hj : (p : B) * y ∈ (⊥ : Ideal B).jacobson :=
    IsAdicComplete.le_jacobson_bot _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton (p : B))))
  have hu1 := (Ideal.mem_jacobson_bot.1 hj) (-(-1) ^ p)
  have hgeom := mul_neg_geom_sum (-(b * b' - 1)) p
  have h2 : (1 - -(b * b' - 1)) * ∑ i ∈ Finset.range p, (-(b * b' - 1)) ^ i =
      (p : B) * y * (-(-1) ^ p) + 1 := by
    rw [hgeom, neg_pow, hy]; ring
  have h3 : IsUnit (1 - -(b * b' - 1)) := isUnit_of_mul_isUnit_left (h2 ▸ hu1)
  have h4 : (1 - -(b * b' - 1)) = b * b' := by ring
  rw [h4] at h3
  exact isUnit_of_mul_isUnit_left h3

theorem exists_pow_eq {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C]
    {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) (a : O) :
    ∃ r : O, r ^ p = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) (Fact.out : p.Prime).pos
  have h1 : v z ≤ 1 := by
    have := hv.map_le_one a
    rw [← hz, map_pow] at this
    exact (pow_le_one_iff_of_nonneg zero_le' (Fact.out : p.Prime).ne_zero).1 this
  obtain ⟨r, hr⟩ := hv.exists_of_le_one h1
  exact ⟨r, hv.hom_inj (by rw [map_pow, hr, hz])⟩

theorem frob_matrix_isUnit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsUnit U := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hμ k e hB hA U hU
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hm : ∀ x : O, ¬IsUnit x ↔ x ∈ IsLocalRing.maximalIdeal O := fun x =>
    (IsLocalRing.mem_maximalIdeal x).symm
  have hpm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (hm _).1 (Fact.out)
  have hσ : ∀ b, ∃ z, F.σ b = b ^ p + (p : F.B) * z := fun b => by
    obtain ⟨z, hz⟩ := F.σ_pow b
    exact ⟨z, by rw [← hz]; ring⟩
  have hσm : ∀ b, F.θ b ∈ IsLocalRing.maximalIdeal O → F.θ (F.σ b) ∈ IsLocalRing.maximalIdeal O := by
    intro b hb
    obtain ⟨z, hz⟩ := hσ b
    rw [hz, map_add (f := _), map_pow, map_mul, map_natCast]
    exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hb _ (Fact.out : p.Prime).pos)
      (Ideal.mul_mem_right _ _ hpm)
  have key : ∀ w : Fin d ⊕ Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ (w j)) l))) →
      ∀ l, ¬IsUnit (F.θ (w l)) := by
    intro w hw
    have h1 := GlobalTheory.T.quasiLog_first_block_small_of_frobenius p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU w hw
    have h2 := GlobalTheory.T.small_mod_maximal_of_frobenius_image_small p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU (fun j => w (Sum.inr j)) (by
      intro l
      rw [hm]
      have hsplit : U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) (fun j => w (Sum.inr j)) :
          Fin d ⊕ Fin k → F.B) j)) l = U.mulVec (fun j => F.σ (w j)) l -
          ∑ m, U l m * F.σ ((Sum.elim (fun i => w (Sum.inl i)) (fun _ => 0) :
            Fin d ⊕ Fin k → F.B) m) := by
        simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← mul_sub]
        refine Finset.sum_congr rfl fun m _ => ?_
        congr 1
        cases m <;> simp
      rw [hsplit, map_sub]
      refine Ideal.sub_mem _ ((hm _).1 (hw l)) ?_

      rw [map_sum]
      refine Ideal.sum_mem _ fun m _ => ?_
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ (hσm _ ?_)
      cases m with
      | inl i => simpa using (hm _).1 (h1 i)
      | inr j => simp)
    intro l
    cases l with
    | inl i => exact h1 i
    | inr j => exact h2 j
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_of_isUnit_map F.frame
  rw [RingHom.map_det]
  by_contra hdet
  set M := (U.map F.θ).map (IsLocalRing.residue O) with hMdef
  have hM : M.det = 0 := by
    rw [show M = (IsLocalRing.residue O).mapMatrix (F.θ.mapMatrix U) from rfl, ← RingHom.map_det]
    exact (IsLocalRing.residue_eq_zero_iff _).2 ((hm _).1 hdet)
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hM
  have hlift : ∀ l, ∃ b : F.B, IsLocalRing.residue O (F.θ b) ^ p = x l := by
    intro l
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (x l)
    obtain ⟨r, hr⟩ := exists_pow_eq (p := p) hv a
    obtain ⟨b, hb⟩ := F.frame.surj r
    exact ⟨b, by rw [hb, ← map_pow, hr, ha]⟩
  choose w hw using hlift
  have hres : ∀ b, IsLocalRing.residue O (F.θ (F.σ b)) = IsLocalRing.residue O (F.θ b) ^ p := by
    intro b
    obtain ⟨z, hz⟩ := hσ b
    rw [hz, map_add (f := _), map_pow, map_mul, map_natCast, map_add (f := _), map_pow, map_mul,
      (IsLocalRing.residue_eq_zero_iff _).2 hpm, zero_mul, add_zero]
  have hk := key w (by
    intro l
    rw [hm, ← IsLocalRing.residue_eq_zero_iff]
    have := congrFun hx l
    simp only [Matrix.mulVec, dotProduct, hMdef, Matrix.map_apply, Pi.zero_apply] at this ⊢

    rw [map_sum, map_sum]
    simpa [hres, hw] using this)
  apply hx0
  funext l
  rw [← hw l, (IsLocalRing.residue_eq_zero_iff _).2 ((hm _).1 (hk l)), zero_pow (Fact.out : p.Prime).ne_zero,
    Pi.zero_apply]

end GlobalTheory.FrobUnit
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.SmallFin

theorem smallSec_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ M : HermLB p, M.smallSec.Finite := by
  intro k _ X _ p D hX M
  obtain ⟨P, hL, -⟩ := GlobalTheory.VolBr.exists_pair M M
  subst hL
  have hrep : P.Rep 1 0 P.L := (GlobalTheory.VolBr.Pair.rep_base k X p P).1
  obtain ⟨e, he, hrange, hnorm, -⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P 1 0 P.L hrep
  have hfin : (P.Bl 1 0 1).Finite := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P 1 0 1
  refine (hfin.preimage he.injOn).subset ?_
  intro u hu
  refine ⟨?_, fun σ y => ?_⟩
  · have hm : e u ∈ Set.range e := Set.mem_range_self u
    rw [hrange] at hm
    exact hm
  have h0 : 0 ≤ P.nu 1 0 σ y (e u) := by
    unfold Pair.nu; positivity
  have h1 : P.nu 1 0 σ y (e u) ^ 2 ≤ 1 := by
    rw [hnorm]; exact hu σ y
  exact (pow_le_one_iff_of_nonneg h0 two_ne_zero).1 h1

end GlobalTheory.SmallFin
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV


theorem _root_.GlobalTheory.T.flatTensor_vanishes_unless_lastRow_bounded : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), 2 ≤ G.m → IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 → ∀ s, valuation k (x (G.m - 1) (topLast G (G.m - 1 + 1)) s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  first | exact @GlobalTheory.FunObj.FlatLast.flatTensor_lastRow_bounded | exact GlobalTheory.FunObj.FlatLast.flatTensor_lastRow_bounded | (intros; apply GlobalTheory.FunObj.FlatLast.flatTensor_lastRow_bounded <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj

open Filter Topology

variable {D : D7}

theorem mem_GLint_of_entries {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem inBasis_apply {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (i j : Fin n') :
    (inBasis h β w x).1 i j = cpt w ((β⁻¹ * x * β).1 (finCongr h i) (finCongr h j)) := rfl

theorem inBasis_mem_KO {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (hx : x ∈ St β) (w : Pl D.host.E) :
    inBasis rfl β w x ∈ KO (Kw w) (Fin n) := by
  obtain ⟨y, rfl⟩ := hx
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
  have hm : ∀ z : GL (Fin n) (Lev.EAf D), z ∈ ({Formalism.L2.DIV.intGL _ _ n y, (Formalism.L2.DIV.intGL _ _ n y)⁻¹} : Set _) →
      ∀ a b, cpt w (z.1 a b) ∈ Formalism.UG.Ov D.host.E w := by
    intro z hz a b
    refine (mem_OA_iff _).1 ?_ w
    rcases hz with rfl | rfl
    · exact (y.1 a b).2
    · rw [← map_inv]; exact ((y⁻¹).1 a b).2
  have e1 : β⁻¹ * Formalism.L2.DIV.frGL β y * β = Formalism.L2.DIV.intGL _ _ n y := by
    simp only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    group
  have e2 : β⁻¹ * (Formalism.L2.DIV.frGL β y)⁻¹ * β = (Formalism.L2.DIV.intGL _ _ n y)⁻¹ := by
    rw [← e1]; group
  refine mem_GLint_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [inBasis_apply, e1]; exact hm _ (Or.inl rfl) _ _
  · rw [← map_inv, inBasis_apply, e2]; exact hm _ (Or.inr rfl) _ _

end GlobalTheory.FunObj
end
end
