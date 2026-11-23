module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.MapUgCToUg
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle226
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle227
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle228
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle096
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle185
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle197
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle184
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle174
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle038
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIsAdicComplete
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle037
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle035
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle229
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EpsRootProof

variable {l : ℕ} [hl : Fact l.Prime]

theorem iterate_symm_ofCompatible (y : ℕ → OC l) (hy : ∀ k, y (k + 1) ^ l = y k) (n : ℕ) :
    ((_root_.frobeniusEquiv (Ob l) l).symm^[n]) (IsPerfectoidField.ofCompatible l y hy) =
      IsPerfectoidField.ofCompatible l (fun k => y (k + n))
        (fun k => by rw [show k + 1 + n = (k + n) + 1 by omega]; exact hy (k + n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, AInf.frobeniusEquiv_symm_ofCompatible]
    congr 1
    funext k
    exact congrArg y (by omega)

theorem iterate_symm_pow (x : Ob l) (n : ℕ) :
    (((_root_.frobeniusEquiv (Ob l) l).symm^[n]) x) ^ l ^ n = x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p, ih]

theorem untilt_iterate_symm_epsilon (n : ℕ) :
    PreTilt.untilt (((_root_.frobeniusEquiv (Ob l) l).symm^[n]) (epsilon l)) = rootSeqInt l n := by
  rw [epsilon, iterate_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible, zero_add]

theorem sharp_s_eq_oC_untilt (A : PAlg l) (x : Ob l) : A.sharp (A.s x) = A.oC (PreTilt.untilt x) := by
  have h : WittVector.teichmuller l (A.s x) = A.sW (WittVector.teichmuller l x) :=
    (WittVector.map_teichmuller l A.s x).symm
  change A.th (WittVector.teichmuller l (A.s x)) = _
  rw [h, ← PAlg.oC_theta0]
  exact congrArg A.oC (WittVector.fontaineTheta_teichmuller _)

theorem epsRoot : CrystallineSemistableComparison.E.EpsRoot := by
  intro l _ n
  exact ⟨((_root_.frobeniusEquiv (Ob l) l).symm^[n]) (epsilon l), iterate_symm_pow _ n, fun A => by
    rw [sharp_s_eq_oC_untilt, untilt_iterate_symm_epsilon]⟩

end GlobalTheory.CompanionTheory.EpsRootProof
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LcNatProof

theorem natCast_val_castHom {R : Type} [CommRing R] (l n : ℕ) [NeZero (l ^ n)] [NeZero (l ^ (n + 1))]
    (h : (l : R) ^ n = 0) (a : ZMod (l ^ (n + 1))) :
    (((ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))) a).val : R) = (a.val : R) := by
  have key : (((ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))) a).val : ZMod (l ^ n)) =
      (a.val : ZMod (l ^ n)) := by
    rw [ZMod.natCast_zmod_val, ← map_natCast (ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))),
      ZMod.natCast_zmod_val]
  obtain ⟨c, hc⟩ := Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 key)
  have e := congrArg (Int.cast : ℤ → R) hc
  push_cast at e
  rw [h, zero_mul, sub_eq_zero] at e
  exact e.symm

variable {l : ℕ} [Fact l.Prime]

theorem sum_toAcr_teichmuller (A : PAlg l) {ι : Type} [Fintype ι] {e : ι → A.A}
    (he : CompleteOrthogonalIdempotents e) (n : ℕ) :
    ∑ a, A.toAcr n (WittVector.teichmuller l (e a)) = 1 := by
  have hO : OrthogonalIdempotents (fun a => (WittVector.teichmuller l (e a) : A.W)) :=
    { idem := fun a => by
        change WittVector.teichmuller l (e a) * WittVector.teichmuller l (e a) = WittVector.teichmuller l (e a)
        rw [← map_mul, (he.idem a).eq]
      ortho := fun i j hij => by
        change WittVector.teichmuller l (e i) * WittVector.teichmuller l (e j) = 0
        rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero] }
  have hE : IsIdempotentElem (∑ a, (WittVector.teichmuller l (e a) : A.W)) := hO.isIdempotentElem_sum
  have hu : IsIdempotentElem (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)) := hE.one_sub
  have hc : (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)).coeff 0 = 0 := by

    rw [← WittVector.constantCoeff_apply, map_sub, map_one, map_sum]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [he.complete, sub_self]
  obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff _).2 hc)
  have ht : IsIdempotentElem (A.toAcr n (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W))) := hu.map (A.toAcr n)
  have h0 : A.toAcr n (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)) = 0 := by
    rw [← ht.pow_succ_eq n, ← hc', map_mul, map_natCast, mul_pow, pow_succ (l : A.Acr n) n, A.pow_l_acr n,
      zero_mul, mul_zero]

  rw [map_sub, map_one, map_sum, sub_eq_zero] at h0
  exact h0.symm

theorem lcNat : LcIdem → LcSpec → LcNat := by
  intro hId hSp l _ H A hA n
  refine ⟨?_, ?_⟩
  · intro B hB φ h g hg f
    obtain ⟨e, he, hcut, -⟩ := hId l H A hA (ZMod (l ^ n)) f
    have h1 := (hSp l H A hA n).2.2.2 f e he (fun a p => (hcut a p).1)
    have hφ : CompleteOrthogonalIdempotents (φ ∘ e) := he.map φ
    have h2 := (hSp l H B hB n).2.2.2 (lcRes _ (Spec.map (CommRingCat.ofHom g)) f) (φ ∘ e) hφ (fun a p hp => by
      refine (hcut a (PrimeSpectrum.comap g p)).1 fun hm => hp ?_
      have := hg (e a) (he.idem a)
      change algebraMap B.U B.Ug (B.sharp (φ (e a))) ∈ p.asIdeal
      rw [← this]
      exact hm)

    rw [h1, h2, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, PAlg.PdOk.acr_toAcr, WittVector.map_teichmuller, map_natCast]
    rfl
  · intro f
    obtain ⟨e, he, hcut, -⟩ := hId l H A hA (ZMod (l ^ (n + 1))) f
    have h1 := (hSp l H A hA (n + 1)).2.2.2 f e he (fun a p => (hcut a p).1)
    set c := ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n)) with hcdef
    have hL := (hSp l H A hA n).1 (f.map c)
    have hT : ∀ a, A.toAcr n (WittVector.teichmuller l (e a)) * lcA A n (f.map c) =
        A.toAcr n (WittVector.teichmuller l (e a)) * (a.val : A.Acr n) := fun a => by
      rw [hL (e a) (c a) (he.idem a) (fun p hp => by
        change c (f p) = c a
        rw [(hcut a p).1 hp]), natCast_val_castHom l n (A.pow_l_acr n) a]

    rw [h1, map_sum, ← one_mul (lcA A n (f.map c)), ← sum_toAcr_teichmuller A he n, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hT a, map_mul, map_natCast]
    rfl

end GlobalTheory.CompanionTheory.LcNatProof
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.cech_hodge_to_cohomology_iso : ∀ (R : Type) [CommRing R], ∃ e : ∀ {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type}
    (U : ι → ObjectProperty C), (∀ α, Cosieve (U α)) → (∀ T, ∃ α, U α T) → ∀ a : ℕ,
    (∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) → ∀ j : ℕ,
      CH.H F (a + j) ≃ₗ[R] (cechH F U a).cx.H j,
    ∀ {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R) {ι ι' : Type}
      (U : ι → ObjectProperty C) (U' : ι' → ObjectProperty C') (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T)
      (hU' : ∀ α, Cosieve (U' α)) (hc' : ∀ T, ∃ α, U' α T) (a : ℕ)
      (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r))
      (hv' : ∀ n (i : Fin (n + 1) → ι') r, r ≠ a → Subsingleton (HU F' (capT U' i) r)) (m : CH.Mor F F' (RingHom.id R))
      (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) (j : ℕ) (c : (cechH F U a).X j)
      (h0 : (cechH F U a).cx.d j c = 0)
      (h1 : (cechH F' U' a).cx.d j (fun i => (morU m (U := capT U (τ ∘ i)) (U' := capT U' i)
        fun T hT k => hτ (i k) T (hT k)).pull a (c (τ ∘ i))) = 0),
      m.pull (a + j) ((e F U hU hc a hv j).symm ((cechH F U a).cx.cls c h0)) =
        (e F' U' hU' hc' a hv' j).symm ((cechH F' U' a).cx.cls _ h1) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.cech_deg | exact GlobalTheory.CompanionTheory.CechSerre.cech_deg | (intros; apply GlobalTheory.CompanionTheory.CechSerre.cech_deg <;> assumption)
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_toB_eq_zero_iff_t_pow_dvd : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ x : (per l K).P, (lev h k).toB x = 0 ↔ ∃ y : (per l K).P, (x : (per l K).B) = (per l K).tB ^ k * y := by
  first | exact @GlobalTheory.CompanionTheory.LatC.lev_toB_ker | exact GlobalTheory.CompanionTheory.LatC.lev_toB_ker | (intros; apply GlobalTheory.CompanionTheory.LatC.lev_toB_ker <;> assumption)
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_ideal_eq_map : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), (lev h k).IB = (lev h k).I.map (lev h k).ι := by
  first | exact @GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map | exact GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map | (intros; apply GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map <;> assumption)
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_lam_galois_equivariant : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g c, (lev h k).σA g ((lev h k).lam c) = (lev h k).lam ((per l K).σA g c) := by
  first | exact @GlobalTheory.CompanionTheory.LatCSig.sig_lam | exact GlobalTheory.CompanionTheory.LatCSig.sig_lam | (intros; apply GlobalTheory.CompanionTheory.LatCSig.sig_lam <;> assumption)
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCHc

theorem subsingleton_Bk_zero (l : ℕ) [Fact l.Prime] : Subsingleton (Lat.Bk l 0) := by
  refine Ideal.Quotient.subsingleton_iff.2 ?_
  rw [pow_zero, Ideal.span_singleton_one]

theorem hc_k : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ),
    Lat.DPClosed (Lat.ι (Lat.fk l k) (xi0 l) l M) (Lat.γB (Lat.fk l k) (xi0 l)) := by
  intro l _ M k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · intro x _ n
    haveI := subsingleton_Bk_zero l
    exact ⟨0, Subsingleton.elim _ _⟩
  · exact GlobalTheory.CompanionTheory.LatDP.dpClosed _ _ l M k (GlobalTheory.CompanionTheory.LatCHyp.hyp_k l k hk)

end GlobalTheory.CompanionTheory.LatCHc
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCBase

theorem dividedPowerFiltration_anti {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {k s : ℕ} (h : k ≤ s) :
    pdP δ s ≤ pdP δ k := by
  unfold CrystallineSemistableComparison.Pb.pdP
  refine Ideal.span_mono ?_
  rintro z ⟨L, hL, hs, rfl⟩
  exact ⟨L, hL, h.trans hs, rfl⟩

theorem latBase_lev : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ), 1 ≤ k → ∀ s, k ≤ s → LatBase (lev h k).γ l s := by
  intro l hl K M h k hk s hks
  have H := GlobalTheory.CompanionTheory.LatCHyp.hyp_k l k hk
  show CrystallineSemistableComparison.Pb.LatBase (CrystallineSemistableComparison.Pb.Lat.γ (CrystallineSemistableComparison.Pb.Lat.fk l k) (CrystallineSemistableComparison.xi0 l) l M (h.hc k)) l s
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_bot_iff.mp ((dividedPowerFiltration_anti _ hks).trans
      (GlobalTheory.CompanionTheory.LatNil.dividedPowerFiltration_eq_bot _ _ l M k H (h.hc k)).le)
  · exact GlobalTheory.CompanionTheory.Lat.quot_pdP_no_torsion _ _ l M k H (h.hc k)
  · exact GlobalTheory.CompanionTheory.LatticeUnit.natCast_dvd_pow _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatFG.dividedPowerFiltration_fg _ _ l M k H (h.hc k)
  · exact GlobalTheory.CompanionTheory.LatPrime.I_isPrime _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatVal.val _ _ l M k H
  · exact GlobalTheory.CompanionTheory.Lat.pow_mem_span_sup_I _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatCpl.isAdicComplete_A M H
  · exact GlobalTheory.CompanionTheory.LatClosed.closed _ _ l M k H (h.hc k)

end GlobalTheory.CompanionTheory.LatCBase
end
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.acris_mem_lattice_sub : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ) (c : Acris l), Lat.pk l k (ACris.iota ℂ_[l] l c) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatCris.cris_in | exact GlobalTheory.CompanionTheory.LatCris.cris_in | (intros; apply GlobalTheory.CompanionTheory.LatCris.cris_in <;> assumption)
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.existsUnique_period_of_compatible : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M), ∀ y : ∀ m, ((levSys h).L m).B, (∀ m, (levSys h).dB m (y (m + 1)) = y m) → ∃! x : (per l K).P, ∀ m, ((levSys h).L m).toB x = y m := by
  first | exact @GlobalTheory.CompanionTheory.LatC.levSys_existsUnique | exact GlobalTheory.CompanionTheory.LatC.levSys_existsUnique | (intros; apply GlobalTheory.CompanionTheory.LatC.levSys_existsUnique <;> assumption)
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.galois_preserves_lattice_sub : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M k : ℕ) (g : K.fixingSubgroup) (hT : Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g)), ∀ x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M, Ideal.quotientMap _ (Lat.gP l g) hT x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatGal.gal_mem_sub | exact GlobalTheory.CompanionTheory.LatGal.gal_mem_sub | (intros; apply GlobalTheory.CompanionTheory.LatGal.gal_mem_sub <;> assumption)
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.galois_preserves_t_power_span : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (k : ℕ) (g : K.fixingSubgroup), Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g) := by
  first | exact @GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap | exact GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap | (intros; apply GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap <;> assumption)
end
