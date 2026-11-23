module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle267
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle135
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle138
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle427
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle247
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle429
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyResidueFieldUnitBallEquiv
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelTypePlace

theorem not_two_primes {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : p ≠ q) (h1 : (p : R) ∈ P) (h2 : (q : R) ∈ P) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom R)
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact P.add_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)

theorem natCast_mem_of_card {E : Type} [Field E] [NumberField E] (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    {q : ℕ} (hc : Nat.card (𝓞 E ⧸ PP.asIdeal) = q) (hq0 : q ≠ 0) : (q : 𝓞 E) ∈ PP.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
  exact card_nsmul_eq_zero'

theorem offPlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (t : T) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.w ∈ L.Pg → (∀ PP ∈ L.Pg, PP ≠ s.w → ¬ NG.OverPl PP s.v) ∧ (∀ PP ∈ L.Q t, ¬ NG.OverPl PP s.v) ∧ s.w ∉ L.Q t ∧ (L.xiH t).UnrAt s.w := by
  intro D T L μ0 hL hPg t s hs

  have hA : ∀ PP : Pl D.host.E, NG.OverPl PP s.v → ∀ p : ℕ, (p : 𝓞 D.host.E) ∈ s.w.asIdeal →
      (p : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hov p hp
    have h1 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← s.w_under, Ideal.mem_comap, map_natCast]; exact hp
    rw [← hov, Ideal.mem_comap, map_natCast] at h1; exact h1
  have hgne : ∀ k k' : Fin 2, k ≠ k' → D.host.g k ≠ D.host.g k' := by
    intro k k' h
    fin_cases k <;> fin_cases k' <;> first | exact absurd rfl h | exact D.host.g_ne | exact D.host.g_ne.symm
  obtain ⟨k, v, hkv⟩ := (hPg s.w).1 hs
  have hgk : (D.host.g k : 𝓞 D.host.E) ∈ s.w.asIdeal := by rw [hkv]; exact D.naut.plGw_over k v

  have hQ : ∀ PP ∈ L.Q t, (D.host.g k : 𝓞 D.host.E) ∈ PP.asIdeal → False := by
    intro PP hP hg
    obtain ⟨q, hq, hcard, -, hqg⟩ := (hL.Q_pl t PP hP).1
    exact not_two_primes PP.asIdeal (D.host.g_prime k) hq (hqg k).symm hg
      (natCast_mem_of_card PP hcard hq.ne_zero)
  have h3 : s.w ∉ L.Q t := fun h => hQ s.w h hgk
  refine ⟨?_, fun PP hP hov => hQ PP hP (hA PP hov _ hgk), h3, ?_⟩
  · intro PP hP hne hov
    rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s PP hov with e | hc
    · exact hne e.symm
    obtain ⟨k', v', hkv'⟩ := (hPg PP).1 hP
    have hk : k' = k := by
      by_contra hk
      have h1 : (D.host.g k' : 𝓞 D.host.E) ∈ PP.asIdeal := by rw [hkv']; exact D.naut.plGw_over k' v'
      exact not_two_primes PP.asIdeal (D.host.g_prime k') (D.host.g_prime k) (hgne k' k hk) h1
        (hA PP hov _ hgk)
    subst hk
    rw [hkv, hkv'] at hc
    exact D.naut.plGw_nconj k' v' v hc
  · by_contra hn
    rcases (hL.Q_ram t s.w).1 hn with h | ⟨PP', hP', hc⟩
    · exact h3 h
    obtain ⟨q, hq, hcard, -, hqg⟩ := (hL.Q_pl t PP' hP').1
    obtain ⟨c', hc', hcq⟩ := hc _ (natCast_mem_of_card PP' hcard hq.ne_zero)
    have hq' : (q : 𝓞 D.host.E) = c' := by
      apply RingOfIntegers.ext
      rw [hcq]; simp
    exact not_two_primes s.w.asIdeal (D.host.g_prime k) hq (hqg k).symm hgk (hq' ▸ hc')

end GlobalTheory.LevelTypePlace
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.SDFrameStd

theorem lamHat_iff_int : ∀ {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V 1 Λ 1 → ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, y ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ j, swapAE D (y j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D V Λ hβ y
  obtain ⟨c, hf, -, -, h1, h2⟩ := hβ
  have hset : (Λ : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext x
    constructor
    · intro hx
      have := h2 x hx
      simpa using this
    · intro hx
      have := h1 x hx
      simpa using this
  have e1 : y ∈ Formalism.L2.NTheta.LamHat V ↔ (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [← GlobalTheory.LevSplit.latHat_iff Λ y, hset]
  rw [e1, hf]
  simp only [inv_one, Units.val_one, one_mulVec]
  rfl

end GlobalTheory.Mem.SDFrameStd
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2 Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistSplitPlace

theorem isSplitPl_of_not_isConjPl (D : D7) (P : PlE D.host) (h : ¬ Formalism.IndefR.Lev.IsConjPl P P) : IsSplitPl D.host P := by
  unfold Formalism.IndefR.Lev.IsConjPl at h
  push Not at h
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, fun y hy hm => h y hm (hy.trans (GlobalTheory.DimPartsCompare.star_conj _).symm)⟩

theorem exists_splitPlace_of_mem_qPl : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (i : Fin D.R.m) (t : T), ∀ v ∈ qPl D (L.C.mu0 i * L.xiH t), ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.v = v ∧ s.w ∈ L.Q t := by
  rintro D T L μ0 hL i t v ⟨hg, w, hw, hn⟩
  have hu : (L.C.mu0 i).UnrAt w := (L.C.isMu0 i).unr w fun k hk => hg ⟨w, hw, k, hk⟩
  have hx : ¬ (L.xiH t).UnrAt w := fun h => hn fun x hx => by
    simpa [Host.HChar.loc] using congrArg₂ (· * ·) (hu x hx) (h x hx)
  have key : ∀ P ∈ L.Q t, NG.OverPl P v → ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.v = v ∧ s.w ∈ L.Q t := by
    intro P hP hov
    obtain ⟨s, hs⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl D P
      (isSplitPl_of_not_isConjPl D P ((hL.Q_pl t P hP).2 P hP))
    refine ⟨s, HeightOneSpectrum.ext ?_, hs ▸ hP⟩
    rw [← s.w_under, hs]
    exact hov
  rcases (hL.Q_ram t w).1 hx with h | ⟨P, hP, hc⟩
  · exact key w h hw
  · refine key P hP ?_
    rw [GlobalTheory.DimPartsCompare.eq_cPl_of_isConjPl hc]
    exact (congrArg HeightOneSpectrum.asIdeal (GlobalTheory.DimPartsCompare.under_cPl w)).trans hw

end GlobalTheory.TwistSplitPlace
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker GlobalTheory.ThetaMove.Moved

namespace GlobalTheory.Mem.NatEqui

variable {D : D7}

theorem chi_smulLat {χ : IdE D → ℂ} (hχ : IsChi D χ) {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hL : SD D L) : letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E,
      χ (detId D (stdL D n) (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L)) =
        (∏ τ : D.what₂.Tau, (embT D τ (γ : Matrix (Fin n) (Fin n) D.host.E).det)⁻¹) * χ (detId D (stdL D n) L) := by
  letI := D.host.cmStar
  intro γ
  have hst : ∀ x : D.host.E, star x = D.host.conj x := GlobalTheory.NormSum.AdLattice.star_eq_conj D
  let z : unitary D.host.E := ⟨_, Matrix.det_of_mem_unitary γ.2⟩
  rw [GlobalTheory.Mem.Col2.ChiFacLaw.detId_image D (stdL D n) L (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L)
    (γ : Matrix (Fin n) (Fin n) D.host.E)
    (star (γ : Matrix (Fin n) (Fin n) D.host.E)) γ.2.2 (fun x hx => ⟨x, hx, rfl⟩) ?_,
    hχ.1 _ _ (GlobalTheory.Mem.Col2.ChiFacLaw.norm_one_span D z.1 (by rw [← hst]; exact z.2.2))
      (GlobalTheory.RelDetIdeal.detId_normOne_mul D n _ _ _ (sd_stdL D n) hL hL).1, hχ.2 z]
  rintro _ ⟨y, hy, rfl⟩
  change (star (γ : Matrix (Fin n) (Fin n) D.host.E)).mulVec ((γ : Matrix (Fin n) (Fin n) D.host.E).mulVec y) ∈ L
  rwa [Matrix.mulVec_mulVec, γ.2.1, Matrix.one_mulVec]

theorem sd_smulLat {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : SD D L) : letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E, SD D (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L) := by
  intro γ
  obtain ⟨g, hg⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D n L hL
  obtain ⟨γA, hγ⟩ := GlobalTheory.TrueTheta.exists_rat γ
  exact GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.TrueTheta.moves_smulLat hγ hg)

theorem chiFac_ne_zero {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} {L L'} (h : SD D L) (h' : SD D L') :
    Base.chiFac χ N N' L L' ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (chi_detId_ne_zero hχ (sd_stdL D N) h))
    (zpow_ne_zero _ (chi_detId_ne_zero hχ (sd_stdL D N') h'))

theorem chiFac_right {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} (L) {L' L''} (h' : SD D L') (h'' : SD D L'') :
    Base.chiFac χ N N' L L'' = χ (detId D L' L'') ^ (-((N / 2 : ℕ) : ℤ)) * Base.chiFac χ N N' L L' := by
  unfold Base.chiFac
  rw [chi_detId_mul hχ (sd_stdL D N') h' h'', mul_zpow]
  ring

theorem chiFac_left {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} {L L₁} (L') (h : SD D L) (h₁ : SD D L₁) :
    Base.chiFac χ N N' L₁ L' = χ (detId D L L₁) ^ (((N' / 2 : ℕ) : ℤ)) * Base.chiFac χ N N' L L' := by
  unfold Base.chiFac
  rw [chi_detId_mul hχ (sd_stdL D N) h h₁, mul_zpow]
  ring

theorem eqP : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ := by
  intro D cc δ B χ hc hδ hχ
  letI := D.host.cmStar
  have hC : Crv D cc δ := ⟨hc, hδ⟩
  obtain ⟨χ', e, hχ', hv, q1, q2, q3⟩ := GlobalTheory.T.exists_thetaVectorFamily_of_curveDatum D cc δ hC
  have key : ∀ N N', Even N → Even N' → ∃ a : ℂ, ∀ L L', SD D L → SD D L' → B.eNat χ N N' L L' =
      fun z => (a * (Base.chiFac χ N N' L L' / Base.chiFac χ' N N' L L')) * e N N' L L' z := by
    intro N N' hN hN'
    have s := sd_stdL D N
    have s' := sd_stdL D N'
    obtain ⟨v1, v2, -⟩ := hv N N' _ _ ⟨hN, hN', s, s'⟩
    obtain ⟨a, ha⟩ := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC N N' _
      (Or.inr ⟨_, _, s, s', rfl⟩)).1 _
      (GlobalTheory.Mem.Col2.WeilVac.thZero_mem B (GlobalTheory.FourthRootStd.stdOK_of_crv D cc δ B hC) N N') _ v1 v2
    refine ⟨a, fun L L' h h' => funext fun z => ?_⟩
    have e3 := q3 N N' ⟨_, s⟩ ⟨L, h⟩ ⟨_, s'⟩ hN hN'
    have e2 := congrFun (q2 N N' ⟨L, h⟩ ⟨_, s'⟩ ⟨L', h'⟩ hN hN') z
    dsimp only at e2 e3
    rw [e3, iop_mul, ← mul_assoc, mul_comm (χ' _ ^ _)] at e2
    have hh : B.thHalf N N' L = fun w => a * Iop D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) (stdL D N'))
        (La D (tor0 D cc δ) L (stdL D N')) (e N N' (stdL D N) (stdL D N')) w := by
      funext w
      rw [Base.thHalf, ha]
      exact iop_mul D _ _ _ a _ w
    have h0 := chiFac_ne_zero hχ' h h'
    change Base.chiFac χ N N' L L' * B.thMoved N N' L L' z = _
    rw [Base.thMoved, hh, iop_mul, e2]
    change _ = a * (_ / Base.chiFac χ' N N' L L') * (Base.chiFac χ' N N' L L' * _)
    field_simp
  refine ⟨fun N N' L L' hN hN' γ γ' => ?_, fun N N' L L' L'' hN hN' => ?_, fun N N' L L₁ L' hN hN' => ?_⟩
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ (sd_smulLat L.2 γ) (sd_smulLat L'.2 γ'), ← q1 N N' L L' hN hN' γ γ']
    have h1 := chiFac_ne_zero hχ' (sd_smulLat L.2 γ) (sd_smulLat L'.2 γ')
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    funext z
    change _ * pull D _ _ _ (e N N' L.1 L'.1) z = _
    congr 2
    rw [div_eq_div_iff h0 h1]
    unfold Base.chiFac
    rw [chi_smulLat hχ L.2, chi_smulLat hχ L'.2, chi_smulLat hχ' L.2, chi_smulLat hχ' L'.2]
    simp only [mul_zpow]
    ring
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ L.2 L''.2, q2 N N' L L' L'' hN hN']
    funext z
    have h1 := zpow_ne_zero (-((N / 2 : ℕ) : ℤ)) (chi_detId_ne_zero hχ' L'.2 L''.2)
    rw [iop_mul, chiFac_right hχ _ L'.2 L''.2, chiFac_right hχ' _ L'.2 L''.2]
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    generalize χ' _ ^ _ = u at h1 ⊢
    field_simp
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ L₁.2 L'.2, q3 N N' L L₁ L' hN hN']
    funext z
    have h1 := zpow_ne_zero (((N' / 2 : ℕ) : ℤ)) (chi_detId_ne_zero hχ' L.2 L₁.2)
    rw [iop_mul, chiFac_left hχ _ L.2 L₁.2, chiFac_left hχ' _ L.2 L₁.2]
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    generalize χ' _ ^ _ = u at h1 ⊢
    field_simp

end GlobalTheory.Mem.NatEqui
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section
namespace GlobalTheory.TeichPlace

theorem exists_place_isTeich : ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ (A : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g), IsTeich A κ t := by
  intro g _ t ht
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex g
  obtain ⟨κ₀⟩ := GlobalTheory.HeightCounting.nonempty_residueField_unitBall_equiv ι
  obtain ⟨t₀, ht₀, hinj₀⟩ := GlobalTheory.T.exists_teichmuller_reindex_complexPlace g (GlobalTheory.HeightCounting.unitBall ι) κ₀ t ht
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.fbar_exists_complexAut_comp_eq g t t₀ ht hinj₀
  let A : ValuationSubring ℂ := (GlobalTheory.HeightCounting.unitBall ι).comap (σ.symm : ℂ →+* ℂ)
  have hmem : ∀ z : ℂ, z ∈ A ↔ σ.symm z ∈ GlobalTheory.HeightCounting.unitBall ι := fun z => ValuationSubring.mem_comap
  let e : A ≃+* GlobalTheory.HeightCounting.unitBall ι :=
    { toFun := fun a => ⟨σ.symm a, (hmem a).1 a.2⟩
      invFun := fun b => ⟨σ b, (hmem _).2 (by simpa using b.2)⟩
      left_inv := fun a => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  refine ⟨A, (IsLocalRing.ResidueField.mapEquiv e).trans κ₀, fun x => ?_⟩
  have hx : σ.symm (t x) = t₀ x := by rw [← hσ x, RingEquiv.symm_apply_apply]
  obtain ⟨h₀, e₀⟩ := ht₀ x
  refine ⟨(hmem _).2 (hx ▸ h₀), ?_⟩
  refine Eq.trans ?_ e₀
  change κ₀ (IsLocalRing.ResidueField.map (e : A →+* GlobalTheory.HeightCounting.unitBall ι) (IsLocalRing.residue A _)) = _
  rw [IsLocalRing.ResidueField.map_residue]
  congr 2
  exact Subtype.ext hx

end GlobalTheory.TeichPlace
end
end
