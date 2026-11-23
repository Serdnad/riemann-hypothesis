module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle480
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle207
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle462
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle003
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle027
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Mathlib.Data.Matrix.Block
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1964
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle202
import Std.Tactic.BVDecide.Normalize.BitVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTop.BotConstPf

theorem gBig_imp {P R : GP} (hP : GBig P)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → R G μ₀ C x b) : GBig R := by
  obtain ⟨CF0, h1⟩ := hP
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h2⟩ := h1 ε CF hCF
  exact ⟨C0, x0, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (h2 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩

theorem exists_prime_under {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ w.asIdeal := by
  first
  | exact @_root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem
  | exact _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem
  | (apply _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem ..)

theorem lamC_div_norm {p : ℕ} [Fact p.Prime] {u₁ u₂ : ℂ} (h₁ : u₁ ∈ Qbar) (h₂ : u₂ ∈ Qbar)
    (n₁ : ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u₁‖ = 1) (n₂ : ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u₂‖ = 1) :
    u₁ / u₂ ∈ Qbar ∧ ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam (u₁ / u₂)‖ = 1 := by
  have h3 : u₁ / u₂ ∈ Qbar := div_mem h₁ h₂
  refine ⟨h3, fun lam => ?_⟩
  have e : (⟨u₁ / u₂, h3⟩ : Qbar) = ⟨u₁, h₁⟩ / ⟨u₂, h₂⟩ := rfl
  have a := n₁ lam
  have b := n₂ lam
  rw [lamC, dite_eq_left h₁] at a
  rw [lamC, dite_eq_left h₂] at b
  rw [lamC, dite_eq_left h3, e, map_div₀, norm_div, a, b, div_one]

end GlobalTheory.SqTop.BotConstPf

namespace GlobalTheory.SqTop

open BotConstPf

end GlobalTheory.SqTop

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.CMVal GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.ChiGrid

namespace GlobalTheory.SqTop.FieldDatPf

theorem good_prime {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime) (hs : GlobalTheory.Mem.Chr.SplitsC H.E p) :
    ¬ (p : ℤ) ∣ discr H.E ∧ ∀ P : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ P.asIdeal →
      Ideal.absNorm P.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below P) := by
  refine ⟨GlobalTheory.SplitEmbSep.not_dvd_discr_of_split hp _ ((GlobalTheory.Mem.Chr.ncard_places_eq_primesOver hp).symm.trans hs),
    fun P hP => ?_⟩
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Mem.Chr.splitsC_main R H p hp hs P hP
  exact ⟨h1, GlobalTheory.ToricDenom.splits_below H h3⟩

theorem splitsC_of_mod {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime) (h : p % (H.QS * H.q * H.d) = 1) :
    GlobalTheory.Mem.Chr.SplitsC H.E p :=
  (GlobalTheory.HostSplit.split_of_one_mod R H p hp h).1

theorem exists_above {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (OF E)) :
    ∃ P : HeightOneSpectrum (𝓞 E), GlobalTheory.ToricDenom.below P = v := by
  have := v.isMaximal
  obtain ⟨Q, hQ, hv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  exact ⟨⟨Q, hQ.isPrime, hne⟩, HeightOneSpectrum.ext hv.over.symm⟩

theorem natCast_mem_below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    (n : OF E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal ↔ (n : 𝓞 E) ∈ P.asIdeal := by
  show algebraMap (OF E) (𝓞 E) _ ∈ P.asIdeal ↔ _
  rw [map_natCast]

variable {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T}


open Classical in
theorem expIn_condF' (P : Places L) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    expIn (condF P) v = if v ∈ P.S0 then condExp P v else 0 := by
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), v ∉ S →
      ¬ v.asIdeal ∣ ∏ u ∈ S, u.asIdeal ^ condExp P u := fun S hS h => by
    induction S using Finset.induction_on with
    | empty => exact v.prime.not_dvd_one (by simpa using h)
    | @insert u S hu ih =>
      rw [Finset.prod_insert hu] at h
      rcases v.prime.dvd_mul.mp h with h | h
      · have h2 := v.prime.dvd_of_dvd_pow h
        have : v = u := HeightOneSpectrum.ext (associated_iff_eq.1 (v.irreducible.associated_of_dvd u.irreducible h2))
        exact hS (this ▸ Finset.mem_insert_self u S)
      · exact ih (fun hv => hS (Finset.mem_insert_of_mem hv)) h
  show multiplicity v.asIdeal (∏ u ∈ P.S0, u.asIdeal ^ condExp P u) = _
  split_ifs with h
  · rw [← Finset.mul_prod_erase _ _ h]
    refine multiplicity_eq_of_dvd_of_not_dvd (dvd_mul_right _ _) fun h' => ?_
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ v.ne_bot)] at h'
    exact key _ (Finset.notMem_erase _ _) h'
  · exact multiplicity_eq_zero_of_not_dvd (key _ h)

theorem isBaseCond_condF (P : Places L) (hg : ∀ i, D.host.g i % LevelStarExponents.condE D = 1)
    (hpde : ((Ideal.span {(D.host.pde : ℤ)}).primesOver (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧
      ((Ideal.span {(D.host.pde' : ℤ)}).primesOver (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E) :
    IsBaseCond (condF P) := by
  classical
  have hE : 1 < LevelStarExponents.condE D := by
    have := D.host.qd_big
    unfold LevelStarExponents.condE
    have h1 : 1 ≤ D.host.QS := D.host.QS_pos
    have h2 : 1 < D.host.q := by omega
    have h3 : 1 ≤ D.host.d := by omega
    calc 1 < 1 * D.host.q * 1 := by omega
      _ ≤ D.host.QS * D.host.q * D.host.d := by gcongr

  have hgood : ∀ p : ℕ, (p = D.host.g 0 ∨ p = D.host.g 1 ∨ p = D.host.pde ∨ p = D.host.pde' ∨ p = q0 D) →
      p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧ ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
        (p : 𝓞 D.host.E) ∈ Q.asIdeal → Ideal.absNorm Q.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below Q) := by
    have ofMod : ∀ p : ℕ, p.Prime → p % LevelStarExponents.condE D = 1 → p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧
        ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ Q.asIdeal →
          Ideal.absNorm Q.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below Q) := by
      intro p hp hm
      have h4 : p % 4 = 1 := by
        have : (4 : ℕ) ∣ LevelStarExponents.condE D := ((dvd_trans (by norm_num) (UpperTheory.Ram.Rd.sixteen_dvd_QS D.host)).mul_right _).mul_right _
        rw [← Nat.mod_mod_of_dvd p this, hm]
      refine ⟨hp, by omega, good_prime D.host hp (splitsC_of_mod D.host hp hm)⟩
    have ofSplit : ∀ p : ℕ, p.Prime → p % 15 = 1 →
        ((Ideal.span {(p : ℤ)}).primesOver (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E →
        p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧
        ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ Q.asIdeal →
          Ideal.absNorm Q.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below Q) := by
      intro p hp h15 hs
      have hs' : GlobalTheory.Mem.Chr.SplitsC D.host.E p := by
        have e := GlobalTheory.HostSplit.ncard_placesOver D.host.E hp
        rw [hs] at e
        exact e
      exact ⟨hp, by omega, good_prime D.host hp hs'⟩
    rintro p (rfl | rfl | rfl | rfl | rfl)
    · exact ofMod _ (D.host.g_prime 0) (hg 0)
    · exact ofMod _ (D.host.g_prime 1) (hg 1)
    · exact ofSplit _ D.host.pde_prime D.host.pde_mod.1 hpde.1
    · exact ofSplit _ D.host.pde'_prime D.host.pde_mod.2 hpde.2
    · obtain ⟨hq, hqm, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
      refine ofMod _ hq ?_
      rw [← Nat.mod_mod_of_dvd _ (dvd_mul_left (LevelStarExponents.condE D) (Formalism.MainNotions.rPrAv D)), hqm]
      exact Nat.mod_eq_of_lt hE
  have hexp : ∀ v : HeightOneSpectrum (OF D.host.E), v.asIdeal ∣ condF P → v ∈ P.S0 := by
    intro v hv
    by_contra h
    have e := expIn_condF' P v
    rw [if_neg h] at e
    have hne : condF P ≠ 0 := Finset.prod_ne_zero_iff.2 fun u _ => pow_ne_zero _ u.ne_bot
    have := (multiplicity_eq_zero (FiniteMultiplicity.of_prime_left v.prime hne)).1 e
    exact this hv
  refine ⟨?_, ?_, fun v hv => ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ v.ne_bot
  · intro e
    have h0 : P.v0 ∈ P.S0 := P.mem_S0_of_sum_eq.2 (Or.inl rfl)
    have e1 := expIn_condF' P P.v0
    rw [if_pos h0, condExp, if_pos rfl] at e1
    have e2 : expIn (condF P) P.v0 = 0 := by
      rw [e]; exact multiplicity_eq_zero_of_not_dvd fun h => P.v0.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd h))
    omega
  · have hS := hexp v hv
    have hle : expIn (condF P) v ≤ 2 := by
      rw [expIn_condF', if_pos hS, condExp]; split_ifs <;> omega
    obtain ⟨p, hp, hpv⟩ : ∃ p : ℕ, (p = D.host.g 0 ∨ p = D.host.g 1 ∨ p = D.host.pde ∨ p = D.host.pde' ∨ p = q0 D) ∧
        (p : OF D.host.E) ∈ v.asIdeal := by
      rcases P.mem_S0_of_sum_eq.1 hS with h | h
      · exact ⟨q0 D, Or.inr (Or.inr (Or.inr (Or.inr rfl))), h ▸ P.basePlace_over_qZero⟩
      · rcases (S1_mem_OmF D).1 h with h | h | h | h
        · exact ⟨_, Or.inl rfl, h⟩
        · exact ⟨_, Or.inr (Or.inl rfl), h⟩
        · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), h⟩
        · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), h⟩
    obtain ⟨h1, h2, h3, h4⟩ := hgood p hp
    obtain ⟨Q, rfl⟩ := exists_above v
    exact ⟨(h4 Q ((natCast_mem_below Q p).1 hpv)).2, hle, p, h1, h2, hpv, h3, fun Q' hQ' => (h4 Q' hQ').1⟩

theorem isCMType_cmPhi (D : D7) : IsCMType (cmPhi D) ∧ ∀ τ τ', cmPhi D τ D.host.sqrtMinusD = cmPhi D τ' D.host.sqrtMinusD := by
  obtain ⟨hcm, hsq⟩ := GlobalTheory.LamTie.CMType.phi_cmType D.R D.host
  have e : ∀ τ, cmPhi D τ = GlobalTheory.LamTie.phi D.host (D.eTau τ) := fun _ => rfl
  refine ⟨fun σ => ?_, fun τ τ' => by rw [e, e]; exact hsq _ _⟩
  obtain ⟨g, hg, hu⟩ := hcm σ
  refine ⟨D.eTau.symm g, ?_, fun τ hτ => ?_⟩
  · simp only [e, Equiv.apply_symm_apply]
    exact hg
  · have hτ' : σ = GlobalTheory.LamTie.phi D.host (D.eTau τ) ∨ σ = ComplexEmbedding.conjugate (GlobalTheory.LamTie.phi D.host (D.eTau τ)) := by
      simpa only [e] using hτ
    rw [← hu _ hτ', Equiv.symm_apply_apply]

end GlobalTheory.SqTop.FieldDatPf

namespace GlobalTheory.SqTop

theorem fieldDat : FieldDat := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ _ G => ?_⟩⟩
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  obtain ⟨hcm, hsq⟩ := FieldDatPf.isCMType_cmPhi D
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  exact ⟨D.host.isCMField_hostE, GlobalTheory.ToricDenomBridge.host_isAbelianGalois D.host,
    GlobalTheory.ToricDenomBridge.isFieldData_host D.host hcm hsq, FieldDatPf.isBaseCond_condF G.pl Pm.g_mod Pm.pde_split,
    GlobalTheory.ToricDenom.ringPair D.host.d hd,
    GlobalTheory.ToricDenomBridge.isIntLattice_of D.host.hyp.2.1 (by have := D.host.hyp.2.2.2.1; omega) rfl rfl⟩

end GlobalTheory.SqTop

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageDict

open GlobalTheory.ChainFr Matrix

variable {D : D7}

theorem jm_eq_diag {k p : ℕ} {ε : Fin k → ℝ} (h : ∀ a : Fin k, (ε a = 1 ∧ a.val < p) ∨ (ε a = -1 ∧ p ≤ a.val)) :
    Formalism.REAL.Jm (fun a : Fin k => decide (a.val < p)) = Matrix.diagonal (fun a => (ε a : ℂ)) := by
  unfold Formalism.REAL.Jm
  congr 1
  funext a
  rcases h a with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · have : ¬ a.val < p := by omega
    simp [h1, this]

theorem isUnit_of_isONBasis {k p : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G s B p) : IsUnit B := by
  obtain ⟨ε, hε, h1, -⟩ := h
  have hd : IsUnit (Matrix.diagonal fun a => (ε a : ℂ)).det := by
    rw [Matrix.det_diagonal]
    refine IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
    rcases hε a with ⟨e, -⟩ | ⟨e, -⟩ <;> simp [e]
  rw [← h1, Matrix.det_mul, Matrix.det_mul] at hd
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_mul_isUnit_right hd

def sigIdx {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : ℕ := Classical.choose (h.2.2 τ).2

theorem sigIdx_spec {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    IsONBasis (gramAt D V τ) (r.s τ) (r.B τ) (sigIdx r h τ) := Classical.choose_spec (h.2.2 τ).2

def rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) : Fr V where
  ε τ a := decide (a.val < sigIdx r h τ)
  fr τ := (r.B τ)⁻¹
  fr_unit τ := by
    have hu := isUnit_of_isONBasis (sigIdx_spec r h τ)
    exact (Matrix.isUnit_nonsing_inv_iff).2 hu
  fr_gram τ := by
    have hu := isUnit_of_isONBasis (sigIdx_spec r h τ)
    obtain ⟨ε, hε, h1, -⟩ := sigIdx_spec r h τ
    rw [jm_eq_diag hε, ← h1, Matrix.conjTranspose_nonsing_inv]
    have hu' : IsUnit (r.B τ)ᴴ.det := by
      rw [Matrix.det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).star
    have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hu
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu0, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hu', Matrix.one_mul]

theorem onb_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : (rigFr r h).onb τ = r.B τ := by
  have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_isONBasis (sigIdx_spec r h τ))
  simp only [Fr.onb, rigFr]
  exact Matrix.nonsing_inv_nonsing_inv _ hu0

theorem cart_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : (rigFr r h).cart τ = r.s τ := by
  have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_isONBasis (sigIdx_spec r h τ))
  obtain ⟨ε, hε, -, h2⟩ := sigIdx_spec r h τ
  simp only [Fr.cart, rigFr]
  rw [Matrix.nonsing_inv_nonsing_inv _ hu0, jm_eq_diag hε, ← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu0, Matrix.mul_one]

theorem cart_frSgn_true_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    (GlobalTheory.SquareComm.frSgn true (rigFr r h)).cart τ = -r.s τ := by
  rw [← cart_rigFr r h τ]
  simp only [Fr.cart, GlobalTheory.SquareComm.frSgn]
  have e' : Formalism.REAL.Jm (fun a => xor true ((rigFr r h).ε τ a)) = -Formalism.REAL.Jm ((rigFr r h).ε τ) := by
    ext a b
    by_cases hab : a = b
    · subst hab; cases h' : (rigFr r h).ε τ a <;> simp [Formalism.REAL.Jm, h']
    · simp [Formalism.REAL.Jm, hab]
  rw [e', Matrix.mul_neg, Matrix.neg_mul]

theorem cart_frSgn_false_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    (GlobalTheory.SquareComm.frSgn false (rigFr r h)).cart τ = r.s τ := by
  rw [← cart_rigFr r h τ]
  simp [Fr.cart, GlobalTheory.SquareComm.frSgn]

theorem stage_sizes (i j : Fin D.R.m) {p q a a' : ℕ} (hp : p ≤ pp D j) (hq : q ≤ qq D j)
    (ha : a + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p) (ha' : a' + 2 * qq D j = rankV D i j + 2 * q) :
    Even (a + a') ∧ a' + 2 * (2 * (p + q) + 1) < a ∧ 2 * (p + q) + 1 < a' ∧
      a + a' ≤ rankV D (i + 1) (j + 1) + rankV D i j := by
  obtain ⟨u, hu⟩ := D.R.t_odd
  obtain ⟨v, hv⟩ := D.R.m_even
  obtain ⟨w, hw⟩ := D.R.k_even
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have r1 : rankV D i j = D.R.r + j.1 * D.R.t + i.1 * sLen D := rfl
  have r3 : D.R.r = D.R.k + D.R.m - 1 := rfl
  have r4 : sLen D = D.R.r + 6 := rfl
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.three_m_lt_t
  have h3 := D.R.two_le_m
  have hj := j.2
  simp only [pp, qq] at hp hq ha ha'
  refine ⟨Nat.even_iff.2 (by omega), by omega, by omega, by omega⟩

end GlobalTheory.StageDict

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop

namespace GlobalTheory.DiffSOne

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem not_dvd_diff_of_split (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {p : ℕ} (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L)).ncard = Module.finrank ℚ L)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 K) := by
  have h' : ({w : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ w.asIdeal}).ncard = Module.finrank ℚ L := by
    rw [← h, Formalism.L2.SG.Pf.TypedLoc.primesOver_eq L hp]
    exact (Set.ncard_image_of_injective _ fun v w hvw => HeightOneSpectrum.ext hvw).symm
  obtain ⟨he, -⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef K L hp h' v hv
  have hvq : v.asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq K hp]; exact ⟨v, hv, rfl⟩
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := hvq.2
  have : v.asIdeal.IsPrime := v.isPrime
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp)] at he
  rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
  exact he

theorem not_dvd_differentIdeal : ∀ {D : D7} (large₂ : SizeData₂ D), Rec large₂ → ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∈ S1 D →
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro D large₂ hR v hv
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  rcases (S1_mem_OmF D).1 hv with h | h | h | h
  · exact Formalism.L2.SG.Pf.FibD.not_dvd_diff v 0 h
  · exact Formalism.L2.SG.Pf.FibD.not_dvd_diff v 1 h
  · exact not_dvd_diff_of_split D.host.F D.host.E D.host.pde_prime Pm.pde_split.1 v h
  · exact not_dvd_diff_of_split D.host.F D.host.E D.host.pde'_prime Pm.pde_split.2 v h

end GlobalTheory.DiffSOne
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.AnnCompactStdChar

theorem isCompact_annihilator_of_isStdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
      IsCompact {x : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F | ∀ y ∈ L, ψ (pairA D.host.F 0 (x ⬝ᵥ y)) = 1} := by
  intro D ψ hψ κ _ L hL
  exact GlobalTheory.AnnCompactStd.isCompact_annihilator D.host.F ψ (GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ) κ L hL

end GlobalTheory.AnnCompactStdChar
end

section

open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

theorem _root_.GlobalTheory.T.exists_finiteAdelicHaar_integralPoints_one : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)],
    ∃ μf : Measure (κ → Af F), μf.IsAddHaarMeasure ∧ μf {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), evalV F v (y i) ∈ v.adicCompletionIntegers F} = 1 := by
  first | exact @GlobalTheory.FinAdeleHaarNorm.exists_addHaar_integral_eq_one | exact GlobalTheory.FinAdeleHaarNorm.exists_addHaar_integral_eq_one | (intros; apply GlobalTheory.FinAdeleHaarNorm.exists_addHaar_integral_eq_one <;> assumption)
end

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

theorem _root_.GlobalTheory.T.symplecticGroup_generated_levi_lowerUnipotent_weyl : ∀ (K : Type) [Field K] (κ : Type) [Fintype κ] [DecidableEq κ] (P : Matrix (κ ⊕ κ) (κ ⊕ κ) K → Prop),
    (∀ a b, P a → P b → P (a * b)) → (∀ g h : Matrix κ κ K, gᵀ * h = 1 → P (Matrix.fromBlocks g 0 0 h)) →
    (∀ b : Matrix κ κ K, bᵀ = b → P (Matrix.fromBlocks 1 0 b 1)) → P (Matrix.fromBlocks 0 1 (-1) 0) →
    ∀ a : Matrix (κ ⊕ κ) (κ ⊕ κ) K, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → P a := by
  first | exact @GlobalTheory.SpGen.symplectic_generated_levi_lower_weyl | exact GlobalTheory.SpGen.symplectic_generated_levi_lower_weyl | (intros; apply GlobalTheory.SpGen.symplectic_generated_levi_lower_weyl <;> assumption)
end
