module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
public import Formalism.SharpRestriction.CuspSpanNormBounds.AdmissibleBoundsFromSource
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SmoothBigCellSectionsExist
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle031
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PsiCondAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle001
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle029
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle034
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppRedW

@[expose] public section

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.BDatR Formalism.L2.SG.ThmBUseR
  Formalism.L2.SG.Pf.JointAmplitudePoints Formalism.L2.SG.Pf.ThmBChain
open scoped ENNReal

namespace Formalism.L2.SG.Pf.OOCore

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Core

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)

def OOP (w : Point D.host.E (D.R.rS + 1)) : X.Vpi u' →L[ℂ] X.Vpi u :=
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' w)

theorem joint_amplitude_eq_normSq (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) :
    J2of Y u u' ν (toPts w) =
      Complex.normSq ((Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) *
        Formalism.MainNotions.S.hsNormSq (OOP u u' ν w) := by
  have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = toPts w ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g :=
    ⟨w, rfl, hw⟩
  unfold J2of
  rw [dite_eq_left hex]
  have hc : hex.choose = w := toPts_injective hex.choose_spec.1
  rw [hc, Formalism.L2.SG.PackageTie.norm_hsEmb_sq]
  unfold Jw OOP
  rw [Formalism.L2.SG.Pf.LTL.hsNormSq_smul]

variable {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

end Core

end Formalism.L2.SG.Pf.OOCore
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsCountBase

open Finset Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

open Formalism.MainNotions.BridgeLemma NumberField in
theorem splits_X (k : Fin 2) : SplitsCompl X.B.I.E (D.host.g k) := by
  have hp := D.host.g_prime k
  have := span_isMaximal hp
  have hspl := splitsCompl_of_ncard D.host.E (D.host.g k) hp (by
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp,
      (injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k)
  exact Formalism.L2.SG.ThmSOwn.splitsCompl_of_equiv X.ιE hspl

theorem hc_X (hT : AutTie D X.B X.pl) (v : NumberField.InfinitePlace X.B.I.F) : Formalism.QuantumDeterminants.IsHCParam (X.B.lam v) := by
  exact Inh.aut_isHCParam_of_autTie hT v

theorem countBase_of (hT : AutTie D X.B X.pl) {large₂ : SizeData₂ D} {n0 : ℕ} {A C cb : ℝ}
    (hp : AdmissibleBoundsFromSource.CountTheoremHypotheses D large₂ n0 A C cb) (hg1 : 4 * D.R.r < D.host.g 1) : CountBase X n0 A C cb := by
  obtain ⟨-, p2, p3, p4, p5, p6, p7, -, p9, p10, p11, p12⟩ := hp
  have hn := hT.n_eq
  have hf := hT.f_eq
  have hrd := hT.rd_eq
  have tg := X.g_eq
  have hq : ∀ v, X.B.I.pAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = true).card ∧
      X.B.I.qAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = false).card := by
    intro v
    have he := hT.eps_eq v
    constructor
    · simp only [AutInst.pAt, he]
      exact card_cast hn (fun a => epsS D.R a = true)
    · simp only [AutInst.qAt, he]
      exact card_cast hn (fun a => epsS D.R a = false)
  refine ⟨large₂.sc.b, C * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * Real.log (large₂.sc.b * D.host.rdE), fun k => ?_,
    fun v a c hac => ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [hn]; exact p2, ⟨_, _, hq, ?_⟩, p11, ?_, hc_X X hT, ?_, ?_, ?_, D.host.g_prime _, ?_, splits_X X _⟩
    · rw [hn]
      exact le_trans (Nat.pow_le_pow_left card_epsS_false 2) p3
    · rw [hrd, hn]; exact p4
    · intro v a
      rw [hT.lam_eq v a]; exact p5 _ _
    · rw [tg]
      exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
    · rw [tg]
      have : gg D = ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by unfold gg; push_cast; ring
      rw [← this]; exact p6
    · rw [hn]
      fin_cases k
      · exact hg1
      · exact p7
  · rw [hT.lam_eq v a, hT.lam_eq v c]
    exact p9 _ _ _ (by rw [← hT.eps_eq v a, ← hT.eps_eq v c]; exact hac)
  · rw [hn, hf, hrd]
  · rw [hf, hn]; exact p10
  · rw [hf, hn]; exact p12
  · have h := Formalism.MainNotions.BridgeLemma.Dstar_pos D
    rw [hT.Dstar_eq] at h
    exact h

section Fam

open Formalism.MainNotions.S.CountE Formalism.MainNotions.PlaceDegreeData Formalism.L2.SG.ThmSOwn

variable {eps : ℝ} (Fm : FamP eps)

end Fam

end Formalism.L2.SG.Pf.AllRowsCountBase
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.RedBasicsPf

variable {D : D7} (X : HidaSetting D) {kv : Σ k : Fin 2, D.nd.PlG k}

theorem level_mem_wB' (kv : Σ k : Fin 2, D.nd.PlG k) : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal :=
  g_mem_of_gk X (gk_mem X kv)

theorem psiK_ne {ε : 𝓞 X.B.I.E} (hε1 : ε - 1 ∈ (wK X kv).asIdeal)
    (hεP : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv → ε ∈ P.asIdeal)
    (hε : ε ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)}) : psiK X ε hε ≠ 1 := by
  intro h1
  have hp := D.host.g_prime kv.1
  have : NeZero (D.host.g kv.1) := ⟨hp.ne_zero⟩

  have hm : ∀ m : ℕ, X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) = 1 := by
    intro m
    have h2 := congrArg (fun ψ : AddChar (ZMod (D.host.g kv.1)) ℂ => ψ (m : ZMod (D.host.g kv.1))) h1
    simp only [psiK_apply, AddChar.one_apply, ZMod.val_natCast] at h2
    rw [← psi_period X hε (m % D.host.g kv.1) (m / D.host.g kv.1), Nat.mod_add_div] at h2
    exact h2

  have hb : ∀ b : 𝓞 X.B.I.F, X.psiEf (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
      (((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) * ((algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) b : 𝓞 X.B.I.E) : X.B.I.E)))) = 1 := by
    intro b
    set bE : 𝓞 X.B.I.E := algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) b
    obtain ⟨c, hc⟩ := int_surj X.B.I (wK X kv) hp (card_wK X kv) (Ideal.Quotient.mk _ bE)
    set m : ℕ := ((c : ZMod (D.host.g kv.1)).val : ℕ)
    have hbm : bE - (m : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
      have h1' : bE - (c : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, hc, sub_self]
      have h2' : ((c : 𝓞 X.B.I.E) - (m : 𝓞 X.B.I.E)) ∈ (wK X kv).asIdeal := by
        have : ((c - (m : ℤ) : ℤ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
          rw [int_mem_iff X.B.I (wK X kv) hp (card_wK X kv), ← ZMod.intCast_eq_intCast_iff_dvd_sub]
          simp [m]
        simpa using this
      have := add_mem h1' h2'
      simpa using this
    have hall : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal →
        ε * (bE - (m : 𝓞 X.B.I.E)) ∈ P.asIdeal := by
      intro P hP
      by_cases hPw : P = wK X kv
      · rw [hPw]; exact Ideal.mul_mem_left _ _ hbm
      · exact Ideal.mul_mem_right _ _ (hεP P hP hPw)
    obtain ⟨c', hc'⟩ := mem_g_of_all X hall
    have e : iE X.B.I (ε * bE) = iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * iE X.B.I c' := by
      have : ε * bE = ε * (m : 𝓞 X.B.I.E) + ((X.B.g : ℕ) : 𝓞 X.B.I.E) * c' := by rw [← hc']; ring
      rw [this]; simp [iE]
    have h3 := hm m
    rw [← psi_modg X _ (iE_int X.B.I c'), ← e] at h3
    have e2 : iE X.B.I (ε * bE) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((ε : X.B.I.E) * (bE : X.B.I.E)) := by
      simp [iE]
    rw [e2, divN_incl] at h3
    exact h3

  set τ := PI.ScPsiExists.UnitaryGroupMassFormula.tau X.B.I.cm.fixed
  set y : X.B.I.F := (((X.B.g : ℕ) : X.B.I.F))⁻¹ * τ (ε : X.B.I.E)
  have htr : ∀ z : 𝓞 X.B.I.F, ∃ n : ℤ, Algebra.trace ℚ X.B.I.F (y * algebraMap (𝓞 X.B.I.F) X.B.I.F z) = n := by
    intro z
    have h4 := X.psiEf_rat (((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) *
      ((algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) z : 𝓞 X.B.I.E) : X.B.I.E)))
    rw [hb z, one_mul] at h4
    obtain ⟨n, hn⟩ := PsiCondAllPf.trace_of_psi X.B.I _ h4
    refine ⟨n, ?_⟩
    rw [← hn]
    congr 1
    have hz : ((algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) z : 𝓞 X.B.I.E) : X.B.I.E) =
        algebraMap X.B.I.F X.B.I.E (algebraMap (𝓞 X.B.I.F) X.B.I.F z) := rfl
    have e3 : ((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) * algebraMap X.B.I.F X.B.I.E (algebraMap (𝓞 X.B.I.F) X.B.I.F z)) =
        (((X.B.g : ℕ) : X.B.I.F)⁻¹ * algebraMap (𝓞 X.B.I.F) X.B.I.F z) • (ε : X.B.I.E) := by
      rw [Algebra.smul_def, map_mul, map_inv₀, map_natCast]; ring
    rw [hz, e3, LinearMap.map_smul, smul_eq_mul]
    ring

  let v : HeightOneSpectrum (𝓞 X.B.I.F) :=
    { asIdeal := (wK X kv).asIdeal.comap (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro hbot
        have h5 : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.F) ∈ (wK X kv).asIdeal.comap (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E)) := by
          rw [Ideal.mem_comap, map_natCast]; exact gk_mem X kv
        rw [hbot] at h5
        exact (by exact_mod_cast hp.ne_zero : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.F) ≠ 0) ((Submodule.mem_bot _).1 h5) }
  have hv : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal := by
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]; exact gk_mem X kv
  have hun : Algebra.IsUnramifiedAt ℤ v.asIdeal := by
    letI : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra
    exact PsiCondAllPf.unram_of (D.host.g kv.1) hp v hv
      (Formalism.L2.SG.Pf.TypedLoc.tower_ef X.B.I.F D.host.E hp (D.nd.g_split kv.1) v hv).1
  obtain ⟨d, hd, hdv⟩ := PsiCondAllPf.exists_diff_not_mem v hun
  obtain ⟨c, hc⟩ := PsiCondAllPf.mul_diff_int y htr d hd
  obtain ⟨t, ht⟩ := PI.ScPsiExists.UnitaryGroupMassFormula.tau_int X.B.I.cm.fixed ε

  have hgc : ((X.B.g : ℕ) : 𝓞 X.B.I.F) * c = t * d := by
    apply FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) X.B.I.F
    have hg0 : ((X.B.g : ℕ) : X.B.I.F) ≠ 0 := Nat.cast_ne_zero.2 (g_pos X).ne'
    rw [map_mul, map_mul, hc, ht, map_natCast]
    show (X.B.g : X.B.I.F) * ((((X.B.g : ℕ) : X.B.I.F))⁻¹ * τ (ε : X.B.I.E) * _) = τ (algebraMap (𝓞 X.B.I.E) X.B.I.E ε) * _
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hg0, one_mul]
  have htd : t * d ∈ v.asIdeal := by
    rw [← hgc]
    refine Ideal.mul_mem_right _ _ ?_
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact g_mem_of_gk X (gk_mem X kv)
  have htv : t ∈ v.asIdeal := (v.isPrime.mem_or_mem htd).resolve_right hdv

  have htw : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) t ∈ (wK X kv).asIdeal := htv
  have hte : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) t = ε + sigO X.B.I ε := by
    apply RingOfIntegers.ext
    show algebraMap X.B.I.F X.B.I.E (algebraMap (𝓞 X.B.I.F) X.B.I.F t) = (ε : X.B.I.E) + star (ε : X.B.I.E)
    rw [ht, PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply]
  have hsig : sigO X.B.I ε ∈ (wK X kv).asIdeal := by
    have : ε ∈ (wc X.B.I (wK X kv)).asIdeal :=
      hεP _ (natCast_mem_wc X.B.I (level_mem_wB' X kv)) (wK_ne_wc X kv kv).symm
    rwa [mem_wc] at this
  rw [hte] at htw
  have h1w : (1 : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
    have := sub_mem (sub_mem htw hε1) hsig
    convert this using 1; ring
  exact (wK X kv).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1w)

end Formalism.L2.SG.Pf.KppChar
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Cw (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ :=
  Matrix.of fun i j => if i = j then 1 else if h : i < j ∧ blkOf w.1 i.1 = blkOf w.1 j.1 then c ⟨(i, j), h⟩ else 0

theorem isUB_Cw (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) : IsUB (blkW w) (Cw w c) := by
  refine ⟨fun i => by simp [Cw], fun i j hij => ?_⟩
  simp only [Cw, Matrix.of_apply] at hij
  split_ifs at hij with h1 h2
  · subst h1; exact ⟨le_rfl, rfl⟩
  · exact ⟨h2.1.le, h2.2⟩
  · exact absurd rfl hij

theorem Cw_apply_free (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) (p : FreeE w) :
    Cw w c p.1.1 p.1.2 = c p := by
  simp only [Cw, Matrix.of_apply]
  rw [if_neg (ne_of_lt p.2.1), dite_eq_left p.2]
  rfl

theorem span_frm_le (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (k : ℕ)
    (hk : k ≤ D.R.rS) :
    Submodule.span ℂ (frm X w D.host.rdE v '' {a | a.1 < k}) ≤
      spanLt (fun a => rv X.B.I v (X.eR a)) k := by
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have ha' : a.1 < D.R.rS := lt_of_lt_of_le ha hk
  obtain ⟨b, rfl⟩ : ∃ b : Fin D.R.rS, a = b.castSucc := ⟨⟨a.1, ha'⟩, Fin.ext rfl⟩
  simp only [frm, famSc, fam_castSucc, SetLike.mem_coe]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ?_, rfl⟩)
  simpa using ha

theorem frm_castSucc (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (b : Fin D.R.rS) :
    frm X w D.host.rdE v b.castSucc = (((D.host.rdE : ℂ) ^ (D.R.rS - b.1))⁻¹) • rv X.B.I v (X.eR b) := by
  simp only [frm, famSc, fam_castSucc, Fin.val_castSucc]

theorem frm_last (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    frm X w D.host.rdE v (Fin.last D.R.rS) = rv X.B.I v (X.zR w) := by
  simp only [frm, famSc, fam_last, Fin.val_last, Nat.sub_self, pow_zero, inv_one, one_smul]

theorem comb_mem (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    {blk : Fin (D.R.rS + 1) → ℕ} {A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ} (hA : IsUB blk A)
    (a' : Fin (D.R.rS + 1)) :
    ∑ a'', (A - 1) a'' a' • frm X w D.host.rdE v a'' ∈ Submodule.span ℂ (frm X w D.host.rdE v '' {a | a.1 < a'.1}) := by
  refine Submodule.sum_mem _ fun a'' _ => ?_
  by_cases h : (A - 1) a'' a' = 0
  · rw [h, zero_smul]; exact Submodule.zero_mem _
  · have hne : a'' ≠ a' := by intro he; subst he; apply h; simp [hA.1]
    have hA0 : A a'' a' ≠ 0 := by intro h0; apply h; simp [h0, Matrix.one_apply, hne]
    have hlt : a'' < a' := lt_of_le_of_ne (hA.2 _ _ hA0).1 hne
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a'', hlt, rfl⟩)

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section

noncomputable section

open MonoidAlgebra

namespace Formalism.L2.SG.Pf.AllRowsES

open Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsGA Formalism.L2.SG.Pf.AllRowsFin
  Formalism.L2.SG.Pf.AllRowsRhoX

variable {D : D7}

abbrev CV (D : D7) : Type := ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)

def Ea (a : CV D) : MonoidAlgebra ℂ (G0g D.nd) :=
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun γ : G0g D.nd =>
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv)

theorem Ea_coeff (a : CV D) (γ : G0g D.nd) :
    (Ea a).coeff γ = haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) := by
  simp [Ea, MonoidAlgebra.coeff_ofCoeff]

open Classical in
theorem ES_eq (S : Set (Tup2 D)) : ES S = ∑ a ∈ Finset.univ.filter (fun a : CV D => tupOf a ∈ S), Ea a := by
  apply MonoidAlgebra.ext
  ext γ
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_filter]
  unfold ES
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [Ea_coeff]
  · rfl

theorem monicOf_inj {g : ℕ} [Fact g.Prime] {N : ℕ} {a b : Fin N → ZMod g}
    (h : Formalism.CyclotomicNorms.monicOf a = Formalism.CyclotomicNorms.monicOf b) : a = b := by
  funext i
  rw [← Formalism.L2.SG.Pf.RowDictPf.coeff_monicOf a i, ← Formalism.L2.SG.Pf.RowDictPf.coeff_monicOf b i, h]

open Classical in
theorem Ea_mul (a b : CV D) : Ea a * Ea b = if a = b then Ea a else 0 := by
  have : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  apply MonoidAlgebra.ext
  ext γ
  rw [coeff_mul_fin]
  simp only [Ea_coeff]
  have key : ∑ δ : G0g D.nd, (∏ kv : (Σ k : Fin 2, D.nd.PlG k),
        (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (δ kv)) *
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (b kv))).coeff ((δ⁻¹ * γ) kv) =
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))) *
        (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (b kv)))).coeff (γ kv) := by
    simp only [coeff_mul_fin]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr (Finset.ext fun _ => by simp only [Finset.mem_univ]) fun δ _ => ?_
    rw [← Finset.prod_mul_distrib]
    rfl
  rw [key]
  split_ifs with hab
  · subst hab
    rw [Ea_coeff]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [D.ntypes.eSer_idem]
  · obtain ⟨kv, hkv⟩ : ∃ kv, a kv ≠ b kv := by
      by_contra h
      push Not at h
      exact hab (funext h)
    have h0 : (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))) * (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (b kv))) = 0 :=
      D.ntypes.eSer_orth kv.1 _ _ fun h => hkv (monicOf_inj h)
    rw [Finset.prod_eq_zero (Finset.mem_univ kv) (by rw [h0]; simp)]
    simp


open Classical in
theorem ES_idem (S : Set (Tup2 D)) : ES S * ES S = ES S := by
  rw [ES_eq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [Ea_mul]
  rw [Finset.sum_eq_single a (fun b _ hb => if_neg (Ne.symm hb)) (fun h => absurd ha h), if_pos rfl]

theorem ES_central (S : Set (Tup2 D)) (y : MonoidAlgebra ℂ (G0g D.nd)) : ES S * y = y * ES S :=
  central_of_class _ (ES_conj S) y

theorem ES_selfadj (S : Set (Tup2 D)) : conjA (ES S) = ES S :=
  selfadj_of_central_idem _ (ES_idem S) (ES_central S)

end Formalism.L2.SG.Pf.AllRowsES
end
end
