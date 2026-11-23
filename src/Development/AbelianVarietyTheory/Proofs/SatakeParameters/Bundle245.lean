module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle185
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralVacuumIntertwinesSphericalHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle297
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
public import Formalism.LocalRingCardinality.Bundle009
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.Columns.Bundle023
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle241
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle188
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle112
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle111
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle238
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle113
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle012
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle213
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle147
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle219
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle234
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle225
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle239
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle148
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle240
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualLocalBasesEigenframeAtRamifiedPrime
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle242
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.Hk3.StepX

variable {D : D7}

theorem gram_posDef_X (τ : D.what₂.Tau) : (gramAt D D.sp.X' τ).PosDef := by
  have := D.sp.X'_sig (tauE D τ)
  rw [D7.X'_posDef D] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem lift_symm_comp {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (x : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) :
    PiTensorProduct.lift.symm (L ∘ₗ x) = postOn M L (PiTensorProduct.lift.symm x) := by
  refine MultilinearMap.ext fun v => ?_
  rw [postOn_apply]
  simp [PiTensorProduct.lift_symm]

theorem integ_X {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D D.sp.X' →* Module.End ℂ (WO S D.sp.X' → ℂ)}
    (hW : IsWeilDatumO ψ S D.sp.X' χS χT om) {f : WO S D.sp.X' → ℂ} (hf : IsThetaFunO ψ S D.sp.X' f)
    (Φ : GA D D.sp.X' → ℂ) (hΦc : Continuous Φ) (hl : ∀ γ ∈ GQ D.sp.X', ∀ h, Φ (γ * h) = Φ h)
    (ν : Measure (GA D D.sp.X')) (hν : ν.IsHaarMeasure) (𝓕 : Set (GA D D.sp.X'))
    (h𝓕 : IsFundamentalDomain (GQ D.sp.X') 𝓕 ν) (g : GA D S) (y : GA D D.sp.X') :
    IntegrableOn (fun h => thetaKO om g h f * Φ (h * y)) 𝓕 ν := by
  have : IsTopologicalGroup (GA D D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D D.sp.X') := ⟨rfl⟩
  have : Countable (GQ D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig D.sp.X'.gram
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact D.sp.X' gram_posDef_X
  refine GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (GQ D.sp.X') C hC (fun h => ?_) ν hν 𝓕 h𝓕 _ ?_ ?_
  · obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
  · exact ((hW.om_cont f hf 0).comp (Continuous.prodMk_right g)).mul (hΦc.comp (continuous_mul_const y))
  · intro γ hγ h
    have h1 := (GlobalTheory.thetaKO_rat_left_and_eigen_right ψ S D.sp.X' χS χT om hW f hf).1 1 (one_mem _) γ hγ g h
    rw [one_mul] at h1
    show thetaKO om g (γ * h) f * Φ (γ * h * y) = thetaKO om g h f * Φ (h * y)
    rw [h1, mul_assoc, hl γ hγ]

theorem hyp_inv {V : HSp D} (c : CoefA V) (hc : c.Is) {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) {L : LevDat D.host.E ℂ V.rank}
    {P : Pl D.host.E} (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {f : Bridge.Gf V → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) :
    ∀ k ∈ hyp V P, ∀ h, c.ext f (h * k) = c.ext f h := by
  obtain ⟨n, hB⟩ := hβ
  have hlev := (GlobalTheory.LevOp.level_operators V β Λ _ (flag1L L) hB P (GlobalTheory.DefLiftHecke.one_pow_notMem P n) hP).1
  exact fun k hk h => GlobalTheory.DefLiftHecke.ext_level c hc hf (hlev k hk).1 (hlev k hk).2 h

theorem mult_stable {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    (hβ : IsSDFrame V β Λ N) {L : LevDat D.host.E ℂ V.rank} {P : Pl D.host.E} (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) (c : List ℤ →₀ ℂ) {U : MMap M}
    (hU : U ∈ Mult θ M (levS V β L) (levChi V β L)) : postOn M (hk V P c) U ∈ Mult θ M (levS V β L) (levChi V β L) := by
  obtain ⟨n, hB⟩ := hβ
  have hN' : ((N ^ n : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h' =>
    hN (P.isPrime.mem_of_pow_mem n (by rwa [Nat.cast_pow] at h'))
  exact (GlobalTheory.LevOp.level_operators V β Λ _ L hB P hN' hP).2.2.2.2 S θ M c hθ U hU

theorem toMap_hkF {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (P : Pl D.host.E) (z : List ℤ →₀ ℂ) (f : Bridge.Gf V → c.W) (w : Dm) :
    c.toMap pr (hkF V P z f) w = hk V P z (c.toMap pr f w) := by
  funext h
  show pr (c.ext (hkF V P z f) h) w = _
  rw [GlobalTheory.DefLiftHecke.ext_hkF c hc, GlobalTheory.ThetaIntHecke.hk_apply]

  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl



theorem liftInt_toMap_hk {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D D.sp.X' →* Module.End ℂ (WO S D.sp.X' → ℂ)} {P : Pl D.host.E}
    (hW : IsWeilDatumO ψ S D.sp.X' χS χT om) {ν : Measure (GA D D.sp.X')} {𝓕 : Set (GA D D.sp.X')}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ D.sp.X') 𝓕 ν) (hfix : VacFix ψ om P)
    (cS cX : List ℤ →₀ ℂ) (hM : Match ψ om P cS (dualC cX)) {f0 : WO S D.sp.X' → ℂ} (hf0 : IsVacAt ψ S D.sp.X' P f0)
    (c : CoefA D.sp.X') (hc : c.Is) {β : GL (Fin D.sp.X'.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (hβ : IsSDFrame D.sp.X' β Λ 1)
    {L : LevDat D.host.E ℂ D.sp.X'.rank} (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm] (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) {f : Bridge.Gf D.sp.X' → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') c.coef.ρ (levEnv _ β L).J (levEnv _ β L).χ) (w : Dm) :
    Lift.liftInt ν 𝓕 (thetaKO om) f0 (c.toMap pr (hkF D.sp.X' P cX f) w) =
      hk S P cS (Lift.liftInt ν 𝓕 (thetaKO om) f0 (c.toMap pr f w)) := by
  have he : c.toMap pr f w = (pr.flip w) ∘ c.ext f := rfl
  have hlev := hyp_inv c hc hβ hP hf
  have hcont : Continuous (c.toMap pr f w) := by
    rw [he]
    exact (LinearMap.continuous_of_finiteDimensional (pr.flip w)).comp (GlobalTheory.ThetaIntegrand.ext_continuous c hc β L hf)
  have hl : ∀ γ ∈ GQ D.sp.X', ∀ h, c.toMap pr f w (γ * h) = c.toMap pr f w h := fun γ hγ h => by
    rw [he, Function.comp_apply, Function.comp_apply, GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ h]
  have hr : ∀ k ∈ hyp D.sp.X' P, ∀ h, c.toMap pr f w (h * k) = c.toMap pr f w h := fun k hk h => by
    rw [he, Function.comp_apply, Function.comp_apply, hlev k hk h]
  rw [toMap_hkF c hc pr]
  exact GlobalTheory.ThetaIntHecke.liftInt_hk ψ S D.sp.X' χS χT om P hW ν 𝓕 hν h𝓕 hfix cS cX hM f0 hf0 _ hl hr
    (fun g z _ => integ_X hW hf0.1 _ hcont hl ν hν 𝓕 h𝓕 g z)

theorem sub_comp_apply {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (u u' : M →ₗ[ℂ] N)
    (H : N →ₗ[ℂ] N) (x : M) (h : u' x = H (u x)) : (u' - H ∘ₗ u) x = 0 := by
  rw [LinearMap.sub_apply, LinearMap.comp_apply, h, sub_self]

theorem eq_of_sub_comp {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (u u' : M →ₗ[ℂ] N)
    (H : N →ₗ[ℂ] N) (h : u' - H ∘ₗ u = 0) (x : M) : u' x = H (u x) := by
  have := congrArg (fun L => L x) h
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply, sub_eq_zero] at this
  exact this

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem at_It (R : RealDat D A Ks) (F : Face D A) (hC : Core R F) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (hfix : VacFix R.ψ (R.ωX t) P) (cS cX : List ℤ →₀ ℂ) (hM : Match R.ψ (R.ωX t) P cS (dualC cX))
    (y y' : (R.HX t).H) (hy : (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y)) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank)
    (w : SmT R.MX) :
    (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 (R.ItX φ w) =
      hk _ P cS ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 (R.ItX φ w)) := by
  have hIo := hC.chain.ioX t
  have hν := hC.models.νX t
  have hmem : (R.HX t).e y ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J
      (levEnv _ R.βX (R.datXt t)).χ :=
    (hC.models.HX t).2.1.le (LinearMap.mem_range_self _ y)
  have k := liftInt_toMap_hk (hC.chain.ωX t) hν.1.1 hν.2 hfix cS cX hM ((GlobalTheory.T.fockVectors_chain_isVacuum_off_thetaLevels R F hC t P hP).2.1 φ)
    R.cX hC.models.cX hC.lev.βX (L := R.datXt t) hP R.prX hmem w
  have e1 : (((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y' : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) :
      SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w = R.cX.toMap R.prX (hkF D.sp.X' P cX ((R.HX t).e y)) w :=
    congrArg (fun f => R.cX.toMap R.prX f w) hy
  have hyY : Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ) (R.cX.toMap R.prX ((R.HX t).e y) w) =
      (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 (R.ItX φ w) :=
    funext fun g' => hIo.eq ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y) φ w g'
  have hyY' : Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ)
      ((((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y' : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) :
        SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w) =
      (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 (R.ItX φ w) :=
    funext fun g' => hIo.eq ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y') φ w g'
  exact hyY'.symm.trans ((congrArg (Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ)) e1).trans
    (k.trans (congrArg (hk _ P cS) hyY)))

end GlobalTheory.Hk3.StepX



theorem GlobalTheory.Hk3.StepX.stepX_hk : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ t P, Good R t P → VacFix R.ψ (R.ωX t) P → ∀ cS cX, Match R.ψ (R.ωX t) P cS (dualC cX) → ∀ y y' : (R.HX t).H, (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y) → ∀ v, (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 v = hk _ P cS ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 v) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS t P hP hfix cS cX hM y y' hy
  have hm := D.R.two_le_m
  have hu : (hk (Yc D (D.R.m - 1)) P cS ∘ₗ
      ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1)) ∈ R.CC t (D.R.m - 1) := by
    rw [mem_multT, GlobalTheory.Hk3.StepX.lift_symm_comp]
    exact GlobalTheory.Hk3.StepX.mult_stable R.θ hC.models.inf (R.MY (D.R.m - 1)) (hC.lev.βY (D.R.m - 1) (by omega))
      (L := R.datYt t (D.R.m - 1) R.triv) ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1 t P hP).1 hP cS
      ((mem_multT _ _ _ _ _).1 (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).2)
  have hz := GlobalTheory.multT_eq_zero_of_apply_eq_zero R.θ (R.MY (D.R.m - 1)) _ _ (R.νY t (D.R.m - 1)) (R.fdY t (D.R.m - 1))
    hC.models.inf (hC.models.νY' t).1.1 (hC.models.νY' t).2 (hS.1 t (D.R.m - 1) (by omega))
    (((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1) - hk (Yc D (D.R.m - 1)) P cS ∘ₗ
      ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1))
    (sub_mem (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).2 hu)
  have hex : ∃ φ w, R.ItX φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact (hC.chain.ItX t).ne (LinearMap.ext fun φ => LinearMap.ext fun w => hcon φ w)
  refine hex.elim fun φ0 hw0 => hw0.elim fun w0 hne => ?_
  have h0 := hz _ hne (GlobalTheory.Hk3.StepX.sub_comp_apply _ _ _ _ (GlobalTheory.Hk3.StepX.at_It R F hC t P hP hfix cS cX hM y y' hy φ0 w0))
  exact GlobalTheory.Hk3.StepX.eq_of_sub_comp _ _ _ h0
end

section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical

theorem _root_.GlobalTheory.T.lastStepDatum_law_topLevelStabilizer : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → 2 * cst.M ≤ twTopDepth R → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) (a : FrmG (twLt Ch (m2 + 1 + 1)) (twTt (R := R) sel mu (m2 + 1 + 1))), Y ∈ ybSet sel mu cst p.deco.1.N → a • p' = p' → ∀ x, XiTop Ch sel mu cst (m2 + 1) p Y p' (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst (m2 + 1) P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((twLt Ch (m2 + 1 + 1)).chr a.2.1 * (twTt (R := R) sel mu (m2 + 1 + 1)).chr a.2.2 : X.Kˣ) : X.K) * XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  first | exact @GlobalTheory.StabTopLaw.xiTop_stab_law | exact GlobalTheory.StabTopLaw.xiTop_stab_law | (intros; apply GlobalTheory.StabTopLaw.xiTop_stab_law <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LevOne

theorem cong_mem_level_chr_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hCh hsel hL j hj b P k hk
  classical
  obtain ⟨hkG, hkC⟩ := GlobalTheory.T.mem_integralGL_principalCongruence_of_cols_cong P.1 (cst.D P) k (hL.cst_ok.D_pos P) hk
  set κ : GLint X.E (R.N j) P.1 := ⟨k, hkG⟩ with hκdef
  have hψ : cst.psi P (Loc.n1Arg (GlobalTheory.CongLevel.extE (cOf R j) k)) = 1 := by
    rw [GlobalTheory.Mem.Col2.LevMod.unipotentArg_extendByIdOnLastCoords]
    exact hL.cst_ok.psi_int P 0 (by simpa using GlobalTheory.CongLevel.intAt_nat P.1 0)
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  by_cases hP : P.1 ∈ Pr.vGs
  · have hD1 : cst.D P = 1 := hL.depthG P hP
    have hdu := GlobalTheory.Mem.Col2.degOneUnram_of_mem_vGs hX.ok hPr hP
    have hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)) :=
      fun a ha h0 => GlobalTheory.TopStep.intAt_div_of_redP hdu.2 ha h0
    have hred : ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (k x) = redV P.1 x := by
      have h1 := GlobalTheory.TopStep.redGL_of_prinCong (by omega : 0 < cst.D P) hkC
      intro x hx
      have h2 := GlobalTheory.TopStep.redV_redGL κ hx
      rw [h1, Units.val_one, Matrix.one_mulVec] at h2
      exact h2
    have hh := hL.stabG j b P hP
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, GlobalTheory.Mem.Col2.LevMod.extE_mem_Cbe cst.sharp j P.1 hP hd (L.h j b P) hh k hkG hred, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    have hh' := hh
    unfold lamYat at hh'
    rw [if_pos hP] at hh'
    have hcong := GlobalTheory.CongLevel.conj_cong (qOf P.1) _ _ (L.h j b P) hh'
      (GlobalTheory.CongLevel.extE_cong P.1 (qOf P.1) (cOf R j) (fun i => i + 1) hd k hkG hred)
    have h1 := GlobalTheory.T.rowCharacter_id_add_q_smul_latticePreserving_eq_one Ch mu cst.sharp j P.1 hP ((qOf P.1 : X.E)⁻¹ •
      (((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P : AutY X R j).toLinearMap - LinearMap.id))
      fun x hx => by
        have hx' := hx
        unfold lamYat at hx' ⊢
        rw [if_pos hP] at hx' ⊢
        have h2 := hcong x hx'
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
        exact h2
    rw [smul_inv_smul₀ hq, add_sub_cancel] at h1
    unfold chiInv
    rw [h1, hψ, inv_one, one_mul]
  · have hstd : ∀ x, x ∈ lamYat (Pr := Pr) (R := R) j P.1 ↔ x ∈ stdAt X.E (R.N j + cOf R j) P.1 := by
      intro x
      unfold lamYat
      rw [if_neg hP]
      unfold LocE.lamY
      rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.TopStep.mem_stdAt]
      simp only [LocE.scE, Pi.zero_apply, Nat.cast_zero, ite_self, zpow_zero, inv_one, one_mul]
    have hbd := hL.boundQ j b P hP
    have hbd' : ∀ x ∈ stdAt X.E (R.N j + cOf R j) P.1, (L.h j b P)⁻¹ x ∈ stdAt X.E (R.N j + cOf R j) P.1 ∧
        ((qOf P.1 : X.E) ^ j) • (L.h j b P) x ∈ stdAt X.E (R.N j + cOf R j) P.1 := fun x hx => by
      have h1 := hbd x ((hstd x).2 hx)
      exact ⟨(hstd _).1 h1.1, (hstd _).1 h1.2⟩
    have hjD : j + 1 ≤ cst.D P := by
      have h1 := hL.depthQ' P hP
      have h2 := hL.hm
      omega
    have hg := GlobalTheory.T.conj_extend_principalCongruence_cong_one_mod_q P.1 (cOf R j) j (cst.D P) (L.h j b P) κ hkC hjD hbd'
    have hginv := GlobalTheory.T.conj_extend_principalCongruence_cong_one_mod_q P.1 (cOf R j) j (cst.D P) (L.h j b P) κ⁻¹ (inv_mem hkC) hjD hbd'
    have einv : ((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) κ.1 * L.h j b P)⁻¹ =
        (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) (κ⁻¹).1 * L.h j b P := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, GlobalTheory.CongLevel.extE_inv, mul_assoc]
      rfl
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, ⟨GlobalTheory.CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ k, ?_⟩, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    · have e : (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) =
          (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P := by simp
      show (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) ∈ Jat (Pr := Pr) cst.sharp j P.1
      rw [e]
      unfold Jat
      rw [if_neg hP]
      refine GlobalTheory.T.mem_parahoric_of_cong_one_mod_q P.1 (R.k + j) (R.N j) (cOf R j) _ hg ?_
      rw [einv]
      exact hginv
    · unfold chiInv
      rw [hψ, inv_one, one_mul]
      unfold lamRow
      rw [if_neg hP]
      exact GlobalTheory.T.blockDetResidueChar_eq_one_of_cong_mod_q P.1 _ (R.k + j) (R.N j) (R.N j + cOf R j) _ (by omega) hg

end GlobalTheory.LevOne

end
end

section

namespace GlobalTheory.CurveDictionary

theorem curveDict_of_cm : Formalism.L2.Th1.CM.CM2 → Formalism.L2.Th1.CM.CM3 → Formalism.L2.Th1.CM.CM4 →
    Formalism.L2.KerInert.Rep.CurveDict := fun hGood _ hTor =>
  curveDict_of_inputs hGood hTor GlobalTheory.T.curveLattice_sigmaTwo_algebraic_of_invariants_algebraic GlobalTheory.T.unramifiedWeierstrassCurve_transform_coefficients_wellFormed GlobalTheory.T.beta_model_coefficients_invert_l GlobalTheory.T.log_coordinates_exponent_is_coboundary GlobalTheory.T.coboundary_integral_law_respects_simeq
    GlobalTheory.T.phEquiv_shortWeierstrassModel GlobalTheory.T.thetaUnitFunction_shortModel_integral GlobalTheory.T.inverse_series_formalGroup_iso_integral

end GlobalTheory.CurveDictionary
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

theorem _root_.GlobalTheory.T.isIntegralOffPrimes_matrixStepEntryData : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < t.m2 → ∀ al be p p' x, IntOff (t.O u μ).S (t.seam.σ₀ (XiEntry (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i al be p p' x)) := by
  first | exact @GlobalTheory.KerTie.intOff_xiEntry | exact GlobalTheory.KerTie.intOff_xiEntry | (intros; apply GlobalTheory.KerTie.intOff_xiEntry <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem _root_.GlobalTheory.T.dualLocalBases_eigenframe_at_ramifiedPrime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), p = D.host.d → ∀ ι : ℂ ≃+* ℂ_[p], Formalism.L2.KerInert.IotaExt lm ι → ∀ (cD : D.what₂.Tau → ℂ), IsDgen D cD → ∀ (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (κ : D.what₂.Tau → ℂ_[p]), GlobalTheory.KerStd.StdBases D lm L P → GlobalTheory.KerStd.StdBases D lm L' P' → (∀ τ, ‖κ τ‖ ≤ ‖TaylorLogMetric.lamC lm (cD τ)‖) → ∃ u : HH D → ℂ_[p], (∀ t, ‖u t‖ ≤ 1) ∧ ∀ L₁ L₁', TaylorLogMetric.admitted D N N' L₁ L₁' → TaylorLogMetric.EqAt D p L L₁ → TaylorLogMetric.EqAt D p L' L₁' → ∃ (J : Type) (_ : Fintype J) (v : J → DVar X.Tau N N' → ℂ) (A : J → (Bool × HH D) × Fin N × Fin N' → ℂ_[p]) (cE sE : D.host.E ≃+* D.host.E) (δE : D.host.E) (emb : Bool × HH D → (D.host.E →+* ℂ_[p])) (act : 𝓞 D.host.E → (DVar X.Tau N N' → ℂ) →ₗ[ℂ] (DVar X.Tau N N' → ℂ)), Formalism.L2.Th1.GD.IsEigenFrame ι (cmL a₀ b₀ D.host.d ha hd lam hlam) (ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))) (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF (TaylorLogMetric.tor0 D cc δ) L₁ L₁') D.host.E cE sE δE emb act v A u ∧ ∀ i x, frameM (ι : ℂ →+* ℂ_[p]) v A i x = κ (s.iT i.1) * TaylorLogMetric.chgB D lm P P' (s.iT i.1, i.2) ((0 : ZMod 1), (tauPl D x.1, x.2)) := by
  first | exact @GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime.eigenframe_at_d | exact GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime.eigenframe_at_d | (intros; apply GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime.eigenframe_at_d <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.local_systems_lower_bounds_second_real_place : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (E : OrbitPlaces.Ent D) (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Σ Lv : Levels (Y.Fl u w hg), Chain Lv), LatTied hT X Y → FillsAll hT Y → L.FDef → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → (∀ μ, DV.Used D μ → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ → SiteAdm D u w hg (Y.Fl u w hg) (LC μ u w hg).1 (LC μ u w hg).2) → SysTw D L X K Dx (reW Y LC) lev Xe ce 1 := by
  first | exact @GlobalTheory.TwU.SiteSys.sysTw_sites | exact GlobalTheory.TwU.SiteSys.sysTw_sites | (intros; apply GlobalTheory.TwU.SiteSys.sysTw_sites <;> assumption)
end
