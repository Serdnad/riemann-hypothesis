module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle530
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle522
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle553
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSideReadingLevelZeroMoved

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HeightCounting.JumpsSt

theorem mtInput_of {D : D7} {cf : CharFrame D} {M : MtFam D} {ch : NChoice D} (tp : TupTied D cf ch)
    {xi : D.what₂.Tup → HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (h : MtInput D M (fun μ j => cf.mu0 j * xi μ) Q) (hx : tp.xi = xi) (hQ : ch.Q = Q) : MtInput D M tp.tup ch.Q := by
  subst hx hQ
  exact h


end GlobalTheory.HeightCounting.JumpsSt
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up.LiTw

section Gen

variable {D : D7} (N : TwNew D)

theorem goodL_eq (S : RatDat D.ntw) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) :
    goodL N.toD7 (N.rat S) θ j = goodL D S θ j := by
  have h : N.ex.eLL0 = D.nexp.eLL0 := funext fun g =>
    Subtype.ext (D.what₂.embLL.injective ((N.h0 g).trans (D.nStage_trivialCharacter_coeff_eq g).symm))
  exact congrArg (fun e : G0g D.nd → ↥D.LL0 =>
    Module.End.eigenspace (∑ᶠ g : G0g D.nd, ((e g : ↥D.LL0) : D.what₂.LL) • actL D S j g) 1 ⊓
    ⨅ u : Formalism.IndefR.NX.U D.nd, Module.End.eigenspace (actL D S j u)
      (((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL)) h

def ratIn {S : RatDat D.ntw} (I : RatIn D S) : RatIn N.toD7 (N.rat S) where
  Sb := I.Sb
  rho := I.rho
  chi := I.chi
  ks := I.ks
  fd := I.fd
  mk_fg := I.mk_fg
  hL := I.hL
  hs := I.hs
  hL_zero := I.hL_zero
  θ := I.θ
  θ_ne := I.θ_ne
  eig := I.eig
  span := fun j h1 h2 => by rw [goodL_eq N S I.θ j]; exact I.span j h1 h2
  hL_int := fun j k P h1 h2 => by rw [goodL_eq N S I.θ j]; exact I.hL_int j k P h1 h2

theorem cusp {Rw : RowSide D} (h : RowCusp D Rw) : RowCusp N.toD7 (N.row Rw) := h

theorem mtIn {M tup Q} (h : MtInput D M tup Q) : MtInput N.toD7 (N.mt M) tup Q := { h with }

end Gen

end GlobalTheory.HeightCounting.Up.LiTw

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section
namespace GlobalTheory.HeightCounting.Up

def sideB_congr {D : D7} {cf cf' : CharFrame D} {Rw Rw' : RowSide D} {low low' : Finset ℕ}
    {Pq Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S S' : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {hL' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S'.WL j)}
    {eig eig' : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} {θ θ' : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (e1 : cf = cf') (e2 : Rw = Rw') (e3 : low = low') (e4 : Pq = Pq') (e5 : S = S') (e6 : HEq hL hL') (e7 : eig = eig')
    (e8 : θ = θ') (h : SideB D cf Rw low Pq S hL eig θ) : SideB D cf' Rw' low' Pq' S' hL' eig' θ' := by
  subst e1 e2 e3 e4 e5 e7 e8
  cases e6
  exact h

end GlobalTheory.HeightCounting.Up
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem GlobalTheory.LamTie.cond0_primes_lowAll : ∀ (D : D7) (Z : GlobalTheory.LamTie.LamDat D), Z.Ok → Z.q0 = AbsolutelyIrreducibleSpan.q0 D → ∀ P : HeightOneSpectrum (𝓞 D.host.E), (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → ∃ p ∈ lowAll D, P ∈ placesOver D.host.E p := by
  intro D Z hZ hq P hP
  have hPr : Prime (GlobalTheory.ToricDenom.below P).asIdeal := (GlobalTheory.ToricDenom.below P).prime

  have key : ∀ n : ℕ, ((n : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal) →
      ((n : 𝓞 D.host.E) ∈ P.asIdeal) := by
    intro n hn
    have h1 : algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) (n : GlobalTheory.CMVal.OF D.host.E) ∈ P.asIdeal := hn
    simpa using h1
  have key' : ∀ n : ℕ, ((n : 𝓞 D.host.E) ∈ P.asIdeal) →
      ((n : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal) := by
    intro n hn
    show algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) (n : GlobalTheory.CMVal.OF D.host.E) ∈ P.asIdeal
    simpa using hn
  unfold GlobalTheory.LamTie.cond0 at hP
  rcases hPr.dvd_or_dvd hP with h | h
  · have h2 := hPr.dvd_of_dvd_pow h
    rw [Ideal.dvd_span_singleton] at h2
    have h3 := key _ (by exact_mod_cast h2)
    push_cast at h3
    have hpr := P.isPrime
    rcases hpr.mem_or_mem h3 with h4 | h4
    · rcases hpr.mem_or_mem h4 with h5 | h5
      · rcases hpr.mem_or_mem h5 with h6 | h6
        · exact ⟨D.host.g 0, by simp [GlobalTheory.HeightCounting.lowAll], h6⟩
        · exact ⟨D.host.g 1, by simp [GlobalTheory.HeightCounting.lowAll], h6⟩
      · exact ⟨D.host.pde, by simp [GlobalTheory.HeightCounting.lowAll], h5⟩
    · exact ⟨D.host.pde', by simp [GlobalTheory.HeightCounting.lowAll], h4⟩
  · have hle : (GlobalTheory.ToricDenom.below Z.w0).asIdeal ≤ (GlobalTheory.ToricDenom.below P).asIdeal :=
      Ideal.le_of_dvd h
    have heq : (GlobalTheory.ToricDenom.below Z.w0).asIdeal = (GlobalTheory.ToricDenom.below P).asIdeal :=
      ((GlobalTheory.ToricDenom.below Z.w0).isMaximal).eq_of_le (GlobalTheory.ToricDenom.below P).isPrime.ne_top hle
    have hw : ((Z.q0 : ℕ) : 𝓞 D.host.E) ∈ Z.w0.asIdeal := hZ.places.referencePlaceOverPrime
    have hb : ((Z.q0 : ℕ) : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below Z.w0).asIdeal := by
      show algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) ((Z.q0 : ℕ) : GlobalTheory.CMVal.OF D.host.E) ∈ Z.w0.asIdeal
      simpa using hw
    rw [heq] at hb
    refine ⟨Z.q0, ?_, key _ hb⟩
    rw [hq]
    simp [GlobalTheory.HeightCounting.lowAll, lowPr]
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section
namespace GlobalTheory.HeightCounting.Up.PointwiseSettings
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem exists_Sx (D : D7) : ∃ Sx : Finset (PlE D.host), (∀ p ∈ lowAll D, placesOver D.host.E p ⊆ ↑Sx) ∧
    OverSet D Sx (lowAll D) ∧ (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) := by
  have hne : ∀ p ∈ lowAll D, p ≠ 0 := by
    intro p hp
    simp only [lowAll, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl
    · exact lowPr_ne_zero D p hp
    · exact (D.host.g_prime 0).ne_zero
    · exact (D.host.g_prime 1).ne_zero
    · exact D.host.pde_prime.ne_zero
    · exact D.host.pde'_prime.ne_zero
  have hfin : (⋃ p ∈ (lowAll D : Set ℕ), placesOver D.host.E p).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => Formalism.L2.TwC.placesOver_finite' D.host.E p (hne p hp)
  refine ⟨hfin.toFinset, fun p hp Q hQ => ?_, fun Q hQ => ?_, fun Q Q' hQ hc => ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact Set.mem_biUnion (Finset.mem_coe.2 hp) hQ
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact ⟨p, hp, hQp⟩
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact (Set.Finite.mem_toFinset hfin).2 (Set.mem_biUnion hp (placesOver_conj D p hQp hc))


end GlobalTheory.HeightCounting.Up.PointwiseSettings
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistLift

open Polynomial

theorem prod_X_sub_C_scale_mem_lifts {K : Type} [Field K] (f : K →+* ℂ) (M : Multiset ℂ) (y : K)
    (hy : f y ≠ 0) (h : (M.map (fun α => X - C α)).prod ∈ Polynomial.lifts f) :
    ((M.map (fun x => x * f y)).map (fun α => X - C α)).prod ∈ Polynomial.lifts f := by
  set q : ℂ[X] := C (f y)⁻¹ * X with hq
  have key : ((M.map (fun x => x * f y)).map (fun α => X - C α)).prod =
      C (f y) ^ Multiset.card M * ((M.map (fun α => X - C α)).prod).comp q := by
    clear h
    induction M using Multiset.induction_on with
    | empty => simp
    | cons a M ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, ih, mul_comp]
      have e1 : (X - C a).comp q = C (f y)⁻¹ * X - C a := by simp [hq]
      have e2 : X - C (a * f y) = C (f y) * (C (f y)⁻¹ * X - C a) := by
        rw [mul_sub, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hy, C_1, one_mul, ← C_mul, mul_comm (f y) a]
      rw [e1, e2]; ring
  rw [key]
  refine mul_mem (pow_mem (Polynomial.C_mem_lifts f y) _) ?_
  rw [Polynomial.lifts_iff_set_range] at h ⊢
  obtain ⟨p, hp⟩ := h
  refine ⟨p.comp (C y⁻¹ * X), ?_⟩
  rw [Polynomial.map_comp, hp, hq]
  simp [map_inv₀]

end GlobalTheory.TwistLift

namespace GlobalTheory.TwistLift

open Polynomial

theorem galPol_lifts_tw_etaTinv : ∀ (D : D7) (cf : CharFrame D), GlobalTheory.HeightCounting.CharSide D cf → ValLL0 D cf → ∀ π : D.naut.CG D.R.r, (∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D)) → ∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) ((1 - (D.R.nV : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D) := by
  intro D cf hC hV π hπ
  obtain ⟨k, hk⟩ := D.R.t_odd
  filter_upwards [hπ, D.naut.locG_unr_ae π] with w hw hu
  have hUe : cf.eta.UnrAt w := by
    have h1 := (hC.unr_iff D.naut.etaT w).1 (D.naut.etaT_unr w)
    rwa [hC.etaT] at h1
  have hFe : D.naut.frobEig (D.naut.locG D.naut.etaT w) = {((cf.eta.val w : ℂ))⁻¹} := by
    have h1 := hC.frob D.naut.etaT w (by rw [hC.etaT]; exact hUe)
    rw [h1, hC.etaT]; simp
  have hFi : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {(cf.eta.val w : ℂ)} := by
    rw [(D.naut.etaTinv_def w).2, hFe]; simp
  have hUi : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hD1 : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ w
  obtain ⟨y, hy⟩ := hV.eta w hUe
  have hNv : Formalism.ConjugateSelfDual.normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hN : ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ≠ 0 := by
    rw [hNv, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  set N : ℂ := ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) with hNdef
  set lam : D.LL0 := y * (((Formalism.ConjugateSelfDual.normV w : ℕ) : D.LL0) ^ k)⁻¹ with hlamdef
  have hlam : embLL0 D lam = (cf.eta.val w : ℂ) * N ^ (-(1 / 2 : ℂ)) * (N ^ k)⁻¹ := by
    rw [hlamdef, map_mul, map_inv₀, map_pow, map_natCast, hy, Formalism.L2.Host.HChar.valTw, hNdef, hNv]
    push_cast; ring
  have hlam0 : embLL0 D lam ≠ 0 := by
    rw [hlam]
    refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) ?_) (inv_ne_zero (pow_ne_zero _ hN))
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hmul : D.naut.frobEig (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) ((1 - (D.R.nV : ℝ)) / 2)) =
      (D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map (fun x => x * embLL0 D lam) := by
    rw [D.naut.locG_tw, D.naut.frobEig_tw _ _ (D.naut.unr_char _ _ hD1 hu hUi),
      D.naut.frobEig_char _ _ _ hu hUi hD1 hFi, D.naut.frobEig_tw _ _ hu, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun x _ => ?_)
    simp only [Function.comp_apply]
    have hs : (((1 - (D.R.nV : ℝ)) / 2 : ℝ) : ℂ) = (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) + (-(1 / 2 : ℂ)) + (-(k : ℂ)) := by
      have e : D.R.nV = D.R.r + D.R.t := rfl
      rw [e, hk]; push_cast; ring
    rw [hlam, ← hNdef, hs, Complex.cpow_add _ _ hN, Complex.cpow_add _ _ hN, Complex.cpow_neg (x := N) (y := (k : ℂ)),
      Complex.cpow_natCast]
    ring
  have hw' := hw
  simp only [galPol] at hw' ⊢
  rw [hmul]
  exact prod_X_sub_C_scale_mem_lifts (embLL0 D) _ lam hlam0 hw'

end GlobalTheory.TwistLift
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.Mem.Top.TypesTrue GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.CopySide

theorem mem_center_map {G G' : Type} [Monoid G] [Monoid G'] (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ] MonoidAlgebra ℂ G')
    {a : MonoidAlgebra ℂ G} (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) :
    φ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G') := by
  rw [Subalgebra.mem_center_iff] at ha ⊢
  intro b
  obtain ⟨b, rfl⟩ := φ.surjective b
  rw [← map_mul, ← map_mul, ha b]

def cenMap {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Subalgebra.center ℂ (MonoidAlgebra ℂ H) :=
  ((MonoidAlgebra.domCongr ℂ ℂ e).toAlgHom.comp (Subalgebra.center ℂ (MonoidAlgebra ℂ G)).val).codRestrict _ fun z =>
    mem_center_map (MonoidAlgebra.domCongr ℂ ℂ e) z.2

theorem cenMap_coeff {G H : Type} [Group G] [Group H] (e : G ≃* H) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (h : H) :
    ((cenMap e z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)) : MonoidAlgebra ℂ H).coeff h =
      (z : MonoidAlgebra ℂ G).coeff (e.symm h) := by
  show (MonoidAlgebra.domCongr ℂ ℂ e (z : MonoidAlgebra ℂ G)).coeff h = _
  rw [MonoidAlgebra.coeff_domCongr]

theorem domCongr_symm_eq {G H : Type} [Group G] [Group H] (e : G ≃* H) (a : MonoidAlgebra ℂ H) (b : MonoidAlgebra ℂ G)
    (h : ∀ g, a.coeff (e g) = b.coeff g) : MonoidAlgebra.domCongr ℂ ℂ e.symm a = b := by
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun g => ?_
  rw [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_symm]
  exact h g

theorem domCongr_eq {G H : Type} [Group G] [Group H] (e : G ≃* H) (a : MonoidAlgebra ℂ H) (b : MonoidAlgebra ℂ G)
    (h : ∀ g, a.coeff (e g) = b.coeff g) : MonoidAlgebra.domCongr ℂ ℂ e b = a := by
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun g => ?_
  rw [MonoidAlgebra.coeff_domCongr, ← h, MulEquiv.apply_symm_apply]


open Classical in
theorem tie_tr {G H E : Type} [Group G] [Group H] [AddCommGroup E] [Module ℂ E] (e : G ≃* H)
    (cen : Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ E) (a : MonoidAlgebra ℂ G) (b : MonoidAlgebra ℂ H)
    (h : ∀ g, b.coeff (e g) = a.coeff g) :
    (if ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) then cen ⟨a, ha⟩ else 0) =
      (if hb : b ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ H) then (cen.comp (cenMap e.symm)) ⟨b, hb⟩ else 0) := by
  have h1 := domCongr_symm_eq e b a h
  have h2 := domCongr_eq e b a h
  by_cases hb : b ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ H)
  · have ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
      rw [← h1]; exact mem_center_map _ hb
    rw [dite_eq_left ha, dite_eq_left hb, AlgHom.comp_apply]
    congr 1
    exact Subtype.ext h1.symm
  · have ha : a ∉ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
      intro ha; apply hb; rw [← h2]; exact mem_center_map _ ha
    rw [dite_eq_right ha, dite_eq_right hb]



theorem side_copy : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → ∃ (sg : SameGrp (B := B) (C := w.C) x.o.Z (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) (s : Side0 (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)), s.RR = x.s.RR ∧ HEq s.jEE x.s.jEE ∧ ∀ μ (c : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd))) (c0 : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))), (∀ g, (c0 : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)).coeff g = (c : MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd)).coeff (sg.iso g)) → s.cen μ c = x.s.cen μ c0 := by
  intro K B f T w P x N hN
  let sg : SameGrp (B := B) (C := w.C) x.o.Z (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)) :=
    { e := (by with_unfolding_all exact ((plEquiv x.o.N.naut N.naut) :))
      pl := (by with_unfolding_all exact ((TypesTrue.plGw_plEquiv x.fits.grp hN) :))
      e0 := (by with_unfolding_all exact ((x.fits.grp.typeIdempotent_coeff_across_layers hN) :)) }
  let φ := cenMap sg.iso.symm
  have hφ : ∀ c g, (φ c).val.coeff g = c.val.coeff (sg.iso g) := by
    intro c g
    rw [cenMap_coeff, MulEquiv.symm_symm]

  have hstd : ∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR →
      StdIso (w.st x.o.Z) w.px (eR.trans sg.iso.symm) := by
    rintro eR ⟨plg1, iso1, hpl1, hact1⟩
    refine ⟨(Equiv.sigmaCongrRight fun k => sg.e k).trans plg1, fun kv => iso1 ⟨kv.1, sg.e kv.1 kv.2⟩, fun kv => ?_, fun g kv => ?_⟩
    · exact (hpl1 _).trans (sg.pl kv.1 kv.2)
    · exact hact1 g _
  refine ⟨sg, { cen := fun μ => (x.s.cen μ).comp φ
                tie := fun μ => (x.s.tie μ).trans ((by with_unfolding_all exact ((tie_tr sg.iso (x.s.cen μ) _ _ sg.e0) :)))
                is := fun eR h μ c c' hc xx => ?_
                RR := x.s.RR
                frames := x.s.frames
                jEE := x.s.jEE
                basis := x.s.basis
                norm := x.s.norm }, rfl, HEq.rfl, fun μ c c0 hc => ?_⟩
  · show x.s.cen μ (φ c) xx = _
    refine x.s.is (eR.trans sg.iso.symm) (hstd eR h) μ (φ c) c' (fun g => ?_) xx
    exact (hc g).trans ((congrArg c.val.coeff (sg.iso.apply_symm_apply (eR g))).symm.trans (hφ c _).symm)
  · show x.s.cen μ (φ c) = _
    congr 1
    apply Subtype.ext
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun g => ?_
    exact (hφ c g).trans (hc g).symm

end GlobalTheory.Mem.R3.Rw.CopySide

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.Mem.R3.Rw.CopyRead

private theorem pin_of {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok}
    {Wt : Set B.places.Pl} {z₀ : GlobalTheory.Mem.R3.Dat (w.st Z₀) w.I hX T Wt}
    {q : GlobalTheory.Mem.R3.Rw.RowPk w z₀} {o : q.Over}
    {m : GlobalTheory.Mem.R3.Rw.Moved o} {s : GlobalTheory.Mem.R3.Rw.Side0 o}
    (r : GlobalTheory.Mem.R3.Rw.ReadPk m s) (Y : Read m.z.R.toRealDat m.z.F.lv2 s.p0) (e : r.Y = Y)
    (h8 : ∀ π, (Formalism.IndefR.principalLevelFrame.rowRepR m.z.R.θ (Y.eFT π)).Iso (m.t.rep π))
    (h9 : ∀ x, HEq (Y.Ish.jE x).1 ((m.t.ch true).jE x)) (h10 : ∀ x, HEq (Y.Iz.jE x).1 ((m.t.ch false).jE x))
    (h11 : ∀ i x, HEq (Y.mj.eW i x) (m.t.lf.eW i x)) (h12 : ∀ μ h i x, HEq (Y.IL.jMt μ h i x).1 (m.t.lf.jMt μ i x)) : r.Pin := by
  subst e
  exact ⟨h8, h9, h10, h11, h12⟩

private theorem read_pinned {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok}
    {Wt : Set B.places.Pl} {z₀ : GlobalTheory.Mem.R3.Dat (w.st Z₀) w.I hX T Wt}
    {q : GlobalTheory.Mem.R3.Rw.RowPk w z₀} {o : q.Over} (hF : o.Fits)
    (m : GlobalTheory.Mem.R3.Rw.Moved o) (s : GlobalTheory.Mem.R3.Rw.Side0 o)
    (hs : GlobalTheory.Mem.R3.Rw.GoodSideLattices.Good m s) : ∃ r : GlobalTheory.Mem.R3.Rw.ReadPk m s, r.Pin := by
  have k := read_of_fits B f T w Z₀ hX Wt z₀ q o hF m s
  obtain ⟨Y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := k
  have k2 := GoodSideLattices.read_of_good hF m s hs Y h9 h10
  obtain ⟨Z⟩ := k2
  exact ⟨⟨Y, Z, h1, h2, h3, h4, h5, h6, h7⟩, pin_of _ Y rfl h8 h9 h10 h11 h12⟩



theorem read_copyN : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I → (∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR) → ∀ (m : Moved (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)), m.Copy → m.Coh → ∀ (sg : SameGrp (B := B) (C := w.C) x.o.Z (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) (s : Side0 (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)), s.RR = x.s.RR → HEq s.jEE x.s.jEE → (∀ μ (c : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd))) (c0 : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))), (∀ g, (c0 : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)).coeff g = (c : MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd)).coeff (sg.iso g)) → s.cen μ c = x.s.cen μ c0) → ∃ r : ReadPk m s, r.Pin ∧ HEq (repOf r.Y) (repOf x.r.Y)  := by
  intro K B f T w P x N hG hGA hCen m hc hco _ s hRR hj _
  have hF : RowPk.Over.Fits (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over) := ⟨x.fits.div, hG, hGA, hCen⟩
  have k := read_pinned hF m s (good_copy x N m hc hco s hRR hj)
  exact k.imp fun r hp => ⟨hp, repOf_heq x.coh x.r x.pin hco r hp⟩

end GlobalTheory.Mem.R3.Rw.CopyRead
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple.Lay.EigCopy


theorem eigTrue_congr {D : D7} {cf : CharFrame D} {Rw Rw' : RowSide D} {Sb : Finset (PlE D.host)}
    {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} (h : Rw.locR = Rw'.locR) (hT : GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig) :
    GlobalTheory.TwInputs.EigTrue D cf Rw' Sb eig := by
  unfold GlobalTheory.TwInputs.EigTrue at hT ⊢
  rw [← h]
  exact hT


end GlobalTheory.RowTriple.Lay.EigCopy
end
end
