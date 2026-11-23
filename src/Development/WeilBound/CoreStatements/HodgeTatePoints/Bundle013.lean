module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
public import ReciprocityTheory.DualLattices.Bundle018
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Module.ZMod

@[expose] public section

section

namespace PositivityTheory.HtPt.KtwS

open GroundTheory.Heights₂.Heights.Kleiman MvPolynomial

noncomputable section

universe u v w

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_lineBundle_pow (hLT : LineTwist.Statement.{u, w}) (Q : LineBundle S x) (n : ℕ) :
    ∃ Q' : LineBundle S x, Q'.toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => exact ⟨twistBundle S x 0, rfl⟩
  | succ n ih =>
    obtain ⟨Q', hQ'⟩ := ih
    obtain ⟨Q'', hQ''⟩ := hLT S Ω N x Q' Q
    exact ⟨Q'', by rw [hQ'', hQ']; rfl⟩

theorem exists_lineBundle_twistMulOf (hLT : LineTwist.Statement.{u, w}) (M : LineBundle S x) (a : ℕ)
    (c : ℤ) : ∃ Q : LineBundle S x, Q.toSubSystem = twistMul M.toSubSystem a c := by
  obtain ⟨P, hP⟩ := exists_lineBundle_pow hLT M a
  obtain ⟨Q, hQ⟩ := hLT S Ω N x P (twistBundle S x c)
  exact ⟨Q, by rw [hQ, hP]; rfl⟩

variable {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}

theorem exists_restrict_pow (hLT : LineTwist.Statement.{u, w}) (hRT : RestrictTwist.Statement.{u, w})
    (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (hle : primeOf (S := S) x ≤ primeOf (S := S) y)
    (M : LineBundle S x) (M' : LineBundle S y) (r : Ω → K')
    (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (n : ℕ) :
    ∃ (Q : LineBundle S x) (Q' : LineBundle S y) (r' : Ω → K'), Q.toSubSystem = M.toSubSystem.pow n ∧
      Q'.toSubSystem = M'.toSubSystem.pow n ∧ RestrictData Q.toSubSystem hxy Q'.toSubSystem r' := by
  induction n with
  | zero =>
    obtain ⟨r', hr'⟩ := hRT.1 S Ω N x K' y hxy hle 0
    exact ⟨twistBundle S x 0, twistBundle S y 0, r', rfl, rfl, hr'⟩
  | succ n ih =>
    obtain ⟨Q, Q', r', hQ, hQ', hr⟩ := ih
    obtain ⟨Qn, hQn⟩ := hLT S Ω N x Q M
    obtain ⟨Qn', hQn'⟩ := hLT S K' N y Q' M'
    obtain ⟨r'', hr''⟩ := hRT.2 S Ω N x K' y hxy Q M Q' M' r' r hr h
    refine ⟨Qn, Qn', r'', by rw [hQn, hQ]; rfl, by rw [hQn', hQ']; rfl, ?_⟩
    rw [hQn, hQn']
    exact hr''

theorem exists_restrict_twistMul_pow (hLT : LineTwist.Statement.{u, w})
    (hRT : RestrictTwist.Statement.{u, w}) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (M : LineBundle S x) (M' : LineBundle S y)
    (r : Ω → K') (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (a : ℕ) (c : ℤ) (b : ℕ) :
    ∃ (Q : LineBundle S x) (Q' : LineBundle S y) (r' : Ω → K'),
      Q.toSubSystem = (twistMul M.toSubSystem a c).pow b ∧
      Q'.toSubSystem = (twistMul M'.toSubSystem a c).pow b ∧
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r' := by
  obtain ⟨P, P', rP, hP, hP', hrP⟩ := exists_restrict_pow hLT hRT hxy hle M M' r h a
  obtain ⟨rc, hrc⟩ := hRT.1 S Ω N x K' y hxy hle c
  obtain ⟨L, hL⟩ := hLT S Ω N x P (twistBundle S x c)
  obtain ⟨L', hL'⟩ := hLT S K' N y P' (twistBundle S y c)
  obtain ⟨rL, hrL⟩ := hRT.2 S Ω N x K' y hxy P (twistBundle S x c) P' (twistBundle S y c) rP rc hrP hrc
  obtain ⟨Q, Q', r', hQ, hQ', hr'⟩ := exists_restrict_pow hLT hRT hxy hle L L' rL
    (by rw [hL, hL']; exact hrL) b
  refine ⟨Q, Q', r', ?_, ?_, hr'⟩
  · rw [hQ, hL, hP]; rfl
  · rw [hQ', hL', hP']; rfl

end Helpers

section OnW

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem StepTwo.onW (hLT : LineTwist.Statement.{u, w}) (hTA : TwistAlg.Statement.{u, w})
    (hRT : RestrictTwist.Statement.{u, w}) (hNR : NefRestrict.Statement.{u, w})
    (hJP : StepData.JProper.Statement.{u, w}) (hDrop : SubvarDrop.Statement.{u, w})
    (hPt : PrimeFiltration.Point.Statement.{u, w}) (hRes : PrimeFiltration.Restrict.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) (hTV : TwistVanish.Statement.{u, w})
    (T : StepData k x) (hK : ∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e)
    (pp : Ideal (Poly k N)) (hpr : pp.IsPrime) (hhom : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp)
    (hle : primeOf (S := k) x ≤ pp) (hJ : ∀ (f : Poly k N) (e : ℕ), f ∈ T.J → f.IsHomogeneous e → f ∈ pp)
    (hrel : ∃ j, (X j : Poly k N) ∉ pp) :
    ∃ c₁ : ℤ, ∀ (b : ℕ) (Q : LineBundle k x), Q.toSubSystem = T.L.pow b → ∀ c : ℤ, c₁ ≤ c →
      Subsingleton (SubSystem.quotH (Q.twist (twistSys k x c))
        ((Q.twist (twistSys k x c)).twist (idealSys x pp)) 1) := by
  obtain ⟨j, hjp⟩ := hrel
  have hj : x j ≠ 0 := fun h0 => hjp (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := hPt k Ω N x pp hpr hhom hle j hj hjp

  have := hcp
  let A := chartRing k x (singleChart hj)
  let I : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] I.ResidueField := IsScalarTower.toAlgHom k A I.ResidueField
  have hker : RingHom.ker ψ = I := Ideal.ker_algebraMap_residueField I
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    rw [h0, map_zero]
  have hpy : primeOf (S := k) (fun i => ψ (ratio hj i)) = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := hpy ▸ hle

  obtain ⟨f, e₀, hfJ, hfh, hfq⟩ := hJP k Ω N x T
  obtain ⟨e, he, hsub⟩ := hDrop k Ω N x T.d pp T.dim hpr hhom hle ⟨j, hjp⟩ ⟨f, hJ f e₀ hfJ hfh, hfq⟩
  have hsubW : IsSubvar (fun i => ψ (ratio hj i))
      (primeOf (S := k) (fun i => ψ (ratio hj i))) e := by
    rw [hpy]
    exact ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩

  obtain ⟨M', rM, hM'⟩ := hRes k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy T.M
  have hRM : RestrictData T.M.toSubSystem hxy M'.toSubSystem rM :=
    ⟨fun I => (hM' I).1, fun I => (hM' I).2.1, fun I => (hM' I).2.2.1, fun I => (hM' I).2.2.2⟩
  have hnef : Nef M'.toSubSystem := hNR k Ω N x _ _ hxy hxy' T.M M' rM hRM T.nef

  have hts : 0 < T.t - T.s' := by
    have hd : (1 : ℚ) ≤ (T.d : ℚ) + 1 := by
      have := (Nat.cast_nonneg T.d : (0 : ℚ) ≤ T.d); linarith
    have ht : 0 < T.t := by
      by_contra hneg'
      have hneg : T.t ≤ 0 := not_lt.mp hneg'
      have : T.t / ((T.d : ℚ) + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by positivity)
      linarith [T.s'_pos, T.s'_lt]
    have : T.t / ((T.d : ℚ) + 1) ≤ T.t := div_le_self ht.le hd
    linarith [T.s'_lt]
  obtain ⟨q, m', hq, hm', hva⟩ := hK e he _ N _ M' hsubW hnef (T.t - T.s') hts
  obtain ⟨rr, h, hvb⟩ := hva
  have hqm : (q : ℤ) * T.m = T.p * m' := by
    have : (((q : ℤ) * T.m : ℤ) : ℚ) = ((T.p * m' : ℤ) : ℚ) := by
      push_cast; rw [T.m_eq, hm']; ring
    exact_mod_cast this

  obtain ⟨B, hB⟩ := exists_lineBundle_twistMulOf hLT M' q m'
  obtain ⟨L', hL'⟩ := exists_lineBundle_twistMulOf hLT M' T.p T.m
  have hv : ∀ b₂ : ℕ, ∃ c₀ : ℤ, ∀ (b' : ℕ) (c : ℤ), c₀ ≤ c →
      Subsingleton (((((twistMul M'.toSubSystem T.p T.m).pow b₂).twist
        ((twistMul M'.toSubSystem q m').pow b')).twist (twistSys k (fun i => ψ (ratio hj i)) c)).H 1) := by
    intro b₂
    obtain ⟨G, hG⟩ := exists_lineBundle_pow hLT L' b₂
    obtain ⟨c₀, hc₀⟩ := hTV k _ N _ G B rr h (fun l => by rw [hB]; exact hvb.mem_secs l)
      (fun I => by rw [hB]; exact hvb.generates I)
    refine ⟨c₀, fun b' c hc => ?_⟩
    have hs := hc₀ b' c hc
    rwa [hG, hL', hB] at hs
  choose cv hcv using hv
  refine ⟨∑ b₂ ∈ Finset.range q, |cv b₂|, fun b Q hQ c hc => ?_⟩
  obtain ⟨Qb, Qb', r', hQb, hQb', hrd⟩ :=
    exists_restrict_twistMul_pow hLT hRT hxy hxy' T.M M' rM hRM T.p T.m b
  obtain ⟨eqv⟩ := hRQ k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy Qb Qb' r' hrd c 1
  have hQbQ : Qb.toSubSystem = Q.toSubSystem := by rw [hQb, hQ]; rfl
  have hW : Qb'.toSubSystem = ((twistMul M'.toSubSystem T.p T.m).pow (b % q)).twist
      ((twistMul M'.toSubSystem q m').pow (T.p * (b / q))) := by
    rw [hQb', ← hTA k _ N _ M'.toSubSystem T.p q T.m m' (b / q) (b % q) hqm, Nat.div_add_mod b q]
  have hlt : b % q < q := Nat.mod_lt b (by omega)
  have hcb : cv (b % q) ≤ c :=
    le_trans (le_abs_self _) (le_trans (Finset.single_le_sum (f := fun b₂ => |cv b₂|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hlt)) hc)
  have hs : Subsingleton ((Qb'.twist (twistSys k (fun i => ψ (ratio hj i)) c)).H 1) := by
    rw [hW]; exact hcv (b % q) (T.p * (b / q)) c hcb
  rw [← hQbQ]
  exact @Equiv.subsingleton _ _ eqv.toEquiv hs

end OnW

theorem StepTwo.proof (hRed : StepTwo.Reduce.Statement.{u, v, w}) (hLT : LineTwist.Statement.{u, w})
    (hTA : TwistAlg.Statement.{u, w}) (hRT : RestrictTwist.Statement.{u, w})
    (hNR : NefRestrict.Statement.{u, w}) (hJP : StepData.JProper.Statement.{u, w})
    (hDrop : SubvarDrop.Statement.{u, w}) (hPt : PrimeFiltration.Point.Statement.{u, w})
    (hRes : PrimeFiltration.Restrict.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) (hTV : TwistVanish.Statement.{u, w}) :
    StepTwo.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x T hK E _ _ _ _ M₁ M₂ hle hJ
  obtain ⟨n, pr, sh, hpr, hred⟩ := hRed k Ω N x E M₁ M₂ hle T.J hJ
  have hLpow : ∀ b : ℕ, ∃ Q : LineBundle k x, Q.toSubSystem = T.L.pow b := fun b => by
    obtain ⟨L, hL⟩ := exists_lineBundle_twistMulOf hLT T.M T.p T.m
    obtain ⟨Q, hQ⟩ := exists_lineBundle_pow hLT L b
    exact ⟨Q, by rw [hQ, hL]; rfl⟩
  choose Qb hQb using hLpow
  have hW : ∀ i, ∃ c₁ : ℤ, (∃ j, (X j : Poly k N) ∉ pr i) → ∀ (b : ℕ) (c : ℤ), c₁ ≤ c →
      Subsingleton (SubSystem.quotH ((Qb b).twist (twistSys k x c))
        (((Qb b).twist (twistSys k x c)).twist (idealSys x (pr i))) 1) := by
    intro i
    by_cases hrel : ∃ j, (X j : Poly k N) ∉ pr i
    · obtain ⟨c₁, hc₁⟩ := StepTwo.onW hLT hTA hRT hNR hJP hDrop hPt hRes hRQ hTV T hK (pr i)
        (hpr i).1 (hpr i).2.1 (hpr i).2.2.1 (hpr i).2.2.2 hrel
      exact ⟨c₁, fun _ b c hc => hc₁ b (Qb b) (hQb b) c hc⟩
    · exact ⟨0, fun h => absurd h hrel⟩
  choose cw hcw using hW
  refine ⟨∑ i, |cw i - sh i|, fun b c hc => ?_⟩
  have hs := hred (Qb b) c (fun i hi => hcw i hi b (c + sh i) (by
    have h1 : |cw i - sh i| ≤ ∑ i, |cw i - sh i| :=
      Finset.single_le_sum (f := fun i => |cw i - sh i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := le_abs_self (cw i - sh i)
    linarith))
  rwa [hQb b] at hs

end

end PositivityTheory.HtPt.KtwS
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

section

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
lemma comp_mem_addFun (p : ℕ) (e : X ≃+ Y) {f : Y → C} (hf : f ∈ addFun R p Y) :
    (fun x => f (e x)) ∈ addFun R p X := by
  have h : ∀ a b : Y, f (a + b) - f a - f b ∈ pInt R p := hf
  show ∀ a b : X, f (e (a + b)) - f (e a) - f (e b) ∈ pInt R p
  intro a b
  rw [map_add (f := _)]
  exact h (e a) (e b)

private theorem map_pbE_eq_of_addEquiv (e : X ≃+ Y) (SX : Submodule R (X → C)) (SY : Submodule R (Y → C))
    (h1 : ∀ f ∈ SY, (fun x => f (e x)) ∈ SX) (h2 : ∀ g ∈ SX, (fun y => g (e.symm y)) ∈ SY) :
    SY.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = SX := by
  ext g
  rw [Submodule.mem_map_equiv]
  constructor
  · intro h
    have h3 := h1 _ h
    convert h3 using 1
    funext x
    rw [pbE_symm_apply]
    simp
  · intro h
    convert h2 g h using 1
    funext y
    exact pbE_symm_apply e g y

lemma map_addFun (p : ℕ) (e : X ≃+ Y) :
    (addFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = addFun R p X := by
  exact map_pbE_eq_of_addEquiv e _ _ (fun f hf => comp_mem_addFun p e hf) (fun g hg => comp_mem_addFun p e.symm hg)

lemma map_intFun (e : X ≃+ Y) :
    (intFun R Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = intFun R X := by
  refine map_pbE_eq_of_addEquiv e _ _ ?_ ?_
  · intro f hf
    have h : ∀ y : Y, ∃ r : R, algebraMap R C r = f y := hf
    show ∀ x : X, ∃ r : R, algebraMap R C r = f (e x)
    exact fun x => h (e x)
  · intro g hg
    have h : ∀ x : X, ∃ r : R, algebraMap R C r = g x := hg
    show ∀ y : Y, ∃ r : R, algebraMap R C r = g (e.symm y)
    exact fun y => h (e.symm y)

lemma map_pFun (p : ℕ) (e : X ≃+ Y) :
    (pFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = pFun R p X := by
  refine map_pbE_eq_of_addEquiv e _ _ ?_ ?_
  · intro f hf
    simp only [pFun, Submodule.mem_pi, Set.mem_univ, true_implies] at hf ⊢
    exact fun x => hf (e x)
  · intro g hg
    simp only [pFun, Submodule.mem_pi, Set.mem_univ, true_implies] at hg ⊢
    exact fun y => hg (e.symm y)

lemma map_afFun (p : ℕ) (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    (afFun p M).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) =
      afFun p (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) := by
  show Submodule.map _ (M ⊓ addFun R p Y) = _ ⊓ addFun R p X
  rw [Submodule.map_inf, map_addFun]
  exact (pbE (C := C) (R := R) e).injective

lemma map_linFun (p : ℕ) (e : X ≃+ Y) :
    (linFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = linFun R p X := by
  show Submodule.map _ (intFun R Y ⊓ addFun R p Y) = intFun R X ⊓ addFun R p X
  rw [Submodule.map_inf, map_intFun, map_addFun]
  exact (pbE (C := C) (R := R) e).injective

private theorem nonempty_quotient_linearEquiv_map {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (φ : V ≃ₗ[R] W) (L A : Submodule R V) :
    Nonempty ((↥L ⧸ Submodule.comap L.subtype A) ≃ₗ[R]
      (↥(L.map (φ : V →ₗ[R] W)) ⧸ Submodule.comap (L.map (φ : V →ₗ[R] W)).subtype (A.map (φ : V →ₗ[R] W)))) := by
  refine ⟨Submodule.Quotient.equiv _ _ (φ.submoduleMap L) ?_⟩
  ext ⟨w, hw⟩
  constructor
  · rintro ⟨⟨v, hv⟩, hvA, hvw⟩
    have hw' : φ v = w := congrArg Subtype.val hvw
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hvA ⊢
    exact ⟨v, hvA, hw'⟩
  · intro h
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at h
    obtain ⟨v, hvA, rfl⟩ := h
    obtain ⟨v', hv'L, hv'⟩ := hw
    have hvv : v' = v := φ.injective hv'
    subst hvv
    exact ⟨⟨v', hv'L⟩, hvA, rfl⟩

lemma afQuot_equiv (p : ℕ) (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    Nonempty (AFQuot p M ≃ₗ[R]
      AFQuot p (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)))) := by
  obtain ⟨f⟩ := nonempty_quotient_linearEquiv_map (pbE (C := C) (R := R) e) (linFun R p Y) (afFun p M ⊔ pFun R p Y)
  rw [map_linFun, Submodule.map_sup, map_afFun, map_pFun] at f
  exact ⟨f⟩

end

lemma exists_coord (p : ℕ) [Fact p.Prime] (N : Type) [AddCommGroup N] [Finite N]
    [Module (ZMod p) N] : ∃ n : ℕ, Nonempty ((Fin n → ZMod p) ≃+ N) :=
  have : Module.Finite (ZMod p) N := Module.Finite.of_finite
  ⟨_, ⟨(Module.finBasis (ZMod p) N).equivFun.symm.toAddEquiv⟩⟩

private theorem genAF_bot_of_span_monomials {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    {N : Type} [AddCommGroup N] (p : ℕ) {ι : Type} [Fintype ι] (M : Submodule R (N → C))
    (y : ι → N → C) (hy : ∀ j, y j ∈ afFun p M) (S : Set (N → C))
    (hS : M = Submodule.span R S) (hgen : ∀ s ∈ S, ∃ α : ι → ℕ, s = ∏ j, y j ^ α j) :
    GenAF p M ⊥ := by
  have hinv : invFun M (⊥ : AddSubgroup N) = M := by
    ext g
    constructor
    · intro h
      exact (show g ∈ M ∧ ∀ x k : N, k ∈ (⊥ : AddSubgroup N) → g (x + k) = g x from h).1
    · intro h
      show g ∈ M ∧ ∀ x k : N, k ∈ (⊥ : AddSubgroup N) → g (x + k) = g x
      refine ⟨h, ?_⟩
      intro x k hk
      rw [AddSubgroup.mem_bot] at hk
      subst hk
      simp
  show invFun M ⊥ ≤ Subalgebra.toSubmodule (Algebra.adjoin R (afFun p (invFun M ⊥) : Set (N → C)))
  rw [hinv]
  have hsp : Submodule.span R S ≤ Subalgebra.toSubmodule (Algebra.adjoin R (afFun p M : Set (N → C))) := by
    rw [Submodule.span_le]
    intro s hs
    obtain ⟨α, rfl⟩ := hgen s hs
    exact (Subalgebra.mem_toSubmodule _).mpr
      (Subalgebra.prod_mem _ (fun j _ => Subalgebra.pow_mem _ (Algebra.subset_adjoin (hy j)) _))
  intro g hg
  rw [hS] at hg
  exact hsp hg

theorem cnt_of (hcoord : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) := by
  intro p _ C _ _ _ v R _ _ hvR hp N _ _ _ hN AA cA cN hA hC
  letI : Module (ZMod p) N := AddCommGroup.zmodModule hN
  obtain ⟨n, ⟨e⟩⟩ := exists_coord p N
  have hcard : Fintype.card (Fin n → ZMod p) = Fintype.card N := Fintype.card_congr e.toEquiv
  obtain ⟨f⟩ := afQuot_equiv (C := C) (R := R) p e AA.carrier
  have hA' : HasLen v R (AFQuot p (hopfPull e AA).carrier) cA := by
    obtain ⟨m, c, ⟨g⟩, hc⟩ := hA
    exact ⟨m, c, ⟨f.symm.trans g⟩, hc⟩
  have hC' : HasColen R v (hopfPull e AA).carrier cN := hasColen_map v e _ _ hC
  obtain ⟨hle, heq⟩ := hcoord p C v R hvR hp (Fin n) (hopfPull e AA) cA cN hA' hC'
  rw [hcard] at hle heq
  refine ⟨hle, fun hE => ?_⟩
  obtain ⟨x, hxj, hspan⟩ := heq hE
  refine genAF_bot_of_span_monomials p AA.carrier (fun j z => x j (e.symm z)) ?_
    ((⇑(pbE (C := C) (R := R) e.symm)) '' Set.range
      (fun (α : Fin n → ZMod p) (y : Fin n → ZMod p) => ∏ j, x j y ^ (α j).val)) ?_ ?_
  · intro j
    have hx' : x j ∈ (afFun p AA.carrier).map
        (pbE (C := C) (R := R) e : (N → C) →ₗ[R] ((Fin n → ZMod p) → C)) := by
      rw [map_afFun]
      exact hxj j
    have h2 := (Submodule.mem_map_equiv _).mp hx'
    convert h2 using 1
    funext z
    rw [pbE_symm_apply]
  · have h1 := Submodule.map_span (pbE (C := C) (R := R) e.symm : ((Fin n → ZMod p) → C) →ₗ[R] (N → C))
      (Set.range fun (α : Fin n → ZMod p) (y : Fin n → ZMod p) => ∏ j, x j y ^ (α j).val)
    rw [← hspan] at h1
    rw [← map_pbE_symm e AA.carrier]
    exact h1
  · rintro s ⟨_, ⟨α, rfl⟩, rfl⟩
    refine ⟨fun j => (α j).val, ?_⟩
    funext z
    rw [Finset.prod_apply]
    rfl

end PositivityTheory.HtPt.Ra
end
end
