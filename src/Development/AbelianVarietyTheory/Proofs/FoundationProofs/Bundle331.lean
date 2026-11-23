module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterTrivialAtInertPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle247
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle212
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle259
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle314
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle269
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle216
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle221
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle264
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle277
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle278
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle325
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle327
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.InertValue

open GlobalTheory.InertTrivial

variable {D : D7}

theorem val_of_real_neg {N : ℕ} (χ : HeckeU D N) (a : D.host.Eˣ)
    (ha : D.host.conj (a : D.host.E) = a) (hneg : (∏ τ, embT D τ (a : D.host.E)).re < 0) :
    ((χ.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) = (-1) ^ N := by
  have h := χ.aut a
  have hsq : ∀ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ 2 = 1 := by
    intro τ
    have h2 : embT D τ (D.host.conj a) = starRingEnd ℂ (embT D τ a) :=
      D.host.conjE_apply (embT D τ) a
    rw [ha] at h2
    have h0 : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
    rw [div_pow, ← Complex.mul_conj', ← h2, pow_two, div_self (mul_ne_zero h0 h0)]
  have hp : ∀ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ.n τ) =
      (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ N := by
    intro τ
    obtain ⟨c, hc⟩ := χ.par τ
    have h0 : embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ) ≠ 0 := by
      intro h0
      have := hsq τ
      rw [h0] at this
      norm_num at this
    rw [show χ.n τ = 2 * c + N by omega, zpow_add₀ h0, zpow_mul, zpow_natCast, zpow_two, ← pow_two, hsq,
      one_zpow, one_mul]
  rw [Finset.prod_congr rfl (fun τ _ => hp τ), Finset.prod_pow] at h
  have hS : (∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ))) ^ 2 = 1 := by
    rw [← Finset.prod_pow]; exact Finset.prod_eq_one fun τ _ => hsq τ
  rcases (mul_self_eq_one_iff.1 (by rwa [pow_two] at hS)) with h1 | h1
  · exfalso
    rw [Finset.prod_div_distrib, ← Complex.ofReal_prod] at h1
    have h2 := eq_of_div_eq_one h1
    rw [h2, Complex.ofReal_re] at hneg
    exact absurd (Finset.prod_nonneg fun τ _ => norm_nonneg _) (not_le.2 hneg)
  · rw [h1] at h
    have h3 : ((-1 : ℂ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; simp
    linear_combination (-1 : ℂ) ^ N * h - ((χ.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) * h3

theorem hom_gen (N : ℕ) (ψ : (AE D)ˣ →* ℂˣ) (h1 : ∀ u, IntU D u → ψ u = 1)
    (h2 : ∀ y, ψ (y * sgU D y) = 1)
    (h3 : ∀ a : D.host.Eˣ, D.host.conj (a : D.host.E) = a → (∏ τ, embT D τ (a : D.host.E)).re < 0 →
      ((ψ (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) = (-1) ^ N)
    (h4 : ∀ (q : ℕ) (y : (AE D)ˣ), q.Prime → ¬ InertQ D q → (y : AE D) ∈ OhE D →
      (q : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D) ∈ OhE D → ψ y = 1) (B : Ideal (𝓞 D.host.E)) :
    B ≠ ⊥ → Ev D (Ideal.absNorm B) ∧ ∀ y, Gen D B y → ((ψ y : ℂˣ) : ℂ) = sgn D (Ideal.absNorm B) ^ N := by
  have huniq : ∀ {B y z}, Gen D B y → Gen D B z → ψ y = ψ z := fun hy hz => by
    have := h1 _ (hy.intU hz)
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  have hprime : ∀ P : Ideal (𝓞 D.host.E), Prime P →
      Ev D (Ideal.absNorm P) ∧ ∀ y, Gen D P y → ((ψ y : ℂˣ) : ℂ) = sgn D (Ideal.absNorm P) ^ N := by
    intro P hP
    have hP0 : P ≠ ⊥ := hP.ne_zero
    have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
    have hPm : P.IsMaximal := hPp.isMaximal hP0
    obtain ⟨hev, hfix, hmov⟩ := GlobalTheory.InertResidue.norm_prime D P hPm
    refine ⟨hev, fun y hy => ?_⟩
    by_cases hi : D.host.conj • P = P
    · obtain ⟨t, B, ht0, htc, e⟩ := GlobalTheory.T.exists_real_span_eq_conjFixedPrime_mul_relNorm D P hPp hP0 hi
      have hneg := GlobalTheory.NormSignInert.norm_neg D t P B ht0 htc hPm hi e
      have hB : B ≠ ⊥ := by
        rintro rfl
        exact ht0 (by simpa using e)
      obtain ⟨z, hz⟩ := exists_gen D B hB
      have htE : (t : D.host.E) ≠ 0 := by simpa using ht0
      have g1 := gen_span t (Units.mk0 _ htE) rfl
      have g2 := (hy.mul hz).mul hz.conj
      rw [← e] at g2
      have := huniq g1 g2
      rw [mul_assoc, map_mul, h2, mul_one] at this
      rw [← this, h3 _ htc hneg, (hfix hi).1]
    · obtain ⟨q, hq, hqP⟩ : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ P :=
        exists_prime_mem P hPp _ (by simpa [Ideal.absNorm_eq_zero_iff] using hP0) (Ideal.absNorm_mem P)
      rw [h4 q y hq ((hmov hi).2 q hq hqP) hy.1 (hy.inv_mul hqP), (hmov hi).1]
      simp
  induction B using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ B hB =>
    intro _
    rw [Ideal.isUnit_iff.1 hB, Ideal.absNorm_top]
    refine ⟨Ev.one, fun y hy => ?_⟩
    rw [h1 y ⟨hy.1, by simpa using hy.inv_mul (q := 1) Submodule.mem_top⟩, sgn_one]
    simp
  | h₃ C P hC hP ih =>
    intro _
    obtain ⟨e1, v1⟩ := hprime P hP
    obtain ⟨e2, v2⟩ := ih hC
    have n1 : Ideal.absNorm P ≠ 0 := fun h => hP.ne_zero (Ideal.absNorm_eq_zero_iff.1 h)
    have n2 : Ideal.absNorm C ≠ 0 := fun h => hC (Ideal.absNorm_eq_zero_iff.1 h)
    rw [map_mul]
    refine ⟨e1.mul e2 n1 n2, fun y hy => ?_⟩
    obtain ⟨a, ha⟩ := exists_gen D P hP.ne_zero
    obtain ⟨c, hc⟩ := exists_gen D C hC
    rw [huniq hy (ha.mul hc), map_mul, Units.val_mul, v1 a ha, v2 c hc, sgn_mul e1 e2 n1 n2, mul_pow]



theorem character_at_inert_component : ∀ (D : D7) (N : ℕ) (χ : HeckeU D N) (y : 𝓞 D.host.E) (x : (AE D)ˣ), y ≠ 0 → (∀ q : ℕ, q.Prime → (InertQ D q → ZeroAt D q ((x : AE D) - inc D (y : D.host.E))) ∧ (¬ InertQ D q → ZeroAt D q ((x : AE D) - 1))) → ((χ.f x : ℂˣ) : ℂ) = sgn D (Ideal.absNorm (Ideal.span {y})) ^ N := by
  intro D N χ y x hy0 hx
  obtain ⟨hinv, ε, hε, h1, h2, h3⟩ := GlobalTheory.NormSum.HalfIdempotent.conj_involutive_and_exists_half_idempotent D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  have he : (1 - (ε + sgA D ε)) * (1 - (ε + sgA D ε)) = 1 - (ε + sgA D ε) := by
    linear_combination h1 + h1' + 2 * h2
  have heO : 1 - (ε + sgA D ε) ∈ OhE D := sub_mem (one_mem _) (add_mem hε (VacMove.sgA_mem D hε))
  have hse : sgA D (1 - (ε + sgA D ε)) = 1 - (ε + sgA D ε) := by
    rw [map_sub, map_add (f := _), map_one, hinv, add_comm]
  have hunr : ∀ y : (AE D)ˣ, (y : AE D) ∈ OhE D →
      (1 - (ε + sgA D ε)) * ((y⁻¹ : (AE D)ˣ) : AE D) ∈ OhE D → χ.f (proj _ he y) = 1 := by
    intro y hy hy'
    refine χ.unr _ ⟨?_, ?_⟩ fun q hq hi => ?_
    · rw [proj_val]; exact add_mem (mul_mem heO hy) (sub_mem (one_mem _) heO)
    · rw [proj_inv]; exact add_mem hy' (sub_mem (one_mem _) heO)
    · convert VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) ((y : AE D) - 1) using 1
      rw [proj_val]; ring
  have hyE : (y : D.host.E) ≠ 0 := by simpa using hy0
  have key := (hom_gen N (χ.f.comp (proj _ he)) (fun u hu => hunr u hu.1 (mul_mem heO hu.2))
    (fun y => ?_) (fun a ha hneg => ?_) (fun q y hq hi hy hy' => hunr y hy ?_) (Ideal.span {y})
    (by simpa using hy0)).2 _ (gen_span y (Units.mk0 _ hyE) rfl)
  · have h0 : (ε + sgA D ε) * ((x : AE D) - 1) +
        (1 - (ε + sgA D ε)) * ((x : AE D) - inc D (y : D.host.E)) = 0 := by
      have z1 : (ε + sgA D ε) * ((x : AE D) - 1) = 0 := by
        refine (GlobalTheory.IntAdeleComplete.integral_separated_complete D).1 _
          (dvd_of_forall_prime (OhE D) _ fun q hq => ?_)
        by_cases hi : InertQ D q
        · exact VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) _
        · rw [mul_comm]; exact VacMove.zeroAt_mul D hq ((hx q hq).2 hi) _
      have z2 : (1 - (ε + sgA D ε)) * ((x : AE D) - inc D (y : D.host.E)) = 0 := by
        refine (GlobalTheory.IntAdeleComplete.integral_separated_complete D).1 _
          (dvd_of_forall_prime (OhE D) _ fun q hq => ?_)
        by_cases hi : InertQ D q
        · rw [mul_comm]; exact VacMove.zeroAt_mul D hq ((hx q hq).1 hi) _
        · exact VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) _
      rw [z1, z2, add_zero]
    have : proj _ he (Units.map (inc D).toMonoidHom (Units.mk0 _ hyE)) = x := by
      ext; rw [proj_val]
      change _ * inc D (y : D.host.E) + _ = _
      linear_combination -h0
    rwa [MonoidHom.comp_apply, this] at key
  · have : proj _ he (sgU D y) = sgU D (proj _ he y) := by
      ext
      change _ * sgA D y + _ = sgA D (_ * y + _)
      rw [map_add (f := _), map_mul, hse, map_sub, map_one, hse]
    rw [MonoidHom.comp_apply, map_mul, this, χ.norm]
  · have h4 := val_of_real_neg χ a ha hneg
    set t := Units.map (inc D).toMonoidHom a with ht
    have hst : sgA D (t : AE D) = t := by
      change sgA D (inc D a) = inc D a
      rw [GlobalTheory.NormSum.PtsMem.sgA_inc, ha]
    have : t = proj _ he t * (proj ε h1 t * sgU D (proj ε h1 t)) := by
      ext
      change (t : AE D) = (_ * t + _) * ((ε * t + _) * sgA D (ε * t + _))
      rw [map_add (f := _), map_mul, map_sub, map_one, hst]
      linear_combination ((t : AE D) - 1) ^ 2 * he -
        ((t : AE D) - 1) ^ 2 * (1 + (1 - (ε + sgA D ε)) * (t - 1)) * h2
    rw [this, map_mul, χ.norm, mul_one] at h4
    exact h4
  · obtain ⟨m, -, hm, s, hs, e⟩ := (h3 q hq).2 hi 1
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hm
    have hab' := congrArg (Int.cast : ℤ → AE D) hab
    push_cast at hab'
    rw [show (1 - (ε + sgA D ε)) * ((y⁻¹ : (AE D)ˣ) : AE D) =
      (a * s + b * (1 - (ε + sgA D ε))) * ((q : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D)) by
        linear_combination (-(1 - (ε + sgA D ε)) * ((y⁻¹ : (AE D)ˣ) : AE D)) * hab' +
          a * ((y⁻¹ : (AE D)ˣ) : AE D) * e]
    exact mul_mem (add_mem (mul_mem (intCast_mem _ _) hs) (mul_mem (intCast_mem _ _) heO)) hy'

end GlobalTheory.InertValue
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaUnit
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

section
variable {p : ℕ} [Fact p.Prime]

theorem lamC_eq (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) : lamC lam x = lam ⟨x, hx⟩ := dif_pos hx

theorem lamC_mul' (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x * y) = lamC lam x * lamC lam y := by
  rw [lamC_eq lam hx, lamC_eq lam hy, lamC_eq lam (mul_mem hx hy), ← map_mul]; rfl

theorem lamC_ne_zero (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) (h0 : x ≠ 0) : lamC lam x ≠ 0 := by
  rw [lamC_eq lam hx]
  intro h
  apply h0
  have := (map_eq_zero_iff lam lam.injective).1 h
  exact congrArg Subtype.val this

theorem intSer_one : IntSer (1 : PowerSeries ℂ_[p]) := by
  have := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 1).2 norm_one.le
  rwa [map_one] at this

theorem intSer_pow {f : PowerSeries ℂ_[p]} (hf : IntSer f) (n : ℕ) : IntSer (f ^ n) := by
  induction n with
  | zero => simpa using intSer_one (p := p)
  | succ n ih => rw [pow_succ]; exact ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ ih hf).2.2

end

theorem tors_neg' {p : ℕ} {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 p Λ t) : GL3Theta.Tors1 p Λ (-t) := by
  obtain ⟨h0, n, hn, hc, h⟩ := h
  exact ⟨by simpa using h0, n, hn, hc, by simpa using h⟩

theorem laQ_of_tors {p : ℕ} {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 p Λ t) : InRationalLattice Λ t :=
  let ⟨_, n, hn, _, h⟩ := h; ⟨n, hn, h⟩

theorem thetaTranslateOperator_zero_eq_self (Λ : AddSubgroup ℂ) (F : ℂ → ℂ) : U1 Λ 0 F = F := by
  funext z; simp [U1]

theorem thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice {Λ : AddSubgroup ℂ} (hlat : IsLat Λ) {t : ℂ} (ht : t ∉ Λ) :
    U1 Λ t (sgStar Λ) 0 ≠ 0 := by
  simp only [U1, zero_add]
  exact mul_ne_zero ((hlat.sg_eq_zero t).not.2 ht) (Complex.exp_ne_zero _)

theorem atU_smul' {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) {c : ℂ} (hc : c ∈ Qbar) {F : ℂ → ℂ} (hF : AlgEnt F) :
    AlgEnt (fun z => c * F z) ∧ g.atU (fun z => c * F z) = PowerSeries.C (lamC g.lam c) * g.atU F := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SerTransport.transport p g).2.1 c hc
  rw [← h2]
  exact ((GlobalTheory.SerTransport.transport p g).1 _ _ h1 hF).1

theorem tau_eq_C_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → (∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ‖GlobalTheory.EvenTheta.xAt g s‖ ≤ 1) →
    ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∃ w : PowerSeries ℂ_[p], GlobalTheory.EvenTheta.IntSer w ∧
      PowerSeries.constantCoeff w = 1 ∧ GlobalTheory.ThetaTransl.tau g t = PowerSeries.C (GlobalTheory.ThetaTransl.cval g t) * w := by
  intro D p _ cc δ g hg hx t ht
  have hA := GlobalTheory.T.thetaTranslatePowerSeries_pow_boundedCoeffs_of_torsion D p cc δ g hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc hst h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse x hx⟩
  obtain ⟨-, hw, -, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  have hsg : AlgEnt (sgStar g.abelian₂) := by
    have := halg 0 ⟨1, one_pos, by simp⟩
    rwa [thetaTranslateOperator_zero_eq_self] at this
  have hEi : (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [hE]; exact one_ne_zero)
  have hcon : ∀ s, InRationalLattice g.abelian₂ s → PowerSeries.constantCoeff (tau g s) = cval g s ∧
      U1 g.abelian₂ s (sgStar g.abelian₂) 0 ∈ Qbar := by
    intro s hs
    obtain ⟨c, d⟩ := (GlobalTheory.SerTransport.transport p g).2.2.1 _ (halg s hs)
    refine ⟨?_, c⟩
    rw [tau, map_mul, PowerSeries.constantCoeff_inv, hE, inv_one, one_mul, d, cval]
  have hq := laQ_of_tors ht
  have hq' := laQ_of_tors (tors_neg' ht)
  obtain ⟨c1, c2⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg t ht.1 (hwp t hq ht.1).1
  have a3 := (hcon t hq).2
  have b3 := (hcon (-t) hq').2
  have e := (atU_smul' g (mul_mem a3 b3) c1).2
  rw [funext (hlat'.sqTh_mul ht.1), ((GlobalTheory.SerTransport.transport p g).1 _ _ (halg _ hq) (halg _ hq')).1.2,
    c2, lamC_mul' _ a3 b3] at e
  have hprod : tau g t * tau g (-t) = PowerSeries.C (cval g t * cval g (-t)) *
      lineSer g.wq⁻¹ (xAt g t) := by
    simp only [tau, cval]
    linear_combination ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹) * e +
      PowerSeries.C (lamC g.lam (U1 g.abelian₂ t (sgStar g.abelian₂) 0) * lamC g.lam (U1 g.abelian₂ (-t) (sgStar g.abelian₂) 0)) *
        lineSer g.wq⁻¹ (xAt g t) * ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq + 1) * hEi

  have hL : IntSer (lineSer g.wq⁻¹ (xAt g t)) := by
    have h1 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 (xAt g t)).2 (hx t ht)
    have h2 := (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.1
    have h3 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ h2 h2).2.2
    have h4 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ h1 h3).2.2
    have h5 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ hw h4).2.1
    simpa [lineSer, _root_.sq, mul_assoc] using h5
  obtain ⟨n, hn, hcop, hnt⟩ := ht.2
  have hnt' : (n : ℂ) * (-t) ∈ g.abelian₂ := by rw [mul_neg]; exact neg_mem hnt
  have B1 := hA t ht n hn hnt
  have B2 := hA (-t) (tors_neg' ht) n hn hnt'
  set c := cval g t with hc
  set c' := cval g (-t) with hc'
  have hc0 : c ≠ 0 := lamC_ne_zero _ a3 (thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice hlat' ht.1)
  have hc0' : c' ≠ 0 := lamC_ne_zero _ b3 (thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice hlat' (tors_neg' ht).1)
  have hpow : tau g t ^ n * tau g (-t) ^ n = PowerSeries.C ((c * c') ^ n) * lineSer g.wq⁻¹ (xAt g t) ^ n := by
    rw [← mul_pow, hprod, mul_pow, map_pow]
  have hbound : ∀ k, ‖PowerSeries.coeff k (tau g t ^ n * tau g (-t) ^ n)‖ ≤ ‖c * c'‖ ^ n := by
    intro k
    rw [hpow, PowerSeries.coeff_C_mul, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (intSer_pow hL n k)
  have G := GlobalTheory.EvenTheta.sup_norm_mul_padicComplex p _ _ _ B1 B2 hbound
  have h0' : PowerSeries.coeff 0 (tau g (-t) ^ n) = c' ^ n := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, (hcon _ hq').1]
  have hcn : 0 < ‖c'‖ ^ n := pow_pos (norm_pos_iff.2 hc0') n
  have hle : ∀ i, ‖PowerSeries.coeff i (tau g t ^ n)‖ ≤ ‖c‖ ^ n := by
    intro i
    have := G i 0
    rw [h0', norm_pow, norm_mul, mul_pow] at this
    exact le_of_mul_le_mul_right this hcn
  set s := PowerSeries.C c⁻¹ * tau g t with hs
  have hsn : IntSer (s ^ n) := by
    intro k
    rw [hs, mul_pow, ← map_pow, PowerSeries.coeff_C_mul, norm_mul, norm_pow, norm_inv]
    have hcp : 0 < ‖c‖ ^ n := pow_pos (norm_pos_iff.2 hc0) n
    calc ‖c‖⁻¹ ^ n * ‖PowerSeries.coeff k (tau g t ^ n)‖ ≤ ‖c‖⁻¹ ^ n * ‖c‖ ^ n :=
          mul_le_mul_of_nonneg_left (hle k) (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ (norm_ne_zero_iff.2 hc0), one_pow]
  have hs0 : PowerSeries.constantCoeff s = 1 := by
    rw [hs, map_mul, PowerSeries.constantCoeff_C, (hcon t hq).1, inv_mul_cancel₀ hc0]
  refine ⟨s, GlobalTheory.T.powerSeriesCoeffNormLeOne_root_coprime_padic p n hn hcop s hs0 hsn, hs0, ?_⟩
  rw [hs, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]

end GlobalTheory.ThetaUnit
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl

theorem gl_det_eq_one_of_mem_unip {κ : Type} [CommRing κ] {r : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unip κ r) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular (M := (g : Matrix (Fin r) (Fin r) κ))
    (fun i j h => unip_lower hg h)]
  simp [unip_diag hg]

theorem chi_eq_one_of_mem_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (h : R.IsGrp F) :
    ∀ i, ∀ u ∈ F.P0, (R.FW i).chi u = 1 := by
  intro i u hu
  obtain ⟨ψ, -, h0, -⟩ := h.levels
  have h1 : F.P0.comap R.eG.symm.toMonoidHom = Subgroup.pi Set.univ (fun v : R.Pg => unip (kP v.1) D.R.r) :=
    congrArg LevelP.H h0
  have h2 : R.eG u ∈ F.P0.comap R.eG.symm.toMonoidHom := by
    rw [Subgroup.mem_comap]; simpa using hu
  rw [h1] at h2
  apply Units.ext
  apply D.what₂.embLL.injective
  rw [h.chiW i u, Units.val_one, map_one]
  refine Finset.prod_eq_one fun PP _ => ?_
  rw [gl_det_eq_one_of_mem_unip (h2 PP (Set.mem_univ _)), map_one, Units.val_one]

end GlobalTheory.TraceIncl
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCoord

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Cx
open GlobalTheory.FormTies GlobalTheory.OnTies
open GlobalTheory.OntoChain (coordMap thetaMat thetaOp liftLvl liftSub supLat Mir mirIncl uni mirToGL)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem chi_eq_one (hG : R.IsGrp F) (i : Fin D.R.m) {g : G} (hg : g ∈ F.P0) : (R.FW i).chi g = 1 := by
  obtain ⟨u, hu, rfl⟩ := (OntoChain.mem_base_iff hG.levels g).1 hg
  have h1 := (OntoChain.mem_pi_unip_iff R _).2 ⟨u, hu, rfl⟩
  refine Units.ext (D.what₂.embLL.injective ?_)
  rw [hG.chiW, Units.val_one, map_one, OntoChain.eG_mirIncl]
  refine Finset.prod_eq_one fun v _ => ?_
  have h2 := h1 v (Set.mem_univ v)
  have h3 : Matrix.GeneralLinearGroup.det (mirToGL R u v) = 1 := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular h2.1]
    exact Finset.prod_eq_one fun k _ => h2.2 k
  rw [h3, map_one, Units.val_one]

end Real

end GlobalTheory.OnCoord
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tameHeckeChar_trivial_on_finiteUnits_cong_one : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → (∀ P, χ.TameAt P) → ∀ m : ℕ, (∀ P : HeightOneSpectrum (𝓞 D.host.E), (m : 𝓞 D.host.E) ∉ P.asIdeal → χ.UnrAt P) → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = m • y) → c x = 1 := by
  first | exact @GlobalTheory.tame_heckeChar_eq_one_of_finUnit | exact GlobalTheory.tame_heckeChar_eq_one_of_finUnit | (intros; apply GlobalTheory.tame_heckeChar_eq_one_of_finUnit <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.vacuum_image_intertwiner_selfDual_pair : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L' L₁ L₁', SD D L → SD D L' → SD D L₁ → SD D L₁' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ThetaVectorUpToUnits D (tor0 D cc δ) t0 L₁ L₁' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (G : VC D a d → ℂ)) := by
  first | exact @GlobalTheory.ArchFree.firstBasisVectorLike.isVacuum_thetaIntertwiner_selfDual | exact GlobalTheory.ArchFree.firstBasisVectorLike.isVacuum_thetaIntertwiner_selfDual | (intros; apply GlobalTheory.ArchFree.firstBasisVectorLike.isVacuum_thetaIntertwiner_selfDual <;> assumption)
end
