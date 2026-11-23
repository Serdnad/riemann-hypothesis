module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.TwiceValuationFactorialProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Fock

variable {R : Type} [CommRing R] {σ : Type}

theorem fockR_add (G T₁ T₂ : MvPolynomial σ R) : fock G (T₁ + T₂) = fock G T₁ + fock G T₂ := by
  simp only [fock, MvPolynomial.coeff_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem fockR_zero (G : MvPolynomial σ R) : fock G 0 = 0 := by
  simp [fock]

theorem fockR_sum {ι : Type} (G : MvPolynomial σ R) (s : Finset ι) (f : ι → MvPolynomial σ R) :
    fock G (∑ i ∈ s, f i) = ∑ i ∈ s, fock G (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [fockR_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fockR_add, ih]

theorem fockR_monomial (G : MvPolynomial σ R) (mo : σ →₀ ℕ) (c : R) :
    fock G (monomial mo c) = G.coeff mo * c * (expFact mo : R) := by
  unfold fock
  rw [Finset.sum_eq_single mo]
  · simp [coeff_monomial]
  · intro b _ hb
    simp [coeff_monomial, Ne.symm hb]
  · intro h
    simp [MvPolynomial.notMem_support_iff.1 h]

end Fock

section Split

variable {T : Type} [Fintype T] {r K : ℕ}

theorem sum_split {M : Type} [AddCommMonoid M] (f : T × Fin (r + K) → M) :
    ∑ v, f v = (∑ v : T × Fin r, f (v.1, Fin.castAdd K v.2)) + ∑ v : T × Fin K, f (v.1, Fin.natAdd r v.2) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Fin.sum_univ_add _

end Split

section Mon

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (hk : m + 1 = r + K) {J : ℕ} [NeZero J]
  (nL : ZMod J → ℕ)

def tvar (v : TL J nL r × Fin (r + K)) : TV n' (m + 1) := (posOf n' (posTL Fr v.1), Fin.cast hk.symm v.2)

theorem plVar_eq (x : TL J nL r) (a : Fin r) : plVar Fr hk nL x a = tvar Fr hk nL (x, Fin.castAdd K a) := rfl

theorem noVar_eq (x : TL J nL r) (b : Fin K) : noVar Fr hk nL x b = tvar Fr hk nL (x, Fin.natAdd r b) := rfl

def joinE (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) : TL J nL r × Fin (r + K) → ℕ :=
  fun v => Fin.addCases (fun a => bp (v.1, a)) (fun b => bn (v.1, b)) v.2

theorem joinE_left (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) (x : TL J nL r) (a : Fin r) :
    joinE nL bp bn (x, Fin.castAdd K a) = bp (x, a) := by
  simp [joinE]

theorem joinE_right (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) (x : TL J nL r) (b : Fin K) :
    joinE nL bp bn (x, Fin.natAdd r b) = bn (x, b) := by
  simp [joinE]

def bigE (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    TL J nL r × Fin (r + K) → ℕ :=
  fun v => rho v + lowP Fr p v.1 * joinE nL bp bn v

def bigM (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    TV n' (m + 1) →₀ ℕ :=
  Finsupp.mapDomain (tvar Fr hk nL) (Finsupp.equivFunOnFinite.symm (bigE Fr p nL rho bp bn))

def mPl (bp : TL J nL r × Fin r →₀ ℕ) : TV n' (m + 1) →₀ ℕ :=
  ∑ v : TL J nL r × Fin r, Finsupp.single (plVar Fr hk nL v.1 v.2) (lowP Fr p v.1 * bp v)

def mNo (bn : TL J nL r × Fin K →₀ ℕ) : TV n' (m + 1) →₀ ℕ :=
  ∑ v : TL J nL r × Fin K, Finsupp.single (noVar Fr hk nL v.1 v.2) (lowP Fr p v.1 * bn v)

theorem labMon_eq (rho : TL J nL r × Fin (r + K) → ℕ) :
    labMon Fr hk nL rho = ∑ v : TL J nL r × Fin (r + K), Finsupp.single (tvar Fr hk nL v) (rho v) := by
  rw [labMon, sum_split, Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  rfl

theorem bigM_eq (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    labMon Fr hk nL rho + mPl Fr p hk nL bp + mNo Fr p hk nL bn = bigM Fr p hk nL rho bp bn := by
  have hmd : bigM Fr p hk nL rho bp bn =
      ∑ v : TL J nL r × Fin (r + K), Finsupp.single (tvar Fr hk nL v) (bigE Fr p nL rho bp bn v) := by
    rw [bigM, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp)]
    rfl
  rw [hmd, labMon_eq]
  simp only [bigE, Finsupp.single_add, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 1
  rw [sum_split]
  simp only [joinE_left, joinE_right]
  rfl

variable {Fr p hk nL}

theorem tvar_inj (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x)) :
    Function.Injective (tvar Fr hk nL) := by
  intro v w h
  simp only [tvar, Prod.mk.injEq] at h
  exact Prod.ext (hinj h.1) (Fin.cast_injective _ h.2)

theorem bigM_apply (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (v : TL J nL r × Fin (r + K)) : bigM Fr p hk nL rho bp bn (tvar Fr hk nL v) = bigE Fr p nL rho bp bn v := by
  rw [bigM, Finsupp.mapDomain_apply_of_injective (tvar_inj hinj)]
  rfl

theorem bigM_pl (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (x : TL J nL r) (a : Fin r) :
    bigM Fr p hk nL rho bp bn (plVar Fr hk nL x a) = rho (x, Fin.castAdd K a) + lowP Fr p x * bp (x, a) := by
  rw [plVar_eq, bigM_apply hinj]
  simp only [bigE, joinE_left]

theorem bigM_no (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (x : TL J nL r) (b : Fin K) :
    bigM Fr p hk nL rho bp bn (noVar Fr hk nL x b) = rho (x, Fin.natAdd r b) + lowP Fr p x * bn (x, b) := by
  rw [noVar_eq, bigM_apply hinj]
  simp only [bigE, joinE_right]

theorem bigM_notin (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (w : TV n' (m + 1)) (hw : w ∉ Set.range (tvar Fr hk nL)) : bigM Fr p hk nL rho bp bn w = 0 := by
  rw [bigM]
  exact Finsupp.mapDomain_notin_range _ _ hw

theorem eq_bigM (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (hz : ∀ w, w ∉ Set.range (tvar Fr hk nL) → mo w = 0) (hlow : InLow Fr p hk nL rho mo) :
    mo = bigM Fr p hk nL rho (plMon Fr p hk nL mo) (noMon Fr p hk nL mo) := by
  ext w
  by_cases hw : w ∈ Set.range (tvar Fr hk nL)
  · obtain ⟨⟨x, c⟩, rfl⟩ := hw
    rw [bigM_apply hinj]
    induction c using Fin.addCases with
    | left a =>
      simp only [bigE, joinE_left, plMon, Finsupp.coe_equivFunOnFinite_symm, ← hlow.1 x a]
      exact (Nat.mod_add_div _ _).symm
    | right b =>
      simp only [bigE, joinE_right, noMon, Finsupp.coe_equivFunOnFinite_symm, ← hlow.2 x b]
      exact (Nat.mod_add_div _ _).symm
  · rw [bigM_notin _ _ _ _ hw, hz w hw]

theorem lowP_pos (hp : 0 < p) (x : TL J nL r) : 0 < lowP Fr p x := by
  unfold lowP
  exact pow_pos hp _

theorem bigM_inLow (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (hrho : ∀ x c, rho (x, c) < lowP Fr p x)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    InLow Fr p hk nL rho (bigM Fr p hk nL rho bp bn) := by
  refine ⟨fun x a => ?_, fun x b => ?_⟩
  · rw [bigM_pl hinj, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hrho _ _)]
  · rw [bigM_no hinj, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hrho _ _)]

theorem bigM_plMon (hp : 0 < p) (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (hrho : ∀ x c, rho (x, c) < lowP Fr p x)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    plMon Fr p hk nL (bigM Fr p hk nL rho bp bn) = bp := by
  ext ⟨x, a⟩
  simp only [plMon, Finsupp.coe_equivFunOnFinite_symm]
  rw [bigM_pl hinj, Nat.add_mul_div_left _ _ (lowP_pos hp x), Nat.div_eq_of_lt (hrho _ _), zero_add]

theorem bigM_noMon (hp : 0 < p) (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (hrho : ∀ x c, rho (x, c) < lowP Fr p x)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    noMon Fr p hk nL (bigM Fr p hk nL rho bp bn) = bn := by
  ext ⟨x, b⟩
  simp only [noMon, Finsupp.coe_equivFunOnFinite_symm]
  rw [bigM_no hinj, Nat.add_mul_div_left _ _ (lowP_pos hp x), Nat.div_eq_of_lt (hrho _ _), zero_add]

theorem bigM_inBlock (hp : 0 < p) (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (hrho : ∀ x c, rho (x, c) < lowP Fr p x)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) (dPl dNo : TL J nL r → ℕ)
    (h1 : ∀ x, multideg bp x = dPl x) (h2 : ∀ x, multideg bn x = dNo x) :
    InBlock Fr p hk nL dPl dNo (bigM Fr p hk nL rho bp bn) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [← h1 x]
    unfold multideg
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [bigM_pl hinj, Nat.add_mul_div_left _ _ (lowP_pos hp x), Nat.div_eq_of_lt (hrho _ _), zero_add]
  · rw [← h2 x]
    unfold multideg
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [bigM_no hinj, Nat.add_mul_div_left _ _ (lowP_pos hp x), Nat.div_eq_of_lt (hrho _ _), zero_add]

end Mon

end Formalism.MainNotions.Proposition5Numerics
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

def gamR (P rho be : ℕ) : ℚ :=
  ((rho + P * be).factorial : ℚ) / ((rho.factorial : ℚ) * (be.factorial : ℚ) * (P.factorial : ℚ) ^ be)

def diagK {Kf : Type} [Field Kf] {σ : Type} (g : (σ →₀ ℕ) → Kf) (F : MvPolynomial σ Kf) : MvPolynomial σ Kf :=
  ∑ mo ∈ F.support, monomial mo (g mo * F.coeff mo)

section Dig

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

def gamPl (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) : ℚ :=
  ∏ v : TL J nL r × Fin r, gamR (lowP Fr p v.1) (rho (v.1, Fin.castAdd K v.2)) (bp v)

def gamNo (rho : TL J nL r × Fin (r + K) → ℕ) (bn : TL J nL r × Fin K →₀ ℕ) : ℚ :=
  ∏ v : TL J nL r × Fin K, gamR (lowP Fr p v.1) (rho (v.1, Fin.natAdd r v.2)) (bn v)

def cstOf (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) : ℕ :=
  (∏ v : TL J nL r × Fin (r + K), (rho v).factorial) * ∏ x : TL J nL r, (lowP Fr p x).factorial ^ (dPl x + dNo x)

def classOf (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r × Fin (r + K) → ℕ :=
  fun v => Fin.addCases (fun a => mo (plVar Fr hk nL v.1 a) % lowP Fr p v.1)
    (fun b => mo (noVar Fr hk nL v.1 b) % lowP Fr p v.1) v.2

def blkPl (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r → ℕ := fun x => ∑ a : Fin r, mo (plVar Fr hk nL x a) / lowP Fr p x

def blkNo (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r → ℕ := fun x => ∑ b : Fin K, mo (noVar Fr hk nL x b) / lowP Fr p x

def DigFacts (d : Fin n' → ℕ) : Prop :=
  ∀ G : MvPolynomial (TV n' (m + 1)) (KK O), HasMultideg G d →
    (∀ (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ), (∀ x c, rho (x, c) < lowP Fr p x) →
      ∀ A ∈ Pol (KK O) r dPl, ∀ N ∈ Pol (KK O) K dNo,
        fock G (asm Fr p O hk nL rho A N) = ((cstOf Fr p nL rho dPl dNo : ℕ) : KK O) *
          ∑ bp ∈ A.support, ∑ bn ∈ N.support, ((levImg Fr p hk nL rho dPl dNo G).coeff bp).coeff bn *
            (((gamPl Fr p nL rho bp : ℚ) : KK O) * A.coeff bp * ((expFact bp : ℕ) : KK O)) *
            (((gamNo Fr p nL rho bn : ℚ) : KK O) * N.coeff bn * ((expFact bn : ℕ) : KK O))) ∧
    (∀ (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (bp : TL J nL r × Fin r →₀ ℕ),
      (levImg Fr p hk nL rho dPl dNo G).coeff bp ∈ Pol (KK O) K dNo) ∧
    ∀ mo ∈ G.support,
      BlockOK Fr p nL d (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo) ∧
      ((levImg Fr p hk nL (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo) G).coeff
        (plMon Fr p hk nL mo)).coeff (noMon Fr p hk nL mo) = G.coeff mo ∧
      (∀ x, multideg (plMon Fr p hk nL mo) x = blkPl Fr p hk nL mo x) ∧
      (∀ x, multideg (noMon Fr p hk nL mo) x = blkNo Fr p hk nL mo x) ∧
      ((expFact mo : ℕ) : ℚ) = ((cstOf Fr p nL (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo) : ℕ) : ℚ) *
        ((expFact (plMon Fr p hk nL mo) : ℕ) : ℚ) * ((expFact (noMon Fr p hk nL mo) : ℕ) : ℚ) *
        gamPl Fr p nL (classOf Fr p hk nL mo) (plMon Fr p hk nL mo) *
        gamNo Fr p nL (classOf Fr p hk nL mo) (noMon Fr p hk nL mo)

end Dig

section Parts

variable (p : ℕ) {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (Fr : Frames n' r) {J : ℕ} [NeZero J]

def DnoOf (nL : ZMod J → ℕ) (dNo : TL J nL r → ℕ) : ℕ :=
  ∑ i : Σ j : ZMod J, Fin (nL j + r + 1), N0 K * Nat.log p (2 * degIn dNo (NSet nL i.1 i.2.val) + K - 1)

def JPOK (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
    (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))) : Prop :=
  IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e ∧
  (∀ F G, fock (e F) G = fock F (e G)) ∧
  (∀ F ∈ Pol (KK O) K dNo, e F ∈ Pol (KK O) K dNo ∧
    (InBB (O := O) p F → InBB (O := O) p (((p : KK O) ^ DnoOf (K := K) p Dt.nL dNo) • e F))) ∧
  ∀ F i, e F ∈ isoSub (normE p K Dt i) (ka i.1 i.2.val)

def JPAt (Dt : SignedChainData p O r J) : Prop :=
  ∀ (dNo : TL J Dt.nL r → ℕ), ∀ y ∈ Pol (KK O) K dNo,
    ∃ (ka : ZMod J → ℕ → Fin K → ℤ) (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      JPOK p O Dt dNo ka e ∧ vBB (O := O) p (e y) ≤ vBB (O := O) p y

def NoAt (cP : ℕ) (Dt : SignedChainData p O r J) : Prop :=
  ∀ (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ) (rho : TL J Dt.nL r × Fin (r + K) → ℕ)
    (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))) (nu : TL J Dt.nL r × Fin K →₀ ℕ),
    (∀ x c, rho (x, c) < lowP Fr p x) → JPOK p O Dt dNo ka e → (∀ x, multideg nu x = dNo x) →
    ∃ (N0 : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) (cY : KK O),
      NormTest p O cP Dt dNo ka N0 ∧
      leQ (vK p cY) ((padicValNat p (∏ x, (dNo x).factorial) : ℝ) / 2 + DnoOf (K := K) p Dt.nL dNo -
        (padicValNat p (expFact nu) : ℝ) / 2) ∧
      CoefGe p (N0 - diagK (fun bn => ((gamNo Fr p Dt.nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1))) cP

def GaAt (nL : ZMod J → ℕ) : Prop :=
  ∀ rho : TL J nL r × Fin (r + K) → ℕ, (∀ x c, rho (x, c) < lowP Fr p x) →
    (∀ bn : TL J nL r × Fin K →₀ ℕ, gamNo Fr p nL rho bn ≠ 0 ∧ padicValRat p (gamNo Fr p nL rho bn) = 0) ∧
    (∀ bp : TL J nL r × Fin r →₀ ℕ, gamPl Fr p nL rho bp ≠ 0 ∧ padicValRat p (gamPl Fr p nL rho bp) = 0) ∧
    ∃ ga : (TL J nL r × Fin r →₀ ℕ) → O, (∀ al, IsUnit (ga al)) ∧
      (∀ al, algebraMap O (KK O) (ga al) = ((gamPl Fr p nL rho al : ℚ) : KK O)) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ ε : Bool, ∃ lam : (TL J nL r × Fin r →₀ ℕ) →₀ O,
        (∀ m ∈ lam.support, (m.sum fun _ e => e) ≤ 6 * k) ∧
        ∀ al : TL J nL r × Fin r →₀ ℕ,
          geQ (vK p ((if ε then algebraMap O (KK O) (ga al) else (algebraMap O (KK O) (ga al))⁻¹) -
            binomCombF (K := KK O) lam al)) (k : ℝ)

def SizeAt (nL : ZMod J → ℕ) (d : Fin n' → ℕ) (Dn : ℝ) : Prop :=
  ∀ (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ), BlockOK Fr p nL d rho dPl dNo →
    ∀ (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ),
      (∀ x, multideg bp x = dPl x) → (∀ x, multideg bn x = dNo x) →
      (DnoOf (K := K) p nL dNo : ℝ) +
        ((padicValNat p (∏ x, (dPl x).factorial) : ℝ) - (padicValNat p (expFact bp) : ℝ)) / 2 +
        ((padicValNat p (∏ x, (dNo x).factorial) : ℝ) - (padicValNat p (expFact bn) : ℝ)) / 2 ≤ Dn

end Parts

end Formalism.MainNotions.Proposition5Numerics
end
end
