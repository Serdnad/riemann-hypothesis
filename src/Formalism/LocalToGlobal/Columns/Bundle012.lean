module

public import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Columns.Bundle004
public import Formalism.LocalToGlobal.GlobalTheory.GL4.PDetAll
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Columns.Bundle006
public import Formalism.LocalToGlobal.Columns.Bundle007
public import Formalism.LocalToGlobal.Columns.RowForms
import Formalism.QuotientMetricDivisors.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section DiaMoves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

instance diaAction : MulAction (DiaG (E := E) (ST := ST)) (DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) where
  smul c d := d.dia c
  one_smul := DecoSet.dia_one
  mul_smul c c' d := DecoSet.dia_mul c c' d

theorem DecoSet.dia_smul_def (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : c • d = d.dia c := rfl

end DiaMoves

section OpsL

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

theorem diamond_action_apply (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (φ : (formGSD C Λ).EqFun) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) :
    ((diamondOperatorOnForms' C Λ P c φ : (formGSD C Λ).EqFun) : (formGSD C Λ).D → (formGSD C Λ).V) d =
      (φ : (formGSD C Λ).D → (formGSD C Λ).V) (d.dia1 P c) := by
  unfold diamondOperatorOnForms'
  exact LocOp.ofMap_op_apply (S := formGSD C Λ) (S' := formGSD C Λ) _ _ _ _ _ φ d


end OpsL

section ColsL

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem pow_mem {M : Type*} [AddCommGroup M] [Module X.K M] (p : Submodule X.K M)
    (A : Module.End X.K M) (h : ∀ φ ∈ p, A φ ∈ p) (k : ℕ) : ∀ φ ∈ p, (A ^ k) φ ∈ p := by
  induction k with
  | zero => intro φ hφ; simpa using hφ
  | succ k ih =>
    intro φ hφ
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (h φ hφ)

end ColsL

section SeenL

variable {X : Fields} {Pr : Primes X}

theorem mem_pullW (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) (x : 𝓞 X.E) :
    x ∈ (pullW τ w).asIdeal ↔ X.embO τ x ∈ w.asIdeal := Iff.rfl

theorem pullW_mem_vT (hPr : Pr.Ok) (u : Pr.Word) (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) :
    pullW τ w ∈ Pr.vT u ↔ X.embO τ (Pr.piT u) ∈ w.asIdeal :=
  mem_divs (hPr.piT_ne_zero u) _

theorem embO_of_Kq {x : 𝓞 X.E} (hx : (x : X.E) ∈ X.Kq) (τ τ' : X.Tau) : X.embO τ x = X.embO τ' x :=
  RingOfIntegers.ext (hx τ τ')

theorem conjO_mem_Kq (hX : X.Ok) {x : 𝓞 X.E} (hx : (x : X.E) ∈ X.Kq) : ((X.conjO x : 𝓞 X.E) : X.E) ∈ X.Kq := by
  intro τ τ'
  show X.emb τ (star (x : X.E)) = X.emb τ' (star (x : X.E))
  rw [hX.emb_star, hX.emb_star, hx τ τ']

theorem seenC_iff (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) :
    seenC Pr u w ↔ ∀ τ, pullW τ w ∈ Pr.vT u :=
  forall_congr' fun τ => (pullW_mem_vT hPr u τ w).symm

theorem seenC_or_seenBarC (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K))
    (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) : seenC Pr u w ∨ seenBarC Pr u w := by
  by_cases hne : Nonempty X.Tau
  · obtain ⟨τ₀⟩ := hne
    have h1 : X.embO τ₀ (Pr.piT u) * X.embO τ₀ (X.conjO (Pr.piT u)) ∈ w.asIdeal := by
      rw [← map_mul, hPr.piT_norm u, map_natCast]
      exact hw
    rcases w.isPrime.mem_or_mem h1 with h | h
    · left
      intro τ
      rw [embO_of_Kq (hPr.piT_Kq u) τ τ₀]
      exact h
    · right
      intro τ
      rw [embO_of_Kq (conjO_mem_Kq hX (hPr.piT_Kq u)) τ τ₀]
      exact h
  · left
    intro τ
    exact absurd ⟨τ⟩ hne

theorem not_seen_both (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau)
    (h1 : X.embO τ (Pr.piT u) ∈ w.asIdeal) (h2 : X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal) : False := by
  obtain ⟨a, b, e⟩ := hPr.piT_cop u
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have e' := congrArg (X.embO τ) e
  rw [map_add (f := _), map_mul, map_mul, map_one] at e'
  rw [← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

variable {R : Ranks} (W : Wts X Pr.Word R)

end SeenL

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain IntermediateField Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV

section Res

variable {A : Type} [CommRing A] [Finite A] {p : ℕ}

def owedC_res (hp : p.Prime) (h : Nat.card A = p) : A ≃+* ZMod p :=
  letI := Fintype.ofFinite A
  (ZMod.ringEquivOfPrime A hp (by rw [← Nat.card_eq_fintype_card]; exact h)).symm

theorem owedC_res_intCast (hp : p.Prime) (h : Nat.card A = p) (a : ℤ) :
    owedC_res hp h (a : A) = (a : ZMod p) := map_intCast _ _

theorem owedC_exists_int (hp : p.Prime) (h : Nat.card A = p) (x : A) : ∃ a : ℤ, x = (a : A) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨((owedC_res hp h x).val : ℤ), ?_⟩
  apply (owedC_res hp h).injective
  rw [owedC_res_intCast]
  simp

theorem owedC_intCast_eq_iff (hp : p.Prime) (h : Nat.card A = p) (a b : ℤ) :
    (a : A) = (b : A) ↔ (p : ℤ) ∣ a - b := by
  rw [← (owedC_res hp h).injective.eq_iff, owedC_res_intCast, owedC_res_intCast,
    ZMod.intCast_eq_intCast_iff_dvd_sub, ← dvd_neg, neg_sub]

variable {K : Type} [Field K]

end Res

section Chars

variable {X : Fields} {Pr : Primes X}

theorem card_quotient_eq_prime (hPr : Pr.Ok) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    Nat.card (𝓞 X.E ⧸ P.1.asIdeal) = Pr.T u := by
  rw [← hPr.vT_norm u P.1 P.2, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end Chars

section Weil

variable {X : Fields} {Pr : Primes X}

def CharT.psiC (Ps : CharT X Pr) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    AddChar (𝓞 X.E ⧸ P.1.asIdeal) ℂ :=
  (σ₀ : X.K →* ℂ).compAddChar (Ps.psiT u P)

theorem CharT.psiC_apply (Ps : CharT X Pr) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u})
    (c : 𝓞 X.E ⧸ P.1.asIdeal) : Ps.psiC σ₀ u P c = σ₀ (Ps.psiT u P c) := rfl

theorem CharT.Ok.psiC_ne {Ps : CharT X Pr} (h : Ps.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    Ps.psiC σ₀ u P ≠ 1 := by
  intro h1
  apply h.ne u P
  ext c
  apply σ₀.injective
  rw [← CharT.psiC_apply, h1, AddChar.one_apply, AddChar.one_apply, map_one]

end Weil

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end Gauss

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Idem

variable {K : Type} [Field K] {A : Type} [Group A] {M : Type} [Group M] [Fintype M]


end Idem

section Gen

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG) {A : Type} [Group A] [Fintype A]
  (ι : A →* GLG (E := X.E) (n := n) (SG := SG)) (hι : ∀ a w, (Λ w).NormBy (ι a w))
  {M : Type} [Group M] [Fintype M] (j : M →* A) (ε : M →* X.Kˣ)

end Gen

section StabComb

variable (κ : Type) [CommRing κ] {n : ℕ}

variable {κ}

end StabComb

section Stab

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end Stab

section StabPt

variable {X : Fields} {n : ℕ} [NeZero n] {SG : Finset (HeightOneSpectrum (𝓞 X.E))}


end StabPt

section Scal

variable {E : Type} [Field E] [NumberField E]



end Scal

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)



end Rows

section ScalAct

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end ScalAct

section RhoScal

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem tensorWeights_scalar_action (lam : ι → DomWeight n) (t : ι → Kˣ) :
    rhoK lam (fun τ => (brpSc K (t τ) : GL (Fin n) K)) =
      (∏ τ, ((t τ : K) ^ (∑ i, (lam τ).w i))) • (1 : Module.End K (VV K lam)) := by
  classical
  have key : ∀ S : Finset ι, rhoK lam (fun τ => if τ ∈ S then (brpSc K (t τ) : GL (Fin n) K) else 1) =
      (∏ τ ∈ S, ((t τ : K) ^ (∑ i, (lam τ).w i))) • (1 : Module.End K (VV K lam)) := by
    intro S
    refine Finset.induction_on S ?_ (fun a S ha ih => ?_)
    · have h0 : (fun τ : ι => if τ ∈ (∅ : Finset ι) then (brpSc K (t τ) : GL (Fin n) K) else 1) = 1 := by
        funext τ
        simp
      rw [h0, map_one, Finset.prod_empty, one_smul]
    · have h0 : (fun τ => if τ ∈ insert a S then (brpSc K (t τ) : GL (Fin n) K) else 1) =
          Pi.mulSingle a (brpSc K (t a) : GL (Fin n) K) * (fun τ => if τ ∈ S then (brpSc K (t τ) : GL (Fin n) K) else 1) := by
        funext τ
        by_cases hτ : τ = a
        · subst hτ
          simp [ha]
        · have h1 : τ ∈ insert a S ↔ τ ∈ S := by simp [hτ]
          simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hτ, one_mul]
          by_cases h2 : τ ∈ S
          · rw [if_pos (h1.mpr h2), if_pos h2]
          · rw [if_neg (fun h => h2 (h1.mp h)), if_neg h2]
      rw [h0, map_mul, ih, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.rhoK_single_scalar, Finset.prod_insert ha, smul_mul_smul, one_mul]
      rfl
  have h := key Finset.univ
  simp only [Finset.mem_univ, if_true] at h
  exact h

end RhoScal

section RhoScal2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} [NeZero n]


end RhoScal2

section RowsScal

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)



end RowsScal

section LamKEv

end LamKEv

section RowsMain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)




end RowsMain

section RowsMainV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)




end RowsMainV

section Card

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end Card

section RowsCard

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end RowsCard

section NotFaithful

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)



end NotFaithful

end Formalism.L2.Col
end
end
