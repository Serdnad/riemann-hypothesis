module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle007
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Bundle002
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle003
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.KerT

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree (AgreeOff InBox JetsIn moveScal)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word) (i j : ℕ)

def ker (N : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (fr : Frs X.E (R.N i) (rowSG Pr sel mu))
    (N' : Submodule (𝓞 X.E) (Sp X.E (R.N j))) (fr' : Frs X.E (R.N j) (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) (R.N j) → X.K) :
    VV X.K (W.lamTrue u i) →ₗ[X.K] VV X.K (W.lamTrue u j) :=
  kerOf (stepT W Ch sel mu cst A u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N fr N' fr' Ξ

def term {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := SG))
    (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (d' : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := SG')) (fr' : Frs X.E (R.N j) (rowSG Pr sel mu))
    (Ξ₀ : HomE X.E (R.N i) (R.N j) → X.K) : VV X.K (W.lamTrue u i) →ₗ[X.K] VV X.K (W.lamTrue u j) :=
  ker W Ch sel mu cst A u i j d.1.N fr d'.1.N fr' fun x => phiT X.K d.1 d'.1 x * Ξ₀ x

def InBoxOfRowSelection {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ₀ : HomE X.E a b → X.K) : Prop :=
  InBox (rowSG Pr sel mu) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ₀

abbrev Framed {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n SB) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.IsFrames N fr

def JetsAll : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N' : Submodule (𝓞 X.E) (Sp X.E (R.N j))), IsSdLat N → IsSdLat N' →
    JetsIn A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N N'

def MoveStep : Prop :=
  ∀ (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E (R.N j)))
    (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (fr' : Frs X.E (R.N j) (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) (R.N j) → X.K),
    IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' → AgreeOff (Pr.T u) N₁ N₂ → AgreeOff (Pr.T u) N₁' N₂' →
    InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ →
    InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ →
    ker W Ch sel mu cst A u i j N₁ fr N₁' fr' Ξ = moveScal Ch mu u i N₁ N₂ N₁' N₂' • ker W Ch sel mu cst A u i j N₂ fr N₂' fr' Ξ

def RatStep : Prop :=
  ThEquivP (stepT W Ch sel mu cst A u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
    ((rhoVr X.emb (W.lamTrue u i)).comp (ufGL X.E (R.N i))) ((rhoVr X.emb (W.lamTrue u j)).comp (ufGL X.E (R.N j)))

def RatTerm : Prop :=
  ∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := SG)) (fr : Frs X.E (R.N i) (rowSG Pr sel mu))
    (d' : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := SG')) (fr' : Frs X.E (R.N j) (rowSG Pr sel mu)) (Ξ₀ : HomE X.E (R.N i) (R.N j) → X.K)
    (γ : UF X.E (R.N i)) (γ' : UF X.E (R.N j)), InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ →
    term W Ch sel mu cst A u i j (((γ, 1) : UF X.E (R.N i) × GLG (E := X.E) (n := R.N i) (SG := SG)) • d) (fun P => γ.1 * fr P)
        (((γ', 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := SG')) • d') (fun P => γ'.1 * fr' P)
        (fun x => Ξ₀ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap)) =
      (rhoVr X.emb (W.lamTrue u j) (ufGL X.E (R.N j) γ')) ∘ₗ term W Ch sel mu cst A u i j d fr d' fr' Ξ₀ ∘ₗ
        (rhoVr X.emb (W.lamTrue u i) (ufGL X.E (R.N i) γ⁻¹))

def UKTerm : Prop :=
  ∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := SG)) (fr : Frs X.E (R.N i) (rowSG Pr sel mu))
    (d' : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := SG')) (fr' : Frs X.E (R.N j) (rowSG Pr sel mu)) (Ξ₀ : HomE X.E (R.N i) (R.N j) → X.K)
    (P : Pr.vT u) (y : VV X.K (W.lamTrue u i)), MoveHyp (Pr.vT u) SG P → MoveHyp (Pr.vT u) SG' P →
    InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ →
    (∑ᶠ d₁ ∈ {d₁ : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := SG') | d'.1.IsUp P (Pr.T u : 𝓞 X.E) d₁.1},
        term W Ch sel mu cst A u i j d fr d₁ fr' Ξ₀ y) =
      ((Pr.T u : X.K) ^ ((R.t + 1) / 2)) •
        ∑ᶠ d₀ ∈ {d₀ : DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := SG) | d₀.1.IsUp P (Pr.T u : 𝓞 X.E) d.1},
          term W Ch sel mu cst A u i j d₀ fr d' fr' Ξ₀ y

def valAt (w : HeightOneSpectrum (𝓞 X.K)) {n : ℕ} (lam : X.Tau → DomWeight n) (L : Submodule (𝓞 X.E) (Sp X.E n)) :
    Submodule (𝓞 X.K) (VV X.K lam) := localization₂ w.asIdeal (delAtr X.emb lam L)

def BarTerm (w : HeightOneSpectrum (𝓞 X.K)) : Prop :=
  ∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := SG)) (fr : Frs X.E (R.N i) (rowSG Pr sel mu))
    (d' : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := SG')) (fr' : Frs X.E (R.N j) (rowSG Pr sel mu)) (Ξ₀ : HomE X.E (R.N i) (R.N j) → X.K),
    Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation X.K (Ξ₀ x) ≤ 1) →
    ∀ y ∈ valAt w (W.lamTrue u i) d.1.Lsh, ∃ y' ∈ valAt w (W.lamTrue u j) d'.1.Lsh,
      term W Ch sel mu cst A u i j d fr d' fr' Ξ₀ y = ((Pr.T u : X.K) ^ (X.f * ((R.t + 1) / 2))) • y'

def PTerm (w : HeightOneSpectrum (𝓞 X.K)) : Prop :=
  ∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := SG)) (fr : Frs X.E (R.N i) (rowSG Pr sel mu))
    (d' : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := SG')) (fr' : Frs X.E (R.N j) (rowSG Pr sel mu)) (Ξ₀ : HomE X.E (R.N i) (R.N j) → X.K),
    Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation X.K (Ξ₀ x) ≤ 1) →
    ∀ y ∈ valAt w (W.lamTrue u i) d.1.Lsh,
      ((Pr.T u : X.K) ^ (((X.f * R.N i : ℕ) : ℤ) - ∑ τ, (W.lamTrue u j τ).detShift)) •
        term W Ch sel mu cst A u i j d fr d' fr' Ξ₀ y ∈ valAt w (W.lamTrue u j) d'.1.L

def StdOnly {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := SG))
    (d' : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := SG')) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.StdAtT d.1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.StdAtT d'.1

def AlcoveAt : Prop :=
  ∀ τ (a b : Fin (R.N j)), 2 * ((W.lamTrue u j τ).w a - (W.lamTrue u j τ).w b + (R.N j : ℤ)) < (Pr.T u : ℤ)

structure Hyp (Z : Dat) {H : D7} (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ)
    (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S)
    (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) : Prop where
  ok : Z.Ok
  ana : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.AnaOk Z s cc δ χ cD
  chiK : GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.ChiInK s χ
  isSel : IsSel Z.X sel
  host : hostS H.host.q H.host.d (Z.Pr.g 0) (Z.Pr.g 1) (Set.range Z.Pr.T) ⊆ S
  small : ∀ l ∈ H.host.small, l ∈ S
  cop : ∀ P ∈ Sall sel mu u, Nat.Coprime (Ideal.absNorm cc) (Ideal.absNorm P.asIdeal)
  cst_ok : cst.Ok
  tied : ∃ (m0 : Fin Z.R.m → Formalism.L2.Host.HChar Z.X.E) (eta : Formalism.L2.Host.HChar Z.X.E),
    Z.Ch.Tied Z.sig0 (fun j τ => (Z.W.row τ).e j) m0 eta ∧ MuqTieG (Pr := Z.Pr) (R := Z.R) sel mu cst Z.sig0 m0

section Position

variable {Pr : Primes X} {u : Pr.Word} {SG : Finset (HeightOneSpectrum (𝓞 X.E))} {n : ℕ}

theorem moveHyp_of_notMem (hPr : Pr.Ok) (h : ∀ w ∈ SG, (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) (P : Pr.vT u) :
    MoveHyp (Pr.vT u) SG P := by
  refine ⟨(moveHyp_of_ok hPr u P).ne, (moveHyp_of_ok hPr u P).st, fun w => ⟨fun e => ?_, fun e => ?_⟩⟩
  · apply h w.1 w.2
    rw [e]
    exact T_mem hPr u P
  · apply h w.1 w.2
    rw [e, mem_conjP, map_natCast]
    exact T_mem hPr u P

theorem above_finite_nonempty (hX : X.Ok) (hPr : Pr.Ok) {P : Pr.vT u} (hP : MoveHyp (Pr.vT u) SG P)
    (d' : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := SG)) :
    {d₁ : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := SG) | d'.1.IsUp P (Pr.T u : 𝓞 X.E) d₁.1}.Finite ∧
      {d₁ : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := SG) | d'.1.IsUp P (Pr.T u : 𝓞 X.E) d₁.1}.Nonempty :=
  ⟨d'.upSet_finite P _, d'.upSet_nonempty P hP (T_unif hX hPr u P).1 (T_unif hX hPr u P).2⟩

theorem below_eq_dnSet (hX : X.Ok) (hPr : Pr.Ok) {P : Pr.vT u} (hP : MoveHyp (Pr.vT u) SG P)
    (d : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := SG)) :
    {d₀ : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := SG) | d₀.1.IsUp P (Pr.T u : 𝓞 X.E) d.1} = d.dnSet P (Pr.T u : 𝓞 X.E) :=
  Set.ext fun d₀ => DecoSet.mem_upSet_iff_mem_dnSet hP (T_unif hX hPr u P).1 (T_unif hX hPr u P).2 d₀ d

theorem below_finite_nonempty (hX : X.Ok) (hPr : Pr.Ok) {P : Pr.vT u} (hP : MoveHyp (Pr.vT u) SG P)
    (d : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := SG)) :
    {d₀ : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := SG) | d₀.1.IsUp P (Pr.T u : 𝓞 X.E) d.1}.Finite ∧
      {d₀ : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := SG) | d₀.1.IsUp P (Pr.T u : 𝓞 X.E) d.1}.Nonempty := by
  rw [below_eq_dnSet hX hPr hP]
  exact ⟨d.dnSet_finite P hP.ne _, d.dnSet_nonempty P hP (T_unif hX hPr u P).1 (T_unif hX hPr u P).2⟩

end Position


variable {sel u} in
theorem T_notMem_rowSG (hPr : Pr.Ok) (hsel : IsSel X sel) (hT : Pr.T u ∈ S) :
    ∀ w ∈ rowSG Pr sel mu, (Pr.T u : 𝓞 X.E) ∉ w.asIdeal := by
  classical
  intro w hw hm
  rcases Finset.mem_union.1 hw with h | h
  · exact T_notMem_vGs hPr u ⟨w, h⟩ hm
  · unfold QE at h
    split_ifs at h with hf
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := hf.mem_toFinset.1 hv
      have hg : GoodPl X.E S v := by
        by_contra hg
        exact hv' (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 mu.2.2 v) hg)
      have h1 : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal := by
        rw [← hsel v, Ideal.under_def, Ideal.mem_comap, map_natCast]
        exact hm
      apply hg.2.2
      have h2 : ringChar (𝓞 X.F ⧸ v.asIdeal) = Pr.T u := by
        have := v.isPrime
        have h3 : ((Pr.T u : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
          rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
          exact h1
        exact ((Nat.dvd_prime (hPr.T_prime u)).1 (ringChar.dvd h3)).resolve_left CharP.ringChar_ne_one
      show ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
      rw [h2]
      exact hT
    · simp at h


namespace Hyp

variable {Z : Dat} {H : D7} {s : Seam H Z.X} {cc : Ideal (𝓞 H.host.K)} {δ : ℂ} {χ : TaylorLogMetric.IdE H → ℂ} {cD : H.what₂.Tau → ℂ}
  {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} {S : Set ℕ} {mu : Tup Z.X.F Z.X.E Z.X.K S}
  {cst : LocCst Z.X (rowSG Z.Pr sel mu)} {u : Z.Pr.Word}

theorem T_mem (h : Hyp Z s cc δ χ cD sel S mu cst u) : Z.Pr.T u ∈ S := h.host (Or.inr ⟨u, rfl⟩)

theorem g_mem (h : Hyp Z s cc δ χ cD sel S mu cst u) (k : Fin 2) : Z.Pr.g k ∈ S := by
  apply h.host
  fin_cases k <;> simp [hostS]

end Hyp


end GlobalTheory.KerT
end
end

section

noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.GlobalTheoryTheory NumberField

variable {R : Ranks}

def hPH (H : Host R) (p : ℕ) : R.A :=
  R.iotaInv (Classical.epsilon (fun g => g ∈
    {g : R.GG | ∃ (P : Ideal (𝓞 H.E)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)}))
      (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ∧ H.galE σ = g})).2

def dlogH (H : Host R) : ℝ :=
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI : NeZero H.d := ⟨H.hyp.2.1.ne_zero⟩
  (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ))) 1 /
    DirichletCharacter.LFunction ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)) 1).re

abbrev baseOf (s : Scale) (cD ch : ℝ) (H : Host R) : Arith.Base :=
  { R := R, sc := s, q := H.q, d := H.d, cls := H.cls, TT := H.TT, Sc := (R.k : ℝ) * (4 * (Delv s cD : ℝ)),
    eta := (R.m : ℝ) * (h0v s ch : ℝ) }


open Classical in
def BadOK (s : Scale) (Cb : ℝ) (H : Host R) : Prop :=
  let B := baseOf s 0 0 H
  let PR := (Finset.range ⌈s.X'⌉₊).filter (fun p =>
    p.Prime ∧ B.IsResidueClassZero p ∧ s.x ^ (s.eps / 4) ≤ (addOrderOf (hPH H p) : ℝ))
  ∑ p ∈ PR, Real.log p / p *
      ((H.TT.filter (fun t => ¬ Arith.Loc.Good B (hPH H p) (Arith.bsH (Arith.Loc.stepP B (hPH H p) p) t))).card : ℝ) ≤
    4 * (Cb * s.x ^ (-2 : ℝ)) * s.delta1 * R.n * ∑ p ∈ PR, Real.log p / p

def IsCharH (H : Host R) {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop :=
  χ.IsPrimitive ∧ ∃ ψ : R.GG →* ℂˣ, ∀ (a : ℕ) (h : a.Coprime H.condN),
    χ (a : ZMod N) = ((ψ (H.art (ZMod.unitOfCoprime a h)) : ℂˣ) : ℂ)

theorem isCharH_iff_isCharED (D : D7) {N : ℕ} (χ : DirichletCharacter ℂ N) : IsCharH D.host χ ↔ GlobalTheoryTheory.IsCharED D χ := Iff.rfl

theorem isCharH_iff (H : Host R) {N : ℕ} (χ : DirichletCharacter ℂ N) : IsCharH H χ ↔ H.IsCharE χ := by
  have key : ∀ (ψ : R.GG →* ℂˣ) (a : ℕ) (h : a.Coprime H.condN),
      H.dirAt ψ a = ((ψ (H.art (ZMod.unitOfCoprime a h)) : ℂˣ) : ℂ) := fun ψ a h => by
    rw [← H.dir_unit ψ (ZMod.unitOfCoprime a h), ZMod.coe_unitOfCoprime]
    rfl
  constructor
  · rintro ⟨h1, ψ, h2⟩
    exact ⟨ψ, h1, fun a ha => (h2 a ha).trans (key ψ a ha).symm⟩
  · rintro ⟨ψ, h1, h2⟩
    exact ⟨h1, ψ, fun a ha => (h2 a ha).trans (key ψ a ha)⟩

def ThinOK (s : Scale) (c : ℝ) (H : Host R) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharH H χ →
    ∀ y : ℝ, Real.exp (s.x ^ (s.eps / 3)) / 3 ≤ y → ‖GlobalTheoryTheory.gChi χ y‖ ≤ y * Real.exp (-(c * s.x ^ (s.eps / 8)))

theorem thinScales_iff_hostBound (s : Scale) (c : ℝ) (H : Host R) : ThinOK s c H ↔ H.ChebyshevCharacterBound s.x s.eps c :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun χ => imp_congr (isCharH_iff H χ) Iff.rfl

def BoxH (H : Host R) (Y eps : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharH H χ → GlobalTheoryTheory.IsRealChar χ →
    (H.d ∣ N → GlobalTheoryTheory.GoodFor (8 * ((ordCompl[2] H.QS : ℕ) : ℝ) * GlobalTheoryTheory.X1 Y eps * GlobalTheoryTheory.X2 Y eps) χ) ∧
    (H.q ∣ N → ¬ H.d ∣ N → GlobalTheoryTheory.GoodFor (8 * ((ordCompl[2] H.QS : ℕ) : ℝ) * GlobalTheoryTheory.X1 Y eps) χ)

def BoxW (s : Scale) (H : Host R) : Prop :=
  ∃ Y : ℝ, PairWin s Y ∧ PairRow Y s.eps H ∧ Boxq Y s.eps H.q H.d ∧ BoxH H Y s.eps

theorem BoxW.what₂ {s : Scale} {H : Host R} (h : BoxW s H) : ∃ Y : ℝ, PairWin s Y ∧ PairRow Y s.eps H :=
  let ⟨Y, h1, h2, _⟩ := h
  ⟨Y, h1, h2⟩

theorem BoxW.boxesW {s : Scale} {D : D7} (h : BoxW s D.host) : BoxesW D s :=
  let ⟨Y, h1, _, h3, h4⟩ := h
  ⟨Y, h1, h3, h4⟩

theorem BoxW.qdRowsW {s : Scale} {D : D7} (h : BoxW s D.host) : QDRowsW D s := h.what₂

def HostGood (s : Scale) (C8 C5 c6 Cb : ℝ) (H : Host R) (q0 : ℕ) : Prop :=
  HostVal s C8 H ∧ HostArith H ∧ H.secondSet_card_lower_bound ∧ 4 * H.Lw * H.T2.card ≤ R.n0 ∧
  QDq s.x s.eps C5 H.q H.d ∧ BoxW s H ∧ |dlogH H| ≤ s.x ^ s.eps ∧ ThinOK s c6 H ∧ BadOK s Cb H ∧
  Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧
  (∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E) ∧
    (π - 1) ∈ Ideal.span {((H.QS * H.q * H.d : ℕ) : 𝓞 H.E)}) ∧
  (H.pde % Nat.lcm 15 (H.QS * H.q * H.d) = 1 ∧ H.pde' % Nat.lcm 15 (H.QS * H.q * H.d) = 1) ∧
  (q0.Prime ∧ q0 % (H.QS * H.q * H.d) = 1 ∧ (q0 : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C8 ∧ q0 ≠ H.pde ∧ q0 ≠ H.pde') ∧
  H.levelPrimes = {H.g 0, H.g 1, H.pde, H.pde', q0}

abbrev HostReq : Type 1 := ℝ → Scale → ∀ R : Ranks, Host R → ℕ → Prop

def HostExW (la : ℝ) (P : HostReq) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ CT2 C8 C5 c6 Cb x0 : ℝ, 1 ≤ C8 ∧ 0 < C5 ∧ 0 < c6 ∧ 0 < Cb ∧
    ∃ S : Scales la, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → S.Mem s →
      ∃ (R : Ranks) (H : Host R) (q0 : ℕ), RankVal s R ∧ H.CT2 = CT2 ∧ HostGood s C8 C5 c6 Cb H q0 ∧ P C5 s R H q0

def HostExP (P : HostReq) : Prop := ∃ la : ℝ, 1 < la ∧ HostExW la P

def WinOK (s : Scale) (K : G.Consts) (H : Host R) (a b : R.A → ℤ) : Prop :=
  ∀ t ∈ H.TT, (s.a ≤ (a t : ℝ) ∧ (a t : ℝ) ≤ s.a + s.a / ((R.k : ℝ) * s.x ^ (Scale.A / 2))) ∧
    s.b' ≤ (b t : ℝ) ∧ (b t : ℝ) ≤ s.b' + 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s * s.b' / (R.k : ℝ)


open Classical in
def WOK (s : Scale) (cD ch : ℝ) (K : G.Consts) (H : Host R) (a b : R.A → ℤ) : Prop :=
  let B := baseOf s cD ch H
  ∑ p ∈ (Finset.range ⌈s.X'⌉₊).filter (fun p => Arith.Loc.Cand B K (hPH H p) p), Real.log p / p *
      (2 * (if s.x ^ (-s.eps) < Arith.Loc.Sig B (Arith.ins B K 1) K a b (hPH H p) p then (1 : ℝ) else 0) +
        4 * Arith.Loc.Sig B (Arith.ins B K 1) K a b (hPH H p) p) ≤ s.x ^ (-9 : ℝ)

def Pt.From {C : FC} (p : Pt C) (H : Host R) (a b : R.A → ℤ) {M : ℕ} (c : Fin M → Fin (R.k - 2) → Bool)
    (u0 : ℕ) : Prop :=
  p.D.R = R ∧ p.D.host.TT.image Formalism.HC.Frame.A.val = H.TT.image Formalism.HC.Frame.A.val ∧ p.D.host.T2 = H.T2 ∧ p.D.host.q = H.q ∧ p.D.host.d = H.d ∧
  p.D.host.g = H.g ∧ p.D.host.pde = H.pde ∧ p.D.host.pde' = H.pde' ∧ H.levelPrimes ⊆ p.D.host.levelPrimes ∧
  p.D.host.u0.val = u0 ∧ (∀ l, (G.hP p.D l).val = (hPH H l).val) ∧
  (∀ (t : p.D.host.TT) (t' : R.A), (t : p.D.R.A).val = t'.val → p.L.aT t = a t' ∧ p.L.bT t = b t') ∧
  (∃ eW : p.D.what₂.Word ≃ Fin M, ∀ u l, wordBits p.D u l = if h : l < R.k - 2 then c (eW u) ⟨l, h⟩ else false) ∧
  HEq p.D.host.toHostAx H.toHostAx

section From

variable {C : FC} {p : Pt C} {H : Host R} {a b : R.A → ℤ} {M : ℕ} {c : Fin M → Fin (R.k - 2) → Bool} {u0 : ℕ}

theorem Pt.From.words (h : p.From H a b c u0) :
    ∃ eW : p.D.what₂.Word ≃ Fin M, ∀ u l, wordBits p.D u l = if h : l < R.k - 2 then c (eW u) ⟨l, h⟩ else false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Pt.From.field (h : p.From H a b c u0) : HEq p.D.host.toHostAx H.toHostAx := h.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem Pt.From.congr_field (h : p.From H a b c u0) {α : Sort*} (f : ∀ φ : Formalism.HC.Frame, Formalism.HC.HostAx φ → α) :
    f p.D.R.toFrame p.D.host.toHostAx = f R.toFrame H.toHostAx := by
  have h1 := h.1
  have h2 := h.field
  subst h1
  rw [eq_of_heq h2]

theorem Pt.From.QS_eq (h : p.From H a b c u0) : p.D.host.QS = H.QS := h.congr_field fun _ X => X.QS

theorem Pt.From.art_eq (h : p.From H a b c u0) : artNum p.D.host.toHostRaw = artNum H.toHostRaw :=
  h.congr_field fun _ X => artNum X.toHostRaw

theorem Pt.From.rd_eq (h : p.From H a b c u0) : p.D.host.rdE = H.rdE := h.congr_field fun _ X => X.rd

theorem Pt.From.cls_eq (h : p.From H a b c u0) : p.D.host.cls = H.cls :=
  h.congr_field fun _ X => primeClass X.toHostRaw

theorem Pt.From.isCharED_iff (h : p.From H a b c u0) {N : ℕ} (χ : DirichletCharacter ℂ N) :
    GlobalTheoryTheory.IsCharED p.D χ ↔ IsCharH H χ := by
  rw [← isCharH_iff_isCharED, isCharH_iff, isCharH_iff]
  exact iff_of_eq (h.congr_field fun _ X => X.IsCharE χ)

theorem Pt.From.boxE (h : p.From H a b c u0) {Y eps : ℝ} (hB : BoxH H Y eps) : GlobalTheoryTheory.BoxE p.D Y eps := by
  intro N _ χ hχ hr
  have := hB N χ ((h.isCharED_iff χ).1 hχ) hr
  unfold GlobalTheoryTheory.oddQS
  rw [h.QS_eq, h.2.2.2.1, h.2.2.2.2.1]
  exact this

theorem Pt.From.pairRow (h : p.From H a b c u0) {Y eps : ℝ} (hr : PairRow Y eps H) : PairRow Y eps p.D.host := by
  unfold PairRow
  rw [h.QS_eq, h.2.2.2.1, h.2.2.2.2.1]
  exact hr

theorem Pt.From.boxW (h : p.From H a b c u0) {s : Scale} (hB : BoxW s H) : BoxW s p.D.host := by
  obtain ⟨Y, h1, h2, h3, h4⟩ := hB
  refine ⟨Y, h1, h.pairRow h2, ?_, h.boxE h4⟩
  rw [h.2.2.2.1, h.2.2.2.2.1]
  exact h3

theorem Pt.From.boxesW (h : p.From H a b c u0) {s : Scale} (hB : BoxW s H) : BoxesW p.D s := (h.boxW hB).boxesW

theorem Pt.From.qdRowsW (h : p.From H a b c u0) {s : Scale} (hB : BoxW s H) : QDRowsW p.D s := (h.boxW hB).qdRowsW

end From

def CanonInst {D : D7} {L : SizeData₂ D} (X : G.Inst D L) : Prop :=
  (∀ h t, X.bs h t = Arith.bsH h t) ∧
  ∀ j, j ∉ SizeData₂.lifts D → ∀ t : G.HH D,
    X.off j (false, t) = if t ∈ D.host.TT then L.sc.b' / L.sc.x else L.sc.w'' D.R.n

def withDuty (Q : PtProp) : PtProp := fun D L gatT Gx Gy K X cX ex =>
  Q D L gatT Gx Gy K X cX ex ∧ Formalism.MainNotions.AuxBlock8.WReq Gx K (G.aL L) (G.bL L) ∧
    BoxesW D L.sc ∧ QDRowsW D L.sc ∧
    ∃ q0 ∈ D.host.levelPrimes, q0.Prime ∧ q0 % (D.host.QS * D.host.q * D.host.d) = 1 ∧ Real.log q0 ≤ L.sc.L ∧ (q0 : ℝ) < L.sc.X' ∧
      q0 ≠ D.host.pde ∧ q0 ≠ D.host.pde' ∧ ∀ i, q0 ≠ D.host.g i

end GlobalTheory.EX

end
end
