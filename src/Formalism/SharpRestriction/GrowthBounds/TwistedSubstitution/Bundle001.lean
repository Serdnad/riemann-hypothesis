module

public import Formalism.SharpRestriction.GrowthBounds.Lemma5aAt
public import Formalism.SharpRestriction.GrowthBounds.SourceCleaning
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SymbolRealisableBound
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.IsMultiHom
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.DvdOfAdd

@[expose] public section

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting

section Joint

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def jIso {ι : Type*} (E : ι → GLOps n K V) (lam : ι → Fin n → ℤ) : Submodule K V :=
  ⨅ i, isoSub (E i) (lam i)

def IsJProj {ι : Type*} (E : ι → GLOps n K V) (T : Set (ι → Fin n → ℤ)) (e : Module.End K V) : Prop :=
  (∀ lam ∈ T, ∀ x ∈ jIso E lam, e x = x) ∧ ∀ mu, mu ∉ T → ∀ x ∈ jIso E mu, e x = 0

end Joint

section Letters

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r)

def segZ {J : ℕ} (j : ZMod J) : ℤ := (j.val : ℤ)

def llPos (j : ℤ) (l : ℕ) : ℤ := ((Fr.LLset j).sort (· ≤ ·)).getD l 0

def posU (nLj : ℕ) (j : ℤ) (u : ℕ) : ℤ := if u < nLj then llPos Fr j u else Fr.fr j (u - nLj)

def posTL {J : ℕ} {nL : ZMod J → ℕ} : TL J nL r → ℤ
  | ⟨j, Sum.inl l⟩ => llPos Fr (segZ j) l.val
  | ⟨j, Sum.inr m⟩ => Fr.fr (segZ j) (r - 1 - m.val)

def lowP (p : ℕ) {J : ℕ} {nL : ZMod J → ℕ} (x : TL J nL r) : ℕ :=
  p ^ Fr.dist (segZ x.1) (posTL Fr x)

def NSet {J : ℕ} (nL : ZMod J → ℕ) (j : ZMod J) (u : ℕ) : Set (TL J nL r) :=
  {x | ∃ l : Fin (nL j), x = ⟨j, Sum.inl l⟩ ∧ l.val < u} ∪
    {x | ∃ m : Fin r, x = ⟨j, Sum.inr m⟩ ∧ nL j + (r - 1 - m.val) < u}

end Letters

section Level

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

def plVar (x : TL J nL r) (a : Fin r) : TV n' (m + 1) := (posOf n' (posTL Fr x), Fin.cast hk.symm (Fin.castAdd K a))

def noVar (x : TL J nL r) (b : Fin K) : TV n' (m + 1) := (posOf n' (posTL Fr x), Fin.cast hk.symm (Fin.natAdd r b))

def plMon (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r × Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => mo (plVar Fr hk nL v.1 v.2) / lowP Fr p v.1

def noMon (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r × Fin K →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => mo (noVar Fr hk nL v.1 v.2) / lowP Fr p v.1

def InLow (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ) : Prop :=
  (∀ x (a : Fin r), mo (plVar Fr hk nL x a) % lowP Fr p x = rho (x, Fin.castAdd K a)) ∧
  ∀ x (b : Fin K), mo (noVar Fr hk nL x b) % lowP Fr p x = rho (x, Fin.natAdd r b)

def InBlock (dPl dNo : TL J nL r → ℕ) (mo : TV n' (m + 1) →₀ ℕ) : Prop :=
  (∀ x, ∑ a : Fin r, mo (plVar Fr hk nL x a) / lowP Fr p x = dPl x) ∧
  ∀ x, ∑ b : Fin K, mo (noVar Fr hk nL x b) / lowP Fr p x = dNo x

def levImg (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    MvPolynomial (TL J nL r × Fin r) (MvPolynomial (TL J nL r × Fin K) (KK O)) :=
  ∑ mo ∈ F.support.filter (fun mo => InLow Fr p hk nL rho mo ∧ InBlock Fr p hk nL dPl dNo mo),
    monomial (plMon Fr p hk nL mo) (monomial (noMon Fr p hk nL mo) (F.coeff mo))

end Level

def oneT {σ τ : Type} {Kf : Type} [Field Kf] (e : Module.End Kf (MvPolynomial τ Kf))
    (F : MvPolynomial σ (MvPolynomial τ Kf)) : MvPolynomial σ (MvPolynomial τ Kf) :=
  ∑ mo ∈ F.support, monomial mo (e (F.coeff mo))

def planeCoeff {σ τ : Type} {Kf : Type} [Field Kf] (nu : τ →₀ ℕ) (F : MvPolynomial σ (MvPolynomial τ Kf)) :
    MvPolynomial σ Kf :=
  ∑ mo ∈ F.support, monomial mo ((F.coeff mo).coeff nu)

section Comparison₂

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (mS : ℕ)
  {J : ℕ} (nL : ZMod J → ℕ) (K : ℕ) [NeZero K]

def thStar (ka : ZMod J → ℕ → Fin K → ℤ) (j : ZMod J) (u : ℕ) : ℝ :=
  let x := posU Fr (nL j) (segZ j) u
  let B := Bo p Fr deg (segZ j) x
  let s : ℝ := (sl p Fr deg Y k (segZ j) x : ℝ)
  let t1 : ℝ := if Even x then (ka j (u + 1) 0 : ℝ) + mS + s else B / 2
  let t2 : ℝ := if 1 ≤ u ∧ ¬ Even (posU Fr (nL j) (segZ j) (u - 1)) then (ka j (u - 1) 0 : ℝ) + mS + s else B / 2
  max (B / 2) (max t1 t2)

def slU (j : ZMod J) (u : ℕ) : ℝ := (sl p Fr deg Y k (segZ j) (posU Fr (nL j) (segZ j) u) : ℝ)

end Comparison₂

section Tie2

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (mS : ℕ)
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {J : ℕ} (K : ℕ) [NeZero K]

def Tied (Dt : SignedChainData p O r J) (dPl : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ) : Prop :=
  J = Fr.J ∧
  (∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) ∧
  (∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val))) ∧
  Dt.d = dPl ∧
  (∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat) ∧
  (∀ j, Dt.nch j = Dt.nL j + 1) ∧
  (∀ j (i : Fin (Dt.nch j)), Dt.chain j i = {x | x.isRight} ∪ {x | ∃ l : Fin (Dt.nL j), x = Sum.inl l ∧ l.val < i.val}) ∧
  (∀ j (i : Fin (Dt.nch j)), Dt.th j i = thStar Fr p deg Y k mS Dt.nL K ka j i.val - slU Fr p deg Y k Dt.nL j i.val / 8) ∧
  ∀ j (mm : Fin r), mm.val + 2 ≤ r →
    Dt.thL j mm = thStar Fr p deg Y k mS Dt.nL K ka j (Dt.nL j + (r - 1 - mm.val)) -
      3 / 8 * slU Fr p deg Y k Dt.nL j (Dt.nL j + (r - 1 - mm.val))

def normE [NeZero J] (Dt : SignedChainData p O r J) :
    (Σ j : ZMod J, Fin (Dt.nL j + r + 1)) → GLOps K (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) :=
  fun i => glOps (KK O) K Dt.trueLet (NSet Dt.nL i.1 i.2.val)

end Tie2

def MemAt (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
    (F : MvPolynomial (TV n' (m + 1)) (KK O)) : Prop :=
  ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ),
    Tied Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K Dt dPl ka →
    ∀ (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e →
      ∀ nu : TL J Dt.nL r × Fin K →₀ ℕ,
        Dt.XX (planeCoeff nu (oneT e (levImg Fr p hk Dt.nL rho dPl dNo F)))

end Formalism.MainNotions.TestSideWords
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting

def pairSet (O : Type) [CommRing O] (r K : ℕ) [NeZero r] [NeZero K] {n' : ℕ} [NeZero n'] (F : Frames n' r)
    (j : ℤ) (m : ℤ → ℤ) (th : ℤ → ℝ) : Set (SegRing O r K) :=
  {P | ∃ (A : MvPolynomial (ℤ × Fin r) O) (G : MvPolynomial (ℤ × Fin K) O) (M : ℤ → ℤ),
      A ∈ supported O {v : ℤ × Fin r | v.1 ∈ F.letters j} ∧
      G ∈ supported O {v : ℤ × Fin K | v.1 ∈ F.letters j ∧ ¬ F.IsW j v.1} ∧
      (∀ x ∈ F.letters j, ¬ F.IsW j x →
        (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
        (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
        geR (valS LZ {y | y < x} A) (th x)) ∧
      P = plEmb O r K A * nmEmb O r K G}

section Multi

variable (p : ℕ) {n' m r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) (F : Frames n' r)

def symG (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) :
    MvPolynomial (TV n' (m + 1)) (KK O) :=
  MvPolynomial.map (algebraMap O (KK O))
    (rename (castV hk) ((∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (x j)) * monomial l 1) * monomial ga 1)

theorem symG_update (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) (k : ℕ)
    (hk' : k ∈ Finset.range F.J) (y : SegRing O r K) :
    symG p O hk F l ga (Function.update x (k : ℤ) y) =
      MvPolynomial.map (algebraMap O (KK O))
        (rename (castV hk) (phSeg O K p F (k : ℤ) y *
          ((∏ j ∈ (Finset.range F.J).erase k, phSeg O K p F (j : ℤ) (x j)) * monomial l 1)) * monomial ga 1) := by
  unfold symG
  have he : ∏ j ∈ (Finset.range F.J).erase k, phSeg O K p F (j : ℤ) (Function.update x (k : ℤ) y j) =
      ∏ j ∈ (Finset.range F.J).erase k, phSeg O K p F (j : ℤ) (x j) :=
    Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (by exact_mod_cast Finset.ne_of_mem_erase hj)]
  rw [← Finset.mul_prod_erase _ _ hk', he, Function.update_self, mul_assoc]

theorem symG_zero (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) (k : ℕ)
    (hk' : k ∈ Finset.range F.J) : symG p O hk F l ga (Function.update x (k : ℤ) 0) = 0 := by
  rw [symG_update p O hk F l ga x k hk' 0]
  simp

theorem symG_add (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) (k : ℕ)
    (hk' : k ∈ Finset.range F.J) (a b : SegRing O r K) :
    symG p O hk F l ga (Function.update x (k : ℤ) (a + b)) =
      symG p O hk F l ga (Function.update x (k : ℤ) a) + symG p O hk F l ga (Function.update x (k : ℤ) b) := by
  rw [symG_update p O hk F l ga x k hk', symG_update p O hk F l ga x k hk',
    symG_update p O hk F l ga x k hk', map_add, add_mul, map_add, add_mul, map_add]

theorem symG_smul (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) (k : ℕ)
    (hk' : k ∈ Finset.range F.J) (c : O) (a : SegRing O r K) :
    symG p O hk F l ga (Function.update x (k : ℤ) (c • a)) =
      algebraMap O (KK O) c • symG p O hk F l ga (Function.update x (k : ℤ) a) := by
  rw [symG_update p O hk F l ga x k hk', symG_update p O hk F l ga x k hk', map_smul, smul_mul_assoc,
    map_smul, smul_mul_assoc, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
    ← MvPolynomial.smul_eq_C_mul]

theorem symG_span (Q : Submodule (KK O) (MvPolynomial (TV n' (m + 1)) (KK O))) (Sj : ℤ → Set (SegRing O r K))
    (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ)
    (h : ∀ x : ℤ → SegRing O r K, (∀ j : ℕ, j < F.J → x j ∈ Sj j) → symG p O hk F l ga x ∈ Q) :
    ∀ x : ℤ → SegRing O r K, (∀ j : ℕ, j < F.J → x j ∈ Submodule.span O (Sj j)) → symG p O hk F l ga x ∈ Q := by
  have key : ∀ k : ℕ, ∀ x : ℤ → SegRing O r K,
      (∀ j : ℕ, j < F.J → (j < k → x j ∈ Submodule.span O (Sj j)) ∧ (k ≤ j → x j ∈ Sj j)) →
        symG p O hk F l ga x ∈ Q := by
    intro k
    induction k with
    | zero =>
      intro x hx
      exact h x (fun j hj => (hx j hj).2 (Nat.zero_le j))
    | succ k ih =>
      intro x hx
      by_cases hkJ : k < F.J
      · have hk' : k ∈ Finset.range F.J := Finset.mem_range.2 hkJ
        have hspan : ∀ y ∈ Submodule.span O (Sj k),
            symG p O hk F l ga (Function.update x (k : ℤ) y) ∈ Q := by
          intro y hy
          induction hy using Submodule.span_induction with
          | mem y hyS =>
            apply ih
            intro j hj
            by_cases hjk : j = k
            · rw [hjk, Function.update_self]
              exact ⟨fun h' => absurd h' (lt_irrefl _), fun _ => hyS⟩
            · have hne : (j : ℤ) ≠ (k : ℤ) := by exact_mod_cast hjk
              rw [Function.update_of_ne hne]
              exact ⟨fun h' => (hx j hj).1 (by omega), fun h' => (hx j hj).2 (by omega)⟩
          | zero =>
            rw [symG_zero p O hk F l ga x k hk']
            exact Q.zero_mem
          | add a b _ _ ha hb =>
            rw [symG_add p O hk F l ga x k hk']
            exact Q.add_mem ha hb
          | smul c a _ ha =>
            rw [symG_smul p O hk F l ga x k hk']
            exact Q.smul_mem _ ha
        have h1 := hspan (x k) ((hx k hkJ).1 (Nat.lt_succ_self k))
        rwa [Function.update_eq_self] at h1
      · apply ih
        intro j hj
        exact ⟨fun h' => (hx j hj).1 (by omega), fun h' => absurd h' (by omega)⟩
  intro x hx
  exact key F.J x (fun j hj => ⟨fun _ => hx j hj, fun h' => absurd h' (by omega)⟩)

end Multi

def g2mg (p n' : ℕ) [NeZero n'] (r K : ℕ) (F : Frames n' r) (deg : Fin n' → ℕ) (mS : ℕ) (Y : ℝ) (j x : ℤ) : ℤ :=
  (mS : ℤ) + (⌊(deg (posOf n' (F.oldest j x)) : ℝ) / (p : ℝ) ^ F.dist j (F.oldest j x) /
    (((r + K : ℕ) : ℝ) ^ 2 * Y)⌋₊ : ℤ)

def g2th (p n' : ℕ) [NeZero n'] {r : ℕ} (F : Frames n' r) (deg : Fin n' → ℕ) (j x : ℤ) : ℝ :=
  (deg (posOf n' (F.oldest j x)) : ℝ) / (p : ℝ) ^ F.dist j (F.oldest j x) / 2

theorem symbol_spaces_le_pair_span (CLa : ℝ) (p n' : ℕ) [NeZero n'] (O : Type) [CommRing O] (r K : ℕ) [NeZero r] [NeZero K]
    (F : Frames n' r) (deg : Fin n' → ℕ) (L₁ Ns mS : ℕ) (a Y : ℝ) (j : ℤ) {x : SegRing O r K}
    (hx : x ∈ symbolSpaces CLa p n' O r K F deg L₁ Ns mS a Y j) :
    x ∈ Submodule.span O (pairSet O r K F j (g2mg p n' r K F deg mS Y j) (g2th p n' F deg j)) :=
  (Submodule.mem_inf.1 hx).1

end Formalism.MainNotions.TestSideWords
end
end
