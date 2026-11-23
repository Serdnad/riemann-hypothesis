module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.LocalOrderMatrix
public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.SymBridge

theorem toLoc_eq_map_toMatrix' {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
    {N : ℕ} (e : A ≃ Fin N) (x : Sp E N →ₗ[E] Sp E N) :
    toLoc ι e e x = ((LinearMap.toMatrix' x).submatrix e e).map ι := by
  ext i j
  simp only [toLoc, Matrix.map_apply, Matrix.submatrix_apply, LinearMap.toMatrix'_apply]

theorem toLoc_comp_square {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
    {N : ℕ} (e : A ≃ Fin N) (x y : Sp E N →ₗ[E] Sp E N) :
    toLoc ι e e (x ∘ₗ y) = toLoc ι e e x * toLoc ι e e y := by
  rw [toLoc_eq_map_toMatrix', toLoc_eq_map_toMatrix', toLoc_eq_map_toMatrix', LinearMap.toMatrix'_comp,
    ← Matrix.submatrix_mul_equiv _ _ _ e _, Matrix.map_mul]

theorem toLoc_id_square {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
    {N : ℕ} (e : A ≃ Fin N) :
    toLoc ι e e (LinearMap.id : Sp E N →ₗ[E] Sp E N) = 1 := by
  rw [toLoc_eq_map_toMatrix', LinearMap.toMatrix'_id, Matrix.submatrix_one_equiv,
    Matrix.map_one _ ι.map_zero ι.map_one]

end GlobalTheory.SymBridge
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.TopAgree

def zEquiv (κ l τ j : ℕ) : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ) :=
  (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv

theorem zEquiv_val {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) : (zEquiv κ l τ j a).val = zPos a := by
  rcases a with (i | i) | ⟨i, u⟩
  · simp [zEquiv, zPos]
  · simp [zEquiv, zPos]
  · simp [zEquiv, zPos]; ring

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}


open Classical in
def phiM (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ rS r t j N : ℕ)
    (M : ℕ → ℕ → E) : K :=
  if (∀ p p', p < N → p' < r + j * t → IntAt P (M p p')) ∧
      (∀ p p', r + j * t ≤ p → p < N → p' < r + j * t → IntAt P (M p p' / (q : E))) ∧
      (∀ p', p' < r → redP P (M p' p') = 1 ∧ ∀ p, p < r + j * t → p ≠ p' →
        (r ≤ p ∨ symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) → redP P (M p p') = 0) ∧
      (∀ p p', r ≤ p' → p' < r + j * t → p < r + j * t → (p' - r) / t < (p - r) / t → redP P (M p p') = 0)
  then LocE.lamGvS ψ₀ χ k₀ r t j M *
    (LocE.unitV (χ j) (Matrix.det (Matrix.of fun s s' : Fin (r + j * t) => M s.1 s'.1)))⁻¹ else 0

theorem PhiGS_eq (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    LocE.PhiGS q ψ₀ χ k₀ rS r t (j + 1) c' n' c n x =
      phiM q ψ₀ χ k₀ rS r t j (n + c) (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x) := by
  rfl

variable {k : Type} [Field k]

theorem zPos_ixSucc_inl {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) :
    zPos (ixSucc (Fin κ ⊕ Fin l) (Fin τ) j (Sum.inl a)) = zPos a := by
  rcases a with (i | i) | ⟨i, u⟩ <;> rfl

theorem zPos_ixSucc_inr {κ l τ j : ℕ} (u : Fin τ) :
    zPos (ixSucc (Fin κ ⊕ Fin l) (Fin τ) j (Sum.inr u)) = κ + l + j * τ + u := rfl

theorem zPos_lt {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) : zPos a < κ + l + j * τ := by
  rw [← zEquiv_val]; exact (zEquiv κ l τ j a).isLt

theorem det_of_places (ι : E →+* k) {X : Type} [Fintype X] [DecidableEq X] {n : ℕ} (f : X ≃ Fin n) (pos : X → ℕ)
    (off : ℕ) (h : ∀ x, pos x = off + (f x).val) (M : ℕ → ℕ → E) :
    Matrix.det (Matrix.of fun x y => ι (M (pos x) (pos y))) =
      ι (Matrix.det (Matrix.of fun s s' : Fin n => M (off + s.1) (off + s'.1))) := by
  rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self f]
  congr 1
  ext x y
  simp [h]

end GlobalTheory.SymBridge.TopAgree
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.MatchCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
open GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix

theorem isOrd_ordX (R : Ranks) (j : ℕ) : IsOrd xPos (ordX R j) := by
  rintro ((i | i) | ⟨i, l⟩)
  · rfl
  · rfl
  · rw [ordX_d]; simp only [xPos]; ring

section Concl
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Concl

section Arith
variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Arith

section Hyp
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k)

end Hyp

section Trunc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Trunc

section Ext
variable {E K K' : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Field K'] (φ : K →+* K')
  {P : HeightOneSpectrum (𝓞 E)}

end Ext

section Reparam
variable (X : Fields) (K' : Type) [Field K'] [NumberField K']

abbrev extFields : Fields where
  F := X.F
  E := X.E
  K := K'
  starK := starRingOfComm
  Tau := Empty
  emb := Empty.elim

def onePrimes (π : 𝓞 X.E) : Primes (extFields X K') where
  cond := 0
  g := 0
  piG := fun _ => X.conjO π
  Word := Empty
  T := Empty.elim
  piT := Empty.elim

variable {X K'} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (φ : X.K →+* K') (π : 𝓞 X.E)

variable {π} {P : HeightOneSpectrum (𝓞 X.E)}

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Tup X.F X.E X.K S₀)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (z : K')

variable {P} (hP : P.1 ∈ Pr.vGs) (hs : cst.sharp = true) (hq : (qOf P.1 : X.E) ≠ 0) (hP' : P.1 ∈ (onePrimes X K' π).vGs)

end Reparam

end GlobalTheory.MatchCompare
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Ker

open Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.Th1.H

noncomputable section

namespace GlobalTheory.CocIntLoc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}

theorem hv_apply (sc : ℝ) (z w : VV ι a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) := rfl

theorem hv_swap (sc : ℝ) (z w : VV ι a b) :
    HV sc w z = (starRingEnd ℂ) (HV sc z w) := by

  simp only [hv_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem embH_apply (emb : ι → E →+* ℂ) (δ : ℂ) (x : HomE E a b) (τ : ι) (i : Fin b) (j : Fin a) :
    embH emb δ x τ i j = δ * emb τ (x (Pi.single j 1) i) := rfl

theorem hv_smul (emb : ι → E →+* ℂ) (δ : ℂ) (sc : ℝ) (hs : ∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x))
    (r : E) (x y : HomE E a b) :
    HV sc (embH emb δ (r • x)) (embH emb δ y) = HV sc (embH emb δ x) (embH emb δ (star r • y)) := by
  rw [hv_apply, hv_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [embH_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hs, Complex.conj_conj]
  ring

theorem int_of_local (M : Submodule (𝓞 E) (HomE E a b)) (f : HomE E a b → HomE E a b → ℝ)
    (hadd : ∀ x x' y, f (x + x') y = f x y + f x' y) (hsm : ∀ (r : E) x y, f (r • x) y = f x (star r • y))
    (hM : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, f x y = n) (x y : HomE E a b)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), ∃ k : E, k ≠ 0 ∧ k⁻¹ • x ∈ localization₂ Q.asIdeal M ∧
      star k • y ∈ localization₂ (conjPrime₂ Q).asIdeal M) : ∃ n : ℤ, f x y = n := by
  have hzero : ∀ z, f 0 z = 0 := fun z => by
    have := hadd 0 0 z
    rw [add_zero] at this
    linarith
  let I : Ideal (𝓞 E) :=
    { carrier := {r | ∀ s : 𝓞 E, ∃ n : ℤ, f ((s * r) • x) y = n}
      zero_mem' := fun s => ⟨0, by simp [hzero]⟩
      add_mem' := fun {r r'} hr hr' s => by
        obtain ⟨n, hn⟩ := hr s
        obtain ⟨m, hm⟩ := hr' s
        exact ⟨n + m, by rw [mul_add, add_smul, hadd, hn, hm, Int.cast_add]⟩
      smul_mem' := fun c r hr s => by
        show ∃ n : ℤ, f ((s * (c * r)) • x) y = n
        rw [← mul_assoc]
        exact hr _ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 E) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩
    obtain ⟨k, hk, hx, hy⟩ := h Q
    obtain ⟨u, hu, hx⟩ := hx
    obtain ⟨v, hv, hy⟩ := hy
    have hmem : u * cO E v ∈ I := by
      intro s
      obtain ⟨n, hn⟩ := hM _ (Submodule.smul_mem _ s hx) _ hy
      refine ⟨n, ?_⟩
      rw [← hn]
      have e1 : (s * (u * cO E v)) • x = (star (algebraMap (𝓞 E) E v) * k) • (s • u • k⁻¹ • x) := by
        rw [← algebraMap_smul E s, ← algebraMap_smul E u, ← algebraMap_smul E (s * _), smul_smul, smul_smul, smul_smul,
          map_mul, map_mul, algebraMap_cO]
        congr 1
        field_simp
      rw [e1, hsm, star_mul', star_star, mul_smul, algebraMap_smul]
    rcases hP.isPrime.mem_or_mem (hle hmem) with h' | h'
    · exact hu h'
    · exact hv ((mem_conjP Q v).2 h')
  have : (1 : 𝓞 E) ∈ I := hI ▸ Submodule.mem_top
  simpa using this 1

theorem integral_of_local : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → ∀ x y : Formalism.L2.Col.HomE E a b, (∀ Q : HeightOneSpectrum (𝓞 E), ∃ k : E, k ≠ 0 ∧ k⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M ∧ star k • y ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ Q).asIdeal M) → (∃ n : ℤ, Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y) = n) ∧ ∃ n : ℤ, (Real.sqrt d * (HV sc (embH emb δ x) (embH emb δ y)).re + Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2 = n := by
  intro E _ _ _ ι _ _ a b emb δ d sc M _ hs hsd hsc x y h
  have hmemL : ∀ {z : HomE E a b}, z ∈ M → embH emb δ z ∈ laV emb δ M := fun {z} hz => ⟨z, hz, rfl⟩
  have hsmA : ∀ (r : E) (x y : HomE E a b), altE (HV sc) (embH emb δ (r • x)) (embH emb δ y) =
      altE (HV sc) (embH emb δ x) (embH emb δ (star r • y)) := by
    intro r x y; simp only [altE, hv_smul emb δ sc hs]
  have hintA : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, altE (HV sc) (embH emb δ x) (embH emb δ y) = n := by
    intro x hx y hy
    have h1 := hmemL hx
    rw [← hsd] at h1
    exact h1 _ (hmemL hy)
  refine ⟨int_of_local M (fun x y => altE (HV sc) (embH emb δ x) (embH emb δ y)) ?_ hsmA hintA x y h,
    int_of_local M (fun x y => (Real.sqrt d * (HV sc (embH emb δ x) (embH emb δ y)).re +
      altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2) ?_ ?_ ?_ x y h⟩
  · intro x x' y
    simp only [altE, map_add (f := _), LinearMap.add_apply, Complex.add_im]
  · intro x x' y
    simp only [altE, map_add (f := _), LinearMap.add_apply, Complex.add_im, Complex.add_re]
    ring
  · intro r x y
    simp only [altE, hv_smul emb δ sc hs]
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hintA x hx y hy
    have h := hsc.2 _ (hmemL hx) _ (hmemL hy)
    simp only [alV, alphaQ, Formalism.L2.Th1.H.qOf] at h
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n + m, ?_⟩
    have h2 := congrArg Complex.im hn
    have h3 : (HV sc (embH emb δ y) (embH emb δ x)).re = (HV sc (embH emb δ x) (embH emb δ y)).re := by
      rw [hv_swap]; simp
    simp only [altE] at hm
    simp only [map_add (f := _), LinearMap.add_apply, Complex.add_re, h3, altE, hm] at h2
    simp at h2
    simp only [altE, hm]
    push_cast
    apply mul_left_cancel₀ Real.pi_ne_zero
    linarith

end GlobalTheory.CocIntLoc
end
end
