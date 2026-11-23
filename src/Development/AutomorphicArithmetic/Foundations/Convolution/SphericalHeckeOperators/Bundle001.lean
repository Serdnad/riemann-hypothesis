module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Fin.Tuple.Sort
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

theorem UpperTheory.ConvolutionTheory.H.symAlg :
    ∀ (n l : ℕ) (y : LaurentRing n),
      symSum y ∈ symmetricLaurent (n := n) ∧ bc l (symSum y) = symSum (bc l y) ∧
      (∀ p ∈ symmetricLaurent (n := n), symSum (y * p) = symSum y * p) ∧
      (y ∈ symmetricLaurent (n := n) → bc l y ∈ symmetricLaurent (n := n)) ∧
      ∀ z : Fin n → ℂˣ, evalAt z (bc l y) = evalAt (z ^ l) y := by
  intro n l y
  have hb : ∀ (a : Fin n → ℤ) (c : ℂ), bc l (AddMonoidAlgebra.single a c : LaurentRing n) = AddMonoidAlgebra.single ((l : ℤ) • a) c := by
    intro a c
    simp [bc, AddMonoidAlgebra.mapDomainAlgHom, AddMonoidAlgebra.mapDomain_single]
  have hc : ∀ (σ : Equiv.Perm (Fin n)) (y : LaurentRing n), bc l (permAct σ y) = permAct σ (bc l y) := fun σ y => by
    have : (bc l).comp (permAct σ) = (permAct σ).comp (bc (n := n) l) :=
      AddMonoidAlgebra.algHom_ext (fun a => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, permAct_single, hb, hb, permAct_single]; rfl) (Subsingleton.elim _ _)
    exact AlgHom.congr_fun this y
  refine ⟨fun τ => ?_, ?_, fun p hp => ?_, fun hy σ => ?_, fun z => ?_⟩

  · rw [symSum, map_sum]
    simp only [permAct_permAct]
    exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => rfl

  · rw [symSum, symSum, map_sum]
    exact Finset.sum_congr rfl fun σ _ => hc σ y
  · rw [symSum, symSum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => by rw [map_mul, hp σ]
  · rw [← hc, hy σ]
  · have : (evalAt z).comp (bc l) = evalAt (z ^ l) :=
      AddMonoidAlgebra.algHom_ext (fun a => by
        rw [AlgHom.comp_apply, hb, evalAt_single, evalAt_single, monomialChar_apply, monomialChar_apply]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, zpow_mul, zpow_natCast, Pi.pow_apply]) (Subsingleton.elim _ _)
    exact AlgHom.congr_fun this y
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

namespace UpperTheory.ConvolutionTheory.H.NonVanishingCharacter

variable {n : ℕ}

private def phi : (Fin n → ℕ) →+ (Fin n → ℤ) where
  toFun b i := ∑ k, if i ≤ k then (b k : ℤ) else 0
  map_zero' := by
    funext i
    simp
  map_add' b c := by
    funext i
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp

private lemma phi_apply (b : Fin n → ℕ) (i : Fin n) :
    phi b i = ∑ k, if i ≤ k then (b k : ℤ) else 0 := rfl

private lemma phi_nonneg (b : Fin n → ℕ) (i : Fin n) : 0 ≤ phi b i := by
  rw [phi_apply]
  refine Finset.sum_nonneg fun k _ => ?_
  split_ifs <;> simp

private lemma phi_anti (b : Fin n → ℕ) {i j : Fin n} (hij : i ≤ j) : phi b j ≤ phi b i := by
  rw [phi_apply, phi_apply]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases h1 : j ≤ k
  · rw [if_pos h1, if_pos (hij.trans h1)]
  · rw [if_neg h1]
    split_ifs <;> simp

private def chi (w : Fin n → ℂˣ) : Multiplicative (Fin n → ℕ) →* ℂ where
  toFun b := monomialChar (phi (Multiplicative.toAdd b)) w
  map_one' := by simp
  map_mul' b c := by simp [map_add (f := _), monomialChar_add]

private lemma chi_apply (w : Fin n → ℂˣ) (b : Fin n → ℕ) :
    chi w (Multiplicative.ofAdd b) = monomialChar (phi b) w := rfl

private lemma chi_single (w : Fin n → ℂˣ) (k : Fin n) :
    chi w (Multiplicative.ofAdd (Pi.single k 1)) = ∏ i ∈ Finset.Iic k, (w i : ℂ) := by
  have hphi : ∀ i, phi (Pi.single k 1 : Fin n → ℕ) i = if i ≤ k then 1 else 0 := by
    intro i
    rw [phi_apply, Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      simp [Pi.single_eq_of_ne hl]
    · simp
  rw [chi_apply, monomialChar_apply]
  have hI : Finset.Iic k = Finset.univ.filter (· ≤ k) := by
    ext
    simp
  rw [hI, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hphi]
  split_ifs <;> simp

private lemma chi_injective {w w' : Fin n → ℂˣ} (h : chi w = chi w') : w = w' := by
  have hp : ∀ k, ∏ i ∈ Finset.Iic k, (w i : ℂ) = ∏ i ∈ Finset.Iic k, (w' i : ℂ) := fun k => by
    rw [← chi_single, ← chi_single, h]
  funext k
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    have hI : Finset.Iic k = insert k (Finset.Iio k) := by
      ext
      simp [le_iff_eq_or_lt]
    have h1 := hp k
    rw [hI, Finset.prod_insert (by simp), Finset.prod_insert (by simp)] at h1
    have e : ∏ i ∈ Finset.Iio k, (w i : ℂ) = ∏ i ∈ Finset.Iio k, (w' i : ℂ) :=
      Finset.prod_congr rfl fun i hi => by rw [ih i (Finset.mem_Iio.1 hi)]
    rw [e] at h1
    have ne : ∏ i ∈ Finset.Iio k, (w' i : ℂ) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => (w' i).ne_zero
    exact Units.ext (mul_right_cancel₀ ne h1)

private lemma evalAt_varL (w : Fin n → ℂˣ) (i : Fin n) : evalAt w (varL i) = (w i : ℂ) := by
  rw [evalAt_single, one_mul, monomialChar_apply, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private lemma evalAt_dPol (w : Fin n → ℂˣ) (t : ℂ) :
    evalAt w (dPol n t) = ∏ p ∈ pairs n, ((w p.1 : ℂ) - t * (w p.2 : ℂ)) := by
  rw [dPol, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_sub, map_smul, evalAt_varL, evalAt_varL, smul_eq_mul]

private lemma evalAt_dPol_ne {t : ℂ} (ht : ‖t‖ < 1) (w : Fin n → ℂˣ)
    (hw : ∀ i j, i ≤ j → ‖(w j : ℂ)‖ ≤ ‖(w i : ℂ)‖) : evalAt w (dPol n t) ≠ 0 := by
  rw [evalAt_dPol, Finset.prod_ne_zero_iff]
  intro p hp h0
  have hij : p.1 < p.2 := (Finset.mem_filter.1 hp).2
  have e : (w p.1 : ℂ) = t * (w p.2 : ℂ) := sub_eq_zero.1 h0
  have h1 := hw _ _ hij.le
  have hpos : 0 < ‖(w p.2 : ℂ)‖ := norm_pos_iff.2 (w p.2).ne_zero
  rw [e, norm_mul] at h1
  nlinarith

private lemma evalAt_term (z : Fin n → ℂˣ) (a : Fin n → ℤ) (t : ℂ) :
    evalAt z (symSum (monomial a * dPol n t)) =
      ∑ σ : Equiv.Perm (Fin n), monomialChar a (z ∘ σ) * evalAt (z ∘ σ) (dPol n t) := by

  rw [symSum, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [evalAt_permAct, map_mul, evalAt_single, one_mul]

end UpperTheory.ConvolutionTheory.H.NonVanishingCharacter

open UpperTheory.ConvolutionTheory.H.NonVanishingCharacter in
theorem UpperTheory.ConvolutionTheory.H.nonVan :
    ∀ (n : ℕ) (t : ℂ), ‖t‖ < 1 → ∀ (z : Fin n → ℂˣ) (m : ℕ),
      ∃ a : Fin n → ℤ, Gap m a ∧ (∀ i, 0 ≤ a i) ∧ evalAt z (symSum (monomial a * dPol n t)) ≠ 0 := by
  classical
  intro n t ht z m
  by_contra hcon
  push_neg at hcon
  let s : Fin n → ℤ := fun i => (m : ℤ) * ((n : ℤ) - ((i : ℕ) : ℤ))
  have hs0 : ∀ i, 0 ≤ s i := fun i => by
    have : ((i : ℕ) : ℤ) ≤ n := by exact_mod_cast i.2.le
    exact mul_nonneg (by positivity) (by linarith)
  have hsgap : ∀ i j : Fin n, i < j → s j + m ≤ s i := fun i j hij => by
    have h1 : ((i : ℕ) : ℤ) + 1 ≤ ((j : ℕ) : ℤ) := by exact_mod_cast hij
    have hm : (0 : ℤ) ≤ m := by positivity
    simp only [s]
    nlinarith
  let W : Equiv.Perm (Fin n) → ℂ := fun σ => monomialChar s (z ∘ σ) * evalAt (z ∘ σ) (dPol n t)
  let Ψ : Equiv.Perm (Fin n) → (Multiplicative (Fin n → ℕ) →* ℂ) := fun σ => chi (z ∘ σ)
  have hsum : ∀ b, ∑ σ, W σ * Ψ σ b = 0 := by
    intro b
    have h0 := hcon (s + phi (Multiplicative.toAdd b))
      (fun i j hij => by
        have := hsgap i j hij
        have := phi_anti (Multiplicative.toAdd b) hij.le
        simp only [Pi.add_apply]
        linarith)
      (fun i => add_nonneg (hs0 i) (phi_nonneg _ i))
    rw [evalAt_term] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [monomialChar_add]
    simp only [W, Ψ]
    change _ * monomialChar (phi (Multiplicative.toAdd b)) (z ∘ σ) = _
    ring
  have hli := linearIndependent_monoidHom (Multiplicative (Fin n → ℕ)) ℂ
  rw [linearIndependent_iff'] at hli
  let g : (Multiplicative (Fin n → ℕ) →* ℂ) → ℂ := fun χ => ∑ σ with Ψ σ = χ, W σ
  have hg : ∑ χ ∈ Finset.univ.image Ψ, g χ • (χ : Multiplicative (Fin n → ℕ) → ℂ) = 0 := by
    funext b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, g, Finset.sum_mul]
    rw [← hsum b]
    rw [← Finset.sum_fiberwise_of_maps_to (g := Ψ) (t := Finset.univ.image Ψ)
      (fun σ _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))]
    exact Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun σ hσ => by
      rw [(Finset.mem_filter.1 hσ).2]
  let σ₀ : Equiv.Perm (Fin n) := Tuple.sort (fun i => -‖(z i : ℂ)‖)
  have hw : ∀ i j, i ≤ j → ‖((z ∘ σ₀) j : ℂ)‖ ≤ ‖((z ∘ σ₀) i : ℂ)‖ := fun i j hij =>
    neg_le_neg_iff.1 (Tuple.monotone_sort (fun i => -‖(z i : ℂ)‖) hij)
  have hW : W σ₀ ≠ 0 := by
    refine mul_ne_zero ?_ (evalAt_dPol_ne ht _ hw)
    rw [monomialChar_apply, Finset.prod_ne_zero_iff]
    exact fun i _ => Units.ne_zero _
  have hgz : g (Ψ σ₀) = 0 := hli _ g hg (Ψ σ₀) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hfib : g (Ψ σ₀) = ((Finset.univ.filter fun σ => Ψ σ = Ψ σ₀).card : ℂ) * W σ₀ := by
    simp only [g]
    rw [Finset.sum_congr rfl (g := fun _ => W σ₀), Finset.sum_const, nsmul_eq_mul]
    intro σ hσ
    have he : z ∘ σ = z ∘ σ₀ := chi_injective (Finset.mem_filter.1 hσ).2
    simp only [W, he]
  have hc : (Finset.univ.filter fun σ => Ψ σ = Ψ σ₀).card ≠ 0 :=
    Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ σ₀, rfl⟩)
  rw [hfib] at hgz
  exact (mul_ne_zero (Nat.cast_ne_zero.2 hc) hW) hgz
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem UpperTheory.ConvolutionTheory.H.mem_supp_mono {n : ℕ} {a c : Fin n → ℤ} {q : LaurentRing n}
    (h : c ∈ (monomial a * q).coeff.support) : -a + c ∈ q.coeff.support := by
  rw [Finsupp.mem_support_iff] at h ⊢
  have e : (monomial a * q).coeff c = 1 * q.coeff (-a + c) :=
    AddMonoidAlgebra.coeff_single_mul_apply q 1 a c
  rw [e, one_mul] at h
  exact h

private theorem UpperTheory.ConvolutionTheory.H.gap_strict {n : ℕ} (B : Finset (Fin n → ℤ)) :
    ∃ m : ℕ, ∀ a : Fin n → ℤ, Gap m a → ∀ b ∈ B, StrictAnti (a + b) := by
  classical
  set M : ℕ := ∑ b ∈ B, ∑ i, (b i).natAbs with hM
  have hb : ∀ b ∈ B, ∀ i, (b i).natAbs ≤ M := fun b hb i =>
    (Finset.single_le_sum (f := fun i => (b i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun b : Fin n → ℤ => ∑ i, (b i).natAbs)
        (fun _ _ => Nat.zero_le _) hb)
  refine ⟨2 * M + 1, fun a ha b hbB i j hij => ?_⟩
  have h1 := ha i j hij
  have h2 := hb b hbB i
  have h3 := hb b hbB j
  simp only [Pi.add_apply]
  push_cast at h1
  omega

private theorem UpperTheory.ConvolutionTheory.H.Gap.mono {n : ℕ} {m m' : ℕ} (h : m ≤ m') {a : Fin n → ℤ}
    (ha : Gap m' a) : Gap m a := fun i j hij => by
  have := ha i j hij
  have h' : (m : ℤ) ≤ m' := by exact_mod_cast h
  omega

private theorem UpperTheory.ConvolutionTheory.H.Gap.scale {n : ℕ} {m l : ℕ} (hl : 1 ≤ l) {a : Fin n → ℤ}
    (ha : Gap m a) : Gap m ((l : ℤ) • a) := fun i j hij => by
  have h := ha i j hij
  have h' : (1 : ℤ) ≤ l := by exact_mod_cast hl
  have hm : (0 : ℤ) ≤ m := by positivity
  simp only [Pi.smul_apply, smul_eq_mul]
  nlinarith

private theorem UpperTheory.ConvolutionTheory.H.bc_monomial {n : ℕ} (l : ℕ) (a : Fin n → ℤ) :
    bc l (monomial a) = monomial ((l : ℤ) • a) := by
  simp only [bc, AddMonoidAlgebra.mapDomainAlgHom_apply, monomial, AddMonoidAlgebra.mapDomain_single]
  rfl

private theorem UpperTheory.ConvolutionTheory.H.monomial_pow {n : ℕ} (l : ℕ) (a : Fin n → ℤ) :
    monomial ((l : ℤ) • a) = monomial a ^ l := by
  induction l with
  | zero => simp [monomial, AddMonoidAlgebra.one_def]
  | succ k ih =>
    rw [pow_succ, ← ih, ← monomial_add]
    congr 1
    push_cast
    rw [add_smul, one_smul]

private noncomputable def UpperTheory.ConvolutionTheory.H.cof (n l : ℕ) (t : ℂ) : LaurentRing n :=
  ∏ p ∈ pairs n, ∑ k ∈ Finset.range l, varL p.1 ^ k * (t • varL p.2) ^ (l - 1 - k)

private theorem UpperTheory.ConvolutionTheory.H.bc_dPol (n l : ℕ) (t : ℂ) :
    bc l (dPol n (t ^ l)) = dPol n t * cof n l t := by
  simp only [dPol, cof, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_sub, map_smul, mul_comm, geom_sum₂_mul, smul_pow]
  simp only [varL, bc_monomial, monomial_pow]

theorem UpperTheory.ConvolutionTheory.H.depth :
    ∀ (n l : ℕ), 1 ≤ l → ∀ (t : ℂ) (P : Finset (LaurentRing n)) (ν ν' : Fin n → ℤ), ∃ m : ℕ, ∀ a : Fin n → ℤ, Gap m a → ∀ p ∈ P,
      SDom (monomial a * dPol n (t ^ l) * p) ∧
      (∃ r, Dom r ∧ monomial a * dPol n (t ^ l) * p = monomial ν * dPol n (t ^ l) * r) ∧
      ∃ r', Dom r' ∧ bc l (monomial a * dPol n (t ^ l) * p) = monomial ν' * dPol n t * r' := by
  classical
  intro n l hl t P ν ν'
  obtain ⟨m₁, h₁⟩ := gap_strict (P.biUnion fun p => (dPol n (t ^ l) * p).coeff.support)
  obtain ⟨m₂, h₂⟩ := gap_strict (P.biUnion fun p => p.coeff.support.image (· - ν))
  obtain ⟨m₃, h₃⟩ := gap_strict
    (P.biUnion fun p => (cof n l t * bc l p).coeff.support.image (· - ν'))
  refine ⟨m₁ + m₂ + m₃, fun a ha p hp => ⟨?_, ⟨monomial (a - ν) * p, ?_, ?_⟩,
    ⟨monomial ((l : ℤ) • a - ν') * (cof n l t * bc l p), ?_, ?_⟩⟩⟩
  · intro c hc
    rw [mul_assoc] at hc
    have hb := mem_supp_mono hc
    have := h₁ a (Gap.mono (by omega) ha) (-a + c)
      (Finset.mem_biUnion.2 ⟨p, hp, hb⟩)
    simpa using this
  · intro c hc
    have hb := mem_supp_mono hc
    have := h₂ a (Gap.mono (by omega) ha) (-(a - ν) + c - ν)
      (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_image.2 ⟨_, hb, rfl⟩⟩)
    have e : a + (-(a - ν) + c - ν) = c := by abel
    rw [e] at this
    exact this.antitone
  · have e : monomial a = monomial ν * monomial (a - ν) := by
      rw [← monomial_add]; congr 1; abel
    rw [e]; ring
  · intro c hc
    have hb := mem_supp_mono hc
    have := h₃ ((l : ℤ) • a) (Gap.scale hl (Gap.mono (by omega) ha))
      (-((l : ℤ) • a - ν') + c - ν')
      (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_image.2 ⟨_, hb, rfl⟩⟩)
    have e : (l : ℤ) • a + (-((l : ℤ) • a - ν') + c - ν') = c := by abel
    rw [e] at this
    exact this.antitone
  · have e : monomial ((l : ℤ) • a) = monomial ν' * monomial ((l : ℤ) • a - ν') := by
      rw [← monomial_add]; congr 1; abel
    rw [map_mul, map_mul, bc_monomial, bc_dPol, e]; ring
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem he_single {n : ℕ} (i : Fin n) (m : ℤ) (w : Fin n → ℂˣ) : monomialChar (Pi.single i m : Fin n → ℤ) w = (w i : ℂ) ^ m := by
  rw [monomialChar_apply, Finset.prod_eq_single i] <;> simp +contextual [Pi.single_apply]

private theorem he_d {n : ℕ} (w : Fin n → ℂˣ) : evalAt w (dPol n 1) = ∏ p ∈ pairs n, ((w p.1 : ℂ) - w p.2) := by
  rw [dPol, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_sub, one_smul, evalAt_single, evalAt_single, he_single, he_single]
  simp

private theorem he_det {n : ℕ} (w : Fin n → ℂˣ) :
    evalAt w (dPol n 1) = (Matrix.projVandermonde (fun _ => (1 : ℂ)) fun i => (w i : ℂ)).det := by
  rw [he_d, Matrix.det_projVandermonde, Finset.prod_sigma', pairs]
  refine Finset.prod_nbij' (fun p => ⟨p.1, p.2⟩) (fun p => (p.1, p.2)) ?_ ?_ ?_ ?_ ?_ <;> simp

private theorem he_alt {n : ℕ} (w : Fin n → ℂˣ) : evalAt w (alternant (staircase n)) = evalAt w (dPol n 1) := by
  rw [he_det, alternant_eq_det, AlgHom.map_det]
  congr 1
  ext a b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, monomial, evalAt_single, he_single, one_mul,
    Matrix.projVandermonde_apply, one_pow]
  rw [← zpow_natCast]
  congr 1
  have := b.2
  simp only [staircase, Fin.val_rev]
  omega

private theorem he_sgn {n : ℕ} (w : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) :
    evalAt (w ∘ σ) (dPol n 1) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * evalAt w (dPol n 1) := by
  rw [he_det, he_det, ← Matrix.det_permute]
  rfl

theorem UpperTheory.ConvolutionTheory.H.hlEval :
    ∀ (n : ℕ) (t : ℂ) (z : Fin n → ℂˣ), Function.Injective z → ∀ a : Fin n → ℤ,
      (∀ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n 1) ≠ 0) ∧
      evalAt z (hlR t a) = ∑ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n t) / evalAt (z ∘ σ) (dPol n 1) * monomialChar a (z ∘ σ) := by
  intro n t z hz a
  have hne : ∀ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n 1) ≠ 0 := fun σ => by
    rw [he_d]
    refine Finset.prod_ne_zero_iff.2 fun p hp => sub_ne_zero.2 fun h => ?_
    have h1 : p.1 < p.2 := by simpa [pairs] using hp
    exact h1.ne (σ.injective (hz (Units.ext h)))
  refine ⟨hne, ?_⟩
  have h1 := congrArg (evalAt z) (alternant_mul_altQuot (monomial a * hlFactor n t))

  rw [map_mul, he_alt, antisymm_apply, map_sum] at h1
  have h0 : evalAt z (dPol n 1) ≠ 0 := hne 1
  refine mul_left_cancel₀ h0 (h1.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h2 := he_sgn z σ
  have h3 := hne σ
  rw [Units.smul_def, map_zsmul, evalAt_permAct, map_mul, monomial, evalAt_single, one_mul, zsmul_eq_mul]
  have h4 : ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h5 : evalAt z (dPol n 1) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * evalAt (z ∘ σ) (dPol n 1) := by
    rw [h2, ← mul_assoc, h4, one_mul]
  rw [h5]
  change _ * (_ * evalAt (z ∘ σ) (dPol n t)) = _
  field_simp
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem vs_single {n : ℕ} (i : Fin n) (w : Fin n → ℂˣ) : monomialChar (Pi.single i 1 : Fin n → ℤ) w = w i := by
  rw [monomialChar_apply, Finset.prod_eq_single i] <;> simp +contextual [Pi.single_apply]

theorem UpperTheory.ConvolutionTheory.H.vandSum :
    ∀ (n : ℕ) (z : Fin n → ℂˣ) (σ τ : Equiv.Perm (Fin n)),
      ∑ S ∈ (pairs n).powerset, sgS S * (monomialChar (eL S) (z ∘ σ) * monomialChar (eR S) (z ∘ τ)) =
        if σ = τ then evalAt (z ∘ σ) (dPol n 1) else 0 := by
  intro n z σ τ
  have hL : ∀ (s : Finset (Fin n × Fin n)) (f : Fin n × Fin n → Fin n) (w : Fin n → ℂˣ),
      monomialChar (∑ p ∈ s, (Pi.single (f p) 1 : Fin n → ℤ)) w = ∏ p ∈ s, (w (f p) : ℂ) := by
    intro s f w
    classical
    induction s using Finset.induction_on with
    | empty => simp [monomialChar_zero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, monomialChar_add, ih, vs_single]
  have h1 : ∑ S ∈ (pairs n).powerset, sgS S * (monomialChar (eL S) (z ∘ σ) * monomialChar (eR S) (z ∘ τ)) =
      ∏ p ∈ pairs n, ((z (σ p.1) : ℂ) - z (τ p.2)) := by
    simp only [sub_eq_add_neg]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [eL, eR, hL S Prod.fst, hL _ Prod.snd, sgS, Finset.prod_neg]
    simp only [Function.comp]
    ring
  rw [h1]
  split_ifs with h
  · subst h
    rw [dPol, map_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [map_sub, one_smul, evalAt_single, evalAt_single, vs_single, vs_single]
    simp
  · by_contra hne
    apply h
    have hge : ∀ j, j ≤ (σ⁻¹ * τ) j := fun j => by
      by_contra hlt
      refine hne (Finset.prod_eq_zero (i := ((σ⁻¹ * τ) j, j)) (by simpa [pairs] using hlt) ?_)
      simp
    have hs : ∑ j : Fin n, (j : ℕ) = ∑ j : Fin n, (((σ⁻¹ * τ) j : Fin n) : ℕ) := (Equiv.sum_comp (σ⁻¹ * τ) fun j : Fin n => (j : ℕ)).symm
    have he := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) fun (j : Fin n) _ => Fin.le_def.1 (hge j)).1 hs
    have : σ⁻¹ * τ = 1 := Equiv.ext fun j => (Fin.ext (he j (Finset.mem_univ _))).symm
    exact inv_mul_eq_one.1 this
end
