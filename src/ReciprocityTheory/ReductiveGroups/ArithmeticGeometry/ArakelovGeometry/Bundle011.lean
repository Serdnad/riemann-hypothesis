module

public import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.MonoNormSq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.GaussSt
public import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.MonomSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ChooseLePowDivFactorial
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsHomogeneousGrL

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

theorem aeval_eq_sum_adt {D N : ℕ} {S : Type*} [CommRing S] (g : MvPolynomial (Fin (D + 1)) ℤ)
    (hg : g.IsHomogeneous N) (y : Fin (D + 1) → S) :
    aeval y g = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N,
      ((AddMonoidAlgebra.coeff g (Finsupp.equivFunOnFinite.symm a) : ℤ) : S) * ∏ i, y i ^ a i := by
  classical
  rw [aeval_def, eval₂_eq']
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ => Finsupp.equivFunOnFinite.symm a) ?_ ?_ ?_ ?_
  · intro a _ ha
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply ha
    simp [h]
  · intro a _ _ b _ _ h
    exact Finsupp.equivFunOnFinite.symm.injective h
  · intro d hd hne
    refine ⟨Finsupp.equivFunOnFinite d, ?_, ?_, ?_⟩
    · rw [Finset.Nat.mem_antidiagonalTuple]
      have h := hg (MvPolynomial.mem_support_iff.1 hd)
      rw [Finsupp.weight_apply] at h
      simpa [Finsupp.sum_fintype] using h
    · simpa using hne
    · simp
  · intro a _ _
    simp

theorem integral_sphProb_le {D : ℕ} (F : (Fin (D + 1) → ℂ) → ℝ) (hF0 : ∀ w, 0 ≤ F w) {B : ℝ}
    (hB : ∀ w, sqN w = 1 → F w ≤ B) : ∫ w, F w ∂(sphProb (D + 1)) ≤ B := by
  have hae : ∀ᵐ w ∂(sphProb (D + 1)), sqN w = 1 := by
    rw [ae_iff]
    exact sphProb_compl_sphere D
  letI : IsProbabilityMeasure (sphProb (D + 1)) := by
    unfold sphProb
    infer_instance
  letI : IsFiniteMeasure (sphProb (D + 1)) := ⟨by rw [measure_univ]; norm_num⟩
  calc ∫ w, F w ∂(sphProb (D + 1)) ≤ ∫ _w, B ∂(sphProb (D + 1)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hF0) (integrable_const B)
          (hae.mono fun w hw => hB w hw)
    _ = B := by
      rw [integral_const]
      simp [Measure.real]

def secTraceHom {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ} (x : κ → Ω)
    (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) (n : ℕ) : sec ℤ x n →+ Ω :=
  AddMonoidHom.mk' (fun s => secTrace x e n s) fun s t => secTrace_add x e h n s.2 t.2

def adtEnum (D N : ℕ) (i : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card) : Fin (D + 1) → ℕ :=
  ((Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm i).1

theorem sum_adtEnum {M : Type*} [AddCommMonoid M] (D N : ℕ) (f : (Fin (D + 1) → ℕ) → M) :
    ∑ i, f (adtEnum D N i) = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, f a := by
  exact (Fintype.sum_equiv (Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm _
    (fun x => f x.1) fun _ => rfl).trans (Finset.sum_coe_sort _ f)

def monoDiag (D N δ : ℕ) : Matrix (Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card))
    (Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card)) ℂ :=
  Matrix.diagonal fun p => ((monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2) : ℝ) : ℂ)

theorem monoDiag_posDef (D N δ : ℕ) : (monoDiag D N δ).PosDef := by
  rw [monoDiag, Matrix.posDef_diagonal_iff]
  intro p
  have h : 0 < monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2) := by
    unfold monoNormSq
    positivity
  exact_mod_cast h

theorem neg_log_det_monoDiag (D N δ : ℕ) :
    -(1 / 2) * Real.log (monoDiag D N δ).det.re = δ * chiP D N := by
  have hpos : ∀ a : Fin (D + 1) → ℕ, 0 < monoNormSq a := fun a => by
    unfold monoNormSq
    positivity
  have hdet : (monoDiag D N δ).det.re =
      ∏ p : Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card),
        monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2) := by
    rw [monoDiag, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]
  rw [hdet, Real.log_prod fun p _ => (hpos _).ne']
  rw [← finProdFinEquiv.sum_comp (fun p => Real.log (monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2)))]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_adtEnum D N (fun a => Real.log (monoNormSq a)), chiP]
  ring

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def dmap (W : Ideal (MRing ι)) (i : ∀ k, ι k) (a : K → ℕ) : mPiece W a → MRing ι ⧸ dehomI W i :=
  fun x => Ideal.Quotient.factor (le_sup_left : W ≤ dehomI W i) x.1

theorem dmap_injective {W : Ideal (MRing ι)} (hWp : W.IsPrime) (hWm : IsMultiHomogIdeal W)
    {i : ∀ k, ι k} (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W) (a : K → ℕ) :
    Function.Injective (dmap W i a) := by
  classical
  have homog_of_mem : ∀ {b : K → ℕ} {f : MRing ι}, f ∈ mHom ι b → IsMultiHomog f b := by
    intro b f hf
    unfold mHom at hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      intro m hm
      simp at hm
    | add x y _ _ hx hy =>
      intro m hm k
      rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
      · exact hx m h k
      · exact hy m h k
    | smul n x _ hx =>
      intro m hm k
      exact hx m (MvPolynomial.support_smul hm) k
  rintro ⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩ hxy
  have hd : Ideal.Quotient.mk (dehomI W i) s = Ideal.Quotient.mk (dehomI W i) t := hxy
  have hsub : s - t ∈ dehomI W i := Ideal.Quotient.eq.1 hd
  have hW := mem_of_mem_dehomI hWp hWm hi (homog_of_mem (Submodule.sub_mem _ hs ht)) hsub
  apply Subtype.ext
  exact Ideal.Quotient.eq.2 hW

theorem dmap_mono (W : Ideal (MRing ι)) (i : ∀ k, ι k) {a a' : K → ℕ} (h : ∀ k, a k ≤ a' k)
    (x : mPiece W a) : ∃ x' : mPiece W a', dmap W i a' x' = dmap W i a x := by
  classical
  have homog_of_mem : ∀ {b : K → ℕ} {f : MRing ι}, f ∈ mHom ι b → IsMultiHomog f b := by
    intro b f hf
    unfold mHom at hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      intro m hm
      simp at hm
    | add x y _ _ hx hy =>
      intro m hm k
      rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
      · exact hx m h k
      · exact hy m h k
    | smul n x _ hx =>
      intro m hm k
      exact hx m (MvPolynomial.support_smul hm) k
  obtain ⟨_, s, hs, rfl⟩ := x
  have hprod : s * xpow i (fun k => a' k - a k) ∈ mHom ι a' := by
    apply Submodule.subset_span
    have := isMultiHomog_mul (homog_of_mem hs) (isMultiHomog_xpow i (fun k => a' k - a k))
    have hsum : a + (fun k => a' k - a k) = a' := by
      funext k
      simp only [Pi.add_apply]
      have := h k
      omega
    rw [hsum] at this
    exact this
  refine ⟨⟨_, Submodule.mem_map_of_mem hprod⟩, ?_⟩
  show Ideal.Quotient.mk (dehomI W i) (s * xpow i (fun k => a' k - a k)) = Ideal.Quotient.mk (dehomI W i) s
  rw [map_mul, mk_xpow, mul_one]

theorem isMultiHomog_monomial (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) :
    IsMultiHomog (monomial m c : MRing ι) (fun k => ∑ i, m ⟨k, i⟩) := by
  classical
  intro m' hm' k
  rw [MvPolynomial.support_monomial] at hm'
  split_ifs at hm' with hc
  · simp at hm'
  · rw [Finset.mem_singleton] at hm'
    rw [hm']

theorem dmap_cover (W : Ideal (MRing ι)) (i : ∀ k, ι k) (y : MRing ι ⧸ dehomI W i) :
    ∃ (a : K → ℕ) (x : mPiece W a), dmap W i a x = y := by
  classical
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  let deg : ((Σ k, ι k) →₀ ℕ) → K → ℕ := fun m k => ∑ j, m ⟨k, j⟩
  let a : K → ℕ := fun k => f.support.sup (fun m => deg m k)
  have hle : ∀ m ∈ f.support, ∀ k, deg m k ≤ a k := fun m hm k =>
    Finset.le_sup (f := fun m => deg m k) hm
  have hterm : ∀ m ∈ f.support,
      monomial m (f.coeff m) * xpow i (fun k => a k - deg m k) ∈ mHom ι a := by
    intro m hm
    apply Submodule.subset_span
    have := isMultiHomog_mul (isMultiHomog_monomial m (f.coeff m))
      (isMultiHomog_xpow i (fun k => a k - deg m k))
    have hsum : (fun k => ∑ j, m ⟨k, j⟩) + (fun k => a k - deg m k) = a := by
      funext k
      simp only [Pi.add_apply]
      have := hle m hm k
      simp only [deg] at this ⊢
      omega
    rw [hsum] at this
    exact this
  have hF : (∑ m ∈ f.support, monomial m (f.coeff m) * xpow i (fun k => a k - deg m k)) ∈ mHom ι a :=
    Submodule.sum_mem _ hterm
  refine ⟨a, ⟨_, Submodule.mem_map_of_mem hF⟩, ?_⟩
  show Ideal.Quotient.mk (dehomI W i)
      (∑ m ∈ f.support, monomial m (f.coeff m) * xpow i (fun k => a k - deg m k)) =
    Ideal.Quotient.mk (dehomI W i) f

  simp only [map_sum, map_mul, mk_xpow, mul_one]
  conv_rhs => rw [f.as_sum]

  rw [map_sum]

theorem card_dehom {W : Ideal (MRing ι)} (hWp : W.IsPrime) (hWm : IsMultiHomogIdeal W)
    {i : ∀ k, ι k} (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W) {a₁ c0 : ℕ}
    (hconst : ∀ a : K → ℕ, (∀ k, a₁ ≤ a k) → Nat.card (mPiece W a) = c0)
    (hfin : ∀ a : K → ℕ, Finite (mPiece W a)) {a : K → ℕ} (ha : ∀ k, a₁ ≤ a k) :
    Nat.card (MRing ι ⧸ dehomI W i) = c0 := by
  classical
  have hinj := fun b => dmap_injective hWp hWm hi b
  have hsurj : Function.Surjective (dmap W i a) := by
    intro y
    obtain ⟨b, x, hx⟩ := dmap_cover W i y
    let a' : K → ℕ := fun k => max (a k) (b k)
    have ha' : ∀ k, a₁ ≤ a' k := fun k => le_trans (ha k) (le_max_left _ _)
    obtain ⟨x', hx'⟩ := dmap_mono W i (fun k => le_max_right (a k) (b k)) x
    haveI := hfin a
    haveI := hfin a'
    have hsub : Set.range (dmap W i a) ⊆ Set.range (dmap W i a') := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨z', hz'⟩ := dmap_mono W i (fun k => le_max_left (a k) (b k)) z
      exact ⟨z', hz'⟩
    have hcard : (Set.range (dmap W i a')).ncard ≤ (Set.range (dmap W i a)).ncard := by
      show Nat.card (Set.range (dmap W i a')) ≤ Nat.card (Set.range (dmap W i a))
      first
        | rw [Set.Nat.card_range_of_injective (hinj a), Set.Nat.card_range_of_injective (hinj a'),
            hconst a ha, hconst a' ha']
        | rw [Nat.card_range_of_injective (hinj a), Nat.card_range_of_injective (hinj a'),
            hconst a ha, hconst a' ha']
    have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.finite_range _)
    have hy : y ∈ Set.range (dmap W i a') := ⟨x', hx'.trans hx⟩
    rw [← heq] at hy
    exact hy
  rw [← hconst a ha]
  exact (Nat.card_eq_of_bijective _ ⟨hinj a, hsurj⟩).symm

theorem natCard_eq_pow_length {A : Type*} [AddCommGroup A] [Finite A] {p : ℕ} (hp : p.Prime)
    (h : ∀ x : A, p • x = 0) : Nat.card A = p ^ (Module.length ℤ A).toNat := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Module (ZMod p) A := AddCommGroup.zmodModule h
  have hlen : Module.length ℤ A = Module.length (ZMod p) A :=
    Module.length_eq_of_surjective (fun x => ⟨(x.val : ℤ), by simp⟩)
  have hfin : Module.length (ZMod p) A = (Module.finrank (ZMod p) A : ℕ∞) :=
    @Module.length_eq_finrank (ZMod p) A _ _ _ Module.Finite.of_finite
  have hcard : Nat.card A = Nat.card (ZMod p) ^ Module.finrank (ZMod p) A :=
    @Module.natCard_eq_pow_finrank (ZMod p) A _ _ _ Module.Finite.of_finite
  rw [hlen, hfin, ENat.toNat_coe, hcard, Nat.card_zmod]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem natCast_mem_of_charOf (W : Ideal (MRing ι)) : ((charOf W : ℕ) : MRing ι) ∈ W := by
  show (((Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs : ℕ) : MRing ι) ∈ W
  have hg := Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing ι))
  have hn : (((Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs : ℕ) : ℤ) ∈
      W.comap (C : ℤ →+* MRing ι) := by
    obtain ⟨u, hu⟩ : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) ∣
        ((Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs : ℤ) :=
      Int.dvd_natAbs.2 dvd_rfl
    rw [hu]
    exact Ideal.mul_mem_right u _ hg
  have h := Ideal.mem_comap.1 hn
  rwa [map_natCast] at h

theorem charOf_ne_zero_of_mem {W : Ideal (MRing ι)} {p : ℕ} (hp : p ≠ 0)
    (hpW : (p : MRing ι) ∈ W) : charOf W ≠ 0 := by
  intro h0
  have hp' : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, map_natCast]; exact hpW
  have hg0 : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) = 0 := Int.natAbs_eq_zero.1 h0
  obtain ⟨s, hs⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator _).1 hp'
  rw [hg0, smul_zero] at hs
  exact hp (by exact_mod_cast hs)

theorem charOf_eq_of_mem {W : Ideal (MRing ι)} (hW : W.IsPrime) {p : ℕ} (hp : p.Prime)
    (hpW : (p : MRing ι) ∈ W) : charOf W = p := by
  have hp' : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, map_natCast]; exact hpW
  have hdvd := (Submodule.IsPrincipal.mem_iff_generator_dvd _).1 hp'
  have hd : charOf W ∣ p := Int.natAbs_dvd_natAbs.2 hdvd
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h1
  · exfalso
    have hu : IsUnit (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))) :=
      Int.isUnit_iff_natAbs_eq.2 h1
    have h1m : (1 : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) :=
      (Submodule.IsPrincipal.mem_iff_generator_dvd _).2 hu.dvd
    rw [Ideal.mem_comap, map_one] at h1m
    exact hW.ne_top ((Ideal.eq_top_iff_one _).2 h1m)
  · exact h1

theorem isMultiHomogIdeal_chain {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)} {f : Fin N → MRing ι}
    {c : Fin N → K → ℕ} (h0 : IsMultiHomogIdeal (F 0))
    (hj : ∀ j : Fin N, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j}) :
    ∀ j : Fin (N + 1), IsMultiHomogIdeal (F j) := by
  intro j
  induction j using Fin.induction with
  | zero => exact h0
  | succ i ih =>
    obtain ⟨S, hS, hSe⟩ := ih
    refine ⟨S ∪ {f i}, ?_, ?_⟩
    · rintro g (hg | hg)
      · exact hS g hg
      · rw [Set.mem_singleton_iff.1 hg]; exact ⟨c i, (hj i).1⟩
    · rw [(hj i).2, hSe, Ideal.span_union]

theorem le_chain {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)} {f : Fin N → MRing ι}
    (hj : ∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j}) :
    ∀ j : Fin (N + 1), F 0 ≤ F j := by
  intro j
  induction j using Fin.induction with
  | zero => exact le_rfl
  | succ i ih => rw [hj i]; exact ih.trans le_sup_left

theorem card_mPiece_top (a : K → ℕ) : Nat.card (mPiece (⊤ : Ideal (MRing ι)) a) = 1 := by
  have : Subsingleton (MRing ι ⧸ (⊤ : Ideal (MRing ι))) := Ideal.Quotient.subsingleton_iff.2 rfl
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨0⟩⟩

theorem card_mPiece_chain (a : K → ℕ) : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι))
    (f : Fin N → MRing ι) (c : Fin N → K → ℕ) (q : Fin N → Ideal (MRing ι)),
    IsMultiHomogIdeal (F 0) → F (Fin.last N) = ⊤ →
    (∀ j : Fin N, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    (∀ j k, c j k ≤ a k) →
    Nat.card (mPiece (F 0) a) = ∏ j, Nat.card (mPiece (q j) (a - c j)) := by
  intro N
  induction N with
  | zero =>
    intro F f c q h0 hlast hj ha
    have : F 0 = ⊤ := hlast
    rw [this, card_mPiece_top, Fin.prod_univ_zero]
  | succ N ih =>
    intro F f c q h0 hlast hj ha
    have htail := ih (fun j => F j.succ) (fun j => f j.succ) (fun j => c j.succ)
      (fun j => q j.succ)
      (isMultiHomogIdeal_chain h0 (fun j => ⟨(hj j).1, (hj j).2.1⟩) 1)
      (by simpa [Fin.succ_last] using hlast)
      (fun j => by
        have h := hj j.succ
        rwa [← Fin.succ_castSucc] at h)
      (fun j => ha j.succ)
    obtain ⟨h1, h2, h3⟩ := hj 0
    rw [Fin.castSucc_zero] at h2 h3
    rw [card_mPiece_step h0 h1 h3 (ha 0), ← h2, Fin.prod_univ_succ, mul_comm]
    rw [htail]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end
