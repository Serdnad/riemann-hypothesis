module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle023
public import Mathlib.Basic.Real.Basic
public import Formalism.CharacterColumnKernels.Bundle001
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Nat.Choose.Sum
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

noncomputable section

namespace GlobalTheory.StableLatCount

theorem exists_smul_mem_of_span_eq_top (O : Type) [CommRing O] [IsDomain O] (E : Type) [Field E] [Algebra O E]
    [IsFractionRing O E] {A : Type} [AddCommGroup A] [Module E A] [Module O A] [IsScalarTower O E A]
    (M : Submodule O A) (hM : Submodule.span E (M : Set A) = ⊤) (a : A) :
    ∃ d ∈ nonZeroDivisors O, d • a ∈ M := by
  have ha : a ∈ Submodule.span E (M : Set A) := hM ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_mem _, by simpa using hx⟩
  | zero => exact ⟨1, one_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₂ * d₁, mul_mem hd₂ hd₁, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm d₂ d₁ y]
    exact M.add_mem (M.smul_mem _ h₁) (M.smul_mem _ h₂)
  | smul e x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨o, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors O) e
    have h1 : (s : O) • (e • x) = o • x := by
      rw [← algebraMap_smul E (s : O) (e • x), smul_smul, mul_comm, hs, algebraMap_smul]
    refine ⟨(s : O) * d, mul_mem s.2 hd, ?_⟩
    rw [mul_comm, mul_smul, h1, smul_comm d o x]
    exact M.smul_mem o h

theorem exists_smul_mem_finset_of_span_eq_top (O : Type) [CommRing O] [IsDomain O] (E : Type) [Field E]
    [Algebra O E] [IsFractionRing O E] {A : Type} [AddCommGroup A] [Module E A] [Module O A]
    [IsScalarTower O E A] (M : Submodule O A) (hM : Submodule.span E (M : Set A) = ⊤) (t : Finset A) :
    ∃ d ∈ nonZeroDivisors O, ∀ a ∈ t, d • a ∈ M := by
  classical
  refine Finset.induction_on t ⟨1, one_mem _, by simp⟩ ?_
  intro a t _ ih
  obtain ⟨d₁, hd₁, h₁⟩ := ih
  obtain ⟨d₂, hd₂, h₂⟩ := exists_smul_mem_of_span_eq_top O E M hM a
  refine ⟨d₁ * d₂, mul_mem hd₁ hd₂, ?_⟩
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · rw [mul_smul]; exact M.smul_mem _ h₂
  · rw [mul_comm, mul_smul]; exact M.smul_mem _ (h₁ b hb)

theorem homLat_fg_and_span_eq_top (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type)
    [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁]
    [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂]
    [Module.Finite E A₁] [Module.Finite E A₂] (M₁ : Submodule O A₁) (M₂ : Submodule O A₂) :
    IsLat O E M₁ → IsLat O E M₂ →
      (homLat E M₁ M₂).FG ∧ Submodule.span E (homLat E M₁ M₂ : Set (A₂ →ₗ[E] A₁)) = ⊤ := by
  classical
  intro h₁ h₂
  obtain ⟨h₁fg, h₁sp⟩ := h₁
  obtain ⟨h₂fg, h₂sp⟩ := h₂
  obtain ⟨s, hs⟩ := h₂fg
  have hsE : Submodule.span E (s : Set A₂) = ⊤ := by
    rw [eq_top_iff, ← h₂sp, Submodule.span_le, ← hs]
    exact fun x hx => Submodule.span_le_restrictScalars O E _ hx
  have memH : ∀ ψ ∈ homLat E M₁ M₂, ∀ x ∈ M₂, ψ x ∈ M₁ := fun ψ hψ => hψ
  refine ⟨?_, ?_⟩
  · haveI : Module.Finite O M₁ := Module.Finite.iff_fg.mpr h₁fg
    let f : homLat E M₁ M₂ →ₗ[O] (s → M₁) :=
      { toFun := fun ψ x => ⟨ψ.1 x, memH ψ.1 ψ.2 x (hs ▸ Submodule.subset_span x.2)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro ψ φ h
      apply Subtype.ext
      apply LinearMap.ext_on hsE
      intro x hx
      exact congrArg Subtype.val (congrFun h ⟨x, hx⟩)
    haveI := Module.Finite.of_injective f hf
    exact Module.Finite.iff_fg.mp this
  · rw [eq_top_iff]
    intro ψ _
    obtain ⟨d, hd, hdψ⟩ := exists_smul_mem_finset_of_span_eq_top O E M₁ h₁sp (s.image ψ)
    have hmem : d • ψ ∈ homLat E M₁ M₂ := by
      show ∀ x ∈ M₂, (d • ψ) x ∈ M₁
      intro x hx
      rw [← hs] at hx
      induction hx using Submodule.span_induction with
      | mem y hy => rw [LinearMap.smul_apply]; exact hdψ _ (Finset.mem_image_of_mem _ hy)
      | zero => simp
      | add y z _ _ hy hz => rw [map_add (f := _)]; exact M₁.add_mem hy hz
      | smul o y _ hy => rw [LinearMap.map_smul_of_tower]; exact M₁.smul_mem o hy
    have hd' : algebraMap O E d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    have hψ : ψ = (algebraMap O E d)⁻¹ • (d • ψ) := by
      rw [← algebraMap_smul E d ψ, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hψ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.StableLatCount
end
end

section

open GlobalTheory.LogU MvPolynomial Finset

namespace GlobalTheory.LogUIntg

lemma single_add_single_eq_iff {i j i' j' : ℕ} :
    (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j = Finsupp.single 0 i' + Finsupp.single 1 j') ↔
      (i = i' ∧ j = j') := by
  constructor
  · intro h
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma coeff_monomial_two (i j p q : ℕ) (c : ℤ) :
    AddMonoidAlgebra.coeff (monomial (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q) c)
        (Finsupp.single 0 i + Finsupp.single 1 j) =
      if p = i ∧ q = j then c else 0 := by
  rw [coeff_monomial]
  simp only [single_add_single_eq_iff]

lemma monomial_two_eq (p q : ℕ) (c : ℤ) :
    monomial (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q) c = C c * X 0 ^ p * X 1 ^ q := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, monomial_mul]
  simp

lemma factorial_dvd_term (n K s a : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) (hs : s ≤ K) (ha : a ≤ K - s)
    (hn : n ≤ (s + a) + (s + (K - s - a))) :
    n.factorial * ((n - 1) / 2).factorial ∣
      (s + a).factorial * (s + (K - s - a)).factorial *
        (n.factorial / K * (K.choose s * (K - s).choose a)) := by
  have e1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right s a)
  rw [Nat.add_sub_cancel_left] at e1
  have e2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right s (K - s - a))
  rw [Nat.add_sub_cancel_left] at e2
  have e3 := Nat.choose_mul_factorial_mul_factorial ha
  have e4 := Nat.choose_mul_factorial_mul_factorial hs
  have e5 : n.factorial / K * K.factorial = n.factorial * (K - 1).factorial := by
    rw [← Nat.mul_factorial_pred (by omega : K ≠ 0), ← mul_assoc,
      Nat.div_mul_cancel (Nat.dvd_factorial (by omega) hKn)]
  rw [← e1, ← e2]
  have key : (s + a).choose s * s.factorial * a.factorial *
      ((s + (K - s - a)).choose s * s.factorial * (K - s - a).factorial) *
        (n.factorial / K * (K.choose s * (K - s).choose a)) =
      n.factorial * ((K - 1).factorial * ((s + a).choose s * (s + (K - s - a)).choose s * s.factorial)) := by
    calc _ = (s + a).choose s * (s + (K - s - a)).choose s * s.factorial *
          ((K.choose s * s.factorial * ((K - s).choose a * a.factorial * (K - s - a).factorial)) *
            (n.factorial / K)) := by ring
      _ = (s + a).choose s * (s + (K - s - a)).choose s * s.factorial *
          (n.factorial / K * K.factorial) := by rw [e3, e4]; ring
      _ = _ := by rw [e5]; ring
  rw [key]
  exact mul_dvd_mul (dvd_refl _)
    (dvd_mul_of_dvd_left (Nat.factorial_dvd_factorial (by omega)) _)

def Good (n : ℕ) (f : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∀ i j : ℕ, n ≤ i + j → ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) ∣
    ((i.factorial * j.factorial : ℕ) : ℤ) * AddMonoidAlgebra.coeff f (Finsupp.single 0 i + Finsupp.single 1 j)

lemma good_sub {n : ℕ} {f g : MvPolynomial (Fin 2) ℤ} (hf : Good n f) (hg : Good n g) :
    Good n (f - g) := by
  intro i j h
  rw [MvPolynomial.coeff_sub, mul_sub]
  exact dvd_sub (hf i j h) (hg i j h)

lemma good_sum {n : ℕ} {ι : Type} (t : Finset ι) (f : ι → MvPolynomial (Fin 2) ℤ)
    (hf : ∀ x ∈ t, Good n (f x)) : Good n (∑ x ∈ t, f x) := by
  intro i j h
  rw [coeff_sum, Finset.mul_sum]
  exact Finset.dvd_sum fun x hx => hf x hx i j h

lemma good_C_mul {n : ℕ} (c : ℤ) {f : MvPolynomial (Fin 2) ℤ} (hf : Good n f) :
    Good n (C c * f) := by
  intro i j h
  rw [coeff_C_mul, mul_left_comm]
  exact Dvd.dvd.mul_left (hf i j h) c

lemma good_atom (n K s a : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) (hs : s ≤ K) (ha : a ≤ K - s) :
    Good n (monomial (Finsupp.single (0 : Fin 2) (s + a) + Finsupp.single 1 (s + (K - s - a)))
      ((n.factorial / K * (K.choose s * (K - s).choose a) : ℕ) : ℤ)) := by
  intro i j h
  rw [coeff_monomial_two]
  split_ifs with hij
  · obtain ⟨rfl, rfl⟩ := hij
    rw [← Nat.cast_mul]
    exact Int.natCast_dvd_natCast.mpr (factorial_dvd_term n K s a hK1 hKn hs ha h)
  · simp

lemma C_mul_pow_u (m K : ℕ) :
    C (m : ℤ) * (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ^ K =
      ∑ s ∈ range (K + 1), ∑ a ∈ range (K - s + 1),
        monomial (Finsupp.single (0 : Fin 2) (s + a) + Finsupp.single 1 (s + (K - s - a)))
          ((m * (K.choose s * (K - s).choose a) : ℕ) : ℤ) := by
  rw [show (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) = X 0 * X 1 + (X 0 + X 1) by ring,
    add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [add_pow]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [monomial_two_eq]
  simp only [Nat.cast_mul, map_mul, map_natCast]
  ring

lemma good_C_mul_pow_u (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  rw [C_mul_pow_u]
  refine good_sum _ _ fun s hs => good_sum _ _ fun a ha => ?_
  rw [Finset.mem_range] at hs ha
  exact good_atom n K s a hK1 hKn (by omega) (by omega)

lemma logPolynomialDefectDivisible_C_mul_X_zero_pow (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 0 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  have h := good_atom n K 0 K hK1 hKn (by omega) (by omega)
  rw [monomial_two_eq] at h
  simpa using h

lemma logPolynomialDefectDivisible_C_mul_X_one_pow (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 1 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  have h := good_atom n K 0 0 hK1 hKn (by omega) (by omega)
  rw [monomial_two_eq] at h
  simpa using h

lemma good_truncLogF (n : ℕ) (u : MvPolynomial (Fin 2) ℤ)
    (hu : ∀ K, 1 ≤ K → K ≤ n → Good n (C ((n.factorial / K : ℕ) : ℤ) * u ^ K)) :
    Good n (truncLogF n u) := by
  unfold truncLogF
  refine good_sum _ _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  have e : ((-1 : MvPolynomial (Fin 2) ℤ) ^ k * ((n.factorial / (k + 1) : ℕ) : MvPolynomial (Fin 2) ℤ) *
      u ^ (k + 1)) = C ((-1) ^ k) * (C ((n.factorial / (k + 1) : ℕ) : ℤ) * u ^ (k + 1)) := by
    simp only [map_pow, map_neg, map_one, map_natCast]; ring
  rw [e]
  exact good_C_mul _ (hu (k + 1) (by omega) (by omega))

theorem good_logDefect (n : ℕ) : Good n (logDefect n) := by
  unfold logDefect
  refine good_sub (good_sub ?_ ?_) ?_
  · exact good_truncLogF n _ fun K h1 h2 => good_C_mul_pow_u n K h1 h2
  · exact good_truncLogF n _ fun K h1 h2 => logPolynomialDefectDivisible_C_mul_X_zero_pow n K h1 h2
  · exact good_truncLogF n _ fun K h1 h2 => logPolynomialDefectDivisible_C_mul_X_one_pow n K h1 h2

theorem logDefect_coeff_dvd : ∀ (n i j : ℕ), n ≤ i + j → ∃ d : ℤ,
    ((i.factorial * j.factorial : ℕ) : ℤ) *
        AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) =
      ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * d := by
  intro n i j h
  exact good_logDefect n i j h

end GlobalTheory.LogUIntg
end

section

open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem card_ker_eq_card_quot_range {O : Type} [CommRing O] {N : Type} [AddCommGroup N] [Module O N]
    [Finite N] (f : N →ₗ[O] N) :
    Nat.card (LinearMap.ker f) = Nat.card (N ⧸ LinearMap.range f) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h3 : Nat.card (N ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr (f.quotKerEquivRange).toEquiv
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  rw [h3] at h1
  rw [h1] at h2
  nlinarith [h2]

def invariantsOfKilledLevelEquiv {O : Type} [CommRing O] {G : Type} [Group G] {M : Type} [AddCommGroup M]
    [Module O M] (ρ : Representation O G M) (c : O) :
    ReciprocityTheory.Gal.H0 (levRep ρ c) ≃
      LinearMap.ker (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants) where
  toFun x := ⟨⟨x.1.val, fun g => by
      have h : levRep ρ c g x.1 = x.1 := x.2 g
      have := congrArg Lev.val h
      rwa [levRep_val] at this⟩, by
      apply Subtype.ext
      show c • x.1.val = 0
      exact Lev.smul_val x.1⟩
  invFun y := ⟨Lev.mk y.1.1 (by
      have h : (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants) y.1 = 0 := y.2
      exact congrArg Subtype.val h), by
      show ∀ g, _
      intro g
      apply Lev.ext
      rw [levRep_val, Lev.val_mk]
      exact y.1.2 g⟩
  left_inv x := by
    apply Subtype.ext
    apply Lev.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem card_H0_level_rep : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M]
    [Module O M] (ρ : Representation O G M) (c : O), Finite ρ.invariants →
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
      Nat.card (ρ.invariants ⧸ LinearMap.range (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) := by
  intro O _ G _ _ M _ _ ρ c hfin
  rw [Nat.card_congr (invariantsOfKilledLevelEquiv ρ c)]
  exact card_ker_eq_card_quot_range _

end GlobalTheory.ShapeNeg
end

section

namespace GlobalTheory

open GlobalTheory.PositionData

theorem hS_le_bound : ∀ (t : ℕ) (up : Bool) (Fl Fc : Finset ℤ) (η S B W0 : ℝ), 1 ≤ t → (t : ℝ) ≤ η → 0 ≤ B → 0 ≤ S →
    (∀ z ∈ Fl, |(z : ℝ) - ((t : ℝ) - 1) / 2| ≤ η ∧ 2 * B + (t : ℝ) / 2 + 3 ≤ |(z : ℝ) - ((t : ℝ) - 1) / 2|) →
    (∀ z ∈ Fc, W0 ≤ (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ≤ W0 + S + η + 1) →
    2 * B + (t : ℝ) / 2 + 3 ≤ W0 →
    ((GlobalTheory.PositionData.hS up t Fl Fc : ℕ) : ℝ) ≤ W0 + S + 2 * η + 3 := by
  intro t up Fl Fc η S B W0 ht htη hB hS0 hFl hFc hW
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hFl' : ∀ z ∈ Fl, ((t : ℝ) - 1) / 2 - η ≤ (z : ℝ) ∧ (z : ℝ) ≤ ((t : ℝ) - 1) / 2 + η := by
    intro z hz
    have h := (hFl z hz).1
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have castToNat : ∀ x : ℤ, ((x.toNat : ℕ) : ℝ) = max (x : ℝ) 0 := by
    intro x
    have h : ((x.toNat : ℕ) : ℤ) = max x 0 := Int.toNat_eq_max x
    rw [← Int.cast_natCast, h]
    push_cast
    rfl
  have hmn : ∀ (s : Finset ℤ) (H : s.Nonempty) (a : ℝ), (∀ y ∈ s, a ≤ (y : ℝ)) →
      a ≤ ((s.min' H : ℤ) : ℝ) := fun s H a h => h _ (Finset.min'_mem s H)
  have hmx : ∀ (s : Finset ℤ) (H : s.Nonempty) (a : ℝ), (∀ y ∈ s, (y : ℝ) ≤ a) →
      ((s.max' H : ℤ) : ℝ) ≤ a := fun s H a h => h _ (Finset.max'_mem s H)

  have hmxLo : ((mxLo t Fl : ℤ) : ℝ) ≤ ((t : ℝ) - 1) / 2 + η := by
    apply hmx
    intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · push_cast; linarith
    · exact (hFl' y hy).2
  cases up
  ·
    have hFc' : ∀ z ∈ Fc, ((t : ℝ) - 1) / 2 - W0 - S - η - 1 ≤ (z : ℝ) := by
      intro z hz
      have h := (hFc z hz).2
      simp only [Bool.false_eq_true, if_false] at h
      linarith
    have h1 : ((t : ℝ) - 1) / 2 - W0 - S - η - 1 ≤ ((mnAll Fl Fc : ℤ) : ℝ) := by
      apply hmn
      intro y hy
      rw [Finset.mem_insert, Finset.mem_union] at hy
      rcases hy with rfl | hy | hy
      · push_cast; linarith
      · linarith [(hFl' y hy).1]
      · exact hFc' y hy
    have h0 : mnAll Fl Fc ≤ 0 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    have hw : ((wS false Fl Fc : ℕ) : ℤ) = 1 - mnAll Fl Fc := by
      simp only [wS, Bool.false_eq_true, if_false]
      exact Int.toNat_of_nonneg (by omega)
    simp only [PositionData.hS, Bool.false_eq_true, if_false]
    rw [castToNat, hw]
    apply max_le
    · push_cast; linarith
    · linarith
  ·
    have hFc' : ∀ z ∈ Fc, (z : ℝ) ≤ ((t : ℝ) - 1) / 2 + W0 + S + η + 1 := by
      intro z hz
      have h := (hFc z hz).2
      simp only [if_true] at h
      linarith
    have h1 : ((mxAll t Fl Fc : ℤ) : ℝ) ≤ ((t : ℝ) - 1) / 2 + W0 + S + η + 1 := by
      apply hmx
      intro y hy
      rw [Finset.mem_insert, Finset.mem_union] at hy
      rcases hy with rfl | hy | hy
      · push_cast; linarith
      · linarith [(hFl' y hy).2]
      · exact hFc' y hy
    have h2 : ((t : ℝ) - 1) / 2 - η ≤ ((mnLo Fl : ℤ) : ℝ) := by
      apply hmn
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · push_cast; linarith
      · exact (hFl' y hy).1
    have h0 : mnLo Fl ≤ 0 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    have hw : ((wS true Fl Fc : ℕ) : ℤ) = 1 - mnLo Fl := by
      simp only [wS, if_true]
      exact Int.toNat_of_nonneg (by omega)
    simp only [PositionData.hS, if_true]
    rw [castToNat, hw]
    apply max_le
    · push_cast; linarith
    · linarith

end GlobalTheory
end

section

open ReciprocityTheory.Gal

namespace GlobalTheory

theorem KO_divisible_by_uniformiser : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ y : Formalism.NG.KO O, ϖ • y = x := by
  intro O _ _ _ ϖ hϖ x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hϖ.ne_zero
  refine ⟨Submodule.Quotient.mk (z / algebraMap O (FractionRing O) ϖ), ?_⟩
  rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, mul_div_cancel₀ _ h0]

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.exists_linear_relation_descend_base_field : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (ι : Type) [Fintype ι] (V : Set (ι → K)) (c : ι → Ω), c ≠ 0 → (∀ v ∈ V, ∑ s, c s * algebraMap K Ω (v s) = 0) → ∃ d : ι → K, d ≠ 0 ∧ ∀ v ∈ V, ∑ s, d s * v s = 0 := by
  first | exact @GlobalTheory.linRelation_descend | exact GlobalTheory.linRelation_descend | (intros; apply GlobalTheory.linRelation_descend <;> assumption)
end
