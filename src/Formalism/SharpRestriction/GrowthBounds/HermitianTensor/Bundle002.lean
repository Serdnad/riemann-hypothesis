module

public import Formalism.PolynomialDimension.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle009
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TieDefs
public import Formalism.PolynomialDimension.MultinomialDepth.HarmonicDecompositionHolds
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankLetter
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle004
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle008
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsTwoWeightIff
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle004
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def dPsi (K : Type) [Field K] (m : ℕ) : PolXY K (m + 1) →ₗ[K] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  (deltaB K m).toLinearMap ∘ₗ (PsiXY K m).toLinearMap

theorem dPsi_apply (K : Type) [Field K] (m : ℕ) (f : PolXY K (m + 1)) : dPsi K m f = deltaB K m (PsiXY K m f) := rfl

theorem tie5b (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (hg : IsUnit g.det) (g' : GL (Fin (m + 1)) R.Kf)
    (hg' : (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) = g⁻¹) (a b : ℕ)
    (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) :
    y ∈ H0 R.O m (wtPQ m a b) (colSpan R.O g) ↔
      ∃ f ∈ PolAB R.Kf (m + 1) a b, f ∈ latOf g' (GaussLat R.Ov.toSubring) ∧ deltaB R.Kf m (PsiXY R.Kf m f) = y := by
  have := R.std.1.frac_O
  have hΛ : IsLattice R.O (colSpan R.O g) := ⟨g, hg, rfl⟩
  rw [mem_invariant_sections_two_weight_iff hCO m a b hm _ hΛ y]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨f, hf, rfl⟩ := (h2 R.Kf m hm a b x).1 (twoLat_le_twoSp m a b _ hΛ x hx)
    exact ⟨f, hf, (h5 p n' R m hm g hg g' hg' a b f hf).1 hx, rfl⟩
  · rintro ⟨f, hf, hl, rfl⟩
    exact ⟨_, (h5 p n' R m hm g hg g' hg' a b f hf).2 hl, rfl⟩

theorem tie3 (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (a b : ℕ) :
    (PolAB R.Kf (m + 1) a b).map (dPsi R.Kf m) = dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b)) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    exact delta_twoSp R.Kf m a b hm _ ((h2 R.Kf m hm a b _).2 ⟨f, hf, rfl⟩)
  · have h1 : IsUnit (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf).det := by rw [Matrix.det_one]; exact isUnit_one
    obtain ⟨B, -, hB1, -, hB2⟩ := la_basis hinj m (wtPQ m a b) 1 h1
    rw [← hB2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : B i ∈ H0 R.O m (wtPQ m a b) (colSpan R.O (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf)) := by
      rw [H0_eq_twisted_nabla (la_indep hinj) m _ (wtPQ_anti m a b hm) 1 h1, ← hB1]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨f, hf, -, hfe⟩ := (tie5b h2 h5 hCO R m hm 1 h1 1 (by simp) a b (B i)).1 hi
    exact ⟨f, hf, hfe⟩

theorem nuOf_wtPQ_cast (m a b : ℕ) (i : Fin (m + 2)) :
    ((nuOf (wtPQ (m + 1) a b) i : ℕ) : ℤ) = hwt m a b i + b := by
  have h0 : (0 : Fin (m + 1 + 1)) ≠ Fin.last (m + 1) := (last_ne_zero' m).symm
  rw [hwt_apply]
  by_cases hi : i = 0
  · subst hi
    simp [nuOf, wtPQ, h0.symm]
    omega
  · by_cases hl : i = Fin.last (m + 1)
    · simp [nuOf, wtPQ, hl, h0.symm]
    · simp [nuOf, wtPQ, hi, hl, h0.symm]

theorem weylDim_shift (n : ℕ) (lam : Fin n → ℤ) (c : ℤ) : weylDim n (fun i => lam i + c) = weylDim n lam := by
  unfold weylDim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [add_sub_add_right_eq_sub]

theorem finrank_wtPQ (D : Formalism.BasicNotions.D7) (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) (K : Type) [Field K] [CharZero K] (m a b : ℕ) :
    Module.finrank K (dualWeyl K (m + 1 + 1) (m + 1 + 1) (nuOf (wtPQ (m + 1) a b))) = dimHar (m + 1) a b := by
  have hanti : Antitone (nuOf (wtPQ (m + 1) a b)) := by
    intro i j hij
    have := wtPQ_anti (m + 1) a b (by omega) hij
    unfold nuOf
    omega
  have hq : (Module.finrank K (dualWeyl K (m + 1 + 1) (m + 1 + 1) (nuOf (wtPQ (m + 1) a b))) : ℚ) =
      (dimHar (m + 1) a b : ℚ) := by
    rw [finrank_weyl D h3 K _ _ hanti, ← weylDim_hwt_eq, ← weylDim_shift (m + 2) (hwt m a b) b]
    congr 1
    funext i
    exact nuOf_wtPQ_cast m a b i
  exact_mod_cast hq

theorem tie4 (D : Formalism.BasicNotions.D7) (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) {p n' : ℕ}
    (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (a b : ℕ) :
    ∀ f ∈ PolAB R.Kf (m + 1) a b, deltaB R.Kf m (PsiXY R.Kf m f) = 0 →
      ∃ G ∈ PolAB R.Kf (m + 1) (a - 1) (b - 1), f = hXY R.Kf (m + 1) * G := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have : CharZero R.Kf := R.charZero
  have hfin : Module.Finite R.Kf (PolAB R.Kf (m + 1 + 1) a b) := Har2.finite_polAB (m + 1) a b
  set T := (dPsi R.Kf (m + 1)).domRestrict (PolAB R.Kf (m + 1 + 1) a b) with hT
  have hrange : LinearMap.range T = dualWeyl R.Kf (m + 1 + 1) (m + 1 + 1) (nuOf (wtPQ (m + 1) a b)) := by
    rw [hT, LinearMap.range_domRestrict]
    exact tie3 h2 h5 hCO R (m + 1) hm a b
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  rw [hrange, finrank_wtPQ D h3 R.Kf m a b, Har2.finrank_polAB] at hrn
  intro f hf hf0
  have hfk : (⟨f, hf⟩ : PolAB R.Kf (m + 1 + 1) a b) ∈ LinearMap.ker T := hf0
  by_cases hab : a = 0 ∨ b = 0
  · have hk0 : Module.finrank R.Kf (LinearMap.ker T) = 0 := by
      unfold dimHar dimPol at hrn
      rw [if_pos hab] at hrn
      omega
    have hbot : LinearMap.ker T = ⊥ := Submodule.finrank_eq_zero.1 hk0
    rw [hbot, Submodule.mem_bot] at hfk
    have hf00 : f = 0 := congrArg Subtype.val hfk
    exact ⟨0, Submodule.zero_mem _, by rw [hf00, mul_zero]⟩
  · rw [not_or] at hab
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    let μ : PolAB R.Kf (m + 1 + 1) a b →ₗ[R.Kf] PolAB R.Kf (m + 1 + 1) (a + 1) (b + 1) :=
      LinearMap.codRestrict _ ((LinearMap.mulLeft R.Kf (hXY R.Kf (m + 1 + 1))) ∘ₗ (PolAB R.Kf (m + 1 + 1) a b).subtype)
        (fun G => Har2.h_mul_mem G.2)
    have hμinj : Function.Injective μ := by
      intro G G' h
      have h' : hXY R.Kf (m + 1 + 1) * (G : PolXY R.Kf (m + 1 + 1)) = hXY R.Kf (m + 1 + 1) * G' :=
        congrArg Subtype.val h
      exact Subtype.ext (mul_left_cancel₀ (hXY_ne_zero R.Kf (m + 1)) h')
    have hle : LinearMap.range μ ≤ LinearMap.ker T := by
      rintro _ ⟨G, rfl⟩
      show deltaB R.Kf (m + 1) (PsiXY R.Kf (m + 1) (hXY R.Kf (m + 1 + 1) * (G : PolXY R.Kf (m + 1 + 1)))) = 0
      rw [map_mul, map_mul, delta_Psi_h R.Kf (m + 1) hm, zero_mul]
    have hr : Module.finrank R.Kf (LinearMap.range μ) = (a + (m + 1)).choose (m + 1) * (b + (m + 1)).choose (m + 1) := by
      rw [LinearMap.finrank_range_of_inj hμinj, Har2.finrank_polAB]
    have hle2 := Submodule.finrank_mono hle
    have heq : LinearMap.range μ = LinearMap.ker T := by
      apply Submodule.eq_of_le_of_finrank_eq hle
      unfold dimHar dimPol at hrn
      rw [if_neg (by omega)] at hrn
      simp only [Nat.add_sub_cancel] at hrn
      have hkle : Module.finrank R.Kf (LinearMap.ker T) ≤
          (a + 1 + (m + 1)).choose (m + 1) * (b + 1 + (m + 1)).choose (m + 1) := by omega
      omega
    rw [← heq] at hfk
    obtain ⟨G, hG⟩ := hfk
    exact ⟨G, G.2, (congrArg Subtype.val hG).symm⟩

theorem tiePsi_of (D : Formalism.BasicNotions.D7) (h1 : ExplicitMapInjective) (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto)
    (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) : TiePsi := by
  intro p n' R m hm
  have hm1 : 1 ≤ m := by omega
  refine ⟨h1 R.Kf m hm1, h2 R.Kf m hm1, ?_, tie4 D h3 h2 h5 hCO R m hm1, ?_⟩
  · intro a b y
    rw [← tie3 h2 h5 hCO R m hm1 a b]
    exact Submodule.mem_map
  · rintro Λ ⟨g, hg, rfl⟩
    have hgi : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
    refine ⟨Matrix.GeneralLinearGroup.mk'' g⁻¹ hgi, ?_, ?_⟩
    · intro P Q f hf
      exact h5 p n' R m hm1 g hg _ rfl P Q f hf
    · intro a b y
      exact tie5b h2 h5 hCO R m hm1 g hg _ rfl a b y

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def midI (r : ℕ) (j : Fin r) : Fin (r + 1 + 1) := j.castSucc.succ

def midOf {r : ℕ} (t : Fin (r + 1 + 1)) : Option (Fin r) :=
  if h : 0 < t.val ∧ t.val < r + 1 then some ⟨t.val - 1, by omega⟩ else none

def subY (A : Type) [CommRing A] (r : ℕ) :
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A) :=
  aeval fun v => match midOf v.2 with
    | some j => ∑ i : Fin r, C (X (i, j)) * X (v.1, midI r i)
    | none => X v

def sub2 (K : Type) [Field K] (r : ℕ) :
    MvPolynomial (Bool × (Fin (r + 1 + 1) × Fin (r + 1 + 1))) K →ₐ[K]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
  aeval fun w => map (blockEmb K (k := r) (n := r) w.1).toRingHom (subY K r (X w.2))

theorem coeff_sum_monomial_linear {K B σ : Type} [Field K] [CommRing B] [Algebra K B] (L : B →ₗ[K] K) (f : MvPolynomial σ B)
    (u : σ →₀ ℕ) : AddMonoidAlgebra.coeff (∑ u' ∈ f.support, monomial u' (L (AddMonoidAlgebra.coeff f u'))) u = L (AddMonoidAlgebra.coeff f u) := by
  classical
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hu
  · rfl
  · have h0 : AddMonoidAlgebra.coeff f u = 0 := by simpa [mem_support_iff] using hu
    rw [h0, map_zero]

def lcoef {K B σ : Type} [Field K] [CommRing B] [Algebra K B] (L : B →ₗ[K] K) :
    MvPolynomial σ B →ₗ[K] MvPolynomial σ K where
  toFun f := ∑ u ∈ f.support, monomial u (L (AddMonoidAlgebra.coeff f u))
  map_add' f g := by
    ext u
    simp only [AddMonoidAlgebra.coeff_add (R := K), Finsupp.add_apply, coeff_sum_monomial_linear]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]
  map_smul' c f := by
    ext u
    rw [RingHom.id_apply, MvPolynomial.coeff_smul, coeff_sum_monomial_linear, coeff_sum_monomial_linear, MvPolynomial.coeff_smul, map_smul]

theorem coeff_lcoef {K B σ : Type} [Field K] [CommRing B] [Algebra K B] (L : B →ₗ[K] K) (f : MvPolynomial σ B)
    (u : σ →₀ ℕ) : AddMonoidAlgebra.coeff (lcoef L f) u = L (AddMonoidAlgebra.coeff f u) :=
  coeff_sum_monomial_linear L f u

def lamOf (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) :
    MvPolynomial (Bool × (Fin (r + 1 + 1) × Fin (r + 1 + 1))) K →ₗ[K] MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K :=
  lcoef L ∘ₗ (sub2 K r).toLinearMap

def detY (A : Type) [CommRing A] (r : ℕ) : MvPolynomial (Fin r × Fin r) A :=
  Matrix.det (fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))

def resY (A : Type) [CommRing A] (r : ℕ) (s : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) :
    MvPolynomial (Fin r × Fin r) A :=
  eval (idPoint (MvPolynomial (Fin r × Fin r) A) (r + 1 + 1) (r + 1 + 1)) (subY A r s)

def RowA {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (f : MvPolynomial (Fin k × Fin n) K) (d : ℕ) : Prop :=
  ∀ u, AddMonoidAlgebra.coeff f u ≠ 0 → rowDeg u a = d

def shapeC {r : ℕ} (c : ℕ) (β : Fin r → ℕ) : Fin (r + 1 + 1) → ℕ :=
  fun t => if t = 0 then c else match midOf t with
    | some j => β j
    | none => 0

def PhInv (K : Type) [Field K] (r N : ℕ) (α α' : Fin r → ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) : Prop :=
  ∀ l : Matrix (Fin r) (Fin r) K, IsUnit l.det → ∀ f ∈ dualWeyl K r r α, ∀ f' ∈ dualWeyl K r r α',
    L (blockEmb K true (rowAct K l f) * blockEmb K false (rowAct K l f')) =
      l.det ^ N * L (blockEmb K true f * blockEmb K false f')

def QPh : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (r : ℕ), 1 ≤ r → ∀ (a c N : ℕ) (α : Fin r → ℕ), Antitone α → (∀ i, α i ≤ N) →
    (∀ i j, α i ≤ α j + c) → c ≤ 8 * a →
    ∃ L : MvPolynomial (Bool × (Fin r × Fin r)) R.Kf →ₗ[R.Kf] R.Kf,
      PhInv R.Kf r N α (fun i => N - α i.rev) L ∧
      (∀ f ∈ intO R.O r α, ∀ f' ∈ intO R.O r (fun i => N - α i.rev),
        L (blockEmb R.Kf true f * blockEmb R.Kf false f') ∈ Set.range (algebraMap R.O R.Kf)) ∧
      ∃ (nb : ℕ) (u u' : Fin nb → MvPolynomial (Fin r × Fin r) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = weylDim r (fun j => (α j : ℤ)) ∧ (∀ b, ka b ≤ ⌈kappaOneExponent p a (r + 1)⌉₊) ∧
        (∀ b, u b ∈ intO R.O r α) ∧ (∀ a', u' a' ∈ intO R.O r (fun i => N - α i.rev)) ∧
        ∀ a' b, L (blockEmb R.Kf true (u b) * blockEmb R.Kf false (u' a')) = if a' = b then (p : R.Kf) ^ ka b else 0

def SubCoeffP : Prop :=
  ∀ (A : Type) [CommRing A] (r : ℕ) (ν : Fin (r + 1 + 1) → ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A),
    v ∈ dualWeyl A (r + 1 + 1) (r + 1 + 1) ν → ∀ u, AddMonoidAlgebra.coeff (subY A r v) u ∈ dualWeyl A r r (fun j => ν (midI r j))

def SubMapP : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A),
    subY B r (map φ v) = map (map φ) (subY A r v)

def SubRowP : Prop :=
  ∀ (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (d : ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A),
    RowA a v d → RowA a (subY A r v) d

def LamCoeffP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ),
    AddMonoidAlgebra.coeff (lamOf K r L (blockEmb K true v * blockEmb K false t)) u =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal u,
        L (blockEmb K true (AddMonoidAlgebra.coeff (subY K r v) x.1) * blockEmb K false (AddMonoidAlgebra.coeff (subY K r t) x.2))

def LamEquivP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (g : Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) K) (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K),
    lamOf K r L (blockEmb K true (rowAct K g v) * blockEmb K false (rowAct K g t)) =
      rowAct K g (lamOf K r L (blockEmb K true v * blockEmb K false t))

def LamMulP : Prop :=
  ∀ (K : Type) [Field K] (r Q : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (F s t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K), subY K r F = C (detY K r ^ Q) * map C F →
    lamOf K r L (blockEmb K true (F * s) * blockEmb K false t) =
      F * lcoef L (C (blockEmb K true (detY K r ^ Q)) * map (blockEmb K (k := r) (n := r) true).toRingHom (subY K r s) *
        map (blockEmb K (k := r) (n := r) false).toRingHom (subY K r t))

def LamEvalP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K),
    eval (idPoint K (r + 1 + 1) (r + 1 + 1)) (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      L (blockEmb K true (resY K r v) * blockEmb K false (resY K r t))

def LamMemP : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (r N : ℕ) (ν ν' νp : Fin (r + 1 + 1) → ℕ)
    (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K),
    ν (Fin.last (r + 1)) = 0 → ν' (Fin.last (r + 1)) = 0 → νp (Fin.last (r + 1)) = 0 → νp 0 = ν 0 + ν' 0 →
    (∀ j, νp (midI r j) = N) → PhInv K r N (fun j => ν (midI r j)) (fun j => ν' (midI r j)) L →
    ∀ v ∈ dualWeyl K (r + 1 + 1) (r + 1 + 1) ν, ∀ t ∈ dualWeyl K (r + 1 + 1) (r + 1 + 1) ν',
      lamOf K r L (blockEmb K true v * blockEmb K false t) ∈ dualWeyl K (r + 1 + 1) (r + 1 + 1) νp

def SubMuP : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (r : ℕ), 1 ≤ r → ∀ (P Q : ℕ),
    ∀ F ∈ dualWeyl R.Kf (r + 1 + 1) (r + 1 + 1) (nuOf (wtPQ (r + 1) P Q)), subY R.Kf r F = C (detY R.Kf r ^ Q) * map C F

def TopLineP : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (r : ℕ), 1 ≤ r → ∀ (a b : ℕ),
    ∀ Ψ ∈ dualWeyl R.Kf (r + 1 + 1) (r + 1 + 1) (nuOf (wtPQ (r + 1) a b)), RowA 0 Ψ (a + b) → RowA (Fin.last (r + 1)) Ψ 0 →
      Ψ = C (eval (idPoint R.Kf (r + 1 + 1) (r + 1 + 1)) Ψ) * hw R.Kf (le_refl (r + 1 + 1)) (nuOf (wtPQ (r + 1) a b))

def LiftP : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (r c : ℕ) (β : Fin r → ℕ), Antitone β → (∀ j, β j ≤ c) →
    ∀ u ∈ dualWeyl A r r β, ∃ s ∈ dualWeyl A (r + 1 + 1) (r + 1 + 1) (shapeC c β),
      RowA 0 s c ∧ RowA (Fin.last (r + 1)) s 0 ∧ resY A r s = u

def DetDivP : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (r Q : ℕ) (β : Fin r → ℕ), 1 ≤ r → Antitone β →
    ∀ u ∈ dualWeyl A r r (fun j => β j + Q), ∃ u₀ ∈ dualWeyl A r r β, u = detY A r ^ Q * u₀

def IntCapP : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K], Function.Injective (algebraMap O K) →
    ∀ (k : ℕ) (ν : Fin k → ℕ) (F : MvPolynomial (Fin k × Fin k) K), F ∈ dualWeyl K k k ν →
      (∀ u, AddMonoidAlgebra.coeff F u ∈ Set.range (algebraMap O K)) → F ∈ intO O k ν

def HwMulP : Prop :=
  ∀ (A : Type) [CommRing A] (k : ℕ) (ν ν' : Fin k → ℕ), Antitone ν → Antitone ν' →
    hw A (le_refl k) (ν + ν') = hw A (le_refl k) ν * hw A (le_refl k) ν' ∧
    eval (idPoint A k k) (hw A (le_refl k) ν) = 1

end Formalism.MainNotions.flipOneThree.Pf

end
end
