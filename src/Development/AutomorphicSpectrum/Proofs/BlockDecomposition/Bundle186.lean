module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.RingHom.Flat
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle177
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle153
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
import Formalism.ConjugateSelfDual.Bundle001
import Mathlib.RepresentationTheory.Basic
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle166
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal.SnocPerm

theorem eq_succAbove_of_snoc_eq_perm {n : ℕ} (I : Fin n → Fin (n + 1)) (k : Fin (n + 1))
    (π : Equiv.Perm (Fin (n + 1))) (hI : StrictMono I)
    (h : Fin.snoc (α := fun _ => Fin (n + 1)) I k = ⇑π) : I = k.succAbove := by
  have hcast : ∀ i : Fin n, π i.castSucc = I i := fun i => by
    rw [← h]; simp
  have hlast : π (Fin.last n) = k := by
    rw [← h]; simp
  have hrange : Set.range I = Set.range k.succAbove := by
    rw [Fin.range_succAbove]
    ext y
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩ hy
      rw [← hcast i, ← hlast] at hy
      exact (Fin.castSucc_lt_last i).ne (π.injective hy)
    · intro hy
      obtain ⟨x, rfl⟩ := π.surjective y
      have hx : x ≠ Fin.last n := fun hx => hy (by rw [hx, hlast])
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hx
      exact ⟨i, (hcast i).symm⟩
  exact (StrictMono.range_inj hI (Fin.strictMono_succAbove k)).1 hrange

end GlobalTheory.CompanionTheory.ConeLocal.SnocPerm
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal.JacAlg

def minorGroup {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) {d m : ℕ}
    (D : Fin d → B → B) (κ : Fin m → Fin d) : AddSubgroup B :=
  AddSubgroup.closure {y | ∃ (b : A) (bs : Fin m → A),
    y = ρ b * (Matrix.of fun k l => D (κ k) (ρ (bs l))).det}

theorem minorGroup_mul {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) {d m : ℕ}
    (D : Fin d → B → B) (κ : Fin m → Fin d) (a : A) {y : B}
    (hy : y ∈ minorGroup ρ D κ) : ρ a * y ∈ minorGroup ρ D κ := by
  unfold minorGroup at hy ⊢
  refine AddSubgroup.closure_induction (fun z hz => ?_) ?_
    (fun z₁ z₂ _ _ h₁ h₂ => ?_) (fun z _ hz => ?_) hy
  · obtain ⟨b, bs, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a * b, bs, by rw [map_mul, mul_assoc]⟩
  · rw [mul_zero]
    exact zero_mem _
  · rw [mul_add]
    exact add_mem h₁ h₂
  · rw [mul_neg]
    exact neg_mem hz

theorem leibniz_pow {R : Type} [CommRing R] (q : R → R)
    (hmul : ∀ x y, q (x * y) = x * q y + y * q x) (φ : R) (N : ℕ) :
    q (φ ^ N) = (N : R) * φ ^ (N - 1) * q φ := by
  induction N with
  | zero =>
    have h1 := hmul 1 1
    simp only [mul_one, one_mul] at h1
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    linear_combination -h1
  | succ n ih =>
    rw [pow_succ, hmul, ih]
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      ring

theorem column_clear {A B Af Bw : Type} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bw]
    (ρ : A →+* B) (lam : B →+* Bw) (ι : A →+* Af) (μ : Af →+* Bw) (f : A)
    (hc : μ.comp ι = lam.comp ρ) {d : ℕ} (D : Fin d → B → B) (p : Fin d → Bw → Bw)
    (hmul : ∀ k x y, p k (x * y) = x * p k y + y * p k x)
    (hD : ∀ k x, p k (lam x) = lam (D k x))
    (a : Af) (b : A) (N : ℕ) (hb : ι f ^ N * a = ι b) (k : Fin d) :
    lam (ρ (f ^ N) * D k (ρ b) + ρ (-(N : A) * f ^ (N - 1) * b) * D k (ρ f))
      = (lam (ρ f)) ^ (2 * N) * p k (μ a) := by
  have e1 : ∀ x, μ (ι x) = lam (ρ x) := fun x => by
    simpa using RingHom.congr_fun hc x
  have hF : lam (ρ f) ^ N * μ a = lam (ρ b) := by
    have h1 := congrArg μ hb
    rwa [map_mul, map_pow, e1, e1] at h1
  have hp1 := hmul k (lam (ρ f) ^ N) (μ a)
  rw [hF, hD, leibniz_pow (p k) (hmul k) (lam (ρ f)) N, hD] at hp1
  simp only [map_add (f := _), map_mul, map_neg, map_pow, map_natCast]
  rw [hp1, ← hF]
  ring

theorem det_mem {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) (f : A) {d m : ℕ}
    (D : Fin d → B → B) (κ : Fin m → Fin d) (c₁ c₂ b : Fin m → A) :
    (Matrix.of fun k l => ρ (c₁ l) * D (κ k) (ρ (b l))
      + ρ (c₂ l) * D (κ k) (ρ f)).det ∈ minorGroup ρ D κ := by
  classical
  unfold minorGroup
  set X : Fin m → Fin m → B := fun l k => ρ (c₁ l) * D (κ k) (ρ (b l)) with hX
  set Y : Fin m → Fin m → B := fun l k => ρ (c₂ l) * D (κ k) (ρ f) with hY
  have h1 : (Matrix.of fun k l => ρ (c₁ l) * D (κ k) (ρ (b l))
      + ρ (c₂ l) * D (κ k) (ρ f)).det = Matrix.det (Matrix.of fun l k => (X + Y) l k) := by
    rw [← Matrix.det_transpose]
    rfl
  have h2 : Matrix.det (Matrix.of fun l k => (X + Y) l k) =
      ∑ s : Finset (Fin m), Matrix.det (Matrix.of fun l k => s.piecewise X Y l k) :=
    (Matrix.detRowAlternating (n := Fin m) (R := B)).toMultilinearMap.map_add_univ X Y
  rw [h1, h2]
  refine AddSubgroup.sum_mem _ fun s _ => AddSubgroup.subset_closure ?_
  refine ⟨∏ l, (if l ∈ s then c₁ l else c₂ l), fun l => if l ∈ s then b l else f, ?_⟩
  rw [map_prod, ← Matrix.det_transpose (Matrix.of fun k l =>
      D (κ k) (ρ ((fun l => if l ∈ s then b l else f) l))),
    ← Matrix.det_mul_column]
  congr 1
  ext l k
  by_cases hl : l ∈ s <;> simp [hl, hX, hY, Finset.piecewise, Matrix.transpose_apply]

theorem det_clear {A B Af Bw : Type} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bw]
    (ρ : A →+* B) (lam : B →+* Bw) (ι : A →+* Af) (μ : Af →+* Bw) (f : A)
    (hc : μ.comp ι = lam.comp ρ) (hloc : ∀ a : Af, ∃ (b : A) (N : ℕ), ι f ^ N * a = ι b)
    {d m : ℕ} (D : Fin d → B → B) (p : Fin d → Bw → Bw)
    (hmul : ∀ k x y, p k (x * y) = x * p k y + y * p k x)
    (hD : ∀ k x, p k (lam x) = lam (D k x))
    (κ : Fin m → Fin d) (u : Fin m → Af) :
    ∃ (M : ℕ) (n : B), n ∈ minorGroup ρ D κ ∧
      (lam (ρ f)) ^ M * (Matrix.of fun k l => p (κ k) (μ (u l))).det = lam n := by
  classical
  choose bb NN hbN using hloc
  obtain ⟨N, hN⟩ : ∃ N, ∀ l, NN (u l) ≤ N :=
    ⟨Finset.univ.sup fun l => NN (u l), fun l => Finset.le_sup (f := fun l => NN (u l))
      (Finset.mem_univ l)⟩
  let b : Fin m → A := fun l => f ^ (N - NN (u l)) * bb (u l)
  have hb : ∀ l, ι f ^ N * u l = ι (b l) := by
    intro l
    simp only [b, map_mul, map_pow]
    rw [← hbN (u l), ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hN l)]
  have hcol : ∀ k l, lam (ρ (f ^ N) * D (κ k) (ρ (b l))
      + ρ (-(N : A) * f ^ (N - 1) * b l) * D (κ k) (ρ f))
      = lam (ρ f) ^ (2 * N) * p (κ k) (μ (u l)) :=
    fun k l => column_clear ρ lam ι μ f hc D p hmul hD (u l) (b l) N (hb l) (κ k)
  refine ⟨2 * N * m, (Matrix.of fun k l => ρ (f ^ N) * D (κ k) (ρ (b l))
      + ρ (-(N : A) * f ^ (N - 1) * b l) * D (κ k) (ρ f)).det,
    det_mem ρ f D κ (fun _ => f ^ N) (fun l => -(N : A) * f ^ (N - 1) * b l) b, ?_⟩
  rw [RingHom.map_det]
  have hmat : lam.mapMatrix (Matrix.of fun k l => ρ (f ^ N) * D (κ k) (ρ (b l))
      + ρ (-(N : A) * f ^ (N - 1) * b l) * D (κ k) (ρ f)) =
      Matrix.of fun k l => (fun _ => lam (ρ f) ^ (2 * N)) k * p (κ k) (μ (u l)) := by
    ext k l
    first
      | exact hcol k l
      | simpa using hcol k l
  rw [hmat, Matrix.det_mul_column, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul]
  rfl

theorem clear_sum : ∀ {A B Af Bw : Type} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bw] (ρ : A →+* B) (lam : B →+* Bw) (ι : A →+* Af) (μ : Af →+* Bw) (f : A),
    μ.comp ι = lam.comp ρ → (∀ a : Af, ∃ (b : A) (N : ℕ), ι f ^ N * a = ι b) → (∀ x : B, lam x = 0 → ∃ N : ℕ, ρ f ^ N * x = 0) →
    ∀ {d m : ℕ} {Λ : Type} [Fintype Λ] (D : Fin d → B → B) (p : Fin d → Bw → Bw), (∀ k x y, p k (x + y) = p k x + p k y) →
      (∀ k x y, p k (x * y) = x * p k y + y * p k x) → (∀ k x, p k (lam x) = lam (D k x)) →
      ∀ (κ : Fin m → Fin d) (z : Λ → Af) (u : Λ → Fin m → Af) (x : B),
        lam x = ∑ L, μ (z L) * (Matrix.of fun k l => p (κ k) (μ (u L l))).det →
        ∃ M : ℕ, ρ f ^ M * x ∈ AddSubgroup.closure {y | ∃ (b : A) (bs : Fin m → A), y = ρ b * (Matrix.of fun k l => D (κ k) (ρ (bs l))).det} := by
  intro A B Af Bw _ _ _ _ ρ lam ι μ f hc hloc hker d m Λ _ D p _ hmul hD κ z u x hx
  classical
  have e1 : ∀ a : A, μ (ι a) = lam (ρ a) := fun a => by
    simpa using RingHom.congr_fun hc a
  choose MM nn hnn hMM using fun L => det_clear ρ lam ι μ f hc hloc D p hmul hD κ (u L)
  choose bz Nz hz using fun L => hloc (z L)
  obtain ⟨K, hK⟩ : ∃ K, ∀ L, MM L + Nz L ≤ K :=
    ⟨Finset.univ.sup fun L => MM L + Nz L, fun L => Finset.le_sup (f := fun L => MM L + Nz L)
      (Finset.mem_univ L)⟩
  let e : Λ → A := fun L => f ^ (K - (MM L + Nz L)) * bz L
  have hterm : ∀ L, lam (ρ f) ^ K * (μ (z L) * (Matrix.of fun k l => p (κ k) (μ (u L l))).det)
      = lam (ρ (e L) * nn L) := by
    intro L
    have hzL : lam (ρ f) ^ Nz L * μ (z L) = lam (ρ (bz L)) := by
      have h1 := congrArg μ (hz L)
      rwa [map_mul, map_pow, e1, e1] at h1
    have hK' : K = (K - (MM L + Nz L)) + Nz L + MM L := by
      have h := Nat.sub_add_cancel (hK L)
      rw [add_assoc, add_comm (Nz L) (MM L), h]
    simp only [e, map_mul, map_pow, ← hzL, ← hMM L]
    conv_lhs => rw [hK', pow_add, pow_add]
    ring
  have hymem : (∑ L, ρ (e L) * nn L) ∈ minorGroup ρ D κ :=
    AddSubgroup.sum_mem _ fun L _ => minorGroup_mul ρ D κ (e L) (hnn L)
  have h0 : lam (ρ f ^ K * x - ∑ L, ρ (e L) * nn L) = 0 := by

    rw [map_sub, map_mul, map_pow, hx, Finset.mul_sum, map_sum]
    simp only [hterm]
    exact sub_self _
  obtain ⟨N', hN'⟩ := hker _ h0
  refine ⟨N' + K, ?_⟩
  have h2 : ρ f ^ (N' + K) * x = ρ (f ^ N') * ∑ L, ρ (e L) * nn L := by
    rw [pow_add, mul_assoc, ← sub_eq_zero, map_pow, ← mul_sub]
    exact hN'
  rw [h2]
  exact minorGroup_mul ρ D κ (f ^ N') hymem

end GlobalTheory.CompanionTheory.ConeLocal.JacAlg
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

theorem _root_.GlobalTheory.T.totally_complex_of_ring_equiv : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (e : F ≃+* F'), IsTotallyComplex F → IsTotallyComplex F' := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv | exact GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

theorem exists_coeffs_of_mem_mul_span {S : Type} [CommRing S] {r : ℕ} (J : Ideal S)
    (u : Fin r → S) {w : S} (hw : w ∈ J * Ideal.span (Set.range u)) :
    ∃ a : Fin r → S, (∀ i, a i ∈ J) ∧ ∑ i, u i * a i = w := by
  have hw' : w ∈ J • Submodule.span S (Set.range u) := hw
  obtain ⟨a, ha, hsum⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum J u w).1 hw'
  refine ⟨a, ha, ?_⟩
  rw [← hsum, Finsupp.sum_fintype _ _ (fun i => zero_smul S (u i))]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem mem_map_maximalIdeal_of_flat {R : Type} [CommRing R] [IsLocalRing R] {S : Type}
    [CommRing S] [Algebra R S] [Module.Flat R S] {r : ℕ} (t : Fin r → R)
    (hmin : ∀ x : Fin r → R, ∑ i, x i * t i = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (y a : Fin r → S) (h : ∑ i, algebraMap R S (t i) * y i = ∑ i, algebraMap R S (t i) * a i)
    (i : Fin r) : y i - a i ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R S) := by
  have hrel : ∑ j, t j • (y j - a j) = 0 := by
    simp only [Algebra.smul_def, mul_sub, Finset.sum_sub_distrib, h, sub_self]
  obtain ⟨k, d, w, hw, hd⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := S)
    (f := t) (x := fun j => y j - a j) hrel
  have hwi : y i - a i = ∑ j, d i j • w j := hw i
  rw [hwi]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
  refine hmin (fun i => d i j) ?_ i
  rw [← hd j]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem minimal_generators_flat_independent :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Type) [CommRing S] (c : R →+* S), c.Flat →
    ∀ (r : ℕ) (t : Fin r → R) (I : Ideal R), Ideal.span (Set.range t) = I →
      (∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I →
        ∀ i, x i ∈ IsLocalRing.maximalIdeal R) →
      ∀ y : Fin r → S, ∑ i, c (t i) * y i ∈ (IsLocalRing.maximalIdeal R * I).map c →
        ∀ i, y i ∈ (IsLocalRing.maximalIdeal R).map c := by
  intro R _ _ S _ c hc r t I hI hmin y hy i
  have hmap : (IsLocalRing.maximalIdeal R * I).map c
      = (IsLocalRing.maximalIdeal R).map c * Ideal.span (Set.range fun j => c (t j)) := by
    rw [Ideal.map_mul, ← hI, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hmap] at hy
  obtain ⟨a, ha, hsum⟩ := exists_coeffs_of_mem_mul_span _ _ hy
  have hmin0 : ∀ x : Fin r → R, ∑ i, x i * t i = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal R :=
    fun x hx => hmin x (by rw [hx]; exact Ideal.zero_mem _)
  have h3 : y i - a i ∈ (IsLocalRing.maximalIdeal R).map c := by
    letI := c.toAlgebra
    haveI : Module.Flat R S := hc
    exact mem_map_maximalIdeal_of_flat t hmin0 y a hsum.symm i
  have h4 := Ideal.add_mem _ h3 (ha i)
  rwa [sub_add_cancel] at h4

end GlobalTheory.CompanionTheory.FewEq
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

theorem _root_.GlobalTheory.T.galois_quotient_equiv_of_matching_places : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') → ∀ (T : Set (HeightOneSpectrum (𝓞 F))) (T' : Set (HeightOneSpectrum (𝓞 F'))), (∀ v, v ∈ T ↔ eV v ∈ T') → ∃ Ψ : GS Ω T ≃ₜ* GS Ω' T', ∀ σ : G F Ω, Ψ (toGS Ω T σ) = toGS Ω' T' (Φ σ) := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.exists_gsIso | exact GlobalTheory.CompanionTheory.PTIso.exists_gsIso | (intros; apply GlobalTheory.CompanionTheory.PTIso.exists_gsIso <;> assumption)
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

theorem _root_.GlobalTheory.T.ring_equiv_cyclotomic_character : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω), cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic | exact GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic | (intros; apply GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic <;> assumption)
end
