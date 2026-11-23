module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle005
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open scoped BigOperators
open IsLocalRing

namespace GlobalTheory

theorem coeff_aeval_C_mul_X {K A J : Type*} [CommRing K] [CommRing A] [Algebra K A] (w : J → A)
    (G : MvPolynomial J K) (d : ℕ) :
    (MvPolynomial.aeval (fun j => Polynomial.C (w j) * Polynomial.X) G).coeff d =
      MvPolynomial.aeval w (MvPolynomial.homogeneousComponent d G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial u a =>
    have h : MvPolynomial.aeval (fun j => Polynomial.C (w j) * Polynomial.X)
        (MvPolynomial.monomial u a) =
        Polynomial.C (MvPolynomial.aeval w (MvPolynomial.monomial u a)) *
          Polynomial.X ^ u.degree := by
      simp only [MvPolynomial.aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_apply,
        mul_assoc]
      rfl
    rw [h, Polynomial.coeff_C_mul_X_pow, MvPolynomial.homogeneousComponent_of_mem
      (MvPolynomial.isHomogeneous_monomial a (rfl : u.degree = u.degree))]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add (f := _), Polynomial.coeff_add, hp, hq]

theorem exists_complete_discreteValuationRing_of_mem_closure_cone :
    ∀ (K A J : Type) [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Fintype J], Algebra.FiniteType K A → ∀ (w : J → A) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J K) (d : ℕ), G.IsHomogeneous d → MvPolynomial.aeval w G = 0 → MvPolynomial.eval v G = 0) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A →ₐ[K] FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  intro K A J _ _ _ _ _ hA w v hv hG
  let L := FractionRing (Polynomial A)
  have hinj : Function.Injective (algebraMap (Polynomial A) L) := IsFractionRing.injective _ _
  have : Algebra.EssFiniteType (Polynomial A) L := .of_isLocalization L (nonZeroDivisors _)
  have : Algebra.FiniteType K (Polynomial A) := .trans hA inferInstance
  have : Algebra.EssFiniteType K L := .comp K (Polynomial A) L
  let ψ : MvPolynomial J K →ₐ[K] Polynomial A :=
    MvPolynomial.aeval fun j => Polynomial.C (w j) * Polynomial.X
  let Φ : MvPolynomial J K →+* L := (algebraMap (Polynomial A) L).comp ψ.toRingHom
  have hker : RingHom.ker Φ ≤ RingHom.ker (MvPolynomial.eval v) := by
    intro G h
    have h1 : ψ G = 0 := hinj (h.trans (map_zero _).symm)

    rw [RingHom.mem_ker, ← MvPolynomial.sum_homogeneousComponent G, map_sum]
    refine Finset.sum_eq_zero fun d _ => hG _ d (MvPolynomial.homogeneousComponent_isHomogeneous d G) ?_
    rw [← coeff_aeval_C_mul_X]
    change (ψ G).coeff d = 0
    rw [h1, Polynomial.coeff_zero]
  have hne : (RingHom.ker (MvPolynomial.eval v)).map Φ.rangeRestrict ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one, Ideal.mem_map_iff_of_surjective _ Φ.rangeRestrict_surjective]
    rintro ⟨G, h1, h2⟩
    have h3 : G - 1 ∈ RingHom.ker Φ := by
      rw [RingHom.mem_ker, RingHom.map_sub, map_one, sub_eq_zero]
      exact congrArg Subtype.val h2
    have h4 := hker h3
    rw [RingHom.mem_ker] at h1 h4
    simp [h1] at h4
  obtain ⟨U, hU, hU'⟩ := Ideal.image_subset_nonunits_valuationSubring (A := Φ.range) _ hne
  have hC : ∀ r : K, Φ (MvPolynomial.C r) = algebraMap K L r := fun r => by
    rw [IsScalarTower.algebraMap_apply K (Polynomial A) L, ← ψ.commutes]
    rfl
  let t : J → L := fun j => Φ (MvPolynomial.X j - MvPolynomial.C (v j))
  have ht : ∀ j, t j = algebraMap (Polynomial A) L
      (Polynomial.C (w j) * Polynomial.X - Polynomial.C (algebraMap K A (v j))) := fun j => by
    simp [t, Φ, ψ]
  obtain ⟨V, hV, hKV, -, htV⟩ := exists_discreteValuationSubring_of_valuationSubring (R := K) U
    (fun r => hU ⟨_, hC r⟩) Set.finite_empty (Set.finite_range t) (by simp)
    (by
      rintro _ ⟨j, rfl⟩
      exact hU' ⟨_, Ideal.mem_map_of_mem _
        (show MvPolynomial.X j - MvPolynomial.C (v j) ∈ _ by simp [RingHom.mem_ker]), rfl⟩)
    (by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
      refine ⟨_, ⟨j, rfl⟩, fun h => hj ?_⟩
      rw [ht, map_eq_zero_iff _ hinj] at h
      simpa using congrArg (fun p : Polynomial A => p.coeff 0) h)
  let W := AdicCompletion (maximalIdeal V) V
  let κ : K →+* V := (algebraMap K L).codRestrict V hKV
  let ι : V →+* W := algebraMap V W
  letI : Algebra K W := (ι.comp κ).toAlgebra
  have hι : Function.Injective ((algebraMap W (FractionRing W)).comp ι) :=
    (IsFractionRing.injective W _).comp (algebraMap_adicCompletion_injective_of_dvr V)
  let g : L →+* FractionRing W := IsFractionRing.lift hι
  have hg : ∀ x : V, g x = algebraMap W (FractionRing W) (ι x) := fun x =>
    IsFractionRing.lift_algebraMap hι x
  let f : A →ₐ[K] FractionRing W :=
    { g.comp ((algebraMap (Polynomial A) L).comp Polynomial.C) with
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply K W (FractionRing W)]
        exact hg (κ r) }
  have htm : ∀ j, t j ∈ V := fun j => V.nonunits_subset (htV _ ⟨j, rfl⟩)
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, f,
    g (algebraMap (Polynomial A) L Polynomial.X), fun j => ι (⟨t j, htm j⟩ + κ (v j)),
    inferInstance, ?_, fun j => ⟨?_, ?_⟩⟩
  · rw [map_ne_zero, map_ne_zero_iff _ hinj]
    exact Polynomial.X_ne_zero
  · rw [← hg]
    change g (t j + algebraMap (Polynomial A) L (Polynomial.C (algebraMap K A (v j)))) =
      _ * g (algebraMap (Polynomial A) L (Polynomial.C (w j)))
    rw [ht, ← map_add (f := _), sub_add_cancel, mul_comm, map_mul, map_mul]
  · change ι _ - ι (κ (v j)) ∈ _
    rw [← map_sub, add_sub_cancel_right]
    exact map_nonunit ι _
      ((ValuationSubring.coe_mem_nonunits_iff (a := ⟨t j, htm j⟩)).mp (htV _ ⟨j, rfl⟩))

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem algHom_eq_of_reduction_eq_of_coords_eq :
    ∀ (O B : Type) [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B] [Algebra.FiniteType O B] (s s' : B →ₐ[O] O) (g : ℕ) (u : Fin g → B), (∀ b, s b - s' b ∈ IsLocalRing.maximalIdeal O) → (∀ i, s (u i) = s' (u i)) → (∀ b, s b = 0 → ∃ t : B, IsUnit (s t) ∧ t * b ∈ Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))) ⊔ (IsLocalRing.maximalIdeal O).map (algebraMap O B)) → s = s' := by
  intro O B _ _ _ _ hft s s' g u hred hu hgen
  classical
  obtain ⟨S, hS⟩ := hft.out
  let N : Ideal O := Ideal.span ((S.image fun b => s' b - s b : Finset O) : Set O)
  have hNfg : N.FG := ⟨_, rfl⟩
  have h1 : ∀ b, s' b - s b ∈ N := by
    intro b
    have hb : b ∈ Algebra.adjoin O (S : Set B) := hS ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      exact Ideal.subset_span (by
        simp only [Finset.coe_image]; exact ⟨x, hx, rfl⟩)
    | algebraMap r => simp
    | add x y _ _ hx hy =>
      have : s' (x + y) - s (x + y) = (s' x - s x) + (s' y - s y) := by
        simp only [map_add (f := _)]; ring
      rw [this]; exact N.add_mem hx hy
    | mul x y _ _ hx hy =>
      have : s' (x * y) - s (x * y) = s' x * (s' y - s y) + s y * (s' x - s x) := by
        simp only [map_mul]; ring
      rw [this]; exact N.add_mem (N.mul_mem_left _ hy) (N.mul_mem_left _ hx)
  have h2 : ∀ y ∈ (IsLocalRing.maximalIdeal O).map (algebraMap O B),
      ∀ c : B, s' (c * y) - s (c * y) ∈ IsLocalRing.maximalIdeal O * N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro c
      have : s' (c * algebraMap O B a) - s (c * algebraMap O B a) = a * (s' c - s c) := by
        simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]; ring
      rw [this]; exact Ideal.mul_mem_mul ha (h1 c)
    | zero => intro c; simp
    | add x y _ _ hx hy =>
      intro c
      have : s' (c * (x + y)) - s (c * (x + y))
          = (s' (c * x) - s (c * x)) + (s' (c * y) - s (c * y)) := by
        simp only [map_add (f := _), map_mul]; ring
      rw [this]; exact Ideal.add_mem _ (hx c) (hy c)
    | smul a x _ hx =>
      intro c
      have := hx (c * a)
      rwa [_root_.mul_assoc] at this
  have h3 : ∀ j ∈ Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))),
      s j = 0 ∧ s' j = 0 := by
    intro j hj
    have a1 : Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))) ≤
        RingHom.ker (s : B →+* O) := by
      rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]
    have a2 : Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))) ≤
        RingHom.ker (s' : B →+* O) := by
      rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker, hu i]
    exact ⟨a1 hj, a2 hj⟩
  have h4 : ∀ x, s' x - s x ∈ IsLocalRing.maximalIdeal O * N := by
    intro x
    have hb : s (x - algebraMap O B (s x)) = 0 := by simp
    have hb' : s' (x - algebraMap O B (s x)) = s' x - s x := by simp
    obtain ⟨t, ht, hmem⟩ := hgen _ hb
    obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 hmem
    have ht' : IsUnit (s' t) := by
      by_contra hn
      have m1 : s' t ∈ IsLocalRing.maximalIdeal O := hn
      have m2 := Ideal.add_mem _ (hred t) m1
      rw [sub_add_cancel] at m2
      exact m2 ht
    obtain ⟨j1, j2⟩ := h3 j hj
    have e1 := congrArg s hjy
    have e2 := congrArg s' hjy
    rw [map_add (f := _), map_mul, hb, j1] at e1
    rw [map_add (f := _), map_mul, hb', j2] at e2
    have h5 := h2 y hy 1
    rw [_root_.one_mul] at h5
    have : s' y - s y = s' t * (s' x - s x) := by
      linear_combination e2 - e1
    rw [this] at h5
    exact (Ideal.unit_mul_mem_iff_mem _ ht').1 h5
  have hN : N = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O) N hNfg ?_ ?_
    · rw [Ideal.span_le]
      intro z hz
      simp only [Finset.coe_image] at hz
      obtain ⟨x, _, rfl⟩ := hz
      exact h4 x
    · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  ext b
  have := h1 b
  rw [hN, Ideal.mem_bot, sub_eq_zero] at this
  exact this.symm

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.exists_ringHom_powerSeries_root' : ∀ (O K : Type) [CommRing O] [CommRing K] (φ : PowerSeries O →+* K) (k : ℕ) (t : K), 0 < k → t ^ k = φ PowerSeries.X → ∃ Φ : PowerSeries O →+* K, (∀ a, Φ (PowerSeries.C a) = φ (PowerSeries.C a)) ∧ Φ PowerSeries.X = t ∧ ∀ f, Φ f ∈ Subring.closure (Set.range φ ∪ {t}) := by
  first | exact @GlobalTheory.exists_ringHom_powerSeries_root | exact GlobalTheory.exists_ringHom_powerSeries_root | (intros; apply GlobalTheory.exists_ringHom_powerSeries_root <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open TensorProduct in
theorem _root_.GlobalTheory.exists_smul_mem_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : Type) [CommRing A]
      [Algebra R A] [Algebra.FiniteType R A] (A₀ : Subalgebra R A) (x : A)
      (Sg : Set (PrimeSpectrum R)), A₀.FG → Dense Sg →
      (∀ P ∈ Sg, ∃ (K : Type) (_ : Field K) (_ : Algebra R K),
        RingHom.ker (algebraMap R K) = P.asIdeal ∧
        (1 ⊗ₜ[R] x : TensorProduct R K A) ∈
          (Algebra.TensorProduct.map (AlgHom.id R K) A₀.val).range) →
      ∃ a : R, a ≠ 0 ∧ a • x ∈ A₀ := by
  intro R _ _ _ A _ _ _ A₀ x Sg hfg hdense hfib
  classical
  haveI : Algebra.FiniteType R A₀ := (Subalgebra.fg_iff_finiteType A₀).1 hfg
  haveI : Algebra.FiniteType A₀ A := Algebra.FiniteType.of_restrictScalars_finiteType R A₀ A
  obtain ⟨a, ha0, s, -, hli, hspan⟩ := _root_.GlobalTheory.GenericFreeness.exists_hasBasisAway_quotient R A₀ A (M := A) (Submodule.span A₀ ({1} : Set A)) (Submodule.fg_span_singleton 1)
  set P := (Submodule.span A₀ ({1} : Set A)).restrictScalars R with hPdef
  have hP : ∀ y, y ∈ P ↔ y ∈ A₀ := by
    intro y
    rw [hPdef, Submodule.restrictScalars_mem, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      rw [Algebra.smul_def, _root_.mul_one]
      exact c.2
    · intro hy
      exact ⟨⟨y, hy⟩, by rw [Algebra.smul_def, _root_.mul_one]; rfl⟩
  obtain ⟨N, hN⟩ := hspan x Submodule.mem_top
  obtain ⟨p, hp, v, hv, hpv⟩ := Submodule.mem_sup.1 hN
  obtain ⟨c, hcs, hcv⟩ := Submodule.mem_span_set.1 hv
  have hcoord : ∀ (K : Type) [Field K] [Algebra R K], algebraMap R K a ≠ 0 → ∀ j ∈ s,
      ∃ θ : A →ₗ[R] K, (∀ y ∈ P, θ y = 0) ∧ ∀ m ∈ s, θ m = if m = j then 1 else 0 := by
    intro K _ _ haK j hj
    let S := Submonoid.powers a
    let f := LocalizedModule.mkLinearMap S (A ⧸ P)
    have hli' : LinearIndependent R (fun i : s => P.mkQ (i : A)) := hli
    have hliₐ := hli'.of_isLocalizedModule (Localization S) S f
    have hsp : ⊤ ≤ Submodule.span (Localization S) (Set.range (⇑f ∘ fun i : s => P.mkQ (i : A))) := by
      intro z _
      obtain ⟨⟨q, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f z
      obtain ⟨y, rfl⟩ := P.mkQ_surjective q
      obtain ⟨n, hn⟩ := hspan y Submodule.mem_top
      obtain ⟨p', hp', w, hw, hpw⟩ := Submodule.mem_sup.1 hn
      have h1 : P.mkQ (a ^ n • y) ∈ Submodule.span R (Set.range fun i : s => P.mkQ (i : A)) := by
        have hp0 : P.mkQ p' = 0 := (Submodule.Quotient.mk_eq_zero P).2 hp'
        rw [← hpw, map_add (f := _), hp0, zero_add]
        have := Submodule.mem_map_of_mem (f := P.mkQ) hw
        rwa [Submodule.map_span, Set.image_eq_range] at this
      have h2 : f (P.mkQ (a ^ n • y)) ∈ Submodule.span (Localization S) (Set.range (⇑f ∘ fun i : s => P.mkQ (i : A))) := by
        have := Submodule.mem_map_of_mem (f := f) h1
        rw [Submodule.map_span, ← Set.range_comp] at this
        exact Submodule.span_le_restrictScalars R (Localization S) _ this
      have hmemS : a ^ n * (t : R) ∈ S := S.mul_mem (Submonoid.pow_mem _ (Submonoid.mem_powers a) n) t.2
      have hu : IsUnit (algebraMap R (Localization S) (a ^ n * t)) := IsLocalization.map_units _ ⟨_, hmemS⟩
      have heq : (algebraMap R (Localization S) (a ^ n * t)) • IsLocalizedModule.mk' f (P.mkQ y) t = f (P.mkQ (a ^ n • y)) := by
        rw [algebraMap_smul, mul_smul, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel', map_smul, map_smul]
      show IsLocalizedModule.mk' f (P.mkQ y) t ∈ _
      rw [← inv_smul_smul hu.unit (IsLocalizedModule.mk' f (P.mkQ y) t)]
      exact Submodule.smul_of_tower_mem _ _ (by rw [Units.smul_def, IsUnit.unit_spec, heq]; exact h2)
    let b := Module.Basis.mk hliₐ hsp
    have hunit : ∀ y : S, IsUnit ((Algebra.ofId R K) y) := by
      rintro ⟨y, k, rfl⟩
      exact IsUnit.mk0 _ (by rw [map_pow]; exact pow_ne_zero _ haK)
    let ψ : Localization S →ₐ[R] K := IsLocalization.liftAlgHom hunit
    refine ⟨ψ.toLinearMap ∘ₗ ((b.coord ⟨j, hj⟩).restrictScalars R) ∘ₗ f ∘ₗ P.mkQ, ?_, ?_⟩
    · intro y hy
      simp [(Submodule.Quotient.mk_eq_zero P).2 hy]
    · intro m hm
      have hb : f (P.mkQ m) = b ⟨m, hm⟩ := by simp [b]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, hb, Module.Basis.coord_apply, Module.Basis.repr_self]
      by_cases hmj : m = j
      · subst hmj; simp
      · simp [Finsupp.single_apply, hmj, Ne.symm hmj]
  have hfibre : ∀ P' ∈ Sg, a ∉ P'.asIdeal → ∀ j ∈ s, c j ∈ P'.asIdeal := by
    intro P' hP' haP j hj
    obtain ⟨K, hK, hKa, hker, hmem⟩ := hfib P' hP'
    obtain ⟨z, hz⟩ := (AlgHom.mem_range _).1 hmem
    have haK : algebraMap R K a ≠ 0 := fun h => haP (hker ▸ RingHom.mem_ker.2 h)
    obtain ⟨θ, hθP, hθs⟩ := hcoord K haK j hj
    let Θ : K ⊗[R] A →ₗ[R] K := TensorProduct.lift ((LinearMap.mul R K).compl₂ θ)
    have hΘ : ∀ k y, Θ (k ⊗ₜ y) = k * θ y := fun k y => rfl
    have hΘ0' : ∀ w, Θ (Algebra.TensorProduct.map (AlgHom.id R K) A₀.val w) = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul k y =>
        rw [Algebra.TensorProduct.map_tmul, hΘ, hθP (A₀.val y) ((hP _).2 y.2), mul_zero]
      | add z₁ z₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂, add_zero]
    have hx : θ x = 0 := by
      have hΘ0 := hΘ0' z
      rw [hz, hΘ, _root_.one_mul] at hΘ0
      exact hΘ0
    by_cases hjs : j ∈ c.support
    · have hθv : θ v = c j • (1 : K) := by
        rw [← hcv, map_finsuppSum, Finsupp.sum, Finset.sum_eq_single j]
        · rw [map_smul, hθs j hj, if_pos rfl]
        · intro m hm hmj
          rw [map_smul, hθs m (hcs hm), if_neg hmj, smul_zero]
        · intro h; exact absurd hjs h
      have h0 : θ (a ^ N • x) = 0 := by rw [map_smul, hx, smul_zero]
      rw [← hpv, map_add (f := _), hθP p hp, zero_add, hθv, Algebra.smul_def, _root_.mul_one] at h0
      rw [← hker]
      exact RingHom.mem_ker.2 h0
    · rw [Finsupp.notMem_support_iff.1 hjs]
      exact P'.asIdeal.zero_mem
  have hc0 : c = 0 := by
    ext j
    by_contra hne
    have hj : j ∈ s := hcs (Finsupp.mem_support_iff.2 hne)
    have hsub : Sg ⊆ PrimeSpectrum.zeroLocus {c j * a} := by
      intro P' hP'
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      by_cases haP : a ∈ P'.asIdeal
      · exact P'.asIdeal.mul_mem_left _ haP
      · exact P'.asIdeal.mul_mem_right _ (hfibre P' hP' haP j hj)
    have huniv : PrimeSpectrum.zeroLocus {c j * a} = Set.univ :=
      Set.eq_univ_of_univ_subset (hdense.closure_eq ▸ closure_minimal hsub (PrimeSpectrum.isClosed_zeroLocus _))
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff, Set.singleton_subset_iff] at huniv
    have hz : c j * a = 0 := (mem_nilradical.1 huniv).eq_zero
    exact hne ((mul_eq_zero.1 hz).resolve_right ha0)
  refine ⟨a ^ N, pow_ne_zero _ ha0, (hP _).1 ?_⟩
  have hv0 : v = 0 := by rw [← hcv, hc0, Finsupp.sum_zero_index]
  rw [← hpv, hv0, add_zero]
  exact hp

end GlobalTheory
end
