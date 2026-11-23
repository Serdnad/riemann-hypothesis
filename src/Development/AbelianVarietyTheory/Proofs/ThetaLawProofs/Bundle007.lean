module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem setIntegral_periodic_eq_measure_mul_cube {E I : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]
    (ν : Measure E) [ν.IsAddHaarMeasure] (T : (I → ℝ) ≃L[ℝ] E) (Λ : Submodule ℤ E)
    (hΛ : ∀ p, T p ∈ Λ ↔ ∀ i, ∃ k : ℤ, (k : ℝ) = p i)
    (Fd : Set E) (hFd : IsAddFundamentalDomain Λ Fd ν)
    (F : E → ℝ) (hF : ∀ (l : Λ) z, F (z + l) = F z) :
    ∫ z in Fd, F z ∂ν = (ν Fd).toReal *
      ∫ p in Set.pi Set.univ (fun _ : I => Set.Ico (0 : ℝ) 1), F (T p) := by
  classical
  set b : Module.Basis I ℝ E := (Pi.basisFun ℝ I).map T.toLinearEquiv with hb
  have hrepr : ∀ p i, b.repr (T p) i = p i := by
    intro p i
    simp [hb]
  have hspan : Λ = Submodule.span ℤ (Set.range b) := by
    ext z
    obtain ⟨p, rfl⟩ := T.surjective z
    rw [hΛ, Module.Basis.mem_span_iff_repr_mem]
    simp [hrepr]
  subst hspan
  have hcell := ZSpan.isAddFundamentalDomain b ν
  have hpre : T ⁻¹' ZSpan.fundamentalDomain b
      = Set.pi Set.univ (fun _ : I => Set.Ico (0 : ℝ) 1) := by
    ext p
    simp only [Set.mem_preimage, ZSpan.mem_fundamentalDomain, hrepr, Set.mem_pi, Set.mem_univ,
      true_imp_iff]
  have hcount : Countable (Submodule.span ℤ (Set.range b)) := inferInstance
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range b)) E ν :=
    ⟨fun c s _ => measure_preimage_add ν (c : E) s⟩
  have h1 : ∫ z in Fd, F z ∂ν = ∫ z in ZSpan.fundamentalDomain b, F z ∂ν :=
    hFd.setIntegral_eq hcell (fun l z => by
      have := hF l z
      rw [add_comm] at this
      exact this)
  have h2 : ν Fd = ν (ZSpan.fundamentalDomain b) := hFd.measure_eq hcell
  let e : (I → ℝ) ≃ᵐ E := T.toHomeomorph.toMeasurableEquiv
  have he : (e : (I → ℝ) → E) = T := rfl
  haveI : (Measure.map T (volume : Measure (I → ℝ))).IsAddHaarMeasure :=
    T.isAddHaarMeasure_map _
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • Measure.map e (volume : Measure (I → ℝ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul ν (Measure.map T volume)⟩
  have h3 : ν (ZSpan.fundamentalDomain b) = c := by
    rw [hc, Measure.smul_apply, e.map_apply, he, hpre, Real.volume_pi_Ico]
    simp
  rw [h1, h2, h3, hc, Measure.restrict_smul, integral_smul_nnreal_measure, setIntegral_map_equiv,
    he, hpre]
  simp [NNReal.smul_def]

theorem setIntegral_periodLattice_eq_volume_mul_cube :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
    (τ.map Complex.im).PosDef →
    (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
    ∀ F : (Fin g → ℂ) → ℝ, (∀ (l : Λ) z, F (z + l) = F z) →
    ∫ z in Fd, F z = (volume Fd).toReal * ∫ p in Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1),
      F (φ ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ)))) := by
  intro g Λ φ τ hτ hΛ Fd hFd F hF
  let L : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ) :=
    { toFun := fun p => φ ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ)))
      map_add' := fun p q => by
        rw [← map_add (f := _)]
        congr 1
        ext i
        simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := fun c p => by
        have : ∀ v : Fin g → ℂ, c • v = (c : ℂ) • v := fun v => by ext i; simp
        rw [RingHom.id_apply, this, ← map_smul]
        congr 1
        ext i
        simp [Matrix.mulVec, dotProduct, mul_add, Finset.mul_sum, mul_left_comm] }
  have hL : ∀ p, L p = φ ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ))) :=
    fun _ => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hL, LinearEquiv.map_eq_zero_iff] at hp
    have him : (τ.map Complex.im).mulVec (fun i => p (.inr i)) = 0 := by
      ext i
      have := congrArg Complex.im (congrFun hp i)
      simpa [Matrix.mulVec, dotProduct] using this
    have hr : (fun i => p (.inr i)) = 0 :=
      (Matrix.mulVec_injective_iff_isUnit.mpr hτ.isUnit) (by rw [him, Matrix.mulVec_zero])
    have hr' : ∀ i, p (.inr i) = 0 := fun i => congrFun hr i
    ext (i | i)
    · have := congrFun hp i
      simpa [Matrix.mulVec, dotProduct, hr'] using this
    · exact hr' i
  have hdim : Module.finrank ℝ (Fin g ⊕ Fin g → ℝ) = Module.finrank ℝ (Fin g → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    ring
  let T : (Fin g ⊕ Fin g → ℝ) ≃L[ℝ] (Fin g → ℂ) :=
    (L.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
  have hT : ∀ p, T p = L p := fun _ => rfl
  refine setIntegral_periodic_eq_measure_mul_cube volume T Λ (fun p => ?_) Fd hFd F hF
  rw [hT, hL, hΛ]
  constructor
  · rintro ⟨m, n, h⟩
    have : L p = L (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) := by
      rw [hL, hL, h]
      simp
    have hp := hinj this
    rintro (i | i)
    · exact ⟨m i, by simp [hp]⟩
    · exact ⟨n i, by simp [hp]⟩
  · intro h
    choose k hk using h
    refine ⟨fun i => k (.inl i), fun i => k (.inr i), ?_⟩
    simp [← hk]

end GlobalTheory
end

section

open GlobalTheory.KeyKa

namespace GlobalTheory.SeriesNakayama

theorem mem_pow_smul_top_iff {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] (π : O)
    (n : ℕ) (x : M) :
    x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O M) ↔ ∃ y : M, π ^ n • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem mem_pow_smul_top_pi {O ι : Type*} [CommRing O] (π : O) (n : ℕ) (x : ι → O) :
    x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O (ι → O)) ↔
      ∀ i, x i ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O O) := by
  simp only [mem_pow_smul_top_iff]
  refine ⟨fun ⟨y, hy⟩ i => ⟨y i, congrFun hy i⟩, fun h => ?_⟩
  choose y hy using h
  exact ⟨y, funext hy⟩

theorem surjective_of_mod {O ι κ : Type*} [CommRing O] (π : O)
    [IsAdicComplete (Ideal.span {π}) O] (Φ : (ι → O) →ₗ[O] (κ → O))
    (h : ∀ G : κ → O, ∃ x, ∀ j, G j - Φ x j ∈ Ideal.span {π}) : Function.Surjective Φ := by
  have : IsPrecomplete (Ideal.span {π}) (ι → O) := by
    refine ⟨fun u hu => ?_⟩
    have h1 : ∀ i, ∃ L : O, ∀ k, u k i ≡ L [SMOD (Ideal.span {π} ^ k • ⊤ : Submodule O O)] :=
      fun i => IsPrecomplete.prec' (fun k => u k i) fun {a b} hab =>
        SModEq.sub_mem.2 ((mem_pow_smul_top_pi π a _).1 (SModEq.sub_mem.1 (hu hab)) i)
    choose L hL using h1
    exact ⟨L, fun k => SModEq.sub_mem.2
      ((mem_pow_smul_top_pi π k _).2 fun i => SModEq.sub_mem.1 (hL i k))⟩
  have : IsHausdorff (Ideal.span {π}) (κ → O) := by
    refine ⟨fun x hx => funext fun j => IsHausdorff.haus' (I := Ideal.span {π}) (x j) fun n => ?_⟩
    exact SModEq.sub_mem.2 ((mem_pow_smul_top_pi π n _).1 (SModEq.sub_mem.1 (hx n)) j)
  refine surjective_of_mkQ_comp_surjective (I := Ideal.span {π}) fun G => ?_
  obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
  obtain ⟨x, hx⟩ := h G
  refine ⟨x, ((Submodule.Quotient.eq _).2 ?_).symm⟩
  have := (mem_pow_smul_top_pi π 1 (G - Φ x)).2 fun j => by simpa using hx j
  rwa [pow_one] at this

theorem exists_projection {O K : Type*} [CommRing O] [IsLocalRing O] [Field K] (f : O →+* K)
    (hf : RingHom.ker f = IsLocalRing.maximalIdeal O) :
    ∃ (μ : K →+ K) (l : K → O), (∀ a, f (l a) = μ a) ∧ (∀ a o, μ (a * f o) = μ a * f o) ∧
      ∀ o, μ (f o) = f o := by
  let φ : IsLocalRing.ResidueField O →+* K :=
    Ideal.Quotient.lift _ f fun a ha => by rwa [← hf] at ha
  have hφ : ∀ o, φ (IsLocalRing.residue O o) = f o := fun _ => rfl
  letI := φ.toAlgebra
  obtain ⟨r, hr⟩ := (Algebra.linearMap (IsLocalRing.ResidueField O) K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 φ.injective)
  choose l hl using fun a => IsLocalRing.residue_surjective (R := O) (r a)
  refine ⟨φ.toAddMonoidHom.comp r.toAddMonoidHom, l, fun a => ?_, fun a o => ?_, fun o => ?_⟩
  · change _ = φ (r a)
    rw [← hl, hφ]
  · change φ (r _) = φ (r a) * _
    have : a * f o = IsLocalRing.residue O o • a := mul_comm _ _
    rw [this, map_smul, smul_eq_mul, map_mul, hφ, mul_comm]
  · change φ (r _) = _
    have : r (f o) = IsLocalRing.residue O o := LinearMap.congr_fun hr (IsLocalRing.residue O o)
    rw [this, hφ]

theorem span_mod_equations_lift (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (K : Type) [Field K] (f : O →+* K) (g N : ℕ)
    (Y : Type) (F : Y → Fin g → (MvPowerSeries (Fin g) O))
    (ρ : Y → Fin N → (MvPowerSeries (Fin g) O))
    (hf : RingHom.ker f = IsLocalRing.maximalIdeal O)
    (h : ∀ G : Y → MvPowerSeries (Fin g) K, ∃ v : Fin N → K, ∀ y,
      G y - ∑ k, v k • MvPowerSeries.map f (ρ y k) ∈
        Ideal.span (Set.range fun i => MvPowerSeries.map f (F y i)))
    (G : Y → (MvPowerSeries (Fin g) O)) :
    ∃ v : Fin N → O, ∀ y, G y - ∑ k, v k • ρ y k ∈ Ideal.span (Set.range (F y)) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm := hπ.maximalIdeal_eq
  have : IsAdicComplete (Ideal.span {π}) O := hm ▸ ‹_›
  obtain ⟨μ, l, hl, hμ, hμ1⟩ := exists_projection f hf
  let Φ : (Fin N ⊕ (Y × Fin g × (Fin g →₀ ℕ)) → O) →ₗ[O] (Y × (Fin g →₀ ℕ) → O) :=
    { toFun := fun x j => ∑ k, x (.inl k) * MvPowerSeries.coeff j.2 (ρ j.1 k) +
        ∑ i, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j.2,
          x (.inr (j.1, i, p.1)) * MvPowerSeries.coeff p.2 (F j.1 i)
      map_add' := fun x x' => funext fun j => by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => funext fun j => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum,
          mul_assoc] }
  have hΦ : Function.Surjective Φ := by
    refine surjective_of_mod π Φ fun G => ?_
    let G' : Y → MvPowerSeries (Fin g) K := fun y d => f (G (y, d))
    obtain ⟨v, hv⟩ := h G'
    choose H hH using fun y => (Ideal.mem_span_range_iff_exists_fun).1 (hv y)
    refine ⟨Sum.elim (fun k => l (v k)) fun q => l (MvPowerSeries.coeff q.2.2 (H q.1 q.2.1)), ?_⟩
    rintro ⟨y, d⟩
    rw [← hm, ← hf, RingHom.mem_ker]
    have h1 := congrArg (fun s => μ (MvPowerSeries.coeff d s)) (eq_sub_iff_add_eq.1 (hH y))
    have h2 : MvPowerSeries.coeff d (G' y) = f (G (y, d)) := rfl

    simp only [map_add (f := _), map_sum, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_map,
    MvPowerSeries.coeff_smul, hμ, hμ1, h2] at h1

    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, map_sub, map_add (f := _), map_sum, map_mul, Sum.elim_inl,
    Sum.elim_inr, hl]
    rw [← h1, add_comm, sub_self]
  obtain ⟨x, hx⟩ := hΦ fun j => MvPowerSeries.coeff j.2 (G j.1)
  refine ⟨fun k => x (.inl k), fun y => Ideal.mem_span_range_iff_exists_fun.2
    ⟨fun i => (show MvPowerSeries (Fin g) O from fun d => x (.inr (y, i, d))), ?_⟩⟩
  ext d
  have h1 : _ = MvPowerSeries.coeff d (G y) := congrFun hx (y, d)

  simp only [map_sub, map_sum, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_smul, ← h1, Φ,
  LinearMap.coe_mk, AddHom.coe_mk, add_sub_cancel_left]
  exact Finset.sum_congr rfl fun i _ => MvPowerSeries.coeff_mul d _ _

end GlobalTheory.SeriesNakayama
end

section

open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem exists_pow_span_X_le_of_dense (K : Type) [Field K] (g N : ℕ)
    (I : Ideal (MvPowerSeries (Fin g) K)) (ρ : Fin N → MvPowerSeries (Fin g) K)
    (h : ∀ (r : ℕ) (G : MvPowerSeries (Fin g) K), ∃ v : Fin N → K,
      G - ∑ k, v k • ρ k ∈ I ⊔ Ideal.span (Set.range MvPowerSeries.X) ^ r) :
    ∃ r : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) K)) ^ r ≤ I := by
  set J : Ideal (MvPowerSeries (Fin g) K) := Ideal.span (Set.range MvPowerSeries.X) with hJ
  let L : (Fin N → K) →ₗ[K] MvPowerSeries (Fin g) K := Fintype.linearCombination K ρ
  have hL : ∀ v, L v = ∑ k, v k • ρ k := fun v => Fintype.linearCombination_apply K ρ v
  let V : ℕ →o (Submodule K (Fin N → K))ᵒᵈ :=
    ⟨fun r => OrderDual.toDual (((I ⊔ J ^ r).restrictScalars K).comap L), by
      intro a b hab
      change ((I ⊔ J ^ b).restrictScalars K).comap L ≤ ((I ⊔ J ^ a).restrictScalars K).comap L
      intro v hv
      exact (sup_le_sup_left (Ideal.pow_le_pow_right hab) I) hv⟩
  obtain ⟨r, hr⟩ := IsArtinian.monotone_stabilizes V
  have hV : ∀ v, L v ∈ I ⊔ J ^ r → L v ∈ I ⊔ J ^ (r + 1) := by
    intro v hv
    have e : ((I ⊔ J ^ r).restrictScalars K).comap L = ((I ⊔ J ^ (r + 1)).restrictScalars K).comap L :=
      hr (r + 1) (Nat.le_succ r)
    have : v ∈ ((I ⊔ J ^ r).restrictScalars K).comap L := hv
    rw [e] at this
    exact this
  have hfg : J.FG := Submodule.fg_span (Set.finite_range _)
  have hjac : J ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hJ, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  refine ⟨r, Submodule.le_of_le_smul_of_le_jacobson_bot (N' := J ^ r) (N := I) (I := J)
    (Ideal.FG.pow hfg) hjac ?_⟩
  intro G hG
  obtain ⟨v, hv⟩ := h (r + 1) G
  rw [← hL] at hv
  have h1 : L v ∈ I ⊔ J ^ r := by
    have h2 : G - L v ∈ I ⊔ J ^ r :=
      (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ r)) I) hv
    have h3 : G ∈ I ⊔ J ^ r := Ideal.mem_sup_right hG
    simpa using Ideal.sub_mem _ h3 h2
  have h4 := Ideal.add_mem _ hv (hV v h1)
  rw [sub_add_cancel, pow_succ'] at h4
  exact h4

theorem exists_sub_mem_of_dense : ∀ (K : Type) [Field K] (g N : ℕ) (Y : Type) [Finite Y] (I : Y → Ideal (MvPowerSeries (Fin g) K)) (ρ : Y → Fin N → MvPowerSeries (Fin g) K), (∀ (r : ℕ) (G : Y → MvPowerSeries (Fin g) K), ∃ v : Fin N → K, ∀ y, G y - ∑ k, v k • ρ y k ∈ I y ⊔ Ideal.span (Set.range MvPowerSeries.X) ^ r) → ∀ G : Y → MvPowerSeries (Fin g) K, ∃ v : Fin N → K, ∀ y, G y - ∑ k, v k • ρ y k ∈ I y := by
  intro K _ g N Y _ I ρ h G
  have hy : ∀ y, ∃ r : ℕ,
      Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) K)) ^ r ≤ I y :=
    fun y => exists_pow_span_X_le_of_dense K g N (I y) (ρ y) fun r F => by
      obtain ⟨v, hv⟩ := h r (fun _ => F)
      exact ⟨v, hv y⟩
  choose r hr using hy
  obtain ⟨R, hR⟩ := (Set.finite_range r).bddAbove
  obtain ⟨v, hv⟩ := h R G
  refine ⟨v, fun y => ?_⟩
  exact (sup_le le_rfl ((Ideal.pow_le_pow_right (hR ⟨y, rfl⟩)).trans (hr y))) (hv y)

end GlobalTheory.KeyKa
end
