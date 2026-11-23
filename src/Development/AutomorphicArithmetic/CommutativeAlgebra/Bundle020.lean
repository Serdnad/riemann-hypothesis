module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle013
public import Development.EtaleCohomology.EtaleSheaves.Bundle009
public import Development.EtaleCohomology.EtaleSheaves.ProperLineCovers.CoverPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.KrullDimension.Field
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle004
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import GroundTheory.FunctionField.PlaceDefs

@[expose] public section

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.exists_regular_parameters_of_reduced_quotient :
    ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover ℂ K x → IsReduced ((rB ℂ K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0})))) → ∀ φ : rB ℂ K x {0} →ₐ[ℂ] ℂ, (∀ j : Fin d, φ ⟨_, tco_mem ℂ K x j⟩ = 0) → ∀ b : rB ℂ K x {0}, φ b = 0 → ∃ (c : rB ℂ K x {0}) (g : Fin d → rB ℂ K x {0}), φ c ≠ 0 ∧ c * b = ∑ l, g l * ⟨_, tco_mem ℂ K x l⟩ := by
  intro F K _ _ _ _ _ _ d x hc hred φ hφ b hb
  set I : Ideal (rB ℂ K x {0}) := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0})) with hI
  have hφI : ∀ a ∈ I, φ a = 0 := by
    intro a ha
    rw [hI, Ideal.mem_span_range_iff_exists_fun] at ha
    obtain ⟨g, rfl⟩ := ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [map_mul, hφ j, mul_zero]
  let ψ : (rB ℂ K x {0} ⧸ I) →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ I φ hφI
  have hψ : ∀ a, ψ (Ideal.Quotient.mk I a) = φ a := fun a => rfl
  let ι : ↥(rA ℂ x {0}) →+* ↥(rB ℂ K x {0}) :=
    (algebraMap (↥(rA ℂ x {0})) K).codRestrict (rB ℂ K x {0}) (fun r => isIntegral_algebraMap)
  have hι : ∀ r, (ι r : K) = algebraMap F K (r : F) := fun r => rfl
  have hbot : ∀ y (hy : y ∈ rA ℂ x {0}), ∃ c : ℂ,
      Ideal.Quotient.mk I (ι ⟨y, hy⟩) = algebraMap ℂ _ c := by
    intro y hy
    have hy' : y ∈ Algebra.adjoin ℂ {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = x j / x i} := hy
    induction hy' using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨i, hi, j, rfl⟩ := hz
      rw [Finset.mem_singleton] at hi
      subst hi
      induction j using Fin.cases with
      | zero =>
        by_cases h0 : x 0 = 0
        · refine ⟨0, ?_⟩
          have : ι ⟨x 0 / x 0, hy⟩ = 0 := Subtype.ext (by rw [hι]; simp [h0])
          rw [this, map_zero, map_zero]
        · refine ⟨1, ?_⟩
          have : ι ⟨x 0 / x 0, hy⟩ = 1 := Subtype.ext (by rw [hι]; simp [h0])
          rw [this, map_one, map_one]
      | succ j =>
        refine ⟨0, ?_⟩
        rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
        have : ι ⟨x j.succ / x 0, hy⟩ = ⟨_, tco_mem ℂ K x j⟩ := rfl
        rw [this]
        exact Ideal.subset_span ⟨j, rfl⟩
    | algebraMap c =>
      refine ⟨c, ?_⟩
      have : ι ⟨algebraMap ℂ F c, hy⟩ = algebraMap ℂ _ c := by
        apply Subtype.ext
        rw [hι]
        exact (IsScalarTower.algebraMap_apply ℂ F K c).symm
      rw [this]
      exact (Ideal.Quotient.mkₐ ℂ I).commutes c
    | add y z hy1 hz1 ihy ihz =>
      obtain ⟨c1, h1⟩ := ihy hy1
      obtain ⟨c2, h2⟩ := ihz hz1
      refine ⟨c1 + c2, ?_⟩
      have : ι ⟨y + z, hy⟩ = ι ⟨y, hy1⟩ + ι ⟨z, hz1⟩ := by
        rw [← map_add (f := _)]
        rfl
      rw [this, map_add (f := _), h1, h2, map_add (f := _)]
    | mul y z hy1 hz1 ihy ihz =>
      obtain ⟨c1, h1⟩ := ihy hy1
      obtain ⟨c2, h2⟩ := ihz hz1
      refine ⟨c1 * c2, ?_⟩
      have : ι ⟨y * z, hy⟩ = ι ⟨y, hy1⟩ * ι ⟨z, hz1⟩ := by
        rw [← map_mul]
        rfl
      rw [this, map_mul, h1, h2, map_mul]
  let f : ↥(rA ℂ x {0}) →+* (rB ℂ K x {0} ⧸ I) := (Ideal.Quotient.mk I).comp ι
  let g : ↥(rA ℂ x {0}) →+* ℂ := ψ.toRingHom.comp f
  have hfg : (algebraMap ℂ (rB ℂ K x {0} ⧸ I)).comp g = f := by
    ext r
    obtain ⟨c, hc'⟩ := hbot r.1 r.2
    have hr : f r = algebraMap ℂ _ c := hc'
    show algebraMap ℂ _ (ψ (f r)) = f r
    rw [hr, ψ.commutes]
    rfl
  have hint : Algebra.IsIntegral ℂ (rB ℂ K x {0} ⧸ I) := by
    constructor
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨p, hpm, hp⟩ := (a.2 : IsIntegral (↥(rA ℂ x {0})) (a : K))
    refine ⟨p.map g, hpm.map g, ?_⟩
    rw [Polynomial.eval₂_map, hfg]
    have hzero : p.eval₂ ι a = 0 := by
      apply Subtype.ext
      have := Polynomial.hom_eval₂ p ι (rB ℂ K x {0}).val.toRingHom a
      simpa using this.trans hp
    have := Polynomial.hom_eval₂ p ι (Ideal.Quotient.mk I) a
    rw [hzero, map_zero] at this
    exact this.symm
  have hft : Algebra.FiniteType ℂ (rB ℂ K x {0} ⧸ I) := by
    have := hc.3 0
    exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ I) (Ideal.Quotient.mkₐ_surjective ℂ I)
  have hfin : Module.Finite ℂ (rB ℂ K x {0} ⧸ I) := Algebra.IsIntegral.finite
  have hart : IsArtinianRing (rB ℂ K x {0} ⧸ I) := IsArtinianRing.of_finite ℂ _
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (Ideal.Quotient.mk I b) (1 : rB ℂ K x {0} ⧸ I)
  obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨1 - b * y0, ?_⟩
  have hc1 : φ (1 - b * y0) ≠ 0 := by
    simp [map_sub, map_mul, hb]
  have hkill : Ideal.Quotient.mk I ((1 - b * y0) * b) = 0 := by
    have hy2 : Ideal.Quotient.mk I b ^ (n + 1) * Ideal.Quotient.mk I y0 = Ideal.Quotient.mk I b ^ n := by
      simpa [smul_eq_mul] using hy
    have h0 : Ideal.Quotient.mk I (1 - b * y0) * Ideal.Quotient.mk I b ^ n = 0 := by
      rw [map_sub, map_one, map_mul]
      linear_combination (-1 : rB ℂ K x {0} ⧸ I) * hy2
    apply IsReduced.eq_zero
    refine ⟨n + 1, ?_⟩
    rw [map_mul, mul_pow]
    calc Ideal.Quotient.mk I (1 - b * y0) ^ (n + 1) * Ideal.Quotient.mk I b ^ (n + 1)
        = Ideal.Quotient.mk I (1 - b * y0) ^ n * Ideal.Quotient.mk I b
          * (Ideal.Quotient.mk I (1 - b * y0) * Ideal.Quotient.mk I b ^ n) := by ring
      _ = 0 := by rw [h0, mul_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_range_iff_exists_fun] at hkill
  obtain ⟨gg, hgg⟩ := hkill
  exact ⟨gg, hc1, hgg.symm⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.InverseDerivation

variable {a b c : Act} (ρ : Act.Hom a b) (σ : Act.Hom a c) (A : CommRingCat.{0})

private abbrev BD : Prop :=
  Function.Bijective (fun x : a.D.obj A => ((ρ.d.app A x, σ.d.app A x) : b.D.obj A × c.D.obj A))

private abbrev BG : Prop :=
  Function.Bijective (fun g : a.G.obj A => ((ρ.g.app A g, σ.g.app A g) : b.G.obj A × c.G.obj A))

variable {ρ σ A}

private noncomputable def invD (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : a.D.obj A :=
  (Equiv.ofBijective _ hd).symm p

private noncomputable def invG (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : a.G.obj A :=
  (Equiv.ofBijective _ hg).symm p

private theorem invD_fst (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : ρ.d.app A (invD hd p) = p.1 := by
  exact congrArg Prod.fst (Equiv.ofBijective_apply_symm_apply _ hd p)

private theorem invD_snd (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : σ.d.app A (invD hd p) = p.2 := by
  exact congrArg Prod.snd (Equiv.ofBijective_apply_symm_apply _ hd p)

private theorem invG_fst (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : ρ.g.app A (invG hg p) = p.1 := by
  exact congrArg Prod.fst (Equiv.ofBijective_apply_symm_apply _ hg p)

private theorem invG_snd (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : σ.g.app A (invG hg p) = p.2 := by
  exact congrArg Prod.snd (Equiv.ofBijective_apply_symm_apply _ hg p)

private theorem invD_eq (hd : BD ρ σ A) {x : a.D.obj A} {p : b.D.obj A × c.D.obj A}
    (h1 : ρ.d.app A x = p.1) (h2 : σ.d.app A x = p.2) : invD hd p = x := by
  apply hd.1
  refine (Equiv.ofBijective_apply_symm_apply _ hd p).trans ?_
  exact Prod.ext h1.symm h2.symm

private theorem invG_eq (hg : BG ρ σ A) {x : a.G.obj A} {p : b.G.obj A × c.G.obj A}
    (h1 : ρ.g.app A x = p.1) (h2 : σ.g.app A x = p.2) : invG hg p = x := by
  apply hg.1
  refine (Equiv.ofBijective_apply_symm_apply _ hg p).trans ?_
  exact Prod.ext h1.symm h2.symm

private noncomputable def lift (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) : J ⥤ Ob a A where
  obj j := ⟨invD hd ((y.obj j).pt, (z.obj j).pt)⟩
  map {i j} f := ⟨invG hg ((y.map f).1, (z.map f).1), by
    refine hd.1 (Prod.ext ?_ ?_)
    · change ρ.d.app A _ = ρ.d.app A (a.smul A _ _)
      rw [ρ.eq, invD_fst, invD_fst, invG_fst]
      exact (y.map f).2
    · change σ.d.app A _ = σ.d.app A (a.smul A _ _)
      rw [σ.eq, invD_snd, invD_snd, invG_snd]
      exact (z.map f).2⟩
  map_id j := by
    refine Subtype.ext (invG_eq hg ?_ ?_)
    · change ρ.g.app A 1 = (y.map (𝟙 j)).1
      rw [y.map_id]
      exact map_one (ρ.g.app A).hom
    · change σ.g.app A 1 = (z.map (𝟙 j)).1
      rw [z.map_id]
      exact map_one (σ.g.app A).hom
  map_comp {i j l} f g := by
    refine Subtype.ext (invG_eq hg ?_ ?_)
    · change ρ.g.app A (invG hg _ * invG hg _) = (y.map (f ≫ g)).1
      rw [y.map_comp]
      refine (map_mul (ρ.g.app A).hom _ _).trans ?_
      change ρ.g.app A _ * ρ.g.app A _ = _
      rw [invG_fst, invG_fst]
      rfl
    · change σ.g.app A (invG hg _ * invG hg _) = (z.map (f ≫ g)).1
      rw [z.map_comp]
      refine (map_mul (σ.g.app A).hom _ _).trans ?_
      change σ.g.app A _ * σ.g.app A _ = _
      rw [invG_snd, invG_snd]
      rfl

private theorem lift_fst (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) :
    lift hd hg y z ⋙ ρ.fn A = y := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨ρ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob b A) = y.obj j
    rw [invD_fst]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨ρ.d.app A (invD hd ((y.obj i).pt, (z.obj i).pt))⟩ : Ob b A) = y.obj i
      rw [invD_fst]
    · change (⟨ρ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob b A) = y.obj j
      rw [invD_fst]
    · change ρ.g.app A (invG hg ((y.map f).1, (z.map f).1)) = (y.map f).1
      rw [invG_fst]

private theorem lift_snd (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) :
    lift hd hg y z ⋙ σ.fn A = z := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨σ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob c A) = z.obj j
    rw [invD_snd]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨σ.d.app A (invD hd ((y.obj i).pt, (z.obj i).pt))⟩ : Ob c A) = z.obj i
      rw [invD_snd]
    · change (⟨σ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob c A) = z.obj j
      rw [invD_snd]
    · change σ.g.app A (invG hg ((y.map f).1, (z.map f).1)) = (z.map f).1
      rw [invG_snd]

private theorem lift_comp (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (w : J ⥤ Ob a A) :
    lift hd hg (w ⋙ ρ.fn A) (w ⋙ σ.fn A) = w := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨invD hd (ρ.d.app A (w.obj j).pt, σ.d.app A (w.obj j).pt)⟩ : Ob a A) = w.obj j
    rw [invD_eq hd rfl rfl]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨invD hd (ρ.d.app A (w.obj i).pt, σ.d.app A (w.obj i).pt)⟩ : Ob a A) = w.obj i
      rw [invD_eq hd rfl rfl]
    · change (⟨invD hd (ρ.d.app A (w.obj j).pt, σ.d.app A (w.obj j).pt)⟩ : Ob a A) = w.obj j
      rw [invD_eq hd rfl rfl]
    · change invG hg (ρ.g.app A (w.map f).1, σ.g.app A (w.map f).1) = (w.map f).1
      exact invG_eq hg rfl rfl

private theorem comp_inj (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] {w w' : J ⥤ Ob a A}
    (h1 : w ⋙ ρ.fn A = w' ⋙ ρ.fn A) (h2 : w ⋙ σ.fn A = w' ⋙ σ.fn A) : w = w' := by
  calc w = lift hd hg (w ⋙ ρ.fn A) (w ⋙ σ.fn A) := (lift_comp hd hg w).symm
    _ = lift hd hg (w' ⋙ ρ.fn A) (w' ⋙ σ.fn A) := by rw [h1, h2]
    _ = w' := lift_comp hd hg w'

end UpperTheory.InverseDerivation

open UpperTheory.InverseDerivation in
theorem UpperTheory.isIso_stackProductPair_of_bijective :
    ∀ (E : Spc) {a b c : Act} (ρ : Act.Hom a b) (σ : Act.Hom a c),
        (∀ A, Function.Bijective (fun x : a.D.obj A => ((ρ.d.app A x, σ.d.app A x) : b.D.obj A × c.D.obj A))) →
        (∀ A, Function.Bijective (fun g : a.G.obj A => ((ρ.g.app A g, σ.g.app A g) : b.G.obj A × c.G.obj A))) →
        IsIso (Sp.pair E ρ σ) := by
  intro E a b c ρ σ hd hg
  refine isIso_of_bijective_on_simplices _ (fun k T => ?_)
  let A : CommRingCat := Scheme.Γ.obj (op T)
  change Function.Bijective
    (fun p : (E.obj (op (SimplexCategory.mk k))).obj (op T) × (Fin (k+1) ⥤ Ob a A) =>
      (((p.1, p.2 ⋙ ρ.fn A), p.2 ⋙ σ.fn A) :
        ((E.obj (op (SimplexCategory.mk k))).obj (op T) × (Fin (k+1) ⥤ Ob b A)) × (Fin (k+1) ⥤ Ob c A)))
  refine ⟨fun p q h => ?_, fun q => ?_⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact Prod.ext h1 (comp_inj (hd A) (hg A) h2 h3)
  · refine ⟨(q.1.1, lift (hd A) (hg A) q.1.2 q.2), ?_⟩
    simp only [lift_fst, lift_snd]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.PbSp

private theorem hom_val {c : Act} {A : CommRingCat.{0}} {J : Type} [SmallCategory J] {F G : J ⥤ Ob c A} (h : F = G)
    {i j : J} (f : i ⟶ j) : (F.map f).1 = (G.map f).1 := by
  subst h
  rfl

private theorem law_id {P a : Act} (φ : Act.Hom P a) {A : CommRingCat.{0}} {J : Type} [SmallCategory J] (x : J ⥤ Ob a A)
    (j : J) : φ.g.app A 1 = (x.map (𝟙 j)).1 := by
  rw [x.map_id]
  exact map_one _

private theorem law_comp {P a : Act} (φ : Act.Hom P a) {A : CommRingCat.{0}} {J : Type} [SmallCategory J] (x : J ⥤ Ob a A)
    {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (p q : P.G.obj A) (hp : φ.g.app A p = (x.map f).1)
    (hq : φ.g.app A q = (x.map g).1) : φ.g.app A (p * q) = (x.map (f ≫ g)).1 := by
  rw [x.map_comp]
  change _ = (x.map f).1 * (x.map g).1
  rw [map_mul, hp, hq]

private theorem fn_square {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c)
    (A : CommRingCat.{0})
    (h1 : ∀ z : P.D.obj A, r.d.app A (t.d.app A z) = u.d.app A (l.d.app A z))
    (h2 : ∀ z : P.G.obj A, r.g.app A (t.g.app A z) = u.g.app A (l.g.app A z)) :
    t.fn A ⋙ r.fn A = l.fn A ⋙ u.fn A := by
  have ho : ∀ z : Ob P A, (t.fn A ⋙ r.fn A).obj z = (l.fn A ⋙ u.fn A).obj z :=
    fun z => congrArg Ob.mk (h1 z.pt)
  refine Functor.hext ho (fun z w f => ?_)
  exact Ob.hom_heq (ho z) (ho w) _ _ (h2 f.1)

private theorem lift_chain {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c)
    (A : CommRingCat.{0})
    (h3 : ∀ (x : a.D.obj A) (y : b.D.obj A), r.d.app A x = u.d.app A y → ∃! z : P.D.obj A, t.d.app A z = x ∧ l.d.app A z = y)
    (h4 : ∀ (g : a.G.obj A) (h : b.G.obj A), r.g.app A g = u.g.app A h → ∃! z : P.G.obj A, t.g.app A z = g ∧ l.g.app A z = h)
    {J : Type} [SmallCategory J] (x : J ⥤ Ob a A) (y : J ⥤ Ob b A) (h : x ⋙ r.fn A = y ⋙ u.fn A) :
    ∃! z : J ⥤ Ob P A, z ⋙ t.fn A = x ∧ z ⋙ l.fn A = y := by
  have hobj : ∀ j, r.d.app A (x.obj j).pt = u.d.app A (y.obj j).pt :=
    fun j => congrArg (fun F : J ⥤ Ob c A => (F.obj j).pt) h
  have hmap : ∀ (i j : J) (f : i ⟶ j), r.g.app A (x.map f).1 = u.g.app A (y.map f).1 :=
    fun i j f => hom_val h f
  choose zo hzo hzu using fun j => h3 (x.obj j).pt (y.obj j).pt (hobj j)
  choose zg hzg hzgu using fun (i j : J) (f : i ⟶ j) => h4 (x.map f).1 (y.map f).1 (hmap i j f)
  let F : J ⥤ Ob P A :=
    { obj := fun j => Ob.mk (zo j)
      map := fun {i j} f => ⟨zg i j f, by
        refine (hzu i _ ⟨?_, ?_⟩).symm
        · change t.d.app A (P.smul A (zg i j f) (zo j)) = _
          rw [t.eq, (hzg i j f).1, (hzo j).1]
          exact (x.map f).2.symm
        · change l.d.app A (P.smul A (zg i j f) (zo j)) = _
          rw [l.eq, (hzg i j f).2, (hzo j).2]
          exact (y.map f).2.symm⟩
      map_id := fun j => by
        apply Subtype.ext
        exact (hzgu j j (𝟙 j) 1 ⟨law_id t x j, law_id l y j⟩).symm
      map_comp := fun {i j k} f g => by
        apply Subtype.ext
        exact (hzgu i k (f ≫ g) (zg i j f * zg j k g)
          ⟨law_comp t x f g _ _ (hzg i j f).1 (hzg j k g).1,
            law_comp l y f g _ _ (hzg i j f).2 (hzg j k g).2⟩).symm }
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · have ho : ∀ j, (F ⋙ t.fn A).obj j = x.obj j := fun j => congrArg Ob.mk (hzo j).1
    exact Functor.hext ho (fun i j f => Ob.hom_heq (ho i) (ho j) _ _ (hzg i j f).1)
  · have ho : ∀ j, (F ⋙ l.fn A).obj j = y.obj j := fun j => congrArg Ob.mk (hzo j).2
    exact Functor.hext ho (fun i j f => Ob.hom_heq (ho i) (ho j) _ _ (hzg i j f).2)
  · rintro w ⟨hw1, hw2⟩
    have ho : ∀ j, w.obj j = F.obj j := fun j =>
      congrArg Ob.mk (hzu j (w.obj j).pt
        ⟨congrArg (fun G : J ⥤ Ob a A => (G.obj j).pt) hw1,
          congrArg (fun G : J ⥤ Ob b A => (G.obj j).pt) hw2⟩)
    exact Functor.hext ho (fun i j f =>
      Ob.hom_heq (ho i) (ho j) _ _ (hzgu i j f (w.map f).1 ⟨hom_val hw1 f, hom_val hw2 f⟩))

private abbrev Ch (a : Act) (k : ℕ) (T : Scheme.{0}) : Type := Fin (k + 1) ⥤ Ob a (Scheme.Γ.obj (op T))

private def pr1 {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (s : Sx (Sp E a) k T) : Sx E k T :=
  Prod.fst (α := Sx E k T) (β := Ch a k T) s

private def pr2 {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (s : Sx (Sp E a) k T) : Ch a k T :=
  Prod.snd (α := Sx E k T) (β := Ch a k T) s

private def mkS {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (e : Sx E k T) (x : Ch a k T) : Sx (Sp E a) k T :=
  Prod.mk (α := Sx E k T) (β := Ch a k T) e x

end UpperTheory.PbSp

open UpperTheory.PbSp in
theorem UpperTheory.stackProduct_isPullback_of_actionPullback :
    ∀ (E : Spc) {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c),
        (∀ A (z : P.D.obj A), r.d.app A (t.d.app A z) = u.d.app A (l.d.app A z)) →
        (∀ A (z : P.G.obj A), r.g.app A (t.g.app A z) = u.g.app A (l.g.app A z)) →
        (∀ A (x : a.D.obj A) (y : b.D.obj A), r.d.app A x = u.d.app A y → ∃! z : P.D.obj A, t.d.app A z = x ∧ l.d.app A z = y) →
        (∀ A (g : a.G.obj A) (h : b.G.obj A), r.g.app A g = u.g.app A h → ∃! z : P.G.obj A, t.g.app A z = g ∧ l.g.app A z = h) →
        IsPullback (Sp.map E t) (Sp.map E l) (Sp.map E r) (Sp.map E u) := by
  intro E P a b c t l r u h1 h2 h3 h4
  have hsq : ∀ A, t.fn A ⋙ r.fn A = l.fn A ⋙ u.fn A := fun A => fn_square t l r u A (h1 A) (h2 A)
  apply isPullback_of_unique_simplices_pullback
  · ext k T s
    refine Prod.ext rfl ?_
    exact congrArg (fun F => s.2 ⋙ F) (hsq _)
  · intro k T x y hxy
    have e1 : pr1 x = pr1 y := congrArg pr1 hxy
    have e2 : pr2 x ⋙ r.fn _ = pr2 y ⋙ u.fn _ := congrArg pr2 hxy
    obtain ⟨z, ⟨hz1, hz2⟩, hzu⟩ := lift_chain t l r u _ (h3 _) (h4 _) (pr2 x) (pr2 y) e2
    refine ⟨mkS (pr1 x) z, ⟨?_, ?_⟩, ?_⟩
    · change mkS (pr1 x) (z ⋙ t.fn _) = x
      rw [hz1]
      rfl
    · change mkS (pr1 x) (z ⋙ l.fn _) = y
      rw [hz2, e1]
      rfl
    · rintro w ⟨hw1, hw2⟩
      have f1 : pr1 w = pr1 x := congrArg pr1 hw1
      have f2 : pr2 w = z := hzu _ ⟨congrArg pr2 hw1, congrArg pr2 hw2⟩
      change mkS (pr1 w) (pr2 w) = mkS (pr1 x) z
      rw [f1, f2]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem not_isField_of_curve {k : Type} [Field k] {C : Scheme.{0}} (c : C ⟶ Sp k) (hc : IsCurve c)
    (W : C.Opens) (hW : IsAffineOpen W) (hWn : (W : Set C).Nonempty) : ¬ IsField Γ(C, W) := by
  intro hF
  have h := CurveCut.CoverPf.krullDim_eq_one c hc W hW hWn
  rw [ringKrullDim_eq_zero_of_isField hF] at h
  norm_num at h

private theorem stalk_isIntegrallyClosed {k : Type} [Field k] [IsAlgClosed k] {C : Scheme.{0}} (c : C ⟶ Sp k)
    (hc : IsCurve c) (y : C) : IsIntegrallyClosed (C.presheaf.stalk y) := by
  haveI := hc.1
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by simp)
  have hne : (U : Set C).Nonempty := ⟨y, hyU⟩
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  haveI : IsIntegrallyClosed Γ(C, U) := CurveCut.CoverPf.leafNormal _ c hc U hU hne
  letI : Algebra Γ(C, U) (C.presheaf.stalk y) := C.presheaf.algebra_section_stalk ⟨y, hyU⟩
  haveI := hU.isLocalization_stalk ⟨y, hyU⟩
  exact isIntegrallyClosed_of_isLocalization _ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

theorem UpperTheory.isDedekindDomain_affine_sections_of_isCurve :
    ∀ (k : Type) [Field k] [IsAlgClosed k] {C : Scheme.{0}} (c : C ⟶ Sp k), IsCurve c → (∀ W : C.Opens, IsAffineOpen W → (W : Set C).Nonempty → IsDedekindDomain Γ(C, W) ∧ ¬ IsField Γ(C, W)) ∧ ∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y) := by
  intro k _ _ C c hc
  refine ⟨fun W hW hWn => ⟨?_, not_isField_of_curve c hc W hW hWn⟩, stalk_isIntegrallyClosed c hc⟩
  exact LateralTheory.E.E4.CurveCut.CoverPf.LeafDedRing_of LateralTheory.E.E4.CurveCut.CoverPf.leafDim1
    LateralTheory.E.E4.CurveCut.CoverPf.leafNormal k c hc W hW hWn
end
