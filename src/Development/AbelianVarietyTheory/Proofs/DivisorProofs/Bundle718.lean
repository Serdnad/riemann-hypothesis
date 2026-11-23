module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.WpFam.TrAdd

open IsDedekindDomain GlobalTheory.Idele
open scoped nonZeroDivisors

theorem tr_iff {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (x x' : K) :
    Tr t x x' ↔ (t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x ∈
      adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [mem_adelicIdeal_one_iff]; rfl

theorem main : ∀ (K : Type) [Field K] [NumberField K] (t : (Af K)ˣ), (∀ x x' y y' : K, Tr t x x' → Tr t y y' → Tr t (x - y) (x' - y')) ∧ (∀ (a x x' : K), IsIntegral ℤ a → Tr t x x' → Tr t (a * x) (a * x')) ∧ (∀ x : K, ∃ x', Tr t x x') ∧ (∀ x' : K, ∃ x, Tr t x x') := by
  intro K _ _ t
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y y' hx hy
    rw [tr_iff] at *
    have := sub_mem hx hy
    convert this using 1
    simp only [map_sub]
    ring
  · intro a x x' ha hx
    rw [tr_iff] at *
    let b : 𝓞 K := ⟨a, ha⟩
    have := Submodule.smul_mem _ b hx
    convert this using 1
    ext v
    rw [adele_smul_apply]
    have : algebraMap (𝓞 K) K b = a := rfl
    rw [this]
    simp only [adele_sub_apply, adele_mul_apply, adele_algebraMap_apply, map_mul]
    ring
  · intro x
    have hI : ((t⁻¹ : (Af K)ˣ) • (1 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 :=
      GlobalTheory.Idele.smul_ne_zero _ one_ne_zero
    obtain ⟨x', hx'⟩ := exists_sub_mem_adelicIdeal hI (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x)
    refine ⟨x', ?_⟩
    rw [tr_iff]
    have e : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x - algebraMap K (Af K) x' =
        ((t⁻¹ : (Af K)ˣ) : Af K) * -((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) := by
      rw [mul_neg, mul_sub, Units.inv_mul_cancel_left]
      ring
    rw [e, mul_mem_adelicIdeal_smul] at hx'
    simpa using neg_mem hx'
  · intro x'
    obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K))
      ((t : Af K) * algebraMap K (Af K) x')
    exact ⟨x, (tr_iff t x x').2 hx⟩

end GlobalTheory.WpFam.TrAdd
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory



theorem dRel_pull : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (x : HO1 s) (n : ℕ) (y : Fin n → HO1 s) (w : Fin n → GlobForm s), DRel (OAff s) x y w → DRel (OAff s') (pullHO1 h x) (fun k ↦ pullHO1 h (y k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (w k)) := by
  intro R R' _ _ X X' s s' σ φ h x n y w hx
  obtain ⟨f, g, ω, hf, hg, hD⟩ := hx
  obtain ⟨f', hf'⟩ := H1.mk_surjective (OAff s') (pullHO1 h x)
  choose g' hg' using fun k ↦ H1.mk_surjective (OAff s') (pullHO1 h (y k))
  have ef := (isPullO_pullHO1 h x).symm
  rw [← hf', ← hf, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at ef
  obtain ⟨A, hA⟩ := ef
  have eg : ∀ k, ∃ B : C0 (OPair φ s'), d0 (OPair φ s') B =
      ((pairRes φ s').pullbackOneCocycle (g' k)).1 - ((pairPull h).pullbackOneCocycle (g k)).1 := by
    intro k
    have e := (isPullO_pullHO1 h (y k)).symm
    rw [← hg' k, ← hg k, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at e
    exact e
  choose B hB using eg
  have hA' : ∀ ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'), ((pairRes φ s').pullbackOneCocycle f').1 t t' a =
      ((pairPull h).pullbackOneCocycle f).1 t t' a + (A t' - mp (OPair φ s') a (A t)) := by
    intro t t' a
    have e := congrFun (congrFun (congrFun hA t) t') a
    rw [amitsur_d0_apply, Pi.sub_apply, Pi.sub_apply] at e
    exact sub_eq_iff_eq_add'.1 e.symm
  have hB' : ∀ k ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'), ((pairRes φ s').pullbackOneCocycle (g' k)).1 t t' a =
      ((pairPull h).pullbackOneCocycle (g k)).1 t t' a + (B k t' - mp (OPair φ s') a (B k t)) := by
    intro k t t' a
    have e := congrFun (congrFun (congrFun (hB k) t) t') a
    rw [amitsur_d0_apply, Pi.sub_apply, Pi.sub_apply] at e
    exact sub_eq_iff_eq_add'.1 e.symm
  set w' : Fin n → GlobForm s' := fun k ↦ pullForm h (w k) with hw'def
  let Wm : Fin n → Glob1 (OPair φ s') := fun k ↦ pullGlob1 (pairPull h) (w k)
  have hWm : ∀ k t, (Wm k).1 t = (w' k).1 ((pairFst φ).obj t) := fun k t ↦
    (congrArg (fun z : Glob1 (OPair φ s') ↦ z.1 t) (isPullForm_pullForm h (w k))).trans
      (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s') (pairFst φ) t _)
  let κ : A1 (OAff s') := fun T T' a ↦ D R' _ (f'.1 T T' a) - ∑ k, (g' k).1 T T' a • (w' k).1 T'
  have hκ : ∀ ⦃T T' T'' : AffOp X'⦄ (a : T ⟶ T') (b : T' ⟶ T''),
      κ T T'' (a ≫ b) = p1 (OAff s') b (κ T T' a) + κ T' T'' b := by
    intro T T' T'' a b
    have e1 : D R' _ (f'.1 T T'' (a ≫ b)) =
        p1 (OAff s') b (D R' _ (f'.1 T T' a)) + D R' _ (f'.1 T' T'' b) := by
      rw [Z1.comp, Derivation.map_add (D := _), p1_D]
    have e2 : ∀ k, (g' k).1 T T'' (a ≫ b) • (w' k).1 T'' =
        p1 (OAff s') b ((g' k).1 T T' a • (w' k).1 T') + (g' k).1 T' T'' b • (w' k).1 T'' := by
      intro k; rw [Z1.comp, add_smul, oneFormsMapOfFunctorMorphism_smul, ← (w' k).2 b]
    simp only [κ]

    rw [e1, Finset.sum_congr rfl fun k _ ↦ e2 k, Finset.sum_add_distrib, map_sub, map_sum]
    abel
  let θP : A0 (OPair φ s') := fun t ↦
    q1 (pairPull h) t (ω ((pairPull h).G.obj t)) + D R' _ (A t) - ∑ k, B k t • (Wm k).1 t
  have key : ∀ ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'),
      D R' _ (((pairRes φ s').pullbackOneCocycle f').1 t t' a) - ∑ k, ((pairRes φ s').pullbackOneCocycle (g' k)).1 t t' a • (Wm k).1 t' =
        θP t' - p1 (OPair φ s') a (θP t) := by
    intro t t' a
    have hW : ∀ k, (Wm k).1 t' = p1 (OPair φ s') a ((Wm k).1 t) := fun k ↦ (Wm k).2 a
    have e1 : D R' _ (((pairPull h).pullbackOneCocycle f).1 t t' a) =
        ∑ k, ((pairPull h).pullbackOneCocycle (g k)).1 t t' a • (Wm k).1 t' +
          (q1 (pairPull h) t' (ω ((pairPull h).G.obj t')) -
            p1 (OPair φ s') a (q1 (pairPull h) t (ω ((pairPull h).G.obj t)))) := by

      rw [CoefMap.pullCocycleOne_apply, ← cechDeRhamCoefMapOneForms_D, hD, map_add (f := _), map_sum, map_sub, cechDeRhamCoefMapOneForms_naturality]
      congr 1
      exact Finset.sum_congr rfl fun k _ ↦ prodFirstProjection_smul _ _ _
    have e2 : ∀ k, ((pairRes φ s').pullbackOneCocycle (g' k)).1 t t' a • (Wm k).1 t' =
        ((pairPull h).pullbackOneCocycle (g k)).1 t t' a • (Wm k).1 t' + B k t' • (Wm k).1 t' -
          p1 (OPair φ s') a (B k t • (Wm k).1 t) := by
      intro k
      rw [hB', oneFormsMapOfFunctorMorphism_smul, ← hW k, add_smul, sub_smul]
      abel
    simp only [θP]
    rw [hA', Derivation.map_add (D := _), Derivation.map_sub, ← p1_D, e1, Finset.sum_congr rfl fun k _ ↦ e2 k]

    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, map_sub, map_add (f := _), map_sum]
    abel
  let θ' : ∀ t : (Pair φ)ᵒᵖ, Ω[(OAff s').obj ((pairFst φ).obj t)⁄R'] := θP
  have hθ' : ∀ ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'), κ _ _ ((pairFst φ).map a) =
      θ' t' - p1 (OAff s') ((pairFst φ).map a) (θ' t) := by
    intro t t' a
    have k := key a
    simp only [hWm] at k
    exact k
  obtain ⟨θ, hθ⟩ := GlobalTheory.cocycle_one_forms_coboundary_of_restrict (OAff s') (pairFst φ)
    (_root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) (_root_.GlobalTheory.CechDR.pair_cover_affine φ s'))
    (_root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) (_root_.GlobalTheory.CechDR.pair_cover_affine φ s')
      (_root_.GlobalTheory.CechDR.exists_pair_below_two φ s')) κ hκ θ' hθ'
  refine ⟨f', g', θ, hf', hg', fun T T' a ↦ ?_⟩
  exact sub_eq_iff_eq_add'.1 (hθ a)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem clRel_pullForm : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (w : GlobForm s) (n : ℕ) (u v : Fin n → GlobForm s), ClRel (OAff s) w u v → ClRel (OAff s') (GlobalTheory.CechDR.pullForm h w) (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) := by
  intro R R' _ _ X X' s s' σ φ h w n u v hw T'
  have hp : ∀ (ω : GlobForm s) (p : Pair φ), (GlobalTheory.CechDR.pullForm h ω).1 (Opposite.op p.1.1) =
      (semiHom_secPull h p).m1 (ω.1 (Opposite.op p.1.2)) :=
    fun ω p ↦ ((isPullForm_iff.1 (isPullForm_pullForm h ω)) p).symm
  have hg : ∀ (ω : GlobForm s') {T T' : AffOp X'} (a : T ⟶ T'), p1 (OAff s') a (ω.1 T) = ω.1 T' :=
    fun ω _ _ a ↦ (ω.2 a).symm
  rw [← sub_eq_zero]
  refine twoForm_sep_of_basis s' (pairFst φ) (pair_cover_affine φ s') T' _ fun t a ↦ ?_
  rw [map_sub, sub_eq_zero, pOm_dOne, hg]
  have e1 : ∀ k, pOm (OAff s') 2 a (wedge R' _ ((GlobalTheory.CechDR.pullForm h (u k)).1 T')
      ((GlobalTheory.CechDR.pullForm h (v k)).1 T')) = wedge R' _ ((GlobalTheory.CechDR.pullForm h (u k)).1 ((pairFst φ).obj t))
      ((GlobalTheory.CechDR.pullForm h (v k)).1 ((pairFst φ).obj t)) := fun k ↦
    (pOm_wedge (OAff s') a _ _).trans (by rw [hg, hg])
  refine Eq.trans ?_ ((map_sum (pOm (OAff s') 2 a) _ _).trans (Finset.sum_congr rfl fun k _ ↦ e1 k)).symm
  have key : ∀ p : Pair φ, dOne R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h w).1 (Opposite.op p.1.1)) =
      ∑ k, wedge R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h (u k)).1 (Opposite.op p.1.1))
        ((GlobalTheory.CechDR.pullForm h (v k)).1 (Opposite.op p.1.1)) := by
    intro p
    calc dOne R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h w).1 (Opposite.op p.1.1))
        = dOne R' (Sec s' p.1.1.1) ((semiHom_secPull h p).m1 (w.1 (Opposite.op p.1.2))) :=
          congrArg _ (hp w p)
      _ = (semiHom_secPull h p).mOm 2 (dOne R (Sec s p.1.2.1) (w.1 (Opposite.op p.1.2))) :=
          (SemiHom.mOm_dOne _ _).symm
      _ = (semiHom_secPull h p).mOm 2 (wsum (OAff s) u v (Opposite.op p.1.2)) :=
          congrArg ((semiHom_secPull h p).mOm 2) (hw (Opposite.op p.1.2))
      _ = (semiHom_secPull h p).mOm 2 (∑ k, wedge R (Sec s p.1.2.1) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))) := rfl
      _ = ∑ k, (semiHom_secPull h p).mOm 2 (wedge R (Sec s p.1.2.1) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))) := map_sum _ _ _
      _ = ∑ k, wedge R' (Sec s' p.1.1.1) ((semiHom_secPull h p).m1 ((u k).1 (Opposite.op p.1.2)))
            ((semiHom_secPull h p).m1 ((v k).1 (Opposite.op p.1.2))) :=
          Finset.sum_congr rfl fun k _ ↦ SemiHom.mOm_wedge (semiHom_secPull h p) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))
      _ = ∑ k, wedge R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h (u k)).1 (Opposite.op p.1.1))
            ((GlobalTheory.CechDR.pullForm h (v k)).1 (Opposite.op p.1.1)) :=
          Finset.sum_congr rfl fun k _ ↦ congrArg₂ (fun a b ↦ wedge R' (Sec s' p.1.1.1) a b)
            (hp (u k) p).symm (hp (v k) p).symm
  exact key t.unop

end GlobalTheory.AbCoh
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.PullbackCupProduct

open GlobalTheory.CatCoh

universe u v u' v' u'' v''

theorem pull_cup_of_bijective {R R' : Type} [CommRing R] [CommRing R']
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
    {σ : R →+* R'} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
    {F'' : C'' ⥤ CommAlgCat.{0} R'} (m : CoefMap σ F F'') (n : CoefMap (RingHom.id R') F' F'')
    (h1 : Function.Bijective n.pull1) (h2 : Function.Bijective n.pull2) (a b : H1 F) :
    (LinearEquiv.ofBijective n.pull2 h2).symm (m.pull2 (cup F a b)) =
      cup F' ((LinearEquiv.ofBijective n.pull1 h1).symm (m.pull1 a))
        ((LinearEquiv.ofBijective n.pull1 h1).symm (m.pull1 b)) := by
  have back : ∀ x, n.pull1 ((LinearEquiv.ofBijective n.pull1 h1).symm x) = x := fun x =>
    (LinearEquiv.ofBijective n.pull1 h1).apply_symm_apply x
  apply (LinearEquiv.ofBijective n.pull2 h2).injective
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply, n.pullCohomologyTwo_cup, back, back, m.pullCohomologyTwo_cup]

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : AlgebraicGeometry.Scheme}
  {s : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} {s' : X' ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R'} {σ : R →+* R'}
  {φ : X' ⟶ X}

theorem pullHO2_cup (h : φ ≫ s = s' ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) (a b : GlobalTheory.CechDR.HO1 s) :
    GlobalTheory.AbCoh.pullHO2 h (cup _ a b) = cup _ (GlobalTheory.CechDR.pullHO1 h a) (GlobalTheory.CechDR.pullHO1 h b) := by
  unfold GlobalTheory.AbCoh.pullHO2 GlobalTheory.CechDR.pullHO1 GlobalTheory.CechDR.pairResEquivO
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact pull_cup_of_bijective _ _ _ _ a b

theorem main : ∀ (R R' : Type) [inst : CommRing R] [inst_1 : CommRing R'] (X X' : AlgebraicGeometry.Scheme) (s : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (s' : X' ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : CategoryTheory.CategoryStruct.comp φ s = CategoryTheory.CategoryStruct.comp s' (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ)), Function.Surjective (⇑(GlobalTheory.CechDR.pullHO1 h) : GlobalTheory.CechDR.HO1 s → GlobalTheory.CechDR.HO1 s') → GlobalTheory.AbCoh.WedgeO (GlobalTheory.CechDR.OAff s') → Function.Surjective (⇑(GlobalTheory.AbCoh.pullHO2 h) : GlobalTheory.AbCoh.HO2 s → GlobalTheory.AbCoh.HO2 s') := by
  intro R R' _ _ X X' s s' σ φ h hsurj hwedge
  obtain ⟨e, he⟩ := hwedge

  have key : ∀ x, ∀ r : R', ∃ z, GlobalTheory.AbCoh.pullHO2 h z = e (r • x) := by
    intro x
    have hx : x ∈ Submodule.span R' (Set.range (exteriorPower.ιMulti R' 2)) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      intro r
      obtain ⟨a, ha⟩ := hsurj (r • v 0)
      obtain ⟨b, hb⟩ := hsurj (v 1)
      refine ⟨cup _ a b, ?_⟩
      have hv : r • exteriorPower.ιMulti R' 2 v = exteriorPower.ιMulti R' 2 ![r • v 0, v 1] := by
        have hupd : (![r • v 0, v 1] : Fin 2 → _) = Function.update v 0 (r • v 0) := by
          funext i
          fin_cases i <;> simp
        rw [hupd, AlternatingMap.map_update_smul, Function.update_eq_self]
      rw [pullHO2_cup, ha, hb, hv, he]
    | zero =>
      intro r
      exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro r
      obtain ⟨z₁, h₁⟩ := hx r
      obtain ⟨z₂, h₂⟩ := hy r
      exact ⟨z₁ + z₂, by rw [map_add (f := _), h₁, h₂, smul_add, map_add (f := _)]⟩
    | smul c x _ hx =>
      intro r
      obtain ⟨z, hz⟩ := hx (r * c)
      exact ⟨z, by rw [hz, smul_smul]⟩
  intro y
  obtain ⟨z, hz⟩ := key (e.symm y) 1
  exact ⟨z, by rw [hz, one_smul, LinearEquiv.apply_symm_apply]⟩

end GlobalTheory.PullbackCupProduct
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem bijective_of_split_of_FP : ∀ (R : Type) [CommRing R] (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ), FP R M n → FP R N n → ∀ (f : M →ₗ[R] N) (r : N →ₗ[R] M), (∀ x, r (f x) = x) → Function.Bijective f := by
  intro R _ M N _ _ _ _ n hM hN f r hrf
  obtain ⟨hMf, hMp, hMr⟩ := hM
  obtain ⟨hNf, hNp, hNr⟩ := hN
  have hinj : Function.Injective f := fun a b h => by
    have := congrArg r h; rwa [hrf, hrf] at this
  let K := LinearMap.ker r
  let π : N →ₗ[R] K := LinearMap.codRestrict K (LinearMap.id - f ∘ₗ r) (fun x => by
    show r (x - f (r x)) = 0
    simp [hrf])
  have hπ : ∀ k : K, π (k : N) = k := fun k => by
    ext; simp [π, LinearMap.mem_ker.1 k.2]
  haveI : Module.Finite R K := Module.Finite.of_surjective π (fun k => ⟨k, hπ k⟩)
  haveI : Module.Projective R K := Module.Projective.of_split K.subtype π (by ext k; simp [hπ])
  let e : N ≃ₗ[R] M × K :=
    { toFun := fun x => (r x, π x)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp
      invFun := fun p => f p.1 + (p.2 : N)
      left_inv := fun x => by simp [π]
      right_inv := fun p => by
        obtain ⟨m, k⟩ := p
        have hk : r (k : N) = 0 := k.2
        ext
        · simp [hrf, hk]
        · simp [π, hrf, hk] }
  have hK : Module.rankAtStalk (R := R) K = 0 := by
    have h1 := Module.rankAtStalk_eq_of_equiv e
    rw [Module.rankAtStalk_prod] at h1
    funext p
    have h2 := congrFun h1 p
    simp only [Pi.add_apply, hMr p, hNr p] at h2
    simp only [Pi.zero_apply]; omega
  haveI : Subsingleton K := Module.rankAtStalk_eq_zero_iff_subsingleton.1 hK
  refine ⟨hinj, fun y => ⟨r y, ?_⟩⟩
  have : π y = 0 := Subsingleton.elim _ _
  have h3 := congrArg Subtype.val this
  simp [π, sub_eq_zero] at h3
  exact h3.symm

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem hasFrame_of_isBaseChange : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∀ (W : Type) [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Projective R W] (j : W →ₗ[R] Glob1 F), (∀ T : C, ∃ e : W →ₗ[R] Ω[F.obj T⁄R], (∀ w, e w = (j w).1 T) ∧ IsBaseChange (F.obj T) e) → HasFrame F := by
  intro R _ C _ F W _ _ _ _ j h
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin' R W
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property v (LinearMap.id) hv
  have hw : ∀ x : W, x = ∑ i, σ x i • v (Pi.single i 1) := by
    intro x
    have := LinearMap.congr_fun hσ x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
    conv_lhs => rw [← this]
    conv_lhs => rw [show σ x = ∑ i, σ x i • Pi.single i (1 : R) from by
      ext k; simp [Finset.sum_apply, Pi.single_apply]]

    simp [map_sum, map_smul]
  choose e he hb using h
  let l : Fin n → W →ₗ[R] R := fun i ↦ LinearMap.proj i ∘ₗ σ
  let δ : Fin n → ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T :=
    fun i T ↦ (hb T).lift (Algebra.linearMap R (F.obj T) ∘ₗ l i)
  have hδ : ∀ i T (x : W), δ i T (e T x) = algebraMap R (F.obj T) (σ x i) := by
    intro i T x
    exact (hb T).lift_eq _ x
  refine ⟨n, ⟨⟨fun i ↦ j (v (Pi.single i 1)), δ, ?_, ?_⟩⟩⟩
  · intro i T T' φ ω
    refine (hb T).inductionOn ω ?_ ?_ ?_
    · intro x
      have h1 : p1 F φ (e T x) = e T' x := by
        rw [he T x, he T' x]; exact ((j x).2 φ).symm
      rw [h1, hδ, hδ]
      exact ((mp F φ).commutes _).symm
    · intro s ω hω
      rw [oneFormsMapOfFunctorMorphism_smul, LinearMap.map_smul, LinearMap.map_smul, hω, smul_eq_mul, smul_eq_mul, map_mul]
    · intro a b ha hb'
      rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb', map_add (f := _)]
  · intro T ω
    refine (hb T).inductionOn ω ?_ ?_ ?_
    · intro x
      simp_rw [hδ, ← he T, algebraMap_smul]
      conv_lhs => rw [hw x]

      rw [map_sum]; simp_rw [map_smul]
    · intro s ω hω
      conv_lhs => rw [hω]
      simp_rw [LinearMap.map_smul, Finset.smul_sum, smul_eq_mul, mul_smul]
    · intro a b ha hb'
      conv_lhs => rw [ha, hb']
      simp_rw [map_add (f := _), add_smul, Finset.sum_add_distrib]

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem dRel_of_frame_exists (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) :
    HasFrame F → ∀ x : GlobalTheory.CatCoh.H1 F, ∃ (n : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F), DRel F x y w := by
  rintro ⟨n, ⟨fr⟩⟩ x
  obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F x
  let g : Fin n → Z1 F := fun i ↦ ⟨fun T T' φ ↦ fr.δ i T' (D R (F.obj T') (f.1 T T' φ)), by
    intro T T' T'' φ ψ
    simp only
    rw [Z1.comp f φ ψ, map_add (f := _), map_add (f := _), ← p1_D, fr.nat]⟩
  refine ⟨n, fun i ↦ GlobalTheory.CatCoh.H1.mk F (g i), fr.w, f, g, 0, rfl, fun _ ↦ rfl, ?_⟩
  intro T T' φ
  simp only [Pi.zero_apply, map_zero, sub_zero, add_zero]
  exact fr.sum T' _

end GlobalTheory.AbCoh
end
