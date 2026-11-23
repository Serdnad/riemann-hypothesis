module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle084
public import Mathlib.Algebra.Central.Defs
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import GroundTheory.Brauer.TensorSimple
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceBlocks
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Lemmata.MiscLemmasM.Imports
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle035
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Finset.Preimage

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub.Local

theorem adjoin_mem_of_away {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A']
    [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R']
    [IsLocalization.Away (algebraMap R A g) A'] (T : Set A) (b : A)
    (hb : algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T)) :
    ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.adjoin_mem_of_away_localization' <;> assumption

theorem mem_gen_of_local (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    (V W : X.Opens) (T : Set (F.obj (op V))) (b : F.obj (op W))
    (H : ∀ x ∈ W ⊓ V, ∃ D : X.Opens, IsAffineOpen D ∧ x ∈ D ∧ ∃ (hW : D ≤ W) (hV : D ≤ V),
      (F.map (homOfLE hW).op).hom b ∈ gen F α hV T)
    (W' : X.Opens) (hW' : IsAffineOpen W') (hW : W' ≤ W) (hV : W' ≤ V) :
    (F.map (homOfLE hW).op).hom b ∈ gen F α hV T := by
  classical
  let _ : Algebra Γ(X, W') (F.obj (op W')) := (α.app (op W')).hom.toAlgebra
  have comp : ∀ {U₁ U₂ U₃ : X.Opens} (h₁₂ : U₂ ≤ U₁) (h₂₃ : U₃ ≤ U₂) (y : F.obj (op U₁)),
      (F.map (homOfLE h₂₃).op).hom ((F.map (homOfLE h₁₂).op).hom y) =
        (F.map (homOfLE (h₂₃.trans h₁₂)).op).hom y := by
    intro U₁ U₂ U₃ h₁₂ h₂₃ y
    show (F.map (homOfLE h₁₂).op ≫ F.map (homOfLE h₂₃).op).hom y = _
    rw [← F.map_comp]
    rfl
  let b' := (F.map (homOfLE hW).op).hom b
  let T' : Set (F.obj (op W')) := (F.map (homOfLE hV).op).hom '' T
  let S := Algebra.adjoin Γ(X, W') T'
  let I : Ideal Γ(X, W') :=
    (Subalgebra.toSubmodule S).comap (LinearMap.toSpanSingleton Γ(X, W') (F.obj (op W')) b')
  have hI : ∀ r, r ∈ I ↔ (α.app (op W')).hom r * b' ∈ S := fun r => by
    simp only [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Subalgebra.mem_toSubmodule,
      Algebra.smul_def]
    rfl
  have key : ∀ (D : X.Opens) (f : Γ(X, W')) (hfD : X.basicOpen f ≤ D) (hDW : D ≤ W) (hDV : D ≤ V),
      (F.map (homOfLE hDW).op).hom b ∈ gen F α hDV T → f ∈ I.radical := by
    intro D f hfD hDW hDV hbD
    let _ : Algebra Γ(X, X.basicOpen f) (F.obj (op (X.basicOpen f))) :=
      (α.app (op (X.basicOpen f))).hom.toAlgebra
    let _ : Algebra (F.obj (op W')) (F.obj (op (X.basicOpen f))) :=
      (F.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    let _ : Algebra Γ(X, W') (F.obj (op (X.basicOpen f))) :=
      ((F.map (homOfLE (X.basicOpen_le f)).op).hom.comp (α.app (op W')).hom).toAlgebra
    have : IsScalarTower Γ(X, W') (F.obj (op W')) (F.obj (op (X.basicOpen f))) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have : IsScalarTower Γ(X, W') Γ(X, X.basicOpen f) (F.obj (op (X.basicOpen f))) :=
      IsScalarTower.of_algebraMap_eq (fun x => by
        have h := congrArg (fun φ => φ.hom x) (α.naturality (homOfLE (X.basicOpen_le f)).op)
        exact h.symm)
    have : IsLocalization.Away f Γ(X, X.basicOpen f) := hW'.isLocalization_basicOpen f
    have : IsLocalization.Away (algebraMap Γ(X, W') (F.obj (op W')) f)
        (F.obj (op (X.basicOpen f))) := isLocalizationAway F α hα hW' f
    have hres := res_mem_gen_of_mem F α hDV hfD T hbD
    rw [gen_eq_adjoin] at hres
    have hb'' : algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) b' ∈
        Algebra.adjoin Γ(X, X.basicOpen f)
          (algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) '' T') := by
      have e1 : algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) b' =
          (F.map (homOfLE hfD).op).hom ((F.map (homOfLE hDW).op).hom b) :=
        (comp hW (X.basicOpen_le f) b).trans (comp hDW hfD b).symm
      have e2 : algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) '' T' =
          (F.map (homOfLE (hfD.trans hDV)).op).hom '' T := by
        simp only [T', Set.image_image]
        exact Set.image_congr (fun y _ => comp hV (X.basicOpen_le f) y)
      rw [e1, e2]
      exact hres
    obtain ⟨m, hm⟩ := adjoin_mem_of_away f T' b' hb''
    exact ⟨m, (hI _).mpr (by rw [map_pow]; exact hm)⟩
  have cover : W' ≤ ⨆ f : (I.radical : Set Γ(X, W')), X.basicOpen f.1 := by
    intro x hx
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨D, hD, hxD, hDW, hDV, hbD⟩ := H x (by exact ⟨hW hx, hV hx⟩)
    obtain ⟨f, hfD, hxf⟩ := hW'.exists_basicOpen_le (V := D) ⟨x, hxD⟩ hx
    exact ⟨⟨f, key D f hfD hDW hDV hbD⟩, hxf⟩
  have htop : I = ⊤ := by
    rw [← Ideal.radical_eq_top, ← Ideal.span_eq I.radical]
    exact (hW'.self_le_iSup_basicOpen_iff).mp cover
  have h1 : (1 : Γ(X, W')) ∈ I := htop ▸ Submodule.mem_top
  rw [hI, map_one, one_mul] at h1
  rw [gen_eq_adjoin]
  exact h1

end GlobalTheory.QcSub.Local
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

set_option autoImplicit false

namespace GlobalTheory.HilbGlue

theorem idealSheaf_ext_of_openImmersions {P : Scheme.{0}} {ι : Type*} {X : ι → Scheme.{0}}
    (f : ∀ i, X i ⟶ P) [∀ i, IsOpenImmersion (f i)] (hf : ∀ x : P, ∃ i y, f i y = x)
    (I J : P.IdealSheafData) (h : ∀ i, I.comap (f i) = J.comap (f i)) : I = J := by
  apply GlobalTheory.HilbAff.idealSheafData_ext_of_openCover <;> assumption

end GlobalTheory.HilbGlue

theorem GlobalTheory.HilbGlue.HPt.ext_openCover : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x x' : GlobalTheory.HilbGlue.HPt z r Y), (∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x = GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x') → x = x' := by
  intro S Z z r Y 𝒰 x x' e
  obtain ⟨g, I⟩ := x
  obtain ⟨g', I'⟩ := x'
  obtain rfl : g = g' := 𝒰.hom_ext _ _ fun i => congrArg Sigma.fst (e i)
  rw [HPt.mk_eq_mk_iff]
  have hP : ∀ i : 𝒰.I₀, IsPullback (pullback.snd z (𝒰.f i ≫ g)) (bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) (𝒰.f i)
      (pullback.snd z g) := fun i => (isPullback_bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl).flip
  haveI : ∀ i : 𝒰.I₀, IsOpenImmersion (bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hP i) inferInstance
  refine idealSheaf_ext_of_openImmersions (ι := 𝒰.I₀) (X := fun i => pullback z (𝒰.f i ≫ g)) (fun i => bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) ?_ I.1 I'.1 fun i => ?_
  · intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (pullback.snd z g x)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd z g)
      (g := 𝒰.f i) x y hy.symm
    refine ⟨i, (isPullback_bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl).isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw]
  · have := (HPt.mk_eq_mk_iff _ _).1 (e i)
    exact this
end

section

namespace GlobalTheory.PositiveFormRecursion

theorem step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have h1 : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
  have h2 : (3/2 : ℝ) ≤ ‖w + 1‖ := by
    have e : (2 : ℂ) = (w + 1) - (w - 1) := by ring
    have h3 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
      rw [e]; exact norm_sub_le _ _
    have h4 : ‖(2 : ℂ)‖ = 2 := by norm_num
    linarith
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (w - 1)]

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ (2 : ℕ) ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  apply GlobalTheory.IterativeScalingBound.main <;> assumption

end GlobalTheory.PositiveFormRecursion
end

section

universe u v

namespace GlobalTheory.CompanionTheory.BurnsideU

theorem mem_of_irred {K : Type u} {V : Type v} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (hirr : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  apply GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> assumption

theorem burnside_surj_of_irred {A : Type u} {V : Type v} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V)
    (hirr : ∀ W : Submodule ℂ V, (∀ h, ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ :=
    by
    intro f
    have hf : f ∈ ρ.range :=
      mem_of_irred ρ.range (fun W hW => hirr W fun h w hw => hW (ρ h) ⟨h, rfl⟩ w hw) f
    obtain ⟨h, rfl⟩ := (AlgHom.mem_range ρ).mp hf
    exact ⟨h, rfl⟩

end GlobalTheory.CompanionTheory.BurnsideU
end

section

open scoped TensorProduct

namespace GlobalTheory.CsaCharpoly
open Polynomial

theorem injective_of_isSimpleRing {R S : Type} [Ring R] [IsSimpleRing R] [Ring S] [Nontrivial S]
    (f : R →+* S) : Function.Injective f := by
  rcases eq_bot_or_eq_top (TwoSidedIdeal.ker f) with h | h
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ TwoSidedIdeal.ker f := (TwoSidedIdeal.mem_ker f).2 hx
    rw [h] at this
    simpa using this
  · exfalso
    have : (1 : R) ∈ TwoSidedIdeal.ker f := by rw [h]; trivial
    rw [TwoSidedIdeal.mem_ker, map_one] at this
    exact one_ne_zero this

theorem natDegree_minpoly_le_one_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  apply GlobalTheory.DescCoeff.natDegree_minpoly_le_one_tmul <;> assumption

end GlobalTheory.CsaCharpoly

namespace GlobalTheory
open Polynomial

theorem charpoly_algHom_eq_map_minpoly : ∀ (F L C : Type) [Field F] [Field L] [Algebra F L] [Ring C]
    [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ),
    Module.finrank F C = n ^ 2 → ∀ (ι : C →ₐ[F] Matrix (Fin n) (Fin n) L) (y : C),
    (minpoly F y).natDegree = n → (ι y).charpoly = (minpoly F y).map (algebraMap F L) := by
  intro F L C _ _ _ _ _ _ _ _ n _ ι a hdeg
  have ha : IsIntegral F a := IsIntegral.of_finite F a
  have hn : 0 < n := hdeg ▸ minpoly.natDegree_pos ha
  haveI : NeZero n := ⟨hn.ne'⟩
  let g : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ι (fun l y ↦ Algebra.commute_algebraMap_left l _)
  haveI : IsSimpleRing (L ⊗[F] C) := GroundTheory.Brauer.isSimpleRing_tensorProduct_of_right
  have hg : Function.Injective g := GlobalTheory.CsaCharpoly.injective_of_isSimpleRing g.toRingHom
  have eg : g ((1 : L) ⊗ₜ a) = ι a := by
    simp only [g]; erw [Algebra.TensorProduct.lift_tmul]; simp
  have hyi : IsIntegral L ((1 : L) ⊗ₜ[F] a) := IsIntegral.of_finite L _
  have hxi : IsIntegral L (ι a) := IsIntegral.of_finite L _
  have hmin : minpoly L (ι a) = minpoly L ((1 : L) ⊗ₜ[F] a) := by
    rw [← eg]; exact minpoly.algHom_eq g hg _
  have hge : n ≤ (minpoly L (ι a)).natDegree := by
    rw [hmin, ← hdeg]; exact GlobalTheory.CsaCharpoly.natDegree_minpoly_le_one_tmul L a hyi
  have hdvd : minpoly L (ι a) ∣ (minpoly F a).map (algebraMap F L) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hmonic : ((minpoly F a).map (algebraMap F L)).Monic := (minpoly.monic ha).map _
  have hdm : ((minpoly F a).map (algebraMap F L)).natDegree = n := by rw [natDegree_map, hdeg]
  have e1 : (minpoly F a).map (algebraMap F L) = minpoly L (ι a) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) hmonic hdvd (by rw [hdm]; exact hge)
  have e2 : (ι a).charpoly = minpoly L (ι a) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) (Matrix.charpoly_monic _)
      (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hge)
  rw [e2, e1]

end GlobalTheory
end

section

namespace GlobalTheory.PowerTwoNormLowerBound

theorem norm_pow_two_pow_sub_one_ge {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < (1 / 2 : ℝ)) :
    ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  apply GlobalTheory.IterationConvergence.iter <;> assumption

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 : (1 / 2 : ℝ) < (3 / 2 : ℝ) ^ k * ‖z - 1‖ := (div_lt_iff₀ hpos).mp hk
  have h2 := norm_pow_two_pow_sub_one_ge h k
  have h3 := h (2 ^ k)
  linarith

end GlobalTheory.PowerTwoNormLowerBound
end

section

open scoped BigOperators

namespace GlobalTheory
namespace OrbitFibre

open MulAction Function

theorem finsum_sigma_iter {ι : Type} {κ : ι → Type} (f : (Σ i, κ i) → ℂ)
    (hf : (support f).Finite) : ∑ᶠ p, f p = ∑ᶠ i, ∑ᶠ k, f ⟨i, k⟩ := by
  apply UpperTheory.V.Z.Sym.Tf.finsum_sig <;> assumption

variable {Γ A B J : Type} [Group Γ] [MulAction Γ A] [MulAction Γ B]


end OrbitFibre

end GlobalTheory
end

section

namespace GlobalTheory.UnitNormRealPartBound

lemma norm_eq_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) : ‖z‖ = 1 := by
  have hup : ∀ n : ℕ, ‖z‖ ^ n < 3 / 2 := fun n => by
    have := h n
    calc ‖z‖ ^ n = ‖(z ^ n - 1) + 1‖ := by rw [sub_add_cancel, norm_pow]
      _ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ < 3 / 2 := by rw [norm_one]; linarith
  have hlo : ∀ n : ℕ, 1 / 2 < ‖z‖ ^ n := fun n => by
    have := h n
    have h2 : ‖(1 : ℂ)‖ ≤ ‖z ^ n - 1‖ + ‖z ^ n‖ := by
      calc ‖(1 : ℂ)‖ = ‖-(z ^ n - 1) + z ^ n‖ := by ring_nf
        _ ≤ ‖-(z ^ n - 1)‖ + ‖z ^ n‖ := norm_add_le _ _
        _ = ‖z ^ n - 1‖ + ‖z ^ n‖ := by rw [norm_neg]
    rw [norm_one, norm_pow] at h2
    linarith
  rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) h1
    linarith [hlo n]
  · exact h1
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 / 2 : ℝ) h1
    linarith [hup n]

lemma re_gt {w : ℂ} (hw : ‖w‖ = 1) (h : ‖w - 1‖ < 1 / 2) : 7 / 8 < w.re := by
  have h1 : ‖w - 1‖ ^ 2 < 1 / 4 := by nlinarith [norm_nonneg (w - 1)]
  have h2 : ‖w‖ ^ 2 = 1 := by rw [hw]; norm_num
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h1 h2
  simp at h1
  nlinarith

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  apply Bl.SecondBlockLemmaN.goal1 <;> assumption

end GlobalTheory.UnitNormRealPartBound
end

section

namespace GlobalTheory.InductiveNormBound

theorem step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w^2 - 1‖ := by
  have e : w^2 - 1 = (w - 1) * ((w - 1) + 2) := by ring
  rw [e, norm_mul]
  have h2 : (3/2 : ℝ) ≤ ‖(w - 1) + 2‖ := by
    have h3 := norm_sub_le ((w - 1) + 2) (w - 1)
    have h4 : (w - 1) + 2 - (w - 1) = (2:ℂ) := by ring
    rw [h4] at h3
    have : ‖(2:ℂ)‖ = 2 := by simp
    linarith
  have h0 := norm_nonneg (w - 1)
  nlinarith

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  apply Bl.SecondBlockLemmaN.goal1 <;> assumption

end GlobalTheory.InductiveNormBound
end

section

open Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem schwartz_dense_hasCompactSupport :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    Dense {f : SchwartzMap V ℂ | HasCompactSupport (f : V → ℂ)} := by
  intro V _ _ _
  exact SchwartzMap.dense_hasCompactSupport

end GlobalTheory
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity

noncomputable section
namespace GlobalTheory.HermitianPreEigenvalues
variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

def mulR (a : S → O) (N : ℕ) (r : RS a) : (Fin N → RS a) →ₗ[O] (Fin N → RS a) :=
  (LinearMap.lsmul (RS a) (Fin N → RS a) r).restrictScalars O

def preEig (a : S → O) {N : ℕ} (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) :
    Submodule O (Fin N → RS a) :=
  (Fil.restrictScalars O).comap (mulR a N (lin a τ))

def filKer (a : S → O) {N : ℕ} (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) :
    Submodule O (Fin N → RS a) :=
  Fil.restrictScalars O ⊓ LinearMap.ker (mulR a N (cofac a τ))

end GlobalTheory.HermitianPreEigenvalues
end
end
