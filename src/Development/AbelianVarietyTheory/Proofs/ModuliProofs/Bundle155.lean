module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeDescendsAlongEtaleIsogeny
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle124
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle151
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteFlatSurjectiveMulByNAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle152
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle032
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreAmple

theorem pw_pw_natCast {X : Scheme.{0}} (H : LB X) (a b : ℕ) :
    pw (pw H a) b = pw H ((a * b : ℕ) : ℤ) := by
  rw [Nat.cast_mul]
  exact congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem triv_theta_pull {S S' : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (g : S' ⟶ S)
    (H : LB A.left) (h : Triv (Theta ((Over.pullback g).obj A) (H.pull (pullback.fst A.hom g)))) :
    Triv ((Theta A H).pull (pullback.fst (G3 A).hom g)) := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨u, hu⟩ := GlobalTheory.CubeDescent.exists_gen_comp H (pullback.fst A.hom g) _ _ t ht
  let B := (Over.pullback g).obj A
  let T : Over S' := Over.mk (pullback.snd (G3 A).hom g)
  have hG := isGrpPullback_pullback A g
  let y : Fin 3 → (T ⟶ B) := fun i => Over.homMk
    (pullback.lift (pullback.fst (G3 A).hom g ≫ (x3 A i).left) (pullback.snd (G3 A).hom g)
      (by rw [Category.assoc, Over.w, pullback.condition])) (pullback.lift_snd _ _ _)
  let r : T ⟶ G3 B := lift (y 0) (lift (y 1) (y 2))
  have hr : ∀ i, r ≫ x3 B i = y i := fun i => by fin_cases i <;> simp [r, x3]
  let U : Over.mk (T.hom ≫ g) ⟶ G3 A := Over.homMk (pullback.fst (G3 A).hom g) pullback.condition
  have key : ∀ I : Finset (Fin 3), r.left ≫ (psum B (x3 B) I).left ≫ pullback.fst A.hom g =
      pullback.fst (G3 A).hom g ≫ (psum A (x3 A) I).left := fun I => by
    have e₁ : r ≫ psum B (x3 B) I = psum B y I :=
      (psum_hom (preHom r) (x3 B) I).trans (congrArg (fun z => psum B z I) (funext hr))
    have e₂ := psum_push hG y (x3 A) U (fun i => Over.OverMorphism.ext (pullback.lift_fst _ _ _)) I
    rw [← Category.assoc, ← Over.comp_left, e₁]
    exact e₂
  refine (CubeGen.triv_pull_iff H (thφ A (x3 A)) thε _).2 ?_
  have e : (fun k => pullback.fst (G3 A).hom g ≫ thφ A (x3 A) k) =
      fun k => r.left ≫ thφ B (x3 B) k ≫ pullback.fst A.hom g := funext fun k => (key k.down).symm
  unfold CubeGen.TrivAt
  rw [e]
  exact ⟨_, DVR.pullGen_isGen _ _ _ u hu r.left⟩

theorem exists_ne_zero {X : Scheme.{0}} [Nonempty X] {N : LB X} {I : Type} (s : I → LB.Sec N)
    (h : ⨆ i, Out.nonzeroLocus (s i) = ⊤) : ∃ (σ : LB.Sec N) (k : N.ι), σ.f k ≠ 0 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx : x ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [h]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  refine ⟨s i, k, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hk
  exact hk

theorem relAmple_of_fibres : Out.Laws → ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (algebraMap O K)))) (M.pull (pullback.fst A.hom (spMap (algebraMap O K)))) → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (IsLocalRing.residue O)))) (M.pull (pullback.fst A.hom (spMap (IsLocalRing.residue O)))) → Out.RelAmple A M := by
  intro hL O K _ _ _ _ _ _ _ _ A _ hA M hM hK hk
  have isLB_pw {Y : Scheme.{0}} {H : LB Y} (hH : H.IsLB) (t : ℤ) :
      (pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hB := CubeGen.isAb_baseChange hA (spMap (algebraMap O K))
  obtain ⟨d, hd, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K _ _ (LB.isLB_pull hM _)).1 hK
  have hH := isLB_pw hM d
  have hproj : IsProjBy ((Over.pullback (spMap (algebraMap O K))).obj A).hom :=
    ⟨_, isLB_pw (LB.isLB_pull hM _) _, n, s, hs⟩
  have cK := triv_theta_pull A _ (pw M d)
    (GlobalTheory.T.theorem_of_cube_projective_abelianScheme_affineBase hL K _ hB hproj _ (LB.isLB_pull hH (pullback.fst A.hom (spMap (algebraMap O K)))))
  have s₂ : Smooth (A ⊗ A).hom := by
    change Smooth (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have p₂ : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have c₂ : GeometricallyConnected (A ⊗ A).hom := by
    change GeometricallyConnected (pullback.fst A.hom A.hom ≫ A.hom)
    exact GeometricallyConnected.comp _ _
  have s₃ : Smooth (G3 A).hom := by
    change Smooth (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom); infer_instance
  have p₃ : IsProper (G3 A).hom := by
    change IsProper (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom); infer_instance
  have c₃ : GeometricallyConnected (G3 A).hom := by
    change GeometricallyConnected (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom)
    exact GeometricallyConnected.comp _ _
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have cube : Triv (Theta A (pw M d)) :=
    GlobalTheory.T.generator_extends_from_genericFibre_valuationRing O K _ _ (G3 A).hom _ _ (IsPullback.of_hasPullback _ _) s₃ inferInstance (gi _ _ _ s₃ c₃) _
      (LB.isLB_linComb hH _ _) cK
  have ne : Nonempty ((Over.pullback (spMap (algebraMap O K))).obj A).left :=
    ⟨(η[(Over.pullback (spMap (algebraMap O K))).obj A]).left (default : PrimeSpectrum K)⟩
  have hσ : ∃ (σ : LB.Sec ((pw M d).pull (pullback.fst A.hom (spMap (algebraMap O K))))) (k : _), σ.f k ≠ 0 := by
    have := @exists_ne_zero _ ne _ _ s hs.1
    rw [GlobalTheory.TrivLocus.pull_pw]
    exact this
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨-, t, -, -, ht⟩ := GlobalTheory.T.exists_sec_nonzero_on_special_fibre_extending_smul O K _ _ A.hom _ _ (IsPullback.of_hasPullback _ _) hA.smooth
    inferInstance (gi _ _ _ hA.smooth hA.geomConnected) _ hH σ hσ
  have hu := GlobalTheory.T.exists_sections_generate_square_bundle O K A hA _ hH cube t ht
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, pw_pw_natCast] at hu
  obtain ⟨m, u, hu⟩ := hu
  have aff := GlobalTheory.T.isAffineOpen_nonzeroLocus_of_fibrewise_ample O _ A.hom M (d * 2) m u (by omega) hA.proper hM hu (fun q hq => by
    by_cases h0 : q = ⊥
    · exact ⟨K, inferInstance, algebraMap O K,
        h0 ▸ (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O K), hK⟩
    · exact ⟨_, inferInstance, IsLocalRing.residue O,
        IsLocalRing.ker_residue.trans (IsLocalRing.eq_maximalIdeal (hq.isMaximal h0)).symm, hk⟩)
  obtain ⟨e, he, hv⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw_of_affine_loci O _ A.hom _ m u (isLB_pw hM _) hu aff
  rw [pw_pw_natCast] at hv
  exact (GlobalTheory.Unif.relAmple_iff_veryAmpleBy O A M hM).2 ⟨d * 2 * e, Nat.mul_pos (by omega) he, hv⟩

end GlobalTheory.FibreAmple
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem of_local_near_veryDense (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (P : Set (Ideal R))
    (hP : ∀ (q : Ideal R) (f : R), q.IsPrime → f ∉ q → ∃ p ∈ P, p.IsPrime ∧ q ≤ p ∧ f ∉ p)
    (h : ∀ q ∈ P, ∃ f : R, f ∉ q ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Q (pullback.snd s (spMap φ))) : Q s := by
  let S : Set R := {f | ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Q (pullback.snd s (spMap φ))}
  have hS : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, hp, -, hmp, -⟩ := hP m 1 hm.isPrime ((Ideal.ne_top_iff_one m).1 hm.ne_top)
    obtain ⟨f, hf, hfS⟩ := h p hp
    exact hf (hmp (hle (Ideal.subset_span hfS)))
  have hS' : Ideal.span (Set.range (fun f : S => (f : R))) = ⊤ := by
    rw [Subtype.range_coe]; exact hS
  refine IsZariskiLocalAtTarget.of_openCover (P := Q)
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R) (fun f : S => (f : R)) hS').openCover ?_
  intro i
  exact (show S from i).2 (Localization.Away ((show S from i) : R)) (algebraMap R _)
    (IsLocalization.Away.algebraMap_isUnit _)

theorem smooth_and_geomConnected_of_veryDense : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (P : Set (Ideal R)), (∀ (q : Ideal R) (f : R), q.IsPrime → f ∉ q → ∃ p ∈ P, p.IsPrime ∧ q ≤ p ∧ f ∉ p) → IsProjOver s → Flat s → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ SmoothOfRelativeDimension g (pullback.snd s (spMap x)) ∧ GeometricallyConnected (pullback.snd s (spMap x))) → SmoothOfRelativeDimension g s ∧ GeometricallyConnected s := by
  intro R _ _ Z s g P hP hproj hflat h
  have hsm : SmoothOfRelativeDimension g s := by
    have : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} g) := HasRingHomProperty.instIsZariskiLocalAtTarget _
    refine of_local_near_veryDense (@SmoothOfRelativeDimension.{0} g) R Z s P hP ?_
    intro q hq
    obtain ⟨K, _, x, hx, h1, -⟩ := h q hq
    obtain ⟨f, hf, H⟩ := GlobalTheory.T.exists_smoothOfRelDim_of_isUnit_proper_flat R Z s g K x (projProper R Z s hproj) hflat h1
    exact ⟨f, by rw [← hx]; exact hf, H⟩
  refine ⟨hsm, ?_⟩
  have : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  refine of_local_near_veryDense (@GeometricallyConnected.{0}) R Z s P hP ?_
  intro q hq
  obtain ⟨K, _, x, hx, -, h2⟩ := h q hq
  obtain ⟨f, hf, H⟩ := GlobalTheory.T.geometricallyConnected_open_condition_smooth_projective R Z s K x hproj (SmoothOfRelativeDimension.smooth g s) h2
  exact ⟨f, by rw [← hx]; exact hf, H⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.seesaw_reduced_base_abelianScheme_of_dense_fibres : Out.GlobalFnsSt → ∀ (S₀ : Scheme.{0}) (B : Over S₀) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (S X : Scheme.{0}) [IsReduced S] (t : S ⟶ S₀) (π : X ⟶ B.left) (f : X ⟶ S) (N : LB X), IsPullback π f B.hom t → N.IsLB → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (Y : Scheme.{0}) (ρ : Y ⟶ X) (h : Y ⟶ Sp K), p ∈ Set.range x ∧ IsPullback ρ h f x ∧ ∃ c : (N.pull ρ).Gen, c.IsGen} → ∀ σ : S ⟶ X, σ ≫ f = 𝟙 S → (∃ c : (N.pull σ).Gen, c.IsGen) → ∃ c : N.Gen, c.IsGen := by
  first | exact @GlobalTheory.seesaw_reduced_of_dense | exact GlobalTheory.seesaw_reduced_of_dense | (intros; apply GlobalTheory.seesaw_reduced_of_dense <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.finite_flat_surjective_mul_by_n_abelianScheme : Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple A M → ∀ n : ℕ, 1 ≤ n → IsFinite ((𝟙 A) ^ n : A ⟶ A).left ∧ Flat ((𝟙 A) ^ n : A ⟶ A).left ∧ Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  first | exact @GlobalTheory.MulAmple.finite_flat_surjective_pow | exact GlobalTheory.MulAmple.finite_flat_surjective_pow | (intros; apply GlobalTheory.MulAmple.finite_flat_surjective_pow <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem seesaw_rigidified_of_dense :
    ∀ (R : Type) [CommRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (M N : LB A.left) (Sg : Set (Sp R)), IsAbelianScheme A → M.IsLB → Out.RelAmple A M → N.IsLB → Dense Sg → Out.Rigidified A N → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (X : Scheme.{0}) (φ : X ⟶ A.left) (π : X ⟶ Sp K), p ∈ Set.range x ∧ IsPullback φ π A.hom x ∧ ∃ t : (N.pull φ).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro R _ _ A _ M N Sg hA hM hamp hN hd hr hf
  exact GlobalTheory.seesaw_reduced_of_dense GlobalTheory.globalFns_holds (Sp R) A M hA hM hamp (Sp R) A.left (𝟙 _) (𝟙 _)
    A.hom N (IsPullback.of_horiz_isIso ⟨by simp⟩) hN (hd.mono fun p hp => hf p hp) (eSec A)
    (Over.w η[A]) hr

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem card_torsion_abelianVariety : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g N : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (N : k) ≠ 0 → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ B // x ^ N = 1} = N ^ (2 * g) :=
  fun k _ _ B _ g N hB hg hN => GlobalTheory.abMulN_holds k B g N hB hg hN

end GlobalTheory
end
