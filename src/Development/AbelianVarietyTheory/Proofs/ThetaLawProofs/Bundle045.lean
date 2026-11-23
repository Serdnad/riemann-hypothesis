module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle128
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle019
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle043
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
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
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle002
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

theorem exists_finset_lbIso_adjoin {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    {B : Scheme.{0}} (pB : B ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB] (M N : LB B)
    (hM : M.IsLB) (hN : N.IsLB)
    (H : LBIso (M.pull (pullback.fst pB (spMap (algebraMap k A))))
      (N.pull (pullback.fst pB (spMap (algebraMap k A))))) :
    ∃ s : Finset A,
      LBIso (M.pull (pullback.fst pB (spMap (algebraMap k (Algebra.adjoin k (s : Set A))))))
        (N.pull (pullback.fst pB (spMap (algebraMap k (Algebra.adjoin k (s : Set A)))))) := by
  apply GlobalTheory.GenericLB.exists_finset_lbIso <;> assumption

theorem lbIso_descends_to_subring_containing_finset :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (M N : LB X₀), IsPullback π f f₀ (spMap R₀.subtype) → M.IsLB → N.IsLB → LBIso (M.pull π) (N.pull π) → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → LBIso (M.pull π₁) (N.pull π₁) := by
  intro S _ R₀ X X₀ f f₀ π _ _ M N hp hM hN H
  have same : ∀ {Y Y' : Scheme.{0}} (a : Y ⟶ X₀) (j : Y' ⟶ Y) (a' : Y' ⟶ X₀), a' = j ≫ a →
      LBIso (M.pull a) (N.pull a) → LBIso (M.pull a') (N.pull a') := fun a j a' e h =>
    LBIso.chartPull (chartPullSame M _ _ _ j fun _ => e) (chartPullSame N _ _ _ j fun _ => e) h
  have hp' : IsPullback π f f₀ (spMap (algebraMap R₀ S)) := hp
  have H₁ := same π hp'.isoPullback.inv (pullback.fst f₀ (spMap (algebraMap R₀ S)))
    (IsPullback.isoPullback_inv_fst hp').symm H
  obtain ⟨s, H₂⟩ := exists_finset_lbIso_adjoin f₀ M N hM hN H₁
  refine ⟨s, fun R₁ h hs X₁ f₁ π₁ hp₁ ↦ ?_⟩
  have hle : (Algebra.adjoin R₀ (s : Set S)).toSubring ≤ R₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h r.2
    | add x y _ _ hx hy => exact R₁.add_mem hx hy
    | mul x y _ _ hx hy => exact R₁.mul_mem hx hy
  let g : Algebra.adjoin R₀ (s : Set S) →+* R₁ := Subring.inclusion hle
  have hg : spMap g ≫ spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))) =
      spMap (Subring.inclusion h) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let m : X₁ ⟶ pullback f₀ (spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S)))) :=
    pullback.lift π₁ (f₁ ≫ spMap g) (by rw [Category.assoc, hg, hp₁.w])
  exact same _ m π₁ (pullback.lift_fst _ _ _).symm H₂

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory.KeyKa

theorem secCube_tw_exactAt_of_veryAmpleBy : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ p, (cubeComplex (secCube f (tw M H t) (fun i => Out.nonzeroLocus (s i)))).ExactAt p := by
  intro R _ _ Y f H m s M hH hM hv
  obtain ⟨N, _, _, _, _, 𝒩, _, _, hfin, hφ⟩ :=
    GlobalTheory.AbLaw.exists_finite_graded_module_secCube R Y f H m s M hH hM hv
  obtain ⟨n₀, hn⟩ := GlobalTheory.cubeComplex_grCube_exactAt_of_finite (Fin (m + 1)) R N 𝒩 hfin
  refine ⟨n₀, fun t ht p => ?_⟩
  have h01 := secCube_exactAt_zero_and_one R Y f (tw M H t) (Fin (m + 1))
    (fun i => Out.nonzeroLocus (s i)) hv.1
  match p with
  | 0 => exact h01.1
  | 1 => exact h01.2
  | p + 2 =>
    obtain ⟨φ, hb⟩ := hφ t
    have := isIso_cechComplexMap φ hb
    rw [← cechComplex_exactAt_succ_iff_cube]
    exact ((cechComplex_exactAt_succ_iff_cube _ p).2 (hn t ht (p + 2))).of_iso
      (asIso (cechComplexMap φ))

end GlobalTheory.KeyKa
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_thetaKeyDatum_known_value_rat : Out.Laws → ThetaUnifAV → ∀ g : ℕ, 1 ≤ g → ∃ y : KeyIn ℚ, y.P.g = g ∧ Known ℚ y := by
  first | exact @GlobalTheory.KeyFam.exists_known_rat | exact GlobalTheory.KeyFam.exists_known_rat | (intros; apply GlobalTheory.KeyFam.exists_known_rat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_thetaKeyFamily_universal_frames : Out.Laws → ∀ (k S : Type) [Field k] [CommRing S] [Algebra k S] (y : KeyIn S) (x : KeyIn ℂ) (s : S →+* ℂ) (φ : x.P.A.left ⟶ y.P.A.left) (s₀ : S →ₐ[k] k), GeomInt k S → PolPB x.P y.P (spMap s) φ → ∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S') (j : S →ₐ[k] S') (y' : KeyIn S') (s' : S' →+* ℂ) (s₀' : S' →ₐ[k] k) (ψ : y'.P.A.left ⟶ y.P.A.left), GeomInt k S' ∧ KeyPB x y' s' ∧ PolPB y'.P y.P (spMap j.toRingHom) ψ ∧ s₀'.comp j = s₀ := by
  first | exact @GlobalTheory.KeyFam.exists_univ_frames | exact GlobalTheory.KeyFam.exists_univ_frames | (intros; apply GlobalTheory.KeyFam.exists_univ_frames <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.exists_l2Val_field_or_dvr_split_kernel : Out.Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (m ^ x.P.g) → RR x m) (ξ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x), IsUnit (m : R) → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → IsBasis x b → (∀ I I', I ≠ I' → ∀ p : Sp R, ∃ r, (ξ I r).left p ≠ (ξ I' r).left p) → (∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1) → ∃ lam, IsSquareDeterminantComparison x m al b lam := by
  first | exact @GlobalTheory.SimilLocal.exists_l2Val | exact GlobalTheory.SimilLocal.exists_l2Val | (intros; apply GlobalTheory.SimilLocal.exists_l2Val <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.thetaFrameValueKnown_of_polarizedPullback : Out.Laws → ∀ (K : Type) [Field K] (y y' : KeyIn K) (φ : y'.P.A.left ⟶ y.P.A.left), PolPB y'.P y.P (𝟙 _) φ → Known K y → Known K y' := by
  first | exact @GlobalTheory.KnownScale.known_of_polPB | exact GlobalTheory.KnownScale.known_of_polPB | (intros; apply GlobalTheory.KnownScale.known_of_polPB <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem ringKrullDim_localization_quotient_le {R : Type} [CommRing R] {k : ℕ} (f : Fin k → R) (m : Ideal R)
    [m.IsPrime] :
    ringKrullDim (Localization.AtPrime m ⧸
        Ideal.span (Set.range fun j => algebraMap R (Localization.AtPrime m) (f j))) ≤
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Set.range f) : Set (PrimeSpectrum R)) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have h₁ := (PrimeSpectrum.localization_comap_isInducing (R := R) (Localization.AtPrime m) m.primeCompl).comp
    (PrimeSpectrum.isEmbedding_comap_of_surjective _ (Ideal.Quotient.mk
      (Ideal.span (Set.range fun j => algebraMap R (Localization.AtPrime m) (f j))))
      Ideal.Quotient.mk_surjective).isInducing
  refine (h₁.codRestrict (s := PrimeSpectrum.zeroLocus (Set.range f)) fun p => ?_).topologicalKrullDim_le
  rintro _ ⟨j, rfl⟩
  change Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime m) (f j)) ∈ p.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self (f := fun j => algebraMap R (Localization.AtPrime m) (f j)) j))]
  exact p.asIdeal.zero_mem

theorem ofList_take_ofFn {R : Type} [CommRing R] {g : ℕ} (f : Fin g → R) (i : ℕ) :
    Ideal.ofList ((List.ofFn f).take i) = Ideal.span (f '' {j | j.val < i}) := by
  unfold Ideal.ofList
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, List.mem_take_iff_getElem, List.length_ofFn, List.getElem_ofFn, Set.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, by omega⟩, by simp only; omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by have := j.2; omega, rfl⟩

theorem isWeaklyRegular_of_dim_zeroLocus {R : Type} [CommRing R] {g : ℕ} (f : Fin g → R)
    (hreg : ∀ (m : Ideal R) [m.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = g)
    (hdim : ∀ (k : ℕ) (hk : k ≤ g),
      (PrimeSpectrum.zeroLocus (Set.range fun j => f (Fin.castLE hk j)) : Set (PrimeSpectrum R)).Nonempty →
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Set.range fun j => f (Fin.castLE hk j)) :
        Set (PrimeSpectrum R)) ≤ ((g - k : ℕ) : WithBot ℕ∞)) :
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f) := by
  refine ⟨fun i hi => ?_⟩
  have hi' : i < g := by simpa using hi
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem, ofList_take_ofFn, List.getElem_ofFn]
  simp only [smul_eq_mul, Ideal.mul_top]
  intro a ha
  refine Ideal.mem_of_localization_maximal fun m hm => ?_
  have ha' := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime m)) ha
  rw [map_mul] at ha'
  by_cases hall : ∀ j : Fin g, j.val ≤ i → f j ∈ m
  · obtain ⟨h₁, h₂⟩ := hreg m
    have hk : i + 1 ≤ g := hi'
    have hd := (ringKrullDim_localization_quotient_le (fun j => f (Fin.castLE hk j)) m).trans
      (hdim (i + 1) hk ⟨⟨m, hm.isPrime⟩, by
        rintro _ ⟨j, rfl⟩
        exact hall _ (by have := j.2; simp only [Fin.val_castLE]; omega)⟩)
    have hr := GlobalTheory.isRegular_ofFn_of_ringKrullDim_quotient_add_le (Localization.AtPrime m) g (i + 1)
      (fun j => algebraMap R (Localization.AtPrime m) (f (Fin.castLE hk j))) h₂
      (fun j => (IsLocalization.AtPrime.to_map_mem_maximal_iff _ m _).2
        (hall _ (by have := j.2; simp only [Fin.val_castLE]; omega)))
      ((add_le_add_left hd _).trans (by
        rw [← Nat.cast_add, Nat.sub_add_cancel hk]))
    have h₃ := hr.toIsWeaklyRegular.regular_mod_prev i (by simp)
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem, ofList_take_ofFn, List.getElem_ofFn] at h₃
    simp only [smul_eq_mul, Ideal.mul_top] at h₃
    have e : Ideal.map (algebraMap R (Localization.AtPrime m)) (Ideal.span (f '' {j | j.val < i})) =
        Ideal.span ((fun j : Fin (i + 1) => algebraMap R (Localization.AtPrime m) (f (Fin.castLE hk j))) ''
          {j | j.val < i}) := by
      rw [Ideal.map_span]
      congr 1
      ext b
      constructor
      · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨⟨j, Nat.lt_succ_of_lt hj⟩, hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨_, ⟨Fin.castLE hk j, hj, rfl⟩, rfl⟩
    rw [e] at ha' ⊢
    exact h₃ _ ha'
  · push Not at hall
    obtain ⟨j, hj, hjm⟩ := hall
    have hu : IsUnit (algebraMap R (Localization.AtPrime m) (f j)) :=
      IsLocalization.map_units _ (⟨f j, hjm⟩ : m.primeCompl)
    rcases hj.eq_or_lt with hj | hj
    · subst hj
      exact (Ideal.unit_mul_mem_iff_mem _ hu).1 ha'
    · rw [Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_image_of_mem f (show j ∈ {j : Fin g | j.val < i} from hj)))) hu]
      trivial

theorem isWeaklyRegular_of_finZ : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n : ℕ) (s : Fin x.P.g → RR x n) (V : x.P.A.left.Opens) (c : x.P.L.ι) (h : V ≤ x.P.L.U c), 1 ≤ n → FinZ x s → IsAffineOpen V → RingTheory.Sequence.IsWeaklyRegular Γ(x.P.A.left, V) (List.ofFn fun i => resG x.P.A.left h ((s i).f c)) := by
  intro hL K _ _ x n s V c h hn hZ hV
  refine isWeaklyRegular_of_dim_zeroLocus _ (fun m _ => ?_) fun k hk hne => ?_
  · exact GlobalTheory.isRegularLocalRing_and_ringKrullDim_eq_of_polAV K x.P Γ(x.P.A.left, V) hV.fromSpec m _ inferInstance
  · let W : Set x.P.A.left := {y | ∀ j : Fin k, y ∉ Out.nonzeroLocus (s (Fin.castLE hk j))}
    have hW : IsClosed W := by
      have : W = ⋂ j : Fin k, (Out.nonzeroLocus (s (Fin.castLE hk j)) : Set x.P.A.left)ᶜ := by
        ext y; simp [W]
      rw [this]
      exact isClosed_iInter fun j => (Out.nonzeroLocus _).isOpen.isClosed_compl
    have hmem : ∀ p : (PrimeSpectrum.zeroLocus (Set.range fun j => resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) :
        Set (PrimeSpectrum Γ(x.P.A.left, V))), hV.fromSpec p.1 ∈ W := by
      intro p j hj
      have hpV : hV.fromSpec p.1 ∈ V := by
        have : hV.fromSpec p.1 ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
        rwa [hV.range_fromSpec] at this
      have h₁ := (GlobalTheory.AmpleSpan.isUnit_gs_iff (𝟙 _) _ _ (h hpV) _).1
        ((GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (s (Fin.castLE hk j)) (𝟙 _) (hV.fromSpec p.1) (k := c) (h hpV)).1 hj)
      have h₂ : hV.fromSpec p.1 ∈ x.P.A.left.basicOpen (resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) := by
        have := x.P.A.left.basicOpen_res (show Γ(x.P.A.left, x.P.L.U c) from (s (Fin.castLE hk j)).f c) (homOfLE h).op
        exact this.ge ⟨hpV, h₁⟩
      have h₃ : p.1 ∈ hV.fromSpec ⁻¹ᵁ x.P.A.left.basicOpen (resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) := h₂
      rw [hV.fromSpec_preimage_basicOpen] at h₃
      exact h₃ (p.2 ⟨j, rfl⟩)
    have hind : Topology.IsInducing fun p : (PrimeSpectrum.zeroLocus
        (Set.range fun j => resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) :
        Set (PrimeSpectrum Γ(x.P.A.left, V))) => hV.fromSpec p.1 :=
      hV.fromSpec.isOpenEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
    refine (hind.codRestrict hmem).topologicalKrullDim_le.trans ?_
    obtain ⟨p, hp⟩ := hne
    refine GlobalTheory.T.topologicalKrullDim_le_of_finite_common_zeros hL K x n (x.P.g - k) (fun j => s ⟨k + j, by have := j.2; omega⟩) W hn hW
      ⟨_, hmem ⟨p, hp⟩⟩ (Set.Finite.subset hZ ?_)
    rintro y ⟨hy₁, hy₂⟩ i
    by_cases hi : i.val < k
    · exact hy₁ ⟨i, hi⟩
    · have := hy₂ ⟨i - k, by have := i.2; omega⟩
      simp only [show k + (i.val - k) = i.val by omega] at this
      exact this

end GlobalTheory.KeyKa
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyFamOfExact

theorem keyFam_of_keyFormula : KeyFormula → KeyFam fun _ => 1 := fun h => by
  obtain ⟨κ, h1, h2, h3, h4, h5⟩ := keyFormula_iff.1 h
  exact ⟨κ, h1, h2, h3, h4, h5, GlobalTheory.KeyFamUnit.famUnit κ h2 h3,
    GlobalTheory.KeyFamHomog.famHomog_of_homog _ κ h1, GlobalTheory.T.thetaKeyRule_valuationUnit_of_functorial κ h2 h3⟩

end GlobalTheory.KeyFamOfExact
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.lineBundleIso_descends_to_subring_of_finset : ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (M N : LB X₀), IsPullback π f f₀ (spMap R₀.subtype) → M.IsLB → N.IsLB → LBIso (M.pull π) (N.pull π) → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → LBIso (M.pull π₁) (N.pull π₁) := by
  first | exact @GlobalTheory.lbIso_descends_to_subring_containing_finset | exact GlobalTheory.lbIso_descends_to_subring_containing_finset | (intros; apply GlobalTheory.lbIso_descends_to_subring_containing_finset <;> assumption)

end
end
