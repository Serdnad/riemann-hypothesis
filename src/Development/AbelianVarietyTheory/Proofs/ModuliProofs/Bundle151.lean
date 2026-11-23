module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeometricValuesIsoOfIdentificationDvr
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle080
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle149
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyMorphismFromVeryDenseGraphs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.theorem_of_cube_projective_abelianScheme_affineBase : Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ M : LB A.left, M.IsLB → Triv (Theta A M) := by
  first | exact @GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy | exact GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy | (intros; apply GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_geometric_values_iso_of_identification_dvr : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D D' : DegPre V) (e : IsPullDeg (RingHom.id V) D D') (F : Type) [Field F] [Algebra (FractionRing V) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N'), ∃ J : NumD.Iso N N', GeoIso ν ν' J.toIso ∧ ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D' F k) (q : N.QT k) (q' : N'.QT k), ν.QPt p q → ν'.QPt p' q' → GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition.Carries e p p' → q'.1.1.toAdd = J.e q.1.1.toAdd ∧ J.Rel q.1.2 q'.1.2 := by
  first | exact @GlobalTheory.IdentifiedValues.exists_geoIso_rel | exact GlobalTheory.IdentifiedValues.exists_geoIso_rel | (intros; apply GlobalTheory.IdentifiedValues.exists_geoIso_rel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.ZV.HilbFn

theorem exists_forms_basis {K σ : Type} [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    ∃ G : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → MvPolynomial σ K, (∀ i, (G i).IsHomogeneous e) ∧
      ∀ F : MvPolynomial σ K, F.IsHomogeneous e → ∃! a : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → K,
        F - ∑ i, a i • G i ∈ I := by
  classical
  have hQ : ∀ x, x ∈ GlobalTheory.quotPiece I e ↔
      ∃ y, y ∈ MvPolynomial.homogeneousSubmodule σ K e ∧ Ideal.Quotient.mkₐ K I y = x := by
    intro x
    rw [GlobalTheory.quotPiece_natCast, Submodule.mem_map]
    rfl
  have : Module.Finite K (GlobalTheory.quotPiece I e) := by
    rw [GlobalTheory.quotPiece_natCast]
    exact Module.Finite.map _ _
  let b := Module.finBasis K (GlobalTheory.quotPiece I e)
  have hlift : ∀ i, ∃ G : MvPolynomial σ K, G.IsHomogeneous e ∧
      Ideal.Quotient.mkₐ K I G = (b i : MvPolynomial σ K ⧸ I) := fun i =>
    (hQ _).1 (b i).2
  choose G hG hGb using hlift
  have hsum : ∀ a : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → K,
      Ideal.Quotient.mkₐ K I (∑ i, a i • G i) =
        ((∑ i, a i • b i : GlobalTheory.quotPiece I e) : MvPolynomial σ K ⧸ I) := by
    intro a

    simp only [map_sum, map_smul, hGb, Submodule.coe_sum, Submodule.coe_smul]
  refine ⟨G, hG, fun F hF => ?_⟩
  have hF' : Ideal.Quotient.mkₐ K I F ∈ GlobalTheory.quotPiece I e := (hQ _).2 ⟨F, hF, rfl⟩
  have hiff : ∀ a : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → K,
      F - ∑ i, a i • G i ∈ I ↔ (∑ i, a i • b i) = (⟨_, hF'⟩ : GlobalTheory.quotPiece I e) := by
    intro a
    rw [← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk K, hsum,
      Subtype.ext_iff, eq_comm]
  refine ⟨fun i => b.repr ⟨_, hF'⟩ i, (hiff _).2 (b.sum_repr _), fun a ha => ?_⟩
  funext i
  rw [← (hiff a).1 ha, b.repr_sum_self]

theorem dimDeg_add {K σ : Type} [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    dimDeg I e + Module.finrank K (GlobalTheory.quotPiece I e) =
      Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) := by
  classical
  let H := MvPolynomial.homogeneousSubmodule σ K e
  let f : H →ₗ[K] MvPolynomial σ K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap.comp H.subtype
  have hr : LinearMap.range f = GlobalTheory.quotPiece I e := by
    rw [GlobalTheory.quotPiece_natCast, LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker f = (I.restrictScalars K).comap H.subtype := by
    ext x
    simp [f, LinearMap.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [hr, hk] at hrk
  have hm : Module.finrank K ((I.restrictScalars K).comap H.subtype) =
      Module.finrank K ↥(H ⊓ I.restrictScalars K) := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
  unfold dimDeg
  rw [← hm, add_comm]
  exact hrk

variable {K σ : Type} [Field K] {X : Scheme.{0}}

def toPw (M : LB X) (e : ℕ) (t : (lbPow M e).Sec) : (AbLaw.pw M e).Sec where
  f := fun k => resG X (show M.U k ≤ (lbPow M e).U (fun _ => k) from
    fun _ hy => Set.mem_iInter.2 fun _ => hy) (t.f fun _ => k)
  compat := fun (i j : M.ι) => by
    have h := congrArg (resG X (show M.U i ⊓ M.U j ≤ (lbPow M e).U (fun _ => i) ⊓ (lbPow M e).U (fun _ => j) from
      inf_le_inf (fun _ hy => Set.mem_iInter.2 fun _ => hy) (fun _ hy => Set.mem_iInter.2 fun _ => hy)))
      (t.compat (fun _ => i) (fun _ => j))
    rw [map_mul] at h
    refine (AbLaw.rs_rs _ _ _).trans (((AbLaw.rs_rs _ _ _).symm.trans h).trans ?_)
    congr 1
    · have hu : res (show M.U i ⊓ M.U j ≤ (lbPow M e).U (fun _ => i) ⊓ (lbPow M e).U (fun _ => j) from
          inf_le_inf (fun _ hy => Set.mem_iInter.2 fun _ => hy) (fun _ hy => Set.mem_iInter.2 fun _ => hy))
          ((lbPow M e).g (fun _ => i) (fun _ => j)) = M.g i j ^ (e : ℤ) := by
        first
          | (change res _ (∏ _k : PUnit, _) = _
             rw [Fintype.prod_unique, map_zpow])
          | refine (congrArg (res _) (@Fintype.prod_unique PUnit _ _ _ _ _)).trans ((map_zpow _ _ _).trans ?_)
          | refine (congrArg (res _) (Fintype.prod_unique _)).trans ((map_zpow _ _ _).trans ?_)
        congr 1
        ext
        exact (AbLaw.rs_rs _ _ _).trans (AbLaw.rs_self _ _)
      exact congrArg Units.val hu
    · exact (AbLaw.rs_rs _ _ _).trans (AbLaw.rs_rs _ _ _).symm

theorem eventually_surj [Finite σ] [Nonempty σ] (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec) (hM : M.IsLB)
    (h : VAmp p M th) : ∀ᶠ e : ℕ in Filter.atTop, ∀ t : (lbPow M e).Sec, ∃ F : MvPolynomial σ K,
      F.IsHomogeneous e ∧ ∀ j, t.f j = MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) (fun i => resG X
        (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) F := by
  obtain ⟨m, ε, hε⟩ := h.exists_veryAmpleBy
  obtain ⟨t₀, ht⟩ := (AbLaw.serre_h1Zero_and_sections_polynomial).2 K X p M m (fun i => th (ε i)) hM hε
  refine Filter.eventually_atTop.2 ⟨t₀, fun e he t => ?_⟩
  obtain ⟨F, hF, hFe⟩ := ht e he (toPw M e t)
  refine ⟨MvPolynomial.rename ε F, hF.rename_isHomogeneous, fun j => ?_⟩
  have hj := hFe (j PUnit.unit)
  unfold toPw at hj
  unfold AbLaw.cst at hj
  have hrs : ∀ {U V : X.Opens} (hUV : V ≤ U), resG X hUV = AbLaw.rs X hUV := fun _ => rfl
  have hA : (lbPow M e).U j ≤ M.U (j PUnit.unit) := LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit
  have hj' := congrArg (AbLaw.rs X hA) hj
  simp only [hrs] at hj' ⊢
  erw [AbLaw.rs_rs, AbLaw.rs_self] at hj'
  rw [hj', MvPolynomial.map_eval₂Hom, MvPolynomial.eval₂_rename, MvPolynomial.coe_eval₂Hom]
  congr 1
  ext a
  simp only [RingHom.comp_apply, AbLaw.rs_rs]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra

theorem hilbertFunction_idealOf : ∀ (K σ : Type) [Field K] [Finite σ] [Nonempty σ] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec), M.IsLB → VAmp p M th → ∃ Q : Polynomial ℚ, ∀ᶠ e : ℕ in Filter.atTop, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℚ) = Q.eval (e : ℚ) ∧ dimDeg (idealOf p M th (𝟙 X)) e + r = Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) := by
  intro K σ _ _ _ X p M th hM h
  classical
  obtain ⟨hhom, -, hsec⟩ := GlobalTheory.T.homogeneous_ideal_sections_of_line_bundle_power K σ X p M th hM h
  have hI : (idealOf p M th (𝟙 X)).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K) := by
    intro i r hr
    convert hhom r hr i using 1
    exact MvPolynomial.decomposition.decompose'_apply r i
  refine ⟨GlobalTheory.idealHilbertPoly (idealOf p M th (𝟙 X)), ?_⟩
  filter_upwards [GlobalTheory.eventually_finrank_quotPiece hI, eventually_surj p M th hM h] with e he hsurj
  refine ⟨Module.finrank K (GlobalTheory.quotPiece (idealOf p M th (𝟙 X)) e), ?_, he, dimDeg_add _ e⟩
  obtain ⟨G, hG, hGu⟩ := exists_forms_basis (idealOf p M th (𝟙 X)) e
  choose s hs1 hs2 hs3 using fun i => hsec e (G i) (hG i)
  have lin : ∀ (R : Type) [CommRing R] (φ : K →+* R) (v : σ → R)
      (a : Fin (Module.finrank K (GlobalTheory.quotPiece (idealOf p M th (𝟙 X)) e)) → K),
      MvPolynomial.eval₂ φ v (∑ i, a i • G i) = ∑ i, φ (a i) * MvPolynomial.eval₂ φ v (G i) := by
    intro R _ φ v a

    rw [← MvPolynomial.coe_eval₂Hom, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
  have hsumG : ∀ a : Fin (Module.finrank K (GlobalTheory.quotPiece (idealOf p M th (𝟙 X)) e)) → K,
      (∑ i, a i • G i).IsHomogeneous e := by
    intro a
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (hG i))
  have hzero : ∀ D : MvPolynomial σ K, D.IsHomogeneous e →
      ((∀ j : (lbPow M e).ι, MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) (fun i => resG X
        (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) D = 0) ↔
        D ∈ idealOf p M th (𝟙 X)) := by
    intro D hD
    obtain ⟨τ, hτ1, hτ2, -⟩ := hsec e D hD
    rw [← hτ2]
    exact forall_congr' fun j => by rw [hτ1 j]; exact Iff.rfl
  refine ⟨s, fun t => ?_⟩
  obtain ⟨F, hF, hFt⟩ := hsurj t
  obtain ⟨a, ha, hau⟩ := hGu F hF
  refine ⟨a, fun j => ?_, fun a' ha' => hau a' ?_⟩
  · have h0 := (hzero _ (hF.sub (hsumG a))).2 ha j
    rw [MvPolynomial.eval₂_sub, sub_eq_zero] at h0
    rw [hFt j, h0, lin]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs1 i j]
    rfl
  · refine (hzero _ (hF.sub (hsumG a'))).1 fun j => ?_
    rw [MvPolynomial.eval₂_sub, sub_eq_zero, ← hFt j, ha' j, lin]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs1 i j]
    rfl

end GlobalTheory.ZV.HilbFn
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.thetaSections_veryAmple_periodic : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g (N' ^ 2) J b (spMap β)) (m : ℕ) σ, Odd N' → m ∣ N' → 2 ≤ m → t.Emb m (Over.mk (𝟙 (Sp K))) σ → IsIso (snd (Over.mk (𝟙 (Sp K))) t.A).left ∧ (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))).IsLB ∧ VAmp (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ ∧ LBIso (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))) ((lbPow t.L (m ^ 2)).pull (snd (Over.mk (𝟙 (Sp K))) t.A).left) ∧ (∀ a a' : Ix g (N' ^ 2), (∀ i, (a i).val ≡ (a' i).val [MOD m ^ 2]) → ∀ j, (σ a).f j = (σ a').f j) ∧ TorsBasis t.A (N' ^ 2) t.pt ∧ ∀ x : Out.baseOver (Sp K) ⟶ t.A, x ^ N' = 1 → ∃ h, t.lab h ^ N' = x := by
  first | exact @GlobalTheory.embSec_veryAmple_periodic | exact GlobalTheory.embSec_veryAmple_periodic | (intros; apply GlobalTheory.embSec_veryAmple_periodic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.pelObject_fibre_from_complex_charZero : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (τ : SAB H S), IsPEL D a bas ρ t τ → ∀ (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S), FromC em (PELClass (b := b) D a bas ρ em) t x := by
  first | exact @GlobalTheory.PELFrom.fromC_of_isPEL | exact GlobalTheory.PELFrom.fromC_of_isPEL | (intros; apply GlobalTheory.PELFrom.fromC_of_isPEL <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.thetaClosure_component_trdeg_ge : Out.Laws → Out.Laws2 → ∀ (n : ℕ), ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : ThetaFam n em C), ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ F.MM), IsOpenImmersion x → x ≫ F.s = spMap (algebraMap o R) → ∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y := by
  first | exact @GlobalTheory.ZM.GenericTrdeg.exists_algebraicIndependent | exact GlobalTheory.ZM.GenericTrdeg.exists_algebraicIndependent | (intros; apply GlobalTheory.ZM.GenericTrdeg.exists_algebraicIndependent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.fromC_sharpClass_fibre_of_charZero : Out.Laws → Out.Laws2 → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) [Finite J] (a : J → Matrix (Fin 8) (Fin 8) ℤ) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ), ArBase em → ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (c : SiegPre h (N' ^ 2) (b.ζ : o) s), c.Principal → IsSharp W a bas t c → ∀ (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S), FromC em (SharpClass (b := b) W a bas em) t x := by
  first | exact @GlobalTheory.SharpFrom.fromC_sharpClass | exact GlobalTheory.SharpFrom.fromC_sharpClass | (intros; apply GlobalTheory.SharpFrom.fromC_sharpClass <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.siegelPullback_iff_eighthPower_pullback : Out.Laws → Out.Laws2 → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (c : SiegPre h k (b.ζ : o) s) (c' : SiegPre h k (b.ζ : o) s') (t : TObj g k J b s) (t' : TObj g k J b s') (f : S' ⟶ S), c.Principal → c'.Principal → IsSharp W a bas t c → IsSharp W a bas t' c' → (SiegPB c' c f → TMap t' t f) ∧ ((∀ u v, ∃ j, a j = Matrix.single u v 1) → TMap t' t f → SiegPB c' c f) := by
  first | exact @GlobalTheory.PowerPullback.main | exact GlobalTheory.PowerPullback.main | (intros; apply GlobalTheory.PowerPullback.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.KerZero

def derPt {o R : Type} [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ]
    (D : Derivation o R ℂ) : R →+* DualNumber ℂ where
  toFun r := TrivSqZeroExt.inl (algebraMap R ℂ r) + TrivSqZeroExt.inr (D r)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]; rfl

theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f f' : R →+* R'} (h : spMap f = spMap f') : f = f' := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem derivation_eq_zero_of_ks_zero : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g k J b (spMap (algebraMap o R))) (s₀ : Sp ℂ ⟶ Sp o) (t₀ : TObj g k J b s₀) (m : t₀.A.left ⟶ t.A.left) (u : HolUnif t₀.pol.A t₀.pol.L t₀.pol.g) (Hm : Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → (IsGrpPullback t₀.A t.A (spMap (algebraMap R ℂ)) m ∧ LBIso t₀.L (t.L.pull m) ∧ (∀ i, (t₀.pt i).left ≫ m = (spMap (algebraMap R ℂ)) ≫ (t.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ m = m ≫ (t.act jj).left) → (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g k J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → ∀ (D : Derivation o R ℂ) s, KSRel u t.A.hom m (fun r => D r) 0 s → D = 0 := by
  intro h₁ h₂ h₃ o _ g k J b R _ _ _ _ _ t s₀ t₀ m u Hm χ hu hm hun D s hs
  obtain ⟨hm₁, hm₂, hm₃, hm₄⟩ := hm
  have hfst : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (derPt D) = spMap (algebraMap R ℂ) := by
    rw [spMap_comp]; congr 1; ext r; simp [derPt]
  obtain ⟨t', ht'⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g k J b _ _ _ _ (spMap (derPt D)) t rfl
  obtain ⟨φ, hφ₁, hφ₂, hφ₃, hφ₄⟩ := id ht'
  have hp := hφ₁.1
  let j : t₀.A.left ⟶ t'.A.left := hp.lift m (t₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    (by rw [hm₁.1.w, Category.assoc, hfst])
  have hj : j ≫ φ = m := hp.lift_fst _ _ _
  have hw : j ≫ t'.A.hom = t₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := hp.lift_snd _ _ _
  have hj₁ : IsGrpPullback t₀.A t'.A (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j :=
    hφ₁.cancel (hm₁.congr hfst.symm hj.symm) hw
  have hj₂ : LBIso t₀.L (t'.L.pull j) :=
    LBIso.trans t₀.isLB (pull_isLB t.isLB m) (pull_isLB t'.isLB j) hm₂
      (LBIso.chartPull (Geo.Tor.chartPullPull t'.L j j rfl) (chartPullSame t.L _ _ _ j fun _ => hj.symm) hφ₂).symm
  have hj₃ : ∀ i, (t₀.pt i).left ≫ j = (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (t'.pt i).left := by
    intro i
    apply hp.hom_ext
    · rw [Category.assoc, hj, hm₃, Category.assoc, hφ₃, ← Category.assoc, hfst]
    · have a₁ : (t₀.pt i).left ≫ t₀.A.hom = 𝟙 _ := Over.w (t₀.pt i)
      have a₂ : (t'.pt i).left ≫ t'.A.hom = 𝟙 _ := Over.w (t'.pt i)
      rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hj₄ : ∀ jj, (t₀.act jj).left ≫ j = j ≫ (t'.act jj).left := by
    intro a
    apply hp.hom_ext
    · rw [Category.assoc, hj, hm₄, Category.assoc, hφ₄, ← Category.assoc, hj]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_isConst_of_ksRel_zero' h₁ t₀.pol u Hm χ hu R (derPt D) t.A t'.A φ j s t.ab t'.ab hφ₁ hj₁ (by
    have e : (fun r => (derPt D r).snd) = fun r => D r := by funext r; simp [derPt]
    rw [e]
    exact hj ▸ hs)
  have hc := GlobalTheory.T.thetaObject_constantFamily_dualNumbers_isPullback h₁ h₂ h₃ o g k J b s₀ _ t₀ t' ρ j hρ ⟨hj₁, hj₂, hj₃, hj₄⟩
  have hcp : constPt (spMap (derPt D)) = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (algebraMap R ℂ) := by
    rw [constPt, hfst]
  have hc' : TMap t' t (constPt (spMap (derPt D))) := by
    rw [hcp]
    exact ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b _ _ _ _ _ _ t t₀ t').2 _ _ ⟨m, hm₁, hm₂, hm₃, hm₄⟩).1 hc
  have hx := hun (spMap (derPt D)) t' (by
    rw [hcp, spMap_comp, spMap_comp, spMap_comp]
    congr 1
    ext r <;> simp [derPt, TrivSqZeroExt.algebraMap_eq_inl]) ht' hc'
  rw [hcp, spMap_comp] at hx
  have hx' := spMap_inj hx
  ext r
  have := congrArg (fun f : R →+* DualNumber ℂ => (f r).snd) hx'
  simpa [derPt, TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.KS.KerZero
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_family_morphism_from_veryDense_graphs : ∀ (R σ₁ σ₂ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ₁] [Finite σ₂] [Finite Hh] (Z₁ Z₂ : Over (Sp R)) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (p₁ : Hh → σ₁ → R) (p₂ : Hh → σ₂ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z₁.hom (spMap x) ⟶ Z₂.left) → Prop), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsProper Z₁.hom → IsProper Z₂.hom → Smooth Z₁.hom → (∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → f ≫ Z₂.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ f) Q d (fun h i => x (p₁ h i.1 * p₂ h i.2))) → VeryDense {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (f : _), RingHom.ker x = q ∧ G K x f} → ∃ F : Z₁ ⟶ Z₂, ∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → f = pullback.fst _ _ ≫ F.left := by
  first | exact @GlobalTheory.ZM.GraphMor.exists_hom_of_graphs | exact GlobalTheory.ZM.GraphMor.exists_hom_of_graphs | (intros; apply GlobalTheory.ZM.GraphMor.exists_hom_of_graphs <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.siegelFamily_tangent_dimension_bound : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → ∀ (w w' : J), (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : o →+* K) (t : TObj g k J b (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))) (c : SiegPre h k (b.ζ : o) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), c.Principal → IsSharp W a bas t c → (∀ (lam : (Fin r → K) →ₗ[K] K) (t' : TObj g k J b (spMap ((algebraMap K (DualNumber K)).comp β))), TMap t' t (spMap (dirMap lam)) → TMap t' t (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ h * (h + 1) / 2 := by
  first | exact @GlobalTheory.PowerTangent.main | exact GlobalTheory.PowerTangent.main | (intros; apply GlobalTheory.PowerTangent.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

theorem _root_.GlobalTheory.T.exists_familyHom_of_graphs_over_ring_inverting_element : ∀ (R σ₁ σ₂ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ₁] [Finite σ₂] [Finite Hh] (Z₁ Z₂ : Over (Sp R)) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (p₁ : Hh → σ₁ → R) (p₂ : Hh → σ₂ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z₁.hom (spMap x) ⟶ Z₂.left) → Prop), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsProper Z₁.hom → IsProper Z₂.hom → Smooth Z₁.hom → (∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → φ ≫ Z₂.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ φ) Q d (fun h i => x (p₁ h i.1 * p₂ h i.2))) → DenseP {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ} → ∀ (K₀ : Type) [Field K₀] (x₀ : R →+* K₀) φ₀, G K₀ x₀ φ₀ → ∃ f : R, x₀ f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Y : Scheme.{0}) (π : Y ⟶ Z₁.left) (sY : Y ⟶ Sp R'), π ≫ Z₁.hom = sY ≫ spMap ρ → ∃ F : Y ⟶ Z₂.left, F ≫ Z₂.hom = sY ≫ spMap ρ ∧ ∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → ∀ io : pullback Z₁.hom (spMap x) ⟶ Y, io ≫ π = pullback.fst _ _ → φ = io ≫ F := by
  first | exact @GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit | exact GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit | (intros; apply GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit <;> assumption)
end
