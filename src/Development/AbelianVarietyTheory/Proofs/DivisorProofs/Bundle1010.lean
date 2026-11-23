module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle018
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle992
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle820
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle984
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section
namespace GlobalTheory.CubeThm

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

theorem comp_psum {T T' : Over S} {n : ℕ} (f : T' ⟶ T) (v : Fin n → (T ⟶ B)) (I : Finset (Fin n)) :
    f ≫ psum B v I = psum B (fun i => f ≫ v i) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp [pzero]
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    simp only [padd]
    rw [← Category.assoc, comp_lift]

theorem lift_comp_cubeCoordinates (x y z : B ⟶ B) :
    (fun i => lift x (lift y z) ≫ x3 B i) = ![x, y, z] := by
  funext i
  fin_cases i <;> simp [x3]

theorem cube_pic (M : GlobalTheory.UU.CP B) (x y z : B ⟶ B) :
    GlobalTheory.CechPic.pull (x * y * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull x.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull y.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) =
      GlobalTheory.CechPic.pull (x * y).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (x * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (y * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) := by
  set c := GlobalTheory.CechPic.cls M.L.L M.L.isLB
  have hT : (Theta B M.L.L).IsLB := LB.isLB_linComb M.L.isLB _ _
  have h0 : GlobalTheory.CechPic.cls (Theta B M.L.L) hT = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff hT).2 ⟨M.c.t, M.c.isGen⟩
  have h1 : (∑ I : ULift.{0} (Finset (Fin 3)),
      ((-1 : ℤ) ^ (3 - I.down.card)) • GlobalTheory.CechPic.pull (psum B (x3 B) I.down).left c) = 0 :=
    (GlobalTheory.CechPic.cls_linComb M.L.isLB (fun I : ULift.{0} (Finset (Fin 3)) => (psum B (x3 B) I.down).left)
      (fun I => (-1 : ℤ) ^ (3 - I.down.card)) hT).symm.trans h0
  have h2 := congrArg (GlobalTheory.CechPic.pull (lift x (lift y z)).left) h1

  rw [map_sum, map_zero] at h2
  simp only [map_zsmul, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, comp_psum, lift_comp_cubeCoordinates] at h2
  rw [← Equiv.ulift.symm.sum_comp] at h2
  simp only [Equiv.ulift_symm_down] at h2
  rw [show (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide] at h2
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at h2
  have e0 : psum B ![x, y, z] ∅ = 1 := rfl
  have e1 : psum B ![x, y, z] {0} = x := (show _ = x * 1 from rfl).trans (mul_one x)
  have e2 : psum B ![x, y, z] {1} = y := (show _ = y * 1 from rfl).trans (mul_one y)
  have e3 : psum B ![x, y, z] {2} = z := (show _ = z * 1 from rfl).trans (mul_one z)
  have e4 : psum B ![x, y, z] {0, 1} = x * y :=
    (show _ = x * (y * 1) from rfl).trans (congrArg (x * ·) (mul_one y))
  have e5 : psum B ![x, y, z] {0, 2} = x * z :=
    (show _ = x * (z * 1) from rfl).trans (congrArg (x * ·) (mul_one z))
  have e6 : psum B ![x, y, z] {1, 2} = y * z :=
    (show _ = y * (z * 1) from rfl).trans (congrArg (y * ·) (mul_one z))
  have e7 : psum B ![x, y, z] {0, 1, 2} = x * y * z :=
    (show _ = x * (y * (z * 1)) from rfl).trans
      ((congrArg (x * ·) (congrArg (y * ·) (mul_one z))).trans (mul_assoc x y z).symm)
  rw [e0, e1, e2, e3, e4, e5, e6, e7] at h2
  have c0 : (∅ : Finset (Fin 3)).card = 0 := rfl
  have c1 : ({0} : Finset (Fin 3)).card = 1 := rfl
  have c2 : ({1} : Finset (Fin 3)).card = 1 := rfl
  have c3 : ({2} : Finset (Fin 3)).card = 1 := rfl
  have c4 : ({0, 1} : Finset (Fin 3)).card = 2 := rfl
  have c5 : ({0, 2} : Finset (Fin 3)).card = 2 := rfl
  have c6 : ({1, 2} : Finset (Fin 3)).card = 2 := rfl
  have c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := rfl
  rw [c0, c1, c2, c3, c4, c5, c6, c7] at h2
  norm_num at h2
  rw [← sub_eq_zero]
  rw [← h2]
  abel

end GlobalTheory.CubeThm
end
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM


open MvPolynomial in
theorem GlobalTheory.NormSheaf.normIdeal_map_eq_prod_lifts : ∀ (A B K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [CharZero K] [Algebra A K] [Algebra B L] [Algebra K L] [FiniteDimensional K L]
    [IsFractionRing A K] [IsFractionRing B L] (φ : A →+* B), φ.Finite →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp φ → ∀ (J : Ideal B)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ψ : Fin (Module.finrank K L) → (B →+* V')), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ (∀ j, (ψ j).comp φ = f.comp h) ∧
      (GlobalTheory.NormSheaf.normIdeal A K L B J).map (f.comp h) = ∏ j, J.map (ψ j) := by
  intro A B K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ hφ hcomp J V _ _ _ _ hV h
  obtain ⟨R, _, _, hinj, hfin, σ, hσ, hP⟩ := GlobalTheory.T.exists_finite_algebra_splitting_normForm A B K L φ hφ hcomp
  obtain ⟨V', _, _, _, _, f, ρ, hV', hf, hloc, hρ⟩ := GlobalTheory.T.exists_lift_to_complete_dvr_of_finite' A R hinj hfin V hV h
  let ψ : Fin (Module.finrank K L) → (B →+* V') := fun j => ρ.comp (σ j)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, f, ψ, hV', hf, hloc, ?_, ?_⟩
  · intro j
    show (ρ.comp (σ j)).comp φ = f.comp h
    rw [RingHom.comp_assoc, hσ j, hρ]
  have key : ∀ (m : ℕ) (g : Fin m → B) (P : MvPolynomial (Fin m) A),
      P.map (algebraMap A R) = ∏ j, ∑ i, C (σ j (g i)) * X i →
      Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) =
        ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) := by
    intro m g P hPR
    rw [← GlobalTheory.T.span_coeff_prod_linear_eq_prod_span V' _ m (fun j i => ψ j (g i))]
    have hE : (∏ j, ∑ i, C (ψ j (g i)) * X i : MvPolynomial (Fin m) V') = (P.map (algebraMap A R)).map ρ := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hPR]; simp [map_prod, map_sum, ψ]
    have hfun : (fun s => (f.comp h) (P.coeff s)) =
        fun s => (∏ j, ∑ i, C (ψ j (g i)) * X i : MvPolynomial (Fin m) V').coeff s := by
      funext s
      rw [hE, MvPolynomial.map_map, MvPolynomial.coeff_map, hρ]
    rw [hfun]
  unfold GlobalTheory.NormSheaf.normIdeal
  rw [Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨a, ⟨m, g, hgJ, s, hs⟩, rfl⟩
    obtain ⟨P, hPK, hPR⟩ := hP m g
    have ha : a = P.coeff s := IsFractionRing.injective A K (by rw [hs, ← hPK, MvPolynomial.coeff_map])
    have hmem : (f.comp h) a ∈ Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) :=
      Ideal.subset_span ⟨s, by rw [ha]⟩
    rw [key m g P hPR] at hmem
    have hle : ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) ≤ ∏ j, J.map (ψ j) :=
      Finset.prod_le_prod' (fun j _ => Ideal.span_le.2 (by
        rintro _ ⟨i, rfl⟩; exact Ideal.mem_map_of_mem _ (hgJ i)))
    exact hle hmem
  · have hfg : ∀ j, ∃ t : Finset V', (↑t : Set V') ⊆ ψ j '' (J : Set B) ∧ J.map (ψ j) = Ideal.span (↑t : Set V') := by
      intro j
      have h1 : (J.map (ψ j)).FG := IsNoetherian.noetherian _
      rw [Ideal.map] at h1 ⊢
      exact (Submodule.fg_span_iff_fg_span_finset_subset _).1 h1
    choose t ht hspan using hfg
    have hpre : ∀ (x : Σ j, (t j : Set V')), ∃ b ∈ J, ψ x.1 b = x.2 := by
      rintro ⟨j, x, hx⟩
      obtain ⟨b, hb, e⟩ := ht j hx
      exact ⟨b, hb, e⟩
    choose pre hpreJ hpreψ using hpre
    let e := Fintype.equivFin (Σ j, (t j : Set V'))
    let g : Fin (Fintype.card (Σ j, (t j : Set V'))) → B := fun i => pre (e.symm i)
    have hgJ : ∀ i, g i ∈ J := fun i => hpreJ _
    obtain ⟨P, hPK, hPR⟩ := hP _ g
    have hj : ∀ j, Ideal.span (Set.range fun i => ψ j (g i)) = J.map (ψ j) := by
      intro j
      apply le_antisymm
      · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact Ideal.mem_map_of_mem _ (hgJ i)
      · rw [hspan j, Ideal.span_le]
        intro x hx
        apply Ideal.subset_span
        refine ⟨e ⟨j, x, hx⟩, ?_⟩
        simp only [g, Equiv.symm_apply_apply]
        exact hpreψ ⟨j, x, hx⟩
    calc ∏ j, J.map (ψ j) = ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) := by simp_rw [hj]
      _ = Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) := (key _ g P hPR).symm
      _ ≤ _ := by
        rw [Ideal.span_le]
        rintro _ ⟨s, rfl⟩
        apply Ideal.subset_span
        exact ⟨P.coeff s, ⟨_, g, hgJ, s, by rw [← hPK, MvPolynomial.coeff_map]⟩, rfl⟩
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_specialUnitary_section_lowerUnitriangular_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (σ : V (nd X) → realSU X.Ψ X.Gm) (ρ : ℝ) (D₁ : V (nd X) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), 0 < ρ ∧ σ 0 = 1 ∧ ContinuousOn σ (Metric.ball 0 ρ) ∧ (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) ∧ HasStrictFDerivAt (fun z => (fun τ a b => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) D₁ 0 ∧ ∀ z, D₁ z ∈ realLie X.Ψ X.Gm ∧ (∀ τ a b, b < a → inFrame x (D₁ z) τ a b = nmat X z τ a b) ∧ ∀ τ a, inFrame x (D₁ z) τ a a = 0 := by
  first | exact @GlobalTheory.SUChartSection.exists_section | exact GlobalTheory.SUChartSection.exists_section | (intros; apply GlobalTheory.SUChartSection.exists_section <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginBC



theorem etale_bc : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∀ a : A, a ≠ 0 →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective f → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp f = i →
      (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁)),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      (∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
        GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
        GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (Localization.AtPrime QA₁) DA₁ ρ₁) ∧
      (∀ (P₁ : Ideal (Localization.AtPrime QA₁)) [P₁.IsPrime], P₁.height ≤ 1 →
        GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (Localization.AtPrime QA₁) DA₁ P₁) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA
    hFits ρ hρ hpt a ha0 ha A₁ _ _ _ _ _ _ f i₁ hf hi₁ hloc₁ hcomp hK
  obtain ⟨-, -, hqA, -, hj, hψ, htor⟩ := hFits
  obtain ⟨hρA, hρker, hρmod⟩ := hρ
  have hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0 := by
    rw [← RingHom.mem_ker, hρker]; exact Ideal.subset_span rfl
  have hmax := comap_maximalIdeal_eq_origin P φ hφ hsh hP
  set β := fibBC f i i₁ EA QA jA hcomp hj hf with hβ
  have hcong := reduce_sub_glue_mem f i i₁ EA QA jA hcomp hj ρ hρA hρX hρmod
  have hunit := isUnit_reduce f i i₁ EA QA jA hcomp hj ρ hρA hρX hmax hloc₁ hcong
  refine ⟨Ext f EA, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ideal₁ f i i₁ EA QA jA hcomp hj, inferInstance, locMap f i i₁ EA QA jA hcomp hj,
    fibMap f i i₁ EA QA jA hcomp hj hi₁, BC β DA, inferInstance, inferInstance, bcAct β DA q actA,
    ⟨hi₁, hloc₁, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit, ⟨?_, ?_, ?_⟩, ?_⟩, ?_, β, inclD β DA, ?_,
    inclD_algebraMap β DA⟩
  · simpa using hqA.map f
  · exact comap_ideal₁_eq_origin f i i₁ EA QA jA hcomp hj hmax hloc₁
  · apply RingHom.ext; intro p
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A₁[X] (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj),
      locMap_algebraMap, Algebra.TensorProduct.algebraMap_apply]
    rw [glue_tmul]
    change algebraMap T[X] O (Polynomial.map i₁ p) * _ = _
    simp
  · let L := Loc₁ f i i₁ EA QA jA hcomp hj
    letI : IsLocalization (Algebra.algebraMapSubmonoid L (nonZeroDivisors A₁))
        (GlobalTheory.LocAcyc.GenFib A₁ L) := Localization.isLocalization (M := Algebra.algebraMapSubmonoid L (nonZeroDivisors A₁))
    exact IsLocalization.lift_comp _
  · exact isZTorsor_bc β DA q hq actA htor
  · apply RingHom.ext; intro x
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A₁ (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj)]
    simp only [reduceLoc, IsLocalization.lift_eq, algebraMap_ext, reduce_tmul]
    change Polynomial.eval 0 (Polynomial.C x) * _ = _
    simp
  · exact GlobalTheory.T.ker_baseChangedReduction_eq_span_X T O A A₁ f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit hρker
  · exact reduceLoc_sub_locMap_mem f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit hcong
  · exact GlobalTheory.T.localization_at_prime_etale_compat T O A A₁ f i i₁ hf EA QA jA hcomp hj ρ hρA hρX hunit DA q actA hq htor hpt
  · intro P₁ _ hP₁
    by_cases h : algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∈ P₁
    · exact GlobalTheory.T.integralClosure_torsor_etale_height_one_abhyankar T O A A₁ f i i₁ hf EA QA jA hcomp hj DA q actA hq hqA htor a ha0 hK P₁ hP₁ h
    · exact GlobalTheory.T.normal_local_ring_etale_base_change T O A A₁ f i i₁ hf EA QA jA hcomp hj DA q actA hq hqA htor a ha0 ha P₁ h
  · have hloc : (locMap f i i₁ EA QA jA hcomp hj).comp (locBC f i i₁ EA QA jA hcomp hj) = jA := by
      apply IsLocalization.ringHom_ext QA.primeCompl
      apply RingHom.ext; intro x
      simp [locBC_algebraMap, locMap_algebraMap, glue_inclE]
    apply IsLocalization.ringHom_ext
      (Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A))
    apply RingHom.ext; intro r
    rw [RingHom.comp_apply, RingHom.comp_apply, hβ, fibBC_algebraMap, RingHom.comp_apply, ← RingHom.comp_apply ψA, hψ]
    simp only [fibMap, IsLocalization.lift_eq, RingHom.comp_apply]
    rw [← RingHom.comp_apply (locMap f i i₁ EA QA jA hcomp hj), hloc]

end GlobalTheory.KeyOriginBC
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump.FinBump

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem psiFin_add (a b : Af E) : psiFin (a + b) = psiFin a * psiFin b := by
  simp only [psiFin, map_add (f := _), AddChar.map_add_eq_mul, Circle.coe_mul]

theorem bumpFin_eq (hK : ∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n),
      u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1)
    {g u : GL (Fin n) (Af E)} (hu : u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n))
    (hg : u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) :
    bumpFin g = psiFin (GlobalTheory.Whittaker.superDiag u) := by
  have h : ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n :=
    ⟨u, hu, hg⟩
  unfold bumpFin
  rw [dite_eq_left h]
  obtain ⟨hu', hg'⟩ := h.choose_spec
  set u' := h.choose
  have hw : u⁻¹ * u' ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) := mul_mem (inv_mem hu) hu'
  have hwK : u⁻¹ * u' ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := by
    have : u⁻¹ * u' = (u⁻¹ * g) * (u'⁻¹ * g)⁻¹ := by group
    rw [this]; exact mul_mem hg (inv_mem hg')
  have hsplit : u' = u * (u⁻¹ * u') := by group
  rw [hsplit, GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip hu hw, psiFin_add, hK _ hw hwK, mul_one]

end GlobalTheory.WhitBump.FinBump

namespace GlobalTheory.WhitBump.FinBump

theorem bumpFin_zero_of_not {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}
    {g : GL (Fin n) (Af E)}
    (h : ¬ ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) :
    bumpFin g = 0 := by
  unfold bumpFin; rw [dite_eq_right h]

theorem bumpFin_props : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ),
    (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n →
      psiFin (GlobalTheory.Whittaker.superDiag u) = 1) →
    bumpFin (E := E) (n := n) 1 = 1 ∧
    (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), ∀ g, bumpFin (u * g) = psiFin (GlobalTheory.Whittaker.superDiag u) * bumpFin g) ∧
    (∀ k ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n, ∀ g, bumpFin (g * k) = bumpFin g) ∧
    ∀ g, bumpFin g ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n),
      u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := by
  intro E _ _ _ n hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bumpFin_eq hK (one_mem _) (by simpa using one_mem _), hK 1 (one_mem _) (one_mem _)]
  · intro u hu g
    by_cases h : ∃ v ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), v⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n
    · obtain ⟨v, hv, hvg⟩ := h
      have e : (u * v)⁻¹ * (u * g) = v⁻¹ * g := by group
      rw [bumpFin_eq hK (mul_mem hu hv) (by rw [e]; exact hvg), bumpFin_eq hK hv hvg,
        GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip hu hv, psiFin_add]
    · rw [bumpFin_zero_of_not h, mul_zero]
      refine bumpFin_zero_of_not fun ⟨v, hv, hvg⟩ => h ⟨u⁻¹ * v, mul_mem (inv_mem hu) hv, ?_⟩
      have e : (u⁻¹ * v)⁻¹ * g = v⁻¹ * (u * g) := by group
      rw [e]; exact hvg
  · intro k hk g
    by_cases h : ∃ v ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), v⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n
    · obtain ⟨v, hv, hvg⟩ := h
      have e : v⁻¹ * (g * k) = (v⁻¹ * g) * k := by group
      rw [bumpFin_eq hK hv (by rw [e]; exact mul_mem hvg hk), bumpFin_eq hK hv hvg]
    · rw [bumpFin_zero_of_not h]
      refine bumpFin_zero_of_not fun ⟨v, hv, hvg⟩ => h ⟨v, hv, ?_⟩
      have e : v⁻¹ * g = (v⁻¹ * (g * k)) * k⁻¹ := by group
      rw [e]; exact mul_mem hvg (inv_mem hk)
  · intro g hg
    by_contra h
    exact hg (bumpFin_zero_of_not h)

end GlobalTheory.WhitBump.FinBump
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_abelianScheme_quotient_by_finite_translations : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (H : Subgroup (𝟙_ (Over S) ⟶ A)), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Finite H → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ A), h ∈ H → toUnit (Over.mk x) ≫ h = 1 → h = 1) → ∃ (A' : Over S) (_ : GrpObj A') (_ : IsCommMonObj A') (ψ : A ⟶ A'), IsAbelianScheme A' ∧ IsMonHom ψ ∧ GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left := by
  first | exact @GlobalTheory.TranslQuotient.exists_quotient | exact GlobalTheory.TranslQuotient.exists_quotient | (intros; apply GlobalTheory.TranslQuotient.exists_quotient <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.isTestHomMatrix_of_proportional_generating_combinations : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c → GlobalTheory.HomFixUniv.Normal t c αA βB → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  first | (exact @GlobalTheory.HomFixCond.isMat_of_conditions) | (exact GlobalTheory.HomFixCond.isMat_of_conditions) | (intros; apply GlobalTheory.HomFixCond.isMat_of_conditions  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.eq_of_pullbackSectionsProportionalToCombinations : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (Ψ₁ Ψ₂ : X ⟶ B₀), GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → GlobalTheory.HomFixUniv.Generates a φ p c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₁ c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₂ c → Ψ₁ ≫ fB = Ψ₂ ≫ fB → Ψ₁ = Ψ₂ := by
  first | (exact @GlobalTheory.HomFixUniv.eq_of_proport) | (exact GlobalTheory.HomFixUniv.eq_of_proport) | (intros; apply GlobalTheory.HomFixUniv.eq_of_proport  <;> assumption)
end

section

namespace GlobalTheory.FinGL.MultSharpObj

open GlobalTheory.FinGL Formalism.L2.DIV

theorem placeBound : MultSharpPf.PlaceBound := by
  intro F _ _ ψ hψ r V _ _ _ b σ hσ ρ k hk hr hq
  rw [GlobalTheory.T.symmetricPositionCharMultiplicity_parabolicInduction F ψ hψ r V b σ hσ ρ k hr]
  exact sum_numBlockSets_mul_gamma_two_sided_bounds r k (Fintype.card F) b hk (by omega) hq Fintype.one_lt_card

theorem multSharp : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.MultSharp := MultSharpPf.multSharp_of_placeBound placeBound

end GlobalTheory.FinGL.MultSharpObj
end
