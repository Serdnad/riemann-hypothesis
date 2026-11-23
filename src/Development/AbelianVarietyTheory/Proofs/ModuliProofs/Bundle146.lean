module

import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle138
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle141
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle084
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteOfAmpleDeterminantFramesPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle142
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle143
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.ConnOpen

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw ReciprocityTheory.ChartRestriction.G.Out

theorem preconnectedSpace_of_functions (Y : Scheme.{0})
    (H : ∀ s : Γ(Y, ⊤), Y.basicOpen s = ⊥ ∨ Y.basicOpen s = ⊤) : PreconnectedSpace Y := by
  apply _root_.GlobalTheory.ConnSpread.preconnectedSpace_of_functions <;> assumption

theorem surjective_appTop {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}}
    (p : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed p] :
    Function.Surjective p.appTop.hom := by
  apply _root_.GlobalTheory.AlgGroup.surjective_appTop <;> assumption

variable {X X' : Scheme.{0}}

def fnSec (π : X' ⟶ X) (s : Γ(X', ⊤)) : LB.Sec ((Inh.trivLB X).pull π) where
  f := fun _ => rs X' le_top s
  compat := fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (rs_rs _ _ s).trans (rs_rs _ _ s).symm

theorem triv_pull (π : X' ⟶ X) : Triv ((Inh.trivLB X).pull π) :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    erw [Inh.linComb_triv_g, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm⟩

theorem preconnectedSpace_of_line {R F : Type} [CommRing R] [Field F]
    {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (Inh.trivLB X)) {g : R →+* F} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of F)} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (v : Fin P.a → F) (hv : ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : F, w = c • v) :
    PreconnectedSpace X' := by
  obtain ⟨E, hE⟩ := P.sec F g X' π f' h
  have key : ∀ s : Γ(X', ⊤), ∃ c : F, ∀ i,
      rs X' (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s = GlobalTheory.AbLaw.cst f' _ c * loc P π f' v i := fun s => by
    obtain ⟨w, hw⟩ := E.surjective (fnSec π s)
    obtain ⟨c, hc⟩ := hv w.1 w.2
    refine ⟨c, fun i => ?_⟩
    have e := hE w i
    rw [hw] at e
    refine ((rs_rs _ _ s).symm.trans e).trans ?_
    rw [← loc_smul, ← hc]
    rfl
  obtain ⟨c₁, h₁⟩ := key 1
  have hu : ∀ i, IsUnit (loc P π f' v i) := fun i =>
    isUnit_of_mul_isUnit_right (by rw [← h₁ i, map_one]; exact isUnit_one)
  refine preconnectedSpace_of_functions X' fun s => ?_
  obtain ⟨c, hc⟩ := key s
  by_cases h0 : c = 0
  · refine Or.inl (le_bot_iff.1 fun y hy => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have := (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).2 hy
    rwa [hc, h0, map_zero, zero_mul, Scheme.basicOpen_zero] at this
  · refine Or.inr (top_unique fun y _ => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    refine (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).1 ?_
    rw [hc]
    exact mem_of_isUnit (((IsUnit.mk0 c h0).map _).mul (hu i)) hi

theorem exists_nonempty_fibre {R K : Type} [CommRing R] [Field K] {Z Z₀ : Scheme.{0}} (s : Z ⟶ Sp R)
    (hs : IsOpenMap s) (x : R →+* K) {π : Z₀ ⟶ Z} {q : Z₀ ⟶ Sp K} (h : π ≫ s = q ≫ spMap x) (z : Z₀) :
    ∃ e : R, x e ≠ 0 ∧ ∀ p : PrimeSpectrum R, e ∉ p.asIdeal → ∃ y : Z, s y = p := by
  have hz : s (π z) ∈ Set.range s := ⟨_, rfl⟩
  obtain ⟨_, ⟨e, rfl⟩, he, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz hs.isOpen_range
  refine ⟨e, fun h0 => ?_, fun p hp => hle hp⟩
  have e' : s (π z) = spMap x (q z) := congrArg (fun t => t z) h
  rw [e'] at he
  refine he ?_
  change x e ∈ (q z).asIdeal
  rw [h0]
  exact zero_mem _

theorem geometricallyConnected_near : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (K : Type) [Field K] (x : R →+* K), IsProjOver s → Smooth s → GeometricallyConnected (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → GeometricallyConnected (pullback.snd s (spMap φ)) := by
  intro R _ Z s K _ x hp hs hc
  have hp' := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver s).2 hp
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R Z s hs hp' _ (Inh.trivLB_isLB _)
  have hpr : IsProper s := GlobalTheory.AbLaw.isProper_of_isProjBy R Z s hp'
  let L := AlgebraicClosure K
  let g₀ : R →+* L := (algebraMap K L).comp x
  let q := pullback.snd s (spMap x)
  let y₀ : Sp L ⟶ Sp K := spMap (algebraMap K L)
  have h₀ : IsPullback (pullback.fst q y₀ ≫ pullback.fst s (spMap x)) (pullback.snd q y₀) s
      (Spec.map (CommRingCat.ofHom g₀)) := by
    have := (IsPullback.of_hasPullback q y₀).paste_horiz (IsPullback.of_hasPullback s (spMap x))
    rwa [← Spec.map_comp] at this
  have hi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ q inferInstance hc
  have hint : IsIntegral (pullback q y₀) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback q y₀)
  have hpr₀ : IsProper (pullback.snd q y₀) := MorphismProperty.of_isPullback h₀ hpr
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀⟩ : Nonempty ↥(pullback q y₀) := inferInstance
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst q y₀ ≫ pullback.fst s (spMap x)) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul L (0 : Fin P.a → L), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline (surjective_appTop _))
  obtain ⟨e, he, him⟩ := exists_nonempty_fibre s s.isOpenMap g₀ h₀.w x₀
  refine ⟨δ * e, fun h0 => mul_ne_zero hδ he ?_, fun R' _ φ hφ => ?_⟩
  · rw [← map_mul]
    exact (congrArg (algebraMap K L) h0).trans (map_zero _)
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Y fst snd h => ?_⟩
  let g : R →+* F := (algebraMap R' F).comp φ
  have h₁ : IsPullback (fst ≫ pullback.fst s (spMap φ)) snd s (Spec.map (CommRingCat.ofHom g)) := by
    have := h.paste_horiz (IsPullback.of_hasPullback s (spMap φ))
    rwa [← Spec.map_comp] at this
  have hg : IsUnit (g δ * g e) := by
    rw [← map_mul]
    exact hφ.map (algebraMap R' F)
  have := preconnectedSpace_of_line P h₁ _ (hker F g (isUnit_of_mul_isUnit_left hg))
  obtain ⟨y, hy⟩ := him (PrimeSpectrum.comap g ⊥) fun hm =>
    (isUnit_of_mul_isUnit_right hg).ne_zero hm
  obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback h₁ y (⊥ : PrimeSpectrum F) hy
  exact ⟨⟨z⟩⟩

end GlobalTheory.ConnOpen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AbLaw.CubeAffine

theorem triv_theta_of_isProjBy :
    Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ M : LB A.left, M.IsLB → Triv (Theta A M) :=
  fun hL R _ A _ _ hA hp M hM => CubeProj.exists_gen_theta_of_isProjBy hL.globalFns R A hA hp M hM

end GlobalTheory.AbLaw.CubeAffine
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

theorem _root_.GlobalTheory.T.card_basis_polarisation_power_zero_eq_one : Out.GlobalFnsSt → ∀ (R : Type) [CommRing R] [Nontrivial R] (P : Out.PolAV (Sp R)) (n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L ((0 : ℕ) : ℤ) (Over.mk (𝟙 (Sp R))))), GlobalTheory.LN.BasisAlong P.A P.L 0 (𝟙 _) b → n = 1 := by
  first | exact @GlobalTheory.basisAlong_zero_card | exact GlobalTheory.basisAlong_zero_card | (intros; apply GlobalTheory.basisAlong_zero_card <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

theorem _root_.GlobalTheory.T.pulledSectionsFormBasis_id_of_pulledSectionsFormBasis : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N n : ℕ) (T T' : Over Z) (h : T' ⟶ T) (b : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T)), L.IsLB → GlobalTheory.LN.BasisAlong G L N h b → ∃ b' : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T'), GlobalTheory.LN.BasisAlong G L N (𝟙 T') b' := by
  first | exact @GlobalTheory.ModelSum.basisAlong_id_of_basisAlong | exact GlobalTheory.ModelSum.basisAlong_id_of_basisAlong | (intros; apply GlobalTheory.ModelSum.basisAlong_id_of_basisAlong <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

theorem _root_.GlobalTheory.T.card_pulledSectionsFormBasis_eq_pow_dim : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : Out.PolAV (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L (N : ℤ) (Over.mk (𝟙 (Sp R))))), 1 ≤ N → GlobalTheory.LN.BasisAlong P.A P.L N (𝟙 _) b → n = N ^ P.g := by
  first | exact @GlobalTheory.LN.SecRank.card_basis_eq_pow | exact GlobalTheory.LN.SecRank.card_basis_eq_pow | (intros; apply GlobalTheory.LN.SecRank.card_basis_eq_pow <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.isFinite_of_ampleDeterminantFrames_pullback : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Y : Scheme.{0}) [IsLocallyNoetherian Z] (z : Z ⟶ Sp ℤ) (t : SAB H Z) (t' : SAB H Y) (f : Z ⟶ Y) (_ : SABMap t t' f) (N : ℕ) (_ : GlobalTheory.LN.AmpFrames t.G t.PP.L N), 0 < N → IsNormalScheme Z → Flat z → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsProper f → IsFinite f := by
  first | exact @GlobalTheory.FrameFinite.isFinite_of_ampFrames | exact GlobalTheory.FrameFinite.isFinite_of_ampFrames | (intros; apply GlobalTheory.FrameFinite.isFinite_of_ampFrames <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.exists_isConst_of_ksRel_zero' : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (φ : A'.left ⟶ A.left) (j : P₀.A.left ⟶ A'.left) (s : (Fin P₀.g → ℂ) → ∀ W : A.left.Opens, Γ(A.left, W) → ℂ), IsAbelianScheme A → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) φ → IsGrpPullback P₀.A A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j → KSRel u A.hom (j ≫ φ) (fun r => (xD r).snd) 0 s → ∃ ρ, IsConst A' P₀.A ρ j := by
  first | exact @GlobalTheory.KS.exists_isConst_of_ksRel_zero | exact GlobalTheory.KS.exists_isConst_of_ksRel_zero | (intros; apply GlobalTheory.KS.exists_isConst_of_ksRel_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

theorem exists_hom_of_graphs_of_isUnit : ∀ (R σ₁ σ₂ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ₁] [Finite σ₂] [Finite Hh] (Z₁ Z₂ : Over (Sp R)) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (p₁ : Hh → σ₁ → R) (p₂ : Hh → σ₂ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z₁.hom (spMap x) ⟶ Z₂.left) → Prop), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsProper Z₁.hom → IsProper Z₂.hom → Smooth Z₁.hom → (∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → φ ≫ Z₂.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ φ) Q d (fun h i => x (p₁ h i.1 * p₂ h i.2))) → DenseP {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ} → ∀ (K₀ : Type) [Field K₀] (x₀ : R →+* K₀) φ₀, G K₀ x₀ φ₀ → ∃ f : R, x₀ f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Y : Scheme.{0}) (π : Y ⟶ Z₁.left) (sY : Y ⟶ Sp R'), π ≫ Z₁.hom = sY ≫ spMap ρ → ∃ F : Y ⟶ Z₂.left, F ≫ Z₂.hom = sY ≫ spMap ρ ∧ ∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → ∀ io : pullback Z₁.hom (spMap x) ⟶ Y, io ≫ π = pullback.fst _ _ → φ = io ≫ F := by
  intro R σ₁ σ₂ Hh _ _ _ _ _ _ Z₁ Z₂ I₁ I₂ M₁ M₂ th₁ th₂ p₁ p₂ Q d G h1 h2 h3 h4 h5 h6 h7 K₀ _ x₀ φ₀ h0
  obtain ⟨f, F₀, hf, hF, hG⟩ :=
    GlobalTheory.T.exists_familyHom_near_goodPrime_of_graphs R σ₁ σ₂ Hh Z₁ Z₂ I₁ I₂ M₁ M₂ th₁ th₂ p₁ p₂ Q d G h1 h2 h3 h4 h5 h6 h7 K₀ x₀ φ₀ h0
  refine ⟨f, hf, fun R' _ ρ hρ Y π sY hπ => ?_⟩
  have e : (IsLocalization.Away.lift f hρ : Localization.Away f →+* R').comp
      (algebraMap R (Localization.Away f)) = ρ := IsLocalization.Away.lift_comp _ _
  have w : π ≫ Z₁.hom = (sY ≫ spMap (IsLocalization.Away.lift f hρ : Localization.Away f →+* R')) ≫
      spMap (algebraMap R (Localization.Away f)) := by
    rw [Category.assoc, ← spMap_comp, e, hπ]
  refine ⟨pullback.lift π _ w ≫ F₀, ?_, fun K _ x φ hφ io hio => ?_⟩
  · rw [Category.assoc, hF, pullback.lift_fst_assoc, hπ]
  · rw [← Category.assoc]
    exact hG K x φ hφ _ (by rw [Category.assoc, pullback.lift_fst, hio])

end GlobalTheory.ZM.NearBuild
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.nonempty_levelQuot_of_level_dvd : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (LevelQuot l Xo₂) := by
  first | exact @GlobalTheory.nonempty_levelQuot | exact GlobalTheory.nonempty_levelQuot | (intros; apply GlobalTheory.nonempty_levelQuot <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.fullLevelObject_of_covering_pullbacks : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (ν : SABMap t' t f) (lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)), p ∈ Set.range f ∧ (∀ a, (lv' a).left ≫ ν.φ = f ≫ (lv a).left) ∧ FullObj D (f ≫ s) t' lv') → FullObj D s t lv := by
  first | exact @GlobalTheory.FullDescent.fullObj_of_cover | exact GlobalTheory.FullDescent.fullObj_of_cover | (intros; apply GlobalTheory.FullDescent.fullObj_of_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.fullLevelObject_pullback_exists_and_full : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (f : S' ⟶ S), (∃ (t' : SAB H S') (ν : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), ∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) ∧ ∀ (t' : SAB H S') (ν : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), (∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) → FullObj D s t lev → FullObj D (f ≫ s) t' lv := by
  first | exact @GlobalTheory.fullObj_pull | exact GlobalTheory.fullObj_pull | (intros; apply GlobalTheory.fullObj_pull <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.torsion_eq_one_of_translDiff_trivial_model : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (f : V →+* Ω), IsLocalHom f → ∀ n : ℕ, (n : Ω) ≠ 0 → ∀ x : Over.mk (spMap f) ⟶ B, x ^ n = 1 → GlobalTheory.AbLaw.Triv (translDiff B M.L.L x) → x = 1 := by
  first | exact @GlobalTheory.PrincipalModel.torsion_eq_one_of_triv | exact GlobalTheory.PrincipalModel.torsion_eq_one_of_triv | (intros; apply GlobalTheory.PrincipalModel.torsion_eq_one_of_triv <;> assumption)
end
