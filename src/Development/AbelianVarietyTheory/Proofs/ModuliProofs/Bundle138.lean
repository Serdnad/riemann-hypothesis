module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AmpleDeterminantFramesPullbackOfIsAffineHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionPowerTransportCartesianSquare
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoOfAmpleDeterminantFrames
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
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.SeesawReduced

theorem triv_locally_of_dense : ∀ (R : Type) [CommRing R] [IsReduced R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Smooth f → IsProper f → GeometricallyIntegral f → IsProjBy f → Dense {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧ IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)} → ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsUnit (g r) → Triv (M.pull π) := by
  intro R _ _ X f M hM hSm hPr hGI hPB hD p
  haveI := hPr
  haveI := hGI

  have hP : Nonempty (Perf f M) := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R X f hSm hPB M hM
  have hQ : Nonempty (Perf f (pw M (-1))) := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R X f hSm hPB _ (isLB_pw hM (-1))

  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R X f M hM hP hQ hPr hGI
  have hAll := hD.closure_eq.symm.trans hC.closure_eq
  have hmem : ∀ q : PrimeSpectrum R, q ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K)
      (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
      IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)} := by
    intro q; rw [← hAll]; exact Set.mem_univ q

  obtain ⟨K, _, g, X₁, π₁, f₁, hk, hpb, htr⟩ := hmem p
  obtain ⟨K₀, _, g₀, X₀, π₀, f₀, hk₀, hpb₀, hbij, htr₀⟩ :=
    GlobalTheory.GeomFibre.exists_field_pullback_appTop_bijective_and_triv R X f M hM hPr hGI K g X₁ π₁ f₁ hpb htr
  obtain ⟨r, I, hr, -, hI⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R X f M hM hP inferInstance inferInstance
    K₀ g₀ X₀ π₀ f₀ hpb₀ hbij htr₀
  refine ⟨r, ?_, ?_⟩
  · intro hrp
    apply hr
    have hrk : r ∈ RingHom.ker g₀ := by rw [hk₀, hk]; exact hrp
    exact RingHom.mem_ker.1 hrk

  have hvan : ∀ x ∈ I, x * r = 0 := by
    intro x hx
    apply IsReduced.eq_zero
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro J hJ
    let q : PrimeSpectrum R := ⟨J, hJ⟩
    by_cases hrJ : r ∈ J
    · exact J.mul_mem_left x hrJ
    · apply J.mul_mem_right r
      obtain ⟨L, _, gq, Xq, πq, fq, hkq, hpbq, htrq⟩ := hmem q
      have hu : IsUnit (gq r) := by
        rw [isUnit_iff_ne_zero]
        intro h0
        have hrk : r ∈ RingHom.ker gq := RingHom.mem_ker.2 h0
        rw [hkq] at hrk
        exact hrJ hrk
      have := ((hI L gq Xq πq fq hpbq hu).1 htrq) hx
      rw [RingHom.mem_ker] at this
      show x ∈ q.asIdeal
      rw [← hkq]; exact this
  intro R' _ g' X' π f' hpb' hu'
  refine (hI R' g' X' π f' hpb' hu').2 ?_
  intro x hx
  rw [RingHom.mem_ker]
  have h0 : g' x * g' r = 0 := by rw [← map_mul, hvan x hx, map_zero]
  exact (hu'.mul_left_eq_zero).1 h0

end GlobalTheory.SeesawReduced
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ConnSpread

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw ReciprocityTheory.ChartRestriction.G.Out

theorem preconnectedSpace_of_functions (Y : Scheme.{0})
    (H : ∀ s : Γ(Y, ⊤), Y.basicOpen s = ⊥ ∨ Y.basicOpen s = ⊤) : PreconnectedSpace Y := by
  apply _root_.GlobalTheory.AlgGroup.preconnectedSpace_of_functions <;> assumption

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
      rs X' (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s = AbLaw.cst f' _ c * loc P π f' v i := fun s => by
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

theorem exists_geometricallyConnected_away_of_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (K : Type) [Field K] (x : R →+* K), IsProjOver s → Smooth s → GeometricallyConnected (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ GeometricallyConnected (pullback.snd s (spMap (algebraMap R (Localization.Away f)))) := by
  intro R _ _ Z s K _ x hp hs hc
  have hp' : IsProjBy s := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver s).2 hp
  obtain ⟨P⟩ := nonempty_perf_of_smooth_isProjBy R Z s hs hp' _ (Inh.trivLB_isLB _)
  have hpr : IsProper s := isProper_of_isProjBy R Z s hp'
  have h₀ : IsPullback (pullback.fst s (spMap x)) (pullback.snd s (spMap x)) s
      (Spec.map (CommRingCat.ofHom x)) := IsPullback.of_hasPullback _ _
  have hbij := bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected K _
    (pullback.snd s (spMap x)) inferInstance inferInstance hc
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀, -⟩ := (pullback.snd s (spMap x)).surjective (⊥ : PrimeSpectrum K)
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst s (spMap x)) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul K (0 : Fin P.a → K), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector x P.D₀ v hv0 (hline hbij.2)
  let p : PrimeSpectrum R := s ((pullback.fst s (spMap x)) x₀)
  have hpx : ∀ a : R, a ∉ p.asIdeal → x a ≠ 0 := fun a ha h0 => by
    have e : p = Spec.map (CommRingCat.ofHom x) (pullback.snd s (spMap x) x₀) :=
      congrArg (fun t => t x₀) h₀.w
    apply ha
    rw [e]
    change x a ∈ (pullback.snd s (spMap x) x₀).asIdeal
    rw [h0]
    exact zero_mem _
  obtain ⟨_, ⟨ε, rfl⟩, hε, hεs⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ (Set.range s : Set (PrimeSpectrum R)) from ⟨_, rfl⟩) s.isOpenMap.isOpen_range
  refine ⟨δ * ε, by rw [map_mul]; exact mul_ne_zero hδ (hpx ε hε), ?_⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Y fst snd h => ?_⟩
  let g : R →+* F := (algebraMap (Localization.Away (δ * ε)) F).comp (algebraMap R _)
  have hg : IsUnit (g δ * g ε) := by
    rw [← map_mul]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (δ * ε)) (δ * ε)).map
      (algebraMap (Localization.Away (δ * ε)) F)
  have h' : IsPullback (fst ≫ pullback.fst s (spMap (algebraMap R (Localization.Away (δ * ε))))) snd s
      (Spec.map (CommRingCat.ofHom g)) := by
    have := h.paste_horiz (IsPullback.of_hasPullback s _)
    rwa [← Spec.map_comp] at this
  have hmem : Spec.map (CommRingCat.ofHom g) (⊥ : PrimeSpectrum F) ∈ Set.range s :=
    hεs fun h0 : g ε ∈ (⊥ : Ideal F) => (isUnit_of_mul_isUnit_right hg).ne_zero h0
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨y, -⟩ := Scheme.exists_preimage_of_isPullback h' z _ hz
  have := preconnectedSpace_of_line P h' _ (hker F _ (isUnit_of_mul_isUnit_left hg))
  exact ⟨⟨y⟩⟩

end GlobalTheory.ConnSpread
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.GenericSection
open GlobalTheory.AbLaw GlobalTheory.AbLaw.SecBC

theorem exists_ker_ne_zero {R K K' : Type} [CommRing R] [Field K] [Field K'] (g : R →+* K) (g' : R →+* K')
    (hg : Function.Injective g) {a b : ℕ} (D : Matrix (Fin b) (Fin a) R) (v : Fin a → K) (hv : v ≠ 0)
    (h : (D.map g).mulVec v = 0) : ∃ v' : Fin a → K', v' ≠ 0 ∧ (D.map g').mulVec v' = 0 := by
  by_contra hno
  push Not at hno
  have hind : LinearIndependent K' (fun j : Fin a => fun i : Fin b => (D.map g') i j) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hc0
    push Not at hc0
    have hc' : c ≠ 0 := fun h0 => by
      obtain ⟨j, hj⟩ := hc0
      exact hj (by rw [h0]; rfl)
    apply hno c hc'
    funext i
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  obtain ⟨e, -, he⟩ := GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent K' b (Fin a) _ hind
  have hdet : (D.submatrix e id).det ≠ 0 := by
    intro h0
    apply he
    have : (Matrix.of fun k j => (D.map g') (e k) j) = (D.submatrix e id).map g' := by
      ext k j
      rfl
    have hm := RingHom.map_det g' (D.submatrix e id)
    rw [RingHom.mapMatrix_apply] at hm
    rw [this, ← hm, h0, map_zero]
  have hdetK : ((D.map g).submatrix e id).det ≠ 0 := by
    have : (D.map g).submatrix e id = (D.submatrix e id).map g := rfl
    have hm := RingHom.map_det g (D.submatrix e id)
    rw [RingHom.mapMatrix_apply] at hm
    rw [this, ← hm]
    exact fun h0 => hdet (hg (by rw [h0, map_zero]))
  apply hv
  apply Matrix.eq_zero_of_mulVec_eq_zero hdetK
  funext k
  have := congrFun h (e k)
  simpa [Matrix.mulVec, dotProduct, Matrix.submatrix] using this

def zeroSec {X : Scheme.{0}} (M : LB X) : LB.Sec M where
  f := fun _ => 0
  compat := fun _ _ => by rw [map_zero, map_zero, mul_zero]

theorem exists_sec_iff {X X' Y : Scheme.{0}} {L : LB Y} {p : X ⟶ Y} {R R' : Type} [CommRing R] [CommRing R']
    {f : X ⟶ Spec (CommRingCat.of R)} (F : Perf f (L.pull p)) (g : R →+* R') {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {q : X' ⟶ Y} (e : q = π ≫ p) :
    (∃ (s : (L.pull q).Sec) (j : _), s.f j ≠ 0) ↔ ∃ v : Fin F.a → R', v ≠ 0 ∧ (F.D₀.map g).mulVec v = 0 := by
  subst e
  unfold LB.pull at F ⊢
  let c : R' →+* Γ(X', ⊤) := f'.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom
  obtain ⟨h1, h2, h3⟩ := SecBC.rep_main (F := F) (ψ := fun _ => π ≫ p) (fun _ => rfl) g f' H c (fun _ => rfl)
  have h0 : SecBC.Rep π (fun _ => π ≫ p) F c 0 (zeroSec (L.LinComb (fun _ : PUnit.{1} => π ≫ p) (fun _ => 1))).f := by
    have hs := SecBC.Rep.sum (F := F) (ψ := fun _ => π ≫ p) (c := c) (fun _ => rfl) (I := Empty)
      (w := Empty.elim) (b := Empty.elim) (fun l => l.elim) Empty.elim
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hs
    exact hs
  constructor
  · rintro ⟨s, j, hs⟩
    obtain ⟨v, hv, hrep⟩ := h2 s
    refine ⟨v, fun hv0 => hs ?_, hv⟩
    subst hv0
    rw [SecBC.Rep.sec_eq (fun _ => rfl) hrep h0]
    rfl
  · rintro ⟨v, hv0, hv⟩
    obtain ⟨s, hs⟩ := h1 v hv
    by_contra hno
    push Not at hno
    apply hv0
    have hz : s = zeroSec _ := SecBC.sec_ext (fun j => hno s j)
    rw [hz] at hs
    exact h3 v 0 (zeroSec (L.LinComb (fun _ : PUnit.{1} => π ≫ p) (fun _ => 1))) hv (Matrix.mulVec_zero _) hs h0

theorem exists_ringHom {S : Scheme.{0}} {R K : Type} [CommRing R] [Field K] (t : Sp R ⟶ S) [IsOpenImmersion t]
    (x : Sp K ⟶ S) (h : Set.range x ⊆ Set.range t) :
    ∃ g : R →+* K, Spec.map (CommRingCat.ofHom g) ≫ t = x := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift t x h)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac t x h

theorem exists_isPullback {A S T T' : Scheme.{0}} (a : A ⟶ S) (t : T ⟶ S) (u : T' ⟶ T) (x : T' ⟶ S)
    (h : u ≫ t = x) : ∃ π : pullback a x ⟶ pullback a t,
      IsPullback π (pullback.snd a x) (pullback.snd a t) u ∧ pullback.fst a x = π ≫ pullback.fst a t := by
  subst h
  have hc : pullback.fst a (u ≫ t) ≫ a = (pullback.snd a (u ≫ t) ≫ u) ≫ t := by
    rw [pullback.condition, Category.assoc]
  refine ⟨pullback.lift _ _ hc, ?_, (pullback.lift_fst _ _ hc).symm⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ hc) (IsPullback.of_hasPullback a t)
  rw [pullback.lift_fst]
  exact IsPullback.of_hasPullback a (u ≫ t)

theorem exists_sec_ne_zero_of_generic : Out.Laws → ∀ (S : Scheme.{0}) [IsIntegral S] (P : Out.PolAV S) (N : LB P.A.left) (K K' : Type) [Field K] [Field K'] (x : Sp K ⟶ S) (y : Sp K' ⟶ S) (s : (N.pull (pullback.fst P.A.hom x)).Sec), N.IsLB → Set.range x = {genericPoint S} → (∃ j, s.f j ≠ 0) → ∃ (s' : (N.pull (pullback.fst P.A.hom y)).Sec) (j : _), s'.f j ≠ 0 := by
  intro hLaws S _ P N K K' _ _ x y s hN hx hs
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset
    (show y (IsLocalRing.closedPoint K') ∈ (⊤ : S.Opens) from trivial)
  let t : Sp Γ(S, W) ⟶ S := hW.fromSpec
  have hrange : Set.range t = W := hW.range_fromSpec
  have hgen : genericPoint S ∈ (W : Set S) := by
    rw [(genericPoint_spec S).mem_open_set_iff W.isOpen]
    exact ⟨_, trivial, hyW⟩
  have : Nonempty W := ⟨⟨_, hyW⟩⟩
  have hxr : Set.range x ⊆ Set.range t := by
    rw [hx, hrange]
    simpa using hgen
  have hyr : Set.range y ⊆ Set.range t := by
    rintro _ ⟨z, rfl⟩
    rw [hrange, Subsingleton.elim z (IsLocalRing.closedPoint K')]
    exact hyW
  obtain ⟨gx, hgx⟩ := exists_ringHom t x hxr
  obtain ⟨gy, hgy⟩ := exists_ringHom t y hyr
  have hinj : Function.Injective gx := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hne : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W))).Nonempty :=
      ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa [PrimeSpectrum.mem_basicOpen] using hr0⟩
    have hop : IsOpen (t '' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W)))) :=
      t.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen r).isOpen
    have hg2 : genericPoint S ∈ t '' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W))) := by
      rw [(genericPoint_spec S).mem_open_set_iff hop]
      obtain ⟨q, hq⟩ := hne
      exact ⟨_, trivial, q, hq, rfl⟩
    obtain ⟨q, hq, hqe⟩ := hg2
    have hxpt : x (IsLocalRing.closedPoint K) = genericPoint S := by
      have hm : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rw [hx] at hm
      exact hm
    have hq2 : q = Spec.map (CommRingCat.ofHom gx) (IsLocalRing.closedPoint K) := by
      apply t.isOpenEmbedding.injective
      rw [hqe, ← hxpt, ← hgx]
      rfl
    rw [hq2] at hq
    apply (PrimeSpectrum.mem_basicOpen _ _).1 hq
    show r ∈ (PrimeSpectrum.comap gx (IsLocalRing.closedPoint K)).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hr]
    exact zero_mem _
  have H0 : IsPullback (pullback.fst P.A.hom t) (pullback.snd P.A.hom t) P.A.hom t :=
    IsPullback.of_hasPullback _ _
  obtain ⟨n, -, m, σ, hlb, hva⟩ := polAV_veryAmpleBy hLaws.polBaseChange S P Γ(S, W) t _ _ _ H0
  have : Smooth P.A.hom := by
    have := P.smoothDim
    exact SmoothOfRelativeDimension.smooth P.g P.A.hom
  have hproj : IsProjBy (pullback.snd P.A.hom t) := ⟨_, hlb, m, σ, hva⟩
  obtain ⟨F⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj Γ(S, W) _ (pullback.snd P.A.hom t) inferInstance hproj
    (N.pull (pullback.fst P.A.hom t)) (LB.isLB_pull hN _)
  obtain ⟨πx, hπx, hex⟩ := exists_isPullback P.A.hom t (Spec.map (CommRingCat.ofHom gx)) x hgx
  obtain ⟨πy, hπy, hey⟩ := exists_isPullback P.A.hom t (Spec.map (CommRingCat.ofHom gy)) y hgy
  obtain ⟨v, hv, hker⟩ := (exists_sec_iff F gx hπx hex).1 ⟨s, hs⟩
  obtain ⟨v', hv', hker'⟩ := exists_ker_ne_zero gx gy hinj F.D₀ v hv hker
  exact (exists_sec_iff F gy hπy hey).2 ⟨v', hv', hker'⟩

end GlobalTheory.GenericSection
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.GenTrait

theorem charZero_functionField (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [CharZero W]
    (f : Sp W ⟶ Z) : CharZero Z.functionField := by
  have h1 : CharZero Γ(Z, ⊤) :=
    RingHom.charZero (f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  exact charZero_of_injective_ringHom (Z.germToFunctionField_injective ⊤)

theorem exists_trait_genericPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [IsDomain W] [CharZero W] (_ : Sp W ⟶ Z), ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R), GlobalTheory.LN.CDvr R ∧ ∃ χ : Sp R ⟶ Z, ∀ y, χ y = genericPoint Z := by
  intro Z _ W _ _ _ f
  have := charZero_functionField Z W f
  refine ⟨PowerSeries Z.functionField, inferInstance, inferInstance, inferInstance, ?_,
    spMap (algebraMap Z.functionField (PowerSeries Z.functionField)) ≫
      Z.fromSpecStalk (genericPoint Z), fun y => ?_⟩
  · exact ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance,
      algebraRat.charZero _⟩
  · rw [Scheme.Hom.comp_apply]
    have hy : ∀ p : PrimeSpectrum Z.functionField, p = IsLocalRing.closedPoint Z.functionField :=
      fun p => Subsingleton.elim _ _
    exact (congrArg (Z.fromSpecStalk (genericPoint Z)) (hy _)).trans
      Scheme.fromSpecStalk_closedPoint

end GlobalTheory.GenTrait
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.ampleDeterminantFrames_pullback_of_isAffineHom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Z' : Scheme.{0}) (t : SAB H Z) (t' : SAB H Z') (f : Z' ⟶ Z) (_ : SABMap t' t f) (N : ℕ) (A : GlobalTheory.LN.AmpFrames t.G t.PP.L N), IsAffineHom f → ∃ A' : GlobalTheory.LN.AmpFrames t'.G t'.PP.L N, A'.r = A.r ∧ A'.s = A.s := by
  first | exact @GlobalTheory.AmpPull.ampFrames_pull_of_isAffineHom | exact GlobalTheory.AmpPull.ampFrames_pull_of_isAffineHom | (intros; apply GlobalTheory.AmpPull.ampFrames_pull_of_isAffineHom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

theorem _root_.GlobalTheory.T.exists_sectionPower_transport_cartesian_square : ∀ (Z Z' : Scheme.{0}) (G : Over Z) (G' : Over Z') (f : Z' ⟶ Z) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsPullback φ G'.hom G.hom f → LBIso L' (L.pull φ) → ∀ N : ℕ, ∃ e : ∀ (T' : Over Z') (T : Over Z) (u : T'.left ≅ T.left), u.hom ≫ T.hom = T'.hom ≫ f → (LB.Sec (Out.LPow G' L' (N : ℤ) T') ≃ LB.Sec (Out.LPow G L (N : ℤ) T)), ∀ (T₁' T₂' : Over Z') (T₁ T₂ : Over Z) (u₁ : T₁'.left ≅ T₁.left) (u₂ : T₂'.left ≅ T₂.left) (h₁ : u₁.hom ≫ T₁.hom = T₁'.hom ≫ f) (h₂ : u₂.hom ≫ T₂.hom = T₂'.hom ≫ f) (k' : T₂' ⟶ T₁') (k : T₂ ⟶ T₁), k'.left ≫ u₁.hom = u₂.hom ≫ k.left → ∀ (n : ℕ) (b : Fin n → LB.Sec (Out.LPow G' L' (N : ℤ) T₁')) (c : Fin n → Γ(T₂.left, ⊤)) (s : LB.Sec (Out.LPow G' L' (N : ℤ) T₂')), GlobalTheory.LN.Lin G' L' N k' b (fun i => u₂.hom.appTop.hom (c i)) s ↔ GlobalTheory.LN.Lin G L N k (fun i => e T₁' T₁ u₁ h₁ (b i)) c (e T₂' T₂ u₂ h₂ s) := by
  first | exact @GlobalTheory.SecMove.transport | exact GlobalTheory.SecMove.transport | (intros; apply GlobalTheory.SecMove.transport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.lineBundleIso_of_ampleDeterminantFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Z₁ Z₂ : Scheme.{0}) [IsLocallyNoetherian Z] (z : Z ⟶ Sp ℤ) (t : SAB H Z) (t₁ : SAB H Z₁) (t₂ : SAB H Z₂) (f₁ : Z ⟶ Z₁) (f₂ : Z ⟶ Z₂) (_ : SABMap t t₁ f₁) (_ : SABMap t t₂ f₂) (N : ℕ) (A₁ : GlobalTheory.LN.AmpFrames t₁.G t₁.PP.L N) (A₂ : GlobalTheory.LN.AmpFrames t₂.G t₂.PP.L N), IsNormalScheme Z → Flat z → genericPoints Z ⊆ abLocus t.G → A₁.r = A₂.r → A₁.s = A₂.s → LBIso (A₁.A.pull f₁) (A₂.A.pull f₂) := by
  first | exact @GlobalTheory.FrameCmp.lbIso_of_ampFrames | exact GlobalTheory.FrameCmp.lbIso_of_ampFrames | (intros; apply GlobalTheory.FrameCmp.lbIso_of_ampFrames <;> assumption)
end
