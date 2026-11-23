module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.CmpUnif

theorem thList_smul {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    {ρ : LB.Gen (L.pull (eSec G))} (hL : L.IsLB) {m : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x}
    {a : K} (hθ : SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ) {N : ℕ}
    {pt : Fin N → (Over.mk x ⟶ G)} {c : Fin N → K} (h : ThList G L ρ m x θ pt c) :
    ThList G L ρ m x θ' pt (fun b => a * c b) := by
  have hfn : ∀ u v : K, GlobalTheory.ZH.fn (u * v) = GlobalTheory.ZH.fn u * GlobalTheory.ZH.fn v := fun u v => map_mul _ u v
  refine ⟨h.1, fun b => ?_, h.2.2⟩
  rw [hfn]
  exact ThG.smul hL hθ (h.2.1 b)

theorem cmp_unif : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (_ : Unif (IsLocalRing.maximalIdeal W) D A G) (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing W →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : W) → Odd m' → 3 ≤ m' → IsUnit (m' : W) → (letI := A.isAb.comm; HasTh₂ A.A A.L ρ m m' (spMap io) d d') → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d' b / a) := by
  intro W _ _ _ _ hW D A G _ _ hG U ρ hρ K _ _ io m m' N N' d d' hm hm3 hmu hm' hm3' hmu' hd
  letI := A.isAb.comm
  obtain ⟨-, -, w, hp, -, hw, -⟩ := GlobalTheory.Ex.GenericFibre.exists_isoData W _ D A G U.toUnifPre
  have h₁ := (GlobalTheory.UMin.ThMove.hasTh₂_move _ G U.LG.L U.LG.rig U.LG.isLB U.LG.rigGen _ A.A A.L ρ (jK W) _ A.isLB hρ hp
    ⟨w, hw⟩ m m' N N' K (spMap io) d d').1 hd
  set i : W →+* K := io.comp (algebraMap W (FractionRing W)) with hi
  have hinj : Function.Injective i := io.injective.comp (IsFractionRing.injective W (FractionRing W))
  have ex : spMap io ≫ jK W = spMap i ≫ 𝟙 (Sp W) := by
    rw [Category.comp_id, hi, ← Spec.map_comp]; rfl
  rw [ex] at h₁
  obtain ⟨θ, pt, pt', hθ, hl, hl'⟩ := h₁
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_section_nonzero_uniformised_model_dvr W hW D A G hG U
  obtain ⟨r, hr⟩ := (isGenSec_iff θ).1 hθ (SecM.ofSec G (SecAt.pull G U.LG.L σ i))
  obtain ⟨u, rfl⟩ := (fnR (spMap i ≫ 𝟙 (Sp W))).surjective r
  have hP := GlobalTheory.T.theta_constants_integral_unit_member_uniformised_trait W hW D A G hG U σ hσ m N hm hm3 hmu K i pt _ hinj (thList_smul U.LG.isLB (a := u) hr hl)
  have hP' := GlobalTheory.T.theta_constants_integral_unit_member_uniformised_trait W hW D A G hG U σ hσ m' N' hm' hm3' hmu' K i pt' _ hinj
    (thList_smul U.LG.isLB (a := u) hr hl')
  have hu : u ≠ 0 := by
    obtain ⟨-, b, hb, -⟩ := hP
    exact left_ne_zero_of_mul hb
  refine ⟨u⁻¹, inv_ne_zero hu, ?_, ?_⟩
  · simpa only [div_inv_eq_mul, _root_.mul_comm] using hP
  · simpa only [div_inv_eq_mul, _root_.mul_comm] using hP'

end GlobalTheory.SiegTh.CmpUnif
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.SymRat

theorem grpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sec_eq {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}

theorem thList_congr {m : ℕ} {R : Type} [CommRing R] {x : Sp R ⟶ S} (θ : SecAt G L x) {K : Type} [Field K]
    {y y' : Sp K ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x) (hu : u.left = u'.left)
    {N : ℕ} {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y (VVRank.pullS G _ u θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) pt' c := by
  subst e
  obtain rfl : u = u' := Over.OverMorphism.ext hu
  exact ⟨pt, H⟩

end GlobalTheory.UMin.SymRat

namespace GlobalTheory.UMin.SymRat

theorem symAt_exists : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω]
    (x : Sp Ω ⟶ S) (θ : SecAt G L x), Odd m → N = m ^ (4 * g) → PolFib G L g x → ∃ e : Fin N → Ω, SymAt G L ρ m x θ e := by
  intro S G _ _ L ρ hL hρ g m N Ω _ _ x θ hm hN hP
  obtain ⟨Ω', instF, instA, pt₀, c₀, hfd, hgal, -, hT, hτ⟩ := GlobalTheory.T.theta_constants_listed_finite_galois_extension S G L ρ hL hρ g m N Ω x θ hm hN hP
  haveI := hfd
  haveI := hgal
  have sb := GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_basic_properties
  have hfix : ∀ j, ∃ e : Ω, algebraMap Ω Ω' e = symTup c₀ j := by
    intro j
    have hm : symTup c₀ j ∈ Set.range (algebraMap Ω Ω') := (IsGalois.mem_range_algebraMap_iff_fixed _).2 fun τ => by
      obtain ⟨σ, hσ⟩ := hτ τ
      have e1 : τ (symTup c₀ j) = symTup (fun b => τ (c₀ b)) j := sb.2.2.1 Ω' Ω' (τ : Ω' →+* Ω') N c₀ j
      rw [e1, show (fun b => τ (c₀ b)) = fun b => c₀ (σ b) from funext hσ, sb.2.1 Ω' N c₀ σ]
    obtain ⟨e, he⟩ := hm
    exact ⟨e, he⟩
  choose e he using hfix
  refine ⟨e, ?_⟩
  intro K _ i pt c hc j
  let k : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  letI : Algebra Ω (AlgebraicClosure K) := (k.comp i).toAlgebra
  haveI : Algebra.IsAlgebraic Ω Ω' := Algebra.IsAlgebraic.of_finite Ω Ω'
  let jj : Ω' →ₐ[Ω] AlgebraicClosure K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hcomp : (jj : Ω' →+* AlgebraicClosure K).comp (algebraMap Ω Ω') = k.comp i :=
    RingHom.ext fun r => jj.commutes r
  obtain ⟨p1, -, h1⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S G L ρ hL hρ m N Ω' (AlgebraicClosure K) (jj : Ω' →+* AlgebraicClosure K) _ _ pt₀ c₀ hT
  obtain ⟨p2, -, h2⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S G L ρ hL hρ m N K (AlgebraicClosure K) k _ _ pt c hc
  simp only [SecAt.pull] at h1 h2
  rw [pullS_comp G hL] at h1 h2
  have ey1 : spMap (jj : Ω' →+* AlgebraicClosure K) ≫ spMap (algebraMap Ω Ω') ≫ x = spMap (k.comp i) ≫ x := by
    rw [← Category.assoc, spMap_comp_ring, hcomp]
  have ey2 : spMap k ≫ spMap i ≫ x = spMap (k.comp i) ≫ x := by
    rw [← Category.assoc, spMap_comp_ring]
  obtain ⟨q1, H1⟩ := thList_congr θ ey1 _ (Over.homMk (spMap (k.comp i)) rfl : Over.mk (spMap (k.comp i) ≫ x) ⟶ Over.mk x)
    (by simp only [Over.comp_left, Over.homMk_left]; rw [spMap_comp_ring, hcomp]) h1
  obtain ⟨q2, H2⟩ := thList_congr θ ey2 _ (Over.homMk (spMap (k.comp i)) rfl : Over.mk (spMap (k.comp i) ≫ x) ⟶ Over.mk x)
    (by simp only [Over.comp_left, Over.homMk_left]; rw [spMap_comp_ring]) h2
  have hPy : PolFib G L g (spMap (k.comp i) ≫ x) :=
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S G L G L (𝟙 S) (𝟙 G.left) hL hL (grpPullback_self G) (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hL) g Ω
      x).2 (AlgebraicClosure K) (k.comp i) hP
  have hmAC : (m : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast (k.comp i) m]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hm.pos.ne')
  obtain ⟨σ, hσ⟩ := (GlobalTheory.T.thetaConstantLists_unique_up_to_perm_scalar S G L ρ hL hρ g m m N N (AlgebraicClosure K) (spMap (k.comp i) ≫ x) hm hmAC hm hmAC
    hPy).1 _ q2 q1 _ _ H2 H1
  apply k.injective
  calc k (i (e j)) = jj (algebraMap Ω Ω' (e j)) := (RingHom.congr_fun hcomp (e j)).symm
    _ = jj (symTup c₀ j) := by rw [he]
    _ = symTup (fun b => jj (c₀ b)) j := sb.2.2.1 _ _ (jj : Ω' →+* AlgebraicClosure K) _ _ _
    _ = symTup (fun b => k (c (σ b))) j := by rw [show (fun b => jj (c₀ b)) = fun b => k (c (σ b)) from funext hσ]
    _ = symTup (fun b => k (c b)) j := by rw [sb.2.1 _ N (fun b => k (c b)) σ]
    _ = k (symTup c j) := (sb.2.2.1 _ _ k _ _ _).symm

end GlobalTheory.UMin.SymRat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem pCrd_of_symAt : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (q : X ⟶ S) (f : X ⟶ PSpace o n) (S' : Scheme.{0}) (A : Over S') [GrpObj A] [IsCommMonObj A] (L' : LB A.left) (ρ' : LB.Gen (L'.pull (eSec A))) (Ω : Type) [Field Ω] [CharZero Ω] (x : Sp Ω ⟶ X) (x' : Sp Ω ⟶ S') (P : PolAV (Sp Ω)) (α : P.A.left ⟶ G.left) (α' : P.A.left ⟶ A.left) (θ : SecAt A L' x') (e : Fin (n + 1) → Ω), Odd m → n + 1 = m ^ (4 * g) → ThMap G L ρ m q f → L'.IsLB → ρ'.IsGen → P.g = g → IsGrpPullback P.A G (x ≫ q) α → LBIso P.L (L.pull α) → IsGrpPullback P.A A x' α' → LBIso P.L (L'.pull α') → IsGenSec A L' _ θ → SymAt A L' ρ' m x' θ e → PCrd (x ≫ f) e := by
  intro S G _ _ L ρ hL hρ g m n o _ X q f S' A _ _ L' ρ' Ω _ _ x x' P α α' θ e hm hn hf hL' hρ' hg hα hw hα' hw' hθ he
  have hpol : PolFib A L' g x' := ⟨P, α', hg, hα', hw'⟩
  obtain ⟨Ω', _, _, pt, c, -, -, -, hl, -⟩ := GlobalTheory.T.theta_constants_listed_finite_galois_extension S' A L' ρ' hL' hρ' g m (n + 1) Ω x' θ hm hn hpol
  have hgen := (GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable S' A L' hL' g Ω x' hpol).2 θ hθ Ω' (algebraMap Ω Ω')
  have h₁ : HasTh₂ A L' ρ' m m (spMap (algebraMap Ω Ω') ≫ x') c c := hasTh_iff.1 ⟨_, pt, hgen, hl⟩
  obtain ⟨w, hw₀⟩ := id hw
  obtain ⟨ρP, hρP, -⟩ := exists_rigidificationPullbackCompatibleIso hα hw₀ hL P.isLB hρ
  haveI : IsCommMonObj P.A := P.isAb.comm
  have h₂ := (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian S' A L' ρ' hL' hρ' _ P.A P.L ρP x' α' P.isLB hρP hα' hw' m m _ _ Ω' _ c c).2 h₁
  have h₃ := (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian S G L ρ hL hρ _ P.A P.L ρP (x ≫ q) α P.isLB hρP hα hw m m _ _ Ω' _ c c).1 h₂
  rw [← Category.assoc] at h₃
  have h₄ := hf Ω' _ c (hasTh_iff.2 h₃)
  refine GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend.2.2 o Ω Ω' n _ e (algebraMap Ω Ω') ?_
  rw [← Category.assoc, funext (he Ω' _ pt c hl)]
  exact h₄

end GlobalTheory.UMin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.generates_sections_of_thetaSymmetricFunctions_ne_zero : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (x : Sp Ω ⟶ S) (θ : SecAt G L x) (e : Fin N → Ω), Odd m → N = m ^ (4 * g) → PolFib G L g x → SymAt G L ρ m x θ e → (∃ j, e j ≠ 0) → IsGenSec G L ((1 : ℕ) : ℤ) θ := by
  first | exact @GlobalTheory.UMin.GenSym.isGenSec_of_symAt | exact GlobalTheory.UMin.GenSym.isGenSec_of_symAt | (intros; apply GlobalTheory.UMin.GenSym.isGenSec_of_symAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)), Nonempty (SABMap t' t χ) → Nonempty (PELUnif (IsLocalRing.maximalIdeal V) t') → ∀ (σ : SecAt t.G t.PP.L χ), NZ t.G t.PP.L χ σ → ∀ (m N : ℕ), Odd m → 3 ≤ m → IsUnit (m : V) → ∀ (K : Type) [Field K] (i : V →+* K) (pt : Fin N → (Over.mk (spMap i ≫ χ) ⟶ t.G)) (c : Fin N → K), Function.Injective i → ThList t.G t.PP.L t.PP.rig m (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c → Prim i c := by
  first | exact @GlobalTheory.UMin.PrimTrait.main | exact GlobalTheory.UMin.PrimTrait.main | (intros; apply GlobalTheory.UMin.PrimTrait.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstantList_fieldExtension_eq_up_to_perm : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (K F : Type) [Field K] [Field F] (i : R →+* K) (i' : R →+* F) (φ : K →+* F), φ.comp i = i' → ∀ (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G)) (c : Fin N → K) (pt' : Fin N → (Over.mk (spMap i' ≫ x) ⟶ G)) (c' : Fin N → F), ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt c → ThList G L ρ m (spMap i' ≫ x) (SecAt.pull G L θ i') pt' c' → ∃ σ : Equiv.Perm (Fin N), ∀ b, c' b = φ (c (σ b)) := by
  first | exact @GlobalTheory.UMin.SymCmp.thList_ext_perm | exact GlobalTheory.UMin.SymCmp.thList_ext_perm | (intros; apply GlobalTheory.UMin.SymCmp.thList_ext_perm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaMap_finite_geometricFibres_of_large_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (j n : ℕ) (f : Xo.XF c ⟶ PSpace o n), 81 ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)).factorial < 3 ^ j * 81 → n + 1 = (3 ^ j * 81) ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (3 ^ j * 81) (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.XF c), Set.Finite {y : Sp K ⟶ Xo.XF c | y ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ ∧ y ≫ f = x ≫ f} := by
  first | exact @GlobalTheory.UMin.QF.finite_fibre_thMap | exact GlobalTheory.UMin.QF.finite_fibre_thMap | (intros; apply GlobalTheory.UMin.QF.finite_fibre_thMap <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr

theorem exists_bound_nsq {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (M : HermLB p) (u : M.B.Sec) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), (M.φ σ).nsq (CxPts.secVal p σ u) y ≤ C := by
  have := hX.finite_emb
  have hb : ∀ σ : k →+* ℂ, ∃ K : ℝ, ∀ y, (M.φ σ).nsq (CxPts.secVal p σ u) y ≤ K := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨K, hK⟩ := (isCompact_range ((M.cInf σ).continuous_nsq u)).bddAbove
    exact ⟨K, fun y => hK ⟨y, rfl⟩⟩
  choose K hK using hb
  have := Fintype.ofFinite (k →+* ℂ)
  refine ⟨∑ τ, |K τ| + 1, ?_, fun σ y => (hK σ y).trans ?_⟩
  · linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)]
  · have := Finset.single_le_sum (fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)) (Finset.mem_univ σ)
    linarith [le_abs_self (K σ)]

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

def Pair.shiftA (P : Pair p) (c : ℝ) : Pair p :=
  ⟨P.L, P.A.shift (fun _ => c) (fun _ => rfl), P.r, P.r', P.hr, P.hr'⟩

theorem Pair.nu_shiftA (P : Pair p) (c : ℝ) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    (P.shiftA c).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * c)) := by
  simp only [Pair.shiftA, Pair.nu, Pair.loc, HermLB.shift, Weight.addFn]
  have key : ∀ (n u v w : ℝ), n * Real.exp (-(u + v * (w + 2 * c)) / 2) =
      n * Real.exp (-(u + v * w) / 2) * Real.exp (-(v * c)) := by
    intro n u v w
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  exact key _ _ _ _

theorem Pair.nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f := by
  unfold Pair.nu; positivity

theorem not_unitAt_zero (x : X) : ¬ UnitAt x (0 : X.functionField) := by
  rintro ⟨a, ha, h⟩
  exact (ha.map (algebraMap _ X.functionField)).ne_zero h

end GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem exists_good_pair : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ L : HermLB p, ∃ (P : Pair p) (b : ℕ) (s t : X.functionField), P.L = L ∧ P.Good D b s t := by
  intro hC k _ X _ p D hX L
  obtain ⟨A₀, hAmp, hNef, s₀, hs₀, hs₀ne⟩ := GlobalTheory.T.exists_ample_nef_hermitian_smallSection hC k X p D hX
  obtain ⟨P, rfl, rfl⟩ := exists_pair L A₀
  have hrep := GlobalTheory.T.represents_base_bundles_and_trivial k X p P

  obtain ⟨e, -, he_rng, he_nu, he_loc⟩ := GlobalTheory.T.representedBundle_sections_rationalFunctions_dict k X p P 0 1 P.A hrep.2.1
  have hsH : e s₀ ∈ P.H 0 1 := by
    show e s₀ ∈ (P.H 0 1 : Set X.functionField)
    rw [← he_rng]; exact ⟨s₀, rfl⟩
  have hη : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s₀ := (GlobalTheory.sec_ne_zero_iff s₀).1 hs₀ne
  obtain ⟨i₀, hi₀⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart P.L.isLB (genericPoint X)
  obtain ⟨j₀, hj₀⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart P.A.isLB (genericPoint X)
  have hsne : e s₀ ≠ 0 := by
    intro h0
    have hu := (he_loc s₀ _ i₀ j₀ hi₀ hj₀).1 hη
    rw [h0] at hu
    exact not_unitAt_zero _ (by simpa [Pair.loc] using hu)
  have hs_le : ∀ σ y, P.nu 0 1 σ y (e s₀) ≤ 1 := fun σ y => by
    have h1 := he_nu s₀ σ y
    have h2 := hs₀ σ y
    have h3 := P.nu_nonneg 0 1 σ y (e s₀)
    nlinarith

  obtain ⟨S, hSfin, hS⟩ := GlobalTheory.T.exists_finite_set_controlling_regularity_of_quotient k X p D hX P (e s₀) hsH hsne

  obtain ⟨b, hb, u, hu⟩ := GlobalTheory.T.exists_section_ampleTwist_nonvanishing_finiteSet k X p D hX P.L.dual P.A hAmp (insert (genericPoint X) S) (hSfin.insert _)
  have hR1 : P.Rep (-1) 0 P.L.dual := by simpa using GlobalTheory.T.represents_hermitianLineBundle_dual k X p P 1 0 P.L hrep.1
  have hR2 : P.Rep 0 b (P.A.pow b) := by simpa using GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A b hrep.2.1
  have hR : P.Rep (-1) b (P.L.dual.tens (P.A.pow b)) := by
    simpa using GlobalTheory.T.hermPairWithSections_represents_tensor k X p P (-1) 0 0 b _ _ hR1 hR2
  obtain ⟨e', -, he'_rng, he'_nu, he'_loc⟩ := GlobalTheory.T.representedBundle_sections_rationalFunctions_dict k X p P (-1) b _ hR
  have htH : e' u ∈ P.H (-1) b := by
    show e' u ∈ (P.H (-1) b : Set X.functionField)
    rw [← he'_rng]; exact ⟨u, rfl⟩
  have htne : e' u ≠ 0 := by
    intro h0
    have hv := (he'_loc u _ i₀ j₀ hi₀ hj₀).1 (hu (Set.mem_insert _ _))
    rw [h0] at hv
    exact not_unitAt_zero _ (by simpa [Pair.loc] using hv)
  obtain ⟨C, hC1, hCb⟩ := exists_bound_nsq hX _ u
  have ht_le : ∀ σ y, P.nu (-1) b σ y (e' u) ≤ C := fun σ y => by
    have h1 := he'_nu u σ y
    have h2 := hCb σ y
    have h3 := P.nu_nonneg (-1) b σ y (e' u)
    nlinarith

  set c := Real.log C with hc
  have hc0 : 0 ≤ c := Real.log_nonneg hC1
  have hCpos : 0 < C := by linarith
  have hexpc : Real.exp (-c) = C⁻¹ := by rw [Real.exp_neg, hc, Real.exp_log hCpos]
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hexpb : Real.exp (-((b : ℤ) * c)) ≤ C⁻¹ := by
    rw [← hexpc]; apply Real.exp_le_exp.2; push_cast; nlinarith
  refine ⟨P.shiftA c, b, e s₀, e' u, rfl, ?_⟩
  have hsub : ∀ (z x : X) (U : X.Opens), z ⤳ x → x ∈ U → z ∈ U := fun z x U h hx => h.mem_open U.isOpen hx
  exact {
    ample := hAmp
    nef := GlobalTheory.T.hermitianLineBundle_isNef_shift_of_nonneg k X p D hX P.A c hc0 hNef
    pos := hb
    s_mem := ⟨hsH, fun σ y => by
      rw [Pair.nu_shiftA]
      have := hs_le σ y
      have h4 : Real.exp (-(((1 : ℤ) : ℝ) * c)) ≤ 1 := by
        apply Real.exp_le_one_iff.2; push_cast; linarith
      have h5 := P.nu_nonneg 0 1 σ y (e s₀)
      nlinarith [Real.exp_pos (-(((1 : ℤ) : ℝ) * c))]⟩
    s_ne := hsne
    t_mem := ⟨htH, fun σ y => by
      rw [Pair.nu_shiftA]
      have := ht_le σ y
      have h5 := P.nu_nonneg (-1) b σ y (e' u)
      calc P.nu (-1) b σ y (e' u) * Real.exp (-((b : ℤ) * c)) ≤ C * C⁻¹ :=
            mul_le_mul this hexpb (Real.exp_pos _).le hCpos.le
        _ = 1 := mul_inv_cancel₀ hCpos.ne'⟩
    t_ne := htne
    reg := fun x i j hi hj g hg h1 => hS x i j hi hj (P.loc (-1) b (e' u) i j) g (htH x i j hi hj)
      (fun z hz hzx => (he'_loc u z i j (hsub z x _ hzx hi) (hsub z x _ hzx hj)).1 (hu (Set.mem_insert_of_mem _ hz)))
      hg h1 }

end GlobalTheory.VolBr
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_twist_nef_squarefree_monomials_small : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (N : HermLB p) (x : Fin D → X.functionField), ∃ H : HermLB p, (N.tens H).IsNef D ∧ ∀ W : HermLB p, ∃ P : Pair p, P.L = W ∧ P.A = H ∧ ∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1 := by
  first | exact @GlobalTheory.HSNef.BoxTwist.exists_twist | exact GlobalTheory.HSNef.BoxTwist.exists_twist | (intros; apply GlobalTheory.HSNef.BoxTwist.exists_twist <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.mixedHeight_pow_eq_degree_log_card_finiteField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ (m : ℕ) T, IsMix p m T → ∀ (N : HermLB p) (d : ℕ), d ≤ m → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = d → T d (fun _ => N) (i (genericPoint Z)) = topSelfIntersection κ (N.B.pull i) d * Real.log (Nat.card κ) := by
  first | exact @GlobalTheory.MixHtVert.mixHt_pow_eq_topSelf | exact GlobalTheory.MixHtVert.mixHt_pow_eq_topSelf | (intros; apply GlobalTheory.MixHtVert.mixHt_pow_eq_topSelf <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections : ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (s : M.B.Sec) (t : N.B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) = recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) := by
  first | exact @GlobalTheory.MixHt.recVal_cons_recip | exact GlobalTheory.MixHt.recVal_cons_recip | (intros; apply GlobalTheory.MixHt.recVal_cons_recip <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.principalDivisor_degree_zero_finiteField_curve : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (1 : ℕ) → ∀ (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Y, ⊤)] (f : Y.functionField), f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = 0 := by
  first | exact @GlobalTheory.PrincDegZero.finsum_ord_mul_log_card_eq_zero | exact GlobalTheory.PrincDegZero.finsum_ord_mul_log_card_eq_zero | (intros; apply GlobalTheory.PrincDegZero.finsum_ord_mul_log_card_eq_zero <;> assumption)
end
