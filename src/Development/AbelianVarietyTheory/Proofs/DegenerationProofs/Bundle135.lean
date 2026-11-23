module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle124
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle039
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle127
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle121
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.HasFields

theorem cdv_powerSeries (k : Type) [Field k] [CharZero k] : CDV (PowerSeries k) := by
  have hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have h0 : CharZero (PowerSeries k) := algebraRat.charZero _
  exact (GlobalTheory.LN.cDvr_iff _).2 ⟨inferInstance, hc, h0⟩

theorem exists_lift (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [FaithfulSMul R K] [Algebra.IsAlgebraic R K] [Field L] [IsAlgClosed L] (ψ : R →+* L)
    (hψ : Function.Injective ψ) : ∃ e : K →+* L, ∀ x, e (algebraMap R K x) = ψ x := by
  letI : Algebra R L := ψ.toAlgebra
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).2 hψ
  let e : K →ₐ[R] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨e, fun x => e.commutes x⟩

theorem exists_cdv_over_powerSeries : ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (K : Type) [Field K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : PowerSeries O' →+* W) (K₁ : Type) (_ : Field K₁) (_ : Algebra (FractionRing W) K₁) (_ : Algebra.IsAlgebraic (FractionRing W) K₁) (e : K →+* K₁), CDV W ∧ φ PowerSeries.X ∈ IsLocalRing.maximalIdeal W ∧ ∀ x, e (algebraMap (PowerSeries O') K x) = algebraMap (FractionRing W) K₁ (algebraMap W _ (φ x)) := by
  intro O' _ _ _ K _ _ _ _
  let F := FractionRing O'
  haveI : CharZero F := IsFractionRing.charZero_of_isFractionRing O'
  let W := PowerSeries F
  let φ : PowerSeries O' →+* W := PowerSeries.map (algebraMap O' F)
  have hφ : Function.Injective φ :=
    PowerSeries.map_injective _ (IsFractionRing.injective O' F)
  let K₁ := AlgebraicClosure (FractionRing W)
  let ψ : PowerSeries O' →+* K₁ :=
    (algebraMap (FractionRing W) K₁).comp ((algebraMap W (FractionRing W)).comp φ)
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing W) K₁).injective.comp
      ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  have key : ∃ e : K →+* K₁, ∀ x, e (algebraMap (PowerSeries O') K x) = ψ x :=
    exists_lift _ K K₁ ψ hψ
  obtain ⟨e, he⟩ := key
  refine ⟨W, inferInstance, inferInstance, inferInstance, φ, K₁, inferInstance, inferInstance,
    inferInstance, e, cdv_powerSeries F, ?_, he⟩
  rw [PowerSeries.maximalIdeal_eq_span_X]
  have hX : φ PowerSeries.X = PowerSeries.X := PowerSeries.map_X _
  rw [hX]
  exact Ideal.subset_span rfl

end GlobalTheory.HasFields
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.preUniformisation_comparison_torus_invariant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D D' : DegPre R) (A A' : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (U' : PreU I D' A' G) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))) (hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _), IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL → ∀ (e : ℕ) (β : thickObj R I e D'.P.A ≅ thickObj R I e D.P.A), (U'.gt e).q ≫ β.hom = (U.gt e).q → ∀ u : LB.Iso (D'.P.L.pull (U'.gt e).pG.left) (D.P.L.pull (U.gt e).pG.left), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' → (fstG I e G).left (r z) ∈ U.P.L.L.U jL → (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' → gw u r z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') = gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL') → ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (jM : D.P.L.ι) (jM' : D'.P.L.ι), (U.gt e).pG.left (y.left z) ∈ D.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.P.L.U jM' → gw u ((τ ≫ (U.gt e).i) * y).left z jM (fun _ => jM') = gw u y.left z jM (fun _ => jM') := by
  first | exact @GlobalTheory.preU_comparison_torus_invariant | exact GlobalTheory.preU_comparison_torus_invariant | (intros; apply GlobalTheory.preU_comparison_torus_invariant <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem exists_setting_of_hypS : Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField V)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj G)) → HypS A.A A.L → ∀ gen : (Over.pullback (jK V)).obj G ≅ A.A, IsMonHom gen.hom → ∃ s : GlobalTheory.UU.HidaSetting V A G, s.gen = gen := by
  intro laws hext V _ _ hd _ hc A G _ _ hG hE hS gen hgen
  have hV : GlobalTheory.UU.CDVR V := ⟨hd, hc, inferInstance⟩
  obtain ⟨L, hL⟩ := GlobalTheory.UU.polarisation_extends laws V A G hG gen hgen
  obtain ⟨P, rfl⟩ := GlobalTheory.CubicalPackage.exists_package laws V hV A G hG gen hgen L hL
  obtain ⟨w, -, hw, -, -, hiso, -⟩ := GlobalTheory.T.symmetryHyp_extends_semiAbelian_dvr hext V A G hG hS gen hgen P.L hL
  obtain ⟨E, ⟨d⟩⟩ := hE
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue V))).obj G) := Functor.isCommMonObj_obj
  obtain ⟨r, hr⟩ := GlobalTheory.UU.thick_zero_factor V
  obtain ⟨Q₀⟩ := GlobalTheory.UU.nonempty_tq_pullback_comp r _ hr G (GlobalTheory.UU.TQ.ofGtDatum d)
  obtain ⟨P₀, h₀⟩ := GlobalTheory.UU.exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P
  obtain ⟨wA, hwA⟩ := hL
  have := E.free
  have := E.finite
  exact ⟨⟨hV, hG, gen, hgen, P, wA, hwA, E.X, Q₀, P₀, h₀,
    GlobalTheory.T.exists_even_cubical_trivialisation_specialFibre laws V hV A G hG gen hgen P w hw hiso E.X Q₀ P₀ h₀⟩, rfl⟩

end GlobalTheory.ZH
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.exists_psi_generating_on_whole_spectrum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ ψ h, Nonempty (PsiOn (setPsi D ψ h) ⊤) := by
  first | exact @GlobalTheory.PsiTop.exists_setPsi_psiOn_top | exact GlobalTheory.PsiTop.exists_setPsi_psiOn_top | (intros; apply GlobalTheory.PsiTop.exists_setPsi_psiOn_top <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.isCubicalBundleMap_of_pulled_back_degeneration : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (hD : IsPullDeg φ D D'), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (pull_grp hD).1.w hD.w := by
  first | exact @GlobalTheory.DegPullPackage.isCPMap_of_isPullDeg | exact GlobalTheory.DegPullPackage.isCPMap_of_isPullDeg | (intros; apply GlobalTheory.DegPullPackage.isCPMap_of_isPullDeg <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecBasis

theorem exists_sec_of_ker {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)}
    {M : LB Y} (P : Perf f M) (v : Fin P.a → R) (hv : P.D₀.mulVec v = 0) :
    ∃ s : LB.Sec M, ∀ i, rs Y (P.le i) (s.f (P.ch i)) = Seesaw.loc₀ P v i := by
  have h : IsPullback (𝟙 Y) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E, hE⟩ := P.sec R (RingHom.id R) Y (𝟙 Y) f h
  let t := E ⟨v, hv⟩
  have le : ∀ j, M.U j ≤ (M.pull (𝟙 Y)).U (fun _ => j) := fun j => le_pull M (𝟙 Y) le_rfl
  refine ⟨⟨fun j => rs Y (le j) (t.f fun _ => j), fun i j => ?_⟩, fun i => ?_⟩
  · have e := GlobalTheory.LB.sec_rel t (fun _ => i) (fun _ => j) (inf_le_left.trans (le i))
      (inf_le_right.trans (le j)) (inf_le_inf (le i) (le j))
    have e' := (GlobalTheory.LB.resG_pull_g (L := M) (𝟙 Y) (fun _ => i) (fun _ => j)
      (inf_le_inf (le i) (le j))).trans (rs_self _ _)
    exact (rs_rs _ _ _).trans (e.trans (congrArg₂ (· * ·) e' (rs_rs _ _ _).symm))
  · exact (rs_rs _ _ _).trans (hE ⟨v, hv⟩ i)

theorem exists_sec_iso {X X' : Scheme.{0}} {β : X' ⟶ X} {M : LB X} {M' : LB X'} (hM : M.IsLB) (hM' : M'.IsLB)
    (w : LB.Iso M' (M.pull β)) (hw : w.IsGen) (s : LB.Sec M') :
    ∃ t : LB.Sec (M.pull β), ∀ z k k', β z ∈ M.U k → z ∈ M'.U k' →
      gs (𝟙 X') z _ (t.f fun _ => k) = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 X') z _ (s.f k') := by
  refine ⟨SecOn.topEquiv _ (SecOn.congr hM' (LB.isLB_pull hM β) w hw ⊤ ((SecOn.topEquiv M').symm s)),
    fun z k k' hk hk' => ?_⟩
  have hz : z ∈ (M.pull β).U (fun _ => k) ⊓ M'.U k' := ⟨mem_pull.2 hk, hk'⟩
  have e := congrArg (gs (𝟙 X') z _) (SecOn.coord_congr hM' (LB.isLB_pull hM β) w hw
    ((SecOn.topEquiv M').symm s) (fun _ => k) k' (le_inf le_top inf_le_left) (le_inf le_top inf_le_right) le_rfl)
  rw [gs_mul _ _ _ hz, gs_res _ _ _ hz, gs_res _ _ _ hz, gs_res _ _ _ hz] at e
  refine (gs_res _ _ _ hz.1 _).trans (e.trans (congrArg₂ (· * ·) (gs_unit _ _ _ hz _) ?_))
  exact gs_res (𝟙 X') z (inf_le_right : ⊤ ⊓ M'.U k' ≤ _) ⟨trivial, hk'⟩ (s.f k')

theorem gs_comb {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (z : X)
    {U : X.Opens} (h : z ∈ U) {n : ℕ} (c : Fin n → R) (x : Fin n → Γ(X, U)) :
    gs (𝟙 X) z U (∑ j, AbLaw.cst f U (c j) * x j) = ∑ j, gs (𝟙 X) z ⊤ (AbLaw.cst f ⊤ (c j)) * gs (𝟙 X) z U (x j) := by

  rw [gs_eq _ _ _ h, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← gs_eq _ _ _ h, gs_mul _ _ _ h, ← rs_cst f (le_top : U ≤ ⊤), gs_res _ _ _ h]

theorem loc_mulVec {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (P : Perf f M) (π : X' ⟶ X)
    (f' : X' ⟶ Spec (CommRingCat.of R')) {n : ℕ} (B : Matrix (Fin P.a) (Fin n) R') (c : Fin n → R') (i : P.I) :
    Seesaw.loc P π f' (B.mulVec c) i = ∑ j, AbLaw.cst f' _ (c j) * Seesaw.loc P π f' (fun k => B k j) i := by

  simp only [Seesaw.loc, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem exists_basis : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∃ (n : ℕ) (τ : Fin n → LB.Sec M), ∀ (A' : Type) [CommRing A'] (g : A →+* A') (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)) (τ' : Fin n → LB.Sec M'), M'.IsLB → w.IsGen → (∀ i, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((τ i).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((τ' i).f k'))) → ∀ s' : LB.Sec M', ∃! c : Fin n → A', ∀ k : M'.ι, s'.f k = ∑ i, AbLaw.cst f' (M'.U k) (c i) * (τ' i).f k := by
  intro A _ _ _ X f hf hp M hM K _ g₀ hg₀ X₀ π f₀ h₀ M₀ w₀ hM₀ hw₀ hH
  obtain ⟨P⟩ := nonempty_perf_of_noetherian A X f hf hp M hM
  obtain ⟨w₁, hw₁⟩ := LBIso.symm (⟨w₀, hw₀⟩ : LBIso _ _)
  obtain ⟨r, n, B, hr, hB, hu⟩ := exists_matrix_basis_ker_of_exact_at_point A K g₀ _ _ _ P.D₀ P.D₁
    P.comp (P.exact K g₀ X₀ π f₀ h₀ (H1Iso.firstCohomologyVanishes_of_iso_of_isGen hM₀.cover (LB.isLB_pull hM π) w₁ hw₁ hH))
  have hru : IsUnit r := by
    by_contra hn
    have := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g₀ hg₀)
    exact hr ((RingHom.mem_ker).1 (this ▸ (show r ∈ IsLocalRing.maximalIdeal A from hn)))
  choose τ hτ using fun j => exists_sec_of_ker P (fun k => B k j) (funext fun l => congrFun₂ hB l j)
  refine ⟨n, τ, fun A' _ g X' β f' h M' w τ' hM' hw hτ' s' => ?_⟩
  obtain ⟨E, hE⟩ := P.sec A' g X' β f' h
  obtain ⟨t, ht⟩ := exists_sec_iso hM hM' w hw s'
  obtain ⟨v, rfl⟩ := E.surjective t
  have hA : ∀ z i k', β z ∈ P.W i → z ∈ M'.U k' → gs (𝟙 X') z _ (Seesaw.loc P β f' v.1 i) =
      (Geo.Tor.gw w (𝟙 _) z (P.ch i) k').val * gs (𝟙 X') z _ (s'.f k') := fun z i k' hi hk' =>
    (congrArg (gs (𝟙 X') z _) (hE v i).symm).trans ((gs_res (𝟙 X') z (le_pull M β (P.le i)) hi _).trans (ht z _ k' (P.le i hi) hk'))
  have hC : ∀ (c : Fin n → A') z i k', β z ∈ P.W i → z ∈ M'.U k' →
      gs (𝟙 X') z _ (Seesaw.loc P β f' ((B.map g).mulVec c) i) =
      (Geo.Tor.gw w (𝟙 _) z (P.ch i) k').val *
        gs (𝟙 X') z _ (∑ j, AbLaw.cst f' (M'.U k') (c j) * (τ' j).f k') := fun c z i k' hi hk' => by
    rw [loc_mulVec, gs_comb f' z (show z ∈ β ⁻¹ᵁ P.W i from hi), gs_comb f' z hk', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm, ← hτ' j z _ k' (P.le i hi) hk']
    refine congrArg (_ * ·) ?_
    refine (congrArg (gs (𝟙 X') z _) (Seesaw.loc_comp P h (fun k => B k j) i)).trans ?_
    rw [← hτ j i]
    refine (gs_pull (𝟙 X') β z _ hi _).trans ?_
    rw [Category.id_comp]
    exact gs_res β z _ hi _
  refine (existsUnique_congr fun c => ⟨fun hc k' => fn_ext fun z hz => ?_, fun hc => ?_⟩).1
    (hu A' g (hru.map g) v.1 v.2)
  · obtain ⟨i, hi⟩ := Seesaw.exists_mem P (β z)
    have e := hC c z i k' hi hz
    rw [hc, hA z i k' hi hz] at e
    exact (Units.mul_right_inj _).1 e
  · have hk : (P.D₀.map g).mulVec ((B.map g).mulVec c) = 0 := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hB, Matrix.map_zero _ (map_zero g), Matrix.zero_mulVec]
    refine congrArg Subtype.val (E.injective (a₁ := ⟨_, hk⟩) (a₂ := v) ?_)
    refine Seesaw.sec_ext _ _ (fun i => β ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull M β (P.le i))
      (fun y => Seesaw.exists_mem P (β y)) fun i => ?_
    refine (hE ⟨_, hk⟩ i).trans (Eq.trans (fn_ext fun z hz => ?_) (hE v i).symm)
    obtain ⟨k', hk'⟩ := exists_chart hM' z
    exact (hC c z i k' hz hk').trans ((congrArg (fun x => _ * gs (𝟙 X') z _ x) (hc k').symm).trans
      (hA z i k' hz hk').symm)

end GlobalTheory.SecBasis
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData

theorem labels_of_tateIsoQ : BrGtSt → BrWpSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F) (N : NumD F) (ν : NumOf D₀ F N) (q : ∀ n : ℕ, D.La → N.QT n), (∀ n a, ν.QPt (I.ev n a) (q n a)) → Labels N D.EF I.ζ q ∧ ∀ k, 0 < k → ∀ (x : 𝓞 E) (a : D.La), ∃ z, ν.eX (q k (x • a)).1.1.toAdd = x • ν.eX (q k a).1.1.toAdd + k • z := by
  intro hG hW E _ _ _ H D R _ _ D₀ _ oa he hB F _ _ _ I N ν q hq
  obtain ⟨h1, -, h2, -, hQ⟩ := hG R D₀ he hB F N ν
  obtain ⟨hadd, htow⟩ := GlobalTheory.NestQVal.qval_add_tower E H D R D₀ oa he hB F I N ν q h1 h2
    (fun k => ⟨(hQ k).1, (hQ k).2.2⟩) hq
  refine ⟨⟨hadd, fun n hn a b => ?_, fun n hn p => ?_, htow, fun n hn a b => ?_⟩, fun n hn x a => ?_⟩
  · rw [← (hQ n).2.2 _ _ _ _ (hq n a) (hq n b)]
    exact I.ker n hn a b
  · obtain ⟨p₀, hp₀⟩ := (hQ n).2.1 p
    obtain ⟨a, ha⟩ := I.onto n hn p₀
    exact ⟨a, ((hQ n).2.2 _ _ _ _ (hq n a) hp₀).1 ha⟩
  · exact Units.ext ((hW R D₀ he hB F N ν n hn _ _ _ _ _ (hq n a) (hq n b)).1 (I.isom n hn a b)).symm
  · obtain ⟨q₀, hy, -, heq⟩ := I.lin n hn x a
    obtain ⟨c, hc, -⟩ := (hQ n).1 q₀
    obtain ⟨z, hz, -⟩ := ((hQ n).2.2 _ _ _ _ hc (hq n (x • a))).1 heq
    exact ⟨ν.eX z, by rw [hz, map_add (f := _), map_nsmul, hc.1, hy, (hq n a).1]⟩

end GlobalTheory.ModelData
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

theorem _root_.GlobalTheory.T.torsionLabelSystem_twist_by_compatible_roots : ∀ (C : Type) [Field C] (N : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (k₀ : ℕ) (β : N.Form k₀) (u : Cˣ) (r : ℕ → Cˣ), Roots u r → Labels N EF ζ lab → ∀ p : ∀ k : ℕ, La → (N.twist β u).QT k, (∀ k, 0 < k → ∀ x, TwRel β u (r k) (lab k x) (p k x)) → Labels (N.twist β u) EF ζ p := by
  first | exact @GlobalTheory.TwistLabels.labels_twist | exact GlobalTheory.TwistLabels.labels_twist | (intros; apply GlobalTheory.TwistLabels.labels_twist <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

theorem _root_.GlobalTheory.T.exists_degenerationValues_of_strict_pullback : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D'), Strict hD.w → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ x, algebraMap (FractionRing R') F (algebraMap R' _ (φ x)) = algebraMap (FractionRing R) F (algebraMap R _ x)) → ∀ (N : NumD F) (ν : NumOf D F N) (th' : H0 D'.P.L 1), (∀ s : H0 D'.P.L 1, ∃ r : R', ∀ j, s.f j = resTop _ (scal D'.P.A.hom r) * th'.f j) → (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → sval ν.th (r ≫ PsiEvenPull.proj hD) z J = (gw hD.w r z (J (r ≫ PsiEvenPull.proj hD)) (J' r)).val * sval th' r z J') → ∃ ν' : NumOf D' F N, (∀ y, hD.xe (ν'.eX y) = ν.eX y) ∧ ∀ x, (ν'.eA x).left ≫ PsiEvenPull.proj hD = (ν.eA x).left := by
  first | exact @GlobalTheory.ValuesStrictPull.exists_numOf_strict_pull | exact GlobalTheory.ValuesStrictPull.exists_numOf_strict_pull | (intros; apply GlobalTheory.ValuesStrictPull.exists_numOf_strict_pull <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section

namespace GlobalTheory.OneBasis

variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F]
  [Algebra (FractionRing R) F]

theorem exists_isTorsFrame_closed [CharZero R] [IsAlgClosed F] (hLaw : Laws) {ρ : LB.Gen (A.L.pull (eSec A.A))}
    (hρ : ρ.IsGen) {n : ℕ} (hn : Odd n) (x : TFK (R := R) F ⟶ A.A) (hx : x ^ n = 1) :
    ∃ e, IsTorsFrame A ρ n x e := by
  let T := TFK (R := R) F
  have : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hu : IsUnit ((n ^ 2 : ℕ) : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2
      (Nat.cast_ne_zero.2 (pow_ne_zero 2 hn.pos.ne'))
  obtain ⟨y, hy⟩ : ∃ y : T ⟶ A.A, y ^ n = x :=
    TorusExt.exists_pow_eq_of_noetherian (S := Sp (FractionRing R)) (k := F) T.hom hLaw.mulN A hn.pos.ne' x
  have hy' : y ^ (n ^ 2) = 1 := by rw [sq, pow_mul, hy, hx]
  obtain ⟨hex, -⟩ := hLaw.symLift _ A (n ^ 2) hn.pow hu T y hy'
  obtain ⟨V, hV, θ₀, hθ₀⟩ := hex p
  obtain ⟨h, hh⟩ := GlobalLift.exists_section (T := T) hV
  obtain ⟨θ, hθ⟩ := GlobalLift.exists_symLift_pull A.isLB h hθ₀
  rw [← Category.assoc, hh, Category.id_comp] at hθ
  exact exists_isTorsFrame_of_symLift hLaw _ A ρ hρ n hn T y x hy' hy θ hθ


omit [IsDomain R] in
theorem exists_valAt (hLaw : Laws) {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A) {e} (he : LB.Gen.IsGen e) :
    ∃ c, ValAt t x e c := by
  obtain ⟨v, hv, -⟩ := hLaw.evVal _ A k x e he t
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 v
  refine ⟨c, fun z J hJ => ?_⟩
  have := FrameMove.sval_valueAt hv (𝟙 _) hJ
  rw [Category.id_comp] at this
  exact this

end GlobalTheory.OneBasis

namespace GlobalTheory

theorem tab_full_uniq : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m n r : ℕ), Odd m → Odd n → ∀ (th : SecA A F 1) (τ : Fin r → SecA A F (m ^ 2)), (∀ t, ∃! a, Cmb τ a t) → (tab ρ m th τ).Full (m ^ 2) n ∧ (tab ρ m th τ).Uniq (m ^ 2) n := by
  intro hLL R _ _ _ A F _ _ _ ρ hρ m n r hm hn th τ hτ
  have H := existsUnique_thetaConst hLL R A F ρ hρ
  refine ⟨⟨fun x hx => ?_, fun j x hx => ?_, fun j x hx => ?_⟩, fun x a ha => ?_, fun j x c hc => ?_⟩
  · obtain ⟨q, hq, -⟩ := H m hm th x hx
    obtain ⟨a, ha, -⟩ := hτ q.1
    exact ⟨a, hx, q.1, q.2, hq, ha⟩
  · obtain ⟨q, hq, -⟩ := H (n ^ j) hn.pow th x hx
    exact ⟨q.2, hx, q.1, hq⟩
  · obtain ⟨e, he⟩ := exists_isTorsFrame_closed A F hLL.1 hρ (hn.pow (n := j)) x hx
    choose l hl using fun i => exists_valAt A F hLL.1 (τ i) x he.2.1
    exact ⟨l, e, he, hl⟩
  · obtain ⟨hx, t, c, ht, ha⟩ := ha
    refine ⟨hx, ?_⟩
    rintro a' ⟨-, t', c', ht', ha'⟩
    have e : t' = t := congrArg Prod.fst ((H m hm th x hx).unique (y₁ := (t', c')) (y₂ := (t, c)) ht' ht)
    subst e
    exact (hτ t').unique ha' ha
  · obtain ⟨hx, t, ht⟩ := hc
    refine ⟨hx, ?_⟩
    rintro c' ⟨-, t', ht'⟩
    exact congrArg Prod.snd ((H (n ^ j) hn.pow th x hx).unique (y₁ := (t', c')) (y₂ := (t, c)) ht' ht)

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.exists_rigidified_polarised_fibre_at_field_point : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (K : Type) [Field K] (x : Sp K ⟶ Z), PolAt t x → ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ t.G.left) (w : LB.Iso A.L (t.PP.L.pull φ)) (ρ : LB.Gen (A.L.pull (eSec A.A))), RigPull A.A t.G x φ w ρ t.PP.rig := by
  first | exact @GlobalTheory.OneBasis.exists_rigPull_of_polAt | exact GlobalTheory.OneBasis.exists_rigPull_of_polAt | (intros; apply GlobalTheory.OneBasis.exists_rigPull_of_polAt <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.rigidified_bundle_two_pullbacks_compare : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (S S' : Scheme.{0}) (x : S ⟶ Z) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → ∀ (φ : G.left ⟶ G₀.left) (φ' : G'.left ⟶ G₀.left) (w : LB.Iso L (L₀.pull φ)) (w' : LB.Iso L' (L₀.pull φ')) ρ ρ', RigPull G G₀ x φ w ρ ρ₀ → RigPull G' G₀ (f ≫ x) φ' w' ρ' ρ₀ → ∃ (ψ : G'.left ⟶ G.left) (ω : LB.Iso L' (L.pull ψ)), RigPull G' G f ψ ω ρ' ρ ∧ ∀ (k : ℕ) (T₀ : Over Z) (T : Over S) (T' : Over S') (p : T.left ⟶ T₀.left) (q : T'.left ⟶ T.left), p ≫ T₀.hom = T.hom ≫ x → q ≫ T.hom = T'.hom ≫ f → ∀ s₀ s s', Thru w k (T' := T) (T := T₀) p s₀ s → Thru w' k (T' := T') (T := T₀) (q ≫ p) s₀ s' → Thru ω k (T' := T') (T := T) q s s' := by
  first | exact @GlobalTheory.OneBasis.Compare.rigPull_compare | exact GlobalTheory.OneBasis.Compare.rigPull_compare | (intros; apply GlobalTheory.OneBasis.Compare.rigPull_compare <;> assumption)
end
