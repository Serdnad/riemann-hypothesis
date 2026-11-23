module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisTermsAtOtherClassMembers
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralPointOfTorusPointValuationZero
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle091
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.abelianSchemeProperClosureData_basic_properties : ∀ C : Core, IsSeparated C.GG.hom ∧ LocallyOfFiniteType C.GG.hom ∧ QuasiCompact C.GG.hom ∧ IsIntegral C.G.toScheme ∧ Flat (C.GG.hom ≫ C.π) ∧ Flat (C.P.hom ≫ C.π) ∧ IsOpenImmersion C.a ∧ IsPullback C.a C.A.hom C.GG.hom C.U.ι ∧ Set.range C.a = C.GG.hom ⁻¹' C.U ∧ IsNoetherian C.Z ∧ IsNoetherian C.P.left ∧ IsDominant C.GG.hom ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.Cl y ∧ CharZero τ.V ∧ IsSemiAbelian τ.H := by
  first | exact @GlobalTheory.ZJ.core_basic | exact GlobalTheory.ZJ.core_basic | (intros; apply GlobalTheory.ZJ.core_basic <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymExtendDvr

theorem isGrpPullback_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] :
    IsGrpPullback A B (𝟙 S) e.hom.left := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let u : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 _) (by simp)
  have e₁ : x₀ = u ≫ x ≫ e.hom := Over.OverMorphism.ext (hx.trans (Category.id_comp _).symm)
  have e₂ : y₀ = u ≫ y ≫ e.hom := Over.OverMorphism.ext (hy.trans (Category.id_comp _).symm)
  rw [e₁, e₂, ← MonObj.comp_mul, ← MonObj.mul_comp]
  exact Category.id_comp _

theorem hypS_of_generic : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → HypS A.A A.L → ∀ gen : (Over.pullback (jK V)).obj G ≅ A.A, IsMonHom gen.hom → ∀ L : RigLB G, LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V))) → HypS G L.L := by
  intro ext V _ _ _ A G _ _ hG H gen hgen L hL
  have := hG.smooth
  have := hG.geomConnected
  have hc : IsCommMonObj ((Over.pullback (jK V)).obj G) := Functor.isCommMonObj_obj
  have hA : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _
  have H' : HypS ((Over.pullback (jK V)).obj G) (A.L.pull gen.hom.left) :=
    GlobalTheory.SymBaseChange.hypS_baseChange _ _ A.A _ (𝟙 _) gen.hom.left A.L _ A.isLB hA (isGrpPullback_of_iso gen)
      ((GlobalTheory.PrimNorm.lbIso_iff A.isLB _ _ _ _).2 rfl) H
  have : IsOpenImmersion (jK V) := GlobalTheory.DvrModel.isOpenImmersion_generic (K := FractionRing V) (f := 𝟙 _)
    (j := jK V) (fK := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩)
  refine GlobalTheory.SymExtend.hypS_extend (GlobalTheory.IsNormalScheme.pred _) (isGrpPullback_pullback G (jK V)) ?_ _ L hA hL.symm H'
  intro α hα
  obtain ⟨F, ⟨hF, eF⟩, u⟩ := ext V (FractionRing V) G G hG hG α hα
  have c : ∀ F : G ⟶ G, ((Over.pullback (jK V)).map F).left ≫ pullback.fst G.hom (jK V) =
      pullback.fst G.hom (jK V) ≫ F.left := fun F => pullback.lift_fst _ _ _
  refine ⟨F, ⟨hF, ?_⟩, fun F' h' => u F' ⟨h'.1, ?_⟩⟩
  · rw [← eF]
    exact (c F).symm
  · refine Over.OverMorphism.ext (pullback.hom_ext ((c F').trans h'.2) ?_)
    exact (Over.w ((Over.pullback (jK V)).map F')).trans (Over.w α).symm

end GlobalTheory.SymExtendDvr
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_frames_on_uniformisedModel_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∀ x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∃ (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, LB.Gen (LB.LinComb u.A.L (Y := (TFK (R := u.V) (PadicAlgCl p)).left) (K := Fin 1) (fun _ => (x a).left) (fun _ => 1))), rig.IsGen ∧ (∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a)) ∧ ∀ (k : ℕ) (σ : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))), ∃ t : SecA u.A (PadicAlgCl p) k, ∀ (a : S.Gam) (c : S.R), IsValueAt ρ.P.A ρ.P.L (k : ℤ) σ (ρ.pt a) (powFrame ρ.P.A ρ.P.L (ρ.pt a) (ρ.fr a) (k : ℤ)) (fn c) → ∀ z J, Good u.A.L z J → sA t (ptSecT u.A.A (x a)).left z J = @id ((TFK (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z) (cst (R := u.V) (PadicAlgCl p) z (y₀ c)) * (val (powFrame u.A.A u.A.L (x a) (e a) (k : ℤ)) (𝟙 _) z J).val := by
  first | exact @GlobalTheory.exists_frames_on_fibre | exact GlobalTheory.exists_frames_on_fibre | (intros; apply GlobalTheory.exists_frames_on_fibre <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.adaptedBasis_terms_at_other_class_members : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → ∀ (i₀ : J) (α : u.D.toPre.X), (∃ m, α = cls i₀ + k • m) → (Short l.q k α → IsBasisB u.D.toPre (fun i : {i // cls i = cls i₀} => f i α)) ∧ (¬ Short l.q k α → ∃ (a : u.V) (β : u.D.toPre.SecB k α), a ∈ IsLocalRing.maximalIdeal u.V ∧ ∀ j, (f i₀ α).f j = constFn u.D.toPre.P.A.hom _ a * β.f j) := by
  first | exact @GlobalTheory.ZH.Shift.main | exact GlobalTheory.ZH.Shift.main | (intros; apply GlobalTheory.ZH.Shift.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.exists_integralPoint_of_torusPoint_valuationZero : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (g : GtPtF u.D.toPre (PadicAlgCl p)), u.GtN g 0 → ∃ c : Sp (OO p) ⟶ u.G.left, c ≫ u.G.hom = spMap u.j ∧ u.Lev c g := by
  first | exact @GlobalTheory.GtDescent.exists_integral_point | exact GlobalTheory.GtDescent.exists_integral_point | (intros; apply GlobalTheory.GtDescent.exists_integral_point <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.OpenPart

theorem le_nonzeroLocus_iff {k K : Type} [CommRing k] [Field K] {X : Scheme.{0}} {p : X ⟶ Sp k} {H : LB X}
    {J : Type} [Fintype J] {s : J → H.Sec} {a : J → k} {φ : H.Sec} (hφ : IsLin p s a φ)
    {x : Sp K ⟶ X} {ψ : k →+* K} (hx : x ≫ p = spMap ψ) {v : J → K} (hv : Crd H s x v) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus φ ↔ ∑ j, ψ (a j) * v j ≠ 0 := by
  have h : Crd H (fun _ : Unit => φ) x (fun _ => ∑ j, ψ (a j) * v j) := by
    obtain ⟨l, c, hl, hv⟩ := hv
    refine ⟨l, c, hl, fun _ => ?_⟩
    beta_reduce

    rw [hφ l, CrdCalc.valR_eq x _ hl, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq,
      GlobalTheory.Points.valR_constFn_of_over p ψ x hx _ hl, hv, mul_left_comm]
  exact (CrdCalc.crd_isUnit_iff () h).symm.trans isUnit_iff_ne_zero

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω}

theorem TT_le_TT {z z' : M.Z} (h : S.supI M z' ⊆ S.supI M z) : S.TT M z ≤ S.TT M z' :=
  fun _ ha b hb => ha b (AddSubgroup.closure_mono h hb)

theorem isOpen_supI_subset (z : M.Z) : IsOpen {z' | S.supI M z ⊆ S.supI M z'} := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : {z' | S.supI M z ⊆ S.supI M z'} = ⋂ a ∈ S.supI M z, {z' | M.Div S.th a z'} := by
    ext z'
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [this]
  exact (Set.toFinite _).isOpen_biInter fun a _ => M.isOpen_setOf_div _ _

theorem supI_subset {U₀ : M.Z.Opens} (h : S.Over₀ M U₀) (z : M.Z) {z' : M.Z} (hz' : z' ∈ U₀) :
    S.supI M z ⊆ S.supI M z' := fun a ha => ⟨ha.1, fun j => by
  rw [div_eq_mul_inv]
  exact RatModel.ringOn_le_O hz' (mul_mem (h.le (S.th_mem j)) (h.th_unit a ha.1))⟩

theorem exists_ne_zero_of_le {T T' : AddSubgroup S.Gam} (h : T' ≤ T) (hT : S.IsoFree T) (hT' : S.IsoFree T')
    {K : Type} [Field K] (ψ : o →+* K) (v : S.J → K) {i : S.J} (hi : ∑ j, ψ (S.proj T 0 j i) * v j ≠ 0) :
    ∃ i, ∑ j, ψ (S.proj T' 0 j i) * v j ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply hi
  rw [← GlobalTheory.ThetaBound.proj_mul_proj S T T' h hT.1 hT' 0 0 fun _ => rfl]

  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := congrArg (ψ (S.proj T 0 k i) * ·) (hn k)
  simp only [Finset.mul_sum, mul_zero] at this
  rw [← this]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem le_preimage_G_iff : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (K : Type) [Field K] (x : Sp K ⟶ Q.P.left) (z : M.Z) (ψ : o →+* K) (v : S.J → K), Set.range (x ≫ Q.P.hom) = {z} → (IsClosed ({z} : Set M.Z) ∨ z ∈ U₀) → x ≫ Q.P.hom ≫ M.s = spMap ψ → Crd Q.O1 Q.st x v → (⊤ ≤ x ⁻¹ᵁ Q.G ↔ ∃ i, ∑ j, ψ (S.proj (S.TT M z) 0 j i) * v j ≠ 0) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE hB Q K _ x z ψ v hz hc hψ hv
  have hψ' : x ≫ (Q.P.hom ≫ M.s) = spMap ψ := hψ
  have hxz : Q.P.hom (x (IsLocalRing.closedPoint K)) = z := by
    have : (x ≫ Q.P.hom) (IsLocalRing.closedPoint K) ∈ Set.range (x ≫ Q.P.hom) := ⟨_, rfl⟩
    rw [hz] at this
    exact this
  rw [CrdCalc.top_le_iff]
  simp only [Clos.G, TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨z', -, W, hW, i, φ, hφ, h1, h2⟩
    have h1' : z ∈ W := hxz ▸ h1
    exact exists_ne_zero_of_le (TT_le_TT (hW z h1')) (hB.free _).1 (hB.free _).1 ψ v
      ((le_nonzeroLocus_iff hφ hψ' hv).1 ((CrdCalc.top_le_iff x _).2 h2))
  · intro hi
    obtain ⟨z', hz', hs, hs'⟩ : ∃ z' : M.Z, IsClosed ({z'} : Set M.Z) ∧ S.supI M z' ⊆ S.supI M z ∧
        S.supI M z ⊆ S.supI M z' := by
      rcases hc with hc | hc
      · exact ⟨z, hc, le_rfl, le_rfl⟩
      · have := hB.jac
        obtain ⟨z', h1, h2⟩ := nonempty_inter_closedPoints (Z := (U₀ : Set M.Z)) ⟨z, hc⟩
          U₀.isOpen.isLocallyClosed
        exact ⟨z', h2, supI_subset hB.ov _ hc, supI_subset hB.ov _ h1⟩
    obtain ⟨i, hi⟩ := hi
    obtain ⟨i, hi⟩ := exists_ne_zero_of_le (TT_le_TT hs') (hB.free _).1 (hB.free _).1 ψ v hi
    obtain ⟨φ, hφ, -⟩ := GlobalTheory.SecRatio.existsUnique_isLin (Q.P.hom ≫ M.s) Q.st
      (fun j => S.proj (S.TT M z') 0 j i)
    refine ⟨z', hz', ⟨_, isOpen_supI_subset z'⟩, fun _ h => h, i, φ, hφ, ?_,
      (CrdCalc.top_le_iff x _).1 ((le_nonzeroLocus_iff hφ hψ' hv).2 hi)⟩
    change S.supI M z' ⊆ S.supI M (Q.P.hom (x (IsLocalRing.closedPoint K)))
    rw [hxz]
    exact hs

end GlobalTheory.ZH.OpenPart
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH.DivCrd

open GlobalTheory.Points CrdCalc

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {N : RatModel o Ω} {X : Scheme.{0}} {a : N.Z ⟶ X}
  {H : LB X} {J : Type} {s : J → H.Sec} {t : J → Ω}

theorem ratio_eq (ht : Crd H s (N.pt ≫ a) t) {k : J} {z : N.Z} (hz : a z ∈ nonzeroLocus (s k)) :
    t k ≠ 0 ∧ ∀ (j : J) (r : Γ(X, nonzeroLocus (s k))), IsRatio (s j) (s k) _ r →
      valF N.pt (a ⁻¹ᵁ nonzeroLocus (s k)) (a.app _ r) = t j / t k := by
  have h : ⊤ ≤ (N.pt ≫ a) ⁻¹ᵁ nonzeroLocus (s k) :=
    N.top_le_preimage_pt (U := a ⁻¹ᵁ nonzeroLocus (s k)) ⟨z, hz⟩
  have hk : t k ≠ 0 := ((crd_isUnit_iff k ht).2 h).ne_zero
  refine ⟨hk, fun j r hr => ?_⟩
  rw [eq_div_iff hk, crd_ratio ht hr h, valR_comp]
  rfl

theorem div_of_mem (hH : H.IsLB) (ht : Crd H s (N.pt ≫ a) t) {k : J} {z : N.Z}
    (hz : a z ∈ nonzeroLocus (s k)) : N.Div t k z := by
  obtain ⟨hk, h⟩ := ratio_eq ht hz
  refine ⟨hk, fun j => ?_⟩
  obtain ⟨r, hr, -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio hH (s j) (s k) _ le_rfl
  exact ⟨a ⁻¹ᵁ nonzeroLocus (s k), a.app _ r, hz, h j r hr⟩

theorem crd_eq_val_mul (hH : H.IsLB) (ht : Crd H s (N.pt ≫ a) t) {K : Type} [Field K] {x : Sp K ⟶ N.Z}
    {v : J → K} {k : J} (hv : Crd H s (x ≫ a) v)
    (hz : a (x (IsLocalRing.closedPoint K)) ∈ nonzeroLocus (s k)) :
    v k ≠ 0 ∧ ∀ j, v j = N.val x (t j / t k) * v k := by
  have hx : ⊤ ≤ x ⁻¹ᵁ (a ⁻¹ᵁ nonzeroLocus (s k)) := (le_preimage_iff x _).2 hz
  have h : ⊤ ≤ (x ≫ a) ⁻¹ᵁ nonzeroLocus (s k) := hx
  refine ⟨((crd_isUnit_iff k hv).2 h).ne_zero, fun j => ?_⟩
  obtain ⟨r, hr, -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio hH (s j) (s k) _ le_rfl
  rw [RatModel.val_eq ((top_le_preimage_iff _ _).1 hx) ((ratio_eq ht hz).2 j r hr), crd_ratio hv hr h,
    valR_comp]
  rfl

theorem mem_of_div_pt (hH : H.IsLB) (hs : ⨆ j, nonzeroLocus (s j) = ⊤) (ht : Crd H s (N.pt ≫ a) t)
    {K : Type} [Field K] (x : Sp K ⟶ N.Z) {i : J} (hi : N.Div t i (x (IsLocalRing.closedPoint K))) :
    a (x (IsLocalRing.closedPoint K)) ∈ nonzeroLocus (s i) := by
  have hm : a (x (IsLocalRing.closedPoint K)) ∈ ⨆ j, nonzeroLocus (s j) := by rw [hs]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  obtain ⟨v, hv⟩ := crd_exists hH s (x ≫ a)
  obtain ⟨h0, h1⟩ := crd_eq_val_mul hH ht hv hk
  have hd := div_of_mem hH ht hk
  have hu := (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton x _) _).2 ((hd.div_iff_isUnit i).1 hi)
  have hvi : IsUnit (v i) := isUnit_iff_ne_zero.2 (by rw [h1 i]; exact mul_ne_zero hu h0)
  exact (le_preimage_iff (x ≫ a) _).1 ((crd_isUnit_iff i hv).1 hvi)

theorem mem_of_div (hH : H.IsLB) (hs : ⨆ j, nonzeroLocus (s j) = ⊤) (ht : Crd H s (N.pt ≫ a) t)
    {i : J} {z : N.Z} (hi : N.Div t i z) : a z ∈ nonzeroLocus (s i) := by
  let x : Sp (N.Z.residueField z) ⟶ N.Z := N.Z.fromSpecResidueField z
  have e : x (IsLocalRing.closedPoint (N.Z.residueField z)) = z := Scheme.fromSpecResidueField_apply _ _
  have h := mem_of_div_pt hH hs ht x (i := i) (by rw [e]; exact hi)
  rwa [e] at h

theorem div_iff_mem_nonzeroLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (N : RatModel o Ω) (X : Scheme.{0}) (a : N.Z ⟶ X) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω), H.IsLB → ⨆ j, nonzeroLocus (s j) = ⊤ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ N.Z) (v : J → K) (k : J), Crd H s (x ≫ a) v → N.Div t k (x (IsLocalRing.closedPoint K)) → v k ≠ 0 ∧ ∀ j, v j = N.val x (t j / t k) * v k :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hH hs ht =>
    ⟨fun _ _ => ⟨mem_of_div hH hs ht, div_of_mem hH ht⟩,
      fun _ _ x _ _ hv hk => crd_eq_val_mul hH ht hv (mem_of_div_pt hH hs ht x hk)⟩

end GlobalTheory.ZH.DivCrd
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

noncomputable section
namespace GlobalTheory.ZH.IntegralSum
open GlobalTheory.FormalValue Filter Topology

theorem exists_lift_valR {O T : Type} [CommRing O] [IsLocalRing O] [CommRing T] [IsLocalRing T] (π : O →+* T)
    [IsLocalHom π] {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i] (c : Sp O ⟶ X) (ce : Sp T ⟶ Y)
    (h : ce ≫ i = spMap π ≫ c) (U : Y.Opens) (hU : ⊤ ≤ ce ⁻¹ᵁ U) (f : Γ(Y, U)) :
    ∃ (U' : X.Opens) (f' : Γ(X, U')), ⊤ ≤ c ⁻¹ᵁ U' ∧ π (valR c U' f') = valR ce U f := by
  have hy : ce (cpt T) ∈ U := hU trivial
  obtain ⟨a, ha⟩ := i.stalkMap_surjective (ce (cpt T)) ((Y.presheaf.germ U _ hy).hom f)
  obtain ⟨U', hU', f', rfl⟩ := X.presheaf.germ_exist a
  have hcl : spMap π (cpt T) = cpt O := IsLocalRing.comap_closedPoint π
  have h1 : (spMap π ≫ c) (cpt T) ∈ U' := by rw [← h]; exact hU'
  have h2 : ⊤ ≤ c ⁻¹ᵁ U' := (top_le_iff_cpt c U').2 (by rw [← hcl]; exact h1)
  refine ⟨U', f', h2, toStkA_injective ?_⟩
  rw [toStkA_map_valR π c U' _ h2, toStkA_valR_eq_gs ce U _ hU, ← h, ← gs_pull ce i _ U' hU',
    gs_eq ce _ U hy, gs_eq ce _ (i ⁻¹ᵁ U') hU', ← Scheme.Hom.germ_stalkMap_apply ce U _ hy,
    ← Scheme.Hom.germ_stalkMap_apply ce (i ⁻¹ᵁ U') _ hU', ← ha]
  exact congrArg _ (Scheme.Hom.germ_stalkMap_apply i U' _ hU' f').symm

variable {p : ℕ} [Fact p.Prime]

theorem exists_finite_values {V : Type} [CommRing V] (j : V →+* OO p) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K₀] (hj : ∀ x, (j x : PadicAlgCl p) ∈ K₀) {X : Scheme.{0}} (s : X ⟶ Sp V)
    [LocallyOfFiniteType s] (c : Sp (OO p) ⟶ X) (hc : c ≫ s = spMap j) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
      ∀ (U : X.Opens), ⊤ ≤ c ⁻¹ᵁ U → ∀ f, ((valR c U f : OO p) : PadicAlgCl p) ∈ K := by
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (x := c (cpt _)) (U := ⊤) trivial
  have hWt : ⊤ ≤ c ⁻¹ᵁ W := (top_le_iff_cpt c W).2 hyW
  have hft : (s.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  letI := (s.appLE ⊤ W le_top).hom.toAlgebra
  obtain ⟨t, ht⟩ := hft.1
  let φ : Γ(X, W) →+* PadicAlgCl p := (OO p).subtype.comp (CrdCalc.valHom c W hWt)
  have hφ : ∀ f, φ f = ((valR c W f : OO p) : PadicAlgCl p) := fun f => by
    rw [CrdCalc.valR_eq c W hWt]; rfl
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (φ '' (t : Set Γ(X, W)))) :=
    haveI : Finite (φ '' (t : Set Γ(X, W))) := ((t.finite_toSet).image φ).to_subtype
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨K₀ ⊔ IntermediateField.adjoin ℚ_[p] (φ '' (t : Set Γ(X, W))), inferInstance, ?_⟩
  set K := K₀ ⊔ IntermediateField.adjoin ℚ_[p] (φ '' (t : Set Γ(X, W)))
  have hall : ∀ f, φ f ∈ K := fun f => by
    have hf : f ∈ Algebra.adjoin Γ(Sp V, ⊤) (t : Set Γ(X, W)) := ht ▸ trivial
    induction hf using Algebra.adjoin_induction with
    | mem x hx => exact (le_sup_right : _ ≤ K) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
    | algebraMap r =>
      refine (le_sup_left : _ ≤ K) ?_
      have e : (s.appLE ⊤ W le_top ≫ c.appLE W ⊤ hWt ≫ (Scheme.ΓSpecIso (CommRingCat.of (OO p))).hom) =
          (Scheme.ΓSpecIso (CommRingCat.of V)).hom ≫ CommRingCat.ofHom j := by
        rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality]
        refine congrArg (· ≫ _) ((Scheme.Hom.appLE_comp_appLE c s ⊤ W ⊤ le_top hWt).trans ?_)
        simp only [hc]
        rfl
      have e' : CrdCalc.valHom c W hWt (algebraMap Γ(Sp V, ⊤) Γ(X, W) r) =
        j ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom r) := congrArg (fun q => q.hom r) e
      have := hj ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom r)
      rw [← e'] at this
      exact this
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  intro U hU f
  obtain ⟨g, hgU, hyg⟩ := hW.exists_basicOpen_le ⟨c (cpt _), hU trivial⟩ hyW
  have hgt : ⊤ ≤ c ⁻¹ᵁ X.basicOpen g := (top_le_iff_cpt c _).2 hyg
  have := hW.isLocalization_basicOpen g
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) (resG X hgU f)
  have e2 := congrArg (valR c (X.basicOpen g)) e
  rw [CrdCalc.valR_mul c _ hgt, CrdCalc.valR_res c hgU hgt] at e2
  have r1 : ∀ b : Γ(X, W), valR c (X.basicOpen g) (algebraMap Γ(X, W) Γ(X, X.basicOpen g) b) = valR c W b :=
    fun b => CrdCalc.valR_res c (X.basicOpen_le g) hgt b
  rw [r1, r1] at e2
  have hu : IsUnit (valR c W g) := (CrdCalc.isUnit_valR_iff c W hWt g).2 hgt
  have hg0 : φ (g ^ n) ≠ 0 := by
    rw [map_pow, hφ]
    exact pow_ne_zero _ (hu.map (OO p).subtype).ne_zero
  have e3 : ((valR c U f : OO p) : PadicAlgCl p) = φ a / φ (g ^ n) := by
    rw [eq_div_iff hg0, hφ, hφ]
    exact congrArg Subtype.val e2
  rw [e3]
  exact div_mem (hall _) (hall _)

theorem exists_tendsto (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] {r : ℝ}
    (hr : r < 1) (ω : ℕ → PadicAlgCl p) (hK : ∀ e, ω e ∈ K) (h : ∀ e, ‖ω (e + 1) - ω e‖ ≤ r ^ (e + 1)) :
    ∃ a, Tendsto ω atTop (𝓝 a) := by
  have hc : CauchySeq ω := cauchySeq_of_le_geometric r r hr fun e => by
    rw [dist_comm, dist_eq_norm, ← pow_succ']; exact h e
  haveI : FiniteDimensional ℚ_[p] K.toSubmodule := inferInstanceAs (FiniteDimensional ℚ_[p] K)
  obtain ⟨a, -, ha⟩ := cauchySeq_tendsto_of_isComplete K.toSubmodule.complete_of_finiteDimensional hK hc
  exact ⟨a, ha⟩

theorem hasSum_of_levels {Ix : Type} {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1) (x : Ix → PadicAlgCl p)
    (s : ℕ → PadicAlgCl p) (a : PadicAlgCl p) (hs : Tendsto s atTop (𝓝 a))
    (h : ∀ e, ∃ S : Finset Ix, ∀ T, S ⊆ T → ‖s e - ∑ i ∈ T, x i‖ ≤ r ^ (e + 1)) : HasSum x a := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have h1 := (Metric.tendsto_nhds.1 hs) (ε / 2) (half_pos hε)
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr).comp (tendsto_add_atTop_nat 1)
  have h3 := h2.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨e, he1, he2⟩ := (h1.and h3).exists
  obtain ⟨S, hS⟩ := h e
  refine ⟨S, fun T hT => ?_⟩
  have := hS T hT
  rw [← dist_eq_norm, dist_comm] at this
  have h4 := dist_triangle (∑ i ∈ T, x i) (s e) a
  simp only [Function.comp] at he2
  linarith

end GlobalTheory.ZH.IntegralSum
end
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaRecognition_lattice_iso_and_terms_agree : AllMatch fun μ _ _ => μ.A → ∃ e, μ.B e ∧ μ.Term e := by
  first | exact @GlobalTheory.MatchTerm.main | exact GlobalTheory.MatchTerm.main | (intros; apply GlobalTheory.MatchTerm.main <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

theorem _root_.GlobalTheory.T.exists_closedImmersion_projSpace_of_sections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) (s : J → H.Sec) (m : ℕ) (e : Fin (m + 1) ≃ J), ImmBy p H s Set.univ → ∃ φ : X ⟶ PSpace k m, IsClosedImmersion φ ∧ φ ≫ PSpace.str k m = p ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd (ProjSpace.O1 k m) (ProjSpace.coord k m) (x ≫ φ) (fun i => v (e i)) := by
  first | exact @GlobalTheory.ZH.ImmProj.exists_closedImmersion_of_immBy | exact GlobalTheory.ZH.ImmProj.exists_closedImmersion_of_immBy | (intros; apply GlobalTheory.ZH.ImmProj.exists_closedImmersion_of_immBy <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

theorem _root_.GlobalTheory.T.isImmersion_projSpace_of_local_linearChange : ∀ (o : Type) [CommRing o] (Y Z : Scheme.{0}) [IsReduced Y] (s : Z ⟶ Sp o) (f : Y ⟶ Z) (m : ℕ) (π : Y ⟶ PSpace o m) (h : π ≫ PSpace.str o m = f ≫ s), (∀ y : Y, ∃ (W : Z.Opens) (A : Type) (_ : CommRing A) (c : W.toScheme ⟶ Sp A) (ψ : (f ⁻¹ᵁ W).toScheme ⟶ PSpace A m) (a : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(Z, W)) (K : Type) (_ : Field K) (η : Sp K ⟶ (f ⁻¹ᵁ W).toScheme) (v : Fin (m + 1) → K), f y ∈ W ∧ IsImmersion ψ ∧ ψ ≫ PSpace.str A m = (f ∣_ W) ≫ c ∧ IsUnit a.det ∧ IsDominant η ∧ Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (η ≫ (f ⁻¹ᵁ W).ι ≫ π) v ∧ Crd (ProjSpace.O1 A m) (ProjSpace.coord A m) (η ≫ ψ) ((a.map (valF (η ≫ (f ⁻¹ᵁ W).ι ≫ f) W)).mulVec v)) → IsImmersion (pullback.lift π f h) := by
  first | exact @GlobalTheory.ZH.LinFrame.isImmersion_lift_of_linear_change | exact GlobalTheory.ZH.LinFrame.isImmersion_lift_of_linear_change | (intros; apply GlobalTheory.ZH.LinFrame.isImmersion_lift_of_linear_change <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

theorem _root_.GlobalTheory.T.exists_projSpace_map_of_local_sections_no_common_zero : ∀ (o : Type) [CommRing o] (X Z : Scheme.{0}) (f : X ⟶ Z) (s : Z ⟶ Sp o) (B : LB X) (V : X.Opens) (J : Type) (σ : J → ∀ j, Γ(X, V ⊓ B.U j)) (m : ℕ) (e : Fin (m + 1) ≃ J), (∀ i, σ i ∈ secOn B V) → (∀ x ∈ V, ∃ i j, x ∈ X.basicOpen (σ i j)) → ∃ π : V.toScheme ⟶ PSpace o m, π ≫ PSpace.str o m = (V.ι ≫ f) ≫ s ∧ (∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens) (hi : T ≤ π ⁻¹ᵁ ProjSpace.chart o m i) (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) = ProjSpace.pullRatio π T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ V.toScheme) (j : B.ι), ⊤ ≤ (x ≫ V.ι) ⁻¹ᵁ B.U j → Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (x ≫ π) (fun k => valF (x ≫ V.ι) (V ⊓ B.U j) (σ (e k) j)) := by
  first | exact @GlobalTheory.ZH.CoordMap.exists_coordMap | exact GlobalTheory.ZH.CoordMap.exists_coordMap | (intros; apply GlobalTheory.ZH.CoordMap.exists_coordMap <;> assumption)
end
