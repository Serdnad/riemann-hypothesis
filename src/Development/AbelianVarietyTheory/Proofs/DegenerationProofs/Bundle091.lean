module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle082
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.AmpSub

def chartPullPw {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (t : ℤ) :
    ChartPull (AbLaw.pw (L.pull f) t) (AbLaw.pw L t) f where
  idx J := J PUnit.unit
  le _ _ hy := mem_pull.1 hy
  g y J J' hJ hJ' := (map_zpow _ _ _).trans
    ((congrArg (· ^ t) ((Geo.Tor.chartPullPull L f f rfl).g y J J' hJ hJ')).trans (map_zpow _ _ _).symm)

theorem hasGen_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i : L.ι)
    (h : ∀ y, f y ∈ L.U i) : MulPull.HasGen L (K := PUnit) (fun _ => f) (fun _ => 1) := by
  have le : ∀ J : PUnit → L.ι, (L.pull f).U J ≤ f ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U i) :=
    fun J y hy => ⟨mem_pull.1 hy, h y⟩
  refine ⟨⟨fun J => res (le J) (pullU f _ (L.g (J PUnit.unit) i))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans (gm_rp₁ f y _ _ (le J) hy.1 _)).trans (Eq.symm ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) (gm_pull_g L f (𝟙 Y) y J J' hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (gm_rp₁ f y _ _ (le J') hy.2 _))).trans ?_)))
  rw [Category.id_comp]
  exact gm_cocycle hL f y (mem_pull.1 hy.1) (mem_pull.1 hy.2) (h y)

theorem exists_chart_local {X S : Scheme.{0}} {L : LB X} (hL : L.IsLB) [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    (f : S ⟶ X) : ∃ i, ∀ y, f y ∈ L.U i := by
  obtain ⟨i, hi⟩ := exists_chart hL ((S.isoSpec.inv ≫ f) (IsLocalRing.closedPoint Γ(S, ⊤)))
  have e : (S.isoSpec.inv ≫ f) ⁻¹ᵁ L.U i = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 hi
  refine ⟨i, fun y => ?_⟩
  have : S.isoSpec.hom y ∈ (S.isoSpec.inv ≫ f) ⁻¹ᵁ L.U i := by rw [e]; trivial
  have h2 : (S.isoSpec.hom ≫ S.isoSpec.inv ≫ f) y ∈ L.U i := this
  rwa [Iso.hom_inv_id_assoc] at h2

theorem psum_comp {S : Scheme.{0}} {N G : Over S} [GrpObj N] [GrpObj G] (ν : N ⟶ G) [IsMonHom ν]
    {T' T : Over S} {n : ℕ} (x : Fin n → (T' ⟶ N)) (y : Fin n → (T ⟶ G)) (h : T' ⟶ T)
    (e : ∀ k, x k ≫ ν = h ≫ y k) (I : Finset (Fin n)) : psum N x I ≫ ν = h ≫ psum G y I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact (MonObj.one_comp ν).trans (MonObj.comp_one h).symm
  | cons k l ih =>
    exact (MonObj.mul_comp _ _ ν).trans ((congrArg₂ (· * ·) (e k) ih).trans (MonObj.comp_mul h _ _).symm)

theorem ampleCub_pull_and_pullPow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), AmpleCub G L → (∀ (N : Over S) [GrpObj N] (ν : N ⟶ G), IsMonHom ν → IsClosedImmersion ν.left → AmpleCub N (L.pull ν.left)) ∧ (IsLocalRing Γ(S, ⊤) → IsAffine S → ∀ n : ℕ, PullPow ((𝟙 G) ^ n).left L ((n : ℤ) ^ 2)) := by
  intro S G _ _ L ⟨hL, ⟨c, hc⟩, ⟨s, hs⟩, n, hn, ha⟩
  refine ⟨fun N _ ν hν hcl => ⟨pull_isLB hL _, ?_, ?_, n, hn, fun x => ?_⟩, fun _ _ m => ?_⟩
  · refine gen_chartPull (chartPullLinComb L ν.left _ _ _ (ν ⊗ₘ ν ⊗ₘ ν).left fun I => ?_) c hc
    refine congrArg (fun z => z.left) (psum_comp ν (x3 N) (x3 G) (ν ⊗ₘ ν ⊗ₘ ν) (fun k => ?_) I.down)
    fin_cases k <;> simp [x3]
  · refine gen_chartPull (chartPullLinComb L ν.left _ _ _ ν.left fun k => ?_) s hs
    fin_cases k
    · exact congrArg (fun z => z.left) (GrpObj.inv_hom ν)
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · obtain ⟨σ, hx, hσ⟩ := ha (ν.left x)
    have e : Out.nonzeroLocus (chartSec (chartPullPw L ν.left n) σ) = ν.left ⁻¹ᵁ Out.nonzeroLocus σ :=
      nonzeroLocus_chartSec _ σ fun y j hj => ⟨fun _ => j, mem_pull.2 hj⟩
    refine ⟨chartSec (chartPullPw L ν.left n) σ, ?_, ?_⟩ <;> rw [e]
    · exact hx
    · exact hσ.preimage _
  · have hcube : MulPull.HasGen L (thφ G (x3 G)) thε := ⟨c, hc⟩
    have hsym : MulPull.HasGen L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] := ⟨s, hs⟩
    obtain ⟨i, hi⟩ := exists_chart_local (S := S) hL (eSec G)
    have hrig := hasGen_of_chart hL (eSec G) i hi
    have h := MulPull.hasGen_pow hL hcube (𝟙 G) ((hrig.pull (toUnit G).left).of_formEq hL (fun U _ h => by
        simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
          Matrix.cons_val_zero, _root_.mul_one]
        rfl))
      (hsym.inv.of_formEq hL (fun U _ h => by
        rw [Fin.prod_univ_two, Fin.prod_univ_two, Hom.inv_def, Category.id_comp, mul_comm]
        rfl)) m
    refine h.inv.of_formEq hL fun U _ h => ?_
    rw [Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]
    rfl

end GlobalTheory.SS.AmpSub
end
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

namespace GlobalTheory.ZH.ImmProj

theorem exists_closedImmersion_of_immBy : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) (s : J → H.Sec) (m : ℕ) (e : Fin (m + 1) ≃ J), ImmBy p H s Set.univ → ∃ φ : X ⟶ PSpace k m, IsClosedImmersion φ ∧ φ ≫ PSpace.str k m = p ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd (ProjSpace.O1 k m) (ProjSpace.coord k m) (x ≫ φ) (fun i => v (e i)) := by
  intro k _ X p H J s m e ⟨hc, hi⟩
  have hs : ⨆ i, nonzeroLocus (s (e i)) = ⊤ := by
    rw [e.iSup_comp (g := fun j => nonzeroLocus (s j))]
    simpa only [Set.mem_univ, iSup_pos] using hc
  refine ⟨ProjSpace.toProj p (fun i => s (e i)) hs, ?_, ProjSpace.toProj_str _ _ _, ?_⟩
  · refine (ProjSpace.isClosedImmersion_toProj_iff p _ hs).2 fun i => ⟨(hi (e i) trivial).1, ?_⟩
    obtain ⟨r, hr, hcl⟩ := (hi (e i) trivial).2
    obtain rfl : r = fun j => ProjSpace.secRatio (s (e i)) (s j) :=
      funext fun j => ProjSpace.eq_secRatio _ _ (hr j)
    rw [← SpanImm.closure_eq_top_iff, ← hcl]
    congr 2
    exact e.surjective.range_comp (fun j => ProjSpace.secRatio (s (e i)) (s j))
  · intro K _ x v hv
    obtain ⟨i, hx⟩ := Points.exists_le_preimage_of_iSup_eq_top x hs
    have hu := (CrdCalc.crd_isUnit_iff (e i) hv).2 hx
    have hle := (ProjSpace.toProj_preimage_chart p (fun i => s (e i)) hs i).ge
    refine ⟨i, hu.unit, hx.trans (x.preimage_mono hle), fun j => ?_⟩
    have h1 := CrdCalc.crd_ratio (i := e i) (j := e j) hv (ProjSpace.secRatio_spec (s (e i)) (s (e j))) hx
    beta_reduce
    rw [h1, IsUnit.unit_spec, mul_comm, ← ProjSpace.pullRatio_toProj p (fun i => s (e i)) hs i j]
    exact congrArg _ (Points.valR_appLE x _ hle hx _)

end GlobalTheory.ZH.ImmProj
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

noncomputable section

namespace GlobalTheory.ZH.CoordMap

variable {X Y : Scheme.{0}}

def pullOn (B : LB X) (V : X.Opens) (g : Y ⟶ X) : LB Y where
  ι := B.ι
  U j := g ⁻¹ᵁ (V ⊓ B.U j)
  g j j' := Units.map (g.appLE (B.U j ⊓ B.U j') (g ⁻¹ᵁ (V ⊓ B.U j) ⊓ g ⁻¹ᵁ (V ⊓ B.U j'))
    (inf_le_inf (g.preimage_mono inf_le_right) (g.preimage_mono inf_le_right))).hom.toMonoidHom (B.g j j')

def pullSecOn {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j)) (h : σ ∈ secOn B V) :
    (pullOn B V g).Sec where
  f j := (g.appLE (V ⊓ B.U j) (g ⁻¹ᵁ (V ⊓ B.U j)) le_rfl).hom (σ j)
  compat j j' := by
    have hW : g ⁻¹ᵁ (V ⊓ B.U j) ⊓ g ⁻¹ᵁ (V ⊓ B.U j') ≤ g ⁻¹ᵁ (V ⊓ B.U j ⊓ B.U j') :=
      le_inf inf_le_left (inf_le_right.trans (g.preimage_mono inf_le_right))
    have e := congrArg (g.appLE _ _ hW).hom (h j j')
    rw [map_mul, ProjSpace.appLE_resG, ProjSpace.appLE_resG, ProjSpace.appLE_resG] at e
    exact (ProjSpace.resG_appLE g le_rfl inf_le_left _).trans (e.trans
      (congrArg (_ * ·) (ProjSpace.resG_appLE g le_rfl inf_le_right _).symm))

theorem resG_pullSecOn {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j)) (h : σ ∈ secOn B V)
    (j : B.ι) {T : Y.Opens} (hj : T ≤ g ⁻¹ᵁ (V ⊓ B.U j)) :
    resG Y (U := (pullOn B V g).U j) hj ((pullSecOn g σ h).f j) = (g.appLE _ T hj).hom (σ j) :=
  ProjSpace.resG_appLE g le_rfl hj _

theorem preimage_basicOpen_le {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j))
    (h : σ ∈ secOn B V) (j : B.ι) : g ⁻¹ᵁ X.basicOpen (σ j) ≤ nonzeroLocus (pullSecOn g σ h) := by
  refine le_trans ?_ (le_iSup (fun k => Y.basicOpen ((pullSecOn g σ h).f k)) j)
  refine le_trans ?_ (Scheme.basicOpen_appLE g (g ⁻¹ᵁ (V ⊓ B.U j)) _ le_rfl (σ j)).ge
  exact le_inf (g.preimage_mono (X.basicOpen_le _)) le_rfl

theorem exists_coordMap : ∀ (o : Type) [CommRing o] (X Z : Scheme.{0}) (f : X ⟶ Z) (s : Z ⟶ Sp o) (B : LB X) (V : X.Opens) (J : Type) (σ : J → ∀ j, Γ(X, V ⊓ B.U j)) (m : ℕ) (e : Fin (m + 1) ≃ J), (∀ i, σ i ∈ secOn B V) → (∀ x ∈ V, ∃ i j, x ∈ X.basicOpen (σ i j)) → ∃ π : V.toScheme ⟶ PSpace o m, π ≫ PSpace.str o m = (V.ι ≫ f) ≫ s ∧ (∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens) (hi : T ≤ π ⁻¹ᵁ ProjSpace.chart o m i) (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) = ProjSpace.pullRatio π T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ V.toScheme) (j : B.ι), ⊤ ≤ (x ≫ V.ι) ⁻¹ᵁ B.U j → Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (x ≫ π) (fun k => valF (x ≫ V.ι) (V ⊓ B.U j) (σ (e k) j)) := by
  intro o _ X Z f s B V J σ m e hσ hne
  let t : Fin (m + 1) → (pullOn B V V.ι).Sec := fun k => pullSecOn V.ι (σ (e k)) (hσ _)
  have ht : ⨆ i, nonzeroLocus (t i) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, j, hij⟩ := hne (V.ι y) y.2
    obtain ⟨k, rfl⟩ := e.surjective i
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, preimage_basicOpen_le V.ι _ (hσ _) j hij⟩
  have key : ∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens)
      (hi : T ≤ ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht ⁻¹ᵁ ProjSpace.chart o m i)
      (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧
        ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) =
          ProjSpace.pullRatio _ T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j) := by
    intro i j T hi hj
    refine ⟨?_, fun k => ?_⟩
    · rw [← resG_pullSecOn V.ι _ (hσ _) j hj]
      exact ProjSpace.isUnit_resG_sec (t i) j (hi.trans (ProjSpace.toProj_preimage_chart _ t ht i).le) hj
    · rw [← resG_pullSecOn V.ι _ (hσ _) j hj, ← resG_pullSecOn V.ι _ (hσ _) j hj]
      exact ProjSpace.sec_eq_pullRatio_toProj_mul _ t ht i k j hi hj
  refine ⟨ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht, ProjSpace.toProj_str _ t ht, key, ?_⟩
  generalize ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht = π at key
  intro K _ x j hx
  obtain ⟨i, hi⟩ := Points.exists_le_preimage_of_iSup_eq_top (x ≫ π) (ProjSpace.iSup_chart o m)
  have hT : ⊤ ≤ x ⁻¹ᵁ (π ⁻¹ᵁ ProjSpace.chart o m i ⊓ V.ι ⁻¹ᵁ (V ⊓ B.U j)) :=
    fun z hz => ⟨hi hz, (x z).2, hx hz⟩
  obtain ⟨hu, hk⟩ := key i j _ inf_le_left inf_le_right
  have hu' := hu.map (Points.valMap x _ hT).hom
  rw [← Points.valR_eq] at hu'
  refine ⟨i, hu'.unit, hi, fun k => ?_⟩
  have := congrArg (valR x _) (hk k)
  rw [Points.valR_mul x _ hT, Points.valR_appLE x _ _ hT, ProjSpace.pullRatio, Points.valR_appLE x _ _ hT] at this
  exact this.trans (mul_comm _ _)

end GlobalTheory.ZH.CoordMap
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.isClosedImmersionBySections_of_span : (∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsProper p] (H : LB X), H.IsLB → ∀ (I J : Type) [Fintype I] [Fintype J] (t : I → H.Sec) (s : J → H.Sec), ImmBy p H t Set.univ → (∀ i, ∃ a : J → k, IsLin p s a (t i)) → ImmBy p H s Set.univ) := by
  first | exact @GlobalTheory.ZH.SpanImm.immBy_of_span | exact GlobalTheory.ZH.SpanImm.immBy_of_span | (intros; apply GlobalTheory.ZH.SpanImm.immBy_of_span <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

theorem _root_.GlobalTheory.T.exists_principalPolarisation_abelianFibre : PolBaseChangeSt → ∀ (k : Type) [Field k] (Φ : FibPre k) (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (s : Sp k ⟶ Sp R) (π : Φ.E.B.left ⟶ D.P.A.left), IsGrpPullback Φ.E.B D.P.A s π → ∀ (xe : Φ.E.X → D.X), (∀ χ, LBIso (Φ.E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) → ∀ (N : ℕ), Nonempty (ChartPull Φ.N₀ (npw D.P.L N) π) → ∃ pol : Φ.Pol N, pol.PB.g = D.P.g := by
  first | exact @GlobalTheory.ZH.UFib.exists_pol | exact GlobalTheory.ZH.UFib.exists_pol | (intros; apply GlobalTheory.ZH.UFib.exists_pol <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem FibPre.exists_pure_ne_zero_at :
    Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N : ℕ), 4 ≤ N → Φ.Pol N → ∀ (α : Φ.E.X) (x : Φ.Pt), ∃ φ : (Φ.H 1).Sec, Φ.Pure α φ ∧ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) := by
  intro hL hL2 k _ _ Φ N hN π α x
  obtain ⟨s, hs⟩ := GlobalTheory.TwistNoBasePoint.exists_sec_twist hL hL2 k π.PB (N * 1) (by omega) _
    (x ≫ Φ.D.q ≫ π.β.hom)
  obtain ⟨φ, hφ, h⟩ := (GlobalTheory.T.pureWeightSection_to_twistedPolarisationPower k Φ N 1 π α (by omega) le_rfl).2 s
  exact ⟨φ, hφ, (h x).2 hs⟩

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.VeryAmpleMove

variable {k : Type} [CommRing k] {X Y : Scheme.{0}}

theorem immBy_pull {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (ψ : Y ⟶ X) [IsIso ψ] (hq : ψ ≫ p = q) {L : LB X} {M : LB Y}
    (hL : L.IsLB) (hM : M.IsLB) (H : LBIso M (L.pull ψ)) {J : Type} (s : J → L.Sec) (J₀ : Set J)
    (hs : ImmBy p L s J₀) : ∃ t : J → M.Sec, ImmBy q M t J₀ := by
  obtain ⟨W, hW⟩ := H
  obtain ⟨hcov, hs⟩ := hs
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hL hM (s i)
  have loc : ∀ i, Out.nonzeroLocus (s' i) = ψ ⁻¹ᵁ Out.nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
      (mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hL (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hM y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨s', ?_, fun i hi => ?_⟩
  · simp only [loc]
    rw [← Scheme.Hom.preimage_top ψ, ← hcov]
    simp only [Scheme.Hom.preimage_iSup]
  obtain ⟨haff, r, hr, hsurj⟩ := hs i hi
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hL (ψ y)
    have hm : ψ y ∈ Out.nonzeroLocus (s i) ⊓ L.U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  · have hsur := VeryAmpleCharts.appLE_surjective (ψ := ψ) _ _ (loc i)
    have hc : ∀ a, (ψ.appLE _ _ (loc i).le).hom (constFn p (Out.nonzeroLocus (s i)) a) =
        constFn q (Out.nonzeroLocus (s' i)) a := fun a => by
      subst hq
      unfold constFn
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
      erw [Scheme.Hom.appLE_comp_appLE]
    have e := congrArg (Subring.map (ψ.appLE _ _ (loc i).le).hom) hsurj
    rw [RingHom.map_closure, ← RingHom.range_eq_map, RingHom.range_eq_top.2 hsur, Set.image_union,
      ← Set.range_comp, ← Set.range_comp] at e
    rw [← e]
    congr 2
    exact congrArg Set.range (funext fun a => (hc a).symm)

theorem immBy_lbPow (hA : Out.AmpleSt) (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ)
    (hN : 4 ≤ N) : ∃ (m : ℕ) (s : Fin m → (lbPow P.L N).Sec), ImmBy P.A.hom (lbPow P.L N) s Set.univ := by
  obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow hA K P N hN
  refine ⟨m + 1, s, by simpa using hcov, fun i _ => ?_⟩
  obtain ⟨haff, r, hr, hf⟩ := hs i
  refine ⟨haff, r, hr, top_le_iff.1 fun f _ => ?_⟩
  obtain ⟨F, rfl⟩ := hf f
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂_C]
    exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  | add F G hF hG =>
    rw [MvPolynomial.eval₂_add]
    exact add_mem (hF trivial) (hG trivial)
  | mul_X F j hF =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact mul_mem (hF trivial) (Subring.subset_closure (Or.inr ⟨j, rfl⟩))

theorem exists_immBy_abelianPart : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N : ℕ), 4 ≤ N → Φ.Pol N → ∃ (m : ℕ) (t : Fin m → Φ.N₀.Sec), ImmBy Φ.E.B.hom Φ.N₀ t Set.univ) := by
  intro hL _ k _ _ Φ N hN P
  obtain ⟨m, s, hs⟩ := immBy_lbPow hL.ample k P.PB N hN
  have : IsIso P.β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map P.β.hom))
  obtain ⟨t, ht⟩ := immBy_pull P.β.hom.left (Over.w P.β.hom) (DVR.linComb_isLB _ P.PB.isLB _ _) Φ.isLB P.w₀ s _ hs
  exact ⟨m, t, ht⟩

end GlobalTheory.VeryAmpleMove
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem isProper_hom_of_relAmple {T : Scheme.{0}} {A : Over T} [GrpObj A] {B : LB A.left} (h : RelAmple A B) :
    IsProper A.hom := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) (fun U : T.affineOpens => U.1)
    (iSup_affineOpens_eq_top T) fun U => ?_
  have h₁ := projProper _ _ _ (GlobalTheory.ProjSpace.isProjOver_morphismRestrict_of_relAmple h U.2)
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsProper) _ U.2.isoSpec.hom).1 h₁

theorem abOpen_of_isOpen_abLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → IsOpen (abLocus Z.G) → GlobalTheory.Models.AbOpen Z.G := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Z _ hO
  letI := Z.grp
  let W : M.Z.Opens := ⟨abLocus Z.G, hO⟩
  refine ⟨W, rfl, ?_⟩
  have h : IsProper (pullback.snd Z.G.hom W.ι) := isProper_hom_of_relAmple (Z.pol W le_rfl).1
  unfold morphismRestrict
  infer_instance

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem immBy_of_spans (hA : AmpleSt) {R : Type} [CommRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) {N : ℕ}
    (hN : 4 ≤ N) {J : Type} [Fintype J] (s : J → LB.Sec (LPow P.A P.L N (baseOver (Sp R))))
    (hs : ∀ σ : LB.Sec (LPow P.A P.L N (baseOver (Sp R))), ∃ c : J → Γ((baseOver (Sp R)).left, ⊤),
      ∀ j, σ.f j = ∑ i, liftFun P.A _ (c i) * (s i).f j) :
    ImmBy (baseOver (Sp R) ⊗ P.A).hom (LPow P.A P.L N (baseOver (Sp R))) s Set.univ := by
  have := P.isAb.proper
  have hT : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  have hL : IsLocallyNoetherian (Sp R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
  have key := (AmpleSpan.embedsBy_of_isPullback P.A P.isLB (hA _ P N hN).2 (isAffineOpen_top (Sp R))
    (g := (baseOver (Sp R)).hom ≫ (Sp R).topIso.inv) (φ := (snd (baseOver (Sp R)) P.A).left)
    (f' := (fst (baseOver (Sp R)) P.A).left) (K := Fin 1) (ε := fun _ => (N : ℤ))
    (by rw [AmpleSpan.comp_topIso_inv_ι]; exact (IsPullback.of_hasPullback _ P.A.hom).flip) (by simp) s
    (fun σ => hs σ)).1
  have e : (baseOver (Sp R) ⊗ P.A).hom = (fst (baseOver (Sp R)) P.A).left :=
    (Over.w (fst (baseOver (Sp R)) P.A)).symm.trans (Category.comp_id _)
  rw [SpanImm.immBy_iff, e]
  exact key

theorem ThetaSys.Real.immBy_basis : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), ImmBy (baseOver (Sp S.R) ⊗ ρ.P.A).hom (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))) ρ.s Set.univ := by
  intro hL o Ω _ _ _ _ S ρ
  have := ArithBase.ded (o := o) (Ω := Ω)
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  have hN : 4 ≤ S.N := by
    have h : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]
    exact Nat.pow_le_pow_left h 2
  exact immBy_of_spans hL.1.ample ρ.P hN ρ.s fun σ => (ρ.s_basis σ).exists

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

theorem _root_.GlobalTheory.T.torsionLabelSystems_series_scalar_independent_of_level : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), Odd n → Labels N EF ζ lab → Labels N' EF ζ' lab' → (∀ j, ∃ c : Cˣ, ∀ x, N'.tx (n ^ j) (lab' _ x) = c * N.tx (n ^ j) (lab _ x)) → (∃ x, N.tx (n ^ 1) (lab _ x) ≠ 0) → ∃ c₀ : C, c₀ ≠ 0 ∧ ∀ j x, N'.tx (n ^ j) (lab' _ x) = c₀ * N.tx (n ^ j) (lab _ x) := by
  first | exact @GlobalTheory.ModelData.Scalar.scalar_const | exact GlobalTheory.ModelData.Scalar.scalar_const | (intros; apply GlobalTheory.ModelData.Scalar.scalar_const <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

theorem _root_.GlobalTheory.T.exists_good_torsion_translate_geometricPoint : Laws → ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (n : ℕ), 2 ≤ n → (n : K) ≠ 0 → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ a : Over.mk x ⟶ P.A, ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ ∀ (z : baseOver S ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver S).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (v : Γ((baseOver S).left, ⊤)), (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ z = a * y → τ.IsGen → IsValueAt P.A P.L 1 th z τ v → v ≠ 0 := by
  first | exact @GlobalTheory.ThetaReal.exists_good_translate | exact GlobalTheory.ThetaReal.exists_good_translate | (intros; apply GlobalTheory.ThetaReal.exists_good_translate <;> assumption)
end
