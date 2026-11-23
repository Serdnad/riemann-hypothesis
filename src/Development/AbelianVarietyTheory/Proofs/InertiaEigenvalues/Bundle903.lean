module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle020
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle518
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle499
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle856
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle804
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle831
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle893
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct




noncomputable section

namespace GlobalTheory.RankDescent

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem charZero_frac (i : X.Tw) : CharZero (FractionRing (X.O i)) :=
  (RingHom.charZero_iff ((IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
      (L := FractionRing (X.O i)) (X.O_inj i)).comp (X.emb0 i)).injective).1 inferInstance

theorem eG_eG (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    Formalism.MainNotions.IntegralHeckeForms.eG Y i j b (Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x) = Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x := by
  have h := congrArg (MonoidAlgebra.lift (FractionRing (X.O i)) (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b))) (Y.eAlg_idem i b)
  rw [map_mul] at h
  exact LinearMap.congr_fun h x

theorem good_idempotent_fixes_mem_good_type_space (i : X.Tw) (j : ℕ) (b : Bool) {x : Y.Fm i j b} (hx : x ∈ V0 Y i j b) :
    Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x = x := by
  obtain ⟨y, -, rfl⟩ := hx
  exact eG_eG Y i j b y


open Formalism.MainNotions.IntegralHeckeForms in
theorem AO_eq (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    AO Y i j b x = ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • eG Y i j b x := by
  show ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) • eG Y i j b x = _
  rw [← map_natCast (algebraMap (X.O i) (FractionRing (X.O i))), algebraMap_smul]


open Formalism.MainNotions.IntegralHeckeForms in
theorem thetaSeries_mem_goodTypeForms (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) (a : Y.Dat i j b) (ha : a ∈ E.Dat0 i j b) :
    Y.th i j b a ∈ Fm0 Y i j b := by
  simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u
  have := E.theta_base_equivariant i j b a ha u
  simp [this]


open Formalism.MainNotions.IntegralHeckeForms in
theorem AO_Th_le (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) :
    ∀ x ∈ (Th Y i j b (SgJ Y E i j b)).map (AO Y i j b), x ∈ V0 Y i j b := by
  rintro _ ⟨y, hy, rfl⟩
  rw [AO_eq]
  refine Submodule.smul_mem _ _ ⟨y, ?_, rfl⟩
  refine (Submodule.span_le (p := (Fm0 Y i j b).restrictScalars (X.O i))).2 ?_ hy
  rintro _ ⟨a, ha, rfl⟩
  exact thetaSeries_mem_goodTypeForms Y E i j b a ha


open Formalism.MainNotions.IntegralHeckeForms in
theorem fullRk_of_le (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool)
    (h : V0 Y i j b ≤ Submodule.span (FractionRing (X.O i)) (eG Y i j b '' (Y.th i j b '' E.Dat0 i j b))) :
    FullRk Y E i j b (SgJ Y E i j b) := by
  haveI := charZero_frac (X := X) i
  have hc : ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) ≠ 0 := Nat.cast_ne_zero.2 D.what₂.restRowsFiniteGroupCard_pos.ne'
  refine ⟨subset_rfl, AO_Th_le Y E i j b, le_antisymm (Submodule.span_le.2 (AO_Th_le Y E i j b)) (h.trans ?_)⟩
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  have e1 : eG Y i j b (Y.th i j b a) = ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i))⁻¹ • AO Y i j b (Y.th i j b a) := by
    rw [AO_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [SetLike.mem_coe, e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Submodule.subset_span ⟨a, ha, rfl⟩, rfl⟩)

section Descent

variable {ρ : Setup X} {i : X.Tw} {j : Fin D.R.m} {b : Bool}

theorem rd_mem_span (rd : Rd ρ Y i j b) (S : Set (Y.Fm i ((j : ℕ) + 1) b)) {y : Y.Fm i ((j : ℕ) + 1) b}
    (hy : y ∈ Submodule.span (FractionRing (X.O i)) S) : rd y ∈ Submodule.span ℂ (rd '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

theorem mem_span_of_faithful {rd : Rd ρ Y i j b} (hf : Faithful rd) (S : Set (Y.Fm i ((j : ℕ) + 1) b))
    {x : Y.Fm i ((j : ℕ) + 1) b} (hx : rd x ∈ Submodule.span ℂ (rd '' S)) :
    x ∈ Submodule.span (FractionRing (X.O i)) S := by
  set W := Submodule.span (FractionRing (X.O i)) S
  by_contra hxW
  let bW := Module.finBasis (FractionRing (X.O i)) W
  let v : Fin (Module.finrank (FractionRing (X.O i)) W) → Y.Fm i ((j : ℕ) + 1) b := fun k => (bW k : Y.Fm i ((j : ℕ) + 1) b)
  have hv : LinearIndependent (FractionRing (X.O i)) v := bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hspan : Submodule.span (FractionRing (X.O i)) (Set.range v) = W := by
    have := congrArg (Submodule.map W.subtype) bW.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  have hli : LinearIndependent (FractionRing (X.O i)) (Fin.cons x v : Fin _ → Y.Fm i ((j : ℕ) + 1) b) :=
    linearIndependent_finCons.2 ⟨hv, by rw [hspan]; exact hxW⟩
  have hC := hf _ _ hli
  have hC' : LinearIndependent ℂ (Fin.cons (rd x) (fun k => rd (v k)) : Fin _ → (GA D (Wc D j) → ℂ)) := by
    convert hC using 1
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  refine (linearIndependent_finCons.1 hC').2 ?_
  refine Submodule.span_le.2 ?_ hx
  rintro _ ⟨s, hs, rfl⟩
  have hsW : s ∈ Submodule.span (FractionRing (X.O i)) (Set.range v) := by
    rw [hspan]; exact Submodule.subset_span hs
  have := rd_mem_span Y rd _ hsW
  rw [← Set.range_comp] at this
  exact this

end Descent

theorem fullRk_of_spanGood : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), Comparison₂ hρ rd → (∀ i j b, Faithful (rd i j b)) → ∀ (E : IntegralHeckeForms.XD D) (i : D.ntw.Tw), (∀ j b, RatBase (rd i j b)) → (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b a, a ∈ E.Dat0 i j b) → SpanGood rd i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  intro D ρ hρ rd T hF E i hR hall hS j hj b
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j' : Fin D.R.m, j = (j' : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine fullRk_of_le D.nexp E i _ b ?_
  intro x hx
  have h1 : rd i j' b x ∈ Submodule.span ℂ (rd i j' b '' (D.nexp.th i _ b '' E.Dat0 i _ b)) := by
    refine Submodule.span_mono ?_ (hS j' b x hx)
    rintro _ ⟨s, h, P, hd, rfl⟩
    obtain ⟨d, -, hc, hp⟩ := (T i j' b).dat_onto s h P hd (hR j' b s h P hd)
    refine ⟨D.nexp.th i _ b d, ⟨d, hall _ hj b d, rfl⟩, ?_⟩
    rw [(T i j' b).th_eq d, hc, hp]
  have h2 := mem_span_of_faithful D.nexp (hF i j' b) _ h1
  rw [← good_idempotent_fixes_mem_good_type_space D.nexp i _ b hx]
  have h3 := Submodule.mem_map_of_mem (f := Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i ((j' : ℕ) + 1) b) h2
  rwa [Submodule.map_span] at h3

end GlobalTheory.RankDescent

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section

namespace GlobalTheory.TwistLiftW

theorem isLevelLift_base_of_realisation_lift : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (g : X.Γ) (κ : GA D (Wc D j)),
    Lev.IsLevelLift (Wc D j) (X.R.βW j) (X.R.datWp j X.R.triv) (X.R.eG g) κ →
    Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b (X.cG (X.R.eG g))) κ := by
  intro D X E Y i j b g κ h
  have P := Y.Z.pin
  have rW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  have hβ := P.frT i j b
  have hP := P.Pg i j b
  have tri : ∀ (PP : Pl D.host.E) (r t : ℕ), r = (Wc D j).rank → ∀ x : GL (Fin (Wc D j).rank) (kP PP),
      x ∈ blockTri (blkOf r t) := fun PP r t hr x => mem_blockTri.2 fun a c hac => by
    have ha : a.val < r := lt_of_lt_of_eq a.2 hr.symm
    have e : blkOf r t a = 0 := if_pos ha
    exact absurd (lt_of_lt_of_eq hac e) (Nat.not_lt_zero _)
  refine ⟨h.1, mem_parLev.2 ⟨parLev_UA h.2.1, ?_, fun PP _ => tri PP _ _ rfl _,
    fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, ?_⟩
  · rw [hβ]; exact parLev_St h.2.1
  · funext PP
    obtain ⟨PP, hPP⟩ := PP
    have hPP' : PP ∈ X.R.Pg := hP ▸ hPP
    refine Units.ext (Matrix.ext fun a c => ?_)
    have e1 := P.grp i j b (X.cG (X.R.eG g)) PP hPP hPP' a c
    rw [MulEquiv.symm_apply_apply] at e1
    refine Eq.trans ?_ e1.symm
    rw [← h.2.2, hβ]
    have e2 := upper_block_val_submatrix (le_refl _) (blockTri_blkOf_le _ 1 (tri PP _ 1 rfl (redFn (X.R.βW j) PP (Lev.finE (Wc D j) κ))))
    have e3 := upper_block_val_submatrix rW.ge (blockTri_blkOf_le _ 1 (tri PP _ 1 rW.symm (redFn (X.R.βW j) PP (Lev.finE (Wc D j) κ))))
    exact (congrFun (congrFun e2 a) c).trans (congrFun (congrFun e3 (Fin.cast rW a)) (Fin.cast rW c)).symm

end GlobalTheory.TwistLiftW

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section



namespace GlobalTheory.TwInputs

theorem univSup_of_xi : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd → Laws hρ rd → XiType rd → XiBdd rd → ∀ E : IntegralHeckeForms.XD D, UnivSup D E := by
  intro D ρ hρ rd F L hT hB E i hi j hj b a _
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj1
  let j' : Fin D.R.m := ⟨n, hj2⟩
  have T := F.tie i j' b
  obtain ⟨c, hc⟩ := hB i hi j' b _ _ _ (T.dat a)
  refine ⟨c, fun Q M hs hcl hS hlev => ?_⟩
  have hQ : InRange D.ntw i Q := ⟨hs, hcl, hS⟩
  have hnp : ∀ v ∈ Q, ((normProd (T.supp a) : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal :=
    fun v hv h => Finset.disjoint_left.1 hlev hv ((T.lev_iff a v).2 h)
  obtain ⟨x, hx, he⟩ := T.thU_of_rat (L.rat i hi j' b).2.2 M hQ hlev
  classical
  refine ⟨∑ a', Finsupp.single (spread D.nexp i Q M (ρ.ch i) a') (x a'), ?_, fun δ => ?_⟩
  · rw [he, grpSum, ← Finsupp.sum_finsetSum_index (fun _ => by rw [TensorProduct.zero_tmul])
      (fun _ _ _ => by rw [TensorProduct.add_tmul])]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finsupp.sum_single_index (by rw [TensorProduct.zero_tmul])]
  · have h0 : ∀ a', x a' ∈ Fm0 D.nexp i ((j' : ℕ) + 1) b :=
      fun a' => hT i hi j' b Q M hQ _ _ _ (T.dat a) hnp a' (x a') (hx a')
    have h1 : ∀ a', ((D.ntw.l i : D.ntw.O i) ^ c) • x a' ∈ D.nexp.Bsup i ((j' : ℕ) + 1) b :=
      fun a' => hc Q M hQ hnp a' (x a') (hx a')
    rw [Finsupp.finsetSum_apply]
    refine ⟨Submodule.sum_mem _ fun a' _ => ?_, ?_⟩
    · rw [Finsupp.single_apply]; split_ifs
      · exact h0 a'
      · exact zero_mem _
    · rw [Finset.smul_sum]
      refine Submodule.sum_mem _ fun a' _ => ?_
      rw [Finsupp.single_apply]; split_ifs
      · exact h1 a'
      · rw [smul_zero]; exact zero_mem _

end GlobalTheory.TwInputs
end
end

section




open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntExpOnto

theorem exists_harm_complex {D : D7} (m n : ℕ) (w : _root_.GlobalTheory.ExportSeries.Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m)
    (F : Pol ℂ D.what₂.Tau n) (hF : F ∈ VV ℂ w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn (RingHom.id ℂ) w.lam F := by
  obtain ⟨s, hs⟩ := GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta D m n w B hw hm
  have hs0 : ((s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have key : ∀ u : GLR D n, harmFn m w B (fockGL m w B u (w.delta m)) =
      ((s : ℤ) : ℂ) • Onto.coefLin w.lam (actP w.lam (invTrK (u * B)) (ten fun τ => extremal ℂ n (w.lam τ))) := fun u => by
    funext x
    rw [harmFn_fockGL, hs, Pi.smul_apply, smul_eq_mul]
    congr 1
    change _ = coefFn _ _ _ _
    rw [Onto.coefFn_actP, _root_.mul_inv_rev, mul_assoc]
  have hle : (VV ℂ w.lam).map (Onto.coefLin w.lam) ≤ (harm m w B).map (harmFn m w B) := by
    rw [GlobalTheory.OrbitSpan.VV_eq_span_orbit, harm, Submodule.map_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have h2 := key (invTrK g * B⁻¹)
    rw [inv_mul_cancel_right, Onto.invTrK_invTrK] at h2
    refine (Submodule.smul_mem_iff _ hs0).1 ?_
    beta_reduce
    rw [← h2]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
  exact hle ⟨F, hF, rfl⟩

theorem exists_harm {D : D7} (m n : ℕ) (w : _root_.GlobalTheory.ExportSeries.Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m)
    {K : Type} [Field K] [CharZero K] (σ : K →+* ℂ) (F : VV K w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn σ w.lam (F : Pol K D.what₂.Tau n) := by
  obtain ⟨P, hP, e⟩ := exists_harm_complex m n w B hw hm (MvPolynomial.map σ F.1) (GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ F.2)
  refine ⟨P, hP, e.trans (funext fun x => ?_)⟩
  rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]

theorem onto : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b (F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam), ∃ P ∈ (Y.Z.ρ.B i j b).valSpace, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) := by
  intro _ _ _ D X E Y _ _ i _ j b F
  have hB := Y.Z.good.base i j b
  refine exists_harm _ _ _ _ hB.wt (fun τ => ?_) _ F
  have h1 := hB.sig τ
  have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
  rw [← h1] at h2
  exact h2.le

end GlobalTheory.IntExpOnto
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem levelOf_of_serSide {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D} (Y : SerSide X E) : Y.Z.ρ.LevelOf D.nexp :=
  ⟨fun i j b g => (Y.Z.tie i j b).U_eq g, fun i j b u hu => (Y.Z.tie i j b).psiU_eq u hu⟩

end GlobalTheory.TwInputs
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PinBase

theorem baseOf_of_pin : ∀ (D : D7) (X : RealSide D) (ρ : Setup D.ntw), ρ.Good → RealPin X.R X.cG ρ → ∀ i j b, GlobalTheory.ConjTwist.BaseOf X.R.toRealDat j (ρ.B i j b) := by
  intro D X ρ hρ hp i j b
  have hB := hρ.base i j b
  have hL : X.R.toLevCh.Is X.A3.A.μ0 := X.char.lev
  have hlam := GlobalTheory.BaseLiftWeight.lam_eq D _ X.R.toLevCh X.A3.A.μ0 j (ρ.B i j b) hL hB (hp.mu0 i j b) (hp.ap i j b) (hp.am i j b)
  have hc : ∀ τ, (ρ.B i j b).w.c τ = GlobalTheory.ConjTwist.liftC D j τ := fun τ =>
    GlobalTheory.BaseLiftWeight.c_eq hL hB (hp.mu0 i j b) τ
  have hP : (ρ.B i j b).w.p = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS D j := funext fun τ => congrArg Prod.fst (hB.sig τ)
  have hQ : (ρ.B i j b).w.q = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS D j := funext fun τ => congrArg Prod.snd (hB.sig τ)
  have hAP : (ρ.B i j b).w.ap = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aP D j := funext fun τ => hp.ap i j b τ
  have hAM : (ρ.B i j b).w.am = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aM D j := funext fun τ => hp.am i j b τ
  refine
    { ψ := hp.psi i j b, θ := hp.inf i j b, sT := hp.cartT i j b, BS := hp.onbS i j b, BT := hp.onbT i j b,
      ΛS := hp.latS i j b, ΛT := hp.latT i j b, βS := hp.frS i j b, βT := hp.frT i j b, vac := hp.vac i j b,
      Pg := hp.Pg i j b, mu0 := hp.mu0 i j b, eta := hp.eta i j b, lam := hlam, delta := ?_, p := hP, q := hQ,
      c := funext hc }
  rw [← GlobalTheory.ConjTwist.liftWeight_delta, Weight.delta, Weight.delta, hP, hQ, hAP, hAM]
  rfl

end GlobalTheory.PinBase
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.TwUnit

theorem isKsForm_and_unit : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j, 1 ≤ j → j ≤ D.R.m → (Y.S.A j).IsKsForm) ∧ ∀ i b P, P ∉ D.ntw.S0 i → ∃ u : (D.ntw.O i)ˣ, Y.H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u := by
  intro D X E Y
  refine ⟨fun j h1 h2 => ?_, fun i b P hP => ?_⟩
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
    exact GlobalTheory.isKsForm_of_formsIso _ _ (Y.YS.fi ⟨n, h2⟩) (X.integral ⟨n, h2⟩).1
  · obtain ⟨σ, -, hσ⟩ := GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)
    exact ⟨Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom
      (if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹), Y.del i b P hP σ hσ⟩

end GlobalTheory.TwUnit
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwHkSS

theorem hkSS_of_sides : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), CommG D → HkComm D → SupFull D → HkSS D := by
  intro D X E Y hG hC hSF
  have hX : Formalism.IndefR.NX.NExpHeckeRowX X.R X.cG Y.S Y.YS Y.H (fun j => Formalism.IndefR.NX.goodProjW Y.S j D.nexp.eLL0) :=
    ⟨fun i k P hs ho _ _ hk α R hα hR x _ => Y.reads i k P hs ho hk α R hα hR x⟩
  exact GlobalTheory.GoodSpan.hkSS_of_rows_guarded X.R X.F X.cG Y.S Y.YS Y.H hG hC hSF hX X.char X.unif X.integral
    (fun i P P' hP hc => Y.Z.good.goodSetup_badPlaces_conj i P hP P' hc) (fun i => Y.Z.good.goodSetup_placesOverTwo_subset i) Y.Sb
    (fun i _ j hj b k P hk x => Y.hk_emb i j b k P x (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2 hk)
    Y.B_range Y.hk_split

end GlobalTheory.TwHkSS
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false



noncomputable section

namespace GlobalTheory.SupLaw

theorem hkComm_of_ties : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), HkComm D := by
  intro D X E Y
  have hC : GlobalTheory.ExportPin.Model.Covered X.R := GlobalTheory.ExportPin.Model.covered_of_allPlaces X.R X.char.lev X.char.allPl
  exact hkComm_of_family X.R X.cG Y.S Y.YS Y.H.hL Y.H.hs Y.H.cHk Y.H.hkEq fun i j a b k P k' P' hk hk' =>
    family_comm X.R X.cG Y.S Y.YS X.char.lev X.char.fam X.char.models.HW
      (fun n => GlobalTheory.ExportPin.Model.j_injective X.R X.unif n _) hC Y.H.hL
      (fun i n k P hk α R ha hR => ⟨_, fun x => Y.reads n k P hk.2.2.1 (hC i P hk.2.2.2 hk.2.2.1) hk.2.1 α R ha hR x⟩)
      i j a b k P k' P' hk hk'

end GlobalTheory.SupLaw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult



noncomputable section

namespace GlobalTheory.HeckeDetValue

theorem chr_detAt : ∀ {D : D7} (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (Q : Finset (Pl D.host.E)) (V : HSp D) (P : Pl D.host.E) (k : ℕ) (α : GA D V) (z : (AE D)ˣ), ChrEq c χ → GlobalTheory.ExportSeries.UnramOutside c Q → GlobalTheory.ExportSeries.SplitSet Q → Bridge.SplitOff P (Q : Set (Pl D.host.E)) → IsHeckeAt V P k α → IsDetAt (idemAt P) V α z → ((c z : Circle) : ℂ) = ((χ.val P : ℂˣ) : ℂ) ^ k := by
  intro D c χ Q V P k α z hc hU hS hoff hα hz
  exact GlobalTheory.HeckeDetChar.chi_detAt hc hU hS hoff hα hz

end GlobalTheory.HeckeDetValue
end
end
