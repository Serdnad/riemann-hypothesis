module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemSubringOfLocalInverse
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2265
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.AmplePull

theorem ampleAt_pull : ∀ (Y X : Scheme.{0}) (π : X ⟶ Y) [IsAffineHom π] (N : LB Y), N.IsLB → ∀ x : X,
    AmpleAt N (π x) → AmpleAt (N.pull π) x := by
  intro Y X π _ N hN x h
  obtain ⟨m, A, s, hm, hA, hAmp, hy⟩ := h
  have hNm : (lbPow N m).IsLB := isLB_lbPow hN m
  have hP : (LB.div (lbPow N m) A).IsLB := LB.isLB_div hNm hA
  have hN' : (N.pull π).IsLB := LB.isLB_pull hN π
  have hA' : (A.pull π).IsLB := LB.isLB_pull hA π
  have hNm' : (lbPow (N.pull π) m).IsLB := isLB_lbPow hN' m
  have hQ : (LB.div (lbPow (N.pull π) m) (A.pull π)).IsLB := LB.isLB_div hNm' hA'
  have iso : LBIso (LB.div (lbPow (N.pull π) m) (A.pull π)) ((LB.div (lbPow N m) A).pull π) := by
    rw [← cls_eq_iff hQ (LB.isLB_pull hP π), cls_div hNm' hA' hQ, cls_pull hP π, cls_div hNm hA hP,
      cls_lbPow hN' m hNm', cls_pull hN π hN', cls_pull hA π hA', cls_lbPow hN m hNm, map_sub, map_nsmul]
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hQ (LB.isLB_pull hP π) iso (ZM.RepBC.secPull _ π s)
  refine ⟨m, A.pull π, t, hm, hA', hAmp.pull_of_isAffineHom π, ?_⟩
  rw [ht, GlobalTheory.ZV.GraphSystem.nonzeroLocus_pull]
  exact hy

end GlobalTheory.AmplePull
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.DegSep

variable {S : Scheme.{0}}

theorem one_left' (T : Over S) (G : Over S) [GrpObj G] : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  have h := Over.w (toUnit T)
  change (toUnit T ≫ η[G]).left = _
  rw [Over.comp_left]
  congr 1

theorem comp_pow_id (T G : Over S) [GrpObj G] (x : T ⟶ G) (n : ℕ) : x ≫ (𝟙 G) ^ n = x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

end GlobalTheory.AV.DegSep

namespace GlobalTheory.AV.DegSep

theorem isUnit_natCast_Γ (K : Type) [Field K] (n : ℕ) (hn : (n : K) ≠ 0) : IsUnit (n : Γ(Sp K, ⊤)) := by
  have h : IsUnit (n : K) := hn.isUnit
  have := h.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  simpa using this

theorem deg_eq_card_ker (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (n : ℕ) (hn : (n : K) ≠ 0)
    (hiso : IsIsogeny f) (hker : ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1) :
    deg f = Nat.card (ptMap f).ker := by
  have hfl : Flat f.hom.left := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hiso).2.1
  have hfin : IsFinite f.hom.left := hiso.1
  have hprop : IsProper B.X.hom := B.ab.proper
  let e : Sp K ⟶ B.X.left := η[B.X].left
  have he1 : e ≫ B.X.hom = 𝟙 _ := Over.w η[B.X]
  have hecl : IsClosedImmersion e := by
    have : IsClosedImmersion (e ≫ B.X.hom) := by rw [he1]; infer_instance
    exact IsClosedImmersion.of_comp e B.X.hom
  let p := pullback.snd f.hom.left e
  let i := pullback.fst f.hom.left e
  have hpi : i ≫ A.X.hom = p := by
    calc i ≫ A.X.hom = i ≫ f.hom.left ≫ B.X.hom := by rw [Over.w f.hom]
      _ = p ≫ e ≫ B.X.hom := by rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = p := by rw [he1, Category.comp_id]
  have hifu : FormallyUnramified i := inferInstance

  let T : Over (Sp K) := Over.mk (i ≫ A.X.hom)
  let x : T ⟶ A.X := Over.homMk i
  have hx1 : x ≫ f.hom = 1 := by
    ext1
    rw [Over.comp_left, one_left']
    change i ≫ f.hom.left = (i ≫ A.X.hom) ≫ e
    rw [hpi, pullback.condition]
  have hxn := hker T x hx1
  have hleft : i ≫ (Out.mulA A.X n).left = p ≫ η[A.X].left := by
    have h : (x ^ n).left = (1 : T ⟶ A.X).left := by rw [hxn]
    rw [← comp_pow_id, one_left'] at h
    change i ≫ (Out.mulA A.X n).left = _ at h
    rw [h]
    change (i ≫ A.X.hom) ≫ _ = _
    rw [hpi]
  let j : pullback f.hom.left e ⟶ pullback (Out.mulA A.X n).left η[A.X].left :=
    pullback.lift i p hleft
  have hmu : FormallyUnramified (Out.mulA A.X n).left :=
    GlobalTheory.formallyUnramified_mulA (Sp K) A.X n (isUnit_natCast_Γ K n hn)
  have hsnd : FormallyUnramified (pullback.snd (Out.mulA A.X n).left η[A.X].left) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hmu
  have hjfu : FormallyUnramified j := by
    have : FormallyUnramified (j ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; exact hifu
    exact FormallyUnramified.of_comp j (pullback.fst _ _)
  have hpfu : FormallyUnramified p := by
    have : j ≫ pullback.snd _ _ = p := pullback.lift_snd _ _ _
    rw [← this]
    exact MorphismProperty.comp_mem (@FormallyUnramified) _ _ hjfu hsnd
  have hpet : Etale p := Etale.of_formallyUnramified_of_flat p

  let t : Sp (AlgebraicClosure K) ⟶ Sp K := (ptOver K (AlgebraicClosure K)).hom
  obtain ⟨-, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank p t (IsLocalRing.closedPoint _)
  rw [Scheme.Hom.finrank_pullback_snd] at hcard
  have horig : e (t (IsLocalRing.closedPoint _)) = B.origin := by
    rw [origin, one_left']
    change e _ = (𝟙 (Sp K) ≫ e) _
    rw [Category.id_comp]
    congr 1
    exact Subsingleton.elim _ _
  rw [horig] at hcard
  rw [deg, if_pos hiso, ← hcard]
  symm
  refine Nat.card_congr ?_
  exact
    { toFun := fun y => ⟨pullback.lift y.1.left t (by
          have h := y.2
          rw [MonoidHom.mem_ker, ptMap_apply] at h
          have h2 : (y.1 ≫ f.hom).left = (1 : ptOver K (AlgebraicClosure K) ⟶ B.X).left := by rw [h]
          rw [Over.comp_left, one_left'] at h2
          exact h2), pullback.lift_snd _ _ _⟩
      invFun := fun y => ⟨Over.homMk (y.1 ≫ i) (by
          change (y.1 ≫ i) ≫ A.X.hom = t
          rw [Category.assoc, hpi, y.2]), by
          rw [MonoidHom.mem_ker, ptMap_apply]
          ext1
          rw [Over.comp_left, one_left']
          change (y.1 ≫ i) ≫ f.hom.left = t ≫ e
          rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩
      left_inv := fun y => by
        apply Subtype.ext
        ext1
        exact pullback.lift_fst _ _ _
      right_inv := fun y => by
        apply Subtype.ext
        apply pullback.hom_ext
        · exact pullback.lift_fst _ _ _
        · rw [pullback.lift_snd]; exact y.2.symm }

end GlobalTheory.AV.DegSep

namespace GlobalTheory.AV.DegSep

theorem deg_eq_card_ker_of_killed : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (n : ℕ), (n : K) ≠ 0 →
    IsIsogeny f → (∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1) →
    deg f = Nat.card (ptMap f).ker :=
  fun K _ A B f n hn hiso hker => deg_eq_card_ker K A B f n hn hiso hker

end GlobalTheory.AV.DegSep
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isIsogeny_comp_and_deg_comp : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C),
    IsIsogeny f → IsIsogeny g → IsIsogeny (f ≫ g) ∧ deg (f ≫ g) = deg f * deg g := by
  intro K _ A B C f g hf hg
  obtain ⟨-, hflf, -, hrf⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hf
  obtain ⟨-, hflg, -, -⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K B C g hg
  have : IsFinite f.hom.left := hf.1
  have : Surjective f.hom.left := hf.2
  have : IsFinite g.hom.left := hg.1
  have : Surjective g.hom.left := hg.2
  have hc : IsIsogeny (f ≫ g) := by
    refine ⟨?_, ?_⟩
    · rw [comp_hom, Over.comp_left]; infer_instance
    · rw [comp_hom, Over.comp_left]; infer_instance
  refine ⟨hc, ?_⟩
  have hdg : deg g = g.hom.left.finrank C.origin := if_pos hg
  have hdc : deg (f ≫ g) = (f ≫ g).hom.left.finrank C.origin := if_pos hc
  rw [hdc, hdg, comp_hom, Over.comp_left]
  exact GlobalTheory.FinrankComp.finrank_comp_of_const f.hom.left g.hom.left (deg f) hrf C.origin

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem bcMap_isPullback (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f : A ⟶ B) :
    IsPullback (pullback.fst A.X.hom (spMap (algebraMap K L))) (bcMap L f).hom.left f.hom.left
      (pullback.fst B.X.hom (spMap (algebraMap K L))) := by
  have h1 : ((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.snd B.X.hom (spMap (algebraMap K L)) =
      pullback.snd A.X.hom (spMap (algebraMap K L)) :=
    Over.w ((Over.pullback (spMap (algebraMap K L))).map f.hom)
  have h3 : ((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.fst B.X.hom (spMap (algebraMap K L)) =
      pullback.fst A.X.hom (spMap (algebraMap K L)) ≫ f.hom.left :=
    pullback.lift_fst _ _ _
  have h2 : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have hout : IsPullback (pullback.fst A.X.hom (spMap (algebraMap K L)))
      (((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.snd B.X.hom (spMap (algebraMap K L)))
      (f.hom.left ≫ B.X.hom) (spMap (algebraMap K L)) := by
    rw [h1, h2]
    exact IsPullback.of_hasPullback A.X.hom (spMap (algebraMap K L))
  exact IsPullback.of_bot hout h3.symm (IsPullback.of_hasPullback B.X.hom (spMap (algebraMap K L)))

theorem isIsogeny_bcMap_iff_and_deg_bcMap : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A B : AbVar K)
    (f : A ⟶ B), (IsIsogeny (bcMap L f) ↔ IsIsogeny f) ∧ deg (bcMap L f) = deg f := by
  intro K _ L _ _ A B f
  have := GlobalTheory.LevelMap.isFinite_descendsAlong_fpqc
  have sq := bcMap_isPullback K L f
  have hB := IsPullback.of_hasPullback B.X.hom (spMap (algebraMap K L))
  have hs : Surjective (spMap (algebraMap K L)) := GlobalTheory.LevelMap.surjective_spMap _
  have hf : Flat (spMap (algebraMap K L)) := GlobalTheory.LevelMap.flat_spMap _
  have hq : QuasiCompact (spMap (algebraMap K L)) := by unfold spMap; infer_instance
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
      (pullback.fst B.X.hom (spMap (algebraMap K L))) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact MorphismProperty.of_isPullback (P := @Surjective) hB.flip hs
    · exact MorphismProperty.of_isPullback (P := @Flat) hB.flip hf
    · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hB.flip hq
  have hiso : IsIsogeny (bcMap L f) ↔ IsIsogeny f :=
    and_congr (MorphismProperty.iff_of_isPullback (P := @IsFinite) sq.flip hQ)
      (MorphismProperty.iff_of_isPullback (P := @Surjective) sq.flip hQ)
  refine ⟨hiso, ?_⟩
  by_cases h : IsIsogeny f
  · obtain ⟨-, hfl, -, hrk⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f h
    have : IsFinite f.hom.left := h.1
    have e : deg (bcMap L f) = (bcMap L f).hom.left.finrank (baseChange L B).origin := if_pos (hiso.2 h)
    rw [e]
    exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ sq (baseChange L B).origin).trans (hrk _)
  · have e1 : deg (bcMap L f) = 0 := if_neg (fun h' => h (hiso.1 h'))
    have e2 : deg f = 0 := if_neg h
    rw [e1, e2]

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.topForms_graphLocalRing_freelyGenerated : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ')
  (hc : ∀ a, algebraMap ℂ L a ∈ GlobalTheory.DiagLoc.loc L σ),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' →
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  IsFreeGen (GlobalTheory.DiagLoc.loc L σ) (dForm ((algebraMap ℂ L).codRestrict (GlobalTheory.DiagLoc.loc L σ) hc)
    (Fin.append (fun i => GlobalTheory.DiagLoc.toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) (fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1)))) := by
  first | exact @GlobalTheory.DiagLoc.isFreeGen_dForm_graph | exact GlobalTheory.DiagLoc.isFreeGen_dForm_graph | (intros; apply GlobalTheory.DiagLoc.isFreeGen_dForm_graph <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

namespace GlobalTheory.CoordsOrigin

theorem coords_at_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ δ : Fin n → Derivation ℤ (G.left.presheaf.stalk (origin G)) (G.left.presheaf.stalk (origin G)), (∀ a O (hO : origin G ∈ O) f, δ a ((G.left.presheaf.germ O (origin G) hO).hom f) = (G.left.presheaf.germ O (origin G) hO).hom (dd a O f)) → ∃ z : Fin n → G.left.presheaf.stalk (origin G), (∀ i, evO G (z i) = 0) ∧ (∀ a i, evO G (δ a (z i)) = if a = i then 1 else 0) ∧ maximalIdeal (G.left.presheaf.stalk (origin G)) = (maximalIdeal R).map (constO G) ⊔ Ideal.span (Set.range z) := by
  intro R _ _ _ _ G _ _ hsm n v dd hinv δ hδ
  letI : Algebra R (G.left.presheaf.stalk (origin G)) := (constO G).toAlgebra
  obtain ⟨hN, hF, hFin⟩ := GlobalTheory.T.originLocalRing_noetherian_free_unitSectionConormal R G hsm
  have key : ∀ a f, evO G (δ a f) = tanDer G (v a) f := by
    intro a f
    obtain ⟨O, hx, g, rfl⟩ := G.left.presheaf.exists_germ_eq f
    rw [hδ a O hx g]
    exact GlobalTheory.T.invariantVectorField_eval_origin_eq_tangentDerivative R G (v a) (dd a) (hinv a) O hx g
  have hadd : ∀ a x y, tanDer G (v a) (x + y) = tanDer G (v a) x + tanDer G (v a) y := by
    intro a x y
    rw [← key, ← key, ← key, map_add (f := _), map_add (f := _)]
  have hmul : ∀ a x y, tanDer G (v a) (x * y) = evO G x * tanDer G (v a) y + evO G y * tanDer G (v a) x := by
    intro a x y
    rw [← key, ← key, ← key, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul]
  have hc : ∀ a r, tanDer G (v a) (algebraMap R _ r) = 0 := by
    intro a r
    rw [← key]
    show evO G (δ a (constO G r)) = 0
    rw [← GlobalTheory.GermConst.germ_constFn_origin R G ⊤ trivial r, hδ a ⊤ trivial,
      GlobalTheory.Heat.isInv_constFn R G (v a) (dd a) (hinv a) ⊤ r, map_zero, map_zero]
  let φ : TanM (𝟙 (Sp R)) G →+ (G.left.presheaf.stalk (origin G) → R) :=
    { toFun := fun w => tanDer G w
      map_zero' := funext fun f => by
        have h := GlobalTheory.T.tangentDerivativeAtOrigin_smul_tangentVector R G 0 0 f
        rwa [zero_smul, zero_mul] at h
      map_add' := fun u w => funext fun f => GlobalTheory.T.tangentDerivativeAtOrigin_add_tangentVector R G u w f }
  have hlin : ∀ (c : Fin n → R) f, tanDer G (∑ a, c a • v a) f = ∑ a, c a * tanDer G (v a) f := by
    intro c f
    have h1 : tanDer G (∑ a, c a • v a) f = φ (∑ a, c a • v a) f := rfl

    rw [h1, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => GlobalTheory.T.tangentDerivativeAtOrigin_smul_tangentVector R G (c a) (v a) f
  have hbasis : ∀ D : G.left.presheaf.stalk (origin G) → R, (∀ x y, D (x + y) = D x + D y) →
      (∀ x y, D (x * y) = evO G x * D y + evO G y * D x) → (∀ r, D (algebraMap R _ r) = 0) →
      ∃! c : Fin n → R, ∀ x, D x = ∑ a, c a * tanDer G (v a) x := by
    intro D h1 h2 h3
    obtain ⟨w, hw⟩ := GlobalTheory.T.exists_tangentVector_of_originDerivation R G D h1 h2 h3
    refine ⟨fun a => v.repr w a, ?_, ?_⟩
    · intro x
      rw [← hw x, ← hlin]
      congr 1
      exact (v.sum_repr w).symm
    · intro c hc'
      have hw' : ∑ a, c a • v a = w := GlobalTheory.T.tangentVector_eq_of_tangentDerivativeAtOrigin_eq R G _ _ fun f => by rw [hlin, hw, hc' f]
      funext a
      rw [← hw', v.repr_sum_self]
  obtain ⟨z, hz0, hz1, hz2⟩ := GlobalTheory.T.derivation_family_cotangent_basis R _ (evO G) (GlobalTheory.FormalOrigin.evO_constO R G) hF hFin n
    (fun a => tanDer G (v a)) hadd hmul hc hbasis
  exact ⟨z, hz0, fun a i => by rw [key]; exact hz1 a i, hz2⟩

end GlobalTheory.CoordsOrigin
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.bertiniNumberField_of_hilbertSamuel₂ : Quoted → BertiniNF := by
  first | exact @GlobalTheory.HSShort.bertiniNumberField_of_hilbertSamuel | exact GlobalTheory.HSShort.bertiniNumberField_of_hilbertSamuel | (intros; apply GlobalTheory.HSShort.bertiniNumberField_of_hilbertSamuel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fockJets_unitVacuum_eq_scaled_thetaJets : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ f, IsVacO ψ θ S T sS sT (colLat frS : Set _) (colLat frT : Set _) f → ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank) ∧ Θ ≠ 0 ∧ ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ)) (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 = (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ := by
  first | exact @GlobalTheory.FockPos.fock_jets_eq_theta | exact GlobalTheory.FockPos.fock_jets_eq_theta | (intros; apply GlobalTheory.FockPos.fock_jets_eq_theta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.vacuum_real_restriction_gaussian_mul_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ, θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) ∧ θ ≠ 0 ∧ ∀ w : WO (G.pS (.top t j)) (G.pT (.top t j)), w.map (finPart D) = 0 → f w = Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ)) * θ (δ • (fun τ => (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ)) := by
  first | exact @GlobalTheory.VacRealForm.vacuum_real_form | exact GlobalTheory.VacRealForm.vacuum_real_form | (intros; apply GlobalTheory.VacRealForm.vacuum_real_form <;> assumption)
end

section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.flagSpaceComponent_functionField_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ Z : Comp Xo c, (⊤ : IntermediateField c.F (Om Z)).FG := by
  first | exact @GlobalTheory.DegVal.om_fg | exact GlobalTheory.DegVal.om_fg | (intros; apply GlobalTheory.DegVal.om_fg <;> assumption)
end

section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.cuspFormGrowthOnComponent_nsmul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G : WTZ E), Even G.2 → ∀ a : ℕ, 1 ≤ a → growthOn U Z (a • G) = (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G := by
  first | exact @GlobalTheory.GrowthMul.growthOn_nsmul | exact GlobalTheory.GrowthMul.growthOn_nsmul | (intros; apply GlobalTheory.GrowthMul.growthOn_nsmul <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianLift_reduction_standard_facts : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → AllPrim (dp0 R) (𝟙 _) A' ∧ AllPrim (dp0 R₀) (𝟙 _) A₀ ∧ AllPrim (divided₂ hI) (spMap π) A₀ ∧ Function.Bijective (liftMor (divided₂ hI) h').pull ∧ Module.Finite R (Cr hI π A₀.hom) ∧ Module.Projective R (Cr hI π A₀.hom) ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension g A₀.hom := by
  first | exact @GlobalTheory.LiftSys.abelianLift_facts | exact GlobalTheory.LiftSys.abelianLift_facts | (intros; apply GlobalTheory.LiftSys.abelianLift_facts <;> assumption)
end
