module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt)
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.CechPic GlobalTheory.AmpleRigid
open scoped TensorProduct CategoryTheory.Obj
universe u

private theorem diag_fst {S : Scheme.{0}} (A : Over S) :
    (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 A.left := by
  rw [← Over.comp_left, lift_fst]
  rfl

private theorem diag_snd {S : Scheme.{0}} (A : Over S) :
    (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 A.left := by
  rw [← Over.comp_left, lift_snd]
  rfl

section

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N : ℕ} {S S' : Scheme.{0}}
  {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : GObj gb N s} {o' : GObj gb N s'} {f : S' ⟶ S}

private theorem tensor_left_hom_ext_of_fst_snd {S : Scheme.{0}} {X Y : Over S} {W : Scheme.{0}} {u v : W ⟶ (X ⊗ Y).left}
    (h₁ : u ≫ (fst X Y).left = v ≫ (fst X Y).left) (h₂ : u ≫ (snd X Y).left = v ≫ (snd X Y).left) : u = v := by
  have hw : u ≫ (X ⊗ Y).hom = v ≫ (X ⊗ Y).hom := by
    rw [← Over.w (fst X Y), ← Category.assoc, h₁, Category.assoc]
  let U : Over.mk (u ≫ (X ⊗ Y).hom) ⟶ X ⊗ Y := Over.homMk u
  let V : Over.mk (u ≫ (X ⊗ Y).hom) ⟶ X ⊗ Y := Over.homMk v hw.symm
  have hUV : U = V := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.OverMorphism.ext (by simpa [U, V] using h₁)
    · exact Over.OverMorphism.ext (by simpa [U, V] using h₂)
  exact congrArg CommaMorphism.left hUV

private theorem map_diag (m : GObjMap o' o f) :
    (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ m.φ₂ = m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
  apply tensor_left_hom_ext_of_fst_snd
  · have key : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (fst o'.A o'.A).left ≫ m.φ = m.φ := by
      rw [← Category.assoc, diag_fst, Category.id_comp]
    rw [Category.assoc, m.sq.1, key, Category.assoc, diag_fst, Category.comp_id]
  · have key : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (snd o'.A o'.A).left ≫ m.φ = m.φ := by
      rw [← Category.assoc, diag_snd, Category.id_comp]
    rw [Category.assoc, m.sq.2, key, Category.assoc, diag_snd, Category.comp_id]

private theorem pull_diag_cls (m : GObjMap o' o f) :
    pull m.φ (cls (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (pull_isLB o.isLB _)) =
      cls (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (pull_isLB o'.isLB _) := by
  rw [cls_pull o.isLB, cls_pull o'.isLB, ← pull_comp, ← map_diag m, pull_comp,
    ← cls_pull o.isLB _ (pull_isLB o.isLB m.φ₂),
    (cls_eq_iff (pull_isLB o.isLB m.φ₂) o'.isLB).2 (LBIso.symm m.pol)]

private theorem eq_at_point (hN : 3 ≤ N) (m m' : GObjMap o' o f) {K : Type} [Field K] [IsAlgClosed K] (j : Sp K ⟶ S') :
    pullback.fst o'.A.hom j ≫ m.φ = pullback.fst o'.A.hom j ≫ m'.φ := by
  have hA' : IsAbelianScheme ((Over.pullback j).obj o'.A) := by
    haveI := o'.ab.comm
    haveI := o'.ab.smooth
    haveI := o'.ab.proper
    haveI := o'.ab.geomConnected
    constructor
    · infer_instance
    · dsimp; infer_instance
    · dsimp; infer_instance
    · dsimp; infer_instance
  have c := (isGrpPullback_pullback o'.A j).comp m.cart
  have c' := (isGrpPullback_pullback o'.A j).comp m'.cart
  refine GlobalTheory.SiegRigid.eq_of_field (pull_isLB o.isLB _) o.ample hA' c c' ?_ hN ?_ ?_
  · rw [pull_comp, pull_comp, pull_diag_cls m, pull_diag_cls m']
  · intro h0
    let ψ : ℚ →+* K := (Spec.preimage (R := CommRingCat.of R) (S := CommRingCat.of K) (j ≫ s')).hom.comp
      (algebraMap ℚ R)
    have e0 : ψ (N : ℚ) = ψ 0 := by rw [map_natCast, map_zero]; exact h0
    have e1 : (N : ℚ) = 0 := ψ.injective e0
    norm_cast at e1
    omega
  · intro Ω _ _ t x hx
    let β : R →+* Ω := (Spec.preimage (R := CommRingCat.of R) (S := CommRingCat.of Ω) ((t ≫ j) ≫ s')).hom
    have hβ : (t ≫ j) ≫ s' = spMap β := by
      simp only [spMap, β, CommRingCat.ofHom_hom, Spec.map_preimage]
    obtain ⟨I, hI⟩ := o'.geom Ω (t ≫ j) β hβ
    let x₁ := pushHom (isGrpPullback_pullback o'.A j) (Over.mk t) x
    have hx₁ : x₁ ^ N = 1 := by
      simp only [x₁]
      rw [← map_pow, hx, map_one]
    obtain ⟨y, hy⟩ := (I.onto N (by omega) x₁).1 hx₁
    have hl : x.left ≫ pullback.fst o'.A.hom j = x₁.left := rfl
    have key : ∀ mm : GObjMap o' o f, x.left ≫ pullback.fst o'.A.hom j ≫ mm.φ =
        (toUnit (Over.mk (t ≫ j))).left ≫ f ≫ (o.eta y).left := by
      intro mm
      rw [← Category.assoc, hl, ← hy, ← hI y, Over.comp_left, Category.assoc, mm.eta y]
    rw [key m, key m']

end

theorem UpperTheory.Gal.G3.pRigid :
    Rigid := by
  intro p _ D R _ _ gb S S' s s' f hf N o o' m m'
  have hN : 3 ≤ (N : ℕ) := N.2.1
  obtain ⟨σ, hσmon, hσ⟩ := GlobalTheory.SiegRigid.exists_aut m.cart m'.cart
  have hid : σ.hom = 𝟙 o'.A := by
    refine GlobalTheory.eq_id_of_forall_geometric_fibre GlobalTheory.laws_without_cohomology.1 o'.A o'.ab σ.hom
      (IsMonHom.one_hom σ.hom) ?_
    intro t
    let K := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫
      S'.fromSpecResidueField t
    refine ⟨Sp K, pullback o'.A.hom j, j, pullback.fst o'.A.hom j, pullback.snd o'.A.hom j,
      IsLocalRing.closedPoint K, ?_, IsPullback.of_hasPullback _ _, ?_⟩
    · exact Scheme.fromSpecResidueField_apply t _
    · apply m'.cart.1.hom_ext
      · rw [Category.assoc, hσ, eq_at_point hN m m' j]
      · rw [Category.assoc, Over.w]
  rw [← hσ, hid, Over.id_left, Category.id_comp]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pKSNice :
    KNBasic → PowSm → TwFEt → SigmaFEt → KSNice := by
  intro hKN hP hT hS p _ D G L hsc R _ _ gb k T N J g
  have hq := T.e_q N
  obtain ⟨hsm, -, hpr⟩ := hP p D R gb N (T.M N) k
  refine ⟨?_, ?_, ?_⟩
  · show Smooth (T.X.q (T.lev N))
    rw [← hq]
    infer_instance
  · show IsProjOver (T.X.q (T.lev N))
    rw [← hq]
    exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion _ (hpr hsc.cpt)
  · intro j
    dsimp only [UpperTheory.Gal.Int.Geo.KS.tower]
    have hne : ((L.KN ↑N).subgroupOf (g j).K).index ≠ 0 := by
      have h0 := (hKN p D G L 1).2.2 N (by norm_num) (by have := N.2.1; omega)
      rw [← Subgroup.relIndex_mul_relIndex _ _ _ (g j).le (g j).le_one] at h0
      exact left_ne_zero_of_mul h0
    haveI : ((L.KN ↑N).subgroupOf (g j).K).FiniteIndex := ⟨hne⟩
    refine ⟨_, hS _ _ _ (hT T.X _ _ ⟨?_, ?_⟩)⟩
    · exact one_mem _
    · intro u hu
      rw [T.K_eq] at hu ⊢
      simpa using UpperTheory.Gal.Int.Geo.KN_anti (g j).dvd hu
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem exists_sigma_point {W : Scheme.{0}} {I : Type} (K : Type) [Field K]
    (y : Spec (CommRingCat.of K) ⟶ ∐ fun _ : I => W) :
    ∃ (i : I) (y' : Spec (CommRingCat.of K) ⟶ W), y' ≫ Sigma.ι (fun _ : I => W) i = y := by
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨⟨i, w⟩, hw⟩ := (sigmaMk (fun _ : I => W)).surjective (y pt)
  rw [sigmaMk_mk] at hw
  refine ⟨i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => W) i) y ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨q, rfl⟩
  rw [Subsingleton.elim q pt]
  exact ⟨w, hw⟩

private theorem card_sigma_fibre {Y Z : Scheme.{0}} (s : Y ⟶ Z) (I : Type) (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ Z) :
    Nat.card {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y) // y ≫ (Sigma.desc fun _ : I => s) = x} =
      Nat.card I * Nat.card {y' : Spec (CommRingCat.of K) ⟶ Y // y' ≫ s = x} := by
  let F : I × {y' : Spec (CommRingCat.of K) ⟶ Y // y' ≫ s = x} →
      {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y) // y ≫ (Sigma.desc fun _ : I => s) = x} :=
    fun q => ⟨q.2.1 ≫ Sigma.ι (fun _ : I => Y) q.1, by
      rw [Category.assoc, Sigma.ι_desc]
      exact q.2.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, a, ha⟩ ⟨j, b, hb⟩ h
      have h' : a ≫ Sigma.ι (fun _ : I => Y) i = b ≫ Sigma.ι (fun _ : I => Y) j :=
        congrArg Subtype.val h
      by_cases hij : i = j
      · subst hij
        have hab : a = b := (cancel_mono _).mp h'
        subst hab
        rfl
      · exfalso
        have hE := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : I => Y) ⟨h'⟩ hij
        obtain ⟨p⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K)))
        exact hE.false p
    · rintro ⟨y, hy⟩
      obtain ⟨i, y', rfl⟩ := exists_sigma_point K y
      refine ⟨⟨i, y', ?_⟩, rfl⟩
      rw [Category.assoc, Sigma.ι_desc] at hy
      exact hy
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod]

theorem UpperTheory.Gal.G3.pSigmaFEt :
    SigmaFEt := by
  intro Y Z s d I _ hs
  obtain ⟨hfin, het, hcard⟩ := hs
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hid : IsFinite (Sigma.desc fun _ : I => 𝟙 Y) := by
    have h1 := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y n
    have h2 : IsFinite ((Sigma.reindex e (fun _ : Fin n => Y)).hom ≫
        Sigma.desc fun _ : Fin n => 𝟙 Y) := inferInstance
    have h3 : (Sigma.desc fun _ : I => 𝟙 Y) =
        (Sigma.reindex e (fun _ : Fin n => Y)).hom ≫ Sigma.desc fun _ : Fin n => 𝟙 Y := by
      refine Sigma.hom_ext (f := fun _ : I => Y) _ _ fun i => ?_
      rw [Sigma.ι_desc, ← Category.assoc]
      erw [Sigma.ι_reindex_hom (f := fun _ : Fin n => Y) e i]
      rw [Sigma.ι_desc]
    rw [h3]
    exact h2
  have hfac : (Sigma.desc fun _ : I => s) = (Sigma.desc fun _ : I => 𝟙 Y) ≫ s := by
    refine Sigma.hom_ext (f := fun _ : I => Y) _ _ fun i => ?_
    simp
  have hloc : IsZariskiLocalAtSource @Etale.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine ⟨?_, ?_, ?_⟩
  · rw [hfac]
    infer_instance
  · exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{0}) fun _ => het
  · intro K _ _ x
    rw [card_sigma_fibre, hcard]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

open GlobalTheory.CechPic GlobalTheory.BirigUniq in
theorem UpperTheory.Gal.G3.pPolDesc :
    PolDesc := by
  intro G₀ R _ _ gb S S' s s' c _ _ _ N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ ψ' hψ hcomm e h'
  obtain ⟨h'⟩ := h'
  haveI := hψ
  have hpb : IsPullback m₁.φ o₁'.A.hom o₁.A.hom c := m₁.cart.1
  let Y' : Over S := Over.mk (m₁.φ ≫ o₁.A.hom)
  let cO : Y' ⟶ o₁.A := Over.homMk m₁.φ rfl
  have hP1 : (Hecke.lbPow o₁.P e).IsLB := by
    unfold Hecke.lbPow
    exact LB.isLB_linComb o₁.isLB _ _
  have hP1' : (Hecke.lbPow o₁'.P e).IsLB := by
    unfold Hecke.lbPow
    exact LB.isLB_linComb o₁'.isLB _ _
  have hQ : (o₂.P.pull (Hecke.sq2 ψ)).IsLB := pull_isLB o₂.isLB _
  have hQ' : (o₂'.P.pull (Hecke.sq2 ψ')).IsLB := pull_isLB o₂'.isLB _
  refine ⟨(cls_eq_iff hP1 hQ).1 ?_⟩
  rw [← sub_eq_zero]
  have hfl : Flat m₁.φ := MorphismProperty.of_isPullback (P := @Flat) hpb.flip (inferInstance : Flat c)
  have hsu : Surjective m₁.φ :=
    MorphismProperty.of_isPullback (P := @Surjective) hpb.flip (inferInstance : Surjective c)
  have hqc : QuasiCompact m₁.φ :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hpb.flip (inferInstance : QuasiCompact c)
  refine pic_eq_zero_of_fpqc o₁.A o₁.A Y' o₁.ab cO hfl hsu hqc _ ?_ ?_
  · have key : (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left ≫ Hecke.sq2 ψ =
        ψ.left ≫ (lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A)).left := by
      unfold Hecke.sq2
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext
      · simp [one_comp_monHom]
      · simp
    rw [map_sub, GlobalTheory.BirigidPow.cls_lbPow o₁.isLB e hP1, map_nsmul,
      ← cls_pull o₁.isLB _ (pull_isLB o₁.isLB _), (cls_eq_zero_iff _).2 o₁.rig₁, smul_zero,
      cls_pull o₂.isLB _ hQ, ← pull_comp, key, pull_comp,
      ← cls_pull o₂.isLB _ (pull_isLB o₂.isLB _), (cls_eq_zero_iff _).2 o₂.rig₁, map_zero, sub_zero]
  · have hw : (fst o₁.A Y').left ≫ o₁.A.hom = ((snd o₁.A Y').left ≫ o₁'.A.hom) ≫ c := by
      have h1 := Over.w (fst o₁.A Y')
      have h2 := Over.w (snd o₁.A Y')
      rw [h1, ← h2, Category.assoc, ← hpb.w]
      rfl
    let u₀ : (o₁.A ⊗ Y').left ⟶ o₁'.A.left := hpb.lift (fst o₁.A Y').left ((snd o₁.A Y').left ≫ o₁'.A.hom) hw
    have hu₀ : u₀ ≫ o₁'.A.hom = (snd o₁.A Y').left ≫ o₁'.A.hom := hpb.lift_snd _ _ _
    let g : (o₁.A ⊗ Y').left ⟶ Limits.pullback o₁'.A.hom o₁'.A.hom :=
      Limits.pullback.lift u₀ (snd o₁.A Y').left hu₀
    have K1 : (lift (fst o₁.A Y') (snd o₁.A Y' ≫ cO)).left = g ≫ m₁.φ₂ := by
      apply Limits.pullback.hom_ext (f := o₁.A.hom) (g := o₁.A.hom)
      · change _ ≫ (fst o₁.A o₁.A).left = (g ≫ m₁.φ₂) ≫ (fst o₁.A o₁.A).left
        rw [← Over.comp_left, lift_fst, Category.assoc, m₁.sq.1, ← Category.assoc]
        change _ = (g ≫ Limits.pullback.fst _ _) ≫ m₁.φ
        rw [Limits.pullback.lift_fst]
        exact (hpb.lift_fst _ _ _).symm
      · change _ ≫ (snd o₁.A o₁.A).left = (g ≫ m₁.φ₂) ≫ (snd o₁.A o₁.A).left
        rw [← Over.comp_left, lift_snd, Category.assoc, m₁.sq.2, ← Category.assoc]
        change _ = (g ≫ Limits.pullback.snd _ _) ≫ m₁.φ
        rw [Limits.pullback.lift_snd, Over.comp_left]
        rfl
    have K2 : m₁.φ₂ ≫ Hecke.sq2 ψ = Hecke.sq2 ψ' ≫ m₂.φ₂ := by
      unfold Hecke.sq2
      apply Limits.pullback.hom_ext (f := o₂.A.hom) (g := o₂.A.hom)
      · change (_ ≫ _) ≫ (fst o₂.A o₂.A).left = (_ ≫ _) ≫ (fst o₂.A o₂.A).left
        rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_fst, m₂.sq.1, Over.comp_left,
          ← Category.assoc, m₁.sq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left,
          Category.assoc, Category.assoc, hcomm]
      · change (_ ≫ _) ≫ (snd o₂.A o₂.A).left = (_ ≫ _) ≫ (snd o₂.A o₂.A).left
        rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_snd, m₂.sq.2, Over.comp_left,
          ← Category.assoc, m₁.sq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left,
          Category.assoc, Category.assoc, hcomm]
    have pol1 : cls o₁'.P o₁'.isLB = cls (o₁.P.pull m₁.φ₂) (pull_isLB o₁.isLB _) :=
      (cls_eq_iff _ _).2 m₁.pol
    have pol2 : cls o₂'.P o₂'.isLB = cls (o₂.P.pull m₂.φ₂) (pull_isLB o₂.isLB _) :=
      (cls_eq_iff _ _).2 m₂.pol
    have E1 : (pull (lift (fst o₁.A Y') (snd o₁.A Y' ≫ cO)).left) (cls _ hP1) =
        (pull g) (cls _ hP1') := by
      rw [K1, pull_comp, GlobalTheory.BirigidPow.cls_lbPow o₁.isLB e hP1, map_nsmul,
        ← cls_pull o₁.isLB _ (pull_isLB o₁.isLB _), ← pol1, ← GlobalTheory.BirigidPow.cls_lbPow o₁'.isLB e hP1']
    have E2 : (pull (lift (fst o₁.A Y') (snd o₁.A Y' ≫ cO)).left) (cls _ hQ) =
        (pull g) (cls _ hQ') := by
      rw [K1, cls_pull o₂.isLB _ hQ, ← pull_comp, Category.assoc, K2, ← Category.assoc, pull_comp,
        pull_comp, ← cls_pull o₂.isLB _ (pull_isLB o₂.isLB _), ← pol2, cls_pull o₂'.isLB _ hQ']
    rw [map_sub, E1, E2, (cls_eq_iff hP1' hQ').2 h', sub_self]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem isUnit_nat_of_rat {R : Type} [CommRing R] [Algebra ℚ R] {S : Scheme.{0}} (s : S ⟶ Sp R) {d : ℕ}
    (hd : 0 < d) : IsUnit (d : Γ(S, ⊤)) := by
  have hR : IsUnit (d : R) := by
    have hq : IsUnit (algebraMap ℚ R (d : ℚ)) :=
      (isUnit_iff_ne_zero.mpr (by exact_mod_cast hd.ne')).map _
    simpa using hq
  have h := hR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
  simpa using h

theorem UpperTheory.Gal.G3.pIsogFEt :
    IsogFEt := by
  intro R _ _ S s A A' _ _ _ _ hA hA' ψ ψ' d hd hψ hψ' h1 h2
  exact GlobalTheory.UPel.HT.ES.isFinite_etale_surjective_of_isQuasiInv S A A' d ψ ψ' hA hA'
    (isUnit_nat_of_rat s hd) ⟨hψ, hψ', h1, h2⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem nsmul_cancel' {V : Type} [AddCommGroup V] [Module ℚ V] {c : ℕ} (hc : c ≠ 0) {a b : V}
    (h : c • a = c • b) : a = b := by
  have h' : (c : ℚ) • a = (c : ℚ) • b := by
    rw [Nat.cast_smul_eq_nsmul ℚ, Nat.cast_smul_eq_nsmul ℚ]
    exact h
  exact smul_right_injective V (Nat.cast_ne_zero.mpr hc) h'

private theorem rel_core {p : ℕ} [Fact p.Prime] {D : Datum p} (F : D.La →+ AfP p ⊗[ℚ] VQ D)
    (hFmem : ∀ z, F z ∈ LaHat D) {Q Q' : Type} [Group Q] [Group Q'] (Φ : Q →* Q')
    (eI : ℕ → D.La → Q) (eJ : ℕ → D.La → Q')
    (addI : ∀ n a b, eI n (a + b) = eI n a * eI n b) (addJ : ∀ n a b, eJ n (a + b) = eJ n a * eJ n b)
    (kerI : ∀ n, 0 < n → ∀ x, eI n x = 1 ↔ ∃ y, x = n • y)
    (kerJ : ∀ n, 0 < n → ∀ x, eJ n x = 1 ↔ ∃ y, x = n • y)
    (towerI : ∀ n m, 0 < n → 0 < m → ∀ x, eI (n * m) x ^ m = eI n x)
    (f : ℕ → D.La →+ D.La) (k : ℕ) (hk0 : 0 < k) (hk : k.Coprime p)
    (honto : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, f n y = k • x + n • z)
    (hrel : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, F (f n x) = k • inAf D x + n • w)
    (hev : ∀ n, 0 < n → n.Coprime p → ∀ x, eJ n x = Φ (eI (n * k) (f (n * k) x)))
    (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (x y : D.La) :
    Φ (eI n x) = eJ n y ↔ ∃ v ∈ LaHat D, F x = inAf D y + n • v := by
  have hpowI : ∀ N, 0 < N → ∀ (m : ℕ) a, eI N (m • a) = eI N a ^ m := by
    intro N hN m a
    induction m with
    | zero =>
      rw [zero_nsmul, pow_zero]
      exact (kerI N hN 0).mpr ⟨0, by simp⟩
    | succ m ih => rw [succ_nsmul, addI, ih, pow_succ]
  have hinAf : ∀ a : D.La, inAf D (n • a) = n • inAf D a := fun a =>
    map_nsmul (GlobalTheory.HeckeApprox.inAfH D) n a
  have hNpos : 0 < n * k := Nat.mul_pos hn hk0
  have hNp : (n * k).Coprime p := Nat.Coprime.mul_left hnp hk
  obtain ⟨y', z, hy'⟩ := honto (n * k) hNpos hNp x
  have hL : Φ (eI n x) = eJ n y' := by
    rw [← towerI n k hn hk0 x, hev n hn hnp y', hy', addI, (kerI (n * k) hNpos ((n * k) • z)).mpr ⟨z, rfl⟩,
      _root_.mul_one, hpowI (n * k) hNpos]
  obtain ⟨v0, hv0, hv0eq⟩ : ∃ v0 ∈ LaHat D, F x = inAf D y' + n • v0 := by
    obtain ⟨w, hw, hFw⟩ := hrel (n * k) hNpos hNp y'
    rw [hy', map_add (f := _), map_nsmul, map_nsmul] at hFw
    refine ⟨w - F z, (LaHat D).sub_mem hw (hFmem z), ?_⟩
    apply nsmul_cancel' (c := k) (Nat.pos_iff_ne_zero.mp hk0)
    have e : k • F x = k • inAf D y' + (n * k) • w - (n * k) • F z := by
      rw [← hFw]
      abel
    rw [e, smul_add, smul_smul, mul_comm k n, smul_sub, add_sub_assoc]
  have hdiff : eJ n y' = eJ n y ↔ eJ n (y' - y) = 1 := by
    have hsplit : eJ n y' = eJ n (y' - y) * eJ n y := by rw [← addJ, sub_add_cancel]
    constructor
    · intro h
      rw [hsplit] at h
      exact mul_right_cancel (h.trans (_root_.one_mul _).symm)
    · intro h
      rw [hsplit, h, _root_.one_mul]
  rw [hL, hdiff, kerJ n hn (y' - y)]
  constructor
  · rintro ⟨z', hz'⟩
    refine ⟨v0 + inAf D z', (LaHat D).add_mem hv0 (GlobalTheory.HeckeApprox.inAf_mem D z'), ?_⟩
    have h1 : inAf D y' - inAf D y = n • inAf D z' := by
      rw [← GlobalTheory.HeckeApprox.inAf_sub, hz', hinAf]
    rw [hv0eq, smul_add, ← h1]
    abel
  · rintro ⟨v, hv, hFv⟩
    apply GlobalTheory.LKGeo.LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (y' - y) n hn hnp (v - v0) ((LaHat D).sub_mem hv hv0)
    have h2 := hv0eq.symm.trans hFv
    rw [GlobalTheory.HeckeApprox.inAf_sub, smul_sub, sub_eq_sub_iff_add_eq_add, h2, add_comm]

theorem UpperTheory.Gal.G3.pRelArith :
    RelArith := by
  unfold UpperTheory.Gal.G3.RelArith UpperTheory.Gal.G3.Rel
  intro p _ D G L R _ _ gb S s N N' o' o K _ t I J ψ h f u c k hψ hint hsys hrel hev n hn hnp x y
  haveI := hψ
  have hk : k.Coprime p := hsys.2.1
  have hk0 : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hk0
    rw [hk0, Nat.coprime_zero_left] at hk
    exact (Fact.out : p.Prime).one_lt.ne' hk
  let Φ : (Over.mk t ⟶ o'.A) →* (Over.mk t ⟶ o.A) :=
    MonoidHom.mk' (fun g => g ≫ ψ) (fun a b => MonObj.mul_comp a b ψ)
  exact rel_core ((L.actG h).toAddMonoidHom.comp (GlobalTheory.HeckeApprox.inAfH D))
    (fun z => hint _ (GlobalTheory.HeckeApprox.inAf_mem D z)) Φ I.ev J.ev I.add J.add I.ker J.ker I.tower f k hk0 hk
    hsys.2.2.2.2.2.2 hrel hev n hn hnp x y
end
