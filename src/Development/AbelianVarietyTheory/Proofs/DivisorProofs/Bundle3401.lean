module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineInvariantFan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle710
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3392
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegOfFieldExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTLieCrys

theorem isLieImage_sum {C : Type} [CommRing C] {A : Over (Sp C)} [GrpObj A] :
    ∀ (n : ℕ) (H : Fin n → HdR A) (u : Fin n → (epsR C ⟶ A)), (∀ i, IsLieImage (H i) (u i)) →
      IsLieImage (∑ i, H i) (List.ofFn u).prod
  | 0, H, u, _ => by
      simpa using (isLieImage_one_iff (A := A)).2 (zero_mem _)
  | n + 1, H, u, hu => by
      rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
      exact (hu 0).add (isLieImage_sum n _ _ fun i => hu i.succ)

theorem comp_listProd {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] {M X Y : 𝒞} [MonObj M]
    (f : X ⟶ Y) : ∀ (n : ℕ) (u : Fin n → (Y ⟶ M)),
      f ≫ (List.ofFn u).prod = (List.ofFn fun i => f ≫ u i).prod
  | 0, u => by simp
  | n + 1, u => by
      rw [List.ofFn_succ, List.prod_cons, MonObj.comp_mul, comp_listProd f n, List.ofFn_succ,
        List.prod_cons]

theorem one_left_eq {C : Type} [CommRing C] (A : Over (Sp C)) [GrpObj A] (x : Sp C ⟶ Sp C) (hx : x = 𝟙 (Sp C)) :
    (1 : Over.mk x ⟶ A).left = η[A].left := by
  have w := Over.w (toUnit (Over.mk x))
  rw [Hom.one_def, Over.comp_left]
  have e1 : (toUnit (Over.mk x)).left = x := by
    simpa using w
  rw [e1, hx]
  exact Category.id_comp _

def overId {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) : Over.mk q ⟶ Over.mk q' :=
  Over.homMk (𝟙 P) ((Category.id_comp q').trans h)

theorem overId_rfl {P S : Scheme.{0}} (q : P ⟶ S) : overId q q rfl = 𝟙 _ :=
  Over.OverMorphism.ext rfl

theorem overId_comp {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) (h' : q = q') :
    overId q' q h' ≫ overId q q' h = 𝟙 _ := by
  subst h
  rw [overId_rfl, Category.id_comp]

theorem overId_comp_left {T P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) {A : Over S}
    (f : Over.mk q' ⟶ A) (a : T ⟶ P) (b : T ⟶ A.left) (e : a ≫ f.left = b) :
    a ≫ (overId q q' h ≫ f).left = b := by
  subst h
  rw [overId_rfl, Category.id_comp]
  exact e

theorem overId_scal {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) {A : Over S}
    (f : Over.mk q' ⟶ A) (g : A ⟶ A) (a : P ⟶ P) (e : Over.mk q ⟶ Over.mk q) (he : e.left = a)
    (hf : (f ≫ g).left = a ≫ f.left) : (overId q q' h ≫ f) ≫ g = e ≫ overId q q' h ≫ f := by
  subst h
  subst he
  rw [overId_rfl, Category.id_comp]
  exact Over.OverMorphism.ext hf

theorem overId_scal_left {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) {A : Over S}
    (f : Over.mk q' ⟶ A) (g : A ⟶ A) (a : P ⟶ P) (e : Over.mk q' ⟶ Over.mk q') (he : e.left = a)
    (hf : f ≫ g = e ≫ f) : ((overId q q' h ≫ f) ≫ g).left = a ≫ (overId q q' h ≫ f).left := by
  subst h
  subst he
  rw [overId_rfl, Category.id_comp, hf]
  rfl

theorem epsPt_hq (C : Type) [CommRing C] :
    spMap (algebraMap C (DualNumber C)) ≫ spMap (RingHom.id C) = spMap (algebraMap C (DualNumber C)) := by
  rw [show spMap (RingHom.id C) = 𝟙 (Sp C) from Spec.map_id _, Category.comp_id]

theorem lieAt_id_of_liftFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ liftFil (divided₂ hsq) h → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) h) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) h) → GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h hA act hact hyp
  obtain ⟨g, hg⟩ := GlobalTheory.SemiAbelianDim.exists_relDim_of_isSemiAbelian C A
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA)
  have ADR := GlobalTheory.T.abelianScheme_firstDeRham_structure
  obtain ⟨LE1, LE2⟩ : LieExact A := (ADR.2.1 C A g hA hg).1
  have bij : Function.Bijective (crysToDR (divided₂ hsq) h) :=
    GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective ADR.2.2.2.1 hA hg (isDPNilpotent_squareZero hsq) hπ rfl h
  have eqv : ∀ (c : D.O) (d : Crys (divided₂ hsq) (spMap π) o₀.A),
      (haveI := o₀.act.hom c; crysToDR (divided₂ hsq) h (push (divided₂ hsq) (spMap π) (o₀.act.act c) d)) =
      (haveI := act.hom c; push (dp0 C) (𝟙 _) (act.act c) (crysToDR (divided₂ hsq) h d)) := by
    intro c d
    haveI := o₀.act.hom c
    haveI := act.hom c
    exact crysToDR_push (divided₂ hsq) h h (o₀.act.act c) (act.act c) (hact c).symm d
  have hq := epsPt_hq C
  have one_left := one_left_eq A (spMap (RingHom.id C)) (Spec.map_id _)
  intro v hv
  obtain ⟨hv1, hv2⟩ := hv
  let v' : epsR C ⟶ A := overId _ _ hq ≫ v
  have tan' : IsTangent v' := overId_comp_left _ _ hq v _ _ (hv1.trans one_left)
  obtain ⟨H0, hH0⟩ := LE2 v' tan'
  obtain ⟨d, rfl⟩ := bij.2 H0
  have scal : v' ≫ act.act (algebraMap (𝓞 D.F) D.O D.ω) = GlobalTheory.GrpTangent.epsScale (tR b.ρ) ≫ v' :=
    overId_scal _ _ hq v _ _ _ (GlobalTheory.GrpTangent.epsScale_left _) hv2
  have hmem : (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω);
      push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) d) - tR b.ρ • d ∈
      liftFil (divided₂ hsq) h := by
    haveI := act.hom (algebraMap (𝓞 D.F) D.O D.ω)
    rw [liftFil, Submodule.mem_comap, map_sub, map_smul, eqv]
    have h1 := hH0.push (act.act (algebraMap (𝓞 D.F) D.O D.ω))
    rw [scal] at h1
    exact h1.sub_mem (hH0.smul (tR b.ρ))
  obtain ⟨w, hw, hsum⟩ := hyp d hmem
  have ex : ∀ j, ∃ u : epsR C ⟶ A, IsLieImage (crysToDR (divided₂ hsq) h (w j)) u :=
    fun j => (LE1 _).exists
  choose u hu using ex
  have hu_scal : ∀ j (c : 𝓞 D.F), u j ≫ act.act (algebraMap (𝓞 D.F) D.O c) =
      GlobalTheory.GrpTangent.epsScale (tR (b.t j c)) ≫ u j := by
    intro j c
    haveI := act.hom (algebraMap (𝓞 D.F) D.O c)
    have m := hw j c
    rw [liftFil, Submodule.mem_comap, map_sub, map_smul, eqv] at m
    have k2 := ((hu j).smul (tR (b.t j c))).add (isLieImage_one_iff.2 m)
    rw [_root_.mul_one, add_sub_cancel] at k2
    exact (LE1 _).unique ((hu j).push _) k2
  have hprod : v' = (List.ofFn u).prod := by

    rw [liftFil, Submodule.mem_comap, map_sub, map_sum] at hsum
    have k2 := (isLieImage_sum _ _ _ hu).add (isLieImage_one_iff.2 hsum)
    rw [_root_.mul_one, add_sub_cancel] at k2
    exact (LE1 _).unique hH0 k2
  refine ⟨fun j => overId _ _ hq.symm ≫ u j, fun j c => ⟨?_, ?_⟩, ?_⟩
  · exact overId_comp_left _ _ hq.symm (u j) _ _ (Eq.trans (hu j).1 one_left.symm)
  · exact overId_scal_left _ _ hq.symm (u j) _ _ _ (GlobalTheory.GrpTangent.epsScale_left _) (hu_scal j c)
  · have e1 : v = overId _ _ hq.symm ≫ v' := by
      show v = overId _ _ hq.symm ≫ (overId _ _ hq ≫ v)
      rw [← Category.assoc, overId_comp, Category.id_comp]
    rw [e1, hprod, comp_listProd]
end GlobalTheory.HTLieCrys
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTCount

theorem crysAct_mem_Fil {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R} (o₀ : GlobalTheory.UPel.HT.Obj b N t)
    (x : D.O) {h : HdR o₀.A} (hh : h ∈ Fil o₀.A) : crysAct o₀ x h ∈ Fil o₀.A := by
  haveI := o₀.act.hom x
  exact push_mem_Fil (o₀.act.act x) hh

theorem crysAct_intCast {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R} (o₀ : GlobalTheory.UPel.HT.Obj b N t)
    (n : ℤ) (h : HdR o₀.A) : crysAct o₀ (algebraMap (𝓞 D.F) D.O (n : 𝓞 D.F)) h = (n : k) • h := by
  rw [map_intCast, map_intCast, Int.cast_smul_eq_zsmul]
  rfl

theorem lieZ_le_Fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (β : R →+* k) (s : Sp k ⟶ Sp R), s = spMap β →
    ∀ o₀ : GlobalTheory.UPel.HT.Obj b N s, GlobalTheory.HTCount.lieZ o₀ β ≤ Fil o₀.A := by
  intro p _ D R _ b N k _ β s hs o₀
  rw [lieZ, Submodule.span_le]
  rintro z ⟨r, lam, c, y, ⟨x, rfl⟩, hlam, rfl⟩
  set T := crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) with hT

  have hω : D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
    rw [← D.nm_eq, ← D.tr_eq]; ring
  have hT2 : T (T x) = (D.tr : k) • T x - (D.nm : k) • x := by
    have := congrArg (fun u => crysAct o₀ (algebraMap (𝓞 D.F) D.O u) x) hω
    simp only [map_mul, map_sub, Module.End.mul_apply, LinearMap.sub_apply] at this
    rw [crysAct_intCast, crysAct_intCast] at this
    exact this

  have hρ : β b.ρ * ((D.tr : k) - β b.ρ) = (D.nm : k) := by
    have := congrArg β b.ρ_root
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    linear_combination -this

  have hy0 : T ((T - ((D.tr : k) - β b.ρ) • 1) x) - β b.ρ • (T - ((D.tr : k) - β b.ρ) • 1) x = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hT2]
    rw [← hρ]
    module
  obtain ⟨w, hw, hyw⟩ := GlobalTheory.HTSummand.lie_mod_fil p D R b N k β s hs o₀ _ (hy0 ▸ zero_mem _)
  set y := (T - ((D.tr : k) - β b.ρ) • 1) x
  set q := (Fil o₀.A).mkQ
  have key : ∀ c' : 𝓞 D.F, q (crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y) = ∑ i, β (b.t i c') • q (w i) := by
    intro c'
    have h1 : crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y - ∑ i, crysAct o₀ (algebraMap (𝓞 D.F) D.O c') (w i) ∈ Fil o₀.A := by
      have := crysAct_mem_Fil o₀ (algebraMap (𝓞 D.F) D.O c') hyw
      rwa [map_sub, map_sum] at this
    have e1 : q (crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y) = q (∑ i, crysAct o₀ (algebraMap (𝓞 D.F) D.O c') (w i)) :=
      (Submodule.Quotient.eq _).2 h1

    rw [e1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_smul]
    exact (Submodule.Quotient.eq _).2 (hw i c')
  rw [SetLike.mem_coe, ← Submodule.Quotient.mk_eq_zero]
  change q _ = 0

  simp only [map_sum, map_smul, key, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hlam, zero_smul, Finset.sum_const_zero]

end GlobalTheory.HTCount
end
end

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

namespace GlobalTheory.HodgeDominates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_sec_detOm (hE : GlobalTheory.Published.SemiAbelianHomExtension) (hS : GlobalTheory.Published.SiegelToroidalIntegral)
    (hF : GlobalTheory.Published.ToroidalChartsForFan) (hr : 1 ≤ Dw.p + Dw.q) (Y : Model Xo c (RingHom.id c.F))
    (hY : (FlagMod.detOm Y).IsLB) (w : Xo.XF c) {A : LB Y.X} (hA : A.IsLB) :
    ∃ m : ℕ, 0 < m ∧ ∃ s : (LB.div (lbPow (FlagMod.detOm Y) m) A).Sec, Y.j w ∈ nonzeroLocus s := by
  obtain ⟨φs, hs, -⟩ := hS (max 1 (Module.finrank ℚ E * min Dw.p Dw.q)) (le_max_left _ _)
  obtain ⟨φ, h₁, h₂, -⟩ := GlobalTheory.PolFan.exists_fine_invariant_fan H hs (le_max_right _ _) ∅ (by simp)
  obtain ⟨Y', BD, d, k, -, hk, hsm, -, hBD, -, hamp⟩ := hF E H Dw hr φ h₁ h₂ l Xo c
  have hY' := GlobalTheory.FanTheta.isLB_detOm_of_smooth Y' hr hsm
  obtain ⟨N, _, _, u, p, p', hu, hu', hp, hpt, e⟩ := exists_common_modification hE Y Y' hY hY'
  have e₁ : p (u w) = Y.j w := by rw [← hu]; rfl
  have e₂ : p' (u w) = Y'.j w := by rw [← hu']; rfl
  rw [← e₁]
  refine exists_sec_of_common p p' hp (u w) (fun W hW => ⟨Y'.j ''ᵁ (Y.j ⁻¹ᵁ W), ⟨w, (show Y.j w ∈ W from e₁ ▸ hW), e₂.symm⟩, ?_⟩) hY hY'
    (hamp hY') BD.isLB_lb e hk ?_ BD.canonical ?_ hA
  · rintro n ⟨w', hw', h⟩
    show p n ∈ W
    rw [hpt n w' h.symm]
    exact hw'
  · have h := cls_tens (isLB_lbPow hY' k) (isLB_dual BD.isLB_lb) (hamp hY').isLB
    rw [cls_lbPow hY', cls_dual BD.isLB_lb] at h
    exact (congrArg (· + _) h).trans (by abel)
  · rw [← SetLike.mem_coe, BD.coe_nonzeroLocus_canonical, e₂]
    refine fun h => hBD _ h ?_
    have h' : Y'.jQ w ∈ pullback.fst Y'.s (spMap (RingHom.id c.F)) ⁻¹' abLocus Y'.t.G := by
      rw [Y'.ab_gen]; exact ⟨w, rfl⟩
    exact h'

theorem exists_lb_dominates (hE : GlobalTheory.Published.SemiAbelianHomExtension) (hS : GlobalTheory.Published.SiegelToroidalIntegral)
    (hF : GlobalTheory.Published.ToroidalChartsForFan) (TF : TorFlag Xo c) :
    ∃ (ω : LB TF.Y.X) (hω : ω.IsLB), cls _ (TF.X.isLB_Llam (FlagMod.mu0 Dw)) = CechPic.pull TF.X.π (cls ω hω) ∧
      ∀ (w : Xo.XF c) (A : LB TF.Y.X), A.IsLB →
        ∃ m : ℕ, 0 < m ∧ ∃ s : (LB.div (lbPow ω m) A).Sec, TF.Y.j w ∈ nonzeroLocus s := by
  have := TF.smooth
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h0 | hr
  · have hd : Dw.dim = 0 := by rw [Datum.dim, show Dw.q = 0 by omega, mul_zero]
    rw [hd] at this
    have : Etale TF.Y.s := (Etale.iff_smoothOfRelativeDimension_zero _).2 this
    have := GlobalTheory.ThetaDescent.isProper_of_isProjOver TF.Y.proj
    have := GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified TF.Y.s
    have := IsFinite.of_isProper_of_locallyQuasiFinite TF.Y.s
    have : IsAffine TF.Y.X := isAffine_of_isAffineHom TF.Y.s
    refine ⟨_, LB.isLB_triv _, ?_, fun w A hA => ⟨1, one_pos, ?_⟩⟩
    · have he : AllWt.exOf Dw (FlagMod.mu0 Dw) 0 = 0 := by
        rw [FlagMod.unitaryWeightExponentVector_signatureWeightMuZero]
        funext ix
        rcases ix with _ | ⟨σ, i⟩
        · rfl
        · have := i.2
          have : Dw.mult σ = 0 := by unfold Datum.mult; split_ifs <;> omega
          omega
      refine Eq.trans (b := 0) ((cls_eq_zero_iff _).2 ⟨⟨fun _ => 1⟩, fun k k' => ?_⟩) (map_zero _).symm
      have hg : (TF.X.Llam (FlagMod.mu0 Dw)).g k k' = 1 :=
        Finset.prod_eq_one fun ix _ => by rw [he]; exact zpow_zero _
      rw [hg, map_one, map_one, mul_one]
    · obtain ⟨s, hs, -⟩ := exists_sec_finite_subset_of_isQuasiAffine (LB.isLB_div (isLB_lbPow (LB.isLB_triv _) 1) hA)
        (Set.finite_singleton (TF.Y.j w)) (U := ⊤) (Set.subset_univ _)
      exact ⟨s, hs rfl⟩
  · have hY := GlobalTheory.FanTheta.isLB_detOm_of_smooth TF.Y hr
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) this)
    refine ⟨_, hY, ?_, fun w A hA => exists_sec_detOm hE hS hF hr TF.Y hY w hA⟩
    rw [← cls_pull hY _ (pull_isLB hY _), ← (cls_eq_iff TF.X.F.isLB_detOm _).2 (TF.X.F.detOm_iso_pull hY)]
    exact ((cls_eq_iff _ _).2 (FlagHodge.lbIso_detOm_Llam TF.X)).symm

end GlobalTheory.HodgeDominates
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTDeform


open GlobalTheory.Published.GrothendieckMessing in
theorem liftFil_isCompl_red_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl (liftFil (divided₂ hsq) m.cart) M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ liftFil (divided₂ hsq) m.cart, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ liftFil (divided₂ hsq) m.cart, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ liftFil (divided₂ hsq) m.cart) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR s s₀ o₀ o m _ _
  have HC := canonical_of_abelianDeRham GlobalTheory.T.abelianScheme_firstDeRham_structure (isDPNilpotent_squareZero hsq) hπ rfl
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C o.A o.ab
  obtain ⟨bij, ⟨M, hM⟩, hAdm⟩ := HC g o₀.A o.A m.φ m.cart o.ab hg
  have bijD := HC.crysToDR_bijective m.cart o.ab hg
  let e := LinearEquiv.ofBijective (crysToDR (divided₂ hsq) m.cart) bijD
  refine ⟨⟨M.comap (crysToDR (divided₂ hsq) m.cart), (Submodule.orderIsoMapComap e).symm.isCompl hM⟩,
    fun y ↦ ?_, fun c d hd ↦ ?_⟩
  · rw [hAdm y]
    constructor
    · rintro ⟨x, hx, ex⟩
      obtain ⟨d, rfl⟩ := bijD.2 x
      exact ⟨d, hx, (corr_crysToDR_iff rfl m.cart bij.2 d y).1 ex⟩
    · rintro ⟨d, hd, ed⟩
      exact ⟨_, hd, (corr_crysToDR_iff rfl m.cart bij.2 d y).2 ed⟩
  · haveI := o₀.act.hom c
    haveI := o.act.hom c
    exact push_mem_liftFil (divided₂ hsq) m.cart m.cart (o₀.act.act c) (o.act.act c) (m.act c).symm hd

end GlobalTheory.HTDeform
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasGoodReduction_of_many_rational_torsion_points : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], GlobalTheory.SS.SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → {m : ℕ | (m : ResidueField R) ≠ 0 ∧ Nat.card {x : 𝟙_ (Over (Sp K)) ⟶ A // x ^ m = 1} = m ^ (2 * g)}.Infinite → HasGoodReduction R K A := by
  first | exact @GlobalTheory.GoodRedTorsion.hasGoodReduction_of_torsion | exact GlobalTheory.GoodRedTorsion.hasGoodReduction_of_torsion | (intros; apply GlobalTheory.GoodRedTorsion.hasGoodReduction_of_torsion <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor GlobalTheory.EndLoc

variable {O : Type} [Ring O]

def ActPB {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    (z' : SiegPre h M ζ s') (act' : O → (z'.A ⟶ z'.A)) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A))
    (f : S' ⟶ S) : Prop :=
  ∃ (φ : z'.A.left ⟶ z.A.left) (φ₂ : (G2 z'.A).left ⟶ (G2 z.A).left),
    IsGrpPullback z'.A z.A f φ ∧ IsSquare φ φ₂ ∧ LBIso z'.P (z.P.pull φ₂) ∧
      (∀ a, (z'.lev a).left ≫ φ = f ≫ (z.lev a).left) ∧ ∀ o, (act' o).left ≫ φ = φ ≫ (act o).left

theorem ActPB.trans {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B}
    {s' : S' ⟶ Sp B} {s'' : S'' ⟶ Sp B} {z : SiegPre h M ζ s} {z' : SiegPre h M ζ s'} {z'' : SiegPre h M ζ s''}
    {act : O → (z.A ⟶ z.A)} {act' : O → (z'.A ⟶ z'.A)} {act'' : O → (z''.A ⟶ z''.A)} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m' : ActPB z'' act'' z' act' f') (m : ActPB z' act' z act f) :
    ActPB z'' act'' z act (f' ≫ f) := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl, ha⟩ := m
  obtain ⟨ψ, ψ₂, hψ, hs', hw', hl', ha'⟩ := m'
  refine ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hψ.comp hφ, GlobalTheory.TChart.AbPol.isSquare_comp hs' hs,
    GlobalTheory.TChart.AbLevel.lbIso_comp z.isLB z'.isLB z''.isLB hw hw', fun a => ?_, fun o => ?_⟩
  · rw [← Category.assoc, hl' a, Category.assoc, hl a, Category.assoc]
  · rw [← Category.assoc, ha' o, Category.assoc, ha o, Category.assoc]

def ZRel {h h' M : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {t : S ⟶ Sp B} (e : O)
    (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) {n : ℕ} (o : Fin n → O)
    (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (c : SiegPre h M ζ t) (z : SiegPre h' M ζ t)
    (act : O → (z.A ⟶ z.A)) : Prop :=
  ∃ (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 c.A ∧ pr ≫ inc = act e ∧
    LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) ∧ (∀ a, c.lev a ≫ inc = z.lev (jl a)) ∧
    ∀ a, z.lev a = (List.ofFn fun k => c.lev (κ k a) ≫ inc ≫ act (o k)).prod

theorem isQProjOver_comp_immersion {R : Type} [CommRing R] {X Y : Scheme.{0}} (j : X ⟶ Y) (s : Y ⟶ Sp R)
    (hj : IsImmersion j) (hq : QuasiCompact j) (hs : IsQProjOver s) : IsQProjOver (j ≫ s) := by
  obtain ⟨N, i, hi, hiq, rfl⟩ := hs
  exact ⟨N, j ≫ i, inferInstance, inferInstance, (Category.assoc _ _ _).symm⟩

end GlobalTheory.UPel.HT
end
end
