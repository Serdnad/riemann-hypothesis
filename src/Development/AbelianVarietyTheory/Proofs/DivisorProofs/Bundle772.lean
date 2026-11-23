module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle737
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsClopenLocusOfAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle738
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseAdelicThetaTransformRapidDecay
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KummerSplit

theorem exists_comp_eq_of_injective {R : Type} [CommRing R] {A B K : Shv R} [Injective K] (g : A ⟶ B) (φ : A ⟶ K)
    (h : ∀ U (a : Sec A U), Sec.map g a = 0 → Sec.map φ a = 0) : ∃ ψ : B ⟶ K, g ≫ ψ = φ := by
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hS : S.Exact := S.exact_of_f_is_kernel (kernelIsKernel g)
  have hf : S.f ≫ φ = 0 := by
    refine (GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R (S.f ≫ φ)).2.2.2 0 fun U a => ?_
    have h0 : Sec.map g (Sec.map (kernel.ι g) a) = 0 := by
      rw [← sec_map_comp, kernel.condition]; rfl
    change Sec.map φ (Sec.map (kernel.ι g) a) = Sec.map (0 : kernel g ⟶ K) a
    rw [h U _ h0]; rfl
  exact ⟨hS.descToInjective φ hf, hS.comp_descToInjective φ hf⟩

theorem kernel_local (q : ℕ) [NeZero q] (V : Scheme.{0}) (c : (tripP q).obj (op V) →₀ ULift.{1} (ZMod q))
    (h : (c.sum fun x r => r • (freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).tgt) -
      freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).src))) = 0) :
    (c.sum fun x r => r • resGen 1 (tripP.get x).root) = 0 := GlobalTheory.T.kummerRelation_boundary_kernel_generator_sum_zero q V c h

theorem exists_isKum (q : ℕ) [NeZero q] : ∃ t, IsKum q t := by
  have hinj : Injective ((res (ZMod q) (tw q 1)).X 0) := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q 1)).2.1 0
  have hu := free_hom_sections (ZMod q) unitsP ((free (ZMod q)).obj unitsP)
  obtain ⟨G, hG⟩ := (free_hom_sections (ZMod q) (tripP q) ((free (ZMod q)).obj unitsP)).1
    (fun U x => freeGen (ZMod q) unitsP U (unitsP.mk (tripP.get x).tgt) -
      freeGen (ZMod q) unitsP U (unitsP.mk (tripP.get x).src))
    (fun V U g x => by
      rw [res_sub, hu.2.2.1, hu.2.2.1]
      rfl)
  obtain ⟨Φ, hΦ⟩ := (free_hom_sections (ZMod q) (tripP q) ((res (ZMod q) (tw q 1)).X 0)).1
    (fun U x => resGen 1 (tripP.get x).root)
    (fun V U g x => by
      unfold resGen
      rw [sec_res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1]
      rfl)
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_injective G Φ (fun U a ha => by
    apply sec_eq_zero_of_loc
    refine loc_calculus.2.1 U _ _ ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination (ZMod q) (tripP q) U).1 a) ?_
    rintro V g ⟨c, hc⟩
    have hc' := congrArg (Sec.map G) hc
    rw [← sec_res_map, ha, res_zero', smap_sum] at hc'
    rw [sec_res_map, hc, smap_sum]
    simp only [hG] at hc'
    simp only [hΦ]
    exact kernel_local q V c hc'.symm)
  refine ⟨fun U v => Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk v)), ?_, ?_⟩
  · intro V U g v _
    rw [sec_res_map, hu.2.2.1]
    rfl
  · intro U ζ v w hw
    have e := congrArg (Sec.map ψ) (hG U (tripP.mk ⟨ζ, v, w, hw⟩))
    rw [← sec_map_comp, hψ, hΦ, smap_sub] at e
    change resGen 1 ζ = Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk w)) -
      Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk v)) at e
    show Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk w)) =
      Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk v)) + resGen 1 ζ
    rw [e]
    exact (add_sub_cancel _ _).symm

theorem isKum_kumT : ∀ (q : ℕ) [NeZero q], IsKum q (kumT q) := fun q _ => pick_spec (exists_isKum q)

end GlobalTheory.EtC.KummerSplit
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

theorem _root_.GlobalTheory.T.twisted_cocycle_classes_pullback_cup : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (n i : ℤ) (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (hz : ∀ j : Fin N, CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) (z j) (zero_add _)) = pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ))) (a : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) (b : Cocycle (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n) (hb : b.1 = phi q V ℓ i (fun j => (z j).1) n (fun j => (a j).1)), pull _ (twIso E V).hom _ n (pbfMap q V n i (fun j => CohomologyClass.mk (a j))) = cpull (awChains (ZMod q) (twX E V)) (res _ (tw q i)) n (CohomologyClass.mk b) := by
  first | (exact @GlobalTheory.PBFc.pbfMap_eq_cpull_aw) | (exact GlobalTheory.PBFc.pbfMap_eq_cpull_aw) | (intros; apply GlobalTheory.PBFc.pbfMap_eq_cpull_aw  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixMat

theorem isTest_pullback : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (T T' : Scheme.{0}) (t : T ⟶ Sp Rg) (h : T' ⟶ T) (A₁ B₁ : Over T) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → ∃ (A₂ : Over T') (_ : GrpObj A₂) (B₂ : Over T') (_ : GrpObj B₂) (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂), IsTest A B L M (h ≫ t) A₂ B₂ φA₂ φB₂ Φ₂ ∧ IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ h := by
  intro Rg _ A B _ _ L M T T' t h A₁ B₁ _ _ φA₁ φB₁ Φ₁ hT
  obtain ⟨hA, hB, hm, hl⟩ := hT
  haveI : IsMonHom Φ₁ := hm
  have eΦ : ((Over.pullback h).map Φ₁).left ≫ pullback.fst B₁.hom h = pullback.fst A₁.hom h ≫ Φ₁.left :=
    pullback.lift_fst _ _ _
  have gA := isGrpPullback_pullback A₁ h
  have gB := isGrpPullback_pullback B₁ h
  refine ⟨(Over.pullback h).obj A₁, inferInstance, (Over.pullback h).obj B₁, inferInstance,
    pullback.fst A₁.hom h ≫ φA₁, pullback.fst B₁.hom h ≫ φB₁, (Over.pullback h).map Φ₁,
    ⟨gA.comp hA, gB.comp hB, PullGtPf.isMonHom_of_grpPullback gA gB Φ₁ _ eΦ, ?_⟩,
    pullback.fst A₁.hom h, pullback.fst B₁.hom h, gA, gB, rfl, rfl, eΦ⟩
  exact LBIso.chartPull
    (chartPullSame L (fun _ => pullback.fst A₁.hom h ≫ φA₁) (fun _ => φA₁) (fun _ => 1) (pullback.fst A₁.hom h)
      (fun _ => rfl))
    (HomFixGlue.chartPullPullPull M _ _ _ _ (pullback.fst A₁.hom h)
      (by rw [← Category.assoc, eΦ, Category.assoc])) hl

end GlobalTheory.HomFixMat
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

theorem _root_.GlobalTheory.T.exists_split_place_uniformiser_idele : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)) (x : OF E), Splits v → (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) → ∃ π : (Af E)ˣ, (∀ P, Over P v → (π : Af E) P = iota x P) ∧ (∀ P, ¬ Over P v → (π : Af E) P = 1) ∧ modF π = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ 2 ∧ ∀ χ : HChar E, TrivOnF χ → finPart χ π = 1 := by
  first | exact @GlobalTheory.CMVal.Euler.exists_split_unif_idele | exact GlobalTheory.CMVal.Euler.exists_split_unif_idele | (intros; apply GlobalTheory.CMVal.Euler.exists_split_unif_idele <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

theorem _root_.GlobalTheory.T.exists_uniformiser_split_place_cm_order_nonunit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → ∃ x : OF E, (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) ∧ ∀ (n : ℕ) (π y : (Af E)ˣ), (∀ P, Over P v → (π : Af E) P = iota x P) → (LocIn n v ((π⁻¹ * y : (Af E)ˣ) : Af E) ↔ LocIn (n + 1) v (y : Af E) ∧ ¬ ∀ P, Over P v → Valued.v ((y : Af E) P) = 1) := by
  first | exact @GlobalTheory.CMVal.Euler.locIn_succ_nonunit_iff | exact GlobalTheory.CMVal.Euler.locIn_succ_nonunit_iff | (intros; apply GlobalTheory.CMVal.Euler.locIn_succ_nonunit_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

theorem _root_.GlobalTheory.T.finrank_jointEigenspace_add_conj_eq_mul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (D' : PLat D.O D.inv) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : D'.La →+ (Fin D.g → ℂ)), IsPeriod D' ρ Q → ∀ τ : D.F →+* ℂ, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ) + Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) ((starRingEnd ℂ).comp τ)) = D.m * D.n := by
  first | exact @GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq | exact GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq | (intros; apply GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.TrStab

theorem one_left' {S : Scheme.{0}} (G : Over S) [GrpObj G] (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.toUnit_left']

theorem eq_one_of_push {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {θ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f θ) {T : Over S'} (x : T ⟶ G')
    (hx : x.left ≫ θ = T.hom ≫ f ≫ η[G].left) : x = 1 := by
  ext
  apply h.1.hom_ext
  · rw [hx, one_left', Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h]
  · rw [Over.w x, Over.w (1 : T ⟶ G')]

theorem push_one {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {θ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f θ) (T : Over S') :
    (1 : T ⟶ G').left ≫ θ = T.hom ≫ f ≫ η[G].left := by
  rw [one_left', Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h]

end GlobalTheory.UPel.HT.ES.TrStab

namespace GlobalTheory.UPel.HT.ES

open TrStab

theorem kerStableAt_iff_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (KerStableAt o ψ t ↔ KerStableAt o₁ ψ₁ (𝟙 T)) := by
  intro p _ D R _ b N T Y s₁ s t o₁ o m B₁ _ _ B _ _ θ ψ₁ ψ hB hψ
  constructor
  · intro h T' σ hσ g hg a
    rw [Category.comp_id] at hσ
    subst hσ
    have hG : pushPt m.cart.1.w g ≫ ψ = 1 := by
      ext
      rw [one_left', Over.comp_left]
      show (g.left ≫ m.φ) ≫ ψ.left = _
      rw [Category.assoc, hψ, ← Category.assoc, ← Over.comp_left, hg, push_one hB]
      rfl
    have h2 := h (Over.mk (T'.hom ≫ t)) T'.hom rfl (pushPt m.cart.1.w g) hG a
    apply eq_one_of_push hB
    have e := congrArg Over.Hom.left h2
    rw [one_left', Over.comp_left, Over.comp_left] at e
    simp only [Over.comp_left, Category.assoc]
    rw [← hψ, ← Category.assoc (o₁.act.act a).left, m.act a, Category.assoc]
    exact e
  · intro h T0 σ hσ g hg a
    have w : g.left ≫ o.A.hom = σ ≫ t := by rw [Over.w g, hσ]
    let g₁ : Over.mk σ ⟶ o₁.A := Over.homMk (m.cart.1.lift g.left σ w) (m.cart.1.lift_snd _ _ _)
    have hg₁ : g₁.left ≫ m.φ = g.left := m.cart.1.lift_fst _ _ _
    have h1 : g₁ ≫ ψ₁ = 1 := by
      apply eq_one_of_push hB
      rw [Over.comp_left, Category.assoc, ← hψ, ← Category.assoc, hg₁, ← Over.comp_left, hg, one_left', ← hσ, Category.assoc]
      rfl
    have h2 := h (Over.mk σ) σ (Category.comp_id σ) g₁ h1 a
    ext
    rw [one_left', Over.comp_left, Over.comp_left, ← hg₁, Category.assoc, ← Category.assoc m.φ (o.act.act a).left,
      ← m.act a]
    simp only [Category.assoc]
    rw [hψ]
    have e : (g₁ ≫ o₁.act.act a ≫ ψ₁).left ≫ θ = (1 : Over.mk σ ⟶ B₁).left ≫ θ := by rw [h2]
    rw [push_one hB] at e
    simp only [Over.comp_left, Category.assoc] at e
    rw [e, ← hσ, Category.assoc]
    rfl

end GlobalTheory.UPel.HT.ES
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.quasiInverseIsogenyPair_baseChange_grpPullback : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ : A₁.left ⟶ A.left), IsAbelianScheme B → IsQuasiInv k ψ ψ' → IsGrpPullback A₁ A t φ → ∃ (B₁ : Over T) (_ : GrpObj B₁) (_ : IsCommMonObj B₁) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ ∧ IsGrpPullback B₁ B t θ ∧ IsQuasiInv k ψ₁ ψ₁' ∧ φ ≫ ψ.left = ψ₁.left ≫ θ ∧ θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  first | (exact @GlobalTheory.UPel.HT.ES.pullQuasiInv) | (exact GlobalTheory.UPel.HT.ES.pullQuasiInv) | (intros; apply GlobalTheory.UPel.HT.ES.pullQuasiInv  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_clopen_kernelStable_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ KerStableAt o ψ t := by
  first | exact @GlobalTheory.UPel.HT.ES.exists_clopen_kerStableAt | exact GlobalTheory.UPel.HT.ES.exists_clopen_kerStableAt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_clopen_locus_of_annihilator : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ), ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ TjAt r w j o ψ t := by
  first | exact @UpperTheory.Cb.exists_clopen_locus_of_annihilator | exact UpperTheory.Cb.exists_clopen_locus_of_annihilator
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical


theorem _root_.GlobalTheory.T.continuous_adelicThetaTransformSymplectic_of_decay : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → Continuous (thV ψ Φ) := by
  first | exact @GlobalTheory.ThetaTransform.continuous_thV | exact GlobalTheory.ThetaTransform.continuous_thV | (intros; apply GlobalTheory.ThetaTransform.continuous_thV <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical


theorem _root_.GlobalTheory.T.inverseAdelicThetaTransform_rapid_decay : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ 𝒱 : Set (VA F N → ℂ), (∀ f ∈ 𝒱, QuasiV ψ f ∧ ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) → (∀ f ∈ 𝒱, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ f' ∈ 𝒱, ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0) → ∀ f ∈ 𝒱, ∀ (x : Fin N → AF F) (k : ℕ), ∃ C : ℝ, ∀ t : Fin N → mixedEmbedding.mixedSpace F, ‖t‖ ^ k * ‖invV ψ ν 𝓓 f (x + embR t)‖ ≤ C := by
  first | exact @GlobalTheory.InvDecay.invV_decay | exact GlobalTheory.InvDecay.invV_decay | (intros; apply GlobalTheory.InvDecay.invV_decay <;> assumption)
end
