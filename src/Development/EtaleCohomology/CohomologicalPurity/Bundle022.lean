module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle012
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Development.EtaleCohomology.CohomologicalPurity.Bundle013
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (a : Ht q E' n i) : pull _ f (tw q i') n' (Ht.cast h1 h2 a) = Ht.cast h1 h2 (pull _ f (tw q i) n a) := by
  subst h1; subst h2; rfl

theorem pull_cpow (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hI : Inv q E')
    (x : Ht q E' 2 1) (k : ℕ) : pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast, (h6 q).2.1 f hI]
  | succ k ih => rw [cpow_succ, cpow_succ, pull_cast, (h6 q).1, ih]

theorem tail_fst (d : ℕ) (R : Type) [CommRing R] :
    (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) ≫ prod.fst ≫ Pj.line d 0 =
      prod.fst ≫ Pj.line (d + 1) 1 := by
  rw [prod.map_fst_assoc, Pj.tail_line]

theorem pull_hyp (h6 : DivisorNaturality) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (hI : Inv q (PR d 0 R)) :
    pull _ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) _ _ (hyp q d 0 R) = hyp q (d + 1) 1 R := by
  unfold hyp
  rw [(h6 q).2.2.1 _ _ hI, tail_fst]

theorem tail_poly (hG : LeafGeo) (h6 : DivisorNaturality) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
    (hq : IsUnit (q : R)) (n i : ℤ) (a : ∀ j : Fin d, Ht q (sp R) (n - 2 * (j : ℕ)) (i - (j : ℕ))) :
    pull _ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) (tw q i) n (poly q d 0 R d n i a) =
      poly q (d + 1) 1 R d n i a := by
  have hI := hG.2.1 q d 0 R hq
  unfold poly

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_cast, (h6 q).1, ← pull_comp, prod.map_snd, Category.comp_id, pull_cpow h6 q _ hI, pull_hyp h6 q d R hI]

theorem LeafTauU_of (hG : LeafGeo) : LeafTauU := by
  intro hPB hTl H q _ d R _ hq n i
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hb := (hTl H q d R hq i n).comp (hPB H.1 h6 H.2.2.2.2.2.2.2.2.2.2.1 q d R hq n i)
  convert hb using 1
  funext a
  exact (tail_poly hG h6 q d R hq n i a).symm

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem isIso_cokMap_f {R : Type} [CommRing R] {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (comm : f ≫ b = a ≫ f') (n : ℤ)
    (h : IsIso (cokernel.map (f.f n) (f'.f n) (a.f n) (b.f n) (sqw comm n).symm)) : IsIso ((cokernel.map f f' a b comm.symm).f n) := by
  let E := HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) n
  let e1 : (cokernel f).X n ≅ cokernel (f.f n) := PreservesCokernel.iso E f
  let e2 : (cokernel f').X n ≅ cokernel (f'.f n) := PreservesCokernel.iso E f'
  have h1 : (cokernel.π f).f n ≫ e1.hom = cokernel.π (f.f n) := PreservesCokernel.π_iso_hom E f
  have h2 : (cokernel.π f').f n ≫ e2.hom = cokernel.π (f'.f n) := PreservesCokernel.π_iso_hom E f'
  have hep : Epi ((cokernel.π f).f n) := by
    have e : (cokernel.π f).f n = cokernel.π (f.f n) ≫ e1.inv := by
      rw [← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [e]; infer_instance
  have key : (cokernel.map f f' a b comm.symm).f n ≫ e2.hom = e1.hom ≫ cokernel.map (f.f n) (f'.f n) (a.f n) (b.f n) (sqw comm n).symm := by
    rw [← cancel_epi ((cokernel.π f).f n), reassoc_of% h1, ← HomologicalComplex.comp_f_assoc]
    simp [cokernel.map, h2]
  have key' : (cokernel.map f f' a b comm.symm).f n = e1.hom ≫ cokernel.map (f.f n) (f'.f n) (a.f n) (b.f n) (sqw comm n).symm ≫ e2.inv := by
    rw [← Category.assoc, ← key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [key']; infer_instance

theorem shortExact_cok {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) (hf : ∀ n, Mono (f.f n)) :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact := by
  have : Mono f := HomologicalComplex.mono_of_mono_f _ hf
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)) inferInstance inferInstance

theorem leafConeCok_of : LeafConeCok := by
  intro R _ K L K' L' f f' a b comm hf hf' hc
  let S1 := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let S2 := ShortComplex.mk f' (cokernel.π f') (cokernel.condition f')
  let φ : S1 ⟶ S2 := ⟨a, b, cokernel.map f f' a b comm.symm, comm.symm, by simp [S1, S2]⟩
  have q1 := mappingCone.quasiIso_descShortComplex (shortExact_cok f hf)
  have q2 := mappingCone.quasiIso_descShortComplex (shortExact_cok f' hf')
  have hcomp : ∀ n, IsIso (φ.τ₃.f n) := fun n => isIso_cokMap_f f f' a b comm n (hc n)
  have : IsIso φ.τ₃ := HomologicalComplex.Hom.isIso_of_components _
  have hm := mappingCone.map_descShortComplex S1 S2 φ
  have : QuasiIso (mappingCone.descShortComplex S1 ≫ φ.τ₃) := inferInstance
  have : QuasiIso (mappingCone.map f f' a b comm ≫ mappingCone.descShortComplex S2) := by
    change QuasiIso (mappingCone.map S1.f S2.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm ≫ mappingCone.descShortComplex S2)
    rw [hm]; infer_instance
  exact (quasiIso_iff_comp_right _ (mappingCone.descShortComplex S2)).1 this

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

open GlobalTheory.EtC in
theorem leafConeCok : LeafConeCok := by
  intro R _ K L K' L' f f' a b comm hf hf' hi
  have hm : Mono f := HomologicalComplex.mono_of_mono_f _ hf
  have hm' : Mono f' := HomologicalComplex.mono_of_mono_f _ hf'
  let S₁ := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let S₂ := ShortComplex.mk f' (cokernel.π f') (cokernel.condition f')
  have h₁ : S₁.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)) hm inferInstance
  have h₂ : S₂.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f')) hm' inferInstance
  let τ : S₁ ⟶ S₂ := { τ₁ := a, τ₂ := b, τ₃ := cokernel.map f f' a b comm.symm, comm₁₂ := comm.symm, comm₂₃ := by simp [S₁, S₂] }
  have iso3 : IsIso (cokernel.map f f' a b comm.symm) := by
    have : ∀ n, IsIso ((cokernel.map f f' a b comm.symm).f n) := by
      intro n
      have e₁ := (h₁.map_of_exact (HomologicalComplex.eval _ _ n)).gIsCokernel
      have e₂ := (h₂.map_of_exact (HomologicalComplex.eval _ _ n)).gIsCokernel
      let i₁ : cokernel (f.f n) ≅ (cokernel f).X n := (colimit.isColimit _).coconePointUniqueUpToIso e₁
      let i₂ : cokernel (f'.f n) ≅ (cokernel f').X n := (colimit.isColimit _).coconePointUniqueUpToIso e₂
      have key : (cokernel.map f f' a b comm.symm).f n = i₁.inv ≫ cokernel.map (f.f n) (f'.f n) (a.f n) (b.f n) (sqw comm n).symm ≫ i₂.hom := by
        rw [Iso.eq_inv_comp]
        refine (cancel_epi (cokernel.π (f.f n))).1 ?_
        have p₁ : cokernel.π (f.f n) ≫ i₁.hom = (cokernel.π f).f n :=
          (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom e₁ WalkingParallelPair.one
        have p₂ : cokernel.π (f'.f n) ≫ i₂.hom = (cokernel.π f').f n :=
          (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom e₂ WalkingParallelPair.one
        rw [← Category.assoc, p₁, cokernel.π_desc_assoc, Category.assoc, p₂, ← HomologicalComplex.comp_f,
          ← HomologicalComplex.comp_f, cokernel.π_desc]
      rw [key]; infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  have q1 := CochainComplex.mappingCone.quasiIso_descShortComplex h₁
  have q2 := CochainComplex.mappingCone.quasiIso_descShortComplex h₂
  have e := CochainComplex.mappingCone.map_descShortComplex S₁ S₂ τ
  have : QuasiIso (CochainComplex.mappingCone.map f f' a b comm ≫ CochainComplex.mappingCone.descShortComplex S₂) := by
    rw [show CochainComplex.mappingCone.map f f' a b comm = CochainComplex.mappingCone.map S₁.f S₂.f τ.τ₁ τ.τ₂ τ.comm₁₂.symm from rfl, e]
    infer_instance
  exact (quasiIso_iff_comp_right _ (CochainComplex.mappingCone.descShortComplex S₂)).1 this

theorem etaleSplitExcision_of_mono_cokernel_relative (hM : LeafChainsMono) (hK : LeafCokIso) (hR : LeafHsRel) : LateralTheory.CohomologicalPurity.Thom.LeafExcSp :=
  leafExcSp_of' hM hK leafConeCok hR

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.ZlocPf

theorem res_comp {R : Type} [CommRing R] {G : Shv R} {T V W : Scheme.{0}} (f : T ⟶ V) (g : V ⟶ W) (a : Sec G W) :
    Sec.res (f ≫ g) a = Sec.res f (Sec.res g a) := by
  show (G.obj.map (f ≫ g).op).hom a = (G.obj.map f.op).hom ((G.obj.map g.op).hom a)
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_zero {R : Type} [CommRing R] {G : Shv R} {V W : Scheme.{0}} (f : V ⟶ W) :
    Sec.res f (0 : Sec G W) = 0 := by
  show (G.obj.map f.op).hom 0 = 0
  exact map_zero _

theorem map_res {R : Type} [CommRing R] {G H : Shv R} (φ : G ⟶ H) {V W : Scheme.{0}} (f : V ⟶ W) (a : Sec G W) :
    Sec.map φ (Sec.res f a) = Sec.res f (Sec.map φ a) := by
  have e := φ.hom.naturality f.op
  show (G.obj.map f.op ≫ φ.hom.app (op V)).hom a = (φ.hom.app (op W) ≫ H.obj.map f.op).hom a
  rw [e]

theorem sep {R : Type} [CommRing R] {G : Shv R} {Y : Scheme.{0}} (s : Sec G Y)
    (H : ∀ y : Y, ∃ (Z : Scheme.{0}) (f : Z ⟶ Y), IsOpenImmersion f ∧ y ∈ Set.range f ∧ Sec.res f s = 0) : s = 0 := by
  let I := {p : Σ Z : Scheme.{0}, Z ⟶ Y // IsOpenImmersion p.2 ∧ Sec.res p.2 s = 0}
  let Zf : I → Scheme.{0} := fun i => i.1.1
  let ff : ∀ i : I, Zf i ⟶ Y := fun i => i.1.2
  have hG : Presheaf.IsSheaf (Scheme.etaleTopology) (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.property
  have hmem : Sieve.generate (Presieve.ofArrows Zf ff) ∈ Scheme.etaleTopology Y := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff (P := (@Etale : MorphismProperty Scheme.{0}))).2 ⟨fun y => ?_, fun i => ?_⟩
    · obtain ⟨Z, f, hf, hy, hs⟩ := H y
      exact ⟨⟨⟨Z, f⟩, hf, hs⟩, hy⟩
    · haveI := i.2.1
      exact (inferInstance : Etale i.1.2)
  have hS := hG.isSheafFor _ hmem
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hS
  have hc : Presieve.Arrows.Compatible (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) ff
      (fun _ => (0 : Sec G _)) := by
    intro i j Z gi gj _
    change (G.obj.map gi.op).hom 0 = (G.obj.map gj.op).hom 0
    simp
  obtain ⟨t, -, ht⟩ := hS _ hc
  have e1 := ht s (fun i => i.2.2)
  have e2 := ht 0 (fun i => res_zero (G := G) i.1.2)
  rw [e1, e2]

theorem vanish {R : Type} [CommRing R] {G : Shv R} {Y Z T : Scheme.{0}} (f : Z ⟶ Y) [IsOpenImmersion f] (g : T ⟶ Y)
    (hr : Set.range g ⊆ Set.range f) (s : Sec G Y) (h0 : Sec.res f s = 0) : Sec.res g s = 0 := by
  rw [← IsOpenImmersion.lift_fac f g hr, res_comp, h0, res_zero]

theorem pt {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) (q : V.toScheme) : W.ι (X.homOfLE h q) = V.ι q := by
  rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]

theorem memι {X : Scheme.{0}} (V : X.Opens) (q : V.toScheme) : V.ι q ∈ V := by
  show V.ι q ∈ (V : Set X)
  rw [← Scheme.Opens.range_ι V]; exact ⟨q, rfl⟩

theorem lift_pt {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) (y : W.toScheme) (hy : W.ι y ∈ V) :
    y ∈ Set.range (X.homOfLE h) := by
  change W.ι y ∈ (V : Set X) at hy
  rw [← Scheme.Opens.range_ι V] at hy
  obtain ⟨q, hq⟩ := hy
  refine ⟨q, W.ι.isOpenEmbedding.injective ?_⟩
  rw [pt, hq]

theorem rangeU {X : Scheme.{0}} (U : X.Opens) {V W : X.Opens} (h : V ≤ W) :
    Set.range ((V.ι ⁻¹ᵁ U).ι ≫ X.homOfLE h) ⊆ Set.range (W.ι ⁻¹ᵁ U).ι := by
  rintro _ ⟨p, rfl⟩
  rw [Scheme.Opens.range_ι]
  show W.ι (((V.ι ⁻¹ᵁ U).ι ≫ X.homOfLE h) p) ∈ U
  rw [Scheme.Hom.comp_apply, pt]
  exact memι (V.ι ⁻¹ᵁ U) p

open LateralTheory.CohomologicalPurity.Cl in
theorem LeafZloc_of : LateralTheory.CohomologicalPurity.Cl.Flq.LeafZloc := by
  intro R _ K X U n
  refine ⟨?_, ?_⟩
  · intro V W h a ha
    obtain ⟨ha1, ha2⟩ := (mem_Zc a).1 ha
    refine (mem_Zc _).2 ⟨?_, ?_⟩
    · rw [← res_comp]; exact vanish _ _ (rangeU U h) a ha1
    · rw [map_res, ha2, res_zero]
  · intro W a H
    refine (mem_Zc _).2 ⟨?_, ?_⟩
    · apply sep; intro y
      obtain ⟨V, h, hxV, hb⟩ := H (W.ι ((W.ι ⁻¹ᵁ U).ι y)) (memι W _)
      obtain ⟨hb1, -⟩ := (mem_Zc _).1 hb
      let O : (W.ι ⁻¹ᵁ U).toScheme.Opens := ((W.ι ⁻¹ᵁ U).ι ≫ W.ι) ⁻¹ᵁ V
      refine ⟨O.toScheme, O.ι, inferInstance, ?_, ?_⟩
      · rw [Scheme.Opens.range_ι]
        show ((W.ι ⁻¹ᵁ U).ι ≫ W.ι) y ∈ V
        rw [Scheme.Hom.comp_apply]; exact hxV
      · rw [← res_comp]
        apply vanish ((V.ι ⁻¹ᵁ U).ι ≫ X.homOfLE h) _ ?_ a (by rw [res_comp]; exact hb1)
        rintro _ ⟨z, rfl⟩
        have hz : ((W.ι ⁻¹ᵁ U).ι ≫ W.ι) (O.ι z) ∈ V := memι O z
        rw [Scheme.Hom.comp_apply] at hz
        have hwU : W.ι ((W.ι ⁻¹ᵁ U).ι (O.ι z)) ∈ U := memι (W.ι ⁻¹ᵁ U) (O.ι z)
        obtain ⟨q, hq⟩ := lift_pt h _ hz
        have hqU : q ∈ (V.ι ⁻¹ᵁ U : Set V.toScheme) := by
          show V.ι q ∈ U
          rw [← pt h, hq]; exact hwU
        rw [← Scheme.Opens.range_ι] at hqU
        obtain ⟨p, hp⟩ := hqU
        exact ⟨p, by rw [Scheme.Hom.comp_apply, hp, hq, Scheme.Hom.comp_apply]⟩
    · apply sep; intro y
      obtain ⟨V, h, hxV, hb⟩ := H (W.ι y) (memι W y)
      obtain ⟨-, hb2⟩ := (mem_Zc _).1 hb
      refine ⟨V.toScheme, X.homOfLE h, inferInstance, lift_pt h y hxV, ?_⟩
      rw [← map_res]; exact hb2

end LateralTheory.CohomologicalPurity.ZlocPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.CohomologicalPurity.Thom

namespace HtpyOnePf

theorem pull_bij_of_iso {R : Type} [CommRing R] (F : Shv R) {E E' : Spc} (a : E ⟶ E') [IsIso a] (n : ℤ) :
    Function.Bijective (pull R a F n) :=
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv a) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id],
    fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

theorem eqv_of_sq {R : Type} [CommRing R] (F : Shv R) {E1 E2 E3 E4 : Spc} (f : E1 ⟶ E2) (g : E3 ⟶ E4)
    (a : E3 ⟶ E1) (b : E4 ⟶ E2) [IsIso a] [IsIso b] (w : a ≫ f = g ≫ b) (hg : Eqv R g F) : Eqv R f F := by
  intro n
  have h1 : (pull R a F n) ∘ (pull R f F n) = (pull R g F n) ∘ (pull R b F n) := by
    funext x; simp only [Function.comp_apply]; rw [← pull_comp, ← pull_comp, w]
  have h2 : Function.Bijective ((pull R a F n) ∘ (pull R f F n)) := by
    rw [h1]; exact (hg n).comp (pull_bij_of_iso F b n)
  exact (Function.Bijective.of_comp_iff' (pull_bij_of_iso F a n) _).1 h2

theorem off_span (A : Type) [CommRing A] (x : A) :
    off A (Ideal.span {x}) = PrimeSpectrum.basicOpen x := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus ((Ideal.span {x} : Ideal A) : Set A))ᶜ = _
  rw [PrimeSpectrum.zeroLocus_span]; exact (PrimeSpectrum.basicOpen_eq_zeroLocus_compl x).symm

theorem off_span_C (A : Type) [CommRing A] (x : A) :
    off (Polynomial A) ((Ideal.span {x}).map Polynomial.C) = PrimeSpectrum.basicOpen (C x) := by
  rw [Ideal.map_span, Set.image_singleton]; exact off_span _ _

attribute [local instance] Polynomial.algebra in
theorem away_poly (A : Type) [CommRing A] (x : A) :
    IsLocalization.Away (C x) (Polynomial (Localization.Away x)) := by
  have := Polynomial.isLocalization (Submonoid.powers x) (Localization.Away x)
  rw [Submonoid.map_powers] at this
  exact this

theorem sq (A : Type) [CommRing A] (x : A)
    (h : off (Polynomial A) ((Ideal.span {x}).map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A (Ideal.span {x})) :
    ∃ (eT : Spec (CommRingCat.of (Polynomial (Localization.Away x))) ≅
        (off (Polynomial A) ((Ideal.span {x}).map Polynomial.C)).toScheme)
      (eB : Spec (CommRingCat.of (Localization.Away x)) ≅ (off A (Ideal.span {x})).toScheme),
      eT.hom ≫ (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h =
        Spec.map (CommRingCat.ofHom (Polynomial.C : Localization.Away x →+* _)) ≫ eB.hom := by
  letI : Algebra (Polynomial A) (Polynomial (Localization.Away x)) := Polynomial.algebra A (Localization.Away x)
  have := away_poly A x
  let jB := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))
  let jT := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial A) (Polynomial (Localization.Away x))))
  have : IsOpenImmersion jT := IsOpenImmersion.of_isLocalization (C x)
  have rB : Set.range jB = Set.range (off A (Ideal.span {x})).ι := by
    rw [Scheme.Opens.range_ι, off_span]
    exact PrimeSpectrum.localization_away_comap_range _ x
  have rT : Set.range jT = Set.range (off (Polynomial A) ((Ideal.span {x}).map Polynomial.C)).ι := by
    rw [Scheme.Opens.range_ι, off_span_C]
    exact PrimeSpectrum.localization_away_comap_range _ (C x)
  refine ⟨IsOpenImmersion.isoOfRangeEq jT _ rT, IsOpenImmersion.isoOfRangeEq jB _ rB, ?_⟩
  rw [← cancel_mono (off A (Ideal.span {x})).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
  simp only [jT, jB, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a : 2
  simp [Polynomial.algebraMap_def]

end HtpyOnePf

theorem LeafHtpyOne_of : LeafHtpyOne := by
  intro _ c4 q _ A _ x hq h i
  obtain ⟨eT, eB, w⟩ := HtpyOnePf.sq A x h
  have hqB : IsUnit ((q : ℕ) : Localization.Away x) := by
    simpa using hq.map (algebraMap A (Localization.Away x))
  refine HtpyOnePf.eqv_of_sq _ _ (sch.map (Spec.map (CommRingCat.ofHom (Polynomial.C : Localization.Away x →+* _))))
    (sch.map eT.hom) (sch.map eB.hom) ?_ (c4 q (Localization.Away x) hqB i)
  rw [← Functor.map_comp, ← Functor.map_comp, w]

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem etale_section_boundary_of_mem_addSubgroup_closure {R : Type} [CommRing R] (K : Cx R) {Y : Scheme.{0}} (U' : Y.Opens) (n : ℤ)
    (a : Sec (K.X n) Y) (ha : a ∈ AddSubgroup.closure {a | Bd K U' n a}) : Bd K U' n a := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, map_zero _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb0, hb⟩ := hx
    obtain ⟨c, hc0, hc⟩ := hy
    refine ⟨b + c, ?_, ?_⟩
    · show ((K.X (n-1)).obj.map U'.ι.op).hom (b + c) = 0
      rw [map_add (f := _), show ((K.X (n-1)).obj.map U'.ι.op).hom b = 0 from hb0, show ((K.X (n-1)).obj.map U'.ι.op).hom c = 0 from hc0, add_zero]
    · show ((K.d (n - 1) n).hom.app (op Y)).hom (b + c) = x + y
      rw [map_add (f := _)]; rw [← hb, ← hc]
  | neg x _ hx =>
    obtain ⟨b, hb0, hb⟩ := hx
    refine ⟨-b, ?_, ?_⟩
    · show ((K.X (n-1)).obj.map U'.ι.op).hom (-b) = 0
      rw [map_neg]; rw [show ((K.X (n-1)).obj.map U'.ι.op).hom b = 0 from hb0, neg_zero]
    · show ((K.d (n - 1) n).hom.app (op Y)).hom (-b) = -x
      rw [map_neg]; rw [← hb]

theorem LeafBdAdd_of : LeafBdAdd := by
  intro R _ K X U n W a ha
  exact etale_section_boundary_of_mem_addSubgroup_closure K _ n a ha

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem etale_sheaf_sections_restrict_restrict_eq_restrict_comp {R : Type} [CommRing R] {F : Shv R} {Y Z W : Scheme.{0}} (f : Y ⟶ Z) (g : Z ⟶ W) (a : Sec F W) :
    Sec.res f (Sec.res g a) = Sec.res (f ≫ g) a := by
  show (F.obj.map f.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (f ≫ g).op).hom a
  rw [op_comp, Functor.map_comp]; rfl

theorem etale_sheaf_sections_restriction_of_zero_eq_zero {R : Type} [CommRing R] {F : Shv R} {Y Z : Scheme.{0}} (f : Y ⟶ Z) :
    Sec.res f (0 : Sec F Z) = 0 := by
  show (F.obj.map f.op).hom 0 = 0
  exact map_zero _

theorem etale_sheaf_sections_map_restrict_comm {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {Y Z : Scheme.{0}} (f : Y ⟶ Z) (a : Sec F Z) :
    Sec.map φ (Sec.res f a) = Sec.res f (Sec.map φ a) := by
  show (φ.hom.app (op Y)).hom ((F.obj.map f.op).hom a) = (G.obj.map f.op).hom ((φ.hom.app (op Z)).hom a)
  have h := φ.hom.naturality f.op
  exact congrArg (fun ψ => ψ.hom a) h

theorem LeafTop_of : LeafTop := by
  intro R _ K X U n c' hc'
  obtain ⟨h1, h2⟩ := (mem_Zc c').1 hc'
  refine ⟨Sec.res X.topIso.inv c', (mem_Zc _).2 ⟨?_, ?_⟩, ?_⟩
  · have : IsIso (⊤ : X.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
    have e : U.ι ≫ X.topIso.inv = inv ((⊤ : X.Opens).ι ∣_ U) ≫ ((⊤ : X.Opens).ι ⁻¹ᵁ U).ι := by
      rw [← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
        Scheme.topIso_hom, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    rw [etale_sheaf_sections_restrict_restrict_eq_restrict_comp, e, ← etale_sheaf_sections_restrict_restrict_eq_restrict_comp, h1, etale_sheaf_sections_restriction_of_zero_eq_zero]
  · rw [etale_sheaf_sections_map_restrict_comm, h2, etale_sheaf_sections_restriction_of_zero_eq_zero]
  · intro V
    rw [etale_sheaf_sections_restrict_restrict_eq_restrict_comp]
    congr 1
    rw [← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Scheme.topIso_hom,
      Scheme.homOfLE_ι]

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end
