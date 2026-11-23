module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteProjBundleModelCohomologyEquivProdFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle342
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle456
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open GlobalTheory.EtC.CupSpec GlobalTheory.EtC.DiscCoch in

theorem _root_.GlobalTheory.T.discrete_projBundleModel_cohomology_equiv_prod_fibre :
    ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ),
      ∃ e : CohomologyClass ((chains R).obj (disc.obj F)) (Jcx R q N I) n ≃+
          CohomologyClass ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n,
        ∀ (β : Cocycle ((chains R).obj (disc.obj F)) (Jcx R q N I) n)
          (γ : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n),
          (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), β.1.v (-(p : ℤ)) s h = 0) →
          (∀ (U : Scheme.{0}) (x : F.obj (op U)),
            ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n,
              ev (R := R) β.1 0 n (by simp) U x = Jsec c ∧
              ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + n = s) (V : Scheme.{0})
                (y : Sx (sch.obj U ⨯ fibQ q N) k V),
                ev (R := R) c k s hs V y =
                  ev (R := R) γ.1 k s hs V
                    (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y)) →
          e (CohomologyClass.mk β) = CohomologyClass.mk γ := by
  apply _root_.GlobalTheory.EtC.DiscCoch.model <;> assumption
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC
namespace TensFlat

variable {R : Type} [CommRing R]

theorem rl_comm {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module (ULift.{1} R) M] [Module (ULift.{1} R) N] [Module (ULift.{1} R) P] [Module (ULift.{1} R) Q]
    (f : M →ₗ[ULift.{1} R] P) (g : N →ₗ[ULift.{1} R] Q) (x : TensorProduct (ULift.{1} R) M N) :
    LinearMap.rTensor Q f (LinearMap.lTensor M g x) = LinearMap.lTensor P g (LinearMap.rTensor N f x) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_apply]

theorem tres_comp (X Y : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) {W V U : Scheme.{0}} (m : W ⟶ V) (k : V ⟶ U)
    (x : TensorProduct (ULift.{1} R) (X.obj (op U)) (Y.obj (op U))) :
    TensorProduct.map (X.map (m ≫ k).op).hom (Y.map (m ≫ k).op).hom x =
      TensorProduct.map (X.map m.op).hom (Y.map m.op).hom (TensorProduct.map (X.map k.op).hom (Y.map k.op).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem nat_apply {X Z : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (ψ : X ⟶ Z) {V U : Scheme.{0}} (k : V ⟶ U)
    (a : X.obj (op U)) : (Z.map k.op).hom ((ψ.app (op U)).hom a) = (ψ.app (op V)).hom ((X.map k.op).hom a) := by
  have h := congrArg (fun h => ModuleCat.Hom.hom h a) (ψ.naturality k.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem tres_rTensor {X Z : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (Y : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    (ψ : X ⟶ Z) {V U : Scheme.{0}} (k : V ⟶ U) (x : TensorProduct (ULift.{1} R) (X.obj (op U)) (Y.obj (op U))) :
    TensorProduct.map (Z.map k.op).hom (Y.map k.op).hom (LinearMap.rTensor _ (ψ.app (op U)).hom x) =
      LinearMap.rTensor _ (ψ.app (op V)).hom (TensorProduct.map (X.map k.op).hom (Y.map k.op).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, nat_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tres_lTensor (X : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) {Y Z : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)}
    (ψ : Y ⟶ Z) {V U : Scheme.{0}} (k : V ⟶ U) (x : TensorProduct (ULift.{1} R) (X.obj (op U)) (Y.obj (op U))) :
    TensorProduct.map (X.map k.op).hom (Z.map k.op).hom (LinearMap.lTensor _ (ψ.app (op U)).hom x) =
      LinearMap.lTensor _ (ψ.app (op V)).hom (TensorProduct.map (X.map k.op).hom (Y.map k.op).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, nat_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem ker_tensor_loc {A B C : Shv R} (f : A ⟶ B) (g : B ⟶ C)
    (hex : ∀ U (b : Sec B U), Sec.map g b = 0 → Loc U fun V k => ∃ a : Sec A V, Sec.map f a = Sec.res k b)
    (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (W : Scheme.{0})
    (z : TensorProduct (ULift.{1} R) (LinearMap.ker (g.hom.app (op W)).hom) (P.obj (op W))) :
    Loc W fun W' n => ∃ y : TensorProduct (ULift.{1} R) (Sec A W') (P.obj (op W')),
      LinearMap.rTensor _ (f.hom.app (op W')).hom y = TensorProduct.map (B.obj.map n.op).hom (P.map n.op).hom
        (LinearMap.rTensor _ (LinearMap.ker (g.hom.app (op W)).hom).subtype z) := by
  induction z using TensorProduct.induction_on with
  | zero => exact loc_of_forall W _ fun W' n => ⟨0, by simp⟩
  | tmul b p =>
    refine loc_mono W _ _ (hex W b.1 (LinearMap.mem_ker.mp b.2)) ?_
    rintro W' n ⟨a, ha⟩
    refine ⟨a ⊗ₜ (P.map n.op).hom p, ?_⟩
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, Submodule.coe_subtype]
    exact congrArg (· ⊗ₜ[ULift.{1} R] (P.map n.op).hom p) ha
  | add z₁ z₂ h₁ h₂ =>
    refine loc_mono W _ _ (loc_and W _ _ h₁ h₂) ?_
    rintro W' n ⟨⟨y₁, e₁⟩, ⟨y₂, e₂⟩⟩
    exact ⟨y₁ + y₂, by simp only [map_add (f := _), e₁, e₂]⟩

end TensFlat


open TensFlat in
theorem tensor_flat_loc_exact : ∀ (R : Type) [CommRing R] (M : Shv R), FlatS M → ∀ {A B C : Shv R} (f : A ⟶ B) (g : B ⟶ C), f ≫ g = 0 → (∀ U (b : Sec B U), Sec.map g b = 0 → Loc U fun V k => ∃ a : Sec A V, Sec.map f a = Sec.res k b) → ∀ U (x : TensorProduct (ULift.{1} R) (Sec B U) (Sec M U)), (Loc U fun V k => LinearMap.rTensor _ (g.hom.app (op V)).hom (TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x) = 0) → Loc U fun V k => ∃ y : TensorProduct (ULift.{1} R) (Sec A V) (Sec M V), LinearMap.rTensor _ (f.hom.app (op V)).hom y = TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x := by
  intro R _ M hM A B C f g _ hex U x hx
  obtain ⟨P, φ, hsurj, hinj, hflat⟩ := hM
  have h1 := (GlobalTheory.T.sectionwiseTensor_presheaf_locallyBijective R B.obj P M.obj φ hsurj hinj U).1 x
  apply loc_trans
  refine loc_mono U _ _ (loc_and U _ _ h1 hx) ?_
  rintro V k ⟨⟨x', hx'⟩, hz⟩
  have hz0 : LinearMap.lTensor _ (φ.app (op V)).hom (LinearMap.rTensor _ (g.hom.app (op V)).hom x') = 0 := by
    rw [← rl_comm, hx']
    exact hz
  have h2 := (GlobalTheory.T.sectionwiseTensor_presheaf_locallyBijective R C.obj P M.obj φ hsurj hinj V).2 _ hz0
  apply loc_trans
  refine loc_mono V _ _ h2 ?_
  intro W m hm
  have hg0 : LinearMap.rTensor _ (g.hom.app (op W)).hom
      (TensorProduct.map (B.obj.map m.op).hom (P.map m.op).hom x') = 0 := by
    rw [← tres_rTensor]; exact hm
  by_cases hW : Nonempty W
  · haveI := hflat W hW
    have hexact := Module.Flat.rTensor_exact (P.obj (op W))
      (LinearMap.exact_subtype_ker_map (g.hom.app (op W)).hom)
    obtain ⟨z, hzx⟩ := (hexact _).mp hg0
    refine loc_mono W _ _ (ker_tensor_loc f g hex P W z) ?_
    rintro W' n ⟨y, hy⟩
    refine ⟨LinearMap.lTensor _ (φ.app (op W')).hom y, ?_⟩
    rw [rl_comm, hy, hzx, tres_comp, tres_comp, ← hx', tres_lTensor, tres_lTensor]
  · haveI : IsEmpty W := not_nonempty_iff.mp hW
    exact loc_of_isEmpty W _

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.FreeMonoEpi

theorem freeP_map_mono (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) [Mono f] : Mono ((freeP R).map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [ModuleCat.mono_iff_injective]
  have hf : Function.Injective (f.app U) := (mono_iff_injective (f.app U)).1 inferInstance
  have hu : Function.Injective (uliftFunctor.{1}.map (f.app U)) := by
    intro a b h; cases a; cases b; exact congrArg ULift.up (hf (congrArg ULift.down h))
  exact Finsupp.mapDomain_injective hu

theorem free_map_mono (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) [Mono f] : Mono ((free R).map f) := by
  haveI := freeP_map_mono R f
  exact (presheafToSheaf _ _).map_mono ((freeP R).map f)

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (k ≫ g) a = Sec.res k (Sec.res g a) := by
  simp [Sec.res]

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.map φ (Sec.res g a) = Sec.res g (Sec.map φ a) := by
  have := congrArg (fun h => ModuleCat.Hom.hom h a) (φ.hom.naturality g.op)
  simpa [Sec.map, Sec.res] using this

abbrev gsum (R : Type) [CommRing R] (P : PSh) (V : Scheme.{0}) (c : P.obj (op V) →₀ ULift.{1} R) : Sec ((free R).obj P) V :=
  c.sum fun x r => r • freeGen R P V x

theorem res_gsum (R : Type) [CommRing R] (P : PSh) {W V : Scheme.{0}} (k : W ⟶ V) (c : P.obj (op V) →₀ ULift.{1} R) :
    Sec.res k (gsum R P V c) = c.sum fun x r => r • freeGen R P W (P.map k.op x) := by
  simp only [gsum, Sec.res, map_finsuppSum, map_smul]
  refine Finsupp.sum_congr fun x _ => ?_
  congr 1
  exact (GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.1 W V k x

theorem res_gsum' (R : Type) [CommRing R] (P : PSh) {W V : Scheme.{0}} (k : W ⟶ V) (c : P.obj (op V) →₀ ULift.{1} R) :
    Sec.res k (gsum R P V c) = gsum R P W (Finsupp.mapDomain (P.map k.op) c) := by
  rw [res_gsum, gsum, Finsupp.sum_mapDomain_index (h := fun (x : P.obj (op W)) (r : ULift.{1} R) => r • freeGen R P W x)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]

theorem map_gsum (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) {V : Scheme.{0}} (c : P.obj (op V) →₀ ULift.{1} R) :
    Sec.map ((free R).map f) (gsum R P V c) = gsum R Q V (Finsupp.mapDomain (f.app (op V)) c) := by
  rw [gsum, gsum, Finsupp.sum_mapDomain_index (h := fun (x : Q.obj (op V)) (r : ULift.{1} R) => r • freeGen R Q V x)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Sec.map, map_finsuppSum, map_smul]
  refine Finsupp.sum_congr fun x _ => ?_
  congr 1
  exact (GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.2 Q f V x

theorem loc_all {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.1 U P h

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) :
    Loc U Q :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U P Q h hPQ

theorem loc_trans {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.1 U P h

theorem loc_fin {U : Scheme.{0}} {ι : Type} [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.1 U ι P h

theorem free_map_epi (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q)
    (hs : ∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) : Epi ((free R).map f) := by
  rw [(GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R ((free R).map f)).2.2.1]
  intro U b
  apply loc_trans
  refine loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R Q U).1 b) ?_
  rintro V g ⟨c, hc⟩
  have hl : Loc V fun W k => ∀ i : c.support, ∃ x, f.app (op W) x = Q.map k.op i.1 :=
    loc_fin (fun i : c.support => fun W k => ∃ x, f.app (op W) x = Q.map k.op i.1) (fun i => hs V i.1)
  refine loc_mono hl ?_
  intro W k hk
  choose x hx using hk
  refine ⟨∑ i : c.support, c i.1 • freeGen R P W (x i), ?_⟩
  have e1 : Sec.map ((free R).map f) (∑ i : c.support, c i.1 • freeGen R P W (x i)) =
      ∑ i : c.support, c i.1 • freeGen R Q W (Q.map k.op i.1) := by

    simp only [Sec.map, map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← hx i]; exact (GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.2 Q f W (x i)
  rw [e1, res_comp, hc, res_gsum, Finsupp.sum]
  exact Finset.sum_coe_sort c.support (fun y => c y • freeGen R Q W (Q.map k.op y))

theorem loc_kill {R : Type} [CommRing R] {P Q : PSh} (f : P ⟶ Q)
    (hi : ∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x')
    {W : Scheme.{0}} (d : P.obj (op W) →₀ ULift.{1} R) (hd : Finsupp.mapDomain (f.app (op W)) d = 0) :
    Loc W fun _ k => Finsupp.mapDomain (P.map k.op) d = 0 := by
  classical
  have hl : Loc W fun W' k => ∀ i : d.support × d.support,
      f.app (op W) i.1.1 = f.app (op W) i.2.1 → P.map k.op i.1.1 = P.map k.op i.2.1 :=
    loc_fin _ fun i => by
      by_cases h : f.app (op W) i.1.1 = f.app (op W) i.2.1
      · exact loc_mono (hi W _ _ h) fun _ _ e _ => e
      · exact loc_all fun _ _ e => absurd e h
  refine loc_mono hl ?_
  intro W' k hk
  rcases d.support.eq_empty_or_nonempty with h0 | ⟨x0, _⟩
  · rw [Finsupp.support_eq_empty.1 h0, Finsupp.mapDomain_zero]
  let h : Q.obj (op W) → P.obj (op W') := fun y =>
    if hy : ∃ x ∈ d.support, f.app (op W) x = y then P.map k.op hy.choose else P.map k.op x0
  have e : Finsupp.mapDomain (P.map k.op) d = Finsupp.mapDomain (h ∘ f.app (op W)) d := by
    refine Finsupp.mapDomain_congr rfl ?_
    intro x hx
    have hy : ∃ x' ∈ d.support, f.app (op W) x' = f.app (op W) x := ⟨x, hx, rfl⟩
    show _ = h (f.app (op W) x)
    simp only [h, dif_pos hy]
    exact hk (⟨x, hx⟩, ⟨hy.choose, hy.choose_spec.1⟩) hy.choose_spec.2.symm
  rw [e, Finsupp.mapDomain_comp, hd, Finsupp.mapDomain_zero]

theorem free_map_mono_of_loc (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q)
    (hi : ∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x') :
    Mono ((free R).map f) := by
  rw [(GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R ((free R).map f)).2.1]
  intro U a ha
  apply loc_trans
  refine loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R P U).1 a) ?_
  rintro V g ⟨c, hc⟩
  have h0 : gsum R Q V (Finsupp.mapDomain (f.app (op V)) c) = 0 := by
    rw [← map_gsum, show gsum R P V c = Sec.res g a from hc.symm, map_res, ha]; simp [Sec.res]
  apply loc_trans
  refine loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R Q V).2 _ h0) ?_
  intro W k hk
  have hd : Finsupp.mapDomain (f.app (op W)) (Finsupp.mapDomain (P.map k.op) c) = 0 := by
    rw [← Finsupp.mapDomain_comp]
    rw [show (f.app (op W) ∘ P.map k.op) = (Q.map k.op ∘ f.app (op V)) from
      funext fun x => NatTrans.naturality_apply f k.op x]
    rw [Finsupp.mapDomain_comp]; exact hk
  refine loc_mono (loc_kill f hi _ hd) ?_
  intro W' k' hk'
  rw [res_comp, res_comp, hc, res_gsum', res_gsum', hk']
  simp [gsum]

end GlobalTheory.EtC.FreeMonoEpi

namespace GlobalTheory.EtC


open GlobalTheory.EtC.FreeMonoEpi in
theorem free_map_mono_epi_iso : ∀ (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q), (Mono f → Mono ((free R).map f)) ∧ ((∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) → Epi ((free R).map f)) ∧ ((∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) → (∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x') → IsIso ((free R).map f)) := by
  intro R _ P Q f
  refine ⟨fun _ => free_map_mono R f, free_map_epi R f, fun hs hi => ?_⟩
  haveI := free_map_epi R f hs
  haveI := free_map_mono_of_loc R f hi
  exact isIso_of_mono_of_epi _

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.SchLocExact

variable {R : Type} [CommRing R]

theorem map_res {F G : Shv R} (ψ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map ψ (Sec.res g x) = Sec.res g (Sec.map ψ x) := by
  simp only [Sec.map, Sec.res]
  exact congrArg (fun f => f.hom x) (ψ.hom.naturality g.op)

theorem map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := by
  simp [Sec.map]

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.res f x) = Sec.res (g ≫ f) x := by
  simp [Sec.res]

theorem res_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

theorem subsingleton_of_homotopyEquiv {K L M : Cx R} (e : HomotopyEquiv K L) (n : ℤ)
    (h : Subsingleton (CohomologyClass L M n)) : Subsingleton (CohomologyClass K M n) := by
  suffices H : ∀ x : CohomologyClass K M n, x = 0 from ⟨fun x y => (H x).trans (H y).symm⟩
  intro x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have h0 : cpull e.inv M n (CohomologyClass.mk α) = 0 := Subsingleton.elim _ _
  have key : cpull e.hom M n (cpull e.inv M n (CohomologyClass.mk α)) = CohomologyClass.mk α := by
    change CohomologyClass.mk (zcomp (Cocycle.ofHom e.hom) (zcomp (Cocycle.ofHom e.inv) α (zero_add n)) (zero_add n)) =
      CohomologyClass.mk α
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨n.negOnePow • (Cochain.ofHomotopy e.homotopyHomInvId).comp α.1 (by omega), ?_⟩
    rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) (by omega), Cocycle.δ_eq_zero, δ_ofHomotopy]
    ext p q hpq
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq, smul_smul]
  rw [← key, h0, map_zero]

theorem lift_of_subsingleton {A : Shv R} {M : Cx R} {m' m : ℤ} (hm : m' + 1 = m)
    (hA : Subsingleton (CohomologyClass (sgl A) M m)) (f : A ⟶ M.X m) (hf : f ≫ M.d m (m + 1) = 0) :
    ∃ g : A ⟶ M.X m', g ≫ M.d m' m = f := by
  have h0 : CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add m) (m + 1) rfl hf) = 0 := Subsingleton.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ m' hm] at h0
  exact h0

end GlobalTheory.EtC.SchLocExact


open GlobalTheory.EtC.SchLocExact in
theorem GlobalTheory.EtC.sch_loc_exact : ∀ (R : Type) [CommRing R] (M : Cx R) (U : Scheme.{0}),
    (∀ n, Subsingleton (CohomologyClass ((chains R).obj (sch.obj U)) M n)) → ∀ (n : ℤ) (b : Sec (M.X n) U),
    Sec.map (M.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (M.X (n - 1)) V, Sec.map (M.d (n - 1) n) a = Sec.res g b := by
  intro R _ M U hU n b hb
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  have hs : Subsingleton (CohomologyClass (sgl ((free R).obj (yoneda.obj U))) M n) :=
    subsingleton_of_homotopyEquiv (e (yoneda.obj U)) n (hU n)
  obtain ⟨hex, -, -, -⟩ := GlobalTheory.EtC.free_hom_sections R (yoneda.obj U) (M.X n)
  obtain ⟨φ, hφ⟩ := hex (fun V x => Sec.res x b) (fun V W g x => res_res g x b)
  have hφd : φ ≫ M.d n (n + 1) = 0 := by
    apply (GlobalTheory.EtC.free_hom_sections R (yoneda.obj U) (M.X (n + 1))).2.1
    intro W x
    rw [map_comp, hφ, map_res, hb]
    simp [Sec.map, Sec.res]
  obtain ⟨ψ, hψ⟩ := lift_of_subsingleton (m' := n - 1) (by omega) hs φ hφd
  let a0 : Sec (M.X (n - 1)) U := Sec.map ψ (freeGen R (yoneda.obj U) U (𝟙 U))
  have ha0 : Sec.map (M.d (n - 1) n) a0 = b := by
    simp only [a0]
    rw [← map_comp, hψ, hφ, res_id]
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨Sec.res g a0, ?_⟩⟩
  rw [map_res, ha0]
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.PrHomotopy

lemma deg_sub {N k : ℕ} {a b : Pr N →₀ ℤ} (ha : Pr.Deg k a) (hb : Pr.Deg k b) : Pr.Deg k (a - b) := by
  intro z hz
  rcases Finset.mem_union.1 (Finsupp.support_sub hz) with h | h
  · exact ha z h
  · exact hb z h

lemma deg_zero {N k : ℕ} : Pr.Deg k (0 : Pr N →₀ ℤ) := by
  intro z hz; simp at hz

lemma bd_sub {N : ℕ} (a b : Pr N →₀ ℤ) : Pr.bd (a - b) = Pr.bd a - Pr.bd b := by
  simp [Pr.bd, map_sub, smul_sub, Finset.sum_sub_distrib]

lemma aw_zero_eq_wa_zero : Pr.aw 0 = Pr.wa 0 := by
  simp [Pr.aw, Pr.wa]


open Classical in
noncomputable def step (N : ℕ) (c : Pr N →₀ ℤ) : Pr (N + 1) →₀ ℤ :=
  if H : ∃ e, Pr.Deg (N + 2) e ∧ Pr.d (N + 1) e = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c then H.choose else 0

noncomputable def hom : ∀ N, Pr N →₀ ℤ
  | 0 => 0
  | N + 1 => step N (hom N)

lemma step_spec (N : ℕ) (c : Pr N →₀ ℤ) (hc : Pr.Deg (N + 1) c)
    (hd : Pr.bd (Pr.d N c) = Pr.bd (Pr.aw N - Pr.wa N)) :
    Pr.Deg (N + 2) (step N c) ∧ Pr.d (N + 1) (step N c) = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c := by
  obtain ⟨-, -, -, hbdeg, -, hdbd, haw⟩ := GlobalTheory.T.prism_chain_complex_boundary_identities
  have H : ∃ e, Pr.Deg (N + 2) e ∧ Pr.d (N + 1) e = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c := by
    apply GlobalTheory.T.standardSimplexFacePairs_acyclic_positive_degree (N + 1) N
    · exact deg_sub (deg_sub (haw (N + 1)).1 (haw (N + 1)).2) (hbdeg _ _ _ hc)
    · obtain ⟨h1, h2⟩ := GlobalTheory.T.alexanderWhitneyDiagonal_and_swap_chain_maps N
      rw [map_sub, map_sub, h1, h2, hdbd, hd, bd_sub, sub_self]
  unfold step
  rw [dite_eq_left H]
  exact H.choose_spec

lemma hom_spec (N : ℕ) : Pr.Deg (N + 1) (hom N) ∧ Pr.bd (Pr.d N (hom N)) = Pr.bd (Pr.aw N - Pr.wa N) := by
  induction N with
  | zero => exact ⟨deg_zero, by simp [hom, aw_zero_eq_wa_zero]⟩
  | succ N ih =>
    obtain ⟨h1, h2⟩ := step_spec N (hom N) ih.1 ih.2
    obtain ⟨-, -, -, -, hbb, -, -⟩ := GlobalTheory.T.prism_chain_complex_boundary_identities
    refine ⟨h1, ?_⟩
    show Pr.bd (Pr.d (N + 1) (step N (hom N))) = _
    rw [h2, bd_sub, hbb, sub_zero]

end GlobalTheory.EtC.PrHomotopy

theorem GlobalTheory.EtC.pr_aw_wa_homotopy :
    ∃ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧
      ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  refine ⟨PrHomotopy.hom, fun N => (PrHomotopy.hom_spec N).1, ?_, fun N => ?_⟩
  · simp [PrHomotopy.hom, PrHomotopy.aw_zero_eq_wa_zero]
  · have := (PrHomotopy.step_spec N (PrHomotopy.hom N) (PrHomotopy.hom_spec N).1 (PrHomotopy.hom_spec N).2).2
    show Pr.d (N + 1) (PrHomotopy.step N (PrHomotopy.hom N)) + _ = _
    rw [this, sub_add_cancel]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.rootOfUnity_etaleLocally_pow_primitiveRoot : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ ω : (Γ(U, ⊤))ˣ, ω ^ q = 1 →
    Loc U fun V g => ∃ (ζ : Prim q Γ(V, ⊤)) (a : ℕ), (Units.map g.appTop.hom.toMonoidHom ω : Γ(V, ⊤)) = ζ.1 ^ a := by
  first | (exact @GlobalTheory.EtC.RootLoc.root_loc_pow_prim) | (exact GlobalTheory.EtC.RootLoc.root_loc_pow_prim) | (intros; apply GlobalTheory.EtC.RootLoc.root_loc_pow_prim <;> assumption)
end
