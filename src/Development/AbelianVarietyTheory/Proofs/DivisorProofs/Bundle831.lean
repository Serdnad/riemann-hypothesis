module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityRamifiedOfExpansion
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle802
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Ext
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section
variable {R : Type} [CommRing R]

theorem sec_map_res' {F G : Shv R} (ψ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U) :
    Sec.map ψ (Sec.res g z) = Sec.res g (Sec.map ψ z) :=
  congrArg (fun f => f.hom z) (ψ.hom.naturality g.op)

theorem sec_map_comp' {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sec_map_id' {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem flatS_of_iso {M N : Shv R} (i : M ≅ N) (h : FlatS M) : FlatS N := by
  obtain ⟨P, φ, hs, hi, hf⟩ := h
  refine ⟨P, φ ≫ i.hom.hom, ?_, ?_, hf⟩
  · intro U y
    obtain ⟨S, hS, hP⟩ := hs U (Sec.map i.inv y)
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    refine ⟨x, ?_⟩
    change Sec.map i.hom ((φ.app (op V)).hom x) = Sec.res g y
    rw [hx, sec_map_res', ← sec_map_comp', i.inv_hom_id, sec_map_id']
  · intro U x hx
    refine hi U x ?_
    have h1 : Sec.map i.inv (Sec.map i.hom ((φ.app (op U)).hom x)) = Sec.map i.inv (0 : Sec N U) :=
      congrArg (Sec.map i.inv) hx
    rw [← sec_map_comp', i.hom_inv_id, sec_map_id'] at h1
    exact h1.trans (map_zero _)

theorem flatS_of_isZero {M : Shv R} (h : IsZero M) : FlatS M := by
  have hsub : ∀ U : Scheme.{0}, Subsingleton (Sec M U) := fun U => by
    have h1 : IsZero M.obj := (sheafToPresheaf _ _).map_isZero h
    exact ModuleCat.subsingleton_of_isZero (((evaluation _ _).obj (op U)).map_isZero h1)
  refine ⟨M.obj, 𝟙 _, fun U y => ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => ⟨Sec.res g y, rfl⟩⟩,
    fun U x _ => ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => (hsub V).elim _ _⟩, fun U _ => ?_⟩
  haveI := hsub U
  change Module.Flat _ (Sec M U)
  infer_instance

theorem flatS_sgl {F : Shv R} (h : FlatS F) (t : ℤ) : FlatS ((sgl F).X t) := by
  by_cases ht : t = 0
  · subst ht
    exact flatS_of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm h
  · exact flatS_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ ht)

end

theorem isTwRes_tensor : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {I J T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U) (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q i I e → IsTwRes q j J e' → (∀ t, FlatS (J.X t)) → ∀ τ : Pair I J T, τ.IsTensor → IsTwRes q k T fun U ζ => τ.mul U 0 0 0 (add_zero 0) (e U ζ) (e' U ζ) := by
  intro q _ i j k hk I J T e e' hI hJ hflat τ hτ
  obtain ⟨hIge, εI, hεI, heI⟩ := hI
  obtain ⟨hJge, εJ, hεJ, heJ⟩ := hJ
  obtain ⟨μ, hμ, hμgen⟩ := GlobalTheory.T.tateTwist_mul_isTensorPairing q i j k hk
  obtain ⟨T₁, τ₁, hτ₁⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (sgl (tw q i)) J
  have hTge : T.IsStrictlyGE 0 := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ).2.1 hIge hJge
  obtain ⟨u₁, hu₁, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) μ hμ).1 τ₁ (𝟙 _) εJ
  obtain ⟨u₂, hu₂, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ₁ hτ₁).1 τ εI (𝟙 J)
  obtain ⟨ν, hμν, -, hνt⟩ := GlobalTheory.T.exists_isFlip_sheafComplexPairing (ZMod q) μ
  obtain ⟨ν₁, hν₁, -, hν₁t⟩ := GlobalTheory.T.exists_isFlip_sheafComplexPairing (ZMod q) τ₁
  have hflati : ∀ t, FlatS ((sgl (tw q i)).X t) := flatS_sgl (flatS_tw q i)
  have hid : ∀ {K : Cx (ZMod q)} (t : ℤ) {U : Scheme.{0}} (x : Sec (K.X t) U), Sec.map (HomologicalComplex.Hom.f (𝟙 K) t) x = x :=
    fun _ _ _ => rfl
  haveI := hIge
  haveI := hJge
  haveI := hεI
  haveI := hεJ
  have hc : ν.Compat ν₁ εJ (𝟙 _) u₁ := by
    intro U s t w h a b
    rw [hμν U t s w (by omega) b a, hid, hν₁ U t s w (by omega) b (Sec.map (εJ.f s) a), Units.smul_def,
      Units.smul_def]
    have h1 := hu₁ U t s w (by omega) b a
    rw [hid] at h1
    rw [← h1]
    exact map_zsmul ((u₁.f w).hom.app (op U)).hom _ _
  have hq1 : QuasiIso u₁ := GlobalTheory.T.tensor_flat_complex_preserves_quasiIso (ZMod q) ν ν₁ (hνt hμ) (hν₁t hτ₁) hflati εJ u₁ hc
  have hq2 : QuasiIso u₂ := GlobalTheory.T.tensor_flat_complex_preserves_quasiIso (ZMod q) τ₁ τ hτ₁ hτ hflat εI u₂ hu₂
  refine ⟨hTge, u₁ ≫ u₂, quasiIso_comp (hφ := hq1) (hφ' := hq2) _ _, fun U ζ => ?_⟩
  rw [← hμgen U ζ]
  change Sec.map (u₂.f 0) (Sec.map (u₁.f 0) _) = _
  rw [hu₁ U 0 0 0 (add_zero 0), hu₂ U 0 0 0 (add_zero 0), hid, hid, heI, heJ]

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ScalarExt

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)).symm

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hP0⟩ := h
  exact ⟨S, hS, fun V g hg => hP V g (hP0 V g hg)⟩

theorem agree_on_twist {Q q : ℕ} [NeZero Q] (k : ℤ) {T : Cx (ZMod Q)} {J : Cx (ZMod q)} (ε : sgl (tw Q k) ⟶ T)
    (σ σ' : SemiMap T J)
    (he : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))) =
      σ'.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))))
    (U : Scheme.{0}) (y : Sec (tw Q k) U) :
    σ.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) y)) = σ'.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) y)) := by
  refine ((GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (J.X 0) U).1 _ _ (loc_mono ((GlobalTheory.T.tateTwist_sections_locally_generated Q k).1 U y) fun V g hg => ?_))
  rw [σ.nat, σ'.nat, sec_map_res, sec_map_res]
  rcases hg with h0 | ⟨ζ, c, hc⟩
  · rw [h0]; simp
  · have hm : ∀ {A B : Shv (ZMod Q)} (φ : A ⟶ B) (x : Sec A V), Sec.map φ (c • x) = c • Sec.map φ x :=
      fun φ x => map_nsmul (φ.hom.app (op V)).hom c x
    rw [hc, hm, hm, map_nsmul, map_nsmul, he]

end GlobalTheory.EtC.ScalarExt

namespace GlobalTheory.EtC.ScalarExt

theorem semiMap_op_eq_of_flat_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (k : ℤ) {T : Cx (ZMod Q)} (e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes Q k T e → (∀ t, FlatS (T.X t)) → ∀ σ σ' : SemiMap T (res _ (tw q k)), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (e U ζ) = σ'.app U 0 (e U ζ)) → ∀ (E : Spc) (n : ℤ) (x : CohomologyClass ((chains (ZMod Q)).obj E) T n), σ.op.app E n x = σ'.op.app E n x := by
  intro Q q _ h k T e hT hflat σ σ' hσ E n x
  obtain ⟨hge, ε, hqi, hεe⟩ := hT
  haveI := hge
  have hl := zmod_semilinear h σ
  have hl' := zmod_semilinear h σ'
  let εb : sgl ((ext (ZMod.castHom h (ZMod q))).obj (tw Q k)) ⟶ (extCx (ZMod.castHom h (ZMod q))).obj T :=
    ((HomologicalComplex.singleMapHomologicalComplex (ext (ZMod.castHom h (ZMod q))) (ComplexShape.up ℤ) 0).app
      (tw Q k)).inv ≫ (extCx (ZMod.castHom h (ZMod q))).map ε
  have hq2 : QuasiIso ((extCx (ZMod.castHom h (ZMod q))).map ε) :=
    GlobalTheory.T.quasiIso_extendScalars_zmod_of_flat_resolution Q q h (tw Q k) T (GlobalTheory.T.tateTwistSheaf_isLocallyFlat Q k) hflat ε hqi
  haveI : IsIso ((HomologicalComplex.singleMapHomologicalComplex (ext (ZMod.castHom h (ZMod q))) (ComplexShape.up ℤ) 0).app
      (tw Q k)).inv := Iso.isIso_inv _
  have hq1 : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex (ext (ZMod.castHom h (ZMod q))) (ComplexShape.up ℤ) 0).app
      (tw Q k)).inv := quasiIso_of_isIso _
  haveI : QuasiIso εb := quasiIso_comp (hφ := hq1) (hφ' := hq2) _ _
  haveI : (res (ZMod q) (tw q k)).IsKInjective :=
    inferInstanceAs ((injectiveResolution (tw q k)).cochainComplex.IsKInjective)
  haveI : (res (ZMod q) (tw q k)).IsStrictlyGE 0 :=
    inferInstanceAs ((injectiveResolution (tw q k)).cochainComplex.IsStrictlyGE 0)
  haveI : IsIso (sglι (tw Q k)) := by unfold sglι; exact Iso.isIso_inv _
  have he : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))) =
      σ'.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))) := fun U ζ => by
    rw [hεe]; exact hσ U ζ
  have hcomp : εb ≫ semiBar σ hl = εb ≫ semiBar σ' hl' := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = 0
    · subst hi
      have key : (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ (semiBar σ hl).f 0 =
          (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ (semiBar σ' hl').f 0 := by
        change (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ ((adj _).homEquiv _ _).symm (semiHom σ hl 0) =
          (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ ((adj _).homEquiv _ _).symm (semiHom σ' hl' 0)
        rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_left_symm]
        congr 1
        rw [← cancel_epi (sglι (tw Q k))]
        ext U y
        exact agree_on_twist k ε σ σ' he U.unop y
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      dsimp only [εb]
      erw [HomologicalComplex.comp_f, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) key
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _
  obtain ⟨H⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) _ _ _ εb).2 _ _ hcomp
  have h1 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective (ZMod Q) (ZMod q) (unitSemi T) σ (semiBar σ hl) (semi_factor σ hl)).1 E n x
  have h2 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective (ZMod Q) (ZMod q) (unitSemi T) σ' (semiBar σ' hl') (semi_factor σ' hl')).1 E n x
  rw [h1, h2, ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial (ZMod q)).2.2.2.2 _ _ ⟨H⟩ _ n).2]

end GlobalTheory.EtC.ScalarExt

end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem finrank_quot_kerIdeal_succ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G Q : PDivGroup p k)
    (m n : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G) (h : q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G) (hmn : m ≤ n) :
    Module.finrank k (G.A (n + 1) ⧸ kerIdeal (q.app (n + 1))) =
      Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) := by
  have h1 : Hom.app (q ≫ q') (n + 1) = mulBy k (G.A (n + 1)) (p ^ m) := by
    rw [h, ← Nat.cast_pow, natCast_smul_id_app]
  have h2 : torsionIdeal (R := k) (A := G.A (n + 1)) (p ^ m) ≤ kerIdeal (q.app (n + 1)) := by
    rw [torsionIdeal, ← h1, comp_app, kerIdeal_comp]
    refine Ideal.map_mono ((kerIdeal_le_ker_iff _ (counitAlgHom k _)).2 fun c => ?_)
    simp
  have h3 : RingHom.ker (G.res n : G.A (n + 1) →ₐ[k] G.A n) ≤ kerIdeal (q.app (n + 1)) :=
    (G.ker_res n).le.trans ((torsionIdeal_le_of_dvd (pow_dvd_pow p hmn)).trans h2)
  have h4 : Ideal.map (G.res n : G.A (n + 1) →ₐ[k] G.A n) (kerIdeal (q.app (n + 1))) =
      kerIdeal (q.app n) := by
    rw [← kerIdeal_comp, q.comm n, kerIdeal_comp_of_surjective _ (Q.res_surjective n)]
  have hs : Function.Surjective (G.res n : G.A (n + 1) →ₐ[k] G.A n) := G.res_surjective n
  have hc : Ideal.comap (G.res n : G.A (n + 1) →ₐ[k] G.A n) (kerIdeal (q.app n)) =
      kerIdeal (q.app (n + 1)) := by
    rw [← h4, Ideal.comap_map_of_surjective _ hs, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 h3
  let e := Ideal.quotientMapₐ (kerIdeal (q.app n)) (G.res n : G.A (n + 1) →ₐ[k] G.A n) hc.ge
  have he : Function.Bijective e :=
    ⟨Ideal.quotientMap_injective' (H := hc.ge) hc.le, Ideal.quotientMap_surjective (H := hc.ge) hs⟩
  exact (AlgEquiv.ofBijective e he).toLinearEquiv.finrank_eq

theorem finrank_quot_kerIdeal_eq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G Q : PDivGroup p k) (m n : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G),
    q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → m ≤ n →
      Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) = Module.finrank k (G.A m ⧸ kerIdeal (q.app m)) := by
  intro p _ k _ _ G Q m n q q' h hmn
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih => exact (finrank_quot_kerIdeal_succ p k G Q m n q q' h hmn).trans ih

end GlobalTheory.Dieu
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

noncomputable section

namespace GlobalTheory.PDivGroup

theorem cotMap_comp_eq_zero_of_kerIdeal_le {k A B C : Type} [Field k] [CommRing A] [CommRing B]
    [CommRing C] [Bialgebra k A] [Bialgebra k B] [Bialgebra k C] (g : B →ₐc[k] A)
    (π : A →ₐc[k] C) (h : kerIdeal g ≤ RingHom.ker π) (x : Cot k B) :
    cotMap π (cotMap g x) = 0 := by
  rw [← LinearMap.comp_apply, ← cotMap_comp]
  obtain ⟨b, rfl⟩ := AugCot.d_surjective _ x
  rw [cotMap_d]
  have h' := (kerIdeal_le_ker_iff g (π : A →ₐ[k] C)).1 h b
  change dUnit (R := k) ((π : A →ₐ[k] C) (g b)) = 0
  rw [h']
  exact AugCot.d_algebraMap _ _

theorem cot_kernel_eq_coker_omegaMap : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H) (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (π : G.A 1 →ₐc[k] C), Function.Surjective π → (kerIdeal (q.app 1) ≤ RingHom.ker π → ∀ w ∈ LinearMap.range (omegaMap G H q), cotMap π (w.1 1) = 0) ∧ (RingHom.ker π ≤ kerIdeal (q.app 1) ⊔ augIdeal k (G.A 1) ^ 2 → kerIdeal (q.app 1) ≤ RingHom.ker π → Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) = Module.finrank k (Cot k C)) ∧ ∀ (H' : PDivGroup p k) (f : G ⟶ H'), (∀ w ∈ LinearMap.range (omegaMap G H' f), cotMap π (w.1 1) = 0) → cotMap (π.comp (f.app 1)) = 0 := by
  intro p _ k _ _ G H q C _ _ _ _ π hπ
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have part1 : kerIdeal (q.app 1) ≤ RingHom.ker π →
      ∀ w ∈ LinearMap.range (omegaMap G H q), cotMap π (w.1 1) = 0 := by
    rintro h w ⟨v, rfl⟩
    exact cotMap_comp_eq_zero_of_kerIdeal_le (q.app 1) π h (v.1 1)
  refine ⟨part1, fun h1 h2 => ?_, fun H' f hf => ?_⟩
  ·
    let Φ : G.omega →ₗ[k] Cot k C := cotMap π ∘ₗ G.omegaLevel 1
    have hΦ : Function.Surjective Φ :=
      (cotMap_surjective hπ).comp (G.omegaLevel_one_bijective hp).2
    have hker : LinearMap.ker Φ = LinearMap.range (omegaMap G H q) := by
      ext w
      rw [LinearMap.mem_ker]
      constructor
      · intro hw
        have hw' : AugCot.map (π : G.A 1 →ₐ[k] C) (BialgHomClass.counitAlgHom_comp π) (w.1 1) = 0 :=
          hw
        obtain ⟨x, hx⟩ := (AugCot.exact_kerMap_map (π : G.A 1 →ₐ[k] C)
          (BialgHomClass.counitAlgHom_comp π) hπ (w.1 1)).1 hw'
        have hx2 : dUnit (R := k) (x : G.A 1) = w.1 1 := by
          rw [← hx]; exact (AugCot.kerMap_apply _ _ x).symm
        have hxm : (x : G.A 1) ∈ kerIdeal (q.app 1) ⊔ augIdeal k (G.A 1) ^ 2 := h1 x.2
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hxm
        have hz0 : dUnit (R := k) z = 0 := by
          have hzI : z ∈ augIdeal k (G.A 1) := Ideal.pow_le_self two_ne_zero hz
          have hεz : counitAlgHom k (G.A 1) z = 0 := hzI
          rw [dUnit, AugCot.d_eq_zero_iff, hεz, map_zero, sub_zero]
          exact hz
        obtain ⟨u, hu⟩ := dUnit_mem_range_of_mem_kerIdeal (q.app 1) hy
        obtain ⟨v, rfl⟩ := (H.omegaLevel_one_bijective hp).2 u
        refine ⟨v, (G.omegaLevel_one_bijective hp).1 ?_⟩
        change cotMap (q.app 1) (H.omegaLevel 1 v) = w.1 1
        rw [hu, ← hx2, ← hyz]
        change dUnit (R := k) y = dUnit (R := k) (y + z)
        rw [show dUnit (R := k) (y + z) = dUnit (R := k) y + dUnit (R := k) z from map_add _ y z, hz0, add_zero]
      · intro hw
        exact part1 h2 w hw
    rw [← hker]
    exact (Φ.quotKerEquivOfSurjective hΦ).finrank_eq
  · rw [cotMap_comp]
    refine LinearMap.ext fun u => ?_
    obtain ⟨v, rfl⟩ := (H'.omegaLevel_one_bijective hp).2 u
    exact hf _ ⟨v, rfl⟩

end GlobalTheory.PDivGroup
end
end

section

open TensorProduct Coalgebra Bialgebra WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory

namespace PDivGroup

theorem convPow_prime_apply_pow_prime (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p) (a ^ p) = χ (mulBy R (G.A n) p a) ^ p := by
  let A := G.A n
  let S := ULift.{0} R
  let σ : R →+* S := ULift.ringEquiv.symm.toRingHom.comp (frobRing h)
  let : Algebra R S := σ.toAlgebra
  let : Module R S := Algebra.toModule
  let : SMul R S := Algebra.toSMul
  have hA : (p : A) = 0 := natCast_eq_zero_of_algebra h A
  -- With Frobenius acting on the target scalars, precomposition by the pth power is linear.
  let pullPow (φ : CartierDual R A) : WithConv (A →ₗ[R] S) := toConv
    { toFun := fun x => ULift.up (φ (x ^ p))
      map_add' := fun x y => by
        change ULift.up (φ.ofConv ((x + y) ^ p)) =
          ULift.up (φ.ofConv (x ^ p) + φ.ofConv (y ^ p))
        rw [← frobRing_apply hA (x + y), map_add, map_add, frobRing_apply, frobRing_apply]
      map_smul' := fun r x => by
        change ULift.up (φ.ofConv ((r • x) ^ p)) = r • ULift.up (φ.ofConv (x ^ p))
        rw [smul_pow, φ.ofConv.map_smul, Algebra.smul_def (R := R) (A := S)]
        change ULift.up (r ^ p * φ.ofConv (x ^ p)) =
          ULift.up (frobRing h r * φ.ofConv (x ^ p))
        rw [frobRing_apply] }
  let pull : CartierDual R A →* WithConv (A →ₗ[R] S) :=
    { toFun := pullPow
      map_one' := WithConv.ext (LinearMap.ext fun x => by
        change ULift.up ((1 : CartierDual R A) (x ^ p)) = (1 : WithConv (A →ₗ[R] S)) x
        rw [LinearMap.convOne_apply, LinearMap.convOne_apply, counit_pow]
        change ULift.up (counit (R := R) x ^ p) = ULift.up (frobRing h (counit x))
        rw [frobRing_apply])
      map_mul' := fun φ ψ => WithConv.ext (LinearMap.ext fun x => by
        let d := Coalgebra.Repr.arbitrary R x
        let dPow : Coalgebra.Repr R (x ^ p) (A × A) :=
          ⟨d.index, fun i => d.left i ^ p, fun i => d.right i ^ p, by
            rw [comul_pow, ← d.eq,
              ← frobRing_apply (natCast_eq_zero_of_algebra h (A ⊗[R] A)), map_sum]
            simp only [frobRing_apply, Algebra.TensorProduct.tmul_pow]⟩
        change ULift.up ((φ * ψ) (x ^ p)) = (pullPow φ * pullPow ψ) x
        rw [dPow.convMul_apply, d.convMul_apply]
        exact map_sum ULift.ringEquiv.symm (fun i => φ (d.left i ^ p) * ψ (d.right i ^ p)) d.index) }
  obtain ⟨s, hs⟩ := exists_dualSystem R A
  have hmul : mulBy R A p a = ∑ i ∈ s, (i.1 ^ p) a • i.2 ^ p := by
    have he := BialgHom.toLinearMap_convPow (toConv (BialgHom.id R A)) p
    exact (congrArg (fun f : WithConv (A →ₗ[R] A) => f a) he).trans
      (convPow_prime_apply h s Prod.fst Prod.snd LinearMap.id (fun x => (hs x).symm) a)
  let f := (pull χ).ofConv
  have hf (x : A) : f x = ∑ i ∈ s, i.1 x • f i.2 := by
    simpa only [map_sum, map_smul] using congrArg f (hs x).symm
  let g : A →ₗ[R] S := (Algebra.linearMap R S).comp χ.ofConv
  have hg (x : A) : f x ^ p = g (x ^ p) := by
    change ULift.up (χ (x ^ p) ^ p) = ULift.up (frobRing h (χ (x ^ p)))
    rw [frobRing_apply]
  have e : pull (χ ^ p) a = g (mulBy R A p a) := by
    rw [map_pow]
    change (toConv f ^ p) a = _
    rw [convPow_prime_apply h s Prod.fst (fun i => f i.2) f hf a, hmul, map_sum]
    simp only [map_smul, hg]
  exact (congrArg ULift.down e).trans (frobRing_apply h _)

theorem convPow_primePow_apply_pow (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r := by
  induction r generalizing a with
  | zero =>
    simp only [pow_zero, pow_one]
    rw [mulBy, pow_one]
    rfl
  | succ r ih =>
    rw [pow_succ, pow_mul, pow_mul, convPow_prime_apply_pow_prime p R h G n, map_pow, ih,
      mulBy_mulBy, ← pow_mul, mul_comm (p ^ r) p, ← pow_succ']

end PDivGroup

end GlobalTheory
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.valuation_bound_multiplier_sqrt_neg_d : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (σ p : ℂ), d.Prime → 4 < d → l ≠ d → Sz l lam 0 (12 * p) → Sz l lam 0 (-2 * (d : ℂ) * σ + ((d : ℂ) + 1) * p) → (l = 3 → d % 3 = 2) → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else 0) σ := by
  first | exact @GlobalTheory.SzMult.main | exact GlobalTheory.SzMult.main | (intros; apply GlobalTheory.SzMult.main <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.valuation_bound_three_inert : ∀ [Fact (Nat.Prime 3)] (lam : algebraicClosure ℚ ℂ →+* ℂ_[3]) (d : ℕ) (w σ p : ℂ), d % 3 = 1 → w ^ 2 = -(d : ℂ) → Sz 3 lam 0 (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz 3 lam 0 (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p) → Sz 3 lam 0 σ := by
  first | exact @GlobalTheory.ArithThreeInert.main | exact GlobalTheory.ArithThreeInert.main | (intros; apply GlobalTheory.ArithThreeInert.main <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal

theorem _root_.GlobalTheory.T.latticeValueIntegrality_ramified_of_expansion : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → Expansion → LatIntRam := by
  first | exact @GlobalTheory.LatValRam.latIntRam | exact GlobalTheory.LatValRam.latIntRam | (intros; apply GlobalTheory.LatValRam.latIntRam <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.inner_fockOmegaAction_adjoint_lines : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι → ∀ (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P Q : Pol p q r s), inner ℂ (ι (omAct p q r s Z P)) (ι Q) = inner ℂ (ι P) (ι (omAct p q r s (Matrix.kroneckerMap (· * ·) (Jm p q) (Jm r s) * Z.conjTranspose * Matrix.kroneckerMap (· * ·) (Jm p q) (Jm r s)) Q)) := by
  first | exact @GlobalTheory.FockAdjLines.inner_omAct_adj | exact GlobalTheory.FockAdjLines.inner_omAct_adj | (intros; apply GlobalTheory.FockAdjLines.inner_omAct_adj <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fischerDecomposition_fockNoncompactParts : ∀ (p q r s d : ℕ), (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm2 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm1 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (jointHarm p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨ ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) := by
  first | exact @GlobalTheory.FischerParts.fischer_parts | exact GlobalTheory.FischerParts.fischer_parts | (intros; apply GlobalTheory.FischerParts.fischer_parts <;> assumption)
end
