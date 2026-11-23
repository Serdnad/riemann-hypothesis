module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle173
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Localization.Integral

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HilbAff.IdealDet
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem comm_fst {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) (a : A) :
    ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)) =
    ((pullback.snd (str A B) g).app U).hom (secAlg A g U a) := by
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a) =
      (str A B).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) :=
    congrArg (fun f => f.hom a) h1
  have key : (str A B).appTop ≫ (pullback.fst (str A B) g).appLE ⊤
      ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) =
      g.appLE ⊤ U (by simp) ≫ (pullback.snd (str A B) g).app U := by
    calc _ = (pullback.fst (str A B) g ≫ str A B).appLE ⊤
          ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) :=
          (Scheme.Hom.comp_appLE _ _ _ _ _).symm
      _ = (pullback.snd (str A B) g ≫ g).appLE ⊤
          ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) :=
          appLE_eq_of_eq (by simp [pullback.condition]) _ _ _ _
      _ = _ := by
          rw [Scheme.Hom.app_eq_appLE]; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [h2, secAlg, RingHom.comp_apply, ← CommRingCat.comp_apply, key, CommRingCat.comp_apply]

def theta {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) :
    letI := (secAlg A g U).toAlgebra
    Γ(T, U) ⊗[A] B →+* Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  (Algebra.TensorProduct.lift
    { toRingHom := ((pullback.snd (str A B) g).app U).hom, commutes' := fun (_ : A) => rfl }
    { toRingHom := (((pullback.fst (str A B) g).appLE ⊤ _ (by simp)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom),
      commutes' := fun a => comm_fst A B g U a }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem theta_tmul {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) (c : Γ(T, U)) (b : B) :
    (letI := (secAlg A g U).toAlgebra
     theta A B g U (c ⊗ₜ[A] b) = ((pullback.snd (str A B) g).app U).hom c *
       ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
         ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) := by
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem kappa_apply {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) :
    (letI := (secAlg A g U).toAlgebra
     ∀ x : Γ(T, U) ⊗[A] B, kappa A B g I U x =
       (I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U)).hom (theta A B g U x)) := by
  letI := (secAlg A g U).toAlgebra
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]; rfl
  | tmul c b =>
    change ((I.subschemeι ≫ pullback.snd (str A B) g).app U).hom c *
      ((I.subschemeι ≫ pullback.fst (str A B) g).appLE ⊤
        ((I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = _
    rw [theta_tmul, map_mul]
    have e : (pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) ≫
        I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U) =
        (I.subschemeι ≫ pullback.fst (str A B) g).appLE ⊤ ((I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U)
          (by simp) := by
      rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    congr 1
    rw [← e]; rfl

theorem theta_surjective {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens)
    (hU : IsAffineOpen U) : Function.Surjective (theta A B g U) := by
  letI := (secAlg A g U).toAlgebra
  have hP := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE (IsPullback.of_hasPullback (str A B) g)
    inferInstance (isAffineOpen_top _) hU le_top (by simp)
  let R : CommRingCat.{0} := CommRingCat.of (Γ(T, U) ⊗[A] B)
  let k : Γ(T, U) ⟶ R := CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (S := A)).toRingHom
  let h : Γ(Spec (CommRingCat.of B), (str A B) ⁻¹ᵁ ⊤) ⟶ R :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := Γ(T, U))).toRingHom
  have w : (str A B).app ⊤ ≫ h = g.appLE ⊤ U le_top ≫ k := by
    ext x
    obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (CommRingCat.of A)).inv a = x :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom x, by simp⟩
    have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))
    have h2 : (str A B).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap A B a) :=
      (congrArg (fun f => f.hom a) h1).symm
    change (Algebra.TensorProduct.includeRight (R := A) (A := Γ(T, U)))
      ((Scheme.ΓSpecIso (CommRingCat.of B)).hom ((str A B).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
      (Algebra.TensorProduct.includeLeft (S := A)) (secAlg A g U a)
    rw [h2, Iso.inv_hom_id_apply]
    exact ((Algebra.TensorProduct.includeRight).commutes a).trans
      ((Algebra.TensorProduct.includeLeft (S := A)).commutes a).symm
  let ψ := hP.desc h k w
  have hθ : ψ ≫ CommRingCat.ofHom (theta A B g U) = 𝟙 _ := by
    apply hP.hom_ext
    · rw [hP.inl_desc_assoc, Category.comp_id]
      ext z
      change theta A B g U ((1 : Γ(T, U)) ⊗ₜ[A] ((Scheme.ΓSpecIso (CommRingCat.of B)).hom z)) = _
      have e : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of B)).hom z) = z :=
        Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of B)) z
      rw [theta_tmul, map_one, one_mul, e]
      rfl
    · rw [hP.inr_desc_assoc, Category.comp_id]
      ext c
      change theta A B g U (c ⊗ₜ[A] (1 : B)) = _
      rw [theta_tmul, map_one, map_one, mul_one]
  intro y
  exact ⟨ψ y, congrArg (fun F => F.hom y) hθ⟩

theorem eq_of_ker_kappa_eq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I₁ I₂ : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData),
    (∀ U : T.affineOpens, RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₁ U) =
      RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₂ U)) → I₁ = I₂ := by
  intro A B _ _ _ T g I₁ I₂ h
  haveI : IsAffineHom (pullback.snd (str A B) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback (str A B) g)
      (inferInstance : IsAffineHom (str A B))
  let W : T.affineOpens → (pullback (str A B) g).affineOpens :=
    fun U => ⟨pullback.snd (str A B) g ⁻¹ᵁ U, U.2.preimage _⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top W ?_ ?_
  · exact (pullback.snd (str A B) g).iSup_preimage_eq_top (iSup_affineOpens_eq_top T)
  · intro U
    letI := (secAlg A g U).toAlgebra
    have key : ∀ I : (pullback (str A B) g).IdealSheafData,
        I.ideal (W U) = Ideal.map (theta A B g U) (RingHom.ker (kappa A B g I U)) := by
      intro I
      have e : RingHom.ker (kappa A B g I U) = Ideal.comap (theta A B g U) (I.ideal (W U)) := by
        ext x
        rw [RingHom.mem_ker, Ideal.mem_comap, ← I.ker_subschemeι_app (W U), RingHom.mem_ker,
          kappa_apply]
        rfl
      rw [e, Ideal.map_comap_of_surjective _ (theta_surjective A B g U U.2)]
    rw [key, key, h U]

end GlobalTheory.HilbAff.IdealDet
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem good_xI : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) {r : ℕ} (v : Fin r → B), LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)) → Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤ → GlobalTheory.HilbAff.Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (GlobalTheory.HilbAff.xI A B C J) := by
  intro A B C _ _ _ _ _ J r v hli hsp
  let bas : Module.Basis (Fin r) C ((C ⊗[A] B) ⧸ J) := Module.Basis.mk hli hsp.ge
  haveI : Module.Free C ((C ⊗[A] B) ⧸ J) := Module.Free.of_basis bas
  haveI : Module.Finite C ((C ⊗[A] B) ⧸ J) := Module.Finite.of_basis bas
  have hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp
      (Algebra.TensorProduct.comm A B C).toRingHom) :=
    (Ideal.Quotient.mk_surjective).comp (Algebra.TensorProduct.comm A B C).surjective
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp
      (Algebra.TensorProduct.comm A B C).toRingHom))) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  have hsnd : (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp
      (Algebra.TensorProduct.comm A B C).toRingHom)) ≫ (pullbackSpecIso A B C).inv) ≫
      pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap C ((C ⊗[A] B) ⧸ J))) := by
    rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  refine good_ker A B r _ _ ?_ ?_ ?_
  · rw [hsnd]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · rw [hsnd]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  · intro y
    rw [hsnd]
    refine (Scheme.Hom.finrank_SpecMap_algebraMap C ((C ⊗[A] B) ⧸ J) y).trans ?_
    haveI : Nontrivial C := by
      let p : PrimeSpectrum C := y
      refine ⟨⟨0, 1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩⟩
      rw [← h]; exact p.asIdeal.zero_mem
    rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis bas, Fintype.card_fin]
    rfl

end GlobalTheory.HilbAff
end

section

open IsLocalRing



namespace GlobalTheory

open Polynomial TensorProduct

theorem tensor_exists_smul_eq_eval₂ (S K L : Type) [CommRing S] [IsDomain S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] (π : S) (e : ℕ) (D : Type) [CommRing D]
    [Algebra S D] (φ : D ≃ₐ[S] AdjoinRoot (X ^ e - C π)) (z : TensorProduct S D L) :
    ∃ (f : Polynomial (integralClosure S L)) (s : S), s ≠ 0 ∧
      algebraMap S (TensorProduct S D L) s * z =
        f.eval₂ ((Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).comp
            (integralClosure S L).val).toRingHom
          (algebraMap D (TensorProduct S D L) (φ.symm (AdjoinRoot.root (X ^ e - C π)))) := by
  set gA : integralClosure S L →ₐ[S] TensorProduct S D L :=
    (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).comp (integralClosure S L).val
  set t := φ.symm (AdjoinRoot.root (X ^ e - C π))
  have hg : ∀ s : S, gA.toRingHom (algebraMap S (integralClosure S L) s) =
      algebraMap S (TensorProduct S D L) s := fun s => gA.commutes s
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | tmul d l =>
    have hl : IsAlgebraic S l :=
      (IsFractionRing.isAlgebraic_iff S K L).2 (Algebra.IsAlgebraic.isAlgebraic l)
    obtain ⟨s, hs, hint⟩ := hl.exists_integral_multiple
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (φ d)
    have hd : d = aeval t p := by
      rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, hp]
      simp [t]
    refine ⟨C ⟨s • l, hint⟩ * p.map (algebraMap S (integralClosure S L)), s, hs, ?_⟩
    rw [eval₂_mul, eval₂_C, eval₂_map]
    have : (gA.toRingHom.comp (algebraMap S (integralClosure S L))) =
        algebraMap S (TensorProduct S D L) := RingHom.ext hg
    rw [this, ← aeval_def]
    have h2 : aeval (algebraMap D (TensorProduct S D L) t) p =
        algebraMap D (TensorProduct S D L) d := by
      rw [hd, aeval_algebraMap_apply]
    rw [h2]
    simp only [gA, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.coe_comp,
      Function.comp_apply, Subalgebra.coe_val, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← Algebra.smul_def, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨f₁, s₁, hs₁, h₁⟩ := hx
    obtain ⟨f₂, s₂, hs₂, h₂⟩ := hy
    refine ⟨C (algebraMap S _ s₂) * f₁ + C (algebraMap S _ s₁) * f₂, s₁ * s₂,
      mul_ne_zero hs₁ hs₂, ?_⟩
    rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_C, eval₂_C, hg, hg, ← h₁, ← h₂, map_mul]
    ring

theorem normalisation_mul_eq_aeval_root (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D]
    (φ : D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π))
    (b : integralClosure D (TensorProduct S D L)) :
    ∃ (f : Polynomial (integralClosure S L)) (s : S), s ≠ 0 ∧
      algebraMap S (integralClosure D (TensorProduct S D L)) s * b =
        Polynomial.aeval (algebraMap D (integralClosure D (TensorProduct S D L))
          (φ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)))) f := by
  obtain ⟨f, s, hs, h⟩ := tensor_exists_smul_eq_eval₂ S K L π e D φ (b : TensorProduct S D L)
  refine ⟨f, s, hs, Subtype.ext ?_⟩
  rw [aeval_def]
  have hc := Polynomial.hom_eval₂ f
    (algebraMap (integralClosure S L) (integralClosure D (TensorProduct S D L)))
    (integralClosure D (TensorProduct S D L)).val.toRingHom
    (algebraMap D (integralClosure D (TensorProduct S D L))
      (φ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π))))
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Subalgebra.coe_val] at hc
  rw [hc]
  convert h using 2 <;> first | rfl | exact RingHom.ext fun _ => rfl
end GlobalTheory
end

section

open IsLocalRing



namespace GlobalTheory

theorem integralClosure_tensor_localization_injective : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    Function.Injective
      (@algebraMap (Localization.AtPrime (Q.under (integralClosure S L))) (Localization.AtPrime Q)
        _ _ (Localization.AtPrime.algebraOfLiesOver (Q.under (integralClosure S L)) Q)) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ _ _ _ _ _ Q _
  set P := Q.under (integralClosure S L) with hP
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
  have h1 : algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)
      (algebraMap (integralClosure S L) (Localization.AtPrime P) x) = 0 := by
    rw [← IsLocalization.mk'_spec (Localization.AtPrime P) x s, map_mul, hz, zero_mul]
  have h2 : algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
      (algebraMap (integralClosure S L) (integralClosure D (TensorProduct S D L)) x) = 0 := by
    rw [← h1]
    exact (Localization.localRingHom_to_map _ _ _ _ x).symm
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl (Localization.AtPrime Q) _).1 h2
  have hx : x = 0 := by
    by_contra hx0
    have hxL : (x : L) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have ht' : ((t : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) *
        ((1 : D) ⊗ₜ[S] (x : L)) = 0 := by
      have := congrArg (fun y : integralClosure D (TensorProduct S D L) => (y : TensorProduct S D L)) ht
      simpa [algebraMap_integralClosure_tensor_eq] using this
    have hu : ((1 : D) ⊗ₜ[S] (x : L)) * ((1 : D) ⊗ₜ[S] ((x : L)⁻¹)) = 1 := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hxL]
      rfl
    have ht0 : ((t : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) = 0 := by
      have := congrArg (· * ((1 : D) ⊗ₜ[S] ((x : L)⁻¹))) ht'
      simpa [mul_assoc, hu] using this
    have : (t : integralClosure D (TensorProduct S D L)) = 0 := Subtype.ext ht0
    exact t.2 (this ▸ Q.zero_mem)
  subst hx
  exact IsLocalization.mk'_zero _

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory.ZarhinFam

theorem zpow_finset_sum' {G ι : Type} [CommGroup G] (a : G) (s : Finset ι) (e : ι → ℤ) :
    a ^ (∑ k ∈ s, e k) = ∏ k ∈ s, a ^ e k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.prod_insert hb, _root_.zpow_add, ih]

theorem prod_prod_zpow_mul {G : Type} [CommGroup G] (P Q : Matrix (Fin 4) (Fin 4) ℤ) (w : Fin 4 → G)
    (a : Fin 4) : ∏ k, (∏ i, w i ^ Q k i) ^ P a k = ∏ i, w i ^ (P * Q) a i := by
  simp_rw [← Finset.prod_zpow, ← _root_.zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, zpow_finset_sum']
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem prod_zpow_smul_one {G : Type} [CommGroup G] (c : ℤ) (w : Fin 4 → G) (a : Fin 4) :
    ∏ i, w i ^ (c • (1 : Matrix (Fin 4) (Fin 4) ℤ)) a i = w a ^ c := by
  simp [Matrix.smul_apply, Matrix.one_apply]

theorem zarhin_kernel_trivial : ∀ (d : ℕ) (GA GB : Type) [CommGroup GA] [CommGroup GB] (f : GA →* GB) (g : GB →* GA), 0 < d → (∀ a, g (f a) = a ^ d) → ∀ (u : Fin 4 → GA) (v : Fin 4 → GB), (∀ i, f (u i) * ∏ j, v j ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ j, f (∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i) * v j ^ d = 1) → ((∀ j, v j = 1) → ∀ j, ∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ i, u i = 1) ∧ ∀ j, v j = 1 := by
  intro d GA GB _ _ f g hd hgf u v hA hB hC
  have hxx : quat d * (quat d)ᵀ = (((d - 1 : ℕ) : ℤ)) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
    quat_mul_transpose d
  have hxtx : (quat d)ᵀ * quat d = (((d - 1 : ℕ) : ℤ)) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
    quat_transpose_mul d
  have hd1 : d = (d - 1) + 1 := by omega
  have hv : ∀ k, v k = 1 := by
    intro k
    have E : ∏ i, (f (u i) * ∏ j, v j ^ quat d j i) ^ quat d k i = 1 := by
      simp [hA]
    rw [Finset.prod_congr rfl fun i _ => mul_zpow (f (u i)) (∏ j, v j ^ quat d j i) (quat d k i),
      Finset.prod_mul_distrib] at E
    have E2 : ∏ i, (∏ j, v j ^ (quat d)ᵀ i j) ^ quat d k i = v k ^ (((d - 1 : ℕ) : ℤ)) := by
      rw [prod_prod_zpow_mul, hxx, prod_zpow_smul_one]
    simp only [Matrix.transpose_apply] at E2
    have hF : f (∏ i, u i ^ quat d k i) = ∏ i, f (u i) ^ quat d k i := by
      simp [map_prod, map_zpow]
    rw [E2, ← hF, zpow_natCast] at E
    have hBk := hB k
    rw [show v k ^ d = v k ^ (d - 1) * v k by rw [← pow_succ, ← hd1], ← mul_assoc, E, one_mul] at hBk
    exact hBk
  refine ⟨?_, hv⟩
  have hxu := hC hv
  intro l
  have E : ∏ k, (∏ i, u i ^ quat d k i) ^ (quat d)ᵀ l k = 1 := by
    simp [hxu]
  rw [prod_prod_zpow_mul, hxtx, prod_zpow_smul_one, zpow_natCast] at E
  have hfu : f (u l) = 1 := by
    have h := hA l
    simpa [hv] using h
  have hdu : u l ^ d = 1 := by
    rw [← hgf, hfu, map_one]
  rw [show u l ^ d = u l ^ (d - 1) * u l by rw [← pow_succ, ← hd1], E, one_mul] at hdu
  exact hdu

end GlobalTheory.ZarhinFam
end

section

noncomputable section

open Matrix

namespace GlobalTheory.ZarhinFam

def polUnit (d : ℕ) : ord d :=
  ⟨single (Sum.inl 0) (Sum.inr 0) 1, fun i j => by simp [single]⟩

@[simp] theorem polUnit_coe (d : ℕ) :
    ((polUnit d : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) = single (Sum.inl 0) (Sum.inr 0) 1 :=
  rfl

end GlobalTheory.ZarhinFam
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

theorem eq_of_chartHom_eq {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type}
    [CommRing S] (c c' : Sp S ⟶ Y) (hc : c ⁻¹ᵁ V = ⊤) (hc' : c' ⁻¹ᵁ V = ⊤)
    (e : ∀ x, chartHom V c hc x = chartHom V c' hc' x) : c = c' := by
  have e₁ : c.appLE V ⊤ hc.ge = c'.appLE V ⊤ hc'.ge := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of S)).hom]
    exact CommRingCat.hom_ext (RingHom.ext e)
  have a := IsAffineOpen.SpecMap_appLE_fromSpec c hV (isAffineOpen_top (Sp S)) hc.ge
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec c' hV (isAffineOpen_top (Sp S)) hc'.ge
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm

theorem combIn_unique : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V → ∀ (S : Type) [CommRing S] (ι : Type) [Fintype ι]
    (u c c' : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    GlobalTheory.SecGlue.IsCombIn V u c w a → GlobalTheory.SecGlue.IsCombIn V u c' w a → c = c' := by
  intro Y V hV S _ ι _ u c c' w a h h'
  obtain ⟨hu, hc, hw, e⟩ := h
  obtain ⟨hu', hc', hw', e'⟩ := h'
  refine eq_of_chartHom_eq hV c c' hc hc' fun x => ?_
  rw [e x, e' x]

end GlobalTheory.SecGlue
end
end
