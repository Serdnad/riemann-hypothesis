module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoequifiberedDiagramMap
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpecHomCompCoaction
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomEqOneOfNilpotent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
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
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.CategoryTheory.EffectiveEpi.Comp
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AbLaw

def finSecPullId {X : Scheme.{0}} {M : LB X} (s : LB.Sec M) : LB.Sec (M.pull (𝟙 X)) where
  f := fun j => rs X (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) j PUnit.unit) (s.f (j PUnit.unit))
  compat := fun i j => by
    have h := congrArg (rs X (inf_le_inf (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) i PUnit.unit)
      (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) j PUnit.unit) :
        (M.pull (𝟙 X)).U i ⊓ (M.pull (𝟙 X)).U j ≤ M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)))
      (s.compat (i PUnit.unit) (j PUnit.unit))
    rw [map_mul] at h
    erw [rs_rs, rs_rs] at h
    erw [rs_rs, rs_rs, h]
    congr 1
    unfold LB.pull LB.LinComb
    dsimp only
    rw [Fintype.prod_unique, zpow_one]
    rfl

theorem finSec_eq_zero_of_cover {X : Scheme.{0}} {I : Type} (V : I → X.Opens) (hV : ⨆ i, V i = ⊤)
    {U : X.Opens} (x : Γ(X, U)) (hx : ∀ i, rs X (inf_le_left : U ⊓ V i ≤ U) x = 0) : x = 0 := by
  refine X.sheaf.eq_of_locally_eq' (fun i => U ⊓ V i) U (fun i => homOfLE inf_le_left) ?_ x 0 ?_
  · rw [← inf_iSup_eq, hV, inf_top_eq]
  · intro i
    exact (hx i).trans (map_zero (rs X (inf_le_left : U ⊓ V i ≤ U))).symm

theorem Perf.exists_relation {X : Scheme.{0}} {K : Type} [Field K] {f : X ⟶ Spec (CommRingCat.of K)}
    {M : LB X} (Q : Perf f M) (s : Fin (Q.a + 1) → LB.Sec M) :
    ∃ c : Fin (Q.a + 1) → K, c ≠ 0 ∧ ∀ i, ∑ k, cst f (M.U i) (c k) * (s k).f i = 0 := by
  have hpb : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id K))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.id_horiz f
  obtain ⟨E, hE⟩ := Q.sec K (RingHom.id K) X (𝟙 X) f hpb
  let v : Fin (Q.a + 1) → Fin Q.a → K := fun k => (E.symm (finSecPullId (s k))).1
  have hv : ∀ k j, rs X (Q.le j) ((s k).f (Q.ch j)) = ∑ l, cst f (Q.W j) (v k l) * Q.u l j := by
    intro k j
    have h := hE (E.symm (finSecPullId (s k))) j
    rw [Equiv.apply_symm_apply] at h
    refine Eq.trans ?_ h
    exact (rs_rs _ _ _).symm
  have hdep : ¬ LinearIndependent K v := by
    intro h
    have := h.fintype_card_le_finrank
    simp at this
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨c, hc, k₀, hk₀⟩ := hdep
  have hc' : ∀ l, ∑ k, c k * v k l = 0 := fun l => by
    have := congrFun hc l
    simpa [Finset.sum_apply] using this
  have hW : ∀ j, ∑ k, cst f (Q.W j) (c k) * rs X (Q.le j) ((s k).f (Q.ch j)) = 0 := by
    intro j
    simp only [hv, Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_comm]

    simp only [← Finset.sum_mul, ← map_sum, hc', map_zero, zero_mul, Finset.sum_const_zero]
  refine ⟨c, fun h => hk₀ (congrFun h k₀), fun i => ?_⟩
  refine finSec_eq_zero_of_cover Q.W Q.cover _ fun j => ?_
  have h₁ : ∀ k, rs X (inf_le_left : M.U i ⊓ Q.W j ≤ M.U i) ((s k).f i) =
      rs X (inf_le_inf le_rfl (Q.le j) : M.U i ⊓ Q.W j ≤ M.U i ⊓ M.U (Q.ch j)) (M.g i (Q.ch j)).val *
        rs X (inf_le_right : M.U i ⊓ Q.W j ≤ Q.W j) (rs X (Q.le j) ((s k).f (Q.ch j))) := by
    intro k
    have h := congrArg (rs X (inf_le_inf le_rfl (Q.le j) : M.U i ⊓ Q.W j ≤ M.U i ⊓ M.U (Q.ch j)))
      ((s k).compat i (Q.ch j))
    rw [map_mul] at h
    simp only [rs_rs] at h ⊢
    exact h
  have h₂ := congrArg (rs X (inf_le_right : M.U i ⊓ Q.W j ≤ Q.W j)) (hW j)

  simp only [map_sum, map_mul, rs_cst, map_zero] at h₂

  simp only [map_sum, map_mul, rs_cst, h₁]
  simp only [mul_left_comm (cst f _ _), ← Finset.mul_sum, h₂, mul_zero]

theorem sections_finite_of_perf
    (hperf : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)),
      Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M))
    (hva : ∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S)
      (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)),
      IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)),
        (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s)
    (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left)
    (hM : M.IsLB) :
    ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧
      ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0 := by
  obtain ⟨N, -, m, σ, hLB, hσ⟩ := hva _ P K (𝟙 _) P.A.left (𝟙 _) P.A.hom (IsPullback.id_horiz _)
  have hsm : Smooth P.A.hom := by
    haveI := P.smoothDim
    exact SmoothOfRelativeDimension.smooth P.g _
  obtain ⟨Q⟩ := hperf K P.A.left P.A.hom hsm ⟨_, hLB, m, σ, hσ⟩ M hM
  refine ⟨Q.a + 1, fun s => ?_⟩
  obtain ⟨c, hc, h⟩ := Q.exists_relation s
  refine ⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c k), fun h0 => hc ?_, h⟩
  funext k
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
  exact hinj ((congrFun h0 k).trans (map_zero _).symm)

end GlobalTheory.AbLaw
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineQuotient

set_option backward.isDefEq.respectTransparency false


open TensorProduct Algebra.TensorProduct in
lemma exists_coaction {R Λ : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ]
    {A : Over (Spec (CommRingCat.of R))} [GrpObj A] (i : specOver R Λ ⟶ A) {Y : Scheme.{0}}
    (f : A.left ⟶ Y) (g : (specOver R Λ ⊗ A).left ⟶ Y)
    (ha : ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A).left ≫ f = g)
    (hp : (snd (specOver R Λ) A).left ≫ f = g) (U : Y.Opens) (hf : IsAffineOpen (f ⁻¹ᵁ U))
    (hg : IsAffineOpen (g ⁻¹ᵁ U)) :
    ∃ (_ : Algebra R Γ(A.left, f ⁻¹ᵁ U)) (v : specOver R Γ(A.left, f ⁻¹ᵁ U) ⟶ A) (_ : Mono v)
      (ρ : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R] Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)
      (e : Γ((specOver R Λ ⊗ A).left, g ⁻¹ᵁ U) ⟶ .of (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)) (_ : IsIso e),
      specHom ρ ≫ v = (specHom includeRight ≫ i) * (specHom includeLeft ≫ v) ∧
      pullOver f g _ ha U ≫ e = CommRingCat.ofHom ρ.toRingHom ∧
      pullOver f g _ hp U ≫ e = CommRingCat.ofHom (includeLeft : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R]
        Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ).toRingHom := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hf.fromSpec ≫ A.hom)
  let : Algebra R Γ(A.left, f ⁻¹ᵁ U) := φ.hom.toAlgebra
  let v : specOver R Γ(A.left, f ⁻¹ᵁ U) ⟶ A := Over.homMk hf.fromSpec hφ.symm
  have : Mono v.left := inferInstanceAs (Mono hf.fromSpec)
  have P₁ : IsPullback (Spec.map (pullOver f g _ hp U))
      (hg.fromSpec ≫ (fst (specOver R Λ) A).left) (Spec.map φ) (specOver R Λ).hom := by
    rw [hφ]
    exact (isPullback_pullOver f g _ hp hf hg).paste_vert
      (IsPullback.of_hasPullback (specOver R Λ).hom A.hom).flip
  have P₂ : IsPullback (specHom (includeLeft : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R]
        Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)).left (specHom (includeRight : Λ →ₐ[R]
        Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)).left (Spec.map φ) (specOver R Λ).hom :=
    isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R Γ(A.left, f ⁻¹ᵁ U) Λ)
  obtain ⟨e, he⟩ := Spec.map_surjective (P₂.isoIsPullback _ _ P₁).hom
  have : IsIso (Spec.map e) := by rw [he]; infer_instance
  have : IsIso e := by
    have : IsIso (Scheme.Spec.map e.op) := this
    have := Spec.fullyFaithful.isIso_of_isIso_map e.op
    exact isIso_of_op e
  have h₁ := P₂.isoIsPullback_hom_fst _ _ P₁
  have h₂ := P₂.isoIsPullback_hom_snd _ _ P₁
  rw [← he] at h₁ h₂
  have hw : (Spec.map e ≫ hg.fromSpec) ≫ (specOver R Λ ⊗ A).hom =
      (specOver R (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)).hom := by
    rw [← Over.w (fst (specOver R Λ) A), Category.assoc, reassoc_of% h₂, Over.w]
  let k : specOver R (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ) ⟶ specOver R Λ ⊗ A :=
    Over.homMk (Spec.map e ≫ hg.fromSpec) hw
  have k₁ : k ≫ fst _ _ = specHom includeRight := by
    ext1
    rw [← h₂]
    exact Category.assoc ..
  have k₂ : k ≫ snd _ _ = specHom includeLeft ≫ v := by
    ext1
    rw [Over.comp_left, Over.comp_left, ← h₁]
    change (Spec.map e ≫ hg.fromSpec) ≫ _ = (Spec.map e ≫ _) ≫ hf.fromSpec
    rw [Category.assoc, Category.assoc, SpecMap_pullOver f g _ hp hf hg]
  have k₃ : (k ≫ ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A)).left =
      Spec.map (pullOver f g _ ha U ≫ e) ≫ hf.fromSpec := by
    rw [Spec.map_comp, Category.assoc, SpecMap_pullOver f g _ ha hf hg]
    exact Category.assoc ..
  have h₃ : φ ≫ pullOver f g _ ha U ≫ e =
      CommRingCat.ofHom (algebraMap R (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, ← Category.assoc, ← k₃, Over.w]
    rfl
  let ρ : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R] Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ :=
    ⟨(pullOver f g _ ha U ≫ e).hom, fun r ↦ congr($h₃ r)⟩
  refine ⟨inferInstance, v, Over.mono_of_mono_left v, ρ, e, this, ?_, rfl, ?_⟩
  · rw [← k₂, ← k₁, Category.assoc, ← comp_mul]
    ext1
    exact k₃.symm
  · apply Spec.map_injective
    rw [Spec.map_comp, h₁]
    rfl

lemma exists_quotient_hopf
    (hq : (∀ (R Λ B : Type) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] TensorProduct R B Λ), (∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b)) → (∀ b, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) → Module.Finite (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ Module.FaithfullyFlat (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ RingHom.ker (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) = Ideal.span {z | ∃ b ∈ AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ), z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}))
    {R Λ : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ]
    [Module.Projective R Λ]
    {A : Over (Spec (CommRingCat.of R))} [GrpObj A] [IsCommMonObj A] (i : specOver R Λ ⟶ A)
    [IsMonHom i] [Mono i] {Y : Over (Spec (CommRingCat.of R))} [IsLocallyNoetherian Y.left]
    (f : A ⟶ Y) [IsFinite f.left]
    (h : ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A) ≫ f = snd (specOver R Λ) A ≫ f) :
    ∃ (Q : Over (Spec (CommRingCat.of R))) (q : A ⟶ Q) (π : Q ⟶ Y), IsFinite π.left ∧
      IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A) (snd (specOver R Λ) A) q q := by
  have : IsAffine (specOver R Λ).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffineHom (specOver R Λ).hom := inferInstance
  have : IsAffineHom (snd (specOver R Λ) A).left :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) (specOver R Λ).hom A.hom this
  have ha : ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A).left ≫ f.left =
    (snd (specOver R Λ) A).left ≫ f.left := congr(($h).left)
  obtain ⟨Q, q, π, h₀, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient f.left _ _ ha _ rfl (fun U ↦ by
    obtain ⟨_, v, _, ρ, e, _, hρ, e₁, e₂⟩ :=
      exists_coaction i f.left _ ha rfl U.1 (U.2.preimage _) (U.2.preimage _)
    have hs := coaction_free i v ρ hρ
    obtain ⟨-, hff, hk⟩ := hq R Λ _ ρ (coaction_assoc i v ρ hρ) (coaction_counit i v ρ hρ) hs
    have hC : invariants f.left _ _ ha _ rfl U.1 = ρ.toRingHom.eqLocus
        (Algebra.TensorProduct.includeLeft : Γ(A.left, f.left ⁻¹ᵁ U.1) →ₐ[R] _).toRingHom := by
      ext x
      rw [mem_invariants, ← (ConcreteCategory.bijective_of_isIso e).1.eq_iff,
        ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e₁, e₂]
      rfl
    rw [hC]
    refine ⟨hff, ?_⟩
    refine (isPushout_equalizer ρ _ hs hk).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso e).symm (by simp) (by simp) ?_ ?_
    · rw [← e₁]; simp
    · rw [← e₂]; simp)
  refine ⟨Over.mk (π ≫ Y.hom), Over.homMk q (by simp [reassoc_of% h₀]), Over.homMk π rfl,
    h₁, h₂, h₃, h₄, ?_⟩
  exact IsPullback.of_map_of_faithful (Over.forget _) h₅

lemma exists_hopfAlgebra (R : Type) [CommRing R] [IsNoetherianRing R]
    (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [IsFinite H.hom] [Flat H.hom] :
    ∃ (Λ : Type) (_ : CommRing Λ) (_ : HopfAlgebra R Λ) (_ : Module.Finite R Λ)
      (_ : Module.Projective R Λ) (e : specOver R Λ ≅ H), IsMonHom e.hom := by
  have : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨⟨Λ⟩, ⟨e⟩⟩ := (essImage_hopfSpec (R := .of R) (G := Grp.mk H)).2 this
  let e' : specOver R Λ ≅ H := (Grp.forget _).mapIso e
  have h₁ : IsFinite (specOver R Λ).hom := by
    rw [← Over.w e'.hom]; infer_instance
  have h₂ : Flat (specOver R Λ).hom := by
    rw [← Over.w e'.hom]; infer_instance
  have : Module.Finite R Λ := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h₁)
  have : Module.Flat R Λ := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h₂)
  have : Module.FinitePresentation R Λ := Module.finitePresentation_of_finite R Λ
  exact ⟨Λ, inferInstance, inferInstance, inferInstance,
    Module.Flat.projective_of_finitePresentation, e', e.hom.hom.isMonHom_hom⟩

end GlobalTheory.AffineQuotient

namespace GlobalTheory

open AffineQuotient


set_option backward.isDefEq.respectTransparency false in
theorem exists_quotient_scheme_of_finite_flat_subgroup :
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [IsCommMonObj H], IsFinite H.hom → Flat H.hom → ∃ N : ℕ, 1 ≤ N ∧ 𝟙 H ^ N = 1) → (∀ (R Λ B : Type) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] TensorProduct R B Λ), (∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b)) → (∀ b, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) → Module.Finite (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ Module.FaithfullyFlat (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ RingHom.ker (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) = Ideal.span {z | ∃ b ∈ AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ), z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Spec (CommRingCat.of R))) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] (i : H ⟶ P.A), IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∃ (Q : Over (Spec (CommRingCat.of R))) (q : P.A ⟶ Q), IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧ IsPullback ((fst H P.A ≫ i) * snd H P.A) (snd H P.A) q q := by
  intro hk hq hm R _ _ P H _ i _ _ _ _
  have := P.isAb.comm
  have := P.isAb.proper
  have : IsCommMonObj H := ⟨by
    rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  obtain ⟨N, hN, hH⟩ := hk R H ‹_› ‹_›
  have : IsLocallyNoetherian P.A.left := LocallyOfFiniteType.isLocallyNoetherian P.A.hom
  have := (hm _ P N hN).1
  obtain ⟨Λ, _, _, _, _, e, _⟩ := exists_hopfAlgebra R H
  have hi : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hH, MonObj.one_comp]
  obtain ⟨Q, q, π, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient_hopf hq (e.hom ≫ i) (mulA P.A N) (by
    rw [mulA, comp_pow, comp_pow, Category.comp_id, Category.comp_id, mul_pow, ← comp_pow,
      ← comp_pow i, hi, comp_one, comp_one, _root_.one_mul])
  refine ⟨Q, q, h₂, h₃, h₄, ?_, ?_, ?_⟩
  · rw [← Over.w π]; infer_instance
  · rw [← Over.w π]; infer_instance
  · refine h₅.of_iso (whiskerRightIso e P.A) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      <;> simp [comp_mul]

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorusLocal

theorem pullback_map_eq_one {S S' : Scheme.{0}} (p : S' ⟶ S) (X : Type) [AddCommGroup X]
    (B : Over S) [GrpObj B] (f : splitTorus S X ⟶ B) (hf : IsMonHom f)
    (h : ∀ g : splitTorus S' X ⟶ (Over.pullback p).obj B, IsMonHom g →
      g = toUnit _ ≫ η[(Over.pullback p).obj B]) :
    (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) := by
  obtain ⟨e, he, -⟩ := splitTorus_baseChange S S' p X
  have h1 : e.hom ≫ (Over.pullback p).map f = 1 := h _ inferInstance
  have h2 : (Over.pullback p).map (1 : splitTorus S X ⟶ B) = 1 := Functor.map_one _
  rw [← cancel_epi e.hom, h1, ← Hom.one_def, h2, MonObj.comp_one]

theorem eq_one_of_isNilpotent_maximalIdeal (A : Type) [CommRing A] [IsLocalRing A]
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Spec (CommRingCat.of A))) [GrpObj B]
    [IsProper B.hom] (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ B) (hf : IsMonHom f) :
    f = toUnit _ ≫ η[B] := by
  refine splitTorus_hom_eq_one_of_nilpotent A _ hA X B f hf (pullback_map_eq_one _ X B f hf ?_)
  intro g hg
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  have : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))).obj B).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  exact splitTorus_hom_proper_trivial_field (A ⧸ IsLocalRing.maximalIdeal A) X _ g hg

theorem eq_zero_of_forall_mem_map_pow {A C : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing C] [Algebra A C] [Module.Free A C] (x : C)
    (hx : ∀ n : ℕ, x ∈ (IsLocalRing.maximalIdeal A ^ (n + 1)).map (algebraMap A C)) : x = 0 := by
  let b := Module.Free.chooseBasis A C
  refine b.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal.isMaximal A).ne_top, Ideal.mem_iInf]
  intro n
  have := TorusNil.map_mem_map _ (b.coord i) (hx n)
  rw [Algebra.algebraMap_self, Ideal.map_id] at this
  exact Ideal.pow_le_pow_right (Nat.le_succ n) this


open TorusNil in
theorem pt_ext_of_quotients {A C : Type} [CommRing A] [CommRing C] [Algebra A C] {N : Type}
    (I : N → Ideal C) (hI : ∀ x, (∀ i, x ∈ I i) → x = 0)
    {B : Over (Spec (CommRingCat.of A))} [IsSeparated B.hom] {a b : sp A C ⟶ B}
    (h : ∀ i, spm (Ideal.Quotient.mkₐ A (I i)) ≫ a = spm (Ideal.Quotient.mkₐ A (I i)) ≫ b) :
    a = b := by
  have : IsAffine (sp A C).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of C)))
  have hinj : Function.Injective (equalizer.ι a b).left.appTop := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have hb := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).hom
    apply hb.1
    refine Eq.trans (hI _ fun i => ?_) (map_zero _).symm
    have h1 : (spm (Ideal.Quotient.mkₐ A (I i))).left.appTop x = 0 := by
      rw [← equalizer.lift_ι _ (h i), Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        hx, map_zero]
    have h2 := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I i)))) x
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine h2.symm.trans ?_
    refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (C ⧸ I i))).hom h1).trans (map_zero _)
  have := IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  apply Over.OverMorphism.ext
  rw [← cancel_epi (equalizer.ι a b).left, ← Over.comp_left, equalizer.condition, Over.comp_left]

end TorusLocal


open TorusNil TorusLocal in
theorem splitTorus_hom_proper_trivial_local (A : Type) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsProper B.hom]
    (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ B) (hf : IsMonHom f) :
    f = toUnit _ ≫ η[B] := by
  have hn : ∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))))).map (toUnit _ ≫ η[B]) := by
    intro n
    set J := IsLocalRing.maximalIdeal A ^ (n + 1) with hJ
    refine pullback_map_eq_one _ X B f hf fun g hg => ?_
    have hJt : J ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
    have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJt
    have : IsLocalRing (A ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    have : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk J)))).obj B).hom :=
      inferInstanceAs (IsProper (pullback.snd _ _))
    refine eq_one_of_isNilpotent_maximalIdeal (A ⧸ J) ⟨n + 1, ?_⟩ X _ g hg
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective, ← Ideal.map_pow, ← hJ, Ideal.map_quotient_self]
    rfl
  set t := torusPt A X (AddMonoidAlgebra.of A X) with ht
  have h1 : t ≫ f = t ≫ toUnit _ ≫ η[B] := by
    refine pt_ext_of_quotients (fun n : ℕ =>
      (IsLocalRing.maximalIdeal A ^ (n + 1)).map (algebraMap A (AddMonoidAlgebra A X)))
      eq_zero_of_forall_mem_map_pow fun n => ?_
    rw [← Category.assoc, ← Category.assoc _ t]
    exact comp_eq_of_pullback_map_eq (hn n) _
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _
        (algebraMap A (AddMonoidAlgebra A X ⧸ (IsLocalRing.maximalIdeal A ^ (n + 1)).map
          (algebraMap A (AddMonoidAlgebra A X)))) (fun a ha => by
          rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_map_of_mem _ ha))))
      (by rw [← Spec.map_comp]; rfl)
  have := isIso_torusPt_of A X
  apply Over.OverMorphism.ext
  rw [← cancel_epi t.left, ← Over.comp_left, h1, ← Over.comp_left]

end GlobalTheory
end
