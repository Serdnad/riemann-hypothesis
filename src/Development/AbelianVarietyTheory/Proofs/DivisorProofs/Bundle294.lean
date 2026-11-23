module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle007
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle179
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

open TensorProduct LinearMap IsLocalRing

namespace GlobalTheory

namespace LocalFlatMax

universe u

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]

theorem lTensor_injective_of_smul_le (I : Ideal A) [hI : I.IsMaximal]
    (h : Function.Injective (I.subtype.lTensor M))
    {F : Type u} [AddCommGroup F] [Module A F] (N : Submodule A F)
    (hN : I • (⊤ : Submodule A F) ≤ N) : Function.Injective (N.subtype.lTensor M) := by
  let p : (M →₀ A) →ₗ[A] M := Finsupp.linearCombination A id
  have hp : Function.Surjective p := Finsupp.linearCombination_id_surjective A M
  have h1 : Function.Injective ((ker p).subtype.lTensor (A ⧸ I)) :=
    lTensor_injective_of_exact_of_exact_of_rTensor_injective (exact_subtype_mkQ I)
      (Submodule.mkQ_surjective I) (exact_subtype_ker_map p) hp
      ((lTensor_inj_iff_rTensor_inj _ _).mp h)
      (Module.Flat.lTensor_preserves_injective_linearMap _ (ker p).injective_subtype)
  have htors : Module.IsTorsionBySet A (F ⧸ N) I := by
    intro x a
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    change N.mkQ (a.1 • x) = 0
    exact (Submodule.Quotient.mk_eq_zero N).mpr (hN (Submodule.smul_mem_smul a.2 trivial))
  letI : Module (A ⧸ I) (F ⧸ N) := htors.module
  haveI : IsScalarTower A (A ⧸ I) (F ⧸ N) := htors.isScalarTower
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  have h2 : Function.Injective ((ker p).subtype.lTensor (F ⧸ N)) := by
    have h3 : Function.Injective
        ((AlgebraTensorModule.lTensor (A ⧸ I) (A ⧸ I) (ker p).subtype).lTensor (F ⧸ N)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ h1
    have : AlgebraTensorModule.lTensor (A ⧸ I) (F ⧸ N) (ker p).subtype =
        (AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) (F ⧸ N) _).toLinearMap ∘ₗ
          (AlgebraTensorModule.lTensor (A ⧸ I) (A ⧸ I) (ker p).subtype).lTensor (F ⧸ N) ∘ₗ
          (AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) (F ⧸ N) _).symm.toLinearMap := by
      ext
      simp
    change Function.Injective (AlgebraTensorModule.lTensor (A ⧸ I) (F ⧸ N) (ker p).subtype)
    rw [this]
    simpa using h3
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective (exact_subtype_ker_map p) hp
    (exact_subtype_mkQ N) (Submodule.mkQ_surjective N) ((lTensor_inj_iff_rTensor_inj _ _).mp h2)
    (Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype)

theorem lTensor_injective_of_pow_smul_le (I : Ideal A) [hI : I.IsMaximal]
    (h : Function.Injective (I.subtype.lTensor M))
    {F : Type u} [AddCommGroup F] [Module A F] (n : ℕ) (N : Submodule A F)
    (hN : I ^ n • (⊤ : Submodule A F) ≤ N) : Function.Injective (N.subtype.lTensor M) := by
  induction n generalizing N with
  | zero => exact lTensor_injective_of_smul_le I h N (le_top.trans (by simpa using hN))
  | succ n ih =>
    let N' : Submodule A F := N ⊔ I ^ n • ⊤
    have h1 := ih N' le_sup_right
    have h2 := lTensor_injective_of_smul_le I h (N.comap N'.subtype) (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_subtype_top,
        Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ']
      exact sup_le Submodule.smul_le_right hN)
    have : N.subtype = N'.subtype ∘ₗ (N.comap N'.subtype).subtype ∘ₗ
        (Submodule.comapSubtypeEquivOfLe (le_sup_left : N ≤ N')).symm.toLinearMap := by
      ext
      rfl
    rw [this, lTensor_comp, lTensor_comp]
    exact h1.comp (h2.comp (LinearEquiv.lTensor M _).injective)

theorem relationsLift_of_lTensor_injective (K : Ideal A)
    (h : ∀ L : Ideal A, K ≤ L → Function.Injective (L.subtype.lTensor M)) :
    LocalFlat.RelationsLift K M := by
  intro F _ _ f x hx
  have hy : ∃ y : M ⊗[A] K, TensorProduct.rid A M (K.subtype.lTensor M y) =
      TensorProduct.rid A M (f.lTensor M x) := by
    refine Submodule.smul_induction_on (p := fun d => ∃ y : M ⊗[A] K,
      TensorProduct.rid A M (K.subtype.lTensor M y) = d) hx ?_ ?_
    · intro r hr m _
      exact ⟨m ⊗ₜ ⟨r, hr⟩, by simp⟩
    · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, by simp⟩
  obtain ⟨y, hy⟩ := hy
  replace hy := (TensorProduct.rid A M).injective hy
  let g : F × K →ₗ[A] A := f.coprod (-K.subtype)
  let z : M ⊗[A] (F × K) := (inl A F K).lTensor M x + (inr A F K).lTensor M y
  have hgz : g.lTensor M z = 0 := by
    simp only [z, g, map_add (f := _), ← lTensor_comp_apply, coprod_inl, coprod_inr, lTensor_neg,
      LinearMap.neg_apply, hy, add_neg_cancel]
  have hL : K ≤ range g := fun a ha => ⟨(0, ⟨-a, neg_mem ha⟩), by simp [g]⟩
  have hz : g.rangeRestrict.lTensor M z = 0 := by
    apply h _ hL
    rw [← lTensor_comp_apply, map_zero]
    exact hgz
  obtain ⟨w, hw⟩ := (lTensor_exact M (exact_subtype_ker_map g.rangeRestrict)
    g.surjective_rangeRestrict z).mp hz
  refine LocalFlat.range_lTensor_le (fst A F K ∘ₗ (ker g.rangeRestrict).subtype) _ ?_ ⟨w, ?_⟩
  · rintro ⟨⟨v, k⟩, hv⟩
    have : f v + -(k : A) = 0 := congrArg Subtype.val hv
    change f v ∈ K
    rw [add_neg_eq_zero.mp this]
    exact k.2
  · rw [lTensor_comp_apply, hw]
    simp only [z, map_add (f := _), ← lTensor_comp_apply, fst_comp_inl, fst_comp_inr, lTensor_id,
      lTensor_zero, LinearMap.zero_apply, add_zero, id_apply]

theorem flat_of_lTensor_injective [IsNoetherianRing A] (B : Type*) [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [Module B M] [IsScalarTower A B M] [Module.Finite B M] (I : Ideal A)
    [I.IsMaximal] (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥)
    (h : Function.Injective (I.subtype.lTensor M)) : Module.Flat A M :=
  LocalFlat.flat_of_relationsLift B hI fun n =>
    relationsLift_of_lTensor_injective _ fun L hL =>
      lTensor_injective_of_pow_smul_le I h n L (by simpa using hL)

theorem lTensor_map_injective {O : Type*} [CommRing O] [Algebra O A] [Module O M]
    [IsScalarTower O A M] [Module.Flat O M] (J : Ideal O) :
    Function.Injective ((J.map (algebraMap O A)).subtype.lTensor M) := by
  let j : J →ₗ[O] J.map (algebraMap O A) :=
    { toFun := fun a => ⟨algebraMap O A a, Ideal.mem_map_of_mem _ a.2⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun a b => Subtype.ext (by simp [Algebra.smul_def]) }
  let t : M ⊗[O] J →ₗ[O] M ⊗[A] J.map (algebraMap O A) :=
    mapOfCompatibleSMul A O O M _ ∘ₗ j.lTensor M
  have ht : ∀ x, ∃ y, t y = x := by
    intro x
    induction x with
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, map_add _ _ _⟩
    | tmul m r =>
      obtain ⟨r, hr⟩ := r
      induction hr using Submodule.span_induction generalizing m with
      | mem r hr =>
        obtain ⟨a, ha, rfl⟩ := hr
        exact ⟨m ⊗ₜ ⟨a, ha⟩, rfl⟩
      | zero => exact ⟨0, (map_zero _).trans (tmul_zero _ _).symm⟩
      | add a b ha hb iha ihb =>
        obtain ⟨a', ha'⟩ := iha m
        obtain ⟨b', hb'⟩ := ihb m
        exact ⟨a' + b', by rw [map_add (f := _), ha', hb', ← tmul_add]; rfl⟩
      | smul c a ha iha =>
        obtain ⟨a', ha'⟩ := iha (c • m)
        exact ⟨a', by rw [ha', smul_tmul]; rfl⟩
  have hc : ∀ y, TensorProduct.rid A M ((J.map (algebraMap O A)).subtype.lTensor M (t y)) =
      TensorProduct.rid O M (J.subtype.lTensor M y) := by
    intro y
    induction y with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul m a => simp [t, j]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := ht x
  have h0 := hc y
  rw [hx, map_zero, eq_comm, LinearEquiv.map_eq_zero_iff] at h0
  have h1 : y = 0 :=
    Module.Flat.lTensor_preserves_injective_linearMap _ J.injective_subtype
      (h0.trans (map_zero _).symm)
  rw [h1, map_zero]

end LocalFlatMax

theorem ringHom_flat_of_comp_flat_of_map_maximalIdeal :
    ∀ (O R' E : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R']
      [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [IsNoetherianRing E]
      (φ' : O →+* R') (b : R' →+* E), φ'.Flat → (maximalIdeal O).map φ' = maximalIdeal R' →
      IsLocalHom b → (b.comp φ').Flat → b.Flat := by
  intro O R' E _ _ _ _ _ _ _ _ _ φ' b _ hm hb hc
  algebraize [φ', b, b.comp φ']
  refine LocalFlatMax.flat_of_lTensor_injective E (maximalIdeal R') ?_ ?_
  · have h : (maximalIdeal R').map b ≤ maximalIdeal E := ((local_hom_tfae b).out 1 3).mp hb
    exact h.trans (maximalIdeal_le_jacobson _)
  · rw [← hm]
    exact LocalFlatMax.lTensor_map_injective (maximalIdeal O)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory

namespace UnitCocycle

section Tensor

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]


variable (R B) in
noncomputable def m₁₂ : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.map (AlgHom.id R B) Algebra.TensorProduct.includeLeft


variable (R B) in
noncomputable def m₁₃ : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.map (AlgHom.id R B) Algebra.TensorProduct.includeRight


variable (R B) in
noncomputable def m₂₃ : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.includeRight

noncomputable def datum (c : B ⊗[R] B) : B →ₗ[B] B ⊗[R] B :=
  LinearMap.toSpanSingleton B _ c

theorem datum_apply (c : B ⊗[R] B) (x : B) : datum c x = c * (x ⊗ₜ[R] (1 : B)) := by
  rw [datum, LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_comm]
  rfl

theorem lmul'_eq_one {c : B ⊗[R] B} (hu : IsUnit c)
    (h : m₁₃ R B c = m₁₂ R B c * m₂₃ R B c) : Algebra.TensorProduct.lmul' R c = (1 : B) := by
  let μ : B ⊗[R] B →ₐ[R] B := Algebra.TensorProduct.lmul' R
  let ν : B ⊗[R] (B ⊗[R] B) →ₐ[R] B :=
    μ.comp (Algebra.TensorProduct.map (AlgHom.id R B) μ)
  have h12 : ν.comp (m₁₂ R B) = μ := by ext <;> simp [ν, μ, m₁₂, Algebra.TensorProduct.one_def]
  have h13 : ν.comp (m₁₃ R B) = μ := by ext <;> simp [ν, μ, m₁₃, Algebra.TensorProduct.one_def]
  have h23 : ν.comp (m₂₃ R B) = μ := by ext <;> simp [ν, μ, m₂₃, Algebra.TensorProduct.one_def]
  have h' := congrArg ν h
  rw [map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply, h12, h13, h23] at h'
  exact (hu.map μ).mul_left_cancel (by rw [mul_one]; exact h'.symm)

theorem isDescentDatum {c : B ⊗[R] B} (hu : IsUnit c)
    (h : m₁₃ R B c = m₁₂ R B c * m₂₃ R B c) : GlobalTheory.FlatDescent.IsDescentDatum (datum c) := by
  have ha : ∀ z : B ⊗[R] B, GlobalTheory.FlatDescent.act (A := R) (B := B) (N := B) z = Algebra.TensorProduct.lmul' R z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul b m => simp
  have h1 : ∀ z : B ⊗[R] B,
      ((datum c).restrictScalars R).lTensor B z = m₁₂ R B z * m₂₃ R B c := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_mul]
    | tmul b m => simp [datum_apply, m₁₂, m₂₃, mul_comm]
  have h2 : ∀ z : B ⊗[R] B, (TensorProduct.mk R B B 1).lTensor B z = m₁₃ R B z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul b m => simp [m₁₃]
  constructor
  · intro n
    rw [ha, datum_apply, map_mul, lmul'_eq_one hu h]
    simp
  · intro n
    rw [h1, h2, datum_apply, map_mul, map_mul, h, mul_right_comm]
    congr 1

theorem exists_local_tensor [Module.FaithfullyFlat R B] {c : B ⊗[R] B} (hu : IsUnit c)
    (h : m₁₃ R B c = m₁₂ R B c * m₂₃ R B c) (P : Ideal R) (hP : P ≠ ⊤) :
    ∃ s : R, s ∉ P ∧ ∃ x y : B, x * y = algebraMap R B s ∧
      (1 : B) ⊗ₜ[R] x = c * (x ⊗ₜ[R] (1 : B)) := by
  have hd := isDescentDatum hu h
  have hI := hd.invertible_invariants
  let I := GlobalTheory.FlatDescent.invariants (datum c)
  obtain ⟨φ, m, hm⟩ : ∃ (φ : Module.Dual R I) (m : I), φ m ∉ P := by
    by_contra hcon
    push_neg at hcon
    apply hP
    rw [Ideal.eq_top_iff_one]
    obtain ⟨z, hz⟩ := hI.bijective.2 1
    rw [← hz]
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _)]; exact P.add_mem hx hy
    | tmul b m => simpa using hcon b m
  let e := LinearEquiv.ofBijective _ hd.bijective_extend
  let Φ : B →ₗ[B] B :=
    (AlgebraTensorModule.rid R B B).toLinearMap ∘ₗ LinearMap.baseChange B φ ∘ₗ e.symm.toLinearMap
  have h1 : e.symm (m : B) = 1 ⊗ₜ m := by
    rw [LinearEquiv.symm_apply_eq]
    simp [e]
  refine ⟨φ m, hm, m, Φ 1, ?_, ?_⟩
  · rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    simp [Φ, h1, Algebra.algebraMap_eq_smul_one]
  · rw [← datum_apply]
    exact (GlobalTheory.FlatDescent.mem_invariants.1 m.2).symm

end Tensor

theorem exists_local (R B C D : CommRingCat.{0}) (f : R ⟶ B) (j₁ j₂ : B ⟶ C) (d₁₂ d₂₃ d₁₃ : C ⟶ D)
    (hC : IsPushout f f j₁ j₂) (hD : IsPushout j₂ j₁ d₁₂ d₂₃) (h₁ : j₁ ≫ d₁₃ = j₁ ≫ d₁₂)
    (h₂ : j₂ ≫ d₁₃ = j₂ ≫ d₂₃) (hf : f.hom.FaithfullyFlat) (c : Cˣ)
    (hc : d₁₃.hom (c : C) = d₁₂.hom (c : C) * d₂₃.hom (c : C)) (P : Ideal R) (hP : P.IsPrime) :
    ∃ s : R, s ∉ P ∧ ∃ x y : B, x * y = f.hom s ∧ j₂.hom x = (c : C) * j₁.hom x := by
  letI : Algebra R B := f.hom.toAlgebra
  haveI : Module.FaithfullyFlat R B := hf
  have hT := CommRingCat.isPushout_tensorProduct R B B
  let e : C ≅ CommRingCat.of (B ⊗[R] B) := hC.isoIsPushout _ _ hT
  have e1 : j₁ ≫ e.hom = _ := hC.inl_isoIsPushout_hom _ _ hT
  have e2 : j₂ ≫ e.hom = _ := hC.inr_isoIsPushout_hom _ _ hT
  have e1' : ∀ x : B, e.hom.hom (j₁.hom x) = x ⊗ₜ[R] (1 : B) := fun x =>
    congrArg (fun q => q.hom x) e1
  have e2' : ∀ x : B, e.hom.hom (j₂.hom x) = (1 : B) ⊗ₜ[R] x := fun x =>
    congrArg (fun q => q.hom x) e2
  let n₁₂ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) := e.hom ≫ CommRingCat.ofHom (m₁₂ R B).toRingHom
  let n₁₃ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) := e.hom ≫ CommRingCat.ofHom (m₁₃ R B).toRingHom
  let n₂₃ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) := e.hom ≫ CommRingCat.ofHom (m₂₃ R B).toRingHom
  have w : j₂ ≫ n₁₂ = j₁ ≫ n₂₃ := by
    ext x
    change m₁₂ R B (e.hom.hom (j₂.hom x)) = m₂₃ R B (e.hom.hom (j₁.hom x))
    rw [e1', e2']
    simp [m₁₂, m₂₃]
  let ψ := hD.desc n₁₂ n₂₃ w
  have p12 : d₁₂ ≫ ψ = n₁₂ := hD.inl_desc _ _ _
  have p23 : d₂₃ ≫ ψ = n₂₃ := hD.inr_desc _ _ _
  have p13 : d₁₃ ≫ ψ = n₁₃ := by
    apply hC.hom_ext
    · rw [← Category.assoc, h₁, Category.assoc, p12]
      ext x
      change m₁₂ R B (e.hom.hom (j₁.hom x)) = m₁₃ R B (e.hom.hom (j₁.hom x))
      rw [e1']
      simp [m₁₂, m₁₃, Algebra.TensorProduct.one_def]
    · rw [← Category.assoc, h₂, Category.assoc, p23]
      ext x
      change m₂₃ R B (e.hom.hom (j₂.hom x)) = m₁₃ R B (e.hom.hom (j₂.hom x))
      rw [e2']
      simp [m₂₃, m₁₃]
  have hco : m₁₃ R B (e.hom.hom c) = m₁₂ R B (e.hom.hom c) * m₂₃ R B (e.hom.hom c) := by
    have h' := congrArg ψ.hom hc
    rw [map_mul] at h'
    have q12 : ψ.hom (d₁₂.hom c) = m₁₂ R B (e.hom.hom c) := congrArg (fun q => q.hom (c : C)) p12
    have q13 : ψ.hom (d₁₃.hom c) = m₁₃ R B (e.hom.hom c) := congrArg (fun q => q.hom (c : C)) p13
    have q23 : ψ.hom (d₂₃.hom c) = m₂₃ R B (e.hom.hom c) := congrArg (fun q => q.hom (c : C)) p23
    rwa [q12, q13, q23] at h'
  obtain ⟨s, hs, x, y, hxy, hx⟩ :=
    exists_local_tensor (c.isUnit.map e.hom.hom) hco P hP.ne_top
  refine ⟨s, hs, x, y, hxy, ?_⟩
  apply e.commRingCatIsoToRingEquiv.injective
  change e.hom.hom _ = e.hom.hom _
  rw [map_mul, e1', e2']
  exact hx

end UnitCocycle

end GlobalTheory
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

noncomputable section

namespace GlobalTheory.RealWeil

theorem continuous_omS_prod (l : Type) [Fintype l] [DecidableEq l] (G : Type) [Group G] [TopologicalSpace G]
    (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l))
    (hpr : Continuous pr) (hom : ∀ f : L2 l, Continuous fun g => om g f)
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) :
    Continuous fun x : G × Sch l => omS x.1 x.2 := by

  have hjoint : Continuous fun x : G × L2 l => om x.1 x.2 :=
    continuous_prod_of_continuous_lipschitzWith' (fun x : G × L2 l => om x.1 x.2) 1
      (fun g => (om g).isometry.lipschitz) hom
  have hentry : ∀ a b, Continuous fun g => (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b := fun a b =>
    by
    have hv : Continuous fun g => (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
      (continuous_subtype_val (p := fun M => M ∈ Matrix.symplecticGroup l ℝ)).comp hpr
    exact (continuous_apply b).comp ((continuous_apply a).comp hv)

  have key : ∀ {A : Sch l →L[ℂ] Sch l}, A ∈ weylAlg l →
      Continuous fun x : G × Sch l => schwartzToL2 l (A (omS x.1 x.2)) := by
    intro A hA
    refine weylAlg_induction (P := fun A => Continuous fun x : G × Sch l => schwartzToL2 l (A (omS x.1 x.2)))
      ?_ ?_ ?_ ?_ ?_ hA
    · have e : (fun x : G × Sch l => schwartzToL2 l ((1 : Sch l →L[ℂ] Sch l) (omS x.1 x.2))) =
          fun x => om x.1 (schwartzToL2 l x.2) := by
        funext x
        simp only [ContinuousLinearMap.one_apply, schwartzToL2_apply, h4]
      rw [e]
      exact hjoint.comp (continuous_fst.prodMk ((schwartzToL2 l).continuous.comp continuous_snd))
    · intro A w ih
      simp only [toLp_dRho_omS h3 h4]
      refine continuous_finsetSum _ fun a _ => ?_
      have hih : Continuous fun x : G × Sch l => schwartzToL2 l (A (omS x.1 (dRho (Pi.single a 1) x.2))) :=
        ih.comp (continuous_fst.prodMk ((dRho (Pi.single a 1)).continuous.comp continuous_snd))
      refine Continuous.smul (M := ℂ) ?_ hih
      refine continuous_ofReal.comp ?_
      simp only [mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, transpose_apply]
      exact continuous_finsetSum _ fun b _ => Continuous.mul (Continuous.neg (continuous_finsetSum _ fun c _ =>
        Continuous.mul (continuous_finsetSum _ fun d _ => continuous_const.mul
          ((hentry _ _).comp continuous_fst)) continuous_const)) continuous_const
    · simp only [ContinuousLinearMap.zero_apply, map_zero]
      exact continuous_const
    · intro A B hA hB
      simp only [ContinuousLinearMap.add_apply, map_add (f := _)]
      exact hA.add hB
    · intro c A hA
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      exact hA.const_smul c
  rw [continuous_iff_continuousAt]
  intro x0
  unfold ContinuousAt
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨A, hA, hb⟩ := exists_seminorm_le (l := l) k n
  have ht : Filter.Tendsto (fun x : G × Sch l => ∑ r, ‖schwartzToL2 l (A r (omS x.1 x.2)) - schwartzToL2 l (A r (omS x0.1 x0.2))‖)
      (nhds x0) (nhds 0) := by
    have : (0 : ℝ) = ∑ r : Fin n → l, ‖schwartzToL2 l (A r (omS x0.1 x0.2)) - schwartzToL2 l (A r (omS x0.1 x0.2))‖ := by simp
    rw [this]
    exact tendsto_finsetSum _ fun r _ => ((((key (hA r)).sub continuous_const).norm).tendsto x0)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with x hx
  refine lt_of_le_of_lt ?_ hx
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  refine (hb _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← schwartzToL2_apply, map_sub, map_sub]

end GlobalTheory.RealWeil
end
end

section

open NumberField

theorem _root_.GlobalTheory.T.twistedProjector_idempotent_of_groupAlgebra_idem : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL),
    (∀ k, ∑ g, eC g * eC (g⁻¹ * k) = eC k) → A.eOp eC ∘ₗ A.eOp eC = A.eOp eC := by
  first | exact @GlobalTheory.eOp_comp_self_of_conv_idem | exact GlobalTheory.eOp_comp_self_of_conv_idem | (intros; apply GlobalTheory.eOp_comp_self_of_conv_idem <;> assumption)
end
