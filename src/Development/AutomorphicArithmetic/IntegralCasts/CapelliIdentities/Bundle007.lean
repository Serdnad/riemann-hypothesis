module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Star.Basic
public import Mathlib.LinearAlgebra.Span.Defs
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

@[expose] public section

section

open TensorProduct in
private theorem UpperTheory.universal_derivation_surjective {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Algebra B A] [IsScalarTower A B A]
    [Algebra.FormallySmooth A B] [Algebra.EssFiniteType A B] :
    ∃ (n : ℕ) (d : Derivation A B (Fin n → A)), Function.Surjective d ∧
      ∀ (R : Type) [AddCommGroup R] [Module A R] [Module B R] [IsScalarTower B A R]
        (δ : Derivation A B R), ∃ c : Fin n → R, ∀ b, δ b = ∑ i, d b i • c i := by
  haveI : Module.Free A (A ⊗[B] Ω[B⁄A]) := Module.free_of_flat_of_isLocalRing
  let e := Module.finBasis A (A ⊗[B] Ω[B⁄A])
  let D0 : Derivation A B (A ⊗[B] Ω[B⁄A]) :=
    (TensorProduct.mk B A Ω[B⁄A] 1).compDer (KaehlerDifferential.D A B)
  have hD0 : ∀ b, D0 b = 1 ⊗ₜ KaehlerDifferential.D A B b := fun b => rfl
  have hsurj : Function.Surjective D0 := by
    have h1 : ∀ (w : Ω[B⁄A]) (a : A), a ⊗ₜ[B] w ∈ LinearMap.range D0.toLinearMap := by
      intro w
      have hw : w ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        intro a
        have : a ⊗ₜ[B] KaehlerDifferential.D A B b = a • D0 b := by
          rw [hD0, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ ⟨b, rfl⟩
      | zero => intro a; simp
      | add x y _ _ hx hy =>
        intro a
        rw [TensorProduct.tmul_add]
        exact add_mem (hx a) (hy a)
      | smul b x _ hx =>
        intro a
        rw [← TensorProduct.smul_tmul]
        exact hx _
    intro x
    change x ∈ LinearMap.range D0.toLinearMap
    induction x with
    | tmul a w => exact h1 w a
    | add x y hx hy => exact add_mem hx hy
  refine ⟨_, (e.equivFun.toLinearMap.restrictScalars B).compDer D0,
    e.equivFun.surjective.comp hsurj, ?_⟩
  intro R _ _ _ _ δ
  haveI : IsScalarTower A B R := ⟨fun a b r => by
    rw [← algebraMap_smul A (a • b) r, ← algebraMap_smul A b r, ← mul_smul]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, smul_assoc, ← Algebra.algebraMap_eq_smul_one, smul_eq_mul]⟩
  let f : A ⊗[B] Ω[B⁄A] →ₗ[A] R := δ.liftKaehlerDifferential.liftBaseChange A
  refine ⟨fun i => f (e i), fun b => ?_⟩
  have h2 : δ b = f (D0 b) := by
    simp [f, hD0]
  rw [h2]

  conv_lhs => rw [← e.sum_equivFun (D0 b), map_sum]
  simp only [map_smul]
  rfl

theorem UpperTheory.formally_smooth_surjective_derivation :
    ∀ {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] (α : A →+* B) (σ : B →+* A),
        σ.comp α = RingHom.id A → α.FormallySmooth → α.EssFiniteType →
          ∃ (n : ℕ) (d : B → Fin n → A), Function.Surjective d ∧
            ∀ (R : Type) [CommRing R] (φ : A →+* R),
              (∀ c : Fin n → R, ∃ g : B →+* DualNumber R,
                (∀ a, g (α a) = TrivSqZeroExt.inl (φ a)) ∧ (∀ b, (g b).fst = φ (σ b)) ∧
                  ∀ b, (g b).snd = ∑ i, φ (d b i) * c i) ∧
              ∀ g : B →+* DualNumber R, (∀ a, g (α a) = TrivSqZeroExt.inl (φ a)) → (∀ b, (g b).fst = φ (σ b)) →
                ∃ c : Fin n → R, ∀ b, (g b).snd = ∑ i, φ (d b i) * c i := by
  intro A B _ _ _ α σ hσ hfs hft
  have hσ' : ∀ a, σ (α a) = a := fun a => RingHom.congr_fun hσ a
  letI : Algebra A B := α.toAlgebra
  letI : Algebra B A := σ.toAlgebra
  haveI : IsScalarTower A B A := IsScalarTower.of_algebraMap_eq fun a => (hσ' a).symm
  haveI : Algebra.FormallySmooth A B := hfs
  haveI : Algebra.EssFiniteType A B := hft
  obtain ⟨n, d, hd, H⟩ := UpperTheory.universal_derivation_surjective (A := A) (B := B)
  have hmul : ∀ x y i, d (x * y) i = σ x * d y i + σ y * d x i := fun x y i => by
    rw [d.leibniz]; rfl
  have hα : ∀ a, d (α a) = 0 := fun a => d.map_algebraMap a
  refine ⟨n, d, hd, fun R _ φ => ⟨fun c => ?_, fun g hg1 hg2 => ?_⟩⟩
  · refine ⟨{ toFun := fun b => TrivSqZeroExt.inl (φ (σ b)) +
                TrivSqZeroExt.inr (∑ i, φ (d b i) * c i)
              map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_, ?_⟩
    · ext <;> simp
    · intro x y
      ext
      · simp
      · simp [hmul, -Derivation.leibniz, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, mul_add, add_comm]
    · ext <;> simp
    · intro x y
      ext <;> simp [add_mul, Finset.sum_add_distrib]
    · intro a
      simp [hα, hσ']
    · intro b
      simp
    · intro b
      simp
  · letI : Algebra A R := φ.toAlgebra
    letI : Algebra B R := (φ.comp σ).toAlgebra
    haveI : IsScalarTower B A R := IsScalarTower.of_algebraMap_eq fun b => rfl
    let δ : Derivation A B R := Derivation.mk'
      { toFun := fun b => (g b).snd
        map_add' := fun x y => by simp
        map_smul' := fun a b => by
          change (g (α a * b)).snd = φ a * (g b).snd
          simp [hg1] }
      (fun x y => by
        change (g (x * y)).snd = φ (σ x) * (g y).snd + φ (σ y) * (g x).snd
        simp [hg2, mul_comm])
    exact H R δ
end

section

noncomputable def UpperTheory.Reformulated.B.Qf15.CardLe :
    Type → ℕ → Prop :=
    fun (M : Type) (B : ℕ) ↦ Finite M ∧ Nat.card M ≤ B

noncomputable def UpperTheory.Reformulated.B.Qf15.TorsLe :
    (M : Type) → [AddCommGroup M] → ℕ → Prop :=
    fun (M : Type) [AddCommGroup M] (B : ℕ) ↦ Finite ↥(AddCommGroup.torsion M) ∧ Nat.card ↥(AddCommGroup.torsion M) ≤ B

theorem UpperTheory.Reformulated.B.Qf15.torsStep :
    ∀ (A B C : Type) [inst : AddCommGroup A] [inst_1 : AddCommGroup B] [inst_2 : AddCommGroup C] (f : A →+ B) (g : B →+ C)
      (a c : ℕ),
      Function.Exact (⇑f : A → B) (⇑g : B → C) →
        UpperTheory.Reformulated.B.Qf15.CardLe A a → UpperTheory.Reformulated.B.Qf15.TorsLe C c → UpperTheory.Reformulated.B.Qf15.TorsLe B (a * c) := by
  intro A B C _ _ _ f g a c hfg hA hC
  obtain ⟨hAf, hAc⟩ := hA
  obtain ⟨hCf, hCc⟩ := hC
  let φ : AddCommGroup.torsion B →+ AddCommGroup.torsion C :=
    (g.comp (AddCommGroup.torsion B).subtype).codRestrict _
      (fun x => g.isOfFinAddOrder x.2)
  have hk : ∀ x : φ.ker, ∃ y : A, f y = ((x : AddCommGroup.torsion B) : B) := by
    intro x
    have hx : φ x = 0 := x.2
    exact (hfg _).1 (congrArg Subtype.val hx)
  choose s hs using hk
  have hsi : Function.Injective s := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    rw [← hs x, ← hs y, h]
  haveI : Finite φ.ker := Finite.of_injective s hsi
  have e := (QuotientAddGroup.quotientKerEquivRange φ).toEquiv
  haveI : Finite (AddCommGroup.torsion B ⧸ φ.ker) := Finite.of_equiv _ e.symm
  have h1 : Nat.card φ.ker ≤ a := (Nat.card_le_card_of_injective s hsi).trans hAc
  have h2 : Nat.card (AddCommGroup.torsion B ⧸ φ.ker) ≤ c := by
    rw [Nat.card_congr e]
    exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans hCc
  refine ⟨Finite.of_equiv _ (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := φ.ker)).symm, ?_⟩
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker, mul_comm]
  exact Nat.mul_le_mul h1 h2
end

section

namespace AddCharEqMulShift

private lemma card_le (F K : Type) [Field F] [Fintype F] [Field K] :
    Finite (AddChar F K) ∧ Nat.card (AddChar F K) ≤ Nat.card F := by
  have hli : LinearIndependent K
      (fun ψ : AddChar F K => ((AddChar.toMonoidHomEquiv ψ : Multiplicative F →* K) :
        Multiplicative F → K)) :=
    (linearIndependent_monoidHom (Multiplicative F) K).comp _
      AddChar.toMonoidHomEquiv.injective
  have hfin : Finite (AddChar F K) := hli.finite
  refine ⟨hfin, ?_⟩
  haveI : Fintype (AddChar F K) := Fintype.ofFinite _
  have h := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h
  simpa [Nat.card_eq_fintype_card] using h

end AddCharEqMulShift

theorem UpperTheory.Reformulated.B.Yde4.main :
    ∀ {F K : Type} [inst : Field F] [Fintype F] [inst_2 : Field K] (ψ₀ ψ : AddChar F K),
      ψ₀ ≠ (1 : AddChar F K) → ∃ (c : F), ψ = ψ₀.mulShift c := by
  intro F K _ _ _ ψ₀ ψ h
  obtain ⟨hfin, hle⟩ := AddCharEqMulShift.card_le F K
  have hinj : Function.Injective ψ₀.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one h)
  obtain ⟨c, hc⟩ := (hinj.bijective_of_nat_card_le hle).2 ψ
  exact ⟨c, hc.symm⟩
end

section

namespace UpperTheory.Reformulated.B.AddCharacterCount.Helpers

private lemma card_le {C F : Type} [Field C] [Fintype F] [AddCommGroup F] :
    Finite (AddChar F C) ∧ Nat.card (AddChar F C) ≤ Nat.card F := by
  have li : LinearIndependent C (M := Multiplicative F → C)
      ((fun f => f : (Multiplicative F →* C) → Multiplicative F → C) ∘ AddChar.toMonoidHomEquiv) :=
    (linearIndependent_monoidHom (Multiplicative F) C).comp _ AddChar.toMonoidHomEquiv.injective
  have h1 := li.cardinalMk_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have hlt : Cardinal.mk (AddChar F C) < Cardinal.aleph0 :=
    lt_of_le_of_lt h1 Cardinal.natCast_lt_aleph0
  have hfin : Finite (AddChar F C) := Cardinal.lt_aleph0_iff_finite.mp hlt
  refine ⟨hfin, ?_⟩
  have : Nat.card (AddChar F C) ≤ Fintype.card (Multiplicative F) := by
    have h2 := Cardinal.toNat_le_toNat h1 Cardinal.natCast_lt_aleph0
    simpa only [Cardinal.toNat_mk, Cardinal.toNat_natCast] using h2
  simpa [Nat.card_eq_fintype_card] using this

end UpperTheory.Reformulated.B.AddCharacterCount.Helpers

open UpperTheory.Reformulated.B.AddCharacterCount.Helpers in
theorem UpperTheory.Reformulated.B.AddCharacterCount.main :
    ∀ {C F : Type} [inst : Field C] [inst_1 : Field F] [Fintype F] [DecidableEq F] (ψ : AddChar F C),
      ψ ≠ (1 : AddChar F C) →
        ∃ (e : F ≃ AddChar F C),
          (∀ (h h' : F), (e : F → AddChar F C) (h + h') = (e : F → AddChar F C) h * (e : F → AddChar F C) h') ∧
            ∀ (h a : F), ((e : F → AddChar F C) h : F → C) a = (ψ : F → C) (h * a) := by
  intro C F _ _ _ _ ψ hψ
  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hψ)
  obtain ⟨hfin, hc⟩ := card_le (C := C) (F := F)
  have hbij : Function.Bijective ψ.mulShift := hinj.bijective_of_nat_card_le hc
  refine ⟨Equiv.ofBijective _ hbij, ?_, ?_⟩
  · intro h h'
    simp [AddChar.mulShift_mul]
  · intro h a
    simp
end

section

namespace UpperTheory.Reformulated.B.S3

private theorem prod_mul_mem {k : Type} [Field k] {n : ℕ} (W : Submodule k (Fin n → k)) (d : Fin n → k)
    (hW : ∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) (v : Fin n → k) (hv : v ∈ W) (s : Finset (Fin n)) :
    (fun j => (∏ l ∈ s, (d j - d l)) * v j) ∈ W := by
  induction s using Finset.induction_on with
  | empty => simpa using hv
  | insert a s ha ih =>
    have h := W.sub_mem (hW _ ih) (W.smul_mem (d a) ih)
    convert h using 1
    ext j
    simp [Matrix.mulVec_diagonal, Finset.prod_insert ha, smul_eq_mul]
    ring

theorem single_mem {k : Type} [Field k] {n : ℕ} (W : Submodule k (Fin n → k)) (d : Fin n → k) (hd : Function.Injective d)
    (hW : ∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) (v : Fin n → k) (hv : v ∈ W) (i : Fin n) (hi : v i ≠ 0) :
    (Pi.single i 1 : Fin n → k) ∈ W := by
  have h := prod_mul_mem W d hW v hv (Finset.univ.erase i)
  have hc : (∏ l ∈ Finset.univ.erase i, (d i - d l)) * v i ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun l hl => ?_) hi
    exact sub_ne_zero.mpr fun e => (Finset.ne_of_mem_erase hl) (hd e).symm
  have h2 := W.smul_mem ((∏ l ∈ Finset.univ.erase i, (d i - d l)) * v i)⁻¹ h
  convert h2 using 1
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hc]
  · have hz : (∏ l ∈ Finset.univ.erase i, (d j - d l)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) (sub_self _)
    rw [Pi.single_eq_of_ne hj, Pi.smul_apply, smul_eq_mul, hz, zero_mul, mul_zero]

end UpperTheory.Reformulated.B.S3
end

section

theorem UpperTheory.Reformulated.B.SingleMemOfDiagonal.single_mem_of_diag :
    ∀ {κ : Type} [inst : Field κ] {m : ℕ} (d : Fin m → κ),
    Function.Injective d →
      ∀ (W : Submodule κ (Fin m → κ)),
        (∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) →
          ∀ v ∈ W, ∀ (i : Fin m), v i ≠ (0 : κ) → Pi.single i (1 : κ) ∈ W := by
  intro κ _ m d hd W hW v hv i hi
  have key : ∀ s : Finset (Fin m), (fun k => (∏ j ∈ s, (d k - d j)) * v k) ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hv
    | insert a s ha ih =>
      have h := W.sub_mem (hW _ ih) (W.smul_mem (d a) ih)
      convert h using 1
      funext k
      simp only [Finset.prod_insert ha, Pi.sub_apply, Matrix.mulVec_diagonal, Pi.smul_apply,
        smul_eq_mul]
      ring
  have hc : (∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j hj => ?_) hi
    exact sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hj) (hd h).symm
  have h := W.smul_mem ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹
    (key (Finset.univ.erase i))
  convert h using 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
    exact (inv_mul_cancel₀ hc).symm
  · have h0 : (∏ j ∈ Finset.univ.erase i, (d k - d j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) (sub_self _)
    simp only [Pi.single_eq_of_ne hk, Pi.smul_apply, smul_eq_mul, h0, zero_mul, mul_zero]
end

section

theorem UpperTheory.Reformulated.B.SingleMemSubmodule.single_mem :
    ∀ {K : Type} [inst : Field K] (d : Fin (3 : ℕ) → K),
    Function.Injective d →
      ∀ (W : Submodule K (Fin (3 : ℕ) → K)),
        (∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) →
          ∀ {v : Fin (3 : ℕ) → K}, v ∈ W → ∀ {i : Fin (3 : ℕ)}, v i ≠ (0 : K) → Pi.single i (1 : K) ∈ W := by
  intro K _ d hd W hW v hv i hi
  have step : ∀ (c : K), ∀ w ∈ W, (fun l => (d l - c) * w l) ∈ W := by
    intro c w hw
    have h := W.sub_mem (hW w hw) (W.smul_mem c hw)
    have e : (fun l => (d l - c) * w l) = (Matrix.diagonal d).mulVec w - c • w := by
      funext l
      simp only [Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul]
      ring
    rw [e]
    exact h
  have iter : ∀ s : Finset (Fin 3), (fun l => (∏ j ∈ s, (d l - d j)) * v l) ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : (fun l => (∏ j ∈ (∅ : Finset (Fin 3)), (d l - d j)) * v l) = v := by
        funext l
        simp
      rw [e]
      exact hv
    | insert a s ha ih =>
      have h := step (d a) _ ih
      have e : (fun l => (∏ j ∈ insert a s, (d l - d j)) * v l)
          = fun l => (d l - d a) * ((∏ j ∈ s, (d l - d j)) * v l) := by
        funext l
        rw [Finset.prod_insert ha, mul_assoc]
      rw [e]
      exact h
  have hc : (∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr ?_) hi
    intro j hj
    exact sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hj) (hd h).symm
  have h := W.smul_mem ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹
    (iter (Finset.univ.erase i))
  have e : (Pi.single i (1 : K) : Fin 3 → K)
      = ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹ •
        (fun l => (∏ j ∈ Finset.univ.erase i, (d l - d j)) * v l) := by
    funext l
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hl : l = i
    · subst hl
      rw [Pi.single_eq_same, inv_mul_cancel₀ hc]
    · have hz : ∏ j ∈ Finset.univ.erase i, (d l - d j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩) (sub_self _)
      rw [Pi.single_eq_of_ne hl, hz, zero_mul, mul_zero]
  rw [e]
  exact h
end

section

noncomputable def UpperTheory.Reformulated.B.Qe24.spanS.{u_1, u_2} :
    {K : Type u_1} →
      {V : Type u_2} →
        [inst : Field K] →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module K V] → (S : Subring K) → {n : ℕ} → (Fin n → V) → Submodule (↥S) V :=
    fun {K : Type u_1} {V : Type u_2} [Field K] [AddCommGroup V] [_root_.Module K V] (S : Subring K) {n : ℕ}
        (x : Fin n → V) ↦
      Submodule.span (↥S) (Set.range x)

theorem UpperTheory.Reformulated.B.Qe24.spanS_induction.{u_1, u_2} :
    ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [StarRing K] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      {S : Subring K} {n : ℕ} {x : Fin n → V} {p : V → Prop},
      p (0 : V) →
        (∀ (a b : V), p a → p b → p (a + b)) →
          (∀ c ∈ S, ∀ (a : V), p a → p (c • a)) → (∀ (i : Fin n), p (x i)) → ∀ v ∈ UpperTheory.Reformulated.B.Qe24.spanS S x, p v := by
  intro K V _ _ _ _ S n x p h0 hadd hsmul hx v hv
  unfold UpperTheory.Reformulated.B.Qe24.spanS at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hx i
  | zero => exact h0
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul c a _ ha => exact hsmul c.1 c.2 a ha
end

section

theorem UpperTheory.Reformulated.B.DYha5.main :
    ∀ {Ω Ω₀ F F₀ : Type} [inst : Field Ω] [inst_1 : Field Ω₀] [inst_2 : AddCommGroup F] [inst_3 : _root_.Module Ω F]
      [inst_4 : AddCommGroup F₀] [inst_5 : _root_.Module Ω₀ F₀] (i : Ω₀ →+* Ω) (ι : F₀ →+ F),
      (∀ (a : Ω₀) (e : F₀), (ι : F₀ → F) (a • e) = (i : Ω₀ → Ω) a • (ι : F₀ → F) e) →
        ∀ (W : Subring Ω) (A : Subring Ω₀),
          (∀ a ∈ A, (i : Ω₀ → Ω) a ∈ W) →
            ∀ (T : Set F₀),
              Submodule.span (↥W) ((⇑ι : F₀ → F) '' (↑(Submodule.span (↥A) T) : Set F₀)) =
                Submodule.span (↥W) ((⇑ι : F₀ → F) '' T) := by
  intro Ω Ω₀ F F₀ _ _ _ _ _ _ i ι hι W A hA T
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.span (↥A) T := hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ (hy ‹_›) (hz ‹_›)
    | smul a y _ hy =>
      have h1 : ι (a • y) = (⟨i a, hA a a.2⟩ : ↥W) • ι y := hι (a : Ω₀) y
      rw [h1]
      exact Submodule.smul_mem _ _ (hy ‹_›)
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qp8.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

theorem UpperTheory.Reformulated.B.Qp8.pow_eig :
    ∀ {C : Type} [inst : Field C] {N : ℕ} (y : UpperTheory.Reformulated.B.Qp8.Mat C N) (l : C) (w : Fin N → C),
      Matrix.mulVec y w = l • w → ∀ (m : ℕ), Matrix.mulVec (y ^ m) w = l ^ m • w := by
  intro C _ N y l w h m
  induction m with
  | zero => rw [pow_zero, pow_zero, one_smul, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
end
