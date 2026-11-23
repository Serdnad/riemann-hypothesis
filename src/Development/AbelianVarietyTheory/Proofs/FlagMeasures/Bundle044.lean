module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle031
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle032
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardCokernelUnramifiedOrderMatrixOfDetBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductContinuousOnLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalCharacterSum
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle035
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle036
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesPairingStabilizerBlockDiagonal
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
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnramCard

theorem card_quot_mul {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) (b : R) :
    Nat.card (R ⧸ Ideal.span {a * b}) =
      Nat.card (R ⧸ Ideal.span {a}) * Nat.card (R ⧸ Ideal.span {b}) := by
  have h : Ideal.span {a * b} = a • Ideal.span {b} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Submodule.ideal_span_singleton_smul,
      smul_eq_mul]
  rw [h]
  have hi := Ideal.mulQuot_injective (Ideal.span {b}) ha
  have hs := Ideal.quotOfMul_surjective (a := a) (Ideal.span {b})
  have he := Ideal.exact_mulQuot_quotOfMul (a := a) (Ideal.span {b})
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (Ideal.quotOfMul a (Ideal.span {b}))),
    Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ hs).toEquiv, he.linearMap_ker_eq,
    ← Nat.card_congr (LinearEquiv.ofInjective _ hi).toEquiv, mul_comm]

theorem card_quot_map {R : Type*} [CommRing R] (c : R ≃+* R) (a : R) :
    Nat.card (R ⧸ Ideal.span {c a}) = Nat.card (R ⧸ Ideal.span {a}) := by
  refine (Nat.card_congr (Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {c a}) c ?_).toEquiv).symm
  rw [Ideal.map_span]
  simp

theorem card_quot_eq_pow : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ δ : L.O, IsUnit (δ : E) → 0 ≤ vE L ϖ ((δ : E) * L.cj δ) ∧ Nat.card (L.O ⧸ Ideal.span {δ}) = resQ ϖ ^ (vE L ϖ ((δ : E) * L.cj δ)).toNat := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ δ hδ
  obtain ⟨-, h2, -, -, h5, h6, -, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨-, -, v3, v4⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  obtain ⟨hcm, -, n, hn⟩ := h2 δ δ.2
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hE : Nontrivial E := hinj.nontrivial
  have hn0 : (n : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hn
    exact (hδ.mul (hδ.map L.cj)).ne_zero hn
  rw [hn]
  have hv : 0 ≤ vE L ϖ (algebraMap F E (n : F)) := (v3 _ hn0).2 n.2
  refine ⟨hv, ?_⟩
  obtain ⟨u, hu⟩ := v4 _ hn0
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hv
  rw [hj, zpow_natCast] at hu
  rw [hj, Int.toNat_natCast]
  let c : L.O ≃+* L.O :=
    { toFun := fun x => ⟨L.cj x, GlobalTheory.UnramOrder.cj_mem L x.2⟩
      invFun := fun x => ⟨L.cj x, GlobalTheory.UnramOrder.cj_mem L x.2⟩
      left_inv := fun x => Subtype.ext (L.cj_cj x)
      right_inv := fun x => Subtype.ext (L.cj_cj x)
      map_mul' := fun x y => Subtype.ext (map_mul L.cj (x : E) y)
      map_add' := fun x y => Subtype.ext (map_add L.cj (x : E) y) }
  have hnz : δ ∈ nonZeroDivisors L.O := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have hx' : (x : E) * δ = 0 := by exact_mod_cast congrArg Subtype.val hx
    exact Subtype.ext (hδ.mul_left_eq_zero.1 hx')
  have hmul := card_quot_mul hnz (c δ)
  rw [card_quot_map] at hmul
  let ι : 𝒪[F] →+* L.O :=
    ((algebraMap F E).comp (𝒪[F]).subtype).codRestrict L.O (fun x => (h5 _).2 x.2)
  have hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)} = {ι (ϖ ^ j)} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff]
    rfl
  have hprod : δ * c δ = ι (ϖ ^ j) * ι u := by
    apply Subtype.ext
    change (δ : E) * L.cj δ = algebraMap F E ((ϖ : F) ^ j) * algebraMap F E ((u : 𝒪[F]) : F)
    rw [hn, ← map_mul, ← hu]
  have h7 := h6 j
  rw [hset] at h7
  rw [hprod, Ideal.span_singleton_mul_right_unit (u.isUnit.map ι), h7, two_mul, pow_add] at hmul
  exact (Nat.mul_self_inj.1 hmul).symm

end GlobalTheory.UnramCard
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.haarInvVolume_conj_modular_character : ∀ {G : Type} [Group G] (H K : Subgroup G), K ≤ H → (∀ h ∈ H, K.relIndex (MulAut.conj h • K) ≠ 0 ∧ (MulAut.conj h • K).relIndex K ≠ 0) → (∀ a ∈ H, ∀ b ∈ H, invVol K (MulAut.conj (a * b) • K) = invVol K (MulAut.conj a • K) * invVol K (MulAut.conj b • K)) ∧ (∀ a ∈ H, 0 < invVol K (MulAut.conj a • K)) ∧ (∀ α : G ≃* G, K.map α.toMonoidHom = K → ∀ a ∈ H, invVol K (MulAut.conj (α a) • K) = invVol K (MulAut.conj a • K)) ∧ ∀ K' : Subgroup G, K.relIndex K' ≠ 0 → K'.relIndex K ≠ 0 → ∀ a ∈ H, invVol K (MulAut.conj a • K') = invVol K (MulAut.conj a • K) * invVol K K' ∧ (MulAut.conj a • K' = K' → invVol K (MulAut.conj a • K) = 1) := by
  first | exact @GlobalTheory.HL.invVol_conj_modular | exact GlobalTheory.HL.invVol_conj_modular | (intros; apply GlobalTheory.HL.invVol_conj_modular <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.card_cokernel_unramifiedOrder_matrix_of_det_base : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι L.O) (j : ℕ) (u : (𝒪[F])ˣ), ((A.det : L.O) : E) = algebraMap F E ((ϖ : F) ^ j * ((u : 𝒪[F]) : F)) → Nat.card ((ι → L.O) ⧸ LinearMap.range A.mulVecLin) = resQ ϖ ^ (2 * j) := by
  first | exact @GlobalTheory.UnramOrder.card_coker_of_det_eq | exact GlobalTheory.UnramOrder.card_coker_of_det_eq | (intros; apply GlobalTheory.UnramOrder.card_coker_of_det_eq <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.dual_inter_selfDualHermitianLattice_subspace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → perp L Hm (perp L Hm (Submodule.span E (Set.range y))) = (Submodule.span E (Set.range y)) ∧ (∀ v, (∀ x ∈ Λ, x ∈ perp L Hm (Submodule.span E (Set.range y)) → hf L Hm x v ∈ L.O) ↔ ∃ a ∈ Λ, v - a ∈ (Submodule.span E (Set.range y))) ∧ (∀ v, (∀ x ∈ Λ, x ∈ (Submodule.span E (Set.range y)) → hf L Hm x v ∈ L.O) ↔ ∃ a ∈ Λ, v - a ∈ perp L Hm (Submodule.span E (Set.range y))) ∧ ∃ b : Fin m → Fin n → E, ∃ c : Fin m → Fin n → E, Λ ⊓ (Submodule.span E (Set.range y)).restrictScalars L.O = Submodule.span L.O (Set.range b) ∧ (∀ j, c j ∈ Λ) ∧ ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.HL.DualInter.dual_inter | exact GlobalTheory.HL.DualInter.dual_inter | (intros; apply GlobalTheory.HL.DualInter.dual_inter <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianEichlerProduct_continuous_on_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (X u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (he : ∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) (Λ : Submodule L.O (Fin N → E)) (hΛ : IsLat L Λ) (c : Fˣ), ∃ d : Fˣ, ∀ (u' : Fin r → Fin N → E) (s' : Fin r → E) (e' : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i v, e' i v = eich L Hm (X i) (u' i) (s' i) v) → (∀ i j, ∃ o ∈ L.O, u' i j - u i j = algebraMap F E d * o) → (∀ i, ∃ o ∈ L.O, s' i - s i = algebraMap F E d * o) → ∀ x ∈ Λ, ∃ y ∈ Λ, ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x = algebraMap F E c • y := by
  first | exact @GlobalTheory.HL.EichCont.prod_eich_cont | exact GlobalTheory.HL.EichCont.prod_eich_cont | (intros; apply GlobalTheory.HL.EichCont.prod_eich_cont <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitian_local_character_sum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ψ : AddChar F ℂ), (∀ x : F, ‖ψ x‖ = 1) → (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) → ∀ (UU : Submodule L.O (Fin n → E)), (∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O) → ∀ (ρ : ℕ) (e : Fin ρ → Fin n → E), (∀ a, e a ∈ UU) → (∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) → ∀ (π : E) (j N : ℕ), π ∈ L.O → π * L.cj π = algebraMap F E ((ϖ : F) ^ j) → (∃ c ∈ L.O, algebraMap F E ((ϖ : F) ^ N) = π * c) → ∀ (R : Finset (Fin n → E)) (nrm : (Fin n → E) → F), (∀ u, algebraMap F E (nrm u) = hf L Hm u u) → (∀ u ∈ R, u ∈ UU) → (∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y) → ((R.filter fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c).card : ℝ) = (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) ∧ ∀ (i : ℕ), i ≤ N → ∀ (t : F) (u₀ : (𝒪[F])ˣ), t * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) → ‖∑ u ∈ R.filter (fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c), ψ (t * nrm u)‖ ≤ (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) * (resQ ϖ : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ)) := by
  first | exact @GlobalTheory.HL.DivisibleGauss.share_and_gauss_sum | exact GlobalTheory.HL.DivisibleGauss.share_and_gauss_sum | (intros; apply GlobalTheory.HL.DivisibleGauss.share_and_gauss_sum <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ContAut

theorem relVol_mul {W : Type} [AddCommGroup W] {X Y B : AddSubgroup W}
    (hYX : Y.relIndex X ≠ 0) (hBY : B.relIndex Y ≠ 0) :
    relVol X B = relVol X Y * relVol Y B := by
  have hCY : (B ⊓ Y).relIndex Y ≠ 0 := by rwa [AddSubgroup.inf_relIndex_right]
  have hCX : (B ⊓ Y).relIndex X ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hCY hYX
  have e1 := ContModel.relVol_of_le (W0 := X) (inf_le_left : B ⊓ Y ≤ B) hCX
  have e2 := ContModel.relVol_of_le (W0 := X) (inf_le_right : B ⊓ Y ≤ Y) hCX
  have e3 := ContModel.relVol_of_le (W0 := Y) (inf_le_left : B ⊓ Y ≤ B) hCY
  have e4 : relVol Y (B ⊓ Y) = 1 / ((B ⊓ Y).relIndex Y : ℝ) := by
    unfold relVol
    rw [AddSubgroup.relIndex_eq_one.2 (inf_le_right : B ⊓ Y ≤ Y)]
    simp
  have c : ((B ⊓ Y).relIndex Y : ℝ) ≠ 0 := by exact_mod_cast hCY
  rw [e1, e2, e3, e4]
  field_simp

theorem image_mk {W : Type} [AddCommGroup W] (A : AddSubgroup W) (φ : W ≃+ W) (S : Set W) :
    ∃ f : W ⧸ A → W ⧸ A.map φ.toAddMonoidHom, Function.Injective f ∧
      (QuotientAddGroup.mk : W → W ⧸ A.map φ.toAddMonoidHom) '' (φ '' S)
        = f '' ((QuotientAddGroup.mk : W → W ⧸ A) '' S) := by
  refine ⟨QuotientAddGroup.map A (A.map φ.toAddMonoidHom) φ.toAddMonoidHom
    (AddSubgroup.le_comap_map _ _), ?_, ?_⟩
  · intro u v
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
    intro h
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, QuotientAddGroup.eq] at h
    obtain ⟨a, ha, hh⟩ := h
    rw [QuotientAddGroup.eq]
    have : a = -x + y := φ.injective (by simpa using hh)
    rwa [← this]
  · rw [Set.image_image, Set.image_image]
    rfl

theorem cont_image : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (φ : W ≃+ W), (W0.map φ.toAddMonoidHom).relIndex W0 ≠ 0 → W0.relIndex (W0.map φ.toAddMonoidHom) ≠ 0 → ∀ S, IsCO W0 S → IsCO W0 (φ '' S) ∧ cont W0 (φ '' S) = relVol W0 (W0.map φ.toAddMonoidHom) * cont W0 S := by
  intro W _ W0 φ h1 h2 S ⟨A, hA⟩
  have hi : Function.Injective φ.toAddMonoidHom := φ.injective
  have m1 := AddSubgroup.relIndex_map_map_of_injective A W0 hi
  have m2 := AddSubgroup.relIndex_map_map_of_injective W0 A hi
  obtain ⟨f, hf, him⟩ := image_mk A φ S
  have a1 : (A.map φ.toAddMonoidHom).relIndex (W0.map φ.toAddMonoidHom) ≠ 0 := m1 ▸ hA.1
  have a2 : (W0.map φ.toAddMonoidHom).relIndex (A.map φ.toAddMonoidHom) ≠ 0 := m2 ▸ hA.2.1
  have hG : GoodSub W0 (A.map φ.toAddMonoidHom) (φ '' S) := by
    refine ⟨AddSubgroup.relIndex_ne_zero_trans a1 h1, AddSubgroup.relIndex_ne_zero_trans h2 a2,
      ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨a, ha, rfl⟩
      exact ⟨x + a, hA.2.2.1 x hx a ha, by simp⟩
    · rw [him]; exact hA.2.2.2.image f
  refine ⟨⟨_, hG⟩, ?_⟩
  rw [ContModel.cont_eq hG, ContModel.cont_eq hA, him, Set.ncard_image_of_injective _ hf,
    relVol_mul h1 a1]
  have : relVol (W0.map φ.toAddMonoidHom) (A.map φ.toAddMonoidHom) = relVol W0 A := by
    unfold relVol; rw [m1, m2]
  rw [this]; ring

end GlobalTheory.HL.ContAut
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive : ∀ (G α : Type) [Group G] [MulAction G α] , (∀ (X Y : Set α) (N N' : α → ℝ≥0∞), X ⊆ Y → (∀ x ∈ X, N x ≤ N' x) → orbSum G X N ≤ orbSum G Y N') ∧ (∀ (X : Set α) (B : ℝ≥0∞), orbSum G X (fun _ => B) = B * orbMass G X) ∧ (∀ (ι : Type) (s : Finset ι) (X : Set α) (Xi : ι → Set α) (N : α → ℝ≥0∞), X ⊆ ⋃ i ∈ s, Xi i → orbSum G X N ≤ ∑ i ∈ s, orbSum G (Xi i) N) ∧ (∀ (X : Set α) (s : Set α), (∀ x ∈ X, ∃ y ∈ s, ∃ g : G, g • y = x) → orbMass G X ≤ ((s.encard : ℕ∞) : ℝ≥0∞)) ∧ (∀ (X : Set α) (N N' : α → ℝ≥0∞), orbSum G X (fun x => N x + N' x) = orbSum G X N + orbSum G X N') := by
  first | exact @GlobalTheory.Mass.OrbMono.main | exact GlobalTheory.Mass.OrbMono.main | (intros; apply GlobalTheory.Mass.OrbMono.main <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.Witt

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem mem_perp (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (v : V) :
    v ∈ perp h U ↔ ∀ x ∈ U, h x v = 0 := by
  simp [perp, Submodule.mem_iInf, LinearMap.mem_ker]

private lemma h_sub_smul_sub_smul_eq_of_hww (h : V →ₗ⋆[K] V →ₗ[K] K) (hsym : ∀ a b, star (h a b) = h b a)
    (w : V) (α : K) (hα : α ≠ 0) (hww : h w w = α + star α) (a b : V) :
    h (a - (α⁻¹ * h w a) • w) (b - (α⁻¹ * h w b) • w) = h a b := by
  have hα' : star α ≠ 0 := star_ne_zero.mpr hα
  simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
    starRingEnd_apply]
  rw [← hsym w a, hww, star_mul, star_inv₀]
  field_simp
  ring

theorem exists_isom_move [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x, h x x = 0 → x = 0) (x y : V) (hxy : h x x = h y y) :
    ∃ g ∈ isom h, g x = y ∧ ∀ v, h (x - y) v = 0 → g v = v := by
  have hsym : ∀ a b, star (h a b) = h b a := fun a b => by
    rw [← starRingEnd_apply]; exact hs.eq a b
  have hww : h (x - y) (x - y) = h (x - y) x + star (h (x - y) x) := by
    rw [hsym]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hxy]; ring
  by_cases hα : h (x - y) x = 0
  · have h0 : h (x - y) (x - y) = 0 := by rw [hww, hα, star_zero, add_zero]
    have hxy' : x = y := sub_eq_zero.mp (ha _ h0)
    exact ⟨1, (isom h).one_mem, by simp [hxy'], fun v _ => rfl⟩
  · let f : V →ₗ[K] V :=
      LinearMap.id - LinearMap.smulRight ((h (x - y) x)⁻¹ • h (x - y)) (x - y)
    have hf : ∀ v, f v = v - ((h (x - y) x)⁻¹ * h (x - y) v) • (x - y) := fun v => rfl
    have key : ∀ a b, h (f a) (f b) = h a b := fun a b => by
      rw [hf, hf]; exact h_sub_smul_sub_smul_eq_of_hww h hsym (x - y) _ hα hww a b
    have hinj : Function.Injective f := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha0
      apply ha a
      rw [← key a a, ha0, map_zero]
    let g : V ≃ₗ[K] V := LinearEquiv.ofInjectiveEndo f hinj
    have hg : ∀ v, g v = f v := fun v => rfl
    refine ⟨g, fun a b => by rw [hg, hg, key], ?_, fun v hv => ?_⟩
    · rw [hg, hf, inv_mul_cancel₀ hα, one_smul, sub_sub_cancel]
    · rw [hg, hf, hv, mul_zero, zero_smul, sub_zero]

theorem exists_isom_finset [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x, h x x = 0 → x = 0) {ι : Type} (a b : ι → V)
    (hab : ∀ i j, h (b i) (b j) = h (a i) (a j)) (t : Finset ι) :
    ∃ g ∈ isom h, ∀ i ∈ t, g (a i) = b i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, (isom h).one_mem, by simp⟩
  | insert j s hj ih =>
    obtain ⟨g, hg, hgs⟩ := ih
    have hg' : ∀ u v, h (g u) (g v) = h u v := hg
    have hgx : h (g (a j)) (g (a j)) = h (b j) (b j) := by rw [hg', hab]
    obtain ⟨k, hk, hkx, hkfix⟩ := exists_isom_move h hs ha (g (a j)) (b j) hgx
    refine ⟨k * g, (isom h).mul_mem hk hg, fun i hi => ?_⟩
    show k (g (a i)) = b i
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hkx
    · rw [hgs i hi]
      apply hkfix
      have e1 : h (g (a j)) (b i) = h (b j) (b i) :=
        calc h (g (a j)) (b i) = h (g (a j)) (g (a i)) := by rw [hgs i hi]
          _ = h (a j) (a i) := hg' _ _
          _ = h (b j) (b i) := (hab j i).symm
      rw [map_sub, LinearMap.sub_apply, e1, sub_self]

theorem isCompl_perp [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (ha : ∀ x, h x x = 0 → x = 0) (U : Submodule K V) : IsCompl U (perp h U) := by
  have hdis : Disjoint U (perp h U) := by
    rw [Submodule.disjoint_def]
    intro x hxU hxP
    exact ha x (((mem_perp h U x).1 hxP) x hxU)
  let bU := Module.finBasis K U
  let T : V →ₗ[K] (Fin (Module.finrank K U) → K) := LinearMap.pi fun i => h (bU i : V)
  have hker : LinearMap.ker T ≤ perp h U := by
    intro v hv
    rw [mem_perp]
    intro x hx
    have hv' : ∀ i, h (bU i : V) v = 0 := fun i => by
      have := congrFun (LinearMap.mem_ker.mp hv) i
      simpa [T] using this
    have hx' : x = ∑ i, (bU.repr ⟨x, hx⟩ i) • (bU i : V) := by
      have e := congrArg Subtype.val (bU.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e
      exact e.symm

    rw [hx', map_sum, LinearMap.sum_apply]
    simp [hv']
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  have h2 : Module.finrank K (LinearMap.range T) ≤ Module.finrank K U := by
    simpa using Submodule.finrank_le (LinearMap.range T)
  have h3 := Submodule.finrank_mono hker
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq U (perp h U)
  rw [hdis.eq_bot, finrank_bot] at h4
  refine ⟨hdis, ?_⟩
  rw [codisjoint_iff]
  apply Submodule.eq_top_of_finrank_eq
  have h5 := Submodule.finrank_le (U ⊔ perp h U)
  omega

theorem perp_perp [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x, h x x = 0 → x = 0) (U : Submodule K V) : perp h (perp h U) = U := by
  have hle : U ≤ perp h (perp h U) := by
    intro u hu
    rw [mem_perp]
    intro w hw
    have h0 : h u w = 0 := (mem_perp h U w).1 hw u hu
    rw [← hs.eq u w, h0, map_zero]
  have c1 := Submodule.finrank_add_eq_of_isCompl (isCompl_perp h ha U)
  have c2 := Submodule.finrank_add_eq_of_isCompl (isCompl_perp h ha (perp h U))
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem witt_definite : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ U U' : Submodule K V, ∀ e : U ≃ₗ[K] U', (∀ x y, h (e x : V) (e y : V) = h (x : V) (y : V)) → ∃ g ∈ isom h, ∀ x : U, g (x : V) = (e x : V)) ∧ ∀ U : Submodule K V, IsCompl U (perp h U) ∧ (hRes h U).IsSymm ∧ PD (hRes h U) ∧ perp h (perp h U) = U := by
  intro K V _ _ _ _ _ _ _ _ h _ hs hpd
  have ha : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpd τ x hne
    rw [hx, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨?_, fun U => ⟨isCompl_perp h ha U, ?_, ?_, perp_perp h hs ha U⟩⟩
  · intro U U' e he
    let bU := Module.finBasis K U
    obtain ⟨g, hg, hgb⟩ := exists_isom_finset h hs ha (fun i => (bU i : V))
      (fun i => (e (bU i) : V)) (fun i j => he _ _) Finset.univ
    refine ⟨g, hg, fun x => ?_⟩
    have hcomp : (g : V →ₗ[K] V).comp U.subtype = U'.subtype.comp (e : U →ₗ[K] U') := by
      apply bU.ext
      intro i
      simpa using hgb i (Finset.mem_univ i)
    exact LinearMap.congr_fun hcomp x
  · exact ⟨fun x y => hs.eq x y⟩
  · intro τ x hx
    show 0 < (τ (h x x)).re
    exact hpd τ x (fun h0 => hx (Subtype.ext h0))

end GlobalTheory.Mass.Witt
end

section

open GlobalTheory.IdxInt
open scoped Pointwise Classical

theorem _root_.GlobalTheory.T.indexMeasureIntegral_prod_fubini : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] (A : AddSubgroup W) (A' : AddSubgroup W') (φ : W × W' → ℂ), Nice (A.prod A') φ → (∀ w, Nice A' (fun w' => φ (w, w'))) ∧ Nice A (fun w => cint A' (fun w' => φ (w, w'))) ∧ cint (A.prod A') φ = cint A (fun w => cint A' (fun w' => φ (w, w'))) := by
  first | exact @GlobalTheory.IdxInt.Fubini.cint_prod | exact GlobalTheory.IdxInt.Fubini.cint_prod | (intros; apply GlobalTheory.IdxInt.Fubini.cint_prod <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFrames_pairingStabilizer_blockDiagonal : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s → IsUni s' → cT L s * S.Zh * s' = S.Zh → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0 ∧ s' i j = 0) ∧ (IsIntM L s ↔ IsIntM L s')) ∧ ∀ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0) → ∃ s', IsUni s' ∧ cT L s * S.Zh * s' = S.Zh := by
  first | exact @GlobalTheory.HL.BlockStab.stabiliser_blockDiag | exact GlobalTheory.HL.BlockStab.stabiliser_blockDiag | (intros; apply GlobalTheory.HL.BlockStab.stabiliser_blockDiag <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianDoubleCosetFrames_level_le_iff_congr_flagSteps : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k) (g g' : Fin (r + 1) → S.V), ∀ y ∈ S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1), ∀ j : ℕ, S.lev g g' (algebraMap F E S.th • y) ≤ j ↔ ∃ y₁ ∈ S.spanTo g j ⊔ S.spanTo g' j, y - y₁ ∈ S.Mof g g' := by
  first | exact @GlobalTheory.FrameLevel.main | exact GlobalTheory.FrameLevel.main | (intros; apply GlobalTheory.FrameLevel.main <;> assumption)
end
