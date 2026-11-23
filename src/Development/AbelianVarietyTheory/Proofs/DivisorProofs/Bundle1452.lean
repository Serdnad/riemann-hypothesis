module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.KapOrb

theorem entry_mem_of_mem_GLint {L : Type} [Field L] {n : ℕ} {O : Subring L} {k : GL (Fin n) L}
    (hk : k ∈ GLint (Fin n) O) (i j : Fin n) : (k : Matrix (Fin n) (Fin n) L) i j ∈ O := by
  obtain ⟨k0, rfl⟩ := hk
  exact (k0.val i j).2

theorem mulVec_mem_of_mem_GLint {L : Type} [Field L] {n : ℕ} {O : Subring L} {k : GL (Fin n) L}
    (hk : k ∈ GLint (Fin n) O) {v : Fin n → L} (hv : ∀ i, v i ∈ O) (i : Fin n) :
    ((k : Matrix (Fin n) (Fin n) L) *ᵥ v) i ∈ O := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (entry_mem_of_mem_GLint hk i j) (hv j)

theorem pullLat_mul_of_mem_KGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g k : GLw n w), k ∈ GlobalTheory.LFun.KGL w (n := n) → pullLat w B ψ (g * k) = pullLat w B ψ g := by
  intro E _ _ _ w K B n ψ g k hk
  have hk' : k⁻¹ ∈ GlobalTheory.LFun.KGL w (n := n) := inv_mem hk
  ext y
  show (∀ (c : K.O) (i : Fin n), (((g * k)⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E) ↔
    (∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E)
  simp only [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · intro h c i
    have e : (g⁻¹ : GLw n w).val *ᵥ ψ (c • y) =
        (k : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *ᵥ ((k⁻¹ : GLw n w).val *ᵥ ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y))) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]
    exact mulVec_mem_of_mem_GLint hk (fun j => h c j) i
  · intro h c i
    exact mulVec_mem_of_mem_GLint hk' (fun j => h c j) i

end GlobalTheory.KapOrb
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapCong

theorem mem_GLint_of_entries {L : Type} [Field L] {n : ℕ} {O : Subring L} {x : GL (Fin n) L}
    (h1 : ∀ i j, x.1 i j ∈ O) (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) : x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem pullLat_stable_iff_cong : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), IsModelMap w e B u x γ ψ → u = 1 + algebraMap K.O B.A t * B.g → γ ∈ UL n w → ∀ g ∈ UL n w, ((∀ y ∈ pullLat w B ψ g, B.g * y ∈ pullLat w B ψ g) ↔ g⁻¹ * γ * g ∈ congSet w n k) := by
  intro E _ _ _ w hns K e hB k t ht hval B u x n γ ψ hψ hu hγ g hg
  obtain ⟨hsemi, hmul, -⟩ := hψ
  obtain ⟨hBc, hBint, hBval, -⟩ := hB
  have hO : ∀ z : w.adicCompletion E, z ∈ w.adicCompletionIntegers E ↔ Valued.v z ≤ 1 :=
    fun z => HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w
  have heO : ∀ c : K.O, e (algebraMap K.O K.E c) ∈ w.adicCompletionIntegers E :=
    fun c => (hO _).2 ((hBint _).1 ⟨c, rfl⟩)
  have hcjO : ∀ z ∈ w.adicCompletionIntegers E, cj w z ∈ w.adicCompletionIntegers E := by
    intro z hz
    obtain ⟨o, ho⟩ := (hBint (e.symm z)).2 (by rw [e.apply_symm_apply]; exact (hO z).1 hz)
    obtain ⟨o', ho'⟩ := K.c_int o
    have h2 : cj w z = e (algebraMap K.O K.E o') := by
      rw [← ho', ho, hBc, e.apply_symm_apply]
    rw [h2]; exact heO o'
  obtain ⟨et, het⟩ : ∃ et, e (algebraMap K.O K.E t) = et := ⟨_, rfl⟩
  have het0 : et ≠ 0 := by
    rw [← het]; intro h0
    apply ht.1
    have h1 : algebraMap K.O K.E t = 0 := e.injective (h0.trans (map_zero e).symm)
    exact IsFractionRing.injective K.O K.E (h1.trans (map_zero _).symm)
  have hvet : Valued.v et = WithZero.exp (-(k : ℤ)) := by
    have h1 := hBval (algebraMap K.O K.E t)
    rw [hval, het] at h1
    have hv0 : Valued.v et ≠ 0 := (Valuation.ne_zero_iff _).2 het0
    unfold ordL at h1
    rw [dite_eq_right hv0] at h1
    rw [← WithZero.coe_unzero hv0, WithZero.exp]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    omega
  have hkey : ∀ y, ψ (B.g * y) = et⁻¹ • (γ.val *ᵥ ψ y - ψ y) := by
    intro y
    have h1 := hmul y
    rw [hu, add_mul, one_mul, mul_assoc, map_add (f := _), IsScalarTower.algebraMap_apply K.O K.E B.A, ← Algebra.smul_def,
      hsemi, het] at h1
    rw [← h1, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ het0, one_smul]
  have hmem : ∀ (h : GLw n w) y, y ∈ pullLat w B ψ h ↔
      ∀ i, ((h⁻¹ : GLw n w).val *ᵥ ψ y) i ∈ w.adicCompletionIntegers E := by
    intro h y
    constructor
    · intro hy i
      have h1 : ((h⁻¹ : GLw n w).val *ᵥ ψ ((1 : K.O) • y)) i ∈ w.adicCompletionIntegers E := hy 1 i
      rwa [one_smul] at h1
    · intro hy c i
      show ((h⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ _
      rw [← IsScalarTower.algebraMap_smul K.E c y, hsemi, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact mul_mem (heO c) (hy i)
  have hgg : (g⁻¹ * γ * g : GLw n w).val * (g⁻¹ : GLw n w).val = (g⁻¹ : GLw n w).val * γ.val := by
    rw [← Units.val_mul, mul_inv_cancel_right, Units.val_mul]
  have hG : ∀ y, (g⁻¹ : GLw n w).val *ᵥ ψ (B.g * y) =
      et⁻¹ • (((g⁻¹ * γ * g : GLw n w).val - 1) *ᵥ ((g⁻¹ : GLw n w).val *ᵥ ψ y)) := by
    intro y
    rw [hkey, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec (ψ y) ((g⁻¹ * γ * g : GLw n w).val), hgg]
  have hinvg : ∀ v : Fin n → w.adicCompletion E, (g⁻¹ : GLw n w).val *ᵥ (g.val *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hP : (∀ y ∈ pullLat w B ψ g, B.g * y ∈ pullLat w B ψ g) ↔
      ∀ v : Fin n → w.adicCompletion E, (∀ i, v i ∈ w.adicCompletionIntegers E) →
        ∀ i, (et⁻¹ • (((g⁻¹ * γ * g : GLw n w).val - 1) *ᵥ v)) i ∈ w.adicCompletionIntegers E := by
    constructor
    · intro H v hv i
      have hy : ψ.symm (g.val *ᵥ v) ∈ pullLat w B ψ g := by
        rw [hmem]; intro j; rw [ψ.apply_symm_apply, hinvg]; exact hv j
      have h1 := (hmem g _).1 (H _ hy) i
      rwa [hG, ψ.apply_symm_apply, hinvg] at h1
    · intro H y hy
      rw [hmem] at hy ⊢
      intro i; rw [hG]; exact H _ hy i
  have hent : ∀ z, et⁻¹ * z ∈ w.adicCompletionIntegers E ↔ Valued.v z ≤ WithZero.exp (-(k : ℤ)) := by
    intro z
    rw [hO, map_mul, map_inv₀, hvet]
    exact inv_mul_le_one₀ (WithZero.exp_pos)
  have hPQ : (∀ v : Fin n → w.adicCompletion E, (∀ i, v i ∈ w.adicCompletionIntegers E) →
        ∀ i, (et⁻¹ • (((g⁻¹ * γ * g : GLw n w).val - 1) *ᵥ v)) i ∈ w.adicCompletionIntegers E) ↔
      ∀ i j, Valued.v (((g⁻¹ * γ * g : GLw n w).val - 1) i j) ≤ WithZero.exp (-(k : ℤ)) := by
    constructor
    · intro H i j
      have h1 := H (Pi.single j 1) (fun l => by
        rw [Pi.single_apply]; split_ifs
        · exact one_mem _
        · exact zero_mem _) i
      rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one] at h1
      change et⁻¹ * ((g⁻¹ * γ * g : GLw n w).val - 1) i j ∈ _ at h1
      rwa [hent] at h1
    · intro H v hv i
      rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine sum_mem fun j _ => ?_
      rw [← mul_assoc]
      exact mul_mem ((hent _).2 (H i j)) (hv j)
  rw [hP, hPQ]
  constructor
  · intro H
    refine ⟨?_, fun i j => by simpa [Matrix.sub_apply] using H i j⟩
    have hγ' : g⁻¹ * γ * g ∈ UL n w := mul_mem (mul_mem (inv_mem hg) hγ) hg
    unfold UL at hγ'
    rw [if_neg hns] at hγ'
    have hU : cT (cj w) (g⁻¹ * γ * g : GLw n w).val * 1 * (g⁻¹ * γ * g : GLw n w).val = 1 := hγ'
    rw [Matrix.mul_one] at hU
    have hinv : ((g⁻¹ * γ * g)⁻¹ : GLw n w).val = cT (cj w) (g⁻¹ * γ * g : GLw n w).val :=
      Units.inv_eq_of_mul_eq_one_left hU
    have hint : ∀ i j, (g⁻¹ * γ * g : GLw n w).val i j ∈ w.adicCompletionIntegers E := by
      intro i j
      have h1 : (g⁻¹ * γ * g : GLw n w).val i j =
          ((g⁻¹ * γ * g : GLw n w).val - 1) i j + (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
        rw [Matrix.sub_apply, sub_add_cancel]
      rw [h1]
      refine add_mem ((hO _).2 ((H i j).trans ((WithZero.exp_le_exp.2 (by omega)).trans_eq WithZero.exp_zero))) ?_
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    refine mem_GLint_of_entries (fun i j => hint i j) (fun i j => ?_)
    rw [hinv]
    exact hcjO _ (hint j i)
  · intro H i j
    simpa [Matrix.sub_apply] using H.2 i j

end GlobalTheory.KapCong
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

noncomputable def mulMatHom : B.A →+* Matrix (Fin m) (Fin m) (w.adicCompletion E) :=
  (e : K.E →+* w.adicCompletion E).mapMatrix.comp
    ((LinearMap.toMatrixAlgEquiv b).toRingHom.comp (Algebra.lmul K.E B.A).toRingHom)

theorem mulMatHom_apply (a : B.A) : mulMatHom e b a = mulMat e b a := by
  rw [mulMat_eq_map]
  simp only [mulMatHom, RingHom.comp_apply]
  congr 1

theorem mulMatHom_algebraMap (x : K.E) :
    mulMatHom e b (algebraMap K.E B.A x) = algebraMap (w.adicCompletion E) _ (e x) := by
  simp only [mulMatHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgEquiv.coe_toRingEquiv,
    RingEquiv.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  rw [Matrix.algebraMap_eq_diagonal, Matrix.algebraMap_eq_diagonal]
  simp [Pi.algebraMap_def]

theorem mulMatHom_injective : Function.Injective (mulMatHom e b) := by
  intro a a' h
  rw [mulMatHom_apply, mulMatHom_apply] at h
  exact mulMat_injective e b h

theorem isIntegral_of_isIntegral_mulMat
    (hint : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (a : B.A)
    (h : IsIntegral (w.adicCompletionIntegers E) (mulMat e b a)) : IsIntegral K.O a := by
  obtain ⟨p, hpm, hp⟩ := h
  set Q : (w.adicCompletion E)[X] := p.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) with hQdef
  have hQ : aeval (mulMat e b a) Q = 0 := by
    rw [hQdef, aeval_map_algebraMap]; exact hp
  set Q' : K.E[X] := Q.map e.symm.toRingHom with hQ'def
  have hQQ : Q'.map (e : K.E →+* w.adicCompletion E) = Q := by
    rw [hQ'def, Polynomial.map_map]
    convert Polynomial.map_id
    ext x; simp
  have hu : aeval a Q' = 0 := by
    apply mulMatHom_injective e b
    rw [map_zero, aeval_def, Polynomial.hom_eval₂]
    have hc : (mulMatHom e b).comp (algebraMap K.E B.A) =
        (algebraMap (w.adicCompletion E) (Matrix (Fin m) (Fin m) (w.adicCompletion E))).comp
          (e : K.E →+* w.adicCompletion E) := by
      ext x; simp [mulMatHom_algebraMap]
    rw [hc, ← Polynomial.eval₂_map, hQQ, mulMatHom_apply, ← aeval_def]
    exact hQ
  have hlift : Q' ∈ Polynomial.lifts (algebraMap K.O K.E) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [hQ'def, Polynomial.coeff_map, hQdef, Polynomial.coeff_map]
    have hv : Valued.v (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) (p.coeff i)) ≤ 1 :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (p.coeff i).2
    have := (hint (e.symm (algebraMap _ _ (p.coeff i)))).2 (by simpa using hv)
    simpa using this
  obtain ⟨P, hPm, -, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift (by rw [hQ'def]; exact (hpm.map _).map _)
  refine ⟨P, hPmon, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K.E, hPm]
  exact hu

theorem mem_intUnits_of_isCompact_closure_zpowers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (a : B.Aˣ), IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwLat.mulU e b a) : Set (GLw m w))) → a ∈ GlobalTheory.UnitLemma.intUnits K.O B.A := by
  intro E _ _ _ _ w _ K e _ hint _ B m b a hc
  have h1 : IsIntegral (w.adicCompletionIntegers E) (mulMat e b (a : B.A)) := by
    rw [← mulU_val]
    exact GlobalTheory.isIntegral_of_isCompact_closure_zpowers E w m _ hc
  have hc' : IsCompact (closure (Subgroup.zpowers (mulU e b a⁻¹) : Set (GLw m w))) := by
    rw [map_inv, Subgroup.zpowers_inv]; exact hc
  have h2 : IsIntegral (w.adicCompletionIntegers E) (mulMat e b ((a⁻¹ : B.Aˣ) : B.A)) := by
    rw [← mulU_val]
    exact GlobalTheory.isIntegral_of_isCompact_closure_zpowers E w m _ hc'
  exact ⟨isIntegral_of_isIntegral_mulMat e b hint _ h1, isIntegral_of_isIntegral_mulMat e b hint _ h2⟩

end GlobalTheory.TwLat
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.IntCpt

open IsDedekindDomain.HeightOneSpectrum

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

theorem entries_le_one (hint : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1)
    (g : GLw m w) (x : B.A) (hx : ∀ y ∈ GlobalTheory.TwLat.lat e b g, x * y ∈ GlobalTheory.TwLat.lat e b g) (i j : Fin m) :
    Valued.v (((g⁻¹).val * GlobalTheory.TwLat.mulMat e b x * g.val) i j) ≤ 1 := by
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin m) (Fin m) (w.adicCompletion E),
      Y = (g⁻¹).val * GlobalTheory.TwLat.mulMat e b x * g.val := ⟨_, rfl⟩
  rw [← hY]
  have hgY : g.val * Y = GlobalTheory.TwLat.mulMat e b x * g.val := by
    rw [hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hgcol : ∀ j, x * Lv.col e b g.val j = ∑ l, e.symm (Y l j) • Lv.col e b g.val l := by
    intro j
    rw [Lv.mul_col, ← hgY]
    apply b.repr.injective
    ext i
    rw [Lv.repr_sum_smul_col, Lv.repr_col]
    simp only [RingEquiv.apply_symm_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hmem : x * Lv.col e b g.val j ∈ GlobalTheory.TwLat.lat e b g := hx _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun K.O).mp hmem
  have ho' : ∑ l, algebraMap K.O K.E (o l) • Lv.col e b g.val l = ∑ l, e.symm (Y l j) • Lv.col e b g.val l := by
    rw [← hgcol j, ← ho]
    exact Finset.sum_congr rfl fun l _ => algebraMap_smul K.E (o l) _
  have := congrFun (Lv.sum_smul_col_inj e b g _ _ ho') i
  have hi := (hint (algebraMap K.O K.E (o i))).mp ⟨o i, rfl⟩
  rw [this, RingEquiv.apply_symm_apply] at hi
  exact hi

theorem isCompact_intGL :
    IsCompact {h : GLw m w | (∀ i j, Valued.v (h.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((h⁻¹).val i j) ≤ 1} := by
  have hO : IsCompact ((w.adicCompletionIntegers E).toSubring : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers E w)
  have := GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint (n := Fin m) _ hO
  rw [GlobalTheory.LFun.IntPtsUnitary.coe_GLint] at this
  convert this using 1
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, ValuationSubring.mem_toSubring, mem_adicCompletionIntegers]

def unitsIn (R : Subalgebra K.O B.A) : Subgroup B.Aˣ where
  carrier := {u | (u : B.A) ∈ R ∧ ((u⁻¹ : B.Aˣ) : B.A) ∈ R}
  one_mem' := by simp [R.one_mem]
  mul_mem' := by
    intro u v hu hv
    refine ⟨by simpa using R.mul_mem hu.1 hv.1, ?_⟩
    rw [_root_.mul_inv_rev, Units.val_mul]
    exact R.mul_mem hv.2 hu.2
  inv_mem' := by
    intro u hu
    exact ⟨hu.2, by simpa using hu.1⟩

end GlobalTheory.TwLat.IntCpt

namespace GlobalTheory.TwLat

open IsDedekindDomain.HeightOneSpectrum

theorem isCompact_closure_zpowers_mulU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (a : B.Aˣ), a ∈ GlobalTheory.UnitLemma.intUnits K.O B.A → IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwLat.mulU e b a) : Set (GLw m w))) := by
  intro E _ _ _ hU w hw K e hc hint hval B m b a ha
  let R : Subalgebra K.O B.A := Algebra.adjoin K.O {(a : B.A), ((a⁻¹ : B.Aˣ) : B.A)}
  haveI : Module.Finite K.O R := by
    apply Algebra.finite_adjoin_of_finite_of_isIntegral (Set.toFinite _)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha.1
    · exact ha.2
  let L : Submodule K.O B.A := (Submodule.span R (Set.range b)).restrictScalars K.O
  have hLfg : L.FG := Submodule.FG.restrictScalars (Submodule.fg_span (Set.finite_range b))
  have hbL : ∀ i, b i ∈ L := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hLsp : Submodule.span K.E (L : Set B.A) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (hbL i)
  have hLst : ∀ x ∈ R, ∀ y ∈ L, x * y ∈ L := by
    intro x hx y hy
    exact (Submodule.span R (Set.range b)).smul_mem (⟨x, hx⟩ : R) hy
  obtain ⟨g, hg⟩ := GlobalTheory.TwLat.exists_GLw_lat_eq E hU w hw K e hc hint hval B m b L ⟨hLfg, hLsp⟩
  have haH : a ∈ IntCpt.unitsIn R :=
    ⟨Algebra.subset_adjoin (Set.mem_insert _ _), Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)⟩
  let S : Set (GLw m w) := {h | (∀ i j, Valued.v (h.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((h⁻¹).val i j) ≤ 1}
  have hC : IsCompact ((fun h => g * h * g⁻¹) '' S) :=
    (IntCpt.isCompact_intGL (w := w) (m := m)).image (by fun_prop)
  have hsub : (Subgroup.zpowers (mulU e b a) : Set (GLw m w)) ⊆ (fun h => g * h * g⁻¹) '' S := by
    rintro _ ⟨k, rfl⟩
    have hu : a ^ k ∈ IntCpt.unitsIn R := zpow_mem haH k
    refine ⟨g⁻¹ * mulU e b (a ^ k) * g, ⟨?_, ?_⟩, ?_⟩
    · intro i j
      have := IntCpt.entries_le_one e b hint g _ (hg ▸ hLst _ hu.1) i j
      rw [Units.val_mul, Units.val_mul, mulU_val]
      exact this
    · intro i j
      have := IntCpt.entries_le_one e b hint g _ (hg ▸ hLst _ hu.2) i j
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← map_inv (mulU e b), ← mul_assoc, Units.val_mul,
        Units.val_mul, mulU_val]
      exact this
    · show g * (g⁻¹ * mulU e b (a ^ k) * g) * g⁻¹ = mulU e b a ^ k
      rw [map_zpow]
      group
  exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)

end GlobalTheory.TwLat
end
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem polEval_pderiv :
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [DecidableEq ι] (m d : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V), (∀ i j, d i * m j - m j * d i = if i = j then 1 else 0) →
    (∀ i, d i f₀ = 0) → ∀ (i : ι) (p : MvPolynomial ι ℂ),
      GlobalTheory.CCRFock.polEval m hm f₀ (MvPolynomial.pderiv i p) = d i (GlobalTheory.CCRFock.polEval m hm f₀ p) := by
  intro V _ _ ι _ m d hm f₀ hc h0 i p
  have hX : ∀ (j : ι) (q : MvPolynomial ι ℂ),
      polEval m hm f₀ (MvPolynomial.X j * q) = m j (polEval m hm f₀ q) := by
    intro j q
    simp [polEval, Module.End.mul_apply]
  have h1 : polEval m hm f₀ 1 = f₀ := by simp [polEval]
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hC : (MvPolynomial.C a : MvPolynomial ι ℂ) = a • (1 : MvPolynomial ι ℂ) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [MvPolynomial.pderiv_C, map_zero, hC, map_smul, h1, map_smul, h0, smul_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X q j hq =>
    have hv := LinearMap.congr_fun (hc i j) (polEval m hm f₀ q)
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_eq_iff_eq_add] at hv
    rw [mul_comm q, MvPolynomial.pderiv_mul, map_add (f := _), hX, hX, hq, hv]
    congr 1
    by_cases hij : i = j
    · subst hij
      simp
    · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij)]
      simp [hij]

end GlobalTheory.CCRFock
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

theorem _root_.GlobalTheory.T.self_dual_lattice_standard_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ L : Submodule K.O B.A, IsLat K.O K.E L → (∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) → ∃ q : UL n w, unitLat e B ψ q = L := by
  first | exact @GlobalTheory.InertUnitOrb.LatOnto.exists_unitLat_eq | exact GlobalTheory.InertUnitOrb.LatOnto.exists_unitLat_eq | (intros; apply GlobalTheory.InertUnitOrb.LatOnto.exists_unitLat_eq <;> assumption)
end
