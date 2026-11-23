module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle609
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle508
import Formalism.AdmissibleDesigns.InvariantsEqBotIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp

private def tinv {Γ R : Type} [Group Γ] [CommRing R] {n : ℕ} (r : Γ →* GL (Fin n) R) : Γ →* GL (Fin n) R where
  toFun s := ⟨((r s)⁻¹).val.transpose, (r s).val.transpose,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' s t := by
    apply Units.ext
    simp [Matrix.transpose_mul]

private theorem tinv_val {Γ R : Type} [Group Γ] [CommRing R] {n : ℕ} (r : Γ →* GL (Fin n) R) (s : Γ) :
    (tinv r s).val = (r s⁻¹).val.transpose := by
  rw [map_inv]
  rfl

private theorem dot_symm {L Γ : Type} [Field L] [Group Γ] {n : ℕ} (ρ ρ' : Representation L Γ (Fin n → L))
    (h : ∀ g x y, x ⬝ᵥ ρ g⁻¹ y = ρ' g x ⬝ᵥ y) (g : Γ) (φ : Module.Dual L (Fin n → L)) :
    (dotProductEquiv L (Fin n)).symm (ρ.dual g φ) = ρ' g ((dotProductEquiv L (Fin n)).symm φ) := by
  obtain ⟨x, rfl⟩ := (dotProductEquiv L (Fin n)).surjective φ
  apply (dotProductEquiv L (Fin n)).injective
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  refine LinearMap.ext fun y => ?_
  exact h g x y

theorem UpperTheory.potentiallyCrystalline_contragredient :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
        (r r' : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω),
        (∀ s, (r' s).val = ((r s)⁻¹).val.transpose) → UpperTheory.V.Af.PotCrysAt r A → UpperTheory.V.Af.PotCrysAt r' A := by
  intro F Ω _ _ _ _ _ l _ n r r' A h hp
  obtain ⟨O, i1, i2, i3, Bw, hj, L₁, r₁, hm, K', hK, hc⟩ := hp
  refine ⟨O, i1, i2, i3, Bw, hj, L₁, tinv r₁, ⟨hm.1, ?_⟩, K', hK, ?_⟩
  · refine MonoidHom.ext fun g => Units.ext ?_
    have e1 : r (g : G F Ω)⁻¹ = Formalism.MainNotions.N.mapRep (algebraMap ↥L₁.1 (Formalism.BasicNotions.Loc.Om l)) r₁ g⁻¹ :=
      (DFunLike.congr_fun hm.2 g⁻¹).symm
    have e2 : ((r' (g : G F Ω)) : Matrix (Fin n) (Fin n) (Qbar l)) = (r (g : G F Ω)⁻¹).val.transpose := by
      rw [h, map_inv]
    change (algebraMap ↥L₁.1 (Formalism.BasicNotions.Loc.Om l)).mapMatrix (tinv r₁ g).val = (r' (g : G F Ω)).val
    rw [e2, e1, tinv_val]
    rfl
  · obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
    have := L₁.2
    have hd := GlobalTheory.Per.TiedDual.tied_isCrys_dual l (UpperTheory.V.Loc.PP l) (UpperTheory.V.Loc.AIP l) T
      (GlobalTheory.T.periodRings_regular_phi_surjective_fil l _ _ T).1 K' L₁ _ _ hc
    refine Formalism.MainNotions.N.K.Norm.isCrys_congr _ (dotProductEquiv ↥L₁.1 (Fin n)).symm
      (dot_symm _ _ fun g x y => ?_) hd
    change x ⬝ᵥ (Bw.repE L₁ r₁ _ y) = (Bw.repE L₁ (tinv r₁) _ x) ⬝ᵥ y
    rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, tinv_val, Matrix.mulVec_transpose,
      Matrix.dotProduct_mulVec, map_inv, map_inv, map_inv]
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base
open scoped Pointwise

private theorem fixAux {K Ω : Type} [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (u : G ℚ Ω) (c : G K Ω ≃* G K Ω)
    (hc : ∀ s, galEmb ℚ K Ω (c s) = u * galEmb ℚ K Ω s * u⁻¹) (x : K) :
    ∃ y : K, algebraMap K Ω y = u (algebraMap K Ω x) := by
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  have h1 : u (algebraMap K Ω x) ∈ (⊥ : IntermediateField K Ω) := by
    rw [← InfiniteGalois.fixedField_bot, IntermediateField.mem_fixedField_iff]
    intro s _
    obtain ⟨t, rfl⟩ := c.surjective s
    have h2 : (c t) (u (algebraMap K Ω x)) = (u * galEmb ℚ K Ω t * u⁻¹) (u (algebraMap K Ω x)) :=
      DFunLike.congr_fun (hc t) _
    have h3 : (galEmb ℚ K Ω t) (algebraMap K Ω x) = algebraMap K Ω x := t.commutes x
    rw [h2]
    simp [h3]
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 h1
  exact ⟨y, hy⟩

private theorem mem_decomposition_conj_iff {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (u : G ℚ Ω) (A A' : ValuationSubring Ω)
    (hu : ∀ x, x ∈ A' ↔ u x ∈ A) (t : G ℚ Ω) :
    t ∈ Dec (F := ℚ) A' ↔ u * t * u⁻¹ ∈ Dec (F := ℚ) A := by
  have hgA : u • A' = A := by
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hu]
    simp [AlgEquiv.smul_def]
  rw [mem_Dec, mem_Dec, ← hgA, mul_smul, inv_smul_smul, mul_smul, smul_left_cancel_iff]

private theorem partialTrace_valuation_sum {K Ω : Type} [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (u : G ℚ Ω) (c : G K Ω ≃* G K Ω) (hc : ∀ s, galEmb ℚ K Ω (c s) = u * galEmb ℚ K Ω s * u⁻¹)
    (r : G K Ω →* GL (Fin n) (Qbar l)) (A A' : ValuationSubring Ω) (hu : ∀ x, x ∈ A' ↔ u x ∈ A)
    (hA : PotCrysAt r A) : PotCrysAt (r.comp c.toMonoidHom) A' := by
  obtain ⟨O, i1, i2, i3, Bw, hj, LL', r', ⟨hle, hmap⟩, K', hK', hcr⟩ := hA
  have hc' : ∀ s, galEmb ℚ K Ω (c.symm s) = u⁻¹ * galEmb ℚ K Ω s * u := fun s => by
    have h := hc (c.symm s)
    rw [c.apply_symm_apply] at h
    rw [h]; group
  have hmem : ∀ s : G K Ω, s ∈ Dec (F := K) A' ↔ c s ∈ Dec (F := K) A := fun s => by
    change galEmb ℚ K Ω s ∈ Dec (F := ℚ) A' ↔ galEmb ℚ K Ω (c s) ∈ Dec (F := ℚ) A
    rw [hc]
    exact mem_decomposition_conj_iff u A A' hu _
  let φ : ↥(Dec (F := K) A') ≃* ↥(Dec (F := K) A) :=
    { toFun := fun s => ⟨c s, (hmem s).1 s.2⟩
      invFun := fun t => ⟨c.symm t, (hmem _).2 (by rw [c.apply_symm_apply]; exact t.2)⟩
      left_inv := fun s => Subtype.ext (c.symm_apply_apply _)
      right_inv := fun t => Subtype.ext (c.apply_symm_apply _)
      map_mul' := fun s t => Subtype.ext (map_mul c _ _) }
  have hemb := (galEmbTop ℚ K Ω).1
  have hcc : Continuous c := hemb.continuous_iff.2 (by
    have e : (galEmb ℚ K Ω) ∘ c = fun s => u * galEmb ℚ K Ω s * u⁻¹ := funext hc
    rw [e]
    exact (continuous_const.mul hemb.continuous).mul continuous_const)
  have hcs : Continuous c.symm := hemb.continuous_iff.2 (by
    have e : (galEmb ℚ K Ω) ∘ c.symm = fun s => u⁻¹ * galEmb ℚ K Ω s * u := funext hc'
    rw [e]
    exact (continuous_const.mul hemb.continuous).mul continuous_const)
  have hφ : Continuous φ := (hcc.comp continuous_subtype_val).subtype_mk _
  have hφs : Continuous φ.symm := (hcs.comp continuous_subtype_val).subtype_mk _
  let Bw' : LocBridge l K Ω (Dec (F := K) A') O :=
    { Kw := Bw.Kw, j := Bw.j.comp (u : Ω →+* Ω)
      j_E := fun x => by
        change Bw.j (u (algebraMap K Ω x)) ∈ _
        obtain ⟨y, hy⟩ := fixAux u c hc x
        rw [← hy]; exact Bw.j_E y
      j_dense := Bw.j_dense.trans (closure_mono (by
        rintro _ ⟨x, rfl⟩
        obtain ⟨y, hy⟩ := fixAux u⁻¹ c.symm hc' x
        refine ⟨y, ?_⟩
        change Bw.j (u (algebraMap K Ω y)) = Bw.j (algebraMap K Ω x)
        rw [hy]
        simp))
      e := φ.trans Bw.e
      e_cont := Bw.e_cont.comp hφ, e_symm_cont := hφs.comp Bw.e_symm_cont
      e_comm := fun s x => by
        refine (Bw.e_comm (φ s) (u x)).trans ?_
        have h2 : (c (s : G K Ω)) (u x) = (u * galEmb ℚ K Ω (s : G K Ω) * u⁻¹) (u x) :=
          DFunLike.congr_fun (hc s) _
        change Bw.j ((c (s : G K Ω)) (u x)) = Bw.j (u ((s : G K Ω) x))
        rw [h2]
        congr 1
        simp
        rfl
      LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg
      eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }
  refine ⟨O, i1, i2, i3, Bw', fun x => (hu x).trans (hj (u x)), LL', r'.comp φ.toMonoidHom,
    ⟨hle, MonoidHom.ext fun s => DFunLike.congr_fun hmap (φ s)⟩, K', hK', ?_⟩
  have e : Bw'.repE LL' (r'.comp φ.toMonoidHom) = Bw.repE LL' r' := by
    refine MonoidHom.ext fun t => ?_
    simp [LocBridge.repE, Bw']
  rw [e]
  exact hcr

end

theorem UpperTheory.potentiallyCrystalline_comp_conjugation :
    ∀ {K Ω : Type} [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
        (u : G ℚ Ω) (c : G K Ω ≃* G K Ω), (∀ s, UpperTheory.V.Base.galEmb ℚ K Ω (c s) = u * UpperTheory.V.Base.galEmb ℚ K Ω s * u⁻¹) →
        ∀ (r : G K Ω →* GL (Fin n) (Qbar l)) (A A' : ValuationSubring Ω), (∀ x, x ∈ A' ↔ u x ∈ A) →
          UpperTheory.V.Af.PotCrysAt r A → UpperTheory.V.Af.PotCrysAt (r.comp c.toMonoidHom) A' := by
  intro K Ω _ _ _ _ _ _ _ l _ n u c hc r A A' hu hA
  exact partialTrace_valuation_sum u c hc r A A' hu hA
end
