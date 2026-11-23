module

import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.ExistsZalgOfCenterU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Formalism.WeaklyAdmissibleFiltrations
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere

open UpperTheory.V UpperTheory.V.Af

private theorem flag_stable {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (D N N' : Subgroup Γ) (hN : N ≤ N')
    (hc : ∀ d ∈ D, ∀ s ∈ N, d⁻¹ * s * d ∈ N) (χ : Fin 2 → Γ →* kˣ) (hne : ∃ s ∈ N, χ 0 s ≠ χ 1 s)
    (h : IsFlagOn r N' fun i => (χ i).comp N'.subtype) :
    ∃ κ, IsFlagOn r D κ ∧ ∀ i (s : ↥D), (s : Γ) ∈ N → κ i s = χ i s := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨s0, hs0, hne⟩ := hne
  let M : Γ →* GL (Fin 2) k := (MulAut.conj g).toMonoidHom.comp r
  have hM : ∀ s, M s = g * r s * g⁻¹ := fun _ => rfl
  have h1 : ∀ s ∈ N, M s 1 0 = 0 := fun s hs => (hg ⟨s, hN hs⟩).1 1 0 (by decide)
  have h2 : ∀ s ∈ N, ∀ i, M s i i = χ i s := fun s hs i => (hg ⟨s, hN hs⟩).2 i
  have hmul : ∀ s t i j, M (s * t) i j = M s i 0 * M t 0 j + M s i 1 * M t 1 j := fun s t i j => by
    rw [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h3 : ∀ d ∈ D, M d 1 0 = 0 := fun d hd => by
    have e : s0 * d = d * (d⁻¹ * s0 * d) := by group
    have e2 := hmul s0 d 1 0
    have e3 : χ 0 (d⁻¹ * s0 * d) = χ 0 s0 := by rw [map_mul, map_mul, map_inv, mul_right_comm]; simp
    rw [e, hmul, h1 _ (hc d hd s0 hs0), h1 _ hs0, h2 _ (hc d hd s0 hs0), h2 _ hs0, e3] at e2
    have : (χ 0 s0 : k) - χ 1 s0 ≠ 0 := sub_ne_zero.2 fun h => hne (Units.ext h)
    apply mul_left_cancel₀ this
    linear_combination e2
  refine ⟨fun i => MonoidHom.toHomUnits
    { toFun := fun s => M s i i
      map_one' := by simp
      map_mul' := fun s t => by
        rw [Subgroup.coe_mul, hmul]
        fin_cases i
        · simp [h3 _ t.2]
        · simp [h3 _ s.2] }, ⟨g, fun s => ⟨fun i j hij => ?_, fun i => rfl⟩⟩, fun i s hs => Units.ext (h2 _ hs i)⟩
  fin_cases i <;> fin_cases j
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact h3 _ s.2
  · exact absurd hij (by decide)

private theorem dual_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

private theorem ss_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep r) : IsSSRep (tw r χ) := by
  have hinv (W : Submodule k (Fin n → k)) : IsInv (tw r χ) W ↔ IsInv r W := by
    constructor
    · intro hW g v hv
      have hsmul := W.smul_mem ((χ g : k)⁻¹) (hW g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at hsmul
    · intro hW g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (hW g v hv)
  intro W hW
  obtain ⟨W', hW', hcompl⟩ := h W ((hinv W).1 hW)
  exact ⟨W', (hinv W').2 hW', hcompl⟩

private theorem place_of {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {p : ℕ} [hp : Fact p.Prime]
    {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w := by
  obtain ⟨p1, p2, p3, -⟩ := UpperTheory.V.Base.places ℚ Ω p A
  obtain ⟨v, hv⟩ := p1 fun h => (p2 h).2 hA
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp.out)
  have hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have e : v = w := HeightOneSpectrum.ext
    ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ((p3 v hv).1 hA))).symm.trans
      (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))
  exact e ▸ hv

private theorem cont_cycBar (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)

private theorem cyc_inf {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]
    {A : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := ℚ) A, ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l s ^ k ≠ 1 := by
  have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  obtain ⟨s, hs, he⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  refine ⟨s, hs, fun k hk h => ?_⟩
  have h2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = (l + 1 : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [he, hu.unit_spec, map_natCast, map_natCast]
  have h3 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h3
  have := hl.out.pos
  omega

private theorem charpoly_smul {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : M.charpoly.map φ = (B.map fun b => X - C b).prod) :
    (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod := by
  have hcard : B.card = 2 := by
    simpa only [natDegree_map, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      natDegree_multiset_prod_X_sub_C_eq_card] using (congrArg natDegree h).symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    map_X, map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have hzero := congrArg (eval 0) h
  have hone := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hzero hone
  have hdet : φ M.det = x * y := by linear_combination hzero
  have htrace : φ M.trace = x + y := by linear_combination hzero - hone
  rw [hdet, htrace]
  simp only [C_mul, C_add]
  ring

end UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open scoped Pointwise

attribute [local instance 10000] DivisionSemiring.to_moduleIsTorsionFree

private theorem move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F))) :
    ∃ (B : ValuationSubring Ω) (g : G F Ω), IsPlaceOver B w ∧ (∀ x, x ∈ B ↔ g x ∈ A) ∧
      (∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) A) ∧
      ∀ s ∈ Ine (F := K) B, g * res F Ω K s * g⁻¹ ∈ Ine (F := F) A := by
  obtain ⟨B, hB⟩ := (exists_isPlaceOver Ω w : ∃ B : ValuationSubring Ω, IsPlaceOver B w)
  have hB' : IsPlaceOver B (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω]
    exact hB (algebraMap (𝓞 F) (𝓞 K) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hB' hA
  have hm : ∀ x, x ∈ B ↔ g x ∈ g • B := fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hv : ∀ y, (g • B).valuation (g y) < 1 ↔ B.valuation y < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hm, ← hm, map_eq_zero_iff _ g.injective]
  have hD : ∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) (g • B) := fun s hs => by
    have h1 : res F Ω K s • B = B := hs
    show (g * res F Ω K s * g⁻¹) • g • B = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  refine ⟨B, g, hB, hm, hD, fun s hs => ⟨hD s hs.1, fun x hx => ?_⟩⟩
  obtain ⟨y, rfl⟩ := g.surjective x
  have e : (g * res F Ω K s * g⁻¹) (g y) = g (s y) := by
    show g (s (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e, ← map_sub, hv]
  exact hs.2 y ((B.valuation_le_one_iff _).2 ((hm y).2 (((g • B).valuation_le_one_iff _).1 hx)))

private theorem nat_mem_under {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (l : ℕ)
    (w : HeightOneSpectrum (𝓞 L)) : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

private theorem char_conj {Γ C : Type} [Group Γ] [CommGroup C] (χ : Γ →* C) (g s : Γ) : χ (g * s * g⁻¹) = χ s := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

private theorem rep_conj {Γ C : Type} [Group Γ] [Group C] (r : Γ →* C) (P : C) (g s : Γ) :
    P * r g * r s * (P * r g)⁻¹ = P * r (g * s * g⁻¹) * P⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  group
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Af.Bc

namespace UpperTheory.V.Br

def SigP (K : Type) [Field K] [NumberField K] [IsCMField K] {n : ℕ} (m : Fin n → ℤ) (M : ℕ) : Set (CuspSub K n) :=
  {π | (∀ τ, π.HasInfChar τ (infOf m)) ∧ (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) ∧ HasFixed π.finPart (KLev K n M)}

def CardP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
      ∀ S : Finset (CuspSub K n), (∀ π ∈ S, π ∈ SigP K m M) → (∀ π ∈ S, ∀ π' ∈ S, π.Iso π' → π = π') →
        S.card ≤ c * (M * (H + 1)) ^ A

def CharConj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], Module.finrank ℚ F = 1 → ∀ (χ : HChar F) (a : (F →+* ℂ) → ℤ), IsAlgPos χ a → ∀ σ : ℂ ≃+* ℂ,
    ∃ χ' : HChar F, (∀ v, χ'.locInf v (-1) = χ.locInf v (-1)) ∧
      ∀ w, χ.UnrAt w → χ'.UnrAt w ∧ ((χ'.val w : ℂˣ) : ℂ) = σ ((χ.val w : ℂˣ) : ℂ)

def SatOfPol : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : CuspSub E n) (ψ : HChar E), GlobalTheory.ContraPair.DualIsConjBy P ψ →
    ∀ w : HeightOneSpectrum (𝓞 E), ψ.UnrAt w → ∀ B B', (CG.mk P).HasSat w B → (CG.mk P).HasSat (cPl w) B' →
      B'.map (·⁻¹) = B.map (· * (ψ.val w)⁻¹)

def ConjP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m →
    ∀ M : ℕ, 1 ≤ M → ∀ (σ : ℂ ≃+* ℂ), ∀ π ∈ SigP K m M, ∃ π' ∈ SigP K m M, ∀ w B, (CG.mk π).HasSat w B →
      ∃ B', (CG.mk π').HasSat w B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ

def IntP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ π ∈ SigP K m M, ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M →
      ¬ (p : ℤ) ∣ discr K → ∀ B, (CG.mk π).HasSat w B → SlopesIn (normV w) m (algSat n (normV w) B)

def QuadFam : Prop :=
  ∀ N : ℕ, ∃ (K : Fin N → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, NumberField (K i)) (_ : ∀ i, IsCMField (K i)),
    (∀ i, Module.finrank ℚ (K i) = 2) ∧ ∀ i j, i ≠ j → IsCoprime (discr (K i)) (discr (K j))

def SignNe : Prop :=
  ∀ (K K' Ω : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [Algebra K' Ω]
    [IsScalarTower ℚ K Ω] [IsScalarTower ℚ K' Ω] [IsAlgClosure ℚ Ω], Module.finrank ℚ K = 2 → IsCoprime (discr K) (discr K') →
    (res ℚ Ω K).range ≠ (res ℚ Ω K').range

def TwCard : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (n : ℕ) (r : Γ →* GL (Fin n) k), IsIrr r → ∀ S : Finset (Γ →* kˣ),
    (∀ δ ∈ S, RepIso r (tw r δ)) → S.card ≤ n ^ 2

def ResTwo : Prop :=
  ∀ (Γ Γ' k : Type) [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] [CharZero k] (n : ℕ) (φ : Γ' →* Γ) (δ : Γ →* kˣ),
    (∀ s, δ s = 1 ↔ s ∈ φ.range) → (∀ s, δ s = 1 ∨ δ s = -1) → ∀ r : Γ →* GL (Fin n) k,
    (IsIrr r → ¬ RepIso r (tw r δ) → IsIrr (r.comp φ)) ∧
    ∀ r' : Γ →* GL (Fin n) k, IsIrr (r.comp φ) → RepIso (r.comp φ) (r'.comp φ) → RepIso r r' ∨ RepIso (tw r δ) r'

def FrobEx : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)),
    (∀ B B', FrobEig ι r w B → FrobEig ι r w B' → B = B') ∧
    ∀ M : ℕ, LevelAway l M r → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ((M : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ B, FrobEig ι r w B

def RootSum : Prop :=
  ∀ (n p : ℕ), 0 < p → ∀ (m : Fin n → ℤ) (wt : ℤ) (I : Type) [Fintype I] (q f : I → ℕ), (∀ i, 1 ≤ f i ∧ f i ≤ 2 ∧ q i = p ^ f i) →
    ∀ D : ∀ i, EigData n (q i) m wt, ∃ D' : EigData n p m wt, Nat.card D'.S ≤ 2 ^ (n + 1) * ∑ i, Nat.card (D i).S ∧
      ∃ e : (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) → D'.S,
        Function.Injective e ∧ ∀ x, D'.β (e x) = x.2.1.1.2

def PotMove : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (A A' : ValuationSubring Ω) (g : _root_.Formalism.ConjugateSelfDual.G F Ω), (∀ x, x ∈ A' ↔ g x ∈ A) → PotCrysAt r A → PotCrysAt r A'

def PotRes : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l))
    (A : ValuationSubring Ω), PotCrysAt r A → PotCrysAt (r.comp (res F Ω K)) A

end UpperTheory.V.Br
end
end

section

open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af


open GroundTheory.Automorphic in
theorem UpperTheory.V.Br.hermEx : Gk.HermEx :=
  Gk.hermEx_of (fun _ _ _ _ _ => CuspFin.mem_cuspForms_of) fun F _ _ _ a => by
    refine ⟨(Fb.lieEq F a).toLinearMap, Subtype.ext ?_, fun X φ _ => congrArg Subtype.val (CuspFin.uAction_lieEq X φ)⟩
    rw [UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← Fb.lieEq_oneL]
    rfl
end
