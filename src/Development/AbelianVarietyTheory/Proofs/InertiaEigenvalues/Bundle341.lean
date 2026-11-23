module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle226
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharacterLabelUniqueGLn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiGradedPieceIsoTwistedOC
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle317
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle315
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle291

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_le_jumpSum_wild :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ ∈ A, σ ^ p ∈ B) → ¬ A ≤ B → Nat.card ↥A ≤ jumpSum (wild K L) A B := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E A B hp hE hA hord hcomm hpow hnot
  obtain ⟨j, hj, hrange, -, hram⟩ := GlobalTheory.T.galoisGroup_fixedField_baseChange_localField K L A
  have hmemA : ∀ σ, j σ ∈ A := fun σ => hrange.le ⟨σ, rfl⟩
  have htop : lowerRamificationGroup (IntermediateField.fixedField A) L 0 = ⊤ := by
    rw [hram, eq_top_iff]
    intro σ _
    exact hA (hmemA σ)
  have hcomm' : ∀ σ τ : L ≃ₐ[IntermediateField.fixedField A] L,
      σ * τ * σ⁻¹ * τ⁻¹ ∈ B.comap j := by
    intro σ τ
    rw [Subgroup.mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hcomm _ (hmemA σ) _ (hmemA τ)
  have hpow' : ∀ σ : L ≃ₐ[IntermediateField.fixedField A] L, σ ^ p ∈ B.comap j := by
    intro σ
    rw [Subgroup.mem_comap, map_pow]
    exact hpow _ (hmemA σ)
  have hne : B.comap j ≠ ⊤ := by
    intro h
    apply hnot
    intro a ha
    obtain ⟨σ, rfl⟩ := hrange.ge ha
    have : σ ∈ B.comap j := h ▸ Subgroup.mem_top σ
    exact this
  have key := GlobalTheory.T.card_le_wild_jumpSum_totallyRamified (IntermediateField.fixedField A) L p E (B.comap j) hp hE htop hord
    hcomm' hpow' hne
  have hwild : wild (IntermediateField.fixedField A) L = fun t => (wild K L t).comap j := by
    funext t
    exact hram _
  have hcard : Nat.card (L ≃ₐ[IntermediateField.fixedField A] L) = Nat.card ↥A := by
    exact (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).trans
      (congrArg (fun H : Subgroup (L ≃ₐ[K] L) => Nat.card ↥H) hrange)
  have hjs : jumpSum (wild K L) A B =
      jumpSum (wild (IntermediateField.fixedField A) L) ⊤ (B.comap j) := by
    rw [hwild, GlobalTheory.T.ramificationJumpSum_comap_injective _ _ j (wild K L) B hj]
    exact congrArg (fun H => jumpSum (wild K L) H B) hrange.symm
  calc Nat.card ↥A = Nat.card (L ≃ₐ[IntermediateField.fixedField A] L) := hcard.symm
    _ ≤ _ := key
    _ = jumpSum (wild K L) A B := hjs.symm

end GlobalTheory.PMon.Ram
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.gaussNormAcris_frobenius_eq_pow_root_radius : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → ∀ x : Formalism.Per.Acris l, gC l ρ (φc l x) = gC l (ρ ^ ((1 : ℝ) / l)) x ^ l := by
  first | exact @GlobalTheory.PMon.Gauss.gC_phi | exact GlobalTheory.PMon.Gauss.gC_phi | (intros; apply GlobalTheory.PMon.Gauss.gC_phi <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraProductList_degree : ∀ (g : ℕ) [Fact g.Prime] (L : List (Pc g)) (n : ℕ), n = degL L → hcL L n 1 * (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod = (∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1)) * (L.map fun p => p.2 1).prod := by
  first | exact @GlobalTheory.GLq.HcDeg.hc_degree | exact GlobalTheory.GLq.HcDeg.hc_degree | (intros; apply GlobalTheory.GLq.HcDeg.hc_degree <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.cuspidalCharacter_label_unique_GLn : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → ∀ (d : ℕ) (P P' : (ZMod g)[X]) (χ χ' : Gn g d → ℂ), IsCuspOf L P χ → (IsCuspOf L P' χ → P = P') ∧ (Green → IsCuspOf L P χ' → χ = χ') := by
  first | exact @GlobalTheory.GLq.isCuspOf_label_unique | exact GlobalTheory.GLq.isCuspOf_label_unique | (intros; apply GlobalTheory.GLq.isCuspOf_label_unique <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField : ∀ (g : ℕ) [Fact g.Prime] (N k s : ℕ) (ψ : AddChar (ZMod g) ℂ), eU g N ψ * eU g N ψ = eU g N ψ ∧ (eU g N ψ).coeff 1 = ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ ∧ (N = k + 2 * s + 1 → eJ g N k s ψ * eJ g N k s ψ = eJ g N k s ψ ∧ (eJ g N k s ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹) ∧ (k < N → eJ' g N k ψ * eJ' g N k ψ = eJ' g N k ψ ∧ (eJ' g N k ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹) := by
  first | exact @GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField | exact GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField | (intros; apply GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.xiGradedPiece_iso_twistedOC : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (i : ℤ), ∃ Φ : Qab (AinfSub l) (xiU AI) i (i + 1) →+ PadicComplex l, Function.Injective Φ ∧ Set.range Φ = {y | ‖y‖ ≤ 1} ∧ (∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) ∧ ∀ g : GQ l, g (P.ζQ 1) = P.ζQ 1 → ∀ x, Φ (actQab (xiOK AI) i (i + 1) g x) = chiC P.χQ i g * AI.actC g (Φ x) := by
  first | exact @GlobalTheory.Cyc.Graded.graded_iso | exact GlobalTheory.Cyc.Graded.graded_iso | (intros; apply GlobalTheory.Cyc.Graded.graded_iso <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.UnrDeg

theorem det_pow_ne_zero {k F : Type} [Field k] [Field F] [Algebra k F] (τ : F ≃ₐ[k] F) {n : ℕ}
    (hord : orderOf τ = n) (bas : Module.Basis (Fin n) k F) :
    (Matrix.of fun i j : Fin n => (τ ^ (j : ℕ)) (bas i)).det ≠ 0 := by
  intro h
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  let L : F →ₗ[k] F :=
    { toFun := fun x => ∑ j : Fin n, u j * (τ ^ (j : ℕ)) x
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_smul_comm]
        congr 1
        exact (τ ^ (j : ℕ)).toLinearEquiv.map_smul r x }
  have hL : L = 0 := by
    refine bas.ext fun i => ?_
    have := congrFun hu i
    simpa [L, Matrix.mulVec, dotProduct, mul_comm] using this
  let f : Fin n → (F →* F) := fun j => ((τ ^ (j : ℕ)).toRingEquiv : F ≃+* F).toMonoidHom
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : τ ^ (i : ℕ) = τ ^ (j : ℕ) := AlgEquiv.ext fun x => DFunLike.congr_fun hij x
    have hi : (i : ℕ) ∈ Set.Iio (orderOf τ) := by rw [hord]; exact i.2
    have hj : (j : ℕ) ∈ Set.Iio (orderOf τ) := by rw [hord]; exact j.2
    exact Fin.ext (pow_injOn_Iio_orderOf hi hj h1)
  have li := (linearIndependent_monoidHom F F).comp f hf
  rw [Fintype.linearIndependent_iff] at li
  apply hu0
  funext j
  refine li u ?_ j
  funext x
  have := LinearMap.congr_fun hL x
  simpa [L, f, Finset.sum_apply, smul_eq_mul] using this

variable {l : ℕ} [Fact l.Prime]

def sig (l : ℕ) [Fact l.Prime] : ↥(MaximalUnramifiedExtension l) ≃ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) :=
  AlgEquiv.ofBijective (frobUr l) frobUr_bijective

theorem fr_apply (k : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : fr l k c = (frobUr l ^ k) c := rfl

theorem sig_pow (k : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : (sig l ^ k) c = fr l k c := by
  rw [fr_apply]
  induction k generalizing c with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgHom.mul_apply, ih]; rfl

end GlobalTheory.PMon.UnrDeg

namespace GlobalTheory.PMon.UnrDeg

theorem exists_moved (l : ℕ) [hl : Fact l.Prime] {r k : ℕ} (hk0 : 0 < k) (hkr : k < r) :
    ∃ c : ↥(MaximalUnramifiedExtension l), fr l r c = c ∧ fr l k c ≠ c := by
  have h2 := hl.out.two_le
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hls : l ^ k ≤ l ^ s := Nat.pow_le_pow_right (by omega) (by omega)
  have hl1 : l ^ 1 ≤ l ^ k := Nat.pow_le_pow_right (by omega) hk0
  rw [pow_one] at hl1
  have h5 : l ^ s * 2 ≤ l ^ s * l := Nat.mul_le_mul_left _ h2
  have hps : l ^ (s + 1) = l ^ s * l := pow_succ _ _
  have hN0 : 0 < l ^ (s + 1) - 1 := by omega
  have hkN : l ^ k < l ^ (s + 1) - 1 := by omega
  have h1N : 1 < l ^ (s + 1) - 1 := by omega
  have hd : ¬ l ∣ l ^ (s + 1) - 1 := fun h => hl.out.one_lt.ne' (Nat.dvd_one.mp
    ((Nat.dvd_sub_iff_right (by omega) (dvd_pow_self l (by omega))).mp h))
  haveI : NeZero (l ^ (s + 1) - 1) := ⟨hN0.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ (s + 1) - 1)
  have hmem : z ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨_, hN0, hd, hz.pow_eq_one⟩
  have h1 : (⟨z, hmem⟩ : ↥(MaximalUnramifiedExtension l)) ^ (l ^ (s + 1) - 1) = 1 := Subtype.ext hz.pow_eq_one
  refine ⟨⟨z, hmem⟩, ?_, fun h => ?_⟩
  · rw [fr_apply, frobUr_pow_root _ _ _ hN0 hd h1, show l ^ (s + 1) = (l ^ (s + 1) - 1) + 1 by omega, pow_succ, h1,
      one_mul]
  · rw [fr_apply, frobUr_pow_root _ _ _ hN0 hd h1] at h
    have h6 : z ^ l ^ k = z ^ 1 := by rw [pow_one]; exact congrArg Subtype.val h
    have := hz.pow_inj hkN h1N h6
    omega

theorem fixed_field_deg : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (E : FinExt l) (ω : Fin r → ↥(MaximalUnramifiedExtension l)),
    E.1 ≤ MaximalUnramifiedExtension l ∧ Module.finrank ℚ_[l] ↥E.1 = r ∧ (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c ↔ (c : Om l) ∈ E.1) ∧
    (∀ k, fr l r (ω k) = ω k) ∧ LinearIndependent ℚ_[l] ω ∧
    (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) ∧
    (Matrix.of fun m k : Fin r => fr l m (ω k)).det ≠ 0 := by
  intro l _ r hr
  let σ := sig l
  let F : IntermediateField ℚ_[l] ↥(MaximalUnramifiedExtension l) := IntermediateField.fixedField (Subgroup.zpowers (σ ^ r))
  have hF : ∀ c, c ∈ F ↔ fr l r c = c := fun c => by
    rw [IntermediateField.mem_fixedField_iff, ← sig_pow]
    refine ⟨fun h => h _ (Subgroup.mem_zpowers _), fun h f hf => ?_⟩
    exact (Subgroup.zpowers_le (H := MulAction.stabilizer _ c)).2 h hf
  have hst : ∀ c ∈ F, σ c ∈ F := fun c hc => by
    rw [hF, ← sig_pow] at hc ⊢
    rw [← AlgEquiv.mul_apply, ← pow_succ, pow_succ', AlgEquiv.mul_apply, hc]
  let τ₀ : ↥F →ₐ[ℚ_[l]] ↥F := ((σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)).comp F.val).codRestrict F.toSubalgebra
    fun c => hst c c.2
  let τ : ↥F ≃ₐ[ℚ_[l]] ↥F := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact AlgEquiv.ofBijective τ₀ (Algebra.IsAlgebraic.algHom_bijective _)
  have hτ : ∀ (k : ℕ) (c : ↥F), (((τ ^ k) c : ↥F) : ↥(MaximalUnramifiedExtension l)) = fr l k c := fun k c => by
    rw [← sig_pow]
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← ih]; rfl
  have hrτ : τ ^ r = 1 := AlgEquiv.ext fun c => Subtype.ext ((hτ r c).trans ((hF c).1 c.2))
  have hord : orderOf τ = r := by
    rw [orderOf_eq_iff hr]
    refine ⟨hrτ, fun k hkr hk0 hk => ?_⟩
    obtain ⟨c, hc, hm⟩ := exists_moved l hk0 hkr
    have := hτ k ⟨c, (hF c).2 hc⟩
    rw [hk, AlgEquiv.one_apply] at this
    exact hm this.symm
  have hfin : IsOfFinOrder τ := isOfFinOrder_iff_pow_eq_one.2 ⟨r, hr, hrτ⟩
  haveI : Finite ↥(Subgroup.zpowers τ) := hfin.finite_zpowers
  have hbot : IntermediateField.fixedField (Subgroup.zpowers τ) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [IntermediateField.mem_fixedField_iff] at hc
    have h1 := congrArg Subtype.val (hc τ (Subgroup.mem_zpowers _))
    have h2 := hτ 1 c
    rw [pow_one] at h2
    obtain ⟨x, hx⟩ := (GlobalTheory.MemLoc.frob_laws l (frobUr l) frobUr_root).2.2 c (h2.symm.trans h1)
    exact ⟨x, Subtype.ext hx⟩
  haveI h1 : FiniteDimensional ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) ↥F :=
    inferInstanceAs (FiniteDimensional ↥(FixedPoints.subfield (Subgroup.zpowers τ) ↥F) ↥F)
  haveI h2 : FiniteDimensional ℚ_[l] ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) := by
    rw [hbot]; infer_instance
  haveI h3 : FiniteDimensional ℚ_[l] ↥F := Module.Finite.trans ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) ↥F
  have hdeg : Module.finrank ℚ_[l] ↥F = r := by
    have h := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers τ)
    rw [hbot, IntermediateField.finrank_bot', Nat.card_zpowers] at h
    exact h.trans hord
  let bas : Module.Basis (Fin r) ℚ_[l] ↥F := Module.finBasisOfFinrankEq ℚ_[l] ↥F hdeg
  refine ⟨⟨F.map (MaximalUnramifiedExtension l).val, (F.equivMap (MaximalUnramifiedExtension l).val).toLinearEquiv.finiteDimensional⟩, fun k => (bas k : ↥(MaximalUnramifiedExtension l)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, -, rfl⟩
    exact y.2
  · show Module.finrank ℚ_[l] ↥(F.map (MaximalUnramifiedExtension l).val) = r
    rw [← (F.equivMap (MaximalUnramifiedExtension l).val).toLinearEquiv.finrank_eq]
    exact hdeg
  · intro c
    show _ ↔ (c : Om l) ∈ F.map (MaximalUnramifiedExtension l).val
    rw [IntermediateField.mem_map, ← hF]
    refine ⟨fun h => ⟨c, h, rfl⟩, ?_⟩
    rintro ⟨y, hy, hyc⟩
    rwa [← Subtype.ext hyc]
  · intro k
    exact (hF _).1 (bas k).2
  · exact bas.linearIndependent.map' F.val.toLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  · intro c hc
    refine ⟨bas.repr ⟨c, (hF c).2 hc⟩, ?_⟩
    have e := congrArg (F.val.toLinearMap) (bas.sum_repr ⟨c, (hF c).2 hc⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e
    simpa using e.symm
  · intro h0
    let M : Matrix (Fin r) (Fin r) ↥F := Matrix.of fun i j : Fin r => (τ ^ (j : ℕ)) (bas i)
    have e : (Matrix.of fun m k : Fin r => fr l m (bas k : ↥(MaximalUnramifiedExtension l))) = (F.val.mapMatrix M).transpose := by
      refine Matrix.ext fun m k => ?_
      simp only [M, Matrix.of_apply, Matrix.transpose_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
      exact (hτ m (bas k)).symm
    rw [e, Matrix.det_transpose, ← AlgHom.map_det] at h0
    exact det_pow_ne_zero τ hord bas (Subtype.ext h0)

end GlobalTheory.PMon.UnrDeg
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResIndep

variable {l : ℕ} [Fact l.Prime]

theorem fr_bijective (l : ℕ) [Fact l.Prime] (m : ℕ) : Function.Bijective (fr l m) := by
  have e : (fr l m : ↥(MaximalUnramifiedExtension l) → ↥(MaximalUnramifiedExtension l)) = (frobUr l)^[m] := by
    funext c
    simp [fr, AlgHom.coe_pow]
  rw [e]
  exact frobUr_bijective.iterate m

variable (P : LocPrime l) {n : Type} [Fintype n] [DecidableEq n]

def resS (m : ℕ) (u : n → P.R.BdR) (d : n → ↥(MaximalUnramifiedExtension l)) : P.R.BdR := ∑ i, kd P (fr l m (d i)) * u i

theorem resS_zero (m : ℕ) (u : n → P.R.BdR) : resS P m u 0 = 0 := by simp [resS]

theorem resS_add (m : ℕ) (u : n → P.R.BdR) (d e : n → ↥(MaximalUnramifiedExtension l)) :
    resS P m u (d + e) = resS P m u d + resS P m u e := by
  simp [resS, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem resS_neg (m : ℕ) (u : n → P.R.BdR) (d : n → ↥(MaximalUnramifiedExtension l)) : resS P m u (-d) = -resS P m u d := by
  simp [resS, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem resS_smul (m : ℕ) (u : n → P.R.BdR) (e : ↥(MaximalUnramifiedExtension l)) (d : n → ↥(MaximalUnramifiedExtension l)) :
    resS P m u (e • d) = kd P (fr l m e) * resS P m u d := by
  simp [resS, Finset.mul_sum, mul_assoc]

def resW (r m : ℕ) (u : n → P.R.BdR) : AddSubgroup (n → ↥(MaximalUnramifiedExtension l)) where
  carrier := {d | (∀ i, fr l r (d i) = d i) ∧ resS P m u d ∈ Fil P 1}
  zero_mem' := ⟨fun i => by simp, by rw [resS_zero]; exact Fil_zero_mem 1⟩
  add_mem' := fun {x y} hx hy => ⟨fun i => by simp [hx.1 i, hy.1 i], by rw [resS_add]; exact Fil_add hx.2 hy.2⟩
  neg_mem' := fun {x} hx => ⟨fun i => by simp [hx.1 i], by rw [resS_neg]; exact Fil_neg hx.2⟩

theorem rat_vecMul {K : FinExt l} {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (hR : IsRat r ρ) (d : n → ↥(MaximalUnramifiedExtension l))
    (hd : ∀ i, fr l r (d i) = d i) (g : ↥(GK K)) (j : n) :
    fr l r (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j) = Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j := by
  change fr l r (∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = ∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j

  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hd, hR.rat]

theorem key {K : FinExt l} {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (hR : IsRat r ρ) (m : ℕ) (u : n → P.R.BdR) (a : ℤ)
    (g : ↥(GK K))
    (hrel : (matD P ρ m g).mulVec (fun i => P.actQdR (g : GQ l) (u i)) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ a : ℚ_[l]ˣ) : ℚ_[l]) • u)
    (d : n → ↥(MaximalUnramifiedExtension l)) (hd : ∀ i, fr l r (d i) = d i)
    (h : resS P m u (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l))) ∈ Fil P 1) : resS P m u d ∈ Fil P 1 := by
  set q : ℚ_[l]ˣ := P.χQ (g : GQ l) ^ a with hq
  have hi : ∀ i, algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * u i =
      ∑ j, kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j) := by
    intro i
    have := congrFun hrel i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, matD, Matrix.map_apply] at this
    exact this.symm
  have hfix : ∀ j, P.actQdR (g : GQ l) (kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j))) =
      kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j)) := fun j =>
    act_kd P g (hR.le _ (fr_comm (rat_vecMul hR d hd g j) m))
  have e1 : algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * resS P m u d =
      P.actQdR (g : GQ l) (resS P m u (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)))) := by
    have hR' : ∀ j, P.actQdR (g : GQ l) (kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j)) * u j) =
        ∑ i, kd P (fr l m (d i)) * (kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j)) := by
      intro j
      rw [map_mul, hfix j]
      change kd P (fr l m (∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * _ = _

      rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, mul_assoc]
    have hL : ∀ i, algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * (kd P (fr l m (d i)) * u i) =
        ∑ j, kd P (fr l m (d i)) * (kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j)) := by
      intro i
      rw [mul_left_comm, hi i, Finset.mul_sum]

    rw [resS, resS, map_sum, Finset.mul_sum]
    simp_rw [hR', hL]
    exact Finset.sum_comm
  have h1 : algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * resS P m u d ∈ Fil P 1 := e1 ▸ Fil_act (g : GQ l) h
  have h2 := Fil_mul_left (q_mem_Fil P ((q⁻¹ : ℚ_[l]ˣ) : ℚ_[l])) h1
  rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at h2

end GlobalTheory.PMon.ResIndep

namespace GlobalTheory.PMon


open GlobalTheory.PMon.ResIndep in
theorem residue_indep_of_not_splits : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (u : n → P.R.BdR) (a : ℤ), IsRat r ρ → ¬ Splits r ρ → (∀ i, u i ∈ Fil P 0) → (∃ i, u i ∉ Fil P 1) → (∀ g : ↥(GK K), (matD P ρ m g).mulVec (fun i => P.actQdR (g : GQ l) (u i)) = algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ a : ℚ_[l]ˣ) : ℚ_[l]) • u) → ∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * u i ∈ Fil P 1 → c = 0 := by
  intro l _ P AI T n _ _ K r ρ m u a hR hNS _ hu1 hrel c hc hS
  by_contra hc0
  apply hNS
  have hbij := fr_bijective l m
  refine GlobalTheory.T.reducible_of_stable_rational_rowSubspace l n K r ρ hR (resW P r m u) (fun d hd => hd.1) ?_ ?_ ?_ ?_
  · intro e he d hd
    refine ⟨fun i => ?_, ?_⟩
    · simp [Pi.smul_apply, smul_eq_mul, map_mul, he, hd.1 i]
    · rw [resS_smul]
      exact Fil_mul_left (kd_mem_Fil P _) hd.2
  · intro g d hd
    have hd1 : ∀ i, fr l r (d i) = d i := hd.1
    have hd' : ∀ j, fr l r (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j) = Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j :=
      rat_vecMul hR d hd1 g
    refine ⟨hd', key P hR m u a g⁻¹ (hrel g⁻¹) _ hd' ?_⟩
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.vecMul_one]
    exact hd.2
  · choose d hd using fun i => hbij.2 (c i)
    have hdr : ∀ i, fr l r (d i) = d i := fun i => hbij.1 (by
      rw [← fr_add, add_comm, fr_add, hd i, hc i])
    intro hbot
    have hmem : d ∈ resW P r m u := ⟨hdr, by
      change ∑ i, kd P (fr l m (d i)) * u i ∈ Fil P 1
      simpa only [hd] using hS⟩
    rw [hbot, AddSubgroup.mem_bot] at hmem
    apply hc0
    funext i
    rw [← hd i, hmem]
    simp
  · obtain ⟨i0, hi0⟩ := hu1
    refine ⟨Pi.single i0 1, fun i => ?_, fun hmem => hi0 ?_⟩
    · by_cases h : i = i0
      · subst h; simp
      · simp [h]
    · have e : resS P m u (Pi.single i0 1) = u i0 := by
        simp [resS, Pi.single_apply]
      rw [← e]
      exact hmem.2

end GlobalTheory.PMon

end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

theorem _root_.GlobalTheory.T.exists_letter_bijection' : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P), ∃ τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K)), Function.Bijective τ ∧ (∀ i, (S.W H).emb (τ i) = S.emb i) ∧ ∀ i, τ (i - 1) = τ i - 1 := by
  first | exact @GlobalTheory.RedFun.exists_letter_bijection | exact GlobalTheory.RedFun.exists_letter_bijection | (intros; apply GlobalTheory.RedFun.exists_letter_bijection <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_frobeniusFixed_unramified_tower_basis : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → LinearIndependent ℚ_[l] ω → (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) → ∀ (M : Type) [AddCommGroup M] [Module ↥(MaximalUnramifiedExtension l) M] [Module ℚ_[l] M] [IsScalarTower ℚ_[l] ↥(MaximalUnramifiedExtension l) M] (n : Type) [Fintype n] [DecidableEq n] (v : n × Fin r → M), LinearIndependent ℚ_[l] v → (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c, e • v c ∈ Submodule.span ℚ_[l] (Set.range v)) → ∃ a : n → M, (∀ j, a j ∈ Submodule.span ℚ_[l] (Set.range v)) ∧ LinearIndependent ℚ_[l] (fun jk : n × Fin r => ω jk.2 • a jk.1) ∧ Submodule.span ℚ_[l] (Set.range fun jk : n × Fin r => ω jk.2 • a jk.1) = Submodule.span ℚ_[l] (Set.range v) := by
  first | exact @GlobalTheory.exists_frFixed_tower_basis | exact GlobalTheory.exists_frFixed_tower_basis | (intros; apply GlobalTheory.exists_frFixed_tower_basis <;> assumption)
end
