module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle035
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentAntidiagonalMemSkewLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMiddleRowMemHomLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle069
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.HermitianLattices.Bundle003
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Formalism.HermitianLattices.StatementLat
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle068
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserRationalUnitriangularPairs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalCommonStabiliserBlockUnitriangularOnFrame
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle070
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PatternApprox

theorem exists_clear {Fp Ep : Type} [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp]
    [IsNonarchimedeanLocalField Fp] [CommRing Ep] [Algebra Fp Ep] [Module.Finite Fp Ep]
    (O : Subring Ep) (hO : ∀ x, x ∈ O ↔ IsIntegral 𝒪[Fp] x) {ι : Type} [Fintype ι] (x : ι → Ep) :
    ∃ a : Fp, a ≠ 0 ∧ ∀ i, algebraMap Fp Ep a * x i ∈ O := by
  have hfr : IsFractionRing 𝒪[Fp] Fp := (Valuation.integer.integers (valuation Fp)).isFractionRing
  have halg : ∀ i, IsAlgebraic 𝒪[Fp] (x i) := fun i =>
    (IsFractionRing.isAlgebraic_iff 𝒪[Fp] Fp Ep).mpr (Algebra.IsIntegral.isIntegral (R := Fp) (x i)).isAlgebraic
  choose y hy0 hyi using fun i => (halg i).exists_integral_multiple
  have hym : ∀ k, algebraMap Fp Ep (y k : Fp) ∈ O := fun k => by
    rw [hO, show algebraMap Fp Ep (y k : Fp) = algebraMap 𝒪[Fp] Ep (y k) from
      (IsScalarTower.algebraMap_apply 𝒪[Fp] Fp Ep (y k)).symm]
    exact isIntegral_algebraMap
  refine ⟨∏ k, (y k : Fp), ?_, fun i => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro k _ h
    exact hy0 k (Subtype.ext (by simpa using h))
  · have h1 : algebraMap Fp Ep (y i : Fp) * x i ∈ O := by
      rw [hO, show algebraMap Fp Ep (y i : Fp) = algebraMap 𝒪[Fp] Ep (y i) from
        (IsScalarTower.algebraMap_apply 𝒪[Fp] Fp Ep (y i)).symm, ← Algebra.smul_def]
      exact hyi i
    rw [map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc]
    exact O.mul_mem (O.prod_mem fun k _ => hym k) h1

variable {R : Type} [CommRing R]

theorem det_eq_one {m : ℕ} (I : Fin m → Fin m → Prop) (hI : ∀ i j, I i j → i < j)
    (s : Matrix (Fin m) (Fin m) R) (hs : ∀ i j, ¬ I i j → s i j = if i = j then 1 else 0) : s.det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [hs i i (fun h => lt_irrefl i (hI i i h))]
    simp
  · intro i j hji
    rw [hs i j (fun h => lt_asymm (hI i j h) hji)]
    have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hji
    simp [hne]

theorem adjugate_mem {m : ℕ} (O : Subring R) (s : Matrix (Fin m) (Fin m) R) (h : ∀ i j, s i j ∈ O) :
    ∀ i j, s.adjugate i j ∈ O := by
  let S : Matrix (Fin m) (Fin m) O := fun i j => ⟨s i j, h i j⟩
  have hS : O.subtype.mapMatrix S = s := by ext i j; rfl
  intro i j
  rw [← hS, ← RingHom.map_adjugate]
  exact (S.adjugate i j).2

end GlobalTheory.HL.PatternApprox


open GlobalTheory.HL.PatternApprox in
theorem GlobalTheory.HL.pattern_strong_approx : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (m : ℕ) (I : Fin m → Fin m → Prop), (∀ i j, I i j → i < j) → (∀ i j l, I i j → I j l → I i l) → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ s : ∀ p, Matrix (Fin m) (Fin m) (A.loc p).Ep, (∀ p i j, ¬ I i j → s p i j = if i = j then 1 else 0) → {p | ¬ IsIntM (A.L p) (s p)}.Finite → ∃ t : Matrix (Fin m) (Fin m) E, (∀ i j, ¬ I i j → t i j = if i = j then 1 else 0) ∧ ∀ p i j, ∃ o ∈ (A.L p).O, ((s p)⁻¹ * t.map (A.loc p).ιE - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  intro F E _ _ _ _ _ sig A m I hlt _htr c hc s hs hsint
  have hinv : ∀ p, (s p)⁻¹ = (s p).adjugate := fun p => by
    rw [Matrix.inv_def, det_eq_one I hlt (s p) (hs p), Ring.inverse_one, one_smul]
  have hcl : ∀ p, ∃ a : ((A.loc p).Fp)ˣ, (IsIntM (A.L p) (s p) → a = 1) ∧
      ∀ i j, algebraMap (A.loc p).Fp (A.loc p).Ep (a : (A.loc p).Fp) * (s p)⁻¹ i j ∈ (A.L p).O := by
    intro p
    haveI := (A.loc p).lf
    haveI : Module.Free (A.loc p).Fp (A.loc p).Ep := (A.loc p).free
    haveI : Module.Finite (A.loc p).Fp (A.loc p).Ep := Module.finite_of_finrank_eq_succ (A.loc p).rank
    by_cases h : IsIntM (A.L p) (s p)
    · refine ⟨1, fun _ => rfl, fun i j => ?_⟩
      rw [Units.val_one, map_one, one_mul, hinv p]
      exact adjugate_mem (A.L p).O (s p) h i j
    · obtain ⟨a, ha0, ha⟩ := exists_clear (A.L p).O (A.L p).O_def
        (fun ij : Fin m × Fin m => (s p)⁻¹ ij.1 ij.2)
      exact ⟨Units.mk0 a ha0, fun h' => absurd h' h, fun i j => ha (i, j)⟩
  choose c' hc'1 hc'2 using hcl
  let d : ∀ p, ((A.loc p).Fp)ˣ := fun p => c p * c' p
  have hd : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite := by
    apply (hc.union hsint).subset
    intro p hp
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno
    obtain ⟨⟨u, hu⟩, hint⟩ := hno
    exact hp ⟨u, by simp [d, hc'1 p hint, hu]⟩
  have hap := (GlobalTheory.T.strong_approximation_additive_quadratic_extension A d hd).2.1
  have hx : ∀ i j, ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O,
      (A.loc p).ιE x - s p i j = algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o :=
    fun i j => hap (fun p => s p i j) (hsint.subset fun p hp hi => hp (hi i j))
  choose x hx using hx
  refine ⟨fun i j => if I i j then x i j else if i = j then 1 else 0, fun i j h => by simp [h], fun p i j => ?_⟩
  set t : Matrix (Fin m) (Fin m) E := fun i j => if I i j then x i j else if i = j then 1 else 0 with ht
  have hD : ∀ k l, ∃ o ∈ (A.L p).O, (t.map (A.loc p).ιE - s p) k l =
      algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o := by
    intro k l
    by_cases hkl : I k l
    · obtain ⟨o, ho, he⟩ := hx k l p
      refine ⟨o, ho, ?_⟩
      rw [← he]
      show (A.loc p).ιE (t k l) - s p k l = (A.loc p).ιE (x k l) - s p k l
      rw [ht]
      simp only [hkl, if_true]
    · refine ⟨0, (A.L p).O.zero_mem, ?_⟩
      rw [Matrix.sub_apply, Matrix.map_apply, hs p k l hkl, mul_zero]
      simp only [ht, hkl, if_false]
      split_ifs <;> simp
  choose o ho hoeq using hD
  have hunit : (s p)⁻¹ * s p = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [det_eq_one I hlt (s p) (hs p)]; exact isUnit_one)
  have heq : (s p)⁻¹ * t.map (A.loc p).ιE - 1 = (s p)⁻¹ * (t.map (A.loc p).ιE - s p) := by
    rw [Matrix.mul_sub, hunit]
  refine ⟨∑ k, (algebraMap (A.loc p).Fp (A.loc p).Ep (c' p : (A.loc p).Fp) * (s p)⁻¹ i k) * o k j,
    (A.L p).O.sum_mem fun k _ => (A.L p).O.mul_mem (hc'2 p i k) (ho k j), ?_⟩
  rw [heq, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hoeq k j]
  simp only [d, Units.val_mul, map_mul]
  ring
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianStabiliser_rational_unitriangular_pairs : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) → ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) → ((s.map sig).transpose * G.Zh * s' = G.Zh ↔ ∃ h ∈ G.St, (∀ j, h (G.f j) = ∑ i, s i j • G.f i) ∧ ∀ j, h (G.f' j) = ∑ i, s' i j • G.f' i) := by
  first | exact @GlobalTheory.HL.RatStab.stab_rat | exact GlobalTheory.HL.RatStab.stab_rat | (intros; apply GlobalTheory.HL.RatStab.stab_rat <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.localCommonStabiliser_blockUnitriangular_on_frame : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ (p : HeightOneSpectrum (𝓞 F)) (h : (G.S p).GLV), h ∈ (G.S p).St → ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep, (∀ i j, ¬ (i < j ∧ ∀ l : Fin (r + 2), ((i : Fin (r + 1)) : ℕ) < l → (l : ℕ) ≤ ((j : Fin (r + 1)) : ℕ) → G.D l = 0) → s i j = if i = j then 1 else 0) ∧ (∀ j, h (A.bc p (G.f j)) = ∑ i, s i j • A.bc p (G.f i)) ∧ ((∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = G.c p) → h ∈ (G.S p).K0 → IsIntM (A.L p) s) := by
  first | exact @GlobalTheory.HL.LocPattern.local_pattern | exact GlobalTheory.HL.LocPattern.local_pattern | (intros; apply GlobalTheory.HL.LocPattern.local_pattern <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.framesCoordinateLattice_isTerm_trivialWitnesses : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → ∃ d₀, S.IsTermW d₀ (coordLat S) 1 1 := by
  first | exact @GlobalTheory.HL.CoordGood.main | exact GlobalTheory.HL.CoordGood.main | (intros; apply GlobalTheory.HL.CoordGood.main <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LiftEntry

theorem eI_inj {k r : ℕ} {a b : Fin r} : eI k r a = eI k r b ↔ a = b := by
  simp [eI, Fin.ext_iff]

theorem eI_ne_esI {k r : ℕ} (a b : Fin r) : eI k r a ≠ esI k r b := by
  simp only [eI, esI, ne_eq, Fin.ext_iff]; omega

theorem eI_ne_wI {k r : ℕ} (a : Fin r) (j : Fin (k + 1)) : eI k r a ≠ wI k r j := by
  simp only [eI, wI, ne_eq, Fin.ext_iff]; omega

theorem Hpk_esI {k r : ℕ} (b : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r b) j = if j = eI k r b then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem herm_single {k r : ℕ} (b : Fin r) (c : ℂ) (j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec j) (c • bvec (esI k r b)) = if j = eI k r b then star c else 0 := by
  simp only [herm, bvec, dotProduct, mulVec, Pi.star_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single (esI k r b)]
  · simp only [if_true, mul_one, star_mul', star_one]
    rw [Finset.sum_eq_single j]
    · simp [Hpk_esI]
    · intro m _ hm; simp [hm]
    · simp
  · intro m _ hm; simp [hm]
  · simp

theorem wI_ne_eI {k r : ℕ} (j : Fin (k + 1)) (a : Fin r) : wI k r j ≠ eI k r a := (eI_ne_wI a j).symm

theorem esI_ne_eI {k r : ℕ} (a b : Fin r) : esI k r a ≠ eI k r b := (eI_ne_esI b a).symm

end GlobalTheory.SnMass.VolN.LiftEntry

namespace GlobalTheory.SnMass.VolN.LiftEntry

theorem form_smul_left {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (c : E) (x z : Fin n → E) : form σ J (c • x) z = c * form σ J x z := by
  simp [form, mulVec_smul, dotProduct_smul]

theorem form_smul_right {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (c : E) (x z : Fin n → E) : form σ J x (c • z) = σ c * form σ J x z := by
  simp only [form, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem form_col {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} {a b : Type} [Fintype a] [Fintype b]
    (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) b E) (Y : Matrix (Fin n) a E) (i : a) (j : b) :
    form σ J (fun l => X l j) (fun l => Y l i) = pairM σ J X Y i j := by
  simp only [form, pairM, cT, dotProduct, mulVec, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end GlobalTheory.SnMass.VolN.LiftEntry

namespace GlobalTheory.SnMass.VolN.LiftEntry

theorem lift_entry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inl p) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inl p) → degB r β ≤ degB r (.inl p) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV p l hl
  have hV' := hV
  obtain ⟨hcm, -, -, -, -, hdu, htup, -, hs, had⟩ := hV'
  have hi : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    change τ (σ (σ x)) = _
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  obtain ⟨u, hu, hlu⟩ := hl
  obtain ⟨⟨a, b⟩, hab⟩ := p
  simp only at hu hlu hab ⊢
  set y : Fin (2 * r + k + 1) → E := (-(σ u)) • fun i => f i b with hy
  refine ⟨rowE (σ : E →+* E) J (fun i => P i a.castSucc) y 0, ?_, ?_⟩
  · refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV a y 0 (fun c hc => ?_) ?_ (fun c hc => ?_)
      (FractionalIdeal.zero_mem _)
    · rw [hy, form_smul_left, form_col, hdu.1]
      have : c.castSucc ≠ b.castSucc := fun h => absurd (Fin.castSucc_injective _ h ▸ hc) (not_le.2 hab)
      simp [this]
    · rw [hy, form_smul_left, form_smul_right, form_col, hdu.2]
      simp
    · have hsu : (σ : E →+* E) u ∈ dInv E (r - a.val) * (dInv E (r - b.val))⁻¹ :=
        (GlobalTheory.SnMass.FrameDual.Stab.mul (GlobalTheory.SnMass.FrameDual.stab_dInv hi _)
          ((GlobalTheory.SnMass.FrameDual.stab_dInv hi _).inv hi (GlobalTheory.SnMass.FrameDual.dInv_ne_zero _))) u hu
      have hm : c * σ u ∈ (dInv E (r - b.val))⁻¹ := by
        have := FractionalIdeal.mul_mem_mul hc hsu
        rwa [← mul_assoc, inv_mul_cancel₀ (GlobalTheory.SnMass.FrameDual.dInv_ne_zero _), one_mul] at this
      have e : c • y = (-(c * σ u)) • fun i => sideM P f i (Fin.natAdd (r + 1) b) := by
        ext i; simp [hy, sideM, mul_comm, mul_left_comm]
      rw [e]
      refine htup (Submodule.subset_span ⟨Fin.natAdd (r + 1) b, -(c * σ u), ?_, rfl⟩)
      rw [GlobalTheory.SnMass.FrameDual.frameDualTupleIdeals_natAdd]
      exact Submodule.neg_mem _ hm
  · have hv : ∀ w : InfinitePlace E, (A w).mulVec (fun l => w.embedding (y l)) =
        (-(star (w.embedding u)) * ((s b)⁻¹ : ℂ)) • bvec (esI k r b) := by
      intro w
      have e : (fun l => w.embedding (y l)) = (-(w.embedding (σ u))) • fun l => w.embedding (f l b) := by
        ext l; simp [hy]
      rw [e, mulVec_smul, (had w b).2, smul_smul, hcm.2.2.2]
    have key : ∀ (w : InfinitePlace E) (a' : Fin r) (j : Fin (2 * r + k + 1)),
        gM A (rowE (σ : E →+* E) J (fun i => P i a.castSucc) y 0) w (eI k r a') j =
          (if eI k r a' = j then 1 else 0) - (if a' = a ∧ j = eI k r b then
            (s a : ℂ) * star (-(star (w.embedding u)) * ((s b)⁻¹ : ℂ)) else 0) := by
      intro w a' j
      rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV a y 0 w, hv w, herm_single]
      simp [bvec, Pi.single_apply, eI_ne_esI, eI_inj, ite_and]
    refine ⟨fun w => ?_, fun β hβ _ w => ?_⟩
    · change gM A _ w (eI k r a) (eI k r b) = l w
      rw [key, hlu]
      simp only [eI_inj, hab.ne, if_false, true_and, if_true, zero_sub]
      push_cast
      simp only [star_mul', star_neg, star_star, Complex.star_def, Complex.conj_ofReal, map_inv₀, Complex.conj_conj]
      ring
    · rcases β with ⟨⟨a', b'⟩, hab'⟩ | a' | ⟨⟨a', b'⟩, hab'⟩ | a'
      · change gM A _ w (eI k r a') (eI k r b') = 0
        rw [key]
        have hne : ¬ (a' = a ∧ eI k r b' = eI k r b) := by
          rintro ⟨rfl, h⟩
          obtain rfl := eI_inj.1 h
          exact hβ rfl
        have hne' : a' ≠ b' := ne_of_lt hab'
        rw [if_neg hne, if_neg (fun h => hne' (eI_inj.1 h)), sub_zero]
      · change (fun j => gM A _ w (eI k r a') (wI k r j)) = (0 : Fin (k + 1) → ℂ)
        funext j
        rw [key]
        simp [eI_ne_wI, wI_ne_eI]
      · change gM A _ w (eI k r a') (esI k r b') = 0
        rw [key]
        simp [eI_ne_esI, esI_ne_eI]
      · change (gM A _ w (eI k r a') (esI k r a')).im = 0
        rw [key]
        simp [eI_ne_esI, esI_ne_eI]

end GlobalTheory.SnMass.VolN.LiftEntry
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LiftCorner

lemma hpk_eI (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

lemma herm_bvec (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) (x : ℂ) :
    herm (Hpk k r) (bvec j) (x • bvec (eI k r a)) = star x * (if j = esI k r a then 1 else 0) := by
  rw [← hpk_eI]
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite (starRingEnd ℂ), ite_mul]

lemma form_smul_left {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (u v : Fin n → E) (x : E) : form σ J (x • u) v = x * form σ J u v := by
  simp [form, Matrix.mulVec_smul, dotProduct_smul]

lemma form_smul_right {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (u v : Fin n → E) (x : E) : form σ J u (x • v) = σ x * form σ J u v := by
  simp [form, dotProduct, Finset.mul_sum, mul_assoc]

lemma form_cols {E : Type} [Field E] (σ : E →+* E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin m) E) (x z : Fin m) :
    form σ J (fun i => P i z) (fun i => P i x) = pairM σ J P P x z := by
  simp only [form, pairM, cT, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem lift_corner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inl p))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inl p))) → degB r β ≤ degB r (.inr (.inr (.inl p))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV p l hl
  obtain ⟨⟨a, b⟩, hab⟩ := p
  have hab' : a.val < b.val := hab
  have ha := a.isLt
  have hb := b.isLt
  obtain ⟨-, -, -, -, hFr, -, hLat, -, -, hAd⟩ := id hV
  obtain ⟨c, hc, hlc⟩ := hl
  dsimp only at hc hlc
  let e : Fin (2 * r + k + 1) → E := fun i => P i a.castSucc
  let y : Fin (2 * r + k + 1) → E := c • e
  have hiso : ∀ x z : Fin r,
      form (σ : E →+* E) J (fun i => P i z.castSucc) (fun i => P i x.castSucc) = 0 := by
    intro x z
    rw [form_cols, hFr.2]
    simp [TF, Matrix.diagonal_apply, Fin.castSucc_ne_last]
  have hd : ∀ j, dInv E j ≠ 0 := fun j =>
    pow_ne_zero _ (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot))
  have hG : rowE (σ : E →+* E) J (fun i => P i b.castSucc) y 0 ∈ GN (σ : E →+* E) J Λ P := by
    refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV b y 0 ?_ ?_ ?_ ?_
    · intro c' _
      show form _ J (c • e) _ = 0
      rw [form_smul_left, hiso, mul_zero]
    · show form _ J (c • e) (c • e) + 0 + (σ : E →+* E) 0 = 0
      rw [form_smul_left, form_smul_right, hiso]
      simp
    · intro c' hc'
      have hmem : c' * c ∈ dInv E (r - a.val) := by
        have := FractionalIdeal.mul_mem_mul hc' hc
        rwa [mul_comm (dInv E (r - a.val)), ← mul_assoc, inv_mul_cancel₀ (hd _), one_mul] at this
      have hy : c' • y = (c' * c) • e := by
        simp only [y, smul_smul]
      rw [hy]
      apply hLat
      apply Submodule.subset_span
      refine ⟨Fin.castAdd r a.castSucc, c' * c, ?_, ?_⟩
      · simpa [id1, Fin.append_left] using hmem
      · ext i
        simp [sideM, Fin.append_left, e]
    · exact (dInv E _ : Submodule (𝓞 E) E).zero_mem
  have hAy : ∀ w : InfinitePlace E, (A w).mulVec (fun l => w.embedding (y l)) =
      (w.embedding c * (s a : ℂ)) • bvec (eI k r a) := by
    intro w
    have h1 : (fun l => w.embedding (y l)) = w.embedding c • fun l => w.embedding (P l a.castSucc) := by
      ext l
      simp [y, e]
    rw [h1, Matrix.mulVec_smul, (hAd w a).1, smul_smul]
  have hent : ∀ w i j, gM A (rowE (σ : E →+* E) J (fun i => P i b.castSucc) y 0) w i j =
      (if i = j then 1 else 0) +
        (if i = eI k r a ∧ j = esI k r b then (s a : ℂ) * s b * w.embedding c else 0) -
        (if i = eI k r b ∧ j = esI k r a then (s b : ℂ) * star (w.embedding c * (s a : ℂ)) else 0) := by
    intro w i j
    rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV b y 0 w i j, hAy w, herm_bvec]
    simp only [bvec, Pi.smul_apply, Pi.single_apply, smul_eq_mul, map_zero, mul_zero, add_zero, ite_and]
    split_ifs <;> ring
  refine ⟨_, hG, fun w => ?_, fun β hβ _ w => ?_⟩
  · show gM A _ w (eI k r a) (esI k r b) = l w
    rw [hent, hlc w]
    have h1 : eI k r a ≠ esI k r b := by simp [Fin.ext_iff, eI, esI]; omega
    have h2 : eI k r a ≠ eI k r b := by simp [Fin.ext_iff, eI]; omega
    simp [h1, h2]
    first | done | (push_cast; ring)
  · rcases β with p' | a' | p' | a'
    · obtain ⟨⟨a', b'⟩, h'⟩ := p'
      have h'' : a'.val < b'.val := h'
      show gM A _ w (eI k r a') (eI k r b') = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · show (fun j' => gM A _ w (eI k r a') (wI k r j')) = (0 : Fin (k + 1) → ℂ)
      funext j'
      have := j'.isLt
      rw [hent]
      simp only [eI, esI, wI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · obtain ⟨⟨a', b'⟩, h'⟩ := p'
      have h'' : a'.val < b'.val := h'
      have hne : ¬ (a'.val = a.val ∧ b'.val = b.val) := by
        rintro ⟨e1, e2⟩
        obtain rfl := Fin.ext e1
        obtain rfl := Fin.ext e2
        exact hβ rfl
      show gM A _ w (eI k r a') (esI k r b') = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · show (gM A _ w (eI k r a') (esI k r a')).im = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp

end GlobalTheory.SnMass.VolN.LiftCorner
end

section

open MeasureTheory NumberField Finset

theorem _root_.GlobalTheory.T.dedekindZeta_residue_le_sixteen_log_rootDiscr_pow : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → 0 < dedekindZeta_residue K ∧ dedekindZeta_residue K ≤ (16 * Real.log (2 * Formalism.HermitianLatticesTheory.vInv K)) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
  first | exact @GlobalTheory.dedekindZeta_residue_le_log_rootDiscr_pow | exact GlobalTheory.dedekindZeta_residue_le_log_rootDiscr_pow | (intros; apply GlobalTheory.dedekindZeta_residue_le_log_rootDiscr_pow <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_global_unitriangular_of_local_congruence : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : GlobalTheory.HL.Places F E sig) (N r : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)), Λ.FG → ∀ (g : ℕ), 0 < g → ∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (y x : Fin (r + 1) → Fin N → E) (ξp : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep), (∀ a b, ξp a b ∈ (A.L p).O) → (∀ a b, b < a → ξp a b = 0) → (∀ a, ξp a a = 1) → (∀ a, A.bc p (y a) ∈ A.lat p Λ) → (∀ b, A.bc p (x b) - ∑ a, ξp a b • A.bc p (y a) ∈ A.lat p (Ideal.span {(g : 𝓞 E)} • Λ)) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal → ∀ b, x b - ∑ a, ((ξ a b : 𝓞 E) : E) • y a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ)) := by
  first | exact @GlobalTheory.HL.LocCongApprox.loc_cong_approx | exact GlobalTheory.HL.LocCongApprox.loc_cong_approx | (intros; apply GlobalTheory.HL.LocCongApprox.loc_cong_approx <;> assumption)
end
