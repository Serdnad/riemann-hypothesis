module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle259
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle276
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle279
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle242
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle257
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle278
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle280
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSelfDualETwo
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

private theorem selfDualK_full {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : IsSelfDualK G M) : Submodule.IsFullLattice K M := by
  classical
  haveI : Submodule.IsLattice K M := hM.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hM.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin n → K) → K := fun x => star x ⬝ᵥ G *ᵥ y
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) s f
  have ha0 : (algebraMap (𝓞 K) K a) ≠ 0 :=
    (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 K) (Fin n → K) := {
    carrier := {x | ∃ b : 𝓞 K, (b : K) = (algebraMap (𝓞 K) K a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : K) + c = _
      rw [hb, hc]
      simp [f, dotProduct, Matrix.mulVec, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd K) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def,
        RingOfIntegers.mapRingHom_apply, Pi.star_apply, star_mul, dotProduct, Matrix.mulVec,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : K) * _ = _
      ring }
  have hsP : (s : Set (Fin n → K)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 K) K a) • y ∈ M := by
    rw [← hM.2]
    change ∀ x ∈ M, star x ⬝ᵥ G *ᵥ ((algebraMap (𝓞 K) K a) • y) ∈ (1 : Submodule (𝓞 K) K)
    intro x hx
    obtain ⟨b, hb⟩ := (hs ▸ Submodule.span_le.mpr hsP) hx
    have hpair : (b : K) = star x ⬝ᵥ G *ᵥ ((algebraMap (𝓞 K) K a) • y) := by
      rw [hb]
      simp only [f, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    refine ⟨b, ?_⟩
    simpa [LinearMap.toSpanSingleton_apply, Algebra.smul_def] using hpair
  have hy' : (algebraMap (𝓞 K) K a) • y ∈ Submodule.span K (M : Set (Fin n → K)) :=
    Submodule.subset_span hy
  have := (Submodule.span K (M : Set (Fin n → K))).smul_mem (algebraMap (𝓞 K) K a)⁻¹ hy'
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

theorem testLatticeCondition_sumLat_nabK_and_delK : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric (sumGram lam e G) X → TestLatticeCondition N X (sumLat lam e fun c => nabK lam (M c)) (bound (Fintype.card ι) n R) ∧ TestLatticeCondition N X (sumLat lam e fun c => delK lam (M c)) (bound (Fintype.card ι) n R) := by
  intro K _ _ _ _ v₀ hv ι _ n lam R hR hsp G hG C _ M hM N e X hX
  classical
  obtain ⟨s, hs0, hs, hlog⟩ := GlobalTheory.T.pairing_normalising_constant_log_le_bound K ι n lam R hR hsp
  have hlat := fun c => GlobalTheory.T.nablaDeltaOperator_lattice_preserved K ι n lam (M c) (fun τ => selfDualK_full (G τ) (M c τ) (hM c τ))
  have main : ∀ T : C → Submodule (𝓞 K) (VV K lam), (∀ c, Submodule.IsFullLattice K (T c)) →
      (∀ c, T c ≤ nabK lam (M c)) → TestLatticeCondition N X (sumLat lam e T) (bound (Fintype.card ι) n R) := by
    intro T hT hle
    obtain ⟨hL, hN, -⟩ := GlobalTheory.T.orthogonalSumCoefficientLattice_isLattice_and_dual K ι n lam C N e T (fun c => (hT c).toIsLattice)
    haveI : Finite C :=
      Finite.of_injective (fun c => e.symm (c, (e ⟨0, hN⟩).2)) (fun a b h => by
        simpa using h)
    letI : Fintype C := Fintype.ofFinite C
    obtain ⟨hval, hdef, -, hdet⟩ := GlobalTheory.T.sumPairingGramMatrix_values_and_definite K ι n lam G hG C N e
    have hne : sumLat lam e T ≠ ⊥ := by
      intro h
      obtain ⟨c⟩ := (inferInstance : Nonempty C)
      obtain ⟨i⟩ := GlobalTheory.TestLat.SumLat.idx_nonempty lam
      have ht : ∃ t ∈ T c, t ≠ 0 := by
        by_contra hn
        push_neg at hn
        have hb : T c = ⊥ := by
          apply le_antisymm _ bot_le
          intro t ht
          simpa using hn t ht
        have hs := (hT c).span_eq_top
        rw [hb] at hs
        have hv := congrArg (fun S : Submodule K (VV K lam) => (bVV K lam i) ∈ S) hs
        have hv0 : bVV K lam i = 0 := by simpa using hv
        exact (bVV K lam).ne_zero i hv0
      obtain ⟨t, ht, ht0⟩ := ht
      let f := GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e
      let z := f.symm (Pi.single c t)
      have hz : z ∈ sumLat lam e T := by
        rw [GlobalTheory.TestLat.Model.mem_sumLat]
        intro c'
        have heq : valAt lam e c' z = (Pi.single c t : C → VV K lam) c' :=
          congrFun (f.apply_symm_apply (Pi.single c t)) c'
        rw [heq]
        by_cases hc : c' = c
        · subst hc; simpa using ht
        · simp [Pi.single_eq_of_ne hc]
      rw [h] at hz
      have hz0 : z = 0 := by simpa using hz
      have heq := congrFun (f.apply_symm_apply (Pi.single c t)) c
      change valAt lam e c z = (Pi.single c t : C → VV K lam) c at heq
      rw [hz0, map_zero, Pi.single_eq_same] at heq
      exact ht0 heq.symm
    refine ⟨hL.fg, hne, fun v => (hX v).1, le_trans ?_ hlog⟩
    refine GlobalTheory.T.maxSlope_le_log_of_integral_hermitian_form K v₀ hv N (sumGram lam e G) X ⟨hdef.2.1, hX⟩ s hs0 _ hL.fg hne ?_
    intro x hx y hy
    rw [hval, Finset.mul_sum, ← hs]
    refine Subring.sum_mem _ fun c _ => ?_
    have hmem : ∀ z ∈ sumLat lam e T, valAt lam e c z ∈ nabK lam (M c) := fun z hz =>
      hle c ((Submodule.mem_iInf _).1 hz c)
    exact GlobalTheory.T.extNorm_mul_weylPairing_integral_selfDual K ι n lam G (M c) (fun τ => (hG τ).1) hdet (hM c) _ (hmem x hx) _ (hmem y hy)
  exact ⟨main _ (fun c => (hlat c).1) (fun c => le_rfl),
    main _ (fun c => (hlat c).2) (fun c => delLeNab K ι n lam (M c))⟩

end GlobalTheory.TestLat
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.EdgeAlg

open GlobalTheory.K5.Basic

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zcong (n : ℕ) (A B : ℤ) (h : (A : ZMod (p ^ n)) = B) : Cong (p := p) n (A : Ω) (B : Ω) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨((-k : ℤ) : Ω), isInt_intCast _, ?_⟩
  have := congrArg (Int.cast : ℤ → Ω) hk
  push_cast at this ⊢
  linear_combination -this

theorem isInt_natCast (m : ℕ) : IsInt (p := p) (m : Ω) := by
  have := isInt_intCast (p := p) (Ω := Ω) (m : ℤ)
  simpa using this

theorem isInt_pow_p (c : ℕ) : IsInt (p := p) ((p : Ω) ^ c) := by
  have := isInt_natCast (p := p) (Ω := Ω) (p ^ c)
  simpa using this

theorem conj_invariant {G M : Type*} [Group G] [AddCommGroup M] (H : Subgroup G) (φ : G → M)
    (hφ : ∀ g ∈ H, ∀ h ∈ H, φ (g * h) = φ g + φ h) {σ h : G} (hσ : σ ∈ H) (hh : h ∈ H) :
    φ (σ * h * σ⁻¹) = φ h := by
  have h1 : φ 1 = 0 := by
    have e := hφ 1 H.one_mem 1 H.one_mem
    rw [mul_one] at e
    have e' : φ 1 + φ 1 = φ 1 + 0 := by rw [add_zero, ← e]
    exact add_left_cancel e'
  have h2 : φ σ + φ σ⁻¹ = 0 := by
    rw [← hφ σ hσ σ⁻¹ (H.inv_mem hσ), mul_inv_cancel, h1]
  rw [hφ _ (H.mul_mem hσ hh) _ (H.inv_mem hσ), hφ σ hσ h hh, add_right_comm, h2, zero_add]

theorem zeta_eq_pow (T : Tower p Ω) (m k : ℕ) : T.ζ m = T.ζ (m + k) ^ p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    show _ = T.ζ (m + k + 1) ^ p ^ (k + 1)
    rw [ih, ← T.ζpow (m + k), ← pow_mul, ← pow_succ']

theorem gn_fix_zeta (T : Tower p Ω) {L n : ℕ} (hn : n ≤ L) {g : Gal p Ω} (hg : g ∈ Gn T L) :
    g (T.ζ n) = T.ζ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [zeta_eq_pow T n k, map_pow, ((mem_gn T _ g).1 hg).1]

theorem kum_add (T : Tower p Ω) {L n : ℕ} (hn : n ≤ L) {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T L) r a) : ∀ g ∈ Gn T L, ∀ h ∈ Gn T L, a (g * h) = a g + a h := by
  intro g hg h hh
  obtain ⟨χ, hχ⟩ := exists_isCyc T n
  have h1 : χ g = 1 := (isCyc_eq_one_iff hχ g).2 (gn_fix_zeta T hn hg)
  rw [isKum_mul hχ hr ha hg hh, h1, one_mul]

theorem isAlgZp_zeta (T : Tower p Ω) (m : ℕ) : IsAlgZp p (T.ζ m) := by
  refine ⟨Polynomial.X ^ (p ^ m) - Polynomial.C 1,
    Polynomial.X_pow_sub_C_ne_zero (pow_pos hp.out.pos m) 1, ?_⟩
  simp [(T.prim m).pow_eq_one]

theorem kum_geo_zero (T : Tower p Ω) {n m : ℕ} {H : Subgroup (Gal p Ω)} {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n H (T.ζ m) a) {g : Gal p Ω} (hH : g ∈ H) (hg : g ∈ Ggeo p Ω) : a g = 0 := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hg' : ∀ x : Ω, IsAlgZp p x → g x = x := hg
  have e := ha g hH
  rw [hg' _ (isAlgZp_zeta T m)] at e
  have hz : T.ζ m ≠ 0 := (T.prim m).ne_zero (pow_ne_zero _ hp.out.ne_zero)
  have e1 : T.ζ n ^ (a g).val = 1 := mul_right_cancel₀ hz (by rw [one_mul]; exact e.symm)
  have e2 : T.ζ n ^ (a g).val = T.ζ n ^ (0 : ℕ) := by rw [pow_zero]; exact e1
  rw [zeta_pow_eq_iff, ← ZMod.natCast_eq_natCast_iff] at e2
  simpa using e2

theorem conj_mem_ggeo {σ h : Gal p Ω} (hh : h ∈ Ggeo p Ω) : σ * h * σ⁻¹ ∈ Ggeo p Ω := by
  have hh' : ∀ x : Ω, IsAlgZp p x → h x = x := hh
  show ∀ x : Ω, IsAlgZp p x → (σ * h * σ⁻¹) x = x
  rintro x ⟨P, hP, hPx⟩
  have hx' : IsAlgZp p (σ⁻¹ x) := ⟨P, hP, by
    have := Polynomial.aeval_algHom_apply (σ⁻¹ : Gal p Ω).toAlgHom x (P.map (algebraMap ℤ_[p] (O0 p)))
    rw [hPx, map_zero] at this
    exact this⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hh' _ hx', ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

end GlobalTheory.EdgeAlg

namespace GlobalTheory.EdgeAlg

open GlobalTheory.K5.Basic

theorem edge_class_cup : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ c₁ : ℕ, ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ (x y lz lq η : Gal p Ω → ZMod (p ^ n)) (f : Ω),
  (∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h ∧ y (g * h) = y g + y h) →
  IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq → IsInt (p := p) f → (∀ g ∈ Gn T L, g f = f) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), x g * y h = η h - η (g * h) + η g) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∃ S : Finset Ω, ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), (∀ z ∈ S, h z = g z) → η h = η g) →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c₁ * (((x g).val : Ω) * ((y h).val : Ω)) + (p : Ω) ^ c₁ * f * (((lz g).val : Ω) * ((lq h).val : Ω))) →
  ∃ o : Ω, IsInt (p := p) o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ ∀ σ ∈ Gn T L,
    Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun h => (p : Ω) ^ c * ((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : Ω) - (σ⁻¹ o - o - (p : Ω) ^ c * f * ((lz σ).val : Ω)) * ((lq h).val : Ω)) := by
  classical
  intro p _ hp2 c₁
  obtain ⟨c', hc'⟩ := GlobalTheory.T.geometric_level_h1_coboundary p hp2
  refine ⟨c₁ + c', ?_⟩
  intro Ω _ _ hclo T L n hnL x y lz lq η f hxy hlz hlq hfi hff hη hηlc hcob
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨W, ⟨hWi, hWlc⟩, hW⟩ := hcob
  have hx_add : ∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h := fun g hg h hh => (hxy g hg h hh).1
  have hlq_add := kum_add T hnL (qq_ne_zero T (L + n)) hlq
  have hlz0 : ∀ g ∈ (Ggeo p Ω ⊓ Gn T L), lz g = 0 := fun g hg =>
    kum_geo_zero T hlz (Subgroup.mem_inf.1 hg).2 (Subgroup.mem_inf.1 hg).1
  have hlqΔ : IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq := fun g hg => hlq g (Subgroup.mem_inf.1 hg).2
  let a : Gal p Ω → Ω := fun g => (p : Ω) ^ c₁ * ((η g).val : Ω) - W g
  have haLC : IntegralLocallyConstCochainModPow n (Ggeo p Ω ⊓ Gn T L) a := by
    refine ⟨fun g _ => IsIntegral.sub (IsIntegral.mul (isInt_pow_p c₁) (isInt_natCast _)) (hWi g), fun g hg => ?_⟩
    obtain ⟨S1, hS1⟩ := hηlc g hg
    obtain ⟨S2, hS2⟩ := hWlc g
    refine ⟨S1 ∪ S2, fun h hh hS => ?_⟩
    have e1 := hS1 h hh (fun z hz => hS z (Finset.mem_union_left _ hz))
    have e2 := hS2 h (fun z hz => hS z (Finset.mem_union_right _ hz))
    simp only [a, e1]
    exact cong_sub (cong_refl _ _) e2
  have haCoc : ∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L),
      Cong (p := p) n (a (g * h)) (a g + g (a h)) := by
    intro g hg h hh
    have hgG := (Subgroup.mem_inf.1 hg).2
    have hhG := (Subgroup.mem_inf.1 hh).2
    obtain ⟨w, hw, ew⟩ := hW g hgG h hhG
    obtain ⟨u, hu, eu⟩ := zcong (p := p) (Ω := Ω) n (((x g).val : ℤ) * ((y h).val : ℤ))
      (((η h).val : ℤ) - ((η (g * h)).val : ℤ) + ((η g).val : ℤ)) (by
        simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
        exact hη g hg h hh)
    simp only [hlz0 g hg, ZMod.val_zero, Nat.cast_zero] at ew
    refine ⟨(p : Ω) ^ c₁ * u - w, IsIntegral.sub (IsIntegral.mul (isInt_pow_p c₁) hu) hw, ?_⟩
    simp only [a, map_sub, map_mul, map_pow, map_natCast]
    push_cast at eu
    linear_combination (p : Ω) ^ c₁ * eu - ew
  obtain ⟨o, hoi, hofix, z, hzi, hz⟩ := (hc' Ω hclo T L n hnL lq hlqΔ).1 a haLC haCoc
  refine ⟨o, hoi, hofix, fun σ hσ => ?_⟩
  have hsi : ∀ v : Ω, σ⁻¹ (σ v) = v := fun v => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hfs : σ⁻¹ f = f := hff _ ((Gn T L).inv_mem hσ)
  refine ⟨σ⁻¹ (z - σ z - (p : Ω) ^ c' * W σ),
    isInt_gal _ (IsIntegral.sub (IsIntegral.sub hzi (isInt_gal σ hzi)) (IsIntegral.mul (isInt_pow_p c') (hWi σ))),
    fun h hh => ?_⟩
  have hhG := (Subgroup.mem_inf.1 hh).2
  have hh2 : σ * h * σ⁻¹ ∈ (Ggeo p Ω ⊓ Gn T L) := Subgroup.mem_inf.2
    ⟨conj_mem_ggeo (Subgroup.mem_inf.1 hh).1, (Gn T L).mul_mem ((Gn T L).mul_mem hσ hhG) ((Gn T L).inv_mem hσ)⟩
  have hh2G := (Subgroup.mem_inf.1 hh2).2
  have hcomm : σ * h * σ⁻¹ * σ = σ * h := by group
  have hxh2 : x (σ * h * σ⁻¹) = x h := conj_invariant (Gn T L) x hx_add hσ hhG
  have hlqh2 : lq (σ * h * σ⁻¹) = lq h := conj_invariant (Gn T L) lq hlq_add hσ hhG
  have hlzh2 : lz (σ * h * σ⁻¹) = 0 := hlz0 _ hh2
  have hsh : σ (h z) = (σ * h * σ⁻¹) (σ z) := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hsi]
  have hs2 : ∀ v : Ω, σ⁻¹ ((σ * h * σ⁻¹) v) = h (σ⁻¹ v) := fun v => by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hsi]
  obtain ⟨w1, hw1, e1⟩ := hW _ hh2G σ hσ
  obtain ⟨w2, hw2, e2⟩ := hW σ hσ h hhG
  obtain ⟨w3, hw3, e3⟩ := hz h hh
  obtain ⟨w4, hw4, e4⟩ := hz _ hh2
  obtain ⟨u0, hu0, e0⟩ := zcong (p := p) (Ω := Ω) n
    (((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : ℕ) : ℤ)
    (((η (σ * h * σ⁻¹)).val : ℤ) - ((η h).val : ℤ) - ((x h).val : ℤ) * ((y σ).val : ℤ) + ((x σ).val : ℤ) * ((y h).val : ℤ))
    (by simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val])
  push_cast at e0
  simp only [hxh2, hlzh2, hcomm, ZMod.val_zero, Nat.cast_zero] at e1
  simp only [a, hlqh2] at e3 e4
  have e3s := congrArg σ e3
  simp only [map_sub, map_mul, map_pow, map_natCast, hsh] at e3s
  have K : (p : Ω) ^ c₁ * (p : Ω) ^ c' * (((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : ℕ) : Ω)
      - (o - σ o - (p : Ω) ^ c₁ * (p : Ω) ^ c' * f * ((lz σ).val : Ω)) * ((lq h).val : Ω)
      - (((σ * h * σ⁻¹) z - (σ * h * σ⁻¹) (σ z) - (p : Ω) ^ c' * (σ * h * σ⁻¹) (W σ)) - (z - σ z - (p : Ω) ^ c' * W σ))
      = (p : Ω) ^ n * ((p : Ω) ^ c₁ * (p : Ω) ^ c' * u0 - (p : Ω) ^ c' * w1 + (p : Ω) ^ c' * w2 + w4 - σ w3) := by
    linear_combination (p : Ω) ^ c₁ * (p : Ω) ^ c' * e0 - (p : Ω) ^ c' * e1 + (p : Ω) ^ c' * e2 + e4 - e3s
  refine ⟨σ⁻¹ ((p : Ω) ^ c₁ * (p : Ω) ^ c' * u0 - (p : Ω) ^ c' * w1 + (p : Ω) ^ c' * w2 + w4 - σ w3), isInt_gal _ ?_, ?_⟩
  · exact IsIntegral.sub (IsIntegral.add (IsIntegral.add (IsIntegral.sub
      (IsIntegral.mul (IsIntegral.mul (isInt_pow_p c₁) (isInt_pow_p c')) hu0)
      (IsIntegral.mul (isInt_pow_p c') hw1)) (IsIntegral.mul (isInt_pow_p c') hw2)) hw4) (isInt_gal σ hw3)
  · have KS := congrArg (⇑(σ⁻¹ : Gal p Ω)) K
    simp only [map_sub, map_mul, map_pow, map_natCast, map_add (f := _), hs2, hsi, hfs] at KS
    simp only [map_sub, map_mul, map_pow, map_natCast, map_add (f := _), hsi, pow_add]
    linear_combination KS

end GlobalTheory.EdgeAlg
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.isogeny_fibres_even_theta_sigmaStarSquareQuotient : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (β t₀ : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β + starRingEnd ℂ β = 1 → β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) → 2 * t₀ ∈ Λ → β * t₀ ∉ Λ → (1 - β) * t₀ ∉ Λ → ∃ (Q : Fin k → ℂ) (Q' : Fin (2 * k) → ℂ), (∀ i, Q i ∉ Λ ∧ InRationalLattice Λ (Q i)) ∧ (∀ j, Q' j ∉ Λ ∧ InRationalLattice Λ (Q' j)) ∧ (∀ z, GL3Theta.th0 Λ t₀ (β * z) = ∏ i, sqTh Λ (Q i) z) ∧ (∀ z, sqTh Λ (β * t₀) (β * z) = ∏ j, sqTh Λ (Q' j) z) ∧ (∀ i j, wpF Λ (Q i) ≠ wpF Λ (Q' j)) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ t₀) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ (β * t₀)) ∧ wpF Λ t₀ ≠ wpF Λ (β * t₀) := by
  first | exact @GlobalTheory.EvenTheta.Fibres.isogeny_fibres | exact GlobalTheory.EvenTheta.Fibres.isogeny_fibres | (intros; apply GlobalTheory.EvenTheta.Fibres.isogeny_fibres <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

namespace GlobalTheory.FrobStickMap

theorem hasSubst_of_cc {R : Type*} [CommRing R] (a : MvPowerSeries (Fin 3) R)
    (ha : MvPowerSeries.constantCoeff a = 0) : PowerSeries.HasSubst a :=
  PowerSeries.HasSubst.of_constantCoeff_zero ha

theorem map_defect {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S)
    (f : Fin 3 → R⟦X⟧) (s : R⟦X⟧) :
    MvPowerSeries.map h (GlobalTheory.FrobStick.defect f s)
      = GlobalTheory.FrobStick.defect (fun j => PowerSeries.map h (f j)) (PowerSeries.map h s) := by
  have hs : ∀ (a : MvPowerSeries (Fin 3) R), MvPowerSeries.constantCoeff a = 0 → ∀ g : R⟦X⟧,
      MvPowerSeries.map h (subst a g) = subst (MvPowerSeries.map h a) (PowerSeries.map h g) :=
    fun a ha g => PowerSeries.map_subst (hasSubst_of_cc a ha) g
  unfold GlobalTheory.FrobStick.defect
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, map_ofNat]
  rw [RingHom.map_det]
  congr 1
  · congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [hs _ (by simp) _]
    simp
  · rw [hs _ (by simp), hs _ (by simp), hs _ (by simp), hs _ (by simp)]
    simp [map_add (f := _), map_sub]

end GlobalTheory.FrobStickMap

namespace GlobalTheory.FrobStickMap

noncomputable def tq (F : ℂ → ℂ) : (↥Qbar)⟦X⟧ :=
  PowerSeries.mk (fun n => if h : coef1 F n ∈ Qbar then ⟨_, h⟩ else 0)

theorem map_tq_of_algEnt (F : ℂ → ℂ) (hF : AlgEnt F) :
    PowerSeries.map (algebraMap (↥Qbar) ℂ) (tq F) = GlobalTheory.FrobStick.tay F := by
  ext n
  simp only [tq, GlobalTheory.FrobStick.tay, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rw [dite_eq_left (hF.2 n)]
  rfl

theorem mvmap_injective {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S)
    (hi : Function.Injective h) :
    Function.Injective (MvPowerSeries.map (σ := Fin 3) h) := by
  intro a b hab
  ext n
  apply hi
  have := congrArg (MvPowerSeries.coeff n) hab
  simpa [MvPowerSeries.coeff_map] using this

theorem defect_ser1_eq_zero_of_defect_tay_eq_zero (p : ℕ) [Fact p.Prime] (lam : (↥Qbar) →+* ℂ_[p]) (f : Fin 3 → ℂ → ℂ)
    (s : ℂ → ℂ) (hf : ∀ j, AlgEnt (f j)) (hs : AlgEnt s)
    (h0 : GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (f j)) (GlobalTheory.FrobStick.tay s) = 0) :
    GlobalTheory.FrobStick.defect (fun j => GL3Theta.ser1 lam (f j)) (GL3Theta.ser1 lam s) = 0 := by
  have hq : GlobalTheory.FrobStick.defect (fun j => tq (f j)) (tq s) = 0 := by
    apply mvmap_injective (algebraMap (↥Qbar) ℂ) (FaithfulSMul.algebraMap_injective _ _)
    rw [map_defect, map_zero]
    simp only [map_tq_of_algEnt _ (hf _), map_tq_of_algEnt _ hs]
    exact h0
  have hser : ∀ F : ℂ → ℂ, AlgEnt F → GL3Theta.ser1 lam F = PowerSeries.map lam (tq F) := fun F hF =>
    GlobalTheory.EvenTheta.Param.theta_series_map_coefficients lam F (tq F) (map_tq_of_algEnt F hF).symm
  simp only [hser _ (hf _), hser _ hs]
  rw [← map_defect, hq, map_zero]

end GlobalTheory.FrobStickMap
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaTripleConstant_eq_one_distributive : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → Dist A₁ A₂ A₃ → μ = 1 := by
  first | exact @GlobalTheory.DistTriple.const_eq_one | exact GlobalTheory.DistTriple.const_eq_one | (intros; apply GlobalTheory.DistTriple.const_eq_one <;> assumption)
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.exists_almostGalois_coordinates : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∃ (ι : Type) (_ : Fintype ι) (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) ∧ (∀ k, v k ∈ FixI (Hfix T r)) ∧
  ∑ k, u k * v k = (p : Ω) ∧ ∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0 := by
  first | exact @GlobalTheory.KumDlog.almostGal_coord | exact GlobalTheory.KumDlog.almostGal_coord | (intros; apply GlobalTheory.KumDlog.almostGal_coord <;> assumption)
end
