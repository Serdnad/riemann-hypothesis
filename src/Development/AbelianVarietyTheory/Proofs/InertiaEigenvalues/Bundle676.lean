module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle545
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle642
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle599
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle451
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle639
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle645
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle646
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.LowLevel

section Series

variable {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M]

theorem conv_one (f : ℤ → M) : conv (1 : PowerSeries LL) f = f := by
  funext k
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem mem_latSpan {ι : Type} (e : ι → ℤ → M) (x : ι) : e x ∈ latSpan (LL := LL) e :=
  Submodule.subset_span ⟨1, x, (conv_one _).symm⟩

theorem neg_eq_zero {ι : Type} {e : ι → ℤ → M} {D : Submodule LL M} (h : Std D (latSpan e))
    (x : ι) (k : ℤ) (hk : k < 0) : e x k = 0 :=
  ((h _).1 (mem_latSpan e x)).2 k hk

theorem span_const {ι : Type} {e : ι → ℤ → M} {D : Submodule LL M} (h : Std D (latSpan e)) :
    Submodule.span LL (Set.range fun x => e x 0) = D := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ((h _).1 (mem_latSpan e x)).1 0
  · intro d hd
    have key : ∀ f ∈ latSpan (LL := LL) e, f 0 ∈ Submodule.span LL (Set.range fun x => e x 0) := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨a, x, rfl⟩ := hf
        unfold conv
        rw [finsum_eq_single _ 0]
        · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_⟩)
          simp
        · intro j hj
          rw [neg_eq_zero h x _ (by omega), smul_zero]
      | zero => exact Submodule.zero_mem _
      | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
      | smul c f _ hf => exact Submodule.smul_mem _ c hf
    have hmem : (Pi.single (0 : ℤ) d : ℤ → M) ∈ latSpan (LL := LL) e := by
      refine (h _).2 ⟨fun k => ?_, fun k hk => Pi.single_eq_of_ne hk.ne _⟩
      by_cases hk : k = 0
      · subst hk
        simpa using hd
      · rw [Pi.single_eq_of_ne hk]
        exact D.zero_mem
    simpa using key _ hmem

theorem span_const_map {M' ι : Type} [AddCommGroup M'] [Module LL M'] {e : ι → ℤ → M}
    {D : Submodule LL M} (h : Std D (latSpan e)) (L : M →ₗ[LL] M') (g : ι → M')
    (hg : ∀ x, g x = L (e x 0)) : Submodule.span LL (Set.range g) = D.map L := by
  rw [← span_const h, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext x
  exact hg x

theorem conv_low (w : PowerSeries LL) (k : ℕ) (f : ℤ → M) (hf : ∀ j < 0, f j = 0) (j : ℤ)
    (hj : j < k) : conv ((PowerSeries.X * w) ^ k) f j = 0 := by
  unfold conv
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : m < k
  · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]
  · rw [hf _ (by omega), smul_zero]

theorem conv_lead (w : PowerSeries LL) (k : ℕ) (f : ℤ → M) (hf : ∀ j < 0, f j = 0) :
    conv ((PowerSeries.X * w) ^ k) f k = PowerSeries.constantCoeff w ^ k • f 0 := by
  unfold conv
  rw [finsum_eq_single _ k]
  · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl]
    simp
  · intro m hmk
    by_cases hm : m < k
    · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]
    · rw [hf _ (by omega), smul_zero]

theorem pullback_span {M' ι : Type} [AddCommGroup M'] [Module LL M'] {P : ι → ℕ → Prop}
    (y : ∀ x k, P x k → ι) (lN : ι → ℤ → M') (e e' : ι → ℤ → M) {D D' : Submodule LL M}
    (L : M →ₗ[LL] M') (φ : M →ₗ[LL] M) (c : LL) (q : PowerSeries LL)
    (hq : ∃ w, IsUnit w ∧ q = PowerSeries.X * w)
    (hN : ∀ x k, lN x k = L (e x k)) (hmem : ∀ x k, e x k ∈ D) (hS : Std D' (latSpan e'))
    (hφ : ∀ x k hk j, e (y x k hk) j = conv (q ^ k) (fun j => c ^ j • φ (e' x j)) j)
    (hsurj : Set.SurjOn φ D' D) (hex : ∀ x, ∃ k, P x k) :
    (∀ x k hk (j : ℤ), lN (y x k hk) j ∈ D.map L ∧ (j < k → lN (y x k hk) j = 0)) ∧
      Submodule.span LL {z | ∃ x k hk, z = lN (y x k hk) (k : ℕ)} = D.map L := by
  obtain ⟨w, hw, rfl⟩ := hq
  have hm : ∀ x k, lN x k ∈ D.map L := fun x k => by
    rw [hN]
    exact Submodule.mem_map_of_mem (hmem x k)
  have hg0 : ∀ x, ∀ j < (0 : ℤ), c ^ j • φ (e' x j) = 0 := by
    intro x j hj
    rw [neg_eq_zero hS x j hj, map_zero, smul_zero]
  have hc : PowerSeries.constantCoeff w ≠ 0 := (hw.map PowerSeries.constantCoeff).ne_zero
  refine ⟨fun x k hk j => ⟨hm _ _, fun hj => ?_⟩, le_antisymm ?_ ?_⟩
  · rw [hN, hφ, conv_low w k _ (hg0 x) j hj, map_zero]
  · rw [Submodule.span_le]
    rintro _ ⟨x, k, hk, rfl⟩
    exact hm _ _
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨d', hd', rfl⟩ := hsurj hd
    have hd'' : d' ∈ Submodule.span LL (Set.range fun x => e' x 0) := by
      rw [span_const hS]
      exact hd'
    clear hd hd'
    induction hd'' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      obtain ⟨k, hk⟩ := hex x
      have h2 : L (φ (e' x 0)) = (PowerSeries.constantCoeff w ^ k)⁻¹ • lN (y x k hk) k := by
        rw [hN, hφ, conv_lead w k _ (hg0 x), map_smul, inv_smul_smul₀ (pow_ne_zero _ hc)]
        simp only [zpow_zero, one_smul]
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, k, hk, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      rw [map_smul, map_smul]
      exact Submodule.smul_mem _ c ha

theorem low_span {M' ι : Type} [AddCommGroup M'] [Module LL M'] (a : ι → ι) (lN : ι → ℤ → M')
    (e : ι → ℤ → M) {D : Submodule LL M} (L : M →ₗ[LL] M') (q : PowerSeries LL) (hq : q = 1)
    (ha : ∀ x k, lN (a x) k = conv q (lN x) k)
    (hN : ∀ x k, lN x k = L (e x k)) (hS : Std D (latSpan e)) :
    (∀ x (k : ℤ), lN (a x) k ∈ D.map L ∧ (k < 0 → lN x k = 0)) ∧
      Submodule.span LL (Set.range fun x => lN (a x) 0) = D.map L := by
  subst hq
  simp only [conv_one] at ha
  refine ⟨fun x k => ⟨?_, fun hk => ?_⟩, span_const_map hS L _ fun x => by rw [ha, hN]⟩
  · rw [hN]
    exact Submodule.mem_map_of_mem (((hS _).1 (mem_latSpan e _)).1 k)
  · rw [hN, neg_eq_zero hS x k hk, map_zero]

end Series

theorem exists_primitive {L : Type} [Field L] {l : ℕ} (hl : l.Prime) {ζ : L} {m : ℕ}
    (h : ζ ^ (l ^ m) = 1) : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).1 (orderOf_dvd_of_pow_eq_one h)
  exact ⟨j, hj ▸ IsPrimitiveRoot.orderOf ζ⟩

theorem pow_pow_pred {L : Type} [Field L] {l s : ℕ} (hs : 1 ≤ s) {ζ : L}
    (h : IsPrimitiveRoot ζ (l ^ s)) : (ζ ^ l) ^ (l ^ (s - 1)) = 1 := by
  rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hs]
  exact h.pow_eq_one



theorem expansions_low_and_pullback : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ (i : Let K) (ζ : ↥LL.1), (∃ m : ℕ, ζ ^ (((D.loc l).PD K).p ^ m) = 1) → PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 → (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : AA K LL) • x) k ∈ (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) ∧ (k < 0 → W.levN T i ζ x k = 0)) ∧ Submodule.span ↥LL.1 (Set.range fun x : ↥(W.N T) => W.levN T i ζ ((letE i : AA K LL) • x) 0) = (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V))) ∧ ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → (∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ), W.levN T i ζ ⟨_, hk⟩ j ∈ (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0)) ∧ Submodule.span ↥LL.1 {w | ∃ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T), w = W.levN T i ζ ⟨_, hk⟩ k} = (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := by
  intro D HW F Cm l _ K s LL h W E C T hT
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hstd : ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 →
      Std (Di (HW l) h T i) (latSpan (ex C h T i ζ)) := GlobalTheory.T.wachLattice_expansions_std_below_level D HW F Cm l K s LL h T hT
  refine ⟨fun i ζ hζ hX => ?_, fun i ζ τ hτ => ?_⟩
  · have hm : ζ ^ (l ^ hζ.choose) = 1 := by
      have := hζ.choose_spec
      rwa [show ((D.loc l).PD K).p ^ hζ.choose = l ^ hζ.choose from congrArg (· ^ _) hp] at this
    have hl := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ (exists_primitive Fact.out hm)
    exact low_span (fun x => (letE i : AA K LL) • x) (W.levN T i ζ) (ex C h T i ζ) _
      (W.lev i ζ (letE i)) hl.2.1 (W.levN_smul T i ζ (letE i))
      ((C.C K s LL h).tie.levN_eq T i ζ) (hstd i ζ (hl.2.2.2.2.1.1 hX))
  · have hprim : IsPrimitiveRoot ζ (l ^ s) :=
      ((GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hτ).1
    have hl := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hprim⟩
    have hφ : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ),
        ex C h T i ζ ⟨_, hk⟩ j = conv ((W.lev i ζ W.Q) ^ k) (fun j => (l : ↥LL.1) ^ j •
          φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (ex C h T (i - 1) (ζ ^ l) x j)) j := by
      intro x k hk j
      have h1 := (C.C K s LL h).tie.levB_φ T hT i ζ ⟨s, by rw [hp]; exact hprim⟩ x k hk j
      rw [map_pow, hp] at h1
      exact h1
    exact pullback_span (P := fun (x : ↥(W.N T)) k => W.Q ^ k • W.φD T x ∈ W.N T)
      (fun _ _ hk => ⟨_, hk⟩) (W.levN T i ζ) (ex C h T i ζ) (ex C h T (i - 1) (ζ ^ l)) _ _ _ _
      (hl.2.2.2.1 hprim).1 ((C.C K s LL h).tie.levN_eq T i ζ) ((C.C K s LL h).tie.levB_mem T i ζ)
      (hstd (i - 1) (ζ ^ l) (pow_pow_pred h.1 hprim)) hφ
      ((GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum D HW l K s LL h T hT).1 i).surjOn (fun x => W.N_φ T x x.2)

end GlobalTheory.NL.LowLevel
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HwUpper

theorem telescope (d : ℕ → ℂ) (f : ℕ → ℕ) (hf : ∀ s, f (s + 1) ≤ f s) (m : ℕ) :
    (∏ s ∈ Finset.range m, (∏ k ∈ Finset.range (s + 1), d k) ^ (f s - f (s + 1))) *
      (∏ k ∈ Finset.range m, d k) ^ f m = ∏ k ∈ Finset.range m, d k ^ f k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ (fun k => d k ^ f k), ← ih, mul_assoc, mul_assoc]
    congr 1
    rw [← pow_add, Nat.sub_add_cancel (hf m), Finset.prod_range_succ, mul_pow]

theorem hwScal_transpose {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) (B : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.BasicNotions.Examples₂.NZ.hwScal ℂ (le_refl n) ν B.transpose = ∏ i, B i i ^ ν i := by
  classical
  set d : ℕ → ℂ := fun k => if h : k < n then B ⟨k, h⟩ ⟨k, h⟩ else 1 with hd
  set f : ℕ → ℕ := fun k => if h : k < n then ν ⟨k, h⟩ else 0 with hfd
  have hf : ∀ s, f (s + 1) ≤ f s := by
    intro s
    by_cases h : s + 1 < n
    · simp only [hfd, dif_pos h, dif_pos (show s < n by omega)]
      exact hν (show (⟨s, by omega⟩ : Fin n) ≤ ⟨s + 1, h⟩ from Fin.mk_le_mk.mpr (by omega))
    · simp only [hfd, dif_neg h]
      exact Nat.zero_le _
  have hinner : ∀ s : Fin n, (∏ a : Fin (s.val + 1),
      B.transpose (Fin.castLE (by omega) a) (Fin.castLE (by omega) a)) = ∏ k ∈ Finset.range (s.val + 1), d k := by
    intro s
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun a _ => ?_
    have ha : a.val < n := by omega
    simp only [hd, dif_pos ha, Matrix.transpose_apply]
    rfl
  have hexp : ∀ s : Fin n, ν s - Formalism.GradedWeylDivisibility.nuNext ν s = f s.val - f (s.val + 1) := by
    intro s
    simp only [hfd, dif_pos s.2, Formalism.GradedWeylDivisibility.nuNext]
  unfold Formalism.BasicNotions.Examples₂.NZ.hwScal
  simp_rw [hinner, hexp]
  rw [Fin.prod_univ_eq_prod_range (fun s => (∏ k ∈ Finset.range (s + 1), d k) ^ (f s - f (s + 1))) n]
  have hfn : f n = 0 := by simp [hfd]
  have ht := telescope d f hf n
  rw [hfn, pow_zero, mul_one] at ht
  rw [ht, ← Fin.prod_univ_eq_prod_range (fun k => d k ^ f k) n]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [hd, hfd, dif_pos i.2]

theorem exists_hw_upper : ∀ (n : ℕ) (lam : DomWeight n), ∃ v : nablaSq ℂ n lam, v ≠ 0 ∧
    ∀ B : GL (Fin n) ℂ, (B : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id →
      GlobalTheory.Branching.sqRep ℂ n lam B v = (∏ i, ((B : Matrix (Fin n) (Fin n) ℂ) i i) ^ (lam.w i)) • v := by
  intro n lam
  have ha : Antitone lam.natW := fun i j hij => by
    have := lam.anti hij
    simp only [DomWeight.natW]
    omega
  refine ⟨⟨extremal ℂ n lam, Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ ha⟩, fun h =>
    Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl lam.natW (congrArg Subtype.val h), fun B hB => ?_⟩
  apply Subtype.ext
  set M : Matrix (Fin n) (Fin n) ℂ := (B : Matrix (Fin n) (Fin n) ℂ) with hM
  have hl : ∀ i j : Fin n, i < j → M.transpose i j = 0 := fun i j hij => by
    rw [Matrix.transpose_apply]; exact hB hij
  have hdet : M.det = ∏ i, M i i := Matrix.det_of_upperTriangular hB
  have hne : ∀ i, M i i ≠ 0 := by
    have h0 : M.det ≠ 0 := by
      have := (Matrix.GeneralLinearGroup.det B).ne_zero
      simpa [hM] using this
    rw [hdet, Finset.prod_ne_zero_iff] at h0
    exact fun i => h0 i (Finset.mem_univ i)
  have hw_eq : ∀ i, (lam.natW i : ℤ) + lam.detShift = lam.w i := by
    intro i
    have hle : lam.detShift ≤ lam.w i := by
      unfold DomWeight.detShift
      have hn : 0 < n := Fin.pos i
      rw [dif_pos hn]
      exact lam.anti (Fin.mk_le_mk.mpr (by omega) : i ≤ ⟨n - 1, by omega⟩)
    simp only [DomWeight.natW]
    omega
  rw [GlobalTheory.Branching.sqRep_coe, Submodule.coe_smul]
  show detPow ℂ n B lam.detShift • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) M.transpose (extremal ℂ n lam) = _
  unfold extremal
  rw [Formalism.BasicNotions.Examples₂.NZ.rowAct_hw ℂ le_rfl lam.natW M.transpose hl, hwScal_transpose lam.natW ha M, smul_smul]
  congr 1
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← hM, hdet, ← Finset.prod_zpow,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_add₀ (hne i), add_comm, hw_eq]

end GlobalTheory.HwUpper
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachModulePoleQuotient



theorem wachModule_consequences_poleQuotient : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), gammaSemisimpleQuotientGlobal D HW F := by
  intro D HW F Cm
  unfold gammaSemisimpleQuotientGlobal gammaSemisimpleLocal GammaSemisimpleQuotient
  intro l _ K s LL h T hT y hy
  classical
  have hfr := GlobalTheory.T.wachModule_inverseQuotient_free_finite_crystalline D HW F l K s LL h T hT y
  have hJ := GlobalTheory.T.crystallineLattice_hodgeTateJumps_finite D HW l K s LL h T hT
  let Fs : Finset (↥(OL LL))ˣ := (hJ.toFinset ×ˢ Finset.Icc 1 y).image
    (fun p : ℤ × ℕ => uU ((HW l).W K s LL h) ^ (-(p.1 + (p.2 : ℤ))))
  have hmem : ∀ c, c ∈ Fs ↔ ∃ a ∈ Jumps (PD := (D.loc l).PD K) T, ∃ j : ℕ, 1 ≤ j ∧ j ≤ y ∧
      c = uU ((HW l).W K s LL h) ^ (-(a + j)) := by
    intro c
    simp only [Fs, Finset.mem_image, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_Icc,
      Prod.exists]
    constructor
    · rintro ⟨a, j, ⟨ha, h1, h2⟩, rfl⟩
      exact ⟨a, ha, j, h1, h2, rfl⟩
    · rintro ⟨a, ha, j, h1, h2, rfl⟩
      exact ⟨a, j, ⟨ha, h1, h2⟩, rfl⟩
  refine ⟨hfr.1, hfr.2, Fs, ?_, ?_, ?_⟩
  · ext c
    exact hmem c
  · intro x hx
    exact GlobalTheory.T.prod_gamma_sub_jump_units_annihilates_quotient D HW F Cm l K s LL h T hT y hy Fs
      (fun a ha j h1 h2 => (hmem _).2 ⟨a, ha, j, h1, h2, rfl⟩) x hx
  · intro c hc
    obtain ⟨a, ha, j, h1, h2, rfl⟩ := (hmem c).1 hc
    obtain ⟨x, hx, hxN, hγ⟩ := GlobalTheory.T.gamma_eigenvalue_on_wachLattice_qPower_quotient D HW F Cm l K s LL h T hT y hy a ha j h1 h2
    exact ⟨x, hx, hxN, hγ⟩

end GlobalTheory.NL.WachModulePoleQuotient
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.inertia_fixing_kummer_root_moves_less : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), ∃ M : ℕ, 0 < M ∧ ¬ l ∣ M ∧ ∀ ρ : Om l, ρ ^ M = -(l : Om l) → ∀ g : GQ l, (∀ y : Om l, ‖y‖ ≤ 1 → ‖g y - y‖ < 1) → g ρ = ρ → ∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖ := by
  first | exact @GlobalTheory.NearRoot.near_root | exact GlobalTheory.NearRoot.near_root | (intros; apply GlobalTheory.NearRoot.near_root <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_galois_fixing_maxUnramified_map_conj : ∀ (l : ℕ) [Fact l.Prime] (x y : Om l), Polynomial.aeval y (minpoly ↥(MaximalUnramifiedExtension l) x) = 0 → ∃ g : GQ l, (∀ z ∈ MaximalUnramifiedExtension l, g z = z) ∧ g x = y := by
  first | exact @GlobalTheory.LiftKur.exists_gal_fix_Kur_map | exact GlobalTheory.LiftKur.exists_gal_fix_Kur_map | (intros; apply GlobalTheory.LiftKur.exists_gal_fix_Kur_map <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_prime_pow_fixing_normal_of_near : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), Normal ℚ_[l] ↥F.1 → ∀ g : GQ l, (∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) → ∃ s : ℕ, ∀ x ∈ F.1, (g ^ l ^ s) x = x := by
  first | exact @GlobalTheory.PowFixNear.main | exact GlobalTheory.PowFixNear.main | (intros; apply GlobalTheory.PowFixNear.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.finrank_mul_natDegree_minpoly_le_of_pow_eq_neg : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (N : ℕ) (x : Om l), 0 < N → x ^ N = -(l : Om l) → F ≤ IntermediateField.adjoin ℚ_[l] {x} → Module.finrank ℚ_[l] F * (minpoly F x).natDegree ≤ N := by
  first | exact @GlobalTheory.finrank_mul_minpoly_natDegree_le_of_pow_eq_neg | exact GlobalTheory.finrank_mul_minpoly_natDegree_le_of_pow_eq_neg | (intros; apply GlobalTheory.finrank_mul_minpoly_natDegree_le_of_pow_eq_neg <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_mul_fixingSubgroup_of_inf_eq_bot : ∀ (l : ℕ) [Fact l.Prime] (K M : IntermediateField ℚ_[l] (Om l)), FiniteDimensional ℚ_[l] K → IsGalois ℚ_[l] K → K ⊓ M = ⊥ → ∀ g : GQ l, ∃ h ∈ K.fixingSubgroup, ∃ k ∈ M.fixingSubgroup, g = h * k := by
  first | exact @GlobalTheory.InertiaEigenvalues.galois_decomp_of_disjoint | exact GlobalTheory.InertiaEigenvalues.galois_decomp_of_disjoint | (intros; apply GlobalTheory.InertiaEigenvalues.galois_decomp_of_disjoint <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.mem_pow_smul_lattice_of_coord_dvd : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (x : ↥T.L.T) (k : ℕ), (∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → (l : ℤ_[l]) ^ k ∣ φ x) → ∃ y ∈ T.L.T, (x : T.V) = ((l : O) ^ k) • y := by
  first | exact @GlobalTheory.InertiaEigenvalues.mem_pow_smul_of_coord_dvd | exact GlobalTheory.InertiaEigenvalues.mem_pow_smul_of_coord_dvd | (intros; apply GlobalTheory.InertiaEigenvalues.mem_pow_smul_of_coord_dvd <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.norm_minpoly_coeff_zero_pow_of_pow_eq_neg_prime : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (N : ℕ) (x : Om l), 0 < N → x ^ N = -(l : Om l) → ‖(((minpoly F x).coeff 0 : F) : Om l)‖ ^ N = ((l : ℝ)⁻¹) ^ (minpoly F x).natDegree := by
  first | exact @GlobalTheory.norm_minpoly_coeff_zero_pow_of_pow_eq_neg | exact GlobalTheory.norm_minpoly_coeff_zero_pow_of_pow_eq_neg | (intros; apply GlobalTheory.norm_minpoly_coeff_zero_pow_of_pow_eq_neg <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.aeval_rootOfUnity_mul_kummer_root_minpoly : ∀ (l : ℕ) [Fact l.Prime] (M : ℕ), 0 < M → ∀ (ρ ξ : Om l), ρ ^ M = -(l : Om l) → ξ ^ M = 1 → Polynomial.aeval (ξ * ρ) (minpoly ↥(MaximalUnramifiedExtension l) ρ) = 0 := by
  first | exact @GlobalTheory.MinpolyKummerUr.aeval_mul_root | exact GlobalTheory.MinpolyKummerUr.aeval_mul_root | (intros; apply GlobalTheory.MinpolyKummerUr.aeval_mul_root <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.natDegree_minpoly_root_neg_prime_unramified : ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) (π : Om l), 0 < N → π ^ N = -(l : Om l) → ∀ (E : Type) [Field E] [Algebra E (Om l)], (∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) → (minpoly E π).natDegree = N := by
  first | exact @GlobalTheory.InertiaDeg.natDegree_minpoly_root_neg_l | exact GlobalTheory.InertiaDeg.natDegree_minpoly_root_neg_l | (intros; apply GlobalTheory.InertiaDeg.natDegree_minpoly_root_neg_l <;> assumption)
end
