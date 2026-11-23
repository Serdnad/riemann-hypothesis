module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle164
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedFormOrthogonalFinrankDetUnitary
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163

@[expose] public section

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S IsDedekindDomain
open scoped ENNReal Classical

namespace GlobalTheory.Mass.DetAgree

section
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

theorem genIdxH_eq_idxN {A B : Submodule (𝓞 K) V} (hBA : B ≤ A) (h0 : idxN A B ≠ 0) :
    Lat.genIdxH A B = (idxN A B : ℝ) := by
  obtain ⟨k, hk, hc⟩ := Formalism.LFunctionChainParameters.LLcv.card_pLen _ A B hBA rfl h0
  let e : HeightOneSpectrum (𝓞 K) ≃ {p : Ideal (𝓞 K) // p.IsMaximal} :=
    { toFun := fun P => ⟨P.asIdeal, P.isMaximal⟩
      invFun := fun p => ⟨p.1, p.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hl : ∀ P : HeightOneSpectrum (𝓞 K), (haveI := P.isPrime; lidx P.asIdeal A B) = (k (e P) : ℤ) := by
    intro P
    have a := hk (e P)
    unfold Formalism.LFunctionChainParameters.LLcv.pLen at a
    unfold lidx
    rw [inf_eq_right.mpr hBA, indexBasic_locLen_self]
    unfold locLen
    erw [a]
    simp
  unfold Lat.genIdxH
  simp only [hl, zpow_natCast]
  have := finprod_comp_equiv (f := fun w : {p : Ideal (𝓞 K) // p.IsMaximal} =>
    ((Ideal.absNorm w.1 : ℕ) : ℝ) ^ k w) e
  refine this.trans ?_
  rw [idxN, hc, finprod_eq_prod_of_mulSupport_subset (s := k.support), Finsupp.prod, Nat.cast_prod]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [Nat.cast_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · intro w hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h
    apply hw
    simp [h]

variable [Module K V] [IsScalarTower (𝓞 K) K V]

theorem span_inf_eq (L : Submodule (𝓞 K) V) (hL : Submodule.IsFullLattice K L) (U : Submodule K V) :
    Submodule.span K ((L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = U := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => hx.2) fun u hu => ?_
  obtain ⟨r, hr, hru⟩ := Formalism.LFunctionChainParameters.LLcv.span_le_locS (K := K) L (x := u) (by rw [hL.span_eq_top]; trivial)
  have h1 : algebraMap (𝓞 K) K r ≠ 0 := by simpa using nonZeroDivisors.ne_zero hr
  have h2 : r • u ∈ Submodule.span K ((L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) :=
    Submodule.subset_span ⟨hru, (U.restrictScalars (𝓞 K)).smul_mem r hu⟩
  rw [← algebraMap_smul K r] at h2
  exact (Submodule.smul_mem_iff _ h1).1 h2

theorem isLattice_latIn (L : Submodule (𝓞 K) V) (hL : Submodule.IsFullLattice K L) (U : Submodule K V) :
    Submodule.IsFullLattice K (latIn U L) := by
  haveI : Submodule.IsLattice K (latIn U L) := by
    apply Submodule.IsLattice.of_fg K
    refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    exact hL.fg.of_le (Submodule.map_comap_le _ _)
  refine ⟨?_⟩
  apply Submodule.map_injective_of_injective U.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  refine (congrArg (Submodule.span K) ?_).trans (span_inf_eq L hL U)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨hx, hxU⟩
    exact ⟨⟨x, hxU⟩, hx, rfl⟩

variable [StarRing K]

theorem nondeg_of_pd {h : V →ₗ⋆[K] V →ₗ[K] K} (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have key : ∀ x, h x x = 0 → x = 0 := fun x hx => by
    by_contra h0
    have := hp τ x h0
    rw [hx] at this
    simp at this
  exact ⟨fun x hx => key x (hx x), fun x hx => key x (hx x)⟩

theorem idxN_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hL : Submodule.IsFullLattice K L)
    (U : Submodule K V) :
    idxN (Lat.dualInH h (L ⊓ U.restrictScalars (𝓞 K))) (L ⊓ U.restrictScalars (𝓞 K)) =
      discN (hRes h U) (latIn U L) := by
  have e1 : (L ⊓ U.restrictScalars (𝓞 K)).toAddSubgroup =
      (latIn U L).toAddSubgroup.map U.subtype.toAddMonoidHom := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
  have e2 : (Lat.dualInH h (L ⊓ U.restrictScalars (𝓞 K))).toAddSubgroup =
      (dual (hRes h U) (latIn U L)).toAddSubgroup.map U.subtype.toAddMonoidHom := by
    unfold Lat.dualInH
    rw [span_inf_eq L hL U]
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, h2⟩, (dualBasic_mem_dual _ _ _).2 fun y hy => ?_, rfl⟩
      exact (dualBasic_mem_dual _ _ _).1 h1 y ⟨hy, y.2⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(dualBasic_mem_dual _ _ _).2 fun z hz => ?_, y.2⟩
      exact (dualBasic_mem_dual _ _ _).1 hy ⟨z, hz.2⟩ hz.1
  rw [discN, idxN, idxN, e1, e2, AddSubgroup.relIndex_map_map_of_injective _ _ U.injective_subtype]

theorem discGen_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hle : L ≤ dual h L) (e : ℕ) :
    Cnt.DiscGen h L e ↔ ∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V) := by
  set D := dual h L with hD
  set q : D →ₗ[𝓞 K] Cnt.discMod h L := (L.comap D.subtype).mkQ with hq
  have key : ∀ s : Finset D, Submodule.span (𝓞 K) ((s.image q : Finset _) : Set (Cnt.discMod h L)) = ⊤ ↔
      D = L ⊔ Submodule.span (𝓞 K) ((s.image D.subtype : Finset V) : Set V) := by
    intro s
    rw [Finset.coe_image, Finset.coe_image, ← Submodule.map_span, ← Submodule.map_span, hq,
      Submodule.map_mkQ_eq_top, ← (Submodule.map_injective_of_injective D.injective_subtype).eq_iff,
      Submodule.map_sup, Submodule.map_comap_subtype, inf_eq_right.2 hle, Submodule.map_top,
      Submodule.range_subtype, eq_comm]
  constructor
  · rintro ⟨s, hs, hsp⟩
    have hsurj : Function.Surjective q := Submodule.mkQ_surjective _
    refine ⟨(s.image (Function.surjInv hsurj)).image D.subtype,
      Finset.card_image_le.trans (Finset.card_image_le.trans hs), (key _).1 ?_⟩
    rw [Finset.image_image, (Function.rightInverse_surjInv hsurj).comp_eq_id, Finset.image_id, hsp]
  · rintro ⟨t, ht, hsp⟩
    have htD : ∀ x ∈ t, x ∈ D := fun x hx => by
      rw [hsp]; exact Submodule.mem_sup_right (Submodule.subset_span hx)
    have ee : (t.subtype (· ∈ D)).image D.subtype = t := by
      ext x
      simp only [Finset.mem_image, Finset.mem_subtype]
      exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun hx => ⟨⟨x, htD x hx⟩, hx, rfl⟩⟩
    refine ⟨(t.subtype (· ∈ D)).image q, Finset.card_image_le.trans ?_, (key _).2 (by rw [ee]; exact hsp)⟩
    rw [Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans ht

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → Lat.latDetH h L ^ 2 = (discN h L : ℝ) ∧ 0 < Lat.latDetH h L ∧ (∀ j de : ℕ, Cnt.cntPrim h L j de = (primSp h L j (de ^ 2)).encard) ∧ (∀ e : ℕ, Cnt.DiscGen h L e ↔ (∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V))) ∧ ∀ (U : Submodule K V), Lat.latDetH h (L ⊓ U.restrictScalars (𝓞 K)) ^ 2 = (discN (hRes h U) (latIn U L) : ℝ) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp L hL
  have hFull : Submodule.IsFullLattice K L := hL.1
  have hle : L ≤ dual h L := fun x hx => (dualBasic_mem_dual _ _ _).2 fun y hy => hL.2 y hy x hx
  have hn := nondeg_of_pd hp
  have h0 := (DiscOrder.main K V h hK hs hn L hL).1
  have hd : Lat.dualInH h L = dual h L := by
    unfold Lat.dualInH
    rw [hFull.span_eq_top]
    simp
  have h1 : Lat.latDetH h L = Real.sqrt (discN h L : ℝ) := by
    rw [Lat.latDetH, hd, genIdxH_eq_idxN hle h0, discN]
  have hU : ∀ U : Submodule K V, Lat.latDetH h (L ⊓ U.restrictScalars (𝓞 K)) =
      Real.sqrt (discN (hRes h U) (latIn U L) : ℝ) := by
    intro U
    have hsU : (hRes h U).IsSymm := ⟨fun x y => hs.eq x y⟩
    have hpU : PD (hRes h U) := fun τ x hx => hp τ x fun e => hx (Subtype.ext e)
    have hI : IsIntLat (hRes h U) (latIn U L) :=
      ⟨isLattice_latIn L hFull U, fun x hx y hy => hL.2 x hx y hy⟩
    have n0 := (DiscOrder.main K U _ hK hsU (nondeg_of_pd hpU) _ hI).1
    rw [← idxN_dualInH h L hFull U] at n0 ⊢
    rw [Lat.latDetH, genIdxH_eq_idxN _ n0]
    intro x hx
    exact ⟨(dualBasic_mem_dual _ _ _).2 fun y hy => hL.2 y hy.1 x hx.1, Submodule.subset_span hx⟩
  refine ⟨by rw [h1, Real.sq_sqrt (Nat.cast_nonneg _)], ?_, fun j de => ?_, discGen_iff h L hle,
    fun U => by rw [hU, Real.sq_sqrt (Nat.cast_nonneg _)]⟩
  · rw [h1]
    exact Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero h0)
  · have hinj : Function.Injective fun U : Submodule K V => L ⊓ U.restrictScalars (𝓞 K) :=
      Function.LeftInverse.injective (g := fun M : Submodule (𝓞 K) V => Submodule.span K (M : Set V))
        (span_inf_eq L hFull)
    have hsq : ∀ n : ℕ, Real.sqrt (n : ℝ) = de ↔ n = de ^ 2 := fun n => by
      rw [Real.sqrt_eq_iff_eq_sq (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact_mod_cast Iff.rfl
    rw [Cnt.cntPrim, ← hinj.encard_image]
    congr 1
    ext M
    constructor
    · rintro ⟨⟨-, a⟩, b, c⟩
      refine ⟨Submodule.span K (M : Set V), ⟨b, ?_⟩, a.symm⟩
      rw [← hsq, ← hU, ← a, c]
    · rintro ⟨U, ⟨a, b⟩, rfl⟩
      refine ⟨⟨inf_le_left, ?_⟩, ?_, ?_⟩
      · simp only
        rw [span_inf_eq L hFull]
      · simp only
        rw [span_inf_eq L hFull, a]
      · simp only
        rw [hU, hsq, b]

end GlobalTheory.Mass.DetAgree
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.OrbitTerm.SplitStab

variable {E : Type} [Field E] {k : ℕ}

theorem det_of_col (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E)
    (h : ∀ a, M a 0 = if a = 0 then 1 else 0) : M.det = (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h, Fin.succ_ne_zero]

theorem mulVec_zero_of_col (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E)
    (h : ∀ a, M a 0 = if a = 0 then 1 else 0) (y : Fin (k + 1) → E) :
    (M *ᵥ y) 0 = y 0 + (fun b => M 0 (Fin.succ b)) ⬝ᵥ Fin.tail y := by
  have h0 : M 0 0 = 1 := by simpa using h 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h0, Fin.tail]

theorem tail_mulVec_of_col (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E)
    (h : ∀ a, M a 0 = if a = 0 then 1 else 0) (y : Fin (k + 1) → E) :
    Fin.tail (M *ᵥ y) = M.submatrix Fin.succ Fin.succ *ᵥ Fin.tail y := by
  funext b
  have hb : M b.succ 0 = 0 := by simpa [Fin.succ_ne_zero] using h b.succ
  simp [Fin.tail, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hb, Matrix.submatrix]

theorem preserves_iff [NumberField E] (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E))
    (Λ' : Submodule (𝓞 E) (Fin k → E)) (hΛ : ∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ')
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E) (h : ∀ a, M a 0 = if a = 0 then 1 else 0) :
    (∀ y, M *ᵥ y ∈ Λ ↔ y ∈ Λ) ↔ (∀ y, M.submatrix Fin.succ Fin.succ *ᵥ y ∈ Λ' ↔ y ∈ Λ') ∧
      ∀ y ∈ Λ', (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ y) ∈ Λ₀ := by
  have key : ∀ y : Fin (k + 1) → E, M *ᵥ y ∈ Λ ↔
      ((fun _ => y 0) + (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ Fin.tail y) : Fin 1 → E) ∈ Λ₀ ∧
        M.submatrix Fin.succ Fin.succ *ᵥ Fin.tail y ∈ Λ' := by
    intro y
    rw [hΛ, mulVec_zero_of_col M h y, tail_mulVec_of_col M h y]
    exact Iff.rfl
  have hcons : ∀ (c : E) (z : Fin k → E),
      (Fin.cons c z : Fin (k + 1) → E) 0 = c ∧ Fin.tail (Fin.cons c z : Fin (k + 1) → E) = z :=
    fun c z => ⟨Fin.cons_zero _ _, Fin.tail_cons _ _⟩
  constructor
  · intro hM
    refine ⟨fun z => ⟨fun hz => ?_, fun hz => ?_⟩, fun z hz => ?_⟩
    ·
      set c : E := -((fun b => M 0 (Fin.succ b)) ⬝ᵥ z)
      have h1 : M *ᵥ (Fin.cons c z : Fin (k + 1) → E) ∈ Λ := by
        rw [key, (hcons c z).1, (hcons c z).2]
        refine ⟨?_, hz⟩
        have hz0 : ((fun _ => c) + (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ z) : Fin 1 → E) = 0 := by
          funext i; simp [c]
        rw [hz0]; exact Λ₀.zero_mem
      have h2 := (hΛ _).1 ((hM _).1 h1)
      rw [(hcons c z).2] at h2
      exact h2.2
    · have h1 : (Fin.cons 0 z : Fin (k + 1) → E) ∈ Λ := by
        rw [hΛ, (hcons 0 z).1, (hcons 0 z).2]; exact ⟨Λ₀.zero_mem, hz⟩
      have h2 := (key _).1 ((hM _).2 h1)
      rw [(hcons 0 z).2] at h2
      exact h2.2
    · have h1 : (Fin.cons 0 z : Fin (k + 1) → E) ∈ Λ := by
        rw [hΛ, (hcons 0 z).1, (hcons 0 z).2]; exact ⟨Λ₀.zero_mem, hz⟩
      have h2 := ((key _).1 ((hM _).2 h1)).1
      rw [(hcons 0 z).1, (hcons 0 z).2] at h2
      have he : ((fun _ => (0 : E)) + (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ z) : Fin 1 → E) =
          fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ z := by
        funext i; simp
      rwa [he] at h2
  · rintro ⟨hA, hr⟩ y
    rw [key, hΛ, hA]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(add_mem_cancel_right (hr _ h2)).1 h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Λ₀.add_mem h1 (hr _ h2), h2⟩

end GlobalTheory.OrbitTerm.SplitStab

namespace GlobalTheory.OrbitTerm


open SplitStab in
theorem mem_autGL_split_iff : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → ∀ x : MatInf E (k + 1), (∀ w a, x w a 0 = if a = 0 then 1 else 0) → (x ∈ autGL E (k + 1) Λ ↔ (fun w a b => x w a.succ b.succ) ∈ autGL E k Λ' ∧ ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ ∀ w b, x w 0 b.succ = w.embedding (τ b)) := by
  intro E _ _ k Λ Λ₀ Λ' hΛ x hx
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  simp only [autGL, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨γ, hγ, hxγ⟩
    have hcol : ∀ a, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) a 0 = if a = 0 then 1 else 0 := by
      intro a
      apply w₀.embedding.injective
      rw [← hxγ w₀ a 0, hx w₀ a]
      split_ifs <;> simp
    have hdet : (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
    rw [det_of_col _ hcol] at hdet
    obtain ⟨hA, hr⟩ := (preserves_iff Λ Λ₀ Λ' hΛ _ hcol).1 hγ
    exact ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, hA, fun w a b => hxγ w a.succ b.succ⟩,
      fun b => (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) 0 b.succ, hr, fun w b => hxγ w 0 b.succ⟩
  · rintro ⟨⟨γ', hγ', hxγ'⟩, τ, hτ, hxτ⟩

    obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin (k + 1)) (Fin (k + 1)) E,
        M = Matrix.of (Fin.cons (Fin.cons 1 τ : Fin (k + 1) → E)
          (fun a => (Fin.cons 0 ((γ' : Matrix (Fin k) (Fin k) E) a) : Fin (k + 1) → E)) :
            Fin (k + 1) → Fin (k + 1) → E) := ⟨_, rfl⟩
    have hcol : ∀ a, M a 0 = if a = 0 then 1 else 0 := by
      intro a
      rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a, rfl⟩ <;> simp [hM, Fin.succ_ne_zero]
    have hsub : M.submatrix Fin.succ Fin.succ = (γ' : Matrix (Fin k) (Fin k) E) := by
      ext a b; simp [hM]
    have hrow : (fun b => M 0 (Fin.succ b)) = τ := by
      funext b; simp [hM]
    have hdet : M.det ≠ 0 := by
      rw [det_of_col M hcol, hsub]; exact (Matrix.isUnits_det_units γ').ne_zero
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, ?_⟩
    · show ∀ y, M *ᵥ y ∈ Λ ↔ y ∈ Λ
      refine (preserves_iff Λ Λ₀ Λ' hΛ M hcol).2 ⟨?_, ?_⟩
      · rw [hsub]; exact hγ'
      · rw [hrow]; exact hτ
    · intro w a b
      show x w a b = w.embedding (M a b)
      rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a, rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b, rfl⟩
      · rw [hx]; simp [hM]
      · rw [hxτ]; simp [hM]
      · rw [hx]; simp [hM, Fin.succ_ne_zero]
      · refine (hxγ' w a b).trans ?_
        simp [hM]

end GlobalTheory.OrbitTerm
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.StrictDomain

theorem null_of_translate_disjoint {X : Type} [Mul X] [MeasurableSpace X] (S : Set X) (μ : Measure X)
    (U D : Set X) (hc : S.Countable) (hm : ∀ γ ∈ S, Measurable fun x => γ * x)
    (hinv : ∀ γ ∈ S, μ.map (fun x => γ * x) = μ)
    (hmul : ∀ γ ∈ S, ∀ δ ∈ S, ∃ ε ∈ S, ∀ x, ε * x = γ * (δ * x))
    (hi : ∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x)
    (hU : MeasurableSet U) (hUS : ∀ γ ∈ S, ∀ x ∈ U, γ * x ∈ U) (hDU : D ⊆ U)
    (hcov : ∀ A, MeasurableSet A → A ⊆ U → (∀ γ ∈ S, ∀ x ∈ A, γ * x ∈ A) →
      covol S μ A = μ (A ∩ D))
    (γ : X) (hγ : γ ∈ S) (B : Set X) (hB : MeasurableSet B) (hfin : μ B ≠ ⊤)
    (hBD : B ⊆ D) (hBγ : ∀ x ∈ B, γ * x ∈ D) (hdis : ∀ x ∈ B, γ * x ∉ B) : μ B = 0 := by
  obtain ⟨δ, hδ, hδγ, hγδ⟩ := hi γ hγ
  set A : Set X := U ∩ ⋃ ε ∈ S, (fun x => ε * x) ⁻¹' B with hA
  have hmemA : ∀ x, x ∈ A ↔ x ∈ U ∧ ∃ ε ∈ S, ε * x ∈ B := by
    intro x
    simp [hA]
  have hAm : MeasurableSet A :=
    hU.inter (MeasurableSet.biUnion hc fun ε hε => hm ε hε hB)
  have hAinv : ∀ η ∈ S, ∀ x ∈ A, η * x ∈ A := by
    intro η hη x hx
    obtain ⟨hxU, ε, hε, hεx⟩ := (hmemA x).1 hx
    obtain ⟨η', hη', h1, -⟩ := hi η hη
    obtain ⟨κ, hκ, hκe⟩ := hmul ε hε η' hη'
    exact (hmemA _).2 ⟨hUS η hη x hxU, κ, hκ, by rw [hκe, h1]; exact hεx⟩
  have hle : μ (A ∩ D) ≤ μ B := by
    rw [← hcov A hAm Set.inter_subset_left hAinv]
    unfold covol
    exact iInf_le_of_le B (iInf_le_of_le hB (iInf_le_of_le (fun x hx => ((hmemA x).1 hx).2) le_rfl))
  set B' : Set X := (fun x => δ * x) ⁻¹' B with hB'
  have hB'm : MeasurableSet B' := hm δ hδ hB
  have hB'μ : μ B' = μ B := by
    rw [hB', ← Measure.map_apply (hm δ hδ) hB, hinv δ hδ]
  have hdj : Disjoint B B' := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have := hdis _ hx'
    rw [hγδ] at this
    exact this hx
  have hsub : B ∪ B' ⊆ A ∩ D := by
    rintro x (hx | hx)
    · obtain ⟨κ, hκ, hκe⟩ := hmul δ hδ γ hγ
      exact ⟨(hmemA x).2 ⟨hDU (hBD hx), κ, hκ, by rw [hκe, hδγ]; exact hx⟩, hBD hx⟩
    · have hxD : x ∈ D := by
        have := hBγ _ hx
        rwa [hγδ] at this
      exact ⟨(hmemA x).2 ⟨hDU hxD, δ, hδ, hx⟩, hxD⟩
  have h2 : μ B + μ B ≤ μ B + 0 := by
    calc μ B + μ B = μ (B ∪ B') := by rw [measure_union hdj hB'm, hB'μ]
      _ ≤ μ (A ∩ D) := measure_mono hsub
      _ ≤ μ B + 0 := by rw [add_zero]; exact hle
  exact le_antisymm ((ENNReal.add_le_add_iff_left hfin).1 h2) zero_le

theorem measure_inter_translate_eq_zero : ∀ (X : Type) [Mul X] [MeasurableSpace X] [MeasurableSpace.CountablySeparated X] (S : Set X) (μ : Measure X) [SigmaFinite μ] (U D : Set X), S.Countable → (∀ γ ∈ S, Measurable fun x => γ * x) → (∀ γ ∈ S, μ.map (fun x => γ * x) = μ) → (∀ γ ∈ S, ∀ δ ∈ S, ∃ ε ∈ S, ∀ x, ε * x = γ * (δ * x)) → (∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x) → MeasurableSet U → (∀ γ ∈ S, ∀ x ∈ U, γ * x ∈ U) → MeasurableSet D → D ⊆ U → (∀ A, MeasurableSet A → A ⊆ U → (∀ γ ∈ S, ∀ x ∈ A, γ * x ∈ A) → covol S μ A = μ (A ∩ D)) → ∀ γ ∈ S, (∀ x ∈ U, γ * x ≠ x) → μ {x | x ∈ D ∧ γ * x ∈ D} = 0 := by
  intro X _ _ _ S μ _ U D hc hm hinv hmul hi hU hUS hD hDU hcov γ hγ hfree
  obtain ⟨V, hVm, hV⟩ := exists_seq_separating X MeasurableSet.univ (Set.univ : Set X)
  have key : ∀ (W : Set X), MeasurableSet W → ∀ m : ℕ,
      μ (D ∩ (fun x => γ * x) ⁻¹' D ∩ W ∩ (fun x => γ * x) ⁻¹' Wᶜ ∩ spanningSets μ m) = 0 := by
    intro W hW m
    refine null_of_translate_disjoint S μ U D hc hm hinv hmul hi hU hUS hDU hcov γ hγ _
      ((((hD.inter (hm γ hγ hD)).inter hW).inter (hm γ hγ hW.compl)).inter
        (measurableSet_spanningSets μ m))
      (ne_top_of_le_ne_top (measure_spanningSets_lt_top μ m).ne
        (measure_mono Set.inter_subset_right)) ?_ ?_ ?_
    · intro x hx
      exact hx.1.1.1.1
    · intro x hx
      exact hx.1.1.1.2
    · intro x hx hx'
      exact hx.1.2 hx'.1.1.2
  have hsub : {x | x ∈ D ∧ γ * x ∈ D} ⊆ ⋃ n : ℕ, ⋃ m : ℕ,
      ((D ∩ (fun x => γ * x) ⁻¹' D ∩ V n ∩ (fun x => γ * x) ⁻¹' (V n)ᶜ ∩ spanningSets μ m) ∪
       (D ∩ (fun x => γ * x) ⁻¹' D ∩ (V n)ᶜ ∩ (fun x => γ * x) ⁻¹' (V n)ᶜᶜ ∩ spanningSets μ m)) := by
    rintro x ⟨hx, hγx⟩
    have hne := hfree x (hDU hx)
    obtain ⟨n, hn⟩ : ∃ n, ¬ (γ * x ∈ V n ↔ x ∈ V n) := by
      by_contra h
      push_neg at h
      exact hne (hV _ (Set.mem_univ _) _ (Set.mem_univ _) h)
    have hm' : x ∈ ⋃ m, spanningSets μ m := by rw [iUnion_spanningSets]; exact Set.mem_univ _
    obtain ⟨m, hm'⟩ := Set.mem_iUnion.1 hm'
    refine Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨m, ?_⟩⟩
    by_cases hxV : x ∈ V n
    · exact Or.inl ⟨⟨⟨⟨hx, hγx⟩, hxV⟩, fun h => hn ⟨fun _ => hxV, fun _ => h⟩⟩, hm'⟩
    · exact Or.inr ⟨⟨⟨⟨hx, hγx⟩, hxV⟩, fun h => hn ⟨fun h' => (h h').elim, fun h' => (hxV h').elim⟩⟩, hm'⟩
  refine measure_mono_null hsub (measure_iUnion_null fun n => measure_iUnion_null fun m => ?_)
  exact measure_union_null (key _ (hVm n) m) (key _ (hVm n).compl m)

end GlobalTheory.StrictDomain
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.OrbitTerm

theorem map_haarGL_mul_left_eq : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (γ : MatInf E j), 0 < GlobalTheory.FlagMeas.detNorm E j γ → (haarGL E j).map (fun g => γ * g) = haarGL E j :=
  fun E _ _ j γ h => (GlobalTheory.HaarLeftInv.measurePreserving_mul_left E j γ h).2.map_eq

end GlobalTheory.OrbitTerm
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (V V' : Submodule ℂ (Fin n → ℂ)), (∀ y, y ∈ V' ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) → Module.finrank ℂ V' + Module.finrank ℂ V = n ∧ (∀ x, (∀ y ∈ V', star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0) → x ∈ V) ∧ ∀ m : Formalism.REAL.UJ ε, ‖(uMat m).det‖ = 1 ∧ ((∀ y ∈ V, uMat m *ᵥ y ∈ V) → (∀ y ∈ V', uMat m *ᵥ y ∈ V') ∧ detOn (uMat m) V' = detOn (uMat m) V ∧ 0 < detOn (uMat m) V) := by
  first | exact @GlobalTheory.PerpModulus.perp_modulus | exact GlobalTheory.PerpModulus.perp_modulus | (intros; apply GlobalTheory.PerpModulus.perp_modulus <;> assumption)
end
