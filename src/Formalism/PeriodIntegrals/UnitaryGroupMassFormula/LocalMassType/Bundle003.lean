module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Bundle002
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.LocMassTypW.WSatP

open Matrix

theorem leftInv_field {K : Type*} [Field K] {n m : ℕ} (A : Matrix (Fin n) (Fin m) K)
    (h : ∀ t, A *ᵥ t = 0 → t = 0) : ∃ L : Matrix (Fin m) (Fin n) K, L * A = 1 := by
  have hk : LinearMap.ker (Matrix.toLin' A) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro t ht
    exact h t (by simpa [Matrix.toLin'_apply] using ht)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' A, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem leftInv_lift {O : Type*} [CommRing O] [IsLocalRing O] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) O)
    (h : ∃ L : Matrix (Fin m) (Fin n) (IsLocalRing.ResidueField O),
      L * A.map (IsLocalRing.residue O) = 1) :
    ∃ L : Matrix (Fin m) (Fin n) O, L * A = 1 := by
  obtain ⟨Lb, hLb⟩ := h
  let L0 : Matrix (Fin m) (Fin n) O :=
    Matrix.of fun i j => Classical.choose (IsLocalRing.residue_surjective (Lb i j))
  have hL0 : L0.map (IsLocalRing.residue O) = Lb :=
    Matrix.ext fun i j => Classical.choose_spec (IsLocalRing.residue_surjective (Lb i j))
  have hdet : IsUnit (L0 * A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply,
      Matrix.map_mul, hL0, hLb, Matrix.det_one]
    exact one_ne_zero
  refine ⟨(L0 * A)⁻¹ * L0, ?_⟩
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet]

end PI.LocMassTypW.WSatP

namespace PI.LocMassTypW

open Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem saturated_split_lattice : SatSplit := by
  intro F _ _ v n m A hsat
  apply WSatP.leftInv_lift
  apply WSatP.leftInv_field
  intro tb htb
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, tb j ≠ 0 := by
    by_contra hall
    exact hne (funext fun k => not_not.mp fun h' => hall ⟨k, h'⟩)
  let t : Fin m → v.adicCompletionIntegers F := fun j =>
    Classical.choose (IsLocalRing.residue_surjective (tb j))
  have ht : ∀ j, IsLocalRing.residue _ (t j) = tb j := fun j =>
    Classical.choose_spec (IsLocalRing.residue_surjective (tb j))
  have htj : IsUnit (t j) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [ht]; exact hj)
  have hAt : ∀ i, (A *ᵥ t) i ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    intro i
    rw [← IsLocalRing.residue_eq_zero_iff, RingHom.map_mulVec]
    have : (IsLocalRing.residue _ ∘ t) = tb := funext ht
    rw [this, htb]
    rfl
  obtain ⟨x, hx⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  let I : Ideal (v.adicCompletionIntegers F) := Ideal.span (insert x (Set.range (A *ᵥ t)))
  obtain ⟨c, hc⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmemI : ∀ y ∈ insert x (Set.range (A *ᵥ t)), ∃ q, q * c = y := by
    intro y hy
    have : y ∈ I := Ideal.subset_span hy
    rw [hc] at this
    exact Ideal.mem_span_singleton'.mp this
  have hcm : c ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    have : c ∈ I := by rw [hc]; exact Submodule.mem_span_singleton_self c
    refine (Ideal.span_le.mpr ?_) this
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact (IsLocalRing.mem_maximalIdeal _).mpr hx.not_isUnit
    · exact hAt i
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨q, hq⟩ := hmemI x (Set.mem_insert _ _)
    rw [mul_zero] at hq
    exact hx.ne_zero hq.symm
  have hcK : (c : v.adicCompletion F) ≠ 0 := by
    intro h0; exact hc0 (Subtype.ext h0)
  let f := (v.adicCompletionIntegers F).subtype
  let t' : Fin m → v.adicCompletion F := (c : v.adicCompletion F)⁻¹ • (f ∘ t)
  have hint : ∀ i, (A.map (fun a => (a : v.adicCompletion F)) *ᵥ t') i ∈
      v.adicCompletionIntegers F := by
    intro i
    obtain ⟨q, hq⟩ := hmemI ((A *ᵥ t) i) (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
    have e1 : (A.map (fun a => (a : v.adicCompletion F)) *ᵥ t') i =
        (c : v.adicCompletion F)⁻¹ * f ((A *ᵥ t) i) := by
      rw [Matrix.mulVec_smul, RingHom.map_mulVec]
      rfl
    rw [e1, ← hq, map_mul]
    have e2 : (c : v.adicCompletion F)⁻¹ * (f q * f c) = f q := by
      change (c : v.adicCompletion F)⁻¹ * (f q * (c : v.adicCompletion F)) = f q
      field_simp
    rw [e2]
    exact q.2
  have hj' := hsat t' hint j
  have e3 : t' j = (c : v.adicCompletion F)⁻¹ * (t j : v.adicCompletion F) := rfl
  rw [e3] at hj'
  set s : v.adicCompletionIntegers F := ⟨_, hj'⟩ with hs
  have hts : t j = c * s := by
    apply Subtype.ext
    change (t j : v.adicCompletion F) = (c : v.adicCompletion F) * ((c : v.adicCompletion F)⁻¹ * (t j : v.adicCompletion F))
    field_simp
  have : t j ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [hts]; exact Ideal.mul_mem_right _ _ hcm
  exact ((IsLocalRing.mem_maximalIdeal _).mp this) htj

end PI.LocMassTypW
end
end

section

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
  (Λ : Set (Fin n → E))

theorem smul_apply_lin (k : HA (Fv F v) σ J) {a : ℕ} (X : TupV (E := E) v n a) (i : Fin a) :
    (k • X) i = lin (Fv F v) σ J k (X i) := rfl

theorem kv_lin {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (y : Fin n → Fv F v ⊗[F] E) :
    lin (Fv F v) σ J k y ∈ latLoc (E := E) v Λ ↔ y ∈ latLoc (E := E) v Λ :=
  (hk y).symm

theorem locF_smul (k : HA (Fv F v) σ J) {r : ℕ} (X : TupV (E := E) v n (r + 1)) :
    locF (E := E) (n := n) (r := r) v (k • X) = k • locF v X := by
  funext a
  show sc (E := E) v (alp v r a) • lin (Fv F v) σ J k (X a) =
    lin (Fv F v) σ J k (sc (E := E) v (alp v r a) • X a)
  rw [map_smul]

def GM (g : ℕ) (z : Fin n → Fv F v ⊗[F] E) : Prop :=
  ∃ y ∈ latLoc (E := E) v Λ, z = sc (E := E) v (g : Fv F v) • y

variable {σ J v Λ}

theorem gm_add {g : ℕ} {z w : Fin n → Fv F v ⊗[F] E} (hz : GM v Λ g z) (hw : GM v Λ g w) :
    GM v Λ g (z + w) := by
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨y', hy', rfl⟩ := hw
  exact ⟨y + y', Submodule.add_mem _ hy hy', by rw [smul_add]⟩

theorem gm_neg {g : ℕ} {z : Fin n → Fv F v ⊗[F] E} (hz : GM v Λ g z) : GM v Λ g (-z) := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨-y, Submodule.neg_mem _ hy, by rw [smul_neg]⟩

theorem gm_lin {g : ℕ} {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    {z : Fin n → Fv F v ⊗[F] E} (hz : GM v Λ g z) : GM v Λ g (lin (Fv F v) σ J k z) := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨lin (Fv F v) σ J k y, (kv_lin σ J v Λ hk y).2 hy, by rw [map_smul]⟩

theorem kv_inv' {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) :
    k⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v := (Kloc (E := E) v Λ).inv_mem hk

theorem kv_mul' {a b : HA (Fv F v) σ J} (ha : a ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (hb : b ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) : a * b ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  (Kloc (E := E) v Λ).mul_mem ha hb

theorem prim_smul {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) {a : ℕ}
    {Y : TupV (E := E) v n a} (hY : IsPrim v Λ Y) : IsPrim v Λ (k • Y) := by
  refine ⟨fun i => ?_, fun c hc => ?_⟩
  · rw [smul_apply_lin, kv_lin σ J v Λ hk]; exact hY.1 i
  · apply hY.2 c
    have : (∑ i, c i • (k • Y) i) = lin (Fv F v) σ J k (∑ i, c i • Y i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [smul_apply_lin, map_sum, map_smul]
    rw [this, kv_lin σ J v Λ hk] at hc
    exact hc

def CongL (g : ℕ) {r : ℕ} (X X' : TupV (E := E) v n (r + 1)) : Prop :=
  ∀ a, GM v Λ g (locF v X' a - locF v X a)

theorem congL_smul {g : ℕ} {r : ℕ} {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    {X X' : TupV (E := E) v n (r + 1)} (h : CongL (Λ := Λ) g X X') : CongL (Λ := Λ) g (k • X) (k • X') := by
  intro a
  rw [locF_smul, locF_smul, smul_apply_lin, smul_apply_lin, ← map_sub]
  exact gm_lin hk (h a)

theorem congL_trans {g : ℕ} {r : ℕ} {X Y Z : TupV (E := E) v n (r + 1)}
    (h1 : CongL (Λ := Λ) g X Y) (h2 : CongL (Λ := Λ) g Y Z) : CongL (Λ := Λ) g X Z := by
  intro a
  have := gm_add (h2 a) (h1 a)
  simpa using this

theorem congL_symm {g : ℕ} {r : ℕ} {X Y : TupV (E := E) v n (r + 1)}
    (h1 : CongL (Λ := Λ) g X Y) : CongL (Λ := Λ) g Y X := by
  intro a
  have := gm_neg (h1 a)
  simpa using this

theorem mem_congruence_subgroup_iff {g : ℕ} {r : ℕ} {P : Frame E n r} {k : HA (Fv F v) σ J} :
    k ∈ K1 σ J v Λ g P ↔ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v ∧
      CongL (Λ := Λ) g (ratTup (F := F) (Fv F v) (F0 P)) (k • ratTup (F := F) (Fv F v) (F0 P)) :=
  Iff.rfl

theorem congruence_mul_mem {g : ℕ} {r : ℕ} {P : Frame E n r} {a b : HA (Fv F v) σ J}
    (ha : a ∈ K1 σ J v Λ g P) (hb : b ∈ K1 σ J v Λ g P) : a * b ∈ K1 σ J v Λ g P := by
  rw [mem_congruence_subgroup_iff] at *
  refine ⟨kv_mul' ha.1 hb.1, ?_⟩
  rw [mul_smul]
  exact congL_trans ha.2 (congL_smul ha.1 hb.2)

theorem column_addition_fixes_transpose {g : ℕ} {r : ℕ} {P : Frame E n r} {a : HA (Fv F v) σ J}
    (ha : a ∈ K1 σ J v Λ g P) : a⁻¹ ∈ K1 σ J v Λ g P := by
  rw [mem_congruence_subgroup_iff] at *
  refine ⟨kv_inv' ha.1, ?_⟩
  have := congL_smul (kv_inv' ha.1) ha.2
  rw [inv_smul_smul] at this
  exact congL_symm this

theorem congruence_mul_mem_iff {g : ℕ} {r : ℕ} {P : Frame E n r} {a : HA (Fv F v) σ J}
    (ha : a ∈ K1 σ J v Λ g P) (m : HA (Fv F v) σ J) :
    a * m ∈ K1 σ J v Λ g P ↔ m ∈ K1 σ J v Λ g P := by
  refine ⟨fun h => ?_, fun h => congruence_mul_mem ha h⟩
  have := congruence_mul_mem (column_addition_fixes_transpose ha) h
  rwa [← mul_assoc, inv_mul_cancel, one_mul] at this

theorem conj_mem_congruence_iff {g : ℕ} {r : ℕ} {P P' : Frame E n r} {κ : HA (Fv F v) σ J}
    (hκ : κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (hc : CongL (Λ := Λ) g (ratTup (F := F) (Fv F v) (F0 P)) (κ • ratTup (F := F) (Fv F v) (F0 P')))
    {h : HA (Fv F v) σ J} (hh : h • ratTup (F := F) (Fv F v) (F0 P') = ratTup (F := F) (Fv F v) (F0 P')) :
    κ * h * κ⁻¹ ∈ K1 σ J v Λ g P ↔ h ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v := by
  constructor
  · intro hm
    have h1 := kv_mul' (kv_mul' (kv_inv' hκ) hm.1) hκ
    rwa [show κ⁻¹ * (κ * h * κ⁻¹) * κ = h by group] at h1
  · intro hK
    have hm : κ * h * κ⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v := kv_mul' (kv_mul' hκ hK) (kv_inv' hκ)
    refine (mem_congruence_subgroup_iff).2 ⟨hm, ?_⟩

    have h1 := congL_smul hm hc
    rw [show (κ * h * κ⁻¹) • κ • ratTup (F := F) (Fv F v) (F0 P') = κ • ratTup (F := F) (Fv F v) (F0 P') by
      rw [← mul_smul, show κ * h * κ⁻¹ * κ = κ * h by group, mul_smul, hh]] at h1
    exact congL_trans hc (congL_symm h1)

end Alg

end PI.LocMassTypW
end
end

section

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct Classical

def frU {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {n r : ℕ} (P : Frame E n r) (u : UIdx r → Fv F v ⊗[F] E) :
    TupV (E := E) v n (r + 1) :=
  fun b => ∑ a, uMat v u a b • ratTup (Fv F v) (F0 P) a

def Cong {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) {r : ℕ} (g : ℕ) (P : Frame E n r) (x : HA (Fv F v) σ J)
    (u : UIdx r → Fv F v ⊗[F] E) : Prop :=
  ∀ b, ∃ w ∈ latLoc (E := E) v Λ,
    locF v (x • ratTup (Fv F v) (F0 P)) b - locF v (frU v P u) b = sc (E := E) v (g : Fv F v) • w

section Grp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}
  {Λ : Set (Fin n → E)}

theorem smul_tup (k : HA (Fv F v) σ J) {a : ℕ} (X : Fin a → Fin n → Fv F v ⊗[F] E) (b : Fin a) :
    (k • X) b = lin (Fv F v) σ J k (X b) := rfl

theorem kv_lat {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    {w : Fin n → Fv F v ⊗[F] E} (hw : w ∈ latLoc (E := E) v Λ) :
    lin (Fv F v) σ J k w ∈ latLoc (E := E) v Λ := (hk w).1 hw

theorem kv_mul {a b : HA (Fv F v) σ J} (ha : a ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (hb : b ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) : a * b ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  Subgroup.mul_mem (Kloc (E := E) v Λ) ha hb

theorem kv_inv {a : HA (Fv F v) σ J} (ha : a ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) :
    a⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  Subgroup.inv_mem (Kloc (E := E) v Λ) ha

theorem kv_one : (1 : HA (Fv F v) σ J) ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  Subgroup.one_mem (Kloc (E := E) v Λ)

theorem locF_act (k : HA (Fv F v) σ J) {r : ℕ} (Y : TupV (E := E) v n (r + 1)) (b : Fin (r + 1)) :
    locF v (k • Y) b = lin (Fv F v) σ J k (locF v Y b) := by
  show sc (E := E) v (alp v r b) • (k • Y) b = _
  rw [smul_tup, locF, map_smul]

theorem locF_comb {r : ℕ} (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E))
    (X : TupV (E := E) v n (r + 1)) (b : Fin (r + 1)) :
    locF v (fun b => ∑ a, M a b • X a) b =
      ∑ a, (sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * M a b) • locF v X a := by
  simp only [locF, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have h : (alp v r a)⁻¹ * alp v r b * alp v r a = alp v r b := by
    rw [mul_comm (alp v r a)⁻¹, mul_assoc, inv_mul_cancel₀ (alp_ne' v r a), mul_one]
  rw [mul_right_comm, sc_mul', h]

theorem prim_div {r : ℕ} {Y : TupV (E := E) v n (r + 1)} (hP : IsPrim v Λ Y)
    (c : Fin (r + 1) → Fv F v ⊗[F] E) {t : Fv F v} (ht : t ≠ 0) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc (E := E) v Λ) (h : ∑ a, c a • Y a = sc (E := E) v t • y) (a : Fin (r + 1)) :
    sc (E := E) v t⁻¹ * c a ∈ OEv (E := E) v := by
  apply hP.2 (fun a => sc (E := E) v t⁻¹ * c a) _ a
  have : ∑ a, (sc (E := E) v t⁻¹ * c a) • Y a = sc (E := E) v t⁻¹ • ∑ a, c a • Y a := by
    rw [Finset.smul_sum]; simp only [smul_smul]
  rw [this, h, sc_smul_sc, inv_mul_cancel₀ ht, sc_one', one_smul]
  exact hy

theorem hR_smul (x w : Fin n → Fv F v ⊗[F] E) (c : Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • w) = c * hR (Fv F v) σ J x w := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sd_smul (hSD : IsSDLoc σ J v Λ) {c : Fv F v ⊗[F] E} (hc : c ∈ OEv (E := E) v)
    {w : Fin n → Fv F v ⊗[F] E} (hw : w ∈ latLoc (E := E) v Λ) : c • w ∈ latLoc (E := E) v Λ :=
  (hSD (c • w)).2 fun x hx => by rw [hR_smul]; exact oev_mul v hc ((hSD w).1 hw x hx)

theorem lat_comb (hSD : IsSDLoc σ J v Λ) {r : ℕ} {Y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E}
    (hY : ∀ a, Y a ∈ latLoc (E := E) v Λ) {c : Fin (r + 1) → Fv F v ⊗[F] E}
    (hc : ∀ a, c a ∈ OEv (E := E) v) : ∑ a, c a • Y a ∈ latLoc (E := E) v Λ :=
  Submodule.sum_mem _ fun a _ => sd_smul hSD (hc a) (hY a)

theorem uMat_sub {r : ℕ} (u u' : UIdx r → Fv F v ⊗[F] E) (a b : Fin (r + 1)) :
    uMat v u' a b - uMat v u a b =
      if h : a < b then u' ⟨(a, b), h⟩ - u ⟨(a, b), h⟩ else 0 := by
  by_cases h1 : a = b
  · subst h1; simp [uMat]
  · by_cases h2 : a < b <;> simp [uMat, h1, h2]

theorem locF_frU_sub {r : ℕ} (P : Frame E n r) (u u' : UIdx r → Fv F v ⊗[F] E) (b : Fin (r + 1)) :
    locF v (frU v P u') b - locF v (frU v P u) b =
      ∑ a, (sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * (uMat v u' a b - uMat v u a b)) •
        locF v (ratTup (Fv F v) (F0 P)) a := by
  unfold frU
  rw [locF_comb, locF_comb, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← sub_smul, mul_sub]

theorem cong_lat_iff (hSD : IsSDLoc σ J v Λ) {r : ℕ} {P : Frame E n r}
    (hP : IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P)))) {g : ℕ} (hg : (g : Fv F v) ≠ 0)
    (u u' : UIdx r → Fv F v ⊗[F] E) :
    (∀ b, ∃ z ∈ latLoc (E := E) v Λ,
      locF v (frU v P u') b - locF v (frU v P u) b = sc (E := E) v (g : Fv F v) • z) ↔
      -u + u' ∈ UOg (E := E) v g r := by
  constructor
  · rintro h ⟨⟨a, b⟩, hab⟩
    obtain ⟨z, hz, hzeq⟩ := h b
    rw [locF_frU_sub] at hzeq
    have := prim_div hP _ hg hz hzeq a
    rw [uMat_sub, dite_eq_left hab] at this
    dsimp only
    convert this using 1
    rw [Pi.add_apply, Pi.neg_apply, neg_add_eq_sub, ← mul_assoc, sc_mul']
    congr 1; congr 1; ring
  · intro h b
    refine ⟨∑ a, (sc (E := E) v (g : Fv F v)⁻¹ * (sc (E := E) v ((alp v r a)⁻¹ * alp v r b) *
      (uMat v u' a b - uMat v u a b))) • locF v (ratTup (Fv F v) (F0 P)) a,
      lat_comb hSD hP.1 ?_, ?_⟩
    · intro a
      rw [uMat_sub]
      split_ifs with hab
      · have := h ⟨(a, b), hab⟩
        simp only [Pi.add_apply, Pi.neg_apply, neg_add_eq_sub] at this
        convert this using 1
        rw [← mul_assoc, sc_mul']
        congr 1; congr 1; ring
      · rw [mul_zero, mul_zero]; exact oev_zero v
    · rw [locF_frU_sub, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_smul, ← mul_assoc, sc_mul', mul_inv_cancel₀ hg, sc_one', one_mul]

theorem cong_iff (hSD : IsSDLoc σ J v Λ) {r : ℕ} {P : Frame E n r}
    (hP : IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P)))) {g : ℕ} (hg : (g : Fv F v) ≠ 0)
    {x y : HA (Fv F v) σ J} (hx : x ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (hy : y ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) {u u' : UIdx r → Fv F v ⊗[F] E}
    (hcx : Cong σ J v Λ g P x u) (hcy : Cong σ J v Λ g P y u') :
    x⁻¹ * y ∈ K1 σ J v Λ g P ↔ -u + u' ∈ UOg (E := E) v g r := by
  rw [← cong_lat_iff hSD hP hg u u']
  have key : ∀ b, locF v ((x⁻¹ * y) • ratTup (Fv F v) (F0 P)) b - locF v (ratTup (Fv F v) (F0 P)) b =
      lin (Fv F v) σ J x⁻¹ (locF v (y • ratTup (Fv F v) (F0 P)) b -
        locF v (x • ratTup (Fv F v) (F0 P)) b) := by
    intro b
    rw [map_sub, locF_act, locF_act, locF_act, lin_mul, lin_inv_lin]
  constructor
  · rintro ⟨-, hk⟩ b
    obtain ⟨z, hz, hzeq⟩ := hk b
    obtain ⟨wx, hwx, hwxe⟩ := hcx b
    obtain ⟨wy, hwy, hwye⟩ := hcy b
    refine ⟨lin (Fv F v) σ J x z - wy + wx,
      Submodule.add_mem _ (Submodule.sub_mem _ (kv_lat hx hz) hwy) hwx, ?_⟩
    have e1 : locF v (y • ratTup (Fv F v) (F0 P)) b - locF v (x • ratTup (Fv F v) (F0 P)) b =
        sc (E := E) v (g : Fv F v) • lin (Fv F v) σ J x z := by
      rw [key] at hzeq
      have := congrArg (lin (Fv F v) σ J x) hzeq
      rwa [← lin_mul, mul_inv_cancel, lin_one, map_smul] at this
    rw [smul_add, smul_sub, ← e1, ← hwye, ← hwxe]
    abel
  · intro h
    refine ⟨kv_mul (kv_inv hx) hy, fun b => ?_⟩
    obtain ⟨z, hz, hzeq⟩ := h b
    obtain ⟨wx, hwx, hwxe⟩ := hcx b
    obtain ⟨wy, hwy, hwye⟩ := hcy b
    refine ⟨lin (Fv F v) σ J x⁻¹ (z + wy - wx),
      kv_lat (kv_inv hx) (Submodule.sub_mem _ (Submodule.add_mem _ hz hwy) hwx), ?_⟩
    rw [key, ← map_smul]
    congr 1
    rw [smul_sub, smul_add, ← hzeq, ← hwye, ← hwxe]
    abel

end Grp

end PI.LocMassTypW
end
end
