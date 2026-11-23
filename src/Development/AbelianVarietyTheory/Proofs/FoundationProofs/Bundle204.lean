module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle194
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
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases

@[expose] public section

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LatBasisAt

variable {K : Type} [Field K] [NumberField K]

abbrev locRing (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  haveI := w.isPrime
  Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors

lemma mem_locRing (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ locRing w ↔ ∃ (a s : 𝓞 K) (_ : s ∉ w.asIdeal),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl

lemma algebraMap_ne_zero (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K}
    (hs : s ∉ w.asIdeal) : algebraMap (𝓞 K) K s ≠ 0 := by
  intro h
  have : s = 0 := (IsFractionRing.injective (𝓞 K) K) (by simpa using h)
  exact hs (this ▸ w.asIdeal.zero_mem)

lemma mem_localization_iff (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ M :=
  Iff.rfl

lemma mem_localization_iff_mem_span (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ↔ x ∈ Submodule.span (locRing w) (M : Set (Fin d → K)) := by
  constructor
  · intro h
    obtain ⟨s, hs, hsx⟩ := (mem_localization_iff w M x).mp h
    have hs0 := algebraMap_ne_zero w hs
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := (Ideal.ne_top_iff_one _).mp w.isPrime.ne_top
    have hu : (algebraMap (𝓞 K) K s)⁻¹ ∈ locRing w := (mem_locRing w _).mpr ⟨1, s, hs, by simp⟩
    have hx : x = (⟨_, hu⟩ : locRing w) • (s • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]
      simp [hs0]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
  · intro hx
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := (Ideal.ne_top_iff_one _).mp w.isPrime.ne_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact (mem_localization_iff w M y).mpr ⟨1, h1, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := (mem_localization_iff w M y).mp hy
      obtain ⟨r, t, ht, hat⟩ := (mem_locRing w a).mp a.2
      refine (mem_localization_iff w M _).mpr ⟨t * s, fun h => (w.isPrime.mem_or_mem h).elim ht hs, ?_⟩
      have ht0 := algebraMap_ne_zero w ht
      have he : (t * s) • (a • y) = r • (s • y) := by
        rw [Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
          ← algebraMap_smul K s, smul_smul, smul_smul]
        congr 1
        rw [map_mul]
        field_simp
      rw [he]
      exact M.smul_mem r hsy

theorem basisAtEx :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
      (M : Submodule (𝓞 K) (Fin n → K)), Submodule.IsFullLattice K M →
      ∀ w : HeightOneSpectrum (𝓞 K), ∃ B : GL (Fin n) K, Formalism.L2.DIV.IsBasisAt w M B := by
  intro K _ _ d L hL w
  haveI := w.isPrime
  have : IsDiscreteValuationRing (locRing w) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) w.ne_bot (locRing w)
  set N : Submodule (locRing w) (Fin d → K) := Submodule.span (locRing w) (L : Set (Fin d → K))
    with hN
  have : Module.Finite (locRing w) N := by
    obtain ⟨s, hs⟩ := hL.fg
    rw [Module.Finite.iff_fg]
    refine ⟨s, ?_⟩
    rw [hN, ← hs, Submodule.span_span_of_tower]
  have : Module.IsTorsionFree (locRing w) N := inferInstance
  let b := Module.Free.chooseBasis (locRing w) N
  let v : Module.Free.ChooseBasisIndex (locRing w) N → Fin d → K := fun i => (b i : Fin d → K)
  have hliA : LinearIndependent (locRing w) v := b.linearIndependent.map' N.subtype N.ker_subtype
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing (locRing w) K).mp hliA
  have hspanA : Submodule.span (locRing w) (Set.range v) = N := by
    have : Set.range v = N.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hL.span_eq_top, Submodule.span_le]
    intro x hx
    have hxN : x ∈ Submodule.span (locRing w) (Set.range v) := by
      rw [hspanA]; exact Submodule.subset_span hx
    exact Submodule.span_le_restrictScalars (locRing w) K _ hxN
  let bK : Basis _ K (Fin d → K) := Basis.mk hli hspan
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (locRing w) N) = d := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  have hli' : LinearIndependent K (v ∘ e.symm) := hli.comp _ e.symm.injective
  let P : Matrix (Fin d) (Fin d) K := Matrix.of fun a j => (v ∘ e.symm) j a
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hli'
  refine ⟨hP.unit, ?_⟩
  have hcol : Formalism.L2.DIV.colLat hP.unit = Submodule.span (𝓞 K) (Set.range (v ∘ e.symm)) := rfl
  unfold Formalism.L2.DIV.IsBasisAt
  ext x
  rw [hcol, mem_localization_iff_mem_span, mem_localization_iff_mem_span, Submodule.span_span_of_tower,
    EquivLike.range_comp, hspanA]

end GlobalTheory.LatBasisAt
end
end

section

open Formalism.MainNotions

namespace GlobalTheory.ResidueRoot

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by show ‖(1 : ℂ_[p])‖ ≤ 1; simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by show ‖(0 : ℂ_[p])‖ ≤ 1; simp
  neg_mem' := fun {a} ha => by show ‖-a‖ ≤ 1; rw [norm_neg]; exact ha

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem norm_add_lt_one {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

theorem sub_one_lt_of_pow_p {y : ℂ_[p]} (hy : ‖y‖ ≤ 1) (h : ‖y ^ p - 1‖ < 1) : ‖y - 1‖ < 1 := by
  let Y : ball p := ⟨y, hy⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (Y - 1) 1
  have hr' := congrArg (fun t : ball p => (t : ℂ_[p])) hr
  simp only [sub_add_cancel, one_pow, mul_one] at hr'
  push_cast at hr'
  have hz : ‖y - 1‖ ≤ 1 := (Y - 1).2
  have hrr : ‖(r : ℂ_[p])‖ ≤ 1 := r.2
  have e : (y - 1) ^ p = (y ^ p - 1) + -((p : ℂ_[p]) * (y - 1) * r) := by
    have : (Y : ℂ_[p]) = y := rfl
    rw [this] at hr'
    rw [hr']; ring
  have h2 : ‖(y - 1) ^ p‖ < 1 := by
    rw [e]
    refine norm_add_lt_one h ?_
    rw [norm_neg, norm_mul, norm_mul, mul_assoc]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) norm_p_lt_one
      (mul_le_one₀ hz (norm_nonneg _) hrr)
  rw [norm_pow] at h2
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).1 h2

theorem sub_one_lt_of_pow_p_pow (k : ℕ) {y : ℂ_[p]} (hy : ‖y‖ ≤ 1) (h : ‖y ^ p ^ k - 1‖ < 1) :
    ‖y - 1‖ < 1 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply sub_one_lt_of_pow_p
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy
    · rwa [← pow_mul, ← pow_succ]

theorem exists_root {x : ℂ_[p]} {m : ℕ} (hm : 0 < m) (h : ‖x ^ m - 1‖ < 1) :
    ∃ ζ : ℂ_[p], ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] m
  have e := congrArg (eval x) (X_pow_sub_one_eq_prod hm hξ)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at e
  rw [e, norm_prod] at h
  by_contra hc
  push Not at hc
  refine absurd h (not_lt.2 ?_)
  exact Finset.prod_induction _ (fun r : ℝ => 1 ≤ r) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
    le_rfl fun ζ hζ => hc ζ ((mem_nthRootsFinset hm _).1 hζ)

theorem exists_pow_alg (x : PadicAlgCl p) (hx : ‖x‖ = 1) : ∃ n, 0 < n ∧ ‖x ^ n - 1‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one
  | exact _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one
  | (apply _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one ..)

end GlobalTheory.ResidueRoot

namespace GlobalTheory

open ResidueRoot

theorem exists_mem_Wp_norm_sub_lt_one (p : ℕ) [hp : Fact p.Prime] (x : ℂ_[p]) (hx : ‖x‖ ≤ 1) :
    ∃ w ∈ GL3Theta.Wp p, ‖x - w‖ < 1 := by
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.1
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)) x 1 one_pos
  rw [dist_eq_norm] at hy
  have hy1 : ‖(y : ℂ_[p])‖ ≤ 1 := by
    have : (y : ℂ_[p]) = x + -(x - y) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
  rcases hy1.lt_or_eq with h | h
  · refine ⟨0, zero_mem _, ?_⟩
    have := norm_add_lt_one hy h
    simpa using this
  · obtain ⟨n, hn, hyn⟩ := exists_pow_alg y (by rwa [PadicComplex.norm_extends] at h)
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.ne_one
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero p))
    have h3 : ‖((y : ℂ_[p]) ^ m) ^ p ^ k - 1‖ < 1 := by
      rw [← PadicComplex.norm_extends, PadicComplex.coe_eq, map_sub, map_pow, map_one,
        ← PadicComplex.coe_eq] at hyn
      rwa [← pow_mul, mul_comm]
    have h4 := sub_one_lt_of_pow_p_pow k
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy1) h3
    obtain ⟨ζ, hζ, h5⟩ := exists_root hm0 h4
    refine ⟨ζ, Subring.le_topologicalClosure _ (Subring.subset_closure
      ⟨m, hm0, ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm).symm, hζ⟩), ?_⟩
    have := norm_add_lt_one hy h5
    simpa using this

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction

namespace GlobalTheory.BlochKatoRank

theorem rank_subquotient_eq {O K X Y : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module K Y] [Module O Y]
    [IsScalarTower O K Y] (φ : X →ₗ[O] Y) (Z B A : Submodule O X) (Zf BV : Submodule K Y)
    (h1 : ∀ a ∈ A, φ a ∈ Zf) (h2 : ∀ b ∈ B, φ b ∈ BV)
    (h3 : ∀ a, φ a ∈ BV → ∃ m : O, m ≠ 0 ∧ m • a ∈ B)
    (h4 : ∀ y ∈ Zf, ∃ m : O, m ≠ 0 ∧ ∃ a ∈ Z, a ∈ A ∧ φ a = m • y) :
    Module.rank O ((A.comap Z.subtype).map (Submodule.mkQ (B.comap Z.subtype))) =
      Module.rank K (Zf ⧸ BV.comap Zf.subtype) := by
  let A' := A.comap Z.subtype
  let g : A' →ₗ[O] (Z ⧸ B.comap Z.subtype) := (Submodule.mkQ _).comp A'.subtype
  have hg : LinearMap.range g = A'.map (Submodule.mkQ (B.comap Z.subtype)) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  let f0 : A' →ₗ[O] Zf :=
    { toFun := fun a => ⟨φ a.1.1, h1 _ a.2⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp) }
  let f : A' →ₗ[O] (Zf ⧸ BV.comap Zf.subtype) :=
    ((Submodule.mkQ (BV.comap Zf.subtype)).restrictScalars O).comp f0
  have hgk : ∀ a : A', g a = 0 ↔ a.1.1 ∈ B := fun a => Submodule.Quotient.mk_eq_zero _
  have hfk : ∀ a : A', f a = 0 ↔ φ a.1.1 ∈ BV := fun a => Submodule.Quotient.mk_eq_zero _
  have hle : LinearMap.ker g ≤ LinearMap.ker f := fun a ha =>
    (hfk a).2 (h2 _ ((hgk a).1 ha))
  let F := (LinearMap.ker g).liftQ f hle
  haveI : IsLocalizedModule (nonZeroDivisors O) F := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x y} h => ?_⟩
    · have hs : algebraMap O K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      rw [Module.End.isUnit_iff]
      refine ⟨fun a b h => ?_, fun a => ⟨(algebraMap O K s)⁻¹ • a, ?_⟩⟩
      · simp only [Module.algebraMap_end_apply] at h
        rw [← algebraMap_smul K, ← algebraMap_smul K (s : O) b] at h
        exact smul_right_injective _ hs h
      · rw [Module.algebraMap_end_apply, ← algebraMap_smul K, smul_inv_smul₀ hs]
    · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨m, hm, a, haZ, haA, ha⟩ := h4 y.1 y.2
      refine ⟨(Submodule.Quotient.mk ⟨⟨a, haZ⟩, haA⟩, ⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩), ?_⟩
      have : f0 ⟨⟨a, haZ⟩, haA⟩ = m • y := Subtype.ext ha
      change m • ((BV.comap Zf.subtype).mkQ.restrictScalars O) y =
        ((BV.comap Zf.subtype).mkQ.restrictScalars O) (f0 ⟨⟨a, haZ⟩, haA⟩)
      rw [this, map_smul]
    · rw [← sub_eq_zero, ← map_sub] at h
      suffices H : ∃ m : O, m ≠ 0 ∧ m • (x - y) = 0 by
        obtain ⟨m, hm, H⟩ := H
        exact ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, by
          rw [smul_sub, sub_eq_zero] at H; exact H⟩
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x - y)
      rw [← ha] at h ⊢
      obtain ⟨m, hm, H⟩ := h3 _ ((hfk a).1 h)
      refine ⟨m, hm, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact (hgk _).2 H
  rw [← hg, ← (LinearMap.quotKerEquivRange g).rank_eq,
    IsLocalization.rank_eq K (nonZeroDivisors O) le_rfl,
    IsLocalizedModule.rank_eq (nonZeroDivisors O) le_rfl F]

section Bridge

open GlobalTheory.BlochKatoIntegralScalars

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

include Bw in
theorem natCast_pow_ne_zero (N : ℕ) : (l : O₀) ^ N ≠ 0 := by
  intro h
  have := congrArg Bw.toLL h
  rw [map_pow, map_natCast, map_zero] at this
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast (eq_zero_of_pow_eq_zero this))

theorem exists_integral {X : Type} [TopologicalSpace X] [CompactSpace X]
    (c : X → Fin m → ↥Bw.LL.1) (hc : Continuous c) :
    ∃ d : O₀, d ≠ 0 ∧ ∃ f : X → Fin m → O₀, Continuous f ∧
      ∀ g j, Bw.toLL (f g j) = Bw.toLL d * c g j := by
  obtain ⟨N, hN⟩ := exists_pow_mul_mem_OL Bw.LL c hc
  refine ⟨(l : O₀) ^ N, natCast_pow_ne_zero Bw N, fun g j => Bw.eO.symm ⟨_, hN g j⟩, ?_, ?_⟩
  · refine continuous_pi fun j => Bw.eO_symm_cont.comp ?_
    exact Continuous.subtype_mk (continuous_const.mul ((continuous_apply j).comp hc)) _
  · intro g j
    show ((Bw.eO (Bw.eO.symm _) : Loc.OL Bw.LL) : Bw.LL.1) = _
    rw [RingEquiv.apply_symm_apply, map_pow, map_natCast]

end Bridge

end GlobalTheory.BlochKatoRank
end
