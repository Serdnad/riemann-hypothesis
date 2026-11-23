module

public import Development.EtaleCohomology.KummerTheory.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.EtaleCohomology.KummerTheory.CupAWCutEv
public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Development.EtaleCohomology.KummerTheory.Bundle002
public import Development.EtaleCohomology.KummerTheory.Bundle003
public import Development.EtaleCohomology.KummerTheory.Bundle004
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

theorem ghostSec_of (hG : Ghost) (h1 : Corep) (h2 : HomKill) : GhostSec := by
  intro Λ _ S C hi hz N m hl j hj U x hx
  have : C.IsStrictlyGE (-1) := (CochainComplex.isStrictlyGE_iff _ _).2 (fun i hi => hz i hi)
  obtain ⟨P, z, hP⟩ := h1 Λ S U
  obtain ⟨f, rfl⟩ := (hP (C.X j)).2 x
  obtain ⟨g, hg⟩ := hG (SlShv Λ S) C hi N m (fun j hj => h2 Λ S C N j (hl j hj)) j hj P f
    ((hP _).1 (hx.trans rfl))
  refine ⟨(g.hom.app (op U)).hom z, ?_⟩
  have := congrArg (fun φ : P ⟶ C.X j => (φ.hom.app (op U)).hom z) hg
  refine this.trans ?_
  generalize N ^ (m + 1) = k
  induction k with
  | zero => simp only [zero_smul]; rfl
  | succ k ih => rw [succ_nsmul, succ_nsmul, ← ih]; rfl

theorem glob_of (h1 : ConeCx) (h2 : GhostSec) : Glob := by
  intro Λ _ I J K μ hJ hK X S p r M γ hc N m hl j hj U x hx
  obtain ⟨C, hi, hz, e, he, hd⟩ := h1 Λ μ hJ hK p r M γ hc
  have hloc : ∀ j : ℤ, j < m → CxLoc C N j := by
    intro j hj U x hx u
    obtain ⟨V, g, hg, y, hy⟩ := hl j hj U (e j U x) (by rw [← hd j (j + 1) rfl, hx, map_zero]) u
    refine ⟨V, g, hg, (e _ V).symm y, (e j V).injective ?_⟩
    rw [hd (j - 1) j (by omega), AddEquiv.apply_symm_apply, hy, map_nsmul, he]
  obtain ⟨y, hy⟩ := h2 Λ S C hi hz N m hloc j hj U ((e j U).symm x) ((e (j + 1) U).injective (by
    rw [hd j (j + 1) rfl, AddEquiv.apply_symm_apply, hx, map_zero]))
  refine ⟨e _ U y, ?_⟩
  rw [← hd (j - 1) j (by omega), hy, map_nsmul, AddEquiv.apply_symm_apply]

theorem clsMore_of (hD : Dict) : ClsMore := by
  intro Λ _ I X n
  obtain ⟨_, d2, d3, d4, _⟩ := hD Λ I X n
  have h0 : IsCls (0 : CochainComplex.HomComplex.CohomologyClass ((chains Λ).obj (sch.obj X)) I n) 0 := by
    obtain ⟨a, ha⟩ := d2 0
    have := (d4 _ _ _ _ ha (d4 _ _ _ _ ha ha).2).1
    rwa [add_neg_cancel, add_neg_cancel] at this
  refine ⟨h0, ?_, ?_, ?_⟩
  · intro N x a h
    induction N with
    | zero => rw [zero_nsmul, zero_nsmul]; exact h0
    | succ N ih => rw [succ_nsmul, succ_nsmul]; exact (d4 _ _ _ _ ih h).1
  · intro ι _ x a h
    classical
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact h0
    | insert t s ht ih => rw [Finset.sum_insert ht, Finset.sum_insert ht]; exact (d4 _ _ _ _ (h t) ih).1
  · intro m hm x x' a a' h h'
    obtain rfl : m = n - 1 := by omega
    have := (d3 _ _ (d4 _ _ _ _ h (d4 _ _ _ _ h' h').2).1).2
    rwa [← sub_eq_add_neg, ← sub_eq_add_neg, sub_eq_zero] at this

theorem lh_of (hD : Dict) (hG : Ghost) (h1 : LocKer) (h2 : LocCok) (h3 : LocCone) (h4 : ExIso) (h5 : ConeCx) (h6 : Corep)
    (h7 : HomKill) : LH :=
  goal_of hD h1 h2 h3 (glob_of h5 (ghostSec_of hG h6 h7)) h4

end LateralTheory.KummerTheory.LHCut
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DegreeZeroClassRestriction

theorem res_neg_zero (R : Type) [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) := by
  apply HomologicalComplex.isZero_extend_X
  intro i hi
  have h' : ((i : ℕ) : ℤ) = s := hi
  omega

def asHom {X U : Scheme.{0}} (x : Sx (sch.obj X) 0 U) : U ⟶ X := by
  unfold sch at x; exact x

def ofHom {X U : Scheme.{0}} (g : U ⟶ X) : Sx (sch.obj X) 0 U := by
  unfold sch; exact g

theorem res_ofHom {X U : Scheme.{0}} (x : Sx (sch.obj X) 0 U) : Sx.res (asHom x) (ofHom (𝟙 X)) = x := by
  change asHom x ≫ 𝟙 X = x
  exact Category.comp_id (asHom x)

theorem cochain_eq (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
    (α β : Cochain ((chains R).obj (sch.obj X)) (res R F) 0)
    (h : ev α 0 0 (by simp) X (𝟙 X) = ev β 0 0 (by simp) X (𝟙 X)) : α = β := by
  apply LateralTheory.KummerTheory.AW.ev_ext
  intro p s hp U x
  cases p with
  | zero =>
    obtain rfl : s = 0 := by simpa using hp.symm
    have key : ∀ γ : Cochain ((chains R).obj (sch.obj X)) (res R F) 0,
        ev γ 0 0 hp U x = Sec.res (asHom x) (ev γ 0 0 hp X (ofHom (𝟙 X))) := by
      intro γ
      rw [LateralTheory.KummerTheory.AW.ev_res]
      rw [res_ofHom]
    rw [key α, key β]
    exact congrArg _ h
  | succ k =>
    have hs : s < 0 := by omega
    rw [LateralTheory.KummerTheory.AW.ev_eq, LateralTheory.KummerTheory.AW.ev_eq, (res_neg_zero R F s hs).eq_of_tgt
      ((chainsXIso R (sch.obj X) (k + 1)).inv ≫ α.v _ _ hp) ((chainsXIso R (sch.obj X) (k + 1)).inv ≫ β.v _ _ hp)]

end LateralTheory.KummerTheory.DegreeZeroClassRestriction

theorem LateralTheory.KummerTheory.Cls0_of (_hT : LateralTheory.KummerTheory.TwSec) : LateralTheory.KummerTheory.Cls0 := by
  intro R _ F X α β h
  have e : α.1 = β.1 := LateralTheory.KummerTheory.DegreeZeroClassRestriction.cochain_eq R F X α.1 β.1 h
  exact congrArg CohomologyClass.mk (Cocycle.ext e)
end
end

section

noncomputable section

namespace LateralTheory.KummerTheory

def PlaceGood (k K : Type) [Field k] [Field K] [Algebra k K] (A : LocalSubring K) : Prop :=
  (∀ c : k, algebraMap k K c ∈ A.toSubring) ∧
    ∀ a ∈ A.toSubring, ∃ c : k, a = algebraMap k K c ∨ (a - algebraMap k K c)⁻¹ ∉ A.toSubring

def PlaceZorn : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K],
  ∃ A : LocalSubring K, PlaceGood k K A ∧ ∀ B : LocalSubring K, A ≤ B → PlaceGood k K B → B ≤ A

def PlaceStep : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] (A : LocalSubring K),
  PlaceGood k K A → (∀ B : LocalSubring K, A ≤ B → PlaceGood k K B → B ≤ A) →
    ∀ x : K, x ∈ A.toSubring ∨ x⁻¹ ∈ A.toSubring

theorem PlaceEx_of (h1 : PlaceZorn) (h2 : PlaceStep) : PlaceEx := by
  intro k K _ _ _ _ _
  obtain ⟨A, hA, hmax⟩ := h1 k K
  have hv := h2 k K A hA hmax
  let T : ValuationSubring K := ⟨A.toSubring, hv⟩
  let σ : k →+* T := (algebraMap k K).codRestrict T (fun c => hA.1 c)
  refine ⟨T, σ, fun x => rfl, ?_⟩
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := hA.2 a a.2
  refine ⟨c, ?_⟩
  simp only [RingHom.comp_apply]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
  have hK : ((σ c : K) - (a : K)) * (w : K) = 1 := by
    have := congrArg (fun z : T => (z : K)) hw
    simpa using this
  rcases hc with h | h
  · have : (σ c : K) - (a : K) = 0 := by rw [h]; simp [σ]
    rw [this, zero_mul] at hK; exact zero_ne_one hK
  · apply h
    have hinv : ((σ c : K) - (a : K))⁻¹ = (w : K) := inv_eq_of_mul_eq_one_right hK
    have : ((a : K) - algebraMap k K c)⁻¹ = -(w : K) := by
      rw [← hinv, ← inv_neg, neg_sub]; rfl
    rw [this]; exact T.neg_mem _ w.2

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.KummerTheory

section Alg
variable (l : ℕ) [Fact l.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[l] M]

theorem adic_decomp [Module.Finite ℤ_[l] M] : ∃ (r : ℕ) (c : Fin r → M) (e : ℕ), 0 < e ∧
    LinearIndependent ℤ_[l] c ∧ ∀ x : M, ∃ (a : Fin r → ℤ_[l]) (τ : M), x = ∑ s, a s • c s + τ ∧ e • τ = 0 := by
  classical
  set T := Submodule.torsion ℤ_[l] M
  have hTfin : Module.Finite ℤ_[l] T := inferInstance
  obtain ⟨a, ha, ha0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors (Submodule.torsion_isTorsion (R := ℤ_[l]) (M := M))
  have hane : a ≠ 0 := nonZeroDivisors.ne_zero ha0
  have hkill : ∀ τ ∈ T, (l ^ a.valuation : ℕ) • τ = 0 := by
    intro τ hτ
    have h1 : a • (⟨τ, hτ⟩ : T) = 0 := Submodule.mem_annihilator.mp ha _ Submodule.mem_top
    have h2 : a • τ = 0 := congrArg Subtype.val h1
    rw [PadicInt.unitCoeff_spec hane, mul_smul] at h2
    have h3 := congrArg (fun v => (((PadicInt.unitCoeff hane)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • v) h2
    simp only [smul_zero, smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at h3
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    push_cast
    exact h3
  set Q := M ⧸ T
  let b := Module.finBasis ℤ_[l] Q
  let c : Fin (Module.finrank ℤ_[l] Q) → M := fun s => (Submodule.Quotient.mk_surjective T (b s)).choose
  have hc : ∀ s, T.mkQ (c s) = b s := fun s => (Submodule.Quotient.mk_surjective T (b s)).choose_spec
  have hcomp : T.mkQ ∘ c = b := funext hc
  refine ⟨_, c, l ^ a.valuation, pow_pos (Fact.out : l.Prime).pos _, ?_, ?_⟩
  · exact LinearIndependent.of_comp T.mkQ (hcomp ▸ b.linearIndependent)
  · intro x
    refine ⟨b.repr (T.mkQ x), x - ∑ s, b.repr (T.mkQ x) s • c s, by abel, hkill _ ?_⟩

    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [map_smul, hc]
    rw [b.sum_repr, sub_self]

theorem adic_qbasis {r : ℕ} (c : Fin r → M) (e : ℕ) (he : 0 < e) (hli : LinearIndependent ℤ_[l] c)
    (hdec : ∀ x : M, ∃ (a : Fin r → ℤ_[l]) (τ : M), x = ∑ s, a s • c s + τ ∧ e • τ = 0) :
    LinearIndependent ℚ_[l] (fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c s : ℚ_[l] ⊗[ℤ_[l]] M)) ∧
    Submodule.span ℚ_[l] (Set.range fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c s : ℚ_[l] ⊗[ℤ_[l]] M)) = ⊤ := by
  let f := TensorProduct.mk ℤ_[l] ℚ_[l] M 1
  refine ⟨hli.of_isLocalizedModule ℚ_[l] (nonZeroDivisors ℤ_[l]) f, ?_⟩
  have htop := span_eq_top_of_isLocalizedModule ℚ_[l] (nonZeroDivisors ℤ_[l]) f (v := Set.univ) Submodule.span_univ
  refine top_unique (htop ▸ Submodule.span_le.mpr ?_)
  rintro _ ⟨x, -, rfl⟩
  obtain ⟨a, τ, rfl, hτ⟩ := hdec x
  have hfτ : f τ = 0 := by
    have h1 : (e : ℚ_[l]) • f τ = 0 := by rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hτ, map_zero]
    exact (smul_eq_zero.mp h1).resolve_left (Nat.cast_ne_zero.mpr he.ne')

  rw [map_add (f := _), hfτ, add_zero, map_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [map_smul]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

end Alg

def levH (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) (k : ℕ) : Hl l E n i →+ Ht (l ^ k) E n i where
  toFun x := lev l x k
  map_zero' := rfl
  map_add' _ _ := rfl

theorem lev_comb (l : ℕ) [Fact l.Prime] {E : Spc} {n i : ℤ} {r : ℕ} (c : Fin r → Hl l E n i) (a : Fin r → ℤ_[l]) (k : ℕ) :
    lev l (∑ s, a s • c s) k = comb (l ^ k) (fun s => lev l (c s) k) (fun s => PadicInt.toZModPow k (a s)) := by
  change levH l E n i k _ = _

  rw [map_sum]
  rfl

theorem AdicAlg_of : AdicAlg := by
  intro l _ E n i hfin hker M hM hcok
  obtain ⟨r, c, e, he, hli, hdec⟩ := adic_decomp l (M := Hl l E n i)
  refine ⟨r, c, e * M, Nat.mul_pos he hM, adic_qbasis l c e he hli hdec, fun k => ⟨?_, ?_⟩⟩
  · intro t ht
    have : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    let a : Fin r → ℤ_[l] := fun s => ((t s).val : ℤ_[l])
    have hat : (fun s => PadicInt.toZModPow k (a s)) = t := funext fun s => by simp [a]
    have hx : lev l (∑ s, a s • c s) k = 0 := by rw [lev_comb, hat]; exact ht
    obtain ⟨y, hy⟩ := hker k _ hx
    obtain ⟨b, τ, rfl, hτ⟩ := hdec y
    have heq : ∑ s, ((e : ℤ_[l]) * a s - (e : ℤ_[l]) * (l : ℤ_[l]) ^ k * b s) • c s = 0 := by
      have h1 := congrArg (fun v => (e : ℤ_[l]) • v) hy
      simp only [smul_add, Finset.smul_sum, smul_smul] at h1
      have h2 : (e : ℤ_[l]) • (l : ℤ_[l]) ^ k • τ = 0 := by
        rw [smul_comm, Nat.cast_smul_eq_nsmul, hτ, smul_zero]
      rw [smul_smul] at h2
      rw [h2, add_zero] at h1
      simp only [sub_smul, Finset.sum_sub_distrib, h1, mul_assoc, sub_self]
    have hs := Fintype.linearIndependent_iff.mp hli _ heq
    have ht0 : t = 0 := by
      funext s
      have h3 : a s = (l : ℤ_[l]) ^ k * b s := by
        have h4 := hs s
        rw [sub_eq_zero, mul_assoc] at h4
        exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr he.ne') h4
      rw [← congrFun hat s]
      simp only [h3, map_mul, map_pow, map_natCast, Pi.zero_apply]
      rw [show ((l : ZMod (l ^ k)) ^ k) = ((l ^ k : ℕ) : ZMod (l ^ k)) by push_cast; rfl, ZMod.natCast_self, zero_mul]
    rw [ht0, smul_zero]
  · intro z
    obtain ⟨x, hx⟩ := hcok k z
    obtain ⟨a, τ, rfl, hτ⟩ := hdec x
    refine ⟨fun s => PadicInt.toZModPow k ((e : ℤ_[l]) * a s), ?_⟩
    rw [← lev_comb, mul_smul, ← hx]
    have key : ∀ w, lev l (e • w) k = e • lev l w k := fun w => map_nsmul (levH l E n i k) e w
    rw [← key, smul_add, hτ, add_zero, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_smul, Nat.cast_smul_eq_nsmul]

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def AdicKer : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), (∀ b, BockData l b E i) →
  (∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) → ∀ (n : ℤ) (k : ℕ) (x : Hl l E n i), lev l x k = 0 →
    ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ k) • y

def AdicFin : Prop := ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ), (∀ k : ℕ, Finite (Ht (l ^ k) E n i)) →
  (∀ (k : ℕ) (x : Hl l E n i), lev l x k = 0 → ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ k) • y) →
    Module.Finite ℤ_[l] (Hl l E n i)

def AdicCok : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), (∀ b, BockData l b E i) →
  (∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) → ∀ n : ℤ, Module.Finite ℤ_[l] (Hl l E (n + 1) i) →
    ∃ M : ℕ, 0 < M ∧ ∀ (k : ℕ) (z : Ht (l ^ k) E n i), ∃ x : Hl l E n i, lev l x k = M • z

theorem AdicLim_of (hK : AdicKer) (hF : AdicFin) (hC : AdicCok) : AdicLim := by
  intro hA l _ E i hB hFin n
  have hker : ∀ m : ℤ, ∀ (k : ℕ) (x : Hl l E m i), lev l x k = 0 → ∃ y : Hl l E m i, x = ((l : ℤ_[l]) ^ k) • y :=
    fun m => hK hA l E i hB hFin m
  have hfin : ∀ m : ℤ, Module.Finite ℤ_[l] (Hl l E m i) := fun m => hF l E m i (fun k => hFin k m) (hker m)
  exact ⟨hfin n, hker n, hC hA l E i hB hFin n (hfin (n + 1))⟩

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open scoped TensorProduct
open Polynomial

namespace LateralTheory.KummerTheory

section
variable (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A]
  [Algebra κ A]

theorem shInsepRes_pow [Nontrivial (A ⊗[κ] K)] (y : A ⊗[κ] K) :
    ∃ n : ℕ, ∃ a : A, y ^ (ringExpChar κ) ^ n = algebraMap A (A ⊗[κ] K) a := by
  set q := ringExpChar κ
  have : ExpChar (A ⊗[κ] K) q :=
    expChar_of_injective_algebraMap (algebraMap κ (A ⊗[κ] K)).injective q
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a k =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem κ q k
    refine ⟨n, c • a ^ q ^ n, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, ← hc]
    show (a ^ q ^ n) ⊗ₜ[κ] (algebraMap κ K c) = (c • a ^ q ^ n) ⊗ₜ[κ] (1 : K)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨n, a, ha⟩ := hx
    obtain ⟨m, b, hb⟩ := hy
    refine ⟨n + m, a ^ q ^ m + b ^ q ^ n, ?_⟩
    rw [add_pow_expChar_pow, map_add (f := _), map_pow, map_pow, ← ha, ← hb, ← pow_mul, ← pow_mul, ← pow_add,
      ← pow_add, add_comm m n]

omit [IsPurelyInseparable κ K] in
theorem shInsepRes_inj : Function.Injective (algebraMap A (A ⊗[κ] K)) :=
  Algebra.TensorProduct.includeLeft_injective (S := A) (algebraMap κ K).injective

theorem shInsepRes_localHom [Nontrivial (A ⊗[κ] K)] : IsLocalHom (algebraMap A (A ⊗[κ] K)) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨u, hu⟩ := ha
  obtain ⟨n, b, hb⟩ := shInsepRes_pow κ K A (↑u⁻¹ : A ⊗[κ] K)
  have hQ : (ringExpChar κ) ^ n ≠ 0 := pow_ne_zero _ (expChar_pos κ (ringExpChar κ)).ne'
  have h1 : algebraMap A (A ⊗[κ] K) (a ^ (ringExpChar κ) ^ n * b) = algebraMap A (A ⊗[κ] K) 1 := by
    rw [map_mul, map_pow, ← hb, ← hu, ← mul_pow, Units.mul_inv, one_pow, map_one]
  have h2 := shInsepRes_inj κ K A h1
  exact (isUnit_pow_iff hQ).mp (isUnit_of_mul_isUnit_left (h2 ▸ isUnit_one))

end

theorem SHInsepRes_of : SHInsepRes := by
  intro κ K A _ _ _ _ _ _ hA _
  obtain ⟨hh, hsc⟩ := hA
  have : IsLocalRing A := hh.toIsLocalRing
  have : IsLocalHom (algebraMap A (A ⊗[κ] K)) := shInsepRes_localHom κ K A
  let _ : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (A ⊗[κ] K)) :=
    (IsLocalRing.ResidueField.map (algebraMap A (A ⊗[κ] K))).toAlgebra
  have : Algebra.IsAlgebraic (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (A ⊗[κ] K)) := by
    constructor
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨n, a, ha⟩ := shInsepRes_pow κ K A y
    have hQ : 0 < (ringExpChar κ) ^ n := pow_pos (expChar_pos κ (ringExpChar κ)) _
    refine ⟨X ^ (ringExpChar κ) ^ n - C (IsLocalRing.residue A a), X_pow_sub_C_ne_zero hQ _, ?_⟩
    rw [map_sub, map_pow, aeval_X, aeval_C, ← map_pow, ha, sub_eq_zero]
    rfl
  exact Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField A)

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.SecSHPf

theorem bij_of_top (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (hU : ∀ S ∈ Scheme.etaleTopology U, S (𝟙 U)) : Function.Bijective (ofRings.sec (R := R) M U) := by
  constructor
  · intro x y hxy
    have h := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M))
      (X := op U) x y hxy
    have := hU _ h
    simp [Presheaf.equalizerSieve] at this
    exact this
  · intro s
    have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op U) s
    obtain ⟨t, ht⟩ := hU _ h
    refine ⟨t, ?_⟩
    simp at ht
    exact ht

def ShSect : Prop := ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)),
  Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _

theorem top_of_sect (hs : ShSect) (A : Type) [CommRing A] (hA : SH A) :
    ∀ S ∈ Scheme.etaleTopology (Spec (CommRingCat.of A)), S (𝟙 _) := by
  intro S hS
  obtain ⟨hH, hsc⟩ := hA
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  obtain ⟨i, y, hy⟩ := ((Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).1 𝒰.mem₀).1
    (IsLocalRing.closedPoint A : Spec (CommRingCat.of A))
  have he : Etale (𝒰.f i) := 𝒰.map_prop i
  have hsurj : Surjective (𝒰.f i) := by
    refine ⟨fun p => ?_⟩
    have hsp : p ⤳ (𝒰.f i) y := by
      rw [hy]; exact IsLocalRing.specializes_closedPoint (R := A) p
    obtain ⟨y', -, hy'⟩ := Flat.generalizingMap (𝒰.f i) hsp
    exact ⟨y', hy'⟩
  obtain ⟨s, hs'⟩ := hs A ⟨hH, hsc⟩ _ (𝒰.f i) he hsurj
  have := S.downward_closed (hle (𝒰.X i) (𝒰.f i) (Presieve.ofArrows.mk i)) s
  rwa [hs'] at this

end LateralTheory.KummerTheory.SecSHPf

namespace LateralTheory.KummerTheory

theorem SecSH_of (h : SecSHPf.ShSect) : SecSH := by
  intro A _ hA R _ M
  exact SecSHPf.bij_of_top R M _ (SecSHPf.top_of_sect h A hA)

end LateralTheory.KummerTheory
end
end
