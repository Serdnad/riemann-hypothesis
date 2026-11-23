module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle348
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

section

noncomputable section

open CategoryTheory

namespace GlobalTheory

namespace PDivGroup

theorem exists_algHom_pi_eq_eval {O ι : Type*} [CommRing O] [Nontrivial O] [Finite ι]
    (hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1) (f : (ι → O) →ₐ[O] O) :
    ∃ k, ∀ g, f g = g k := by
  classical
  have := Fintype.ofFinite ι
  have h1 : ∃ k, f (Pi.single k 1) ≠ 0 := by
    by_contra h
    have h' : ∀ k, f (Pi.single k 1) = 0 := fun k => by_contra fun hk => h ⟨k, hk⟩
    have h2 : f (∑ k, Pi.single k 1) = 0 := by

      rw [map_sum]
      exact Finset.sum_eq_zero fun k _ => h' k
    have h3 : (∑ k, Pi.single k 1 : ι → O) = 1 := Finset.univ_sum_single (1 : ι → O)
    rw [h3, map_one] at h2
    exact one_ne_zero h2
  obtain ⟨k, hk⟩ := h1
  have hi : IsIdempotentElem (Pi.single k 1 : ι → O) := by
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  have h4 : f (Pi.single k 1) = 1 := (hO _ (hi.map f)).resolve_left hk
  refine ⟨k, fun g => ?_⟩
  have h5 : g * Pi.single k 1 = g k • (Pi.single k 1 : ι → O) := by
    funext j
    by_cases hj : j = k
    · subst hj; simp
    · simp [hj]
  have h6 := congrArg f h5
  rwa [map_mul, map_smul, h4, mul_one, smul_eq_mul, mul_one] at h6

variable (p : ℕ) (O : Type) [CommRing O] [Fact p.Prime]

variable [Nontrivial O]

theorem toSpanSingleton_constGen_surjective
    (hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Function.Surjective (LinearMap.toSpanSingleton ℤ_[p] _ (constGen p O)) := fun t => by
  have h1 : ∀ n, ∃ k : ℕ, ∀ φ, t.pt n φ = constFun p O n φ k := fun n => by
    obtain ⟨k, hk⟩ := exists_algHom_pi_eq_eval hO
      ((t.pt n).comp ((constFun p O n).symm : (ZMod (p ^ n) → O) →ₐ[O] (const p O).A n))
    refine ⟨k.val, fun φ => ?_⟩
    rw [ZMod.natCast_zmod_val, ← hk (constFun p O n φ)]
    exact congrArg (t.pt n) ((constFun p O n).symm_apply_apply φ).symm
  choose k hk using h1
  have h2 : ∀ n, ((k (n + 1) : ℕ) : ZMod (p ^ n)) = k n := fun n => by
    have h := t.pt_mulP n ((constFun p O n).symm (Pi.single (k n : ZMod (p ^ n)) 1))
    rw [hk, hk, constFun_mulP, AlgEquiv.apply_symm_apply, Pi.single_eq_same] at h
    by_contra hne
    rw [Pi.single_eq_of_ne hne] at h
    exact zero_ne_one h
  have h3 : ∀ n, (p : ℤ) ^ n ∣ (k (n + 1) : ℤ) - k n := fun n => by
    rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast,
      Int.cast_natCast, h2, sub_self]
  refine ⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => (k n : ℤ)) p h3),
    TateOver.ext (funext fun n => AlgHom.ext fun φ => ?_)⟩
  rw [LinearMap.toSpanSingleton_apply, smul_constGen_pt,
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (k n : ℤ)) p h3 n, Int.cast_natCast, hk]

theorem toSpanSingleton_constGen_bijective
    (hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Function.Bijective (LinearMap.toSpanSingleton ℤ_[p] _ (constGen p O)) :=
  ⟨toSpanSingleton_constGen_injective p O, toSpanSingleton_constGen_surjective p O hO⟩

end PDivGroup

end GlobalTheory
end
end

section

noncomputable section

open Coalgebra Bialgebra WithConv

namespace GlobalTheory

namespace PDiv

variable {R A C D : Type*} [CommRing R] [CommRing A] [CommRing C] [CommRing D]
  [Bialgebra R A] [Bialgebra R C] [Bialgebra R D]

theorem cotMap_surjective {f : C →ₐc[R] A} (hf : Function.Surjective f) :
    Function.Surjective (cotMap f) :=
  AugCot.map_surjective _ _ hf

theorem dUnit_mem_range_of_mem_kerIdeal (g : D →ₐc[R] C) {c : C} (hc : c ∈ kerIdeal g) :
    dUnit (R := R) c ∈ LinearMap.range (cotMap g) := by
  suffices h : counitAlgHom R C c = 0 ∧ dUnit (R := R) c ∈ LinearMap.range (cotMap g) from h.2
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨?_, dUnit (R := R) a, cotMap_d g a⟩
    have ha' : counit (R := R) a = 0 := ha
    simpa using ha'
  | zero => exact ⟨map_zero _, by rw [dUnit, map_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    exact ⟨by rw [map_add (f := _), hx.1, hy.1, add_zero], by rw [dUnit, map_add (f := _)]; exact add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    refine ⟨by rw [smul_eq_mul, map_mul, hx.1, mul_zero], ?_⟩
    rw [smul_eq_mul, dUnit, AugCot.d_mul, hx.1, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ hx.2

theorem exact_cotMap {f : C →ₐc[R] A} (hf : Function.Surjective f) (g : D →ₐc[R] C)
    (hk : RingHom.ker f = kerIdeal g) : Function.Exact (cotMap g) (cotMap f) := by
  intro w
  constructor
  · intro hw
    obtain ⟨x, rfl⟩ := (AugCot.exact_kerMap_map (f : C →ₐ[R] A)
      (BialgHomClass.counitAlgHom_comp f) hf w).1 hw
    obtain ⟨v, hv⟩ := dUnit_mem_range_of_mem_kerIdeal g (hk.le x.2)
    exact ⟨v, hv.trans (AugCot.kerMap_apply _ _ x).symm⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨a, rfl⟩ := AugCot.d_surjective _ v
    rw [cotMap_d, cotMap_d]
    have h := (kerIdeal_le_ker_iff g (f : C →ₐ[R] A)).1 hk.ge a
    exact (congrArg (dUnit (R := R)) h).trans (AugCot.d_algebraMap _ _)

theorem cotMap_mulBy [IsCocomm R C] (m : ℕ) (w : Cot (R := R) (A := C)) :
    cotMap (mulBy (R := R) (A := C) m) w = (m : R) • w := by
  rw [mulBy, cotMap_pow, ofConv_toConv, cotMap_id, Nat.cast_smul_eq_nsmul]
  rfl

theorem cotMap_eq_zero_iff [IsCocomm R C] {f : C →ₐc[R] A} (hf : Function.Surjective f) {m : ℕ}
    (hk : RingHom.ker f = torsionIdeal (R := R) (A := C) m) (w : Cot (R := R) (A := C)) :
    cotMap f w = 0 ↔ ∃ v : Cot (R := R) (A := C), w = (m : R) • v := by
  rw [exact_cotMap hf _ hk w]
  exact exists_congr fun v => by rw [cotMap_mulBy, eq_comm]

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)

theorem cotMap_res_surjective (n : ℕ) : Function.Surjective (cotMap (G.res n)) :=
  cotMap_surjective (G.res_surjective n)

theorem cotMap_res_eq_zero_iff (n : ℕ) (w : Cot (R := O) (A := G.A (n + 1))) :
    cotMap (G.res n) w = 0 ↔ ∃ v, w = (p : O) ^ n • v := by
  rw [cotMap_eq_zero_iff (G.res_surjective n) (G.ker_res n), Nat.cast_pow]

def omegaLevel (n : ℕ) : G.omega →ₗ[O] Cot (R := O) (A := G.A n) :=
  LinearMap.proj n ∘ₗ G.omegaSub.subtype

@[simp] theorem omegaLevel_apply (n : ℕ) (w : G.omega) : G.omegaLevel n w = w.1 n := rfl

@[simp] theorem cotMap_res_omega (n : ℕ) (w : G.omega) :
    cotMap (G.res n) (w.1 (n + 1)) = w.1 n := w.2 n

theorem omega_val_eq_zero_of_le {m n : ℕ} (h : m ≤ n) {w : G.omega} (hw : w.1 n = 0) :
    w.1 m = 0 := by
  induction n, h using Nat.le_induction with
  | base => exact hw
  | succ n _ ih => exact ih (by rw [← w.2 n, hw, map_zero])

theorem cot_zero_eq_zero (w : Cot (R := O) (A := G.A 0)) : w = 0 := by
  simpa using G.pow_smul_cot 0 w

theorem omegaLevel_surjective (n : ℕ) : Function.Surjective (G.omegaLevel n) := by
  have hsec := fun k => (G.cotMap_res_surjective k).hasRightInverse
  choose s hs using hsec

  have key : ∀ (n : ℕ) (x : Cot (R := O) (A := G.A (n + 1))), cotMap (G.res n) x = 0 →
      ∃ w : G.omega, w.1 (n + 1) = x := by
    intro n x hx
    let u : ∀ k, Cot (R := O) (A := G.A k) := fun k =>
      if h : n + 1 ≤ k then Nat.leRecOn h (fun {k} => s k) x else 0
    refine ⟨⟨u, fun k => ?_⟩, by simp [u, Nat.leRecOn_self]⟩
    rcases lt_trichotomy k n with hk | rfl | hk
    · simp only [u]
      rw [dite_eq_right (by omega), dite_eq_right (by omega), map_zero]
    · simp only [u]
      rw [dite_eq_left le_rfl, dite_eq_right (by omega), Nat.leRecOn_self, hx]
    · simp only [u]
      rw [dite_eq_left (by omega), dite_eq_left (show n + 1 ≤ k from hk), Nat.leRecOn_succ (show n + 1 ≤ k from hk)]
      exact hs k _
  induction n with
  | zero => exact fun x => ⟨0, (G.cot_zero_eq_zero _).trans (G.cot_zero_eq_zero _).symm⟩
  | succ n ih =>
    intro x
    obtain ⟨v, hv⟩ := ih (cotMap (G.res n) x)
    obtain ⟨w, hw⟩ := key n (x - v.1 (n + 1)) (by rw [map_sub, v.2 n, ← hv]; exact sub_self _)
    refine ⟨w + v, ?_⟩
    rw [map_add (f := _), omegaLevel_apply, omegaLevel_apply, hw, sub_add_cancel]

theorem exists_sub_pow_smul_val_succ (n : ℕ) (w : G.omega) (hw : w.1 n = 0) :
    ∃ v : G.omega, (w - (p : O) ^ n • v).1 (n + 1) = 0 := by
  obtain ⟨x, hx⟩ := (G.cotMap_res_eq_zero_iff n (w.1 (n + 1))).1 ((w.2 n).trans hw)
  obtain ⟨v, rfl⟩ := G.omegaLevel_surjective (n + 1) x
  refine ⟨v, ?_⟩
  change w.1 (n + 1) - (p : O) ^ n • v.1 (n + 1) = 0
  rw [hx, omegaLevel_apply, sub_self]

theorem omega_val_eq_zero_iff (n : ℕ) (w : G.omega) :
    w.1 n = 0 ↔ ∃ v : G.omega, w = (p : O) ^ n • v := by
  refine ⟨fun hw => ?_, ?_⟩
  swap
  · rintro ⟨v, rfl⟩
    exact G.pow_smul_cot n (v.1 n)
  choose! c hc using G.exists_sub_pow_smul_val_succ
  let r : ℕ → G.omega := fun j => Nat.rec w (fun j x => x - (p : O) ^ (n + j) • c (n + j) x) j
  have hr : ∀ j, (r j).1 (n + j) = 0 := fun j => by
    induction j with
    | zero => exact hw
    | succ j ih => exact hc _ _ ih
  let t : ℕ → G.omega := fun k => ∑ j ∈ Finset.range k, (p : O) ^ j • c (n + j) (r j)
  have ht : ∀ k, w = r k + (p : O) ^ n • t k := fun k => by
    induction k with
    | zero => simp [t, r]
    | succ k ih =>
      have h1 : r (k + 1) = r k - (p : O) ^ (n + k) • c (n + k) (r k) := rfl
      have h2 : t (k + 1) = t k + (p : O) ^ k • c (n + k) (r k) := Finset.sum_range_succ _ _
      rw [h1, h2, smul_add, smul_smul, ← pow_add]
      exact ih.trans (by abel)
  refine ⟨⟨fun k => (t k).1 k, fun k => ?_⟩, Subtype.ext (funext fun k => ?_)⟩
  · have h2 : t (k + 1) = t k + (p : O) ^ k • c (n + k) (r k) := Finset.sum_range_succ _ _
    rw [(t (k + 1)).2 k, h2]
    change (t k).1 k + (p : O) ^ k • (c (n + k) (r k)).1 k = _
    rw [pow_smul_cot, add_zero]
  · have h := congrArg (fun x : G.omega => x.1 k) (ht k)
    refine h.trans ?_
    change (r k).1 k + (p : O) ^ n • (t k).1 k = (p : O) ^ n • (t k).1 k
    rw [G.omega_val_eq_zero_of_le (Nat.le_add_left k n) (hr k), zero_add]

theorem ker_omegaLevel (n : ℕ) :
    LinearMap.ker (G.omegaLevel n) = Ideal.span {(p : O)} ^ n • (⊤ : Submodule O G.omega) := by
  ext w
  rw [LinearMap.mem_ker, omegaLevel_apply, omega_val_eq_zero_iff, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact exists_congr fun v => by simp [eq_comm]

def omegaQuotEquiv (n : ℕ) :
    (G.omega ⧸ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O G.omega)) ≃ₗ[O] Cot (R := O) (A := G.A n) :=
  Submodule.quotEquivOfEq _ _ (G.ker_omegaLevel n).symm ≪≫ₗ
    (G.omegaLevel n).quotKerEquivOfSurjective (G.omegaLevel_surjective n)

@[simp] theorem omegaQuotEquiv_mk (n : ℕ) (w : G.omega) :
    G.omegaQuotEquiv n (Submodule.Quotient.mk w) = w.1 n := rfl

theorem omega_smodEq_iff (n : ℕ) (v w : G.omega) :
    v ≡ w [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O G.omega)] ↔ v.1 n = w.1 n := by
  rw [SModEq.sub_mem, ← ker_omegaLevel, LinearMap.mem_ker, map_sub, sub_eq_zero]
  rfl

instance isAdicComplete_omega : IsAdicComplete (Ideal.span {(p : O)}) G.omega where
  haus' w hw := Subtype.ext (funext fun n => (G.omega_smodEq_iff n w 0).1 (hw n))
  prec' f hf := by
    refine ⟨⟨fun k => (f k).1 k, fun k => ?_⟩, fun n => (G.omega_smodEq_iff n _ _).2 rfl⟩
    rw [(f (k + 1)).2 k]
    exact ((G.omega_smodEq_iff k _ _).1 (hf (Nat.le_succ k))).symm

end PDivGroup

end GlobalTheory
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

noncomputable section

namespace GlobalTheory.PDivGroup

variable {p : ℕ} {k : Type} [CommRing k]

def liftClosed {K G H : PDivGroup p k} (i : K ⟶ G) (hi : ∀ n : ℕ, Function.Surjective (i.app n))
    (f : H ⟶ G) (hf : ∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) : H ⟶ K :=
  ⟨fun n => liftSurj (i.app n) (hi n) (f.app n) (hf n), fun n => BialgHom.ext fun b => by
    obtain ⟨a, rfl⟩ := hi (n + 1) b
    change H.res n (liftSurj (i.app (n + 1)) (hi (n + 1)) (f.app (n + 1)) (hf (n + 1))
        (i.app (n + 1) a)) =
      liftSurj (i.app n) (hi n) (f.app n) (hf n) (K.res n (i.app (n + 1) a))
    rw [liftSurj_apply, res_app, res_app, liftSurj_apply]⟩

theorem liftClosed_comp {K G H : PDivGroup p k} (i : K ⟶ G)
    (hi : ∀ n : ℕ, Function.Surjective (i.app n)) (f : H ⟶ G)
    (hf : ∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) :
    liftClosed i hi f hf ≫ i = f :=
  Hom.ext (funext fun n => BialgHom.ext fun a => liftSurj_apply (i.app n) (hi n) (f.app n) (hf n) a)

theorem cancel_closed {K G H : PDivGroup p k} (i : K ⟶ G)
    (hi : ∀ n : ℕ, Function.Surjective (i.app n)) (g g' : H ⟶ K) (h : g ≫ i = g' ≫ i) :
    g = g' :=
  Hom.ext (funext fun n => BialgHom.ext fun b => by
    obtain ⟨a, rfl⟩ := hi n b
    have := DFunLike.congr_fun (congrArg (fun u : H ⟶ G => u.app n) h) a
    simpa using this)

end GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.factor_closedImmersion : ∀ (p : ℕ) (k : Type) [CommRing k] (K G : PDivGroup p k) (i : K ⟶ G), (∀ n : ℕ, Function.Surjective (i.app n)) → (∀ (H : PDivGroup p k) (f : H ⟶ G), (∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) → ∃ g : H ⟶ K, g ≫ i = f) ∧ ∀ (H : PDivGroup p k) (g g' : H ⟶ K), g ≫ i = g' ≫ i → g = g' :=
  fun _ _ _ _ _ i hi => ⟨fun _ f hf => ⟨liftClosed i hi f hf, liftClosed_comp i hi f hf⟩,
    fun _ g g' h => cancel_closed i hi g g' h⟩
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

theorem ker_app_eq_kerIdeal_of_idempotents (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]
    (G : PDivGroup p k) (u v : G ⟶ G) (huv : u + v = 𝟙 G) (h1 : u ≫ v = 0) (_h2 : v ≫ u = 0)
    (n : ℕ) : RingHom.ker (u.app n) = kerIdeal (v.app n) := by
  apply le_antisymm
  · intro a ha
    rw [RingHom.mem_ker] at ha
    let x := Ideal.Quotient.mkₐ k (kerIdeal (v.app n))
    have hv : ∀ c, x (v.app n c) = algebraMap k _ (counit c) :=
      (kerIdeal_le_ker_iff (v.app n) x).1 fun b hb => by
        rw [RingHom.mem_ker]
        exact Ideal.Quotient.eq_zero_iff_mem.2 hb
    let P := (ptsPush (G.A n) (x : G.A n →ₐ[k] _)).comp toPts
    have hP : P (Hom.conv v n) = 1 := WithConv.ofConv_injective (AlgHom.ext fun c => by
      change x (v.app n c) = _
      rw [hv]
      simp)
    have e : P (Hom.conv (u + v) n) = P (Hom.conv u n) := by
      rw [add_conv, map_mul, hP, mul_one]
    rw [huv] at e
    have e' := congrArg (fun y => y.ofConv a) e
    change x a = x (u.app n a) at e'
    rw [ha, map_zero] at e'
    exact Ideal.Quotient.eq_zero_iff_mem.1 e'
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e := congrArg (fun f : G ⟶ G => Hom.app f n b) h1
    change u.app n (v.app n b) = (1 : WithConv (G.A n →ₐc[k] G.A n)).ofConv b at e
    have hb' : counit (R := k) b = 0 := hb
    refine Eq.trans e ?_
    simp [hb']

end PDivGroup

end GlobalTheory
end
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.differentialOperatorDepth_integral_coordinates : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C) (Φ Ψ : Fin d → MvPowerSeries (Fin d) C), (∀ a, MvIsInt v (Φ a) ∧ constantCoeff (Φ a) = 0 ∧ MvIsInt v (Ψ a) ∧ constantCoeff (Ψ a) = 0) → (∀ a, subst Ψ (Φ a) = X a ∧ subst Φ (Ψ a) = X a) → ∀ (t : Fin d → MvPowerSeries (Fin i) C), (∀ a, constantCoeff (t a) = 0) → (∀ e, subst t (subst Φ (G.lg e)) = ∑ a, u a e • X a) → detDepth G u c = ⨅ f : {f : MvPowerSeries (Σ _ : Fin i, Fin d) C // MvIsInt v f}, toE (v (derivAt0 (detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) f.1))) := by
  first | exact @GlobalTheory.FGDepth.Coord.depth_in_coords | exact GlobalTheory.FGDepth.Coord.depth_in_coords | (intros; apply GlobalTheory.FGDepth.Coord.depth_in_coords <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.formalGroupExp_twoSided_inverse_unique : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : LogFGL v d), IsExp G (expOf G) ∧ (∀ a, subst G.lg (expOf G a) = X a) ∧ ∀ ex, IsExp G ex → ex = expOf G := by
  first | exact @GlobalTheory.FGDepth.expOf_twoSided_unique | exact GlobalTheory.FGDepth.expOf_twoSided_unique | (intros; apply GlobalTheory.FGDepth.expOf_twoSided_unique <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape : ∀ (C : Type) [Field C] [CharZero C] (i c : ℕ), (detPow C i c).IsHomogeneous (i * c) ∧ (∀ α, ∃ n : ℤ, (detPow C i c).coeff α = n) ∧ (detPow C i c).coeff (∑ a : Fin i, Finsupp.single ⟨a, a⟩ c) = 1 ∧ ∀ α ∈ (detPow C i c).support, (∀ a : Fin i, ∑ b : Fin i, α ⟨b, a⟩ = c) ∧ (∀ b : Fin i, ∑ a : Fin i, α ⟨b, a⟩ = c) := by
  first | exact @GlobalTheory.DetPowShape.detPow_shape | exact GlobalTheory.DetPowShape.detPow_shape | (intros; apply GlobalTheory.DetPowShape.detPow_shape <;> assumption)
end

section

open ValuativeRel Matrix


theorem _root_.GlobalTheory.T.rank_deficient_integral_row_reduction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (X : Matrix A D k), X.rank < Fintype.card A → ∃ g ∈ GlobalTheory.SplitWeil.KO k A, ∃ i₀ : A, ∀ j, (g.val * X) i₀ j = 0 := by
  first | exact @GlobalTheory.RankCoinv.exists_KO_row_zero_of_rank_lt | exact GlobalTheory.RankCoinv.exists_KO_row_zero_of_rank_lt | (intros; apply GlobalTheory.RankCoinv.exists_KO_row_zero_of_rank_lt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_hom_of_fieldPoint_relation_proper : ∀ (Q P S : Scheme.{0}) (q : Q ⟶ S) (p : P ⟶ S) [IsProper p] [IsNoetherian Q] [GlobalTheory.IsNormalScheme Q] (R : ∀ (K : Type) [Field K], (Sp K ⟶ Q) → (Sp K ⟶ P) → Prop), (∀ (K : Type) [Field K] (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → z ≫ q = w ≫ p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ Q), ∃! w, R K z w) → (∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → R K' (spMap ι ≫ z) (spMap ι ≫ w)) → (∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ Q) (v : Sp A ⟶ P), u ≫ q = v ≫ p → R (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ u) (spMap (algebraMap A (FractionRing A)) ≫ v) → R (IsLocalRing.ResidueField A) (spMap (IsLocalRing.residue A) ≫ u) (spMap (IsLocalRing.residue A) ≫ v)) → ∃ h : Q ⟶ P, h ≫ p = q ∧ ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), R K z (z ≫ h) := by
  first | exact @GlobalTheory.FieldPointGraph.exists_hom_of_rel | exact GlobalTheory.FieldPointGraph.exists_hom_of_rel | (intros; apply GlobalTheory.FieldPointGraph.exists_hom_of_rel <;> assumption)
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem _root_.GlobalTheory.T.siegelGaussian_pair_standardGaussian : ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (c : ℂ), GlobalTheory.IsSiegel τ → (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (1 - I • τ).det = c ^ 2 := by
  first | exact @GlobalTheory.siegelGauss_pair_standard | exact GlobalTheory.siegelGauss_pair_standard | (intros; apply GlobalTheory.siegelGauss_pair_standard <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

namespace GlobalTheory.CechOne

theorem isLimit_cone_one (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (0 + 1) => GlobalTheory.CechOne.fB A B)
      (GlobalTheory.CechOne.fB A B) (fun _ => 𝟙 _) (fun _ => Category.id_comp _))) := by
  refine ⟨WidePullbackCone.IsLimit.mk _ (fun t => t.π 0) ?_ ?_ ?_⟩
  · intro t
    rw [WidePullbackCone.mk_base]
    exact t.condition 0
  · intro t i
    rw [WidePullbackCone.mk_π]
    exact (Category.comp_id (t.π 0)).trans (congrArg t.π (Fin.fin_one_eq_zero i).symm)
  · intro t m _ hπ
    have := hπ 0
    rw [WidePullbackCone.mk_π] at this
    exact (Category.comp_id m).symm.trans this

end GlobalTheory.CechOne
end
