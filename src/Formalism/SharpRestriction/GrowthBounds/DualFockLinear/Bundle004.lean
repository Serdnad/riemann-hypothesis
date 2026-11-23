module

public import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.MemNablaLTwLetter
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle003
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GroupLattices.FockModels.MkP

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.L2.G.Model

section Gen

variable {S : Type} [Fintype S] [DecidableEq S]

theorem tr_bA_emb (K : Type) [CommRing K] {k n : ℕ} (g : S → Matrix (Fin k) (Fin k) K) (s : S)
    (F : MvPolynomial (Fin k × Fin n) K) : blockAct K g (blockEmb K s F) = blockEmb K s (rowAct K (g s) F) :=
  (blockActTensor K K S k n g).1 s F

theorem tr_prod_smul (K : Type) [CommRing K] {k n : ℕ} (c : S → K) (F : S → MvPolynomial (Fin k × Fin n) K) :
    (∏ s, c s) • ∏ s, blockEmb K s (F s) = ∏ s, blockEmb K s (c s • F s) := by
  rw [smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_smul, smul_eq_C_mul]

theorem tr_map_emb {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {k n : ℕ} (s : S)
    (P : MvPolynomial (Fin k × Fin n) R) : map f (blockEmb R s P) = blockEmb R' s (map f P) := by
  unfold blockEmb
  exact map_rename f _ P

theorem map_letter_substitution {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (m : ℕ) (vec : S → Bool)
    (P : MvPolynomial (S × Fin (m + 1)) R) : map f (Th0 R m vec P) = Th0 R' m vec (map f P) := by
  have key : (map f).comp (Th0 R m vec).toRingHom = (Th0 R' m vec).toRingHom.comp (map f) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Th0]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_X, Th0, aeval_X]
      rw [tr_map_emb, map_Nv]
  exact RingHom.congr_fun key P

theorem tr_rowAct_inv (K : Type) [Field K] {k n : ℕ} (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det)
    (x : MvPolynomial (Fin k × Fin n) K) : rowAct K g (rowAct K g⁻¹ x) = x := by
  have := congrArg (fun f => f x) (rowActMul K k n g g⁻¹)
  simp only [AlgHom.comp_apply] at this
  rw [this, Matrix.nonsing_inv_mul g hg, fl_rowAct_one]

theorem tr_multi_twist (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) (vec : S → Bool) (d : S → ℕ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hM : ∀ s, IsUnit (M s).det)
    (G : MvPolynomial (S × Fin (m + 1)) K) (hG : G ∈ Pol K (m + 1) d) :
    (∏ s, (M s).det ^ (letterWt m (d s) (vec s) (Fin.last m))) • blockAct K M (Th0 K m vec G) =
      Th0 K m vec (Lin (fun s => Aa (vec s) (M s)) G) := by
  unfold Formalism.MainNotions.G.Pol at hG
  rw [restrictSupport_eq_span] at hG
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, hμ, rfl⟩ := hx
    beta_reduce
    rw [mono_factor, map_prod, map_prod, map_prod, map_prod]
    simp only [Th0_emb, Lin_emb, tr_bA_emb]
    rw [tr_prod_smul]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [twist_theta K m hm (d s) (vec s) (M s) (hM s) _ (partS_Hd K d μ hμ s)]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | smul a x _ hx => simp only [map_smul]; rw [smul_comm, hx]

theorem tr_tens_int (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : S → Fin (m + 1) → ℤ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (y : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf)
    (hy : y ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lam s) (M s))) :
    ∃ R : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) O,
      (∏ s, (M s).det ^ (lam s (Fin.last m))) • blockAct Kf M y = map (algebraMap O Kf) R := by
  unfold tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    have h1 := fun s => (nablaLTwMem O Kf m (lam s) (M s) (hM s) (F s)).1 (hF s)
    choose G _ hG2 using h1
    refine ⟨∏ s, blockEmb O s (G s), ?_⟩
    rw [map_prod, map_prod]
    simp only [tr_bA_emb]
    rw [tr_prod_smul]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [tr_map_emb, ← hG2 s]
    rfl
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨R1, h1⟩ := hx
    obtain ⟨R2, h2⟩ := hy
    exact ⟨R1 + R2, by rw [map_add (f := _), smul_add, h1, h2, map_add (f := _)]⟩
  | smul a x _ hx =>
    obtain ⟨R1, h1⟩ := hx
    refine ⟨a • R1, ?_⟩
    rw [fl_map_smul, ← h1, ← algebraMap_smul Kf a x, map_smul, smul_comm, algebraMap_smul]

theorem tr_tens_lift (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : S → Fin (m + 1) → ℤ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (sO : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) O)
    (h : sO ∈ tensorLat O O (fun s => dualWeyl O (m + 1) (m + 1) (nuOf (lam s)))) :
    ∃ y ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lam s) (M s)),
      (∏ s, (M s).det ^ (lam s (Fin.last m))) • blockAct Kf M y = map (algebraMap O Kf) sO := by
  unfold tensorLat at h
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨G, hG, rfl⟩ := hx
    have key : ∀ s, (M s).det ^ (lam s (Fin.last m)) • rowAct Kf (M s)
        (((M s).det ^ (lam s (Fin.last m)))⁻¹ • rowAct Kf (M s)⁻¹ (map (algebraMap O Kf) (G s))) =
        map (algebraMap O Kf) (G s) := by
      intro s
      rw [map_smul, smul_smul, mul_inv_cancel₀ (zpow_ne_zero _ (hM s).ne_zero), one_smul, tr_rowAct_inv _ _ (hM s)]
    refine ⟨∏ s, blockEmb Kf s (((M s).det ^ (lam s (Fin.last m)))⁻¹ •
      rowAct Kf (M s)⁻¹ (map (algebraMap O Kf) (G s))), ?_, ?_⟩
    · apply Submodule.subset_span
      refine ⟨_, fun s => ?_, rfl⟩
      rw [nablaLTwMem O Kf m (lam s) (M s) (hM s), key s]
      exact ⟨G s, hG s, rfl⟩
    · rw [map_prod, map_prod]
      simp only [tr_bA_emb]
      rw [tr_prod_smul]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [tr_map_emb, key s]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨y1, m1, h1⟩ := hx
    obtain ⟨y2, m2, h2⟩ := hy
    exact ⟨y1 + y2, Submodule.add_mem _ m1 m2, by rw [map_add (f := _), smul_add, h1, h2, map_add (f := _)]⟩
  | smul a x _ hx =>
    obtain ⟨y1, m1, h1⟩ := hx
    refine ⟨a • y1, Submodule.smul_mem _ _ m1, ?_⟩
    rw [fl_map_smul, ← h1, ← algebraMap_smul Kf a y1, map_smul, smul_comm, algebraMap_smul]

theorem tr_tens_le (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : S → Fin (m + 1) → ℤ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (y : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf)
    (hy : y ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lam s) (M s))) :
    y ∈ tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lam s))) := by
  unfold tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨F, fun s => ?_, rfl⟩
    obtain ⟨x, hx, hxF⟩ := hF s
    rw [← hxF]
    exact Submodule.smul_mem _ _ (nablaLLe O Kf (m + 1) (m + 1) _ (M s) (hM s) x hx)
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul Kf a x]
    exact Submodule.smul_mem _ _ hx

end Gen

end Formalism.MainNotions.TestSideCounting
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model.TS (fockR)

theorem RE_X (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (v : Fin k × Fin k) :
    RE K k a b (X v) = if v.1 = b then X (a, v.2) else 0 := by
  unfold RE
  simp only [pderiv_X]
  by_cases h : v.1 = b
  · rw [if_pos h, Finset.sum_eq_single v.2]
    · have : ((b, v.2) : Fin k × Fin k) = v := Prod.ext h.symm rfl
      rw [this, Pi.single_eq_same, mul_one]
    · intro t _ ht
      rw [Pi.single_eq_of_ne, mul_zero]
      intro hv
      apply ht
      rw [hv]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro t _
    rw [Pi.single_eq_of_ne, mul_zero]
    intro hv
    apply h
    rw [hv]

theorem RE_C (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (r : K) : RE K k a b (C r) = 0 := by
  unfold RE
  simp

theorem rowGen_coeff_zero (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) :
    (rowGen K a b f).coeff 0 = f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add (f := _), Polynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp

theorem RE_eq_rowDiv (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b f = rowDiv K a b 1 f := by
  unfold rowDiv
  induction f using MvPolynomial.induction_on with
  | C r => rw [RE_C]; simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, Polynomial.coeff_C]
  | add p q hp hq => rw [RE_add, map_add (f := _), Polynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    rw [RE_mul, map_mul, Polynomial.mul_coeff_one, rowGen_coeff_zero, rowGen_coeff_zero, hp, RE_X]
    have : (rowGen K a b (X v)).coeff 1 = if v.1 = b then X (a, v.2) else 0 := by
      simp only [rowGen, aeval_X]
      split_ifs <;> simp [Polynomial.coeff_C]
    rw [this]
    ring

theorem restAdj : RestAdj := by
  intro K _ k a b P Q
  rw [RE_eq_rowDiv, RE_eq_rowDiv]
  exact Formalism.L2.G.Model.TS.Top.fockRRowDivAdj K k k a b 1 P Q

theorem restStab : RestStab := by
  intro K _ _ k ν a b P hP
  rw [RE_eq_rowDiv]
  exact rowDivStable K k k ν a b 1 P hP

end Formalism.MainNotions.TestSideCounting
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (theta Hd nuL)
open Formalism.L2.G.Model.TS (fockR)

section F

variable {τ K : Type} [CommRing K]

theorem fR_symm (f g : MvPolynomial τ K) : fockR f g = fockR g f := (Formalism.L2.G.Model.TS.Top.fockRBilin τ K f 0 g 0).2.2
theorem fR_add_left (f f' g : MvPolynomial τ K) : fockR (f + f') g = fockR f g + fockR f' g :=
  (Formalism.L2.G.Model.TS.Top.fockRBilin τ K f f' g 0).1
theorem fR_smul_left (a : K) (f g : MvPolynomial τ K) : fockR (a • f) g = a * fockR f g :=
  (Formalism.L2.G.Model.TS.Top.fockRBilin τ K f 0 g a).2.1
theorem fR_add_right (f g g' : MvPolynomial τ K) : fockR f (g + g') = fockR f g + fockR f g' := by
  rw [fR_symm, fR_add_left, fR_symm g, fR_symm g']
theorem fR_smul_right (a : K) (f g : MvPolynomial τ K) : fockR f (a • g) = a * fockR f g := by
  rw [fR_symm, fR_smul_left, fR_symm g]
theorem fR_neg_left (f g : MvPolynomial τ K) : fockR (-f) g = -fockR f g := by
  have := fR_smul_left (-1 : K) f g
  simpa using this
theorem fR_sub_left (f f' g : MvPolynomial τ K) : fockR (f - f') g = fockR f g - fockR f' g := by
  rw [sub_eq_add_neg, fR_add_left, fR_neg_left, ← sub_eq_add_neg]
theorem fR_sub_right (f g g' : MvPolynomial τ K) : fockR f (g - g') = fockR f g - fockR f g' := by
  rw [fR_symm, fR_sub_left, fR_symm g, fR_symm g']

end F

abbrev VV (K : Type) [Field K] (m d : ℕ) := ↥(homogeneousSubmodule (Fin (m + 1)) K d)

def thV (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) : VV K m d →ₗ[K] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  (theta K m vec).toLinearMap ∘ₗ (homogeneousSubmodule (Fin (m + 1)) K d).subtype

def RestRep2 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (m : ℕ), 1 ≤ m → ∀ (vec : Bool) (d : ℕ) (f : Module.Dual K (VV K m d)),
    ∃ P : VV K m d, ∀ Q, fockR (thV K m vec d P) (thV K m vec d Q) = f Q

def cForm (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (β s : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    VV K m d →ₗ[K] Module.Dual K (VV K m d) :=
  LinearMap.mk₂ K (fun P Q => fockR (thV K m vec d P * s) (thV K m vec d Q * β))
    (fun P P' Q => by rw [map_add (f := _), add_mul, fR_add_left])
    (fun t P Q => by rw [map_smul, smul_mul_assoc, fR_smul_left, smul_eq_mul])
    (fun P Q Q' => by rw [map_add (f := _), add_mul, fR_add_right])
    (fun t P Q => by rw [map_smul, smul_mul_assoc, fR_smul_right, smul_eq_mul])

theorem cForm_apply (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (β s : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
    (P Q : VV K m d) : cForm K m vec d β s P Q = fockR (thV K m vec d P * s) (thV K m vec d Q * β) := rfl

theorem uniqV (hR : RestRep) {K : Type} [Field K] [CharZero K] {m : ℕ} (hm : 1 ≤ m) (vec : Bool) (d : ℕ) (P : VV K m d)
    (h : ∀ Q, fockR (thV K m vec d P) (thV K m vec d Q) = 0) : P = 0 := by
  apply Subtype.ext
  exact hR K m hm vec d P.1 ((mem_Hd_iff _).2 P.2) fun Q hQ => h ⟨Q, (mem_Hd_iff _).1 hQ⟩

theorem exists_A (hR : RestRep) (hR2 : RestRep2) {K : Type} [Field K] [CharZero K] {m : ℕ} (hm : 1 ≤ m) (vec : Bool) (d : ℕ) :
    ∃ A : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K → Module.End K (VV K m d),
      ∀ β s P Q, fockR (thV K m vec d (A β s P)) (thV K m vec d Q) = fockR (thV K m vec d P * s) (thV K m vec d Q * β) := by
  have hb : Function.Bijective (cForm K m vec d 1 1) := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro P hP
      apply uniqV hR hm vec d P
      intro Q
      have := congrArg (fun f => f Q) hP
      simpa [cForm] using this
    · intro f
      obtain ⟨P, hP⟩ := hR2 K m hm vec d f
      refine ⟨P, LinearMap.ext fun Q => ?_⟩
      simpa [cForm] using hP Q
  let e := LinearEquiv.ofBijective (cForm K m vec d 1 1) hb
  refine ⟨fun β s => e.symm.toLinearMap ∘ₗ cForm K m vec d β s, fun β s P Q => ?_⟩
  have h1 : cForm K m vec d 1 1 (e.symm (cForm K m vec d β s P)) = cForm K m vec d β s P := e.apply_symm_apply _
  have h2 : cForm K m vec d 1 1 (e.symm (cForm K m vec d β s P)) Q = cForm K m vec d β s P Q := by rw [h1]
  rw [cForm_apply, cForm_apply, mul_one, mul_one] at h2
  exact h2

end Formalism.MainNotions.TestSideCounting
end
end
