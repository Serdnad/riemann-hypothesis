module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle083
public import Mathlib.RingTheory.Flat.TorsionFree
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle731
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

theorem mem_augIdeal_map {k A B : Type} [CommRing k] [CommRing A] [CommRing B] [Bialgebra k A]
    [Bialgebra k B] (f : A →ₐc[k] B) {a : A} (ha : a ∈ augIdeal k A) : f a ∈ augIdeal k B := by
  have ha' : counit (R := k) a = 0 := ha
  change counit (R := k) (f a) = 0
  rw [CoalgHomClass.counit_comp_apply, ha']

theorem isNilpotent_of_map_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) {a : A} (h : IsNilpotent (f a)) : IsNilpotent a := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, hf (by rw [map_pow, hN, map_zero])⟩

theorem nil_mulBy_pow_of_succ {p : ℕ} {k : Type} [Field k] (H : PDivGroup p k) (j : ℕ)
    (h : ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ (j + 1)) b)) :
    ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ j) b) := by
  intro n b hb
  obtain ⟨c, rfl⟩ := H.res_surjective n b
  have hc : c ∈ augIdeal k (H.A (n + 1)) := by
    have hb' : counit (R := k) (H.res n c) = 0 := hb
    change counit (R := k) c = 0
    rwa [CoalgHomClass.counit_comp_apply] at hb'
  have h1 := h (n + 1) c hc
  rw [pow_succ', ← mulBy_mulBy, ← H.mulP_res, map_mulBy] at h1
  obtain ⟨ρ, hρ⟩ := HTPair.exists_retraction_mulP H n
  have hinj : Function.Injective (H.mulP n : H.A n →ₐ[k] H.A (n + 1)) :=
    Function.LeftInverse.injective hρ
  exact isNilpotent_of_map_injective (H.mulP n : H.A n →ₐ[k] H.A (n + 1)).toRingHom hinj h1

theorem isConn_of_isIsog : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → G.IsConn → H.IsConn := by
  intro p _ k _ _ G H q hq hG
  obtain ⟨m, q', -, h2⟩ := hq
  have hm : ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ m) b) := by
    intro n b hb
    have e : mulBy k (H.A n) (p ^ m) = (q'.app n).comp (q.app n) := by
      rw [← natCast_smul_id_app H (p ^ m) n, Nat.cast_pow, ← h2]
      rfl
    rw [e, BialgHom.comp_apply]
    exact (hG n _ (mem_augIdeal_map _ hb)).map (q'.app n : G.A n →ₐ[k] H.A n)
  have key : ∀ j, (∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ j) b)) →
      ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ 0) b) := by
    intro j
    induction j with
    | zero => exact id
    | succ j ih => exact fun h => ih (nil_mulBy_pow_of_succ H j h)
  intro n b hb
  have h0 := key m hm n b hb
  have e1 : mulBy k (H.A n) (p ^ 0) b = b := by
    rw [pow_zero, mulBy, pow_one]
    rfl
  rwa [e1] at h0

end GlobalTheory.Dieu
end
end

section

set_option autoImplicit false

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

section FrobInv

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem wittMap_frobeniusEquiv_symm (x : WittVector p k) :
    WittVector.map ((frobeniusEquiv k p).symm : k →+* k) x = (WittVector.frobeniusEquiv p k).symm x := by
  apply (WittVector.frobeniusEquiv p k).injective
  rw [RingEquiv.apply_symm_apply]
  ext n
  simp [WittVector.coeff_frobenius_charP, WittVector.map_coeff]

noncomputable def frobInv (G : PDivGroup p k) :
    SemiHom ((frobeniusEquiv k p).symm : k →+* k) G (frobTwist (p_eq_zero p k) G) :=
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  (SemiHom.ofHom (𝟙 G)).liftOver _ fun r => by
    change r = (frobeniusEquiv k p).symm (frobRing (p_eq_zero p k) r)
    rw [frobRing_apply, ← frobenius_def, frobeniusEquiv_symm_apply_frobenius]

theorem frobInv_frobProj (G : PDivGroup p k) (n : ℕ) (a : G.A n) :
    (frobInv G).app n ((frobProj (p_eq_zero p k) G).app n a) = a := by
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  refine (SemiHom.liftOver_app _ _ _ n 1 a).trans ?_
  simp

theorem frobInv_app_pow (G : PDivGroup p k) (n : ℕ) (y : (frobTwist (p_eq_zero p k) G).A n) :
    ((frobInv G).app n y) ^ p = (relFrob (p_eq_zero p k) G).app n y := by
  have h0 : (p : G.A n) = 0 := natCast_eq_zero_of_algebra (p_eq_zero p k) _
  induction y using frobTwist_induction (p_eq_zero p k) n with
  | h0 => simp [zero_pow (Fact.out : p.Prime).ne_zero]
  | h1 r a =>
    rw [(frobInv G).app n |>.smul_map, frobInv_frobProj, map_smul, relFrob_app_frobProj, smul_pow]
    congr 1
    exact frobeniusEquiv_symm_pow_p k p r
  | h2 x y hx hy =>
    rw [map_add (f := _), map_add (f := _), ← hx, ← hy]
    simpa using map_add (frobRing h0) ((frobInv G).app n x) ((frobInv G).app n y)


omit [CharP k p] [PerfectRing k p] in
theorem Base.smap_ofHom_nsmul_id {P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop} (B : Base p P)
    [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) (n : ℕ) (m : B.M G h) :
    B.smap h h (SemiHom.ofHom (n • 𝟙 G)) m = n • m := by
  induction n with
  | zero =>
    have e := B.smap_add h h 0 0 m
    rw [add_zero] at e
    rw [zero_smul, zero_smul]
    simpa using e
  | succ n ih => rw [succ_nsmul, B.smap_add, ih, B.smap_id, succ_nsmul]

noncomputable def Base.verOp (B : Base p fun _ _ _ => True) (G : PDivGroup p k) :
    B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)]
      B.M G trivial where
  toFun m := B.smap trivial trivial (frobInv G) (B.map trivial trivial (verschiebung (p_eq_zero p k) G) m)
  map_add' x y := by rw [map_add (f := _), map_add (f := _)]
  map_smul' a m := by
    rw [LinearMap.map_smul, B.smap_smul, wittMap_frobeniusEquiv_symm]
    rfl

theorem Base.F_verOp (B : Base p fun _ _ _ => True) (G : PDivGroup p k) (m : B.M G trivial) :
    B.F G trivial (B.verOp G m) = p • m := by
  change B.smap trivial trivial (absFrob (p_eq_zero p k) G) (B.smap trivial trivial (frobInv G)
    (B.smap trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) m)) = _
  rw [← B.smap_comp trivial trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) (frobInv G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))) (fun n a => rfl)]
  rw [← B.smap_comp trivial trivial trivial ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)))
    (absFrob (p_eq_zero p k) G) (SemiHom.ofHom (relFrob (p_eq_zero p k) G ≫ verschiebung (p_eq_zero p k) G)) ?_]
  · rw [relFrob_comp_verschiebung, Nat.cast_smul_eq_nsmul, B.smap_ofHom_nsmul_id]
  · intro n a
    rw [SemiHom.ofHom_app, absFrob_app, SemiHom.comp_app, SemiHom.ofHom_app, frobInv_app_pow]
    rfl

theorem Base.verOp_F (B : Base p fun _ _ _ => True) (G : PDivGroup p k) (m : B.M G trivial) :
    B.verOp G (B.F G trivial m) = p • m := by
  change B.smap trivial trivial (frobInv G)
    (B.smap trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))
      (B.smap trivial trivial (absFrob (p_eq_zero p k) G) m)) = _
  rw [← B.smap_comp trivial trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) (frobInv G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))) (fun n a => rfl)]
  rw [← B.smap_comp trivial trivial trivial (absFrob (p_eq_zero p k) G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)))
    (SemiHom.ofHom (relFrob (p_eq_zero p k) G ≫ verschiebung (p_eq_zero p k) G)) ?_]
  · rw [relFrob_comp_verschiebung, Nat.cast_smul_eq_nsmul, B.smap_ofHom_nsmul_id]
  · intro n a
    rw [SemiHom.ofHom_app, absFrob_app, SemiHom.comp_app, SemiHom.ofHom_app]
    rw [map_pow, map_pow, frobInv_app_pow]
    rfl

end FrobInv

theorem exists_V_of_base : ∀ (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Dieu.Base p (fun _ _ _ => True)),
    ∃ V : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k),
      B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] B.M G trivial,
      (∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial),
        B.F G trivial (V G m) = p • m) ∧
      ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial),
        V G (B.F G trivial m) = p • m :=
  fun _ _ B => ⟨fun G => B.verOp G, fun G m => B.F_verOp G m, fun G m => B.verOp_F G m⟩

end GlobalTheory.Dieu
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory

namespace PDiv

theorem finrank_quot_kerIdeal_comp_le {k A B C : Type} [Field k] [CommRing A] [CommRing B]
    [CommRing C] [HopfAlgebra k A] [HopfAlgebra k B] [HopfAlgebra k C] [Module.Finite k A]
    [Module.Finite k B] (ψ : B →ₐc[k] A) (φ : C →ₐc[k] B) :
    Module.finrank k (A ⧸ kerIdeal (ψ.comp φ)) ≤
      Module.finrank k (A ⧸ kerIdeal ψ) * Module.finrank k (B ⧸ kerIdeal φ) := by
  have hHopf (X Y : Type) [CommRing X] [CommRing Y] [HopfAlgebra k X]
      [HopfAlgebra k Y] (f : Y →ₐc[k] X) : (kerIdeal f).IsHopfIdeal k := by
    refine {
    counit_eq_zero := by
      intro x hx
      exact (kerIdeal_le_ker_iff f (counitAlgHom k X)).2 (fun c => by simp) hx
    map_mkQ_comul_eq_zero := by
      intro x hx
      have h0 := (kerIdeal_le_ker_iff f (Ideal.Quotient.mkₐ k (kerIdeal f))).1
        fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
      have h : kerIdeal f ≤ RingHom.ker
          ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
            (Ideal.Quotient.mkₐ k (kerIdeal f))).comp (comulAlgHom k X)) := by
        refine (kerIdeal_le_ker_iff f _).2 fun c => ?_
        have key : ∀ t : Y ⊗[k] Y, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
            (Ideal.Quotient.mkₐ k (kerIdeal f)) (pullbackTwo f t) =
            algebraMap k _ (counit (R := k)
              (TensorProduct.lid k Y (LinearMap.rTensor Y (counit (R := k) (A := Y)) t))) := by
          intro t
          induction t with
          | add x y hx hy => simp only [map_add (f := _), hx, hy]
          | tmul x y =>
            rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul,
              TensorProduct.lid_tmul, map_smul]
            erw [h0, h0]
            simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
              smul_smul, mul_comm]
        rw [AlgHom.comp_apply, comulAlgHom_apply, ← pullTwo_comul, key, rTensor_counit_comul,
          TensorProduct.lid_tmul, one_smul]
      exact h hx
    antipode_mem := by
      intro x hx
      have h : kerIdeal f ≤ (kerIdeal f).comap (HopfAlgebra.antipodeAlgHom k X) := by
        refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
        have ha' : counit (R := k) a = 0 := ha
        change HopfAlgebra.antipode k (f a) ∈ kerIdeal f
        rw [← bialgHom_map_antipode]
        exact Ideal.mem_map_of_mem (f : Y →ₐ[k] X) (by simp [RingHom.mem_ker, ha'])
      exact h hx
    }
  haveI := hHopf A C (ψ.comp φ)
  haveI := hHopf B C φ
  let πA : A →ₐc[k] A ⧸ kerIdeal (ψ.comp φ) := Bialgebra.Quotient.mkBialgHom (kerIdeal (ψ.comp φ))
  let πB : B →ₐc[k] B ⧸ kerIdeal φ := Bialgebra.Quotient.mkBialgHom (kerIdeal φ)
  have hπA : Function.Surjective πA := Ideal.Quotient.mk_surjective
  have hπB : Function.Surjective πB := Ideal.Quotient.mk_surjective
  have hA : ∀ c, πA (ψ (φ c)) = algebraMap k _ (counit c) :=
    (kerIdeal_le_ker_iff (ψ.comp φ) (πA : A →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))).1
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h1 : kerIdeal φ ≤ RingHom.ker (πA.comp ψ : B →ₐ[k] A ⧸ kerIdeal (ψ.comp φ)) :=
    (kerIdeal_le_ker_iff φ _).2 fun c => hA c
  let m' : (B ⧸ kerIdeal φ) →ₐc[k] A ⧸ kerIdeal (ψ.comp φ) :=
    liftSurj πB hπB (πA.comp ψ) fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)
  have hm' : ∀ b, m' (πB b) = πA (ψ b) := fun b =>
    liftSurj_apply πB hπB (πA.comp ψ) (fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)) b
  let q : A →ₐ[k] (A ⧸ kerIdeal (ψ.comp φ)) ⧸ kerIdeal m' :=
    (Ideal.Quotient.mkₐ k (kerIdeal m')).comp (πA : A →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective.comp hπA
  have h0 := (kerIdeal_le_ker_iff m' (Ideal.Quotient.mkₐ k (kerIdeal m'))).1
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h4 : kerIdeal ψ ≤ RingHom.ker q := (kerIdeal_le_ker_iff ψ q).2 fun b => by
    change Ideal.Quotient.mkₐ k (kerIdeal m') (πA (ψ b)) = _
    rw [← hm', h0, CoalgHomClass.counit_comp_apply]
  let q'' : (A ⧸ kerIdeal ψ) →ₐ[k] (A ⧸ kerIdeal (ψ.comp φ)) ⧸ kerIdeal m' :=
    Ideal.Quotient.liftₐ (kerIdeal ψ) q h4
  have hq'' : Function.Surjective q''.toLinearMap := fun x => by
    obtain ⟨a, rfl⟩ := hq x
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  rw [finrank_eq_ker_mul_range k _ _ m']
  exact Nat.mul_le_mul (LinearMap.finrank_le_finrank_of_surjective hq'')
    (LinearMap.finrank_range_le _)

end PDiv

namespace Dieu

theorem hasLogDeg_comp_le : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K) (a b c : ℕ),
    HasLogDeg f a → HasLogDeg g b → HasLogDeg (f ≫ g) c → c ≤ a + b := by
  intro p _ k _ _ G H K f g a b c ⟨N₁, h₁⟩ ⟨N₂, h₂⟩ ⟨N₃, h₃⟩
  let n := max N₁ (max N₂ N₃)
  have e₁ := h₁ n (le_max_left _ _)
  have e₂ := h₂ n (le_trans (le_max_left _ _) (le_max_right _ _))
  have e₃ := h₃ n (le_trans (le_max_right _ _) (le_max_right _ _))
  have hle := finrank_quot_kerIdeal_comp_le (f.app n) (g.app n)
  rw [← comp_app, e₃, e₁, e₂, ← pow_add] at hle
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle

end Dieu

end GlobalTheory
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

section Height

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem finrank_level (G : PDivGroup p k) (n : ℕ) : Module.finrank k (G.A n) = p ^ (n * G.height) := by
  have h := G.rank_eq n ⟨⊥, Ideal.isPrime_bot⟩
  rwa [Module.rankAtStalk_eq_finrank_of_free] at h

theorem finrank_range_cartierDual_map {A B : Type} [CommRing A] [CommRing B] [HopfAlgebra k A]
    [HopfAlgebra k B] [Module.Finite k A] [Module.Finite k B] (f : B →ₐc[k] A) :
    Module.finrank k (LinearMap.range (CartierDual.map f : CartierDual k A →ₐ[k] CartierDual k B).toLinearMap) =
      Module.finrank k (LinearMap.range (f : B →ₐ[k] A).toLinearMap) := by
  have h : (CartierDual.map f : CartierDual k A →ₐ[k] CartierDual k B).toLinearMap =
      (CartierDual.toDual k B).symm.toLinearMap ∘ₗ
        ((f : B →ₐ[k] A).toLinearMap.dualMap ∘ₗ (CartierDual.toDual k A).toLinearMap) := rfl
  rw [h, LinearMap.range_comp, LinearEquiv.finrank_map_eq,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    LinearMap.finrank_range_dualMap_eq_finrank_range]

theorem finrank_quot_mulBy (G : PDivGroup p k) {m n : ℕ} (h : m ≤ n) :
    Module.finrank k (G.A n ⧸ kerIdeal (mulBy k (G.A n) (p ^ m))) = p ^ (m * G.height) := by
  obtain ⟨f, hf, hk⟩ := G.exists_res_le h
  have hk' : kerIdeal (mulBy k (G.A n) (p ^ m)) = RingHom.ker (f : G.A n →ₐ[k] G.A m) := hk.symm
  rw [hk', (Ideal.quotientKerAlgEquivOfSurjective (f := (f : G.A n →ₐ[k] G.A m)) hf).toLinearEquiv.finrank_eq,
    finrank_level]

theorem height_le_of_comp_eq {G H : PDivGroup p k} (q : G ⟶ H) (g : H ⟶ G) (m : ℕ)
    (hqg : q ≫ g = (p : ℤ_[p]) ^ m • 𝟙 G) : G.height ≤ H.height := by
  have key : ∀ n, m ≤ n → p ^ (n * G.height) ≤ p ^ (m * G.height) * p ^ (n * H.height) := by
    intro n hn
    have hL := finrank_eq_ker_mul_range k (G.A n) (G.A n) (mulBy k (G.A n) (p ^ m))
    rw [finrank_quot_mulBy G hn, finrank_level] at hL
    have happ : (q ≫ g).app n = mulBy k (G.A n) (p ^ m) := by
      rw [hqg, ← Nat.cast_pow, natCast_smul_id_app]
    have hr : LinearMap.range ((mulBy k (G.A n) (p ^ m) : G.A n →ₐ[k] G.A n).toLinearMap) ≤
        LinearMap.range ((q.app n : H.A n →ₐ[k] G.A n).toLinearMap) := by
      rw [← happ]
      exact LinearMap.range_comp_le_range (g.app n : G.A n →ₐ[k] H.A n).toLinearMap
        (q.app n : H.A n →ₐ[k] G.A n).toLinearMap
    have h1 := Submodule.finrank_mono hr
    have h2 := LinearMap.finrank_range_le ((q.app n : H.A n →ₐ[k] G.A n).toLinearMap)
    rw [finrank_level] at h2
    rw [hL]
    exact Nat.mul_le_mul_left _ (h1.trans h2)
  by_contra hlt
  push_neg at hlt
  have h3 := key (m * G.height + m + 1) (by nlinarith)
  rw [← pow_add] at h3
  have h4 := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 h3
  nlinarith [Nat.mul_le_mul_left (m * G.height + m + 1) hlt]

theorem height_eq_and_dual_isog (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H : PDivGroup p k) (q : G ⟶ H) (hq : IsIsog q) :
    G.height = H.height ∧ IsIsog (dualHom G H q) ∧ ∀ e, HasLogDeg q e → HasLogDeg (dualHom G H q) e := by
  obtain ⟨m, g, h1, h2⟩ := hq
  have hGH : G.height = H.height :=
    le_antisymm (height_le_of_comp_eq q g m h1) (height_le_of_comp_eq g q m h2)
  refine ⟨hGH, ⟨m, dualHom H G g, ?_, ?_⟩, ?_⟩
  · rw [← dualHom_comp, h2, map_smul, dualHom_id]
  · rw [← dualHom_comp, h1, map_smul, dualHom_id]
  · rintro e ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have he := hN n hn
    have L1 := finrank_eq_ker_mul_range k (G.A n) (H.A n) (q.app n)
    have L2 := finrank_eq_ker_mul_range k (H.dual.A n) (G.dual.A n) ((dualHom G H q).app n)
    rw [he, finrank_level] at L1
    rw [finrank_level, dualHom_app, finrank_range_cartierDual_map] at L2
    have hr : 0 < Module.finrank k (LinearMap.range (q.app n : H.A n →ₐ[k] G.A n).toLinearMap) := by
      rcases Nat.eq_zero_or_pos (Module.finrank k (LinearMap.range (q.app n : H.A n →ₐ[k] G.A n).toLinearMap))
        with h0 | h0
      · rw [h0, mul_zero] at L1
        exact absurd L1 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      · exact h0
    have L3 : p ^ (n * H.dual.height) = p ^ (n * G.height) := by rw [hGH]
    rw [L1, L2] at L3
    exact Nat.eq_of_mul_eq_mul_right hr L3

end Height

end GlobalTheory.Dieu
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConeLocalization

theorem cone_kinj (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G) :
    (mappingCone (resMap R φ)).IsKInjective := by
  haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.1
  haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R G).2.1
  haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.2.1
  haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R G).2.2.1
  haveI : ∀ n, Injective ((mappingCone (resMap R φ)).X n) := fun n =>
    Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod (resMap R φ) n (n + 1) rfl).symm inferInstance
  haveI : (mappingCone (resMap R φ)).IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1)
  exact isKInjective_of_injective _ (-1)

theorem cone_loc (R : Type) [CommRing R] (E : Spc) {F G : Shv R} (φ : F ⟶ G)
    (hφ : ∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U))) :
    ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec ((mappingCone (resMap R φ)).X n) U),
      Sec.map ((mappingCone (resMap R φ)).d n (n + 1)) b = 0 →
      Loc U fun V g => ∃ a : Sec ((mappingCone (resMap R φ)).X (n - 1)) V,
        Sec.map ((mappingCone (resMap R φ)).d (n - 1) n) a = Sec.res g b := by
  intro U hU n b hb
  exact GlobalTheory.T.mappingCone_locallyExact_of_component_sections R (resMap R φ) U n (GlobalTheory.T.mappingCone_resolution_localChase_on_support R E φ hφ U hU n) b hb

end GlobalTheory.EtC.ConeLocalization

theorem GlobalTheory.EtC.a10 : GlobalTheory.EtC.A10 := by
  intro R _ E F G φ hφ
  haveI := GlobalTheory.EtC.ConeLocalization.cone_kinj R φ
  have hC := GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support R E (mappingCone (resMap R φ)) (GlobalTheory.EtC.ConeLocalization.cone_loc R E φ hφ)
  have ex := GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R ((chains R).obj E) (resMap R φ)
  intro n
  constructor
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := ((ex m).2.2 x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    exact ((ex n).1 y).1 (Subsingleton.elim _ _)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem a6add_holds : GlobalTheory.EtC.DivisorAdditivity := by
  intro q _
  exact ⟨fun L M N hE hN => (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.2 L M N hE hN,
    fun u v hq => (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 u v hq⟩

end GlobalTheory.EtC
end
