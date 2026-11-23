module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Basic
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Nilpotent.Defs

@[expose] public section

section

open TensorProduct Polynomial

namespace GlobalTheory

theorem convPow_sub_nsmul_mem_augIdeal_sq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (ε : B →ₐ[A] A) (Δ : B →ₐ[A] B ⊗[A] B) (α : ℕ → (B →ₐ[A] B)), (Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B) (fun _ _ => Commute.all _ _)).comp Δ = AlgHom.id A B → (Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _)).comp Δ = AlgHom.id A B → α 0 = (Algebra.ofId A B).comp ε → (∀ n, α (n+1) = (Algebra.TensorProduct.lift (α n) (AlgHom.id A B) (fun _ _ => Commute.all _ _)).comp Δ) → ∀ n, ∀ x ∈ RingHom.ker ε, α n x - (n : B) * x ∈ (RingHom.ker ε) ^ 2 := by
  intro A B _ _ _ ε Δ α hL hR h0 hS
  have hεu : ∀ a : A, ε (algebraMap A B a) = a := fun a => by simp
  have hL' : ∀ b, Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
      (fun _ _ => Commute.all _ _) (Δ b) = b := fun b => by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using DFunLike.congr_fun hL b
  have hR' : ∀ b, Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε)
      (fun _ _ => Commute.all _ _) (Δ b) = b := fun b => by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using DFunLike.congr_fun hR b

  have hε : ∀ n b, ε (α n b) = ε b := by
    intro n
    induction n with
    | zero => intro b; rw [h0]; simp [hεu]
    | succ n ih =>
      intro b
      have key : ∀ t : B ⊗[A] B,
          ε (Algebra.TensorProduct.lift (α n) (AlgHom.id A B) (fun _ _ => Commute.all _ _) t) =
          ε (Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
            (fun _ _ => Commute.all _ _) t) := by
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul b c => simp [Algebra.TensorProduct.lift_tmul, ih, hεu]
        | add s t hs ht => simp only [map_add (f := _), hs, ht]
      rw [hS n, AlgHom.comp_apply, key, hL' b]

  have hright : ∀ (ψ : B →ₐ[A] B) (t : B ⊗[A] B),
      Algebra.TensorProduct.lift ψ ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _) t =
      ψ (Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε)
        (fun _ _ => Commute.all _ _) t) := by
    intro ψ t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b c => simp [Algebra.TensorProduct.lift_tmul]
    | add s t hs ht => simp only [map_add (f := _), hs, ht]

  have gen : ∀ (φ : B →ₐ[A] B), (∀ b, ε (φ b) = ε b) → ∀ t : B ⊗[A] B,
      Algebra.TensorProduct.lift φ (AlgHom.id A B) (fun _ _ => Commute.all _ _) t
        - Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
            (fun _ _ => Commute.all _ _) t
        - Algebra.TensorProduct.lift φ ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _) t
        + Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) ((Algebra.ofId A B).comp ε)
            (fun _ _ => Commute.all _ _) t ∈ RingHom.ker ε ^ 2 := by
    intro φ hφ t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.id_apply,
        Algebra.ofId_apply]
      have e : φ b * c - algebraMap A B (ε b) * c - φ b * algebraMap A B (ε c)
          + algebraMap A B (ε b) * algebraMap A B (ε c)
          = (φ b - algebraMap A B (ε b)) * (c - algebraMap A B (ε c)) := by ring
      rw [e, sq]
      exact Ideal.mul_mem_mul (by rw [RingHom.mem_ker]; simp [hφ, hεu])
        (by rw [RingHom.mem_ker]; simp [hεu])
    | add s t hs ht =>
      have e := add_mem hs ht
      simp only [map_add (f := _)]
      convert e using 1
      abel
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [h0]
    simp [RingHom.mem_ker.mp hx]
  | succ n ih =>
    intro x hx
    have E := gen (α n) (hε n) (Δ x)
    rw [hL' x, hright (α n) (Δ x), hright ((Algebra.ofId A B).comp ε) (Δ x), hR' x] at E
    have hx0 : ε x = 0 := by simpa using hx
    have h4 : ((Algebra.ofId A B).comp ε) x = 0 := by simp [hx0]
    rw [h4, add_zero] at E
    rw [hS n, AlgHom.comp_apply]
    convert add_mem E (ih x hx) using 1
    push_cast
    ring

end GlobalTheory
end

section

namespace GlobalTheory.DualParts

theorem card_le_of_injective_chars (G H : Type) [CommGroup G] [Finite G] (U : Type) [CommRing U]
    [IsDomain U] (f : H → (G →* Uˣ)) (hf : Function.Injective f) :
    Finite H ∧ Nat.card H ≤ Nat.card G := by
  classical
  haveI := Fintype.ofFinite G
  let g : H → (G →* U) := fun h => (Units.coeHom U).comp (f h)
  have hg : Function.Injective g := by
    intro a b hab
    apply hf
    refine MonoidHom.ext fun x => Units.ext ?_
    have := congrArg (fun χ : G →* U => χ x) hab
    simpa [g] using this
  have hli : LinearIndependent U (fun h => (g h : G → U)) :=
    (linearIndependent_monoidHom G U).comp g hg
  haveI : Finite H := hli.finite
  haveI := Fintype.ofFinite H
  refine ⟨inferInstance, ?_⟩
  have := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at this
  simpa [Nat.card_eq_fintype_card] using this

theorem conj_dual_parts : ∀ (O : Type) [CommRing O] (bar : O →+* O) (U : Type) [CommRing U] [IsDomain U] (M M' : Type) [CommGroup M] [CommGroup M'] (α : O → M →* M) (α' : O → M' →* M'), (∀ y, α 1 y = y) → (∀ a b y, α (a * b) y = α a (α b y)) → (∀ a b y, α (a + b) y = α a y * α b y) → (∀ x, α' 1 x = x) → (∀ a b x, α' (a * b) x = α' a (α' b x)) → (∀ a b x, α' (a + b) x = α' a x * α' b x) → (∀ a, bar (bar a) = a) → ∀ (e : M' →* M →* Uˣ) (e' : M →* M' →* Uˣ), Function.Injective e → Function.Injective e' → (∀ a x y, e (α' a x) y = e x (α (bar a) y)) → (∀ a y x, e' (α a y) x = e' y (α' (bar a) x)) → ∀ (u w : Ideal O) (n : ℕ), u ≤ w → u ⊔ u.map bar = ⊤ → (∀ a ∈ (u * u.map bar) ^ n, (∀ y, α a y = 1) ∧ ∀ x, α' a x = 1) → (∀ y, (∃ m : ℕ, ∀ a ∈ u ^ m, α a y = 1) → ∀ a ∈ w, α a y = 1) → Finite {y : M // ∀ a ∈ w, α a y = 1} → (∀ x, (∃ m : ℕ, ∀ a ∈ (u.map bar) ^ m, α' a x = 1) → ∀ a ∈ w.map bar, α' a x = 1) ∧ Nat.card {x : M' // ∀ a ∈ w.map bar, α' a x = 1} = Nat.card {y : M // ∀ a ∈ w, α a y = 1} := by
  intro O _ bar U _ _ M M' _ _ α α' h1 hmul hadd h1' hmul' hadd' hbb e e' he he' hee hee' u w n huw hcop
    hkill hw hfin
  have hsurj : Function.Surjective bar := fun a => ⟨bar a, hbb a⟩
  have hbarbar : (u.map bar).map bar = u := by
    rw [Ideal.map_map]
    have : bar.comp bar = RingHom.id O := RingHom.ext hbb
    rw [this, Ideal.map_id]
  have hsplit : ∀ k : ℕ, ∃ a₀ ∈ u ^ k, ∃ b₀ ∈ (u.map bar) ^ k, a₀ + b₀ = 1 := by
    intro k
    have hc : IsCoprime u (u.map bar) := Ideal.isCoprime_iff_sup_eq.2 hcop
    have hs : u ^ k ⊔ (u.map bar) ^ k = ⊤ := Ideal.isCoprime_iff_sup_eq.1 (hc.pow)
    have h1mem : (1 : O) ∈ u ^ k ⊔ (u.map bar) ^ k := by rw [hs]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1mem
    exact ⟨a, ha, b, hb, hab⟩
  have hbar1 : ∀ k, ∀ a ∈ u ^ k, bar a ∈ (u.map bar) ^ k := by
    intro k a ha
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem bar ha
  have hbar2 : ∀ k, ∀ b ∈ (u.map bar) ^ k, bar b ∈ u ^ k := by
    intro k b hb
    have := Ideal.mem_map_of_mem bar hb
    rwa [Ideal.map_pow, hbarbar] at this
  have hprod : ∀ k, n ≤ k → ∀ a ∈ u ^ k, ∀ b ∈ (u.map bar) ^ k, a * b ∈ (u * u.map bar) ^ n := by
    intro k hk a ha b hb
    have : a * b ∈ (u * u.map bar) ^ k := by rw [mul_pow]; exact Ideal.mul_mem_mul ha hb
    exact Ideal.pow_le_pow_right hk this
  have hpowle : ∀ (I : Ideal O) (k m : ℕ), m ≤ k → I ^ k ≤ I ^ m := fun I k m h =>
    Ideal.pow_le_pow_right h

  have part1 : ∀ x, (∃ m : ℕ, ∀ a ∈ (u.map bar) ^ m, α' a x = 1) → ∀ a ∈ w.map bar, α' a x = 1 := by
    rintro x ⟨m, hm⟩ c hc
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective bar hsurj).1 hc
    apply he
    rw [map_one]
    refine MonoidHom.ext fun y => ?_
    rw [MonoidHom.one_apply, hee, hbb]
    obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := hsplit (m + n)
    have hy : y = α a₀ y * α b₀ y := by rw [← hadd, hab, h1]
    rw [hy, map_mul, map_mul]
    have t1 : e x (α a (α a₀ y)) = 1 := by
      rw [← hmul, ← hbb (a * a₀), ← hee, map_mul bar, hmul',
        hm (bar a₀) (hpowle _ (m + n) m (by omega) (hbar1 _ a₀ ha₀))]
      simp
    have t2 : α a (α b₀ y) = 1 := by
      refine hw (α b₀ y) ⟨m + n, fun c hc => ?_⟩ a ha
      rw [← hmul]; exact (hkill _ (hprod (m + n) (by omega) c hc b₀ hb₀)).1 y
    rw [t1, t2, map_one, one_mul]
  refine ⟨part1, ?_⟩

  obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := hsplit (n + 1)
  let A : Subgroup M :=
    { carrier := {y | ∀ a ∈ w, α a y = 1}
      one_mem' := fun a _ => map_one (α a)
      mul_mem' := fun {y z} hy hz a ha => by
        rw [map_mul, (show ∀ a ∈ w, α a y = 1 from hy) a ha,
          (show ∀ a ∈ w, α a z = 1 from hz) a ha, one_mul]
      inv_mem' := fun {y} hy a ha => by
        rw [map_inv, (show ∀ a ∈ w, α a y = 1 from hy) a ha, inv_one] }
  let B : Subgroup M' :=
    { carrier := {x | ∀ a ∈ w.map bar, α' a x = 1}
      one_mem' := fun a _ => map_one (α' a)
      mul_mem' := fun {y z} hy hz a ha => by
        rw [map_mul, (show ∀ a ∈ w.map bar, α' a y = 1 from hy) a ha,
          (show ∀ a ∈ w.map bar, α' a z = 1 from hz) a ha, one_mul]
      inv_mem' := fun {y} hy a ha => by
        rw [map_inv, (show ∀ a ∈ w.map bar, α' a y = 1 from hy) a ha, inv_one] }
  have hu1 : u ^ (n + 1) ≤ u := Ideal.pow_le_self (by omega)
  have hub1 : (u.map bar) ^ (n + 1) ≤ u.map bar := Ideal.pow_le_self (by omega)

  have F1 : ∀ y, α b₀ y ∈ A := by
    intro y
    refine hw (α b₀ y) ⟨n + 1, fun c hc => ?_⟩
    rw [← hmul]; exact (hkill _ (hprod (n + 1) (by omega) c hc b₀ hb₀)).1 y
  have F2 : ∀ x ∈ B, α' (bar a₀) x = 1 := fun x hx =>
    hx _ (Ideal.map_mono huw (hub1 (hbar1 _ a₀ ha₀)))
  have E1 : ∀ x ∈ B, ∀ y, e x y = e x (α b₀ y) := by
    intro x hx y
    conv_lhs => rw [← h1 y, ← hab, hadd, map_mul]
    rw [← hbb a₀, ← hee, F2 x hx]
    simp
  have F3 : ∀ x, α' a₀ x ∈ B := by
    intro x
    refine part1 (α' a₀ x) ⟨n + 1, fun c hc => ?_⟩
    rw [← hmul', mul_comm]; exact (hkill _ (hprod (n + 1) (by omega) a₀ ha₀ c hc)).2 x
  have F4 : ∀ y ∈ A, α (bar b₀) y = 1 := fun y hy => hy _ (huw (hu1 (hbar2 _ b₀ hb₀)))
  have E2 : ∀ y ∈ A, ∀ x, e' y x = e' y (α' a₀ x) := by
    intro y hy x
    conv_lhs => rw [← h1' x, ← hab, hadd', map_mul]
    rw [← hbb b₀, ← hee', F4 y hy]
    simp
  haveI : Finite A := hfin
  have hAB : Finite B ∧ Nat.card B ≤ Nat.card A := by
    refine card_le_of_injective_chars A B U (fun x => (e x.1).comp A.subtype) ?_
    intro x₁ x₂ h
    apply Subtype.ext
    apply he
    refine MonoidHom.ext fun y => ?_
    rw [E1 x₁.1 x₁.2, E1 x₂.1 x₂.2]
    exact congrArg (fun χ : A →* Uˣ => χ ⟨α b₀ y, F1 y⟩) h
  haveI : Finite B := hAB.1
  have hBA : Finite A ∧ Nat.card A ≤ Nat.card B := by
    refine card_le_of_injective_chars B A U (fun y => (e' y.1).comp B.subtype) ?_
    intro y₁ y₂ h
    apply Subtype.ext
    apply he'
    refine MonoidHom.ext fun x => ?_
    rw [E2 y₁.1 y₁.2, E2 y₂.1 y₂.2]
    exact congrArg (fun χ : B →* Uˣ => χ ⟨α' a₀ x, F3 x⟩) h
  exact le_antisymm hAB.2 hBA.2

end GlobalTheory.DualParts
end

section

noncomputable section

namespace GlobalTheory.AbHomDesc

variable {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)

def iota (hI : RingHom.ker π = I) (S : Subring R) : S ⧸ I.comap S.subtype →+* R₀ :=
  Ideal.Quotient.lift _ (π.comp S.subtype) fun x hx => by
    have h : (x : R) ∈ I := hx
    rw [← hI] at h
    exact h

theorem iota_comp_mk (hI : RingHom.ker π = I) (S : Subring R) :
    (iota I π hI S).comp (Ideal.Quotient.mk _) = π.comp S.subtype := rfl

theorem iota_injective (hI : RingHom.ker π = I) (S : Subring R) : Function.Injective (iota I π hI S) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change (x : R) ∈ I
  rw [← hI]
  exact ha

def trans {S S' : Subring R} (h : S ≤ S') : S ⧸ I.comap S.subtype →+* S' ⧸ I.comap S'.subtype :=
  Ideal.quotientMap _ (Subring.inclusion h) fun x hx => hx

theorem iota_comp_trans (hI : RingHom.ker π = I) {S S' : Subring R} (h : S ≤ S') :
    (iota I π hI S').comp (trans I h) = iota I π hI S := by
  ext x
  rfl

theorem trans_comp_mk {S S' : Subring R} (h : S ≤ S') :
    (trans I h).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (Subring.inclusion h) := rfl

end GlobalTheory.AbHomDesc
end
end

section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem reduced_quot_tensor_of_reduced_modp :
    ∀ (O : Type) [CommRing O] (k : Type) [Field k] (p : ℕ) (ϖ : O), (p : k) = 0 →
      IsReduced (k ⊗[ℤ] (O ⧸ Ideal.span {(p : O), ϖ})) →
      IsReduced ((k ⊗[ℤ] O) ⧸ Ideal.span {(1 : k) ⊗ₜ[ℤ] ϖ}) := by
  intro O _ k _ p ϖ hp hred
  set I : Ideal O := Ideal.span {(p : O), ϖ}
  set f := Algebra.TensorProduct.map (AlgHom.id ℤ k) (Ideal.Quotient.mkₐ ℤ I) with hf
  have hker : RingHom.ker f.toRingHom = Ideal.span {(1 : k) ⊗ₜ[ℤ] ϖ} := by
    have h := Algebra.TensorProduct.lTensor_ker (A := k) (Ideal.Quotient.mkₐ ℤ I)
      (Ideal.Quotient.mkₐ_surjective ℤ I)
    have hk : RingHom.ker (Ideal.Quotient.mkₐ ℤ I) = I := Ideal.Quotient.mkₐ_ker ℤ I
    have h0 : (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] k ⊗[ℤ] O) (p : O) = 0 := by
      rw [map_natCast]
      have : ((p : ℕ) : k ⊗[ℤ] O) = (Algebra.TensorProduct.includeLeft : k →ₐ[ℤ] k ⊗[ℤ] O) (p : k) := by
        rw [map_natCast]
      rw [this, hp, map_zero]
    have h1 : (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] k ⊗[ℤ] O) ϖ = (1 : k) ⊗ₜ[ℤ] ϖ := rfl
    have e := h
    rw [hk] at e
    change RingHom.ker f.toRingHom = _ at e
    rw [e, Ideal.map_span, Set.image_pair]
    erw [h0, h1]
    exact Ideal.span_insert_zero
  have hinj : Function.Injective (RingHom.kerLift f.toRingHom) := RingHom.kerLift_injective _
  have hR : IsReduced (k ⊗[ℤ] O ⧸ RingHom.ker f.toRingHom) := isReduced_of_injective _ hinj
  rw [hker] at hR
  exact hR

end GlobalTheory
end

section

namespace GlobalTheory

open TensorProduct



theorem quot_tensor_level : ∀ (R : Type) [CommRing R] (I : Ideal R) (R' : Type) [CommRing R'] [Algebra R R'] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (O : Type) [CommRing O] [Algebra R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (I ^ (e + 1)).map (algebraMap R C')), (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (I ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ (C : Subalgebra R C') (gm : ∀ e : ℕ, (O ⧸ (I ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (I ^ (e + 1)).map (algebraMap R C))), (∀ e (x : O) (c : C), gm e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x) → (∀ y : C', ∃ t : TensorProduct R C R', y - Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ (I.map (algebraMap R C)).map (algebraMap C C')) ∧ ∀ (n : ℕ) (t : TensorProduct R C R'), Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C C') → t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C (TensorProduct R C R')) := by
  intro R _ I R' _ _ C' _ _ _ _ O _ _ i hi C gm hcomp

  have hJ : ∀ k : ℕ, ((I.map (algebraMap R C)) ^ k).map (algebraMap C C') =
      (I ^ k).map (algebraMap R C') := by
    intro k
    rw [← Ideal.map_pow, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  set φ := Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C')
    (fun _ _ => Commute.all _ _) with hφ
  have hφt : ∀ (c : C) (r : R'), φ (c ⊗ₜ r) = (c : C') * algebraMap R' C' r := by
    intro c r
    simp [φ, Algebra.TensorProduct.lift_tmul]
  refine ⟨?_, ?_⟩
  · intro y
    have key : ∀ s : O ⊗[R] R', ∃ t : C ⊗[R] R',
        Algebra.TensorProduct.lift (i 0) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C'))
          (fun _ _ => Commute.all _ _) s = Ideal.Quotient.mk _ (φ t) := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul x r =>
        obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (gm 0 (Ideal.Quotient.mk _ x))
        refine ⟨c ⊗ₜ r, ?_⟩
        rw [Algebra.TensorProduct.lift_tmul, hφt, ← hcomp 0 x c hc.symm]
        simp [map_mul]
      | add a b ha hb =>
        obtain ⟨ta, hta⟩ := ha
        obtain ⟨tb, htb⟩ := hb
        exact ⟨ta + tb, by rw [map_add (f := _), hta, htb, map_add (f := _), map_add (f := _)]⟩
    obtain ⟨s, hs⟩ := (hi 0).1 (Ideal.Quotient.mk _ y)
    obtain ⟨t, ht⟩ := key s
    refine ⟨t, ?_⟩
    have h1 := (Ideal.Quotient.eq).1 (hs.symm.trans ht)
    have h2 := hJ 1
    rw [pow_one] at h2
    rw [h2]
    simpa using h1
  · intro n t ht
    cases n with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
      exact Submodule.mem_top
    | succ e =>
    rw [← Ideal.map_pow] at ht ⊢
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at ht
    set K := (I ^ (e + 1)).map (algebraMap R C) with hK
    set πC : C ⊗[R] R' →ₐ[R] (C ⧸ K) ⊗[R] R' :=
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R K) (AlgHom.id R R') with hπC
    have hker : RingHom.ker πC = K.map (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') := by
      rw [Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective R K)]
      congr 1
      ext a
      simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    have hinc : K.map (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') =
        K.map (algebraMap C (C ⊗[R] R')) := by
      have : ((Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') : C →+* C ⊗[R] R') =
          algebraMap C (C ⊗[R] R') := by
        ext c
        simp [Algebra.TensorProduct.algebraMap_apply]
      rw [← this]
      rfl
    have hvan : ∀ a ∈ K, ((Ideal.Quotient.mkₐ R ((I ^ (e + 1)).map (algebraMap R C'))).comp C.val) a = 0 := by
      intro a ha
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      have : (a : C') ∈ K.map (algebraMap C C') := Ideal.mem_map_of_mem _ ha
      rwa [hK, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at this
    set Λ : (C ⧸ K) ⊗[R] R' →ₐ[R] C' ⧸ (I ^ (e + 1)).map (algebraMap R C') :=
      Algebra.TensorProduct.lift (Ideal.Quotient.liftₐ K _ hvan)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _) with hΛ
    have hL : ∀ c : C, Ideal.Quotient.liftₐ K _ hvan (Ideal.Quotient.mk K c) =
        Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R C')) (c : C') := fun c => rfl
    set G : O ⊗[R] R' →ₐ[R] (C ⧸ K) ⊗[R] R' :=
      Algebra.TensorProduct.map ((gm e).toAlgHom.comp (Ideal.Quotient.mkₐ R _)) (AlgHom.id R R') with hG
    have hGs : Function.Surjective G :=
      Algebra.TensorProduct.map_surjective _ _
        ((gm e).surjective.comp (Ideal.Quotient.mkₐ_surjective R _)) Function.surjective_id
    have hΛG : ∀ s, Λ (G s) = Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _) s := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul x r =>
        obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (gm e (Ideal.Quotient.mk _ x))
        have hc' := hcomp e x c hc.symm
        simp only [G, Λ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
        show Ideal.Quotient.liftₐ K _ hvan (gm e (Ideal.Quotient.mk _ x)) * _ = _
        rw [← hc, ← hc']
        congr 1
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]
    have hΛπ' : Λ.comp πC = (Ideal.Quotient.mkₐ R _).comp (φ.restrictScalars R) := by
      refine Algebra.TensorProduct.ext' fun c r => ?_
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, πC, Λ, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.lift_tmul, hφt]
      rw [map_mul]
      congr 1
    have hΛπ : ∀ u, Λ (πC u) = Ideal.Quotient.mk _ (φ u) := fun u => by
      have := congrArg (fun f => f u) hΛπ'
      simpa using this
    obtain ⟨s, hs⟩ := hGs (πC t)
    have hs0 : s ∈ RingHom.ker (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _)) := by
      rw [RingHom.mem_ker, ← hΛG, hs, hΛπ, Ideal.Quotient.eq_zero_iff_mem]
      exact ht
    rw [(hi e).2] at hs0
    have hGz : G s = 0 := by
      have hle : (I ^ (e + 1)).map (algebraMap R (O ⊗[R] R')) ≤ RingHom.ker G.toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
          IsScalarTower.algebraMap_apply R (C ⧸ K) ((C ⧸ K) ⊗[R] R'), ← Ideal.Quotient.mk_algebraMap,
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha), map_zero]
      exact hle hs0
    rw [← hinc, ← hker, RingHom.mem_ker, ← hs, hGz]

end GlobalTheory
end
