module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
public import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Pi
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
public import Mathlib.RingTheory.Filtration
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Localization.Basic

@[expose] public section

section

namespace GlobalTheory.AlgEquivTrivialPowerCongruence

theorem sub_mem_pow_succ {B : Type} [CommRing B] (Q : Ideal B) (ρ : B →+* B)
    (h0 : ∀ x, ρ x - x ∈ Q) (h1 : ∀ x ∈ Q, ρ x - x ∈ Q ^ 2) :
    ∀ (k : ℕ), ∀ x ∈ Q ^ k, ρ x - x ∈ Q ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro x _; simpa using h0 x
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha q hq
      have hd := ih a ha
      have hρa : ρ a ∈ Q ^ k := by
        have h2 : ρ a - a ∈ Q ^ k := Ideal.pow_le_pow_right (Nat.le_succ k) hd
        have h3 := Ideal.add_mem _ h2 ha
        simpa using h3
      have e : ρ (a * q) - a * q = ρ a * (ρ q - q) + (ρ a - a) * q := by
        rw [map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · have h4 := Ideal.mul_mem_mul hρa (h1 q hq)
        rw [← pow_add] at h4
        exact h4
      · have h4 := Ideal.mul_mem_mul hd hq
        rw [← pow_succ] at h4
        exact h4
    · intro a b ha hb
      have e : ρ (a + b) - (a + b) = (ρ a - a) + (ρ b - b) := by
        rw [map_add (f := _)]; ring
      rw [e]
      exact Ideal.add_mem _ ha hb

theorem algEquiv_eq_one (A B : Type) [CommRing A] [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Algebra A B] (Q : Ideal B) (ρ : B ≃ₐ[A] B) (m : ℕ) (hQ : Q ≠ ⊤) (hm : IsUnit (m : B))
    (hρ : ρ ^ m = 1) (h0 : ∀ x : B, ρ x - x ∈ Q) (h1 : ∀ x ∈ Q, ρ x - x ∈ Q ^ 2) :
    ρ = 1 := by
  have step : ∀ (k : ℕ), ∀ x ∈ Q ^ k, ρ x - x ∈ Q ^ (k + 1) :=
    sub_mem_pow_succ Q (ρ : B →+* B) h0 h1
  have key : ∀ (k : ℕ) (x : B), ρ x - x ∈ Q ^ k := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      have hy := ih x
      have hj : ∀ j : ℕ, (ρ ^ j) x - x - (j : B) * (ρ x - x) ∈ Q ^ (k + 1) := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          have hz := step (k + 1) _ ihj
          have hz' := Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)) hz) ihj
          rw [sub_add_cancel] at hz'
          have hw := Ideal.mul_mem_left _ (j : B) (step k _ hy)
          have h5 := Ideal.add_mem _ hz' hw
          convert h5 using 1
          rw [pow_succ', AlgEquiv.mul_apply]
          simp only [map_sub, map_mul, map_natCast]
          push_cast
          ring
      have hmm := hj m
      rw [hρ] at hmm
      simp only [AlgEquiv.one_apply, sub_self, zero_sub, neg_mem_iff] at hmm
      exact (Ideal.unit_mul_mem_iff_mem _ hm).1 hmm
  have hbot : ⨅ k : ℕ, Q ^ k = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain Q hQ
  ext x
  have hx : ρ x - x ∈ ⨅ k : ℕ, Q ^ k := Ideal.mem_iInf.2 fun k => key k x
  rw [hbot, Ideal.mem_bot, sub_eq_zero] at hx
  simpa using hx

end GlobalTheory.AlgEquivTrivialPowerCongruence
end

section

open CategoryTheory Limits TensorProduct

noncomputable section

namespace GlobalTheory.TorsorColim

def bcAct (S : Type) {R A G : Type} [CommRing R] [CommRing S] [CommRing A] [Algebra R S]
    [Algebra R A] [Monoid G] (act : G →* (A ≃ₐ[R] A)) : G →* (S ⊗[R] A ≃ₐ[S] S ⊗[R] A) where
  toFun g := Algebra.TensorProduct.congr AlgEquiv.refl (act g)
  map_one' := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp
    | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _)]
  map_mul' g h := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp
    | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _)]

@[simp]
theorem bcAct_tmul (S : Type) {R A G : Type} [CommRing R] [CommRing S] [CommRing A] [Algebra R S]
    [Algebra R A] [Monoid G] (act : G →* (A ≃ₐ[R] A)) (g : G) (s : S) (a : A) :
    bcAct S act g (s ⊗ₜ[R] a) = s ⊗ₜ[R] act g a := rfl

def prodMapOf (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) :
    D ⊗[B] D →ₐ[B] (Multiplicative (ZMod q) → D) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
    (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))

@[simp]
theorem prodMapOf_tmul (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) (x y : D) (g : Multiplicative (ZMod q)) :
    prodMapOf B D q act (x ⊗ₜ[B] y) g = x * act g y := by
  simp [prodMapOf]

theorem eventually_and {J : Type} [Category J] [IsFiltered J] {j : J}
    (P Q : ∀ k : J, (j ⟶ k) → Prop)
    (hP : ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), P k (f₀ ≫ f))
    (hQ : ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), Q k (f₀ ≫ f)) :
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), P k (f₀ ≫ f) ∧ Q k (f₀ ≫ f) := by
  obtain ⟨k₁, f₁, h₁⟩ := hP
  obtain ⟨k₂, f₂, h₂⟩ := hQ
  let a := IsFiltered.leftToMax k₁ k₂
  let b := IsFiltered.rightToMax k₁ k₂
  let e := IsFiltered.coeqHom (f₁ ≫ a) (f₂ ≫ b)
  have he : (f₁ ≫ a) ≫ e = (f₂ ≫ b) ≫ e := IsFiltered.coeq_condition _ _
  refine ⟨IsFiltered.coeq (f₁ ≫ a) (f₂ ≫ b), (f₁ ≫ a) ≫ e, fun k f => ⟨?_, ?_⟩⟩
  · have := h₁ k (a ≫ e ≫ f)
    simpa only [Category.assoc] using this
  · have := h₂ k (b ≫ e ≫ f)
    rw [he]
    simpa only [Category.assoc] using this

end GlobalTheory.TorsorColim
end
end

section

open scoped TensorProduct

noncomputable section
namespace GlobalTheory.GoodEtale

variable {R C O G : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O] [Group G]

def galMap (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) : O ⊗[R] C →ₐ[O] (G → O) :=
  Pi.algHom O (fun _ => O) fun g =>
    Algebra.TensorProduct.lift (AlgHom.id O O) (σ.comp (act g).toAlgHom) (fun _ _ => Commute.all _ _)

@[simp] theorem galMap_tmul (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) (o : O) (c : C) (g : G) :
    galMap act σ (o ⊗ₜ c) g = o * σ (act g c) := by
  simp [galMap]

def galElt (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) {n : ℕ} (x y : Fin n → C) (h : G) : O ⊗[R] C :=
  ∑ i, σ (x i) ⊗ₜ act h⁻¹ (y i)

theorem galMap_galElt [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) {n : ℕ} (x y : Fin n → C)
    (b : R) (hxy : ∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C b else 0) (h : G) :
    galMap act σ (galElt act σ x y h) = Pi.single h (algebraMap R O b) := by
  funext g

  simp only [galElt, map_sum, Finset.sum_apply, galMap_tmul]
  have : ∀ i, σ (x i) * σ (act g (act h⁻¹ (y i))) = σ (x i * act (g * h⁻¹) (y i)) := by
    intro i; simp [map_mul]

  simp_rw [this, ← map_sum, hxy]
  by_cases hg : g = h
  · subst hg; simp
  · have : g * h⁻¹ ≠ 1 := fun e => hg (mul_inv_eq_one.mp e)
    simp [this, hg]

end GlobalTheory.GoodEtale
end
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem tensor_decomp_factorwise : ∀ (S F B : Type) [Field S] [CharZero S] [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B],
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, CharZero (L i))
      (_ : ∀ i, Algebra F (L i)) (Φ : S ⊗[ℚ] B ≃+* ((i : ι) → L i ⊗[F] B)) (ψ : S ⊗[ℚ] F ≃+* ((i : ι) → L i)),
      (∀ b : B, Φ ((1 : S) ⊗ₜ[ℚ] b) = fun i => (1 : L i) ⊗ₜ[F] b) ∧
      (∀ z : S ⊗[ℚ] F, Φ (Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom ℚ F B) z) =
        fun i => algebraMap (L i) (L i ⊗[F] B) (ψ z i)) := by
  intro S F B _ _ _ _ _ _ _ _ _
  haveI hEt : Algebra.Etale ℚ F := by
    haveI : Algebra.IsSeparable ℚ F := inferInstance
    haveI : Algebra.FormallyEtale ℚ F := Algebra.FormallyEtale.of_isSeparable ℚ F
    haveI : Algebra.FinitePresentation ℚ F := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    constructor <;> infer_instance
  haveI : Algebra.Etale S (S ⊗[ℚ] F) := Algebra.Etale.baseChange ℚ F S
  obtain ⟨I, hI, L, hL, hAL, e, -⟩ := (Algebra.Etale.iff_exists_algEquiv_prod S (S ⊗[ℚ] F)).mp this
  letI : Fintype I := Fintype.ofFinite I
  classical
  let ψ : S ⊗[ℚ] F ≃+* ((i : I) → L i) := e.toRingEquiv
  letI instF : ∀ i, Algebra F (L i) := fun i =>
    ((Pi.evalRingHom L i).comp (ψ.toRingHom.comp
      (Algebra.TensorProduct.includeRight : F →ₐ[ℚ] S ⊗[ℚ] F).toRingHom)).toAlgebra
  have hchar : ∀ i, CharZero (L i) := fun i =>
    charZero_of_injective_algebraMap (R := S) (algebraMap S (L i)).injective
  let φ : F ⊗[ℚ] S ≃ₐ[F] ((i : I) → L i) :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm ℚ F S).toRingEquiv.trans ψ) (fun x => by
      funext i
      rfl)
  let c : B ⊗[ℚ] S ≃ₐ[F] B ⊗[F] (F ⊗[ℚ] S) :=
    AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ F F B S).symm
      (by simp [Algebra.TensorProduct.one_def])
      (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp))
  let Φ : S ⊗[ℚ] B ≃+* ((i : I) → L i ⊗[F] B) :=
    (Algebra.TensorProduct.comm ℚ S B).toRingEquiv.trans <| c.toRingEquiv.trans <|
      (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[F] B) φ).toRingEquiv.trans <|
      (Algebra.TensorProduct.piRight F F B L).toRingEquiv.trans
      (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F B (L i)).toRingEquiv
  have hΦ : ∀ (s : S) (b : B), Φ (s ⊗ₜ b) = fun i => ψ (s ⊗ₜ 1) i ⊗ₜ[F] b := by
    intro s b
    have hc : c (b ⊗ₜ s) = b ⊗ₜ ((1 : F) ⊗ₜ s) :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul ℚ F F b s
    show (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F B (L i))
      ((Algebra.TensorProduct.piRight F F B L)
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[F] B) φ) (c (b ⊗ₜ s)))) = _
    rw [hc]
    rfl
  refine ⟨I, inferInstance, L, hL, hchar, instF, Φ, ψ, ?_, ?_⟩
  · intro b
    rw [hΦ]
    funext i
    rw [← Algebra.TensorProduct.one_def, map_one, Pi.one_apply]
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => funext i; simp
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy]
      funext i
      simp only [Pi.add_apply, map_add (f := _)]
    | tmul s f =>
      have key : ∀ i, (algebraMap F (L i) f) * ψ (s ⊗ₜ 1) i = ψ (s ⊗ₜ f) i := by
        intro i
        show ψ (1 ⊗ₜ f) i * ψ (s ⊗ₜ 1) i = _
        rw [← Pi.mul_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom', hΦ]
      funext i
      rw [Algebra.algebraMap_eq_smul_one f, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, key, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem injective_and_saturated_of_injective_mod_regular :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A B : Type) [CommRing A]
      [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] (f : R),
      f ∈ maximalIdeal R → IsSMulRegular B f → ∀ ψ : A →ₐ[R] B,
      (∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) →
        a ∈ (Ideal.span {f}).map (algebraMap R A)) →
      Function.Injective ψ ∧ ∀ b : B, f • b ∈ ψ.range → b ∈ ψ.range := by
  intro R _ _ _ A B _ _ _ _ _ f hf hreg ψ hψ

  have memA : ∀ a : A, a ∈ (Ideal.span {f}).map (algebraMap R A) → ∃ c : A, a = f • c := by
    intro a ha
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, hc⟩ := ha
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_comm]⟩
  have memB : ∀ b : B, f • b ∈ (Ideal.span {f}).map (algebraMap R B) := by
    intro b
    rw [Ideal.map_span, Set.image_singleton, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have key : ∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) → ∃ c : A, a = f • c :=
    fun a h => memA a (hψ a h)
  refine ⟨?_, ?_⟩
  ·
    set K : Submodule R A := LinearMap.ker ψ.toLinearMap with hK
    have hFG : K.FG := IsNoetherian.noetherian K
    have hle : K ≤ Ideal.span {f} • K := by
      intro a ha
      have ha0 : ψ a = 0 := ha
      obtain ⟨c, rfl⟩ := key a (by rw [ha0]; exact Submodule.zero_mem _)
      have hc : ψ c = 0 := by
        apply hreg
        change f • ψ c = f • (0 : B)
        rw [smul_zero, ← map_smul]
        exact ha0
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f) hc
    have hjac : Ideal.span {f} ≤ Ideal.jacobson (⊥ : Ideal R) := by
      refine le_trans ?_ (maximalIdeal_le_jacobson _)
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hf
    have hK0 : K = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ K hFG hle hjac
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ K := ha
    rw [hK0] at this
    exact (Submodule.mem_bot R).1 this
  · intro b ⟨a, ha'⟩
    have ha : ψ a = f • b := ha'
    obtain ⟨c, rfl⟩ := key a (by rw [ha]; exact memB b)
    refine ⟨c, ?_⟩
    apply hreg
    change f • ψ c = f • b
    rw [← map_smul, ha]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite

namespace GlobalTheory

theorem awayMap_bijective_of_range_eq_subalgebra :
    ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R B] (C : Subalgebra R B) (φ : A →+* B), Function.Injective φ → ∀ (_ : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B), φ a = b → (∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) → Function.Bijective (Localization.awayMap φ a) := by
  intro R A B _ _ _ _ C φ hφ hC a b hab hloc
  subst hab
  have hmem : ∀ y, φ y ∈ C := fun y => (hC _).2 ⟨y, rfl⟩
  let f : A →+* C := φ.codRestrict C.toSubsemiring hmem
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => hφ (congrArg Subtype.val h), fun c => ?_⟩
    obtain ⟨y, hy⟩ := (hC c.1).1 c.2
    exact ⟨y, Subtype.ext hy⟩
  let e : A ≃+* C := RingEquiv.ofBijective f hf
  have H : Submonoid.map e.toMonoidHom (Submonoid.powers a) = Submonoid.powers (f a) :=
    Submonoid.map_powers e.toMonoidHom a
  have h1 : Function.Bijective (Localization.awayMap f a) := by
    have hb := (IsLocalization.ringEquivOfRingEquiv (Localization.Away a)
      (Localization.Away (f a)) e H).bijective
    have key : ∀ z, Localization.awayMap f a z =
        IsLocalization.ringEquivOfRingEquiv (Localization.Away a) (Localization.Away (f a)) e H z := by
      intro z
      rw [IsLocalization.ringEquivOfRingEquiv_apply]
      rfl
    rw [show (Localization.awayMap f a : Localization.Away a → Localization.Away (f a)) = _ from funext key]
    exact hb
  have h2 : Localization.awayMap φ a =
      (Localization.awayMap C.val.toRingHom (f a)).comp (Localization.awayMap f a) := by
    simp only [Localization.awayMap, IsLocalization.Away.map]
    rw [IsLocalization.map_comp_map]
    rfl
  rw [h2]
  exact (hloc (hmem a)).comp h1

end GlobalTheory
end

section

namespace GlobalTheory.AdjoinAlgebraHomNonempty

theorem nonempty_algHom_adjoin (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω]
    [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S) (hh : ψ h ≠ 0) (T : Set F)
    (hT : ∀ x ∈ T, (h : F) * x ∈ S) : Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  have h0 : h ≠ 0 := fun e => hh (by rw [e, map_zero])
  have h0F : (h : F) ≠ 0 := fun e => h0 (Subtype.ext e)
  have hu : ∀ y : Submonoid.powers h, IsUnit (S.val y) := by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow]
    exact (IsUnit.mk0 _ h0F).pow n
  have hv : ∀ y : Submonoid.powers h, IsUnit (ψ y) := by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow]
    exact (IsUnit.mk0 _ hh).pow n
  let f : Localization.Away h →ₐ[k] F := IsLocalization.liftAlgHom (M := Submonoid.powers h) hu
  let g : Localization.Away h →ₐ[k] Ω := IsLocalization.liftAlgHom (M := Submonoid.powers h) hv
  have hf : ∀ s : S, f (algebraMap S (Localization.Away h) s) = (s : F) := fun s => by
    simp [f, IsLocalization.liftAlgHom_apply]
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (Submonoid.powers h) z
    have h1 := congrArg f hab
    rw [map_mul, hz, zero_mul, hf] at h1
    have ha : a = 0 := Subtype.ext h1.symm
    rw [ha, map_zero] at hab
    exact (IsLocalization.map_units (Localization.Away h) b).mul_left_eq_zero.mp hab
  have hle : Algebra.adjoin k T ≤ f.range := by
    refine Algebra.adjoin_le fun x hx => ?_
    obtain ⟨u, hu'⟩ := IsLocalization.map_units (Localization.Away h)
      (⟨h, Submonoid.mem_powers h⟩ : Submonoid.powers h)
    refine ⟨(↑u⁻¹ : Localization.Away h) * algebraMap S _ ⟨_, hT x hx⟩, ?_⟩
    apply mul_left_cancel₀ h0F
    have e : f u = (h : F) := by rw [hu']; exact hf h
    change (h : F) * f _ = _
    rw [map_mul, hf, ← mul_assoc]
    have e2 : (h : F) * f (↑u⁻¹ : Localization.Away h) = 1 := by
      rw [← e, ← map_mul, Units.mul_inv, map_one]
    rw [e2, one_mul]
  exact ⟨(g.comp (AlgEquiv.ofInjective f hinj).symm.toAlgHom).comp (Subalgebra.inclusion hle)⟩

end GlobalTheory.AdjoinAlgebraHomNonempty
end
