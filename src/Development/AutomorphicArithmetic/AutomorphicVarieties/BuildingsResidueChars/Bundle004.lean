module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Hi

private theorem spC_lim {A : Type} [CommRing A] (I : Ideal A) [IsPrecomplete I A] (x : ℕ → A)
    (h : ∀ k, x (k + 1) - x k ∈ I ^ k) : ∃ L, ∀ k, L - x k ∈ I ^ k := by
  have h1 : ∀ m n, m ≤ n → x n - x m ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem (Ideal.pow_le_pow_right hmn (h n)) ih
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance (f := x) (fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
    exact neg_mem (h1 m n hmn))
  refine ⟨L, fun k => ?_⟩
  have := hL k
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  rw [← neg_sub]
  exact neg_mem this

private theorem spC_eq {A : Type} [CommRing A] (I : Ideal A) [IsHausdorff I A] {x y : A}
    (h : ∀ k, x - y ∈ I ^ k) : x = y := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact h k

theorem UpperTheory.exists_adic_limit_mem_automorphicSpace :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) (a : ℕ → X.Fn A m), (∀ k, a k ∈ X.Sp τ θ U) → (∀ k, a (k + 1) - a k ∈ X.valIn A m k) → ∃ L ∈ X.Sp τ θ U, ∀ k, L - a k ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ U a ha hc
  have hv : ∀ (k : ℕ) (f : X.Fn A m), f ∈ X.valIn A m k ↔ ∀ g i, f g i ∈ maximalIdeal A ^ k := by
    intro k f
    simp [Frame.valIn, Submodule.mem_pi]
  choose L hL using fun g i => spC_lim (maximalIdeal A) (fun k => a k g i) fun k => (hv _ _).1 (hc k) g i
  have key : ∀ φ ψ : X.Fn A m →ₗ[A] X.Fn A m, (∀ k, ∀ f ∈ X.valIn A m k, φ f ∈ X.valIn A m k) →
      (∀ k, ∀ f ∈ X.valIn A m k, ψ f ∈ X.valIn A m k) → (∀ k, φ (a k) = ψ (a k)) → φ L = ψ L := by
    intro φ ψ h1 h2 h3
    funext g i
    refine spC_eq (maximalIdeal A) fun k => ?_
    have hk : L - a k ∈ X.valIn A m k := (hv _ _).2 fun g i => hL g i k
    have := sub_mem (h1 k _ hk) (h2 k _ hk)
    rw [map_sub, map_sub, h3 k, sub_sub_sub_cancel_right] at this
    exact (hv _ _).1 this g i
  have hrp : ∀ b k, ∀ f ∈ X.valIn A m k, X.rp A m b f ∈ X.valIn A m k := fun b k f hf =>
    (hv _ _).2 fun g i => (hv _ _).1 hf _ i
  refine ⟨L, ⟨⟨fun γ g => ?_, fun x hx => ?_, fun t => ?_, fun k => ?_⟩, fun u hu => ?_⟩,
    fun k => (hv _ _).2 fun g i => hL g i k⟩
  · funext i
    refine spC_eq (maximalIdeal A) fun k => ?_
    have := sub_mem (hL (X.glob γ * g) i k) (hL g i k)
    rwa [(ha k).1.1 γ g, sub_sub_sub_cancel_right] at this
  · exact key _ LinearMap.id (hrp x) (fun _ _ h => h) fun k => (ha k).1.2.1 x hx
  · exact key _ ((((θ t)⁻¹ : Aˣ) : A) • LinearMap.id) (hrp t) (fun _ _ h => Submodule.smul_mem _ _ h)
      fun k => (ha k).1.2.2.1 t
  · obtain ⟨c, h⟩ := (ha k).1.2.2.2 k
    refine ⟨c, fun y hy g i => ?_⟩
    have := add_mem (sub_mem (hL (g * (1, y)) i k) (hL g i k)) (h y hy g i)
    convert this using 1
    ring
  · refine key _ LinearMap.id (fun k f hf => (hv _ _).2 fun g i => ?_) (fun _ _ h => h) fun k => (ha k).2 u hu
    rw [Frame.ra_apply]
    simp only [mulVec, dotProduct]
    exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ((hv _ _).1 hf _ j)
end

section

open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.exists_linear_section_automorphicFunctions_of_free :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub), X.Free τ θ U → ∀ (c N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) → ∀ tt : Gp → X.I.T, (∀ b ∈ X.I.Iw 0, ∀ s : X.I.T, tt (s * b) = s * tt b) → ∃ s : (Fin N × Fin m → A) →ₗ[A] X.Fn A m, ∀ v γ i, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, s v (X.glob γ * x i * ((u : Ga), b)) = (((θ (tt b))⁻¹ : Aˣ) : A) • ((τ u⁻¹ : Matrix (Fin m) (Fin m) A) *ᵥ fun j => v (i, j)) := by
  intro Γ Ga Gp _ _ _ X A _ m τ θ U hF c N x hcov hsep tt htt
  choose γ0 i0 u0 hu0 b0 hb0 hg using hcov
  have hle : X.I.Iw c ≤ X.I.Iw 0 := sup_le_sup_left (X.I.Nm_anti (Nat.zero_le c)) _
  refine ⟨{ toFun := fun v g => (((θ (tt (b0 g)))⁻¹ : Aˣ) : A) •
              ((τ (u0 g)⁻¹ : Matrix (Fin m) (Fin m) A) *ᵥ fun j => v (i0 g, j))
            map_add' := fun v w => ?_
            map_smul' := fun a v => ?_ }, fun v γ i u hu b hb => ?_⟩
  · funext g
    rw [Pi.add_apply, ← smul_add, ← mulVec_add]
    rfl
  · funext g
    rw [Pi.smul_apply, RingHom.id_apply, smul_comm a, ← mulVec_smul _ a]
    rfl
  · have h := hg (X.glob γ * x i * ((u : Ga), b))
    have hu1 := hu0 (X.glob γ * x i * ((u : Ga), b))
    have hb1 := hb0 (X.glob γ * x i * ((u : Ga), b))
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    generalize γ0 (X.glob γ * x i * ((u : Ga), b)) = γ1 at h
    generalize i0 (X.glob γ * x i * ((u : Ga), b)) = i1 at h ⊢
    generalize u0 (X.glob γ * x i * ((u : Ga), b)) = u1 at h hu1 ⊢
    generalize b0 (X.glob γ * x i * ((u : Ga), b)) = b1 at h hb1 ⊢
    have hw : ((((u1 * u⁻¹ : X.Ub) : Ga), b1 * b⁻¹) : Ga × Gp) = ((u1 : Ga), b1) * ((u : Ga), b)⁻¹ := rfl
    have hwU : u1 * u⁻¹ ∈ U := mul_mem hu1 (inv_mem hu)
    have hwI : b1 * b⁻¹ ∈ X.I.Iw c := mul_mem hb1 (inv_mem hb)
    have hi : i1 = i := by
      refine hsep i1 i (γ⁻¹ * γ1) _ hwU _ hwI ?_
      rw [hw, map_mul, map_inv, ← mul_assoc, mul_assoc (X.glob γ)⁻¹, mul_assoc (X.glob γ)⁻¹, ← h]
      group
    subst hi
    obtain ⟨-, hs, he⟩ := hF (x i1) (γ1⁻¹ * γ) _ hwU _ (hle hwI) (by
      rw [hw, map_mul, map_inv, mul_assoc, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← h]
      group)
    have ht : tt b1 = ⟨b1 * b⁻¹, hs⟩ * tt b := by
      rw [← htt b (hle hb) ⟨b1 * b⁻¹, hs⟩]
      simp
    have hτ : (τ u1⁻¹ : Matrix (Fin m) (Fin m) A) =
        (θ ⟨b1 * b⁻¹, hs⟩ : A) • (τ u⁻¹ : Matrix (Fin m) (Fin m) A) := by
      have e : u⁻¹ = u1⁻¹ * (u1 * u⁻¹) := by group
      rw [e, map_mul, Units.val_mul, ← Matrix.mul_smul, he, Matrix.mul_one]
    rw [ht, hτ, map_mul, smul_mulVec, smul_smul, ← Units.val_mul]
    congr 2
    rw [mul_inv, mul_right_comm, inv_mul_cancel, one_mul]
end

section

theorem UpperTheory.orbitalFiber_support_finite :
    UpperTheory.V.Z.Sym.Glob.Fib.SuppFin := by
  intro Γ G V _ _ _ _ B hB h0 f hf g
  have hK : Finite ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι) := by
    have h := hB.stab g
    rw [h0, Subgroup.relIndex_bot_left] at h
    exact Nat.finite_of_card_ne_zero h
  have hKs : (((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι : Subgroup Γ) : Set Γ).Finite := Set.toFinite _
  have hfib : ∀ x : G ⧸ B.U, ((fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) ⁻¹' {x}).Finite := by
    intro x
    rcases Set.eq_empty_or_nonempty ((fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) ⁻¹' {x}) with he | ⟨γ₀, h₀⟩
    · rw [he]; exact Set.finite_empty
    · refine (hKs.image (fun k => γ₀ * k)).subset fun γ hγ => ⟨γ₀⁻¹ * γ, ?_, by simp⟩
      have e : ((g⁻¹ * B.ι γ₀ * g : G) : G ⧸ B.U) = ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U) :=
        (Set.mem_singleton_iff.1 h₀).trans (Set.mem_singleton_iff.1 hγ).symm
      refine ⟨_, QuotientGroup.eq.1 e, ?_⟩
      simp [mul_assoc]
  refine (hf.fin.preimage' (f := fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) fun x _ => hfib x).subset ?_
  intro γ hγ h
  apply hγ
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U (g⁻¹ * B.ι γ * g)
  have hr := hf.right u (g⁻¹ * B.ι γ * g)
  change f (((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U).out) = 0 at h
  change f (g⁻¹ * B.ι γ * g * u) = _ at hr
  rw [hu, hr] at h
  exact (mul_eq_zero.1 h).resolve_left (Units.ne_zero _)
end

section

open MulAction in
theorem UpperTheory.orbitalFiber_of_bot :
    UpperTheory.V.Z.Sym.Glob.Fib.Bot := by
  intro H Y _ _ H₀ k
  have hmul : ∀ (a : ℂ) (g : orbitRel.Quotient H Y → ℂ), ∑ᶠ o, a * g o = a * ∑ᶠ o, g o :=
    fun a g => by simpa only [smul_eq_mul] using (smul_finsum a g).symm
  refine ⟨fun a => ?_, fun hc htriv => ?_⟩
  · unfold UpperTheory.V.Z.Sym.gq
    rw [← hmul]
    exact finsum_congr fun o => mul_div_assoc _ _ _
  · unfold UpperTheory.V.Z.Sym.gq
    rw [← hmul]
    refine finsum_congr fun o => ?_
    have hle : H₀ ≤ stabilizer H o.out := fun z hz => htriv z hz _
    have h := Subgroup.relIndex_mul_relIndex ⊥ H₀ (stabilizer H o.out) bot_le hle
    rw [Subgroup.relIndex_bot_left] at h
    have hc' : (Nat.card H₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc
    rw [← h, Nat.cast_mul, ← mul_div_assoc, mul_div_mul_left _ _ hc']
end

section

namespace UpperTheory

private lemma relIndex_normal_sup {Γ : Type} [Group Γ] (N A C : Subgroup Γ) [N.Normal] (hN : N ≤ A)
    (h : A.relIndex C ≠ 0) : A.relIndex (N ⊔ C) ≠ 0 := by
  have hA : (A.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = A := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hN]
  have key : ∀ K : Subgroup Γ, A.relIndex K = (A.map (QuotientGroup.mk' N)).relIndex (K.map (QuotientGroup.mk' N)) := by
    intro K
    rw [← Subgroup.relIndex_comap, hA]
  have hm : (N ⊔ C).map (QuotientGroup.mk' N) = C.map (QuotientGroup.mk' N) := by
    rw [Subgroup.map_sup]
    have : N.map (QuotientGroup.mk' N) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [this, bot_sup_eq]
  rw [key, hm, ← key]
  exact h

theorem orbitalFiber_index_finite : V.Z.Sym.Glob.Fib.IndexFin := by
  intro Γ G _ _ ι S U' Γ₁ Γ₀ hS hΓ₁ hT h0
  obtain ⟨T, hT⟩ := hT
  have hAC : (Γ₁ ⊔ Γ₀).relIndex (U'.comap ι) ≠ 0 := by
    intro h
    apply h0
    have := Subgroup.relIndex_dvd_of_le_left (U'.comap ι) (le_sup_right : Γ₀ ≤ Γ₁ ⊔ Γ₀)
    rw [h] at this
    exact Nat.eq_zero_of_zero_dvd this
  have h1 : (Γ₁ ⊔ Γ₀).relIndex (Γ₁ ⊔ U'.comap ι) ≠ 0 :=
    relIndex_normal_sup Γ₁ _ _ le_sup_left hAC
  have pick : ∀ b : ((S ⊔ U').comap ι : Subgroup Γ), ∃ t, t ∈ T ∧ ∃ h ∈ Γ₁, ∃ u ∈ U',
      ι (b : Γ) = ι h * t * u := by
    intro b
    have hb : ι (b : Γ) ∈ S ⊔ U' := b.2
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hb
    obtain ⟨s, hs, u, hu, e⟩ := hb
    obtain ⟨h, hh, t, ht, u₂, hu₂, rfl⟩ := hT s hs
    exact ⟨t, ht, h, hh, u₂ * u, U'.mul_mem hu₂ hu, by rw [← e]; group⟩
  choose f hfT hf using pick
  have h2 : (Γ₁ ⊔ U'.comap ι).relIndex ((S ⊔ U').comap ι) ≠ 0 := by
    have inj : Function.Injective
        (fun q : ((S ⊔ U').comap ι : Subgroup Γ) ⧸ (Γ₁ ⊔ U'.comap ι).subgroupOf ((S ⊔ U').comap ι) =>
          (⟨f q.out, hfT _⟩ : T)) := by
      intro q q' hq
      have hq' : f q.out = f q'.out := congrArg Subtype.val hq
      rw [← q.out_eq', ← q'.out_eq', QuotientGroup.eq, Subgroup.mem_subgroupOf]
      generalize q.out = a at hq'
      generalize q'.out = b at hq'
      obtain ⟨h, hh, u, hu, ha⟩ := hf a
      obtain ⟨h', hh', u', hu', hb⟩ := hf b
      rw [← hq'] at hb
      have hx : (a : Γ)⁻¹ * (h' * h⁻¹) * a ∈ Γ₁ := by
        simpa using hΓ₁.conj_mem (h' * h⁻¹) (Γ₁.mul_mem hh' (Γ₁.inv_mem hh)) (a : Γ)⁻¹
      have hc : (a : Γ)⁻¹ * h * h'⁻¹ * b ∈ U'.comap ι := by
        have : ι ((a : Γ)⁻¹ * h * h'⁻¹ * b) = u⁻¹ * u' := by
          simp only [map_mul, map_inv, ha, hb]
          group
        rw [Subgroup.mem_comap, this]
        exact U'.mul_mem (U'.inv_mem hu) hu'
      have e : (((a⁻¹ * b : ((S ⊔ U').comap ι : Subgroup Γ))) : Γ)
          = ((a : Γ)⁻¹ * (h' * h⁻¹) * a) * ((a : Γ)⁻¹ * h * h'⁻¹ * b) := by
        push_cast
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hc)
    haveI := Finite.of_injective _ inj
    exact Subgroup.index_ne_zero_of_finite
  exact Subgroup.relIndex_ne_zero_trans h1 h2

end UpperTheory
end

section

open MulAction

private theorem fib_abs {O I : Type} {P : I → Type} (F : ∀ i, P i → O) (S : ∀ i, Set (P i)) (B : Set O) (hB : B.Finite)
    (w : O → ℂ) (wi : ∀ i, P i → ℂ) (hw : ∀ o, o ∉ B → w o = 0) (hwi : ∀ i p, p ∉ S i → wi i p = 0)
    (hF : ∀ i, ∀ p ∈ S i, F i p ∈ B ∧ wi i p = w (F i p)) (hs : ∀ o ∈ B, ∃ i, ∃ p ∈ S i, F i p = o)
    (hij : ∀ i j, ∀ p ∈ S i, ∀ q ∈ S j, F i p = F j q → i = j) (hinj : ∀ i, Set.InjOn (F i) (S i)) :
    ∑ᶠ o, w o = ∑ᶠ i, ∑ᶠ p, wi i p := by
  classical
  have h1 : ∀ i, ∑ᶠ p, wi i p = ∑ᶠ o ∈ F i '' S i, w o := by
    intro i
    rw [finsum_mem_image (hinj i), finsum_mem_def]
    congr 1
    funext p
    by_cases hp : p ∈ S i
    · rw [Set.indicator_of_mem hp, (hF i p hp).2]
    · rw [Set.indicator_of_notMem hp, hwi i p hp]
  have hsub : ∀ i, F i '' S i ⊆ B := by
    rintro i _ ⟨p, hp, rfl⟩
    exact (hF i p hp).1
  have hI : {i | (S i).Nonempty}.Finite := by
    let g : {i | (S i).Nonempty} → B := fun i => ⟨F i.1 i.2.some, (hF _ _ i.2.some_mem).1⟩
    have hg : Function.Injective g := fun i j h =>
      Subtype.ext (hij _ _ _ i.2.some_mem _ j.2.some_mem (congrArg Subtype.val h))
    haveI := hB.to_subtype
    exact Set.finite_coe_iff.1 (Finite.of_injective g hg)
  have hU : B = ⋃ i ∈ {i | (S i).Nonempty}, F i '' S i := by
    ext o
    simp only [Set.mem_iUnion]
    constructor
    · intro ho
      obtain ⟨i, p, hp, rfl⟩ := hs o ho
      exact ⟨i, ⟨p, hp⟩, p, hp, rfl⟩
    · rintro ⟨i, _, ho⟩
      exact hsub i ho
  have h2 : ∑ᶠ o, w o = ∑ᶠ o ∈ B, w o := by
    rw [finsum_mem_def]
    congr 1
    funext o
    by_cases ho : o ∈ B
    · rw [Set.indicator_of_mem ho]
    · rw [Set.indicator_of_notMem ho, hw o ho]
  rw [h2, hU, finsum_mem_biUnion _ hI (fun i _ => hB.subset (hsub i)), finsum_mem_def]
  · congr 1
    funext i
    by_cases hi : i ∈ {i | (S i).Nonempty}
    · rw [Set.indicator_of_mem hi, h1]
    · rw [Set.indicator_of_notMem hi, h1]
      have : S i = ∅ := Set.not_nonempty_iff_eq_empty.1 hi
      rw [this, Set.image_empty, finsum_mem_empty]
  · intro i _ j _ hne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, h⟩
    exact hne (hij i j p hp q hq h.symm)

private theorem rel_smul {H X : Type} [Group H] [MulAction H X] (H₀ : Subgroup H) (hn : H₀.Normal) (h : H) (x : X) :
    H₀.relIndex (stabilizer H (h • x)) = H₀.relIndex (stabilizer H x) := by
  have h0 : H₀.map (MulAut.conj h).toMonoidHom = H₀ := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hn.conj_mem y hy h
    · intro hz
      refine ⟨h⁻¹ * z * h, ?_, ?_⟩
      · simpa using hn.conj_mem z hz h⁻¹
      · simp [mul_assoc]
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← h0]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj h).injective

private theorem out_mk {H X : Type} [Group H] [MulAction H X] (x : X) :
    ∃ h : H, (Quotient.mk (orbitRel H X) x).out = h • x := by
  have : (Quotient.mk (orbitRel H X) x).out ∈ orbit H x :=
    orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (orbitRel H X) x)))
  obtain ⟨h, hh⟩ := this
  exact ⟨h, hh.symm⟩

private theorem mk_smul {H X : Type} [Group H] [MulAction H X] (h : H) (x : X) :
    Quotient.mk (orbitRel H X) (h • x) = Quotient.mk (orbitRel H X) x :=
  Quotient.sound (orbitRel_apply.2 ⟨h, rfl⟩)

theorem UpperTheory.orbitalFiber_decomposition :
    UpperTheory.V.Z.Sym.Glob.Fib.Decomp := by
  intro H X I _ _ H₀ k Hi Yi _ _ φ e ki hn hk hT he hinj hki hke hs hu
  unfold UpperTheory.V.Z.Sym.gq
  have hex : ∀ x x' : X, Quotient.mk (orbitRel H X) x' = Quotient.mk (orbitRel H X) x → ∃ h : H, h • x = x' :=
    fun x x' h => orbitRel_apply.1 (Quotient.exact h)
  refine fib_abs (fun i (p : orbitRel.Quotient (Hi i) (Yi i)) => (Quotient.mk (orbitRel H X) (e i p.out) : orbitRel.Quotient H X))
    (fun i => {p | ki i p.out ≠ 0}) {o | k o.out ≠ 0} ?_ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨T, hT⟩ := hT
    refine (T.finite_toSet.image (Quotient.mk (orbitRel H X))).subset fun o ho => ?_
    obtain ⟨h, s, hs, ho⟩ := hT _ ho
    refine ⟨s, hs, ?_⟩
    rw [← mk_smul h s, ← ho]
    exact Quotient.out_eq o
  · intro o ho
    have : k o.out = 0 := not_not.1 ho
    rw [this, zero_div]
  · intro i p hp
    have : ki i p.out = 0 := not_not.1 hp
    rw [this, zero_div]
  · intro i p hp
    have hp' : ki i p.out ≠ 0 := hp
    obtain ⟨h, hh⟩ := out_mk (H := H) (e i p.out)
    have hv : k (Quotient.mk (orbitRel H X) (e i p.out)).out = ki i p.out := by rw [hh, hk, hke i _ hp']
    refine ⟨fun h0 => hp' (hv ▸ h0), ?_⟩
    have hst : (stabilizer (Hi i) p.out).map (φ i) = stabilizer H (e i p.out) := by
      ext g
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [mem_stabilizer_iff, ← he, mem_stabilizer_iff.1 ha]
      · intro hg
        obtain ⟨_, a, rfl⟩ := hu i i _ _ g hp' hp' hg
        refine ⟨a, hinj i ?_, rfl⟩
        rw [he]
        exact hg
    show _ = k (Quotient.mk (orbitRel H X) (e i p.out)).out /
      (H₀.relIndex (stabilizer H (Quotient.mk (orbitRel H X) (e i p.out)).out) : ℂ)
    rw [hv, hh, rel_smul H₀ hn, Subgroup.relIndex_comap, hst]
  · intro o ho
    obtain ⟨i, y, h, hy, hx⟩ := hs _ ho
    obtain ⟨a, ha⟩ := out_mk (H := Hi i) y
    refine ⟨i, Quotient.mk (orbitRel (Hi i) (Yi i)) y, ?_, ?_⟩
    · show ki i (Quotient.mk (orbitRel (Hi i) (Yi i)) y).out ≠ 0
      rwa [ha, hki]
    · show Quotient.mk (orbitRel H X) (e i (Quotient.mk (orbitRel (Hi i) (Yi i)) y).out) = o
      rw [ha, he, mk_smul, ← mk_smul h, ← hx]
      exact Quotient.out_eq o
  · intro i j p hp q hq hpq
    obtain ⟨h, hh⟩ := hex _ _ hpq.symm
    exact (hu i j _ _ h hp hq hh).1
  · intro i p hp q hq hpq
    obtain ⟨h, hh⟩ := hex _ _ (Eq.symm hpq)
    obtain ⟨_, a, rfl⟩ := hu i i _ _ h hp hq hh
    rw [← he] at hh
    have h3 := hinj i hh
    rw [← Quotient.out_eq p, ← Quotient.out_eq q, ← h3]
    exact (mk_smul a _).symm
end

section

namespace UpperTheory

theorem orbitalFiber_stabilizer_finite : UpperTheory.V.Z.Sym.Glob.Fib.StabFin := by
  intro H G _ _ S U U' ι x hS hidx hfin
  let ψ : H →* G := (MulAut.conj x⁻¹).toMonoidHom.comp (S.subtype.comp ι)
  have hψ : ∀ h, ψ h = x⁻¹ * ι h * x := fun h => by simp [ψ]
  have hB : (U' ⊓ S).comap ψ = U'.comap ψ := by
    ext h
    simp only [Subgroup.mem_comap, Subgroup.mem_inf, and_iff_left_iff_imp]
    intro _
    rw [hψ]
    simpa using hS.conj_mem _ (ι h).2 x⁻¹
  have h1 : (U.comap ψ).relIndex (U'.comap ψ) ≠ 0 := by
    rw [← hB]
    exact Subgroup.relIndex_comap_ne_zero ψ hidx
  have hA : Finite (U.comap ψ) := by
    have : ((U.comap ψ : Subgroup H) : Set H).Finite := by
      convert hfin using 1
      ext h
      simp [hψ]
    exact this.to_subtype
  have hA' : Finite ((U.comap ψ).subgroupOf (U'.comap ψ)) :=
    Finite.of_injective (fun a => (⟨a.1.1, a.2⟩ : U.comap ψ)) (fun a b hab => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : U.comap ψ => (z : H)) hab)
  have hq : Finite ((U'.comap ψ) ⧸ (U.comap ψ).subgroupOf (U'.comap ψ)) :=
    Nat.finite_of_card_ne_zero h1
  have hfB : Finite (U'.comap ψ) :=
    Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup
      (s := (U.comap ψ).subgroupOf (U'.comap ψ))).symm
  have : ((U'.comap ψ : Subgroup H) : Set H).Finite := Set.toFinite _
  convert this using 1
  ext h
  simp [hψ]

end UpperTheory
end
