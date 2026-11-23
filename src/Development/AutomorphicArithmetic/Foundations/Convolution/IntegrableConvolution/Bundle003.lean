module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TrDefs
public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped TensorProduct
open PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

private theorem orderOf_gen (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) : orderOf σ = m + 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank, hm]

private theorem det_ne (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) (b : Module.Basis (Fin (m + 1)) F E) :
    (Matrix.of fun (i j : Fin (m + 1)) => (σ ^ (i : ℕ)) (b j)).det ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.DeterminantNonzero.det_ne σ hσ hm b

variable {A : Type} [CommRing A] [Algebra F A]

private noncomputable def phi (σ : E ≃ₐ[F] E) (p : E →ₐ[F] A) (m : ℕ) : E ⊗[F] A →ₐ[F] (Fin (m + 1) → A) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom F _ fun i : Fin (m + 1) => p.comp ((σ ^ (i : ℕ) : E ≃ₐ[F] E) : E →ₐ[F] E))
    (Pi.algHom F _ fun _ => AlgHom.id F A)

private theorem phi_tmul (σ : E ≃ₐ[F] E) (p : E →ₐ[F] A) (m : ℕ) (x : E) (a : A) (i : Fin (m + 1)) :
    phi σ p m (x ⊗ₜ a) i = p ((σ ^ (i : ℕ)) x) * a := by
  simp [phi]

private theorem phi_bij (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) (p : E →ₐ[F] A) : Function.Bijective (phi σ p m) := by
  let b : Module.Basis (Fin (m + 1)) F E := Module.finBasisOfFinrankEq F E hm
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) E := Matrix.of fun i j => (σ ^ (i : ℕ)) (b j)
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.2 (det_ne σ hσ hm b)
  let N := M⁻¹
  have hMN : M * N = 1 := Matrix.mul_nonsing_inv _ hunit
  have hNM : N * M = 1 := Matrix.nonsing_inv_mul _ hunit
  let Ψ : (Fin (m + 1) → A) → E ⊗[F] A := fun f => ∑ j, b j ⊗ₜ[F] (∑ i, p (N j i) * f i)
  have hr : Function.RightInverse Ψ (phi σ p m) := by
    intro f
    funext k

    simp only [Ψ, map_sum, Finset.sum_apply, phi_tmul]
    have h1 : ∀ i, ∑ j, p ((σ ^ (k : ℕ)) (b j)) * p (N j i) = if k = i then 1 else 0 := fun i => by
      have h2 := congrArg p (congrFun (congrFun hMN k) i)

      simp only [Matrix.mul_apply, Matrix.one_apply, M, Matrix.of_apply, map_sum, map_mul] at h2
      rw [h2]
      split_ifs <;> simp
    calc _ = ∑ i, (∑ j, p ((σ ^ (k : ℕ)) (b j)) * p (N j i)) * f i := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = f k := by
          simp only [h1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hadd : ∀ f g, Ψ (f + g) = Ψ f + Ψ g := fun f g => by
    simp only [Ψ, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.tmul_add]
  have hl : Function.LeftInverse Ψ (phi σ p m) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [Ψ]
    | add s t hs ht => rw [map_add (f := _), hadd, hs, ht]
    | tmul x a =>
      let c : Fin (m + 1) → E := fun l => algebraMap F E (b.repr x l)
      have hx : (fun i : Fin (m + 1) => (σ ^ (i : ℕ)) x) = M.mulVec c := by
        funext i
        conv_lhs => rw [← b.sum_repr x]

        rw [map_sum]
        simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, c]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, Algebra.smul_def, mul_comm]
      have hc : ∀ j, ∑ i, N j i * (σ ^ (i : ℕ)) x = c j := fun j => by
        have : N.mulVec (fun i : Fin (m + 1) => (σ ^ (i : ℕ)) x) = c := by
          rw [hx, Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
        exact congrFun this j
      have h3 : ∀ j, ∑ i, p (N j i) * (p ((σ ^ (i : ℕ)) x) * a) = b.repr x j • a := fun j => by
        calc _ = p (∑ i, N j i * (σ ^ (i : ℕ)) x) * a := by

              simp only [map_sum, map_mul, Finset.sum_mul, mul_assoc]
          _ = _ := by rw [hc]; simp only [c, p.commutes, Algebra.smul_def]
      simp only [Ψ, phi_tmul, h3, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul, b.sum_repr]
  exact ⟨hl.injective, hr.surjective⟩

private theorem phi_shift (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) (p : E →ₐ[F] A) (t : E ⊗[F] A) (i : Fin (m + 1)) :
    phi σ p m (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) t) i = phi σ p m t (i + 1) := by
  have h1 : σ ^ (m + 1) = 1 := by rw [← orderOf_gen σ hσ hm]; exact pow_orderOf_eq_one σ
  have hv : ((i + 1 : Fin (m + 1)) : ℕ) = ((i : ℕ) + 1) % (m + 1) := by simp [Fin.val_add]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add (f := _), Pi.add_apply, hs, ht]
  | tmul x a =>
    rw [Algebra.TensorProduct.map_tmul, phi_tmul, phi_tmul, hv, ← pow_eq_pow_mod _ h1, pow_succ]
    rfl

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.galSplit :
    UpperTheory.ConvolutionTheory.L1.GalSplit := by
  intro F E _ _ _ _ _ _ σ hσ m hm A B _ _ _ _ e₀ p
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  refine ⟨e₀.symm.toRingEquiv.trans (RingEquiv.ofBijective (phi σ p m) (phi_bij σ hσ hm p)),
    fun x a i => ?_, fun b i => ?_⟩
  · show phi σ p m (e₀.symm (e₀ (x ⊗ₜ a))) i = _
    rw [AlgEquiv.symm_apply_apply, phi_tmul]
  · show phi σ p m (e₀.symm (galOf e₀ σ b)) i = phi σ p m (e₀.symm b) (i + 1)
    rw [← phi_shift σ hσ hm p]
    have h : e₀.symm (galOf e₀ σ b) =
        Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) (e₀.symm b) :=
      e₀.symm_apply_apply _
    rw [h]
end

section

private theorem UpperTheory.ConvolutionTheory.L1.simple_of_prime (R : Type) [Ring R] [Nontrivial R] [IsArtinianRing R]
    (h : ∀ I : Ideal R, I.IsTwoSided → ∀ r : R, (∀ x ∈ I, x * r = 0) → I = ⊥ ∨ r = 0) : IsSimpleRing R := by
  have hJ : Ring.jacobson R = ⊥ := by
    by_contra hne
    obtain ⟨n, hn⟩ : IsNilpotent (Ring.jacobson R) := IsSemiprimaryRing.isNilpotent
    have key : ∀ n : ℕ, Ring.jacobson R ^ n ≠ ⊥ := by
      intro n
      induction n with
      | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; exact top_ne_bot
      | succ k ih =>
        intro hk
        apply ih
        rw [eq_bot_iff]
        intro r hr
        rcases h (Ring.jacobson R) inferInstance r (fun x hx => by
          have : x * r ∈ Ring.jacobson R ^ (k + 1) := by
            rw [Ideal.IsTwoSided.pow_succ]
            exact Ideal.mul_mem_mul hx hr
          rw [hk] at this
          exact this) with h1 | h1
        · exact absurd h1 hne
        · exact h1
    exact key n hn
  haveI : IsSemisimpleRing R := IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr hJ
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I.asIdeal
  rcases h I.asIdeal inferInstance (1 - e) (fun x hx => by
    rw [hI, Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [mul_assoc, mul_sub, mul_one, he.eq, sub_self, mul_zero]) with h1 | h1
  · left
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ I.asIdeal := hx
    rw [h1] at this
    exact this
  · right
    have h2 : e ∈ I.asIdeal := by rw [hI]; exact Ideal.subset_span rfl
    rw [← sub_eq_zero.mp h1] at h2
    exact I.one_mem_iff.mp h2

theorem UpperTheory.ConvolutionTheory.L1.matImage :
    UpperTheory.ConvolutionTheory.L1.MatImage := by
  intro A W _ _ _ _ _ _ ρ B hB hirr
  haveI : FiniteDimensional ℂ ρ.range :=
    FiniteDimensional.of_injective ρ.range.val.toLinearMap Subtype.val_injective
  haveI : IsArtinianRing ρ.range := IsArtinianRing.of_finite ℂ _
  haveI : IsSimpleRing ρ.range := by
    refine UpperTheory.ConvolutionTheory.L1.simple_of_prime _ fun I hI r hr => ?_
    let P : Submodule ℂ W :=
      { carrier := {w | ∀ x ∈ I, (x : Module.End ℂ W) w = 0}
        add_mem' := fun {a b} ha hb x hx => by rw [map_add (f := _), ha x hx, hb x hx, add_zero]
        zero_mem' := fun x _ => map_zero _
        smul_mem' := fun c w hw x hx => by rw [map_smul, hw x hx, smul_zero] }
    rcases hirr P (fun a w hw x hx => hw (x * ⟨ρ a, a, rfl⟩) (I.mul_mem_right _ hx))
      (fun b hb w hw x hx => by
        have h0 := hw x hx
        obtain ⟨_, a, rfl⟩ := x
        have h1 : (ρ a * b) w = (b * ρ a) w := by rw [(hB a b hb).eq]
        change ρ a w = 0 at h0
        change ρ a (b w) = 0
        rw [Module.End.mul_apply, Module.End.mul_apply, h0, map_zero] at h1
        exact h1) with h1 | h1
    · right
      ext w
      have : (r : Module.End ℂ W) w ∈ P := fun x hx => by
        have := congrArg (fun y : ρ.range => (y : Module.End ℂ W) w) (hr x hx)
        simpa using this
      rw [h1] at this
      simpa using this
    · left
      rw [eq_bot_iff]
      intro x hx
      have : x = 0 := by
        ext w
        have : w ∈ P := by rw [h1]; trivial
        simpa using this x hx
      exact this
  obtain ⟨n, hn, h⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed ℂ ρ.range
  exact ⟨n, Nat.pos_of_ne_zero hn.out, h⟩
end

section

open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C

private lemma UpperTheory.ConvolutionTheory.L1.cutIrr_prod {Γ G H : Type} [Group Γ] [TopologicalSpace Γ] [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (E : H →L[ℂ] H) {m : ℕ} (ι : Fin (m + 1) → G →* Γ)
    (hE : ∀ i g v, E (π (ι i g) v) = π (ι i g) (E v)) (P : Submodule ℂ H)
    (hP : ∀ i g, ∀ v ∈ P, π (ι i g) v ∈ P) (l : List Γ) (hl : ∀ x ∈ l, ∃ i g, x = ι i g) :
    (∀ v, E (π l.prod v) = π l.prod (E v)) ∧ ∀ v ∈ P, π l.prod v ∈ P := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨i, g, rfl⟩ := hl a (by simp)
    obtain ⟨h1, h2⟩ := ih (fun x hx => hl x (by simp [hx]))
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [List.prod_cons, UnitaryRep.map_mul_apply, UnitaryRep.map_mul_apply, hE, h1]
    · rw [List.prod_cons, UnitaryRep.map_mul_apply]
      exact hP _ _ _ (h2 v hv)

theorem UpperTheory.ConvolutionTheory.L1.cutIrr :
    UpperTheory.ConvolutionTheory.L1.CutIrr := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U h
  have hfix : ∀ v, v ∈ eigIn V E 1 ↔ v ∈ V ∧ E v = v := by
    intro v
    simp [eigIn, Module.End.mem_eigenspace_iff]
  refine ⟨?_, ?_, ?_⟩
  · have hset : (eigIn V E 1 : Set H) = (V : Set H) ∩ {v | E v = v} := by
      ext v
      exact hfix v
    rw [hset]
    exact h.summand.closed.inter (isClosed_eq E.continuous continuous_id)
  · intro i g v hv
    obtain ⟨hV, hE⟩ := (hfix v).1 hv
    exact (hfix _).2 ⟨h.summand.inv _ _ hV, by rw [h.E_ι, hE]⟩
  · intro P hPle hPc hPinv
    by_cases hbot : P = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨w, hwP, hw0⟩ := P.ne_bot_iff.1 hbot
    obtain ⟨hwV, hEw⟩ := (hfix w).1 (hPle hwP)
    let S : Submodule ℂ H := Submodule.span ℂ (Set.range fun γ => π γ w)
    have hSinv : π.IsInvariant S := by
      intro g v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨γ, rfl⟩ := hx
        exact Submodule.subset_span ⟨g * γ, by simp [UnitaryRep.map_mul_apply]⟩
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _)]
        exact S.add_mem hx hy
      | smul a x _ hx =>
        rw [map_smul]
        exact S.smul_mem a hx
    have hSV : S ≤ V := Submodule.span_le.2 (by
      rintro _ ⟨γ, rfl⟩
      exact h.summand.inv _ _ hwV)
    have hQle : S.topologicalClosure ≤ V :=
      Submodule.topologicalClosure_minimal _ hSV h.summand.closed
    have hQ : S.topologicalClosure = V := by
      rcases h.summand.irred _ hQle S.isClosed_topologicalClosure hSinv.topologicalClosure with h0 | h1
      · exfalso
        have hmem : w ∈ S.topologicalClosure :=
          S.le_topologicalClosure (Submodule.subset_span ⟨1, by simp⟩)
        rw [h0] at hmem
        exact hw0 (by simpa using hmem)
      · exact h1
    have hES : ∀ v ∈ S, E v ∈ P := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨γ, rfl⟩ := hx
        obtain ⟨g, γ', c, hγ, hc⟩ := h.rest γ
        have hl : ∀ x ∈ List.ofFn (fun i => ι i (g i)), ∃ i g, x = ι i g := by
          intro x hx
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
          exact ⟨i, g i, rfl⟩
        obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.L1.cutIrr_prod π E ι h.E_ι P hPinv _ hl
        have hc' := hc w hwV
        rw [hEw] at hc'
        show E (π γ w) ∈ P
        rw [hγ, UnitaryRep.map_mul_apply, h1, hc']
        exact h2 _ (P.smul_mem c hwP)
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _)]
        exact P.add_mem hx hy
      | smul a x _ hx =>
        rw [map_smul]
        exact P.smul_mem a hx
    have hEQ : ∀ v ∈ V, E v ∈ P := by
      intro v hv
      rw [← hQ] at hv
      have hcl : v ∈ closure (S : Set H) := hv
      have hm := map_mem_closure E.continuous hcl (t := (P : Set H)) (fun x hx => hES x hx)
      rwa [hPc.closure_eq] at hm
    refine le_antisymm hPle fun v hv => ?_
    obtain ⟨hV, hE⟩ := (hfix v).1 hv
    rw [← hE]
    exact hEQ v hV
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.L1

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev InfD (σ : E ≃ₐ[F] E) (m : ℕ) : Type :=
  Split (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) (galInf σ) m

variable {σ : E ≃ₐ[F] E} {m : ℕ}

def compA (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : archGroup E n →* archGroup F n :=
  (archEquiv F n).toMonoidHom.comp ((D.comp n i).comp (archEquiv E n).symm.toMonoidHom)

def glueA (D : InfD σ m) (n : ℕ) (g : Fin (m + 1) → archGroup F n) : archGroup E n :=
  archEquiv E n (D.glue n fun i => (archEquiv F n).symm (g i))

def IsTens (D : InfD σ m) {n : ℕ} (φ : Fin (m + 1) → TI F n) (β : TI E n) : Prop := ∀ g, β g = ∏ i, φ i (compA D n i g)

def IsBlockElement (D : InfD σ m) (n : ℕ) (s : Fin (m + 1) → archGroup F n →* archGroup E n) : Prop :=
  ∀ i g, s i g = glueA D n (Pi.mulSingle i g)

def InSlot (D : InfD σ m) (τ : E →+* ℂ) (k : Fin (m + 1)) : Prop :=
  ∀ z : ℂ, (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (along τ z) =
    D.e.symm (Pi.single k ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (along (τ.comp (algebraMap F E)) z)))

structure ArchSlot (D : InfD σ m) {n : ℕ} (νE : Measure (archGroup E n)) (νF : Measure (archGroup F n)) (b a : TI F n)
    (aE : TI E n) (aF : TI F n) : Prop where
  meas : νE = Measure.map (glueA D n) (Measure.pi fun _ => νF)
  smooth : SmoothT b
  fin : LeftFin b
  norm : ∫ g, ‖b g‖ ∂νF ≤ 1
  sq : ∀ g, a g = cv νF b (fun x => conj (b x⁻¹)) g
  tens : IsTens D (fun _ => a) aE
  pow : ∀ g, aF g = cvPow νF a m g

end

def ArchBasic : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ),
    (∀ g i, compA D n i (glueA D n g) = g i) ∧ (∀ x, glueA D n (fun i => compA D n i x) = x) ∧
    (∀ g h, glueA D n (g * h) = glueA D n g * glueA D n h) ∧ Continuous (glueA D n) ∧ (∀ i, Continuous (compA D n i)) ∧
    (∃ s, IsBlockElement D n s ∧ ∀ i, Continuous (s i)) ∧
    (∀ (νF : Measure (archGroup F n)) [νF.IsHaarMeasure], (Measure.map (glueA D n) (Measure.pi fun _ => νF)).IsHaarMeasure) ∧
    ∀ φ : Fin (m + 1) → TI F n, ∃ β, IsTens D φ β

def PositionOf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] (σ : E ≃ₐ[F] E) (m : ℕ)
    (D : InfD σ m), (∀ τ, ∃ k, InSlot D τ k) ∧
      ∀ (n : ℕ) (g : archGroup E n), g ∈ archCompact E n ↔ ∀ i, compA D n i g ∈ archCompact F n

def TensSmooth : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] (σ : E ≃ₐ[F] E) (m : ℕ)
    (D : InfD σ m) (n : ℕ) (φ : Fin (m + 1) → TI F n) (β : TI E n), IsTens D φ β →
    ((∀ i, SmoothT (φ i)) → SmoothT β) ∧ ((∀ i, LeftFin (φ i)) → LeftFin β)

def JUnique : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (τ : K →+* ℂ),
    (∃! j, IsJ (n := n) τ j) ∧ ∀ i : Fin n, zc τ i ∈ Subalgebra.center ℂ (UC K n)

def LactLaws : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (β : TI K n), SmoothT β →
    (∀ u, SmoothT (lact u β)) ∧ lact 1 β = β ∧ (∀ u v, lact (u * v) β = lact u (lact v β)) ∧
      (∀ u v, lact (u + v) β = lact u β + lact v β) ∧ ∀ (c : ℂ) u, lact (c • u) β = c • lact u β

def LactGen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] (σ : E ≃ₐ[F] E) (m : ℕ)
    (D : InfD σ m) (n : ℕ) (τ : E →+* ℂ) (k : Fin (m + 1)), InSlot D τ k → ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n),
    (∀ i, SmoothT (φ i)) → IsTens D φ β → ∀ (p q : Fin n) (z : ℂ),
      IsTens D (Function.update φ k (lact ((1 : ℂ) ⊗ₜ elem (τ.comp (algebraMap F E)) p q z) (φ k))) (lact ((1 : ℂ) ⊗ₜ elem τ p q z) β)

def LactTens : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E]
    (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ) (τ : E →+* ℂ) (k : Fin (m + 1)), InSlot D τ k →
    ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β → ∀ i : Fin n,
      IsTens D (Function.update φ k (lact (zc (τ.comp (algebraMap F E)) i) (φ k))) (lact (zc τ i) β)

def LactCv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
    (α β γ : TI K n), SmoothT α → (∀ g, γ g = cv ν α β g) → SmoothT γ ∧ (LeftFin α → LeftFin γ) ∧
      (∀ u g, lact u γ g = cv ν (lact u α) β g) ∧
      (SmoothT β → ∀ z ∈ Subalgebra.center ℂ (UC K n), ∀ g, lact z γ g = cv ν α (lact z β) g)

def TensOp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ)
    (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure],
    νE = Measure.map (glueA D n) (Measure.pi fun _ => νF) →
    ∀ (s : Fin (m + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup E n) H)
      (φ : Fin (m + 1) → TI F n) (β : TI E n), IsTens D φ β →
      π.integrated νE (UnitaryRep.ccToL1 νE β) =
        (List.ofFn fun i => (π.compHom (s i) (hs i)).integrated νF (UnitaryRep.ccToL1 νF (φ i))).prod

def SqOp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (b a aF : TI K n) (m : ℕ),
    (∀ g, a g = cv ν b (fun x => conj (b x⁻¹)) g) → (∀ g, aF g = cvPow ν a m g) → ∫ g, ‖b g‖ ∂ν ≤ 1 →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup K n) H),
      π.integrated ν (UnitaryRep.ccToL1 ν a) =
          π.integrated ν (UnitaryRep.ccToL1 ν b) * star (π.integrated ν (UnitaryRep.ccToL1 ν b)) ∧
        0 ≤ π.integrated ν (UnitaryRep.ccToL1 ν a) ∧ ‖π.integrated ν (UnitaryRep.ccToL1 ν a)‖ ≤ 1 ∧
        π.integrated ν (UnitaryRep.ccToL1 ν aF) = π.integrated ν (UnitaryRep.ccToL1 ν a) ^ (m + 1)

def ArchSlotEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ)
    (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b : TI F n), SmoothT b → LeftFin b → ∫ g, ‖b g‖ ∂νF ≤ 1 →
    ∃ (νE : Measure (archGroup E n)) (_ : νE.IsHaarMeasure) (a : TI F n) (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF

def BumpEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup K n) H) (v : H), v ≠ 0 →
    ∃ b : TI K n, SmoothT b ∧ LeftFin b ∧ ∫ g, ‖b g‖ ∂ν ≤ 1 ∧ star (π.integrated ν (UnitaryRep.ccToL1 ν b)) v ≠ 0

end UpperTheory.ConvolutionTheory.L1
end
end
