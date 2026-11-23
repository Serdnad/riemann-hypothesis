module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare


open Matrix in
open scoped TensorProduct ContDiff ComplexOrder in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.FockCompare.exists_heisenberg_operators : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), _root_.GlobalTheory.FockCompare.Sm ι f → ∀ (u : R) (w : G), _root_.GlobalTheory.FockCompare.hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → ∀ (M : Submodule ℂ (G → ℂ)), (∀ f ∈ M, _root_.GlobalTheory.FockCompare.Sm ι f) → (∀ u, ∀ f ∈ M, _root_.GlobalTheory.FockCompare.hD ι π om u f ∈ M) → ∃ Dop : R → Module.End ℂ M, (∀ u (f : M), ((Dop u f : M) : G → ℂ) = _root_.GlobalTheory.FockCompare.hD ι π om u f) ∧ (∀ u v, Dop (u + v) = Dop u + Dop v) ∧ ∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u := by
  intro G R _ _ _ _ ι π om _ hform M hSm hM
  have hdiff : ∀ f ∈ M, ∀ w : G, DifferentiableAt ℝ (fun x : R => f (w + ι x)) 0 :=
    fun f hf w => ((hSm f hf w).differentiable (by simp)).differentiableAt
  refine ⟨fun u =>
    { toFun := fun f => ⟨_root_.GlobalTheory.FockCompare.hD ι π om u f, hM u f f.2⟩
      map_add' := ?_
      map_smul' := ?_ }, fun u f => rfl, ?_, ?_⟩
  · intro f g
    ext w
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [hform _ (hSm _ (M.add_mem f.2 g.2)), hform _ (hSm _ f.2), hform _ (hSm _ g.2)]
    have hfun : (fun x : R => ((f : G → ℂ) + g) (w + ι x)) =
        (fun x : R => (f : G → ℂ) (w + ι x)) + fun x : R => (g : G → ℂ) (w + ι x) := rfl
    rw [hfun, fderiv_add (hdiff _ f.2 w) (hdiff _ g.2 w)]
    simp only [Pi.add_apply, ContinuousLinearMap.add_apply]
    ring
  · intro a f
    ext w
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [hform _ (hSm _ (M.smul_mem a f.2)), hform _ (hSm _ f.2)]
    have hfun : (fun x : R => (a • (f : G → ℂ)) (w + ι x)) =
        a • fun x : R => (f : G → ℂ) (w + ι x) := rfl
    rw [hfun, fderiv_const_smul (hdiff _ f.2 w)]
    simp only [Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.smul_apply]
    ring
  · intro u v
    ext f w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Submodule.coe_add,
      Pi.add_apply]
    rw [hform _ (hSm _ f.2), hform _ (hSm _ f.2), hform _ (hSm _ f.2)]
    simp only [map_add (f := _)]
    push_cast
    ring
  · intro c u
    ext f w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, SetLike.val_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [hform _ (hSm _ f.2), hform _ (hSm _ f.2)]
    simp only [map_smul, smul_eq_mul, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.FockCompare
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCompare

variable {D : D7}

theorem span_tauE_eq_top {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) :
    Submodule.span ℝ (Set.range fun e : D.host.E => fun τ : D.what₂.Tau => tauE D τ e) = ⊤ := by
  set S := Submodule.span ℝ (Set.range fun e : D.host.E => fun τ : D.what₂.Tau => tauE D τ e) with hS
  have hθ := h.inf
  have hcl : IsClosed (S : Set (D.what₂.Tau → ℂ)) := S.closed_of_finiteDimensional
  have key : ∀ y : Ainf D.host.F ⊗[D.host.F] D.host.E, (fun τ => θ τ y) ∈ S := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      have : (fun τ => θ τ 0) = 0 := by funext τ; exact RingHom.map_zero _
      rw [this]; exact S.zero_mem
    | add a b ha hb =>
      have : (fun τ => θ τ (a + b)) = (fun τ => θ τ a) + fun τ => θ τ b := by
        funext τ; exact RingHom.map_add _ _ _
      rw [this]; exact S.add_mem ha hb
    | tmul a x =>
      have e : ∀ (a : Ainf D.host.F) τ, θ τ (a ⊗ₜ[D.host.F] x) =
          θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D τ x := by
        intro a τ
        rw [← (hθ τ).1, ← RingHom.map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have hc : Continuous fun a : Ainf D.host.F => fun τ => θ τ (a ⊗ₜ[D.host.F] x) := by
        refine continuous_pi fun τ => ?_
        simp only [e]
        exact (hθ τ).2.mul continuous_const
      refine DenseRange.induction_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap D.host.F) a
        (hcl.preimage hc) fun f => ?_
      have e1 : (algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] (1 : D.host.E) =
          (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) := by
        exact (Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F)
          (B := D.host.E)).commutes f |>.trans
          ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f).symm
      refine Submodule.subset_span ⟨algebraMap D.host.F D.host.E f * x, ?_⟩
      funext τ
      show tauE D τ _ = θ τ ((algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] x)
      rw [e, e1, (hθ τ).1, RingHom.map_mul]
  rw [eq_top_iff]
  intro z _
  have := key (infPart D (σ z))
  rwa [show (fun τ => θ τ (infPart D (σ z))) = z from funext fun τ => h.comp z τ] at this

theorem span_piW_ratW_eq_top (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ) (V W : HSp D) :
    Submodule.span ℝ (Set.range fun γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E =>
      piW θ V W (ratW V W γ)) = ⊤ := by
  classical
  set T := Submodule.span ℝ (Set.range fun γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E =>
      piW θ V W (ratW V W γ)) with hT
  let L : Fin V.rank → Fin W.rank → (D.what₂.Tau → ℂ) →ₗ[ℝ] RW V W := fun i j =>
    { toFun := fun z τ k l => if i = k ∧ j = l then z τ else 0
      map_add' := fun x y => by funext τ k l; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by funext τ k l; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
  have hL : ∀ i j z, L i j z ∈ T := by
    intro i j z
    have hz : z ∈ Submodule.comap (L i j) T := by
      refine (Submodule.span_le.2 ?_ : _ ≤ Submodule.comap (L i j) T) ((span_tauE_eq_top h).ge Submodule.mem_top)
      rintro _ ⟨e, rfl⟩
      refine Submodule.subset_span ⟨Matrix.single i j e, ?_⟩
      funext τ k l
      show θ τ (infPart D (incA D (Matrix.single i j e k l))) = if i = k ∧ j = l then tauE D τ e else 0
      rw [comp_incA h.inf, Matrix.single_apply]
      split_ifs
      · rfl
      · exact RingHom.map_zero _
    exact hz
  rw [eq_top_iff]
  intro z _
  have : z = ∑ i, ∑ j, L i j fun τ => z τ i j := by
    funext τ k l
    simp only [Finset.sum_apply]
    show z τ k l = ∑ i, ∑ j, if i = k ∧ j = l then z τ i j else 0
    simp [ite_and]
  rw [this]
  exact T.sum_mem fun i _ => T.sum_mem fun j _ => hL i j _

end GlobalTheory.FockCompare

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCompare.ThetaPeriod

variable {D : D7}

def mulRat (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) : AF D.host.F →+ WA V W where
  toFun a := Matrix.of fun i j => a ⊗ₜ[D.host.F] γ i j
  map_zero' := by ext i j; exact TensorProduct.zero_tmul _ _
  map_add' x y := by ext i j; exact TensorProduct.add_tmul _ _ _

theorem continuous_mulRat (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    Continuous (mulRat V W γ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have e : (fun a : AF D.host.F => mulRat V W γ a i j) =
      fun a => a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] γ i j : AE D) := by
    funext a
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl
  rw [e]
  have : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  exact Continuous.smul (M := AF D.host.F) (X := AE D) (f := fun a : AF D.host.F => a) continuous_id continuous_const

theorem mulRat_one (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    mulRat V W γ 1 = ratW V W γ := by
  ext i j; rfl

theorem ratW_nsmul (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (N : ℕ) :
    ratW V W (N • γ) = N • ratW V W γ := by
  ext i j
  exact (incA D).toAddMonoidHom.map_nsmul N (γ i j)

theorem norm_periodic (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (hU : ∀ U : AddSubgroup (AF D.host.F), IsOpen (U : Set (AF D.host.F)) →
      ∃ N : ℕ, 0 < N ∧ pairA D.host.F 0 (N : Af D.host.F) ∈ U)
    (V W : HSp D) (f : WA V W → ℂ) (hf : IsThetaFun ψ V W f) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    ∃ N : ℕ, 0 < N ∧ ∀ w, ‖f (w + iotaW σ V W ((N : ℝ) • piW θ V W (ratW V W γ)))‖ = ‖f w‖ := by
  obtain ⟨U, hUo, hUf⟩ := hf.level
  obtain ⟨N, hN, hmem⟩ := hU (U.comap (mulRat V W γ)) (hUo.preimage (continuous_mulRat V W γ))
  refine ⟨N, hN, fun w => ?_⟩
  set u : WA V W := mulRat V W γ (pairA D.host.F 0 (N : Af D.host.F)) with hu
  set r : WA V W := mulRat V W γ (pairA D.host.F (N : Ainf D.host.F) 0) with hr
  have hu0 : u.map (infPart D) = 0 := by
    ext i j
    exact TensorProduct.zero_tmul _ (γ i j)
  have hr0 : IsRealW V W r := by
    ext i j
    exact TensorProduct.zero_tmul _ (γ i j)
  have hsum : r + u = N • ratW V W γ := by
    rw [hr, hu, ← AddMonoidHom.map_add (f := _), ← mulRat_one, ← AddMonoidHom.map_nsmul]
    congr 1
    refine Prod.ext ?_ ?_
    · show (N : Ainf D.host.F) + 0 = N • (1 : Ainf D.host.F)
      rw [add_zero, nsmul_one]
    · show 0 + (N : Af D.host.F) = N • (1 : Af D.host.F)
      rw [zero_add, nsmul_one]
  have hpu : piW θ V W u = 0 := by
    funext τ i j
    have : infPart D (u i j) = 0 := congrFun (congrFun hu0 i) j
    show θ τ (infPart D (u i j)) = 0
    rw [this, RingHom.map_zero]
  have hi : iotaW σ V W ((N : ℝ) • piW θ V W (ratW V W γ)) = r := by
    rw [Nat.cast_smul_eq_nsmul, ← AddMonoidHom.map_nsmul, ← hsum, AddMonoidHom.map_add (f := _), hpu, add_zero,
      h.iota_pi hr0]
  have h1 : ∀ x, ‖f (x + u)‖ = ‖f x‖ := fun x => by
    have := congrFun (hUf u hmem hu0) x
    rw [← this, Heisenberg₂, norm_mul, hψ, one_mul]
  have h2 := congrArg norm (hf.quasi (N • γ) w)
  rw [norm_mul, hψ, one_mul, ratW_nsmul, ← hsum] at h2
  rw [hi, ← h1, ← h2, add_assoc, add_comm]

end GlobalTheory.FockCompare.ThetaPeriod

end
end

section

noncomputable section

namespace GlobalTheory.FockCompare.WeylInduct

open GlobalTheory.FockCompare

variable {I M : Type} [AddCommGroup M] [Module ℂ M]

theorem killed_zero (a : I → Module.End ℂ M) (m : M) : Killed a 0 m ↔ m = 0 := by
  constructor
  · intro h; exact h [] rfl
  · intro h l hl
    obtain rfl := List.length_eq_zero_iff.1 hl
    exact h

theorem killed_succ (a : I → Module.End ℂ M) (N : ℕ) (m : M) :
    Killed a (N + 1) m ↔ ∀ i, Killed a N (a i m) := by
  constructor
  · intro h i l hl
    have := h (l ++ [i]) (by simp [hl])
    simpa [List.foldr_append] using this
  · intro h l hl
    obtain rfl | ⟨l', i, rfl⟩ := List.eq_nil_or_concat l
    · simp at hl
    · have := h i l' (by simpa using hl)
      simpa [List.foldr_append] using this

noncomputable def prodE (E : Module.End ℂ M) (lam : ℂ) : ℕ → ℕ → M → M
  | 0, _, x => x
  | N + 1, j, x => prodE E lam N (j + 1) (E x - ((j : ℂ) * lam) • x)

theorem prodE_comm (E : Module.End ℂ M) (lam : ℂ) (N : ℕ) :
    ∀ (j : ℕ) (x : M), prodE E lam N j (E x) = E (prodE E lam N j x) := by
  induction N with
  | zero => intro j x; rfl
  | succ N ih =>
    intro j x
    simp only [prodE]
    rw [← ih, map_sub, map_smul]

theorem shift_prodE (E A : Module.End ℂ M) (lam : ℂ) (h : ∀ x, A (E x) = E (A x) + lam • A x) (N : ℕ) :
    ∀ (j : ℕ) (x : M), A (prodE E lam N (j + 1) x) = prodE E lam N j (A x) := by
  induction N with
  | zero => intro j x; rfl
  | succ N ih =>
    intro j x
    simp only [prodE]
    rw [ih, map_sub, map_smul, h]
    congr 1
    push_cast
    module

theorem killed_stable (a : I → Module.End ℂ M) (E : Module.End ℂ M) (lam : ℂ)
    (h : ∀ i x, a i (E x) = E (a i x) + lam • a i x) (N : ℕ) :
    ∀ (t : ℂ) (x : M), Killed a N x → Killed a N (E x - t • x) := by
  induction N with
  | zero => intro t x hx; rw [killed_zero] at hx ⊢; simp [hx]
  | succ N ih =>
    intro t x hx
    rw [killed_succ] at hx ⊢
    intro i
    have e : a i (E x - t • x) = E (a i x) - (t - lam) • a i x := by
      rw [map_sub, map_smul, h]; module
    rw [e]
    exact ih _ _ (hx i)

theorem prodE_kills (a : I → Module.End ℂ M) (E : Module.End ℂ M) (lam : ℂ)
    (h : ∀ i x, a i (E x) = E (a i x) + lam • a i x) (h0 : ∀ x, (∀ i, a i x = 0) → E x = 0) (N : ℕ) :
    ∀ x : M, Killed a N x → prodE E lam N 0 x = 0 := by
  induction N with
  | zero => intro x hx; exact (killed_zero a x).1 hx
  | succ N ih =>
    intro x hx
    rw [killed_succ] at hx
    simp only [prodE, Nat.cast_zero, zero_mul, zero_smul, sub_zero]
    rw [prodE_comm]
    refine h0 _ fun i => ?_
    rw [shift_prodE E (a i) lam (h i), ih _ (hx i)]

theorem peel (E : Module.End ℂ M) (lam : ℂ) (hl : lam ≠ 0) (S : M → Prop) (P : Submodule ℂ M)
    (hS : ∀ (t : ℂ) x, S x → S (E x - t • x)) (hE : ∀ x, S x → E x ∈ P) (K : ℕ) :
    ∀ (j : ℕ) (x : M), S x → prodE E lam K (j + 1) x ∈ P → x ∈ P := by
  induction K with
  | zero => intro j x _ hx; exact hx
  | succ K ih =>
    intro j x hx hp
    simp only [prodE] at hp
    have h1 := ih _ _ (hS _ x hx) hp
    have h2 := P.sub_mem (hE x hx) h1
    rw [sub_sub_cancel] at h2
    exact (P.smul_mem_iff (mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero j)) hl)).1 h2

theorem mem_of_killed : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a c : I → Module.End ℂ M) (n : ℕ) (e : Fin n → I) (lam : ℂ), lam ≠ 0 → (∀ i, a i * (∑ k, c (e k) * a (e k)) = ((∑ k, c (e k) * a (e k)) + lam • (1 : Module.End ℂ M)) * a i) → ∀ P : Submodule ℂ M, (∀ m, (∀ i, a i m = 0) → m ∈ P) → (∀ i, ∀ m ∈ P, c i m ∈ P) → ∀ (N : ℕ) (m : M), Killed a N m → m ∈ P := by
  intro I M _ _ a c n e lam hl hc P hv hP N
  set E : Module.End ℂ M := ∑ k, c (e k) * a (e k) with hEdef
  have hEx : ∀ x, E x = ∑ k, c (e k) (a (e k) x) := by
    intro x; simp [hEdef, LinearMap.sum_apply]
  have h : ∀ i x, a i (E x) = E (a i x) + lam • a i x := by
    intro i x
    have := LinearMap.congr_fun (hc i) x
    simpa using this
  have h0 : ∀ x, (∀ i, a i x = 0) → E x = 0 := by
    intro x hx; simp [hEx, hx]
  induction N with
  | zero => intro m hm; rw [(killed_zero a m).1 hm]; exact P.zero_mem
  | succ N ih =>
    intro m hm
    refine peel E lam hl (Killed a (N + 1)) P (killed_stable a E lam h (N + 1)) (fun x hx => ?_) N 0 m hm
      (hv _ fun i => ?_)
    · rw [hEx]
      exact P.sum_mem fun k _ => hP _ _ (ih _ ((killed_succ a N x).1 hx _))
    · rw [shift_prodE E (a i) lam (h i)]
      exact prodE_kills a E lam h h0 N _ ((killed_succ a N m).1 hm i)

end GlobalTheory.FockCompare.WeylInduct

end
end

section

namespace GlobalTheory.FockCompare.WeylCreate

open GlobalTheory.FockCompare

variable {I M : Type} [AddCommGroup M] [Module ℂ M] {a : I → Module.End ℂ M}

theorem killed_succ_iff (N : ℕ) (m : M) : Killed a (N + 1) m ↔ ∀ i, Killed a N (a i m) := by
  constructor
  · intro h i l hl
    have := h (l ++ [i]) (by simp [hl])
    simpa [List.foldr_append] using this
  · intro h l hl
    rcases List.eq_nil_or_concat l with rfl | ⟨l', i, rfl⟩
    · simp at hl
    · have := h i l' (by simpa using hl)
      simpa [List.foldr_append] using this

theorem foldr_add_smul (l : List I) (β : ℂ) (x y : M) :
    l.foldr (fun i x => a i x) (x + β • y) =
      l.foldr (fun i x => a i x) x + β • l.foldr (fun i x => a i x) y := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, map_add (f := _), map_smul]

theorem foldr_zero (l : List I) : l.foldr (fun i x => a i x) (0 : M) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, map_zero]

theorem killed_create : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a : I → Module.End ℂ M) (c : Module.End ℂ M),
    (∀ i, ∃ β : ℂ, a i * c - c * a i = β • (1 : Module.End ℂ M)) →
    ∀ (N : ℕ) (m : M), Killed a N m → Killed a (N + 1) (c m) := by
  intro I M _ _ a c hc N
  induction N with
  | zero =>
    intro m hm l _
    have h0 : m = 0 := hm [] rfl
    rw [h0, map_zero]
    exact foldr_zero l
  | succ N ih =>
    intro m hm
    rw [killed_succ_iff]
    intro i
    obtain ⟨β, hβ⟩ := hc i
    have e : a i (c m) = c (a i m) + β • m := by
      have := LinearMap.congr_fun hβ m
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at this
      rw [← this]; abel
    have h1 := ih (a i m) ((killed_succ_iff N m).1 hm i)
    intro l hl
    rw [e, foldr_add_smul, h1 l hl, hm l hl, smul_zero, add_zero]

end GlobalTheory.FockCompare.WeylCreate
end
