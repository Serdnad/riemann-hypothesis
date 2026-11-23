module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039

@[expose] public section

section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.HeisTwist

theorem jm_eq_diagonal (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => (-1 : ℂ))) := by
  rw [Jm, Formalism.UG.Jpq, ← Matrix.fromBlocks_diagonal]
  simp [Matrix.diagonal_neg]
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]

theorem jm_mul_mul_jm_apply {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (a : Ix P Q) (b : Ix R S) :
    (Jm P Q * c * Jm R S) a b = lineSign a b * c a b := by
  rw [jm_eq_diagonal, jm_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem term_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (l : Ln P Q R S) :
    (Complex.I * lineSign l.1 l.2 * c l.1 l.2) • raiB l (1 : Pol P Q R S)
      - (lineSign l.1 l.2 * star (Complex.I * lineSign l.1 l.2 * c l.1 l.2)) • lowB l 1
      = Complex.I • (c l.1 l.2 • raiB l (1 : Pol P Q R S) - (lineSign l.1 l.2 * star (c l.1 l.2)) • lowB l 1) := by
  rcases l with ⟨a | a, b | b⟩ <;>
    simp [raiB, lowB, linePos, lineSign, smul_sub, smul_smul] <;> ring_nf <;> simp [Complex.conj_I] <;> module

end GlobalTheory.HeisTwist

namespace GlobalTheory.RealLift

theorem heisOp_twist_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) :
    heisOp (Complex.I • (Jm P Q * c * Jm R S)) 1 = Complex.I • heisOp c 1 := by
  simp only [heisOp, LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_comm Complex.I]
  congr 1
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Matrix.smul_apply,
    GlobalTheory.HeisTwist.jm_mul_mul_jm_apply, smul_eq_mul]
  rw [← GlobalTheory.HeisTwist.term_one c l, mul_assoc]

end GlobalTheory.RealLift
end
end

section

noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

section Laws

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]


variable (F κ) in
def intPts : Set (κ → Af F) :=
  Set.univ.pi fun _ => {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}

theorem indicator_intPts_mem_SB : (intPts F κ).indicator (1 : (κ → Af F) → ℂ) ∈ SB (κ → Af F) := by
  haveI := GlobalTheory.IntegralFinAdele.t2Space_finiteAdeleRing' F
  have hO : IsOpen {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hC : IsCompact {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1
  have hU : IsOpen (intPts F κ) := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hK : IsCompact (intPts F κ) := isCompact_univ_pi fun _ => hC
  refine ⟨?_, HasCompactSupport.intro' hK hK.isClosed fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ intPts F κ
  · filter_upwards [hU.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem zero_mem_intPts : (0 : κ → Af F) ∈ intPts F κ := fun _ _ v => zero_mem _

def ptAt (a : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), y i)

theorem pureA_ptAt (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (a : κ → mixedEmbedding.mixedSpace F)
    (y : κ → Af F) : pureA F f g (ptAt a y) = f a * g y := by
  change f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i))) * g y = f a * g y
  congr 1
  congr 1
  funext i
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (a i)

theorem fin_eq_zero_of_at {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
  have h2 : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
  rwa [one_mul] at h2

theorem at_of_fin_eq_zero {z : κ → AF F} (hz : ∀ i, (z i).2 = 0) : At (evI F) z := by
  intro u hu
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  funext i
  refine Prod.ext ?_ ?_
  · change u.1 * (z i).1 = 0
    rw [hu1, zero_mul]
  · change u.2 * (z i).2 = 0
    rw [hz i, mul_zero]

theorem tens_eq_pureA (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evI F) z → r (x + z) = r x) :
    tens (evI F) f r = pureA F f (fun y => r (fun i => ((0 : Ainf F), y i))) := by
  funext x
  simp only [tens, pureA, evI]
  congr 1
  have h := hr (fun i => ((0 : Ainf F), (x i).2)) (fun i => ((x i).1, (0 : Af F)))
    (at_of_fin_eq_zero fun i => rfl)
  rw [← h]
  congr 1
  funext i
  exact Prod.ext (zero_add _).symm (add_zero _).symm

theorem mem_SB_of_pureA_mem {f : SInf F κ} (hf : f ≠ 0) {g : (κ → Af F) → ℂ} (h : pureA F f g ∈ schA F κ) :
    g ∈ SB (κ → Af F) := by
  obtain ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hf (SchwartzMap.ext h0)
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → Af F) → ℂ) := LinearMap.funLeft ℂ ℂ (ptAt a)
  have hle : schA F κ ≤ (SB (κ → Af F)).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f', g', hg', rfl⟩
    change (fun y => pureA F f' g' (ptAt a y)) ∈ SB (κ → Af F)
    simp_rw [pureA_ptAt]
    exact (SB (κ → Af F)).smul_mem (f' a) hg'
  have h1 : L (pureA F f g) ∈ SB (κ → Af F) := hle h
  have h2 : L (pureA F f g) = f a • g := by
    funext y
    change pureA F f g (ptAt a y) = _
    rw [pureA_ptAt]
    rfl
  rw [h2] at h1
  have h3 := (SB (κ → Af F)).smul_mem (f a)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h3

theorem eval_mem_adm (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

end Laws

section Main

open scoped Classical

theorem actsLaws : ActsLaws := by
  intro F _ _ κ _ f f₁ f₂
  set g₀ : (κ → Af F) → ℂ := (intPts F κ).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (κ → Af F) := indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem zero_mem_intPts]; rfl

  set r₀ : (κ → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def
  have hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    change g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [fin_eq_zero_of_at hz, add_zero]
  have htens₀ : ∀ φ : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) φ r₀ = pureA F φ g₀ := fun φ => rfl
  have hrest₀ : Rest (evI F) (⇑f) r₀ := ⟨hr₀inv, by rw [htens₀]; exact Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩

  have hext : ∀ h₁ h₂ : SInf F κ, (∀ a, pureA F h₁ g₀ (ptAt a 0) = pureA F h₂ g₀ (ptAt a 0)) → h₁ = h₂ := by
    intro h₁ h₂ h
    ext a
    simpa [pureA_ptAt, hg₀0] using h a

  have hzero : ∀ g : (κ → Af F) → ℂ, pureA F ⇑(0 : SInf F κ) g = 0 := by
    intro g; funext x; simp [pureA]
  have hzeroT : ∀ r : (κ → AF F) → ℂ, tens (evI F) ⇑(0 : SInf F κ) r = 0 := by
    intro r; funext x; simp [tens]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T hT0 hSD r hr x
    by_cases hf : f = 0
    · subst hf
      have hf₁ : f₁ = 0 := hext _ _ fun a => by
        have h := hSD g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
        simp only [LinearMap.proj_apply, hzero, hT0] at h
        rw [hzero]
        exact (h.unique (hasDerivAt_const 0 (0 : ℂ)))
      subst hf₁
      rw [hzeroT]
      simp only [hT0, Pi.zero_apply]
      exact hasDerivAt_const 0 (0 : ℂ)
    · have hg : (fun y => r (fun i => ((0 : Ainf F), y i))) ∈ SB (κ → Af F) :=
        mem_SB_of_pureA_mem hf (tens_eq_pureA (⇑f) hr.1 ▸ hr.2)
      have h := hSD _ hg _ (eval_mem_adm x)
      rw [tens_eq_pureA (⇑f) hr.1, tens_eq_pureA (⇑f₁) hr.1]
      exact h
  · intro T hT0 hSA r hr
    by_cases hf : f = 0
    · subst hf
      have hf₁ : f₁ = 0 := hext _ _ fun a => by
        have h := hSA g₀ hg₀
        rw [hzero, hT0] at h
        rw [← h, hzero]
      subst hf₁
      rw [hzeroT, hT0]
    · have hg : (fun y => r (fun i => ((0 : Ainf F), y i))) ∈ SB (κ → Af F) :=
        mem_SB_of_pureA_mem hf (tens_eq_pureA (⇑f) hr.1 ▸ hr.2)
      rw [tens_eq_pureA (⇑f) hr.1, tens_eq_pureA (⇑f₁) hr.1]
      exact hSA _ hg
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e₁ := h₁ r₀ hrest₀ (ptAt a 0)
    have e₂ := h₂ r₀ hrest₀ (ptAt a 0)
    rw [htens₀] at e₁ e₂
    exact e₁.unique e₂
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e := (h₁ r₀ hrest₀).symm.trans (h₂ r₀ hrest₀)
    rw [htens₀, htens₀] at e
    exact congrFun e (ptAt a 0)
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e₁ := h₁ g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
    have e₂ := h₂ g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
    exact e₁.unique e₂

end Main

end GlobalTheory.RealLift
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section

namespace GlobalTheory.RealLift.Dbl

theorem dblM_gram {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (N : Matrix β β ℂ) (C : Matrix β (Ix R S) ℂ)
    (h : Cᵀ * N * C.map star = Jm R S) :
    (dblM C)ᵀ * Matrix.fromBlocks N 0 0 (-N) * (dblM C).map star = Jm (R + S) (S + R) := by
  have hG : ∀ a a', ∑ x, (∑ y, C y a * N y x) * (starRingEnd ℂ) (C x a') = Jm R S a a' := by
    intro a a'
    have := congrFun (congrFun h a) a'
    simpa [Matrix.mul_apply] using this
  ext j k
  rcases j with p | p <;> rcases k with q | q <;>
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective p
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective q
    rcases x with r | s <;> rcases y with r' | s' <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, dblM, dblCol, hG, Jm, Formalism.UG.Jpq, Matrix.one_apply,
        Finset.sum_neg_distrib, Matrix.neg_apply, Fin.ext_iff, Function.swap] <;> omega

theorem dblM_rinv {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (C : Matrix β (Ix R S) ℂ)
    (h : ∃ C' : Matrix (Ix R S) β ℂ, C * C' = 1) :
    ∃ D : Matrix (Ix (R + S) (S + R)) (β ⊕ β) ℂ, dblM C * D = 1 := by
  obtain ⟨C', hC'⟩ := h
  refine ⟨(dblM C'ᵀ)ᵀ, ?_⟩
  have hI : ∀ i i', ∑ r, C i (Sum.inl r) * C' (Sum.inl r) i' + ∑ s, C i (Sum.inr s) * C' (Sum.inr s) i' =
      (1 : Matrix β β ℂ) i i' := by
    intro i i'
    rw [← hC', Matrix.mul_apply, Fintype.sum_sum_type]
  ext i i'
  rcases i with i | i <;> rcases i' with i' | i' <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_add, dblM, dblCol, Matrix.one_apply, hI, add_comm, Function.swap]

theorem dblM_isFrame {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (N : Matrix β β ℂ) (C : Matrix β (Ix R S) ℂ)
    (h : IsFrame N C) : IsFrame (Matrix.fromBlocks N 0 0 (-N)) (dblM C) :=
  ⟨dblM_gram N C h.1, dblM_rinv C h.2⟩

theorem framed_dbl (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (P Q R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) :
    Framed τ JA JB a b A C → Framed τ JA (dbl JB) a b A (fun w => dblM (C w)) := by
  rintro ⟨hab, hA, hC⟩
  refine ⟨hab, hA, fun w => ?_⟩
  have key : b • (dbl JB).map (piInf (τ w)) =
      Matrix.fromBlocks (b • JB.map (piInf (τ w))) 0 0 (-(b • JB.map (piInf (τ w)))) := by
    simp [dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_smul, Matrix.map_neg]
  rw [key]
  exact dblM_isFrame _ _ (hC w)

end GlobalTheory.RealLift.Dbl

end
end

section

open scoped TensorProduct

namespace GlobalTheory.FactorKernel

variable {ι : Type} [Fintype ι] [hd : DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def contrML (w₀ : ι) (μ : ι → Module.Dual ℂ V) : (ι → V) →ₘₗ[ℂ] V where
  toFun x := (∏ i ∈ Finset.univ.erase w₀, μ i (x i)) • x w₀
  map_update_add' := by
    intro inst x i a b
    obtain rfl : inst = hd := Subsingleton.elim _ _
    by_cases h : i = w₀
    · subst h
      have e : ∀ c, ∏ k ∈ Finset.univ.erase i, μ k (Function.update x i c k) =
          ∏ k ∈ Finset.univ.erase i, μ k (x k) := fun c =>
        Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_self, smul_add]
    · have hi : i ∈ Finset.univ.erase w₀ := Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩
      have e : ∀ c, ∏ k ∈ Finset.univ.erase w₀, μ k (Function.update x i c k) =
          μ i c * ∏ k ∈ (Finset.univ.erase w₀).erase i, μ k (x k) := fun c => by
        rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
        congr 1
        exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_of_ne (Ne.symm h), map_add (f := _), add_mul, add_smul]
  map_update_smul' := by
    intro inst x i c a
    obtain rfl : inst = hd := Subsingleton.elim _ _
    simp only [RingHom.id_apply]
    by_cases h : i = w₀
    · subst h
      have e : ∀ c, ∏ k ∈ Finset.univ.erase i, μ k (Function.update x i c k) =
          ∏ k ∈ Finset.univ.erase i, μ k (x k) := fun c =>
        Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_self, smul_comm c]
    · have hi : i ∈ Finset.univ.erase w₀ := Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩
      have e : ∀ c, ∏ k ∈ Finset.univ.erase w₀, μ k (Function.update x i c k) =
          μ i c * ∏ k ∈ (Finset.univ.erase w₀).erase i, μ k (x k) := fun c => by
        rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
        congr 1
        exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_of_ne (Ne.symm h), map_smul, smul_eq_mul, mul_assoc, smul_smul]

noncomputable def contr (w₀ : ι) (μ : ι → Module.Dual ℂ V) : (⨂[ℂ] _ : ι, V) →ₗ[ℂ] V :=
  PiTensorProduct.lift (contrML w₀ μ)

theorem contr_tprod (w₀ : ι) (μ : ι → Module.Dual ℂ V) (x : ι → V) :
    contr w₀ μ (PiTensorProduct.tprod ℂ x) = (∏ i ∈ Finset.univ.erase w₀, μ i (x i)) • x w₀ := by
  rw [contr, PiTensorProduct.lift.tprod]; rfl

theorem dual_contr (w₀ : ι) (μ : ι → Module.Dual ℂ V) (ν : Module.Dual ℂ V) (T : ⨂[ℂ] _ : ι, V) :
    ν (contr w₀ μ T) =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ (Function.update μ w₀ ν)) T := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, contr_tprod, PiTensorProduct.dualDistrib_apply, map_smul,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ w₀), Function.update_self, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    congr 1
    rw [mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]

theorem contr_atPl (w₀ : ι) (μ : ι → Module.Dual ℂ V) (L : Module.End ℂ V) (T : ⨂[ℂ] _ : ι, V) :
    contr w₀ μ (GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w₀ L T) = L (contr w₀ μ T) := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, GlobalTheory.RealLift.atPl, PiTensorProduct.map_tprod, contr_tprod, contr_tprod,
      map_smul, Function.update_self, L.map_smul]
    congr 2
    exact Finset.prod_congr rfl fun k hk => by
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end GlobalTheory.FactorKernel
end

section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.RealLift

namespace GlobalTheory.KFixIrr

variable (ι : Type) [Fintype ι] (P Q R S : ℕ)

def degLE (k : ℕ) : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :=
  Submodule.span ℂ {T | ∃ f : ι → Formalism.BasicNotions.TH.Pol P Q R S, ∑ w, (f w).totalDegree ≤ k ∧ T = PiTensorProduct.tprod ℂ f}

def chiPart [DecidableEq ι] (x : ι → ℚ) : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :=
  ⨅ w : ι, ⨅ X : {X : Mat P Q // IsKC X},
    LinearMap.ker (atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct1 P Q R S X.1) - ((x w : ℂ) * X.1.trace) • 1)

variable {ι P Q R S}

theorem mem_chiPart [DecidableEq ι] (x : ι → ℚ) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :
    T ∈ chiPart ι P Q R S x ↔ ∀ w (X : Mat P Q), IsKC X →
      atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct1 P Q R S X) T = ((x w : ℂ) * X.trace) • T := by
  simp only [chiPart, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero, Subtype.forall]

theorem degLE_mono : Monotone (degLE ι P Q R S) := fun _ _ h =>
  Submodule.span_mono fun _ ⟨f, hf, e⟩ => ⟨f, hf.trans h, e⟩

theorem tprod_mem_degLE (f : ι → Formalism.BasicNotions.TH.Pol P Q R S) {k : ℕ} (h : ∑ w, (f w).totalDegree ≤ k) :
    PiTensorProduct.tprod ℂ f ∈ degLE ι P Q R S k :=
  Submodule.subset_span ⟨f, h, rfl⟩

end GlobalTheory.KFixIrr

end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem holoChart_trans_algChart {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e)
    (c : AlgChart X.str σ X.dim) :
    DifferentiableOn ℂ (c.e ∘ e.symm) (e.target ∩ e.symm ⁻¹' c.e.source) :=
  differentiableOn_euclidean.2 fun a => ((he _ (c.x a)).mono fun _ (hv : _ ∈ e.target ∩ e.symm ⁻¹' c.e.source) =>
    ⟨hv.1, c.source_subset hv.2⟩).congr fun _ hv => c.apply_eq _ hv.2 a

end GlobalTheory.GoodTop
end
