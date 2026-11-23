module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle056
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle150
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalized
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL

def piTensorHom {α : Type} {Γ : α → Type} [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)]
    {X Y : ∀ i, SmRep (Γ i)} (f : ∀ a, (X a).ρ.IntertwiningMap (Y a).ρ) :
    (piTensor fun a => (X a).ρ).IntertwiningMap (piTensor fun a => (Y a).ρ) where
  toLinearMap := PiTensorProduct.map fun a => (f a).toLinearMap
  isIntertwining' g := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod,
      PiTensorProduct.map_tprod]
    congr 1
    funext a
    exact LinearMap.congr_fun ((f a).isIntertwining' (g a)) (x a)

theorem piTensorMap_add_eq_id {α : Type} [DecidableEq α] {Y : α → Type} [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] (i : α) (u v : ∀ a, Y a →ₗ[ℂ] Y a) (hu : ∀ a, a ≠ i → u a = LinearMap.id)
    (hv : ∀ a, a ≠ i → v a = LinearMap.id) (h : u i + v i = LinearMap.id) :
    PiTensorProduct.map u + PiTensorProduct.map v = LinearMap.id := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply, PiTensorProduct.map_tprod,
    LinearMap.id_apply]

  have hx : ∀ w : ∀ a, Y a →ₗ[ℂ] Y a, (∀ a, a ≠ i → w a = LinearMap.id) →
      (fun a => w a (x a)) = Function.update x i (w i (x i)) := by
    intro w hw
    funext a
    by_cases ha : a = i
    · subst ha
      simp
    · rw [Function.update_of_ne ha, hw a ha, LinearMap.id_apply]
  rw [hx u hu, hx v hv, ← MultilinearMap.map_update_add, ← LinearMap.add_apply, h,
    LinearMap.id_apply, Function.update_eq_self]

theorem piTensor_exact_position : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)] (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α) (B B₁ B₂ : GlobalTheory.SmGL.SmRep (Γ i)) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → ∃ (ι' : (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B₁ a).ρ).IntertwiningMap (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B a).ρ)) (p' : (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B a).ρ).IntertwiningMap (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B₂ a).ρ)), Function.Injective ι' ∧ Function.Surjective p' ∧ (∀ u, p' (ι' u) = 0) ∧ (∀ v, p' v = 0 → ∃ u, ι' u = v) := by
  intro α _ _ Γ _ _ A i B B₁ B₂ ι p hι hp hpι hker

  have key : ∀ a, ∃ (f : (Function.update A i B₁ a).ρ.IntertwiningMap (Function.update A i B a).ρ)
      (g : (Function.update A i B a).ρ.IntertwiningMap (Function.update A i B₂ a).ρ)
      (s : (Function.update A i B a).V →ₗ[ℂ] (Function.update A i B₁ a).V)
      (t : (Function.update A i B₂ a).V →ₗ[ℂ] (Function.update A i B a).V),
      s ∘ₗ f.toLinearMap = LinearMap.id ∧ g.toLinearMap ∘ₗ t = LinearMap.id ∧
      (a ≠ i → f.toLinearMap ∘ₗ s = LinearMap.id ∧ t ∘ₗ g.toLinearMap = LinearMap.id) ∧
      (a = i → f.toLinearMap ∘ₗ s + t ∘ₗ g.toLinearMap = LinearMap.id ∧
        g.toLinearMap ∘ₗ f.toLinearMap = 0) := by
    intro a
    by_cases ha : a = i
    · subst ha
      rw [Function.update_self, Function.update_self, Function.update_self]
      obtain ⟨t, ht⟩ := p.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
      obtain ⟨s₀, hs₀⟩ := ι.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hι)
      have hs₀' : ∀ u, s₀ (ι u) = u := fun u => LinearMap.congr_fun hs₀ u
      have ht' : ∀ z, p (t z) = z := fun z => LinearMap.congr_fun ht z
      refine ⟨ι, p, s₀ ∘ₗ (LinearMap.id - t ∘ₗ p.toLinearMap), t, ?_, ht, fun h => absurd rfl h,
        fun _ => ⟨?_, ?_⟩⟩
      · ext u
        simp [hpι, hs₀']
      · ext y

        obtain ⟨u, hu⟩ := hker (y - t (p y)) (by simp [ht'])
        simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
          Representation.IntertwiningMap.coe_toLinearMap]
        rw [← hu, hs₀', hu, sub_add_cancel]
      · ext u
        simp [hpι]
    · rw [Function.update_of_ne ha, Function.update_of_ne ha, Function.update_of_ne ha]
      exact ⟨Representation.IntertwiningMap.id _, Representation.IntertwiningMap.id _, LinearMap.id, LinearMap.id, by ext; rfl,
        by ext; rfl, fun _ => ⟨by ext; rfl, by ext; rfl⟩, fun h => absurd h ha⟩
  choose f g s t hsf hgt hne heq using key
  have hF : ∀ x, piTensorHom f x = PiTensorProduct.map (fun a => (f a).toLinearMap) x := fun _ => rfl
  have hG : ∀ x, piTensorHom g x = PiTensorProduct.map (fun a => (g a).toLinearMap) x := fun _ => rfl
  have hSF : PiTensorProduct.map s ∘ₗ PiTensorProduct.map (fun a => (f a).toLinearMap) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp, funext hsf, PiTensorProduct.map_id]
  have hGT : PiTensorProduct.map (fun a => (g a).toLinearMap) ∘ₗ PiTensorProduct.map t = LinearMap.id := by
    rw [← PiTensorProduct.map_comp, funext hgt, PiTensorProduct.map_id]
  have hsum : PiTensorProduct.map (fun a => (f a).toLinearMap) ∘ₗ PiTensorProduct.map s +
      PiTensorProduct.map t ∘ₗ PiTensorProduct.map (fun a => (g a).toLinearMap) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
    exact piTensorMap_add_eq_id i _ _ (fun a ha => (hne a ha).1) (fun a ha => (hne a ha).2)
      (heq i rfl).1
  have hGF : PiTensorProduct.map (fun a => (g a).toLinearMap) ∘ₗ
      PiTensorProduct.map (fun a => (f a).toLinearMap) = 0 := by
    rw [← PiTensorProduct.map_comp]
    ext x
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.zero_apply]

    exact MultilinearMap.map_coord_zero _ i (by rw [(heq i rfl).2, LinearMap.zero_apply])
  refine ⟨piTensorHom f, piTensorHom g, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have := congrArg (PiTensorProduct.map s) hxy
    rw [hF, hF] at this
    simpa using (LinearMap.congr_fun hSF x).symm.trans (this.trans (LinearMap.congr_fun hSF y))
  · intro z
    exact ⟨PiTensorProduct.map t z, by rw [hG]; exact LinearMap.congr_fun hGT z⟩
  · intro u
    rw [hG, hF]
    exact LinearMap.congr_fun hGF u
  · intro v hv
    refine ⟨PiTensorProduct.map s v, ?_⟩
    rw [hG] at hv
    have := LinearMap.congr_fun hsum v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hv, map_zero, add_zero,
      LinearMap.id_apply] at this
    rw [hF]
    exact this

end GlobalTheory.SmGL
end
end

section

open scoped TensorProduct

noncomputable section

open PiTensorProduct GlobalTheory.PRep GlobalTheory.JacStages

namespace GlobalTheory.SmGL

section SwapTensor

def sigmaPairSwap (α β : Type) : (Σ _ : α, β) ≃ (Σ _ : β, α) where
  toFun p := ⟨p.2, p.1⟩
  invFun q := ⟨q.2, q.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {α β : Type} [Finite α] [Finite β]
  (Y : α → β → Type) [∀ i j, AddCommGroup (Y i j)] [∀ i j, Module ℂ (Y i j)]

theorem exists_pairCurry : ∃ e : (⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2) ≃ₗ[ℂ] ⨂[ℂ] i, ⨂[ℂ] j, Y i j,
    ∀ x : ∀ p : (Σ _ : α, β), Y p.1 p.2, e (tprod ℂ x) = tprod ℂ fun i => tprod ℂ fun j => x ⟨i, j⟩ := by
  classical
  exact ⟨sigmaCurry (fun p : (Σ _ : α, β) => Y p.1 p.2),
    sigmaCurry_tprod (fun p : (Σ _ : α, β) => Y p.1 p.2)⟩


omit [Finite α] [Finite β] in
theorem exists_pairSwap :
    ∃ e : (⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2) ≃ₗ[ℂ] ⨂[ℂ] q : (Σ _ : β, α), Y q.2 q.1,
    ∀ x : ∀ p : (Σ _ : α, β), Y p.1 p.2,
      e (tprod ℂ x) = tprod ℂ fun q : (Σ _ : β, α) => x ⟨q.2, q.1⟩ :=
  ⟨reindex ℂ (fun p : (Σ _ : α, β) => Y p.1 p.2) (sigmaPairSwap α β),
    fun x => reindex_tprod (sigmaPairSwap α β) x⟩

theorem exists_pairCurrySwap : ∃ e : (⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2) ≃ₗ[ℂ] ⨂[ℂ] j, ⨂[ℂ] i, Y i j,
    ∀ x : ∀ p : (Σ _ : α, β), Y p.1 p.2, e (tprod ℂ x) = tprod ℂ fun j => tprod ℂ fun i => x ⟨i, j⟩ := by
  obtain ⟨e₁, h₁⟩ := exists_pairSwap Y
  obtain ⟨e₂, h₂⟩ := exists_pairCurry (fun j i => Y i j)
  refine ⟨e₁.trans e₂, fun x => ?_⟩
  rw [LinearEquiv.trans_apply, h₁]
  exact h₂ _

end SwapTensor

theorem piTensor_swapBlocks_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] (c : α → β → Type)
    [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (Y : α → β → Type) [∀ i j, AddCommGroup (Y i j)]
    [∀ i j, Module ℂ (Y i j)] (σ : ∀ i j, Representation ℂ (GL (c i j) k) (Y i j)),
    Nonempty (Representation.Equiv
      ((GlobalTheory.SmGL.piTensor fun i => GlobalTheory.SmGL.piTensor fun j => σ i j).comp (GlobalTheory.SmGL.swapBlocks k c))
      (GlobalTheory.SmGL.piTensor fun j => GlobalTheory.SmGL.piTensor fun i => σ i j)) := by
  intro k _ _ _ _ α β _ _ c _ _ Y _ _ σ
  obtain ⟨e₁, h₁⟩ := exists_pairCurry Y
  obtain ⟨e₂, h₂⟩ := exists_pairCurrySwap Y
  refine ⟨Representation.Equiv.mk (e₁.symm.trans e₂) fun g => ?_⟩
  have key : ∀ w : ⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2,
      e₂ (e₁.symm ((piTensor fun i => piTensor fun j => σ i j) (swapBlocks k c g) (e₁ w))) =
        (piTensor fun j => piTensor fun i => σ i j) g (e₂ w) := by
    intro w
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      have h : (piTensor fun i => piTensor fun j => σ i j) (swapBlocks k c g) (e₁ (tprod ℂ x)) =
          e₁ (tprod ℂ fun p : (Σ _ : α, β) => σ p.1 p.2 (g p.2 p.1) (x p)) := by
        rw [h₁, h₁, piTensor_tprod]
        congr 1
        funext i
        exact piTensor_tprod (fun j => σ i j) _ _
      have h' : (piTensor fun j => piTensor fun i => σ i j) g (e₂ (tprod ℂ x)) =
          e₂ (tprod ℂ fun p : (Σ _ : α, β) => σ p.1 p.2 (g p.2 p.1) (x p)) := by
        rw [h₂, h₂, piTensor_tprod]
        congr 1
        funext j
        exact piTensor_tprod (fun i => σ i j) _ _
      rw [map_smul, map_smul, map_smul, map_smul, map_smul, map_smul, h, h', LinearEquiv.symm_apply_apply]
    | add w w' hw hw' =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hw, hw']
  refine LinearMap.ext fun v => ?_
  obtain ⟨w, rfl⟩ := e₁.surjective v
  have h := key w
  rw [← e₁.symm_apply_apply w, e₁.apply_symm_apply] at h
  exact h

end GlobalTheory.SmGL
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory.JacPiTensor (qlift mk_qlift descend descend_mk)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RelJacTensor

section Spec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  (e' : ∀ i, (Σ j, c i j) ≃ m i) {X : α → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))

theorem piTensor_mulSingle (a : α) (g : GL (m a) k) (x : ∀ j, X j) :
    piTensor ρ (Pi.mulSingle a g) (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (Function.update x a (ρ a g (x a))) := by
  rw [piTensor_tprod]
  congr 1
  funext j
  by_cases h : j = a
  · subst h
    simp
  · simp [h]

def qf : (∀ a, X a) →ₘₗ[ℂ] Jacquet (piTensor ρ) (relUnip k e') :=
  (twKer (piTensor ρ) (relUnip k e') 1).mkQ.compMultilinearMap (PiTensorProduct.tprod ℂ)

theorem qf_update (v : ∀ a, X a) (i : α) (w : X i)
    (hw : w ∈ twKer (ρ i) (unipRad k (e' i)) 1) : qf e' ρ (Function.update v i w) = 0 := by
  unfold twKer at hw
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, y, rfl⟩ := hz
    have hu : (Pi.mulSingle (M := fun a => GL (m a) k) i (n : GL (m i) k)) ∈ relUnip k e' := by
      simp only [relUnip, Subgroup.mem_pi]
      intro j _
      by_cases h : j = i
      · subst h
        simpa using n.2
      · rw [Pi.mulSingle_eq_of_ne h]
        exact one_mem _
    have h1 : PiTensorProduct.tprod ℂ (Function.update v i (ρ i (n : GL (m i) k) y)) =
        piTensor ρ (Pi.mulSingle (M := fun a => GL (m a) k) i (n : GL (m i) k))
          (PiTensorProduct.tprod ℂ (Function.update v i y)) := by
      rw [piTensor_mulSingle]
      simp
    rw [qf, LinearMap.compMultilinearMap_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      MonoidHom.one_apply, Units.val_one, one_smul, MultilinearMap.map_update_sub, h1]
    exact Submodule.subset_span ⟨⟨_, hu⟩, PiTensorProduct.tprod ℂ (Function.update v i y), by simp⟩
  | zero => simp [qf]
  | add z z' _ _ hz hz' => rw [MultilinearMap.map_update_add, hz, hz', add_zero]
  | smul r z _ hz => rw [MultilinearMap.map_update_smul, hz, smul_zero]

end Spec

section Spec2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  (e' : ∀ i, (Σ j, c i j) ≃ m i) {X : α → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))

def qmap : (⨂[ℂ] a, X a) →ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  PiTensorProduct.map fun a => (twKer (ρ a) (unipRad k (e' a)) 1).mkQ

theorem qmap_tprod (x : ∀ a, X a) :
    qmap e' ρ (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a))) := by
  simp only [qmap, PiTensorProduct.map_tprod, Submodule.mkQ_apply]

theorem qmap_comp (u : ∀ a, GL (m a) k) (hu : u ∈ relUnip k e') :
    qmap e' ρ ∘ₗ piTensor ρ u = qmap e' ρ := by
  have hu' : ∀ a, u a ∈ unipRad k (e' a) := by
    intro a
    have h := hu
    simp only [relUnip, Subgroup.mem_pi] at h
    exact h a (Set.mem_univ a)
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod, qmap_tprod]
  congr 1
  funext a
  rw [Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨⟨u a, hu' a⟩, x a, by simp⟩

theorem twKer_le_ker : twKer (piTensor ρ) (relUnip k e') 1 ≤ LinearMap.ker (qmap e' ρ) := by
  rw [twKer, Submodule.span_le]
  rintro _ ⟨n, y, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, MonoidHom.one_apply, Units.val_one, one_smul, map_sub,
    sub_eq_zero]
  exact LinearMap.congr_fun (qmap_comp e' ρ (n : ∀ a, GL (m a) k) n.2) y

def fwd : Jacquet (piTensor ρ) (relUnip k e') →ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  (twKer (piTensor ρ) (relUnip k e') 1).liftQ (qmap e' ρ) (twKer_le_ker e' ρ)

def bwd : (⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a))) →ₗ[ℂ] Jacquet (piTensor ρ) (relUnip k e') :=
  PiTensorProduct.lift (descend (qf e' ρ) (qf_update e' ρ))

theorem bwd_tprod (q : ∀ a, Jacquet (ρ a) (unipRad k (e' a))) :
    bwd e' ρ (PiTensorProduct.tprod ℂ q) = Submodule.Quotient.mk (PiTensorProduct.tprod ℂ
      fun i => qlift (fun a => twKer (ρ a) (unipRad k (e' a)) 1) i (q i)) := by
  rw [bwd, PiTensorProduct.lift.tprod]
  rfl

theorem bwd_tprod_mk (x : ∀ a, X a) :
    bwd e' ρ (PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a)))) =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℂ x) := by
  rw [bwd, PiTensorProduct.lift.tprod, descend_mk]
  rfl

theorem fwd_mk_tprod' (x : ∀ a, X a) :
    fwd e' ρ (Submodule.Quotient.mk (PiTensorProduct.tprod ℂ x)) =
      PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a))) := by
  rw [fwd, Submodule.liftQ_apply, qmap_tprod]

def jacEquiv : Jacquet (piTensor ρ) (relUnip k e') ≃ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  LinearEquiv.ofLinear (fwd e' ρ) (bwd e' ρ)
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun q => ?_)
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, bwd_tprod, fwd_mk_tprod']
      simp only [mk_qlift, LinearMap.compMultilinearMap_apply, LinearMap.id_apply])
    (by
      refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        fwd_mk_tprod', bwd_tprod_mk, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.id_apply,
        Submodule.mkQ_apply])

theorem relJac_piTensor :
    Nonempty ((relJac e' (piTensor ρ)).Equiv (piTensor fun a => GlobalTheory.SmGL.jac (e' a) (ρ a))) := by
  refine ⟨Representation.Equiv.mk (jacEquiv e' ρ) fun g => ?_⟩
  refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
    LinearEquiv.coe_coe, jacEquiv, LinearEquiv.ofLinear_apply, relJac_mk, piTensor_tprod, relEmb_apply,
    map_smul, fwd_mk_tprod', jac_mk, MultilinearMap.map_smul_univ, RingHom.id_apply, relDeltaHalf_apply]
  congr 1
  rw [← Finset.prod_inv_distrib, Units.coe_prod]

end Spec2

theorem relJac_piTensor_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β]
    (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (f : ∀ i, (Σ j, c i j) ≃ m i) (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)),
    Nonempty ((relJac f (piTensor ρ)).Equiv (piTensor fun i => GlobalTheory.SmGL.jac (f i) (ρ i))) := by
  intro k _ _ _ _ α β _ _ _ m _ _ c _ _ f X _ _ ρ
  classical
  exact relJac_piTensor f ρ

end GlobalTheory.RelJacTensor
end
end

section

namespace GlobalTheory.FlagEq
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem eq_of_flag_of_hermForm : ∀ {α : Type} {m : α → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : α, Fin (m τ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) → ∀ (h h' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y)) → ∀ (bv : ∀ τ, Fin (m τ) → (Fin g → ℂ)) (s : ℂ), s ≠ 0 → (∀ τ i, h (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → (∀ τ i, h' (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → h = h' := by
  intro α m g e Hm hpos h h' hH bv s hs hh hh'
  have key : ∀ τ, ∀ i : Fin (m τ), h (Pi.single (e.symm ⟨τ, i⟩) 1) = h' (Pi.single (e.symm ⟨τ, i⟩) 1) := by
    intro τ
    let ev : Fin (m τ) → (Fin g → ℂ) := fun j => Pi.single (e.symm ⟨τ, j⟩) 1
    let E : Fin (m τ) → Submodule ℂ (Fin g → ℂ) := fun i => Submodule.span ℂ (ev '' {j | j < i})
    have ha : ∀ i, Submodule.span ℂ (bv τ '' {j | j < i}) ≤ (E i).map h'.toLinearMap := by
      intro i
      induction i using WellFoundedLT.induction with
      | _ i ih =>
        rw [Submodule.span_le]
        rintro _ ⟨j, hj, rfl⟩
        have hj : j < i := hj
        have h1 : h' (ev j) ∈ (E i).map h'.toLinearMap :=
          Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, hj, rfl⟩)
        have h2 : h' (ev j) - s • bv τ j ∈ (E i).map h'.toLinearMap := by
          have := ih j hj (hh' τ j)
          have hsub : {k : Fin (m τ) | k < j} ⊆ {k | k < i} := by
            intro k hk
            exact lt_trans hk hj
          exact Submodule.map_mono (Submodule.span_mono (Set.image_mono hsub)) this
        have h3 : s • bv τ j ∈ (E i).map h'.toLinearMap := by
          have := Submodule.sub_mem _ h1 h2
          simpa using this
        have := Submodule.smul_mem _ s⁻¹ h3
        rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
        exact this
    intro i
    induction i using WellFoundedLT.induction with
    | _ i ih =>
      have hon : Set.EqOn h.toLinearMap h'.toLinearMap (E i) := by
        apply LinearMap.eqOn_span'
        rintro _ ⟨j, hj, rfl⟩
        exact ih j hj
      set u := h (ev i) - h' (ev i) with hu
      have hu' : u = (h (ev i) - s • bv τ i) - (h' (ev i) - s • bv τ i) := by
        rw [hu]; abel
      have huB : u ∈ Submodule.span ℂ (bv τ '' {j | j < i}) := by
        rw [hu']; exact Submodule.sub_mem _ (hh τ i) (hh' τ i)
      obtain ⟨v, hvE, hv⟩ := ha i huB
      have hv' : h' v = u := hv
      have hhv : h v = u := by
        rw [← hv']; exact hon hvE
      have hx : h (ev i) = h' (ev i) + u := by rw [hu]; abel
      have hE := hH (ev i) v
      rw [hhv, hv', hx] at hE
      have h0 : hermForm Hm u u = 0 := by
        unfold hermForm at hE ⊢
        rw [add_dotProduct] at hE
        simpa using hE
      by_contra hne
      have hne' : u ≠ 0 := by
        intro h0'; apply hne; rw [hu] at h0'; exact sub_eq_zero.mp h0'
      have := hpos u hne'
      rw [h0] at this
      simp at this
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun ℂ (Fin g)).ext
  intro n
  rw [Pi.basisFun_apply]
  have := key (e n).1 (e n).2
  simpa using this

end GlobalTheory.FlagEq
end
