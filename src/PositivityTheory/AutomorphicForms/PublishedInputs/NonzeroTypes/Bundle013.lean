module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle425
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle074
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section

open scoped Classical

open GlobalTheory.SmGL

namespace UpperTheory.TNZ.P_spLat

variable {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {I : Representation ℂ Γ V}

theorem eqvInt {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    {α : Representation ℂ Γ A} {β : Representation ℂ Γ B} (e : α.Equiv β) (g : Γ) (v : A) :
    e (α g v) = β g (e v) :=
  Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v

def eqvTrans {A B C : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] {α : Representation ℂ Γ A} {β : Representation ℂ Γ B}
    {γ : Representation ℂ Γ C} (e : α.Equiv β) (f : β.Equiv γ) : α.Equiv γ :=
  Representation.Equiv.mk (e.toLinearEquiv.trans f.toLinearEquiv) (fun g => by
    ext v
    show f (e (α g v)) = γ g (f (e v))
    rw [eqvInt e, eqvInt f])

theorem dich {A : Type} [AddCommGroup A] [Module ℂ A] {α : Representation ℂ Γ A} (hα : α.IsIrreducible)
    (X Y S : Subrepresentation I) (e : (subQuot Y X).Equiv α) :
    Y ⊓ S ≤ X ∨ Y ≤ S ⊔ X := by
  let T : Subrepresentation α :=
    ⟨((S.toSubmodule.comap Y.toSubmodule.subtype).map
        (X.toSubmodule.comap Y.toSubmodule.subtype).mkQ).map e.toLinearMap, by
      rintro g _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨_, ⟨Y.toRepresentation g v, S.apply_mem_toSubmodule g hv, rfl⟩, ?_⟩
      exact eqvInt e g (Submodule.Quotient.mk v)⟩
  rcases hα.eq_bot_or_eq_top T with hT | hT
  · left
    intro v hv
    obtain ⟨hvY, hvS⟩ := hv
    have hm : e (Submodule.Quotient.mk (⟨v, hvY⟩ : Y.toSubmodule)) ∈ T.toSubmodule :=
      ⟨_, ⟨⟨v, hvY⟩, hvS, rfl⟩, rfl⟩
    rw [hT] at hm
    have h0 : e (Submodule.Quotient.mk (⟨v, hvY⟩ : Y.toSubmodule)) = 0 := (Submodule.mem_bot ℂ).1 hm
    rw [map_eq_zero_iff e (EquivLike.injective e), Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  · right
    intro v hvY
    have hm : e (Submodule.Quotient.mk (⟨v, hvY⟩ : Y.toSubmodule)) ∈ T.toSubmodule := by
      rw [hT]; exact Submodule.mem_top
    obtain ⟨_, ⟨w, hwS, rfl⟩, hw⟩ := hm
    have hw' := EquivLike.injective e hw
    have hx0 := (Submodule.Quotient.eq (X.toSubmodule.comap Y.toSubmodule.subtype)).1 hw'
    have hx : (w : V) - v ∈ X.toSubmodule := hx0
    show v ∈ S.toSubmodule ⊔ X.toSubmodule
    refine Submodule.mem_sup.2 ⟨w, hwS, v - w, ?_, by abel⟩
    simpa using X.toSubmodule.neg_mem hx

def eqv (Z W Y X : Subrepresentation I) (hZY : Z ≤ Y) (hY : Y ≤ Z ⊔ X)
    (hW : Z ⊓ W = Z ⊓ X) : (subQuot Z W).Equiv (subQuot Y X) := by
  let f : Z.toSubmodule →ₗ[ℂ] (Y.toSubmodule ⧸ X.toSubmodule.comap Y.toSubmodule.subtype) :=
    (X.toSubmodule.comap Y.toSubmodule.subtype).mkQ ∘ₗ Submodule.inclusion hZY
  have hf : Function.Surjective f := by
    rintro ⟨⟨v, hv⟩⟩
    obtain ⟨z, hz, x, hx, rfl⟩ := Submodule.mem_sup.1 (hY hv)
    refine ⟨⟨z, hz⟩, ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    refine (Submodule.Quotient.eq _).2 ?_
    show z - (z + x) ∈ X.toSubmodule
    simpa using X.toSubmodule.neg_mem hx
  have hker : W.toSubmodule.comap Z.toSubmodule.subtype = LinearMap.ker f := by
    ext ⟨v, hv⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, f,
      LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show v ∈ W.toSubmodule ↔ v ∈ X.toSubmodule
    have h := congrArg Subrepresentation.toSubmodule hW
    simp only [Subrepresentation.toSubmodule_inf] at h
    constructor
    · intro hw
      have : v ∈ Z.toSubmodule ⊓ W.toSubmodule := ⟨hv, hw⟩
      rw [h] at this
      exact this.2
    · intro hx
      have : v ∈ Z.toSubmodule ⊓ X.toSubmodule := ⟨hv, hx⟩
      rw [← h] at this
      exact this.2
  refine Representation.Equiv.mk ((Submodule.quotEquivOfEq _ _ hker).trans
    (f.quotKerEquivOfSurjective hf)) (fun g => ?_)
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply]
  rfl

end UpperTheory.TNZ.P_spLat

namespace UpperTheory.TNZ

open P_spLat in
theorem step_spLat : SpecialLatticeProp := by
  intro Γ V _ _ _ I d hmono hmod htop A B _ _ _ _ α β hα hβ h₁ h₂
  obtain ⟨X₁, Y₁, hXY₁, hd₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨X₂, Y₂, hXY₂, hd₂, ⟨e₂⟩⟩ := h₂
  have hY₁ : d Y₁ ≤ 1 := (hmono le_top).trans htop
  have hY₂ : d Y₂ ≤ 1 := (hmono le_top).trans htop
  have hZ : d (Y₁ ⊓ Y₂) = 1 := by
    have := hmod Y₁ Y₂
    have := (hmono (le_top : Y₁ ⊔ Y₂ ≤ ⊤)).trans htop
    have := hmono (inf_le_left : Y₁ ⊓ Y₂ ≤ Y₁)
    omega
  have hN : d (X₁ ⊔ X₂) = 0 := by
    have := hmod X₁ X₂
    omega
  set Z := Y₁ ⊓ Y₂ with hZdef
  set N := X₁ ⊔ X₂ with hNdef
  have side : ∀ (C : Type) [AddCommGroup C] [Module ℂ C] (γ : Representation ℂ Γ C), γ.IsIrreducible →
      ∀ X Y : Subrepresentation I, X ≤ Y → X ≤ N → Z ≤ Y → d X = 0 → (subQuot Y X).Equiv γ →
      Y ≤ Z ⊔ X ∧ Z ⊓ N = Z ⊓ X := by
    intro C _ _ γ hγ X Y hXY hXN hZY hX e
    refine ⟨?_, ?_⟩
    · rcases dich hγ X Y Z e with h | h
      · exfalso
        have h' : Z ≤ X := by
          have : Y ⊓ Z = Z := inf_eq_right.2 hZY
          rw [← this]; exact h
        have := hmono h'
        omega
      · exact h
    · rcases dich hγ X Y N e with h | h
      · apply le_antisymm
        · exact le_inf inf_le_left ((inf_le_inf_right N hZY).trans h)
        · exact inf_le_inf_left Z hXN
      · exfalso
        have h' : Z ≤ N := hZY.trans (h.trans (sup_le le_rfl hXN))
        have := hmono h'
        omega
  have hd1 : d X₁ = 0 := by omega
  have hd2 : d X₂ = 0 := by omega
  obtain ⟨s₁, t₁⟩ := side A α hα X₁ Y₁ hXY₁ le_sup_left inf_le_left hd1 e₁
  obtain ⟨s₂, t₂⟩ := side B β hβ X₂ Y₂ hXY₂ le_sup_right inf_le_right hd2 e₂
  exact ⟨eqvTrans (eqvTrans e₁.symm (eqv Z N Y₁ X₁ inf_le_left s₁ t₁).symm)
    (eqvTrans (eqv Z N Y₂ X₂ inf_le_right s₂ t₂) e₂)⟩

end UpperTheory.TNZ
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spPiSub

theorem exists_equiv_of_map_eq {ι κ α : Type*} [Fintype ι] [Fintype κ] (f : ι → α) (g : κ → α)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) : ∃ e : ι ≃ κ, ∀ i, g (e i) = f i := by
  have hc : ∀ c, Fintype.card {i // f i = c} = Fintype.card {j // g j = c} := by
    intro c
    have h1 := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at h1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card, Finset.filter_val, eq_comm] using h1
  exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hc c), fun i => Equiv.ofFiberEquiv_map _ i⟩

theorem map_univ_eq_sum {ι α : Type*} [Fintype ι] (φ : ι → α) :
    Finset.univ.val.map φ = ∑ i, ({φ i} : Multiset α) := by
  rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton (Multiset.map φ Finset.univ.val),
    Multiset.map_map]
  rfl

theorem sum_map_univ {s n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {α : Type*}
    (F : ∀ a, Fin (d a) → α) :
    ∑ a, Finset.univ.val.map (F a) = Finset.univ.val.map fun i => F (e.symm i).1 (e.symm i).2 := by
  calc ∑ a, Finset.univ.val.map (F a) = ∑ a, ∑ j, ({F a j} : Multiset α) := by
        simp only [map_univ_eq_sum]
    _ = ∑ p : Σ a, Fin (d a), ({F p.1 p.2} : Multiset α) := (Fintype.sum_sigma (fun p : Σ a, Fin (d a) => ({F p.1 p.2} : Multiset α))).symm
    _ = ∑ i, ({F (e.symm i).1 (e.symm i).2} : Multiset α) :=
        (Equiv.sum_comp e.symm (fun p : Σ a, Fin (d a) => ({F p.1 p.2} : Multiset α))).symm
    _ = _ := (map_univ_eq_sum _).symm

end UpperTheory.TNZ.Grp.P_spPiSub

namespace UpperTheory.TNZ.Grp

open P_spPiSub

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_spPiSub {n : ℕ} (G : Grp k n) : G.SpecialRepresentationSubProp := by
  intro hOrd hL Y _ _ τ _ _ ν hν hc hI
  let χ : Fin G.s → kˣ →* ℂˣ := fun a => absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))
  have hχ : ∀ a, IsSmoothChar (χ a) := fun a => isSmoothChar_absPow _
  have hsupp : ∀ a, HasSupport (G.twD τ a)
      (Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) := by
    intro a
    have h1 := (hasSupport_of_isCuspSupport (hc a)).tw (χ a) (hχ a)
    rw [Multiset.map_map] at h1
    convert h1 using 2
    · rfl
    · rename_i j _
      exact (IrrGL.tw_ofChar (ν a j) (χ a) (hν a j) (hχ a)).symm
  have hcOf : ∀ i, IsSmoothChar (G.cOf ν i) := fun i => (hν _ _).mul (isSmoothChar_absPow _)
  have hS := SupportRing.hasSupport_multiProd hL.loc.zel G.hd (G.twD τ) (fun a => (hsupp a).isSmooth)
    (fun a => (hsupp a).isIrreducible) hsupp hI
  have hsum : (∑ a, Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) =
      Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i) :=
    sum_map_univ G.e (fun a j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a)))
  obtain ⟨h, x, hx, -, -, e', he⟩ := hS
  rw [hsum] at hx
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq x (fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i)) hx
  obtain rfl : x = fun b => IrrGL.ofChar (G.cOf ν (σ b)) (hcOf _) := funext fun b => (hσ b).symm
  have hn : h = n := by simpa using Fintype.card_congr σ
  subst hn
  let φ := multiProdEquiv e' fun b =>
    (equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ b)) (hcOf _))).symm
  have hsq : IsSubquotient (multiProd G.e (G.twD τ)) (prinSeries fun b => G.cOf ν (σ b)) :=
    (he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)).trans
      (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e' _)
  exact hOrd hL _ _ (isSmooth_parInd _ _) hI _ hcOf σ hsq

end UpperTheory.TNZ.Grp
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spOrd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sum_one (n : ℕ) : ∑ _a : Fin n, (1 : ℕ) = n := by simp

theorem stdBlocks_one (n : ℕ) :
    (stdBlocks (fun _ : Fin n => 1) (sum_one n) : (Σ _ : Fin n, Fin 1) ≃ Fin n) =
      Equiv.sigmaUnique (Fin n) (fun _ => Fin 1) := by
  refine Equiv.ext fun x => ?_
  obtain ⟨a, i⟩ := x
  refine Fin.ext ?_
  rw [stdBlocks_val]
  simp

theorem isSmooth_detRep1 {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : IsSmooth (detRep (Fin 1) χ) :=
  (isSmooth_ofChar_iff _).2 (h.detChar (n := Fin 1))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem hasFiniteLength_detRep1 (χ : kˣ →* ℂˣ) : HasFiniteLength (detRep (R := k) (Fin 1) χ) :=
  hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _)

theorem prin_sub_multi {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) :
    IsSubquotient (prinSeries χ)
      (multiProd (stdBlocks (fun _ : Fin n => 1) (sum_one n)) fun i => detRep (Fin 1) (χ i)) := by
  have h := GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ
  rw [← stdBlocks_one] at h
  exact h

end UpperTheory.TNZ.Grp.P_spOrd

namespace UpperTheory.TNZ.Grp

open UpperTheory.TNZ.Grp.P_spOrd GlobalTheory.LocGL.SupportRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem step_spOrd : SpecialOrderProp (k := k) (n := n) := by
  intro hL V _ _ π hs hi c hc σ h
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hL.loc.zel k
  obtain ⟨hp1, e1⟩ := multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n)
    (fun i => detRep (Fin 1) (c (σ i))) (fun i => isSmooth_detRep1 (hc (σ i)))
    (fun i => hasFiniteLength_detRep1 (c (σ i)))
  obtain ⟨hp2, e2⟩ := multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n)
    (fun i => detRep (Fin 1) (c i)) (fun i => isSmooth_detRep1 (hc i))
    (fun i => hasFiniteLength_detRep1 (c i))
  have hcl : clsGL _ hp1 = clsGL _ hp2 := by
    apply Ψ.injective
    rw [e1, e2]
    exact Equiv.prod_comp σ (fun i => Ψ (clsGL (detRep (Fin 1) (c i)) (hasFiniteLength_detRep1 (c i))))
  have h1 := h.trans (prin_sub_multi (fun i => c (σ i)))
  have h2 := clsGL_of_pos hp1 hs hi h1
  rw [hcl] at h2
  exact (isSubquotient_of_clsGL_ne hp2 hs hi h2.ne').trans
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries _ c)

end UpperTheory.TNZ.Grp
end
end
