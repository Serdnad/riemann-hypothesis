module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLSeriesContinuation
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle003
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle117
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle069
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle036
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional.ColumnWeights

theorem getD_flatMap_append {α : Type} (F : α → List ℚ) (s : ℕ) (hF : ∀ a, (F a).length = s) (t : List ℚ) :
    ∀ (l : List α) (j q : ℕ) (hj : j < l.length), q < s →
      (l.flatMap F ++ t).getD (j * s + q) 0 = (F l[j]).getD q 0 := by
  intro l
  induction l with
  | nil =>
    intro j q hj _
    simp at hj
  | cons a l ih =>
    intro j q hj hq
    cases j with
    | zero =>
      rw [List.flatMap_cons, List.append_assoc, zero_mul, zero_add,
        List.getD_append _ _ _ _ (by rw [hF]; exact hq)]
      rfl
    | succ j =>
      rw [List.flatMap_cons, List.append_assoc,
        List.getD_append_right _ _ _ _ (by rw [hF]; nlinarith), hF]
      have e : (j + 1) * s + q - s = j * s + q := by rw [add_mul]; omega
      rw [e]
      exact ih j q (by simpa using hj) hq

theorem flatMap_sublist {α β : Type} (F G : α → List β) (h : ∀ a, (F a).Sublist (G a)) :
    ∀ l : List α, (l.flatMap F).Sublist (l.flatMap G)
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (h a).append (flatMap_sublist F G h l)

variable {S : Sizes}

theorem small_sublist (Q : Entries S) : Q.smallPar.Sublist Q.orderList := by
  unfold Entries.smallPar Entries.basePar Entries.orderList
  rw [← List.append_assoc]
  refine List.Sublist.append (List.Sublist.append (List.Sublist.cons _ ?_) ?_) (List.Sublist.refl _)
  · exact flatMap_sublist _ _ (fun a => List.sublist_append_left _ _) _
  · rw [List.map_eq_flatMap]
    exact flatMap_sublist _ _ (fun a => by simp) _

theorem small_int (Q : Entries S) : ∀ x ∈ Q.smallPar, ∃ z : ℤ, x = z := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · obtain ⟨j, -, h⟩ := List.mem_flatMap.1 h
    exact block_odd (Q.c j) S.s_odd x h
  · exact base_int Q x h

def ent (Q : Entries S) (j : ℕ) : ℤ := ⌊Q.smallPar.getD j 0⌋

theorem ent_cast (Q : Entries S) (j : ℕ) (hj : j < S.nC S.m) : (ent Q j : ℚ) = Q.smallPar.getD j 0 := by
  rw [← length_small Q] at hj
  obtain ⟨z, hz⟩ := small_int Q _ (List.getElem_mem hj)
  rw [ent, List.getD_eq_getElem _ _ hj, hz, Int.floor_intCast]

theorem ent_succ (Q : Entries S) (hQ : Q.Good) (j : ℕ) (hj : j + 1 < S.nC S.m) : ent Q (j + 1) < ent Q j := by
  have h := List.pairwise_iff_getElem.1 (hQ.order.sublist (small_sublist Q)) j (j + 1)
    (by rw [length_small]; omega) (by rw [length_small]; omega) (by omega)
  have h1 := ent_cast Q j (by omega)
  have h2 := ent_cast Q (j + 1) hj
  rw [List.getD_eq_getElem _ _ (by rw [length_small]; omega)] at h1 h2
  rw [← h1, ← h2] at h
  exact_mod_cast h

theorem ent_add (Q : Entries S) (hQ : Q.Good) (j : ℕ) : ∀ d : ℕ, j + d < S.nC S.m → ent Q (j + d) + d ≤ ent Q j := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := ent_succ Q hQ (j + d) (by omega)
    rw [← add_assoc]
    push_cast
    omega

theorem nC_le {i : ℕ} (hi : i ≤ S.m) : S.nC i ≤ S.nC S.m := by
  unfold Sizes.nC
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _

def kap (Q : Entries S) (hQ : Q.Good) (i : Fin (S.m + 1)) : DomWeight (S.nC i) where
  w r := -ent Q (S.nC S.m - 1 - r) + (r : ℕ) + 1 - ((S.nC i + 1) / 2 : ℕ)
  anti a b hab := by
    have h1 : S.nC i ≤ S.nC S.m := nC_le (by omega)
    have ha := a.2
    have hb := b.2
    have hab' : (a : ℕ) ≤ b := hab
    have h := ent_add Q hQ (S.nC S.m - 1 - b) (b - a) (by omega)
    have e : S.nC S.m - 1 - b + (b - a) = S.nC S.m - 1 - a := by omega
    rw [e] at h
    simp only
    omega

theorem ent_block (Q : Entries S) (j : Fin S.m) (q a : ℕ) (ha : S.s = 2 * a + 1) (hq : q < S.s) :
    ent Q (j * S.s + q) = Q.c j + a - q := by
  have h := getD_flatMap_append (fun i : Fin S.m => block (Q.c i) S.s) S.s (fun _ => length_block _ _) Q.basePar
    (List.finRange S.m) j q (by simp) hq
  rw [ent, Entries.smallPar, h, List.getD_eq_getElem _ _ (by rw [length_block]; exact hq)]
  simp only [block, List.getElem_map, List.getElem_range, List.getElem_finRange, Fin.cast_mk, Fin.eta]
  have : (Q.c j : ℚ) + ((S.s : ℚ) - 1) / 2 - q = ((Q.c j + a - q : ℤ) : ℚ) := by
    rw [ha]; push_cast; ring
  rw [this, Int.floor_intCast]

theorem ent_base (Q : Entries S) (q : ℕ) : ent Q (S.m * S.s + q) = ⌊Q.basePar.getD q 0⌋ := by
  have hl : ((List.finRange S.m).flatMap fun i => block (Q.c i) S.s).length = S.m * S.s := by
    simp [List.length_flatMap, length_block]
  rw [ent, Entries.smallPar, List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left]

theorem hw_odd (p : List ℚ) (a : ℕ) (ha : p.length = 2 * a + 1) (i : ℕ) : hw p i = ⌊p.getD i 0⌋ - a + i := by
  have : p.getD i 0 - (((p.length : ℚ) - 1) / 2 - i) = p.getD i 0 + ((-a + i : ℤ) : ℚ) := by
    rw [ha]; push_cast; ring
  rw [hw, this, Int.floor_add_intCast]; ring

theorem exists_column_weights (S : Sizes) (Q : Entries S) (hQ : Q.Good) :
    ∃ kap : ∀ i : Fin (S.m + 1), DomWeight (S.nC i), (∀ r, (kap 0).dual.w r = hw Q.basePar r) ∧
      (∀ r, (kap (Fin.last _)).dual.w r = hw Q.smallPar r) ∧
      ∀ i : Fin S.m, StepW (Q.c i.rev - ((S.nC i.succ + 1) / 2 : ℕ)) (-Q.c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ))
        (kap i.castSucc) (kap i.succ) := by
  refine ⟨kap Q hQ, fun r => ?_, fun r => ?_, fun i r => ?_⟩
  · obtain ⟨r, hr⟩ := r
    obtain ⟨a, ha⟩ : Odd (S.nC 0) := odd_nC ⟨0, rfl⟩
    have h0 : S.nC S.m = S.m * S.s + S.nC 0 := by unfold Sizes.nC; omega
    simp only [DomWeight.dual, kap, Fin.val_rev, Fin.val_zero] at hr ⊢
    have e : S.nC S.m - 1 - (S.nC 0 - (r + 1)) = S.m * S.s + r := by omega
    rw [e, ent_base, hw_odd _ a (by rw [length_base, ha])]
    omega
  · obtain ⟨r, hr⟩ := r
    obtain ⟨a, ha⟩ : Odd (S.nC S.m) := odd_nC S.m_even
    simp only [DomWeight.dual, kap, Fin.val_rev, Fin.val_last] at hr ⊢
    have e : S.nC S.m - 1 - (S.nC S.m - (r + 1)) = r := by omega
    rw [e, hw_odd _ a (by rw [length_small, ha]), ent]
    omega
  · obtain ⟨r, hr⟩ := r
    simp only [kap, Fin.val_succ, Fin.val_castSucc] at hr ⊢
    split_ifs with h
    · ring
    · obtain ⟨a, ha⟩ := S.s_odd
      have h1 : S.nC (i + 1) = S.nC i + S.s := by unfold Sizes.nC; ring
      have h2 : S.nC S.m = S.nC (i + 1) + (i.rev : ℕ) * S.s := by
        have : S.m = i + 1 + (i.rev : ℕ) := by rw [Fin.val_rev]; have := i.2; omega
        unfold Sizes.nC
        rw [add_assoc _ ((i + 1) * S.s), ← add_mul, ← this]
      have e : S.nC S.m - 1 - r = (i.rev : ℕ) * S.s + (S.nC (i + 1) - 1 - r) := by omega
      rw [e, ent_block Q i.rev _ a ha (by omega)]
      omega

end GlobalTheory.OneFunctional.ColumnWeights
end

section

noncomputable section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem contracts_of_iso_directSum (H G I F V : Type) [Monoid H] [Monoid G] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup V] [Module ℂ V] (A B : I → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (a : ∀ i, Representation ℂ H (A i))
    (b : ∀ i, Representation ℂ G (B i)) (φ : Representation ℂ (H × G) F) (σ : Representation ℂ H V) (i₀ : I)
    (hφ : Iso (Representation.directSum fun i =>
      Representation.tprod ((a i).comp (MonoidHom.fst H G)) ((b i).comp (MonoidHom.snd H G))) φ)
    (h0 : ∀ i, i ≠ i₀ → invFun ((a i).tprod σ) = ⊥)
    (h1 : Module.finrank ℂ (invFun ((a i₀).tprod σ)) = 1) : Contracts φ σ (b i₀) := by
  classical
  refine Contracts.congr ?_ hφ (Iso.refl σ) (Iso.refl _)
  obtain ⟨⟨ε, hε⟩, hne, hspan⟩ := finrank_eq_one_iff'.1 h1
  have hε0 : ε ≠ 0 := fun h => hne (Subtype.ext h)
  have hεi : ∀ h x v, ε (a i₀ h x ⊗ₜ σ h v) = ε (x ⊗ₜ v) := fun h x v => by
    simpa using mem_invFun.1 hε h (x ⊗ₜ v)
  obtain ⟨z, hz⟩ : ∃ z, ε z = 1 := LinearMap.surjective hε0 1
  let P : (A i₀ ⊗[ℂ] B i₀) ⊗[ℂ] V →ₗ[ℂ] B i₀ :=
    (TensorProduct.lid ℂ (B i₀)).toLinearMap ∘ₗ LinearMap.rTensor (B i₀) ε ∘ₗ
      (TensorProduct.rightComm ℂ (A i₀) (B i₀) V).toLinearMap
  have hP : ∀ x y v, P ((x ⊗ₜ y) ⊗ₜ v) = ε (x ⊗ₜ v) • y := fun x y v => by simp [P]
  let J : ∀ i, B i → A i ⊗[ℂ] V →ₗ[ℂ] (⨁ i, A i ⊗[ℂ] B i) ⊗[ℂ] V := fun i y =>
    LinearMap.rTensor V (DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] B i) i ∘ₗ (TensorProduct.mk ℂ (A i) (B i)).flip y)
  have hJ : ∀ i y x v, J i y (x ⊗ₜ v) = DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] B i) i (x ⊗ₜ y) ⊗ₜ v :=
    fun i y x v => by simp [J]
  let π : (⨁ i, A i ⊗[ℂ] B i) ⊗[ℂ] V →ₗ[ℂ] B i₀ :=
    P ∘ₗ LinearMap.rTensor V (DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀)
  have hπ : ∀ f v, π (f ⊗ₜ v) = P (DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀ f ⊗ₜ v) :=
    fun f v => by simp [π]
  have hπJ : ∀ y w, π (J i₀ y w) = ε w • y := fun y w => by
    induction w with
    | tmul x v => rw [hJ, hπ, DirectSum.component.lof_self, hP]
    | add s t hs ht => simp only [map_add (f := _), hs, ht, add_smul]
  have hπJ' : ∀ i, i ≠ i₀ → ∀ y x v, π (J i y (x ⊗ₜ v)) = 0 := fun i hi y x v => by
    rw [hJ, hπ, DirectSum.component.of, dite_eq_right hi]; simp
  refine ⟨π, fun y => ⟨J i₀ y z, by rw [hπJ, hz, one_smul]⟩, fun h g f v => ?_, fun l hl => ?_⟩
  · rw [hπ, hπ]
    have e : DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀ ((Representation.directSum fun i =>
        Representation.tprod ((a i).comp (MonoidHom.fst H G)) ((b i).comp (MonoidHom.snd H G))) (h, g) f) =
        TensorProduct.map (a i₀ h) (b i₀ g) (DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀ f) := rfl
    rw [e]
    generalize DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀ f = t
    induction t with
    | tmul x y => rw [TensorProduct.map_tmul, hP, hP, hεi, map_smul]
    | add s t hs ht => simp only [map_add (f := _), TensorProduct.add_tmul, hs, ht]
  · have hinv : ∀ i y, l ∘ₗ J i y ∈ invFun ((a i).tprod σ) := fun i y => mem_invFun.2 fun h w => by
      induction w with
      | tmul x v =>
        have := hl h (DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] B i) i (x ⊗ₜ y)) v
        simpa [hJ] using this
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    let c : B i₀ →ₗ[ℂ] ℂ := l ∘ₗ LinearMap.rTensor V (DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] B i) i₀) ∘ₗ
      (TensorProduct.rightComm ℂ (A i₀) (B i₀) V).symm.toLinearMap ∘ₗ TensorProduct.mk ℂ _ _ z
    have hc : ∀ y, c y = l (J i₀ y z) := fun y => by
      simp only [c, LinearMap.comp_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe]
      congr 1
      generalize z = w
      induction w with
      | tmul x v => simp [hJ]
      | add s t hs ht => simp only [map_add (f := _), TensorProduct.add_tmul, hs, ht]
    have key : ∀ i y x v, l (J i y (x ⊗ₜ v)) = c (π (J i y (x ⊗ₜ v))) := fun i y x v => by
      by_cases hi : i = i₀
      · subst hi
        obtain ⟨r, hr⟩ := hspan ⟨_, hinv i y⟩
        have hr' : ∀ w, l (J i y w) = r * ε w := fun w => by
          simpa using (congrArg (fun m : invFun ((a i).tprod σ) => m.1 w) hr).symm
        rw [hπJ, map_smul, hc, hr', hr', hz, smul_eq_mul]
        ring
      · have := hinv i y
        rw [h0 i hi, Submodule.mem_bot] at this
        rw [hπJ' i hi, map_zero]
        exact LinearMap.congr_fun this _
    have hl' : l = c ∘ₗ π := by
      refine TensorProduct.ext (DirectSum.linearMap_ext _ fun i => TensorProduct.ext' fun x y => ?_)
      ext v
      simpa [hJ] using key i y x v
    intro x hx
    rw [hl', LinearMap.comp_apply, hx, map_zero]

end GlobalTheory.OneFunctional
end
end

section

noncomputable section

namespace GlobalTheory.DefFree

theorem isProj_eig_average {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (P : Subgroup G) [Fintype P] (χ : P →* ℂˣ) :
    LinearMap.IsProj (GlobalTheory.DefFree.eig ρ P fun g => ((χ g : ℂˣ) : ℂ))
      ((Fintype.card P : ℂ)⁻¹ • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • (ρ g : M →ₗ[ℂ] M)) := by
  classical
  have hcard : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have happ : ∀ x : M, ((Fintype.card P : ℂ)⁻¹ • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • (ρ g : M →ₗ[ℂ] M)) x
      = (Fintype.card P : ℂ)⁻¹ • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x := by
    intro x
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  ·
    rw [happ, mem_eig]
    intro h
    have hsum : ρ h (∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x)
        = ((χ h : ℂˣ) : ℂ) • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x := by

      rw [map_sum, Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
      have hc : ((χ h : ℂˣ) : ℂ) * (((χ (h * g))⁻¹ : ℂˣ) : ℂ) = (((χ g)⁻¹ : ℂˣ) : ℂ) := by
        rw [← Units.val_mul, map_mul, mul_inv, mul_inv_cancel_left]
      show ρ h ((((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x)
        = ((χ h : ℂˣ) : ℂ) • ((((χ (h * g))⁻¹ : ℂˣ) : ℂ) • ρ ((h * g : P) : G) x)
      rw [smul_smul, hc, map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    show ρ h (_ • _) = ((χ h : ℂˣ) : ℂ) • (_ • _)
    rw [map_smul, hsum, smul_comm]
  ·
    have hx' : ∀ g : P, ρ g x = ((χ g : ℂˣ) : ℂ) • x := fun g => (mem_eig.mp hx) g
    have hterm : ∀ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x = x := fun g => by
      rw [hx' g, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rw [happ]
    simp only [hterm, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

theorem card_mul_finrank_eig (G M : Type) [Group G] [Finite G] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ G M) (P : Subgroup G) (χ : P →* ℂˣ)
    (h : ∀ g ∈ P, g ≠ 1 → LinearMap.trace ℂ M (ρ g) = 0) :
    Nat.card P * Module.finrank ℂ (GlobalTheory.DefFree.eig ρ P fun g => ((χ g : ℂˣ) : ℂ)) = Module.finrank ℂ M := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  have htr := (isProj_eig_average ρ P χ).trace

  rw [map_smul, map_sum, smul_eq_mul] at htr
  simp only [map_smul, smul_eq_mul] at htr

  rw [Finset.sum_eq_single (1 : P) (fun g _ hg => by
      rw [h g g.2 (fun h1 => hg (Subtype.ext h1)), mul_zero])
    (fun h1 => absurd (Finset.mem_univ _) h1)] at htr
  rw [map_one, inv_one, Units.val_one, one_mul, OneMemClass.coe_one, map_one,
    LinearMap.trace_one] at htr
  have hcard : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Nat.card_eq_fintype_card]
  have key : (Fintype.card P : ℂ) * (Module.finrank ℂ (GlobalTheory.DefFree.eig ρ P fun g => ((χ g : ℂˣ) : ℂ)) : ℂ)
      = (Module.finrank ℂ M : ℂ) := by
    rw [← htr, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  exact_mod_cast key

end GlobalTheory.DefFree

end
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)

namespace GlobalTheory.HeckeOne
open GlobalTheory.CMVal (eulerFactor IsHeckeL)
variable {K : Type} [Field K] [NumberField K]

theorem two_le_N (P : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm P.asIdeal :=
  NumberField.HeightOneSpectrum.one_lt_absNorm P

theorem sumN (σ : ℝ) (hσ : 1 < σ) : Summable fun P : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) :=
  ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 σ hσ).2

theorem nonemptyN : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩⟩

noncomputable def cf (χ : HChar K) (P : HeightOneSpectrum (𝓞 K)) : ℂ := if χ.UnrAt P then ((χ.val P : ℂˣ) : ℂ) else 0

theorem norm_cf {χ : HChar K} (h : χ.IsUnitary) (P : HeightOneSpectrum (𝓞 K)) : ‖cf χ P‖ ≤ 1 := by
  unfold cf; split_ifs
  · exact (h _).le
  · simp

theorem hasProd_exp {χ : HChar K} (h : χ.IsUnitary) {s : ℂ} (hs : 1 < s.re) : HasProd (eulerFactor χ s)
    (Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - cf χ P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)))) := by
  refine (((GlobalTheory.eulerProduct_eq_exp_and_pos _ (fun P : HeightOneSpectrum (𝓞 K) => Ideal.absNorm P.asIdeal) (cf χ) two_le_N
    (norm_cf h) sumN).1 s hs).2).congr_fun fun P => ?_
  unfold eulerFactor cf; split_ifs <;> simp

theorem eulerFactor_mul_normChar (χ : HChar K) (t : ℝ) (s : ℂ) :
    eulerFactor (χ * normChar K t) s = eulerFactor χ (s + (t : ℂ) * Complex.I) := by
  funext v
  have hiff : (χ * normChar K t).UnrAt v ↔ χ.UnrAt v :=
    ⟨fun h => by simpa using h.mul (unrAt_normChar t v).inv, fun h => h.mul (unrAt_normChar t v)⟩
  have hN := two_le_N v
  unfold eulerFactor
  by_cases h : χ.UnrAt v
  · rw [if_pos h, if_pos (hiff.2 h), Formalism.L2.Host.HChar.val_mul, Units.val_mul, val_normChar, mul_assoc,
      ← Complex.cpow_add _ _ (by exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0))]
    congr 4; ring
  · rw [if_neg h, if_neg (mt hiff.1 h)]

theorem entire_of_not_normPow {χ : HChar K} (hu : χ.IsUnitary) (hχ : ¬ ∃ t : ℝ, IsNormPow χ t) :
    ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ := by
  obtain ⟨t, φ, hφ1, hφ2, hφ3, hφ4, hφ5⟩ := GlobalTheory.HeckeOne.exists_normChar_smooth_homogeneous_inf K χ hu
  set χ₀ := χ * normChar K (-t) with hχ₀
  have he : χ = χ₀ * normChar K t := by
    rw [hχ₀, mul_assoc, ← normChar_add, neg_add_cancel, normChar_zero, mul_one]
  have hu₀ : χ₀.IsUnitary := hu.mul (isUnitary_normChar _)
  obtain ⟨m, X, hm, hX0, hX1, hXm, hXn, hXz, hXP, hXβ⟩ := GlobalTheory.T.exists_idealCharacter_of_unitary_heckeChar K χ₀ hu₀
  have hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β) := fun β h0 h1 => by
    have h0' : (β : K) ≠ 0 := by exact_mod_cast h0
    rw [hXβ β (Units.mk0 _ h0') rfl h1, ← hφ5]; rfl
  have hJ : ∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hφ := GlobalTheory.eq_one_of_homogeneous_of_eq_one_on_class K m φ hm hφ3.continuousOn hφ2 (fun β h0 h1 => by
      rw [← hβ β h0 h1]
      refine hcon _ (by rwa [Ne, Ideal.span_singleton_eq_bot]) ?_
      rw [Ideal.eq_top_iff_one, show (1 : 𝓞 K) = β - (β - 1) by ring]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self β)) (Ideal.mem_sup_right h1))
    have h1 : χ₀ = 1 := GlobalTheory.HeckeUnrTrivial.eq_one_of_inf_of_val K χ₀ (fun k => by
      have := hφ (mixedEmbedding K (k : K)) (by
        rw [mixedEmbedding.norm_eq_norm]
        exact_mod_cast abs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 k.ne_zero))
      rw [hφ5, inv_eq_one] at this
      exact Units.ext this) fun v hv => by
      have h2 := hXP v
      rw [if_pos hv] at h2
      refine Units.ext (h2.symm.trans (hcon _ v.ne_bot ?_))
      by_contra h3
      exact (χ₀.val v).ne_zero (h2.symm.trans (hXz _ h3))
    exact hχ ⟨t, (isNormPow_iff _ _).2 (by rw [he, h1, one_mul])⟩
  have hle : ∀ I, ‖X I‖ ≤ 1 := fun I => by
    by_cases hI : I = ⊥
    · simp [hI, hX0]
    by_cases hI' : I ⊔ m = ⊤
    · exact (hXn I hI hI').le
    · simp [hXz I hI']
  obtain ⟨Z, hZd, hZ, hZ1⟩ := GlobalTheory.idealCharacter_LSeries_continuation K m X φ hm hX0 hXm hXn hXz hφ1 hφ2 hφ3 hφ4 hβ
  have hd : Differentiable ℂ (dslope Z 1) := by
    rw [← differentiableOn_univ] at hZd ⊢
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hZd
  refine ⟨fun s => dslope Z 1 (s + (t : ℂ) * Complex.I), hd.comp (by fun_prop), fun s hs => ?_⟩
  have hs' : 1 < (s + (t : ℂ) * Complex.I).re := by simpa using hs
  rw [he, eulerFactor_mul_normChar]
  convert hasProd_exp hu₀ hs' using 1
  have hs1 : s + (t : ℂ) * Complex.I ≠ 1 := fun h => by rw [h] at hs'; simp at hs'
  have hs2 := sub_ne_zero.mpr hs1
  beta_reduce
  rw [dslope_of_ne _ hs1, slope_def_field, hZ1 hJ, hZ _ hs',
    GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hX0 hX1 hXm hle _ hs', sub_zero, mul_div_cancel_left₀ _ hs2]
  simp only [hXP, cf]

theorem _root_.GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne := by
  intro K _ _ χ hu
  refine ⟨entire_of_not_normPow hu, fun h1 => ?_⟩
  obtain ⟨Z, hZd, hZ⟩ := GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K
  by_cases hχ : ∃ t : ℝ, IsNormPow χ t
  · obtain ⟨t, ht⟩ := hχ
    rw [isNormPow_iff] at ht
    subst ht
    have ht0 : t ≠ 0 := fun h => h1 (h ▸ normChar_zero)
    have ht1 : (1 : ℂ) + (t : ℂ) * Complex.I - 1 ≠ 0 := by simpa using ht0
    refine ⟨fun s => Z (s + (t : ℂ) * Complex.I) / (s + (t : ℂ) * Complex.I - 1), ⟨?_, fun s hs => ?_⟩,
      div_ne_zero (GlobalTheory.zetaEulerProduct_ne_zero_one_add_mul_I _ _ two_le_N sumN nonemptyN Z hZd hZ t ht0) ht1⟩
    · exact ((hZd.comp (f := fun s : ℂ => s + (t : ℂ) * Complex.I) (by fun_prop)).analyticAt 1).div (by fun_prop) ht1
    · have hs' : 1 < (s + (t : ℂ) * Complex.I).re := by simpa using hs
      have hs1 : s + (t : ℂ) * Complex.I ≠ 1 := fun h => by rw [h] at hs'; simp at hs'
      rw [← one_mul (normChar K t), eulerFactor_mul_normChar]
      convert hasProd_exp (χ := 1) (fun _ => by simp) hs' using 1
      have hc : ∀ P : HeightOneSpectrum (𝓞 K), cf 1 P = 1 := fun P => if_pos fun _ _ => rfl
      simp only [hc]
      rw [hZ _ hs', mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs1)]
  · obtain ⟨Λ, hΛ⟩ := entire_of_not_normPow hu hχ
    exact ⟨Λ, isContAtOne_of_isHeckeL hΛ, GlobalTheory.eulerProduct_ne_zero_one_of_entire _ _ (cf χ) two_le_N (norm_cf hu) sumN
      nonemptyN Z Λ hZd hΛ.1 hZ fun s hs => (hΛ.2 s hs).unique (hasProd_exp hu hs)⟩

end GlobalTheory.HeckeOne
end
