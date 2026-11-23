module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle298
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.LeviPart

section Order

variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

def pos : (Σ a, Fin (d a)) ≃ Fin N := (stdBlocks d hd).trans (wOpen d hd).symm

theorem wOpen_pos (x : Σ a, Fin (d a)) : wOpen d hd (pos d hd x) = stdBlocks d hd x := by
  simp [pos]

theorem wKey_injective : Function.Injective (wKey d hd) := by
  intro x y hxy
  exact congrArg (fun z => (ofLex z).2) hxy

theorem key_strictMono : StrictMono (wKey d hd ∘ wOpen d hd) :=
  (Tuple.monotone_sort (wKey d hd)).strictMono_of_injective
    ((wKey_injective d hd).comp (wOpen d hd).injective)

theorem blk_std (x : Σ a, Fin (d a)) : blk (stdBlocks d hd) (stdBlocks d hd x) = x.1 := by
  simp [blk]

theorem key_lt (x y : Σ a, Fin (d a)) :
    wKey d hd (stdBlocks d hd x) < wKey d hd (stdBlocks d hd y) ↔
      y.1 < x.1 ∨ x.1 = y.1 ∧ stdBlocks d hd x < stdBlocks d hd y := by
  rw [wKey, wKey, Prod.Lex.lt_iff]
  simp [blk_std]

theorem std_lt (a : Fin h) (i j : Fin (d a)) :
    stdBlocks d hd ⟨a, i⟩ < stdBlocks d hd ⟨a, j⟩ ↔ i < j := by
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, Fin.lt_def]
  omega

theorem pos_lt_iff (x y : Σ a, Fin (d a)) :
    pos d hd x < pos d hd y ↔ y.1 < x.1 ∨ x.1 = y.1 ∧ stdBlocks d hd x < stdBlocks d hd y := by
  rw [← (key_strictMono d hd).lt_iff_lt, Function.comp, Function.comp, wOpen_pos, wOpen_pos, key_lt]

theorem pos_lt (a : Fin h) (i j : Fin (d a)) : pos d hd ⟨a, i⟩ < pos d hd ⟨a, j⟩ ↔ i < j := by
  rw [pos_lt_iff, std_lt]
  simp

theorem pos_succ (a : Fin h) (i j : Fin (d a)) (hij : (j : ℕ) = i + 1) :
    (pos d hd ⟨a, j⟩ : ℕ) = pos d hd ⟨a, i⟩ + 1 := by
  have hlt : pos d hd ⟨a, i⟩ < pos d hd ⟨a, j⟩ := (pos_lt d hd a i j).2 (Fin.lt_def.2 (by omega))
  by_contra hne
  have hlt' := Fin.lt_def.1 hlt
  have hN := (pos d hd ⟨a, j⟩).2
  let t : Fin N := ⟨pos d hd ⟨a, i⟩ + 1, by omega⟩
  obtain ⟨⟨b, l⟩, hl⟩ := (pos d hd).surjective t
  have h1 : pos d hd ⟨a, i⟩ < pos d hd ⟨b, l⟩ := by
    rw [hl]; exact Fin.lt_def.2 (by simp [t])
  have h2 : pos d hd ⟨b, l⟩ < pos d hd ⟨a, j⟩ := by
    rw [hl]; exact Fin.lt_def.2 (by simp only [t]; omega)
  rw [pos_lt_iff] at h1 h2
  have hab : a = b := by
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd h1 (lt_asymm h2)
      · exact absurd h2.1 (ne_of_lt h1)
    · exact h1.1
  subst hab
  have h3 := (std_lt d hd a i l).1 (h1.elim (fun e => absurd e (lt_irrefl _)) (·.2))
  have h4 := (std_lt d hd a l j).1 (h2.elim (fun e => absurd e (lt_irrefl _)) (·.2))
  have := Fin.lt_def.1 h3
  have := Fin.lt_def.1 h4
  omega

theorem pos_succ' (a : Fin h) (i j : Fin (d a)) (hij : (pos d hd ⟨a, j⟩ : ℕ) = pos d hd ⟨a, i⟩ + 1) :
    (j : ℕ) = i + 1 := by
  have hlt : i < j := (pos_lt d hd a i j).1 (Fin.lt_def.2 (by omega))
  by_contra hne
  have hlt' := Fin.lt_def.1 hlt
  have hj := j.2
  let l : Fin (d a) := ⟨i + 1, by omega⟩
  have h1 := Fin.lt_def.1 ((pos_lt d hd a i l).2 (Fin.lt_def.2 (by simp [l])))
  have h2 := Fin.lt_def.1 ((pos_lt d hd a l j).2 (Fin.lt_def.2 (by simp only [l]; omega)))
  omega

theorem sum_superdiag {R : Type} [AddCommMonoid R] (A : Fin N → Fin N → R)
    (hA : ∀ x y : Σ a, Fin (d a), x.1 ≠ y.1 → A (pos d hd x) (pos d hd y) = 0) :
    ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, A p.1 p.2 =
      ∑ b, ∑ p : Fin (d b) × Fin (d b) with (p.2 : ℕ) = p.1 + 1, A (pos d hd ⟨b, p.1⟩) (pos d hd ⟨b, p.2⟩) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => (pos d hd ⟨x.1, x.2.1⟩, pos d hd ⟨x.1, x.2.2⟩)) ?_ ?_ ?_ ?_
  · rintro ⟨b, i, j⟩ hx -
    have hx' : (j : ℕ) = i + 1 := by simpa using hx
    simpa using pos_succ d hd b i j hx'
  · rintro ⟨b, i, j⟩ - - ⟨c, i', j'⟩ - - hxy
    have h1 := (pos d hd).injective (Prod.ext_iff.1 hxy).1
    have h2 := (pos d hd).injective (Prod.ext_iff.1 hxy).2
    simp only [Sigma.mk.injEq] at h1 h2
    obtain ⟨rfl, h1⟩ := h1
    obtain ⟨-, h2⟩ := h2
    obtain rfl := eq_of_heq h1
    obtain rfl := eq_of_heq h2
    rfl
  · rintro ⟨p, q⟩ hpq hne
    have hpq' : (q : ℕ) = p + 1 := by simpa using hpq
    obtain ⟨⟨b, i⟩, rfl⟩ := (pos d hd).surjective p
    obtain ⟨⟨c, j⟩, rfl⟩ := (pos d hd).surjective q
    have hbc : b = c := by
      by_contra hbc
      exact hne (hA _ _ hbc)
    subst hbc
    refine ⟨⟨b, i, j⟩, ?_, hne, rfl⟩
    simpa using pos_succ' d hd b i j hpq'
  · intro x _ _
    rfl

end Order

section Entries

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

theorem conj_apply (w : Equiv.Perm (Fin N)) (A : GL (Fin N) k) (p q : Fin N) :
    ((pm k w * A * (pm k w)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (w p) (w q) =
      (A : Matrix (Fin N) (Fin N) k) p q := by
  rw [← map_inv, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply, Units.val_mul,
    GroundTheory.Automorphic.permGL_mul_apply]
  simp

variable {d hd}
variable {A : GL (Fin N) k} {m : Levi k fun a => Fin (d a)}

theorem ent_same (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m)
    (b : Fin h) (i j : Fin (d b)) :
    (m b : Matrix (Fin (d b)) (Fin (d b)) k) i j =
      (A : Matrix (Fin N) (Fin N) k) (pos d hd ⟨b, i⟩) (pos d hd ⟨b, j⟩) := by
  rw [← leviEmb_apply_same k (stdBlocks d hd) m b i j, ← hm, ← wOpen_pos d hd, ← wOpen_pos d hd, conj_apply]

theorem ent_ne (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m)
    (x y : Σ a, Fin (d a)) (hxy : x.1 ≠ y.1) :
    (A : Matrix (Fin N) (Fin N) k) (pos d hd x) (pos d hd y) = 0 := by
  obtain ⟨b, i⟩ := x
  obtain ⟨c, j⟩ := y
  rw [← conj_apply (wOpen d hd) A, wOpen_pos, wOpen_pos, hm]
  exact leviEmb_apply_ne k (stdBlocks d hd) m hxy i j

theorem mem_unipM_of (hA : A ∈ unipB k (Fin N))
    (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m) :
    m ∈ unipM k d := by
  obtain ⟨h1, h2⟩ := (mem_unipB k).1 hA
  refine fun b _ => (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [ent_same hm]
    exact h1 _ _ ((pos_lt d hd b j i).2 hij)
  · rw [ent_same hm]
    exact h2 _

theorem addChar_sum {ι : Type} (ψ : AddChar k Circle) (s : Finset ι) (f : ι → k) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem whit_eq (ψ : AddChar k Circle) (hA : A ∈ unipB k (Fin N)) (hm' : m ∈ unipM k d)
    (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m) :
    whitChar ψ N ⟨A, hA⟩ = whitM d ψ ⟨m, hm'⟩ := by
  show Circle.toUnits (ψ _) = ∏ a : Fin h, Circle.toUnits (ψ _)
  rw [← map_prod, ← addChar_sum]
  refine congrArg _ (congrArg _ ?_)
  refine (sum_superdiag d hd (fun p q => (A : Matrix (Fin N) (Fin N) k) p q) (ent_ne hm)).trans ?_
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun p _ => (ent_same hm b p.1 p.2).symm

theorem mem_unipB_of (hm' : m ∈ unipM k d)
    (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m) :
    A ∈ unipB k (Fin N) := by
  refine (mem_unipB k).2 ⟨fun p q hpq => ?_, fun p => ?_⟩
  · obtain ⟨⟨b, i⟩, rfl⟩ := (pos d hd).surjective p
    obtain ⟨⟨c, j⟩, rfl⟩ := (pos d hd).surjective q
    by_cases hbc : b = c
    · subst hbc
      rw [← ent_same hm]
      exact ((mem_unipB k).1 (hm' b (Set.mem_univ b))).1 i j ((pos_lt d hd b j i).1 hpq)
    · exact ent_ne hm _ _ hbc
  · obtain ⟨⟨b, i⟩, rfl⟩ := (pos d hd).surjective p
    rw [← ent_same hm]
    exact ((mem_unipB k).1 (hm' b (Set.mem_univ b))).2 i

end Entries

theorem levi_part : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (hb : a ∈ unipB k (Fin N)), ∃ m : unipM k d, pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 ∧ whitChar ψ N ⟨a, hb⟩ = whitM d ψ m) ∧ ∀ m : unipM k d, ∃ a ∈ unipL k d hd, pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 := by
  intro k _ _ _ _ ψ h N d hd
  refine ⟨fun a ha hb => ?_, fun m => ?_⟩
  · obtain ⟨m₀, hm₀⟩ := MonoidHom.mem_range.mp ((OpenFactor.mem_unipL k d hd).mp ha).2
    have hm : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m₀ := hm₀.symm
    have hm' := mem_unipM_of hb hm
    exact ⟨⟨m₀, hm'⟩, hm, whit_eq ψ hb hm' hm⟩
  · have hc : pm k (wOpen d hd) * ((pm k (wOpen d hd))⁻¹ * leviEmb k (stdBlocks d hd) m.1 * pm k (wOpen d hd)) *
        (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 := by group
    exact ⟨_, (OpenFactor.mem_unipL k d hd).mpr
      ⟨mem_unipB_of m.2 hc, MonoidHom.mem_range.mpr ⟨m.1, hc.symm⟩⟩, hc⟩

end GlobalTheory.CompanionTheory.Rodier.LeviPart
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Rodier.OpenFactor

theorem conj_perm_entry {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (g : GL (Fin N) k) (p q : Fin N) :
    ((GroundTheory.Automorphic.permGL k w * g * (GroundTheory.Automorphic.permGL k w)⁻¹ : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) (w p) (w q) = (g : Matrix (Fin N) (Fin N) k) p q := by
  rw [← map_inv]
  change ((w⁻¹).permMatrix k * (g : Matrix (Fin N) (Fin N) k) * (w⁻¹⁻¹).permMatrix k) (w p) (w q) = _
  simp [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem lt_of_blk_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {p q : Fin N}
    (hb : blk (stdBlocks d hd) (wOpen d hd p) < blk (stdBlocks d hd) (wOpen d hd q)) : q < p := by
  by_contra hqp
  have hm := Tuple.monotone_sort (wKey d hd) (not_lt.mp hqp)
  change wKey d hd (wOpen d hd p) ≤ wKey d hd (wOpen d hd q) at hm
  unfold wKey at hm
  rw [Prod.Lex.le_iff] at hm
  simp only [ofLex_toLex] at hm
  rcases hm with hlt | ⟨heq, _⟩
  · exact lt_asymm hb (OrderDual.toDual_lt_toDual.mp hlt)
  · rw [OrderDual.toDual_inj] at heq
    rw [heq] at hb
    exact lt_irrefl _ hb

variable (k : Type) [Field k]
variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

theorem mem_unipU {u : GL (Fin N) k} : u ∈ unipU k d hd ↔
    u ∈ unipB k (Fin N) ∧ pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ unipRadLower k (stdBlocks d hd) := by
  exact Iff.rfl

theorem conj_mem_parabLower {n : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) :
    pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹ ∈ parabLower k (stdBlocks d hd) := by
  rw [GlobalTheory.SmGL.mem_parabLower_iff k]
  intro a b i j hab
  obtain ⟨p, hp⟩ := (wOpen d hd).surjective (stdBlocks d hd ⟨a, i⟩)
  obtain ⟨q, hq⟩ := (wOpen d hd).surjective (stdBlocks d hd ⟨b, j⟩)
  rw [← hp, ← hq]
  unfold pm
  rw [conj_perm_entry]
  apply ((GlobalTheory.SmGL.mem_unipB k).mp hn).1
  apply lt_of_blk_lt d hd
  rw [hp, hq, GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
  exact hab

theorem exists_mul {n : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) :
    ∃ a ∈ unipL k d hd, ∃ u ∈ unipU k d hd, n = a * u := by
  have hc0 := conj_mem_parabLower k d hd hn
  set P := pm k (wOpen d hd) with hP
  set e := stdBlocks d hd with he
  have hc : P * n * P⁻¹ ∈ parab k (opp e) := hc0
  obtain ⟨v, hv, hcv⟩ := exists_levi_mul_unip k (opp e) ⟨P * n * P⁻¹, hc⟩
  set L := leviEmb k (opp e) (leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩) with hL
  have hcv' : P * n * P⁻¹ = L * v := hcv
  have hLentry : ∀ p q : Fin N, ((P⁻¹ * L * P : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p q =
      if blk e (wOpen d hd p) = blk e (wOpen d hd q) then (n : Matrix (Fin N) (Fin N) k) p q else 0 := by
    intro p q
    have h1 := conj_perm_entry (wOpen d hd) (P⁻¹ * L * P) p q
    simp only [show GroundTheory.Automorphic.permGL k (wOpen d hd) = P from rfl] at h1
    rw [show P * (P⁻¹ * L * P) * P⁻¹ = L by group] at h1
    rw [← h1]
    obtain ⟨⟨x, i⟩, hxi⟩ := e.surjective (wOpen d hd p)
    obtain ⟨⟨y, j⟩, hyj⟩ := e.surjective (wOpen d hd q)
    rw [← hxi, ← hyj, GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
    split_ifs with hxy
    · subst hxy
      refine (GlobalTheory.SmGL.leviEmb_apply_same k (opp e) (leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩) x i j).trans ?_
      refine (GlobalTheory.SmGL.leviProj_apply k (opp e) ⟨P * n * P⁻¹, hc⟩ x i j).trans ?_
      change ((P * n * P⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨x, i⟩) (e ⟨x, j⟩) = _
      rw [hxi, hyj]
      exact conj_perm_entry (wOpen d hd) n p q
    · exact GlobalTheory.SmGL.leviEmb_apply_ne k (opp e) _ hxy i j
  have haB : P⁻¹ * L * P ∈ unipB k (Fin N) := by
    rw [GlobalTheory.SmGL.mem_unipB k]
    refine ⟨fun p q hqp => ?_, fun p => ?_⟩
    · rw [hLentry]
      split_ifs
      · exact ((GlobalTheory.SmGL.mem_unipB k).mp hn).1 p q hqp
      · rfl
    · rw [hLentry, ite_eq_left rfl]
      exact ((GlobalTheory.SmGL.mem_unipB k).mp hn).2 p
  refine ⟨P⁻¹ * L * P, ?_, P⁻¹ * v * P, ?_, ?_⟩
  · change P⁻¹ * L * P ∈ unipB k (Fin N) ∧
      P * (P⁻¹ * L * P) * P⁻¹ ∈ (leviEmb k e).range
    refine ⟨haB, ?_⟩
    show P * (P⁻¹ * L * P) * P⁻¹ ∈ (leviEmb k e).range
    rw [show P * (P⁻¹ * L * P) * P⁻¹ = L by group]
    exact ⟨leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩, rfl⟩
  · rw [mem_unipU k d hd]
    refine ⟨?_, ?_⟩
    · have hv' : v = L⁻¹ * (P * n * P⁻¹) := by
        rw [hcv']
        group
      rw [show P⁻¹ * v * P = (P⁻¹ * L * P)⁻¹ * n by rw [hv']; group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haB) hn
    · show P * (P⁻¹ * v * P) * P⁻¹ ∈ unipRadLower k e
      rw [show P * (P⁻¹ * v * P) * P⁻¹ = v by group]
      exact hv
  · rw [show P⁻¹ * L * P * (P⁻¹ * v * P) = P⁻¹ * (L * v) * P by group, ← hcv']
    group

theorem conj_mem_unipU {n u : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) (hu : u ∈ unipU k d hd) :
    n * u * n⁻¹ ∈ unipU k d hd := by
  rw [mem_unipU k d hd] at hu ⊢
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hu.1) (Subgroup.inv_mem _ hn), ?_⟩
  have hN := GlobalTheory.SmGL.parab_le_normalizer k (GlobalTheory.SmGL.opp (stdBlocks d hd)) (conj_mem_parabLower k d hd hn)
  have key : pm k (wOpen d hd) * (n * u * n⁻¹) * (pm k (wOpen d hd))⁻¹ =
      (pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹) * (pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹) *
        (pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹)⁻¹ := by group
  rw [key]
  exact (Subgroup.mem_normalizer_iff.mp hN _).mp hu.2

end GlobalTheory.CompanionTheory.Rodier.OpenFactor

theorem GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ n ∈ unipB k (Fin N), ∃ a ∈ unipL k d hd, ∃ u ∈ unipU k d hd, n = a * u) ∧ ∀ n ∈ unipB k (Fin N), ∀ u ∈ unipU k d hd, n * u * n⁻¹ ∈ unipU k d hd := by
  intro k _ _ _ _ h N d hd
  exact ⟨fun n hn => GlobalTheory.CompanionTheory.Rodier.OpenFactor.exists_mul k d hd hn,
    fun n hn u hu => GlobalTheory.CompanionTheory.Rodier.OpenFactor.conj_mem_unipU k d hd hn hu⟩

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Rodier.RootElt

def elemGL {k : Type} [Field k] {N : ℕ} (i j : Fin N) (hij : i ≠ j) (t : k) : GL (Fin N) k where
  val := Matrix.transvection i j t
  inv := Matrix.transvection i j (-t)
  val_inv := by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp
  inv_val := by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp

theorem elemGL_apply {k : Type} [Field k] {N : ℕ} (i j : Fin N) (hij : i ≠ j) (t : k) (a b : Fin N) :
    (elemGL i j hij t).val a b = (1 : Matrix (Fin N) (Fin N) k) a b + if a = i ∧ b = j then t else 0 := by
  show Matrix.transvection i j t a b = _
  rw [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
  congr 1
  by_cases h : a = i ∧ b = j
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
  · rw [if_neg h, if_neg fun e => h ⟨e.1.symm, e.2.symm⟩]

theorem conj_pm_apply {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (g : GL (Fin N) k) (a b : Fin N) :
    (GroundTheory.Automorphic.permGL k w * g * (GroundTheory.Automorphic.permGL k w)⁻¹).val a b = g.val (w⁻¹ a) (w⁻¹ b) := by
  rw [← map_inv, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply, Units.val_mul,
    GroundTheory.Automorphic.permGL_mul_apply]

theorem exists_root_conj_mem_unipRad : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (w : Equiv.Perm (Fin N)) (i j : Fin N), (j : ℕ) = i + 1 → blk (stdBlocks d hd) (w i) < blk (stdBlocks d hd) (w j) → ∀ t : k, ∃ (u : GL (Fin N) k) (hu : u ∈ unipB k (Fin N)), whitChar ψ N ⟨u, hu⟩ = Circle.toUnits (ψ t) ∧ pm k w * u * (pm k w)⁻¹ ∈ unipRad k (stdBlocks d hd) := by
  intro k _ _ _ _ ψ h N d hd w i j hij hb t
  have hne : i ≠ j := fun e => by rw [e] at hij; omega
  have hlt : i < j := Fin.lt_def.2 (by omega)
  have hu : elemGL i j hne t ∈ unipB k (Fin N) := by
    refine (mem_unipB k).2 ⟨fun a b hba => ?_, fun a => ?_⟩
    · rw [elemGL_apply, Matrix.one_apply_ne hba.ne', if_neg fun e => ?_, add_zero]
      rw [e.1, e.2] at hba
      exact absurd hba hlt.not_gt
    · rw [elemGL_apply, Matrix.one_apply_eq, if_neg fun e => hne (e.1.symm.trans e.2), add_zero]
  refine ⟨elemGL i j hne t, hu, ?_, ?_⟩
  · show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, (elemGL i j hne t).val p.1 p.2)) = _
    congr 2
    rw [Finset.sum_eq_single_of_mem (i, j) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩)]
    · rw [elemGL_apply, Matrix.one_apply_ne hne, if_pos ⟨rfl, rfl⟩, zero_add]
    · rintro ⟨a, b⟩ hp hpne
      have hab : (b : ℕ) = a + 1 := (Finset.mem_filter.1 hp).2
      have hne' : a ≠ b := fun e => by rw [e] at hab; omega
      rw [elemGL_apply, Matrix.one_apply_ne hne', if_neg fun e => hpne (Prod.ext e.1 e.2), add_zero]
  · have hent : ∀ a b : Fin N, (pm k w * elemGL i j hne t * (pm k w)⁻¹).val a b =
        (1 : Matrix (Fin N) (Fin N) k) a b + if a = w i ∧ b = w j then t else 0 := by
      intro a b
      rw [conj_pm_apply, elemGL_apply]
      congr 1
      · by_cases e : a = b
        · rw [e, Matrix.one_apply_eq, Matrix.one_apply_eq]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne fun e' => e (w⁻¹.injective e')]
      · simp only [Equiv.Perm.inv_eq_iff_eq]
    refine mem_unipRad.2 ⟨mem_parab.2 fun a b hab => ?_, fun c x y => ?_⟩
    · have hne' : a ≠ b := fun e => by rw [e] at hab; exact lt_irrefl _ hab
      rw [hent, Matrix.one_apply_ne hne', if_neg fun e => ?_, add_zero]
      rw [e.1, e.2] at hab
      exact lt_asymm hab hb
    · rw [hent, if_neg fun e => ?_, add_zero]
      · by_cases e : x = y
        · rw [e, Matrix.one_apply_eq, Matrix.one_apply_eq]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne fun e' => e (by simpa using (stdBlocks d hd).injective e')]
      · have h1 := blk_apply (stdBlocks d hd) c x
        have h2 := blk_apply (stdBlocks d hd) c y
        rw [e.1] at h1
        rw [e.2] at h2
        rw [h1, h2] at hb
        exact lt_irrefl _ hb

end GlobalTheory.CompanionTheory.Rodier.RootElt
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZNuPair

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {X : Type} [AddCommGroup X] [Module ℂ X]

def whitImg (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    (T : Subrepresentation J) : Subrepresentation (whit2 ψ d J) :=
  ⟨T.toSubmodule.map (whitKer ψ d J).mkQ, fun g v hv => by
    obtain ⟨t, ht, rfl⟩ := hv
    exact ⟨J (firstEmb d g) t, T.apply_mem_toSubmodule _ ht, rfl⟩⟩

theorem whitImg_mono (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    {T T' : Subrepresentation J} (h : T' ≤ T) : whitImg ψ d J T' ≤ whitImg ψ d J T :=
  Submodule.map_mono (f := (whitKer ψ d J).mkQ) h

end

end GlobalTheory.CompanionTheory.BZNuPair

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.exists_divided_powers_on_reductions : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∃ δ : DividedPowers (A.Fil n 1), R.IsPd (A.mkAcr n) (A.Fil0 1) δ) ∧ ∃ δ : DividedPowers (A.PFil n), R.IsPd (A.mkAcr n) A.PFil0 δ := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.exists_dividedPowers_fil_pfil | exact GlobalTheory.CompanionTheory.PerfFil.exists_dividedPowers_fil_pfil | (intros; apply GlobalTheory.CompanionTheory.PerfFil.exists_dividedPowers_fil_pfil <;> assumption)
end
