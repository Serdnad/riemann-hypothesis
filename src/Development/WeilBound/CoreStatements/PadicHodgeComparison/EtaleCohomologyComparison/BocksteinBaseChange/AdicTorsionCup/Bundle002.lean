module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TorsOfForall
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace CrystallineSemistableComparison.AdicCoh

section Heq
variable {q : ℕ} {E : Spc}

theorem eq_cast_of_heq {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') {x : Ht q E n' i'} {y : Ht q E n i} (h : HEq x y) :
    x = y.cast h1 h2 := by
  exact eq_of_heq (h.trans (cast_heq h1 h2 y).symm)

theorem heq_zero {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') {x : Ht q E n i} (h : HEq x (0 : Ht q E n' i')) : x = 0 := by
  subst h1 h2
  exact eq_of_heq h

theorem cup_heq {n m i j n' m' i' j' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : m = m') (h4 : j = j')
    {a : Ht q E n i} {a' : Ht q E n' i'} {b : Ht q E m j} {b' : Ht q E m' j'} (ha : HEq a a') (hb : HEq b b') :
    HEq (cup q a b) (cup q a' b') := by
  subst h1 h2 h3 h4
  cases ha
  cases hb
  exact HEq.rfl

end Heq

section Root
variable (q : ℕ) [NeZero q] {E : Spc} (hR : GlobalTheory.EtC.DivisorRingCompatibility) (hinv : Inv q E) {e : ℤ} (u : Ht q E 0 e) (v : Ht q E 0 (-e))
include hR hinv

theorem cup_one_right {n i : ℤ} (b : Ht q E n i) : HEq (cup q b (one q E)) b := by
  obtain ⟨h1, -, h3⟩ := hR q E
  rw [h3 b (one q E), h1 hinv b]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact (cast_heq _ _ _).trans (cast_heq _ _ _)

theorem root_left (hvu : cup q v u = (one q E).cast (by ring) (by ring)) {n i : ℤ} (b : Ht q E n i) :
    HEq (cup q (cup q b v) u) b := by
  obtain ⟨-, h2, -⟩ := hR q E
  rw [h2 b v u, hvu, cup_cast_right]
  exact (cast_heq _ _ _).trans ((cast_heq _ _ _).trans (cup_one_right q hR hinv b))

theorem root_right (hvu : cup q v u = (one q E).cast (by ring) (by ring)) {n i : ℤ} (b : Ht q E n i) :
    HEq (cup q (cup q b u) v) b := by
  obtain ⟨-, h2, h3⟩ := hR q E
  rw [h2 b u v, h3 u v, hvu]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, cast_cast, cup_cast_right]
  exact (cast_heq _ _ _).trans (cup_one_right q hR hinv b)

end Root

section PD
variable {k : Type} [Field k] [IsAlgClosed k] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Spec (CommRingCat.of k)) [IsProper p]
  (d : ℕ) [SmoothOfRelativeDimension d p] (q : ℕ) [NeZero q] (hq : IsUnit (q : k))
include p hq

theorem vanish (hI : ZIn) (n : ℤ) (hn : 2 * (d : ℤ) < n) : Subsingleton (Ht q (sch.obj Y) n 0) := by
  obtain ⟨tr, htr⟩ := hI.e8 q k hq p d
  haveI : Subsingleton (Ht q (sch.obj Y) (2 * d - n) (d - 0)) :=
    (hI.a9 (ZMod q) (tw q ((d : ℤ) - 0))).1 _ _ (by omega)
  obtain ⟨c, -, hc⟩ := htr n 0 0
  refine ⟨fun a b => (hc a fun y => ?_).trans (hc b fun y => ?_).symm⟩ <;>
    simp [Subsingleton.elim y 0, cast_zero]

theorem nondeg (hI : ZIn) (hprim : Nonempty (Prim q Γ(Y, ⊤))) (hinv : Inv q (sch.obj Y)) (i j : ℤ) (hij : i + j = 2 * d)
    (a : Ht q (sch.obj Y) i 0) (h : ∀ b : Ht q (sch.obj Y) j 0, cup q a b = 0) : a = 0 := by
  obtain ⟨tr, htr⟩ := hI.e8 q k hq p d
  obtain ⟨u, v, hvu⟩ := hI.root q Y hprim (d : ℤ)
  have key : ∀ b' : Ht q (sch.obj Y) (2 * d - i) (d - 0), cup q a b' = 0 := by
    intro b'
    have hc := h ((cup q b' v).cast (by omega) (by omega))
    have s1 : cup q a (cup q b' v) = 0 :=
      heq_zero (by omega) (by omega)
        ((cup_heq rfl rfl (by omega) (by omega) HEq.rfl (cast_heq _ _ _).symm).trans (heq_of_eq hc))
    have s3 : cup q (cup q a (cup q b' v)) u = 0 := by rw [s1, map_zero, AddMonoidHom.zero_apply]
    have s4 : HEq (cup q a (cup q (cup q b' v) u)) (cup q (cup q a (cup q b' v)) u) := by
      rw [(hI.ring q _).2.1 a (cup q b' v) u]
      exact (cast_heq _ _ _).symm
    exact heq_zero (by omega) (by omega)
      ((cup_heq rfl rfl (by omega) (by omega) HEq.rfl (root_left q hI.ring hinv u v hvu b').symm).trans
        (s4.trans (heq_of_eq s3)))
  obtain ⟨c, -, hc⟩ := htr i 0 0
  have ha : a = c := hc a (fun b => by simp [key b, cast_zero])
  have h0 : (0 : Ht q (sch.obj Y) i 0) = c := hc 0 (fun b => by simp [cast_zero])
  exact ha.trans h0.symm

theorem top_cyclic (hI : ZIn) (hprim : Nonempty (Prim q Γ(Y, ⊤))) (hinv : Inv q (sch.obj Y)) :
    ∃ g : Ht q (sch.obj Y) (2 * d) 0, ∀ x, ∃ n : ℤ, x = n • g := by
  obtain ⟨tr, -⟩ := hI.e8 q k hq p d
  obtain ⟨u, v, hvu⟩ := hI.root q Y hprim (d : ℤ)
  refine ⟨(cup q (tr.symm 1) v).cast (by ring) (by ring), fun x => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      ((cup q x u).cast (by ring) (by ring) : Ht q (sch.obj Y) (2 * d) d) = m • tr.symm 1 := by
    refine ⟨((tr ((cup q x u).cast (by ring) (by ring))).val : ℤ), tr.injective ?_⟩
    rw [map_zsmul, AddEquiv.apply_symm_apply, zsmul_one, Int.cast_natCast, ZMod.natCast_zmod_val]
  refine ⟨m, ?_⟩
  have hc : cup q (m • tr.symm 1) v = m • cup q (tr.symm 1) v := by
    rw [map_zsmul]
    rfl
  rw [← cast_smul]
  refine eq_cast_of_heq _ _ ?_
  refine (root_right q hI.ring hinv u v hvu x).symm.trans ?_
  rw [← hc, ← hm]
  exact cup_heq (by ring) (by ring) rfl rfl (cast_heq _ _ _).symm HEq.rfl

end PD

end CrystallineSemistableComparison.AdicCoh
end
end

section

set_option backward.isDefEq.respectTransparency false


noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem pow_mono_tors {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (y : N) {m n : ℕ} (h : m ≤ n)
    (hy : (l : ℤ_[l]) ^ m • y = 0) : (l : ℤ_[l]) ^ n • y = 0 := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_smul, hy, smul_zero]

theorem tors_of_tmul {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℚ_[l]) (hc : c ≠ 0) (y : N)
    (h : c ⊗ₜ[ℤ_[l]] y = 0) : ∃ n : ℕ, (l : ℤ_[l]) ^ n • y = 0 := by
  refine (Adic.tmul_eq_zero y).1 ?_
  have e : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y = c⁻¹ • (c ⊗ₜ[ℤ_[l]] y) := by
    rw [smul_tmul', smul_eq_mul, inv_mul_cancel₀ hc]
  rw [e, h, smul_zero]

theorem tmul_zero_of {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℚ_[l]) (y : N) {n : ℕ}
    (h : (l : ℤ_[l]) ^ n • y = 0) : c ⊗ₜ[ℤ_[l]] y = 0 := by
  have h1 : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y = 0 := (Adic.tmul_eq_zero y).2 ⟨_, h⟩
  rw [← mul_one c, ← smul_eq_mul, ← smul_tmul', h1, smul_zero]

theorem unit_geom (M : Model l K) : IsUnit ((l : ℕ) : Γ(GlobalTheory.Et.geom (PadicAlgCl l) M.q, ⊤)) := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact AdicGeo.unit_of_over (AdicGeo.str M) l

theorem fin_levels (hI : ZIn) (M : Model l K) (h : M.Good) (n i : ℤ) (k : ℕ) :
    Finite (Ht (l ^ k) (sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) M.q)) n i) := by
  have := AdicGeo.proper_str h
  have := neZero_pow l k
  have hu : IsUnit ((l ^ k : ℕ) : PadicAlgCl l) := (Nat.cast_ne_zero.2 (NeZero.ne _)).isUnit
  exact hI.e4 (l ^ k) (PadicAlgCl l) hu (AdicGeo.str M) n i

theorem fin_of (hI : ZIn) (M : Model l K) (h : M.Good) (j : ℕ) : FiniteDimensional ℚ_[l] (M.V j) := by
  have hS := isSys l hI _ (unit_geom M) (j : ℤ) 0 (fin_levels hI M h _ _)
  have : Module.Finite ℤ_[l] (Hl l (sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) M.q)) (j : ℤ) 0) :=
    hS.finite (fun _ => Iff.rfl)
  exact Adic.fd

theorem comp_of (hI : ZIn) (G : Model l K → Prop) (hG : ∀ M, G M → M.Good) (hC : CompM G) (M : Model l K) (hM : G M) :
    ∃ (r : ℕ) (P : Fin r → Model l K) (d : Fin r → ℕ) (u : ∀ a, (P a).X ⟶ M.X)
    (hu : ∀ a, u a ≫ M.p = (P a).p), (∀ a, G (P a) ∧ (P a).Conn (d a)) ∧
    ∀ (j : ℕ) (v : M.V j), (∀ a, Model.pullV (u a) (hu a) j v = 0) → v = 0 := by
  obtain ⟨r, P, d, u, hu, hsum, hP⟩ := hC M hM
  refine ⟨r, P, d, u, hu, hP, fun j v hv => ?_⟩
  have hs := AdicGeo.isSum_geom u hu hsum
  obtain ⟨c, x, rfl⟩ := Adic.tmul_surj v
  by_cases hc : c = 0
  · rw [hc, zero_tmul]
  have ht : ∀ a, ∃ n : ℕ, (l : ℤ_[l]) ^ n • pullHl l (sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) (P a).q
      (Model.genMap (u a) (hu a)) (Model.genMap_q (u a) (hu a)))) j 0 x = 0 := fun a =>
    tors_of_tmul c hc _ ((LinearMap.baseChange_tmul _ _ _).symm.trans (hv a))
  choose n hn using ht
  refine tmul_zero_of c x (n := ∑ a, n a) (sum_inj l hI _ hs j 0 _ fun a => ?_)
  refine ((pullHl l _ j 0).map_smul _ x).trans ?_
  exact pow_mono_tors _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)) (hn a)

end CrystallineSemistableComparison.AdicCoh
end
end
