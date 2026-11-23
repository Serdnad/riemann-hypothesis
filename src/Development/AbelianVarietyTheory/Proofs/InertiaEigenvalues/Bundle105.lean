module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CloseVectorNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Formalism.CharacterColumnKernels.Bundle001
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle072
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle023
public import Mathlib.Basic.Real.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle071
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section
namespace GlobalTheory.PhiGam.QuotShift
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

section lin
variable {k U : Type} [Field k] [AddCommGroup U] [Module k U]

theorem mem_iSup_comap_pow (S : Module.End k U) (Q : Submodule k U) (hQ : ∀ q ∈ Q, S q ∈ Q) (p : U) :
    p ∈ ⨆ m : ℕ, Q.comap (S ^ m) ↔ ∃ m : ℕ, (S ^ m) p ∈ Q := by
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m y hy => ?_
    rw [Submodule.mem_comap, pow_succ', Module.End.mul_apply]
    exact hQ _ hy
  rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
  rfl

theorem gmult_transport (T T' : Module.End k U) (e : U ≃ₗ[k] U) (P Q P' Q' : Submodule k U)
    (hP' : ∀ p, e p ∈ P' ↔ p ∈ P) (hQ' : ∀ p, e p ∈ Q' ↔ p ∈ Q)
    (hTP : ∀ p ∈ P, T p ∈ P) (hTQ : ∀ p ∈ Q, T p ∈ Q) (hTQ' : ∀ p ∈ Q', T' p ∈ Q') (x y : k)
    (h : ∀ p ∈ P, (T' (e p) - x • e p) - e (T p - y • p) ∈ Q') :
    gmult T' P' Q' x = gmult T P Q y := by
  set S := T - algebraMap k (Module.End k U) y with hS
  set S' := T' - algebraMap k (Module.End k U) x with hS'
  have hSa : ∀ p, S p = T p - y • p := fun p => by simp [hS, Module.algebraMap_end_apply]
  have hSa' : ∀ p, S' p = T' p - x • p := fun p => by simp [hS', Module.algebraMap_end_apply]
  have hSP : ∀ p ∈ P, S p ∈ P := fun p hp => by rw [hSa]; exact P.sub_mem (hTP p hp) (P.smul_mem _ hp)
  have hSQ : ∀ p ∈ Q, S p ∈ Q := fun p hp => by rw [hSa]; exact Q.sub_mem (hTQ p hp) (Q.smul_mem _ hp)
  have hSQ' : ∀ p ∈ Q', S' p ∈ Q' := fun p hp => by
    rw [hSa']; exact Q'.sub_mem (hTQ' p hp) (Q'.smul_mem _ hp)
  have key : ∀ p ∈ P, ∀ m : ℕ, (S ^ m) p ∈ P ∧ (S' ^ m) (e p) - e ((S ^ m) p) ∈ Q' := by
    intro p hp m
    induction m with
    | zero => simpa using hp
    | succ m ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      refine ⟨hSP _ ih.1, ?_⟩
      have h1 := hSQ' _ ih.2
      have h2 := h _ ih.1
      rw [← hSa, ← hSa'] at h2
      have h3 := Q'.add_mem h1 h2
      rwa [map_sub, sub_add_sub_cancel] at h3
  have hmem : ∀ p, e p ∈ (P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m)) ↔ p ∈ (P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)) := by
    intro p
    rw [Submodule.mem_inf, Submodule.mem_inf, mem_iSup_comap_pow S Q hSQ, mem_iSup_comap_pow S' Q' hSQ', hP']
    refine and_congr_right fun hp => exists_congr fun m => ?_
    rw [← hQ']
    have := (key p hp m).2
    constructor
    · intro h1; simpa using Q'.sub_mem h1 this
    · intro h1; simpa using Q'.add_mem this h1
  unfold gmult
  rw [← hS, ← hS']
  set A := P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)
  set A' := P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m)
  have hA : A.map (e : U →ₗ[k] U) = A' := by
    ext z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [hmem]
    exact Submodule.map_equiv_eq_comap_symm e A ▸ by simp
  let e' : A ≃ₗ[k] A' := e.ofSubmodules A A' hA
  refine (Submodule.Quotient.equiv (Q.submoduleOf A) (Q'.submoduleOf A') e' ?_).finrank_eq.symm
  ext z
  obtain ⟨w, rfl⟩ := e'.surjective z
  have : (e' w ∈ Q'.submoduleOf A') ↔ w ∈ Q.submoduleOf A := hQ' w
  rw [this]
  exact Submodule.map_equiv_eq_comap_symm e' _ ▸ by simp

theorem fin_of_le {A B C : Submodule k U} (h : C ≤ B) (hf : FiniteDimensional k (A.map C.mkQ)) :
    FiniteDimensional k (A.map B.mkQ) := by
  have : A.map B.mkQ = (A.map C.mkQ).map (Submodule.factor h) := by
    rw [← Submodule.map_comp]; rfl
  rw [this]; infer_instance

theorem fin_trans {A B C : Submodule k U} (h : C ≤ B) (h1 : FiniteDimensional k (A.map B.mkQ))
    (h2 : FiniteDimensional k (B.map C.mkQ)) : FiniteDimensional k (A.map C.mkQ) := by
  have e : A.map B.mkQ = (A.map C.mkQ).map (Submodule.factor h) := by
    rw [← Submodule.map_comp]; rfl
  rw [e] at h1
  have hle : A.map C.mkQ ⊓ LinearMap.ker (Submodule.factor h) ≤ B.map C.mkQ := by
    rintro _ ⟨⟨a, -, rfl⟩, ha⟩
    exact ⟨a, (Submodule.Quotient.mk_eq_zero B).1 ha, rfl⟩
  have h3 := Submodule.finiteDimensional_of_le hle
  exact Module.Finite.iff_fg.2 (Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.factor h)
    (Module.Finite.iff_fg.1 h1) (Module.Finite.iff_fg.1 h3))

theorem fin_quot {A B : Submodule k U} (h : FiniteDimensional k (A.map B.mkQ)) :
    FiniteDimensional k (↥A ⧸ B.submoduleOf A) := by
  have e := LinearMap.quotKerEquivRange (B.mkQ.domRestrict A)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at e
  exact e.symm.finiteDimensional

theorem gmult_self (T : Module.End k U) (P : Submodule k U) (x : k) : gmult T P P x = 0 := by
  unfold gmult
  rw [Submodule.submoduleOf_eq_top.2 inf_le_left]
  exact Module.finrank_zero_of_subsingleton

end lin

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
theorem sh_sup_le {P Q : Submodule k⟦X⟧ V} {m : ℕ} (h : sh ((m + 1 : ℕ) : ℤ) P ≤ Q) :
    sh (m : ℤ) (Q ⊔ sh 1 P) ≤ Q := by
  have : sh (m : ℤ) (Q ⊔ sh 1 P) = sh (m : ℤ) Q ⊔ sh (m : ℤ) (sh 1 P) := Submodule.map_sup _ _ _
  rw [this, sh_sh_eq]
  refine sup_le ?_ (by exact_mod_cast h)
  simpa [sh_zero_eq] using sh_le_sh_of_le (Int.natCast_nonneg m) Q

omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
theorem sh_one_le (P : Submodule k⟦X⟧ V) : sh 1 P ≤ P := by
  simpa [sh_zero_eq] using sh_le_sh_of_le (zero_le_one' ℤ) P

theorem fin_lat (m : ℕ) : ∀ P Q : Submodule k⟦X⟧ V, P.FG → Q.FG → sh (m : ℤ) P ≤ Q →
    FiniteDimensional k ((P.restrictScalars k).map (Q.restrictScalars k).mkQ) := by
  induction m with
  | zero =>
    intro P Q _ _ h
    have : (P.restrictScalars k).map (Q.restrictScalars k).mkQ = ⊥ := by
      rw [← le_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]
      rw [Nat.cast_zero, sh_zero_eq] at h
      exact h
    rw [this]; infer_instance
  | succ m ih =>
    intro P Q hP hQ h
    refine fin_trans (B := (Q ⊔ sh 1 P).restrictScalars k) (fun y hy => Submodule.mem_sup_left hy) ?_
      (ih _ _ (hQ.sup (hP.map _)) hQ (sh_sup_le h))
    exact fin_of_le (fun y hy => Submodule.mem_sup_right hy) (Window.finite_quot hP)

theorem step {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {P Q : Submodule k⟦X⟧ V}
    (hP : CondC g P) (hQ : CondC g Q) (h : sh 1 P ≤ Q) (x : k) :
    qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  have hv := vv_ne_zero k
  let e : V ≃ₗ[k] V := (LinearEquiv.smulOfNeZero k⸨X⸩ V (vv k) hv).restrictScalars k
  have he : ∀ p, e p = vv k • p := fun p => rfl
  have hN : ∀ (N : Submodule k⟦X⟧ V) p, e p ∈ (sh 1 N).restrictScalars k ↔ p ∈ N.restrictScalars k := by
    intro N p
    rw [Submodule.restrictScalars_mem, Submodule.restrictScalars_mem, mem_sh_iff_smul_mem, he, smul_smul,
      zpow_neg_one, inv_mul_cancel₀ hv, one_smul]
  refine gmult_transport _ _ e _ _ _ _ (hN P) (hN Q) (fun p hp => Window.nab_mem hP hp)
    (fun p hp => Window.nab_mem hQ hp) (fun p hp => Window.nab_mem_sh R hg hQ 1 hp) _ _ fun p hp => ?_
  obtain ⟨n', hn', hs⟩ := Window.nab_shift R hg hP 1 hp
  rw [zpow_one, ← he, ← he] at hs
  rw [hs, ← map_smul, ← map_sub, ← map_sub, hN]
  have : nab g p - ((1 : ℤ) : k) • p + vv k • n' - x • p - (nab g p - (x + 1) • p) = vv k • n' := by
    rw [Int.cast_one, add_smul]; abel
  rw [this]
  exact h (mem_sh_iff_exists.2 ⟨n', hn', by rw [zpow_one]⟩)

theorem qmult_add (g : V →ₗ[k] V) (m : ℕ) {P Q S : Submodule k⟦X⟧ V} (hP : P.FG) (hS : S.FG) (h1 : S ≤ Q)
    (h2 : Q ≤ P) (cP : ∀ p ∈ P, nab g p ∈ P) (cQ : ∀ p ∈ Q, nab g p ∈ Q) (cS : ∀ p ∈ S, nab g p ∈ S)
    (h : sh (m : ℤ) P ≤ S) (x : k) : qmult g P S x = qmult g P Q x + qmult g Q S x :=
  GmultAdd.main (nab g) (P.restrictScalars k) (Q.restrictScalars k) (S.restrictScalars k) h1 h2 cP cQ cS
    (fin_quot (fin_lat m P S hP hS h)) x

theorem shift_of_le {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) (x : k) (m : ℕ) :
    ∀ P Q : Submodule k⟦X⟧ V, P.FG → Q.FG → Q ≤ P → CondC g P → CondC g Q → sh (m : ℤ) P ≤ Q →
      qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  induction m with
  | zero =>
    intro P Q _ _ hle _ _ h
    rw [Nat.cast_zero, sh_zero_eq] at h
    rw [le_antisymm hle h, qmult, qmult, gmult_self, gmult_self]
  | succ m ih =>
    intro P Q hP hQ hle cP cQ h
    have hle' : Q ⊔ sh 1 P ≤ P := sup_le hle (sh_one_le P)
    have cQ' : CondC g (Q ⊔ sh 1 P) := by
      rw [condC_iff_nab_mem]
      intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (Window.nab_mem cQ ha) (Window.nab_mem_sh R hg cP 1 hb)
    have h' : sh ((m + 1 : ℕ) : ℤ) (sh 1 P) ≤ sh 1 Q := by
      rw [sh_sh_eq, add_comm, ← sh_sh_eq]; exact sh_le_sh 1 h
    have a1 := qmult_add g (m + 1) hP hQ (le_sup_left (b := sh 1 P)) hle' (fun p hp => Window.nab_mem cP hp)
      (fun p hp => Window.nab_mem cQ' hp) (fun p hp => Window.nab_mem cQ hp) h (x + 1)
    have a2 := qmult_add g (m + 1) (P := sh 1 P) (Q := sh 1 (Q ⊔ sh 1 P)) (S := sh 1 Q) (hP.map _) (hQ.map _)
      (sh_le_sh 1 le_sup_left) (sh_le_sh 1 hle') (fun p hp => Window.nab_mem_sh R hg cP 1 hp)
      (fun p hp => Window.nab_mem_sh R hg cQ' 1 hp) (fun p hp => Window.nab_mem_sh R hg cQ 1 hp) h' x
    rw [a1, a2, step R hg cP cQ' le_sup_right,
      ih (Q ⊔ sh 1 P) Q (hQ.sup (hP.map _)) hQ le_sup_left cQ' cQ (sh_sup_le h)]

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ x : k, qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg P Q hP hQ hle cP cQ x
  obtain ⟨m, hm⟩ := Close.exists_pow hP.1 hQ.2
  exact shift_of_le R hg x m P Q hP.1 hQ.1 hle cP cQ (Close.sh_le hm)

end GlobalTheory.PhiGam.QuotShift
end
end

section

noncomputable section
namespace GlobalTheory.PhiGam.Compare
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem inj_iff_surj {k U : Type} [Field k] [AddCommGroup U] [Module k U] (S : Module.End k U)
    (P Q : Submodule k U) (hP : ∀ p ∈ P, S p ∈ P) (hQ : ∀ p ∈ Q, S p ∈ Q)
    [hfin : FiniteDimensional k (P.map Q.mkQ)] :
    (∀ p ∈ P, S p ∈ Q → p ∈ Q) ↔ ∀ y ∈ P, ∃ p ∈ P, y - S p ∈ Q := by
  have hSQ : Q ≤ Q.comap S := fun p hp => hQ p hp
  let Sq := Q.mapQ Q S hSQ
  have hSq : ∀ z ∈ P.map Q.mkQ, Sq z ∈ P.map Q.mkQ := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨S p, hP p hp, rfl⟩
  constructor
  · intro hinj
    have hi : Function.Injective (Sq.restrict hSq) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨_, p, hp, rfl⟩ hz
      have h1 : Q.mkQ (S p) = 0 := congrArg Subtype.val hz
      have h2 : p ∈ Q := hinj p hp ((Submodule.Quotient.mk_eq_zero _).mp h1)
      exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h2)
    have hs := LinearMap.injective_iff_surjective.mp hi
    intro y hy
    obtain ⟨⟨_, p, hp, rfl⟩, hz⟩ := hs ⟨Q.mkQ y, y, hy, rfl⟩
    have h1 : Q.mkQ (S p) = Q.mkQ y := congrArg Subtype.val hz
    exact ⟨p, hp, (Submodule.Quotient.eq _).mp h1.symm⟩
  · intro hsur
    have hs : Function.Surjective (Sq.restrict hSq) := by
      rintro ⟨_, y, hy, rfl⟩
      obtain ⟨p, hp, h⟩ := hsur y hy
      refine ⟨⟨Q.mkQ p, p, hp, rfl⟩, Subtype.ext ?_⟩
      exact ((Submodule.Quotient.eq _).mpr h).symm
    have hi := LinearMap.injective_iff_surjective.mpr hs
    intro p hp h
    have h0 : Sq.restrict hSq ⟨Q.mkQ p, p, hp, rfl⟩ = 0 :=
      Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h)
    have h1 := (injective_iff_map_eq_zero _).mp hi _ h0
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val h1)

theorem gmult_eq_zero_of_inj {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (P Q : Submodule k U) (x : k)
    (hP : ∀ p ∈ P, (T - algebraMap k (Module.End k U) x) p ∈ P)
    (hQ : ∀ p ∈ Q, (T - algebraMap k (Module.End k U) x) p ∈ Q)
    (h : ∀ p ∈ P, (T - algebraMap k (Module.End k U) x) p ∈ Q → p ∈ Q) : gmult T P Q x = 0 := by
  unfold gmult
  set S := T - algebraMap k (Module.End k U) x with hS
  have h1 : ∀ m : ℕ, ∀ p ∈ P, (S ^ m) p ∈ Q → p ∈ Q := by
    intro m
    induction m with
    | zero => intro p _ hp; simpa using hp
    | succ m ih =>
      intro p hp hq
      rw [pow_succ, Module.End.mul_apply] at hq
      exact h p hp (ih _ (hP p hp) hq)
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m p hp => ?_
    rw [Submodule.mem_comap] at hp ⊢
    rw [pow_succ', Module.End.mul_apply]
    exact hQ _ hp
  have htop : Q.submoduleOf (P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨p, hp, hp'⟩ _
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hp'
    exact h1 m p hp hm
  rw [htop]
  exact Module.finrank_zero_of_subsingleton

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem graded_inj {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (b : ℤ) (y : k) (h : sen g N (y + b) = 0) :
    ∀ x ∈ sh b N, nab g x - y • x ∈ sh (b + 1) N → x ∈ sh (b + 1) N := by
  haveI := Window.finite_quot hN
  obtain ⟨h1, -⟩ := Window.bij_of_gmult_zero (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
    (fun p hp => Window.nab_mem hC hp) (fun p hp => Window.nab_mem_sh R hg hC 1 hp) (y + b) h
  have hv : vv k ≠ 0 := vv_ne_zero k
  intro x hx hx'
  obtain ⟨n, hn, rfl⟩ := mem_sh_iff_exists.mp hx
  obtain ⟨n', hn', e⟩ := Window.nab_shift R hg hC b hn
  obtain ⟨t, ht, e'⟩ := mem_sh_iff_exists.mp hx'
  have hc : y • vv k ^ b • n = vv k ^ b • y • n := by
    rw [← smul_assoc, const_smul_eq, mul_comm, mul_smul, ← mul_one (algebraMap k k⸨X⸩ y), ← const_smul_eq,
      smul_assoc, one_smul]
  rw [e, hc, ← smul_sub, zpow_add_one₀ hv, mul_smul] at e'
  have e2 := smul_right_injective V (zpow_ne_zero b hv) e'
  have : n ∈ sh 1 N := h1 n hn (mem_sh_iff_exists.mpr ⟨t - n', N.sub_mem ht hn', by
    rw [zpow_one, smul_sub, e2, add_smul]; abel⟩)
  obtain ⟨r, hr, rfl⟩ := mem_sh_iff_exists.mp this
  exact mem_sh_iff_exists.mpr ⟨r, hr, by rw [zpow_add₀ hv, mul_smul]⟩

theorem sen_compare : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N₁ N₂ : Submodule k⟦X⟧ V, IsLat N₁ → IsLat N₂ → CondC g N₁ → CondC g N₂ → ∀ s : ℕ, sh s N₁ ≤ N₂ → N₂ ≤ sh (-s) N₁ → ∀ y : k, sen g N₂ y ≠ 0 → ∃ j : ℤ, |j| ≤ s ∧ sen g N₁ (y + j) ≠ 0 := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N₁ N₂ h₁ h₂ c₁ c₂ s lo hi y hy
  by_contra hcon
  push_neg at hcon
  apply hy
  set S : Module.End k V := nab g - algebraMap k (Module.End k V) y with hSdef
  have hS : ∀ p, S p = nab g p - y • p := fun p => rfl
  have st : ∀ N : Submodule k⟦X⟧ V, CondC g N → ∀ b : ℤ, ∀ p ∈ sh b N, S p ∈ sh b N := fun N c b p hp => by
    rw [hS]
    exact (sh b N).sub_mem (Window.nab_mem_sh R hg c b hp) (((sh b N).restrictScalars k).smul_mem y hp)
  have st2 : ∀ p ∈ N₂, S p ∈ N₂ := by
    have := st N₂ c₂ 0
    rwa [sh_zero_eq] at this
  have key : ∀ m : ℕ, m ≤ 2 * s + 1 → ∀ x ∈ N₂, ∃ p ∈ N₂, x - S p ∈ sh (-s + m) N₁ := by
    intro m
    induction m with
    | zero => intro _ x hx; exact ⟨0, N₂.zero_mem, by simpa using hi hx⟩
    | succ m ih =>
      intro hm x hx
      obtain ⟨p, hp, hp'⟩ := ih (by omega) x hx
      set b : ℤ := -s + m with hb
      have hsen := hcon b (by rw [abs_le]; omega)
      have hf := Window.finite_quot (h₁.shift b).1
      rw [sh_sh_eq, add_comm] at hf
      haveI : FiniteDimensional k (((N₂ ⊓ sh b N₁).restrictScalars k).map
          ((sh (b + 1) N₁).restrictScalars k).mkQ) :=
        Submodule.finiteDimensional_of_le (S₂ := ((sh b N₁).restrictScalars k).map
          ((sh (b + 1) N₁).restrictScalars k).mkQ) (Submodule.map_mono fun z hz => hz.2)
      obtain ⟨q, hq, hq'⟩ := (inj_iff_surj S ((N₂ ⊓ sh b N₁).restrictScalars k)
        ((sh (b + 1) N₁).restrictScalars k) (fun z hz => ⟨st2 z hz.1, st N₁ c₁ b z hz.2⟩)
        (fun z hz => st N₁ c₁ _ z hz)).mp
        (fun z hz hz' => graded_inj R hg h₁.1 c₁ b y hsen z hz.2 hz') (x - S p)
        ⟨N₂.sub_mem hx (st2 p hp), hp'⟩
      refine ⟨p + q, N₂.add_mem hp hq.1, ?_⟩
      rw [map_add (f := _), ← sub_sub, Nat.cast_succ, ← add_assoc]
      exact hq'
  haveI := Window.finite_quot h₂.1
  refine gmult_eq_zero_of_inj (nab g) _ _ y st2 (st N₂ c₂ 1) ?_
  refine (inj_iff_surj S (N₂.restrictScalars k) ((sh 1 N₂).restrictScalars k) st2 (st N₂ c₂ 1)).mpr ?_
  intro x hx
  obtain ⟨p, hp, hp'⟩ := key (2 * s + 1) le_rfl x hx
  refine ⟨p, hp, sh_le_sh 1 lo ?_⟩
  rw [sh_sh_eq]
  convert hp' using 2
  push_cast; ring

end GlobalTheory.PhiGam.Compare
end
end

section

namespace GlobalTheory.BK

open PowerSeries Filter Topology

theorem algebraMap_mem_nonZeroDivisors_adicCompletion {B : Type} [CommRing B] {s : B}
    (hs : s ∈ nonZeroDivisors B) :
    algebraMap B (AdicCompletion (Ideal.span {s}) B) s ∈
      nonZeroDivisors (AdicCompletion (Ideal.span {s}) B) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {s}) (n + 1) x)
  have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {s}) (n + 1)) hx
  rw [map_mul, map_zero, AlgHom.commutes, ← hr, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 : (r - s ^ n * c) * s = 0 := by rw [sub_mul, hc]; ring
  have h3 := (mem_nonZeroDivisors_iff_right.1 hs) _ h2
  rw [evalₐ_of_succ _ hr.symm, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact ⟨c, sub_eq_zero.1 h3⟩

theorem Ehat_mem_nonZeroDivisors (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : Ehat O K l e ∈ nonZeroDivisors (Ahat O K l e) := by
  have hE : E (K := K) l e ≠ 0 := by
    intro h
    have hcoeff := congrArg (coeff e) h
    rw [E, map_add, coeff_X_pow_self, ← map_natCast (C : K →+* K⟦X⟧),
      coeff_C_of_ne_zero (NeZero.ne e), add_zero, map_zero] at hcoeff
    exact one_ne_zero hcoeff
  let s : invL l (A O K) :=
    ⟨E (K := K) l e, by
      unfold E
      exact add_mem (pow_mem HasU.X_mem e) (natCast_mem _ l)⟩
  exact algebraMap_mem_nonZeroDivisors_adicCompletion (s := s)
    (mem_nonZeroDivisors_of_ne_zero fun h => hE (congrArg Subtype.val h))

end GlobalTheory.BK
end

section

open GlobalTheory.LogU

theorem _root_.GlobalTheory.T.factorialTruncatedLogAdditivityDefect_coeff_dvd : ∀ (n i j : ℕ), n ≤ i + j → ∃ d : ℤ, ((i.factorial * j.factorial : ℕ) : ℤ) * AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) = ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * d := by
  first | exact @GlobalTheory.LogUIntg.logDefect_coeff_dvd | exact GlobalTheory.LogUIntg.logDefect_coeff_dvd | (intros; apply GlobalTheory.LogUIntg.logDefect_coeff_dvd <;> assumption)
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.finite_card_torsionLevel_fractionRingQuot : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {ϖ : O}, Irreducible ϖ → ∀ {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ n : ℕ,
    Finite (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) ∧
      Nat.card (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  first | exact @GlobalTheory.ShapeNeg.levKO_card | exact GlobalTheory.ShapeNeg.levKO_card | (intros; apply GlobalTheory.ShapeNeg.levKO_card <;> assumption)
end

section


theorem _root_.GlobalTheory.T.shiftedJumpUpperBound_le_twist_bound : ∀ (t : ℕ) (up : Bool) (Fl Fc : Finset ℤ) (η S B W0 : ℝ), 1 ≤ t → (t : ℝ) ≤ η → 0 ≤ B → 0 ≤ S →
    (∀ z ∈ Fl, |(z : ℝ) - ((t : ℝ) - 1) / 2| ≤ η ∧ 2 * B + (t : ℝ) / 2 + 3 ≤ |(z : ℝ) - ((t : ℝ) - 1) / 2|) →
    (∀ z ∈ Fc, W0 ≤ (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ≤ W0 + S + η + 1) →
    2 * B + (t : ℝ) / 2 + 3 ≤ W0 →
    ((GlobalTheory.PositionData.hS up t Fl Fc : ℕ) : ℝ) ≤ W0 + S + 2 * η + 3 := by
  first | exact @GlobalTheory.hS_le_bound | exact GlobalTheory.hS_le_bound | (intros; apply GlobalTheory.hS_le_bound <;> assumption)
end
