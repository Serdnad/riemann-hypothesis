module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle225
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedTraceAndLvlDvd
public import Mathlib.NumberTheory.Padics.RingHoms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle053
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle085
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemPreparationNormalFormOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle054
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle055
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.PrimesCongruentOne
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

private lemma natAbs_eq_one_of_dvd_prime_pow_not_dvd {d : ℤ} {m k : ℕ} (hm : m.Prime) (h1 : d ∣ (m : ℤ) ^ k)
    (h2 : ¬ (m : ℤ) ∣ d) : d.natAbs = 1 := by
  have h1' : d.natAbs ∣ m ^ k := by
    have := Int.natAbs_dvd_natAbs.mpr h1
    simpa [Int.natAbs_pow] using this
  have hc : Nat.Coprime m d.natAbs := by
    rw [hm.coprime_iff_not_dvd]
    intro h
    exact h2 (Int.natCast_dvd.mpr h)
  exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hc).symm h1'

theorem irreducible_cyclotomic_of_not_dvd_discr (K : Type) [Field K] [NumberField K] (m : ℕ)
    (hm : m.Prime) (hd : ¬ (m : ℤ) ∣ discr K) : Irreducible (cyclotomic m K) := by
  apply GlobalTheory.cyclotomic_irreducible_of_not_dvd_discr <;> assumption

theorem exists_prime_dvd_sub_one_irreducible_cyclotomic :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), n ≠ 0 →
      ∃ m : ℕ, m.Prime ∧ n ∣ m - 1 ∧ Irreducible (cyclotomic m K) := by
  intro K _ _ n hn
  obtain ⟨m, hmp, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (NumberField.discr K).natAbs hn
  refine ⟨m, hmp, (Nat.modEq_iff_dvd' hmp.one_le).mp hmod.symm, ?_⟩
  apply irreducible_cyclotomic_of_not_dvd_discr K m hmp
  intro h
  have hne : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.natCast_dvd.mp h)
  omega

end GlobalTheory
end

section

open PowerSeries

namespace GlobalTheory

theorem padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2)
    (δ : ℤ_[l]) {n : ℕ} (hn : n ≠ 0) (hδ : δ ^ n = 1) (h1 : PadicInt.toZMod δ = 1) : δ = 1 := by
  apply GlobalTheory.CycFr.TraceOnePlusX.eq_one_of_pow_eq_one <;> assumption

theorem exists_coset_representatives_of_finite_subgroup_padicInt_units {l : ℕ} [hl : Fact l.Prime]
    (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (h2 : l ≠ 2) :
    ∃ (e : ℕ) (a : Fin e → ℕ), e * Nat.card Δ = l - 1 ∧ (∀ τ, ¬ l ∣ a τ) ∧
      (∀ τ τ', τ ≠ τ' → (a τ : ZMod l) ^ Nat.card Δ ≠ (a τ' : ZMod l) ^ Nat.card Δ) ∧
      ∀ x : ZMod l, x ≠ 0 → ∃! p : Fin e × Δ,
        x = (a p.1 : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) := by
  classical
  let g : Δ →* (ZMod l)ˣ :=
    (Units.map (PadicInt.toZMod (p := l) : ℤ_[l] →+* ZMod l).toMonoidHom).comp Δ.subtype
  have hg : ∀ d : Δ, (g d : ZMod l) = PadicInt.toZMod ((d : ℤ_[l]ˣ) : ℤ_[l]) := fun _ => rfl
  have hs : Nat.card Δ ≠ 0 := Nat.card_pos.ne'
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : PadicInt.toZMod ((d : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by rw [← hg, hd]; rfl
    have hp : ((d : ℤ_[l]ˣ) : ℤ_[l]) ^ Nat.card Δ = 1 := by
      have : d ^ Nat.card Δ = 1 := pow_card_eq_one'
      have := congrArg (fun z : Δ => ((z : ℤ_[l]ˣ) : ℤ_[l])) this
      simpa only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one] using this
    exact Subtype.ext (Units.ext (padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one h2 _ hs hp h1))
  let H : Subgroup (ZMod l)ˣ := g.range
  have hH : Nat.card H = Nat.card Δ := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hHmem : ∀ x : (ZMod l)ˣ, x ^ Nat.card Δ = 1 → x ∈ H := by
    intro x hx
    have hle : H ≤ (powMonoidHom (Nat.card Δ) : (ZMod l)ˣ →* (ZMod l)ˣ).ker := by
      intro y hy
      have : (⟨y, hy⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
      rw [hH] at this
      simpa using congrArg Subtype.val this
    have hc : Nat.card (powMonoidHom (Nat.card Δ) : (ZMod l)ˣ →* (ZMod l)ˣ).ker ≤ Nat.card H := by
      rw [IsCyclic.card_powMonoidHom_ker, hH]
      exact Nat.gcd_le_right _ (Nat.pos_of_ne_zero hs)
    rw [Subgroup.eq_of_le_of_card_ge hle hc]
    simpa using hx
  let φ : ((ZMod l)ˣ ⧸ H) ≃ Fin (Nat.card ((ZMod l)ˣ ⧸ H)) := Finite.equivFin _
  let r : Fin (Nat.card ((ZMod l)ˣ ⧸ H)) → (ZMod l)ˣ := fun τ => (φ.symm τ).out
  have hr : ∀ τ, ((r τ : (ZMod l)ˣ) : (ZMod l)ˣ ⧸ H) = φ.symm τ := fun τ => Quotient.out_eq _
  have hcast : ∀ τ, (((r τ : ZMod l).val : ℕ) : ZMod l) = r τ := fun τ => ZMod.natCast_zmod_val _
  have hreq : ∀ τ τ', (r τ)⁻¹ * r τ' ∈ H → τ = τ' := by
    intro τ τ' h
    have := QuotientGroup.eq.mpr h
    rw [hr, hr] at this
    exact φ.symm.injective this
  refine ⟨_, fun τ => (r τ : ZMod l).val, ?_, ?_, ?_, ?_⟩
  · rw [← hH, ← Subgroup.card_eq_card_quotient_mul_card_subgroup, Nat.card_eq_fintype_card,
      ZMod.card_units]
  · intro τ h
    have := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [hcast] at this
    exact (r τ).ne_zero this
  · intro τ τ' hne h
    simp only [hcast] at h
    have h' : r τ ^ Nat.card Δ = r τ' ^ Nat.card Δ := Units.ext (by simpa using h)
    exact hne (hreq _ _ (hHmem _ (by rw [mul_pow, inv_pow, h', inv_mul_cancel])))
  · intro x hx
    let u : (ZMod l)ˣ := Units.mk0 x hx
    have hu : (r (φ u))⁻¹ * u ∈ H := by
      rw [← QuotientGroup.eq, hr, Equiv.symm_apply_apply]
    obtain ⟨d, hd⟩ := hu
    have hform : ∀ p : Fin (Nat.card ((ZMod l)ˣ ⧸ H)) × Δ,
        x = (((r p.1 : ZMod l).val : ℕ) : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) ↔
          u = r p.1 * g p.2 := by
      intro p
      rw [hcast, ← hg, Units.ext_iff]
      rfl
    have hd' : u = r (φ u) * g d := by rw [hd, mul_inv_cancel_left]
    refine ⟨(φ u, d), (hform _).mpr hd', ?_⟩
    rintro ⟨τ, d'⟩ hp
    have hp' : u = r τ * g d' := (hform _).mp hp
    have hτ : τ = φ u := by
      apply hreq
      refine ⟨d' * d⁻¹, ?_⟩
      rw [map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hp', mul_inv_eq_iff_eq_mul]
      exact hd'
    rw [hτ] at hp'
    have : g d' = g d := mul_left_cancel (hp'.symm.trans hd')
    rw [hτ, hinj this]

end GlobalTheory
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.TestFn

theorem unif_const (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (f : X → ℂ)
    (hf : IsTest f) : ∃ V ∈ 𝓝 (0 : X), ∀ x v, v ∈ V → f (x + v) = f x := by
  apply GlobalTheory.isTest_nhds_inv <;> assumption

theorem slice_test {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (T : X × Y → ℂ) (hT : IsTest T) (y : Y) :
    IsTest (fun x => T (x, y)) := by
  refine ⟨hT.1.comp_continuous (Continuous.prodMk_left y), ?_⟩
  have hc : IsCompact (Prod.fst '' tsupport T) := hT.2.image continuous_fst
  refine hc.of_isClosed_subset (isClosed_tsupport _) ?_
  have h1 : IsClosed ((fun x => (x, y)) ⁻¹' tsupport T) := (isClosed_tsupport T).preimage (Continuous.prodMk_left y)
  refine (closure_minimal ?_ h1).trans ?_
  · intro x hx; exact subset_tsupport T hx
  · intro x hx; exact ⟨(x, y), hx, rfl⟩

end GlobalTheory.TestFn
end

section

noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

namespace InvAlg

variable {K : UQ} (B : InvAlg K)

theorem torusOrb_mem_mulLat_unit (u : B.Aˣ) (L : Submodule K.O B.A) (y : B.A) :
    y ∈ mulLat K.O (u : B.A) L ↔ ((u⁻¹ : B.Aˣ) : B.A) * y ∈ L := by
  unfold mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [LinearMap.mulLeft_apply, ← mul_assoc] using hz
  · intro h
    exact ⟨_, h, by simp [LinearMap.mulLeft_apply, ← mul_assoc]⟩

theorem torusOrb_mulLat_one (L : Submodule K.O B.A) : mulLat K.O (1 : B.A) L = L := by
  ext y; simpa using torusOrb_mem_mulLat_unit B 1 L y

theorem torusOrb_mulLat_mul (s t : B.Aˣ) (L : Submodule K.O B.A) :
    mulLat K.O ((s : B.A)) (mulLat K.O (t : B.A) L) = mulLat K.O ((s * t : B.Aˣ) : B.A) L := by
  ext y
  rw [torusOrb_mem_mulLat_unit, torusOrb_mem_mulLat_unit, torusOrb_mem_mulLat_unit, mul_inv_rev, Units.val_mul, mul_assoc]

theorem torusOrb_mulLat_inv (t : B.Aˣ) (L : Submodule K.O B.A) :
    mulLat K.O ((t⁻¹ : B.Aˣ) : B.A) (mulLat K.O (t : B.A) L) = L := by
  rw [torusOrb_mulLat_mul, inv_mul_cancel, Units.val_one, torusOrb_mulLat_one]

theorem herm_torus_mul_right_eq_inv_mul_middle (x y : B.A) (t : B.Aˣ) (ht : t ∈ B.T) (z : B.A) :
    B.herm x y ((t : B.A) * z) = B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) z := by
  have h1 : ((t⁻¹ : B.Aˣ) : B.A) = B.σ (t : B.A) := Units.inv_eq_of_mul_eq_one_right ht
  unfold herm
  rw [show B.σ ((t : B.A) * z) = B.σ (t : B.A) * B.σ z from map_mul B.σ _ _, ← h1]
  congr 1
  ring

theorem torusOrb_mulLat_mem_X (x : B.A) (t : B.Aˣ) (ht : t ∈ B.T) (L : Submodule K.O B.A) (hL : L ∈ B.X x) :
    mulLat K.O (t : B.A) L ∈ B.X x := by
  apply GlobalTheory.UnitLemma.TorusAction.torus_mem_X <;> assumption

def torusOrbRel (x : B.A) (L M : B.X x) : Prop :=
  ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) (L : Submodule K.O B.A)

theorem torusOrb_orbRel_equivalence (x : B.A) : Equivalence (B.torusOrbRel x) := by
  refine { refl := ?_, symm := ?_, trans := ?_ }
  · intro L
    exact ⟨1, B.T.one_mem, by rw [Units.val_one, torusOrb_mulLat_one]⟩
  · rintro L M ⟨t, ht, h⟩
    refine ⟨t⁻¹, B.T.inv_mem ht, ?_⟩
    rw [h, torusOrb_mulLat_inv]
  · rintro L M N ⟨s, hs, h1⟩ ⟨t, ht, h2⟩
    refine ⟨t * s, B.T.mul_mem ht hs, ?_⟩
    rw [h2, h1, torusOrb_mulLat_mul]

theorem torusOrb_orb_mk_eq (x : B.A) {L M : B.X x}
    (h : (Quot.mk (B.torusOrbRel x) L : Orb K.O B.T (B.X x)) = Quot.mk (B.torusOrbRel x) M) : B.torusOrbRel x L M :=
  (Equivalence.eqvGen_iff (B.torusOrb_orbRel_equivalence x)).1 (Quot.eqvGen_exact h)

def torusOrb_orbSplit (x w : B.A) : {L : B.X x // w ∈ (L : Submodule K.O B.A)} ≃
    Σ o : Orb K.O B.T (B.X x), {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} where
  toFun L := ⟨(Quot.mk (B.torusOrbRel x) L.1 : Orb K.O B.T (B.X x)), L.1.1,
    B.torusOrb_orb_mk_eq x (Quot.out_eq (Quot.mk (B.torusOrbRel x) L.1 : Orb K.O B.T (B.X x))), L.2⟩
  invFun p := ⟨⟨p.2.1, by
      obtain ⟨t, ht, h⟩ := p.2.2.1
      rw [h]
      exact B.torusOrb_mulLat_mem_X x t ht _ (Quot.out p.1).2⟩, p.2.2.2⟩
  left_inv L := rfl
  right_inv p := by
    obtain ⟨o, M, h⟩ := p
    refine Sigma.subtype_ext ?_ rfl
    dsimp only
    conv_rhs => rw [← Quot.out_eq o]
    symm
    apply Quot.sound
    exact h.1

theorem torusOrb_UU_eq_finsum (x w : B.A) (hfin : Finite (Orb K.O B.T (B.X x)))
    (hfib : ∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) :
    B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} := by
  haveI := Fintype.ofFinite (Orb K.O B.T (B.X x))
  unfold UU
  rw [Nat.card_congr (B.torusOrb_orbSplit x w), Nat.card_sigma, finsum_eq_sum_of_fintype]

end InvAlg

theorem UU_eq_sum_orbits : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), Finite (Orb K.O B.T (B.X x)) →
    (∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) →
    B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} :=
  fun _ B x w h1 h2 => B.torusOrb_UU_eq_finsum x w h1 h2

end GlobalTheory.UnitLemma
end
end

section

namespace GlobalTheory.SpanOfResidue

theorem mem_smul_top_of_entries {A : Type} [CommRing A] {r : ℕ} (I : Ideal A)
    (d : Matrix (Fin r) (Fin r) A) (hd : ∀ i j, d i j ∈ I) :
    d ∈ I • (⊤ : Submodule A (Matrix (Fin r) (Fin r) A)) := by
  rw [Matrix.matrix_eq_sum_single d]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have h : Matrix.single i j (d i j) = d i j • Matrix.single i j (1 : A) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h]
  exact Submodule.smul_mem_smul (hd i j) Submodule.mem_top

theorem span_eq_top_of_residue {ι A : Type} [CommRing A] [IsLocalRing A] {r : ℕ}
    (f : ι → Matrix (Fin r) (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range fun (i : ι) ↦ Matrix.map (f i)
        (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A)) = ⊤) :
    Submodule.span A (Set.range f) = ⊤ := by
  apply GlobalTheory.TraceConj.span_top_of_residual <;> assumption

end GlobalTheory.SpanOfResidue
end

section

namespace GlobalTheory.ScalarMultipleMembership

theorem exists_smul_mem {Ks WL : Type} [Field Ks] [NumberField Ks] [AddCommGroup WL] [Module Ks WL]
    [Module (NumberField.RingOfIntegers Ks) WL]
    [IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL]
    (M : Submodule (NumberField.RingOfIntegers Ks) WL) (x : WL)
    (hx : x ∈ Submodule.span Ks (M : Set WL)) :
    ∃ a : NumberField.RingOfIntegers Ks, a ≠ 0 ∧ a • x ∈ M := by
  apply Formalism.L2.SG.Pf.LatEx.exists_smul_mem_of_mem_span <;> assumption

theorem main {LL Ks WL G : Type} [inst : Field LL] [NumberField LL] [inst_2 : Field Ks] [inst_3 : NumberField Ks] [inst_4 : Algebra Ks LL] [inst_5 : AddCommGroup WL] [inst_6 : Module LL WL] [inst_7 : Module Ks WL] [IsScalarTower Ks LL WL] [inst_9 : Module (NumberField.RingOfIntegers Ks) WL] [inst_10 : IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL] {W : (LL →+* ℂ) → Type} [inst_11 : (σ : LL →+* ℂ) → NormedAddCommGroup (W σ)] [inst_12 : (σ : LL →+* ℂ) → InnerProductSpace ℂ (W σ)] [inst_13 : Group G] (Φ : Formalism.IndefR.Arith.FormsL LL Ks WL W G)
    (h : Submodule.span Ks (↑(Formalism.IndefR.Arith.FormsL.MK Φ) : Set WL) = Formalism.IndefR.Arith.FormsL.WK Φ) :
    ∀ x ∈ Formalism.IndefR.Arith.FormsL.WK Φ, ∃ (a : NumberField.RingOfIntegers Ks), a ≠ (0 : NumberField.RingOfIntegers Ks) ∧ a • x ∈ Formalism.IndefR.Arith.FormsL.MK Φ := by
  intro x hx
  rw [← h] at hx
  exact exists_smul_mem _ x hx

end GlobalTheory.ScalarMultipleMembership
end

section

open MeasureTheory

namespace GlobalTheory.SplitWeil

theorem nabs_map_of_homeomorph : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → ∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x := by
  intro k k' _ _ _ _ _ _ _ _ i hi hi' x
  haveI : SecondCountableTopology k := (Model.secondCountable_and_t2_local_field (k := k)).1
  haveI : T2Space k := (Model.secondCountable_and_t2_local_field (k := k)).2
  haveI : SecondCountableTopology k' := (Model.secondCountable_and_t2_local_field (k := k')).1
  haveI : T2Space k' := (Model.secondCountable_and_t2_local_field (k := k')).2
  let e : k ≃ₜ+ k' :=
    { i.toAddEquiv with
      continuous_toFun := hi
      continuous_invFun := hi' }
  unfold nabs
  congr 1
  exact GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e x (Units.map i.toRingHom.toMonoidHom x) (fun y => by
    change i ((x : k) * y) = i x * i y
    exact map_mul i _ _)

end GlobalTheory.SplitWeil
end

section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.additiveSystem_preparation_normalForm_one : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → 1 ≤ D → ∀ M : ℕ → Matrix m m F, Normal 1 M → ∃ (A : Matrix m m F) (U : ℕ → Matrix m m F), (∀ i j, ‖A i j‖ ≤ 1) ∧ (∀ i j, ‖(U 0 - 1) i j‖ < 1) ∧ (∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1) ∧ M 0 = -(U 0 * A) ∧ ∀ x : m → F, gsum (p ^ e) D M x = gsum (p ^ e) D U (fun i => x i ^ p ^ e - A.mulVec x i) := by
  first | exact @GlobalTheory.PMonE.preparation | exact GlobalTheory.PMonE.preparation | (intros; apply GlobalTheory.PMonE.preparation <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hasCompactSupport_partialFourierGLBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f' : Gl r F → ℂ, IsTest f' → (∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) → HasCompactSupport (fourG M ψ f') := by
  first | exact @GlobalTheory.JR.fourG_hasCompactSupport | exact GlobalTheory.JR.fourG_hasCompactSupport | (intros; apply GlobalTheory.JR.fourG_hasCompactSupport <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.partialFourierGLBlock_unitIndicator : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → fourG M ψ (unitG r F) = unitG r F := by
  first | exact @GlobalTheory.JR.fourG_unitG | exact GlobalTheory.JR.fourG_unitG | (intros; apply GlobalTheory.JR.fourG_unitG <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.partialFourierHermitianBlock_hasCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f → (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → HasCompactSupport (fourU M ψ f) := by
  first | exact @GlobalTheory.fourU_hasCompactSupport | exact GlobalTheory.fourU_hasCompactSupport | (intros; apply GlobalTheory.fourU_hasCompactSupport <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.partialFourierHermitianBlock_unitIndicator : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → (∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1) → fourU M ψ (unitU r F E) = unitU r F E := by
  first | exact @GlobalTheory.JR.FourUnit.fourU_unitU | exact GlobalTheory.JR.FourUnit.fourU_unitU | (intros; apply GlobalTheory.JR.FourUnit.fourU_unitU <;> assumption)
end
