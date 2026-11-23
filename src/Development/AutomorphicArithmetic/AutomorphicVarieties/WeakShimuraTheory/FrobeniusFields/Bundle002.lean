module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Bundle002
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002

@[expose] public section

local instance (priority := 2000) ratFieldIsTorsionFreeForFrobeniusFields (Ω : Type) [Field Ω] [CharZero Ω] :
    Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

structure QuadAt (p : ℕ) (s : ℤˣ) (S : Finset ℕ) (η : G ℚ Ω →* ℤˣ) : Prop where
  prime : p.Prime
  nm : p ∉ S
  opn : IsOpen (η.ker : Set (G ℚ Ω))
  idx : η.ker.index = 2
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (p : Ω) < 1 → Ine (F := ℚ) A ≤ η.ker
  ram : ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∃ g ∈ Ine (F := ℚ) A, η g = -1
  cc : ∀ σ : G ℚ Ω, IsCC σ → η σ = s
  split : ∀ q ∈ S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → Dec (F := ℚ) A ≤ η.ker

structure Kap (D : Raw Ω c) (κ : G ℚ Ω →* c.Oˣ) : Prop where
  opn : IsOpen (κ.ker : Set (G ℚ Ω))
  pow : ∃ j : ℕ, κ ^ l ^ j = 1
  unrS : ∀ A, Raw.Away D.S A → Ine (F := ℚ) A ≤ κ.ker
  unrL : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ κ.ker
  kb : ∀ A, Raw.Away {l} A → ∀ g ∈ Ine (F := ℚ) A, Raw.bar D.Psi g = 1 → κ g = 1 → D.ψ g = 1
  kc : ∃ m : ℕ, l.Coprime m ∧ ∀ g, cycZ ℚ Ω l g = 1 → κ g = 1 → D.ψ g ^ m = 1

structure Set2 (D : Raw Ω c) where
  κ : G ℚ Ω →* c.Oˣ
  p₃ : ℕ
  p : ℕ
  p' : ℕ
  φ : G ℚ Ω →* ℤˣ
  η : G ℚ Ω →* ℤˣ
  η' : G ℚ Ω →* ℤˣ
  kap : Kap D κ
  hφ : QuadAt p₃ 1 D.S φ
  hη : QuadAt p (-1) (insert p₃ D.S) η
  hη' : QuadAt p' (-1) (insert p (insert p₃ D.S)) η'
  psi_cc : ∀ σ : G ℚ Ω, IsCC σ → D.Psi σ = 1
  ord : ∃ n : ℕ, D.ξ ^ 2 ^ n = 1
  xi : ∀ A, Raw.Away {2} A → Ine (F := ℚ) A ≤ D.ξ.ker
  ev : ∃ t, D.om t = 1 ∧ κ t = 1 ∧ Raw.bar D.Psi t = -1
  bigL : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
    ∃ g ∈ Dec (F := ℚ) A, Raw.bar D.Psi g = 1 ∧ κ g = 1 ∧ Raw.bar D.ξ g ^ 4 ≠ 1
  big2 : ∀ A : ValuationSubring Ω, A.valuation (2 : Ω) < 1 →
    ∃ g ∈ Ine (F := ℚ) A, Raw.bar D.Psi g = 1 ∧ κ g = 1 ∧ Raw.bar D.ξ g ^ 4 ≠ 1

namespace Set2

variable {D : Raw Ω c} (X : Set2 D)

def H : Subgroup (G ℚ Ω) :=
  ((Units.map (residue c.O).toMonoidHom).comp D.Psi).eqLocus
    ((Units.map (Int.castRingHom (ResidueField c.O)).toMonoidHom).comp X.φ) ⊓ X.η.eqLocus X.η' ⊓ X.κ.ker

theorem mem_H {g : G ℚ Ω} :
    g ∈ X.H ↔ Raw.bar D.Psi g = ((X.φ g : ℤ) : ResidueField c.O) ∧ X.η g = X.η' g ∧ X.κ g = 1 :=
  ⟨fun h => ⟨congrArg Units.val h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨Units.ext h.1, h.2.1⟩, h.2.2⟩⟩

structure Elts (a u t : G ℚ Ω) : Prop where
  a_mem : a ∈ X.H ⊓ X.η.ker
  a_xi : Raw.bar D.ξ a = -1
  a_psi : Raw.bar D.Psi a = 1
  a_om : Raw.bar D.om a = -1
  u_mem : u ∈ X.H ⊓ X.η.ker
  u_xi : Raw.bar D.ξ u ^ 4 ≠ 1
  u_psi : Raw.bar D.Psi u = 1
  u_om : D.om u = 1
  t_mem : t ∈ X.H ⊓ X.η.ker
  t_xi : Raw.bar D.ξ t ^ 2 ≠ 1
  t_psi : Raw.bar D.Psi t = -1
  t_om : D.om t = 1

def On (T : Tower D) : Prop := T.F.fixingSubgroup = X.H ∧ T.K.fixingSubgroup = X.η.ker

end Set2

theorem resQ_mem (F : IntermediateField ℚ Ω) (g : G F Ω) : resQ F g ∈ F.fixingSubgroup :=
  (F.mem_fixingSubgroup_iff _).2 fun x hx => g.commutes ⟨x, hx⟩

theorem exists_resQ {F : IntermediateField ℚ Ω} {g : G ℚ Ω} (hg : g ∈ F.fixingSubgroup) : ∃ s : G F Ω, resQ F s = g :=
  ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun x => (F.mem_fixingSubgroup_iff g).1 hg x.1 x.2, rfl⟩

theorem resQ_Dec (F : IntermediateField ℚ Ω) [NumberField F] (A : ValuationSubring Ω) (g : G F Ω) :
    g ∈ Dec (F := F) A ↔ resQ F g ∈ Dec (F := ℚ) A := Iff.rfl

theorem resQ_Ine (F : IntermediateField ℚ Ω) [NumberField F] (A : ValuationSubring Ω) (g : G F Ω) :
    g ∈ Ine (F := F) A ↔ resQ F g ∈ Ine (F := ℚ) A := Iff.rfl

theorem resQ_cyc (F : IntermediateField ℚ Ω) [NumberField F] (g : G F Ω) : cycZ ℚ Ω l (resQ F g) = cycZ F Ω l g := rfl

end UpperTheory.V.Ws

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open Formalism.GaloisCohomology UpperTheory.V UpperTheory.Top

private theorem psi_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) (e : ℕ) {σ : G ℚ Ω} (h : IsConjOm σ.toRingEquiv)
    (hψ : PsiEven e ψ) : Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 := by
  have h1 : cycZ ℚ Ω l σ = -1 := h.cyc (E := ℚ)
  have h2 : Chr.cls ℚ Ω N σ = -1 := (Chr.clsFacts ℚ Ω N).2.2.2.1 σ h
  have h3 : chiO ℚ Ω l O σ = -1 := by
    ext
    simp [chiO, h1]
  have h4 : ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ : Oˣ) : O) = (-1) ^ e * ψ (-1) := by
    simp [Chr.Psi, Chr.dirG, h2, h3]
  have h5 : ((-1 : O) ^ e) * (-1) ^ e = 1 := by rw [← mul_pow]; simp
  rw [Units.ext_iff, h4, Units.val_one, hψ, h5]

theorem UpperTheory.V.Ws.xi2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → (∃ n : ℕ, D.ξ ^ 2 ^ n = 1) ∧ (∀ A, Raw.Away {2} A → Ine (F := ℚ) A ≤ D.ξ.ker) ∧ ∀ σ : G ℚ Ω, IsCC σ → D.Psi σ = 1 := by
  intro Ω _ _ _ l _ c D hD
  obtain ⟨-, h, t, e, ψ, -, -, -, hψ, -, hO⟩ := hD
  obtain ⟨he, hp, -, _, ξ', ξ₀, -, -, h0, hξ⟩ := hO
  generalize h.nII l ψ = n at ξ' hξ
  have h1 : ξ₀ = 1 := orderOf_eq_one_iff.1 h0
  have h2 : ∀ σ, D.ξ σ = ξ'.toUnitHom (Chr.cls ℚ Ω (2 ^ n) σ) := by
    intro σ
    rw [hξ, MonoidHom.mul_apply, h1]
    have : Chr.cls ℚ Ω 1 σ = 1 := Subsingleton.elim _ _
    simp [Chr.dirG, this]
  refine ⟨⟨n, ?_⟩, fun A hA σ hσ => ?_, fun σ hσ => ?_⟩
  · ext1 σ
    rw [MonoidHom.pow_apply, h2, ← map_pow, MonoidHom.one_apply]
    have h3 : Chr.cls ℚ Ω (2 ^ n) σ ^ 2 ^ n = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      refine orderOf_dvd_card.trans ?_
      rw [ZMod.card_units_eq_totient]
      rcases n with _ | n
      · simp
      · rw [Nat.totient_prime_pow_succ Nat.prime_two]
        simp [pow_succ]
    rw [h3, map_one]
  · have h3 : ¬ A.valuation ((2 ^ n : ℕ) : Ω) < 1 := by
      have h4 := hA 2 (Finset.mem_singleton_self 2)
      rw [Nat.cast_pow, map_pow]
      exact not_lt.2 (one_le_pow₀ (not_lt.1 h4))
    have h4 : Chr.cls ℚ Ω (2 ^ n) σ = 1 := (Chr.clsFacts ℚ Ω (2 ^ n)).2.2.2.2 A h3 hσ
    rw [MonoidHom.mem_ker, h2, h4, map_one]
  · rw [Raw.Psi, he, hp]
    exact psi_cc Ω l ψ e hσ (h.mem_X.1 hψ).2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open UpperTheory.V

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem dirG_pow {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (k : ℕ) (g : G ℚ Ω) :
    Chr.dirG ℚ Ω (χ ^ k) g = Chr.dirG ℚ Ω χ g ^ k := Units.ext (MulChar.pow_apply_coe χ k _)

private theorem dirG_one {O : Type} [CommRing O] {N : ℕ} [NeZero N] (g : G ℚ Ω) :
    Chr.dirG ℚ Ω (1 : DirichletCharacter O N) g = 1 := Units.ext (MulChar.one_apply_coe _)

private theorem dirG_frob {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {A : ValuationSubring Ω} {v : ℕ}
    (hv : v.Prime) (hA : A.valuation (v : Ω) < 1) (hN : ¬ v ∣ N) {σ : G ℚ Ω} (h : IsFrob (F := ℚ) A v σ) :
    (Chr.dirG ℚ Ω χ σ : O) = χ v := by
  have h1 := (ML.placeBasic Ω).2.2.2.2.2.2.1 A v N σ h
    ((ML.placeBasic Ω).2.2.2.1 A v N ((Nat.Prime.coprime_iff_not_dvd hv).2 hN) hA)
  have h2 := (Chr.clsFacts ℚ Ω N).2.2.1 σ (ZMod.unitOfCoprime v ((Nat.Prime.coprime_iff_not_dvd hv).2 hN)) fun ζ hζ => by
    rw [h1 ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod v hζ]
  rw [Chr.dirG, MonoidHom.comp_apply, h2, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]

private theorem pow_cond {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {k : ℕ}
    (h : χ.conductor = 2 ^ k) : χ ^ 2 ^ k = 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h1 : χ.primitiveCharacter ^ Nat.totient χ.conductor = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one,
      MulChar.one_apply_coe]
  have h2 : Nat.totient χ.conductor ∣ 2 ^ k := by
    rw [h]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Nat.totient_prime_pow Nat.prime_two hk]
      simpa using pow_dvd_pow 2 (Nat.sub_le k 1)
  obtain ⟨j, hj⟩ := h2
  rw [← χ.changeLevel_primitiveCharacter, ← map_pow, hj, pow_mul, h1, one_pow, map_one]

private theorem psi_exp (h : Host) {O : Type} [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N) (hψ : h.IsChar ψ)
    {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) :
    ∃ a u : ℕ, Odd u ∧ ψ ^ (2 ^ a * u) = 1 ∧ l ^ 2 * 2 ^ (a + 2) ≤ 2 ^ h.nII l ψ := by
  have hq : 0 < h.q := NeZero.pos _
  have ho : 0 < h.o := orderOf_pos _
  obtain ⟨tψ, ⟨s, hs⟩, -⟩ := X.th1Facts O h.N ψ l hl hl2
  obtain ⟨-, -, t3, -⟩ := hostTh1 h O ψ hψ l hl hl2
  obtain ⟨-, b2⟩ := max_le_iff.1 (Nat.le_pow_clog one_lt_two _ : _ ≤ 2 ^ h.nII l ψ)
  refine ⟨c2 ψ + 1 + h.o.factorization 2, ordCompl[2] h.o * l ^ s, ?_, ?_, ?_⟩
  · exact (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (Nat.not_dvd_ordCompl Nat.prime_two ho.ne'))).mul (hl.odd_of_ne_two hl2).pow
  · have e1 : 2 ^ (c2 ψ + 1 + h.o.factorization 2) * (ordCompl[2] h.o * l ^ s) = 2 ^ c2 ψ * (2 * h.o) * l ^ s := by
      conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self h.o 2]
      ring
    have p1 := pow_cond (psi2 ψ) (compCond O h.N ψ 2 Nat.prime_two).2.2.2.1.symm
    have p2 := orderOf_dvd_iff_pow_eq_one.1 t3
    rw [e1]
    generalize c2 ψ = k at p1 ⊢
    have p3 : (psi2 ψ * th1 l ψ * kap l ψ) ^ (2 ^ k * (2 * h.o) * l ^ s) = 1 := by
      rw [mul_pow, mul_pow, mul_assoc (2 ^ k), pow_mul, p1, one_pow, one_mul, mul_left_comm, pow_mul, p2, one_pow, one_mul,
        ← mul_assoc, mul_comm, pow_mul, hs, one_pow]
    rwa [← tψ] at p3
  · have v2 : 2 ^ h.o.factorization 2 ≤ h.o := Nat.ordProj_le 2 ho.ne'
    refine le_trans ?_ b2
    calc l ^ 2 * 2 ^ (c2 ψ + 1 + h.o.factorization 2 + 2) = 2 ^ (c2 ψ + 3) * 2 ^ h.o.factorization 2 * l ^ 2 * 1 := by ring
      _ ≤ 2 ^ (c2 ψ + 6) * h.o * l ^ 3 * h.q ^ 2 := by
        have hp : 2 ^ (c2 ψ + 3) ≤ 2 ^ (c2 ψ + 6) := by
          gcongr <;> omega
        have hlpow : l ^ 2 ≤ l ^ 3 := by
          gcongr <;> first | exact hl.pos | omega
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hp v2) hlpow)
          (Nat.one_le_pow _ _ hq)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.exists_decomposition_element_at_l_xi_pow_four_ne_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → ∀ (κ : G ℚ Ω →* c.Oˣ) (j : ℕ), κ ^ l ^ j = 1 → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ g ∈ Dec (F := ℚ) A, Raw.bar D.Psi g = 1 ∧ κ g = 1 ∧ Raw.bar D.ξ g ^ 4 ≠ 1 := by
  intro Ω _ _ _ l hl c D ⟨hD, h, t, e, ψ, _, _, _, hmem, _, hO⟩ κ j hκ A hA
  have hlp : l.Prime := hl.out
  have hl2 := hD.l_odd
  obtain ⟨a, u, hu, hψ, hb⟩ := psi_exp h ψ (h.mem_X.1 hmem).1 hlp hl2
  obtain ⟨_, ξ, ξ₀, hξ, -, h0, dξ⟩ := hO.xi
  rw [orderOf_eq_one_iff] at h0
  have hT : l ∈ D.T := Finset.mem_insert_self _ _
  have hfr := hD.sg_frob l hT
  obtain ⟨w, hw, -⟩ := (Chr.placesQ Ω).2.2 l _ A hlp (hD.pl_over l hlp) hA
  have conj : ∀ (γ : G ℚ Ω →* c.Oˣ) (x : G ℚ Ω) (k : ℕ), γ (w⁻¹ * x ^ k * w) = γ x ^ k := fun γ x k => by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul, map_pow]
  generalize h.nII l ψ = n at hb ξ hξ dξ
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : 0 < l ^ 2 * 2 ^ a := by have := hlp.pos; positivity
      rw [pow_add, ← mul_assoc] at hb
      omega
    · exact hn
  have h2 : ¬ l ∣ 2 := fun hd => hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 hd)
  refine ⟨_, hw _ (pow_mem hfr.1 (2 ^ a * u * l ^ j)), ?_, ?_, fun hx => ?_⟩
  · have : D.Psi (D.sg l) = Chr.dirG ℚ Ω ψ (D.sg l) := by
      rw [Raw.Psi, Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, chiO, MonoidHom.comp_apply, hD.sg_cyc,
        map_one, one_pow, one_mul, hO.psi]
    rw [Raw.bar, conj, this, pow_mul, ← dirG_pow, hψ, dirG_one, one_pow, Units.val_one, map_one]
  · rw [conj, mul_comm, pow_mul, ← MonoidHom.pow_apply, hκ, MonoidHom.one_apply, one_pow]
  · have e1 : 2 ^ a * u * l ^ j * 4 = 2 ^ (a + 2) * (u * l ^ j) := by ring
    rw [Raw.bar, conj, ← map_pow, ← Units.val_pow_eq_pow_val, ← pow_mul, e1, dξ, MonoidHom.mul_apply, h0, dirG_one,
      one_mul] at hx
    have r4 : Chr.dirG ℚ Ω ξ (D.sg l) ^ (2 ^ (a + 2) * (u * l ^ j)) = 1 := by
      refine (congrFacts Ω l c).2.2.2.1 _ _ (Nat.totient (2 ^ n)) ?_ ?_ (one_pow _)
        (Ideal.Quotient.eq.1 (hx.trans (map_one (residue c.O)).symm))
      · rw [Nat.totient_prime_pow Nat.prime_two hn]
        exact fun hd => h2 (hlp.dvd_of_dvd_pow (by simpa using hd))
      · rw [← pow_mul, mul_comm, pow_mul, Chr.dirG, MonoidHom.comp_apply, ← map_pow, ZMod.pow_totient, map_one, one_pow]
    have r5 := congrArg Units.val r4
    rw [Units.val_pow_eq_pow_val, dirG_frob ξ hlp (hD.pl_over l hlp) (fun hd => h2 (hlp.dvd_of_dvd_pow hd)) hfr] at r5
    exact (UpperTheory.two_pow_lt_sq_mul_of_primitive_char_pow_eq_one c.O n ξ hξ l (a + 2) _ (hlp.odd_of_ne_two hl2) hlp.one_lt
      (hu.mul (hlp.odd_of_ne_two hl2).pow) r5).not_ge hb
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem res_zpow {O : Type} [CommRing O] [IsLocalRing O] (u : Oˣ) (n : ℤ) :
    residue O ((u ^ n : Oˣ) : O) = residue O (u : O) ^ n := by
  rcases n with k | k
  · simp only [Int.ofNat_eq_coe, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  · rw [zpow_negSucc, zpow_negSucc]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_mul, Units.inv_mul, map_one]

private theorem res_ne {O : Type} [CommRing O] [IsLocalRing O] (u : Oˣ) : residue O (u : O) ≠ 0 :=
  (u.isUnit.map (residue O)).ne_zero

private theorem bar_mul_frobenius_fields {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (f h : G ℚ Ω →* (c.O)ˣ) (g : G ℚ Ω) : Raw.bar (f * h) g = Raw.bar f g * Raw.bar h g := by
  unfold Raw.bar
  rw [MonoidHom.mul_apply, Units.val_mul, map_mul]

private theorem bar_inv' {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (f : G ℚ Ω →* (c.O)ˣ) (g : G ℚ Ω) : Raw.bar f⁻¹ g = (Raw.bar f g)⁻¹ := by
  unfold Raw.bar
  rw [MonoidHom.inv_apply, ← zpow_neg_one, res_zpow, zpow_neg_one]

private theorem bar_pow' {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (f : G ℚ Ω →* (c.O)ˣ) (g : G ℚ Ω) (n : ℕ) : Raw.bar (f ^ n) g = Raw.bar f g ^ n := by
  unfold Raw.bar
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, map_pow]

theorem UpperTheory.V.Ws.barFacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → (-1 : ResidueField c.O) ≠ 1 ∧ (∀ (x : ResidueField c.O) (j : ℕ), x ^ l ^ j = 1 → x = 1) ∧ (∀ g, Raw.bar D.al g = Raw.bar D.ξ g) ∧ (∀ g, Raw.bar D.th g = Raw.bar D.ξ g * Raw.bar D.Psi g) ∧ (∀ g, Raw.bar D.Psi g = Raw.bar D.om g ^ D.e * Raw.bar D.ψ g) ∧ (∀ g, D.rbar g = 1 ↔ Raw.bar D.ξ g = 1 ∧ Raw.bar D.Psi g = 1) ∧ (∀ (T : Tower D) (w : ℤ × ℤ) (g : G T.F Ω), T.rb w g = Raw.bar D.ξ (resQ T.F g) ^ w.1 * Raw.bar D.Psi (resQ T.F g) ^ (if T.pr then -w.2 else w.2)) ∧ (∃ m : ℕ, l.Coprime m ∧ ∀ g, Raw.bar D.Psi g ^ m = 1) ∧ IsOpen {g | Raw.bar D.Psi g = 1} := by
  intro Ω _ _ _ l _ c D hD
  have hmax : ∀ x ∈ maximalIdeal c.O, residue c.O x = 0 := fun x hx => (residue_eq_zero_iff x).mpr hx
  obtain ⟨hchar, hfin⟩ := Gys.coefFacts c (ResidueField c.O) (residue c.O) hmax
  have hl2 : l ≠ 2 := hD.l_odd
  have hlp : l.Prime := Fact.out
  have hal : ∀ g, Raw.bar D.al g = Raw.bar D.ξ g := by
    intro g
    have e1 : D.al = chiO ℚ Ω l c.O * D.om⁻¹ * D.ξ := by
      unfold Raw.al
      rfl
    rw [e1, bar_mul_frobenius_fields, bar_mul_frobenius_fields, bar_inv', ← hD.om_bar g, mul_inv_cancel₀ (res_ne _), one_mul]
  have hth : ∀ g, Raw.bar D.th g = Raw.bar D.ξ g * Raw.bar D.Psi g := by
    intro g
    have e1 : D.th = D.al * D.Psi := by
      unfold Raw.th
      rfl
    rw [e1, bar_mul_frobenius_fields, hal]
  have hPsi : ∀ g, Raw.bar D.Psi g = Raw.bar D.om g ^ D.e * Raw.bar D.ψ g := by
    intro g
    have e1 : D.Psi = chiO ℚ Ω l c.O ^ D.e * D.ψ := by
      unfold Raw.Psi UpperTheory.V.Chr.Psi
      rfl
    rw [e1, bar_mul_frobenius_fields, bar_pow', hD.om_bar g]
  haveI : Finite (ResidueField c.O) := by
    rw [Set.range_eq_univ.mpr residue_surjective] at hfin
    exact Set.finite_univ_iff.mp hfin
  haveI := Fintype.ofFinite (ResidueField c.O)
  have hneg : (-1 : ResidueField c.O) ≠ 1 := by
    apply Ring.neg_one_ne_one_of_char_ne_two
    rw [ringChar.eq (ResidueField c.O) l]
    exact hl2
  have hfrob : ∀ (x : ResidueField c.O) (j : ℕ), x ^ l ^ j = 1 → x = 1 := by
    intro x j hx
    have h0 : (x - 1) ^ l ^ j = 0 := by
      rw [sub_pow_char_pow, hx, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero j hlp.ne_zero)).mp h0)
  have hr : ∀ g, D.rbar g = 1 ↔ Raw.bar D.ξ g = 1 ∧ Raw.bar D.Psi g = 1 := by
    intro g
    unfold Raw.rbar mapRep Raw.r0 diagRep
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    show (Matrix.diagonal fun i => ((D.ps i g : (c.O)ˣ) : c.O)).map (residue c.O) = 1 ↔ _
    rw [Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff]
    have h1 := hal g
    have h2 := hth g
    unfold Raw.bar at h1 h2 ⊢
    simp [Fin.forall_fin_succ, Raw.ps, h1, h2]
    constructor
    · rintro ⟨-, hp, hx⟩
      exact ⟨hx, hp⟩
    · rintro ⟨hx, hp⟩
      exact ⟨by rw [hx, hp, one_mul], hp, hx⟩
  have hrb : ∀ (T : Tower D) (w : ℤ × ℤ) (g : G T.F Ω), T.rb w g = Raw.bar D.ξ (resQ T.F g) ^ w.1 * Raw.bar D.Psi (resQ T.F g) ^ (if T.pr then -w.2 else w.2) := by
    intro T w g
    unfold Tower.rb
    simp only [Fr.rt, Tower.fr, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.coe_comp, Function.comp_apply]
    unfold chi
    generalize resQ T.F g = τ
    have e1 : D.th τ = D.al τ * D.Psi τ := by
      unfold Raw.th
      rfl
    have hinv : ∀ u : (c.O)ˣ, residue c.O ((u⁻¹ : (c.O)ˣ) : c.O) = (residue c.O (u : c.O))⁻¹ := fun u => by
      rw [← zpow_neg_one, res_zpow, zpow_neg_one]
    have hal' : residue c.O (D.al τ : c.O) = residue c.O (D.ξ τ : c.O) := hal τ
    have ha := res_ne (D.al τ)
    have hp := res_ne (D.Psi τ)
    unfold Raw.bar
    rw [← hal']
    cases T.pr <;> simp [lab, Raw.ps, e1, hinv, res_zpow, ha, hp, inv_zpow]
  have hm : ∃ m : ℕ, l.Coprime m ∧ ∀ g, Raw.bar D.Psi g ^ m = 1 := by
    refine ⟨Fintype.card (ResidueField c.O) - 1, ?_, fun g => ?_⟩
    · obtain ⟨n, -, hn⟩ := FiniteField.card (ResidueField c.O) l
      rw [hn]
      have h1 : Nat.Coprime (l ^ (n : ℕ)) (l ^ (n : ℕ) - 1) :=
        (Nat.coprime_self_sub_right (Nat.one_le_pow _ _ hlp.pos)).mpr (Nat.coprime_one_right _)
      exact Nat.Coprime.coprime_dvd_left (dvd_pow_self l n.ne_zero) h1
    · unfold Raw.bar
      exact FiniteField.pow_card_sub_one_eq_one _ (res_ne _)
  have hopen : IsOpen {g | Raw.bar D.Psi g = 1} := by
    have homT : IsOmT c D.om := by
      unfold IsOmT
      refine ⟨hD.om_pow, fun σ => ?_⟩
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact hD.om_bar σ
    have hom := ((omT Ω l c).2 D.om homT).2.2.2.1
    let H : Subgroup (G ℚ Ω) := ((Units.map (residue c.O : c.O →* ResidueField c.O)).comp D.Psi).ker
    have hset : {g | Raw.bar D.Psi g = 1} = (H : Set (G ℚ Ω)) := by
      ext g
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, H, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, Units.ext_iff, Units.coe_map, Units.val_one]
      rfl
    rw [hset]
    refine Subgroup.isOpen_mono (H₁ := D.om.ker ⊓ D.ψ.ker) ?_ (hom.inter hD.psi_open)
    intro g hg
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hg
    rw [MonoidHom.mem_ker] at h1 h2
    have : Raw.bar D.Psi g = 1 := by
      rw [hPsi]
      unfold Raw.bar
      rw [h1, h2, Units.val_one, map_one, one_pow, one_mul]
    rw [← SetLike.mem_coe, ← hset]
    exact this
  exact ⟨hneg, hfrob, hal, hth, hPsi, hr, hrb, hm, hopen⟩
end
