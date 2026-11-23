module

public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Formalism.PeriodIntegrals.Bundle006
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle171
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerUnitsFiniteModPowersAtLevel
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle174
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
noncomputable section

namespace GlobalTheory.EisM

theorem depleted_newform_prim : ∀ (k r : ℕ) (g : Newform k), 1 ≤ k → 2 ≤ r → ∃ χ : DirichletCharacter ℂ (g.M * (g.M * r) ^ 2), Prim k _ χ (fun n => if n.Coprime (g.M * r) then g.a n else 0) ∧ ∀ d : ℕ, d.Coprime (g.M * (g.M * r) ^ 2) → χ d = g.χ d := by
  intro k r g _ hr
  have hM := g.pos
  have hLpos : 0 < g.M * r := Nat.mul_pos hM (by omega)
  have hdvd : g.M ∣ g.M * (g.M * r) ^ 2 := dvd_mul_right _ _
  have hLN : g.M * r ∣ g.M * (g.M * r) ^ 2 := (dvd_pow_self _ two_ne_zero).mul_left g.M
  have hcop : ∀ n : ℕ, n.Coprime (g.M * (g.M * r) ^ 2) ↔ n.Coprime (g.M * r) := by
    intro n
    constructor
    · intro h; exact h.coprime_dvd_right hLN
    · intro h
      exact Nat.Coprime.mul_right (h.coprime_dvd_right (dvd_mul_right _ _)) (Nat.Coprime.pow_right 2 h)
  set χ : DirichletCharacter ℂ (g.M * (g.M * r) ^ 2) := DirichletCharacter.changeLevel hdvd g.χ with hχdef
  have hχZ : ∀ d : ℤ, IsCoprime d ((g.M * (g.M * r) ^ 2 : ℕ) : ℤ) → ch χ d = g.χ (d : ZMod g.M) := by
    intro d hd
    exact DirichletCharacter.changeLevel_eq_cast_of_dvd' g.χ hdvd hd
  have hχN : ∀ d : ℕ, d.Coprime (g.M * (g.M * r) ^ 2) → χ d = g.χ d := by
    intro d hd
    have := hχZ d (Nat.isCoprime_iff_coprime.2 hd)
    simpa [ch] using this
  refine ⟨χ, ?_, hχN⟩

  have hcf0 := ((gamma1_char_elementary k g.M g.χ hM).2 g.f g.char).2
  have htw := GlobalTheory.T.isCuspFormCoeffSeq_dirichletTwist_level_mul_sq k g.M (g.M * r) g.χ (1 : DirichletCharacter ℂ (g.M * r)) (coef g.f) hLpos hcf0
  have hseq : (fun n : ℕ => (1 : DirichletCharacter ℂ (g.M * r)) n * coef g.f n) =
      (fun n => if n.Coprime (g.M * r) then g.a n else 0) := by
    funext n
    by_cases h : n.Coprime (g.M * r)
    · rw [if_pos h, MulChar.one_apply ((ZMod.isUnit_iff_coprime n _).2 h), one_mul]; rfl
    · rw [if_neg h, MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n _).1 hu)), zero_mul]
  rw [hseq] at htw
  have hlin := (GlobalTheory.T.modularFormCoeffSeq_linear_structure k (g.M * (g.M * r) ^ 2) (fun d => ch g.χ d * ch (1 : DirichletCharacter ℂ (g.M * r)) d ^ 2)).2.2.2.1
    (ch χ) _ ?_ htw.1
  swap
  · intro d hd
    have hdL : IsCoprime d ((g.M * r : ℕ) : ℤ) := hd.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hLN)
    rw [hχZ d hd]
    simp only [ch]
    rw [← ZMod.coe_unitOfIsCoprime d hdL, MulChar.one_apply_coe, one_pow, mul_one]
  refine ⟨⟨hlin, htw.2⟩, ?_, ?_, ?_⟩
  · have h1 : (1 : ℕ).Coprime (g.M * r) := Nat.coprime_one_left _
    simp only [if_pos h1]
    exact g.one
  · intro n hn
    have : ¬ n.Coprime (g.M * r) := fun h => hn ((hcop n).2 h)
    simp only [if_neg this]
  · intro q hq hqN
    have hqL : q.Coprime (g.M * r) := (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hqN (h.trans hLN))
    have hqM : ¬ q ∣ g.M := fun h => hqN (h.trans hdvd)
    have hchq : ch χ (q : ℤ) = g.χ (q : ZMod g.M) := by
      rw [hχZ (q : ℤ) (Nat.isCoprime_iff_coprime.2 ((hcop q).2 hqL))]; simp
    have heig := g.eig q hq hqM
    funext n
    simp only [To, Vo, hchq, if_pos hqL]
    by_cases hn : n.Coprime (g.M * r)
    · have hn1 : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0; rw [Nat.coprime_zero_left] at hn; nlinarith
        · exact h0
      have hqn : (q * n).Coprime (g.M * r) := Nat.Coprime.mul_left hqL hn
      rw [if_pos hqn, if_pos hn]
      have e := heig n hn1
      by_cases hd : q ∣ n
      · have hnq : (n / q).Coprime (g.M * r) := hn.coprime_dvd_left (Nat.div_dvd_of_dvd hd)
        rw [if_pos hd, if_pos hnq]
        rw [if_pos hd] at e
        exact e
      · rw [if_neg hd]
        rw [if_neg hd] at e
        exact e
    · have hqn : ¬ (q * n).Coprime (g.M * r) := fun h => hn (Nat.Coprime.coprime_mul_left h)
      rw [if_neg hqn, if_neg hn, mul_zero]
      by_cases hd : q ∣ n
      · have hnq : ¬ (n / q).Coprime (g.M * r) := by
          intro h
          apply hn
          rw [← Nat.mul_div_cancel' hd]
          exact Nat.Coprime.mul_left hqL h
        rw [if_pos hd, if_neg hnq]; simp
      · rw [if_neg hd]; simp

end GlobalTheory.EisM

end
end

section

noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.ZCalc

variable {G : Type} [Group G] [Fintype G]

theorem character_inv (V : FDRep ℂ G) (t : G) : V.character t⁻¹ = (starRingEnd ℂ) (V.character t) := by
  let b := Module.finBasis ℂ V
  have htr : ∀ s, V.character s = (LinearMap.toMatrix b b (V.ρ s)).trace := fun s =>
    LinearMap.trace_eq_matrix_trace ℂ b _
  rw [htr, htr]
  refine Formalism.L2.DIV.trace_inv_of_pow_eq_one _ _ (N := Fintype.card G) Fintype.card_ne_zero ?_ ?_
  · rw [LinearMap.toMatrix_pow, ← map_pow, pow_card_eq_one, map_one, LinearMap.toMatrix_one]
  · rw [← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel, map_one, LinearMap.toMatrix_one]

theorem op_zc (V W : FDRep ℂ G) :
    op W.ρ (zc V.character) = PI.CharIdem.act W (PI.CharIdem.charIdem V) := by
  rw [PI.CharIdemW.act_charIdem]
  simp only [op, zc, FDRep.char_one]

theorem conv_zc_of_scalar (χ : G → ℂ) (W : FDRep ℂ G) (c : ℂ) (h : op W.ρ (zc χ) = c • 1) (x : G) :
    conv (zc χ) (zc W.character) x = c * zc W.character x := by
  have h1 : ∑ y, zc χ y * W.character (y * x⁻¹) = c * W.character x⁻¹ := by
    have h2 : LinearMap.trace ℂ W (op W.ρ (zc χ) * W.ρ x⁻¹) = c * W.character x⁻¹ := by
      rw [h, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]; rfl

    rw [← h2, op, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, ← map_mul]; rfl
  have h3 : ∀ y, zc χ y * zc W.character (y⁻¹ * x) =
      W.character 1 / (Fintype.card G : ℂ) * (zc χ y * W.character (y * x⁻¹)) := by
    intro y
    have : W.character (y⁻¹ * x)⁻¹ = W.character (y * x⁻¹) := by
      rw [mul_inv_rev, inv_inv, FDRep.char_mul_comm]
    rw [show zc W.character (y⁻¹ * x) = W.character 1 / (Fintype.card G : ℂ) * W.character (y⁻¹ * x)⁻¹ from rfl, this]
    ring
  rw [conv, Finset.sum_congr rfl fun y _ => h3 y, ← Finset.mul_sum, h1,
    show zc W.character x = W.character 1 / (Fintype.card G : ℂ) * W.character x⁻¹ from rfl]
  ring

theorem op_conv_eq {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (a b : G → ℂ) :
    op ρ (conv a b) = op ρ a * op ρ b := by
  simp only [op, conv, Finset.sum_smul, Finset.sum_mul_sum, smul_mul_smul_comm, ← map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine (Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_).symm
  simp

theorem rk_eq_trace {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M)
    (e : G → ℂ) (he : conv e e = e) : (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by
  have hi : IsIdempotentElem (op ρ e) := by
    rw [IsIdempotentElem, ← op_conv_eq, he]
  have hp := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace

  rw [rk, ← hp, op, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem zc_calc : ∀ (G : Type) [Group G] [Fintype G], ∀ (V : FDRep ℂ G) [CategoryTheory.Simple V], IsProj (zc V.character) ∧ (∀ a : G → ℂ, conv (zc V.character) a = conv a (zc V.character)) ∧ (∀ (W : FDRep ℂ G) [CategoryTheory.Simple W], V.character ≠ W.character → conv (zc V.character) (zc W.character) = 0) ∧ ∀ e : G → ℂ, conv e e = e → conv (zc V.character) e 1 = (Module.finrank ℂ V : ℂ) * (rk V.ρ e : ℂ) / (Fintype.card G : ℂ) := by
  intro G _ _ V hV
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · funext x
    have h := (PI.CharIdemW.scalar G V V hV hV).1 ⟨CategoryTheory.Iso.refl V⟩
    rw [conv_zc_of_scalar _ V 1 (by rw [op_zc, h, one_smul]), one_mul]
  · intro x
    simp only [zc, map_mul, map_div₀, FDRep.char_one, map_natCast]
    rw [character_inv V x⁻¹]
  · intro a
    funext x
    simp only [conv]
    refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x)) _ _ fun y => ?_
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulRight, zc]
    have : V.character ((y⁻¹ * x)⁻¹ * x)⁻¹ = V.character y⁻¹ := by
      rw [← FDRep.char_conj V y⁻¹ x⁻¹]
      congr 1
      group
    rw [this, mul_comm]
  · intro W hW hne
    funext x
    have h := (PI.CharIdemW.scalar G V W hV hW).2 ⟨fun i => hne (FDRep.char_iso i)⟩
    rw [conv_zc_of_scalar _ W 0 (by rw [op_zc, h, zero_smul]), zero_mul]
    rfl
  · intro e he
    rw [rk_eq_trace _ e he, conv, Finset.mul_sum, Finset.sum_div]
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun y => ?_
    simp only [Equiv.inv_apply, zc, mul_one, FDRep.char_one]
    rw [show LinearMap.trace ℂ V (V.ρ y⁻¹) = V.character y⁻¹ from rfl]
    ring

end GlobalTheory.BadShare.ZCalc
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.UniqRoot

theorem exists_finite_field {F E : Type} [Field F] [Field E] [Algebra F E] (t : E) (A : Set E) (hfin : A.Finite)
    (hA : ∀ a ∈ A, IsAlgebraic (IntermediateField.adjoin F {t}) a) :
    ∃ (L : IntermediateField F E) (ht : t ∈ L), A ⊆ L ∧
      FiniteDimensional (IntermediateField.adjoin F {(⟨t, ht⟩ : L)}) L := by
  let K₀ : IntermediateField F E := IntermediateField.adjoin F {t}
  let L' : IntermediateField K₀ E := IntermediateField.adjoin K₀ A
  haveI : Finite A := hfin
  have hL' : FiniteDimensional K₀ L' := IntermediateField.finiteDimensional_adjoin fun a ha => (hA a ha).isIntegral
  let L : IntermediateField F E := L'.restrictScalars F
  have hK : ∀ x : K₀, (x : E) ∈ L := fun x => L'.algebraMap_mem x
  have ht : t ∈ L := hK ⟨t, IntermediateField.mem_adjoin_simple_self F t⟩
  refine ⟨L, ht, fun a ha => IntermediateField.subset_adjoin K₀ A ha, ?_⟩
  let K' : IntermediateField F L := IntermediateField.adjoin F {(⟨t, ht⟩ : L)}
  have hmap : K'.map L.val = K₀ := by
    simp only [K', K₀, IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ x : K₀, (⟨x, hK x⟩ : L) ∈ K' := by
    intro x
    have hx : (x : E) ∈ K'.map L.val := by rw [hmap]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = ⟨x, hK x⟩ := Subtype.ext hyx
    exact this ▸ hy
  let φ : K₀ →+* K' :=
    { toFun := fun x => ⟨⟨x, hK x⟩, hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra K₀ K' := φ.toAlgebra
  letI : Algebra K₀ L := (inferInstance : Algebra K₀ L')
  haveI : Module.Finite K₀ L := hL'
  haveI : IsScalarTower K₀ K' L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite K₀ K' L

theorem valuation_eq_one_iff' {K : Type} [Field K] (W : ValuationSubring K) (x : K) :
    W.valuation x = 1 ↔ x ≠ 0 ∧ x ∈ W ∧ x⁻¹ ∈ W := by
  rw [← W.valuation_le_one_iff, ← W.valuation_le_one_iff, map_inv₀]
  constructor
  · intro h
    refine ⟨?_, h.le, by rw [h, inv_one]⟩
    rintro rfl
    simp at h
  · rintro ⟨h0, h1, h2⟩
    have hp : 0 < W.valuation x := zero_lt_iff.2 ((map_ne_zero _).2 h0)
    exact le_antisymm h1 ((inv_le_one₀ hp).1 h2)

theorem gauss_comap {F E : Type} [Field F] [Field E] [Algebra F E] {t : E} (L : IntermediateField F E) (ht : t ∈ L)
    {V : ValuationSubring F} {W : ValuationSubring E} (h : Gauss t V W) :
    Gauss (⟨t, ht⟩ : L) V (W.comap (algebraMap L E)) := by
  refine ⟨fun a => ?_, fun P hP hu => ?_⟩
  · rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact h.1 a
  · have h1 := (valuation_eq_one_iff' _ _).1 (h.2 P hP hu)
    have e : algebraMap L E (Polynomial.aeval (⟨t, ht⟩ : L) P) = Polynomial.aeval t P :=
      (Polynomial.aeval_algHom_apply L.val (⟨t, ht⟩ : L) P).symm
    rw [valuation_eq_one_iff', ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀, e]
    refine ⟨fun h0 => h1.1 ?_, h1.2⟩
    rw [← e, h0, map_zero]

theorem transcendental_j {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) :
    Transcendental Ω X.jK := by
  intro h
  have hd := IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible h.isIntegral)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one Ω X.jK hd
  have h1 := X.j_exp.1
  rw [← hc, AlgHom.commutes] at h1
  simp [HahnSeries.algebraMap_apply', HahnSeries.coeff_single] at h1

theorem gauss_unique_root : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring (AlgebraicClosure X.K), Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₁ → Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₂ → ∀ (θ : AlgebraicClosure X.K) (f : X.Kˣ), f ∈ X.Un l → Lev X M₀ f → θ ^ l = algebraMap X.K (AlgebraicClosure X.K) (f : X.K) → ∀ x ∈ IntermediateField.adjoin (levF X M₀) {θ}, x ∈ W₁ ↔ x ∈ W₂ := by
  classical
  intro Ω _ _ _ ε X hj l M₀ hl hM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have halgΩ : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : @Algebra.IsAlgebraic ℚ Ω _ _ DivisionRing.toRatAlgebra := by
    convert halgΩ
    exact Subsingleton.elim _ _
  obtain ⟨R, hR⟩ := GlobalTheory.KZ.FinLev.finite_mod_powers ε X ε.injective hj M₀ l hM hl.pos
  obtain ⟨T, -, hT⟩ := GlobalTheory.T.exists_finset_span_principalCongruenceLevel_functions ε X hj M₀ hM
  let E := AlgebraicClosure X.K
  let ι : X.K →ₐ[Ω] E := IsScalarTower.toAlgHom Ω X.K E
  let t : E := algebraMap X.K E X.jK
  have hmap : (IntermediateField.adjoin Ω {X.jK}).map ι = IntermediateField.adjoin Ω {t} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ c : IntermediateField.adjoin Ω {X.jK}, ι c ∈ IntermediateField.adjoin Ω {t} :=
    fun c => hmap ▸ ⟨c, c.2, rfl⟩
  have halg : ∀ f : X.K, IsAlgebraic (IntermediateField.adjoin Ω {t}) (algebraMap X.K E f) := by
    intro f
    let φ : IntermediateField.adjoin Ω {X.jK} →+* IntermediateField.adjoin Ω {t} :=
      (ι.toRingHom.comp (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K)).codRestrict
        (IntermediateField.adjoin Ω {t}) hmem
    exact ((X.alg_j f).isIntegral.map_of_comp_eq φ (algebraMap X.K E) (RingHom.ext fun _ => rfl)).isAlgebraic
  let A : Set E := algebraMap X.K E '' (T : Set X.K) ∪
    ⋃ r ∈ (R : Set X.Kˣ), {y : E | y ^ l = algebraMap X.K E (r : X.K)}
  have hAfin : A.Finite := by
    refine (T.finite_toSet.image _).union (R.finite_toSet.biUnion fun r _ => ?_)
    refine (Polynomial.nthRoots l (algebraMap X.K E (r : X.K))).toFinset.finite_toSet.subset fun y hy => ?_
    simpa [Polynomial.mem_nthRoots hl.pos] using hy
  have hAalg : ∀ a ∈ A, IsAlgebraic (IntermediateField.adjoin Ω {t}) a := by
    rintro a (⟨f, -, rfl⟩ | ha)
    · exact halg f
    · simp only [Set.mem_iUnion, Set.mem_setOf_eq] at ha
      obtain ⟨r, -, hr⟩ := ha
      exact IsAlgebraic.of_pow hl.pos (hr ▸ halg r)
  obtain ⟨L, ht, hAL, hfin⟩ := exists_finite_field (F := Ω) t A hAfin hAalg
  have htr : Transcendental Ω (⟨t, ht⟩ : L) := by
    intro h
    have h1 : IsAlgebraic Ω (ι X.jK) := h.algHom L.val
    exact transcendental_j X ((isAlgebraic_algHom_iff ι ι.toRingHom.injective).1 h1)
  obtain ⟨S, hS⟩ := GlobalTheory.T.gauss_valuationSubring_unique_away_finset (F := Ω) (⟨t, ht⟩ : L) htr hfin
  have hlev : ∀ f : X.K, Lev X M₀ f → algebraMap X.K E f ∈ L := by
    intro f hf
    have hsp := hT f hf
    clear hf
    induction hsp using Submodule.span_induction with
    | mem x hx => exact hAL (Or.inl ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact L.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact L.add_mem hx hy
    | smul c x _ hx =>
      have hc : ι c ∈ L := (IntermediateField.adjoin_simple_le_iff.2 ht) (hmem c)
      have e : algebraMap X.K E (c • x) = ι c * algebraMap X.K E x := by
        rw [IntermediateField.smul_def, smul_eq_mul, map_mul]
        rfl
      rw [e]
      exact L.mul_mem hc hx
  have hlevF : levF X M₀ ≤ L := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hlev f hf
  refine ⟨S, fun q hq hqS V hV W₁ W₂ h₁ h₂ θ f hf hfl hθ x hx => ?_⟩
  have hW := hS q hq hqS V hV _ _ (gauss_comap L ht h₁) (gauss_comap L ht h₂)
  obtain ⟨r, hr, g, hg, c, hc, hfe⟩ := hR f hf hfl
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hl.pos
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow hl.ne_zero] at hd
    exact hc hd.symm
  let u : E := algebraMap X.K E (g : X.K) * algebraMap Ω E d
  have hu0 : u ≠ 0 := mul_ne_zero ((map_ne_zero _).2 g.ne_zero) ((map_ne_zero _).2 hd0)
  have huL : u ∈ L := L.mul_mem (hlev g hg) (L.algebraMap_mem d)
  have hy : (θ / u) ^ l = algebraMap X.K E (r : X.K) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ hu0), hθ, hfe, mul_pow, ← map_pow, ← map_pow, hd, map_mul, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_assoc]
  have hθL : θ ∈ L := by
    have h1 : θ / u ∈ L := hAL (Or.inr (Set.mem_biUnion (Finset.mem_coe.2 hr) hy))
    have := L.mul_mem h1 huL
    rwa [div_mul_cancel₀ _ hu0] at this
  have hxL : x ∈ L := by
    have hle : IntermediateField.adjoin (levF X M₀) {θ} ≤ IntermediateField.extendScalars hlevF :=
      IntermediateField.adjoin_simple_le_iff.2 hθL
    exact hle hx
  have := SetLike.ext_iff.1 hW ⟨x, hxL⟩
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at this
  exact this

end GlobalTheory.KZ.ES.UniqRoot
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.kronecker_congruence_modularFunctionTower_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ W : ValuationSubring X.K, Dom X V W → ∀ (k : ℕ) (f : X.K), f ≠ 0 → Lev X (M₀ * l ^ k) f → (∃ c : Ω, W.valuation (algebraMap Ω X.K c * Nq X (M₀ * l ^ k) q f / X.gal s f - 1) < 1) ∧ ∃ c : Ω, W.valuation (algebraMap Ω X.K c * X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f / (X.gal s.symm f) ^ q - 1) < 1 := by
  first | exact @GlobalTheory.KZ.ES.kron_cong_level | exact GlobalTheory.KZ.ES.kron_cong_level | (intros; apply GlobalTheory.KZ.ES.kron_cong_level <;> assumption)
end

section

namespace GlobalTheory.ScalarNormBound

variable {l : ℕ} [Fact (Nat.Prime l)]

theorem norm_smul_le_self (a : ℤ_[l]) (y : PadicAlgCl l) : ‖a • y‖ ≤ ‖y‖ := by
  have ha : ‖(a : ℚ_[l])‖ ≤ 1 := a.2
  have hs : a • y = (a : ℚ_[l]) • y := (algebraMap_smul ℚ_[l] a y).symm
  rw [hs, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg y) ha

theorem exists_bound (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [Module.Finite ℤ_[l] O] :
    ∃ C : ℝ, ∀ y : O, ‖(y : PadicAlgCl l)‖ ≤ C := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] O).FG)
  have hnn : ∀ z ∈ s, 0 ≤ ‖((z : O) : PadicAlgCl l)‖ := fun z _ => norm_nonneg _
  refine ⟨∑ z ∈ s, ‖((z : O) : PadicAlgCl l)‖, fun y => ?_⟩
  have hy : y ∈ Submodule.span ℤ_[l] (s : Set O) := hs ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact Finset.single_le_sum hnn hx
  | zero => simpa using Finset.sum_nonneg hnn
  | add x z _ _ hx hz =>
    have e : ((x + z : O) : PadicAlgCl l) = (x : PadicAlgCl l) + (z : PadicAlgCl l) := rfl
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hz)
  | smul a x _ hx =>
    have e : ((a • x : O) : PadicAlgCl l) = a • (x : PadicAlgCl l) := rfl
    rw [e]
    exact (norm_smul_le_self a _).trans hx

theorem norm_le_one : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) (x : ↥(UpperTheory.V.HV.Coef.O c)), ‖(↑x : PadicAlgCl l)‖ ≤ (1 : ℝ) := by
  intro l _ c x
  obtain ⟨C, hC⟩ := exists_bound (UpperTheory.V.HV.Coef.O c)
  by_contra h
  rw [not_le] at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have hb := hC (x ^ n)
  have e : ‖((x ^ n : UpperTheory.V.HV.Coef.O c) : PadicAlgCl l)‖ = ‖(x : PadicAlgCl l)‖ ^ n := by
    rw [SubmonoidClass.coe_pow, norm_pow]
  linarith

end GlobalTheory.ScalarNormBound
end

section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

namespace GlobalTheory.Glob.IntegralWittCoefficients

theorem isCurveIdeal_top (D : D7) : IsCurveIdeal D ⊤ :=
  ⟨top_ne_bot, by simp⟩

end GlobalTheory.Glob.IntegralWittCoefficients
end
end
