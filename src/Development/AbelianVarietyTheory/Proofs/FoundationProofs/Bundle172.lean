module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle093
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle069
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle135
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle121
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle161
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle162
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle159
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle096

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.coef_qExpansionFunctionUpperHalfPlane : ∀ a : ℕ → ℂ, PolyB a → ∀ n, coef (qs a) n = a n := by
  first | exact @GlobalTheory.EisM.coef_qs | exact GlobalTheory.EisM.coef_qs | (intros; apply GlobalTheory.EisM.coef_qs <;> assumption)
end

section

noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt.QDer

section General

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

theorem isDerOn_mono {B B' : Subalgebra A S} {D : S → M} (h : IsDerOn B D) (hle : B' ≤ B) :
    IsDerOn B' D :=
  ⟨fun x hx y hy => h.add x (hle hx) y (hle hy), fun x hx y hy => h.mul x (hle hx) y (hle hy),
    h.alg⟩

theorem isDerOn_sub {B : Subalgebra A S} {D₁ D₂ : S → M} (h₁ : IsDerOn B D₁) (h₂ : IsDerOn B D₂) :
    IsDerOn B (fun x => D₁ x - D₂ x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    simp only [h₁.add x hx y hy, h₂.add x hx y hy]
    abel
  · intro x hx y hy
    simp only [h₁.mul x hx y hy, h₂.mul x hx y hy, smul_sub]
    abel
  · intro a
    simp [h₁.alg a, h₂.alg a]

theorem isDerOn_pow {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B)
    {n : ℕ} (hn : 1 ≤ n) : D (x ^ n) = ((n : S) * x ^ (n - 1)) • D x := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, h.mul _ (pow_mem hx _) _ hx, ih (by omega), smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

end General

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_succ_pow (T : Tower p Ω) (m : ℕ) : zS T (m + 1) ^ p = zS T m :=
  Subtype.ext (by simp [zS, T.ζpow])

theorem qS_succ_pow (T : Tower p Ω) (m : ℕ) : qS T (m + 1) ^ p = qS T m :=
  Subtype.ext (by simp [qS, T.qpow])

theorem zS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

theorem qS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

theorem levelAlg_le_succ (T : Tower p Ω) (m : ℕ) : levelAlg T m ≤ levelAlg T (m + 1) := by
  refine Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · rw [← zS_succ_pow]; exact pow_mem (zS_mem_levelAlg T _) _
  · rw [← qS_succ_pow]; exact pow_mem (qS_mem_levelAlg T _) _

theorem towerAlg_le_iSup (T : Tower p Ω) : towerAlg T ≤ ⨆ m, levelAlg T (m + 1) := by
  refine Algebra.adjoin_le ?_
  rintro x ((⟨m, rfl⟩ | ⟨m, rfl⟩))
  · exact le_iSup (fun k => levelAlg T (k + 1)) m (levelAlg_le_succ T m (zS_mem_levelAlg T m))
  · exact le_iSup (fun k => levelAlg T (k + 1)) m (levelAlg_le_succ T m (qS_mem_levelAlg T m))

theorem exists_level (hC : IsClo p Ω) (T : Tower p Ω) (n : ℕ) (hn : 1 ≤ n) :
    ∃ D : integralClosure (O0 p) Ω → Frac p Ω, IsDerOn (levelAlg T n) D ∧ D (zS T n) = 0 ∧
      D (qS T n) = Submodule.Quotient.mk (T.qq n / (p : Ω) ^ n) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap hC.inj
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  refine GlobalTheory.T.exists_derivation_towerLevelAlgebra_prescribed p Ω hC T n hn (Frac p Ω) 0 _ (smul_zero _) ?_
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p), ?_⟩
  have hpn : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  rw [Algebra.linearMap_apply, ← IsScalarTower.algebraMap_apply, Subalgebra.smul_def, smul_eq_mul]
  have key : (((p : integralClosure (O0 p) Ω) ^ n * qS T n ^ (p ^ n - 1) :
      integralClosure (O0 p) Ω) : Ω) = (p : Ω) ^ n * T.qq n ^ (p ^ n - 1) := by
    simp [qS]
  rw [key, ← GlobalTheory.AlmostEt.qq_pow T n]
  field_simp
  rw [pow_sub_one_mul hpn]

theorem smul_mk_eq (hC : IsClo p Ω) (T : Tower p Ω) (m : ℕ) :
    ((p : integralClosure (O0 p) Ω) * qS T (m + 1) ^ (p - 1)) •
        (Submodule.Quotient.mk (T.qq (m + 1) / (p : Ω) ^ (m + 1)) : Frac p Ω) =
      Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap hC.inj
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpn : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  rw [Subalgebra.smul_def, smul_eq_mul]
  have key : (((p : integralClosure (O0 p) Ω) * qS T (m + 1) ^ (p - 1) :
      integralClosure (O0 p) Ω) : Ω) = (p : Ω) * T.qq (m + 1) ^ (p - 1) := by
    simp [qS]
  rw [key, ← T.qpow m, ← pow_sub_one_mul hpn (T.qq (m + 1)), pow_succ]
  field_simp

theorem exists_qDer (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (hC : IsClo p Ω) (T : Tower p Ω) :
    ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω, IsDerOn (towerAlg T) D ∧
      ∀ m : ℕ, D (zS T m) = 0 ∧ D (qS T m) = Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  choose Dl hDl hz hq using fun m : ℕ => exists_level hC T (m + 1) (by omega)

  have hz' : ∀ m, Dl m (zS T m) = 0 := fun m => by
    rw [← zS_succ_pow, isDerOn_pow (hDl m) (zS_mem_levelAlg T _) hp1, hz, smul_zero]
  have hq' : ∀ m, Dl m (qS T m) = Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := fun m => by
    rw [← qS_succ_pow, isDerOn_pow (hDl m) (qS_mem_levelAlg T _) hp1, hq, smul_mk_eq hC T m]

  have hcomp : ∀ m, ∀ x ∈ levelAlg T (m + 1), Dl (m + 1) x = Dl m x := by
    intro m x hx
    have hE := isDerOn_sub (isDerOn_mono (hDl (m + 1)) (levelAlg_le_succ T (m + 1))) (hDl m)
    have hspan := GlobalTheory.T.derivationOn_adjoin_mem_span_image (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω) {zS T (m + 1), qS T (m + 1)}
      _ hE x hx
    have h1 : Dl (m + 1) (zS T (m + 1)) - Dl m (zS T (m + 1)) = 0 := by rw [hz' (m + 1), hz m, sub_zero]
    have h2 : Dl (m + 1) (qS T (m + 1)) - Dl m (qS T (m + 1)) = 0 := by rw [hq' (m + 1), hq m, sub_self]
    simp only [Set.image_insert_eq, Set.image_singleton, h1, h2, Set.insert_eq_of_mem,
      Set.mem_singleton_iff, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hspan
    exact sub_eq_zero.1 hspan
  have hmono : Monotone (fun m => levelAlg T (m + 1)) :=
    monotone_nat_of_le_succ fun m => levelAlg_le_succ T (m + 1)
  obtain ⟨D, hD, hag⟩ := GlobalTheory.T.exists_derivationOn_iSup_of_compatible (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
    (fun m => levelAlg T (m + 1)) hmono Dl hDl hcomp
  refine ⟨D, isDerOn_mono hD (towerAlg_le_iSup T), fun m => ⟨?_, ?_⟩⟩
  · rw [hag m _ (levelAlg_le_succ T m (zS_mem_levelAlg T m)), hz']
  · rw [hag m _ (levelAlg_le_succ T m (qS_mem_levelAlg T m)), hq']

end GlobalTheory.AlmostEt.QDer
end
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

namespace GlobalTheory.GeoFix

theorem geofix : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (k : ℕ) (o : Ω), IsInt (p := p) o → (∀ g ∈ (Ggeo p Ω ⊓ Gn T n), g o = o) → ∃ (c : ℤ → Ω) (x x' : Ω), Ev ψ c x x' ∧ Cong (p := p) k o x := by
  intro p _ Ω _ _ hc T n ψ h k o ho hfix

  let F : Subfield Ω :=
    { carrier := {y | ∃ (N : Ω) (D : O0 p), InR ψ N ∧ D ≠ 0 ∧ y * ψ D = N}
      zero_mem' := ⟨0, 1, inR_zero ψ, one_ne_zero, by simp⟩
      one_mem' := ⟨ψ 1, 1, inR_psi ψ 1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro a b ⟨N, D, hN, hD, ha⟩ ⟨N', D', hN', hD', hb⟩
        exact ⟨N * ψ D' + N' * ψ D, D * D', inR_add (inR_mul hN (inR_psi ψ D')) (inR_mul hN' (inR_psi ψ D)),
          mul_ne_zero hD hD', by rw [map_mul, ← ha, ← hb]; ring⟩
      mul_mem' := by
        rintro a b ⟨N, D, hN, hD, ha⟩ ⟨N', D', hN', hD', hb⟩
        exact ⟨N * N', D * D', inR_mul hN hN', mul_ne_zero hD hD', by rw [map_mul, ← ha, ← hb]; ring⟩
      neg_mem' := by
        rintro a ⟨N, D, hN, hD, ha⟩
        exact ⟨-N, D, inR_neg hN, hD, by rw [neg_mul, ha]⟩
      inv_mem' := by
        rintro a ⟨N, D, hN, hD, ha⟩
        by_cases ha0 : a = 0
        · rw [ha0, inv_zero]
          exact ⟨0, 1, inR_zero ψ, one_ne_zero, by simp⟩
        · have hψD : ψ D ≠ 0 := fun h0 => hD (h.inj (by rw [h0, map_zero]))
          have hN0 : N ≠ 0 := by rw [← ha]; exact mul_ne_zero ha0 hψD
          obtain ⟨N', D', hN', hD', hNN⟩ := GlobalTheory.T.exists_combination_mul_eq_reparametrization_image p Ω hc T n ψ h N hN hN0
          refine ⟨ψ D * N', D', inR_mul (inR_psi ψ D) hN', hD', ?_⟩
          rw [← hNN, ← ha]
          field_simp }
  have hF1 : ∀ c : O0 p, algebraMap (O0 p) Ω c ∈ F := by
    intro c
    have hmem : algebraMap (O0 p) Ω c ∈ ψ.range := by
      rw [h.rng]; exact Subalgebra.algebraMap_mem _ c
    obtain ⟨c', hc'⟩ := hmem
    exact ⟨ψ c', 1, inR_psi ψ c', one_ne_zero, by rw [map_one, mul_one, hc']⟩
  have hF2 : ∀ x : Ω, IsAlgZp p x → x ∈ F := by
    intro x hx
    obtain ⟨D, hD, hxD⟩ := exists_inR_of_isAlgZp hc h hx
    exact ⟨x * ψ D, D, hxD, hD, rfl⟩
  have hF3 : T.qq n ∈ F := ⟨ψ (qO p), 1, inR_psi ψ _, one_ne_zero, by rw [map_one, mul_one, h.par]⟩
  obtain ⟨N, D, hN, hD, hoD⟩ := GlobalTheory.T.mem_subfield_of_fixed_by_geometric_tower_galois p Ω hc T n F hF1 hF2 hF3 o hfix

  obtain ⟨_, hdvr, hirr⟩ := completed_laurent_isDVR p
  obtain ⟨v, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hD hirr
  have hN1 : InR ψ (N * ψ (↑u⁻¹ : O0 p)) := inR_mul hN (inR_psi ψ _)
  have hpo : (p : Ω) ^ v * o = N * ψ (↑u⁻¹ : O0 p) := by
    rw [← hoD, hu, map_mul, map_pow, map_natCast]
    have : ψ (↑u : O0 p) * ψ (↑u⁻¹ : O0 p) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    linear_combination (-(↑p ^ v * o)) * this
  obtain ⟨d, e, b, he, hNe⟩ := hN1
  obtain ⟨a, z, hz, hza⟩ := GlobalTheory.T.exists_laurentSeries_sum_congruent_mod_p_pow p Ω T n ψ h d e b (fun t => (he t).1) (v + k)
  have hsum : ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) = (p : Ω) ^ v * (o - (p : Ω) ^ k * z) := by
    rw [← hNe] at hza
    rw [pow_add] at hza
    linear_combination -hpo - hza
  have hpi : IsInt (p := p) ((p : Ω) ^ k) := by
    rw [IsInt, ← map_natCast (algebraMap (O0 p) Ω), ← map_pow]; exact isIntegral_algebraMap
  have ho' : IsInt (p := p) (o - (p : Ω) ^ k * z) := IsIntegral.sub ho (IsIntegral.mul hpi hz)
  obtain ⟨c, x', hEv⟩ := GlobalTheory.T.integral_of_expansionSum_eq_primePow_mul_isEval p Ω hc T n ψ h d e a he v _ ho' hsum
  exact ⟨c, _, x', hEv, z, hz, by ring⟩

end GlobalTheory.GeoFix
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.potentialCocycleDehomogenised_laws : ∀ (w N l : ℕ), 0 < N → 0 < l → (∀ F ∈ Pot ℂ w (Gam N l), cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w ∧ (∀ γ : GlobalTheory.HeckeFamilyMatrices.Lev N l, ∀ τ ∈ Hs, deh (slP ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ) = cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F γ) ∧ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w → F ∈ Triv ℂ w (Gam N l))) ∧ (∀ F G, cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (F + G) = cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F + cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) G) ∧ (∀ (c : ℂ) F, cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (c • F) = c • cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  first | exact @GlobalTheory.KZ.cocP_laws | exact GlobalTheory.KZ.cocP_laws | (intros; apply GlobalTheory.KZ.cocP_laws <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.binaryForm_coeff_of_gamma1CapGamma0_invariant : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → ∀ (N w : ℕ) (b : X.Fn l) (c : Fin (w + 1) → X.Khat l), (∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i) → ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b → ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k) := by
  first | exact @GlobalTheory.KZ.H3.coef_of_inv | exact GlobalTheory.KZ.H3.coef_of_inv | (intros; apply GlobalTheory.KZ.H3.coef_of_inv <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.isKummerCharacterAtLevel_integral_matrix_conj : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), 0 < m.det → Kum X l n x χ → Kum X l n (X.kmap l (X.sl (toGQ m)).toRingEquiv x) (fun δ => χ (cj m δ)) := by
  first | exact @GlobalTheory.KZ.H3.kum_kmap_sl | exact GlobalTheory.KZ.H3.kum_kmap_sl | (intros; apply GlobalTheory.KZ.H3.kum_kmap_sl <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.exists_kummerCharacter_of_upperHalfPlane_root : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (f : X.Kˣ) (a b : ℂ → ℂ), AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f → IsRoot X (l ^ n) f a b → ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  first | exact @GlobalTheory.KZ.H3.kum_of_isRoot | exact GlobalTheory.KZ.H3.kum_of_isRoot | (intros; apply GlobalTheory.KZ.H3.kum_of_isRoot <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.kummerCharacter_additive_on_congruence : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M, χ (δ * δ') = χ δ + χ δ' := by
  first | exact @GlobalTheory.KZ.H3.KumHom.kum_hom | exact GlobalTheory.KZ.H3.KumHom.kum_hom | (intros; apply GlobalTheory.KZ.H3.KumHom.kum_hom <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.kummerCharacters_eqOn_principalCongruence : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ χ' : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Kum X l n x χ' → Near χ χ' := by
  first | exact @GlobalTheory.KZ.H3.kum_near | exact GlobalTheory.KZ.H3.kum_near | (intros; apply GlobalTheory.KZ.H3.kum_near <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.exists_homogeneousPolyCocycle_eqOn_congruence : ∀ (N l w : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ, IsFam l w (Gam N l) Φ → ∀ n : ℕ, ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)), IsCoc w (Gam N l) z ∧ Near z (Φ n) := by
  first | exact @GlobalTheory.KZ.H3.exists_coc_near | exact GlobalTheory.KZ.H3.exists_coc_near | (intros; apply GlobalTheory.KZ.H3.exists_coc_near <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.exists_isRoot_of_mem_Un_of_jHol : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) , JHol X → ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, IsRoot X m f a b := by
  first | exact @GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un | exact GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un | (intros; apply GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue.DlUniq

variable {Ω : Type} [Field Ω]

theorem cg_mul (A : ValuationSubring Ω) (l n : ℕ) (D G : HahnSeries ℚ Ω)
    (hD : ∀ r, CgA A l n (D.coeff r) 0) (hG : ∀ r, G.coeff r ∈ A) : ∀ r, CgA A l n ((D * G).coeff r) 0 := by
  intro r
  have h : ∀ i, ∃ z ∈ A, D.coeff i = (l : Ω) ^ n * z := fun i => by
    obtain ⟨z, hz, e⟩ := hD i; exact ⟨z, hz, by simpa using e⟩
  choose z hzA hz using h
  refine ⟨∑ ij ∈ Finset.addAntidiagonal D.isPWO_support G.isPWO_support r, z ij.1 * G.coeff ij.2, ?_, ?_⟩
  · exact Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hzA _) (hG _))
  · rw [HahnSeries.coeff_mul, sub_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ij _ => ?_)
    rw [hz, mul_assoc]

theorem cg_sub (A : ValuationSubring Ω) (l n : ℕ) (D E : HahnSeries ℚ Ω)
    (hD : ∀ r, CgA A l n (D.coeff r) 0) (hE : ∀ r, CgA A l n (E.coeff r) 0) : ∀ r, CgA A l n ((D - E).coeff r) 0 := by
  intro r
  obtain ⟨z, hz, e⟩ := hD r
  obtain ⟨w, hw, e'⟩ := hE r
  refine ⟨z - w, A.sub_mem hz hw, ?_⟩
  rw [HahnSeries.coeff_sub, sub_zero, mul_sub, ← e, ← e', sub_zero, sub_zero]

theorem cg_of (A : ValuationSubring Ω) (l n : ℕ) (D E : HahnSeries ℚ Ω)
    (h : ∀ r, CgA A l n (D.coeff r) (E.coeff r)) : ∀ r, CgA A l n ((D - E).coeff r) 0 := by
  intro r
  obtain ⟨z, hz, e⟩ := h r
  exact ⟨z, hz, by rw [HahnSeries.coeff_sub, sub_zero, e]⟩

theorem key (θ : HahnSeries ℚ Ω → HahnSeries ℚ Ω)
    (hL : ∀ P Q, θ (P * Q) = θ P * Q + P * θ Q) (hC : ∀ c : Ω, θ (HahnSeries.C c) = 0)
    (k k2 : Ω) (hk : k ≠ 0) (a b a2 b2 : HahnSeries ℚ Ω)
    (h : HahnSeries.C k * a * b2 = HahnSeries.C k2 * a2 * b) :
    (θ a * b - a * θ b) * (a2 * b2) = (θ a2 * b2 - a2 * θ b2) * (a * b) := by
  have e1 : θ (HahnSeries.C k * a * b2) = HahnSeries.C k * (θ a * b2 + a * θ b2) := by
    rw [mul_assoc, hL, hC, hL]; ring
  have e2 : θ (HahnSeries.C k * a * b2) = HahnSeries.C k2 * (θ a2 * b + a2 * θ b) := by
    rw [h, mul_assoc, hL, hC, hL]; ring
  have h0 : HahnSeries.C k * ((θ a * b - a * θ b) * (a2 * b2) - (θ a2 * b2 - a2 * θ b2) * (a * b)) = 0 := by
    linear_combination (-(a2 * b)) * e1 + (a2 * b) * e2 - (θ a2 * b + a2 * θ b) * h
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd h1 (HahnSeries.C_ne_zero hk)
  · exact sub_eq_zero.mp h1

end GlobalTheory.Glue.DlUniq

namespace GlobalTheory.Glue.DlUniq

theorem T_pow_mem_Gamma (M : ℕ) : (ModularGroup.T ^ M : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  have h := ModularGroup.coe_T_zpow (M : ℤ)
  rw [zpow_natCast] at h
  simp [h]

theorem mem_KT {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (f : X.K) :
    ∃ M : ℕ, 0 < M ∧ f ∈ KT X M := by
  obtain ⟨M, hM, h⟩ := X.level f
  exact ⟨M, hM, h _ (T_pow_mem_Gamma M)⟩

end GlobalTheory.Glue.DlUniq

namespace GlobalTheory.Glue


open GlobalTheory.Glue.DlUniq in
theorem isDl_unique : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (f : X.K) (φ φ' : HahnSeries ℚ Ω), IsDl X A l n s f φ → IsDl X A l n s f φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X _ l _ A hl n s f φ φ' h1 h2
  obtain ⟨hφA, a, b, κ, hκ, hab, hPa, hPb, hφ⟩ := h1
  obtain ⟨hφ'A, a2, b2, κ2, hκ2, hab2, hPa2, hPb2, hφ'⟩ := h2
  have hth := fun P Q => (GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const (Ω := Ω) s P Q)

  have hK : algebraMap Ω X.K κ * a * b2 = algebraMap Ω X.K κ2 * a2 * b := by
    rw [← hab, ← hab2]; ring
  have hE : HahnSeries.C κ * X.exp a * X.exp b2 = HahnSeries.C κ2 * X.exp a2 * X.exp b := by
    have := congrArg X.exp hK
    simp only [map_mul, AlgHom.commutes] at this
    have ec : ∀ c : Ω, algebraMap Ω (HahnSeries ℚ Ω) c = HahnSeries.C c := fun c => by
      rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply]; simp [HahnSeries.ofPowerSeries_C]
    rwa [ec, ec] at this
  have hkey := key (theta s) (fun P Q => (hth P Q).1) (fun c => (hth 0 0).2.2 c) κ κ2 hκ _ _ _ _ hE

  set P := X.exp a * X.exp b * (X.exp a2 * X.exp b2) with hP
  have hPab := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPa hPb
  have hPab2 := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPa2 hPb2
  have hPP : Prim A P := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPab hPab2
  obtain ⟨M, hM, hMK⟩ := mem_KT X (a * b * (a2 * b2))
  have hsupp := (GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents ε X M hM _).mp hMK
  have hsuppP : ∀ r : ℚ, P.coeff r ≠ 0 → (r * M).den = 1 := by
    simpa [hP, map_mul] using hsupp
  have hD1 := cg_mul A l n _ _ (cg_of A l n _ _ hφ) hPab2.1
  have hD2 := cg_mul A l n _ _ (cg_of A l n _ _ hφ') hPab.1
  have hdiff := cg_sub A l n _ _ hD1 hD2
  have hid : (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) * (X.exp a2 * X.exp b2) -
      (φ' * X.exp a2 * X.exp b2 - (theta s (X.exp a2) * X.exp b2 - X.exp a2 * theta s (X.exp b2))) * (X.exp a * X.exp b)
      = (φ - φ') * P := by
    rw [hP]; linear_combination (-1 : HahnSeries ℚ Ω) * hkey
  rw [hid] at hdiff
  have hint : ∀ r, (φ - φ').coeff r ∈ A := fun r => by
    rw [HahnSeries.coeff_sub]; exact sub_mem (hφA r) (hφ'A r)
  have hfin := GlobalTheory.T.primitiveHahnSeries_not_zeroDivisor_modPrimePow l A hl n M P (φ - φ') hM hPP hsuppP hint hdiff
  intro r
  obtain ⟨z, hz, e⟩ := hfin r
  exact ⟨z, hz, by rw [← e, HahnSeries.coeff_sub, sub_zero]⟩

end GlobalTheory.Glue
end
