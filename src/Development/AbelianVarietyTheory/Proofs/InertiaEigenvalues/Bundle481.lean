module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle450
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle340
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle477
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle472
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle341
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle401
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle166
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle387
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle365
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle344
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle473
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004

@[expose] public section

section

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.LabelMul

theorem ip_add_right {G : Type} [Group G] [Fintype G] (χ φ ψ : G → ℂ) :
    ip χ (φ + ψ) = ip χ φ + ip χ ψ := by
  simp only [ip, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem ip_sum_eq_count {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (hχ : IsIrr χ) (L : List (G → ℂ))
    (hL : ∀ ρ ∈ L, IsIrr ρ) : ip χ L.sum = (L.count χ : ℕ) := by
  induction L with
  | nil => simp [ip]
  | cons ρ L ih =>
    rw [List.sum_cons, ip_add_right, ih (fun σ hσ => hL σ (List.mem_cons_of_mem _ hσ)),
      (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G χ ρ hχ (hL ρ List.mem_cons_self)).2.2, List.count_cons]
    by_cases h : χ = ρ
    · subst h
      simp [add_comm]
    · have h' : ¬ ρ = χ := fun e => h e.symm
      simp [h, h']

theorem ip_nat {G : Type} [Group G] [Fintype G] {χ φ : G → ℂ} (hχ : IsIrr χ) (hφ : IsChar φ) :
    ∃ k : ℕ, ip χ φ = k := by
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G φ).1 hφ
  exact ⟨_, ip_sum_eq_count hχ L hL⟩

theorem exists_add_of_ip_ne_zero {G : Type} [Group G] [Fintype G] {χ φ : G → ℂ} (hχ : IsIrr χ) (hφ : IsChar φ)
    (h : ip χ φ ≠ 0) : ∃ ψ, IsChar ψ ∧ φ = χ + ψ := by
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G φ).1 hφ
  rw [ip_sum_eq_count hχ L hL] at h
  have hm : χ ∈ L := List.count_pos_iff.1 (Nat.pos_of_ne_zero (by exact_mod_cast h))
  refine ⟨(L.erase χ).sum, (GlobalTheory.T.character_decomposition_and_classFunction_expansion G χ).2.2.2.2 _
    (fun ρ hρ => isChar_of_isIrr (hL ρ (List.mem_of_mem_erase hρ))), ?_⟩
  rw [(List.perm_cons_erase hm).sum_eq, List.sum_cons]

variable {g : ℕ} [Fact g.Prime]

theorem hc_add_left (a b n : ℕ) (α α' : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b (α + α') β n = hc a b α β n + hc a b α' β n := by
  funext x
  simp only [hc, hcT, Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · ring
  · simp

theorem hc_add_right (a b n : ℕ) (α : Gn g a → ℂ) (β β' : Gn g b → ℂ) :
    hc a b α (β + β') n = hc a b α β n + hc a b α β' n := by
  funext x
  simp only [hc, hcT, Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · ring
  · simp

omit [Fact g.Prime] in
theorem degL_append (P Q : List (Pc g)) : degL (P ++ Q) = degL P + degL Q := by
  simp [degL]

theorem hcL_append (P Q : List (Pc g)) (hP : ∀ p ∈ P, IsChar p.2) (hQ : ∀ p ∈ Q, IsChar p.2) :
    ∀ n, n = degL P + degL Q →
      hcL (P ++ Q) n = hc (degL P) (degL Q) (hcL P (degL P)) (hcL Q (degL Q)) n := by
  have cQ : IsClass (hcL Q (degL Q)) :=
    (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ _).2.2.1 (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g Q Q _ rfl hQ).1
  induction P with
  | nil =>
    intro n hn
    have hn' : n = degL Q := by simpa [degL] using hn
    subst hn'
    exact (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g (degL Q) (degL Q) (degL Q) (degL Q) _ _ _ cQ cQ cQ).2.2.1.symm
  | cons p P ih =>
    intro n hn
    have hP' : ∀ q ∈ P, IsChar q.2 := fun q hq => hP q (List.mem_cons_of_mem _ hq)
    have cP : IsClass (hcL P (degL P)) :=
      (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ _).2.2.1 (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g P P _ rfl hP').1
    have cp : IsClass p.2 := (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ _).2.2.1 (hP p List.mem_cons_self)
    have key : ∀ m, m = degL P + degL Q → hc p.1 m p.2 (hcL (P ++ Q) m) n =
        hc (p.1 + degL P) (degL Q) (hc p.1 (degL P) p.2 (hcL P (degL P)) (p.1 + degL P)) (hcL Q (degL Q)) n := by
      intro m hm
      subst hm
      rw [ih hP' _ rfl]
      exact ((GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g _ _ _ n _ _ _ cp cP cQ).1 hn).symm
    exact key _ (degL_append P Q)

theorem hasLabel_mul : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (a b n : ℕ) (χ : Gn g n → ℂ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (f₁ f₂ : (ZMod g)[X]), n = a + b → IsIrr χ → IsIrr α → IsIrr β → HasLabel L α f₁ → HasLabel L β f₂ → ip χ (hc a b α β n) ≠ 0 → HasLabel L χ (f₁ * f₂) := by
  intro g _ L a b n χ α β f₁ f₂ hn hχ hα hβ h₁ h₂ hip
  obtain ⟨P, hP, rfl, rfl, iP⟩ := h₁
  obtain ⟨Q, hQ, rfl, rfl, iQ⟩ := h₂
  have cP : ∀ p ∈ P.map Prod.snd, IsChar p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact isChar_of_isIrr (hP q hq).2.1.2.1
  have cQ : ∀ p ∈ Q.map Prod.snd, IsChar p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact isChar_of_isIrr (hQ q hq).2.1.2.1
  obtain ⟨A, hA, eA⟩ := exists_add_of_ip_ne_zero hα (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g _ [] _ rfl cP).1 iP
  obtain ⟨B, hB, eB⟩ := exists_add_of_ip_ne_zero hβ (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g _ [] _ rfl cQ).1 iQ
  refine ⟨P ++ Q, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact hP p h
    · exact hQ p h
  · rw [List.map_append, degL_append, hn]
  · rw [List.map_append, List.prod_append]
  · rw [List.map_append, hcL_append _ _ cP cQ n hn, eA, eB, hc_add_left, hc_add_right, hc_add_right,
      ip_add_right, ip_add_right, ip_add_right]
    have H := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g _ _ n hn).1
    obtain ⟨k₁, e₁⟩ := ip_nat hχ (H _ _ (isChar_of_isIrr hα) (isChar_of_isIrr hβ))
    obtain ⟨k₂, e₂⟩ := ip_nat hχ (H _ _ (isChar_of_isIrr hα) hB)
    obtain ⟨k₃, e₃⟩ := ip_nat hχ (H _ _ hA (isChar_of_isIrr hβ))
    obtain ⟨k₄, e₄⟩ := ip_nat hχ (H _ _ hA hB)
    rw [e₁] at hip
    rw [e₁, e₂, e₃, e₄]
    have h1 : k₁ ≠ 0 := by exact_mod_cast hip
    have : k₁ + k₂ + (k₃ + k₄) ≠ 0 := by omega
    exact_mod_cast this

end GlobalTheory.GLq.LabelMul
end

section

noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.GenericCount

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem ip_comm {G : Type} [Group G] [Fintype G] (α β : G → ℂ) : ip α β = ip β α := by
  unfold ip
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun x => by simp [mul_comm])

theorem tr_finset_sum {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (S : Finset (G → ℂ))
    (c : (G → ℂ) → ℂ) : tr a (∑ ρ ∈ S, c ρ • ρ) = ∑ ρ ∈ S, c ρ * tr a ρ := by
  unfold tr
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun x _ => by ring

theorem gg_isClass {g : ℕ} [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : IsClass (gg ψ n) := by
  intro x z
  simp only [gg]
  congr 1
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft z) _ _ (fun y => ?_)
  have h : (z * y)⁻¹ * (z * x * z⁻¹) * (z * y) = y⁻¹ * x * y := by group
  simp only [Equiv.coe_mulLeft, h]

end GlobalTheory.GLq.GenericCount

namespace GlobalTheory.GLq


open GlobalTheory.GLq.GenericCount in
theorem card_generic_irr_le : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ n : ℕ, 0 < n →
    Set.ncard {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0} ≤ g ^ n - g ^ (n - 1) := by
  intro g _ ψ hψ n hn
  obtain ⟨hfin, -⟩ := GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)
  set S := hfin.toFinset with hS
  have hmemS : ∀ ρ, ρ ∈ S ↔ IsIrr ρ := fun ρ => by rw [hS, Set.Finite.mem_toFinset]; rfl
  have hnorm := GlobalTheory.T.gelfandGraevCharacterGLn_norm_and_reciprocity g ψ hψ n hn
  have hdec := (GlobalTheory.T.character_decomposition_and_classFunction_expansion (Gn g n) (gg ψ n)).2.1 (gg_isClass ψ n)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hdec
  have hirrC : ∀ ρ : Gn g n → ℂ, IsIrr ρ → IsClass ρ := fun ρ h =>
    (GlobalTheory.T.character_decomposition_and_classFunction_expansion (Gn g n) ρ).2.2.1 (isChar_of_isIrr h)
  have hnat : ∀ ρ : Gn g n → ℂ, IsIrr ρ → ∃ m : ℕ, wh ψ ρ = m := fun ρ h =>
    (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g n) (eU g n ψ) ρ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g n 0 0 ψ).1 (isChar_of_isIrr h)
  choose! m hm using hnat
  have hsum : ((∑ ρ ∈ S, m ρ ^ 2 : ℕ) : ℂ) = ((g ^ n - g ^ (n - 1) : ℕ) : ℂ) := by
    rw [Nat.cast_sub (Nat.pow_le_pow_right (Nat.Prime.pos Fact.out) (Nat.sub_le n 1))]
    push_cast
    rw [← hnorm.1]
    have hw : wh ψ (gg ψ n) = ∑ ρ ∈ S, ip (gg ψ n) ρ * wh ψ ρ := by
      conv_lhs => rw [hdec]
      unfold wh
      exact tr_finset_sum _ _ _
    rw [hw]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hI := (hmemS ρ).1 hρ
    rw [ip_comm, hnorm.2 ρ (hirrC ρ hI), hm ρ hI]
    ring
  have hsumN : ∑ ρ ∈ S, m ρ ^ 2 = g ^ n - g ^ (n - 1) := by exact_mod_cast hsum
  have hset : {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0} = ↑(S.filter fun ρ => m ρ ≠ 0) := by
    ext ρ
    simp only [Set.mem_setOf_eq, Finset.coe_filter, hmemS]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h0 => h2 (by rw [hm ρ h1, h0, Nat.cast_zero])⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h0 => h2 (by rw [hm ρ h1] at h0; exact_mod_cast h0)⟩
  rw [hset, Set.ncard_coe_finset, ← hsumN, Finset.card_eq_sum_ones]
  calc ∑ ρ ∈ S.filter (fun ρ => m ρ ≠ 0), 1 ≤ ∑ ρ ∈ S.filter (fun ρ => m ρ ≠ 0), m ρ ^ 2 :=
        Finset.sum_le_sum fun ρ hρ => Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (Finset.mem_filter.1 hρ).2)
    _ ≤ ∑ ρ ∈ S, m ρ ^ 2 := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end GlobalTheory.GLq
end
end

section

noncomputable section

namespace GlobalTheory.ExpImage.LowTerms

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem oB_mem_zero {AI : LocAinf l P} (T : LocTied l P AI) (x : Om l) : oB P x ∈ FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om x
  exact (GlobalTheory.ThetaTie.fil_zero T _).2 ⟨y, h1.symm⟩

theorem tD_pow_mem_zero (j : ℕ) : tD P ^ j ∈ FilB P 0 :=
  FilB_anti (by simp) (FilB_pow (tD_mem (P := P)) j)

theorem act_term (g : GQ l) (c : ℚ_[l]) {x : Om l} (hx : g x = x) (j : ℕ) :
    P.actQdR g (qB P c * (oB P x * tD P ^ j)) =
      qB P (c * (P.χQ g : ℚ_[l]) ^ j) * (oB P x * tD P ^ j) := by
  rw [map_mul, map_mul, map_pow, act_tD, P.actQdR_Om, hx, AlgEquiv.commutes, map_mul, map_pow,
    mul_pow]
  ring

theorem Ks_le_Kinf (K : FinExt l) (s : ℕ) : Ks K s ≤ Kinf K :=
  sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun _ hx => Exists.intro s hx) _

theorem expStar_of_sum : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), IsGen (LT l).χQ K s g → ∀ w : ℕ → Om l, (∀ j, w j ∈ Ks K s) → ∀ b ∈ FilB (LT l) 0, (∀ h ∈ Hinf K, NearZ (LT l) (e + 1) ((LT l).actQdR h b - b)) → NearZ (LT l) (e + 1) (∑ j ∈ Finset.range (e + 1), oB (LT l) (w j) * tD (LT l) ^ j + (qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g b - b)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((LT l).χQ g : ℚ_[l]))⁻¹ * w e) := by
  intro LT l _ AI T K s hs e g hg w hw b hb hH hN
  have hχ : IsCyc (LT l).χQ := (LT l).χQ_cyc
  obtain ⟨hn, -, hker⟩ := GlobalTheory.Cyc.cyc_basic l _ hχ
  obtain ⟨-, -, hint, hlog⟩ := GlobalTheory.PadicLogUnits.logZl_hom l
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  set u : ℚ_[l] := ((LT l).χQ g : ℚ_[l]) with hu
  have hu0 : u ≠ 0 := Units.ne_zero _
  have hL : logZl l u ≠ 0 := by
    rw [← norm_pos_iff, hlog s hs.1 hs.2 u hg.2.le, hg.2]
    exact zpow_pos hl _
  have hLc : ((logChi LT g : ℤ_[l]) : ℚ_[l]) = logZl l u :=
    congrArg Subtype.val (dif_pos (hint _ (hn g)))
  have hne : ∀ j ∈ Finset.range e, u ^ ((j : ℤ) - e) - 1 ≠ 0 := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [← norm_pos_iff, GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l s hs u hg.2 _ (by omega)]
    exact zpow_pos hl _
  set c : ℕ → ℚ_[l] := fun j => (u ^ ((j : ℤ) - e) - 1)⁻¹ with hc
  set S : (LT l).R.BdR :=
    ∑ j ∈ Finset.range e, qB (LT l) (c j) * (oB (LT l) (w j) * tD (LT l) ^ j) with hS
  have hS0 : S ∈ FilB (LT l) 0 :=
    Submodule.sum_mem _ fun j _ =>
      qB_mul_mem _ (FilB_zero_mul (oB_mem_zero T _) (tD_pow_mem_zero j))
  have hSH : ∀ h ∈ Hinf K, (LT l).actQdR h S = S := by
    intro h hh
    have h1 : (LT l).χQ h = 1 := (hker K h (Hinf_le_fix hh)).2.1 hh

    rw [hS, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [act_term h _ (hh ⟨w j, Ks_le_Kinf K s (hw j)⟩), h1]
    simp
  have hSg : qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g S - S =
      ∑ j ∈ Finset.range e, oB (LT l) (w j) * tD (LT l) ^ j := by

    rw [hS, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [act_term g _ (hg.1 ⟨w j, hw j⟩), ← mul_assoc, ← map_mul, ← sub_mul, ← map_sub]
    have : (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (c j * u ^ j) - c j = 1 := by
      have h2 : u ^ ((j : ℤ) - e) = u ^ (-(e : ℤ)) * u ^ j := by
        rw [sub_eq_neg_add, zpow_add₀ hu0, zpow_natCast]
      have h3 : (u ^ ((j : ℤ) - e) - 1) * c j = 1 := mul_inv_cancel₀ (hne j hj)
      rw [Units.val_zpow_eq_zpow_val, ← hu]
      rw [h2] at h3
      linear_combination h3
    rw [this, map_one, one_mul]
  refine GlobalTheory.T.integral_cocycle_of_generator_and_fixing LT l AI T K s hs e g hg _
    (mul_mem (IntermediateField.algebraMap_mem _ _) (hw e)) (b + S) (add_mem hb hS0)
    (fun h hh => ?_) ?_
  · have := hH h hh
    rwa [map_add, hSH h hh, add_sub_add_right_eq_sub]
  · have h4 : qB (LT l) (logZl l u) * oB (LT l) (algebraMap ℚ_[l] (Om l) (logZl l u)⁻¹) = 1 := by
      rw [← IsScalarTower.algebraMap_apply, ← map_mul, mul_inv_cancel₀ hL, map_one]
    convert hN using 1
    rw [hLc, Finset.sum_range_succ, ← hSg, map_add (f := _), map_mul]
    linear_combination (oB (LT l) (w e) * tD (LT l) ^ e) * h4

end GlobalTheory.ExpImage.LowTerms
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial
  GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.OChoose

theorem placesOver_nonempty (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (placesOver E p).Nonempty := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 E) := by
    intro hu
    have h1 := hu.map (Algebra.norm ℤ : 𝓞 E →* ℤ)
    rw [show ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) by simp, Algebra.norm_algebraMap] at h1
    have h2 := Int.isUnit_iff_natAbs_eq.1 h1
    have h3 : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h2
    rcases Nat.pow_eq_one.1 h2 with h | h
    · exact hp.one_lt.ne' h
    · exact h3.ne' h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 E)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((p : ℕ) : 𝓞 E) ∈ M := hle (Ideal.subset_span rfl)
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hmem⟩
  rw [h, Ideal.mem_bot] at hmem
  exact hp.ne_zero (by exact_mod_cast hmem)

theorem exists_wild_inertia_cyclotomic_generator (D : D7) (i : D.nd.Loc) : ∃ g0, IsWildInertiaCyclotomicElement D.nd i g0 := by
  by_cases ht : ∃ k, D.nd.l i = D.host.g k
  · obtain ⟨k, hk⟩ := ht
    obtain ⟨g0, h1, h2, h3⟩ := GlobalTheory.T.exists_wildInertia_generating_cyclotomicValue D i k hk
    exact ⟨g0, ⟨h1, h2⟩, fun _ => h3⟩
  · obtain ⟨w, hw⟩ := placesOver_nonempty D.host.E (D.nd.l i) (D.nd.lPrime i).out
    obtain ⟨g, hg, hc⟩ := GlobalTheory.EpsInertia.epsAll D i w hw 1
    exact ⟨g, ⟨⟨w, hw, hg⟩, 1, by simpa using hc⟩, fun h => absurd h ht⟩

theorem exists_fin_roots {p : ℂ[X]} {t : ℕ} (hm : p.Monic) (hd : p.natDegree = t) :
    ∃ α : Fin t → ℂ, (∀ c, α c ∈ p.roots) ∧ p = ∏ c, (X - C (α c)) := by
  have hcard : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hp := (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard).symm
  obtain ⟨l, hl⟩ : ∃ l : List ℂ, (l : Multiset ℂ) = p.roots := Quotient.exists_rep _
  have hlen : l.length = t := by rw [← hd, ← hcard, ← hl, Multiset.coe_card]
  subst hlen
  refine ⟨fun c => l.get c, fun c => hl ▸ Multiset.mem_coe.2 (List.get_mem l c), ?_⟩
  conv_lhs => rw [hp, ← hl]
  rw [Multiset.map_coe, Multiset.prod_coe]
  rw [← List.prod_ofFn]
  congr 1
  apply List.ext_get (by simp)
  intro n h1 h2
  simp

theorem blockPol_iota (D : D7) (i : D.nd.Loc) {rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))}
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.HidaSetting D.R.t (D.nd.T i) (D.nd.Z i) rep ρ (D.nd.chi i)) {π : D.nd.X i} {g0 : GE D.nd}
    {L : ℕ} {eB e1 X0 : D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)}
    (hc : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsChoice D.R.t (D.nd.T i) rep ρ (D.nd.chi i) π g0 L eB e1 X0) (x : D.nd.X i) :
    ((GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.blockPol (eB x) (X0 x)).map (iotaO D.nd D.naut i)).Monic ∧
      ((GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.blockPol (eB x) (X0 x)).map (iotaO D.nd D.naut i)).natDegree = D.R.t := by
  obtain ⟨hr, -, -, hX1, hX2, -⟩ := GlobalTheory.ConsExists.choice_facts hS.1 hS.2.2.2.1 hc
  obtain ⟨hm, hd⟩ := GlobalTheory.ConsExists.blockPol_monic (congrFun hc.1.2.2.1 x) (hr x) (congrFun hX1 x) (congrFun hX2 x)
  have hinj : Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.toFr (D.nd.O i)) :=
    IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))
  have hm' := Polynomial.monic_of_injective hinj hm
  rw [Polynomial.natDegree_map_eq_of_injective hinj] at hd
  exact ⟨hm'.map _, (hm'.natDegree_map _).trans hd⟩

end GlobalTheory.OChoose

end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem toricCharacter_isCMHostValueDatum : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), 1 ≤ s → (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → IsHostDatum D.host (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 l j a) := by
  intro D Z hZ l j a s hs hN
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hcm, hind⟩ := GlobalTheory.T.conjugateEmbedding_isCMType_sqrtMinusD D.R D.host
  obtain ⟨hκ, hinf⟩ := GlobalTheory.T.one_le_kap_and_lam0_hasInf D Z hZ l j a s hN
  obtain ⟨hu, ht⟩ := GlobalTheory.T.lam0_isUnitary_and_trivOnF D Z hZ l j a
  have hb : IsBaseCond (cond0 D.host Z.w0) :=
    GlobalTheory.T.isBaseCond_of_split_primes D.R D.host Z.q0 Z.w0 (fun p hp P hP => by
      obtain ⟨h1, -, h3, h4⟩ := hZ.places.splits p hp
      exact GlobalTheory.T.splitsInCMField_placeBelow_of_completelySplit D.host.E p h1 h3 h4 P hP) hZ.places
  refine ⟨hcm, hind, hs, hκ, hb, hu, ht, hinf, fun v P hP => ⟨fun h => absurd h (Finset.notMem_empty v), fun _ => ?_⟩⟩
  have hv : v = below P := HeightOneSpectrum.ext (hP.symm.trans (over_below P))
  subst hv
  exact GlobalTheory.T.lam_conductor_exponent D Z hZ l j a P

end GlobalTheory.LamTie
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.weil_group_transport : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (c : Weil h ≃* Weil h'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → (∀ σ, WeilRel φ σ (c σ)) → ∀ L : IntermediateField E Ω, FiniteDimensional E L → IsLocalExt L h → ∃ (L' : IntermediateField E' Ω') (jL : L →+* L'), FiniteDimensional E' L' ∧ IsLocalExt L' h' ∧ Module.finrank E' L' = Module.finrank E L ∧ (∀ x : L, φ (x : Ω) = (jL x : Ω')) ∧ Algebra.adjoin E' (Set.range jL) = ⊤ := by
  first | exact @GlobalTheory.LocLanglands.exists_isLocalExt_transport | exact GlobalTheory.LocLanglands.exists_isLocalExt_transport | (intros; apply GlobalTheory.LocLanglands.exists_isLocalExt_transport <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.place_over_transport_ring_iso : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∃ c : Weil h ≃* Weil h', (∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ') ∧ (∀ σ, deg (c σ) = deg σ) ∧ normV w' = normV w ∧ ∀ (M : Type) [Monoid M] (f : Weil h' →* M), GlobalTheory.WeilDeligne.IsSmooth f ↔ GlobalTheory.WeilDeligne.IsSmooth (f.comp c.toMonoidHom) := by
  first | exact @GlobalTheory.WeilTransport.weil_equiv | exact GlobalTheory.WeilTransport.weil_equiv | (intros; apply GlobalTheory.WeilTransport.weil_equiv <;> assumption)
end
