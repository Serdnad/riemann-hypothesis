module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle026
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle019
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle032
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle040
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma deg_app (a b : List (ℕ × ℕ)) : deg (a ++ b) = deg a + deg b := by
  simp [GlobalTheory.Shin.deg]

private lemma deg_rep (t c : ℕ) : deg (List.replicate t ((1 : ℕ), c)) = t := by
  simp [GlobalTheory.Shin.deg]

private lemma expand_cons' (p : ℕ × ℕ) (D : List (ℕ × ℕ)) :
    expand (p :: D) = List.replicate p.1 (1, p.2) ++ expand D := by
  simp [UpperTheory.Gal.InertialTypesAlt.expand]

private lemma cusp_one_ne {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m k : ℕ)
    (hm : 0 < m) : cusp θ m k 1 ≠ 0 := by
  have h := GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico F (Fin m → F) (GlobalTheory.CuspGL.rootSum θ k) (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).2 (by simpa using hm)
  simp only [cusp, psiG, Units.val_one, Matrix.toLin'_one]
  erw [h]
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  rw [sub_ne_zero]
  intro heq
  have h2 : ((Nat.card F ^ i : ℕ) : ℂ) = 1 := by
    push_cast
    exact heq.symm
  norm_cast at h2
  have h3 := Nat.one_lt_pow (by omega : i ≠ 0) hq
  omega

private lemma pairs_self {G : Type} [Group G] [Finite G] (Y : G → ℂ) (h : Y 1 ≠ 0) : Pairs Y Y := by
  haveI : Fintype G := Fintype.ofFinite G
  unfold Pairs
  rw [finsum_eq_sum_of_fintype]
  intro h0
  have hre := congrArg Complex.re h0
  rw [Complex.re_sum, Complex.zero_re] at hre
  have hnn : ∀ g : G, 0 ≤ (star (Y g) * Y g).re := by
    intro g
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  have hpos : 0 < (star (Y 1) * Y 1).re := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr h
  have : 0 < ∑ g : G, (star (Y g) * Y g).re :=
    Finset.sum_pos' (fun g _ => hnn g) ⟨1, Finset.mem_univ _, hpos⟩
  linarith

private lemma happ (hA : JAppend) {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (R M : List (ℕ × ℕ)) (t b n : ℕ) (hR : deg R = t) (hM : deg M = b) (hn : n = t + b) :
    J θ (R ++ M) n = hc t b (J θ R t) (J θ M b) n := by
  subst hR hM hn
  exact hA F θ R M _ rfl

private lemma char_cast {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (M : List (ℕ × ℕ)) {n m : ℕ}
    (e : n = m) (h : GlobalTheory.BI.IsChar ℂ ℂ (J θ M n)) : GlobalTheory.BI.IsChar ℂ ℂ (J θ M m) := by
  subst e
  exact h

private lemma J_one_ne (h1 : HcOne) {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (M : List (ℕ × ℕ)) (hM : ∀ p ∈ M, 0 < p.1) : J θ M (deg M) 1 ≠ 0 := by
  induction M with
  | nil =>
    rw [J_nil]
    exact one_ne_zero
  | cons p M ih =>
    have hp : 0 < p.1 := hM p (by simp)
    have hM' : ∀ x ∈ M, 0 < x.1 := fun x hx => hM x (by simp [hx])
    rw [J_cons]
    exact h1 F p.1 (deg M) _ (by simp [GlobalTheory.Shin.deg]) _ _ (cusp_one_ne θ p.1 p.2 hp) (ih hM')

theorem UpperTheory.Gal.InertialTypesAlt.jdPair :
    JAppend → HcOne → HcPair → DetPair → JDChar → JDPair := by
  intro hA h1 hP hD hC F _ _ θ hθ a ha hq
  obtain ⟨q, D, L⟩ := a
  obtain ⟨hq2, hDp, hLp⟩ := ha
  have hL0 : ∀ x ∈ L, 0 < x.1 := fun x hx => (hLp x hx).1
  have charJ : ∀ M : List (ℕ × ℕ), (∀ x ∈ M, 0 < x.1 ∧ Reg q x.1 x.2) → ∀ n, n = deg M →
      GlobalTheory.BI.IsChar ℂ ℂ (J θ M n) := by
    intro M hM n hn
    have hc := (hC F θ hθ).2 ⟨q, [], M⟩ ⟨hq2, by simp, hM⟩ hq
    simp only [Lbl.D, Lbl.L, Lbl.rk] at hc
    rw [JD_nil] at hc
    exact char_cast θ M (by simp [GlobalTheory.Shin.deg] at hn ⊢; omega) hc
  have key : ∀ E : List (ℕ × ℕ), (∀ x ∈ E, 0 < x.1) →
      deg (expand E ++ L) = deg E + deg L ∧
        Pairs (J θ (expand E ++ L) (deg E + deg L)) (JD θ E L (deg E + deg L)) := by
    intro E
    induction E with
    | nil =>
      intro _
      have e1 : expand [] ++ L = L := by simp [UpperTheory.Gal.InertialTypesAlt.expand]
      have e2 : deg ([] : List (ℕ × ℕ)) = 0 := by simp [GlobalTheory.Shin.deg]
      rw [e1, e2, zero_add, JD_nil]
      exact ⟨rfl, pairs_self _ (J_one_ne h1 θ L hL0)⟩
    | cons p E ih =>
      intro hp
      have hp1 : 0 < p.1 := hp p (by simp)
      have hE : ∀ x ∈ E, 0 < x.1 := fun x hx => hp x (by simp [hx])
      obtain ⟨hdeg, hpair⟩ := ih hE
      have hdc : deg (p :: E) = p.1 + deg E := by simp [GlobalTheory.Shin.deg]
      have hexp : ∀ x ∈ expand E ++ L, 0 < x.1 ∧ Reg q x.1 x.2 := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · simp only [UpperTheory.Gal.InertialTypesAlt.expand, List.mem_flatMap, List.mem_replicate] at h
          obtain ⟨y, -, -, rfl⟩ := h
          exact ⟨Nat.one_pos, fun i hi hi1 => absurd hi1 (by omega)⟩
        · exact hLp x h
      have hrep : ∀ x ∈ List.replicate p.1 ((1 : ℕ), p.2), 0 < x.1 ∧ Reg q x.1 x.2 := by
        intro x hx
        rw [List.mem_replicate] at hx
        rw [hx.2]
        exact ⟨Nat.one_pos, fun i hi hi1 => absurd hi1 (by omega)⟩
      rw [expand_cons', List.append_assoc, deg_app, deg_rep, hdeg, hdc]
      refine ⟨by omega, ?_⟩
      rw [happ hA θ _ _ p.1 (deg E + deg L) _ (deg_rep _ _) hdeg (by omega), JD_cons]
      refine hP F p.1 _ _ (by omega) _ _ _ _ ((hC F θ hθ).1 _ _)
        (charJ _ hrep _ (deg_rep _ _).symm) ((hC F θ hθ).2 ⟨q, E, L⟩ ⟨hq2, hE, hLp⟩ hq)
        (charJ _ hexp _ hdeg.symm) (hD F θ p.1 p.2) hpair
  exact key D hDp
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem detc_isCl {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t c : ℕ) :
    IsCl (detc θ t c) := by
  intro x y
  simp only [detc, Units.val_mul, Matrix.det_mul]
  congr 2
  rw [mul_comm _ (x : Matrix (Fin t) (Fin t) F).det, mul_assoc, ← Matrix.det_mul, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.det_one, mul_one]

private theorem detc_ne_zero {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t c : ℕ)
    (x : GL (Fin t) F) : detc θ t c x ≠ 0 := by
  unfold detc
  apply pow_ne_zero
  have hx : (x : Matrix (Fin t) (Fin t) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp x.isUnit).ne_zero
  have ha : algebraMap F (AlgebraicClosure F) (x : Matrix (Fin t) (Fin t) F).det ≠ 0 :=
    (_root_.map_ne_zero _).mpr hx
  intro h
  have h1 : θ (algebraMap F (AlgebraicClosure F) (x : Matrix (Fin t) (Fin t) F).det *
      (algebraMap F (AlgebraicClosure F) (x : Matrix (Fin t) (Fin t) F).det)⁻¹) = 1 := by
    rw [mul_inv_cancel₀ ha, map_one]
  rw [map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

private theorem detc_parab {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t c : ℕ)
    (hd : ∑ _i : Fin t, 1 = t) (p : parab F (stdBlocks (fun _ : Fin t => 1) hd)) :
    detc θ t c (p : GL (Fin t) F) =
      ∏ i, detc θ 1 c (leviProj F (stdBlocks (fun _ : Fin t => 1) hd) p i) := by
  have h := congrArg Units.val (det_parab F (stdBlocks (fun _ : Fin t => 1) hd) p)
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod] at h
  simp only [detc, h, map_prod, Finset.prod_pow]

theorem UpperTheory.Gal.InertialTypesAlt.detPair :
    FrobL → JDEq → DetPair := by
  intro hF hJ F _ _ θ t c
  obtain ⟨hJD, hcusp, _⟩ := hJ F θ
  have hd : ∑ _i : Fin t, 1 = t := by simp
  obtain ⟨c', hc', hfr⟩ := hF F t (fun _ => 1) t hd
  have hJt : J θ (List.replicate t (1, c)) t =
      hcL (List.ofFn fun _ : Fin t => (⟨1, detc θ 1 c⟩ : (m : ℕ) × (GL (Fin m) F → ℂ))) t := by
    rw [← JD_nil, hJD]
    congr 1
    simp [hcusp, List.map_replicate, List.ofFn_const]
  unfold Pairs
  rw [hJt, hfr _ _ (detc_isCl θ t c), mul_ne_zero_iff]
  refine ⟨hc', ?_⟩
  simp_rw [← detc_parab θ t c hd]
  haveI : Fintype (parab F (stdBlocks (fun _ : Fin t => 1) hd)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  intro h0
  have hre := congrArg Complex.re h0
  rw [Complex.re_sum, Complex.zero_re] at hre
  have hpos : ∀ p : parab F (stdBlocks (fun _ : Fin t => 1) hd),
      0 < (star (detc θ t c (p : GL (Fin t) F)) * detc θ t c (p : GL (Fin t) F)).re := by
    intro p
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr (detc_ne_zero θ t c _)
  have : 0 < ∑ p : parab F (stdBlocks (fun _ : Fin t => 1) hd),
      (star (detc θ t c (p : GL (Fin t) F)) * detc θ t c (p : GL (Fin t) F)).re :=
    Finset.sum_pos (fun p _ => hpos p) ⟨1, Finset.mem_univ _⟩
  linarith
end

section

noncomputable section

open GlobalTheory.BI GlobalTheory.Shin

namespace UpperTheory.Gal.InertialTypesAlt

section Group

variable {G : Type} [Group G] [Finite G]

private theorem sum_eq_pair {χ : G → ℂ} (ψ : G → ℂ) (hχ : IsChar ℂ ℂ χ) :
    (∑ᶠ g, star (χ g) * ψ g) = (Nat.card G : ℂ) * pair ψ χ := by
  have h := GlobalTheory.T.star_virtualCharacter_eq_apply_inv G χ (AddSubgroup.subset_closure hχ)
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  unfold pair
  rw [← mul_assoc, mul_inv_cancel₀ hG, one_mul]
  exact finsum_congr fun g => by rw [h, mul_comm]

private theorem pairs_iff {χ : G → ℂ} (ψ : G → ℂ) (hχ : IsChar ℂ ℂ χ) : Pairs χ ψ ↔ pair ψ χ ≠ 0 := by
  have hc : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold Pairs
  rw [sum_eq_pair ψ hχ, mul_ne_zero_iff]
  tauto

private theorem pair_add_ne {a u b v : G → ℂ} (ha : IsChar ℂ ℂ a) (hu : IsChar ℂ ℂ u) (hb : IsChar ℂ ℂ b)
    (hv : IsChar ℂ ℂ v) (h : pair a b ≠ 0) : pair (a + u) (b + v) ≠ 0 := by
  obtain ⟨hadd, hnat, -, hsymm⟩ := GlobalTheory.T.finiteGroupFunctionPairing_add_nat_pos_symm ℂ ℂ G
  obtain ⟨n1, h1⟩ := hnat b a hb ha
  obtain ⟨n2, h2⟩ := hnat v a hv ha
  obtain ⟨n3, h3⟩ := hnat b u hb hu
  obtain ⟨n4, h4⟩ := hnat v u hv hu
  have e : pair (a + u) (b + v) = pair b a + pair v a + (pair b u + pair v u) := by
    rw [hadd, hsymm a (b + v), hsymm u (b + v), hadd b v a, hadd b v u]
  have hn1 : n1 ≠ 0 := by
    rintro rfl
    exact h (by rw [hsymm, h1]; simp)
  rw [e, h1, h2, h3, h4]
  exact_mod_cast (by omega : n1 + n2 + (n3 + n4) ≠ 0)

private theorem isChar_of_irr {φ : G → ℂ} (h : IsIrrChar ℂ ℂ φ) : IsChar ℂ ℂ φ := by
  obtain ⟨n, ρ, -, e⟩ := h
  exact ⟨n, ρ, e⟩

private theorem common {A : G → ℂ} (hA : IsChar ℂ ℂ A) {α : G → ℂ} (hα : IsChar ℂ ℂ α) (h : pair A α ≠ 0) :
    ∃ φ R R' : G → ℂ, IsIrrChar ℂ ℂ φ ∧ IsChar ℂ ℂ R ∧ IsChar ℂ ℂ R' ∧ A = φ + R ∧ α = φ + R' := by
  obtain ⟨hadd, -, -, hsymm⟩ := GlobalTheory.T.finiteGroupFunctionPairing_add_nat_pos_symm ℂ ℂ G
  obtain ⟨-, hcadd⟩ := GlobalTheory.T.isCharacterOverSubfield_zero_and_add ℂ ℂ G
  have hzero : ∀ c : G → ℂ, pair 0 c = 0 := by
    intro c
    have := hadd 0 0 c
    rw [add_zero] at this
    linear_combination -this
  revert h
  refine GlobalTheory.T.isCharacterOverSubfield_induction_irreducible ℂ ℂ G (fun α => pair A α ≠ 0 → ∃ φ R R' : G → ℂ, IsIrrChar ℂ ℂ φ ∧ IsChar ℂ ℂ R ∧
    IsChar ℂ ℂ R' ∧ A = φ + R ∧ α = φ + R') ?_ ?_ α hα
  · intro h0
    exact absurd (by rw [hsymm, hzero] : pair A 0 = 0) h0
  · intro φ c hφ hc ih hne
    have hsplit : pair A (φ + c) = pair A φ + pair A c := by
      rw [hsymm A (φ + c), hadd, hsymm φ A, hsymm c A]
    by_cases h1 : pair A φ = 0
    · rw [hsplit, h1, zero_add] at hne
      obtain ⟨ψ, R, R', hψ, hR, hR', hA', hc'⟩ := ih hne
      refine ⟨ψ, R, φ + R', hψ, hR, hcadd _ _ (isChar_of_irr hφ) hR', hA', ?_⟩
      rw [hc']
      abel
    · obtain ⟨R, hR, hAR⟩ := GlobalTheory.T.exists_isChar_eq_add_of_pair_ne_zero' ℂ ℂ G φ A hφ hA h1
      exact ⟨φ, R, c, hφ, hR, hc, hAR, rfl⟩

private theorem irr_one_ne {φ : G → ℂ} (h : IsIrrChar ℂ ℂ φ) : φ 1 ≠ 0 := by
  obtain ⟨n, ρ, hirr, hφ⟩ := h
  rw [hφ, Representation.char_one]
  simp only [Module.finrank_fin_fun, Algebra.algebraMap_self, RingHom.id_apply, ne_eq, Nat.cast_eq_zero]
  rintro rfl
  apply hirr.bot_ne_top
  ext v
  rw [Subsingleton.elim v 0]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

private theorem pair_self_ne {x : G → ℂ} (hx : IsChar ℂ ℂ x) (h : x 1 ≠ 0) : pair x x ≠ 0 := by
  obtain ⟨-, -, hirr, -⟩ := GlobalTheory.T.finiteGroupFunctionPairing_add_nat_pos_symm ℂ ℂ G
  have hx0 : x ≠ 0 := fun e => h (by simp [e])
  obtain ⟨φ, c, hφ, hc, rfl⟩ := GlobalTheory.T.exists_isIrrChar_add_isChar_of_ne_zero ℂ ℂ G x hx hx0
  obtain ⟨n, hn, hpn⟩ := hirr φ hφ
  refine pair_add_ne (isChar_of_irr hφ) hc (isChar_of_irr hφ) hc ?_
  rw [hpn]
  exact_mod_cast hn.ne'

end Group

section Hc

variable {F : Type} [Field F] [Finite F]

private theorem hc_add_left (a b n : ℕ) (α α' : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) :
    hc a b (α + α') β n = hc a b α β n + hc a b α' β n := by
  funext x
  simp only [hc, hcTw, Pi.add_apply]
  rw [← mul_add, ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  congr 1
  refine finsum_congr fun y => ?_
  split_ifs <;> simp [add_mul]

private theorem hc_add_right (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β β' : GL (Fin b) F → ℂ) :
    hc a b α (β + β') n = hc a b α β n + hc a b α β' n := by
  funext x
  simp only [hc, hcTw, Pi.add_apply]
  rw [← mul_add, ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  congr 1
  refine finsum_congr fun y => ?_
  split_ifs <;> simp [mul_add]

end Hc

theorem hcPair : HcChar → HcOne → HcPair := by
  intro hC hO F _ _ a b n hn α A β B hα hA hβ hB hAα hBβ
  have hcC : ∀ (x : GL (Fin a) F → ℂ) (y : GL (Fin b) F → ℂ), IsChar ℂ ℂ x → IsChar ℂ ℂ y →
      IsChar ℂ ℂ (hc a b x y n) :=
    fun x y hx hy => hC F a b n hn x y hx hy
  obtain ⟨-, hcadd⟩ := GlobalTheory.T.isCharacterOverSubfield_zero_and_add ℂ ℂ (GL (Fin n) F)
  rw [pairs_iff _ (hcC A B hA hB)]
  rw [pairs_iff _ hA] at hAα
  rw [pairs_iff _ hB] at hBβ
  obtain ⟨φ, R, R', hφ, hR, hR', rfl, rfl⟩ := common hα hA hAα
  obtain ⟨ψ, S, S', hψ, hS, hS', rfl, rfl⟩ := common hβ hB hBβ
  have hφ' := isChar_of_irr hφ
  have hψ' := isChar_of_irr hψ
  have e1 : hc a b (φ + R) (ψ + S) n =
      hc a b φ ψ n + (hc a b φ S n + (hc a b R ψ n + hc a b R S n)) := by
    rw [hc_add_left, hc_add_right, hc_add_right]
    abel
  have e2 : hc a b (φ + R') (ψ + S') n =
      hc a b φ ψ n + (hc a b φ S' n + (hc a b R' ψ n + hc a b R' S' n)) := by
    rw [hc_add_left, hc_add_right, hc_add_right]
    abel
  rw [e1, e2]
  refine pair_add_ne (hcC _ _ hφ' hψ')
    (hcadd _ _ (hcC _ _ hφ' hS) (hcadd _ _ (hcC _ _ hR hψ') (hcC _ _ hR hS)))
    (hcC _ _ hφ' hψ')
    (hcadd _ _ (hcC _ _ hφ' hS') (hcadd _ _ (hcC _ _ hR' hψ') (hcC _ _ hR' hS'))) ?_
  exact pair_self_ne (hcC _ _ hφ' hψ') (hO F a b n hn φ ψ (irr_one_ne hφ) (irr_one_ne hψ))

end UpperTheory.Gal.InertialTypesAlt
end
end
