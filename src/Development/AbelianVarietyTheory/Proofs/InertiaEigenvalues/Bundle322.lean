module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle296
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.NoGlobalInv

theorem sub_one_mem_of_pow {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {l : ℕ} (hp : l.Prime)
    (hl : (l : Λ) ∈ IsLocalRing.maximalIdeal Λ) (u : Λ) {n : ℕ} (hu : u ^ (l ^ n) = 1) :
    u - 1 ∈ IsLocalRing.maximalIdeal Λ := by
  haveI := Fact.mk hp
  have h0 : ((l : ℕ) : IsLocalRing.ResidueField Λ) = 0 := by
    rw [← map_natCast (IsLocalRing.residue Λ)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hl
  haveI : CharP (IsLocalRing.ResidueField Λ) l := (CharP.charP_iff_prime_eq_zero hp).2 h0
  rw [← IsLocalRing.residue_eq_zero_iff]
  have h1 : (IsLocalRing.residue Λ u - 1) ^ (l ^ n) = 0 := by
    rw [sub_pow_char_pow, ← map_pow, hu]; simp
  simpa using pow_eq_zero_iff (pow_pos hp.pos n).ne' |>.1 h1

theorem exists_socle {Λ M : Type} [CommRing Λ] [AddCommGroup M] [Module Λ M] (I : Ideal Λ) (S : Submodule Λ M) :
    ∀ (n : ℕ) (x : M), x ∈ S → x ≠ 0 → (∀ a ∈ I ^ n, a • x = 0) →
      ∃ y ∈ S, y ≠ 0 ∧ ∀ a ∈ I, a • y = 0 := by
  intro n
  induction n with
  | zero => intro x _ hx h; exact absurd (by simpa using h 1 (by simp)) hx
  | succ n ih =>
    intro x hS hx h
    by_cases h1 : ∀ a ∈ I, a • x = 0
    · exact ⟨x, hS, hx, h1⟩
    push Not at h1
    obtain ⟨a, ha, hax⟩ := h1
    refine ih (a • x) (S.smul_mem a hS) hax fun b hb => ?_
    rw [smul_smul]
    exact h _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hb ha)

theorem eq_zero_of_span {Γ O Λ B : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [Algebra O Λ]
    [AddCommGroup B] [Module Λ B] {r : ℕ} (hr : 2 ≤ r) (ρ : Γ → Matrix (Fin r) (Fin r) O)
    (hρ : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g).map (IsLocalRing.residue O)) = ⊤)
    (x : Fin r → B) (hx : ∀ a ∈ IsLocalRing.maximalIdeal O, ∀ j, algebraMap O Λ a • x j = 0)
    (hs : ∀ g, ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (ρ g p q) • x q = algebraMap O Λ c • x p) : x = 0 := by
  classical
  have key : ∀ M : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O), ∃ A : Matrix (Fin r) (Fin r) O,
      A.map (IsLocalRing.residue O) = M ∧
        ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (A p q) • x q = algebraMap O Λ c • x p := by
    intro M
    have hM : M ∈ Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g).map (IsLocalRing.residue O)) := hρ ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem M h => obtain ⟨g, rfl⟩ := h; exact ⟨ρ g, rfl, hs g⟩
    | zero => exact ⟨0, by ext; simp, 0, by simp⟩
    | add M M' _ _ h h' =>
      obtain ⟨A, rfl, c, hc⟩ := h
      obtain ⟨A', rfl, c', hc'⟩ := h'
      refine ⟨A + A', by ext; simp, c + c', fun p => ?_⟩
      simp only [Matrix.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib, hc, hc']
    | smul t M _ h =>
      obtain ⟨A, rfl, c, hc⟩ := h
      obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
      refine ⟨t • A, by ext; simp, t * c, fun p => ?_⟩
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, mul_smul, ← Finset.smul_sum, hc]
  have key2 : ∀ A : Matrix (Fin r) (Fin r) O,
      ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (A p q) • x q = algebraMap O Λ c • x p := by
    intro A
    obtain ⟨A', hA, c, hc⟩ := key (A.map (IsLocalRing.residue O))
    refine ⟨c, fun p => ?_⟩
    rw [← hc]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : A p q - A' p q ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact (congrFun (congrFun hA p) q).symm
    have := hx _ this q
    rwa [map_sub, sub_smul, sub_eq_zero] at this
  funext b
  haveI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.2 hr
  obtain ⟨a, hab⟩ := exists_ne b
  obtain ⟨c, hc⟩ := key2 (Matrix.single a b 1)
  obtain ⟨c', hc'⟩ := key2 (Matrix.single b b 1)
  have h1 := hc a
  have h2 := hc' a
  have h3 := hc' b
  simp [Matrix.single_apply, hab.symm, apply_ite, ite_smul] at h1 h2 h3
  rw [Pi.zero_apply, h3, h1, smul_comm, ← h2, smul_zero]

theorem invariants_eq_bot {Γ O Λ B : Type} [Group Γ] [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ]
    [Algebra O Λ] [AddCommGroup B] [Module Λ B] {r : ℕ} (hr : 2 ≤ r) (ρ : Γ →* GL (Fin r) O) (χ : Γ →* Oˣ)
    (κ : Γ →* Λˣ) (hloc : IsLocalHom (algebraMap O Λ))
    (hρ : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤)
    (hκ : ∀ g, ((κ g : Λˣ) : Λ) - 1 ∈ IsLocalRing.maximalIdeal Λ) (hB : Tors Λ B) :
    (repOn (twGL ρ χ) κ B).invariants = ⊥ := by
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ a ∈ IsLocalRing.maximalIdeal Λ :=
    fun a ha hu => ha (hloc.map_nonunit a hu)
  rw [eq_bot_iff]
  intro x hx
  by_contra hx0
  choose n hn using fun j => hB (x j)
  obtain ⟨y, hy, hy0, hym⟩ := exists_socle (IsLocalRing.maximalIdeal Λ) _
    (Finset.univ.sup n) x hx hx0 (fun a ha => funext fun j =>
      hn j a (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ j)) ha))
  refine hy0 (eq_zero_of_span (O := O) (Λ := Λ) hr (fun g => (ρ g : Matrix (Fin r) (Fin r) O)) hρ y
    (fun a ha j => congrFun (hym _ (hm a ha)) j) fun g => ⟨(χ g : O), fun p => ?_⟩)
  have hk' : ∀ q, ((κ g : Λˣ) : Λ) • y q = y q := fun q => by
    have := congrFun (hym _ (hκ g)) q
    rwa [Pi.smul_apply, sub_smul, one_smul, Pi.zero_apply, sub_eq_zero] at this
  have hg : ((κ g : Λˣ) : Λ) • ∑ q, algebraMap O Λ ((twGL ρ χ g : Matrix (Fin r) (Fin r) O) p q) • y q = y p :=
    congrFun (hy g) p
  rw [← hg, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_comm ((κ g : Λˣ) : Λ), hk', smul_smul, ← map_mul]
  congr 2
  simp [twGL, scalGL, Matrix.diagonal_mul]

theorem noInv (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
    (Q : Finset (PlE D.host)) (h : Setup bkP i s κ Q) : NoInv i s κ := by
  intro B _ _ _ _ hB
  have hloc := h.2.1
  have hr : 100 ≤ D.R.r := h.1.2.2.2.2.2.2
  have hl0 : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu =>
    X.O_l i (by simpa using hu.map (algebraMap (X.O0 i) (X.O i)))
  have hl : ((X.l i : ℕ) : Λ) ∈ IsLocalRing.maximalIdeal Λ := fun hu =>
    hl0 (hloc.map_nonunit _ (by simpa using hu))
  refine invariants_eq_bot (by omega) (X.rhoS i s) (chiS i s) κ hloc h.1.2.1.1 (fun g => ?_) hB
  obtain ⟨m, hgm⟩ := h.2.2.2.2.1 g
  exact sub_one_mem_of_pow (X.lPrime i).out hl _ (n := m)
    (by rw [← Units.val_pow_eq_pow_val, hgm, Units.val_one])

end GlobalTheory.NoGlobalInv
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwSys


open Classical in
theorem aeval_gen_sub_one_surjective (O : Type) [CommRing O] (n : ℕ) [NeZero n] (ι : Type) [Fintype ι] :
    Function.Surjective (MvPolynomial.aeval (R := O) fun q : ι =>
      MonoidAlgebra.of O (Multiplicative (ι → ZMod n)) (Multiplicative.ofAdd (Pi.single q 1)) - 1) := by
  set φ := (MvPolynomial.aeval (R := O) fun q : ι =>
      MonoidAlgebra.of O (Multiplicative (ι → ZMod n)) (Multiplicative.ofAdd (Pi.single q 1)) - 1) with hφ
  have hg : ∀ g : Multiplicative (ι → ZMod n), MonoidAlgebra.of O _ g ∈ φ.range := by
    intro g
    refine ⟨∏ q, (MvPolynomial.X q + 1) ^ (Multiplicative.toAdd g q).val, ?_⟩
    have h1 : g = ∏ q, (Multiplicative.ofAdd (Pi.single q (1 : ZMod n) : ι → ZMod n)) ^ (Multiplicative.toAdd g q).val := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      funext j
      simp only [toAdd_pow, toAdd_ofAdd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_one, ZMod.natCast_zmod_val]
    conv_rhs => rw [h1]
    simp only [hφ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod, map_pow, map_add (f := _), map_one,
      MvPolynomial.aeval_X, sub_add_cancel]
  intro x
  change x ∈ φ.range
  induction x using MonoidAlgebra.induction_on with
  | of g => exact hg g
  | add f g hf hg => exact add_mem hf hg
  | smul r f hf => exact Subalgebra.smul_mem _ hf r

theorem toLam_surjective {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)
    (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] : Function.Surjective (toLam X i M ι) := by
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  exact aeval_gen_sub_one_surjective (X.O0 i) (X.l i ^ M) ι

theorem SlopeTestRemainingChoices.empty {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
    {i : X.Tw} {M : ℕ} {A : Finset (PlE D.host)} {ι : Type} {P : ι → PlE D.host} {d}
    (h : SlopeTestRemainingChoices X i M A P d) : SlopeTestRemainingChoices X i M ∅ P d := by
  refine ⟨fun q v hv => ?_, h.2⟩
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := h.1 q v hv
  exact ⟨h1, h2, h3, h4, Finset.notMem_empty _, h6⟩

theorem galois_twisted_selmer_auxprimes_of_matrix_and_bounds : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂)
    (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X),
    ThmS bkP → SelmerLengthsByDeterminant bkP → ResidualBoundOddPrimes bkP → ThmC bkP → GaloisSideTwistedSelmerAuxiliaryPrimes bkP := by
  intro D N X bkP hS hS4 h103 hC i T hT
  have hO : OrdBound bkP i (IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i)) := by
    rcases Nat.eq_zero_or_pos (nu X i) with h | h
    · rw [h, pow_zero, IsDiscreteValuationRing.addVal_one]
      exact h103 i h
    · exact hC i h
  obtain ⟨R, Dd, M₀, hM₀⟩ := hO T hT
  refine ⟨R, Dd, max M₀ 1, le_max_right _ _, fun M hM H S d hF z hz H' ho hn A => ?_⟩
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨P, hA, hSt, hP⟩ := hM₀ M (le_trans (le_max_left _ _) hM) H S d hF z hz H' ho hn A
  refine ⟨P, hA, hSt, fun s hs Q hQ => ?_⟩
  obtain ⟨a, Φ, hΦ, -⟩ := hS i s (hT s hs) M _ P _ Q hM1 hA.empty hQ
  obtain ⟨F, hFΦ⟩ := toLam_surjective X i M (Fin R ⊕ Fin R) Φ.det
  exact ⟨F, hS4 i s M _ P _ Q hM1 hA.empty hQ a Φ hΦ F hFΦ, hP s hs Q hQ a Φ hΦ F hFΦ⟩

end GlobalTheory.TwSys
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun

namespace GlobalTheory.Growth

section Chg

variable {R R' : Type} [CommRing R] [CommRing R'] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [ContinuousConstSMul R' M]
  (rho : Representation R Γ M) (rho' : Representation R' Γ M) (h : ∀ g m, rho g m = rho' g m)

theorem mk_eq_mk_iff (z w : Z1 rho) : (Submodule.Quotient.mk z : H1 rho) = Submodule.Quotient.mk w ↔
    ∃ m, ∀ g, z.1 g - w.1 g = rho g m - m := by
  rw [Submodule.Quotient.eq]
  exact mem_coboundaries1 rho _

def chgZ (z : Z1 rho) : Z1 rho' := ⟨z.1, z.2.1, fun g k => by rw [← h]; exact z.2.2 g k⟩

def chg : H1 rho → H1 rho' :=
  Quotient.map' (chgZ rho rho' h) fun z w hzw => by
    obtain ⟨m, hm⟩ := (mk_eq_mk_iff rho z w).1 (Quotient.sound' hzw)
    exact Quotient.exact' ((mk_eq_mk_iff rho' _ _).2 ⟨m, fun g => by rw [← h]; exact hm g⟩)

theorem chg_mk (z : Z1 rho) : chg rho rho' h (Submodule.Quotient.mk z) = Submodule.Quotient.mk (chgZ rho rho' h z) := rfl

theorem chg_zero : chg rho rho' h 0 = 0 := rfl

theorem chg_add (x y : H1 rho) : chg rho rho' h (x + y) = chg rho rho' h x + chg rho rho' h y := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
  induction y using Submodule.Quotient.induction_on with
  | H w => rfl

theorem chg_smul (a : R) (a' : R') (ha : ∀ m : M, a • m = a' • m) (x : H1 rho) :
    chg rho rho' h (a • x) = a' • chg rho rho' h x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [← Submodule.Quotient.mk_smul, chg_mk, chg_mk, ← Submodule.Quotient.mk_smul]
    exact congrArg _ (Subtype.ext (funext fun g => ha _))

theorem chg_mem_span (hs : ∀ a : R, ∃ a' : R', ∀ m : M, a • m = a' • m) {S : Set (H1 rho)} {T : Submodule R' (H1 rho')}
    (hS : ∀ x ∈ S, chg rho rho' h x ∈ T) {x : H1 rho} (hx : x ∈ Submodule.span R S) : chg rho rho' h x ∈ T := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [chg_zero]; exact T.zero_mem
  | add x y _ _ hx hy => rw [chg_add]; exact T.add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨a', ha⟩ := hs a
    rw [chg_smul _ _ _ a a' ha]
    exact T.smul_mem a' hx

theorem chg_chg (x : H1 rho) : chg rho' rho (fun g m => (h g m).symm) (chg rho rho' h x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem res_chg {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (chg rho rho' h x) =
      chg (rho.comp phi) (rho'.comp phi) (fun g m => h (phi g) m) (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem chg_ur (J : Subgroup Γ) (x : H1 rho) (hx : x ∈ H1ur rho J) : chg rho rho' h x ∈ H1ur rho' J := by
  have h0 : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (res_chg rho rho' h J.subtype continuous_subtype_val x).trans
    ((congrArg _ h0).trans (chg_zero _ _ _))

end Chg

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw)

section Sel

variable {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ Λ' : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] [CommRing Λ']
  [Algebra (X.O0 i) Λ'] (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ)
  {B : Type} [AddCommGroup B] [Module Λ B] [Module Λ' B] [TopologicalSpace B] [DiscreteTopology B]
  (h : ∀ g m, repOn ρ κ B g m = repOn ρ κ' B g m) (hs : ∀ a : Λ, ∃ a' : Λ', ∀ b : B, a • b = a' • b)
  (ho : ∀ (y : X.O0 i) (b : B), algebraMap (X.O0 i) Λ y • b = algebraMap (X.O0 i) Λ' y • b)

include hs ho

theorem chg_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ κ B).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ B v) :
    chg _ ((repOn ρ κ' B).comp (DecV N v).subtype) (fun g m => h g.1 m) x ∈ bkOn bkP i ρ κ' B v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · refine chg_mem_span _ _ _ (fun a => (hs a).imp fun a' ha m => funext fun c => ha (m c)) ?_ hx
    rintro x ⟨z, c, y, b, hc, hy, hz, rfl⟩
    exact Submodule.subset_span ⟨chgZ _ _ (fun g m => h g.1 m) z, c, y, b, hc, hy,
      fun g a => (hz g a).trans (ho _ _), rfl⟩
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx]
    exact chg_zero _ _ _

theorem chg_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ B))
    (hx : x ∈ selOn bkP i ρ κ B Q) : chg _ (repOn ρ κ' B) h x ∈ selOn bkP i ρ κ' B Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_chg (repOn ρ κ B) (repOn ρ κ' B) h (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact chg_mem_bkOn bkP i ρ κ κ' h hs ho v _ hv
  · exact Submodule.mem_top
  · exact chg_ur _ _ _ _ _ hv

end Sel

def Represents {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {R : Type} [CommRing R] [Algebra (X.O0 i) R] (κ : GE N →* Rˣ)
    (Q : Finset (PlE D.host)) {a : ℕ} (Ψ : Matrix (Fin a) (Fin a) R) : Prop :=
  ∃ E : ∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B],
      (Fin a → B) → H1 (repOn ρ κ B),
    (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u : Fin a → B),
      matAct Ψ u = 0 → E B u ∈ selOn bkP i ρ κ B Q) ∧
    (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u u' : Fin a → B),
      matAct Ψ u = 0 → matAct Ψ u' = 0 → E B u = E B u' → u = u') ∧
    (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B],
      ∀ y ∈ selOn bkP i ρ κ B Q, ∃ u, matAct Ψ u = 0 ∧ E B u = y) ∧
    ∀ (B B' : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B]
      [AddCommGroup B'] [Module R B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[R] B') (u : Fin a → B),
      matAct Ψ u = 0 → E B' (fun c => f (u c)) = h1Map ρ κ f (E B u)

variable {bkP i}

theorem represents_of_computes {s : X.Sig i} {M : ℕ} {ι : Type} {d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))}
    {Q : Finset (PlE D.host)} {a : ℕ} {Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)} (hΦ : Computes bkP i s M d Q Φ)
    {R : Type} [CommRing R] [Algebra (X.O0 i) R] (p : abelian₂ X i M ι →ₐ[X.O0 i] R) (hp : Function.Surjective p)
    (κ : GE N →* Rˣ) (hκ : ∀ g, p (delInv i M d g : (abelian₂ X i M ι)ˣ) = κ g) (n : ℕ) (hn : ((X.l i ^ n : ℕ) : R) = 0) :
    Represents bkP i (Tgl i s) κ Q (Φ.map p) := by
  classical
  obtain ⟨e, he⟩ := hΦ
  have tor : ∀ (B : Type) [AddCommGroup B] [Module R B], ∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0 := fun B _ _ b =>
    ⟨n, by rw [← Nat.cast_smul_eq_nsmul R, hn, zero_smul]⟩
  let inst : ∀ (B : Type) [AddCommGroup B] [Module R B], Module (abelian₂ X i M ι) B := fun B _ _ =>
    Module.compHom B p.toRingHom
  have hsm : ∀ (B : Type) [AddCommGroup B] [Module R B] (x : abelian₂ X i M ι) (b : B), x • b = p x • b := fun _ _ _ _ _ => rfl
  have hk : ∀ (B : Type) [AddCommGroup B] [Module R B] (u : Fin a → B), matAct (Φ.map p) u = matAct Φ u :=
    fun _ _ _ _ => rfl
  have ho : ∀ (B : Type) [AddCommGroup B] [Module R B] (y : X.O0 i) (b : B),
      algebraMap (X.O0 i) (abelian₂ X i M ι) y • b = algebraMap (X.O0 i) R y • b := fun B _ _ y b => by
    rw [hsm, AlgHom.commutes]
  have hr : ∀ (B : Type) [AddCommGroup B] [Module R B] g m,
      repOn (Tgl i s) (delInv i M d) B g m = repOn (Tgl i s) κ B g m := fun B _ _ g m => by
    funext c
    change (delInv i M d g : abelian₂ X i M ι) • ∑ j, algebraMap (X.O0 i) (abelian₂ X i M ι) _ • m j =
      (κ g : R) • ∑ j, algebraMap (X.O0 i) R _ • m j
    rw [hsm, hκ]
    simp only [ho]
  refine ⟨fun B _ _ _ _ u => if h : matAct Φ u = 0 then chg _ _ (hr B) (e B (tor B) ⟨u, h⟩).1 else 0,
    fun B _ _ _ _ u hu => ?_, fun B _ _ _ _ u u' hu hu' huu => ?_, fun B _ _ _ _ y hy => ?_,
    fun B B' _ _ _ _ _ _ _ _ f u hu => ?_⟩
  · rw [hk] at hu
    simp only [dif_pos hu]
    exact chg_mem_selOn bkP i _ _ _ (hr B) (fun x => ⟨p x, hsm B x⟩) (ho B) Q _ (e B (tor B) ⟨u, hu⟩).2
  · rw [hk] at hu hu'
    simp only [dif_pos hu, dif_pos hu'] at huu
    have h1 := congrArg (chg _ _ fun g m => (hr B g m).symm) huu
    rw [chg_chg, chg_chg] at h1
    exact congrArg Subtype.val ((e B (tor B)).injective (Subtype.ext h1))
  · have h1 := chg_mem_selOn bkP i _ _ _ (fun g m => (hr B g m).symm)
      (fun x => by obtain ⟨x', rfl⟩ := hp x; exact ⟨x', fun b => (hsm B x' b).symm⟩) (fun y b => (ho B y b).symm) Q y hy
    obtain ⟨u, hu⟩ := (e B (tor B)).surjective ⟨_, h1⟩
    have hu0 : matAct Φ u.1 = 0 := u.2
    refine ⟨u.1, hu0, ?_⟩
    simp only [dif_pos hu0]
    rw [show (⟨u.1, hu0⟩ : LinearMap.ker (matAct (M := B) Φ)) = u from rfl, hu]
    exact chg_chg _ _ _ y
  · rw [hk] at hu
    let f' : B →ₗ[abelian₂ X i M ι] B' := ⟨f.toAddHom, fun x b => f.map_smul (p x) b⟩
    have hu' : matAct Φ (fun c => f (u c)) = 0 := by
      show matAct Φ (fun c => f' (u c)) = 0
      funext c
      have := congrArg f' (congrFun hu c)

      simpa [matAct, map_sum] using this
    simp only [dif_pos hu, dif_pos hu']
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (e B (tor B) ⟨u, hu⟩).1
    rw [he B B' (tor B) (tor B') f' ⟨u, hu⟩ ⟨_, hu'⟩ z (cocycles1MapOfEquivariant _ _ (f'.compLeft _) continuous_of_discreteTopology
      (repOn_map _ _ f') z) (fun _ => rfl) (fun _ _ => rfl) hz.symm, ← hz]
    rfl

end GlobalTheory.Growth
end
end

section

noncomputable section

namespace GlobalTheory.LocCongrRoad

open GlobalTheory.LiftLeaf GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

private theorem foldr_lpSum_lpTw_lpChar (hL : CharSum N A) {w : PlE H} (x c : A.LP w) (hc : A.lpDim c = 1)
    (s : ℝ) (L : List ℝ) :
    L.foldr (fun k acc => A.lpSum (A.lpTw (A.lpChar x c) (s - k)) acc) (A.lpZero w) =
      A.lpChar (L.foldr (fun k acc => A.lpSum (A.lpTw x (s - k)) acc) (A.lpZero w)) c := by
  induction L with
  | nil => exact ((hL w (A.lpZero w) (A.lpZero w) c 0 hc).2.2).symm
  | cons k L ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, (hL w _ _ c 0 hc).1, (hL w _ (A.lpZero w) c _ hc).2.1]

theorem spehLoc_twist (hL : CharSum N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  unfold spehLoc
  simp only [A.locG_tw]
  exact foldr_lpSum_lpTw_lpChar N A hL (A.locG p.π w) (A.locG χ w) (A.locG_dim χ w) _ _

theorem isoLoc_twist (hL : CharSum N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hχ : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction S with
  | nil => exact ((hL w (A.lpZero w) (A.lpZero w) (A.locG χ w) 0 hχ).2.2).symm
  | cons p S ih =>
    change A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [spehLoc_twist N A hL p χ w, ih, (hL w _ _ _ 0 hχ).1]

theorem isoLoc_append_singleton (S : List (Part A.CG)) (q : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [q]) w = A.lpSum (isoLoc N A S w) (spehLoc N A q w) := by
  induction S with
  | nil => exact A.lpSum_comm _ _
  | cons p S ih =>
    change A.lpSum (spehLoc N A p w) (isoLoc N A (S ++ [q]) w) =
      A.lpSum (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (spehLoc N A q w)
    rw [ih, A.lpSum_assoc]

end GlobalTheory.LocCongrRoad
end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.card_cocycles_independent_mod_coboundaries_le : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (Dt : TopData n m) (N : Lats k n m), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ABC D Dt.w Dt.wst N → (∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen (D.γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen (D.γ i) (N i) (a : k) = m ∧ EPoly (D.γ i) (N i) (Dt.wst i + 1))) → ∀ (s : ℕ) (z : Fin s → (ZMod n → Vc k m) × (ZMod n → Vc k m)), (∀ a, InZZ D Dt N (z a).1 (z a).2) → LinearIndependent k (fun a => (herrB D).mkQ (z a)) → s ≤ Dt.dsum := by
  first | exact @GlobalTheory.Models.PolarBound.main | exact GlobalTheory.Models.PolarBound.main | (intros; apply GlobalTheory.Models.PolarBound.main <;> assumption)
end
