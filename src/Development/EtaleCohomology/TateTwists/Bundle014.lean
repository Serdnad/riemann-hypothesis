module

public import Development.EtaleCohomology.TateTwists.Bundle006
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.TateTwists.Bundle008
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
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

open Polynomial

noncomputable section
set_option linter.unusedSectionVars false

namespace LateralTheory.EtaleFoundations.TwFlat
open GlobalTheory.EtC

variable {q : ℕ} {A : Type} [CommRing A]

theorem prim_pow_q (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, aeval_X, map_one] at h
  exact sub_eq_zero.1 h

theorem pow_mod_q (ζ : Prim q A) (n : ℕ) : ζ.1 ^ (n % q) = ζ.1 ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, prim_pow_q, one_pow, one_mul]

theorem pow_val_one (ζ : Prim q A) : ζ.1 ^ (1 : ZMod q).val = ζ.1 := by
  rw [ZMod.val_one_eq_one_mod, pow_mod_q, pow_one]

theorem pow_val_mul (ζ : Prim q A) (a b : ZMod q) : ζ.1 ^ (a * b).val = (ζ.1 ^ a.val) ^ b.val := by
  rw [ZMod.val_mul, pow_mod_q, pow_mul]

theorem val_inj [NeZero q] [Nontrivial A] (ζ : Prim q A) (a b : ZMod q) (h : ζ.1 ^ a.val = ζ.1 ^ b.val) : a = b := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let π : A →+* A ⧸ m := Ideal.Quotient.mk m
  have : NeZero ((q : ℕ) : A ⧸ m) := ⟨by
    have hu := ζ.2.1.map π
    rw [map_natCast] at hu
    exact hu.ne_zero⟩
  have hr : IsRoot (cyclotomic q (A ⧸ m)) (π ζ.1) := by
    have h2 := aeval_algHom_apply π.toIntAlgHom ζ.1 (cyclotomic q ℤ)
    rw [ζ.2.2, map_zero] at h2
    rw [IsRoot, ← map_cyclotomic q (algebraMap ℤ (A ⧸ m)), eval_map_algebraMap]
    exact h2
  have hp : IsPrimitiveRoot (π ζ.1) q := (isRoot_cyclotomic_iff).1 hr
  have h3 : (π ζ.1) ^ a.val = (π ζ.1) ^ b.val := by rw [← map_pow, ← map_pow, h]
  exact ZMod.val_injective q (hp.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h3)

end LateralTheory.EtaleFoundations.TwFlat

namespace LateralTheory.EtaleFoundations.TwFlat
open GlobalTheory.EtC

variable (q : ℕ) [NeZero q] (A : Type) [CommRing A]

def Rel (ζ ξ : Prim q A) : Prop := ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val

def St : Setoid (Prim q A) where
  r := Rel q A
  iseqv := by
    refine ⟨fun ζ => ⟨1, by rw [Units.val_one, pow_val_one]⟩, ?_, ?_⟩
    · rintro ζ ξ ⟨a, h⟩
      refine ⟨a⁻¹, ?_⟩
      rw [h, ← pow_val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, pow_val_one]
    · rintro ζ ξ η ⟨a, h⟩ ⟨b, h'⟩
      exact ⟨a * b, by rw [h', h, Units.val_mul, pow_val_mul]⟩

variable {q A}

def rep (ξ : Prim q A) : Prim q A := (Quotient.mk (St q A) ξ).out

theorem rep_rel (ξ : Prim q A) : Rel q A (rep ξ) ξ := Quotient.mk_out (s := St q A) ξ

def cc (ξ : Prim q A) : (ZMod q)ˣ := (rep_rel ξ).choose

theorem cc_spec (ξ : Prim q A) : ξ.1 = (rep ξ).1 ^ (cc ξ : ZMod q).val := (rep_rel ξ).choose_spec

theorem rep_eq {ζ ξ : Prim q A} (h : Rel q A ζ ξ) : rep ζ = rep ξ := by
  unfold rep; rw [Quotient.sound (s := St q A) h]

theorem cc_mul [Nontrivial A] {ζ ξ : Prim q A} (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    cc ξ = cc ζ * a := by
  apply Units.ext
  apply val_inj (rep ξ)
  rw [← cc_spec ξ, Units.val_mul, pow_val_mul, ← rep_eq ⟨a, h⟩, ← cc_spec ζ, h]

theorem cc_out [Nontrivial A] (o : Quotient (St q A)) : cc o.out = 1 := by
  have hr : rep o.out = o.out := by
    show (Quotient.mk (St q A) o.out).out = o.out
    rw [Quotient.out_eq]
  apply Units.ext
  apply val_inj o.out
  have h := cc_spec o.out
  rw [hr] at h
  rw [← h, Units.val_one, pow_val_one]

end LateralTheory.EtaleFoundations.TwFlat

namespace LateralTheory.EtaleFoundations.TwFlat
open GlobalTheory.EtC

variable {q : ℕ} [NeZero q] {A : Type} [CommRing A]

def wt (i : ℤ) (ξ : Prim q A) : ULift.{1} (ZMod q) := ULift.up (((cc ξ ^ i : (ZMod q)ˣ)) : ZMod q)

def psi0 (i : ℤ) : (Prim q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] (Quotient (St q A) →₀ ULift.{1} (ZMod q)) :=
  Finsupp.linearCombination _ fun ξ => Finsupp.single (Quotient.mk (St q A) ξ) (wt i ξ)

theorem primitive_roots_twisted_weight_map_single (i : ℤ) (ξ : Prim q A) (r : ULift.{1} (ZMod q)) :
    psi0 i (Finsupp.single ξ r) = Finsupp.single (Quotient.mk (St q A) ξ) (r * wt i ξ) := by
  rw [psi0, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul]

theorem rel_le [Nontrivial A] (i : ℤ) : twRel q i A ≤ LinearMap.ker (psi0 i) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, primitive_roots_twisted_weight_map_single]
  rw [sub_eq_zero, Quotient.sound (s := St q A) (⟨a, h⟩ : Rel q A ζ ξ)]
  congr 1
  apply ULift.ext
  simp only [wt, ULift.mul_down, cc_mul a h, mul_zpow, Units.val_mul, one_mul]
  ring

def phi [Nontrivial A] (i : ℤ) : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)]
    (Quotient (St q A) →₀ ULift.{1} (ZMod q)) := (twRel q i A).liftQ (psi0 i) (rel_le i)

def theta (i : ℤ) : (Quotient (St q A) →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)]
    ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) :=
  (twRel q i A).mkQ ∘ₗ Finsupp.lmapDomain _ _ (fun o : Quotient (St q A) => o.out)

theorem phi_theta [Nontrivial A] (i : ℤ) : phi i ∘ₗ theta (q := q) (A := A) i = LinearMap.id := by
  refine Finsupp.lhom_ext fun o r => ?_
  simp only [theta, phi, LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Submodule.mkQ_apply, Submodule.liftQ_apply, primitive_roots_twisted_weight_map_single, LinearMap.id_apply]
  rw [Quotient.out_eq]
  congr 1
  rw [wt, cc_out, one_zpow, Units.val_one]
  apply ULift.ext
  simp

theorem theta_phi [Nontrivial A] (i : ℤ) : theta i ∘ₗ phi (q := q) (A := A) i = LinearMap.id := by
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ξ r => ?_)
  simp only [theta, phi, LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Submodule.mkQ_apply, Submodule.liftQ_apply, primitive_roots_twisted_weight_map_single, LinearMap.id_apply]
  refine (Submodule.Quotient.eq _).2 ?_
  have hm : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) - Finsupp.single (rep ξ) (ULift.up ((cc ξ ^ i : (ZMod q)ˣ) : ZMod q))
      ∈ twRel q i A := Submodule.subset_span ⟨rep ξ, ξ, cc ξ, cc_spec ξ, rfl⟩
  have h2 := Submodule.smul_mem _ r hm
  rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one] at h2
  rw [← neg_mem_iff, neg_sub]
  exact h2

theorem flat_of_nontrivial [Nontrivial A] (i : ℤ) :
    Module.Flat (ULift.{1} (ZMod q)) ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) :=
  Module.Flat.of_linearEquiv (LinearEquiv.ofLinearMap (phi i) (theta i) (phi_theta i) (theta_phi i))

end LateralTheory.EtaleFoundations.TwFlat

namespace LateralTheory.EtaleFoundations.TwFlat
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem shf_loc (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    (∀ (U : Scheme.{0}) (y : Sec ((presheafToSheaf Scheme.etaleTopology _).obj P) U),
      Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology P).app (op V)).hom x = Sec.res g y) ∧
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = 0 →
      Loc U fun _ g => (P.map g.op).hom x = 0) := by
  constructor
  · intro U y
    refine ⟨Presheaf.imageSieve (toSheafify Scheme.etaleTopology P) y,
      Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) y, ?_⟩
    rintro V g ⟨t, ht⟩
    exact ⟨t, ht⟩
  · intro U x hx
    have h : (toSheafify Scheme.etaleTopology P).app (op U) x = (toSheafify Scheme.etaleTopology P).app (op U) 0 := by
      change ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0
      rw [hx, map_zero]
    refine ⟨Presheaf.equalizerSieve (F := P) (X := op U) x 0,
      Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) x 0 h, ?_⟩
    intro V g hg
    have hg' : (P.map g.op).hom x = (P.map g.op).hom 0 := hg
    rw [hg', map_zero]

end LateralTheory.EtaleFoundations.TwFlat


open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_sections_flat_of_quotient_iso : LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat := by
  intro q _ i
  obtain ⟨h1, h2⟩ := LateralTheory.EtaleFoundations.TwFlat.shf_loc (ZMod q) (Scheme.Γ ⋙ twF q i)
  refine ⟨Scheme.Γ ⋙ twF q i, toSheafify Scheme.etaleTopology _, h1, h2, fun U hU => ?_⟩
  have : Nonempty (⊤ : U.Opens) := ⟨⟨hU.some, trivial⟩⟩
  exact LateralTheory.EtaleFoundations.TwFlat.flat_of_nontrivial (A := Γ(U, ⊤)) i
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

def leaf_acyc : Prop := ∀ (N k : ℕ) (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.d N c = 0 →
  ∃ b : Pr N →₀ ℤ, Pr.Deg (k + 2) b ∧ Pr.d N b = c

def leaf_dbd : Prop := ∀ (N : ℕ) (c : Pr N →₀ ℤ), Pr.d (N + 1) (Pr.bd c) = Pr.bd (Pr.d N c)

def leaf_bdbd : Prop := ∀ (N : ℕ) (c : Pr N →₀ ℤ), Pr.bd (Pr.bd c) = 0

def leaf_aw : Prop := ∀ N : ℕ, Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N)

def leaf_wa : Prop := ∀ N : ℕ, Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N)

lemma deg_zero {N k : ℕ} : Pr.Deg k (0 : Pr N →₀ ℤ) := by
  intro z hz; simp at hz

lemma deg_sub {N k : ℕ} {a b : Pr N →₀ ℤ} (ha : Pr.Deg k a) (hb : Pr.Deg k b) : Pr.Deg k (a - b) := by
  intro z hz
  rcases Finset.mem_union.1 (Finsupp.support_sub hz) with h | h
  · exact ha z h
  · exact hb z h

lemma deg_bd {N k : ℕ} {c : Pr N →₀ ℤ} (hc : Pr.Deg k c) : Pr.Deg k (Pr.bd c) := by
  intro z hz
  unfold Pr.bd at hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have h2 := Finsupp.support_smul hi
  unfold Pr.push at h2
  simp only [Finsupp.lmapDomain_apply] at h2
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h2)
  exact hc w hw

lemma deg_aw (N : ℕ) : Pr.Deg N (Pr.aw N) := by
  intro z hz
  unfold Pr.aw at hz
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have := Finsupp.support_single_subset hp
  rw [Finset.mem_singleton] at this
  subst this
  have := p.isLt
  show (p : ℕ) + (N - p) = N
  omega

lemma deg_wa (N : ℕ) : Pr.Deg N (Pr.wa N) := by
  intro z hz
  unfold Pr.wa at hz
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have := Finsupp.support_single_subset hp
  rw [Finset.mem_singleton] at this
  subst this
  have := p.isLt
  show (N - p) + (p : ℕ) = N
  omega

lemma bd_sub {N : ℕ} (a b : Pr N →₀ ℤ) : Pr.bd (a - b) = Pr.bd a - Pr.bd b := by
  unfold Pr.bd
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, smul_sub]

lemma bd_zero {N : ℕ} : Pr.bd (0 : Pr N →₀ ℤ) = 0 := by
  simpa using bd_sub (0 : Pr N →₀ ℤ) 0

lemma aw_zero_eq : Pr.aw 0 = Pr.wa 0 := by
  simp [Pr.aw, Pr.wa]

def Good (N : ℕ) (x : Pr N →₀ ℤ) : Prop :=
  Pr.Deg (N + 1) x ∧ Pr.bd (Pr.aw N - Pr.wa N - Pr.d N x) = 0

lemma step (hA : leaf_acyc) (hD : leaf_dbd) (hB : leaf_bdbd) (hAW : leaf_aw) (hWA : leaf_wa)
    (N : ℕ) (x : Pr N →₀ ℤ) (hx : Good N x) :
    ∃ y : Pr (N + 1) →₀ ℤ, Good (N + 1) y ∧ Pr.d (N + 1) y + Pr.bd x = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  set c := Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd x with hcdef
  have hcdeg : Pr.Deg (N + 1) c := deg_sub (deg_sub (deg_aw _) (deg_wa _)) (deg_bd hx.1)
  have hcyc : Pr.d (N + 1) c = 0 := by
    rw [hcdef, map_sub, map_sub, hAW, hWA, hD, ← bd_sub, ← bd_sub]
    exact hx.2
  obtain ⟨b, hbdeg, hb⟩ := hA (N + 1) N c hcdeg hcyc
  refine ⟨b, ⟨hbdeg, ?_⟩, ?_⟩
  · have : Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.d (N + 1) b = Pr.bd x := by
      rw [hb, hcdef]; abel
    rw [this]; exact hB N x
  · rw [hb, hcdef]; abel

lemma good_zero : Good 0 0 := by
  refine ⟨deg_zero, ?_⟩
  rw [aw_zero_eq, map_zero, sub_self, sub_zero, bd_zero]

end LateralTheory.EtaleFoundations.SteenPf

open LateralTheory.EtaleFoundations.SteenPf in
theorem LateralTheory.EtaleFoundations.etale_prism_alexander_whitney_homotopy_of_relations (hA : leaf_acyc) (hD : leaf_dbd) (hB : leaf_bdbd)
    (hAW : leaf_aw) (hWA : leaf_wa) : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := by
  classical
  let seq : ∀ N, {x : Pr N →₀ ℤ // Good N x} := fun N =>
    Nat.rec (motive := fun N => {x : Pr N →₀ ℤ // Good N x}) ⟨0, good_zero⟩
      (fun N x => ⟨Classical.choose (step hA hD hB hAW hWA N x.1 x.2),
        (Classical.choose_spec (step hA hD hB hAW hWA N x.1 x.2)).1⟩) N
  refine ⟨fun N => (seq N).1, fun N => (seq N).2.1, ?_, fun N => ?_⟩
  · show Pr.d 0 0 = _
    rw [map_zero, aw_zero_eq, sub_self]
  · exact (Classical.choose_spec (step hA hD hB hAW hWA N (seq N).1 (seq N).2)).2
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleSimplicialCochainEvaluationAdditive : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x

def EtaleSimplicialCochainEvaluationRestrictionNaturality : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)

def EtaleSimplicialCochainExtOfEvaluation : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β

def EtaleSimplicialCochainEvaluationPrecompSpaceMap : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)

def EtaleSimplicialCochainEvaluationPostcompComplexMap : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

end LateralTheory.EtaleFoundations

namespace LateralTheory.EtaleFoundations.BasicPf
variable {R : Type} [CommRing R]

lemma app_add {A B : Shv R} (φ ψ : A ⟶ B) (U : Scheme.{0}) (y : Sec A U) :
    ((φ + ψ).hom.app (op U)).hom y = (φ.hom.app (op U)).hom y + (ψ.hom.app (op U)).hom y := by
  rfl

noncomputable def evH {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
  AddMonoidHom.mk' (fun α => ev α p s h U x) (by
    intro α β
    show ((((chainsXIso R E p).inv ≫ (α + β).v _ _ h).hom.app (op U))).hom _ = _
    rw [Cochain.add_v, Preadditive.comp_add, app_add]
    rfl)

theorem lin : EtaleSimplicialCochainEvaluationAdditive := by
  intro R _ E I n α β p s h U x
  exact ⟨map_add (evH p s h U x) α β, map_sub (evH p s h U x) α β, map_zero (evH p s h U x),
    fun c => map_zsmul (evH p s h U x) c α⟩

theorem cx : EtaleSimplicialCochainEvaluationPostcompComplexMap := by
  intro R _ E I n J m α p s h U x
  show ((((chainsXIso R E p).inv ≫ (α.comp (Cochain.ofHom m) (add_zero n)).v _ _ h).hom.app (op U))).hom _ = _
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

lemma freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen Sec.res
  erw [← ConcreteCategory.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply]
  congr 1
  exact ModuleCat.free_map_apply _ _

theorem nat : EtaleSimplicialCochainEvaluationRestrictionNaturality := by
  intro R _ E I n α p s h V U g x
  show Sec.res g ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U)).hom (freeGen R _ U x)) =
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op V)).hom (freeGen R _ V (x.res g)))
  rw [show x.res g = (E.obj (op (SimplexCategory.mk p))).map g.op x from rfl, ← freeGen_res]
  simp only [Sec.res]
  exact (congrArg (fun f => ModuleCat.Hom.hom f (freeGen R _ U x))
    (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)).symm

lemma freeGen_map {P Q : PSh} (η : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map η).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (η.app (op U) x) := by
  unfold freeGen
  erw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← toSheafify_naturality, NatTrans.comp_app, ConcreteCategory.comp_apply]
  congr 1
  exact ModuleCat.free_map_apply _ _

theorem spc : LateralTheory.EtaleFoundations.EtaleSimplicialCochainEvaluationPrecompSpaceMap := by
  intro R _ E I n E' f α p s h U x
  have key : (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p:ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
    simp only [chains, chainsXIso, Functor.comp_map]
    erw [HomologicalComplex.extendMap_f _ _ (i := p) rfl, Iso.inv_hom_id_assoc]
    rfl
  show ((((chainsXIso R E' p).inv ≫ ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)).v _ _ h).hom.app (op U))).hom _ = ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U))).hom (freeGen R _ U (x.map f))
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, key, Category.assoc]
  show (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U)).hom ((((free R).map (f.app (op (SimplexCategory.mk p)))).hom.app (op U)).hom (freeGen R _ U x)) = _
  rw [freeGen_map]
  rfl

theorem ext : LateralTheory.EtaleFoundations.EtaleSimplicialCochainExtOfEvaluation := by
  intro R _ E I n α β hev
  apply Cochain.ext
  intro a b hab
  rcases le_or_gt a 0 with ha | ha
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = -(k:ℤ) := ⟨a.natAbs, by omega⟩
    rw [← cancel_epi (chainsXIso R E k).inv]
    apply (sheafToPresheaf _ _).map_injective
    apply sheafify_hom_ext _ _ _ (I.X b).property
    apply NatTrans.ext
    funext U
    apply ModuleCat.free_hom_ext
    rintro ⟨y⟩
    exact hev k b hab U.unop y
  · apply (HomologicalComplex.isZero_extend_X _ _ a _).eq_of_src
    intro i hi
    change -(i:ℤ) = a at hi
    omega

end LateralTheory.EtaleFoundations.BasicPf

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.etaleSimplicialCochain_evaluation_properties_of_components : EtaleSimplicialCochainEvaluationProperties := by
  intro R _ E I n
  exact ⟨BasicPf.lin R, BasicPf.nat R, BasicPf.ext R, BasicPf.spc R, BasicPf.cx R⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleShortComplexExactIffLocallySurjectiveOnKernel : Prop :=
  ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔
    ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b

def EtaleTensorComplexLocallyExactOfFlatBounded : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → (∀ t, FlatS (J.X t)) →
    (∀ (s : ℤ) (U : Scheme.{0}) (y : Sec (C.sc s).X₂ U), Sec.map (C.sc s).g y = 0 →
      Loc U fun V g => ∃ x : Sec (C.sc s).X₁ V, Sec.map (C.sc s).f x = Sec.res g y) →
    ∀ (w : ℤ) (U : Scheme.{0}) (y : Sec (T.sc w).X₂ U), Sec.map (T.sc w).g y = 0 →
      Loc U fun V g => ∃ x : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f x = Sec.res g y

theorem etale_tensor_complex_acyclic_of_locally_exact_flat (hE : EtaleShortComplexExactIffLocallySurjectiveOnKernel) (hS : EtaleTensorComplexLocallyExactOfFlatBounded) :
    EtaleTensorAcyclicOfFlatBounded := by
  intro R _ C J T a b _ _ τ hτ hJ hC w
  have hCl := fun s => (hE R (C.sc s)).1 (hC s)
  exact (hE R (T.sc w)).2 (hS R a b τ hτ hJ hCl w)

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleTateTwistCupPairingExistsAndCupUnique : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
      ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h

theorem t_twpair_ex_of (htw : EtaleTateTwistCupPairingExistsAndCupUnique) : t_twpair_ex := by
  intro q _ i j
  exact ⟨twPair q i j, (htw q i j).1⟩

end LateralTheory.EtaleFoundations
end
