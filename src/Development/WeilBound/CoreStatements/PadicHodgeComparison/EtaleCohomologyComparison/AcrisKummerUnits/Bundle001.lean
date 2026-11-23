module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.AcrisModLBaseChange
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.FiltrationSpanDividedPowers
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationSquareOfValuationMod
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.PAlg

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}


variable (l) in
def base : PAlg l where
  A := Ob l
  s := RingHom.id _
  perf := inferInstance
  compl := RL.base_ex.1
  tf := RL.base_ex.2

theorem isBase_base : IsBase l (base l) := Function.bijective_id

variable (A : PAlg l)

def fromBase : base l ⟶ A := ⟨A.s, rfl⟩

theorem fromBase_comp {B : PAlg l} (f : A ⟶ B) : A.fromBase ≫ f = B.fromBase := Hom.ext (Hom.comm f)

def pdFil (n : ℕ) : DividedPowers (A.Fil n 1) := (RL.pd_ex A n).1.choose

theorem isPd_pdFil (n : ℕ) : R.IsPd (A.mkAcr n) (A.Fil0 1) (A.pdFil n) := (RL.pd_ex A n).1.choose_spec

def pdPFil (n : ℕ) : DividedPowers (A.PFil n) := (RL.pd_ex A n).2.choose

theorem isPd_pdPFil (n : ℕ) : R.IsPd (A.mkAcr n) A.PFil0 (A.pdPFil n) := (RL.pd_ex A n).2.choose_spec

def thetaN (n : ℕ) : A.Acr n →+* A.Un n := (RL.theta_ex A n).choose

theorem thetaN_toAcr (n : ℕ) (x : A.W) : A.thetaN n (A.toAcr n x) = Ideal.Quotient.mk _ (A.th x) :=
  (RL.theta_ex A n).choose_spec.1 x

theorem ker_thetaN (n : ℕ) : RingHom.ker (A.thetaN n) = A.Fil n 1 := (RL.theta_ex A n).choose_spec.2

theorem mkAcr_surjective (n : ℕ) : Function.Surjective (A.mkAcr n) := Ideal.Quotient.mk_surjective

theorem dpow_dxi (n k : ℕ) : (A.pdFil n).dpow k (A.dxi n 1) = A.dxi n k :=
  (A.isPd_pdFil n).2 k _ _ (Ideal.subset_span ⟨1, le_rfl, rfl⟩) (by
    have h1 := (RL.filtration_multiplicative A).2.2.1 1
    rw [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at h1
    rw [(RL.filtration_multiplicative A).2.2.1 k, h1])

theorem dpow_mem_fil (n k : ℕ) {x : A.Acr n} (hx : x ∈ A.Fil n 1) : (A.pdFil n).dpow k x ∈ A.Fil n k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [(RL.filtration_multiplicative A).2.2.2.2.2.2.1]; trivial
  rw [(RL.filtration_multiplicative A).2.2.2.2.1] at hx
  obtain ⟨x, hx', rfl⟩ := (Ideal.mem_map_iff_of_surjective _ (A.mkAcr_surjective n)).1 hx
  obtain ⟨y, -, hy⟩ := (RL.pdi A).1 x hx' k hk.ne'
  rw [(A.isPd_pdFil n).2 k x y hx' hy, (RL.filtration_multiplicative A).2.2.2.2.1]
  exact Ideal.mem_map_of_mem _ ((RL.pdi A).2.2 x hx' k y hy)

variable {A} {B : PAlg l}

theorem PdOk.acris_positive_filtration {f : A.A →+* B.A} (h : PdOk f) (h1 : ∀ x ∈ A.Fil0 1, h.acr0 x ∈ B.PFil0) :
    ∀ x ∈ A.PFil0, h.acr0 x ∈ B.PFil0 := by
  have : A.PFil0 ≤ B.PFil0.comap h.acr0 := sup_le (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) h1
  exact this

theorem twist_acrisZero_preserves_filtration (f : A ⟶ B) (r : ℕ) : ∀ x ∈ A.Fil0 r, (pdOk_hom f).acr0 x ∈ B.Fil0 r := by
  have : A.Fil0 r ≤ (B.Fil0 r).comap (pdOk_hom f).acr0 := by
    rw [Fil0, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    exact Ideal.subset_span ⟨k, hk, Subtype.ext ((awayW_dpw (Hom.f f) k (A.isUnit_natCast k.factorial_ne_zero) A.xi).trans
      (congrArg (dpw k) (mapW_xi f)))⟩
  exact this

theorem dp_mapAcr (f : A ⟶ B) (n : ℕ) : DividedPowers.IsDPMorphism (A.pdFil n) (B.pdFil n) (mapAcr f n) :=
  RL.pd_mor _ _ _ _ _ _ (pdOk_hom f).acr0 _ (A.mkAcr_surjective n) (RL.pdi A).1 (A.isPd_pdFil n) (B.isPd_pdFil n)
    (twist_acrisZero_preserves_filtration f 1) fun _ => rfl

theorem dpP_mapAcr (f : A ⟶ B) (n : ℕ) : DividedPowers.IsDPMorphism (A.pdPFil n) (B.pdPFil n) (mapAcr f n) :=
  RL.pd_mor _ _ _ _ _ _ (pdOk_hom f).acr0 _ (A.mkAcr_surjective n) (RL.pdi A).2.1 (A.isPd_pdPFil n) (B.isPd_pdPFil n)
    ((pdOk_hom f).acris_positive_filtration fun x hx => Ideal.mem_sup_right (twist_acrisZero_preserves_filtration f 1 x hx)) fun _ => rfl

variable (A)

theorem dp_fil_pfil (n : ℕ) : DividedPowers.IsDPMorphism (A.pdFil n) (A.pdPFil n) (RingHom.id _) :=
  RL.pd_mor _ _ _ _ _ _ (RingHom.id _) _ (A.mkAcr_surjective n) (RL.pdi A).1 (A.isPd_pdFil n) (A.isPd_pdPFil n)
    (fun x hx => Ideal.mem_sup_right hx) fun _ => rfl

theorem dp_red {m n : ℕ} (h : n ≤ m) : DividedPowers.IsDPMorphism (A.pdFil m) (A.pdFil n) (A.red h) :=
  RL.pd_mor _ _ _ _ _ _ (RingHom.id _) _ (A.mkAcr_surjective m) (RL.pdi A).1 (A.isPd_pdFil m) (A.isPd_pdFil n)
    (fun x hx => hx) fun _ => rfl

theorem dpP_red {m n : ℕ} (h : n ≤ m) : DividedPowers.IsDPMorphism (A.pdPFil m) (A.pdPFil n) (A.red h) :=
  RL.pd_mor _ _ _ _ _ _ (RingHom.id _) _ (A.mkAcr_surjective m) (RL.pdi A).2.1 (A.isPd_pdPFil m) (A.isPd_pdPFil n)
    (fun x hx => hx) fun _ => rfl

theorem dpP_phi (n : ℕ) : DividedPowers.IsDPMorphism (A.pdPFil n) (A.pdPFil n) (A.phi n) :=
  RL.pd_mor _ _ _ _ _ _ A.pdOk_frob.acr0 _ (A.mkAcr_surjective n) (RL.pdi A).2.1 (A.isPd_pdPFil n) (A.isPd_pdPFil n)
    (fun x hx => Ideal.mem_sup_left ((RL.tw_fil A (1 : Gal(PadicAlgCl l/(⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))))).2.1 x hx))
    fun _ => rfl

theorem dp_twAcr (σ : Gal(PadicAlgCl l/K)) (n : ℕ) :
    DividedPowers.IsDPMorphism ((tw σ A).pdFil n) (A.pdFil n) (twAcr σ A n) :=
  RL.pd_mor _ _ _ _ _ _ (pdOk_twId σ A).acr0 _ ((tw σ A).mkAcr_surjective n) (RL.pdi _).1 ((tw σ A).isPd_pdFil n)
    (A.isPd_pdFil n) (RL.tw_fil A σ).1 fun _ => rfl

theorem dpP_twAcr (σ : Gal(PadicAlgCl l/K)) (n : ℕ) :
    DividedPowers.IsDPMorphism ((tw σ A).pdPFil n) (A.pdPFil n) (twAcr σ A n) :=
  RL.pd_mor _ _ _ _ _ _ (pdOk_twId σ A).acr0 _ ((tw σ A).mkAcr_surjective n) (RL.pdi _).2.1 ((tw σ A).isPd_pdPFil n)
    (A.isPd_pdPFil n) ((pdOk_twId σ A).acris_positive_filtration fun x hx => Ideal.mem_sup_right ((RL.tw_fil A σ).1 x hx)) fun _ => rfl

def baseTw (σ : Gal(PadicAlgCl l/K)) : base l ⟶ tw σ (base l) := (tw σ (base l)).fromBase

def galBase (σ : Gal(PadicAlgCl l/K)) (n : ℕ) : (base l).Acr n →+* (base l).Acr n :=
  (twAcr σ (base l) n).comp (mapAcr (baseTw σ) n)

theorem galBase_cris (σ : Gal(PadicAlgCl l/K)) (n : ℕ) (a : Acris l) :
    galBase σ n ((base l).cris n a) = (base l).cris n (ACris.galCris σ a) := by
  rw [galBase, RingHom.comp_apply, mapAcr_cris, twAcr_cris]

theorem dp_galBase (σ : Gal(PadicAlgCl l/K)) (n : ℕ) :
    DividedPowers.IsDPMorphism ((base l).pdFil n) ((base l).pdFil n) (galBase σ n) :=
  DividedPowers.IsDPMorphism.comp _ (dp_twAcr _ σ n) (dp_mapAcr (baseTw σ) n)

theorem dpP_galBase (σ : Gal(PadicAlgCl l/K)) (n : ℕ) :
    DividedPowers.IsDPMorphism ((base l).pdPFil n) ((base l).pdPFil n) (galBase σ n) :=
  DividedPowers.IsDPMorphism.comp _ (dpP_twAcr _ σ n) (dpP_mapAcr (baseTw σ) n)

def cont (Γ : Type) [TopologicalSpace Γ] : PAlg l where
  A := A.contR Γ
  s := (A.contC Γ).comp A.s
  perf := (RL.cont_ex A Γ).1
  compl := (RL.cont_ex A Γ).2.1
  tf := (RL.cont_ex A Γ).2.2.1

def toCont (Γ : Type) [TopologicalSpace Γ] : A ⟶ A.cont Γ := ⟨A.contC Γ, rfl⟩

def evCont {Γ : Type} [TopologicalSpace Γ] (γ : Γ) : A.cont Γ ⟶ A :=
  ⟨(Pi.evalRingHom (fun _ => A.A) γ).comp (A.contR Γ).subtype, rfl⟩

end CrystallineSemistableComparison.PAlg
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.R

variable {S : Type} [CommRing S]

theorem mk_mem_jacobson {ϖ : S} (h : ϖ ∈ (⊥ : Ideal S).jacobson) (I : Ideal S) :
    Ideal.Quotient.mk I ϖ ∈ (⊥ : Ideal (S ⧸ I)).jacobson := by
  rw [Ideal.mem_jacobson_bot] at h ⊢
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  simpa using (h y).map (Ideal.Quotient.mk I)

theorem mem_jacobson_of_complete (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S] : ϖ ∈ (⊥ : Ideal S).jacobson :=
  IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self ϖ)

theorem valuation_of_valuation_mod_square (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S] (h : Val0 (S ⧸ Ideal.span {ϖ ^ 2})) : Val ϖ :=
  RL.val_of_dich ϖ fun m hm =>
    RL.dich_of_mod _ (mk_mem_jacobson (mem_jacobson_of_complete ϖ) _) (RL.valuation_square_of_valuation_mod ϖ h m hm.isPrime)

theorem aic_of_mod (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S] (h0 : ϖ ∈ nonZeroDivisors S) (hv : Val ϖ)
    (h : Aic (S ⧸ Ideal.span {ϖ ^ 2})) : Aic S := by
  refine RL.aic_limit ϖ (RL.step_glob ϖ fun m hm => ?_) (RL.pow_dvd ϖ h0 hv)
  refine RL.step_comp _ (mk_mem_jacobson (mem_jacobson_of_complete ϖ) _) ((RL.dich_comp ϖ m hm.isPrime).2 h0)
    ((RL.dich_comp ϖ m hm.isPrime).1 hv) ((RL.surj_pass (Ideal.quotientMap _ (Ideal.Quotient.mk (compI m)) ?_) ?_).1 h)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _
  · exact Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective

theorem splits (ha : Aic S) (hl : Loc S) : Splits (Spec (CommRingCat.of S)) := fun Y f he hs =>
  (RL.sec_rules Y f).2.2 (RL.glue (SecOn f) (RL.sec_rules Y f).1 (fun e e' _ _ => (RL.sec_rules Y f).2.1 e e')
    (RL.sec_add Y f) (RL.split_pt ha hl Y f he hs))

end CrystallineSemistableComparison.R

namespace CrystallineSemistableComparison.PAlg

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem l_mem_nzd_U : (l : A.U) ∈ nonZeroDivisors A.U := (RL.u_tf A).1

instance completeU : IsAdicComplete (Ideal.span {(l : A.U)}) A.U := RL.u_complete A

variable {A}

theorem IsTest.val_aic (h : A.IsTest) : R.Val (l : A.U) ∧ R.Aic A.U := by
  obtain ⟨ϖ, e, h0, h1⟩ := RL.untilt_valuation_mod_square A h
  have hl := (Fact.out : l.Prime).ne_zero
  have : IsAdicComplete (Ideal.span {ϖ}) A.U := (RL.val_pow ϖ l hl).2 (e.symm ▸ A.completeU)
  have hv := R.valuation_of_valuation_mod_square ϖ h0
  have hz : ϖ ∈ nonZeroDivisors A.U := by
    have := A.l_mem_nzd_U
    rw [← e] at this
    obtain ⟨c, hc⟩ := dvd_pow_self ϖ hl
    rw [hc] at this
    exact (mul_mem_nonZeroDivisors.1 this).1
  exact ⟨e ▸ (RL.val_pow ϖ l hl).1.2 hv, R.aic_of_mod ϖ hz hv h1⟩

theorem IsTest.splitU (h : A.IsTest) : R.Splits (Spec (CommRingCat.of A.U)) :=
  R.splits h.val_aic.2 ((RL.loc_aic (l : A.U)).1 h.val_aic.1).1

theorem IsTest.splitUg (h : A.IsTest) : R.Splits (Spec (CommRingCat.of A.Ug)) :=
  R.splits ((RL.loc_aic (l : A.U)).2 h.val_aic.2) ((RL.loc_aic (l : A.U)).1 h.val_aic.1).2

theorem IsTest.intClosed (h : A.IsTest) (x : A.Ug) (hx : IsIntegral A.U x) : ∃ y, algebraMap A.U A.Ug y = x :=
  RL.int_closed _ A.l_mem_nzd_U h.val_aic.1 x hx

theorem algebraMap_Ug_injective (A : PAlg l) : Function.Injective (algebraMap A.U A.Ug) :=
  IsLocalization.injective _ (M := Submonoid.powers (l : A.U)) (Submonoid.powers_le.2 A.l_mem_nzd_U)

theorem IsTest.idem (h : A.IsTest) (e : A.Ug) (he : IsIdempotentElem e) :
    ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ algebraMap A.U A.Ug (A.sharp e₀) = e := by
  obtain ⟨y, rfl⟩ := h.intClosed e ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by decide)), by
    simp [pow_two, he.eq]⟩
  have hy : IsIdempotentElem y := A.algebraMap_Ug_injective (by rw [map_mul, he.eq])
  obtain ⟨e₀, h₀, hu⟩ := RL.idem_au A y hy
  exact ⟨e₀, ⟨h₀.1, by rw [h₀.2]⟩, fun e₁ h₁ => hu e₁ ⟨h₁.1, A.algebraMap_Ug_injective h₁.2⟩⟩

theorem IsTest.sharp_surjective (h : A.IsTest) : Function.Surjective A.sharp := fun f => by
  have hl := (Fact.out : l.Prime).pos
  have hr : ∀ x : A.U, ∃ y, y ^ l = x := fun x => by
    rcases subsingleton_or_nontrivial A.U with h' | h'
    · exact ⟨0, Subsingleton.elim _ _⟩
    obtain ⟨y, hy⟩ := h.val_aic.2 (Polynomial.X ^ l - Polynomial.C x) (Polynomial.monic_X_pow_sub_C x hl.ne')
      (by rw [Polynomial.natDegree_X_pow_sub_C _]; exact hl)
    exact ⟨y, by simpa [sub_eq_zero] using hy⟩
  choose r hr using hr
  obtain ⟨a, -, ha⟩ := RL.tilt_ex A (fun i => r^[i] f) fun i => by rw [Function.iterate_succ_apply', hr]
  exact ⟨a 0, ha 0⟩

theorem IsTest.sharp_unit (h : A.IsTest) (u : (A.U)ˣ) : ∃ w : (A.A)ˣ, A.sharp w = u := by
  obtain ⟨a, ha⟩ := h.sharp_surjective u
  obtain ⟨w, rfl⟩ := RL.unit_lift A a (ha ▸ u.isUnit)
  exact ⟨w, ha⟩

end CrystallineSemistableComparison.PAlg
end
end

section

set_option backward.isDefEq.respectTransparency false

open CrystallineSemistableComparison.PAlg

theorem CrystallineSemistableComparison.R.forD (l : ℕ) [Fact l.Prime] : CrystallineSemistableComparison.D.RIn l :=
  ⟨RL.d_ob l, RL.acris_mod_l_base_change l, RL.d_seq l, fun A => ⟨(RL.u_tf A).1, fun x => by
    rw [← (RL.u_mod A).2, RingHom.mem_ker, sharpMap_coeff, Ideal.Quotient.eq_zero_iff_mem, pow_one]⟩, fun A n r => RL.gr A n r⟩
end
