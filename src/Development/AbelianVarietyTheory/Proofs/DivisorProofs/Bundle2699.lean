module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle088
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.Poinc

theorem nnnorm_le_of_mem_span {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] (v : R →+* K)
    (hv : ∀ r, ‖v r‖₊ ≤ 1) {s : Set R} {ρ : NNReal} (hs : ∀ c ∈ s, ‖v c‖₊ ≤ ρ) :
    ∀ c ∈ Ideal.span s, ‖v c‖₊ ≤ ρ := by
  intro c hc
  induction hc using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    rw [smul_eq_mul, map_mul, nnnorm_mul]
    exact (mul_le_mul' (hv a) hx).trans (by rw [one_mul])

theorem nnnorm_le_pow_of_mem_pow {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] (v : R →+* K)
    (hv : ∀ r, ‖v r‖₊ ≤ 1) {I : Ideal R} {ρ : NNReal} (hI : ∀ c ∈ I, ‖v c‖₊ ≤ ρ) :
    ∀ k : ℕ, ∀ b ∈ I ^ k, ‖v b‖₊ ≤ ρ ^ k := by
  intro k
  induction k with
  | zero => intro b _; simpa using hv b
  | succ k ih =>
    intro b hb
    rw [pow_succ] at hb
    refine Submodule.mul_induction_on hb ?_ ?_
    · intro a ha c hc
      rw [map_mul, nnnorm_mul, pow_succ]
      exact mul_le_mul' (ih a ha) (hI c hc)
    · intro a c ha hc
      rw [map_add (f := _)]
      exact (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le ha hc)

end GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem generates_of_close : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (∀ x ∈ D.idealSheaf.support, x ∉ U) → ∀ (x : M.Z) (p : ℕ) [Fact p.Prime] (y₀ : Sp (OO p) ⟶ M.Z), M.Cen U x y₀ → ∀ f, EqAt M D x f → ∃ k : ℕ, ∀ (G b : M₁.O (π x)), ‖M.val (gPt p ≫ y₀) ((G : Ω) + b)‖ = ‖M.val (gPt p ≫ y₀) f‖ → b ∈ Ideal.span {c : M₁.O (π x) | ¬ IsUnit c} ^ k → (G : Ω) / f ∈ M.O x → (G : Ω) ≠ 0 ∧ f / G ∈ M.O x := by
  intro o Ω _ _ _ _ M₁ M π hπ U D hD x p _ y₀ hy f hf
  obtain ⟨i, hxi, rfl⟩ := hf
  set F : Ω := valF M.pt (D.U i) (D.f i) with hFdef
  set y : Sp (PadicAlgCl p) ⟶ M.Z := gPt p ≫ y₀ with hydef

  have hFO : F ∈ M.O x := RatModel.valF_mem_O hxi _
  have hwx : y (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ x := RatModel.gPt_specializes hy.1 _
  have hwU : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ U := hy.2 ⟨_, rfl⟩
  have hwi : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ D.U i := hwx.mem_open (D.U i).isOpen hxi
  have hwb : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ M.Z.basicOpen (D.f i) := by
    by_contra h
    exact hD _ ((D.mem_support_iff i hwi).2 h) hwU
  have hF0 : M.val y F ≠ 0 :=
    (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton y (IsLocalRing.closedPoint (PadicAlgCl p)))
      ⟨_, RatModel.valF_mem_O hwi _⟩).2 ((RatModel.isUnit_valF_iff hwi (D.f i)).2 hwb)
  have hFpos : 0 < ‖M.val y F‖₊ := nnnorm_pos.2 hF0

  have hle : M₁.O (π x) ≤ M.O x := fun c hc => hπ.map_mem_O hc
  let v : M₁.O (π x) →+* PadicAlgCl p :=
    (RatModel.valHomOf y x (RatModel.gPt_specializes hy.1)).comp (Subalgebra.inclusion hle).toRingHom
  have hv_apply : ∀ c : M₁.O (π x), v c = M.val y c := fun c => rfl
  have hv1 : ∀ c, ‖v c‖₊ ≤ 1 := fun c => by
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, hv_apply]
    exact RatModel.norm_val_le_one hy.1 (hle c.2)
  have hvlt : ∀ c : M₁.O (π x), ¬ IsUnit c → ‖v c‖₊ < 1 := by
    intro c hc
    have hc' : (c : Ω) ∈ M₁.O (π (y (IsLocalRing.closedPoint (PadicAlgCl p)))) :=
      RatModel.O_le_of_specializes (hwx.map π.continuous) c.2
    have e := hπ.val_comp y (IsLocalRing.closedPoint (PadicAlgCl p)) hc'
    have hc0 : (y₀ ≫ π) (cPt p) = π x := by rw [Scheme.Hom.comp_apply, hy.1]
    have h1 := (RatModel.norm_val_lt_one_iff hc0 c.2).2 hc
    rw [← Category.assoc, ← hydef, e] at h1
    rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one, hv_apply]
    exact h1

  haveI : IsDedekindDomain o := ArithBase.ded (Ω := Ω)
  haveI := M₁.lft
  haveI : IsLocallyNoetherian M₁.Z := LocallyOfFiniteType.isLocallyNoetherian M₁.s
  haveI : IsNoetherianRing (M₁.O (π x)) := isNoetherianRing_of_ringEquiv _ (M₁.stalkEquiv (π x))
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (maximalIdeal (M₁.O (π x)))
  set ρ : NNReal := s.sup fun c => ‖v c‖₊
  have hρ : ρ < 1 := by
    refine (Finset.sup_lt_iff (by simp)).2 fun c hc => hvlt c ?_
    have : c ∈ maximalIdeal (M₁.O (π x)) := hs ▸ Submodule.subset_span hc
    exact (mem_maximalIdeal c).1 this
  have hm : ∀ c ∈ maximalIdeal (M₁.O (π x)), ‖v c‖₊ ≤ ρ := by
    rw [← hs]
    exact nnnorm_le_of_mem_span v hv1 fun c hc => Finset.le_sup (f := fun c => ‖v c‖₊) hc
  have hspan : Ideal.span {c : M₁.O (π x) | ¬ IsUnit c} = maximalIdeal (M₁.O (π x)) := by
    have : {c : M₁.O (π x) | ¬ IsUnit c} = (maximalIdeal (M₁.O (π x)) : Set (M₁.O (π x))) :=
      Set.ext fun c => (mem_maximalIdeal c).symm
    rw [this, Ideal.span_eq]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hFpos hρ
  refine ⟨k, fun G b hGb hb hGf => ?_⟩

  rw [hspan] at hb
  have hbk : ‖M.val y b‖₊ < ‖M.val y F‖₊ :=
    lt_of_le_of_lt (nnnorm_le_pow_of_mem_pow v hv1 hm k b hb) hk
  have hadd : M.val y ((G : Ω) + b) = M.val y G + M.val y b :=
    RatModel.val_add (RatModel.gPt_specializes hy.1) (hle G.2) (hle b.2)
  have hGb' : ‖M.val y G + M.val y b‖₊ = ‖M.val y F‖₊ := by
    rw [← hadd]
    exact NNReal.eq hGb
  have hG : ‖M.val y G‖₊ = ‖M.val y F‖₊ := by
    refine le_antisymm ?_ ?_
    · have e : M.val y G = (M.val y G + M.val y b) + -M.val y b := by ring
      rw [e]
      refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le hGb'.le ?_)
      rw [nnnorm_neg]
      exact hbk.le
    · rw [← hGb']
      refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le le_rfl ?_)
      by_contra h
      push_neg at h
      have := (IsUltrametricDist.nnnorm_add_le_max (M.val y G) (M.val y b)).trans
        (max_le h.le le_rfl)
      rw [hGb'] at this
      exact absurd hbk (not_lt.2 this)
  have hG0 : (G : Ω) ≠ 0 := by
    intro h
    rw [h, RatModel.val_zero, nnnorm_zero] at hG
    exact hFpos.ne hG
  have hFne : F ≠ 0 := by
    intro h
    rw [h, RatModel.val_zero] at hF0
    exact hF0 rfl
  refine ⟨hG0, ?_⟩
  have hmul : M.val y ((G : Ω) / F * F) = M.val y ((G : Ω) / F) * M.val y F :=
    RatModel.val_mul (RatModel.gPt_specializes hy.1) hGf hFO
  rw [div_mul_cancel₀ _ hFne] at hmul
  have hq : ‖M.val y ((G : Ω) / F)‖₊ = 1 := by
    have h2 : ‖M.val y ((G : Ω) / F)‖₊ * ‖M.val y F‖₊ = 1 * ‖M.val y F‖₊ := by
      rw [one_mul, ← nnnorm_mul, ← hmul, hG]
    exact mul_right_cancel₀ hFpos.ne' h2
  have hq' : ‖M.val (gPt p ≫ y₀) ((G : Ω) / F)‖ = 1 := by
    rw [← coe_nnnorm]
    exact congrArg NNReal.toReal hq
  have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.norm_val_eq_one_iff hy.1 hGf).1 hq')
  simpa [inv_div] using hu.2

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.FibreCorr

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M₁ M : RatModel o Ω} {π : M.Z ⟶ M₁.Z}

theorem mem_O_of_isHom (hπ : M₁.IsHom M (AlgHom.id o Ω) π) {x : M.Z} {F : Ω} (hF : F ∈ M₁.O (π x)) : F ∈ M.O x := by
  simpa using hπ.map_mem_O hF

theorem norm_val_le_one' (hπ : M₁.IsHom M (AlgHom.id o Ω) π) {q : ℕ} [Fact q.Prime] {y : Sp (OO q) ⟶ M.Z} {z : M₁.Z}
    (hy : π (y (cPt q)) = z) {F : Ω} (hF : F ∈ M₁.O z) : ‖M.val (gPt q ≫ y) F‖ ≤ 1 :=
  RatModel.norm_val_le_one rfl (mem_O_of_isHom hπ (hy ▸ hF))

theorem bound_mono {r s t : ℝ} {Q : Ω → Prop} {g : Ω → ℝ} (hs : s ≤ r) (H : r ≤ t ∨ ∃ h, Q h ∧ r ≤ g h) :
    s ≤ t ∨ ∃ h, Q h ∧ s ≤ g h :=
  H.imp hs.trans fun ⟨h, hq, hr⟩ => ⟨h, hq, hs.trans hr⟩

theorem nonUnitAt_of_not_isUnit {z : M₁.Z} {h : M₁.O z} (hh : ¬ IsUnit h) : NonUnitAt M₁ z h := by
  refine ⟨h.2, ?_⟩
  by_cases h0 : (h : Ω) = 0
  · exact Or.inl h0
  · exact Or.inr fun hi => hh ((RatModel.isUnit_O_iff h).2 ⟨h0, hi⟩)

theorem exists_nonUnit_pow (hπ : M₁.IsHom M (AlgHom.id o Ω) π) {q : ℕ} [Fact q.Prime] {y : Sp (OO q) ⟶ M.Z} {z : M₁.Z}
    (hy : π (y (cPt q)) = z) (e : ℕ) : ∀ F ∈ maximalIdeal (M₁.O z) ^ e, ∃ h : M₁.O z, ¬ IsUnit h ∧
      ‖M.val (gPt q ≫ y) (F : Ω)‖ ≤ ‖M.val (gPt q ≫ y) (h : Ω)‖ ^ e := by
  have hs : ∀ w, (gPt q ≫ y) w ⤳ y (cPt q) := RatModel.gPt_specializes rfl
  have hO : ∀ a : M₁.O z, (a : Ω) ∈ M.O (y (cPt q)) := fun a => mem_O_of_isHom hπ (hy ▸ a.2)
  have hadd : ∀ a b : M₁.O z, M.val (gPt q ≫ y) ((a + b : M₁.O z) : Ω) = M.val (gPt q ≫ y) a + M.val (gPt q ≫ y) b :=
    fun a b => RatModel.val_add hs (hO a) (hO b)
  have hmul : ∀ a b : M₁.O z, M.val (gPt q ≫ y) ((a * b : M₁.O z) : Ω) = M.val (gPt q ≫ y) a * M.val (gPt q ≫ y) b :=
    fun a b => RatModel.val_mul hs (hO a) (hO b)
  induction e with
  | zero =>
    intro F _
    refine ⟨0, not_isUnit_zero, ?_⟩
    rw [pow_zero]
    exact norm_val_le_one' hπ hy F.2
  | succ n ih =>
    intro F hF
    rw [pow_succ] at hF
    refine Submodule.mul_induction_on hF ?_ ?_
    · intro a ha b hb
      obtain ⟨h, hh, hle⟩ := ih a ha
      have hb' : ¬ IsUnit b := (mem_maximalIdeal b).1 hb
      rw [hmul, norm_mul]
      rcases le_total ‖M.val (gPt q ≫ y) (h : Ω)‖ ‖M.val (gPt q ≫ y) (b : Ω)‖ with hc | hc
      · refine ⟨b, hb', ?_⟩
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right (hle.trans (pow_le_pow_left₀ (norm_nonneg _) hc n)) (norm_nonneg _)
      · refine ⟨h, hh, ?_⟩
        rw [pow_succ]
        exact mul_le_mul hle hc (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    · rintro a b ⟨h₁, hh₁, h₁le⟩ ⟨h₂, hh₂, h₂le⟩
      rw [hadd]
      rcases le_total ‖M.val (gPt q ≫ y) (h₁ : Ω)‖ ‖M.val (gPt q ≫ y) (h₂ : Ω)‖ with hc | hc
      · exact ⟨h₂, hh₂, (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (h₁le.trans (pow_le_pow_left₀ (norm_nonneg _) hc _)) h₂le)⟩
      · exact ⟨h₁, hh₁, (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le h₁le (h₂le.trans (pow_le_pow_left₀ (norm_nonneg _) hc _)))⟩

variable (hπ : M₁.IsHom M (AlgHom.id o Ω) π)

def approxIdeal (U : M.Z.Opens) (D : EffCartierData M.Z) (z : M₁.Z) (e : ℕ) : Ideal (M₁.O z) where
  carrier := {F | ∀ (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ M.Z), π (y (cPt q)) = z → Set.range (gPt q ≫ y) ⊆ U →
    ∀ f, EqAt M D (y (cPt q)) f → ‖M.val (gPt q ≫ y) (F : Ω)‖ ≤ ‖M.val (gPt q ≫ y) f‖ ∨
      ∃ h, NonUnitAt M₁ z h ∧ ‖M.val (gPt q ≫ y) (F : Ω)‖ ≤ ‖M.val (gPt q ≫ y) h‖ ^ e}
  add_mem' := by
    intro a b ha hb q _ y hy hU f hf
    have hs : ∀ w, (gPt q ≫ y) w ⤳ y (cPt q) := RatModel.gPt_specializes rfl
    have e1 : M.val (gPt q ≫ y) ((a + b : M₁.O z) : Ω) = M.val (gPt q ≫ y) a + M.val (gPt q ≫ y) b :=
      RatModel.val_add hs (mem_O_of_isHom hπ (hy ▸ a.2)) (mem_O_of_isHom hπ (hy ▸ b.2))
    rw [e1]
    rcases le_total ‖M.val (gPt q ≫ y) (a : Ω)‖ ‖M.val (gPt q ≫ y) (b : Ω)‖ with h | h
    · exact bound_mono ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h le_rfl)) (hb q y hy hU f hf)
    · exact bound_mono ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl h)) (ha q y hy hU f hf)
  zero_mem' := by
    intro q _ y hy hU f hf
    left
    simp [RatModel.val_zero]
  smul_mem' := by
    intro c a ha q _ y hy hU f hf
    have hs : ∀ w, (gPt q ≫ y) w ⤳ y (cPt q) := RatModel.gPt_specializes rfl
    have e1 : M.val (gPt q ≫ y) ((c • a : M₁.O z) : Ω) = M.val (gPt q ≫ y) c * M.val (gPt q ≫ y) a :=
      RatModel.val_mul hs (mem_O_of_isHom hπ (hy ▸ c.2)) (mem_O_of_isHom hπ (hy ▸ a.2))
    rw [e1, norm_mul]
    exact bound_mono (mul_le_of_le_one_left (norm_nonneg _) (norm_val_le_one' hπ hy c.2)) (ha q y hy hU f hf)

def fibreIdeal (D : EffCartierData M.Z) (z : M₁.Z) : Ideal (M₁.O z) where
  carrier := {G | ∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → (G : Ω) / f' ∈ M.O x'}
  add_mem' := by
    intro a b ha hb x' hx f hf
    rw [Subalgebra.coe_add, add_div]
    exact add_mem (ha x' hx f hf) (hb x' hx f hf)
  zero_mem' := by
    intro x' hx f hf
    simp
  smul_mem' := by
    intro c a ha x' hx f hf
    rw [smul_eq_mul, Subalgebra.coe_mul, mul_div_assoc]
    exact mul_mem (mem_O_of_isHom hπ (by rw [hx]; exact c.2)) (ha x' hx f hf)

variable {hπ}

theorem mem_fibreIdeal {D : EffCartierData M.Z} {z : M₁.Z} {G : M₁.O z} :
    G ∈ fibreIdeal hπ D z ↔ ∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → (G : Ω) / f' ∈ M.O x' := Iff.rfl

theorem approxIdeal_antitone (U : M.Z.Opens) (D : EffCartierData M.Z) (z : M₁.Z) :
    Antitone (approxIdeal hπ U D z) := by
  intro e e' hee F hF q _ y hy hU f hf
  rcases hF q y hy hU f hf with h | ⟨h, hh, hle⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, hh, hle.trans (pow_le_pow_of_le_one (norm_nonneg _) (norm_val_le_one' hπ hy hh.1) hee)⟩

theorem pow_le_approxIdeal (U : M.Z.Opens) (D : EffCartierData M.Z) (z : M₁.Z) (e : ℕ) :
    maximalIdeal (M₁.O z) ^ e ≤ approxIdeal hπ U D z e := by
  intro F hF q _ y hy hU f hf
  obtain ⟨h, hh, hle⟩ := exists_nonUnit_pow hπ hy e F hF
  exact Or.inr ⟨h, nonUnitAt_of_not_isUnit hh, hle⟩

theorem isNoetherianRing_O [ArithBase o Ω] (M : RatModel o Ω) (z : M.Z) : IsNoetherianRing (M.O z) := by
  haveI : IsDedekindDomain o := ArithBase.ded Ω
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  exact isNoetherianRing_of_ringEquiv _ (M.stalkEquiv z)

end GlobalTheory.FibreCorr
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.Izumi

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem norm_val_add_le {U : Set M.Z} {x : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hy : M.Cen U x y)
    (F G : M.O x) :
    ‖M.val (gPt p ≫ y) ((F + G : M.O x) : Ω)‖ ≤ max ‖M.val (gPt p ≫ y) (F : Ω)‖ ‖M.val (gPt p ≫ y) (G : Ω)‖ := by
  rw [Subalgebra.coe_add, RatModel.val_add (RatModel.gPt_specializes hy.1) F.2 G.2]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_val_mul_le {U : Set M.Z} {x : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hy : M.Cen U x y)
    (c F : M.O x) : ‖M.val (gPt p ≫ y) ((c * F : M.O x) : Ω)‖ ≤ ‖M.val (gPt p ≫ y) (F : Ω)‖ := by
  rw [Subalgebra.coe_mul, RatModel.val_mul (RatModel.gPt_specializes hy.1) c.2 F.2, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hy.norm_val_le_one c.2)

def smallIdeal (U : M.Z.Opens) (x : M.Z) (f : Ω) (N : ℕ) : Ideal (M.O x) where
  carrier := {F | ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y →
      ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨
        ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ N}
  zero_mem' := by
    intro p _ y _
    left
    have h0 : ((0 : M.O x) : Ω) = 0 := rfl
    rw [h0, RatModel.val_zero, norm_zero]
    exact norm_nonneg _
  add_mem' := by
    intro F G hF hG p _ y hy
    have h := norm_val_add_le M hy F G
    rcases le_total ‖M.val (gPt p ≫ y) (F : Ω)‖ ‖M.val (gPt p ≫ y) (G : Ω)‖ with hle | hle
    · rw [max_eq_right hle] at h
      rcases hG p y hy with h' | ⟨k, hk, h'⟩
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨k, hk, h.trans h'⟩
    · rw [max_eq_left hle] at h
      rcases hF p y hy with h' | ⟨k, hk, h'⟩
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨k, hk, h.trans h'⟩
  smul_mem' := by
    intro c F hF p _ y hy
    have h := norm_val_mul_le M hy c F
    rcases hF p y hy with h' | ⟨k, hk, h'⟩
    · exact Or.inl (h.trans h')
    · exact Or.inr ⟨k, hk, h.trans h'⟩

variable {M}

theorem mem_smallIdeal {U : M.Z.Opens} {x : M.Z} {f : Ω} {N : ℕ} {F : M.O x} :
    F ∈ smallIdeal M U x f N ↔ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y →
      ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨
        ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ N := Iff.rfl

theorem smallIdeal_antitone (U : M.Z.Opens) (x : M.Z) (f : Ω) : Antitone (smallIdeal M U x f) := by
  intro N N' hN F hF p _ y hy
  rcases hF p y hy with h' | ⟨k, hk, h'⟩
  · exact Or.inl h'
  · refine Or.inr ⟨k, hk, h'.trans (pow_le_pow_of_le_one (norm_nonneg _) (hy.norm_val_le_one hk.1) hN)⟩

theorem self_mem_smallIdeal (U : M.Z.Opens) {x : M.Z} {f : Ω} (hf : f ∈ M.O x) (N : ℕ) :
    (⟨f, hf⟩ : M.O x) ∈ smallIdeal M U x f N :=
  fun _ _ _ _ => Or.inl le_rfl

end GlobalTheory.Izumi

namespace GlobalTheory.Izumi

open IsLocalRing

theorem exists_le_span_sup_pow (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : ℕ → Ideal A)
    (f : A) (hK : Antitone K) (hf : ∀ N, f ∈ K N)
    (h : ⨅ N, (K N).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) ≤
      Ideal.span {algebraMap A (AdicCompletion (maximalIdeal A) A) f}) (e : ℕ) :
    ∃ N, K N ≤ Ideal.span {f} ⊔ maximalIdeal A ^ e := by
  set B := AdicCompletion (maximalIdeal A) A
  set φ := algebraMap A B
  have : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  set I : Ideal B := Ideal.span {φ f}
  let L : ℕ → Submodule B (B ⧸ I) := fun N => Submodule.map I.mkQ ((K N).map φ)
  have hL : Directed (· ≥ ·) L := by
    refine Antitone.directed_ge fun N N' hN => ?_
    exact Submodule.map_mono (Ideal.map_mono (hK hN))
  have hIK : ∀ N, I ≤ (K N).map φ := fun N =>
    (Ideal.span_le).2 (Set.singleton_subset_iff.2 (Ideal.mem_map_of_mem φ (hf N)))
  have h0 : (⨅ N, L N) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨b, rfl⟩ := I.mkQ_surjective x
    have hb : b ∈ ⨅ N, (K N).map φ := by
      refine Submodule.mem_iInf _ |>.2 fun N => ?_
      obtain ⟨b', hb', hbb'⟩ := (Submodule.mem_iInf _).1 hx N
      have hd : b' - b ∈ I := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
        simp only [Submodule.mkQ_apply] at hbb'
        rw [hbb', sub_self]
      have := Submodule.sub_mem _ hb' (hIK N hd)
      simpa using this
    have := h hb
    simp only [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact this
  obtain ⟨N, hN⟩ := GlobalTheory.Chevalley.exists_le_maximalIdeal_pow_smul_of_directed B (B ⧸ I) ℕ L
    inferInstance hL h0 e
  refine ⟨N, fun a ha => ?_⟩
  have h1 : I.mkQ (φ a) ∈ maximalIdeal B ^ e • (⊤ : Submodule B (B ⧸ I)) :=
    hN (Submodule.mem_map_of_mem (Ideal.mem_map_of_mem φ ha))
  have h2 : maximalIdeal B ^ e • (⊤ : Submodule B (B ⧸ I)) = Submodule.map I.mkQ (maximalIdeal B ^ e) := by
    have h4 : maximalIdeal B ^ e • (⊤ : Submodule B B) = maximalIdeal B ^ e := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    rw [← Submodule.range_mkQ I, ← Submodule.map_top, ← Submodule.map_smul'', h4]
  rw [h2, ← Submodule.mem_comap, Submodule.comap_map_mkQ] at h1
  obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  set ψ := AdicCompletion.evalₐ (maximalIdeal A) (R := A) e
  have hψ : ∀ r : A, ψ (φ r) = Ideal.Quotient.mk _ r := fun r => ψ.commutes r
  have ht0 : ψ t = 0 := by
    have hle : maximalIdeal B ^ e ≤ RingHom.ker ψ.toRingHom := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      rw [hψ, Ideal.Quotient.eq_zero_iff_mem]
      exact hr
    exact hle ht
  obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective (ψ c)
  have h3 := congrArg ψ hut
  rw [map_add (f := _), map_mul, ht0, add_zero, hψ, hψ, ← hc', ← map_mul, Ideal.Quotient.eq] at h3
  have : a = c' * f + (a - c' * f) := by ring
  rw [this]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)) (by rw [← neg_sub]; exact neg_mem h3)

end GlobalTheory.Izumi
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_projectiveSpace_point_of_unit_coordinate : ∀ (o R : Type) [CommRing o] [CommRing R] (n : ℕ) (β : o →+* R) (v : Fin (n + 1) → R), (∃ j, IsUnit (v j)) → ∃ ξ : Sp R ⟶ PSpace o n, ξ ≫ PSpace.str o n = spMap β ∧ PCrd ξ v := by
  first | exact @GlobalTheory.UMin.exists_pCrd_of_isUnit | exact GlobalTheory.UMin.exists_pCrd_of_isUnit | (intros; apply GlobalTheory.UMin.exists_pCrd_of_isUnit <;> assumption)
end
