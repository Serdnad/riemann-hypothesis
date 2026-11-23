module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
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
public import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.CharP.Invertible
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
public import ReciprocityTheory.DualLattices.ProdDvdOfIso

@[expose] public section

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Chart (spMap_comp spMap_id)

namespace PositivityTheory.HtPt.Rf

section
variable {R : Type} [CommRing R] {p : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

omit [GrpObj G] in
theorem spc {A B S : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing S]
    [Algebra R S] (ψ : B →ₐ[R] S) (φ : A →ₐ[R] B) (y : sp (R₀ := R) A ⟶ G) :
    spMap (ψ.comp φ) ≫ y = spMap ψ ≫ spMap φ ≫ y := by
  rw [← Category.assoc, spMap_comp]

omit [GrpObj G] in
theorem spc' {A B S : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing S]
    [Algebra R S] (ψ : B →ₐ[R] S) (φ : A →ₐ[R] B) (y : sp (R₀ := R) A ⟶ G) :
    spMap ψ ≫ spMap φ ≫ y = spMap (ψ.comp φ) ≫ y := (spc ψ φ y).symm

theorem tors_pow (T : TorsRep G p) {S : Type} [CommRing S] [Algebra R S] (φ : T.A →ₐ[R] S) :
    (spMap φ ≫ T.y) ^ p = 1 := by
  rw [← MonObj.comp_pow, T.y_p, MonObj.comp_one]

theorem tors_ext (T : TorsRep G p) {S : Type} [CommRing S] [Algebra R S] {φ φ' : T.A →ₐ[R] S}
    (h : spMap φ ≫ T.y = spMap φ' ≫ T.y) : φ = φ' := by
  exact (T.univ S _ (tors_pow T φ)).unique rfl h.symm

theorem lift_comul (T : TorsRep G p) (Δ : T.A →ₐ[R] TensorProduct R T.A T.A)
    (hΔ : spMap Δ ≫ T.y = (spMap (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) * (spMap (Algebra.TensorProduct.includeRight : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y))
    {S : Type} [CommRing S] [Algebra R S] (F : TensorProduct R T.A T.A →ₐ[R] S) :
    spMap (F.comp Δ) ≫ T.y = (spMap (F.comp Algebra.TensorProduct.includeLeft) ≫ T.y) *
      (spMap (F.comp Algebra.TensorProduct.includeRight) ≫ T.y) := by
  rw [spc, hΔ, MonObj.comp_mul, spc', spc']

end

theorem tors_alg : ∀ (R : Type) [CommRing R] (p : ℕ), ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ T : TorsRep G p, ∃ (Δ : T.A →ₐ[R] TensorProduct R T.A T.A) (ε : T.A →ₐ[R] R) (s : T.A →ₐ[R] T.A), spMap Δ ≫ T.y = (spMap (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) * (spMap (Algebra.TensorProduct.includeRight : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) ∧ spMap ε ≫ T.y = 1 ∧ (spMap s ≫ T.y) * T.y = 1 ∧ (Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp ((Algebra.TensorProduct.map Δ (AlgHom.id R T.A)).comp Δ) = (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp Δ ∧ (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp Δ = (Algebra.TensorProduct.lid R T.A).symm.toAlgHom ∧ (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp Δ = (Algebra.TensorProduct.rid R R T.A).symm.toAlgHom ∧ (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp Δ = (Algebra.ofId R T.A).comp ε ∧ (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp Δ = Δ := by
  intro R _ p G _ _ T
  set iL : T.A →ₐ[R] TensorProduct R T.A T.A := Algebra.TensorProduct.includeLeft with hiL
  set iR : T.A →ₐ[R] TensorProduct R T.A T.A := Algebra.TensorProduct.includeRight with hiR
  have hz : ((spMap iL ≫ T.y) * (spMap iR ≫ T.y)) ^ p = 1 := by
    rw [mul_pow, tors_pow, tors_pow, _root_.one_mul]
  obtain ⟨Δ, hΔ, -⟩ := T.univ _ _ hz
  obtain ⟨ε, hε, -⟩ := T.univ R (1 : sp (R₀ := R) R ⟶ G) (one_pow p)
  have hz' : (T.y⁻¹) ^ p = 1 := by rw [inv_pow, T.y_p, inv_one]
  obtain ⟨s, hs, -⟩ := T.univ T.A _ hz'
  refine ⟨Δ, ε, s, hΔ, hε, by rw [hs, _root_.inv_mul_cancel], ?_, ?_, ?_, ?_, ?_⟩
  · apply tors_ext T
    rw [← AlgHom.comp_assoc, lift_comul T Δ hΔ, lift_comul T Δ hΔ]
    have e1 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.map Δ (AlgHom.id R T.A))).comp iL = ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp Δ := by
      ext x; simp [hiL]
    have e2 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.map Δ (AlgHom.id R T.A))).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp iR := by
      ext x; simp [hiR, Algebra.TensorProduct.one_def]
    have e3 : (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp iL = (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)) := by
      ext x; simp [hiL]
    have e4 : (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp Δ := by
      ext x; simp [hiR]
    have e5 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp iL = (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)) := by
      ext x; simp [hiL, Algebra.TensorProduct.one_def]
    have e6 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp iL := by
      ext x; simp [hiL, hiR, Algebra.TensorProduct.one_def]
    rw [e1, e2, lift_comul T Δ hΔ, e5, e6, e3, e4, lift_comul T Δ hΔ, _root_.mul_assoc]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp iL = (Algebra.TensorProduct.includeLeft : R →ₐ[R] TensorProduct R R T.A).comp ε := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp iR = (Algebra.TensorProduct.lid R T.A).symm.toAlgHom := by
      ext x; simp [hiR]
    rw [e1, e2, spc, hε, MonObj.comp_one, _root_.one_mul]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp iL = (Algebra.TensorProduct.rid R R T.A).symm.toAlgHom := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp iR = (Algebra.TensorProduct.includeRight : R →ₐ[R] TensorProduct R T.A R).comp ε := by
      ext x; simp [hiR]
    rw [e1, e2, spc, hε, MonObj.comp_one, _root_.mul_one]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp iL = s := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp iR = AlgHom.id R T.A := by
      ext x; simp [hiR]
    rw [e1, e2, spMap_id, Category.id_comp, hs, _root_.inv_mul_cancel, spc, hε, MonObj.comp_one]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ, hΔ]
    have e1 : (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp iL = iR := by
      ext x; simp [hiL, hiR]
    have e2 : (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp iR = iL := by
      ext x; simp [hiL, hiR]
    rw [e1, e2, _root_.mul_comm]

end PositivityTheory.HtPt.Rf
end

section

noncomputable section

namespace PositivityTheory.HtPt.Cb

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open ReciprocityTheory.ChartRestriction.G.TB

section

variable {R : Type} [CommRing R] {σ : Type} [Finite σ]

def scl (w : σ → ℕ) (m : σ →₀ ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun s => w s * m s

theorem scl_inj {w : σ → ℕ} (hw : ∀ s, w s ≠ 0) : Function.Injective (scl w) := fun m m' h => by
  ext s
  have := congrArg (fun f => f s) h
  simpa [scl, hw s] using this

theorem hasSubst_w {w : σ → ℕ} (hw : ∀ s, w s ≠ 0) :
    HasSubst (fun s => (X s : MvPowerSeries σ R) ^ w s) :=
  hasSubst_of_constantCoeff_zero fun s => by simp [hw s]

theorem prod_w (w : σ → ℕ) (m : σ →₀ ℕ) :
    (m.prod fun s e => ((X s : MvPowerSeries σ R) ^ w s) ^ e) = monomial (scl w m) 1 := by
  classical
  have := Fintype.ofFinite σ
  rw [monomial_eq', Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp [scl, pow_mul]

theorem coeff_scl {w : σ → ℕ} (hw : ∀ s, w s ≠ 0) (g : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff (scl w m) (subst (fun s => (X s : MvPowerSeries σ R) ^ w s) g) = coeff m g := by
  classical
  rw [coeff_subst (hasSubst_w hw), finsum_eq_single _ m]
  · simp [prod_w]
  · intro m' h
    rw [prod_w, coeff_monomial, ite_eq_right ((scl_inj hw).ne h.symm), smul_zero]

theorem coeff_not_scl {w : σ → ℕ} (hw : ∀ s, w s ≠ 0) (g : MvPowerSeries σ R) (e : σ →₀ ℕ)
    (he : ∀ m, e ≠ scl w m) :
    coeff e (subst (fun s => (X s : MvPowerSeries σ R) ^ w s) g) = 0 := by
  classical
  rw [coeff_subst (hasSubst_w hw)]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  rw [prod_w, coeff_monomial, ite_eq_right (he m), smul_zero]

theorem exists_scl (p : ℕ) [hp : Fact p.Prime] [CharP R p] (S : σ → Prop) [DecidablePred S]
    (f : MvPowerSeries σ R) (hf : ∀ s, S s → pderiv s f = 0) :
    ∃ g : MvPowerSeries σ R, f = subst (fun s => (X s : MvPowerSeries σ R) ^ (if S s then p else 1)) g := by
  classical
  have hw : ∀ s, (if S s then p else 1) ≠ 0 := fun s => by split_ifs <;> simp [hp.out.ne_zero]
  obtain ⟨g, hg⟩ : ∃ g : MvPowerSeries σ R, ∀ m, coeff m g = coeff (scl (fun s => if S s then p else 1) m) f :=
    ⟨fun m => coeff (scl (fun s => if S s then p else 1) m) f, fun _ => rfl⟩
  refine ⟨g, ?_⟩
  ext e
  by_cases he : ∃ m, e = scl (fun s => if S s then p else 1) m
  · obtain ⟨m, rfl⟩ := he
    rw [coeff_scl hw, hg]
  · rw [coeff_not_scl hw _ _ (not_exists.1 he)]
    obtain ⟨s, hS, hs⟩ : ∃ s, S s ∧ ¬ p ∣ e s := by
      by_contra hc
      push Not at hc
      refine he ⟨Finsupp.equivFunOnFinite.symm fun s => if S s then e s / p else e s, ?_⟩
      ext s
      by_cases h : S s
      · simp [scl, h, Nat.mul_div_cancel' (hc s h)]
      · simp [scl, h]
    have h0 : e s ≠ 0 := fun h => hs (h ▸ dvd_zero p)
    have h1 := congrArg (coeff (e - Finsupp.single s 1)) (hf s hS)
    rw [coeff_pderiv, tsub_add_cancel_of_le (by simpa [Finsupp.single_le_iff] using Nat.one_le_iff_ne_zero.2 h0),
      map_zero] at h1
    have h2 : (((e - Finsupp.single s 1 : σ →₀ ℕ) s : ℕ) : R) + 1 = (e s : R) := by
      rw [← Nat.cast_succ]; congr 1; simp; omega
    rw [h2] at h1
    have hu : IsUnit (e s : R) := (CharP.isUnit_natCast_iff hp.out).2 hs
    exact hu.mul_left_eq_zero.1 h1

end

section

variable {R : Type} [CommRing R] {d : ℕ} (p : ℕ)

theorem ev_pow_one_eq (g : PS R 1 d) : ev (n := 1) ![ptPow R d p 0] g =
    subst (fun s : Fin 1 × Fin d => (X s : PS R 1 d) ^ (if s.1 = 0 then p else 1)) g := by
  unfold ev; congr 1; funext ⟨j, i⟩; fin_cases j; simp [ptPow]

theorem ev_pow_two_eq (g : PS R 2 d) : ev (n := 2) ![ptPow R d p 0, pt R d 1] g =
    subst (fun s : Fin 2 × Fin d => (X s : PS R 2 d) ^ (if s.1 = 0 then p else 1)) g := by
  unfold ev; congr 1; funext ⟨j, i⟩; fin_cases j <;> simp [ptPow, pt]

variable [hp : Fact p.Prime]

theorem w_ne {n : ℕ} [NeZero n] (s : Fin n × Fin d) : (if s.1 = 0 then p else 1) ≠ 0 := by
  split_ifs <;> simp [hp.out.ne_zero]

theorem ev_pow_inj {f g : PS R 1 d} (h : ev (n := 1) ![ptPow R d p 0] f = ev ![ptPow R d p 0] g) : f = g := by
  ext m
  rw [← coeff_scl (w_ne p) f, ← coeff_scl (w_ne p) g, ← ev_pow_one_eq, ← ev_pow_one_eq, h]

theorem coeff_ev_pow_one (g : PS R 1 d) (j : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), j) p) (ev (n := 1) ![ptPow R d p 0] g) =
      coeff (Finsupp.single ((0 : Fin 1), j) 1) g := by
  rw [← coeff_scl (w_ne p) g, ev_pow_one_eq]
  congr 2
  ext s
  by_cases h : s = (0, j)
  · simp [scl, h]
  · simp [scl, Finsupp.single_eq_of_ne h]

theorem bil_ev_pow_two (g : PS R 2 d) : bil (ev (n := 2) ![ptPow R d p 0, pt R d 1] g) p 1 = bil g 1 1 := by
  ext i j
  rw [bil, bil, ← coeff_scl (w_ne p) g, ev_pow_two_eq]
  congr 2
  ext ⟨s, t⟩
  fin_cases s <;> simp [scl, Finsupp.single_apply]

end

theorem series_in_p : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ), (∀ f : PS R 1 d, (∀ j, pderiv ((0 : Fin 1), j) f = 0) → ∃ g : PS R 1 d, f = ev (n := 1) ![ptPow R d p 0] g) ∧ ∀ f : PS R 2 d, (∀ j, pderiv ((0 : Fin 2), j) f = 0) → ∃ g : PS R 2 d, f = ev (n := 2) ![ptPow R d p 0, pt R d 1] g := by
  intro R _ p _ _ d
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩
  · simp only [ev_pow_one_eq]
    exact exists_scl p (fun s : Fin 1 × Fin d => s.1 = 0) f fun ⟨s, t⟩ h => by
      obtain rfl : s = 0 := h
      exact hf t
  · simp only [ev_pow_two_eq]
    exact exists_scl p (fun s : Fin 2 × Fin d => s.1 = 0) f fun ⟨s, t⟩ h => by
      obtain rfl : s = 0 := h
      exact hf t

theorem frob_subst : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d n : ℕ) (f : PS R n d), f ^ p = ev (fun j => ptPow R d p j) (MvPowerSeries.map (frobenius R p) f) := by
  intro R _ p hp _ d n f
  rw [← map_frobenius_expand p hp.out.ne_zero, map_expand, expand, substAlgHom_apply]
  rfl

end PositivityTheory.HtPt.Cb
end
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F]

theorem mem_aug {X : Type} [AddCommGroup X] {M : Submodule R (X → C)} {g : X → C} :
    g ∈ augIdeal M ↔ g ∈ M ∧ g 0 = 0 := Iff.rfl

section Pull

variable {X Y : Type} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]

theorem eig_zero {M : Submodule R (X → C)} {χ : MulChar F R} {g : X → C} (hg : g ∈ eig M χ) :
    g 0 = 0 := by
  have := hg.2 0 0
  rwa [smul_zero, MulChar.map_zero, map_zero, zero_mul] at this

theorem eig_pull (u : X →ₗ[F] Y) {M : Submodule R (Y → C)} {M' : Submodule R (X → C)}
    (h : ∀ g ∈ M, g ∘ u ∈ M') {χ : MulChar F R} {g : Y → C} (hg : g ∈ eig M χ) :
    g ∘ u ∈ eig M' χ :=
  ⟨h g hg.1, fun a x => by simpa using hg.2 a (u x)⟩

theorem sq_pull (u : X →ₗ[F] Y) {M : Submodule R (Y → C)} {M' : Submodule R (X → C)}
    (h : ∀ g ∈ M, g ∘ u ∈ M') {g : Y → C} (hg : g ∈ sqIdeal (augIdeal M)) :
    g ∘ u ∈ sqIdeal (augIdeal M') := by
  have : (sqIdeal (augIdeal M)).map (LinearMap.funLeft R C u) ≤ sqIdeal (augIdeal M') := by
    rw [sqIdeal, Submodule.map_span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine Submodule.subset_span ⟨a ∘ u, ⟨h a ha.1, ?_⟩, b ∘ u, ⟨h b hb.1, ?_⟩, rfl⟩
    · show a (u 0) = 0
      rw [map_zero]; exact ha.2
    · show b (u 0) = 0
      rw [map_zero]; exact hb.2
  exact this (Submodule.mem_map_of_mem hg)

theorem hasLen_transport (e : X ≃ₗ[F] Y) {M : Submodule R (Y → C)} {M' : Submodule R (X → C)}
    (h : ∀ g, g ∈ M ↔ g ∘ e ∈ M') {χ : MulChar F R} {x : NNReal}
    (hx : HasLen v R (OmType M' χ) x) : HasLen v R (OmType M χ) x := by
  have h1 : ∀ g ∈ M, g ∘ (e : X →ₗ[F] Y) ∈ M' := fun g hg => (h g).1 hg
  have c1 : ∀ g : X → C, (g ∘ (e.symm : Y →ₗ[F] X)) ∘ e = g := fun g => by
    funext x; simp
  have c2 : ∀ g : Y → C, (g ∘ e) ∘ (e.symm : Y →ₗ[F] X) = g := fun g => by
    funext x; simp
  have h2 : ∀ g ∈ M', g ∘ (e.symm : Y →ₗ[F] X) ∈ M := fun g hg => by
    rw [h, c1]; exact hg
  let φ : eig M χ ≃ₗ[R] eig M' χ :=
    { toFun := fun g => ⟨g.1 ∘ e, eig_pull (e : X →ₗ[F] Y) h1 g.2⟩
      invFun := fun g => ⟨g.1 ∘ (e.symm : Y →ₗ[F] X), eig_pull _ h2 g.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun g => Subtype.ext (c2 g.1)
      right_inv := fun g => Subtype.ext (c1 g.1) }
  obtain ⟨m, c, ⟨ψ⟩, hx⟩ := hx
  refine ⟨m, c, ⟨(Submodule.Quotient.equiv _ _ φ ?_).trans ψ⟩, hx⟩
  ext g
  rw [Submodule.mem_map_equiv]
  constructor
  · intro hg
    have : (g.1 ∘ (e.symm : Y →ₗ[F] X)) ∘ e ∈ sqIdeal (augIdeal M') :=
      sq_pull (e : X →ₗ[F] Y) h1 hg
    rw [c1] at this
    exact this
  · intro hg
    exact sq_pull (e.symm : Y →ₗ[F] X) h2 hg

end Pull

variable {N : Type} [AddCommGroup N] [Module F N]

theorem hasLen_trivial (hv : v.Integers R) [Subsingleton N] {M : Submodule R (N → C)}
    {χ : MulChar F R} {x : NNReal} (hx : HasLen v R (OmType M χ) x) : x = 1 := by
  have : Subsingleton (eig M χ) := ⟨fun a b => Subtype.ext (funext fun y => by
    rw [Subsingleton.elim y 0, eig_zero a.2, eig_zero b.2])⟩
  have : Subsingleton (OmType M χ) := (Submodule.Quotient.mk_surjective _).subsingleton
  refine hasLen_unique hv hx ⟨0, Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩, by simp⟩

theorem quot_step (M : Submodule R (N → C)) {L K : Submodule F N} (hLK : L ≤ K) (t : N) :
    stepOrder (M.comap (LinearMap.funLeft R C (L.mkQ : N → N ⧸ L))) (K.map L.mkQ) (L.mkQ t) =
      stepOrder M K t := by
  ext h
  constructor
  · rintro ⟨g, ⟨hg, hi⟩, rfl⟩
    refine ⟨g ∘ L.mkQ, ⟨hg, fun x k hk => ?_⟩, ?_⟩
    · show g (L.mkQ (x + k)) = g (L.mkQ x)
      rw [map_add (f := _)]
      exact hi _ _ (Submodule.mem_map_of_mem hk)
    · funext a
      show g (L.mkQ (a • t)) = g (a • L.mkQ t)
      rw [map_smul]
  · rintro ⟨g, ⟨hg, hi⟩, rfl⟩
    have hsur := L.mkQ_surjective
    have key : ∀ x, g (Function.surjInv hsur (L.mkQ x)) = g x := fun x => by
      have h1 : L.mkQ (Function.surjInv hsur (L.mkQ x) - x) = 0 := by
        rw [map_sub, Function.surjInv_eq hsur, sub_self]
      have h2 : Function.surjInv hsur (L.mkQ x) - x ∈ K :=
        hLK ((Submodule.Quotient.mk_eq_zero L).1 h1)
      have := hi x _ h2
      rwa [add_sub_cancel] at this
    refine ⟨g ∘ Function.surjInv hsur, ⟨?_, ?_⟩, ?_⟩
    · show (fun x => g (Function.surjInv hsur (L.mkQ x))) ∈ M
      simpa only [key] using hg
    · rintro x _ ⟨k, hk, rfl⟩
      obtain ⟨x, rfl⟩ := hsur x
      show g (Function.surjInv hsur (L.mkQ x + L.mkQ k)) = g (Function.surjInv hsur (L.mkQ x))
      rw [← map_add (f := _), key, key]
      exact hi x k hk
    · funext a
      show g (Function.surjInv hsur (a • L.mkQ t)) = g (a • t)
      rw [← map_smul, key]

theorem sub_stepRes (M : Submodule R (N → C)) {L K : Submodule F N} (hKL : K ≤ L) (t : L) :
    stepOrderRes (M.map (LinearMap.funLeft R C (Subtype.val : L → N))) (K.comap L.subtype) t =
      stepOrderRes M K (t : N) := by
  ext h
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, e⟩
    exact ⟨g, hg, fun a k hk => e a ⟨k, hKL hk⟩ hk⟩
  · rintro ⟨g, hg, e⟩
    exact ⟨_, ⟨g, hg, rfl⟩, fun a k hk => e a k hk⟩

theorem hasLen_line (M : Submodule R (N → C)) {t : N} (ht : t ≠ 0) {χ : MulChar F R} {x : NNReal}
    (hx : HasLen v R (OmType (stepOrder M (⊥ : Submodule F N) t) χ) x) :
    HasLen v R (OmType (M.map (LinearMap.funLeft R C
      (Subtype.val : Submodule.span F {t} → N))) χ) x := by
  refine hasLen_transport (LinearEquiv.toSpanNonzeroSingleton F N t ht) (fun g => ?_) hx
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g, ⟨hg, fun x k hk => ?_⟩, rfl⟩
    obtain rfl : k = 0 := hk
    rw [add_zero]
  · rintro ⟨g', ⟨hg, -⟩, e⟩
    refine ⟨g', hg, ?_⟩
    funext y
    obtain ⟨a, rfl⟩ := (LinearEquiv.toSpanNonzeroSingleton F N t ht).surjective y
    exact congrFun e a

end PositivityTheory.HtPt.Rd
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb

theorem mem_ctrSet_of {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {i : Ω →+* Ω'} {p' : Cpt ξ'}
    (c : κ) (hc : x c ≠ 0) (ho : ∀ r : o, i (algebraMap o Ω r) ∈ regAt ξ' p')
    (hx : ∀ j, i (x j / x c) ∈ regAt ξ' p') : p' ∈ ctrSet o x i ξ' := by
  refine ⟨c, hc, fun a ha => ?_⟩
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact hx j
  | algebraMap r => exact ho r
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

theorem join_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (w : κ' → Ω') (M' : PModel o (joinCo i x w)), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → ∀ p' : Cpt M'.ξ, p' ∈ ctrSet o x i M'.ξ ∧ ∃ l, InChart M'.ξ w l p' := by
  intro o _ Ω _ _ κ κ' x Ω' _ _ i w M' hi p'
  obtain ⟨⟨c, l⟩, hc⟩ := M'.tie.cover p'
  have h0 : i (x c) * w l ≠ 0 := hc.1
  have h1 := left_ne_zero_of_mul h0
  have h2 := right_ne_zero_of_mul h0
  refine ⟨mem_ctrSet_of c ((map_ne_zero i).1 h1) (fun r => ?_) fun j => ?_, l, h2, fun j => ?_⟩
  · rw [hi]
    exact (M'.tie.ring (c, l) hc.1 _).1 (Subalgebra.algebraMap_mem _ r) p' hc
  · have := hc.2 (j, l)
    simp only [joinCo] at this
    rwa [mul_div_mul_right _ _ h2, ← map_div₀] at this
  · have := hc.2 (c, j)
    simp only [joinCo] at this
    rwa [mul_div_mul_left _ _ h1] at this

end PositivityTheory.HtPt.Mb
end
