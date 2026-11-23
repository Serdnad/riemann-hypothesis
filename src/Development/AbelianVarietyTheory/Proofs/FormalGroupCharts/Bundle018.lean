module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionIffPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftInjective
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle015
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle005

@[expose] public section

section

noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart
namespace GlobalTheory.JetSer
variable {R : Type} [CommRing R] {κ : Type}

theorem jet_mk_eq_iff (m : ℕ) (P Q : MvPolynomial κ R) :
    (Ideal.Quotient.mk _ P : JetR R κ m) = Ideal.Quotient.mk _ Q ↔
      ∀ e : κ →₀ ℕ, Finsupp.degree e < m + 1 → P.coeff e = Q.coeff e := by
  rw [Ideal.Quotient.eq]
  refine (MvPolynomial.mem_pow_idealOfVars_iff' (m + 1) (P - Q)).trans ?_
  simp only [MvPolynomial.coeff_sub, sub_eq_zero]

variable [Finite κ]

theorem toJet_eq_mk_iff (m : ℕ) (g : MvPowerSeries κ R) (Q : MvPolynomial κ R) :
    toJet m g = Ideal.Quotient.mk _ Q ↔
      ∀ e : κ →₀ ℕ, Finsupp.degree e < m + 1 → coeff e g = Q.coeff e := by
  unfold toJet
  rw [jet_mk_eq_iff]
  refine forall₂_congr fun e he => ?_
  rw [coeff_truncTotal_eq_ite, if_pos he]

theorem toJet_eq_iff (m : ℕ) (g g' : MvPowerSeries κ R) :
    toJet m g = toJet m g' ↔ ∀ e : κ →₀ ℕ, Finsupp.degree e < m + 1 → coeff e g = coeff e g' := by
  refine (toJet_eq_mk_iff m g _).trans (forall₂_congr fun e he => ?_)
  rw [coeff_truncTotal_eq_ite, if_pos he]

theorem toJet_coe (m : ℕ) (Q : MvPolynomial κ R) :
    toJet m (Q : MvPowerSeries κ R) = Ideal.Quotient.mk _ Q :=
  (toJet_eq_mk_iff m _ Q).2 fun e _ => MvPolynomial.coeff_coe Q e


variable (R κ) in
def toJetHom (m : ℕ) : MvPowerSeries κ R →ₐ[R] JetR R κ m :=
  (truncTotalAlgHom κ R (m + 1)).restrictScalars R

theorem toJetHom_apply (m : ℕ) (g : MvPowerSeries κ R) : toJetHom R κ m g = toJet m g := rfl

theorem jetTruncR_toJet (m : ℕ) (g : MvPowerSeries κ R) :
    jetTruncR R κ m (toJet (m + 1) g) = toJet m g := by
  symm
  refine (toJet_eq_mk_iff m g (truncTotal (m + 1 + 1) g)).2 fun e he => ?_
  rw [coeff_truncTotal_eq_ite, if_pos (by omega)]

theorem jetAug_toJet (m : ℕ) (g : MvPowerSeries κ R) :
    jetAug R κ m (toJet m g) = constantCoeff g := by
  show MvPolynomial.aeval (fun _ : κ => (0 : R)) (truncTotal (m + 1) g) = _
  rw [MvPolynomial.aeval_zero', MvPolynomial.constantCoeff_eq, coeff_truncTotal_eq_ite, if_pos (by simp)]
  rfl

theorem eq_of_toJet_eq {g g' : MvPowerSeries κ R} (h : ∀ m, toJet m g = toJet m g') : g = g' := by
  ext e
  exact (toJet_eq_iff _ g g').1 (h (Finsupp.degree e)) e (Nat.lt_succ_self _)

theorem exists_toJet_eq (p : ∀ m, JetR R κ m) (hp : ∀ m, jetTruncR R κ m (p (m + 1)) = p m) :
    ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = p m := by
  choose P hP using fun m => Ideal.Quotient.mk_surjective (p m)
  have h1 : ∀ m (e : κ →₀ ℕ), Finsupp.degree e < m + 1 → (P (m + 1)).coeff e = (P m).coeff e := fun m => by
    rw [← jet_mk_eq_iff, hP m, ← hp m, ← hP (m + 1)]
    rfl
  have h2 : ∀ (e : κ →₀ ℕ) m, Finsupp.degree e ≤ m → (P (Finsupp.degree e)).coeff e = (P m).coeff e := by
    intro e m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [ih, h1 m e (by omega)]
  refine ⟨fun e => (P (Finsupp.degree e)).coeff e, fun m => ?_⟩
  rw [← hP m]
  exact (toJet_eq_mk_iff m _ _).2 fun e he => h2 e m (by omega)

theorem exists_jetHom {σ : Type} (a : σ → MvPowerSeries κ R) (ha : ∀ j, constantCoeff (a j) = 0) (m : ℕ) :
    ∃ ψ : JetR R σ m →ₐ[R] JetR R κ m, ∀ j, ψ (zR m j) = toJet m (a j) :=
  ⟨jetLift R (RingHom.ker (jetAug R κ m)) (ker_jetAug_pow κ m) (fun j => toJet m (a j))
    (fun j => (jetAug_toJet m (a j)).trans (ha j)), fun j => jetLift_zR _ _ _ _ j⟩

theorem jetHom_toJet {σ : Type} [Finite σ] (a : σ → MvPowerSeries κ R) (ha : ∀ j, constantCoeff (a j) = 0) (m : ℕ)
    (ψ : JetR R σ m →ₐ[R] JetR R κ m) (hψ : ∀ j, ψ (zR m j) = toJet m (a j)) (g : MvPowerSeries σ R) :
    ψ (toJet m g) = toJet m (subst a g) := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hpoly : ∀ Q : MvPolynomial σ R, ψ (Ideal.Quotient.mk _ Q) = toJet m (subst a (Q : MvPowerSeries σ R)) := by
    intro Q
    rw [subst_coe, ← toJetHom_apply]
    have : ψ.comp (Ideal.Quotient.mkₐ R _) = (toJetHom R κ m).comp (MvPolynomial.aeval a) := by
      apply MvPolynomial.algHom_ext
      intro j
      rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.aeval_X, toJetHom_apply]
      exact hψ j
    exact AlgHom.congr_fun this Q
  refine (hpoly (truncTotal (m + 1) g)).trans ((toJet_eq_iff m _ _).2 fun e he => ?_)
  set r : MvPowerSeries σ R := (truncTotal (m + 1) g : MvPolynomial σ R) - g with hr
  have hro : ((m + 1 : ℕ) : ℕ∞) ≤ r.order := nat_le_order fun d hd => by
    rw [hr, map_sub, MvPolynomial.coeff_coe, coeff_truncTotal_eq_ite, if_pos hd, sub_self]
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (a i).order := le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (ha i)
  have h2 : ((m + 1 : ℕ) : ℕ∞) ≤ (subst a r).order := by
    refine le_trans ?_ (le_order_subst hs r)
    calc ((m + 1 : ℕ) : ℕ∞) = 1 * ((m + 1 : ℕ) : ℕ∞) := (one_mul _).symm
      _ ≤ _ := mul_le_mul' h1 hro
  have h3 : coeff e (subst a r) = 0 := coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast he) h2)
  rwa [hr, ← substAlgHom_apply hs, map_sub, map_sub, sub_eq_zero, substAlgHom_apply, substAlgHom_apply] at h3

theorem jetAlg : JetAlgSt := fun R _ κ _ =>
  ⟨fun m => ⟨toJetHom R κ m, fun _ => rfl, fun j => toJet_X m j⟩,
    fun m g => ⟨jetTruncR_toJet m g, jetAug_toJet m g⟩,
    fun _ _ h => eq_of_toJet_eq h, exists_toJet_eq,
    fun _ _ a ha m => ⟨exists_jetHom a ha m, jetHom_toJet a ha m⟩⟩

end GlobalTheory.JetSer
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartUniv

section Jets
open ReciprocityTheory.ChartRestriction.G.Chart

variable {R : Type} [CommRing R]

theorem jetAug_eq (κ : Type) (m : ℕ) : jetAug R κ m = (jetAug R κ 0).comp (jetZeroR R κ m) :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm

theorem jetZero_zR (κ : Type) (m : ℕ) (j : κ) : jetZeroR R κ m (zR m j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact Ideal.subset_span ⟨j, rfl⟩)

theorem jetZero_eq (κ : Type) (m : ℕ) : jetZeroR R κ m = (Algebra.ofId R (JetR R κ 0)).comp (jetAug R κ m) :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR, map_zero, jetZero_zR]

theorem aug_comp_iff {κ κ' : Type} {m : ℕ} (ψ : JetR R κ m →ₐ[R] JetR R κ' m) :
    (jetAug R κ' m).comp ψ = jetAug R κ m ↔ ∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0 := by
  constructor
  · intro h j
    have := AlgHom.congr_fun h (zR m j)
    rw [AlgHom.comp_apply, jetAug_zR] at this
    rw [jetZero_eq, AlgHom.comp_apply, this, map_zero]
  · intro h
    refine jet_ext fun j => ?_
    rw [AlgHom.comp_apply, jetAug_zR, jetAug_eq, AlgHom.comp_apply, h, map_zero]

theorem spMap_id' (A : Type) [CommRing A] [Algebra R A] : spMap (R₀ := R) (AlgHom.id R A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [spMap_left]
  exact Spec.map_id _

def jetRen {κ κ' : Type} (f : κ → κ') (m : ℕ) : JetR R κ m →ₐ[R] JetR R κ' m :=
  jetLift R (RingHom.ker (jetAug R κ' m)) (ker_jetAug_pow κ' m) (fun j => zR m (f j)) (fun j => zR_mem_ker m (f j))

theorem jetRen_zR {κ κ' : Type} (f : κ → κ') (m : ℕ) (j : κ) : jetRen (R := R) f m (zR m j) = zR m (f j) :=
  jetLift_zR _ _ _ _ j

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem univ_all [IsLocalRing R] [Smooth G.hom] {κ : Type} {m : ℕ} (x : sp (R₀ := R) (JetR R κ m) ⟶ G)
    (h0 : spMap (jetZeroR R κ m) ≫ x = 1)
    (hu : ∀ (κ' : Type) (y : sp (R₀ := R) (JetR R κ' m) ⟶ G), spMap (jetZeroR R κ' m) ≫ y = 1 →
      ∃! ψ : JetR R κ m →ₐ[R] JetR R κ' m, (∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x)
    (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (hA : (RingHom.ker aug) ^ (m + 1) = ⊥)
    (y : sp (R₀ := R) A ⟶ G) (hy : spMap aug ≫ y = 1) :
    ∃! ψ : JetR R κ m →ₐ[R] A, aug.comp ψ = jetAug R κ m ∧ y = spMap ψ ≫ x := by
  obtain ⟨n, z, -, hz0, hzu⟩ := univChartLoc G
  have hxa : spMap (jetAug R κ m) ≫ x = 1 := by
    rw [jetAug_eq, ← spMap_comp, Category.assoc, h0, comp_one']
  obtain ⟨α, ⟨ha1, ha2⟩, -⟩ := hzu (JetR R κ m) (jetAug R κ m) m (ker_jetAug_pow κ m) x hxa
  obtain ⟨β, ⟨hb1, hb2⟩, -⟩ := hu (Fin n) (z m) (hz0 m)
  have hb1' := (aug_comp_iff β).2 hb1
  have hab : α.comp β = AlgHom.id R _ := by
    refine (hu κ x h0).unique ⟨(aug_comp_iff _).1 ?_, ?_⟩ ⟨fun j => jetZero_zR κ m j, ?_⟩
    · rw [← AlgHom.comp_assoc, ha1, hb1']
    · rw [← spMap_comp, Category.assoc, ← hb2, ← ha2]
    · rw [spMap_id', Category.id_comp]
  obtain ⟨ψ, ⟨h1, h2⟩, hψ⟩ := hzu A aug m hA y hy
  refine ⟨ψ.comp β, ⟨?_, ?_⟩, ?_⟩
  · rw [← AlgHom.comp_assoc, h1, hb1']
  · rw [← spMap_comp, Category.assoc, ← hb2, ← h2]
  · rintro φ ⟨g1, g2⟩
    have : φ.comp α = ψ := hψ _ ⟨by rw [← AlgHom.comp_assoc, g1, ha1], by
      rw [← spMap_comp, Category.assoc, ← ha2, ← g2]⟩
    rw [← this, AlgHom.comp_assoc, hab, AlgHom.comp_id]

theorem isUnivChart_ren [IsLocalRing R] [Smooth G.hom] {κ : Type} {d : ℕ} (e : κ ≃ Fin d)
    (x : ∀ m, sp (R₀ := R) (JetR R κ m) ⟶ G)
    (ht : ∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m)
    (h0 : ∀ m, spMap (jetZeroR R κ m) ≫ x m = 1)
    (hu : ∀ (κ' : Type) (m : ℕ) (y : sp (R₀ := R) (JetR R κ' m) ⟶ G), spMap (jetZeroR R κ' m) ≫ y = 1 →
      ∃! ψ : JetR R κ m →ₐ[R] JetR R κ' m, (∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x m) :
    IsUnivChart G d (fun m => spMap (jetRen e m) ≫ x m) := by
  refine ⟨fun m => ?_, fun m => ?_, fun A _ _ aug m hA y hy => ?_⟩
  · have : (jetTruncR R (Fin d) m).comp (jetRen e (m + 1)) = (jetRen e m).comp (jetTruncR R κ m) :=
      jet_ext fun j => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, jetRen_zR]
        exact (jetRen_zR (R := R) e m j).symm
    show _ ≫ _ ≫ _ = _ ≫ _
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, ht]
  · have : (jetZeroR R (Fin d) m).comp (jetRen e m) = (jetRen e 0).comp (jetZeroR R κ m) :=
      jet_ext fun j => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, jetRen_zR, jetZero_zR, jetZero_zR, map_zero]
    show _ ≫ _ ≫ _ = _
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, h0, comp_one']
  · obtain ⟨ψ, ⟨h1, h2⟩, hψ⟩ := univ_all (x m) (h0 m) (fun κ' => hu κ' m) A aug hA y hy
    have e1 : (jetRen (R := R) e m).comp (jetRen e.symm m) = AlgHom.id R _ :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetRen_zR, e.apply_symm_apply]; rfl
    have e2 : (jetRen (R := R) e.symm m).comp (jetRen e m) = AlgHom.id R _ :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetRen_zR, e.symm_apply_apply]; rfl
    have a1 : (jetAug R κ m).comp (jetRen e.symm m) = jetAug R (Fin d) m :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetAug_zR, jetAug_zR]
    have a2 : (jetAug R (Fin d) m).comp (jetRen e m) = jetAug R κ m :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetAug_zR, jetAug_zR]
    refine ⟨ψ.comp (jetRen e.symm m), ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, h1, a1]
    · show y = _ ≫ _ ≫ _
      rw [← Category.assoc, spMap_comp, AlgHom.comp_assoc, e2, AlgHom.comp_id]
      exact h2
    · rintro φ ⟨g1, g2⟩
      have : φ.comp (jetRen e m) = ψ := hψ _ ⟨by rw [← AlgHom.comp_assoc, g1, a2], by
        rw [← spMap_comp, Category.assoc]; exact g2⟩
      rw [← this, AlgHom.comp_assoc, e1, AlgHom.comp_id]

end Jets

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj

theorem isUnivChart_of_isChartJ : ∀ (T : Type) [CommRing T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∃ x0 : GlobalTheory.JetSer.Fam G (Fin d), Chart.IsUnivChart G d x0 ∧ ∃ ρ : ∀ m, JetR T (Fin 1 × Fin d) m →ₐ[T] Chart.JetR T (Fin d) m, (∀ m j, ρ m (zR m ((0 : Fin 1), j)) = Chart.zR m j) ∧ ∀ m, (x0 m).left = spMap (ρ m : JetR T (Fin 1 × Fin d) m →+* Chart.JetR T (Fin d) m) ≫ (x m).left := by
  intro T _ _ G _ _ hG d F x hx
  haveI := hG
  let e : Fin 1 × Fin d ≃ Fin d := Equiv.uniqueProd (Fin d) (Fin 1)
  refine ⟨fun m => Chart.spMap (jetRen e m) ≫ x m,
    isUnivChart_ren e x hx.trunc hx.zero hx.univ, fun m => jetRen e m, fun m j => jetRen_zR e m _, fun m => rfl⟩

end GlobalTheory.ChartUniv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.jetPoints_unit_law_action_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ((∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) ↔ (∀ m, homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x' m = 1)) ∧ (∀ F : Fin d → PS S 2 d, (∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m = jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)) ↔ (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))) ∧ ∀ act : 𝓞 E → Fin d → PS S 1 d, (∀ m (b : 𝓞 E), x m ≫ t.act.act b = homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m) ↔ (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) := by
  first | exact @GlobalTheory.jetPoints_laws_iff_pullback | exact GlobalTheory.jetPoints_laws_iff_pullback | (intros; apply GlobalTheory.jetPoints_laws_iff_pullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.primitiveIsoG_unique_on_abelian : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), IsAbelianScheme t.G → ∀ wP wP' : PrimTyG t, IsPrimG t wP → IsPrimG t wP' → wP = wP' := by
  first | exact @GlobalTheory.isPrimG_unique | exact GlobalTheory.isPrimG_unique | (intros; apply GlobalTheory.isPrimG_unique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.FrameSym

section Val

variable {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K K₁ : Type} [Fintype K] [Fintype K₁]

theorem val_tie (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (hm : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) {J' : (Z ⟶ X') → L'.ι}
    (hJ' : Good L' z J') :
    val c r z J = (∏ k, gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k) * val a r z J' := by
  have P := (maps_iff w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) (flatGen L F φ' ε c)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).1 hm
  · have := P Z r z (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => J' (r ≫ φ' k)) (fun k => hJ ((r ≫ φ' k) ≫ F))
      (fun k => hJ' (r ≫ φ' k))
    rw [Category.comp_id] at this
    rw [val_of c r z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc])]
    exact this
  · refine unit_ext fun y hy => ?_
    have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
    have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
      wchart_pull_le L F φ' j hy
    refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
    refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
    have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (c.s fun k => j k ⟨⟩)
    rw [Category.comp_id] at e
    exact e.symm

def scale (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ ε) :=
  ⟨fun j => res le_top u * g.s j⟩

theorem val_scale {φ : K → (Y ⟶ X)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb L φ ε)) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (scale φ ε u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) u) rfl)

theorem good_exists (hL : L.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good L z J := by
  choose d hd using fun χ : Z ⟶ X => exists_chart hL (χ z)
  exact ⟨d, hd⟩

theorem corr_sym_iff (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (hm : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c))
    (φ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (e : LB.Gen (LB.LinComb L φ ε₁)) (hc : LB.Gen.Corr L _ _ _ _ c e)
    (s : Y ⟶ Y) (hs : FormEq φ' ε (fun k => s ≫ φ' k) ε) (u : Γ(Y, ⊤)ˣ) :
    LB.Gen.Corr L _ _ _ _ e (scale _ _ u (LB.pullGen L φ ε₁ e s)) ↔
      LB.Gen.Corr L' _ _ _ _ a (scale _ _ u (LB.pullGen L' φ' ε a s)) := by
  have key : ∀ (y : Y) J J', Good L y J → Good L' y J' →
      (val e (𝟙 Y) y J = val (scale _ _ u (LB.pullGen L φ ε₁ e s)) (𝟙 Y) y J ↔
        val a (𝟙 Y) y J' = val (scale _ _ u (LB.pullGen L' φ' ε a s)) (𝟙 Y) y J') := by
    intro y J J' hJ hJ'
    rw [val_scale _ _ _ _ hJ, val_scale _ _ _ _ hJ', val_pull hJ, val_pull hJ', ← val_corr hJ hc, ← val_corr hJ hc,
      val_tie w φ' ε a c hm _ y hJ hJ', val_tie w φ' ε a c hm _ y hJ hJ']
    have h := hs _ (fun ψ => gw w ψ y (J (ψ ≫ F)) (J' ψ))
    simp only [Category.id_comp]
    rw [← h, mul_left_comm, mul_right_inj]
  constructor
  · intro h
    refine corr_of_val hL' fun y J' hJ' => ?_
    obtain ⟨J, hJ⟩ := good_exists hL y
    exact (key y J J' hJ hJ').1 (val_corr hJ h _)
  · intro h
    refine corr_of_val hL fun y J hJ => ?_
    obtain ⟨J', hJ'⟩ := good_exists hL' y
    exact (key y J J' hJ hJ').2 (val_corr hJ' h _)

end Val

theorem formEq_swap {B : Scheme.{0}} (G : Over B) [GrpObj G] [IsCommMonObj G] {T : Over B} (a b : T ⟶ G) (s : T ⟶ T)
    (ha : s ≫ a = b) (hb : s ≫ b = a) :
    FormEq (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![a, b] I.down).left) (cε 2)
      (fun I => s.left ≫ (psum G ![a, b] I.down).left) (cε 2) := by
  intro U _ h
  have hp : ∀ I : Finset (Fin 2), s.left ≫ (psum G ![a, b] I).left = (psum G ![b, a] I).left := fun I => by
    have := psum_hom (preHom (G := G) s) ![a, b] I
    have e : (fun i => preHom (G := G) s (![a, b] i)) = ![b, a] := by
      funext i; fin_cases i
      exacts [ha, hb]
    rw [e] at this
    exact congrArg (fun z => z.left) this
  simp only [hp]
  have hu : (Finset.univ : Finset (ULift.{0} (Finset (Fin 2)))) = {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} := by decide
  rw [hu]
  simp only [Finset.prod_insert (by decide : (⟨∅⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} : Finset _)),
    Finset.prod_insert (by decide : (⟨{0}⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{1}⟩, ⟨{0, 1}⟩} : Finset _)),
    Finset.prod_insert (by decide : (⟨{1}⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{0, 1}⟩} : Finset _)),
    Finset.prod_singleton]
  have p0 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs ∅ = 1 := fun _ => rfl
  have p1 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {0} = xs 0 * 1 := fun _ => rfl
  have p2 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {1} = xs 1 * 1 := fun _ => rfl
  have p3 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {0, 1} = xs 0 * (xs 1 * 1) := fun _ => rfl
  simp only [p0, p1, p2, p3, Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one]
  rw [_root_.mul_comm b a]
  exact congrArg _ (mul_left_comm _ _ _)

theorem jetMap_mk {R : Type} [CommRing R] {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' R) (hφ : ∀ i, φ i ∈ orig R κ')
    (p : MvPolynomial κ R) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.aeval φ p) := rfl

theorem swap_jpt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (m : ℕ)
    (φ : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (i k : Fin 2) (h : φ i = fun j => X (k, j)) :
    Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) ≫ jptG t x0 d x m i = jptG t x0 d x m k := by
  have e : (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)).comp (jetCopy d m i) = jetCopy d m k := by
    refine Ideal.Quotient.algHom_ext S (MvPolynomial.algHom_ext fun p => ?_)
    show jetSubstP m _ (jetCopy d m i (Ideal.Quotient.mk _ (X p))) = jetCopy d m k (Ideal.Quotient.mk _ (X p))
    simp [jetSubstP, jetCopy, jetMap_mk, h]
  rw [jptG, jptG, ← Category.assoc, ← e]
  congr 1
  apply Over.OverMorphism.ext
  simp only [Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem frame_sym_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (sy : PS S 2 d), (∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t.PP.L _ _ _ _ (e m) (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))) ↔ (∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (e' m) (scaleGenG t' _ _ (unitΓ u⁻¹) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w _ d x x' _ e e' _ _ ht sy
  refine forall_congr' fun m => exists_congr fun u => and_congr Iff.rfl ?_
  obtain ⟨c₁, hc, hm⟩ := ht m
  exact corr_sym_iff t.PP.isLB t'.PP.isLB w _ (cε 2) (e' m) c₁ hm
    (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) hc _
    (formEq_swap t'.G _ _ _ (swap_jpt t' _ d x' m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] 0 1 rfl)
      (swap_jpt t' _ d x' m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] 1 0 rfl)) (unitΓ u⁻¹)

end GlobalTheory.FrameSym
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.jetPoint_add_sqZero_eq_prod_mul_tangent : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) → (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) → (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) → ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (J : Ideal A), J * RingHom.ker aug = ⊥ → J ≤ RingHom.ker aug → ∀ (m : ℕ) (ψ ψ' : JetR R (Fin d) m →ₐ[R] A), aug.comp ψ = jetAug R (Fin d) m → aug.comp ψ' = jetAug R (Fin d) m → ∀ e : Fin d → (DualNumber R →ₐ[R] A), (∀ j, e j (TrivSqZeroExt.inr 1) ∈ J) → (∀ j, ψ' (zR m j) = ψ (zR m j) + e j (TrivSqZeroExt.inr 1)) → spMap ψ' ≫ x m = (∏ j, (spMap (e j) ≫ v j : sp (R₀ := R) A ⟶ G)) * (spMap ψ ≫ x m) := by
  first | exact @GlobalTheory.jet_add_sqZero_eq_prod_mul | exact GlobalTheory.jet_add_sqZero_eq_prod_mul | (intros; apply GlobalTheory.jet_add_sqZero_eq_prod_mul <;> assumption)
end
