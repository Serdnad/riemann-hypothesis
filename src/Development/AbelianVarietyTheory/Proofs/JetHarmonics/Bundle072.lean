module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBFr
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm.NabJet
open MvPowerSeries

variable {k : Type} [CommRing k] {d n : ℕ}

theorem coeff_mul_congr (N : ℕ) (f g E : PS k n d)
    (h : ∀ a : Fin n × Fin d →₀ ℕ, a.degree ≤ N → coeff a f = coeff a g)
    (a : Fin n × Fin d →₀ ℕ) (ha : a.degree ≤ N) : coeff a (f * E) = coeff a (g * E) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = a := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = a.degree := by rw [← hp', map_add (f := _)]
  rw [h p.1 (by omega)]

theorem coeff_DofN_congr (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) (N : ℕ) (f g : PS k n d)
    (h : ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + 1 → coeff mo f = coeff mo g)
    (mo : Fin n × Fin d →₀ ℕ) (hmo : mo.degree ≤ N) :
    coeff mo (DofN F b v f) = coeff mo (DofN F b v g) := by
  classical
  unfold DofN

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = mo := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = mo.degree := by rw [← hp', map_add (f := _)]
  rw [coeff_pderiv, coeff_pderiv, h]
  rw [map_add (f := _), Finsupp.degree_single]
  omega

theorem coeff_iterate_DofN_congr (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) (r : ℕ) :
    ∀ (N : ℕ) (f g : PS k n d),
      (∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + r → coeff mo f = coeff mo g) →
      ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N →
        coeff mo ((DofN F b v)^[r] f) = coeff mo ((DofN F b v)^[r] g) := by
  induction r with
  | zero => intro N f g h mo hmo; exact h mo hmo
  | succ r ih =>
    intro N f g h mo hmo
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih N _ _ (coeff_DofN_congr F b v (N + r) f g h) mo hmo

theorem coeff_foldr_DofN_congr (F : Fin d → PS k 2 d) {Ix : Type} (cp : Ix → Fin n) (u : Ix → Fin d → k) (m : Ix → ℕ)
    (f g : PS k n d) (L : List Ix) :
    ∀ N : ℕ,
      (∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + (L.map m).sum → coeff mo f = coeff mo g) →
      ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N →
        coeff mo (L.foldr (fun l s => (DofN F (cp l) (u l))^[m l] s) f) =
          coeff mo (L.foldr (fun l s => (DofN F (cp l) (u l))^[m l] s) g) := by
  induction L with
  | nil => intro N h mo hmo; exact h mo hmo
  | cons l L ih =>
    intro N h mo hmo
    rw [List.foldr_cons, List.foldr_cons]
    refine coeff_iterate_DofN_congr F (cp l) (u l) (m l) N _ _ (ih (N + m l) fun mo' h' => h mo' ?_) mo hmo
    rw [List.map_cons, List.sum_cons]
    omega

theorem constantCoeff_DmonN_congr (F : Fin d → PS k 2 d) {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k)
    (m : Ix →₀ ℕ) (f g : PS k n d)
    (h : ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ m.degree → coeff mo f = coeff mo g) :
    constantCoeff (DmonN F cp u m f) = constantCoeff (DmonN F cp u m g) := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
  unfold DmonN
  refine coeff_foldr_DofN_congr F cp u m f g _ 0 (fun mo' h' => h mo' ?_) 0 (by simp)
  rwa [Finset.sum_map_toList, ← Finsupp.degree_eq_sum, zero_add] at h'

theorem isLinearMap_DofN (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) :
    IsLinearMap k (DofN F b v : PS k n d → PS k n d) := by
  constructor
  · intro f g
    unfold DofN
    simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]
  · intro c f
    unfold DofN
    simp only [Derivation.map_smul, mul_smul_comm, Finset.smul_sum]

theorem isLinearMap_iterate {M : Type} [AddCommGroup M] [Module k M] (φ : M → M) (hφ : IsLinearMap k φ) (r : ℕ) :
    IsLinearMap k φ^[r] := by
  induction r with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | succ r ih =>
    constructor
    · intro f g
      simp only [Function.iterate_succ_apply, hφ.map_add (f := _), ih.map_add (f := _)]
    · intro c f
      simp only [Function.iterate_succ_apply, hφ.map_smul, ih.map_smul]

theorem isLinearMap_DmonN (F : Fin d → PS k 2 d) {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k)
    (m : Ix →₀ ℕ) : IsLinearMap k (DmonN F cp u m : PS k n d → PS k n d) := by
  unfold DmonN
  induction (Finset.univ : Finset Ix).toList with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | cons l L ih =>
    have hl := isLinearMap_iterate _ (isLinearMap_DofN F (cp l) (u l)) (m l)
    constructor
    · intro f g
      simp only [List.foldr_cons]
      rw [ih.map_add (f := _), hl.map_add (f := _)]
    · intro c f
      simp only [List.foldr_cons]
      rw [ih.map_smul, hl.map_smul]

theorem constantCoeff_DpolyN_eq (F : Fin d → PS k 2 d) {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k)
    (P : MvPolynomial Ix k) (f : PS k n d) (S : Finset (Ix →₀ ℕ)) (hS : P.support ⊆ S) :
    constantCoeff (DpolyN F cp u P f) = ∑ m ∈ S, P.coeff m * constantCoeff (DmonN F cp u m f) := by
  unfold DpolyN

  rw [map_sum]
  simp only [map_mul, constantCoeff_C]
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul]

end GlobalTheory.PowGerm.NabJet

namespace GlobalTheory.PowGerm
open MvPowerSeries

theorem nabJet : NabJetSt := by
  intro R _ d O _ _ B k _ _ _ h w0 q n Ix _ cp u
  classical
  refine ⟨fun P f g hfg => ?_, fun P J _ c f => ?_, fun f J _ c P => ?_⟩
  · unfold nabValN
    rw [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl, NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl]
    refine Finset.sum_congr rfl fun m hm => ?_
    congr 1
    refine NabJet.constantCoeff_DmonN_congr _ cp u m _ _ fun mo hmo => ?_
    refine NabJet.coeff_mul_congr P.totalDegree f g _ hfg mo (hmo.trans ?_)
    have := MvPolynomial.le_totalDegree hm
    rwa [Finsupp.degree_apply]
  · unfold nabValN
    simp only [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hl := NabJet.isLinearMap_DmonN (B.FK k) cp u m

    rw [Finset.sum_mul, ← IsLinearMap.mk'_apply hl, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, map_smul, IsLinearMap.mk'_apply, smul_eq_C_mul, map_mul, constantCoeff_C]
    ring
  · unfold nabValN
    set S : Finset (Ix →₀ ℕ) := (∑ j, c j • P j).support ∪ Finset.univ.biUnion fun j => (P j).support with hS
    rw [NabJet.constantCoeff_DpolyN_eq _ cp u _ _ S Finset.subset_union_left]
    have hj : ∀ j, (P j).support ⊆ S := fun j =>
      (Finset.subset_biUnion_of_mem (fun j => (P j).support) (Finset.mem_univ j)).trans Finset.subset_union_right
    simp only [fun j => NabJet.constantCoeff_DpolyN_eq (B.FK k) cp u (P j)
      (f * FB.expS k ((q : k) • ∑ b, ev ![pt k d b] (B.hL k h w0))) S (hj j), Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul, _root_.mul_assoc]

end GlobalTheory.PowGerm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowGerm.UnivConv

variable {V : Type} [CommRing V]

def toAt (A : Type) [CommRing A] [Algebra V A] : Chart.sp (R₀ := V) A ⟶ overAt (𝟙 (Sp V)) A :=
  Over.homMk (𝟙 _) (by simp)

def ofAt (A : Type) [CommRing A] [Algebra V A] : overAt (𝟙 (Sp V)) A ⟶ Chart.sp (R₀ := V) A :=
  Over.homMk (𝟙 _) (by simp)

theorem toAt_ofAt (A : Type) [CommRing A] [Algebra V A] : toAt (V := V) A ≫ ofAt A = 𝟙 _ :=
  Over.OverMorphism.ext (Category.comp_id _)

theorem ofAt_toAt (A : Type) [CommRing A] [Algebra V A] : ofAt (V := V) A ≫ toAt A = 𝟙 _ :=
  Over.OverMorphism.ext (Category.comp_id _)

theorem spMap_toAt {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B) :
    Chart.spMap f ≫ toAt A = toAt B ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f :=
  Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm)

theorem ofAt_spMap {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B) :
    ofAt B ≫ Chart.spMap f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) f ≫ ofAt A :=
  Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm)

def ren {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) : Chart.JetR V (Fin N) m ≃ₐ[V] Jet V κ m :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv V β) (by
    rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp, orig]
    congr 2
    ext p
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨β.symm k, by simp⟩
    · rintro ⟨i, rfl⟩
      exact ⟨β i, by simp⟩)

theorem ren_zR {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) (i : Fin N) :
    ren (V := V) β m (Chart.zR m i) = Ideal.Quotient.mk _ (MvPolynomial.X (β i)) := by
  show Ideal.Quotient.mk _ (MvPolynomial.rename β (MvPolynomial.X i)) = _
  rw [MvPolynomial.rename_X]

theorem aug_ren {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (jetAug : Jet V κ m →ₐ[V] V).comp (ren (V := V) β m).toAlgHom = Chart.jetAug V (Fin N) m :=
  Chart.jet_ext fun j => by
    rw [Chart.jetAug_zR]
    show jetAug (ren (V := V) β m (Chart.zR m j)) = 0
    rw [ren_zR]
    show MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X (β j)) = 0
    simp

theorem trunc_ren {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m).comp (ren (V := V) β (m + 1)).toAlgHom =
      (ren (V := V) β m).toAlgHom.comp (Chart.jetTruncR V (Fin N) m) :=
  Chart.jet_ext fun j => rfl

theorem aug_symm {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (Chart.jetAug V (Fin N) m).comp (ren (V := V) β m).symm.toAlgHom = jetAug := by
  rw [← aug_ren β m]
  exact AlgHom.ext fun a => by simp

theorem trunc_symm {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (Chart.jetTruncR V (Fin N) m).comp (ren (V := V) β (m + 1)).symm.toAlgHom =
      (ren (V := V) β m).symm.toAlgHom.comp (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) :=
  AlgHom.ext fun a => by
    obtain ⟨b, rfl⟩ := (ren (V := V) β (m + 1)).surjective a
    have h : jetTrunc (ren (V := V) β (m + 1) b) = ren (V := V) β m (Chart.jetTruncR V (Fin N) m b) :=
      AlgHom.congr_fun (trunc_ren (V := V) β m) b
    show Chart.jetTruncR V (Fin N) m ((ren (V := V) β (m + 1)).symm (ren (V := V) β (m + 1) b)) =
      (ren (V := V) β m).symm (jetTrunc (ren (V := V) β (m + 1) b))
    rw [h, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]

theorem zero_eq (N m : ℕ) : Chart.jetZeroR V (Fin N) m =
    (Algebra.ofId V (Chart.JetR V (Fin N) 0)).comp (Chart.jetAug V (Fin N) m) :=
  Chart.jet_ext fun j => by
    rw [AlgHom.comp_apply, Chart.jetAug_zR, map_zero]
    show Ideal.Quotient.mk _ (MvPolynomial.X j) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one]
    exact Ideal.subset_span ⟨j, rfl⟩

end GlobalTheory.PowGerm.UnivConv

namespace GlobalTheory.PowGerm
open UnivConv

theorem univConv : UnivConvSt := by
  intro V _ G _ κ z hz N β
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨fun m => Chart.spMap (ren (V := V) β m).symm.toAlgHom ≫ toAt _ ≫ z m, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro m
    rw [← Category.assoc, Chart.spMap_comp, trunc_symm, ← Chart.spMap_comp, Category.assoc,
      ← Category.assoc (Chart.spMap jetTrunc), spMap_toAt, Category.assoc, h1]
  · intro m
    rw [← Category.assoc, Chart.spMap_comp, zero_eq, AlgHom.comp_assoc, aug_symm, ← Chart.spMap_comp, Category.assoc,
      ← Category.assoc (Chart.spMap jetAug), spMap_toAt, Category.assoc, h2, ← Category.assoc]
    exact MonObj.comp_one _
  · intro A _ _ aug m hm y hy
    obtain ⟨φ, ⟨hφ1, hφ2⟩, hu⟩ := h3 A aug m hm (ofAt A ≫ y) (by
      rw [← Category.assoc, ← ofAt_spMap, Category.assoc, hy]
      exact MonObj.comp_one _)
    refine ⟨φ.comp (ren (V := V) β m).toAlgHom, ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, hφ1, aug_ren]
    · have e : (φ.comp (ren (V := V) β m).toAlgHom).comp (ren (V := V) β m).symm.toAlgHom = φ :=
        AlgHom.ext fun a => by simp
      rw [← Category.assoc, Chart.spMap_comp, e, ← Category.assoc, spMap_toAt, Category.assoc, ← hφ2,
        ← Category.assoc, toAt_ofAt, Category.id_comp]
    · rintro ψ ⟨hψ1, hψ2⟩
      have e := hu (ψ.comp (ren (V := V) β m).symm.toAlgHom) ⟨by rw [← AlgHom.comp_assoc, hψ1, aug_symm], by
        rw [hψ2, ← Category.assoc (Chart.spMap ψ), Chart.spMap_comp, ← Category.assoc, ofAt_spMap, Category.assoc,
          ← Category.assoc (ofAt _), ofAt_toAt, Category.id_comp]⟩
      rw [← e]
      exact AlgHom.ext fun a => by simp
  · intro m
    refine ⟨ren β m, ren_zR β m, ?_⟩
    have e : Chart.spMap (ren (V := V) β m).toAlgHom ≫
        Chart.spMap (ren (V := V) β m).symm.toAlgHom ≫ toAt _ ≫ z m = toAt _ ≫ z m := by
      have e' : (ren (V := V) β m).toAlgHom.comp (ren (V := V) β m).symm.toAlgHom = AlgHom.id V _ :=
        AlgHom.ext fun a => by simp
      have e'' : Chart.spMap (AlgHom.id V (Jet V κ m)) = 𝟙 _ :=
        Over.OverMorphism.ext (Spec.map_id _)
      rw [← Category.assoc, Chart.spMap_comp, e', e'', Category.id_comp]
    exact (Category.id_comp _).symm.trans (congrArg CommaMorphism.left e).symm

end GlobalTheory.PowGerm
end
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PowGerm

namespace GlobalTheory.LinkEps

theorem linkEps : LinkEpsSt := by
  intro E _ _ _ H V _ _ t d FT act ph1 ph2 sy ad tg xT eT wPT hch _ _ htr j hj
  have hL := t.PP.isLB
  have hi0 : (e0 t (𝟙 (Sp V))) ⁻¹ᵁ t.PP.L.U j = ⊤ := by
    refine top_unique fun y _ => ?_
    exact hj (x := (toUnit (overAt (𝟙 (Sp V)) V)).left y) trivial
  have hW : ∀ m, LB.wchart t.PP.L
      (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (fun _ => j) = ⊤ := fun m =>
    wchart_top t (𝟙 (Sp V)) d j hi0 _ fun i => by
      rw [vec2 (fun i => jptG t (𝟙 (Sp V)) d xT m i)]; exact jpt_aug hch m i
  have hU : ∀ m, ∃ u : Γ((jOG (𝟙 (Sp V)) d m 2).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG (𝟙 (Sp V)) d m 2).left) (z : Z)
      (J : (Z ⟶ t.G.left) → t.PP.L.ι),
      (∀ I, J (r ≫ cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I) = j) →
      (val (eT m) r z J).val = gs r z ⊤ u := by
    intro m
    refine ⟨((jOG (𝟙 (Sp V)) d m 2).left.presheaf.map (homOfLE (hW m).ge).op).hom ((eT m).s (fun _ => j)).val,
      fun Z r z J hJ => ?_⟩
    exact (congrArg Units.val (val_of (eT m) r z J (fun _ => j) hJ)).trans
      ((gs_unit r z _ ((hW m).ge trivial) _).symm.trans (gs_res r z (hW m).ge trivial _).symm)
  choose U hU using hU
  have hUc : ∀ m, U m = (ρn (𝟙 (Sp V)) d 2 m).left.appTop.hom (U (m + 1)) := by
    intro m
    refine fn_ext (V := ⊤) fun y _ => ?_
    obtain ⟨J, hJ, hJi⟩ := exists_good t.PP.L hL y
      (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (fun _ => j)
      (fun _ _ _ => rfl) (fun I => Set.mem_iInter.1 ((hW m).ge (Set.mem_univ y)) I)
    have hmor : ∀ I : ULift (Finset (Fin 2)), (𝟙 _ ≫ (ρn (𝟙 (Sp V)) d 2 m).left) ≫
        cφG t ![jptG t (𝟙 (Sp V)) d xT (m + 1) (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT (m + 1) (1 : Fin 2)] I =
        cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I := by
      intro I
      rw [Category.id_comp, vec2 (fun i => jptG t (𝟙 (Sp V)) d xT (m + 1) i),
        vec2 (fun i => jptG t (𝟙 (Sp V)) d xT m i)]
      simp only [cφG, ← Over.comp_left]
      refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
      exact congrArg (fun f => psum t.G f I.down) (funext fun i => jpt_trunc hch m i)
    have e0' := hU m _ (𝟙 _) y J (fun I => (congrArg J (Category.id_comp _)).trans (hJi I))
    have e1 := hU (m + 1) _ (𝟙 _ ≫ (ρn (𝟙 (Sp V)) d 2 m).left) y J (fun I => (congrArg J (hmor I)).trans (hJi I))
    have e2 := (val_pull hJ (eT (m + 1)) _ _).symm.trans (val_corr hJ (htr m) (𝟙 _))
    have e3 := gs_pull (𝟙 _) (ρn (𝟙 (Sp V)) d 2 m).left y ⊤ trivial (U (m + 1))
    exact e0'.symm.trans ((congrArg Units.val e2).symm.trans (e1.trans e3.symm))
  choose a ha using fun m => (⟨_, congrArg (fun f => CommRingCat.Hom.hom f (U m))
    (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet V (Fin 2 × Fin d) m))))⟩ :
      ∃ b, toΓ (Jet V (Fin 2 × Fin d) m) b = U m)
  have hac : ∀ m, (jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _) (a (m + 1)) = a m := by
    intro m
    apply toΓ_injective
    rw [ha m, hUc m, ← ha (m + 1)]
    exact congrArg (fun f => CommRingCat.Hom.hom f (a (m + 1)))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _) :
        Jet V (Fin 2 × Fin d) (m + 1) →+* Jet V (Fin 2 × Fin d) m)))
  obtain ⟨f, hf⟩ := exists_ps_of_jets a hac
  refine ⟨f, fun m y J _ hJ => ?_⟩
  rw [hf m, ha m]
  exact hU m _ (𝟙 _) y J hJ

end GlobalTheory.LinkEps
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TopNum

theorem hsq_le (r : ℕ) (T b C : ℝ) (hC : 0 ≤ C) (hb : 2 ≤ b)
    (hT : T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ))) :
    Hsq r T b ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have h1 : (1 : ℝ) ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) :=
    Real.one_le_rpow hb1 (mul_nonneg hC (Nat.cast_nonneg _))
  have h2 : max 1 T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) := max_le h1 hT
  have h3 : (C + 10) * ((2 * r + 2 : ℕ) : ℝ)
      = C * ((2 * r + 2 : ℕ) : ℝ) + ((20 * (r + 1) : ℕ) : ℝ) := by
    push_cast; ring
  rw [h3, Real.rpow_add hb0, Real.rpow_natCast]
  unfold Hsq
  exact mul_le_mul_of_nonneg_right h2 (pow_nonneg hb0.le _)

theorem top_num : ∀ (r : ℕ) (T T' b C : ℝ), 0 ≤ C → 2 ≤ b → T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) → T' ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) → Real.sqrt (Hsq r T b * Hsq r T' b) ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := by
  intro r T T' b C hC hb hT hT'
  have hb0 : 0 < b := by linarith
  have h1 := hsq_le r T b C hC hb hT
  have h2 := hsq_le r T' b C hC hb hT'
  have hp : 0 ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := Real.rpow_nonneg hb0.le _
  have h0 : 0 ≤ Hsq r T' b := by
    unfold Hsq
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (pow_nonneg hb0.le _)
  rw [Real.sqrt_le_left hp, sq]
  exact mul_le_mul h1 h2 h0 hp

end GlobalTheory.TopNum
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem bessel_nonzero_on_translates : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), R.IsDS ε mu → IsBes R z π l → NzOn R l → ∃ v ∈ R.TK, l v ≠ 0 := by
  intro hH k r ε mu R Wp _ _ _ _ z π l hds hB hnz
  obtain ⟨⟨-, -, hKF, -⟩, hCyc, -⟩ := hH
  have hex : ∃ w0, PI.UpqRep.IsLowUnitH k r ε mu R.σ w0 := by
    obtain ⟨P, hP, -, -, -, -, -, ⟨S, hS⟩, -⟩ := hds.2
    obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, P, hP, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · exact Submodule.smul_mem _ _ (Submodule.mem_sSup.mpr fun N hN => hN S hS hvS)
  obtain ⟨w0, hlow⟩ := hex
  have hwK : R.KFin w0 := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow
  by_contra hcon
  push_neg at hcon
  obtain ⟨w, hw, hlw⟩ := hnz
  refine hlw (Formalism.FourierDecayAlt.P.bessel_ne_zero_of_cyclic_orbit hCyc hKF k r ε mu R.H R.σ w0 Wp z Formalism.QuantumDeterminants.cStd π hds.1 hds.2 hlow
    l hB (fun x hx => hcon x ?_) w hw)
  refine Submodule.span_mono ?_ hx
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, hg, w0, hwK, rfl⟩

end GlobalTheory
end
