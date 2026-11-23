module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle299
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle301
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle300
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.FilIsSubDPIdeal
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle149
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle163
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.QuoK

section Abstract
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem toSq_bijective_of_bot (a₀ b : IdF A) (h0 : ∀ T, a₀.S T = ⊤) (hb : ∀ T, b.S T = ⊥) (j : ℕ) :
    Function.Bijective ((toSq a₀ b h0).pull j) := by
  refine CrystallineSemistableComparison.P.mapH_bij (toSq a₀ b h0).hom (fun n => ⟨fun f f' h => ?_, fun y => ?_⟩) j
  · funext s
    have h1 := congrArg Subtype.val (congrFun h s)
    have h2 := Ideal.Quotient.eq.1 h1
    rw [hb] at h2
    exact sub_eq_zero.1 h2
  · have hm : ∀ s : ComposableArrows C n, ∃ t : A.obj (s.obj (Fin.last n)),
        Ideal.Quotient.mk _ t = (show sqM a₀ b _ from y s).1 :=
      fun s => Ideal.Quotient.mk_surjective _
    choose t ht using hm
    exact ⟨t, funext fun s => Subtype.ext (ht s)⟩

end Abstract

section Concrete
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem ks_le_of_le {u s : ℕ} (hus : u ≤ s) (𝒱 : Set X.Opens) : KS q u 𝒱 ≤ KS q s 𝒱 := by
  rintro T ⟨⟨h1, h2⟩, hV⟩
  exact ⟨⟨le_bot_iff.1 (h1 ▸ T.pdPow_anti hus), h2⟩, hV⟩

theorem quoK_comm {u s : ℕ} (hus : u ≤ s) (𝒱 : Set X.Opens) (r : ℤ) (j : ℕ) (x : HdR q j) :
    ((incl (ks_le_of_le q hus 𝒱)).sq (incl_fil _ 0) (incl_fil _ r)).pull j (quoK q (KS q s 𝒱) r j x) =
      quoK q (KS q u 𝒱) r j x := by
  obtain ⟨z, hz, hx⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx (CH.modF (thA (smFun X q)))) j).1 x
  subst hx
  rfl

theorem quoK_bij_self {u : ℕ} (𝒱 : Set X.Opens) (j : ℕ) (h : Function.Bijective (resK q (KS q u 𝒱) j)) :
    Function.Bijective (quoK q (KS q u 𝒱) (u : ℤ) j) := by
  have hB := toSq_bijective_of_bot (sFil (KS q u 𝒱) 0) (sFil (KS q u 𝒱) (u : ℤ)) (fun T => T.obj.pdPow_zero)
    (fun T => by
      have h := T.property.1.1
      change T.obj.pdPow ((u : ℤ).toNat) = ⊥
      rw [Int.toNat_natCast]
      exact h) j
  exact hB.comp h

end Concrete

theorem quoK_bijective : KH.KIso → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (U : Cov q) (s u : ℕ), (∀ α, U.d α < u) → u ≤ s → ∀ (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ (j : ℕ),
    Function.Bijective (quoK q (KS q s 𝒱) (u : ℤ) j) := by
  intro hK K _ _ X q U s u hd hus 𝒱 h𝒱 j
  have h1 := quoK_bij_self q 𝒱 j (hK q U u hd 𝒱 h𝒱 j).1
  have h2 := GlobalTheory.T.filtered_cohomology_restriction_bijective (TF 1 s) 1 u (Or.inr ⟨s, hus, rfl⟩) 𝒱 (ks_le_of_le q hus 𝒱) 0 (u : ℤ) le_rfl j
  refine (Function.Bijective.of_comp_iff' h2 _).1 ?_
  have e : (((incl (ks_le_of_le q hus 𝒱)).sq (incl_fil _ 0) (incl_fil _ (u : ℤ))).pull j) ∘ (quoK q (KS q s 𝒱) (u : ℤ) j) =
      quoK q (KS q u 𝒱) (u : ℤ) j := funext (quoK_comm q hus 𝒱 (u : ℤ) j)
  exact (congrArg Function.Bijective e).mpr h1

end GlobalTheory.CompanionTheory.QuoK
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.PolyTfCon

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

section Thickening

variable (T : Thick (nlFun γ 0 X q κ)) {l s : ℕ} (hT : TF l s T)


include hT in
theorem tr_facts : fil (trD T s) s = ⊥ ∧
    (∀ (r : ℕ) (x : trB T s), (l : trB T s) * x ∈ fil (trD T s) r → x ∈ fil (trD T s) r) ∧
    IsNilpotent (trJ T s) :=
  GlobalTheory.CompanionTheory.SiteTr.tr_tf T.δ l s (trD T s) (trD_spec T s).1 hT.1 hT.2

abbrev pT : Thick (nlFun γ 0 X q κ) :=
  polyTr T s ⟨fun h => absurd rfl h, fun _ => (tr_facts T hT).2.2⟩

abbrev jT : T ⟶ pT T hT := homOf _ _ _ _ _ _ _

theorem pT_tf : TF l s (pT T hT) := ⟨(tr_facts T hT).1, (tr_facts T hT).2.1⟩

abbrev xT : trB T s := Ideal.Quotient.mk (trI T s) ((pq T.B).e 1)

theorem e_mem (B : Type) [CommRing B] (J : Ideal B) : (pq B).e 1 ∈ (pq B).ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem xT_mem : xT (s := s) T ∈ trJ T s := Ideal.mem_map_of_mem _ (e_mem _ _)

theorem sum_eq (b : ℕ →₀ T.B) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) =
      Ideal.Quotient.mk (trI T s) (b.sum fun k c => algebraMap T.B (pq T.B).P c * (eta T.δ).dpow k ((pq T.B).e 1)) := by

  rw [Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, (trD_spec T s).1.dpow_comp _ (e_mem _ _)]
  rfl

theorem toNat_sub (r : ℤ) (k : ℕ) : (r - k).toNat = r.toNat - k := by omega

theorem fil_coeff (b : ℕ →₀ T.B) (r : ℤ) (hr : r ≤ s) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) ∈ fil (trD T s) r.toNat ↔
      ∀ k : ℕ, b k ∈ fil T.δ (r - k).toNat := by
  rw [sum_eq]
  simpa only [toNat_sub] using
    (GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit T.δ s (trD T s) (trD_spec T s).1 b r.toNat (by omega) 0).1

theorem std_coeff (b : ℕ →₀ T.B) (r : ℤ) (hr : r ≤ s) (c : R) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) ∈
        fil (trD T s) r.toNat ⊔ Ideal.span {Ideal.Quotient.mk (trI T s) (algebraMap T.B (pq T.B).P (T.i c))} ↔
      ∀ k : ℕ, b k ∈ fil T.δ (r - k).toNat ⊔ Ideal.span {T.i c} := by
  rw [sum_eq]
  simpa only [toNat_sub] using
    (GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit T.δ s (trD T s) (trD_spec T s).1 b r.toNat (by omega) (T.i c)).2

theorem univ_tr {T' : Thick (nlFun γ 0 X q κ)} (hT' : T'.pdPow s = ⊥) (φ : T ⟶ T') (x : T'.B) (hx : x ∈ T'.J) :
    ∃! ψ : pT T hT ⟶ T', jT T hT ≫ ψ = φ ∧ ψ.φ (xT (s := s) T) = x := by
  obtain ⟨F, ⟨hF1, hF2, hF3⟩, hFu⟩ := GlobalTheory.CompanionTheory.PDUniv.pdPoly_universal T.δ T'.δ φ.φ φ.dp x hx
  have hk : trI T s ≤ RingHom.ker F := by
    intro z hz
    have h1 : F z ∈ fil T'.δ (max s 1) := FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le _ _ F hF3 _ (Ideal.mem_map_of_mem F hz)
    have h2 : fil T'.δ (max s 1) ≤ fil T'.δ s := GlobalTheory.Cris.ExpBij.dpFil_anti T'.δ (le_max_left _ _)
    have h3 : F z ∈ T'.pdPow s := h2 h1
    rw [hT'] at h3
    exact h3
  let g : trB T s →+* T'.B := Ideal.Quotient.lift (trI T s) F fun a ha => hk ha
  have hgF : g.comp (Ideal.Quotient.mk (trI T s)) = F := by
    refine RingHom.ext fun z => ?_
    exact Ideal.Quotient.lift_mk (trI T s) F fun a ha => hk ha
  have hg : g.comp (trF T s) = φ.φ := by
    rw [← RingHom.comp_assoc, hgF, hF1]
  have hdp : IsDPMorphism (trD T s) T'.δ g := (trD_spec T s).2 _ _ _ g (by rw [hgF]; exact hF3)
  have hle : trJ T s ≤ T'.J.comap g := Ideal.map_le_iff_le_comap.1 hdp.1
  refine ⟨descOf φ g hg hdp hle, ⟨hom_ext hg, (Ideal.Quotient.lift_mk (trI T s) F fun a ha => hk ha).trans hF2⟩, ?_⟩
  rintro ψ ⟨h1, h2⟩
  refine hom_ext ?_
  change ψ.φ = g
  have e := hFu (ψ.φ.comp (Ideal.Quotient.mk (trI T s))) ⟨?_, h2, ?_⟩
  · refine Ideal.Quotient.ringHom_ext ?_
    rw [e, hgF]
  · have := congrArg Thick.Hom.φ h1
    exact this
  · exact IsDPMorphism.comp _ ψ.dp (trD_spec T s).1

end Thickening

section Site

variable (l s : ℕ) (𝒱 : Set X.Opens)

abbrev Qc : ObjectProperty (Thick (nlFun γ 0 X q κ)) := St (TF l s) 𝒱

variable {l s 𝒱}

theorem pT_mem (T : (Qc (γ := γ) (q := q) (κ := κ) l s 𝒱).FullSubcategory) : Qc l s 𝒱 (pT T.obj T.property.1) := by
  obtain ⟨V, hV, h⟩ := T.property.2
  exact ⟨pT_tf _ _, V, hV, inU_hom (jT T.obj T.property.1) h⟩

variable (l s 𝒱)

def polyQ : Poly (sP (Qc (γ := γ) (q := q) (κ := κ) l s 𝒱)) where
  P T := ⟨pT T.obj T.property.1, pT_mem T⟩
  j T := ObjectProperty.homMk (jT T.obj T.property.1)
  X T := xT (s := s) T.obj
  X_mem T := xT_mem T.obj
  univ {T T'} φ x hx := by
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := univ_tr T.obj T.property.1 T'.property.1.1 φ.hom x hx
    refine ⟨ObjectProperty.homMk ψ, ⟨ObjectProperty.hom_ext _ h1, h2⟩, ?_⟩
    rintro ψ' ⟨h3, h4⟩
    exact ObjectProperty.hom_ext _ (hu ψ'.hom ⟨congrArg (fun f => f.hom) h3, h4⟩)
  span T z := by
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective (show trB T.obj s from z)
    obtain ⟨b, rfl⟩ := GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow T.obj.δ w
    exact ⟨b, (sum_eq T.obj b).symm⟩

theorem crit_fil (r : ℤ) (hr : r ≤ s) : (polyQ (γ := γ) (q := q) (κ := κ) l s 𝒱).Crit (sFil _) r :=
  fun T b => fil_coeff T.obj b r hr

theorem crit_std (r : ℤ) (hr : r ≤ s) (c : R) :
    (polyQ (γ := γ) (q := q) (κ := κ) l s 𝒱).Crit (fun r => stdI _ (some r) c) r :=
  fun T b => std_coeff T.obj b r hr c

end Site

theorem polyTf : KH.PolyTf := by
  intro O R _ _ I γ X q κ l s 𝒱
  exact ⟨polyQ l s 𝒱, fun r hr => ⟨crit_fil l s 𝒱 r hr, crit_std l s 𝒱 r hr⟩⟩

end GlobalTheory.CompanionTheory.PolyTfCon
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

theorem _root_.GlobalTheory.T.truncated_envelope_torsion_free : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (l s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → fil δ s = ⊥ → (∀ (r : ℕ) (x : B), (l : B) * x ∈ fil δ r → x ∈ fil δ r) → fil δ' s = ⊥ ∧ (∀ (r : ℕ) (x : (pq B).P ⧸ fil (eta δ) (max s 1)), (l : (pq B).P ⧸ fil (eta δ) (max s 1)) * x ∈ fil δ' r → x ∈ fil δ' r) ∧ IsNilpotent (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1)))) := by
  first | exact @GlobalTheory.CompanionTheory.SiteTr.tr_tf | exact GlobalTheory.CompanionTheory.SiteTr.tr_tf | (intros; apply GlobalTheory.CompanionTheory.SiteTr.tr_tf <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

theorem _root_.GlobalTheory.T.divided_power_envelope_filtration : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (b : ℕ →₀ B) (r : ℕ) (c : B), ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil (eta δ) r ↔ ∀ k, b k ∈ fil δ (r - k)) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c} ↔ ∀ k, b k ∈ fil δ (r - k) ⊔ Ideal.span {c}) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ Ideal.span {algebraMap B (pq B).P c} ↔ ∀ k, b k ∈ Ideal.span {c}) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) = 0 ↔ ∀ k, b k = 0) := by
  first | exact @GlobalTheory.CompanionTheory.PDCrit.coeff_criteria | exact GlobalTheory.CompanionTheory.PDCrit.coeff_criteria | (intros; apply GlobalTheory.CompanionTheory.PDCrit.coeff_criteria <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

theorem _root_.GlobalTheory.T.divided_power_envelope_universal : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {C : Type} [CommRing C] {J'' : Ideal C} (δ'' : DividedPowers J'') (f : B →+* C), IsDPMorphism δ δ'' f → ∀ x ∈ J'', ∃! F : (pq B).P →+* C, F.comp (algebraMap B (pq B).P) = f ∧ F ((pq B).e 1) = x ∧ IsDPMorphism (eta δ) δ'' F := by
  first | exact @GlobalTheory.CompanionTheory.PDUniv.pdPoly_universal | exact GlobalTheory.CompanionTheory.PDUniv.pdPoly_universal | (intros; apply GlobalTheory.CompanionTheory.PDUniv.pdPoly_universal <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

theorem _root_.GlobalTheory.T.flat_comp_envelope_algebraMap : ∀ {A B : Type} [CommRing A] [CommRing B] (i : A →+* B), i.Flat → ((algebraMap B (pq B).P).comp i).Flat := by
  first | exact @GlobalTheory.CompanionTheory.SitePD.pdPoly_flat_comp | exact GlobalTheory.CompanionTheory.SitePD.pdPoly_flat_comp | (intros; apply GlobalTheory.CompanionTheory.SitePD.pdPoly_flat_comp <;> assumption)
end

section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem _root_.GlobalTheory.T.iwahori_levi_unipotent_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ KOne k (Fin n),
    ∃ m : Levi k (fun a => Fin (d a)), leviEmb k e m ∈ KOne k (Fin n) ∧
      ∃ x ∈ unipRad k e ⊓ KOne k (Fin n), ∃ c ∈ lowC k e, g = leviEmb k e m * x * c := by
  first | exact @GlobalTheory.CompanionTheory.KOneFactor.kone_factor | exact GlobalTheory.CompanionTheory.KOneFactor.kone_factor | (intros; apply GlobalTheory.CompanionTheory.KOneFactor.kone_factor <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem exists_mirUin_gpProj_lift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (n : MirUin k (j + 1)),
    ∃ (u : MirUin k (m + (j + 1))) (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
      gpProj k m (j + 1) ⟨u, hh⟩ = (1, (n : Mir k (j + 1))) := by
  intro k _ _ _ _ m j n
  obtain ⟨v, hv, e⟩ := GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip k m (j + 1) (n : Mir k (j + 1)) n.2
  exact ⟨⟨v, hv⟩, v.2, e⟩

end GlobalTheory.CompanionTheory.LeibPhi

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem continuous_gpProj_phi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) :=
  GlobalTheory.CompanionTheory.BZMir.continuous_gpProj

end GlobalTheory.CompanionTheory.LeibPhi
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.WhitRank

theorem finrank_piTensorProduct_eq_prod {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)]
    [∀ i, Module ℂ (E i)] : Module.finrank ℂ (⨂[ℂ] i, E i) = ∏ i, Module.finrank ℂ (E i) := by
  open Module in
  rw [Module.finrank_eq_nat_card_basis (Basis.piTensorProduct fun i => Module.Free.chooseBasis ℂ (E i)),
    Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => (Module.finrank_eq_nat_card_basis (Module.Free.chooseBasis ℂ (E i))).symm

theorem finrank_eq_prod_of_nonempty_equiv {ι A : Type} [Fintype ι] [AddCommGroup A] [Module ℂ A] (E : ι → Type)
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] (e : Nonempty (A ≃ₗ[ℂ] ⨂[ℂ] i, E i)) :
    Module.finrank ℂ A = ∏ i, Module.finrank ℂ (E i) := by
  obtain ⟨f⟩ := e
  rw [f.finrank_eq, finrank_piTensorProduct_eq_prod]

theorem whitRankProd_of_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], WhitHeredity k → WhitRankProd k := by
  intro k _ _ _ _ hW ψ hψ hψ1 h N x hd
  obtain ⟨f⟩ := hW ψ hψ hψ1 h N (fun a => (x a).fst) hd (fun a => (x a).snd.rep.V) (fun a => (x a).rep)
    (fun a => (x a).snd.rep.smooth)
  exact finrank_eq_prod_of_nonempty_equiv _ ⟨f⟩

end GlobalTheory.CompanionTheory.WhitRank

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Leib

theorem nontrivial_piTensorProduct_iff {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] :
    Nontrivial (⨂[ℂ] i, M i) ↔ ∀ i, Nontrivial (M i) := by
  classical
  constructor
  · intro hN i
    by_contra hi
    rw [not_nontrivial_iff_subsingleton] at hi
    have h0 : ∀ x : ⨂[ℂ] i, M i, x = 0 := by
      intro x
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        rw [(PiTensorProduct.tprod ℂ).map_coord_zero i (Subsingleton.elim (f i) 0), smul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    obtain ⟨x, y, hxy⟩ := hN.exists_pair_ne
    exact hxy ((h0 x).trans (h0 y).symm)
  · intro hM
    have hv : ∀ i, ∃ v : M i, v ≠ 0 := fun i => @exists_ne _ (hM i) 0
    choose v hv using hv
    have hφ : ∀ i, ∃ φ : Module.Dual ℂ (M i), φ (v i) ≠ 0 := fun i => by
      by_contra hc
      simp only [not_exists, ne_eq, not_not] at hc
      exact hv i ((Module.forall_dual_apply_eq_zero_iff ℂ (v i)).1 hc)
    choose φ hφ using hφ
    refine ⟨⟨PiTensorProduct.tprod ℂ v, 0, fun h => ?_⟩⟩
    have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)) h
    simp only [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply] at h1
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hφ i) h1

theorem genericProdIff_of_whitHeredity (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : WhitHeredity k → GenericProdIff k := by
  intro hW h N d hd X _ _ π hsm
  obtain ⟨ψ, hψc, hψ1⟩ := GlobalTheory.LocGL.exists_continuous_addChar_ne_one (k := k)
  obtain ⟨e⟩ := hW ψ hψc hψ1 h N d hd X π hsm
  simp only [GlobalTheory.LocGL.isGeneric_iff_isGenericFor hψc hψ1, GlobalTheory.LocGL.IsGenericFor]
  exact Iff.trans ⟨fun hn => @Equiv.nontrivial _ _ e.symm.toEquiv hn, fun hn => @Equiv.nontrivial _ _ e.toEquiv hn⟩
    (nontrivial_piTensorProduct_iff _)

end GlobalTheory.CompanionTheory.Leib

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZSeg

theorem rank_piTensorProduct_le_one {ι : Type} [Fintype ι] (W : ι → Type) [∀ a, AddCommGroup (W a)]
    [∀ a, Module ℂ (W a)] (hW : ∀ a, Module.rank ℂ (W a) ≤ 1) : Module.rank ℂ (⨂[ℂ] a, W a) ≤ 1 := by
  classical
  choose w hw using fun a => rank_le_one_iff.1 (hW a)
  refine rank_le_one_iff.2 ⟨PiTensorProduct.tprod ℂ w, fun t => ?_⟩
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    choose c hc using fun a => hw a (f a)
    refine ⟨r * ∏ a, c a, ?_⟩
    have hf : f = fun a => c a • w a := funext fun a => (hc a).symm
    rw [hf, (PiTensorProduct.tprod ℂ).map_smul_univ, smul_smul]
    simp only [RingHom.id_apply]
  | add x y hx hy =>
    obtain ⟨r, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    exact ⟨r + s, add_smul _ _ _⟩

theorem whitRank_multiProd_le_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (ψ : AddChar k Circle) (hc : Continuous ψ)
    (h1 : ψ ≠ 1) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (hs : ∀ a, IsSmooth (π a))
    (hr : ∀ a, Module.rank ℂ (TwJacquet (π a) (unipB k (Fin (d a))) (whitChar ψ (d a))) ≤ 1) :
    Module.rank ℂ (TwJacquet (multiProd (stdBlocks d hd) π) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  obtain ⟨e⟩ := hH ψ hc h1 h N d hd X π hs
  exact e.rank_eq.le.trans (rank_piTensorProduct_le_one _ hr)

theorem whitRankStd_of_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k →
    GlobalTheory.BZSeg.WhitRankStd k := by
  intro k _ _ _ _ hH hR ψ hc h1 h N x hd
  exact whitRank_multiProd_le_one hH ψ hc h1 h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V) (fun a => (x a).rep)
    (fun a => (x a).2.rep.smooth)
    (fun a => hR ψ hc h1 (x a).1 (x a).2.rep.V (x a).rep (x a).2.rep.smooth (x a).2.rep.irr)

end GlobalTheory.CompanionTheory.BZSeg

end
end
