module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle557
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle561
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle552
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle605
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle609
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismPushoutModAdicPowUniversal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle082
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle604
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.ProdStable

theorem quot_pi_bij {P : Type} [CommRing P] {n : ℕ} {Ps : Fin n → Type} [∀ i, CommRing (Ps i)]
    (g : ∀ i, P →+* Ps i) (hg : Function.Bijective fun (x : P) (i : Fin n) => g i x)
    (J : Ideal P) (Ji : ∀ i, Ideal (Ps i)) (hle : ∀ i, J ≤ (Ji i).comap (g i))
    (hJ : ∀ i, J.map (g i) = Ji i) :
    Function.Bijective fun (x : P ⧸ J) (i : Fin n) => Ideal.quotientMap (Ji i) (g i) (hle i) x := by
  classical
  have hsurj : ∀ i, Function.Surjective (g i) := fun i y => by
    obtain ⟨a, ha⟩ := hg.2 (Pi.single (M := Ps) i y)
    exact ⟨a, by simpa using congrFun ha i⟩
  choose e he0 using fun i => hg.2 (Pi.single (M := Ps) i 1)
  have he : ∀ i j, g j (e i) = Pi.single (M := Ps) i 1 j := fun i j => congrFun (he0 i) j
  let F : (P ⧸ J) →+* ∀ i, Ps i ⧸ Ji i := Pi.ringHom fun i => Ideal.quotientMap (Ji i) (g i) (hle i)
  change Function.Bijective F
  refine ⟨(injective_iff_map_eq_zero F).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hb : ∀ i, ∃ b ∈ J, g i b = g i a := fun i => by
      have := congrFun hx i
      change Ideal.Quotient.mk (Ji i) (g i a) = 0 at this
      rw [Ideal.Quotient.eq_zero_iff_mem, ← hJ i] at this
      exact (Ideal.mem_map_iff_of_surjective _ (hsurj i)).1 this
    choose b hbJ hbg using hb
    have ha : a = ∑ i, e i * b i := hg.1 <| funext fun j => by
      change g j a = g j (∑ i, e i * b i)

      rw [map_sum, Finset.sum_eq_single j]
      · rw [map_mul, he j j, Pi.single_eq_same, one_mul, hbg]
      · intro i _ hij
        rw [map_mul, he i j, Pi.single_eq_of_ne (Ne.symm hij), zero_mul]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [ha]
    exact J.sum_mem fun i _ => J.mul_mem_left _ (hbJ i)
  · choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)
    obtain ⟨a, ha⟩ := hg.2 z
    refine ⟨Ideal.Quotient.mk J a, funext fun i => ?_⟩
    change Ideal.Quotient.mk (Ji i) (g i a) = y i
    rw [show g i a = z i from congrFun ha i, hz]

theorem flat_of_pi {A P : Type} [CommRing A] [CommRing P] {n : ℕ} {Ps : Fin n → Type} [∀ i, CommRing (Ps i)]
    (f : A →+* P) (g : ∀ i, P →+* Ps i) (hg : Function.Bijective fun (x : P) (i : Fin n) => g i x)
    (hf : ∀ i, ((g i).comp f).Flat) : f.Flat := by
  classical
  let e : P ≃+* ∀ i, Ps i := RingEquiv.ofBijective (Pi.ringHom g) hg
  have hpi : (Pi.ringHom fun i => (g i).comp f).Flat := by
    letI : ∀ i, Algebra A (Ps i) := fun i => ((g i).comp f).toAlgebra
    haveI : ∀ i, Module.Flat A (Ps i) := fun i => RingHom.flat_algebraMap_iff.1 (hf i)
    haveI : Module.Flat A (Π₀ i, Ps i) := inferInstance
    haveI : Module.Flat A (∀ i, Ps i) :=
      Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := A) (M := Ps)).symm
    exact RingHom.flat_algebraMap_iff.2 this
  have : f = (e.symm : (∀ i, Ps i) →+* P).comp (Pi.ringHom fun i => (g i).comp f) := by
    ext a
    apply e.injective
    simp [e]
    rfl
  rw [this]
  exact hpi.comp (RingHom.Flat.of_bijective e.symm.bijective)

theorem qmap_comp {l : ℕ} {R : Type} [CommRing R] {X Y Z : Obj l R} (g : Hom Y Z) (f : Hom X Y) (m : ℕ) :
    qmap (g.comp f) m = (qmap g m).comp (qmap f m) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem adI_pow_map {l : ℕ} {R : Type} [CommRing R] {X Y : Obj l R} (f : Hom X Y)
    (hI : X.I.map f.f = Y.I) (m : ℕ) : (adI X ^ m).map f.f = adI Y ^ m := by
  rw [Ideal.map_pow, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, hI]

theorem qmap_pi_bij {l : ℕ} {R : Type} [CommRing R] {n : ℕ} {C : Fin n → Obj l R} {Q : Obj l R}
    (π : ∀ i, Hom Q (C i)) (hbij : Function.Bijective fun (x : Q.A) (i : Fin n) => (π i).f x)
    (hI : ∀ i, Q.I.map (π i).f = (C i).I) (m : ℕ) :
    Function.Bijective fun (x : Q.A ⧸ adI Q ^ m) (i : Fin n) => qmap (π i) m x :=
  quot_pi_bij (fun i => (π i).f) hbij _ _ (fun i => adI_pow_le (π i) m) fun i => adI_pow_map (π i) (hI i) m

theorem prodStable : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (n : ℕ) (C : Fin n → Obj l R),
    (∀ i, ∃ t, (C i).I = Ideal.span {t}) → ∀ (Q : Obj l R) (π : ∀ i, Hom Q (C i)),
    Function.Bijective (fun (x : Q.A) (i : Fin n) => (π i).f x) → ∀ (B : Obj l R) (h : Hom B Q),
    (∀ i, Stable ((π i).comp h)) → Stable h := by
  intro l _ R _ n C hC Q π hbij B h hs
  have hQI : ∀ i, Q.I.map (π i).f = (C i).I := fun i => GlobalTheory.T.prism_hom_map_ideal_eq l R Q (C i) (π i)
  refine ⟨fun m => ?_, fun B' k => ?_⟩
  · exact flat_of_pi (qmap h m) (fun i => qmap (π i) m) (qmap_pi_bij π hbij hQI m)
      fun i => by rw [← qmap_comp]; exact (hs i).flat m
  · choose C' k' h' hpo using fun i => (hs i).po B' k
    have hC' : ∀ i, ∃ t, (C' i).I = Ideal.span {t} := fun i => by
      obtain ⟨t, ht⟩ := hC i
      exact ⟨(k' i).f t, by rw [← GlobalTheory.T.prism_hom_map_ideal_eq l R _ _ (k' i), ht, Ideal.map_span, Set.image_singleton]⟩
    obtain ⟨Q', π', hbij', -, huniv⟩ := GlobalTheory.T.exists_finite_product_oriented_boundedPrisms l R n C' hC'
    have hQ'I : ∀ i, Q'.I.map (π' i).f = (C' i).I := fun i => GlobalTheory.T.prism_hom_map_ideal_eq l R Q' (C' i) (π' i)
    obtain ⟨K, hK⟩ := huniv Q fun i => (k' i).comp (π i)
    obtain ⟨H, hH⟩ := huniv B' h'
    have hinj : ∀ {X : Obj l R} (a b : Hom X Q'), (∀ i, (π' i).comp a = (π' i).comp b) → a = b :=
      fun a b hab => Hom.ext' (RingHom.ext fun x => hbij'.1 (funext fun i => congrArg (fun c => c.f x) (hab i)))
    refine ⟨Q', K, H, ⟨hinj _ _ fun i => ?_, fun m => ?_⟩⟩
    · calc (π' i).comp (K.comp h) = ((π' i).comp K).comp h := Hom.ext' rfl
        _ = (k' i).comp ((π i).comp h) := by rw [hK i]; exact Hom.ext' rfl
        _ = (h' i).comp k := (hpo i).comm
        _ = ((π' i).comp H).comp k := by rw [hH i]
        _ = (π' i).comp (H.comp k) := Hom.ext' rfl
    · refine GlobalTheory.T.ringHom_isPushout_of_pi_components (qmap h m) (qmap k m) (qmap K m) (qmap H m) (fun i => qmap (π i) m)
        (fun i => qmap (π' i) m) (fun i => qmap (k' i) m) (fun i => qmap (h' i) m)
        (qmap_pi_bij π hbij hQI m) (qmap_pi_bij π' hbij' hQ'I m) (fun i => ?_) (fun i => ?_) (fun i => ?_)
      · rw [← qmap_comp, ← qmap_comp, hK i]
      · rw [← qmap_comp, hH i]
      · rw [← qmap_comp]; exact (hpo i).po m

end GlobalTheory.ProdStable
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isPushout_of_bases {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (g' : S →+* S') (f' : R' →+* S') (hc : g'.comp f = f'.comp g) {ι : Type} :
    letI := f.toAlgebra; letI := f'.toAlgebra
    ∀ (b : Module.Basis ι R S) (b' : Module.Basis ι R' S'), (∀ i, g' (b i) = b' i) →
      CategoryTheory.IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom g')
        (CommRingCat.ofHom f') := by
  letI := f.toAlgebra; letI := g.toAlgebra; letI := g'.toAlgebra; letI := f'.toAlgebra
  letI : Algebra R S' := (f'.comp g).toAlgebra
  intro b b' hb
  haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hc x).symm
  have hbc : IsBaseChange R' (IsScalarTower.toAlgHom R S S').toLinearMap := by
    refine IsBaseChange.of_equiv ((Algebra.TensorProduct.basis R' b).equiv b' (Equiv.refl _)) fun m => ?_
    have : (((Algebra.TensorProduct.basis R' b).equiv b' (Equiv.refl _)).toLinearMap.restrictScalars R ∘ₗ
        TensorProduct.mk R R' S 1) = (IsScalarTower.toAlgHom R S S').toLinearMap := b.ext fun i => by
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
        IsScalarTower.coe_toAlgHom']
      rw [← Algebra.TensorProduct.basis_apply, Module.Basis.equiv_apply, Equiv.refl_apply]
      exact (hb i).symm
    exact LinearMap.congr_fun this m
  haveI : Algebra.IsPushout R R' S S' := ⟨hbc⟩
  haveI : Algebra.IsPushout R S R' S' := Algebra.IsPushout.symm inferInstance
  exact CommRingCat.isPushout_of_isPushout R S R' S'

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem exists_basis_quot_of_map_eq {S A : Type} [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (J : Ideal A)
    (hJ : I.map s = J) (hle : I ≤ J.comap s) {ι : Type} (b₀ : ι → A)
    (h : letI := (Ideal.quotientMap (I.map s) s Ideal.le_comap_map).toAlgebra
      ∃ b : Module.Basis ι (S ⧸ I) (A ⧸ I.map s), ∀ i, b i = Ideal.Quotient.mk _ (b₀ i)) :
    letI := (Ideal.quotientMap J s hle).toAlgebra
    ∃ b : Module.Basis ι (S ⧸ I) (A ⧸ J), ∀ i, b i = Ideal.Quotient.mk _ (b₀ i) := by
  subst hJ
  exact h

theorem map_adI_pow {R : Type} [CommRing R] {l : ℕ} {B B' : Obj l R} (f : Hom B B') (hI : B.I.map f.f = B'.I)
    (m : ℕ) : (adI B ^ m).map f.f = adI B' ^ m := by
  rw [Ideal.map_pow, adI, adI, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, hI]

end GlobalTheory.BSP

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem env_map_tb_b {bk : BK K} {B B' : Obj l ↥(OL K)} {t p : B.A} {k : Hom B B'} {En : Env bk B t p}
    {En' : Env bk B' (k.f t) (k.f p)} (k' : Hom En.Q En'.Q) (h1 : k'.comp En.inl = En'.inl.comp k)
    (h2 : k'.comp En.inr = En'.inr) (α : Digits l) : k'.f (En.tb.b α) = En'.tb.b α := by
  have hreg : En'.inl.f (k.f t) ∈ nonZeroDivisors En'.Q.A :=
    by
    haveI := En'.Q.inv
    exact mem_nonZeroDivisors_of_invertible_span_singleton _ _ (Module.Invertible.congr (LinearEquiv.ofEq _ _ En'.I_eq))
  have e1 : ∀ a, k'.f (En.inl.f a) = En'.inl.f (k.f a) := fun a => by
    have := congrArg (fun h => Hom.f h a) h1
    exact this
  have e2 : k'.f (BK.hf En.inr X) = BK.hf En'.inr X := by
    have := congrArg (fun h => Hom.f h X) h2
    exact this
  have hw : k'.f En.w = En'.w := by
    have a1 := congrArg k'.f En.w_eq
    have a2 := En'.w_eq
    have a3 : k'.f (En.inl.f p + En.inl.f t * En.w) = En'.inl.f (k.f p) + En'.inl.f (k.f t) * k'.f En.w := by
      simp only [map_add (f := _), map_mul, e1]
    have : En'.inl.f (k.f t) * (k'.f En.w - En'.w) = 0 := by linear_combination -a3 - a1 + e2 + a2
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hreg).2 _ (by rw [mul_comm]; exact this))
  have hδ : ∀ i : ℕ, k'.f (En.Q.D.δ^[i] En.w) = En'.Q.D.δ^[i] En'.w := fun i =>
    (Function.Semiconj.iterate_right (f := k'.f) k'.f_δ i En.w).trans (congrArg (En'.Q.D.δ^[i]) hw)
  calc k'.f (En.tb.b α) = k'.f (α.1.prod fun i n => (En.Q.D.δ^[i] En.w) ^ n) := congrArg k'.f (En.tb_b α)
    _ = α.1.prod fun i n => k'.f ((En.Q.D.δ^[i] En.w) ^ n) := map_finsuppProd k'.f _ _
    _ = α.1.prod fun i n => (En'.Q.D.δ^[i] En'.w) ^ n :=
      Finsupp.prod_congr fun i _ => (map_pow _ _ _).trans (congrArg (· ^ α.1 i) (hδ i))
    _ = En'.tb.b α := (En'.tb_b α).symm

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem env_isPO : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B B' : Obj l ↥(OL K)) (t p : B.A)
    (k : Hom B B') (En : Env bk B t p) (En' : Env bk B' (k.f t) (k.f p)),
    ∃ k' : Hom En.Q En'.Q, IsPO En.inl k k' En'.inl := by
  intro l _ K bk B B' t p k En En'
  obtain ⟨k', ⟨h1, h2⟩, -⟩ := En.univ En'.Q (En'.inl.comp k) En'.inr
  have e1 : ∀ a, k'.f (En.inl.f a) = En'.inl.f (k.f a) := fun a => by
    have := congrArg (fun h => Hom.f h a) h1
    exact this
  refine ⟨k', ⟨h1, fun m => ?_⟩⟩
  have q1 := map_adI_pow En.inl (GlobalTheory.T.prism_hom_map_ideal_eq l _ B En.Q En.inl) m
  have q2 := GlobalTheory.T.adicTopologicalBasis_basis_mod_pow B.A En.Q.A En.inl.f (adI B) (Digits l) En.tb m
  have q3 := exists_basis_quot_of_map_eq En.inl.f (adI B ^ m) (adI En.Q ^ m) q1 (adI_pow_le En.inl m) En.tb.b q2
  obtain ⟨b, hb⟩ := q3
  have r1 := map_adI_pow En'.inl (GlobalTheory.T.prism_hom_map_ideal_eq l _ B' En'.Q En'.inl) m
  have r2 := GlobalTheory.T.adicTopologicalBasis_basis_mod_pow B'.A En'.Q.A En'.inl.f (adI B') (Digits l) En'.tb m
  have r3 := exists_basis_quot_of_map_eq En'.inl.f (adI B' ^ m) (adI En'.Q ^ m) r1 (adI_pow_le En'.inl m) En'.tb.b r2
  obtain ⟨b', hb'⟩ := r3
  refine isPushout_of_bases (qmap En.inl m) (qmap k m) (qmap k' m) (qmap En'.inl m) ?_ b b' fun α => ?_
  · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    exact congrArg (Ideal.Quotient.mk (adI En'.Q ^ m)) (e1 a)
  · exact (congrArg (qmap k' m) (hb α)).trans ((qmap_mk k' m _).trans
      ((congrArg (Ideal.Quotient.mk (adI En'.Q ^ m)) (env_map_tb_b k' h1 h2 α)).trans (hb' α).symm))

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory.BKLim

theorem frame_of_links : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (P : Pre bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk P.T (F m).T (tw.Pi m) n r) → ∃ F₀ : Frame bk N d fun g => (ρ g).val, F₀.toPre = P := by
  intro l _ K bk d N ρ tw F P r hL
  obtain ⟨u, hu⟩ := P.unit
  obtain ⟨Ti, hT1, hT2⟩ : ∃ Ti : Matrix (Fin d) (Fin d) (WCb l), P.T * Ti = 1 ∧ Ti * P.T = 1 :=
    ⟨↑u⁻¹, by rw [← hu]; exact u.mul_inv, by rw [← hu]; exact u.inv_mul⟩
  have key : ∀ (g : ↥(GK K)) (i j : Fin d), ∃ a : Ainf l,
      (Ti * zW (ρ g).val * P.T.map (galW l (g : GQ l))) i j
        = inclW l (1 * a) := by
    intro g i j
    refine GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) r _ ?_
    intro n
    obtain ⟨m, hnm, R, G, hc, hd⟩ := hL n
    obtain ⟨σ, hσ⟩ : ∃ σ : WCb l →+* WCb l, ∀ x, σ x = galW l (g : GQ l) x := ⟨((galW l (g : GQ l)).toRingEquiv : WCb l →+* WCb l), fun _ => rfl⟩
    have hσf : (⇑(galW l (g : GQ l)) : WCb l → WCb l) = ⇑σ := funext fun x => (hσ x).symm
    set π := Ideal.Quotient.mk (Ideal.span {((l : WCb l) ^ n)}) with hπ
    have hq : ∀ x y : WCb l, (l : WCb l) ^ n ∣ x - y → π x = π y := fun x y h =>
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h)
    have hM : ∀ {a b : Type} (A B : Matrix a b (WCb l)),
        (∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) → A.map π = B.map π := fun A B h => by
      ext i j; exact hq _ _ (by simpa using h i j)
    have hσd : ∀ x : WCb l, (l : WCb l) ^ n ∣ x → (l : WCb l) ^ n ∣ σ x := fun x ⟨y, hy⟩ =>
      ⟨σ y, by rw [hy, map_mul, map_pow, map_natCast]⟩
    have hσz : ∀ {a b : Type} (M : Matrix a b ℤ_[l]), (zW M).map σ = zW M := fun M => by
      ext i j; simp [zW, hσ]
    have hMM : ∀ {a b b' c : Type} [Fintype b] [Fintype b'] (A : Matrix a b (WCb l)) (B : Matrix b c (WCb l))
        (C : Matrix a b' (WCb l)) (D : Matrix b' c (WCb l)),
        (∀ i j, (l : WCb l) ^ n ∣ (A * B - C * D) i j) → A.map π * B.map π = C.map π * D.map π := by
      intro a b b' c _ _ A B C D h
      rw [← Matrix.map_mul, ← Matrix.map_mul]; exact hM _ _ h
    set T' := (F m).T
    set ε' := (F m).ε g
    set Pi := tw.Pi m
    have Ga := (F m).gal g
    rw [hσf] at Ga
    rw [hσf]
    have E1 : (zW Pi).map π * T'.map π = P.T.map π * (R.map bk.evW).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul]; exact hM _ _ hc
    have E1σ : (zW Pi).map π * (T'.map σ).map π = (P.T.map σ).map π * ((R.map bk.evW).map σ).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      apply hM
      intro i j
      have h1 : zW Pi * T'.map σ - P.T.map σ * (R.map bk.evW).map σ = (zW Pi * T' - P.T * R.map bk.evW).map σ := by
        rw [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul, hσz]
      rw [h1, Matrix.map_apply]; exact hσd _ (hc i j)
    have E2 : (zW Pi).map π * (zW (tw.ρ' m g).val).map π = (zW (ρ g).val).map π * (zW Pi).map π := by
      apply hMM
      intro i j
      have h1 : zW Pi * zW (tw.ρ' m g).val - zW (ρ g).val * zW Pi = zW (Pi * (tw.ρ' m g).val - (ρ g).val * Pi) := by
        simp only [zW]; rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul]
      rw [h1]
      have h2 := map_dvd (algebraMap ℤ_[l] (WCb l)) ((pow_dvd_pow (l : ℤ_[l]) hnm).trans ((tw.onto m).equi g i j))
      simpa [zW] using h2
    have E3 : ((R.map bk.evW).map σ).map π * ((G.map bk.evW).map σ).map π
        = (((l : WCb l) ^ r) • (1 : Matrix (Fin d) (Fin d) (WCb l))).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul]
      apply hM
      intro i j
      have h1 : (((R * G).map bk.evW).map σ - ((l : WCb l) ^ r) • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j
          = σ (bk.evW ((R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)) i j)) := by
        simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, map_sub]
        split_ifs <;> simp
      rw [h1]
      exact hσd _ (by simpa using map_dvd bk.evW (hd i j))
    have He : P.T.map π * ((Ti * zW (ρ g).val * P.T.map σ).map π) = (zW (ρ g).val).map π * (P.T.map σ).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hT1, Matrix.one_mul]
    have GaP : (zW (tw.ρ' m g).val).map π * (T'.map σ).map π = T'.map π * (ε'.map (inclW l)).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, Ga]
    have C1 : P.T.map π * ((Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π)
        = P.T.map π * ((R.map bk.evW).map π * (ε'.map (inclW l)).map π) := by
      calc P.T.map π * ((Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π)
          = (P.T.map π * (Ti * zW (ρ g).val * P.T.map σ).map π) * ((R.map bk.evW).map σ).map π := (Matrix.mul_assoc _ _ _).symm
        _ = (zW (ρ g).val).map π * ((P.T.map σ).map π * ((R.map bk.evW).map σ).map π) := by rw [He, Matrix.mul_assoc]
        _ = (zW (ρ g).val).map π * ((zW Pi).map π * (T'.map σ).map π) := by rw [E1σ]
        _ = ((zW Pi).map π * (zW (tw.ρ' m g).val).map π) * (T'.map σ).map π := by rw [E2, Matrix.mul_assoc]
        _ = (zW Pi).map π * (T'.map π * (ε'.map (inclW l)).map π) := by rw [Matrix.mul_assoc, GaP]
        _ = P.T.map π * ((R.map bk.evW).map π * (ε'.map (inclW l)).map π) := by rw [← Matrix.mul_assoc, E1, Matrix.mul_assoc]
    have hTi : Ti.map π * P.T.map π = 1 := by
      rw [← Matrix.map_mul, hT2, Matrix.map_one _ (map_zero _) (map_one _)]
    have C2 : (Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π
        = (R.map bk.evW).map π * (ε'.map (inclW l)).map π := by
      calc _ = (Ti.map π * P.T.map π) *
            ((Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π) := by rw [hTi, Matrix.one_mul]
        _ = _ := by rw [Matrix.mul_assoc, C1, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
    have C3 : (Ti * zW (ρ g).val * P.T.map σ).map π * (((R.map bk.evW).map σ).map π * ((G.map bk.evW).map σ).map π)
        = (R.map bk.evW).map π * (ε'.map (inclW l)).map π * ((G.map bk.evW).map σ).map π := by
      rw [← Matrix.mul_assoc, C2]
    rw [E3] at C3
    have hR : (R.map bk.ev).map (inclW l) = R.map bk.evW := by ext; rfl
    have hG : (G.map fun x => Per.σA (g : GQ l) (bk.ev x)).map (inclW l) = (G.map bk.evW).map σ := by
      ext; simp [BK.evW, hσ, galW_inclW]
    have hY : ((R.map bk.ev * ε' * G.map fun x => Per.σA (g : GQ l) (bk.ev x)).map (inclW l)).map π
        = (R.map bk.evW).map π * (ε'.map (inclW l)).map π * ((G.map bk.evW).map σ).map π := by
      simp only [Matrix.map_mul, hR, hG]
    refine ⟨(R.map bk.ev * ε' * G.map fun x => Per.σA (g : GQ l) (bk.ev x)) i j, ?_⟩
    have C4 : (((l : WCb l) ^ r) • (Ti * zW (ρ g).val * P.T.map σ)).map π
        = ((R.map bk.ev * ε' * G.map fun x => Per.σA (g : GQ l) (bk.ev x)).map (inclW l)).map π := by
      rw [hY, ← C3, ← Matrix.map_mul, Matrix.mul_smul, mul_one]
    have C5 := congrFun (congrFun C4 i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at C5
    rw [one_mul]
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 C5)
  choose ε hε using key
  refine ⟨{ toPre := P, ε := fun g => Matrix.of (ε g), gal := fun g => ?_ }, rfl⟩
  have h1 : (Matrix.of (ε g)).map (inclW l) = Ti * zW (ρ g).val * P.T.map (galW l (g : GQ l)) := by
    ext i j; rw [Matrix.map_apply, Matrix.of_apply, hε g i j, one_mul]
  show zW (ρ g).val * P.T.map (galW l (g : GQ l)) = P.T * (Matrix.of (ε g)).map (inclW l)
  rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hT1, Matrix.one_mul]

end GlobalTheory.BKLim
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.prismPushoutModAdicPow_universal : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C B' C' : Obj l R) (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C'), IsPO h k k' h' → ∀ (Q : Obj l R) (a : Hom C Q) (b : Hom B' Q), a.comp h = b.comp k → ∃! c : Hom C' Q, c.comp k' = a ∧ c.comp h' = b := by
  first | exact @GlobalTheory.BSP.PoUniv.isPO_univ | exact GlobalTheory.BSP.PoUniv.isPO_univ | (intros; apply GlobalTheory.BSP.PoUniv.isPO_univ <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.CrisBounded

theorem dvd_of_ev_eq_zero {l : ℕ} [Fact l.Prime] {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l))
    (m : ℕ) (y : Per.BdRp l) (hy : Per.ev l m y = 0) : ainfToBdRp l d ^ m ∣ y := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have h2 := hd.trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)
  have h3 : d ∣ GlobalTheory.MemLoc.xi e := Ideal.mem_span_singleton.1 (h2 ▸ Ideal.mem_span_singleton_self _)
  have h4 := ((GlobalTheory.MemLoc.filtration_eq_xi_pow l e hE).1 m y).1 ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m y).2 hy)
  exact (pow_dvd_pow_of_dvd (map_dvd (GlobalTheory.MemLoc.aDp l) h3) m).trans h4

theorem bdd_crisP {l : ℕ} [Fact l.Prime] {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l)) (m : ℕ) :
    ∃ N : ℕ, ∀ x : Per.Acris l, ∃ a : Ainf l,
      ainfToBdRp l d ^ m ∣ (l : Per.BdRp l) ^ N * acrisToBdRp l x - ainfToBdRp l a := by
  obtain ⟨N, hN⟩ := (isCrisP_crisP l).bdd m
  refine ⟨N, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hN x
  refine ⟨a, dvd_of_ev_eq_zero hd m _ ?_⟩
  rw [map_sub, sub_eq_zero]
  exact ha.trans (GlobalTheory.MemLoc.CrisUnique.ev_aDp m a).symm

theorem bdd_tensor {Z O A C D : Type} [CommRing Z] [CommRing O] [Algebra Z O] [Module.Free Z O]
    [Module.Finite Z O] [CommRing A] [Algebra Z A] [CommRing C] [Algebra Z C] [CommRing D] [Algebra Z D]
    (f : A →ₐ[Z] D) (j : C →ₐ[Z] D) (t : D) (n : ℕ) (h : ∀ x : C, ∃ a : A, t ∣ (n : D) * j x - f a)
    (z : O ⊗[Z] C) : ∃ y : O ⊗[Z] A, ((1 : O) ⊗ₜ[Z] t) ∣
      (n : O ⊗[Z] D) * Algebra.TensorProduct.map (AlgHom.id O O) j z -
        Algebra.TensorProduct.map (AlgHom.id O O) f y := by
  let b := Module.Free.chooseBasis Z O
  choose a c hc using fun i => h (GlobalTheory.Decompl.crd b i z)
  refine ⟨∑ i, b i ⊗ₜ[Z] a i, ∑ i, b i ⊗ₜ[Z] c i, GlobalTheory.Decompl.ext_crd b fun i => ?_⟩
  rw [map_sub, GlobalTheory.Decompl.crd_natCast_mul, GlobalTheory.Decompl.crd_map, GlobalTheory.Decompl.crd_map, GlobalTheory.Decompl.crd_mul,
    GlobalTheory.Decompl.crd_sum, GlobalTheory.Decompl.crd_sum, hc]

theorem bdd_crisToOD : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ), ∃ N : ℕ, ∀ z : OCr l O, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ (l : OD l O) ^ N * crisToOD l O z - toOD l O y := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ m
  rw [show ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) from
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))]
  obtain ⟨N, hN⟩ := bdd_crisP (ϖ.span_ev_eis 1) m
  refine ⟨N, fun z => ?_⟩
  obtain ⟨y, hy⟩ := bdd_tensor (ainfToBdRp l) (acrisToBdRp l) _ (l ^ N)
    (fun x => by rw [Nat.cast_pow]; exact hN x) z
  refine ⟨y, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← Nat.cast_pow]
  exact hy

end GlobalTheory.BKReal.CrisBounded
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

theorem _root_.GlobalTheory.T.desc_eq_X_pow_smul_nabla_pow' : ∀ {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (v : Vec K a ι), C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v := by
  first | exact @GlobalTheory.DescFalling.desc_eq_X_pow_smul_nabla_pow | exact GlobalTheory.DescFalling.desc_eq_X_pow_smul_nabla_pow | (intros; apply GlobalTheory.DescFalling.desc_eq_X_pow_smul_nabla_pow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per

theorem _root_.GlobalTheory.T.breuilKisin_full_faithfulness_lattice_morphism : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T T' : Lat a O K ϖ) (I : Ident t ϖ P T) (I' : Ident t ϖ Q T'), IsBK I → IsBK I' → ∀ f : LatHom T.L T'.L, ∃ F, IsMapOf I I' f F := by
  first | exact @GlobalTheory.BKReal.Full.main | exact GlobalTheory.BKReal.Full.main | (intros; apply GlobalTheory.BKReal.Full.main <;> assumption)
end
