module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle094
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle069
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CxPairing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
public import Mathlib.Algebra.Exact.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle095
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle097
public import Mathlib.RingTheory.Artinian.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle096
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk

@[expose] public section

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.cm_conjugation_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x, σ (σ x) = x) ∧ (∀ x, σ x = x → ∃ y : F, algebraMap F E y = x) ∧ (∀ (o : 𝓞 E), ((sO σ o : 𝓞 E) : E) = σ (o : E)) ∧ (∀ I : Ideal (𝓞 E), Ideal.absNorm (I.map (sO σ)) = Ideal.absNorm I) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isCMExt_conj_fixed_integers | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isCMExt_conj_fixed_integers | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isCMExt_conj_fixed_integers <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.EtaleSections

theorem exists_algHom_away_of_etale {S : Type} [CommRing S]
    (hA : Aic (S := S)) (hL : Loc (S := S))
    (B : Type) [CommRing B] [Algebra S B] [Algebra.Etale S B] (Q : Ideal B) [hQ : Q.IsPrime]
    (hm : (Q.comap (algebraMap S B)).IsMaximal) :
    ∃ e : S, IsIdempotentElem e ∧ e ∉ Q.comap (algebraMap S B) ∧
      Nonempty (B →ₐ[S] Localization.Away e) := by
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := S) Q
  let Bg := Localization.Away g
  have hdisj : Disjoint (Submonoid.powers g : Set B) (Q : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hg (hQ.mem_of_pow_mem n hn)
  have hQ' : (Q.map (algebraMap B Bg)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Bg Q hQ hdisj
  have hcomap : (Q.map (algebraMap B Bg)).comap (algebraMap B Bg) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Bg hQ hdisj
  have hc : (Q.map (algebraMap B Bg)).comap (algebraMap S Bg) = Q.comap (algebraMap S B) := by
    rw [IsScalarTower.algebraMap_eq S B Bg, ← Ideal.comap_comap, hcomap]
  let q := Q.map (algebraMap B Bg)
  have hqm : (q.comap (algebraMap S Bg)).IsMaximal := hc ▸ hm
  have hsection : ∃ e : S, IsIdempotentElem e ∧ e ∉ q.comap (algebraMap S Bg) ∧
      Nonempty (Bg →ₐ[S] Localization.Away e) := by
    obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := S) (S := Bg)
    obtain ⟨s, hs⟩ := GlobalTheory.T.absolutely_closed_polynomial_splits hA P.f P.monic_f

    have hprod : (s.map fun b => P.x - algebraMap S Bg b).prod ∈ q := by
      have h0 : Polynomial.aeval P.x P.f = 0 := P.hasMap.1
      rw [hs, map_multiset_prod, Multiset.map_map] at h0
      have : (s.map fun b => P.x - algebraMap S Bg b).prod = 0 := by
        rw [← h0]
        congr 1
        apply Multiset.map_congr rfl
        intro b _
        simp
      rw [this]
      exact q.zero_mem
    obtain ⟨b, hbs, hbQ⟩ :=
      GlobalTheory.CompanionTheory.EtaleSection.exists_sub_mem_of_prod_mem q hQ' P.x s hprod
    have hroot : Polynomial.eval b P.f = 0 := by
      have hd : (Polynomial.X - Polynomial.C b) ∣ P.f := by
        rw [hs]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hbs)
      exact Polynomial.dvd_iff_isRoot.1 hd

    set c : S := Polynomial.eval b P.g with hc
    have hcm : c ∉ q.comap (algebraMap S Bg) := by
      intro hcQ
      have hcQ' : algebraMap S Bg c ∈ q := hcQ
      have hd : P.x - algebraMap S Bg b ∣
          Polynomial.aeval P.x P.g - algebraMap S Bg c := by
        have := Polynomial.sub_dvd_eval_sub P.x (algebraMap S Bg b) (P.g.map (algebraMap S Bg))
        rwa [Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap,
          Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at this
      have hgQ : Polynomial.aeval P.x P.g ∈ q := by
        have h1 := Ideal.mem_of_dvd q hd hbQ
        simpa using q.add_mem h1 hcQ'
      exact hQ'.ne_top (Ideal.eq_top_of_isUnit_mem q hgQ P.hasMap.2)

    obtain ⟨a, μ, hμ, haμ⟩ := hqm.exists_inv hcm
    obtain ⟨e, he, hec, he1⟩ := hL (a * c)
    have h1ac : 1 - a * c = μ := by rw [← haμ]; ring
    have he1m : 1 - e ∈ q.comap (algebraMap S Bg) := by
      rw [h1ac] at he1
      exact (Ideal.span_singleton_le_iff_mem _).2 hμ he1
    have hem : e ∉ q.comap (algebraMap S Bg) := by
      intro hem
      have : (1 : S) ∈ q.comap (algebraMap S Bg) := by
        simpa using Ideal.add_mem _ hem he1m
      exact hqm.ne_top ((Ideal.eq_top_iff_one _).2 this)
    refine ⟨e, he, hem, ?_⟩

    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hec
    have heu : IsUnit (algebraMap S (Localization.Away e) e) :=
      IsLocalization.Away.algebraMap_isUnit e
    have hcu : IsUnit (algebraMap S (Localization.Away e) c) := by
      have : algebraMap S (Localization.Away e) e =
          algebraMap S (Localization.Away e) (r * a) * algebraMap S (Localization.Away e) c := by
        rw [← map_mul, ← hr]; ring_nf
      rw [this] at heu
      exact isUnit_of_mul_isUnit_right heu
    have hmap : P.P.HasMap (algebraMap S (Localization.Away e) b) := by
      refine ⟨?_, ?_⟩
      · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hroot, map_zero]
      · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
        exact hcu
    exact ⟨(P.P.lift _ hmap).comp P.equivRing.toAlgHom⟩
  obtain ⟨e, he, hem, ⟨ψ⟩⟩ := hsection
  exact ⟨e, he, hc ▸ hem, ⟨ψ.comp (IsScalarTower.toAlgHom S B Bg)⟩⟩

theorem exists_secOn_of_etale_surjective : ∀ {S : Type} [CommRing S],
    Aic (S := S) → Loc (S := S) →
    ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), Etale f → Surjective f →
    ∀ m : Ideal S, m.IsMaximal → ∃ e : S, IsIdempotentElem e ∧ e ∉ m ∧ SecOn f e := by
  intro S _ hA hL Y f hE hS m hm
  let x : Spec (CommRingCat.of S) := ⟨m, hm.isPrime⟩
  obtain ⟨y, hy⟩ := hS.surj x
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV.fromSpec ≫ f)
  have hEt : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hφe : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hEt
  let _ : Algebra S Γ(Y, V) := φ.hom.toAlgebra
  have : Algebra.Etale S Γ(Y, V) := RingHom.etale_algebraMap.1 hφe
  have hyr : y ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hyV
  obtain ⟨z, hz⟩ := hyr
  have hcm : z.asIdeal.comap (algebraMap S Γ(Y, V)) = m := by
    have h1 : (Spec.map φ) z = x := by
      rw [hφ, Scheme.Hom.comp_apply, hz, hy]
    exact congrArg PrimeSpectrum.asIdeal h1
  have : z.asIdeal.IsPrime := z.2
  obtain ⟨e, he, hem, ⟨ψ⟩⟩ := exists_algHom_away_of_etale hA hL Γ(Y, V) z.asIdeal (by rw [hcm]; exact hm)
  refine ⟨e, he, hcm ▸ hem, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  congr 1
  ext a
  exact ψ.commutes a

end GlobalTheory.CompanionTheory.EtaleSections
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.Cech

theorem elMor_bijective_of_bijective {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R) (h : ∀ T, Function.Bijective (p.app T)) (n : ℕ) : Function.Bijective ((elMor p F).hom.f n) := by
  haveI : ∀ T, IsIso (p.app T) := fun T => (isIso_iff_bijective _).2 (h T)
  haveI : IsIso p := NatIso.isIso_of_isIso_app p
  have e1 : ∀ x, (elMor (inv p) F).pullC n ((elMor p F).pullC n x) = x := fun x => by
    have e : (inv p ≫ p : E ⟶ E) = 𝟙 E := IsIso.inv_hom_id p
    exact congrArg (fun a => (elMor a F).pullC n x) e
  have e2 : ∀ x, (elMor p F).pullC n ((elMor (inv p) F).pullC n x) = x := fun x => by
    have e : (p ≫ inv p : E' ⟶ E') = 𝟙 E' := IsIso.hom_inv_id p
    exact congrArg (fun a => (elMor a F).pullC n x) e
  exact Function.bijective_iff_has_inverse.2 ⟨(elMor (inv p) F).pullC n, e1, e2⟩

end GlobalTheory.CompanionTheory.Cech
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

theorem _root_.GlobalTheory.T.total_complex_flip_isomorphism : ∀ {R : Type} [CommRing R] (K : DCx.{w} R), ∃ φ : Cx.Hom K.tot K.flip.tot (RingHom.id R), (∀ n, Function.Bijective (φ.f n)) ∧ ∀ n (x : K.tot.X n) p q, (φ.f n x).1 q p = (-1 : ℤ) ^ (p * q) • x.1 p q := by
  first | exact @GlobalTheory.CompanionTheory.DCFlip.flip_tot | exact GlobalTheory.CompanionTheory.DCFlip.flip_tot | (intros; apply GlobalTheory.CompanionTheory.DCFlip.flip_tot <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

theorem _root_.GlobalTheory.T.natTrans_upTo_sq_pullback : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F F' : C ⥤ ModuleCat.{w} R} (α : F ⟶ F') (s : R), (∀ T, UpTo s (α.app T).hom) → ∀ n, UpTo (s ^ 2) ((Mor.ofNatTrans α).pull n) := by
  first | exact @GlobalTheory.CompanionTheory.CoefUpTo.coef_upTo | exact GlobalTheory.CompanionTheory.CoefUpTo.coef_upTo | (intros; apply GlobalTheory.CompanionTheory.CoefUpTo.coef_upTo <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.inverse_limit_cohomology_comparison : ∀ {R : Type} [CommRing R] {K : Cx.{1} R} (Kn : ℕ → Cx.{1} R) (c : R) (red : ∀ n, Cx.Hom K (Kn n) (RingHom.id R))
    (tr : ∀ n, Cx.Hom (Kn (n + 1)) (Kn n) (RingHom.id R)), (∀ n j x, (tr n).f j ((red (n + 1)).f j x) = (red n).f j x) →
    (∀ n j, Function.Surjective ((red n).f j)) → (∀ n j x, (red n).f j x = 0 ↔ ∃ y, x = c ^ n • y) → (∀ j (x : K.X j), c • x = 0 → x = 0) →
    ∀ j k : ℕ, (∀ (x : K.H (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) → (∀ x : K.H j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0) →
    (∀ x : ℕ → K.H j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : K.H j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) →
    (∀ x : ∀ n, (Kn n).H j, (∀ n, (tr n).mapH j (x (n + 1)) = x n) → ∃ z : K.H j, ∀ n, (red n).mapH j z = c ^ (2 * k) • x n) ∧
    ∀ z : K.H j, (∀ n, (red n).mapH j z = 0) → c ^ k • z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LimLift.lim_lift | exact GlobalTheory.CompanionTheory.LimLift.lim_lift | (intros; apply GlobalTheory.CompanionTheory.LimLift.lim_lift <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cohomology_vanishing_short_exact : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (α : F₁ ⟶ F₂)
    (β : F₂ ⟶ F₃), (∀ T, Function.Injective (α.app T).hom) → (∀ T, Function.Exact (α.app T).hom (β.app T).hom) →
    (∀ T, Function.Surjective (β.app T).hom) → (∀ n, Subsingleton (CH.H F₂ n)) → (∀ n, Subsingleton (CH.H F₃ n)) →
    ∀ n, Subsingleton (CH.H F₁ n) := by
  first | exact @GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses | exact GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses | (intros; apply GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.CechVB

theorem vb_basis : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (str : ∀ V : X.Opens, O →+* Γ(X, V)) {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} O) {ι : Type}
    (U : ι → X.Opens) (U' : ι → ObjectProperty C) (m : ℕ) (κ : ι → Type) [∀ α, Fintype (κ α)]
    (act : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Γ(X, capO U i) →+* AddMonoid.End (HU F (capT U' i) m))
    (b : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (a : Fin (n + 1)), κ (i a) → HU F (capT U' i) m)
    (g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β))
    (hfree : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a : Fin (n + 1)) (h : HU F (capT U' i) m),
      ∃! f : κ (i a) → Γ(X, capO U i), h = ∑ k, act i (f k) (b i a k))
    (hstr : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (c : O) (h : HU F (capT U' i) m), act i (str _ c) h = c • h)
    (hres : ∀ (n : ℕ) (i : Fin (n + 2) → ι) (j : Fin (n + 2)) (f : Γ(X, capO U (i ∘ j.succAbove))) (h : HU F (capT U' (i ∘ j.succAbove)) m),
      (resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (act (i ∘ j.succAbove) f h) =
        act i (rs (capO_comp U i j.succAbove) f) ((resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m h))
    (hb : ∀ (n : ℕ) (i : Fin (n + 2) → ι) (j : Fin (n + 2)) (a : Fin (n + 1)) (k : κ (i (j.succAbove a))),
      (resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (b (i ∘ j.succAbove) a k) = b i (j.succAbove a) k)
    (hg : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a a' : Fin (n + 1)) (k' : κ (i a')),
      b i a' k' = ∑ k, act i (rs (le_inf (capO_le U i a) (capO_le U i a')) (g (i a) (i a') k k')) (b i a k)),
    Nonempty (VB str U (CrystallineSemistableComparison.Pb.cechH F U' m)) := by
  intro O _ X str C _ F ι U U' m κ _ act b g hfree hstr hres hb hg
  simp only [ExistsUnique] at hfree
  choose co h1 h2 using hfree
  have actadd : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (f f' : Γ(X, capO U i)) (h : HU F (capT U' i) m),
      act i (f + f') h = act i f h + act i f' h := by
    intro n i f f' h
    rw [map_add (f := _)]; rfl
  have actmul : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (f f' : Γ(X, capO U i)) (h : HU F (capT U' i) m),
      act i (f * f') h = act i f (act i f' h) := by
    intro n i f f' h
    rw [map_mul]; rfl
  have actsum : ∀ {n : ℕ} (i : Fin (n + 1) → ι) {κ' : Type} (s : Finset κ') (f : κ' → Γ(X, capO U i))
      (h : HU F (capT U' i) m), act i (∑ k ∈ s, f k) h = ∑ k ∈ s, act i (f k) h := by
    intro n i κ' s f h
    exact map_sum ((AddMonoidHom.eval h).comp (act i).toAddMonoidHom) f s
  have coadd : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a : Fin (n + 1)) (h h' : HU F (capT U' i) m),
      co n i a (h + h') = co n i a h + co n i a h' := by
    intro n i a h h'
    refine (h2 n i a _ _ ?_).symm
    conv_lhs => rw [h1 n i a h, h1 n i a h']
    simp only [Pi.add_apply, actadd, Finset.sum_add_distrib]
  refine ⟨{ κ := κ, g := g, e := fun n a =>
              { toFun := fun x i => co n i a (x i)
                invFun := fun f i => ∑ k, act i (f i k) (b i a k)
                left_inv := fun x => funext fun i => (h1 n i a (x i)).symm
                right_inv := fun f => funext fun i => (h2 n i a _ (f i) rfl).symm
                map_add' := fun x y => funext fun i => coadd n i a (x i) (y i) }
            e_smul := ?_, e_δ := ?_, e_chg := ?_ }⟩
  · intro n a c x i k
    have key : co n i a (c • x i) = fun k => str _ c * co n i a (x i) k := by
      refine (h2 n i a _ _ ?_).symm
      rw [← hstr n i c (x i)]
      conv_lhs => rw [h1 n i a (x i)]

      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => (actmul i _ _ _).symm
    exact congrFun key k
  · intro n a b' x i k
    have key : co (n + 1) i (b'.succAbove a) ((resU F (U := capT U' (i ∘ b'.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (x (i ∘ b'.succAbove))) =
        fun k => rs (capO_comp U i b'.succAbove) (co n (i ∘ b'.succAbove) a (x (i ∘ b'.succAbove)) k) := by
      refine (h2 (n + 1) i (b'.succAbove a) _ _ ?_).symm
      conv_lhs => rw [h1 n (i ∘ b'.succAbove) a (x (i ∘ b'.succAbove))]

      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hres, hb]
    exact congrFun key k
  · intro n a b' x i k
    have key : co n i a (x i) = fun k => ∑ k' : κ (i b'), rs (le_inf (capO_le U i a) (capO_le U i b')) (g (i a) (i b') k k') * co n i b' (x i) k' := by
      refine (h2 n i a _ _ ?_).symm
      have e1 : ∀ k', act i (co n i b' (x i) k') (b i b' k') =
          ∑ k, act i (rs (le_inf (capO_le U i a) (capO_le U i b')) (g (i a) (i b') k k') * co n i b' (x i) k') (b i a k) := by
        intro k'
        conv_lhs => rw [hg n i a b' k']

        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← actmul, mul_comm]
      conv_lhs => rw [h1 n i b' (x i)]
      rw [Finset.sum_congr rfl fun k' _ => e1 k', Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => (actsum i _ _ _).symm
    exact congrFun key k

end GlobalTheory.CompanionTheory.CechVB
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeRs

theorem rs_appLE_apply {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) {V W : X.Opens} (h : V ≤ W) (hW : W ≤ f ⁻¹ᵁ U)
    (s : Γ(Y, U)) : rs h ((f.appLE U W hW).hom s) = (f.appLE U V (h.trans hW)).hom s := by
  change ((f.appLE U W hW) ≫ X.presheaf.map (homOfLE h).op).hom s = _
  rw [Scheme.Hom.appLE_map]

end GlobalTheory.CompanionTheory.ConeRs
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.SerreFin

theorem finite_mid {R : Type} [CommRing R] [IsNoetherianRing R] {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (h : Function.Exact f g)
    [Module.Finite R M₁] [Module.Finite R M₃] : Module.Finite R M₂ := by
  have hk : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.1 h
  haveI : Module.Finite R (LinearMap.ker g) := by
    rw [hk]
    exact Module.Finite.range f
  haveI : IsNoetherian R M₃ := isNoetherian_of_isNoetherianRing_of_finite R M₃
  haveI : Module.Finite R (M₂ ⧸ LinearMap.ker g) := Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

theorem exists_serre_finite : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∃ 𝒮 : Serre.{1} R,
    ∀ (M : Type 1) [AddCommGroup M] [Module R M], 𝒮.P M ↔ Module.Finite R M := by
  intro R _ _
  refine ⟨⟨fun M _ _ => Module.Finite R M, fun M _ _ _ => ?_, ?_⟩, fun M _ _ => Iff.rfl⟩
  · exact Module.Finite.of_surjective (0 : (Fin 0 → R) →ₗ[R] M)
      (fun x => ⟨0, Subsingleton.elim _ _⟩)
  · intro M₁ M₂ M₃ _ _ _ _ _ _ f g h h₁ h₃
    exact finite_mid f g h

end GlobalTheory.CompanionTheory.SerreFin
end

section

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls

theorem _root_.GlobalTheory.T.lseq_of_level_isos : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' T T' : Sys.{1} W) (e : Sys.Hom S T (RingHom.id W)) (e' : Sys.Hom S' T' (RingHom.id W)), (∀ n, Function.Bijective (e.f n)) → (∀ n, Function.Bijective (e'.f n)) → LSeq l S S' → Nonempty (LSeq l T T') := by
  first | exact @GlobalTheory.CompanionTheory.TowerSeq.lseq_transport | exact GlobalTheory.CompanionTheory.TowerSeq.lseq_transport | (intros; apply GlobalTheory.CompanionTheory.TowerSeq.lseq_transport <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.Tower

theorem rho_lim {W : Type} [CommRing W] {l : ℕ} {S S' : Sys.{1} W} (L : LSeq l S S') (x : S.lim)
    (b c : ℕ) (h : b ≤ c) : L.ρ c b (x.1 c) = x.1 b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact L.ρ_self b _
  | succ d ih =>
    have h' := L.ρ_succ (b + d) b (Nat.le_add_right _ _) (x.1 (b + d + 1))
    rw [x.2 (b + d), ih (Nat.le_add_right _ _)] at h'
    exact h'

theorem lim_eq_pow_smul : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'),
    (∀ n, IsArtinian W (S.M n)) → ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y := by
  intro W _ l S S' L hA n x hx
  have hex : ∀ a, ∃ y, L.ν a (n + a) y = x.1 (n + a) := fun a =>
    L.ex₁ a n (n + a) (Nat.add_comm _ _) _ (by rw [rho_lim L x n (n + a) (Nat.le_add_right _ _), hx])
  choose y hy using hex
  have hN : ∀ a w, w ∈ LinearMap.ker (L.ν (a + 1) (n + (a + 1))) →
      S.r a w ∈ LinearMap.ker (L.ν a (n + a)) := by
    intro a w hw
    have hw' : L.ν (a + 1) (n + a + 1) w = 0 := hw
    rw [LinearMap.mem_ker, ← L.ν_r a (n + a) (Nat.le_add_left _ _), hw', map_zero]
  have hc : ∀ a, S.r a (y (a + 1)) - y a ∈ LinearMap.ker (L.ν a (n + a)) := by
    intro a
    have h1 : L.ν (a + 1) (n + a + 1) (y (a + 1)) = x.1 (n + a + 1) := hy (a + 1)
    rw [LinearMap.mem_ker, map_sub, ← L.ν_r a (n + a) (Nat.le_add_left _ _), h1, x.2 (n + a), hy a,
      sub_self]
  obtain ⟨z, hz⟩ := GlobalTheory.T.artinian_limit_lift_of_compatible W S hA (fun a => LinearMap.ker (L.ν a (n + a))) y hN hc
  have key : ∀ a, ((l : W) ^ n) • z.1 (n + a) = x.1 (n + a) := by
    intro a
    have h1 := L.ν_ρ a (n + a) (Nat.le_add_left _ _) (z.1 (n + a))
    have h2 : L.ν a (n + a) (z.1 a) = x.1 (n + a) := by
      have h3 : L.ν a (n + a) (z.1 a - y a) = 0 := hz a
      rw [map_sub, hy a, sub_eq_zero] at h3
      exact h3
    rw [rho_lim L z a (n + a) (Nat.le_add_left _ _), h2, Nat.add_sub_cancel] at h1
    exact h1.symm
  refine ⟨z, Subtype.ext (funext fun c => ?_)⟩
  calc x.1 c = L.ρ (n + c) c (x.1 (n + c)) := (rho_lim L x c (n + c) (Nat.le_add_left _ _)).symm
    _ = L.ρ (n + c) c (((l : W) ^ n) • z.1 (n + c)) := by rw [key]
    _ = ((l : W) ^ n) • L.ρ (n + c) c (z.1 (n + c)) := map_smul _ _ _
    _ = ((l : W) ^ n) • z.1 c := by rw [rho_lim L z c (n + c) (Nat.le_add_left _ _)]

end GlobalTheory.CompanionTheory.Tower
end
