module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelBaseChangeUniv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle126
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle058
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct

private theorem sec_eq_of_points {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (n : ℕ) (hn : IsUnit (n : Γ(X, ⊤))) (σ σ' : 𝟙_ (Over X) ⟶ A) (h₁ : σ ^ n = 1) (h₂ : σ' ^ n = 1)
    (hpt : ∀ q : X, ∃ (k : Type) (_ : Field k) (y : Sp k ⟶ X), q ∈ Set.range y ∧
      toUnit (Over.mk y) ≫ σ = toUnit (Over.mk y) ≫ σ') : σ = σ' := by
  have key : ∀ q : X, ∃ V : X.Opens, q ∈ V ∧ V.ι ≫ σ.left = V.ι ≫ σ'.left := by
    intro q
    obtain ⟨k, hk, y, ⟨z, hz⟩, he⟩ := hpt q
    obtain ⟨V, hV, hVe⟩ := GlobalTheory.UPel.LocSim.exists_open_eq_of_torsion_point X A hA n hn σ σ' h₁ h₂ k y he
    exact ⟨V, hV ⟨z, hz⟩, hVe⟩
  choose V hV hVe using key
  have hcov : TopologicalSpace.IsOpenCover V := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun q _ => ?_)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨q, hV q⟩
  apply Over.OverMorphism.ext
  exact Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover V hcov) _ _ fun q => hVe q

private theorem map_nsmul_pow {M Q : Type} [AddCommGroup M] [Group Q] (f : M → Q) (hf : ∀ a b, f (a + b) = f a * f b)
    (m : ℕ) (a : M) : f (m • a) = f a ^ m := by
  induction m with
  | zero =>
    rw [zero_nsmul, pow_zero]
    have h := hf 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := f 0) (by rw [_root_.mul_one]; exact h.symm)
  | succ m ih =>
    rw [succ_nsmul, hf, ih, pow_succ]

private theorem pow_comp_hom {C : Type*} [Category C] [CartesianMonoidalCategory C] {T A B : C} [GrpObj A] [GrpObj B]
    (a : T ⟶ A) (ψ : A ⟶ B) [IsMonHom ψ] (m : ℕ) : (a ≫ ψ) ^ m = (a ^ m) ≫ ψ := (map_pow (IsMonHom.monoidHom ψ T) a m).symm

private theorem ev_tower {G : GDatum} {k Q : Type} [Field k] [Group Q] {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : GTateIso G k Q act e) {M n c : ℕ} (hM : M = n * c) (hn : 0 < n) (hc : 0 < c) (z : G.La) :
    I.ev M (c • z) = I.ev n z := by
  subst hM
  rw [map_nsmul_pow (I.ev _) (I.add _)]
  exact I.tower n c hn hc z

theorem UpperTheory.trace_eta_identity : UpperTheory.Gal.Int.Geo.TrEta := by
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT n c' c hN' hN x y hxy
  haveI : IsMonHom ψ := hT.1
  have h3' := N'.2.1
  have h3 := N.2.1
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hN'; omega)
  have hc' : 0 < c' := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hN'; omega)
  have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hN; omega)
  have hcop : n.Coprime p := Nat.Coprime.coprime_dvd_left ⟨c', hN'⟩ N'.2.2
  have hunit : IsUnit (n : Γ(X, ⊤)) := by
    have hR : IsUnit (n : R) := by
      have hq : IsUnit (n : ℚ) := (Nat.cast_ne_zero.mpr hn.ne').isUnit
      simpa using hq.map (algebraMap ℚ R)
    have := hR.map ((s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using this
  have ex' : (n • c' • x : D.La) = (↑N' : ℕ) • x := by rw [smul_smul, ← hN']
  have ex : (n • c • y : D.La) = (↑N : ℕ) • y := by rw [smul_smul, ← hN]
  have e1 : (o'.eta (c' • x)) ^ n = 1 :=
    (map_nsmul_pow o'.eta o'.eta_add n (c' • x)).symm.trans ((congrArg o'.eta ex').trans (o'.eta_ker x))
  have hpow1 : (o'.eta (c' • x) ≫ ψ) ^ n = 1 :=
    (pow_comp_hom _ _ _).trans ((congrArg (· ≫ ψ) e1).trans (map_one (IsMonHom.monoidHom ψ _)))
  have hpow2 : (o.eta (c • y)) ^ n = 1 :=
    (map_nsmul_pow o.eta o.eta_add n (c • y)).symm.trans ((congrArg o.eta ex).trans (o.eta_ker y))
  refine sec_eq_of_points o.A o.ab n hunit _ _ hpow1 hpow2 (fun q => ?_)
  let κ := X.residueField q
  let k := AlgebraicClosure κ
  let y0 : Sp k ⟶ X := spMap (algebraMap κ k) ≫ X.fromSpecResidueField q
  let β : R →+* k := (Spec.preimage (y0 ≫ s)).hom
  have hβ : y0 ≫ s = spMap β := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (y0 ≫ s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨I', I'', hI', hI'', hiff⟩ := hT.2.2.2.2 k y0 β hβ
  refine ⟨k, inferInstance, y0, ⟨IsLocalRing.closedPoint k, Scheme.fromSpecResidueField_apply q _⟩, ?_⟩
  calc toUnit (Over.mk y0) ≫ (o'.eta (c' • x) ≫ ψ)
      = (toUnit (Over.mk y0) ≫ o'.eta (c' • x)) ≫ ψ := (Category.assoc _ _ _).symm
    _ = I'.ev (↑N') (c' • x) ≫ ψ := congrArg (· ≫ ψ) (hI' _)
    _ = I'.ev n x ≫ ψ := congrArg (· ≫ ψ) (ev_tower I' hN' hn hc' x)
    _ = I''.ev n y := (hiff n hn hcop x y).mpr hxy
    _ = I''.ev (↑N) (c • y) := (ev_tower I'' hN hn hc y).symm
    _ = toUnit (Over.mk y0) ≫ o.eta (c • y) := (hI'' _).symm
end
end

section

open UpperTheory.Gal.Int.Geo

theorem UpperTheory.group_scheme_pullback_exists :
    GPull := by
  intro G R _ _ gb N X X' s e o
  exact GlobalTheory.UPel.HT.Gen.BaseChange.exists_gObjMap_pull e o
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.site_exists_of_splitting_and_power_projector :
    MIn → SplitQ → BaseEx → PowProj → SiteEx := by
  intro hM hS hB hP
  intro p _ D G hSc E _ _ e gb hstd w q _ r 𝔴 𝔫 hpl hat hlev
  have sp := hS p D hSc.m1 q
  obtain ⟨N₀, 𝔞, h3, hcq, hcp, hsup, hupow, hlv⟩ := hlev
  obtain ⟨f, b, hmat, hstdb, hqmem, hnorm⟩ :=
    hB q (datAt hat sp) hSc.a1 hSc.m1 E e gb hstd w 𝔴 r hpl hat.le N₀ h3 hcq
  obtain ⟨M⟩ := hM.ex q (datAt hat sp) (Ow w) b N₀ h3 hcq
  have hEt : UpperTheory.Gal.FiniteEtaleModels.IsEtIdeal b 𝔞 :=
    (hM.placeOf q (datAt hat sp) (Ow w) b r 𝔴 hat.max hstdb.pmem hSc.a1 hstdb.ule hstdb.tw 𝔞 hsup).2 hupow
  obtain ⟨Y, π, ρ, hov, ⟨hmπ⟩, hgal⟩ := hM.finModel q (datAt hat sp) (Ow w) b N₀ h3 hcq 𝔞 1 hEt M
  have hfin : IsFinite π := hgal.fin
  have het : Etale π := hgal.etale
  have hMproj : IsProjOver M.s := hM.proj q (datAt hat sp) (Ow w) b N₀ h3 hcq hSc.cpt M
  have hYproj : IsProjOver Y.s := by
    rw [← hov]
    exact GlobalTheory.T.isProjOver_comp_finite (Ow w) M.X Y.X π M.s hfin hMproj
  have hYsm : SmoothOfRelativeDimension (0 + (datAt hat sp).a * ((datAt hat sp).n - 1)) Y.s := by
    rw [← hov]
    haveI : SmoothOfRelativeDimension 0 π := by
      rw [← AlgebraicGeometry.Etale.eq_smoothOfRelativeDimension_zero]
      exact het
    haveI := M.smooth
    infer_instance
  have hPw := fun k => hP q (datAt hat sp) (Ow w) b N₀ h3 hcq Y.X Y.s Y.univ k
  exact ⟨⟨hat, sp, f, b, hmat, N₀, 𝔞, hstdb, hqmem, hnorm, hcp, hsup, hupow, hlv, M, Y, π, hov, hmπ,
    hfin, het, fun k => (hPw k).1 hYproj, fun k => (hPw k).2 _ hYsm⟩⟩
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem UpperTheory.integralGeometricGalois_splitting : UpperTheory.Gal.Int.Geo.SplitOf := by
  intro W X c _ _ Δ _ a ha h
  refine UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts c c Δ a ha ?_
  intro Ω _ _ x y hy
  obtain ⟨δ, hδ, hu⟩ := h Ω x y hy.symm
  exact ⟨δ, hδ.symm, fun δ' hδ' => hu δ' hδ'.symm⟩
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace UpperTheory

private theorem card_quot_of {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (I : Ideal A) (h : ∀ a, a ∈ I ↔ f a = 0) :
    Nat.card (A ⧸ I) = Nat.card B := by
  have hk : I = RingHom.ker f := by
    ext a
    rw [RingHom.mem_ker]
    exact h a
  exact Nat.card_congr ((Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective hf)).toEquiv

section Local

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

private def iota : 𝓞 E →+* Gal.Int.Geo.Ow w :=
  (algebraMap (𝓞 E) E).codRestrict (w.valuation E).valuationSubring
    (fun a => by
      rw [Valuation.mem_valuationSubring_iff]
      exact w.valuation_le_one a)

private theorem iota_mem_max (a : 𝓞 E) :
    iota w a ∈ IsLocalRing.maximalIdeal (Gal.Int.Geo.Ow w) ↔ a ∈ w.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.valuationSubring.integers (w.valuation E)).isUnit_iff_valuation_eq_one,
    ← w.valuation_lt_one_iff_mem (K := E) a]
  exact ⟨fun h => lt_of_le_of_ne (w.valuation_le_one a) h, ne_of_lt⟩

private theorem res_surj :
    Function.Surjective ((IsLocalRing.residue (Gal.Int.Geo.Ow w)).comp (iota w)) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hx : (x : E) ∈ w.valuationSubringAtPrime E := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact x.2
  haveI : IsLocalization w.asIdeal.primeCompl (w.valuationSubringAtPrime E) :=
    Localization.subalgebra.isLocalization_ofField E w.asIdeal.primeCompl
      w.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj w.asIdeal.primeCompl
    (⟨x, hx⟩ : w.valuationSubringAtPrime E)
  have hxs : x * iota w (s : 𝓞 E) = iota w a :=
    Subtype.ext (congrArg (fun z : w.valuationSubringAtPrime E => (z : E)) h)
  obtain ⟨c, i, hi, hc⟩ := w.isMaximal.exists_inv s.2
  refine ⟨a * c, ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hc' : iota w c * iota w (s : 𝓞 E) + iota w i = 1 := by
    rw [← map_mul, ← map_add (f := _), hc, map_one]
  have e1 : iota w (a * c) - x = -(x * iota w i) := by
    rw [map_mul, ← hxs]
    linear_combination x * hc'
  rw [e1]
  exact neg_mem (Ideal.mul_mem_left _ _ ((iota_mem_max w i).2 hi))

private theorem card_res :
    Nat.card (IsLocalRing.ResidueField (Gal.Int.Geo.Ow w)) = Nat.card (𝓞 E ⧸ w.asIdeal) :=
  (card_quot_of _ (res_surj w) w.asIdeal (fun a => by
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, iota_mem_max])).symm

private theorem card_pow (q : ℕ) (hq : q.Prime) (h : (q : 𝓞 E) ∈ w.asIdeal) :
    ∃ f : ℕ, Nat.card (𝓞 E ⧸ w.asIdeal) = q ^ f :=
  by apply _root_.UpperTheory.Reformulated.B.Qi54.card_pow <;> assumption

end Local

theorem baseExtension_holds : Gal.Int.Geo.BaseEx := by
  intro q _ D ha hm E _ _ e gb hstd w 𝔴 r hpl hu N₀ h3 hcop
  haveI : Subsingleton (Fin D.a) := by
    rw [ha]
    infer_instance
  have hq : q.Prime := Fact.out
  let j : 𝓞 D.F ≃+* 𝓞 E := NumberField.RingOfIntegers.mapRingEquiv e
  have hj : ∀ c : 𝓞 D.F, ((j c : 𝓞 E) : E) = e (c : D.F) := fun c => rfl
  have hpl' : ∀ c : 𝓞 D.F, c ∈ 𝔴 ↔ j c ∈ w.asIdeal := fun c => hpl c (j c) (hj c)
  have hqm : (q : 𝓞 E) ∈ w.asIdeal := by
    have h := (hpl' (q : 𝓞 D.F)).1 (hu (ES.p_mem_uIdeal D r))
    rwa [map_natCast] at h
  obtain ⟨f, hf⟩ := card_pow w q hq hqm
  have hnw : Ideal.absNorm w.asIdeal = q ^ f := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hf]
  have hroot : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    linear_combination D.ω * D.tr_eq - D.nm_eq
  let t : 𝓞 D.F →+* Gal.Int.Geo.Ow w := (iota w).comp j.toRingHom
  have hunit : ∀ k : ℕ, k.Coprime q → IsUnit (k : Gal.Int.Geo.Ow w) := by
    intro k hk
    have hkw : (k : 𝓞 E) ∉ w.asIdeal := by
      intro hmem
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hk
      have h1 : (u : 𝓞 E) * (k : 𝓞 E) + (v : 𝓞 E) * (q : 𝓞 E) = 1 := by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huv
      refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      rw [← h1]
      exact add_mem (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hqm)
    by_contra hn
    refine hkw ((iota_mem_max w _).1 ?_)
    rw [map_natCast]
    exact (IsLocalRing.mem_maximalIdeal _).2 hn
  let b : Base D (Gal.Int.Geo.Ow w) :=
    { unit := hunit
      ρ := t D.ω
      ρ_root := by
        have h := congrArg t hroot
        simpa only [map_add (f := _), map_sub, map_mul, map_pow, map_intCast, map_zero] using h
      t := fun _ => t
      t_ω := fun _ => rfl
      comax := fun i j h => absurd (Subsingleton.elim i j) h
      apart := fun i j h => absurd (Subsingleton.elim i j) h }
  refine ⟨f, b, ⟨?_, ?_⟩, ?_, hqm, hnw⟩
  · exact hstd.1
  · exact fun i => RingHom.ext fun c => hstd.2 i c
  · have hsurj : Function.Surjective ((Ideal.Quotient.mk w.asIdeal).comp j.toRingHom) :=
      Ideal.Quotient.mk_surjective.comp j.surjective
    refine
      { pmem := ?_
        card := by rw [card_res, hf]
        three := h3
        cop := hcop
        m1 := hm
        a1 := ha
        ule := hu
        norm := ?_
        tw := fun i x hx => (iota_mem_max w _).2 ((hpl' x).1 hx) }
    · rw [← map_natCast (iota w)]
      exact (iota_mem_max w _).2 hqm
    · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
        card_quot_of _ hsurj 𝔴 (fun a => by
          rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
          exact hpl' a), hf]

end UpperTheory
end
end
