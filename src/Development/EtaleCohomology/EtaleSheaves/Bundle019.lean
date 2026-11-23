module

public import Development.EtaleCohomology.EtaleSheaves.Bundle010
public import Development.EtaleCohomology.TateTwists.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StdCoverPf

theorem mono_spMap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    [Mono (Spec.map (CommRingCat.ofHom φ))] : Mono (spMap φ) := by
  have h : Mono (yoneda.map (Spec.map (CommRingCat.ofHom φ))) := inferInstance
  haveI : ∀ X, Mono ((spMap φ).app X) := fun _ => h
  exact NatTrans.mono_of_mono_app _

abbrev Xs {S : Type} [CommRing S] (f g : S) (b : Bool) : Scheme.{0} :=
  Spec (CommRingCat.of (Localization.Away (bif b then f else g)))

abbrev ι {S : Type} [CommRing S] (f g : S) (b : Bool) : Xs f g b ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (bif b then f else g))))

theorem cover_mem {S : Type} [CommRing S] (f g : S) (hfg : Ideal.span {f, g} = ⊤) :
    Sieve.ofArrows (Xs f g) (ι f g) ∈ Scheme.etaleTopology.{0} (Spec (CommRingCat.of S)) := by
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale) (f := ι f g)).2 ⟨fun pt => ?_, fun b => inferInstance⟩
  let p : PrimeSpectrum S := pt
  have hp : f ∉ p.asIdeal ∨ g ∉ p.asIdeal := by
    by_contra hc
    push_neg at hc
    have : Ideal.span {f, g} ≤ p.asIdeal := by
      rw [Ideal.span_le]; intro z hz
      rcases hz with rfl | hz
      · exact hc.1
      · rw [Set.mem_singleton_iff] at hz; exact hz ▸ hc.2
    rw [hfg] at this
    exact p.isPrime.ne_top (top_le_iff.mp this)
  rcases hp with h | h
  · have hm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away f))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]; exact h
    obtain ⟨q, hq⟩ := hm
    exact ⟨true, q, hq⟩
  · have hm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]; exact h
    obtain ⟨q, hq⟩ := hm
    exact ⟨false, q, hq⟩

theorem key (R : Type) [CommRing R] (S : Type) [CommRing S] (f g : S) (hfg : Ideal.span {f, g} = ⊤) {G : Shv R}
    (u v : (free R).obj (yoneda.obj (Spec (CommRingCat.of S))) ⟶ G)
    (hb : ∀ b, (free R).map (yoneda.map (ι f g b)) ≫ u = (free R).map (yoneda.map (ι f g b)) ≫ v) : u = v := by
  let adj := sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  apply (adj.homEquiv ((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))) G).injective
  have hb' : ∀ b, (freeP R).map (yoneda.map (ι f g b)) ≫ adj.homEquiv _ G u =
      (freeP R).map (yoneda.map (ι f g b)) ≫ adj.homEquiv _ G v := by
    intro b
    have h0 : (presheafToSheaf _ _).map ((freeP R).map (yoneda.map (ι f g b))) ≫ u =
        (presheafToSheaf _ _).map ((freeP R).map (yoneda.map (ι f g b))) ≫ v := hb b
    have h1 := congrArg (adj.homEquiv _ G) h0
    erw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left] at h1
    exact h1
  generalize adj.homEquiv _ G u = u' at hb' ⊢
  generalize adj.homEquiv _ G v = v' at hb' ⊢
  ext X : 2
  apply ModuleCat.free_hom_ext
  intro x0
  have hT := Scheme.etaleTopology.pullback_stable x0.down (cover_mem f g hfg)
  have e := G.property.hom_ext ⟨_, hT⟩
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ (u'.app X (ModuleCat.freeMk x0))))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ (v'.app X (ModuleCat.freeMk x0)))) ?_
  · have := congrArg (fun e => e.hom 1) e
    simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul] at this
    exact this
  rintro ⟨W, k, hk⟩
  obtain ⟨Z, h, _, ⟨b⟩, hh⟩ := hk
  ext1
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.toSpanSingleton_apply, one_smul]
  have hm : (((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0) =
      (((freeP R).map (yoneda.map (ι f g b))).app (op W)).hom (ModuleCat.freeMk (ULift.up h)) := by
    simp only [freeP, ModuleCat.freeMk]
    erw [Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    change Finsupp.single (ULift.up (k ≫ x0.down)) _ = Finsupp.single (ULift.up (h ≫ ι f g b)) _
    rw [hh]
  change ((u'.app X ≫ (G.obj.map k.op)).hom (ModuleCat.freeMk x0)) =
    ((v'.app X ≫ (G.obj.map k.op)).hom (ModuleCat.freeMk x0))
  erw [← u'.naturality, ← v'.naturality]
  change (u'.app (op W)).hom ((((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0)) =
    (v'.app (op W)).hom ((((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0))
  rw [hm]
  change ((((freeP R).map (yoneda.map (ι f g b))) ≫ u').app (op W)).hom (ModuleCat.freeMk (ULift.up h)) =
    ((((freeP R).map (yoneda.map (ι f g b))) ≫ v').app (op W)).hom (ModuleCat.freeMk (ULift.up h))
  rw [hb' b]

theorem epi_cover (R : Type) [CommRing R] (S : Type) [CommRing S] (f g : S) (hfg : Ideal.span {f, g} = ⊤)
    (n : SimplexCategoryᵒᵖ) :
    Epi (biprod.desc ((free R).map ((spMap (algebraMap S (Localization.Away f))).app n))
      ((free R).map ((spMap (algebraMap S (Localization.Away g))).app n))) := by
  constructor
  intro G u v h
  have hf := congrArg (biprod.inl ≫ ·) h
  have hg := congrArg (biprod.inr ≫ ·) h
  simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc] at hf hg
  exact key R S f g hfg u v (fun b => by cases b; exacts [hg, hf])

end LateralTheory.E.StdCoverPf

open LateralTheory.E.StdCoverPf in
theorem LateralTheory.E.MVPf.StdCover_of : LateralTheory.E.MVPf.StdCover := by
  intro R _ S _ f g hfg
  exact ⟨mono_spMap _, mono_spMap _, epi_cover R S f g hfg⟩
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.Gluing₂

theorem orth {S : Type} [CommRing S] : ∀ (n : ℕ) (ε : Fin n → S), (∀ j, IsIdempotentElem (ε j)) →
    ∃ ε' : Fin n → S, OrthogonalIdempotents ε' ∧ (∀ j, ∃ c, ε' j = ε j * c) ∧
      ∑ j, ε' j = 1 - ∏ j, (1 - ε j) := by
  intro n
  induction n with
  | zero => intro ε _; exact ⟨fun _ => 0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, by simp⟩
  | succ n ih =>
    intro ε hε
    obtain ⟨ε₀, ho, hd, hs⟩ := ih (fun j => ε j.succ) (fun j => hε j.succ)
    have ha : IsIdempotentElem (ε 0) := hε 0
    have ha' : IsIdempotentElem (1 - ε 0) := ha.one_sub
    refine ⟨Fin.cons (ε 0) (fun j => (1 - ε 0) * ε₀ j), ⟨?_, ?_⟩, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · simp only [Fin.cons_succ]
        exact ha'.mul (ho.idem j)
    · intro i k hik
      induction i using Fin.cases with
      | zero =>
        induction k using Fin.cases with
        | zero => exact absurd rfl hik
        | succ k =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← mul_assoc, mul_sub, mul_one, ha.eq, sub_self, zero_mul]
      | succ i =>
        induction k using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [mul_comm, ← mul_assoc, mul_sub, mul_one, ha.eq, sub_self, zero_mul]
        | succ k =>
          simp only [Fin.cons_succ]
          have hik' : i ≠ k := fun h => hik (by rw [h])
          calc (1 - ε 0) * ε₀ i * ((1 - ε 0) * ε₀ k) = ((1 - ε 0) * (1 - ε 0)) * (ε₀ i * ε₀ k) := by ring
            _ = 0 := by rw [ho.ortho hik', mul_zero]
    · intro i
      refine Fin.cases ⟨1, by simp⟩ (fun j => ?_) i
      obtain ⟨c, hc⟩ := hd j
      exact ⟨(1 - ε 0) * c, by simp only [Fin.cons_succ, hc]; ring⟩
    · rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← Finset.mul_sum, hs]
      ring

theorem glue : LateralTheory.E.FinEtSectionPf.Glue := by
  intro S C _ _ _ n e he hsurj ε hε hr hh
  obtain ⟨ε', ho, hd, hs⟩ := orth n ε hε

  have hf0 : ∏ j, (1 - ε j) = 0 := by
    have hidem : IsIdempotentElem (∏ j, (1 - ε j)) := by
      have := ho.isIdempotentElem_sum (s := Finset.univ).one_sub
      rwa [hs, sub_sub_cancel] at this
    refine hidem.eq_zero_of_isNilpotent ((nilpotent_iff_mem_prime).2 fun J hJ => ?_)
    obtain ⟨q, hq⟩ := hsurj ⟨J, hJ⟩
    have : ∃ j, e j ∉ q.asIdeal := by
      by_contra hall
      push_neg at hall
      exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (he.complete ▸ Ideal.sum_mem _ fun j _ => hall j))
    obtain ⟨j, hj⟩ := this
    have hq' : q ∈ Set.range (PrimeSpectrum.comap (algebraMap C (Localization.Away (e j)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (e j)) (e j)]; exact hj
    obtain ⟨q', rfl⟩ := hq'
    have hmem : (⟨J, hJ⟩ : PrimeSpectrum S) ∈ (PrimeSpectrum.basicOpen (ε j) : Set (PrimeSpectrum S)) := by
      rw [← hr j]; exact ⟨q', by rw [PrimeSpectrum.comap_comp_apply, hq]⟩
    have hεj : ε j ∉ J := hmem
    have h1 : 1 - ε j ∈ J := by
      have : ε j * (1 - ε j) ∈ J := by rw [mul_sub, mul_one, (hε j).eq, sub_self]; exact J.zero_mem
      exact (hJ.mem_or_mem this).resolve_left hεj
    exact J.mem_of_dvd (Finset.dvd_prod_of_mem (fun i => 1 - ε i) (Finset.mem_univ j)) h1
  have hco : CompleteOrthogonalIdempotents ε' := ⟨ho, by rw [hs, hf0, sub_zero]⟩
  choose h hh using hh
  choose c hc using hd
  have hunit : ∀ j, IsUnit (Ideal.Quotient.mk (Ideal.span {1 - ε' j}) (ε j)) := by
    intro j
    refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ (c j), ?_⟩
    rw [← (Ideal.Quotient.mk (Ideal.span {1 - ε' j})).map_mul, ← hc j, ← (Ideal.Quotient.mk (Ideal.span {1 - ε' j})).map_one, Ideal.Quotient.eq]
    have hm := (Ideal.span {1 - ε' j}).neg_mem (Ideal.mem_span_singleton_self (1 - ε' j))
    rwa [neg_sub] at hm
  let L : ∀ j, Localization.Away (ε j) →+* S ⧸ Ideal.span {1 - ε' j} :=
    fun j => IsLocalization.Away.lift (ε j) (hunit j)
  let Φ : C →+* (∀ j, S ⧸ Ideal.span {1 - ε' j}) :=
    RingHom.pi fun j => ((L j).comp (h j)).comp (algebraMap C (Localization.Away (e j)))
  let E := RingEquiv.ofBijective _ hco.bijective_pi
  have hΦ : ∀ s : S, Φ (algebraMap S C s) = E s := by
    intro s
    funext j
    have := congrArg (fun g => L j (g s)) (hh j)
    simp only [RingHom.comp_apply] at this
    show L j (h j (algebraMap C _ (algebraMap S C s))) = Ideal.Quotient.mk _ s
    rw [this]
    exact IsLocalization.Away.lift_eq (ε j) (hunit j) s
  refine ⟨{ E.symm.toRingHom.comp Φ with commutes' := fun s => ?_ }⟩
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, hΦ]
  simp

theorem Glue_of (_hL : LateralTheory.E.t_E1Cut.EtLift) (_hA : LateralTheory.E.t_E1Cut.EtAIC) : LateralTheory.E.FinEtSectionPf.Glue := glue

end LateralTheory.E.Gluing₂
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.DomOpenPf

theorem algClosed_of_AIC (T : Type) [CommRing T] [IsDomain T] (hT : AIC T) :
    IsAlgClosed (FractionRing T) := by
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  set K := FractionRing T
  set f := algebraMap T K
  have hf : Function.Injective f := IsFractionRing.injective T K
  obtain ⟨b, hb₁, hb₂⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors T) p
  set q := IsLocalization.integerNormalization (nonZeroDivisors T) p
  have hb0 : (b : T) ≠ 0 := nonZeroDivisors.ne_zero hb₁
  have hdeg : q.natDegree = p.natDegree := by
    rw [← natDegree_map_eq_of_injective hf q, hb₂, ← IsScalarTower.algebraMap_smul K b p,
      natDegree_smul_of_smul_regular]
    exact IsSMulRegular.of_ne_zero (by simpa [f] using (map_ne_zero_iff f hf).mpr hb0)
  have hpos : 0 < p.natDegree := Irreducible.natDegree_pos hirr
  have hq0 : q ≠ 0 := by intro h; rw [h] at hdeg; simp at hdeg; omega
  obtain ⟨a, ha⟩ := hT (integralNormalization q) (monic_integralNormalization hq0)
    (by rw [natDegree_integralNormalization]; omega)
  have hlc : f q.leadingCoeff ≠ 0 := (map_ne_zero_iff f hf).mpr (leadingCoeff_ne_zero.mpr hq0)
  refine ⟨f a / f q.leadingCoeff, ?_⟩
  have key := integralNormalization_eval₂_leadingCoeff_mul (p := q) (by omega) f (f a / f q.leadingCoeff)
  rw [mul_div_cancel₀ _ hlc, eval₂_at_apply, ha, map_zero] at key
  have h2 : q.eval₂ f (f a / f q.leadingCoeff) = 0 := by
    rcases mul_eq_zero.mp key.symm with h | h
    · exact absurd (pow_eq_zero_iff'.mp h).1 hlc
    · exact h
  rw [eval₂_eq_eval_map, hb₂, ← IsScalarTower.algebraMap_smul K b p, eval_smul, smul_eq_mul] at h2
  exact (mul_eq_zero.mp h2).resolve_left ((map_ne_zero_iff f hf).mpr hb0)

theorem algebraMap_ne_zero_of_flat (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [Nontrivial D]
    [Algebra T D] [Module.Flat T D] {s : T} (hs : s ≠ 0) : algebraMap T D s ≠ 0 := by
  intro h
  have hr : IsSMulRegular D s := Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs)
  apply one_ne_zero (α := D)
  apply hr
  simp [Algebra.smul_def, h]

theorem exists_frac (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [IsDomain D] [Algebra T D]
    [Algebra.Etale T D] (hT : AIC T) (a : D) :
    ∃ s t : T, s ≠ 0 ∧ algebraMap T D s * a = algebraMap T D t := by
  classical
  haveI := algClosed_of_AIC T hT
  let M := nonZeroDivisors T
  let S := Localization (Algebra.algebraMapSubmonoid D M)
  have hle : Algebra.algebraMapSubmonoid D M ≤ nonZeroDivisors D := by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (algebraMap_ne_zero_of_flat T D (nonZeroDivisors.ne_zero hs))
  have : IsDomain S := IsLocalization.isDomain_localization hle
  have : IsLocalization (M.map (algebraMap T D)) S := inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid D M) S)
  have : Algebra.FormallyEtale (FractionRing T) S :=
    Algebra.FormallyEtale.localization_map M (Rₘ := FractionRing T) (Sₘ := S) (S := D)
  have : Algebra.EssFiniteType (FractionRing T) S := Algebra.EssFiniteType.of_comp T (FractionRing T) S
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed (FractionRing T) S
  have hsub : Subsingleton (PrimeSpectrum S) := by
    constructor
    intro p q
    by_contra hpq
    have h0 : ((fun r => if r = p then (1 : FractionRing T) else 0) * fun r => if r = q then 1 else 0) = 0 := by
      funext r; simp only [Pi.mul_apply, Pi.zero_apply]; split_ifs with h1 h2 <;> simp_all
    have : e.symm (fun r => if r = p then (1 : FractionRing T) else 0) * e.symm (fun r => if r = q then 1 else 0) = 0 := by rw [← map_mul, h0, map_zero]
    rcases mul_eq_zero.mp this with h | h
    · have := congrFun (e.symm.injective (h.trans (map_zero _).symm)) p
      simp at this
    · have := congrFun (e.symm.injective (h.trans (map_zero _).symm)) q
      simp at this
  obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum S) := inferInstance
  set x := algebraMap D S a
  have hx : algebraMap (FractionRing T) S (e x p₀) = x := by
    apply e.injective
    funext p
    rw [AlgEquiv.commutes]
    simp [Subsingleton.elim p p₀]
  generalize e x p₀ = c at hx
  obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.mk'_surjective M c
  change IsLocalization.mk' (FractionRing T) t s = c at hts
  refine ⟨s, t, nonZeroDivisors.ne_zero s.2, ?_⟩
  apply IsLocalization.injective S hle
  rw [map_mul, ← IsScalarTower.algebraMap_apply T D S, ← IsScalarTower.algebraMap_apply T D S,
    show algebraMap D S a = x from rfl, ← hx, ← hts,
    IsScalarTower.algebraMap_apply T (FractionRing T) S (s : T), IsScalarTower.algebraMap_apply T (FractionRing T) S t,
    ← map_mul, mul_comm, IsLocalization.mk'_spec]

theorem isEpi (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [IsDomain D] [Algebra T D]
    [Algebra.Etale T D] (hT : AIC T) : Algebra.IsEpi T D := by
  rw [Algebra.isEpi_iff_forall_one_tmul_eq]
  intro a
  obtain ⟨s, t, hs, hst⟩ := exists_frac T D hT a
  have hr : IsSMulRegular (TensorProduct T D D) s :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs)
  rw [← sub_eq_zero]
  apply hr
  change s • (1 ⊗ₜ[T] a - a ⊗ₜ[T] 1) = s • (0 : TensorProduct T D D)
  have hsa : s • a = t • (1 : D) := by rw [Algebra.smul_def, hst, Algebra.smul_def, mul_one]
  have e1 : s • ((1 : D) ⊗ₜ[T] a) = t • ((1 : D) ⊗ₜ[T] (1 : D)) := by
    rw [← TensorProduct.tmul_smul, hsa, TensorProduct.tmul_smul]
  have e2 : s • (a ⊗ₜ[T] (1 : D)) = t • ((1 : D) ⊗ₜ[T] (1 : D)) := by
    rw [TensorProduct.smul_tmul', hsa, ← TensorProduct.smul_tmul']
  rw [smul_zero, smul_sub, e1, e2, sub_self]

theorem DomOpen_of : LateralTheory.E.EtAICPf.DomOpen := by
  intro T D _ _ _ _ _ _ hT
  set f := CommRingCat.ofHom (algebraMap T D)
  have : Algebra.IsEpi T D := isEpi T D hT
  have : Epi f := CommRingCat.epi_iff_epi.mpr inferInstance
  have : Mono (Spec.map f) := inferInstanceAs (Mono (Scheme.Spec.map f.op))
  have : Flat (Spec.map f) := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : LocallyOfFinitePresentation (Spec.map f) :=
    (LocallyOfFinitePresentation.SpecMap_iff f).mpr (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  exact IsOpenImmersion.of_flat_of_mono _

end LateralTheory.E.DomOpenPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.MVSpcPf

def Ses : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∃ w,
  (ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)))
    (biprod.desc ((chains R).map f) ((chains R).map g)) w).ShortExact

variable {R : Type} [CommRing R] {I : Cx R}

abbrev pc {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cochain L I m) : Cochain K I m := (Cochain.ofHom φ).comp z (zero_add m)

theorem pc_comp {K L M : Cx R} (φ : K ⟶ L) (ψ : L ⟶ M) {m : ℤ} (z : Cochain M I m) : pc (φ ≫ ψ) z = pc φ (pc ψ z) := by
  simp [pc, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem pc_addm {K L : Cx R} (φ ψ : K ⟶ L) {m : ℤ} (z : Cochain L I m) : pc (φ + ψ) z = pc φ z + pc ψ z := by
  simp [pc, Cochain.ofHom_add, Cochain.add_comp]

theorem pc_negm {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cochain L I m) : pc (-φ) z = -pc φ z := by
  simp [pc, Cochain.ofHom_neg, Cochain.neg_comp]

theorem pc_zerom {K L : Cx R} {m : ℤ} (z : Cochain L I m) : pc (0 : K ⟶ L) z = 0 := by
  simp [pc, Cochain.ofHom_zero, Cochain.zero_comp]

theorem pc_add {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z z' : Cochain L I m) : pc φ (z + z') = pc φ z + pc φ z' := by
  simp [pc, Cochain.comp_add]

theorem pc_sub {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z z' : Cochain L I m) : pc φ (z - z') = pc φ z - pc φ z' := by
  simp [pc, Cochain.comp_sub]

theorem pc_δ {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cochain L I m) (m' : ℤ) : δ m m' (pc φ z) = pc φ (δ m m' z) :=
  δ_ofHom_comp φ z m'

theorem cpre_mk' {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cocycle L I m) :
    cpre (Cocycle.ofHom φ) I m m (zero_add m) (CohomologyClass.mk z) =
      CohomologyClass.mk (Cocycle.mk (pc φ z.1) (m + 1) rfl (by rw [pc_δ, Cocycle.δ_eq_zero, pc, Cochain.comp_zero])) := by
  rw [cpre_mk]; congr 1

theorem cocy_δ {K : Cx R} {m : ℤ} (z : Cocycle K I m) (m' : ℤ) : δ m m' z.1 = 0 := by
  by_cases h : m + 1 = m'
  · exact (Cocycle.mem_iff m m' h z.1).1 z.2
  · exact δ_shape _ _ h _

theorem chase (hI : ∀ n, Injective (I.X n)) {K1 KA KB K3 : Cx R} (φ : K1 ⟶ KA) (ψ : K1 ⟶ KB) (u : KA ⟶ K3)
    (v : KB ⟶ K3) (w) (hS : (ShortComplex.mk (biprod.lift φ (-ψ)) (biprod.desc u v) w).ShortExact) (n : ℤ)
    (hc : ∀ c : CohomologyClass K1 I n, ∃ a b, c = cpre (Cocycle.ofHom φ) I n n (zero_add n) a -
      cpre (Cocycle.ofHom ψ) I n n (zero_add n) b)
    (x : CohomologyClass K3 I (n + 1)) (hu : cpre (Cocycle.ofHom u) I _ _ (zero_add _) x = 0)
    (hv : cpre (Cocycle.ofHom v) I _ _ (zero_add _) x = 0) : x = 0 := by
  have hC := fun m => LateralTheory.EtaleFoundations.etale_simplicial_cochain_short_exact_sequence_holds R I hI _ hS m
  obtain ⟨z, rfl⟩ := x.mk_surjective
  rw [cpre_mk', CohomologyClass.mk_eq_zero_iff] at hu hv
  obtain ⟨m, hm, aU, haU⟩ := hu
  obtain ⟨m', hm', aV, haV⟩ := hv
  have e1 : n = m := by omega
  subst e1
  have e2 : n = m' := by omega
  subst e2
  simp only [Cocycle.mk_coe] at haU haV
  set b : Cochain (KA ⊞ KB) I n := pc biprod.fst aU + pc biprod.snd aV with hbdef
  have hb : δ n (n + 1) b = pc (biprod.desc u v) z.1 := by
    rw [hbdef, δ_add, pc_δ, pc_δ, haU, haV, ← pc_comp, ← pc_comp, ← pc_addm, ← biprod.desc_eq]
  have hαb : δ n (n + 1) (pc (biprod.lift φ (-ψ)) b) = 0 := by
    rw [pc_δ, hb, ← pc_comp, w, pc_zerom]
  obtain ⟨a, b0, hab⟩ := hc (CohomologyClass.mk (Cocycle.mk (pc (biprod.lift φ (-ψ)) b) (n + 1) rfl hαb))
  obtain ⟨a, rfl⟩ := a.mk_surjective
  obtain ⟨b0, rfl⟩ := b0.mk_surjective
  rw [cpre_mk', cpre_mk', ← CohomologyClass.mk_sub, ← sub_eq_zero, ← CohomologyClass.mk_sub,
    CohomologyClass.mk_eq_zero_iff] at hab
  obtain ⟨k, hk, e, he⟩ := hab
  obtain ⟨e2, he2⟩ := (hC k).1 e
  set b2 : Cochain (KA ⊞ KB) I n := pc biprod.fst a.1 + pc biprod.snd b0.1 with hb2def
  have hαb2 : pc (biprod.lift φ (-ψ)) b2 = pc φ a.1 - pc ψ b0.1 := by
    rw [hb2def, pc_add, ← pc_comp, ← pc_comp, biprod.lift_fst, biprod.lift_snd, pc_negm, sub_eq_add_neg]
  have hδb2 : δ n (n + 1) b2 = 0 := by
    rw [hb2def, δ_add, pc_δ, pc_δ, cocy_δ, cocy_δ, pc, pc, Cochain.comp_zero, Cochain.comp_zero, add_zero]
  have hr : pc (biprod.lift φ (-ψ)) (b - b2 - δ k n e2) = 0 := by
    have he2' : pc (biprod.lift φ (-ψ)) e2 = e := he2
    rw [pc_sub, pc_sub, ← pc_δ, he2', he]
    change _ - _ - (pc (biprod.lift φ (-ψ)) b - (pc φ a.1 - pc ψ b0.1)) = 0
    rw [hαb2]; abel
  obtain ⟨c3, hc3⟩ := (hC n).2.1 _ hr
  have hc3' : pc (biprod.desc u v) c3 = _ := hc3
  have hz : pc (biprod.desc u v) (δ n (n + 1) c3 - z.1) = 0 := by
    rw [pc_sub, ← pc_δ]
    change δ n (n + 1) (pc (biprod.desc u v) c3) - _ = 0
    rw [hc3', δ_sub, δ_sub, δ_δ, hδb2, hb]; simp
  have := (hC (n + 1)).2.2 _ hz
  exact (CohomologyClass.mk_eq_zero_iff _).2 ⟨n, rfl, c3, sub_eq_zero.1 this⟩

end LateralTheory.E.MVSpcPf

open LateralTheory.E.MVSpcPf in
theorem LateralTheory.E.MVPf.MVSpc_of (hS : Ses) : LateralTheory.E.MVPf.MVSpc := by
  intro _ R _ F U V E f g hc n hd x hxf hxg
  obtain ⟨w, hw⟩ := hS R f g hc
  have hI : ∀ k, Injective ((res R F).X k) := fun k => by unfold res; infer_instance
  exact chase hI _ _ _ _ w hw n hd x hxf hxg
end
end
