module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.SetTheory.ZFC.PSet
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartB
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle004
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom

@[expose] public section

section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

variable {n : ℕ}

def ptIdeal (p : Fin n → ℂ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  RingHom.ker (MvPolynomial.eval p : MvPolynomial (Fin n) ℂ →+* ℂ)

instance ptIdeal_isPrime (p : Fin n → ℂ) : (ptIdeal p).IsPrime :=
  RingHom.ker_isPrime _

abbrev locPt (p : Fin n → ℂ) : Type :=
  Localization.AtPrime (ptIdeal p)

abbrev locRing (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) : Type :=
  locPt p ⧸ Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K

def grad (p : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) : Fin n → ℂ :=
  fun j => eval p (pderiv j h)

def jacSpan (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (grad p '' (K : Set (MvPolynomial (Fin n) ℂ)))

theorem locRing_isLocalRing_isNoetherian (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) : IsLocalRing (locRing K p) ∧ IsNoetherianRing (locRing K p) := by
  have hK : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K ≤
      IsLocalRing.maximalIdeal (locPt p) := by
    rw [Ideal.map_le_iff_le_comap]
    intro h hh
    have h2 : h ∈ ptIdeal p := (RingHom.mem_ker).2 (hp h hh)
    rw [← Localization.AtPrime.under_maximalIdeal (I := ptIdeal p)] at h2
    exact h2
  have hne : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hK
  haveI : Nontrivial (locRing K p) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsNoetherianRing (locPt p) :=
    IsLocalization.isNoetherianRing (ptIdeal p).primeCompl _ inferInstance
  exact ⟨IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective,
    inferInstance⟩

theorem finrank_cotangentSpace_locRing (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    [IsLocalRing (locRing K p)] :
    Module.finrank (IsLocalRing.ResidueField (locRing K p)) (IsLocalRing.CotangentSpace (locRing K p))
      + Module.finrank ℂ (jacSpan K p) = n := by
  exact @JacobianCriterionAlt.finrank_cot_eq n p K (inferInstanceAs (IsLocalRing (locRing K p)))

theorem exists_jacobian_cut (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (e : ℕ)
    [IsRegularLocalRing (locRing K p)] (he : ringKrullDim (locRing K p) = e) :
    e ≤ n ∧ ∃ F : Fin (n - e) → MvPolynomial (Fin n) ℂ, (∀ i, F i ∈ K) ∧
      LinearIndependent ℂ (fun i => grad p (F i)) ∧
      ∃ h : MvPolynomial (Fin n) ℂ, eval p h ≠ 0 ∧ ∀ g ∈ K, h * g ∈ Ideal.span (Set.range F) := by
  exact @JacobianCriterionAlt.exists_jacobian_cut' n K p e
    (inferInstanceAs (IsRegularLocalRing (locRing K p))) he

end

end ReciprocityTheory.AnForm.R
end

section

namespace ReciprocityTheory.AnForm.R.WMult

open AlgebraicGeometry CategoryTheory IsLocalRing

variable {W : Scheme.{0}}

theorem stalkId_eq_map_germ (I : W.IdealSheafData) (y : W) (U : W.affineOpens) (hy : y ∈ U.1) :
    FinalTheorems.stalkId I y = Ideal.map (W.presheaf.germ U.1 y hy).hom (I.ideal U) := by
  have key : ∀ (V V' : W.affineOpens) (h : V' ≤ V) (hyV' : y ∈ V'.1),
      Ideal.map (W.presheaf.germ V.1 y ((show V'.1 ≤ V.1 from h) hyV')).hom (I.ideal V) =
        Ideal.map (W.presheaf.germ V'.1 y hyV').hom (I.ideal V') := by
    intro V V' h hyV'
    rw [← I.map_ideal h, Ideal.map_map]
    congr 1
    rw [← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom (W.presheaf.germ_res (homOfLE (show V'.1 ≤ V.1 from h)) y hyV').symm
  rw [FinalTheorems.stalkId]
  apply le_antisymm
  · refine iSup₂_le fun V hyV => ?_
    obtain ⟨f, g, hfg, hyf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 y ⟨hy, hyV⟩
    have hWU : W.affineBasicOpen f ≤ U := W.basicOpen_le f
    have hWV : W.affineBasicOpen f ≤ V := by
      show W.basicOpen f ≤ V.1
      rw [hfg]
      exact W.basicOpen_le g
    rw [key V _ hWV hyf, key U _ hWU hyf]
  · exact le_iSup₂ (f := fun (V : W.affineOpens) (hV : y ∈ V.1) =>
      Ideal.map (W.presheaf.germ V.1 y hV).hom (I.ideal V)) U hy

theorem mem_support_fromSpec_iff (I : W.IdealSheafData) (U : W.affineOpens) (hU : IsAffineOpen U.1)
    (P : PrimeSpectrum Γ(W, U.1)) :
    hU.fromSpec P ∈ (I.support : Set W) ↔ I.ideal U ≤ P.asIdeal := by
  have hmem : hU.fromSpec P ∈ U.1 := by
    have hr : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rw [hU.range_fromSpec] at hr
    exact hr
  show hU.fromSpec P ∈ I.support ↔ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hmem]
  exact (Set.ext_iff.1 (hU.fromSpec_preimage_zeroLocus (I.ideal U : Set Γ(W, U.1))) P).trans
    ((PrimeSpectrum.mem_zeroLocus _ _).trans SetLike.coe_subset_coe)

private theorem ring_ord_ringEquiv_apply {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (z : A) : Ring.ord B (e z) = Ring.ord A z := by
  have hI : Ideal.comap e (Ideal.span {e z}) = Ideal.span {z} := by
    rw [show Ideal.span {e z} = Ideal.map e (Ideal.span {z}) by rw [Ideal.map_span, Set.image_singleton]]
    exact Ideal.comap_map_of_bijective e e.bijective
  unfold Ring.ord
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  refine Order.krullDim_eq_of_orderIso ?_
  let o3 := Ideal.relIsoOfBijective (e : A →+* B) e.bijective
  have h3 : o3 (Ideal.span {e z}) = Ideal.span {z} := hI
  exact (Submodule.comapMkQRelIso _).trans (((o3.Ici _).trans
    (OrderIso.setCongr _ _ (by rw [h3]))).trans (Submodule.comapMkQRelIso _).symm)

theorem ord_isLocalization_eq_exponent {R : Type*} [CommRing R] [IsRegularLocalRing R] {n : ℕ}
    (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) (u : Rˣ) (m : Fin n → ℕ) (i : Fin n) (hi : i ∈ J)
    [(Ideal.span {f i}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S (Ideal.span {f i})] :
    Ring.ord S (algebraMap R S (u * ∏ j ∈ J, f j ^ m j)) = (m i : ℕ∞) := by
  have hL := ord_localization_eq_exponent f hspan hdim J u m i hi
  let e : Localization.AtPrime (Ideal.span {f i}) ≃ₐ[R] S :=
    IsLocalization.algEquiv (Ideal.span {f i}).primeCompl (Localization.AtPrime (Ideal.span {f i})) S
  rw [← e.commutes, ← hL]
  exact ring_ord_ringEquiv_apply e.toRingEquiv _

end ReciprocityTheory.AnForm.R.WMult
end

section

namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

section Top

variable {α : Type*} [TopologicalSpace α]

def compsH (T : Set α) : Set (Set α) :=
  {C | Maximal (fun C => IsIrreducible C ∧ C ⊆ T) C}

theorem compsH_pre_isPreirreducible {T C : Set α} (hCT : C ⊆ T) (hC : IsPreirreducible C) :
    IsPreirreducible ((Subtype.val ⁻¹' C : Set T)) := by
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hC ⊢
  intro z₁ z₂ h₁ h₂ hsub
  obtain ⟨Z₁, hZ₁, rfl⟩ := isClosed_induced_iff.mp h₁
  obtain ⟨Z₂, hZ₂, rfl⟩ := isClosed_induced_iff.mp h₂
  have hC' : C ⊆ Z₁ ∪ Z₂ := fun c hc => hsub (show (⟨c, hCT hc⟩ : T) ∈ Subtype.val ⁻¹' C from hc)
  rcases hC Z₁ Z₂ hZ₁ hZ₂ hC' with h | h
  · exact Or.inl (fun x hx => h hx)
  · exact Or.inr (fun x hx => h hx)

theorem compsH_pre_isIrreducible {T C : Set α} (hCT : C ⊆ T) (hC : IsIrreducible C) :
    IsIrreducible ((Subtype.val ⁻¹' C : Set T)) := by
  obtain ⟨c, hc⟩ := hC.nonempty
  exact ⟨⟨⟨c, hCT hc⟩, hc⟩, compsH_pre_isPreirreducible hCT hC.isPreirreducible⟩

theorem image_mem_compsH {T : Set α} {A : Set T} (hA : A ∈ irreducibleComponents T) :
    Subtype.val '' A ∈ compsH T := by
  refine ⟨⟨hA.1.image _ continuous_subtype_val.continuousOn, by rintro _ ⟨x, _, rfl⟩; exact x.2⟩, ?_⟩
  intro C' hC' hle
  have h1 : A ⊆ Subtype.val ⁻¹' C' := fun x hx => hle ⟨x, hx, rfl⟩
  have h2 := hA.2 (compsH_pre_isIrreducible hC'.2 hC'.1) h1
  intro c hc
  exact ⟨⟨c, hC'.2 hc⟩, h2 hc, rfl⟩

theorem pre_mem_irreducibleComponents {T C : Set α} (hC : C ∈ compsH T) :
    (Subtype.val ⁻¹' C : Set T) ∈ irreducibleComponents T := by
  refine ⟨compsH_pre_isIrreducible hC.1.2 hC.1.1, ?_⟩
  intro B hB hle
  have h1 : C ⊆ Subtype.val '' B := fun c hc => ⟨⟨c, hC.1.2 hc⟩, hle hc, rfl⟩
  have h2 := hC.2 ⟨hB.image _ continuous_subtype_val.continuousOn, by rintro _ ⟨x, _, rfl⟩; exact x.2⟩ h1
  intro x hx
  exact h2 ⟨x, hx, rfl⟩

theorem compsH_finite [NoetherianSpace α] (T : Set α) : (compsH T).Finite := by
  have hfin : (irreducibleComponents T).Finite := NoetherianSpace.finite_irreducibleComponents
  refine (hfin.image (Set.image Subtype.val)).subset fun C hC =>
    ⟨Subtype.val ⁻¹' C, pre_mem_irreducibleComponents hC, ?_⟩
  exact Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hC.1.2)

theorem isClosed_of_mem_compsH {T : Set α} (hT : IsClosed T) {C : Set α} (hC : C ∈ compsH T) :
    IsClosed C := by
  have h2 : closure C ⊆ C := hC.2 ⟨hC.1.1.closure, closure_minimal hC.1.2 hT⟩ subset_closure
  exact closure_subset_iff_isClosed.mp h2

theorem sUnion_compsH (T : Set α) : ⋃₀ compsH T = T := by
  apply Set.Subset.antisymm
  · rintro x ⟨C, hC, hx⟩
    exact hC.1.2 hx
  · intro x hx
    exact ⟨Subtype.val '' irreducibleComponent (⟨x, hx⟩ : T),
      image_mem_compsH (irreducibleComponent_mem_irreducibleComponents _),
      ⟨⟨x, hx⟩, mem_irreducibleComponent, rfl⟩⟩

end Top

section Alg

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S] {p : Ideal A} [p.IsPrime]
  [IsLocalization.AtPrime S p] [IsRegularLocalRing S] {n : ℕ} {f : Fin n → A}

def parPrime (f : Fin n → A) (i : Fin n) : Ideal A :=
  (Ideal.span {algebraMap A S (f i)}).comap (algebraMap A S)

variable (S) in
theorem parPrime_spec (hrsp : FinalTheorems.Rsp S n (fun i => algebraMap A S (f i))) (i : Fin n) :
    (parPrime (S := S) f i).IsPrime ∧ parPrime (S := S) f i ≤ p ∧ f i ∈ parPrime (S := S) f i := by
  have hp := prime_of_regular_params _ hrsp.1 hrsp.2 i
  have hP : (Ideal.span {algebraMap A S (f i)}).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  refine ⟨Ideal.comap_isPrime _ _, ?_, Ideal.mem_comap.mpr (Ideal.subset_span rfl)⟩
  intro a ha
  have hle : Ideal.span {algebraMap A S (f i)} ≤ maximalIdeal S := by
    rw [Ideal.span_le, Set.singleton_subset_iff, ← hrsp.1]
    exact Ideal.subset_span ⟨i, rfl⟩
  have := hle (Ideal.mem_comap.mp ha)
  have h2 : (maximalIdeal S).comap (algebraMap A S) = p :=
    IsLocalization.AtPrime.under_maximalIdeal S p
  rw [← Ideal.mem_comap, h2] at this
  exact this

variable (S) in
theorem mem_iff_parPrime_le (hrsp : FinalTheorems.Rsp S n (fun i => algebraMap A S (f i))) (i : Fin n)
    {Q : Ideal A} [Q.IsPrime] (hQ : Q ≤ p) : f i ∈ Q ↔ parPrime (S := S) f i ≤ Q := by
  refine ⟨fun h => ?_, fun h => h (parPrime_spec (p := p) S hrsp i).2.2⟩
  have hdisj : Disjoint (p.primeCompl : Set A) Q := by
    rw [Set.disjoint_left]
    intro a ha haQ
    exact ha (hQ haQ)
  have hQ' := IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S ‹Q.IsPrime› hdisj
  intro a ha
  rw [← hQ']
  show algebraMap A S a ∈ Q.map (algebraMap A S)
  have h1 : Ideal.span {algebraMap A S (f i)} ≤ Q.map (algebraMap A S) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ h
  exact h1 (Ideal.mem_comap.mp ha)

variable (S) in
theorem eq_of_mem_parPrime (hrsp : FinalTheorems.Rsp S n (fun i => algebraMap A S (f i))) {i j : Fin n}
    (h : f j ∈ parPrime (S := S) f i) : j = i := by
  by_contra hji
  have : IsDomain S := isDomain_of_isRegularLocalRing
  have hpi := prime_of_regular_params _ hrsp.1 hrsp.2 i
  have hpj := prime_of_regular_params _ hrsp.1 hrsp.2 j
  have hd : algebraMap A S (f i) ∣ algebraMap A S (f j) :=
    Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp h)
  have hass : Associated (algebraMap A S (f i)) (algebraMap A S (f j)) :=
    hpi.associated_of_dvd hpj hd
  exact (regular_params_spec _ hrsp.1 hrsp.2).2 i j (Ne.symm hji) hass

end Alg

noncomputable section

section Pts

variable {W : Scheme.{0}} {U : W.Opens}

theorem specializes_iff_pOf (hU : IsAffineOpen U) {z z' : W} (hz : z ∈ U) (hz' : z' ∈ U) :
    z ⤳ z' ↔ hU.primeIdealOf ⟨z, hz⟩ ≤ hU.primeIdealOf ⟨z', hz'⟩ := by
  have := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff
    (x := hU.primeIdealOf ⟨z, hz⟩) (y := hU.primeIdealOf ⟨z', hz'⟩)
  rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this
  rw [PrimeSpectrum.le_iff_specializes]
  exact this

theorem eq_of_pOf_eq (hU : IsAffineOpen U) {z z' : W} (hz : z ∈ U) (hz' : z' ∈ U)
    (h : hU.primeIdealOf ⟨z, hz⟩ = hU.primeIdealOf ⟨z', hz'⟩) : z = z' := by
  have h1 := hU.fromSpec_primeIdealOf ⟨z, hz⟩
  have h2 := hU.fromSpec_primeIdealOf ⟨z', hz'⟩
  rw [h] at h1
  exact h1.symm.trans h2

theorem fromSpec_mem (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(W, U)) : hU.fromSpec P ∈ U := by
  have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
  rwa [hU.range_fromSpec] at this

theorem pOf_fromSpec (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(W, U)) :
    hU.primeIdealOf ⟨hU.fromSpec P, fromSpec_mem hU P⟩ = P :=
  hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)

end Pts

end

end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
end
