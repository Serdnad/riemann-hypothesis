module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle113
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle196
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle322
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle321
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle007
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem under_place {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {t : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A t) :
    IsPlaceOver A (t.under (𝓞 ℚ)) := fun x => by
  rw [IsScalarTower.algebraMap_apply ℚ F Ω]
  exact hA (algebraMap _ _ x)

private theorem res_dec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (g : G F Ω) :
    (AlgEquiv.restrictScalarsHom ℚ g : G ℚ Ω) ∈ Dec (F := ℚ) A ↔ g ∈ Dec (F := F) A :=
  GlobalTheory.AboveL.mem_dec_congr A _ g fun _ => rfl

private theorem res_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (g : G F Ω) :
    (AlgEquiv.restrictScalarsHom ℚ g : G ℚ Ω) ∈ Ine (F := ℚ) A ↔ g ∈ Ine (F := F) A := by
  rw [mem_Ine, mem_Ine]
  exact Iff.rfl

private theorem eq_of_natCast_mem {p : ℕ} (hp : p.Prime) {a b : HeightOneSpectrum (𝓞 ℚ)}
    (ha : ((p : ℕ) : 𝓞 ℚ) ∈ a.asIdeal) (hb : ((p : ℕ) : 𝓞 ℚ) ∈ b.asIdeal) : a = b := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hmax : (Ideal.span {((p : ℕ) : 𝓞 ℚ)}).IsMaximal := by
    have h := Ideal.map_isMaximal_of_equiv Rat.ringOfIntegersEquiv.symm (p := Ideal.span {(p : ℤ)})
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h
  have key : ∀ c : HeightOneSpectrum (𝓞 ℚ), ((p : ℕ) : 𝓞 ℚ) ∈ c.asIdeal →
      c.asIdeal = Ideal.span {((p : ℕ) : 𝓞 ℚ)} := fun c hc =>
    (hmax.eq_of_le c.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hc)).symm
  exact HeightOneSpectrum.ext ((key a ha).trans (key b hb).symm)

private theorem natCast_normV_mem (u : HeightOneSpectrum (𝓞 ℚ)) (h : (normV u).Prime) :
    ((normV u : ℕ) : 𝓞 ℚ) ∈ u.asIdeal := by
  have hne : Nat.card (𝓞 ℚ ⧸ u.asIdeal) ≠ 0 := by
    have h0 := h.ne_zero
    unfold normV at h0
    exact h0
  haveI : Finite (𝓞 ℚ ⧸ u.asIdeal) := Nat.finite_of_card_ne_zero hne
  haveI := Fintype.ofFinite (𝓞 ℚ ⧸ u.asIdeal)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  unfold normV
  rw [Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero _

private theorem core {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (hFC : FreshChar) (V : Subgroup (G F Ω)) (hV : IsOpen (V : Set (G F Ω)))
    (T : Set (HeightOneSpectrum (𝓞 F))) (hT : T.Finite) (n : ℕ) (hn : 0 < n) :
    ∃ ψ : G F Ω →* ℂˣ, Good ψ.ker ∧
      (∀ (t : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A t →
        Ine (F := F) A ≤ ψ.ker ∨ Dec (F := F) A ≤ V) ∧ ψ ^ n = 1 ∧
      (∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := F) A, ψ g = 1) ∧
      ∃ u ∉ T, ∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := F) A ≤ V ∧
        ∃ τ ∈ Ine (F := F) A, orderOf (ψ τ) = n := by
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
  let res : G F Ω →* G ℚ Ω := AlgEquiv.restrictScalarsHom ℚ
  have hres_inj : Function.Injective res := fun g h hgh => AlgEquiv.ext fun x => by
    have e := congrArg (fun σ : G ℚ Ω => σ x) hgh
    exact e
  have hVo : IsOpen ((V.map res : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) :=
    GlobalTheory.KLift.isOpen_map_restrictScalars V hV
  obtain ⟨ψ₀, hG₀, hpow₀, hT₀, u₀, hu₀T, hp, hu₀, hram⟩ := hFC ℚ Ω (V.map res) hVo
    ((fun t : HeightOneSpectrum (𝓞 F) => t.under (𝓞 ℚ)) '' T) (hT.image _) n hn
  have decV : ∀ A : ValuationSubring Ω, IsPlaceOver A u₀ → Dec (F := F) A ≤ V := by
    intro A hA g hg
    obtain ⟨h, hhV, hh⟩ := (hu₀ A hA).1 ((res_dec A g).2 hg)
    rwa [hres_inj hh] at hhV
  obtain ⟨A₀, hA₀⟩ := exists_isPlaceOver Ω u₀
  obtain ⟨u, hu⟩ := GlobalTheory.AbOverSubfield.exists_place_between (F := ℚ) (K := F) hA₀
  have eu : u.under (𝓞 ℚ) = u₀ := eq_of_isPlaceOver (under_place hu) hA₀
  have hunder : ∀ A : ValuationSubring Ω, IsPlaceOver A u → IsPlaceOver A u₀ := by
    intro A hA
    rw [← eu]
    exact under_place hA
  refine ⟨ψ₀.comp res, ?_, ?_, ?_, ?_, u, ?_, ?_⟩
  · refine ⟨hG₀.isOpen.preimage (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ F Ω),
      Abelianization.commutator_subset_ker _, fun j c hc => ?_⟩
    exact hG₀.real j (res c) hc
  · intro t A hA
    by_cases hpt : ((normV u₀ : ℕ) : 𝓞 ℚ) ∈ (t.under (𝓞 ℚ)).asIdeal
    · right
      have e : t.under (𝓞 ℚ) = u₀ := eq_of_natCast_mem hp hpt (natCast_normV_mem u₀ hp)
      apply decV
      rw [← e]
      exact under_place hA
    · left
      intro g hg
      exact hram _ A (under_place hA) hpt _ ((res_ine A g).2 hg)
  · refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hpow₀,
      MonoidHom.one_apply, MonoidHom.one_apply]
  · intro t ht A hA g hg
    exact hT₀ _ ⟨t, ht, rfl⟩ A (under_place hA) _ ((res_dec A g).2 hg)
  · intro huT
    exact hu₀T ⟨u, huT, eu⟩
  · intro A hA
    refine ⟨decV A (hunder A hA), ?_⟩
    obtain ⟨τ₀, hτ₀, ho⟩ := (hu₀ A (hunder A hA)).2
    obtain ⟨h, -, hh⟩ := (hu₀ A (hunder A hA)).1 (Ine_le_Dec A hτ₀)
    refine ⟨h, (res_ine A h).1 (by rw [show res h = τ₀ from hh]; exact hτ₀), ?_⟩
    show orderOf (ψ₀ (res h)) = n
    rw [show res h = τ₀ from hh]
    exact ho

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.freshSplit :
    FreshChar → FreshSplit := by
  intro hFC E Ω _ _ _ _ _ _ U hU T hT n hn
  haveI := isAlgClosure_plus (E := E) (Ω := Ω)
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  obtain ⟨ψ, h1, h2, h3, h4, u, hu, h5⟩ := core hFC (U ⊓ fixGrp (maximalRealSubfield E) Ω E)
    (hU.inter (isOpen_fixGrp _ Ω E)) T hT n hn
  exact ⟨ψ, h1, fun t A hA => (h2 t A hA).imp_right fun h g hg => (h hg).2, h3, h4, u, hu,
    fun A hA => ⟨fun g hg => ((h5 A hA).1 hg).1, (h5 A hA).2⟩⟩
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.layerOf :
    InclOf → IndexComap → LayerOf := by
  intro hIncl hIdx
  unfold LayerOf
  intro E Ω _ _ _ _ _ _ S H H' hH' hle hp X Y hX hY u hS hDec hτex
  obtain ⟨A, hA, τ, hτ, hτ'⟩ := hτex
  unfold Cuts at hX hY
  have overUnder : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver B w →
      IsPlaceOver B (w.under (𝓞 (maximalRealSubfield E))) := by
    intro B w hB x
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, ← hB]
    rfl
  have resLift : ∀ (g : G (maximalRealSubfield E) Ω) (hg : Fixes E g),
      AlgEquiv.restrictScalarsHom (maximalRealSubfield E) (GlobalTheory.AboveL.DecRes.lift (E := E) g hg) = g :=
    fun g hg => AlgEquiv.ext fun x => rfl
  have hτD := Ine_le_Dec A hτ
  obtain ⟨hτE, hτH⟩ := hDec A hA τ hτD
  obtain ⟨τ', hres⟩ : ∃ τ' : G E Ω, AlgEquiv.restrictScalarsHom (maximalRealSubfield E) τ' = τ :=
    ⟨_, resLift τ hτE⟩
  have fY : fixGrp E Ω Y.K = H'.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) :=
    Subgroup.ext fun g => hY g
  have fX : fixGrp E Ω X.K = H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) :=
    Subgroup.ext fun g => hX g
  have hidx := hIdx (G (maximalRealSubfield E) Ω) (G E Ω)
    (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) H H' hH'.comm hle hp
    ⟨τ', by rw [hres]; exact hτH, by rw [hres]; exact hτ'⟩
  obtain ⟨x0, t0E, t0Ω, hgal, hfin⟩ := hIncl E Ω X Y (by rw [fY, fX]; exact Subgroup.comap_mono hle)
  rw [fY, fX, hidx] at hfin
  obtain ⟨w, hw⟩ := GlobalTheory.AbOverSubfield.exists_place_between (F := maximalRealSubfield E) (K := E) hA
  have hwu : w.under (𝓞 (maximalRealSubfield E)) = u := eq_of_isPlaceOver (overUnder A w hw) hA
  have hfixX : Fixes X.K τ' := (hX τ').2 (by rw [hres]; exact hτH)
  refine ⟨⟨x0, t0E, t0Ω, hgal, by rw [hfin]; exact hp, w, ?_, ?_, A, hw,
    GlobalTheory.AboveL.DecRes.lift (E := X.K) τ' hfixX, ?_, ?_⟩, ?_⟩
  · intro hwS
    exact hS w hwS hwu
  · intro B hB g hg
    have hBu : IsPlaceOver B u := by
      rw [← hwu]
      exact overUnder B w hB
    obtain ⟨hgE, hgH⟩ := hDec B hBu g hg
    refine ⟨hgE, ?_⟩
    have h1 := (hX (GlobalTheory.AboveL.DecRes.lift (E := E) g hgE)).2 (by rw [resLift]; exact hgH)
    exact h1
  · subst hres
    rw [mem_Ine]
    have hτI := (mem_Ine (A := A)).1 hτ
    exact ⟨(GlobalTheory.AboveL.mem_dec_congr A _ _ (fun x => rfl)).2 hτI.1, hτI.2⟩
  · intro hfix
    exact hτ' (by rw [← hres]; exact (hY τ').1 hfix)
  · intro x1 t1
    have hx : x1 = x0 := by
      refine Algebra.algebra_ext _ _ fun r => (algebraMap Y.K Ω).injective ?_
      rw [← @IsScalarTower.algebraMap_apply X.K Y.K Ω _ _ _ x1 _ _ t1 r,
        ← @IsScalarTower.algebraMap_apply X.K Y.K Ω _ _ _ x0 _ _ t0Ω r]
    subst hx
    exact hfin
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem zpow_mem_fix {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (σ : G F Ω) (z : Ω)
    (h : σ z = z) (n : ℤ) : (σ ^ n) z = z := by
  have hs : σ ∈ MulAction.stabilizer (G F Ω) z := h
  exact (MulAction.stabilizer (G F Ω) z).zpow_mem hs n

private theorem sq_apply_of_pm {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (φ : G F Ω) (z : Ω)
    (h : φ z = z ∨ φ z = -z) : (φ ^ (2 : ℤ)) z = z := by
  have e : φ ^ (2 : ℤ) = φ * φ := zpow_two φ
  rw [e, AlgEquiv.mul_apply]
  rcases h with h | h
  · rw [h, h]
  · rw [h, map_neg, h, neg_neg]

private theorem fix_of_parity {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [CharZero Ω] (φ : G F Ω) (e x : Ω)
    (he0 : e ≠ 0) (hφe : φ e = e ∨ φ e = -e) (hφx : φ x = x ∨ φ x = -x) (k m : ℤ)
    (hk : (φ ^ k) e ≠ e) (hm : (φ ^ m) e = e) : (φ ^ m) x = x := by
  rcases Int.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hj, ← two_mul, zpow_mul]
    exact zpow_mem_fix _ x (sq_apply_of_pm φ x hφx) j
  · exfalso
    have hφe' : φ e = -e := by
      rcases hφe with h | h
      · exact absurd (zpow_mem_fix φ e h k) hk
      · exact h
    rw [hj, zpow_add, zpow_one, zpow_mul, AlgEquiv.mul_apply, hφe', map_neg,
      zpow_mem_fix _ e (sq_apply_of_pm φ e hφe) j] at hm
    have h2 : (2 : Ω) * e = 0 := by linear_combination -hm
    rcases mul_eq_zero.1 h2 with h | h
    · exact two_ne_zero h
    · exact he0 h

private theorem pm_of_sq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (σ : G F Ω) (z : Ω)
    (h : σ (z ^ 2) = z ^ 2) : σ z = z ∨ σ z = -z := by
  rw [map_pow] at h
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

private theorem fixes_of_imag {Y Ω : Type} [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra Y Ω]
    (e : Y) (he : e ≠ 0) (hce : IsCMField.complexConj Y e = -e) (g : G (maximalRealSubfield Y) Ω)
    (hg : g (algebraMap Y Ω e) = algebraMap Y Ω e) : Fixes Y g := by
  intro y
  have h2 : (2 : Y) ≠ 0 := two_ne_zero
  obtain ⟨a, haa⟩ : ∃ a : Y, a = (y + IsCMField.complexConj Y y) / 2 := ⟨_, rfl⟩
  obtain ⟨b, hbb⟩ : ∃ b : Y, b = (y - IsCMField.complexConj Y y) / (2 * e) := ⟨_, rfl⟩
  have ha : IsCMField.complexConj Y a = a := by
    rw [haa, map_div₀, map_add (f := _), IsCMField.complexConj_apply_apply, map_ofNat, add_comm]
  have hb : IsCMField.complexConj Y b = b := by
    rw [hbb, map_div₀, map_sub, IsCMField.complexConj_apply_apply, map_mul, map_ofNat, hce]
    field_simp
    ring
  have hy : y = a + e * b := by
    rw [haa, hbb]
    field_simp
    ring
  have hfa : g (algebraMap Y Ω a) = algebraMap Y Ω a :=
    g.commutes ⟨a, (IsCMField.complexConj_eq_self_iff Y a).1 ha⟩
  have hfb : g (algebraMap Y Ω b) = algebraMap Y Ω b :=
    g.commutes ⟨b, (IsCMField.complexConj_eq_self_iff Y b).1 hb⟩
  rw [hy, map_add (f := _), map_mul, map_add (f := _), map_mul, hfa, hfb, hg]

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.inertSplit :
    DecGen → InertSplit := by
  intro hD Y Ω _ _ _ _ _ _ A u hu x a hx hI hg h hh
  obtain ⟨g, hgD, hgY⟩ := hg
  haveI : IsAlgClosure (maximalRealSubfield Y) Ω := IsAlgClosure.ofAlgebraic _ Y Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 (maximalRealSubfield Y)), IsPlaceOver A v := by
    refine ⟨⟨u.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield Y)) (𝓞 Y)), Ideal.IsPrime.comap _, ?_⟩, ?_⟩
    · intro hb
      exact u.ne_bot (Ideal.eq_bot_of_comap_eq_bot hb)
    · intro z
      exact hu (algebraMap (𝓞 (maximalRealSubfield Y)) (𝓞 Y) z)
  obtain ⟨φ, hφ⟩ := exists_isFrob hv
  obtain ⟨e, he0, hce⟩ : ∃ e : Y, e ≠ 0 ∧ IsCMField.complexConj Y e = -e := by
    obtain ⟨y, hy⟩ : ∃ y : Y, IsCMField.complexConj Y y ≠ y := by
      by_contra hc
      push_neg at hc
      exact IsCMField.complexConj_ne_one Y (AlgEquiv.ext hc)
    refine ⟨y - IsCMField.complexConj Y y, sub_ne_zero.2 (Ne.symm hy), ?_⟩
    rw [map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hXf : ({x, algebraMap Y Ω e} : Set Ω).Finite := Set.toFinite _
  have hIX : ∀ τ ∈ (Ine A : Subgroup (G (maximalRealSubfield Y) Ω)),
      ∀ y ∈ ({x, algebraMap Y Ω e} : Set Ω), τ y = y := by
    intro τ hτ y hy
    rcases hy with rfl | rfl
    · exact (hI τ hτ).2
    · exact (hI τ hτ).1 e
  let h' : G (maximalRealSubfield Y) Ω := AlgEquiv.restrictScalars _ h
  have hh' : h' ∈ Dec A := (GlobalTheory.AboveL.mem_dec_congr A h' h (fun _ => rfl)).2 hh
  obtain ⟨k, hk⟩ := hD _ Ω A v hv φ hφ _ hXf hIX g hgD
  obtain ⟨m, hm⟩ := hD _ Ω A v hv φ hφ _ hXf hIX h' hh'
  have hE0 : algebraMap Y Ω e ≠ 0 := (map_ne_zero _).2 he0
  have hpmE : φ (algebraMap Y Ω e) = algebraMap Y Ω e ∨ φ (algebraMap Y Ω e) = -algebraMap Y Ω e := by
    apply pm_of_sq
    have hs : e ^ 2 ∈ maximalRealSubfield Y := by
      rw [← IsCMField.complexConj_eq_self_iff, map_pow, hce, neg_sq]
    rw [← map_pow]
    exact φ.commutes (⟨e ^ 2, hs⟩ : maximalRealSubfield Y)
  have hpmx : φ x = x ∨ φ x = -x := by
    apply pm_of_sq
    rw [hx, map_intCast]
  have hkE : (φ ^ k) (algebraMap Y Ω e) ≠ algebraMap Y Ω e := by
    rw [← hk _ (by simp)]
    intro hgE
    exact hgY (fixes_of_imag e he0 hce g hgE)
  have hmE : (φ ^ m) (algebraMap Y Ω e) = algebraMap Y Ω e := by
    rw [← hm _ (by simp)]
    exact h.commutes e
  have hfx := fix_of_parity φ _ x hE0 hpmE hpmx k m hkE hmE
  rw [← hm x (by simp)] at hfx
  exact hfx
end
