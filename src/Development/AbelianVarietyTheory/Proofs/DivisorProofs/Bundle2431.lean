module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy.MultIso

theorem ord_ringEquiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) :
    Ring.ord B (e a) = Ring.ord A a := by
  have : RingHomSurjective (e : A →+* B) := ⟨e.surjective⟩
  have hIJ : Ideal.span {e a} = (Ideal.span {a}).map (e : A →+* B) := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  let q := Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {e a}) e hIJ
  let f : (A ⧸ Ideal.span {a}) →ₛₗ[(e : A →+* B)] (B ⧸ Ideal.span {e a}) :=
    { toFun := q
      map_add' := q.map_add
      map_smul' := fun r x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        show q (Ideal.Quotient.mk _ (r * y)) = Ideal.Quotient.mk _ (e r) * q (Ideal.Quotient.mk _ y)
        rw [Ideal.quotientEquiv_mk, Ideal.quotientEquiv_mk, map_mul, map_mul] }
  rw [Ring.ord, Ring.ord, Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f q.bijective)]

theorem ordFrac_ringEquiv {A B K L : Type} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Ring.KrullDimLE 1 A] [Ring.KrullDimLE 1 B]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    (e : A ≃+* B) (φ : K →+* L) (h : ∀ a, φ (algebraMap A K a) = algebraMap B L (e a)) (f : K) :
    Ring.ordFrac B (φ f) = Ring.ordFrac A f := by
  have key : ∀ a : A, Ring.ordFrac B (algebraMap B L (e a)) = Ring.ordFrac A (algebraMap A K a) := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp
    have hea : e a ≠ 0 := by simpa using ha
    rw [Ring.ordFrac_eq_ord (R := B) (K := L), Ring.ordFrac_eq_ord (R := A) (K := K)]
    simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, ha, hea, not_false_eq_true, if_true,
      ord_ringEquiv]
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) f
  dsimp only at hxy
  subst hxy
  have hspec := IsLocalization.mk'_spec K x y
  have h1 : Ring.ordFrac A (IsLocalization.mk' K x y) * Ring.ordFrac A (algebraMap A K y) =
      Ring.ordFrac A (algebraMap A K x) := by rw [← map_mul, hspec]
  have h2 : Ring.ordFrac B (φ (IsLocalization.mk' K x y)) * Ring.ordFrac B (algebraMap B L (e y)) =
      Ring.ordFrac B (algebraMap B L (e x)) := by rw [← map_mul, ← h, ← map_mul, hspec, h]
  rw [key, key] at h2
  have hy : algebraMap A K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2
  have hc : Ring.ordFrac A (algebraMap A K y) ≠ 0 := (map_ne_zero _).mpr hy
  exact mul_right_cancel₀ hc (h2.trans h1.symm)

private theorem isIso_stalkMap_restrict_of_isIso {X Y : Scheme.{0}} (s : Y ⟶ X) (U : X.Opens)
    [IsIso (s ∣_ U)] (x : s ⁻¹ᵁ U) : IsIso ((s ∣_ U).stalkMap x) := by
  have h : IsOpenImmersion (s ∣_ U) := inferInstance
  exact LocallyRingedSpace.IsOpenImmersion.stalk_iso (H := h) (s ∣_ U).toLRSHom x

theorem isIso_stalkMap_of_isIso_restrict {X Y : Scheme.{0}} (s : Y ⟶ X) (U : X.Opens)
    [IsIso (s ∣_ U)] (w : Y) (hw : s w ∈ U) : IsIso (s.stalkMap w) := by
  have hw' : w ∈ s ⁻¹ᵁ U := hw
  have e := morphismRestrictStalkMap s U ⟨w, hw'⟩
  have hi : IsIso ((s ∣_ U).stalkMap ⟨w, hw'⟩) := isIso_stalkMap_restrict_of_isIso s U _
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).mp hi

theorem coheight_eq_of_isIso_stalkMap {X Y : Scheme.{0}} (s : Y ⟶ X) (w : Y)
    [IsIso (s.stalkMap w)] : Order.coheight w = Order.coheight (s w) := by
  apply WithBot.coe_injective
  rw [← ringKrullDim_stalk_eq_coheight, ← ringKrullDim_stalk_eq_coheight]
  exact (ringKrullDim_eq_of_ringEquiv (asIso (s.stalkMap w)).commRingCatIsoToRingEquiv).symm

theorem ord_functionFieldMap_of_isIso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X)
    [IsDominant s] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (w : Y)
    [IsIso (s.stalkMap w)] (f : X.functionField) :
    Scheme.ord (functionFieldMap s f) w = Scheme.ord f (s w) := by
  have hco := coheight_eq_of_isIso_stalkMap s w
  by_cases hc : Order.coheight (s w) = 1
  · have hw : Order.coheight w = 1 := hco.trans hc
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hw, Scheme.ord_eq_ordHom_of_coheight_eq_one hc]
    have : Ring.KrullDimLE 1 (X.presheaf.stalk (s w)) := krullDimLE_of_coheight_le hc.le
    have : Ring.KrullDimLE 1 (Y.presheaf.stalk w) := krullDimLE_of_coheight_le hw.le
    congr 2
    exact ordFrac_ringEquiv (asIso (s.stalkMap w)).commRingCatIsoToRingEquiv (functionFieldMap s)
      (fun a => functionFieldMap_algebraMap s w a) f
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hc,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hc (hco ▸ h))]

theorem coheight_eq_and_mult_pullCart : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (U : X.Opens), IsIso (s ∣_ U) → ∀ w : Y, s w ∈ U → Order.coheight w = Order.coheight (s w) ∧ ∀ D : CartierDiv X, (pullCart s D).mult w = D.mult (s w) := by
  intro X Y _ _ s _ _ _ U hU w hw
  haveI := hU
  haveI := isIso_stalkMap_of_isIso_restrict s U w hw
  refine ⟨coheight_eq_of_isIso_stalkMap s w, fun D => ?_⟩
  obtain ⟨g, hg⟩ := D.exists_isEqn (s w)
  rw [(isEqn_pullCart s hg).mult_eq, hg.mult_eq]
  exact ord_functionFieldMap_of_isIso s w (g : X.functionField)

end GlobalTheory.Discrepancy.MultIso
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

variable {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

theorem functionFieldMap_comp_dominant (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t] :
    functionFieldMap (t ≫ s) = (functionFieldMap t).comp (functionFieldMap s) := by
  ext f
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective
    (A := X.presheaf.stalk ((t ≫ s) (genericPoint Z))) f
  have key : ∀ c : X.presheaf.stalk ((t ≫ s) (genericPoint Z)),
      functionFieldMap (t ≫ s) (algebraMap _ X.functionField c) =
        functionFieldMap t (functionFieldMap s (algebraMap _ X.functionField c)) := by
    intro c
    have h1 := functionFieldMap_algebraMap (t ≫ s) (genericPoint Z) c
    have h2 := functionFieldMap_algebraMap s (t (genericPoint Z)) c
    have h3 := functionFieldMap_algebraMap t (genericPoint Z) (s.stalkMap (t (genericPoint Z)) c)
    refine h1.trans (Eq.trans ?_ ((congrArg (functionFieldMap t) h2).trans h3).symm)
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  simp only [map_div₀, RingHom.comp_apply, key]

theorem pullCart_comp (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t] (D : CartierDiv X) :
    pullCart (t ≫ s) D = pullCart t (pullCart s D) :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨g, hg⟩ := D.exists_isEqn ((t ≫ s) z)
    refine ⟨_, isEqn_pullCart (t ≫ s) hg, ?_⟩
    have e : fnPull (t ≫ s) g = fnPull t (fnPull s g) :=
      Units.ext (RingHom.congr_fun (functionFieldMap_comp_dominant s t) g)
    rw [e]
    exact isEqn_pullCart t (isEqn_pullCart s hg)

theorem isDivOfForm_ratPull_comp {k : Type} [Field k] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s]
    (t : Z ⟶ Y) [IsDominant t] (n : ℕ) (η : RatForms p n) (K : CartierDiv Z) :
    IsDivOfForm K (EtaleKlt.ratPull p (t ≫ s) n η) ↔
      IsDivOfForm K (EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η)) := by
  have key : ∀ (q q' : Z ⟶ Sp k) (_ : q = q') (φ : X.functionField →+* Z.functionField)
      (h : φ.comp (Cartier.constFn p) = Cartier.constFn q) (h' : φ.comp (Cartier.constFn p) = Cartier.constFn q'),
      IsDivOfForm (p := q) K (TopForm.formMap n φ h η) ↔
        IsDivOfForm (p := q') K (TopForm.formMap n φ h' η) := by
    intro q q' e φ h h'
    subst e
    rfl
  have h' : (functionFieldMap (t ≫ s)).comp (Cartier.constFn p) = Cartier.constFn (t ≫ s ≫ p) := by
    rw [EtaleKlt.functionFieldMap_comp_constFn, Category.assoc]
  have e : EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η) =
      TopForm.formMap n (functionFieldMap (t ≫ s)) h' η :=
    formMap_formMap _ _ _ (functionFieldMap_comp_dominant s t).symm _ _ _ η
  rw [e]
  exact key _ _ (Category.assoc t s p) _ _ h'

theorem pull_comp : ∀ (k : Type) [Field k] (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t], functionFieldMap (t ≫ s) = (functionFieldMap t).comp (functionFieldMap s) ∧ (∀ D : CartierDiv X, pullCart (t ≫ s) D = pullCart t (pullCart s D)) ∧ ∀ (n : ℕ) (η : RatForms p n) (K : CartierDiv Z), IsDivOfForm K (EtaleKlt.ratPull p (t ≫ s) n η) ↔ IsDivOfForm K (EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η)) :=
  fun _ _ _ _ _ _ _ _ p s _ t _ =>
    ⟨functionFieldMap_comp_dominant s t, pullCart_comp s t, isDivOfForm_ratPull_comp p s t⟩

end GlobalTheory.Discrepancy
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BirOrd

theorem formOrd_ratPull_of_over : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ (n : ℕ) (η : RatForms p n), η ≠ 0 → E'.formOrd (EtaleKlt.ratPull p s n η) = E.formOrd η := by
  intro k _ X Y _ _ p s _ hbij E' E hO n η hη
  set φ := functionFieldMap s with hφdef
  let φe : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective φ hbij
  have hpc : φ.comp (Cartier.constFn p) = Cartier.constFn (s ≫ p) :=
    EtaleKlt.functionFieldMap_comp_constFn p s
  have hcc : (φe.symm : Y.functionField →+* X.functionField).comp (Cartier.constFn (s ≫ p)) =
      Cartier.constFn p := by
    ext a
    rw [← hpc]
    exact φe.symm_apply_apply _

  let Φ' := TopForm.formMap n (φe.symm : Y.functionField →+* X.functionField) hcc
  have hinv : ∀ ξ : RatForms p n, Φ' (EtaleKlt.ratPull p s n ξ) = ξ := by
    intro ξ
    have e0 : (φe.symm : Y.functionField →+* X.functionField).comp φ = RingHom.id _ := by
      ext x
      exact φe.symm_apply_apply x
    refine (TopForm.formMap_formMap φ (φe.symm : Y.functionField →+* X.functionField)
      (RingHom.id _) e0 hpc hcc (RingHom.id_comp _) ξ).trans ?_
    exact TopForm.formMap_of_eq_id _ rfl _ ξ

  let ψ : E.ring →+* E'.ring := φ.restrict E.ring E'.ring fun x hx => (hO x).1 hx
  have hψv : ∀ a, (ψ a : Y.functionField) = φ a := fun _ => rfl
  have hψb : Function.Bijective ψ := by
    refine ⟨fun a b h => Subtype.ext (hbij.1 (by simpa [hψv] using congrArg Subtype.val h)), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := hbij.2 (y : Y.functionField)
    have hxE : x ∈ E.ring := (hO x).2 (hx ▸ y.2)
    exact ⟨⟨x, hxE⟩, Subtype.ext hx⟩
  let eψ : E.ring ≃+* E'.ring := RingEquiv.ofBijective ψ hψb
  let χ : E'.ring →+* E.ring := eψ.symm
  have hc : ψ.comp E.const = E'.const := by
    ext a
    exact RingHom.congr_fun hpc a
  have hc' : χ.comp E'.const = E.const := by
    ext a
    rw [← hc]
    exact congrArg Subtype.val (eψ.symm_apply_apply (E.const a))
  have hχv : ∀ y, ((χ y : E.ring) : X.functionField) = φe.symm (y : Y.functionField) := by
    intro y
    obtain ⟨x, rfl⟩ := eψ.surjective y
    have h1 : χ (eψ x) = x := eψ.symm_apply_apply x
    rw [h1]
    exact (φe.symm_apply_apply (x : X.functionField)).symm

  have hord : ∀ g : X.functionFieldˣ, E'.ord (Units.map φ.toMonoidHom g) = E.ord g := by
    intro g
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
    exact EtaleDiv.log_ordFrac_map E.ring E'.ring φ ψ hψv ht (ht.map eψ) g.ne_zero
  have hfe : ∀ ω : Forms E.const n, IsFreeGen E.ring ω →
      IsFreeGen E'.ring (TopForm.formMap n ψ hc ω) := fun ω hω =>
    EtaleDiv.isFreeGen_formMap (EtaleDiv.formallyEtale_of_bijective ψ hψb) hc hω
  have hfe' : ∀ ω : Forms E'.const n, IsFreeGen E'.ring ω →
      IsFreeGen E.ring (TopForm.formMap n χ hc' ω) := fun ω hω =>
    EtaleDiv.isFreeGen_formMap (EtaleDiv.formallyEtale_of_bijective χ eψ.symm.bijective) hc' hω
  have hτ : (E'.ring.subtype.comp ψ).comp E.const = Cartier.constFn (s ≫ p) := by
    rw [RingHom.comp_assoc, hc]
    rfl
  have key : ∀ ω : Forms E.const n,
      EtaleKlt.ratPull p s n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ψ hc ω) := by
    intro ω
    have e : φ.comp E.ring.subtype = E'.ring.subtype.comp ψ := by
      ext x
      rfl
    have k1 := TopForm.formMap_formMap (D := n) E.ring.subtype φ _ e rfl hpc hτ ω
    have k2 := TopForm.formMap_formMap (D := n) ψ E'.ring.subtype _ rfl hc rfl hτ ω
    exact k1.trans k2.symm
  have hτ' : (E.ring.subtype.comp χ).comp E'.const = Cartier.constFn p := by
    rw [RingHom.comp_assoc, hc']
    rfl
  have key' : ∀ ω : Forms E'.const n,
      Φ' (E'.toRat n ω) = E.toRat n (TopForm.formMap n χ hc' ω) := by
    intro ω
    have e : (φe.symm : Y.functionField →+* X.functionField).comp E'.ring.subtype =
        E.ring.subtype.comp χ := by
      ext y
      exact (hχv y).symm
    have k1 := TopForm.formMap_formMap (D := n) E'.ring.subtype
      (φe.symm : Y.functionField →+* X.functionField) _ e rfl hcc hτ' ω
    have k2 := TopForm.formMap_formMap (D := n) χ E.ring.subtype _ rfl hc' rfl hτ' ω
    exact k1.trans k2.symm
  have fwd : ∀ a, E.IsFormOrd η a → E'.IsFormOrd (EtaleKlt.ratPull p s n η) a := by
    rintro a ⟨ω, hω, g, hη', hg⟩
    refine ⟨_, hfe ω hω, Units.map φ.toMonoidHom g, ?_, (hord g).trans hg⟩
    rw [hη', map_smulₛₗ, key]
    rfl
  have bwd : ∀ a, E'.IsFormOrd (EtaleKlt.ratPull p s n η) a → E.IsFormOrd η a := by
    rintro a ⟨ω, hω, f, hη', hf⟩
    let g : X.functionFieldˣ := Units.map (φe.symm : Y.functionField →+* X.functionField).toMonoidHom f
    have hgf : Units.map φ.toMonoidHom g = f := by
      ext
      exact φe.apply_symm_apply (f : Y.functionField)
    refine ⟨_, hfe' ω hω, g, ?_, ?_⟩
    · rw [← hinv η, hη', map_smulₛₗ, key']
      rfl
    · rw [← hord g, hgf, hf]
  have hne : EtaleKlt.ratPull p s n η ≠ 0 := by
    intro h0
    apply hη
    rw [← hinv η, h0, map_zero]
  by_cases h : ∃ a, E.IsFormOrd η a
  · obtain ⟨a, ha⟩ := h
    rw [ha.formOrd_eq hη, (fwd a ha).formOrd_eq hne]
  · have h' : ¬ ∃ a, E'.IsFormOrd (EtaleKlt.ratPull p s n η) a :=
      fun ⟨a, ha⟩ => h ⟨a, bwd a ha⟩
    rw [DivOver.formOrd, DivOver.formOrd, dite_eq_right h, dite_eq_right h']

end GlobalTheory.BirOrd
end
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTop.SqField

theorem gBig_and {Q Q' : GP} (h : GBig @Q) (h' : GBig @Q') :
    GBig fun {_ _ _ _} G μ C x b => Q G μ C x b ∧ Q' G μ C x b := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨a', ha'⟩ := h'
  refine ⟨max a a', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h1⟩ := ha ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h2⟩ := ha' ε CF (le_of_max_le_right hCF)
  refine ⟨max C0 C1, max x0 x1, fun C hC D large₂ he hx hR T Lc μ hμ G => ⟨?_, ?_⟩⟩
  · exact h1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hμ G
  · exact h2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hμ G

theorem isAlgebraic_norm {D : D7} {δ t0 : ℂ} {Q N : ℕ} {B : ℝ} {del : ℕ → ℝ} (hC : GlobalTheory.NormSum.CoordInt D N B Q del)
    (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (hP : P.Small N B) : IsAlgebraic ℚ ((P.norm : ℝ) : ℂ) := by
  have hco : ∀ h T, P.coord h T ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun h T => by
    obtain ⟨p, hp, hi⟩ := GlobalTheory.T.exists_prime_isIntegralOverStandardLatticeStabiliser D P.d h
    haveI : Fact p.Prime := ⟨hp⟩
    exact ((hC δ t0 p Q le_rfl P hP).2.2 h hi T).1
  have hsq : ∀ g, ((P.sq g : ℝ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun g => by
    unfold GlobalTheory.NormSum.Pair.sq
    rw [Complex.ofReal_sum]
    refine sum_mem fun T _ => ?_
    have e : ((‖P.coord g T‖ ^ 2 : ℝ) : ℂ) = P.coord g T * (starRingEnd ℂ) (P.coord g T) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e]
    exact mul_mem (hco g T)
      (mem_algebraicClosure_iff.2 ((mem_algebraicClosure_iff.1 (hco g T)).algHom (starRingEnd ℂ).toRatAlgHom))
  have hterm : ∀ h : GlobalTheory.NormSum.Cls D P.d P.J,
      (((((GlobalTheory.NormSum.gam D P.J h.out : ℝ))⁻¹ * P.sq h.out : ℝ)) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun h => by
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    exact mul_mem (inv_mem (natCast_mem _ _)) (hsq _)
  refine mem_algebraicClosure_iff.1 ?_
  unfold GlobalTheory.NormSum.Pair.norm
  by_cases hs : (Function.support fun h : GlobalTheory.NormSum.Cls D P.d P.J =>
      ((GlobalTheory.NormSum.gam D P.J h.out : ℝ))⁻¹ * P.sq h.out).Finite
  · rw [finsum_eq_sum _ hs, Complex.ofReal_sum]
    exact sum_mem fun h _ => hterm h
  · rw [finsum_of_infinite_support hs, Complex.ofReal_zero]
    exact zero_mem _

theorem isAlgebraic_div_of_beta {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {d s : ℕ} (hd : 0 < d)
    (hs : 1 ≤ s) (κ : I → ℕ) (Λ : PeriodPair) {x y : ℂ} (hx : x ≠ 0)
    (ha : IsAlgebraic ℚ (GlobalTheory.CMVal.beta E d s κ Λ x)) (hb : IsAlgebraic ℚ (GlobalTheory.CMVal.beta E d s κ Λ y)) :
    IsAlgebraic ℚ (y / x) := by
  have hC : (GlobalTheory.CMVal.C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (GlobalTheory.CMVal.cmValueConst_pos E hd (by omega) κ).ne'
  have hΔ : GlobalTheory.CMVal.latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ ≠ 0 := pow_ne_zero _ (GlobalTheory.CMVal.latDisc_ne_zero Λ)
  have e : (y / x) ^ 12 = GlobalTheory.CMVal.beta E d s κ Λ y / GlobalTheory.CMVal.beta E d s κ Λ x := by
    unfold GlobalTheory.CMVal.beta
    field_simp
  refine IsAlgebraic.of_pow (n := 12) (by norm_num) ?_
  rw [e]
  exact mem_algebraicClosure_iff.1 (div_mem (mem_algebraicClosure_iff.2 hb) (mem_algebraicClosure_iff.2 ha))

theorem sqIn_of {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T)
    (hI : GlobalTheory.NormSum.IntSt) (hΛ : ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ)
    (hT : ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c, ∃ x, IsTor G i j s (fam G μ₀ i j c) x ∧ x ≠ 0 ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ →
        IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D sc.cGap i j s) Λ x))
    (hQ : GlobalTheory.NormSum.GoodLevel D (levQ G.pl))
    (hS : ∀ (δ t0 : ℂ) (Q : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) t (i j : Fin D.R.m) 𝔪, IsBottom G t i j 𝔪 P P' →
      P.Small (bigN D) (maxWt D sc.cGap) ∧ P'.Small (bigN D) (maxWt D sc.cGap)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ GlobalTheory.BigTop.Fun.SqIn G μ₀ (algebraMap M ℂ) := by
  obtain ⟨C, -, hI⟩ := hI
  have hN : 1 ≤ bigN D := by have := D.R.m_add_three_le_k; unfold bigN; omega
  obtain ⟨-, del, -, hco, -⟩ := hI D (levQ G.pl) (bigN D) (maxWt D sc.cGap) (max 1 (Real.log D.host.rdE)) hQ hN
    (by exact_mod_cast le_max_left _ _) (le_max_left _ _) (le_max_right _ _)

  obtain ⟨Sn, hSn, hSa, hSb⟩ : ∃ Sn : Set ℂ, Sn.Finite ∧ (∀ z ∈ Sn, IsAlgebraic ℚ z) ∧
      (GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (fun _ => True) → GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (· ∈ Sn)) := by
    by_cases hb : GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (fun _ => True)
    · obtain ⟨δ, t0, hb⟩ := hb
      choose P P' hP using hb
      refine ⟨Set.range (fun ij => ((P ij).norm : ℂ)) ∪ Set.range (fun ij => ((P' ij).norm : ℂ)),
        (Set.finite_range _).union (Set.finite_range _), ?_,
        fun _ => ⟨δ, t0, fun ij => ⟨P ij, P' ij, (hP ij).1, Or.inl ⟨ij, rfl⟩, Or.inr ⟨ij, rfl⟩⟩⟩⟩
      rintro z (⟨ij, rfl⟩ | ⟨ij, rfl⟩)
      · exact isAlgebraic_norm hco _ (hS δ t0 _ _ _ _ _ _ _ (hP ij).1).1
      · exact isAlgebraic_norm hco _ (hS δ t0 _ _ _ _ _ _ _ (hP ij).1).2
    · exact ⟨∅, Set.finite_empty, fun z hz => absurd hz (Set.notMem_empty z), fun h => absurd h hb⟩

  let St : Set ℂ := ⋃ (i : Fin D.R.m) (j : Fin D.R.m) (s ∈ Set.Icc 1 (halfRank D i j)) (c : Bool),
    {z | ∃ x y, IsTor G i j s (nuH G μ₀ i j) x ∧ IsTor G i j s (nuH G μ₀ i j * delOf Lc c) y ∧ z = y / x}
  have hSt : St.Finite := by
    refine Set.finite_iUnion fun i => Set.finite_iUnion fun j => (Set.finite_Icc _ _).biUnion fun s _ =>
      Set.finite_iUnion fun c => Set.Subsingleton.finite ?_
    rintro _ ⟨x, y, hx, hy, rfl⟩ _ ⟨x', y', hx', hy', rfl⟩
    rw [hx.2.unique hx'.2, hy.2.unique hy'.2]
  have hd : 0 < D.host.d := D.host.hypOdd.2.1.pos
  obtain ⟨Λ, hΛ⟩ := hΛ
  have hSta : ∀ z ∈ St, IsAlgebraic ℚ z := by
    intro z hz
    simp only [St, Set.mem_iUnion, Set.mem_setOf_eq] at hz
    obtain ⟨i, j, s, ⟨h1, h2⟩, c, x, y, hx, hy, rfl⟩ := hz
    obtain ⟨x0, hx0, hx00, ha⟩ := hT i j s h1 h2 none
    obtain ⟨x1, hx1, -, hb⟩ := hT i j s h1 h2 (some c)
    rw [hx.2.unique hx0.2, hy.2.unique hx1.2]
    exact isAlgebraic_div_of_beta hd h1 _ Λ hx00 (ha Λ hΛ) (hb Λ hΛ)
  let S : Set ℂ := Sn ∪ St
  haveI : Finite S := (hSn.union hSt).to_subtype
  have hmem : ∀ z ∈ S, z ∈ Set.range (algebraMap (IntermediateField.adjoin ℚ S) ℂ) := fun z hz =>
    ⟨⟨z, IntermediateField.subset_adjoin ℚ S hz⟩, rfl⟩
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin fun z hz =>
    (Or.elim hz (hSa z) (hSta z)).isIntegral, ⟨fun h => ?_, fun i j s c x y h1 h2 hx hy => ?_⟩⟩
  · obtain ⟨δ, t0, b⟩ := hSb h
    exact ⟨δ, t0, fun ij => let ⟨P, P', a, b1, b2⟩ := b ij; ⟨P, P', a, hmem _ (Or.inl b1), hmem _ (Or.inl b2)⟩⟩
  · refine hmem _ (Or.inr ?_)
    simp only [St, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨i, j, s, ⟨h1, h2⟩, c, x, y, hx, hy, rfl⟩

end GlobalTheory.SqTop.SqField

namespace GlobalTheory.BigTop.Fun

end GlobalTheory.BigTop.Fun

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

theorem _root_.GlobalTheory.T.one_le_intersectionNumber_subvariety_through_positive : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → ∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → 1 ≤ interNumRed k Z (fun _ : Fin e => N) := by
  first | exact @GlobalTheory.PosThrough.one_le_interNumRed | exact GlobalTheory.PosThrough.one_le_interNumRed | (intros; apply GlobalTheory.PosThrough.one_le_interNumRed <;> assumption)
end

end

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.form_order_birational_pullback : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ (n : ℕ) (η : RatForms p n), η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (EtaleKlt.ratPull p s n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  first | exact @_root_.GlobalTheory.BirOrd.formOrd_ratPull_of_over | exact _root_.GlobalTheory.BirOrd.formOrd_ratPull_of_over | (intros; apply _root_.GlobalTheory.BirOrd.formOrd_ratPull_of_over <;> assumption)

end
end
