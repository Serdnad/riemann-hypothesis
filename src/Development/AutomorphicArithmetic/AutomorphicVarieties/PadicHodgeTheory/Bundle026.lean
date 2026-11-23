module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle612
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle454
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle645
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocB
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem algPow_ne {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] (w : Plc F)
    (hh : (F →+* Qbar l) → ℤ) (x : (w.adicCompletion F)ˣ) : algPow w hh (x : w.adicCompletion F) ≠ 0 := by
  unfold algPow
  apply finprod_induction (fun z : Qbar l => z ≠ 0) one_ne_zero
  · intro a b ha hb
    exact mul_ne_zero ha hb
  · intro j
    exact zpow_ne_zero _ ((map_ne_zero _).mpr x.ne_zero)

private theorem algPow_mul {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] (w : Plc F)
    (hh : (F →+* Qbar l) → ℤ) (x y : w.adicCompletion F) : algPow w hh (x * y) = algPow w hh x * algPow w hh y := by
  haveI := finite_contEmb (l := l) w
  unfold algPow
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun j => by rw [map_mul, mul_zpow]

private noncomputable def algHom {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] (w : Plc F)
    (hh : (F →+* Qbar l) → ℤ) : (w.adicCompletion F)ˣ →* (Qbar l)ˣ :=
  MonoidHom.mk' (fun x => Units.mk0 _ (algPow_ne w hh x)) fun x y => Units.ext (algPow_mul w hh x y)

private theorem artin_unique (H : GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w}
    {a a' : Weil h →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) (ha' : IsLocalArtin h a') : a' = a := by
  obtain ⟨art, hart⟩ := H F Ω
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' F Ω art hart w
  exact MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)

private theorem part_iff (H : GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w)
    (ι : Qbar l ≃+* ℂ) (a : Weil h →* (w.adicCompletion F)ˣ) (ha : IsLocalArtin h a) (hh : (F →+* Qbar l) → ℤ)
    (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ω : (w.adicCompletion F)ˣ →* ℂˣ) (ho : OrdChar ι a ω hh ψ)
    (ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ) :
    IsWtPart h ψ (fun τ => hh (τ.1.comp (algebraMap F (w.adicCompletion F)))) ph ↔
      ∀ σ : ↥(Ine (F := F) A), ι (ph σ : Qbar l) = ((ω (a (ineIncl h σ)))⁻¹ : ℂˣ) := by
  have key : ∀ σ : Ine (F := F) A,
      ((ψ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) : Qbar l)) =
        ι.symm (ω (a (ineIncl h σ)) : ℂ) * algPow w (-hh) (a (ineIncl h σ) : w.adicCompletion F) :=
    fun σ => ho.val _ _ rfl (Set.mem_univ _)
  constructor
  · rintro ⟨-, hw⟩ σ
    have e := hw a ha σ
    rw [Units.val_mul, key σ] at e
    change _ = algPow w (-hh) _ at e
    have hP : algPow w (-hh) (a (ineIncl h σ) : w.adicCompletion F) ≠ 0 := algPow_ne w (-hh) _
    have e2 : ι.symm (ω (a (ineIncl h σ)) : ℂ) * (ph σ : Qbar l) = 1 := by
      apply mul_right_cancel₀ hP
      rw [one_mul]
      convert e using 1
      ring
    apply_fun ι at e2
    rw [map_mul, map_one, RingEquiv.apply_symm_apply] at e2
    rw [Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_right e2
  · intro hR
    refine ⟨?_, fun a' ha' σ => ?_⟩
    · have hker : (ph.ker : Set (Ine (F := F) A)) = (fun σ => a (ineIncl h σ)) ⁻¹' (ω.ker : Set _) := by
        ext σ
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage]
        constructor
        · intro h1
          have e := hR σ
          rw [h1, Units.val_one, map_one] at e
          exact inv_eq_one.mp (Units.val_eq_one.mp e.symm)
        · intro h1
          have e := hR σ
          rw [h1, inv_one, Units.val_one] at e
          exact Units.val_eq_one.mp (ι.injective (e.trans (map_one ι).symm))
      rw [hker]
      exact IsOpen.preimage ha.cont ho.smooth
    · rw [artin_unique H ha ha', Units.val_mul, key σ]
      change _ = algPow w (-hh) _
      have e := hR σ
      have hph : (ph σ : Qbar l) = ι.symm (((ω (a (ineIncl h σ)))⁻¹ : ℂˣ) : ℂ) := by
        rw [← e, RingEquiv.symm_apply_apply]
      rw [hph, Units.val_inv_eq_inv_val, map_inv₀]
      have hne : ι.symm (ω (a (ineIncl h σ)) : ℂ) ≠ 0 := by simp
      field_simp

theorem UpperTheory.V.Loc.ordCharIff :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (ι : Qbar l ≃+* ℂ) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ (hh : (F →+* Qbar l) → ℤ) (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), ((∃ ω, OrdChar ι a ω hh ψ) ↔ Continuous ψ ∧ IsLocAlg h ψ fun τ => hh (τ.1.comp (algebraMap F (w.adicCompletion F)))) ∧ ∀ ω, OrdChar ι a ω hh ψ → ∀ ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ, (IsWtPart h ψ (fun τ => hh (τ.1.comp (algebraMap F (w.adicCompletion F)))) ph ↔ ∀ σ : ↥(Ine (F := F) A), ι (ph σ : Qbar l) = ((ω (a (ineIncl h σ)))⁻¹ : ℂˣ)) := by
  intro H F Ω _ _ _ _ _ l _ A w h ι a ha hh ψ
  refine ⟨⟨fun ⟨ω, ho⟩ => ⟨ho.cont, ?_⟩, fun ⟨hc, ph, hph⟩ => ?_⟩,
    fun ω ho ph => part_iff H h ι a ha hh ψ ω ho ph⟩
  · let ph : Ine (F := F) A →* (Qbar l)ˣ :=
      (Units.map (ι.symm : ℂ →+* Qbar l).toMonoidHom).comp ((ω.comp (a.comp (ineIncl h)))⁻¹)
    refine ⟨ph, (part_iff H h ι a ha hh ψ ω ho ph).mpr fun σ => ?_⟩
    simp [ph]
  · let incl : Weil h →* Dec (F := F) A := Subgroup.inclusion (Weil_le_Dec h)
    let ξ : Weil h →* ℂˣ :=
      (Units.map (ι : Qbar l →+* ℂ).toMonoidHom).comp (ψ.comp incl * ((algHom w (-hh)).comp a)⁻¹)
    have hξ : ∀ s, ((ξ s : ℂˣ) : ℂ) =
        ι ((ψ (incl s) : Qbar l) / algPow w (-hh) (a s : w.adicCompletion F)) := by
      intro s
      simp [ξ, algHom, div_eq_mul_inv]
    have hsm : IsSmooth ξ := by
      have hset : {σ | ξ (ineIncl h σ) = 1} = (ph.ker : Set (Ine (F := F) A)) := by
        ext σ
        simp only [Set.mem_setOf_eq, SetLike.mem_coe, MonoidHom.mem_ker]
        have e := hph.2 a ha σ
        change ((ψ (incl (ineIncl h σ)) * ph σ : (Qbar l)ˣ) : Qbar l) =
          algPow w (-hh) (a (ineIncl h σ) : w.adicCompletion F) at e
        have hP := algPow_ne w (-hh) (a (ineIncl h σ))
        constructor
        · intro h1
          have h2 : (ψ (incl (ineIncl h σ)) : Qbar l) / algPow w (-hh) (a (ineIncl h σ) : w.adicCompletion F) = 1 := by
            apply ι.injective
            rw [← hξ, h1, Units.val_one, map_one]
          rw [div_eq_one_iff_eq hP] at h2
          rw [Units.val_mul, h2] at e
          apply Units.ext
          rw [Units.val_one]
          exact mul_left_cancel₀ hP (e.trans (mul_one _).symm)
        · intro h1
          rw [Units.val_mul, h1, Units.val_one, mul_one] at e
          apply Units.ext
          rw [Units.val_one, hξ, e, div_self hP, map_one]
      show IsOpen {σ | ξ (ineIncl h σ) = 1}
      rw [hset]
      exact hph.1
    obtain ⟨χ, hχs, hχ⟩ := ha.factor ξ hsm
    refine ⟨χ, ⟨hχs, hc, ?_⟩⟩
    intro s g hg _
    have hgs : g = incl s := Subtype.ext (by exact hg)
    subst hgs
    show (ψ (incl s) : Qbar l) = ι.symm (χ (a s) : ℂ) * algPow w (-hh) (a s : w.adicCompletion F)
    have hχa : χ (a s) = ξ s := by
      rw [hχ]
      rfl
    rw [hχa, hξ, RingEquiv.symm_apply_apply, div_mul_cancel₀ _ (algPow_ne w (-hh) (a s))]
end

section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

theorem UpperTheory.V.Loc.decJFacts :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l), IsOpenEmbedding ((MonoidHom.snd _ _).comp (UpperTheory.V.Af.decJ F j).subtype) ∧ IsEmbedding ((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype) ∧ ((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype).range = Dec (F := F) (placeJ j) := by
  intro F Ω _ _ _ _ _ _ l _ j
  haveI : IsAlgClosure ℚ Ω := Examples₂.LB.isAlgClosureQ F Ω
  have hj : ∀ x : Ω, x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := by
    intro x
    change (Valued.v : Valuation (Om l) NNReal) (j x) ≤ 1 ↔ _
    rw [← NNReal.coe_le_coe]
    exact Iff.rfl
  let e := Examples₂.LB.eDec (E := F) hj
  have he : Continuous e := Examples₂.LB.continuous_eDec hj
  have hes : Continuous e.symm := Examples₂.LB.continuous_eDec_symm hj
  have hc : ∀ g x, ((e g : _) : GQ l) (j x) = j ((g : G F Ω) x) := Examples₂.LB.eDec_comm hj
  have hK : ∀ x : ↥(UpperTheory.V.Af.decJ F j), x.1.2 ∈ (Examples₂.LB.KwF (E := F) j).fixingSubgroup := by
    intro x
    refine Examples₂.LB.mem_GK_of_fix j _ fun y => ?_
    have := x.2 (algebraMap F Ω y)
    rw [AlgEquiv.commutes] at this
    exact this
  have hfst : ∀ x : ↥(UpperTheory.V.Af.decJ F j), ((e.symm ⟨x.1.2, hK x⟩ : _) : G F Ω) = x.1.1 := by
    intro x
    refine AlgEquiv.ext fun y => j.injective ?_
    rw [← hc, MulEquiv.apply_symm_apply]
    exact x.2 y
  let h : ↥(UpperTheory.V.Af.decJ F j) ≃ₜ ↥(Examples₂.LB.KwF (E := F) j).fixingSubgroup :=
    { toFun := fun x => ⟨x.1.2, hK x⟩
      invFun := fun σ => ⟨(((e.symm σ : _) : G F Ω), σ.1), fun y => by
        have := hc (e.symm σ) y
        rw [MulEquiv.apply_symm_apply] at this
        exact this⟩
      left_inv := fun x => Subtype.ext (Prod.ext (hfst x) rfl)
      right_inv := fun σ => rfl
      continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := ((continuous_subtype_val.comp hes).prodMk continuous_subtype_val).subtype_mk _ }
  let e' : ↥(Examples₂.LB.KwF (E := F) j).fixingSubgroup ≃ₜ ↥(Dec (F := F) (placeJ j)) :=
    { toEquiv := e.symm.toEquiv, continuous_toFun := hes, continuous_invFun := he }
  have h1 : ⇑((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype) = Subtype.val ∘ (h.trans e') :=
    funext fun x => (hfst x).symm
  refine ⟨?_, ?_, ?_⟩
  · exact (IntermediateField.fixingSubgroup_isOpen (Examples₂.LB.KwF (E := F) j)).isOpenEmbedding_subtypeVal.comp
      h.isOpenEmbedding
  · rw [h1]
    exact IsEmbedding.subtypeVal.comp (h.trans e').isEmbedding
  · apply SetLike.coe_injective
    rw [MonoidHom.coe_range, h1, Set.range_comp, (h.trans e').surjective.range_eq, Set.image_univ, Subtype.range_coe_subtype]
    rfl
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem isCr_comp {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (c : G →* G)
    (hc : Function.Surjective c) (ρ : Representation A G V) :
    IsCr (φ.comp c) (ρ.comp c : Representation A G V) ↔ IsCr φ ρ := by
  have hr : (φ.comp c).range = φ.range := by
    ext σ
    refine ⟨fun ⟨g, hg⟩ => ⟨c g, hg⟩, fun ⟨g, hg⟩ => ?_⟩
    obtain ⟨g, rfl⟩ := hc g
    exact ⟨g, hg⟩
  have hd : Dcr (φ.comp c) (resCoef ℚ_[l] (ρ.comp c : Representation A G V)) = Dcr φ (resCoef ℚ_[l] ρ) := by
    unfold Dcr
    exact hc.iInf_comp (fun g => LinearMap.ker (actC φ (resCoef ℚ_[l] ρ) g - LinearMap.id))
  unfold IsCr
  rw [hr, hd]

private theorem conj_left {B : Type} [CommRing B] (w : GG (m := 3) (R := B)) (x y : GL (Fin 3) B)
    (h : GG.ofGL y = w * GG.ofGL x * w⁻¹) : y = w.left * sgnAct 3 B w.right x * w.left⁻¹ := by
  have := congrArg SemidirectProduct.left h
  have e : sgnAct 3 B w.right (sgnAct 3 B w.right w.left) = w.left := by
    rw [← MulAut.mul_apply, ← map_mul, Int.units_mul_self, map_one, MulAut.one_apply]
  simpa [e] using this

private theorem dot_inv {B : Type} [CommRing B] (a m : GL (Fin 3) B) (u x : Fin 3 → B) :
    dotProduct ((Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)).mulVec
      (((a * theta m * a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).mulVec u))
      ((m : Matrix (Fin 3) (Fin 3) B).mulVec x) =
    dotProduct ((Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)).mulVec u) x := by
  have e : Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) *
      ((a * theta m * a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) =
      ((m⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).transpose *
        (Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)) := by
    rw [Matrix.mul_assoc, ← Units.val_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, Units.val_mul,
      theta_val]
    simp only [← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec x, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem UpperTheory.conjugate_restriction_open_normal :
    ∀ {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (H : Subgroup (GQ l)) [H.Normal], IsOpen (H : Set (GQ l)) → ∀ (ρ ρ' : ↥H →* GL (Fin 3) B), Continuous (fun g => (ρ g : Matrix (Fin 3) (Fin 3) B)) → ∀ (s : GQ l) (w : GG (m := 3) (R := B)), (∀ g g' : H, (g' : GQ l) = s⁻¹ * g * s → GG.ofGL (ρ' g) = w * GG.ofGL (ρ g') * w⁻¹) → IsCr H.subtype (colRep ρ) → IsCr H.subtype (colRep ρ') := by
  intro l _ B _ _ _ _ _ _ H hN hH ρ ρ' hρ s w hw hcr
  have hψ : IsOpenEmbedding H.subtype := hH.isOpenEmbedding_subtypeVal
  let c : H →* H := (MulAut.conjNormal (H := H) s⁻¹).toMonoidHom
  have hc : ∀ g : H, (c g : GQ l) = s⁻¹ * g * s := fun g => by
    change ((MulAut.conjNormal (H := H) s⁻¹ g : H) : GQ l) = _
    rw [MulAut.conjNormal_apply, inv_inv]
  have hcc : Continuous c := by
    refine continuous_induced_rng.2 ?_
    have : Subtype.val ∘ c = fun g : H => s⁻¹ * (g : GQ l) * s := funext hc
    rw [this]
    fun_prop
  let σ : H →* GL (Fin 3) B := ρ.comp c
  have hσ : Continuous (fun g => (σ g : Matrix (Fin 3) (Fin 3) B)) := hρ.comp hcc
  have hσi : Continuous (fun g => (((σ g)⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)) := by
    simp only [← map_inv]
    exact hσ.comp continuous_inv
  have hσcr : IsCr H.subtype (colRep σ) := by
    have h1 := (isCr_comp H.subtype c (MulAut.conjNormal (H := H) s⁻¹).surjective (colRep ρ)).2 hcr
    have h2 : H.subtype.comp c = (MulAut.conj s⁻¹).toMonoidHom.comp H.subtype := by
      refine MonoidHom.ext fun g => ?_
      change (c g : GQ l) = s⁻¹ * g * s⁻¹⁻¹
      rw [hc, inv_inv]
    rw [h2] at h1
    exact (admissible_conjugate H.subtype hψ (colRep σ) s⁻¹).1.1 h1
  have he : ∀ g, ρ' g = w.left * sgnAct 3 B w.right (σ g) * w.left⁻¹ := fun g =>
    conj_left w _ _ (hw g (c g) (hc g))
  generalize w.left = a at he
  rcases Int.units_eq_one_or w.right with h | h
  · simp only [h, sgnAct_one] at he
    have hρ' : Continuous (fun g => (ρ' g : Matrix (Fin 3) (Fin 3) B)) := by
      simp only [he, Units.val_mul]
      exact (continuous_const.matrix_mul hσ).matrix_mul continuous_const
    refine ((isCrys_isDR_sub_quot H.subtype hψ (colRep σ) (colRep ρ') (contAction_colRep hσ) (contAction_colRep hρ')
      ((Matrix.toLin' (a : Matrix (Fin 3) (Fin 3) B)).restrictScalars ℚ_[l]) (fun g x => ?_)).2
      (fun v => ?_)).1 hσcr
    · simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, colRep_apply, Matrix.mulVec_mulVec, he,
        ← Units.val_mul, inv_mul_cancel_right]
    · refine ⟨((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).mulVec v, ?_⟩
      simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · simp only [h, sgnAct_neg_one] at he
    have hρ' : Continuous (fun g => (ρ' g : Matrix (Fin 3) (Fin 3) B)) := by
      simp only [he, Units.val_mul, theta_val]
      exact (continuous_const.matrix_mul ((continuous_const.matrix_mul hσi.matrix_transpose).matrix_mul
        continuous_const)).matrix_mul continuous_const
    have c1 : ContAction (chRep (1 : H →* Bˣ)) := contAction_chRep continuous_const
    have cr1 : IsCr H.subtype (chRep (1 : H →* Bˣ)) :=
      crUnr (A := ℚ_[l]) H.subtype hψ (resCoef ℚ_[l] (chRep (1 : H →* Bˣ))) c1 0
        (fun g _ x => by simp [resCoef, chRep])
    let N : Matrix (Fin 3) (Fin 3) B := Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)
    refine (isCrys_isDR_internalHom H.subtype hψ (colRep σ) (chRep (1 : H →* Bˣ)) (colRep ρ') (contAction_colRep hσ) c1
      (contAction_colRep hρ')
      (LinearMap.mk₂ ℚ_[l] (fun (u x : Fin 3 → B) => dotProduct (N.mulVec u) x)
        (fun _ _ _ => by rw [Matrix.mulVec_add, add_dotProduct])
        (fun _ _ _ => by rw [Matrix.mulVec_smul, smul_dotProduct])
        (fun _ _ _ => dotProduct_add _ _ _) (fun _ _ _ => dotProduct_smul _ _ _))
      (fun g u x => ?_) (fun u u' huu => ?_)).1 hσcr cr1
    · simp only [LinearMap.mk₂_apply, colRep_apply, chRep_apply, MonoidHom.one_apply, Units.val_one, one_mul]
      rw [he]
      exact dot_inv a (σ g) u x
    · have h1 : N.mulVec u = N.mulVec u' := by
        funext i
        have := LinearMap.congr_fun huu (Pi.single i 1)
        simpa only [LinearMap.mk₂_apply, dotProduct_single, mul_one] using this
      have h2 : ((a : Matrix (Fin 3) (Fin 3) B) * Jmat B 3) * N = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Jmat B 3), Jmat_mul_Jmat, Matrix.one_mul, Units.mul_inv]
      have h3 := congrArg ((a : Matrix (Fin 3) (Fin 3) B) * Jmat B 3).mulVec h1
      simpa only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] using h3
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

section Generic

open GlobalTheory.RegularRing GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module Qp V] [FiniteDimensional Qp V] [IsDomain B]

private theorem exists_inv_matrix (hf : FracInv PD) (hu : LineUnit PD) (ρ : Representation Qp G V) {d : ℕ}
    (v : Basis (Fin d) Qp V) (h : IsCrys PD ρ) :
    ∃ M M' : Matrix (Fin d) (Fin d) B, M * M' = 1 ∧
      ∀ g, (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) * M.map (PD.actB g) = M := by
  classical
  obtain ⟨h1, -⟩ := finite_le₀ PD hf ρ
  have h2 : finrank K₀ ↥(DcrisK₀ PD ρ) = d := by
    rw [(isCrys_iff_finrank PD ρ).1 h, finrank_eq_card_basis v, Fintype.card_fin]
  let d₀ := Module.finBasisOfFinrankEq K₀ ↥(DcrisK₀ PD ρ) h2
  let b := (Algebra.TensorProduct.basis B d₀).map
    (LinearEquiv.ofBijective _ (comparison_bijective PD hf hu ρ h))
  have hd : ∀ g i, sig PD ρ g (b i) = b i := by
    intro g i
    have : b i = (d₀ i : B ⊗[Qp] V) := by simp [b, comparison_tmul]
    rw [this]
    exact (mem_DcrisK₀ PD ρ _).1 (d₀ i).2 g
  let e := Algebra.TensorProduct.basis B v
  have hrep : ∀ g (w : B ⊗[Qp] V) k, e.repr (sig PD ρ g w) k =
      ∑ j, algebraMap Qp B (v.repr (ρ g (v j)) k) * PD.actB g (e.repr w j) := by
    intro g w k
    conv_lhs => rw [← e.sum_repr w]

    simp only [map_sum, sig_smul, map_smul, Finset.sum_apply', Finsupp.smul_apply,
    smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 1
    simp [e, sig_tmul, Algebra.algebraMap_eq_smul_one]
  refine ⟨e.toMatrix b, b.toMatrix e, Basis.toMatrix_mul_toMatrix_flip _ _, fun g => ?_⟩
  ext k i
  rw [Matrix.mul_apply]
  change _ = e.repr (b i) k
  conv_rhs => rw [← hd g i, hrep]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply]

private theorem exists_period_matrix (hf : FracInv PD) (hu : LineUnit PD) (ρ : Representation Qp G V) {d : ℕ}
    (v : Basis (Fin d) Qp V) (h : IsCrys PD ρ) :
    ∃ (M M' : Matrix (Fin d) (Fin d) B) (A : Matrix (Fin d) (Fin d) K₀), M * M' = 1 ∧ IsUnit A.det ∧
      M.map PD.φ = M * A.map (algebraMap K₀ B) ∧
      ∀ g, (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) * M.map (PD.actB g) = M := by
  obtain ⟨M, M', hM, hg⟩ := exists_inv_matrix PD hf hu ρ v h
  have hM' : M' * M = 1 := mul_eq_one_comm.1 hM
  have hinv : ∀ g, (M' * M.map PD.φ).map (PD.actB g) = M' * M.map PD.φ := by
    intro g
    set R := (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) with hR
    have h1 : M.map (PD.actB g) * M'.map (PD.actB g) = 1 := by
      rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : M'.map (PD.actB g) = M' * R := by
      have : R * (M.map (PD.actB g) * M'.map (PD.actB g)) = M * M'.map (PD.actB g) := by
        rw [← Matrix.mul_assoc, hg g]
      rw [h1, Matrix.mul_one] at this
      rw [this, ← Matrix.mul_assoc, hM', Matrix.one_mul]
    have h3 : R * (M.map PD.φ).map (PD.actB g) = M.map PD.φ := by
      have h4 : R.map PD.φ = R := by
        ext i j
        simp [hR]
      have h5 : (M.map PD.φ).map (PD.actB g) = (M.map (PD.actB g)).map PD.φ := by
        ext i j
        simp [PD.φ_comm]
      rw [h5, ← h4, ← Matrix.map_mul, hg g]
    rw [Matrix.map_mul, h2, Matrix.mul_assoc, h3]
  choose A hA using fun i j => PD.invB ((M' * M.map PD.φ) i j) fun g => congrFun (congrFun (hinv g) i) j
  have hA' : (Matrix.of A).map (algebraMap K₀ B) = M' * M.map PD.φ := by
    ext i j
    exact hA i j
  refine ⟨M, M', Matrix.of A, hM, ?_, by rw [hA', ← Matrix.mul_assoc, hM, Matrix.one_mul], hg⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have h1 : ((Matrix.of A).map (algebraMap K₀ B)).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have h2 : (M' * M.map PD.φ) * (M'.map PD.φ * M) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (M.map PD.φ), ← Matrix.map_mul, hM,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, hM']
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, ← hA', h1, zero_mul, Matrix.det_one] at h3
  exact zero_ne_one h3

end Generic

theorem UpperTheory.exists_crystalline_period_matrix_bcris_of_isCrys :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) {d : ℕ} (e : Basis (Fin d) ℚ_[l] V), IsCrys ((PP l).PD K) ρ → ∃ (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (A : Matrix (Fin d) (Fin d) ↥(K0 K)), M * M' = 1 ∧ IsUnit A.det ∧ M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l)) ∧ (∀ g : ↥(GK K), (LinearMap.toMatrix e e (ρ g)).map (algebraMap ℚ_[l] (Bcr l)) * M.map ((PP l).actQ (g : GQ l)) = M) := by
  intro l _ K V _ _ _ ρ d e h
  obtain ⟨T⟩ := tiedP l
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  obtain ⟨M, M', A, h1, h2, h3, h4⟩ := exists_period_matrix ((PP l).PD K)
    (GlobalTheory.TateDualCrys.fracInv_of_tied T K) (GlobalTheory.TateDualCrys.lineUnit_of_tied T K) ρ e h
  refine ⟨M, M', A, h1, h2, ?_, fun g => ?_⟩
  · rw [← h3]
    ext i j
    exact ((PP l).PD_φ K _).symm
  · have h5 : M.map ((PP l).actQ (g : GQ l)) = M.map (((PP l).PD K).actB g) := by
      ext i j
      exact ((PP l).PD_actB K g _).symm
    rw [h5, h4]
end
