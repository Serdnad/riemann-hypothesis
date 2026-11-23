module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2161
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle245
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.CrysLift

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def diagSec (X : Scheme.{0}) : AffOp X ⥤ (Pair (𝟙 X))ᵒᵖ :=
  (Monotone.functor (f := fun U : X.affineOpens ↦ (⟨(U, U), by simp⟩ : Pair (𝟙 X))) fun _ _ h ↦
      Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨h, h⟩)).op

def diagCoef (s : X ⟶ Sp R) : CoefMap (RingHom.id R) (OPair (𝟙 X) s) (OAff s) where
  G := diagSec X
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem diag_res_degree_one (s : X ⟶ Sp R) (c : HH1 s) :
    pullHyp1 (diagCoef s) (pullHyp1 (pairRes (𝟙 X) s) c) = c := by
  rw [← pullHyp1_comp]
  exact (pullHyp1_eq_of_natTrans _ (CoefMap.id _) { app U := 𝟙 U }
    (fun U b ↦ mp_id (OAff s) U b) c).trans (pullHyp1_id c)

theorem diag_res_degree_two (s : X ⟶ Sp R) (c : HH2 s) :
    pullHyp2 (diagCoef s) (pullHyp2 (pairRes (𝟙 X) s) c) = c := by
  rw [← pullHyp2_comp]
  exact (pullHyp2_eq_of_natTrans _ (CoefMap.id _) { app U := 𝟙 U }
    (fun U b ↦ mp_id (OAff s) U b) c).trans (pullHyp2_id c)

theorem eq_of_isPull1 {s : X ⟶ Sp R} (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) {c c' : HH1 s}
    (e : IsPull1 h c c') : c = c' := by
  have e' : pullHyp1 (pairRes (𝟙 X) s) c = pullHyp1 (pairRes (𝟙 X) s) c' :=
    (isPull1_id h c).symm.trans e
  rw [← diag_res_degree_one s c, e', diag_res_degree_one]

theorem eq_of_isPull2 {s : X ⟶ Sp R} (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) {c c' : HH2 s}
    (e : IsPull2 h c c') : c = c' := by
  have e' : pullHyp2 (pairRes (𝟙 X) s) c = pullHyp2 (pairRes (𝟙 X) s) c' :=
    (isPull2_id h c).symm.trans e
  rw [← diag_res_degree_two s c, e', diag_res_degree_two]

theorem red_of {R₀ : Type} [CommRing R₀] {I : Ideal R} {π : R →+* R₀} (hπ : Function.Surjective π)
    (hI : RingHom.ker π = I) {X₀ : Scheme.{0}} {s : X ⟶ Sp R} {s₀ : X₀ ⟶ Sp R₀} {i : X₀ ⟶ X}
    (hp : IsPullback i s₀ s (spMap π)) :
    ∃ s₀' : X₀ ⟶ Sp (R ⧸ I), IsPullback i s₀' s (spMap (Ideal.Quotient.mk I)) ∧
      s₀ ≫ spMap π = s₀' ≫ spMap (Ideal.Quotient.mk I) := by
  subst hI
  let e := RingHom.quotientKerEquivOfSurjective hπ
  have he : (e : R ⧸ RingHom.ker π →+* R₀).comp (Ideal.Quotient.mk _) = π := RingHom.ext fun _ ↦ rfl
  have hs : spMap π = spMap (e : R ⧸ RingHom.ker π →+* R₀) ≫ spMap (Ideal.Quotient.mk _) := by
    conv_lhs => rw [← he]
    show Spec.map _ = Spec.map _ ≫ Spec.map _; rw [← Spec.map_comp]; rfl
  have : IsIso (CommRingCat.ofHom (e : R ⧸ RingHom.ker π →+* R₀)) := e.toCommRingCatIso.isIso_hom
  refine ⟨s₀ ≫ spMap (e : R ⧸ RingHom.ker π →+* R₀), ?_, by rw [hs, Category.assoc]⟩
  exact hp.of_iso (Iso.refl _) (Iso.refl _) (asIso (spMap (e : R ⧸ RingHom.ker π →+* R₀))) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp [hs])

end GlobalTheory.CrysLift

namespace GlobalTheory.CrysLift

open GlobalTheory.SmoothLift

theorem crystallineDeRham_of_smoothLift : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.CrystallineDeRham := by
  rintro ⟨e₁, e₂, -, -, hnat⟩ R _ I κ hκ R₀ _ π hπ hI X X₀ s s₀ i hs hsep hqc hp m
  have hid : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
  have : IsIso (spMap (RingHom.id R)) := by rw [hid]; infer_instance
  let D : Data :=
    { R := R, I := ⊥, κ := dp0 R, nil := isDPNilpotent_bot R, X := X, X₀ := X, s := s, t := s, i := 𝟙 X,
      smooth := hs, sep := hsep, qc := hqc,
      red := by
        obtain ⟨s', h1, h2⟩ := red_of (π := RingHom.id R) Function.surjective_id
          ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id)
          (IsPullback.of_horiz_isIso (fst := 𝟙 X) (g := spMap (RingHom.id R)) (snd := s) (f := s)
            ⟨by rw [show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.comp_id]⟩)
        refine ⟨s', h1, ?_⟩
        rw [← h2, show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.comp_id] }
  let D' : Data :=
    { R := R, I := I, κ := κ, nil := hκ, X := X, X₀ := X₀, s := s, t := s₀ ≫ spMap π, i := i,
      smooth := hs, sep := hsep, qc := hqc,
      red := by
        obtain ⟨s', h1, h2⟩ := red_of hπ hI hp
        exact ⟨s', h1, h2⟩ }
  have h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R) := by
    rw [show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.comp_id]
  obtain ⟨h1, h2⟩ := hnat D D' (RingHom.id R) (𝟙 X) i h m (by simp [D, D'])
  have k1 : ∀ c, m.pull1 c = ((e₁ D).trans (e₁ D').symm) c := fun c ↦
    ((e₁ D').symm_apply_apply _).symm.trans (congrArg (e₁ D').symm (eq_of_isPull1 h (h1 c)).symm)
  have k2 : ∀ c, m.pull2 c = ((e₂ D).trans (e₂ D').symm) c := fun c ↦
    ((e₂ D').symm_apply_apply _).symm.trans (congrArg (e₂ D').symm (eq_of_isPull2 h (h2 c)).symm)
  exact ⟨(funext k1 : (⇑m.pull1 : _ → _) = _) ▸ ((e₁ D).trans (e₁ D').symm).bijective,
    (funext k2 : (⇑m.pull2 : _ → _) = _) ▸ ((e₂ D).trans (e₂ D').symm).bijective⟩

end GlobalTheory.CrysLift
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BirigidHom

theorem exists_hom_of_triv : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B],
    IsAbelianScheme A → IsAbelianScheme B → ∀ (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ →
    ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    ∃ l : A ⟶ B, IsMonHom l ∧ LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) := by
  intro k _ A B _ _ _ hA hB P₀ hd P hP h₁ h₂
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k A hA
  let AV : GlobalTheory.AV.AbVar k := { X := A, ab := hA, dim := g, smooth := hg }
  obtain ⟨c, L, hL, hamp, -⟩ := GlobalTheory.AV.exists_isAmpleCls k AV
  obtain ⟨H, hH, aH⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod (A := A) (B := A) hA hA hL hamp hL hamp
  obtain ⟨a₁, -⟩ := GlobalTheory.BirigidLift.additive_of_triv hA hA hH aH hP h₁ h₂
  obtain ⟨x, hx, -⟩ := hd.univ A P hP a₁
  have hE : (ev P₀ (fst A A) (snd A A ≫ x)).IsLB := pull_isLB hd.isLB _
  have e : cls P hP = evc hd.isLB (fst A A) (snd A A ≫ x) := (cls_eq_iff hP hE).2 hx
  refine ⟨x, GlobalTheory.rigidity_holds (Sp k) A B hA hB x ?_, hx⟩
  apply hd.eq_one
  rw [triv_ev_iff hd.isLB, ← Category.assoc, ← GlobalTheory.BirigidLift.evc_of_cls hd.isLB hP e]
  have u1 : snd A (𝟙_ (Over (Sp k))) ≫ (η : 𝟙_ (Over (Sp k)) ⟶ A) = 1 := by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A (𝟙_ (Over (Sp k)))) (toUnit _)]
  rw [u1]
  exact evc_one_right hP h₂ _

end GlobalTheory.BirigidHom
end
end

section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem galTate_eq_one_of_embedding {K Ω Ω' : Type} [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω']
    (j : Ω →ₐ[K] Ω') (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (l : ℕ) [Fact l.Prime]
    (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[K] Ω') (h : ∀ x, σ' (j x) = j (σ x)) (h1 : galTate A l σ' = 1) :
    galTate A l σ = 1 := by
  obtain ⟨f, hf, hc⟩ := GlobalTheory.T.exists_injective_points_larger_field_galois K Ω Ω' j A
  refine LinearMap.ext fun t => Tate.ext fun n => hf ?_
  have e := congrArg (fun u => u.lev n) (LinearMap.congr_fun h1 (Tate.map l f t))
  exact (hc σ σ' h (t.lev n)).trans e

theorem finite_image_inertia_of_goodReduction_baseChange (h : NeronOggShafarevichSt) (R K Ω : Type) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω)
    (hV : IsAbove R K V.toSubring) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (l : ℕ) [Fact l.Prime] (hl : (l : ResidueField R) ≠ 0)
    (L W Ω' : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Algebra W L] [IsFractionRing W L] [Field Ω'] [Algebra L Ω'] [IsSepClosure L Ω']
    [Algebra K Ω'] [IsScalarTower K L Ω'] (hW : IsAbove R K (algebraMap W L).range)
    (hg : HasGoodReduction W L ((Over.pullback (spMap (algebraMap K L))).obj A)) :
    (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite := by
  haveI : IsSepClosed Ω' := IsSepClosure.sep_closed L
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  haveI : IsGalois K Ω := inferInstance
  let j : Ω →ₐ[K] Ω' := IsSepClosed.lift
  obtain ⟨V', hV'⟩ := exists_isAbove W L Ω'
  obtain ⟨hp, hm⟩ := GlobalTheory.T.residue_perfect_and_char_alt R K L W hW
  obtain ⟨hAL, hc⟩ := GlobalTheory.T.isAbelianScheme_and_comm_baseChange_field K L A hA
  have hT := (h.iff_tateUnramified hV' hAL l (hm l hl)).1 hg
  have hV'' : IsAbove R K (V'.comap (j : Ω →+* Ω')).toSubring := by
    unfold IsAbove at hW hV' ⊢
    rw [← hW, ← hV']
    ext x
    change j (algebraMap K Ω x) ∈ V' ↔ algebraMap L Ω' (algebraMap K L x) ∈ V'
    rw [j.commutes, ← IsScalarTower.algebraMap_apply]
  obtain ⟨H, hH, hext⟩ := GlobalTheory.T.exists_finiteIndex_subgroup_aut_extend_sepClosure K L Ω Ω' j
  obtain ⟨g, hgV⟩ := GlobalTheory.T.exists_galois_smul_eq_valuationSubring_over_dvr R K Ω V _ hV hV''
  have key : ∀ σ ∈ inertia K (V'.comap (j : Ω →+* Ω')), σ ∈ H → galTate A l σ = 1 := by
    intro σ hσ hσH
    obtain ⟨σ', hσ'⟩ := hext σ hσH
    have h1 := GlobalTheory.T.inertia_lift_of_purelyInseparable_alt K L Ω Ω' j (GlobalTheory.T.sepClosure_exists_pow_mem_range_of_finiteDimensional K L Ω Ω' j) V' σ σ' hσ' hσ
    have h2 := (GlobalTheory.T.galoisRepresentationTateModule_baseChange_eq_one_iff K L Ω' A l σ').1 (hT σ' h1)
    exact galTate_eq_one_of_embedding j A l σ (σ'.restrictScalars K) hσ' h2
  refine GlobalTheory.T.finite_image_of_map_eq_one_on_inf_finiteIndex' _ _ (galTate A l) (inertia K V) (H.comap (MulAut.conj g).toMonoidHom) ?_ ?_
  · constructor
    rw [Subgroup.index_comap_of_surjective _ (MulAut.conj g).surjective]
    exact hH.index_ne_zero
  · intro σ hσ hσH
    have h1 := key (g * σ * g⁻¹) (hgV ▸ GlobalTheory.T.inertia_conj_mem_smul' K Ω V g σ hσ) hσH
    have e : σ = g⁻¹ * (g * σ * g⁻¹) * g := by group
    rw [e, map_mul, map_mul, h1, _root_.mul_one, ← map_mul, inv_mul_cancel, map_one]

theorem finite_image_inertia_of_potentialGoodReduction : NeronOggShafarevichSt → ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → HasPotentialGoodReduction R K A → (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite := by
  intro h R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA l _ hl hP
  obtain ⟨L, W, _, _, _, _, _, _, _, _, hW, hg⟩ := hP
  exact finite_image_inertia_of_goodReduction_baseChange h R K Ω V hV A hA l hl L W (SeparableClosure L) hW hg

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InertiaFixedUniformizer

theorem valuation_uniformizer_lt_one {R K Ω : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring)
    {π : R} (hπ : Irreducible π) : V.valuation (algebraMap K Ω (algebraMap R K π)) < 1 := by
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero
  have hle : V.valuation (algebraMap K Ω (algebraMap R K π)) ≤ 1 := by
    rw [V.valuation_le_one_iff]
    have : algebraMap R K π ∈ (V.toSubring).comap (algebraMap K Ω) := by
      rw [hV]; exact ⟨π, rfl⟩
    exact this
  refine lt_of_le_of_ne hle fun h1 => hπ.not_isUnit ?_
  have hinv : (algebraMap R K π)⁻¹ ∈ (V.toSubring).comap (algebraMap K Ω) := by
    change algebraMap K Ω (algebraMap R K π)⁻¹ ∈ V
    rw [← V.valuation_le_one_iff, map_inv₀, map_inv₀, h1, inv_one]
  rw [hV] at hinv
  obtain ⟨u, hu⟩ := hinv
  refine IsUnit.of_mul_eq_one u (IsFractionRing.injective R K ?_)
  rw [map_mul, hu, mul_inv_cancel₀ hπ0, map_one]

theorem uniformizer_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π →
    V.valuation (algebraMap K Ω (algebraMap R K π)) < 1 ∧
      ∀ y : IntermediateField.fixedField (inertia K V), V.valuation (y : Ω) < 1 →
        ∃ z : IntermediateField.fixedField (inertia K V), (z : Ω) ∈ V ∧
          y = algebraMap K _ (algebraMap R K π) * z := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV π hπ
  refine ⟨valuation_uniformizer_lt_one V hV hπ, fun y hy => ?_⟩
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero
  have hmem := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (y : Ω) y.2
    ((ValuationSubring.mem_nonunits_iff _).2 hy)
  refine ⟨y / algebraMap K _ (algebraMap R K π), ?_, ?_⟩
  · simpa using hmem
  · rw [mul_div_cancel₀]
    exact (map_ne_zero _).2 hπ0

end GlobalTheory.InertiaFixedUniformizer
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InertiaFixedDVR

theorem isDiscreteValuationRing_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    IsDiscreteValuationRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  classical
  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set W := V.comap (algebraMap K' Ω) with hW
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  set c : Ω := algebraMap K Ω (algebraMap R K π) with hc
  have hπK : algebraMap R K π ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
  have hc0 : c ≠ 0 := (map_ne_zero _).2 hπK
  have hcV : c ∈ V := by
    have h : algebraMap R K π ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨π, rfl⟩
    exact h
  have hcinv : c⁻¹ ∉ V := by
    intro h
    have h' : (algebraMap R K π)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω (algebraMap R K π)⁻¹ ∈ V
      rw [map_inv₀]; exact h
    rw [hV] at h'
    obtain ⟨r, hr⟩ := h'
    apply hπ.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨r, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr, map_one, mul_inv_cancel₀ hπK]
  have hcK' : c ∈ K' := K'.algebraMap_mem _

  let j : W → Ω := fun w => ((w : K') : Ω)
  have hjinj : Function.Injective j := fun a b h => Subtype.ext (Subtype.ext h)
  have hjV : ∀ w : W, j w ∈ V := fun w => w.2
  have hjK : ∀ w : W, j w ∈ K' := fun w => (w : K').2
  have hj_mul : ∀ a b : W, j (a * b) = j a * j b := fun _ _ => rfl
  have hj_zero : j 0 = 0 := rfl
  have hj_one : j 1 = 1 := rfl
  have hj_pow : ∀ (a : W) (n : ℕ), j (a ^ n) = j a ^ n := by
    intro a n
    induction n with
    | zero => simpa using hj_one
    | succ n ih => rw [pow_succ, hj_mul, ih, pow_succ]
  let mk : (y : Ω) → y ∈ K' → y ∈ V → W := fun y h1 h2 => ⟨⟨y, h1⟩, h2⟩
  have hunit : ∀ w : W, j w ≠ 0 → (j w)⁻¹ ∈ V → IsUnit w := by
    intro w h0 hinv
    refine isUnit_iff_exists_inv.2 ⟨mk (j w)⁻¹ (K'.inv_mem (hjK w)) hinv, hjinj ?_⟩
    rw [hj_mul, hj_one]
    exact mul_inv_cancel₀ h0
  have hdvd : ∀ w : W, ¬ IsUnit w → ∃ u : W, w = mk c hcK' hcV * u := by
    intro w hw
    have hnu : j w ∈ V.nonunits := by
      rw [GlobalTheory.FixInertUnram.mem_nonunits_iff']
      by_cases h0 : j w = 0
      · exact Or.inl h0
      · exact Or.inr fun h => hw (hunit w h0 h)
    have hq := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (j w) (hjK w) hnu
    refine ⟨mk (j w / c) (K'.div_mem (hjK w) hcK') hq, hjinj ?_⟩
    rw [hj_mul]
    change j w = c * (j w / c)
    field_simp
  set ϖ : W := mk c hcK' hcV with hϖ
  have hϖnu : ¬ IsUnit ϖ := by
    intro h
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.1 h
    apply hcinv
    have e : c * j v = 1 := by
      have := congrArg j hv
      rw [hj_mul, hj_one] at this
      exact this
    rw [inv_eq_of_mul_eq_one_right e]
    exact hjV v
  have hϖ0 : ϖ ≠ 0 := fun h => hc0 (by have := congrArg j h; rw [hj_zero] at this; exact this)
  have hirr : Irreducible ϖ := by
    refine ⟨hϖnu, fun a b hab => ?_⟩
    by_contra hne
    push_neg at hne
    obtain ⟨a', rfl⟩ := hdvd a hne.1
    obtain ⟨b', rfl⟩ := hdvd b hne.2
    apply hϖnu
    have e : ϖ * 1 = ϖ * (ϖ * (a' * b')) := by
      rw [_root_.mul_one]
      calc ϖ = ϖ * a' * (ϖ * b') := hab
        _ = ϖ * (ϖ * (a' * b')) := by ring
    have h1 := mul_left_cancel₀ hϖ0 e
    exact isUnit_iff_exists_inv.2 ⟨a' * b', h1.symm⟩
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨ϖ, hirr, fun {x} hx => ?_⟩
  have hx0 : j x ≠ 0 := fun h => hx (hjinj (h.trans hj_zero.symm))
  have hex : ∃ n : ℕ, j x / c ^ n ∉ V := GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ (j x) hx0
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, j x / c ^ n ∉ V ∧ ∀ k < n, j x / c ^ k ∈ V :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => by simpa using Nat.find_min hex hk⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hn
    rw [pow_zero, div_one]
    exact hjV x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmV : j x / c ^ m ∈ V := hmin m (by omega)
  have hyK : j x / c ^ m ∈ K' := K'.div_mem (hjK x) (pow_mem hcK' m)
  have hy0 : j x / c ^ m ≠ 0 := div_ne_zero hx0 (pow_ne_zero _ hc0)
  have hyinv : (j x / c ^ m)⁻¹ ∈ V := by
    by_contra hyi
    have hq := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (j x / c ^ m) hyK
      ((GlobalTheory.FixInertUnram.mem_nonunits_iff' V _).2 (Or.inr hyi))
    apply hn
    rw [pow_succ, ← div_div]
    exact hq
  have hu : IsUnit (mk (j x / c ^ m) hyK hmV) := hunit _ hy0 hyinv
  refine ⟨m, hu.unit, hjinj ?_⟩
  rw [IsUnit.unit_spec, hj_mul, hj_pow]
  change c ^ m * (j x / c ^ m) = j x
  field_simp

end GlobalTheory.InertiaFixedDVR
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem cuspForm_isSqInt_and_isDiscrete :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
      (∀ φ : Sm E a, IsCuspForm φ → (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) → IsSqInt φ.1) ∧
        ∀ x : CuspSub E a, IsNormalised x → IsDiscrete x.V := by
  intro E _ _ _ a
  have hB : CuspFormsBoundedGL :=
    GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay
      (GlobalTheory.cuspRapidDecaySiegelGL_of_finite GlobalTheory.automorphicFormsFiniteGL)
  have h1 : ∀ φ : Sm E a, IsCuspForm φ → (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) → IsSqInt φ.1 :=
    fun φ hφ h' =>
      have hC := hB.of_invariant hφ h'
      GlobalTheory.DiscChar.isSqInt_of_bounded h' (C := hC.choose) hC.choose_spec
  exact ⟨h1, fun x hx => ⟨fun φ hφ => (x.cusp φ hφ).1, fun φ hφ => h1 φ (x.cusp φ hφ) (hx φ hφ), x.stable, x.ne_bot,
    x.irred⟩⟩

end GlobalTheory.ResW

end
end
