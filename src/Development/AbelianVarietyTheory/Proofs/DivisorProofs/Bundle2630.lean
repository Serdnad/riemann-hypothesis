module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle087
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2615
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FibreAbDim

theorem exists_isLieBasis_of_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X) {G' : Over (Sp R)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G x φ) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left))
    (hv : ∀ a, IsTanAtG t x (v a))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf : Fin n → R, IsCombAtG t x v cf w) :
    ∃ v' : Fin n → (epsR R ⟶ G'), IsLieBasis v' := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.HeckePoint.exists_ptsEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  obtain ⟨σ, hσ⟩ := GlobalTheory.HeckePoint.exists_ptsEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _)
  have h1 : η[G'].left ≫ φ = (1 : Over.mk x ⟶ t.G).left := by
    have := hσ 1
    rw [map_one] at this
    rw [this]
    congr 2
  have tan : ∀ w : epsR R ⟶ G', IsTangent w ↔ IsTanAtG t x (ρ w).left := by
    intro w
    constructor
    · intro hw
      refine ⟨Over.w (ρ w), ?_⟩
      rw [hρ, ← Category.assoc, hw, h1]
    · intro hw
      apply h.1.hom_ext
      · rw [Category.assoc, ← hρ, hw.2, h1]
      · rw [Category.assoc, Over.w w, Over.w η[G']]
        show spMap _ ≫ spMap _ = 𝟙 _
        unfold spMap
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
  let v' : Fin n → (epsR R ⟶ G') := fun a => ρ.symm (Over.homMk (v a) (hv a).1)
  have hv' : ∀ a, (v' a).left ≫ φ = v a := fun a => by
    rw [← hρ]
    simp [v']
  have comb : ∀ (c : Fin n → R) (w : epsR R ⟶ G'), IsLieComb c v' w ↔ IsCombAtG t x v c (ρ w).left := by
    intro c w
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun i => ρ (u i), fun i => ?_, ?_⟩
      · rw [hρ, hu, Category.assoc, hv']
        rfl
      · rw [map_list_prod, List.map_ofFn]
        rfl
    · rintro ⟨u, hu, e⟩
      refine ⟨fun i => ρ.symm (u i), fun i => ?_, ?_⟩
      · apply h.1.hom_ext
        · rw [← hρ, MulEquiv.apply_symm_apply, hu, Category.assoc, hv']
          rfl
        · rw [Category.assoc, Over.w, Over.w]
          show spMap _ = spMap _ ≫ spMap _
          unfold spMap
          rw [← Spec.map_comp]
          congr 1
          ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
      · apply ρ.injective
        rw [map_list_prod, List.map_ofFn]
        refine (Over.OverMorphism.ext ?_)
        rw [← e]
        congr 3
        funext i
        exact (ρ.apply_symm_apply (u i)).symm
  refine ⟨v', fun a => (tan _).2 ?_, fun w hw => ?_⟩
  · rw [hρ, hv']
    exact hv a
  · simpa only [comb] using hb _ ((tan w).1 hw)

theorem isAbelianScheme_and_relDim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (j : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) j → IsAbelianScheme A ∧ SmoothOfRelativeDimension n A.hom := by
  intro E _ _ _ H X t hp U n v hv hb m hm A _ j hj
  have hG := GlobalTheory.HeckePoint.isAbelianScheme_of_proper t hp
  have pullAb : ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'}
      [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left},
      IsAbelianScheme G → IsGrpPullback G' G f φ → IsAbelianScheme G' := by
    intro S S' f G G' _ _ φ hG h
    have := hG.comm
    have hc : IsCommMonObj G' := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hG.geomConnected⟩
  have hA := pullAb hG hj
  refine ⟨hA, ?_⟩
  have h₀ := isGrpPullback_pullback t.G (chart U)
  have hG' := pullAb hG h₀
  obtain ⟨v', hv'⟩ := exists_isLieBasis_of_frame t (chart U) h₀ v hv hb
  have w : j ≫ t.G.hom = (A.hom ≫ spMap (Ideal.Quotient.mk m)) ≫ chart U := by
    rw [hj.1.w, Category.assoc]
  have h₁ := IsGrpPullback.cancel h₀ (hj.congr rfl (h₀.1.lift_fst _ _ w).symm) (h₀.1.lift_snd _ _ w)
  have := hG'.comm
  have := hA.comm
  have := hG.comm
  obtain ⟨v₁, hv₁, -⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ _ _ A _ h₁ hG'.smooth n v' hv'
  have : IsLocalRing (Γ(X, U.1) ⧸ m) := by
    letI := Ideal.Quotient.field m
    infer_instance
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim _ A hA
  obtain ⟨v₂, hv₂⟩ := GlobalTheory.KeyPow.exists_isLieBasis A hg
  rw [GlobalTheory.KeyFramePoint.card_eq_of_isLieBasis hj hv₁ hv₂]
  exact hg

end GlobalTheory.FibreAbDim
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KltGlobal

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {n : ℕ}
  {Δ : X → ℚ} {η : RatForms p n} {x y : X} {m : ℕ} {g h : X.functionFieldˣ}

theorem compactSpace_of_isProjOver' {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Sp R}
    (hf : IsProjOver f) : CompactSpace Y := by
  obtain ⟨N, i, hi, rfl⟩ := hf
  have := isProper_str R N
  have : IsProper (i ≫ PSpace.str R N) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R N)

theorem unitAt_of_specializes' {z : X} {f : X.functionField} (hz : z ⤳ y) (hf : UnitAt y f) :
    UnitAt z f :=
  (unitAt_iff hf.ne_zero).2 ⟨regAt_of_specializes hz hf.regAt, regAt_of_specializes hz hf.inv.regAt⟩

theorem ord_eq_zero_of_unitAt' {E : DivOver p} {z : X} (hE : E.IsAt z) {u : X.functionFieldˣ}
    (hu : UnitAt z (u : X.functionField)) : E.ord u = 0 := by
  have h1 := (E.ord_nonneg_iff u).2 ((hE _).2 hu.regAt)
  have h2 := (E.ord_nonneg_iff u⁻¹).2 ((hE _).2 (by rw [Units.val_inv_eq_inv_val]; exact hu.inv.regAt))
  rw [E.ord_inv] at h2
  omega

theorem isLogEqn_pow' (hg : IsLogEqn p Δ η x m g) (r : ℕ) : IsLogEqn p Δ η x (m * r) (g ^ r) := by
  intro z hz E hE
  rw [E.ord_pow]
  push_cast
  rw [← hg z hz E hE]
  ring

theorem isLogEqn_of_unitAt' (hg : IsLogEqn p Δ η y m g)
    (hu : UnitAt y ((h : X.functionField) / g)) : IsLogEqn p Δ η y m h := by
  intro z hz E hE
  have h0 : E.ord (h * g⁻¹) = 0 := ord_eq_zero_of_unitAt' hE (by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv]
    exact unitAt_of_specializes' hz hu)
  have e : E.ord h = E.ord g := by
    have := E.ord_mul (h * g⁻¹) g
    rwa [inv_mul_cancel_right, h0, zero_add] at this
  rw [hg z hz E hE, e]

theorem unitAt_of_isLogEqn' [LocallyOfFiniteType p] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (hg : IsLogEqn p Δ η y m g) (hh : IsLogEqn p Δ η y m h) :
    UnitAt y ((h : X.functionField) / g) := by
  have h0 : ∀ z, z ⤳ y → ∀ F : DivOver p, F.IsAt z → F.ord (h * g⁻¹) = 0 := by
    intro z hz F hF
    have a := hg z hz F hF
    have b := hh z hz F hF
    rw [F.ord_mul, F.ord_inv]
    have : (F.ord g : ℚ) = F.ord h := a.symm.trans b
    have : F.ord g = F.ord h := by exact_mod_cast this
    omega
  have reg : ∀ v : X.functionFieldˣ, (∀ z, z ⤳ y → ∀ F : DivOver p, F.IsAt z → F.ord v = 0) →
      RegAt y (v : X.functionField) := fun v hv =>
    regAt_of_forall_coheight_eq_one fun z hz h1 =>
      have ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) h1
      (hF _).1 ((F.ord_nonneg_iff v).1 (hv z hz F hF).ge)
  have hne : (h : X.functionField) / g ≠ 0 := div_ne_zero h.ne_zero g.ne_zero
  have e1 : ((h * g⁻¹ : X.functionFieldˣ) : X.functionField) = h / g := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  have e2 : (((h * g⁻¹)⁻¹ : X.functionFieldˣ) : X.functionField) = ((h : X.functionField) / g)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, e1]
  refine (unitAt_iff hne).2 ⟨e1 ▸ reg _ h0, e2 ▸ reg _ fun z hz F hF => ?_⟩
  rw [F.ord_inv, h0 z hz F hF, neg_zero]

theorem exists_isLogEqn_of_form' [PerfectField k] [LocallyOfFiniteType p]
    (hn : topologicalKrullDim X = n) {η₀ : RatForms p n} (hη₀ : η₀ ≠ 0) (hη : η ≠ 0)
    (hg : IsLogEqn p Δ η x m g) : ∃ g' : X.functionFieldˣ, IsLogEqn p Δ η₀ x m g' := by
  by_cases hE : Nonempty (DivOver p)
  · obtain ⟨E⟩ := hE
    obtain ⟨ω, hω, f₀, e₀, -⟩ := E.isFormOrd_formOrd hn hη₀
    obtain ⟨f, e⟩ := (E.isFreeGen_toRat hω).2 η
    have hf : f ≠ 0 := fun h0 => hη (by rw [← e, h0]; exact zero_smul _ _)
    obtain ⟨c, hc⟩ : ∃ c : X.functionFieldˣ, η = (c : X.functionField) • η₀ :=
      ⟨Units.mk0 f hf * f₀⁻¹, by rw [e₀, smul_smul, ← e]; simp⟩
    refine ⟨g * (c ^ m)⁻¹, fun z hz F hF => ?_⟩
    have a := hg z hz F hF
    rw [hc, F.formOrd_smul hn hη₀] at a
    rw [F.ord_mul, F.ord_inv, F.ord_pow]
    push_cast at a ⊢
    linear_combination a
  · exact ⟨1, fun z _ F _ => (hE ⟨F⟩).elim⟩

theorem exists_nhds_isLogEqn' [IsLocallyNoetherian X] [CompactSpace X]
    (hfin : {z : X | ∃ E : DivOver p, E.IsAt z ∧ (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η ≠ 0}.Finite)
    (hΔ : (Function.support Δ).Finite) (hg : IsLogEqn p Δ η x m g) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, IsLogEqn p Δ η y m g := by
  set B : Set X := {z | ∃ E : DivOver p, E.IsAt z ∧ (m : ℚ) * (E.formOrd η + Δ z) ≠ E.ord g}
    with hB
  have hBf : B.Finite := by
    refine ((hfin.union hΔ).union (CartierDiv.principal g).finite_support_mult).subset ?_
    rintro z ⟨E, hE, hne⟩
    by_cases h1 : E.formOrd η = 0
    · by_cases h2 : Δ z = 0
      · right
        show (CartierDiv.principal g).mult z ≠ 0
        rw [(CartierDiv.isEqn_principal g z).mult_eq, ← hE.ord_eq]
        intro h3
        apply hne
        rw [h1, h2, h3]
        simp
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl ⟨E, hE, h1⟩)
  have key : ∀ y, y ∈ closure B → ∃ z ∈ B, z ⤳ y := by
    intro y hy
    have hc : closure B = ⋃ z ∈ B, closure {z} := by
      conv_lhs => rw [← Set.biUnion_of_singleton B]
      exact hBf.closure_biUnion _
    rw [hc] at hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨z, hz, hy⟩ := hy
    exact ⟨z, hz, specializes_iff_mem_closure.2 hy⟩
  refine ⟨⟨(closure B)ᶜ, isClosed_closure.isOpen_compl⟩, show x ∉ closure B from fun hx => ?_,
    fun y hy z hz E hE => ?_⟩
  · obtain ⟨z, ⟨E, hE, hne⟩, hzx⟩ := key x hx
    exact hne (hg z hzx E hE)
  · have hy' : y ∉ closure B := hy
    by_contra hne
    exact hy' (closure_mono (Set.singleton_subset_iff.2 (show z ∈ B from ⟨E, hE, hne⟩))
      (specializes_iff_mem_closure.1 hz))

end GlobalTheory.KltGlobal

namespace GlobalTheory.Discrepancy

open GlobalTheory.KltGlobal

theorem exists_isLogCanonicalMultiple_of_kltAt :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
      (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p →
      topologicalKrullDim X = n → ∀ Δ : X → ℚ, IsEffQDiv Δ → (∀ y, KltAt p n Δ y) →
      ∃ (m : ℕ) (G : CartierDiv X), 0 < m ∧ IsLogCanonicalMultiple p n Δ m G := by
  intro X _ _ _ p n hP hn Δ hΔ hklt
  classical
  haveI : CompactSpace X := compactSpace_of_isProjOver' hP
  haveI : LocallyOfFiniteType p := isProjOver_locallyOfFiniteType ℂ X p hP
  obtain ⟨η₀, -, -, hη₀, -, -, -⟩ := hklt (genericPoint X)
  have hfin := GlobalTheory.FormOrdFinite.finite_setOf_formOrd_ne_zero ℂ X p n hP hn η₀ hη₀
  have h1 : ∀ x, ∃ (m : ℕ) (g : X.functionFieldˣ) (U : X.Opens), 0 < m ∧ x ∈ U ∧
      ∀ y ∈ U, IsLogEqn p Δ η₀ y m g := by
    intro x
    obtain ⟨η, m, g, hη, hm, hg, -⟩ := hklt x
    obtain ⟨g', hg'⟩ := exists_isLogEqn_of_form' hn hη₀ hη hg
    obtain ⟨U, hU, hy⟩ := exists_nhds_isLogEqn' hfin hΔ.finite hg'
    exact ⟨m, g', U, hm, hU, hy⟩
  choose mm gg UU hm hU hy using h1
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (UU x : Set X))
    (fun x => (UU x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hU x⟩)
  set M := ∏ i ∈ t, mm i with hM
  have hM0 : 0 < M := Finset.prod_pos fun i _ => hm i
  have hMd : ∀ i ∈ t, mm i * (M / mm i) = M := fun i hi =>
    Nat.mul_div_cancel' (Finset.dvd_prod_of_mem _ hi)
  have sel : ∀ y : X, ∃ i ∈ t, y ∈ UU i := fun y => by
    have := ht (Set.mem_univ y)
    simpa using this
  choose s hs hsy using sel
  let e : X → X.functionFieldˣ := fun y => gg (s y) ^ (M / mm (s y))
  have he : ∀ y, ∀ w ∈ UU (s y), IsLogEqn p Δ η₀ w M (e y) := fun y w hw => by
    have := isLogEqn_pow' (hy (s y) w hw) (M / mm (s y))
    rwa [hMd _ (hs y)] at this
  let G : CartierDiv X := show cartierGroup X from
    ⟨fun y => germOf y (e y), fun x => ⟨UU (s x), hsy x, e x, fun y hy' =>
      germOf_eq_iff.2 (unitAt_of_isLogEqn' (he y y (hsy y)) (he x y hy'))⟩⟩
  refine ⟨M, G, hM0, η₀, hη₀, fun x g hg => ?_⟩
  have h0 : G.IsEqn x (e x) := rfl
  exact isLogEqn_of_unitAt' (he x x (hsy x)) (h0.iff_unitAt.1 hg)

end GlobalTheory.Discrepancy
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

theorem _root_.GlobalTheory.T.two_le_hermitianRank_and_hostDegree_eq : ∀ D : D7, 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f := by
  first | exact @GlobalTheory.RankHostFacts.main | exact GlobalTheory.RankHostFacts.main | (intros; apply GlobalTheory.RankHostFacts.main <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.MonoHom

variable {X : Type} [AddCommGroup X] {K : Type} [Field K]

def pform {ι : Type} (e : Module.Basis ι ℤ X) (i j : ι) : LinearMap.BilinForm ℤ X :=
  (e.coord i).smulRight (e.coord j)

@[simp] theorem pform_apply {ι : Type} (e : Module.Basis ι ℤ X) (i j : ι) (x y : X) :
    pform e i j x y = e.coord i x * e.coord j y := by
  simp [pform]

end GlobalTheory.MonoHom

namespace GlobalTheory.MonoHom

end GlobalTheory.MonoHom
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

namespace GlobalTheory

theorem latt_free_sub_full_rank {E : Type} [Field E] [NumberField E] (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    ∃ (f : (Fin (Module.finrank (𝓞 E) X) → 𝓞 E) →ₗ[𝓞 E] X) (m : ℕ), 0 < m ∧
      Function.Injective f ∧ ∀ x : X, m • x ∈ LinearMap.range f := by
  classical
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  set r := Module.finrank (𝓞 E) X
  obtain ⟨e, he⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := X) (le_refl r)
  let f : (Fin r → 𝓞 E) →ₗ[𝓞 E] X := Fintype.linearCombination (𝓞 E) e
  have hfv' : ∀ c : Fin r → 𝓞 E, f c = ∑ i, c i • e i := fun c => by
    simp [f, Fintype.linearCombination_apply]
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [hfv'] at hc
    exact funext ((Fintype.linearIndependent_iff.mp he) c hc)

  have key : ∀ x : X, ∃ n : ℕ, 0 < n ∧ n • x ∈ LinearMap.range f := by
    intro x
    have hdep : ¬ LinearIndependent (𝓞 E) (Fin.cons x e : Fin (r + 1) → X) := by
      intro h
      have := h.fintype_card_le_finrank
      simp [r] at this
    rw [Fintype.not_linearIndependent_iff] at hdep
    obtain ⟨g, hg, i, hi⟩ := hdep
    rw [Fin.sum_univ_succ] at hg
    simp only [Fin.cons_zero, Fin.cons_succ] at hg
    have ha : g 0 ≠ 0 := by
      intro h0
      rw [h0, zero_smul, zero_add] at hg
      have hz := (Fintype.linearIndependent_iff.mp he) (fun j => g j.succ) hg
      refine hi ?_
      refine Fin.cases h0 (fun j => hz j) i
    have hax : g 0 • x ∈ LinearMap.range f := by
      refine ⟨fun j => - g j.succ, ?_⟩
      rw [hfv']
      simp only [neg_smul, Finset.sum_neg_distrib]
      exact (neg_eq_of_add_eq_zero_left hg)
    have hI : Ideal.span {g 0} ≠ ⊥ := by simpa using ha
    have hN : Ideal.absNorm (Ideal.span {g 0}) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {g 0}))
    refine ⟨Ideal.absNorm (Ideal.span {g 0}), Nat.pos_of_ne_zero hN, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hb, mul_smul]
    exact Submodule.smul_mem _ _ hax
  choose N hNpos hNmem using key
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  refine ⟨f, ∏ s ∈ S, N s, Finset.prod_pos (fun s _ => hNpos s), hf, ?_⟩
  have hgen : ∀ s ∈ S, (∏ t ∈ S, N t) • s ∈ LinearMap.range f := by
    intro s hs
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem N hs
    rw [hk, mul_comm, mul_smul]
    exact AddSubmonoid.nsmul_mem (LinearMap.range f).toAddSubmonoid (hNmem s) k
  intro x
  have hx : x ∈ Submodule.span ℤ (S : Set X) := by rw [hS]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_comm]
    exact zsmul_mem hy a

end GlobalTheory
end
