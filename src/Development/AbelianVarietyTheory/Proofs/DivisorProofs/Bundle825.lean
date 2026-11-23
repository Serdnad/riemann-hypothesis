module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle794
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle796
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546

@[expose] public section

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped ENNReal NNReal

namespace GlobalTheory.KSp

theorem weil_representation_preserves_L2 : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (μ' : Measure (Matrix α ν E)) [μ'.IsAddHaarMeasure] (g : UG c (stdJ ν E)) (φ : SB (Matrix α ν E)), ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _ κ ω hKW μ' _ g φ
  obtain ⟨hfd, htr, hinv, ht2, hc, hn, htrc, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨hmt, hgood⟩ := hmat α ν
  haveI := hfd
  haveI := hmt
  haveI := hgood.grp
  haveI := hgood.t2
  haveI := hgood.lc
  haveI := hgood.sc
  let N : SB (Matrix α ν E) → ℝ≥0∞ := fun f => ∫⁻ x, ‖(f : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ
  let U : Subgroup (UG c (stdJ ν E)) :=
    { carrier := {g | ∀ φ, N (ω g φ) = N φ}
      one_mem' := by intro φ; simp
      mul_mem' := by
        intro g h hg hh φ
        show N (ω (g * h) φ) = N φ
        rw [map_mul, Module.End.mul_apply, hg, hh]
      inv_mem' := by
        intro g hg φ
        have := hg (ω g⁻¹ φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        exact this.symm }
  have hsieg : sieg c ν ≤ U := by
    intro p hp φ
    show N (ω p φ) = N φ
    simp only [N]
    rw [hKW.par p hp φ]
    exact GlobalTheory.T.lintegral_sq_siegelParabolicOperator_eq F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ p hp φ
  obtain ⟨β, hβ, hβs, hβn, -, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  have hpair : IsPair (fun x y : Matrix α ν E => ψ (pr c Q x y)) := by
    have := GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F (Matrix α ν E) ψ hψ hψ1 hψne β hβs hβn
    simpa only [hβ] using this
  obtain ⟨C, hC, hfi⟩ := GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect (Matrix α ν E) hgood μ _ hpair
  have hpl := GlobalTheory.T.lintegral_four_sq_eq_mul_of_inversion (Matrix α ν E) hgood μ _ hpair C hC hfi
  have hw : ∀ φ : SB (Matrix α ν E), N (ω (weyl c ν) φ) = (‖κ‖ₑ ^ 2 * ENNReal.ofReal C) * N φ := by
    intro φ
    simp only [N]
    rw [hKW.wey φ]
    simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
    rw [lintegral_const_mul' _ _ (by simp), fou, hpl _ φ.2, mul_assoc]
  have hww : weyl c ν * weyl c ν ∈ sieg c ν := by
    rw [mem_sieg]
    show ((stdJ ν E) * (stdJ ν E)).toBlocks₂₁ = 0
    rw [stdJ_mul_stdJ]
    ext i j
    simp [toBlocks₂₁]
  obtain ⟨L, hLc, hLo, -⟩ := hgood.large ∅ isCompact_empty
  have hmem : (L : Set (Matrix α ν E)).indicator (1 : Matrix α ν E → ℂ) ∈ SB (Matrix α ν E) := by
    refine ⟨?_, ?_⟩
    · have hcl : IsClopen (L : Set (Matrix α ν E)) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
      exact (LocallyConstant.charFn ℂ hcl).isLocallyConstant
    · exact HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  set φ₀ : SB (Matrix α ν E) := ⟨_, hmem⟩ with hφ₀
  have hN0 : N φ₀ = μ L := by
    simp only [N, hφ₀]
    have e : (fun x => ‖(L : Set (Matrix α ν E)).indicator (1 : Matrix α ν E → ℂ) x‖ₑ ^ 2) =
        (L : Set (Matrix α ν E)).indicator 1 := by
      funext x
      by_cases hx : x ∈ (L : Set (Matrix α ν E)) <;> simp [hx]
    rw [e, lintegral_indicator_one hLo.measurableSet]
  have hpos : μ L ≠ 0 := (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne'
  have hfin : μ L ≠ ∞ := hLc.measure_lt_top.ne
  set k : ℝ≥0∞ := ‖κ‖ₑ ^ 2 * ENNReal.ofReal C with hk
  have hkk : k * k = 1 := by
    have h1 : N (ω (weyl c ν * weyl c ν) φ₀) = N φ₀ := hsieg hww φ₀
    rw [map_mul, Module.End.mul_apply, hw, hw, ← mul_assoc, hN0] at h1
    have h2 := congrArg (· / μ L) h1
    simpa [ENNReal.mul_div_cancel_right hpos hfin, ENNReal.div_self hpos hfin] using h2
  have hk1 : k = 1 := by
    rcases lt_trichotomy k 1 with h | h | h
    · have : k * k ≤ k * 1 := by gcongr
      rw [hkk, mul_one] at this
      exact absurd this (not_le.mpr h)
    · exact h
    · have : 1 * k ≤ k * k := by gcongr
      rw [hkk, one_mul] at this
      exact absurd this (not_le.mpr h)
  have hwU : weyl c ν ∈ U := by
    intro φ
    show N (ω (weyl c ν) φ) = N φ
    rw [hw, hk1, one_mul]
  have htop : U = ⊤ := GlobalTheory.T.siegelParabolic_weylElement_generate_unitary F E c δ hE ν U hsieg hwU
  have hgU : g ∈ U := htop ▸ Subgroup.mem_top g
  have hμ' : μ' = Measure.addHaarScalarFactor μ' μ • μ := Measure.isAddLeftInvariant_eq_smul μ' μ
  rw [hμ', lintegral_smul_measure, lintegral_smul_measure]
  exact congrArg _ (hgU φ)
end GlobalTheory.KSp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.formallyUnramified_adjointRingAction_scheme : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left) (O : Type) [Ring O] (bar : O → O) (R : ActRep A Q bar), IsAbelianScheme A → FormallyUnramified R.π := by
  first | exact @GlobalTheory.EndLoc.formallyUnramified_actRep | exact GlobalTheory.EndLoc.formallyUnramified_actRep | (intros; apply GlobalTheory.EndLoc.formallyUnramified_actRep; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.exists_morita_lattice_quotient_torsion : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal → (p : 𝓞 D.F) ∈ w0 →
  ∀ (G : Type) [CommGroup G] (act : D.O → G → G), (∀ b g h, act b (g * h) = act b g * act b h) → (∀ g, act 1 g = g) →
  (∀ b c g, act (b * c) g = act b (act c g)) → (∀ b c g, act (b + c) g = act b g * act c g) →
  ∀ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) → G, (∀ a a', f (a + a') = f a * f a') →
  (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk (w0 ^ r) c • a) = act (algebraMap (𝓞 D.F) D.O c) (f a)) → Function.Injective f →
  (∀ g, (∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ a, f a = g) →
  ∃ l : D.La → G, (∀ x y, l (x + y) = l x * l y) ∧ (∀ (b : D.O) x, l (b • x) = act b (l x)) ∧
    (∀ x, l x = 1 ↔ x ∈ wSub D w0 r) ∧ ∀ g, (∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, l y = g := by
  first | (exact @GlobalTheory.EtLevMorita.exists_lev) | (exact GlobalTheory.EtLevMorita.exists_lev) | (intros; apply GlobalTheory.EtLevMorita.exists_lev <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem isClosedImmersion_of_isPullback_spMap_surj {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    (hσ : Function.Surjective σ) {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (h : IsPullback φ s' s (spMap σ)) : IsClosedImmersion φ := by
  have : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hσ
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip this

theorem restrict_pull1_preRes_pairFst {R' : Type} [CommRing R'] {X Y Y' : Scheme.{0}} (ψ : Y ⟶ X)
    (χ : Y' ⟶ Y) [IsAffineHom χ] (q' : Y' ⟶ Sp R') (y : HO1 q') :
    (CoefMap.restrict (OPre χ q') (pairFst ψ)).pull1 ((preRes χ q').pull1 y) =
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 y := by
  obtain ⟨y, rfl⟩ := H1.mk_surjective _ y
  rfl

theorem restrict_pull2_preRes_pairFst {R' : Type} [CommRing R'] {X Y Y' : Scheme.{0}} (ψ : Y ⟶ X)
    (χ : Y' ⟶ Y) [IsAffineHom χ] (q' : Y' ⟶ Sp R') (y : HO2 q') :
    (CoefMap.restrict (OPre χ q') (pairFst ψ)).pull2 ((preRes χ q').pull2 y) =
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 y := by
  obtain ⟨y, rfl⟩ := H2.mk_surjective _ y
  rfl



theorem bock_natural : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → ∀ (x : HO1 s') (z : HO2 s₀) (z' : HO2 q₀), Bock h.w h₀.w t x z → Bock k.w k₀.w t (pullHO1 w' x) z' → z' = pullHO2 w₀ z := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ψ ψ' ψ₀ w w' w₀ hc hc₀
    hS hs hq x z z' hB hB'
  obtain ⟨f, v, hfv, hf, hv⟩ := hB
  obtain ⟨f₂, v₂, hfv₂, hf₂, hv₂⟩ := hB'
  haveI : IsClosedImmersion φ := isClosedImmersion_of_isPullback_spMap_surj hS.1 h
  haveI : IsClosedImmersion φ₀ := isClosedImmersion_of_isPullback_spMap_surj hS.2.2.1 h₀
  haveI : IsClosedImmersion χ := isClosedImmersion_of_isPullback_spMap_surj hS.1 k
  haveI : IsClosedImmersion χ₀ := isClosedImmersion_of_isPullback_spMap_surj hS.2.2.1 k₀
  have hsec := GlobalTheory.AbCoh.preα_surjective_and_ker R R' R₀ t σ σ₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ hS hq
  obtain ⟨c₁, hc₁, hC₁⟩ :=
    (GlobalTheory.AbCoh.red_preimage_pairs R R' σ X X' Y Y' s s' q q' φ χ h.w ψ ψ' w w' hc inferInstance).1 f x hf
  obtain ⟨c₂, hc₂, hC₂⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R' Y Y' q q' σ χ k.w).1 f₂ (pullHO1 w' x)).1 hf₂
  obtain ⟨e₁, he₁, hE₁⟩ :=
    (GlobalTheory.AbCoh.red_preimage_pairs R R₀ σ₀ X X₀ Y Y₀ s s₀ q q₀ φ₀ χ₀ h₀.w ψ ψ₀ w w₀ hc₀ inferInstance).2 v z hv
  obtain ⟨e₂, he₂, hE₂⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R₀ Y Y₀ q q₀ σ₀ χ₀ k₀.w).2.1 v₂ z').1 hv₂
  have nat : ∀ {U V : AffOp Y} (a : U ⟶ V) (b : (OAff q).obj U),
      preα χ q q' V (mp (OAff q) a b) = mp (OPre χ q') a (preα χ q q' U b) :=
    fun a b ↦ (preCoef k.w).naturality a b
  have nat₀ : ∀ {U V : AffOp Y} (a : U ⟶ V) (b : (OAff q).obj U),
      preα χ₀ q q₀ V (mp (OAff q) a b) = mp (OPre χ₀ q₀) a (preα χ₀ q q₀ U b) :=
    fun a b ↦ (preCoef k₀.w).naturality a b

  obtain ⟨g', hg'⟩ := (H1.mk_eq_mk (f := c₁)
    (f' := (CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂)).1 (by
      rw [hC₁, ← CoefMap.pullCohomologyOne_class, hC₂, restrict_pull1_preRes_pairFst])
  choose g hg using fun p : (Pair ψ)ᵒᵖ ↦ (hsec ((pairFst ψ).obj p)).1 (g' p)
  obtain ⟨F1, hF1⟩ : ∃ F1 : C1 (OPair ψ q), ∀ a b (u : a ⟶ b),
      F1 a b u = (pairPull w).α b (f _ _ ((pairPull w).G.map u)) := ⟨_, fun _ _ _ ↦ rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F2 : C1 (OPair ψ q), ∀ a b (u : a ⟶ b),
      F2 a b u = f₂ _ _ ((pairFst ψ).map u) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hred : ∀ a b (u : a ⟶ b),
      preα χ q q' ((pairFst ψ).obj b) ((F1 - F2 - d0 (OPair ψ q) g) a b u) = 0 := by
    intro a b u
    have hc₂' : ((CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂).1 a b u =
        preα χ q q' ((pairFst ψ).obj b) (f₂ _ _ ((pairFst ψ).map u)) := hc₂ _ _ _
    have e : g' b - mp (pairFst ψ ⋙ OPre χ q') u (g' a) =
        c₁.1 a b u - ((CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂).1 a b u :=
      congrFun (congrFun (congrFun hg' a) b) u
    have e' : preα χ q q' ((pairFst ψ).obj b) (mp (OPair ψ q) u (g a)) =
        mp (pairFst ψ ⋙ OPre χ q') u (g' a) := by
      have := nat ((pairFst ψ).map u) (g a)
      rw [hg a] at this
      exact this
    simp only [Pi.sub_apply, amitsur_d0_apply, map_sub]
    rw [hF1, hF2, ← hc₁, ← hc₂', hg b, e', e, sub_self]
  choose u₀ hu₀ using fun a b (u : a ⟶ b) ↦ ((hsec ((pairFst ψ).obj b)).2.1 _).1 (hred a b u)
  have hD : F1 - F2 - d0 (OPair ψ q) g = t • (u₀ : C1 (OPair ψ q)) := by
    funext a b u; exact hu₀ a b u
  obtain ⟨W1, hW1⟩ : ∃ W1 : C2 (OPair ψ q), ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      W1 a b c u u' = (pairPull w).α c (v _ _ _ ((pairPull w).G.map u) ((pairPull w).G.map u')) :=
    ⟨_, fun _ _ _ _ _ ↦ rfl⟩
  obtain ⟨W2, hW2⟩ : ∃ W2 : C2 (OPair ψ q), ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      W2 a b c u u' = v₂ _ _ _ ((pairFst ψ).map u) ((pairFst ψ).map u') := ⟨_, fun _ _ _ _ _ ↦ rfl⟩
  have hdF1 : d1 (OPair ψ q) F1 = t • W1 := by
    funext a b c u u'
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hfv _) _) _)
      ((pairPull w).G.map u)) ((pairPull w).G.map u')
    simp only [d1_apply, Pi.smul_apply] at e ⊢
    rw [hF1, hF1, hF1, hW1, ← (pairPull w).naturality, Functor.map_comp, ← map_sub, ← map_add (f := _), e,
      (pairPull w).smul]
    rfl
  have hdF2 : d1 (OPair ψ q) F2 = t • W2 := by
    funext a b c u u'
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hfv₂ _) _) _)
      ((pairFst ψ).map u)) ((pairFst ψ).map u')
    simp only [d1_apply, Pi.smul_apply] at e ⊢
    rw [hF2, hF2, hF2, hW2, Functor.map_comp]
    exact e
  have hdd : d1 (OPair ψ q) (d0 (OPair ψ q) g) = 0 := by
    have := commAlgFunctorCoboundaryZero_mem_cocyclesOne (OPair ψ q) g
    rw [commAlgFunctorCocyclesOne_eq_ker] at this
    exact this
  have hmain : t • (W1 - W2 - d1 (OPair ψ q) u₀) = 0 := by
    rw [smul_sub, smul_sub, ← hdF1, ← hdF2, ← (d1 (OPair ψ q)).map_smul, ← hD, map_sub, map_sub, hdd,
      sub_zero, sub_self]
  have hzero : ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      preα χ₀ q q₀ ((pairFst ψ).obj c) ((W1 - W2 - d1 (OPair ψ q) u₀) a b c u u') = 0 := by
    intro a b c u u'
    refine ((hsec ((pairFst ψ).obj c)).2.2.2 _).2 ?_
    exact congrFun (congrFun (congrFun (congrFun (congrFun hmain a) b) c) u) u'
  obtain ⟨ub, hub⟩ : ∃ ub : C1 (pairFst ψ ⋙ OPre χ₀ q₀), ∀ a b (u : a ⟶ b),
      ub a b u = preα χ₀ q q₀ ((pairFst ψ).obj b) (u₀ a b u) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hH2 : H2.mk _ e₁ = H2.mk _ ((CoefMap.restrict (OPre χ₀ q₀) (pairFst ψ)).pullbackTwoCocycle e₂) := by
    refine H2.mk_eq_mk.2 ⟨ub, ?_⟩
    funext a b c u u'
    have E := hzero a b c u u'
    simp only [Pi.sub_apply, d1_apply, map_sub, map_add (f := _)] at E
    have E1 : preα χ₀ q q₀ ((pairFst ψ).obj c) (mp (OPair ψ q) u' (u₀ a b u)) =
        mp (pairFst ψ ⋙ OPre χ₀ q₀) u' (ub a b u) := by
      rw [hub]; exact nat₀ ((pairFst ψ).map u') (u₀ a b u)
    have E2 : e₁.1 a b c u u' = preα χ₀ q q₀ _ (W1 a b c u u') := by rw [he₁, hW1]
    have E3 : ((CoefMap.restrict (OPre χ₀ q₀) (pairFst ψ)).pullbackTwoCocycle e₂).1 a b c u u' =
        preα χ₀ q q₀ _ (W2 a b c u u') := by
      rw [hW2]; exact he₂ _ _ _ _ _
    simp only [d1_apply, Pi.sub_apply]
    rw [E2, E3, ← E1, hub, hub]
    linear_combination -E
  rw [hE₁, ← CoefMap.pullCohomologyTwo_class, hE₂, restrict_pull2_preRes_pairFst] at hH2
  exact ((GlobalTheory.AbCoh.pair_pre_bijective R₀ X Y Y₀ ψ χ₀ q₀).2.1.1 hH2).symm

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cohomologyClass_pullback_reduction_pairs : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' Y Y' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (φ : X' ⟶ X) (χ : Y' ⟶ Y) [IsAffineHom χ] (h : φ ≫ s = s' ≫ spMap σ) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')), ψ' ≫ φ = χ ≫ ψ → IsAffineHom φ → (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x → ∃ c : Z1 (pairFst ψ ⋙ OPre χ q'), (∀ a b (u : a ⟶ b), c.1 a b u = preα χ q q' ((pairFst ψ).obj b) ((pairPull w).α b (f _ _ ((pairPull w).G.map u)))) ∧ GlobalTheory.CatCoh.H1.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 (pullHO1 w' x)) ∧ ∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z → ∃ c : Z2 (pairFst ψ ⋙ OPre χ q'), (∀ a b d (u : a ⟶ b) (u' : b ⟶ d), c.1 a b d u u' = preα χ q q' ((pairFst ψ).obj d) ((pairPull w).α d (v _ _ _ ((pairPull w).G.map u) ((pairPull w).G.map u')))) ∧ GlobalTheory.CatCoh.H2.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 (pullHO2 w' z) := by
  first | exact @GlobalTheory.AbCoh.red_preimage_pairs | exact GlobalTheory.AbCoh.red_preimage_pairs | (intros; apply GlobalTheory.AbCoh.red_preimage_pairs <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (φ : X' ⟶ X) [IsClosedImmersion φ] (s' : X' ⟶ Sp R'), Function.Bijective (preRes φ s').pull1 ∧ Function.Bijective (preRes φ s').pull2 ∧ (CohomZeroIsConstants (OAff s') → CohomZeroIsConstants (OPre φ s')) := by
  first | exact @GlobalTheory.AbCoh.preRes_bijective | exact GlobalTheory.AbCoh.preRes_bijective | (intros; apply GlobalTheory.AbCoh.preRes_bijective <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pairFst_preimage_restriction_bijective_closedImmersion : ∀ (R' : Type) [CommRing R'] (X Y Y' : Scheme.{0}) (ψ : Y ⟶ X) (χ : Y' ⟶ Y) [IsClosedImmersion χ] (q' : Y' ⟶ Sp R'), Function.Bijective (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 ∧ (CohomZeroIsConstants (OAff q') → CohomZeroIsConstants (pairFst ψ ⋙ OPre χ q')) := by
  first | exact @GlobalTheory.AbCoh.pair_pre_bijective | exact GlobalTheory.AbCoh.pair_pre_bijective | (intros; apply GlobalTheory.AbCoh.pair_pre_bijective <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.wedge_property_from_fibres : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Module.Finite R (HO1 s) → Module.Projective R (HO1 s) → Module.Finite R (HO2 s) → Module.Projective R (HO2 s) → StructureSheafH1BaseChange s → StructureSheafH2BaseChange s → (∀ x : HO1 s, cup _ x x = 0) → (∀ (k : Type) [Field k] [Algebra R k] (X' : Scheme.{0}) (s' : X' ⟶ Sp k) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R k))), WedgeO (OAff s')) → WedgeO (OAff s) := by
  first | exact @GlobalTheory.AbCoh.Wedge.wedgeO_of_fibres | exact GlobalTheory.AbCoh.Wedge.wedgeO_of_fibres | (intros; apply GlobalTheory.AbCoh.Wedge.wedgeO_of_fibres <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.glob1_finite_and_projective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Module.Finite R (Glob1 F) ∧ Module.Projective R (Glob1 F) := by
  first | exact @GlobalTheory.AbCoh.compatibleGlobalOneForms_finite_projective | exact GlobalTheory.AbCoh.compatibleGlobalOneForms_finite_projective | (intros; apply GlobalTheory.AbCoh.compatibleGlobalOneForms_finite_projective <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_connection_of_cohomologyDerivativeRelation : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F), DRel F x y w → (∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = 0) → ∃ (m : ℕ) (u v : Fin m → Glob1 F), ObRel F x u v := by
  first | exact @GlobalTheory.AbCoh.exists_obRel_of_dRel | exact GlobalTheory.AbCoh.exists_obRel_of_dRel | (intros; apply GlobalTheory.AbCoh.exists_obRel_of_dRel <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.grpObj_pullback_axes_cohomology_projections : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], (∀ a, pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 (fst A A) a) = a ∧ pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 (snd A A) a) = 0 ∧ pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 μ[A] a) = a ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 (fst A A) a) = 0 ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 (snd A A) a) = a ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 μ[A] a) = a) ∧ (∀ a, pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (fst A A) a) = a ∧ pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (snd A A) a) = 0 ∧ pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF μ[A] a) = a ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (fst A A) a) = 0 ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (snd A A) a) = a ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF μ[A] a) = a) ∧ (∀ a, deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback (fst A A) a) = a ∧ deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback (snd A A) a) = 0 ∧ deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback μ[A] a) = a ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback (fst A A) a) = 0 ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback (snd A A) a) = a ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback μ[A] a) = a) := by
  first | exact @GlobalTheory.AbCoh.AxesPull.main | exact GlobalTheory.AbCoh.AxesPull.main | (intros; apply GlobalTheory.AbCoh.AxesPull.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isBaseChange_compatibleGlobalOneForms : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (T : C) (e : Glob1 F →ₗ[R] Ω[F.obj T⁄R]), (∀ w, e w = w.1 T) → IsBaseChange (F.obj T) e := by
  first | exact @GlobalTheory.AbCoh.isBaseChange_glob1 | exact GlobalTheory.AbCoh.isBaseChange_glob1 | (intros; apply GlobalTheory.AbCoh.isBaseChange_glob1 <;> assumption)
end
