module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle629
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle280
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle199
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle711
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.RegOrInvModel

theorem exists_idealSheaf_principalises_of_ne_zero : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (n : ℕ) (U : Fin n → X.Opens) (m : Fin n → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)), (∀ j, IsAffineOpen (U j)) → (∀ j, ∃ k, A j k ≠ 0) → ∃ J : X.IdealSheafData, genericPoint X ∉ J.support ∧ ∀ (W : Scheme.{0}) (b : W ⟶ X), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) → ∀ (w : W) (j : Fin n), b w ∈ U j → ∃ (V : W.Opens) (hV : V ≤ b ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧ ∃ k, ∀ k', (b.appLE (U j) V hV).hom (A j k) ∣ (b.appLE (U j) V hV).hom (A j k') := by
  intro X _ _ n U m A hU hA
  choose J hJU hJp using fun j => GlobalTheory.Principalise.kerIdealAffine X (U j) (hU j) (Ideal.span (Set.range (A j)))
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hηV₀, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hsupp : ∀ I : X.IdealSheafData, genericPoint X ∉ I.support ↔
      ∃ f ∈ I.ideal ⟨V₀, hV₀⟩, genericPoint X ∈ X.basicOpen f := by
    intro I
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V₀, hV₀⟩) hηV₀, Scheme.mem_zeroLocus_iff]
    push_neg
    rfl
  have hmul : ∀ I I' : X.IdealSheafData, genericPoint X ∉ I.support → genericPoint X ∉ I'.support →
      genericPoint X ∉ (I * I').support := by
    intro I I' h h'
    obtain ⟨f, hf, hηf⟩ := (hsupp I).1 h
    obtain ⟨f', hf', hηf'⟩ := (hsupp I').1 h'
    refine (hsupp _).2 ⟨f * f', ?_, ?_⟩
    · rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
      exact Ideal.mul_mem_mul hf hf'
    · rw [Scheme.basicOpen_mul]
      exact ⟨hηf, hηf'⟩
  have hone : genericPoint X ∉ (1 : X.IdealSheafData).support := by
    refine (hsupp _).2 ⟨1, ?_, ?_⟩
    · show (1 : Γ(X, V₀)) ∈ (⊤ : X.IdealSheafData).ideal ⟨V₀, hV₀⟩
      rw [Scheme.IdealSheafData.ideal_top]
      exact Submodule.mem_top
    · rw [Scheme.basicOpen_one]
      exact hηV₀
  have hJj : ∀ j, genericPoint X ∉ (J j).support := by
    intro j
    obtain ⟨k, hk⟩ := hA j
    have hb : X.basicOpen (A j k) ≠ ⊥ := fun h0 => hk ((basicOpen_eq_bot_iff _).1 h0)
    obtain ⟨x, hx⟩ : ∃ x, x ∈ X.basicOpen (A j k) := by
      by_contra hc
      push_neg at hc
      exact hb (eq_bot_iff.2 fun x hx => (hc x hx).elim)
    have hηb : genericPoint X ∈ X.basicOpen (A j k) := gen_mem hx
    have hηU : genericPoint X ∈ U j := X.basicOpen_le _ hηb
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U j, hU j⟩) hηU, Scheme.mem_zeroLocus_iff, hJU j]
    exact fun h => h _ (Ideal.subset_span ⟨k, rfl⟩) hηb
  refine ⟨∏ j, J j, ?_, ?_⟩
  · exact Finset.prod_induction J (fun I => genericPoint X ∉ I.support) hmul hone fun j _ => hJj j
  · intro W b hE w j hw
    obtain ⟨V₁, f, hw₁, hf, hV₁⟩ := hE w
    obtain ⟨g, hgle, hwg⟩ := V₁.2.exists_basicOpen_le (V := V₁.1 ⊓ b ⁻¹ᵁ U j) ⟨w, hw₁, hw⟩ hw₁
    have hDU : (W.affineBasicOpen g).1 ≤ b ⁻¹ᵁ U j := hgle.trans inf_le_right
    have hDV : (W.affineBasicOpen g).1 ≤ V₁.1 := W.basicOpen_le g
    have hfD : (W.presheaf.map (homOfLE hDV).op).hom f ∈ nonZeroDivisors Γ(W, (W.affineBasicOpen g).1) :=
      (GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen (W.affineBasicOpen g).2).1
        (((GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen V₁.2).2 hf).resG hDV)
    have hI1 := ((∏ i, J i).comap b).map_ideal_basicOpen V₁ g
    rw [hV₁, Ideal.map_span, Set.image_singleton] at hI1
    have hI2 := GlobalTheory.Principalise.comapIdealAffine (∏ i, J i) b ⟨U j, hU j⟩ (W.affineBasicOpen g) hDU
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j), Scheme.IdealSheafData.ideal_mul,
      Pi.mul_apply, Ideal.map_mul, hJU, Ideal.map_span, ← Set.range_comp] at hI2
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j)] at hI1
    have hwD : w ∈ (W.affineBasicOpen g).1 := hwg
    obtain ⟨k, s, hsP, hdiv⟩ := GlobalTheory.Principalise.exists_dvd_of_span_mul_eq
      (Ideal.comap (W.presheaf.germ (W.affineBasicOpen g).1 w hwD).hom (IsLocalRing.maximalIdeal _)) _ _
      (hI2.symm.trans hI1.symm) hfD
    have hsu : w ∈ W.basicOpen s := by
      rw [Scheme.mem_basicOpen _ _ _ hwD]
      by_contra hc
      exact hsP ((IsLocalRing.mem_maximalIdeal _).2 hc)
    have hED : W.basicOpen s ≤ (W.affineBasicOpen g).1 := W.basicOpen_le s
    have hV : W.basicOpen s ≤ b ⁻¹ᵁ U j := fun x hx => hDU (hED hx)
    refine ⟨W.basicOpen s, hV, hsu, (W.affineBasicOpen g).2.basicOpen s, k, fun k' => ?_⟩
    have key : b.appLE (U j) _ hDU ≫ W.presheaf.map (homOfLE hED).op = b.appLE (U j) (W.basicOpen s) hV :=
      Scheme.Hom.appLE_map _ _ _
    have hu := W.toRingedSpace.isUnit_res_basicOpen s
    have h1 := map_dvd (W.presheaf.map (homOfLE hED).op).hom (hdiv k')
    rw [map_mul] at h1
    have h2 := hu.dvd_mul_left.1 h1
    rw [← key]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    exact h2

theorem exists_model_regAt_or_regAt_inv : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ g : X.functionField, g ≠ 0 → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ ∀ y : Y, RegAt y (φ g) ∨ RegAt y (φ g)⁻¹ := by
  intro k _ X _ p D hX g hg
  have := hX.isLocallyNoetherian
  have := hX.isNoetherian
  choose V hVa hxV using fun x : X => (by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV, hx⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  let e := t.equivFin
  let U : Fin t.card → X.Opens := fun j => V (e.symm j).1
  have hU : ∀ j, IsAffineOpen (U j) := fun j => hVa _
  have hη : ∀ j, genericPoint X ∈ U j := fun j => gen_mem (hxV (e.symm j).1)
  have hfr : ∀ j, ∃ a b : Γ(X, U j), b ≠ 0 ∧ fnOf (U j) (hη j) a / fnOf (U j) (hη j) b = g := by
    intro j
    have : Nonempty (U j) := ⟨⟨_, hη j⟩⟩
    have := functionField_isFractionRing_of_isAffineOpen X (U j) (hU j)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, U j)) g
    exact ⟨a, b, nonZeroDivisors.ne_zero hb, hab⟩
  choose a b hb hab using hfr
  let A : ∀ j, Fin 2 → Γ(X, U j) := fun j => ![a j, b j]
  obtain ⟨J, hJη, hJdiv⟩ := exists_idealSheaf_principalises_of_ne_zero X t.card U (fun _ => 2) A hU fun j => ⟨1, hb j⟩
  obtain ⟨Y, ρ, hY, hE, hiso⟩ := GlobalTheory.BlowArith.exists_isArithVar_effCartier_isIso k X p D hX J hJη
  have : IsIntegral Y := hY.isIntegral
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isBirationalModel_of_isIso_over_nonempty_open X Y ρ J.support.compl ⟨genericPoint X, hJη⟩ (hiso _ fun _ hx => hx)
  obtain ⟨-, -, hfn, -⟩ := GlobalTheory.T.birationalModel_regular_unit_values k X Y p (ρ ≫ p) ρ rfl φ hφ
  refine ⟨Y, inferInstance, ρ, φ, hY, hφ, fun y => ?_⟩
  obtain ⟨x, hxt, hyx⟩ : ∃ x ∈ t, ρ y ∈ V x := by
    simpa using ht (Set.mem_univ (ρ y))
  set j := e ⟨x, hxt⟩ with hj
  have hyj : ρ y ∈ U j := by simpa [U, j] using hyx
  obtain ⟨W, hW, hyW, -, kk, hdiv⟩ := hJdiv Y ρ hE y j hyj
  have hWη : genericPoint Y ∈ W := gen_mem hyW
  have key : ∀ c : Γ(X, U j), fnOf W hWη ((ρ.appLE (U j) W hW).hom c) = φ (fnOf (U j) (hη j) c) := by
    intro c
    rw [hfn (U j) (hη j) (hW hWη) c]
    exact fnOf_resG hW hWη ((ρ.app (U j)).hom c)
  have hbne : φ (fnOf (U j) (hη j) (b j)) ≠ 0 := by
    rw [map_ne_zero]
    exact fun h0 => hb j (fnOf_injective _ _ (h0.trans (map_zero _).symm))
  have hane : φ (fnOf (U j) (hη j) (a j)) ≠ 0 := by
    rw [map_ne_zero]
    intro h0
    apply hg
    rw [← hab j, h0, zero_div]
  have hφg : φ g = φ (fnOf (U j) (hη j) (a j)) / φ (fnOf (U j) (hη j) (b j)) := by
    rw [← hab j, map_div₀]
  fin_cases kk
  · right
    obtain ⟨c, hc⟩ := hdiv 1
    have e1 := congrArg (fnOf W hWη) hc
    rw [map_mul, key, key] at e1
    have : (φ g)⁻¹ = fnOf W hWη c := by
      rw [hφg, inv_div, div_eq_iff hane]
      exact e1.trans (mul_comm _ _)
    rw [this]
    exact regAt_fnOf hyW hWη c
  · left
    obtain ⟨c, hc⟩ := hdiv 0
    have e1 := congrArg (fnOf W hWη) hc
    rw [map_mul, key, key] at e1
    have : φ g = fnOf W hWη c := by
      rw [hφg, div_eq_iff hbne]
      exact e1.trans (mul_comm _ _)
    rw [this]
    exact regAt_fnOf hyW hWη c

end GlobalTheory.RegOrInvModel
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjFormulaVert



theorem exists_affine_finite_free (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (hX : IsProjOver p) (hY : IsProjOver q) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (hg : π (genericPoint Y) = genericPoint X) (hδ : π.residueDegree (genericPoint Y) ≠ 0) :
    ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧
      (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧
        Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = π.residueDegree (genericPoint Y)) := by
  have hqP : IsProper q := by
    obtain ⟨N, j, _, hj⟩ := hY
    have := isProper_str k N
    exact hj ▸ inferInstance
  have : IsSeparated (π ≫ p) := hπ ▸ (inferInstance : IsSeparated q)
  have hsep : IsSeparated π := IsSeparated.of_comp π p
  have : LocallyOfFiniteType (π ≫ p) := hπ ▸ (inferInstance : LocallyOfFiniteType q)
  have hlft : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  have : IsLocallyNoetherian X := by
    obtain ⟨N, j, _, hj⟩ := hX
    have : LocallyOfFiniteType p := hj ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U₀, hU₀, hxU₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X))
  have hyU₀ : genericPoint Y ∈ π ⁻¹ᵁ U₀ := by
    show π (genericPoint Y) ∈ U₀
    rw [hg]; exact hxU₀
  obtain ⟨V₀, hV₀, hyV₀, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hyU₀
  haveI : Nonempty U₀ := ⟨⟨_, hxU₀⟩⟩
  haveI : Nonempty V₀ := ⟨⟨_, hyV₀⟩⟩
  letI : Algebra Γ(X, U₀) Γ(Y, V₀) := (π.appLE U₀ V₀ hVle).hom.toAlgebra
  haveI : IsNoetherianRing Γ(X, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  haveI : FaithfulSMul Γ(X, U₀) Γ(Y, V₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (GlobalTheory.appLE_injective_of_genericPoint_map π hg ⟨_, hyV₀⟩ hVle)
  haveI : Algebra.FiniteType Γ(X, U₀) Γ(Y, V₀) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType π hlft ⟨U₀, hU₀⟩ ⟨V₀, hV₀⟩ hVle
  haveI : Algebra.IsAlgebraic Γ(X, U₀) Γ(Y, V₀) := GlobalTheory.GenDegAlg.isAlgebraic_appLE π hg hδ hU₀ ⟨_, hyV₀⟩ hVle
  obtain ⟨a₁, ha₁, H₁⟩ := GlobalTheory.finite_away_of_isAlgebraic_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  obtain ⟨a₂, ha₂, H₂⟩ := GlobalTheory.free_away_mul_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  have ha : a₁ * a₂ ≠ 0 := mul_ne_zero ha₁ ha₂
  have hUU₀ : X.basicOpen (a₁ * a₂) ≤ U₀ := X.basicOpen_le _
  have hUa : IsAffineOpen (X.basicOpen (a₁ * a₂)) := hU₀.basicOpen _
  have hxU : genericPoint X ∈ X.basicOpen (a₁ * a₂) := by
    have hne : X.basicOpen (a₁ * a₂) ≠ ⊥ := fun h => ha ((basicOpen_eq_bot_iff _).1 h)
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen (a₁ * a₂)).isOpen).2
      ⟨z, trivial, hz⟩
  set U : X.Opens := X.basicOpen (a₁ * a₂) with hU_def
  set V : Y.Opens := Y.basicOpen (π.appLE U₀ V₀ hVle (a₁ * a₂)) with hV_def
  have hVV₀ : V ≤ V₀ := Y.basicOpen_le _
  have hVe : V = V₀ ⊓ π ⁻¹ᵁ U := Scheme.basicOpen_appLE π V₀ U₀ hVle _
  have hVU : V ≤ π ⁻¹ᵁ U := by rw [hVe]; exact inf_le_right
  have hVa : IsAffineOpen V := hV₀.basicOpen _
  have hyV : genericPoint Y ∈ V := by
    rw [hVe]; exact ⟨hyV₀, show π (genericPoint Y) ∈ U from hg ▸ hxU⟩
  letI iA : Algebra Γ(X, U₀) Γ(X, U) := (X.presheaf.map (homOfLE hUU₀).op).hom.toAlgebra
  letI iB : Algebra Γ(Y, V₀) Γ(Y, V) := (Y.presheaf.map (homOfLE hVV₀).op).hom.toAlgebra
  letI iAB : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V hVU).hom.toAlgebra
  letI iAB' : Algebra Γ(X, U₀) Γ(Y, V) := (π.appLE U₀ V (hVV₀.trans hVle)).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U₀) Γ(X, U) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.map_appLE hVU (homOfLE hUU₀).op).symm)
  haveI : IsScalarTower Γ(X, U₀) Γ(Y, V₀) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.appLE_map hVle (homOfLE hVV₀).op).symm)
  haveI hlA : IsLocalization.Away (a₁ * a₂) Γ(X, U) :=
    hU₀.isLocalization_of_eq_basicOpen _ (homOfLE hUU₀) rfl
  haveI hlB : IsLocalization.Away (algebraMap Γ(X, U₀) Γ(Y, V₀) (a₁ * a₂)) Γ(Y, V) :=
    hV₀.isLocalization_of_eq_basicOpen _ (homOfLE hVV₀) rfl
  have e2 : a₂ * a₁ = a₁ * a₂ := mul_comm _ _
  have hfin : Module.Finite Γ(X, U) Γ(Y, V) := H₁ a₂ Γ(X, U) Γ(Y, V) hlA hlB
  have hfree : Module.Free Γ(X, U) Γ(Y, V) :=
    H₂ a₁ Γ(X, U) Γ(Y, V) (by rw [e2]; exact hlA) (by rw [e2]; exact hlB)
  have hpre : π ⁻¹ᵁ U = V := GlobalTheory.preimage_eq_of_finite_appLE π hUa hVa ⟨_, hyV⟩ hVU hfin
  have key : ∀ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U →
      (letI := (π.appLE U W hW).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, W) ∧ Module.Finite Γ(X, U) Γ(Y, W)) →
      (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by
    rintro W hW rfl h
    rw [Scheme.Hom.app_eq_appLE]
    exact h
  obtain ⟨h1, h2⟩ := key V hVU hpre.symm ⟨hfree, hfin⟩
  exact ⟨U, hUa, hxU, hpre ▸ hVa, h1, h2,
    GlobalTheory.GenFinEtField.finrank_app_eq_residueDegree π hg hUa (hpre ▸ hVa) hxU⟩

end GlobalTheory.ProjFormulaVert

namespace GlobalTheory.ProjFormulaVert

theorem algebra_zmod_eq {l : ℕ} {R : Type} [CommRing R] (a b : Algebra (ZMod l) R) : a = b :=
  Algebra.algebra_ext a b fun r => congrFun (congrArg DFunLike.coe
    (RingHom.ext_zmod (@algebraMap _ _ _ _ a) (@algebraMap _ _ _ _ b))) r

theorem height_pull_vertical : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ),
    IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ),
    L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ (y : Y) (l : ℕ) [Fact l.Prime],
    Nonempty (Algebra (ZMod l) Γ(clo y, ⊤)) → h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' hh hh' y l _ ⟨instW⟩
  obtain ⟨g, hgc, hgen, hgdeg⟩ := GlobalTheory.T.exists_dominant_restriction_pointClosures X Y π y
  have hδ : g.residueDegree (genericPoint (clo y)) = π.residueDegree y := by
    rw [hgdeg, cloι_genericPoint]

  have hinj : Function.Injective g.appTop.hom := by
    have := GlobalTheory.appLE_injective_of_genericPoint_map g hgen (U := ⊤) (V := g ⁻¹ᵁ ⊤)
      ⟨genericPoint (clo y), trivial⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  haveI : Nonempty (⊤ : (clo y).Opens) := ⟨⟨genericPoint (clo y), trivial⟩⟩
  haveI : CharP Γ(clo y, ⊤) l :=
    charP_of_injective_algebraMap (algebraMap (ZMod l) Γ(clo y, ⊤)).injective l
  haveI : CharP Γ(clo (π y), ⊤) l := ⟨fun n => by
    rw [← CharP.cast_eq_zero_iff Γ(clo y, ⊤) l n, ← map_natCast g.appTop.hom n,
      map_eq_zero_iff _ hinj]⟩
  letI instZ : Algebra (ZMod l) Γ(clo (π y), ⊤) := ZMod.algebra _ l
  have hWp : IsProjOver (strHom (ZMod l) (X := (clo y))) :=
    GlobalTheory.FibreProj.isProjOver_closed_fibre k Y q E hY (clo y) (cloι y) l
  have hZp : IsProjOver (strHom (ZMod l) (X := (clo (π y)))) :=
    GlobalTheory.FibreProj.isProjOver_closed_fibre k X p D hX (clo (π y)) (cloι (π y)) l
  have hgs : g ≫ strHom (ZMod l) (clo (π y)) = strHom (ZMod l) (clo y) :=
    comp_strHom fun r => congrFun (congrArg DFunLike.coe
      (RingHom.ext_zmod (g.appTop.hom.comp (algebraMap (ZMod l) _)) (algebraMap (ZMod l) _))) r

  obtain ⟨⟨m, hm⟩, -, -, -, hcl, hgd⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q (isAmb_of_isArithVar hY)
  obtain ⟨⟨m', hm'⟩, -, -, -, hcl', hgd'⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p (isAmb_of_isArithVar hX)
  obtain ⟨d, -, hd⟩ := hm y
  obtain ⟨d', -, hd'⟩ := hm' (π y)
  have hWd : topologicalKrullDim (clo y) = d :=
    (hgd (clo y) d).1 ((hcl (clo y) (cloι y) _ d).1 (by rw [cloι_genericPoint]; exact hd))
  have hZd : topologicalKrullDim (clo (π y)) = d' :=
    (hgd' (clo (π y)) d').1 ((hcl' (clo (π y)) (cloι (π y)) _ d').1 (by rw [cloι_genericPoint]; exact hd'))
  obtain ⟨hle, hiff⟩ := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q (isAmb_of_isArithVar hX) (isAmb_of_isArithVar hY) π hπ y d d' hd hd'

  have e1 := hh'.vertical (clo y) (cloι y) (ZMod l) d hWd
  have e2 := hh.vertical (clo (π y)) (cloι (π y)) (ZMod l) d' hZd
  rw [cloι_genericPoint] at e1 e2
  have ej : (cloι y ≫ π) ≫ p = cloι y ≫ q := by rw [Category.assoc, hπ]
  have ei : (g ≫ cloι (π y)) ≫ p = g ≫ cloι (π y) ≫ p := Category.assoc _ _ _
  have t1 : topSelfIntersection (ZMod l) ((L.pull π hπ).B.pull (cloι y)) d = topSelfIntersection (ZMod l) (L.B.pull (cloι y ≫ π)) d :=
    topSelf_congr (ZMod l) ((L.pull π hπ).pull (cloι y) rfl).isLB (L.pull (cloι y ≫ π) ej).isLB
      (LBIso.chartPull (chartPullLinComb L.B π (fun _ : PUnit => cloι y)
        (fun _ => cloι y ≫ π) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
        (chartPullId _) (PolBaseChange.lbIso_refl (LB.isLB_pull L.isLB _))) d
  have t2 : topSelfIntersection (ZMod l) (L.B.pull (g ≫ cloι (π y))) d =
      topSelfIntersection (ZMod l) ((L.B.pull (cloι (π y))).pull g) d :=
    topSelf_congr (ZMod l) (L.pull (g ≫ cloι (π y)) ei).isLB ((L.pull (cloι (π y)) rfl).pull g rfl).isLB
      (LBIso.symm (LBIso.chartPull (chartPullLinComb L.B (cloι (π y)) (fun _ : PUnit => g)
        (fun _ => g ≫ cloι (π y)) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
        (chartPullId _) (PolBaseChange.lbIso_refl (LB.isLB_pull L.isLB _)))) d
  rw [t1, ← hgc, t2] at e1
  rw [e1, e2]
  suffices key : topSelfIntersection (ZMod l) ((L.B.pull (cloι (π y))).pull g) d =
      (π.residueDegree y : ℤ) * topSelfIntersection (ZMod l) (L.B.pull (cloι (π y))) d' by
    rw [key]; push_cast; ring
  have hB : (L.B.pull (cloι (π y))).IsLB := (L.pull (cloι (π y)) rfl).isLB
  have hBg : ((L.B.pull (cloι (π y))).pull g).IsLB := ((L.pull (cloι (π y)) rfl).pull g rfl).isLB
  have hclo : topologicalKrullDim (closure ({g (genericPoint (clo y))} : Set (clo (π y)))) = d' := by
    rw [hgen, (genericPoint_spec (clo (π y))).def]
    exact (Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq.trans hZd
  by_cases h0 : π.residueDegree y = 0
  · have hne : d ≠ d' := fun e => (hiff.2 e) h0
    have hlt : d' < d := lt_of_le_of_ne hle (Ne.symm hne)
    have hz := GlobalTheory.PullVanish.interNum_pull_eq_zero (ZMod l) 0 d (clo y) (clo (π y)) hWp
      (by rw [Nat.zero_add, hWd]) g (by rw [hclo]; exact_mod_cast hlt)
      (fun i => i.elim0) (fun i => i.elim0) (fun _ => L.B.pull (cloι (π y))) (fun _ => hB)
    rw [h0, Nat.cast_zero, zero_mul, topSelf_def, ← interNum_comp_equiv (ZMod l) _ (fun _ => hBg)
      (Equiv.emptySum (Fin 0) (Fin d)), ← hz]
    congr 1
    funext x
    rcases x with i | a
    · exact i.elim0
    · rfl
  · have hdd : d = d' := hiff.1 h0
    subst hdd
    obtain ⟨U, hU, hgU, hU', hfree, hfin, hrank⟩ := exists_affine_finite_free (ZMod l) (clo (π y)) (clo y)
      (strHom (ZMod l) (clo (π y))) (strHom (ZMod l) (clo y)) hZp hWp g hgs hgen (hδ ▸ h0)
    have key := GlobalTheory.FieldProj.interNum_pull_eq_mul (ZMod l) (clo y) (clo (π y)) (strHom (ZMod l) (clo (π y))) g
      (hgs ▸ hWp) hZp U _ hgU hU hU' ⟨hfree, hfin, hrank⟩ d hZd.le (fun _ => L.B.pull (cloι (π y))) (fun _ => hB)
    rw [hδ] at key
    rw [topSelf_def, topSelf_def]
    convert key using 3
    · exact algebra_zmod_eq _ _
    · exact algebra_zmod_eq _ _

end GlobalTheory.ProjFormulaVert
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

noncomputable section

namespace GlobalTheory.FlagCell2.Dim

theorem card_low (s : ℕ) : Fintype.card (Low s) = s.choose 2 := by
  have h₁ : Fintype.card (Low s) = ∑ i : Fin s, (Finset.Ioi i).card := by
    rw [← Finset.card_sigma, ← Finset.card_univ]
    refine Finset.card_bij' (fun s _ => ⟨s.1.2, s.1.1⟩) (fun t ht => ⟨(t.2, t.1), by simpa using ht⟩) ?_ ?_ ?_ ?_ <;>
      simp
  rw [h₁, Nat.choose_two_right]
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => s - 1 - i), Finset.sum_range_reflect (fun i => i), Finset.sum_range_id]

theorem dim_eq_of_refines {F : Type} [Field F] [CharZero F] {X Y Y' : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ}
    {E : Fr (ratOf X) m 0} {S : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X}
    {S' : Fr (ratOf Y') m m} {φ' : X.Fn →ₐ[F] Y'.Fn} {f' : Y'.X ⟶ X.X}
    (hR : Refines E S φ f) (hR' : Refines E S' φ' f') : Y.dim = Y'.dim := by
  have R₁ := hR.reps
  have R₂ := hR'.reps
  obtain ⟨ψ, hψ, hG⟩ := exists_fieldMap_coBear_generic F ι m X Y Y' E S φ f S' φ' f' R₁ R₂
  obtain ⟨h, hh⟩ := GlobalTheory.ZH.RatModel.exists_isHom_of_map_O F Y'.Fn (ratOf Y') Y.Fn (ratOf Y) ψ
    (dominates_O F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ ψ hψ hG)
  have hf : h ≫ f' = f := by
    have h1 := R₂.1.comp hh
    rw [hψ] at h1
    exact h1.unique R₁.1
  have hb := CoBear₂ F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ h hf
    (coBear_comp_of_isHom F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ ψ hψ hG h hh)
  change Y.X ⟶ Y'.X at h
  have : IsIso h := GlobalTheory.BijPointsIso.isIso_of_bijective_points F Y Y' h hh.inducedModelMorphism_comp_structureMap fun K _ _ => hb K
  have hd : topologicalKrullDim Y.X = topologicalKrullDim Y'.X :=
    IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso h)).isHomeomorph
  rw [Y.topologicalKrullDim_eq, Y'.topologicalKrullDim_eq] at hd
  exact_mod_cast hd

theorem main : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → Y.dim = X.dim + Fintype.card (Cell m) := by
  intro F _ σ X Y ι _ m E E' φ f _ hR
  have : CharZero F := σ.charZero
  obtain ⟨Y', φ', f', S', hd, hR'⟩ := tower _ (ratOf X) X.dim E (good_ratOf X) (fun _ => Nat.zero_le _) rfl
  rw [dim_eq_of_refines hR hR', hd, Fintype.card_sigma]
  simp only [card_low, Pi.zero_apply, Nat.sub_zero]

end GlobalTheory.FlagCell2.Dim
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_e8ThetaPower_over_moduli_domain : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (R : Type) [CommRing R] [IsDomain R] (u : Sp R ⟶ F.X), ∃ P : PolAV (Sp R), SharpOver F W P u := by
  first | exact @GlobalTheory.Poinc.exists_sharpOver_domain | exact GlobalTheory.Poinc.exists_sharpOver_domain | (intros; apply GlobalTheory.Poinc.exists_sharpOver_domain <;> assumption)
end
