module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle615
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle619
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Mathlib.RingTheory.Bialgebra.Quotient

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem representing_qc_qs_loft : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0})
    (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H),
    QuasiCompact (R.homEquiv (𝟙 H)).1 ∧ QuasiSeparated (R.homEquiv (𝟙 H)).1 ∧
      LocallyOfFiniteType (R.homEquiv (𝟙 H)).1 := by
  intro A B _ _ _ _ _ r H R
  classical
  let e : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex A B))) A B :=
    (Module.Free.chooseBasis A B).reindex (Fintype.equivFin _)
  set N := Fintype.card (Module.Free.ChooseBasisIndex A B)
  set ξ := R.homEquiv (𝟙 H) with hξ
  have hR : ∀ {Z : Scheme.{0}} (b : Z ⟶ H), R.homEquiv b = (functor A B r).map b.op ξ := by
    intro Z b
    have := R.homEquiv_comp b (𝟙 H)
    rwa [Category.comp_id] at this
  have hmap : ∀ {Z Z' : Scheme.{0}} (a : Z' ⟶ Z) (b : Z ⟶ H),
      (functor A B r).map a.op ((functor A B r).map b.op ξ) = (functor A B r).map (a ≫ b).op ξ := by
    intro Z Z' a b
    rw [← hR b, ← hR (a ≫ b), R.homEquiv_comp]
  have hrc : ∀ {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z),
      Set.range (a ≫ b) = b '' Set.range a := by
    intro X Y Z a b
    ext p
    simp
  choose W hW hWc using fun σ : Fin r ↪ Fin N => GlobalTheory.T.exists_open_affineHilbertChartBasic_locus A B N r e σ H ξ
  choose X x hXa hXl hXb hXu using fun σ : Fin r ↪ Fin N => GlobalTheory.T.affineHilbertChart_representable A B N r e σ
  have hcov : ⨆ σ, W σ = ⊤ := by
    rw [eq_top_iff]
    intro h _
    obtain ⟨σ, U, hU, hb⟩ := GlobalTheory.T.exists_affineHilbertChartBasic_neighbourhood A B N r e H ξ h
    have := (hW σ _ U.ι).2 hb
    rw [Scheme.Opens.range_ι] at this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨σ, this hU⟩
  have hiso : ∀ σ, ∃ g : (W σ).toScheme ⟶ X σ, IsIso g ∧ (W σ).ι ≫ ξ.1 = g ≫ (x σ).1 := by
    intro σ
    have hb : Basic A B e σ ((functor A B r).map (W σ).ι.op ξ) :=
      (hW σ _ _).1 (by rw [Scheme.Opens.range_ι])
    obtain ⟨g, hg, -⟩ := hXu σ _ _ hb
    obtain ⟨f, hf⟩ : ∃ f, R.homEquiv f = x σ := ⟨_, Equiv.apply_symm_apply _ _⟩
    have hfr : Set.range f ⊆ Set.range (W σ).ι := by
      rw [Scheme.Opens.range_ι]
      exact (hW σ _ f).2 (by rw [← hR, hf]; exact hXb σ)
    let f' := IsOpenImmersion.lift (W σ).ι f hfr
    have hf' : f' ≫ (W σ).ι = f := IsOpenImmersion.lift_fac _ _ _
    have hgf : g ≫ f = (W σ).ι := R.homEquiv.injective (by rw [R.homEquiv_comp, hf, hg, hR])
    have h1 : g ≫ f' = 𝟙 _ := by
      rw [← cancel_mono (W σ).ι, Category.assoc, hf', hgf, Category.id_comp]
    have h2 : f' ≫ g = 𝟙 _ := by
      obtain ⟨g0, -, hu⟩ := hXu σ (X σ) (x σ) (hXb σ)
      have e1 : (functor A B r).map (f' ≫ g).op (x σ) = x σ := by
        rw [← hf, ← R.homEquiv_comp, Category.assoc, hgf, hf']
      have e2 : (functor A B r).map (𝟙 (X σ)).op (x σ) = x σ := by simp
      exact (hu _ e1).trans (hu _ e2).symm
    exact ⟨g, ⟨f', h1, h2⟩, (congrArg Sigma.fst hg).symm⟩
  choose g hg hgx using hiso
  have hWa : ∀ σ, IsAffineOpen (W σ) := fun σ => by
    haveI := hg σ; haveI := hXa σ; exact IsAffine.of_isIso (g σ)
  have hint : ∀ (U : H.Opens), CompactSpace U.toScheme → ∀ τ, IsCompact ((U : Set H) ∩ W τ) := by
    intro U hU τ
    obtain ⟨V, hV, hVc⟩ := GlobalTheory.T.exists_open_affineHilbertChartBasic_locus A B N r e τ U.toScheme ((functor A B r).map U.ι.op ξ)
    have key : ∀ (Z' : Scheme.{0}) (a : Z' ⟶ U.toScheme),
        Set.range a ⊆ V ↔ U.ι '' Set.range a ⊆ W τ := fun Z' a => by
      rw [hV, hmap, ← hW, hrc]
    have hVeq : (V : Set U.toScheme) = U.ι ⁻¹' (W τ) := by
      apply subset_antisymm
      · have := (key _ V.ι).1 (by rw [Scheme.Opens.range_ι])
        rw [Scheme.Opens.range_ι] at this
        exact Set.image_subset_iff.1 this
      · have := (key _ (U.ι ⁻¹ᵁ W τ).ι).2 (by
          rw [Scheme.Opens.range_ι]; exact Set.image_preimage_subset _ _)
        rw [Scheme.Opens.range_ι] at this
        exact this
    have : (U : Set H) ∩ W τ = U.ι '' V := by
      rw [hVeq, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm]
    rw [this]
    exact (hVc hU).image U.ι.continuous
  have hWc' : ∀ σ, CompactSpace (W σ).toScheme := fun σ => by
    haveI : IsAffine (W σ).toScheme := hWa σ
    infer_instance
  refine ⟨?_, ?_, ?_⟩
  · rw [quasiCompact_iff_compactSpace]
    show CompactSpace H
    rw [← isCompact_univ_iff]
    have : (Set.univ : Set H) = ⋃ σ, (W σ : Set H) := by
      rw [← TopologicalSpace.Opens.coe_iSup, hcov]; rfl
    rw [this]
    exact isCompact_iUnion fun σ => (hWa σ).isCompact
  · rw [quasiSeparated_iff_quasiSeparatedSpace]
    exact Scheme.quasiSeparatedSpace_of_isOpenCover W hcov hWa
      (fun σ τ => hint (W σ) (hWc' σ) τ)
  · haveI : IsZariskiLocalAtSource @LocallyOfFiniteType := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFiniteType) W hcov fun σ => ?_
    rw [hgx σ]
    haveI := hg σ
    haveI := hXl σ
    infer_instance

end GlobalTheory.HilbAff
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.invariantDerivation_coeff_eq_zero_of_degree_lt : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R) (r : ℕ), (∀ α : Fin d →₀ ℕ, α.degree < r + 1 → coeff α F = 0) → ∀ α : Fin d →₀ ℕ, α.degree < r → coeff α (invDer μ u F) = 0 := by
  first | exact @GlobalTheory.invDer_coeff_eq_zero_of_degree_lt | exact GlobalTheory.invDer_coeff_eq_zero_of_degree_lt | (intros; apply GlobalTheory.invDer_coeff_eq_zero_of_degree_lt <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.LawDer.IterateLocal

open MvPowerSeries in
set_option autoImplicit false in
private lemma iterate_invDer_sub (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → R) :
    ∀ (m : ℕ) (F G : MvPowerSeries (Fin d) R),
      (_root_.GlobalTheory.LawDer.invDer μ u)^[m] F - (_root_.GlobalTheory.LawDer.invDer μ u)^[m] G =
        (_root_.GlobalTheory.LawDer.invDer μ u)^[m] (F - G) := by
  have hadd := (_root_.GlobalTheory.LawDer.Linear.invDer_linear R d μ hμ u).1
  intro m
  induction m with
  | zero => intro F G; rfl
  | succ m ih =>
    intro F G
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    rw [sub_eq_iff_eq_add, ← hadd, sub_add_cancel]

open MvPowerSeries in
set_option autoImplicit false in
private lemma coeff_iterate_invDer_eq_zero_of_degree_lt (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → R) (N : ℕ) :
    ∀ (m : ℕ) (H : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree < N + m → coeff α H = 0) →
      ∀ α : Fin d →₀ ℕ, α.degree < N →
        coeff α ((_root_.GlobalTheory.LawDer.invDer μ u)^[m] H) = 0 := by
  intro m
  induction m with
  | zero => intro H hH α hα; exact hH α (by simpa using hα)
  | succ m ih =>
    intro H hH α hα
    rw [Function.iterate_succ_apply]
    refine ih _ (fun β hβ => ?_) α hα
    exact _root_.GlobalTheory.invDer_coeff_eq_zero_of_degree_lt R d μ hμ u H (N + m)
      (fun γ hγ => hH γ (by omega)) β hβ


open MvPowerSeries in
set_option autoImplicit false in
theorem _root_.GlobalTheory.LawDer.IterateLocal.constantCoeff_iterate_invDer_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (n : ℕ) (F G : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree ≤ n → coeff α F = coeff α G) → constantCoeff ((_root_.GlobalTheory.LawDer.invDer μ u)^[n] F) = constantCoeff ((_root_.GlobalTheory.LawDer.invDer μ u)^[n] G) := by
  intro R _ d μ hμ u n F G hFG
  rw [← sub_eq_zero, ← map_sub, iterate_invDer_sub R d μ hμ u,
    ← coeff_zero_eq_constantCoeff_apply]
  refine coeff_iterate_invDer_eq_zero_of_degree_lt R d μ hμ u 1 n (F - G) (fun α hα => ?_) 0
    (by simp)
  rw [map_sub, hFG α (by omega), sub_self]

end GlobalTheory.LawDer.IterateLocal
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.norm_iteratedFDeriv_fTerm_le_of_isCompact : ∀ (F : Type) [Field F] [NumberField F] (K : Set ℂ), IsCompact K → K ⊆ halfPlane →
    ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
      ∀ σ ∈ K, ∀ z ∈ L, ∀ b ν : F, b ≠ 0 → ν ≠ 0 →
        ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z b ν) z‖ ≤
          C * ∏ τ : Emb F, (|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N := by
  first | exact @GlobalTheory.HeckeTwo.TermBound.fTerm_iteratedFDeriv_bound | exact GlobalTheory.HeckeTwo.TermBound.fTerm_iteratedFDeriv_bound | (intros; apply GlobalTheory.HeckeTwo.TermBound.fTerm_iteratedFDeriv_bound <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.squareZero_local_lifts_corrected_agree_on_overlaps : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by
  first | exact @GlobalTheory.SecGlue.lifts_corrected_agree_on_overlaps | exact GlobalTheory.SecGlue.lifts_corrected_agree_on_overlaps | (intros; apply GlobalTheory.SecGlue.lifts_corrected_agree_on_overlaps <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.depth_ge_three_finite_etale_punctured_regular : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ∉ maximalIdeal R ^ 2 → ∀ [IsLocalRing (R ⧸ Ideal.span {f})], GlobalTheory.PurityFree (R ⧸ Ideal.span {f}) → ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 2 → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ReciprocityTheory.CA.ModDepthGE R A 3 := by
  first | exact @GlobalTheory.LocalLefschetz.depth_three | exact GlobalTheory.LocalLefschetz.depth_three | (intros; apply GlobalTheory.LocalLefschetz.depth_three <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobKerPrim

theorem mem_frobKerIdeal_of_cobOne (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H] (b : H)
    (_hb : counit (R := K) b = 0) (hd : dUnit (R := K) b = 0)
    (hc : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))
      (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) (cobOne K H b) = 0) :
    b ∈ frobKerIdeal p K H := by
  have hadd {A : Type} [CommRing A] (h : (p : A) = 0) (x y : A) :
      (x + y) ^ p = x ^ p + y ^ p := by
    rw [add_pow_prime_eq (Fact.out : p.Prime), h]; simp
  have hcast (A : Type) [CommRing A] [Algebra K A] : (p : A) = 0 := by
    rw [← map_natCast (algebraMap K A), CharP.cast_eq_zero, map_zero]
  have hmk (x : H) : Ideal.Quotient.mkₐ K (frobKerIdeal p K H) x ^ p =
      algebraMap K _ (counit (R := K) x) ^ p := by
    have hx : x - algebraMap K H (counit (R := K) x) ∈ augIdeal K H := by
      simp [RingHom.mem_ker]
    have h0 : Ideal.Quotient.mkₐ K (frobKerIdeal p K H)
        ((x - algebraMap K H (counit (R := K) x)) ^ p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal hx)
    have e : x = (x - algebraMap K H (counit (R := K) x)) + algebraMap K H (counit (R := K) x) := by ring
    conv_lhs => rw [e, ← map_pow, hadd (hcast H), map_add, h0, zero_add, map_pow, AlgHom.commutes]
  have hmap (t : H ⊗[K] H) :
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))
        (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) t ^ p =
      (1 : H ⧸ frobKerIdeal p K H) ⊗ₜ[K] (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)
        (TensorProduct.lid K H (LinearMap.rTensor H (counit (R := K) (A := H)) t)) ^ p) := by
    induction t with
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [hadd (hcast _), hadd (hcast _), hx, hy, tmul_add]
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow, hmk,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, smul_pow, ← map_pow,
        Algebra.algebraMap_eq_smul_one, smul_tmul]
  haveI : (frobKerIdeal p K H).IsHopfIdeal K := {
    counit_eq_zero x hx := frobKerIdeal_le_augIdeal (Fact.out : p.Prime).ne_zero K H hx
    map_mkQ_comul_eq_zero x hx := by
      have h : frobKerIdeal p K H ≤ RingHom.ker
          ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))
            (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))).comp (comulAlgHom K H)) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, AlgHom.comp_apply, hmap,
          comulAlgHom_apply, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul, ← map_pow]
        have : Ideal.Quotient.mkₐ K (frobKerIdeal p K H) (a ^ p) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
        rw [this, tmul_zero]
      exact h hx
    antipode_mem x hx := by
      have h : frobKerIdeal p K H ≤ (frobKerIdeal p K H).comap (HopfAlgebra.antipodeAlgHom K H) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
        apply pow_mem_frobKerIdeal
        have ha' : counit (R := K) a = 0 := ha
        simp [RingHom.mem_ker, ha']
      exact h hx }
  set J := frobKerIdeal p K H with hJ
  let π : H →ₐc[K] H ⧸ J := Bialgebra.Quotient.mkBialgHom J
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : IsCocomm K (H ⧸ J) := by
    constructor
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hπ y
    have h1 := pullTwo_comul π x
    simp only [LinearMap.comp_apply]
    rw [← h1]
    simp only [pullbackTwo]
    have h2 := TensorProduct.map_comm (π : H →ₗ[K] H ⧸ J) (π : H →ₗ[K] H ⧸ J) (comul x)
    rw [comm_comul] at h2
    exact h2.symm
  have hpow : ∀ a ∈ augIdeal K (H ⧸ J), a ^ p = 0 := by
    intro a ha
    obtain ⟨x, rfl⟩ := hπ a
    have hx : x ∈ augIdeal K H := ha
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal hx)
  have hc' : cobOne K (H ⧸ J) (π b) = 0 := by
    rw [← pullTwo_cobOne]
    exact hc
  have hd' : dUnit (R := K) (π b) = 0 := by
    rw [← cotMap_d, hd, map_zero]
  have h0 := GlobalTheory.T.hopf_height_one_primitive_eq_zero_of_zero_differential p K (H ⧸ J) hpow (π b) hc' hd'
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0

end GlobalTheory.PDiv.FrobKerPrim
end
end

section

open CategoryTheory Limits

theorem _root_.GlobalTheory.T.exists_zmodTorsor_model_of_filtered_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)), GlobalTheory.LocAcyc.IsZModTorsor c.pt D q act →
    ∃ (j : J), letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    ∃ (Dj : Type) (_ : CommRing Dj) (_ : Algebra (F.obj j) Dj)
      (actj : Multiplicative (ZMod q) →* (Dj ≃ₐ[F.obj j] Dj)),
      GlobalTheory.LocAcyc.IsZModTorsor (F.obj j) Dj q actj ∧
      Nonempty (TensorProduct (F.obj j) c.pt Dj ≃ₐ[c.pt] D) := by
  first | (exact @GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit) | (exact GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit) | (intros; apply GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw

theorem _root_.GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_injective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Injective ((etaS q).hom.app (op U)).hom := by
  first | (exact @GlobalTheory.EtC.MuTw.Inj.etaS_injective) | (exact GlobalTheory.EtC.MuTw.Inj.etaS_injective) | (intros; apply GlobalTheory.EtC.MuTw.Inj.etaS_injective  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.injective_projBundleModelCochainComplex_X : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R), (∀ n, CategoryTheory.Injective (I.X n)) → ∀ n, CategoryTheory.Injective ((Jcx R q N I).X n) := by
  first | (exact @GlobalTheory.EtC.Jcx_X_injective) | (exact GlobalTheory.EtC.Jcx_X_injective) | (intros; apply GlobalTheory.EtC.Jcx_X_injective  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.fibre_zero_mem_coinvariants : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB (k := k) a (a + b), GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b) := by
  first | exact @GlobalTheory.RankFibreKer.fibre_ker | exact GlobalTheory.RankFibreKer.fibre_ker | (intros; apply GlobalTheory.RankFibreKer.fibre_ker <;> assumption)
end

section

open GlobalTheory.WeilM Matrix

theorem _root_.GlobalTheory.T.schwartzBruhat_minor_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] [Nonempty T] (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) → ∀ (τ : R → D), ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → ∃ Φ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y : Matrix (R ⊕ T) D k, Y.rank ≤ Fintype.card R → Φ Y = f Y := by
  first | exact @GlobalTheory.RankChart.exists_mem_nsp_eq_of_rank_le | exact GlobalTheory.RankChart.exists_mem_nsp_eq_of_rank_le | (intros; apply GlobalTheory.RankChart.exists_mem_nsp_eq_of_rank_le <;> assumption)
end
