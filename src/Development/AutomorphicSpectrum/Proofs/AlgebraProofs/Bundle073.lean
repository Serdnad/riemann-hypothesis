module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendedBundleGaloisCover
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfFinite
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle012
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle065
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle067
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle072
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle042
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle045
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle061
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle040
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.FinFlatNorm

open TopologicalSpace GlobalTheory.FiniteAmple GlobalTheory.LB ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LBGerm
open GlobalTheory.FlatNorm (nm nm_of_isPushout isUnit_of_nm exists_preimage_le)

variable {X Y : Scheme.{0}} (π : Y ⟶ X) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]

theorem exists_finFree_app_of_finitePresentation {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U ∧ FinFree (π.app V).hom := by
  apply GlobalTheory.FiniteAmpleFP.exists_finFree_app_fp <;> assumption

abbrev FreeOpen (V : X.Opens) : Type := {W : X.Opens // IsAffineOpen W ∧ W ≤ V ∧ FinFree (π.app W).hom}

theorem le_iSup_freeOpen (V : X.Opens) : V ≤ ⨆ W : FreeOpen π V, W.1 := by
  intro x hx
  obtain ⟨W, hW, hxW, hWV, hF⟩ := exists_finFree_app_of_finitePresentation π hx
  exact Opens.mem_iSup.mpr ⟨⟨W, hW, hWV, hF⟩, hxW⟩

theorem ext_freeOpen {V : X.Opens} {a b : Γ(X, V)}
    (h : ∀ W : FreeOpen π V, resG X W.2.2.1 a = resG X W.2.2.1 b) : a = b := by
  refine TopCat.Presheaf.section_ext X.sheaf V a b fun x hx => ?_
  obtain ⟨W, hxW⟩ := Opens.mem_iSup.mp (le_iSup_freeOpen π V hx)
  have e := congrArg (X.presheaf.germ W.1 x hxW).hom (h W)
  simp [resG] at e
  exact e

omit [Flat π] [LocallyOfFinitePresentation π] in
theorem resG_nm {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V)
    (hF : FinFree (π.app V).hom) (b : Γ(Y, π ⁻¹ᵁ V)) :
    resG X h (nm (π.app V).hom b) = nm (π.app W).hom (resG Y (π.preimage_mono h) b) := by
  exact (nm_of_isPushout (isPushout_app π hV hW h) hF b).symm

private theorem resG_nm_app_eq_nm_app_of_le_freeOpen {V : X.Opens} (b : Γ(Y, π ⁻¹ᵁ V)) (k : FreeOpen π V) {W' : X.Opens}
    (hW' : IsAffineOpen W') (h : W' ≤ k.1) :
    resG X h (nm (π.app k.1).hom (resG Y (π.preimage_mono k.2.2.1) b)) =
      nm (π.app W').hom (resG Y (π.preimage_mono (h.trans k.2.2.1)) b) := by
  rw [resG_nm π k.2.1 hW' h k.2.2.2, resG_resG]

theorem exists_normFun (V : X.Opens) (b : Γ(Y, π ⁻¹ᵁ V)) : ∃ a : Γ(X, V), ∀ W : FreeOpen π V,
    resG X W.2.2.1 a = nm (π.app W.1).hom (resG Y (π.preimage_mono W.2.2.1) b) := by
  refine exists_fun_of_cover (fun k : FreeOpen π V => k.1) (fun k => k.2.2.1) (le_iSup_freeOpen π V)
    (fun k => nm (π.app k.1).hom (resG Y (π.preimage_mono k.2.2.1) b)) fun k l => ?_
  refine ext_freeOpen π fun W' => ?_
  rw [resG_resG, resG_resG, resG_nm_app_eq_nm_app_of_le_freeOpen π b k W'.2.1, resG_nm_app_eq_nm_app_of_le_freeOpen π b l W'.2.1]

def normFun (V : X.Opens) : Γ(Y, π ⁻¹ᵁ V) →* Γ(X, V) where
  toFun b := (exists_normFun π V b).choose
  map_one' := ext_freeOpen π fun W => by
    rw [(exists_normFun π V 1).choose_spec W, map_one, map_one, map_one]
  map_mul' a b := ext_freeOpen π fun W => by
    rw [(exists_normFun π V _).choose_spec W, map_mul, map_mul, map_mul,
      (exists_normFun π V a).choose_spec W, (exists_normFun π V b).choose_spec W]

theorem resG_normFun_free {V : X.Opens} (b : Γ(Y, π ⁻¹ᵁ V)) (W : FreeOpen π V) :
    resG X W.2.2.1 (normFun π V b) = nm (π.app W.1).hom (resG Y (π.preimage_mono W.2.2.1) b) := by
  exact (exists_normFun π V b).choose_spec W

theorem resG_normFun {V W : X.Opens} (h : W ≤ V) (b : Γ(Y, π ⁻¹ᵁ V)) :
    resG X h (normFun π V b) = normFun π W (resG Y (π.preimage_mono h) b) := by
  refine ext_freeOpen π fun W' => ?_
  rw [resG_resG, resG_normFun_free π b ⟨W'.1, W'.2.1, W'.2.2.1.trans h, W'.2.2.2⟩,
    resG_normFun_free π _ W', resG_resG]

private theorem basicOpen_resG_eq_inf_basicOpen {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (f : Γ(Z, U)) :
    Z.basicOpen (resG Z h f) = V ⊓ Z.basicOpen f :=
  Z.basicOpen_res f (homOfLE h).op

private theorem isUnit_resG_of_le_basicOpen' {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (f : Γ(Z, U))
    (hV : V ≤ Z.basicOpen f) : IsUnit (resG Z h f) := by
  rw [← resG_resG (Z.basicOpen_le f) hV f]
  exact (RingedSpace.isUnit_res_basicOpen _ f).map (resG Z hV)

theorem mem_basicOpen_normFun {V : X.Opens} (b : Γ(Y, π ⁻¹ᵁ V)) {x : X} (hx : x ∈ V) :
    x ∈ X.basicOpen (normFun π V b) ↔ ∀ y, π y = x → y ∈ Y.basicOpen b := by
  obtain ⟨W, hW, hxW, hWV, hF⟩ := exists_finFree_app_of_finitePresentation π hx
  have e0 := resG_normFun_free π b ⟨W, hW, hWV, hF⟩
  have key : x ∈ X.basicOpen (normFun π V b) ↔
      x ∈ X.basicOpen (nm (π.app W).hom (resG Y (π.preimage_mono hWV) b)) := by
    rw [← e0, basicOpen_resG_eq_inf_basicOpen]
    exact ⟨fun h => ⟨hxW, h⟩, fun h => h.2⟩
  rw [key]
  constructor
  · intro hx' y hy
    obtain ⟨W'', hW'', hxW'', hle, hF''⟩ := exists_finFree_app_of_finitePresentation π hx'
    have hW''W : W'' ≤ W := hle.trans (X.basicOpen_le _)
    have hu := isUnit_resG_of_le_basicOpen' hW''W _ hle
    rw [resG_nm π hW hW'' hW''W hF, resG_resG] at hu
    have hu' := isUnit_of_nm hF'' hu
    have hy'' : y ∈ Y.basicOpen (resG Y (π.preimage_mono (hW''W.trans hWV)) b) := by
      rw [Y.basicOpen_of_isUnit hu']
      show π y ∈ W''
      rw [hy]
      exact hxW''
    rw [basicOpen_resG_eq_inf_basicOpen] at hy''
    exact hy''.2
  · intro hall
    have hall' : ∀ y, π y = x → y ∈ Y.basicOpen (resG Y (π.preimage_mono hWV) b) := by
      intro y hy
      rw [basicOpen_resG_eq_inf_basicOpen]
      refine ⟨?_, hall y hy⟩
      show π y ∈ W
      rw [hy]
      exact hxW
    obtain ⟨V', hxV', hV'⟩ := exists_preimage_le π hall'
    obtain ⟨W'', hW'', hxW'', hle, hF''⟩ :=
      exists_finFree_app_of_finitePresentation π (U := W ⊓ V') ⟨hxW, hxV'⟩
    have hW''W : W'' ≤ W := hle.trans inf_le_left
    have hu := isUnit_resG_of_le_basicOpen' (π.preimage_mono hW''W) (resG Y (π.preimage_mono hWV) b)
      ((π.preimage_mono (hle.trans inf_le_right)).trans hV')
    have hu2 := hu.map (nm (π.app W'').hom)
    rw [← resG_nm π hW hW'' hW''W hF] at hu2
    have h3 : x ∈ X.basicOpen (resG X hW''W (nm (π.app W).hom (resG Y (π.preimage_mono hWV) b))) := by
      rw [X.basicOpen_of_isUnit hu2]
      exact hxW''
    rw [basicOpen_resG_eq_inf_basicOpen] at h3
    exact h3.2

end GlobalTheory.CompanionTheory.FinFlatNorm


open GlobalTheory.CompanionTheory.FinFlatNorm in
theorem GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf : ∀ {X Y : Scheme.{0}} (q : X ⟶ Y), IsFinite q → Flat q → LocallyOfFinitePresentation q → ∃ N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V), (∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)), (Y.presheaf.map (homOfLE h).op).hom (N V a) = N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)) ∧ ∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V → (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a) := by
  intro X Y q h1 h2 h3
  exact ⟨normFun q, fun V W h a => resG_normFun q h a, fun V a y hy => mem_basicOpen_normFun q a hy⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_orthogonal_local_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes) (x' : Fin p → D.La), p + q = D.p + D.q → (gramE D x').det ≠ 0 → (∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ = -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → ∃ x : Fin p ⊕ Fin q → D.La, x ∘ Sum.inl = x' ∧ IsLocBasis (𝓞 E) ℓ x ∧ ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0 := by
  exact @PositivityTheory.Xgf.exists_orthogonal_local_basis
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_local_basis_cm_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : ℕ), ℓ.Prime → ∃ (f : ℕ) (b : Fin f → 𝓞 E), 2 * f = Module.finrank ℚ E ∧ IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order | exact GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_local_basis' : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M] (I : Type) [Fintype I] (ℓ : ℕ), ℓ.Prime → Fintype.card I = Module.finrank (𝓞 E) M → ∃ x : I → M, IsLocBasis (𝓞 E) ℓ x := by
  first | exact @PositivityTheory.Xgf.exists_local_basis' | exact PositivityTheory.Xgf.exists_local_basis'
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot


theorem _root_.GlobalTheory.T.finite_flat_locally_free_affine : ∀ {Y S : Scheme.{0}} (g : Y ⟶ S) [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] (s : S), ∃ W : S.Opens, s ∈ W ∧ IsAffineOpen W ∧ GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom (g ∣_ W).appTop.hom := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.exists_affine_finiteFreeHom | exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.exists_affine_finiteFreeHom | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.exists_affine_finiteFreeHom <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem fubini_study_sum_crofton {n e δ : ℕ} (h : HermNorm n) (u : Fin n → ℂ)
    (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ)
    (hc : (fibrePts S π).encard = δ)
    (hs : ∑' y : fibrePts S π, logGap h u y < ⊤) :
    (∑' y : fibrePts S π, logGap h u y).toReal = δ * Real.log (h.norm u) - fsSum h u S π := by
  have hfin : (fibrePts S π).Finite := Set.finite_of_encard_eq_coe hc
  have hcard : hfin.toFinset.card = δ := by
    have h1 := hfin.encard_eq_coe_toFinset_card
    rw [hc] at h1
    exact_mod_cast h1.symm
  have hne0 : ∀ y ∈ fibrePts S π, y ≠ 0 := by
    rintro y ⟨-, hy⟩ rfl
    have h2 := congrArg (fun v : EuclideanSpace ℂ (Fin (e + 1)) => v.ofLp 0) hy
    simp [linProj, firstCoordVec] at h2
  have hsum : ∀ y ∈ fibrePts S π, ∑ j, u j * h.pointOf y j ≠ 0 := by
    intro y hy h0
    have htop : logGap h u y = ⊤ := by simp [logGap, hne0 y hy, h0]
    have hle : logGap h u y ≤ ∑' z : fibrePts S π, logGap h u z :=
      ENNReal.le_tsum (f := fun z : fibrePts S π => logGap h u z) ⟨y, hy⟩
    rw [htop] at hle
    exact absurd hs (not_lt.2 hle)
  have hval : ∀ y ∈ fibrePts S π,
      logGap h u y = ENNReal.ofReal (Real.log (h.norm u) - fsLog h u (h.pointOf y)) := by
    intro y hy
    simp [logGap, hne0 y hy, hsum y hy]
  have hnn : ∀ y ∈ fibrePts S π, 0 ≤ Real.log (h.norm u) - fsLog h u (h.pointOf y) := fun y hy =>
    sub_nonneg.2 (GlobalTheory.T.fubini_study_log_le_log_norm n h u y (hne0 y hy) (hsum y hy))
  haveI : Fintype (fibrePts S π) := hfin.fintype
  have htsum : ∑' z : fibrePts S π, logGap h u z = ∑ y ∈ hfin.toFinset, logGap h u y := by
    rw [tsum_fintype]
    exact (Finset.sum_subtype hfin.toFinset (fun y => hfin.mem_toFinset) (logGap h u)).symm
  rw [htsum, ENNReal.toReal_sum (fun y hy => by
      rw [hval y (hfin.mem_toFinset.1 hy)]
      exact ENNReal.ofReal_ne_top)]
  rw [Finset.sum_congr rfl (fun y hy => by
      rw [hval y (hfin.mem_toFinset.1 hy), ENNReal.toReal_ofReal (hnn y (hfin.mem_toFinset.1 hy))])]
  rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, fsSum,
    finsum_mem_eq_finite_toFinset_sum _ hfin]

end GlobalTheory.CompanionTheory.Ar.Short.Crofton

private theorem tsum_fibre_pts_eq_sum {n e : ℕ} (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ)
    (hfin : (fibrePts S π).Finite) (g : EuclideanSpace ℂ (Fin n) → ℝ≥0∞) :
    ∑' y : fibrePts S π, g y = ∑ y ∈ hfin.toFinset, g y := by
  haveI : Fintype (fibrePts S π) := hfin.fintype
  rw [tsum_fintype]
  exact (Finset.sum_subtype hfin.toFinset (fun y => hfin.mem_toFinset) g).symm

private theorem ne_zero_of_mem_fibre_pts {n e : ℕ} (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ fibrePts S π) : y ≠ 0 := by
  rintro rfl
  obtain ⟨-, h0⟩ := hy
  have h2 := congrArg (fun v : EuclideanSpace ℂ (Fin (e + 1)) => v.ofLp 0) h0
  simp [linProj, firstCoordVec] at h2

theorem GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f → GroundTheory.Heights₂.Heights.linForm u ∉ W →
    Integrable (fsSum h u (coneSet h W)) (gaussM (e + 1) n) ∧
      ∫ π, fsSum h u (coneSet h W) π ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * coneIntegral h W e (fsLog h u) := by
  intro n e δ h W f u hW hf hδ hu
  obtain ⟨hLGm, hLGo⟩ := GlobalTheory.T.log_gap_measurable_scale_stable n h u
  obtain ⟨hGm, hGeq⟩ := GlobalTheory.T.crofton_formula_fibre_sum n e δ h W f hW hf hδ (logGap h u) hLGm hLGo
  obtain ⟨hL, hLr⟩ := GlobalTheory.T.cone_ball_log_gap_integral n e h W f u hW hf hu
  obtain ⟨hμ0, hμt⟩ := GlobalTheory.T.gaussian_matrix_measure_pos_finite (e + 1) n
  obtain ⟨hpm0, hpmt⟩ : 0 < planeMass n e ∧ planeMass n e < ⊤ :=
    GroundTheory.Heights₂.Heights.coordBall_mass (chowGroups_le hW hf hδ)
  have hac : gaussM (e + 1) n ≪ (volume : Measure (Fin (e + 1) → Fin n → ℂ)) :=
    withDensity_absolutelyContinuous _ _
  have hcnt : ∀ᵐ π ∂(gaussM (e + 1) n), (fibrePts (coneSet h W) π).encard = δ :=
    hac.ae_le (GlobalTheory.T.ae_fibre_points_card_eq_degree n e δ h W f hW hf hδ)
  have hd : (0 : ℝ) < ((2 * (e + 1) : ℕ) : ℝ) := by positivity
  haveI := MeasureTheory.Measure.nullSingletonClass_hausdorff (EuclideanSpace ℂ (Fin n)) hd
  have hφm : Measurable (({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (measurableSet_singleton 0).compl
  have hφo : ∀ s : ℝ≥0∞,
      IsOpen {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} ∧
      IsScaleStable {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} := by
    intro s
    by_cases hs1 : s < 1
    · have hset : {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} =
          {0}ᶜ := by
        ext y
        by_cases hy : y = 0
        · simp [Set.indicator_apply, hy]
        · simp [Set.indicator_apply, hy, hs1]
      rw [hset]
      exact ⟨isOpen_compl_singleton, fun y hy t ht => by simpa [ht] using hy⟩
    · have hset : {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} =
          ∅ := by
        ext y
        by_cases hy : y = 0
        · simp [Set.indicator_apply, hy]
        · simp [Set.indicator_apply, hy, hs1]
      rw [hset]
      exact ⟨isOpen_empty, fun y hy => hy.elim⟩
  obtain ⟨-, hCeq⟩ := GlobalTheory.T.crofton_formula_fibre_sum n e δ h W f hW hf hδ _ hφm hφo
  have hae1 : ∀ᵐ π ∂(gaussM (e + 1) n), ∑' y : fibrePts (coneSet h W) π,
      ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y = δ := by
    filter_upwards [hcnt] with π hπ
    have hfin : (fibrePts (coneSet h W) π).Finite := Set.finite_of_encard_eq_coe hπ
    have hcard : hfin.toFinset.card = δ := by
      have h1 := hfin.encard_eq_coe_toFinset_card
      rw [hπ] at h1
      exact_mod_cast h1.symm
    have h1 : ∀ y ∈ hfin.toFinset,
        ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y = 1 := fun y hy =>
      Set.indicator_of_mem (ne_zero_of_mem_fibre_pts _ π y (hfin.mem_toFinset.1 hy)) _
    rw [tsum_fibre_pts_eq_sum _ π hfin, Finset.sum_congr rfl h1, Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
  have hball : ∫⁻ y in coneBall h W, ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y
      ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) := by
    rw [lintegral_indicator_const (measurableSet_singleton 0).compl, one_mul,
      Measure.restrict_apply (measurableSet_singleton 0).compl, Set.inter_comm, ← Set.sdiff_eq,
      measure_sdiff_null (measure_singleton 0)]
  rw [lintegral_congr_ae hae1, lintegral_const, hball] at hCeq
  have hHc : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) = δ * planeMass n e := by
    have h2 : gaussM (e + 1) n Set.univ * (δ * planeMass n e) =
        gaussM (e + 1) n Set.univ * Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) := by
      rw [← hCeq]
      ring
    exact ((ENNReal.mul_right_inj hμ0.ne' hμt.ne).1 h2).symm
  have hGfin : ∫⁻ π, ∑' y : fibrePts (coneSet h W) π, logGap h u y ∂(gaussM (e + 1) n) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hpm0.ne'] at hGeq
    exact ENNReal.mul_ne_top hμt.ne hL.ne hGeq.symm
  have hGae := ae_lt_top hGm hGfin
  have hfs : ∀ᵐ π ∂(gaussM (e + 1) n), fsSum h u (coneSet h W) π =
      δ * Real.log (h.norm u) - (∑' y : fibrePts (coneSet h W) π, logGap h u y).toReal := by
    filter_upwards [hcnt, hGae] with π h1 h2
    rw [fubini_study_sum_crofton h u _ π h1 h2]
    ring
  haveI : IsFiniteMeasure (gaussM (e + 1) n) := ⟨hμt⟩
  have hGint := integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hGfin
  have hint : Integrable (fun π => (δ : ℝ) * Real.log (h.norm u) -
      (∑' y : fibrePts (coneSet h W) π, logGap h u y).toReal) (gaussM (e + 1) n) :=
    (integrable_const _).sub hGint
  refine ⟨hint.congr (hfs.mono fun π hπ => hπ.symm), ?_⟩
  rw [integral_congr_ae hfs, integral_sub (integrable_const _) hGint, integral_const,
    integral_toReal hGm.aemeasurable hGae, measureReal_def, smul_eq_mul]
  have hX := congrArg ENNReal.toReal hGeq
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, hLr, hHc, ENNReal.toReal_mul, ENNReal.toReal_natCast] at hX
  have hpmr : 0 < (planeMass n e).toReal := ENNReal.toReal_pos hpm0.ne' hpmt.ne
  have hci : coneIntegral h W e (fsLog h u) = (∫ y in coneBall h W, fsLog h u (h.pointOf y)
      ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))) / (planeMass n e).toReal := rfl
  rw [hci]
  have alg : ∀ a p X lg d I : ℝ, p ≠ 0 → p * X = a * (lg * (d * p) - I) →
      a * (d * lg) - X = a * (I / p) := by
    intro a p X lg d I hp hX'
    have hX'' : X = a * (lg * (d * p) - I) / p := by
      rw [eq_div_iff hp, mul_comm]
      exact hX'
    rw [hX'']
    field_simp
    ring
  exact alg _ _ _ _ _ _ hpmr.ne' hX
end
