module

public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle084
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle098
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import Development.WeilBound.CoreStatements.FlagImmersions.ExistsUnitMetric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle138
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle131
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

theorem chiEx : ChiEx := by
  intro E _ _ _ H _
  haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩
  have h4 : H.d % 4 = 3 := by
    have := H.d_mod
    omega
  refine ⟨(quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ), GlobalTheory.isKroneckerChar_quadraticChar h4, ?_⟩
  have hr : rootDiscr E = hostRd E := by
    simp [rootDiscr_def, hostRd, Int.cast_abs, one_div]
  have hpos : 0 < hostRd E := by
    unfold hostRd
    apply Real.rpow_pos_of_pos
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
  simp only [GlobalTheory.CM.logOm, hostLval]
  rw [Complex.sub_re, Complex.ofReal_re, hr, Real.log_div (by positivity) hpos.ne']
  ring

end RootFieldNumerics.RF
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF.Loc

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unit_of_val {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R}
    (h : genPt ξ ⤳ centre z) (hv : ValAt ξ z a r) (hr : IsUnit r) : unitAt ξ ⟨centre z, h⟩ a := by
  obtain ⟨h', x, rfl, rfl⟩ := hv
  obtain ⟨x, rfl⟩ : IsUnit x := (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo z).hom).map_nonunit x hr
  exact ⟨(x.isUnit.map (genMap ξ ⟨centre z, h'⟩)).ne_zero, ⟨x.val, rfl⟩, ⟨x⁻¹.val, map_units_inv _ x⟩⟩

variable {L : Type} [Field L] {z : Spec (CommRingCat.of L) ⟶ X}

theorem val_mul {a b : Ω} {r s : L} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨_, y, rfl, rfl⟩ := h'
  exact ⟨h, x * y, map_mul _ _ _, map_mul _ _ _⟩

theorem val_pow {a : Ω} {r : L} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  exact ⟨h, x ^ n, map_pow _ _ _, map_pow _ _ _⟩

theorem val_inv {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨x, rfl⟩ : IsUnit x :=
    (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo z).hom).map_nonunit x (IsUnit.mk0 _ hr)
  exact ⟨h, x⁻¹.val, map_units_inv _ x, map_units_inv _ x⟩

theorem val_zpow {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) (n : ℤ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using val_pow h n
  · simpa using val_inv (val_pow h n) (pow_ne_zero _ hr)

end Val

theorem frame_of_matrix {S : Scheme.{0}} {L : Type} [Field L] {G : Over S} [GrpObj G] [IsCommMonObj G] {x₀ : Sp L ⟶ S}
    {W : Type} [AddCommGroup W] [Module L W] (M : LieModel G x₀ W) {O : Type} [CommRing O] (act : OAct O G)
    (ρ : O →+* Module.End L W) (σ : O →+* L) (hM : M.IsActOf act.act ρ) {n : ℕ} (x : Fin n → W)
    (hx : IsEigFrame act x₀ σ fun k => M.pt (x k)) (P : Matrix (Fin n) (Fin n) L) (hP : P.det ≠ 0) :
    LinearIndependent L (fun k => ∑ i, P k i • x i) ∧ IsEigFrame act x₀ σ (fun k => M.pt (∑ i, P k i • x i)) ∧
      ∀ k, IsComb (P k) (fun i => M.pt (x i)) (M.pt (∑ i, P k i • x i)) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.T.eigen_frame_iff_eigenspace_basis S L G x₀ W M O act ρ σ n x hM).1 hx
  have hU : IsUnit P.det := IsUnit.mk0 _ hP
  have key : ∀ u : Fin n → L, ∑ k, u k • ∑ i, P k i • x i = ∑ i, (Matrix.vecMul u P) i • x i := fun u => by
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have huniq : ∀ e ∈ eigSp ρ σ, ∃! cf : Fin n → L, e = ∑ k, cf k • ∑ i, P k i • x i := fun e he => by
    obtain ⟨cf, hcf, hu⟩ := h2 e he
    refine ⟨Matrix.vecMul cf P⁻¹, ?_, fun u h => ?_⟩
    · change e = ∑ k, (Matrix.vecMul cf P⁻¹) k • ∑ i, P k i • x i
      rw [key, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hU, Matrix.vecMul_one]
      exact hcf
    · have e1 : Matrix.vecMul u P = cf := hu _ (h.trans (key u))
      rw [← e1, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hU, Matrix.vecMul_one]
  refine ⟨Fintype.linearIndependent_iff.2 fun u hu k => ?_, ?_, fun k => ?_⟩
  · obtain ⟨cf, -, h0⟩ := huniq 0 (Submodule.zero_mem _)
    have e1 : u = cf := h0 u hu.symm
    have e2 : (0 : Fin n → L) = cf := h0 0 (by simp)
    rw [e1, ← e2]
    rfl
  · exact (GlobalTheory.T.eigen_frame_iff_eigenspace_basis S L G x₀ W M O act ρ σ n (fun k => ∑ i, P k i • x i) hM).2
      ⟨fun k => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h1 i), huniq⟩
  · exact (GlobalTheory.T.is_comb_tangent_iff_linear_sum S L G x₀ W M n x (P k) _).2 rfl

theorem tied_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type}
    [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} {F : Type} [Field F]
    {z : Spec (CommRingCat.of F) ⟶ 𝔐.X} {y₀ : Sp F ⟶ Xo.XF c} {vb : epsAt z ⟶ 𝔐.t.G}
    {v v' : epsAt (under y₀) ⟶ Xo.univ.t.G} (h : Tied 𝔐 z y₀ vb v) (h' : Tied 𝔐 z y₀ vb v') : v = v' := by
  obtain ⟨u, h1, h2⟩ := h
  obtain ⟨u', h1', h2'⟩ := h'
  obtain rfl : u = u' := Over.OverMorphism.ext (h2.symm.trans h2')
  exact h1.unique_left h1'

end RootFieldNumerics.RF.Loc
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

private theorem noetherianSpace_projectiveSpectrum {A σ : Type} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℕ → σ)
    [GradedRing 𝒜] [IsNoetherianRing A] : TopologicalSpace.NoetherianSpace (ProjectiveSpectrum 𝒜) := by
  let f : ProjectiveSpectrum 𝒜 → PrimeSpectrum A := fun p => ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩
  have hf : Topology.IsInducing f := by
    refine ⟨TopologicalSpace.ext_iff_isClosed.2 fun s => ?_⟩
    rw [isClosed_induced_iff, ProjectiveSpectrum.isClosed_iff_zeroLocus]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨PrimeSpectrum.zeroLocus t, PrimeSpectrum.isClosed_zeroLocus t, ?_⟩
      ext x
      simp [f, ProjectiveSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus]
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨u, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus t).1 ht
      refine ⟨u, ?_⟩
      ext x
      simp [f, ProjectiveSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus]
  exact hf.noetherianSpace

theorem cptEx : CptEx := by
  intro E _ _ _ H D l Xo c _ Y S Ω _ K _ J _ y 𝔐
  have hfr : ∀ x : ↥c.F, ∃ (a b : 𝓞 ↥c.F), (algebraMap (𝓞 ↥c.F) ↥c.F) b ≠ 0 ∧ x * (algebraMap (𝓞 ↥c.F) ↥c.F) b = (algebraMap (𝓞 ↥c.F) ↥c.F) a := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 ↥c.F) x
    have hb' : (algebraMap (𝓞 ↥c.F) ↥c.F) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩
  have hinj : Function.Injective (algebraMap (𝓞 ↥c.F) ↥c.F) := IsFractionRing.injective _ _
  obtain ⟨hpre, hflat⟩ := GlobalTheory.CompanionTheory.Ar.Flat.spMap_flat_preimmersion (algebraMap (𝓞 ↥c.F) ↥c.F) hinj hfr
  obtain ⟨jpre, jflat⟩ := GlobalTheory.CompanionTheory.Ar.Flat.j_flat_preimmersion Y hinj hfr
  haveI := hpre
  haveI := jpre
  haveI := Y.jQ_open
  haveI : TopologicalSpace.NoetherianSpace Y.X := by
    obtain ⟨N, i, hi, -⟩ := Y.proj
    have : TopologicalSpace.NoetherianSpace (PSpace (𝓞 ↥c.F) N) := by
      unfold PSpace
      letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := 𝓞 ↥c.F)
      exact noetherianSpace_projectiveSpectrum _
    exact i.isClosedEmbedding.isInducing.noetherianSpace
  have hfx : 𝔐.f (genPt 𝔐.ξ) = genPt 𝔐.ξ₀ := GlobalTheory.CompanionTheory.Ar.Dominates.map_genPt 𝔐.fn_over
  have hsx : Y.s (genPt 𝔐.ξ₀) ∈ Set.range (spMap (algebraMap (𝓞 ↥c.F) ↥c.F)) := by
    refine ⟨spMap 𝔐.cst (IsLocalRing.closedPoint Ω), ?_⟩
    have h2 := congrArg (fun g => g (IsLocalRing.closedPoint Ω)) 𝔐.cst_over
    have h3 : spMap (𝔐.cst.comp (algebraMap (𝓞 ↥c.F) ↥c.F)) = spMap 𝔐.cst ≫ spMap (algebraMap (𝓞 ↥c.F) ↥c.F) := by
      simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [h3] at h2
    simp only [Scheme.Hom.comp_apply] at h2
    rw [← hfx]
    exact h2.symm
  have hsx2 : genPt 𝔐.ξ₀ ∈ Set.range (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))) := by
    rw [Scheme.Pullback.range_fst]
    exact hsx
  obtain ⟨x', hx'⟩ := hsx2
  have hgen : ∀ {p z : ↥Y.X}, genPt 𝔐.ξ₀ ⤳ p → z ⤳ p → genPt 𝔐.ξ₀ ⤳ z := fun hp hz =>
    GlobalTheory.CompanionTheory.Ar.Flat.genPt_specializes_of_specializes 𝔐.ξ₀ 𝔐.gen₀ hp hz
  have hopen : IsOpen (closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)) := by
    refine GlobalTheory.CompanionTheory.Ar.Flat.isOpen_of_isClosed_of_generizing _ isClosed_closure ?_
    intro a b hab hb
    exact specializes_iff_mem_closure.1 (hgen (specializes_iff_mem_closure.2 hb) hab)
  have hV : IsOpen ((pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base ⁻¹' closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)) :=
    hopen.preimage (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).continuous
  obtain ⟨q, hqV, u0, rfl⟩ := Y.jQ_dense.inter_open_nonempty _ hV
    ⟨x', by
      show (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base x' ∈ closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)
      rw [hx']
      exact subset_closure rfl⟩
  have hsp : x' ⤳ Y.jQ u0 := by
    rw [← (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).isEmbedding.isInducing.specializes_iff, hx']
    exact specializes_iff_mem_closure.2 hqV
  obtain ⟨u, hu⟩ := hsp.mem_open Y.jQ.isOpenEmbedding.isOpen_range ⟨u0, rfl⟩
  have hju : Y.j u = genPt 𝔐.ξ₀ := by
    show (Y.jQ ≫ pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base u = genPt 𝔐.ξ₀
    rw [Scheme.Hom.comp_apply, hu, hx']
  have hmin : ∀ z, z ⤳ u → z = u := by
    intro z hz
    have h1 : Y.j z ⤳ genPt 𝔐.ξ₀ := hju ▸ hz.map Y.j.continuous
    have h2 : genPt 𝔐.ξ₀ ⤳ Y.j z := hgen (specializes_refl _) h1
    exact Y.j.isEmbedding.injective ((h1.antisymm h2).eq.trans hju.symm)
  obtain ⟨U, hU, huU⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {u} isIrreducible_singleton
  obtain ⟨Z⟩ := GlobalTheory.CompanionTheory.Ar.Flat.nonempty_cptOver_of_fraction hinj hfr Y U hU
  have hZu : genPt Z.ξ₀ = u := hmin _ ((Z.closure u).1 (huU rfl))
  obtain ⟨U', hU', -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.cptOver_isOpen_isDomain E H D l Xo c (𝓞 ↥c.F) (algebraMap (𝓞 ↥c.F) ↥c.F) Y U Z
    ⟨hinj, inferInstance, hfr⟩
  refine ⟨U, Z, ⟨isClosed_of_mem_irreducibleComponents U hU, hU' ▸ U'.isOpen⟩, hU.1, ?_⟩
  have : genPt (Z.ξ₀ ≫ Y.j) = Y.j (genPt Z.ξ₀) := by
    unfold genPt
    exact Scheme.Hom.comp_apply _ _ _
  rw [this, hZu, hju]

end RootFieldNumerics.RF
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
  GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

namespace RootFieldNumerics.RF

namespace Smooth

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem mem_genFibre (z : Spec (CommRingCat.of ℂ) ⟶ X) (hc : genPt ξ ⤳ centre z) :
    (⟨centre z, hc⟩ : Cpt ξ) ∈ genFibre ℤ ξ := by
  intro o ho
  have h1 : ValAt ξ z (o : Ω) (o : ℂ) := LiesOver.valAt_int hc o
  have h2 := CxVal.inv h1 (by exact_mod_cast ho)
  have h3 := CxVal.mul h1 h2
  have h0 : (o : Ω) ≠ 0 := by
    intro h
    have h4 : ValAt ξ z (0 : Ω) (0 : ℂ) := by simpa using LiesOver.valAt_int hc 0
    rw [h] at h1
    exact ho (by exact_mod_cast CxVal.unique h1 h4)
  obtain ⟨_, s, e, -⟩ := h1
  obtain ⟨_, s', e', -⟩ := h2
  exact ⟨by simpa using h0, ⟨s, by simpa using e⟩, ⟨s', by simpa using e'⟩⟩

theorem val_ne_zero {z : Spec (CommRingCat.of ℂ) ⟶ X} {hc : genPt ξ ⤳ centre z} {u : Ω} {r : ℂ}
    (hu : unitAt ξ ⟨centre z, hc⟩ u) (hr : ValAt ξ z u r) : r ≠ 0 := by
  obtain ⟨s, hs⟩ := hu.2.2
  have h1 := CxVal.mul hr (⟨hc, s, hs, rfl⟩ : ValAt ξ z u⁻¹ _)
  rw [mul_inv_cancel₀ hu.1] at h1
  exact left_ne_zero_of_mul_eq_one (CxVal.unique h1 (CxVal.one hc))

theorem unitAt_of_span {p : Cpt ξ} {s t : Ω} (hs : s ≠ 0) (ht : t ≠ 0)
    (h : Submodule.span (regAt ξ p) {s} = Submodule.span (regAt ξ p) {t}) : unitAt ξ p (s / t) := by
  have key : ∀ {s t : Ω}, t ≠ 0 → s ∈ Submodule.span (regAt ξ p) {t} → s / t ∈ regAt ξ p := by
    intro s t ht hm
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hm
    have : s / t = r := by
      rw [← hr]
      exact mul_div_cancel_right₀ _ ht
    rw [this]
    exact r.2
  refine ⟨div_ne_zero hs ht, key ht (h ▸ Submodule.mem_span_singleton_self s), ?_⟩
  rw [inv_div]
  exact key hs (h ▸ Submodule.mem_span_singleton_self t)

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem pres_on (hT : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) {L : Lat ξ Ω} {a : K → ℤ} {e₀ c₀ : Ω}
    (hD : L.IsDegOn Set.univ y a e₀) (hg : ∀ p ∈ genFibre ℤ ξ, L.IsGenAt p (c₀ * e₀))
    {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y)) :
    ∃ g h dg dh, Pres y a c₀ g h dg dh ∧ evC w g ≠ 0 ∧ evC w h ≠ 0 := by
  classical
  obtain ⟨z, hz, hco⟩ := SheetDecomposition.ChartForm.exists_point hT w
    (fun k => (hw.1 k).imp fun _ h => IsUnit.mk0 _ h) (fun g hg => by rw [← evC_eq]; exact hw.2 g hg)
  choose c hc using hco.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hco.2 k _ (hc k)).1
  have hY : ∀ m : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
  have hW : ∀ m : K → ℕ, (∏ k, w ⟨k, c k⟩ ^ m k) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k).ne_zero
  have hxc : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  let p : Cpt ξ := ⟨centre z, hz⟩
  have hch : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p := by
    refine ⟨hxc, fun c' => ?_⟩
    show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ _
    rw [← Finset.prod_div_distrib]
    refine Subring.prod_mem _ fun k _ => ?_
    obtain ⟨r, ⟨_, s, e, -⟩, -⟩ := (hco.2 k _ (hc k)).2 (c' k)
    exact ⟨s, e⟩
  have hYa : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have hgen := hg p (mem_genFibre z hz)
  have hu : unitAt ξ p (c₀ / ∏ k, y ⟨k, c k⟩ ^ a k) := by
    have := unitAt_of_span hgen.1 (mul_ne_zero hYa hD.1) (hgen.2.symm.trans (hD.2 p trivial c hch))
    rwa [mul_div_mul_right _ _ hD.1] at this
  obtain ⟨U, hU, hmem⟩ := hT.affine c hxc
  have hpU : p.1 ∈ U := (hmem _).2 ⟨hz, hch⟩
  have hgU : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, CoordBase.inChart_gen hT hxc⟩
  obtain ⟨s, hs⟩ := hu.2.1
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p.1, hpU⟩ : U)
  have hloc := hU.isLocalization_stalk ⟨p.1, hpU⟩
  obtain ⟨⟨t, f⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨p.1, hpU⟩).asIdeal.primeCompl s
  have e' : s * X.presheaf.germ U p.1 hpU f.1 = X.presheaf.germ U p.1 hpU t := e
  have hfu : IsUnit (X.presheaf.germ U p.1 hpU f.1) := IsLocalization.map_units (X.presheaf.stalk p.1) f
  have h2 := congrArg (genMap ξ p) e'
  rw [map_mul, hs, CoordBase.genMap_germ_val U hgU p hpU, CoordBase.genMap_germ_val U hgU p hpU] at h2
  have hfu' : unitAt ξ p (CoordBase.val U hgU f.1) := by
    rw [← CoordBase.genMap_germ_val U hgU p hpU]
    obtain ⟨v, hv⟩ := hfu
    rw [← hv]
    exact ⟨(v.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨v⁻¹.val, map_units_inv _ v⟩⟩
  have htu : unitAt ξ p (CoordBase.val U hgU t) := h2 ▸ ZUnit.mul hu hfu'
  have hin : ∀ b : Γ(X, U), CoordBase.val U hgU b ∈ chartRingZ y c := fun b => by
    rw [← CptIn.Intr.segre_chart y c hy]
    exact (CoordBase.mem_adjoin_iff hT hxc hU hmem hgU _).2 ⟨b, rfl⟩
  obtain ⟨δt, Gt, ht1, ht2, ht3⟩ := LiesOver.exists_form_valAt hz hco c hy hc (hin t)
  obtain ⟨δf, Gf, hf1, hf2, hf3⟩ := LiesOver.exists_form_valAt hz hco c hy hc (hin f.1)
  have nt : evC w Gt ≠ 0 := fun h => val_ne_zero htu ht3 (by rw [h, zero_div])
  have nf : evC w Gf ≠ 0 := fun h => val_ne_zero hfu' hf3 (by rw [h, zero_div])
  have hm : ∀ m : K → ℕ, evC w (cMon c m) ≠ 0 := fun m => by
    rw [evC_eq, aeval_cMon]
    exact hW m
  refine ⟨Gt * cMon c δf * cMon c fun k => (a k).toNat, Gf * cMon c δt * cMon c fun k => (-a k).toNat, _, _,
    ⟨homog_mul (homog_mul ht1 (homog_cMon _ _)) (homog_cMon _ _),
      homog_mul (homog_mul hf1 (homog_cMon _ _)) (homog_cMon _ _), fun k => ?_, ?_⟩, ?_, ?_⟩
  · simp only [Pi.add_apply]
    omega
  · have ea : (∏ k, y ⟨k, c k⟩ ^ (a k).toNat) = (∏ k, y ⟨k, c k⟩ ^ a k) * ∏ k, y ⟨k, c k⟩ ^ (-a k).toNat := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k)]
      congr 1
      omega
    simp only [map_mul, aeval_cMon, ht2, hf2]
    rw [ea, ← h2]
    field_simp
  · rw [evC_mul, evC_mul]; exact mul_ne_zero (mul_ne_zero nt (hm _)) (hm _)
  · rw [evC_mul, evC_mul]; exact mul_ne_zero (mul_ne_zero nf (hm _)) (hm _)

end Smooth

open Smooth in
theorem smoothLine : SmoothLine := by
  intro X Ω _ ξ K _ J _ y F' _ _ ψ L a e₀ c₀ cinf n _ hT _ hO _ hvar hD hg hpos hconj
  obtain ⟨A₀, ha, hsm, hcj, hn⟩ := exists_unit_metric y a c₀ fun w hw => by
    by_cases h : w ∈ mcPts (mCoordIdeal y)
    · exact pres_on hT hD hg h
    · exact pres_off hvar.2.1.2.1 a c₀ hw h
  obtain ⟨u, hu, huc⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K J Ω F' y ψ (fun σ => Real.log (cinf σ)) hO
  have huc' := huc fun σ => by simp only [hconj]
  refine ⟨hu.shift A₀, ?_, ?_, fun z => ?_, ?_, fun w hw => ?_⟩
  · show A₀.a + 0 = a
    rw [add_zero, ha]
  · exact ContDiffOn.mul hsm hu.smooth.neg.exp
  · show A₀.h _ * Real.exp (-u _) = A₀.h z * Real.exp (-u z)
    rw [hcj z, huc' z]
  · intro σ z g h dg dh hz h1 h2 h3 h4
    have h3' : ∀ k, (dg k : ℤ) - dh k = a k := fun k => by
      rw [h3 k]
      show (A₀.a + 0) k = a k
      rw [add_zero, ha]
    rw [hn z hz.1 g h dg dh ⟨h1, h2, h3', h4⟩]
    show _ = cinf σ * (A₀.h z * Real.exp (-u z)) * _
    rw [(hu.near σ z hz).self_of_nhds, Real.exp_neg, Real.exp_log (hpos σ)]
    have := (hpos σ).ne'
    field_simp
  · obtain ⟨g, h, dg, dh, hP, -, hh⟩ := pres_on hT hD hg hw
    exact ⟨g, h, dg, dh, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2, hh⟩

end RootFieldNumerics.RF
end
end
