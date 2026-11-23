module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.WeightZeroSectionValueConjPoint
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpaces
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle094
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Mathlib.Algebra.MvPolynomial.Cardinal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle101
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace ComplexTransfer

theorem epi_spMap_field {k Ω : Type} [Field k] [Field Ω] (σ : k →+* Ω) : Epi (spMap σ) := by
  letI := σ.toAlgebra
  haveI : Flat (spMap σ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem countable_of_finiteType (K A : Type) [CommRing K] [Countable K] [CommRing A] [Algebra K A]
    [h : Algebra.FiniteType K A] : Countable A := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  haveI : Countable (MvPolynomial (Fin n) K) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (MvPolynomial.cardinalMk_le_max).trans ?_
    simp
  exact hf.countable

theorem exists_common_field {K : Type} [Field K] [Countable K] (σ : K →+* ℂ) {A B k : Type} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] [Countable A] [Countable B] [Field k] [Algebra K k]
    (φ : A →ₐ[K] k) (ψ : B →ₐ[K] k) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (ι : L →ₐ[K] k) (j : L →ₐ[K] CAt σ) (φL : A →ₐ[K] L)
      (ψL : B →ₐ[K] L), ι.comp φL = φ ∧ ι.comp ψL = ψ ∧ Function.Injective j := by
  let s : Set k := Set.range φ ∪ Set.range ψ
  have hs : s.Countable := (Set.countable_range _).union (Set.countable_range _)
  let L := IntermediateField.adjoin K s
  have hL : Countable L := by
    have := hs.to_subtype
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (IntermediateField.cardinalMk_adjoin_le K s).trans ?_
    simp
  letI : Algebra K ℂ := σ.toAlgebra
  obtain ⟨j⟩ := GlobalTheory.nonempty_algHom_complex_of_countable K L
  refine ⟨L, inferInstance, inferInstance, L.val, j,
    φ.codRestrict L.toSubalgebra fun a => IntermediateField.subset_adjoin K s (Or.inl ⟨a, rfl⟩),
    ψ.codRestrict L.toSubalgebra fun a => IntermediateField.subset_adjoin K s (Or.inr ⟨a, rfl⟩), ?_, ?_, ?_⟩
  · ext a; rfl
  · ext a; rfl
  · exact j.toRingHom.injective

theorem evalAt_of_mapR {K : Type} [Field K]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (hW : EvalWD pts mapR) (f : Rules pts) (hf : IsNatural pts mapR f)
    {S : Type} [CommRing S] [Algebra K S] (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R) (z : pts S)
    (hz : mapR φ y z) : evalAt pts mapR f z = φ (f p y) := by
  have hT : FromTest pts mapR z := ⟨p, φ, y, hz⟩
  unfold evalAt
  rw [dite_eq_left hT]
  exact (hW f hf S p _ φ _ y _ z hz hT.choose_spec.choose_spec.choose_spec).symm

end ComplexTransfer

theorem exists_complex_framed_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (k : Type) [Field k] [Algebra c.F k] (y y' : FrPt Xo c k), ∃ z z' : FrPt Xo c (CAt c.F.val.toRingHom), (∀ ρ : Xo.X ⟶ Xo.X, y'.x = y.x ≫ ρ → z'.x = z.x ≫ ρ) ∧ (∀ f ∈ sec Xo c 0 0, evR Xo c f y = 0 → evR Xo c f z = 0) ∧ ∀ f ∈ sec Xo c 0 0, ∀ a : c.F, evR Xo c f z' = algebraMap c.F (CAt c.F.val.toRingHom) a * evR Xo c f z → evR Xo c f y' = algebraMap c.F k a * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c k _ _ y y'
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  obtain ⟨p, φ, y₀, hy⟩ := hA k y
  obtain ⟨q, ψ, y₁, hy'⟩ := hA k y'
  haveI := c.fin
  haveI : Countable c.F := ComplexTransfer.countable_of_finiteType ℚ c.F
  haveI : Countable p.R := ComplexTransfer.countable_of_finiteType c.F p.R
  haveI : Countable q.R := ComplexTransfer.countable_of_finiteType c.F q.R
  obtain ⟨L, _, _, ι, j, φL, ψL, hφ, hψ, hj⟩ :=
    ComplexTransfer.exists_common_field c.F.val.toRingHom φ ψ
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ (j.comp φL) y₀
  obtain ⟨z', hz'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ (j.comp ψL) y₁
  have hι : Function.Injective ι := ι.toRingHom.injective
  have ev : ∀ f ∈ sec Xo c 0 0, evR Xo c f y = ι (φL (f p y₀)) ∧ evR Xo c f y' = ι (ψL (f q y₁)) ∧
      evR Xo c f z = j (φL (f p y₀)) ∧ evR Xo c f z' = j (ψL (f q y₁)) := by
    intro f hf
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← AlgHom.comp_apply, hφ]
      exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 p φ y₀ y hy
    · rw [← AlgHom.comp_apply, hψ]
      exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 q ψ y₁ y' hy'
    · exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 p _ y₀ z hz
    · exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 q _ y₁ z' hz'
  refine ⟨z, z', ?_, ?_, ?_⟩
  · intro ρ h
    have e1 : y.x = spMap ι.toRingHom ≫ spMap φL.toRingHom ≫ y₀.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hy.1, ← hφ]; rfl
    have e2 : y'.x = spMap ι.toRingHom ≫ spMap ψL.toRingHom ≫ y₁.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hy'.1, ← hψ]; rfl
    have e3 : z.x = spMap j.toRingHom ≫ spMap φL.toRingHom ≫ y₀.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hz.1]; rfl
    have e4 : z'.x = spMap j.toRingHom ≫ spMap ψL.toRingHom ≫ y₁.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hz'.1]; rfl
    haveI := ComplexTransfer.epi_spMap_field ι.toRingHom
    rw [e1, e2, Category.assoc, cancel_epi] at h
    rw [e3, e4, h]
    simp only [Category.assoc]
  · intro f hf h
    obtain ⟨h1, -, h3, -⟩ := ev f hf
    rw [h1, map_eq_zero_iff ι hι] at h
    rw [h3, h, map_zero]
  · intro f hf a h
    obtain ⟨h1, h2, h3, h4⟩ := ev f hf
    rw [h3, h4, ← j.commutes, ← map_mul] at h
    rw [h1, h2, hj h, map_mul, ι.commutes]

end GlobalTheory.Frames
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.weightZeroSection_value_conj_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (τ : ℂ ≃+* ℂ), ∀ f ∈ sec Xo c 0 0, ∀ (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((τ : ℂ →+* ℂ).comp σ))), y'.x = spMap (τ : ℂ →+* ℂ) ≫ y.x → Formalism.L2.PjFree.toC (evR Xo c f y') = τ (Formalism.L2.PjFree.toC (evR Xo c f y)) := by
  first | exact @GlobalTheory.WeightZeroValue.evR_conj | exact GlobalTheory.WeightZeroValue.evR_conj | (intros; apply GlobalTheory.WeightZeroValue.evR_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem SupNormCusp.eq_zero_of_pnorm_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (hx : x ∈ X.dom) (h : X.pnorm la P x = 0) : P x = 0 := by
  have hx' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := by
    intro τ i h0
    have := (hx' τ).2 i
    rw [h0] at this
    simp at this
  unfold Data.pnorm at h
  rcases mul_eq_zero.1 h with h1 | h1
  · exact norm_eq_zero.1 h1
  · exfalso
    refine (ne_of_gt ?_) h1
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
    exact norm_pos_iff.2 (div_ne_zero (hd τ _) (hd τ _))

theorem supNorm_definite_on_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → Formalism.L2.PjFree.SupDef Xo c U := by
  intro E _ _ _ H Dw l Xo c r U hU a n hd σ hσ f hf h0
  refine (GlobalTheory.T.rdU_linearIndependent_and_injective GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c σ r (U σ) (hU σ hσ) a n).2 f
    (Formalism.L2.PjFree.cusp_le_sec Xo c U a n hf) fun k x hx => ?_
  have hfin := Formalism.L2.PjFree.supE_cusp_ne_top hσ hf
  have hE : Formalism.L2.PjFree.supE (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) (Formalism.L2.PjFree.rdU (U σ) f) = 0 := by
    unfold Formalism.L2.PjFree.supN at h0
    rcases ENNReal.toReal_eq_zero_iff _ |>.1 h0 with h1 | h1
    · exact h1
    · exact absurd h1 hfin
  have hle : ENNReal.ofReal (((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k)
      (Formalism.L2.PjFree.rdU (U σ) f k) x) ≤ 0 := by
    rw [← hE]
    exact le_iSup (fun p : Formalism.L2.PjFree.FPt (U σ).X => ENNReal.ofReal (((U σ).X p.1).pnorm
      (Formalism.L2.PjFree.laU (U σ) a n p.1) (Formalism.L2.PjFree.rdU (U σ) f p.1) p.2)) ⟨k, ⟨x, hx⟩⟩
  have hp : ((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k) (Formalism.L2.PjFree.rdU (U σ) f k) x = 0 := by
    refine le_antisymm (ENNReal.ofReal_eq_zero.1 (le_antisymm hle zero_le)) ?_
    unfold Data.pnorm
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _)
  exact SupNormCusp.eq_zero_of_pnorm_eq_zero _ _ _ x hx hp

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompBij

open GlobalTheory.CompInj




theorem ik_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), 1 ≤ r → GoodEmb c σ → IsUnf U → ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), (∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) → (∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ), (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧ IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧ ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) ((U.un k x).u τ i)) → Function.Bijective ik := by
  intro E _ _ _ H D l Xo c σ r U h1 hσ hU g e F ik φ hEF hP
  obtain ⟨hr, hX, hcov, hfib, -⟩ := hU
  refine ⟨fun k k' hk => ?_, fun i => ?_⟩
  · obtain ⟨x, hx⟩ := dom_nonempty (U.X k)
    obtain ⟨x₀, hx₀⟩ := dom_nonempty (U.X k')
    obtain ⟨P, -, hper, hpt, hder⟩ := hP k ⟨x, hx⟩
    obtain ⟨P₀, hP₀, hper₀, -⟩ := hP k' ⟨x₀, hx₀⟩
    have hP' := fun y => (hP k' y).imp fun _ h => (⟨h.1, h.2.2.1, h.2.2.2⟩ : _ ∧ _ ∧ _)
    have hEF' := hEF k'
    generalize φ k' = ψ at hP₀ hP' hEF'
    clear hP hEF φ
    generalize ik k' = n at *
    subst hk
    obtain ⟨x', hx', hPx⟩ := exists_frame (c := c) (σ := σ) hσ h1 hr e (U.X k') (hX k').1 (hX k').2 _ (F.sig _).1
      (F.sig _).2 ψ hEF' x₀ hx₀ P₀ hP₀ hper₀ P hper
    obtain ⟨P', hP', hpt', hder'⟩ := hP' ⟨x', hx'⟩
    obtain rfl : P = P' := by
      ext a j
      exact (hPx a j).trans (hP' a j).symm
    have hbor := frBor_of_eq (U.un k ⟨x, hx⟩) (U.un k' ⟨x', hx'⟩) (hpt'.trans hpt.symm) fun τ i =>
      ((GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo _ g _ F _ P hper).2.1 _).unique (hder' τ i) (hder τ i)
    obtain ⟨γ, -, b, -, h⟩ := (hfib k k' _ _).1 hbor
    exact (congrArg Sigma.fst h).symm
  · have hty : IsTypeFn H (F.Di i).p (F.Di i).q (fun j => relab c σ (e j).1) := by
      rw [(F.sig i).1, (F.sig i).2]
      exact (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 D g e
    obtain ⟨-, P, hPi⟩ := GlobalTheory.PeriodExists.period_of_isTypeFn H (F.Di i) g _ hty
    let _ : Algebra c.F ℂ := σ.toAlgebra
    obtain ⟨y, hy⟩ := Formalism.L2.Pj.exists_frPt_local (Xo := Xo) (c := c) (L := ℂ)
      GlobalTheory.firstFiveLaws.2.1.secTwist (F.u i P) ((F.over_σ i P hPi).trans rfl)
    obtain ⟨k, x, t, hb⟩ := hcov y
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k x
    exact ⟨k, F.disj _ _ Pm P hPm hPi (hx.symm.trans (hb.1.symm.trans hy))⟩

end GlobalTheory.CompBij
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.RootOfUnityFn

theorem evR_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (f : Rul Xo c) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S)
    (h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) (m : ℕ) :
    evR Xo c (f ^ m) y = evR Xo c f y ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; exact evalAt_one _ _ y h
  | succ k ih =>
    rw [pow_succ, pow_succ, ← ih]
    exact evalAt_mul _ _ _ _ y

theorem exists_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (n : ℕ) (d : DeltaDat Xo c n) (m : ℕ), 0 < m → d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → d.cδ ^ m = 1 → (∀ y : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom), ∃ a : d.c₂.F, evR d.Xo₂ d.c₂ d.cδ y = algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom) a) → ∃ (Cls : Type) (_ : CommGroup Cls) (_ : Finite Cls) (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), CMP Xo c d _ Cls δ gdet false := by
  intro E _ _ _ H Dw l Xo c n d m hm hsec hpow hval
  choose a ha using hval
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : IsReduced (CAt d.c₂.F.val.toRingHom) := (inferInstance : IsReduced ℂ)
  have hinj : Function.Injective (algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom)) :=
    (d.c₂.F.val.toRingHom).injective
  have hroot : ∀ y, a y ^ m = 1 := by
    intro y
    have hT := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂ _ y
    have h1 := evR_pow d.Xo₂ d.c₂ d.cδ y hT m
    have h0 := evR_pow d.Xo₂ d.c₂ d.cδ y hT 0
    rw [pow_zero, pow_zero] at h0
    rw [hpow, h0, ha, ← map_pow] at h1
    exact hinj (by rw [map_one]; exact h1.symm)
  refine ⟨rootsOfUnity m d.c₂.F, inferInstance, inferInstance, (rootsOfUnity m d.c₂.F).subtype,
    fun y => rootsOfUnity.mkOfPowEq (a y) (hroot y), hsec, fun y => ?_⟩
  rw [ha]
  rfl

end GlobalTheory.RootOfUnityFn
end
end
