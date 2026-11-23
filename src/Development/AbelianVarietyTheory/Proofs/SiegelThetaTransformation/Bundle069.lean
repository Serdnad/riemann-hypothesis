module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle076
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueWeightTriangularFrame
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CmHostIdempotentTraceEqOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle068
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle059
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle062
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle037
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory

theorem changeRoot_scalar_isMu (t b b' D : ℂ) (A A' m : ℕ) (hb' : b' ≠ 0) (hA : A ≠ 0) (hm : 0 < m)
    (h1 : (b ^ 2 * (A' : ℂ)) ^ m = (b' ^ 2 * (A : ℂ) * D) ^ m) (h2 : IsMu (t ^ 2 * D)) :
    IsMu (t * b * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) / (b' * ((Real.sqrt (A : ℝ) : ℝ) : ℂ))) := by
  obtain ⟨k, hk, h2⟩ := h2
  have e : ∀ B : ℕ, ((Real.sqrt (B : ℝ) : ℝ) : ℂ) ^ 2 = (B : ℂ) := fun B => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg B)]; simp
  have hA' : (A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hA
  refine ⟨2 * m * k, by positivity, ?_⟩
  have e2 : (t * b * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) / (b' * ((Real.sqrt (A : ℝ) : ℝ) : ℂ))) ^ 2 =
      t ^ 2 * (b ^ 2 * (A' : ℂ)) / (b' ^ 2 * (A : ℂ)) := by
    rw [div_pow, mul_pow, mul_pow, mul_pow, e, e, _root_.mul_assoc]
  have hne : (b' ^ 2 * (A : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hb') hA')
  have e3 : (t ^ 2 * (b ^ 2 * (A' : ℂ)) / (b' ^ 2 * (A : ℂ))) ^ m = (t ^ 2 * D) ^ m := by
    rw [div_pow, mul_pow (t ^ 2), h1, mul_pow _ D, div_eq_iff hne, mul_pow (t ^ 2) D]; ring
  rw [pow_mul, pow_mul, e2, e3, ← pow_mul, mul_comm m k, pow_mul, h2, one_pow]

theorem changeRoot_complex (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ]
    [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) (n : ℕ) (hn : Even n)
    (hfib : ∃ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)
      (e : Fin g ≃ Lt1 Dw) (hr : X.p0 + Dw.p = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n)),
      IsSympl X bas ∧ r = Dw.p + Dw.q ∧
      (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) ∧
      (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) ∧
      ∀ y : FrPt Xo c ℂ, ∃ (y₀ : FrPt Xo c ℂ) (t : Ix Dw → ℂˣ) (x : Frame X.Ψ r) (L : Lt E r),
        FrBor t y₀ y ∧ x ∈ X.dom ∧ SelfD X L ∧ Nonempty (AnFib X bas idx e x L y₀))
    (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (b b' : c.F) (hU : Λ.Unimod) (hh : IsUnitaryM h)
    (hT : Λ.TrivAt l.M) (hT' : (actLat h Λ).TrivAt l.M) (hb : IsBeta Dw c Λ b) (hb' : IsBeta Dw c (actLat h Λ) b') :
    ∃ z : ℂ, IsMu z ∧ ∀ (w : (Fin n → LevQ Dw l) → c.F), FixesDatum c h w →
      ∀ N N' : ℕ, Λ.LevOK N l.M → (actLat h Λ).LevOK N' l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ),
      ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)),
      ∀ (y : FrPt Xo c ℂ) (v v' : ℂ), ShortValAt Xo c nab w Λ b N P y v →
        ShortValAt Xo c nab w (actLat h Λ) b' N' (pushLet c h P) y v' → v' = z * v := by
  obtain ⟨r, g, X, bas, idx, e, hr, eL, hS, hr', hL, hrow, hy⟩ := hfib
  by_cases hne : Nonempty (FrPt Xo c ℂ)
  swap
  · exact ⟨1, isMu_one, fun _ _ _ _ _ _ _ _ _ y => (hne ⟨y⟩).elim⟩
  obtain ⟨y1⟩ := hne
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨t, -, ht⟩ := GlobalTheory.Phase.ChangePt.change_at_point hC E H Dw l Xo c r g X bas idx e Dw.p n hr eL hS hr' hn hL hrow nab hnab
    Λ h hU hh hT hT'
  obtain ⟨m, hm, hbeta⟩ := GlobalTheory.BetaChange.beta_sq_compare E H Dw l c n Λ h b b' hU hh hb hb'
  obtain ⟨hP, hΛ⟩ : _ ∧ _ := ⟨fun a => (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1,
    ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU⟩
  set A := ((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) with hAdef
  set A' := ((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q)
    with hA'def
  have hb0 : algebraMap c.F ℂ b ≠ 0 := (map_ne_zero _).2 hb.1
  have hb0' : algebraMap c.F ℂ b' ≠ 0 := (map_ne_zero _).2 hb'.1
  have hA : A ≠ 0 := by
    intro h0
    have h1 := hb.2.2 (algebraMap c.F ℂ)
    rw [← Nat.cast_pow, ← hAdef, h0, Nat.cast_zero, pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h1
    exact hb0 h1
  have hsq : ((Real.sqrt (A : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hA))).ne'
  obtain ⟨y₀, t₀, x, L, -, hx, hSD, ⟨F⟩⟩ := hy y1
  have hmu := (ht x L y₀ F hx hSD).1
  have hbeta' := congrArg (algebraMap c.F ℂ) hbeta
  simp only [map_pow, map_mul, map_natCast, map_prod] at hbeta'
  refine ⟨_, changeRoot_scalar_isMu t _ _ _ A A' m hb0' hA hm hbeta' hmu, ?_⟩
  intro w hw N N' hN hN' a P hPa y v v' hv hv'
  obtain ⟨y₀, t₀, x, L, hB, hx, hSD, ⟨F⟩⟩ := hy y
  have ex1 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hPa w b).1 ℂ
  have ex2 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) N' hΛ hT' hN' a _ (hP a P hPa) w b').1 ℂ
  obtain ⟨u, hu, -⟩ := ex1 y₀
  obtain ⟨u', hu', -⟩ := ex2 y₀
  have k1 := (ex1 y).unique hv
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a P).2 hPa w Λ b N u hu)
  have k2 := (ex2 y).unique hv'
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a _).2 (hP a P hPa) w _ b' N' u' hu')
  have k3 := (ht x L y₀ F hx hSD).2 w hw N N' hN hN' a P hPa b b' u u' hb.1 hb'.1 hu hu'
  have k4 : u' = t * algebraMap c.F ℂ b * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) /
      (algebraMap c.F ℂ b' * ((Real.sqrt (A : ℝ) : ℝ) : ℂ)) * u := by
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hb0' hsq), ← _root_.mul_assoc]
    exact k3
  rw [k1, k2, k4]; ring

theorem changeRoot_of_chartIndep : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ), ChangeRoot Xo c nab n := by
  intro hC E _ _ _ H Dw l Xo c _ nab n hs bad hbad Λ h b b' hU hh hT hT' hb hb'
  obtain ⟨-, hodd, hn, hnab⟩ := hs
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  have triv : ∀ Λ : GenLat E n, Λ.TrivAt bad → Λ.TrivAt l.M := fun Λ ⟨k, hk, h1⟩ =>
    ⟨k, hk.coprime_dvd_right hbad.2.2.1, h1⟩
  have hT := triv _ hT
  have hT' := triv _ hT'
  obtain ⟨s, hfib⟩ := GlobalTheory.Dict.exists_anFib_all_points E H Dw l Xo c hodd.pos n hn
  obtain ⟨z, hz, hid⟩ := @changeRoot_complex hC E _ _ _ H Dw l Xo c s.toAlgebra _ nab hnab n hn hfib
    Λ h b b' hU hh hT hT' hb hb'
  have hP := fun a => (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1
  have hΛ := ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU
  let J : Type := {p : ((Fin n → LevQ Dw l) → c.F) × ℕ × ℕ × ((E →+* ℂ) × ℕ → ℕ) × MvPolynomial (LtN Dw n) c.F //
    FixesDatum c h p.1 ∧ Λ.LevOK p.2.1 l.M ∧ (actLat h Λ).LevOK p.2.2.1 l.M ∧
      p.2.2.2.2 ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => p.2.2.2.1 (τ, i))}
  have ex1 := fun j : J => GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ j.1.2.1 hU hT j.2.2.1 j.1.2.2.2.1
    j.1.2.2.2.2 j.2.2.2.2 j.1.1 b
  have ex2 := fun j : J => GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) j.1.2.2.1 hΛ hT' j.2.2.2.1
    j.1.2.2.2.1 _ (hP _ _ j.2.2.2.2) j.1.1 b'
  choose u hu using fun (j : J) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => ((ex1 j).1 S y).exists
  choose u' hu' using fun (j : J) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => ((ex2 j).1 S y).exists
  obtain ⟨z₀, hz₀, hfin⟩ := GlobalTheory.ConstRatio.exists_ratio E H Dw l Xo c s J u u'
    (fun j S T _ _ _ _ φ y y' hy => (ex1 j).2 S T φ y y' hy _ _ (hu j S y) (hu j T y'))
    (fun j S T _ _ _ _ φ y y' hy => (ex2 j).2 S T φ y y' hy _ _ (hu' j S y) (hu' j T y')) z hz
    (fun j y => hid j.1.1 j.2.1 _ _ j.2.2.1 j.2.2.2.1 _ _ j.2.2.2.2 y _ _
      (@hu j ℂ _ s.toAlgebra y) (@hu' j ℂ _ s.toAlgebra y))
  refine ⟨z₀, hz₀, ?_⟩
  intro w hw N N' hN hN' a P hPa S _ _ y v v' hv hv'
  let j : J := ⟨(w, N, N', a, P), hw, hN, hN', hPa.1⟩
  rw [((ex1 j).1 S y).unique hv (hu j S y), ((ex2 j).1 S y).unique hv' (hu' j S y)]
  exact hfin j S y

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory

theorem mem_span_of_map_mem_span_image {K : Type*} [Field K] {σ : K →+* ℂ} {C : Type*} [AddCommGroup C]
    [Module K C] {W : Type*} [AddCommGroup W] [Module ℂ W] (j : C →ₛₗ[σ] W) (V : Submodule K C)
    (hj : ∀ (m : ℕ) (b : Fin m → C), (∀ i, b i ∈ V) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => j (b i)))
    (S : Set C) (hS : S ⊆ V) {f : C} (hf : f ∈ V) (hjf : j f ∈ Submodule.span ℂ (j '' S)) :
    f ∈ Submodule.span K S := by
  let V' : Submodule K C := V ⊓ (Submodule.span ℂ (j '' S)).comap j
  have hSV : S ⊆ V' := fun s hs => ⟨hS hs, Submodule.subset_span ⟨s, hs, rfl⟩⟩
  have hind : ReciprocityTheory.ChartRestriction.G.PullbackSections.IndepToC (j.domRestrict V') := by
    intro m b hb
    exact hj m (fun i => (b i : C)) (fun i => (b i).2.1) (hb.map' V'.subtype (Submodule.ker_subtype V'))
  have himg : (j.domRestrict V') '' (V'.subtype ⁻¹' S) = j '' S := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hSV hx⟩, hx, rfl⟩
  have htop := ReciprocityTheory.ChartRestriction.G.PullbackSections.span_eq_top_of_indepToC (j.domRestrict V') hind (V'.subtype ⁻¹' S)
    (fun g => by rw [himg]; exact g.2.2)
  have h1 : (⟨f, hf, hjf⟩ : V') ∈ Submodule.span K (V'.subtype ⁻¹' S) := by
    rw [htop]; exact Submodule.mem_top
  have h2 := Submodule.mem_map_of_mem (f := V'.subtype) h1
  rw [Submodule.map_span] at h2
  exact Submodule.span_mono (Set.image_preimage_subset _ _) h2

theorem cusp_le_span_shortGen : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ) → 1 ≤ r → l.A = 1 → (∀ k k', ((U σ).X k).Gm = ((U σ).X k').Gm ∧ ((U σ).X k).ξ0 = ((U σ).X k').ξ0) → (∀ k, HasPrinc ((U σ).X k) l.M) → (∀ a n, Dom a n → ∀ k, ChiOne ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k)) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (dδ : ∀ n, DeltaDat Xo c n), 0 < bad → (∀ n, (dδ n).IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab (dδ n).Xo₂ (dδ n).c₂ (dδ n).nab₂) ∧ UnitC (dδ n) ∧ ¬ 3 ∣ (dδ n).pd ∧ (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, (dδ n).PhiPin ph ψ x₀) ∧ ∀ a, Dom a n → ShortValTot Xo c nab bad nV a n (dδ n)) → SpanningAtDominantWeight Xo c nab bad nV (Formalism.L2.PjFree.cusp Xo c U) dδ := by
  intro hC E _ _ _ H Dw l Xo c r U σ hσ hU hr hA hG hP hχ nab bad nV dδ hbad hd a n hDom _ hn f hf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd n
  have hrk : 4 * (Module.finrank ℚ E * r) + 4 ≤ n := by
    have he : Module.finrank ℚ E = 2 * NumberField.InfinitePlace.nrComplexPlaces E :=
      NumberField.IsTotallyComplex.finrank E
    have hr' : r = Dw.p + Dw.q := hU.1
    rw [he, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), ← hr'] at hn
    rw [he]
    calc 4 * (2 * NumberField.InfinitePlace.nrComplexPlaces E * r) + 4
        = 8 * NumberField.InfinitePlace.nrComplexPlaces E * r + 4 := by ring
      _ ≤ n := hn
  have hsp := GlobalTheory.Dict.holSub0_le_span_shortGen hC E H Dw l Xo c n (dδ n) σ r (U σ) hσ hU hr hA hG hP h1 h2 h3 h4 h5 nab bad nV a
    hbad hDom hrk (hχ a n hDom) (h6 a hDom)
  have hf' := (Formalism.L2.PjFree.mem_cusp Xo c U a n f).1 hf
  have hind := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c σ r
    (U σ) hU a n).1
  refine mem_span_of_map_mem_span_image (Formalism.L2.PjFree.rdU (U σ)) (sec Xo c a n) hind (shortGen Xo c nab bad nV a n (dδ n)) (fun g hg => hg.1) hf'.1 (hsp ?_)
  refine ⟨hf'.2 σ hσ, fun k x hx => ?_⟩
  exact dif_neg hx

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.cuspForms_vanishing_off_frames_le_span_shortTheta : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → (∀ k, HasPrinc (U.X k) l.M) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ¬ 3 ∣ d.pd → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, ChiOne (U.X k) (Formalism.L2.PjFree.laU U a n k)) → ShortValTot Xo c nab bad nV a n d → GlobalTheory.Dict.holSub0 U.X (Formalism.L2.PjFree.laU U a n) ≤ Submodule.span ℂ (Formalism.L2.PjFree.rdU U '' shortGen Xo c nab bad nV a n d) := by
  first | exact @GlobalTheory.Dict.holSub0_le_span_shortGen | exact GlobalTheory.Dict.holSub0_le_span_shortGen | (intros; apply GlobalTheory.Dict.holSub0_le_span_shortGen <;> assumption)
end
