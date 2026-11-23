module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle036
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}


theorem evR_of_frMap (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    {f : Rul Xo c} (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra c.F S] {p : TRing c.F} {φ : p.R →ₐ[c.F] S} {y : FrPt Xo c p.R}
    {w : FrPt Xo c S} (hy : FrMap φ y w) : evR Xo c f w = φ (f p y) := by
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, y, hy⟩
  unfold evR evalAt
  rw [dite_eq_left hT]
  exact hW f hf S _ _ _ _ _ _ w hT.choose_spec.choose_spec.choose_spec hy

end Gen

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D}

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem ratio_single {Z : Comp Xo c} (G : WTZ E) (r s : Om Z) (hs : s ≠ 0) :
    ratio (Ω := Om Z) (AddMonoidAlgebra.single G r : AC Z) (AddMonoidAlgebra.single G s) = r / s := by
  have hex : ∃ a : Om Z, (AddMonoidAlgebra.single G r : AC Z) = a • AddMonoidAlgebra.single G s :=
    ⟨r / s, by rw [AddMonoidAlgebra.smul_single', div_mul_cancel₀ r hs]⟩
  unfold ratio
  rw [dite_eq_left hex]
  have e := hex.choose_spec
  rw [AddMonoidAlgebra.smul_single'] at e
  have e2 : r = hex.choose * s := by
    simpa [AddMonoidAlgebra.coeff_single] using congrArg (fun q : AC Z => q.coeff G) e
  rw [eq_div_iff hs]
  exact e2.symm

variable {D : D7} {T : Top D} {j : ℕ}
  {d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)}
  {Z : Comp (T.Q.Xo j) T.Q.c} {X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r}


end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

theorem holSub_comp_SS {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) (hP : P ∈ holSub X la) (k : Comp) :
    P k ∈ (X k).SS (la k) := by
  have hM := siegelSpaceAlgebra_holds (E := E)
  induction hP using Submodule.span_induction with
  | mem x hx => exact hx k
  | zero => exact (hM r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact (hM r (X k) (la k) (la k) 0).1.2.1 _ hx _ hy
  | smul a x _ hx => exact (hM r (X k) (la k) (la k) 0).1.2.2 a _ hx

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem volPair_of_tie (hT : VolTieG D) (V : HSp D) (hs : V.SigOK) : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2 := by
  have h := hT V hs
  clear hT
  obtain ⟨⟨μ, hμ⟩, hb⟩ := h
  obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := hb μ hμ
  refine ⟨(μ, 𝓕), ?_⟩
  exact ⟨hμ, h𝓕⟩

theorem quotSupp_of (V : HSp D) (hV : FinVol V) (hP : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2) :
    QuotSupp V := by
  intro φ hφc hφinv hae g0
  by_contra hg0
  haveI : Countable (GQ V) := by
    unfold GQ
    exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  have hvp : IsVolPair D V (volPair V).1 (volPair V).2 := by
    have e : volPair V = hP.choose := by
      unfold volPair
      rw [dite_eq_left hP]
    rw [e]
    exact hP.choose_spec
  haveI : (volPair V).1.IsHaarMeasure := hvp.1.1
  haveI : BorelSpace (GA D V) := by
    first
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA _ _
  haveI : MeasurableMul (GA D V) := by
    first
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA _ _
  haveI : MeasurableConstSMul (GQ V) (GA D V) := ⟨fun c => measurable_const_mul (c : GA D V)⟩
  haveI : SMulInvariantMeasure (GQ V) (GA D V) (volPair V).1 :=
    ⟨fun c s _ => measure_preimage_mul (volPair V).1 (c : GA D V) s⟩
  let O : Set (GA D V) := {g | φ g ≠ 0}
  have hO : IsOpen O := isOpen_ne_fun hφc continuous_const
  have hOinv : ∀ γ : GQ V, γ • O = O := by
    intro γ
    ext g
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      show φ ((γ : GA D V) * x) ≠ 0
      rw [hφinv _ γ.2]
      exact hx
    · intro hg
      refine ⟨((γ⁻¹ : GQ V) : GA D V) * g, ?_, ?_⟩
      · show φ (((γ⁻¹ : GQ V) : GA D V) * g) ≠ 0
        rw [hφinv _ (γ⁻¹).2]
        exact hg
      · show (γ : GA D V) * (((γ⁻¹ : GQ V) : GA D V) * g) = g
        rw [← mul_assoc, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, one_mul]
  have hpos : 0 < (volPair V).1 O := hO.measure_pos _ ⟨g0, hg0⟩
  have hOF : (volPair V).1 (O ∩ (volPair V).2) ≠ 0 := fun h =>
    hpos.ne' (hvp.2.measure_zero_of_invariant O hOinv h)
  let S : Set (AutQ V) := {q | ¬ onQ V φ q = (0 : AutQ V → ℂ) q}
  have h0 : muQ1 V S = 0 := ae_iff.mp hae
  have hS : muQ V S = 0 := by
    unfold muQ1 at h0
    rw [if_pos (show muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤ from hV), Measure.smul_apply,
      smul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (ENNReal.inv_eq_zero.mp h) hV.2
    · exact h
  have hmeas : AEMeasurable (autMk V) ((volPair V).1.restrict (volPair V).2) := by
    have hm : Measurable (autMk V) := by
      first
      | exact measurable_quotient_mk'
      | exact fun _ hs => hs
    exact hm.aemeasurable
  have hpre : autMk V ⁻¹' S = O := by
    ext g
    have hrel := Quotient.mk_out (s := QuotientGroup.rightRel (GQ V)) g
    rw [QuotientGroup.rightRel_apply] at hrel
    have hv : φ (autMk V g).out = φ g := by
      have e : g = (g * (autMk V g).out⁻¹) * (autMk V g).out := by group
      conv_rhs => rw [e]
      rw [hφinv _ hrel]
    show ¬ φ (autMk V g).out = 0 ↔ φ g ≠ 0
    rw [hv]
  have hle := Measure.le_map_apply hmeas S
  rw [hpre, Measure.restrict_apply hO.measurableSet] at hle
  have e2 : muQ V S = Measure.map (autMk V) ((volPair V).1.restrict (volPair V).2) S := rfl
  rw [← e2, hS] at hle
  exact hOF (le_antisymm hle (zero_le))

section Dom

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem aeDom_of {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, ((U σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hA : AdelAut V dict mu) (hV : FinVol V) (hP : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2)
    (hmu : MuUnit V dict mu) (hd : DictIsUnif V dict Kf th hr) : AeDom U σ V dict mu := by
  intro la P hPm hae k x hx
  have key : ∀ Q ∈ holSub (U σ).X la,
      ((∀ γ ∈ GQ V, ∀ g, adel V dict mu Q (γ * g) = adel V dict mu Q g) ∧
        Continuous (adel V dict mu Q)) ∧
      ∀ k, (∀ x ∈ ((U σ).X k).dom, ∀ b ∈ Bor ((U σ).X k).Ψ r, Q k (rmul x b) = bchar (la k) b * Q k x) ∧
        ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Q k (lact γ x) = ((U σ).X k).χ (la k) γ * Q k x := by
    intro Q hQ
    unfold holSub at hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      refine ⟨hA la Q hQ, fun k => ?_⟩
      have hs := (hQ k).1.1
      exact ⟨hs.2.1, hs.2.2⟩
    | zero =>
      refine ⟨⟨fun γ _ g => by simp, by rw [map_zero]; exact continuous_zero⟩,
        fun k => ⟨fun x _ b _ => by simp, fun γ _ x _ => by simp⟩⟩
    | add Q₁ Q₂ _ _ h1 h2 =>
      refine ⟨⟨fun γ hγ g => ?_, ?_⟩, fun k => ⟨fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩⟩
      · rw [map_add (f := _), Pi.add_apply, Pi.add_apply, h1.1.1 γ hγ g, h2.1.1 γ hγ g]
      · rw [map_add (f := _)]
        exact h1.1.2.add h2.1.2
      · simp only [Pi.add_apply]
        rw [(h1.2 k).1 x hx b hb, (h2.2 k).1 x hx b hb, mul_add]
      · simp only [Pi.add_apply]
        rw [(h1.2 k).2 γ hγ x hx, (h2.2 k).2 γ hγ x hx, mul_add]
    | smul a Q _ h =>
      refine ⟨⟨fun γ hγ g => ?_, ?_⟩, fun k => ⟨fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩⟩
      · rw [map_smul, Pi.smul_apply, Pi.smul_apply, h.1.1 γ hγ g]
      · rw [map_smul]
        exact h.1.2.const_smul a
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [(h.2 k).1 x hx b hb]
        ring
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [(h.2 k).2 γ hγ x hx]
        ring
  obtain ⟨⟨hinv, hcont⟩, hlaw⟩ := key P hPm
  have hz := quotSupp_of V hV hP (adel V dict mu P) hcont hinv hae
  obtain ⟨-, -, -, hd4, hd5, -⟩ := hd
  obtain ⟨g, γ, hγ, b, hb, hg⟩ := hd5 k x hx
  have h0 : P (dict g).1 (dict g).2 = 0 := by
    have e : mu g * P (dict g).1 (dict g).2 = 0 := hz g
    have hmu0 : mu g ≠ 0 := by
      intro h
      have h1 := hmu.2.1 g
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    exact (mul_eq_zero.mp e).resolve_left hmu0
  have hdom := hd4 g
  rw [hg] at h0 hdom
  exact eq_zero_of_orbit _ (la k) (P k) (hlaw k).1 (hlaw k).2 hx hγ hb hdom h0

end Dom

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions MeasureTheory
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Par.Canon (Q : Par D) : Prop :=
  Q.H = hostOfRecord D ∧ ∀ j (hj : InR D j), ∃ hP hd, HEq (Q.Dw j) (datumOfRecord D j hj hP hd)

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.BasicNotions Formalism.MainNotions

section Mean

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

theorem htI2et_of_pt (d : Data K ι Ω WT A)
    (hpt : ∀ sg, Real.log (d.supN sg (d.n1 • d.wde) d.et) / d.i ≤ d.Pet) : d.HeightIntegralEstimateTrivialPlace := by
  unfold Data.HeightIntegralEstimateTrivialPlace meanK
  have hN : (0 : ℝ) < (Fintype.card (K →+* ℂ) : ℝ) := by
    first
    | exact_mod_cast Fintype.card_pos
    | (haveI : Nonempty (K →+* ℂ) := ⟨(IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom⟩
       exact_mod_cast Fintype.card_pos)
  rw [div_right_comm, Finset.sum_div, div_le_iff₀ hN]
  calc ∑ sg, (fun sg => Real.log (d.supN sg (d.n1 • d.wde) d.et)) sg / (d.i : ℝ)
      ≤ ∑ _sg : K →+* ℂ, d.Pet := Finset.sum_le_sum (fun sg _ => hpt sg)
    _ = d.Pet * (Fintype.card (K →+* ℂ) : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

end Mean

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def recNrm {σ : c.F →+* ℂ} {rU : ℕ} (U : Unf Xo c σ rU) (xR : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c)
    (k : U.Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ rU) : ℝ :=
  lieFac Dw xR a * (U.X k).pnorm (laU U a n k) (rdU U f k) x

def I2AtFramePoints {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul Xo c)
    (uL : WtR E) (th tableLineDegreeFive DF cc : ℝ) : Prop :=
  ∀ σ, GoodEmb c σ → ∀ (k : (U σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ rU), x ∈ ((U σ).X k).dom →
    -Real.log (Real.sqrt (∑ j, recNrm (U σ) xR uL.1 uL.2 (wR j) k x ^ 2)) ≤
      tableLineDegreeFive * DF + cc * ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th x

def NrmTieU (h : GenFrEx Xo c) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul Xo c) (uL : WtR E)
    (etR : Rul Xo c) (uet : WtR E) : Prop :=
  ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ), ∃ σ, GoodEmb c σ ∧ ∃ (k : (U σ).Comp)
    (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ rU), x ∈ ((U σ).X k).dom ∧
    (∀ j, nrmC fn (yP Z) (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) P = recNrm (U σ) xR uL.1 uL.2 (wR j) k x) ∧
    nrmC fn (yP Z) (wtZ uet.1 uet.2) (valC h uet.1 uet.2 etR Z) P ≤ recNrm (U σ) xR uet.1 uet.2 etR k x

variable [Fintype (Comp Xo c)]

theorem supN_dataOf_nonneg (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ) (sg : c.F →+* ℂ) (G : WTZ E) (x : ∀ Z : Comp Xo c, AC Z) :
    0 ≤ (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).supN sg G x := by
  unfold Data.supN
  apply Real.iSup_nonneg
  intro p
  unfold dataOf nrmC
  dsimp only
  first
  | positivity
  | exact (rfl : (0 : ℕ) = 0)

theorem htI2be_of (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (xR th : ℝ)
    (hi : 0 < i) (hcc : 0 ≤ cc) (hfn : FnNe Xo c fn) (het : NZAt h etR)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2)
    (htie : NrmTieU h fn yP U xR wR uL etR uet) (hI2 : I2AtFramePoints U xR wR uL th tableLineDegreeFive DF cc)
    (harch : ∀ σ, GoodEmb c σ → ∀ (k : (U σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ rU),
      x ∈ ((U σ).X k).dom → recNrm (U σ) xR uet.1 uet.2 etR k x ≤
        Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th x - tableLineDegreeTwo))) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HeightIntegralBoundEstimate := by
  intro Z P
  obtain ⟨σ, hσ, k, x, hx, hw, he⟩ := htie Z P
  have h1 := hI2 σ hσ k x hx
  have h2 := harch σ hσ k x hx
  show -Real.log (Real.sqrt (∑ j, nrmC fn (yP Z) (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) P ^ 2)) ≤
    tableLineDegreeFive * DF + cc / (i : ℝ) * (-Real.log (nrmC fn (yP Z) ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) P)) +
      cc * tableLineDegreeTwo
  have hbe : (∑ j, nrmC fn (yP Z) (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) P ^ 2) =
      ∑ j, recNrm (U σ) xR uL.1 uL.2 (wR j) k x ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [hw j]
  rw [hbe]
  have hm := valC_mem h uet.1 uet.2 etR Z
  rw [huet] at hm
  have hpos : 0 < nrmC fn (yP Z) ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) P :=
    nrmC_pos fn (yP Z) hfn P hm (valC_ne_zero (het Z))
  have he' : nrmC fn (yP Z) ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) P ≤
      recNrm (U σ) xR uet.1 uet.2 etR k x := by
    rw [← huet]; exact he
  have hlog := Real.log_le_log hpos (he'.trans h2)
  rw [Real.log_exp] at hlog
  set e := Real.log (nrmC fn (yP Z) ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) P)
  set φ := ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th x
  have hi' : (0 : ℝ) < i := Nat.cast_pos.2 hi
  have h3 : φ - tableLineDegreeTwo ≤ -e / i := by
    rw [le_div_iff₀ hi']; nlinarith
  have key : cc * φ ≤ cc / (i : ℝ) * (-e) + cc * tableLineDegreeTwo :=
    calc cc * φ = cc * (φ - tableLineDegreeTwo) + cc * tableLineDegreeTwo := by ring
      _ ≤ cc * (-e / i) + cc * tableLineDegreeTwo := by gcongr
      _ = cc / (i : ℝ) * (-e) + cc * tableLineDegreeTwo := by ring
  linarith

end Gen

section Rec

variable {D : D7} {T : Top D} (hL : LawsP T)

variable (j : ℕ) [IsCMField D.host.E] [Fintype (Comp (T.Q.Xo j) T.Q.c)]

end Rec

end Formalism.L2.Pj
end
end
