module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1785
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHomogeneousSecZGenFix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle729
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem inPsi_orbit_parity {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {h : ℕ}
    (hh : 0 < h) (lab : ZMod h → (E →+* ℂ)) (hstep : ∀ s, InPsi H (lab (s + 1)) ↔ ¬ InPsi H (lab s))
    (h0 : InPsi H (lab 0)) : Even h ∧ ∀ s : ZMod h, InPsi H (lab s) ↔ Even s.val := by
  have hn : ∀ n : ℕ, InPsi H (lab (n : ZMod h)) ↔ Even n := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [Nat.cast_succ, hstep, ih, Nat.even_add_one]
  haveI : NeZero h := ⟨hh.ne'⟩
  refine ⟨(hn h).1 (by simpa [ZMod.natCast_self] using h0), fun s => ?_⟩
  have := hn s.val
  rwa [ZMod.natCast_zmod_val] at this

theorem facBetween_fine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), p ≠ 2 → ¬ (p : ℤ) ∣ discr E → InertInK H p → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → 1 ≤ k → ∃ A B : ℝ, FacBetween Xo la f k A B ∧ B - A ≤ boundFine p (Dw.p + Dw.q) Dw.q (rk f) k := by
  intro E _ _ _ H Dw l Xo c p _ la hp2 hdisc hin f k hf hk
  letI := H.starRing
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpp : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hL : 0 ≤ Real.logb p k := Real.logb_nonneg hp1 (by exact_mod_cast hk)
  refine ⟨((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p / ((p : ℝ) ^ 2 - 1) - (rk f : ℝ) ^ 2 * (Real.logb p k + 1),
    k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)), ?_, ?_⟩
  · intro T io e ho y
    refine ⟨le_nuFac fun Ch X => ?_, fun halg =>
      (GlobalTheory.T.factorDepth_upperBound_oddUnramifiedPrime E H Dw l Xo c p T io y (not_isUnit_of_overLa la ho) halg hp2 hdisc f k hf).2 hin⟩
    obtain ⟨hfrob, hty⟩ := GlobalTheory.T.formalGroup_rootsOfUnity_typed_lieRanks E H Dw l Xo c (fun _ => rfl) p hdisc T io X
    obtain ⟨h, hh0, -, lab, horb, d', G', ty, I, P, -, ⟨mu⟩, -, hcard, hfr⟩ := hty y Ch f.1
    have hstep : ∀ s, InPsi H (lab (s + 1)) ↔ ¬ InPsi H (lab s) := by
      intro s
      rw [((hfrob _ _ (horb.2.1 s)).2 hin)]
      constructor
      · intro h1 h2
        exact ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.not_inPsi_both H (lab s) ⟨h2, h1⟩
      · intro h1
        exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H (lab s)).resolve_left h1
    obtain ⟨hev, hpar⟩ := inPsi_orbit_parity hh0 lab hstep (by rw [horb.1]; exact hf)
    have hodd : ∀ s : ZMod h, Odd s.val → (Finset.univ.filter fun a => ty a = s).card ≤ Dw.q := by
      intro s hs
      have hn : ¬ InPsi H (lab s) := fun h1 => (Nat.not_even_iff_odd.2 hs) ((hpar s).1 h1)
      have h2 := hcard s
      rw [if_neg hn] at h2
      rw [← h2, Fintype.card_subtype]
    obtain ⟨hsat, hzero, hdep⟩ := hfr 0 f horb.1.symm
    obtain ⟨cr, -, hcr, hlow⟩ := GlobalTheory.T.detDepth_lower_bound_saturated_even_type X.C (vX_vp X) p hp (vX_vp_p X) hp3 d' h hh0 hev ty G' mu Dw.q hodd
      (0 : ZMod h) (by simp) (rk f) k hk (fun a => P.mulVec (frame Ch X f a)) hsat hzero
    rw [nuFacC, ← hdep] at *
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) hlow
    have h3 : ((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p ≤ ((rk f : ℝ) - cr) * k * p := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have h4 := div_le_div_of_nonneg_right h3 hpp.le
    linarith
  · have hab : (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ 1 / ((p : ℝ) - 1) := by
      rw [div_le_div_iff₀ hpp (by linarith)]
      nlinarith
    have hkey : boundFine p (Dw.p + Dw.q) Dw.q (rk f) k -
        (k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)) -
          (((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p / ((p : ℝ) ^ 2 - 1) - (rk f : ℝ) ^ 2 * (Real.logb p k + 1))) =
        (k : ℝ) * Dw.q * (1 / 2 * (1 / ((p : ℝ) - 1)) + (3 / 2 + Real.logb p k / 2) * (1 / ((p : ℝ) - 1) - (p : ℝ) / ((p : ℝ) ^ 2 - 1))) := by
      unfold boundFine
      push_cast
      ring
    have hpos : 0 ≤ (k : ℝ) * Dw.q * (1 / 2 * (1 / ((p : ℝ) - 1)) + (3 / 2 + Real.logb p k / 2) * (1 / ((p : ℝ) - 1) - (p : ℝ) / ((p : ℝ) ^ 2 - 1))) := by
      have hb : 0 ≤ 1 / ((p : ℝ) - 1) := by apply div_nonneg <;> linarith
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ 3 / 2 + Real.logb p k / 2) (sub_nonneg.2 hab)
      positivity
    linarith

end GlobalTheory.RefSum
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel


theorem _root_.GlobalTheory.T.exists_routeDatum_finite_pureTensors_vacuum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB ∧
      ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F v) → ℂ)
        (φ₀ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ),
        ΦB = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) ∧
        (∀ k, φ k Bs.v₁ = φ₀) ∧
        ∃ (ι : ((Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ]
              (Matrix (Fin (G.V (.grid i j)).rank) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)) (Fv D.host.F Bs.v₁) → ℂ))
          (P : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁))
          (Λ : Submodule 𝒪[Fv D.host.F Bs.v₁] (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁)) (c : ℂ),
          Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι ∧
          ∀ Y, ι φ₀ Y = c * (matLat (Fin (G.V (.grid i j)).rank) Λ : Set _).indicator 1 (P.val * Y) := by
  first | exact @GlobalTheory.SmallDatum.exists_datum_pure_linBar | exact GlobalTheory.SmallDatum.exists_datum_pure_linBar | (intros; apply GlobalTheory.SmallDatum.exists_datum_pure_linBar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FunObj

theorem squareChars_isGood : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∃ S₀ Q : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      (∀ v ∈ S₀ ∪ Q, (∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) ∧
        Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v)) ∧
      ∀ B : Base D.host.F D.host.E, S₀ ∪ Q ⊆ B.P → B.v₁ ∉ S₀ ∪ Q → SplitsFully D.host.E B.v₁ →
        HasExp B.emb (alpha G t i j) B.mα → HasExp B.emb (beta G i j) B.mβ →
        Chars.IsGood B ⟨alpha G t i j, beta G i j, S₀, Q⟩ (spW G i j).rank (spW₁ G i j).rank := by
  intro D T L sc G μ₀ hL t i j _hst
  refine ⟨G.pl.S0, (L.Q t).image (fun P => P.under (𝓞 D.host.F)) \ G.pl.S0, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · have hw : G.pl.w v ∈ locPl G t := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
      have e := G.pl.under_w hv
      exact ⟨⟨_, hw, e⟩, e ▸ GlobalTheory.T.gridLocalTensorPlaces_over_split_places hL t _ hw⟩
    · obtain ⟨P, hP, e⟩ := Finset.mem_image.1 (Finset.mem_sdiff.1 hv).1
      have hw : P ∈ locPl G t := Finset.mem_union_right _ hP
      exact ⟨⟨P, hw, e⟩, e ▸ GlobalTheory.T.gridLocalTensorPlaces_over_split_places hL t _ hw⟩
  · intro B hsub hv₁ hsp hα hβ
    have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
    obtain ⟨rα, rβ⟩ := GlobalTheory.T.thetaGrid_alpha_beta_restrict_quadratic_pow_rank hL t i j
    refine ⟨?_, ?_, GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow _ _ h2 _ _ rα, GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow _ _ h2 _ _ rβ, hα, hβ, ?_, hsub, ?_, ?_, ?_, ⟨hv₁, hsp⟩⟩
    · have hm := (hL.mu0 j).1
      have hx := (hL.xi t).1
      have he := hL.eta.1
      refine ⟨(hm.1.mul hx.1).mul (he.1.pow _), fun x => ?_⟩
      have e1 := hm.2 x
      have e2 := hx.2 x
      have e3 := he.2 x
      show L.mu0 ((j : ℕ) + 1) _ * L.xi t _ * (L.eta ^ _) _ = 1
      rw [MonoidHom.pow_apply]
      rw [e1, e2, e3]
      simp
    · have hc := (G.ch.chi_eq (D.R.m - (i : ℕ)) (by omega) (by omega)).1
      have he := hL.eta.1
      refine ⟨hc.1.mul (he.1.pow _), fun x => ?_⟩
      have e1 := hc.2 x
      have e3 := he.2 x
      show G.ch.chi (D.R.m - (i : ℕ)) _ * (L.eta ^ _) _ = 1
      rw [MonoidHom.pow_apply, e1, e3]
      simp
    · exact Finset.disjoint_sdiff
    · intro w hw
      rcases Finset.mem_union.1 hw with hw | hw
      · rcases (G.pl.mem_S0_of_sum_eq).1 hw with h | h
        · exact GlobalTheory.T.not_unrAt_of_under_eq_v0 hL t i j w h
        · exact GlobalTheory.T.alpha_div_beta_ramified_first hL t i j w h
      · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hw
        obtain ⟨P, hP, e⟩ := Finset.mem_image.1 h1
        exact GlobalTheory.T.alpha_div_beta_ramified_at_level hL t i j w P hP e h2
    · intro w hw
      have hw' : w.under (𝓞 D.host.F) ∉ G.pl.S0 ∪ ((L.Q t).image (fun P => P.under (𝓞 D.host.F)) \ G.pl.S0) := hw
      refine GlobalTheory.T.alpha_unramified_outside hL t i j w (fun h => hw' (Finset.mem_union_left _ h)) fun P hP e => hw' ?_
      by_cases h : w.under (𝓞 D.host.F) ∈ G.pl.S0
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨Finset.mem_image.2 ⟨P, hP, e⟩, h⟩)
    · intro w hw
      have hw' : w.under (𝓞 D.host.F) ∉ G.pl.S0 ∪ ((L.Q t).image (fun P => P.under (𝓞 D.host.F)) \ G.pl.S0) := hw
      exact GlobalTheory.T.beta_unramified_outside hL i j w (fun h => hw' (Finset.mem_union_left _ h))

end GlobalTheory.FunObj

end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic

namespace GlobalTheory.LatFull.CMInt

theorem exists_frame_denom_dominant_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ y : FrPt Xo c z.K, y.x = z.x → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ la : GlobalTheory.AllWt.Weight Dw, (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) (Dw.p - 1)) → ∀ m : ℕ, ∃ N : z.K, N ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la m), (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) → IsIntegral ℤ (N * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz y hy _hp _hq la _hanti _hgap m
  classical
  set e : Formalism.L2.Pj.Ix Dw → ℤ := GlobalTheory.AllWt.exOf Dw la m with he
  let k : (E →+* ℂ) → ℕ := fun b => ∑ i : Fin (Dw.mult b), (-(e (some ⟨b, i⟩))).toNat
  let a : ∀ b : E →+* ℂ, Fin (Dw.mult b) → ℕ := fun b i => (e (some ⟨b, i⟩) + (k b : ℤ)).toNat
  have hak : ∀ (b : E →+* ℂ) (i : Fin (Dw.mult b)), e (some ⟨b, i⟩) + (k b : ℤ) = (a b i : ℤ) := by
    intro b i
    have h1 : (-(e (some ⟨b, i⟩))).toNat ≤ k b :=
      Finset.single_le_sum (f := fun i : Fin (Dw.mult b) => (-(e (some ⟨b, i⟩))).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only [a]
    omega
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.T.exists_commonDenom_framePolynomials_cmPoint_generator E H Dw l Xo c z f La hz e k
  obtain ⟨g, s, hg, hgs⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c z.K z.y y).1 (hy.trans hz.2.2.2.1.symm)
  let Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K := fun b => (g b).transpose
  have hYd : ∀ b, (Y b).det ≠ 0 := fun b => by
    simp only [Y, Matrix.det_transpose]; exact (hg b).ne_zero
  have hgY : (fun b => (Y b).transpose) = g := funext fun b => Matrix.transpose_transpose _
  obtain ⟨w₀, hw₀, hsw⟩ := GlobalTheory.FieldPolyZ.exists_frChg_one_evR_eq E H Dw l Xo c z.K z.y y Y s hYd
    (by rw [hgY]; exact hgs)
  obtain ⟨N₀, hN₀, hint⟩ := GlobalTheory.LatFull.CMInt.exists_denom_eval
    (fun _ : Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ => FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 z.K)) ((t : z.K)⁻¹))
    (fun v : Formalism.L2.LamCM.FrVar Dw.mult => Y v.1 v.2.2 v.2.1) (∑ b, ∑ i, a b i)
  have hsu : (((s ^ e none : z.Kˣ)) : z.K) ≠ 0 := Units.ne_zero _
  refine ⟨N₀ * (∏ b, (Y b).det ^ k b) * ((((s ^ e none : z.Kˣ)) : z.K))⁻¹,
    mul_ne_zero (mul_ne_zero hN₀ (Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hYd b))) (inv_ne_zero hsu),
    fun F hF hv => ?_⟩
  obtain ⟨G, hGh, hG⟩ := GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ_genFix E H Dw l Xo c z.K z.y e k a hak F hF
  have h1 := hG w₀ Y hYd hw₀
  have h2 : N₀ * (∏ b, (Y b).det ^ k b) * ((((s ^ e none : z.Kˣ)) : z.K))⁻¹ * evR Xo c F y =
      N₀ * Formalism.L2.LamCM.evalFr G Y := by
    rw [hsw e F hF, ← h1]
    field_simp
  rw [h2]
  refine hint G hGh fun μ => ?_
  rw [FractionalIdeal.mem_spanSingleton]
  refine ⟨⟨_, ht F hF hv G (fun y' Y' hY' h' => hG y' Y' hY' h') μ⟩, ?_⟩
  have htK : (t : z.K) ≠ 0 := fun h => ht0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  change (t : z.K) * AddMonoidAlgebra.coeff G μ * (t : z.K)⁻¹ = _
  field_simp

end GlobalTheory.LatFull.CMInt
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)

open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic

namespace GlobalTheory.LatFull.CMInt

theorem exists_frame_denom_dominant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ y : FrPt Xo c z.K, y.x = z.x → 1 ≤ (Dw).p → 1 ≤ (Dw).q → ∀ la : GlobalTheory.AllWt.Weight (Dw), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((Dw).p - 1)) → ∃ N : z.K, N ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0), (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) → IsIntegral ℤ (N * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz y hy _hp _hq la _hanti _hgap
  classical
  set e : Formalism.L2.Pj.Ix Dw → ℤ := GlobalTheory.AllWt.exOf Dw la 0 with he
  have he0 : e none = 0 := by
    simp [he, GlobalTheory.AllWt.exOf, GlobalTheory.AllWt.wtOf, exZ]
  let k : (E →+* ℂ) → ℕ := fun b => ∑ i : Fin (Dw.mult b), (-(e (some ⟨b, i⟩))).toNat
  let a : ∀ b : E →+* ℂ, Fin (Dw.mult b) → ℕ := fun b i => (e (some ⟨b, i⟩) + (k b : ℤ)).toNat
  have hak : ∀ (b : E →+* ℂ) (i : Fin (Dw.mult b)), e (some ⟨b, i⟩) + (k b : ℤ) = (a b i : ℤ) := by
    intro b i
    have h1 : (-(e (some ⟨b, i⟩))).toNat ≤ k b :=
      Finset.single_le_sum (f := fun i : Fin (Dw.mult b) => (-(e (some ⟨b, i⟩))).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only [a]
    omega
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.T.exists_commonDenom_framePolynomials_cmPoint E H Dw l Xo c z f La hz e k he0
  obtain ⟨g, s, hg, hgs⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c z.K z.y y).1 (hy.trans hz.2.2.2.1.symm)
  let Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K := fun b => (g b).transpose
  have hYd : ∀ b, (Y b).det ≠ 0 := fun b => by
    simp only [Y, Matrix.det_transpose]; exact (hg b).ne_zero
  have hgY : (fun b => (Y b).transpose) = g := funext fun b => Matrix.transpose_transpose _
  have htK : (t : z.K) ≠ 0 := fun h => ht0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨N₀, hN₀, hint⟩ := GlobalTheory.LatFull.CMInt.exists_denom_eval
    (fun _ : Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ => FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 z.K)) ((t : z.K)⁻¹))
    (fun v : Formalism.L2.LamCM.FrVar Dw.mult => Y v.1 v.2.2 v.2.1) (∑ b, ∑ i, a b i)
  refine ⟨N₀ * ∏ b, (Y b).det ^ k b, mul_ne_zero hN₀ (Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hYd b)),
    fun F hF hv => ?_⟩
  obtain ⟨G, hGh, hG⟩ := GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ E H Dw l Xo c z.K z.y e k a he0 hak F hF
  have h1 := hG y Y s hYd (by rw [hgY]; exact hgs)
  have h2 : N₀ * (∏ b, (Y b).det ^ k b) * evR Xo c F y = N₀ * Formalism.L2.LamCM.evalFr G Y := by
    rw [mul_assoc, h1]
  rw [h2]
  refine hint G hGh fun μ => ?_
  rw [FractionalIdeal.mem_spanSingleton]
  refine ⟨⟨_, ht F hF hv G (fun y' Y' s' hY' h' => hG y' Y' s' hY' h') μ⟩, ?_⟩
  change (t : z.K) * AddMonoidAlgebra.coeff G μ * (t : z.K)⁻¹ = _
  field_simp

end GlobalTheory.LatFull.CMInt
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_fieldPoint : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → ∀ (K : Type) [Field K] (s : Sp K ⟶ S), HasRep A g (Over.mk s) := by
  first | exact @GlobalTheory.DualCon.FieldRep.hasRep_field | exact GlobalTheory.DualCon.FieldRep.hasRep_field | (intros; apply GlobalTheory.DualCon.FieldRep.hasRep_field <;> assumption)
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.CovTop

theorem _root_.GlobalTheory.T.complexUniformizationLaws_of_goodDeepCover : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → Laws Y.U (xiR D) := by
  first | exact @GlobalTheory.LawsDeep.laws_deep | exact GlobalTheory.LawsDeep.laws_deep | (intros; apply GlobalTheory.LawsDeep.laws_deep <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_pos_klt_add_smul_effective_divisor : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (B : X → ℚ), 0 < m → IsLogCanonicalMultiple p n Δ m G → (∀ y, KltAt p n Δ y) → IsQCart B → ∃ c : ℚ, 0 < c ∧ ∀ y, KltAt p n (Δ + c • B) y := by
  first | exact @GlobalTheory.PairStep.exists_pos_kltAt_add_smul | exact GlobalTheory.PairStep.exists_pos_kltAt_add_smul | (intros; apply GlobalTheory.PairStep.exists_pos_kltAt_add_smul <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_rational_logCanonicalThreshold_at_point : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (D B : X → ℚ) (x : X), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → IsQCart B → KltAt p n (Δ + D) x → ¬ KltAt p n (Δ + D + B) x → ∃ c : ℚ, 0 < c ∧ c ≤ 1 ∧ LcAt p n (Δ + D + c • B) x ∧ ¬ KltAt p n (Δ + D + c • B) x := by
  first | exact @GlobalTheory.PairStep.exists_threshold_lcAt_not_kltAt | exact GlobalTheory.PairStep.exists_threshold_lcAt_not_kltAt | (intros; apply GlobalTheory.PairStep.exists_threshold_lcAt_not_kltAt <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.howe_finite_length_tensor_product_factors : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)) (C : ∀ w, Submodule ℂ (V w)), (∀ w, Pack (a w) (C w)) → HoweAlg (fun w => actAt w (a w)) (tensAny C) := by
  first | exact @GlobalTheory.HoweR.howeAlg_tensAny | exact GlobalTheory.HoweR.howeAlg_tensAny | (intros; apply GlobalTheory.HoweR.howeAlg_tensAny <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RankCoinv


open GlobalTheory.SplitFlip in
theorem exists_soLoc_sub_mem_augAt : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v,
    X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ t : E →ₐ[F] Fv F v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₀ ∈ G.M'.SoLoc B.ψ t, φ - φ₀ ∈ augAt om' v := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hν t φ hφ
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_bar_good_place hP F E σ B a a' G X om om' hT v hv t
  obtain ⟨ν₀, hν₀, hf⟩ := GlobalTheory.T.exists_unramified_character_good hP F E σ B a a' G X om om' hT v hv hν t
  have hspan : Submodule.span ℂ {Z | ∃ g : GL (Fin a') (Fv F v), ∃ Ψ' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      Z = omB ν₀ ν₀ g 1 Ψ' - Ψ'} ≤ (augAt om' v ⊓ SB _).map ι := by
    rw [Submodule.span_le]
    rintro Z ⟨g₀, Ψ', hΨ', rfl⟩
    obtain ⟨φ', hφ', rfl⟩ := hι.bij.surjOn hΨ'
    obtain ⟨g, hg, hact⟩ := hf ι hι g₀
    obtain ⟨φ₁, hφ₁, hA, hE⟩ := hact φ' hφ'
    refine ⟨φ₁ - φ', ⟨Submodule.subset_span ⟨g, hg, φ', hφ', φ₁, hφ₁, hA, rfl⟩, Submodule.sub_mem _ hφ₁ hφ'⟩, ?_⟩
    simp [map_sub, hE]
  obtain ⟨Ψ₀, -, hrk, hmem⟩ := GlobalTheory.T.schwartzBruhat_full_rank_modulo_translates (Fv F v) a' (a + a') ν₀ (unifAt v)
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec hν₀ (ι φ) (hι.bij.mapsTo hφ)
  obtain ⟨n, ⟨hnA, hnSB⟩, hn⟩ := hspan hmem
  refine ⟨φ - n, ⟨Submodule.sub_mem _ hφ hnSB, ι, hι, fun Y hY => ?_⟩, by simpa using hnA⟩
  have : ι (φ - n) = Ψ₀ := by rw [map_sub, hn]; abel
  rw [this]; exact hrk Y hY

end GlobalTheory.RankCoinv
end
