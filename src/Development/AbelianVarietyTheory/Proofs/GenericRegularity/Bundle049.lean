module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle023
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle038
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle040
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle013
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.UniformSpace.Uniformizable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle012
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm

theorem fn_continuousOn_good {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r)
    (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) (xR : ℝ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (hx : 0 < xR) (hfn : FnPin U xR fn)
    (σ : c.F →+* ℂ) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (A : Type) [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A]
    (yA : FrPt Xo c A) (X : Type) [TopologicalSpace X] (W : Set X) (φ : X → (A →ₐ[c.F] CAt σ))
    (y : X → FrPt Xo c (CAt σ)) (hφ : ∀ a, ContinuousOn (fun x => Formalism.L2.PjFree.toC (φ x a)) W)
    (hy : ∀ x ∈ W, FrMap (φ x) yA (y x)) (i : Ix Dw) : ContinuousOn (fun x => |fn σ (y x) i|) W := by
  classical
  intro x₀ hx₀
  let ρ : X → (A →+* ℂ) := fun x => (φ x).toRingHom
  have hρ : ∀ x, (ρ x).comp (algebraMap c.F A) = σ := fun x => RingHom.ext fun a => (φ x).commutes a
  have hρc : ∀ a, ContinuousOn (fun x => ρ x a) W := hφ
  obtain ⟨m, s, B, ψ, S, ε, hB, hε, hψ, hd, hnear⟩ := GlobalTheory.T.exists_holomorphic_family_of_ringHom_near c.F A σ (ρ x₀) (hρ x₀)
  let ψ' : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ) := fun b =>
    if h : b ∈ B then
      { (show A →+* CAt σ from ψ b) with commutes' := fun a => RingHom.congr_fun (hψ b h).1 a }
    else φ x₀
  have hψ' : ∀ b ∈ B, ∀ a, Formalism.L2.PjFree.toC (ψ' b a) = ψ b a := by
    intro b hb a
    simp only [ψ', dif_pos hb]
    rfl
  choose z hz using fun b => GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c A (CAt σ) (ψ' b) yA
  have hcont := GlobalTheory.T.frameNorms_continuousOn_holomorphic_framedFamily E H Dw l Xo c r U hU xR fn hx hfn σ hσ A yA m B ψ' z hB
    (fun a => (hd a).congr fun b hb => hψ' b hb a) (fun b _ => hz b) i
  let p : X → (Fin m → ℂ) := fun x j => ρ x (s j)
  have hp : ContinuousWithinAt p W x₀ := continuousWithinAt_pi.2 fun j => hρc (s j) x₀ hx₀
  have hev : ∀ᶠ x in nhdsWithin x₀ W, ∀ a ∈ S, ‖ρ x a - ρ x₀ a‖ < ε := by
    rw [Filter.eventually_all_finset]
    intro a _
    have := Metric.tendsto_nhds.1 (hρc a x₀ hx₀) ε hε
    simpa only [dist_eq_norm] using this
  have key : ∀ x ∈ W, (∀ a ∈ S, ‖ρ x a - ρ x₀ a‖ < ε) → p x ∈ B ∧ y x = z (p x) := by
    intro x hxW h
    obtain ⟨h1, h2⟩ := hnear (ρ x) (hρ x) h
    refine ⟨h1, ?_⟩
    have e : ψ' (p x) = φ x := by
      refine AlgHom.ext fun a => ?_
      have := hψ' (p x) h1 a
      rw [show ψ (p x) = ρ x from h2] at this
      exact this
    have h3 := hz (p x)
    rw [e] at h3
    exact (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c A (CAt σ) (φ x) yA).1 _ _ (hy x hxW) h3
  have h0 := key x₀ hx₀ (fun a _ => by simpa using hε)
  have hc : ContinuousWithinAt (fun x => |fn σ (z (p x)) i|) W x₀ :=
    ContinuousAt.comp_continuousWithinAt (f := p) (g := fun b => |fn σ (z b) i|)
      (hcont.continuousAt (hB.mem_nhds h0.1)) hp
  refine hc.congr_of_eventuallyEq ?_ (by rw [h0.2])
  filter_upwards [hev, self_mem_nhdsWithin] with x h hxW
  rw [(key x hxW h).2]

theorem fn_continuousOn_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (σ : c.F →+* ℂ) (A : Type) [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A] (yA : FrPt Xo c A) (X : Type) [TopologicalSpace X] (W : Set X) (φ : X → (A →ₐ[c.F] CAt σ)) (y : X → FrPt Xo c (CAt σ)), (∀ a, ContinuousOn (fun x => Formalism.L2.PjFree.toC (φ x a)) W) → (∀ x ∈ W, FrMap (φ x) yA (y x)) → ∀ i, ContinuousOn (fun x => |fn σ (y x) i|) W := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hfn σ A _ _ _ yA X _ W φ y hφ hy i
  by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
  · exact fn_continuousOn_good U hU xR fn hx hfn σ hσ A yA X W φ y hφ hy i
  · have hσ' : Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
      have := Formalism.L2.PjFree.goodEmb_goodOf c σ
      unfold Formalism.L2.PjFree.goodOf at this
      rwa [if_neg hσ] at this
    choose z hz using fun x => GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c (CAt σ)
      (CAt ((starRingEnd ℂ).comp σ)) (conjAlg σ) (y x)
    have h := fn_continuousOn_good U hU xR fn hx hfn _ hσ' A yA X W (fun x => (conjAlg σ).comp (φ x)) z
      (fun a => Complex.continuous_conj.comp_continuousOn (hφ a))
      (fun x hxW => frMap_trans (Xo := Xo) (c := c) _ _ _ (φ x) (conjAlg σ) yA (y x) (z x) (hy x hxW) (hz x)) i
    exact h.congr fun x _ => (hfn.2 σ (y x) (z x) (hz x) i).symm

end GlobalTheory.FrameNorm
end

section




noncomputable section

namespace GlobalTheory.CompBij

section Free

open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem frames_nonempty (X : Data E r) : X.dom.Nonempty := by
  classical
  choose P hP hG using X.signature
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have h : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    have hm : mat (Ψ := X.Ψ) (fun τ => P τ) τ = P τ := rfl
    unfold dmin lminor
    rw [hm, hG τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    rw [Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ))]
    rfl
  rw [h, Complex.ofReal_re]
  refine mul_self_pos.2 ?_
  unfold psgn
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  unfold sgn
  split_ifs <;> norm_num

theorem rdU_eq_of_reads (U : Unf Xo c σ r) (h : GenFrEx Xo c) (k : U.Comp)
    (Z : Comp Xo c) (x : (U.X k).dom) (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ)
    (hm : FrMap φ (genFr h Z) y') (hb : FrBor t (U.un k x) y') (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    ∃ w : ℂ, w ≠ 0 ∧ ∀ f ∈ sec Xo c u n, w * rdU U f k x = toC (φ (evC h Z f)) := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨hL, -, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have h3 : wchar (ex Dw u n) t ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (t i).ne_zero
  refine ⟨toC (wchar (ex Dw u n) t), h3, fun f hf => ?_⟩
  have h1 : evR Xo c f y' = φ (evC h Z f) := by
    obtain ⟨q, χ, y₀, hy₀⟩ := hL.test (Om Z) (genFr h Z)
    unfold evC
    rw [GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q χ y₀ _ hy₀,
      GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q (φ.comp χ) y₀ y' (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans χ φ hy₀ hm)]
    rfl
  have h2 : evR Xo c f y' = wchar (ex Dw u n) t * evR Xo c f (U.un k x) :=
    hL.wt u n f hf (CAt σ) t _ _ (hL.test _ _) (hL.test _ _) hb
  have h4 : rdU U f k x = toC (evR Xo c f (U.un k x)) := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk]
    rw [dite_eq_left x.2]
  rw [h4, ← h1, h2]
  rfl

theorem exists_bijection (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (hF : FnAlgClosed (Xo := Xo) (c := c))
    (h : GenFrEx Xo c) :
    ∃ κ : Comp Xo c → U.Comp, Function.Bijective κ ∧
      (∀ Z (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom u n → ∀ f ∈ sec Xo c u n,
        evC h Z f = 0 ↔ ∀ x ∈ (U.X (κ Z)).dom, rdU U f (κ Z) x = 0) ∧
      ∀ Z (φ : Om Z →ₐ[c.F] CAt σ), ∃ x ∈ (U.X (κ Z)).dom, ∀ (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
        ∃ w : ℂ, w ≠ 0 ∧ ∀ f ∈ sec Xo c u n, w * rdU U f (κ Z) x = toC (φ (evC h Z f)) := by
  have hread := GlobalTheory.GenericReading.embedding_read_at_frame E H Dw l Xo c σ r U hσ hU h
  have hconn := GlobalTheory.GeomConn.comp_eq_of_fnAlgClosed E H Dw l Xo c σ r U hσ hU hF h
  have hex : ∀ Z : Comp Xo c, ∃ (k : U.Comp) (x : (U.X k).dom), ∃ (φ : Om Z →ₐ[c.F] CAt σ)
      (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y' := by
    intro Z
    obtain ⟨⟨φ⟩, hφ⟩ := hread Z
    obtain ⟨k, x, y', t, hh⟩ := hφ φ
    exact ⟨k, x, φ, y', t, hh⟩
  choose κ x₀ hκ using hex
  have htie := fun Z => GlobalTheory.evC_eq_zero_iff_rdU_eq_zero E H Dw l Xo c σ r U hσ hU h (κ Z) Z (x₀ Z) (hκ Z)
  refine ⟨κ, ⟨fun Z Z' e => ?_, fun k => ?_⟩, htie, fun Z φ => ?_⟩
  · refine GlobalTheory.Reg.comp_unique_of_reading E H Dw l Xo c σ r U hσ hU h (κ Z) Z Z' (frames_nonempty _) (htie Z) ?_
    rw [e]
    exact htie Z'
  · obtain ⟨Z, S, hS, hg⟩ := GlobalTheory.GenericFrames.exists_comp_generic_off_meagre E H Dw l Xo c σ r U hσ hU h k
    have hd : Dense (⋂ n, (S n)ᶜ) :=
      dense_iInter_of_isOpen (fun n => (hS n).1.isOpen_compl) fun n => interior_eq_empty_iff_dense_compl.1 (hS n).2
    obtain ⟨y, hy, hy'⟩ := hd.inter_open_nonempty _ (FourierCoefficientDomain.isOpen_dom (U.X k)) (frames_nonempty _)
    exact ⟨Z, hconn Z _ _ (x₀ Z) ⟨y, hy⟩ (hκ Z) (hg ⟨y, hy⟩ (Set.mem_iInter.1 hy'))⟩
  · obtain ⟨k, x, y', t, hm, hb⟩ := (hread Z).2 φ
    obtain rfl : k = κ Z := hconn Z _ _ x (x₀ Z) ⟨φ, y', t, hm, hb⟩ (hκ Z)
    exact ⟨x.1, x.2, fun u n => rdU_eq_of_reads U h _ Z x φ y' t hm hb u n⟩

end Free

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

end GlobalTheory.CompBij
end
end

end

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

theorem _root_.GlobalTheory.T.frameNorms_continuousOn_smoothChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (σ : c.F →+* ℂ) (A : Type) [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A] (yA : FrPt Xo c A) (X : Type) [TopologicalSpace X] (W : Set X) (φ : X → (A →ₐ[c.F] CAt σ)) (y : X → FrPt Xo c (CAt σ)), (∀ a, ContinuousOn (fun x => Formalism.L2.PjFree.toC (φ x a)) W) → (∀ x ∈ W, FrMap (φ x) yA (y x)) → ∀ i, ContinuousOn (fun x => |fn σ (y x) i|) W := by
  first | exact @GlobalTheory.FrameNorm.fn_continuousOn_smooth | exact GlobalTheory.FrameNorm.fn_continuousOn_smooth | (intros; apply GlobalTheory.FrameNorm.fn_continuousOn_smooth <;> assumption)

end
end
