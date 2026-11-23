module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle399
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle388
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle026
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle060
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle079
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormOfParts
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle081
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle064
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open scoped CommRingCat.HomTopology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc.Leave

theorem block_of_span_le {N p : ℕ} {M M' : Matrix (Fin N) (Fin N) ℂ} (hM : M.det ≠ 0)
    (h : Submodule.span ℂ (col M' '' {a | (a : ℕ) < p}) ≤ Submodule.span ℂ (col M '' {a | (a : ℕ) < p}))
    (a b : Fin N) (ha : p ≤ a) (hb : (b : ℕ) < p) : (M⁻¹ * M') a b = 0 := by
  let L : (Fin N → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj a).comp (Matrix.mulVecLin M⁻¹)
  have hL : ∀ (P : Matrix (Fin N) (Fin N) ℂ) (d : Fin N), L (col P d) = (M⁻¹ * P) a d := fun _ _ => rfl
  have h1 : Submodule.span ℂ (col M '' {a | (a : ℕ) < p}) ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    show L (col M d) = 0
    rw [hL, Matrix.nonsing_inv_mul _ hM.isUnit]
    exact Matrix.one_apply_ne fun e => absurd (show (d : ℕ) < p from hd) (by rw [← e]; omega)
  exact (hL M' b).symm.trans (h1 (h (Submodule.subset_span ⟨b, hb, rfl⟩)))

theorem imTop_neBot : imTop.NeBot :=
  Filter.comap_neBot fun t ht => by
    obtain ⟨a, ha⟩ := Filter.nonempty_of_mem ht
    exact ⟨a * Complex.I, by simpa using ha⟩

theorem tendsto_eTwoPi : Tendsto eTwoPi imTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : Tendsto (fun w : ℂ => Real.exp (-(2 * Real.pi * w.im))) imTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop (by positivity) tendsto_comap)
  refine h.congr fun w => ?_
  simp [eTwoPi, Complex.norm_exp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {N : ℕ} {U : Unf Xo c σ N}

theorem x_eq_of_samePos (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (x x' : (U.X k).dom)
    (h : SamePos (U.X k) x.1 x'.1) : (U.un k x).x = (U.un k x').x :=
  GlobalTheory.TrueCx.PointWell.pt_eq_of_block (U := Formalism.L2.PjFree.Unf.ofPj U) hU hσ k x x'
    (fun τ => block_of_span_le (x.2 τ).1 (h τ).ge) fun τ => block_of_span_le (x'.2 τ).1 (h τ).le

theorem isHolTo_ptC (hU : IsUnf U) (k : U.Comp) (s : Frame (U.X k).Ψ N → (U.X k).dom)
    (hs : ∀ x ∈ (U.X k).dom, (s x).1 = x) : IsHolTo (U.X k).dom fun x => GlobalTheory.TrueCx.ptC (U.un k (s x)) := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hun⟩ := hU
  choose P hP hP' hx _ using hun k
  let L : Frame (U.X k).Ψ N ≃L[ℂ] (Fin (Module.finrank ℂ (Frame (U.X k).Ψ N)) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp only [Module.finrank_fin_fun])
  have ho : IsOpen (U.X k).dom := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _
  have hB := ho.preimage L.symm.continuous
  have h1 := (F.hol (ik k) _ _ (fun b => P (s (L.symm b))) hB ⟨fun b _ => hP' _, fun a =>
    differentiableOn_pi.2 fun i => by
      simp only [hP]
      refine GlobalTheory.TrueCx.TorHolo.differentiableOn_perFr _ (fun b _ => (s _).2) (fun τ a d => ?_) _ _ _
      refine (differentiable_pi.1 (differentiable_pi.1 (differentiable_pi.1 L.symm.differentiable τ) a)
        d).differentiableOn.congr fun b hb => ?_
      rw [hs _ hb]
      rfl⟩).1
  have h2 : IsHolTo (L.symm ⁻¹' (U.X k).dom) fun b => GlobalTheory.TrueCx.ptC (U.un k (s (L.symm b))) := by
    refine GlobalTheory.TrueCx.TorHolo.isHolTo_of_fst _ _ hB _ (fun b => GlobalTheory.TrueCx.ptC_snd _) ?_
    simp only [GlobalTheory.TrueCx.ptC_fst]
    exact LocLift.isHolTo_congr h1 fun b _ => hx _
  refine LocLift.isHolTo_congr (LocLift.isHolTo_comp h2 ho L.differentiableOn fun v hv => ?_) fun v _ => ?_
  · rwa [Set.mem_preimage, L.symm_apply_apply]
  · rw [L.symm_apply_apply]

theorem lift_not_converges : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsBdArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsLift U k y T xx → ∀ x₀ ∈ (U.X k).dom, ∀ x' : ℂ → Frame (U.X k).Ψ N, Tendsto x' imTop (𝓝 x₀) → ¬ ∀ᶠ w in imTop, x' w ∈ (U.X k).dom ∧ SamePos (U.X k) (xx w) (x' w) := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T xx hσ hU ⟨⟨⟨hr, hψ⟩, hxs, hφ⟩, hb0, _⟩ hm hl x₀ hx₀ x' ht hev
  have := isProper_genStr Z
  have := imTop_neBot
  let s : Frame (U.X k).Ψ N → (U.X k).dom := fun v => if h : v ∈ (U.X k).dom then ⟨v, h⟩ else ⟨x₀, hx₀⟩
  have hs : ∀ v (h : v ∈ (U.X k).dom), s v = ⟨v, h⟩ := fun v h => dif_pos h
  let pt : Frame (U.X k).Ψ N → CxPts (genStr Z) σ := fun v =>
    ⟨GlobalTheory.TrueCx.ptC (U.un k (s v)) ≫ Z.jQ, by rw [Category.assoc, Z.jQ_over, GlobalTheory.TrueCx.ptC_snd]⟩
  have hc : ContinuousOn pt (U.X k).dom := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo
    (LocLift.isHolTo_comp_hom (isHolTo_ptC hU k s fun v h => by rw [hs v h]) Z.jQ)
  have h1 : Tendsto (fun w => pt (x' w)) imTop (𝓝 (pt x₀)) :=
    (hc.continuousAt ((ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _).mem_nhds hx₀)).tendsto.comp ht
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  let q : CxPts (genStr Z) σ := ⟨spMap (ψ 0) ≫ x, by
    rw [Category.assoc, hxs, ← hφ 0 h0, ← Spec.map_comp]; rfl⟩
  have ha : ContinuousAt (fun u => spMap (ψ u) ≫ x) 0 := by
    refine ((GlobalTheory.Points.continuous_comp x).comp
      (GlobalTheory.Points.continuous_specMap (C := ℂ) (CommRingCat.of A))).continuousAt.comp
      (f := fun u => CommRingCat.ofHom (ψ u)) ?_
    refine (CommRingCat.HomTopology.isEmbedding_hom _ _).isInducing.continuousAt_iff.2 (continuousAt_pi.2 fun a => ?_)
    exact ((hψ a).differentiableAt (Metric.isOpen_ball.mem_nhds h0)).continuousAt
  have h2 : Tendsto (fun w => pt (x' w)) imTop (𝓝 q) := by
    refine tendsto_subtype_rng.2 ((ha.tendsto.comp tendsto_eTwoPi).congr' ?_)
    filter_upwards [hev, tendsto_eTwoPi.eventually (Metric.isOpen_ball.mem_nhds h0),
      (tendsto_comap (f := Complex.im)).eventually (eventually_gt_atTop T)] with w hw hb hT
    obtain ⟨hd, he, -⟩ := hl w hT
    have e1 := (hm _ hb (Complex.exp_ne_zero _)).1
    have e2 : GlobalTheory.TrueCx.ptC (U.un k (s (x' w))) = GlobalTheory.TrueCx.ptC (y (eTwoPi w)) := by
      refine pullback.hom_ext ?_ ((GlobalTheory.TrueCx.ptC_snd _).trans (GlobalTheory.TrueCx.ptC_snd _).symm)
      rw [GlobalTheory.TrueCx.ptC_fst, GlobalTheory.TrueCx.ptC_fst, hs _ hw.1]
      exact (x_eq_of_samePos hσ hU k ⟨_, hd⟩ ⟨_, hw.1⟩ hw.2).symm.trans he
    exact e1.symm.trans (congrArg (· ≫ Z.jQ) e2.symm)
  have h3 : (pt x₀).1 = q.1 := congrArg Subtype.val (tendsto_nhds_unique h1 h2)
  refine mem_genBd.1 (hb0 (IsLocalRing.closedPoint ℂ)) ⟨GlobalTheory.TrueCx.ptC (U.un k (s x₀)) (IsLocalRing.closedPoint ℂ), ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun f : Sp ℂ ⟶ gen Z => f (IsLocalRing.closedPoint ℂ)) h3)

end GlobalTheory.ShFam.BdArc.Leave
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.KeyRel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_sameLie {S : Type} [CommRing S] [Algebra c.F S] [IsLocalRing S] {e : Ix Dw → ℤ} (he : e none = 0)
    {g : Rul Xo c} (hg : g ∈ GlobalTheory.AllWt.secZ Xo c e) {y y' : FrPt Xo c S} (h : SameLie y y') :
    evR Xo c g y' = evR Xo c g y := by
  obtain ⟨g0, a, -, hc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c S y y').1 h.1.symm
  have h1 := (GlobalTheory.Frames.frChg_calculus E H Dw l Xo c S).2.1 y
  let T : Ix Dw → Sˣ := fun k => k.elim a fun _ => 1
  have hb : FrBor T y y' := ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c S).2.2.2 T y y').2
    ⟨fun _ => 1, fun τ i => Matrix.one_apply_eq i, fun τ i j hij => Matrix.one_apply_ne hij.ne, hc.1,
      fun τ i => h.2 τ i ▸ h1.2.1 τ i, hc.2.2⟩
  rw [GlobalTheory.FlagTan.evR_frBor hg hb, Fintype.prod_option, he, zpow_zero, _root_.one_mul]
  simp [T]

end GlobalTheory.ShFam.KeyRel
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem kch_eq_one_of_wchar {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {S : Type} [CommRing S] (t : Ix Dw → Sˣ)
    (h : wchar (Formalism.L2.Pj.ex Dw (fun _ => 1) 0) t = wchar (Formalism.L2.Pj.ex Dw (fun _ => 0) 2) t) : kch t = 1 := by
  rw [kch_eq, mul_inv_eq_one]
  apply Units.ext
  simp only [wchar, Fintype.prod_option, Formalism.L2.Pj.ex, pow_zero, pow_one, one_mul, Finset.prod_const_one,
    mul_one] at h
  rw [Units.coe_prod, Units.val_pow_eq_pow_val]
  exact h

theorem rootVal_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : _root_.GlobalTheory.FrameUnif.ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → FramesOK e F M un → ∀ (y : FrPt Xo c (CAt σ)) (v v' : ℂ), RootVal (unfOf e F M un) y v → RootVal (unfOf e F M un) y v' → v = v' := by
  intro E _ _ _ H Dw l Xo c σ g e F r M un hσ hM hN hun y v v' hv hv'
  obtain ⟨k, x, t, ht, rfl⟩ := hv
  obtain ⟨k', x', t', ht', rfl⟩ := hv'
  obtain ⟨-, hmul, hinv, huniq⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  have h0 : FrBor (t * t'⁻¹) (un k x) (un k' x') := hmul _ _ _ _ _ ht (hinv _ _ _ ht')
  obtain ⟨γ, hγ, b, hb, heq⟩ := (fibre_unfOf e F M un hun hM
    (GlobalTheory.FibreFlag.fibTri E H Dw l Xo c σ g e F r M hσ hM hN) k k' x x').1 ⟨_, h0⟩
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 heq
  have h3 : x'.1 = rmul (lact γ x.1) b := eq_of_heq h2
  have hxg : lact γ x.1 ∈ (M.X k').dom := (hM.domStab k' x.1 x.2).2 γ hγ
  obtain ⟨t1, ht1, hw1⟩ := hun.2.2.1 k' γ hγ x hxg
  have hxb : rmul (⟨lact γ x.1, hxg⟩ : (M.X k').dom).1 b ∈ (M.X k').dom := by
    have hx2 := x'.2
    rw [h3] at hx2
    exact hx2
  obtain ⟨t2, ht2, hw2⟩ := hun.2.1 k' ⟨lact γ x.1, hxg⟩ b hb hxb
  have hx' : (⟨rmul (lact γ x.1) b, hxb⟩ : (M.X k').dom) = x' := Subtype.ext h3.symm
  rw [hx'] at ht2
  have h12 : t * t'⁻¹ = t1 * t2 := huniq _ _ _ _ h0 (hmul _ _ _ _ _ ht1 ht2)
  have d1 : Formalism.L2.Pj.Dom (fun _ : (E →+* ℂ) × ℕ => 1) 0 := ⟨fun _ => antitone_const, by decide⟩
  have d2 : Formalism.L2.Pj.Dom (fun _ : (E →+* ℂ) × ℕ => 0) 2 := ⟨fun _ => antitone_const, by decide⟩
  have k1 : kch t1 = 1 := kch_eq_one_of_wchar t1 ((hw1 _ _ d1).trans (hw1 _ _ d2).symm)
  have hla : Formalism.L2.PjFree.laU (unfOf e F M un) (fun _ => 1) 0 k' =
      Formalism.L2.PjFree.laU (unfOf e F M un) (fun _ => 0) 2 k' := by
    funext τ j
    simp only [Formalism.L2.PjFree.laU]
    split_ifs <;> simp
  have k2 : kch t2 = 1 :=
    kch_eq_one_of_wchar t2 ((hw2 _ _ d1).trans ((congrArg (fun la => bchar la b) hla).trans (hw2 _ _ d2).symm))
  have hk := congrArg kch h12
  rw [kch_mul, kch_mul, kch_inv, k1, k2, one_mul, mul_inv_eq_one] at hk
  rw [hk]

end GlobalTheory.KeyFourth
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

section Unif

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.OrthoMetric GlobalTheory.ArchMetricCompare Formalism.L2.LamCM GlobalTheory.CM GlobalTheory.Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem exists_unif_of_frame {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) (i : Fin F.n)
    {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) {y : Sp ℂ ⟶ Xo.X} (hy : y = F.u i P)
    {s : LB.Sec (PPx y)} (Φ : FibKey Xo ℂ y) (ht : SecTie Φ.m Φ.th s)
    {θ : (Fin g → ℂ) → ℂ} {fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ}
    (c₁ : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (c₂ : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (c₃ : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex i P z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
      (Xo.univ.t.PP.L.g j j').val * fr j' z)
    (c₄ : ∀ j, ⊤ ≤ (F.ex i P 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' y ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
      (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (c₆ : ∀ j z (pt : Sp ℂ ⟶ Gx y), pt ≫ gxFst y = (F.ex i P z).left → pt ≫ gxSnd y = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) :
    ∃ u : HolUnif Φ.key.P.A Φ.key.P.L g, u.Λ = P.range.toIntSubmodule ∧
      u.IsRig Φ.key.rig ∧ u.IsFn Φ.key.th θ ∧ ∀ z, (u.ex z).left ≫ Φ.m.φ = (F.ex i P z).left := by
  subst hy
  obtain ⟨w, ⟨hw, hrig⟩, hth⟩ := val_tie Φ.m ht
  obtain ⟨w', hw', hinv⟩ := ConjUnif.exists_inv w hw
  have hL := Φ.T.t.PP.isLB
  have hM := LB.isLB_pull Xo.univ.t.PP.isLB Φ.m.φ
  have hol := isHolTo_exp F i hP
  let u₁ := fibreUnif Φ.m.cart (F.ex i P) P.range fr (F.ex_add i P hP) (F.ex_onto i P hP) (F.ex_ker i P hP)
    hP.2.2.1 hP.2.2.2.1 hol c₁ c₂ c₃
  have hex : ∀ z, (u₁.ex z).left ≫ Φ.m.φ = (F.ex i P z).left := fun z => liftPt_comp Φ.m.cart _
  have hle : ∀ z j, ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ (Xo.univ.t.PP.L.pull Φ.m.φ).U j →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (j PUnit.unit) := fun z j => (lift_le Φ.m.cart _ j).1
  have hfr : ∀ (j : Xo.univ.t.PP.L.ι) (k : Φ.T.t.PP.L.ι) (z : Fin g → ℂ),
      ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ ((Xo.univ.t.PP.L.pull Φ.m.φ).U (fun _ => j) ⊓ Φ.T.t.PP.L.U k) →
      valAt' (u₁.ex z).left ((Xo.univ.t.PP.L.pull Φ.m.φ).U (fun _ => j) ⊓ Φ.T.t.PP.L.U k)
        (w.s (fun _ => j, k)).val * (carry u₁ hM hL hw').fr k z = fr j z := by
    intro j k z hz
    obtain ⟨hj, hk⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [carry_fr u₁ hM hL hw' k (fun _ => j) z hk hj, hinv _ _ _ hz]
    exact mul_inv_cancel_left₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j, k))) _
  refine ⟨carry u₁ hM hL hw', rfl, ?_, ?_, hex⟩
  · intro k hk
    have h0 : (u₁.ex 0).left = eSec Φ.T.t.G := by
      rw [(u₁.ker 0).2 u₁.Λ.zero_mem, Hom.one_def]
      simp [eSec]
    obtain ⟨j, hj⟩ := exists_chart_at hM (u₁.ex 0).left
    have hk' : ⊤ ≤ (u₁.ex 0).left ⁻¹ᵁ Φ.T.t.PP.L.U (k PUnit.unit) := by
      rw [h0]
      exact fun p hp => mem_pull.1 (hk hp)
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hk'⟩
    have e := hfr (j PUnit.unit) (k PUnit.unit) 0 hz
    rw [c₄ _ (hle 0 j hj), h0] at e
    rw [h0] at hz
    have e' := val_rig Φ.m.cm.e_comm w Φ.T.t.PP.rig Xo.univ.t.PP.rig hrig (j PUnit.unit) (k PUnit.unit) hz
    rw [Φ.m.base] at e'
    exact mul_left_cancel₀ (valAt'_unit_ne_zero _ hz _) (e.trans e')
  · intro k z hk
    obtain ⟨j, hj⟩ := exists_chart_at hM (u₁.ex z).left
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hk⟩
    obtain ⟨pt, p₁, p₂, hpt⟩ := hth (u₁.ex z).left (Over.w _)
    have e := hfr (j PUnit.unit) k z hz
    refine mul_left_cancel₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j PUnit.unit, k))) ?_
    have e₁ := hpt (j PUnit.unit) k hz
    have e₂ := c₆ (j PUnit.unit) z pt (p₁.trans (hex z)) p₂ (hle z j hj)
    rw [← e] at e₂
    exact e₁.symm.trans (e₂.trans (mul_left_comm _ _ _))

end Unif

theorem mulVec_period {g : ℕ} {La : Type} [AddCommGroup La] (P : La →+ (Fin g → ℂ))
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (h τ : Matrix (Fin g) (Fin g) ℂ)
    (hn : ∀ i, h *ᵥ P (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1) (a : Fin g ⊕ Fin g → ℤ) :
    h *ᵥ P (bas a) = (fun i => (a (Sum.inl i) : ℂ)) + τ *ᵥ (fun i => (a (Sum.inr i) : ℂ)) := by
  have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
    intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
  have h2 : a = ∑ s, a s • (Pi.single s 1 : Fin g ⊕ Fin g → ℤ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [h1 (fun i => a (Sum.inl i)), h1 (fun i => a (Sum.inr i))]
  conv_lhs => rw [h2]

  simp only [map_sum, map_zsmul, Fintype.sum_sum_type, map_add (f := _), Matrix.mulVec_add, Matrix.mulVec_sum,
  Matrix.mulVec_smul, (hn _).1, (hn _).2]

theorem normalAt_of_coord (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) {La : Type} [AddCommGroup La]
    (P : La →+ (Fin x.P.g → ℂ)) (bas : (Fin x.P.g ⊕ Fin x.P.g → ℤ) ≃ₗ[ℤ] La)
    (h τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₁ c₂ : Fin x.P.g → ℂ) (a : ℂ) (hu : IsUnit h.det)
    (hsymm : τ.IsSymm) (hpos : (τ.map Complex.im).PosDef)
    (hn : ∀ i, h *ᵥ P (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1)
    (hΛ : u.Λ = P.range.toIntSubmodule) (hR : u.IsRig x.rig)
    (hF : u.IsFn x.th fun z => a * thetaChar τ c₁ c₂ (h *ᵥ z)) (hD : ∀ i, u.IsDiff (Pi.single i 1) (x.v i)) :
    KeyPow.NormalAt x τ ((2 * Real.pi * Complex.I : ℂ) • hᵀ) c₁ c₂ a := by
  let φ : (Fin x.P.g → ℂ) ≃L[ℂ] (Fin x.P.g → ℂ) :=
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).symm.toContinuousLinearEquiv
  have hφ : ∀ z, h *ᵥ φ z = z := fun z =>
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).apply_symm_apply z
  have hφ' : ∀ z, φ (h *ᵥ z) = z := fun z =>
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).symm_apply_apply z
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  clear_value φ
  refine ⟨KeyNormalForm.change u φ (fun _ => 0) (differentiable_const _), hsymm, hpos, fun z => ?_,
    KeyNormalForm.isRig_change u φ _ _ rfl hR,
    KeyNormalForm.isFn_change u φ _ _ hF fun z => by simp only [hφ, Complex.exp_zero, mul_one],
    fun i => KeyNormalForm.isDiff_change u φ _ _ ?_⟩
  · rw [KeyNormalForm.mem_change, hΛ]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨m, rfl⟩ := bas.surjective v
      refine ⟨fun i => m (Sum.inl i), fun i => m (Sum.inr i), ?_⟩
      rw [← hφ z, ← hv]
      exact mulVec_period _ bas _ _ hn m
    · rintro ⟨m, n, rfl⟩
      refine ⟨bas (Sum.elim m n), ?_⟩
      rw [← hφ' (P _), mulVec_period _ bas _ _ hn]
      rfl
  · have e₁ : (2 * Real.pi * Complex.I : ℂ)⁻¹ • ((2 * Real.pi * Complex.I : ℂ) • hᵀ) i = h *ᵥ Pi.single i 1 := by
      funext j
      simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.mulVec_single_one,
        Matrix.col_apply]
      rw [inv_mul_cancel_left₀ hπ]
    rw [e₁, hφ']
    exact hD i

theorem value_at_thetaPt : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : _root_.GlobalTheory.FrameUnif.ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (a : ℂ) (y : FrPt Xo c (CAt σ)) (Φ : FibKey Xo ℂ y.x), a ≠ 0 → IsThetaPt T b a y → Tied (S := ℂ) e y.s y.u Φ → a ^ 8 * (κ ℂ Φ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g * (T.h b).det) ^ 4 := by
  intro κ hH hT E _ _ _ H Dw l Xo c σ g e F r M k T b hb a y Φ ha ⟨hx, hder, hsec⟩ ⟨ht, hg, hv⟩
  subst hg
  have hP := T.isPer _ hb
  obtain ⟨hu, hsymm, hpos, hn⟩ := T.norm b hb
  have hj : Differentiable ℂ (fun z : Fin Φ.T.g → ℂ => (b, z)) := by fun_prop
  obtain ⟨u, hΛ, hR, hF, hex⟩ := exists_unif_of_frame F k hP hx Φ ht
    (θ := fun z => a * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z)) (fr := fun j z => T.fr j (b, z))
    (fun j => (T.fr_hol j).comp hj.differentiableOn fun z hz => ⟨hb, hz⟩)
    (fun j z hz => T.fr_ne j b z hb hz) (fun j j' z hz => T.fr_coc j j' b z hb hz)
    (fun j hj => (T.fr_rig j b hb hj).trans (congrArg (fun q => valAt' q _ _) hx.symm)) hsec
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hN := normalAt_of_coord Φ.key u _ T.bas (T.h b) (T.ta b) T.c₁ T.c₂ a hu hsymm hpos hn hΛ hR hF fun i => by
    obtain ⟨W, hW, -⟩ := (existsUnique_isDiff_and_linear Φ.key u).1 _ (Φ.basis.1 i)
    have d := OrthoMetric.isDerivAt0_comp u Φ.m.φ (e := fun z => (F.ex k (T.Pf (T.co b)) z).left) hex (Φ.basis.1 i) hW
    have d' := hder (e i).1 (e i).2
    rw [show e.symm ⟨(e i).1, (e i).2⟩ = i from e.symm_apply_apply i,
      ← show _ = y.u (e i).1 (e i).2 from hv i] at d'
    obtain ⟨t₁, -, t₃⟩ := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ F k _ hP
    have hWi : W = Pi.single i 1 := (t₃ _ (t₁ _ _ d)).unique d d'
    exact hWi ▸ hW
  have hdet : ((2 * Real.pi * Complex.I : ℂ) • (T.h b)ᵀ).det = (2 * Real.pi * Complex.I) ^ Φ.T.g * (T.h b).det := by
    rw [Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
  have key := KeyCl.value_of_normalAt hH hT Φ.key ⟨T.half₁, T.half₂⟩ ha
    (hdet.trans_ne (mul_ne_zero (pow_ne_zero _ hπ) hu.ne_zero)) hN
  rw [key, mul_div_cancel₀ _ (pow_ne_zero 8 ha)]
  exact congrArg (· ^ 4) hdet

end GlobalTheory.KeyFourth
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem card_frame_index {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    Module.finrank ℚ E / 2 * (Dw.p + Dw.q) = g := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => τ (H.rt : E) = H.rt0)
  rw [Finset.card_univ, Embeddings.card] at h1
  have h2 := GlobalTheory.PeriodCoord.card_cmType H
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h2
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E),
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  have h4 : (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card = Module.finrank ℚ E / 2 := by
    omega
  have h5 : (Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).card = Module.finrank ℚ E / 2 := by
    omega
  have h6 := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_sigma] at h6
  simp_rw [Fintype.card_fin, Datum.mult] at h6
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h4, h5, smul_eq_mul, smul_eq_mul] at h6
  rw [h6, mul_add]

theorem exists_tied : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S : Type) [CommRing S] [Nontrivial S] [Algebra c.F S] (y : FrPt Xo c S), 1 ≤ Dw.p + Dw.q → ∃ Φ : FibKey Xo S y.x, Tied e y.s y.u Φ := by
  intro E _ _ _ H Dw l Xo c g e S _ _ _ y hpq
  obtain ⟨U, hU, hg⟩ := GlobalTheory.CM.exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp S), Nonempty (SABMap t Xo.univ.t y.x) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull y.x Xo.univ.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨⟨T, rfl, hTg⟩, -⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ y.x U t (hU ▸ m)
  have hpos : 1 ≤ Module.finrank ℚ E / 2 := by
    have h1 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    have h2 : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  have hgp : 1 ≤ T.g := by
    rw [hTg, hg]
    exact Nat.mul_pos hpos hpq
  obtain rfl : T.g = g := hTg.trans (hg.trans (card_frame_index Dw e))
  obtain ⟨-, h₁, h₂⟩ := SecTieEx.secTie_exists_unique E H Dw l Xo S y.x T.t m
  obtain ⟨th, ht⟩ := h₁ y.s
  have hne := (h₂ th _ ht).2.1
    (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo S _ _ y.gen)
  have hB := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c S y.x y.u T.g e y.tan y.eig).1 y.basis
  obtain ⟨hl, hb⟩ := GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo S y.x T.t.G m.φ m.cart
  choose v hv using fun j => hl _ (y.tan (e j).1 (e j).2)
  refine ⟨⟨T, m, hgp, th, hne, v, (hb _ v).2 ?_⟩, ht, rfl, hv⟩
  rw [funext hv]
  exact hB

end GlobalTheory.KeyFourth

end
