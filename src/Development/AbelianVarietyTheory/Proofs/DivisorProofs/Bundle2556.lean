module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle062
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2551
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open Module

namespace GlobalTheory.ShareOn.Alg

theorem finrank_eig_eq {LL G W : Type} [Field LL] [Group G] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (σ : LL →+* ℂ) (f : (Fin n → LL) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun k => f (Pi.single k 1))
    (hsp : Submodule.span ℂ (Set.range f) = ⊤)
    (ρV : G →* ((Fin n → LL) →ₗ[LL] (Fin n → LL))) (ρ : Representation ℂ G W)
    (hρ : ∀ g v, ρ g (f v) = f (ρV g v)) (H : Subgroup G) [Finite H] (μ : H →* LLˣ) :
    finrank ℂ (GlobalTheory.BadCount.eig ρ H ((Units.map σ.toMonoidHom).comp μ)) =
      finrank LL (⨅ h : H, LinearMap.ker (ρV h - ((μ h : LLˣ) : LL) • LinearMap.id) : Submodule LL (Fin n → LL)) := by
  classical
  letI : Algebra LL ℂ := σ.toAlgebra
  letI : Module LL W := Module.compHom W σ
  haveI : IsScalarTower LL ℂ W := ⟨fun a b w => by
    show (σ a * b) • w = σ a • (b • w)
    rw [mul_smul]⟩
  have hsum : ∀ v : Fin n → LL, f v = ∑ k, σ (v k) • f (Pi.single k 1) := by
    intro v
    conv_lhs => rw [show v = ∑ k, v k • Pi.single k (1 : LL) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ]
  have hsp' : ⊤ ≤ Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) := by
    rw [← hsp]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, rfl⟩
    rw [hsum v]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let b : Basis (Fin n) ℂ W := Basis.mk hli hsp'
  let f' : (Fin n → LL) →ₗ[LL] W :=
    { toFun := f, map_add' := f.map_add, map_smul' := fun a v => by
        show f (a • v) = σ a • f v
        rw [map_smulₛₗ] }
  have hf' : f' = Fintype.linearCombination LL b := by
    apply LinearMap.ext
    intro v
    rw [Fintype.linearCombination_apply]
    show f v = _
    rw [hsum v]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Basis.mk_apply]
    rfl
  have hbc : IsBaseChange ℂ f' := hf' ▸ IsBaseChange.of_fintype_basis LL b
  have key := (GlobalTheory.T.finrank_iInf_ker_eq_of_isBaseChange_family LL ℂ (Fin n → LL) W H f' hbc
    (fun h => ρV h - ((μ h : LLˣ) : LL) • LinearMap.id)
    (fun h => ρ h - ((σ (μ h : LLˣ)) : ℂ) • LinearMap.id) (fun h v => by
      show ρ h (f v) - σ ((μ h : LLˣ) : LL) • f v = f (ρV h v - ((μ h : LLˣ) : LL) • v)
      rw [map_sub, map_smulₛₗ, hρ])).1
  exact key

end GlobalTheory.ShareOn.Alg

namespace GlobalTheory.ShareOn.Alg

theorem top_le_span_single {LL W : Type} [Field LL] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (σ : LL →+* ℂ) (f : (Fin n → LL) →ₛₗ[σ] W) (hsp : Submodule.span ℂ (Set.range f) = ⊤) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) := by
  classical
  rw [← hsp]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, rfl⟩
  have hv : v = ∑ k, v k • Pi.single k (1 : LL) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]

  rw [hv, map_sum]
  exact Submodule.sum_mem _ fun k _ => by
    rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem finrank_eq_of_semilinear {LL W : Type} [Field LL] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (σ : LL →+* ℂ) (f : (Fin n → LL) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun k => f (Pi.single k 1))
    (hsp : Submodule.span ℂ (Set.range f) = ⊤) : finrank ℂ W = n := by
  rw [finrank_eq_card_basis (Basis.mk hli (top_le_span_single σ f hsp)), Fintype.card_fin]

end GlobalTheory.ShareOn.Alg

namespace GlobalTheory.ShareOn

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem halfUnip_bot (p : PtAt ex Csz) : HalfUnip p ⊥ := by
  refine ⟨0, fun g hg v => ?_⟩
  rw [Subgroup.mem_bot] at hg
  subst hg
  intro a b
  simp only [map_one, Pi.one_apply, Units.val_one]
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => by rw [h, Matrix.one_apply_eq]⟩

theorem shareW_of_modelAt (p : PtAt ex Csz) (i : Fin D.R.m) (T : ℕ) (y : ℝ) (hy : 0 ≤ y) (hM : ModelAt p i T)
    (hH : HalfUnip p p.P.P0)
    (hs : ∀ p0 : ℕ, p0 ≤ D.R.r → 2 * D.R.r + 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) + 2 ≤ T)
    (he : (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) * (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) + 6) / T ≤ y)) :
    ShareW p i y := by
  obtain ⟨C, hC, _, M, ka, ρ, σ, f, hpull, hρ, hli, hsp, hlev, hcard, hcase⟩ := hM
  let H : Subgroup p.P.Gp := p.P.P0
  let μ : H →* D.what₂.LLˣ := ((p.R.toRealDat.FW i).chi.comp H.subtype) * (p.P.ψ0)⁻¹
  let lam : H →* ℂˣ := (Units.map σ.toMonoidHom).comp μ
  have hty : spType p.R.toRealDat p.F.lv2 i = ⨅ h : H, LinearMap.ker ((p.R.toRealDat.FW i).ρ h -
      ((μ h : D.what₂.LLˣ) : D.what₂.LL) • LinearMap.id) := by
    ext v
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hdim : finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := by
    rw [hty]
    exact Alg.finrank_eig_eq σ f hli hsp (p.R.toRealDat.FW i).ρ ρ hρ H μ
  have hn : finrank ℂ (M.cusp ka) = p.R.toRealDat.nW i := Alg.finrank_eq_of_semilinear σ f hli hsp
  have key : (1 - y) * (finrank ℂ (M.cusp ka) : ℝ) ≤ (Nat.card H : ℝ) * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) := by
    rcases hcase with hdef | ⟨h0, hr, harch⟩
    · have hd := (GlobalTheory.T.definite_cuspForms_finite_regularRepresentation _ _ _ _ M hdef ka ρ hpull).2 H (hlev H hH)
      rw [← Nat.cast_mul, hd.2 lam]
      have : (0 : ℝ) ≤ finrank ℂ (M.cusp ka) := Nat.cast_nonneg _
      nlinarith
    · have hsO : sOf M ≤ T := by
        have := hs M.p0 hr.le
        unfold sOf TwoLevels.dimX
        rw [hcard]
        exact this
      have hR := GlobalTheory.T.twoLevelFlagDomain_cuspForm_ranks_shifted_weights _ _ _ _ M (hlev ⊥ (halfUnip_bot p)) h0 hr ka T harch hsO
      have hS := (GlobalTheory.T.twoLevelFlagDomain_eigenspace_share _ _ _ _ M ka ρ hpull _ _ hR H (hlev H hH) lam).2
      have hY : ((M.dimY : ℝ) * (M.dimY + 6) / T) ≤ y := by
        unfold TwoLevels.dimY
        rw [hcard]
        exact he
      have : (0 : ℝ) ≤ finrank ℂ (M.cusp ka) := Nat.cast_nonneg _
      nlinarith
  unfold ShareW
  rw [← hdim, ← hn]
  exact key

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies Formalism.MainNotions.ArithmeticCylinders

end GlobalTheory.ShareOn
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumSmallSpread not_isBig_iff)

namespace GlobalTheory.RefSum.OscInert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}


open Classical in
theorem two_mul_card_psi_le :
    2 * (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤ Module.finrank ℚ E := by
  have hne : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
    intro h
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
    have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
    simp [pow_two, Complex.mul_re, him] at h2
    have hd : (2:ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    nlinarith [sq_nonneg H.rt0.re]
  have hinj : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤
      (Finset.univ.filter (fun τ : E →+* ℂ => ¬ InPsi H τ)).card := by
    refine Finset.card_le_card_of_injOn (fun τ => (starRingEnd ℂ).comp τ) ?_ ?_
    · intro τ hτ
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
      unfold InPsi at hτ ⊢
      simp only [RingHom.coe_comp, Function.comp_apply, hτ]
      exact hne
    · intro τ _ σ _ h
      ext x
      have := congrArg (fun g : E →+* ℂ => starRingEnd ℂ (g x)) h
      simpa using this
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => InPsi H τ)
  rw [Finset.card_univ, NumberField.Embeddings.card] at htot
  omega


open Classical in
theorem card_big_fiber_le {Dw : Datum H} {F k m : ℕ} (hS : Shape Dw F k m) (τ : E →+* ℂ) :
    (Finset.univ.filter (fun f : Lt1 Dw => _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ f.1 = τ)).card ≤ m + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  calc _ ≤ (Finset.Ico (k - 2) Dw.p).card := by
        refine Finset.card_le_card_of_injOn (fun f => f.2.val) ?_ ?_
        · intro f hf
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and,
            Set.mem_setOf_eq, Finset.mem_Ico] at hf ⊢
          obtain ⟨⟨hpsi, hk⟩, -⟩ := hf
          have hlt := f.2.isLt
          have hm : Dw.mult f.1 = Dw.p := if_pos hpsi
          have hk' : k ≤ f.2.val + 1 + 1 := hk
          omega
        · intro f hf g hg hfg
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and,
            Set.mem_setOf_eq] at hf hg
          obtain ⟨τ1, j1⟩ := f
          obtain ⟨τ2, j2⟩ := g
          obtain ⟨-, h1'⟩ := hf
          obtain ⟨-, h2'⟩ := hg
          simp only at h1' h2' hfg
          subst h1' h2'
          exact Sigma.ext rfl (heq_of_eq (Fin.ext hfg))
    _ ≤ m + 1 := by rw [Nat.card_Ico]; omega

theorem boundFine_le {p N q i c m M : ℕ} (hp : 2 ≤ p) (hq : q ≤ m) (hi : N ≤ m + i) (hiN : i ≤ N) (hc : 1 ≤ c)
    (hcM : c ≤ M) :
    boundFine p N q i c ≤ (c : ℝ) * (m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1)) + (N : ℝ) ^ 2 * (Real.logb p M + 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq' : (q : ℝ) ≤ m := by exact_mod_cast hq
  have hi' : (N : ℝ) ≤ m + i := by exact_mod_cast hi
  have hiN' : (i : ℝ) ≤ N := by exact_mod_cast hiN
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcM' : (c : ℝ) ≤ M := by exact_mod_cast hcM
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.logb p c := Real.logb_nonneg (by linarith) hc'
  have hl : Real.logb p c ≤ Real.logb p M := Real.logb_le_logb_of_le (by linarith) (by linarith) hcM'
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hcm : (0 : ℝ) ≤ c * m := by positivity
  have t1 : (c : ℝ) * ((N : ℝ) - 2 * q - i) * p / ((p : ℝ) ^ 2 - 1) ≤ c * m / ((p : ℝ) - 1) := by
    calc _ ≤ (c : ℝ) * m * p / ((p : ℝ) ^ 2 - 1) := by
          gcongr
          linarith
      _ ≤ _ := by
          rw [div_le_div_iff₀ hp2 hp1]
          nlinarith [mul_nonneg hcm hp1.le]
  have t2 : (c : ℝ) * q * (3 + 1 / 2 * Real.logb p c) / ((p : ℝ) - 1) ≤
      c * m * (3 + 1 / 2 * Real.logb p M) / ((p : ℝ) - 1) := by
    gcongr
  have t3 : (i : ℝ) ^ 2 * (Real.logb p c + 1) ≤ (N : ℝ) ^ 2 * (Real.logb p M + 1) := by
    gcongr
  have e : (c : ℝ) * (m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1)) =
      c * m / ((p : ℝ) - 1) + c * m * (3 + 1 / 2 * Real.logb p M) / ((p : ℝ) - 1) := by ring
  unfold boundFine
  linarith


open Classical in
theorem sum_bound_le {Dw : Datum H} {F k m M : ℕ} {Mb Sm : ℝ} {cx : Lt1 Dw → ℕ} {p : ℕ}
    (hS : Shape Dw F k m) (hB : ExpBd Dw k cx Mb Sm M) (hp : 2 ≤ p) (hM : 1 ≤ M) :
    ∑ f, (if _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ 1 ≤ cx f then boundFine p (Dw.p + Dw.q) Dw.q (rk f) (cx f) else boundAll p (rk f) (cx f))
      ≤ eSmall F (Dw.p + Dw.q) m Mb Sm M p := by
  have hfib := card_big_fiber_le hS
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  obtain ⟨hMb, hτ, hSm, hcM⟩ := hB
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hL : 0 ≤ Real.logb p M := Real.logb_nonneg (by linarith) (by exact_mod_cast hM)
  have hF : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤ F := by
    have := two_mul_card_psi_le (H := H)
    omega
  have hF' : ((Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card : ℝ) ≤ F := by exact_mod_cast hF
  set X : ℝ := m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1) with hX
  set Y : ℝ := ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (Real.logb p M + 1) with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hmaps : ∀ f ∈ Finset.univ.filter (fun f : Lt1 Dw => _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f),
      f.1 ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ) := fun f hf =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2.1⟩
  have hbig : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f), ((cx f : ℝ) * X + Y) ≤
      F * (Mb * X + (m + 1) * Y) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ ≤ ∑ _τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ), (Mb * X + (m + 1) * Y) := by
          refine Finset.sum_le_sum fun τ _ => ?_
          rw [Finset.filter_filter, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
          have a1 := hτ τ
          have a2 : ((Finset.univ.filter (fun f : Lt1 Dw => _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ f.1 = τ)).card : ℝ) ≤ m + 1 := by
            exact_mod_cast hfib τ
          rw [Nat.cast_sum] at a1
          refine add_le_add (mul_le_mul_of_nonneg_right ?_ hX0) (mul_le_mul_of_nonneg_right ?_ hY0)
          · convert a1
          · convert a2
      _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hF' (by positivity)
  have hsm : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f), boundAll p (rk f) (cx f) ≤
      Sm / ((p : ℝ) - 1) := by
    refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right hSm hp1.le)
    unfold sumSmallSpread boundAll
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr ?_ fun f _ => by rw [Nat.cast_mul]
    ext f
    simp only [Finset.mem_filter, not_isBig_iff]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun f : Lt1 Dw => _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f)]
  have e : eSmall F (Dw.p + Dw.q) m Mb Sm M p = F * (Mb * X + (m + 1) * Y) + Sm / ((p : ℝ) - 1) := by
    rw [hX, hY]
    unfold eSmall
    ring
  rw [e]
  refine add_le_add (le_trans (Finset.sum_le_sum fun f hf => ?_) hbig) (le_trans (le_of_eq ?_) hsm)
  · have hb : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f := (Finset.mem_filter.1 hf).2
    have hm : Dw.mult f.1 = Dw.p := if_pos hb.1
    have hr := rk_le f
    have hk := hb.2
    split_ifs with h
    · exact boundFine_le hp h2 (by omega) (by omega) h.2 (hcM f)
    · have h0 : cx f = 0 := by
        by_contra hne
        exact h ⟨hb, by omega⟩
      simp [boundAll, h0, hY0]
  · exact Finset.sum_congr rfl fun f hf => if_neg fun h => (Finset.mem_filter.1 hf).2 h.1

end GlobalTheory.RefSum.OscInert

namespace GlobalTheory.RefSum

theorem oscLe_eSmall_of_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → InertInK H p → 1 ≤ M → OscLe Xo c p cx (eSmall F (Dw.p + Dw.q) m Mb Sm M p + 1) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hB p hp hp2 hpd hin hM la
  classical
  have key : ∀ f : Lt1 Dw, ∃ A B : ℝ, FacBetween Xo la f (cx f) A B ∧ B - A ≤
      (if _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ 1 ≤ cx f then boundFine p (Dw.p + Dw.q) Dw.q (rk f) (cx f) else boundAll p (rk f) (cx f)) := by
    intro f
    split_ifs with h
    · exact GlobalTheory.T.factor_depth_bounded_odd_inert_prime_cmType E H Dw l Xo c p la hp2 hpd hin f (cx f) h.1.1 h.2
    · exact ⟨0, _, (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1, (sub_zero _).le⟩
  choose A B hAB hle using key
  obtain ⟨-, n, hn⟩ := (GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 A B hAB
  have h1 := OscInert.sum_bound_le hS hB hp.out.two_le hM
  have h2 := (Finset.sum_le_sum fun f (_ : f ∈ Finset.univ) => hle f).trans (by convert h1)
  exact ⟨n, fun T io e ho y => ⟨(hn T io e ho y).1, fun ha => ((hn T io e ho y).2 ha).trans
    (EReal.coe_le_coe_iff.2 (by linarith))⟩⟩

end GlobalTheory.RefSum

end
end

section


open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.LatAllFG

theorem fg_latOf_congr {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
    [IsScalarTower (𝓞 K) K R] {C C' : Submodule K R} (hC : C = C')
    (Vs : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → Set (R → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (h : (latOf C Vs hV).FG) : (latOf C' Vs hV).FG := by
  subst hC; exact h

theorem latW_fg {D : D7} (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (hn : 0 < w.n) :
    (latW (T.U j) (wtZ (wtA w) w.n)).FG := by
  have h := (GlobalTheory.SupFull.fullAt_of_pins D T.toCore hT.pins j hj (hT.unf j hj _ T.good_σ₀) w hn).1
  unfold GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation.supLat GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation.latIn at h
  have h2 := Submodule.fg_of_fg_map_injective _ Subtype.val_injective h
  exact fg_latOf_congr (cuspW_wtZ (Xo := T.Q.Xo j) (c := T.Q.c) (U := T.U j) (wtA w) w.n).symm _ _ h2

theorem fg_span_image {K L V W : Type} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module L W] [Module (𝓞 L) W] [IsScalarTower (𝓞 L) L W]
    (ι : V →ₛₗ[algebraMap K L] W) (M : Submodule (𝓞 K) V) (hM : M.FG) :
    (Submodule.span (𝓞 L) (ι '' (M : Set V))).FG := by
  classical
  obtain ⟨s, hs⟩ := hM
  refine ⟨s.image ι, le_antisymm ?_ ?_⟩
  · rw [Finset.coe_image]
    exact Submodule.span_mono (Set.image_mono (hs ▸ Submodule.subset_span))
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      have e : ι (c • y) = (RingOfIntegers.mapRingHom (algebraMap K L) c) • ι y := by
        rw [← algebraMap_smul K c y, ι.map_smulₛₗ, ← algebraMap_smul L (RingOfIntegers.mapRingHom (algebraMap K L) c) (ι y)]
        rfl
      rw [e]
      exact Submodule.smul_mem _ _ hy

end GlobalTheory.CovTop.LatAllFG

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_definiteBottomTriple_transferred_frames : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ),
    IsStdChar D W.ψ (-1) → ∀ μ₀ : T, L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
    (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    ∃ Y₁ : Tri T A A' WW, IsBottomTri W i j Y₁ ∧ Y₁.rA = X.rA ∧ Y₁.rA' = X.rA' ∧ Y₁.rW = X.rW ∧
      ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → ∃ u : T → D.what₂.LLˣ, Y₁.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  first | exact @GlobalTheory.BotFrames.frames_transfer | exact GlobalTheory.BotFrames.frames_transfer | (intros; apply GlobalTheory.BotFrames.frames_transfer <;> assumption)
end
