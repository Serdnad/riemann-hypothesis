module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2418
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle861
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterPrecisionLeLengthAndRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentSumEqZeroOfOrbitalIntegralEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle872
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem uAt_chi_eq_one : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (k : (uAt r v i).Comp) (la : Wt ((uAt r v i).X k).Ψ D.R.r), ∀ γ ∈ ((uAt r v i).X k).Γ, ((uAt r v i).X k).χ la γ = 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v k la γ hγ
  exact GlobalTheory.OneEmbeddingProbe.chi_eq_one (uAt r v i)
    (fun a n hd k γ hγ => (h.laws v).p.chiTriv ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ _
      (r.used v).full.toCore.good_σ₀ a n hd k γ hγ) k la γ hγ

end GlobalTheory.ShareOn

end
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

theorem natCast_mem_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h2 : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
  rw [← l.prod] at h2
  exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable {E : Type} [Field E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}

theorem lact_mul_lact (a b : GL (Fin r) E) (x : Frame Ψ r) : lact (a * b) x = lact a (lact b x) := by
  funext τ
  simp only [lact, Units.val_mul, Matrix.map_mul]
  exact Matrix.mul_assoc _ _ _

theorem lact_rmul_comm (a : GL (Fin r) E) (x b : Frame Ψ r) : lact a (rmul x b) = rmul (lact a x) b := by
  funext τ
  show (a : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) =
    ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) * mat b τ
  rw [Matrix.mul_assoc]

theorem lact_one_frame (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  simp only [lact, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

end Cong



theorem sub_mem_half_smul_latP : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (k : (uAt r v i).Comp), ∀ γ ∈ ((uAt r v i).X k).Γ, ∀ w ∈ lattice₂ D ((uAt r v i).X k).Λ, Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w ∈ p.T.Q.l.Mb • lattice₂ D ((uAt r v i).X k).Λ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v k γ hγ w hw
  have hL := (h.laws v).p.toLawsCore
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ := (r.used v).full.toCore.good_σ₀
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D _ hL.pins
  have hU := (Formalism.L2.PjFree.isUnf_ofPj _).2 (hL.unf _ hj _ hσ)
  obtain ⟨th, hrk, hth, hD⟩ := hL.dictU _ hj _ hσ
  obtain ⟨⟨x0, hx0, -⟩, -⟩ := hD.2.2
  obtain ⟨η, hηU, hηc, b, hb, hx⟩ := GlobalTheory.T.exists_principal_congruence_back_triangular_frame _ _ _ _ _ _ _ _ _ hσ hU hA (hnum _ hj).2.1 k γ hγ (x0 k) (hx0 k).1
  have hηΓ : η ∈ ((uAt r v i).X k).Γ :=
    GlobalTheory.PrincCore.hasPrinc_core D _ hL _ hj _ hσ k η hηU hηc
  have hmem : (η * γ)⁻¹ ∈ ((uAt r v i).X k).Γ := inv_mem (mul_mem hηΓ hγ)
  have hfix : lact (η * γ)⁻¹ (x0 k) = rmul (x0 k) b := by
    calc lact (η * γ)⁻¹ (x0 k) = lact (η * γ)⁻¹ (rmul (lact η (lact γ (x0 k))) b) := congrArg _ hx
      _ = rmul (lact (η * γ)⁻¹ (lact η (lact γ (x0 k)))) b := lact_rmul_comm _ _ _
      _ = rmul (lact ((η * γ)⁻¹ * (η * γ)) (x0 k)) b := by
        rw [lact_mul_lact ((η * γ)⁻¹) (η * γ), lact_mul_lact η γ]
      _ = rmul (x0 k) b := by rw [inv_mul_cancel, lact_one_frame]
  have h1 := ((uAt r v i).X k).Γ_free _ hmem (x0 k) (hx0 k).1 b hb hfix
  have hγη : γ = η⁻¹ := by
    rw [inv_eq_one] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hγU := ((uAt r v i).X k).Γ_stab γ hγ

  have hcong : ∀ u ∈ ((uAt r v i).X k).Λ, ∃ y ∈ ((uAt r v i).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) u - u = ((r.used v).full.Q.l.M : D.host.E) • y := by
    intro u hu
    obtain ⟨y, hy, he⟩ := hηc (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) u) ((hγU.2 u).1 hu)
    have hηγ : Matrix.mulVec (η : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)
        (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) u) = u := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, hγη, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨-y, ((uAt r v i).X k).Λ.neg_mem hy, ?_⟩
    rw [hηγ] at he
    rw [smul_neg, ← he]
    abel

  have hM0 : ((r.used v).full.Q.l.M : D.host.E) ≠ 0 := by
    have := (r.used v).full.Q.l.three_le
    exact_mod_cast (show (r.used v).full.Q.l.M ≠ 0 by omega)
  obtain ⟨z, hz⟩ : ∃ z : Fin D.R.r → D.host.E, z = ((r.used v).full.Q.l.M : D.host.E)⁻¹ •
      (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w) := ⟨_, rfl⟩
  have hzP : z ∈ lattice₂ D ((uAt r v i).X k).Λ := by
    refine mem_latP.2 fun a ha => ?_
    obtain ⟨y, hy, he⟩ := hcong (a • w) (mem_latP.1 hw a ha)
    have : a • z = y := by
      rw [hz, smul_comm, smul_sub, ← Matrix.mulVec_smul, he, smul_smul, inv_mul_cancel₀ hM0, one_smul]
    rw [this]
    exact hy
  have hMmem : ((r.used v).full.Q.l.M : 𝓞 D.host.E) ∈ (r.used v).full.Q.l.Mb := natCast_mem_half _
  have hfin : Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w =
      ((r.used v).full.Q.l.M : 𝓞 D.host.E) • z := by
    rw [hz, ← algebraMap_smul D.host.E, smul_smul, map_natCast, mul_inv_cancel₀ hM0, one_smul]
  rw [hfin]
  exact Submodule.smul_mem_smul hMmem hzP

end GlobalTheory.ShareOn
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HighWtEmb

theorem exists_prodProj (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ) (z₀ : Gm)
    (hz : ∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z₀ = z₀) (s : Finset ι) :
    ∃ e : alg O N lam, e • z₀ = z₀ ∧ ∀ x : ∀ τ, dualWeyl O N N (res N (lam τ)),
      (e : Module.End O (NablaT O N lam)) (PiTensorProduct.tprod O x) =
        PiTensorProduct.tprod O (fun σ => if σ ∈ s then rowProj O N (res N (lam σ)) (w σ) (x σ) else x σ) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_smul _ _, fun x => by simp⟩
  | insert τ s hτ ih =>
    obtain ⟨e, he, hex⟩ := ih
    obtain ⟨p, hp, -⟩ := exists_unique_isProj O N ι lam τ (w τ)
    let pA : alg O N lam := ⟨p, Algebra.subset_adjoin (Or.inr ⟨τ, w τ, hp⟩)⟩
    refine ⟨pA * e, by rw [mul_smul, he]; exact hz τ pA hp, fun x => ?_⟩
    show p ((e : Module.End O (NablaT O N lam)) _) = _
    rw [hex]
    rw [hp _ (rowProj O N (res N (lam τ)) (w τ) (x τ)) (by simp [hτ, rowProj])]
    congr 1
    funext σ
    by_cases h : σ = τ
    · subst h; simp
    · simp [Function.update_of_ne h, h]

theorem prodProj_mul_eq_zero (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (w : ι → Fin N → ℕ) (e : Module.End O (NablaT O N lam))
    (he : ∀ x : ∀ τ, dualWeyl O N N (res N (lam τ)),
      e (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (fun σ => rowProj O N (res N (lam σ)) (w σ) (x σ)))
    (τ : ι) (v : Fin N → ℕ) (a : Module.End O (NablaT O N lam)) (ha : IsProj O N lam τ v a) (hv : v ≠ w τ) : e * a = 0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply, LinearMap.zero_apply]
  rw [ha x (rowProj O N (res N (lam τ)) v (x τ)) (by simp [rowProj]), he]
  refine (PiTensorProduct.tprod O).map_coord_zero τ ?_
  simp only [Function.update_self]
  apply Subtype.ext
  simp only [rowProj, LinearMap.restrict_apply, ZeroMemClass.coe_zero]
  rw [weightedHomogeneousComponent_of_mem (weightedHomogeneousComponent_isWeightedHomogeneous _ _), if_neg hv.symm]


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_weightForm : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], SubQ O N lam ϖ Gm → ∀ (w : ι → Fin N → ℕ) (z₀ : Gm), z₀ ≠ 0 → (∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z₀ = z₀) → ∃ φ : Gm →+ O ⧸ Ideal.span {ϖ}, φ z₀ ≠ 0 ∧ (∀ (c : O) (z : Gm), φ (algebraMap O (alg O N lam) c • z) = Ideal.Quotient.mk (Ideal.span {ϖ}) c * φ z) ∧ ∀ τ (v : Fin N → ℕ) (a : alg O N lam), IsProj O N lam τ v a → v ≠ w τ → ∀ z, φ (a • z) = 0 := by
  intro O _ _ _ N ι _ _ lam ϖ hϖ Gm _ _ hSQ w z₀ hz0 hfix

  have hkill : ∀ z : Gm, algebraMap O (alg O N lam) ϖ • z = 0 := by
    obtain ⟨U, π, hπ, h0⟩ := hSQ
    intro z
    obtain ⟨x, rfl⟩ := hπ z
    rw [← map_smul]
    exact h0 _ x rfl
  letI iO : Module O Gm := Module.compHom Gm (algebraMap O (alg O N lam))
  have hT : Module.IsTorsionBySet O Gm (Ideal.span {ϖ} : Ideal O) :=
    (Module.isTorsionBySet_span_singleton_iff ϖ).2 fun z => hkill z
  haveI hmax : (Ideal.span {ϖ} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI kF : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  letI iK : Module (O ⧸ Ideal.span {ϖ}) Gm := hT.module
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (O ⧸ Ideal.span {ϖ}) hz0
  obtain ⟨e, he, hex⟩ := exists_prodProj O N ι lam Gm w z₀ hfix Finset.univ
  let φ : Gm →+ O ⧸ Ideal.span {ϖ} :=
    { toFun := fun z => f (e • z)
      map_zero' := by simp
      map_add' := fun y z => by simp [smul_add] }
  refine ⟨φ, ?_, fun c z => ?_, fun τ v a ha hv z => ?_⟩
  · show f (e • z₀) ≠ 0
    rw [he]; exact hf
  · show f (e • (algebraMap O (alg O N lam) c • z)) = _ * f (e • z)
    rw [← mul_smul, ← Algebra.commutes, mul_smul]
    have : algebraMap O (alg O N lam) c • (e • z) = (Ideal.Quotient.mk (Ideal.span {ϖ}) c) • (e • z) := rfl
    rw [this, map_smul, smul_eq_mul]
  · show f (e • (a • z)) = 0
    have h0 : e * a = 0 := by
      apply Subtype.ext
      exact prodProj_mul_eq_zero O N ι lam w (e : Module.End O (NablaT O N lam))
        (fun x => by rw [hex]; simp) τ v a ha hv
    rw [← mul_smul, h0, zero_smul, map_zero]

end GlobalTheory.HighWtEmb
end
end

section



noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.WtShape

section Rec

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P)

theorem six_le_r (R : Ranks) : 6 ≤ R.r := by
  have := R.two_le_m; have := R.m_add_three_le_k; unfold Ranks.r; omega

theorem one_le_Dp : 1 ≤ T.Dp := by
  rw [T.Dp_eq]
  have h2 : 0 < D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord from D.R.ord_pos); omega
  exact Nat.mul_pos h2 (Nat.choose_pos (by have := six_le_r D.R; omega))

theorem forty_le_PP : 40 ≤ T.PP := le_trans (by exact_mod_cast T.nW_40) T.nW_le

theorem len_ge : 4 * T.Dp + 4 ≤ ⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ := by
  have h1 : (1 : ℝ) ≤ T.Dp := by exact_mod_cast one_le_Dp T
  have h2 := forty_le_PP T
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 0 < D.R.m)
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : D.R.m ≤ D.R.k)
  have h3 : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
    rw [le_div_iff₀ hm]; exact mul_le_mul_of_nonneg_left hmk (by positivity)
  have h4 : (8 : ℝ) * (T.Dp : ℝ) ^ 2 ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have h5 : ((4 * T.Dp + 4 : ℕ) : ℝ) ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
    push_cast; nlinarith
  exact_mod_cast h5.trans (Nat.le_ceil _)

theorem cZeroN_le_TO (j : ℕ) : cZeroN D j ≤ 12 * T.TO := by
  have h1 := cZeroN_le D j
  have h2 := T.TO_11D2
  have h6 := six_le_r D.R
  have h3 : D.R.r ^ 4 ≤ 6 * (D.R.r.choose 2) ^ 2 := by
    obtain ⟨s, hs⟩ : ∃ s, D.R.r = s + 1 := ⟨D.R.r - 1, by omega⟩
    have e : 2 * (D.R.r.choose 2) = D.R.r * s := by
      rw [hs, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_div_cancel' (by
        rw [mul_comm]; exact (Nat.even_mul_succ_self s).two_dvd)]
    have e2 : 4 * (D.R.r.choose 2) ^ 2 = D.R.r ^ 2 * s ^ 2 := by
      rw [← mul_pow, ← e]; ring
    have e3 : 4 * D.R.r ^ 2 ≤ 6 * s ^ 2 := by
      have : 5 ≤ s := by omega
      rw [hs]; nlinarith
    have e4 : D.R.r ^ 2 * (4 * D.R.r ^ 2) ≤ D.R.r ^ 2 * (6 * s ^ 2) := Nat.mul_le_mul_left _ e3
    nlinarith
  have h4 : D.R.f ^ 2 * D.R.r ^ 4 ≤ D.R.f ^ 2 * (6 * (D.R.r.choose 2) ^ 2) := Nat.mul_le_mul_left _ h3
  rw [T.Dp_eq, mul_pow] at h2
  nlinarith

theorem spacing_ge (j n : ℕ) (hn : n ≤ T.TO) :
    4 * ((cZeroN D j : ℝ) + 2 * D.R.r + n + T.Dp + 1) ≤ LevelStarExponents.h0 L ∧ 24 * (D.R.r : ℝ) * n ≤ LevelStarExponents.h0 L ∧
      4 * (n : ℝ) ^ 2 ≤ LevelStarExponents.h0 L := by
  have a1 : (cZeroN D j : ℝ) ≤ 12 * T.TO := by exact_mod_cast cZeroN_le_TO T j
  have a2 : 6 * (D.R.r : ℝ) ≤ T.TO := by
    have h := T.order_ge_rank_bound
    have : 6 * D.R.r ≤ T.TO := by nlinarith [Nat.zero_le (D.R.r * T.Dp)]
    exact_mod_cast this
  have a3 : 40 * ((T.Dp : ℝ) + 2) ≤ T.TO := by exact_mod_cast T.TO_40
  have a4 : (n : ℝ) ≤ T.TO := by exact_mod_cast hn
  have a5 := T.heightBound_ge_order_sq
  have b0 : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _
  have b1 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have b2 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have b3 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨by nlinarith, ?_, by nlinarith⟩
  have : 6 * (D.R.r : ℝ) * n ≤ T.TO * T.TO := mul_le_mul a2 a4 b2 (by linarith)
  nlinarith

theorem prod_bounds (n : ℕ) (hn : n ≤ T.TO) :
    T.PP * n * D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * T.Dp ≤ LevelStarExponents.h0 L ∧
    T.PP ^ 2 * D.R.r * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 ≤ L.sc.b ∧
    T.PP * n * (T.Dp : ℝ) ^ 2 * L.sc.L ≤ L.sc.b := by
  have a4 : (n : ℝ) ≤ T.TO := by exact_mod_cast hn
  have hP := forty_le_PP T
  have hP0 : 0 ≤ T.PP := by linarith
  have hrN : (D.R.r : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have : D.R.r ≤ D.R.N D.R.m := by
      unfold Ranks.r Ranks.N
      have h1 : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      omega
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ T.heightBound_ge_order_product
    have e1 : T.PP * n * (D.R.r : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) ≤
        T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) := by
      gcongr
    have e2 : T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) ≤
        T.ChT * (T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k *
          (T.Dp : ℝ)) := le_mul_of_one_le_left (by positivity) T.ChT_ge
    calc _ ≤ _ := e1.trans e2
      _ = _ := by ring
  · refine le_trans ?_ T.b_ge
    have e2 : T.PP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 ≤
        T.CbN * (T.PP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3) :=
      le_mul_of_one_le_left (by positivity) T.CbN_ge
    calc _ ≤ _ := e2
      _ = _ := by ring
  · have hb0 : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
    have hlb : Real.log L.sc.b = L.sc.L := by unfold Scale.b; exact Real.log_exp _
    have hL : 0 ≤ L.sc.L := by unfold Scale.L; exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
    have c1 := T.TD2'
    have c2 := T.TO_PP'
    rw [hlb] at c1
    have c3 : (1 : ℝ) ≤ T.TO := by
      have := T.TO_40
      exact_mod_cast (by omega : 1 ≤ T.TO)
    have c4 : T.PP ≤ L.sc.b ^ (1 / 2 : ℝ) := le_trans (le_mul_of_one_le_left hP0 c3) c2
    have c5 : (n : ℝ) * (T.Dp : ℝ) ^ 2 * L.sc.L ≤ L.sc.b ^ (1 / 2 : ℝ) := le_trans (by gcongr) c1
    have c6 : L.sc.b ^ (1 / 2 : ℝ) * L.sc.b ^ (1 / 2 : ℝ) = L.sc.b := by
      rw [← Real.rpow_add hb0]; norm_num
    calc _ = T.PP * ((n : ℝ) * (T.Dp : ℝ) ^ 2 * L.sc.L) := by ring
      _ ≤ _ := mul_le_mul c4 c5 (by positivity) (by positivity)
      _ = _ := c6

theorem abs_logOm_le (hS : SizesAt L) (hL : 3 ≤ L.sc.L) : |L.logOm| ≤ 3 * L.sc.L := by
  obtain ⟨-, -, -, -, -, hCond, hQD, -⟩ := hS
  have hx0 : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have h1 := log_rdE_le_L D L hCond hQD
  have hrd : 1 ≤ D.host.rdE := hQD.2.2.2.2.2.2.1
  have h0 := Real.log_nonneg hrd
  have h2 : |L.logDerivativeAtOne| ≤ L.sc.L := hQD.2.2.2.2.2.1
  have h3 := Real.one_half_lt_eulerMascheroniConstant
  have h4 := Real.eulerMascheroniConstant_lt_two_thirds
  have h5 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h6 : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos; linarith [Real.pi_le_four]
  have h7 := Real.log_two_lt_d9
  have h8 := Real.log_two_gt_d9
  unfold SizeData₂.logOm Host.v
  rw [Real.log_div Real.pi_pos.ne' (by positivity), Real.log_div (by positivity) (by norm_num)]
  obtain ⟨h9, h10⟩ := abs_le.1 h2
  rw [abs_le]
  constructor <;> linarith

def entR (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) : ℝ :=
  sgR D t n + DV.wSz D ((i : ℕ) + 1) t + n - ((D.R.k : ℝ) + i) + ((D.R.r : ℝ) + 1) / 2 -
    if n < D.R.k + i then 0 else (D.R.r : ℝ)

theorem ent_cast (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) : ((ent D i t n : ℚ) : ℝ) = entR D i t n := by
  unfold ent entR sgR
  rw [← DV.eQ_cast, eQ_succ]
  split_ifs <;> push_cast <;> ring

theorem entR_cloud (L : SizeData₂ D) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) (hn : n < D.R.k - 1) :
    DV.wSz D ((i : ℕ) + 1) t - D.R.r ≤ entR D i t n ∧ entR D i t n ≤ DV.wSz D ((i : ℕ) + 1) t + L.Sc + D.R.r := by
  unfold entR
  rw [if_pos (by omega), sgR_cloud D t n hn]
  obtain ⟨v0, v1⟩ := L.cloud_v t ⟨n, hn⟩
  have c1 : (n : ℝ) + 2 ≤ D.R.k := by exact_mod_cast (by omega : n + 2 ≤ D.R.k)
  have c3 : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast i.2
  have c4 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have c5 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have c6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast six_le_r D.R
  have := r_cast D.R
  constructor <;> linarith

theorem entR_node (L : SizeData₂ D) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) (hn : D.R.k - 1 ≤ n) (hr : n < D.R.r) :
    |entR D i t n| ≤ L.etaSz + D.R.r := by
  obtain ⟨a1, a2⟩ := abs_le.1 (sgR_be D L ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 t n hn hr)
  have c1 : (D.R.k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (by omega : D.R.k ≤ n + 1)
  have c2 : (n : ℝ) + 1 ≤ D.R.r := by exact_mod_cast hr
  have c3 : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast i.2
  have c5 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have c7 : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  have := r_cast D.R
  unfold entR
  split_ifs with h
  · have c8 : (n : ℝ) + 1 ≤ (D.R.k : ℝ) + (i : ℕ) := by exact_mod_cast h
    rw [abs_le]; constructor <;> linarith
  · have c8 : (D.R.k : ℝ) + (i : ℕ) ≤ n := by exact_mod_cast not_lt.1 h
    rw [abs_le]; constructor <;> linarith

theorem entR_step (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) :
    entR D i t n - entR D i t (n + 1) =
      sgR D t n - sgR D t (n + 1) - 1 + if n + 1 = D.R.k + i then (D.R.r : ℝ) else 0 := by
  unfold entR
  split_ifs <;> first | omega | (push_cast; ring)

theorem entR_cloud_sub (L : SizeData₂ D) (i : Fin D.R.m) (t : D.what₂.Tau)
    (hs : ∀ a, a + 1 < D.R.r → 1 ≤ sgR D t a - sgR D t (a + 1)) (n : ℕ) (hn : n < D.R.k - 1) :
    0 ≤ entR D i t n - entR D i t (D.R.k - 1 - 1) ∧ entR D i t n - entR D i t (D.R.k - 1 - 1) ≤ L.Sc := by
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h1 := steps_sum (sgR D t) 0 D.R.r 1 (fun a _ ha => hs a ha) n (Nat.zero_le _) (D.R.k - 1 - 1) (by omega) (by omega)
  have h2 : (n : ℝ) ≤ ((D.R.k - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ D.R.k - 1 - 1)
  have h3 := (L.cloud_v t ⟨n, hn⟩).2
  have h4 := (L.cloud_v t ⟨D.R.k - 1 - 1, by omega⟩).1
  rw [← sgR_cloud] at h3 h4
  unfold entR
  rw [if_pos (by omega), if_pos (by omega)]
  constructor <;> linarith

end Rec

end GlobalTheory.CovTop.WtShape

end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.centSum_eq_zero_of_orbitalIntegral_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
    ∀ (B : GlobalTheory.LKDef.DForm G) (y : GlobalTheory.LKCx.grp G B.β),
      orbK (MonoidHom.id _) (L.K.toSubgroup.prod K') (B.emb y) (fun h => f h.1 * f' h.2) = 0 →
      centSum (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec)
        (GlobalTheory.LKCx.toP1 G B.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' y = 0 := by
  first | (exact @GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK) | (exact GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK) | (intros; apply GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK <;> assumption)
end
