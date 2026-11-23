module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfLine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle452
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement
import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle431
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle448
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle401
import Formalism.LocalToGlobal.Columns.Bundle024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle013
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle451
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceTransvectionActsPositivelyInvariantFor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped InnerProductSpace ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.CoefIso

theorem bcVV_rhoVr {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
    (σ : K →+* ℂ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (g : GL (Fin n) E) (v : VV K lam) :
    GlobalTheory.CoefSpace.bcVV σ lam (rhoVr emb lam g v) =
      rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) (GlobalTheory.CoefSpace.bcVV σ lam v) := by
  apply Subtype.ext
  show MvPolynomial.map σ (actP lam (invTrK (embGL emb g)) v.1) =
    actP lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) (MvPolynomial.map σ v.1)
  rw [GlobalTheory.CoefSpace.map_actP]
  congr 2

theorem invTr_unitary_one {n : ℕ} (U : GL (Fin n) ℂ) (hU : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * U = 1) :
    ((inside₂ ℂ n U : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * (1 : Matrix (Fin n) (Fin n) ℂ) *
      ((inside₂ ℂ n U : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have hi : ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (U : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
    calc ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
        = ((U : Matrix (Fin n) (Fin n) ℂ)ᴴ * U) * ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
          rw [hU, Matrix.one_mul]
      _ = (U : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  show (((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ)ᴴ * 1 * ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ = 1
  have e : (((U : Matrix (Fin n) (Fin n) ℂ)ᴴ)ᵀ)ᴴ = (U : Matrix (Fin n) (Fin n) ℂ)ᵀ := by
    ext i j
    simp
  rw [hi, Matrix.mul_one, e, ← Matrix.transpose_mul, hU, Matrix.transpose_one]

theorem ratMat_unitary {D : D7} (V : HSp D) (hg : V.gram = 1) (γ : GQ V) (γE : GL (Fin V.rank) D.host.E)
    (h : Bridge.IsRatMat V γ γE) (φ : D.host.E →+* ℂ) :
    ((Formalism.UG.bc φ γE : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ *
      ((Formalism.UG.bc φ γE : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 1 := by
  obtain ⟨γ, ⟨g, hgU, hgm⟩⟩ := γ
  have e1 : Formalism.UG.bc (incA D) g = Formalism.UG.bc (incA D) γE := hgm.trans h
  have e2 : g = γE := Units.ext (Matrix.ext fun i j =>
    (Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F))
      (congrArg (fun u => (Units.val u) i j) e1))
  subst e2
  have hu : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram := hgU
  rw [hg, Matrix.mul_one] at hu
  have hc : ((g : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map φ)ᴴ =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).map φ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
    exact (D.sp.cm.cmUnram.2.1 φ _).symm
  rw [bc_coe, hc, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]



theorem coef_iso : ∀ (D : D7) (V : HSp D) (n : ℕ), V.rank = n → V.gram = 1 → ∀ (c : CoefA V), c.Is → ∀ {K ι : Type} [Field K] [NumberField K] [Fintype ι] (σ : K →+* ℂ) (emb : ι → (D.host.E →+* K)) (lam : ι → DomWeight n) (c0 : VV K lam →ₛₗ[σ] c.W), Nonempty (VVIdx lam) →
  (∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (g : GL (Fin n) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g → ∀ v, c0 (rhoVr emb lam g v) = c.coef.ρ γ (c0 v)) →
  (LinearIndependent ℂ fun i => c0 (bVV K lam i)) →
  ∃ (e : VV ℂ lam ≃ₗ[ℂ] c.W) (s : ℝ), 0 < s ∧ (∀ v, c0 v = (s : ℂ) • e (GlobalTheory.CoefSpace.bcVV σ lam v)) ∧
    (∀ x y, inner ℂ (e x) (e y) = pairK lam (fun _ => 1) x y) ∧
    ∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (g : GL (Fin n) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g →
      ∀ x, e (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) x) = c.coef.ρ γ (e x) := by
  intro D V n hn hg c hc K ι _ _ _ σ emb lam c0 hne hint hli
  subst hn
  classical
  have hMat : ∀ γ : GQ V, ∃ γE, Bridge.IsRatMat V γ γE ∧ MatEq γE γE := fun γ => by
    obtain ⟨γE, h⟩ := GlobalTheory.Mem.StdUnique.exists_ratMat γ
    exact ⟨γE, h, rfl, fun i j i' j' hi hj => by rw [Fin.ext hi, Fin.ext hj]⟩
  have hmem : ∀ v, c0 v ∈ Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range (bVV K lam)) := by rw [(bVV K lam).span_eq]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  obtain ⟨i₀⟩ := hne
  have htop : Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) = ⊤ := by
    refine (GlobalTheory.Mem.StdUnique.bot_or_top c hc _ fun γ hγ w hw => ?_).resolve_left fun h0 => ?_
    · obtain ⟨γE, h1, h2⟩ := hMat ⟨γ, hγ⟩
      have hle : (Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i))).map (c.ρ γ) ≤
          Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) := by
        rw [Submodule.map_span_le]
        rintro _ ⟨i, rfl⟩
        rw [show c.ρ γ (c0 (bVV K lam i)) = c.coef.ρ ⟨γ, hγ⟩ (c0 (bVV K lam i)) from rfl,
          ← hint ⟨γ, hγ⟩ γE γE h1 h2]
        exact hmem _
      exact hle ⟨w, hw, rfl⟩
    · have := hmem (bVV K lam i₀)
      rw [h0, Submodule.mem_bot] at this
      exact hli.ne_zero i₀ this
  let b1 : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) :=
    Module.Basis.mk (GlobalTheory.CoefSpace.bcVV_indep σ lam) (GlobalTheory.CoefSpace.bcVV_span σ lam).ge
  let b2 : Module.Basis (VVIdx lam) ℂ c.W := Module.Basis.mk hli htop.ge
  have hb1 : ∀ i, b1 i = GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i) := fun i => Module.Basis.mk_apply _ _ i
  have hb2 : ∀ i, b2 i = c0 (bVV K lam i) := fun i => Module.Basis.mk_apply _ _ i
  obtain ⟨e0, he0b⟩ : ∃ e0 : VV ℂ lam ≃ₗ[ℂ] c.W, ∀ i, e0 (b1 i) = b2 i :=
    ⟨b1.equiv b2 (Equiv.refl _), fun i => by simp⟩
  have he0 : ∀ v, e0 (GlobalTheory.CoefSpace.bcVV σ lam v) = c0 v := by
    intro v
    have : (e0.toLinearMap.comp (GlobalTheory.CoefSpace.bcVV σ lam) : VV K lam →ₛₗ[σ] c.W) = c0 :=
      (bVV K lam).ext fun i => by
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← hb1, he0b, hb2]
    exact LinearMap.congr_fun this v
  have hR : ∀ (γ : GQ V) (γE g : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g → ∀ x,
      e0 (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) x) = c.ρ γ (e0 x) := by
    intro γ γE g h1 h2 x
    have : e0.toLinearMap.comp (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g)) =
        (c.ρ γ).comp e0.toLinearMap := b1.ext fun i => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hb1, ← bcVV_rhoVr, LinearEquiv.coe_coe, he0, he0,
        hint γ γE g h1 h2]
      rfl
    exact LinearMap.congr_fun this x
  have hP : ∀ (γ : GQ V) (γE g : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g → ∀ x y : VV ℂ lam,
      pairK lam (fun _ => 1) (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) x)
        (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) y) = pairK lam (fun _ => 1) x y := by
    intro γ γE g h1 h2
    obtain rfl : γE = g := Units.ext (Matrix.ext fun i j => h2.2 i j i j rfl rfl)
    exact pairInv ℂ ι V.rank lam (fun _ => 1) _ fun τ =>
      invTr_unitary_one (Formalism.UG.bc (σ.comp (emb τ)) γE) (ratMat_unitary V hg γ γE h1 _)
  have hgr : GlobalTheory.CoefSpace.gramOf (fun _ : ι => (1 : GL (Fin V.rank) ℂ)) = fun _ => 1 := by
    funext τ
    simp [GlobalTheory.CoefSpace.gramOf]
  let S : c.W →ₗ[ℂ] GlobalTheory.CoefSpace.HV lam (fun _ => (1 : GL (Fin V.rank) ℂ)) := e0.symm.toLinearMap
  have hS : ∀ w, S w = e0.symm w := fun _ => rfl
  let T : Module.End ℂ c.W := (LinearMap.adjoint S).comp S
  have hT : ∀ w w', inner ℂ w (T w') = pairK lam (fun _ => 1) (e0.symm w) (e0.symm w') := by
    intro w w'
    show inner ℂ w (LinearMap.adjoint S (S w')) = _
    rw [LinearMap.adjoint_inner_right, GlobalTheory.CoefSpace.inner_HV, hgr]
    rfl
  have hBinv : ∀ (γ : GQ V) a b, pairK lam (fun _ => 1) (e0.symm (c.ρ γ a)) (e0.symm (c.ρ γ b)) =
      pairK lam (fun _ => 1) (e0.symm a) (e0.symm b) := by
    intro γ a b
    obtain ⟨γE, h1, h2⟩ := hMat γ
    have key : ∀ a, e0.symm (c.ρ γ a) = rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) γE) (e0.symm a) :=
      fun a => by rw [LinearEquiv.symm_apply_eq, hR γ γE γE h1 h2, LinearEquiv.apply_symm_apply]
    rw [key, key, hP γ γE γE h1 h2]
  have hcomm : ∀ (γ : GQ V) x, T (c.ρ γ x) = c.ρ γ (T x) := by
    intro γ x
    refine ext_inner_left ℂ fun w => ?_
    have hinv : c.ρ γ (c.ρ (γ⁻¹ : GQ V) w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, map_one,
        Module.End.one_apply]
    calc inner ℂ w (T (c.ρ γ x)) = inner ℂ (c.ρ γ (c.ρ (γ⁻¹ : GQ V) w)) (T (c.ρ γ x)) := by rw [hinv]
      _ = pairK lam (fun _ => 1) (e0.symm (c.ρ (γ⁻¹ : GQ V) w)) (e0.symm x) := by rw [hT, hBinv]
      _ = inner ℂ (c.ρ (γ⁻¹ : GQ V) w) (T x) := (hT _ _).symm
      _ = inner ℂ (c.ρ γ (c.ρ (γ⁻¹ : GQ V) w)) (c.ρ γ (T x)) := (hc.2.1 _ _ _).symm
      _ = inner ℂ w (c.ρ γ (T x)) := by rw [hinv]
  obtain ⟨μ, hμ⟩ := GlobalTheory.Mem.RowCoord.scalar_of_comm_rat c hc T hcomm
  have hx₀ : GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀) ≠ 0 := by
    rw [← hb1]
    exact b1.ne_zero i₀
  have hpos := GlobalTheory.CoefSpace.pairK_pos lam (fun _ => 1) _ hx₀
  rw [hgr] at hpos
  have h1 := hT (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))) (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀)))
  have hsq : inner ℂ (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))) (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))) =
      ((‖e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hμ, inner_smul_right, LinearEquiv.symm_apply_apply, hsq] at h1
  rw [← h1] at hpos
  have hn : 0 < ‖e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (e0.map_ne_zero_iff.2 hx₀)) 2
  obtain ⟨hre, him⟩ := Complex.lt_def.1 hpos
  simp only [Complex.re_mul_ofReal, Complex.im_mul_ofReal, Complex.zero_re, Complex.zero_im] at hre him
  have hm : 0 < μ.re := (pos_iff_pos_of_mul_pos hre).2 hn
  have hμr : ((μ.re : ℝ) : ℂ) = μ := Complex.ext rfl (by
    rw [Complex.ofReal_im]
    exact ((mul_eq_zero.1 him.symm).resolve_right hn.ne').symm)
  have hr : 0 < Real.sqrt μ.re := Real.sqrt_pos.2 hm
  have hr0 : ((Real.sqrt μ.re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  obtain ⟨e, he⟩ : ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, ∀ x, e x = ((Real.sqrt μ.re : ℝ) : ℂ) • e0 x :=
    ⟨e0.trans (LinearEquiv.smulOfNeZero ℂ c.W _ hr0), fun _ => rfl⟩
  refine ⟨e, (Real.sqrt μ.re)⁻¹, inv_pos.2 hr, fun v => ?_, fun x y => ?_, fun γ γE g h1 h2 x => ?_⟩
  · rw [he, he0, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
  · rw [he, he, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hm.le, hμr, ← inner_smul_right, ← hμ, hT, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
  · rw [he, he, hR γ γE g h1 h2]
    exact ((c.ρ γ).map_smul _ _).symm

end GlobalTheory.Mem.CoefIso
end
end

section

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar



section Trans

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

def LocIso.trans {A B C : Formalism.MainNotions.S.Loc.LocAt F E sig p} (a : Formalism.L2.S.LocIso A B) (b : Formalism.L2.S.LocIso B C) :
    Formalism.L2.S.LocIso A C where
  eF := a.eF.trans b.eF
  eF_ι x := (congrArg b.eF (a.eF_ι x)).trans (b.eF_ι x)
  eF_val x y := (a.eF_val x y).trans (b.eF_val _ _)
  eF_cont := b.eF_cont.comp a.eF_cont
  eF_symm_cont := a.eF_symm_cont.comp b.eF_symm_cont
  eF_ql x := (congrArg b.eF (a.eF_ql x)).trans (b.eF_ql x)
  eE := a.eE.trans b.eE
  eE_alg x := (congrArg b.eE (a.eE_alg x)).trans (b.eE_alg _)
  eE_ι x := (congrArg b.eE (a.eE_ι x)).trans (b.eE_ι x)
  eE_cont := b.eE_cont.comp a.eE_cont
  eE_symm_cont := a.eE_symm_cont.comp b.eE_symm_cont
  eE_cj y := (congrArg b.eE (a.eE_cj y)).trans (b.eE_cj _)
  eE_O y := (a.eE_O y).trans (b.eE_O _)
  eE_psi y := (a.eE_psi y).trans (b.eE_psi _)

variable {R : Ranks} {Word Tau : Type} {hc : Word → Tau → HCParam R}

def SIso.trans {s s' s'' : Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc} (a : SIso s s') (b : SIso s' s'') : SIso s s'' where
  cd := a.cd.trans b.cd
  del := a.del.trans b.del
  letter := a.letter.trans b.letter
  eHH := a.eHH.trans b.eHH
  eCu u := (a.eCu u).trans (b.eCu u)
  Pu_eq u x := (congrArg b.eHH (a.Pu_eq u x)).trans (b.Pu_eq u _)
  volN := a.volN.trans b.volN
  volH := a.volH.trans b.volH
  eT u u' := (a.eT u u').trans (b.eT u u')
  aTerm_eq u u' t x := (congrArg (b.eCu u) (a.aTerm_eq u u' t x)).trans (b.aTerm_eq u u' _ _)
  isId t := (a.isId t).trans (b.isId _)
  inS t := (a.inS t).trans (b.inS _)
  relevant t := (a.relevant t).trans (b.relevant _)
  FeqF t := (a.FeqF t).trans (b.FeqF _)
  Gterm t := (a.Gterm t).trans (b.Gterm _)
  atP p := LocIso.trans (a.atP p) (b.atP p)
  ePl := a.ePl.trans b.ePl
  BBne t q := (a.BBne t q).trans (b.BBne _ _)
  generic t := (a.generic t).trans (b.generic _)
  eP u u' := (a.eP u u').trans (b.eP u u')
  pfst p := (congrArg (b.eT _ _) (a.pfst p)).trans (b.pfst _)
  psnd p := (congrArg (b.eT _ _) (a.psnd p)).trans (b.psnd _)
  s0 p := (a.s0 p).trans (b.s0 _)
  scalarPair p := (a.scalarPair p).trans (b.scalarPair _)
  pval p := (a.pval p).trans (b.pval _)
  ptOf t := (a.ptOf t).trans (b.ptOf _)
  cTerm t := (a.cTerm t).trans (b.cTerm _)
  massPair p := (a.massPair p).trans (b.massPair _)
  meanCount := a.meanCount.trans b.meanCount

end Trans

section Move

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ)

theorem SRest.exists_re_ofDiv {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P)
    {F' : ∀ u, Forms0 (reD D (New.ofDiv D N hh)) u} (h : SameForms0LevelsAndValues (New.ofDiv D N hh) F F')
    (hF : FinX (reY (New.ofDiv D N hh) P.Y)) :
    ∃ S' : SRest (P.re (New.ofDiv D N hh) h hF), HEq S'.j S.j := by
  obtain ⟨e, heH, heC⟩ := sIso_reD D (New.ofDiv D N hh) P.X P.Y P.fin hF
  let hI' : SIso (reD D (New.ofDiv D N hh)).s (sOf (P.re (New.ofDiv D N hh) h hF).fin) := (by with_unfolding_all exact (SIso.trans S.hI e :))
  let aT : Formalism.MainNotions.S.AutTie (reD D (New.ofDiv D N hh)) (P.re (New.ofDiv D N hh) h hF).X.B
      (P.re (New.ofDiv D N hh) h hF).X.pl :=
    ⟨(by with_unfolding_all exact (S.autTie.n_eq :)), (by with_unfolding_all exact (S.autTie.f_eq :)), (by with_unfolding_all exact (S.autTie.rd_eq :)), (by with_unfolding_all exact (S.autTie.eps_eq :)),
      (by with_unfolding_all exact (S.autTie.lam_eq :)), (by with_unfolding_all exact (S.autTie.ds :)), (by with_unfolding_all exact (S.autTie.low :)), (by with_unfolding_all exact (S.autTie.g_eq :)),
      (by with_unfolding_all exact (S.autTie.g0_eq :)), (by with_unfolding_all exact (S.autTie.D_eq :)), (by with_unfolding_all exact (S.autTie.Dstar_eq :))⟩
  let jj : (reD D (New.ofDiv D N hh)).what₂.EE ≃ₗᵢ[ℂ] EEC (P.re (New.ofDiv D N hh) h hF).X
      (P.re (New.ofDiv D N hh) h hF).G := (by with_unfolding_all exact (S.j :))
  have lT : Formalism.L2.SG.Pf.LocCP.LocTied (reD D (New.ofDiv D N hh)) := (by with_unfolding_all exact (S.locTied :))
  have cP : ∀ (u : (reD D (New.ofDiv D N hh)).what₂.Word) (x : (reD D (New.ofDiv D N hh)).s.Cu u),
      colDict (P.re (New.ofDiv D N hh) h hF).X ((P.re (New.ofDiv D N hh) h hF).tr u)
        (P.re (New.ofDiv D N hh) h hF).Y.hK ((P.re (New.ofDiv D N hh) h hF).into u)
        ((P.re (New.ofDiv D N hh) h hF).bij u) (hI'.eCu u x) = (reD D (New.ofDiv D N hh)).s_Cu u x := by
    intro u x
    have hx : hI'.eCu u x = ((by with_unfolding_all exact (S.hI.eCu u x :))) := (by with_unfolding_all exact (congrArg (fun f => f (S.hI.eCu u x)) (eq_of_heq (heC u)) :))
    rw [hx]
    apply Subtype.ext
    exact (by with_unfolding_all exact ((colDictL_reTr (New.ofDiv D N hh) (P.tr u) (h u).2.1 (h u).2.2 P.Y.hK
      (toCu (cs := P.Y.cs u) (hinj := P.fin.shInj u) P.X P.Y.hK (S.hI.eCu u x))).trans (congrArg Subtype.val (S.colPin u x)) :))
  have rP : ∀ x : (reD D (New.ofDiv D N hh)).what₂.EE,
      hI'.eHH ((reD D (New.ofDiv D N hh)).sEE x) =
        conjHH (P.re (New.ofDiv D N hh) h hF).X (P.re (New.ofDiv D N hh) h hF).G (jj x) := by
    intro x
    exact (by with_unfolding_all exact ((congrArg (fun f => f (S.hI.eHH (D.sEE x))) (eq_of_heq heH)).trans (S.rowPin x) :))
  exact ⟨⟨hI', aT, cP, jj, rP, lT⟩, (by with_unfolding_all exact (HEq.refl S.j :))⟩

end Move

end GlobalTheory.Mem.SRe

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.referenceTupleLiftForms_pass_to_coeffEnlargement : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (W₁ : Set B₁.places.Pl) (W₂ : Set B₂.places.Pl), Enl B₁ B₂ → HEq (B₂.primes w₂.px).vGs (B₁.primes w₁.px).vGs → (∀ (j₁ : Fin B₁.R.m) (j₂ : Fin B₂.R.m), (j₁ : ℕ) = j₂ → ∀ (p₁ : {p // p ∈ (B₁.primes w₁.px).vGs}) (p₂ : {p // p ∈ (B₂.primes w₂.px).vGs}), HEq p₂.1 p₁.1 → ∀ (c₁ : (𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)ˣ) (c₂ : (𝓞 B₂.fields.E ⧸ p₂.1.asIdeal)ˣ), HEq c₂ c₁ → B₂.embLL ((w₂.I.Ch.chi j₂ p₂ c₂ : B₂.fields.Kˣ) : B₂.fields.K) = B₁.embLL ((w₁.I.Ch.chi j₁ p₁ c₁ : B₁.fields.Kˣ) : B₁.fields.K)) → ∀ j₁ j₂ : ℕ, j₁ = j₂ → (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).D = (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).D ∧ ∀ φ₁ : (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).EqFun, ∃ φ₂ : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).EqFun, ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (φ₂.1 d₂).1) (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (φ₁.1 d₁).1) := by
  first | exact @GlobalTheory.Mem.R3.Tr.lift_refTuple_enl | exact GlobalTheory.Mem.R3.Tr.lift_refTuple_enl | (intros; apply GlobalTheory.Mem.R3.Tr.lift_refTuple_enl <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.OkVals

theorem isConjAt_embLL (B : Base) : Formalism.DivisionValues.IsConjAt (InfinitePlace.mk B.embLL) := fun a => by
  rcases InfinitePlace.embedding_mk_eq B.embLL with e | e
  · rw [e]
    exact B.starLL_cx a
  · rw [e, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, B.starLL_cx a]

theorem ev_of_forall {p : Top.Ctx → Prop} (h : ∀ K, p K) : Top.Ev p :=
  ⟨1 / 100, by norm_num, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨0, fun K _ _ _ _ _ => h K⟩⟩⟩⟩⟩

theorem large_coefficientField_contains_twist_values : Top.EvLg fun _ B f T => ∀ (px : PreX B.toPre) (I : Col2.ColIn B px) (hX : B.fields.Ok), I.Ok → I.C = f →
    Set.range I.xi = T.set f → ValsIn I ∧ ∀ U Xg tr, (∀ χ ∈ Xg, IsAbsIrrChar χ) → (famC I hX U Xg tr).fam3.Ok3 1 := by
  obtain ⟨Sv, hSv, hV⟩ := GlobalTheory.T.exists_algebraicRoots_coeffFieldContainsTwistValues
  obtain ⟨So, hSo, hF⟩ := GlobalTheory.T.exists_coefficientField_contains_heckeEigenvalues
  unfold Top.EvLg
  refine ev_of_forall fun _ => ?_
  unfold Top.large₂
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun P f F F₀ Ξ => Sv P Ξ ∪ So P f F F₀ Ξ, fun _ _ _ z hz => absurd hz (Finset.notMem_empty z), ?_, ?_⟩
  · intro P f F F₀ Ξ z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact hSv P Ξ z h
    · exact hSo P f F F₀ Ξ z h
  intro B f T _ hH _ _ px I hX hOk hC hR
  have hL : ∀ z ∈ Sv B.toPre (Set.range I.xi) ∪ So B.toPre I.C B.KsC B.fixedCoefficientFieldInComplex (Set.range I.xi), z ∈ B.LLC := by
    rw [hR, hC]
    exact hH.2
  refine ⟨hV B px I hOk fun z hz => hL z (Finset.mem_union_left _ hz), fun U Xg tr hirr => ?_⟩
  have hFI := hF B px I hX hOk fun z hz => hL z (Finset.mem_union_right _ hz)
  have hC2 := GlobalTheory.T.rowsLifts_heckeOperators_commute B px I hX hOk
  have key : ∀ τ : TupU I U, ∃ a : I.ι, I.tup a = τ.1 := fun τ => ⟨_, tup_ixOf I τ⟩

  have hH3 : ColHyp3 B.wts I.Ch I.sel (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ := by
    refine ⟨⟨isConjAt_embLL B, hirr, fun τ => Formalism.L2.Col.heckeComm_of_paths _ _ Formalism.L2.Col.pathCount_symmetric_holds, fun τ => ?_,
      fun j τ => Formalism.L2.Col.heckeComm_of_paths _ _ Formalism.L2.Col.pathCount_symmetric_holds, fun j τ => ?_⟩, fun τ => ?_, fun τ => ?_, fun j τ => ?_, fun j τ => ?_⟩
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact fun i => (hFI a).1 (Sum.inl i)
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact fun i => (hFI a).2 j (Sum.inl i)
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact (hC2 a).1
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact fun i => (hFI a).1 (Sum.inr i)
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact (hC2 a).2 j
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact fun i => (hFI a).2 j (Sum.inr i)
  have h := colFam3_ok B.wts I.Ch I.sel hX (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ (xiValOf I) tr hH3
  exact h

end GlobalTheory.Mem.R3.OkVals

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Cls

theorem coeffField_rootsOfUnity_typePrimes_hermitianStages : ∀ X : Stages, GlobalTheory.Core.Cls.RootsG X.toD7 := by
  intro X i
  have hp : Nat.Prime (X.B.host.g i) := X.B.host.g_prime i
  obtain ⟨z, -, hz⟩ := X.B.roots_Ks (X.B.host.g i * (X.B.host.g i - 1)) (by fin_cases i <;> simp)
  have hne : X.B.host.g i * (X.B.host.g i - 1) ≠ 0 :=
    mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim : IsPrimitiveRoot z (X.B.host.g i * (X.B.host.g i - 1)) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := X.B.embLL) ?_ X.B.embLL.injective
    rw [hz]
    exact_mod_cast Complex.isPrimitiveRoot_exp _ hne
  have hpos : 0 < X.B.host.g i * (X.B.host.g i - 1) := Nat.pos_of_ne_zero hne
  exact ⟨⟨z ^ (X.B.host.g i - 1), hprim.pow hpos (mul_comm _ _)⟩, ⟨z ^ X.B.host.g i, hprim.pow hpos rfl⟩⟩

end GlobalTheory.Core.Cls
end

section

open CategoryTheory Polynomial

theorem _root_.GlobalTheory.T.trace_harishChandra_induced_eq_product_characters : ∀ (g : ℕ) [Fact g.Prime] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x := by
  first | exact @GlobalTheory.HCChar.trace_hcRep_eq_hcL | exact GlobalTheory.HCChar.trace_hcRep_eq_hcL | (intros; apply GlobalTheory.HCChar.trace_hcRep_eq_hcL <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

theorem _root_.GlobalTheory.T.splitPlaceTransvection_acts_positively_invariant_forms : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ ξ, IsoVec T ξ → ∀ e, IsSplitIdem D e → ∀ z ∈ ZI T ξ, Formalism.L2.Theta.SuppAt e T z → ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ a f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (along S T ξ a) f) = ℓ f) → ∀ f, IsThetaFunO ψ S T f → ℓ (om (1, z) f) = (r : ℂ) * ℓ f := by
  first | exact @GlobalTheory.SplitTransvection.transvection_pos | exact GlobalTheory.SplitTransvection.transvection_pos | (intros; apply GlobalTheory.SplitTransvection.transvection_pos <;> assumption)
end
