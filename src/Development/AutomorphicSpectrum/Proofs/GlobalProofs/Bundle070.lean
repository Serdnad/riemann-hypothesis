module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle754
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealLineBlockEmbeddingExpInfinitePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraSpannedByCompactAndFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle607
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle630
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle529
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle051
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle671
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle068
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle328
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle069
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.GoodPos

theorem goodPos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ g : GAd σ J, ∃ u ∈ GlobalTheory.StdPar.unip σ J Xf S, u ∈ infPts σ J ∧ ∃ (y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E)) (g₀ : GAd σ J),
        g = u * ι (GlobalTheory.CuspRep.infGL E d y) * g₀ ∧
        ∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K := by
  intro F E _ _ _ _ _ _ σ hCM n J hJ r Xf Yf hW K hK S l d h ι hι hd h1 h2 h3 g
  have hconj : ∀ a : GAd σ J, Continuous fun x : GAd σ J => a * x * a⁻¹ := fun a =>
    (continuous_const.mul continuous_id).mul continuous_const
  have hnorm : ∀ a x : GAd σ J, x ∈ infPts σ J → a * x * a⁻¹ ∈ infPts σ J := fun a x hx => by
    rw [mem_infPts_iff_forall] at hx ⊢
    intro v
    simp [map_mul, map_inv, hx v]
  set K1 : Subgroup (GAd σ J) := K.map (MulAut.conj g).toMonoidHom with hK1
  have hK1le : K1 ≤ infPts σ J := by
    rintro _ ⟨x, hx, rfl⟩
    exact hnorm g x (hK.1.1 hx)
  have hK1c : IsCompact (K1 : Set (GAd σ J)) := by
    have : (K1 : Set (GAd σ J)) = (fun x => g * x * g⁻¹) '' (K : Set (GAd σ J)) := by
      ext x; simp [hK1, MulAut.conj_apply]
    rw [this]; exact hK.1.2.image (hconj g)
  obtain ⟨c, hc, hle⟩ := GlobalTheory.T.exists_majorantFrame_compact_subgroup_le F E σ hCM n J hJ K1 hK1le hK1c
  set K2 : Subgroup (GAd σ J) := (majCpt σ J c).map (MulAut.conj g⁻¹).toMonoidHom with hK2
  have hmc := (isMaxCpt_majCpt hCM hc).1
  have hK2le : K2 ≤ infPts σ J := by
    rintro _ ⟨x, hx, rfl⟩
    exact hnorm g⁻¹ x (hmc.1 hx)
  have hK2c : IsCompact (K2 : Set (GAd σ J)) := by
    have : (K2 : Set (GAd σ J)) = (fun x => g⁻¹ * x * g⁻¹⁻¹) '' (majCpt σ J c : Set (GAd σ J)) := by
      ext x; simp [hK2, MulAut.conj_apply]
    rw [this]; exact hmc.2.image (hconj g⁻¹)
  have hKK2 : K ≤ K2 := fun x hx => ⟨g * x * g⁻¹, hle ⟨x, hx, rfl⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hK2K : K2 ≤ K := hK.2 ⟨hK2le, hK2c⟩ hKK2
  obtain ⟨u, hu, hui, y, hy⟩ := exists_conj_mem_majCpt_frame F E σ hCM n J hJ r Xf Yf hW c hc S l d h ι hι hd h1 h2 h3
  refine ⟨u, hu, hui, y, (u * ι (GlobalTheory.CuspRep.infGL E d y))⁻¹ * g, by group, fun k => hK2K ?_⟩
  refine ⟨_, hy k, ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv, _root_.mul_inv_rev]
  group

end GlobalTheory.CompanionTheory.GoodPos
end

section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.CuspSmooth

theorem mem_Sm_blockEmb_smFun : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.host.E] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (l d : ℕ) (h : l + d ≤ m)
    (ι : GlobalTheory.CuspRep.GA D.host.E d →* GA D V), GlobalTheory.BlockForms.IsBlockEmb D.sp.cm.sig V.gram X Y h ι →
    ∀ F : GlobalTheory.Mem.AutSpace.SmFun θ V, (fun x => F.1 (ι x)) ∈ GlobalTheory.CuspRep.Sm D.host.E d := by
  intro D _ θ hθ V m Xf Yf hW l d h ι hι F g
  classical
  obtain ⟨hcm, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  refine GlobalTheory.T.contDiffOn_invSet_of_smooth_along_prod_exp D.host.E d _ {X | ∃ v, ∀ i j, ∀ u, u ≠ v → X i j u = 0} ?_ ?_
  · rw [eq_top_iff]
    intro X _
    have e : X = ∑ v : InfinitePlace D.host.E, (Matrix.of fun i j => Pi.single v (X i j v)) := by
      ext i j u
      rw [Matrix.sum_apply, Finset.sum_apply]
      simp [Pi.single_apply]
    rw [e]
    exact Submodule.sum_mem _ fun v _ => Submodule.subset_span ⟨v, fun i j u hu => by simp [hu]⟩
  · intro k X hX y hy
    choose v hv using hX
    have hγ : ∀ i, IsRealLine D.sp.cm.sig V.gram (fun t : ℝ => ι (GlobalTheory.CuspRep.infGL D.host.E d (GlobalTheory.CuspRep.expGLi d (t • X i)))) :=
      fun i => GlobalTheory.BlockRealLine.isRealLine_blockEmb_exp D.host.F D.host.E D.sp.cm.sig hcm _ V.gram (hJ V) m Xf Yf hW l d h ι hι (v i) (X i) (hv i)
    choose p hp e using fun i => (hγ i).eq_oneP hθ
    have hs := F.2 k (fun i => (p i).1) (fun i => (p i).2) hp (ι (g * GlobalTheory.CuspRep.infGL D.host.E d hy.unit))
    simp only [← e] at hs
    convert hs using 2 with t
    set P : GL (Fin d) (GlobalTheory.CuspRep.Cinf D.host.E) := (List.ofFn fun i => GlobalTheory.CuspRep.expGLi d (t i • X i)).prod
    have hP : (P : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf D.host.E)) =
        (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod := by
      simp only [P]
      rw [← Units.coeHom_apply, map_list_prod, List.map_ofFn]
      rfl
    have hU : GlobalTheory.CuspRep.toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod) =
        GlobalTheory.CuspRep.toL (hy.unit * P).val := by
      rw [Units.val_mul, hP]
      congr 2
    rw [hU, GlobalTheory.CuspRep.chart_val]
    have e3 : (List.ofFn fun i => ι (GlobalTheory.CuspRep.infGL D.host.E d (GlobalTheory.CuspRep.expGLi d (t i • X i)))) =
        (List.ofFn fun i => GlobalTheory.CuspRep.expGLi d (t i • X i)).map (ι.comp (GlobalTheory.CuspRep.infGL D.host.E d)) := by
      simp [List.map_ofFn, Function.comp_def]
    rw [e3, ← map_list_prod]
    simp only [P, map_mul, MonoidHom.comp_apply, mul_assoc]

end GlobalTheory.CompanionTheory.CuspSmooth
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.lie_algebra_spanned_by_compact_and_frame : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ → ∃ (n₁ n₂ : ℕ) (X : Fin n₁ → Matrix (Fin V.rank) (Fin V.rank) ℂ) (y : Fin n₂ → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ a, X a ∈ lieAt V τ) ∧ (∀ b, GlobalTheory.CompanionTheory.HCCusp.IsKLie e (y b)) ∧ (∀ Z ∈ lieAt V τ, Z ∈ Submodule.span ℝ (Set.range X ∪ Set.range fun b => P⁻¹ * y b * P)) ∧ ∀ f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, gelf θ V τ 1 f = ∑ a, Rder θ V τ (X a) (Rder θ V τ (X a) f) - ∑ b, Rder θ V τ (P⁻¹ * y b * P) (Rder θ V τ (P⁻¹ * y b * P) f) :=
  GlobalTheory.CompanionTheory.HCCusp.quadGelf_frame
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame

theorem isIsoFrame_initCols {D : D7} {V : HSp D} {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (k : Fin m) : IsIsoFrame V (GlobalTheory.StdPar.initCols X k) := by
  have hf := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hli := GlobalTheory.CompanionTheory.UnipCocompact.linearIndependent_of_isWittFrame (GlobalTheory.SiegelSet.sigma_sigma hf.1) (hf.2 V) hW
  refine ⟨Nat.succ_pos _, ?_, ?_⟩
  · exact hli.comp (Fin.castLE k.2) (Fin.castLE_injective k.2)
  · have h := hW.xx
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun h (Fin.castLE k.2 a)) (Fin.castLE k.2 b)
    simpa [GlobalTheory.StdPar.initCols, Matrix.mul_apply, Formalism.UG.cT] using this

theorem isCuspFun_of_isConstAlong : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → (∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → r ≤ m) → ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → (∀ k : Fin m, IsConstAlong D.sp.cm.sig V.gram X {k} f 0) → IsCuspFun V f := by
  intro D V m X Y hW hmax f hl hc
  have hl' : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) f := hl
  refine (GlobalTheory.Cusp.isCuspFun_iff hl').2 fun W hW' => ?_
  obtain ⟨r, C, hC, rfl⟩ := (GlobalTheory.AutFunCompare.isIsotropic_iff V W).1 hW'
  have hrm := hmax r C hC
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := hC.1; omega⟩
  let k : Fin m := ⟨r', by omega⟩
  have hC0 : IsIsoFrame V (GlobalTheory.StdPar.initCols X k) := isIsoFrame_initCols hW k
  have hcc : GlobalTheory.Cusp.Cocompact (GQ V) (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) := GlobalTheory.Cusp.cocompact_single _
  haveI : LocallyCompactSpace (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) := by
    rw [GlobalTheory.Cusp.NA_frameFlag hC0]
    exact (GlobalTheory.CuspDecay.Model.isClosed_NI V hC0).locallyCompactSpace
  have e : GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0) = GlobalTheory.SiegelSet.unipRad D.sp.cm.sig V.gram (GlobalTheory.StdPar.initCols X k) :=
    GlobalTheory.Cusp.NA_frameFlag hC0
  have h1 : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) f 0 := by
    rw [e]
    exact GlobalTheory.UAut.isConstTerm_iff.1 ((GlobalTheory.StdPar.isConstAlong_singleton hW k).1 (hc k))
  have h2 : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) f
      (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC0) f) := fun μ 𝓕 b1 b2 b3 g => by
    rw [GlobalTheory.Cusp.constTerm_eq b2 hl' g, MeasureTheory.Measure.real, b3]
    simp
  have h0 : GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC0) f = 0 := h2.unique hcc h1
  exact GlobalTheory.CompanionTheory.ConstTermConj.constTerm_eq_zero_of_frame D V (r' + 1) _ C hC0 hC f hl h0

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame

end
end

section

theorem GlobalTheory.CompanionTheory.Glob.cellSemisimplification : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.CellSemisimplification k :=
  GlobalTheory.SmGL.CellSemis.cellSemisimplification GlobalTheory.T.bernstein_zelevinsky_finiteness
end

section

theorem _root_.GlobalTheory.T.jacquetOfInducedFiltration' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetOfInducedFiltration k := GlobalTheory.T.jacquet_of_induced_filtration
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.cusp_translate_bounded_by_derivative : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D) (hθ : IsInfFam θ) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : GlobalTheory.SmoothForms.LieN V) (φ : GlobalTheory.CompanionTheory.HCCusp.Mc θ V), ‖GlobalTheory.Cusp.Rcusp V μ (GlobalTheory.SmoothForms.expInf θ V X) (GlobalTheory.CompanionTheory.HCCusp.io μ hθ φ) - GlobalTheory.CompanionTheory.HCCusp.io μ hθ φ‖ ≤ ‖GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.derInf hθ X φ)‖ :=
  @GlobalTheory.CompanionTheory.HCCusp.norm_Rcusp_expInf_sub_le
end
