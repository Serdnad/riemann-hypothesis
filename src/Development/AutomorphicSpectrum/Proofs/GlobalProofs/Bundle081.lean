module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle069
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle075
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousConjBlockEmbedding
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle076
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle080
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf

open MeasureTheory GlobalTheory.SiegelSet GlobalTheory.Mem.AutSpace GlobalTheory.SphSmooth

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

def pairSpan (V : HSp D) (φ c : GA D V → ℂ) : Submodule ℂ ((GA D V → ℂ) × (GA D V → ℂ)) :=
  Submodule.span ℂ {p | ∃ l : List (ℝ → GA D V), (∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) ∧
    p = (l.foldr lineDer φ, l.foldr lineDer c)}

theorem pairSpan_le (φ c : GA D V → ℂ) : pairSpan V φ c ≤ (derSpan V φ).prod (derSpan V c) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, rfl⟩
  exact ⟨Submodule.subset_span ⟨l, hl, rfl⟩, Submodule.subset_span ⟨l, hl, rfl⟩⟩

theorem Rder_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) {p : (GA D V → ℂ) × (GA D V → ℂ)}
    (hp : p ∈ pairSpan V φ c) : (Rder θ V τ X p.1, Rder θ V τ X p.2) ∈ pairSpan V φ c := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact Submodule.subset_span ⟨oneP θ V τ X :: l, List.forall_mem_cons.2 ⟨isRealLine_oneP hθ V hX, hl⟩, rfl⟩
  | zero =>
    have := Rder_smul (θ := θ) 0 (0 : GA D V → ℂ) τ X
    rw [zero_smul, zero_smul] at this
    simp only [Prod.fst_zero, Prod.snd_zero, this]
    exact zero_mem (pairSpan V φ c)
  | add x y hx hy ihx ihy =>
    have h1 := pairSpan_le φ c hx
    have h2 := pairSpan_le φ c hy
    simp only [Prod.fst_add, Prod.snd_add]
    rw [Rder_add (derSpan_le hθ hφ h1.1) (derSpan_le hθ hφ h2.1) hX,
      Rder_add (derSpan_le hθ hc h1.2) (derSpan_le hθ hc h2.2) hX]
    exact add_mem ihx ihy
  | smul a x _ ih =>
    simp only [Prod.smul_fst, Prod.smul_snd, Rder_smul]
    exact Submodule.smul_mem _ a ih

theorem RderC_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) (τ : D.what₂.Tau)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) {p : (GA D V → ℂ) × (GA D V → ℂ)}
    (hp : p ∈ pairSpan V φ c) : (RderC θ V τ Z p.1, RderC θ V τ Z p.2) ∈ pairSpan V φ c := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  exact add_mem (Rder_mem_pairSpan hθ hφ hc h1 hp)
    (Submodule.smul_mem _ Complex.I (Rder_mem_pairSpan hθ hφ hc h2 hp))

theorem word_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) (τ : D.what₂.Tau)
    (L : List ((GA D V → ℂ) → GA D V → ℂ)) (hL : ∀ A ∈ L, ∃ Z, A = RderC θ V τ Z) :
    (L.foldr (fun f acc => f acc) φ, L.foldr (fun f acc => f acc) c) ∈ pairSpan V φ c := by
  induction L with
  | nil => exact Submodule.subset_span ⟨[], by simp, rfl⟩
  | cons A L ih =>
    obtain ⟨Z, rfl⟩ := hL A List.mem_cons_self
    exact RderC_mem_pairSpan hθ hφ hc τ Z (ih fun B hB => hL B (List.mem_cons_of_mem _ hB))

theorem gelf_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) (τ : D.what₂.Tau)
    (k : ℕ) : (gelf θ V τ k φ, gelf θ V τ k c) ∈ pairSpan V φ c := by
  have e : (gelf θ V τ k φ, gelf θ V τ k c) = ∑ idx : Fin (k + 1) → Fin V.rank,
      ((List.ofFn fun a : Fin (k + 1) => RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) φ,
        (List.ofFn fun a : Fin (k + 1) => RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) c) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]; rfl
    · rw [Prod.snd_sum]; rfl
  rw [e]
  refine Submodule.sum_mem _ fun idx _ => word_mem_pairSpan hθ hφ hc τ _ fun A hA => ?_
  obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).1 hA
  exact ⟨_, rfl⟩

variable {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}

theorem good_of_mem_pairSpan (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (T : Finset (Fin m)) {φ c : GA D V → ℂ}
    (hφ : IsSmModOn D.sp.cm.sig V.gram ((GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V)) : Set (GA D V)) φ)
    (h : ∀ l : List (ℝ → GA D V), (∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) →
      IsConstAlong D.sp.cm.sig V.gram X T (l.foldr lineDer φ) (l.foldr lineDer c))
    (μ : Measure (unip D.sp.cm.sig V.gram X T)) (𝓕 : Set (unip D.sp.cm.sig V.gram X T)) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain ((GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram).subgroupOf (unip D.sp.cm.sig V.gram X T)) 𝓕 μ)
    (h1 : μ 𝓕 = 1) (g : GA D V) {p : (GA D V → ℂ) × (GA D V → ℂ)} (hp : p ∈ pairSpan V φ c) :
    IntegrableOn (fun u : unip D.sp.cm.sig V.gram X T => p.1 ((u : GA D V) * g)) 𝓕 μ ∧
      p.2 g = ∫ u in 𝓕, p.1 ((u : GA D V) * g) ∂μ := by
  have hJ : IsHermND D.sp.cm.sig V.gram :=
    ⟨fun i j => V.herm.eq (V.frame j) (V.frame i), (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero⟩
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine ⟨?_, h l hl μ 𝓕 hμ h𝓕 h1 g⟩
    obtain ⟨C, hC, hcov⟩ := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame _ _ _ (GlobalTheory.AdelicU.isCMExt_host D) _ _ hJ _ X Y hW T
    have hcont := GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic _ _ _ (GlobalTheory.AdelicU.isCMExt_host D) _ _ hJ φ hφ.level hφ.cont hφ.smooth l hl
    have hleft := GlobalTheory.UAut.ConstAut.leftInv_foldr
      (Γ := (GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V))) (φ := φ) (fun γ hγ x => hφ.left γ hγ x) l
    refine GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ _ C hC hcov μ hμ 𝓕 h𝓕 _
      (hcont.comp (continuous_subtype_val.mul continuous_const)) fun γ hγ u => ?_
    simp only [Subgroup.coe_mul, mul_assoc]
    exact hleft γ ⟨Subgroup.mem_subgroupOf.1 hγ, γ.2⟩ _
  | zero => exact ⟨integrableOn_zero, by simp⟩
  | add x y _ _ ihx ihy =>
    refine ⟨ihx.1.add ihy.1, ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [ihx.2, ihy.2]
    exact (integral_add ihx.1 ihy.1).symm
  | smul a x _ ih =>
    refine ⟨ih.1.const_mul a, ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [ih.2]
    exact (integral_const_mul a _).symm

theorem isConstAlong_gelf : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (φ c : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram ((GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V)) : Set (GA D V)) φ → GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram c → (∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c)) → ∀ (τ : D.what₂.Tau) (k : ℕ), IsConstAlong D.sp.cm.sig V.gram X T (gelf θ V τ k φ) (gelf θ V τ k c) := by
  intro D θ hθ V m X Y hW T φ c hφ hc h τ k μ 𝓕 hμ h𝓕 h1 g
  have sφ : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram φ := hφ.smooth
  exact (good_of_mem_pairSpan hW T hφ h μ 𝓕 hμ h𝓕 h1 g
    (gelf_mem_pairSpan hθ (mem_smFun_of_isSm hθ sφ) (mem_smFun_of_isSm hθ hc) τ k)).2

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet


theorem _root_.GlobalTheory.T.orthogonal_subspace_unitary_embedding : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → (∀ h, s h ∈ uPart D.sp.cm.sig V.gram X Y T) ∧ (∀ g ∈ uPart D.sp.cm.sig V.gram X Y T, ∃ h, s h = g) ∧ ∀ h ∈ GfC V', s h ∈ GfC V := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb.range_embHom | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb.range_embHom | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb.range_embHom <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb (hT_col)
open Formalism.UG (cT)

variable {D : D7} {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V}

theorem frameMat_mulVec (z : Fin V'.rank → D.host.E) :
    frameMat V V' ι *ᵥ z = ⇑(V.frame.repr (ι (V'.frame.equivFun.symm z))) := by
  have h := LinearMap.toMatrix_mulVec_repr V'.frame V.frame ι (V'.frame.equivFun.symm z)
  have hz : ⇑(V'.frame.repr (V'.frame.equivFun.symm z)) = z := funext fun i => repr_symm V' z i
  rw [hz] at h
  exact h

theorem symm_frameMat_mulVec (z : Fin V'.rank → D.host.E) :
    V.frame.equivFun.symm (frameMat V V' ι *ᵥ z) = ι (V'.frame.equivFun.symm z) := by
  rw [frameMat_mulVec]
  have h := V.frame.equivFun.symm_apply_apply (ι (V'.frame.equivFun.symm z))
  rwa [Module.Basis.equivFun_apply] at h

theorem hE_eq_hT (V : HSp D) (a b : Fin V.rank → D.host.E) :
    hE D.sp.cm.sig V.gram a b = V.hT (V.frame.equivFun.symm a) (V.frame.equivFun.symm b) := by
  rw [hT_frame]
  rfl

theorem frameMat_isom (hι : HSpace.IsIsomEmb V' V ι) :
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram * frameMat V V' ι = V'.gram := by
  rw [cT_frameMat_mul_gram, Matrix.mul_assoc, prM_mul_frameMat hι, Matrix.mul_one]

theorem pairing_submatrix (hι : HSpace.IsIsomEmb V' V ι) {m m' : ℕ} {e : Fin m' → Fin m}
    {A B : Matrix (Fin V.rank) (Fin m) D.host.E} {A' B' : Matrix (Fin V'.rank) (Fin m') D.host.E}
    (hA : frameMat V V' ι * A' = A.submatrix id e) (hB : frameMat V V' ι * B' = B.submatrix id e) :
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) A' * V'.gram * B' =
      (cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B).submatrix e e := by
  have hc : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι * A') =
      cT (D.sp.cm.sig : D.host.E →+* D.host.E) A' * cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) := by
    simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have h1 : cT (D.sp.cm.sig : D.host.E →+* D.host.E) A' * V'.gram * B' =
      cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι * A') * V.gram * (frameMat V V' ι * B') := by
    rw [← frameMat_isom hι, hc]
    simp only [Matrix.mul_assoc]
  rw [h1, hA, hB]
  ext i j
  simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply, id]

theorem exists_sliceFrame : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∃ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' ∧ GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' := by
  intro D V m X Y hW T V' ι hι hrange
  classical
  obtain ⟨hxx, hyy, hxy, hani⟩ := hW
  have hpair : ∀ {p q : ℕ} (A : Matrix (Fin V.rank) (Fin p) D.host.E)
      (B : Matrix (Fin V.rank) (Fin q) D.host.E) (k : Fin p) (i : Fin q),
      V.hT (V.frame.equivFun.symm fun j => A j k) (V.frame.equivFun.symm fun j => B j i) =
        (cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B) k i := by
    intro p q A B k i
    rw [hT_col V A (fun j => B j i) k]
    rfl
  have hne : ∀ i k, i ∉ upTo T → k ∈ upTo T → i ≠ k := by
    rintro i k hi hk rfl
    exact hi hk
  have hxmem : ∀ i, i ∉ upTo T → (V.frame.equivFun.symm fun j => X j i) ∈ LinearMap.range ι := by
    intro i hi
    rw [hrange]
    intro k hk
    constructor
    · rw [hpair X X k i, hxx, Matrix.zero_apply]
    · rw [← V.herm.eq (V.frame.equivFun.symm fun j => X j i) (V.frame.equivFun.symm fun j => Y j k),
        hpair X Y i k, hxy, Matrix.one_apply_ne (hne i k hi hk), map_zero]
  have hymem : ∀ i, i ∉ upTo T → (V.frame.equivFun.symm fun j => Y j i) ∈ LinearMap.range ι := by
    intro i hi
    rw [hrange]
    intro k hk
    constructor
    · rw [hpair X Y k i, hxy, Matrix.one_apply_ne (hne i k hi hk).symm]
    · rw [hpair Y Y k i, hyy, Matrix.zero_apply]
  set S : Finset (Fin m) := Finset.univ.filter (fun i => i ∉ upTo T) with hS
  have he_mono : StrictMono (fun k => S.orderEmbOfFin rfl k) := (S.orderEmbOfFin rfl).strictMono
  have he_range : ∀ i, i ∉ upTo T ↔ i ∈ Set.range (fun k => S.orderEmbOfFin rfl k) := by
    intro i
    have h : Set.range (fun k => S.orderEmbOfFin rfl k) = (S : Set (Fin m)) :=
      Finset.range_orderEmbOfFin S rfl
    rw [h, hS]
    simp
  have he_out : ∀ k, S.orderEmbOfFin rfl k ∉ upTo T := fun k => (he_range _).2 ⟨k, rfl⟩
  have hx' : ∀ k, ∃ w : V'.V, ι w = V.frame.equivFun.symm fun j => X j (S.orderEmbOfFin rfl k) :=
    fun k => LinearMap.mem_range.1 (hxmem _ (he_out k))
  have hy' : ∀ k, ∃ w : V'.V, ι w = V.frame.equivFun.symm fun j => Y j (S.orderEmbOfFin rfl k) :=
    fun k => LinearMap.mem_range.1 (hymem _ (he_out k))
  choose wx hwx using hx'
  choose wy hwy using hy'
  have hsym : ∀ w : V'.V, V'.frame.equivFun.symm (fun a => V'.frame.repr w a) = w := by
    intro w
    have h := V'.frame.equivFun.symm_apply_apply w
    rw [Module.Basis.equivFun_apply] at h
    exact h
  have hcol : ∀ (Z : Matrix (Fin V.rank) (Fin m) D.host.E) (w : Fin S.card → V'.V),
      (∀ k, ι (w k) = V.frame.equivFun.symm fun j => Z j (S.orderEmbOfFin rfl k)) →
      frameMat V V' ι * Matrix.of (fun a k => V'.frame.repr (w k) a) =
        Z.submatrix id (fun k => S.orderEmbOfFin rfl k) := by
    intro Z w hw
    ext a k
    have h := congrFun (frameMat_mulVec (V := V) (V' := V') (ι := ι)
      (fun b => V'.frame.repr (w k) b)) a
    rw [hsym (w k), hw k, repr_symm] at h
    exact h
  refine ⟨S.card, fun k => S.orderEmbOfFin rfl k, Matrix.of (fun a k => V'.frame.repr (wx k) a),
    Matrix.of (fun a k => V'.frame.repr (wy k) a), ?_, ?_⟩
  · exact And.intro he_mono (And.intro he_range (And.intro (hcol X wx hwx) (hcol Y wy hwy)))
  have hXX := pairing_submatrix hι (hcol X wx hwx) (hcol X wx hwx)
  have hYY := pairing_submatrix hι (hcol Y wy hwy) (hcol Y wy hwy)
  have hXY := pairing_submatrix hι (hcol X wx hwx) (hcol Y wy hwy)
  refine GlobalTheory.SiegelSet.IsWittFrame.mk ?_ ?_ ?_ ?_
  · rw [hXX, hxx]
    rfl
  · rw [hYY, hyy]
    rfl
  · rw [hXY, hxy]
    exact Matrix.submatrix_one _ he_mono.injective
  · intro z' h1 h2 h3
    have hz : frameMat V V' ι *ᵥ z' = 0 := by
      apply hani
      · funext i
        rw [← hT_col, symm_frameMat_mulVec]
        by_cases hi : i ∈ upTo T
        · exact ((hrange _).1 (LinearMap.mem_range_self ι _) i hi).1
        · obtain ⟨k, rfl⟩ := (he_range i).1 hi
          rw [← hwx k, hι (wx k) (V'.frame.equivFun.symm z'), ← hsym (wx k)]
          exact (hT_col V' (Matrix.of fun a k => V'.frame.repr (wx k) a) z' k).trans (congrFun h1 k)
      · funext i
        rw [← hT_col, symm_frameMat_mulVec]
        by_cases hi : i ∈ upTo T
        · exact ((hrange _).1 (LinearMap.mem_range_self ι _) i hi).2
        · obtain ⟨k, rfl⟩ := (he_range i).1 hi
          rw [← hwy k, hι (wy k) (V'.frame.equivFun.symm z'), ← hsym (wy k)]
          exact (hT_col V' (Matrix.of fun a k => V'.frame.repr (wy k) a) z' k).trans (congrFun h2 k)
      · rw [hE_eq_hT, symm_frameMat_mulVec,
          hι (V'.frame.equivFun.symm z') (V'.frame.equivFun.symm z'), ← hE_eq_hT V' z' z']
        exact h3
    have h := congrArg (fun w => prM V V' ι *ᵥ w) hz
    simp only [Matrix.mulVec_mulVec, prM_mul_frameMat hι, Matrix.one_mulVec, Matrix.mulVec_zero] at h
    exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.langlands_decomposition_unipotent_levi : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (b : GA D V), ∃ n ∈ unip D.sp.cm.sig V.gram X T, ∃ mm ∈ levi D.sp.cm.sig V.gram X Y T, ∃ b₀ : GA D V, b = n * mm * b₀ ∧ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.IsAdapted V X Y T ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b₀)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.iwasawa_adapted | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.iwasawa_adapted | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.iwasawa_adapted <;> assumption)
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem _root_.GlobalTheory.T.constant_term_smooth_moderate_growth : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (φ c : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram ((GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V)) : Set (GA D V)) φ → GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram c → (∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c)) → ∀ (τ : D.what₂.Tau) (k : ℕ), IsConstAlong D.sp.cm.sig V.gram X T (gelf θ V τ k φ) (gelf θ V τ k c) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf.isConstAlong_gelf | exact GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf.isConstAlong_gelf | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf.isConstAlong_gelf <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet


theorem _root_.GlobalTheory.T.orthogonal_subspace_witt_frame_extension : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∃ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' ∧ GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.exists_sliceFrame | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.exists_sliceFrame | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.exists_sliceFrame <;> assumption)

end
end
