module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle389
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle313
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle275
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle385
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle129
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle335
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle364
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle362
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel : ∀ (D : D7) (V : HSp D), (∃ μ : Measure (GfC V), μ.IsHaarMeasure) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), (∃ μ : Measure ((jacGrp d).subgroupOf (GfC V)), μ.IsHaarMeasure) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∃ μ : Measure ((besGrp d o).subgroupOf (GfC V)), μ.IsHaarMeasure := by
  first | exact @GlobalTheory.HaarExist.haar_exists | exact GlobalTheory.HaarExist.haar_exists | (intros; apply GlobalTheory.HaarExist.haar_exists <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastSrcSlice

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem col_mem_SB {n n' : Type} {Ψ : Matrix n n' k → ℂ} {a : (n → k) → ℂ}
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) (hΨ : Ψ ≠ 0) : a ∈ SB (n → k) := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, Ψ x₀ ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hΨ (funext h0)
  have hg := Comm.comp_mem_SB h
    (p := fun y : n → k => Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y i) j)
    (s := fun x : Matrix n (n' ⊕ Fin 1) k => fun i => x i (Sum.inr 0)) ?_ (by fun_prop) (fun y => rfl)
  · have e : a = (Ψ x₀)⁻¹ • fun y : n → k =>
        tensCol Ψ a (Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y i) j) := by
      funext y
      show a y = (Ψ x₀)⁻¹ * (Ψ x₀ * a y)
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ hg
  · refine continuous_matrix fun i j => ?_
    rcases j with j | j
    · exact continuous_const
    · exact (continuous_apply i)

theorem sb_of_sbHalf (p : SplitPt D k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S T : HSp D} (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) {Φ : WO S T → ℂ} (hΦ : IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) Φ) :
    (fun x => Φ (HalfInd.wr α β x)) ∈ SB (Matrix n n' k) := by
  classical
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  have : CharZero k := charZero_of_injective_ringHom (f := p.pr.comp (incA D)) (RingHom.injective _)
  obtain ⟨-, k0, hk0, hinv, hsup⟩ := hΦ
  obtain ⟨hUc, hUo⟩ := HalfInd.compact_open α β hS hT
  set U := {x : Matrix n n' k | HalfInd.wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧
    IsHalf p.e (HalfInd.wr α β x)} with hU
  have hc : ((k0 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  have hwr : ∀ z : Matrix n n' k, HalfInd.wr α β (((k0 : ℕ) : k) • z) = k0 • HalfInd.wr α β z := by
    intro z
    rw [Nat.cast_smul_eq_nsmul, map_nsmul]
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · refine ⟨{x' | ((k0 : ℕ) : k)⁻¹ • (x' - x) ∈ U}, hUo.preimage (by fun_prop), ?_, fun x' hx' => ?_⟩
    · show ((k0 : ℕ) : k)⁻¹ • (x - x) ∈ U
      rw [sub_self, smul_zero]
      refine ⟨?_, HalfInd.isHalf_wr α β 0⟩
      rw [map_zero]; exact zero_mem _
    · set z := ((k0 : ℕ) : k)⁻¹ • (x' - x) with hz
      have hx'z : x' = x + ((k0 : ℕ) : k) • z := by
        rw [hz, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
      show Φ (HalfInd.wr α β x') = Φ (HalfInd.wr α β x)
      rw [hx'z, map_add (f := _), hwr]
      exact hinv _ hx'.1 hx'.2 _
  · refine HasCompactSupport.intro (hUc.image (f := fun z => ((k0 : ℕ) : k)⁻¹ • z) (by fun_prop)) fun x hx => ?_
    by_contra h
    have h1 := hsup _ h
    have h2 : ((k0 : ℕ) : k) • x ∈ U := by
      refine ⟨?_, HalfInd.isHalf_wr α β _⟩
      rw [hwr]; exact h1
    exact hx ⟨_, h2, by beta_reduce; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem extFun_wr (p : SplitPt D k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S T : HSp D} (α : Frame p S n') (β : Frame p T n) {Φ : WO S T → ℂ} (hΦ : ∀ t, Φ t ≠ 0 → IsHalf p.e t) :
    extFun α β (fun x => Φ (HalfInd.wr α β x)) = Φ := by
  classical
  funext t
  unfold extFun
  by_cases ht : IsHalf p.e t
  · rw [if_pos ht]
    beta_reduce
    rw [HalfInd.wr_rd α β ht]
  · rw [if_neg ht]
    by_contra h
    exact ht (hΦ t (Ne.symm h))

end GlobalTheory.LastSrcSlice

namespace GlobalTheory.LastSrcSlice

theorem main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), a ≠ 0 → ∀ (LA : Lat A) (LS : Lat S), IsSelfDualC A LA → IsSelfDualC S LS → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ a) Ξ → ∀ y : WO L S, ∃ g, Over ψ α β LA LS g Ψ (fun u => Ξ ((o.resS S).symm (u, y))) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ _ V₀ A L S o ζ _ α α₀ β hsum Ψ a ha LA LS hLA hLS L₁ L₂ f₁ Ξ hΞ y
  obtain ⟨hL₁, hL₂, hf₁, hSB, ⟨T, hT⟩, hall⟩ := hΞ
  have hΞT : Ξ = T (extFun α₀ β (tensCol Ψ a)) := hall T hT
  by_cases hΨ0 : Ψ = 0
  ·
    subst hΨ0
    have hext : extFun α₀ β (tensCol (0 : Matrix n n' k → ℂ) a) = 0 := by
      classical
      funext t
      simp [extFun, tensCol]
    have hslice : (fun u => Ξ ((o.resS S).symm (u, y))) = 0 := by
      rw [hΞT, hext, map_zero]; rfl
    have hheis0 : ∀ (w : WO A S), heisO ψ A S w (0 : WO A S → ℂ) = 0 := by
      intro w; funext x; simp [heisO]
    refine ⟨0, hLA, hLS, ⟨?_, ?_⟩, Submodule.zero_mem _, ⟨0, ?_⟩, fun T' hT' => ?_⟩
    · exact { quasi := fun γ w => by simp
              level := ⟨⊤, isOpen_univ, fun u _ _ => hheis0 u⟩
              cont := continuous_const
              smooth := fun _ _ _ _ _ => by simpa using contDiff_const }
    · exact ⟨fun u _ => hheis0 _, fun _ _ u _ _ => hheis0 u⟩
    · exact ⟨fun Φ _ x _ => by simp [hheis0], fun Φ _ y' _ => by simp [hheis0], by simp⟩
    · rw [hslice]
      have : extFun α β (0 : Matrix n n' k → ℂ) = 0 := by
        classical
        funext t; simp [extFun]
      beta_reduce
      rw [this, map_zero]
  · have haSB : a ∈ SB (n → k) := col_mem_SB hSB hΨ0
    have hΨSB : Ψ ∈ SB (Matrix n n' k) := TensSB.of_tensCol_mem hSB ha
    set r := o.resS S with hr
    set a' := ExtZero.colFun β ζ a with ha'
    set ΛA := latO A S (LA : Set (Fin A.rank → D.host.E)) (LS : Set (Fin S.rank → D.host.E)) (· = p.v) with hΛA
    set Λ₁ := latO V₀ S (L₁ : Set (Fin V₀.rank → D.host.E)) (L₂ : Set (Fin S.rank → D.host.E)) (· = p.v) with hΛ₁
    set T₁ := ExtZero.restrModel r a' T y with hT₁
    set g := T₁ (halfInd p.e ΛA) with hg
    have hbox : ∀ Φ : WO A S → ℂ, (fun t => Φ (r t).1 * a' (r t).2) = o.boxS S Φ a' := fun Φ => rfl

    have hsb : ∀ Φ, IsSBHalf p.e ΛA Φ → IsSBHalf p.e Λ₁ (fun t => Φ (r t).1 * a' (r t).2) := by
      intro Φ hΦ
      have h1 := sb_of_sbHalf p α β hLA hLS hΦ
      have h2 := extFun_wr p α β (Φ := Φ) hΦ.1
      rw [hbox, ← h2, ← GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' V₀ A L S o ζ α α₀ β hsum]
      exact OverProof.isSBHalf_extFun D k p _ _ V₀ S α₀ β L₁ L₂ hL₁ hL₂ _ (Comm.tensCol_mem h1 haSB)

    have hmodel : IsPlaceModel ψ (symplO A S) (heisO ψ A S) p.e ΛA 1 g T₁ := by
      refine ⟨?_, ?_, ?_⟩
      · intro Φ hΦ x hx
        funext w
        rw [ExtZero.restrModel_apply]
        have hfun : (fun t => (fun t => Φ (t + x)) (r t).1 * a' (r t).2) =
            fun t => (fun t => Φ (r t).1 * a' (r t).2) (t + r.symm (x, 0)) := by
          funext t
          simp only [map_add (f := _), AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero]
        rw [hfun, hT.trans _ (hsb Φ hΦ) _ (ExtZero.half_resS_symm o hx), hr, ExtZero.heisO_resS_symm]
        rfl
      · intro Φ hΦ y' hy'
        funext w
        rw [ExtZero.restrModel_apply]
        have hfun : (fun t => (fun t => ψ (symplO A S t y') * Φ t) (r t).1 * a' (r t).2) =
            fun t => ψ (symplO V₀ S t (r.symm (y', 0))) * (fun t => Φ (r t).1 * a' (r t).2) t := by
          funext t
          rw [hr, ExtZero.symplO_resS_symm, mul_assoc]
        rw [hfun, hT.modul _ (hsb Φ hΦ) _ (ExtZero.half_resS_symm o hy'), hr, ExtZero.heisO_resS_symm]
        rfl
      · rw [one_smul]

    have hlat : IsLatVac (heisO ψ A S) ΛA g :=
      Rebase.latVac_image D k p ψ hψ A S LA LA LS LS hLA hLS hLA hLS g T₁ hmodel

    have htheta : IsThetaFunO ψ A S g := by
      obtain ⟨ΨA, hΨA, hΨAe⟩ := HalfInd.exists_SB_extFun_eq_halfInd D k p A S n n' α β LA LS hLA hLS
      have hover := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hψ V₀ S α₀ β L₁ L₂ hL₁ hL₂ f₁ hf₁).1
      obtain ⟨F, hF, -⟩ := hover _ (Comm.tensCol_mem hΨA haSB)
      have hFth := ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hψ V₀ S α₀ β L₁ L₂ hL₁ hL₂ f₁ hf₁).2.1 _ _ hF).1
      have hFT : F = T (extFun α₀ β (tensCol ΨA a)) := hF.2.2.2.2.2 T hT
      rw [GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' V₀ A L S o ζ α α₀ β hsum, hΨAe] at hFT
      have := GlobalTheory.BoxSlice.isThetaFunO_slice_left o hFth y
      rw [hFT] at this
      exact this
    have hvac : Vac ψ A S LA LS (· = p.v) g := ⟨htheta, hlat⟩

    have hslice : (fun u => Ξ ((o.resS S).symm (u, y))) = T₁ (extFun α β Ψ) := by
      funext u
      rw [ExtZero.restrModel_apply, hΞT, GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' V₀ A L S o ζ α α₀ β hsum]
      rfl
    refine ⟨g, ?_⟩
    obtain ⟨f, hf, -⟩ := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hψ A S α β LA LS hLA hLS g hvac).1 Ψ hΨSB
    have hfT₁ : f = T₁ (extFun α β Ψ) := hf.2.2.2.2.2 T₁ hmodel
    rw [hslice, ← hfT₁]
    exact hf

end GlobalTheory.LastSrcSlice
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameGlInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mat_int {p : SplitPt D k} {S : HSp D} {L : Lat S} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank)
    (β : Frame p S (Fin S.rank)) {Λ : Submodule 𝒪[k] (Fin S.rank → k)} (h : β.IsLat L Λ) (g : GL (Fin S.rank) k)
    (hg : g • Λ = Λ) (r s : Fin S.rank) : (β.b * g.val * β.b') r s ∈ 𝒪[k] := by
  have hmem : ∀ x, x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := fun x => by
    rw [h x, GlobalTheory.SeeSaw.StdOff.mem_latV_int hL]
    exact forall_congr' fun r =>
      ((p.int_iff _).trans (and_iff_right (GlobalTheory.SeeSaw.StdOff.sec_mem_idAt p _)).symm).symm
  have h1 : β.b' *ᵥ Pi.single s 1 ∈ Λ := (hmem _).2 fun r => by
    rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have h2 : g • (β.b' *ᵥ Pi.single s 1) ∈ Λ := hg ▸ Submodule.smul_mem_pointwise_smul _ _ _ h1
  have h3 := (hmem _).1 h2 r
  convert h3 using 1
  rw [show g • (β.b' *ᵥ Pi.single s 1) = g.val *ᵥ (β.b' *ᵥ Pi.single s 1) from rfl, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

theorem finM_mul (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    GlobalTheory.AdForm.finM V hn (g * h) = GlobalTheory.AdForm.finM V hn g * GlobalTheory.AdForm.finM V hn h := by
  simp [GlobalTheory.AdForm.finM, Formalism.L2.Theta.mt, Matrix.map_mul, Matrix.submatrix_mul_equiv]

theorem prF_finM (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D)
    {n : ℕ} (hn : V.rank = n) (g : GA D V) (r s : Fin n) :
    q.prF he (GlobalTheory.AdForm.finM V hn g r s) = (Formalism.L2.Theta.mt V g).map q.pr ((finCongr hn).symm r) ((finCongr hn).symm s) := by
  simp [GlobalTheory.AdForm.finM, Matrix.reindex_apply, SplitPt.prF_toEAf]

theorem finM_one (V : HSp D) {n : ℕ} (hn : V.rank = n) : GlobalTheory.AdForm.finM V hn 1 = 1 := by
  simp [GlobalTheory.AdForm.finM, Formalism.L2.Theta.mt]

end GlobalTheory.FrameGlInt

namespace GlobalTheory.FrameGlInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]



theorem exists_int (p : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt p.e PP) (S : HSp D)
    {n : ℕ} (hn : S.rank = n) (hgram : S.gram.reindex (finCongr hn) (finCongr hn) = 1) {L : Lat S}
    (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank) (β : Frame p S (Fin S.rank)) {Λ : Submodule 𝒪[k] (Fin S.rank → k)}
    (hlat : β.IsLat L Λ) (g : GL (Fin S.rank) k) (hgl : g • Λ = Λ) :
    ∃ δ : GL (Fin n) (GlobalTheory.AdForm.EF D), δ.1 = GlobalTheory.AdForm.finM S hn (β.gl g) ∧
      δ ∈ Formalism.UG.UPts (sigD D) (1 : Matrix (Fin n) (Fin n) D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
      (∀ r r', δ.1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      (∀ r r', (δ⁻¹).1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) := by
  obtain ⟨⟨x, hx0⟩, hx⟩ := GlobalTheory.AdForm.RdVal.finM_mem S hn _ hgram.symm (β.gl g)
  refine ⟨x, hx, hx0, ?_⟩
  have hgl' : g⁻¹ • Λ = Λ := by
    conv_lhs => rw [← hgl]
    exact inv_smul_smul g _
  have hcomp : ∀ h : GL (Fin S.rank) k, h • Λ = Λ → ∀ r s,
      toEAf D p.e * GlobalTheory.AdForm.finM S hn (β.gl h) r s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro h hh r s
    rw [← p.prF_mem_iff he]
    have e1 := prF_finM p he S hn (β.gl h) r s
    rw [β.gl_mat h] at e1
    exact e1 ▸ mat_int hL β hlat h hh _ _
  set σ := Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) with hσ

  have hu0 : Formalism.UG.cT σ x.1 * ((1 : Matrix (Fin n) (Fin n) D.host.E).map
      (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) * x.1 =
      (1 : Matrix (Fin n) (Fin n) D.host.E).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := hx0
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at hu0
  have hinvM : (x⁻¹).1 = Formalism.UG.cT σ x.1 := by
    calc (x⁻¹).1 = (Formalism.UG.cT σ x.1 * x.1) * (x⁻¹).1 := by rw [hu0, one_mul]
      _ = _ := by rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

  have hxi : (x⁻¹).1 = GlobalTheory.AdForm.finM S hn (β.gl g⁻¹) := by
    have h1 : x.1 * GlobalTheory.AdForm.finM S hn (β.gl g⁻¹) = 1 := by
      rw [hx, ← finM_mul, ← map_mul, mul_inv_cancel, map_one, finM_one]
    calc (x⁻¹).1 = (x⁻¹).1 * (x.1 * GlobalTheory.AdForm.finM S hn (β.gl g⁻¹)) := by rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  obtain ⟨hf, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D p.e PP he
  have hσmem : ∀ y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, σ y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun y hy => GlobalTheory.Mem.Col2.sigR_mem_rInt D.sp.cm hy
  have hσσ : ∀ y, σ (σ y) = y := Formalism.L2.DIV.sigR_sigR D.sp.cm
  have hcA : toEAf D (cA D p.e) = σ (toEAf D p.e) := GlobalTheory.AdForm.RdVal.toEAf_sig p.e
  have hint : ∀ r r', x.1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro r r'
    have hs := congrArg (toEAf D) (β.gl_supp g ((finCongr hn).symm r) ((finCongr hn).symm r'))
    have hxr : x.1 r r' = toEAf D (Formalism.L2.Theta.mt S (β.gl g) ((finCongr hn).symm r) ((finCongr hn).symm r')) := by
      rw [hx]; rfl
    have hcm : toEAf D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((finCongr hn).symm r) ((finCongr hn).symm r')) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [Matrix.one_apply]; split_ifs
      · rw [RingHom.map_one]; exact one_mem _
      · rw [RingHom.map_zero]; exact zero_mem _
    rw [Matrix.sub_apply, RingHom.map_mul, RingHom.map_sub, RingHom.map_add (f := _), hcA, ← hxr] at hs
    have hdec : x.1 r r' = toEAf D p.e * x.1 r r' + σ (toEAf D p.e * (x⁻¹).1 r' r) +
        (1 - toEAf D p.e - σ (toEAf D p.e)) *
          toEAf D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((finCongr hn).symm r) ((finCongr hn).symm r')) := by
      have e2 : σ (toEAf D p.e * (x⁻¹).1 r' r) = σ (toEAf D p.e) * x.1 r r' := by
        rw [hinvM, map_mul]
        show σ (toEAf D p.e) * σ (σ (x.1 r r')) = _
        rw [hσσ]
      rw [e2]
      linear_combination (-1 : GlobalTheory.AdForm.EF D) * hs
    rw [hdec]
    refine add_mem (add_mem ?_ ?_) (mul_mem (sub_mem (sub_mem (one_mem _) hf) (hσmem _ hf)) hcm)
    · exact hx ▸ hcomp g hgl r r'
    · exact hσmem _ (hxi ▸ hcomp g⁻¹ hgl' r' r)
  exact ⟨hint, fun r r' => by
    rw [hinvM]
    exact hσmem _ (hint r' r)⟩

end GlobalTheory.FrameGlInt

theorem GlobalTheory.AdForm.frameGl_int : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (s : 𝓀[k]ˣ), g • Q j i = s • Q j i →
    ∃ δ : TC.GA B (B.R.N j), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) ∧ δ ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N j) ∧
      (∀ r r', δ.1 r r' ∈ Formalism.L2.DIV.RInt B.host.F B.host.E) ∧ (∀ r r', (δ⁻¹).1 r r' ∈ Formalism.L2.DIV.RInt B.host.F B.host.E) := by
  intro B X I hOk hPins l Z u a k _ _ _ _ ι p β Q L hStd j hj i v hIdem g s hgs
  have hg1 : gramN (I.rec7 l Z) j hj = 1 := ((TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 j hj).1
  obtain ⟨-, hT⟩ := hStd
  obtain ⟨hL, hT'⟩ := hT j hj
  obtain ⟨hlat, -⟩ := hT' i
  have hgl : g • (Q j i).lat = (Q j i).lat := by
    have := congrArg GlobalTheory.LatPair.Pair.lat hgs
    rwa [GlobalTheory.LatPair.Pair.smul_lat, GlobalTheory.LatPair.Pair.dia_lat] at this
  obtain ⟨δ, h1, h2, h3, h4⟩ := GlobalTheory.FrameGlInt.exists_int (p i) hIdem _ (rankN (I.rec7 l Z) j hj) hg1 hL (β j i) hlat g hgl
  exact ⟨δ, h1, h2, h3, h4⟩

end
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal.Inj

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem exists_fin {D : D7} (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) :
    ∃ g' : GA D V, g' ∈ GfC V ∧ finHom V g' = finHom V g ∧
      ∃ y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        y ∈ Formalism.UG.UPts D.sp.cm.sig (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
        ∀ i j, (Formalism.UG.bc (swapAE D) (finHom V g')).1 i j = y.1 (finCongr hn i) (finCongr hn j) := by
  subst hn
  let z := (GlobalTheory.FinPartIso.finEquiv D.sp.cm.sig V.gram).symm (GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram g)
  have hz : GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram z.1 = GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram g :=
    (GlobalTheory.FinPartIso.finEquiv D.sp.cm.sig V.gram).apply_symm_apply _
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D V _ rfl
  refine ⟨z.1, z.2, congrArg Subtype.val hz, (e ⟨z.1, z.2⟩).1, (e ⟨z.1, z.2⟩).2, fun i j => ?_⟩
  rw [he]
  rfl

theorem eq_zero_of_models {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (h : R.models_jX) (t : T) (x : A.fam.amb.FR t)
    (hx : ∀ g, (R.HX t).e (R.jX t x) ((finHom D.sp.X').rangeRestrict g) = 0) : x = 0 := by
  have h1 : R.B.jR t x = 0 := by
    funext k
    obtain ⟨g, hg⟩ := (finHom D.sp.X').rangeRestrict_surjective k
    exact (congrFun (h t x) k).symm.trans ((congrArg ((R.HX t).e (R.jX t x)) hg.symm).trans (hx g))
  have h2 : Function.Injective (R.B.jR t) := GlobalTheory.PresBasic.extL_injective (R.B.R t).pres
  exact (injective_iff_map_eq_zero (R.B.jR t)).1 h2 x h1

theorem eq_zero_of_isRes {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : Col2.TC B X) (a : I.ι) (φ : Frm I a) τ (e : I.tup a = τ)
    (ok : (Formalism.L2.Col.mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel τ).Ok)
    (h : IsRes φ (0 : ((Formalism.L2.Col.mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel τ).toCSD ok).Forms)) : φ = 0 := by
  subst e
  obtain ⟨ok', h⟩ := h
  exact (LinearEquiv.map_eq_zero_iff _).1 (eq_of_heq h)



theorem eq_zero_twArgs (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) :
    ∀ (s : a.x.T) (φ : Frm w.I (a.x.Y.tup s)), IsRes φ (0 : a.x.A3.A.fam.amb.FR s) → φ = 0 := by
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tup = t.r.Y.tup := eq_of_heq htup
  intro s φ h
  have e : w.I.tup (Y.tup s) = s.1 :=
    (congrArg w.I.tup ((congrFun hT' s).trans (t.r.tup_ix s))).trans (R3.tup_ixOf w.I s)
  exact eq_zero_of_isRes w.I _ φ s.1 e _ h

theorem exists_hasMat {D : D7} (gP : Formalism.L2.Forms.gramP D = 1) (g : GA D D.sp.X') :
    ∃ g' y, GlobalTheory.Core.Rk.Top.HasMat g' y ∧ y ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N D.R.m - 1) ∧
      (finHom D.sp.X').rangeRestrict g = (finHom D.sp.X').rangeRestrict g' := by
  obtain ⟨g', h1, h2, y, h3, h4⟩ := exists_fin _ _ (Formalism.L2.Forms.rankP D) g
  have h6 : y ∈ Formalism.UG.UPts _ (Formalism.L2.Forms.gramP D) _ := h3
  rw [gP] at h6
  exact ⟨g', y, ⟨h1, h4⟩, h6, Subtype.ext h2.symm⟩

theorem eq_zero_of_hasMat {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (h : R.models_jX) (gP : Formalism.L2.Forms.gramP D = 1)
    (t : T) (x : A.fam.amb.FR t)
    (hx : ∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → y ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N D.R.m - 1) →
      (R.HX t).e (R.jX t x) ((finHom D.sp.X').rangeRestrict g) = 0) : x = 0 := by
  refine eq_zero_of_models R h t x fun g => ?_
  exact (exists_hasMat gP g).elim fun g' h1 => h1.elim fun y h2 =>
    (congrArg ((R.HX t).e (R.jX t x)) h2.2.2).trans (hx g' y h2.1 h2.2.1)


end GlobalTheory.TopVal.Inj
end
