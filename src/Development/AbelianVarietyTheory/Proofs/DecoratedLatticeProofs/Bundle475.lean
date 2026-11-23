module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle426
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle448
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle332
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle460
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle360
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle445
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle462
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle396
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle454
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle387
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle456
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle139
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle190
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mem_latV_iff (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) (w : Fin S.rank → k) :
    (fun i => q.sec (w i)) ∈ latV S L (· = q.v) ↔ ∀ i, w i ∈ 𝒪[k] := by
  classical
  have hmem : ∀ x : Fin S.rank → D.host.E, x ∈ L ↔ ∀ i, IsIntegral ℤ (x i) := fun x => by
    rw [← SetLike.mem_coe, hL]; rfl
  have hsingle : ∀ i : Fin S.rank, (Pi.single i (1 : D.host.E) : Fin S.rank → D.host.E) ∈ L := fun i =>
    (hmem _).2 fun j => by
      by_cases h : j = i
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_apply, h] using isIntegral_zero
  let G : Finset (Fin S.rank → D.host.E) := Finset.univ.image fun i => Pi.single i 1
  have hGL : ∀ x ∈ (G : Set (Fin S.rank → D.host.E)), x ∈ L := by
    intro x hx
    simp only [G, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hsingle i
  have hG : Submodule.span (𝓞 D.host.E) (G : Set (Fin S.rank → D.host.E)) = L := by
    apply le_antisymm
    · rw [Submodule.span_le]; exact hGL
    · intro x hx
      have hi := (hmem x).1 hx
      have e : x = ∑ i, (⟨x i, hi i⟩ : 𝓞 D.host.E) • (Pi.single i 1 : Fin S.rank → D.host.E) := by
        funext j
        rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
        simp [Algebra.smul_def]
      rw [e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp [G]))
  constructor
  · intro h
    have h1 := FullLatFrame.pr_mem_span q G hG h
    simp only [q.pr_sec] at h1
    have h2 : ∀ z ∈ Submodule.span 𝒪[k] (FullLatFrame.aux₃ q '' (G : Set (Fin S.rank → D.host.E))), ∀ i, z i ∈ 𝒪[k] := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        intro i
        exact FullLatFrame.pr_int_mem q ⟨x i, (hmem x).1 (hGL x hx) i⟩
      | zero => intro i; exact zero_mem _
      | add x y _ _ hx hy => intro i; exact add_mem (hx i) (hy i)
      | smul a x _ hx => intro i; exact mul_mem a.2 (hx i)
    exact h2 _ h1
  · intro h
    have e : w = ∑ i, (⟨w i, h i⟩ : 𝒪[k]) • FullLatFrame.aux₃ q (S := S) (Pi.single i 1) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [FullLatFrame.aux₃, Pi.single_apply, Ne.symm hb]) (by simp)]
      simp [FullLatFrame.aux₃]
      change _ = w j * 1
      rw [mul_one]
    rw [← FullLatFrame.mem_latW, e]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [FullLatFrame.mem_latW]
    exact GlobalTheory.FinPl.FrameLat.sec_inc_mem (hsingle i)

theorem intIn_stdFr (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) {Y : Type} [Fintype Y] [DecidableEq Y]
    (e : Y ≃ Fin S.rank) : IntIn q S (stdFr k e) L := by
  intro y
  rw [sec_mem_latV_iff q S L hL]
  have h : (stdFr k e).β *ᵥ y = y ∘ e.symm := by
    change (1 : Matrix (Fin S.rank) (Fin S.rank) k).submatrix id e *ᵥ y = _
    have := Matrix.submatrix_mulVec_equiv (1 : Matrix (Fin S.rank) (Fin S.rank) k) y id e
    simpa [Function.comp_def] using this
  rw [h]
  exact ⟨fun h i => h _, fun h a => by simpa using h (e a)⟩

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def diagFr {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (e : Y ≃ Fin N) (d : Y → k) (hd : ∀ y, d y ≠ 0) :
    GlobalTheory.LocMod.Frame k N Y where
  β := (stdFr k e).β * Matrix.diagonal d
  γ := Matrix.diagonal (fun y => (d y)⁻¹) * (stdFr k e).γ
  βγ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal d), Matrix.diagonal_mul_diagonal,
      show (fun y => d y * (d y)⁻¹) = fun _ => (1 : k) from funext fun y => mul_inv_cancel₀ (hd y),
      Matrix.diagonal_one, Matrix.one_mul, (stdFr k e).βγ]
  γβ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (stdFr k e).γ, (stdFr k e).γβ, Matrix.one_mul, Matrix.diagonal_mul_diagonal,
      show (fun y => (d y)⁻¹ * d y) = fun _ => (1 : k) from funext fun y => inv_mul_cancel₀ (hd y), Matrix.diagonal_one]

theorem intIn_diagFr (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) {Y : Type} [Fintype Y] [DecidableEq Y]
    (e : Y ≃ Fin S.rank) (d : Y → k) (hd : ∀ y, d y ≠ 0) (hv : ∀ y, valuation k (d y) = 1) :
    IntIn q S (diagFr e d hd) L := by
  intro y
  have h1 := intIn_stdFr q S L hL e (fun a => d a * y a)
  have h2 : (diagFr e d hd).β *ᵥ y = (stdFr k e).β *ᵥ fun a => d a * y a := by
    change ((stdFr k e).β * Matrix.diagonal d) *ᵥ y = _
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext a
    exact Matrix.mulVec_diagonal _ _ _
  rw [h2, ← h1]
  refine forall_congr' fun a => ?_
  change valuation k (y a) ≤ 1 ↔ valuation k (d a * y a) ≤ 1
  rw [map_mul, hv, one_mul]

variable {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre}

theorem oTop_iA {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) (n : ℕ) (h : n = (I.rec7 l Z).R.m) :
    ∀ b a, (oTop l Z hI n h).iA b a = if (a : ℕ) = (b : ℕ) then 1 else 0 := by
  subst h; intro b a; rfl

theorem oTop_iB {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) (n : ℕ) (h : n = (I.rec7 l Z).R.m) :
    ∀ b a, (oTop l Z hI n h).iB b a = if (I.rec7 l Z).sp.X'.rank = (b : ℕ) then 1 else 0 := by
  subst h; intro b a; rfl

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames

theorem entry_inl {E k : Type} [Field E] [Field k] (f : E → k) (hf0 : f 0 = 0) (hf1 : f 1 = 1) {n N : ℕ} {Y : Type} [Fintype Y]
    [DecidableEq Y] (eT : Y ≃ Fin n) (iA : Matrix (Fin N) (Fin n) E) (hA : ∀ b a, iA b a = if (a : ℕ) = (b : ℕ) then 1 else 0)
    (r : Fin N) (c : Y) (m : Fin N) (hm : (m : ℕ) = eT c) :
    (1 : Matrix (Fin N) (Fin N) k) r m = (iA.map f * (1 : Matrix (Fin n) (Fin n) k).submatrix id eT) r c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (eT c)
    (fun b _ hb => by rw [Matrix.submatrix_apply, id, Matrix.one_apply_ne hb, mul_zero]) (by simp)]
  rw [Matrix.submatrix_apply, id, Matrix.one_apply_eq, mul_one, Matrix.map_apply, hA, Matrix.one_apply]
  by_cases h : (eT c : ℕ) = r
  · rw [if_pos h, hf1, if_pos (Fin.ext (h.symm.trans hm.symm))]
  · rw [if_neg h, hf0, if_neg (fun h' => h (hm.symm.trans (congrArg Fin.val h'.symm)))]

theorem entry_inr {E k : Type} [Field E] [Field k] (f : E → k) (hf0 : f 0 = 0) (hf1 : f 1 = 1) {n N : ℕ}
    (iB : Matrix (Fin N) (Fin 1) E) (hB : ∀ b a, iB b a = if n = (b : ℕ) then 1 else 0) (z : Fin 1 → E) (x : E)
    (hz : ∀ i, z i = x) (r : Fin N) (m : Fin N) (hm : (m : ℕ) = n) :
    (1 : Matrix (Fin N) (Fin N) k) r m * f x = (iB.map f *ᵥ fun i => f (z i)) r := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.map_apply, hB, hz, Matrix.one_apply]
  by_cases h : n = (r : ℕ)
  · rw [if_pos h, hf1, if_pos (Fin.ext (h.symm.trans hm.symm))]
  · rw [if_neg h, hf0, if_neg (fun h' => h (hm.symm.trans (congrArg Fin.val h'.symm)))]

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames


end GlobalTheory.XGeoStd.Frames
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_realThetaIntertwiner_exchangedPair : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (k : Fin D.R.m) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), S = parB (Ptw D) k → S' = parB (Ptw D) (k + 1) → IsInfFam θ → ChainPar D k → ∃ It : PolF D V.rank W.rank →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ (ω : (GA D W × GA D V →* Module.End ℂ (WO W V → ℂ))) (f : WO W V → ℂ), IsWeilExp ψ W V (expT D k) (expS D k) ω → IsVacVec ψ θ M' M f → IsItW θ M' M ω (ptOf ψ θ M' M f) It := by
  first | exact @GlobalTheory.Chain.RealIt.itPairUp | exact GlobalTheory.Chain.RealIt.itPairUp | (intros; apply GlobalTheory.Chain.RealIt.itPairUp <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.BasicId

open Filter Set GlobalTheory.Eis

theorem measurable_tsum_of_summable' {X I : Type} [MeasurableSpace X] [Countable I]
    (F : I → X → ℂ) (hF : ∀ i, Measurable (F i)) (hs : ∀ x, Summable fun i => F i x) :
    Measurable fun x => ∑' i, F i x :=
  measurable_of_tendsto_metrizable' (atTop : Filter (Finset I))
    (f := fun s x => ∑ i ∈ s, F i x) (fun s => Finset.measurable_sum s fun i _ => hF i)
    (tendsto_pi_nhds.2 fun x => (hs x).hasSum)

theorem out_mul_inv_mem {D : D7} (V : HSp D) (x : GQ (dblSp V)) :
    (((mk ((siegel V).subgroupOf (GQ (dblSp V))) x).out : GQ (dblSp V)) : GA D (dblSp V)) *
      ((x : GA D (dblSp V)))⁻¹ ∈ siegel V := by
  obtain ⟨γ, e⟩ := mk_eq_iff.1 (Quotient.out_eq (mk ((siegel V).subgroupOf (GQ (dblSp V))) x))
  have e' := congrArg (fun z : GQ (dblSp V) => (z : GA D (dblSp V))) e
  simp only [Subgroup.coe_mul] at e'
  rw [← e', mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  exact inv_mem (Subgroup.mem_subgroupOf.1 γ.2)

theorem basicIdentity_unfold : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → IsCuspFun V f₁ → GlobalTheory.Eis.BasicIdentity V μ m φ f₁ f₂ := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂ hcusp
  haveI := hm
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have hL : LeftInv (siegelQ V) φ := leftInv_of_mem hμ hφ
  have hφc : Continuous φ := hφ.2.1

  have hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D V (frameLat V) a (GlobalTheory.Core.Rk.AbsConv.isSelfDualC_frameLat V) ha
  have hS : SphConv V a := GlobalTheory.Eis.sphConv D V a hI
  have hσ : (V.rank : ℝ) / 2 < ((s.re : ℂ)).re := by simpa using hs
  have hconvS : ∀ g, EisConv V (sph V a (s.re : ℂ)) g := fun g => (((sphConv_iff hI).1 hS).1 _ hσ).2 g
  have h2 : ∀ g, sph V a (s.re : ℂ) g = (((hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) : ℝ) : ℂ) := fun g => by
    rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]; push_cast; rfl
  have hr0 : ∀ g, 0 ≤ (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g =>
    Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hn : ∀ g, ‖sph V a (s.re : ℂ) g‖ = (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g => by
    rw [h2, Complex.norm_real, Real.norm_of_nonneg (hr0 g)]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := by
    haveI := t2Space_adeleRing' (F := D.host.F)
    exact hI.exists_norm_le continuous_absE (isCompact_Khat V a) hφ
  have hsum : ∀ y, Summable fun q : SiegelCosets V => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * y) :=
    fun y => Summable.of_norm (((hconvS y).of_norm_le (C := max C 0) fun g =>
      (hC g).trans (by rw [hn]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hr0 g))) : EisConv V φ y)

  set P : Set (SiegelCosets V) := {q | ∃ δ ∈ GQ V, ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V}
    with hP
  let e0 : GQ V → P := fun δ => ⟨mk _ ⟨io V ((δ : GA D V), 1), io_mem_GQ V δ.2 (one_mem _)⟩,
    ⟨δ, δ.2, out_mul_inv_mem V ⟨io V ((δ : GA D V), 1), io_mem_GQ V δ.2 (one_mem _)⟩⟩⟩
  have hbij : Function.Bijective e0 := by
    refine ⟨fun δ δ' h => injective_mk_io (congrArg Subtype.val h), fun q => ?_⟩
    obtain ⟨δ, hδ, hq⟩ := q.2
    refine ⟨⟨δ, hδ⟩, Subtype.ext ?_⟩
    have hm' : (q.1.out : GQ (dblSp V)) * (⟨io V (δ, 1), io_mem_GQ V hδ (one_mem _)⟩ : GQ (dblSp V))⁻¹ ∈
        (siegel V).subgroupOf (GQ (dblSp V)) := Subgroup.mem_subgroupOf.2 (by simpa using hq)
    exact (mk_eq_iff.2 ⟨⟨_, hm'⟩, by simp⟩).trans q.1.out_eq
  have hterm : ∀ (δ : GQ V) y, φ ((((e0 δ).1.out : GQ (dblSp V)) : GA D (dblSp V)) * y) = φ (io V ((δ : GA D V), 1) * y) :=
    fun δ y => term_mk hL y ⟨io V ((δ : GA D V), 1), io_mem_GQ V δ.2 (one_mem _)⟩
  obtain ⟨Eo, hEo⟩ : ∃ Eo : GA D (dblSp V) → ℂ, Eo = fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y) := ⟨_, rfl⟩
  obtain ⟨En, hEn⟩ : ∃ En : GA D (dblSp V) → ℂ, En = fun y => ∑' q : {q : GlobalTheory.Eis.SiegelCosets V // ¬ ∃ δ ∈ GQ V,
      ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V},
      φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y) := ⟨_, rfl⟩
  have hEoP : ∀ y, Eo y = ∑' q : P, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y) := fun y => by
    rw [hEo, ← (Equiv.ofBijective e0 hbij).tsum_eq]
    exact tsum_congr fun δ => (hterm δ y).symm
  have hsumO : ∀ y, Summable fun δ : GQ V => φ (io V ((δ : GA D V), 1) * y) := fun y => by
    have := ((Equiv.ofBijective e0 hbij).summable_iff (f := fun q : P =>
      φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y))).2 ((hsum y).subtype (fun q => q ∈ P))
    exact this.congr fun δ => hterm δ y
  have hsplit : ∀ y, eis V φ y = Eo y + En y := fun y => by
    rw [hEoP, hEn]
    exact ((hsum y).tsum_subtype_add_tsum_subtype_compl P).symm

  have hEoInv : ∀ γ ∈ (GQ V).prod (GQ V), ∀ y, Eo (io V γ * y) = Eo y := by
    rintro ⟨γ₁, γ₂⟩ ⟨h1, h2⟩ y
    let e : GQ V ≃ GQ V := (Equiv.mulLeft (⟨γ₂, h2⟩ : GQ V)⁻¹).trans (Equiv.mulRight ⟨γ₁, h1⟩)
    rw [hEo]
    show ∑' δ : GQ V, φ (io V ((δ : GA D V), 1) * (io V (γ₁, γ₂) * y)) = ∑' δ : GQ V, φ (io V ((δ : GA D V), 1) * y)
    rw [← e.tsum_eq (fun δ : GQ V => φ (io V ((δ : GA D V), 1) * y))]
    refine tsum_congr fun δ => ?_
    have hd : io V ((δ : GA D V), 1) * (io V (γ₁, γ₂) * y) = io V (γ₂, γ₂) * (io V (((e δ : GQ V) : GA D V), 1) * y) := by
      rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
      congr 2
      refine Prod.ext ?_ ?_
      · simp [e, mul_assoc]
      · simp
    rw [hd, hL _ ⟨(io_mem_siegel V).2 rfl, io_mem_GQ V h2 h2⟩]
  have hi : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ Eo f₁ f₂) := fun γ hγ g => by
    simp only [dblIntegrand, map_mul (io V), hEoInv γ hγ, Prod.fst_mul, Prod.snd_mul, h₁.1 _ hγ.1, h₂.1 _ hγ.2,
      map_mul (detA V), map_mul μ, apply_detA hμ hγ.2, one_mul]

  have hEom : Measurable Eo := by
    rw [hEo]
    exact measurable_tsum_of_summable' (fun δ : GQ V => fun y => φ (io V ((δ : GA D V), 1) * y))
      (fun δ => (hφc.comp (continuous_const.mul continuous_id)).measurable) hsumO
  have hDm : Measurable (dblIntegrand V μ Eo f₁ f₂) := by
    have e : dblIntegrand V μ Eo f₁ f₂ = fun g => Eo (io V g) * dblIntegrand V μ (fun _ => 1) f₁ f₂ g :=
      funext fun g => by simp only [dblIntegrand]; ring
    rw [e]
    exact (hEom.comp (continuous_io V).measurable).mul
      (continuous_dblIntegrand hμ continuous_const h₁.continuous h₂.continuous).measurable

  have h𝓕 := isFundamentalDomain_stdDom (GQ V) m
  have habs := GlobalTheory.Core.Rk.AbsConv.absConv_unfolded D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  have hfin := habs.1 _ h𝓕
  have hmeasq : ∀ q : SiegelCosets V, AEMeasurable (fun x =>
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ)
      ((m.prod m).restrict (stdDom (GQ V) ×ˢ stdDom (GQ V))) := fun q =>
    (continuous_dblIntegrand hμ (hφc.comp (continuous_const.mul continuous_id)) h₁.continuous
      h₂.continuous).measurable.enorm.aemeasurable
  have hpt : ∀ x, ‖dblIntegrand V μ Eo f₁ f₂ x‖ₑ ≤ ∑' q : SiegelCosets V,
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ := fun x => by
    simp only [GlobalTheory.Core.Rk.AbsConv.enorm_dblIntegrand]
    rw [ENNReal.tsum_mul_right]
    gcongr ?_ * _
    rw [hEoP]
    exact enorm_tsum_le_tsum_enorm.trans (tsum_comp_le_tsum_of_injective (f := fun q : P => q.1) Subtype.val_injective
      (fun q : SiegelCosets V => ‖φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * io V x)‖ₑ))
  have hOn : IntegrableOn (dblIntegrand V μ Eo f₁ f₂) (stdDom (GQ V) ×ˢ stdDom (GQ V)) (m.prod m) := by
    refine ⟨hDm.aestronglyMeasurable, ?_⟩
    show ∫⁻ x in stdDom (GQ V) ×ˢ stdDom (GQ V), ‖dblIntegrand V μ Eo f₁ f₂ x‖ₑ ∂m.prod m < ⊤
    calc _ ≤ ∫⁻ x in stdDom (GQ V) ×ˢ stdDom (GQ V), ∑' q : SiegelCosets V,
          ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m :=
          lintegral_mono hpt
      _ = _ := lintegral_tsum hmeasq
      _ < ⊤ := hfin.lt_top
  have hEoC : DblConv V μ m Eo f₁ f₂ := (dblConv_iff hi hDm h𝓕).2 hOn

  have hQ : ∀ q, dblIntegrandQ V μ (eis V φ) f₁ f₂ q = dblIntegrandQ V μ Eo f₁ f₂ q + dblIntegrandQ V μ En f₁ f₂ q :=
    fun q => by simp only [dblIntegrandQ, dblIntegrand, hsplit]; ring
  have hEnI : Integrable (dblIntegrandQ V μ En f₁ f₂) ((autMeasure V m).prod (autMeasure V m)) :=
    (habs.2.2.sub hEoC.2).congr (Eventually.of_forall fun q => by simp only [Pi.sub_apply, hQ]; ring)
  have h6 := GlobalTheory.T.doubling_integral_negligible_orbits_eq_zero_cuspForm D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂ hcusp
  have h7 := GlobalTheory.T.doubling_open_orbit_unfolds_to_adelic_integral D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  rw [← hEn] at h6
  rw [← hEo] at h7
  refine ⟨habs.2, h7.1, ?_⟩
  show ∫ q, dblIntegrandQ V μ (eis V φ) f₁ f₂ q ∂(autMeasure V m).prod (autMeasure V m) = _
  rw [integral_congr_ae (Eventually.of_forall hQ), integral_add hEoC.2 hEnI, h7.2, h6, add_zero]

end GlobalTheory.Core.Rk.BasicId

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.VacAll

theorem vacT_twist {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {θ : InfFam (I.rec7 l Z)}
    {i : ℕ} {hi : i + 1 ≤ B.R.m} {c₀ : ℂ} {ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ} {μ₀ μ : (AE (I.rec7 l Z))ˣ →* Circle}
    {om₀ om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))}
    {vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ} (hv : IsThetaFunO ψ _ _ vac)
    (h0 : IsWeilDatumO ψ _ _ μ₀ μ₀ om₀) (h1 : IsWeilDatumO ψ _ _ μ μ om) (H : VacT I l Z θ i hi c₀ μ₀ om₀ vac) :
    VacT I l Z θ i hi c₀ μ om vac := by
  intro g hg h hh N N' hN hN' x y hx hy
  have e := GlobalTheory.WeilChange.weilData_differ_by_splitFac _ ψ _ _ μ₀ μ₀ μ μ om₀ om h0 h1 g h x y hx hy vac hv
  rw [e, xiS_smul, H g hg h hh N N' hN hN' x y hx hy]
  funext z
  have a1 : (μ₀ x : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have a2 : (μ₀ y : ℂ) ≠ 0 := Circle.coe_ne_zero _
  simp only [splitFacO, Circle.coe_mul, Circle.coe_inv]
  field_simp

end GlobalTheory.AdForm.VacAll

namespace GlobalTheory.AdForm.VacAll

theorem vacT_one : GlobalTheory.Published.StrongApproxSU → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ VacT I l Z θ i hi c₀ μ om vac := by
  intro hSA B X I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw
  obtain ⟨c₀, hc₀, h1⟩ := GlobalTheory.T.movedVacuum_at_identity_nonzero_constant I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw
  have hstd := (GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hP l Z ψ θ hψ hθ).1 i hi
  refine ⟨c₀, hc₀, vacT_iff.2 fun g hg h hh => ?_⟩
  obtain ⟨r, s, k, hr, hs, hk, hkL, rfl⟩ :=
    GlobalTheory.SplitDec.exists_rat_split_stab hSA _ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) hstd.gS g hg
  obtain ⟨r', s', k', hr', hs', hk', hkL', rfl⟩ :=
    GlobalTheory.SplitDec.exists_rat_split_stab hSA _ _ _ (rankN (I.rec7 l Z) (i + 1) hi) hstd.gT h hh
  have h2 := GlobalTheory.T.movedVacuum_invariant_under_stdLattice_stabilizers I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ 1 1 (one_mem _) (one_mem _) h1 k hk k' hk' hkL hkL'
  rw [one_mul, one_mul] at h2
  have h3 := GlobalTheory.AdForm.VacConst.split_induction _ (fun g => MoveT I l Z θ i hi c₀ μ om vac g k') (fun g hg H e he t ht => by
    have := GlobalTheory.T.movedVacuum_invariant_under_singleSplitPlace I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ g k' hg hk' H e he t 1 ht
      (GlobalTheory.AdForm.VacConst.suppAt_one e _)
    rwa [one_mul] at this) hs
  have hsk := mul_mem h3.1 hk
  have h4 := GlobalTheory.AdForm.VacConst.split_induction _ (fun h => MoveT I l Z θ i hi c₀ μ om vac (s * k) h) (fun h hh H e he t ht => by
    have := GlobalTheory.T.movedVacuum_invariant_under_singleSplitPlace I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ (s * k) h hsk hh H e he 1 t
      (GlobalTheory.AdForm.VacConst.suppAt_one e _) ht
    rwa [one_mul] at this) hs'
  have h5 := GlobalTheory.T.movedVacuum_invariant_rationalFiniteParts I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ _ _ hsk (mul_mem h4.1 hk')
    (h4.2 k' hk' (h3.2 k hk h2)) r r' hr hr'
  rw [mul_assoc, mul_assoc]
  exact h5

theorem vacT_all : GlobalTheory.Published.StrongApproxSU → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → VacT I l Z θ i hi c₀ μ om vac := by
  intro hSA B X I hI hP l Z ψ θ hψ hθ i hi vac hvac
  by_cases hex : ∃ (a : I.ι) (μ : (AE (I.rec7 l Z))ˣ →* Circle) (om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))),
      ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) ∧ IsWeilDatumO ψ _ _ μ μ om
  · obtain ⟨a₀, μ₀, om₀, hc0, hw0⟩ := hex
    obtain ⟨c₀, hc, H⟩ := vacT_one hSA I hI hP l Z ψ θ hψ hθ i hi vac hvac a₀ μ₀ om₀ hc0 hw0
    exact ⟨c₀, hc, fun a μ om _ hw => vacT_twist hvac.2.2 hw0 hw H⟩
  · exact ⟨1, one_ne_zero, fun a μ om hc hw => (hex ⟨a, μ, om, hc, hw⟩).elim⟩

end GlobalTheory.AdForm.VacAll
end
