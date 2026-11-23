module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle478
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueAdelicMatrixRealComponentsFinitePart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle238
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle291
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocCongr

variable {D : D7}

theorem mul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {z : Fin S.rank → AE D} (hz : z ∈ latV S L P) :
    (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) ∈ latA S L P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (0 : Fin S.rank → AE D) i) = 0 := by
      funext i; simp
    rw [this]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (z + z') i) =
        (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) + (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z' i) := by
      funext i; simp [mul_add]
    rw [this]; exact add_mem hz hz'
  | neg z _ hz =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (-z) i) =
        -(fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) := by
      funext i; simp
    rw [this]; exact neg_mem hz

theorem latA_le_of_latV_le {S : HSp D} {L L' : Lat S} {P : Pl D → Prop} (h : latV S L P ≤ latV S L' P) :
    latA S L P ≤ latA S L' P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩
  have hz : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) ∈ latV S L P :=
    AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
  have hm := mul_mem_latA (L := L') ha (h hz)
  have key : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
      fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [SetLike.mem_coe, key]
  exact hm

theorem latA_congr {S : HSp D} {L L' : Lat S} {P : Pl D → Prop} (h : latV S L P = latV S L' P) :
    latA S L P = latA S L' P :=
  le_antisymm (latA_le_of_latV_le h.le) (latA_le_of_latV_le h.ge)

theorem latO_congr {S T : HSp D} {LS LS' : Lat S} {LT LT' : Lat T} (hS : IsSelfDualC S LS) (hS' : IsSelfDualC S LS')
    (hT : IsSelfDualC T LT) (hT' : IsSelfDualC T LT') {P : Pl D → Prop} (eS : latV S LS P = latV S LS' P)
    (eT : latV T LT P = latV T LT' P) :
    latO S T (LS : Set _) (LT : Set _) P = latO S T (LS' : Set _) (LT' : Set _) P := by
  ext u
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS' LT' hS' hT', eS,
    latA_congr eT]

theorem monoAt_congr {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L L' : Lat S} {L₀ L₀' : Lat S₀} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (e₀ : latV S₀ L₀ (· = v) = latV S₀ L₀' (· = v)) (H : MonoAt d L L₀ v) :
    MonoAt d L' L₀' v := by
  unfold MonoAt at H ⊢
  rw [← e, ← e₀]
  exact H

theorem orthAt_congr {S A B : HSp D} {o : OrthDec S A B} {L L' : Lat S} {LA : Lat A} {LB : Lat B} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (H : OrthAt o L LA LB v) : OrthAt o L' LA LB v := by
  unfold OrthAt at H ⊢
  rw [← e]
  exact H

theorem primAt_congr {ψ : AddChar (AF D.host.F) ℂ} {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L L' : Lat S} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (H : PrimAt ψ d L v) : PrimAt ψ d L' v := by
  unfold PrimAt at H ⊢
  rw [← e]
  exact H

theorem colsAt_congr {V V₀ W : HSp D} {ρ : ℕ} {d : HypDec V V₀ ρ} {x : Mx D W.rank ρ} {LV LV' : Lat V} {LW LW' : Lat W}
    {v : Pl D} (e : latV V LV (· = v) = latV V LV' (· = v)) (eW : latV W LW (· = v) = latV W LW' (· = v))
    (H : ColsAt d x LV LW v) : ColsAt d x LV' LW' v := by
  unfold ColsAt at H ⊢
  rw [← e, ← latA_congr eW]
  exact H

end GlobalTheory.LocCongr

namespace GlobalTheory.LocCongr

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem goodBF_congr {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} {LV LV' : Lat B.V} {LV₀ LV₀' : Lat B.V₀} {LW LW' : Lat J.W}
    {LW₀ : Lat J.W₀} {v : Pl D} (sV : IsSelfDualC B.V LV') (sV₀ : IsSelfDualC B.V₀ LV₀') (sW : IsSelfDualC J.W LW')
    (eV : latV B.V LV (· = v) = latV B.V LV' (· = v)) (eV₀ : latV B.V₀ LV₀ (· = v) = latV B.V₀ LV₀' (· = v))
    (eW : latV J.W LW (· = v) = latV J.W LW' (· = v)) (H : GoodBF ψ B J LV LV₀ LW LW₀ v) :
    GoodBF ψ B J LV' LV₀' LW' LW₀ v :=
  { tame := H.tame
    sdV := sV
    sdV₀ := sV₀
    sdW := sW
    sdW₀ := H.sdW₀
    monoV := monoAt_congr eV eV₀ H.monoV
    monoW := monoAt_congr eW rfl H.monoW
    prim := primAt_congr eV H.prim
    cols := colsAt_congr eV eW H.cols
    last := by
      rw [← latO_congr H.sdV₀ sV₀ H.sdW sW eV₀ eW]
      exact H.last }

theorem adaptFB_congr {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} {LV LV' : Lat J.W} {LV₀ : Lat J.W₀}
    {LW LW' : Lat B.V} {LW₀ LW₀' : Lat B.V₀} {v : Pl D} (sV : IsSelfDualC J.W LV') (sW : IsSelfDualC B.V LW')
    (sW₀ : IsSelfDualC B.V₀ LW₀') (eV : latV J.W LV (· = v) = latV J.W LV' (· = v))
    (eW : latV B.V LW (· = v) = latV B.V LW' (· = v)) (eW₀ : latV B.V₀ LW₀ (· = v) = latV B.V₀ LW₀' (· = v))
    (H : AdaptFB ψ J B LV LV₀ LW LW₀ v) : AdaptFB ψ J B LV' LV₀ LW' LW₀' v :=
  { tame := H.tame
    sdV := sV
    sdV₀ := H.sdV₀
    sdW := sW
    sdW₀ := sW₀
    monoV := monoAt_congr eV rfl H.monoV
    monoW := monoAt_congr eW eW₀ H.monoW
    prim := primAt_congr eV H.prim
    cols := colsAt_congr eV eW H.cols }

theorem goodAt_splitAt_congr : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀)
    (x : Pl D), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) ∧ IsSelfDualC (c.V j) (N j) ∧
      latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) →
    (∀ j ρ h, IsSelfDualC _ (o.M j ρ h) ∧ IsSelfDualC _ (M j ρ h) ∧ latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) →
    (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧
      (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x) := by
  intro D c v k _ _ _ _ ι o N M x hN hM
  refine ⟨fun hg => ⟨fun j ρ h => ?_, fun j σ h => ?_⟩, fun hs => ⟨fun j ρ h => ?_, fun j h => ?_⟩⟩
  · have h0 := hN j (by omega)
    have h1 := hN (j + 1) (by omega)
    exact goodBF_congr h0.2.1 (hM j ρ h).2.1 h1.2.1 h0.2.2.symm (hM j ρ h).2.2.symm h1.2.2.symm (hg.bf j ρ h)
  · have h1 := hN (j + 1) (by omega)
    have h2 := hN (j + 1 + 1) (by omega)
    exact adaptFB_congr h1.2.1 h2.2.1 (hM (j + 1 + 1) σ (idx_step h)).2.1 h1.2.2.symm h2.2.2.symm
      (hM (j + 1 + 1) σ (idx_step h)).2.2.symm (hg.fb j σ h)
  · obtain ⟨LL, hLL, hO⟩ := hs.core j ρ h
    exact ⟨LL, hLL, orthAt_congr (hM j ρ h).2.2.symm hO⟩
  · obtain ⟨LL, LZ, h1, h2, h3, h4, h5⟩ := hs.top j h
    exact ⟨LL, LZ, h1, h2, orthAt_congr (hM j 0 h).2.2.symm h3, h4, h5⟩

end GlobalTheory.LocCongr
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepLev
variable {D : D7}

theorem vac_of_all {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} (P : Pl D → Prop)
    {f : WO S T → ℂ} (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT P f := by
  have hle : latO S T (↑LS) (↑LT) P ≤ latO S T (↑LS) (↑LT) (fun _ => True) := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, hr⟩
    exact ⟨α, hα, fun _ hv => (hv trivial).elim, hr⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hle hu), fun e he u hu => hf.2.2 e he u (hle hu)⟩

theorem hand_mul_right {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ) (φ : GA D B.A → ℂ) (k : GA D J.W) (a : ℂ) (ha : a ≠ 0)
    (h₁ : s₁.om (1, k) Φ₁ = a⁻¹ • Φ₁) (h₂ : s₂.om (k, 1) Φ₂ = a • Φ₂) (g : GA D B.V) (q₁ : GA D J.W) (q₂ : GA D B'.V) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g (q₁ * k) q₂ = Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g q₁ q₂ := by
  have e₁ : s₁.om (g, q₁ * k) Φ₁ = a⁻¹ • s₁.om (g, q₁) Φ₁ := by
    rw [show ((g, q₁ * k) : GA D B.V × GA D J.W) = (g, q₁) * (1, k) from by simp, map_mul, Module.End.mul_apply, h₁,
      LinearMap.map_smul]
  have e₂ : s₂.om (q₁ * k, q₂) Φ₂ = a • s₂.om (q₁, q₂) Φ₂ := by
    rw [show ((q₁ * k, q₂) : GA D J.W × GA D B'.V) = (q₁, q₂) * (k, 1) from by simp, map_mul, Module.End.mul_apply, h₂,
      LinearMap.map_smul]
  unfold Chain.hand
  rw [e₁, e₂, (GlobalTheory.HandHom.hand_hom D ψ σ B J B' s₁ s₂ l vL φ).1, inv_mul_cancel₀ ha, one_smul]

theorem integ_lev : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ k ∈ v.JG (j + 1), ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (q₁ * k) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ _ G x a _ f _ k hk q₁ q₂
  obtain ⟨b, hb, l₁, l₂, -⟩ := hF.lawG j (by omega) k hk
  have hd : ∀ p, p ∈ w.Q → ¬ p ∈ v.gP := fun p hp => Finset.disjoint_left.1 hF.disjG hp
  have v₁ := ((GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· ∈ w.Q) (· ∈ v.gP) hd).2.1 (w.eQ j) (hF.atQ j).1).2 _ _ _
    (vac_of_all (· ∈ v.gP) hΨ₁)
  have v₂ := ((GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· ∈ w.Q) (· ∈ v.gP) hd).2.1 (w.eQ (j + 1)) (hF.atQ (j + 1)).1).2 _ _ _
    (vac_of_all (· ∈ v.gP) hΨ₂)
  have m₁ := l₁ _ v₁
  have m₂ := l₂ (by omega) _ v₂
  rw [← (ht.sBF j (σ + 1) h).1] at m₁
  rw [← (ht.sFB j σ h).1] at m₂
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  exact congrArg (fun y => w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ y (rTrans q₂ f))
    (hand_mul_right (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ (φ α) k b hb m₁ m₂ g q₁ q₂)

end GlobalTheory.DStepLev
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepOff

theorem vac_off {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} {w : VTup t} (hc : c.Is) (hv : v.Is) (hf : VForm v w)
    (j : ℕ) (hj : j + 1 < D.R.m) (Ψ : WO (c.V j) (c.V (j + 1)) → ℂ)
    (hΨ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ) :
    Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ)) := by
  have h0 : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) Ψ := by
    have h1 := (GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (offP v w) (fun p => ¬ offP v w p)
      (fun p hp hn => hn hp)).2.2.2.2 (v.N j) (v.N (j + 1)) Ψ (hv.sd j (by omega)) (hv.sd (j + 1) hj)
    have h2 : (fun p => offP v w p ∨ ¬ offP v w p) = fun _ : Pl D => True := by
      funext p; exact propext ⟨fun _ => trivial, fun _ => em _⟩
    rw [h2] at h1
    exact (h1.1 hΨ).1
  have hQ := ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (· ∈ w.Q) (offP v w)
    (fun p hp hn => hn.2 hp)).2.1 (w.eQ j) (hf.atQ j).1).2 _ _ _ h0
  exact ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (· ∈ v.gP) (offP v w)
    (fun p hp hn => hn.1 hp)).2.1 (v.eG j) (hv.atG j).1).2 _ _ _ hQ

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ κ, InK (c.V (j + 1)) (v.N (j + 1)) (offP v w) κ → ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (q₁ * κ) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hf _ hoff _ _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ _ G x a _ f _ κ hκ q₁ q₂
  have k₁ := vac_off hc hv hf j (by omega) Ψ₁ h₁
  have k₂ := vac_off hc hv hf (j + 1) (by omega) Ψ₂ h₂
  obtain ⟨e₁, e₂⟩ := (hoff j σ h _ _ k₁ k₂).1 κ hκ
  have a₁ : ∀ g, t.om j (g, q₁ * κ) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) =
      t.om j (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) := by
    intro g
    have : ((g, q₁ * κ) : GA D (c.V j) × GA D (c.V (j + 1))) = (g, q₁) * (1, κ) := by simp
    rw [this, map_mul, Module.End.mul_apply, e₁]
  have a₂ : t.om (j + 1) (q₁ * κ, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) =
      t.om (j + 1) (q₁, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
    have : ((q₁ * κ, q₂) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) = (q₁, q₂) * (κ, 1) := by simp
    rw [this, map_mul, Module.End.mul_apply, e₂]
  rw [← (ht.sBF j (σ + 1) h).1] at a₁
  rw [← (ht.sFB j σ h).1] at a₂
  unfold integ Chain.hand
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  erw [a₁ g, a₂]

end GlobalTheory.DStepOff
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

noncomputable section

namespace GlobalTheory.DStepOffSnd

theorem vac_off {D : D7} {c : Comm D} (v : VCom c) {t : Tup c} (w : VTup t) (hc : c.Is) (hv : v.Is) (hw : VForm v w)
    (i : ℕ) (hi : i + 1 < D.R.m) (Ψ : WO (c.V i) (c.V (i + 1)) → ℂ)
    (hΨ : Vac c.ψ _ _ (v.N i) (v.N (i + 1)) (fun _ => True) Ψ) :
    Vac c.ψ _ _ (v.N i) (v.N (i + 1)) (offP v w) (comb c.ψ _ _ (v.eG i) (comb c.ψ _ _ (w.eQ i) Ψ)) := by
  have h0 : Vac c.ψ _ _ (v.N i) (v.N (i + 1)) (offP v w) Ψ := by
    have key := (GlobalTheory.DisjComb.main D c.ψ hc.std (c.V i) (c.V (i + 1)) (offP v w) (fun p => ¬ offP v w p)
      (fun p hp hn => hn hp)).2.2.2.2 (v.N i) (v.N (i + 1)) Ψ (hv.sd i (by omega)) (hv.sd (i + 1) hi)
    have e : (fun p => offP v w p ∨ ¬ offP v w p) = fun _ => True := by
      funext p; exact eq_true (Classical.em _)
    rw [e] at key
    exact (key.1 hΨ).1
  have h1 := ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V i) (c.V (i + 1)) (· ∈ w.Q) (offP v w)
      (fun p hp hn => hn.2 hp)).2.1 (w.eQ i) (hw.atQ i).1).2 _ _ _ h0
  exact ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V i) (c.V (i + 1)) (· ∈ v.gP) (offP v w)
      (fun p hp hn => hn.1 hp)).2.1 (v.eG i) (hv.atG i).1).2 _ _ _ h1

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ κ, InK (c.V (j + 1 + 1)) (v.N (j + 1 + 1)) (offP v w) κ → ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (q₂ * κ) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hw _ hoff _ _ _ _ j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ _ G x a ha f hf κ hκ q₁ q₂
  have hΦ₁ := vac_off v w hc hv hw j (by omega) Ψ₁ hΨ₁
  have hΦ₂ := vac_off v w hc hv hw (j + 1) (by omega) Ψ₂ hΨ₂
  have hfix := (hoff j σ h _ _ hΦ₁ hΦ₂).2.1 κ hκ
  have hom : t.om (j + 1) (q₁, q₂ * κ) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) =
      t.om (j + 1) (q₁, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
    have e : ((q₁, q₂ * κ) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) = (q₁, q₂) * (1, κ) := by simp
    rw [e, map_mul, Module.End.mul_apply, hfix]
  have hrow : rTrans κ f = f := by
    rw [hf]; exact (hw.row (j + 1 + 1) (by omega) G x a ha).2 κ hκ
  have hr : rTrans (q₂ * κ) f = rTrans q₂ f := by
    conv_rhs => rw [← hrow]
    funext g; simp only [rTrans, mul_assoc]
  have hs := (ht.sFB j σ h).1
  have hom' : (t.sFB j σ h).om (q₁, q₂ * κ) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) =
      (t.sFB j σ h).om (q₁, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
    rw [hs]; exact hom
  unfold integ Chain.hand
  rw [hr]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  exact congrArg (fun Z => w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
    (handFB (t.sFB j σ h) (c.vL j σ h) (handBF (t.sBF j (σ + 1) h) (c.lnk j σ h) (φ α) (flatBF (t.sBF j (σ + 1) h)
      ((t.sBF j (σ + 1) h).om (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))))) (flatFB (t.sFB j σ h) Z))
      (rTrans q₂ f)) hom'

end GlobalTheory.DStepOffSnd

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

namespace GlobalTheory.Mem.Col2.AdT

theorem exists_SBof_over_sub : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P : SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) := by
  intro B X I hOk _ l Z a v hv
  obtain ⟨P, hP, hPv⟩ := exists_SBof_over I hOk l Z a v hv
  exact ⟨⟨P, hP⟩, hPv⟩

end GlobalTheory.Mem.Col2.AdT
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.RealPar

variable {D : D7}




theorem finPart_cA_eq (z : AE D) :
    finPart D (cA D z) = Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, sigR, finPart]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]


open Classical in
theorem exists_real_point {θ : InfFam D} (hθ : IsInfFam θ) (τ₀ : D.what₂.Tau) (t : ℝ) :
    ∃ x : Ainf D.host.F, ∀ τ, θ τ (x ⊗ₜ[D.host.F] (1 : D.host.E)) = if τ = τ₀ then (t : ℂ) else 0 := by
  obtain ⟨w, ⟨hw, hf⟩, -⟩ := exists_unique_of_comp_finPart D θ hθ 1 1
    (fun τ => fun _ _ => if τ = τ₀ then (t : ℂ) else 0) 0
  set a : AE D := w 0 0 with ha
  have hcomp : ∀ τ, θ τ (infPart D a) = if τ = τ₀ then (t : ℂ) else 0 := fun τ => by
    have := congrFun (congrFun (hw τ) 0) 0
    simpa [compAt] using this
  have hfin : finPart D a = 0 := by
    have := congrFun (congrFun hf 0) 0
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.zero_apply, map_zero] at this
    exact this
  have hRC := RealComp.real_components D θ hθ
  have hc : cA D a = a := by
    have h0 : cA D a - a = 0 := by
      apply hRC.2.2.2
      · intro τ
        rw [map_sub, map_sub, hRC.2.1 a τ, hcomp τ]
        split_ifs <;> simp
      · rw [map_sub, finPart_cA_eq, hfin]
        simp
    exact sub_eq_zero.mp h0
  obtain ⟨y, hy⟩ := GlobalTheory.DetRootRows.fixed_mem_range a hc
  refine ⟨fstA D.host.F y, fun τ => ?_⟩
  rw [← hcomp τ, ← hy]
  rfl

theorem realPar_unique : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ l l' : D.what₂.Tau → ℝ, HasRealPar ψ θ l → HasRealPar ψ θ l' → l = l' := by
  classical
  intro D ψ θ hθ l l' hl hl'
  funext τ₀
  by_contra hne
  have hd : l τ₀ - l' τ₀ ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨x, hx⟩ := exists_real_point hθ τ₀ (1 / (2 * (l τ₀ - l' τ₀)))
  have e := (hl x).symm.trans (hl' x)
  simp only [hx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp e
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h1 : ((l τ₀ : ℂ) - l' τ₀) * ((1 / (2 * (l τ₀ - l' τ₀)) : ℝ) : ℂ) = n := by
    apply mul_left_cancel₀ hpi
    linear_combination hn
  have h2 : ((l τ₀ : ℂ) - l' τ₀) * ((1 / (2 * (l τ₀ - l' τ₀)) : ℝ) : ℂ) = 1 / 2 := by
    have hd' : ((l τ₀ : ℂ) - l' τ₀) ≠ 0 := by exact_mod_cast hd
    push_cast
    field_simp
  rw [h2] at h1
  have h3 : ((n : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; exact h1.symm
  have h4 : (n : ℝ) = 1 / 2 := by exact_mod_cast h3
  have h5 : (2 : ℝ) * n = 1 := by rw [h4]; norm_num
  have h6 : (2 : ℤ) * n = 1 := by exact_mod_cast h5
  omega

end GlobalTheory.StdUnn.RealPar
end

section

open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal


theorem _root_.GlobalTheory.T.derivativeClosedFunctionClass_smooth_and_schwartz : ∀ (k : ℕ) (V : Set ((Fin k → ℝ) → ℂ)), (∀ φ ∈ V, Continuous φ) → (∀ φ ∈ V, ∀ i : Fin k, ∃ φ' ∈ V, ∀ x : Fin k → ℝ, HasDerivAt (fun t : ℝ => φ (x + t • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' x) 0) → (∀ φ ∈ V, ContDiff ℝ ∞ φ) ∧ ((∀ φ ∈ V, ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ N * ‖φ x‖ ≤ C) → ∀ φ ∈ V, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ x, g x = φ x) := by
  first | exact @GlobalTheory.Unf.PartialClass.smooth_schwartz | exact GlobalTheory.Unf.PartialClass.smooth_schwartz | (intros; apply GlobalTheory.Unf.PartialClass.smooth_schwartz <;> assumption)
end
