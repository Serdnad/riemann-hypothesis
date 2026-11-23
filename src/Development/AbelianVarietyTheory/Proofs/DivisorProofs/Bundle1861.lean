module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicAdelicFormOfBoundedSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.holomorphicAdelicForm_of_boundedSection : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ P : FDSec X, (∀ k, (X k).IsBddSec (la k) (P k)) → HolForm θ M w (Kf : Set (GA D V)) (fun _ => 1) (adel V dict (muPin V dict mu c) P) := by
  first | exact @GlobalTheory.HolDict.BackHol.holForm_adel | exact GlobalTheory.HolDict.BackHol.holForm_adel | (intros; apply GlobalTheory.HolDict.BackHol.holForm_adel <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

noncomputable section

theorem mt_mul_splitStab {D : D7} (V : HSp D) (g h : GA D V) : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one_splitStab {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one, Units.val_one]

theorem idem_unit_splitStab {R : Type} [CommRing R] {e d d' : R} (he : e * e = e) (h : d' * d = 1) :
    (e * d + (1 - e)) * (e * d' + (1 - e)) = 1 := by
  linear_combination (e * e) * h + (2 - d - d') * he

theorem exists_isDetAt_splitStab {D : D7} {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne _ _ (idem_unit_splitStab he (det_conj_mul V g)), Units.val_mkOfMulEqOne _⟩

open scoped ComplexOrder in
theorem isCartanInv_one_splitStab (k : ℕ) : IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1 := by
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one]
  exact Matrix.PosDef.one

theorem heisO_zero_splitStab {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (f : WO V W → ℂ) : heisO ψ V W 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem om_vacuum_split_stab : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ (e : AE D) (k : GA D W), IsSplitIdem D e → SuppAt e W k → (∀ u, u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ actO V W 1 k u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True)) → om (1, k) f = mu k • f := by
  intro D ψ θ V W χV χW om hP mu hmu ΛV ΛW hV hW s hs f hf e k he hk hst
  obtain ⟨y, hy⟩ := exists_isDetAt_splitStab he.1 W k
  have h1 : ∀ τ, IsCartanInv (gramAt D V τ) ((fun _ => 1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ) := by
    intro τ
    have : gramAt D V τ = 1 := by
      unfold gramAt
      rw [hP.std]
      simp
    rw [this]
    exact isCartanInv_one_splitStab _
  have hs1 : SuppAt e V 1 := by
    intro i j
    rw [mt_one_splitStab, sub_self, Matrix.zero_apply, mul_zero]
  have hx : IsDetAt e V 1 1 := by
    unfold IsDetAt
    rw [mt_one_splitStab, Matrix.det_one, Units.val_one]
    ring
  have hact : ∀ u, actO V W 1 k (actO V W 1 k⁻¹ u) = u := by
    intro u
    unfold actO
    rw [inv_one, mt_one_splitStab, Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_assoc, ← mt_mul_splitStab,
      mul_inv_cancel, mt_one_splitStab, Matrix.one_mul]
  have key := GlobalTheory.SplitScalar.om_vacuum_eq_splitFac_smul_sum D ψ θ V W χV χW om hP.weil hP.inf hP.sigV hP.sigW
    (fun _ => 1) s h1 hs ΛV ΛV ΛW ΛW hV hV hW hW e he 1 k hs1 hk 1 y hx hy
    (fun u => ⟨fun hu => ⟨actO V W 1 k⁻¹ u, (hst _).2 (by rw [hact]; exact hu), (hact u).symm⟩,
      fun ⟨u₀, hu₀, h⟩ => h ▸ (hst u₀).1 hu₀⟩)
    {0} {0}
    (fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact ⟨zero_mem _, fun i j => mul_zero _⟩)
    (fun u hu _ => ⟨0, ⟨Finset.mem_singleton_self _, by rwa [sub_zero]⟩, fun v hv => Finset.mem_singleton.1 hv.1⟩)
    (fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact ⟨zero_mem _, fun i j => mul_zero _⟩)
    (fun u hu _ => ⟨0, ⟨Finset.mem_singleton_self _, by rwa [sub_zero]⟩, fun v hv => Finset.mem_singleton.1 hv.1⟩)
    f hf
  have hr : IsDetRoot W k y := isDetAt_root he W k hk y hy
  rw [key, hmu.2 k y hr]
  simp [heisO_zero_splitStab, splitFacO]

end

end GlobalTheory.AdTh
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.kottwitzPair_form_ratio_local_scalar_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ P₁ : Pair G, ∃ S : Finset ℕ, ∀ (P : Pair G), P.γ = P₁.γ → P.c = P₁.c → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf), f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0 → ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (P₁.γ : G.C)) ∧ inC G ℚ_[ℓ] ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (P₁.β : G.C) * (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((P₁.β⁻¹ : G.Cˣ) : G.C)) := by
  first | (exact @GlobalTheory.CxRegPair.local_pair_scalar_norm) | (exact GlobalTheory.CxRegPair.local_pair_scalar_norm) | (intros; apply GlobalTheory.CxRegPair.local_pair_scalar_norm  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem share_le_of_rankLow (h : RankLow) (F : Type) [Field F] [NumberField F] (X : Data F)
    (hn : IsNef F X.LA) (hb : IsBig F X.LA) : (X.R : ℤ) * X.del ≤ X.d := by
  refine (h F X.toGeo hn hb X.T).trans ?_
  rw [X.d_eq_finrank]
  exact_mod_cast Submodule.finrank_mono (X.global_le X.T le_rfl)

theorem share_le : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F),
    IsNef F X.LA → IsBig F X.LA → (X.R : ℤ) * X.del ≤ X.d :=
  fun q => share_le_of_rankLow (GlobalTheory.T.globalSectionRankLowerBound_of_hilbertSamuel q)

end GlobalTheory.HSCore
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.kottwitzTerm_eq_definitePair_of_local_isometry : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Q : DPair G), P.γ = Q.γ → P.c = Q.c → (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) * (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C)) → ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → P.term Kf f r K φ = Q.term Kf f r K φ := by
  first | exact @GlobalTheory.LKDefTerm.term_eq_of_local_isom | exact GlobalTheory.LKDefTerm.term_eq_of_local_isom | (intros; apply GlobalTheory.LKDefTerm.term_eq_of_local_isom <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.PairForm

section Point

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

theorem powAt_congr {G G₁ : V n → Matrix r r ℂ} {v : V n} (h : G =ᶠ[𝓝 v] G₁) (k : ℕ) :
    powAt G v k = powAt G₁ v k := by
  simp only [powAt, curvEv, curvPoly, curv_congr h]

theorem transAt_congr {G G₁ G' G₁' : V n → Matrix r r ℂ} {v : V n} (h : G =ᶠ[𝓝 v] G₁)
    (h' : G' =ᶠ[𝓝 v] G₁') (k : ℕ) : transAt G G' v k = transAt G₁ G₁' v k := by
  simp only [transAt, curvEv, curvPoly, curv_congr h, curv_congr h', conn_congr h, conn_congr h']

end Point

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {r : Type} [Fintype r] [DecidableEq r]

theorem contDiffAt_change (x x' : A.Pt) (h : x.pt = x'.pt) : ContDiffAt ℂ 2 (x'.ch ∘ x.ch.symm) x.crd := by
  have hs : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hm : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source := by
    refine ⟨x.ch.map_source x.2, ?_⟩
    show x.ch.symm ((x.ch) x.pt) ∈ x'.ch.source
    rw [x.ch.left_inv x.2]
    exact (congrArg (fun y => y ∈ x'.ch.source) h).mpr x'.2
  exact GlobalTheory.SCV.contDiffAt_of_differentiableOn (A.holo x.1.1 x'.1.1) (hs.mem_nhds hm) 2

theorem change_crd (x x' : A.Pt) (h : x.pt = x'.pt) : (x'.ch ∘ x.ch.symm) x.crd = x'.crd := by
  show (x'.ch) (x.ch.symm ((x.ch) x.pt)) = (x'.ch) x'.pt
  rw [x.ch.left_inv x.2]
  exact congrArg x'.ch h

theorem germ_change (G : M → M → Matrix r r ℂ) (x x' : A.Pt) (h : x.pt = x'.pt) :
    (fun u => G x.pt (x.ch.symm u)) =ᶠ[𝓝 x.crd] fun u => G x'.pt (x'.ch.symm ((x'.ch ∘ x.ch.symm) u)) := by
  have hc : ContinuousAt x.ch.symm x.crd := x.ch.continuousAt_symm (x.ch.map_source x.2)
  have hmem : x'.ch.source ∈ 𝓝 (x.ch.symm x.crd) := by
    show x'.ch.source ∈ 𝓝 (x.ch.symm ((x.ch) x.pt))
    rw [x.ch.left_inv x.2]
    exact (congrArg (fun y => x'.ch.source ∈ 𝓝 y) h).mpr (x'.ch.open_source.mem_nhds x'.2)
  filter_upwards [hc hmem] with u hu
  show G x.pt (x.ch.symm u) = G x'.pt (x'.ch.symm ((x'.ch) (x.ch.symm u)))
  rw [x'.ch.left_inv hu]
  exact congrArg (fun y => G y (x.ch.symm u)) h

theorem smooth_crd (G : M → M → Matrix r r ℂ) (hG : ∀ y, SmoothUnitAt A (G y) y) (x : A.Pt) :
    MContDiffAt ∞ (fun u => G x.pt (x.ch.symm u)) x.crd ∧ IsUnit (G x.pt (x.ch.symm x.crd)).det := by
  refine ⟨((hG x.pt).2 x.1.1 x.2).self_of_nhds, ?_⟩
  show IsUnit (G x.pt (x.ch.symm ((x.ch) x.pt))).det
  rw [x.ch.left_inv x.2]
  exact (hG x.pt).1

theorem smooth_change (G : M → M → Matrix r r ℂ) (hG : ∀ y, SmoothUnitAt A (G y) y) (x x' : A.Pt) (h : x.pt = x'.pt) :
    MContDiffAt ∞ (fun u => G x'.pt (x'.ch.symm u)) ((x'.ch ∘ x.ch.symm) x.crd) ∧
      IsUnit (G x'.pt (x'.ch.symm ((x'.ch ∘ x.ch.symm) x.crd))).det := by
  rw [change_crd A x x' h]
  exact smooth_crd A G hG x'

end Manifold

theorem isForm_pow_trans : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r]
    [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' →
      ∀ k, A.IsForm (fld A (powFld A G k)) ∧ A.IsForm (transFld A G G' k) := by
  intro M _ n A r _ _ G G' hG k
  have sG : ∀ y, SmoothUnitAt A (G y) y := fun y => (hG.smooth y).1
  have sG' : ∀ y, SmoothUnitAt A (G' y) y := fun y => (hG.smooth y).2
  have near := GlobalTheory.T.gramConnectionPair_chernFields_local_frame M n A r G G' hG
  constructor
  · refine ⟨fun i S => ?_, fun x x' h => ?_⟩
    · intro v hv
      let x : A.Pt := ⟨(i, (A.e i).symm v), (A.e i).map_target hv⟩
      have hx : x.crd = v := (A.e i).right_inv hv
      obtain ⟨h1, h2⟩ := smooth_crd A G sG x
      have hs := (GlobalTheory.T.curvature_power_sum_transgression_smooth_dbar_closed n r _ _ x.crd h1 h2 h1 h2 k).1 S
      have key : ContDiffAt ℝ ∞ (fun v => (bas n).repr (A.loc (fld A (powFld A G k)) i v) S) x.crd :=
        hs.congr_of_eventuallyEq ((near x k).mono fun u hu => congrArg (fun a => (bas n).repr a S) hu.1)
      rw [hx] at key
      exact key.contDiffWithinAt
    · obtain ⟨h1, h2⟩ := smooth_change A G sG x x' h
      have hc := ((GlobalTheory.T.curvature_power_pullback_holomorphic n n r _ (x'.ch ∘ x.ch.symm) x.crd (contDiffAt_change A x x' h) h1 h2).2 k).1
      show (powAt (fun v => G x.pt (x.ch.symm v)) x.crd k : Alt n) =
        pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (powAt (fun v => G x'.pt (x'.ch.symm v)) x'.crd k : Alt n)
      rw [powAt_congr (germ_change A G x x' h), hc, change_crd A x x' h]
  · refine ⟨fun i S => ?_, fun x x' h => ?_⟩
    · intro v hv
      let x : A.Pt := ⟨(i, (A.e i).symm v), (A.e i).map_target hv⟩
      have hx : x.crd = v := (A.e i).right_inv hv
      obtain ⟨h1, h2⟩ := smooth_crd A G sG x
      obtain ⟨h1', h2'⟩ := smooth_crd A G' sG' x
      have hs := (GlobalTheory.T.curvature_power_sum_transgression_smooth_dbar_closed n r _ _ x.crd h1 h2 h1' h2' k).2.2 S
      have key : ContDiffAt ℝ ∞ (fun v => (bas n).repr (A.loc (transFld A G G' k) i v) S) x.crd :=
        hs.congr_of_eventuallyEq ((near x k).mono fun u hu => congrArg (fun a => (bas n).repr a S) hu.2.2)
      rw [hx] at key
      exact key.contDiffWithinAt
    · obtain ⟨h1, h2⟩ := smooth_change A G sG x x' h
      obtain ⟨h1', h2'⟩ := smooth_change A G' sG' x x' h
      have hc := GlobalTheory.T.chernTransgressionForm_holomorphic_pullback n n r _ _ (x'.ch ∘ x.ch.symm) x.crd (contDiffAt_change A x x' h) h1 h2 h1' h2' k
      show transAt (fun v => G x.pt (x.ch.symm v)) (fun v => G' x.pt (x.ch.symm v)) x.crd k =
        pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd)
          (transAt (fun v => G x'.pt (x'.ch.symm v)) (fun v => G' x'.pt (x'.ch.symm v)) x'.crd k)
      rw [transAt_congr (germ_change A G x x' h) (germ_change A G' x x' h), hc, change_crd A x x' h]

end GlobalTheory.ChernCalc.PairForm
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem graded_weight : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (gr : Root m → X.Dv), IsGraded E gr →
    IsMetricFr E H → ∀ x : Root m, ∃ (L : LB X.X) (r : L.ι → X.Fnˣ) (ψ : Weight X.str σ L),
      Presents (gr x) L r ∧ ψ.IsCInf ∧ c1W ψ = grF E H x := by
  intro F _ σ X ι _ m E H gr hG hH x
  obtain ⟨B, hB, hgr⟩ := hG
  have hunit : ∀ (z : X.X) (A : Mat m X.Fn), A ∈ E.S z → ∀ f : X.Fnˣ, (gr x).IsEqn z f →
      UnitAt z ((B * A⁻¹) x.1 x.2 x.2 / f) := by
    intro z A hA f hf
    obtain ⟨A₀, hA₀, t, ht, he⟩ := hgr z x
    obtain ⟨hu, hd⟩ := GlobalTheory.T.adaptedFullFlag_frame_change_diagonal_units F X ι m E B hB z A₀ A hA₀ hA x
    have htf : UnitAt z ((t : X.Fn) / f) := (hf.iff_unitAt).1 he
    have hne : (A * A₀⁻¹) x.1 x.2 x.2 ≠ 0 := fun h0 => by
      obtain ⟨a, ha, h⟩ := hu
      rw [h0] at h
      exact (ha.map (algebraMap _ X.Fn)).ne_zero h
    have e : (B * A⁻¹) x.1 x.2 x.2 / f = ((t : X.Fn) / f) * ((A * A₀⁻¹) x.1 x.2 x.2)⁻¹ := by
      rw [← ht, hd]; field_simp
    rw [e]; exact htf.mul hu.inv

  let Ach : CxPts X.str σ → Mat m X.Fn := fun y => (E.nonempty (under y)).choose
  have hAch : ∀ y, Ach y ∈ E.S (under y) := fun y => (E.nonempty (under y)).choose_spec
  let val : Mat m X.Fn → CxPts X.str σ → X.Fn → ℝ := fun A y f =>
    -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2)
  let D := gr x
  have hP := presents_toLB D
  have heq : ∀ (i : (toLB D).ι) (y : CxPts X.str σ), y ∈ ptsIn X.str σ ((toLB D).U i) →
      D.IsEqn (under y) (i.1.2) := fun i y hy => i.2.2 _ (mem_ptsIn.1 hy)
  have hindep : ∀ (i : (toLB D).ι) (y : CxPts X.str σ), y ∈ ptsIn X.str σ ((toLB D).U i) →
      ∀ A ∈ E.S (under y), val (Ach y) y i.1.2 = val A y i.1.2 := fun i y hy A hA =>
    GlobalTheory.T.flaggedBundleMetric_graded_weight_frame_independent F σ X ι m E H hH B hB y (Ach y) (hAch y) A hA x _ (hunit _ A hA _ (heq i y hy))
  let ψ : Weight X.str σ (toLB D) :=
    { isLB := isLB_toLB D
      φ := fun i y => val (Ach y) y i.1.2
      trans := by
        intro i j y hi hj
        have hu1 := hunit _ _ (hAch y) _ (heq i y hi)
        have hu2 : UnitAt (under y) ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) := ((heq j y hj).iff_unitAt).1 (heq i y hi)
        have hg : gv X.str σ (toLB D) i j y = ratVal ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) y := by
          have hgen : genericPoint X.X ∈ (toLB D).U i ⊓ (toLB D).U j := ⟨i.2.1, j.2.1⟩
          rw [← fnOf_toLB_g i j hgen, ratVal_fnOf (mem_ptsIn_inf.2 ⟨hi, hj⟩) hgen]
          rfl
        have hi0 := (i.1.2).ne_zero
        have hj0 := (j.1.2).ne_zero
        have e : (B * (Ach y)⁻¹) x.1 x.2 x.2 / (j.1.2 : X.Fn) =
            ((B * (Ach y)⁻¹) x.1 x.2 x.2 / i.1.2) * ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) := by
          field_simp
        show val (Ach y) y j.1.2 = val (Ach y) y i.1.2 - _
        simp only [val]
        rw [e, ratVal_mul hu1.regAt hu2.regAt, log_normSq_mul (ratVal_ne_zero hu1) (ratVal_ne_zero hu2), hg]
        ring }
  refine ⟨toLB D, fun i => i.1.2, ψ, hP, ?_, ?_⟩
  · intro i y hy
    have hu := hunit _ _ (hAch y) _ (heq i y hy)
    refine (GlobalTheory.T.complexPointsSmoothAt_log_unit_add_graded_length F σ X ι m m E H hH y (Ach y) (hAch y) _ hu x.1 x.2).congr ?_
    filter_upwards [frame_eventually_near F σ X ι m m E y (Ach y) (hAch y), (isOpen_ptsIn _).mem_nhds hy] with z hz hzi
    exact hindep i z hzi (Ach y) hz
  · funext p
    obtain ⟨⟨c, y⟩, hy⟩ := p
    have hy' : y ∈ c.e.source := hy
    have ha : y ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) := mem_pick ψ.isLB y
    have hu := hunit _ _ (hAch y) _ (heq _ y ha)
    have hnear : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) ∧ Ach y ∈ E.S (under z) :=
      Filter.Eventually.and ((isOpen_ptsIn _).mem_nhds ha) (frame_eventually_near F σ X ι m m E y (Ach y) (hAch y))
    have hnear' : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) ∧
        Ach y ∈ E.S (under (c.e.symm v)) := by
      have hc := c.e.continuousAt_symm (c.e.map_source hy')
      rw [ContinuousAt, c.e.left_inv hy'] at hc
      exact hc.eventually hnear
    have key : leviForm (fun v => ψ.φ (pick ψ.isLB y) (c.e.symm v)) (c.e y) =
        leviForm (fun v => -Real.log (grD (H (Ach y) (c.e.symm v) x.1) x.2)) (c.e y) := by
      rw [leviForm_congr (u' := fun v => val (Ach y) (c.e.symm v) (pick ψ.isLB y).1.2)]
      · exact GlobalTheory.T.leviForm_graded_length_sub_log_unit_normSq F σ X ι m m E H hH y (Ach y) (hAch y) _ hu x.1 x.2 c hy'
      · filter_upwards [hnear'] with v hv
        exact hindep _ _ hv.1 (Ach y) hv.2
    have e1 : c1W ψ ⟨(c, y), hy⟩ =
        ofValues (HermFrame.ddc (fun v => ψ.φ (pick ψ.isLB y) (c.e.symm v)) (c.e y)) := rfl
    have e2 : grF E H x ⟨(c, y), hy⟩ =
        ofValues (HermFrame.ddc (fun v => -Real.log (grD (H (Ach y) (c.e.symm v) x.1) x.2)) (c.e y)) := rfl
    rw [e1, e2]
    unfold HermFrame.ddc
    rw [key]

end GlobalTheory.ChernCalc
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSShort

theorem totRes_incl_zero {K : Type} [Field K] [NumberField K] {X : Data K} {s : Fin X.D → Fin X.N → K} {hs : X.IsGood s} {δ : ℕ}
    (Co : Coord X.toGeo hs δ) (x : X.V 0) : totRes Co (incl X 0 x) = Co.ev 0 (hs.res 0 x.1) := by
  have h : incl X 0 x 0 = x.1 := Pi.single_eq_same (M := fun j => X.toGeo.Sec j) 0 x.1
  simp only [totRes, LinearMap.comp_apply, LinearMap.proj_apply, h, LinearEquiv.coe_coe]

theorem map_totRes_range_incl_zero : Quoted → ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), IsNef K X.L₂ → IsBig K X.L₂ → (LinearMap.range (incl X 0)).map (totRes Co) = ⊤ := by
  intro Q K _ _ X s hs δ Co hnef hbig
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨f, hf⟩ := GlobalTheory.HSResOnto.res_onto Q K X.toGeo hnef hbig s hs ((Co.ev 0).symm v)
  have hf' : hs.res 0 (X.toGeo.mulE 0 f) = (Co.ev 0).symm v := hf
  have hm : X.toGeo.mulE 0 f ∈ X.V 0 := X.global_le 0 (Nat.zero_le _) (X.toGeo.mulE_mem_global 0 f)
  refine Submodule.mem_map.2 ⟨incl X 0 ⟨_, hm⟩, LinearMap.mem_range_self _ _, ?_⟩
  rw [totRes_incl_zero, hf', LinearEquiv.apply_symm_apply]

end GlobalTheory.HSShort
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

theorem _root_.GlobalTheory.T.evaluation_good_models_intertwine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁),
    M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → IsTame F e := by
  first | exact @GlobalTheory.EvTame.isTame_of_isEv | exact GlobalTheory.EvTame.isTame_of_isEv | (intros; apply GlobalTheory.EvTame.isTame_of_isEv <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)


theorem _root_.GlobalTheory.T.eigen_intertwiner_composition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  first | exact @GlobalTheory.ThKEvAdm.comp_mem_adm | exact GlobalTheory.ThKEvAdm.comp_mem_adm | (intros; apply GlobalTheory.ThKEvAdm.comp_mem_adm <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one : GlobalTheory.EtC.C2 := by
  first | (exact @GlobalTheory.EtC.etC_c2) | (exact GlobalTheory.EtC.etC_c2) | (intros; apply GlobalTheory.EtC.etC_c2  <;> assumption)
end
