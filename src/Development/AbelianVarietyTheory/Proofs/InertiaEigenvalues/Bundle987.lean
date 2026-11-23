module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle986
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMapEveryNormalisedFamilyAtCoreConstants
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReading
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle029
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle985
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.vacuumReadingConstants_levelCover_relate_core : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D (T.V j σ) →* Module.End ℂ (WO V (T.V j σ) → ℂ)), IsPair ψ θ V (T.V j σ) χV χW om → ∀ hr : (T.V j σ).rank = D.R.r, (∀ k, IsMod (T.V j σ) hr ((T.U j σ).X k)) → ∀ (h : GA D (T.V j σ)) (δ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ γ : GA D (T.V j σ), (∀ τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ, Matrix.reindex (finCongr hr) (finCongr hr) (realM θ (Formalism.L2.Theta.mt (T.V j σ) γ) τ) = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ) → ∀ (hx₁ : (T.dict j σ h).2 ∈ ((T.U j σ).X (T.dict j σ h).1).dom) (hx₂ : (C.dict₂ h).2 ∈ (C.U₂.X (C.dict₂ h).1).dom), IsUnitFr ((T.U j σ).X (T.dict j σ h).1) (T.dict j σ h).2 → ∀ (F₁ F₂ : WO V (T.V j σ) → ℂ) (m₁ m₂ : ℂ), (∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (C.U₂.X (C.dict₂ h).1).Λ) (idx : Fin g ≃ (C.U₂.X (C.dict₂ h).1).Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw j)), IsSympl (C.U₂.X (C.dict₂ h).1) bas → IdxIs C.d.c₂ C.σ₂ (C.U₂.X (C.dict₂ h).1) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads C.U₂ (C.dict₂ h).1 bas idx e ⟨(C.dict₂ h).2, hx₂⟩ ϑ → ∀ w : WO V (T.V j σ), w.map (finPart D) = 0 → F₁ w = m₁ * cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx (C.U₂.X (C.dict₂ h).1) bas idx (C.dict₂ h).2 (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b) (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b)) * ∏ b, ϑ (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b)) → (∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] ((T.U j σ).X (T.dict j σ h).1).Λ) (idx : Fin g ≃ ((T.U j σ).X (T.dict j σ h).1).Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw j)), IsSympl ((T.U j σ).X (T.dict j σ h).1) bas → IdxIs T.Q.c σ ((T.U j σ).X (T.dict j σ h).1) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads (T.U j σ) (T.dict j σ h).1 bas idx e ⟨(T.dict j σ h).2, hx₁⟩ ϑ → ∀ w : WO V (T.V j σ), w.map (finPart D) = 0 → F₂ w = m₂ * cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx ((T.U j σ).X (T.dict j σ h).1) bas idx (T.dict j σ h).2 (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b) (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b)) * ∏ b, ϑ (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b)) → (∀ w, F₂ (actO V (T.V j σ) 1 γ w) = F₁ w) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a V.rank, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a V.rank, C.IsPull f f₂ → m₁ * rdU C.U₂ f₂ (C.dict₂ h).1 (C.dict₂ h).2 = m₂ * rdU (T.U j σ) f (T.dict j σ h).1 (T.dict j σ h).2 := by
  first | exact @GlobalTheory.CoverConstMove.const_cover | exact GlobalTheory.CoverConstMove.const_cover | (intros; apply GlobalTheory.CoverConstMove.const_cover <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.coverPullback_mem_boundedCuspidalHolomorphic : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n) → ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ ∈ holSub0 C.U₂.X (laU C.U₂ a n) := by
  first | exact @GlobalTheory.CoverHol.cover_pull_holSub0 | exact GlobalTheory.CoverHol.cover_pull_holSub0 | (intros; apply GlobalTheory.CoverHol.cover_pull_holSub0 <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_unitConstant_coverPullbackReading : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∃ u : C.U₂.Comp → ℂ, (∀ k, ‖u k‖ = 1) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → ∀ h : GA D (T.V j σ), rdU C.U₂ f₂ (C.dict₂ h).1 (C.dict₂ h).2 = u (C.dict₂ h).1 * rdU (T.U j σ) f (T.dict j σ h).1 (T.dict j σ h).2 := by
  first | exact @GlobalTheory.CoverConstAt.cover_read_const | exact GlobalTheory.CoverConstAt.cover_read_const | (intros; apply GlobalTheory.CoverConstAt.cover_read_const <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.oneMap_every_normalisedFamily_at_coreConstants : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → ∃ (ζ : ℂ) (z : G), IsRoot1 ζ ∧ z ∈ Subgroup.center G ∧ ∀ (t : Tp) (h : M.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), RepsR R i (tup t) h (M.bad t) J' (M.Lh t) (M.gam t) (M.vol t) → ∀ (y : (R.HV i (tup t)).H) (x : M.Cl' t → VsV D i M.c'.F), Place R i (tup t) h M.c0' y x → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M t x f → ∀ g : GA D (Wc D i), ph i * R.thF i (tup t) y (v₀ i (sg0 D A)) g = ζ * T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2 := by
  first | exact @GlobalTheory.SerAll.ser_at_core_constants | exact GlobalTheory.SerAll.ser_at_core_constants | (intros; apply GlobalTheory.SerAll.ser_at_core_constants <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar




noncomputable section

namespace GlobalTheory.DictionaryCast
open Formalism.IndefR.FWT Formalism.L2.Pj
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}

theorem evW_smul (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (j : Fin D.R.m) (a : D.what₂.LL) (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₀ j (a • x) = sg0 D A3.A a • evW YS v₀ j x := by
  simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [LinearEquiv.map_smul, LinearMap.map_smulₛₗ, map_smul]
  rfl

theorem castDict_sum_smul' {V W : HSp D} (e : V = W) {m : ℕ} (a : Fin m → ℂ) (ψ : Fin m → GA D V → ℂ) (g : GA D W) :
    castDict e (∑ i, a i • ψ i) g = ∑ i, a i * castDict e (ψ i) g := by
  subst e
  simp [castDict, Finset.sum_apply]

theorem castDict_phiJ' {T : CoreJ D} {j : ℕ} {W : HSp D} {σ : T.Q.c.F →+* ℂ} (hσ : σ = T.σ₀) (h1 : T.V j σ = W)
    (h2 : T.V j T.σ₀ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    (h1 ▸ T.phiJ j σ a f : GA D W → ℂ) g = castDict h2 (T.phiJ j T.σ₀ a f) g := by
  subst hσ
  subst h1
  rfl

end GlobalTheory.DictionaryCast

theorem GlobalTheory.XiIntCore.supLattice_comb_of_baseInt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) (b : Bool) (hV : X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j) (la : HeightOneSpectrum (𝓞 X.core.Q.c.F)), (∀ x : X.core.Q.c.F, FinitePlace.mk la x ≤ 1 ↔ ∃ o : D.ntw.O i, Y.Z.ρ.eO i b o = X.core.σ₀ x) → ∀ (n : ℕ) (o : Fin n → D.ntw.O i) (ψ : Fin n → (GA D (X.core.V ((j : ℕ) + 1) X.core.σ₀) → ℂ)), (∀ k, ψ k ∈ GlobalTheory.CoverRead.baseInt X.core ((j : ℕ) + 1) X.core.σ₀ (Formalism.L2.Pj.wtA (X.geo.κ j)) (X.geo.κ j).n {la}) → ∃ (n' : ℕ) (o' : Fin n' → D.ntw.O i) (m : Fin n' → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ FWT.castDict hV (∑ k, Y.Z.ρ.eO i b (o k) • ψ k) = ∑ k, Y.Z.ρ.eO i b (o' k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  intro hA hR hI D X E Y hF hP i hi j b hV la hla n o ψ hψ
  have hev : X.geo.fw.Evaluates := X.geo.fw.evaluates_of_lUnif X.unif
  have hσ : FWT.res X.core (sg0 D X.A3.A) = X.core.σ₀ := by
    rw [show sg0 D X.A3.A = D.what₂.embLL from sgAt_mk _ X.R.hv0]
    exact FWT.res_embLL X.core X.geo.fw.alg_eq X.geo.fw.laws.pins.2.2.1
  have hV' : X.core.V ((j : ℕ) + 1) (FWT.res X.core (sg0 D X.A3.A)) = Wc D j := by rw [hσ]; exact hV
  have hlast : (X.geo.κ j).LastPos := fun τ k hk => by
    rw [(X.geo.fw.kap j τ).1 k]; exact GlobalTheory.LiftWeight.kapTop_lastPos D j τ k hk
  have hinR : Formalism.L2.Pj.InR D ((j : ℕ) + 1) := ⟨Nat.le_add_left _ _, j.2⟩
  have key : ∀ k, ∃ (o'' : D.ntw.O i) (m : NX.FmK Y.S ((j : ℕ) + 1)), Subtype.val m ∈ (Y.S.A ((j : ℕ) + 1)).MK ∧
      FWT.castDict hV (ψ k) = Y.Z.ρ.eO i b o'' • evW Y.YS X.geo.v₀ j (Subtype.val m) := by
    intro k
    obtain ⟨f, ⟨hsec, hhol, hint⟩, hfk⟩ := hψ k
    have hcu := GlobalTheory.CuspAllEmb.mem_cuspA_of_rdU_mem_holSub0 D X.core X.geo.fw.laws _ hinR (X.geo.κ j) hlast f hsec hhol
    let fc : FWT.Cu X.core X.geo.κ j := ⟨f, hcu⟩
    have hball : ∀ y : (X.R.FW j).Pt la, (X.R.FW j).nrm la y (X.geo.fw.e j fc) ≤ 1 := fun y => by
      rw [X.geo.fw.nrm_eq]
      exact (X.core.nrmM_le_one_iff _ la _ _).2 (hint la rfl _ (X.geo.fw.pt j la y).2)
    obtain ⟨s, hs, hsM⟩ := GlobalTheory.supLattice_localisation_of_unitBall _ _ _ _ _ (X.R.FW j) (X.integral j).2.1.2 la _ hball
    set w := X.geo.fw.e j fc with hw
    have hx₀ : evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (w : Fin (X.R.nW j) → D.what₂.LL)) =
        FWT.phiC X.core hV' (Formalism.L2.Pj.wtA (X.geo.κ j)) f := by
      refine Eq.trans ?_ (hev j (sg0 D X.A3.A) (by rw [hσ]; exact X.core.toCore.good_σ₀) hV' fc)
      simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [LinearEquiv.apply_symm_apply]
      rfl
    have hsm : s • (w : Fin (X.R.nW j) → D.what₂.LL) =
        algebraMap X.core.Q.c.F D.what₂.LL (s : X.core.Q.c.F) • (w : Fin (X.R.nW j) → D.what₂.LL) := by
      rw [algebraMap_smul]
      exact (algebraMap_smul X.core.Q.c.F s _).symm
    let m : NX.FmK Y.S ((j : ℕ) + 1) := ⟨(Y.YS.fi j).e.symm (s • (w : Fin (X.R.nW j) → D.what₂.LL)),
      ((Y.YS.fi j).wk _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hsM.fst)⟩
    have hmK : Subtype.val m ∈ (Y.S.A ((j : ℕ) + 1)).MK :=
      ((Y.YS.fi j).mkK _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hsM)
    have hsσ : sg0 D X.A3.A (algebraMap X.core.Q.c.F D.what₂.LL (s : X.core.Q.c.F)) = X.core.σ₀ (s : X.core.Q.c.F) :=
      congrArg (fun τ : X.core.Q.c.F →+* ℂ => τ (s : X.core.Q.c.F)) hσ
    have hevm : evW Y.YS X.geo.v₀ j (Subtype.val m) =
        X.core.σ₀ (s : X.core.Q.c.F) • evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (w : Fin (X.R.nW j) → D.what₂.LL)) := by
      change evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (s • (w : Fin (X.R.nW j) → D.what₂.LL))) = _
      rw [hsm, LinearEquiv.map_smul, GlobalTheory.DictionaryCast.evW_smul, hsσ]
    have hs0 : (s : X.core.Q.c.F) ≠ 0 := fun h => hs (by
      rw [show s = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact la.asIdeal.zero_mem)
    have hinv : FinitePlace.mk la ((s : X.core.Q.c.F)⁻¹) ≤ 1 := by
      rw [map_inv₀, FinitePlace.mk_apply, (FinitePlace.norm_eq_one_iff_notMem X.core.Q.c.F la s).mpr hs, inv_one]
    obtain ⟨o'', ho''⟩ := (hla _).1 hinv
    refine ⟨o'', m, hmK, ?_⟩
    have hc : FWT.castDict hV (ψ k) = FWT.phiC X.core hV' (Formalism.L2.Pj.wtA (X.geo.κ j)) f := by
      rw [← hfk]
      funext g
      exact (GlobalTheory.DictionaryCast.castDict_phiJ' hσ hV' hV _ _ g).symm
    rw [hc, ← hx₀, hevm, ho'', smul_smul, map_inv₀, inv_mul_cancel₀ ((map_ne_zero _).2 hs0), one_smul]
  choose o'' m hm he using key
  refine ⟨n, fun k => o k * o'' k, m, hm, ?_⟩
  funext g
  rw [GlobalTheory.DictionaryCast.castDict_sum_smul', Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he k]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodForms_classSums_of_projectedLift_range : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) → ∀ i, BaseTup Y i → SumOnto Y.Z.rd i := by
  first | exact @GlobalTheory.RankOnto.sumOnto_of_goodRange | exact GlobalTheory.RankOnto.sumOnto_of_goodRange | (intros; apply GlobalTheory.RankOnto.sumOnto_of_goodRange <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct




namespace GlobalTheory.Unframe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ} (kap : ℝ) (lam : type_of% Rl.lam3)
  {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  (hw : ∀ i σ, w i σ ∈ Subgroup.center Γ) (hst : ∀ i, (Rl.FW i).MKStable)
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem pin_move {ρ : Setup D.ntw} (h : RealPin Rl cG ρ) : RealPin (fullHeckeRealDatMovedReadings Rl w kap lam) cG ρ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15, h.16, h.17, h.18⟩

theorem isNorm_move {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (ν : ℂ) :
    IsNorm (fullHeckeRealDatMovedReadings Rl w kap lam) v₀ B ν ↔ IsNorm Rl v₀ B ν := Iff.rfl

theorem vec_move {j : Fin D.R.m} (h : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) :
    FWT.IsChosenExtremalVector (fullHeckeRealDatMovedReadings Rl w kap lam).toRealDat j (sg0 D A3.A) (v₀ j _) := h

theorem isScalar_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {ν : ℂ}
    (h : IsScalar YS v₀ hρ i j b ν) : IsScalar (Rl := fullHeckeRealDatMovedReadings Rl w kap lam) (cG := cG) (S := moveS w YS) (moveYS kap lam YS hw hst) v₀ hρ i j b ν :=
  ⟨h.ne, fun h' => (isNorm_move kap lam _ _).2 (h.norm (h'.imp fun _ => (isNorm_move kap lam _ _).1)), fun h' =>
    (congrArg (Rat hρ) (realRd_move kap lam YS hw hst v₀ hρ i j b ν)).mpr
      (h.rat ((ratRow_move kap lam YS hw hst v₀ hρ i j b).1 h'))⟩

def moveZ (Z : ExportTie YS v₀) : ExportTie (Rl := fullHeckeRealDatMovedReadings Rl w kap lam) (cG := cG) (S := moveS w YS) (moveYS kap lam YS hw hst) v₀ where
  ρ := Z.ρ
  good := Z.good
  pin := pin_move kap lam Z.pin
  vec := fun j => vec_move kap lam (Z.vec j)
  ν := Z.ν
  scalar := fun i j b => isScalar_move kap lam hw hst Z.good i j b (Z.scalar i j b)
  tie := cast (congrArg (Comparison₂ Z.good (Y := D.nexp)) (rd_move kap lam hw hst Z).symm) Z.tie
  hecke := fun i j b => (congrArg HeckeTie (realRd_move kap lam YS hw hst v₀ Z.good i j b _)).mpr (Z.hecke i j b)
  univ := Z.univ

end GlobalTheory.Unframe

end
end
