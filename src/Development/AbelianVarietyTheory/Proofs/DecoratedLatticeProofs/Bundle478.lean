module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle021
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle451
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAtSeesawProductDatumEqVacuumCombinations
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle467
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle445
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle300
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle399
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle469
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle370
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle474
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle468
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle470
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem twVec' : TwVec' := by
  intro B X I hOk hPins l Z u a Ch A hA ψ θ x vac c₀ hX k _ _ _ _ ι p β Q hStd J hPl j hj α γ cT hReps e he
  have hjm : j ≤ B.R.m := Nat.le_of_succ_le hj
  have hL0 : ∀ z, z ∈ (x j).L ↔ z ∈ intVec (I.rec7 l Z) _ := (hX.xs j hjm).2.2
  have hL1 : ∀ z, z ∈ (x (j + 1)).L ↔ z ∈ intVec (I.rec7 l Z) _ := (hX.xs (j + 1) hj).2.2
  have hvac := hX.vc j (by omega)
  have hS0 : ((x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ := by ext z; exact hL0 z
  have hS1 : ((x (j + 1)).L : Set (Fin ((I.rec7 l Z).sp.X (j + 1)).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ := by ext z; exact hL1 z
  have hV : Vac ψ _ _ (x j).L (x (j + 1)).L (fun v => ∃ i, v = (p i).v) (vac j) := by
    refine ⟨hvac.2.theta, ?_⟩
    have hle : latO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ((x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) ((x (j + 1)).L : Set (Fin ((I.rec7 l Z).sp.X (j + 1)).rank → (I.rec7 l Z).host.E)) (fun v => ∃ i, v = (p i).v) ≤ stdHom _ _ := by
      rw [hS0, hS1]
      apply AddSubgroup.closure_mono
      rintro w ⟨a, ha, -, rest⟩
      exact ⟨a, ha, fun _ h => absurd trivial h, rest⟩
    exact ⟨fun u hu => hvac.2.lat.1 u (hle hu), fun e' he' u hu hh => hvac.2.lat.2 e' he' u (hle hu) hh⟩
  have hO := hReps.2 (vac j) hV
  obtain ⟨eq, heq⟩ := hStd.1
  have hF := GlobalTheory.T.putInSplitPlaces_datum_product_on_half (I.rec7 l Z) k ι p J hPl _ _ ψ hX.std _ _ (β j) (β (j + 1)) (x j).L (x (j + 1)).L
    (GlobalTheory.T.integral_coordinate_vectors_chain_space_selfDual I hOk l Z j hjm _ hL0) (GlobalTheory.T.integral_coordinate_vectors_chain_space_selfDual I hOk l Z (j + 1) hj _ hL1) hL0 hL1 _ e he ⟨eq, heq⟩ _ (vac j) _ hvac.2.theta hvac.2.lat hO
  have hval := GlobalTheory.T.chartBasePoints_levelDatum_eq_local_prod I hOk hPins l Z u a Ch A hA k ι p β Q _ hStd J hPl j hj α γ
  convert hF using 2 with z
  exact hval z

end GlobalTheory.AdForm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section
namespace GlobalTheory.SeeSaw.LocSrc

section Local
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLoc_one (p : Place D k) {S : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) :
    p.IsLoc F 1 1 := by
  refine ⟨fun i j => by simp [Formalism.L2.Theta.mt], ?_⟩
  have : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
  simp [F.βγ]

theorem isComp_inv (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ⁻¹ μ) : p.IsComp χ μ⁻¹ := by
  intro x a ha
  have h1 := h x a ha
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv] at h1 ⊢
  rw [h1, inv_inv]

theorem valuation_det_of_mem_stabLat {Y : Type} [Fintype Y] [DecidableEq Y] {g h : GL Y k} (hh : h ∈ GlobalTheory.StepData.stabLat g) :
    valuation k ((Matrix.GeneralLinearGroup.det h : kˣ) : k) = 1 := by
  have h1 := valuation_det_of_mem_KO (GlobalTheory.StepData.mem_stabLat.1 hh)
  have e : Matrix.GeneralLinearGroup.det (g⁻¹ * h * g) = Matrix.GeneralLinearGroup.det h := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  rwa [e] at h1

theorem om_Phi {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hu : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) (j a : ℕ) (H : j + a = s) (hb : j + (a + 1) = s + 1)
    (x : ((S.T t).lev j (a + 1) hb).J) :
    GlobalTheory.SplitWeil.om (μ (j + 1)) x.1 1 ((S.T t).Phi j a H) = (((S.T t).lev j (a + 1) hb).lam x : ℂ) • (S.T t).Phi j a H := by
  obtain ⟨e1, e2⟩ := GlobalTheory.SeeSaw.MuUnits.withMu_eq k s κ S t μ hμ hu
  have hx : x.1 ∈ (((withMu S μ hμ).T t).lev j (a + 1) hb).J := by rw [(e2 j (a + 1) hb).1]; exact x.2
  have L : ((withMu S μ hμ).T t).Laws := Chain.ofType_laws _ _ _ _ _
  have h1 := (L.1 j a H).1 ⟨x.1, hx⟩
  rw [e1, (e2 j (a + 1) hb).2 x.1 hx x.2] at h1
  exact h1

end Local

theorem seeSaw_local_sourceLevel_character : ∀ (D : D7) (c : Comm D) (v : VCom c) (G : GLoc v), c.Is → v.Is → ∀ (j : ℕ) (χS χT : (AE D)ˣ →* Circle) (om : Om (c.V j) (c.V (j + 1))), IsWeilDatumO c.ψ _ _ χS χT om → ∀ (μ : ℕ → G.kˣ →* ℂˣ), (∀ i, IsTame (μ i)) → (∀ i (x : G.kˣ), valuation G.k (x : G.k) = 1 → μ i x = G.S.μ i x) → (ofSplit G.q).IsComp χS⁻¹ (μ (j + 1)) → (∃ μ', (ofSplit G.q).IsComp χT μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1) x = 1) → j ≤ G.s → ∀ (b : ℕ) (hb : j + b = G.s + 1) (x : ((G.S.T (Fin D.R.t)).lev j b hb).J) (h : GA D (c.V j)), (ofSplit G.q).IsLoc (G.FY j b hb) h x.1 → ∀ f : WO (c.V j) (c.V (j + 1)) → ℂ, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = G.q.v) f → om (h, 1) (comb c.ψ _ _ (G.eg j) f) = (((G.S.T (Fin D.R.t)).lev j b hb).lam x : ℂ) • comb c.ψ _ _ (G.eg j) f := by
  intro D c v G hc hv j χS χT ω hω μ hμ hu hS hT hj b hb x h hl f hf
  obtain ⟨μ', hT, hT'⟩ := hT
  obtain ⟨a, rfl⟩ : ∃ a, b = a + 1 := ⟨b - 1, by omega⟩
  have H : j + a = G.s := by omega
  have H' : j + 1 + a = G.s + 1 := by omega
  have hm := G.hs
  obtain ⟨Tm, hTm, hO⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D G.k G.q G.unit _ _ (c.V j) (c.V (j + 1)) (G.FY j (a + 1) hb) (G.FY (j + 1) a H')
    c.ψ G.S.ψ hc.std G.char G.S.cond (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega))
    (G.latY j (a + 1) hb) (G.latY (j + 1) a H')).2 f hf
  obtain ⟨O, hO1, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := G.k) (Y := XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin a)
    (Y' := XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (a + 1))
  have R : (G.S.T (Fin D.R.t)).Regular := Chain.ofType_regular _ _ _ _ _
  let Φ : SB (Matrix (XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin a) (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (a + 1)) G.k) :=
    ⟨(G.S.T (Fin D.R.t)).Phi j a H, R.1 j a H⟩
  have e1 : Tm Φ = comb c.ψ _ _ (G.eg j) f := by
    rw [← hO O hO1]
    exact (G.eg_is j a H).2 Tm hTm O Φ hO1 rfl
  have hd := valuation_det_of_mem_stabLat ((R.2.2 j (a + 1) hb).2.2 x.2)
  have e2 : ((μ (j + 1))⁻¹ * μ'⁻¹) (Matrix.GeneralLinearGroup.det x.1) = 1 := by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, ← mul_inv, mul_comm, hT' _ hd, inv_one]
  have key := GlobalTheory.T.weilDatum_localModel_formula D G.k (ofSplit G.q) c.ψ _ _ χS χT ω hω (μ (j + 1))⁻¹ μ' (isComp_inv _ hS) hT _ _
    (G.FY j (a + 1) hb) (G.FY (j + 1) a H') Tm hTm h x.1 1 1 hl (isLoc_one _ _) Φ
    ((((G.S.T (Fin D.R.t)).lev j (a + 1) hb).lam x : ℂ) • Φ) (by
      rw [e2, inv_inv, Units.val_one, one_smul]
      exact (om_Phi G.S (Fin D.R.t) μ hμ hu j a H hb x).symm)
  rw [← e1, key, map_smul]

end GlobalTheory.SeeSaw.LocSrc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seesaw_first_flatMap_support_at_level_place : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp1 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ (x : GA D (c.V (j + 1))), SuppAt Gi.q.e (c.V (j + 1)) x → flatBF (t.sBF j (σ + 1) h) (t.om j (1, x) (comb c.ψ _ _ (Gi.eg j) F)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, SuppAt Gi.q.e (c.V (j + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  first | exact @GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at | exact GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at | (intros; apply GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem _root_.GlobalTheory.T.foldr_splitPlaceSecondCombinations_vacuum_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) F → F ≠ 0 → (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F ≠ 0 := by
  first | exact @GlobalTheory.VacComb.foldr_comb_ne_zero | exact GlobalTheory.VacComb.foldr_comb_ne_zero | (intros; apply GlobalTheory.VacComb.foldr_comb_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_flatMap_contraction_support_at_level_place : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp2 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F₁ : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F₁ → ∀ (F₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ), Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· = Gi.q.v) F₂ → ∀ (x : GA D (c.V (j + 1 + 1))), SuppAt Gi.q.e (c.V (j + 1 + 1)) x → c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (Gi.eg j) F₁) (t.om (j + 1) (1, x) (comb c.ψ _ _ (Gi.eg (j + 1)) F₂)) ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, SuppAt Gi.q.e (c.V (j + 1 + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  first | exact @GlobalTheory.SeeSaw.PlaceSupp.supp_ctr | exact GlobalTheory.SeeSaw.PlaceSupp.supp_ctr | (intros; apply GlobalTheory.SeeSaw.PlaceSupp.supp_ctr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaAt_seesawProductDatum_eq_vacuumCombinations : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ f₀ f, Vac ψ S T M M' (fun _ => True) f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ (prodDat L) f → IsThetaFunO ψ S T f → f = (List.finRange n).foldr (fun i g => comb ψ S T (L i).e (comb ψ S T (L i).o g)) f₀ ∧ ∀ (N : Lat S) (N' : Lat T), IsSelfDualC S N → IsSelfDualC T N' → (∀ i, IntIn (L i).q S (L i).FS N ∧ IntIn (L i).q T (L i).FT N') → (∀ p, (∀ i, p ≠ (L i).q.v) → latV S N (· = p) = latV S M (· = p) ∧ latV T N' (· = p) = latV T M' (· = p)) → Vac ψ S T N N' (fun _ => True) ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) f₀) := by
  first | exact @GlobalTheory.VecProd.thetaAt_prodDat | exact GlobalTheory.VecProd.thetaAt_prodDat | (intros; apply GlobalTheory.VecProd.thetaAt_prodDat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevZeroInd in

theorem GlobalTheory.LevZero.gen : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ Q : GA D (c.V 0) → Prop, (∀ k ∈ levS (c.V 0) st.β st.L, ∀ k' ∈ levS (c.V 0) st.β st.L, Q k → Q k' → Q (k * k')) → (∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (c.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * n * b)) → (∀ x ∈ GfC (c.X 0), b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b)) → (∀ k ∈ levS (c.V 0) st.β st.L, (∀ PP ∈ cm.Pg, redFn st.β PP (finE (c.V 0) k) = 1) → Q k) → ∀ k ∈ levS (c.V 0) st.β st.L, Q k := by
  intro D c v cm st b G h0 hB Q hmul hN hU hred
  classical
  have hst := hB.mem
  obtain ⟨hr, ξ, hL⟩ := hst.lev
  have hn : (c.V 0).rank = D.R.r := by rw [hst.rank]; show D.R.r + 0 * D.R.t = D.R.r; simp
  have key := fun x => GlobalTheory.LevYZero.lev_datY_zero (c.V 0) st.β st.L D.R.r D.R.t hr hn cm.Pg cm.P cm.chi ξ hL
    (Lev.finE (c.V 0) x) (GlobalTheory.LevSplit.finE_mem_UA _ x)
  have hSt : ∀ x ∈ levS (c.V 0) st.β st.L, Lev.finE (c.V 0) x ∈ St st.β := fun x hx => ((key x).1.1 hx.2).1
  have hRed : ∀ x ∈ levS (c.V 0) st.β st.L, ∀ PP : cm.Pg, ∃ z, GlobalTheory.LevZero.Red (G PP) PP.1 z (upperLeftBlock hr (redFn st.β PP.1 (Lev.finE (c.V 0) x))) :=
    fun x hx PP => (hB.grp _).1 ((key x).1.1 hx.2).2 PP
  have hmulm : ∀ x ∈ levS (c.V 0) st.β st.L, ∀ y ∈ levS (c.V 0) st.β st.L, x * y ∈ levS (c.V 0) st.β st.L :=
    fun x hx y hy => Subgroup.mul_mem _ hx hy
  have hinvm : ∀ x ∈ levS (c.V 0) st.β st.L, x⁻¹ ∈ levS (c.V 0) st.β st.L := fun x hx => Subgroup.inv_mem _ hx
  have claim : ∀ s : Finset (Pl D.host.E), ∀ k ∈ levS (c.V 0) st.β st.L,
      (∀ PP ∈ cm.Pg, PP ∉ s → redFn st.β PP (Lev.finE (c.V 0) k) = 1) → Q k := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro k hk h
      exact hred k hk fun PP hPP => h PP hPP (Finset.notMem_empty _)
    · intro a s ha ih k hk h
      by_cases haP : a ∈ cm.Pg
      · obtain ⟨z, hz⟩ := hRed k hk ⟨a, haP⟩
        obtain ⟨m, hm0, hQm, hmr, hmo⟩ := GlobalTheory.T.exists_indexZeroLevel_element_given_reduction_at_place cm st b G h0 hB Q hmul hN hU ⟨a, haP⟩ z
        have e1 : redFn st.β a (Lev.finE (c.V 0) m) = redFn st.β a (Lev.finE (c.V 0) k) :=
          reductionBlock_injective_of_eq hr hn ((GlobalTheory.LevZeroUniq.main (G ⟨a, haP⟩) a (hB.loc ⟨a, haP⟩).idem).2 z z _ _ (hmr hr) hz
            (by rw [inv_mul_cancel]; exact one_mem _))
        have hk1 : m⁻¹ * k ∈ levS (c.V 0) st.β st.L := hmulm _ (hinvm m hm0) k hk
        have hred1 : ∀ PP, redFn st.β PP (Lev.finE (c.V 0) (m⁻¹ * k)) =
            (redFn st.β PP (Lev.finE (c.V 0) m))⁻¹ * redFn st.β PP (Lev.finE (c.V 0) k) := fun PP => by
          rw [map_mul, map_inv, redFn_mul _ _ (inv_mem (hSt m hm0)) (hSt k hk), redFn_inv _ _ (hSt m hm0)]
        have hQ1 := ih (m⁻¹ * k) hk1 fun PP hPP hPs => by
          rw [hred1]
          by_cases hPa : PP = a
          · subst hPa
            rw [e1, inv_mul_cancel]
          · rw [hmo PP hPP hPa, h PP hPP (by simp [hPa, hPs]), inv_one, one_mul]
        have := hmul m hm0 _ hk1 hQm hQ1
        simpa using this
      · exact ih k hk fun PP hPP hPs => h PP hPP (by
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun e => haP (e ▸ hPP), hPs⟩)
  intro k hk
  exact claim cm.Pg k hk fun PP hPP h => absurd hPP h
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistCombination_splits_singlePlace_vacuum : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → v.Is → F.Pins w → ∀ j, j + 1 < D.R.m → ∀ (i : Fin F.r) Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∃ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ ∧ comb c.ψ _ _ (w.eQ j) Ψ₁ = comb c.ψ _ _ ((F.Q i).eL j) f₁ := by
  first | exact @GlobalTheory.TwistPlaceSplit.main | exact GlobalTheory.TwistPlaceSplit.main | (intros; apply GlobalTheory.TwistPlaceSplit.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem exists_clsT_of_pinTop : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∃ E : ClsT (realOf u R g s J) (tupOf R P u g t r k tl), E.Is := by
  intro B X I hI hPins l Z u G iG iGf Pl0 T F Ks iK iNK iA R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG
  choose h hh using fun c : (I.fm l u a).clsP => GlobalTheory.Core.Rk.Top.Model.hasMat_exists (K.y c)
  choose G' hG' using hG 0
  obtain ⟨hrep, hst⟩ := GlobalTheory.T.last_space_moved_level_class_points_representatives I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG h hh
  refine ⟨clsTop R g P r k tl s J UT h eW ε G', hrep, ?_, ?_, ?_⟩
  · exact GlobalTheory.T.lastPeriod_law_movedLevel I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG
  · intro n hn f v β c x hx
    show trc (k.eT n hn β) (f.1 v) (h c * x) = ellTop R P eW ε G' c f (J v x)
    rw [hTop.eT n hn β, trc_single_apply, ellTop_apply, GlobalTheory.T.form_translate_real_point_read_by_period I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG h hh G' (fun f => (hG' f).1) f v c x hx]
    ring
  · exact GlobalTheory.T.lastPeriod_tail_eq_lowered_evaluation_period I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG h hh hst G' (fun f => (hG' f).1)

end GlobalTheory.AdForm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_component_at_split_place : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → ∀ (PP : Pl D.host.E), QAll W PP → ∀ (l : LocX a (pk W).βX PP), LocY l y v.N (pk W).βY b (fun _ _ _ => 1) → (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (l.FX j hj)) → IsStdFr GlobalTheory.SymBridge.zPos l.FT → ∃ G : GlobalTheory.QTw.QGeo v (baseOf (pk W) (lvP W) u (mkGeo m b)) PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (G.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos G.FT ∧ G.z₀ = fun r => (ofSplit G.q).pr (a.ζ₀ r) := by
  first | exact @GlobalTheory.QGeoAt.geo_of_frames | exact GlobalTheory.QGeoAt.geo_of_frames | (intros; apply GlobalTheory.QGeoAt.geo_of_frames <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem levelLaw : ∀ D : D7, LevelLaw D := by
  intro D hgap c hc k hk s s' hs hs' p hp φ
  obtain ⟨h1, h2⟩ := GlobalTheory.T.thetaChainStep_vector_twoLevel_law D hgap c hc k hk s s' hs hs' p hp
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hc.inf hp.weil _ _ _ _ p.f hp.theta
      κ (Subgroup.mem_inf.1 hκ).1 1 (one_mem _) _ (h1 κ hκ) φ
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hc.inf hp.weil _ _ _ _ p.f hp.theta
      1 (one_mem _) κ (Subgroup.mem_inf.1 hκ).1 _ (h2 κ hκ) φ

end GlobalTheory.ChainOnto
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainCoef_vanishes_off_level : ∀ D : D7, CoefSupp D := by
  first | exact @GlobalTheory.ChainOnto.CoefSuppPf.coefSupp | exact GlobalTheory.ChainOnto.CoefSuppPf.coefSupp | (intros; apply GlobalTheory.ChainOnto.CoefSuppPf.coefSupp <;> assumption)
end
