module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle118
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle220
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle214
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle315
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle222
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle221
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator (FnModAt FnMod facTop facPen Zmu)
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis)

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))

def Bd {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    (c : K) (M : Submodule (𝓞 K) V) (M' : Submodule (𝓞 K) V') (k : V →ₗ[K] V') : Prop :=
  ∀ v ∈ localization₂ w.asIdeal M, c • k v ∈ localization₂ w.asIdeal M'

def WtUnit (S : GSD K) : Prop := ∀ d : S.D, w.valuation K ((Nat.card (MulAction.stabilizer S.G d) : ℕ) : K)⁻¹ ≤ 1

variable {w}

theorem Bd.transfer {S S' : GSD K} (g : S.G) (g' : S'.G) {M M₂ : Submodule (𝓞 K) S.V} {M' M₂' : Submodule (𝓞 K) S'.V}
    (hM : M₂ = M.map ((S.ρ g).restrictScalars (𝓞 K))) (hM' : M₂' = M'.map ((S'.ρ g').restrictScalars (𝓞 K)))
    {k k₂ : S.V →ₗ[K] S'.V} (hk : k₂ = (S'.ρ g') ∘ₗ k ∘ₗ (S.ρ g⁻¹)) {c : K} (h : Bd w c M₂ M₂' k₂) : Bd w c M M' k := by
  subst hM hM' hk
  rintro v ⟨s, hs, hv⟩
  obtain ⟨t, ht, y, hy, e⟩ := h (S.ρ g v) ⟨s, hs, s • v, hv, by simp⟩
  refine ⟨t, ht, ?_⟩
  have e1 : S.ρ g⁻¹ (S.ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e2 : y = t • c • k v := by
    have h2 := congrArg (S'.ρ g'⁻¹) e
    simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, e1, LinearMap.map_smul_of_tower, map_smul] at h2
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h2
    exact h2
  exact e2 ▸ hy

theorem opOf_bound {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec) (hw : WtUnit w S) {c : K}
    (hk : ∀ d d', Bd w c (S.Del d) (S'.Del d') (A.k d d')) {c₀ : K} (φ : S.EqFun)
    (hφ : ∀ d, c₀ • φ.1 d ∈ localization₂ w.asIdeal (S.Del d)) (d' : S'.D) :
    (c * c₀) • (A.opOf h s φ).1 d' ∈ localization₂ w.asIdeal (S'.Del d') := by
  change (c * c₀) • A.appOf h s φ d' ∈ _
  unfold ClsKer.appOf
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [smul_comm, wt_eq_card]
  refine smul_mem_localizationAt_of_le w _ (hw _) ?_
  rw [mul_smul, ← map_smul]
  exact hk _ _ _ (hφ _)

theorem comp_bound {S₀ S S₁ : GSD K} {Y : Cpl S} (A : CplKer S₀ S S₁ Y) (h : S.Ok) (s : S.Sec) (hw : WtUnit w S) {c₁ c₂ : K}
    (h1 : ∀ d₀ d, ∀ y ∈ Y.ys d, Bd w c₁ (S₀.Del d₀) (S.Del d) (A.k1 d₀ d y))
    (h2 : ∀ d d₁, ∀ y ∈ Y.ys d, Bd w c₂ (S.Del d) (S₁.Del d₁) (A.k2 d y d₁)) (d₀ : S₀.D) (d₁ : S₁.D) :
    Bd w (c₂ * c₁) (S₀.Del d₀) (S₁.Del d₁) ((A.comp h s).k d₀ d₁) := by
  intro v hv
  simp only [CplKer.comp, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [smul_comm, wt_eq_card]
  refine smul_mem_localizationAt_of_le w _ (hw _) ?_
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun y hy => ?_
  have hy' : y ∈ Y.ys (s.rep x) := by simpa using hy
  rw [mul_smul, ← map_smul]
  exact h2 _ _ y hy' _ (h1 _ _ y hy' v hv)

theorem colTo_bound {F : ℕ → GFam K} (kk : KerFam F) (hF : ∀ j, (F j).Ok) (c : ℕ → K)
    (φ : (F 0).Forms) (hφ : ∀ b d, (φ b).1 d ∈ localization₂ w.asIdeal (((F 0).mem b).Del d)) (n : ℕ)
    (hw : ∀ j < n, ∀ b, WtUnit w ((F j).mem b))
    (hk : ∀ j < n, ∀ al be d d', Bd w (c j) (((F j).mem al).Del d) (((F (j + 1)).mem be).Del d') ((kk j al be).k d d'))
    (b : (F n).β) (d : ((F n).mem b).D) :
    (∏ j ∈ Finset.range n, c j) • (kk.colTo hF n φ b).1 d ∈ localization₂ w.asIdeal (((F n).mem b).Del d) := by
  induction n with
  | zero => rw [Finset.prod_range_zero, one_smul]; exact hφ b d
  | succ n ih =>
    have e : (kk.colTo hF (n + 1) φ b).1 d =
        ∑ al, ((kk n al b).opOf (hF n al) ((F n).mem al).outSec (kk.colTo hF n φ al)).1 d := by
      change (KerFam.step kk hF n (kk.colTo hF n φ) b).1 d = _
      simp only [KerFam.step, GFam.Mat.opOf, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, Submodule.coe_sum, Finset.sum_apply]
    rw [e, Finset.smul_sum, Finset.prod_range_succ, mul_comm]
    exact Submodule.sum_mem _ fun al _ => opOf_bound _ _ _ (hw n (Nat.lt_succ_self n) al) (hk n (Nat.lt_succ_self n) al b) _
      (ih (fun j hj => hw j (Nat.lt_succ_of_lt hj)) (fun j hj => hk j (Nat.lt_succ_of_lt hj)) al) d

theorem colCpl_bound {F : ℕ → GFam K} (kk : KerFam F) (hF : ∀ j, (F j).Ok) {n : ℕ} (hw : ∀ j ≤ n, ∀ b, WtUnit w ((F j).mem b))
    (c : ℕ → K) {S S₁ : GSD K} {Y : Cpl S} (A : ∀ b : (F n).β, CplKer ((F n).mem b) S S₁ Y) (h : S.Ok) (hS : WtUnit w S)
    (hk : ∀ j < n, ∀ al be d d', Bd w (c j) (((F j).mem al).Del d) (((F (j + 1)).mem be).Del d') ((kk j al be).k d d'))
    (h1 : ∀ b d₀ d, ∀ y ∈ Y.ys d, Bd w (c n) (((F n).mem b).Del d₀) (S.Del d) ((A b).k1 d₀ d y))
    (h2 : ∀ b d d₁, ∀ y ∈ Y.ys d, Bd w (c (n + 1)) (S.Del d) (S₁.Del d₁) ((A b).k2 d y d₁))
    (φ : (F 0).Forms) (hφ : ∀ b d, (φ b).1 d ∈ localization₂ w.asIdeal (((F 0).mem b).Del d)) (d : S₁.D) :
    (∏ j ∈ Finset.range (n + 2), c j) • (colCpl kk hF n A h φ).1 d ∈ localization₂ w.asIdeal (S₁.Del d) := by
  have e : (colCpl kk hF n A h φ).1 d =
      ∑ b, (((A b).comp h S.outSec).opOf (hF n b) ((F n).mem b).outSec (kk.colTo hF n φ b)).1 d := by
    simp only [colCpl, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.coe_sum, Finset.sum_apply]
  have e2 : ∏ j ∈ Finset.range (n + 2), c j = (c (n + 1) * c n) * ∏ j ∈ Finset.range n, c j := by
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    ring
  rw [e, Finset.smul_sum, e2]
  exact Submodule.sum_mem _ fun b _ => opOf_bound _ _ _ (hw n le_rfl b) (comp_bound (A b) h _ hS (h1 b) (h2 b)) _
    (colTo_bound kk hF c φ hφ n (fun j hj => hw j hj.le) hk b) d

end Generic

theorem not_dvd_card_stab_frm {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (d : DecoF X.E n ST SG Q)
    [Finite (MulAction.stabilizer (FrmG Λ Θ) d)] {p : ℕ} (hp : p.Prime) (hb : Module.finrank ℚ X.E * n + 1 < p) :
    ¬ p ∣ Nat.card (MulAction.stabilizer (FrmG Λ Θ) d) := by
  refine not_dvd_card_of_injective (((UF X.E n).subtype.comp (MonoidHom.fst _ _)).comp (Subgroup.subtype _)) ?_ hp hb
  rw [injective_iff_map_eq_one]
  rintro ⟨⟨γ, h, c⟩, hs⟩ h1
  have h2 : γ = 1 := Subtype.ext h1
  subst h2
  have h3 : h.1 = 1 := glg_eq_one_of_fix d.1.1 h.1 (congrArg (fun x : DecoF X.E n ST SG Q => x.1.1.1) hs)
  have h4 : c.1 = 1 := by
    funext P
    have h5 : (1 : Sp X.E n ≃ₗ[X.E] Sp X.E n) * d.1.2 P * ((c.1 P)⁻¹).1 = d.1.2 P :=
      congrArg (fun x : DecoF X.E n ST SG Q => x.1.2 P) hs
    rw [one_mul, mul_eq_left] at h5
    exact inv_eq_one.1 (Subtype.ext h5)
  exact Subtype.ext (Prod.ext rfl (Prod.ext (Subtype.ext h3) (Subtype.ext h4)))

theorem stdOver_tilH {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} (hN : N = n + 1)
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ v : SG, pi ∉ v.1.asIdeal)
    (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) {p : ℕ} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver p d.1.N) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver p (DecoSet.tilH (ST := ST) hN pi d).1.N := by
  subst hN
  change _root_.GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver p (DecoSet.til (ST := ST) pi d).1.N
  rw [DecoSet.til_val d hT hG]
  intro P hP
  ext x
  change x ∈ localization₂ P.asIdeal (tilN d.1.N) ↔ _
  rw [mem_localization_tilN, h P hP, GlobalTheory.TopStep.mem_stdAt, GlobalTheory.TopStep.mem_stdAt, Fin.forall_fin_succ']
  rfl

section Column

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Amb X)

theorem exists_std_pt (hM : StdMove) (hPr : Pr.Ok) (i : Fin 2) (u : Pr.Word) (j : ℕ) (b : L.β j)
    (p : ((chF W sel mu L u j).mem b).D) : ∃ g : ((chF W sel mu L u j).mem b).G, _root_.GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (Pr.g i) (DecoF.deco (g • p)).1.N := by
  obtain ⟨γ, hγ⟩ := hM X Pr hPr i _ (DecoF.deco p).1.N ⟨(DecoF.deco p).2.lat, (DecoF.deco p).2.uni⟩
  exact ⟨(γ, 1, 1), hγ⟩

theorem evGSD_del_smul (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hS : Pr.T u ∈ S) (P : LevFam X.E X.K R.r Pr.vGs)
    (γ : UF X.E (R.N R.m - 1)) (d : (evGSD W Ch sel mu P u).D) :
    (evGSD W Ch sel mu P u).Del (((γ, 1) : (evGSD W Ch sel mu P u).G) • d) =
      ((evGSD W Ch sel mu P u).Del d).map (((evGSD W Ch sel mu P u).ρ (γ, 1)).restrictScalars (𝓞 X.K)) := by
  have h1 := DecoSet.tilH_smul (ST := Pr.vT u) (N_m_succ R) (γ, (1 : GLG (E := X.E) (n := _) (SG := rowSG Pr sel mu))) d (conj_piT_notMem hPr u)
    (piT_notMem_rowSG sel mu hPr hsel u hS)
  have h2 : (evGSD W Ch sel mu P u).ρ (γ, 1) = (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho (extUH (N_m_succ R) γ) := by
    change ((((rowTy Ch sel mu P).inv.chr 1)⁻¹ : X.Kˣ) : X.K) •
      (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho (extUH (N_m_succ R) γ) = _
    rw [map_one, inv_one, Units.val_one, one_smul]
  rw [h2]
  refine Eq.trans ?_ (colVal_del_smul W u R.m (extUH (N_m_succ R) γ, extGH (N_m_succ R) 1) (tilQ sel mu u d))
  exact congrArg (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).Del h1

theorem wtUnit_chF (hX : X.Ok) (u : Pr.Word) (hF : ∀ j, (chF W sel mu L u j).Ok) {p : ℕ} (hp : p.Prime)
    (hb : 2 * X.f * R.N R.m + 1 < p) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) {j : ℕ} (hj : j ≤ R.m)
    (b : L.β j) : WtUnit w ((chF W sel mu L u j).mem b) := by
  intro d
  have hE : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
    rfl
  have := (hF j b).fin_stab d
  have hN : R.N j ≤ R.N R.m := Examples₂.N_mono hj
  exact (valuation_inv_natCast w hp hw (not_dvd_card_stab_frm (L.levG j b) (L.levQ j b) d hp
    (lt_of_le_of_lt (by rw [hE]; gcongr) hb))).le

end Column

end GlobalTheory.ColPeriod
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

noncomputable section

namespace GlobalTheory.Cong.AdaptLevFix

open GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem eq_one_of_forall_cLoc {x : UA E a} (hx : x ∈ finU (E := E) (n := a)) (h : ∀ u, cLoc u x = 1) : x = 1 := by
  have hinf : cInf x = 1 := MonoidHom.mem_ker.1 hx
  refine Subtype.ext (ga_ext ?_ ?_)
  · exact hinf.trans (map_one _).symm
  · rw [Subgroup.coe_one, map_one]
    refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
    have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (h u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    split_ifs with hij <;> simp [hij] <;> rfl

theorem isCompact_integral :
    IsCompact {k : finU (E := E) (n := a) | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a)} := by
  have e' : ∀ k : finU (E := E) (n := a), k ∈ (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap
      (GlobalTheory.BCT.GlobLev.finPart E a) ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a) := by
    intro k
    rw [Subgroup.mem_comap, GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
    simp only [GlobalTheory.BCT.GlobLev.mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
    exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
      fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩
  have e : {k : finU (E := E) (n := a) | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a)} =
      ((GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap (GlobalTheory.BCT.GlobLev.finPart E a) :
        Set (finU (E := E) (n := a))) := by
    ext k
    exact (e' k).symm
  have hO : IsOpen ((GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap (GlobalTheory.BCT.GlobLev.finPart E a) :
      Set (finU (E := E) (n := a))) :=
    (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a).preimage GlobalTheory.BCT.GlobLev.continuous_finPart
  rw [e]
  refine IsCompact.of_isClosed_subset (GlobalTheory.BCT.GlobLev.isClosedEmbedding_finU.isCompact_preimage
      ((GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E a).image GlobalTheory.BCT.GlobLev.continuous_finGL_ad))
      (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨GlobalTheory.BCT.GlobLev.finPart E a x, hx, ?_⟩
  have h1 : Matrix.GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

theorem exists_finite_fix {φ : UA E a → ℂ} (hφ : IsAutFormU φ) :
    ∃ t : Finset (HeightOneSpectrum (𝓞 E)), ∀ k ∈ finU (E := E) (n := a), (∀ u, cLoc u k ∈ GlobalTheory.LFun.KGL u (n := a)) →
      (∀ u ∈ t, cLoc u k = 1) → RU E a k φ = φ := by
  haveI : ∀ u : HeightOneSpectrum (𝓞 E), T2Space (GL (Fin a) (u.adicCompletion E)) := fun u =>
    Units.isEmbedding_embedProduct.t2Space
  have hc := (isCompact_integral (E := E) (a := a)).diff hφ.level
  have hcov : {k : finU (E := E) (n := a) | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a)} \ {k : finU (E := E) (n := a) | RU E a k φ = φ} ⊆
      ⋃ u, {k : finU (E := E) (n := a) | cLoc u k.1 ≠ 1} := by
    rintro k ⟨-, hk⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hne
    push_neg at hne
    apply hk
    show RU E a k.1 φ = φ
    rw [eq_one_of_forall_cLoc k.2 hne, map_one]
    rfl
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover _ (fun u => isOpen_ne_fun
    ((GlobalTheory.BCT.GlobLev.continuous_cLoc u).comp continuous_subtype_val) continuous_const) hcov
  refine ⟨t, fun k hk hint h1 => ?_⟩
  by_contra hne
  have := ht (show (⟨k, hk⟩ : finU (E := E) (n := a)) ∈ _ from ⟨hint, hne⟩)
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
  obtain ⟨u, hu, hne'⟩ := this
  exact hne' (h1 u hu)

theorem one_of_cLoc_eq_one {q : HeightOneSpectrum (𝓞 E)} {z : UA E a} (h : cLoc q z = 1) :
    ∀ u, ¬ Apart u q → cLoc u z = 1 := by
  intro u hu
  by_cases hq : IsSplitAt q
  · exact GlobalTheory.Cong.LevelExt.one_of_cLoc hq z h u hu
  · rw [eq_of_not_apart_of_not_split hq hu]
    exact h

theorem peel (φ : UA E a → ℂ) (S : Set (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ k ∈ finU (E := E) (n := a), (∀ u, cLoc u k ∈ GlobalTheory.LFun.KGL u (n := a)) → (∀ u ∈ S, cLoc u k = 1) → RU E a k φ = φ)
    (Q : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ x ∈ finU (E := E) (n := a), (∀ u, (∀ q ∈ Q, Apart u q) → (u ∈ S → cLoc u x = 1) ∧ cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a)) →
      (∀ q ∈ Q, ∃ y ∈ locU a q, RU E a y φ = φ ∧ cLoc q y = cLoc q x) → RU E a x φ = φ := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
    intro x hx h1 _
    exact hS x hx (fun u => (h1 u (by simp)).2) (fun u hu => (h1 u (by simp)).1 hu)
  | @insert q Q hqQ ih =>
    intro x hx h1 h2
    obtain ⟨y, hyl, hyφ, hyq⟩ := h2 q (Finset.mem_insert_self q Q)
    have hyf : y ∈ finU (E := E) (n := a) := ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).1
    have hya : ∀ u, Apart u q → cLoc u y = 1 := ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).2
    have hq1 : cLoc q (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hyq, inv_mul_cancel]
    have hfib : ∀ u, ¬ Apart u q → cLoc u (y⁻¹ * x) = 1 := one_of_cLoc_eq_one hq1
    have happ : ∀ u, Apart u q → cLoc u (y⁻¹ * x) = cLoc u x := fun u hu => by
      rw [map_mul, map_inv, hya u hu, inv_one, one_mul]
    have key : RU E a (y⁻¹ * x) φ = φ := by
      refine ih (y⁻¹ * x) (mul_mem (inv_mem hyf) hx) (fun u hu => ?_) (fun q' hq' => ?_)
      · by_cases huq : Apart u q
        · rw [happ u huq]
          exact h1 u (fun p hp => by
            rcases Finset.mem_insert.1 hp with rfl | hp
            · exact huq
            · exact hu p hp)
        · rw [hfib u huq]
          exact ⟨fun _ => rfl, Subgroup.one_mem _⟩
      · by_cases hqq : Apart q' q
        · obtain ⟨y', hy'l, hy'φ, hy'q⟩ := h2 q' (Finset.mem_insert_of_mem hq')
          exact ⟨y', hy'l, hy'φ, hy'q.trans (happ q' hqq).symm⟩
        · exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl, by rw [map_one, hfib q' hqq]⟩
    have hxe : x = y * (y⁻¹ * x) := by rw [mul_inv_cancel_left]
    rw [hxe, map_mul, Module.End.mul_apply, key, hyφ]

end GlobalTheory.Cong.AdaptLevFix


open GlobalTheory.Cong.AdaptLevFix in
theorem GlobalTheory.Cong.AdaptLev.fixed_of_levelOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → ∀ φ : UA E a → ℂ, IsAutFormU φ → (∀ w, Apart w w₀ → ∀ x ∈ H w, RU E a x φ = φ) → ∀ x ∈ GlobalTheory.Cong.AdaptLev.levelOf a w₀ H, RU E a x φ = φ := by
  intro E _ _ _ a w₀ H hHle _ _ _ hcof φ hφ hfix x hx
  classical
  obtain ⟨t, ht⟩ := exists_finite_fix hφ
  have hT : {w | ¬ H w = intU a w}.Finite := Filter.eventually_cofinite.1 hcof
  let Q : Finset (HeightOneSpectrum (𝓞 E)) := (t ∪ hT.toFinset).filter (fun w => Apart w w₀)
  obtain ⟨hxf, hx1, hxH⟩ := mem_levelOf.1 hx
  refine peel φ (t : Set _) (fun k hk hi h1 => ht k hk hi h1) Q x hxf (fun u hu => ?_) (fun q hq => ?_)
  · by_cases hu0 : Apart u w₀
    · have huQ : u ∉ Q := fun h => hu u h rfl
      have hut : u ∉ t := fun h => huQ (Finset.mem_filter.2 ⟨Finset.mem_union_left _ h, hu0⟩)
      have huT : H u = intU a u := by
        by_contra h
        exact huQ (Finset.mem_filter.2 ⟨Finset.mem_union_right _ (hT.mem_toFinset.2 h), hu0⟩)
      obtain ⟨y, hy, hyx⟩ := hxH u hu0
      rw [huT] at hy
      refine ⟨fun h => absurd h hut, ?_⟩
      rw [← hyx]
      exact (mem_intU.1 hy).2 u (fun h => h rfl)
    · rw [hx1 u hu0]
      exact ⟨fun _ => rfl, Subgroup.one_mem _⟩
  · have hq0 : Apart q w₀ := (Finset.mem_filter.1 hq).2
    obtain ⟨y, hy, hyx⟩ := hxH q hq0
    exact ⟨y, hHle q hy, hfix q hq0 y hy, hyx⟩
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.Cong

theorem exists_weight_of_isAutRepU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ)
    (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∃ lam : (E →+* ℂ) → DomWeight a, ∀ τ, HasWeightAt U τ (lam τ) := by
  intro E _ _ _ a U hU
  choose lam hlam using fun τ : E →+* ℂ => (GlobalTheory.DefU.AU.existsUnique_hasWt E a (GlobalTheory.DefU.AU.mk ⟨U, hU⟩) τ).exists
  exact ⟨lam, hlam⟩

end GlobalTheory.Cong
end

section

noncomputable section

namespace GlobalTheory.InverseSeriesIntegral

open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (wToC LTIso)
open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.L2.KerInert.BeCob (vLT eLT)
open GlobalTheory.CurveDictionary (cc_lgF' lgF_eq_logF)

theorem exists_witt_series_inverse_formalGroup_iso {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) :
    ∃ w : PowerSeries (Formalism.MainNotions.FormalGroupSystem.WW l), PowerSeries.map (wToC l) w = vLT hLT := by
  apply _root_.GlobalTheory.ShortModelTie.exists_witt_series_inverse_formalGroup_iso <;> assumption

theorem v_integral : ∀ (l : ℕ) [Fact l.Prime] (g : G1 l), g.Ok → ∀ (hLT : LTIso g) (n : ℕ),
    ‖PowerSeries.coeff n (vLT hLT)‖ ≤ 1 := by
  intro l _ g hOk hLT n
  obtain ⟨w, hw⟩ := exists_witt_series_inverse_formalGroup_iso hOk hLT
  rw [← hw, PowerSeries.coeff_map]
  have := Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)
  simpa using this

end GlobalTheory.InverseSeriesIntegral
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

theorem _root_.GlobalTheory.T.precedingStepDatum_integral_away_from_levels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ al p₀ p Yb x, IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl1 (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 al p₀ p Yb x)) := by
  first | exact @GlobalTheory.xiCpl1_intOff | exact GlobalTheory.xiCpl1_intOff | (intros; apply GlobalTheory.xiCpl1_intOff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ggeo.FracLocal

theorem isFractionRing_gat : ∀ {D : D7} (Gl : G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf :=
  fun {_} Gl u w hg => GlobalTheory.TwV.Lt.fracAt Gl u w hg

end GlobalTheory.Ggeo.FracLocal
end

section

open NumberField

namespace GlobalTheory.RealGal

theorem QCM.even_finrank_maximalRealSubfield (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    (Q : GlobalTheory.RealGal.QCM E Ω) : Even (Module.finrank ℚ (maximalRealSubfield Q.K)) := by
  have h1 := (letI : Module.Free (maximalRealSubfield Q.K) Q.K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield Q.K) Q.K)
  have h2 := Module.finrank_mul_finrank ℚ E Q.K
  have h3 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield Q.K) Q.K] at h1
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h3
  rw [Q.two] at h2
  exact ⟨Module.finrank ℚ (maximalRealSubfield E), by omega⟩

end GlobalTheory.RealGal
end
