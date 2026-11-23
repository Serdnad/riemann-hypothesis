module

public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle112
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle282
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle281
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle297
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle306
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle123
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle263
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle304
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle019
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.Bundle001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle011
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle014
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigIsoInert

def stabRt {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (f : GAf L n → W) : Subgroup (GAf L n) where
  carrier := {κ | NG.rt L n κ f = f}
  one_mem' := funext fun y => by
    show f (y * 1) = f y
    rw [mul_one]
  mul_mem' := by
    intro a b ha hb
    have ha' : NG.rt L n a f = f := ha
    have hb' : NG.rt L n b f = f := hb
    show NG.rt L n (a * b) f = f
    have e : NG.rt L n (a * b) f = NG.rt L n a (NG.rt L n b f) := funext fun y => by
      show f (y * (a * b)) = f (y * a * b)
      rw [mul_assoc]
    rw [e, hb', ha']
  inv_mem' := by
    intro a ha
    have ha' : NG.rt L n a f = f := ha
    show NG.rt L n a⁻¹ f = f
    calc NG.rt L n a⁻¹ f = NG.rt L n a⁻¹ (NG.rt L n a f) := by rw [ha']
      _ = f := funext fun y => by
        show f (y * a⁻¹ * a) = f y
        rw [inv_mul_cancel_right]

theorem eig_of_irr (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
    (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (w : HeightOneSpectrum (𝓞 L)) (hw : NG.OverPl w v) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ)
    (hsat : NG.SatAt { a with S := S, irrS := hS } Dv α) (f : GAf L n → a.W) (hfS : f ∈ S)
    (hfK : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f)
    (h : Formalism.UG.GU Dv.σw n → ℂ) (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) :
    heckeFunI L n (Umax L n) Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f := by
  let U : Subgroup (GAf L n) := Umax L n ⊓ stabRt f
  have hU : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n) :=
    fun κ hκ => ⟨fun h1 => h1.1, fun h1 => ⟨h1, hfK κ h1 hκ⟩⟩
  have e1 := GlobalTheory.InertSph.satU_of_fixed L n a S hS v w Dv α hw hsat U hU f hfS (fun κ hκ => hκ.2) h hh
  have hK : ∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n :=
    fun κ hκ _ => ⟨GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv κ, GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv κ hκ _⟩
  rw [GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK (Umax L n) U (fun _ _ => Iff.rfl) hU a.W h hh.1 f hfK]
  exact e1

theorem eig_of_isoTyp_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → ∀ φ ∈ NG.isoTyp π.ρ π.S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), heckeFunI L n (Umax L n) Dv h φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  intro L _ _ _ n π v w hw Dv α hsat φ hφ hφK h hh
  have hfin : ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) →
      ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
        (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0} :=
    fun U hU h hh => GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv (fun s => GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram s)
      (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv) U hU h hh
  set c := Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α with hc

  have hirr : ∀ S' : Submodule ℂ (GAf L n → π.W), NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S' → ∀ f ∈ S',
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) → heckeFunI L n (Umax L n) Dv h f = c • f := by
    rintro S' ⟨hS', hiso⟩ f hf hfK
    have hsat' : NG.SatAt { π.toAlgWt with S := S', irrS := hS' } Dv α :=
      GlobalTheory.SatIso.satAt_of_iso L n π { π.toAlgWt with S := S', irrS := hS' } ⟨⟨LinearEquiv.refl ℂ _, fun _ _ => rfl⟩, hiso⟩ v w Dv α hfin hsat
    exact eig_of_irr L n π.toAlgWt S' hS' v w hw Dv α hsat' f hf hfK h hh

  obtain ⟨C, cf, xs, hC⟩ := GlobalTheory.SatIso.heckeFunI_eq_sum Dv (Umax L n) h (hfin (Umax L n) (fun _ _ => Iff.rfl) h hh)
  have hadd : ∀ y z : GAf L n → π.W, heckeFunI L n (Umax L n) Dv h (y + z) =
      heckeFunI L n (Umax L n) Dv h y + heckeFunI L n (Umax L n) Dv h z := by
    intro y z
    rw [hC π.W, hC π.W, hC π.W, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_add (f := _), smul_add]
  have hzero : heckeFunI L n (Umax L n) Dv h (0 : GAf L n → π.W) = 0 := by
    rw [hC π.W]
    simp
  have key : ∀ t : Finset (Submodule ℂ (GAf L n → π.W)),
      (↑t ⊆ {S' | NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S'}) → ∀ f ∈ (⨆ i ∈ t, i),
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) → heckeFunI L n (Umax L n) Dv h f = c • f := by
    classical
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _ f hf _
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
      subst hf
      rw [hzero, smul_zero]
    | insert a t ha ih =>
      intro hsub f hf hfix
      have haF : NG.IsIrrRep π.ρ a ∧ NG.IsoRep π.S a := hsub (Finset.mem_insert_self a t)
      have hsF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S'} :=
        fun x hx => hsub (Finset.mem_insert_of_mem hx)
      rw [Finset.iSup_insert] at hf
      have hMst : ∀ g, ∀ y ∈ (⨆ i ∈ t, i), NG.rt L n g y ∈ (⨆ i ∈ t, i) :=
        GlobalTheory.IsoFix.iSup_finset_stable t (fun i hi => (hsF hi).1.1.stable)
      by_cases hd : a ⊓ (⨆ i ∈ t, i) = ⊥
      · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
        have hyz : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ y = y ∧ NG.rt L n κ z = z := by
          intro κ hκ hκt
          have e := hfix κ hκ hκt
          rw [map_add (f := _)] at e
          have h1 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
          have hm : NG.rt L n κ y - y ∈ a ⊓ (⨆ i ∈ t, i) :=
            ⟨a.sub_mem (haF.1.1.stable κ y hy) hy, h1 ▸ Submodule.sub_mem _ hz (hMst κ z hz)⟩
          rw [hd, Submodule.mem_bot] at hm
          refine ⟨sub_eq_zero.1 hm, ?_⟩
          rw [hm] at h1
          exact (sub_eq_zero.1 h1.symm).symm
        rw [hadd, hirr a haF y hy (fun κ hκ hκt => (hyz κ hκ hκt).1),
          ih hsF z hz (fun κ hκ hκt => (hyz κ hκ hκt).2), smul_add]
      · have hsubrep : NG.IsSubrep π.ρ (a ⊓ ⨆ i ∈ t, i) :=
          ⟨inf_le_left.trans haF.1.1.le, fun g y hy => ⟨haF.1.1.stable g y hy.1, hMst g y hy.2⟩⟩
        have heq : a ⊓ (⨆ i ∈ t, i) = a := (haF.1.2.2 _ hsubrep inf_le_left).resolve_left hd
        have hle : a ≤ ⨆ i ∈ t, i := heq ▸ inf_le_right
        exact ih hsF f ((sup_le hle le_rfl) hf) hfix
  unfold NG.isoTyp at hφ
  obtain ⟨s, hs, hfs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hφ
  exact key s hs φ hfs (fun κ hκ hκt => hφK κ hκ hκt)

end GlobalTheory.EigIsoInert
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem hypFree_of_top_int : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt → t.HypFree := by
  intro D L hT Gi Gl K Y cX ex t hTop hInt u μ i hi c c' hnp
  have hsd := (GlobalTheory.TieLat.tie_AA_fg_and_sd D L hT Gi Gl K Y cX ex t).2 u μ
  refine ⟨hsd i c, hsd (i + 1) c', ?_⟩
  have hm : D.R.m = t.m2 + 2 := (t.idx_ok μ).hm
  obtain ⟨-, -, pt, ix, yb, pT, -, -, -, -, -, hpin, -⟩ := hTop u μ
  have hi' : i = t.m2 + 1 := by
    by_contra hne
    exact hnp (hpin (i + 1) (by omega) c')
  subst hi'
  exact hInt u μ c c' hnp

theorem kerEntTied_hyp : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.TopPinned → t.Hyp := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 hQ hTop
  have h0 : t.Hyp0 := by
    first
      | exact GlobalTheory.T.kernelDatum_periodLatticeIdeal_fg_of_heckeCharacters D L hT Gi Gl K Y cX ex t h1 h2 hQ
      | exact GlobalTheory.T.kernelDatum_periodLatticeIdeal_fg_of_heckeCharacters D L hT Gi Gl K Y cX ex t h1 h2
  exact hypotheses_of_base_hypotheses D L hT Gi Gl K Y cX ex t h0
    (hypFree_of_top_int D L hT Gi Gl K Y cX ex t hTop (GlobalTheory.T.lastStepKernelData_integral_awayFromLevels D L hT Gi Gl K Y cX ex t hTop))

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.TwU.XiTwo

section Abs

open Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Mv
open Formalism.L2.KerInert Formalism.L2.KerInert.PullbackComparison Formalism.L2.KerInert.RepComb

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [DecidableEq W]
  (H : Sesq V) (α : V → ℂ) (H₁ : Sesq W) (α₁ : W → ℂ) (T : V ≃+ W)

omit [DecidableEq W] in
theorem brk_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (y t : V) : brk H₁ (T y) (T t) = brk H y t := by
  unfold brk altE
  rw [hH]

theorem hatS_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (vol : ℝ) (SA : Finset V) (Φ : W → ℂ) (x y : V) :
    hatS H₁ vol (SA.image T) (fun s => Φ (s - T x)) (T y) = hatS H vol SA (fun s => Φ (T (s - x))) y := by
  unfold hatS
  rw [Finset.card_image_of_injective _ T.injective, Finset.sum_image (fun a _ b _ h => T.injective h)]
  congr 2
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [brk_map H H₁ T hH]
  simp only [map_sub]

omit [DecidableEq W] in
theorem opU_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (x : V) (e : W → ℂ) (z : V) :
    opU H₁ (T x) e (T z) = opU H x (fun v => e (T v)) z := by
  unfold opU
  rw [hH, hH, ← map_add (f := _)]

theorem xiL_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (hα : ∀ x, α₁ (T x) = α x) (vol : ℝ) (SX SA SB : Finset V)
    (Φ e : W → ℂ) (z : V) :
    xiL H₁ α₁ vol (SX.image T) (SA.image T) (SB.image T) Φ e (T z) =
      xiL H α vol SX SA SB (fun v => Φ (T v)) (fun v => e (T v)) z := by
  rw [xiL_expand, xiL_expand, Finset.sum_image (fun a _ b _ h => T.injective h)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_image (fun a _ b _ h => T.injective h)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hatS_map H H₁ T hH, hα, hα, hH, hH, ← map_add (f := _), opU_map H H₁ T hH]


omit [Module ℂ V] [Module ℂ W] in
theorem isReps_image {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S)
    (h1 : ∀ x, T x ∈ M₁ ↔ x ∈ Λ₁) (h2 : ∀ x, T x ∈ M₂ ↔ x ∈ Λ₂) : IsReps M₁ M₂ (S.image T) := by
  first
  | exact @_root_.GlobalTheory.RepresentativesImage.isReps_image
  | exact _root_.GlobalTheory.RepresentativesImage.isReps_image
  | (apply _root_.GlobalTheory.RepresentativesImage.isReps_image <;> assumption)
  | (intros; apply _root_.GlobalTheory.RepresentativesImage.isReps_image <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RepresentativesImage.isReps_image <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RepresentativesImage.isReps_image ..)


omit [Module ℂ V] [Module ℂ W] in
theorem repsOf_eq_image {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} (hS : ∃ S, IsReps Λ₁ Λ₂ S)
    (h1 : ∀ x, T x ∈ M₁ ↔ x ∈ Λ₁) (h2 : ∀ x, T x ∈ M₂ ↔ x ∈ Λ₂) :
    ∃ S : Finset V, IsReps Λ₁ Λ₂ S ∧ repsOf M₁ M₂ = S.image T := by
  classical
  obtain ⟨S, hS⟩ := hS
  have hex : ∃ S₁, IsReps M₁ M₂ S₁ := ⟨_, isReps_image T hS h1 h2⟩
  have hR : IsReps M₁ M₂ (repsOf M₁ M₂) := by
    unfold repsOf
    exact Classical.epsilon_spec hex
  refine ⟨(repsOf M₁ M₂).image T.symm, isReps_image T.symm hR (fun x => ?_) (fun x => ?_), ?_⟩
  · rw [← h1, AddEquiv.apply_symm_apply]
  · rw [← h2, AddEquiv.apply_symm_apply]
  · rw [Finset.image_image]
    have : (T ∘ T.symm : W → W) = id := funext fun x => T.apply_symm_apply x
    rw [this, Finset.image_id]

end Abs

section Main

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xiL_two : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (H₁ : Formalism.L2.Th1.H.Sesq W) (α₁ : W → ℂ) (T : V ≃+ W), (∀ x y, H₁ (T x) (T y) = H x y) → (∀ x, α₁ (T x) = α x) → ∀ (A B Λ : AddSubgroup V) (A₁ B₁ Λ₁ : AddSubgroup W), SplitHyp H α A B Λ → (∀ x, T x ∈ Λ₁ ↔ x ∈ Λ) → (∀ x, T x ∈ A₁ ↔ x ∈ A) → (∀ x, T x ∈ B₁ ↔ x ∈ B) → (∃ S, Formalism.L2.Th1.H.IsReps Λ A S) → (∃ S, Formalism.L2.Th1.H.IsReps B (Λ ⊓ A) S) → (∃ S, Formalism.L2.Th1.H.IsReps Λ B S) → ∀ (vol : ℝ) (θ Φ : W → ℂ), (fun v => θ (T v)) ∈ Formalism.L2.Th1.H.fixedBy H α Λ → InvOn A B (fun v => Φ (T v)) → ∀ z, xiL H₁ α₁ vol (repsOf Λ₁ A₁) (repsOf B₁ (Λ₁ ⊓ A₁)) (repsOf Λ₁ B₁) Φ θ (T z) = xiL H α vol (repsOf Λ A) (repsOf B (Λ ⊓ A)) (repsOf Λ B) (fun v => Φ (T v)) (fun v => θ (T v)) z := by
  intro V W _ _ _ _ H α H₁ α₁ T hH hα A B Λ A₁ B₁ Λ₁ hyp hΛ hA hB hX hSA hSB vol θ Φ hθ hΦ z
  classical
  have hΛA : ∀ x, T x ∈ Λ₁ ⊓ A₁ ↔ x ∈ Λ ⊓ A := fun x => by
    rw [AddSubgroup.mem_inf, AddSubgroup.mem_inf, hΛ, hA]
  obtain ⟨SX, rX, eX⟩ := repsOf_eq_image T hX hΛ hA
  obtain ⟨SA, rA, eA⟩ := repsOf_eq_image T hSA hB hΛA
  obtain ⟨SB, rB, eB⟩ := repsOf_eq_image T hSB hΛ hB
  rw [eX, eA, eB, xiL_map H α H₁ α₁ T hH hα]
  exact twist_representatives V H α A B Λ hyp _ _ _ _ _ _ (GlobalTheory.TwU.KerMove.repsOf_of_exists hX) (GlobalTheory.TwU.KerMove.repsOf_of_exists hSA)
    (GlobalTheory.TwU.KerMove.repsOf_of_exists hSB) rX rA rB vol _ hθ _ hΦ z

end Main

end GlobalTheory.TwU.XiTwo
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.LocCarry

theorem prV_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    (fun i => prV (E := E) v ((M *ᵥ w) i)) = M.map (prV (E := E) v) *ᵥ (fun i => prV (E := E) v (w i)) := by
  ext i

  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem coe_bc_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    (((bc (prV (E := E) v) x)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
      Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) =
      ((x⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _).map (prV (E := E) v) := by
  rw [← map_inv]
  rfl

theorem coe_bc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    ((bc (prV (E := E) v) x : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
      Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) =
      (x : Matrix (Fin N) (Fin N) _).map (prV (E := E) v) := rfl

theorem mem_latS_latAd_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)),
    Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fin N → E ⊗[F] v.adicCompletion F),
      z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (latAd x Lb) ↔
        (((bc (prV (E := E) v) x)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
          latS (F := F) (v.adicCompletion F) (intV E v) Lb := by
  intro F E _ _ _ _ _ _ N x Lb hfin hspan v z
  have hrec := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin N) Lb hfin hspan x
  have hpr : ∀ y : Fin N → E ⊗[F] v.adicCompletion F,
      (fun i => prV (E := E) v (Formalism.UG.P.afsplitIE v (y i))) = y := fun y => by
    ext i; exact Formalism.UG.P.afsplit_prV_IE v (y i)
  have hlat : Formalism.L2.PairingIndexBounds.F.latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
  rw [hlat]
  constructor
  · intro hz
    have h1 := Formalism.L2.Geo.Def.PN.IE_latS (Formalism.UG.CS.globLat x Lb) v hz
    have h2 := (hrec _).1 h1
    have h3 := Formalism.L2.Geo.Def.PN.prV_latS Lb v h2
    rw [prV_mulVec, hpr, ← coe_bc_inv] at h3
    exact h3
  · intro hz
    have h1 := Formalism.L2.Geo.Def.PN.IE_latS Lb v hz
    set u : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
      ((x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _) *ᵥ
        (fun i => Formalism.UG.P.afsplitIE v (((((bc (prV (E := E) v) x)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
          Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ z) i)) with hu
    have h2 : u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.UG.CS.globLat x Lb) := by
      refine (hrec u).2 ?_
      rw [hu, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact h1
    have h3 := Formalism.L2.Geo.Def.PN.prV_latS (Formalism.UG.CS.globLat x Lb) v h2
    rw [hu, prV_mulVec, hpr, ← coe_bc, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h3
    exact h3

end GlobalTheory.LocCarry
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.CompanFG

theorem fg_of_le_fg {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    {P Q : Submodule R M} (hQ : Q.FG) (hPQ : P ≤ Q) : P.FG := by
  haveI := isNoetherian_of_fg_of_noetherian Q hQ
  have h1 : (P.comap Q.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map Q.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hPQ] at h2

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ c • v ∈ Lb := by
  first
  | exact @_root_.GlobalTheory.ExistsSmulMem.exists_smul_mem
  | exact _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem
  | (apply _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExistsSmulMem.exists_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem ..)

theorem hform_single {E : Type} [Field E] {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E)
    (c : E) (i : Fin N) (y : Fin N → E) :
    hform σ J (c • Pi.single i 1) y = σ c * (J *ᵥ y) i := by
  simp [hform, Pi.single_apply, mulVec, dotProduct, Finset.mul_sum, mul_assoc, apply_ite σ, ite_mul]

theorem dualSet_le_fg {E : Type} [Field E] [NumberField E] {N : ℕ} (σ : E →+* E)
    (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (Lb : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) :
    ∃ M : Submodule (𝓞 E) (Fin N → E), M.FG ∧ dualSet σ J Lb ⊆ M := by
  choose c hc0 hcm using fun i : Fin N => exists_smul_mem Lb hsp (Pi.single i 1)
  refine ⟨Submodule.span (𝓞 E) (Set.range fun i => (σ (c i : E))⁻¹ • (J⁻¹ *ᵥ Pi.single i 1)),
    Submodule.fg_span (Set.finite_range _), ?_⟩
  intro y hy
  have hint : ∀ i, ∃ w : 𝓞 E, (w : E) = σ (c i : E) * (J *ᵥ y) i := by
    intro i
    have h := hy _ (hcm i)
    rw [← algebraMap_smul E (c i), hform_single] at h
    obtain ⟨w, hw⟩ := h
    exact ⟨w, hw⟩
  choose w hw using hint
  have hσ : ∀ i, σ (c i : E) ≠ 0 := fun i => by
    rw [map_ne_zero]
    exact_mod_cast hc0 i
  have hy' : y = ∑ i, w i • ((σ (c i : E))⁻¹ • (J⁻¹ *ᵥ Pi.single i 1)) := by
    have e1 : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
    conv_lhs => rw [e1, ← Finset.univ_sum_single (J *ᵥ y)]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul E (w i), smul_smul, ← Matrix.mulVec_smul]
    congr 1
    ext k
    simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · subst_vars
      show (J *ᵥ y) k = (algebraMap (𝓞 E) E (w k)) * (σ (c k : E))⁻¹ * 1
      rw [show algebraMap (𝓞 E) E (w k) = (w k : E) from rfl, hw k]
      field_simp [hσ k]
    · simp
  rw [hy']
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanFG

namespace GlobalTheory


open GlobalTheory.CompanFG in
theorem compan_fg {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (a : 𝓞 E)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfg : Lb.FG) (hsp : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) :
    (compan (sp := sp) J a Lb).FG := by
  obtain ⟨M, hM, hle⟩ := dualSet_le_fg (sp.cm.sig : E →+* E) J hJ Lb hsp
  have h1 : (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)).FG :=
    fg_of_le_fg hM (Submodule.span_le.mpr hle)
  exact hfg.sup (fg_of_le_fg h1 Submodule.smul_le_right)

end GlobalTheory
end
