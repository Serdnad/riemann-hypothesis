module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle139
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SDFrameLattice

open NumberField GlobalTheory.PlaceModel

theorem mem_dualL_iff {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (y : Fin V.rank → D.host.E) :
    y ∈ Formalism.L2.Herm.dualL D.sp.cm V Λ ↔
      ∀ x ∈ Λ, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ i, ∑ j, star (x i) * V.gram i j * y j := by
  unfold Formalism.L2.Herm.dualL
  constructor
  · intro hy x hx
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb⟩ := RingHom.mem_range.mp (hz x hx)
      exact ⟨b, hb⟩
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨b, hb⟩ := hz
      obtain ⟨a, ha⟩ := hw
      refine ⟨b + a, ?_⟩
      have e1 : ((b + a : 𝓞 D.host.E) : D.host.E) = (b : D.host.E) + a := by push_cast; ring
      rw [e1, hb, ha, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, mul_add]
    | smul a z _ hz =>
      obtain ⟨b, hb⟩ := hz
      refine ⟨a * b, ?_⟩
      have e1 : ((a * b : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E a * b := by first | (push_cast; ring) | push_cast | simp
      rw [e1, hb, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def]
      ring
  · intro hy
    apply Submodule.subset_span
    intro x hx
    obtain ⟨b, hb⟩ := hy x hx
    exact RingHom.mem_range.mpr ⟨b, hb⟩

theorem isSelfDualC_of_isSDFrame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → IsSelfDualC V Λ := by
  intro D V β Λ N h
  obtain ⟨c, hc⟩ := h
  obtain ⟨-, hdual, hN, hin, hout⟩ := hc
  set M : ℕ := N ^ c with hM
  have hMpos : 0 < M := hN
  have hME : (M : D.host.E) ≠ 0 := by exact_mod_cast hMpos.ne'
  unfold IsSelfDualC
  refine ⟨?_, fun y => ?_⟩
  swap
  · have e : Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ := hdual
    have key := mem_dualL_iff V Λ y
    rw [e] at key
    exact key
  · let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] V.V :=
      V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 D.host.E)
    have hf : ∀ x, f x = ∑ i, x i • V.frame i := fun x => by simp [f]
    have hfinj : Function.Injective f := V.frame.equivFun.symm.injective
    have hL := V.standardTuple_isLattice
    let s : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := M • LinearMap.id
    have hs : ∀ x, s x = M • x := fun x => by simp [s]
    have hsinj : Function.Injective s := by
      intro x x' hxx
      rw [hs, hs] at hxx
      exact nsmul_right_injective hMpos.ne' hxx
    have hout' : ∀ x ∈ Λ, f (M • x) ∈ V.L0 := by
      intro x hx
      have h1 := hout x hx
      rw [Nat.cast_smul_eq_nsmul] at h1
      rw [hf]
      exact h1
    have hfg : Λ.FG := by
      refine Submodule.fg_of_fg_map_injective (f ∘ₗ s) (hfinj.comp hsinj) (Submodule.FG.of_le hL.fg ?_)
      rintro _ ⟨x, hx, rfl⟩
      rw [LinearMap.comp_apply, hs]
      exact hout' x hx
    exact Submodule.IsLattice.of_fg D.host.E hfg

end GlobalTheory.SDFrameLattice
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ThetaLeftW

theorem thetaKernel_leftInvariant_rationalUnitary : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (χS χT : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)), Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) χS χT ω → ∀ φ : WO (Vc D i) (Wc D i) → ℂ, Datum.IsThetaFunO R.ψ (Vc D i) (Wc D i) φ → ∀ (h : GA D (Vc D i)) (γ : GA D (Wc D i)), γ ∈ GQ (Wc D i) → ∀ g : GA D (Wc D i), Datum.thetaKO ω h (γ * g) φ = Datum.thetaKO ω h g φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i χS χT ω hW φ hφ h γ hγ g
  unfold Datum.thetaKO
  have e : (h, γ * g) = ((1 : GA D (Vc D i)), γ) * (h, g) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut 1 (one_mem _) γ hγ _ (hW.om_pres _ _ hφ)

end GlobalTheory.ThetaLeftW
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowClassSum

section Generic

open Formalism.IndefR.Bridge

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ι : Γ →* G} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}

theorem card_stab (γ : Γ) (h : G) (k : J) :
    Nat.card (stab ι J (ι γ * h * k)) = Nat.card (stab ι J h) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj γ⁻¹).toEquiv fun δ => ?_)
  have e : (ι γ * h * k)⁻¹ * ι δ * (ι γ * h * k) =
      (k : G)⁻¹ * (h⁻¹ * ι ((MulAut.conj γ⁻¹).toEquiv δ) * h) * k := by
    simp [mul_assoc]
  rw [mem_stab, mem_stab, e, J.mul_mem_cancel_right k.2, J.mul_mem_cancel_left (J.inv_mem k.2)]

theorem adInner_indep (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y y' : I → G} (hy : IsReps ι J y) (hy' : IsReps ι J y')
    {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ) (hF' : F' ∈ AdForms ι ρ J χ) :
    adInner ι J y' F F' = adInner ι J y F F' := by
  choose s γ k hs using fun i => (hy (y' i)).exists
  have hinj : Function.Injective s := by
    intro i j hij
    refine (hy' (y' i)).unique ⟨1, 1, by simp⟩ ⟨γ i * (γ j)⁻¹, (k j)⁻¹ * k i, ?_⟩
    rw [hs i, hs j, hij]
    simp [mul_assoc]
  unfold adInner
  refine Fintype.sum_bijective s (Finite.injective_iff_bijective.1 hinj) _ _ fun i => ?_
  rw [hs i, card_stab, hF, hF', inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _),
    Complex.conj_mul', hχ, hρ]
  simp

variable {Q : Subgroup G} {ch : Q →* ℂˣ}

theorem reductionGroupAction_mem_adelicForms (hJ : J ≤ Q) (hn : ∀ κ ∈ Q, ∀ k ∈ J, κ⁻¹ * k * κ ∈ J) (hch : ∀ k : J, ch ⟨k, hJ k.2⟩ = χ k)
    (κ : Q) {F : G → W} (hF : F ∈ AdForms ι ρ J χ) : g0Act ch κ F ∈ AdForms ι ρ J χ := by
  intro γ h k
  have hk := hn κ κ.2 k k.2
  have e : ι γ * h * k * κ = ι γ * (h * κ) * ((⟨_, hk⟩ : J) : G) := by simp [mul_assoc]
  have e2 : χ ⟨_, hk⟩ = χ k := by
    rw [← hch, ← hch]
    have : (⟨_, hJ hk⟩ : Q) = κ⁻¹ * ⟨k, hJ k.2⟩ * κ := rfl
    rw [this, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  unfold g0Act
  rw [e, hF, e2, map_smul, smul_comm]

theorem adInner_g0Act (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1)
    (hn : ∀ κ ∈ Q, ∀ k ∈ J, κ⁻¹ * k * κ ∈ J) (κ : Q) (hκ : ‖(ch κ : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : IsReps ι J y)
    {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ) (hF' : F' ∈ AdForms ι ρ J χ) :
    adInner ι J y (g0Act ch κ F) (g0Act ch κ F') = adInner ι J y F F' := by
  have hn' : ∀ k ∈ J, (κ : G) * k * (κ : G)⁻¹ ∈ J := fun k hk => by
    simpa using hn _ (Q.inv_mem κ.2) k hk
  have hy' : IsReps ι J fun i => y i * κ := by
    intro h
    refine (existsUnique_congr fun i => ?_).1 (hy (h * (κ : G)⁻¹))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, ⟨_, hn κ κ.2 k k.2⟩, ?_⟩
      rw [mul_inv_eq_iff_eq_mul] at e
      rw [e]; simp [mul_assoc]
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, ⟨_, hn' k k.2⟩, ?_⟩
      rw [e]; simp [mul_assoc]
  rw [← adInner_indep hρ hχ hy hy' hF hF']
  unfold adInner g0Act
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : stab ι J (y i * κ) = stab ι J (y i) := by
    ext δ
    rw [mem_stab, mem_stab]
    constructor
    · intro h
      simpa [mul_assoc] using hn' _ h
    · intro h
      simpa [mul_assoc] using hn κ κ.2 _ h
  rw [hs, inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _), Complex.conj_mul',
    Units.val_inv_eq_inv_val, norm_inv, hκ]
  simp

theorem exists_g0Act (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hn1 : ∀ q, ‖(ch q : ℂ)‖ = 1)
    (hJ : J ≤ Q) (hn : ∀ κ ∈ Q, ∀ k ∈ J, κ⁻¹ * k * κ ∈ J) (hch : ∀ k : J, ch ⟨k, hJ k.2⟩ = χ k)
    {I : Type} [Fintype I] {y : I → G} (hy : IsReps ι J y) (M : Links.HMod (G → W))
    (hM : M.Is (AdForms ι ρ J χ) (adInner ι J y)) (κ : Q) (x : M.H) :
    ∃ x' : M.H, M.e x' = g0Act ch κ (M.e x) ∧ ‖x'‖ = ‖x‖ := by
  obtain ⟨-, hr, hi⟩ := hM
  have hχ : ∀ k, ‖(χ k : ℂ)‖ = 1 := fun k => by
    rw [← hch]; exact hn1 _
  have hx : M.e x ∈ AdForms ι ρ J χ := by
    rw [← hr]; exact ⟨x, rfl⟩
  have hm := reductionGroupAction_mem_adelicForms hJ hn hch κ hx
  rw [← hr] at hm
  obtain ⟨x', hx'⟩ := hm
  refine ⟨x', hx', ?_⟩
  have e : inner ℂ x' x' = inner ℂ x x := by
    rw [hi, hi, hx']
    exact adInner_g0Act hρ hχ hn κ (hn1 _) hy hx hx
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ x, e]

theorem twistedTranslate_apply_eq_inv_smul {a : G} (ha : a ∈ Q) (F : G → W) (h : G) {z : ℂ} (hz : ((ch ⟨a, ha⟩ : ℂˣ) : ℂ) = z) :
    g0Act ch ⟨a, ha⟩ F h = z⁻¹ • F (h * a) := by
  rw [← hz, ← Units.val_inv_eq_inv_val]
  rfl

end Generic

variable {D : D7}

theorem norm_levFn_flagL (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (x : GL (Fin V.rank) (Lev.EAf D)) : ‖((levFn β (flagL L) x : ℂˣ) : ℂ)‖ = 1 := by
  have h2 : Formalism.L2.DIV.ext1 (flagL L).P.H (flagL L).P.chi (Formalism.L2.DIV.rTup β (flagL L) x) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h2, one_mul, Units.val_mul, norm_mul, Units.coe_prod, Units.coe_prod, norm_prod, norm_prod,
    Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP _
    exact norm_residueChar_eq_one PP _ _
  · intro PP _
    rw [Units.coe_prod, norm_prod]
    exact Finset.prod_eq_one fun c _ => norm_residueChar_eq_one PP _ _

theorem conj_mem_flag1L (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {a b : GL (Fin V.rank) (Lev.EAf D)} (ha : a ∈ lev D.sp.cm V.gram β (flagL L))
    (hb : b ∈ lev D.sp.cm V.gram β (flag1L L)) : a⁻¹ * b * a ∈ lev D.sp.cm V.gram β (flag1L L) := by
  have h1 : a ∈ parLev D.sp.cm V.gram β L := ha.1
  have h2 : b ∈ parLev D.sp.cm V.gram β L := hb.1
  have h3 : rTup β L b = 1 := Subgroup.mem_bot.1 hb.2
  have h4 : a⁻¹ * b ∈ parLev D.sp.cm V.gram β L := Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h2
  have h5 : rTup β L (a⁻¹ * b * a) = 1 := by
    rw [rTup_mul h4 h1, rTup_mul (Subgroup.inv_mem _ h1) h2, rTup_inv h1, h3, mul_one, inv_mul_cancel]
  exact ⟨Subgroup.mul_mem _ h4 h1, Subgroup.mem_bot.2 h5⟩

theorem levEnv_normal (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ κ ∈ (levEnv V β L).Q, ∀ k ∈ (levEnv V β L).J, κ⁻¹ * k * κ ∈ (levEnv V β L).J := by
  intro κ hκ k hk
  have h := conj_mem_flag1L V β L (a := Formalism.UG.bc (swapAE D) κ.1) (b := Formalism.UG.bc (swapAE D) k.1) hκ hk
  rw [← map_inv, ← map_mul, ← map_mul] at h
  exact h

theorem levEnv_ch (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) : (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) q.1.1) := rfl

theorem mem_levEnv_Q {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {g0 : G0 L.Pg L.r} {κ : GA D V} (hκ : IsLevelLift V β L g0 κ) :
    (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q := by
  have h : finE V κ ∈ lev D.sp.cm V.gram β (flagL L) := ⟨hκ.2.1, Subgroup.mem_top _⟩
  exact h

theorem levEnv_ch_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {κ : GA D V} (hq : (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q) :
    (((levEnv V β L).ch ⟨_, hq⟩ : ℂˣ) : ℂ) = levChi V β (flagL L) κ := by
  rw [levEnv_ch]
  rfl

theorem exists_translate (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (c : CoefA V) (hc : c.Is) (M : HMod (Bridge.Gf V → c.W)) {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hM : M.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y))
    (g0 : G0 L.Pg L.r) (κ : GA D V) (hκ : IsLevelLift V β L g0 κ) (x : M.H) :
    ∃ x' : M.H, (∀ h, M.e x' h = (levChi V β (flagL L) κ)⁻¹ • M.e x (h * (finHom V).rangeRestrict κ)) ∧
      ‖x'‖ = ‖x‖ := by
  have hq := mem_levEnv_Q hκ
  have hch : ∀ q, ‖(((levEnv V β L).ch q : ℂˣ) : ℂ)‖ = 1 := fun q => by
    rw [levEnv_ch]; exact norm_levFn_flagL V β L _
  have hρ : ∀ (γ : GQ V) (u u' : c.W),
      inner ℂ ((c.ρ.comp (GQ V).subtype) γ u) ((c.ρ.comp (GQ V).subtype) γ u') = inner ℂ u u' :=
    fun γ u u' => hc.2.1 γ.1 u u'
  have key : ∃ x' : M.H, M.e x' = Bridge.g0Act (levEnv V β L).ch ⟨_, hq⟩ (M.e x) ∧ ‖x'‖ = ‖x‖ :=
    exists_g0Act (W := c.coef.W) (ι := Bridge.ratF V) (ρ := c.coef.ρ) (χ := (levEnv V β L).χ)
      (ch := (levEnv V β L).ch) hρ hch (levEnv V β L).J_le (levEnv_normal V β L) (levEnv V β L).ch_J hy M hM ⟨_, hq⟩ x
  obtain ⟨x', hx', hn⟩ := key
  refine ⟨x', fun h => ?_, hn⟩
  refine Eq.trans ?_ (twistedTranslate_apply_eq_inv_smul (ch := (levEnv V β L).ch) hq (M.e x) h (levEnv_ch_lift hq))
  exact congrFun hx' h

end GlobalTheory.RowClassSum

namespace GlobalTheory

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicIntegrable

theorem integrable_of_rapid_decay : ∀ (D : D7) (a b : ℕ) (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, Continuous f → ∀ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K → (∀ y : Mx D a b, y.map (finPart D) ∉ K → f y = 0) → (∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C) → Integrable f μ := by
  intro D a b μ hμ θ hθ f hf K hK hKf hdec
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D a b
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ

  let π : Mx D a b → (Fin a → Fin b → D.what₂.Tau → ℂ) := fun y i j τ => θ τ (infPart D (y i j))
  have hπc : Continuous π := continuous_pi fun i => continuous_pi fun j => continuous_pi fun τ =>
    (GlobalTheory.FockCompare.continuous_comp hθ τ).comp ((continuous_apply j).comp (continuous_apply i))
  have hπm : Measurable π := hπc.measurable

  let s : (Fin a → Fin b → D.what₂.Tau → ℂ) → Mx D a b := fun c => Matrix.of fun i j => σ (c i j)
  have hπs : ∀ c y, π (s c + y) = c + π y := by
    intro c y; funext i j τ
    show θ τ (infPart D (σ (c i j) + y i j)) = c i j τ + θ τ (infPart D (y i j))
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp]
  have hfs : ∀ c (y : Mx D a b), (s c + y).map (finPart D) = y.map (finPart D) := by
    intro c y; ext i j
    show finPart D (σ (c i j) + y i j) = finPart D (y i j)
    rw [RingHom.map_add (f := _), hσ.fin, zero_add]
  let S : Set (Mx D a b) := {y | y.map (finPart D) ∈ K}
  let ν : Measure (Fin a → Fin b → D.what₂.Tau → ℂ) := (μ.restrict S).map π
  have hνA : ∀ A, MeasurableSet A → ν A = μ (π ⁻¹' A ∩ S) := fun A hA => by
    rw [Measure.map_apply hπm hA, Measure.restrict_apply (hπm hA)]
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun c => Measure.ext fun A hA => ?_⟩
    rw [Measure.map_apply (measurable_const_add c) hA, hνA _ (measurable_const_add c hA), hνA _ hA]
    have e : π ⁻¹' ((fun x => c + x) ⁻¹' A) ∩ S = (fun y => s c + y) ⁻¹' (π ⁻¹' A ∩ S) := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage, S, Set.mem_setOf_eq, hπs, hfs]
    rw [e, measure_preimage_add]
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun A hA => ?_⟩
    obtain ⟨R, hR⟩ := hA.isBounded.exists_norm_le
    choose C hC hCK using fun i j => GlobalTheory.StabCompact.exists_compact_adele D θ hθ R
      ((fun M : Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E) => M i j) '' K)
      (hK.image ((continuous_apply j).comp (continuous_apply i)))
    have hc : IsCompact (Set.pi Set.univ fun i => Set.pi Set.univ fun j => C i j : Set (Mx D a b)) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j => hC i j
    rw [hνA _ hA.isClosed.measurableSet]
    haveI : IsFiniteMeasureOnCompacts μ := hμ.toIsFiniteMeasureOnCompacts
    refine lt_of_le_of_lt (measure_mono ?_) (IsFiniteMeasureOnCompacts.lt_top_of_isCompact (μ := μ) hc)
    rintro y ⟨hyA, hyS⟩ i - j -
    refine hCK i j _ ⟨_, hyS, rfl⟩ fun ρ => le_trans ?_ (hR _ hyA)
    exact (norm_le_pi_norm (π y i j) ρ).trans ((norm_le_pi_norm (π y i) j).trans (norm_le_pi_norm (π y) i))
  have hνe : ν = ν.addHaarScalarFactor Measure.addHaar • (Measure.addHaar : Measure (Fin a → Fin b → D.what₂.Tau → ℂ)) :=
    Measure.isAddLeftInvariant_eq_smul ν Measure.addHaar

  set N : ℕ := Module.finrank ℝ (Fin a → Fin b → D.what₂.Tau → ℂ) + 1 with hN
  obtain ⟨C, hC⟩ := hdec N
  let G : (Fin a → Fin b → D.what₂.Tau → ℂ) → ℝ := fun x => C * (1 + ‖x‖) ^ (-(N : ℝ))
  have hGv : Integrable G (Measure.addHaar : Measure (Fin a → Fin b → D.what₂.Tau → ℂ)) :=
    (integrable_one_add_norm (by rw [hN]; push_cast; linarith)).const_mul C
  have hGν : Integrable G ν := by
    rw [hνe]; exact hGv.smul_measure ENNReal.coe_ne_top
  have hGπ : Integrable (G ∘ π) (μ.restrict S) :=
    (integrable_map_measure hGν.aestronglyMeasurable hπm.aemeasurable).1 hGν
  have hbound : ∀ y, ‖f y‖ ≤ G (π y) := by
    intro y
    have hsum : ‖π y‖ ≤ ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2
        fun j => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun τ => ?_
      refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖)
        (fun _ _ => by positivity) (Finset.mem_univ τ))
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖θ τ (infPart D (y i j))‖)
        (fun _ _ => by positivity) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j => ‖θ τ (infPart D (y i j))‖) (fun _ _ => by positivity)
        (Finset.mem_univ j)
    have h1 : 0 < 1 + ‖π y‖ := by positivity
    have h2 : (1 + ‖π y‖) ^ N ≤ (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N :=
      pow_le_pow_left₀ h1.le (by linarith) N
    have h3 := hC y
    have h4 : (1 + ‖π y‖) ^ N * ‖f y‖ ≤ C := le_trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) h3
    show ‖f y‖ ≤ C * (1 + ‖π y‖) ^ (-(N : ℝ))
    rw [Real.rpow_neg h1.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos h1 N), mul_comm]
    exact h4
  have hfS : IntegrableOn f S μ :=
    hGπ.mono' hf.aestronglyMeasurable.restrict (Filter.Eventually.of_forall hbound)
  exact hfS.integrable_of_forall_notMem_eq_zero fun y hy => hKf y hy

end GlobalTheory.AdelicIntegrable

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.NormRed

theorem sq_norm_two_haar : ∀ (D : D7) (V' W : HSp D) (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (μ'' : Measure (WO V' W)) (𝓕'' : Set (WO V' W)), IsCovolOne (ratL W V') μ'' 𝓕'' → ∃ c : ENNReal, ∀ g : WO V' W → ℂ, Continuous g → (∀ γ ∈ ratL W V', ∀ w, ‖g (γ + w)‖ = ‖g w‖) → ∫⁻ x in 𝓕', ‖g x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x in 𝓕'', ‖g x‖ₑ ^ 2 ∂μ'' := by
  intro D V' W μ' 𝓕' hμ' hF' μ'' 𝓕'' h''
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (WO V' W) := i1
  haveI : LocallyCompactSpace (WO V' W) := i2
  haveI : SecondCountableTopology (WO V' W) := i3
  haveI : T2Space (WO V' W) := i4
  haveI : DiscreteTopology (ratL W V') := i5
  haveI : TopologicalSpace.SeparableSpace (ratL W V') := inferInstance
  haveI : Countable (ratL W V') := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : MeasurableConstVAdd (ratL W V') (WO V' W) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  obtain ⟨hμ'', hF'', -⟩ := h''
  haveI : VAddInvariantMeasure (ratL W V') (WO V' W) μ'' :=
    ⟨fun c s _ => measure_preimage_add μ'' (c : WO V' W) s⟩
  have e := Measure.isAddLeftInvariant_eq_smul μ' μ''
  set c := Measure.addHaarScalarFactor μ' μ''
  have hc : c ≠ 0 := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' μ'').ne'
  have hac : μ'' ≪ μ' := by
    rw [e]; exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc)
  have hF2 : IsAddFundamentalDomain (ratL W V') 𝓕' μ'' := hF'.mono hac
  refine ⟨(c : ENNReal), fun g hg hper => ?_⟩
  have hp : ∀ (γ : ratL W V') (x : WO V' W), ‖g (γ +ᵥ x)‖ₑ ^ 2 = ‖g x‖ₑ ^ 2 := by
    intro γ x
    rw [AddSubgroup.vadd_def, vadd_eq_add]
    have h1 : ‖g ((γ : WO V' W) + x)‖₊ = ‖g x‖₊ := NNReal.eq (hper γ γ.2 x)
    simp only [enorm_eq_nnnorm, h1]
  rw [e, Measure.restrict_smul, lintegral_smul_measure, hF2.setLIntegral_eq hF'' _ hp]
  rfl

end GlobalTheory.Twist.NormRed
end
