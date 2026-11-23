module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle007
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Formalism.LocalToGlobal.Divisibility.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum

namespace Formalism.IndefR.Eqv.KerDiag

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isSelfDualC_of_base {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {N : ℕ} (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ N) : IsSelfDualC V Λ := by
  obtain ⟨-, hdual, hN, hin, hout⟩ := hB
  have hN0 : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hl0 := (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.self_dual_lattice_is_self_dual V).1
  let φ : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := (N : 𝓞 D.host.E) • LinearMap.id
  have hφ : ∀ x, φ x = (N : D.host.E) • x := fun x => by
    simp only [φ, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← algebraMap_smul D.host.E (N : 𝓞 D.host.E) x, map_natCast]
  refine ⟨⟨?_, ?_⟩, fun y => ?_⟩
  · have hφinj : Function.Injective φ := fun a b hab => by
      rw [hφ, hφ] at hab
      exact smul_right_injective _ hN0 hab
    have hle : Λ.map φ ≤ Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.mem_self_dual_lattice_set, hφ]
      exact hout x hx
    have : IsNoetherian (𝓞 D.host.E) (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V) := isNoetherian_of_fg_of_noetherian _ hl0.fg
    have h1 : ((Λ.map φ).comap (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V).subtype
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.2 hle] at h2
    exact Submodule.fg_of_fg_map_injective φ hφinj h2
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · rw [Formalism.IndefR.Eqv.dual_of_dualL hdual y]
    simp only [Formalism.UG.hform, starRingEnd_apply, RingHom.mem_range]

section R

open Formalism.IndefR.Links Formalism.IndefR.Links.RealDat

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


end R

end Formalism.IndefR.Eqv.KerDiag

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.Eqv.Act

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Comm

variable {D : D7} {V : HSp D}

theorem mem_GfC' (h : GA D V) : h ∈ GfC V ↔ (matA D V h).map (infPart D) = 1 := by
  rw [GfC, MonoidHom.mem_ker, Units.ext_iff]
  rfl

theorem comm_inf_fin {a b : GA D V} (ha : a ∈ GinfC V) (hb : b ∈ GfC V) : a * b = b * a := by
  have ha' := (mem_GinfC (D := D) (V := V) (h := a)).1 ha
  have hb' := (mem_GfC' b).1 hb
  have hinf : (matA D V a * matA D V b).map (infPart D) = (matA D V b * matA D V a).map (infPart D) := by
    rw [Matrix.map_mul, Matrix.map_mul, hb', mul_one, one_mul]
  have hfin : (matA D V a * matA D V b).map (finPart D) = (matA D V b * matA D V a).map (finPart D) := by
    rw [Matrix.map_mul, Matrix.map_mul, ha', mul_one, one_mul]
  have key : matA D V (a * b) = matA D V (b * a) := by
    rw [matA_mul, matA_mul]
    ext i j
    exact ae_ext (D := D) (congrFun (congrFun hinf i) j) (congrFun (congrFun hfin i) j)
  first
  | exact Subtype.ext (Units.ext key)
  | (apply Subtype.ext; apply Units.ext; exact key)
  | (apply Subtype.ext; apply Subtype.ext; apply Units.ext; exact key)

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

theorem atTau_mem (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_mem _

theorem oneP_mem (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) : oneP θ V τ X t ∈ GinfC V := by
  unfold oneP
  exact atTau_mem θ τ _

end Comm

section RTr

variable {D : D7} {V : HSp D} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {κ : GA D V}

end RTr

end Formalism.IndefR.Eqv.Act

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar



open Classical

variable (D : D7)

theorem glueA_eq_homeo (y : Ainf D.host.F ⊗[D.host.F] D.host.E) (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    glueA D y z = (G5.tensCoordH (basE D) (AF D.host.F)).symm
      (fun k => pairA D.host.F ((basA D).repr y k) ((basAf D).repr z k)) := by
  apply (G5.tensCoordH (basE D) (AF D.host.F)).injective
  rw [Homeomorph.apply_symm_apply]
  funext k
  rw [G5.tensCoordH_apply]
  exact repr_glueA D y z k

theorem continuous_glueA (z : Af D.host.F ⊗[D.host.F] D.host.E) : Continuous fun y => glueA D y z := by
  have e : (fun y => glueA D y z) = fun y => (G5.tensCoordH (basE D) (AF D.host.F)).symm
      (fun k => pairA D.host.F ((basA D).repr y k) ((basAf D).repr z k)) := funext fun y => glueA_eq_homeo D y z
  rw [e]
  have hp : Continuous fun p : Ainf D.host.F × Af D.host.F => pairA D.host.F p.1 p.2 := continuous_id
  exact (G5.tensCoordH (basE D) (AF D.host.F)).symm.continuous.comp
    (continuous_pi fun k => hp.comp ((continuous_repr D k).prodMk continuous_const))

theorem continuous_splitInv : Continuous (splitInv D) := by
  rw [← splitEquiv_symm]; exact continuous_splitEquiv_symm D

variable (V : HSp D)

theorem atTau_eq (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    atTau (thetaC D) V τ g = atH D V τ g hg := by
  have hex : ∃ x, IsAtTau (thetaC D) V τ g x := ⟨_, isAtTau_atH D V τ g hg⟩
  unfold atTau
  rw [dite_eq_left hex]
  exact matA_inj D V ((matA_of_isAtTau D V hex.choose_spec).trans (matA_atH D V τ g hg).symm)

section Line

variable {m n : ℕ}

def lineF (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) : Datum.Mx D m n :=
  Matrix.of fun i j => glueA D (splitInv D fun τ' => if τ' = τ then (t : ℂ) * z i j else 0) 0

theorem psi_lineF (τ τ' : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    (lineF D τ z t).map (psiT D τ') = if τ' = τ then (t : ℂ) • z else 0 := by
  ext i j
  simp only [lineF, Matrix.map_apply, Matrix.of_apply, psiT_glueA]
  split_ifs <;> simp

theorem fin_lineF (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) : (lineF D τ z t).map (finPart D) = 0 := by
  ext i j
  simp [lineF, finPart_glueA]

def lineL (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) : ℝ →+ Datum.Mx D m n where
  toFun := lineF D τ z
  map_zero' := by
    apply mat_ext D
    · intro τ'
      rw [psi_lineF, Matrix.map_zero _ (map_zero _)]
      split_ifs <;> simp
    · rw [fin_lineF, Matrix.map_zero _ (map_zero _)]
  map_add' s t := by
    apply mat_ext D
    · intro τ'
      rw [Matrix.map_add _ (map_add _), psi_lineF, psi_lineF, psi_lineF]
      split_ifs
      · push_cast; rw [add_smul]
      · simp
    · rw [Matrix.map_add _ (map_add _), fin_lineF, fin_lineF, fin_lineF, add_zero]

theorem continuous_lineF (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) : Continuous (lineF D τ z) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_glueA D _).comp ((continuous_splitInv D).comp (continuous_pi fun τ' => ?_))
  by_cases h : τ' = τ
  · simp only [h, if_true]; exact Complex.continuous_ofReal.mul continuous_const
  · simp only [h, if_false]; exact continuous_const

theorem compAt_thetaC (τ : D.what₂.Tau) (w : Datum.Mx D m n) : Datum.compAt (thetaC D) τ w = w.map (psiT D τ) := rfl

theorem isLineAt_lineL (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) :
    Datum.IsLineAt (thetaC D) τ z (lineL D τ z) :=
  ⟨continuous_lineF D τ z, fun t => fin_lineF D τ z t, fun t τ' => by
    rw [compAt_thetaC]; exact psi_lineF D τ τ' z t⟩

end Line

theorem lineAtExists_holds : Datum.LineAtExists D := by
  intro θ hθ m n τ z
  rw [eq_thetaC D hθ]
  exact ⟨lineL D τ z, isLineAt_lineL D τ z⟩

section Fam

variable (V : HSp D)

def famM (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) (AE D) :=
  Matrix.of fun i j => glueA D (splitInv D fun τ => gs τ i j)
    ((1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j)

theorem psi_famM (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau) :
    (famM D V gs).map (psiT D τ) = gs τ := by
  ext i j
  simp [famM, psiT_glueA]

theorem fin_famM (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : (famM D V gs).map (finPart D) = 1 := by
  ext i j
  simp [famM, finPart_glueA]

theorem famM_mul (gs gs' : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    famM D V (gs * gs') = famM D V gs * famM D V gs' := by
  apply mat_ext D
  · intro τ
    rw [Matrix.map_mul, psi_famM, psi_famM, psi_famM]
    rfl
  · rw [Matrix.map_mul, fin_famM, fin_famM, fin_famM, mul_one]

theorem famM_one : famM D V 1 = 1 := by
  apply mat_ext D
  · intro τ
    rw [psi_famM, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  · rw [fin_famM, Matrix.map_one _ (map_zero _) (map_one _)]

def IsUnitFam (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  ∀ τ, (gs τ)ᴴ * gramAt D V τ * gs τ = gramAt D V τ

theorem famM_unitary (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hgs : IsUnitFam D V gs) :
    Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (famM D V gs) * JR (AF D.host.F) V.gram * famM D V gs =
      JR (AF D.host.F) V.gram := by
  apply mat_ext D
  · intro τ
    rw [Matrix.map_mul, Matrix.map_mul, cT_map_psiT, JR_map_psiT, psi_famM]
    exact hgs τ
  · rw [Matrix.map_mul, Matrix.map_mul, cT_map_fin, JR_map_fin, fin_famM, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

def famH (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hgs : IsUnitFam D V gs) : GA D V :=
  (⟨⟨famM D V gs, famM D V (fun τ => ginv D V τ (gs τ)),
      by rw [← famM_mul]; convert famM_one D V; funext τ; exact mul_ginv D V τ (gs τ) (hgs τ),
      by rw [← famM_mul]; convert famM_one D V; funext τ; exact ginv_mul D V τ (gs τ) (hgs τ)⟩,
    famM_unitary D V gs hgs⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)

theorem matA_famH (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hgs : IsUnitFam D V gs) :
    matA D V (famH D V gs hgs) = famM D V gs := rfl

theorem infMat_famH (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hgs : IsUnitFam D V gs) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (thetaC D τ) (famH D V gs hgs) = gs τ := by
  rw [infMat_thetaC, matA_famH, psi_famM]

theorem famH_mem_GinfC (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hgs : IsUnitFam D V gs) :
    famH D V gs hgs ∈ GinfC V :=
  (mem_GinfC D V _).mpr (fin_famM D V gs)

theorem famH_unique (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hgs : IsUnitFam D V gs) (h : GA D V)
    (h1 : h ∈ GinfC V) (h2 : ∀ τ, infMat D.sp.cm.sig V.gram (thetaC D τ) h = gs τ) : h = famH D V gs hgs := by
  apply matA_inj D V
  rw [matA_famH]
  apply mat_ext D
  · intro τ; rw [← infMat_thetaC, h2, psi_famM]
  · rw [fin_famM]; exact (mem_GinfC D V h).mp h1

theorem infMat_unitary' (h : GA D V) : IsUnitFam D V fun τ => infMat D.sp.cm.sig V.gram (thetaC D τ) h := by
  intro τ
  have hu := congrArg (fun M => M.map (psiT D τ)) (matA_unitary D V h)
  simp only [Matrix.map_mul, cT_map_psiT, JR_map_psiT] at hu
  show (infMat D.sp.cm.sig V.gram (thetaC D τ) h)ᴴ * gramAt D V τ * infMat D.sp.cm.sig V.gram (thetaC D τ) h = _
  rw [infMat_thetaC]
  exact hu

def infOnly (h : GA D V) : GA D V := famH D V _ (infMat_unitary' D V h)

theorem infMat_infOnly (h : GA D V) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (thetaC D τ) (infOnly D V h) = infMat D.sp.cm.sig V.gram (thetaC D τ) h :=
  infMat_famH D V _ _ τ

theorem infOnly_mem_GinfC (h : GA D V) : infOnly D V h ∈ GinfC V := famH_mem_GinfC D V _ _

end Fam

end Formalism.IndefR.Eqv

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

theorem continuous_psiT (τ : D.what₂.Tau) : Continuous (psiT D τ) := by
  have heq : (psiT D τ : AE D → ℂ) = fun x => gW D (plW D τ) (fstA D.host.F ((basAF D).repr x 0)) +
      gW D (plW D τ) (fstA D.host.F ((basAF D).repr x 1)) * betaT D τ := by
    funext x
    simp only [psiT, RingHom.coe_comp, Function.comp_apply]
    rw [thetaC_decomp, repr_infPart, repr_infPart]
  rw [heq]
  have hc : ∀ k : Fin 2, Continuous fun x : AE D => (basAF D).repr x k := fun k => by
    have := (continuous_apply k).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous
    convert this using 1
    rfl
  have hf : Continuous (fstA D.host.F) := continuous_fst
  exact ((continuous_gW (D := D) _).comp (hf.comp (hc 0))).add
    (((continuous_gW (D := D) _).comp (hf.comp (hc 1))).mul continuous_const)

end Formalism.IndefR.Eqv

end
end

section

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Formalism.IndefR.Eqv

theorem rightInv_holds : RightInv := by
  intro H _ _ _ Γ _ ν _ _ 𝓕 h𝓕 ψ hψ k
  have hψ' : ∀ (g : Γ) (x : H), ψ (g • x) = ψ x := fun g x => hψ g g.2 x
  have h2 : IsFundamentalDomain Γ (MulOpposite.op k • 𝓕) ν := h𝓕.smul_of_comm (MulOpposite.op k)
  have himg : MulOpposite.op k • 𝓕 = (fun h => h * k) '' 𝓕 := by
    ext x
    simp [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x * k⁻¹, hx, by simp⟩
  have hmp := measurePreserving_mul_right ν k
  have hme := measurableEmbedding_mulRight (G := H) k
  constructor
  · have e1 := (hmp.integrableOn_image hme (f := ψ) (s := 𝓕)).symm
    rw [← himg] at e1
    exact e1.trans (h2.integrableOn_iff h𝓕 hψ')
  · calc ∫ h in 𝓕, ψ (h * k) ∂ν = ∫ y in (fun h => h * k) '' 𝓕, ψ y ∂ν :=
          (hmp.setIntegral_image_emb hme ψ 𝓕).symm
      _ = ∫ y in MulOpposite.op k • 𝓕, ψ y ∂ν := by rw [himg]
      _ = ∫ h in 𝓕, ψ h ∂ν := h2.setIntegral_eq h𝓕 hψ'

section GA

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end GA

end Formalism.IndefR.Eqv

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

def cAlin (D : D7) : AE D →ₗ[AF D.host.F] AE D where
  toFun := cA D
  map_add' := fun x y => RingHom.map_add _ x y
  map_smul' := fun c z => cA_smul c z

theorem continuous_cA : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap (cAlin D)

theorem continuous_trace : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
  IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))


theorem continuous_hO : Continuous fun p : WO S T × WO S T => hO S T p.1 p.2 := by
  have hc := continuous_cA (D := D)
  unfold hO
  fun_prop



end Formalism.IndefR.Eqv

end
end
