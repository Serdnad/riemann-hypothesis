module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle354
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle457
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle014
import Formalism.LocalToGlobal.IndefiniteReal.SelfDualFullLattice

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (γ : W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ →
    ∀ φ : (κ → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (co.rho ψ γ) φ
      (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v γ) φ) := by
  first | exact @GlobalTheory.VacBridge.rho_acts_locCo | exact GlobalTheory.VacBridge.rho_acts_locCo | (intros; apply GlobalTheory.VacBridge.rho_acts_locCo <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.LocSplitOp

theorem exists_locOp : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {G : Type} [Group G] (act : G → W → W) (om : G →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd act om →
    ∀ (v : Pl (F := F)) (p : G), (∀ u, At (evFin F v) u → At (evFin F v) (act p u)) →
    (∀ Φ ∈ SB (κ → Fv F v), ∃ Φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om p) Φ Φ₁) →
    ∃ S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ,
      (∀ Φ ∈ SB (κ → Fv F v), S Φ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) (om p) Φ (S Φ)) ∧
      ∀ u, At (evFin F v) u → ∀ Φ ∈ SB (κ → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
          schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v (act p u)) (S Φ) := by
  intro F _ _ W _ _ Bf κ _ dd ψ hψ G _ act om hsp v p hat hex
  choose! S hS using hex
  refine ⟨S, hS, ?_⟩
  intro u hu Φ hΦ
  have hc : Continuous ψ := hψ.1
  have hw := GlobalTheory.SchrSB.schr_mem_SB ψ hc v (GlobalTheory.LatVac.locCo dd v u) Φ hΦ
  have restS : ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) Φ r → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) (S Φ) r :=
    fun r hr => ⟨hr.1, by rw [← (hS Φ hΦ).2 r hr]; exact hsp.pres p _ hr.2⟩
  refine GlobalTheory.TensUniq.eq_of_tens_eq v Φ _ _ hΦ fun r hr => ?_
  have hb1 := GlobalTheory.VacBridge.rho_acts_locCo dd ψ v u hu Φ r hr
  have hRw : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v)
      (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) r :=
    ⟨hr.1, by rw [← hb1]; exact GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ _ _ hr.2⟩
  rw [← (hS _ hw).2 r hRw, ← hb1, hsp.impl _ _ _ hr.2, (hS Φ hΦ).2 r hr,
    GlobalTheory.VacBridge.rho_acts_locCo dd ψ v _ (hat u hu) (S Φ) r (restS r hr)]

end GlobalTheory.LocSplitOp
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockLevel

open Matrix
open scoped TensorProduct
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance isModTopAFE : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩

theorem finiteDimensional_FE : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

local instance : FiniteDimensional F E := finiteDimensional_FE

local instance topRingAFE : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem continuous_sigR_ad (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  have e : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add a b ha hb => rw [map_add (f := _), LinearMap.map_add (f := _), ha, hb]
  rw [e]
  exact IsModuleTopology.continuous_of_linearMap _

theorem infTens_sigR (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) :
    GlobalTheory.LFun.infTens F E (sigR (AF F) σ z) = sigR (Ainf F) σ (GlobalTheory.LFun.infTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem continuous_finGL (d : ℕ) : Continuous (GlobalTheory.CuspRep.finGL E d) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (GlobalTheory.CuspRep.sFin E : GlobalTheory.CuspRep.Af E → GlobalTheory.CuspRep.Ad E) :=
    (continuous_const.prodMk continuous_id :
      Continuous fun x : GlobalTheory.CuspRep.Af E => ((0, x) : InfiniteAdeleRing E × GlobalTheory.CuspRep.Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Af E) => 1 - GlobalTheory.CuspRep.matN d (GlobalTheory.CuspRep.sFin E) 1 + x.map (GlobalTheory.CuspRep.sFin E))

variable [_root_.NumberField.IsTotallyComplex E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
  {Xf Yf : Matrix (Fin n) (Fin r) E} {l d : ℕ} {h : l + d ≤ r} {ι : GlobalTheory.CuspRep.GA E d →* GAd σ J}

theorem continuous_of_isBlockEmb (hι : GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι) : Continuous ι := by
  obtain ⟨Φ, j, -, hΦs, -, -, hf⟩ := hι
  have hval : Continuous fun g : GlobalTheory.CuspRep.GA E d => ((matHom (AF F) σ J (ι g)).1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) := by
    simp only [hf, cT]
    have h1 : Continuous fun g : GlobalTheory.CuspRep.GA E d => (g.1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) := Units.continuous_val
    have h2 : Continuous fun g : GlobalTheory.CuspRep.GA E d => ((g⁻¹).1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) :=
      Units.continuous_val.comp continuous_inv
    have h3 := h1.matrix_map hΦs
    have h4 := ((h2.matrix_map hΦs).matrix_map (continuous_sigR_ad σ)).matrix_transpose
    exact (continuous_const.add ((continuous_const.matrix_mul (h3.sub continuous_const)).matrix_mul continuous_const)).add
      ((continuous_const.matrix_mul (h4.sub continuous_const)).matrix_mul continuous_const)
  have hU : Continuous fun g : GlobalTheory.CuspRep.GA E d => matHom (AF F) σ J (ι g) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have : (fun g : GlobalTheory.CuspRep.GA E d => ((matHom (AF F) σ J (ι g))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1) =
        (fun g => ((matHom (AF F) σ J (ι g)).1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) ∘ fun g => g⁻¹ := by
      funext g; simp [map_inv]
    rw [this]
    exact hval.comp continuous_inv
  exact (isEmbedding_matHom (AF F) σ J).continuous_iff.2 hU

theorem infTens_symm_finGL (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E)
    (hΦ : ∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z)))
    (k : GL (Fin d) (GlobalTheory.CuspRep.Af E)) (a b : Fin d) :
    GlobalTheory.LFun.infTens F E (Φ.symm ((GlobalTheory.CuspRep.finGL E d k).1 a b)) = (1 : Matrix (Fin d) (Fin d) (Ainf F ⊗[F] E)) a b := by
  have e1 : GlobalTheory.LFun.infTens F E (Φ.symm ((GlobalTheory.CuspRep.finGL E d k).1 a b)) = j.symm (((GlobalTheory.CuspRep.finGL E d k).1 a b).1) := by
    have key : ∀ x, GlobalTheory.LFun.infTens F E (Φ.symm x) = j.symm x.1 := fun x => by
      have e := congrArg Prod.fst (hΦ (Φ.symm x))
      rw [RingEquiv.apply_symm_apply] at e
      rw [e, RingEquiv.symm_apply_apply]
    exact key _
  rw [e1]
  change j.symm (((1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) a b - GlobalTheory.CuspRep.sFin E ((1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Af E)) a b) + GlobalTheory.CuspRep.sFin E (k.1 a b)).1) = _
  change j.symm (((1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) a b).1 - 0 + 0) = _
  rw [sub_zero, add_zero, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem finGL_mem_finPts (hι : GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι) (k : GL (Fin d) (GlobalTheory.CuspRep.Af E)) :
    ι (GlobalTheory.CuspRep.finGL E d k) ∈ finPts σ J := by
  obtain ⟨Φ, j, -, -, -, hΦ, hf⟩ := hι
  have hA : ∀ k : GL (Fin d) (GlobalTheory.CuspRep.Af E),
      (RingHom.mapMatrix (GlobalTheory.LFun.infTens F E)) ((GlobalTheory.CuspRep.finGL E d k).1.map Φ.symm) = 1 := by
    intro k
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact infTens_symm_finGL Φ j hΦ k a b
  have hB : (RingHom.mapMatrix (GlobalTheory.LFun.infTens F E))
      (cT (sigR (AF F) σ) ((GlobalTheory.CuspRep.finGL E d k)⁻¹.1.map Φ.symm)) = 1 := by
    rw [← map_inv]
    ext a b
    have e := congrArg (fun M => M b a) (hA k⁻¹)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, cT, Matrix.transpose_apply, infTens_sigR, e]
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (Ne.symm hab), if_neg hab, map_zero]
  simp only [finPts, MonoidHom.mem_ker, MonoidHom.comp_apply]
  apply Units.ext
  change (RingHom.mapMatrix (GlobalTheory.LFun.infTens F E)) (matHom (AF F) σ J (ι (GlobalTheory.CuspRep.finGL E d k))).1 = 1
  have hA' : ((GlobalTheory.CuspRep.finGL E d k).1.map Φ.symm - 1).map (GlobalTheory.LFun.infTens F E) = 0 := by
    rw [← RingHom.mapMatrix_apply, map_sub, hA, map_one, sub_self]
  have hB' : (cT (sigR (AF F) σ) ((GlobalTheory.CuspRep.finGL E d k)⁻¹.1.map Φ.symm) - 1).map (GlobalTheory.LFun.infTens F E) = 0 := by
    rw [← RingHom.mapMatrix_apply, map_sub, hB, map_one, sub_self]
  rw [hf]
  simp only [map_add (f := _), map_one, RingHom.mapMatrix_apply, Matrix.map_mul, hA', hB', Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem isOpen_rightInv_finGL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        IsOpen {k : GL (Fin d) (GlobalTheory.CuspRep.Af E) | ∀ g, ψ (ι (g * GlobalTheory.CuspRep.finGL E d k) * g₀) = ψ (ι g * g₀)} := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ K _ S l d h ι hι _ _ _ _ ψ hψ g₀ _
  obtain ⟨U, hUo, hU⟩ := hψ.1.level
  let H : Subgroup (GL (Fin d) (GlobalTheory.CuspRep.Af E)) :=
    { carrier := {k | ∀ g, ψ (ι (g * GlobalTheory.CuspRep.finGL E d k) * g₀) = ψ (ι g * g₀)}
      one_mem' := fun g => by simp
      mul_mem' := fun {a b} ha hb g => by
        show ψ (ι (g * GlobalTheory.CuspRep.finGL E d (a * b)) * g₀) = _
        rw [(GlobalTheory.CuspRep.finGL E d).map_mul a b, ← mul_assoc, hb (g * GlobalTheory.CuspRep.finGL E d a), ha g]
      inv_mem' := fun {a} ha g => by
        show ψ (ι (g * GlobalTheory.CuspRep.finGL E d a⁻¹) * g₀) = _
        have e : g * GlobalTheory.CuspRep.finGL E d a⁻¹ * GlobalTheory.CuspRep.finGL E d a = g := by
          rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
        rw [← ha (g * GlobalTheory.CuspRep.finGL E d a⁻¹), e] }
  let m : GL (Fin d) (GlobalTheory.CuspRep.Af E) → GAd σ J := fun k => g₀⁻¹ * ι (GlobalTheory.CuspRep.finGL E d k) * g₀
  have hm : Continuous m :=
    (continuous_const.mul ((continuous_of_isBlockEmb hι).comp (continuous_finGL d))).mul continuous_const
  have hN : (finPts σ J).Normal := MonoidHom.normal_ker _
  have hsub : m ⁻¹' (U : Set (GAd σ J)) ⊆ (H : Set (GL (Fin d) (GlobalTheory.CuspRep.Af E))) := by
    intro k hk g
    have hfin : m k ∈ finPts σ J := by
      have := hN.conj_mem _ (finGL_mem_finPts hι k) g₀⁻¹
      simpa [m] using this
    have e := hU (m k) hk hfin (ι g * g₀)
    rw [← e]
    simp only [m, map_mul, mul_assoc, mul_inv_cancel_left]
  have h1 : m ⁻¹' (U : Set (GAd σ J)) ∈ nhds (1 : GL (Fin d) (GlobalTheory.CuspRep.Af E)) := by
    refine hm.continuousAt.preimage_mem_nhds ?_
    have : m 1 = 1 := by simp [m]
    rw [this]
    exact hUo.mem_nhds U.one_mem
  exact H.isOpen_of_mem_nhds (Filter.mem_of_superset h1 hsub)

end GlobalTheory.BlockLevel
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspKinfFin

theorem kinf_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : GlobalTheory.CuspRep.Kinf E d => fun g : GlobalTheory.CuspRep.GA E d => ψ (ι (g * GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀))) := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ K _ S l d h ι _ _ _ _ _ ψ hψ g₀ hK
  classical
  let T : (GAd σ J → ℂ) →ₗ[ℂ] (GlobalTheory.CuspRep.GA E d → ℂ) :=
    { toFun := fun φ g => φ (ι g * g₀)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hV := hψ.1.kfin
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun g => ψ (g * k))).map T) ?_
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  refine ⟨fun x => ψ (x * (g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀)), Submodule.subset_span ⟨⟨_, hK k⟩, rfl⟩, ?_⟩
  funext g
  show ψ (ι g * g₀ * (g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀)) = _
  simp only [map_mul, mul_assoc, mul_inv_cancel_left]

end GlobalTheory.CuspKinfFin
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SqTop.CondExpo

theorem levelLe_of_le {K : Type} [Field K] [NumberField K] {χ : Formalism.L2.Host.HChar K} {v : HeightOneSpectrum (𝓞 K)}
    {a b : ℕ} (h : χ.LevelLe v a) (hab : a ≤ b) : χ.LevelLe v b :=
  fun x hx hle => h x hx (hle.trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hab))))

theorem expAt_succ {K : Type} [Field K] [NumberField K] {χ : Formalism.L2.Host.HChar K} {v : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    (h : χ.LevelLe v (n + 1)) (h' : ¬ χ.LevelLe v n) : GlobalTheory.CMVal.ExpAt χ v (n + 1) := fun m =>
  ⟨fun hm => by
    by_contra hlt
    exact h' (levelLe_of_le hm (by omega)), fun hm => levelLe_of_le h hm⟩

end GlobalTheory.SqTop.CondExpo


open GlobalTheory.SqTop.CondExpo in
theorem GlobalTheory.SqTop.CondExpo.expo_modul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) (i j : Fin D.R.m) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), (∀ w ∈ locPl G t, GlobalTheory.CMVal.ExpAt (nuH G t i j) w (c w)) →
    (∀ w ∈ locPl G t, 1 ≤ c w) ∧ modul (locPl G t) c = GlobalTheory.SqTop.modT G t := by
  intro D T L sc G μ₀ hL t i j c hc
  have k1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have k2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  have hμ := L.C.isMu0 j
  have enu : nuH G t i j = L.C.mu0 j * L.xiH t * (G.ch.chiH (D.R.m - i))⁻¹ := by
    rw [nuH, div_eq_mul_inv]
  have echi : G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH t * (nuH G t i j)⁻¹ := by
    rw [enu, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]

  have hW : ∀ v ∈ G.pl.S0, GlobalTheory.CMVal.ExpAt (nuH G t i j) (G.pl.w v) (SqNum.condExp G.pl v) := by
    intro v hv
    have hu := G.pl.under_w hv
    by_cases h0 : v = G.pl.v0
    · subst h0
      rw [SqNum.condExp, if_pos rfl]
      refine expAt_succ (n := 0) ?_ ?_
      · rw [enu]
        exact ((hμ.tame _).mul (hL.xi_tame t _)).mul (G.ch.lev0 _ k1 k2 _ hu).1.inv
      · intro h
        exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)
    · have h1 : v ∈ S1 D := (G.pl.mem_S0_of_sum_eq.1 hv).resolve_left h0
      rw [SqNum.condExp, if_neg h0]
      have hl := G.ch.lev1 _ k1 k2 (G.pl.w v) (by rw [hu]; exact h1)
      refine expAt_succ (n := 1) ?_ ?_
      · rw [enu]
        exact ((levelLe_of_le (hμ.tame _) (by omega)).mul (levelLe_of_le (hL.xi_tame t _) (by omega))).mul hl.1.inv
      · intro h
        apply hl.2
        rw [echi]
        exact ((hμ.tame _).mul (hL.xi_tame t _)).mul h.inv

  have hQ : ∀ w ∈ twPl G t, GlobalTheory.CMVal.ExpAt (nuH G t i j) w 1 := by
    intro w hw
    have hw' : w ∈ L.Q t ∧ w ∉ G.pl.W0 := by
      simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hw
      exact ⟨hw.1.resolve_left hw.2, hw.2⟩
    have hS1 : w.under (𝓞 D.host.F) ∉ S1 D := fun h => by
      refine hw'.2 ?_
      rw [G.pl.w_Q t w hw'.1 h]
      exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
    have hS0 : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h =>
      (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t w hw'.1) hS1
    refine expAt_succ (n := 0) ?_ ?_
    · rw [enu]
      exact ((hμ.tame _).mul (hL.xi_tame t _)).mul
        (Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ k1 k2 w hS0) 1).inv
    · intro h
      exact GlobalTheory.SqTop.nuH_not_unrAt_twPl G hL t i j w hw ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)
  have cW : ∀ v ∈ G.pl.S0, c (G.pl.w v) = SqNum.condExp G.pl v := fun v hv =>
    (hc _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv))).unique (hW v hv)
  have cQ : ∀ w ∈ twPl G t, c w = 1 := fun w hw =>
    (hc w (Finset.mem_filter.1 hw).1).unique (hQ w hw)
  refine ⟨fun w hw => ?_, ?_⟩
  · by_cases h : w ∈ G.pl.W0
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      rw [cW v hv, SqNum.condExp]
      split_ifs <;> omega
    · rw [cQ w (Finset.mem_filter.2 ⟨hw, h⟩)]
  · rw [modul, modT, ← Finset.prod_filter_mul_prod_filter_not (locPl G t) (fun w => w ∈ G.pl.W0)]
    have e1 : (locPl G t).filter (fun w => w ∈ G.pl.W0) = G.pl.W0 := by
      ext w
      simp only [Finset.mem_filter, GlobalTheory.FunObj.locPl, Finset.mem_union]
      tauto
    have e2 : (locPl G t).filter (fun w => w ∉ G.pl.W0) = twPl G t := rfl
    rw [e1, e2]
    congr 1
    · rw [Places.W0, Finset.prod_image fun v hv v' hv' h =>
        (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))]
      exact Finset.prod_congr rfl fun v hv => by rw [cW v hv]
    · exact Finset.prod_congr rfl fun w hw => by rw [cQ w hw, pow_one]

end
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

namespace GlobalTheory.BottomRallis.TrivParFun

variable {D : D7}

theorem isParamFun_one_trivPar : ∀ {D : D7} (A : HSp D) (LA : Lat A) (Sf : Finset (FinPl D)), IsSelfDualC A LA →
    (∀ v ∉ Sf, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) →
    GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) (fun _ : GA D A => (1 : ℂ))
      (GlobalTheory.BottomRallis.trivPar A.rank) := by
  intro D V L Sf hLd _ v _ w h
  have hH := GlobalTheory.Doubling.isHermND_gram V
  have hL := hLd.1
  classical
  have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
    intro V Λ hΛ
    exact Formalism.IndefR.Datum.IsSelfDualC.isFullLattice V Λ hΛ
  haveI : Submodule.IsFullLattice D.host.E L := hfull V L hLd
  have hd := GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hLd v
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := fun P _ => by
    have := GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  let const : ℂ →ₗ[ℂ] (GA D V → ℂ) := LinearMap.pi fun _ => LinearMap.id
  have hconst : const 1 = (fun _ : GA D V => (1 : ℂ)) := rfl
  have h0 : (fun _ : GA D V => (1 : ℂ)) ≠ 0 := fun e => one_ne_zero (congrFun e 1)
  rcases (LFun.exists_isInertChart _ (isCMExt_host D) v).1 hun with hs | ⟨w', hw'⟩
  · obtain ⟨e, he, -, -⟩ := LFun.SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg Submodule.IsFullLattice.span_eq_top h hs hd
    refine Or.inl ⟨hs, e, he, ?_⟩
    rw [← hconst]
    exact ((LFun.Model.hasSatGL_trivial w V.rank).2 1 (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl)
      one_ne_zero).map const (fun _ _ => rfl) (by simpa only [hconst] using h0)
  · obtain rfl := (GlobalTheory.LFun.InertChart.under_eq_iff hw' w).1 h
    obtain ⟨-, ⟨τ, hτ, -⟩, -, -, hconj⟩ := (LFun.exists_isInertChart _ (isCMExt_host D) v).2 w h hw'
    obtain ⟨⟨ϖ, hϖ⟩, hch⟩ := hconj τ hτ
    obtain ⟨e, he, -, -⟩ := hch V.rank V.gram L hH hL.fg Submodule.IsFullLattice.span_eq_top hd
    refine Or.inr ⟨hw', τ, ϖ, e, _root_.GlobalTheory.LFun.Model.rhoU (LFun.qV_ne_zero v) V.rank, hϖ, he, ?_, ?_⟩
    · rw [← hconst]
      exact ((LFun.Model.hasSatU_trivial hϖ (LFun.qV_ne_zero v) V.rank).2 1
        (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) one_ne_zero).map hϖ const
        (fun _ _ => rfl) (by simpa only [hconst] using h0)
    · rw [GlobalTheory.Core.Rk.Exh.Model.bcParam_rho]
      exact GlobalTheory.Core.Rk.Exh.Model.seg_eq_str (LFun.qV_ne_zero v) (LFun.InertChart.absNorm_eq D.sp.cm.deg2 hw') _

end GlobalTheory.BottomRallis.TrivParFun

end
end
