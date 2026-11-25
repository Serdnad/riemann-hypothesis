module

import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStandardIsometryFourthPowerSplitPrime
public import Formalism.LocalToGlobal.InertKernelTheory.StatementReBase
public import Formalism.LocalToGlobal.InertKernelTheory.StatementCurve
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelConditionEquivalent
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.HalfTorsionNotMemCmLattice
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.HalfPeriodStandardCM
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IsTorsionPointStandardCM
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique

@[expose] public section

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (CmOK cmL matH stdH stdLat pow4 imgLat relIdx StdData Th alphaQ kernel4 tens4 stdChar)
open Formalism.L2.Th1.Top (IsLTNorm)

namespace ReBase

theorem odd_norm {D : D7} {cc : Ideal (𝓞 D.host.K)} (hcc : TaylorLogMetric.IsCurveIdeal D cc) : Odd (Ideal.absNorm cc) := by
  have hc2 : Nat.Coprime (Ideal.absNorm cc) 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 _) hcc.2
  rcases Nat.even_or_odd (Ideal.absNorm cc) with he | ho
  · exact absurd (Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.1 he) hc2) (by decide)
  · exact ho

theorem cm_change_of_base : CmReBase := by
  apply _root_.GlobalTheory.CmThetaMoment.cmReBase' <;> assumption

theorem isThMM_eq {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B B' : Base D cc δ) (hγ : B'.gC = B.gC)
    (hκ : B'.kappa = B.kappa) (hω : (B.ω₀ - B'.ω₀) / 2 ∈ B'.L.lattice) : B'.IsThMM = B.IsThMM := by
  have h := KS.lattice_eq B B'
  have e : IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa = IsThM B'.L B'.ω₀ B.cq B.lamM B.gC B.kappa := by
    funext θ
    unfold IsThM kernel4 Formalism.L2.Th1.H.F0 Formalism.L2.Th1.H.stdLat
    rw [KS.hOne_congr h, KS.stdH_congr h, KS.thetaNull_congr_lattice h hω (Base.half_not_mem B'), h]
  show IsThM B'.L B'.ω₀ B.cq B.lamM B'.gC B'.kappa = IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa
  rw [hγ, hκ, e]

theorem theta_change_of_base : ThMMReBase := by
  intro D cc δ B hcc
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, hlat, ht, hω⟩ := cm_change_of_base D cc δ B hcc (delta_ne_of_base B)
  have hω' : (B.ω₀ - (g : ℂ) * δ * a₀) / 2 ∈ (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice :=
    (KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat _).1 hω
  refine ⟨a₀, g, b₀, c₀, ha, hd, hl, KS.cmBase B a₀ b₀ c₀ ha hd ((g : ℂ) * δ) hl hcm hlat, hcm, hN,
    KS.cmBase_isCm B a₀ b₀ c₀ ha hd _ hl hcm hlat, KS.lattice_eq _ B, rfl, rfl, rfl,
    (KS.lattice_eq B (KS.cmBase B a₀ b₀ c₀ ha hd ((g : ℂ) * δ) hl hcm hlat)) ▸ hω',
    isThMM_eq B _ rfl rfl hω', (KS.thMM_reBase B _ hlat _ (KS.isTorsionPoint_standard_CM a₀ b₀ c₀ ha hd _ hl hcm hlat) hω').symm⟩

theorem stdLat_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : Type) : stdLat L n = stdLat L' n := by
  unfold Formalism.L2.Th1.H.stdLat; rw [h]

theorem isLTNorm_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 s2 ε : MaximalUnramifiedExtension l) : IsLTNorm l L ι g2 g3 s2 ε ↔ IsLTNorm l L' ι g2 g3 s2 ε := by
  obtain ⟨-, -, -, -, hs, -, -, h2, h3⟩ := _root_.Formalism.L2.Th1.F.lattice_only L L' h
  unfold IsLTNorm
  rw [h2, h3, hs]

theorem th0Char_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ} (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice)
    {x : ℂ} (hx : x ∈ L'.lattice) : Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ x = Formalism.L2.Th1.F.thetaZeroCharacter L' ω₀' x := by
  apply _root_.GlobalTheory.CmThetaMoment.th0Char_congr <;> assumption

theorem stdData_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ} (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice)
    (hn : ω₀ / 2 ∉ L.lattice) {n : Type} [Fintype n] [DecidableEq n] {hh : Matrix n n ℂ} {Λ : AddSubgroup (n → ℂ)}
    {α : (n → ℂ) → ℂ} {β : (Fin 4 × n → ℂ) → ℂ} {g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)}
    (S : StdData L' ω₀' hh Λ α β g) : StdData L ω₀ hh Λ α β g := by
  apply _root_.GlobalTheory.CmThetaMoment.stdData_congr <;> assumption

end ReBase

end Formalism.L2.KerInert
