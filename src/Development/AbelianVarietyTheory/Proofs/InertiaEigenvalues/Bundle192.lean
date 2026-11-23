module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle029
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Formalism.GaloisCohomology.StatementLoc
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Mathlib.Data.Matrix.PEquiv
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle178
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle177
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle180
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle176
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
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle004
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section
open GlobalTheory.BI

namespace GlobalTheory.BrauerZero

def D0 (G : Type) [Group G] : AddSubgroup (G → ℂ) :=
  AddSubgroup.closure {f | ∃ (H : Subgroup G) (χ : H →* ℂˣ),
    f = ind H (fun h => (χ h : ℂ)) - ind H (fun _ => 1)}

theorem ind_sub {G : Type} [Group G] [Finite G] (T : Subgroup G) (a b : T → ℂ) :
    ind T (a - b) = ind T a - ind T b :=
  (indAddHomComplex T).map_sub a b

theorem ind_const {G : Type} [Group G] [Finite G] (T : Subgroup G) (c : ℂ) (g : G) :
    ind T (fun _ => c) g = c * ind T (fun _ => 1) g := by
  classical
  haveI := Fintype.ofFinite G
  simp only [ind, finsum_eq_sum_of_fintype, ext0]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

theorem ind_apply_one {G : Type} [Group G] [Finite G] (T : Subgroup G) (ψ : T → ℂ) :
    ind T ψ 1 = (T.index : ℂ) * ψ 1 := by
  classical
  haveI := Fintype.ofFinite G
  have h1 : ∀ x : G, ext0 T ψ (x⁻¹ * 1 * x) = ψ 1 := fun x => by
    have e : x⁻¹ * 1 * x = 1 := by group
    simp only [ext0, e, dif_pos T.one_mem]
    rfl
  simp only [ind, finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← T.card_mul_index]
  have : (Nat.card T : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := T)).ne'
  push_cast
  field_simp

theorem ind_top {G : Type} [Group G] [Finite G] (F : G → ℂ) (hF : ∀ g x : G, F (x⁻¹ * g * x) = F g) :
    ind (⊤ : Subgroup G) (fun h => F h) = F := by
  classical
  haveI := Fintype.ofFinite G
  funext g
  simp only [ind, finsum_eq_sum_of_fintype, ext0, Subgroup.mem_top, dite_true, hF]
  have hc : Nat.card {x : G // True} = Nat.card G := Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hc]
  have : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  field_simp

theorem indFun_eq_ind {G : Type} [Group G] [Fintype G] (H : Subgroup G) (f : H → ℂ) :
    GlobalTheory.Published.indFun H f = ind H f := by
  classical
  funext g
  simp only [GlobalTheory.Published.indFun, ind, finsum_eq_sum_of_fintype, ext0]

end GlobalTheory.BrauerZero
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory

theorem exists_descend_pair_quotient {Γ M : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [TopologicalSpace M] (N : Subgroup Γ) (w : Γ × Γ → M)
    (hw : Continuous w) (h : ∀ g h : Γ, ∀ n ∈ N, ∀ n' ∈ N, w (g * n, h * n') = w (g, h)) :
    ∃ W : (Γ ⧸ N) × (Γ ⧸ N) → M, Continuous W ∧
      ∀ g h : Γ, W ((g : Γ ⧸ N), (h : Γ ⧸ N)) = w (g, h) := by
  refine ⟨fun p => Quotient.liftOn₂' p.1 p.2 (fun a b => w (a, b)) ?_, ?_, fun g h => rfl⟩
  · intro a b a' b' ha hb
    have e := h a b _ (QuotientGroup.leftRel_apply.1 ha) _ (QuotientGroup.leftRel_apply.1 hb)
    simpa using e.symm
  · rw [((QuotientGroup.isOpenQuotientMap_mk (N := N)).prodMap
      (QuotientGroup.isOpenQuotientMap_mk (N := N))).isQuotientMap.continuous_iff]
    exact hw

theorem sum_inv_eq_zero_of_unramified_cocycle : PoitouTateTotallyComplex → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ζ : Ω), IsPrimitiveRoot ζ (l ^ 1) → ∃ inv : InvFam F Ω l 1, IsLocalInvariants ζ inv ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l → ∀ Av : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v) → ∀ w : Z2 (muRep F Ω l 1), (∀ g h : G F Ω, ∀ n ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), ∀ n' ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), w.1 (g * n, h * n') = w.1 (g, h)) → ∀ wl : ∀ v, Z2 (muLoc F l 1 (Av v)), (∀ v (g h : Dec (F := F) (Av v)), (wl v).1 (g, h) = w.1 ((g : G F Ω), (h : G F Ω))) → ∑ v ∈ S, inv (Av v) (Submodule.Quotient.mk (wl v)) = 0 := by
  intro hPT F Ω _ _ _ _ _ _ l _ ζ hζ
  obtain ⟨inv, hinv, H⟩ := hPT.annihilators F Ω l 1 one_pos ζ hζ
  refine ⟨inv, hinv, fun S hS Av hA w hw wl hwl => ?_⟩
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (Ω := Ω) (r := 1) hS
  obtain ⟨W, hWc, hW⟩ := exists_descend_pair_quotient _ w.1 w.2.1 hw
  have hmem : W ∈ Z2 (charRep μ) := by
    refine ⟨hWc, fun g h k => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective h
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
    have e := w.2.2 g h k
    have e2 : μ (g : G F Ω ⧸ _) = cycMod F Ω l 1 g := DFunLike.congr_fun hμ g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hW, hW, hW, hW, charRep_apply, e2]
    exact e
  have e := (H S hS (fun v => Av v.1) (fun v => hA v.1) μ hμ).1
    (Submodule.Quotient.mk ⟨W, hmem⟩)
  rw [← Finset.sum_coe_sort]
  refine Eq.trans (Finset.sum_congr rfl fun v _ => ?_) e
  refine congrArg (inv (Av v.1)) ?_
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => ?_))
  exact (hwl v.1 p.1 p.2).trans (hW _ _).symm

end GlobalTheory
end

section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

theorem _root_.GlobalTheory.T.cyclotomicCharacter_congr_root_of_unity_pow : ∀ {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (g : Formalism.GaloisCohomology.GK p K) (k : ℕ), ∃ ζ : PadicAlgCl p, ζ ^ (p ^ k) = 1 ∧ ∀ a : ℕ, g ζ = ζ ^ a → (a : ZMod (p ^ k)) = PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) : ℤ_[p]ˣ) : ℤ_[p]) := by
  first | exact @GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr | exact GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr | (intros; apply GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr <;> assumption)
end

section

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

theorem _root_.GlobalTheory.T.simpleRepCentralIdempotent_isCentralIdempotent : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ → zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := by
  first | exact @GlobalTheory.SerOSys.zIdem_centralIdempotent | exact GlobalTheory.SerOSys.zIdem_centralIdempotent | (intros; apply GlobalTheory.SerOSys.zIdem_centralIdempotent <;> assumption)
end

section

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

theorem _root_.GlobalTheory.T.simpleRepCentralIdempotent_mul_eq_zero_of_ne : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ), Simple τ → Simple τ' → zIdem τ ≠ zIdem τ' → zIdem τ * zIdem τ' = 0 := by
  first | exact @GlobalTheory.SerOSys.zIdem_mul_eq_zero_of_ne | exact GlobalTheory.SerOSys.zIdem_mul_eq_zero_of_ne | (intros; apply GlobalTheory.SerOSys.zIdem_mul_eq_zero_of_ne <;> assumption)
end

section

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys.TranspLabel

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def permGL {α : Type} [Fintype α] [DecidableEq α] (π : α ≃ α) : GL α K :=
  ⟨π.symm.toPEquiv.toMatrix, π.toPEquiv.toMatrix, by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply], by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply]⟩

theorem glEquiv_perm {α : Type} [Fintype α] [DecidableEq α] (π : α ≃ α) (g : GL α K) :
    glEquiv K π g = permGL π * g * (permGL π)⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show Matrix.reindex π π (g : Matrix α α K) =
    π.symm.toPEquiv.toMatrix * (g : Matrix α α K) * π.toPEquiv.toMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

def repIsoOf {G : Type} [Group G] (V W : FDRep ℂ G) (L : (V : Type) ≃ₗ[ℂ] (W : Type))
    (h : ∀ g v, L (V.ρ g v) = W.ρ g (L v)) : V ≅ W :=
  Action.mkIso (LinearEquiv.toFGModuleCatIso L) (fun g => by
    ext v
    exact h g v)

def rhoEquiv {G : Type} [Group G] (σ : FDRep ℂ G) (P : G) : (σ : Type) ≃ₗ[ℂ] (σ : Type) :=
  LinearEquiv.ofLinear (σ.ρ P) (σ.ρ P⁻¹)
    (LinearMap.ext fun v => by
      show (σ.ρ P * σ.ρ P⁻¹) v = v
      rw [← map_mul, mul_inv_cancel, map_one]; rfl)
    (LinearMap.ext fun v => by
      show (σ.ρ P⁻¹ * σ.ρ P) v = v
      rw [← map_mul, inv_mul_cancel, map_one]; rfl)

theorem rho_conj {G : Type} [Group G] (σ : FDRep ℂ G) (P X : G) (w : (σ : Type)) :
    σ.ρ P (σ.ρ X w) = σ.ρ (P * X * P⁻¹) (σ.ρ P w) := by
  rw [show σ.ρ (P * X * P⁻¹) (σ.ρ P w) = σ.ρ (P * X * P⁻¹ * P) w by rw [map_mul σ.ρ (P * X * P⁻¹) P]; rfl,
    inv_mul_cancel_right, map_mul]
  rfl

theorem lab_transp_transp {C : LabelConv K} (O : LabelMap K C) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (σ : FDRep ℂ (GL α K)) (e : α ≃ β) (d : ℕ) (e₁ : α ≃ Fin d) (e₂ : β ≃ Fin d) :
    O.lab d (transp e₁ σ) = O.lab d (transp e₂ (transp e σ)) := by
  apply O.lab_iso
  let π : α ≃ α := e₁.trans (e.trans e₂).symm
  have hA : ∀ γ : GL (Fin d) K, (glEquiv K e).symm ((glEquiv K e₂).symm γ) =
      glEquiv K π ((glEquiv K e₁).symm γ) := by
    intro γ
    apply Units.ext
    ext i j
    simp [π, Formalism.L2.PT.coe_glEquiv_symm, Formalism.L2.PT.coe_glEquiv]
  refine ⟨repIsoOf _ _ (rhoEquiv σ (permGL π)) fun γ v => ?_⟩
  show σ.ρ (permGL π) (σ.ρ ((glEquiv K e₁).symm γ) v) =
    σ.ρ ((glEquiv K e).symm ((glEquiv K e₂).symm γ)) (σ.ρ (permGL π) v)
  rw [hA, glEquiv_perm]
  exact rho_conj σ _ _ v

theorem labO_transp {C : LabelConv K} (O : LabelMap K C) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (σ : FDRep ℂ (GL α K)) :
    labO O (transp e σ) = labO O σ := by
  have key : ∀ (d : ℕ) (e₂ : β ≃ Fin d) (d' : ℕ) (e₁ : α ≃ Fin d'),
      O.lab d (transp e₂ (transp e σ)) = O.lab d' (transp e₁ σ) := by
    intro d e₂ d' e₁
    have hd : d = d' := by
      have h1 := Fintype.card_congr e₂
      have h2 := Fintype.card_congr e₁
      have h3 := Fintype.card_congr e
      simp only [Fintype.card_fin] at h1 h2
      omega
    subst hd
    exact (lab_transp_transp O σ e d e₁ e₂).symm
  exact key _ _ _ _

end GlobalTheory.SerOSys.TranspLabel

namespace GlobalTheory.SerOSys.TranspLabel

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

end GlobalTheory.SerOSys.TranspLabel
end
end

section

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

theorem _root_.GlobalTheory.T.repIso_of_simple_of_centralIdempotent_eq : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ), Simple τ → Simple τ' → zIdem τ = zIdem τ' → RepIso τ.ρ τ'.ρ := by
  first | exact @GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple | exact GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple | (intros; apply GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CycIntegral

theorem cyc_mem (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) (g : ↥(GK K)) :
    ∃ b : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL b := by
  obtain ⟨_, _, _, _, hopen⟩ := hO
  obtain ⟨a, ha, _⟩ := P.χQ_cyc (g : GQ l) 0 1 (one_pow _)
  have hn : ‖((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    have h1 : ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) =
        (((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l]) := by ring
    rw [h1]
    refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
    · simpa using ha
    · exact_mod_cast Padic.norm_int_le_one (a : ℤ)
  have hmem := GlobalTheory.GoodCoeff.padicInt_mem (algebraMap O LL).range
    (by rw [RingHom.coe_range]; exact hopen) (⟨_, hn⟩ : ℤ_[l])
  obtain ⟨b, hb⟩ := RingHom.mem_range.1 hmem
  refine ⟨b, ?_⟩
  rw [hb]
  simp [cycLL, LocPrime.PD_χ]

theorem cyc_lattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) := by
  intro l _ P K LL _ _ _ O _ _ hO
  obtain ⟨⟨hD, hV, hF⟩, _⟩ := id hO
  refine ⟨⟨LinearMap.range (Algebra.linearMap O LL), ?_, ?_, ?_, ?_⟩, rfl⟩
  · rintro g _ ⟨x, rfl⟩
    obtain ⟨b, hb⟩ := cyc_mem l P K LL O hO g
    refine ⟨b * x, ?_⟩
    show algebraMap O LL (b * x) = ((cycLL (P.PD K) LL g : LLˣ) : LL) • algebraMap O LL x
    rw [map_mul, hb, smul_eq_mul]
  · rw [← Submodule.map_top]
    exact Submodule.FG.map _ Module.Finite.fg_top
  · exact Module.Free.of_equiv
      (LinearEquiv.ofInjective (Algebra.linearMap O LL) (IsFractionRing.injective O LL))
  · rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL
        ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) :=
      Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x h1

end GlobalTheory.CycIntegral
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

noncomputable section
namespace GlobalTheory.DualTwist

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l)
  {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]

def dualEquiv : (Fin (finrank ℚ_[l] V) → ℚ_[l]) ≃ₗ[ℚ_[l]] Module.Dual ℚ_[l] V :=
  (Module.finBasis ℚ_[l] V).dualBasis.equivFun.symm

theorem dualEquiv_basis (z : Fin (finrank ℚ_[l] V) → ℚ_[l]) (i : Fin (finrank ℚ_[l] V)) :
    dualEquiv z (Module.finBasis ℚ_[l] V i) = z i := by
  simp [dualEquiv, Basis.equivFun_symm_apply, Finset.sum_apply, Basis.dualBasis_apply_self, Finsupp.single_apply]

theorem dualEquiv_symm_apply (f : Module.Dual ℚ_[l] V) (i : Fin (finrank ℚ_[l] V)) :
    (dualEquiv (V := V)).symm f i = f (Module.finBasis ℚ_[l] V i) := by
  conv_rhs => rw [← (dualEquiv (V := V)).apply_symm_apply f]
  rw [dualEquiv_basis]

def chiS (g : ↥(GK K)) : ℚ_[l] := ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])

theorem chiS_mul (g h : ↥(GK K)) : chiS P K (g * h) = chiS P K g * chiS P K h := by
  simp [chiS]

theorem chiS_one : chiS P K 1 = 1 := by simp [chiS]

def dualOp (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) :
    (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) where
  toFun y := chiS P K g • (dualEquiv (V := V)).symm ((dualEquiv y).comp (ρ g⁻¹))
  map_add' y z := by simp [LinearMap.add_comp, smul_add]
  map_smul' c y := by simp [LinearMap.smul_comp, smul_comm c]

theorem dualEquiv_dualOp (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) (y) :
    dualEquiv (dualOp P K ρ g y) = chiS P K g • (dualEquiv y).comp (ρ g⁻¹) := by
  simp [dualOp]

def dualRep (ρ : Representation ℚ_[l] ↥(GK K) V) :
    Representation ℚ_[l] ↥(GK K) (Fin (finrank ℚ_[l] V) → ℚ_[l]) where
  toFun g := dualOp P K ρ g
  map_one' := by
    refine LinearMap.ext fun y => ?_
    apply (dualEquiv (V := V)).injective
    rw [dualEquiv_dualOp]
    simp [chiS_one, Module.End.one_eq_id]
  map_mul' g h := by
    refine LinearMap.ext fun y => ?_
    apply (dualEquiv (V := V)).injective
    rw [Module.End.mul_apply, dualEquiv_dualOp, dualEquiv_dualOp, dualEquiv_dualOp, chiS_mul,
      mul_inv_rev, map_mul, Module.End.mul_eq_comp, LinearMap.smul_comp, smul_smul, LinearMap.comp_assoc]

def dualPair : V →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] ℚ_[l] :=
  (dualEquiv (V := V)).toLinearMap.flip

theorem dualPair_apply (x : V) (y : Fin (finrank ℚ_[l] V) → ℚ_[l]) : dualPair x y = dualEquiv y x := rfl

end GlobalTheory.DualTwist

namespace GlobalTheory.DualTwist
variable {l : ℕ} [Fact l.Prime]

theorem chiS_eq (P : LocPrime l) (K : FinExt l) (g : ↥(GK K)) :
    chiS P K g = (P.χQ (g : GQ l) : ℚ_[l]) := by
  simp [chiS, cycLL, P.PD_χ]

theorem chiS_cont (P : LocPrime l) (K : FinExt l) : Continuous (chiS P K) := by
  have h : chiS P K = fun g : ↥(GK K) => (P.χQ (g : GQ l) : ℚ_[l]) := funext (chiS_eq P K)
  rw [h]
  exact (GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val

theorem exists_dual1 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → ∃ (ρ' : Representation ℚ_[l] ↥(GK K) (Fin (finrank ℚ_[l] V) → ℚ_[l])) (m : V →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] ℚ_[l]), (∀ y, Continuous fun g => ρ' g y) ∧ IsDual1 (P.PD K) ρ ρ' m := by
  intro l _ P K V _ _ _ _ _ _ _ ρ hc
  refine ⟨dualRep P K ρ, dualPair, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    apply continuous_pi
    intro i
    have h : (fun g : ↥(GK K) => dualRep P K ρ g y i) =
        fun g => chiS P K g * dualEquiv y (ρ g⁻¹ (Module.finBasis ℚ_[l] V i)) := by
      funext g
      change dualOp P K ρ g y i = _
      simp [dualOp, dualEquiv_symm_apply]
    rw [h]
    have hy : Continuous (dualEquiv (V := V) y) :=
      IsModuleTopology.continuous_of_linearMap (dualEquiv (V := V) y)
    exact (chiS_cont P K).mul (hy.comp ((hc _).comp continuous_inv))
  · intro g x y
    change dualEquiv (dualOp P K ρ g y) (ρ g x) = chiS P K g * dualEquiv y x
    rw [dualEquiv_dualOp, LinearMap.smul_apply, LinearMap.comp_apply, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, smul_eq_mul]
  · intro x hx
    apply (Module.finBasis ℚ_[l] V).forall_coord_eq_zero_iff.mp
    intro i
    have := hx ((dualEquiv (V := V)).symm ((Module.finBasis ℚ_[l] V).coord i))
    rwa [dualPair_apply, LinearEquiv.apply_symm_apply] at this
  · intro y hy
    funext i
    exact (dualEquiv_basis y i).symm.trans (hy _)
  · simp

end GlobalTheory.DualTwist
end
end

section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

theorem _root_.GlobalTheory.T.exists_dualLattice_pairing_eq_inv_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), IsLatticeIn D.T → PerfectRight D.bT → ∀ ϖ : O, Irreducible ϖ → ∀ x : VT ⧸ D.T, x ≠ 0 → ∃ f : ↥D.T', pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  first | exact @GlobalTheory.LocDualInt.exists_dual_pairKO_eq_inv_unif | exact GlobalTheory.LocDualInt.exists_dual_pairKO_eq_inv_unif | (intros; apply GlobalTheory.LocDualInt.exists_dual_pairKO_eq_inv_unif <;> assumption)
end

section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

theorem _root_.GlobalTheory.T.continuous_quotient_torsion_bounded : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] [TopologicalSpace V] [IsTopologicalAddGroup V] {X : Type} [TopologicalSpace X] [CompactSpace X] (T : Submodule O V), IsLatticeIn T → IsOpen (T : Set V) → ∀ ϖ : O, Irreducible ϖ → ∀ c : X → V ⧸ T, Continuous c → ∃ r : ℕ, ∀ x, ϖ ^ r • c x = 0 := by
  first | exact @GlobalTheory.LatticeQuotBound.pow_smul_eq_zero_of_compact | exact GlobalTheory.LatticeQuotBound.pow_smul_eq_zero_of_compact | (intros; apply GlobalTheory.LatticeQuotBound.pow_smul_eq_zero_of_compact <;> assumption)
end
