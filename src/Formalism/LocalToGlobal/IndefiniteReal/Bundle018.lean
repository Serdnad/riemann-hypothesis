module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle482
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.Divisibility.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle003
public import Formalism.LocalToGlobal.Columns.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelFrame
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Cong

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

theorem cong_natCast_eq_tmul_one (k : ℕ) : (k : ReciprocityTheory.Aut.AL L) = (k : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L) := by
  rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast]

theorem cong_natCast_eq_one_tmul (k : ℕ) : (k : ReciprocityTheory.Aut.AL L) = (1 : L) ⊗ₜ[L⁺] (k : ReciprocityTheory.Aut.AFplus L) := by
  rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]

theorem cong_adele_nat_denom (a : ReciprocityTheory.Aut.AFplus L) :
    ∃ k : ℕ, 0 < k ∧ ∀ v, ((k : ReciprocityTheory.Aut.AFplus L) * a) v ∈ v.adicCompletionIntegers L⁺ := by
  obtain ⟨d, hd0, hd⟩ := Formalism.UG.P.levelaf_adele_denom (F := L⁺) a
  set k := Ideal.absNorm (Ideal.span {d}) with hk
  have hk0 : k ≠ 0 := by
    rw [hk, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨k, Nat.pos_of_ne_zero hk0, ?_⟩
  have e : (k : ReciprocityTheory.Aut.AFplus L) * a =
      algebraMap (𝓞 L⁺) (ReciprocityTheory.Aut.AFplus L) c * (algebraMap (𝓞 L⁺) (ReciprocityTheory.Aut.AFplus L) d * a) := by
    rw [← mul_assoc, ← map_mul, hc, map_natCast]
  have hm : (k : ReciprocityTheory.Aut.AFplus L) * a ∈ Formalism.UG.intAd L⁺ := by
    rw [e]
    exact Subring.mul_mem _ (Formalism.UG.P.levelaf_int_mem c) hd
  exact hm

theorem cong_nat_denom (x : ReciprocityTheory.Aut.AL L) : ∃ d : ℕ, 0 < d ∧ (d : ReciprocityTheory.Aut.AL L) * x ∈ ReciprocityTheory.Aut.ALint L := by
  apply GlobalTheory.FinTypCount.exists_denom <;> assumption

theorem cong_dvd_mem {x : ReciprocityTheory.Aut.AL L} {d e : ℕ} (hx : (d : ReciprocityTheory.Aut.AL L) * x ∈ ReciprocityTheory.Aut.ALint L) (hde : d ∣ e) :
    (e : ReciprocityTheory.Aut.AL L) * x ∈ ReciprocityTheory.Aut.ALint L := by
  obtain ⟨c, rfl⟩ := hde
  rw [Nat.cast_mul, mul_comm (d : ReciprocityTheory.Aut.AL L), mul_assoc]
  exact Subring.mul_mem _ (natCast_mem _ _) hx

end Cong

theorem congConj_holds (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : CongConj L n := by
  classical
  intro h N hN
  choose D hD0 hD using fun x : ReciprocityTheory.Aut.AL L => cong_nat_denom (L := L) x
  set H : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) := (h.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) with hH
  set Hi : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) :=
    ((h⁻¹ : Formalism.AUTREP.GAf L n).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) with hHi
  set d : ℕ := ∏ i, ∏ j, (D (H i j) * D (Hi i j)) with hd
  have hd0 : 0 < d := Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => Nat.mul_pos (hD0 _) (hD0 _)
  have hdv : ∀ i j, D (H i j) * D (Hi i j) ∣ d := fun i j =>
    dvd_trans (Finset.dvd_prod_of_mem (fun j => D (H i j) * D (Hi i j)) (Finset.mem_univ j))
      (Finset.dvd_prod_of_mem (fun i => ∏ j, D (H i j) * D (Hi i j)) (Finset.mem_univ i))
  have hHd : ∀ i j, (d : ReciprocityTheory.Aut.AL L) * H i j ∈ ReciprocityTheory.Aut.ALint L := fun i j =>
    cong_dvd_mem (hD _) (dvd_trans (dvd_mul_right _ _) (hdv i j))
  have hHid : ∀ i j, (d : ReciprocityTheory.Aut.AL L) * Hi i j ∈ ReciprocityTheory.Aut.ALint L := fun i j =>
    cong_dvd_mem (hD _) (dvd_trans (dvd_mul_left _ _) (hdv i j))
  refine ⟨N * d * d, Nat.mul_pos (Nat.mul_pos hN hd0) hd0, ?_⟩
  intro κ hκ
  choose Y hYm hYe using hκ.2
  set K : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) := (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) with hK
  have hprod : ((h⁻¹ * κ * h : Formalism.AUTREP.GAf L n).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = Hi * K * H := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  have hHiH : Hi * H = 1 := by
    rw [hHi, hH, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have hKY : K - 1 = ((N * d * d : ℕ) : ReciprocityTheory.Aut.AL L) • Matrix.of Y := by
    ext k l
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact hYe k l
  set Z : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) :=
    ((d : ReciprocityTheory.Aut.AL L) • Hi) * Matrix.of Y * ((d : ReciprocityTheory.Aut.AL L) • H) with hZ
  have hZm : ∀ i j, Z i j ∈ ReciprocityTheory.Aut.ALint L := by
    intro i j
    simp only [hZ, Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _
      (Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hHid i k) (hYm k l)) (hHd l j)
  have hmain : Hi * K * H - 1 = (N : ReciprocityTheory.Aut.AL L) • Z := by
    have e1 : Hi * K * H - 1 = Hi * (K - 1) * H := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hHiH]
    rw [e1, hKY, hZ, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hentry : ∀ i j, (Hi * K * H) i j - (1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) i j =
      (N : ReciprocityTheory.Aut.AL L) * Z i j := by
    intro i j
    rw [← Matrix.sub_apply, hmain, Matrix.smul_apply, smul_eq_mul]
  refine ⟨fun i j => ?_, fun i j => ⟨Z i j, hZm i j, by rw [hprod]; exact hentry i j⟩⟩
  show ((h⁻¹ * κ * h : Formalism.AUTREP.GAf L n).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) i j ∈ ReciprocityTheory.Aut.ALint L
  rw [hprod]
  have e : (Hi * K * H) i j = (1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) i j + (N : ReciprocityTheory.Aut.AL L) * Z i j := by
    rw [← hentry i j]; ring
  rw [e, Matrix.one_apply]
  refine Subring.add_mem _ ?_ (Subring.mul_mem _ (natCast_mem _ _) (hZm i j))
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

end Formalism.IndefR.principalLevelFrame
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.PublishedAut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def AtTauExists (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Prop :=
  ∀ τ (g : Matrix (Fin V.rank) (Fin V.rank) ℂ), g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) → ∃ x, IsAtTau θ V τ g x

theorem atTauExists_of {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) (V : HSp D) :
    AtTauExists θ V := by
  intro τ g hg
  obtain ⟨x, hx, -⟩ := Formalism.IndefR.Eqv.atTauExUnique_holds (D := D) θ hθ V τ g hg
  exact ⟨x, hx⟩

end Formalism.IndefR.PublishedAut

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

abbrev RowSideT (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (L : LevCh D T) (cX : CoefA D.sp.X') (pl : Pl0 → Pl D.host.E) (t : T) : Type :=
  Bridge.SideReal D D.sp.X' (Bridge.envOf cX.coef (levEnvOf D.sp.X' L.βX (L.datXt t) pl (A3.A.ok t)))
    (A3.A.MtildeCSD t) (A3.A.leftGroupActionRight t) (A3.A.heckeR t) (fun i => i.2)

abbrev LiftSideT (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (L : LevCh D T) (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (i : Fin D.R.m) (t : T) : Type :=
  Bridge.SideReal D (Vc D i) (Bridge.envOf (cV i).coef (levEnvOf (Vc D i) (L.βV i) (L.datVt i t) pl (A3.A.ok t)))
    (A3.A.MtCSD i t) (A3.A.leftGroupActionLift i t) (A3.A.heckeL i t) (fun i => i.2)


open Classical in
def PrIso {D : D7} (MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (cX : CoefA D.sp.X') (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ) : Prop :=
  ∀ (ι : D.what₂.Tau → Type) [∀ τ, Fintype (ι τ)] (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (MX.sm τ)) (w w' : cX.W),
    inner ℂ w w' = ∑ f : (∀ τ, ι τ),
      starRingEnd ℂ (prX w (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))) * prX w' (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))

end Formalism.IndefR.Seed
end
end

section

noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Conj

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def conjSub (U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) where
  carrier := {f | (fun g => star (f g)) ∈ U}
  zero_mem' := by
    show (fun g => star ((0 : Formalism.AUTREP.GAf L n → ℂ) g)) ∈ U
    have : (fun g => star ((0 : Formalism.AUTREP.GAf L n → ℂ) g)) = 0 := by
      funext g
      simp
    rw [this]
    exact U.zero_mem
  add_mem' := by
    intro f f' hf hf'
    show (fun g => star ((f + f') g)) ∈ U
    have : (fun g => star ((f + f') g)) = (fun g => star (f g)) + (fun g => star (f' g)) := by
      funext g
      simp
    rw [this]
    exact U.add_mem hf hf'
  smul_mem' := by
    intro a f hf
    show (fun g => star ((a • f) g)) ∈ U
    have : (fun g => star ((a • f) g)) = star a • (fun g => star (f g)) := by
      funext g
      simp [mul_comm]
    rw [this]
    exact U.smul_mem _ hf

theorem mem_conjSub {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} {f : Formalism.AUTREP.GAf L n → ℂ} :
    f ∈ conjSub U ↔ (fun g => star (f g)) ∈ U := Iff.rfl

theorem conjSub_conjSub (U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) : conjSub (conjSub U) = U := by
  ext f
  have hf : (fun g => star (star (f g))) = f := by
    funext g
    simp
  show (fun g => star (star (f g))) ∈ U ↔ f ∈ U
  rw [hf]

theorem conjSub_mono {U U' : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (h : U ≤ U') : conjSub U ≤ conjSub U' :=
  fun _ hf => h hf

theorem conjSub_bot : conjSub (⊥ : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) = ⊥ := by
  ext f
  rw [mem_conjSub, Submodule.mem_bot, Submodule.mem_bot]
  constructor
  · intro h
    funext g
    have := congrFun h g
    simpa using this
  · intro h
    subst h
    funext g
    simp

theorem conj_rt (h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) :
    (fun g => star (Formalism.L2.NG.rt L n h f g)) = Formalism.L2.NG.rt L n h (fun g => star (f g)) := rfl

theorem conjSub_stable {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (hU : ∀ h, ∀ f ∈ U, Formalism.L2.NG.rt L n h f ∈ U) :
    ∀ h, ∀ f ∈ conjSub U, Formalism.L2.NG.rt L n h f ∈ conjSub U := by
  intro h f hf
  rw [mem_conjSub] at hf ⊢
  rw [conj_rt]
  exact hU h _ hf

def FinTyp.conjT (π : Formalism.L2.NG.FinTyp L n) : Formalism.L2.NG.FinTyp L n where
  S := conjSub π.S
  stable := conjSub_stable π.stable
  smooth := by
    intro f hf
    obtain ⟨N, hN, hfix⟩ := π.smooth _ hf
    refine ⟨N, hN, fun κ hκ => ?_⟩
    funext g
    have := congrFun (hfix κ hκ) g
    rw [← conj_rt] at this
    simp only at this
    exact star_injective this
  ne := by
    intro h
    apply π.ne
    rw [← conjSub_conjSub π.S, h, conjSub_bot]
  irr := by
    intro S' hle hst
    rcases π.irr (conjSub S') (by rw [← conjSub_conjSub π.S]; exact conjSub_mono hle) (conjSub_stable hst) with h | h
    · left
      rw [← conjSub_conjSub S', h, conjSub_bot]
    · right
      rw [← conjSub_conjSub S', h]

theorem conjT_S (π : Formalism.L2.NG.FinTyp L n) : (FinTyp.conjT π).S = conjSub π.S := rfl

end Conj

section Act

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostI (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

def rtA (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := rTr V k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def actM (P : RowPsi V n) (M : Mult.DSModel V Sp) : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ (Mult.MMap M) where
  toFun h := Mult.postOn M (rtA (P.ψ h))
  map_one' := by
    apply LinearMap.ext
    intro T
    apply MultilinearMap.ext
    intro v
    funext g
    simp [Mult.postOn_apply, rtA, rTr]
  map_mul' a b := by
    apply LinearMap.ext
    intro T
    apply MultilinearMap.ext
    intro v
    funext g
    simp only [map_mul, Module.End.mul_apply, Mult.postOn_apply]
    show T v (g * (P.ψ a * P.ψ b)) = T v (g * P.ψ a * P.ψ b)
    rw [mul_assoc]

theorem actM_apply (P : RowPsi V n) (M : Mult.DSModel V Sp) (h : Formalism.AUTREP.GAf D.host.E n) (T : Mult.MMap M) (v : M.Vec)
    (g : GA D V) : actM P M h T v g = T v (g * P.ψ h) := rfl

def levN (P : RowPsi V n) (N : ℕ) : Set (GA D V) := P.ψ '' {κ | Formalism.L2.NG.Cong D.host.E n N κ}

def Minf (P : RowPsi V n) (M : Mult.DSModel V Sp) : Submodule ℂ (Mult.MMap M) :=
  ⨆ N : ℕ, Mult.Mult θ M (levN P (N + 1)) (fun _ => 1)

def isotIn {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A)
    (π : Formalism.L2.NG.FinTyp D.host.E n) : Submodule ℂ A :=
  ⨆ (Φ : π.S →ₗ[ℂ] A) (_ : IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C), LinearMap.range Φ

def isotL (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (π : Formalism.L2.NG.FinTyp D.host.E n) : Submodule ℂ (Mult.MMap M) :=
  Mult.goodPart θ M J χ e ⊓ isotIn (actM P M) (Minf θ P M) π

def isotE (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (π : Formalism.L2.NG.FinTyp D.host.E n) : Submodule ℂ (Mult.MMap M) :=
  isotL θ P M J χ e (FinTyp.conjT π)

def OccRows (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ)
    (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) : Set (Formalism.L2.NG.FinTyp D.host.E n) :=
  {π | ∃ b, isotE θ P M (J b) (χ b) (e b) π ≠ ⊥}

abbrev FTR (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ)
    (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) : Type :=
  Formalism.L2.Col.FinTypCls (OccRows θ P M J χ e)

def rowRepR {P : RowPsi V n} {M : Mult.DSModel V Sp} {J : Bool → Set (GA D V)} {χ : Bool → GA D V → ℂ}
    {e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} (σ : FTR θ P M J χ e) : Formalism.L2.NG.FinTyp D.host.E n :=
  Formalism.L2.Col.finTypRep _ σ

theorem rowRepR_occ {P : RowPsi V n} {M : Mult.DSModel V Sp} {J : Bool → Set (GA D V)} {χ : Bool → GA D V → ℂ}
    {e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} (σ : FTR θ P M J χ e) : rowRepR θ σ ∈ OccRows θ P M J χ e :=
  Formalism.L2.Col.finTypRep_mem _ σ

theorem rowRepR_inj {P : RowPsi V n} {M : Mult.DSModel V Sp} {J : Bool → Set (GA D V)} {χ : Bool → GA D V → ℂ}
    {e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} (σ σ' : FTR θ P M J χ e)
    (h : (rowRepR θ σ).Iso (rowRepR θ σ')) : σ = σ' :=
  Formalism.L2.Col.finTypRep_inj h

def IsEigOf (P : RowPsi V n) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (π : Formalism.L2.NG.FinTyp D.host.E n) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Prop :=
  (∃ x ∈ π.S, x ≠ 0 ∧ IsTypeVec (P.ψ ⁻¹' J) (fun κ => χ (P.ψ κ)) x) ∧
  (∀ Pr d R, Mult.Hecke₂ V J χ Sb Pr d R → ∀ x ∈ π.S, IsTypeVec (P.ψ ⁻¹' J) (fun κ => χ (P.ψ κ)) x →
    Hecke₃ P R x = c Pr d • x) ∧
  ∀ Pr d, (¬ ∃ R, Mult.Hecke₂ V J χ Sb Pr d R) → c Pr d = 0


open Classical in
def cOfT (P : RowPsi V n) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (π : Formalism.L2.NG.FinTyp D.host.E n) : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ :=
  if h : ∃ c, IsEigOf P J χ Sb π c then h.choose else 0

structure IsIsomFin {Y W : Formalism.BasicNotions.TH.HSp D} (ι : ↥(GfC Y) →* ↥(GfC W)) : Prop where
  bij : Function.Bijective ι
  conj : ∃ (X : Matrix (Fin W.rank) (Fin Y.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (X' : Matrix (Fin Y.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), X * X' = 1 ∧ X' * X = 1 ∧
      ∀ g : GfC Y, finMat D.sp.cm.sig W.gram ((ι g : GfC W) : GA D W) = X * finMat D.sp.cm.sig Y.gram (g : GA D Y) * X'
  lat : ∀ g : GfC Y, ((g : GA D Y) ∈ KsphC Y ∅ ↔ ((ι g : GfC W) : GA D W) ∈ KsphC W ∅)

def FrameMatch {Y W : Formalism.BasicNotions.TH.HSp D} (PY : RowPsi Y n) (PW : RowPsi W n) (ι : ↥(GfC Y) →* ↥(GfC W)) : Prop :=
  ∃ k : Formalism.AUTREP.GAf D.host.E n, ∀ h, PW.ψ (k⁻¹ * h * k) = ((ι ⟨PY.ψ h, PY.into h⟩ : GfC W) : GA D W)

end Act

end Formalism.IndefR.principalLevelFrame
end
end
