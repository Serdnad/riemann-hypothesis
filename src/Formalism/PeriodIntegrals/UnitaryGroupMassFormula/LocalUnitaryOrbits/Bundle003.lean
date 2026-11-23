module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IsCompactSpanRange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUniformizerHermitianIdeal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CrossMSmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfOrthoB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle001
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem omLocU_of' (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (hU : UnifEx v)
    (h1 : OrbAll σ J ψ v Λ a Y) (h2 : FibU' σ J ψ v Λ a Y) (h3 : CountU σ J ψ v Λ a Y)
    (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y := by
  have h2' : FibU σ J ψ v Λ a Y := by
    intro hG hfib ϖ hϖ
    obtain ⟨hW, hH⟩ := hSd hG.1
    exact h2 hG hW hH hfib ϖ hϖ
  exact omLocU_of σ J ψ v Λ a Y hSd hOm hU h1 h2' h3 h4 h5

theorem omLocU_of_fib (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a)
    (h1 : OrbAll σ J ψ v Λ a Y) (hL : LamOC v Λ a) (hH : HermOC σ v a) (hHe : FibHens σ J ψ v Λ a Y)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of' σ J ψ v Λ a Y hSd hOm (unifEx_holds v) h1 (fibU'_of σ J ψ v Λ a Y hL hH hHe) h3 h4 h5

theorem omLocU_of_hens (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hHe : FibHens σ J ψ v Λ a Y)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_fib σ J ψ v Λ a Y hSd hOm h1 (lamOC_holds v Λ a hFull) (hermOC_holds v σ a) hHe h3 h4 h5

end PI.OmLocU
end
end

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

abbrev latA : AddSubgroup (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v Λ).toAddSubgroup

def lattice₂ (ϖ : Fv F v) : AddSubgroup (Fin n → Fv F v ⊗[F] E) :=
  (latA v Λ).map (DistribSMul.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E := E) v ϖ))

def IdxV (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (lattice₂ v Λ ϖ).relIndex (latA v Λ) = (Ideal.absNorm v.asIdeal) ^ (2 * n)

def redT (a : ℕ) (ϖ : Fv F v) :
    lamA v Λ a →+ (Fin a → latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) where
  toFun X i := QuotientAddGroup.mk ⟨(X : TupV (E := E) v n a) i, X.2 i⟩
  map_zero' := by
    funext i
    rw [Pi.zero_apply, ← QuotientAddGroup.mk_zero]
    rfl
  map_add' X Y := by
    funext i
    rw [Pi.add_apply, ← QuotientAddGroup.mk_add]
    rfl

theorem redT_surj (a : ℕ) (ϖ : Fv F v) : Function.Surjective (redT v Λ a ϖ) := by
  intro c
  refine ⟨⟨fun i => ((c i).out : Fin n → Fv F v ⊗[F] E), fun i => (c i).out.2⟩, ?_⟩
  funext i
  show QuotientAddGroup.mk ⟨((c i).out : Fin n → Fv F v ⊗[F] E), (c i).out.2⟩ = c i
  exact QuotientAddGroup.out_eq' (c i)

theorem redT_ker (a : ℕ) (ϖ : Fv F v) :
    (redT v Λ a ϖ).ker = (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a) := by
  ext X
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro h
    have hi : ∀ i, ∃ z ∈ latLoc (E := E) v Λ, sc (E := E) v ϖ • z = (X : TupV (E := E) v n a) i := by
      intro i
      have h1 := congrFun h i
      change (QuotientAddGroup.mk _ : latA v Λ ⧸ _) = 0 at h1
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h1
      obtain ⟨z, hz, hze⟩ := h1
      exact ⟨z, hz, hze⟩
    choose Z hZ hZe using hi
    exact ⟨Z, hZ, funext hZe⟩
  · rintro ⟨Z, hZ, hZe⟩
    funext i
    change (QuotientAddGroup.mk _ : latA v Λ ⧸ _) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact ⟨Z i, hZ i, congrFun hZe i⟩

theorem idxU_of (a : ℕ) (Y : TupV (E := E) v n a) (h : IdxV σ J ψ v Λ a Y) : IdxU σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have hV := h hG ϖ hϖ
  rw [AddSubgroup.relIndex, ← redT_ker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 (redT_surj v Λ a ϖ), AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a),
    Fintype.card_fin]
  have hq : Nat.card (latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) =
      (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
    rw [← hV, AddSubgroup.relIndex, AddSubgroup.index]
  rw [hq, ← pow_mul]

end PI.OmLocU
end
end

section

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

abbrev OR : Subring (Fv F v ⊗[F] E) := Orb.oRing (E := E) v (Orb.oSub (E := E) v)

def IsRes (ϖ : Fv F v) {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K) : Prop :=
  Function.Surjective π ∧ (∀ x : OR (E := E) v, π x = 0 ↔ (x : Fv F v ⊗[F] E) ∈ PO (E := E) v ϖ) ∧
    ∀ x y : OR (E := E) v, (y : Fv F v ⊗[F] E) = sigR (Fv F v) σ x → π y = τ (π x)

theorem hR_add_right (x y z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y + z) = hR (Fv F v) σ J x y + hR (Fv F v) σ J x z := by
  simp only [hR, hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem coord_eq (e : Fin n → Fin n → Fv F v ⊗[F] E) (he1 : gramR (Fv F v) σ J e = 1)
    (c : Fin n → Fv F v ⊗[F] E) (j : Fin n) : hR (Fv F v) σ J (e j) (∑ i, c i • e i) = c j := by
  rw [Orb.hR_sum_right σ J v]
  have h : ∀ i, hR (Fv F v) σ J (e j) (e i) = (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) j i := by
    intro i; rw [← he1]; rfl
  simp only [h, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem bas_mem {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (j : Fin n) :
    e j ∈ latLoc (E := E) v Λ := by
  refine (he _).2 ⟨Pi.single j 1, fun i => ?_, ?_⟩
  · by_cases h : i = j
    · subst h; simpa using (Orb.oSub (E := E) v).1
    · simpa [Pi.single_apply, h] using Orb.oev_zero (E := E) v
  · simp [Pi.single_apply, ite_smul]

theorem expand {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1)
    {x : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc (E := E) v Λ) :
    x = ∑ j, hR (Fv F v) σ J (e j) x • e j := by
  obtain ⟨c, -, rfl⟩ := (he x).1 hx
  simp only [coord_eq σ J v e he1]

theorem ffGram_one {K : Type} [CommRing K] (τ : K →+* K) {a : ℕ} (X : Fin a → Fin n → K) (i j : Fin a) :
    ffGram τ (1 : Matrix (Fin n) (Fin n) K) X i j = ∑ p, τ (X i p) * X j p := by
  simp only [ffGram, ffH, Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem gY_mem {a : ℕ} {Y : TupV (E := E) v n a} (hG : GoodY σ J ψ v Λ a Y) (i j : Fin a) :
    gramR (Fv F v) σ J Y i j ∈ OR (E := E) v :=
  (hG.2.2.1 (Y j)).1 (hG.2.2.2.2.2.1.1 j) (Y i) (hG.2.2.2.2.2.1.1 i)

end PI.OmLocU.Red
end
end

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem oEv_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v :=
  (PI.OmLocU.Orb.oSub (E := E) v).2 x hx y hy

theorem oEv_sum {ι : Type} (s : Finset ι) (f : ι → Fv F v ⊗[F] E) (h : ∀ i ∈ s, f i ∈ OEv (E := E) v) :
    ∑ i ∈ s, f i ∈ OEv (E := E) v := by
  unfold OEv at *
  exact Submodule.sum_mem _ h

theorem hR_sum_smul_right {a : ℕ} (x : Fin n → Fv F v ⊗[F] E) (c : Fin a → Fv F v ⊗[F] E)
    (y : Fin a → Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (∑ k, c k • y k) = ∑ k, c k * hR (Fv F v) σ J x (y k) := by
  have := map_sum (PI.VolStabSW.hLin (Fv F v) σ J x) (fun k => c k • y k) Finset.univ
  simp only [map_smul, smul_eq_mul] at this
  exact this

theorem hR_smul_left' (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = sigR (Fv F v) σ c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_sum_smul_left {a : ℕ} (y : Fin n → Fv F v ⊗[F] E) (c : Fin a → Fv F v ⊗[F] E)
    (x : Fin a → Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (∑ k, c k • x k) y = ∑ k, sigR (Fv F v) σ (c k) * hR (Fv F v) σ J (x k) y := by
  have := map_sum (AddMonoidHom.mk' (fun z => hR (Fv F v) σ J z y) (fun z z' => hR_add_left σ J z z' y))
    (fun k => c k • x k) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at this
  rw [this]
  exact Finset.sum_congr rfl fun k _ => hR_smul_left' σ J v (c k) (x k) y

section Onto

variable (Λ : Set (Fin n → E)) (ψ : AddChar (AF F) ℂ)

def GramInvO (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ → ∀ y ∈ LamT v Λ a,
    (∀ i j, gramR (Fv F v) σ J y i j - gramR (Fv F v) σ J Y i j ∈ PO (E := E) v ϖ) →
    ∃ Ginv : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E), (∀ i j, Ginv i j ∈ OEv (E := E) v) ∧
      gramR (Fv F v) σ J y * Ginv = 1

def TrOnto : Prop :=
  UnramAt (E := E) v → ∀ s ∈ OEv (E := E) v, sigR (Fv F v) σ s = s →
    ∃ x ∈ OEv (E := E) v, x + sigR (Fv F v) σ x = s

theorem hensOnto_of (a : ℕ) (Y : TupV (E := E) v n a) (hGI : GramInvO σ J v Λ ψ a Y) (hTr : TrOnto σ v) :
    HensOnto σ J v Λ ψ a Y := by
  classical
  intro hGood ϖ hϖ y hy hyT S hS
  obtain ⟨Ginv, hGi, hGG⟩ := hGI hGood ϖ hϖ y hy hyT
  obtain ⟨L, -, hLΛ⟩ := hGood.2.1
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabSW.sigma_invol σ hGood.1.1.2.2.2
  have hJ : ∀ i j, σ (J j i) = J i j := hGood.1.2.1.1
  have hdiag : ∀ i, ∃ x ∈ OEv (E := E) v, x + sigR (Fv F v) σ x = (S : Matrix (Fin a) (Fin a) _) i i :=
    fun i => hTr hGood.2.2.2.1 _ (hS i i) (S.2 i i)
  choose x hx hxs using hdiag
  set A : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := fun i j =>
    if i < j then (S : Matrix (Fin a) (Fin a) _) i j else if i = j then x i else 0 with hAdef
  have hA : ∀ i j, A i j ∈ OEv (E := E) v := by
    intro i j
    simp only [hAdef]
    split_ifs
    · exact hS i j
    · exact hx i
    · exact oEv_zero v
  have hAS : ∀ i j, A i j + sigR (Fv F v) σ (A j i) = (S : Matrix (Fin a) (Fin a) _) i j := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [hAdef, h, not_lt.2 h.le, h.ne']
    · simp [hAdef, hxs]
    · simp only [hAdef, h, not_lt.2 h.le, h.ne, h.ne', if_false, if_true, zero_add]
      exact S.2 i j
  set C := Ginv * A with hCdef
  have hC : ∀ i j, C i j ∈ OEv (E := E) v := fun i j => by
    rw [hCdef, Matrix.mul_apply]
    exact oEv_sum v _ _ fun k _ => oEv_mul v (hGi i k) (hA k j)
  have hGm := PI.VolStabSW.gramR_mem (Fv F v) σ hσ J hJ y
  subst hLΛ
  refine ⟨fun j => ∑ k, C k j • y k, fun j => ?_, ?_⟩
  · exact Submodule.sum_mem _ fun k _ => oEv_smul_mem v L (hC k j) (hy k)
  · funext i j
    simp only [crossM]
    rw [hR_sum_smul_right, hR_sum_smul_left]
    have e1 : ∑ k, C k j * hR (Fv F v) σ J (y i) (y k) = A i j := by
      have : (gramR (Fv F v) σ J y * C) i j = A i j := by
        rw [hCdef, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
      rw [← this, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have e2 : ∑ k, sigR (Fv F v) σ (C k i) * hR (Fv F v) σ J (y k) (y j) = sigR (Fv F v) σ (A j i) := by
      have : (gramR (Fv F v) σ J y * C) j i = A j i := by
        rw [hCdef, ← Matrix.mul_assoc, hGG, Matrix.one_mul]

      rw [← this, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, mul_comm]
      congr 1
      exact (hGm k j).symm
    rw [e1, e2, hAS]

end Onto

end PI.OmLocU
end
end

section

noncomputable section

namespace PI.OmLocU.Orb

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def PerpG {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E) : Set (Fin n → Fv F v ⊗[F] E) :=
  {w | w ∈ latLoc (E := E) v Λ ∧ ∀ i, hR (Fv F v) σ J (X i) w = 0}

def gramG {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E) : Matrix ι ι (Fv F v ⊗[F] E) :=
  fun a b => hR (Fv F v) σ J (X a) (X b)

def UniG {ι : Type} [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E) : Prop :=
  ∃ w ∈ OEv (E := E) v, (gramG σ J v X).det * w = 1

def UnitV : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E), (∀ i, X i ∈ latLoc (E := E) v Λ) →
      UniG σ J v X → Fintype.card ι < n →
      ∃ p ∈ PerpG σ J v Λ X, hR (Fv F v) σ J p p = 1 ∧ ∀ i, hR (Fv F v) σ J p (X i) = 0

theorem hR_smul_right (x y : Fin n → Fv F v ⊗[F] E) (c : Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem perp_full {ι : Type} [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E)
    (hU : UniG σ J v X) (hc : Fintype.card ι = n) (w : Fin n → Fv F v ⊗[F] E)
    (hw : ∀ i, hR (Fv F v) σ J (X i) w = 0) : w = 0 := by
  obtain ⟨u, -, hu⟩ := hU
  have hG : IsUnit (gramG σ J v X).det := ⟨⟨_, u, hu, by rw [mul_comm]; exact hu⟩, rfl⟩
  let eq : ι ≃ Fin n := Fintype.equivFinOfCardEq hc
  let M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := Matrix.of fun i m => X (eq.symm m) i
  have hA : cT (sigR (Fv F v) σ) M * JR (Fv F v) J * M = (gramG σ J v X).submatrix eq.symm eq.symm := by
    ext p q
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    simp only [M, Matrix.of_apply, gramG, hR, hform, Matrix.submatrix_apply]
    exact Finset.sum_comm
  have hdA : IsUnit (cT (sigR (Fv F v) σ) M * JR (Fv F v) J).det := by
    have h1 := congrArg det hA
    rw [det_submatrix_equiv_self, det_mul] at h1
    rw [← h1] at hG
    exact isUnit_of_mul_isUnit_left hG
  have hB : (cT (sigR (Fv F v) σ) M * JR (Fv F v) J) *ᵥ w = 0 := by
    funext m
    have h2 := hw (eq.symm m)
    simp only [hR, hform] at h2
    simp only [Matrix.mulVec, dotProduct, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Pi.zero_apply, Finset.sum_mul]
    simp only [M, Matrix.of_apply]
    rw [Finset.sum_comm]
    exact h2
  have h3 := congrArg (fun y => (cT (sigR (Fv F v) σ) M * JR (Fv F v) J)⁻¹ *ᵥ y) hB
  simpa [mulVec_mulVec, nonsing_inv_mul _ hdA] using h3

theorem orthoGen (hU : UnitV σ J ψ v Λ) (hstd : StdHyp σ J ψ)
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hsd : IsSDLoc σ J v Λ) (hun : UnramAt (E := E) v) :
    ∀ (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E),
      Fintype.card ι + k = n → (∀ i, X i ∈ latLoc (E := E) v Λ) → UniG σ J v X →
      ∃ e : Fin k → Fin n → Fv F v ⊗[F] E, (∀ j, e j ∈ PerpG σ J v Λ X) ∧
        (∀ i j, hR (Fv F v) σ J (e j) (X i) = 0) ∧ gramR (Fv F v) σ J e = 1 ∧
        ∀ w ∈ PerpG σ J v Λ X, ∃ d : Fin k → Fv F v ⊗[F] E, (∀ j, d j ∈ OEv (E := E) v) ∧
          w = ∑ j, d j • e j := by
  intro k
  induction k with
  | zero =>
    intro ι _ _ X hc hX hUX
    refine ⟨Fin.elim0, fun j => j.elim0, fun i j => j.elim0, ?_, ?_⟩
    · ext i
      exact i.elim0
    · intro w hw
      refine ⟨Fin.elim0, fun j => j.elim0, ?_⟩
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      exact perp_full σ J v X hUX (by omega) w hw.2
  | succ k ih =>
    intro ι _ _ X hc hX hUX
    obtain ⟨p, hp, hpp, hpX⟩ := hU hstd hL hsd hun ι X hX hUX (by omega)
    let X' : ι ⊕ Unit → Fin n → Fv F v ⊗[F] E := Sum.elim X (fun _ => p)
    have hG' : gramG σ J v X' = Matrix.fromBlocks (gramG σ J v X) 0 0 1 := by
      ext s t
      rcases s with i | ⟨⟩ <;> rcases t with j | ⟨⟩
      · rfl
      · simp [gramG, X', hp.2 i]
      · simp [gramG, X', hpX j]
      · simp [gramG, X', hpp]
    have hU' : UniG σ J v X' := by
      obtain ⟨u, hu0, hu⟩ := hUX
      refine ⟨u, hu0, ?_⟩
      rw [hG', det_fromBlocks_zero₂₁, det_one, mul_one, hu]
    have hX' : ∀ s, X' s ∈ latLoc (E := E) v Λ := by
      rintro (i | ⟨⟩)
      · exact hX i
      · exact hp.1
    obtain ⟨e', he'P, he'X, he'e, he'span⟩ :=
      ih (ι ⊕ Unit) X' (by rw [Fintype.card_sum, Fintype.card_unit]; omega) hX' hU'
    refine ⟨Fin.cons p e', ?_, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases hp (fun j => ⟨(he'P j).1, fun i => (he'P j).2 (Sum.inl i)⟩) j
    · intro i j
      refine Fin.cases (hpX i) (fun j => he'X (Sum.inl i) j) j
    · ext i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simpa [gramR] using hpp
      · have h1 : hR (Fv F v) σ J p (e' j) = 0 := (he'P j).2 (Sum.inr ())
        simpa [gramR, Matrix.one_apply, (Fin.succ_ne_zero j).symm] using h1
      · have h1 : hR (Fv F v) σ J (e' i) p = 0 := he'X (Sum.inr ()) i
        simpa [gramR, Matrix.one_apply, Fin.succ_ne_zero] using h1
      · simpa [gramR, Matrix.one_apply] using congrFun (congrFun he'e i) j
    · intro w hw
      set c := hR (Fv F v) σ J p w with hcdef
      have hc0 : c ∈ OEv (E := E) v := (hsd w).1 hw.1 p hp.1
      have hw' : w - c • p ∈ PerpG σ J v Λ X' := by
        refine ⟨Submodule.sub_mem _ hw.1 (oSmul v Λ hL c hc0 p hp.1), ?_⟩
        rintro (i | ⟨⟩)
        · show hR (Fv F v) σ J (X i) (w - c • p) = 0
          rw [hR_sub_right, hR_smul_right, hw.2 i, hp.2 i, mul_zero, sub_zero]
        · show hR (Fv F v) σ J p (w - c • p) = 0
          rw [hR_sub_right, hR_smul_right, hpp, mul_one, ← hcdef, sub_self]
      obtain ⟨d', hd'O, hd'⟩ := he'span _ hw'
      refine ⟨Fin.cons c d', fun j => Fin.cases hc0 hd'O j, ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hd']
      abel

theorem orthoB_of (a : ℕ) (Y : TupV (E := E) v n a) (hU : UnitV σ J ψ v Λ) : OrthoB σ J ψ v Λ a Y := by
  intro h hG X hX hXY
  obtain ⟨w, hw0, -, hw⟩ := hG.2.2.2.2.2.2
  rw [← hXY] at hw
  exact orthoGen σ J ψ v Λ hU hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 (n - a) (Fin a) X
    (by rw [Fintype.card_fin]; omega) hX ⟨w, hw0, hw⟩

theorem orbAll_of_unitV (a : ℕ) (Y : TupV (E := E) v n a) (hU : UnitV σ J ψ v Λ) : OrbAll σ J ψ v Λ a Y :=
  orbAll_of_orthoB σ J ψ v Λ a Y (oSub v) (oSmul v Λ) (orthoB_of σ J ψ v Λ a Y hU)

end PI.OmLocU.Orb
end
end
