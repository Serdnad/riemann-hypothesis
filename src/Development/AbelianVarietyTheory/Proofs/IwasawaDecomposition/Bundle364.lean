module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle345
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Formalism.LocalToGlobal.Columns.RecLevelLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle457
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle338
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle162
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

theorem stab_iff_mem_conj : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (U : Subgroup (GL (Fin n) (AfE F E))) (k' y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), (∀ (g x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), IsPtOf hc (g * k') p → IsPtOf hc (g * x * k') p' → (x ∈ U ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p')) → IsPtOf hc (y * k') p → ∀ γ : UF E n, (∃ (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p) ↔ ratAd F γ ∈ U.map (MulAut.conj y).toMonoidHom := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q Λ Θ U k' y p hlev hp γ
  have hγ : IsPtOf hc (ratAd F γ * (y * k')) (((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
    first | exact GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd F E hc n ST SG Q γ (y * k') p hp | exact GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd (hc := hc) γ hp | (apply GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd <;> assumption)
  have hx : IsPtOf hc (y * (y⁻¹ * ratAd F γ * y) * k') (((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
    have : y * (y⁻¹ * ratAd F γ * y) * k' = ratAd F γ * (y * k') := by group
    rw [this]; exact hγ
  have key := hlev y (y⁻¹ * ratAd F γ * y) p _ hp hx
  have hmem : ratAd F γ ∈ U.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * ratAd F γ * y ∈ U := by
    constructor
    · rintro ⟨u, hu, he⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
      rw [← he]; simpa [mul_assoc] using hu
    · intro hu
      refine ⟨_, hu, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  rw [hmem, key]
  constructor
  · rintro ⟨h, θ, he⟩
    refine ⟨h⁻¹, θ⁻¹, ?_⟩
    have e1 : ((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) = ((1, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * (γ, h.1, θ.1) := by
      ext <;> simp
    rw [e1, mul_smul, he]
  · rintro ⟨h, θ, he⟩
    refine ⟨h⁻¹, θ⁻¹, ?_⟩
    have : ((γ, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) = ((1, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * (γ, 1, 1) := by
      ext <;> simp
    rw [this, mul_smul, ← he, ← mul_smul]
    have : ((1, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * (1, h.1, θ.1) = 1 := by
      ext <;> simp
    rw [this, one_smul]

end GlobalTheory.Mem.Col2.TopCh
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwUnit

section Diag

variable {E : Type} [Field E]


open Classical in
def dEnt (n : ℕ) (π : E) (i : Fin n) : E := if i.1 + 1 = n then (if π = 0 then 1 else π) else 1

theorem dEnt_ne (n : ℕ) (π : E) (i : Fin n) : dEnt n π i ≠ 0 := by
  unfold dEnt
  split_ifs with h1 h2 <;> simp_all

def dAut (n : ℕ) (π : E) : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
  LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfNeZero E E (dEnt n π i) (dEnt_ne n π i)

theorem dAut_apply (n : ℕ) (π : E) (x : Fin n → E) (i : Fin n) : dAut n π x i = dEnt n π i * x i := rfl

end Diag

theorem exists_tw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (π : 𝓞 E), (∀ P ∈ Q, π ∉ P.asIdeal) → ∃ t : GL (Fin n) (AfE F E), t ∈ K1 hc n ST SG ∧ (∀ (P : Q) (i j : Fin n), adAt F P.1 (t.1 i j) = algebraMap E _ (if i = j then (if i.1 + 1 = n then (π : E) else 1) else 0)) ∧ ∀ w : HeightOneSpectrum (𝓞 E), w ∉ Q → conjPrime₂ w ∉ Q → ∀ i j : Fin n, adAt F w (t.1 i j) = if i = j then 1 else 0 := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q hQ π hπ
  classical
  have hQc : ∀ P ∈ Q, conjPrime₂ P ∉ Q := fun P hP => (hQ P hP).2.2.2.2
  have hπ0 : ∀ P ∈ Q, (π : E) ≠ 0 := fun P hP h => hπ P hP (by
    have : π = 0 := RingOfIntegers.coe_eq_zero_iff.1 h
    rw [this]; exact P.asIdeal.zero_mem)
  have hval : ∀ P ∈ Q, ∀ i : Fin n, P.valuation E (dEnt n (π : E) i) = 1 := by
    intro P hP i
    unfold dEnt
    rw [if_neg (hπ0 P hP)]
    split_ifs
    · exact le_antisymm (HeightOneSpectrum.valuation_le_one _ π)
        (not_lt.1 fun h => hπ P hP ((HeightOneSpectrum.valuation_lt_one_iff_mem _ _).1 h))
    · exact map_one _
  have hfr : ∀ P ∈ Q, CharValCompare.IsFr P (Formalism.UG.CS.globLat (1 : GL (Fin n) (AfE F E)) (stdLat E n))
      (dAut n (π : E)) := by
    intro P hP x
    rw [globLat_one_std]
    show _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n) ↔ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n)
    rw [mem_localization_standardLattice, mem_localization_standardLattice]
    simp only [dAut_apply, CharValCompare.intAt_iff, map_mul, hval P hP, one_mul]
  obtain ⟨g, hg, c1, c2, c3⟩ := PtExist.exists_modify (hc := hc) hQc (one_mem (UAd hc n)) (fun _ => dAut n (π : E)) hfr

  have hST : ∀ P ∈ ST, P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP =>
    ⟨fun h => (hQ P h).1 hP, fun h => (hQ _ h).2.2.1 (by rw [CharValCompare.conjP_conjP]; exact hP)⟩
  have hSG : ∀ P ∈ SG, P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP =>
    ⟨fun h => (hQ P h).2.1 hP, fun h => (hQ _ h).2.2.2.1 (by rw [CharValCompare.conjP_conjP]; exact hP)⟩
  let p : DecoF E n ST SG ∅ :=
    ⟨(⟨decoRaw ST SG (1 : GL (Fin n) (AfE F E)),
      decorated_lattice_exists hc n ST SG 1 (one_mem _)⟩, fun P => Finset.notMem_empty _ P.2 |>.elim),
      fun P => Finset.notMem_empty _ P.2 |>.elim⟩
  have hb : IsPtOf hc 1 p := by
    apply (PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ 1 p rfl).2
    exact ⟨one_mem _, rfl⟩
  have hpt : IsPtOf hc g p := by
    refine ⟨hg, ?_, fun P x hx i hi => ?_, fun w x hx i => ?_, fun P => absurd P.2 (Finset.notMem_empty _)⟩
    · exact c1
    · rw [c3 P.1 (hST P.1 P.2).1 (hST P.1 P.2).2 x i]
      exact hb.f P x hx i hi
    · rw [c3 w.1 (hSG w.1 w.2).1 (hSG w.1 w.2).2 x i]
      exact hb.be w x hx i
  have hd := (PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ g p rfl).1 hpt
  have hK := mem_principal_of_same_decoration hc n ST SG (one_mem _) hg hd.2
  rw [inv_one, one_mul] at hK
  refine ⟨g, hK, fun P i j => ?_, fun w hw hw' i j => ?_⟩
  · rw [c2 P.1 P.2 i j]
    congr 1
    show dAut n (π : E) (Pi.single j 1) i = _
    rw [dAut_apply]
    unfold dEnt
    rw [if_neg (hπ0 P.1 P.2)]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · have e1 : ∀ i j, adAt F w (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        if i = j then 1 else 0 := by
      intro i j
      have h := c3 w hw hw' (Pi.single j 1) i
      have hv : (fun k => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((Pi.single j (1 : E) : Fin n → E) k)) =
          Pi.single j 1 := by
        ext k
        by_cases hk : k = j
        · subst hk; simp
        · simp [hk]
      have h' : adAt F w ((((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) i) =
          adAt F w ((((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) i) := by
        rw [← hv]; exact h
      rw [inv_one, Units.val_one, Matrix.one_mulVec, Matrix.mulVec_single_one] at h'
      have h'' : adAt F w (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
          adAt F w ((Pi.single j 1 : Fin n → AfE F E) i) := h'
      rw [h'', Pi.single_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hMi : (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))).map (adAt F w) = 1 := by
      ext a b
      rw [Matrix.map_apply, e1, Matrix.one_apply]
    have hgg : (g : Matrix (Fin n) (Fin n) (AfE F E)) * ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hM : (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
      have h := congrArg (fun M => M.map (adAt F w)) hgg
      simp only [Matrix.map_mul, hMi, mul_one] at h
      rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
    have h := congrFun (congrFun hM i) j
    rw [Matrix.map_apply, Matrix.one_apply] at h
    exact h

end GlobalTheory.Mem.Col2.TwUnit
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.PtLat

theorem latS_deco_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (S : Submodule (𝓞 E) (Fin n → E)) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), t ∈ K1 hc n ST SG → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → IsPtOf hc (y * (k * t)) p → ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) p.deco.1.L ↔ (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q S k t y p ht hS hp x
  have hp0 : IsPtOf hc (y * (k * t)) (extTo ∅ p) :=
    hp.extTo (Finset.empty_subset _) (Finset.disjoint_empty_right _)
  obtain ⟨hg, hd⟩ := (PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ _ _ rfl).1 hp0
  have hd' : p.deco.1 = decoRaw ST SG (y * (k * t)) := hd
  have hcar := decoRaw_carries hc n ST SG hg x
  rw [hd']
  refine hcar.trans ?_
  have hst := mirabolicLevel_le_stabilizer_base hc n ST (principal_le_congruence_subgroup hc n ST SG (Subgroup.inv_mem _ ht))
  have e : (((y * (k * t))⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x =
      ((t⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x)) := by
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e]
  exact ((hst _).symm).trans (hS _).symm

end GlobalTheory.Mem.Col2.PtLat
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology MeasureTheory
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

theorem sum_ite_val {m : ℕ} (f : Fin m → ℂ) (c : ℕ) (hc : c < m) :
    ∑ j : Fin m, (if (j : ℕ) = c then f j else 0) = f ⟨c, hc⟩ := by
  rw [Finset.sum_eq_single ⟨c, hc⟩]
  · simp
  · intro j _ hj
    rw [if_neg]
    exact fun h => hj (Fin.ext h)
  · simp

theorem sum_ite_val_zero {m : ℕ} (f : Fin m → ℂ) (c : ℕ) (hc : m ≤ c) :
    ∑ j : Fin m, (if (j : ℕ) = c then f j else 0) = 0 :=
  Finset.sum_eq_zero fun j _ => if_neg (by have := j.2; omega)

theorem isBlock_of_frame {p q N n : ℕ} (hp : p = N) (hq : q = n) (hN : N = n + 1) (M : Matrix (Fin p) (Fin p) ℂ)
    (M' : Matrix (Fin q) (Fin q) ℂ)
    (h1 : M * Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) =
      Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) * M')
    (h2 : M *ᵥ (fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) = fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) :
    GlobalTheory.BranchFormula.IsBlock hN (fun i j : Fin N => M (Fin.cast hp.symm i) (Fin.cast hp.symm j))
      (fun a b : Fin n => M' (Fin.cast hq.symm a) (Fin.cast hq.symm b)) 1 := by
  subst hp hq hN
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have e := congrFun (congrFun h1 (Br.iC rfl a)) b
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul] at e
    simp only [eq_comm (a := ((Br.iC rfl a : Fin (q+1)) : ℕ))] at e
    rw [sum_ite_val _ _ (by have := b.2; omega), sum_ite_val _ _ (show ((Br.iC rfl a : Fin (q+1)) : ℕ) < q from a.2)] at e
    exact e
  · have e := congrFun h2 (Br.iC rfl a)
    simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero] at e
    rw [sum_ite_val _ _ (by omega), if_neg (by have := a.2; simp [Br.iC]; omega)] at e
    exact e
  · have e := congrFun (congrFun h1 (Br.iL rfl)) a
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul] at e
    simp only [eq_comm (a := ((Br.iL rfl : Fin (q+1)) : ℕ))] at e
    rw [sum_ite_val _ _ (by have := a.2; omega), sum_ite_val_zero _ _ (by simp [Br.iL])] at e
    exact e
  · have e := congrFun h2 (Br.iL rfl)
    simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero] at e
    rw [sum_ite_val _ _ (by omega), if_pos (by simp [Br.iL])] at e
    exact e

end GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

namespace GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

theorem isBlock_of_entries {p q N n : ℕ} (hp : p = N) (hq : q = n) (hN : N = n + 1) (M : Matrix (Fin p) (Fin p) ℂ)
    (M' : Matrix (Fin q) (Fin q) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) (A' : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A i j = M (Fin.cast hp.symm i) (Fin.cast hp.symm j))
    (hA' : ∀ i j, A' i j = M' (Fin.cast hq.symm i) (Fin.cast hq.symm j))
    (h1 : M * Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) =
      Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) * M')
    (h2 : M *ᵥ (fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) = fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) :
    GlobalTheory.BranchFormula.IsBlock hN A A' 1 := by
  have e1 : A = fun i j => M (Fin.cast hp.symm i) (Fin.cast hp.symm j) := funext fun i => funext fun j => hA i j
  have e2 : A' = fun i j => M' (Fin.cast hq.symm i) (Fin.cast hq.symm j) := funext fun i => funext fun j => hA' i j
  subst e1 e2
  exact isBlock_of_frame hp hq hN M M' h1 h2

end GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

namespace GlobalTheory.Mem.Col2.TC

end GlobalTheory.Mem.Col2.TC
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselConvDefinite

theorem isAniso_of_isDefinite {D : D7} (A : HSp D) (hs : A.SigOK) (hd : A.IsDefinite) : IsAniso A := by
  rw [GlobalTheory.BesselCompare.isAniso_iff]
  intro v hv
  by_contra hne
  have hc := D.sp.cm.cmUnram
  have := hc.1
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  rcases hd τ with h | h
  · have := (GlobalTheory.BaseChangeExistsCompare.sig_pos_iff A hs τ (hc.2.1 τ)).1 h v hne
    simp [hv] at this
  · have := (GlobalTheory.BaseChangeExistsCompare.sig_neg_iff A hs τ (hc.2.1 τ)).1 h v hne
    simp [hv] at this


open Pointwise in
theorem measure_fundamentalDomain_lt_top {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ g : G, ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k) (μ : Measure G) [μ.IsHaarMeasure] {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) : μ F < ⊤ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have hsub : F ⊆ ⋃ γ : Γ, ((γ • K) ∩ F) := by
    intro g hg
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov g
    exact Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ), ⟨k, hk, e.symm⟩, hg⟩
  calc μ F ≤ μ (⋃ γ : Γ, ((γ • K) ∩ F)) := measure_mono hsub
    _ ≤ ∑' γ : Γ, μ ((γ • K) ∩ F) := measure_iUnion_le _
    _ = μ K := (hF.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

section Conj

open GlobalTheory.BesselCompare

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem iA_eq_sum (t : Fin A.rank → AE D) : iA ι t = ∑ l, t l • vecA B (ι (A.frame l)) := by
  rw [iA, frameMat_eq, eMat_mulVec]

theorem vecA_add (x y : B.V) : vecA B (x + y) = vecA B x + vecA B y := by
  funext k; simp [vecA]

theorem vecA_iota (a : A.V) : vecA B (ι a) = iA ι (vecA A a) := by
  rw [iA_eq_sum]
  funext k
  have h : B.frame.repr (ι a) k = ∑ c, A.frame.repr a c * B.frame.repr (ι (A.frame c)) k := by
    conv_lhs => rw [← A.frame.sum_repr a]

    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

  simp only [vecA, h, map_sum, map_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem embRel_fix {g : GA D B} {h : GA D A} (e : EmbRel B A ι g h) {w : B.V} (hw : ∀ x, B.hD w (ι x) = 0) :
    (mt B g).mulVec (vecA B w) = vecA B w :=
  e.2 (co B w) (by funext i; rw [frameMat_eq, cT_mulVec]; exact hw _)

theorem embRel_iA {g : GA D B} {h : GA D A} (e : EmbRel B A ι g h) (t : Fin A.rank → AE D) :
    (mt B g).mulVec (iA ι t) = iA ι ((mt A h).mulVec t) := by
  rw [iA, iA, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun M => Matrix.mulVec M t) e.1

theorem conj_mem_NSet (d : BesselDatum A B ι) {g : GA D B} {h : GA D A} (e : EmbRel B A ι g h) {n : GA D B}
    (hn : n ∈ d.NSet) : g * n * g⁻¹ ∈ d.NSet := by
  have hinv : ∀ {x y}, (mt B g).mulVec x = y → (mt B g⁻¹).mulVec y = x := fun hxy => by
    rw [← hxy, mulVec_inv_cancel]
  have he : ∀ l, (mt B g).mulVec (vecA B (d.e l)) = vecA B (d.e l) := fun l => embRel_fix e (d.eA l)
  have hsum : ∀ c : Fin d.ρ → AE D, (mt B g).mulVec (∑ l, c l • vecA B (d.e l)) = ∑ l, c l • vecA B (d.e l) :=
    fun c => by simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, he]
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨c, hc, h1⟩ := hn.1 i
    refine ⟨c, hc, ?_⟩
    unfold actV at h1 ⊢
    rw [mulVec_mul, mulVec_mul, hinv (he i), h1, Matrix.mulVec_add, he, hsum]
  · obtain ⟨a, ha⟩ := exists_rep A (B.hT x ∘ₗ ι)
    have hw : ∀ y, B.hD (x - ι a) (ι y) = 0 := fun y => hD_swap_zero (by
      unfold HSpace.hD
      rw [map_sub, LinearMap.sub_apply, d.isom, ha]; exact sub_self _)
    have hιe : ∀ y i, B.hD (ι y) (d.e i) = 0 := fun y i => hD_swap_zero (d.eA i y)
    have hwe : ∀ i, B.hD (x - ι a) (d.e i) = 0 := fun i => by
      have h1 := hx i
      have h2 := hιe a i
      unfold HSpace.hD at h1 h2 ⊢
      rw [map_sub, h1, h2, sub_zero]
    obtain ⟨c₀, hc₀⟩ := hn.2 _ hwe
    choose c hc using fun k => hn.2 _ (hιe (A.frame k))
    unfold actV at hc₀ hc ⊢
    set t := (mt A h⁻¹).mulVec (vecA A a) with ht
    have hx1 : vecA B x = vecA B (x - ι a) + iA ι (vecA A a) := by rw [← vecA_iota, ← vecA_add, sub_add_cancel]
    have hg : (mt B g).mulVec (vecA B (x - ι a) + iA ι t) = vecA B x := by
      rw [Matrix.mulVec_add, embRel_fix e hw, embRel_iA e, ht, mulVec_cancel_inv, hx1]
    have hn1 : (mt B n).mulVec (vecA B (x - ι a) + iA ι t) =
        (vecA B (x - ι a) + iA ι t) + ∑ l, (c₀ l + ∑ k, t k * c k l) • vecA B (d.e l) := by
      rw [Matrix.mulVec_add, hc₀, iA_eq_sum]
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hc, smul_add, add_smul, Finset.sum_add_distrib,
        Finset.smul_sum, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm (f := fun k l => t k • c k l • vecA B (d.e l))]
      abel
    exact ⟨_, by rw [mulVec_mul, mulVec_mul, hinv hg, hn1, Matrix.mulVec_add, hg, hsum]⟩

theorem conj_mem_N (d : BesselDatum A B ι) {g : GA D B} {h : GA D A} (e : EmbRel B A ι g h) {n : GA D B}
    (hn : n ∈ d.N) : g * n * g⁻¹ ∈ d.N :=
  (Subgroup.closure_le (d.N.comap (MulAut.conj g).toMonoidHom)).2
    (fun _ hm => Subgroup.subset_closure (conj_mem_NSet d e hm)) hn

end Conj

theorem convergesDef : ∀ D : D7, ConvergesDef D := by
  intro D A B ι d ψ hψ hs hd μ 𝓕 hμ ν 𝓝 hν s hs' φ F hφ hF g
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A (isAniso_of_isDefinite A hs hd)
  obtain ⟨s₀, hcont, hrel, hQ⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι d.isom
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs' h)
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have := hμ.1.1
  have hfin : μ 𝓕 < ⊤ := measure_fundamentalDomain_lt_top (GQ A) hK hcov μ hμ.2
  have hFc : Continuous (rTr B g F) := hF.cont.comp (continuous_id.mul continuous_const)
  have hFl : ∀ γ ∈ GQ B, ∀ x, rTr B g F (γ * x) = rTr B g F x := fun γ hγ x => by
    simp only [rTr, mul_assoc]; exact hF.left γ hγ _
  obtain ⟨-, hc, hb⟩ := GlobalTheory.RootExch.CoefInt.coeff_integrable_continuous D A B ι d ψ hψ ν 𝓝 hν (rTr B g F) hFc hFl
  obtain ⟨M, hM⟩ := hb (s₀ '' K) (hK.image hcont)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφ.cont.continuousOn
  have hcontI : Continuous fun h => φ h * d.coeff ψ ν 𝓝 (rTr B g F) (s₀ h) := hφ.cont.mul (hc.comp hcont)
  refine Measure.integrableOn_of_bounded (M := C * M) hfin.ne hcontI.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => ?_)
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov h
  rw [norm_mul, hφ.left γ hγ]
  refine mul_le_mul (hC k hk) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hC k hk))
  have h1 : ν 𝓝 < ⊤ := by rw [hν.2.2]; exact ENNReal.one_lt_top
  have h2 := norm_setIntegral_le_of_norm_le_const (μ := ν) (s := 𝓝) (C := M)
    (f := fun n : d.N => rTr B g F ((n : GA D B) * s₀ (γ * k)) * star (d.psiN ψ (n : GA D B))) h1 (fun n _ => by
      have hn : s₀ γ⁻¹ * n * (s₀ γ⁻¹)⁻¹ ∈ d.N := conj_mem_N d ((hrel _ _).2 rfl) n.2
      have e : (n : GA D B) * s₀ (γ * k) = s₀ γ * (s₀ γ⁻¹ * n * (s₀ γ⁻¹)⁻¹ * s₀ k) := by
        simp only [map_mul, map_inv, inv_inv, mul_assoc, mul_inv_cancel_left]
      rw [norm_mul, norm_star, e, hFl _ (hQ γ hγ), BesselDatum.psiN, hψ.2.1, mul_one]
      exact hM _ hn _ ⟨k, hk, rfl⟩)
  rwa [Measure.real, hν.2.2, ENNReal.toReal_one, mul_one] at h2

end GlobalTheory.BesselConvDefinite
end
