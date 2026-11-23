module

public import Formalism.AlgebraicWeights.InertDatumExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle110
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle545
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle642
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle632
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle646
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG

namespace GlobalTheory.InertHeckeAdd

open Classical in
theorem heckeFunI_add_smul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h₁ h₂ : Formalism.UG.GU Dv.σw n → ℂ), h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ (c : ℂ) (f : GAf L n → W), heckeFunI L n U Dv (h₁ + h₂) f = heckeFunI L n U Dv h₁ f + heckeFunI L n U Dv h₂ f ∧ heckeFunI L n U Dv (c • h₁) f = c • heckeFunI L n U Dv h₁ f := by
  intro L _ _ _ n v w Dv U hU W _ _ h h' hh hh' c f
  have hfin : ∀ k ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
      (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval k (Dv.loc x) ≠ 0} := fun k hk =>
    GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram)
      (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) U hU k hk
  have hsupp : ∀ k ∈ Hecke ℂ (KU Dv.σw n), ∀ (φ : GAf L n → W) (g : GAf L n),
      (Function.support (fun c : GAf L n ⧸ U =>
        if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
          Dv.hval k (Dv.loc hc.choose) • φ (g * hc.choose) else 0)).Finite := by
    intro k hk φ g
    refine (hfin k hk).subset ?_
    intro c hc
    simp only [Function.mem_support] at hc
    split_ifs at hc with h1
    · refine ⟨h1.choose, h1.choose_spec.1, h1.choose_spec.2, ?_⟩
      intro h0
      rw [h0, zero_smul] at hc
      exact hc rfl
    · exact absurd rfl hc
  have hadd : ∀ y, Dv.hval (h + h') y = Dv.hval h y + Dv.hval h' y := by
    intro y; unfold InertDatum.hval; split_ifs <;> simp
  have hsmul : ∀ y, Dv.hval (c • h) y = c * Dv.hval h y := by
    intro y; unfold InertDatum.hval; split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · funext g
    simp only [heckeFunI, Pi.add_apply]
    rw [← finsum_add_distrib (hsupp h hh f g) (hsupp h' hh' f g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [hadd, add_smul]
  · funext g
    simp only [heckeFunI, Pi.smul_apply]
    rw [_root_.smul_finsum' c (hsupp h hh f g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [hsmul, mul_smul]

end GlobalTheory.InertHeckeAdd
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertSurj

theorem exists_supported (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (m : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ∃ z : AL L, compAt L v z = m ∧ ∀ u, u ≠ v → compAt L u z = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨a, c, h⟩ := GlobalTheory.InertUmax.tensor_decomp b m
  refine ⟨b 0 ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v a +
    b 1 ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v c, ?_, ?_⟩
  · rw [map_add (f := _), GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same,
      GlobalTheory.InertUmax.sgl_same, h]
  · intro u hu
    rw [map_add (f := _), GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v a hu,
      GlobalTheory.InertUmax.sgl_ne L v c hu, tmul_zero, tmul_zero, add_zero]

theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L) :
    compAt L u (conjAL L z) = Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (u.adicCompletion (maximalRealSubfield L)) (compAt L u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [GlobalTheory.InertUmax.compAt_tmul]
    simp [conjAL, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul, GlobalTheory.InertUmax.compAt_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem loc_surj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (y : GL (Fin n) (w.adicCompletion L)), y ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  intro L _ _ _ n v w Dv y hy
  classical
  let sig := Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L))
  let eS : w.adicCompletion L →+* L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) :=
    Dv.e.symm.toRingHom
  have hcomm : ∀ a, sig (eS a) = eS (Dv.σw a) := by
    intro a
    apply Dv.e.injective
    have h := Dv.comm (eS a)
    simp only [eS, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at h ⊢
    exact h
  let Pm : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P : Matrix (Fin n) (Fin n) _)
  let Qm : Matrix (Fin n) (Fin n) (w.adicCompletion L) := ((Dv.P⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)
  let Ym : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (y : Matrix (Fin n) (Fin n) _)
  have hPQ : Pm * Qm = 1 := by simp [Pm, Qm]
  have hy' : Formalism.UG.cT Dv.σw Ym * Formalism.UG.antiJ (w.adicCompletion L) n * Ym =
      Formalism.UG.antiJ (w.adicCompletion L) n := hy
  let X := Pm * Ym * Qm
  have hX : Formalism.UG.cT Dv.σw X * X = 1 := by
    have hP := Dv.Panti
    change Formalism.UG.cT Dv.σw Pm * Pm = _ at hP
    calc Formalism.UG.cT Dv.σw X * X
        = Formalism.UG.cT Dv.σw Qm * (Formalism.UG.cT Dv.σw Ym * (Formalism.UG.cT Dv.σw Pm * Pm) * Ym) * Qm := by
          simp only [X, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT Dv.σw Qm * (Formalism.UG.cT Dv.σw Pm * Pm) * Qm := by rw [hP, hy']
      _ = Formalism.UG.cT Dv.σw (Pm * Qm) * (Pm * Qm) := by
          simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul]
  have hX' : X * Formalism.UG.cT Dv.σw X = 1 := mul_eq_one_comm.mp hX
  let M := X.map eS
  have hMc : conjT sig M = (Formalism.UG.cT Dv.σw X).map eS := by
    ext i j
    simp [M, conjT, Formalism.UG.cT, hcomm]
  have hM : M * conjT sig M = 1 := by
    rw [hMc]
    change X.map eS * (Formalism.UG.cT Dv.σw X).map eS = 1
    rw [← Matrix.map_mul, hX', Matrix.map_one _ (map_zero _) (map_one _)]
  choose lift hlv hlw using GlobalTheory.InertSurj.exists_supported L v
  let E : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v 1
  have hEv : compAt L v E = 1 := by
    rw [GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]; rfl
  have hEw : ∀ u, u ≠ v → compAt L u E = 0 := by
    intro u hu
    rw [GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v 1 hu, tmul_zero]
  let Z : Matrix (Fin n) (Fin n) (AL L) := M.map lift + (1 - E) • (1 : Matrix (Fin n) (Fin n) (AL L))
  have hZv : Z.map (compAt L v) = M := by
    ext i j
    simp only [Z, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
      map_sub, map_one, hEv, hlv, sub_self, zero_mul, add_zero]
  have hZw : ∀ u, u ≠ v → Z.map (compAt L u) = 1 := by
    intro u hu
    ext i j
    simp only [Z, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
      map_sub, map_one, hEw u hu, hlw _ u hu, sub_zero, one_mul, zero_add]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hZconj : ∀ u, (conjT (conjAL L) Z).map (compAt L u) =
      conjT (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (u.adicCompletion (maximalRealSubfield L)))
        (Z.map (compAt L u)) := by
    intro u
    ext i j
    simp [conjT, GlobalTheory.InertSurj.compAt_conjAL]
  have hZZ : Z * conjT (conjAL L) Z = 1 := by
    ext i j
    rw [← sub_eq_zero]
    apply GlobalTheory.InertUmax.eq_zero_of_compAt
    intro u
    have key : (Z * conjT (conjAL L) Z).map (compAt L u) = 1 := by
      rw [Matrix.map_mul, hZconj]
      rcases eq_or_ne u v with rfl | hu
      · rw [hZv]; exact hM
      · rw [hZw u hu, conjT_one, Matrix.one_mul]
    have h1 := congrFun (congrFun key i) j
    have h2 := congrFun (congrFun (Matrix.map_one (compAt L u) (map_zero _) (map_one _)) i) j
    simp only [Matrix.map_apply] at h1 h2
    rw [map_sub, h1, h2, sub_self]
  have hZZ' : conjT (conjAL L) Z * Z = 1 := mul_eq_one_comm.mp hZZ
  let g : GL (Fin n) (AL L) := ⟨Z, conjT (conjAL L) Z, hZZ, hZZ'⟩
  have hg : g ∈ ReciprocityTheory.Aut.GA L n := hZZ
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · intro u hu
    exact hZw u (by simpa using hu)
  · have hb : Formalism.UG.bc (n := Fin n)
        (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
        (Matrix.GeneralLinearGroup.map (compAt L v) (((⟨g, hg⟩ : GAf L n)) : GL (Fin n) (AL L))) =
        Dv.P * y * Dv.P⁻¹ := by
      apply Units.ext
      change (Z.map (compAt L v)).map _ = X
      rw [hZv]
      ext i j
      simp [M, eS]
    unfold InertDatum.loc
    rw [hb]
    group

end GlobalTheory.InertSurj
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertKU

theorem compAt_mem_tensInt (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {z : AL L} (hz : z ∈ ALint L) :
    compAt L v z ∈ Formalism.UG.tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L)
      (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  have key : ALint L ≤ (Formalism.UG.tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L)
      (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · apply Subring.subset_closure
      left
      refine ⟨⟨(y : L), y, rfl⟩, ?_⟩
      rw [GlobalTheory.InertUmax.compAt_tmul]
      rfl
    · apply Subring.subset_closure
      right
      refine ⟨⟨a v, ha v⟩, ?_⟩
      rw [GlobalTheory.InertUmax.compAt_tmul]
  exact key hz

theorem mem_range_bc_of_entries {K : Type} [Field K] (S : Subring K) {n : ℕ} (g : GL (Fin n) K)
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ S)
    (hg' : ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ S) :
    g ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range := by
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, hg i j⟩
  let M' : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, hg' i j⟩
  have hM : (RingHom.mapMatrix S.subtype) M = (g : Matrix (Fin n) (Fin n) K) := rfl
  have hM' : (RingHom.mapMatrix S.subtype) M' = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) S.subtype) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have h1 : M * M' = 1 := inj (by rw [map_mul, map_one, hM, hM']; exact Units.mul_inv g)
  have h2 : M' * M = 1 := inj (by rw [map_mul, map_one, hM, hM']; exact Units.inv_mul g)
  refine ⟨⟨M, M', h1, h2⟩, ?_⟩
  ext i j
  rfl

theorem loc_inv (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x⁻¹ = (Dv.loc x)⁻¹ := by
  unfold InertDatum.loc
  simp only [InvMemClass.coe_inv, map_inv]
  group

theorem loc_entries_mem (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (y : GAf L n) (hy : y ∈ Umax L n) (i j : Fin n) :
    ((Dv.loc y : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j
      ∈ Formalism.UG.intL (w.adicCompletion L) := by
  have hP := GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint
  have hP' := GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hE : ∀ l k, ((Formalism.UG.bc (n := Fin n)
      (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (compAt L v) (y : GL (Fin n) (AL L))) : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) (w.adicCompletion L)) l k ∈ Formalism.UG.intL (w.adicCompletion L) :=
    fun l k => (Dv.integ _).1 (compAt_mem_tensInt L v (hy l k))
  unfold InertDatum.loc
  simp only [Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
    (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (hE l k)) (hP k j)

theorem loc_mem_KU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (x : GAf L n), x ∈ Umax L n → ∀ hg : Dv.loc x ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc x, hg⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
  intro L _ _ _ n v w Dv x hx hg
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf]
  refine ⟨hg, ?_⟩
  apply mem_range_bc_of_entries
  · exact loc_entries_mem L n v w Dv x hx
  · intro i j
    rw [← loc_inv]
    exact loc_entries_mem L n v w Dv x⁻¹ (inv_mem hx) i j

end GlobalTheory.InertKU
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.GamModX

theorem full_of_std {L M : Type} [Field L] [AddCommGroup M] [Module L M] {D : Submodule L M}
    {Λ : Submodule L (ℤ → M)} (h : Std D Λ) : Full D Λ :=
  ⟨0, fun f h1 h2 => (h f).2 ⟨h1, by simpa using h2⟩⟩

theorem shift_mem {L M : Type} [Field L] [AddCommGroup M] [Module L M] {D : Submodule L M}
    {Λ : Submodule L (ℤ → M)} (h : Std D Λ) (e y : ℤ → M) (he : e ∈ Λ) (u : L)
    (hy : ∀ k : ℤ, y k = u ^ k • e k - e k) :
    ∃ f ∈ Λ, ∀ j : ℤ, y j = f (j - ((1 : ℕ) : ℤ)) := by
  obtain ⟨h1, h2⟩ := (h e).1 he
  refine ⟨fun k => y (k + 1), (h _).2 ⟨fun k => ?_, fun k hk => ?_⟩, fun j => by simp⟩
  · rw [hy]; exact D.sub_mem (D.smul_mem _ (h1 _)) (h1 _)
  · rw [hy]
    rcases (show k + 1 < 0 ∨ k + 1 = 0 by omega) with h3 | h3
    · simp [h2 _ h3]
    · simp [h3]

theorem conv_one {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : ℤ → M) :
    conv (1 : PowerSeries L) f = f := by
  funext k
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem exists_smul_of_dvd_repr {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M]
    [Fintype ι] (N : Submodule A M) (nb : Module.Basis ι A ↥N) (a : A) (z : ↥N)
    (hz : ∀ j, a ^ 1 ∣ nb.repr z j) : ∃ y ∈ N, (z : M) = a • y := by
  choose c hc using hz
  refine ⟨((∑ j, c j • nb j : ↥N) : M), Subtype.property _, ?_⟩
  have key : z = a • ∑ j, c j • nb j := by
    conv_lhs => rw [← nb.sum_repr z]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc j, pow_one, mul_smul]
  exact congrArg Subtype.val key



theorem ex_of_val {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {F : LocFon l P AI H} (C : LocCmpT l P AI H F) {K : FinExt l} {s : ℕ} {LL : FinExt l}
    (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) (i : Let K) (ζ : ↥LL.1) (m : ℕ)
    (hζ : ζ ^ (l ^ m) = 1) (g : (H.W K s LL h).Gam)
    (hg : (m : WithTop ℚ) ≤
      P.v LL (algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ g : ↥(OL LL)) - 1))
    (x : ↥((H.W K s LL h).N T)) (k : ℤ) :
    ex C h T i ζ ⟨_, (H.W K s LL h).N_Γ T g x x.2⟩ k =
      (algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ g : ↥(OL LL))) ^ k • ex C h T i ζ x k := by
  obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).1 (orderOf_dvd_of_pow_eq_one hζ)
  have hjs : (j : WithTop ℚ) ≤ (m : WithTop ℚ) := by exact_mod_cast hj
  exact (C.C K s LL h).tie.levB_Γ T hT g i ζ ζ j 1
    (by rw [P.PD_p, ← hord]; exact IsPrimitiveRoot.orderOf ζ)
    (by rw [Nat.cast_one]; exact hjs.trans hg) (pow_one ζ).symm x
    ((H.W K s LL h).N_Γ T g x x.2) k



theorem sub_mem_X_of_val : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (_ : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL), let W := (HW l).W K s LL h;
    ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ g : W.Gam,
      ((s - 1 : ℕ) : WithTop ℚ) ≤
        (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) - 1) →
      ∀ x ∈ W.N T, ∃ y ∈ W.N T, W.γD T g x - x = W.X • y := by
  intro D HW F Cm l _ K s LL h W T hT g hg x hx
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  let x' : ↥(W.N T) := ⟨x, hx⟩
  let g' : ↥(W.N T) := ⟨_, W.N_Γ T g x hx⟩
  refine exists_smul_of_dvd_repr (W.N T) nb W.X (g' - x') fun j => ?_
  refine (GlobalTheory.T.wachWeierstrass_test_and_density D HW l K s LL h).2.1 1 _ fun i ζ hζ => ?_
  have hS := GlobalTheory.T.wachLattice_expansions_std_below_level D HW F Cm l K s LL h T hT i ζ hζ
  have hprim : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
    obtain ⟨j, -, hord⟩ :=
      (Nat.dvd_prime_pow (Fact.out : l.Prime)).1 (orderOf_dvd_of_pow_eq_one hζ)
    exact ⟨j, hord ▸ IsPrimitiveRoot.orderOf ζ⟩
  have hI := (GlobalTheory.T.wachExpansion_basis_divisibility D HW F Cm l K s LL h T hT i ζ hprim (full_of_std hS)).2 _ nb
  refine (hI.2.2 (g' - x') 1).1 ?_ j
  refine shift_mem hS (ex (Cm l) h T i ζ x') _ ?_
    (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL))) fun k => ?_
  · exact Submodule.subset_span ⟨1, x', (conv_one _).symm⟩
  · rw [← ex_of_val (Cm l) h T hT i ζ (s - 1) hζ g hg x' k]
    unfold ex
    rw [map_sub]
    rfl



theorem gam_mod_π_mod_X : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (_ : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL), let W := (HW l).W K s LL h;
    ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ →
      (∀ g : W.Gam, ∀ x ∈ W.N T, W.γD T g x ∈ W.N T) ∧
      (∀ g : W.Gam, ∀ x ∈ W.N T, ∃ y ∈ W.N T, W.γD T g x - x = (letπ : AA K LL) • y) ∧
      ∀ x ∈ W.N T, ∃ y ∈ W.N T, W.γD T W.gam x - x = W.X • y := by
  intro D HW F Cm l _ K s LL h W T hT
  refine ⟨W.N_Γ T, W.N_π T, sub_mem_X_of_val D HW F Cm l K s LL h T hT W.gam ?_⟩
  have hg := W.gam_gen
  rw [(HW l).W_s] at hg
  have hs : ((s - 1 : ℕ) : WithTop ℚ) ≤ (s : WithTop ℚ) := by exact_mod_cast Nat.sub_le s 1
  exact hs.trans hg.ge

end GlobalTheory.NL.GamModX
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachLattice_heights_from_hodgeJumps : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), P5 D HW F := by
  first | exact @GlobalTheory.NL.Heights.heights_from_jumps | exact GlobalTheory.NL.Heights.heights_from_jumps | (intros; apply GlobalTheory.NL.Heights.heights_from_jumps <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

namespace GlobalTheory.InertQlUnr

theorem IK_qlExt_fixes_Kur : ∀ (l : ℕ) [Fact l.Prime] (g : ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l))), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → ∀ x ∈ MaximalUnramifiedExtension l, (g : GQ l) x = x := by
  intro l _ g hg x hx
  exact GlobalTheory.InerQl.IK_fixes_Kur _ hg hx

end GlobalTheory.InertQlUnr
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.integralityFromMetric_of_160_le : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ CA CB CK C : ℝ, 160 ≤ C → ElementDenominator.IntegralityFromMetric D HW F Cm CA CB CK C := by
  first | exact @GlobalTheory.TheoremAFinal.integralityFromMetric_of_le | exact GlobalTheory.TheoremAFinal.integralityFromMetric_of_le | (intros; apply GlobalTheory.TheoremAFinal.integralityFromMetric_of_le <;> assumption)
end
