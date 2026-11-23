module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CoboundaryLemmaNoColumn
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsIsDiagOnOfIsDiagOnInfKerSign
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle012
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtIneL
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtInertiaAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

section




section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia
namespace UpperTheory.V.Aut
structure BPrime_s (K : Type) [Field K] [NumberField K] [IsCMField K] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : G ℚ Ω → Matrix (Fin 3) (Fin 3) (Qbar l)) : Prop where
  opens : ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ (eta4 Ω).ker → MatIrr U a
  cyc : MatIrr ((eta4 Ω).ker ⊓ (cycZ ℚ Ω l).ker) a
  aut : _root_.UpperTheory.V.Af.AutOnAlt K ι (-1) a
def ThmS6_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∃ g₁ : Gam Ω S, F.Marked g₁ ∧
    ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (u : Gam Ω S →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
      Module.Finite c.O (wpart c.O u 0) ∧
      ∀ (ξ : Sring (O := c.O) u →ₐ[c.O] PadicAlgCl l) (r : Gam Ω S →* GG (m := 3) (R := PadicAlgCl l)), IsPtHom u ξ r → TypeI F.η r →
        _root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r (toGS Ω _ s)).mat
def ThmS6Core_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∃ g₁ : Gam Ω S, F.Marked g₁ ∧
    ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (u : Gam Ω S →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
      Module.Finite c.O (wpart c.O u 0) ∧
      ∀ (ξ : Sring (O := c.O) u →ₐ[c.O] PadicAlgCl l) (r : Gam Ω S →* GG (m := 3) (R := PadicAlgCl l)), IsPtHom u ξ r → TypeI F.η r →
        _root_.UpperTheory.V.Af.AutOnAlt K ι (-1) fun s => (r (toGS Ω _ s)).mat
end UpperTheory.V.Aut
end
end
end

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_global_compatibility_complex_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → LocCompC := by
  first | exact @_root_.GlobalTheory.LocCompCLit.main_alt | exact _root_.GlobalTheory.LocCompCLit.main_alt | (intros; apply _root_.GlobalTheory.LocCompCLit.main_alt <;> assumption)
end
end

section

noncomputable abbrev UpperTheory.V.U3.Dat.IsModularDense := @UpperTheory.V.Z.Win.Dn.IsModularA
end

section




section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3
theorem UpperTheory.GalN.V.adm2B_rhoK_of_typeII_of_modular_extensions :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)} (h : D.IsPt U g₁ r), ∀ (ι : Qbar l ≃+* ℂ),
      TypeII D.η r → (∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → _root_.UpperTheory.V.Z.Win.Dn.IsModularA D ι W) →
      _root_.UpperTheory.V.Z.Win.Dn.Adm2B ι e (N * (discr K).natAbs) (D.rhoK r h.mult) := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h ι hII hmod
  obtain ⟨h11, -, W, hext, hcont, hirr, -, hdet⟩ := typeII_facts hC D hM h hII
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  let ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hfin : ∀ g, ψQ g ^ Nat.card (ZMod N)ˣ = 1 := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) ^ _ = 1
    rw [← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]
  have hodd : Odd (discr K).natAbs := Nat.coprime_two_right.1 (D.gd.cop.coprime_dvd_right D.gd.N_even.two_dvd)
  have hkill : ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ (N * (discr K).natAbs) = 1 → g ζ = ζ) → ψQ g = 1 ∧ D.η g = 1 := fun g hg => by
    constructor
    · show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) = 1
      have hcls : Chr.cls ℚ Ω N g = 1 := by
        have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
        have : NeZero (N : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
        obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω N
        have hfix := hg ζ (by rw [pow_mul, hζ.pow_eq_one, one_pow])
        have hpow := Chr.cls_spec (k := ℚ) N g ζ hζ.pow_eq_one
        rw [hfix] at hpow
        have hone : ζ ^ (1 : ZMod N).val = ζ := by
          rw [ZMod.val_one_eq_one_mod, hζ.eq_orderOf, pow_mod_orderOf, pow_one]
        apply Units.ext
        apply ZMod.val_injective
        exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hpow.symm.trans hone.symm)
      rw [hcls, map_one, map_one]
    · rw [← MonoidHom.mem_ker, D.η_ker]
      exact UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity Ω K D.gd.quad hodd g fun ζ hζ => hg ζ (by rw [pow_mul', hζ, one_pow])
  have hblk : ∀ g ∈ D.η.ker, (r g).mat = !![W g 0 0, 0, W g 0 1; 0, 1, 0; W g 1 0, 0, W g 1 1] := fun g hg => by
    have hzero := hII.1 g hg
    have h01 := hzero 0 1 (by decide)
    have h10 := hzero 1 0 (by decide)
    have h12 := hzero 1 2 (by decide)
    have h21 := hzero 2 1 (by decide)
    change (r g).mat =
      !![(W g).val 0 0, 0, (W g).val 0 1; 0, 1, 0; (W g).val 1 0, 0, (W g).val 1 1]
    rw [hext.1 g hg]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [corner, h01, h10, h12, h21, h11 g hg]
  refine ⟨W, hirr, hmod W hext, ⟨hcont, fun w hw => ?_, fun w hw => ?_⟩, ?_, 1, fun s => ?_⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : ¬ A.valuation (l : Ω) < 1 := fun h' => hw (((places ℚ Ω l A).2.2.1 w hA).1 h')
    obtain ⟨M, hMM⟩ := pt_inertia_away D hM h A hAl
    have h1 := UpperTheory.diagonal_on_subgroup_of_conjugate (Ine (F := ℚ) A ⊓ D.η.ker) W ψQ M fun g hg => by
      have hc : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hAl hg.1
      have hc' : cycBar ℚ Ω l g = 1 := by
        rw [cycBar, MonoidHom.comp_apply, hc, map_one]
      rw [← hblk g hg.2, hMM g hg.1 hg.2, GG.mat, unitaryThreeReflection_left, tor_val, hΨ, hc', _root_.one_zpow, one_mul]
      congr 2
      funext i
      fin_cases i <;> simp [wt1]
    obtain ⟨χ, hχ, hd⟩ := UpperTheory.exists_isDiagOn_of_isDiagOn_inf_ker_sign _ _ W ψQ h1
    exact ⟨A, hA, χ, fun i s hs => hχ i s (hkill s hs).1 (hkill s hs).2, hd⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : A.valuation (l : Ω) < 1 := ((places ℚ Ω l A).2.2.1 w hA).2 hw
    obtain ⟨-, M, hup, hdiag⟩ := pt_inertia_above hC D hM h A hAl
    obtain ⟨hIk, s₀, hs₀, hu⟩ := hl1 A hAl
    obtain ⟨hnorm, hID, -⟩ := Chr.decCyc Ω l A hl.out hAl
    have hs₀' : (D.ΨQ s₀ : Qbar l) ^ 2 ≠ 1 := by
      have := (hu.map (algebraMap c.O (PadicAlgCl l))).ne_zero
      rw [map_sub, map_pow, map_one, sub_ne_zero] at this
      exact this
    set v : Fin 3 → Qbar l := (M⁻¹ : GL (Fin 3) (Qbar l)).val *ᵥ Pi.single 0 1 with hv
    have hv0 : v ≠ 0 := fun h0 => by
      have := congrArg (fun x => (M.val *ᵥ x) 0) (hv.symm.trans h0)
      simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      simp at this
    have hev : ∀ s ∈ Ine (F := ℚ) A,
        !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] *ᵥ v = (D.ΨQ s : Qbar l) • v := fun s hs => by
      have hr : (r s).right = 1 := (h.mult s).trans (hIk hs)
      rw [← hblk s (hIk hs)]
      have hconj : (conjBy M r s).mat = M.val * (r s).mat * (M⁻¹ : GL (Fin 3) (Qbar l)).val := by
        simp [conjBy, GG.mat, hr]
      have hcol : (conjBy M r s).mat *ᵥ Pi.single 0 1 = (D.ΨQ s : Qbar l) • Pi.single 0 1 := by
        rw [Matrix.mulVec_single_one]
        funext i
        fin_cases i
        · simpa [Matrix.col, GG.mat, tor_val, wt1] using hdiag s hs 0
        · simpa using hup s (hID hs) (hIk hs) 1 0 (by decide)
        · simpa using hup s (hID hs) (hIk hs) 2 0 (by decide)
      rw [hv, ← Matrix.mulVec_smul, ← hcol, hconj, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have hv1 : v 1 = 0 := by
      have := congrFun (hev s₀ hs₀) 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
      by_contra hne
      have h3 : (D.ΨQ s₀ : Qbar l) = 1 := (mul_right_cancel₀ hne ((one_mul _).trans this)).symm
      exact hs₀' (by rw [h3, one_pow])
    obtain ⟨κ, hflag, hκ⟩ := UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup (Dec (F := ℚ) A) (Ine (F := ℚ) A) W D.ΨQ ![v 0, v 2]
      (fun d hd s hs => hnorm.conj_mem' ⟨s, hID hs⟩ hs ⟨d, hd⟩)
      (fun h0 => hv0 (by
        funext i
        fin_cases i
        · exact congrFun h0 0
        · exact hv1
        · exact congrFun h0 1))
      (fun s hs => by
        have a0 := congrFun (hev s hs) 0
        have a2 := congrFun (hev s hs) 2
        funext i
        fin_cases i
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a0
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a2)
      (fun s hs => by rw [hdet, show D.η s = 1 from hIk hs]; simp)
      ⟨s₀, hs₀, hs₀'⟩
    have hκ' : ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
        κ i s = cycBar ℚ Ω l s ^ (![(e : ℤ), -(e : ℤ)] i) * (![ψQ, ψQ⁻¹] i) s := fun i s hs => by
      fin_cases i
      · exact (hκ s hs).1.trans (hΨ s)
      · refine (hκ s hs).2.trans ?_
        rw [hΨ, mul_inv, ← _root_.zpow_neg]
        rfl
    refine ⟨A, hA, ![ψQ, ψQ⁻¹], κ, fun i s hs => ?_, hflag, hκ', Or.inl fun i j hij => ?_⟩
    · fin_cases i <;> simp [(hkill s hs).1]
    · have htwo : ∃ s ∈ Ine (F := ℚ) A, ∀ n : ℤ, cycBar ℚ Ω l s ^ n = 1 → n = 0 := by
        have hu : IsUnit ((2 : ℕ) : ℤ_[l]) := by
          rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
          exact (Nat.coprime_primes hl.out Nat.prime_two).2 D.gd.l_odd
        obtain ⟨u, hu⟩ := hu
        obtain ⟨s, hs, hcyc⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hAl u
        refine ⟨s, hs, fun n hn => ?_⟩
        have hval : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = ((2 : ℚ) : Qbar l) := by
          show ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) (cycZ ℚ Ω l s : ℤ_[l]) = _
          rw [hcyc, hu, map_natCast]
          simp
        have hpow := congrArg Units.val hn
        rw [Units.val_zpow_eq_zpow_val, hval, Units.val_one, ← Rat.cast_zpow] at hpow
        have hrat : (2 : ℚ) ^ n = 1 := by exact_mod_cast hpow
        exact (zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).1 hrat
      obtain ⟨s, hs, hn⟩ := htwo
      have h1 := DFunLike.congr_fun hij ⟨s, hID hs⟩
      rw [MonoidHom.mul_apply, hκ' i _ hs, hκ' j _ hs] at h1
      have hf : ∀ i, ((![ψQ, ψQ⁻¹] i) s) ^ Nat.card (ZMod N)ˣ = 1 := fun i => by
        fin_cases i
        · exact hfin s
        · show (ψQ s)⁻¹ ^ _ = 1
          rw [inv_pow, hfin, inv_one]
      have h2 := congrArg (· ^ Nat.card (ZMod N)ˣ) h1
      simp only [mul_pow, hf, mul_one] at h2
      change (cycBar ℚ Ω l s ^ _) ^ _ = (cycBar ℚ Ω l s ^ _) ^ _ * cycBar ℚ Ω l s ^ _ at h2
      rw [← mul_pow, ← _root_.zpow_add_one, ← mul_inv_eq_one, ← inv_pow, ← mul_pow, ← _root_.zpow_sub, ← _root_.zpow_natCast,
        ← _root_.zpow_mul] at h2
      have h3 := (mul_eq_zero.1 (hn _ h2)).resolve_right (by exact_mod_cast Nat.card_pos.ne')
      fin_cases i <;> fin_cases j <;> simp at h3 <;> omega
  · refine ⟨N * (discr K).natAbs, Matrix.GeneralLinearGroup.det.comp W,
      Nat.mul_pos (NeZero.pos N) hodd.pos, fun s hs => Units.ext ?_, by simp⟩
    have := hdet s
    rw [(hkill s hs).2] at this
    simpa using this
  · rw [one_mul, inv_one, mul_one, D.rhoK_apply]
    exact hblk _ (D.η_ker ▸ galEmb_mem ℚ K Ω s)
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base
namespace UpperTheory.GalN.V
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}
theorem autCsd_iso_alt {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.RepIso r r')
    (H : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r) : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r' :=
  ⟨H.1.imp fun _ k => ⟨k.1, k.2.1, attC_iso h k.2.2⟩, fun c => (H.2 (continuous_of_iso c h.symm')).isobaricDense h⟩
end
def AutomorphyOverRationalsIsobaricDense : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → _root_.UpperTheory.V.Z.Win.IsAutQA ι r' → _root_.UpperTheory.V.Z.Win.IsAutQA ι r
theorem autQIsoN : _root_.UpperTheory.GalN.V.AutomorphyOverRationalsIsobaricDense := by
  intro F Ω _ _ _ _ l _ ι n r r' e h hc K _ _ _ _ _ _ h2 hi
  let φ : G K Ω →* G F Ω := AlgEquiv.restrictScalarsHom F
  have e' : RepIso (r.comp φ) (r'.comp φ) :=
    e.imp fun _ hg s => hg _
  have hi' : IsIrr (r'.comp φ) := by
    obtain ⟨g, hg⟩ := e'
    refine ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
    let T := Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) (Qbar l))
    have hcomm (s : G K Ω) : g * (r.comp φ) s = (r'.comp φ) s * g := by
      rw [hg s, inv_mul_cancel_right]
    have hcomap := hi.2.2 (W.comap T) le_top (fun s v hv => by
      change T ((↑((r.comp φ) s) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v) ∈ W
      dsimp only [T]
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul, hcomm,
        Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hW s (T v) hv)
    have hsurj : Function.Surjective T := fun v =>
      ⟨(↑(g⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v, by
        dsimp only [T]
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.one_mulVec]⟩
    have hmap := Submodule.map_comap_eq_of_surjective hsurj W
    rcases hcomap with hbot | htop
    · left
      rw [← hmap, hbot, Submodule.map_bot]
    · right
      rw [← hmap, htop, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  obtain ⟨⟨π, h1, h3⟩, hw⟩ := h (continuous_of_iso hc e) K h2 hi'
  exact ⟨⟨π, h1, attC_iso e'.symm' h3⟩, hw.isobaricDense e'.symm'⟩
end UpperTheory.GalN.V
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Pa
section Lv
variable (l : ℕ) {L : Type} [Field L] [NumberField L] (n : ℕ) {q : ℕ} (w : Fin q → Plc L)
end Lv
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid V0.frame O n} {B : UniversalOrdinaryDeterminantRing r} {J : Ideal B.B} {D : ℕ} (b : TWBase (pairOf B.u) J Empty D)
  {V : s.Lev} (h : (globOf r V).Hom (globOf r V0)) {q : ℕ} (w : Fin q → Plc L)
variable {b h w}
structure LevPtAlt (A : LevMod b h w) (ι : Qbar l ≃+* ℂ) : Type 1 where
  θ : A.R →+* Qbar l
  rep : (globOf r V).G₀ →* GL (Fin n) (Qbar l)
  cont : Continuous rep
  det : A.p.D.map θ = GDet.ofRep (mat rep)
  Y : Type
  [add : AddCommGroup Y]
  [mod : Module ℂ Y]
  π : Representation ℂ (GV n w) Y
  sp : A.P →+ Y
  sp_smul : ∀ (t : A.R) m, sp (t • m) = ι (θ t) • sp m
  sp_act : ∀ g m, sp (A.ρ g m) = π g (sp m)
  σ : ∀ j, SmIrr (GLw n (w j))
  iso : ∀ j, IsoSum (π.comp (atJ n w j)) ⊤ (σ j)
  lg : ∀ j (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (w j)) (rc : IrrGL (k := (w j).adicCompletion L) → WD hB), _root_.UpperTheory.Zero.LLC.IsRecT hB rc →
    _root_.UpperTheory.V.Z.Win.WOT ι (rep.comp V.pr) (rc (algNorm (σ j)))
attribute [instance] LevPtAlt.add LevPtAlt.mod
def LevMod.ClassicalAlt (A : LevMod b h w) : Prop :=
  ∃ ι : Qbar l ≃+* ℂ, ∀ m : A.P, (∀ x : _root_.UpperTheory.V.Pa.LevPtAlt A ι, x.sp m = 0) → m = 0
variable (B J) in
def LevelAlt : Prop :=
  ∃ b : TWBase (pairOf B.u) J Empty (n * Module.finrank ℚ (Lp L)),
    ∀ (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (v : Fin q → Plc (Lp L)) (w : Fin q → Plc L)
      (Bq : Fin q → ValuationSubring Ω), (∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) → Function.Injective v → (∀ j, v j ∉ s.S) →
      V.S' = s.S ∪ Set.range v → (∀ j, IsPlaceOver (Bq j) (w j)) → (∀ j, IsPlaceOver (Bq j) (v j)) →
      (∀ j, Dec (F := Lp L) (Bq j) ≤ (resP L Ω).range) → ∃ A : LevMod b h w, A.ClassicalAlt
structure LocPAlt : Prop where
  bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  gl : GlobalTheory.Published.GeometricLemma
  tame : GlobalTheory.Published.TameLocal
def HasAutOfAlt : Prop :=
  _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B), V0.S' = s.S → _root_.UpperTheory.V.Pa.LevelAlt B J → HasAut B J
end UpperTheory.V.Pa
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
open UpperTheory.V.HV (Coef)
section Alg
variable {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] (n : ℕ) {V : Type} [Fintype V] (S : V → Plc L)
variable {n S}
end Alg
namespace HSet
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c)
variable (A : Type) [CommRing A] [Algebra c.O A]
variable {A} (θ : H.X.I.T →* Aˣ)
variable (ι : Qbar l ≃+* ℂ)
structure PartAltAlt (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) : Type 1 where
  Y : Submodule ℂ (Fin H.m → H.X.Fn ℂ d)
  le : Y ≤ H.Big ι ξ
  ne : Y ≠ ⊥
  σl : ∀ v : H.V, SmIrr (GLw n (H.Sl v))
  isoL : ∀ v, IsoSum (H.atV d v) Y (σl v)
  σq : ∀ q : H.Q, SmIrr (GLw n (H.wq q))
  isoQ : ∀ q : H.Q, IsoSum (H.atW ι d (H.wq q)) Y (σq q)
  a : H.Wp → ℕ → ℂ
  a_zero : ∀ w, a w 0 = 1
  sph : ∀ (w : H.Wp) j, ∀ F ∈ Y, sphOp (H.atW ι d w.1) j F = a w j • F
  r : H.Gq →* GL (Fin n) (Qbar l)
  cont : Continuous r
  ss : IsSSRep r
  frob : ∀ (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
    (r (H.prj σ⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = heckePol n (normV w.1) (a w)
  atL : ∀ v, _root_.UpperTheory.V.Z.Ord.AtLT ι (H.ovr v) (r.comp (H.dec v)) lam (σl v)
  atQ : ∀ (q : H.Q) (B : ValuationSubring Ω) (h : IsPlaceOver B (H.wq q)) (rc : IrrGL (k := (H.wq q).adicCompletion L) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc →
    _root_.UpperTheory.V.Z.Win.WOT ι (r.comp H.prj) (rc (algNorm (σq q)))
def AutomorphicHeckeSet (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop) : Prop :=
  ∀ lam ∈ H.admitted, ∀ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), IsAlgWt ι lam ξ → ∀ F ∈ H.Big ι ξ,
    (∃ K, F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K)) → (∃ e, F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e)) →
    F ∈ ⨆ Y : {Y : H.PartAltAlt ι lam ξ // P lam Y.r}, Y.1.Y
variable [IsLocalRing A] (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))]
end HSet
end UpperTheory.V.Hi
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.J.D
def TypePS2Alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub L n) (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (τ : SmIrr (GLw n w)), π.IsLocComp w τ →
    ∀ χ : Fin n → Ine (F := L) A →* ℂˣ, (∀ i, ∃ ψ : Weil h →* ℂˣ, ∀ g, ψ (ineIncl h g) = χ i g) → (∀ rc, _root_.UpperTheory.Zero.LLC.IsRecT h rc → IsTypeWD h χ (rc (algNorm τ))) →
    ∃ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ Nonempty (τ.ρ.Equiv (PS ω)) ∧
      ∀ i (g : Ine (F := L) A), ω i (artOf h (ineIncl h g)) = χ i g
def ResidualEqualityRankTwo : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ), 1 ≤ n →
    ∀ (π π' : CuspSub L n) (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (τ τ' : SmIrr (GLw n w)), π.IsLocComp w τ →
    π'.IsLocComp w τ' → ∀ χ : Fin n → Ine (F := L) A →* ℂˣ, (∀ i, ∃ ψ : Weil h →* ℂˣ, ∀ g, ψ (ineIncl h g) = χ i g) → (∀ rc, _root_.UpperTheory.Zero.LLC.IsRecT h rc → IsTypeWD h χ (rc (algNorm τ))) →
    (∀ rc, _root_.UpperTheory.Zero.LLC.IsRecT h rc → IsTypeWD h χ (rc (algNorm τ'))) → KEq τ τ'
end UpperTheory.V.Z.J.D
end
end
end
