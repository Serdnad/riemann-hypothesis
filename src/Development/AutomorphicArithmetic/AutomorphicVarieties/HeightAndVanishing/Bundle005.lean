module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem ker_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter O N) (m : ℕ) [NeZero m] (h : ψ.conductor ∣ m) :
    (Chr.cls ℚ Ω m).ker ≤ (Chr.dirG ℚ Ω ψ).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ ⊢
  obtain ⟨hd, χ₀, hχ⟩ := ψ.factorsThrough_conductor
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  have e1 := (Chr.clsFacts ℚ Ω N).2.1 ψ.conductor hd
  have e2 := (Chr.clsFacts ℚ Ω m).2.1 ψ.conductor h
  have hc : Chr.cls ℚ Ω ψ.conductor σ = 1 := by
    rw [← e2, MonoidHom.comp_apply, hσ, map_one]
  have hu : ∀ u : (ZMod N)ˣ, MulChar.toUnitHom ψ u = MulChar.toUnitHom χ₀ (ZMod.unitsMap hd u) := by
    intro u
    apply Units.ext
    rw [MulChar.coe_toUnitHom, MulChar.coe_toUnitHom]
    conv_lhs => rw [hχ]
    rw [DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  unfold Chr.dirG
  rw [MonoidHom.comp_apply, hu, ← MonoidHom.comp_apply (ZMod.unitsMap hd), e1, hc, map_one]

theorem UpperTheory.V.HV.ivField :
    ∀ (χ : PChar) (l : ℕ) [Fact l.Prime] (j : ℕ), l ≠ 2 → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω],
      ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (L₁ : Type) (_ : Field L₁) (_ : NumberField L₁) (_ : Algebra L₀ L₁) (_ : Algebra L₁ Ω)
        (_ : IsAlgClosure L₁ Ω) (_ : IsAbelianGalois ℚ L₁), IsAbField (Lchi χ l) L₀ ∧ IsLayer l j L₀ L₁ ∧ Module.finrank ℚ L₁ ≤ l * χ.N * l ^ j ∧
        ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N), ψ.conductor ∣ χ.N → galOf ℚ L₁ Ω ≤ (Chr.dirG ℚ Ω ψ).ker := by
  intro χ l _ j hl2 Ω _ _ _
  haveI := χ.ne
  have hlp : l.Prime := Fact.out
  have hAm : (Lchi χ l).m = l * χ.N := by
    simp only [Lchi, AbF.cyc]
    exact max_eq_left (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hlp.ne_zero (NeZero.ne _)))
  have hldvd : l ∣ (Lchi χ l).m := by rw [hAm]; exact dvd_mul_right l _
  obtain ⟨L₀, i0, i1, hab, hdeg⟩ := exists_numberField_isAbField_finrank_eq_deg (Lchi χ l)
  have hmu : (Lchi χ l).HasMu l := by
    refine ⟨hldvd, ?_⟩
    rintro a ⟨u, hu, hua⟩
    have hu1 : u = 1 := (Subgroup.mem_bot).mp hu
    rw [hu1, Units.val_one] at hua
    have h2 : ((a : ℕ) : ZMod (Lchi χ l).m) = ((1 : ℕ) : ZMod (Lchi χ l).m) := by
      rw [Nat.cast_one]; exact hua.symm
    exact Nat.ModEq.of_dvd hldvd ((ZMod.natCast_eq_natCast_iff _ _ _).mp h2)
  obtain ⟨z, hz⟩ := (abelianField_hasMu_iff_exists_primitiveRoot (Lchi χ l) l hlp hl2 L₀ hab).mp hmu
  obtain ⟨L₁, i2, i3, i4, hlay⟩ := exists_cyclotomic_layer_of_primitiveRoot l j hlp hl2 L₀ ⟨z, hz⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra L₁ Ω := (IsAlgClosed.lift (R := ℚ) (S := L₁) (M := Ω)).toRingHom.toAlgebra
  letI : Algebra L₀ Ω := ((algebraMap L₁ Ω).comp (algebraMap L₀ L₁)).toAlgebra
  haveI : IsScalarTower L₀ L₁ Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsScalarTower ℚ L₁ Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsScalarTower ℚ L₀ L₁ := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI hcl : IsAlgClosure L₁ Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) L₁⟩
  obtain ⟨N', hN', H, hlev⟩ := Chr.layerLevel (Lchi χ l) l j hlp L₀ L₁ hab hlay
  obtain ⟨habel, -, -⟩ := Chr.levGal L₁ N' H hlev
  have hlev0 := Chr.abLevel.1 (Lchi χ l) L₀ hab
  have hgal0 := ((Chr.levGal L₀ _ _ hlev0).2.2 Ω).1
  refine ⟨L₀, i0, i1, L₁, i2, i3, i4, inferInstance, hcl, habel, hab, hlay, ?_, ?_⟩
  · rw [← Module.finrank_mul_finrank ℚ L₀ L₁, hdeg, hlay.2]
    apply Nat.mul_le_mul_right
    rw [AbF.deg]
    show (⊥ : Subgroup (ZMod (Lchi χ l).m)ˣ).index ≤ l * χ.N
    rw [Subgroup.index_bot, ← hAm]
    haveI : NeZero (Lchi χ l).m := ⟨(AbF.pos _).ne'⟩
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact Nat.totient_le _
  · intro O _ _ N _ ψ hψ
    calc galOf ℚ L₁ Ω ≤ galOf ℚ L₀ Ω := galOf_le ℚ L₀ Ω L₁
      _ = Chr.levH ℚ Ω (Lchi χ l).H := hgal0
      _ ≤ (Chr.dirG ℚ Ω ψ).ker := by
        rw [Chr.levH]
        show Subgroup.comap _ ⊥ ≤ _
        rw [MonoidHom.comap_bot]
        exact ker_le Ω ψ _ (hψ.trans (hAm ▸ dvd_mul_left _ _))
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem idx_le (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N) :
    ψ.toUnitHom.ker.index ≤ orderOf ψ := by
  have hpos := MulChar.orderOf_pos ψ
  haveI : NeZero (orderOf ψ) := ⟨hpos.ne'⟩
  rw [Subgroup.index_ker]
  calc Nat.card ψ.toUnitHom.range ≤ Nat.card (rootsOfUnity (orderOf ψ) O) := by
        apply Subgroup.card_le_of_le
        rintro _ ⟨u, rfl⟩
        rw [mem_rootsOfUnity]
        ext
        rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply' ψ hpos.ne',
          pow_orderOf_eq_one, MulChar.one_apply_coe, Units.val_one]
    _ ≤ orderOf ψ := card_rootsOfUnity O _

theorem UpperTheory.V.HV.vsField :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N),
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra L Ω) (_ : IsAlgClosure L Ω) (_ : IsAbelianGalois ℚ L), HasMuQ l L ∧
        Module.finrank ℚ L ≤ orderOf ψ * l ∧ Nonempty (L →ₐ[ℚ] CyclotomicField (l * N) ℚ) ∧ galOf ℚ L Ω ≤ (Chr.dirG ℚ Ω ψ).ker := by
  intro Ω _ _ _ l hl hl2 O _ _ N _ ψ
  have hlp : l.Prime := hl.out
  haveI : NeZero l := ⟨hlp.ne_zero⟩
  haveI hMz : NeZero (l * N) := ⟨mul_ne_zero hlp.ne_zero (NeZero.ne N)⟩
  let φN : (ZMod (l * N))ˣ →* (ZMod N)ˣ := ZMod.unitsMap (dvd_mul_left N l)
  let φl : (ZMod (l * N))ˣ →* (ZMod l)ˣ := ZMod.unitsMap (dvd_mul_right l N)
  let H : Subgroup (ZMod (l * N))ˣ := (ψ.toUnitHom.comp φN).ker ⊓ φl.ker
  let A : AbF := ⟨l * N, Nat.pos_of_ne_zero (NeZero.ne (l * N)), H⟩
  obtain ⟨L, fL, nfL, hab, -⟩ := exists_numberField_isAbField_finrank_eq_deg A
  have hlev : Chr.HasLevel L (l * N) H := Chr.abLevel.1 A L hab
  obtain ⟨hgal, hfin, hΩ⟩ := Chr.levGal L (l * N) H hlev
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let f : L →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra L Ω := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ L Ω := inferInstance
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  haveI hcl : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  refine ⟨L, fL, nfL, inferInstance, hcl, hgal, ?_, ?_, ?_, ?_⟩
  · have hmu : A.HasMu l := by
      unfold AbF.HasMu
      refine ⟨dvd_mul_right l N, ?_⟩
      intro a ha
      unfold AbF.ker at ha
      obtain ⟨u, hu, hua⟩ := ha
      have h1 : φl u = 1 := MonoidHom.mem_ker.mp hu.2
      have h2 : ((φl u : (ZMod l)ˣ) : ZMod l) = (a : ZMod l) := by
        simp only [φl, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply]
        rw [hua, ZMod.cast_natCast (dvd_mul_right l N)]
      rw [h1, Units.val_one] at h2
      exact (ZMod.natCast_eq_natCast_iff a 1 l).mp (by rw [← h2, Nat.cast_one])
    obtain ⟨z, hz⟩ := (abelianField_hasMu_iff_exists_primitiveRoot A l hlp hl2 L hab).mp hmu
    unfold HasMuQ
    rw [if_neg hl2]
    exact ⟨z, hz⟩
  · rw [hfin]
    refine (Subgroup.index_inf_le).trans (Nat.mul_le_mul ?_ ?_)
    · rw [← MonoidHom.comap_ker, Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective _)]
      exact idx_le O N ψ
    · rw [Subgroup.index_ker]
      refine (Subgroup.card_le_card_group _).trans ?_
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      exact Nat.totient_le l
  · have hab' := hab
    unfold IsAbField at hab'
    obtain ⟨N', hN', j, ζ, hmN, hζ, h3⟩ := hab'
    haveI : NeZero N' := hN'
    haveI : NeZero ((N' : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N')⟩
    haveI : IsCyclotomicExtension {N'} ℚ (CyclotomicField N' ℚ) := CyclotomicField.isCyclotomicExtension N' ℚ
    haveI : IsGalois ℚ (CyclotomicField N' ℚ) := IsCyclotomicExtension.isGalois {N'} ℚ _
    haveI : FiniteDimensional ℚ (CyclotomicField N' ℚ) := IsCyclotomicExtension.finiteDimensional {N'} ℚ _
    haveI : NeZero ((l * N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne (l * N))⟩
    haveI : IsCyclotomicExtension {l * N} ℚ (CyclotomicField (l * N) ℚ) :=
      CyclotomicField.isCyclotomicExtension (l * N) ℚ
    have hmN' : l * N ∣ N' := hmN
    have hdpos : N' / (l * N) ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N')) hmN')
        (Nat.pos_of_ne_zero (NeZero.ne (l * N)))).ne'
    have hη : IsPrimitiveRoot (ζ ^ (N' / (l * N))) (l * N) := by
      have := hζ.pow_of_dvd hdpos (Nat.div_dvd_of_dvd hmN')
      rwa [Nat.div_div_self hmN' (NeZero.ne N')] at this
    let F : IntermediateField ℚ (CyclotomicField N' ℚ) := IntermediateField.adjoin ℚ {ζ ^ (N' / (l * N))}
    haveI : IsCyclotomicExtension {l * N} ℚ F := hη.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hmem : ∀ x, j x ∈ F := by
      intro x
      rw [← IsGalois.fixedField_fixingSubgroup F, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      have hτη : τ (ζ ^ (N' / (l * N))) = ζ ^ (N' / (l * N)) :=
        (IntermediateField.mem_fixingSubgroup_iff F τ).mp hτ _
          (IntermediateField.mem_adjoin_simple_self ℚ _)
      have hτζ : τ ζ = ζ ^ ((hζ.autToPow ℚ τ : ZMod N')).val := (hζ.autToPow_spec ℚ τ).symm
      have hpow : (ζ ^ (N' / (l * N))) ^ ((hζ.autToPow ℚ τ : ZMod N')).val = ζ ^ (N' / (l * N)) := by
        calc (ζ ^ (N' / (l * N))) ^ ((hζ.autToPow ℚ τ : ZMod N')).val
            = (ζ ^ ((hζ.autToPow ℚ τ : ZMod N')).val) ^ (N' / (l * N)) := by
              rw [← pow_mul, ← pow_mul, mul_comm]
          _ = (τ ζ) ^ (N' / (l * N)) := by rw [hτζ]
          _ = τ (ζ ^ (N' / (l * N))) := (map_pow τ ζ _).symm
          _ = ζ ^ (N' / (l * N)) := hτη
      have hne : ζ ^ (N' / (l * N)) ≠ 0 := hη.ne_zero (NeZero.ne (l * N))
      have hz : (ζ ^ (N' / (l * N))) ^ ((((hζ.autToPow ℚ τ : ZMod N')).val : ℤ) - 1) = 1 := by
        rw [zpow_sub₀ hne, zpow_natCast, zpow_one, hpow, div_self hne]
      have hd := (hη.zpow_eq_one_iff_dvd _).mp hz
      have hc : ((((((hζ.autToPow ℚ τ : ZMod N')).val : ℤ) - 1 : ℤ)) : ZMod (l * N)) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ (l * N)).mpr hd
      push_cast at hc
      have hker : A.ker ((hζ.autToPow ℚ τ : ZMod N')).val := by
        unfold AbF.ker
        exact ⟨1, Subgroup.one_mem _, by rw [Units.val_one]; exact (sub_eq_zero.mp hc).symm⟩
      exact ((h3 τ _ hτζ).mpr hker) x
    exact ⟨(IsCyclotomicExtension.algEquiv {l * N} ℚ F (CyclotomicField (l * N) ℚ)).toAlgHom.comp
      (j.codRestrict F.toSubalgebra hmem)⟩
  · intro σ hσ
    rw [(hΩ Ω).1] at hσ
    unfold Chr.levH at hσ
    rw [Subgroup.mem_comap] at hσ
    rw [MonoidHom.mem_ker]
    unfold Chr.dirG
    rw [← (Chr.clsFacts ℚ Ω (l * N)).2.1 N (dvd_mul_left N l)]
    exact MonoidHom.mem_ker.mp hσ.1
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.lossLe :
    ∀ l N n e : ℕ, l.Prime → l ≠ 2 → 2 ≤ N → n ≤ N → 1 ≤ e → lossAll l N n e ≤ (N * e) ^ 6 ∧ LDataCardLeFinrank.nuBound l N e ≤ 2 * N * e := by
  intro l N n e hl hl2 hN hn he
  have hfac : ∀ (p m : ℕ), m.factorization p ≤ m := by
    intro p m
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0]
    · exact (Nat.factorization_lt p h0.ne').le
  have hnu : LDataCardLeFinrank.nuBound l N e ≤ 2 * N * e := by
    unfold LDataCardLeFinrank.nuBound
    have a1 := hfac l N
    have a2 := hfac l e
    split_ifs
    · have : max (N.factorization l) 1 ≤ N.factorization l + 1 := max_le (by omega) (by omega)
      nlinarith
    · exact Nat.zero_le _
  have hk : N.primeFactors.card ≤ N := by
    calc N.primeFactors.card ≤ (Finset.Icc 1 N).card := by
          apply Finset.card_le_card
          intro p hp
          have hp' := Nat.mem_primeFactors.mp hp
          simp only [Finset.mem_Icc]
          exact ⟨hp'.1.one_lt.le, Nat.le_of_dvd (by omega) hp'.2.1⟩
      _ = N := by simp
  have hv : n.factorization l ≤ N := (hfac l n).trans hn
  refine ⟨?_, hnu⟩
  set M := N * e with hM
  have hNM : N ≤ M := Nat.le_mul_of_pos_right N he
  have hM2 : 2 ≤ M := hN.trans hNM
  have hnuM : LDataCardLeFinrank.nuBound l N e ≤ 2 * M := by rw [hM, ← mul_assoc]; exact hnu
  unfold lossAll Chr.loss
  have b1 : (n + n ^ 2) * LDataCardLeFinrank.nuBound l N e ≤ (M + M ^ 2) * (2 * M) := by
    apply Nat.mul_le_mul _ hnuM
    have : n ≤ M := hn.trans hNM
    have : n ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left this 2
    omega
  have b2 : N.primeFactors.card * (n * n.factorization l) ≤ M * (M * M) :=
    Nat.mul_le_mul (hk.trans hNM) (Nat.mul_le_mul (hn.trans hNM) (hv.trans hNM))
  have b3 : N.primeFactors.card * n.factorization l ≤ M * M :=
    Nat.mul_le_mul (hk.trans hNM) (hv.trans hNM)
  have hM3 : 8 ≤ M ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ M ^ 3 := Nat.pow_le_pow_left hM2 3
  have b4 : (M + M ^ 2) * (2 * M) + M * (M * M) + M * M ≤ M ^ 6 := by
    have e6 : M ^ 6 = M ^ 3 * M ^ 3 := by ring
    have : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h1 : (M + M ^ 2) * (2 * M) + M * (M * M) + M * M = 2 * M ^ 2 + 3 * M ^ 3 + M ^ 2 := by ring
    rw [h1, e6]
    nlinarith
  omega
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem point_arith (x B : ℝ) (hx : 2 ≤ x) (hB : 0 ≤ B) (k K D C0 : ℕ) (hk : k ≤ K) :
    (k : ℝ) * (x ^ D + D * B) + x ^ C0 ≤ x ^ (C0 + D + K + K * D) + ((C0 + D + K + K * D : ℕ) : ℝ) * B := by
  have hx1 : (1:ℝ) ≤ x := by linarith
  have h1 := one_add_mul_le_pow (show (-2:ℝ) ≤ x - 1 by linarith) K
  rw [show (1:ℝ) + (x - 1) = x by ring] at h1
  have hKr : (k:ℝ) ≤ K := by exact_mod_cast hk
  have hK0 : (0:ℝ) ≤ K := by positivity
  have hD0 : (0:ℝ) ≤ D := by positivity
  have hC0 : (0:ℝ) ≤ C0 := by positivity
  have hc : (K:ℝ) + 1 ≤ x ^ K := by nlinarith
  have ha : 1 ≤ x ^ C0 := one_le_pow₀ hx1
  have hb : 1 ≤ x ^ D := one_le_pow₀ hx1
  have he : 1 ≤ x ^ (K * D) := one_le_pow₀ hx1
  have hpow : x ^ (C0 + D + K + K * D) = x ^ C0 * x ^ D * x ^ K * x ^ (K * D) := by
    rw [pow_add, pow_add, pow_add]
  have hM : (k:ℝ) * D ≤ ((C0 + D + K + K * D : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hMB : (k:ℝ) * D * B ≤ ((C0 + D + K + K * D : ℕ) : ℝ) * B :=
    mul_le_mul_of_nonneg_right hM hB
  have hab : x ^ C0 ≤ x ^ C0 * x ^ D := le_mul_of_one_le_right (by positivity) hb
  have habc : x ^ C0 * x ^ D * ((K:ℝ) + 1) ≤ x ^ C0 * x ^ D * x ^ K :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  have hq : x ^ C0 * x ^ D * x ^ K ≤ x ^ C0 * x ^ D * x ^ K * x ^ (K * D) :=
    le_mul_of_one_le_right (by positivity) he
  have hkb : (k:ℝ) * x ^ D ≤ K * x ^ D := mul_le_mul_of_nonneg_right hKr (by positivity)
  have hKb : (K:ℝ) * x ^ D ≤ K * (x ^ C0 * x ^ D) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) ha) hK0
  rw [hpow]
  nlinarith

theorem UpperTheory.V.HV.point :
    SumIn → SumOut → PointHV := by
  intro hin hout χ j
  classical
  obtain ⟨C0, r₁, r₂, hr₁, hr₂, hO⟩ := hout χ
  obtain ⟨Cl, hCl⟩ : ∃ Cl : ℕ → ℕ, ∀ (l : Nat.Primes) (hl : (l:ℕ) ∈ Bchi χ),
      Cl l = Classical.choose (hin χ l (j l) hl) :=
    ⟨fun n => if hn : n.Prime ∧ n ∈ Bchi χ then Classical.choose (hin χ ⟨n, hn.1⟩ (j n) hn.2) else 0,
      fun l hl => dif_pos (show (l:ℕ).Prime ∧ (l:ℕ) ∈ Bchi χ from ⟨l.2, hl⟩)⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ l ∈ Bchi χ, Cl l ≤ D :=
    ⟨∑ l ∈ Bchi χ, Cl l, fun l hl => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hl⟩
  refine ⟨C0 + D + (Bchi χ).card + (Bchi χ).card * D, r₁, r₂, hr₁, hr₂, ?_⟩
  intro h hχ h1 h2 h3 h4 t ht hbig B hB hlay E _ _ _ hE Ω _ _ _ ld
  have hIn : ∀ l : Nat.Primes, (l:ℕ) ∈ Bchi χ →
      PlusLe ld {l} t (((h.N:ℝ) * t) ^ (Cl l) + (Cl l : ℝ) * B) := by
    intro l hl
    rw [hCl l hl]
    exact Classical.choose_spec (hin χ l (j l) hl) h hχ t ht hbig B hB (hlay l hl) E hE Ω ld
  have hOut : ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l:ℕ) ≠ 2 ∧ (l:ℕ) ∉ Bchi χ) →
      PlusLe ld S t (((h.N:ℝ) * t) ^ C0) :=
    fun S hS => hO h hχ h1 h2 h3 h4 t ht hbig E hE Ω ld S hS
  have hx2 : (2:ℝ) ≤ (h.N:ℝ) * t := by
    have hN : (1:ℝ) ≤ h.N := by exact_mod_cast h.N_pos
    have ht' : (2:ℝ) ≤ t := by exact_mod_cast ht
    nlinarith
  refine ⟨?_, ?_⟩
  · intro p hpf e hp2 he1 he2
    by_cases hb : p ∈ Bchi χ
    · exact (hIn ⟨p, hpf.out⟩ hb).1 ⟨p, hpf.out⟩ (Finset.mem_singleton_self _) e he1 he2
    · refine (hOut {⟨p, hpf.out⟩} ?_).1 ⟨p, hpf.out⟩ (Finset.mem_singleton_self _) e he1 he2
      intro l hl
      obtain rfl := Finset.mem_singleton.mp hl
      exact ⟨hp2, hb⟩
  · intro S hS2
    rw [← Finset.sum_filter_add_sum_filter_not S (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ)]
    have hout2 := (hOut (S.filter (fun l : Nat.Primes => (l:ℕ) ∉ Bchi χ)) (by
      intro l hl
      rw [Finset.mem_filter] at hl
      exact ⟨hS2 l hl.1, hl.2⟩)).2
    have hin2 : ∑ l ∈ S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ),
        Real.log ((l:ℕ):ℝ) * ∑ e ∈ Finset.Ico 1 t, ((plusLen (ld l) e).toNat : ℝ)
        ≤ ∑ l ∈ S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ), (((h.N:ℝ) * t) ^ D + (D:ℝ) * B) := by
      apply Finset.sum_le_sum
      intro l hl
      rw [Finset.mem_filter] at hl
      have h0 := (hIn l hl.2).2
      rw [Finset.sum_singleton] at h0
      have hle := hD l hl.2
      have hp1 : ((h.N:ℝ) * t) ^ (Cl l) ≤ ((h.N:ℝ) * t) ^ D := pow_le_pow_right₀ (by linarith) hle
      have hp2 : (Cl l : ℝ) * B ≤ (D:ℝ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hB
      linarith
    rw [Finset.sum_const, nsmul_eq_mul] at hin2
    have hcard : (S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ)).card ≤ (Bchi χ).card :=
      Finset.card_le_card_of_injOn (fun l : Nat.Primes => (l:ℕ))
        (fun l hl => (Finset.mem_filter.mp hl).2) Subtype.coe_injective.injOn
    have key := point_arith ((h.N:ℝ) * t) B hx2 hB _ (Bchi χ).card D C0 hcard
    linarith
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.countZ :
    PropZ → CountZ := by
  intro hZ χ
  refine ⟨0, fun h _ t hB Ω _ _ _ l hl c e hl2 he0 het ψ hψ hc => ?_⟩
  obtain ⟨hnB, hdiv, rfl⟩ := hc
  have h5 : 5 ≤ l := by
    have h3 : l ≠ 3 := fun h3 => hnB (h3 ▸ Finset.mem_insert_self _ _)
    have h4 : l ≠ 4 := fun h4 => absurd (h4 ▸ hl.out) (by norm_num)
    have := hl.out.two_le
    omega
  have hev : Even e := by
    have h1 := (h.mem_X.1 hψ).2
    unfold PsiEven at h1
    rw [MulChar.one_apply (isUnit_one.neg)] at h1
    by_contra hne
    rw [(Nat.not_even_iff_odd.1 hne).neg_one_pow] at h1
    have h2 : (2 : c.O) = 0 := by linear_combination h1
    exact two_ne_zero h2
  have h2e : 2 ≤ e := by obtain ⟨k, rfl⟩ := hev; omega
  have hd : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O h.N) = 1 := by
    ext σ
    simp [Chr.dirG]
  have h0 : Vlen Ω c e (1 : DirichletCharacter c.O h.N) = 0 := by
    unfold Vlen
    rw [hd]
    exact le_antisymm ((Chr.V'_le_V l h.N e 1).trans (hZ Ω l c e h5 h2e hev hdiv).le) bot_le
  refine ⟨by rw [h0]; simp, ?_⟩
  simp [Vn, h0, Chr.nrm]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.pZeroLe :
    ∀ m : ℕ, 0 < m → (pZero m).Prime ∧ 5 ≤ pZero m ∧ ¬ pZero m ∣ m ∧ pZero m ≤ 2 * m + 10 := by
  intro m hm
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (m + 5) (by omega)
  have hmem : p ∈ {p : ℕ | p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ m} :=
    ⟨hp, by omega, fun h => by have := Nat.le_of_dvd hm h; omega⟩
  have h3 : UpperTheory.V.HV.pZero m ∈ {p : ℕ | p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ m} := Nat.sInf_mem ⟨p, hmem⟩
  have h4 : UpperTheory.V.HV.pZero m ≤ p := Nat.sInf_le hmem
  exact ⟨h3.1, h3.2.1, h3.2.2, by omega⟩
end
