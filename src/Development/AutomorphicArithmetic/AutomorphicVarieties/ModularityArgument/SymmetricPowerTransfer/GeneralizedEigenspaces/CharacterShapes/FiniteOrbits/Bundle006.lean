module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.EUInvApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
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
import Mathlib.RingTheory.Valuation.Integral
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Local

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem det_dg (d : Fin 2 → kˣ) : GeneralLinearGroup.det (dg d) = d 0 * d 1 := by
  ext
  simp [dg, val_diagT, Matrix.det_diagonal, Fin.prod_univ_two]

private theorem det_mem (V : Lev k) (g : GL (Fin 2) k) (hg : g ∈ V.J 2) : GeneralLinearGroup.det g ∈ V.H := by
  obtain ⟨a, ha, s, hs, b, hb, rfl⟩ := (factJ k V 2).1 g hg
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
  have hau : a ∈ unipB k (Fin 2) := (glIwa k 2).N_le ha
  have hb0 : b ∈ Subgroup.comap (GlobalTheory.CuspRep.invT 2 k) (unipB k (Fin 2)) ⊓ Kc k 2 (V.c + 1) := hb
  have hbl := GlAx.mem_low.1 (Subgroup.mem_inf.1 hb0).1
  have hal := (mem_unipB k).1 hau
  have da : GeneralLinearGroup.det a = 1 := by
    ext
    simp only [GeneralLinearGroup.val_det_apply, Units.val_one]
    rw [Matrix.det_of_upperTriangular (fun i j hij => hal.1 i j hij)]
    simp [hal.2]
  have db : GeneralLinearGroup.det b = 1 := by
    ext
    simp only [GeneralLinearGroup.val_det_apply, Units.val_one]
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hbl.1 i j hij)]
    simp [hbl.2]
  rw [map_mul, map_mul, da, db, one_mul, mul_one]
  have ht' : ∀ i, t i ∈ V.H := fun i => ht i (Set.mem_univ i)
  rw [show diagT k (Fin 2) t = dg t from rfl, det_dg]
  exact V.H.mul_mem (ht' 0) (ht' 1)

private theorem loc {O : Type} [CommRing O] [Algebra O k] (hO : IsInts k O) (h2 : (2 : k) ≠ 0) {Δ s : k} (hs : s * s = Δ)
    (hs0 : s ≠ 0) (V : Lev k) (u : DX Δ) (hu : eD hs u ∈ V.J 2) :
    ∃ c : DX Δ, eD hs c ∈ V.J 2 ∧ u * c⁻¹ ∈ SU Δ ∧ c⁻¹ * u ∈ SU Δ ∧ ∃ x : kˣ, eD hs c = dg ![x, 1] := by
  obtain ⟨hbij, -, -, -, hdet, -⟩ := eD_facts k O hO h2 Δ s hs hs0
  obtain ⟨c, hc⟩ := hbij.2 (dg ![GeneralLinearGroup.det (eD hs u), 1])
  have hxH : GeneralLinearGroup.det (eD hs u) ∈ V.H := det_mem V _ hu
  have hcJ : eD hs c ∈ V.J 2 := by
    rw [hc]
    apply V.dg_mem
    intro i
    fin_cases i
    · simpa using hxH
    · simpa using V.H.one_mem
  have hdet1 : ∀ w : DX Δ, GeneralLinearGroup.det (eD hs w) = 1 → w ∈ SU Δ := by
    intro w hw
    show GeneralLinearGroup.det ((DX Δ).subtype w) = 1
    apply Units.ext
    have h0 := (hdet w).1
    simp only [GeneralLinearGroup.val_det_apply, Units.val_one, Subgroup.coe_subtype]
    rw [h0, ← GeneralLinearGroup.val_det_apply, hw]
    simp
  have hec : GeneralLinearGroup.det (eD hs c) = GeneralLinearGroup.det (eD hs u) := by
    rw [hc, det_dg]
    simp
  refine ⟨c, hcJ, hdet1 _ ?_, hdet1 _ ?_, _, hc⟩
  · rw [map_mul, map_inv, map_mul, map_inv, hec, mul_inv_cancel]
  · rw [map_mul, map_inv, map_mul, map_inv, hec, inv_mul_cancel]

end Local

theorem UpperTheory.V.Z.Sym.So.torPart :
    UpperTheory.V.Z.Sym.So.TorPart := by
  classical
  intro F _ _ Δ A hA u hu
  obtain ⟨-, -, hloc, -, hU2⟩ := datOk F Δ A hA
  obtain ⟨huJ, huK⟩ := (hU2 u).1 hu
  have hex : ∀ v (h : v ∈ A.Sg), ∃ c : DX ((cv v) Δ), eD (A.hs v h) c ∈ (A.V v).J 2 ∧
      u.1 v * c⁻¹ ∈ SU ((cv v) Δ) ∧ c⁻¹ * u.1 v ∈ SU ((cv v) Δ) ∧
      ∃ x : (Kv v)ˣ, eD (A.hs v h) c = dg ![x, 1] := by
    intro v h
    obtain ⟨hO, h2, hs0, -, -⟩ := hloc v h
    exact loc hO h2 (A.hs v h) hs0 (A.V v) _ (huJ v h)
  let cf : (v : Pl F) → DX ((cv v) Δ) := fun v =>
    if h : v ∈ A.Sg then Classical.choose (hex v h) else u.1 v
  have cf_in : ∀ v (h : v ∈ A.Sg), cf v = Classical.choose (hex v h) := fun v h => dif_pos h
  have cf_out : ∀ v, v ∉ A.Sg → cf v = u.1 v := fun v h => dif_neg h
  have hcRP : cf ∈ RP (fun v => DX ((cv v) Δ)) (fun v => KD ((cv v) Δ) (Ov v)) := by
    show ∀ᶠ v in Filter.cofinite, cf v ∈ KD ((cv v) Δ) (Ov v)
    rw [Filter.eventually_cofinite]
    refine A.Sg.finite_toSet.subset (fun v hv => ?_)
    by_contra h
    exact hv (by rw [cf_out v h]; exact huK v h)
  let c : DA Δ := ⟨cf, hcRP⟩
  have hSA : ∀ w : DA Δ, (∀ v, w.1 v ∈ SU ((cv v) Δ)) → w ∈ SA Δ := by
    intro w hw
    exact Subgroup.mem_iInf.2 (fun v => hw v)
  refine ⟨c, (hU2 c).2 ⟨fun v h => ?_, fun v h => ?_⟩, hSA _ (fun v => ?_), hSA _ (fun v => ?_),
    fun g d hgd => ?_⟩
  · show eD _ (cf v) ∈ _
    rw [cf_in v h]
    exact (Classical.choose_spec (hex v h)).1
  · show cf v ∈ _
    rw [cf_out v h]
    exact huK v h
  · show u.1 v * (cf v)⁻¹ ∈ SU ((cv v) Δ)
    by_cases h : v ∈ A.Sg
    · rw [cf_in v h]
      exact (Classical.choose_spec (hex v h)).2.1
    · rw [cf_out v h, mul_inv_cancel]
      exact one_mem _
  · show (cf v)⁻¹ * u.1 v ∈ SU ((cv v) Δ)
    by_cases h : v ∈ A.Sg
    · rw [cf_in v h]
      exact (Classical.choose_spec (hex v h)).2.2.1
    · rw [cf_out v h, inv_mul_cancel]
      exact one_mem _
  · apply Subtype.ext
    funext v
    show cf v * g.1 v = g.1 v * cf v
    by_cases h : v ∈ A.Sg
    · rw [cf_in v h]
      obtain ⟨hO, h2, hs0, -, -⟩ := hloc v h
      have hinj := (eD_facts (Kv v) (Ov v) hO h2 _ _ (A.hs v h) hs0).1.1
      obtain ⟨-, -, -, x, hx⟩ := Classical.choose_spec (hex v h)
      apply hinj
      rw [map_mul, map_mul, hx, hgd.1 v h]
      show diagT _ (Fin 2) ![x, 1] * diagT _ (Fin 2) (d v) = diagT _ (Fin 2) (d v) * diagT _ (Fin 2) ![x, 1]
      rw [← map_mul, ← map_mul, mul_comm]
    · rw [hgd.2 v h, mul_one, one_mul]

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem mem_J_of_cong (V : Lev k) {n : ℕ} (g : GL (Fin n) k)
    (h : ∀ i j, valuation k ((g.val - 1) i j) ≤ uniformizer k ^ (V.c + 1)) : g ∈ V.J n := by
  have hu : uniformizer k ^ (V.c + 1) < 1 := pow_lt_one₀ zero_le' uniformizer_lt_one (Nat.succ_ne_zero _)
  have e : ∀ i, valuation k (g.val i i) = 1 := fun i => by
    have h1 : valuation k (g.val i i - 1) < 1 := by
      have := h i i
      rw [Matrix.sub_apply, Matrix.one_apply_eq] at this
      exact this.trans_lt hu
    have := Valuation.map_one_add_of_lt _ h1
    rwa [add_sub_cancel] at this
  refine (Sig.memJ k V n g).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · by_cases hij : i = j
    · subst hij
      exact (e i).le
    · have := h i j
      rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at this
      exact (this.trans_lt hu).le
  · have := h i j
    rw [Matrix.sub_apply, Matrix.one_apply_ne hij.ne', sub_zero] at this
    rwa [GlAx.unif_spec]
  · have h0 : g.val i i ≠ 0 := fun h0 => by
      have := e i
      simp [h0] at this
    refine ⟨Units.mk0 _ h0, V.le (mem_Uc.2 ⟨e i, ?_⟩), rfl⟩
    have := h i i
    rw [Matrix.sub_apply, Matrix.one_apply_eq] at this
    rwa [zpow_natCast]

private theorem proj_int {O : Type} [CommRing O] [Algebra O k] (hO : IsInts k O) {Δ s : k} (hs : s * s = Δ)
    (a : Lsq k Δ) (ha : IsIntegral O a) : valuation k (proj hs a) ≤ 1 := by
  have hv : (valuation k).Integers O :=
    ⟨hO.inj, fun x => (hO.range _).1 ⟨x, rfl⟩, fun x hx => (hO.range x).2 hx⟩
  have h : IsIntegral O (proj hs a) := ha.map_of_comp_eq (RingHom.id O) (proj hs) (by
    ext x
    have e : algebraMap O (Lsq k Δ) x = ⟨algebraMap O k x, 0⟩ := rfl
    simp [proj, e])
  exact hv.mem_of_integral h

end Loc

private theorem mem_KD {K O : Type} [Field K] [CommRing O] [Algebra O K] {Δ : K} (x : DX Δ) (hd : (mt x).det = 1)
    (hi : ∀ i j, IsIntegral O (mt x i j)) : x ∈ KD Δ O := by
  let X : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := fun i j => ⟨mt x i j, hi i j⟩
  have hX : X.det = 1 := Subtype.ext (by
    have h := RingHom.map_det ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ) X
    refine h.trans ?_
    exact hd)
  exact Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.mk'' X (by rw [hX]; exact isUnit_one), Units.ext (Matrix.ext fun i j => rfl)⟩

private theorem det_conj {K : Type} [Field K] {Δ : K} (a b : DX Δ) (h : (mt b).det = 1) : (mt (a⁻¹ * b * a)).det = 1 := by
  have e : mt (a⁻¹ * b * a) = mt a⁻¹ * mt b * mt a := rfl
  have e2 : mt a⁻¹ * mt a = 1 := by
    show mt (a⁻¹ * a) = 1
    rw [inv_mul_cancel]
    rfl
  rw [e, Matrix.det_mul, Matrix.det_mul, h, mul_one, ← Matrix.det_mul, e2, Matrix.det_one]

private theorem val_norm {F : Type} [Field F] [NumberField F] (v : Pl F) :
    valuation (Kv v) ((Ideal.absNorm v.asIdeal : ℕ) : Kv v) ≤ uniformizer (Kv v) := by
  rw [le_uniformizer_iff]
  have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2 (Ideal.absNorm_mem _)
  have h2 : (Valued.v : Valuation (Kv v) _) ((Ideal.absNorm v.asIdeal : ℕ) : Kv v) < 1 := by
    have e := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := F) v ((Ideal.absNorm v.asIdeal : ℕ) : F)
    have e2 : ((Ideal.absNorm v.asIdeal : ℕ) : Kv v) = algebraMap F (Kv v) ((Ideal.absNorm v.asIdeal : ℕ) : F) := (map_natCast _ _).symm
    rw [e2]
    refine e.trans_lt ?_
    change v.valuation F (algebraMap (𝓞 F) F ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)) < 1 at h
    rw [map_natCast] at h
    exact h
  haveI : (Valued.v : Valuation (Kv v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have he : (valuation (Kv v)).IsEquiv (Valued.v : Valuation (Kv v) (WithZero (Multiplicative ℤ))) := isEquiv _ _
  simp only [← not_le] at h2 ⊢
  exact fun h3 => h2 (he.one_le_iff_one_le.1 h3)

private theorem eD_sub {K : Type} [Field K] {Δ s : K} (hs : s * s = Δ) (x : DX Δ) (i j : Fin 2) :
    ((eD hs x).val - 1) i j = proj hs ((mt x - 1) i j) := by
  have e : (eD hs x).val i j = proj hs (mt x i j) := rfl
  rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem nat_int {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (n : ℕ) : IsIntegral O (n : R) := by
  simpa using isIntegral_algebraMap (R := O) (A := R) (x := (n : O))

private def nrm {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ) : ℕ :=
  ∏ v ∈ A.Sg, Ideal.absNorm v.asIdeal ^ ((A.V v).c + 1)

private theorem mem_lvS_of_congruence {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ) (hA : A.Ok) (y : DA Δ) (g : SA Δ)
    (key : ∀ (v : Pl F) (i j : Fin 2), ∃ a, IsIntegral (Ov v) a ∧ (mt ((y⁻¹ * g * y : DA Δ).1 v) - 1) i j =
      (nrm A : Lsq (Kv v) (cv v Δ)) * a) : g ∈ A.lvS y := by
  obtain ⟨-, -, hInt, -, hU2⟩ := datOk _ _ A hA
  have hg1 : ∀ v, (mt ((g : DA Δ).1 v)).det = 1 := fun v => by
    have h1 := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 g.2 v)
    exact congrArg Units.val (MonoidHom.mem_ker.1 h1)
  have e : (MulAut.conj y⁻¹).toMonoidHom (g : DA Δ) = y⁻¹ * g * y := by simp
  rw [SD.lvS, Subgroup.mem_subgroupOf, Subgroup.mem_comap, e, hU2]
  refine ⟨fun v hv => mem_J_of_cong _ _ fun i j => ?_, fun v hv => mem_KD _ ?_ fun i j => ?_⟩
  · obtain ⟨a, ha, e1⟩ := key v i j
    obtain ⟨r, hr⟩ : Ideal.absNorm v.asIdeal ^ ((A.V v).c + 1) ∣ nrm A :=
      Finset.dvd_prod_of_mem (fun v => Ideal.absNorm v.asIdeal ^ ((A.V v).c + 1)) hv
    rw [eD_sub, e1, map_mul, map_natCast, map_mul, hr, Nat.cast_mul, Nat.cast_pow, map_mul, map_pow]
    have h1 : valuation (Kv v) ((r : ℕ) : Kv v) ≤ 1 := natCast_mem (valuation (Kv v)).integer r
    have h2 := proj_int (hInt v hv).1 (A.hs v hv) a ha
    calc _ ≤ uniformizer (Kv v) ^ ((A.V v).c + 1) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' (pow_le_pow_left' (val_norm v) _) h1) h2
      _ = _ := by simp
  · exact det_conj _ _ (hg1 v)
  · obtain ⟨a, ha, e1⟩ := key v i j
    have e2 : mt ((y⁻¹ * g * y : DA Δ).1 v) i j = (mt ((y⁻¹ * g * y : DA Δ).1 v) - 1) i j + (1 : Matrix (Fin 2) (Fin 2) _) i j := by
      simp
    rw [e2, e1]
    refine IsIntegral.add (IsIntegral.mul (nat_int _) ha) ?_
    rw [Matrix.one_apply]
    split_ifs
    exacts [isIntegral_one, isIntegral_zero]

private theorem mem_under {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) (N : ℕ)
    (hN : (N : 𝓞 (Lp L)) ∈ (un w).asIdeal) : (N : 𝓞 L) ∈ w.asIdeal := by
  have h2 := Ideal.mem_comap.1 hN
  simpa using h2

private theorem norm_ne {F : Type} [Field F] [NumberField F] (v : Pl F) : Ideal.absNorm v.asIdeal ≠ 0 :=
  fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

private theorem nrm_ne {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ) : nrm A ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (norm_ne v)

private theorem mem_of_dvd {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) (M : ℕ)
    (h : Ideal.absNorm (un w).asIdeal ∣ M) : ((3 * M : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  obtain ⟨q, rfl⟩ := h
  refine mem_under w _ ?_
  rw [Nat.cast_mul, Nat.cast_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _))

private theorem entry_mono {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) (z : Kw w) (a q : ℕ)
    (h : ∃ b ∈ w.adicCompletionIntegers L, z = ((3 * (a * q) : ℕ) : Kw w) * b) :
    ∃ b ∈ w.adicCompletionIntegers L, z = (a : Kw w) * b := by
  obtain ⟨b, hb, e⟩ := h
  refine ⟨(3 * q : ℕ) * b, mul_mem (natCast_mem _ _) hb, ?_⟩
  rw [e]
  push_cast
  ring

private theorem abs_lev {α β γ υ σ : Type} (Y : Finset α) (p : α → β → Prop) (hY : ∀ y ∈ Y, {v | ¬ p y v}.Finite)
    (b : β → ℕ) (hb : ∀ v, b v ≠ 0) (un : γ → β) (mem : ℕ → γ → Prop) (hmem : ∀ w M, b (un w) ∣ M → mem (3 * M) w)
    (C : ℕ → υ → Prop) (D : υ → σ → Prop) (E : α → σ → Prop)
    (h : ∀ y, ∃ a, a ≠ 0 ∧ ∀ q U, C (3 * (a * q)) U → ∀ g, D U g → E y g) :
    ∃ m : ℕ, 3 ≤ m ∧ (∀ w, ¬ mem m w → ∀ y ∈ Y, p y (un w)) ∧ ∀ U, C m U → ∀ y ∈ Y, ∀ g, D U g → E y g := by
  classical
  choose a ha hE using h
  let P : Finset β := (Set.Finite.biUnion Y.finite_toSet hY).toFinset
  let M : ℕ := (∏ y ∈ Y, a y) * ∏ v ∈ P, b v
  have hM : 0 < M := Nat.pos_of_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun y _ => ha y)
    (Finset.prod_ne_zero_iff.2 fun v _ => hb v))
  refine ⟨3 * M, Nat.le_mul_of_pos_right 3 hM, fun w hw y hy => ?_, fun U hU y hy g hg => ?_⟩
  · by_contra hne
    have hv : un w ∈ P := (Set.Finite.mem_toFinset _).2 (Set.mem_biUnion hy hne)
    exact hw (hmem w M (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hv) _))
  · obtain ⟨q, hq⟩ : a y ∣ M := Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hy) _
    rw [hq] at hU
    exact hE y q U hU g hg

set_option allowUnsafeReducibility true in
attribute [local irreducible] cv Ov DX KD RP SA Lsq

theorem UpperTheory.V.Z.Sym.So.congLev :
    UpperTheory.V.Z.Sym.So.CongLev := by
  intro L _ _ _ B hB _ _ _ A hA _ Y hY
  refine abs_lev Y _ hY (fun v => Ideal.absNorm v.asIdeal) norm_ne un _ (fun w M h => mem_of_dvd w M h) _ _ _ fun y => ?_
  exact (hB.cong y (nrm A) (nrm_ne A)).elim fun a h => ⟨a, h.1, fun q U hU g hg =>
    mem_lvS_of_congruence A hA y g fun v => h.2 g v fun w _ i j => entry_mono w _ _ _ (((hU _).1 hg).2 w i j)⟩

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

private theorem rp_exists_unique {I : Type} {Gv Hv : I → Type} [∀ v, Group (Gv v)] [∀ v, Group (Hv v)]
    (K : ∀ v, Subgroup (Gv v)) (S : Finset I) (e : ∀ v, v ∈ S → (Gv v →* Hv v))
    (he : ∀ v h, Function.Bijective (e v h)) (w : ∀ v, Hv v) :
    ∃! g : RP Gv K, (∀ v (h : v ∈ S), e v h (g.1 v) = w v) ∧ ∀ v, v ∉ S → g.1 v = 1 := by
  classical
  let x : ∀ v, Gv v := fun v => if h : v ∈ S then Function.surjInv (he v h).2 (w v) else 1
  have hx : x ∈ RP Gv K := by
    show ∀ᶠ v in Filter.cofinite, x v ∈ K v
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra h
    rw [Finset.mem_coe] at h
    exact hv (by simp [x, h, one_mem])
  refine ⟨⟨x, hx⟩, ⟨fun v h => ?_, fun v h => ?_⟩, ?_⟩
  · show e v h (x v) = w v
    simp only [x, dif_pos h]
    exact Function.surjInv_eq _ _
  · show x v = 1
    simp [x, h]
  · rintro g ⟨h1, h2⟩
    apply Subtype.ext
    funext v
    by_cases h : v ∈ S
    · apply (he v h).1
      rw [h1 v h]
      show w v = e v h (x v)
      simp only [x, dif_pos h]
      exact (Function.surjInv_eq _ _).symm
    · rw [h2 v h]
      show 1 = x v
      simp [x, h]

private theorem det_dg_inv {k : Type} [Field k] (t : kˣ) :
    ((dg ![t, t⁻¹] : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = 1 := by
  simp [dg, val_diagT, Matrix.det_diagonal, Fin.prod_univ_two]

end UpperTheory.V.Z.Sym.So

private theorem mem_su_of_det_eq_one {K : Type} [Field K] {D : K} (x : DX D) (hx : (Glob.mt x).det = 1) :
    x ∈ SU D := by
  rw [SU, MonoidHom.mem_ker]
  refine Units.ext ?_
  rw [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact hx

theorem UpperTheory.V.Z.Sym.So.elEx :
    UpperTheory.V.Z.Sym.So.ElEx := by
  intro F _ _ Δ A hA
  have loc := fun v (h : v ∈ A.Sg) => (datOk F Δ A hA).2.2.1 v h
  have bU : ∀ v (h : v ∈ A.Sg), Function.Bijective (eU (A.hs v h)) := fun v h =>
    (eU_facts (Kv v) (Ov v) (loc v h).1 (loc v h).2.1 _ (A.s v) (A.hs v h) (loc v h).2.2.1).1
  have bD : ∀ v (h : v ∈ A.Sg), Function.Bijective (eD (A.hs v h)) := fun v h =>
    (eD_facts (Kv v) (Ov v) (loc v h).1 (loc v h).2.1 _ (A.s v) (A.hs v h) (loc v h).2.2.1).1
  refine ⟨fun d => ?_, fun d => ?_, ?_, ?_, ?_⟩
  · exact rp_exists_unique (Hv := fun v => GL (Fin 3) (Kv v)) _ A.Sg (fun v h => eU (A.hs v h)) bU
      (fun v => dg (d v))
  · exact rp_exists_unique (Hv := fun v => GL (Fin 2) (Kv v)) _ A.Sg (fun v h => eD (A.hs v h)) bD
      (fun v => dg (d v))
  · rintro g g' d d' ⟨hg1, hg2⟩ ⟨hg1', hg2'⟩
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · show eU (A.hs v h) (g.1 v * g'.1 v) = dg (d v * d' v)
      rw [map_mul, hg1 v h, hg1' v h]
      exact (map_mul (diagT (Kv v) (Fin 3)) _ _).symm
    · show g.1 v * g'.1 v = 1
      rw [hg2 v h, hg2' v h, mul_one]
  · rintro g g' d d' ⟨hg1, hg2⟩ ⟨hg1', hg2'⟩
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · show eD (A.hs v h) (g.1 v * g'.1 v) = dg (d v * d' v)
      rw [map_mul, hg1 v h, hg1' v h]
      exact (map_mul (diagT (Kv v) (Fin 2)) _ _).symm
    · show g.1 v * g'.1 v = 1
      rw [hg2 v h, hg2' v h, mul_one]
  · rintro g t ⟨hg1, hg2⟩
    simp only [SA, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v
    show g.1 v ∈ SU (cv v Δ)
    by_cases h : v ∈ A.Sg
    · have hfac := (eD_facts (Kv v) (Ov v) (loc v h).1 (loc v h).2.1 _ (A.s v) (A.hs v h)
        (loc v h).2.2.1).2.2.2.2.1 (g.1 v)
      have hd := hg1 v h
      have h2 : ((dg (SD.dS t v) : GL (Fin 2) (Kv v)) : Matrix (Fin 2) (Fin 2) (Kv v)).det = 1 :=
        det_dg_inv (t v)
      refine mem_su_of_det_eq_one _ ?_
      rw [hfac.1, hd, h2, map_one]
    · exact (hg2 v h).symm ▸ one_mem _

end
end
