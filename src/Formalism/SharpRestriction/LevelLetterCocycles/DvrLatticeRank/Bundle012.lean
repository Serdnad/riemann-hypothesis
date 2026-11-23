module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle026
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfDict
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle009
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
public import Mathlib.FieldTheory.Relrank
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Cyclotomic.Gal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.DvdPf

open Formalism.BasicNotions Formalism.BasicNotions.Loc Module

private theorem finrank_cyclotomicExt_dvd_sub_one {F Ω : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω]
    [IsAlgClosed Ω] [CharZero Ω] [Algebra.IsIntegral F Ω] (E K : IntermediateField F Ω) (hEK : E ≤ K) (l : ℕ) (hp : l.Prime)
    (hle : K ≤ E ⊔ IntermediateField.adjoin F {x : Ω | x ^ (l ^ 1) = 1}) :
    Module.finrank E (IntermediateField.extendScalars hEK) ∣ l - 1 := by
  have hl0 : 0 < l := hp.pos
  haveI : NeZero l := ⟨hp.ne_zero⟩
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  haveI : NeZero (l : E) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  haveI : Algebra.IsIntegral E Ω := ⟨fun x => (Algebra.IsIntegral.isIntegral (R := F) x).tower_top⟩

  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ l := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic l Ω)
      (Polynomial.degree_cyclotomic_pos l Ω hl0).ne'
    exact ⟨z, Polynomial.isRoot_cyclotomic_iff.mp hz⟩
  set M : IntermediateField E Ω := IntermediateField.adjoin E {ζ} with hM
  haveI hcyc : IsCyclotomicExtension {l} E M := by
    first
    | exact hζ.intermediateField_adjoin_isCyclotomicExtension E
    | exact hζ.intermediateField_adjoin_isCyclotomicExtension
    | exact IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension E hζ
  haveI : FiniteDimensional E M := by
    first
    | exact IntermediateField.adjoin.finiteDimensional (hζ.isIntegral hl0).tower_top
    | exact IsCyclotomicExtension.finiteDimensional {l} E M
  haveI : IsGalois E M := IsCyclotomicExtension.isGalois {l} E M

  have hcard : Module.finrank E M ∣ l - 1 := by
    have hμ := IsCyclotomicExtension.zeta_spec l E M
    have hinj := IsPrimitiveRoot.autToPow_injective E hμ
    have h1 : Nat.card (M ≃ₐ[E] M) ∣ Nat.card (ZMod l)ˣ := by
      rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card (M ≃ₐ[E] M) = Module.finrank E M := by
      first
      | exact IsGalois.card_aut_eq_finrank E M
      | (rw [Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank E M)
    have h3 : Nat.card (ZMod l)ˣ = l - 1 := by
      haveI : Fact l.Prime := ⟨hp⟩
      first
      | (rw [Nat.card_eq_fintype_card, ZMod.card_units])
      | (rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp])
    rw [← h2, ← h3]
    exact h1

  have hsup : E ⊔ IntermediateField.adjoin F {x : Ω | x ^ (l ^ 1) = 1} ≤ M.restrictScalars F := by
    apply sup_le
    · intro y hy
      rw [IntermediateField.mem_restrictScalars]
      exact M.algebraMap_mem ⟨y, hy⟩
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      have hy' : y ^ l = 1 := by simpa using hy
      have hζM : ζ ∈ M := IntermediateField.mem_adjoin_simple_self E ζ
      show y ∈ M.restrictScalars F
      rw [IntermediateField.mem_restrictScalars]
      first
      | (obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy'
         exact pow_mem hζM i)
      | (obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy' hl0
         exact pow_mem hζM i)
  have hKM : IntermediateField.extendScalars hEK ≤ M := by
    intro x hx
    rw [IntermediateField.mem_extendScalars] at hx
    exact (IntermediateField.mem_restrictScalars F).mp (hsup (hle hx))

  have hdvd : Module.finrank E (IntermediateField.extendScalars hEK) ∣ Module.finrank E M := by
    first
    | (have h := IntermediateField.relfinrank_mul_relfinrank
          (bot_le : (⊥ : IntermediateField E Ω) ≤ IntermediateField.extendScalars hEK) hKM
       rw [IntermediateField.relfinrank_bot_left, IntermediateField.relfinrank_bot_left] at h
       exact Dvd.intro _ h)
    | exact IntermediateField.finrank_dvd_of_le_right hKM
  exact hdvd.trans hcard

theorem dvdCondition : Formalism.MainNotions.N.Ln34.DvdStep := by
  intro l _ hl K LL hG
  have hle : K.1 ≤ Ks K 1 := hG.2.2.1
  have hEK : K0 K ≤ K.1 := inf_le_left
  haveI : CharZero (Om l) := charZero_of_injective_algebraMap (algebraMap ℚ_[l] (Om l)).injective
  have h := finrank_cyclotomicExt_dvd_sub_one (F := ℚ_[l]) (K0 K) K.1 hEK l (Fact.out) hle
  first
  | exact h
  | (show Module.finrank (K0 K) K.1 ∣ l - 1
     convert h using 1
     exact LinearEquiv.finrank_eq
       { toFun := fun y => ⟨y.1, y.2⟩
         invFun := fun y => ⟨y.1, y.2⟩
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl })

end Formalism.MainNotions.N.Ln34.DvdPf
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}
    (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)


open Classical in
def framepf_gco (x : ↥(NcS W T (c - 1))) : Fin Bs.r → PowerSeries O :=
  if h : ∃ g : Fin Bs.r → PowerSeries O, (x : W.DD T) = ∑ k, framepf_ι π' (c - 1) (g k) • Bs.b k
  then Classical.choose h else 0

include hπ0 hR2 in
theorem framepf_gco_spec (x : ↥(NcS W T (c - 1))) :
    (x : W.DD T) = ∑ k, framepf_ι π' (c - 1) (framepf_gco Bs π' c x k) • Bs.b k := by
  have h := framepf_coord Bs π' (c - 1) hπ0 hR2 x.2
  unfold framepf_gco
  rw [dite_eq_left h]
  exact Classical.choose_spec h

include hπ0 hΔπ hR2 γ0 in
theorem framepf_gco_eq (x : ↥(NcS W T (c - 1))) (g : Fin Bs.r → PowerSeries O)
    (hg : (x : W.DD T) = ∑ k, framepf_ι π' (c - 1) (g k) • Bs.b k) : framepf_gco Bs π' c x = g :=
  framepf_coord_uniq Bs π' (c - 1) hπ0 hΔπ hR2 γ0
    ((framepf_gco_spec Bs π' c hπ0 hR2 x).symm.trans hg)

include hπ0 in
theorem framepf_ι_C_mul (o : O) (g : PowerSeries O) :
    framepf_ι π' (c - 1) (PowerSeries.C o * g) = algebraMap O (LetA O n) o * framepf_ι π' (c - 1) g := by
  rw [framepf_ι_mul π' (c - 1) (hπ0 _), framepf_ι_C π' (c - 1) (hπ0 _), mul_comm (letE (c - 1)),
    mul_assoc, framepf_letE_ι π' (c - 1) hπ0]

def framepf_coordL : ↥(NcS W T (c - 1)) →ₗ[O] (Fin Bs.r → O) where
  toFun x := fun k => PowerSeries.constantCoeff (framepf_gco Bs π' c x k)
  map_add' x y := by
    have e : framepf_gco Bs π' c (x + y) = framepf_gco Bs π' c x + framepf_gco Bs π' c y := by
      apply framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0
      rw [Submodule.coe_add, framepf_gco_spec Bs π' c hπ0 hR2 x, framepf_gco_spec Bs π' c hπ0 hR2 y,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.add_apply, framepf_ι_add π' (c - 1) (hπ0 _), add_smul]
    funext k
    rw [e, Pi.add_apply, map_add (f := _)]
    rfl
  map_smul' o x := by
    have e : framepf_gco Bs π' c (o • x) = fun k => PowerSeries.C o * framepf_gco Bs π' c x k := by
      apply framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0
      rw [Submodule.coe_smul, framepf_gco_spec Bs π' c hπ0 hR2 x, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [framepf_ι_C_mul π' c hπ0, mul_smul, algebraMap_smul]
    funext k
    rw [e, map_mul, PowerSeries.constantCoeff_C]
    rfl

theorem framepf_coordL_apply (x : ↥(NcS W T (c - 1))) (k : Fin Bs.r) :
    framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0 x k = PowerSeries.constantCoeff (framepf_gco Bs π' c x k) := rfl

variable (hu : IsUnit (algebraMap (LetA O n) W.EE π'))


include hπ0 hΔπ hR2 γ0 hu in
theorem framepf_coordL_ker (x : ↥(NcS W T (c - 1))) :
    framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0 x = 0 ↔ (x : W.DD T) ∈ PiNS W T π' 1 := by
  have hx := framepf_gco_spec Bs π' c hπ0 hR2 x
  have hxc := (mem_NcS W T (c - 1) x).1 x.2
  constructor
  · intro h0
    have hX : ∀ k, ∃ hk : PowerSeries O, framepf_gco Bs π' c x k = PowerSeries.X * hk := by
      intro k
      have := congrFun h0 k
      rw [framepf_coordL_apply] at this
      exact PowerSeries.X_dvd_iff.2 this
    choose hk hhk using hX
    rw [mem_PiNS]
    refine ⟨⟨∑ k, framepf_ι π' (c - 1) (hk k) • Bs.b k,
      Submodule.sum_mem _ fun k _ => (W.N T).smul_mem _ (Bs.mem k).1, ?_⟩, hxc.2.1⟩
    rw [pow_one, hx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hhk k, smul_smul, framepf_ι_mul π' (c - 1) (hπ0 _), framepf_ι_X π' (c - 1) (hπ0 _),
      mul_comm (letE (c - 1)) π', mul_assoc, framepf_letE_ι π' (c - 1) hπ0]
  · intro h
    obtain ⟨⟨d, hdN, hd⟩, -⟩ := (mem_PiNS W T π' 1 _).1 h
    rw [pow_one] at hd
    have hdc : d ∈ NcS W T (c - 1) := by
      rw [mem_NcS]
      refine ⟨hdN, fun δ hδ => ?_, ?_⟩
      · rw [← sub_eq_zero]
        apply gradNPf_tf W T π' hu
        rw [smul_sub, ← hΔπ δ hδ, ← gradNPf_γD_smul, hΔπ δ hδ, hd, hxc.2.1 δ hδ, sub_self]
      · rw [← sub_eq_zero]
        apply gradNPf_tf W T π' hu
        rw [smul_sub, smul_smul, mul_comm, ← smul_smul, hd, hxc.2.2, sub_self]
    have hdd := framepf_gco_spec Bs π' c hπ0 hR2 ⟨d, hdc⟩
    have e : framepf_gco Bs π' c x = fun k => PowerSeries.X * framepf_gco Bs π' c ⟨d, hdc⟩ k := by
      apply framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0
      rw [← hd]
      conv_lhs => rw [show d = ((⟨d, hdc⟩ : ↥(NcS W T (c - 1))) : W.DD T) from rfl, hdd]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, framepf_ι_mul π' (c - 1) (hπ0 _), framepf_ι_X π' (c - 1) (hπ0 _),
        mul_comm (letE (c - 1)) π', mul_assoc, framepf_letE_ι π' (c - 1) hπ0]
    funext k
    rw [framepf_coordL_apply, e]
    simp

include hπ0 hΔπ hR2 γ0 in
theorem framepf_coordL_surj : Function.Surjective (framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0) := by
  intro o
  have hmem : ∑ k, framepf_ι π' (c - 1) (PowerSeries.C (o k)) • Bs.b k ∈ NcS W T (c - 1) := by
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [framepf_ι_C π' (c - 1) (hπ0 _), mul_comm, mul_smul, algebraMap_smul]
    exact (NcS W T (c - 1)).smul_mem _ (framepf_letE_mem Bs (c - 1) k)
  refine ⟨⟨_, hmem⟩, ?_⟩
  have e := framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0 ⟨_, hmem⟩ (fun k => PowerSeries.C (o k)) rfl
  funext k
  rw [framepf_coordL_apply, e, PowerSeries.constantCoeff_C]

def framepf_Lbas : LcQ W T π' c ≃ₗ[O] (Fin Bs.r → O) :=
  (Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_ker,
      framepf_coordL_ker Bs π' c hπ0 hΔπ hR2 γ0 hu])).trans
    (LinearMap.quotKerEquivOfSurjective _ (framepf_coordL_surj Bs π' c hπ0 hΔπ hR2 γ0))

theorem framepf_Lbas_mk (x : ↥(NcS W T (c - 1))) :
    framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu (Submodule.Quotient.mk x) =
      framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0 x := rfl

def framepf_hh (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) : LcQ W T π' c →ₗ[O] W.DD T :=
  (Fintype.linearCombination O (fun k => framepf_vec Bs π' (c - 1) H k)).comp
    (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu).toLinearMap

end Local

end Formalism.MainNotions.N.Ln34

end
end
