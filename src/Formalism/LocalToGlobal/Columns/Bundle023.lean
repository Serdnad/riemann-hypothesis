module

public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Columns.CmUnramifiedOfFieldConditions
public import Formalism.LocalToGlobal.Columns.RecLevelSym
public import Formalism.LocalToGlobal.Columns.Bundle018
public import Formalism.LocalToGlobal.Columns.RecLevelDiv
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle006
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Formalism.LocalToGlobal.Columns.RecLevelLocF
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.Columns.RecLevelLocK
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
public import Formalism.LocalToGlobal.Columns.RecLevelTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP)

section CM

variable {X : Fields}

def fixedIntermediateField (hX : X.Ok) : IntermediateField X.F X.E where
  carrier := {x | star x = x}
  mul_mem' := by
    intro a b ha hb
    show star (a * b) = a * b
    rw [star_mul', ha, hb]
  add_mem' := by
    intro a b ha hb
    show star (a + b) = a + b
    rw [star_add, ha, hb]
  algebraMap_mem' := hX.star_F
  inv_mem' := by
    intro a ha
    show star a⁻¹ = a⁻¹
    rw [star_inv₀, ha]

theorem rlh_fixed (hX : X.Ok) (a : X.E) : star a = a ↔ a ∈ (algebraMap X.F X.E).range := by
  constructor
  · intro ha
    have hp : (Module.finrank X.F X.E).Prime := by rw [hX.rankE]; exact Nat.prime_two
    have := IntermediateField.isSimpleOrder_of_finrank_prime X.F X.E hp
    rcases eq_bot_or_eq_top (fixedIntermediateField hX) with h | h
    · have h1 : a ∈ fixedIntermediateField hX := ha
      rw [h, IntermediateField.mem_bot] at h1
      exact h1
    · exfalso
      have hall : ∀ x : X.E, star x = x := fun x => by
        have : x ∈ fixedIntermediateField hX := by rw [h]; exact IntermediateField.mem_top
        exact this
      obtain ⟨φ⟩ : Nonempty (X.E →+* ℂ) := inferInstance
      have hreal : NumberField.ComplexEmbedding.IsReal φ := by
        rw [NumberField.ComplexEmbedding.isReal_iff]
        ext x
        rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← hX.conjE, hall]
      have hc := hX.cplxE.isComplex (NumberField.InfinitePlace.mk φ)
      rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
      exact hc hreal
  · rintro ⟨x, rfl⟩
    exact hX.star_F x

theorem cmData_of_totallyRealFieldsConditions (hX : X.AbelianUnramifiedExtensionConditions) :
    Formalism.BasicNotions.CMData X.F X.E :=
  { cmUnram := cm_unramified_of_field_conditions hX
    totReal := hX.ok.realF
    deg2 := hX.ok.rankE
    fixed := rlh_fixed hX.ok }

end CM

section Split

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem rlh_conjP_conjP (P : Pl E) : conjPrime₂ (conjPrime₂ P) = P := by
  apply HeightOneSpectrum.ext
  ext x
  show cO E (cO E x) ∈ P.asIdeal ↔ x ∈ P.asIdeal
  rw [cO_cO]

end Split

section Primes

variable {X : Fields} {Pr : Primes X}


end Primes

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section FE

variable {X : Fields} {Pr : Primes X} {R : Ranks}

private theorem mulVec_eN_eq_of_mem_HPar {κ : Type} [CommRing κ] {n r k rS t s : ℕ} (hr : r ≤ n) (ht : 0 < t)
    (hn : n = r + s * t) (hkr : k < r) (hkrS : k + rS ≤ r) (M : GL (Fin n) κ)
    (hM : M ∈ HPar n κ hr (List.replicate s t) (HPsymF κ r k rS)) :
    (M : Matrix (Fin n) (Fin n) κ) *ᵥ Loc.eN κ n k = Loc.eN κ n k := by
  rw [mem_HPar_iff hr ht hn] at hM
  obtain ⟨hB, hS⟩ := hM
  rw [mem_HPsymF_iff hkrS] at hS
  obtain ⟨s1, s2, s3⟩ := hS
  have hv := upper_block_val_submatrix hr (blockTri_blkOf_le r t hB)
  rw [mem_blockTri] at hB
  have hkn : k < n := by omega
  have he : Loc.eN κ n k = Pi.single (⟨k, hkn⟩ : Fin n) 1 := by
    funext l
    simp only [Loc.eN, Pi.single_apply, Fin.ext_iff]
  rw [he, Matrix.mulVec_single_one]
  funext i
  simp only [Matrix.col_apply, Pi.single_apply]
  by_cases hir : (i : ℕ) < r
  · have key : ∀ a b : Fin r, ((upperLeftBlock hr M : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) a b =
        (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE hr a) (Fin.castLE hr b) := by
      intro a b
      rw [hv]
      rfl
    have hk' : (⟨k, hkn⟩ : Fin n) = Fin.castLE hr ⟨k, hkr⟩ := Fin.ext rfl
    rw [hk']
    by_cases hik : (i : ℕ) = k
    · have hi2 : i = Fin.castLE hr ⟨k, hkr⟩ := Fin.ext hik
      rw [if_pos hi2, hi2, ← key]
      exact s2 _
    · have hi' : i = Fin.castLE hr ⟨i, hir⟩ := Fin.ext rfl
      rw [if_neg (fun h => hik (by rw [h]; rfl)), hi', ← key]
      by_cases hrS : rS = 0
      · rcases Nat.lt_or_gt_of_ne hik with h | h
        · exact s3 _ _ h (by simp [hrS])
        · exact s1 _ _ (by simp only [symIdx, Fin.val_mk, hrS]; split_ifs <;> omega)
      · exact s1 _ _ (by simp only [symIdx, Fin.val_mk]; split_ifs <;> omega)
  · rw [if_neg (fun h => hir (by rw [h]; exact hkr))]
    exact hB _ _ (by
      simp only [blkOf, Fin.val_mk, if_pos hkr, if_neg hir]
      exact Nat.succ_pos _)

theorem fixE_colLevSym (Ch : Chars X Pr R.m) {m2 : ℕ} (hm : R.m = m2 + 2) : FixE (R := R) (colLevSym Ch) m2 := by
  intro h hh w
  have hw : h w ∈ (colLevSym Ch (m2 + 1) w).H := (Subgroup.mem_pi _).mp hh w (Set.mem_univ _)
  have e0 : ¬ (m2 + 1 = 0) := by omega
  have e1 : ¬ (m2 + 1 + 1 < R.m) := by omega
  have e2 : m2 + 1 + 1 = R.m := by omega
  unfold colLevSym at hw
  rw [if_neg e0, dite_eq_right e1, dite_eq_left e2] at hw
  exact mulVec_eN_eq_of_mem_HPar _ (by have := R.rank_add_five_le; omega)
    (by
      show R.k + (m2 + 1) * (R.t + 1) = R.k + R.m - 1 + (m2 + 1) * R.t
      rw [hm, Nat.mul_succ]
      omega)
    (by
      show R.k < R.k + R.m - 1
      have := R.two_le_m
      omega)
    (by
      show R.k + (R.m / 2 - 1) ≤ R.k + R.m - 1
      omega) _ hw

end FE

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section IntegralTwistedLevel

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E))

def kOneLastExponents (n c : ℕ) (l : ℕ) : ℤ := if l + 1 = n then (c : ℤ) else 0

def twistedLevelExponent (n c : ℕ) (l : ℕ) : ℤ := if l + 1 = n then 0 else (c : ℤ)

theorem scaledConstLattice_stable {n c : ℕ} {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ GLint E n P) {x : Sp E n}
    (hx : x ∈ LocE.sclLat P (qOf P) n (fun _ => (c : ℤ))) :
    g x ∈ LocE.sclLat P (qOf P) n (fun _ => (c : ℤ)) := by
  rw [ciMem_sclLat] at hx ⊢
  have hy : ((qOf P : E) ^ (c : ℤ))⁻¹ • x ∈ stdAt E n P := by
    rw [ciMem_stdAt]; intro l; simpa [Pi.smul_apply, smul_eq_mul] using hx l
  have h1 := (hg _).2 hy
  rw [map_smul, ciMem_stdAt] at h1
  intro l
  simpa [Pi.smul_apply, smul_eq_mul] using h1 l

def twK1H (n r c : ℕ) : Subgroup ↥(GLint E n P) where
  carrier := {g | (g : Sp E n ≃ₗ[E] Sp E n) ∈ LocE.JQ P (qOf P) r n 0 ∧
    (g : Sp E n ≃ₗ[E] Sp E n) ∈ stabL E n (LocE.sclLat P (qOf P) n (kOneLastExponents n c)) ∧
    (g : Sp E n ≃ₗ[E] Sp E n) ∈ stabL E n (LocE.sclLat P (qOf P) n (twistedLevelExponent n c)) ∧
    ∀ w ∈ LocE.sclLat P (qOf P) n (twistedLevelExponent n c), (g : Sp E n ≃ₗ[E] Sp E n) w - w ∈ LocE.sclLat P (qOf P) n (fun _ => (c : ℤ))}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, Subgroup.one_mem _, fun w _ => by
    show (1 : Sp E n ≃ₗ[E] Sp E n) w - w ∈ _
    rw [show (1 : Sp E n ≃ₗ[E] Sp E n) w = w from rfl, sub_self]; exact zero_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3, ha4⟩ ⟨hb1, hb2, hb3, hb4⟩
    refine ⟨Subgroup.mul_mem _ ha1 hb1, Subgroup.mul_mem _ ha2 hb2, Subgroup.mul_mem _ ha3 hb3, fun w hw => ?_⟩
    show (a : Sp E n ≃ₗ[E] Sp E n) ((b : Sp E n ≃ₗ[E] Sp E n) w) - w ∈ _
    have e : (a : Sp E n ≃ₗ[E] Sp E n) ((b : Sp E n ≃ₗ[E] Sp E n) w) - w =
        (a : Sp E n ≃ₗ[E] Sp E n) ((b : Sp E n ≃ₗ[E] Sp E n) w - w) + ((a : Sp E n ≃ₗ[E] Sp E n) w - w) := by
      rw [map_sub]; abel
    rw [e]
    exact add_mem (scaledConstLattice_stable P a.2 (hb4 w hw)) (ha4 w hw)
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3, ha4⟩
    refine ⟨Subgroup.inv_mem _ ha1, Subgroup.inv_mem _ ha2, Subgroup.inv_mem _ ha3, fun w hw => ?_⟩
    have e : ((a⁻¹ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) w - w =
        -(((a⁻¹ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) ((a : Sp E n ≃ₗ[E] Sp E n) w - w)) := by
      rw [map_sub]
      show _ = -((a : Sp E n ≃ₗ[E] Sp E n).symm _ - (a : Sp E n ≃ₗ[E] Sp E n).symm w)
      rw [LinearEquiv.symm_apply_apply]
      show (a : Sp E n ≃ₗ[E] Sp E n).symm w - w = _
      abel
    rw [e]
    exact neg_mem (scaledConstLattice_stable P (a⁻¹).2 (ha4 w hw))

theorem mem_R1_zero {n : ℕ} (g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)) : g ∈ Loc.R1 E n 0 := by
  have hc : ∀ r : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0), Loc.R1cond E n 0 r := fun r => by
    have hU : ∀ i (v : Sp E (n + 0)), v ∈ Loc.Ufl E n 0 i := fun i v l hl => absurd (show l.1 < n + i by have := l.2; omega) hl
    have he : Loc.eN E (n + 0) n = 0 := by
      funext l; unfold Loc.eN; rw [if_neg (by have := l.2; omega)]; rfl
    exact ⟨fun i v _ => hU i _, by rw [he, map_zero], fun i => hU i _⟩
  exact ⟨hc g, hc g⁻¹⟩

def kOneCharacter (n r c : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : ↥(twK1H P n r c) →* K where
  toFun g := LocE.lamQB ξ r n ((g : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n).toLinearMap
  map_one' := by
    obtain ⟨h1, h2⟩ := _root_.TwChrOne E K P (fun _ => 1) ξ r n 0 (fun _ _ => rfl)
    have hm : (1 : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)) ∈ Loc.Cbe (LocE.JQ P (qOf P) r n 0) 1 := Subgroup.one_mem _
    have a := h2 1 hm 1 hm 1 hm (fun _ => rfl)
    have b := h1 1 hm
    have e : PI.TwChrOne.ChiL P (fun _ => (1 : K)) ξ r n 0 1 1 = LocE.lamQB ξ r n (1 : Sp E n ≃ₗ[E] Sp E n).toLinearMap := by
      unfold PI.TwChrOne.ChiL; simp only [inv_one, one_mul, mul_one]; rfl
    rw [e] at a b
    show LocE.lamQB ξ r n (1 : Sp E n ≃ₗ[E] Sp E n).toLinearMap = 1
    exact (mul_left_cancel₀ b ((mul_one _).trans a)).symm
  map_mul' g g' := by
    obtain ⟨-, h2⟩ := _root_.TwChrOne E K P (fun _ => 1) ξ r n 0 (fun _ _ => rfl)
    have hC : ∀ x : ↥(twK1H P n r c), ((x : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) ∈ Loc.Cbe (LocE.JQ P (qOf P) r n 0) 1 :=
      fun x => ⟨mem_R1_zero _, by
        show (MulAut.conj (1 : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0))⁻¹) _ ∈ _
        rw [inv_one, map_one]; exact x.2.1⟩
    have a := h2 _ (hC g) _ (hC g') _ (hC (g * g')) (fun _ => rfl)
    have e : ∀ y : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0), PI.TwChrOne.ChiL P (fun _ => (1 : K)) ξ r n 0 1 y = LocE.lamQB ξ r n y.toLinearMap :=
      fun y => by unfold PI.TwChrOne.ChiL; simp only [inv_one, one_mul, mul_one]; rfl
    rw [e, e, e] at a
    exact a

def kOneLevel (n r c : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LevI E K n P :=
  ⟨twK1H P n r c, (kOneCharacter P n r c ξ).toHomUnits⟩

end IntegralTwistedLevel

section TwTop

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def twTopDepth (R : Ranks) : ℕ := 4 * R.m + 1

def twLt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs := colLevSym Ch

def twTt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)) := fun j P =>
  kOneLevel P.1 (R.N j) R.r (twTopDepth R) (resChar (mu : Chr X.F X.E X.K) P.1)


end TwTop

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG : Finset (Pl E)} (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)))
  {π : 𝓞 E} {T f : ℕ}

def stepOf (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal)
    (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG)
    (hidx : (baseLb E n ST).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f))
    (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG (E := E) (n := n) (SG := SG))) →* ℂˣ) :
    Formalism.L2.Forms.StepLevel F E hc.sig (1 : Matrix (Fin n) (Fin n) E) T f (plUnder F SG) where
  Lb := baseLb E n ST
  Lb_fin := baseLb_fin n ST
  Lb_span := baseLb_span n ST
  Lb_int := baseLb_int hc n ST
  Lb_dual := baseLb_dual hc n ST (fun P hP => (hST P).1 hP) hTπ
  Lb_index := hidx
  Uloc := levLoc hc n ST SG (Subgroup.pi Set.univ Hw)
  Uloc_le := levLoc_le hc n ST SG _
  Uloc_lev := levLoc_le_levelVL hc n ST SG _
  Uloc_hyp v hv hT := levLoc_eq_levelVL hc n ST SG _ v
    (fun h => hT ((mem_plUnder_iff_norm hc hST T hTπ v).1 h)) hv
  fM v _ := fMod hc n ST v
  fT v _ := fLoc hc n ST v
  fT_ne v h := fLoc_ne hc n v hB ((mem_plUnder_iff_norm hc hST T hTπ v).2 h)
  fT_T v _ x := fLoc_natCast_smul_eq_zero_of_dvd hc n v hB T ⟨cO E π, hTπ.symm⟩ x
  fM_card v h := by
    obtain ⟨P, hP, hov⟩ := (mem_plUnder_iff_norm hc hST T hTπ v).2 h
    rw [fMod_card hc n v hB hP hov (hB.over_unique hc hP hov), hcard P hP]
  fT_L v _ x hx := fLoc_L hc n v x hx
  UlocAlt v h := levLoc_eq_stabFun hc n SG _ v hB (hSG v h)
  U := levU hc n ST SG (Subgroup.pi Set.univ Hw)
  U_eq x := levU_eq_prod hc n ST SG Hw x
  U_compact := levU_compact hc n ST SG _
  U_open := levU_open hc n ST SG _
  chi := levTyp lam
  chi_triv x h := levTyp_eq_one hc n ST SG _ lam x h

end Gen

section Col

open Formalism.BasicNotions (Ranks)

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem rls_T_notUnder (hPr : Pr.Ok) (u : Pr.Word) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal) :
    v ∉ plUnder X.F Pr.vGs := by
  rintro ⟨w, hw, hov⟩
  apply T_notMem_vGs hPr u ⟨w, hw⟩
  have : (Pr.T u : 𝓞 X.F) ∈ w.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := hov ▸ h
  rwa [Ideal.mem_comap, map_natCast] at this

theorem rls_vT_iff (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (P : Pl X.E) : P ∈ Pr.vT u ↔ Pr.piT u ∈ P.asIdeal :=
  mem_divs (basePi_of_ok hX hPr u).ne_zero P

end Col

end Formalism.L2.Col
end
end
