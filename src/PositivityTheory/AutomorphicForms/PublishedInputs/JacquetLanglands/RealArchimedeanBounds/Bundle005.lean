module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import GroundTheory.GlobalFields.Adele.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

namespace LatticeCountingLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def box (r : ℝ) : Set F := {t : F | IsIntegral ℤ t ∧ ∀ v : InfinitePlace F, v t ≤ r}

theorem place_eq (v : InfinitePlace F) (t : F) : v t = |sg v t| := by
  rw [← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal v), Real.norm_eq_abs]

theorem det_r {c : Pl F → ℕ} (χ : Hc c →* ℂˣ) (v : InfinitePlace F) (g : GL (Fin 2) F) :
    ((mkDat c χ).r v g).val.det = sg v g.val.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul]
  rfl

theorem bnd (v : InfinitePlace F) (N : ℕ) (x : F) {b : ℝ} (h : |sg v x| ≤ b) : v ((N : F) * x) ≤ N * b := by
  rw [place_eq, map_mul, map_natCast, abs_mul, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

end LatticeCountingLemmas

open LatticeCountingLemmas in
theorem dCnt : DScale → DBox → DEntry → DCnt := by
  intro hS hB hE F _ _ _ cc hcc χ ω δ C c hδ hc
  classical
  obtain ⟨N, C0, hN, hC0, hg⟩ := hS F cc hcc χ ω
  obtain ⟨CB, hCB⟩ := hB F
  obtain ⟨B, hBd⟩ := hE δ (max C C0) c hδ hc
  choose gg hgg using hg
  have ha : 0 ≤ (N : ℝ) * max B 0 := by positivity
  have hCB0 : 0 ≤ CB := by
    have h0 : ((box (F := F) 0).ncard : ℝ) ≤ CB * (1 + 0 ^ Fintype.card (InfinitePlace F)) := (hCB 0 le_rfl).2
    have h1 : (0 : ℝ) < 1 + 0 ^ Fintype.card (InfinitePlace F) := by positivity
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg h1
    linarith [Nat.cast_nonneg (α := ℝ) (box (F := F) 0).ncard]
  refine ⟨(CB * (1 + ((N : ℝ) * max B 0) ^ Fintype.card (InfinitePlace F))) ^ 3 * CB *
    (1 + ((N : ℝ) * max B 0 * C * C) ^ Fintype.card (InfinitePlace F)), fun z hz => ?_⟩
  obtain ⟨v0⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hz v0).1
  have hR : 0 ≤ (N : ℝ) * max B 0 * C * |(z v0).1.im| := by positivity
  let f : PG F → F × F × F × F := fun γ => if h : γ • ω = ω then
    ((N : F) * gg γ h 1 0, (N : F) * gg γ h 0 0, (N : F) * gg γ h 1 1, (N : F) * gg γ h 0 1) else 0
  have hinj : Set.InjOn f {γ : PG F | γ • ω = ω ∧ Near δ z (γ • z)} := by
    intro γ1 h1 γ2 h2 he
    simp only [f, dif_pos h1.1, dif_pos h2.1, Prod.mk.injEq] at he
    obtain ⟨e1, e2, e3, e4⟩ := he
    have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN
    have hgeq : gg γ1 h1.1 = gg γ2 h2.1 := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact mul_left_cancel₀ hN' e2
      · exact mul_left_cancel₀ hN' e4
      · exact mul_left_cancel₀ hN' e1
      · exact mul_left_cancel₀ hN' e3
    calc γ1 = (gg γ1 h1.1 : PG F) := (hgg γ1 h1.1).1.symm
      _ = (gg γ2 h2.1 : PG F) := by rw [hgeq]
      _ = γ2 := (hgg γ2 h2.1).1
  have hmaps : f '' {γ : PG F | γ • ω = ω ∧ Near δ z (γ • z)} ⊆
      box ((N : ℝ) * max B 0) ×ˢ box ((N : ℝ) * max B 0) ×ˢ box ((N : ℝ) * max B 0) ×ˢ
        box ((N : ℝ) * max B 0 * C * |(z v0).1.im|) := by
    rintro _ ⟨γ, ⟨hgω, hnear⟩, rfl⟩
    obtain ⟨hgγ, hint, hdet⟩ := hgg γ hgω
    simp only [f, dif_pos hgω]
    generalize gg γ hgω = g at hgγ hint hdet ⊢
    have hE' : ∀ v, |(mkDat cc χ).r v g 1 0| ≤ B ∧ |(mkDat cc χ).r v g 0 0| ≤ B ∧ |(mkDat cc χ).r v g 1 1| ≤ B ∧
        |(mkDat cc χ).r v g 0 1| ≤ B * |(z v).1.im| := by
      intro v
      have hv := hnear v
      rw [← hgγ] at hv
      exact hBd ((mkDat cc χ).r v g) (z v) ((hz v).1.trans (le_max_left _ _)) (hz v).2.1
        (by rw [det_r]; exact (hdet v).2.trans (le_max_right _ _)) hv
    have hB3 : ∀ v i j, |(mkDat cc χ).r v g i j| ≤ B → v ((N : F) * g i j) ≤ (N : ℝ) * max B 0 := fun v i j h =>
      bnd v N (g i j) (h.trans (le_max_left _ _))
    have hB4 : ∀ v : InfinitePlace F, v ((N : F) * g 0 1) ≤ (N : ℝ) * max B 0 * C * |(z v0).1.im| := fun v => by
      have h1 : |(mkDat cc χ).r v g 0 1| ≤ max B 0 * (C * |(z v0).1.im|) :=
        (hE' v).2.2.2.trans (mul_le_mul (le_max_left _ _) ((hz v).2.2 v0) (abs_nonneg _) (le_max_right _ _))
      refine (bnd v N (g 0 1) h1).trans (le_of_eq ?_)
      ring
    exact ⟨⟨hint 1 0, fun v => hB3 v 1 0 (hE' v).1⟩, ⟨hint 0 0, fun v => hB3 v 0 0 (hE' v).2.1⟩,
      ⟨hint 1 1, fun v => hB3 v 1 1 (hE' v).2.2.1⟩, ⟨hint 0 1, hB4⟩⟩
  have hfin := (hCB _ ha).1.prod ((hCB _ ha).1.prod ((hCB _ ha).1.prod (hCB _ hR).1))
  refine ⟨Set.Finite.of_finite_image (hfin.subset hmaps) hinj, ?_⟩
  have hle := Set.ncard_le_ncard hmaps hfin
  rw [hinj.ncard_image, Set.ncard_prod, Set.ncard_prod, Set.ncard_prod] at hle
  have h1 : ((box (F := F) ((N : ℝ) * max B 0)).ncard : ℝ) ≤ CB * (1 + ((N : ℝ) * max B 0) ^ Fintype.card (InfinitePlace F)) :=
    (hCB _ ha).2
  have h4 : ((box (F := F) ((N : ℝ) * max B 0 * C * |(z v0).1.im|)).ncard : ℝ) ≤
      CB * (1 + ((N : ℝ) * max B 0 * C * |(z v0).1.im|) ^ Fintype.card (InfinitePlace F)) := (hCB _ hR).2
  have hP : 0 ≤ ∏ v, |(z v).1.im| := Finset.prod_nonneg fun _ _ => abs_nonneg _
  have hprod : |(z v0).1.im| ^ Fintype.card (InfinitePlace F) ≤ C ^ Fintype.card (InfinitePlace F) * ∏ v, |(z v).1.im| := by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ => |(z v0).1.im|) (g := fun v => C * |(z v).1.im|)
      (fun _ _ => abs_nonneg _) (fun v _ => (hz v0).2.2 v)
    rwa [Finset.prod_const, Finset.card_univ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at this
  have hRd : ((N : ℝ) * max B 0 * C * |(z v0).1.im|) ^ Fintype.card (InfinitePlace F) ≤
      ((N : ℝ) * max B 0 * C * C) ^ Fintype.card (InfinitePlace F) * ∏ v, |(z v).1.im| := by
    calc _ = ((N : ℝ) * max B 0 * C) ^ Fintype.card (InfinitePlace F) * |(z v0).1.im| ^ Fintype.card (InfinitePlace F) :=
          mul_pow _ _ _
      _ ≤ ((N : ℝ) * max B 0 * C) ^ Fintype.card (InfinitePlace F) * (C ^ Fintype.card (InfinitePlace F) * ∏ v, |(z v).1.im|) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by ring
  have hX : 0 ≤ CB * (1 + ((N : ℝ) * max B 0) ^ Fintype.card (InfinitePlace F)) := mul_nonneg hCB0 (by positivity)
  have hM : 0 ≤ ((N : ℝ) * max B 0 * C * C) ^ Fintype.card (InfinitePlace F) := by positivity
  have h4' : ((box (F := F) ((N : ℝ) * max B 0 * C * |(z v0).1.im|)).ncard : ℝ) ≤
      CB * ((1 + ((N : ℝ) * max B 0 * C * C) ^ Fintype.card (InfinitePlace F)) * (1 + ∏ v, |(z v).1.im|)) :=
    h4.trans (mul_le_mul_of_nonneg_left (by nlinarith) hCB0)
  have hle' : (({γ : PG F | γ • ω = ω ∧ Near δ z (γ • z)}.ncard : ℕ) : ℝ) ≤
      ((box (F := F) ((N : ℝ) * max B 0)).ncard : ℝ) * (((box (F := F) ((N : ℝ) * max B 0)).ncard : ℝ) *
        (((box (F := F) ((N : ℝ) * max B 0)).ncard : ℝ) * ((box (F := F) ((N : ℝ) * max B 0 * C * |(z v0).1.im|)).ncard : ℝ))) := by
    exact_mod_cast hle
  refine hle'.trans ((mul_le_mul h1 (mul_le_mul h1 (mul_le_mul h1 h4' (Nat.cast_nonneg _) hX) (by positivity) hX)
    (by positivity) hX).trans_eq (by ring))
end Esk
end UpperTheory
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aTrans : ATrans := by
  intro F _ _ _
  classical
  let b := mixedEmbedding.latticeBasis F
  refine ⟨(∑ i, ‖b i‖) + 1, by positivity, fun x => ?_⟩
  let p : mixedEmbedding.mixedSpace F := (fun w => x w.1, 0)
  have hm : (ZSpan.floor b p : mixedEmbedding.mixedSpace F) ∈
      Submodule.span ℤ (Set.range b) := (ZSpan.floor b p).2
  rw [mixedEmbedding.mem_span_latticeBasis] at hm
  obtain ⟨s, hs⟩ := hm
  refine ⟨-(s : F), (RingOfIntegers.isIntegral_coe s).neg, fun v => ?_⟩
  have h1 := ZSpan.norm_fract_le b p
  have h2 : (ZSpan.fract b p).1 ⟨v, IsTotallyReal.isReal v⟩ = x v + sg v (-(s : F)) := by
    rw [ZSpan.fract_apply, ← hs]
    simp [p, sg, sub_eq_add_neg]
  have h3 : ‖(ZSpan.fract b p).1 ⟨v, IsTotallyReal.isReal v⟩‖ ≤ ‖ZSpan.fract b p‖ :=
    (norm_le_pi_norm _ _).trans (norm_fst_le _)
  rw [h2, Real.norm_eq_abs] at h3
  linarith

end UpperTheory.Esk
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.CompactSubgroupMembership

variable {F : Type} [Field F] [NumberField F]

def mP (w : Pl F) (c : ℕ) : AddSubgroup (w.adicCompletion F) :=
  (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c).toAddSubgroup.map
    (w.adicCompletionIntegers F).subtype.toAddMonoidHom

theorem mem_parahoricTimesPrincipalCongruence_iff {w : Pl F} {c : ℕ} {g : GL (Fin 2) (w.adicCompletion F)} :
    g ∈ K1 w c ↔ (∀ a b, g a b ∈ w.adicCompletionIntegers F) ∧
      (∀ a b, (g⁻¹ : GL (Fin 2) (w.adicCompletion F)) a b ∈ w.adicCompletionIntegers F) ∧
      g 1 0 ∈ mP w c ∧ g 1 1 - 1 ∈ mP w c := by
  have key : ∀ k : GL (Fin 2) (w.adicCompletionIntegers F),
      k ∈ ((mirab _).comap (Matrix.GeneralLinearGroup.map (n := Fin 2)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)))) ↔
      k 1 0 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c ∧
        k 1 1 - 1 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c := fun k => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq, map_one]
    change ![0, 1] ᵥ* _ = ![0, 1] ↔ _
    rw [funext_iff, Fin.forall_fin_two]
    simp [Matrix.vecMul, dotProduct]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h1, h2⟩ := (key k).1 hk
    refine ⟨fun a b => (k a b).2, fun a b => ?_, ⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩⟩
    rw [← map_inv]; exact ((k⁻¹ : GL (Fin 2) (w.adicCompletionIntegers F)) a b).2
  · rintro ⟨ha, hb, ⟨y, hy, e⟩, ⟨y', hy', e'⟩⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin 2) (w.adicCompletionIntegers F).subtype) := fun x y h =>
      Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
    let k : GL (Fin 2) (w.adicCompletionIntegers F) :=
      ⟨Matrix.of fun a b => ⟨g a b, ha a b⟩, Matrix.of fun a b => ⟨(g⁻¹ : GL (Fin 2) (w.adicCompletion F)) a b, hb a b⟩,
        inj (by rw [map_mul, map_one]; exact g.mul_inv), inj (by rw [map_mul, map_one]; exact g.inv_mul)⟩
    refine ⟨k, (key k).2 ⟨?_, ?_⟩, Units.ext rfl⟩
    · rw [show k 1 0 = y from Subtype.ext e.symm]; exact hy
    · rw [show k 1 1 - 1 = y' from Subtype.ext e'.symm]; exact hy'

theorem mem_mP_zero {w : Pl F} {x : w.adicCompletion F} (hx : x ∈ w.adicCompletionIntegers F) : x ∈ mP w 0 :=
  ⟨⟨x, hx⟩, by simp, rfl⟩

theorem mem_O {x : Af F} : x ∈ Ohat F ↔ ∀ w : Pl F, pLoc F w x ∈ w.adicCompletionIntegers F := by
  simp [Ohat, Subring.mem_iInf]

theorem mem_Ov {x : Af F} : x ∈ Ohat F ↔ ∀ w : Pl F, Valued.v (pLoc F w x) ≤ 1 := by
  rw [mem_O]; simp only [HeightOneSpectrum.mem_adicCompletionIntegers]

theorem v_le {x : Af F} (hx : x ∈ Ohat F) (w : Pl F) : Valued.v (pLoc F w x) ≤ 1 := mem_Ov.1 hx w

theorem integral_transvection_mem_slIntegers_conjugate_zero {g : GF F} :
    g ∈ K0 F ↔ (∀ i j, g.val i j ∈ Ohat F) ∧ ∀ i j, (g⁻¹ : GF F).val i j ∈ Ohat F := by
  simp only [K0, Kc, Subgroup.mem_iInf, Subgroup.mem_comap, mem_parahoricTimesPrincipalCongruence_iff, ← map_inv, mem_O]
  constructor
  · intro h
    exact ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2.1 i j⟩
  · rintro ⟨h1, h2⟩ w
    exact ⟨fun i j => h1 i j w, fun i j => h2 i j w, mem_mP_zero (h1 1 0 w),
      mem_mP_zero (sub_mem (h1 1 1 w) (one_mem _))⟩

theorem Kc_le (c : Pl F → ℕ) : Kc c ≤ K0 F := fun g hg => by
  rw [integral_transvection_mem_slIntegers_conjugate_zero]
  simp only [Kc, Subgroup.mem_iInf, Subgroup.mem_comap, mem_parahoricTimesPrincipalCongruence_iff, ← map_inv] at hg
  exact ⟨fun i j => mem_O.2 fun w => (hg w).1 i j, fun i j => mem_O.2 fun w => (hg w).2.1 i j⟩

theorem zc_normal : ((zc F).range).Normal :=
  ⟨fun n hn g => by
    obtain ⟨z, rfl⟩ := hn
    have := Subgroup.mem_center_iff.1 (zc_center z) g
    exact ⟨z, by rw [this, mul_inv_cancel_right]⟩⟩

theorem mem_Hc (c : Pl F → ℕ) (h : GF F) : h ∈ Hc c ↔ ∃ k ∈ Kc c, ∃ z, h = k * zc F z := by
  have := zc_normal (F := F)
  change h ∈ Kc c ⊔ (zc F).range ↔ _
  rw [Subgroup.mem_sup_of_normal_right]
  constructor
  · rintro ⟨k, hk, _, ⟨z, rfl⟩, rfl⟩
    exact ⟨k, hk, z, rfl⟩
  · rintro ⟨k, hk, z, rfl⟩
    exact ⟨k, hk, _, ⟨z, rfl⟩, rfl⟩

theorem det_mem {g : GF F} (h : ∀ i j, g.val i j ∈ Ohat F) : g.val.det ∈ Ohat F := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (h 0 0) (h 1 1)) (mul_mem (h 0 1) (h 1 0))

theorem k_prop {k : GF F} (hk : k ∈ K0 F) (w : Pl F) :
    Valued.v (pLoc F w ((Matrix.GeneralLinearGroup.det k : (Af F)ˣ) : Af F)) = 1 ∧
      max (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) = 1 := by
  obtain ⟨h1, h2⟩ := integral_transvection_mem_slIntegers_conjugate_zero.1 hk
  refine ⟨?_, ?_⟩
  · have hd2 := v_le (det_mem h2) w
    have hdd : k.val.det * (k⁻¹ : GF F).val.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    have e1 : Valued.v (pLoc F w k.val.det) * Valued.v (pLoc F w (k⁻¹ : GF F).val.det) = 1 := by
      rw [← map_mul, ← map_mul, hdd, map_one, map_one]
    change Valued.v (pLoc F w k.val.det) = 1
    exact le_antisymm (v_le (det_mem h1) w) (e1 ▸ mul_le_of_le_one_right' hd2)
  · have e : k.val 1 0 * (k⁻¹ : GF F).val 0 1 + k.val 1 1 * (k⁻¹ : GF F).val 1 1 = 1 := by
      have := congrFun (congrFun (Units.mul_inv k) 1) 1
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at this
      exact this
    have hv : Valued.v (pLoc F w (k.val 1 0) * pLoc F w ((k⁻¹ : GF F).val 0 1) +
        pLoc F w (k.val 1 1) * pLoc F w ((k⁻¹ : GF F).val 1 1)) = 1 := by
      rw [← map_mul, ← map_mul, ← map_add (f := _), e, map_one, map_one]
    refine le_antisymm (max_le (v_le (h1 1 0) w) (v_le (h1 1 1) w)) ?_
    refine hv.ge.trans ((Valuation.map_add _ _ _).trans (max_le_max ?_ ?_))
    · rw [map_mul]; exact mul_le_of_le_one_right' (v_le (h2 0 1) w)
    · rw [map_mul]; exact mul_le_of_le_one_right' (v_le (h2 1 1) w)

theorem val_pLoc (w : Pl F) (x : F) :
    Valued.v (pLoc F w (algebraMap F (Af F) x)) = w.valuation F x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem int_iff (t : F) : IsIntegral ℤ t ↔ algebraMap F (Af F) t ∈ Ohat F := by
  rw [mem_Ov]
  simp only [val_pLoc]
  constructor
  · intro h w
    exact HeightOneSpectrum.valuation_le_one w (⟨t, h⟩ : 𝓞 F)
  · intro h
    obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F t h
    exact RingOfIntegers.isIntegral_coe r

theorem af_den (a : Af F) : ∃ n : ℕ, n ≠ 0 ∧ (n : Af F) * a ∈ Ohat F := by
  have hU : IsOpen {z : Af F | a - z ∈ Ohat F} :=
    isOpen_Ohat.preimage (f := fun z : Af F => a - z) (by fun_prop)
  obtain ⟨x, hx⟩ := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).exists_mem_open hU
    ⟨a, by simp⟩
  obtain ⟨m, hm0, hm⟩ :=
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm0, ?_⟩
  have h1 : algebraMap F (Af F) (m • x) ∈ Ohat F :=
    mem_Ohat.2 (GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles F ⟨_, hm⟩)
  have h2 := add_mem h1 (mul_mem (intCast_mem (Ohat F) m) hx)
  have h3 : (m : Af F) * a ∈ Ohat F := by
    convert h2 using 1
    rw [zsmul_eq_mul, map_mul, map_intCast]; ring
  rcases Int.natAbs_eq m with h | h
  · rw [h] at h3; simpa using h3
  · rw [h] at h3; simpa using neg_mem h3

theorem den_ex (g : GF F) : ∃ N : ℕ, N ≠ 0 ∧ ∀ i j, (N : Af F) * g.val i j ∈ Ohat F := by
  choose n hn0 hn using fun p : Fin 2 × Fin 2 => af_den (g.val p.1 p.2)
  refine ⟨∏ p, n p, Finset.prod_ne_zero_iff.2 fun p _ => hn0 p, fun i j => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (i, j))
  rw [hk, Nat.cast_mul, mul_comm ((n (i, j) : ℕ) : Af F), mul_assoc]
  exact mul_mem (natCast_mem _ k) (hn (i, j))

theorem unit_scalar_mem_maximal_compact {u : (Af F)ˣ} (hu : ∀ w : Pl F, Valued.v (pLoc F w (u : Af F)) = 1) :
    zc F u ∈ K0 F ∧ ∀ t ∈ Ohat F, aff u t ∈ K0 F := by
  have hu1 : (u : Af F) ∈ Ohat F := mem_Ov.2 fun w => (hu w).le
  have hu2 : ((u⁻¹ : (Af F)ˣ) : Af F) ∈ Ohat F := by
    refine mem_Ov.2 fun w => ?_
    have : Valued.v (pLoc F w (u : Af F)) * Valued.v (pLoc F w ((u⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    rw [hu w, one_mul] at this
    exact this.le
  refine ⟨integral_transvection_mem_slIntegers_conjugate_zero.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun t ht => integral_transvection_mem_slIntegers_conjugate_zero.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · fin_cases i <;> fin_cases j <;> simp [zc, hu1]
  · rw [show (zc F u)⁻¹ = zc F u⁻¹ from (map_inv (zc F) u).symm]
    fin_cases i <;> fin_cases j <;> simp [-map_inv, zc, hu2]
  · change (!![(u : Af F), t; 0, 1] : Matrix (Fin 2) (Fin 2) (Af F)) i j ∈ Ohat F
    fin_cases i <;> fin_cases j <;> simp [hu1, ht]
  · change (!![((u⁻¹ : (Af F)ˣ) : Af F), -(((u⁻¹ : (Af F)ˣ) : Af F) * t); 0, 1] : Matrix (Fin 2) (Fin 2) (Af F)) i j ∈
      Ohat F
    fin_cases i <;> fin_cases j <;> simp [hu2, mul_mem hu2 ht]

end UpperTheory.Esk.CompactSubgroupMembership

open UpperTheory.Esk.CompactSubgroupMembership in
theorem UpperTheory.Esk.aMem : UpperTheory.Esk.AMem := by
  intro F _ _
  exact ⟨fun g => integral_transvection_mem_slIntegers_conjugate_zero, fun x => mem_Ov, Kc_le, mem_Hc, fun k hk w => k_prop hk w, int_iff, den_ex,
    fun u hu => unit_scalar_mem_maximal_compact hu⟩
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aAdd : AMem → AAdd := by
  intro _ F _ _ t u
  have hU : IsOpen {z : Af F | ((t⁻¹ : (Af F)ˣ) : Af F) * (u - z) ∈ Ohat F} :=
    isOpen_Ohat.preimage (by fun_prop)
  obtain ⟨y, hy⟩ := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).exists_mem_open hU
    ⟨u, by simp⟩
  exact ⟨y, hy⟩

end UpperTheory.Esk
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HeightProductFormula

theorem reAt_eq {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    reAt v x = sg v x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

theorem rowF_apply {F : Type} [Field F] [NumberField F] (s : Fin 2 → F) (x : GF F) (i : Fin 2) :
    rowF s x i = algebraMap F (Af F) (s 0) * x.val 0 i + algebraMap F (Af F) (s 1) * x.val 1 i := by
  simp [rowF, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem det_id {F : Type} [Field F] [NumberField F] (s s' : Fin 2 → F) (x : GF F) :
    algebraMap F (Af F) (s 0 * s' 1 - s 1 * s' 0) * (Matrix.GeneralLinearGroup.det x : Af F) =
      rowF s x 0 * rowF s' x 1 - rowF s x 1 * rowF s' x 0 := by
  rw [rowF_apply, rowF_apply, rowF_apply, rowF_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [map_sub, map_mul]
  ring

end UpperTheory.Esk.HeightProductFormula

namespace UpperTheory.Esk

open HeightProductFormula in
theorem dProd : AMem → AMono → ARow → DProd := by
  intro hM hMo hR F _ _ _ c _ χ s s' hΔ x
  obtain ⟨hpos, hmul, -, hprod⟩ := UpperTheory.V.Sd.Hm.absf F
  have hs : s ≠ 0 := fun h => hΔ (by simp [h])
  have hs' : s' ≠ 0 := fun h => hΔ (by simp [h])
  obtain ⟨t, k, hk, ht⟩ := (hR F s x).1 hs
  obtain ⟨t', k', hk', ht'⟩ := (hR F s' x).1 hs'
  have hn : nF s x = absF t := (hR F s x).2 t k hk ht
  have hn' : nF s' x = absF t' := (hR F s' x).2 t' k' hk' ht'
  obtain ⟨hK, hO, -⟩ := hM F
  have hle : ∀ (g : GF F), g ∈ K0 F → ∀ i j (w : Pl F), Valued.v (pLoc F w (g.val i j)) ≤ 1 :=
    fun g hg i j w => (hO _).1 (((hK g).1 hg).1 i j) w
  set Δ := s 0 * s' 1 - s 1 * s' 0 with hΔd
  set U1 : (Af F)ˣ := ratU F (Units.mk0 Δ hΔ) * Matrix.GeneralLinearGroup.det x
  have key : absF U1 ≤ absF (t * t') := by
    refine hMo F _ _ fun w => ?_
    have e : (U1 : Af F) = (t * t' : (Af F)ˣ) * (k.val 1 0 * k'.val 1 1 - k.val 1 1 * k'.val 1 0) := by
      change algebraMap F (Af F) Δ * (Matrix.GeneralLinearGroup.det x : Af F) = _
      rw [det_id, ht, ht, ht', ht', Units.val_mul]
      ring
    rw [e, map_mul, map_mul]
    have h1 : Valued.v (pLoc F w (k.val 1 0 * k'.val 1 1 - k.val 1 1 * k'.val 1 0)) ≤ 1 := by
      rw [map_sub, map_mul, map_mul]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
      · rw [map_mul]; exact mul_le_one' (hle k hk 1 0 w) (hle k' hk' 1 1 w)
      · rw [map_mul]; exact mul_le_one' (hle k hk 1 1 w) (hle k' hk' 1 0 w)
    calc _ ≤ Valued.v (pLoc F w ((t * t' : (Af F)ˣ) : Af F)) * 1 := mul_le_mul_right h1 _
      _ = _ := mul_one _
  have hU1 : absF U1 = absF (ratU F (Units.mk0 Δ hΔ)) * absF (Matrix.GeneralLinearGroup.det x) := hmul _ _
  have hP := hprod (Units.mk0 Δ hΔ)
  change (∏ v, |reAt v Δ|) * absF (ratU F (Units.mk0 Δ hΔ)) = 1 at hP
  simp only [reAt_eq] at hP
  change absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 * (absF (Matrix.GeneralLinearGroup.det x) / nF s' x ^ 2) ≤
    ∏ v, sg v Δ ^ 2
  rw [hn, hn']
  have hsq : ∏ v, sg v Δ ^ 2 = (∏ v, |sg v Δ|) ^ 2 := by
    rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun v _ => (sq_abs _).symm
  rw [hsq]
  set P := ∏ v, |sg v Δ|
  set R := absF (ratU F (Units.mk0 Δ hΔ))
  set A := absF (Matrix.GeneralLinearGroup.det x)
  have hA := hpos (Matrix.GeneralLinearGroup.det x)
  have hT := hpos t
  have hT' := hpos t'
  have hRp := hpos (ratU F (Units.mk0 Δ hΔ))
  have hPp : 0 ≤ P := Finset.prod_nonneg fun v _ => abs_nonneg _
  rw [hU1, hmul t t'] at key
  have hA2 : A ≤ absF t * absF t' * P := by
    have : A = P * (R * A) := by rw [← mul_assoc, hP, one_mul]
    rw [this, mul_comm (absF t * absF t') P]
    exact mul_le_mul_of_nonneg_left key hPp
  rw [div_mul_div_comm, div_le_iff₀ (by positivity), ← sq, ← mul_pow, ← mul_pow]
  exact pow_le_pow_left₀ hA.le (by linarith) 2

end UpperTheory.Esk
end
end
