module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ThetaDiag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

section aux

variable {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] (Φ : OddForm B N)

private theorem ev_alg (b : B) : (algebraMap B Φ.Ext b).ev = b := by
  rw [Algebra.algebraMap_eq_smul_one, OddForm.ev_smul, OddForm.ev_one, mul_one]

private theorem od_alg (b : B) : (algebraMap B Φ.Ext b).od = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, OddForm.od_smul, OddForm.od_one, smul_zero]

private theorem mem_one_iff (z : Φ.Ext) : z ∈ (1 : Submodule B Φ.Ext) ↔ z.od = 0 := by
  rw [Submodule.mem_one]
  refine ⟨?_, fun h => ⟨z.ev, OddForm.ext (ev_alg Φ _) (by rw [od_alg, h])⟩⟩
  rintro ⟨b, rfl⟩
  exact od_alg Φ b

private def oddPart : Submodule B Φ.Ext where
  carrier := {z | z.ev = 0}
  add_mem' := fun {x y} (hx : x.ev = 0) (hy : y.ev = 0) => show (x + y).ev = 0 by
    rw [OddForm.ev_add, hx, hy, add_zero]
  zero_mem' := rfl
  smul_mem' := fun c x (hx : x.ev = 0) => show (c • x).ev = 0 by
    rw [OddForm.ev_smul, hx, mul_zero]

private theorem mem_oddPart (z : Φ.Ext) : z ∈ oddPart Φ ↔ z.ev = 0 := Iff.rfl

private theorem compl_oddPart : _root_.IsCompl (1 : Submodule B Φ.Ext) (oddPart Φ) := by
  refine ⟨Submodule.disjoint_def.2 fun z h1 h2 => ?_, codisjoint_iff.2 (eq_top_iff.2 fun z _ => ?_)⟩
  · exact OddForm.ext ((mem_oddPart Φ z).1 h2) ((mem_one_iff Φ z).1 h1)
  · refine Submodule.mem_sup.2 ⟨Φ.el z.ev 0, (mem_one_iff Φ _).2 rfl, Φ.el 0 z.od, rfl, ?_⟩
    apply OddForm.ext
    · change z.ev + 0 = z.ev
      simp
    · change 0 + z.od = z.od
      simp

end aux

private theorem oB_eq_iff {n a : ℕ} (h1 : 1 ≤ a) (h2 : a < n) (i j : Fin n) :
    oB n a i = oB n a j ↔ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) := by
  unfold oB
  by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] <;> omega

theorem UpperTheory.V.Pa.gr_E :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} [Module.Finite B E] (a : ℕ) (T : TrInv B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F) (U : T.Units (Fin n) (oB n a)), 1 ≤ a → a < n → RingHom.ker (algebraMap B F) = maximalIdeal B → (∀ y, r (T.st y) = (r y)ᵀ) → (∀ i, r (U.x i) = single (oB n a i) i 1) → (∀ y, r y ∈ Ev F F n a) → Nonempty (GrAlg T n a r U.ep) := by
  intro B E F _ _ _ _ _ _ n _ a T r U h1 h2 hker hst hx hev
  let p : Fin n := ⟨0, by omega⟩
  let q : Fin n := ⟨n - 1, by omega⟩
  have hpq : p ≠ q := fun h => by
    have := congrArg Fin.val h
    simp only [p, q] at this
    omega
  have ho : ∀ i, oB n a i = p ∨ oB n a i = q := fun i => by
    unfold oB
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hp : oB n a p = p := by
    unfold oB
    rw [if_pos (show 0 < a by omega)]
  have hq : oB n a q = q := by
    unfold oB
    rw [if_neg (show ¬ (n - 1 < a) by omega)]
  have h0 : ∀ y i j, oB n a i ≠ oB n a j → r y i j = 0 := fun y i j h =>
    (Submodule.mem_bot F).1 ((hev y i j).2 fun h' => h ((oB_eq_iff h1 h2 i j).2 h'))
  obtain ⟨φ, hφ, hφst, -⟩ := vr_hom T (oB n a) U p q hpq ho
  obtain ⟨hinj, hrange⟩ := vr_range T (oB n a) U p q hpq ho
  obtain ⟨hred, hle⟩ := vr_reduction T (oB n a) U r p q hst hx h0
  have hle' := hle hp hq hpq
  rw [hker] at hle'
  have hφe : (φ : E → _) = U.vr p q := funext hφ
  haveI : Module.Finite B (corner B (U.ep p) (U.ep q)) := Module.Finite.range _
  have hv : ∀ y y' k l, U.x k * y * T.st (U.x l) = U.x k * y' * T.st (U.x l) → φ y k l = φ y' k l :=
    fun y y' k l h => by
      rw [hφ, hφ]
      simp only [TrInv.Units.vr, Matrix.of_apply, h]
  have ha : ∀ i, U.x i * U.ep i = U.x i := fun i => by
    conv_lhs => rw [← U.x_mem i, mul_assoc, (U.coi.idem i).eq]
    exact U.x_mem i
  have hd : ∀ i, U.ep i * T.st (U.x i) = T.st (U.x i) := fun i => by
    rw [← U.st_ep i, ← T.st_mul, ha]
  refine ⟨{ AA := (U.oddForm p q).Ext
            fin := inferInstance
            inj := fun b b' h => ?_
            N := oddPart _
            compl := compl_oddPart _
            mul_mem := fun y hy z hz => ?_
            typeI := fun h => absurd h h2.ne
            φ := φ
            φ_inj := hφe ▸ hinj
            range := fun Y => ?_
            st := hφst
            φ_ep := fun i => ?_
            red := fun y i j b h => ?_ }⟩
  · rw [← ev_alg (U.oddForm p q) b, h, ev_alg]
  · rw [mem_oddPart] at hy hz
    refine ⟨(U.oddForm p q).be y.od z.od, hle' (Ideal.subset_span ⟨_, _, rfl⟩), OddForm.ext ?_ ?_⟩
    · rw [ev_alg, OddForm.ev_mul, hy, zero_mul, zero_add]
    · rw [od_alg, OddForm.od_mul, hy, hz, zero_smul, zero_smul, add_zero]
  · rw [hφe, hrange]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [mem_one_iff, mem_oddPart, Ne, oB_eq_iff h1 h2]
  · ext1 k l
    by_cases hk : k = i
    · subst hk
      by_cases hl : l = k
      · subst hl
        rw [hv (U.ep l) 1 l l (by rw [ha, mul_one]), map_one, one_apply_eq, single_apply_same]
      · have e : U.ep k * U.ep l = 0 := U.coi.ortho (Ne.symm hl)
        rw [hv (U.ep k) 0 k l (by rw [← hd l, mul_assoc, ← mul_assoc (U.ep k), e]; simp), map_zero,
          single_apply_of_col_ne _ _ (Ne.symm hl), Matrix.zero_apply]
    · have e : U.ep k * U.ep i = 0 := U.coi.ortho hk
      rw [hv (U.ep i) 0 k l (by rw [← ha k, mul_assoc (U.x k), e]; simp), map_zero,
        single_apply_of_row_ne (Ne.symm hk), Matrix.zero_apply]
  · rw [← hred y i j, ← hφ]
    have e : φ y i j = (φ y i j - algebraMap B _ b) + algebraMap B _ b := (sub_add_cancel _ _).symm
    rw [e, OddForm.ev_add, (mem_oddPart _ _).1 h, ev_alg, zero_add]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.hat_st :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) → ∀ H : Hat h x u.D P.ker Bh (G.frame.eps O B), ∀ y, H.r (H.T.st y) = (H.r y)ᵀ := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hf H
  have key : ∀ g : G.G₀, (algebraMap B Bh) ↑((G.frame.eps O B) g ^ (1 - (n : ℤ))) •
      ((mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹)).map (algebraMap x.A (FractionRing x.A)) =
      (((mat x.ρ) (h.p₀ g)).map (algebraMap x.A (FractionRing x.A)))ᵀ := by
    intro g
    obtain ⟨he, hc⟩ := eps_eq P g
    have hunit : P.f (↑((G.frame.eps O B) g ^ (1 - (n : ℤ))) : B) =
        ↑((G0.frame.eps ℤ_[l] x.A) (h.p₀ g) ^ (1 - (n : ℤ))) := by
      have hu : Units.map (P.f : B →* x.A) ((G.frame.eps O B) g) =
          (G0.frame.eps ℤ_[l] x.A) (h.p₀ g) := by
        apply Units.ext
        rw [Units.coe_map]
        exact he
      rw [← hu, ← map_zpow (Units.map (P.f : B →* x.A)), Units.coe_map]
      rfl
    have hinvM : (mat x.ρ) (h.p₀ (G.frame.conj g)) * (mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
    have hA : ((mat x.ρ) (h.p₀ g))ᵀ =
        (↑((G0.frame.eps ℤ_[l] x.A) (h.p₀ g) ^ (1 - (n : ℤ))) : x.A) •
          (mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹) := by
      have hform := x.form (h.p₀ g)
      rw [Units.val_one, Matrix.mul_one, ← hc] at hform
      calc ((mat x.ρ) (h.p₀ g))ᵀ = ((mat x.ρ) (h.p₀ g))ᵀ * ((mat x.ρ) (h.p₀ (G.frame.conj g)) *
            (mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹)) := by rw [hinvM, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, hform, Matrix.smul_mul, Matrix.one_mul]
    rw [← Matrix.transpose_map, hA]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    rw [Algebra.smul_def, hf, hunit]
  intro y
  obtain ⟨z, rfl⟩ := H.surj y
  refine MonoidAlgebra.induction_on (motive := fun z => H.r (H.T.st (H.ι z)) = (H.r (H.ι z))ᵀ)
    z ?_ ?_ ?_
  · intro g
    rw [MonoidAlgebra.of_apply, H.st, map_smul, H.r_ι, H.r_ι]
    exact key g
  · intro a b ha hb
    simp only [map_add (f := _), ha, hb, Matrix.transpose_add]
  · intro c a ha
    simp only [map_smul, ha, Matrix.transpose_smul]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.rep_star :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ y, P.rep (G.frame.star O B n y) = (P.rep y)ᵀ := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P y
  have sb := star_basic G.frame n O B
  have hrep : ∀ (g : G.G₀) (b : B), P.rep (MonoidAlgebra.single g b) = P.f b • mat x.ρ (h.p₀ g) := by
    intro g b
    simp only [OoPt.rep, GDet.repAlg, RingHom.comp_apply, MonoidAlgebra.mapRingHom_single,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.comp_apply,
      Algebra.algebraMap_self, RingHom.mapMatrix_id]
    rfl
  induction y using MonoidAlgebra.induction_linear with
  | zero =>
    have h0 : G.frame.star O B n 0 = 0 := by simpa using sb.2.2.2.2.2.1 0 0
    rw [h0, map_zero, Matrix.transpose_zero]
  | add p q hp hq => rw [sb.2.2.1, map_add (f := _), map_add (f := _), hp, hq, Matrix.transpose_add]
  | single g b =>
    rw [sb.2.2.2.2.2.2 g b]
    obtain ⟨he, hc⟩ := eps_eq P g
    have hform := x.form (h.p₀ g)
    rw [Units.val_one, mul_one] at hform
    have hci : mat x.ρ (G0.frame.conj (h.p₀ g)) * mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hT : (mat x.ρ (h.p₀ g))ᵀ =
        ((G0.frame.eps ℤ_[l] (PowerSeries x.K) (h.p₀ g) ^ (1 - (n : ℤ)) : (PowerSeries x.K)ˣ) : PowerSeries x.K) •
          mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹ := by
      calc (mat x.ρ (h.p₀ g))ᵀ
          = (mat x.ρ (h.p₀ g))ᵀ * (mat x.ρ (G0.frame.conj (h.p₀ g)) * mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹) := by
            rw [hci, mul_one]
        _ = _ := by rw [← mul_assoc, hform, Matrix.smul_mul, one_mul]
    have hu : Units.map (P.f.toRingHom : B →* x.A) (G.frame.eps O B g) = G0.frame.eps ℤ_[l] x.A (h.p₀ g) :=
      Units.ext he
    have hfu : P.f ((G.frame.eps O B g ^ (1 - (n : ℤ)) : Bˣ) : B) =
        ((G0.frame.eps ℤ_[l] x.A (h.p₀ g) ^ (1 - (n : ℤ)) : (x.A)ˣ) : x.A) := by
      calc P.f ((G.frame.eps O B g ^ (1 - (n : ℤ)) : Bˣ) : B)
          = ((Units.map (P.f.toRingHom : B →* x.A) (G.frame.eps O B g ^ (1 - (n : ℤ))) : (x.A)ˣ) : x.A) := rfl
        _ = _ := by rw [map_zpow, hu]
    rw [hrep, hrep, Matrix.transpose_smul, map_mul, hfu, hT, map_inv, hc, mul_smul]
end

section

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

theorem rF_surj : ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K]
    {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u)
    {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)],
    (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) →
    RingHom.ker (algebraMap Bh (FractionRing x.A)) = maximalIdeal Bh →
    Function.Surjective (algebraMap Bh (FractionRing x.A)) := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hcomp hker z
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors x.A) z
  obtain ⟨a', rfl⟩ := (f_surj P).1 a
  obtain ⟨b', hb'⟩ := (f_surj P).1 (b : x.A)
  have hu : IsUnit (algebraMap B Bh b') := by
    by_contra hn
    have hm : algebraMap B Bh b' ∈ maximalIdeal Bh := (mem_maximalIdeal _).2 hn
    rw [← hker, RingHom.mem_ker, hcomp, hb'] at hm
    exact nonZeroDivisors.coe_ne_zero b
      ((IsFractionRing.injective x.A (FractionRing x.A)) (hm.trans (map_zero _).symm))
  obtain ⟨v, hv⟩ := hu
  refine ⟨algebraMap B Bh a' * ↑v⁻¹, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← hb', ← hcomp, ← hv, ← map_mul, mul_assoc,
    Units.inv_mul, mul_one, hcomp]

end UpperTheory.V.Pa
end
end
