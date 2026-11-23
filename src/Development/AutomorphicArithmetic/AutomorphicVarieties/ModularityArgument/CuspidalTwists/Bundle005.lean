module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle064
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

private theorem low_ne {Γ R : Type} [Group Γ] [Field R] (y a : Γ → R) (hy : ∀ g h, y (g * h) = y g * a h + y h)
    (g0 g : Γ) (h0 : y g0 = 0) (ha : a g0 ≠ 1) (hg : y g ≠ 0) : y (g * g0 * g⁻¹) ≠ 0 := by
  intro h
  have e1 := hy (g * g0 * g⁻¹) g
  rw [inv_mul_cancel_right, hy, h, h0] at e1
  have e2 : y g * (a g0 - 1) = 0 := by linear_combination e1
  rcases mul_eq_zero.1 e2 with e | e
  · exact hg e
  · exact ha (sub_eq_zero.1 e)

private theorem conj_res {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [hF : IsGalois ℚ F]
    (g : _root_.Formalism.ConjugateSelfDual.G ℚ Ω) (s : _root_.Formalism.ConjugateSelfDual.G F Ω) : ∃ t : _root_.Formalism.ConjugateSelfDual.G F Ω, resQ F t = g * resQ F s * g⁻¹ := by
  haveI : IsGalois ℚ Ω := {}
  have hN : F.fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois F).2 (by convert hF <;> exact Subsingleton.elim _ _)
  have hs : resQ F s ∈ F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact s.commutes ⟨x, hx⟩
  exact ⟨F.fixingSubgroupEquiv ⟨_, hN.conj_mem _ hs g⟩, rfl⟩

private theorem tn_21 {R : Type} [CommRing R] (a b : M2 R) : UpperTheory.V.Cu.tn a b 2 1 = -(a 1 0 * b 1 1) := by
  rfl

private theorem tn_30 {R : Type} [CommRing R] (a b : M2 R) : UpperTheory.V.Cu.tn a b 3 0 = a 1 0 * b 0 0 := by
  rfl

theorem UpperTheory.V.Cu.entOf4 : EntOf4 := by
  intro Ω _ _ _ l _ d T hT hO R _ f hf
  have hU : ∀ y : d.c₁.O, IsUnit y → f y ≠ 0 := fun y hy => (hy.map f).ne_zero
  have h00 : ∀ g, f (d.ρ₁ g 0 0) = f (inc d.h (UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k g)) := fun g => by
    have := hf _ (d.mod.red g).1
    rwa [map_sub, sub_eq_zero] at this
  have h11 : ∀ g, f (d.ρ₁ g 1 1) = 1 := fun g => by
    have := hf _ (d.mod.red g).2.1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have t00 : ∀ g, f (d.τ g 0 0) = 1 := fun g => by
    have := hf _ (d.tau.red g).1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have t11 : ∀ g, f (d.τ g 1 1) ≠ 0 := fun g => by
    by_cases hg : g ∈ d.K'.fixingSubgroup
    · rw [(d.tau.on g hg).1, t00]
      exact one_ne_zero
    · rw [(d.tau.off g hg).1, map_neg, t00]
      exact neg_ne_zero.2 one_ne_zero
  have hPhi : Raw.bar (UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k) (resQ T.F T.g0) ≠ 1 := by
    intro e
    apply hO.dist 0 3 (by decide)
    rw [hT.pr, d.tw.red0, d.tw.red3, e, mul_one]
  have ha : f (d.ρ₁ (resQ T.F T.g0) 0 0) ≠ 1 := by
    rw [h00]
    intro e
    have hu : IsUnit ((UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k (resQ T.F T.g0) : d.c.O) - 1) := by
      by_contra hn
      apply hPhi
      have : residue d.c.O ((UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k (resQ T.F T.g0) : d.c.O) - 1) = 0 :=
        (residue_eq_zero_iff _).2 hn
      rwa [map_sub, map_one, sub_eq_zero] at this
    apply hU _ (hu.map (inc d.h))
    rw [map_sub, map_sub, e, map_one, map_one, sub_self]
  obtain ⟨g, hg⟩ := d.mod.ne
  have hg' : f (d.ρ₁ g 1 0) ≠ 0 := hU _ (by by_contra hn; exact hg hn)
  have key : ∃ t : _root_.Formalism.ConjugateSelfDual.G T.F Ω, f (d.ρ₁ (resQ T.F t) 1 0) ≠ 0 := by
    by_cases h0 : f (d.ρ₁ (resQ T.F T.g0) 1 0) = 0
    · obtain ⟨t, ht⟩ := conj_res T.F g T.g0
      refine ⟨t, ?_⟩
      rw [ht]
      refine low_ne (fun g => f (d.ρ₁ g 1 0)) (fun g => f (d.ρ₁ g 0 0)) (fun g h => ?_) _ g h0 ha hg'
      simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add (f := _), h11, one_mul]
    · exact ⟨T.g0, h0⟩
  obtain ⟨t, ht⟩ := key
  have hδ : f (toC d.h d.δ (resQ T.F t) : d.c₁.O) ≠ 0 := hU _ (Units.isUnit _)
  have ent : ∀ i j, ((d.Q T).map f).r t i j =
      f (toC d.h d.δ (resQ T.F t) : d.c₁.O) * f (UpperTheory.V.Cu.tn (d.ρ₁ (resQ T.F t)) (d.τ (resQ T.F t)) i j) := fun i j => by
    rw [← map_mul]
    rfl
  refine ⟨⟨t, 2, 1, by decide, ?_⟩, ⟨t, 3, 0, by decide, ?_⟩⟩
  · rw [ent, tn_21, map_neg, map_mul]
    exact mul_ne_zero hδ (neg_ne_zero.2 (mul_ne_zero ht (t11 _)))
  · rw [ent, tn_30, map_mul, t00, mul_one]
    exact mul_ne_zero hδ ht

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu.SymplecticFlagConjugation

section Alg

variable {R : Type} [CommRing R]

theorem flg_eq (x s : R) : flg x s = !![1, 0, 0, 0; s, 1, 0, 0; -(x * s), -x, 1, 0; x, 0, -s, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, low, nA, Matrix.mul_apply, Fin.sum_univ_four]

theorem adj_flg (x s : R) : adj (flg x s) = !![1, 0, 0, 0; -s, 1, 0, 0; 0, x, 1, 0; -x, x * s, s, 1] := by
  rw [flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

theorem isGSp_flg (x s : R) : IsGSp 1 (flg x s) := by
  unfold IsGSp
  rw [adj_flg, flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem gsp_tn (d : R) (g t : Matrix (Fin 2) (Fin 2) R) (h00 : t 0 0 * t 0 0 - t 1 0 * t 1 0 = 1)
    (h01 : t 0 0 * t 0 1 - t 1 0 * t 1 1 = 0) (h11 : t 0 1 * t 0 1 - t 1 1 * t 1 1 = -1) :
    IsGSp (d ^ 2 * g.det) (d • tn g t) := by
  unfold IsGSp
  rw [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn, adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
    | ring1
    | linear_combination (d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) * h00
    | linear_combination (d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) * h01
    | linear_combination (-(d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0))) * h01
    | linear_combination (-(d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0))) * h11

theorem flag_conj_smul_tensor_symmetric_eq (x s d a b p q r : R) (hs : s * s = 1) :
    adj (flg x s) * (d • tn !![p, q; (p + q * x) * x - r * x, r] !![a, b; b, a]) * flg x s =
      d • !![(a + b * s) * (p + q * x), b * (p + q * x), -(q * (a * s + b)), a * q;
        0, (a - b * s) * (p + q * x), 0, -(q * (a * s - b));
        0, 0, (a + b * s) * (r - x * q), -(b * (r - x * q));
        0, 0, 0, (a - b * s) * (r - x * q)] := by
  rw [Matrix.mul_smul, Matrix.smul_mul, adj_flg, flg_eq]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
    | ring1
    | linear_combination (-(b * (p + q * x))) * hs
    | linear_combination (-(b * (q * x - r))) * hs
    | linear_combination (b * (p + q * x)) * hs
    | linear_combination (b * (q * x - r)) * hs
    | linear_combination (q * a) * hs

theorem conj_flg (x s d : R) (g t : Matrix (Fin 2) (Fin 2) R) (hs : s * s = 1)
    (hf : g 1 0 + g 1 1 * x = (g 0 0 + g 0 1 * x) * x) (ht : t 1 1 = t 0 0 ∧ t 1 0 = t 0 1) :
    adj (flg x s) * (d • tn g t) * flg x s =
      d • !![(t 0 0 + t 0 1 * s) * (g 0 0 + g 0 1 * x), t 0 1 * (g 0 0 + g 0 1 * x), -(g 0 1 * (t 0 0 * s + t 0 1)), t 0 0 * g 0 1;
        0, (t 0 0 - t 0 1 * s) * (g 0 0 + g 0 1 * x), 0, -(g 0 1 * (t 0 0 * s - t 0 1));
        0, 0, (t 0 0 + t 0 1 * s) * (g 1 1 - x * g 0 1), -(t 0 1 * (g 1 1 - x * g 0 1));
        0, 0, 0, (t 0 0 - t 0 1 * s) * (g 1 1 - x * g 0 1)] := by
  have e1 : g = !![g 0 0, g 0 1; (g 0 0 + g 0 1 * x) * x - g 1 1 * x, g 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linear_combination hf
  have e2 : t = !![t 0 0, t 0 1; t 0 1, t 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht.1, ht.2]
  conv_lhs => rw [e1, e2]
  exact flag_conj_smul_tensor_symmetric_eq x s d (t 0 0) (t 0 1) (g 0 0) (g 0 1) (g 1 1) hs

theorem form_eqs (t : Matrix (Fin 2) (Fin 2) R) (h : tᵀ * !![1, 0; 0, -1] * t = !![1, 0; 0, -1]) :
    t 0 0 * t 0 0 - t 1 0 * t 1 0 = 1 ∧ t 0 0 * t 0 1 - t 1 0 * t 1 1 = 0 ∧ t 0 1 * t 0 1 - t 1 1 * t 1 1 = -1 := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  exact ⟨by linear_combination e00, by linear_combination e01, by linear_combination e11⟩

theorem symplecticAdjoint_map_ringHom {R' : Type} [CommRing R'] (f : R →+* R') (X : M4 R) : adj (X.map f) = (adj X).map f := by
  ext i j
  simp [adj_apply]

theorem conj_map {R' : Type} [CommRing R'] (f : R →+* R') (N M : M4 R) :
    adj (N.map f) * M.map f * N.map f = (adj N * M * N).map f := by
  rw [symplecticAdjoint_map_ringHom, ← Matrix.map_mul, ← Matrix.map_mul]

theorem gsp_map {R' : Type} [CommRing R'] (f : R →+* R') {ν : R} {M : M4 R} (h : IsGSp ν M) : IsGSp (f ν) (M.map f) := by
  unfold IsGSp at *
  rw [symplecticAdjoint_map_ringHom, ← Matrix.map_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem pow_diag {g : M2 R} (h : g 0 1 = 0 ∧ g 1 0 = 0) (n : ℕ) :
    (g ^ n) 0 1 = 0 ∧ (g ^ n) 1 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h.1, h.2, ih.1, ih.2]

theorem res_inv {O : Type} [CommRing O] [IsLocalRing O] (u : Oˣ) (h : residue O (u : O) = 1) :
    residue O ((u⁻¹ : Oˣ) : O) = 1 := by
  have e := congrArg (residue O) (Units.inv_mul u)
  rwa [map_mul, h, mul_one, map_one] at e

end Alg

end UpperTheory.V.Cu.SymplecticFlagConjugation

open UpperTheory.V.Cu.SymplecticFlagConjugation in
theorem UpperTheory.V.Cu.pairOf4 : UpperTheory.V.Cu.PairOf4 := by
  intro Ω _ _ _ l _ d T hT hok W R _ f hdet hθ
  have hr : ∀ g, ((d.Q T).map f).r g =
      ((inc d.h (d.δ (resQ T.F g) : d.c.O)) • tn (d.ρ₁ (resQ T.F g)) (d.τ (resQ T.F g))).map f := fun g => rfl
  have hn : ∀ v, ((d.Q T).map f).n v = (flg (d.x (T.pl v)) (d.s (T.pl v))).map f := fun v => rfl
  have hF : ∀ g : G T.F Ω, resQ T.F g ∈ T.F.fixingSubgroup := fun g x => g.commutes x
  have hcyc : ∀ g : G T.F Ω, cycZ ℚ Ω l (resQ T.F g) = cycZ T.F Ω l g := fun g => rfl
  have hD : ∀ A, ∀ g ∈ Dec (F := T.F) A, resQ T.F g ∈ Dec (F := ℚ) A := fun A g h => mem_Dec.2 (mem_Dec.1 h)
  have hI : ∀ A, ∀ g ∈ Ine (F := T.F) A, resQ T.F g ∈ Ine (F := ℚ) A := fun A g h => mem_Ine.2 (mem_Ine.1 h)
  have hsgn : ∀ A, d.s A * d.s A = 1 := fun A => by
    rcases d.tau.sgn A with h | h <;> rw [h] <;> ring
  refine ⟨fun g => ?_, ?_, ?_, fun v => ?_, fun v s hs => ?_, fun v s hs i => ?_⟩
  · obtain ⟨h00, h01, h11⟩ := form_eqs _ (d.tau.form (resQ T.F g))
    have h1 := _root_.UpperTheory.V.Cu.SymplecticFlagConjugation.gsp_map f (gsp_tn (inc d.h (d.δ (resQ T.F g) : d.c.O)) (d.ρ₁ (resQ T.F g)) _ h00 h01 h11)
    have key : inc d.h (d.δ (resQ T.F g) : d.c.O) ^ 2 * inc d.h (Phi d.D d.T₀.pr d.k (resQ T.F g) : d.c.O) =
        inc d.h (d.D.th (resQ T.F g) : d.c.O) := by
      rw [← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, d.tw.mul]
    rw [map_mul, hdet _ (hF g), ← map_mul, key] at h1
    exact h1
  · rintro g ⟨A, hA, hg, h1⟩
    have hl := hA l (Finset.mem_insert_self _ _)
    have hI' := hI A g hg
    have h2 := d.tw.kill _ ((places ℚ Ω l A).2.2.2 hl hI') h1
    have hK : resQ T.F g ∈ d.K'.fixingSubgroup := by
      by_contra hn'
      have hres : resQ d.T₀.F (resLe hT.le g) = resQ T.F g := AlgEquiv.ext fun _ => rfl
      have hoff := d.quad.off (resLe hT.le g) (by rwa [hres])
      have hb : ∀ j, residue d.c.O (d.D.ps j (resQ T.F g) : d.c.O) = 1 := fun j => by
        have e := congrFun (congrFun h1 j) j
        simpa [Raw.rbar, Raw.r0, diagRep] using e
      have hon : d.T₀.rb wAl (resLe hT.le g) = 1 := by
        show residue d.c.O (((chi d.D d.T₀.pr 0 (resQ T.F g) * (chi d.D d.T₀.pr 1 (resQ T.F g))⁻¹) ^ (1 : ℤ) *
          (chi d.D d.T₀.pr 0 (resQ T.F g) * (chi d.D d.T₀.pr 2 (resQ T.F g))⁻¹) ^ (0 : ℤ) : d.c.Oˣ) : d.c.O) = 1
        have hb' : ∀ i, residue d.c.O (chi d.D d.T₀.pr i (resQ T.F g) : d.c.O) = 1 := fun i => hb (lab d.T₀.pr i)
        rw [zpow_one, zpow_zero, mul_one, Units.val_mul, map_mul, hb', res_inv _ (hb' 1), mul_one]
      have := (UpperTheory.V.Ws.P1.coefRes d.c).2.1
      exact Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq (ResidueField d.c.O) l]; exact d.ctx.1.l_odd)
        (hoff.symm.trans hon)
    have h3 := d.tau.unr A hl _ hI' hK
    have h4 := d.mod.away A hl _ hI' h2.2 (hθ A hA g hg)
    refine (hr g).trans ?_
    rw [h2.1, h3, h4, tn_one]
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · obtain ⟨j, hj⟩ := hT.g0
    have hρ := pow_diag d.mod.nrm (l ^ j)
    have hτ := pow_diag (g := d.τ (resQ d.T₀.F d.T₀.g0)) (by rw [d.tau.nrm]; simp) (l ^ j)
    rw [← map_pow, ← hj] at hρ hτ
    intro a b hab
    refine (congrFun (congrFun (hr T.g0) a) b).trans ?_
    generalize resQ T.F T.g0 = g1 at hρ hτ ⊢
    fin_cases a <;> fin_cases b <;> simp [tn, hρ.1, hρ.2, hτ.1, hτ.2] at hab ⊢
  · change IsLow ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f)
    refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
    · simpa using _root_.UpperTheory.V.Cu.SymplecticFlagConjugation.gsp_map f (isGSp_flg (d.x (T.pl v)) (d.s (T.pl v)))
    · rw [flg_eq]
      fin_cases i <;> simp
    · rw [flg_eq]
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp
  · have hsD := hD _ s hs
    change IsUp (adj ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f) * ((inc d.h (d.δ (resQ T.F s) : d.c.O)) • tn (d.ρ₁ (resQ T.F s)) (d.τ (resQ T.F s))).map f * (flg (d.x (T.pl v)) (d.s (T.pl v))).map f)
    rw [conj_map, conj_flg _ _ _ _ _ (hsgn _) (d.mod.flag _ (T.ovl v) _ hsD)
      (d.tau.on _ (d.quad.split _ (T.ovl v) hsD))]
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp
  · obtain ⟨hi, hc⟩ := UpperTheory.inertia_acts_trivially_on_roots_of_unity T.F Ω l d.ctx.1.l_odd _ (T.ovl v) s hs
    have hc' := (hcyc s).trans hc
    have hsD : resQ T.F s ∈ Dec (F := ℚ) (T.pl v) := hD _ s hs.1
    have hsI := hI _ s hi
    have hK := d.quad.split _ (T.ovl v) hsD
    have hδ := (d.tw.kill _ hc' (hok.ineL _ (T.ovl v) s hi)).1
    have hm := d.mod.ine _ (T.ovl v) _ hsI
    have h3 : chiO ℚ Ω l d.c₁.O (resQ T.F s) = 1 := by
      show Units.map _ (cycZ ℚ Ω l _) = 1
      rw [hc', map_one]
    have ht := d.tau.ine _ (T.ovl v) _ hsI
    rw [h3, one_pow, Units.val_one] at ht hm
    obtain ⟨h00, -, -⟩ := form_eqs _ (d.tau.form (resQ T.F s))
    have hon := d.tau.on _ hK
    have hss := hsgn (T.pl v)
    have h4 : d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.s (T.pl v) = 1 := by
      linear_combination (-(d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.s (T.pl v))) * ht + h00 +
        (d.τ (resQ T.F s) 1 0 + d.τ (resQ T.F s) 0 1) * hon.2 + (-(d.τ (resQ T.F s) 0 1 ^ 2)) * hss
    change (adj ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f) * ((inc d.h (d.δ (resQ T.F s) : d.c.O)) • tn (d.ρ₁ (resQ T.F s)) (d.τ (resQ T.F s))).map f * (flg (d.x (T.pl v)) (d.s (T.pl v))).map f) i i = 1
    rw [conj_map, conj_flg _ _ _ _ _ hss (d.mod.flag _ (T.ovl v) _ hsD) hon, hm.1, hm.2, ht, h4, hδ]
    fin_cases i <;> simp

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu

section Alg

variable {R R' : Type} [CommRing R] [CommRing R']

private theorem tn_map (f : R →+* R') (g t : M2 R) : (tn g t).map f = tn (g.map f) (t.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn]

private theorem flg_map (f : R →+* R') (x s : R) : (flg x s).map f = flg (f x) (f s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem adj_flg (x s : R) : adj (flg x s) = nA (-s) * tn (low (-x)) 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ, sgn, Fin.rev] <;> ring

private theorem conj_flg (a x y s s' : R) (g t : M2 R) :
    adj (flg y s') * (a • tn g t) * flg x s = a • (nA (-s') * tn (low (-y) * g * low x) t * nA s) := by
  have e : tn (low (-y) * g * low x) t = tn (low (-y)) 1 * tn g t * tn (low x) 1 := by
    rw [← tn_mul, ← tn_mul, one_mul, mul_one]
  rw [adj_flg, e, flg]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

private theorem isUp_mid (a : R) {m t : M2 R} {s s' : R} (hm01 : m 0 1 = 0) (hm10 : m 1 0 = 0) (ht01 : t 0 1 = 0)
    (ht10 : t 1 0 = 0) (hs1 : t 1 1 * s = t 0 0 * s') (hs2 : t 1 1 * s' = t 0 0 * s) :
    IsUp (a • (nA (-s') * tn m t * nA s)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [nA, tn, Matrix.mul_apply, Fin.sum_univ_succ, hm01, hm10, ht01, ht10] at hij ⊢ <;>
    first
    | linear_combination (a * m 0 0) * hs1
    | linear_combination (-(a * m 0 0)) * hs1
    | linear_combination (a * m 1 1) * hs2

end Alg

private theorem conj_dec {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {A A' : ValuationSubring Ω} {g s : _root_.Formalism.ConjugateSelfDual.G ℚ Ω}
    (hA : ∀ x, g x ∈ A' ↔ x ∈ A) (hs : s ∈ _root_.ReciprocityTheory.Gal.Dec (F := ℚ) A') : g⁻¹ * s * g ∈ _root_.ReciprocityTheory.Gal.Dec (F := ℚ) A :=
  UpperTheory.V.conjGal_mem_Dec (τ := RingEquiv.refl ℚ) (σ := g.toRingEquiv) (fun x => g.commutes x) hA hs

private theorem key {R : Type} [Field R] {g s t : M2 R} {x y : R} (h : g * t = s * g) (hg0 : g 0 0 ≠ 0)
    (hg : g 1 1 = 1 ∧ g 0 1 = 0) (hs : s 1 1 = 1 ∧ s 0 1 = 0) (ht : t 1 1 = 1 ∧ t 0 1 = 0) (hne : s 0 0 ≠ 1)
    (hx : t 1 0 + t 1 1 * x = (t 0 0 + t 0 1 * x) * x) (hy : s 1 0 + s 1 1 * y = (s 0 0 + s 0 1 * y) * y) :
    g 1 0 + g 1 1 * x - (g 0 0 + g 0 1 * x) * y = 0 := by
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hg.1, hg.2, hs.1, hs.2, ht.1, ht.2] at h0 h1 hx hy ⊢
  have e : t 0 0 = s 0 0 := mul_left_cancel₀ hg0 (by linear_combination h0)
  rw [e] at h1 hx
  refine mul_left_cancel₀ (sub_ne_zero.2 hne) ?_
  linear_combination h1 - hx + g 0 0 * hy

private theorem phi_ne {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (h : D.Good) (pr : Bool) (k : ℕ) (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ _root_.ReciprocityTheory.Gal.Dec (F := ℚ) A, Raw.bar (Phi D pr k) s ≠ 1 := by
  have hT : l ∈ D.T := Finset.mem_insert_self _ _
  obtain ⟨u, hu, -⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 l _ A hl.out (h.pl_over l hl.out) hA
  have hc : chiO ℚ Ω l c.O (D.sg l) = 1 := by simp [chiO, h.sg_cyc]
  have e : Phi D pr k (u⁻¹ * D.sg l * u) = (D.ξ * D.Psi ^ (if pr then (-1 : ℤ) else 1)) (D.sg l) := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
    cases pr <;> simp [Phi, phi, Raw.Psi, Chr.Psi, hc]
  exact ⟨_, hu _ (h.sg_frob l hT).1, fun h' => h.condD l hT _
    ((congrArg (fun z : c.Oˣ => residue c.O (z : c.O)) e).symm.trans h')⟩

theorem overOf4 : OverOf4 := by
  intro Ω _ _ _ l _ d T hT R _ f hf
  refine ⟨rfl, fun v' => ?_⟩
  obtain ⟨v, g, hg⟩ := (d.T₀.cover (T.pl v') (T.ovl v')).exists
  refine ⟨v, g, hg, ?_⟩
  obtain ⟨s, hs, hne⟩ := phi_ne d.D d.ctx.1 d.T₀.pr d.k (T.pl v') (T.ovl v')
  have ht : (resQ d.T₀.F g)⁻¹ * s * resQ d.T₀.F g ∈ _root_.ReciprocityTheory.Gal.Dec (F := ℚ) (d.T₀.pl v) := conj_dec hg hs
  have h1 : ∀ t, ((d.ρ₁ t).map f) 1 1 = 1 ∧ ((d.ρ₁ t).map f) 0 1 = 0 := fun t =>
    ⟨by simpa [sub_eq_zero] using hf _ (d.mod.red t).2.1, hf _ (d.mod.red t).2.2⟩
  have h0 : ∀ t, ((d.ρ₁ t).map f) 0 0 = f (inc d.h (Phi d.D d.T₀.pr d.k t)) := fun t => by
    simpa [sub_eq_zero] using hf _ (d.mod.red t).1
  have hk := key (g := (d.ρ₁ (resQ d.T₀.F g)).map f) (s := (d.ρ₁ s).map f)
    (t := (d.ρ₁ ((resQ d.T₀.F g)⁻¹ * s * resQ d.T₀.F g)).map f) (x := f (d.x (d.T₀.pl v))) (y := f (d.x (T.pl v')))
    (by rw [← Matrix.map_mul, ← Matrix.map_mul, ← map_mul, ← map_mul]; congr 2; group)
    (by rw [h0]; exact (((Phi d.D d.T₀.pr d.k _).isUnit.map (inc d.h)).map f).ne_zero) (h1 _) (h1 _) (h1 _)
    (fun h => by
      rw [h0] at h
      have hn : ¬ IsUnit ((Phi d.D d.T₀.pr d.k s : d.c.O) - 1) := fun hu => by
        have := ((hu.map (inc d.h)).map f).ne_zero
        rw [map_sub, map_sub, map_one, map_one, h, sub_self] at this
        exact this rfl
      refine hne ?_
      show residue d.c.O (Phi d.D d.T₀.pr d.k s : d.c.O) = 1
      rw [← map_one (residue d.c.O)]
      exact Ideal.Quotient.eq.2 hn)
    (by simpa using congrArg f (d.mod.flag _ (d.T₀.ovl v) _ ht))
    (by simpa using congrArg f (d.mod.flag _ (T.ovl v') _ hs))
  have z01 : f (d.τ (resQ d.T₀.F g) 0 1) = 0 := hf _ (d.tau.red _).2
  have hsg := d.tau.mov (d.T₀.pl v) (T.pl v') (resQ d.T₀.F g) (d.T₀.ovl v) hg
  have hτ : ((d.τ (resQ d.T₀.F g)).map f) 1 0 = 0 ∧
      ((d.τ (resQ d.T₀.F g)).map f) 1 1 * f (d.s (d.T₀.pl v)) = ((d.τ (resQ d.T₀.F g)).map f) 0 0 * f (d.s (T.pl v')) ∧
      ((d.τ (resQ d.T₀.F g)).map f) 1 1 * f (d.s (T.pl v')) = ((d.τ (resQ d.T₀.F g)).map f) 0 0 * f (d.s (d.T₀.pl v)) := by
    simp only [Matrix.map_apply]
    by_cases hK : resQ d.T₀.F g ∈ d.K'.fixingSubgroup
    · obtain ⟨e1, e2⟩ := d.tau.on _ hK
      rw [e1, e2, hsg.1 hK, z01]
      exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨e1, e2⟩ := d.tau.off _ hK
      rw [e1, e2, hsg.2 hK, map_neg, map_neg, map_neg, z01]
      exact ⟨neg_zero, by ring, by ring⟩
  have e : ((d.Q d.T₀).map f).r g =
      f (toC d.h d.δ (resQ d.T₀.F g)) • tn ((d.ρ₁ (resQ d.T₀.F g)).map f) ((d.τ (resQ d.T₀.F g)).map f) := by
    rw [← tn_map]
    ext i j
    exact map_mul f _ _
  have e1 : ((d.Q d.T₀).map f).n v = flg (f (d.x (d.T₀.pl v))) (f (d.s (d.T₀.pl v))) := by
    rw [← flg_map]; rfl
  have e2 : ((d.Q T).map f).n v' = flg (f (d.x (T.pl v'))) (f (d.s (T.pl v'))) := by
    rw [← flg_map]; rfl
  rw [e, e1, e2, conj_flg]
  refine isUp_mid _ ?_ ?_ (by simpa using z01) hτ.1 hτ.2.1 hτ.2.2
  · simp only [low, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination (h1 (resQ d.T₀.F g)).2
  · simp only [low, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination hk

end UpperTheory.V.Cu

end
end
