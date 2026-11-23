module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle253
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle352
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle353
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle356
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle355
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle349
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp)
open Module

namespace GlobalTheory.Cusp.WittIdx

section Lin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Formalism.BasicNotions.HSpace E}

theorem mem_perp' {W : Submodule E V.V} {y : V.V} : y ∈ perp V W ↔ ∀ x ∈ W, V.hT x y = 0 := by
  simp only [perp, Submodule.mem_iInf, LinearMap.mem_ker]

private theorem perp_eq_ker_pi_hT_finBasis (A : Submodule E V.V) :
    perp V A = LinearMap.ker (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V)) := by
  ext y
  rw [mem_perp', LinearMap.mem_ker]
  constructor
  · intro h
    funext k
    simpa using h _ (Module.finBasis E A k).2
  · intro h x hx
    have hk : ∀ k, V.hT ((Module.finBasis E A k : A) : V.V) y = 0 := fun k => by
      simpa using congrFun h k
    have hx' : x = ∑ k, (Module.finBasis E A).repr ⟨x, hx⟩ k • ((Module.finBasis E A k : A) : V.V) := by
      have e := congrArg A.subtype ((Module.finBasis E A).sum_repr ⟨x, hx⟩)

      simp only [map_sum, map_smul, Submodule.subtype_apply] at e
      exact e.symm
    rw [hx']

    simp [map_sum, hk]

private theorem pi_hT_finBasis_range_surjective (A : Submodule E V.V) :
    LinearMap.range (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V)) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := (LinearMap.range (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V))).exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
  have hw : ∀ y, V.hT (∑ k, star (φ fun j => if k = j then (1 : E) else 0) •
      ((Module.finBasis E A k : A) : V.V)) y = 0 := by
    intro y
    have h1 := hle ⟨y, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at h1
    simp only [LinearMap.pi_apply, smul_eq_mul] at h1
    have h2 : ∑ k, (φ fun j => if k = j then (1 : E) else 0) *
        V.hT ((Module.finBasis E A k : A) : V.V) y = 0 := by
      calc _ = ∑ k, V.hT ((Module.finBasis E A k : A) : V.V) y *
            (φ fun j => if k = j then (1 : E) else 0) := Finset.sum_congr rfl fun k _ => mul_comm _ _
        _ = 0 := h1

    rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
    exact h2
  have h0 := V.nondeg.1 _ hw
  have h0' : ∑ k, star (φ fun j => if k = j then (1 : E) else 0) • Module.finBasis E A k = 0 := by
    apply Subtype.ext
    simpa using h0
  have hc : ∀ k, φ (fun j => if k = j then (1 : E) else 0) = 0 := fun k => by
    have := Fintype.linearIndependent_iff.1 (Module.finBasis E A).linearIndependent _ h0' k
    simpa using this
  apply hφ
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp [hc]

theorem finrank_add_finrank_perp (A : Submodule E V.V) : finrank E A + finrank E (perp V A) = V.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V))
  rw [pi_hT_finBasis_range_surjective, finrank_top, Module.finrank_fin_fun, ← perp_eq_ker_pi_hT_finBasis, V.rank_eq] at h
  exact h

end Lin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.Cusp.WittIdx
end

section

noncomputable section

namespace GlobalTheory.StdFrameObj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.FWT GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_piT_mul {P : PreCh} (L : LevCh P) :
    (star (L.piT P.u₀ : L.host.E) : L.host.E) * (L.piT P.u₀ : L.host.E) = (L.T P.u₀ : L.host.E) := by
  have h : (star (L.piT P.u₀ : L.host.E) : L.host.E) = L.host.conj (L.piT P.u₀ : L.host.E) :=
    bridge_star_holds P.R L.host _
  rw [h, mul_comm]
  exact L.piT_norm _

def coordPre (P : PreCh) (L : LevCh P) : Pre :=
  Pre.ofCh P L (DiagSp.spacesNorm P.R (host_cmData P.R L.host) (L.T P.u₀) (L.T_prime _) _ (star_piT_mul L)) rfl
    (fun j _ τ => DiagSp.spacesNorm_Y_sig _ _ _ _ _ _ j τ)
    (fun j _ hj => DiagSp.spacesNorm_hasFrame _ _ _ _ _ _ j hj) (fun _ _ _ => rfl)
    (DiagSp.spacesNorm_z_norm _ _ _ _ _ _)

theorem diagSpaces_coordPre (P : PreCh) (L : LevCh P) : DiagSpaces (coordPre P L).sp :=
  DiagSp.spacesNorm_coord _ _ _ _ _ _

end GlobalTheory.StdFrameObj

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

theorem _root_.GlobalTheory.T.kummerScalarLayerLink_of_shapiroSpecialization_approx : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (e : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), (∀ r, ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → ‖y s 1 - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s 1‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → SpLink A e χ (fun r s x => Y r s x 1) y := by
  first | exact @GlobalTheory.KZ.spLink_of_spec_approx | exact GlobalTheory.KZ.spLink_of_spec_approx | (intros; apply GlobalTheory.KZ.spLink_of_spec_approx <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.KZ.DiamU

theorem isDiam_sgD_of_coprime' {N l d : ℕ} (hl : l ≠ 0) (hd : Nat.Coprime d N) : IsDiam N l d (sgD N l d) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : d = 1 := (Nat.coprime_zero_right d).1 hd
    subst h1
    exact Classical.epsilon_spec (p := IsDiam 0 l 1) ⟨1, Subgroup.one_mem _, by simp [en]⟩
  · exact Betti.isDiam_sgD hN.ne' hl hd

theorem upper_mul_eq {N l d : ℕ} {σ : SL(2, ℤ)} (hσ : IsDiam N l d σ) (hl : 0 < l) (j k : ℕ)
    (hk : (k : ZMod l) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod l) =
      (((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod l)) :
    ∃ s : SL(2, ℤ), IsDiam N l d s ∧
      !![1, (j : ℤ); 0, (l : ℤ)] * (σ : Matrix (Fin 2) (Fin 2) ℤ) =
        (s : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (k : ℤ); 0, (l : ℤ)] := by
  obtain ⟨h0, hd⟩ := hσ
  rw [Subgroup.mem_inf] at h0
  have hcN := CongruenceSubgroup.Gamma0_mem.1 h0.1
  have hcl := CongruenceSubgroup.Gamma0_mem.1 h0.2
  have hdet := σ.det_coe
  rw [Matrix.det_fin_two] at hdet
  simp only [en] at hd
  have hdiv : (l : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      k * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hk hcl ⊢
    rw [hcl]
    linear_combination -hk
  obtain ⟨q, hq⟩ := hdiv
  set a := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set b := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set c := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set e := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  set S : Matrix (Fin 2) (Fin 2) ℤ := !![a + j * c, q; l * c, e - c * k] with hSdef
  have hM : !![1, (j : ℤ); 0, (l : ℤ)] * (σ : Matrix (Fin 2) (Fin 2) ℤ) = S * !![1, (k : ℤ); 0, (l : ℤ)] := by
    ext i i'
    fin_cases i <;> fin_cases i' <;>
      simp [hSdef, Matrix.mul_apply, Fin.sum_univ_two, a, b, c, e] <;> first | ring1 | linear_combination hq
  have hS : S.det = 1 := by
    have h := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul, σ.det_coe] at h
    simp only [Matrix.det_fin_two_of] at h
    have hl' : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
    have : ((l : ℤ)) * 1 = S.det * (l : ℤ) := by linarith
    exact (mul_right_cancel₀ hl' (by linarith : S.det * (l : ℤ) = 1 * (l : ℤ)))
  refine ⟨⟨S, hS⟩, ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩, hM⟩
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    show ((l * c : ℤ) : ZMod N) = 0
    rw [Int.cast_mul, hcN, mul_zero]
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    show ((l * c : ℤ) : ZMod l) = 0
    rw [Int.cast_mul, hcl, mul_zero]
  · simp only [en]
    simp [hSdef]
    rw [hcN]; simpa using hd

private def res (l : ℕ) (x : ℤ) : ℕ := (x % (l : ℤ)).toNat

private theorem res_lt {l : ℕ} (hl : 0 < l) (x : ℤ) : res l x < l := by
  have h1 := Int.emod_lt_of_pos x (show (0 : ℤ) < l by exact_mod_cast hl)
  have h2 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by exact_mod_cast hl.ne')
  unfold res; omega

private theorem res_cast {l : ℕ} (hl : 0 < l) (x : ℤ) : ((res l x : ℕ) : ZMod l) = (x : ZMod l) := by
  have h2 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by exact_mod_cast hl.ne')
  rw [← Int.cast_natCast, res, Int.toNat_of_nonneg h2, ZMod.intCast_mod]

private theorem res_eq {l : ℕ} (hl : 0 < l) {x : ℤ} {j : ℕ} (hj : j < l) (h : (x : ZMod l) = j) : res l x = j := by
  rw [← res_cast hl, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (res_lt hl x)] at h
  exact h

theorem act_sgD_heckeU : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    (w d : ℕ), d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w →
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b) =
      X.heckeU l (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  intro Ω _ _ ε X N l _ w d hd _ b hb
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hσ := isDiam_sgD_of_coprime' hl.ne' hd
  have hcl := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hσ.1).2
  have hdet := (sgD N l d).det_coe
  rw [Matrix.det_fin_two] at hdet
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have hm : ∀ j : ℕ, 0 < (!![1, (j : ℤ); 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := fun j => by
    rw [Matrix.det_fin_two_of]; simpa using hl
  have key := fun j k => upper_mul_eq hσ hl j k
  generalize hA : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = A at hdet key
  generalize hB : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = B at hdet key
  generalize hE : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = E at hdet key
  have hae : (A : ZMod l) * E = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod l) hdet
    push_cast at h
    rw [hcl] at h
    linear_combination h

  simp only [Tower.heckeU, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_nbij' (fun j : ℕ => res l ((B + j * E) * E)) (fun k : ℕ => res l ((k * A - B) * A))
    (fun j _ => Finset.mem_range.2 (res_lt hl _)) (fun k _ => Finset.mem_range.2 (res_lt hl _)) ?_ ?_ ?_
  · intro j hj
    refine res_eq hl (Finset.mem_range.1 hj) ?_
    push_cast
    rw [res_cast hl]
    push_cast
    linear_combination ((j : ZMod l) + (B + j * E) * A) * hae
  · intro k hk
    refine res_eq hl (Finset.mem_range.1 hk) ?_
    push_cast
    rw [res_cast hl]
    push_cast
    linear_combination ((k : ZMod l) + (k * A - B) * E) * hae
  · intro j _
    obtain ⟨s, hs, hM⟩ := key j (res l ((B + j * E) * E)) (by
      rw [res_cast hl]
      push_cast
      linear_combination ((B : ZMod l) + j * E) * hae)
    rw [Tower.act_act Ω ε X l _ _ (hm j) (hpos _), hM, ← Tower.act_act Ω ε X l _ _ (hpos _) (hm _),
      X.act_isDiam_eq hb hs]

end GlobalTheory.KZ.DiamU
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.galB_act_diagNatOne_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → ∀ (l : ℕ) [Fact l.Prime] (q : ℕ), 0 < q → ∀ (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l), X.galB l s (X.act l !![(q : ℤ), 0; 0, 1] b) = X.act l !![(q : ℤ), 0; 0, 1] (X.galB l s b) := by
  first | exact @GlobalTheory.KZ.Tower.galB_act_diag | exact GlobalTheory.KZ.Tower.galB_act_diag | (intros; apply GlobalTheory.KZ.Tower.galB_act_diag <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.sum_act_upperTriangular_hecke_reindex_coprime_unit : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (c : X.Fn l), (∀ t : ℤ, X.act l !![1, t; 0, 1] c = c) → ∀ (q : ℕ) (e : ℤ), 0 < q → IsCoprime e (q : ℤ) → ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ) * e; 0, (q : ℤ)] c = ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] c := by
  first | exact @GlobalTheory.KZ.Tower.sum_act_upper_mul_unit | exact GlobalTheory.KZ.Tower.sum_act_upper_mul_unit | (intros; apply GlobalTheory.KZ.Tower.sum_act_upper_mul_unit <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.isCuspFunctionalValueModPrimePow_diamond_independent : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ) (b : X.Fn l), b ∈ X.B N l w → ∀ s : SL(2, ℤ), IsDiam N l d s → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n (X.act l (s : Matrix (Fin 2) (Fin 2) ℤ) b) φ ↔ IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ := by
  first | exact @GlobalTheory.KZ.isThB_act_isDiam_iff | exact GlobalTheory.KZ.isThB_act_isDiam_iff | (intros; apply GlobalTheory.KZ.isThB_act_isDiam_iff <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_integral_limit_compatible_modPrimePow : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (X : Type) (a : ℕ → X → Qbar l), (∀ n x, a n x ∈ c.O) → (∀ n x, Cg n (a (n + 1) x) (a n x)) → ∃ z : X → Qbar l, (∀ x, z x ∈ c.O) ∧ ∀ n x, Cg n (z x) (a n x) := by
  first | exact @GlobalTheory.Ord2.exists_limit_coef | exact GlobalTheory.Ord2.exists_limit_coef | (intros; apply GlobalTheory.Ord2.exists_limit_coef <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.integralGaloisRep_locallyConstant_modPrimePow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (W : R2 Ω l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j, ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o := by
  first | exact @GlobalTheory.Ord2.locConst_mod_pow | exact GlobalTheory.Ord2.locConst_mod_pow | (intros; apply GlobalTheory.Ord2.locConst_mod_pow <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.limit_of_approximate_cocycles : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l), (∀ s i j, mat W s i j ∈ c.O) → ∀ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (z : G ℚ Ω → Fin 2 → Qbar l), (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) → (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) → (∀ n s, Cv n (z s) (a n s)) → z ∈ Z1 (Loc.colRep W) := by
  first | exact @GlobalTheory.Ord2.limit_cocycle_mem_cocycles | exact GlobalTheory.Ord2.limit_cocycle_mem_cocycles | (intros; apply GlobalTheory.Ord2.limit_cocycle_mem_cocycles <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.cob2_of_cocycle_cong_of_invariant : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (D K : Subgroup (G ℚ Ω)) (φ : ↥D) (m : ℕ) (d : ↥D →* Multiplicative (ZMod (m * l ^ n))) (ξ : G ℚ Ω → G ℚ Ω → Qbar l), 0 < m → ((φ ^ m : ↥D) : G ℚ Ω) ∈ K → IsOpen (d.ker : Set ↥D) → (∀ s : ↥D, (((φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s : ↥D) : G ℚ Ω) ∈ K) → (∀ k ∈ K, Cg n (eps l k) 1) → (∀ s t, ξ s t ∈ c.O) → (∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s)) → (∀ s ∈ D, ∀ t ∈ D, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)) → Cob2 c n D ξ := by
  first | exact @GlobalTheory.Ord2.FrobCob.twoCocycleModPow_coboundary_of_frobenius_split | exact GlobalTheory.Ord2.FrobCob.twoCocycleModPow_coboundary_of_frobenius_split | (intros; apply GlobalTheory.Ord2.FrobCob.twoCocycleModPow_coboundary_of_frobenius_split <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.LocCharSpan

open UpperTheory.V.X

variable {O Γ : Type} [CommRing O] [TopologicalSpace O] [Group Γ] [TopologicalSpace Γ]

theorem red_mem (p : O) (hp : Continuous (Lev.mk p)) (θ : Γ →* Oˣ) (a : Γ → O) (ha : Continuous a)
    (hc : ∀ s t, p ∣ a (s * t) - (a s + ((θ s : Oˣ) : O) * a t)) :
    (fun s => Lev.mk p (a s)) ∈ Z1 (Formalism.GaloisCohomology.scalRep (Lev p) θ) := by
  refine ⟨hp.comp ha, fun s t => ?_⟩
  have h := (Lev.mk_eq_zero p _).2 (hc s t)
  rw [map_sub, sub_eq_zero, map_add (f := _), ← smul_eq_mul ((θ s : Oˣ) : O), map_smul] at h
  exact h


omit [TopologicalSpace O] in
theorem lift_cob (p : O) (θ : Γ →* Oˣ) (z : Z1 (Formalism.GaloisCohomology.scalRep (Lev p) θ)) (f : Γ → O)
    (hf : ∀ s, z.1 s = Lev.mk p (f s))
    (hz : (Submodule.Quotient.mk z : H1 (Formalism.GaloisCohomology.scalRep (Lev p) θ)) = 0) :
    ∃ y : O, ∀ s, p ∣ f s - (((θ s : Oˣ) : O) * y - y) := by
  obtain ⟨y', hy'⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hz)
  obtain ⟨y, rfl⟩ := Lev.mk_surjective p y'
  refine ⟨y, fun s => (Lev.mk_eq_zero p _).1 ?_⟩
  have h : z.1 s = ((θ s : Oˣ) : O) • Lev.mk p y - Lev.mk p y := hy' s
  rw [map_sub, map_sub, ← hf, h, ← smul_eq_mul, map_smul, sub_self]


omit [TopologicalSpace O] in
theorem kill (p : O) (θ : Γ →* Oˣ) (h : H1 (Formalism.GaloisCohomology.scalRep (Lev p) θ)) : p • h = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  have h0 : p • z = 0 := Subtype.ext (funext fun s => by
    obtain ⟨y, hy⟩ := Lev.mk_surjective p (z.1 s)
    change p • z.1 s = 0
    rw [← hy, ← map_smul, Lev.mk_eq_zero]
    exact Dvd.intro _ rfl)
  rw [← Submodule.Quotient.mk_smul, h0, Submodule.Quotient.mk_zero]

theorem span_of_classes (p q : O) (hp : Continuous (Lev.mk p)) (θ : Γ →* Oˣ) (m : ℕ)
    (hcount : ∀ z : H1 (Formalism.GaloisCohomology.scalRep (Lev p) θ), (∀ x : O, x • z = 0 → q ∣ x) →
      ∀ h : H1 (Formalism.GaloisCohomology.scalRep (Lev p) θ), ∃ x : O, m • h = x • z)
    (a : Γ → O) (ha : Continuous a) (hca : ∀ s t, p ∣ a (s * t) - (a s + ((θ s : Oˣ) : O) * a t))
    (hann : ∀ x y : O, (∀ s, p ∣ x * a s - (((θ s : Oˣ) : O) * y - y)) → q ∣ x)
    (a' : Γ → O) (ha' : Continuous a') (hca' : ∀ s t, p ∣ a' (s * t) - (a' s + ((θ s : Oˣ) : O) * a' t)) :
    ∃ x y : O, ∀ s, p ∣ (m : O) * a' s - (x * a s + (((θ s : Oˣ) : O) * y - y)) := by
  let z : Z1 (Formalism.GaloisCohomology.scalRep (Lev p) θ) := ⟨_, red_mem _ hp θ a ha hca⟩
  let z' : Z1 (Formalism.GaloisCohomology.scalRep (Lev p) θ) := ⟨_, red_mem _ hp θ a' ha' hca'⟩
  obtain ⟨x, hx⟩ := hcount (Submodule.Quotient.mk z) (fun x hx => by
      rw [← Submodule.Quotient.mk_smul] at hx
      obtain ⟨y, hy⟩ := lift_cob _ θ (x • z) (fun s => x * a s)
        (fun s => ((Lev.mk p).map_smul x (a s)).symm) hx
      exact hann x y hy) (Submodule.Quotient.mk z')
  rw [← Nat.cast_smul_eq_nsmul O, ← sub_eq_zero, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_sub] at hx
  obtain ⟨y, hy⟩ := lift_cob _ θ ((m : O) • z' - x • z) (fun s => (m : O) * a' s - x * a s)
    (fun s => by
      rw [map_sub, ← smul_eq_mul, ← smul_eq_mul, map_smul, map_smul]
      rfl) hx
  refine ⟨x, y, fun s => ?_⟩
  rw [← sub_sub]
  exact hy s

end GlobalTheory.LocCharSpan

theorem GlobalTheory.LocCharSpan.span : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ' : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ' g : c.Oˣ) : c.O)) → (∃ g, θ' g ≠ 1) → (∃ g, θ' g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g) → ∀ r : ℕ, ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 1 ≤ n → ∀ a : ↥(Dec (F := ℚ) A) → c.O, Continuous a → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a (s * t) - (a s + ((θ' s : c.Oˣ) : c.O) * a t)) → (∀ x y : c.O, (∀ s, ((l : ℕ) : c.O) ^ n ∣ x * a s - (((θ' s : c.Oˣ) : c.O) * y - y)) → ((l : ℕ) : c.O) ^ (n - r) ∣ x) → ∀ a' : ↥(Dec (F := ℚ) A) → c.O, Continuous a' → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a' (s * t) - (a' s + ((θ' s : c.Oˣ) : c.O) * a' t)) → ∃ x y : c.O, ∀ s, ((l : ℕ) : c.O) ^ n ∣ (m : c.O) * a' s - (x * a s + (((θ' s : c.Oˣ) : c.O) * y - y)) := by
  intro h1 h2 h3 l _ Ω _ _ _ c A hA θ hθ hn1 hn2 r
  obtain ⟨C, hC⟩ := GlobalTheory.T.local_character_h1_finite_levels h1 h2 h3 l Ω c A hA θ hθ hn1 hn2
  obtain ⟨m, hm, hcount⟩ := GlobalTheory.CycIndex.nsmul_mem_span_of_card_le l c C r
  refine ⟨m, hm, fun n hn a ha hca hann a' ha' hca' => ?_⟩
  obtain ⟨hfin, hcard⟩ := hC n hn
  have hl : ((l : ℕ) : c.O) ≠ 0 := fun h => by
    have h' := congrArg Subtype.val h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h'
    exact (Fact.out : l.Prime).ne_zero h'
  have hp := (UpperTheory.V.X.So.adicCont l c).1 _ (pow_ne_zero n hl)
  exact GlobalTheory.LocCharSpan.span_of_classes _ _ hp θ m
    (hcount n _ (GlobalTheory.LocCharSpan.kill _ θ) hcard) a ha hca hann a' ha' hca'
end
