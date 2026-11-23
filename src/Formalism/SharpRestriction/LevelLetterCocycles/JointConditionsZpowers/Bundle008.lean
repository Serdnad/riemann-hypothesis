module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataParams₂
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem bloch_kato_annihilator_above_l (D : D7) (i : D.nd.Loc) (h55 : Formalism.MainNotions.LocalSituation.Conclusion5 D) (hO : LitGoodO) :
    Formalism.MainNotions.LargeLevelLemmas.BlochKatoAnnihilators (D := D) i := by
  intro w hw C _
  exact Formalism.MainNotions.LargeLevelLemmas.bkAAt_of_core (h := (h55 _ _).1) (hO := hO _ C.LL)

end Formalism.MainNotions.N
end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Module

variable {D : D7}

section Pts

variable (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL)

variable {HW i r w hw Cx hG}

end Pts

theorem zeta_of_good {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l} (h : Good K 1 LL) :
    ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  haveI : NeZero (l : Om l) := ⟨by exact_mod_cast hl.ne'⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic l (Om l)) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hl).ne')
  have hp : IsPrimitiveRoot z l := Polynomial.isRoot_cyclotomic_iff.mp hz
  have hmem : z ∈ Ks K 1 := by
    unfold Formalism.BasicNotions.Loc.Ks
    exact (le_sup_right (a := K0 K)) (IntermediateField.subset_adjoin _ _ (by simpa using hp.pow_eq_one))
  exact ⟨⟨z, h.2.2.2 (Ks K 1).val ⟨z, hmem⟩⟩, IsPrimitiveRoot.coe_submonoidClass_iff.mp hp⟩

section Pts2

variable {L : SizeData₂ D} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL}

end Pts2

theorem epsU_eq (i : D.nd.Loc) : epsU D.nd i = chiU D.nd i 1 * (chiU D.nd i 2)⁻¹ := by
  have ht : 2 ≤ D.R.t := by
    have := D.R.rank_add_five_le
    omega
  unfold epsU chiU Formalism.MainNotions.N.Glob.epsO
  rw [D.nd.chi_def i 2 (by norm_num) ht, show (-(((2 : ℕ) : ℤ) - 1)) = -1 by norm_num, zpow_neg_one,
    mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]

theorem rDuO_cont (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (x : D.nd.X i) : Continuous fun g => rDuO D.nd i r x g := by
  have hinv : Continuous fun g : GE D.nd => g⁻¹ := continuous_inv
  have hχ : ∀ c, Continuous fun g => ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i) :=
    fun c => D.nd.chi_cont i c
  have hc : Continuous fun g => (((chiU D.nd i 1 * epsU D.nd i) g : (D.nd.O i)ˣ) : D.nd.O i) := by
    rw [epsU_eq]
    have e : ∀ g, (((chiU D.nd i 1 * (chiU D.nd i 1 * (chiU D.nd i 2)⁻¹)) g : (D.nd.O i)ˣ) : D.nd.O i) =
        (chiU D.nd i 1 g : D.nd.O i) * ((chiU D.nd i 1 g : D.nd.O i) * (chiU D.nd i 2 g⁻¹ : D.nd.O i)) := by
      intro g
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_inv]
    simp only [e]
    exact (hχ 1).mul ((hχ 1).mul ((hχ 2).comp hinv))
  show Continuous fun g => (((chiU D.nd i 1 * epsU D.nd i) g : (D.nd.O i)ˣ) : D.nd.O i) •
    (rO D.nd i r x g⁻¹).transpose
  exact hc.smul ((hr x).comp hinv).matrix_transpose

section Cond

variable (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

variable {L HW i r ρ π}

variable (L HW i r ρ π)

attribute [local instance] nLet_neZero

variable {L HW i r ρ π}

end Cond

end Formalism.MainNotions.N

end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

theorem isClosed_det_eq {Γ A : Type} [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] {n r : ℕ} {ι : Type} (s : Finset ι) (M : Γ → Matrix (Fin n) (Fin n) A)
    (N' : Γ → Matrix (Fin r) (Fin r) A) (χ : ι → Γ → A) (hM : Continuous M) (hN : Continuous N')
    (hχ : ∀ j, Continuous (χ j)) (c : A) :
    IsClosed {g | (Matrix.scalar (Fin n) c - M g).det =
      (Matrix.scalar (Fin r) c - N' g).det * ∏ j ∈ s, (c - χ j g)} := by
  refine isClosed_eq ?_ ?_
  · exact (continuous_const.sub hM).matrix_det
  · apply (continuous_const.sub hN).matrix_det.mul
    classical
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty]; exact continuous_const
    | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (continuous_const.sub (hχ a)).mul ih

theorem infinite_O (D : D7) (i : D.nd.Loc) : Infinite (D.nd.O i) := by
  by_contra h
  haveI : Finite (D.nd.O i) := not_infinite_iff_finite.mp h
  have hf : IsField (D.nd.O i) := Finite.isField_of_domain (D.nd.O i)
  exact IsDiscreteValuationRing.not_a_field' ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hf)

theorem charpoly_of_isRhoOf (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (x : D.nd.X i) (ρ' : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (hAN : Formalism.MainNotions.SumRepresentations.adm5 D) (hr : GoodR D.nd i r)
    (hρ : IsRhoOf D.nd i x ρ') (g : GE D.nd) :
    ((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly =
      ((ρ' g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i)) := by
  unfold Formalism.MainNotions.SumRepresentations.adm5 Formalism.MainNotions.SumRepresentations.At.JacquetShalikaStrongMultOne at hAN
  have hCheb := hAN.2.2.1
  obtain ⟨hrc, -, hrF⟩ := hr x
  obtain ⟨hρc, -, hρF⟩ := hρ
  have hP : (placesOver D.host.E (D.nd.l i)).Finite := by
    have hne : Ideal.span {((D.nd.l i : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.mpr (D.nd.lPrime i).out.ne_zero
    refine (Ideal.finite_factors hne).subset ?_
    intro v hv
    exact Ideal.dvd_span_singleton.mpr hv
  set Sg : Set (PlE D.host) := placesOver D.host.E (D.nd.l i) ∪ (↑(D.nd.S i) : Set (PlE D.host)) ∪
    (↑(D.nd.Q i) : Set (PlE D.host)) with hSg_def
  have hSg : Sg.Finite := (hP.union (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet
  set Fr : Set (GE D.nd) := {σ | ∃ w ∉ Sg, IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
    IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} with hFr_def
  have hden : closure Fr = Set.univ := hCheb Sg hSg
  have hg : g ∈ closure Fr := by rw [hden]; exact Set.mem_univ g
  haveI := infinite_O D i
  refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
  refine Set.Infinite.mono ?_ Set.infinite_univ
  intro c _
  simp only [Set.mem_setOf_eq]
  haveI : T2Space (D.nd.O i) := by
    have hA := isAdic_iff.mp (D.nd.O_adic i)
    refine IsTopologicalAddGroup.t2Space_of_zero_sep ?_
    intro y hy
    obtain ⟨n, hn⟩ : ∃ n, y ∉ (IsLocalRing.maximalIdeal (D.nd.O i)) ^ n := by
      by_contra hcon
      push_neg at hcon
      apply hy
      refine (D.nd.O_complete i).toIsHausdorff.haus y fun n => ?_
      rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
      exact hcon n
    exact ⟨_, (hA.1 n).mem_nhds (Ideal.zero_mem _), hn⟩
  have hcl := isClosed_det_eq (Finset.Icc 1 D.R.t)
    (fun g => ((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))
    (fun g => ((ρ' g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))
    (fun k g => ((D.nd.chi i k g : (D.nd.O i)ˣ) : D.nd.O i)) hrc hρc (fun k => D.nd.chi_cont i k) c
  have hmain := (hcl.closure_subset_iff.mpr ?_) hg
  · simp only [Set.mem_setOf_eq] at hmain
    rw [Polynomial.eval_mul, Polynomial.eval_prod, Matrix.eval_charpoly, Matrix.eval_charpoly]
    simpa only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hmain
  · rintro σ ⟨w, hw, hs, B, hB, hFb⟩
    have hso : SplitOut D.nd i w :=
      ⟨hs, fun h => hw (Or.inl (Or.inl h)), fun h => hw (Or.inl (Or.inr h)), fun h => hw (Or.inr h)⟩
    have e3 := congrArg (Polynomial.eval c) ((hrF w hso B σ hB hFb).trans (hρF w hso B σ hB hFb).symm)
    rw [Polynomial.eval_mul, Polynomial.eval_prod, Matrix.eval_charpoly, Matrix.eval_charpoly] at e3
    simp only [Set.mem_setOf_eq]
    simpa only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using e3

def rhoChiK (D : D7) (i : D.nd.Loc) (ρ' : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    GE D.nd →* GL (Fin (D.R.r + D.R.t)) (KK D.nd i) :=
  blockRep (mapRep (algebraMap (D.nd.O i) (KK D.nd i)) ρ')
    (diagGL fun c : Fin D.R.t => (Units.map (algebraMap (D.nd.O i) (KK D.nd i)).toMonoidHom).comp
      (D.nd.chi i ((c : ℕ) + 1)))

theorem semisimple_decomposition_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hAN : Formalism.MainNotions.SumRepresentations.adm5 D) (hr : GoodR D.nd i r) (hρ : IsRhoOf D.nd i π (ρ π))
    (hSS : IsSSRep (rhoChiK D i (ρ π))) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π := by
  have hcp : ∀ g, ((r π g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly =
      ((ρ π g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i)) :=
    fun g => charpoly_of_isRhoOf D i r π (ρ π) hAN hr hρ g
  unfold Formalism.MainNotions.SumRepresentations.adm5 Formalism.MainNotions.SumRepresentations.At.JacquetShalikaStrongMultOne at hAN
  have hBN := hAN.2.2.2
  obtain ⟨-, hSS1, -⟩ := hr π
  have hblk : ∀ g, ((rhoChiK D i (ρ π) g : GL _ _) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)) =
      blockHom (KK D.nd i) D.R.r D.R.t
        ((toK D.nd i).mapMatrix ((ρ π g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)),
         Matrix.diagonal fun c : Fin D.R.t =>
           toK D.nd i ((D.nd.chi i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i)) := fun g => rfl
  have hdiag : ∀ d : Fin D.R.t → KK D.nd i, (Matrix.diagonal d).charpoly = ∏ c, (X - C (d c)) := by
    intro d
    first
    | exact Matrix.charpoly_diagonal d
    | (unfold Matrix.charpoly
       rw [show Matrix.charmatrix (Matrix.diagonal d) = Matrix.diagonal fun c => X - C (d c) from by
         ext a b
         by_cases h : a = b <;> simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, h]]
       exact Matrix.det_diagonal)
  obtain ⟨Pm, hPm⟩ := hBN (KK D.nd i) (D.R.r + D.R.t) (mapRep (toK D.nd i) (r π)) (rhoChiK D i (ρ π))
    hSS1 hSS (by
      intro g
      show ((toK D.nd i).mapMatrix ((r π g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))).charpoly =
        (blockHom (KK D.nd i) D.R.r D.R.t
          ((toK D.nd i).mapMatrix ((ρ π g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)),
           Matrix.diagonal fun c : Fin D.R.t =>
             toK D.nd i ((D.nd.chi i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i))).charpoly
      rw [blockHom_charpoly, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.charpoly_map,
        Matrix.charpoly_map, hcp g, Polynomial.map_mul, Polynomial.map_prod, hdiag]
      congr 1
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rw [Fin.prod_univ_eq_prod_range
          (fun c => X - C (toK D.nd i ((D.nd.chi i (c + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) D.R.t,
        Finset.range_eq_Ico,
        Finset.prod_Ico_add' (fun c => X - C (toK D.nd i ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i))),
        zero_add]
      congr 1)
  let e0 : (Fin (D.R.r + D.R.t) → KK D.nd i) ≃ₗ[KK D.nd i] (Fin (D.R.r + D.R.t) → KK D.nd i) :=
    LinearEquiv.ofLinear (Matrix.toLin' ((Pm⁻¹ : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)))
      (Matrix.toLin' ((Pm : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)))
      (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
  refine ⟨e0.trans (splitRT (KK D.nd i) D.R.r D.R.t), ?_⟩
  intro g u
  have hm' := congrArg Units.val (hPm g)
  rw [Units.val_mul, Units.val_mul] at hm'
  have hv : ((Pm⁻¹ : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec ((mapM (toK D.nd i) (rO D.nd i r π) g : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec u) =
      ((rhoChiK D i (ρ π) g : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec (((Pm⁻¹ : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec u) := by
    have key : ∀ (A P Q : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)) (v : Fin (D.R.r + D.R.t) → KK D.nd i), P * Q = 1 →
        (Q * A * P).mulVec (Q.mulVec v) = Q.mulVec (A.mulVec v) := by
      intro A P Q v hPQ
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      simp only [mul_assoc, hPQ, mul_one]
    rw [hm']
    exact (key _ _ _ u (Units.mul_inv Pm)).symm
  show splitRT (KK D.nd i) D.R.r D.R.t (((Pm⁻¹ : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec
      ((mapM (toK D.nd i) (rO D.nd i r π) g : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec u)) = _
  rw [hv, hblk, blockHom_mulVec]
  refine Prod.ext rfl ?_
  funext c
  simp only [Matrix.mulVec_diagonal]
  rfl

end Formalism.MainNotions.N
end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Module

variable {D : D7}

section Cores

variable (L : SizeData₂ D)

def coreE (l : ℕ) : ℝ := 1 + Formalism.MainNotions.TwistedPlaces.hB L / l + Real.logb l (Formalism.MainNotions.TwistedPlaces.hB L)

def coreH (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℝ :=
  ((Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * (Formalism.MainNotions.TwistedPlaces.hB L / (l : ℝ) ^ 2)

open Classical in
def flat (bd : Prop) (l : ℕ) : ℝ :=
  (Formalism.MainNotions.TwistedPlaces.wP L + Formalism.MainNotions.TwistedPlaces.eta₃ L) / l + L.Sc + Formalism.MainNotions.TwistedPlaces.large₂ L +
    Formalism.MainNotions.TwistedPlaces.eta₃ L * (if bd then 1 else 0)

def coreF (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℝ :=
  ((Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * flat L bd l

def coreM (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℝ :=
  (Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) * D.R.m * coreE L l

def bdCD (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) (K₁ K₂ K₃ : ℝ) : ℝ :=
  K₁ * coreH L l lam + K₂ * coreF L bd l lam + K₃ * coreM L l lam

end Cores

structure WordBox (L : SizeData₂ D) {n : ℕ} (Wd : WordDat n) : Prop where
  box_le : ∀ a, ((Wd.Mi a + Wd.hi a : ℕ) : ℝ) ≤ 2 * Formalism.MainNotions.TwistedPlaces.hB L
  nt : ∀ a, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a →
    ∃ s : ℝ, L.sc.w'' D.R.n ≤ s ∧ s ≤ Formalism.MainNotions.TwistedPlaces.wB L ∧ |(Wd.sz a : ℝ) - s| ≤ ((D.R.t : ℝ) + 1) / 2
  b_lo : L.sc.b - ((D.R.t : ℝ) + 1) / 2 ≤ Wd.b
  b_hi : (Wd.b : ℝ) ≤ L.sc.b - ((D.R.t : ℝ) + 1) / 2 + 1

structure WordsNT {n : ℕ} (Wd : WordDat n) : Prop where
  eta_lt : ∀ a, Wd.η < Wd.sz a
  w20 : 20 * Wd.w ≤ Wd.b
  η20 : 20 * Wd.η ≤ Wd.b
  twenty_words_le_b : 20 * Wd.S ≤ Wd.b
  some_nt : ∃ a, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a
  alt : ∀ a, Wd.up (a + 1) ≠ Wd.up a ∧
    ¬ (Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a ∧ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz (a + 1) ∧
      Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz (a + 2))

structure WordsAT (l : ℕ) {n : ℕ} [NeZero n] (Wd : WordDat n) (d : ℕ) : Prop where
  even : Even n
  typ : ∀ a : ZMod n, Wd.up a = true ↔ (a.val + d) % 2 ≠ 0
  thick : ∀ a, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a
  big1 : ∀ a, 2 * Formalism.MainNotions.RamifiedCoefficientChains.aR l (Formalism.MainNotions.RamifiedCoefficientChains.hpar n Wd.sz Wd.S + Wd.η) + (Wd.η : ℝ) + 1 ≤ (Wd.sz a : ℝ)
  big2 : ∀ a, ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n Wd.sz Wd.S : ℕ) : ℝ) / 2 ≤ (Wd.sz a : ℝ)

section Word2

variable {L : SizeData₂ D} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL}

def WordDat.band {n : ℕ} (Wd : WordDat n) (l : ℕ) (CB : ℝ) : Prop :=
  Formalism.MainNotions.TruncatedSeriesCountingBounds.Band l Wd.b Wd.S Wd.η Wd.sz
    (Real.logb l (2 * ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℕ) : ℝ))) CB

end Word2

attribute [local instance] nLet_neZero

section Word3

variable {L : SizeData₂ D} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL}


variable (ρ π hG) in
structure WordBaseC (Wd : WordDat (nLet i w hw)) : Prop where
  zeta : ∃ ζ : ↥Cx.LL.1, IsPrimitiveRoot ζ (D.nd.l i)
  mult : ∀ T₂ : LatW i w hw Cx, IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ →
    ∀ (a : ZMod (nLet i w hw)) (τ : ↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1),
      Formalism.MainNotions.LiftingTheory.Over (WW HW i w hw Cx hG) τ a →
      ∑ x ∈ Finset.Icc (-(Wd.η : ℤ)) (Wd.η : ℤ),
        multV ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₂.ρ τ x ≤ (Wd.m : ℤ)

end Word3

section RowCD

variable (L : SizeData₂ D)

def LocalRepresentationCongruenceCondition (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL),
      ∃ Wd : WordDat (nLet i w hw), WordBase L HW i r ρ π w hw Cx hG Wd ∧ WordBox L Wd ∧
        (WordsNT Wd ∨ (WordBaseC (HW := HW) ρ π hG Wd ∧ ∃ d, WordsAT (D.nd.l i) Wd d))

def bandOf (HW : HWOf D.loc) (CB : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (lam : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  11 ≤ D.nd.l i ∧ ∃ π ∈ D.nd.Zgood i, ∃ (hw : lam ∈ placesOver D.host.E (D.nd.l i))
    (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i lam hw) (hG : Good (D.nbr i lam hw).Kw 1 Cx.LL)
    (Wd : WordDat (nLet i lam hw)), WordBase L HW i r ρ π lam hw Cx hG Wd ∧ WordBox L Wd ∧ WordsNT Wd ∧
      Wd.band (D.nd.l i) CB

def lenRowCD (bd : HeightOneSpectrum (𝓞 D.host.E) → Prop) (K₁ K₂ K₃ : ℝ) (l : ℕ)
    (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  ratIn (bdCD L (bd lam) l lam K₁ K₂ K₃) (bdCD L (bd lam) l lam K₁ (K₂ + 1) K₃)

variable (tb : Formalism.MainNotions.TwistedPlaces.Tab L)
  (len0 : ∀ i : D.nd.Loc, D.nd.X i → HeightOneSpectrum (𝓞 D.host.E) → ℝ)

end RowCD

end Formalism.MainNotions.N

end
end
