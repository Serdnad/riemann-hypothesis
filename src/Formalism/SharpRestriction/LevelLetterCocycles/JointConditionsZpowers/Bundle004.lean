module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Charpoly.Basic

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

def GlobalDatumCompatibility (D : D7) : Prop :=
  Formalism.MainNotions.SphericalInertData.HypEFK D ∧
    (2 ≤ Module.finrank ℚ D.host.F ∧
      ∀ w : PlE D.host, ¬ IsSplitPl D.host w → ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) ∧
    ∀ j, 1 ≤ j → j ≤ D.R.m → (letI := D.host.cmStar; (D.sp.V j).IsDefinite)

theorem nV_pos (D : D7) : 1 ≤ D.R.nV := by
  have := D.R.t_odd.pos
  show 1 ≤ D.R.r + D.R.t
  omega

theorem hypCM_of (D : D7) (hc : GlobalDatumCompatibility D) : Formalism.MainNotions.SphericalInertData.HypCM D := by
  refine ⟨?_, hc.2.1⟩
  letI := D.host.cmStar
  exact D.sp.cm.cmUnram

theorem base_change_automorphic_of (D : D7) (h45 : Formalism.MainNotions.SphericalInertData.Conclusion1 D) (hc : GlobalDatumCompatibility D) :
    Formalism.MainNotions.SumRepresentations.adm1 D := by
  intro i P
  obtain ⟨Pa, h1, h2, h3, h4, h5, h6⟩ :=
    h45 hc.1 (hypCM_of D hc) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (nV_pos D)
      (hc.2.2 _ (D.nd.j_range i).1 (D.nd.j_range i).2) (D.nbc.embAV i P)
      (fun w hw => D.nbc.embAV_sph i P w hw)
  refine ⟨Pa, h1, h2, h3, fun w hw => (h4 w hw).trans (D.nbc.embAV_loc i P w).symm,
    fun w hw => ⟨(h5 w hw).1, (h5 w hw).2.trans (congrArg _ (D.nbc.embAV_sat i P w).symm)⟩,
    fun τ => (h6 τ).trans (congrFun (D.nbc.embAV_inf i P) τ).symm⟩

def LitBNIrr (Γ : Type) [Group Γ] : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)),
    (∀ g, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)).charpoly =
      ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)).charpoly) →
    Formalism.CyclotomicNorms.IrredOn ρ' ⊤ → Formalism.CyclotomicNorms.IrredOn ρ ⊤

theorem charpoly_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ}
    (f : A →+* B) (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL _ _) : Matrix (Fin a) (Fin a) B).charpoly =
      (((ρ g : GL _ _) : Matrix (Fin a) (Fin a) A).charpoly).map f :=
  Matrix.charpoly_map _ f

end Formalism.MainNotions.N
end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

open NumberField IsDedekindDomain

section H0

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def tTwoLocalLattice {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hc : ∀ v, Continuous fun g => matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) g v)
    (L2 : Lattice (O := ↥(OL C.LL)) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)))) :
    LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
  { V := Fin D.R.r → ↥C.LL.1, ρ := matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)), cont := hc, L := L2 }

end H0

end Formalism.MainNotions.N
end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

open NumberField IsDedekindDomain

theorem locC_rTwO (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x) =
      twistM (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (Formalism.MainNotions.TruncatedSeriesCountingIdentities.chi1C C)⁻¹ := by
  apply MonoidHom.ext
  intro g
  apply Matrix.ext
  intro a b
  have key : ∀ u v : D.nd.O i, C.inc ((D.nbr i w hw).toLL (u * v)) =
      C.inc ((D.nbr i w hw).toLL u) * C.inc ((D.nbr i w hw).toLL v) := by
    intro u v
    rw [map_mul, map_mul]
  exact key _ _

theorem locC_cont (D : D7) (i : D.nd.Loc) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (v : Fin k → ↥C.LL.1) :
    Continuous fun g => (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C M g).mulVec v := by
  have hmat : Continuous fun g => Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C M g := by
    refine continuous_matrix fun a b => ?_
    have h1 : Continuous fun g : Br.G D.nbr i w hw => M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) a b :=
      (hM.matrix_elem a b).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
    have h2 : Continuous fun y : D.nd.O i => (((D.nbr i w hw).eO y : ↥(OL (D.nbr i w hw).LL)) :
        ↥(D.nbr i w hw).LL.1) := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
    have h3 : Continuous fun y : ↥(D.nbr i w hw).LL.1 => C.inc y :=
      Continuous.subtype_mk continuous_subtype_val _
    exact h3.comp (h2.comp h1)
  exact hmat.matrix_mulVec continuous_const

theorem rTwO_cont (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (x : D.nd.X i) : Continuous fun g => rTwO D.nd i r x g := by
  have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [map_inv]
      rfl
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  exact h1.smul (hr x)

end Formalism.MainNotions.N
end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

theorem continuous_family_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r := by
  intro x
  exact (hr x).1

theorem semisimple_family_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admSS (D := D) i r := by
  intro x W hW
  obtain ⟨W', hW', hc⟩ := (hr x).2.1 W hW
  exact ⟨W', hW', hc⟩

theorem coefficient_compatibility_of (D : D7) (i : D.nd.Loc)
    (hdeg : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), Br.DegW D.nbr i w hw) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility (D := D) i := by
  intro w hw
  exact ⟨(D.nbr i w hw).eO_alg, ⟨(D.nbr i w hw).eO_cont, (D.nbr i w hw).eO_symm_cont⟩, hdeg w hw⟩

theorem isOpen_ker_redRep (D : D7) (a : D.nd.Loc) {n : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin n) (D.nd.O a))
    (h : Continuous (fun g => ((ρ g : GL (Fin n) (D.nd.O a)) : Matrix (Fin n) (Fin n) (D.nd.O a)))) :
    IsOpen ((redRep D.nd a ρ).ker : Set (G D.host.E D.nd.Om)) := by
  have hm : IsOpen ((IsLocalRing.maximalIdeal (D.nd.O a) : Ideal (D.nd.O a)) : Set (D.nd.O a)) := by
    simpa using (isAdic_iff.mp (D.nd.O_adic a)).1 1
  have hset : ((redRep D.nd a ρ).ker : Set (G D.host.E D.nd.Om)) =
      ⋂ i, ⋂ j, (fun g => ((ρ g : GL (Fin n) (D.nd.O a)) : Matrix (Fin n) (Fin n) (D.nd.O a)) i j -
        (1 : Matrix (Fin n) (Fin n) (D.nd.O a)) i j) ⁻¹'
        ((IsLocalRing.maximalIdeal (D.nd.O a) : Ideal (D.nd.O a)) : Set (D.nd.O a)) := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage]
    rw [Units.ext_iff, ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    have h1 : ((1 : GL (Fin n) (IsLocalRing.ResidueField (D.nd.O a))) :
        Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField (D.nd.O a))) i j =
        IsLocalRing.residue (D.nd.O a) ((1 : Matrix (Fin n) (Fin n) (D.nd.O a)) i j) := by
      rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [h1]
    exact Ideal.Quotient.eq
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact hm.preimage ((h.matrix_elem i j).sub continuous_const)

theorem charpoly_of_decomp (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hdec : Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π) (g : GE D.nd) :
    (rO D.nd i r π g).charpoly = (rhoO D.nd i ρ π g).charpoly *
      ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i)) := by
  obtain ⟨e, he⟩ := hdec
  apply Polynomial.map_injective (toK D.nd i) (IsFractionRing.injective (D.nd.O i) (KK D.nd i))
  rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  show (mapM (toK D.nd i) (rO D.nd i r π) g).charpoly = (mapM (toK D.nd i) (rhoO D.nd i ρ π) g).charpoly *
    ∏ c ∈ Finset.Icc 1 D.R.t, (X - C (toK D.nd i ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i)))

  have hmat : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin m) (KK D.nd i)), (Matrix.toLin' M).charpoly = M.charpoly := by
    intro m M
    rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' M) (Pi.basisFun (KK D.nd i) (Fin m)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

  have hconj : e.conj (Matrix.toLin' (mapM (toK D.nd i) (rO D.nd i r π) g)) =
      (Matrix.toLin' (mapM (toK D.nd i) (rhoO D.nd i ρ π) g)).prodMap
        (Matrix.toLin' (Matrix.diagonal fun c : Fin D.R.t =>
          toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) := by
    apply LinearMap.ext
    intro p
    obtain ⟨u, rfl⟩ := e.surjective p
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Matrix.toLin'_apply, LinearMap.prodMap_apply]
    rw [he g u]
    refine Prod.ext rfl (funext fun c => ?_)
    simp [Matrix.mulVec_diagonal]
  have hdiag : (Matrix.diagonal fun c : Fin D.R.t =>
      toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i)).charpoly =
      ∏ c : Fin D.R.t, (X - C (toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) := by
    have hch : Matrix.charmatrix (Matrix.diagonal fun c : Fin D.R.t =>
        toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i)) =
        Matrix.diagonal fun c : Fin D.R.t =>
          (X - C (toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [Matrix.charmatrix_apply]
      · simp [Matrix.charmatrix_apply, hab, Matrix.diagonal_apply_ne _ hab]
    rw [Matrix.charpoly, hch, Matrix.det_diagonal]

  have hidx : ∏ c : Fin D.R.t, (X - C (toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) =
      ∏ c ∈ Finset.Icc 1 D.R.t, (X - C (toK D.nd i ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))) := by
    rw [Fin.prod_univ_eq_prod_range (fun c => X - C (toK D.nd i ((chiU D.nd i (c + 1) g : (D.nd.O i)ˣ) : D.nd.O i))),
      Finset.range_eq_Ico,
      Finset.prod_Ico_add' (fun c => X - C (toK D.nd i ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))) 0 D.R.t 1]
    congr 1
  rw [← hmat, ← LinearEquiv.charpoly_conj e, hconj, LinearMap.charpoly_prodMap, hmat, hmat, hdiag, hidx]

def AbsIrreducibleDistinct (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ x, AbsIrrDistinct (repK D.nd i r x)

end Formalism.MainNotions.N
end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Module

def CrysOnCond (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (Y : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) Y.ρ →
    Formalism.MainNotions.LocalSituation.IsCrysOn (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL h)
      (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL h).W.GKs Y

end Formalism.MainNotions.N
end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem dimension_input_one_of_bloch_kato (D : D7) (h : Formalism.MainNotions.LocalSituation.Conclusion5 D) : Formalism.MainNotions.BlochKatoDuality.adm1 D := by
  intro l _ K
  exact (h l K).1

theorem dimension_input_two_of_bloch_kato (D : D7) (h : Formalism.MainNotions.LocalSituation.Conclusion5 D) : Formalism.MainNotions.BlochKatoDuality.adm2 D := by
  intro l _ K
  exact (h l K).2.2.2.1

end Formalism.MainNotions.N
end
end
