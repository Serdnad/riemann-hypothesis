module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle010
public import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.AbsIrrOfSpan
public import Formalism.PadicSubsetSums.StableGradedCounts.ARCReuse
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.OrderOfVanishing.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.HerrComplexNaturality

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def FN (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.adm9 D HW F

def HerrNaturality (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm17 D HW F

def AdmNat (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F

def HerrNaturalityTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmNat D HW F → HerrNaturality D HW F

theorem herr_naturality_theorem_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrNaturalityTheorem D HW F := by
  intro h l _ K s LL g
  refine ⟨(h l K s LL g).2.2, ?_⟩
  intro hg T T' f pr pr' hp
  have h1 := (h l K s LL g).1 hg T
  exact (h1.2.2 T' f pr pr' hp).symm

def HerrExtensionClass (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm16 D HW F

def HerrExtensionUpToUnit (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.ElementDenominator.coreHerrExt ((HW l).W K s LL h) ∧ Formalism.MainNotions.ElementDenominator.coreHerrExtΔ ((HW l).W K s LL h)

theorem herr_class_maps_of_naturality (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h1 : HerrNaturality D HW F) (h2 : HerrExtensionUpToUnit D HW F) : Formalism.MainNotions.ElementDenominator.HerrClassMapsLocal D HW F :=
  fun l _ K s LL h => ⟨(h1 l K s LL h).1, (h1 l K s LL h).2, (h2 l K s LL h).1, (h2 l K s LL h).2⟩

end Formalism.MainNotions.HerrComplexNaturality
end
end

section

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)

theorem card_blk (r t : ℕ) (c : Fin (t + 1)) (hc : c ≠ 0) :
    Fintype.card {a : Fin (r + t) // blkG r t a = c} = 1 := by
  rw [Fintype.card_eq_one_iff]
  have hc1 : 1 ≤ (c : ℕ) := by
    rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
    · exact absurd (Fin.ext h) hc
    · exact h
  have hct := c.isLt
  refine ⟨⟨⟨r + ((c : ℕ) - 1), by omega⟩, ?_⟩, ?_⟩
  · unfold blkG
    rw [dite_eq_right (by simp)]
    exact Fin.ext (by simp; omega)
  · rintro ⟨a, ha⟩
    apply Subtype.ext
    unfold blkG at ha
    split_ifs at ha with h
    · exact absurd ha.symm hc
    · have h2 := congrArg Fin.val ha
      simp at h2
      exact Fin.ext (by simp; omega)

theorem exists_natAdd (r t : ℕ) (a : Fin (r + t)) (ha : blkG r t a ≠ 0) :
    ∃ c : Fin t, a = Fin.natAdd r c := by
  unfold blkG at ha
  split_ifs at ha with h
  · exact absurd rfl ha
  · exact ⟨⟨(a : ℕ) - r, by have := a.2; omega⟩, Fin.ext (by simp; omega)⟩

theorem primHyp_of (hN : NormAt N r ρ π)
    (hG1 : ∀ (γ : GE N) (k : ℕ), (fun x : N.X i => ((rO N i r x γ).charpolyRev).coeff k) ∈ N.T i) :
    PrimHyp (N.O i) (N.T i) (repX N r) π (blk R) (chiU N i 1) (epsU N i) := by
  obtain ⟨hbd, hχ, -⟩ := hN
  refine ⟨N.T_local i, N.T_sep i, hG1, hbd, fun c hc => card_blk R.r R.t c hc, fun g a ha => ?_⟩
  obtain ⟨c, rfl⟩ := exists_natAdd R.r R.t a ha
  have h1 : ((blk R (Fin.natAdd R.r c) : Fin (R.t + 1)) : ℕ) - 1 = (c : ℕ) := by
    rw [show blk R (Fin.natAdd R.r c) = c.succ from blkG_natAdd R.r R.t c]
    simp
  rw [h1]
  refine (hχ g c).trans ?_
  have h2 := N.chi_def i ((c : ℕ) + 1) (by omega) (by have := c.2; omega)
  have h3 : chiU N i ((c : ℕ) + 1) g = chiU N i 1 g * ((epsU N i g)⁻¹ ^ (c : ℕ)) := by
    show N.chi i ((c : ℕ) + 1) g = _
    rw [h2, MonoidHom.mul_apply]
    congr 1
    have h4 : (-(((((c : ℕ) + 1 : ℕ) : ℤ)) - 1)) = -((c : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h4, _root_.zpow_neg, zpow_natCast, MonoidHom.inv_apply, MonoidHom.pow_apply, inv_pow]
    rfl
  rw [h3]
  simp

def InertiaElementIdempotentChoice : Prop :=
  ∃ g0 : GE N, (∃ w ∈ placesOver H.E (N.l i), g0 ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
    (∃ u : ℤ_[N.l i]ˣ, ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
      1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * (u : ℤ_[N.l i])) ∧
    ∃ eB e₁ s : N.X i → MatN N i, IdemHyp (N.O i) (N.T i) (repX N r) π (blk R) eB e₁ ∧
      DistinctEigenvalueCornerPerturbation (N.O i) (N.T i) (repX N r) π R.t g0 eB s

end Formalism.MainNotions.N.RepresentationBoundsCohomology

namespace Formalism.MainNotions.LargeLevelLemmas

open Formalism.MainNotions.N Formalism.MainNotions.N.RepresentationBoundsCohomology

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* Matrix.GeneralLinearGroup (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* Matrix.GeneralLinearGroup (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

end Formalism.MainNotions.LargeLevelLemmas

end
end

section

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.NG

def blockZeroEquiv (r t : ℕ) : Fin r ≃ {a : Fin (r + t) // blkG r t a = 0} where
  toFun a := ⟨Fin.castAdd t a, blkG_castAdd r t a⟩
  invFun y := ⟨(y.1 : ℕ), by
    have h := y.2
    unfold blkG at h
    split_ifs at h with h1
    · exact h1
    · exact absurd h (by simp [Fin.ext_iff])⟩
  left_inv a := by
    ext
    rfl
  right_inv y := by
    apply Subtype.ext
    ext
    rfl

theorem absIrr_block {k G : Type} [Field k] {r t : ℕ} (M : G → Matrix (Fin (r + t)) (Fin (r + t)) k)
    (ρb : G → Matrix (Fin r) (Fin r) k)
    (h : ∀ g a b, M g (Fin.castAdd t a) (Fin.castAdd t b) = ρb g a b)
    (hs : Submodule.span k (Set.range ρb) = ⊤) :
    AbsIrr (fun g => (M g).toSquareBlock (blkG r t) 0) := by
  apply absIrr_of_span
  intro a b
  let L := Matrix.reindexLinearEquiv k k (blockZeroEquiv r t) (blockZeroEquiv r t)
  have hL : ∀ g, L (ρb g) = (M g).toSquareBlock (blkG r t) 0 := by
    intro g
    ext x y
    obtain ⟨x', rfl⟩ := (blockZeroEquiv r t).surjective x
    obtain ⟨y', rfl⟩ := (blockZeroEquiv r t).surjective y
    simp only [L, Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply]
    exact (h g x' y').symm
  have h1 : L.symm (Matrix.single a b (1 : k)) ∈ Submodule.span k (Set.range ρb) := by
    rw [hs]
    exact Submodule.mem_top
  have h2 := Submodule.mem_map_of_mem (f := L.toLinearMap) h1
  rw [Submodule.map_span] at h2
  have h3 : L.toLinearMap (L.symm (Matrix.single a b (1 : k))) = Matrix.single a b (1 : k) :=
    L.apply_symm_apply _
  rw [h3] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  exact ⟨g, (hL g).symm⟩

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)

theorem one_le_letterBlockLength (R : Ranks) : 1 ≤ R.t := by
  have h := R.rank_add_five_le
  omega

theorem absIrr_of_res (hN : NormAt N r ρ π)
    (hres : Submodule.span (kk N i)
      (Set.range (mapM (IsLocalRing.residue (N.O i)) (rhoO N i ρ π))) = ⊤) :
    AbsIrr (fun g => ((repX N r g π).toSquareBlock (blk R) 0).map (IsLocalRing.residue (N.O i))) :=
  absIrr_block (r := R.r) (t := R.t) (fun g => (rO N i r π g).map (IsLocalRing.residue (N.O i)))
    (fun g => mapM (IsLocalRing.residue (N.O i)) (rhoO N i ρ π) g)
    (fun g a b => congrArg (IsLocalRing.residue (N.O i)) (hN.2.2 g a b)) hres

end Formalism.MainNotions.N.RepresentationBoundsCohomology

end
end

section

noncomputable section

namespace Formalism.MainNotions.ElementDenominator

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Orbit

variable {G LL : Type} [Group G] [Field LL] (I : Subgroup G) [hI : I.Normal] (Fr : G)

end Orbit

section Iner

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)

end Iner

section PartII

variable {l : ℕ} [Fact l.Prime]
    {K₀' K' B BdR : Type} [Field K₀'] [Field K'] [Algebra ℚ_[l] K₀'] [Algebra ℚ_[l] K']
    [Algebra K₀' K'] [IsScalarTower ℚ_[l] K₀' K'] [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B]
    [Algebra ↥(K0 (qlExt l)) B] [IsScalarTower ℚ_[l] ↥(K0 (qlExt l)) B] [Algebra K₀' B]
    [IsScalarTower ℚ_[l] K₀' B] [Algebra ℚ_[l] BdR] [Algebra ↥(K0 (qlExt l)) BdR]
    [Algebra ↥(qlExt l).1 BdR] [IsScalarTower ℚ_[l] ↥(qlExt l).1 BdR]
    [IsScalarTower ↥(K0 (qlExt l)) ↥(qlExt l).1 BdR] [IsScalarTower ℚ_[l] ↥(K0 (qlExt l)) BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower ℚ_[l] K' BdR] [IsScalarTower K₀' K' BdR]
    [IsScalarTower ℚ_[l] K₀' BdR]
    (PC : PotCrysData ↥(GK (qlExt l)) ℚ_[l] ↥(K0 (qlExt l)) ↥(qlExt l).1 K₀' K' B BdR)
    (LL : FinExt l)

def HypT (T₁ T₂ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (N η H : ℕ)
    (U : Finset ℤ) (Sig : Finset (PC.Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK (qlExt l))) : Prop :=
  PC.IsPotCrys T₁.ρ ∧ PC.IsPotCrys T₂.ρ ∧ F.Onto ∧
    PC.IsFrob Fr ∧ FrobStable PC.Iner Fr Sig ∧ 1 ∈ Sig ∧ Sig.card ≤ N ∧ 2 ≤ N ∧
    PC.InertiaThrough T₁.ρ Sig ∧ PC.InertiaThrough T₂.ρ Sig ∧
    (∀ u ∈ U, -(η : ℤ) ≤ u ∧ u ≤ H) ∧ (0 : ℤ) ∈ U ∧ U.card ≤ N + 1 ∧ 1 ≤ η ∧ η < H ∧
    (∀ τ, JumpsInV PC.PD T₁.ρ τ (U : Set ℤ)) ∧ (∀ τ, JumpsInV PC.PD T₂.ρ τ (U : Set ℤ))

def thmTLift (C : ℕ) : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (N η H : ℕ)
    (U : Finset ℤ) (Sig : Finset (PC.Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK (qlExt l))),
    HypT PC LL T₁ T₂ F N η H U Sig Fr → C * (H * N ^ 2 + N ^ 3) < l →
      F.LiftF PC.PD (C * (N * rPrime PC.Iner Fr Sig + η * (N + rPrime PC.Iner Fr Sig)))

variable {PC LL}

variable (PC LL)

end PartII

def LiftingClause (D : D7) (C : ℕ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K' : FinExt l) (h : (qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (qlExt l))) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc l).PD (qlExt l)).actB g (algebraMap ↥(K0 K') (D.loc l).R.B c) =
        algebraMap ↥(K0 K') (D.loc l).R.B c')
    (LL : FinExt l), thmTLift (pc (D.loc l) h hN hF hS) LL C

def TwoStep {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (l g g₀ e e' : ℕ)
    (Z Bc I : Submodule O M) : Prop :=
  ∃ s s₀ : Finset M, s.card ≤ g ∧ Submodule.span O (s : Set M) ⊔ Bc = Z ∧
    s₀.card ≤ g₀ ∧ (s₀ : Set M) ⊆ Z ∧
    (∀ p ∈ Z, (l ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) ∧
    (∀ p ∈ Submodule.span O (s₀ : Set M), (l ^ e' : ℕ) • p ∈ I)

theorem len_ne_top {O : Type} [CommRing O] [IsDedekindDomain O] (x : O) (h : x ≠ 0) :
    Module.length O (O ⧸ Ideal.span {x}) ≠ ⊤ := by
  rw [Module.length_ne_top_iff]
  apply isFiniteLength_quotient_span_singleton
  rwa [mem_nonZeroDivisors_iff_ne_zero]

theorem len_le_nat {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (l p g g₀ y e' k : ℕ)
    (Z Bc I : Submodule O M) (h : TwoStep l g g₀ y e' Z Bc I) (hB : Bc ≤ I) (hp : p = l)
    (hk : Module.length O (O ⧸ Ideal.span {((p : ℕ) : O)}) = (k : ℕ∞)) :
    ∃ m : ℕ, Module.length O (↥Z ⧸ I.comap Z.subtype) = (m : ℕ∞) ∧ m ≤ (g * y + g₀ * e') * k := by
  subst hp
  obtain ⟨s, s₀, hs, hgen, hs₀, hsub, h1, h2⟩ := h
  have key := Formalism.IrreducibleCountingLemmas.WindowSums.colength_bound_two_layers O M p g g₀ y e' Z Bc I s s₀ hs hgen hB hs₀ hsub h1 h2
  rw [hk] at key
  have hcol : Module.length O (↥Z ⧸ I.comap Z.subtype) ≤ (((g * y + g₀ * e') * k : ℕ) : ℕ∞) := by
    push_cast
    exact key
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hcol)
  refine ⟨m, hm.symm, ?_⟩
  rw [← hm] at hcol
  exact_mod_cast hcol

section PartI

variable {l : ℕ} [Fact l.Prime]

theorem lenOl_finite (P : LocPrime l) (K LL : FinExt l) :
    ∃ k : ℕ, lenOl (P.PD K) (O := ↥(OL LL)) = (k : ℕ∞) := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsDedekindDomain ↥(OL LL) := integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1
  have hne : lenOl (P.PD K) (O := ↥(OL LL)) ≠ ⊤ := by
    apply len_ne_top
    rw [P.PD_p K]
    intro h
    have h2 := congrArg (Subtype.val : ↥(OL LL) → ↥LL.1) h
    have h3 : ((l : ℕ) : ↥LL.1) = 0 := by simpa using h2
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h3)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
  exact ⟨k, hk.symm⟩

theorem colLe_mono (P : LocPrime l) (K LL : FinExt l) {T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)}
    (F : LatHom T₁.L T₂.L) {b b' : ℝ} (hb : b ≤ b') (h : colLe P K LL F b) : colLe P K LL F b' := by
  obtain ⟨m, k, h1, h2, h3⟩ := h
  exact ⟨m, k, h1, h2, h3.trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg k))⟩

theorem colLe_of_twoStep (P : LocPrime l) (K LL : FinExt l)
    {T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)} (F : LatHom T₁.L T₂.L) (g g₀ y e' : ℕ)
    (h : TwoStep l g g₀ y e' (latticeFiniteCocycles (P.PD K) T₂.L) (latticeCoboundaries T₂.L) (F.ImF (P.PD K))) :
    colLe P K LL F ((g : ℝ) * y + (g₀ : ℝ) * e') := by
  obtain ⟨k, hk⟩ := lenOl_finite P K LL
  obtain ⟨m, hm, hmk⟩ := len_le_nat l (P.PD K).p g g₀ y e' k _ _ _ h le_sup_right (P.PD_p K) hk
  refine ⟨m, k, hm, hk, ?_⟩
  exact_mod_cast hmk

def HypA (P : LocPrime l) (K LL : FinExt l) (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (F : LatHom T₁.L T₂.L) (r S η m h : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
    (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) : Prop :=
  IsCrys (P.PD K) T₁.ρ ∧ IsCrys (P.PD K) T₂.ρ ∧ F.Onto ∧
    finrank ↥LL.1 T₂.V = r ∧
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) ∧
    (∀ τ, η < b τ) ∧
    (∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) T₂.ρ τ a ≤ m) ∧
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) ∧
    (finrank ↥(K0 K) ↥K.1 = 2 ∨ ∀ τ τ', intersection_update_fsHerm_neg_one K τ = intersection_update_fsHerm_neg_one K τ' → up τ = up τ')

end PartI

end Formalism.MainNotions.ElementDenominator

end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.LocalTheoryWindows

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

inductive LT where
  | thin : LT
  | up (b : ℕ) : LT
  | down (b : ℕ) : LT
  deriving DecidableEq

def LT.thick : LT → Bool
  | .thin => false
  | _ => true

def LT.isUp : LT → Bool
  | .up _ => true
  | _ => false

def LT.isDown : LT → Bool
  | .down _ => true
  | _ => false

def LT.size : LT → ℕ
  | .thin => 0
  | .up b => b
  | .down b => b

def LT.win (G S η : ℕ) : LT → Set ℤ
  | .thin => Set.Icc (-(G : ℤ)) G
  | .up b => Set.Icc (b : ℤ) (b + S) ∪ Set.Icc (-(η : ℤ)) η
  | .down b => Set.Icc (-(b : ℤ) - S) (-(b : ℤ)) ∪ Set.Icc (-(η : ℤ)) η

def LT.ok (η : ℕ) : LT → Prop
  | .thin => True
  | .up b => η < b
  | .down b => η < b

def CutsOK (n j : ℕ) (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) : Prop :=
  cuts.Nonempty ∧ 1 ≤ j ∧
    (∀ c ∈ cuts, 1 ≤ arcLen c ∧ arcLen c ≤ n ∧ c - ((arcLen c : ℕ) : ZMod n) ∈ cuts ∧
      ∀ d : ℕ, 1 ≤ d → d < arcLen c → c - (d : ZMod n) ∉ cuts) ∧
    (∀ c ∈ cuts, j ≤ arcLen c) ∧
    (∀ c ∈ cuts, ∀ k : ℕ, 1 ≤ k → k ≤ j → ty (c + (k : ZMod n)) = LT.thin)

def thickLv {n : ℕ} (ty : ZMod n → LT) (arcLen : ZMod n → ℕ) (c : ZMod n) : Finset ℕ :=
  (Finset.range (arcLen c)).filter fun s => (ty (c - (s : ZMod n))).thick

def ro {n : ℕ} (ty : ZMod n → LT) (arcLen : ZMod n → ℕ) (c : ZMod n) : ℕ :=
  (thickLv ty arcLen c).card

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end Core

section Lit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {Bc BdR : Type} [CommRing Bc] [CommRing BdR] [Algebra Qp Bc] [Algebra K₀ Bc]
    [IsScalarTower Qp K₀ Bc] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

def H1fGeneratorBound (PD : PeriodData G Qp K₀ K Bc BdR) (LL O : Type) [Field LL] [Algebra Qp LL]
    [TopologicalSpace LL] [CommRing O] [Algebra O LL] : Prop :=
  Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBound PD LL O

end Lit

section Theory

def H1fGeneratorBoundAll (Th : LocTheory) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBoundAll Th

end Theory

end Formalism.MainNotions.LocalTheoryWindows
end
end
