module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle270
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle271
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Divisibility.Bundle001
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin.TypeSum

theorem orth_ker_eq_range_adjoint {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (A : V →ₗ[ℂ] W) : (LinearMap.ker A)ᗮ = LinearMap.range (LinearMap.adjoint A) := by
  have h : (LinearMap.range (LinearMap.adjoint A))ᗮ = LinearMap.ker A := by
    ext x
    simp only [Submodule.mem_orthogonal, LinearMap.mem_range, LinearMap.mem_ker, forall_exists_index,
      forall_apply_eq_imp_iff, LinearMap.adjoint_inner_left]
    constructor
    · intro hx
      exact ext_inner_left ℂ (fun y => by rw [hx y, inner_zero_right])
    · intro hx y
      rw [hx, inner_zero_right]
  rw [← h, Submodule.orthogonal_orthogonal]

variable {D : D7}

def eqvMt {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) :
    D.what₂.Mt μ' j' ≃ₗ[ℂ] D.what₂.Mt μ j := by
  subst hμ; subst hj; exact LinearEquiv.refl ℂ _

theorem map_eqvMt_self {μ : D.what₂.Tup} {j : ℕ} (hμ : μ = μ) (hj : j = j) (V : Submodule ℂ (D.what₂.Mt μ j)) :
    V.map (eqvMt hμ hj).toLinearMap = V :=
  Submodule.map_id V

theorem map_eqvMt_thetaT_isot {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) (σ : D.what₂.FT) :
    ((D.what₂.isot j' σ).map (D.what₂.thetaT μ' j')).map (eqvMt hμ hj).toLinearMap =
      (D.what₂.isot j σ).map (D.what₂.thetaT μ j) := by
  subst hμ; subst hj; exact map_eqvMt_self _ _ _

theorem map_eqvMt_range_thetaT {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) :
    (LinearMap.range (D.what₂.thetaT μ' j')).map (eqvMt hμ hj).toLinearMap =
      LinearMap.range (D.what₂.thetaT μ j) := by
  subst hμ; subst hj; exact map_eqvMt_self _ _ _

theorem isoTyp_eq_of_isoRep {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) {S S' : Submodule ℂ (GAf L n → W)}
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) (h : NG.IsoRep S S') : NG.isoTyp ρ S = NG.isoTyp ρ S' := by
  unfold NG.isoTyp
  congr 1
  ext T
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (h.symm hS).trans h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h.trans h2⟩⟩

variable {M : MtFam D}

theorem typeV_of_transport (A : AVTied D M) (i : D.nd.Loc) {μ' : D.what₂.Tup} {j' : ℕ}
    (hμ : μ' = D.nd.mu i) (hj : j' = D.nd.j i) (h1 : 1 ≤ j') (h2 : j' ≤ D.R.m)
    (S' : Submodule ℂ (GAf D.host.E D.R.nV → (M μ' j' h1 h2).wt.W))
    (hirr : NG.IsIrrRep (M μ' j' h1 h2).wt.ρ S')
    (hne : (NG.isoTyp (M μ' j' h1 h2).wt.ρ S').comap (M μ' j' h1 h2).real ≠ ⊥) :
    ∃ P, ((NG.isoTyp (M μ' j' h1 h2).wt.ρ S').comap (M μ' j' h1 h2).real).map (eqvMt hμ hj).toLinearMap =
      D.naut.typeV i P := by
  subst hμ; subst hj
  obtain ⟨P, hP⟩ := A.surj i S' hirr hne
  refine ⟨P, ?_⟩
  have e := isoTyp_eq_of_isoRep (M.loc i).wt.ρ (A.irr i P).1.stable hP
  rw [map_eqvMt_self, A.typeV i P, e]
  rfl

theorem eig_of_transport (A : AVTied D M) (i : D.nd.Loc) (P : D.naut.AV i) (x : D.nd.X i)
    (hx : D.naut.ptV i P = some x) {μ' : D.what₂.Tup} {j' : ℕ}
    (hμ : μ' = D.nd.mu i) (hj : j' = D.nd.j i) (h1 : 1 ≤ j') (h2 : j' ≤ D.R.m)
    (V : Submodule ℂ (D.what₂.Mt μ' j')) (hV : V.map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P)
    (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E))
    (hw : SplitOut D.nd i w) (hc : IsConjPl D.host w s.w) (hu : IsUnif D.host.E s.v ϖ) (k1 : 1 ≤ k)
    (k2 : k ≤ D.R.nV) (c : ℂ)
    (hV' : ∀ y ∈ V, NG.tN (M μ' j' h1 h2).J s ϖ k ((M μ' j' h1 h2).real y) = c • (M μ' j' h1 h2).real y) :
    c = iotaOC D i ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x) := by
  subst hμ; subst hj
  rw [map_eqvMt_self] at hV
  subst hV
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i P)
  have e1 := A.eigen i P x hx w k s ϖ hw hc hu k1 k2 y hy
  have e2 := hV' y hy
  have hr : (M.loc i).real y ≠ 0 := fun h => hy0 ((M.loc i).real_inj (h.trans (map_zero _).symm))
  exact smul_left_injective ℂ hr (e2.symm.trans e1)

end GlobalTheory.EtaJoin.TypeSum

namespace GlobalTheory.EtaJoin.TypeSum

theorem main : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → AVTied D M → SplitUnif D → TypeOrth D i →
    ThetaCut D (D.nd.mu i) (D.nd.j i) → Rows.IsotInternal D.what₂ → Formalism.MainNotions.SumRepresentations.ConclusionZ D →
    (∀ σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i),
      Formalism.MainNotions.N.HG D.nd D.naut i' ∧ Formalism.MainNotions.N.AtM D.nd D.naut i' σ) → ZSpec D i := by
  intro D M i HT A SU TO TC II PZ EX
  have hZ0 : Idx.Z0 D (D.nd.mu i) (D.nd.j i) = LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
    unfold Idx.Z0
    rw [orth_ker_eq_range_adjoint]
    exact inf_eq_left.2 TC
  have hmu : ∀ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), D.nd.mu i' = D.nd.mu i := fun i' hi' => by
    rw [D.nd.mu_w, D.nd.mu_w, ((D.nd.locs_mem _ _ i').1 hi').2]
  let G : Set (D.naut.AV i) := {P | ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), ∃ x' ∈ Formalism.MainNotions.N.ZgoodN D.nd D.naut i',
    ∃ P' : D.naut.AV i', D.naut.ptV i' P' = some x' ∧ ∃ (hμ : D.nd.mu i' = D.nd.mu i) (hj : D.nd.j i' = D.nd.j i),
      (D.naut.typeV i' P').map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P}

  have hin : ∀ P ∈ G, D.naut.typeV i P ≤ LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
    rintro P ⟨i', hi', x', hx', P', hP', hμ, hj, he⟩
    have hZ := (PZ i' ⟨x', hx'⟩).2.1
    have h1 : D.naut.typeV i' P' ≤ LinearMap.range (D.what₂.thetaT (D.nd.mu i') (D.nd.j i')) := by
      refine le_trans ?_ (LinearMap.map_le_range (f := D.what₂.thetaT (D.nd.mu i') (D.nd.j i'))
        (p := Formalism.MainNotions.N.goodPartM D.nd D.naut i'))
      rw [hZ]
      refine le_trans ?_ (le_biSup (fun x => Formalism.MainNotions.N.eigC D.nd D.naut i' x) hx')
      unfold Formalism.MainNotions.N.eigC
      exact le_biSup (fun Q => D.naut.typeV i' Q) (show P' ∈ {Q | D.naut.ptV i' Q = some x'} from hP')
    rw [← he, ← map_eqvMt_range_thetaT hμ hj]
    exact Submodule.map_mono h1

  have hsub : LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) ≤ ⨆ P ∈ G, D.naut.typeV i P := by
    rw [LinearMap.range_eq_map, ← ((II (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2).submodule_iSup_eq_top),
      Submodule.map_iSup]
    refine iSup_le fun σ => ?_
    by_cases h0 : D.what₂.isot (D.nd.j i) σ = ⊥
    · rw [h0, Submodule.map_bot]; exact bot_le
    obtain ⟨hg, i', hi', hHG, hAt⟩ := EX σ h0
    have hj : D.nd.j i' = D.nd.j i := ((D.nd.locs_mem _ _ i').1 hi').1
    have hμ := hmu i' hi'
    have h1 : D.what₂.isot (D.nd.j i') σ ≤ Formalism.MainNotions.N.goodPartM D.nd D.naut i' :=
      le_biSup (fun τ => D.what₂.isot (D.nd.j i') τ) (show σ ∈ {τ | D.nd.goodRow τ ∧ Formalism.MainNotions.N.AtM D.nd D.naut i' τ} from ⟨hg, hAt⟩)
    have h2 := Submodule.map_mono (f := D.what₂.thetaT (D.nd.mu i') (D.nd.j i')) h1
    rw [(PZ i' hHG).2.1] at h2
    rw [← map_eqvMt_thetaT_isot hμ hj]
    refine le_trans (Submodule.map_mono h2) ?_
    rw [Submodule.map_le_iff_le_comap]
    refine iSup₂_le fun x' hx' => ?_
    unfold Formalism.MainNotions.N.eigC
    refine iSup₂_le fun P' hP' => ?_
    rw [← Submodule.map_le_iff_le_comap]
    have hne : (NG.isoTyp (M.loc i').wt.ρ (A.S i' P')).comap (M.loc i').real ≠ ⊥ := by
      rw [← A.typeV i' P']; exact D.naut.typeV_ne i' P'
    obtain ⟨P, hP⟩ := typeV_of_transport A i hμ hj (D.nd.j_range i').1 (D.nd.j_range i').2 (A.S i' P') (A.irr i' P') hne
    have hT : (D.naut.typeV i' P').map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P := by
      rw [A.typeV i' P']; exact hP
    rw [hT]
    exact le_biSup (fun Q => D.naut.typeV i Q) (show P ∈ G from ⟨i', hi', x', hx', P', hP', hμ, hj, hT⟩)
  have hZG : LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) = ⨆ P ∈ G, D.naut.typeV i P :=
    le_antisymm hsub (iSup₂_le hin)
  have hout : ∀ P, P ∉ G → D.naut.typeV i P ≤ (LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)))ᗮ := by
    intro P hP
    rw [← Submodule.isOrtho_iff_le]
    apply Submodule.IsOrtho.symm
    rw [Submodule.isOrtho_iff_le, hZG]
    refine iSup₂_le fun Q hQ => ?_
    rw [← Submodule.isOrtho_iff_le]
    exact TO Q P (fun h => hP (h ▸ hQ))
  unfold ZSpec
  rw [hZ0]
  intro P
  refine ⟨(em (P ∈ G)).elim (fun h => Or.inl (hin P h)) (fun h => Or.inr (hout P h)), fun x hx => ⟨fun hg => ?_, fun hb => hout P ?_⟩⟩
  · exact hin P ⟨i, (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩, x, (D.Zgood_tie i x).1 hg, P, hx, rfl, rfl, map_eqvMt_self _ _ _⟩
  · rintro ⟨i', hi', x', hx', P', hP', hμ, hj, he⟩
    obtain ⟨hj', hw'⟩ := (D.nd.locs_mem _ _ i').1 hi'
    by_cases hii : i' = i
    · subst hii
      rw [map_eqvMt_self] at he
      have hPP : P' = P := by
        by_contra hne
        have hd : Disjoint (D.naut.typeV i' P') (D.naut.typeV i' P) := (D.naut.typeV_indep i').pairwiseDisjoint hne
        rw [he] at hd
        exact D.naut.typeV_ne i' P (disjoint_self.1 hd)
      subst hPP
      rw [hx] at hP'
      cases hP'
      exact hb ((D.Zgood_tie _ _).2 hx')
    · obtain ⟨φ, hφ⟩ := HT.sameO i i' hj'.symm hw'.symm
      obtain ⟨v, k, hv, hv', k1, k2, hunit⟩ := HT.sep i i' φ hφ hj'.symm hw'.symm (Ne.symm hii) x x'
      obtain ⟨s, ϖ, hc, hu⟩ := SU v hv.1
      have e := eig_of_transport A i P x hx hμ hj (D.nd.j_range i').1 (D.nd.j_range i').2 (D.naut.typeV i' P') he
        v k s ϖ hv hc hu k1 k2 _ (fun y hy => A.eigen i' P' x' hP' v k s ϖ hv' hc hu k1 k2 y hy)
      rw [hφ] at e
      have hinj : Function.Injective (iotaOC D i') := by
        intro a b h
        simp only [iotaOC, RingHom.coe_comp, Function.comp_apply] at h
        exact IsFractionRing.injective (D.nd.O i') (FractionRing (D.nd.O i'))
          ((D.naut.iotaQ i').injective ((D.naut.iotaQC i').injective h))
      rw [hinj e, sub_self] at hunit
      exact not_isUnit_zero hunit

end GlobalTheory.EtaJoin.TypeSum
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwSys.InertiaElt

open Filter Topology

theorem exists_coprime_dvd_mul_pow (m : ℕ) (o : ℕ) (ho : o ≠ 0) : ∃ t K : ℕ, Nat.Coprime t m ∧ o ∣ t * m ^ K := by
  induction o using Nat.recOnMul with
  | zero => exact absurd rfl ho
  | one => exact ⟨1, 0, Nat.coprime_one_left m, one_dvd _⟩
  | prime p hp =>
    by_cases h : p ∣ m
    · exact ⟨1, 1, Nat.coprime_one_left m, by simpa using h⟩
    · exact ⟨p, 0, (Nat.Prime.coprime_iff_not_dvd hp).2 h, by simp⟩
  | mul a b iha ihb =>
    obtain ⟨t, K, ht, hK⟩ := iha (left_ne_zero_of_mul ho)
    obtain ⟨t', K', ht', hK'⟩ := ihb (right_ne_zero_of_mul ho)
    refine ⟨t * t', K + K', Nat.Coprime.mul_left ht ht', ?_⟩
    have : t * t' * m ^ (K + K') = (t * m ^ K) * (t' * m ^ K') := by ring
    rw [this]
    exact mul_dvd_mul hK hK'

theorem exists_limit_pow {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (σ : Γ) (m : ℕ) : ∃ z : Γ, (∀ I : Subgroup Γ, IsClosed (I : Set Γ) → σ ∈ I → z ∈ I) ∧
      (∀ U : Subgroup Γ, IsOpen (U : Set Γ) → ∃ k : ℕ, z⁻¹ * σ ^ (m ^ k) ∈ U) ∧
      ∀ U : Subgroup Γ, IsOpen (U : Set Γ) → U.Normal → ∃ n : ℕ, Nat.Coprime n m ∧ z ^ n ∈ U := by
  obtain ⟨z, hz⟩ : ∃ z : Γ, MapClusterPt z atTop (fun k : ℕ => σ ^ (m ^ k)) :=
    exists_clusterPt_of_compactSpace (map (fun k : ℕ => σ ^ (m ^ k)) atTop)
  have key : ∀ U : Subgroup Γ, IsOpen (U : Set Γ) → ∃ᶠ k : ℕ in atTop, z⁻¹ * σ ^ (m ^ k) ∈ U := by
    intro U hU
    have ho : IsOpen ((fun x : Γ => z⁻¹ * x) ⁻¹' (U : Set Γ)) := hU.preimage (by fun_prop)
    exact hz.frequently (p := fun x => z⁻¹ * x ∈ U) (ho.mem_nhds (by simp))
  refine ⟨z, fun I hI hσ => ?_, fun U hU => (key U hU).exists, fun U hU hN => ?_⟩
  · exact hI.mem_of_mapClusterPt hz (Eventually.of_forall fun k => I.pow_mem hσ _)
  · have : Finite (Γ ⧸ U) := U.quotient_finite_of_isOpen hU
    obtain ⟨t, K, ht, hK⟩ := exists_coprime_dvd_mul_pow m (orderOf (QuotientGroup.mk' U σ)) (orderOf_pos _).ne'
    obtain ⟨k, hk, hmem⟩ := frequently_atTop.1 (key U hU) K
    refine ⟨t, ht, ?_⟩
    have e : QuotientGroup.mk' U z = QuotientGroup.mk' U σ ^ (m ^ k) := by
      rw [← map_pow]
      exact QuotientGroup.eq.2 hmem
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' U (z ^ t) = 1
    rw [map_pow, e, ← pow_mul, ← orderOf_dvd_iff_pow_eq_one]
    refine hK.trans ?_
    rw [mul_comm]
    exact Nat.mul_dvd_mul_right (pow_dvd_pow m hk) t

theorem isUnit_sub_one {O : Type*} [CommRing O] [IsDomain O] {n : ℕ} {ζ : O} (hn : IsUnit (n : O))
    (h : IsPrimitiveRoot ζ n) (h1 : 1 < n) : IsUnit (ζ - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 + 1 := ⟨n - 2, by omega⟩
  have e := h.prod_one_sub_pow_eq_order
  rw [Finset.prod_range_succ'] at e
  have hu : IsUnit (1 - ζ ^ (0 + 1)) := by
    refine isUnit_of_mul_isUnit_right (x := ∏ j ∈ Finset.range k, (1 - ζ ^ (j + 1 + 1))) ?_
    rw [e]
    exact_mod_cast hn
  rw [← neg_sub]
  simpa using hu.neg

theorem exists_place_mem (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 E) := by
    intro h
    have h2 : IsUnit (Algebra.norm ℤ ((p : ℕ) : 𝓞 E)) := h.map _
    have e : Algebra.norm ℤ ((p : ℕ) : 𝓞 E) = (p : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      rw [← Algebra.norm_algebraMap]
      simp
    rw [e, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h2
    exact hp.one_lt.ne' h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 E)}) (by
    rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((p : ℕ) : 𝓞 E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hmem))

end GlobalTheory.TwSys.InertiaElt


open GlobalTheory.TwSys.InertiaElt in
theorem GlobalTheory.TwSys.exists_tameInertiaElementAtAuxiliaryPrime : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
    (i : X.Tw), ∃ z, IsTameInertiaElementAtTwistPrime X i z := by
  intro D N X i
  have hl : (X.l i).Prime := (X.lPrime i).out
  obtain ⟨v, hv⟩ : ∃ v, v ∈ X.pD i := by
    have hp : (if X.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
      split_ifs
      · exact D.host.pde'_prime
      · exact D.host.pde_prime
    obtain ⟨v, hv⟩ := exists_place_mem D.host.E hp
    refine ⟨v, ?_⟩
    rw [← Finset.mem_coe, X.pD_eq i]
    exact hv
  obtain ⟨A, hA⟩ := exists_isPlaceOver N.Om v

  obtain ⟨p, hp, hp15, hp2, hpl⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ 15 ∧ p ≠ 2 ∧ p ≠ X.l i := by
    by_cases h : X.l i = 3
    · exact ⟨5, by norm_num, by norm_num, by norm_num, by omega⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, fun h' => h h'.symm⟩
  have : Fact p.Prime := ⟨hp⟩
  have hcard := X.delta_15 i v hv A hA
  have : Finite ((Ine (F := D.host.E) A).map (X.delta i)) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨⟨y, hy⟩, hyo⟩ := exists_prime_orderOf_dvd_card' (G := (Ine (F := D.host.E) A).map (X.delta i)) p
    (by rw [hcard]; exact hp15)
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hy
  have hord : orderOf (X.delta i σ) = p := by
    rw [← hyo, ← Subgroup.orderOf_coe]
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_limit_pow σ (X.l i * Ideal.absNorm v.asIdeal)
  refine ⟨z, v, hv, A, hA, hz1 _ (isClosed_Ine A) hσ, ?_, hz3⟩
  obtain ⟨k, hk⟩ := hz2 _ (X.delta_open i)
  have hz : X.delta i z = X.delta i σ ^ ((X.l i * Ideal.absNorm v.asIdeal) ^ k) := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, inv_mul_eq_one] at hk
    exact hk
  have hpl' : Nat.Coprime p (X.l i) := (Nat.coprime_primes hp hl).2 hpl
  have hpq : Nat.Coprime p (Ideal.absNorm v.asIdeal) := by
    refine Nat.Coprime.coprime_dvd_left hp15 ?_
    have := X.delta_tame i v hv
    rw [Nat.Coprime, Nat.gcd_rec, this]
    norm_num
  have hprim : IsPrimitiveRoot (X.delta i σ) p := hord ▸ IsPrimitiveRoot.orderOf _
  have hcop : Nat.Coprime ((X.l i * Ideal.absNorm v.asIdeal) ^ k * 2) p :=
    Nat.Coprime.symm (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (Nat.Coprime.mul_right hpl' hpq))
      ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have hprim2 : IsPrimitiveRoot (((X.delta i z : (X.O0 i)ˣ) : X.O0 i) ^ 2) p := by
    have := hprim.pow_of_coprime _ hcop
    rw [pow_mul, ← hz] at this
    rw [← Units.val_pow_eq_pow_val]
    exact IsPrimitiveRoot.coe_units_iff.2 this
  refine isUnit_sub_one ?_ hprim2 hp.one_lt
  have hlnu : ¬ IsUnit ((X.l i : ℕ) : X.O0 i) := by
    intro h
    have h2 := h.map (algebraMap (X.O0 i) (X.O i))
    rw [map_natCast] at h2
    exact X.O_l i h2
  have hc : IsCoprime ((p : ℕ) : X.O0 i) ((X.l i : ℕ) : X.O0 i) := hpl'.cast
  obtain ⟨a, b, hab⟩ := hc
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hab ▸ isUnit_one) with h | h
  · exact isUnit_of_mul_isUnit_right h
  · exact absurd (isUnit_of_mul_isUnit_right h) hlnu
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwSys.TameScalar

theorem not_mem_placesOver {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E p) : v ∉ placesOver E q := by
  intro hv'
  have hc : IsCoprime ((p : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 h)
  obtain ⟨a, b, hab⟩ := hc
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hv')

theorem isUnit_inv_sq_sub_one {O : Type} [CommRing O] (u : Oˣ) (h : IsUnit ((u : O) ^ 2 - 1)) :
    IsUnit (((u⁻¹ : Oˣ) : O) ^ 2 - 1) := by
  have e : ((u⁻¹ : Oˣ) : O) ^ 2 - 1 = -(((u⁻¹ : Oˣ) : O) ^ 2 * ((u : O) ^ 2 - 1)) := by
    rw [mul_sub, ← mul_pow, Units.inv_mul]; ring
  rw [e]
  exact (((u⁻¹).isUnit.pow 2).mul h).neg

theorem isUnit_sub_one {O : Type} [CommRing O] (x : O) (h : IsUnit (x ^ 2 - 1)) : IsUnit (x - 1) := by
  have e : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
  rw [e] at h
  exact isUnit_of_mul_isUnit_left h

theorem exists_scalar_tmat_of_tame_inertia : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (z : GE N), IsotypicValuationAtRing bkP i s → IsTameInertiaElementAtTwistPrime X i z → ∃ d : (X.O0 i)ˣ, Tmat i s z = (d : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) ∧ IsUnit ((d : X.O0 i) ^ 2 - 1) ∧ IsUnit ((d : X.O0 i) - 1) ∧ eps0 X i z = 1 := by
  intro D N X bkP i s z h hz
  obtain ⟨v, hv, A, hA, hzA, hu, -⟩ := hz
  have hlp : (X.l i).Prime := (X.lPrime i).out
  have hv' : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← X.pD_eq i]; exact hv
  have hp : (if X.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  have hl : v ∉ placesOver D.host.E (X.l i) := by
    refine not_mem_placesOver hp hlp ?_ hv'
    split_ifs with hh
    · rw [hh]; exact D.host.pde_ne.symm
    · exact fun e => hh e.symm
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k => by
    refine not_mem_placesOver hp (D.host.g_prime k) ?_ hv'
    split_ifs
    exacts [(D.host.pde_ne_g k).2, (D.host.pde_ne_g k).1]
  have h1 : X.rhoS i s z = 1 := h.1 v hl hg A hA z hzA
  have h2 : chiS i s z = if X.side i s then X.delta i z else (X.delta i z)⁻¹ :=
    X.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA z hzA
  have h3 : IsUnit ((((chiS i s z)⁻¹ : (X.O0 i)ˣ) : X.O0 i) ^ 2 - 1) := by
    rw [h2]
    split_ifs
    · exact isUnit_inv_sq_sub_one _ hu
    · rw [inv_inv]; exact hu
  refine ⟨(chiS i s z)⁻¹, ?_, h3, isUnit_sub_one _ h3, ?_⟩
  · rw [Tmat, h1, Units.val_one]
  · have h4 : cycZ D.host.E N.Om (X.l i) z = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.1 fun n => ?_)
      rw [cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hzA.2 x hx) n]
      simp
    simp [eps0, h4]

end GlobalTheory.TwSys.TameScalar
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.breuilKisin_exactTriple_jumps_characters_lift : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ μ : Type) [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (η H : ℕ) (D₀ : BKDat O K l e a ι η H) (D₁ : BKDat O K l e a κ η H) (D₂ : BKDat O K l e a μ η H) (F : BKHom D₀ D₁) (G : BKHom D₁ D₂), IsExactTriple F.toHom G.toHom → D₀.jumps ⊆ D₁.jumps ∧ (∀ τ, D₀.desc.chars τ ⊆ D₁.desc.chars τ) ∧ Function.Injective F.onPol ∧ (∀ n : ℕ, (∀ y ∈ D₂.M, ∃ x ∈ D₁.M, G.app x = (l : K) ^ n • y) → ∀ w ∈ D₁.Z, G.onPol w = 0 → ∃ w₀ ∈ D₀.Z, F.onPol w₀ = (l : K) ^ n • w) := by
  first | exact @GlobalTheory.exactTriple_jumps_chars_lift | exact GlobalTheory.exactTriple_jumps_chars_lift | (intros; apply GlobalTheory.exactTriple_jumps_chars_lift <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.zeta_series_higher_terms_mem_lPow_breuilKisin : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (y₀ : Vec K a ι), 1 ≤ η → η < H → 14 * H < l → E K l e ^ η • y₀ ∈ D.M → ∃ r ∈ D.MM, D.zeta ((X : K⟦X⟧) ^ e • y₀) + D.lphi (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (l : K) ^ (l - 14 * H) • r := by
  first | exact @GlobalTheory.zeta_add_lphi_conn_mem | exact GlobalTheory.zeta_add_lphi_conn_mem | (intros; apply GlobalTheory.zeta_add_lphi_conn_mem <;> assumption)
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct


theorem _root_.GlobalTheory.T.equivariantIso_transport_cocycles_extensions : ∀ {O G : Type} [CommRing O] [Group G] [TopologicalSpace G] {M M' : Type} [AddCommGroup M]
    [Module O M] [AddCommGroup M'] [Module O M'] (W : Representation O G M) (W' : Representation O G M')
    (e : M ≃ₗ[O] M'), (∀ g x, e (W g x) = W' g (e x)) →
    ∀ (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] (z : G → M ⊗[O] X) (z' : G → M' ⊗[O] X),
      (∀ g, z' g = LinearEquiv.rTensor X e (z g)) →
      (z ∈ Z1 (twCoef W χ X) ⊤ ↔ z' ∈ Z1 (twCoef W' χ X) ⊤) ∧
      (∀ (hz : z ∈ Z1 (twCoef W χ X) ⊤) (hz' : z' ∈ Z1 (twCoef W' χ X) ⊤) {c : O} (hc : ∀ x : X, c • x = 0),
        ∃ f : ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) ≃ₗ[O] ((M' ⊗[O] X) × (O ⧸ Ideal.span {c})),
          ∀ g x, f (Ea W χ hc ⟨z, hz⟩ g x) = Ea W' χ hc ⟨z', hz'⟩ g (f x)) ∧
      (z ∈ B1 (twCoef W χ X) ⊤ ↔ z' ∈ B1 (twCoef W' χ X) ⊤) ∧
      ∀ I : Subgroup G, (∃ b, ∀ g ∈ I, z g = twCoef W χ X g b - b) ↔
        (∃ b', ∀ g ∈ I, z' g = twCoef W' χ X g b' - b') := by
  first | exact @GlobalTheory.TransportCoef.transport | exact GlobalTheory.TransportCoef.transport | (intros; apply GlobalTheory.TransportCoef.transport <;> assumption)
end
