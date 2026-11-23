module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle195
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenus
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle091
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairOmSumSameDatumLe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle103
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle300
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle287
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle249
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle081
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormOrbitSumLeOfSymmKernel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle148
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle301
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle212
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle131
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle172
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle149
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle244
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

namespace GlobalTheory.IntSmulMemSubmodule

theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (w : Fin n → E) : ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • w ∈ L := by
  apply GlobalTheory.LatAlmostAll.exists_int_smul_mem <;> assumption

end GlobalTheory.IntSmulMemSubmodule
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.definiteUnitaryGroup_count_eq_mainTerm : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount.DefiniteHyp B d p → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → (B.D : ℝ) = mainTerm B d := by
  first | exact @GlobalTheory.Dec.definite_count_of_finite | exact GlobalTheory.Dec.definite_count_of_finite | (intros; apply GlobalTheory.Dec.definite_count_of_finite <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass

theorem exists_orthoLattice_of_unimodular : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) :=
  fun K _ _ _ hK => GlobalTheory.OrthoLattice.hasOrtho K hK

end GlobalTheory.Mass
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.cyclicDiscriminant_lattices_form_one_genus : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ T : ℕ, T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → (∃ s : Finset (Ideal (𝓞 K)), s.card = fDeg K ∧ (∀ P ∈ s, P.IsMaximal ∧ Ideal.absNorm P = T) ∧ IsCoprime (∏ P ∈ s, P) (conjIdeal (K := K) (∏ P ∈ s, P)) ∧ (∏ P ∈ s, P) * conjIdeal (K := K) (∏ P ∈ s, P) = Ideal.span {(T : 𝓞 K)}) ∧ ∀ L N : Submodule (𝓞 K) V, IsIntLat h L → Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → (N ∈ genus h L ↔ IsIntLat h N ∧ Nonempty ((↥(dual h N) ⧸ N.comap (dual h N).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}))) := by
  first | exact @GlobalTheory.Mass.CyclicGenus.main | exact GlobalTheory.Mass.CyclicGenus.main | (intros; apply GlobalTheory.Mass.CyclicGenus.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem tlat_one_genus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → TLat cm.sig J T f M → ∃ h : UPts cm.sig J (Ad F), ∀ x, (h⁻¹).1.1 *ᵥ x ∈ hat F L ↔ x ∈ hat F M := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L M hT hS hf hL hM
  classical
  have hLat : IsLat L := hL.1
  have hMat : IsLat M := hM.1

  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g ∈ UPts cm.sig J (v.adicCompletion F),
      ∀ x, x ∈ loc v L ↔ g.1 *ᵥ x ∈ loc v M := by
    intro v
    by_cases hv : (T : 𝓞 F) ∈ v.asIdeal
    · exact GlobalTheory.T.exists_localUnitary_lattices_of_level F E cm n J hJ hdet T f L M hT hS hf hL hM v hv
    · exact GlobalTheory.T.exists_localUnitary_of_selfDual_at_place F E cm n J hJ hdet L M hLat hMat v
        (GlobalTheory.T.isLocallySelfDual_of_hermitianLatticeOfLevel F E cm n J hJ hdet T f L hL v hv)
        (GlobalTheory.T.isLocallySelfDual_of_hermitianLatticeOfLevel F E cm n J hJ hdet T f M hM v hv)
  choose g hgU hg using hloc

  let k : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F) :=
    fun v => if loc v L = loc v M then 1 else g v
  have hkU : ∀ v, k v ∈ UPts cm.sig J (v.adicCompletion F) := by
    intro v
    by_cases hv : loc v L = loc v M
    · simp only [k, if_pos hv]; exact one_mem _
    · simp only [k, if_neg hv]; exact hgU v
  have hfin : {v | k v ≠ 1}.Finite := by
    refine (GlobalTheory.T.localSpanOfLatticeAtPlace_eq_for_almost_all_places F E n L M hLat hMat).subset ?_
    intro v hv heq
    exact hv (by simp only [k, if_pos heq])
  obtain ⟨y, hyU, hy⟩ := GlobalTheory.T.exists_adelic_unitary_of_finite_support F E n cm.sig J k hkU hfin
  have hglob : ∀ x, x ∈ hat F L ↔ y.1 *ᵥ x ∈ hat F M := by
    rw [GlobalTheory.T.adelicLattice_carry_iff_forall_place F E n L M hLat hMat y]
    intro v x
    rw [hy v]
    by_cases hv : loc v L = loc v M
    · simp only [k, if_pos hv, Units.val_one, Matrix.one_mulVec, hv]
    · simp only [k, if_neg hv]; exact hg v x
  refine ⟨⟨y, hyU⟩, fun x => ?_⟩
  rw [hglob, Matrix.mulVec_mulVec]
  have hinv : ((⟨y, hyU⟩ : UPts cm.sig J (Ad F))⁻¹).1 = y⁻¹ := rfl
  rw [hinv, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.St.G
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePair_omSum_same_datum_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ i b : ℕ, N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) ≤ ENNReal.ofReal (((i : ℝ) * b) ^ Module.finrank K N.Wt * (i : ℝ) ^ cf K * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  first | exact @GlobalTheory.DegCnt.OmCount.main | exact GlobalTheory.DegCnt.OmCount.main | (intros; apply GlobalTheory.DegCnt.OmCount.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.AmpCancel

theorem ofReal_tsum_ite {ι : Type} (p : ι → Prop) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hfin : {i | p i}.Finite) :
    ENNReal.ofReal (∑' i, if p i then f i else 0) =
      ∑' i, if p i then ENNReal.ofReal (f i) else 0 := by
  have hs : ∀ i, i ∉ hfin.toFinset → ¬ p i := fun i hi h => hi (hfin.mem_toFinset.2 h)
  have hs' : ∀ i ∈ hfin.toFinset, p i := fun i hi => hfin.mem_toFinset.1 hi
  rw [tsum_eq_sum (s := hfin.toFinset) (fun i hi => if_neg (hs i hi)),
    tsum_eq_sum (s := hfin.toFinset) (fun i hi => if_neg (hs i hi)),
    Finset.sum_congr rfl (fun i hi => if_pos (hs' i hi)),
    Finset.sum_congr rfl (fun i hi => if_pos (hs' i hi)),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hf i)]

theorem amp_le_mass {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hk : 4 * r + 7 ≤ k)
    (β J βJ : ℕ) (d : S.Datum) :
    ENNReal.ofReal (‖S.amp d (S.InFF β J βJ d)‖) ≤
      ENNReal.ofReal (7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) * S.mass d (S.InFF β J βJ d) := by
  have hk1 : 1 ≤ k := by omega
  have hc0 : 0 ≤ (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := zpow_nonneg (Nat.cast_nonneg _) _
  have hvol : ∀ K : Subgroup S.GLV, 0 ≤ invVol S.K0 K := fun K =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨P, hP⟩ : ∃ P : Submodule L.O S.V → Prop, P = fun Λ => S.IsTerm d Λ ∧ S.InFF β J βJ d Λ :=
    ⟨_, rfl⟩
  have hPiff : ∀ Λ, P Λ ↔ S.IsTerm d Λ ∧ S.InFF β J βJ d Λ := fun Λ => by rw [hP]
  have hPfin : {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | P o.out}.Finite :=
    (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk1 d).2.subset fun o ho => ((hPiff _).1 ho).1
  have hmass : S.mass d (S.InFF β J βJ d) = ENNReal.ofReal (∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0) := by
    rw [ofReal_tsum_ite (ι := MulAction.orbitRel.Quotient S.St (Submodule L.O S.V)) (fun o => P o.out)
      (fun o => invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out)) (fun o => hvol _) hPfin]
    subst hP
    unfold Frames.mass Frames.mu
    exact tsum_congr fun o => by congr
  have hsum0 : 0 ≤ ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0 :=
    tsum_nonneg fun o => by split_ifs <;> simp [hvol]
  have hamp : S.amp d (S.InFF β J βJ d) = ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then ((invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) : ℝ) : ℂ) * S.om d o.out
      else 0 := by
    subst hP
    unfold Frames.amp Frames.mu
    exact tsum_congr fun o => by congr
  have key : ‖S.amp d (S.InFF β J βJ d)‖ ≤ 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) *
      ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
        if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0 := by
    by_cases hJ : 1 ≤ J ∧ J ≤ r
    · have hj : ((⟨J - 1, by omega⟩ : Fin r) : ℕ) + 1 = J := by simp only; omega
      obtain ⟨m, hm_inv, hm⟩ := GlobalTheory.T.exists_symm_invariant_kernel_hermitian_frames L r k S hk ⟨J - 1, by omega⟩ β βJ d P
        (fun Λ => by rw [hj]; exact hPiff Λ)
      have hK0 : S.K0 ≤ S.St := fun g hg => hg.1.1
      have bound := GlobalTheory.HL.norm_orbit_sum_le_of_symm_kernel S.St S.K0 P (S.om d) m
        (24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) hK0
        (fun h hh x hx => by
          obtain ⟨hT, hI⟩ := (hPiff x).1 hx
          have T := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d x hT h hh
          have hlat := (GlobalTheory.HL.TermBasic.term_basic L r k S d x hT).1.1
          exact ⟨(hPiff _).2 ⟨T.1, (T.2.2.2.2.2.2.2.2.2.1 β J βJ).2 hI⟩, T.2.1,
            ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 x hlat).2.2 h hh, fun y hy => hm_inv h hh x y hx hy⟩)
        (fun x hx => by
          have hb := GlobalTheory.HL.TermBasic.term_basic L r k S d x ((hPiff x).1 hx).1
          have A := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 x hb.1.1
          have W := (GlobalTheory.HL.WitIndep.witness_independence L r k S d x _ _ hb.2.1).2.2.2.2
          obtain ⟨h1, h2, h3, h4⟩ := hm x hx
          exact ⟨A.1, A.2.1, W, h1, h2, h3, h4⟩)
        hPfin
      rw [hamp]
      have h2 : 2 * (24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) ≤
          7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by linarith
      exact bound.trans (mul_le_mul_of_nonneg_right h2 hsum0)
    · have hempty : ∀ Λ, ¬ P Λ := by
        intro Λ hΛ
        obtain ⟨hT, hTB, -, hle, ⟨y, hy, hyJ⟩, -⟩ := (hPiff Λ).1 hΛ
        by_cases hJr : r < J
        · have := hTB.2.1 y hy
          omega
        · have hJ0 : J = 0 := by omega
          apply hTB.1
          refine le_antisymm (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1 fun z hz => ?_
          refine ((GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.2.2.2.2.1 z hz).1 ?_
          have := hle z hz
          omega
      rw [hamp]
      simp [hempty]
  rw [hmass, ← ENNReal.ofReal_mul (by linarith)]
  exact ENNReal.ofReal_le_ofReal key

end GlobalTheory.HL.AmpCancel
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspAllKType

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  simp only [AutInst.Kg, AutInst.Kset, Set.mem_setOf_eq]
  refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
  · simp
  · simp [AutInst.fmat]

theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  intro k hk
  obtain ⟨h1, hm, hn, -, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨-, -, -, -, -, hbi, -⟩ := B.e_adm

  set π : B.I.Gf → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund) := fun a => B.R (1, a) with hπ
  have hπ1 : π 1 = 1 := h1
  have hπm : ∀ a b, π (a * b) = π a * π b := fun a b => by
    simp only [hπ]
    rw [← hm]
    congr 1
    ext <;> simp
  have hπn : ∀ a v, ‖π a v‖ = ‖v‖ := fun a v => hn _ v

  have hek : ∀ x, B.e (k * x) = B.e x := fun x => by
    simpa using hbi x k hk 1 (one_mem_Kg B.I B.g)
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply]
  change ⟪x, π k (B.Re y)⟫_ℂ = _
  rw [GlobalTheory.IdemProj.inner_rep π hπ1 hπm hπn k x (B.Re y), B.Re_spec.2 (π k⁻¹ x) y, B.Re_spec.2 x y]
  have hinner : ∀ a, ⟪π k⁻¹ x, B.R (1, a) y⟫_ℂ = ⟪x, B.R (1, k * a) y⟫_ℂ := fun a => by
    have := (GlobalTheory.IdemProj.inner_rep π hπ1 hπm hπn k x (π a y)).symm
    change ⟪π k⁻¹ x, π a y⟫_ℂ = ⟪x, π (k * a) y⟫_ℂ
    rw [this, hπm, ContinuousLinearMap.mul_apply]
  simp_rw [hinner]
  calc ∫ a, B.e a * ⟪x, B.R (1, k * a) y⟫_ℂ ∂B.μf
      = ∫ a, (fun b => B.e b * ⟪x, B.R (1, b) y⟫_ℂ) (k * a) ∂B.μf := by
        congr 1
        ext a
        simp only [hek]
    _ = ∫ a, B.e a * ⟪x, B.R (1, a) y⟫_ℂ ∂B.μf := by
        exact integral_mul_left_eq_self (μ := B.μf) (fun b => B.e b * ⟪x, B.R (1, b) y⟫_ℂ) k

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hl : LocDec B h) (hb : HBig B 40 h) : Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have hmaj := hint 0 le_rfl (fun v => by
    by_cases hq : rkR (B.I.ε v) = 0
    · exact Or.inl hq
    right

    have hqn : rkR (B.I.ε v) ≤ B.I.n := by
      unfold rkR
      exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
    have hq1 : (1 : ℝ) ≤ (rkR (B.I.ε v) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq
    have hqn' : (rkR (B.I.ε v) : ℝ) ≤ (B.I.n : ℝ) := by exact_mod_cast hqn
    have hs : 0 < Real.sqrt (rkR (B.I.ε v) : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hn : 0 < (B.I.n : ℝ) := by linarith
    have hns : 0 < (B.I.n : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) := mul_pos hn hs
    have h1 : (B.I.n : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) * (rkR (B.I.ε v) : ℝ)
        ≤ (B.I.n : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) * (B.I.n : ℝ) :=
      mul_le_mul_of_nonneg_left hqn' hns.le
    have h2 := hb v
    nlinarith)
  simp only [zero_mul, Real.exp_zero, mul_one] at hmaj
  exact hmaj.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hle)

theorem cusp_all : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, A ∈ B.I.HomS B.σs B.μf B.fund B.R ∧ ∀ u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A u)) ∧ ∀ k ∈ B.I.Kg B.g, B.R (1, k) (A u) = A u := by
  intro B d h hd hK hg hh hl hb A hA

  obtain ⟨T0, hT0, hA'⟩ := Submodule.mem_map.1 hA
  have hAe : A = B.Re.comp T0 := by rw [← hA']; rfl
  subst hAe
  have hT0' : ∀ g : B.I.Ginf, T0.comp (B.σs g) = (B.R (g, 1)).comp T0 := hT0
  have hint := integrable_ph B d h hd hl hb
  obtain ⟨-, hcomm, ⟨T, hT⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd hint
  have hHom : ∀ g : B.I.Ginf, (B.Re.comp T0).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp T0) := fun g => by
    rw [ContinuousLinearMap.comp_assoc, hT0' g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  refine ⟨hHom, fun u => ?_⟩

  obtain ⟨S, hSmem, hScl, hSinv, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  obtain ⟨-, hirr, -, hnorm, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  have hw := GlobalTheory.T.countedVectors_are_cuspForms_singleLowestKType B d h hd hK hg hh hl hb T hT (B.Re.comp T0) hA
  let S' : Submodule ℂ B.Hs := S.comap ((B.Re.comp T0 : B.Hs →L[ℂ] B.I.L2 B.μf B.fund) : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund)
  have hS'cl : IsClosed (S' : Set B.Hs) := hScl.preimage (B.Re.comp T0).continuous
  have hS'inv : ∀ g, ∀ v ∈ S', B.σs g v ∈ S' := fun g v hv => by
    have hv' : (B.Re.comp T0) v ∈ S := hv
    show (B.Re.comp T0) (B.σs g v) ∈ S
    have := congrArg (fun F : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => F v) (hHom g)
    simp only [ContinuousLinearMap.comp_apply] at this
    simp only [ContinuousLinearMap.comp_apply]
    rw [this]
    exact hSinv _ _ hv'
  have hwS : B.tens B.w ∈ S' := (hSmem _).2 hw
  rcases hirr S' hS'cl hS'inv with h0 | htop
  · exfalso
    rw [h0, Submodule.mem_bot] at hwS
    rw [hwS, norm_zero] at hnorm
    exact zero_ne_one hnorm
  · have hu : u ∈ S' := htop ▸ Submodule.mem_top
    refine ⟨(hSmem _).1 hu, fun k hk => ?_⟩
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply (B.R (1, k)) B.Re, re_fixed B k hk]

end GlobalTheory.Dec.CuspAllKType
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.reproducing_formula_discreteSeries_test_growth : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ), IsContRep B (T y) f → (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) ∧ (∃ Φ : B.I.GA → ℝ, Integrable Φ (B.I.muA B.μf) ∧ ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g) ∧ ∀ x, f x = ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
  first | exact @GlobalTheory.Reproducing.reproducing_formula | exact GlobalTheory.Reproducing.reproducing_formula | (intros; apply GlobalTheory.Reproducing.reproducing_formula <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.isKTypeOf_lowK_of_countHyp : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) := by
  first | exact @GlobalTheory.Dec.countHyp_isKTypeOf_lowKSub | exact GlobalTheory.Dec.countHyp_isKTypeOf_lowKSub | (intros; apply GlobalTheory.Dec.countHyp_isKTypeOf_lowKSub <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : WCoord P S), (∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → S.IsTerm (c.dat d) (c.lat t.abelian₂) ∧ LocNG.om P t = S.om (c.dat d) (c.lat t.abelian₂) ∧ (LocNG.BBne (H := H) t ↔ ¬ S.BBzero (c.dat d) (c.lat t.abelian₂))) ∧ (∀ d d' : LocNG.Datum P, LocNG.Datum.Rel d d' ↔ ∃ h ∈ S.H0, h • c.dat d = c.dat d') ∧ P.Hp = S.Hp ∧ (P.PrimeTo → S.Hp = 1) ∧ ∀ (R : LocNG.Reps P) (d : LocNG.Datum P), LocNG.amp R d (LocNG.BBne (H := H)) = S.amp (c.dat d) (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧ LocNG.amp R d (fun t => ¬ LocNG.BBne (H := H) t) = S.amp (c.dat d) (S.BBzero (c.dat d)) := by
  first | exact @GlobalTheory.HL.WCoordTerms.terms_orbits_heights_amps | exact GlobalTheory.HL.WCoordTerms.terms_orbits_heights_amps | (intros; apply GlobalTheory.HL.WCoordTerms.terms_orbits_heights_amps <;> assumption)
end

section

namespace GlobalTheory.Deep

theorem ptBound_and_farBound_and_decGap :
    GlobalTheory.Deep.PtBound ∧ GlobalTheory.Deep.FarBound ∧ GlobalTheory.DSId.DecGap :=
  have hd : GlobalTheory.DSId.DecGap :=
    GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap
  have hp : GlobalTheory.Deep.PtBound := GlobalTheory.Deep.ptBound_of_decGap hd
  ⟨hp, GlobalTheory.FarTerms.farBound_of_ptBound hp, hd⟩

end GlobalTheory.Deep
end
