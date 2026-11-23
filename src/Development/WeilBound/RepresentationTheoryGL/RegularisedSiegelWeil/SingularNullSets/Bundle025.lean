module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle453
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle444
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle705
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle023
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle602
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle617
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle024
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ}

theorem theta_levi {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hχ : IsHeckeChar D χ) (hω : IsWeilSch ψ χ θ V μ ω)
    (g : G D n) (a : GL (Fin n) D.host.E) (hg : mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))))
    (Φ : schwartzA θ V.rank n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  let a' : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) a
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a) := by
    apply Units.ext
    simp [a', Matrix.GeneralLinearGroup.map]
    exact (RingHom.map_det _ _).symm
  have h1 : absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact absE_inclR _
  have h2 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact hχ.2 _
  have hinv : (a'⁻¹).1 = (a⁻¹).1.map (incA D) := by
    show ((Matrix.GeneralLinearGroup.map (incA D) a)⁻¹).1 = _
    rw [← map_inv]; rfl
  have hg' : mat g = blk4 a'.1 0 0 (adj (a'⁻¹).1) := by
    rw [hinv]; exact hg
  have hm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      (ω g Φ).1 (ξ.map (incA D)) = Φ.1 ((ξ * a.1).map (incA D)) := by
    intro ξ
    rw [hω.levi g a' hg' Φ, h1, h2]
    have e : (HMul.hMul (ξ.map (incA D)) a'.1 : Mx D V.rank n) = (ξ * a.1).map (incA D) := by
      rw [Matrix.map_mul]; rfl
    rw [e]
    simp [npow]
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun ξ => ξ * a.1
      invFun := fun ξ => ξ * (a⁻¹).1
      left_inv := fun ξ => by
        show ξ * a.1 * (a⁻¹).1 = ξ
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      right_inv := fun ξ => by
        show ξ * (a⁻¹).1 * a.1 = ξ
        rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one] }
  simp_rw [hm]
  exact e.tsum_eq (fun ξ => Φ.1 (ξ.map (incA D)))

theorem theta_unip {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hω : IsWeilSch ψ χ θ V μ ω)
    (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E) (hg : mat g = blk4 1 (b.map (incA D)) 0 1)
    (Φ : schwartzA θ V.rank n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  refine tsum_congr fun ξ => ?_
  rw [hω.unip g (b.map (incA D)) hg Φ (ξ.map (incA D)), GlobalTheory.CompanionTheory.ThetaInv.psi_unip_rat hψ, one_mul]

open GlobalTheory.CompanionTheory.ThetaPoisson in
theorem theta_weyl {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hθ : IsInfFam θ) {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    (hω : IsWeilSch ψ χ θ V μ ω) (g : G D n) (hg : mat g = blk4 0 1 (-1) 0) (Φ : schwartzA θ V.rank n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hT := isHermND_gram V
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D V.rank n V.gram hT ψ hψ
  have hs := pairing_symm (n := n) hT ψ
  have hval : ∀ x, (ω g Φ).1 x = ∫ y, Φ.1 y * GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing V.gram ψ y x ∂μ := fun x => by
    rw [hω.weyl g hg Φ x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hs y x]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing, GlobalTheory.SiegelWeilLitCompare.gramQ_eq]
    rfl
  haveI := hμ.1
  have key := poisson_translates (ratMx D V.rank n) K hK hKc (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing (n := n) V.gram ψ)
    (fun y => ?_) hs (fun x x' y => ?_) (fun x y => hψ.2.1 _) h1 h2 μ 𝓕 hμ.2.1 hμ.2.2 (f := Φ.1) ?_
    (translates_bound hθ Φ) ?_
  · simp only [← hval] at key
    rw [tsum_ratMx, tsum_ratMx (fun x => (ω g Φ).1 x)] at key
    exact key.symm
  · simp only [hs _ y]
    haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have ht : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA (D := D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
    exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)
  · simp only [hs _ y]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.gramQ GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.mmul
    rw [Matrix.mul_add, Matrix.trace_add, map_add (f := _), AddChar.map_add_eq_mul]
  · exact (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ n Φ.1
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ n Φ.1 Φ.2)).1
  · simp only [← hval]
    exact (ratEquiv D V.rank n).summable_iff.1 (GlobalTheory.SiegelWeilLitCompare.summable_rat hθ (ω g Φ))

theorem thetaInv' {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hχ : IsHeckeChar D χ) (hθ : IsInfFam θ) {𝓕 : Set (Mx D V.rank n)}
    (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank n) {γ : G D n}
    (hγ : γ ∈ GF D n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  let S : Subgroup (G D n) :=
    { carrier := {γ | ∀ Φ : schwartzA θ V.rank n,
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
          ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D))}
      one_mem' := fun Φ => by simp
      mul_mem' := fun {g h} hg hh Φ => by
        rw [map_mul, Module.End.mul_apply]
        exact (hg _).trans (hh Φ)
      inv_mem' := fun {g} hg Φ => by
        have := hg (ω g⁻¹ Φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        exact this.symm }
  have hle : GF D n ≤ S := GlobalTheory.T.rational_group_le_of_generators_mem D n S (fun g a hg Φ => theta_levi hχ hω g a hg Φ)
    (fun g b hg Φ => theta_unip hψ hω g b hg Φ)
    (fun g hg Φ => theta_weyl hψ hθ hμ hω g hg Φ)
  exact hle hγ Φ

theorem theta_rat {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hχ : IsHeckeChar D χ) (hθ : IsInfFam θ) {𝓕 : Set (Mx D V.rank n)}
    (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank n) {γ : G D n}
    (hγ : γ ∈ GF D n) (g : G D n) (h : GA D V) : theta ω Φ (γ * g) h = theta ω Φ g h := by
  have hc := (GlobalTheory.WeilSchComm.subst_mem_and_comm D n V ψ χ θ hθ μ 𝓕 hμ ω hω h⁻¹).2 γ (ω g Φ)
    (GlobalTheory.WeilSchComm.subst θ V n h⁻¹ (ω g Φ)) (fun _ => rfl)
  have ht := thetaInv' hψ hχ hθ hμ hω (GlobalTheory.WeilSchComm.subst θ V n h⁻¹ (ω g Φ)) hγ
  simp only [hc] at ht
  unfold theta
  rw [map_mul, Module.End.mul_apply]
  exact ht

end PositivityTheory.Rg.Rsw.L.LThBdd

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutLow

open GlobalTheory.CompanionTheory.PcFc (chn)

variable {D : D7} {n : ℕ}

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (t : AF D.host.F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 t)]

theorem cutR_left {nb : hermA D n → G D n} {v : Pl D} (C : Cut D n v) {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) :
    LeftInv (GF D n) (cutR nb C F) := fun γ hγ g => by
  unfold cutR
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc, hinv γ hγ]

theorem cutR_cont {nb : hermA D n → G D n} {v : Pl D} (C : Cut D n v) {F : G D n → ℂ} (hF : Continuous F) :
    Continuous (cutR nb C F) := by
  unfold cutR
  exact continuous_finsetSum _ fun x _ => continuous_const.mul (hF.comp (continuous_id.mul continuous_const))

theorem cutR_lev {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {F : G D n → ℂ}
    (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) {k : G D n} (hk : k ∈ lev nb C.s)
    (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) (g : G D n) : cutR nb C F (g * k) = cutR nb C F g := by
  unfold cutR
  refine Finset.sum_congr rfl fun x hx => ?_
  have e : g * k * nb x = g * nb x * ((nb x)⁻¹ * k * nb x) := by group
  rw [e, hK _ (conj_mem_KAt hnb C hk hkv hx)]

theorem fc_cutR_low {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) {v : Pl D} (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g)
    (C : Cut D n v) {r : ℕ} (hkill : C.Kills ψ r) (β : HermE D n) (hβ : β.1.rank < r) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : fc ψ lam 𝓖 nb (cutR nb C F) β g = 0 := by
  rw [fc_cutR hψ hC hF hinv C β hg]
  by_cases h : ∀ x : hermA D n, IntAt v x → pch ψ x.1 (rat β.1) = 1
  · rw [hkill β hβ h, zero_mul]
  · push Not at h
    obtain ⟨x, hx, hne⟩ := h
    have e := fc_fix hψ hC hinv hK β hx hg
    have h0 : (1 - pch ψ x.1 (rat β.1)) * fc ψ lam 𝓖 nb F β g = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    rw [(mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 (Ne.symm hne)), mul_zero]

theorem vanish_at {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (hFP : FourierPt) {nb : hermA D n → G D n}
    (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {r : ℕ} (hkill : C.Kills ψ r) {F : G D n → ℂ} (hF : Continuous F)
    (hinv : LeftInv (GF D n) F) (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) (hR : RankLT ψ F r) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : cutR nb C F g = 0 := by
  obtain ⟨lam, 𝓖, hcov⟩ := GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D n
  have hC : CoefData (D := D) (n := n) nb lam 𝓖 := ⟨hnb, hcov⟩
  have hco : ∀ β : HermE D n, ∫ x in 𝓖, cutR nb C F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam = 0 := by
    intro β
    have e : ∫ x in 𝓖, cutR nb C F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam = fc ψ lam 𝓖 nb (cutR nb C F) β g := by
      rw [fc_eq]
      refine integral_congr_ae (.of_forall fun b => ?_)
      show _ * conj (pch ψ b.1 (rat β.1)) = _ * chn ψ β b
      rw [pch_rat, conj_psi hψ, chn_eq]
    rw [e]
    by_cases hβ : β.1.rank < r
    · exact fc_cutR_low hψ hC hF hinv hK C hkill β hβ hg
    · rw [fc_cutR hψ hC hF hinv C β hg, hR nb lam 𝓖 hC β (not_lt.1 hβ) g, mul_zero]
  have key := hFP D n ψ hψ lam 𝓖 hcov (fun b => cutR nb C F (nb b * g)) (cont_nb (cutR_cont C hF) hnb g)
    (fun γ hγ b => per_nb (cutR_left C hinv) hnb g γ hγ b) hco
  have h0 := congrFun key 0
  simp only [GlobalTheory.CompanionTheory.FourierN.nb_zero hnb, one_mul, Pi.zero_apply] at h0
  exact h0

end PositivityTheory.Rg.Rsw.L.LCutLow

namespace PositivityTheory.Rg.Rsw.L

open LCutLow in
theorem cutLow : FourierPt → WeakApproximationFinitePlace → CutLow := by
  intro hFP hWA D n r ψ hψ nb hnb v C hkill F hF hinv hK
  have hlev : ∀ k ∈ lev nb C.s, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ g, cutR nb C F (g * k) = cutR nb C F g :=
    fun k hk hkv g => cutR_lev hnb C hK hk hkv g
  refine ⟨fun hR => ?_, ⟨lev nb C.s, isOpen_lev nb C.s, hlev⟩, fun lam 𝓖 hC β g hg =>
    ⟨fc_cutR hψ hC hF hinv C β hg, fun hβ => fc_cutR_low hψ hC hF hinv hK C hkill β hβ hg⟩⟩
  funext g
  obtain ⟨γ, hγ, g', hg', k, hk, hkv, rfl⟩ := hWA D n v (lev nb C.s) (isOpen_lev nb C.s) g
  show cutR nb C F (γ * g' * k) = 0
  rw [hlev k hk hkv, cutR_left C hinv γ hγ g']
  exact vanish_at hψ hFP hnb C hkill hF hinv hK hR hg'

end PositivityTheory.Rg.Rsw.L

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L


theorem cutId : Polar → CfFJ → CoefId → ThCoef → FourierPt → WeakApproximationFinitePlace → CfInv → ThBdd → CutLow → IkSch → IkEq → WMaj → CutId := by
  intro hPolar hCfFJ hCoefId hThCoef hFP hWA1 hCfInv hThBdd hCutLow _ hIkEq hWMaj
  intro D n t B W d hn ψ χ θ μB μW ωB ωW hS I H hH Φ U dd E σ hcont ε hrad nb hnb v C hK hKv 𝓕 h𝓕 Ψ Ψ' hΨ hΨ'
  obtain ⟨nb₀, lam, 𝓖, hCD⟩ := GlobalTheory.T.coefficient_data_exists D n
  have hC : CoefData (D := D) (n := n) nb lam 𝓖 := ⟨hnb, hCD.2⟩
  obtain ⟨κ, hκ⟩ := hCoefId D n t B W d hn ψ χ θ μB μW ωB ωW hS I H hH Φ U dd E σ hcont ε hrad nb lam 𝓖 hC
  refine ⟨κ, ?_⟩

  have hBr : B.rank = W.rank + 2 * t := d.rank_add.symm
  have hlaw : IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ).1 0) :=
    LCutId.law0 hS.hB Φ _ (by rw [hBr, ← hn]; push_cast; ring)
  have hηB : ResEta D χ B.rank := by rw [hBr]; exact LCutId.resEta_add hS.hη t
  have hφc : Continuous (fun g => (ωB g Φ).1 0) :=
    (hWMaj D n B ψ hS.hψ χ hS.hχ hηB θ hS.hθ μB hS.hμB ωB hS.hB Φ).1.comp (continuous_id.prodMk continuous_const)
  have hpol := hPolar D n W.rank t hn hS.big ψ hS.hψ χ hS.hχ hS.hη
    (fun h0 => absurd h0 (by have := hS.pos; omega)) θ hS.hθ H hH _ hφc hlaw U dd E σ hcont ε hrad
  have hRk := hpol.1 1 le_rfl

  obtain ⟨hcf, -, -⟩ := hCfFJ D n H _ _ U dd E σ hcont ε hrad
  have hcf1c := (hcf 1).1
  have hcf1i := (hcf 1).2
  have hcfK : ∀ k ∈ KAt D n v, ∀ g, cf dd E ((t : ℂ) / 2) ε 1 (g * k) = cf dd E ((t : ℂ) / 2) ε 1 g := by
    intro k hk g
    exact hCfInv D n H _ _ U dd E σ hcont ε hrad k (fun g => (hKv k hk).2 g) (fun g => by
      show (ωB (g * k) Φ).1 0 = (ωB g Φ).1 0
      rw [map_mul, Module.End.mul_apply, (hKv k hk).1]) 1 g
  obtain ⟨-, ⟨U₁, hU₁, hU₁i⟩, hlow⟩ := hCutLow D n W.rank ψ hS.hψ nb hnb v C hK _ hcf1c hcf1i hcfK

  have hΨK : ∀ k ∈ KAt D n v, ωW k Ψ = Ψ := fun k hk => Subtype.ext (by
    rw [hIkEq D n t B W d hn ψ χ θ μB μW ωB ωW hS I Φ Ψ hΨ k, (hKv k hk).1, ← hΨ])
  obtain ⟨-, hthL, ⟨U₂, hU₂, hU₂i⟩, -, hthF⟩ :=
    hThBdd D n W ψ hS.hψ χ hS.hχ hS.hη θ hS.hθ μW hS.hμW ωW hS.hW nb hnb v C hK Ψ Ψ' hΨK hΨ'
  obtain ⟨F₂, hF₂⟩ : ∃ F₂ : G D n → ℂ, F₂ = fun g => ∫ h in 𝓕, theta ωW Ψ' g h ∂I.m := ⟨_, rfl⟩
  have hF₁L : ∀ γ ∈ GF D n, ∀ g, cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (γ * g) = cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) g := by
    intro γ hγ g
    unfold cutR
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, hcf1i γ hγ]
  have hF₁c : Continuous (cutR nb C (cf dd E ((t : ℂ) / 2) ε 1)) := by
    unfold cutR
    exact continuous_finsetSum _ fun x _ => continuous_const.mul (hcf1c.comp (continuous_mul_const _))
  have hF₂L : ∀ γ ∈ GF D n, ∀ g, F₂ (γ * g) = F₂ g := by
    intro γ hγ g
    rw [hF₂]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    exact hthL γ hγ g h
  have hF₂R : ∀ k ∈ U₂, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ g, F₂ (g * k) = F₂ g := by
    intro k hk hk' g
    rw [hF₂]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    show ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E, (ωW (g * k) Ψ').1 _ = ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E, (ωW g Ψ').1 _
    rw [map_mul, Module.End.mul_apply, hU₂i k hk hk']

  have key : ∀ g, proj D.sp.cm.sig (Jst D n) v g = 1 → cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) g = κ * F₂ g := by
    intro g hg
    obtain ⟨-, hTc, hTβ⟩ := hThCoef D n W ψ hS.hψ θ hS.hθ I.m 𝓕 I.haar h𝓕 lam 𝓖 hCD.2 (ωW g Ψ').1 (ωW g Ψ').2
    have hthS : ∀ x : hermA D n, F₂ (nb x * g) = thS W I.m 𝓕 (fun X => pch ψ x.1 (ip W X X) * (ωW g Ψ').1 X) := by
      intro x
      rw [hF₂]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      exact (hthF x g hg).2 h
    have hF₂c : Continuous fun x : hermA D n => F₂ (nb x * g) := by
      simp only [hthS]; exact hTc
    have hF₁c' : Continuous fun x : hermA D n => cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) :=
      hF₁c.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_nb hnb).mul continuous_const)
    have hper : ∀ {F : G D n → ℂ}, (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
        ∀ γ ∈ ratHerm D n, ∀ x, F (nb (γ + x) * g) = F (nb x * g) := by
      intro F hF γ hγ x
      rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
      exact hF _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _
    have hcoef : ∀ β : HermE D n, fc ψ lam 𝓖 nb (cutR nb C (cf dd E ((t : ℂ) / 2) ε 1)) β g =
        κ * ∫ x in 𝓖, F₂ (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam := by
      intro β
      simp only [hthS]
      have hlowβ := hlow lam 𝓖 hC β g hg
      have horb : ∀ x₀ : Matrix (Fin W.rank) (Fin n) D.host.E, gramQ W x₀ = β.1 →
          orb W I.m (ωW g Ψ').1 x₀ = cutF ψ C (rat β.1) * orb W I.m (ωW g Ψ).1 x₀ := by
        intro x₀ hx₀
        unfold orb
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun h => ?_)
        show (ωW g Ψ').1 _ = _ * (ωW g Ψ).1 _
        rw [(hthF 0 g hg).1, LCutId.ip_orbit, hx₀]
      rcases lt_trichotomy β.1.rank W.rank with hlt | heq | hgt
      · rw [hlowβ.2 hlt]
        by_cases hx : ∃ x, x.rank = W.rank ∧ gramQ W x = β.1
        · obtain ⟨x₀, hx₀r, hx₀⟩ := hx
          rw [(hTβ β).2 x₀ hx₀r hx₀]
          unfold orb
          rw [show (∫ h, (ωW g Ψ').1 (mm (Formalism.L2.Theta.mt W h⁻¹) (rat x₀)) ∂I.m) = ∫ _h, (0 : ℂ) ∂I.m from
            integral_congr_ae (Eventually.of_forall fun h => ?_), integral_zero, mul_zero]
          show (ωW g Ψ').1 _ = 0
          rw [(hthF 0 g hg).1, LCutId.ip_orbit, hx₀]
          by_cases hdual : ∀ y : hermA D n, IntAt v y → pch ψ y.1 (rat β.1) = 1
          · rw [hK β hlt hdual, zero_mul]
          · push Not at hdual
            obtain ⟨y, hy, hne⟩ := hdual
            have hfix := LCutId.omega_fix hS.hW hnb Ψ hΨK hg hy (mm (Formalism.L2.Theta.mt W h⁻¹) (rat x₀))
            rw [LCutId.ip_orbit, hx₀] at hfix
            have h2 : (1 - pch ψ y.1 (rat β.1)) * (ωW g Ψ).1 (mm (Formalism.L2.Theta.mt W h⁻¹) (rat x₀)) = 0 := by
              rw [sub_mul, one_mul, ← hfix, sub_self]
            rw [(mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hne)), mul_zero]
        · rw [(hTβ β).1 hx, mul_zero]
      · rw [hlowβ.1]
        by_cases hx : ∃ x, gramQ W x = β.1
        · obtain ⟨x₀, hx₀⟩ := hx
          have hx₀r : x₀.rank = W.rank := by
            have h1 := LCutId.rank_gram_le W x₀
            rw [hx₀, heq] at h1
            exact le_antisymm (Matrix.rank_le_height x₀) h1
          rw [((hκ β heq g).2 x₀ hx₀), (hTβ β).2 x₀ hx₀r hx₀, horb x₀ hx₀,
            hIkEq D n t B W d hn ψ χ θ μB μW ωB ωW hS I Φ Ψ hΨ g]
          ring
        · rw [(hκ β heq g).1 hx, (hTβ β).1 fun ⟨x, _, hx'⟩ => hx ⟨x, hx'⟩, mul_zero, mul_zero]
      · rw [hlowβ.1, hRk nb lam 𝓖 hC β (Nat.succ_le_of_lt hgt) g, mul_zero]
        rw [(hTβ β).1 fun ⟨x, hxr, hx'⟩ => by
          have h1 := LCutId.rank_gram_le W x
          rw [hx', hxr] at h1
          omega, mul_zero]
    have hf0 := hFP D n ψ hS.hψ lam 𝓖 hCD.2
      (fun x => cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) - κ * F₂ (nb x * g))
      (hF₁c'.sub (continuous_const.mul hF₂c))
      (fun γ hγ x => by simp only [hper hF₁L γ hγ x, hper hF₂L γ hγ x])
      (fun β => by
        have i1 := LCutId.intOn hCD.2 hF₁c' (hper hF₁L) (LCutId.cont_conj_pch hS.hψ β) (LCutId.norm_conj_pch hS.hψ · β)
        have i2 := LCutId.intOn hCD.2 hF₂c (hper hF₂L) (LCutId.cont_conj_pch hS.hψ β) (LCutId.norm_conj_pch hS.hψ · β)
        have e : (fun x : hermA D n => (cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) - κ * F₂ (nb x * g)) *
            conj (pch ψ x.1 (rat β.1))) = fun x => cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) * conj (pch ψ x.1 (rat β.1)) -
              κ * (F₂ (nb x * g) * conj (pch ψ x.1 (rat β.1))) := funext fun x => by ring
        rw [e, integral_sub i1 (i2.const_mul κ), integral_const_mul, ← LCutId.fc_eq hS.hψ, hcoef β, sub_self])
    have h0 := congrFun hf0 0
    simp only [GlobalTheory.CompanionTheory.FourierN.nb_zero hnb, one_mul, Pi.zero_apply] at h0
    exact sub_eq_zero.1 h0

  intro g
  obtain ⟨γ, hγ, g', hg', k, hkU, hkv, hgeq⟩ := hWA1 D n v (U₁ ⊓ U₂) (by rw [Subgroup.coe_inf]; exact hU₁.inter hU₂) g
  have e1 : cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (γ * g' * k) = cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) g' := by
    rw [hU₁i k (Subgroup.mem_inf.1 hkU).1 hkv, hF₁L γ hγ]
  have e2 : F₂ (γ * g' * k) = F₂ g' := by
    rw [hF₂R k (Subgroup.mem_inf.1 hkU).2 hkv, hF₂L γ hγ]
  rw [hgeq, e1, key g' hg', ← e2, hF₂]

end PositivityTheory.Rg.Rsw.L

end
end
