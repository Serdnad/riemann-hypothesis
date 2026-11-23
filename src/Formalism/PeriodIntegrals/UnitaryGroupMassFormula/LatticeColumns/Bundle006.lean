module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdapt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxAsm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfFrameBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.QtoPInvMulVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle013
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

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

def DClause (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
    (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (Q : GL (Idx D.R.rS D.R.k) (FpX X p)) : Prop :=
  ∀ (ψ : KvA X p.1 →* GL (Idx D.R.rS D.R.k) (Op X p)),
    (∀ x : KvA X p.1, ((MassDataIdxRed.glRed (algebraMap (Op X p) (FpX X p)) (ψ x) : GL (Idx D.R.rS D.R.k) (FpX X p)) :
        Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) =
      ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *
        Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) *
        (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p))) →
    ∀ (π : Op X p →+* ZMod (gOf p)), RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)} →
    ∀ (x : KvH X u p.1) (B : GL (Fin D.R.k) (Op X p)), ψ (inclH X u p x) = hEmbGL D.R.rS D.R.k B →
      (x ∈ (unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1) ↔
        MassDataIdxRed.glRed π B ∈ Formalism.DoubleCosetMeasures.upUniG (ZMod (gOf p)) D.R.k)

def DClauseAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p), IsSplitEquiv X p θ →
    ∀ (Q : GL (Idx D.R.rS D.R.k) (FpX X p)) (l : Idx D.R.rS D.R.k → FpX X p), (∀ s, ¬ IsW s → l s ≠ 0) →
      (∀ s, ¬ IsW s → ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (pr1 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm) =
          (Pi.single s (1 : FpX X p) : Idx D.R.rS D.R.k → FpX X p)) →
      (∀ s, ¬ IsW s → (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p))ᵀ *ᵥ
        ((Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ
          (pr2 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm)) =
        l s • (Pi.single (dlH s) (1 : FpX X p) : Idx D.R.rS D.R.k → FpX X p)) →
      LatBasis X p θ (reindex₂ X p Q) → WClause X hb u p θ Q → DClause X hb u p θ Q

theorem hModelU_of (hD : DClauseAll) (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word)
    (hT : X.MeasTie hb) (hL : X.LevelSubgroupNormalized) (p : TypX X) (hA : HAdaptQ X hb u p) : HModelU X hb u p := by
  obtain ⟨θ, hθ, Q, l, hl, hy1, hy2, hLB, hW⟩ := hA
  obtain ⟨ψ, hψ, hker, hform⟩ := latCoreX_holds X p θ hθ Q hLB (KvA X p.1) rfl
  have hres : MassDataIdxSteps.ResArith X p := by
    have hgp : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
    have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
      have hty := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
        (D.host.g_prime 1).ne_zero p.1).1 p.2
      unfold gOf
      split_ifs with h
      · exact h
      · exact hty.resolve_left h
    have hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) |
        ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
      unfold gOf
      split_ifs
      · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)
      · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)
    obtain ⟨he, hf⟩ := MassDataIdxRes.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gOf p) hsplit p.1 hmem
    obtain ⟨hc, hn⟩ := MassDataIdxRes.arith_of_loc (gOf p) p.1 hmem he hf
    exact ⟨hc, hmem, hn⟩
  obtain ⟨π, hπ, hπk⟩ := MassDataIdxSteps.stResZ_of X p hres
  refine ⟨ψ, 1, π, 1, hψ, hker, fun x => ?_, hπ, hπk, fun x B hB => ?_⟩
  · rw [inv_one, one_mul, mul_one]
    exact hH_of_form X u p θ hθ Q l hl hy1 hy2 ψ hform x
  · rw [inv_one, one_mul, mul_one] at hB
    rw [inv_one, one_mul, mul_one]
    exact hD X hb hK u hT hL p θ hθ Q l hl hy1 hy2 hLB hW ψ hform π hπk x B hB

def HAdaptAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ p : TypX X, HAdaptQ X hb u p

theorem hModelAll_of (hA : HAdaptAll) (hD : DClauseAll) : HModelAll :=
  fun X hb hK u hT hL p => hModelU_of hD X hb hK u hT hL p (hA X hb hK u hT hL p)

end PIW.MassDataColumns
end
end

section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

theorem hEmb_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {r k : ℕ} (M : Matrix (Fin k) (Fin k) A) :
    (hEmb r M).map f = hEmb r (M.map f) := by
  unfold hEmb midEmb
  simp only [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f), Matrix.map_one _ (map_zero f) (map_one f)]

section Vec

variable (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (Idx D.R.rS D.R.k) (FpX X p))

def mkVec (w : Idx D.R.rS D.R.k → FpX X p) : Fin X.B.I.n → TpX X p :=
  fun m => θ.symm (((Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ w) ((idxEquiv X) m), 0)

theorem firstProj_mkVec_eq_mulVec (w : Idx D.R.rS D.R.k → FpX X p) :
    pr1 θ (mkVec X p θ Q w) ∘ (idxEquiv X).symm = (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ w := by
  funext i
  simp [pr1, mkVec]

theorem secondProj_mkVec_zero (w : Idx D.R.rS D.R.k → FpX X p) : pr2 θ (mkVec X p θ Q w) = 0 := by
  funext m
  simp [pr2, mkVec]

theorem crd_mkVec (w : Idx D.R.rS D.R.k → FpX X p) : crd X p θ Q (mkVec X p θ Q w) = w := by
  unfold crd
  rw [firstProj_mkVec_eq_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem eq_of_crd (v w : Fin X.B.I.n → TpX X p) (h1 : crd X p θ Q v = crd X p θ Q w) (h2 : pr2 θ v = pr2 θ w) :
    v = w := by
  have h3 : pr1 θ v ∘ (idxEquiv X).symm = pr1 θ w ∘ (idxEquiv X).symm := by
    have := congrArg (fun x => (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ x) h1
    simpa [crd, Matrix.mulVec_mulVec] using this
  funext m
  apply θ.injective
  have hm := congrFun h3 (idxEquiv X m)
  have hm2 := congrFun h2 m
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at hm
  simp only [pr1, pr2] at hm hm2
  exact Prod.ext hm hm2

theorem oep_int (hL : LatBasis X p θ (reindex₂ X p Q)) (t : TpX X p) (ht : t ∈ OEp X p) :
    (θ t).1 ∈ p.1.adicCompletionIntegers X.B.I.F := by
  have hk : Nonempty (Idx D.R.rS D.R.k) := by
    have hn := imA_n_pos X
    rw [← card_idx X] at hn
    exact Fintype.card_pos_iff.1 hn
  obtain ⟨s0⟩ := hk
  set μ := mkVec X p θ Q (Pi.single s0 1) with hμ
  have hμL : μ ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    refine lat_of_crd X p θ Q hL μ (secondProj_mkVec_zero X p θ Q _) fun s => ?_
    rw [crd_mkVec]
    by_cases hs : s = s0
    · subst hs; simp
    · simp [Pi.single_apply, hs]
  have h2 := crd_int_of_lat X p θ Q hL _ (imA_lat_OEp X p ht hμL) s0
  rw [crd_smul, crd_mkVec] at h2
  simpa using h2

end Vec

end PIW.MassDataColumns
end
end
