module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuSign
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLatticeComplement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter UpperTheory.V.Af.Bc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

private theorem unlocked_of_potentially {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r : G F Ω →* GL (Fin n) (Qbar l)} {v : HeightOneSpectrum (𝓞 F)} (h : PotUnl r v) : Unl1 r v := fun A hA =>
  (h A hA).imp fun _ k => ⟨k.1, fun i j e => k.2 i j 1 le_rfl (by simpa only [pow_one] using e)⟩

private theorem keeps_of_pot (hFL : FlagLaws) {K M Ω : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] [Algebra K Ω] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (r : G ℚ Ω →* GL (Fin n) (Qbar l))
    (hp : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → PotUnl r v) :
    Keeps (r.comp (resG ℚ K Ω)) M := by
  intro w hw _
  have hv : ((l : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by
    simpa [HeightOneSpectrum.under, Ideal.mem_comap] using hw
  have h := (((hFL ℚ Ω l n r).2.2.2 M).2.2 w hw).1 (hp _ hv)
  exact unlocked_of_potentially h

private theorem step (hFL : FlagLaws) (hUD : AUpDown) (hP : HypothesesH) (hR : RowT) (K K' Ω : Type) [Field K] [NumberField K] [IsCMField K]
    [Field K'] [NumberField K'] [IsCMField K'] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [Algebra K' Ω]
    (hK : Module.finrank ℚ K = 2) (hK' : Module.finrank ℚ K' = 2) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n)
    (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (hp : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → PotUnl r v)
    (hc : Continuous r) (hA : IsAutomorphicOverImagQuad ι r)
    (θ : G ℚ Ω →* (Qbar l)ˣ) (hθ : IsAlgChar ι θ) (hd : DualTw r θ) (hI : IneAb r) (hF : Flagged r)
    (hi : IsIrr (r.comp ((resG ℚ K Ω).range ⊓ (resG ℚ K' Ω).range).subtype))
    (hW : WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) :
    WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K' Ω →* G ℚ Ω)) := by
  obtain ⟨M, _, _, _, iK, iK', iM, tK, tK', gK, gK', hs, hs', hM, hM'⟩ := UpperTheory.V.Z.Bc.biQuad K K' Ω hK hK'
  have closure_over (L : Type) [Field L] [CharZero L] [Algebra L Ω] : IsAlgClosure L Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  have := closure_over K
  have := closure_over K'
  have := closure_over M
  have exists_conj : ∃ c : G ℚ Ω, IsConjEl c := by
    let j : Ω →ₐ[ℚ] ℂ := _root_.IsAlgClosed.lift
    let : Algebra Ω ℂ := j.toRingHom.toAlgebra
    have : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
    let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
    exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, τ.restrictNormal_commutes Ω⟩
  obtain ⟨c, hcc⟩ := exists_conj
  have he : (r.comp (resG ℚ K Ω)).comp (resG K M Ω) = (r.comp (resG ℚ K' Ω)).comp (resG K' M Ω) :=
    MonoidHom.ext fun s => rfl
  have irr_of_range {Δ Δ' : Type} [Group Δ] [Group Δ']
      (f : Δ →* G ℚ Ω) (f' : Δ' →* G ℚ Ω) (h : ∀ s, ∃ t, f' t = f s)
      (H : IsIrr (r.comp f)) : IsIrr (r.comp f') := by
    refine ⟨H.1, fun _ _ _ => trivial, fun W hW hI => H.2.2 W hW fun s v hv => ?_⟩
    obtain ⟨t, ht⟩ := h s
    simpa only [MonoidHom.comp_apply, ht] using hI t v hv
  have hiM : IsIrr ((r.comp (resG ℚ K Ω)).comp (resG K M Ω)) := by
    refine irr_of_range _ ((resG ℚ K Ω).comp (resG K M Ω)) ?_ hi
    rintro ⟨s, ⟨t, rfl⟩, h2⟩
    obtain ⟨u, rfl⟩ := (hM t).2 h2
    exact ⟨u, rfl⟩
  have hiM' : IsIrr ((r.comp (resG ℚ K' Ω)).comp (resG K' M Ω)) := he ▸ hiM
  have hiK : IsIrr (r.comp (resG ℚ K Ω)) :=
    irr_of_range ((resG ℚ K Ω).comp (resG K M Ω)) (resG ℚ K Ω) (fun s => ⟨resG K M Ω s, rfl⟩) hiM
  have hiK' : IsIrr (r.comp (resG ℚ K' Ω)) :=
    irr_of_range ((resG ℚ K' Ω).comp (resG K' M Ω)) (resG ℚ K' Ω) (fun s => ⟨resG K' M Ω s, rfl⟩) hiM'
  have exists_pairing (F : Type) [Field F] [CharZero F] [Algebra F Ω] :
      ∃ P, IsPairing c (r.comp (resG ℚ F Ω)) (θ.comp (resG ℚ F Ω)) P := by
    obtain ⟨J, hJ⟩ := hd
    refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
    have h' : resG ℚ F Ω s' = c * resG ℚ F Ω s * c⁻¹ := h
    have e : r c⁻¹ * r (resG ℚ F Ω s') = r (resG ℚ F Ω s) * r c⁻¹ := by
      rw [h', ← map_mul, ← map_mul]
      congr 1
      group
    have e' : (r c⁻¹).val * (r (resG ℚ F Ω s')).val = (r (resG ℚ F Ω s)).val * (r c⁻¹).val :=
      congrArg Units.val e
    have hp := hJ (resG ℚ F Ω s)
    simp only [MonoidHom.comp_apply]
    rw [Units.val_mul, ← Matrix.smul_mul, ← hp]
    simp only [Matrix.mul_assoc, e']
  obtain ⟨P, hPa⟩ := exists_pairing K
  obtain ⟨P', hPa'⟩ := exists_pairing K'
  have pol : Sol.Pol ι (r.comp (resG ℚ K Ω)) :=
    ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      θ, c, P, hθ, UpperTheory.V.Ws.auSign θ, hcc, hPa⟩
  have pol' : Sol.Pol ι (r.comp (resG ℚ K' Ω)) :=
    ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      θ, c, P', hθ, UpperTheory.V.Ws.auSign θ, hcc, hPa'⟩
  have up := (hUD hP hR K M Ω hs l ι n hn (r.comp (resG ℚ K Ω)) (hc.comp (continuous_restrictScalarsHom ℚ K Ω)) hiM pol
    (hA hc K hK hiK) (((hFL ℚ Ω l n r).2.2.2 K).2.1 hF)).1 hW
  rw [he] at up
  exact (hUD hP hR K' M Ω hs' l ι n hn (r.comp (resG ℚ K' Ω)) (hc.comp (continuous_restrictScalarsHom ℚ K' Ω)) hiM' pol'
    (hA hc K' hK' hiK') (((hFL ℚ Ω l n r).2.2.2 K').2.1 hF)).2 (((hFL ℚ Ω l n r).2.2.2 K').1 hI)
    (keeps_of_pot hFL r hp) up

end UpperTheory.V.Z.Win
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HeckeGal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

private theorem semisimple_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r')
    (H : IsSSRep r) : IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (Units.mul_inv g) (fun s => ?_) H
  rw [hg s, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

private theorem attC_conj {F Ω : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} {π : CuspSub F n} (h : RepIso r r')
    (H : AttC ι r π) : AttC ι r' π :=
  ⟨semisimple_conj h H.1, H.2.mono fun _ ⟨B, hB, hE⟩ => ⟨B, hB, hE.of_iso h⟩⟩

private theorem tw_tw_inv {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (μ : Γ →* kˣ) :
    tw (tw r μ) μ⁻¹ = r := by
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [tw_val, tw_val, smul_smul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    inv_mul_cancel₀ (Units.ne_zero _), one_smul]

private theorem algPos_inv {K : Type} [Field K] [NumberField K] {χ : HChar K} {a : (K →+* ℂ) → ℤ} (h : IsAlgPos χ a) :
    IsAlgPos χ⁻¹ (-a) := fun k hk => by
  have e : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
  rw [e, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm

private theorem regAlg_tw {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {a : (K →+* ℂ) → ℤ} (hκ : IsAlgPos κ a) : (CG.mk (P.twist κ)).IsRegAlg := by
  have halg : κ.IsAlg a := fun k => hκ k fun φ => absurd
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_ofReal (φ x))))
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (Complex.ofRealHom.comp φ))))
  refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_
  replace h := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).1 h
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 a halg τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + a τ, by push_cast; ring⟩

theorem aIsoTwOf : AIsoTwOf := by
  intro FL WT _ F Ω _ _ _ _ _ _ l _ ι n r hW
  refine ⟨fun r' hi => ⟨fun v hv h => ?_, fun π hreg ha => ?_⟩, fun μ hμ => ?_⟩
  · exact (((FL F Ω l n r).1 r' hi).2.2 v).2 (hW.1 v hv ((((FL F Ω l n r').1 r hi.symm').2.2 v).1 h))
  · obtain ⟨t, ht⟩ := hW.2 π hreg (attC_conj hi.symm' ha)
    exact ⟨t, fun v hv => ht v (hv.imp id (((FL F Ω l n r').1 r hi.symm').2.2 v).2)⟩
  · obtain ⟨χ, -, art, a, hart, hpos, hL⟩ := hμ
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have e : tw r μ = r := MonoidHom.ext fun s => Units.ext (by ext i; exact i.elim0)
      rw [e]
      exact hW
    have hv : ∀ v, (Unl1 (tw r μ) v → Unl1 r v) ∧ (PotUnl r v → PotUnl (tw r μ) v) ∧ (PotUnl (tw r μ) v → PotUnl r v) := fun v =>
      have h := ((FL F Ω l n r).2.1 μ).2.2 v
      ⟨h.1.2, h.2.1, h.2.2⟩
    refine ⟨fun v hl h => (hv v).2.1 (hW.1 v hl ((hv v).1 h)), fun π' hreg ha => ?_⟩
    have hatt : AttC ι r (π'.twist χ⁻¹) := by
      have h := UpperTheory.V.Af.Cq.attTwist F Ω l ι n (tw r μ) π' ha art χ⁻¹ (-a) μ⁻¹ hart hL.inv
      rwa [tw_tw_inv] at h
    obtain ⟨t, ht⟩ := hW.2 _ (regAlg_tw hreg (algPos_inv hpos)) hatt
    obtain ⟨b, hb⟩ := WT F χ
    refine ⟨t + b, fun v h => ?_⟩
    have h1 := hb n hn _ t v (ht v (h.imp id (hv v).2.2))
    rwa [← CuspSub.twist_mul, inv_mul_cancel, CuspSub.twist_one] at h1

end UpperTheory.V.Z.Win
end
end
