module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle160
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle303
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.UnitaryCharEqOneOfTrivialRationalSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ExistsSplitAt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
set_option linter.unusedSectionVars false
noncomputable section
namespace PositivityTheory.ThKW.SplitChar
open Filter Topology
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open GlobalTheory.UnRep GlobalTheory.SplitIdem
open GlobalTheory.SplitCharTrivial (cut cutH cut_val cT_add cT_smul rf tendsto_UJ tendsto_rf norm_cut cut_rf exists_seq map_sub_one map_cut)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n : ℕ} {c : E ≃ₐ[F] E} {J : Matrix (Fin n) (Fin n) E}
section Char
variable {ν : GAF (c : E →ₐ[F] E) J →* Circle}
end Char
section Refl
variable {P : Matrix (Fin n) (Fin n) E} (hP : P * P = P) (hJ : Formalism.UG.cT ((c : E →ₐ[F] E) : E →+* E) P * J = J * P)
end Refl
section Char
variable {ν : GAF (c : E →ₐ[F] E) J →* Circle}
end Char
end PositivityTheory.ThKW.SplitChar
open PositivityTheory.ThKW.SplitChar Filter Topology GlobalTheory.UnRep
open GlobalTheory.SplitCharTrivial (cut cutH cut_val cT_add cT_smul rf tendsto_UJ tendsto_rf norm_cut cut_rf exists_seq map_sub_one map_cut)
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem PositivityTheory.ThKW.unitary_character_trivial_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ ν : Formalism.IndefR.DatumF.GAF σ J →* Circle, Continuous ν → (∀ γ ∈ Formalism.IndefR.DatumF.GQF σ J, ν γ = 1) →
        (∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e → ∀ g, Formalism.IndefR.DatumF.SuppAtF σ e J g → ν g = 1) → ∀ g, ν g = 1 := by
  intro F E _ _ _ _ _ σ B hB n J hJ
  have hcm := hB.cm
  have hσ := GlobalTheory.SplitDetCharF.sig_invol hcm
  obtain ⟨c, rfl⟩ : ∃ c : E ≃ₐ[F] E, (c : E →ₐ[F] E) = σ :=
    ⟨AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ), rfl⟩
  intro ν hν hq hs
  have hH := isHermForm hcm hJ
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E (c : E →ₐ[F] E) n J
  have he1 : ∀ g, (Formalism.IndefR.DatumF.mtF _ J g).map (Formalism.IndefR.DatumF.infPartF F E) = (HA.mat _ _ J (e g).1).1 :=
    fun g => (he g).2.symm
  have he2 : ∀ g, (Formalism.IndefR.DatumF.mtF _ J g).map (Formalism.IndefR.DatumF.finPartF F E) = (HA.mat _ _ J (e g).2).1 :=
    fun g => (he g).1.symm
  have hc1 : Continuous fun x : HA (Ainf F) (c : E →ₐ[F] E) J => ν (e.symm (x, 1)) :=
    hν.comp (e.symm.continuous.comp (continuous_id.prodMk continuous_const))
  have hc2 : Continuous fun x : HA (Af F) (c : E →ₐ[F] E) J => ν (e.symm (1, x)) :=
    hν.comp (e.symm.continuous.comp (continuous_const.prodMk continuous_id))
  have hinf : ∀ x, ν (e.symm (x, 1)) = 1 := by
    have hd := GlobalTheory.RealApprox.dense_inf F E (c : E →ₐ[F] E) hσ (GlobalTheory.SplitDetCharF.sig_ne hcm) J
      (Matrix.ext fun i j => hJ.1 i j) hJ.2
    refine fun x => hd.induction (P := fun x => ν (e.symm (x, 1)) = 1) ?_ (isClosed_eq hc1 continuous_const) x
    rintro x ⟨γ, hγ, hx⟩
    obtain ⟨l, hl, e'⟩ := GlobalTheory.UnRep.isUnE_eq_prod_refl _ _ c n Jᵀ hH γ.1 ((isUnE_iff γ).2 hγ)
    have h3 := eq_one_rat hcm hH hν hq hs l hl (ratPt γ hγ) (by rw [← e']; rfl)
    have h4 : e.symm (x, 1) = pInf _ J (ratPt γ hγ) := by
      refine ga_ext ?_ ?_
      · rw [he1, e.apply_symm_apply, inf_pInf, mt_ratPt]
        refine (congrArg Units.val hx).symm.trans ?_
        ext i j
        exact (Algebra.TensorProduct.map_tmul _ _ _ _ |>.trans (by rw [map_one]; rfl)).symm
      · rw [he2, e.apply_symm_apply, fin_pInf]
        rfl
    rw [h4, h3]
  have hsplit : ∀ g, ν g = ν (e.symm (1, (e g).2)) := fun g => by
    have : g = e.symm ((e g).1, 1) * e.symm (1, (e g).2) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.eta, e.symm_apply_apply]
    conv_lhs => rw [this, map_mul, hinf, one_mul]
  let μ : HA (Af F) (c : E →ₐ[F] E) J →* Circle := ν.comp (e.symm.toMonoidHom.comp (MonoidHom.inr _ _))
  have hμ : ∀ x, μ x = ν (e.symm (1, x)) := fun _ => rfl
  intro g
  rw [hsplit, ← hμ]
  generalize (e g).2 = x
  let L : Submodule (𝓞 E) (Fin n → E) := Submodule.span (𝓞 E) (Set.range (Pi.basisFun E (Fin n)))
  have hfg : L.FG := Submodule.fg_span (Set.finite_range _)
  have hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    rw [Submodule.span_span_of_tower, (Pi.basisFun E (Fin n)).span_eq]
  choose γ h k u1 u2 u3 hg hsup hk hk' using fun N : ℕ => GlobalTheory.T.exists_unitary_adelic_decomposition_split_support F E c n Jᵀ hH hcm.2.2.1 L hfg hsp
    (HA.mat _ _ J x) N.factorial ((isUnA_iff _).2 (show HR (Af F) (c : E →ₐ[F] E) J from x).2) N.factorial_pos
  let k' : ℕ → HA (Af F) (c : E →ₐ[F] E) J := fun N => (⟨k N, (isUnA_iff _).1 (u3 N)⟩ : HR (Af F) (c : E →ₐ[F] E) J)
  have h1 : ∀ N, μ x = μ (k' N) := fun N => by
    let h' : HA (Af F) (c : E →ₐ[F] E) J := (⟨h N, (isUnA_iff _).1 (u2 N)⟩ : HR (Af F) (c : E →ₐ[F] E) J)
    let r := ratPt (γ N) ((isUnE_iff _).1 (u1 N))
    have ex : x = (e r).2 * h' * k' N := by
      refine Subtype.ext (Units.ext ((hg N).trans ?_))
      change _ = (HA.mat _ _ J (e r).2).1 * (h N).1 * (k N).1
      rw [← he2, mt_ratPt]
      congr 2
    have a1 : μ (e r).2 = 1 := by rw [hμ, ← hsplit]; exact hq _ (ratPt_mem _ _)
    have a2 : μ h' = 1 := by
      obtain ⟨ε, b1, b2, b3, b4⟩ := hsup N
      refine eq_one_of_idem hcm hs ε b1 b2 (fun v hv => (b3 v hv).1) (e.symm (1, h')) ?_
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul]
      refine parts_inj _ _ ?_ ?_
      · have h6 : (Formalism.IndefR.DatumF.mtF _ J (e.symm (1, h'))).map (Formalism.IndefR.DatumF.infPartF F E) = 1 := by
          rw [he1, e.apply_symm_apply]; rfl
        rw [RingHom.map_mul, map_sub_one, h6, sub_self, Matrix.zero_apply, mul_zero]
      · have h6 : (Formalism.IndefR.DatumF.mtF _ J (e.symm (1, h'))).map (Formalism.IndefR.DatumF.finPartF F E) = (h N).1 := by
          rw [he2, e.apply_symm_apply]; rfl
        rw [RingHom.map_mul, map_sub_one, h6]
        exact congrFun (congrFun b4 i) j
    rw [ex, map_mul, map_mul, a1, a2, one_mul, one_mul]
  have t1 := GlobalTheory.SplitRepsOpen.tendsto_one_of_cong F E L hfg hsp (fun N => (k N).1) hk
  have t2 := GlobalTheory.SplitRepsOpen.tendsto_one_of_cong F E L hfg hsp (fun N => ((k N)⁻¹).1) fun N z hz => by
    obtain ⟨y, hy, e'⟩ := hk N _ (hk' N z hz)
    refine ⟨-y, neg_mem hy, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at e'
    rw [neg_nsmul, ← e', neg_sub]
  have t3 : Tendsto k' atTop (𝓝 1) :=
    tendsto_UJ (sigR (Af F) (c : E →ₐ[F] E)) (JR (Af F) J) t1 t2
  have t := (hc2.tendsto _).comp t3
  have h0 : ν (e.symm (1, 1)) = 1 := by rw [← hμ, map_one]
  rw [h0] at t
  exact tendsto_nhds_unique (tendsto_const_nhds.congr h1) t
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.RatDarbouxTransferF
open scoped Pointwise

theorem haar_fundDomain_transfer_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
            IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
            ∃ (ν' : @Measure ((κ → AF F) × (κ → AF F)) (borel _)) (𝓕' : Set ((κ → AF F) × (κ → AF F))),
              @Measure.IsAddHaarMeasure _ _ _ (borel _) ν' ∧
              @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕' ν' ∧
              ∀ f : (κ → AF F) × (κ → AF F) → ℂ,
                ∫⁻ w in 𝓕, ‖f (co.e w)‖ₑ ^ 2 ∂ν = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂ν' := by
  intro F E _ _ _ _ _ σ B _ _ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ _ _ κ _ co hrat ν 𝓕 hν h𝓕
  obtain ⟨hfr, hfin, -⟩ := finrank_AEF F E
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI hMT : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  letI mP : MeasurableSpace ((κ → AF F) × (κ → AF F)) := borel _
  haveI : BorelSpace ((κ → AF F) × (κ → AF F)) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  let ce : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E) ≃L[AF F] (κ → AF F) × (κ → AF F) :=
    { co.e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap }
  let ca : WOF F E nS nT ≃ₜ+ (κ → AF F) × (κ → AF F) :=
    { co.e.toAddEquiv with
      continuous_toFun := ce.continuous
      continuous_invFun := ce.symm.continuous }
  let me : WOF F E nS nT ≃ᵐ (κ → AF F) × (κ → AF F) := ca.toHomeomorph.toMeasurableEquiv
  have into : ∀ g ∈ ratLF F E nS nT, co.e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, co.e.symm p ∈ ratLF F E nS nT :=
    onto F E nS nT κ co.e hrat
  refine ⟨ν.map me, me '' 𝓕, ?_, ?_, ?_⟩
  · exact ca.isAddHaarMeasure_map ν
  · refine ⟨?_, ?_, ?_⟩
    · have hqmp : Measure.QuasiMeasurePreserving me.symm (ν.map me) ν :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕 = me.symm ⁻¹' 𝓕 :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨co.e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show co.e ((g : WOF F E nS nT) + x) = co.e g + co.e x
      rw [map_add (f := _)]
    · intro p q hpq
      let g : ratLF F E nS nT := ⟨co.e.symm p, onto' p p.2⟩
      let h : ratLF F E nS nT := ⟨co.e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro e
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratLF F E nS nT => co.e (t : WOF F E nS nT)) e
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair F κ) (k : ratLF F E nS nT),
          (k : WOF F E nS nT) = co.e.symm r → r +ᵥ me '' 𝓕 = me '' (k +ᵥ 𝓕) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : (κ → AF F) × (κ → AF F)) + co.e w = co.e ((k : WOF F E nS nT) + w)
        rw [map_add (f := _), hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (ν.map me) (p +ᵥ me '' 𝓕) (q +ᵥ me '' 𝓕)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕.aedisjoint hgh
  · intro f
    rw [MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, lintegral_map_equiv]
    rfl
end GlobalTheory.RatDarbouxTransferF
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
namespace GlobalTheory.WeilPairPartnerF
theorem pair_partnerF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (a : UG (cA σ) (incM F JA)) (b : UG (cA σ) (incM F JB)),
          ∃ (g : GAF σ JS) (h : GAF σ JT), mtF σ JT h = a.1.1 ∧ mtF σ JS g = (b⁻¹).1.1ᵀ := by
  intro F E _ _ _ _ _ σ B _ _ nS nT JS JT hS _ ξ₀ hξ₀ _ JA JB ξ hA hB a b
  have hmap : ∀ {m n : Type} (X : Matrix m n (AF F ⊗[F] E)),
      X.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) = X.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) :=
    fun X => Matrix.ext fun i j => rfl
  have ha : (a.1.val)ᵀ * incM F JA * (a.1.val).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = incM F JA := a.2
  set A : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E) := a.1.val with hAdef
  have hJA : incM F JA = (incM F JT)ᵀ := by
    rw [hA]; rfl
  rw [hJA] at ha
  have ha' := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at ha'
  have hmemA : a.1 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF F) σ JT := by
    show Formalism.UG.cT _ a.1.val * _ * a.1.val = _
    simp only [Formalism.UG.cT, hmap]
    rw [Matrix.mul_assoc]
    exact ha'
  obtain ⟨cR, hcR⟩ : ∃ f, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ = f := ⟨_, rfl⟩
  have hb : (b.1.val)ᵀ * incM F JB * (b.1.val).map cR = incM F JB := by
    rw [← hcR, hmap]; exact b.2
  have hBB : b.1.val * (b⁻¹).1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).mul_inv
  have hBB' : (b⁻¹).1.val * b.1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).inv_mul
  obtain ⟨Bm, hBdef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), b.1.val = M := ⟨_, rfl⟩
  obtain ⟨Bi, hBidef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), (b⁻¹).1.val = M := ⟨_, rfl⟩
  rw [hBdef] at hb hBB hBB'
  rw [hBidef] at hBB hBB'
  have hdet : JS.det ≠ 0 := hS.2
  have hGN := GlobalTheory.WeilPairPartner.map_mul_map_inv (inclR (F := F) (E := E) (AF F)) JS hdet
  have hNG := GlobalTheory.WeilPairPartner.map_inv_mul_map (inclR (F := F) (E := E) (AF F)) JS hdet
  have hsm : incM F (ξ₀ • JS⁻¹) = inclR (F := F) (AF F) ξ₀ • incM F JS⁻¹ :=
    GlobalTheory.WeilPairPartner.map_smul_eq _ _ _
  have hu : IsUnit (inclR (F := F) (E := E) (AF F) ξ₀) :=
    (isUnit_iff_ne_zero.mpr hξ₀).map _
  have hcore := GlobalTheory.WeilPairPartner.conj_inv_transpose cR ξ _ hu Bm Bi (incM F JB) (incM F JS)
    (incM F JS⁻¹) hb hBB hBB' (hB.trans hsm) hGN hNG
  have hTT : Biᵀ * Bmᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  let gU : GL (Fin nS) (AF F ⊗[F] E) :=
    ⟨Biᵀ, Bmᵀ, hTT, by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩
  have hmemB : gU ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF F) σ JS := by
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) Biᵀ * incM F JS * Biᵀ = incM F JS
    rw [hcR]
    simp only [Formalism.UG.cT, Matrix.transpose_map, Matrix.transpose_transpose]
    exact hcore
  refine ⟨⟨gU, hmemB⟩, ⟨a.1, hmemA⟩, rfl, ?_⟩
  show Biᵀ = ((b⁻¹).1.val)ᵀ
  rw [hBidef]
end GlobalTheory.WeilPairPartnerF
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
noncomputable section
namespace GlobalTheory.HeisDerivCM
open Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem heisOF_deriv_fix_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ u : Formalism.IndefR.DatumF.WOF F E nS nT, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) f = f →
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) (fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0) = fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ _ f L _ hL u hu hf
  funext w
  have key : ∀ t : ℝ, B.ψ (symplOHF σ JS JT ξ₀ w u) * heisOF σ JS JT ξ₀ B.ψ (L t) f (w + u) =
      heisOF σ JS JT ξ₀ B.ψ (L t) f w := by
    intro t
    obtain ⟨h1, h2⟩ := symplOHF_fin_real σ JS JT ξ₀ u (L t) hu (hL t)
    have hfx := congrFun hf (w + L t)
    simp only [heisOF] at hfx ⊢
    conv_rhs => rw [← hfx]
    rw [symplOHF_add_left, symplOHF_add_left, h1, h2, add_zero, add_zero,
      show w + u + L t = w + L t + u by abel]
    ring
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + u)) 0 = _
  rw [← deriv_const_mul_field]
  exact congrArg (fun g : ℝ → ℂ => deriv g 0) (funext key)
end GlobalTheory.HeisDerivCM
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
noncomputable section
namespace GlobalTheory.HeisLineDiffF
open Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
end GlobalTheory.HeisLineDiffF
open Formalism.IndefR.DatumF in
theorem GlobalTheory.HeisLineDiffF.differentiableAt_heisOF_line_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, DifferentiableAt ℝ (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f w) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hψ f hf L hL hL0 w
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log hψ
  let φ : ℝ →+ ℂ :=
    { toFun := fun t => lam (symplOHF σ JS JT ξ₀ w (L t))
      map_zero' := by rw [map_zero L, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero]
      map_add' := fun x y => by rw [map_add L, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add (f := _)] }
  have hφ : Continuous φ := hl.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ w hL)
  let L' : (Fin 1 → ℝ) →+ WOF F E nS nT := L.comp (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0)
  have hL' : Continuous L' := hL.comp (continuous_apply 0)
  have hsm := hf.smooth 1 L' hL' (fun x => hL0 (x 0)) w
  have hg : ContDiff ℝ ∞ fun t : ℝ => f (w + L' (fun _ => t)) :=
    hsm.comp (contDiff_pi.2 fun _ => contDiff_id)
  have e : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f w) =
      fun t : ℝ => Complex.exp (φ t) * f (w + L' (fun _ => t)) := by
    funext t
    rw [heisOF, hlam _ (GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ w (L t) (hL0 t))]
    rfl
  rw [e]
  have hd1 : DifferentiableAt ℝ (fun t : ℝ => Complex.exp (φ t)) 0 :=
    ((φ.toRealLinearMap hφ).differentiableAt).cexp
  exact hd1.mul ((hg.differentiable (by simp)) 0)
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ResEtaFOfPow
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open Classical in
theorem resEtaF_of_resEtaPow_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (n : ℕ),
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n → Formalism.IndefR.DatumF.ResEtaF χ n := by
  intro F E _ _ _ _ _ σ B hB χ n hχ
  have hcm : IsCMExt F E σ := hB.cm
  refine ⟨exists_isEtaF hcm, fun η hη a => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := hη
  have hS : ∀ x ∈ normGrp F E, η x = 1 := by
    have : normGrp F E ≤ η.ker := sup_le (by rintro _ ⟨y, rfl⟩; exact h1 y) (by rintro _ ⟨y, rfl⟩; exact h2 y)
    exact fun x hx => this hx
  have hsq : ∀ x, η x * η x = 1 := fun x => by rw [← map_mul]; exact hS _ (sq_mem_normGrp hcm x)
  have key : ∀ x, ((χ (Formalism.IndefR.DatumF.idFF F E x) : Circle) : ℂ) = if x ∈ normGrp F E then 1 else (-1) ^ n :=
    fun x => hχ x
  apply Circle.ext
  rw [key a, Circle.coe_pow]
  by_cases ha : a ∈ normGrp F E
  · rw [if_pos ha, hS a ha]; simp
  rw [if_neg ha]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · rw [← two_mul, pow_mul, pow_mul, neg_one_sq, one_pow, ← Circle.coe_pow, sq, hsq a]; simp
  have hn1 : ((-1 : ℂ)) ^ n = -1 := hn.neg_one_pow
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push_neg at hh
    exact h3 (MonoidHom.ext hh)
  have hbS : b ∉ normGrp F E := fun hm => hb (hS b hm)
  have hab : a * b ∈ normGrp F E := by
    by_contra hn2
    have e := key (a * b)
    rw [map_mul, map_mul, Circle.coe_mul, key a, key b, if_neg ha, if_neg hbS, if_neg hn2, hn1] at e
    norm_num at e
  have hηb : (η b : ℂ) = -1 := GlobalTheory.VolHeckeCompare.circle_eq_neg_one (hsq b) hb
  have e2 : (η a : ℂ) * η b = 1 := by rw [← Circle.coe_mul, ← map_mul, hS _ hab]; simp
  rw [hηb] at e2
  have hηa : (η a : ℂ) = -1 := by linear_combination -e2
  rw [hηa]
end GlobalTheory.ResEtaFOfPow
end
end
end
