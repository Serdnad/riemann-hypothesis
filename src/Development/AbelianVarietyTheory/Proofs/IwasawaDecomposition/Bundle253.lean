module

import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDictionaryCoreLawsBaseFrameChange
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle249
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle250
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem

theorem host_cmData : ∀ (R : Ranks) (H : Host R), @CMData H.F H.E _ _ _ _ H.cmStar _ := by
  apply Formalism.BasicNotions.Examples₂.cmData <;> assumption

end GlobalTheory.Mem
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_core_laws_for_replaced_hecke_characters : ∀ (D : D7) (T : CoreJ D) (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle), LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj T.σ₀ σ (chiW j T.σ₀) (chiW j σ)) → ∃ mu, LawsJ (reCore T T.dict mu chiW T.x₀ T.cE) ∧ LawsCore (reCore T T.dict mu chiW T.x₀ T.cE).toCore := by
  first | exact @GlobalTheory.RealGeo.exists_mu_reCore | exact GlobalTheory.RealGeo.exists_mu_reCore | (intros; apply GlobalTheory.RealGeo.exists_mu_reCore <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_geometric_half_realisation_geometric_action : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), PreChar R → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → Fired T R κ v₀ O ph → ∃ B : GeoHalf T (geoR T R κ v₀ O) ph, B.κ = κ ∧ B.v₀ = v₀ ∧ Fired T (geoR T R κ v₀ O) B.κ B.v₀ B.O ph ∧ PreChar (geoR T R κ v₀ O) ∧ (geoR T R κ v₀ O).grp_chiW := by
  first | exact @GlobalTheory.RealGeo.exists_geoHalf_geoR | exact GlobalTheory.RealGeo.exists_geoHalf_geoR | (intros; apply GlobalTheory.RealGeo.exists_geoHalf_geoR <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_dictionary_core_laws_baseFrame_change : ∀ (D : D7) (T : CoreJ D) (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), VolTieG D → LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ)) → ∃ dict, LawsJ (reCore T dict T.mu T.chiW x₀ T.cE) ∧ LawsCore (reCore T dict T.mu T.chiW x₀ T.cE).toCore := by
  first | exact @GlobalTheory.BaseFrameChange.exists_dict_of_x0Orth | exact GlobalTheory.BaseFrameChange.exists_dict_of_x0Orth | (intros; apply GlobalTheory.BaseFrameChange.exists_dict_of_x0Orth <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo.FrameModels

theorem card_signs {n p q : ℕ} (hpq : p + q = n) :
    (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true).card = p ∧
      (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = false).card = q := by
  have h1 : (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true).card = p := by
    have : (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true) =
        Finset.univ.map (Fin.castLEEmb (by omega : p ≤ n)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_map]
      constructor
      · intro ha
        exact ⟨⟨a, ha⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        simp
    rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  refine ⟨h1, ?_⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun a : Fin n => decide ((a : ℕ) < p) = true)
  simp only [Bool.not_eq_true] at h2
  rw [h1, Finset.card_univ, Fintype.card_fin] at h2
  omega


open Formalism.L2.NTheta in
theorem goodPar_holPar {R : Ranks} (h : HCParam R) {n p q : ℕ} (hn : n = R.r) (hpq : p + q = n) :
    GoodPar n p q (holPar p q (kapW h p q)) := by
  have hs : StrictAnti fun a : Fin n => ((lamAt h a : ℚ) : ℝ) := fun a b hab => by
    have := GlobalTheory.HolDict.lamAt_strictAnti h hn hab
    show ((lamAt h b : ℚ) : ℝ) < ((lamAt h a : ℚ) : ℝ)
    exact_mod_cast this
  refine ⟨fun a => (lamAt h a : ℝ), fun a => decide ((a : ℕ) < p), ⟨hs, fun a => lamAt h a, fun a => rfl,
    GlobalTheory.HolDict.holPar_kapW_eq h hn hpq⟩, ⟨hs, fun a => ?_⟩, (card_signs hpq).1, (card_signs hpq).2⟩
  obtain ⟨z, hz⟩ := lamAt_int h a
  obtain ⟨s, hs'⟩ := odd_r R
  refine ⟨z - s, ?_⟩
  have hn' : ((n : ℕ) : ℝ) = 2 * s + 1 := by rw [hn, hs']; push_cast; rfl
  show ((lamAt h a : ℚ) : ℝ) - _ = _
  rw [hz, hn']
  push_cast
  ring

theorem goodPar_dualPar {n p q : ℕ} {S : SPar} (h : GoodPar n p q S) : GoodPar n p q (dualPar S) := by
  obtain ⟨lam, ε, ⟨hl, r, hr, hS⟩, ⟨-, hi⟩, hp, hq⟩ := h
  have hs : StrictAnti fun a => -lam (Fin.rev a) := fun a b hab => neg_lt_neg (hl (Fin.rev_lt_rev.2 hab))
  refine ⟨fun a => -lam (Fin.rev a), fun a => ε (Fin.rev a), ⟨hs, fun a => -r (Fin.rev a), fun a => by simp [hr], ?_⟩,
    ⟨hs, fun a => ?_⟩, ?_, ?_⟩
  · rw [hS]
    ext z
    simp only [dualPar, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨Fin.rev a, by simp⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨Fin.rev a, rfl⟩, rfl⟩
  · obtain ⟨m, hm⟩ := hi (Fin.rev a)
    refine ⟨-m - n + 1, ?_⟩
    push_cast
    linarith
  · rw [← hp]
    exact Finset.card_equiv Fin.revPerm (by simp)
  · rw [← hq]
    exact Finset.card_equiv Fin.revPerm (by simp)

variable {D : D7}

theorem sig_add (i : Fin D.R.m) (ρ : D.what₂.Tau) :
    ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = (Wc D i).rank := by
  rw [show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _, D.sp.W_rank _ (Nat.le_add_left _ _) i.2]
  have := D.R.m_add_three_le_k
  have hi := i.2
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem goodPar_parAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    GoodPar (Wc D i).rank ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (parAt (Wc D i) σ ρ) := by
  have h := goodPar_holPar (D.hc (lab σ ρ)) (D.sp.W_rank _ (Nat.le_add_left _ _) i.2) (sig_add i ρ)
  unfold Links.parAt
  split_ifs
  · exact h
  · exact goodPar_dualPar h

theorem parAt_congr (W : HSp D) {σ σ' : D.what₂.LL →+* ℂ} (h : labE σ = labE σ') : parAt W σ = parAt W σ' := by
  have hl : lab σ = lab σ' := by
    funext ρ
    unfold lab
    rw [h]
  funext ρ
  unfold Links.parAt kapAt
  rw [h, hl]

theorem exists_frameKs : GlobalTheory.Published.DiscreteSeriesExists → ∀ (D : D7) (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL], (∀ x, D.embE x ∈ (algebraMap Ks D.what₂.LL).range) → ∃ MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ), FrameKs Ks MW := by
  intro hP D Ks _ _ hK
  classical
  have hne : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), Nonempty (DSModel (Wc D i) (parAt (Wc D i) σ)) := fun i σ =>
    GlobalTheory.Published.dsExists_of_discreteSeriesExists hP D _ _ (D.sp.W_sig _) (goodPar_parAt i σ)
  have hx : ∀ (V : HSp D) (S S' : D.what₂.Tau → SPar) (h : Nonempty (DSModel V S)) (h' : Nonempty (DSModel V S')), S = S' →
      ∀ ρ, x0Mat (Classical.choice h) ρ = x0Mat (Classical.choice h') ρ := by
    intro V S S' h h' e ρ
    subst e
    rfl
  refine ⟨fun i σ => Classical.choice (hne i σ), fun i σ σ' hσ ρ => hx _ _ _ _ _ (parAt_congr _ ?_) ρ, fun i σ hσ τ a => ?_⟩
  · funext τ
    ext x
    obtain ⟨y, hy⟩ := hK (D.host.sigmaOf (D.eTau τ).1 x)
    show σ (D.embE (D.host.sigmaOf (D.eTau τ).1 x)) = σ' (D.embE (D.host.sigmaOf (D.eTau τ).1 x))
    rw [← hy]
    exact RingHom.congr_fun hσ y
  · have he := (Classical.choice (hne i σ)).enum τ
    have e : parAt (Wc D i) σ τ = Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) σ τ) := if_pos (hσ τ)
    rw [e] at he
    exact (GlobalTheory.HolDict.isEnum_holPar_kapW _ (D.sp.W_rank _ (Nat.le_add_left _ _) i.2) (sig_add i τ) he a).2

end GlobalTheory.RealGeo.FrameModels
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.nonempty_hostHeckeCharacterFrame : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ), (∀ k, _root_.GlobalTheory.Mem.Chr.SplitsC H.E (H.g k)) → _root_.GlobalTheory.Mem.Chr.SplitsC H.E H.pde → _root_.GlobalTheory.Mem.Chr.SplitsC H.E H.pde' → (∀ j τ, ∃ z : ℤ, e j τ = z) → (∀ j, UpperTheory.MUQ (_root_.Formalism.L2.Host.embPsi H) (e j)) → Nonempty (_root_.GlobalTheory.Mem.Chr.HFrame H e) := by
  first | exact @GlobalTheory.nonempty_hFrame | exact GlobalTheory.nonempty_hFrame | (intros; apply GlobalTheory.nonempty_hFrame <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

theorem _root_.GlobalTheory.T.exists_ext_place_of_ne_zero_maximal : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] [CharZero R] (𝔪 : Ideal R), 𝔪.IsMaximal → ∀ g : R, g ≠ 0 → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : R →+* e.O), (∀ a : 𝓞 F, ((φ (algebraMap (𝓞 F) R a) : e.O) : AlgebraicClosure F) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a)) ∧ (IsLocalRing.maximalIdeal e.O).comap φ = 𝔪 ∧ φ g ≠ 0 := by
  first | exact @GlobalTheory.TrueGeo.HorizRing.main | exact GlobalTheory.TrueGeo.HorizRing.main | (intros; apply GlobalTheory.TrueGeo.HorizRing.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoefReal

open GlobalTheory.CoefModel

theorem vact_eq_actP {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) :
    vact lam (fun τ => (g τ : Matrix (Fin n) (Fin n) ℂ)) = actP lam (invTrK g) := by
  unfold vact actP trAct
  rw [detTw_eq]
  simp only [invTrK_coe, Matrix.transpose_transpose, Matrix.det_transpose, Pi.inv_apply, Matrix.coe_units_inv,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', _root_.zpow_neg, _root_.inv_zpow]

theorem continuous_coeff_actP {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {X : Type} [TopologicalSpace X]
    (A : X → ι → GL (Fin n) ℂ) (hA : ∀ τ, Continuous fun x => (A x τ : Matrix (Fin n) (Fin n) ℂ)) (F : Pol ℂ ι n)
    (m : ι × Fin n × Fin n →₀ ℕ) : Continuous fun x => AddMonoidAlgebra.coeff (actP lam (A x) F) m := by
  simp only [actP, LinearMap.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul, detTw_eq, AlgHom.toLinearMap_apply, trAct]
  refine Continuous.mul (continuous_finsetProd _ fun τ _ => (hA τ).matrix_det.zpow₀ _ fun x => Or.inl ?_)
    (continuous_coeff_blockAct _ (fun τ => (hA τ).matrix_transpose) _ m)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (A x τ).isUnit).ne_zero

theorem exists_scalarExt {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n)
    {W : Type} [AddCommGroup W] [Module ℂ W] (c0 : VV K lam →ₛₗ[φ] W)
    (h1 : LinearIndependent ℂ fun i => c0 (bVV K lam i))
    (h2 : Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) = ⊤) :
    ∃ e : VV ℂ lam ≃ₗ[ℂ] W, ∀ v, e (mapVV φ lam v) = c0 v := by
  let b1 := Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge
  let b2 := Module.Basis.mk h1 h2.ge
  refine ⟨b1.equiv b2 (Equiv.refl _), fun v => ?_⟩
  have : (b1.equiv b2 (Equiv.refl _)).toLinearMap.comp (mapVV φ lam) = c0 := by
    refine (bVV K lam).ext fun i => ?_
    have h := b1.equiv_apply i b2 (Equiv.refl _)
    simpa [b1, b2] using h
  exact LinearMap.congr_fun this v

variable {D : D7}

theorem exists_real_model (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank)
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W) (hθ : IsInfFam θ) (hc : c.Is)
    (ht : Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam)) :
    ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, (∀ v, e (mapVV D.what₂.embLL lam v) = c0 v) ∧
      ∀ u ∈ GinfC V, ∀ v, c.ρ u (e v) = e (rhoK lam (invTrK (realGL θ V u)) v) := by
  obtain ⟨e, he⟩ : ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, ∀ v, e (mapVV D.what₂.embLL lam v) = c0 v :=
    exists_scalarExt D.what₂.embLL lam c0 ht.2.1 ht.2.2
  refine ⟨e, he, fun u hu v => ?_⟩
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hlab : ∀ τ x, D.what₂.embLL (labLL D τ x) = tauE D τ x := fun τ x =>
    DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x
  have hrat : ∀ (γ : GQ V) (v : VV ℂ lam), c.ρ γ.1 (e v) = e (rhoK lam (invTrK (realGL θ V γ.1)) v) := by
    intro γ v
    obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat V γ γE := by
      obtain ⟨γ, ⟨g, -, hg⟩⟩ := γ
      exact ⟨g, hg.symm⟩
    have e1 : (fun τ => Formalism.UG.bc D.what₂.embLL (invTrK (embGL (labLL D) γE) τ)) = invTrK (realGL θ V γ) := by
      funext τ
      apply Units.ext
      rw [bc_coe, invTrK_coe, invTrK_coe, realGL_rat hθ V γ γE hγ, embGL_inv, ← map_inv, embGL_coe, bc_coe]
      ext a b
      exact hlab _ _
    have : (c.ρ γ).comp e.toLinearMap = e.toLinearMap.comp (rhoK lam (invTrK (realGL θ V γ))) := by
      refine LinearMap.ext_on_range (span_mapVV D.what₂.embLL lam) fun i => ?_
      show c.ρ γ (e _) = e (rhoK lam (invTrK (realGL θ V γ)) _)
      rw [← e1, ← mapVV_rhoK, he, he]
      exact (ht.1 γ γE hγ _).symm
    exact LinearMap.congr_fun this v
  have hfin : ∀ k ∈ GfC V, realGL θ V k = 1 := fun k hk => funext fun τ => by
    show Formalism.UG.bc (θ τ) (infHom V k) = 1
    rw [show infHom V k = 1 from hk, map_one]
  rw [← e.symm_apply_eq]
  refine Subtype.ext (MvPolynomial.ext _ _ fun m => ?_)
  let L : c.W →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ m ∘ₗ (VV ℂ lam).subtype ∘ₗ e.symm.toLinearMap
  have hf : Continuous fun h => L (c.ρ h (e v)) := L.continuous_of_finiteDimensional.comp (hc.2.2.1 _)
  have hg : Continuous fun h => AddMonoidAlgebra.coeff (actP lam (invTrK (realGL θ V h)) v.1) m := by
    refine continuous_coeff_actP lam _ (fun τ => ?_) _ m
    refine (((realGL_laws hθ V).1 τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show (realGL θ V h⁻¹ τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ = _
    rw [map_inv]
    rfl
  by_contra hne
  obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V u hu _ (isOpen_ne_fun hf hg) hne
  refine hU ?_
  show L (c.ρ (γ * k) (e v)) = AddMonoidAlgebra.coeff (actP lam (invTrK (realGL θ V (γ * k))) v.1) m
  rw [map_mul, map_mul (realGL θ V), hc.1 k hk, hfin k hk, mul_one, mul_one, hrat ⟨γ, hγ⟩ v]
  simp [L, rhoK_coe]

theorem exists_poly_model : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W), IsInfFam θ → c.Is → Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → ∀ BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsUnit (BS τ)) → ∃ j : c.W →ₗ[ℂ] Pol ℂ D.what₂.Tau V.rank, LinearMap.range j = VV ℂ lam ∧ ∀ u ∈ GinfC V, ∀ w, j (c.ρ u w) = vact lam (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) (j w) := by
  intro D V θ c lam c0 hθ hc ht BS hBS
  obtain ⟨e, -, he⟩ := exists_real_model V θ c lam c0 hθ hc ht
  choose B hB using hBS
  refine ⟨(VV ℂ lam).subtype ∘ₗ rhoK lam (invTrK B⁻¹) ∘ₗ e.symm.toLinearMap, ?_, fun u hu w => ?_⟩
  · have hs : Function.Surjective (rhoK lam (invTrK B⁻¹)) := fun x => ⟨rhoK lam (invTrK B) x, by
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]⟩
    rw [LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      LinearMap.range_eq_top.2 hs, Submodule.map_top,
      Submodule.range_subtype]
  · obtain ⟨v, rfl⟩ := e.surjective w
    have e1 : (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) =
        fun τ => (((B⁻¹ * realGL θ V u * B) τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
      funext τ
      rw [← hB τ, ← Matrix.coe_units_inv]
      rfl
    rw [e1, vact_eq_actP, he u hu v]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.subtype_apply]
    rw [← rhoK_coe, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
      mul_inv_cancel_right]

end GlobalTheory.CoefReal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_column_highest_weight_polynomial_map : ∀ (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (U : Submodule ℂ (X →ₗ[ℂ] Pol ι m n)), U ≠ ⊥ → (∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) → ∃ Φ ∈ U, Φ ≠ 0 ∧ (∀ τ k l, k < l → colLie m τ k l ∘ₗ Φ = 0) ∧ ∃ μ : ι → Fin n → ℤ, ∀ τ k, colLie m τ k k ∘ₗ Φ = (μ τ k : ℂ) • Φ := by
  first | exact @GlobalTheory.DefLift.exists_colHighest | exact GlobalTheory.DefLift.exists_colHighest | (intros; apply GlobalTheory.DefLift.exists_colHighest <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

theorem exists_valuation_point {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (y : M.Z) :
    ∃ (V : ValuationSubring Ω) (v : Sp V ⟶ M.Z), spMap (algebraMap V Ω) ≫ v = M.pt ∧
      v (IsLocalRing.closedPoint V) = y := by
  haveI : IsLocalRing (M.O y).toSubring := inferInstanceAs (IsLocalRing (M.O y))
  obtain ⟨V, hle, hloc⟩ := (LocalSubring.mk (M.O y).toSubring).exists_le_valuationSubring
  let ψ : M.Z.presheaf.stalk y →+* V :=
    (M.stalkHom y).codRestrict V (fun a => hle (M.stalkEquiv y a).2)
  haveI : IsLocalHom ψ := ⟨fun a ha => by
    have h1 : IsUnit (Subring.inclusion hle (M.stalkEquiv y a)) := ha
    exact (MulEquiv.isUnit_map (M.stalkEquiv y)).1 (hloc.map_nonunit _ h1)⟩
  refine ⟨V, spMap ψ ≫ M.Z.fromSpecStalk y, ?_, ?_⟩
  · have hs := M.pt_specializes (IsLocalRing.closedPoint Ω) y
    have hc : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V Ω) =
        M.Z.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt := by
      ext a
      rfl
    calc spMap (algebraMap V Ω) ≫ spMap ψ ≫ M.Z.fromSpecStalk y
        = Spec.map (CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V Ω)) ≫ M.Z.fromSpecStalk y := by
          rw [Spec.map_comp, Category.assoc]
      _ = Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt) ≫
            Spec.map (M.Z.presheaf.stalkSpecializes hs) ≫ M.Z.fromSpecStalk y := by
          rw [hc, Spec.map_comp, Category.assoc]
      _ = M.pt := by
          rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · have ec : spMap ψ (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint _ := IsLocalRing.comap_closedPoint ψ
    show M.Z.fromSpecStalk y (spMap ψ (IsLocalRing.closedPoint V)) = y
    rw [ec]
    exact Scheme.fromSpecStalk_closedPoint

theorem exists_valuation_point_var {F : Type} [Field F] (Y : Var F) (y : Y.X) :
    ∃ (V : ValuationSubring Y.Fn) (v : Sp V ⟶ Y.X), spMap (algebraMap V Y.Fn) ≫ v = (ratOf Y).pt ∧
      v (IsLocalRing.closedPoint V) = y :=
  exists_valuation_point (ratOf Y) y

theorem lift_specializes_genericPoint : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ q : Sp Y₁.Fn ⟶ Y₂.X, q ≫ f₂ = (ratOf Y₁).pt ≫ f₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt q → ∀ y : Y₁.X, (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (p' : Sp K ⟶ Y₂.X), p (IsLocalRing.closedPoint K) = y → p ≫ f₁ = p' ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p p' → p' (IsLocalRing.closedPoint K) = genericPoint Y₂.X) → q (IsLocalRing.closedPoint Y₁.Fn) ⤳ genericPoint Y₂.X := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ q hq hco y hy
  obtain ⟨V, v, hvg, hvc⟩ := exists_valuation_point_var Y₁ y
  have hs : f₂ ≫ X.str = Y₂.str := h₂.1.inducedModelMorphism_comp_structureMap
  haveI : IsProper (f₂ ≫ X.str) := hs ▸ inferInstance
  haveI : UniversallyClosed f₂ := UniversallyClosed.of_comp_of_isSeparated f₂ X.str
  have hE : ValuativeCriterion.Existence f₂ :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f₂) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) f₂).1
  have hsq : q ≫ f₂ = spMap (algebraMap V Y₁.Fn) ≫ (v ≫ f₁) := by
    exact hq.trans ((congrArg (· ≫ f₁) hvg.symm).trans (Category.assoc _ _ _))
  obtain ⟨⟨l⟩⟩ := hE { R := V, K := Y₁.Fn, i₁ := q, i₂ := v ≫ f₁, commSq := ⟨hsq⟩ }
  have hl₁ : spMap (algebraMap V Y₁.Fn) ≫ l.l = q := l.fac_left
  have hl₂ : l.l ≫ f₂ = v ≫ f₁ := l.fac_right
  have hinc := GlobalTheory.T.fullFlag_common_closedPoint_of_generic F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ V Y₁.Fn v l.l hl₂.symm
    (by
      have e : spMap (algebraMap V Y₁.Fn) ≫ v ≫ f₁ = (ratOf Y₁).pt ≫ f₁ :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f₁) hvg)
      have key : ∀ (x x' : Sp Y₁.Fn ⟶ X.X) (p p' : Sp Y₁.Fn ⟶ Y₁.X) (r r' : Sp Y₁.Fn ⟶ Y₂.X), x = x' → p = p' →
          r = r' → CoBear Eb S₁ φ₁ S₂ φ₂ x p r → CoBear Eb S₁ φ₁ S₂ φ₂ x' p' r' := by
        rintro _ _ _ _ _ _ rfl rfl rfl h
        exact h
      exact key _ _ _ _ _ _ e.symm hvg.symm hl₁.symm hco)
  have ec : spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) =
      IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint (IsLocalRing.residue V)
  have hp' := hy (IsLocalRing.ResidueField V) (spMap (IsLocalRing.residue V) ≫ v)
    (spMap (IsLocalRing.residue V) ≫ l.l)
    (by
      show v (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint _)) = y
      rw [ec]
      exact hvc)
    ((Category.assoc _ _ _).trans ((congrArg (spMap (IsLocalRing.residue V) ≫ ·) hl₂.symm).trans
      (Category.assoc _ _ _).symm))
    (by convert hinc using 1; exact Category.assoc _ _ _)
  have e2 : l.l (IsLocalRing.closedPoint V) = genericPoint Y₂.X := by
    change l.l (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint _)) = _ at hp'
    rwa [ec] at hp'
  have e1 : q (IsLocalRing.closedPoint Y₁.Fn) =
      l.l (spMap (algebraMap V Y₁.Fn) (IsLocalRing.closedPoint Y₁.Fn)) := by
    have := congrArg (fun g : Sp Y₁.Fn ⟶ Y₂.X => g (IsLocalRing.closedPoint Y₁.Fn)) hl₁
    exact this.symm
  have h2 := (IsLocalRing.specializes_closedPoint
    (spMap (algebraMap V Y₁.Fn) (IsLocalRing.closedPoint Y₁.Fn))).map l.l.continuous
  convert h2 using 1
  exact e2.symm

end GlobalTheory.FlagBundle
end
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


theorem _root_.GlobalTheory.T.admissible_form_eq_mul_point_class_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), ∃ β : ℝ, ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ → Θ P = β * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  first | exact @GlobalTheory.GrassTop.span_point | exact GlobalTheory.GrassTop.span_point | (intros; apply GlobalTheory.GrassTop.span_point <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.smooth_vector_word_action_continuous : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ w ∈ smSub G (trRep σ P), Continuous fun g : Formalism.REAL.UJ ε => word (trRep σ P) l (σ (umat g) w) := by
  first | exact @GlobalTheory.SmVec.WordCont.continuous_word_translate | exact GlobalTheory.SmVec.WordCont.continuous_word_translate | (intros; apply GlobalTheory.SmVec.WordCont.continuous_word_translate <;> assumption)
end
