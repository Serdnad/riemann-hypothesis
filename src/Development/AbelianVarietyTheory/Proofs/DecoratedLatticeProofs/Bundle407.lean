module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle348
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle564
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle592
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle373
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle377
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle382
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle381
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (ipO Place IsBaseOff)

noncomputable section

namespace GlobalTheory.TwistNorm

theorem level_trivial_eq_ofLocal {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) :
    LevelP.triv Pg r ℂ = LevelP.ofLocal (fun _ => ⊥) (fun _ => 1) := by
  have hH : (Subgroup.pi Set.univ fun PP : ↥Pg => (⊥ : Subgroup (GL (Fin r) (kP PP.1)))) = ⊥ := by
    ext g
    simp [Subgroup.mem_pi, funext_iff]
  haveI : Subsingleton (↥(⊥ : Subgroup (G0 Pg r)) →* ℂˣ) :=
    ⟨fun f g => MonoidHom.ext fun y => by rw [Subsingleton.elim y 1, map_one, map_one]⟩
  unfold LevelP.triv LevelP.ofLocal
  congr 1
  · exact hH.symm
  · exact Subsingleton.helim (congrArg (fun H : Subgroup (G0 Pg r) => (↥H →* ℂˣ)) hH.symm) _ _

theorem norm_sq_eq_inner_product {D : D7} {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (g : WO S T → ℂ) :
    ((nrm2 μ 𝓕 g : ℝ) : ℂ) = ipO μ 𝓕 g g := by
  unfold nrm2 ipO
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem chainStep_twisted_normSq_eq_untwisted_mul_localFactors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (f₀ : WO S T → ℂ) (m : Measure (WO S T)) (X : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) m X → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (r t j t' : ℕ) (hr : r ≤ S.rank), S.rank + t' = T.rank → ∀ (Pg Q : Finset (Pl D.host.E)), Disjoint Pg Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f f' : WO S T → ℂ), IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (Lev.datY S.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B) χj Q ξ f₀ f → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (Lev.datY S.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) χj ∅ ξ' f₀ f' → nrm2 m X f = nrm2 m X f' * ∏ PP ∈ Q, (zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹) := by
  classical
  intro D ψ θ S T sS sT ΛS ΛT βS βT f₀ m X hB hC hFS hFT r t j t' hr ht Pg Q hdisj hQ2 χ χj ξ ξ' f f' hf hf'
  have hP : (Lev.datY S.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B).P =
      LevelP.ofLocal (Pg := Pg) (r := r) (LL := ℂ) (fun _ => ⊥) (fun _ => 1) := by
    show (if Lev.Frm.B = Lev.Frm.B then LevelP.triv Pg r ℂ else (LevelP.triv Pg r ℂ).conj) = _
    rw [if_pos rfl]
    exact level_trivial_eq_ofLocal Pg r
  have hP' : (Lev.datY S.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B).P =
      LevelP.ofLocal (Pg := Pg) (r := r) (LL := ℂ) (fun _ => ⊥) (fun _ => 1) := by
    show (if Lev.Frm.B = Lev.Frm.B then LevelP.triv Pg r ℂ else (LevelP.triv Pg r ℂ).conj) = _
    rw [if_pos rfl]
    exact level_trivial_eq_ofLocal Pg r
  obtain ⟨⟨x, hx⟩, hall⟩ := GlobalTheory.StepVec.stepVecLocal D ψ θ S T sS sT ΛS ΛT βS βT _ χj Q ξ f₀ f m X t' ht _ _ hP hB hC
    hFS hFT hdisj hf
  have hall' := (GlobalTheory.StepVec.stepVecLocal D ψ θ S T sS sT ΛS ΛT βS βT _ χj ∅ ξ' f₀ f' m X t' ht _ _ hP' hB hC hFS hFT
    (Finset.disjoint_empty_right _) hf').2
  obtain ⟨hvac, e, ⟨⟨es, hes, rfl⟩, hce⟩, -⟩ := hf
  have hes' : ∀ PP ∈ Pg ∪ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP := hes
  have hce' : (∑ PP ∈ Pg ∪ Q, es PP) * cA D (∑ PP ∈ Pg ∪ Q, es PP) = 0 := hce
  have hsum := GlobalTheory.SplitIdemDict.idem_dictionary D
  choose vA φA hφA hprA using fun i : ↥(Pg ∪ Q) => hsum.1 (es i.1) i.1 (hes' i.1 i.2)
  have hunder : ∀ i : ↥(Pg ∪ Q), (i.1).asIdeal.under (𝓞 D.host.F) = (vA i).asIdeal := fun i =>
    (hsum.2 _ _ _ (hprA i)).1
  have hcross := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es (Pg ∪ Q)
    (fun i hi => (hes' i hi).1.1) hce'
  have hinj : Function.Injective vA := by
    intro i j hij
    have h1 := (hφA i).2.1
    have h2 := (hφA j).2.1
    rw [hij] at h1
    have h3 := GlobalTheory.PlaceDatum.idempotent_eq_of_orthogonal_decomp (hes' i.1 i.2).1.1 (hes' i.1 i.2).1.2.1 (hes' j.1 j.2).1.1
      (hes' j.1 j.2).1.2.1 (h1.trans h2.symm) (hcross _ i.2 _ j.2) (hcross _ j.2 _ i.2)
    exact Subtype.ext (GlobalTheory.StepVec.prime_eq_of_idem (hes' i.1 i.2) (h3 ▸ hes' j.1 j.2))

  obtain ⟨x', hx'l, hx'r⟩ : ∃ x' : Place D → WO S T → ℂ, (∀ τ, x' (.inr τ) = f₀) ∧
      ∀ v, x' (.inl v) = if ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal then x (.inl v) else f₀ :=
    ⟨Sum.elim (fun v => if ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal then x (.inl v) else f₀) fun _ => f₀,
      fun _ => rfl, fun _ => rfl⟩
  have hpure' := hall' x' ⟨⟨hx'l, fun v hv => by
      rw [hx'r, if_neg]
      rintro ⟨PP, h1, h2⟩
      exact hv PP (Finset.mem_union_left _ h1) h2⟩,
    fun v φ e' he' mu => ⟨fun PP hpp hmu J lam hJ => by
      have h := (hx.2 v φ e' he' mu).1 PP hpp hmu J lam hJ
      rw [hx'r, if_pos ⟨PP.1, PP.2, (hsum.2 v φ PP.1 hpp).1⟩]
      exact h, fun PP hq => by simp at hq⟩⟩
  have hpure := hall x hx
  obtain ⟨hfin, hxx⟩ := GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod D ψ θ S T sS sT ΛS ΛT f₀ m X hB hC x x f f
    hpure hpure
  obtain ⟨-, hxx'⟩ := GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod D ψ θ S T sS sT ΛS ΛT f₀ m X hB hC x' x' f' f'
    hpure' hpure'
  have h0 : ipO m X f₀ f₀ = 1 := by
    rw [← norm_sq_eq_inner_product, hvac.2.norm.2 (m, X) hC]
    simp

  let iq : ↥Q → ↥(Pg ∪ Q) := fun i => ⟨i.1, Finset.mem_union_right _ i.2⟩
  let U : Finset (Place D) := Q.attach.image fun i => (Sum.inl (vA (iq i)) : Place D)
  have hnotPg : ∀ i : ↥Q, ¬ ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = (vA (iq i)).asIdeal := by
    rintro i ⟨PP, hPP, hu⟩
    have h1 : vA ⟨PP, Finset.mem_union_left _ hPP⟩ = vA (iq i) := HeightOneSpectrum.ext ((hunder _).symm.trans hu)
    have h2 : PP = i.1 := congrArg Subtype.val (hinj h1)
    exact Finset.disjoint_left.1 hdisj hPP (by rw [h2]; exact i.2)
  have hpt : ∀ p, ipO m X (x p) (x p) =
      ipO m X (x' p) (x' p) * (if p ∈ U then ipO m X (x p) (x p) else 1) := by
    intro p
    by_cases hp : p ∈ U
    · rw [if_pos hp]
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
      rw [hx'r, if_neg (hnotPg i), h0, one_mul]
    · rw [if_neg hp, mul_one]
      rcases p with v | τ
      · rw [hx'r]
        by_cases hv : ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal
        · rw [if_pos hv]
        · rw [if_neg hv]
          have hxv : x (.inl v) = f₀ := hx.1.2 v fun PP hPP hu => by
            rcases Finset.mem_union.1 hPP with h | h
            · exact hv ⟨PP, h, hu⟩
            · exact hp (Finset.mem_image.2 ⟨⟨PP, h⟩, Finset.mem_attach _ _,
                congrArg Sum.inl (HeightOneSpectrum.ext ((hunder _).symm.trans hu))⟩)
          rw [hxv]
      · rw [hx'l, hx.1.1 τ]
  let s0 : Finset (Place D) := hfin.toFinset ∪ U
  have hA : ∏ᶠ p, ipO m X (x p) (x p) = ∏ p ∈ s0, ipO m X (x p) (x p) :=
    finprod_eq_prod_of_mulSupport_subset _ fun p hp => Finset.mem_union_left _ (hfin.mem_toFinset.2 hp)
  have hA' : ∏ᶠ p, ipO m X (x' p) (x' p) = ∏ p ∈ s0, ipO m X (x' p) (x' p) := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun p hp => ?_
    by_cases hU : p ∈ U
    · exact Finset.mem_union_right _ hU
    · refine Finset.mem_union_left _ (hfin.mem_toFinset.2 ?_)
      have h := hpt p
      rw [if_neg hU, mul_one] at h
      rw [Function.mem_mulSupport] at hp ⊢
      rwa [h]
  have hsplit : ∏ p ∈ s0, ipO m X (x p) (x p) =
      (∏ p ∈ s0, ipO m X (x' p) (x' p)) * ∏ p ∈ U, ipO m X (x p) (x p) := by
    rw [Finset.prod_congr rfl fun p _ => hpt p, Finset.prod_mul_distrib, Finset.prod_ite_mem,
      Finset.inter_eq_right.2 Finset.subset_union_right]
  have hU : ∏ p ∈ U, ipO m X (x p) (x p) = ∏ i ∈ Q.attach, ipO m X (x (.inl (vA (iq i)))) (x (.inl (vA (iq i)))) := by
    refine Finset.prod_image fun i _ j _ h => ?_
    have h1 := hinj (Sum.inl_injective h)
    have h2 : (iq i).1 = (iq j).1 := congrArg Subtype.val h1
    exact Subtype.ext h2
  have hloc : ∀ i : ↥Q, ipO m X (x (.inl (vA (iq i)))) (x (.inl (vA (iq i)))) =
      ((zinv i.1 0 r * ((Ideal.absNorm i.1.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹ : ℝ) : ℂ) := by
    intro i
    obtain ⟨mu, hmu⟩ := (GlobalTheory.PlaceRed.red_dict D (vA (iq i)) (φA (iq i)) i.1 (hprA (iq i))).2 (ξ i.1)⁻¹
    have hθ := (hx.2 (vA (iq i)) (φA (iq i)) (es i.1) (hφA (iq i)) mu).2 i.1 i.2 (hprA (iq i)) hmu
    rw [← norm_sq_eq_inner_product, GlobalTheory.T.normSq_thetaLocalDatum_at_twistPlace D ψ θ S T sS sT ΛS ΛT βS βT f₀ m X hB hC hFS hFT i.1 (vA (iq i)) (φA (iq i)) (es i.1)
      (hφA (iq i)) (hprA (iq i)) (GlobalTheory.T.homLatticeIdeal_isUnit_splitPlace D i.1 (hQ2 i.1 i.2) (vA (iq i)) (φA (iq i)) (hprA (iq i))) r hr (by omega)
      (ξ i.1)⁻¹ mu hmu _ hθ]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, Complex.ofReal_prod, norm_sq_eq_inner_product, norm_sq_eq_inner_product, hxx, hxx', hA, hA', hsplit, hU,
    Finset.prod_congr rfl fun i _ => hloc i,
    Finset.prod_attach Q fun PP => ((zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹ : ℝ) : ℂ)]

end GlobalTheory.TwistNorm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QValOuter

open AddMonoidAlgebra in
theorem aconv_cons {G : Type} [AddMonoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    (ofCoeff (aconv (e :: l)) : AddMonoidAlgebra ℂ G) = ofCoeff e * ofCoeff (aconv l) := by
  apply AddMonoidAlgebra.coeff_injective
  rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.coeff_finsuppSum]
  simp only [AddMonoidAlgebra.coeff_finsuppSum, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_ofCoeff]
  rfl

theorem aconv_nil {G : Type} [AddMonoid G] :
    (AddMonoidAlgebra.ofCoeff (aconv ([] : List (G →₀ ℂ))) : AddMonoidAlgebra ℂ G) = 1 := rfl

theorem aconv_pair {G : Type} [AddMonoid G] (c d : G →₀ ℂ) :
    (AddMonoidAlgebra.ofCoeff (aconv [c, d]) : AddMonoidAlgebra ℂ G) =
      AddMonoidAlgebra.ofCoeff c * AddMonoidAlgebra.ofCoeff d := by
  rw [aconv_cons, aconv_cons, aconv_nil, mul_one]

theorem aconv_pair_cons {G : Type} [AddMonoid G] (c d : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    aconv (aconv [c, d] :: l) = aconv (c :: d :: l) := by
  apply (AddMonoidAlgebra.ofCoeff_injective (R := ℂ) (M := G))
  rw [aconv_cons, aconv_pair, aconv_cons, aconv_cons, mul_assoc]

theorem mem_support_aconv_pair {G : Type} [AddMonoid G] (c d : G →₀ ℂ) {u : G} (hu : u ∈ (aconv [c, d]).support) :
    ∃ a ∈ c.support, ∃ b ∈ d.support, a + b = u := by
  classical
  have h : (AddMonoidAlgebra.ofCoeff c * AddMonoidAlgebra.ofCoeff d : AddMonoidAlgebra ℂ G).coeff u ≠ 0 := by
    rw [← aconv_pair]; exact Finsupp.mem_support_iff.1 hu
  rw [AddMonoidAlgebra.coeff_mul] at h
  simp only [AddMonoidAlgebra.coeff_ofCoeff] at h
  obtain ⟨a, ha, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨b, hb, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  by_cases hab : a + b = u
  · exact ⟨a, ha, b, hb, hab⟩
  · exact absurd (if_neg hab) h2

open MonoidAlgebra in
theorem conv_cons {G : Type} [Monoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    (ofCoeff (conv (e :: l)) : MonoidAlgebra ℂ G) = ofCoeff e * ofCoeff (conv l) := by
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.mul_def, MonoidAlgebra.coeff_finsuppSum]
  simp only [MonoidAlgebra.coeff_finsuppSum, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_ofCoeff]
  rfl

theorem conv_nil {G : Type} [Monoid G] :
    (MonoidAlgebra.ofCoeff (conv ([] : List (G →₀ ℂ))) : MonoidAlgebra ℂ G) = 1 := rfl

theorem mul_comm_of_support {G : Type} [Monoid G] (a b : MonoidAlgebra ℂ G)
    (h : ∀ x ∈ a.coeff.support, ∀ y ∈ b.coeff.support, x * y = y * x) : a * b = b * a := by
  rw [MonoidAlgebra.mul_def, MonoidAlgebra.mul_def]
  unfold Finsupp.sum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
  dsimp only
  rw [h x hx y hy, mul_comm (a.coeff x)]

theorem comm_conv {G : Type} [Monoid G] (E : G →₀ ℂ) (l : List (G →₀ ℂ))
    (h : ∀ x ∈ E.support, ∀ e ∈ l, ∀ y ∈ e.support, x * y = y * x) :
    (MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ G) * MonoidAlgebra.ofCoeff (conv l) =
      MonoidAlgebra.ofCoeff (conv l) * MonoidAlgebra.ofCoeff E := by
  induction l with
  | nil => rw [conv_nil, mul_one, one_mul]
  | cons e l ih =>
    have h1 : (MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ G) * MonoidAlgebra.ofCoeff e =
        MonoidAlgebra.ofCoeff e * MonoidAlgebra.ofCoeff E :=
      mul_comm_of_support _ _ fun x hx y hy => h x hx e List.mem_cons_self y hy
    rw [conv_cons, ← mul_assoc, h1, mul_assoc, ih fun x hx e' he' y hy => h x hx e' (List.mem_cons_of_mem _ he') y hy,
      mul_assoc]

section Trc
variable {D : D7} {V : HSp D}

theorem trc_eq_sum (e : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc e f = e.sum fun g a => a • rTrans g f := rfl

theorem trc_single (g : GA D V) (a : ℂ) (f : GA D V → ℂ) : trc (Finsupp.single g a) f = a • rTrans g f := by
  rw [trc_eq_sum, Finsupp.sum_single_index]
  exact zero_smul _ _

theorem trc_zero (f : GA D V → ℂ) : trc (0 : GA D V →₀ ℂ) f = 0 := by
  simp [trc]

theorem trc_add (e e' : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc (e + e') f = trc e f + trc e' f := by
  simp only [trc_eq_sum]
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

theorem trc_apply (e : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) : trc e f x = ∑ g ∈ e.support, e g * f (x * g) := by
  simp [trc, Finset.sum_apply, rTrans]

theorem trc_add_right (e : GA D V →₀ ℂ) (f f' : GA D V → ℂ) : trc e (f + f') = trc e f + trc e f' := by
  funext x
  simp only [trc_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem trc_zero_right (e : GA D V →₀ ℂ) : trc e (0 : GA D V → ℂ) = 0 := by
  funext x
  simp [trc_apply]

theorem trc_mul (e e' : GA D V →₀ ℂ) (f : GA D V → ℂ) :
    trc (MonoidAlgebra.ofCoeff e * MonoidAlgebra.ofCoeff e' : MonoidAlgebra ℂ (GA D V)).coeff f = trc e (trc e' f) := by
  induction e using Finsupp.induction_linear with
  | zero => rw [MonoidAlgebra.ofCoeff_zero, zero_mul, MonoidAlgebra.coeff_zero, trc_zero, trc_zero]
  | add x y hx hy =>
    rw [MonoidAlgebra.ofCoeff_add, add_mul, MonoidAlgebra.coeff_add, trc_add, trc_add, hx, hy]
  | single g a =>
    induction e' using Finsupp.induction_linear with
    | zero => rw [MonoidAlgebra.ofCoeff_zero, mul_zero, MonoidAlgebra.coeff_zero, trc_zero, trc_zero_right]
    | add x y hx hy =>
      rw [MonoidAlgebra.ofCoeff_add, mul_add, MonoidAlgebra.coeff_add, trc_add, hx, hy, trc_add, trc_add_right]
    | single h b =>
      rw [MonoidAlgebra.ofCoeff_single, MonoidAlgebra.ofCoeff_single, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.coeff_single, trc_single, trc_single, trc_single]
      funext x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem contAut_trc (e : GA D V →₀ ℂ) {f : GA D V → ℂ} (hf : IsContAut V f) : IsContAut V (trc e f) := by
  refine ⟨fun γ hγ x => ?_, ?_⟩
  · simp only [trc_apply, mul_assoc, hf.1 γ hγ]
  · have : trc e f = fun x => ∑ g ∈ e.support, e g * f (x * g) := funext (trc_apply e f)
    rw [this]
    exact continuous_finsetSum _ fun g _ => (GlobalTheory.Core.Mi.BotPin.isContAut_rTrans g hf).2.const_smul (e g)

end Trc

end GlobalTheory.QValOuter
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.VacAway

variable {D : D7}

def combL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring

theorem comb_single_one (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (y : WO S T) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single y 1) f = heisO ψ S T y f := by
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

theorem vac_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q₀ : QStep S) (c₁ : WO S.B.V S.J.W →₀ ℂ) (c₂ : WO S.J.W S.B'.V →₀ ℂ), IsFinComb c₁ → IsFinComb c₂ → Q₀.Away c₁ → Q₀.Away c₂ → ∀ f₁ f₂, IsThetaFunO ψ _ _ f₁ → IsThetaFunO ψ _ _ f₂ → Q₀.Vac f₁ f₂ → Q₀.Vac (comb ψ _ _ c₁ f₁) (comb ψ _ _ c₂ f₂) := by
  intro D ψ hψ σ S Q₀ c₁ c₂ hc₁ hc₂ ha₁ ha₂ f₁ f₂ _ _ hv
  obtain ⟨hee, hec, -⟩ := Q₀.q.split
  have hce : cA D Q₀.q.e * Q₀.q.e = 0 := by rw [mul_comm, hec]
  have hcc : cA D Q₀.q.e * cA D Q₀.q.e = cA D Q₀.q.e := by rw [← map_mul, hee]
  have hreal : cA D (Q₀.q.e + cA D Q₀.q.e) = Q₀.q.e + cA D Q₀.q.e := by
    rw [map_add (f := _), Formalism.L2.Theta.cA_cA, add_comm]
  have hidem : (Q₀.q.e + cA D Q₀.q.e) * (Q₀.q.e + cA D Q₀.q.e) = Q₀.q.e + cA D Q₀.q.e := by
    rw [add_mul, mul_add, mul_add, hee, hec, hce, hcc, add_zero, zero_add]
  have horth : (Q₀.q.e + cA D Q₀.q.e) * (1 - (Q₀.q.e + cA D Q₀.q.e)) = 0 := by
    rw [mul_sub, mul_one, hidem, sub_self]
  have comm : ∀ {A B : HSp D} (c : WO A B →₀ ℂ), Q₀.Away c → ∀ (f : WO A B → ℂ) (y : WO A B),
      IsHalf (Q₀.q.e + cA D Q₀.q.e) y → comb ψ A B c (heisO ψ A B y f) = heisO ψ A B y (comb ψ A B c f) := by
    intro A B c ha f y hy
    have h := (GlobalTheory.HeisComb.main D ψ A B).2.1 (Finsupp.single y 1) c (fun x hx u hu => by
      have hxy : x = y := Finset.mem_singleton.1 (Finsupp.support_single_subset hx)
      subst hxy
      exact GlobalTheory.HeisComb.symplO_half A B _ _ x u hreal horth hy (ha u hu)) f
    rw [comb_single_one, comb_single_one] at h
    exact h.symm
  obtain ⟨⟨T₁, O₁, hT₁, hO₁, rfl⟩, ⟨T₂, O₂, hT₂, hO₂, rfl⟩⟩ := hv
  refine ⟨⟨combL ψ _ _ c₁ ∘ₗ T₁, O₁, ?_, hO₁, rfl⟩, ⟨combL ψ _ _ c₂ ∘ₗ T₂, O₂, ?_, hO₂, rfl⟩⟩
  · exact (GlobalTheory.LocModU.localModel_uniq_transport_exist D Q₀.k (ofSplit Q₀.q) _ _ _ _ Q₀.F.G₀ Q₀.F.G₁ ψ hψ).2.1 T₁ hT₁
      (combL ψ _ _ c₁) (fun f hf => (GlobalTheory.HeisComb.main D ψ _ _).2.2.1 c₁ f hf hc₁ hψ)
      (fun f _ y hy => comm c₁ ha₁ f y hy)
  · exact (GlobalTheory.LocModU.localModel_uniq_transport_exist D Q₀.k (ofSplit Q₀.q) _ _ _ _ Q₀.F.G₁ Q₀.F.G₂ ψ hψ).2.1 T₂ hT₂
      (combL ψ _ _ c₂) (fun f hf => (GlobalTheory.HeisComb.main D ψ _ _).2.2.1 c₂ f hf hc₂ hψ)
      (fun f _ y hy => comm c₂ ha₂ f y hy)

end GlobalTheory.VacAway

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QPl.QStep

theorem gl₂_embX_eq_embA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (g : GL Q.n₂ Q.k), ∃ a₀ : GA D S.B'.A, GlobalTheory.MixPer.embA S.B'.d S.B'.o a₀ = Q.gl₂ (embX (Q.c + 1) g) ∧ (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g := by
  intro D ψ σ S Q g
  obtain ⟨a₀, ha⟩ := GlobalTheory.LocMod.Witness.exists_isLoc (ofSplit Q.q) Q.F.F₂ g
  exact ⟨a₀, GlobalTheory.LocGrp.isLoc_unique (ofSplit Q.q)
    (GlobalTheory.NormalFramePeriod.isLoc_embA (ofSplit Q.q) S.B' _ Q.F.F₂ Q.F.G₂ Q.F.bes' ha) (Q.loc₂ _), ha⟩

end GlobalTheory.QPl.QStep
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_heisenbergAction_line_modulation_translation : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ →
    ∃ ε : k, (ε = 1 ∨ ε = -1) ∧ ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (σ : ℕ) (B : BesLev D (σ + 1)) (B' : BesLev D σ) (W₀ : HSp D) (l : Link B B'.L B'.ζ) (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n) (γ : Frame p B'.A n'') (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ → IsStdChar D ψ (-1) → ∀ t : n → k,
      (∃ w₀ : WO W₀ B'.L,
        (∀ (L₁ : Lat B.V₀) (L₂ : Lat W₀) (f₁ : WO B.V₀ W₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (Ξ : WO B.V₀ W₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ fun y => (χ (ε * (t ⬝ᵥ y)) : ℂ) * a y) (heisO ψ B.V₀ W₀ ((B.o.resS W₀).symm (0, l.κ W₀ w₀)) Ξ)) ∧
        (∀ (L₂' : Lat W₀) (L₃ : Lat B'.V₀) (f₂ : WO W₀ B'.V₀ → ℂ) (Ψ₂ : Matrix n'' n k → ℂ) (b : (n → k) → ℂ) (Ξ : WO W₀ B'.V₀ → ℂ),
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ fun η => b (η - t)) (heisO ψ W₀ B'.V₀ ((B'.o.resT W₀).symm (0, -w₀)) Ξ))) ∧
      (∃ w₀ : WO W₀ B'.L,
        (∀ (L₁ : Lat B.V₀) (L₂ : Lat W₀) (f₁ : WO B.V₀ W₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (Ξ : WO B.V₀ W₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ fun y => a (y - t)) (heisO ψ B.V₀ W₀ ((B.o.resS W₀).symm (0, l.κ W₀ w₀)) Ξ)) ∧
        (∀ (L₂' : Lat W₀) (L₃ : Lat B'.V₀) (f₂ : WO W₀ B'.V₀ → ℂ) (Ψ₂ : Matrix n'' n k → ℂ) (b : (n → k) → ℂ) (Ξ : WO W₀ B'.V₀ → ℂ),
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ fun η => (χ (ε * (η ⬝ᵥ t)) : ℂ) * b η) (heisO ψ W₀ B'.V₀ ((B'.o.resT W₀).symm (0, -w₀)) Ξ))) := by
  first | exact @GlobalTheory.FinPl.LineAct.line_act | exact GlobalTheory.FinPl.LineAct.line_act | (intros; apply GlobalTheory.FinPl.LineAct.line_act <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

theorem _root_.GlobalTheory.T.carriesLatticeCompletion_iff_forall_place : ∀ {D : D7} (S : HSp D) (g : GA D S) (L : GlobalTheory.FinPl.Lat S), Submodule.IsLattice D.host.E L → ∀ (P : GlobalTheory.FinPl.Pl D → Prop), GlobalTheory.FinPl.Moves S g L L P ↔ ∀ v, P v → GlobalTheory.FinPl.Moves S g L L (· = v) := by
  first | exact @GlobalTheory.FinPlMovesLoc.moves_iff | exact GlobalTheory.FinPlMovesLoc.moves_iff | (intros; apply GlobalTheory.FinPlMovesLoc.moves_iff <;> assumption)
end
