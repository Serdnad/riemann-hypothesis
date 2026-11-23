module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle528
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle545
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle546
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle544
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitOfRetract
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle555
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierTransformMatrixSpaceInvolution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinHalfAsm

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

theorem cptPart_le' {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) : cptPart T ≤ T := by
  unfold GlobalTheory.BCT.cptPart
  exact (Subgroup.closure_le _).mpr fun t ht => ht.1

theorem mass_inf_twCent {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (Γ : Subgroup G) (δ : G) :
    mass θ (Γ ⊓ twCent θ δ) δ = mass θ Γ δ := by
  have h1 : (Γ ⊓ GlobalTheory.BCT.twCent θ δ).subgroupOf (GlobalTheory.BCT.twCent θ δ) = Γ.subgroupOf (GlobalTheory.BCT.twCent θ δ) :=
    Subgroup.inf_subgroupOf_right _ _
  have h2 : Γ ⊓ GlobalTheory.BCT.twCent θ δ ⊓ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)
      = Γ ⊓ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ) := by
    rw [inf_assoc, inf_eq_right.mpr (cptPart_le' _)]
  unfold GlobalTheory.BCT.mass
  rw [h1, h2]

theorem index_rStab_orbit {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K U : Subgroup G)
    (f : G → ℂ) (δ : G) (hK : IsCompact (K : Set G)) (hU : IsOpen (U : Set G))
    (hf : ∀ u ∈ U, ∀ y, f (u⁻¹ * y * θ u) = f y) (x : G) :
    (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hopen : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hU.preimage continuous_subtype_val
  have hle : U.subgroupOf K ≤ GlobalTheory.BCT.rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k)) := by
    intro k' hk'
    rw [Subgroup.mem_subgroupOf] at hk'
    change ∀ y : K, f ((x * ↑(y * k'))⁻¹ * δ * θ (x * ↑(y * k'))) = f ((x * ↑y)⁻¹ * δ * θ (x * ↑y))
    intro y
    rw [← hf (k' : G) hk' ((x * ↑y)⁻¹ * δ * θ (x * ↑y))]
    congr 1
    simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  haveI : (U.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI := Subgroup.finiteIndex_of_le hle
  exact Subgroup.FiniteIndex.index_ne_zero

theorem range_pair (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) :
    ((ratF E a).prodMap (ratF E b)).range = (ratF E a).range.prod (ratF E b).range := by
  exact MonoidHom.range_prodMap _ _

theorem finHalfOf : FinHalfOf := by
  unfold PositivityTheory.Rg.BcB.G8.Fin.FinHalfOf PositivityTheory.Rg.BcB.G8.Fin.DcCount PositivityTheory.Rg.BcB.G8.Fin.MassProd
    PositivityTheory.Rg.BcB.G8.Fin.RatFin PositivityTheory.Rg.BcB.G8.Fin.SuppFin PositivityTheory.Rg.BcB.G8.Fin.EulerFin
    PositivityTheory.Rg.BcB.G8.KfOC PositivityTheory.Rg.BcB.G8.FinLevel PositivityTheory.Rg.BcB.G8.FinHalf
  intro hDc hMP hRat hSupp hEuler hKf hFL E _ _ _ hUnr a b S hS φ₁ φ₂ hT1 hT2 δ₁ δ₂ h1 h2
  obtain ⟨hGood, hfin1, hfin2, hfin3⟩ := hRat E hUnr a b δ₁ δ₂ h1 h2
  obtain ⟨hsupp, hsuppG⟩ := hSupp E hUnr a b S hS φ₁ φ₂ hT1 hT2 δ₁ δ₂ h1 h2
  obtain ⟨U, hUo, hUinv⟩ := hFL E hUnr a b S φ₁ φ₂ hT1 hT2
  have hKo : IsOpen (((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b) :
      Subgroup (PositivityTheory.Rg.BcB.G8.Gf E a b)) : Set (PositivityTheory.Rg.BcB.G8.Gf E a b)) := by
    rw [Subgroup.coe_prod]
    exact (hKf E a).1.prod (hKf E b).1
  have hKc : IsCompact (((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b) :
      Subgroup (PositivityTheory.Rg.BcB.G8.Gf E a b)) : Set (PositivityTheory.Rg.BcB.G8.Gf E a b)) := by
    rw [Subgroup.coe_prod]
    exact (hKf E a).2.prod (hKf E b).2
  have hdc := hDc (PositivityTheory.Rg.BcB.G8.Gf E a b) (PositivityTheory.Rg.BcB.G8.thP E a b)
    ((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b)) (PositivityTheory.Rg.BcB.G8.gam δ₁ δ₂)
    ((GlobalTheory.BCT.ratF E a) δ₁, (GlobalTheory.BCT.ratF E b) δ₂) (PositivityTheory.Rg.BcB.G8.finFn S φ₁ φ₂)
    hKo hKc hGood inf_le_right hfin1 hfin2 hfin3
    (fun x0 => index_rStab_orbit _ _ U _ _ hKc hUo hUinv (x0 : PositivityTheory.Rg.BcB.G8.Gf E a b)) hsupp
  have hdc' : PositivityTheory.Rg.BcB.G8.dcSum (PositivityTheory.Rg.BcB.G8.gam δ₁ δ₂)
      ((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b)) (PositivityTheory.Rg.BcB.G8.orbFn S φ₁ φ₂ δ₁ δ₂) = _ := hdc
  have hmass : GlobalTheory.BCT.mass (PositivityTheory.Rg.BcB.G8.thP E a b) (PositivityTheory.Rg.BcB.G8.gam δ₁ δ₂)
      ((GlobalTheory.BCT.ratF E a) δ₁, (GlobalTheory.BCT.ratF E b) δ₂) =
      GlobalTheory.BCT.mass (GlobalTheory.BCT.thF E a) (GlobalTheory.BCT.ratF E a).range ((GlobalTheory.BCT.ratF E a) δ₁) *
        GlobalTheory.BCT.mass (GlobalTheory.BCT.thF E b) (GlobalTheory.BCT.ratF E b).range ((GlobalTheory.BCT.ratF E b) δ₂) := by
    unfold PositivityTheory.Rg.BcB.G8.gam
    rw [mass_inf_twCent, range_pair]
    exact hMP _ _ (GlobalTheory.BCT.thF E a) (GlobalTheory.BCT.thF E b) _ _ _ _
  refine ⟨hsuppG, hfin1, ?_⟩
  rw [hdc', hmass, hEuler E hUnr a b S hS φ₁ φ₂ hT1 hT2 δ₁ δ₂ h1 h2]

end GlobalTheory.CompanionTheory.FinHalfAsm

end
end

section

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.AdelicU PositivityTheory.Rg.Rsw.L

namespace GlobalTheory.CompanionTheory.UnitCell

theorem artinian_fields {ι : Type} [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, IsArtinianRing (A i)]
    {R : Type} [CommRing R] (c : ∀ i, R →+* A i) :
    ∃ (m : ℕ) (Ω : Fin m → Type) (_ : ∀ k, Field (Ω k)) (φ : ∀ k, R →+* Ω k),
      (∀ x, (∀ i, c i x = 1) → ∀ k, φ k x = 1) ∧
      ∀ z, (∀ k, φ k z ≠ 0) ↔ ∀ i, IsUnit (c i z) := by
  obtain ⟨m, ⟨q⟩⟩ := Finite.exists_equiv_fin (Σ i, MaximalSpectrum (A i))
  have hmax : ∀ k : Fin m, (q.symm k).2.asIdeal.IsMaximal := fun k => (q.symm k).2.isMaximal
  refine ⟨m, fun k => A (q.symm k).1 ⧸ (q.symm k).2.asIdeal, fun k => Ideal.Quotient.field _,
    fun k => (Ideal.Quotient.mk _).comp (c (q.symm k).1), fun x hx k => ?_, fun z => ⟨fun hz i => ?_, fun hz k h => ?_⟩⟩
  · simp [hx]
  · by_contra hu
    obtain ⟨M, hM, hzM⟩ := exists_max_ideal_of_mem_nonunits hu
    obtain ⟨k, hk⟩ : ∃ k, q.symm k = ⟨i, ⟨M, hM⟩⟩ := ⟨q _, q.symm_apply_apply _⟩
    refine hz k (Ideal.Quotient.eq_zero_iff_mem.2 ?_)
    rw [hk]
    exact hzM
  · have hk := hmax k
    have h' : c (q.symm k).1 z ∈ (q.symm k).2.asIdeal := Ideal.Quotient.eq_zero_iff_mem.1 h
    exact hk.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (hz _))

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def sc {R : Type} [CommRing R] (r : Rˣ) : GL (Fin 1) R := Units.map (Matrix.scalar (Fin 1)).toMonoidHom r

theorem sc_apply {R : Type} [CommRing R] (r : Rˣ) : (sc r).1 0 0 = r := by simp [sc]

theorem exists_adele (S : Finset (HeightOneSpectrum (𝓞 F))) (b : ∀ v : HeightOneSpectrum (𝓞 F), (Fv F v ⊗[F] E)ˣ)
    (hb : ∀ v ∉ S, b v = 1) (c : ∀ w : InfinitePlace F, (w.Completion ⊗[F] E)ˣ) :
    ∃ x : AF F ⊗[F] E, (∀ v, compFin F E v x = b v) ∧ ∀ w, compInf F E w x = c w := by
  obtain ⟨a, ha, hc⟩ := GlobalTheory.AdelicU.Frames.exists_GL_of_components S (fun v => sc (b v))
    (fun v hv => by rw [hb v hv]; exact map_one _) (fun w => sc (c w))
  refine ⟨a.1 0 0, fun v => ?_, fun w => ?_⟩
  · have h := congrArg (fun g : GL (Fin 1) (Fv F v ⊗[F] E) => g.1 0 0) (ha v)
    exact h.trans (sc_apply _)
  · have h := congrArg (fun g : GL (Fin 1) (w.Completion ⊗[F] E) => g.1 0 0) (hc w)
    exact h.trans (sc_apply _)


variable (F E) in
def LocR (S : Finset (HeightOneSpectrum (𝓞 F))) : InfinitePlace F ⊕ S → Type
  | .inl w => w.Completion ⊗[F] E
  | .inr v => Fv F v.1 ⊗[F] E

instance locRing (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ c, CommRing (LocR F E S c)
  | .inl w => inferInstanceAs (CommRing (w.Completion ⊗[F] E))
  | .inr v => inferInstanceAs (CommRing (Fv F v.1 ⊗[F] E))


variable (F E) in
def locC (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ c, AF F ⊗[F] E →+* LocR F E S c
  | .inl w => compInf F E w
  | .inr v => compFin F E v.1

instance locArt (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ c, IsArtinianRing (LocR F E S c) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rintro (w | v)
  · exact IsArtinianRing.of_finite w.Completion (w.Completion ⊗[F] E)
  · exact IsArtinianRing.of_finite (Fv F v.1) (Fv F v.1 ⊗[F] E)


open Classical in
theorem crit (S : Finset (HeightOneSpectrum (𝓞 F))) (e : AF F ⊗[F] E) (h1 : ∀ w, compInf F E w e = 1)
    (h2 : ∀ v, compFin F E v e = if v ∈ S then 1 else 0) :
    ∃ (m : ℕ) (Ω : Fin m → Type) (_ : ∀ i, Field (Ω i)) (φ : ∀ i, AF F ⊗[F] E →+* Ω i), (∀ i, φ i e = 1) ∧
      ∀ z : AF F ⊗[F] E, IsUnit (1 - e + e * z) ↔ ∀ i, φ i z ≠ 0 := by
  obtain ⟨m, Ω, fld, φ, hφ, hu⟩ := artinian_fields (LocR F E S) (locC F E S)
  have he : ∀ k, φ k e = 1 := hφ e (by
    rintro (w | ⟨v, hv⟩)
    · exact h1 w
    · exact (h2 v).trans (if_pos hv))
  refine ⟨m, Ω, fld, φ, he, fun z => ⟨fun h k => ?_, fun h => ?_⟩⟩
  · have h' := h.map (φ k)
    rw [map_add (f := _), map_sub, map_mul, map_one, he, sub_self, zero_add, one_mul] at h'
    exact h'.ne_zero
  · have hz := (hu z).1 h
    have hI : ∀ w, IsUnit (compInf F E w z) := fun w => hz (.inl w)
    have hS : ∀ v (h : v ∈ S), IsUnit (compFin F E v z) := fun v h => hz (.inr ⟨v, h⟩)
    obtain ⟨x, hxf, hxi⟩ := exists_adele (E := E) S
      (fun v => if h : v ∈ S then (hS v h).unit⁻¹ else 1) (fun v hv => dif_neg hv) (fun w => (hI w).unit⁻¹)
    refine isUnit_iff_exists_inv.2 ⟨x, GlobalTheory.AdelicU.Supp.adTens_eq_one' (fun w => ?_) fun v => ?_⟩
    · rw [map_mul, map_add (f := _), map_sub, map_mul, map_one, h1, hxi, sub_self, zero_add, one_mul]
      exact (hI w).mul_val_inv
    · rw [map_mul, map_add (f := _), map_sub, map_mul, map_one, h2, hxf]
      by_cases hv : v ∈ S
      · simp only [if_pos hv, dif_pos hv, sub_self, zero_add, one_mul]
        exact (hS v hv).mul_val_inv
      · simp [if_neg hv, dif_neg hv]

end Glue

theorem unitCrit : PositivityTheory.Rg.Rsw.L.IdemEx → PositivityTheory.Rg.Rsw.Cell.UnitCrit := fun _ D S e he =>
  crit S e he.1 (by convert he.2 using 4)

end GlobalTheory.CompanionTheory.UnitCell

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellTop

open GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

theorem mem_cell_iff {e : AE D} (hee : e * e = e) (g : G D p) : g ∈ cell e ↔ InCell e g :=
  isUnit_mix_iff hee (cB g)

theorem continuous_cB : Continuous (cB : G D p → Mx D p p) := by
  have hm : Continuous (mat : G D p → Mx D (p + p) (p + p)) := Units.continuous_val.comp continuous_subtype_val
  exact continuous_matrix fun i j => hm.matrix_elem _ _

theorem continuous_dB : Continuous (dB : G D p → Mx D p p) := by
  have hm : Continuous (mat : G D p → Mx D (p + p) (p + p)) := Units.continuous_val.comp continuous_subtype_val
  exact continuous_matrix fun i j => hm.matrix_elem _ _

theorem cell_eq {e : AE D} (hee : e * e = e) :
    cell e = (fun g : G D p => (cB g).det) ⁻¹' {z : AE D | IsUnit (1 - e + e * z)} := by
  ext g
  change IsUnit _ ↔ IsUnit _
  rw [det_mix_one hee]


open Classical in
def tau (e : AE D) (g : G D p) : hermS D p e := if h : ∃ x, IsB e g x then h.choose else 0

theorem isB_tau {e : AE D} {g : G D p} (h : ∃ x, IsB e g x) : IsB e g (tau e g) := by
  rw [tau, dite_eq_left h]
  exact h.choose_spec

theorem tau_eq {e : AE D} {g : G D p} {x : hermS D p e} (h : IsB e g x) : tau e g = x :=
  isB_unique (isB_tau ⟨x, h⟩) h

theorem tau_formula {e : AE D} (hee : e * e = e) {g : G D p} {x : hermS D p e} (hu : g ∈ cell e) (h : IsB e g x) :
    Ring.inverse (1 - e + e * (cB g).det) • (((1 - e) • (1 : Mx D p p) + e • cB g).adjugate * (e • dB g)) = x.1.1 := by
  have hu' : IsUnit (1 - e + e * (cB g).det) := by
    have := hu
    rw [cell_eq hee] at this
    exact this
  exact mix_solve hee hu' x.2 h.2

theorem continuousOn_tau {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (hee : e * e = e) (hce : cA D e = e) :
    ContinuousOn (tau e : G D p → hermS D p e) (cell e) := by
  have : IsTopologicalRing (AE D) := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hd : Continuous fun g : G D p => (cB g).det := continuous_cB.matrix_det
  have h1 : ContinuousOn (fun g : G D p => Ring.inverse (1 - e + e * (cB g).det)) (cell e) := by
    refine (unit_AE he).2.comp hd.continuousOn ?_
    intro g hg
    rw [cell_eq hee] at hg
    exact hg
  have h2 : Continuous fun g : G D p => ((1 - e) • (1 : Mx D p p) + e • cB g).adjugate * (e • dB g) := by
    refine Continuous.matrix_mul (Continuous.matrix_adjugate ?_) (continuous_dB.const_smul e)
    exact continuous_const.add (continuous_cB.const_smul e)
  have h3 : ContinuousOn (fun g : G D p => ((tau e g).1.1 : Mx D p p)) (cell e) := by
    refine (h1.smul h2.continuousOn).congr fun g hg => ?_
    have hB : IsB e g (tau e g) := isB_tau (exists_isB hee hce ((mem_cell_iff hee g).1 hg))
    exact (tau_formula hee hg hB).symm
  have i1 : Topology.IsInducing (Subtype.val : hermS D p e → hermA D p) := Topology.IsInducing.subtypeVal
  have i2 : Topology.IsInducing (Subtype.val : hermA D p → Mx D p p) := Topology.IsInducing.subtypeVal
  exact (i2.comp i1).continuousOn_iff.2 h3

theorem cellAlg : IdemEx → CellAlg := by
  intro hI D p nb hnb w hw S e he
  obtain ⟨hee, hce⟩ := (hI D S).2 e he
  have hex : ∀ g ∈ cell (p := p) e, IsB e g (tau e g) := fun g hg =>
    isB_tau (exists_isB hee hce ((mem_cell_iff hee g).1 hg))
  have hcell : ∀ {g : G D p} {x : hermS D p e}, IsB e g x → g ∈ cell e := fun h => (mem_cell_iff hee _).2 h.1
  refine ⟨tau e, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, continuousOn_tau he hee hce, (continuous_nb hnb).comp continuous_subtype_val,
      fun x y => isNMap_add hnb x.1 y.1⟩
    · rw [cell_eq hee]
      exact (unit_AE he).1.preimage (continuous_cB.matrix_det (R := AE D))
    · intro q hq x hx
      have h := (LeftCell.isB_left hq (tau e x)).2 (hex x hx)
      exact ⟨hcell h, (tau_eq h)⟩
    · intro y x hx
      have h := (isB_mul_nb hnb y (tau e x)).2 (hex x hx)
      exact ⟨hcell h, tau_eq h⟩
  · intro g hg u hu
    exact hcell ((isB_mul_right_iff he hu (tau e g)).2 (hex g hg))
  · intro g hg
    have h := hex g hg
    change (e • cB g) * _ = _
    rw [smul_mul_assoc]
    have h2 : cB g * (tau e g).1.1 = e • dB g := h.2
    rw [h2, smul_smul, hee]

end GlobalTheory.CompanionTheory.CellTop
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CompanionTheory.SiegelEis

theorem rpow_le_add_rpow {A u c d : ℝ} (hA : 0 < A) (hc : c ≤ u) (hd : u ≤ d) :
    A ^ u ≤ A ^ c + A ^ d := by
  rcases le_total 1 A with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h hd
    have := Real.rpow_nonneg hA.le c
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hA h hc
    have := Real.rpow_nonneg hA.le d
    linarith

theorem differentiable_cpow_term {A : ℝ} (hA : 0 < A) (s₁ w : ℂ) :
    Differentiable ℂ (fun s : ℂ => (A : ℂ) ^ (s - s₁) * w) := by
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  exact ((differentiable_id.sub_const s₁).const_cpow (Or.inl hA')).mul_const w

theorem eis_half_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ Ê : ℂ → G2 σ Y → ℂ, ∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧ ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re} := by
  intro F E _ _ _ _ _ σ B n Y r s' hB hn hY b K a hb hK hH χ s₁ f hf
  have hKc := GlobalTheory.T.isCompact_standard_maximal F E σ B n Y r s' hB hn hY b K a hb hK hH
  obtain ⟨-, hpos⟩ := GlobalTheory.T.height_function_continuous_pos' F E σ B n Y r s' hB hn hY b K a hb hK hH
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.flat_section_growth_bound K a hKc hH hpos χ s₁ f hf
  obtain ⟨σ₀, hσ₀⟩ := GlobalTheory.T.eisenstein_series_convergent F E σ B n Y r s' hB hn hY b K a hb hK hH
  have hC : ∀ s x, ‖flat a f s₁ s x‖ ≤ max C₀ 0 * a x ^ (s.re + (n : ℝ) / 2) := fun s x =>
    (hC₀ s x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (hpos x).le _))
  have hsum : ∀ σ' : ℝ, σ₀ < σ' → ∀ x, Summable fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ' := by
    intro σ' h x
    obtain ⟨C', N, h'⟩ := hσ₀ σ' h
    exact (h' x).1
  refine ⟨fun s x => ∑' q, eisTerm (flat a f s₁ s) x q, σ₀ - (n : ℝ) / 2, ?_, ?_⟩
  · intro s hs x
    apply Summable.hasSum
    have hg := (hsum (s.re + (n : ℝ) / 2) (by linarith) x).mul_left (max C₀ 0)
    first
      | exact Summable.of_norm_bounded _ hg (fun q => hC s _)
      | exact Summable.of_norm_bounded hg (fun q => hC s _)
  · intro x s₀ hs₀
    have hs₀' : σ₀ - (n : ℝ) / 2 < s₀.re := hs₀
    set c := (σ₀ - (n : ℝ) / 2 + s₀.re) / 2 with hc
    set d := s₀.re + 1 with hd
    have hU : IsOpen {s : ℂ | c < s.re ∧ s.re < d} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
    have hmem : {s : ℂ | c < s.re ∧ s.re < d} ∈ 𝓝 s₀ :=
      hU.mem_nhds ⟨by linarith, by linarith⟩
    have hg : Summable fun q : Cos σ Y => max C₀ 0 * (a ((Quotient.out q).1 * x) ^ (c + (n : ℝ) / 2) +
        a ((Quotient.out q).1 * x) ^ (d + (n : ℝ) / 2)) :=
      ((hsum _ (by linarith) x).add (hsum _ (by linarith) x)).mul_left (max C₀ 0)
    have hD : DifferentiableOn ℂ (fun s => ∑' q, eisTerm (flat a f s₁ s) x q) {s : ℂ | c < s.re ∧ s.re < d} := by
      refine Complex.differentiableOn_tsum_of_summable_norm (F := fun q s => eisTerm (flat a f s₁ s) x q) hg
        (fun q => ?_) hU (fun q s hs => ?_)
      · exact (differentiable_cpow_term (hpos _) s₁ (f ((Quotient.out q).1 * x))).differentiableOn
      · refine (hC s _).trans (mul_le_mul_of_nonneg_left (rpow_le_add_rpow (hpos _) ?_ ?_) (le_max_right _ _))
        · linarith [hs.1]
        · linarith [hs.2]
    exact (hD.differentiableAt hmem).differentiableWithinAt

end GlobalTheory.CompanionTheory.SiegelEis
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG

theorem intertwiner_eq_zero_of_highest {n : ℕ} (H V : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [AddCommGroup V] [Module ℂ V]
    (G : Fin n → Fin n → Module.End ℂ H) (D : Fin n → Fin n → Module.End ℂ V)
    (hrel : Formalism.REAL.GlRel G)
    (hadj : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (R : H →ₗ[ℂ] V) (hR : ∀ a b w, R (G a b w) = D a b (R w))
    (hhigh : ∀ (μ : Fin n → ℝ) (v : H), Formalism.REAL.KHighest (fun _ => true) G μ v → R v = 0) :
    R = 0 := by
  by_contra hne
  have hKtop : LinearMap.ker R ≠ ⊤ := fun h => hne (LinearMap.ker_eq_top.mp h)
  have hN : (LinearMap.ker R)ᗮ ≠ ⊥ := fun h =>
    hKtop ((Submodule.orthogonal_eq_bot_iff).mp h)
  have hstable : ∀ a b, ∀ w ∈ (LinearMap.ker R)ᗮ, G a b w ∈ (LinearMap.ker R)ᗮ := by
    intro a b w hw
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hu' : G b a u ∈ LinearMap.ker R := by
      rw [LinearMap.mem_ker] at hu ⊢
      rw [hR, hu, map_zero]
    rw [← hadj]
    exact (Submodule.mem_orthogonal _ _).mp hw _ hu'
  obtain ⟨μ, v, hvN, hv0, hk⟩ := GlobalTheory.T.exists_highest_weight_in_invariant_submodule H G hrel hadj _ hN hstable
  have hvK : v ∈ LinearMap.ker R := hhigh μ v hk
  exact hv0 (inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp hvN v hvK))

end GlobalTheory.CompanionTheory.RealCountG
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.fourier_transform_matrix_space_involution : ∀ (m n : ℕ) (C s : ℂ) (k : ℝ), C ≠ 0 → k ≠ 0 → ‖s‖ = 2 * |k| → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, (fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u) ⇑φ))))) 0 = c * ∫ v : Fin m → Fin n → ℂ, φ v := by
  first | exact @GlobalTheory.CompanionTheory.Kloc.Fresnel.value_at_zero | exact GlobalTheory.CompanionTheory.Kloc.Fresnel.value_at_zero | (intros; apply GlobalTheory.CompanionTheory.Kloc.Fresnel.value_at_zero <;> assumption)
end
