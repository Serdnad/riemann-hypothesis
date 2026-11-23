module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle353
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle349
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle327
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle407
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle411
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBase
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChartQuot

open GlobalTheory.FinPl GlobalTheory.FinPlLoc ValuativeRel

variable {D : D7}

theorem chrEq_div {a c : (AE D)ˣ →* Circle} {α γ : Formalism.L2.Host.HChar D.host.E} (ha : ChrEq a α) (hc : ChrEq c γ) :
    ChrEq (a * c⁻¹) (α * γ⁻¹) := by
  refine ⟨⟨ha.1.1.mul hc.1.1.inv, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ha.1.2, hc.1.2, inv_one, one_mul]
  · show ((a x * (c x)⁻¹ : Circle) : ℂ) = ((α.locK P k * (γ.locK P k)⁻¹ : ℂˣ) : ℂ)
    rw [Circle.coe_mul, Circle.coe_inv, ha.2 P e he k x hx, hc.2 P e he k x hx,
      Units.val_mul, Units.val_inv_eq_inv_val]

theorem quot_triv {a c : (AE D)ˣ →* Circle} {α γ ξ : Formalism.L2.Host.HChar D.host.E} (ha : ChrEq a (α * ξ)) (hc : ChrEq c (γ * ξ))
    (hα : α.TrivOn D.host.F) (hγ : γ.TrivOn D.host.F) (b : (AF D.host.F)ˣ) : (a * c⁻¹) (idF D b) = 1 := by
  have h := chrEq_div ha hc
  rw [_root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel_right] at h
  exact GlobalTheory.GridWeil.triv_base h (hα.mul hγ.inv) b

theorem eq_of_finM {V : HSp D} {n : ℕ} (hn : V.rank = n) {g g' : GA D V} (hg : g ∈ GfC V) (hg' : g' ∈ GfC V)
    (h : finM V hn g = finM V hn g') : g = g' := by
  subst hn
  have e0 : ∀ g : GA D V, finM V rfl g = (Formalism.L2.Theta.mt V g).map (toEAf D) := fun g => by simp [finM]
  rw [e0, e0] at h
  apply mt_inj
  ext i j
  have h1 : infPart D (Formalism.L2.Theta.mt V g i j) = infPart D (Formalism.L2.Theta.mt V g' i j) := by
    have a : infHom V g = infHom V g' := (show infHom V g = 1 from hg).trans (show infHom V g' = 1 from hg').symm
    exact congrArg (fun z : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => z.1 i j) a
  have h2 : finPart D (Formalism.L2.Theta.mt V g i j) = finPart D (Formalism.L2.Theta.mt V g' i j) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective (congrFun (congrFun h i) j)
  rw [← sub_eq_zero]
  apply eq_zero_of_comp
  · rw [RingHom.map_sub, h1, sub_self]
  · intro w
    rw [RingHom.map_sub]
    unfold GlobalTheory.FinPl.compAt
    rw [RingHom.comp_apply, RingHom.comp_apply, h2, sub_self]

section Pt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem sum_parts : infPart D (p.e + cA D p.e) = 0 ∧
    ∀ w, compAt D w (p.e + cA D p.e) = if w = p.v then 1 else 0 := by
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, he⟩ := p.above
  rw [he]
  change infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 ∧
    ∀ w, compAt D w (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = _
  refine ⟨infPart_pair _ _, fun w => ?_⟩
  rw [compAt_pair]
  split_ifs with hw
  · rw [hw, h1]; rfl
  · rw [h0 w hw, TensorProduct.zero_tmul]

theorem idele_off {R : Type} [CommRing R] (φ : AE D →+* R) (h : φ (p.e + cA D p.e) = 0) (a : kˣ) :
    φ (p.idele a : AE D) = 1 ∧ φ (cA D (p.idele a : AE D)) = 1 := by
  have e1 := p.split.1
  have e2 := p.split.2.1
  have e3 : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, e1]
  have f1 : φ p.e = 0 := by
    have : p.e = p.e * (p.e + cA D p.e) := by rw [mul_add, e1, e2, add_zero]
    rw [this, map_mul, h, mul_zero]
  have f2 : φ (cA D p.e) = 0 := by
    rw [map_add (f := _), f1, zero_add] at h; exact h
  have s : p.sec a = p.e * p.sec a := by rw [← p.sec_pr, p.pr_sec]
  rw [p.idele_val, s]
  simp only [map_add (f := _), map_sub, map_mul, map_one, f1, f2]
  simp

theorem idele_on {R : Type} [CommRing R] (φ : AE D →+* R) (h : φ (p.e + cA D p.e) = 1) (a : kˣ) (δ : AE D)
    (hδ : cA D δ * δ = 1) (ha : p.pr δ = a) :
    φ (p.idele a : AE D) = φ δ * φ (cA D (p.idele a : AE D)) := by
  have s : p.sec a = p.e * δ := by rw [← ha, p.sec_pr]
  rw [p.idele_val, s]
  have h2 := congrArg φ hδ
  simp only [map_add (f := _), map_sub, map_mul, map_one] at h h2 ⊢
  linear_combination (φ δ - 1) * h - φ (cA D p.e) * h2

end Pt

theorem det_sub_one_mem {V : HSp D} {I : Ideal (AE D)} {h : GA D V} (hh : h ∈ congGrp V I) :
    (Formalism.L2.Theta.mt V h).det - 1 ∈ I := by
  rw [mem_congGrp] at hh
  rw [← Ideal.Quotient.eq, map_one, RingHom.map_det]
  have : (Ideal.Quotient.mk I).mapMatrix (Formalism.L2.Theta.mt V h) = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq]
    exact hh i j
  rw [this, map_one, Matrix.det_one]



theorem isDetRoot_prod {ι : Type} [Fintype ι] {k : ι → Type} [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (p : ∀ i, SplitPt D (k i))
    (hp : Function.Injective fun i => (p i).v) {V : HSp D} {h : GA D V} (hh : h ∈ grpAt V fun w => ∃ i, (p i).v = w)
    (d : ∀ i, (k i)ˣ) (hd : ∀ i, (p i).pr (Formalism.L2.Theta.mt V h).det = d i) :
    IsDetRoot V h (∏ i, (p i).idele (d i)) := by
  have hδ := det_sub_one_mem hh
  have hn := Formalism.L2.Theta.det_conj_mul V h
  show _ = (Formalism.L2.Theta.mt V h).det * cA D _
  have off : ∀ {R : Type} [CommRing R] (φ : AE D →+* R), (∀ i, φ ((p i).e + cA D (p i).e) = 0) →
      φ ((Formalism.L2.Theta.mt V h).det - 1) = 0 →
      φ (((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D) - (Formalism.L2.Theta.mt V h).det * cA D ((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D)) = 0 := by
    intro R _ φ h1 h2
    rw [map_sub, map_one, sub_eq_zero] at h2
    rw [Units.coe_prod, map_sub, map_mul, map_prod, map_prod, map_prod, h2,
      Finset.prod_eq_one fun i _ => (idele_off (p i) φ (h1 i) (d i)).1,
      Finset.prod_eq_one fun i _ => (idele_off (p i) φ (h1 i) (d i)).2, mul_one, sub_self]
  have on : ∀ {R : Type} [CommRing R] (φ : AE D →+* R) (i : ι), (∀ j, j ≠ i → φ ((p j).e + cA D (p j).e) = 0) →
      φ ((p i).e + cA D (p i).e) = 1 →
      φ (((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D) - (Formalism.L2.Theta.mt V h).det * cA D ((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D)) = 0 := by
    intro R _ φ i o h1
    rw [Units.coe_prod, map_sub, map_mul, map_prod, map_prod, map_prod,
      Finset.prod_eq_single i (fun j _ hj => (idele_off (p j) _ (o j hj) (d j)).1) (fun h => absurd (Finset.mem_univ i) h),
      Finset.prod_eq_single i (fun j _ hj => (idele_off (p j) _ (o j hj) (d j)).2) (fun h => absurd (Finset.mem_univ i) h), sub_eq_zero]
    exact idele_on (p i) _ h1 _ _ hn (hd i)
  rw [← sub_eq_zero]
  apply eq_zero_of_comp
  · exact off (infPart D) (fun i => (sum_parts (p i)).1) (infPart_of_idAt hδ)
  · intro w
    by_cases hw : ∃ i, (p i).v = w
    · obtain ⟨i, rfl⟩ := hw
      refine on (compAt D (p i).v) i (fun j hj => ?_) ?_
      · rw [(sum_parts (p j)).2, if_neg fun e => hj (hp e).symm]
      · rw [(sum_parts (p i)).2, if_pos rfl]
    · refine off (compAt D w) (fun i => ?_) (compAt_of_idAt hδ hw)
      rw [(sum_parts (p i)).2, if_neg fun e => hw ⟨i, e.symm⟩]

theorem exists_unit_det {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (g : GL (Y ⊕ Fin 0) k)
    (hg : g ∈ GlobalTheory.SplitWeil.KO k (Y ⊕ Fin 0)) :
    ∃ d : kˣ, valuation k (d : k) = 1 ∧ (F.β * g.val.toBlocks₁₁ * F.γ).det = d := by
  refine ⟨Matrix.GeneralLinearGroup.det g, ?_, ?_⟩
  · obtain ⟨g₀, rfl⟩ := hg
    have e : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀) : kˣ) : k) =
        algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det g₀ : 𝒪[k]ˣ) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
      rfl
    rw [e]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
  · rw [Matrix.det_conj_of_mul_eq_one F.βγ F.γβ, Matrix.GeneralLinearGroup.val_det_apply,
      ← Matrix.det_submatrix_equiv_self (Equiv.sumEmpty Y (Fin 0)).symm]
    rfl

theorem chr_eq_of_root {χ : (AE D)ˣ →* Circle} (hF : ∀ a, χ (idF D a) = 1) {V : HSp D} {g : GA D V} {x x' : (AE D)ˣ}
    (h : IsDetRoot V g x) (h' : IsDetRoot V g x') : χ x = χ x' := by
  obtain ⟨a, ha⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 g _ _ h h'
  rw [ha, map_mul, hF, mul_one]

theorem chr_eq_of_root_mul {χ : (AE D)ˣ →* Circle} (hF : ∀ a, χ (idF D a) = 1) {V : HSp D} {g h : GA D V} {x y z : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hy : IsDetRoot V h y) (h1 : χ y = 1) (hz : IsDetRoot V (g * h) z) : χ z = χ x := by
  rw [chr_eq_of_root hF hz ((GlobalTheory.Member.isDetRoot_laws D V).2.2.2 _ _ _ _ hx hy), map_mul, h1, mul_one]

theorem eq_on_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    {c c' : (AE D)ˣ →* Circle} {η η' δ : kˣ →* ℂˣ} (h : (ofSplit p).IsComp c⁻¹ (η * δ)) (h' : (ofSplit p).IsComp c'⁻¹ (η' * δ))
    (hη : GlobalTheory.SplitWeil.IsUnram η) (hη' : GlobalTheory.SplitWeil.IsUnram η') (d : kˣ) (hd : valuation k (d : k) = 1) :
    c (p.idele d) = c' (p.idele d) := by
  have e : (p.idele d : AE D) = (ofSplit p).ι d + (1 - (ofSplit p).e) := by
    rw [p.idele_val, add_comm]; rfl
  have a := h d _ e
  have a' := h' d _ e
  rw [MonoidHom.mul_apply, hη d hd] at a
  rw [MonoidHom.mul_apply, hη' d hd, a] at a'
  have := Circle.ext a'
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply] at this
  exact inv_injective this

theorem det_cast (n n' : ℕ) (e : n = n') (h : GA D (D.sp.X n')) :
    (Formalism.L2.Theta.mt _ (e ▸ h : GA D (D.sp.X n))).det = (Formalism.L2.Theta.mt _ h).det := by
  subst e; rfl


end GlobalTheory.ChartQuot
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel Filter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw.GeoInhab
open GlobalTheory.FinPl (SplitPt latV idAt intAt Lat Pl)
open Formalism.L2.NTheta (IsIdemAt)
open _root_.Formalism.L2.Col (IntAt qOf)
open GlobalTheory.SymBridge (IsOrd zPos xPos IsCompl)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsUnif)

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem int_dense {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) :
    (∀ a, (ofSplit q).pr a ∈ 𝒪[k] ↔ IntAt PP a) ∧ DenseRange (ofSplit q).pr := by
  obtain ⟨k₀, _, _, _, _, q₀, he, -, hi, hd⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP q.e h
  have pe : ∀ x, q.pr (q.e * x) = q.pr x := fun x => by rw [← q.sec_pr, q.pr_sec]
  refine ⟨fun a => ?_, ?_⟩
  · rw [← hi, q.int_iff, q₀.int_iff]
    change finPart D (q.sec (q.pr _)) ∈ _ ↔ finPart D (q₀.sec (q₀.pr _)) ∈ _
    rw [q.sec_pr, q₀.sec_pr, he]
  · have hs : Function.Surjective (fun x => q.pr (q₀.sec x)) := fun y =>
      ⟨q₀.pr (q.sec y), by simp only [q₀.sec_pr, he, pe, q.pr_sec]⟩
    have := hs.denseRange.comp hd (q.cont_pr.comp q₀.cont_sec)
    convert this using 1
    funext a
    change q.pr _ = q.pr (q₀.sec (q₀.pr _))
    rw [q₀.sec_pr, he, pe]

theorem xi_unit (hu : q.UnitAA) : valuation k (ofSplit q).xi = 1 := by
  have he := (DblInhab.sec_mem_intAt q 1).2 (map_one _).le
  obtain ⟨h1, h2⟩ := hu.1 _ he
  have h3 := DblInhab.pr_le_one q h1
  have h4 := DblInhab.pr_le_one q h2
  rw [map_mul, q.pr_sec, mul_one] at h3 h4
  change valuation k ((q.pr.comp (incA D)) _) ≤ 1 at h4
  rw [map_inv₀, map_inv₀] at h4
  exact le_antisymm h3 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (Witness.xi_ne (ofSplit q))))).1 h4)

theorem exists_char (hu : q.UnitAA) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ ψk, (ofSplit q).IsChar ψ ψk ∧ HasConductor ψk 1 := by
  obtain ⟨⟨ψk, hk⟩, -⟩ := GlobalTheory.LocChar.weil_char_split D k (ofSplit q) ψ hψ
  have hx := Witness.xi_ne (ofSplit q)
  have hv := xi_unit q hu
  have h1 : q.IsChar ψ (ψk.mulShift (ofSplit q).xi⁻¹) := fun a => by
    rw [AddChar.mulShift_apply, hk]
    change psiE ψ (incA D D.host.xi0 * q.sec _) = _
    rw [mul_comm (incA D _), ← DblInhab.sec_mul_pr]
    change psiE ψ (q.sec (_ * (ofSplit q).xi)) = _
    rw [mul_comm, mul_inv_cancel_left₀ hx]
  have h2 := GlobalTheory.SplitCharCond.hasConductor_one D k q ψ _ hψ h1 hu
  refine ⟨ψk, hk, fun x => (Iff.trans ⟨fun h y hy => ?_, fun h y hy => ?_⟩ (h2 x))⟩
  · exact h _ (by simpa [hv] using hy)
  · have := h ((ofSplit q).xi * y) (by simpa [hv] using hy)
    rwa [AddChar.mulShift_apply, inv_mul_cancel_left₀ hx] at this

end Place

section Rat
variable {D : D7}

variable {n : Type} [Fintype n] [DecidableEq n]

end Rat

variable {D : D7}

section Loc
open GlobalTheory.Fam Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.MainNotions

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Links.RealDat D A Ks) (P : Formalism.L2.DIV.LevelP R.Pg D.R.r ℂ) (u : D.what₂.Word)
  {a : XGeo D} {y : YRat a} (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf R u (mkGeo m b)))
  {PP : Formalism.L2.DIV.Pl D.host.E} (l : LocX a R.βX PP)


end Loc

end GlobalTheory.QTw.GeoInhab
end
end

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

theorem _root_.GlobalTheory.T.nrm2_twisted_eq_untwisted_mul_prod_zinv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (f₀ : WO S T → ℂ) (m : Measure (WO S T)) (X : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) m X → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (r t j t' : ℕ) (hr : r ≤ S.rank), S.rank + t' = T.rank → ∀ (Pg Q : Finset (Pl D.host.E)), Disjoint Pg Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f f' : WO S T → ℂ), IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (Lev.datY S.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B) χj Q ξ f₀ f → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (Lev.datY S.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) χj ∅ ξ' f₀ f' → nrm2 m X f = nrm2 m X f' * ∏ PP ∈ Q, (zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹) := by
  first | exact @GlobalTheory.TwistNorm.chainStep_twisted_normSq_eq_untwisted_mul_localFactors | exact GlobalTheory.TwistNorm.chainStep_twisted_normSq_eq_untwisted_mul_localFactors | (intros; apply GlobalTheory.TwistNorm.chainStep_twisted_normSq_eq_untwisted_mul_localFactors <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem moves_emb0_iff_moves_of_monoAt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (M : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (γ : GA D S₀), MonoAt d L M v → (Moves S (d.emb0 γ) L L (· = v) ↔ Moves S₀ γ M M (· = v)) := by
  intro D S S₀ ρ d L M v γ hL
  have supp : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → AE D), (∀ i, y i ∈ idAt D (· = v)) →
      ∀ i, (A *ᵥ y) i ∈ idAt D (· = v) := fun A y hy i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hy k)
  have hc : ∀ {n : ℕ} (x : Matrix (Fin S.rank) (Fin n) (AE D)) (i : Fin n), colMul x i 0 = 0 := fun x i => by
    funext k; simp [colMul]
  have j0iff : ∀ w : Fin S₀.rank → AE D, d.j0 *ᵥ w ∈ latV S L (· = v) ↔ w ∈ latV S₀ M (· = v) := by
    intro w
    rw [hL]
    simp only [Matrix.mulVec_mulVec, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.zero_mulVec, Matrix.one_mulVec, Pi.zero_apply, hc,
      zero_mem, implies_true, true_and]
  constructor
  · intro h w hw
    have h1 := h (d.j0 *ᵥ w) (supp _ _ hw)
    rw [j0iff, Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec, j0iff] at h1
    exact h1
  · intro h y hy
    rw [hL y, hL (mt S (d.emb0 γ) *ᵥ y)]
    simp only [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding, d.wittDecomp_projY_anisotropicEmbedding, d.wittDecomp_projAnisotropic_anisotropicEmbedding]
    rw [← Matrix.mulVec_mulVec, ← h _ (supp _ _ hy)]

end GlobalTheory.Core.Mi.LatMatch
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Core.Rk.SumSplit

theorem orthAt_sumLatO : ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B) (LA : Lat A) (LB : Lat B) (v : Pl D),
    OrthAt o (GlobalTheory.Core.Rk.SumBox.sumLatO o LA LB) LA LB v := by
  intro D S A B o LA LB v y
  constructor
  · intro hy
    refine ⟨GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qA (fun x hx => ?_) _ hy,
      GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qB (fun x hx => ?_) _ hy⟩
    · obtain ⟨x₁, hx₁, x₂, -, rfl⟩ := (GlobalTheory.Core.Rk.SumBox.mem_sumLatO o LA LB x).1 hx
      rw [GlobalTheory.Core.Rk.SumBox.qA_split]; exact hx₁
    · obtain ⟨x₁, -, x₂, hx₂, rfl⟩ := (GlobalTheory.Core.Rk.SumBox.mem_sumLatO o LA LB x).1 hx
      rw [GlobalTheory.Core.Rk.SumBox.qB_split]; exact hx₂
  · rintro ⟨hA, hB⟩
    have e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) := by
      have hs : o.jA * o.pA + o.jB * o.pB = 1 := by
        change (o.iA.map (incA D)) * (o.qA.map (incA D)) + (o.iB.map (incA D)) * (o.qB.map (incA D)) = 1
        rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add (incA D)),
          o.iA_qA_add, Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hs, Matrix.one_mulVec]
    rw [e]
    exact add_mem
      (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iA
        (fun x hx => GlobalTheory.Core.Rk.SumBox.iA_mem_sumLatO o LB hx) _ hA)
      (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iB
        (fun x hx => GlobalTheory.Core.Rk.SumBox.iB_mem_sumLatO o LA hx) _ hB)

end GlobalTheory.Core.Rk.SumSplit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

theorem _root_.GlobalTheory.T.sliceAlongLine_datum_over_vacuum_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), a ≠ 0 → ∀ (LA : Lat A) (LS : Lat S), IsSelfDualC A LA → IsSelfDualC S LS → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ a) Ξ → ∀ y : WO L S, ∃ g, Over ψ α β LA LS g Ψ (fun u => Ξ ((o.resS S).symm (u, y))) := by
  first | exact @GlobalTheory.LastSrcSlice.main | exact GlobalTheory.LastSrcSlice.main | (intros; apply GlobalTheory.LastSrcSlice.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

theorem mulVec_sec_split {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {n : ℕ} (g : Matrix (Fin n) (Fin n) (AE D)) (w : Fin n → k) :
    g *ᵥ (fun i => q.sec (w i)) = fun i => q.sec ((g.map q.pr *ᵥ w) i) := by
  funext i

  simp only [mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := GlobalTheory.LocMod.PinEx.sec_mul q (q.pr (g i j)) (w j)
  have h2 := q.sec_pr (g i j)
  have h3 : q.e * q.sec (w j) = q.sec (w j) := by
    have := q.sec_pr (q.sec (w j))
    rw [q.pr_sec] at this
    exact this.symm
  rw [← h1, h2, mul_assoc, mul_left_comm, h3]

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch


end GlobalTheory.Core.Mi.LatMatch
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel

theorem _root_.GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∃ lS lT : kˣ →* ℂˣ, (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT p.v → IsUnram lS) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS p.v → IsUnram lT) ∧ ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ) (f : WO S T → ℂ), Over ψ α β LS LT f₀ Ψ f → (∀ (g : GL n' k) (h : GL n k), Over ψ α β LS LT f₀ (fun x => (lS (Matrix.GeneralLinearGroup.det g) : ℂ) * (lT (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ ((h⁻¹ : GL n k).val * x * g.val)) (om (α.gl g, β.gl h) f)) ∧ (∀ g ∈ grpOff S (· = p.v), ∀ h ∈ grpOff T (· = p.v), Over ψ α β LS LT (om (g, h) f₀) Ψ (om (g, h) f)) ∧ ∀ (c : ℂ) (Ψ' : Matrix n n' k → ℂ) (f' : WO S T → ℂ), Over ψ α β LS LT f₀ Ψ' f' → Over ψ α β LS LT f₀ (c • Ψ + Ψ') (c • f + f') := by
  first | exact @GlobalTheory.SplitLinAt.linModelAt | exact GlobalTheory.SplitLinAt.linModelAt | (intros; apply GlobalTheory.SplitLinAt.linModelAt <;> assumption)
end
