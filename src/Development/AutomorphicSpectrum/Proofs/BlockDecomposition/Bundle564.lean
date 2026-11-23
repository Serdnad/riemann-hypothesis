module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.Bundle001
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle546
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle547
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle692
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle401
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle421
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle548
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEquivariantForm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveUnipotentOfRestriction
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.BaseChangeFrob

theorem cr_square_gen {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1}
    {h₃ : b₃.t = 1} {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I}
    {κ₄ : O →+* b₄.R ⧸ b₄.I} {Λ₁ Λ₂ Λ₃ Λ₄ : Type} [CommRing Λ₁] [CommRing Λ₂] [CommRing Λ₃] [CommRing Λ₄]
    {c₁ : Λ₁ →+* b₁.R} {c₂ : Λ₂ →+* b₂.R} {c₃ : Λ₃ →+* b₃.R} {c₄ : Λ₄ →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R}
    {τa : Λ₁ →+* Λ₂} {τb : Λ₂ →+* Λ₄} {τc : Λ₁ →+* Λ₃} {τd : Λ₃ →+* Λ₄}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τa a)) (hb : ∀ a, σb (c₂ a) = c₄ (τb a)) (hc : ∀ a, σc (c₁ a) = c₃ (τc a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τd a)) (hτ : ∀ a, τb (τa a) = τd (τc a)) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb τb hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τa ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τd hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc τc hc).pull j x) := by
  haveI i₁ : RingHomCompTriple τa τb (τb.comp τa) := ⟨rfl⟩
  haveI i₂ : RingHomCompTriple τc τd (τb.comp τa) := ⟨(RingHom.ext hτ).symm⟩
  rw [pull_pull (τb.comp τa), pull_pull (τb.comp τa)]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem w_frobenius (r : CrystallineSemistableComparison.Res l K) (w : WittVector l r.k) :
    ACris.phi (K := ℂ_[l]) (p := l) (r.w w) = r.w (WittVector.frobenius w) := by
  change ACris.phi (K := ℂ_[l]) (p := l) (algebraMap (Ainf l) (Acris l) (WittVector.map r.s w)) =
    algebraMap (Ainf l) (Acris l) (WittVector.map r.s (WittVector.frobenius w))
  rw [ACris.phi_algebraMap]
  congr 1
  change WittVector.frobenius (WittVector.map r.s w) = _
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.frobenius_eq_map_frobenius]
  ext n
  simp only [WittVector.map_coeff, frobenius_def, map_pow]

theorem wn_frob (r : CrystallineSemistableComparison.Res l K) (n : ℕ) (x : Wc.Wm l r.k n) :
    (base l).phi n (Mid.wn r n x) = Mid.wn r n (Wc.frob l r.k n x) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Wc.frob_mk', Mid.wn_mk, Mid.wn_mk, (base l).phi_cris, w_frobenius]

theorem phiM_bW {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n j : ℕ)
    (y : (HSW r M j).M n) : phiM r M n j (bW r M n j y) = bW r M n j ((Wc.phiS l (B.schFn M.p) r.ρ j).f n y) := by
  refine cr_square_gen (F₁ := B.schFn M.p) (F₂ := B.schFn M.p) (F₃ := B.schFn M.p) (F₄ := B.schFn M.p)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).phi n) rfl ((base l).dpP_phi n) (phiPtT _ n _) fun _ y r =>
        ((congrArg y.1.1 (B.phi_mk (base l) n r)).trans (map_pow y.1.1 _ l)).symm)
    (Wc.phiM l (B.schFn M.p) r.ρ n)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl)
    (Mid.wn_mk r n) ((base l).phi_cris n) (Wc.frob_mk' l r.k n) (Mid.wn_mk r n) (w_frobenius r) (wn_frob r n) ?_ j y
  intro B₀ y
  rfl

end GlobalTheory.CompanionTheory.BaseChangeFrob
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrisBase

theorem cr_square_coeff {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1} {h₃ : b₃.t = 1}
    {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I} {κ₄ : O →+* b₄.R ⧸ b₄.I}
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c₁ : Λ →+* b₁.R} {c₂ : Λ' →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ' →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τ : Λ →+* Λ'}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τ a)) (hb : ∀ a, σb (c₂ a) = c₄ (RingHom.id Λ' a)) (hc : ∀ a, σc (c₁ a) = c₃ (RingHom.id Λ a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τ a)) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb (RingHom.id Λ') hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τ ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τ hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc (RingHom.id Λ) hc).pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

theorem pullM_bW {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {M N : Model l K}
    (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ) (y : (HSW r N j).M n) :
    pullM r u hu n j (bW r N n j y) = bW r M n j ((Wc.pullS l r.ρ (B.schMap u hu) j).f n y) := by
  exact cr_square_coeff
    (B.crMor (F := B.schFn N.p) (F' := B.schFn N.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl)
    (B.crMor (F := B.schFn N.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism ((B.schMap u hu).ptK _) fun _ _ _ => rfl)
    (Wc.pullM l r.ρ (B.schMap u hu) n)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl)
    (Mid.wn_mk r n) (fun _ => rfl) (Wc.idc _) (Mid.wn_mk r n) (fun _ => rfl) (fun _ _ => rfl) j y

end GlobalTheory.CompanionTheory.CrisBase
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.CrisBaseChange

theorem cr_square_coeff {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1} {h₃ : b₃.t = 1}
    {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I} {κ₄ : O →+* b₄.R ⧸ b₄.I}
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c₁ : Λ →+* b₁.R} {c₂ : Λ' →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ' →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τ : Λ →+* Λ'}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τ a)) (hb : ∀ a, σb (c₂ a) = c₄ (RingHom.id Λ' a)) (hc : ∀ a, σc (c₁ a) = c₃ (RingHom.id Λ a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τ a)) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb (RingHom.id Λ') hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τ ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τ hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc (RingHom.id Λ) hc).pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem red_wn (r : CrystallineSemistableComparison.Res l K) (n : ℕ) (x : Wc.Wm l r.k (n + 1)) :
    (base l).red (Nat.le_succ n) (Mid.wn r (n + 1) x) = Mid.wn r n (Wc.red l r.k n x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Mid.wn_mk, B.red_cris, Wc.red_mk, Mid.wn_mk]
  rfl

theorem bW_red (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M (n + 1)) :
    (redT r M (Nat.le_succ n)).pull j (bW r M (n + 1) j y) = bW r M n j ((HSW r M j).r n y) :=
  cr_square_coeff (τ := r.w)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k (n + 1)) (b' := B.bs l true (n + 1)) (ht := rfl) (ht' := rfl)
      (Mid.wn r (n + 1)) rfl (dp_wn r (n + 1)) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r (n + 1)) (Mid.im_le r (n + 1))) rfl) fun _ _ _ => rfl)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true (n + 1)) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).red (Nat.le_succ n)) rfl (B.dd_red true _ (Nat.le_succ n)) (B.basePt _ _ (red_κm r (Nat.le_succ n))) fun _ _ _ => rfl)
    (Wc.redM l (B.schFn M.p) r.ρ n)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl)
    (Mid.wn_mk r (n + 1)) (B.red_cris _ (Nat.le_succ n)) (Wc.red_mk l r.k n)
    (Mid.wn_mk r n) (red_wn r n) (fun _ _ => rfl) j y

end GlobalTheory.CompanionTheory.CrisBaseChange
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.gram_map_continuous_hermitian : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (ρ : D.what₂.Tau), Continuous (fun y : Mx D V.rank r => (inner V y y : Mx D r r)) ∧ ∀ y : Mx D V.rank r, (inner V y y : Mx D r r) ∈ hermA D r ∧ compAt θ ρ (inner V y y : Mx D r r) = (compAt θ ρ y).conjTranspose * gramAt D V ρ * compAt θ ρ y := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram.inner_facts | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram.inner_facts | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram.inner_facts <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eisenstein_covariance : PositivityTheory.GramSchwartzFunctions.EC.Covar := by
  first | exact @GlobalTheory.CompanionTheory.EisCovar.covar | exact GlobalTheory.CompanionTheory.EisCovar.covar | (intros; apply GlobalTheory.CompanionTheory.EisCovar.covar <;> assumption)
end

section

noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.KerZeroPf

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

theorem main : PositivityTheory.RgBcC.KerZero := by
  intro n _ _ μ _ E κ hκ hr hf y hy
  refine GlobalTheory.CompanionTheory.KerUniq.main n μ E κ (GLs n) GlobalTheory.CompanionTheory.KerUniq.isOpen_GLs subset_rfl ?_ hκ hr ?_ y hy
  · intro y hy k₂
    have hk : (k₂.1).det ≠ 0 := by
      have h : k₂.1 * star k₂.1 = 1 := (Matrix.mem_unitaryGroup_iff).1 k₂.2
      intro h0
      have h1 := congrArg Matrix.det h
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
      exact zero_ne_one h1
    show (y * k₂.1).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hy hk
  · intro f hfE hc _
    have h := hf f hfE hc
    simpa [act] using h

end GlobalTheory.CompanionTheory.KerZeroPf
end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.PosNormFD

theorem posNorm : PositivityTheory.Rg.BcB.SpectralAccumulation.FD.PosNorm := by
  intro E _ _ _ N _ _ μ _ 𝓕 h𝓕 φ hA hS hne
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  have hc : Continuous φ.1 := GlobalTheory.CuspRep.IsAutForm.continuous hA
  have hl := GlobalTheory.DiscreteUnit.left_latticeGL hA hS
  by_contra h0
  have h0' : ∫⁻ g in 𝓕, ‖φ.1 g‖ₑ ^ 2 ∂μ = 0 := by simpa using h0
  have hm : Measurable fun g => ‖φ.1 g‖ₑ ^ 2 := hc.enorm.measurable.pow_const 2
  have hz := (lintegral_eq_zero_iff hm).1 h0'
  have hSo : IsOpen {g | φ.1 g ≠ 0} := isOpen_ne_fun hc continuous_const
  have hSF : μ ({g | φ.1 g ≠ 0} ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply hSo.measurableSet]
    refine measure_mono_null (fun g hg => ?_) (ae_iff.1 hz)
    have hg' : φ.1 g ≠ 0 := hg
    simpa [hg'] using hg'
  have hinv : ∀ γ : latticeGL E N, γ • {g | φ.1 g ≠ 0} = {g | φ.1 g ≠ 0} := fun γ => by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have e : φ.1 (γ⁻¹ • x) = φ.1 x := hl _ (γ⁻¹).2 x
    simp only [Set.mem_setOf_eq, e]
  set_option synthInstance.maxHeartbeats 200000 in
    have hS0 := h𝓕.measure_zero_of_invariant _ hinv hSF
  have hemp := (hSo.measure_eq_zero_iff μ).1 hS0
  refine hne (Subtype.ext (funext fun g => ?_))
  by_contra hg
  exact (Set.eq_empty_iff_forall_notMem.1 hemp g) hg

end GlobalTheory.CompanionTheory.PosNormFD
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.TotalTrace

theorem eq_zero_of_exp_mul_eq_one {c : ℂ} (h : ∀ t : ℝ, Complex.exp (c * t) = 1) : c = 0 := by
  have h0 : HasDerivAt (fun v : ℝ => c * (v : ℂ)) c 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul c
  have h1 := h0.cexp
  have h2 : (fun t : ℝ => Complex.exp (c * t)) = fun _ => 1 := funext h
  rw [h2] at h1
  have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
  simpa using h3

theorem total_trace_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} {m : (E →+* ℂ) → Multiset ℂ} (hV : IsDiscrete V)
    (hm : ∀ τ, HasInfCharGL V τ (m τ)) : ∑ τ, (m τ).sum = 0 := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.ne_bot
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hφ0 (Subtype.ext (funext hcon))
  have hlie : lie E N (oneL E N) φ = (∑ τ, (m τ).sum) • φ := by
    rw [GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop, LinearMap.sum_apply, Finset.sum_smul]
    exact Finset.sum_congr rfl fun τ _ => GlobalTheory.CompanionTheory.CentEig.trace_Eop_eq_of_hasInfCharGL (hm τ) φ hφ
  refine eq_zero_of_exp_mul_eq_one fun t => ?_
  have h1 := GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre E N φ _ hlie t g
  rw [(hV.sqInt φ hφ).1 t g] at h1
  have h2 : Complex.exp ((∑ τ, (m τ).sum) * t) * φ.1 g = 1 * φ.1 g := by rw [one_mul]; exact h1.symm
  exact mul_right_cancel₀ hg h2

theorem twBound : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.TwBound := by
  intro E _ _ _ N
  refine ⟨0, fun V m hV hm => ?_⟩
  rw [total_trace_eq_zero hV hm, norm_zero]

end GlobalTheory.CompanionTheory.TotalTrace

end
end

section

noncomputable section

open NumberField
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.TreeNode

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mulChi_absC_mulChi (n : ℕ) (z z' : ℂ) (φ : Sm E n) :
    mulChi n (Model.absC E z) (mulChi n (Model.absC E z') φ) = mulChi n (Model.absC E (z' + z)) φ := by
  refine Subtype.ext (funext fun g => ?_)
  rw [mulChi_apply, mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val,
    ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem tw_tw {n : ℕ} (V : Submodule ℂ (Sm E n)) (a b : ℂ) : tw (tw V a) b = tw V (a + b) := by
  ext ψ
  constructor
  · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    exact ⟨φ, hφ, (mulChi_absC_mulChi n b a φ).symm⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨_, ⟨φ, hφ, rfl⟩, mulChi_absC_mulChi n b a φ⟩

theorem map_mem_finVec {n : ℕ} {V : Submodule ℂ (Sm E n)} (f : Sm E n →ₗ[ℂ] Sm E n)
    (heq : ∀ o, ∀ φ ∈ V, f (act o φ) = act o (f φ)) {φ : Sm E n} (hφ : φ ∈ V)
    (hfin : φ ∈ finVec (cptRep E n)) : f φ ∈ finVec (cptRep E n) := by
  have h : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E n k φ)) := hfin
  change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E n k (f φ)))
  refine Submodule.finiteDimensional_of_le
    (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E n k φ)).map f) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, heq (.cpt k) φ hφ⟩

theorem nodeEmb : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.NodeEmb := by
  rintro E _ _ _ r s V V₁ V₂ z₁ z₂ hV ⟨f, hf, hinj, heq⟩
  refine ⟨f, fun φ hφ => Submodule.subset_span ⟨?_, ?_⟩, hinj, heq⟩
  · have e₁ : tw (tw V₁ (z₁ - (s : ℂ) / 2)) ((s : ℂ) / 2) = tw V₁ z₁ := by
      rw [tw_tw, sub_add_cancel]
    have e₂ : tw (tw V₂ (z₂ + (r : ℂ) / 2)) (-(r : ℂ) / 2) = tw V₂ z₂ := by
      rw [tw_tw, neg_div, add_neg_cancel_right]
    change MemInd2 (tw (tw V₁ (z₁ - (s : ℂ) / 2)) ((s : ℂ) / 2)) (tw (tw V₂ (z₂ + (r : ℂ) / 2)) (-(r : ℂ) / 2)) (f φ)
    rw [e₁, e₂]
    exact hf φ hφ
  · exact map_mem_finVec f heq hφ (hV.aut φ hφ).kfin

end GlobalTheory.CompanionTheory.TreeNode

end
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.unitary_jacquet_eigenvector_exists : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V), IsUnramInv ϖ σ q → IsAdmissible ρ → ∀ y : V, y ∉ jacU ρ → (∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ρ k y - y ∈ jacU ρ) → ∃ (y' : V) (ξ : GU σ n → ℂ), y' ∉ jacU ρ ∧ (∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ρ t y' - ξ t • y' ∈ jacU ρ) ∧ ∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ξ k = 1 := by
  first | exact @GlobalTheory.CompanionTheory.EigTorus.eigU_complete | exact GlobalTheory.CompanionTheory.EigTorus.eigU_complete | (intros; apply GlobalTheory.CompanionTheory.EigTorus.eigU_complete <;> assumption)
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.unitary_equivariant_form : PositivityTheory.SphericalProduct.EqFormU := by
  first | exact @GlobalTheory.CompanionTheory.EqForm.eqFormU | exact GlobalTheory.CompanionTheory.EqForm.eqFormU | (intros; apply GlobalTheory.CompanionTheory.EqForm.eqFormU <;> assumption)
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.injective_unipotent_of_restriction : PositivityTheory.RgBcC.RealD.InjRL → PositivityTheory.RgBcC.RealD.InjUU := by
  first | exact @GlobalTheory.CompanionTheory.LvChain.injUU_of_injRL | exact GlobalTheory.CompanionTheory.LvChain.injUU_of_injRL | (intros; apply GlobalTheory.CompanionTheory.LvChain.injUU_of_injRL <;> assumption)
end
