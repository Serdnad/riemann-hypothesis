module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
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
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.FlatUnitPf

theorem idAt_mul_idOff {D : D7} (P : Pl D → Prop) (a b : AE D) (ha : a ∈ idAt D P) (hb : b ∈ idOff D P) : a * b = 0 := by
  have h1 : a * b ∈ idAt D P := Ideal.mul_mem_right _ _ ha
  have h2 : a * b ∈ idOff D P := Ideal.mul_mem_left _ _ hb
  rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at h1
  rw [idOff, Ideal.mem_iInf] at h2
  obtain ⟨hinf, hfin⟩ := h1
  rw [RingHom.mem_ker] at hinf
  apply GlobalTheory.LatVac.eq_zero_of_parts
  · exact hinf
  · apply GlobalTheory.SelfDualAt.eq_zero_of_compFin
    intro w
    by_cases hw : P w
    · have := h2 ⟨w, hw⟩
      rw [RingHom.mem_ker] at this
      exact this
    · have := hfin ⟨w, hw⟩
      rw [RingHom.mem_ker] at this
      exact this

end GlobalTheory.FinPl.FlatUnitPf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua : ∀ (D : D7) (P : Pl D → Prop), (∃ ε : AE D, ε * ε = ε ∧ cA D ε = ε ∧ ε ∈ intAt D P ∧ (∀ a, a ∈ idAt D P ↔ ε * a = a) ∧ (∀ a, a ∈ idOff D P ↔ ε * a = 0)) ∧ ∀ S : HSp D, (∀ h : GA D S, ∃ x ∈ grpAt S P, ∃ y ∈ grpOff S P, h = x * y) ∧ (∀ x ∈ grpAt S P, ∀ y ∈ grpOff S P, x * y = y * x) ∧ grpAt S P ⊓ grpOff S P = ⊥ ∧ (∀ (L : Lat S) (y : Fin S.rank → AE D), (Submodule.IsLattice D.host.E L) → (y ∈ latV S L P ↔ (∀ i, y i ∈ idAt D P) ∧ ∀ v, P v → ∀ e ∈ intAt D (· = v), e • y ∈ latV S L (· = v))) := by
  first | exact @GlobalTheory.FinPl.localComponents | exact GlobalTheory.FinPl.localComponents | (intros; apply GlobalTheory.FinPl.localComponents <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.besselDoubleStep_linear_in_secondDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ) (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ) (c : ℂ), hand0 s₁ s₂ l vL φ Ξ₁ (c • Ξ₂) = c • hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ := by
  first | exact @GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel | exact GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel | (intros; apply GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_supportedSubgroup_of_suppAt_splitPlace_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V), SuppAt q.e V g → ∀ P : GlobalTheory.FinPl.Pl D → Prop, P q.v → g ∈ GlobalTheory.FinPl.grpAt V P := by
  first | exact @GlobalTheory.SuppGrp.mem_grpAt_of_suppAt | exact GlobalTheory.SuppGrp.mem_grpAt_of_suppAt | (intros; apply GlobalTheory.SuppGrp.mem_grpAt_of_suppAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.FinPl

section Mix

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mix_mul_decompAt (e : A) (hee : e * e = e) (a b : Matrix n n A) :
    (e • a + (1 - e) • (1 : Matrix n n A)) * (e • b + (1 - e) • 1) = e • (a * b) + (1 - e) • 1 := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, hee, h1, h2, h3, zero_smul, add_zero, zero_add, mul_one, one_mul]

theorem cT_mix_decompAt (s : A →+* A) (e : A) (hs : s e = e) (a : Matrix n n A) :
    Formalism.UG.cT s (e • a + (1 - e) • (1 : Matrix n n A)) = e • Formalism.UG.cT s a + (1 - e) • 1 := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, map_add, map_mul, map_sub, map_one, hs]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem mix_mem_decompAt (s : A →+* A) (J : Matrix n n A) (e : A) (hee : e * e = e) (hs : s e = e) (g : GL n A)
    (hg : g ∈ Formalism.UG.UJ s J) :
    ∃ g' ∈ Formalism.UG.UJ s J, (g' : Matrix n n A) = e • (g : Matrix n n A) + (1 - e) • 1 := by
  refine ⟨⟨e • (g : Matrix n n A) + (1 - e) • 1, e • ((g⁻¹ : GL n A) : Matrix n n A) + (1 - e) • 1, ?_, ?_⟩, ?_, rfl⟩
  · rw [mix_mul_decompAt e hee, Units.mul_inv, ← add_smul, add_sub_cancel, one_smul]
  · rw [mix_mul_decompAt e hee, Units.inv_mul, ← add_smul, add_sub_cancel, one_smul]
  · have hg' : Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
    show Formalism.UG.cT s (e • (g : Matrix n n A) + (1 - e) • 1) * J * (e • (g : Matrix n n A) + (1 - e) • 1) = J
    have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
    have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
    have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
    rw [cT_mix_decompAt s e hs]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, one_mul, mul_one] at hg' ⊢
    rw [hg', hee, h1, h2, h3, zero_smul, zero_smul, add_zero, zero_add, ← add_smul, add_sub_cancel, one_smul]

theorem map_mk_decompAt (I : Ideal A) (g : GL n A) (hg : ∀ i j, ((g : Matrix n n A) - 1) i j ∈ I) :
    Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g = 1 := by
  ext i j
  have key : (1 : Matrix n n (A ⧸ I)) i j = Ideal.Quotient.mk I ((1 : Matrix n n A) i j) := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one]
  rw [key]
  exact Ideal.Quotient.eq.mpr (by simpa [Matrix.sub_apply] using hg i j)

end Mix

theorem sigR_algebraMap_decompAt {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]



theorem decompAt : ∀ (D : D7) (S : HSp D) (h : GA D S) (v : Pl D), ∃ hv ∈ grpAt S (· = v), ∃ h' ∈ grpOff S (· = v),
    h = hv * h' := by
  intro D S h v
  obtain ⟨ε, α, hε, hv1, hv0⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
  obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D v ε α hε
  have hea : algebraMap (AF D.host.F) (AE D) ε = ε ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  set e : AE D := algebraMap (AF D.host.F) (AE D) ε with he_def
  have c1 : compAt D v e = 1 := by rw [hc, hv1]; rfl
  have c0 : ∀ w, w ≠ v → compAt D w e = 0 := fun w hw => by rw [hc, hv0 w hw, TensorProduct.zero_tmul]
  have heAt : e ∈ idAt D (· = v) := (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ e).2 ⟨h0, fun w hw => c0 w hw⟩
  have hee : e * e = e := (mem_supportedAtPlace_iff_placeIdempotent_mul D v e h0 c1 c0 e).1 heAt
  have heOff : 1 - e ∈ idOff D (· = v) := by
    refine (Submodule.mem_iInf _).2 fun w => ?_
    rcases w with ⟨w, hw⟩
    change w = v at hw
    subst hw
    rw [RingHom.mem_ker, RingHom.map_sub, RingHom.map_one, c1, sub_self]
  have hee' : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, hee, sub_self, sub_zero]
  have hσ : ∀ σ' : D.host.E →ₐ[D.host.F] D.host.E, sigR (AF D.host.F) σ' e = e := by
    intro σ'
    exact sigR_algebraMap_decompAt (AF D.host.F) σ' ε
  have hσ' : ∀ σ' : D.host.E →ₐ[D.host.F] D.host.E, sigR (AF D.host.F) σ' (1 - e) = 1 - e := by
    intro σ'; rw [map_sub, map_one, hσ]
  have hmem : h.1 ∈ Formalism.UG.UJ (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram) := h.2
  obtain ⟨g₁, hg₁, hg₁v⟩ := mix_mem_decompAt (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram) e hee
    (hσ _) h.1 hmem
  obtain ⟨g₂, hg₂, hg₂v⟩ := mix_mem_decompAt (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram) (1 - e)
    hee' (hσ' _) h.1 hmem
  have hcong : ∀ (I : Ideal (AE D)) (g : GA D S), (∀ i j, (mt S g - 1) i j ∈ I) → g ∈ congGrp S I := by
    intro I g hg
    rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact map_mk_decompAt I _ hg
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  refine ⟨⟨g₁, hg₁⟩, hcong _ _ ?_, ⟨g₂, hg₂⟩, hcong _ _ ?_, ?_⟩
  · intro i j
    show (g₁.val - 1) i j ∈ _
    have : e • h.1.val + (1 - e) • 1 - 1 = e • (h.1.val - 1) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hg₁v, this, Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ heAt
  · intro i j
    show (g₂.val - 1) i j ∈ _
    have : (1 - e) • h.1.val + (1 - (1 - e)) • 1 - 1 =
        (1 - e) • (h.1.val - 1) := by
      rw [smul_sub, sub_smul (1 : AE D) (1 - e), one_smul]; abel
    rw [hg₂v, this, Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ heOff
  · apply Subtype.ext
    apply Units.ext
    show h.1.val = g₁.val * g₂.val
    rw [hg₁v, hg₂v, sub_sub_cancel]
    simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, hee, hee', h1, h2, zero_smul, zero_add,
      add_zero]
    rw [add_comm, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.FinPl
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.homLattice_placeCut_smul_mem_openSubgroup : ∀ (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∀ u ∈ latO S T LS LT P, ∃ s : Finset (Pl D), ∀ γ ∈ intAf D.host.F, (∀ v ∈ s, evalV D.host.F v γ = 0) → pairA D.host.F 0 γ • u ∈ U := by
  first | exact @GlobalTheory.LatLevel.smul_mem_open_of_vanish | exact GlobalTheory.LatLevel.smul_mem_open_of_vanish | (intros; apply GlobalTheory.LatLevel.smul_mem_open_of_vanish <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.lattices_agree_almost_everywhere : ∀ (D : D7) (S : HSp D) (L M : Lat S), Submodule.IsFullLattice D.host.E L → Submodule.IsFullLattice D.host.E M → ∃ T : Finset (Pl D), ∀ v, v ∉ T → latV S L (· = v) = latV S M (· = v) := by
  intro D S L M hL hM
  first
  | exact GlobalTheory.FinPl.latV_eq_off_finite D S L M hL hM
  | exact GlobalTheory.FinPl.latV_eq_off_finite D S L M hL hM.toIsLattice
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.diagonalAdelic_entries_congr_one_of_ratios_at_place : ∀ (D : D7) (ρ : ℕ) (v : Pl D) (t : GL (Fin ρ) (AE D)), (∀ i j, i ≠ j → t.1 i j = 0) → (∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v)) → (∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i * (t⁻¹).1 j j - 1 ∈ intAt D (· = v)) → (∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v)) → ∀ i, t.1 i i - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.DiagInt.diag_int | exact GlobalTheory.FinPl.DiagInt.diag_int | (intros; apply GlobalTheory.FinPl.DiagInt.diag_int <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.homLatticeCompletion_cut_integral_properties : ∀ (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop) (u : WO S T), u ∈ latO S T LS LT P → (∀ γ ∈ intAf D.host.F, pairA D.host.F 0 γ • u ∈ latO S T LS LT (fun v => P v ∧ evalV D.host.F v γ ≠ 0)) ∧ pairA D.host.F 0 1 • u = u ∧ u.map (infPart D) = 0 ∧ ((∀ v, ¬ P v) → u = 0) := by
  first | exact @GlobalTheory.FinPl.latO_algebra | exact GlobalTheory.FinPl.latO_algebra | (intros; apply GlobalTheory.FinPl.latO_algebra <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inLatticeStabilizerAtPlaces_mul_of_mem : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (a b : GA D S), InK S L P a → InK S L P b → InK S L P (a * b) := by
  first | exact @GlobalTheory.FinPl.inK_mul | exact GlobalTheory.FinPl.inK_mul | (intros; apply GlobalTheory.FinPl.inK_mul <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing

theorem _root_.GlobalTheory.T.isTameFinitePlaceHermitian_all : ∀ (D : D7) (v : Pl D), Tame D v := by
  first | exact @GlobalTheory.FinPl.TamePlaces.tame | exact GlobalTheory.FinPl.TamePlaces.tame | (intros; apply GlobalTheory.FinPl.TamePlaces.tame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitChar

theorem cont_ne_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → IsStdChar D ψ (-1) →
    Continuous χ ∧ χ ≠ 1 := by
  intro D k _ _ _ _ p ψ χ hχ hψ
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have htr : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun a : k => psiE ψ (p.sec a) := hψ.1.1.comp (htr.comp p.cont_sec)
  refine ⟨?_, ?_⟩
  · have h' : Continuous fun a : k => ((χ a : Circle) : ℂ) := by
      have he : (fun a : k => ((χ a : Circle) : ℂ)) = fun a => psiE ψ (p.sec a) := funext hχ
      rw [he]; exact hc
    first
      | exact Circle.isEmbedding_coe.continuous_iff.2 h'
      | exact continuous_induced_rng.2 h'
  · intro h1
    obtain ⟨a, ha⟩ := GlobalTheory.FinPl.CharNontriv.exists_psiE_sec_ne_one D k p ψ hψ
    apply ha
    rw [← hχ a, h1]
    simp

end GlobalTheory.FinPl.SplitChar
end
