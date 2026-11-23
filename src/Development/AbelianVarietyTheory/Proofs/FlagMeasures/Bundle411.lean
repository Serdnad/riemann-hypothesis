module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarMeasureBesselUnitaryEqPullbackProduct
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle389
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle406
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSubgroupUnitriangularPairsKeepingDoubleCos
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle369
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle393
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle365
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle371
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle407
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle342
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardStabilizerInnerDatumRowDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsGenericTermIffNoLocalDefectBaseFrames
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.haarMeasure_besselUnitary_eq_pullback_product : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB → ∀ u : D.what₂.Word, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ X.muH u Set.univ = c ∧ ∀ A : Set X.B.I.Ginf, MeasurableSet A → X.muH u A = c * Measure.pi (C.muW u) (trI C '' A) := by
  first | exact @GlobalTheory.PullHaarW.pullH | exact GlobalTheory.PullHaarW.pullH | (intros; apply GlobalTheory.PullHaarW.pullH <;> assumption)
end

section

noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.HermitianLatticesTheory GlobalTheory.Mass

namespace GlobalTheory.RowsMean

section General
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem sameGenus_trans (h : V →ₗ⋆[K] V →ₗ[K] K) {L M N : Submodule (𝓞 K) V}
    (h1 : SameGenus h L M) (h2 : SameGenus h M N) : SameGenus h L N := by
  intro p hp
  obtain ⟨g₁, hg₁, e₁⟩ := h1 p hp
  obtain ⟨g₂, hg₂, e₂⟩ := h2 p hp
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  rw [genusBasic_gmap_mul, e₁, e₂]

theorem sameGenus_refl (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : SameGenus h L L :=
  fun _ _ => ⟨1, one_mem _, genusBasic_gmap_one _⟩

theorem genus_eq_iff (h : V →ₗ⋆[K] V →ₗ[K] K) {L M : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hM : Submodule.IsFullLattice K M) :
    genus h L = genus h M ↔ L ∈ genus h M := by
  constructor
  · intro e; rw [← e]; exact ⟨hL, sameGenus_refl h L⟩
  · intro hLM
    ext N
    constructor
    · rintro ⟨hN, hs⟩
      exact ⟨hN, sameGenus_trans h hLM.2 hs⟩
    · rintro ⟨hN, hs⟩
      exact ⟨hN, sameGenus_trans h (genusBasic_symm h _ _ hLM.2) hs⟩

theorem mass_nonneg (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : 0 ≤ mass h L := by
  unfold mass
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => by positivity
  · exact le_rfl

end General
end GlobalTheory.RowsMean

namespace GlobalTheory.RowsMean
section General
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem inv_card_eq (X : Type) [Nonempty X] :
    ((ENat.card X : ℕ∞) : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((Nat.card X : ℝ))⁻¹ := by
  rcases finite_or_infinite X with hX | hX
  · rw [ENat.card_eq_coe_natCard]
    have hp : 0 < Nat.card X := Nat.card_pos
    rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hp), ENNReal.ofReal_natCast]
    simp
  · rw [ENat.card_eq_top_of_infinite, Nat.card_eq_zero_of_infinite]
    simp

def stabEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) :
    MulAction.stabilizer (isom h) M ≃ Formalism.ThetaLiftIndependence.autL h M where
  toFun g := ⟨g.1.1, g.1.2, g.2⟩
  invFun a := ⟨⟨a.1, a.2.1⟩, a.2.2⟩
  left_inv g := rfl
  right_inv a := rfl

theorem mass_le_orbMass (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) :
    ENNReal.ofReal (mass h L) ≤ orbMass (isom h) (genus h L) := by
  unfold mass
  split_ifs with hs
  swap
  · simp
  have hs' : Formalism.ThetaLiftIndependence.IsClassReps h L hs.choose := hs.choose_spec
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  have hrel : ∀ M : Submodule (𝓞 K) V, MulAction.orbitRel (isom h) (Submodule (𝓞 K) V)
      (Quotient.out (Quotient.mk'' M : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V))) M :=
    fun M => Quotient.exact' (Quotient.out_eq' _)
  have hq : ∀ M ∈ hs.choose, Quotient.out (Quotient.mk'' M :
      MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V)) ∈ genus h L := by
    intro M hM
    obtain ⟨g, hg⟩ := hrel M
    rw [← hg]
    exact GlobalTheory.Mass.Transp.genus_stable L g M (hs'.1 M hM)
  let qm : hs.choose → {q : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V) //
      Quotient.out q ∈ genus h L} := fun M => ⟨Quotient.mk'' M.1, hq M.1 M.2⟩
  have hinj : Function.Injective qm := by
    rintro ⟨M₁, h₁⟩ ⟨M₂, h₂⟩ e
    have e' : (Quotient.mk'' M₁ : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V)) =
        Quotient.mk'' M₂ := congrArg Subtype.val e
    obtain ⟨g, hg⟩ := Quotient.exact' e'
    have hM₁ : M₁ ∈ genus h L := hs'.1 M₁ h₁
    have u := (hs'.2 M₁ hM₁).unique ⟨h₁, 1, one_mem _, genusBasic_gmap_one _⟩ ⟨h₂, g.1, g.2, hg⟩
    exact Subtype.ext u
  unfold orbMass orbSum
  rw [← Finset.sum_attach]
  have hterm : ∀ M : hs.choose, ENNReal.ofReal (((Nat.card (Formalism.ThetaLiftIndependence.autL h M.1) : ℕ) : ℝ))⁻¹ =
      ((ENat.card (MulAction.stabilizer (isom h) (Quotient.out (qm M).1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1 := by
    intro M
    rw [mul_one]
    have e1 : ENat.card (MulAction.stabilizer (isom h) (Quotient.out (qm M).1)) =
        ENat.card (Formalism.ThetaLiftIndependence.autL h M.1) :=
      ENat.card_congr (((MulAction.stabilizerEquivStabilizerOfOrbitRel (hrel M.1)).toEquiv).trans
        (stabEquiv h M.1))
    haveI : Nonempty (Formalism.ThetaLiftIndependence.autL h M.1) := ⟨stabEquiv h M.1 1⟩
    rw [e1, inv_card_eq]
  simp_rw [hterm]
  exact (Finset.sum_image (s := hs.choose.attach) (g := qm)
    (f := fun q : {q : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V) // Quotient.out q ∈ genus h L} =>
      ((ENat.card (MulAction.stabilizer (isom h) (Quotient.out q.1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1)
    (fun a _ b _ e => hinj e)).symm.le.trans (ENNReal.sum_le_tsum _)

end General
end GlobalTheory.RowsMean

namespace GlobalTheory.RowsMean

theorem sum_le_of_classes {ι α : Type} (s : Finset ι) (L : ι → α) (G : α → Set α) (P : α → Prop)
    (hP : ∀ i ∈ s, P (L i)) (hG : ∀ a b, P a → P b → (G a = G b ↔ a ∈ G b))
    (F w : ι → ℝ≥0∞) (b : ℝ≥0∞)
    (hcl : ∀ i₀ ∈ s, ∑ i ∈ s.filter (fun i => L i ∈ G (L i₀)), F i ≤
      (∑ i ∈ s.filter (fun i => L i ∈ G (L i₀)), w i) * b) :
    ∑ i ∈ s, F i ≤ (∑ i ∈ s, w i) * b := by
  have hmap : ∀ i ∈ s, G (L i) ∈ s.image (fun i => G (L i)) := fun i hi => Finset.mem_image_of_mem _ hi
  rw [← Finset.sum_fiberwise_of_maps_to hmap F, ← Finset.sum_fiberwise_of_maps_to hmap w, Finset.sum_mul]
  refine Finset.sum_le_sum fun y hy => ?_
  obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hy
  have e : s.filter (fun i => G (L i) = G (L i₀)) = s.filter (fun i => L i ∈ G (L i₀)) :=
    Finset.filter_congr fun i hi => hG _ _ (hP i hi) (hP i₀ hi₀)
  rw [e]
  exact hcl i₀ hi₀

end GlobalTheory.RowsMean

namespace GlobalTheory.TypeAsm
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowsMean : RowsMeanC := by
  intro D large₂ X Y u hStd W HW hEmb φ B hB hφ hbd
  have hOrb := GlobalTheory.T.rowsGenus_weightedSumComparison D large₂ X Y u hStd W HW hEmb
  have hLat := GlobalTheory.T.base_lattice_construction_holds D large₂ X Y u hStd W HW hEmb
  have hw : ∀ Λ, 0 ≤ wRow D (X.Fu u) Λ := fun Λ => by unfold wRow; positivity
  have hm : 0 ≤ massRows D (X.Fu u) (Y.what₂ u) := Finset.sum_nonneg fun Λ _ => hw Λ
  rw [ENNReal.ofReal_mul hm]
  unfold massRows
  rw [ENNReal.ofReal_sum_of_nonneg fun Λ _ => hw Λ]
  refine GlobalTheory.RowsMean.sum_le_of_classes (Y.what₂ u) (fun Λ => GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ)
    (Formalism.HermitianLatticesTheory.genus HW.B.flip) (Submodule.IsFullLattice D.host.E) (fun Λ hΛ => (hLat Λ hΛ).1.1)
    (fun a b ha hb => GlobalTheory.RowsMean.genus_eq_iff _ ha hb) _ _ _ ?_
  intro Λ₀ hΛ₀
  have h1 := hOrb φ hφ Λ₀ hΛ₀
  have h2 := hOrb (fun _ => 1) (fun _ _ => rfl) Λ₀ hΛ₀
  simp only [mul_one] at h2
  rw [h1, h2, mul_assoc]
  gcongr
  refine (hbd Λ₀ hΛ₀).trans ?_
  rw [ENNReal.ofReal_mul (GlobalTheory.RowsMean.mass_nonneg _ _)]
  gcongr
  exact GlobalTheory.RowsMean.mass_le_orbMass _ _

end GlobalTheory.TypeAsm
end
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transportedTypeVectors_span_adelicLattice_modLevel : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), c ≡ 1 [MOD X.B.g] → (∀ x, p (embA X wt ιA x) = embA X wt ιA x) → (∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf) → (∀ a, p (incl X.B.I (X.eR a)) = 0 ∧ p (incl X.B.I (X.fR a)) = 0) → p (incl X.B.I (X.zR u)) = 0 → ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → ∀ y ∈ hat D.host.F (Mq wt), InModL (hat D.host.F (Mq wt)) (D.host.g 0 * D.host.g 1) (Set.range b ∪ Set.range bd) y := by
  first | exact @GlobalTheory.St.G.FrameSpan.span_mod | exact GlobalTheory.St.G.FrameSpan.span_mod | (intros; apply GlobalTheory.St.G.FrameSpan.span_mod <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.TgKey

theorem translate_key : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ t : TauC Y u u') (Λ₀ Λ₁ : LV D), TG F F' t₀ Λ₀ → TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → ∃ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam, ∃ a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam', ∀ s : TauC Y u u', s.lam = t₀.lam → s.lam' = t₀.lam' → (∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u')), s.lin = n * (a * t₀.lin * a'⁻¹) * n') → key s = key t := by
  intro D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ h₁ hR
  obtain ⟨hl, hl', a, ha, a', ha', K1⟩ := GlobalTheory.T.terms_same_rational_inner_class_are_translates D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ h₁ hR
  refine ⟨a, ha, a', ha', ?_⟩
  rintro s hs hs' ⟨n, hn, n', hn', hsl⟩
  rw [GlobalTheory.Unfold.KeyIff.key_eq_iff]
  refine ⟨hs.trans hl.symm, hs'.trans hl'.symm, ?_⟩
  rw [hs, hsl]
  have hI : ∀ {x y : GV D}, x ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → y ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      x * y ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun hx hy => (Formalism.HermitianLatticesTheory.isom _).mul_mem hx hy
  have ht : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have htΛ : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have ha'i : a'⁻¹ ∈ Aut0 (lf D (X.Fu u')) t₀.lam' := (GlobalTheory.KeyGroup.flagLatticeAutomorphismGroup _ _).inv_mem ha'
  have hγ : a * t₀.lin * a'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hI (hI ha.1.1 ht) ha'i.1.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap (a * t₀.lin * a'⁻¹) t₀.lam' = t₀.lam := by
    rw [GlobalTheory.Unfold.Model.gmap_mul, GlobalTheory.Unfold.Model.gmap_mul, ha'i.2, htΛ, ha.2]
  have hγn : a * t₀.lin * a'⁻¹ * n' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hI hγ hn'.1.1
  have hγnΛ : Formalism.HermitianLatticesTheory.gmap (a * t₀.lin * a'⁻¹ * n') t₀.lam' = t₀.lam := by
    rw [GlobalTheory.Unfold.Model.gmap_mul, hn'.1.2, hγΛ]
  have hs3 : n * (a * t₀.lin * a'⁻¹) * n' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
    rw [mul_assoc]; exact hI hn.1.1 hγn
  have hs3Λ : Formalism.HermitianLatticesTheory.gmap (n * (a * t₀.lin * a'⁻¹) * n') t₀.lam' = t₀.lam := by
    rw [mul_assoc, GlobalTheory.Unfold.Model.gmap_mul, hγnΛ, hn.1.2]
  have K2 := GlobalTheory.KeyGroup.keyEq_right (F := lf D (X.Fu u)) (F0' := X.Fu u') hγ hγΛ hn'
  have K3 := GlobalTheory.KeyGroup.keyEq_left (F0' := X.Fu u') hγn hn
  rw [← mul_assoc] at K3
  have K4 := GlobalTheory.KeyGroup.keyEq_trans hγ hγn hγΛ hγnΛ K2 K3
  have K5 := GlobalTheory.KeyGroup.keyEq_symm hγ hs3 hγΛ hs3Λ K4
  exact GlobalTheory.KeyGroup.keyEq_trans hs3 hγ hs3Λ hγΛ K5 K1

end GlobalTheory.Unfold.TgKey
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatAdapt

theorem witt_flag (D : D7) (T : D.host.E) (hT : T ≠ 0) (F F' : FlagG (VS D) D.R.rS T) :
    ∃ g : GV D, g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ ∀ a, g (F.fvec a) = F'.fvec a := by
  have hind : ∀ G : FlagG (VS D) D.R.rS T, LinearIndependent D.host.E G.fvec := by
    intro G
    unfold FlagG.fvec
    rw [linearIndependent_finSnoc]
    refine ⟨G.e_indep, fun hz => hT ?_⟩
    have h0 : ∀ x ∈ Submodule.span D.host.E (Set.range G.e), (VS D).hT x G.z = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨a, rfl⟩ := hy; exact G.z_orth a
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul c x _ hx => simp [hx]
    have := h0 _ hz
    rw [G.z_norm] at this
    exact neg_eq_zero.1 this
  have hgram : ∀ G : FlagG (VS D) D.R.rS T, ∀ i j, (VS D).hT (G.fvec i) (G.fvec j) =
      if i = Fin.last _ ∧ j = Fin.last _ then -T else 0 := by
    intro G i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [FlagG.fvec, G.z_norm]
      | cast b =>
        simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
        rw [← (VS D).herm.eq (G.e b) G.z, G.z_orth b, map_zero]
        simp [Fin.castSucc_ne_last]
    | cast a =>
      induction j using Fin.lastCases with
      | last => simp [FlagG.fvec, G.z_orth, Fin.castSucc_ne_last]
      | cast b => simp [FlagG.fvec, G.e_iso, Fin.castSucc_ne_last]
  obtain ⟨g, hg, hgi⟩ := GlobalTheory.St.WittT.witt_family F.fvec F'.fvec (hind F) (hind F')
    (fun i j => by rw [hgram F, hgram F'])
  exact ⟨g, hg, hgi⟩

theorem iso_X {D : D7} {T : D.host.E} (G : FlagG (VS D) D.R.rS T) :
    ∀ y ∈ G.X, ∀ x ∈ G.X, (VS D).hT y x = 0 := by
  intro y hy x hx
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, rfl⟩ := hw
    induction hy using Submodule.span_induction with
    | mem v hv => obtain ⟨a, rfl⟩ := hv; exact G.e_iso a b
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul c u _ hu => simp [hu]

theorem xa_last {D : D7} {T : D.host.E} (G : FlagG (VS D) D.R.rS T) : G.Xa D.R.rS = G.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext v
  simp

theorem lsub_eq {D : D7} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (h : F.fl.X = F'.fl.X) (Λ : LV D) : Lsub Λ F = Lsub Λ F' := by
  simp only [Lsub, Lrep, Xsp, h]

theorem xlam_eq {D : D7} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (h : F.fl.X = F'.fl.X) (Λ : LV D) : XLam Λ F = XLam Λ F' := by
  simp only [XLam, Xsp, h]

theorem row_lattice_of_local_standard : ∀ (D : D7) (Tn : ℕ), Tn ≠ 0 → ∀ (F0 : FlagG (VS D) D.R.rS (Tn : D.host.E)) (G : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ g, Adapt g (lf D F0) G ∧ IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
  intro D Tn hTn F0 G Z A hA Λ hΛ hloc
  have hU := GlobalTheory.T.isUnimodular_of_local_standardLattice_translates
  have hX := GlobalTheory.T.isotropicPart_eq_span_scaledFrame_unitriangular
  have hZ := GlobalTheory.T.exists_add_isotropicSpan_mem_locallyStandardLattice
  have hP := GlobalTheory.T.anisotropicFrameVector_primitive_in_innerLattice
  have hM := GlobalTheory.T.exists_flag_of_unitriangular_isotropic_shift
  have hTr := GlobalTheory.T.rowLattice_properties_transport_by_isometry
  have hC := GlobalTheory.T.fixed_conv_of_integral_flag_lattice
  have hu := hU D Z A Λ hΛ hloc
  obtain ⟨e', he', hXe⟩ := hX D _ G Z A hA Λ hΛ hloc
  obtain ⟨x, hx, hzx⟩ := hZ D _ G Z A hA Λ hΛ hloc
  have hpr := hP D _ G Z A hA Λ hΛ hloc
  obtain ⟨G', hGe, hGz, hGX⟩ := hM D _ G.fl e' x he' hx
  have hT0 : ((Tn : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hTn
  obtain ⟨g, hg, hga⟩ := witt_flag D _ hT0 F0 G'
  have hX' : XLam Λ (lf D G') = XS D G' := by
    rw [xlam_eq (lf D G') G hGX, hXe, XS, hGe]
  have hpr' : ∀ c : D.host.E, c • G'.z ∈ Lsub Λ (lf D G') → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
    intro c hc
    rw [lsub_eq (lf D G') G hGX] at hc
    refine hpr c ?_
    have hcx : c • G.fl.z = c • G'.z - c • x := by rw [hGz, smul_add]; abel
    rw [hcx]
    refine Submodule.sub_mem _ hc ?_
    have hxX : c • x ∈ (Xsp G : Submodule D.host.E (VS D).V) := Submodule.smul_mem _ c hx
    refine ⟨Submodule.mem_sup_right hxX, ?_⟩
    show c • x ∈ orth (VS D) (Xsp G)
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro y hy
    exact iso_X G.fl y hy _ hxX
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hTr D _ F0 G' g hg hga Λ hΛ hu (hGz ▸ hzx) hX' hpr'
  refine ⟨g, ⟨hg, fun a => ?_⟩, h1, ⟨h2, h3, ⟨h4, rfl⟩, hC D _ F0 _ h5 h6⟩, h5⟩
  show g (F0.fvec a) - G.fl.fvec a ∈ G.fl.Xa a.val
  rw [hga a]
  induction a using Fin.lastCases with
  | last =>
    simp only [FlagG.fvec, Fin.snoc_last, Fin.val_last, hGz, xa_last]
    simpa using hx
  | cast b =>
    simp only [FlagG.fvec, Fin.snoc_castSucc, Fin.val_castSucc, hGe]
    exact he' b

end GlobalTheory.RowLatAdapt
end
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_termLattice_baseFrames_of_basePoint : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ t : TauC Y u u', ptPN t = toPts w → ∃ Λ, TG F F' t Λ := by
  first | exact @GlobalTheory.Unfold.tg_of_base_point | exact GlobalTheory.Unfold.tg_of_base_point | (intros; apply GlobalTheory.Unfold.tg_of_base_point <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.local_identification_eq_of_global_lattices_eq : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 → ∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ := by
  first | exact @GlobalTheory.Unfold.IotaLocal.iotaGraph_eq_of_gdat | exact GlobalTheory.Unfold.IotaLocal.iotaGraph_eq_of_gdat | (intros; apply GlobalTheory.Unfold.IotaLocal.iotaGraph_eq_of_gdat <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalLatticeClasses_finite_localOrbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → {h | h ∈ H0 F F' ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite ∧ ∃ S : Finset (LV D), ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∃ Λs ∈ S, ∃ γ ∈ H0 F F', Formalism.HermitianLatticesTheory.gmap γ Λs = Λ := by
  first | exact @GlobalTheory.Unfold.ClFin.classes_finite | exact GlobalTheory.Unfold.ClFin.classes_finite | (intros; apply GlobalTheory.Unfold.ClFin.classes_finite <;> first | assumption | exact (by assumption : Submodule.IsFullLattice _ _).toIsLattice)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.term_row_double_coset_eq_iff_isometries : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', key t = key t' ↔ t.lam = t'.lam ∧ t.lam' = t'.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin t'.lin := by
  first | exact @GlobalTheory.Unfold.KeyIff.key_eq_iff | exact GlobalTheory.Unfold.KeyIff.key_eq_iff | (intros; apply GlobalTheory.Unfold.KeyIff.key_eq_iff <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.card_stabilizer_innerDatum_rowDoubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → ∀ (B : Subgroup (GV D × GV D)) (N N' : Subgroup (GV D)), (∀ b, b ∈ B ↔ b.1 ∈ Aut0 (lf D (X.Fu u)) t.lam ∧ b.2 ∈ Aut0 (lf D (X.Fu u')) t.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin (b.1 * t.lin * b.2⁻¹)) → (N : Set (GV D)) = NLam t.lam (lf D (X.Fu u)) → (N' : Set (GV D)) = NLam t.lam' (lf D (X.Fu u')) → Nat.card (stabL F F' Λ) = (N.prod N').relIndex B := by
  first | exact @GlobalTheory.StabCnt.stab_card | exact GlobalTheory.StabCnt.stab_card | (intros; apply GlobalTheory.StabCnt.stab_card <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_subgroup_unitriangular_pairs_keeping_doubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (t : TauC Y u u'), ∃ B : Subgroup (GV D × GV D), (∀ b, b ∈ B ↔ b.1 ∈ Aut0 (lf D (X.Fu u)) t.lam ∧ b.2 ∈ Aut0 (lf D (X.Fu u')) t.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin (b.1 * t.lin * b.2⁻¹)) ∧ (∀ n ∈ NLam t.lam (lf D (X.Fu u)), ∀ n' ∈ NLam t.lam' (lf D (X.Fu u')), (n, n') ∈ B) ∧ ∀ a₁ ∈ Aut0 (lf D (X.Fu u)) t.lam, ∀ a₂ ∈ Aut0 (lf D (X.Fu u)) t.lam, ∀ a₁' ∈ Aut0 (lf D (X.Fu u')) t.lam', ∀ a₂' ∈ Aut0 (lf D (X.Fu u')) t.lam', (KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam (a₁ * t.lin * a₁'⁻¹) (a₂ * t.lin * a₂'⁻¹) ↔ (a₁⁻¹ * a₂, a₁'⁻¹ * a₂') ∈ B) := by
  first | exact @GlobalTheory.KeyGroup.keyStab_subgroup | exact GlobalTheory.KeyGroup.keyStab_subgroup | (intros; apply GlobalTheory.KeyGroup.keyStab_subgroup <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isGenericTerm_iff_no_localDefect_baseFrames : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → (t.generic ↔ ∀ p d τ, LocNG.IsTermOver (FP p) d τ → τ.abelian₂ = lattice₂ D Z.M p Λ → ¬ LocNG.BBne (H := locH Z p) τ) := by
  first | exact @GlobalTheory.Unfold.GenLoc.generic_iff_local | exact GlobalTheory.Unfold.GenLoc.generic_iff_local | (intros; apply GlobalTheory.Unfold.GenLoc.generic_iff_local <;> assumption)
end
