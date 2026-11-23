module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle045
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle009
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem AnFr.rd_twistPull : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (ψ : Over.mk x0 ⊗ A ⟶ Over.mk x0 ⊗ A) (m : Over.mk x0 ⊗ A ⟶ A) (hm : ψ ≫ snd (Over.mk x0) A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd (Over.mk x0) A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L.L b (Over.mk x0))) (s' : LB.Sec (LPow A L.L a (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ) (p : (Fin g → ℂ) → Fin g → ℂ) (v : (Fin g → ℂ) → ℂ), ψ ≫ fst (Over.mk x0) A = fst (Over.mk x0) A → IsTwistPull A L.L ψ m hm a b α s s' → Φ.Rd b s θ → (∀ z, (ptSecT A (Φ.e z)).left ≫ m.left = (Φ.e (p z)).left ∧ ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j ∧ valAt' (ptSecT A (Φ.e z)).left (LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j) (α.s j).val = v z * (Φ.fr (j 0) z ^ a * Φ.fr (j 1) (p z) ^ (-b))) → Φ.Rd a s' (fun z => v z * θ (p z)) := by
  intro S A _ _ L x0 g Φ ψ m hm a b α s s' θ p v hψ ht hs hα j' z pt h1 h2 hj'
  obtain ⟨hmz, j, hj, hv⟩ := hα z
  change (vtfQ A (Φ.e z)).left ≫ m.left = _ at hmz
  change ⊤ ≤ (vtfQ A (Φ.e z)).left ⁻¹ᵁ _ at hj
  change valAt' (vtfQ A (Φ.e z)).left _ _ = _ at hv
  have h0 : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (j 0) := by
    rw [← vtfQ_snd A (Φ.e z)]
    intro q hq
    exact LB.wchart_le L.L ![(snd (Over.mk x0) A).left, m.left] j 0 (hj hq)
  have h1' : ⊤ ≤ (Φ.e (p z)).left ⁻¹ᵁ L.L.U (j 1) := by
    rw [← hmz]
    intro q hq
    exact LB.wchart_le L.L ![(snd (Over.mk x0) A).left, m.left] j 1 (hj hq)
  have e1 : ((vtfQ A (Φ.e z)).left ≫ ψ.left) ≫ (snd (Over.mk x0) A).left = (Φ.e (p z)).left := by
    rw [Category.assoc, ← Over.comp_left, hm, hmz]
  have e2 : ((vtfQ A (Φ.e z)).left ≫ ψ.left) ≫ (fst (Over.mk x0) A).left = 𝟙 (Sp ℂ) := by
    rw [Category.assoc, ← Over.comp_left, hψ]
    exact vtfQ_fst A (Φ.e z)
  have hr := hs (j 1) (p z) _ e1 e2 h1'
  have tw := vtf_twist A L.L ht (vtfQ A (Φ.e z)).left j hj
  have hne := Φ.fr_ne (j 1) (p z) h1'
  rw [vtf_pt_uniq A (Φ.e z) pt h1 h2]
  refine vtf_read A L.L s' (Φ.e z) (fun i => Φ.fr i z) (fun i i' h => Φ.fr_g i i' z h) (j 0) j' h0 hj' _ ?_
  refine tw.trans ?_
  refine (congrArg₂ (· * ·) hv hr).trans ?_
  have hz : Φ.fr (j 1) (p z) ^ b ≠ 0 := zpow_ne_zero _ hne
  rw [zpow_neg]
  field_simp

end GlobalTheory.AnVal
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.genMove_e_zero : Φ.e 0 = 1 := (Φ.e_ker 0).2 Φ.lat.zero_mem

theorem AnFr.genMove_e_zero_left : (Φ.e 0).left = x0 ≫ eSec A := by
  rw [Φ.genMove_e_zero]
  show (toUnit (Over.mk x0) ≫ η[A]).left = _
  rw [Over.comp_left]
  rfl

theorem AnFr.genMove_e_per (z a : Fin g → ℂ) (ha : a ∈ Φ.lat) : Φ.e (z + a) = Φ.e z := by
  rw [Φ.e_add, (Φ.e_ker a).2 ha, _root_.mul_one]

theorem genMove_chart {X Z : Scheme.{0}} (M : LB X) {K : Type} [Fintype K] (φ : K → (Z ⟶ X)) (q : Sp ℂ ⟶ Z)
    (j : K → M.ι) (h : ⊤ ≤ q ⁻¹ᵁ LB.wchart M φ j) (k : K) : ⊤ ≤ (q ≫ φ k) ⁻¹ᵁ M.U (j k) :=
  fun _ hy => LB.wchart_le M φ j k (h hy)

theorem AnFr.genRd_pullGen_iff {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L.L φ ε)) {Z' : Scheme.{0}} (h : Z' ⟶ Z) (q : Sp ℂ ⟶ Z') (p : K → Fin g → ℂ) (v : ℂ) :
    Φ.GenRd (fun k => h ≫ φ k) ε (LB.pullGen L.L φ ε t h) q p v ↔ Φ.GenRd φ ε t (q ≫ h) p v := by
  have hc : ∀ j : K → L.L.ι, (⊤ ≤ q ⁻¹ᵁ LB.wchart L.L (fun k => h ≫ φ k) j) ↔
      ⊤ ≤ (q ≫ h) ⁻¹ᵁ LB.wchart L.L φ j := fun j =>
    ⟨fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k,
      fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k⟩
  have hv : ∀ j : K → L.L.ι, (⊤ ≤ q ⁻¹ᵁ LB.wchart L.L (fun k => h ≫ φ k) j) →
      valAt' q (LB.wchart L.L (fun k => h ≫ φ k) j) ((LB.pullGen L.L φ ε t h).s j).val =
        valAt' (q ≫ h) (LB.wchart L.L φ j) (t.s j).val := fun j hp =>
    (vtf_val_res q _ hp _).trans (vtf_val_pullU _ _ _ _)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => by rw [Category.assoc]; exact h1 k, fun j hj => ?_⟩
    exact (hv j ((hc j).2 hj)).symm.trans (h2 j ((hc j).2 hj))
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => by rw [← h1 k, Category.assoc], fun j hj => ?_⟩
    exact (hv j hj).trans (h2 j ((hc j).1 hj))

theorem AnFr.genRd_period {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L.L φ ε)) (q : Sp ℂ ⟶ Z) (p a : K → Fin g → ℂ) (v : ℂ) (ha : ∀ k, a k ∈ Φ.lat)
    (H : Φ.GenRd φ ε t q p v) :
    Φ.GenRd φ ε t q (fun k => p k + a k) (v * ∏ k, Φ.fac (a k) (p k) ^ ε k) := by
  obtain ⟨h1, h2⟩ := H
  refine ⟨fun k => by rw [Φ.genMove_e_per _ _ (ha k)]; exact h1 k, fun j hj => ?_⟩
  rw [h2 j hj, _root_.mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk := genMove_chart L.L φ q j hj k
  rw [h1 k] at hk
  rw [Φ.fr_per (a k) (ha k) (j k) (p k) hk, mul_zpow]
  rfl

theorem AnFr.genRd_rigPow (k : ℤ) :
    Φ.GenRd (K := PUnit) (fun _ => eSec A) (fun _ => k) (rigPow A L.L L.rig k) x0 (fun _ => 0) 1 := by
  refine ⟨fun _ => Φ.genMove_e_zero_left.symm, fun j hj => ?_⟩
  have hk := genMove_chart L.L (K := PUnit) (fun _ => eSec A) x0 j hj PUnit.unit
  rw [← Φ.genMove_e_zero_left] at hk
  rw [_root_.one_mul, Fintype.prod_unique]
  have e := Φ.fr_0 (j PUnit.unit) hk
  show _ = Φ.fr (j PUnit.unit) 0 ^ k
  rw [e]
  exact vtf_valU x0 hj (L.rig.s j) k

end

theorem genRd_pull_period_rig : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), (∀ (Z' : Scheme.{0}) (h : Z' ⟶ Z) (q : Sp ℂ ⟶ Z') (p : K → Fin g → ℂ) (v : ℂ), Φ.GenRd (fun k => h ≫ φ k) ε (LB.pullGen L.L φ ε t h) q p v ↔ Φ.GenRd φ ε t (q ≫ h) p v) ∧ (∀ (q : Sp ℂ ⟶ Z) (p a : K → Fin g → ℂ) (v : ℂ), (∀ k, a k ∈ Φ.lat) → Φ.GenRd φ ε t q p v → Φ.GenRd φ ε t q (fun k => p k + a k) (v * ∏ k, Φ.fac (a k) (p k) ^ ε k)) ∧ ∀ k : ℤ, Φ.GenRd (K := PUnit) (fun _ => eSec A) (fun _ => k) (rigPow A L.L L.rig k) x0 (fun _ => 0) 1 :=
  fun _ _ _ _ _ _ _ Φ _ _ _ φ ε t =>
    ⟨fun _ h q p v => Φ.genRd_pullGen_iff φ ε t h q p v,
      fun q p a v ha H => Φ.genRd_period φ ε t q p a v ha H, fun k => Φ.genRd_rigPow k⟩

end GlobalTheory.AnVal
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem form_eq_zero_of_im_span {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (B : (Fin g → ℂ) → (Fin g → ℂ) → ℂ) (h1 : ∀ z z' w, B (z + z') w = B z w + B z' w)
    (h2 : ∀ (r : ℂ) z w, B (r • z) w = r * B z w) (h3 : ∀ z w w', B z (w + w') = B z w + B z w')
    (h4 : ∀ (r : ℝ) z w, B z (r • w) = r * B z w) (h0 : ∀ z ∈ s, ∀ w ∈ s, (B z w).im = 0) (z w : Fin g → ℂ) :
    B z w = 0 := by
  have hA : ∀ z ∈ s, ∀ w, (B z w).im = 0 := by
    intro z hz w
    have hw : w ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw => exact h0 z hz w hw
    | zero => simpa using congrArg Complex.im (h4 0 z 0)
    | add w w' _ _ e e' => rw [h3, Complex.add_im, e, e', add_zero]
    | smul r w _ e => rw [h4, Complex.im_ofReal_mul, e, mul_zero]
  have hB : ∀ z w, (B z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => exact hA z hz w
    | zero => simpa using congrArg Complex.im (h2 0 0 w)
    | add z z' _ _ e e' => rw [h1, Complex.add_im, e, e', add_zero]
    | smul r z _ e =>
      have : r • z = (r : ℂ) • z := by ext k; simp
      rw [this, h2, Complex.im_ofReal_mul, e, mul_zero]
  apply Complex.ext
  · have := hB (Complex.I • z) w
    rw [h2] at this
    simpa using this
  · simpa using hB z w

theorem hermForm_adj_of_im_span {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (A A' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm (A z) w).im = (hermForm Hm z (A' w)).im) (z w : Fin g → ℂ) :
    hermForm Hm (A z) w = hermForm Hm z (A' w) := by
  have hr : ∀ (r : ℝ) (w : Fin g → ℂ), r • w = (r : ℂ) • w := fun r w => by ext k; simp
  have l1 : ∀ z z' w, hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := fun z z' w => by
    simp only [hermForm, add_dotProduct]
  have l2 : ∀ (r : ℂ) z w, hermForm Hm (r • z) w = r * hermForm Hm z w := fun r z w => by
    simp only [hermForm, smul_dotProduct, smul_eq_mul]
  have l3 : ∀ z w w', hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := fun z w w' => by
    simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]
  have l4 : ∀ (r : ℝ) z w, hermForm Hm z ((r : ℂ) • w) = r * hermForm Hm z w := fun r z w => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal]
  refine sub_eq_zero.mp (form_eq_zero_of_im_span s hs
    (fun z w => hermForm Hm (A z) w - hermForm Hm z (A' w)) ?_ ?_ ?_ ?_ ?_ z w)
  · intro z z' w
    simp only [map_add (f := _), l1]; ring
  · intro r z w
    simp only [map_smul, l2]; ring
  · intro z w w'
    simp only [map_add (f := _), l3]; ring
  · intro r z w
    simp only [hr, map_smul, l4]; ring
  · intro z hz w hw
    simp only [Complex.sub_im, h0 z hz w hw, sub_self]

theorem anPt_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (σ' : KA l →+* ℂ) (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (Pm : (F.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ), IsPeriod (F.Di i) ty Pm → y.x = F.u i Pm → AHFrame F i Pm Hm χl fr → (∀ ℓ : Lt1 Dw, IsDerivAt0 (fun z => (F.ex i Pm z).left) (Pi.single (el.symm ℓ) 1) (y.u ℓ.1 ℓ.2)) → ∃ Φ : AnPt y g ty el, Φ.OfFam F i Pm ∧ Φ.Hm = Hm ∧ Φ.χ = χl ∧ Φ.fr = fr ∧ (∀ (α : 𝓞 E) a, Pm (F.t i (α • a)) = tyAct ty α (Pm (F.t i a))) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • Pm (F.t i a)) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el σ' F i Pm Hm χl fr hP hy hA hd
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := y
  dsimp only at hy hd
  subst hy
  obtain ⟨hH, -, hE, f1, f2, f3, f4, f5⟩ := hA
  have hlin : ∀ (α : 𝓞 E) b, Pm (α • b) = tyAct ty α (Pm b) := fun α b => by
    ext k
    simpa [tyAct] using hP.1 α b k
  refine ⟨{ e := F.ex i Pm
            lat := Pm.range
            span := by simpa using hP.2.2.2.1
            e_add := F.ex_add i Pm hP
            e_onto := F.ex_onto i Pm hP
            e_ker := F.ex_ker i Pm hP
            hol := anHol F i Pm hP
            Hm := Hm
            herm := hH
            χ := χl
            fr := fr
            fr_hol := f1
            fr_ne := f2
            fr_g := f3
            fr_0 := f4
            χ_norm := ?_
            fr_per := ?_
            lin := fun a z => F.ex_lin i Pm hP a z
            adj := ?_
            der := hd }, ⟨fun _ => rfl, rfl, hE⟩, rfl, rfl, rfl, fun α a => by rw [map_smul, hlin],
          fun a ha => F.ex_eta i Pm hP a ha⟩
  · rintro _ ⟨a, rfl⟩
    have hc : (F.ex i Pm 0).left.base (IsLocalRing.closedPoint ℂ) ∈
        (⨆ j, Xo.univ.t.PP.L.U j : Xo.univ.t.G.left.Opens) := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨j, -⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact (f5 a j 0).1
  · rintro _ ⟨a, rfl⟩ j z hz
    exact (f5 a j z).2 hz
  · intro a
    refine hermForm_adj_of_im_span _ hP.2.2.2.1 Hm _ _ ?_
    rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    rw [← hlin, ← hlin, hE, hE, (F.Di i).adj]

end GlobalTheory.AnVal
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameImm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

section Group

variable {g : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)}

theorem deriv_one (h0 : e 0 = (1 : Over.mk y ⟶ G).left) : IsDerivAt0 e 0 (1 : epsPt y ⟶ G).left := by
  let φ : epsPt y ⟶ Over.mk y := Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
  have h1 : (1 : epsPt y ⟶ G).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ e 0 := by
    rw [h0, ← MonObj.comp_one φ]
    rfl
  have h2 : spMap GlobalTheory.TangentOrigin.fstC ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ e 0 = e 0 := by
    rw [← Category.assoc, GlobalTheory.FrameTangent.spMap_comp']
    have : GlobalTheory.TangentOrigin.fstC.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ :=
      RingHom.ext fun r => by simp
    rw [this]
    simp [spMap]
  rw [h1, GlobalTheory.PointUnif.isDerivAt0_iff]
  refine ⟨h2, fun U hU f => ?_⟩
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := h2 ▸ (GlobalTheory.TangentOrigin.top_le_preimage_iff _ U).1 hU
  rw [GlobalTheory.TangentOrigin.evalPt_spMap_comp _ _ U hU0 hU, map_zero]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem deriv_list (h0 : e 0 = (1 : Over.mk y ⟶ G).left) :
    ∀ (m : ℕ) (w : Fin m → Fin g → ℂ) (v : Fin m → (epsPt y ⟶ G)), (∀ i, IsDerivAt0 e (w i) (v i).left) →
      IsDerivAt0 e (∑ i, w i) (List.ofFn v).prod.left
  | 0, w, v, _ => by simpa using deriv_one h0
  | m + 1, w, v, h => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
    exact GlobalTheory.PointUnif.deriv_mul h0 (h 0) (deriv_list h0 m _ _ fun i => h i.succ)

end Group

theorem anPt_imm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm := by
  classical
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ w hw
  by_contra hcon
  push Not at hcon
  apply hw
  have he0 : Φ.e 0 = 1 := (Φ.e_ker 0).2 (zero_mem _)
  have h0 : (fun z => (Φ.e z).left) 0 = (1 : Over.mk y.x ⟶ Xo.univ.t.G).left := congrArg (·.left) he0
  have d0 := deriv_one (e := fun z => (Φ.e z).left) h0
  have dw : IsDerivAt0 (fun z => (Φ.e z).left) w (1 : epsPt y.x ⟶ Xo.univ.t.G).left := by
    refine ⟨d0.1, fun U hU f => (d0.2 U hU f).trans ?_⟩
    rw [map_zero]
    refine (hcon U f ?_).symm
    have h3 := (GlobalTheory.TangentOrigin.top_le_preimage_iff _ U).1 hU
    exact (congrArg (fun p : Sp ℂ ⟶ Xo.univ.t.G.left => ⊤ ≤ p ⁻¹ᵁ U) d0.1).mp h3
  let q := (Fintype.equivFin (Lt1 Dw)).symm
  have key : ∀ w' : Fin g → ℂ, IsDerivAt0 (fun z => (Φ.e z).left) w' (1 : epsPt y.x ⟶ Xo.univ.t.G).left →
      IsCombAt y.x (m := Fintype.card (Lt1 Dw)) (fun i => y.u (q i).1 (q i).2) (fun i => w' (el.symm (q i)))
        (1 : epsPt y.x ⟶ Xo.univ.t.G).left := by
    intro w' hw'
    let v : Fin (Fintype.card (Lt1 Dw)) → (epsPt y.x ⟶ Xo.univ.t.G) := fun i =>
      GlobalTheory.FrameTangent.smT y.x (w' (el.symm (q i)))
        (GlobalTheory.FrameTangent.ovT (t := Xo.univ.t) (y.tan (q i).1 (q i).2))
    refine ⟨v, fun i => rfl, GlobalTheory.PointUnif.deriv_unique ?_ hw'⟩
    have hs : w' = ∑ i, w' (el.symm (q i)) • (Pi.single (el.symm (q i)) 1 : Fin g → ℂ) := by
      exact (pi_eq_sum_univ' w').trans
        (Equiv.sum_comp (q.trans el.symm) (fun j => w' j • (Pi.single j 1 : Fin g → ℂ))).symm
    have := deriv_list (e := fun z => (Φ.e z).left) h0 _
      (fun i => w' (el.symm (q i)) • (Pi.single (el.symm (q i)) 1 : Fin g → ℂ)) v
      fun i => GlobalTheory.PointUnif.deriv_smul (Φ.der (q i)) _
    rwa [← hs] at this
  have ht : IsTanAt y.x (1 : epsPt y.x ⟶ Xo.univ.t.G).left := ⟨Over.w _, d0.1.trans h0⟩
  have hu := (GlobalTheory.FrameTangent.frame_tangent_basis E H Dw l Xo c ℂ y _ ht).unique
    (y₁ := fun ℓ => w (el.symm ℓ)) (y₂ := fun ℓ => (0 : Fin g → ℂ) (el.symm ℓ)) (key w dw) (key 0 d0)
  funext j
  simpa using congrFun hu (el j)

end GlobalTheory.FrameImm
end
end
