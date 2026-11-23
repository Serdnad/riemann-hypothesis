module

import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle087
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle025
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericUnitValue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_of_secScal {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ₁ : K → (Y' ⟶ X)} {ε₁ : K → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K' → (Y ⟶ X)} {ε₂ : K' → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)} (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c)
    (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  apply GlobalTheory.UU.sval_of_secScal <;> assumption

theorem isUnit_cst_generic {V : Type} [CommRing V] [IsDomain V] (y : Spec (CommRingCat.of (FractionRing V)))
    {c : V} (hc : c ≠ 0) : IsUnit (cst (jK V) y c) := by
  have hK : IsUnit (algebraMap V (FractionRing V) c) :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)).isUnit
  obtain ⟨w, hw⟩ := hK
  rw [show cst (jK V) y c = cst (𝟙 _) y (algebraMap V (FractionRing V) c) from H1.gs_spec _ y c, ← hw]
  exact ⟨⟨cst (𝟙 _) y (w : FractionRing V), cst (𝟙 _) y (↑w⁻¹ : FractionRing V),
    by rw [← H1.cst_mul, Units.mul_inv, H1.cst_one], by rw [← H1.cst_mul, Units.inv_mul, H1.cst_one]⟩, rfl⟩

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

lemma unitK_fst : (unitK (G := G)) ≫ pullback.fst G.hom (jK V) = jK V ≫ eSec G := by
  simp only [unitK, pullback.lift_fst]

lemma gs_unitK_scal (y : Spec (CommRingCat.of (FractionRing V))) (c : V) :
    gs (unitK (G := G)) y ⊤ (scal (pullback.snd G.hom (jK V) ≫ jK V) c) = cst (jK V) y c := by
  have hsec : (unitK (G := G)) ≫ pullback.snd G.hom (jK V) = 𝟙 _ := by
    simp only [unitK, pullback.lift_snd]
  unfold scal cst
  refine (gs_pull (unitK (G := G)) (pullback.snd G.hom (jK V) ≫ jK V) y ⊤ trivial _).trans ?_
  rw [← Category.assoc, hsec, Category.id_comp]

end

theorem value_at_generic_unit : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k : ℕ) (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k) (u : P.U.SecK (k * N)) (F' : Fam P.D.toPre (FractionRing V) (k * N)), P.U.Expands k s F → P.U.Expands (k * N) u F' → PullAl P.D (FractionRing V) P.oD a k N F F' → ∀ (y : Spec (CommRingCat.of (FractionRing V))) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u unitK y J = (Geo.Tor.val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))).val * Geo.Tor.sval s unitK y J := by
  intro hL V _ _ _ E _ _ _ H t P a N hN hN0
  intro k s F u F' hs hu hpull y J hJ
  let _ := H.starRing
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  obtain ⟨X, hX, hXc⟩ := exists_XB P.D P.D.toPre.P.isLB P.oD H.w0 uΨ huΨ a N hN hN0 1
  obtain ⟨c, σ'', τ, hc, hsτ, huσ, hth⟩ :=
    GlobalTheory.PullExpInt.main hL.globalFns V E H t P a N hN hN0 X hX hXc k s F u F' hs hu hpull
  have hv := GlobalTheory.UnitValue.value_at_unit_section V E H t P a N hN hN0 X hX hXc k σ'' τ hth _ (jK V) y J hJ
  have e₁ := sval_of_secScal huσ unitK y hJ
  have e₂ := sval_of_secScal hsτ unitK y hJ
  rw [unitK_fst, gs_unitK_scal] at e₁ e₂
  rw [e₁, e₂] at hv
  apply (isUnit_cst_generic y hc).mul_left_cancel
  rw [hv]
  ring

end GlobalTheory.GenericUnitValue
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxFamScalar

section Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X X' Y Y' W W' Z : Scheme.{0}}

theorem sval_of_secScal {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  apply GlobalTheory.UU.sval_of_secScal <;> assumption

theorem secScal_of_pointwise {L : LB X} (hL : L.IsLB) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : ∀ (y : Y') (J : (Y' ⟶ X) → L.ι), Good L y J →
      sval s₂ (𝟙 Y' ≫ h) y J = gs (𝟙 Y') y ⊤ c * sval s₁ (𝟙 Y') y J) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c := by
  unfold GeneratorPullback.SecScal resTop
  intro j₁ j₂ hc
  apply fn_ext
  intro y hy
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL y (Sum.elim φ₁ fun k => h ≫ φ₂ k) (Sum.elim j₁ j₂) hc (by
    rintro (k | k)
    · exact Set.mem_iInter.1 hy.1 k
    · exact Set.mem_iInter.1 hy.2 k)
  have hW : h y ∈ LB.wchart L φ₂ j₂ := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
  have e := H y J hJ
  rw [sval_of s₂ (𝟙 Y' ≫ h) y J j₂ (fun k => by simpa using hJj (Sum.inr k)),
    sval_of s₁ (𝟙 Y') y J j₁ (fun k => by simpa using hJj (Sum.inl k))] at e
  calc _ = _ := gs_res _ y _ hy _
    _ = _ := gs_pull _ h y _ hW _
    _ = _ := e
    _ = _ := (congrArg₂ (· * ·) (gs_res _ y _ hy _) (gs_res _ y _ hy _)).symm
    _ = _ := (gs_mul _ y _ hy _ _).symm

variable {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem box_sval (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')}
    {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y' ⟶ Y)}
    (hφ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (s' : LB.Sec (LB.LinComb M' φ' ε))
    (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (hle : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι) i,
      LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM ≤
        ρ i ⁻¹ᵁ LB.wchart M (φ i) (fun a => jN a i))
    (H : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι),
      (@id (Γ(Y', LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
        ((LB.linCombIso w φ' ε).s (jN, jM))).val * rs inf_le_right (s'.f jM) =
        ∏ i, rs (hle jN jM i) (((ρ i).app _).hom ((s i).f (fun a => jN a i))))
    (q : Z ⟶ Y') (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (q ≫ φ' a) y (fun i => J ((q ≫ φ' a) ≫ pr i)) (J' (q ≫ φ' a)) ^ ε a).val * sval s' q y J' =
      ∏ i, sval (s i) (q ≫ ρ i) y J := by
  have hq : q y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (q ≫ φ' a)) :=
    ⟨Good.mem (L := LB.LinComb M pr (fun _ => 1)) (J := fun ψ i => J (ψ ≫ pr i)) (fun ψ => hJ.mem pr ψ) φ' q,
      hJ'.mem φ' q⟩
  have key := congrArg (gs q y _) (H (fun a i => J ((q ≫ φ' a) ≫ pr i)) (fun a => J' (q ≫ φ' a)))
  calc _ = _ := congrArg (fun u => (∏ a, bw w (q ≫ φ' a) y (fun i => J ((q ≫ φ' a) ≫ pr i)) (J' (q ≫ φ' a)) ^ ε a).val * u)
          ((sval_of s' q y J' _ (fun a => rfl)).trans (gs_res q y _ hq _).symm)
    _ = _ := congrArg (· * _) (congrArg Units.val (gm_linCombIso w φ' ε q y _ _ hq).symm)
    _ = _ := congrArg (· * _) (gs_unit q y _ hq _).symm
    _ = _ := (gs_mul q y _ hq _ _).symm
    _ = _ := key
    _ = _ := gs_prod q y _ hq Finset.univ _
    _ = _ := Finset.prod_congr rfl fun i _ =>
          ((gs_res q y _ hq _).trans (gs_pull q (ρ i) y _ (hle _ _ i hq) _)).trans
            (sval_of (s i) (q ≫ ρ i) y J _ (fun a => by simp only [Category.assoc, hφ])).symm

theorem gs_scal {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  unfold scal
  have e := gs_pull (𝟙 Z) r z ⊤ trivial ((Scheme.Hom.appTop p).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))
  rw [Category.id_comp] at e
  rw [← e, Scheme.Hom.comp_appTop]
  rfl

theorem gs_scal_prod {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (p' : Y' ⟶ Spec (CommRingCat.of R))
    (ρ : Fin j → (Y' ⟶ Y)) (hρ : ∀ i, ρ i ≫ p = p') (y : Y') (r : Fin j → R) :
    ∏ i, gs (𝟙 _ ≫ ρ i) y ⊤ (scal p (r i)) = gs (𝟙 _) y ⊤ (scal p' (∏ i, r i)) := by
  have hsc : (∏ i, scal p' (r i)) = scal p' (∏ i, r i) := by
    simp only [scal, map_prod]
  rw [← hsc, gs_prod (𝟙 _) y ⊤ trivial Finset.univ]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gs_scal, Category.id_comp, hρ]

theorem secScal_box (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    {K : Type} [Fintype K] {ε : K → ℤ}
    {φ' : K → (Y' ⟶ X')} {φ : Fin j → K → (Y ⟶ X)} {ρ : Fin j → (Y' ⟶ Y)}
    {ψ' : K → (W' ⟶ X')} {ψ : Fin j → K → (W ⟶ X)} {σ : Fin j → (W' ⟶ W)}
    {h' : Y' ⟶ W'} {h : Y ⟶ W} (e' : ∀ a, φ' a = h' ≫ ψ' a) (e : ∀ i, h' ≫ σ i = ρ i ≫ h)
    (s' : LB.Sec (LB.LinComb M' φ' ε)) (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (t' : LB.Sec (LB.LinComb M' ψ' ε)) (t : ∀ i, LB.Sec (LB.LinComb M (ψ i) ε))
    (Hs : ∀ (y : Y') J J', Good M y J → Good M' y J' →
      (∏ a, bw w (𝟙 Y' ≫ φ' a) y (fun i => J ((𝟙 Y' ≫ φ' a) ≫ pr i)) (J' (𝟙 Y' ≫ φ' a)) ^ ε a).val *
        sval s' (𝟙 Y') y J' = ∏ i, sval (s i) (𝟙 Y' ≫ ρ i) y J)
    (Ht : ∀ (y : Y') J J', Good M y J → Good M' y J' →
      (∏ a, bw w (h' ≫ ψ' a) y (fun i => J ((h' ≫ ψ' a) ≫ pr i)) (J' (h' ≫ ψ' a)) ^ ε a).val *
        sval t' h' y J' = ∏ i, sval (t i) (h' ≫ σ i) y J)
    (c : Fin j → Γ(Y, ⊤)) (c' : Γ(Y', ⊤))
    (hc : ∀ y : Y', ∏ i, gs (𝟙 _ ≫ ρ i) y ⊤ (c i) = gs (𝟙 _) y ⊤ c')
    (H : ∀ i, GeneratorPullback.SecScal M (φ i) ε (s i) (ψ i) ε (t i) h (c i)) :
    GeneratorPullback.SecScal M' φ' ε s' ψ' ε t' h' c' := by
  apply secScal_of_pointwise hM'
  intro y J' hJ'
  obtain ⟨J, hJ, -⟩ := exists_good M hM y (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)
  have hs := Hs y J J' hJ hJ'
  have ht := Ht y J J' hJ hJ'
  have hci := hc y
  have hH : ∀ i, sval (t i) (h' ≫ σ i) y J = gs (𝟙 Y' ≫ ρ i) y ⊤ (c i) * sval (s i) (𝟙 Y' ≫ ρ i) y J :=
    fun i => by rw [← sval_of_secScal (H i) (𝟙 Y' ≫ ρ i) y hJ, Category.id_comp, ← e i]
  simp only [Category.id_comp] at hs hH hci ⊢
  simp only [← e'] at ht
  refine (Units.isUnit (∏ a, bw w (φ' a) y (fun i => J (φ' a ≫ pr i)) (J' (φ' a)) ^ ε a)).mul_left_cancel ?_
  rw [ht, Finset.prod_congr rfl (fun i _ => hH i), Finset.prod_mul_distrib, hci, ← hs, mul_left_comm]

end Generic



theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (pD : IsPowDeg D'.toPre D.toPre j) (k : ℕ) (Fs : Fin j → Fam D.toPre (FractionRing R) k) (f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α) (r : Fin j → R), (∀ i α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((Fs i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom (r i))) → ∀ (F' : Fam D'.toPre (FractionRing R) k), IsBoxFam pD (FractionRing R) k F' Fs → ∀ α' : D'.toPre.X, GeneratorPullback.SecScal D'.toPre.P.L (DegPre.famφ D'.toPre (FractionRing R) α') (DegPre.famε k) (F'.s α') (D'.toPre.famφB α') (DegPre.famε k) (boxFamB pD k f α') (DegPre.prB D'.toPre (FractionRing R)).left (scal (DegPre.BF D'.toPre (FractionRing R)).hom (∏ i, r i)) := by
  intro R _ _ I j D D' pD k Fs f r hF F' hB α'
  have e1 : ∀ i, (D'.toPre.prB (FractionRing R)).left ≫ (pD.pw.pr i).left =
      prB pD (FractionRing R) i ≫ (D.toPre.prB (FractionRing R)).left := by
    intro i
    unfold prB DegPre.prB
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have e2 : ∀ i, prB pD (FractionRing R) i ≫ (D.toPre.BF (FractionRing R)).hom =
      (D'.toPre.BF (FractionRing R)).hom := fun i => Over.w (TF (FractionRing R) ◁ pD.pw.pr i)
  obtain ⟨hφ, hBα⟩ := hB α'
  obtain ⟨hφB, hBB⟩ := isBoxFamB_boxFamB pD k f α'
  exact secScal_box D.toPre.P.isLB D'.toPre.P.isLB pD.w
    (ρ := fun i => prB pD (FractionRing R) i) (σ := fun i => (pD.pw.pr i).left)
    (h' := (D'.toPre.prB (FractionRing R)).left) (h := (D.toPre.prB (FractionRing R)).left)
    (fun a => GC.famφ_eq D'.toPre (FractionRing R) α' a) e1
    (F'.s α') (fun i => (Fs i).s (pD.xe α' i)) (boxFamB pD k f α') (fun i => f i (pD.xe α' i))
    (fun y J J' hJ hJ' => box_sval pD.w hφ (F'.s α') _
      (fun jN _ i => inf_le_left.trans (box_le_of_comp _ _ _ _ _ i (hφ i) jN)) hBα (𝟙 _) y hJ hJ')
    (fun y J J' hJ hJ' => box_sval pD.w hφB (boxFamB pD k f α') _
      (fun jN _ i => inf_le_left.trans (box_le_of_comp _ _ _ _ _ i (hφB i) jN)) hBB _ y hJ hJ')
    (fun i => scal (D.toPre.BF (FractionRing R)).hom (r i)) _
    (fun y => gs_scal_prod _ _ _ e2 y r)
    (fun i => hF i (pD.xe α' i))

end GlobalTheory.BoxFamScalar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TrivLevel

theorem level_dvd_badN (D : D7) {p : ℕ} (hp : p ∈ D.host.levelPrimes) : p ∣ badN D :=
  dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hp) _

theorem badN_pos_iff (D : D7) : 0 < badN D ↔ 0 ∉ D.host.levelPrimes := by
  have h := D.host.qd_big
  constructor
  · intro hb h0
    exact hb.ne' (Nat.eq_zero_of_zero_dvd (level_dvd_badN D h0))
  · intro h0
    unfold badN
    refine Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos (by omega)) (by omega)) (Finset.prod_pos fun p hp => ?_)
    exact Nat.pos_of_ne_zero fun e => h0 (e ▸ hp)

end GlobalTheory.TrivLevel
end
