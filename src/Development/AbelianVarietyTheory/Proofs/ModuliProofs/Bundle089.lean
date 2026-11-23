module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle074
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TorusTorsion

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}

theorem val_unitGen {X Y Z : Scheme.{0}} {L : LB X} (u : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) :
    val (GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen L u) r z J = gm r z ⊤ u :=
  gm_res _ z le_top (hJ.mem PEmpty.elim _) _

theorem isGen_unitGen {X Y : Scheme.{0}} (L : LB X) (u : Γ(Y, ⊤)ˣ) : (GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen L u).IsGen :=
  fun i j => by
    obtain rfl : i = j := funext fun k => k.elim
    exact ((congrArg₂ (· * ·) (Fintype.prod_empty _) rfl).trans (_root_.one_mul _)).symm

theorem TorusVal.val_eq {g : GtPt D T} {χ : D.X} {u : Γ(T.left, ⊤)ˣ} (h : TorusVal g χ u) {Z : Scheme.{0}}
    (r : Z ⟶ T.left) {z : Z} {J} (hJ : Good D.P.L z J) : val (g.s χ) r z J = gm r z ⊤ u :=
  (val_corr hJ h.2 r).trans (val_unitGen u r hJ)

theorem exists_torusPt (u : D.X →+ Additive Γ(T.left, ⊤)ˣ) :
    ∃ g : GtPt D T, ∀ χ, TorusVal g χ (Additive.toMul (u χ)) := by
  obtain ⟨g, hb, hv⟩ := exists_pt (D := D) (T := T) 1 (K := PEmpty) (φ := fun _ => PEmpty.elim) (ε := PEmpty.elim)
    (fun χ => GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen D.P.L (Additive.toMul (u χ))) (fun χ => isGen_unitGen _ _)
    (fun χ U i h => (GlobalTheory.FieldRestrictionTest.formEq_zero (D := D) (T := T) χ U h).symm)
    (fun y J hJ => by rw [val_unitGen _ _ hJ, map_zero, toMul_zero, map_one]) (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [C.face₃, val_unitGen _ _ hJ, val_unitGen _ _ hJ, val_unitGen _ _ hJ, map_add (f := _), toMul_add, map_mul,
        _root_.mul_one])
  exact ⟨g, fun χ => ⟨hb, corr_of_val D.P.isLB fun y J hJ => hv χ _ _ y J hJ⟩⟩

theorem isZero_iff' (g : GtPt D T) : g.IsZero ↔ g.b = 1 ∧ ∀ χ y J, Good D.P.L y J → cv g χ y J = 1 :=
  and_congr Iff.rfl (forall_congr' fun _ => ⟨fun h _ _ hJ => (val_corr hJ h _).trans (val_one _),
    fun h => corr_of_val D.P.isLB fun y J hJ => (h y J hJ).trans (val_one _).symm⟩)

theorem exists_nsmul_zero (k : ℕ) (u : D.X →+ Additive Γ(T.left, ⊤)ˣ) (hu : k • u = 0) {g : GtPt D T}
    (hg : ∀ χ, TorusVal g χ (Additive.toMul (u χ))) : ∃ h : GtPt D T, GtPt.IsNsmul k g h ∧ h.IsZero := by
  choose gs hgs using fun i : ℕ => exists_torusPt (D := D) (T := T) (i • u)
  have z : ∀ i : ℕ, i • u = 0 → (gs i).IsZero := fun i hi => (isZero_iff' _).2 ⟨(hgs i 0).1, fun χ y J hJ => by
    have := TorusVal.val_eq (hgs i χ) (𝟙 _) hJ
    rw [hi] at this
    exact this.trans (map_one _)⟩
  refine ⟨gs k, ⟨fun i => gs i, z 0 (zero_smul _ _), fun i => (TorusModel.isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩,
    rfl⟩, z k hu⟩
  · rw [(hgs _ 0).1, (hgs _ 0).1, (hg 0).1]
    exact (_root_.mul_one (1 : T ⟶ D.P.A)).symm
  · have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
    have hb : g.b = 1 := (hg 0).1
    rw [show th D y J (cP D _ χ) (gs (i.castSucc : Fin (k + 1))).b g.b = 1 by rw [hb, C.face₃], _root_.mul_one]
    refine (TorusVal.val_eq (hgs _ χ) _ hJ).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (TorusVal.val_eq (hgs _ χ) _ hJ) (TorusVal.val_eq (hg χ) _ hJ)).symm)
    rw [Fin.val_succ, Fin.val_castSucc, succ_nsmul, AddMonoidHom.add_apply, toMul_add, map_mul]

theorem isPull_of_units (h : T' ⟶ T) {g : GtPt D T} {g' : GtPt D T'} {u : D.X → Γ(T.left, ⊤)ˣ}
    {u' : D.X → Γ(T'.left, ⊤)ˣ} (hg : ∀ χ, TorusVal g χ (u χ)) (hg' : ∀ χ, TorusVal g' χ (u' χ))
    (e : ∀ χ, h.left.appTop.hom (u χ).val = (u' χ).val) : GtPt.IsPull h.left g g' := by
  refine (TorusModel.isPull_iff h g g').2 ⟨?_, fun χ y J hJ => ?_⟩
  · rw [(hg 0).1, (hg' 0).1]
    exact (MonObj.comp_one h).symm
  · refine (TorusVal.val_eq (hg' χ) _ hJ).trans (Eq.trans (Units.ext ?_) (TorusVal.val_eq (hg χ) _ hJ).symm)
    rw [gm_val _ y ⊤ trivial, gm_val _ y ⊤ trivial, ← e χ]
    rfl

variable {W : (Sp R).Opens}

end Points

end GlobalTheory.TorusTorsion
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.DlogPol

section Germs
variable {X Y Z : Scheme.{0}}

theorem gs_rsT (r : Z ⟶ Y) (z : Z) {O₀ O : Y.Opens} (h : O ≤ O₀) (hz : r z ∈ O) (s : Γ(Y, O₀)) :
    gs r z O (rsT s O) = gs r z O₀ s := by
  rw [rsT, dif_pos h]
  exact gs_res r z h hz s

theorem gs_pbT (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) {O₀ : X.Opens} {O : Y.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (hz : r z ∈ O)
    (s : Γ(X, O₀)) : gs r z O (pbT f s O) = gs (r ≫ f) z O₀ s := by
  rw [pbT, dif_pos h]
  exact (gs_res r z h hz ((f.app O₀).hom s)).trans (gs_pull r f z O₀ (h hz) s)

theorem gs_one (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) : gs r z O 1 = 1 := by
  simp only [gs_eq r z O hz, map_one]

theorem gs_sub (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) (a b : Γ(Y, O)) :
    gs r z O (a - b) = gs r z O a - gs r z O b := by
  simp only [gs_eq r z O hz, map_sub]

theorem gs_constFn {R : Type} [CommRing R] (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) (a : R) :
    gs r z O (constFn p O a) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) :=
  (gs_res r z (show O ≤ p ⁻¹ᵁ ⊤ from fun _ _ => trivial) hz ((p.app ⊤).hom _)).trans (gs_pull r p z ⊤ trivial _)

theorem eps_sq {K : Type} [Field K] (p : X ⟶ Sp (DualNumber K)) (U : X.Opens) :
    constFn p U DualNumber.eps * constFn p U DualNumber.eps = 0 := by
  unfold constFn
  rw [← map_mul, ← map_mul, DualNumber.eps_mul_eps, map_zero, map_zero]

end Germs

theorem exists_gen {K : Type} [Field K] {X Y Y' : Scheme.{0}} (π : Y' ⟶ Sp (DualNumber K)) (τ ρ : Y' ⟶ Y)
    (hτ : ∀ (y : Y') (W : Y.Opens), τ y ∈ W → ρ y ∈ W) (m : Y ⟶ X) (L : LB X) (hL : L.IsLB)
    (k : C1 (fun i => m ⁻¹ᵁ L.U i))
    (hk : ∀ i j (y : Y'), m (τ y) ∈ L.U i → m (τ y) ∈ L.U j →
      gs (τ ≫ m) y _ (L.g i j).val = gs (ρ ≫ m) y _ (L.g i j).val *
        (1 + gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom DualNumber.eps) *
          gs ρ y _ (k i j)))
    (hc : IsCob _ k) :
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) (fun n => ![τ, ρ] n ≫ m) ![1, -1]), t.IsGen := by
  obtain ⟨b, hb⟩ := hc
  let φ : Fin 2 → (Y' ⟶ X) := fun n => ![τ, ρ] n ≫ m
  have h₀ : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (τ y) ∈ L.U (J 0) := fun J y hy =>
    Set.mem_iInter.1 hy 0
  have h₀' : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (ρ y) ∈ L.U (J 0) := fun J y hy =>
    hτ y (m ⁻¹ᵁ L.U (J 0)) (h₀ J y hy)
  have h₁ : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (ρ y) ∈ L.U (J 1) := fun J y hy =>
    Set.mem_iInter.1 hy 1
  have le : ∀ J : Fin 2 → L.ι, LB.wchart L φ J ≤ (ρ ≫ m) ⁻¹ᵁ (L.U (J 0) ⊓ L.U (J 1)) := fun J y hy =>
    ⟨h₀' J y hy, h₁ J y hy⟩
  let u : ∀ J : Fin 2 → L.ι, Γ(Y', LB.wchart L φ J)ˣ := fun J =>
    ⟨1 - constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _, 1 + constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _,
      by linear_combination (-(pbT ρ (b (J 0)) (LB.wchart L φ J)) ^ 2) * eps_sq π (LB.wchart L φ J),
      by linear_combination (-(pbT ρ (b (J 0)) (LB.wchart L φ J)) ^ 2) * eps_sq π (LB.wchart L φ J)⟩
  refine ⟨⟨fun J => res (le J) (pullU (ρ ≫ m) _ (L.g (J 0) (J 1))) * u J⟩, isGen_of_gm _ fun y J J' hJ hJ' => ?_⟩
  set e := gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom DualNumber.eps) with he
  have ee : e * e = 0 := by
    rw [he, ← gs_mul π y ⊤ trivial, ← map_mul, DualNumber.eps_mul_eps, map_zero, gs_eq π y ⊤ trivial, map_zero, map_zero]
  have val : ∀ J : Fin 2 → L.ι, y ∈ LB.wchart L φ J →
      (gm (𝟙 Y') y (LB.wchart L φ J) (res (le J) (pullU (ρ ≫ m) _ (L.g (J 0) (J 1))) * u J)).val =
        (gm (ρ ≫ m) y _ (L.g (J 0) (J 1))).val * (1 - e * gs ρ y _ (b (J 0))) := fun J hJ => by
    rw [map_mul, Units.val_mul, gm_res (𝟙 Y') y (le J) hJ, gm_pull (𝟙 Y') (ρ ≫ m) y _ (le J hJ), Category.id_comp,
      ← gs_unit (𝟙 Y') y _ hJ]
    congr 1
    change gs (𝟙 Y') y _ (1 - constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _) = _
    rw [gs_sub _ _ _ hJ, gs_one _ _ _ hJ, gs_mul _ _ _ hJ, gs_constFn _ _ _ _ hJ,
      gs_pbT (𝟙 Y') ρ y (O₀ := m ⁻¹ᵁ L.U (J 0)) (fun y hy => h₀' J y hy) hJ, Category.id_comp, Category.id_comp]
  have tr : trF φ ![1, -1] (𝟙 Y') y J J' =
      gm (τ ≫ m) y _ (L.g (J 0) (J' 0)) * (gm (ρ ≫ m) y _ (L.g (J 1) (J' 1)))⁻¹ := by
    rw [trF, Fin.prod_univ_two]
    simp only [Category.id_comp]
    simp [φ]
  have c₁ := gm_cocycle hL (ρ ≫ m) y (h₀' J y hJ) (h₀' J' y hJ') (h₁ J' y hJ')
  have c₂ := gm_cocycle hL (ρ ≫ m) y (h₀' J y hJ) (h₁ J y hJ) (h₁ J' y hJ')
  have k₁ := hk _ _ y (h₀ J y hJ) (h₀ J' y hJ')
  have m₀ : ρ y ∈ m ⁻¹ᵁ L.U (J 0) ⊓ m ⁻¹ᵁ L.U (J' 0) := ⟨h₀' J y hJ, h₀' J' y hJ'⟩
  rw [hb, gs_sub _ _ _ m₀, gs_rsT _ _ inf_le_right m₀, gs_rsT _ _ inf_le_left m₀,
    gs_unit (τ ≫ m) y (L.U (J 0) ⊓ L.U (J' 0)) ⟨h₀ J y hJ, h₀ J' y hJ'⟩, gs_unit (ρ ≫ m) y (L.U (J 0) ⊓ L.U (J' 0)) m₀, ← he] at k₁
  change gm (𝟙 Y') y (LB.wchart L φ J) _ = trF φ ![1, -1] (𝟙 Y') y J J' * gm (𝟙 Y') y (LB.wchart L φ J') _
  rw [tr, _root_.mul_assoc, mul_left_comm, eq_inv_mul_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val J hJ, val J' hJ', k₁]
  have d := congrArg Units.val (c₁.trans c₂.symm)
  rw [Units.val_mul, Units.val_mul] at d
  linear_combination (-(1 - e * gs ρ y _ (b (J 0)))) * d +
    ((gm (ρ ≫ m) y _ (L.g (J 0) (J' 0))).val * (gm (ρ ≫ m) y _ (L.g (J' 0) (J' 1))).val *
      (gs ρ y _ (b (J' 0)) - gs ρ y _ (b (J 0))) * gs ρ y _ (b (J' 0))) * ee

theorem isUnit_pbT {X Y : Scheme.{0}} (m : Y ⟶ X) (L : LB X) (i j : L.ι) :
    IsUnit (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j)) := by
  rw [pbT, dif_pos (show m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j ≤ m ⁻¹ᵁ (L.U i ⊓ L.U j) from fun _ h => h)]
  exact (L.g i j).isUnit.map _

theorem isCoc_dlog {X Y : Scheme.{0}} (m : Y ⟶ X) (L : LB X) (hL : L.IsLB)
    (d : ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)) (hmul : ∀ W f f', d W (f * f') = f * d W f' + f' * d W f)
    (hres : ∀ W W' (f : Γ(Y, W)), W' ≤ W → d W' (rsT f W') = rsT (d W f) W')
    (φ : C1 (fun i => m ⁻¹ᵁ L.U i))
    (hφ : ∀ i j, pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) * φ i j =
      d _ (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j))) : IsCoc _ φ := by
  intro i j k
  set O : Y.Opens := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U k with hO
  let G : L.ι → L.ι → Γ(Y, O) := fun a b => rsT (pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b)) O
  have hd : ∀ a b, O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b → d O (G a b) = G a b * rsT (φ a b) O := fun a b h => by
    rw [hres _ _ _ h, ← hφ]
    simp only [G, rsT, dif_pos h, map_mul]
  have hg : ∀ a b, O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b → ∀ y ∈ O,
      gs (𝟙 Y) y O (G a b) = (gm m y _ (L.g a b)).val := fun a b h y hy => by
    rw [gs_rsT _ _ h hy, gs_pbT (𝟙 Y) m y (O₀ := L.U a ⊓ L.U b) (O := m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) (fun _ h => h) (h hy), Category.id_comp,
      gs_unit m y (L.U a ⊓ L.U b) (h hy)]
  have l₁ : O ≤ m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j := inf_le_left
  have l₂ : O ≤ m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U k := fun _ h => ⟨h.1.2, h.2⟩
  have l₃ : O ≤ m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U k := fun _ h => ⟨h.1.1, h.2⟩
  have co : G i j * G j k = G i k := fn_ext fun y hy => by
    rw [gs_mul _ _ _ hy, hg _ _ l₁ y hy, hg _ _ l₂ y hy, hg _ _ l₃ y hy, ← Units.val_mul,
      gm_cocycle hL m y hy.1.1 hy.1.2 hy.2]
  have un : IsUnit (G i k) := by
    simp only [G, rsT, dif_pos l₃]
    exact (isUnit_pbT m L i k).map _
  have e := hmul O (G i j) (G j k)
  rw [co, hd _ _ l₁, hd _ _ l₂, hd _ _ l₃] at e
  refine un.mul_left_cancel ?_
  change G i k * (rsT (φ i j) O + rsT (φ j k) O) = G i k * rsT (φ i k) O
  linear_combination (-1 : Γ(Y, O)) * e - (rsT (φ i j) O + rsT (φ j k) O) * co

theorem preimage_transl {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (w : epsR K ⟶ A) (hw : IsTangent w)
    (W : A.left.Opens) :
    ((fst (epsR K) A ≫ w) * snd (epsR K) A).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W := by
  let z : 𝟙_ (Over (Sp K)) ⟶ epsR K := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)
  have hz : z ≫ w = η[A] := Over.OverMorphism.ext hw
  let j : A ⟶ epsR K ⊗ A := lift (toUnit A ≫ z) (𝟙 A)
  have j₁ : j ≫ snd (epsR K) A = 𝟙 A := lift_snd _ _
  have j₂ : j ≫ ((fst (epsR K) A ≫ w) * snd (epsR K) A) = 𝟙 A := by
    rw [MonObj.comp_mul, j₁, lift_fst_assoc, Category.assoc, hz, ← Hom.one_def, _root_.one_mul]
  have j₃ : j.left ≫ (fst (epsR K) A).left = A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
    have := congrArg (fun q => q.left) (lift_fst (toUnit A ≫ z) (𝟙 A))
    refine this.trans ?_
    change (toUnit A).left ≫ _ = _
    congr 1
  have h := (GlobalTheory.ConstThickening.structure_dualNumber K A.left (epsR K ⊗ A).left A.hom (fst (epsR K) A).left (snd (epsR K) A).left j.left
    (IsPullback.of_hasPullback (epsR K).hom A.hom).flip (congrArg (fun q => q.left) j₁) j₃).1
    (((fst (epsR K) A ≫ w) * snd (epsR K) A).left ⁻¹ᵁ W)
  rw [← h, ← Scheme.Hom.comp_preimage j.left, ← Over.comp_left, j₂]
  rfl

theorem dlog_independent : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X), L.IsLB → LBIso P₀.L (L.pull m) → (∃ φ, IsDlog m L dd φ) ∧ ∀ φ, IsDlog m L dd φ → (∀ a, IsCoc _ (φ a)) ∧ ∀ c, IsCob _ (lc P₀.A.hom c φ) → c = 0 := by
  intro K _ P g v dd hv hdd X m L hL ⟨u, hu⟩
  refine ⟨⟨fun a i j => ((isUnit_pbT m L i j).unit⁻¹ : _ˣ).val * dd a _ (pbT m (L.g i j).val _), fun a i j => ?_⟩,
    fun φ hφ => ⟨fun a => ?_, fun c hc => ?_⟩⟩
  · rw [← _root_.mul_assoc, IsUnit.mul_val_inv, _root_.one_mul]
  · obtain ⟨-, h₁, h₂, -⟩ := (GlobalTheory.KS.InvField.main K P.A (v a) (hv.1 a)).2 _ (hdd a)
    exact isCoc_dlog m L hL (dd a) h₁ h₂ (φ a) (hφ a)
  have := P.isAb.comm
  obtain ⟨a₁, a₂, a₃, -⟩ := GlobalTheory.LieComb.lieComb_algebra K P.A g v hv.1
  obtain ⟨w, hw, -⟩ := a₁ c
  have tw := a₂ c w hw
  obtain ⟨dw, hdw⟩ := (GlobalTheory.KS.InvField.main K P.A w tw).1
  have hsum : ∀ (W : P.A.left.Opens) (h : Γ(P.A.left, W)), dw W h = ∑ a, constFn P.A.hom _ (c a) * dd a W h :=
    GlobalTheory.KS.InvHom.invDer_along_hom K P.A P.A (𝟙 _) g v dd w dw c inferInstance hv.1 tw hdd hdw (by rwa [Category.comp_id])
  have pre := preimage_transl w tw
  set τ := ((fst (epsR K) P.A ≫ w) * snd (epsR K) P.A).left with hτ
  set ρ := (snd (epsR K) P.A).left with hρ
  obtain ⟨t, ht⟩ := exists_gen (fst (epsR K) P.A).left τ ρ (fun y W hy => (pre W).le hy) m L hL _ (fun i j y hi hj => by
    have hy : y ∈ ρ ⁻¹ᵁ (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) := (pre _).le ⟨hi, hj⟩
    have e := congrArg (gs (𝟙 _) y _) (hdw (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (pbT m (L.g i j).val _))
    have e₂ : dw _ (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j)) =
        pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) * lc P.A.hom c φ i j := by
      rw [hsum, lc, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [← hφ a i j, mul_left_comm]
    rw [e₂, gs_add _ _ _ hy, gs_mul _ _ _ hy, gs_constFn _ _ _ _ hy, gs_pbT _ _ _ (pre _).ge hy,
      gs_pbT _ _ _ le_rfl hy, gs_pbT _ _ _ le_rfl hy, Category.id_comp, Category.id_comp, Category.id_comp,
      gs_mul _ _ _ hy, gs_pbT _ m y (O₀ := L.U i ⊓ L.U j) (O := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (fun _ h => h) ⟨hi, hj⟩,
      gs_pbT _ m y (O₀ := L.U i ⊓ L.U j) (O := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (fun _ h => h) hy] at e
    refine e.trans ?_
    ring) hc
  obtain ⟨s, hs⟩ := exists_down ((isGen_iff u).1 hu) hL P.isLB t ht
  have w1 : w = 1 := P.ktriv (DualNumber K) _ w fun p =>
    ⟨⊤, trivial, gen_chartPull (chartPullPull (Out.translDiff P.A P.L w) _ _ rfl) s hs⟩
  have h0 : IsLieComb 0 v w := by
    have := a₃ 0 Fin.elim0 Fin.elim0 Fin.elim0 w (fun i => i.elim0) ⟨Fin.elim0, fun i => i.elim0, by rw [w1]; rfl⟩
    simpa using this
  exact (hv.2 w tw).unique hw h0

end GlobalTheory.KS.DlogPol
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem GlobalTheory.exists_isPEL_of_tmap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (τ : SAB H S) (f : S' ⟶ S), f ≫ s = s' → TMap t' t f → IsPEL D a bas ρ t τ → ∃ τ' : SAB H S', IsPEL D a bas ρ t' τ' := by
  intro E _ _ _ H D g J a bas k o _ b ρ S S' s s' t t' τ f hs ht hP

  exact GlobalTheory.PELPull.isPEL_pull E H D g k J a bas o b ρ S S' s s' f t t' τ hs ht hP
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Uniq

section
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

theorem ex_add_lattice (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem mem_dom_add_lattice (m : A₀.left ⟶ X) (W : X.Opens) (z : Fin g → ℂ) (l : u.Λ) :
    z + l ∈ dom u m W ↔ z ∈ dom u m W := by
  show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ W ↔ ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W
  rw [ex_add_lattice]

theorem fderiv_fn_add_lattice (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) (z : Fin g → ℂ) (l : u.Λ) :
    fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fn u m W f) z := by
  have h : (fun w => fn u m W f (w + (l : Fin g → ℂ))) = fn u m W f := by
    funext w
    unfold fn
    rw [ex_add_lattice]
  calc fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fun w => fn u m W f (w + (l : Fin g → ℂ))) z :=
        (fderiv_comp_add_right (l : Fin g → ℂ)).symm
    _ = fderiv ℂ (fn u m W f) z := by rw [h]

theorem ptDer_sub {y : Sp ℂ ⟶ X} {δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W f => δ W f - δ' W f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro W hW f f'
    rw [h.add W hW f f', h'.add W hW f f']
    ring
  · intro W hW f f'
    rw [h.mul W hW f f', h'.mul W hW f f']
    ring
  · intro W W' hle hW' f
    rw [h.res W W' hle hW' f, h'.res W W' hle hW' f]
end

theorem ks_unique : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ Θ' s s', KSRel u p m D Θ s → KSRel u p m D Θ' s' → Θ = Θ' := by
  intro P₀ u Hm χ hG R _ x₀ X p m hp hpb D Θ Θ' s s' hs hs'
  obtain ⟨w, hwd, hw⟩ := GlobalTheory.T.exists_differentiableOn_verticalVectorField P₀ u Hm χ hG R x₀ X p m hp hpb P₀.g Set.univ id
    (fun z W f => s z W f - s' z W f) isOpen_univ differentiable_id
    (fun z _ => ⟨ptDer_sub (hs.der z) (hs'.der z), fun r => by
      show s z ⊤ (constFn p ⊤ r) - s' z ⊤ (constFn p ⊤ r) = 0
      rw [hs.base, hs'.base, sub_self]⟩)
    (fun W f => ((hs.hol W f).sub (hs'.hol W f)).mono fun z hz => hz.2)
  have hw' : ∀ z W f, z ∈ dom u m W → s z W f - s' z W f = fderiv ℂ (fn u m W f) z (w z) :=
    fun z W f hz => hw z (Set.mem_univ z) W f hz
  have hper : ∀ (l : u.Λ) z, w (z + l) = w z + (Θ - Θ').mulVec (star (l : Fin P₀.g → ℂ)) := by
    intro l z
    obtain ⟨v, -, huniq⟩ := GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hG R x₀ X p m hp hpb z
      (fun W f => s z W f - s' z W f) (ptDer_sub (hs.der z) (hs'.der z)) (fun r => by
        show s z ⊤ (constFn p ⊤ r) - s' z ⊤ (constFn p ⊤ r) = 0
        rw [hs.base, hs'.base, sub_self])
    have e1 := huniq (w z) (fun W f hz => hw' z W f hz)
    have e2 := huniq (w (z + l) - (Θ - Θ').mulVec (star (l : Fin P₀.g → ℂ))) (fun W f hz => by
      have a1 := hw' (z + l) W f ((mem_dom_add_lattice u m W z l).2 hz)
      have a2 := hs.per l W f z hz
      have a3 := hs'.per l W f z hz
      rw [fderiv_fn_add_lattice] at a1
      show s z W f - s' z W f = _
      rw [map_sub, Matrix.sub_mulVec, map_sub]
      linear_combination a1 - a2 + a3)
    rw [← e1] at e2
    exact sub_eq_iff_eq_add.mp e2
  have hdisc : DiscreteTopology u.Λ := u.discrete
  have hspan : Submodule.span ℝ (u.Λ : Set (Fin P₀.g → ℂ)) = ⊤ := u.full
  have hwd' : Differentiable ℂ w := differentiableOn_univ.mp hwd
  ext i j
  have key := GlobalTheory.entire_antilinear_periods_const P₀.g u.Λ hdisc hspan (fun z => w z i) ((Θ - Θ') i)
    (differentiable_pi.mp hwd' i) (fun l z => congrFun (hper l z) i)
  have hij := congrFun key.1 j
  simp only [Matrix.sub_apply, Pi.zero_apply, sub_eq_zero] at hij
  exact hij

end GlobalTheory.KS.Uniq
end

section

noncomputable section

namespace GlobalTheory.CoveringCompare

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Fibres

def SplitOver {S : Scheme.{0}} (G : Over S) [GrpObj G] (x : S) (k : Type) [Field k] [Algebra (S.residueField x) k] :
    Prop :=
  ∃ T : SplitExt (Sp k), T.IsGt ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) k)) ≫ S.fromSpecResidueField x)).obj G)

theorem splitOver_of_torusExtension {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) (k : Type)
    [Field k] [Algebra (S.residueField x) k]
    (h : Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap (S.residueField x) k))).obj
      ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)))) :
    SplitOver G x k := by
  obtain ⟨T⟩ := h
  obtain ⟨i, hi, -⟩ := grpPullback_iso
    ((isGrpPullback_pullback ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)
      (spMap (algebraMap (S.residueField x) k))).comp (isGrpPullback_pullback G _))
    (isGrpPullback_pullback G _)
  have := hG.comm
  exact exists_splitExt_isGt_of_torusExtension _ _ ⟨torusExtOfIso i T⟩

theorem exists_finite_splitOver {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (S.residueField x) k),
      FiniteDimensional (S.residueField x) k ∧ SplitOver G x k := by
  have h₀ := IsSemiAbelian.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x) G hG
  have := h₀.smooth
  obtain ⟨k, hk, T⟩ := exists_finite_torusExtension (S.residueField x) (AlgebraicClosure (S.residueField x)) _
    inferInstance h₀.quasiCompact h₀.separated (h₀.fibres _ _)
  exact ⟨k, inferInstance, inferInstance, hk, splitOver_of_torusExtension G hG x k T⟩

end Fibres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section One

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end One

end GlobalTheory.CoveringCompare
end
end
