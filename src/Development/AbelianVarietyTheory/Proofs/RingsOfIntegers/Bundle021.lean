module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ChangeChart
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TripleProductPointCompProjection
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle019
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig

variable {B B' G G' T T' S S₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {p : T ⟶ B} {p' : T' ⟶ B'} {f : T ⟶ G} {f' : T' ⟶ G'}

theorem rig_box (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    (hwe : we.IsGen) (Q : BoxSquare w we we' h)
    (hF : ∀ i, h i ≫ f = f' ≫ prG i) (hE : ∀ i, p' ≫ pr i = h i ≫ p)
    {u : S ⟶ T} {u' : S ⟶ T'} {s : S ⟶ S₀} {eG : S₀ ⟶ G} {eA : S₀ ⟶ B} {eG' : S₀ ⟶ G'} {eA' : S₀ ⟶ B'}
    {rL : LB.Gen (L.pull eG)} (hrL : rL.IsGen) {rM : LB.Gen (M.pull eA)} {rM' : LB.Gen (M'.pull eA')}
    (H : RigAlong we u s rL rM) (hu : ∀ i, u' ≫ h i = u) (hf : u ≫ f = s ≫ eG) (hp : u ≫ p = s ≫ eA)
    (hp' : u' ≫ p' = s ≫ eA') (hG : ∀ (i : Fin j) (_ : PUnit), eG' ≫ prG i = 𝟙 S₀ ≫ eG)
    (b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => eA' ≫ pr i) (fun _ => 1)))
    (b₁ : GeneratorPullback.MapsAt M M' pr w eA' 1 rM' b)
    (b₂ : LB.Gen.Corr M _ _ _ _ b (GeneratorPullback.finProdGen M (J := Fin j) (fun _ _ => eA) (fun _ _ => 1) (fun _ => rM))) :
    RigAlong we' u' s (GeneratorPullback.boxGen L prG (fun _ : PUnit => eG') (fun _ => 1)
      (fun i => GeneratorPullback.pullAlong L (prG i) (𝟙 S₀) (fun _ => eG) (fun _ => 1) (fun _ => eG') (hG i) rL)) rM' := by
  rintro ⟨qM, qL⟩ V a₁ a₂ a₃
  refine unit_ext fun y hy => ?_
  have key := rel_box hM hM' hL hwe Q hF hE (K := PUnit) (ε := fun _ => 1) y (fun _ => u') hrL rM rM' s
    (fun _ => s) (fun _ => s) (fun i _ => by rw [hu, hf]) (fun _ => hp') (fun i _ => by rw [hu, hp])
    (fun J J' hJ hJ' => (congrArg₂ (· * ·) (Fintype.prod_unique _) rfl).trans
      ((mapsAt_val w eA' 1 rM' b b₁ s y hJ hJ').symm.trans ((val_corr hJ b₂ s).trans (val_finProd _ _ _ s y hJ))))
    (fun i J N hJ hN => by
      have e := H.stalk hf hp (𝟙 S) y (J (s ≫ eA)) (N (s ≫ eG)) ((pt_of_eq hp y).symm ▸ hJ (s ≫ eA))
        ((pt_of_eq hf y).symm ▸ hN (s ≫ eG))
      rw [Category.id_comp, Category.id_comp] at e
      rw [Fintype.prod_unique, zpow_one, hu]
      exact e.symm)
    qL qM (fun a b _ => congrArg qM (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 (a₃ hy) k)
    (fun k i => (pt_of_eq (hG i k) (s y)) ▸ Set.mem_iInter.1 (Set.mem_iInter.1 (a₂ hy) k) i)
  rw [Fintype.prod_unique, zpow_one] at key
  have e := gm_box_pull L prG (fun _ => 𝟙 S₀) hG (fun _ => rL) s y qL (a₂ hy)
  rw [Category.comp_id] at e
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res_pull _ u' y a₁ hy _)
    (gm_res_pull _ s y a₂ hy _)).trans (Eq.trans ?_ (gm_res_pull _ s y a₃ hy _).symm))
  rw [Category.id_comp, Category.id_comp]
  exact (congrArg₂ (· * ·) rfl e).trans key.symm

def EvenAlong (we : LB.Iso (L.pull f) (M.pull p)) (iT : T ⟶ T) {iG : G ⟶ G} {iB : B ⟶ B}
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]))
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])) : Prop :=
  ∀ (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι),
    LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS →
    LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT →
    ∀ (V : T.Opens) (h₁ : V ≤ p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT)
      (h₂ : V ≤ (M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1))
      (h₃ : V ≤ iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)))
      (h₄ : V ≤ f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS),
      res h₁ (pullU p _ (σ.s jT)) * res h₂ (we.s (fun _ => jT 1, fun _ => jS 1)) =
        res h₃ (pullU iT _ (we.s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU f _ (s.s jS))

theorem EvenAlong.stalk {we : LB.Iso (L.pull f) (M.pull p)} {iT : T ⟶ T} {iG : G ⟶ G} {iB : B ⟶ B}
    {s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1])}
    {σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])} (ev : EvenAlong we iT s σ)
    (iF : iT ≫ f = f ≫ iG) (iP : iT ≫ p = p ≫ iB) {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z)
    (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι) (cS : LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS)
    (cT : LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT)
    (hS : ∀ k, (![iG, 𝟙 G] : Fin 2 → (G ⟶ G)) k (f (r z)) ∈ L.U (jS k))
    (hT : ∀ k, (![iB, 𝟙 B] : Fin 2 → (B ⟶ B)) k (p (r z)) ∈ M.U (jT k)) :
    gm (r ≫ p) z (LB.wchart M (K := Fin 2) ![iB, 𝟙 B] jT) (σ.s jT) =
      (∏ k, Geo.Tor.gw we ((![r ≫ iT, r] : Fin 2 → _) k) z (jT k) (fun _ => jS k) ^ (![1, -1] : Fin 2 → ℤ) k) *
        gm (r ≫ f) z (LB.wchart L (K := Fin 2) ![iG, 𝟙 G] jS) (s.s jS) := by
  have S0 : f (iT (r z)) ∈ L.U (jS 0) := (pt_of_eq iF (r z)).symm ▸ hS 0
  have T0 : p (iT (r z)) ∈ M.U (jT 0) := (pt_of_eq iP (r z)).symm ▸ hT 0
  have S1 : f (r z) ∈ L.U (jS 1) := hS 1
  have T1 : p (r z) ∈ M.U (jT 1) := hT 1
  let W : T.Opens := p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT ⊓
    ((M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1)) ⊓
    iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)) ⊓
    f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS
  have hW : r z ∈ W := ⟨⟨⟨Set.mem_iInter.2 hT, mem_pull.2 T1, mem_pull.2 S1⟩, mem_pull.2 T0, mem_pull.2 S0⟩,
    Set.mem_iInter.2 hS⟩
  have l₁ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have l₂ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have l₃ : W ≤ _ := inf_le_left.trans inf_le_right
  have l₄ : W ≤ _ := inf_le_right
  obtain ⟨n₁, n₂⟩ := GlobalTheory.EvenPull.even_stalk we s σ jS jT W l₁ l₂ l₃ l₄ r z hW
  have E := n₁.symm.trans ((congrArg (gm r z W) (ev jS jT cS cT W l₁ l₂ l₃ l₄)).trans n₂)
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg]
  rw [← mul_right_comm, ← E, mul_inv_cancel_right]

theorem even_box (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    (hwe : we.IsGen) (Q : BoxSquare w we we' h)
    (hF : ∀ i, h i ≫ f = f' ≫ prG i) (hE : ∀ i, p' ≫ pr i = h i ≫ p)
    {iT : T ⟶ T} {iG : G ⟶ G} {iB : B ⟶ B} {iT' : T' ⟶ T'} {iG' : G' ⟶ G'} {iB' : B' ⟶ B'}
    (ih : ∀ i, iT' ≫ h i = h i ≫ iT) (iF : iT ≫ f = f ≫ iG) (iP : iT ≫ p = p ≫ iB) (iP' : iT' ≫ p' = p' ≫ iB')
    (hG : ∀ i k, (![iG', 𝟙 G'] : Fin 2 → _) k ≫ prG i = prG i ≫ (![iG, 𝟙 G] : Fin 2 → _) k)
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1])) (hs : s.IsGen)
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]))
    (σ' : LB.Gen (LB.LinComb M' (K := Fin 2) ![iB', 𝟙 B'] ![1, -1]))
    (hσ : ∀ (y : T') J J', Good M y J → Good M' y J' →
      om w y J J' (p' ≫ iB') * (om w y J J' p')⁻¹ * val σ' p' y J' = ∏ i, val σ (p' ≫ pr i) y J)
    (ev : EvenAlong we iT s σ) :
    EvenAlong we' iT' (GeneratorPullback.boxGen L prG _ _ (fun i => GeneratorPullback.pullAlong L (prG i) (prG i) _ _ _ (hG i) s)) σ' := by
  intro jS' jT' _ cT V h₁ h₂ h₃ h₄
  refine unit_ext fun z hz => ?_
  obtain ⟨k₁, k₂⟩ := GlobalTheory.EvenPull.even_stalk we'
    (GeneratorPullback.boxGen L prG _ _ (fun i => GeneratorPullback.pullAlong L (prG i) (prG i) _ _ _ (hG i) s)) σ' jS' jT' V h₁ h₂ h₃ h₄
    (𝟙 T') z hz
  refine k₁.trans (Eq.trans ?_ k₂.symm)
  clear k₁ k₂
  have c₀ : ∀ i k, (![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i = (![h i ≫ iT, h i] : Fin 2 → _) k :=
    fun i => Fin.forall_fin_two.2 ⟨ih i, Category.id_comp _⟩
  have c₁ : ∀ i k, ((![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i) ≫ f = (h i ≫ f) ≫ (![iG, 𝟙 G] : Fin 2 → _) k :=
    fun i => Fin.forall_fin_two.2 ⟨by
      show (iT' ≫ h i) ≫ f = (h i ≫ f) ≫ iG
      rw [ih, Category.assoc, iF, Category.assoc], by
      show (𝟙 T' ≫ h i) ≫ f = (h i ≫ f) ≫ 𝟙 G
      rw [Category.id_comp, Category.comp_id]⟩
  have c₃ : ∀ i k, ((![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i) ≫ p = (h i ≫ p) ≫ (![iB, 𝟙 B] : Fin 2 → _) k :=
    fun i => Fin.forall_fin_two.2 ⟨by
      show (iT' ≫ h i) ≫ p = (h i ≫ p) ≫ iB
      rw [ih, Category.assoc, iP, Category.assoc], by
      show (𝟙 T' ≫ h i) ≫ p = (h i ≫ p) ≫ 𝟙 B
      rw [Category.id_comp, Category.comp_id]⟩
  have mL : ∀ k i, (![iG, 𝟙 G] : Fin 2 → (G ⟶ G)) k ((h i ≫ f) z) ∈ L.U (jS' k i) := fun k i => by
    have a : ((f' ≫ (![iG', 𝟙 G'] : Fin 2 → (G' ⟶ G')) k) ≫ prG i) z ∈ L.U (jS' k i) :=
      Set.mem_iInter.1 (Set.mem_iInter.1 (h₄ hz) k) i
    rw [Category.assoc, hG, ← Category.assoc, ← hF] at a
    exact a
  have HM : ∀ J J', Good M z J → Good M' z J' →
      (∏ k, om w z J J' (p' ≫ (![iB', 𝟙 B'] : Fin 2 → _) k) ^ (![1, -1] : Fin 2 → ℤ) k) * val σ' p' z J' =
        ∏ i, val σ (h i ≫ p) z J := fun J J' hJ hJ' => by
    have e := hσ z J J' hJ hJ'
    simp only [hE] at e
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, zpow_one, zpow_neg]
    exact e
  have HU : ∀ i J N, Good M z J → Good L z N → val σ (h i ≫ p) z J =
      (∏ k, Geo.Tor.gw we ((![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i) z (J ((h i ≫ p) ≫ (![iB, 𝟙 B] : Fin 2 → _) k))
        (fun _ => N ((h i ≫ f) ≫ (![iG, 𝟙 G] : Fin 2 → _) k)) ^ (![1, -1] : Fin 2 → ℤ) k) * val s (h i ≫ f) z N :=
    fun i J N hJ hN => by
      simp only [c₀]
      exact ev.stalk iF iP (h i) z _ _
        (fun a b e => congrArg N ((Category.assoc _ _ _).trans ((congrArg (h i ≫ ·) e).trans
          (Category.assoc _ _ _).symm)))
        (fun a b e => congrArg J ((Category.assoc _ _ _).trans ((congrArg (h i ≫ ·) e).trans
          (Category.assoc _ _ _).symm)))
        (fun k => hN ((h i ≫ f) ≫ (![iG, 𝟙 G] : Fin 2 → _) k)) (fun k => hJ ((h i ≫ p) ≫ (![iB, 𝟙 B] : Fin 2 → _) k))
  have key := rel_box hM hM' hL hwe Q hF hE (K := Fin 2) (ε := ![1, -1]) z ![iT', 𝟙 T'] hs σ σ' p'
    (fun i => h i ≫ p) (fun i => h i ≫ f) c₁
    (Fin.forall_fin_two.2 ⟨iP', (Category.id_comp _).trans (Category.comp_id _).symm⟩) c₃ HM HU
    jS' jT' cT (fun k => Set.mem_iInter.1 (h₁ hz) k) mL
  have e := gm_box_pull L prG prG hG (fun _ => s) f' z jS' (h₄ hz)
  rw [Fin.prod_univ_two] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, hF] at key
  rw [Category.id_comp, Category.id_comp, Category.id_comp]
  refine Eq.trans ?_ (congrArg₂ (· * ·) rfl e).symm
  rw [key, mul_right_comm, inv_mul_cancel_right]

end GlobalTheory.PowUnif
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig GlobalTheory.WCub

theorem tri_map {S S' : Scheme.{0}} {G G' : Over S} (f : S' ⟶ S) {E E' T : Over S'} (p : (Over.map f).obj E ⟶ G)
    (p' : (Over.map f).obj E' ⟶ G') (x : Fin 3 → (T ⟶ E')) (ρ : E' ⟶ E) (π : G' ⟶ G)
    (h : p'.left ≫ π.left = ρ.left ≫ p.left) :
    (∀ a, ((Over.map f).map (x a) ≫ p') ≫ π = (Over.map f).map (x a ≫ ρ) ≫ p) ∧
      tri f p' x ≫ (π ⊗ₘ π ⊗ₘ π).left = tri f p (fun a => x a ≫ ρ) := by
  have e : ∀ a, ((Over.map f).map (x a) ≫ p') ≫ π = (Over.map f).map (x a ≫ ρ) ≫ p := fun a =>
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg ((x a).left ≫ ·) h).trans
      (Category.assoc _ _ _).symm))
  refine ⟨e, ?_⟩
  show (lift _ (lift _ _) ≫ (π ⊗ₘ π ⊗ₘ π)).left = _
  rw [lift_map, lift_map, e, e, e]

theorem psum_comp {S : Scheme.{0}} {E E' T : Over S} [GrpObj E] [IsCommMonObj E] [GrpObj E'] [IsCommMonObj E']
    (x : Fin 3 → (T ⟶ E')) (ρ : E' ⟶ E) [IsMonHom ρ] (k : Finset (Fin 3)) :
    (psum E' x k).left ≫ ρ.left = (psum E (fun a => x a ≫ ρ) k).left :=
  congrArg (fun z => z.left) (psum_hom (MonoidHom.mk' (fun z : T ⟶ E' => z ≫ ρ) fun a b => MonObj.mul_comp a b ρ) x k)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem w_cub_val (U : UnifPre I D A G) (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (x : Fin 3 → (T ⟶ thickObj R I e G)) (y : T.left) {J N} (hJ : Good D.toPre.P.L y J) (hN : Good U.LG.L y N) :
    val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (tri (thick R I e) (U.gt e).pG x) y J =
      (∏ k : thK, Geo.Tor.gw (U.w e) (psum (thickObj R I e G) x k.down).left y
        (J (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k))
        (fun _ => N (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k)) ^ thε k) *
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t (tri (thick R I e) (fstG I e G) x) y N := by
  have := (U.gt e).q_hom
  have f₃ := tri_thφ (thick R I e) (fstG I e G) x (𝟙 _) (Category.id_comp _).symm
  have f₄ := tri_thφ (thick R I e) (U.gt e).pG x (U.gt e).q rfl
  exact (clause_iff (tri (thick R I e) (U.gt e).pG x) (tri (thick R I e) (fstG I e G) x)
    (fun k : thK => (psum (thickObj R I e G) x k.down).left) _ _ _ (D.toPre.cub.t.s _) (U.cubG.t.s _)
    (fun k => (U.w e).s (fun _ => J (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k),
      fun _ => N (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k))) thε).1
    (U.w_cub e T x _ _ (fun a b e => congrArg N e) (fun a b e => congrArg J e)) y
    (hJ.mem _ _) (hN.mem _ _) (fun k => ⟨mem_pull.2 (pt_of_eq (f₄ k) y ▸
      hJ (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k)),
      mem_pull.2 (pt_of_eq (f₃ k) y ▸ hN (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k))⟩)

theorem cub_box_val (hG : GlobalFnsSt) (pD : IsPowDeg D'.toPre D.toPre j) (e : ℕ)
    {E E' T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (p : (Over.map (thick R I e)).obj E ⟶ D.toPre.P.A)
    (p' : (Over.map (thick R I e)).obj E' ⟶ D'.toPre.P.A) (x : Fin 3 → (T ⟶ E')) (ρ : Fin j → (E' ⟶ E))
    (h : ∀ i, p'.left ≫ (pD.pw.pr i).left = (ρ i).left ≫ p.left) (y : T.left) (J J')
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') :
    (∏ k : thK, om (pr := fun i => (pD.pw.pr i).left) pD.w y J J'
        (tri (thick R I e) p' x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ^ thε k) *
      val (L := D'.toPre.P.L) (φ := thφ D'.toPre.P.A (x3 D'.toPre.P.A)) (ε := thε) D'.toPre.cub.t
        (tri (thick R I e) p' x) y J' =
      ∏ i, val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (tri (thick R I e) p (fun a => x a ≫ ρ i)) y J := by
  have c := GlobalTheory.CubBox.cubV_box hG R j D.toPre D'.toPre pD ((Over.map (thick R I e)).obj T) y J J' hJ hJ'
    ((Over.map (thick R I e)).map (x 0) ≫ p') ((Over.map (thick R I e)).map (x 1) ≫ p')
    ((Over.map (thick R I e)).map (x 2) ≫ p')
  have q := prod_cub ((Over.map (thick R I e)).map (x 0) ≫ p') ((Over.map (thick R I e)).map (x 1) ≫ p')
    ((Over.map (thick R I e)).map (x 2) ≫ p') (om (pr := fun i => (pD.pw.pr i).left) pD.w y J J')
  refine (congrArg₂ (· * ·) q rfl).trans ((mul_comm _ _).trans (c.trans (Finset.prod_congr rfl fun i _ => ?_)))
  have t := (tri_map (thick R I e) p p' x (ρ i) (pD.pw.pr i) (h i)).1
  rw [t, t, t]
  rfl

theorem cub_box (hG : GlobalFnsSt) (pD : IsPowDeg D'.toPre D.toPre j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G)
    (e : ℕ) (g' : GtCoord I D'.toPre e G')
    (hq : ∀ i, g'.pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left)
    (w' : LB.Iso ((boxLB U.LG.L pG.pr).pull (fstG I e G').left) (D'.toPre.P.L.pull g'.pG.left))
    (Q : BoxSquare (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) pD.w (U.w e) w' (rhoE I pG e))
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : Fin 3 → (T ⟶ thickObj R I e G'))
    (jL : thK → Fin j → U.LG.L.ι) (jM : thK → D'.toPre.P.L.ι)
    (cM : LB.Coh D'.toPre.P.L (fun k => tri (thick R I e) g'.pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) jM)
    (y : T.left) (hB : tri (thick R I e) g'.pG x y ∈ LB.wchart D'.toPre.P.L (thφ D'.toPre.P.A (x3 D'.toPre.P.A)) jM)
    (hL : tri (thick R I e) (fstG I e G') x y ∈ LB.wchart (boxLB U.LG.L pG.pr) (thφ G' (x3 G')) jL) :
    gm (tri (thick R I e) g'.pG x) y (LB.wchart D'.toPre.P.L (thφ D'.toPre.P.A (x3 D'.toPre.P.A)) jM)
        (D'.toPre.cub.t.s jM) =
      (∏ k : thK, Geo.Tor.gw w' (psum (thickObj R I e G') x k.down).left y (jM k) (fun _ => jL k) ^ thε k) *
      gm (tri (thick R I e) (fstG I e G') x) y (LB.wchart (boxLB U.LG.L pG.pr) (thφ G' (x3 G')) jL)
        ((boxCub pG U.LG.L U.cubG.t).s jL) := by
  have := g'.q_hom
  have := (U.gt e).q_hom
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  let ρ : Fin j → (thickObj R I e G' ⟶ thickObj R I e G) := fun i => (Over.pullback (thick R I e)).map (pG.pr i)
  have ps : ∀ i (k : thK), (psum (thickObj R I e G') x k.down).left ≫ rhoE I pG e i =
      (psum (thickObj R I e G) (fun a => x a ≫ ρ i) k.down).left := fun i k => by
    have := pG.hom i
    exact psum_comp x (ρ i) k.down
  have f₂ := tri_thφ (thick R I e) g'.pG x g'.q rfl
  have f₃ := fun i => tri_thφ (thick R I e) (fstG I e G) (fun a => x a ≫ ρ i) (𝟙 _) (Category.id_comp _).symm
  have f₄ := fun i => tri_thφ (thick R I e) (U.gt e).pG (fun a => x a ≫ ρ i) (U.gt e).q rfl
  have hψ : ∀ i a, thφ G' (x3 G') a ≫ (pG.pr i).left = (pG.pr i ⊗ₘ pG.pr i ⊗ₘ pG.pr i).left ≫ thφ G (x3 G) a :=
    fun i a => letI := pG.hom i; (CubeMap.ofHom (pG.pr i)).psum_comm a.down
  have t := fun i => (tri_map (thick R I e) (fstG I e G) (fstG I e G') x (ρ i) (pG.pr i) (hρ i).symm).2
  have key := rel_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D.toPre.P.isLB D'.toPre.P.isLB
    U.LG.isLB (U.w_gen e) Q hρ hq (K := thK) (ε := thε) y (fun k => (psum (thickObj R I e G') x k.down).left)
    (φ := thφ G (x3 G)) (ψ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ψ' := thφ D'.toPre.P.A (x3 D'.toPre.P.A))
    U.cubG.isGen D.toPre.cub.t D'.toPre.cub.t (tri (thick R I e) g'.pG x)
    (fun i => tri (thick R I e) (U.gt e).pG (fun a => x a ≫ ρ i))
    (fun i => tri (thick R I e) (fstG I e G) (fun a => x a ≫ ρ i))
    (fun i k => (congrArg (· ≫ fGl I G e) (ps i k)).trans (f₃ i k).symm) (fun k => (f₂ k).symm)
    (fun i k => (congrArg (· ≫ pGl U e) (ps i k)).trans (f₄ i k).symm)
    (cub_box_val hG pD e (U.gt e).pG g'.pG x ρ hq y)
    (fun i J N hJ hN => (w_cub_val U e T (fun a => x a ≫ ρ i) y hJ hN).trans (congrArg₂ (· * ·)
      (Finset.prod_congr rfl fun k _ => by rw [ps i k]) rfl))
    jL jM cM (Set.mem_iInter.1 hB) (fun k i => by
      have a : ((tri (thick R I e) (fstG I e G') x ≫ thφ G' (x3 G') k) ≫ (pG.pr i).left) y ∈ U.LG.L.U (jL k i) :=
        Set.mem_iInter.1 (Set.mem_iInter.1 hL k) i
      rw [Category.assoc, hψ, ← Category.assoc, t] at a
      exact a)
  refine key.trans (congrArg₂ (· * ·) rfl (Eq.trans (Finset.prod_congr rfl fun i _ => ?_)
    (gm_box_pull U.LG.L (fun i => (pG.pr i).left) _ hψ (fun _ => U.cubG.t) _ y jL hL).symm))
  rw [t]

end GlobalTheory.PowUnif
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PsiEvenBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily

theorem sym_box (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R}
    (pD : IsPowDeg D' D j) {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (y : Z) {J J'} (hJ : Good D.P.L y J)
    (hJ' : Good D'.P.L y J') :
    om pD.w y J J' (r ≫ (ι[D'.P.A]).left) * (om pD.w y J J' r)⁻¹ * val D'.sym r y J' =
      ∏ i, val D.sym (r ≫ (pD.pw.pr i).left) y J := by
  have hψ : ∀ (i : Fin j) (a : Fin 2), (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → _) a ≫ (pD.pw.pr i).left =
      (pD.pw.pr i).left ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) a := by
    intro i a
    have := pD.pw.hom i
    fin_cases a
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]
    · simp
  have he : eSec D'.P.A ≫ D'.P.A.hom = 𝟙 _ := Over.w η[D'.P.A]
  have hp : Function.Surjective D'.P.A.hom.appTop.hom := (hG _ D'.P.A D'.P.isAb).2
  have hinv : eSec D'.P.A ≫ (ι[D'.P.A]).left = eSec D'.P.A := by
    unfold eSec
    rw [← Over.comp_left, GrpObj.one_inv]
  have hpr : ∀ i, eSec D'.P.A ≫ (pD.pw.pr i).left = eSec D.P.A := fun i => by
    have := pD.pw.hom i
    unfold eSec
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hone : ∀ (E : DegPre R) (z : ↥(𝟙_ (Over (Spec (CommRingCat.of R)))).left)
      (K : ((𝟙_ (Over (Spec (CommRingCat.of R)))).left ⟶ E.P.A.left) → E.P.L.ι), Good E.P.L z K →
      val E.sym (eSec E.P.A) z K = 1 := by
    intro E z K hK
    have h := val_corr hK E.sym_rig (𝟙 _)
    rw [val_pull hK, Category.id_comp, val_one] at h
    exact h
  have key := GlobalTheory.CubBox.box_unique (φ' := ![(ι[D'.P.A]).left, 𝟙 D'.P.A.left]) (φ := ![(ι[D.P.A]).left, 𝟙 D.P.A.left])
    (ε := ![1, -1]) (ρ := fun i => (pD.pw.pr i).left) D.P.isLB D'.P.isLB pD.w pD.w_gen hψ D'.sym_gen D.sym_gen
    D'.P.A.hom (eSec D'.P.A) he hp
  specialize key (by
    intro z K K' hK hK'
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one,
      Category.comp_id, hinv, hpr, mul_inv_cancel]
    rw [hone D' z K' hK', hone D z K hK, Finset.prod_const_one, _root_.mul_one]) Z r y J J' hJ hJ'
  rw [Fin.prod_univ_two] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one,
    Category.comp_id] at key
  exact key

private theorem mul_mul_eq_mul_mul_mul_inv_mul {G : Type*} [CommGroup G] (a b c s : G) :
    b * c * s = a * (c * (b * a⁻¹ * s)) := by
  rw [← mul_inv_cancel_left a (b * c * s)]
  ac_rfl

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j), D.PsiEven → D'.PsiEven := by
  intro hG R _ _ j D D' pD hE χ
  refine corr_of_val D'.P.isLB (fun y J' hJ' => ?_)
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  have ha : D'.xK (-χ) = D'.xK χ ≫ (ι[D'.P.A]).left := by
    show ptK (D'.c (-χ)) = ptK (D'.c χ) ≫ (ι[D'.P.A]).left
    rw [GlobalTheory.PsiEvenPull.c_neg]
    unfold ptK
    rw [← Over.comp_left, Category.assoc]
  have hb : ∀ i, D'.xK χ ≫ (pD.pw.pr i).left = D.xK (pD.xe χ i) := by
    intro i
    have h := cPoint_pr pD (TK R) χ i
    unfold cP at h
    show ptK (D'.c χ) ≫ (pD.pw.pr i).left = ptK (D.c (pD.xe χ i))
    unfold ptK
    rw [← Over.comp_left, h]
  have hc : ∀ i, pD.xe (-χ) i = -pD.xe χ i := fun i => by
    rw [map_neg, Pi.neg_apply]
  have h4 : ∀ i, val (D.psi (pD.xe (-χ) i)) (𝟙 _) y J * val D.sym (D'.xK χ ≫ (pD.pw.pr i).left) y J =
      val (D.psi (pD.xe χ i)) (𝟙 _) y J := fun i => by
    have h := val_corr hJ (hE (pD.xe χ i)) (𝟙 _)
    rw [val_mul hJ, val_pull hJ, Category.id_comp] at h
    rw [hc, hb]
    exact h
  have h1 := psi_val pD hJ hJ' χ (𝟙 _)
  have h2 := psi_val pD hJ hJ' (-χ) (𝟙 _)
  have h3 := sym_box hG pD (D'.xK χ) y hJ hJ'
  rw [Category.id_comp, inv_mul_eq_iff_eq_mul] at h1 h2
  rw [ha] at h2
  rw [val_mul hJ', val_pull hJ', Category.id_comp, h1, h2]
  simp only [← h4, Finset.prod_mul_distrib]
  rw [← h3]
  exact mul_mul_eq_mul_mul_mul_inv_mul _ _ _ _

end GlobalTheory.PsiEvenBox
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.valuation_thetaRatio_eq_bilinear : TWM.VRatioGtStatement := by
  first | exact @GlobalTheory.RatioVal.main | exact GlobalTheory.RatioVal.main | (intros; apply GlobalTheory.RatioVal.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.integralExpansion_unique_of_uniformization : lemmaBSt.{0} → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (σ : H0 U.LG.L k) (f g : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) → (∀ e, U.ExpandsAt e k σ g) → f = g := by
  first | exact @GlobalTheory.ExpUniq.main | exact GlobalTheory.ExpUniq.main | (intros; apply GlobalTheory.ExpUniq.main <;> assumption)
end
