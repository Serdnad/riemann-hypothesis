module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CommutatorPairingE8SharpLevelPoints
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle061
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle062
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle063
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.Moduli

theorem cubicalStr_of_triv_theta : Out.Laws → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.Rigidified A M → Triv (Theta A M) → ∃ L : RigLB A, L.L = M ∧ Nonempty (CubicalStr A L) := by
  intro hL S A _ _ hA M hM hR hT
  obtain ⟨t, ht⟩ := hT
  obtain ⟨r, hr⟩ := hR
  obtain ⟨t', ht', hn⟩ := GlobalTheory.AbLaw.Cube.exists_normalised hM t ht
  exact ⟨⟨M, r, hM, hr⟩, rfl, ⟨GlobalTheory.AbLaw.Cube.cubicalOfNormalised
    (by cases hL; assumption) hA ⟨M, r, hM, hr⟩ t' ht' hn⟩⟩

end GlobalTheory.Moduli
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.thetaObject_comparison_maps_cocycle : (∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s), f ≫ s = s' → ∃ t' : TObj g k J b s', TMap t' t f) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (β : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (I : Type) (U : I → S.Opens) (t : ∀ i, TObj g k J β ((U i).ι ≫ s)) (u : ∀ i j, TObj g k J β ((U i ⊓ U j).ι ≫ s)) (a : ∀ i j, (u i j).A.left ⟶ (t i).A.left) (b : ∀ i j, (u i j).A.left ⟶ (t j).A.left), (∀ i j, IsGrpPullback (u i j).A (t i).A (S.homOfLE inf_le_left) (a i j) ∧ LBIso (u i j).L ((t i).L.pull (a i j)) ∧ ∀ l, ((u i j).pt l).left ≫ a i j = S.homOfLE inf_le_left ≫ ((t i).pt l).left) → (∀ i j, IsGrpPullback (u i j).A (t j).A (S.homOfLE inf_le_right) (b i j) ∧ LBIso (u i j).L ((t j).L.pull (b i j)) ∧ ∀ l, ((u i j).pt l).left ≫ b i j = S.homOfLE inf_le_right ≫ ((t j).pt l).left) → (∀ (T : Scheme.{0}) (i : I) (f : T ⟶ (U i).toScheme) (u : TObj g k J β (f ≫ (U i).ι ≫ s)) (φ φ' : u.A.left ⟶ (t i).A.left), IsOpenImmersion f → IsGrpPullback u.A (t i).A f φ → IsGrpPullback u.A (t i).A f φ' → LBIso u.L ((t i).L.pull φ) → LBIso u.L ((t i).L.pull φ') → (∀ a, (u.pt a).left ≫ φ = (u.pt a).left ≫ φ') → φ = φ') → ∀ i j k (T : Scheme.{0}) (x : T ⟶ (u i j).A.left) (y : T ⟶ (u j k).A.left) (z : T ⟶ (u i k).A.left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k := by
  first | exact @GlobalTheory.ThetaCocycle.cocycle | exact GlobalTheory.ThetaCocycle.cocycle | (intros; apply GlobalTheory.ThetaCocycle.cocycle <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Square

variable {Z : Scheme.{0}}

theorem rsT_eq {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) : rsT s O = resG Z h s := by
  unfold rsT
  rw [dite_eq_left h]

theorem rsT_add {O₀ : Z.Opens} (O : Z.Opens) (s t : Γ(Z, O₀)) : rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT
  split_ifs with h
  · exact map_add _ s t
  · exact (add_zero 0).symm

theorem rsT_sub {O₀ : Z.Opens} (O : Z.Opens) (s t : Γ(Z, O₀)) : rsT (s - t) O = rsT s O - rsT t O := by
  unfold rsT
  split_ifs with h
  · exact map_sub _ s t
  · exact (sub_zero 0).symm

theorem rsT_neg {O₀ : Z.Opens} (O : Z.Opens) (s : Γ(Z, O₀)) : rsT (-s) O = -rsT s O := by
  unfold rsT
  split_ifs with h
  · exact map_neg _ s
  · exact neg_zero.symm

theorem rsT_mul {O₀ : Z.Opens} (O : Z.Opens) (s t : Γ(Z, O₀)) : rsT (s * t) O = rsT s O * rsT t O := by
  unfold rsT
  split_ifs with h
  · exact map_mul _ s t
  · exact (mul_zero 0).symm

theorem rsT_sum {O₀ : Z.Opens} (O : Z.Opens) {g : ℕ} (s : Fin g → Γ(Z, O₀)) :
    rsT (∑ a, s a) O = ∑ a, rsT (s a) O := by
  unfold rsT
  split_ifs with h
  · exact map_sum _ s Finset.univ
  · exact Finset.sum_const_zero.symm

theorem rsT_rsT {O₀ O O' : Z.Opens} (h' : O' ≤ O) (h : O ≤ O₀) (s : Γ(Z, O₀)) :
    rsT (rsT s O) O' = rsT s O' := by
  rw [rsT_eq h', rsT_eq h, rsT_eq (h'.trans h)]
  unfold resG
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem rsT_pbT {Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {O O' : Z.Opens} (h' : O' ≤ O)
    (h : O ≤ f ⁻¹ᵁ O₀) (s : Γ(Y, O₀)) : rsT (pbT f s O) O' = pbT f s O' := by
  unfold pbT
  rw [dite_eq_left h, dite_eq_left (h'.trans h), rsT_eq h']
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

variable {J : Type} {V : J → Z.Opens}

theorem iSup_inf_eq (hV : ⨆ α, V α = ⊤) (W : Z.Opens) : ⨆ α, W ⊓ V α = W := by
  rw [← inf_iSup_eq, hV, inf_top_eq]

theorem ext_cover (hV : ⨆ α, V α = ⊤) {W : Z.Opens} (s t : Γ(Z, W))
    (h : ∀ α, rsT s (W ⊓ V α) = rsT t (W ⊓ V α)) : s = t := by
  refine TopCat.Sheaf.eq_of_locally_eq' (F := Z.sheaf) (U := fun α => W ⊓ V α) (V := W)
    (iUV := fun α => homOfLE inf_le_left) (iSup_inf_eq hV W).ge s t fun α => ?_
  have hα := h α
  rw [rsT_eq inf_le_left, rsT_eq inf_le_left] at hα
  exact hα

theorem exists_glue (hV : ⨆ α, V α = ⊤) (W : Z.Opens) (F : J → ∀ O : Z.Opens, Γ(Z, O))
    (h₁ : ∀ α O, O ≤ W ⊓ V α → rsT (F α (W ⊓ V α)) O = F α O)
    (h₂ : ∀ α β O, O ≤ W ⊓ V α ⊓ V β → F α O = F β O) :
    ∃ s : Γ(Z, W), ∀ α O, O ≤ W ⊓ V α → rsT s O = F α O := by
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := Z.sheaf) (U := fun α => W ⊓ V α) (V := W)
    (iUV := fun α => homOfLE inf_le_left) (iSup_inf_eq hV W).ge (fun α => F α (W ⊓ V α)) (by
      intro α β
      have e1 := h₁ α ((W ⊓ V α) ⊓ (W ⊓ V β)) inf_le_left
      have e2 := h₁ β ((W ⊓ V α) ⊓ (W ⊓ V β)) inf_le_right
      have e3 := h₂ α β ((W ⊓ V α) ⊓ (W ⊓ V β)) (le_inf inf_le_left (inf_le_right.trans inf_le_right))
      rw [rsT_eq inf_le_left] at e1
      rw [rsT_eq inf_le_right] at e2
      exact e1.trans (e3.trans e2.symm))
  refine ⟨s, fun α O hO => ?_⟩
  have hsα : resG Z (inf_le_left : W ⊓ V α ≤ W) s = F α (W ⊓ V α) := hs α
  rw [← rsT_rsT hO inf_le_left s, rsT_eq (inf_le_left : W ⊓ V α ≤ W) s, hsα]
  exact h₁ α O hO

theorem isAffineOpen_prod {S X Y : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S}
    (H : IsPullback p q iX iY) [IsAffine S] {U : X.Opens} {W : Y.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) := by
  have : IsAffine U := hU
  have : IsAffine W := hW
  have : IsAffine (⊤ : S.Opens) := isAffineOpen_top S
  exact IsAffine.of_isPullback
    (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := U) le_top le_top rfl)

theorem exists_split (hV : ⨆ α, V α = ⊤) {W : Z.Opens} (hW : IsAffineOpen W)
    (k : C1 fun α => W ⊓ V α) (hk : IsCoc _ k) :
    ∃ c : ∀ α, Γ(Z, W ⊓ V α), ∀ α β O, O ≤ W ⊓ V α ⊓ V β →
      rsT (k α β) O = rsT (c β) O - rsT (c α) O := by
  have hW' : IsAffineOpen (⨆ α, W ⊓ V α) := by
    rw [iSup_inf_eq hV W]
    exact hW
  obtain ⟨b, hb⟩ := isCob_of_isAffineOpen Z J (fun α => W ⊓ V α) k hW' hk
  refine ⟨b, fun α β O hO => ?_⟩
  have hO' : O ≤ (W ⊓ V α) ⊓ (W ⊓ V β) :=
    le_inf (hO.trans inf_le_left) (le_inf (hO.trans (inf_le_left.trans inf_le_left)) (hO.trans inf_le_right))
  rw [hb α β, rsT_sub, rsT_rsT hO' inf_le_right, rsT_rsT hO' inf_le_left]

theorem exists_compare (hV : ⨆ α, V α = ⊤) {Y : Scheme.{0}} (p : Z ⟶ Y) {T : Y.Opens}
    {W A B E : Z.Opens} (hA : W ≤ A) (hB : W ≤ B) (hE : W ≤ E) (hT : W ≤ p ⁻¹ᵁ T) {g : ℕ}
    (θ : Fin g → Γ(Y, T)) (e : Fin g → ∀ α, Γ(Z, E ⊓ V α))
    (k : C1 fun α => A ⊓ V α) (k' : C1 fun α => B ⊓ V α)
    (c : ∀ α, Γ(Z, A ⊓ V α)) (c' : ∀ α, Γ(Z, B ⊓ V α))
    (hc : ∀ α β O, O ≤ A ⊓ V α ⊓ V β → rsT (k α β) O = rsT (c β) O - rsT (c α) O)
    (hc' : ∀ α β O, O ≤ B ⊓ V α ⊓ V β → rsT (k' α β) O = rsT (c' β) O - rsT (c' α) O)
    (h : ∀ α β O, O ≤ W ⊓ V α ⊓ V β → rsT (k' α β) O - rsT (k α β) O =
      ∑ a, pbT p (θ a) O * (rsT (e a α) O - rsT (e a β) O)) :
    ∃ s : Γ(Z, W), ∀ α O, O ≤ W ⊓ V α →
      rsT s O = rsT (c' α) O - rsT (c α) O + ∑ a, pbT p (θ a) O * rsT (e a α) O := by
  refine exists_glue hV W
    (fun α O => rsT (c' α) O - rsT (c α) O + ∑ a, pbT p (θ a) O * rsT (e a α) O)
    (fun α O hO => ?_) (fun α β O hO => ?_)
  · have hAα : W ⊓ V α ≤ A ⊓ V α := inf_le_inf_right _ hA
    have hBα : W ⊓ V α ≤ B ⊓ V α := inf_le_inf_right _ hB
    have hEα : W ⊓ V α ≤ E ⊓ V α := inf_le_inf_right _ hE
    have hTα : W ⊓ V α ≤ p ⁻¹ᵁ T := inf_le_left.trans hT
    simp only [rsT_add, rsT_sub, rsT_sum, rsT_mul, rsT_rsT hO hAα, rsT_rsT hO hBα, rsT_rsT hO hEα,
      rsT_pbT p hO hTα]
  · have h1 := hc α β O (hO.trans (inf_le_inf_right _ (inf_le_inf_right _ hA)))
    have h2 := hc' α β O (hO.trans (inf_le_inf_right _ (inf_le_inf_right _ hB)))
    have h3 := h α β O hO
    simp only [mul_sub, Finset.sum_sub_distrib] at h3
    linear_combination h2 - h1 - h3

end GlobalTheory.KS.Square

namespace GlobalTheory.KS
open Square

theorem exists_isSymm_of_square : ∀ (K : Type) [Field K] (Y Z : Scheme.{0}) (q : Y ⟶ Sp K) (p₁ p₂ : Z ⟶ Y) (I : Type) [Finite I] (U : I → Y.Opens) (g : ℕ) (θ φ : Fin g → C1 U), IsSeparated q → IsPullback p₁ p₂ q q → (∀ i, IsAffineOpen (U i)) → (∀ c, IsCob U (lc q c φ) → c = 0) → ∀ (J : Type) (V : J → Z.Opens) (k : ∀ i j, C1 (fun α => p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j ⊓ V α)) (e : Fin g → ∀ j α, Γ(Z, p₂ ⁻¹ᵁ U j ⊓ V α)) (e' : Fin g → ∀ i α, Γ(Z, p₁ ⁻¹ᵁ U i ⊓ V α)), ⨆ α, V α = ⊤ → (∀ i j, IsCoc _ (k i j)) → (∀ a j j' α O, O ≤ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α → rsT (e a j' α) O - rsT (e a j α) O = pbT p₂ (φ a j j') O) → (∀ a i i' α O, O ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ V α → rsT (e' a i' α) O - rsT (e' a i α) O = pbT p₁ (φ a i i') O) → (∀ i i' j α β O, O ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j ⊓ V α ⊓ V β → rsT (k i' j α β) O - rsT (k i j α β) O = ∑ a, pbT p₁ (θ a i i') O * (rsT (e a j α) O - rsT (e a j β) O)) → (∀ i j j' α β O, O ≤ p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α ⊓ V β → rsT (k i j' α β) O - rsT (k i j α β) O = ∑ a, pbT p₂ (θ a j j') O * (rsT (e' a i α) O - rsT (e' a i β) O)) → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob U (θ b - lc q (Θ b) φ) := by
  intro K _ Y Z q p₁ p₂ I _ U g θ φ hq H hU hφ J V k e e' hV hk he he' hk₁ hk₂
  have hA : ∀ i j, IsAffineOpen (p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j) := fun i j =>
    isAffineOpen_prod H (hU i) (hU j)
  choose c hc using fun i j => exists_split hV (hA i j) (k i j) (hk i j)
  choose u hu using fun i i' j => exists_compare hV p₁ (T := U i ⊓ U i')
    (W := p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j) (A := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j)
    (B := p₁ ⁻¹ᵁ U i' ⊓ p₂ ⁻¹ᵁ U j) (E := p₂ ⁻¹ᵁ U j)
    (inf_le_inf_right _ (p₁.preimage_mono inf_le_left)) (inf_le_inf_right _ (p₁.preimage_mono inf_le_right))
    inf_le_right inf_le_left (fun a => θ a i i') (fun a => e a j) (k i j) (k i' j) (c i j) (c i' j)
    (hc i j) (hc i' j) (hk₁ i i' j)
  choose v hv using fun i j j' => exists_compare hV p₂ (T := U j ⊓ U j')
    (W := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) (A := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j)
    (B := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j') (E := p₁ ⁻¹ᵁ U i)
    (inf_le_inf_left _ (p₂.preimage_mono inf_le_left)) (inf_le_inf_left _ (p₂.preimage_mono inf_le_right))
    inf_le_left inf_le_right (fun a => θ a j j') (fun a => e' a i) (k i j) (k i j') (c i j) (c i j')
    (hc i j) (hc i j') (hk₂ i j j')
  refine GlobalTheory.T.kunneth_symm_product_affine_covers K Y Z q p₁ p₂ I U g θ φ hq H hU hφ u (fun i j j' => -v i j j') ?_
  intro i i' j j'
  apply ext_cover hV
  intro α
  have hQ1 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j' :=
    inf_le_inf_left _ (p₂.preimage_mono inf_le_right)
  have hQ2 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j :=
    inf_le_inf_left _ (p₂.preimage_mono inf_le_left)
  have hQ3 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ U i' ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') :=
    inf_le_inf_right _ (p₁.preimage_mono inf_le_right)
  have hQ4 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') :=
    inf_le_inf_right _ (p₁.preimage_mono inf_le_left)
  have hu₁ := hu i i' j' α _ (inf_le_inf_right (V α) hQ1)
  have hu₂ := hu i i' j α _ (inf_le_inf_right (V α) hQ2)
  have hv₁ := hv i' j j' α _ (inf_le_inf_right (V α) hQ3)
  have hv₂ := hv i j j' α _ (inf_le_inf_right (V α) hQ4)
  have hφ₂ := fun a => he a j j' α (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α) (inf_le_inf_right (V α) inf_le_right)
  have hφ₁ := fun a => he' a i i' α (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α) (inf_le_inf_right (V α) inf_le_left)
  have hO : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α ≤
      p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') := inf_le_left
  simp only [rsT_add, rsT_sub, rsT_neg, rsT_sum, rsT_mul,
    Square.rsT_rsT hO hQ1, Square.rsT_rsT hO hQ2, Square.rsT_rsT hO hQ3, Square.rsT_rsT hO hQ4,
    Square.rsT_pbT p₁ hO inf_le_left, Square.rsT_pbT p₂ hO inf_le_right]
  rw [hu₁, hu₂, hv₁, hv₂]
  simp only [← hφ₁, ← hφ₂, mul_sub, sub_mul, Finset.sum_sub_distrib]
  simp only [mul_comm (rsT (e' _ _ α) _)]
  ring

end GlobalTheory.KS
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.exists_lattice_aut_of_isomorphic_theta_objects : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t t' : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q Q' : La →+ (Fin g → ℂ)) (Hm Hm' : Matrix (Fin g) (Fin g) ℂ), Function.Injective Q → Function.Injective Q' → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∃ (u : HolUnif t'.A t'.L g) (χ' : u.Λ → ℂ), u.IsAH Hm' χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q').range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q' x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t'.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q' (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q' x) = Q' (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t'.act j₀) → TMap t' t (𝟙 _) → ∃ (gam : La ≃+ La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), ∀ x, h (Q' x) = Q (gam x) := by
  first | exact @GlobalTheory.exists_lattice_aut_of_tMap_id | exact GlobalTheory.exists_lattice_aut_of_tMap_id | (intros; apply GlobalTheory.exists_lattice_aut_of_tMap_id <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.commutatorPairing_e8Sharp_levelPoints : Out.Laws → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), IsSharpBasis W bas → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → ∀ (K : Type) [Field K] (p : Sp K ⟶ S) (β : o →+* K) (z : Kˣ), p ≫ s = spMap β → (z : K) = β b.ζ → ∀ (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) (y y' : Over.mk p ⟶ t.A), (∀ u, y ≫ pr u = toUnit _ ≫ lev (X u)) → (∀ u, y' ≫ pr u = toUnit _ ≫ lev (Y u)) → Out.WeilIs t.A t.L k y y' (unitOn z ^ ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v)) := by
  first | exact @GlobalTheory.weilIs_sharp_levelPoints | exact GlobalTheory.weilIs_sharp_levelPoints | (intros; apply GlobalTheory.weilIs_sharp_levelPoints <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.exists_localDerivationAlongFibre_of_smooth : ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (Y X : Scheme.{0}) (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDer x₀ D → IsAffineOpen W₀ → ∃ d, LocDer q p m D W₀ d := by
  first | exact @GlobalTheory.KS.exists_locDer_of_smooth | exact GlobalTheory.KS.exists_locDer_of_smooth | (intros; apply GlobalTheory.KS.exists_locDer_of_smooth <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z δ, PtDer ((u.ex z).left ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃! w, ∀ W f, z ∈ dom u m W → δ W f = fderiv ℂ (fn u m W f) z w := by
  first | exact @GlobalTheory.KS.VertFamily.existsUnique_vector | exact GlobalTheory.KS.VertFamily.existsUnique_vector | (intros; apply GlobalTheory.KS.VertFamily.existsUnique_vector <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.projective_representation_pullback_coordinates : ∀ (R R' σ : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (I : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R') (π : Z' ⟶ Z) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → IsPullback π s' s (spMap φ) → ∃ th' : σ → (M.pull π).Sec, ProjRep (I.map (MvPolynomial.map φ)) s' (M.pull π) th' ∧ ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z') (v : σ → T), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v := by
  first | exact @GlobalTheory.ZM.RepBC.projRep_baseChange | exact GlobalTheory.ZM.RepBC.projRep_baseChange | (intros; apply GlobalTheory.ZM.RepBC.projRep_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.Coord
open GlobalTheory.ZM.RepBC

theorem le_iSup_chart {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) : (⊤ : Y.Opens) ≤ iSup L.U := hL.cover.ge

theorem exists_global_unit {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {t t' : L.Gen} (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ j, t.s j = res (le_top : L.U j ≤ ⊤) w * t'.s j := by
  let u : ∀ j, Γ(Y, L.U j)ˣ := fun j => t.s j * (t'.s j)⁻¹
  have compat : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (u i) =
      res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (u j) := by
    intro i j
    simp only [u, map_mul, map_inv, ht i j, ht' i j, mul_inv]
    simp only [_root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
  have glue : ∀ (v : ∀ j, Γ(Y, L.U j)ˣ),
      (∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (v i) =
        res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (v j)) →
      ∃ s : Γ(Y, ⊤), ∀ j, resG Y (le_top : L.U j ≤ ⊤) s = (v j).val := by
    intro v hv
    exact (TopCat.Sheaf.existsUnique_gluing' Y.sheaf L.U ⊤ (fun _ => homOfLE le_top) (le_iSup_chart hL) _ (by
        intro i j
        exact congrArg Units.val (hv i j))).exists
  obtain ⟨s, hs⟩ := glue u compat
  have compat' : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) ((u i)⁻¹) =
      res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) ((u j)⁻¹) := by
    intro i j
    rw [map_inv, map_inv, compat]
  obtain ⟨s', hs'⟩ := glue (fun j => (u j)⁻¹) compat'
  have hss : s * s' = 1 := by
    apply Y.sheaf.eq_of_locally_eq' L.U ⊤ (fun _ => homOfLE le_top) (le_iSup_chart hL)
    intro j
    change resG Y (le_top : L.U j ≤ ⊤) (s * s') = resG Y (le_top : L.U j ≤ ⊤) 1
    rw [map_mul, map_one, hs, hs']
    exact Units.mul_inv (u j)
  let w : Γ(Y, ⊤)ˣ := ⟨s, s', hss, by simpa [mul_comm] using hss⟩
  refine ⟨w, fun j => ?_⟩
  have hw : res (le_top : L.U j ≤ ⊤) w = u j := Units.ext (hs j)
  rw [hw]
  change t.s j = (t.s j * (t'.s j)⁻¹) * t'.s j
  simp

theorem appLE_spec {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (e : (⊤ : (Sp R').Opens) ≤ spMap φ ⁻¹ᵁ ⊤)
    (a : R) : ((spMap φ).appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (φ a) := by
  have h := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  refine Eq.trans ?_ h.symm
  exact r_self (X := Sp R') (U := ⊤) le_rfl (((spMap φ).app ⊤).hom _)

variable {X : Scheme.{0}} {M : LB X} {I : Type} {th : I → M.Sec} {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : I → R}

theorem baseChange (h : SecCoord M th x v) {R' : Type} [CommRing R'] (φ : R →+* R') :
    SecCoord M th (spMap φ ≫ x) (fun i => φ (v i)) := by
  obtain ⟨τ, hτ, h⟩ := h
  refine ⟨LB.pullGen M _ _ τ (spMap φ), ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen M _ _ τ hτ _, fun i j e => ?_⟩
  have hle : (M.pull (spMap φ ≫ x)).U j ≤ spMap φ ⁻¹ᵁ (M.pull x).U j :=
    fun _ hy => le_pull M x j (e hy)
  have h0 := congrArg ((spMap φ).appLE _ _ hle).hom (h i j (pull_le M x j))
  rw [map_mul, appLE_appLE _ _ _ _ e, appLE_r] at h0
  refine h0.trans ?_
  congr 1
  rw [← appLE_spec φ le_top]
  exact (r_appLE (spMap φ) _ _ _).symm

theorem scale (h : SecCoord M th x v) (u : Rˣ) : SecCoord M th x (fun i => u * v i) := by
  obtain ⟨τ, hτ, h⟩ := h
  let w : Γ(Sp R, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom u
  refine ⟨⟨fun j => (res (le_top : (M.pull x).U j ≤ ⊤) w)⁻¹ * τ.s j⟩, fun j j' => ?_, fun i j e => ?_⟩
  · have e1 : res (inf_le_left : (M.pull x).U j ⊓ (M.pull x).U j' ≤ _) (res (le_top : (M.pull x).U j ≤ ⊤) w) =
        res (inf_le_right : (M.pull x).U j ⊓ (M.pull x).U j' ≤ _) (res (le_top : (M.pull x).U j' ≤ ⊤) w) :=
      Units.ext ((rr _ _ _).trans (rr _ _ _).symm)
    simp only [map_mul, map_inv]
    rw [hτ j j', e1, mul_left_comm]
  · rw [h i j e, map_mul, map_mul]
    have e1 : resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u) =
      (res (le_top : (M.pull x).U j ≤ ⊤) w).val := rfl
    rw [e1]
    show _ = _ * (((res (le_top : (M.pull x).U j ≤ ⊤) w)⁻¹).val * (τ.s j).val)
    rw [_root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul]

theorem unique (hM : M.IsLB) (h : SecCoord M th x v) {v' : I → R} (h' : SecCoord M th x v') :
    ∃ u : Rˣ, ∀ i, v' i = u * v i := by
  obtain ⟨τ, hτ, h⟩ := h
  obtain ⟨τ', hτ', h'⟩ := h'
  have hcov : (⊤ : (Sp R).Opens) ≤ iSup (M.pull x).U := by
    intro y _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (show x y ∈ (⊤ : X.Opens) from trivial))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
  have global : ∃ w : Γ(Sp R, ⊤)ˣ, ∀ j, τ.s j = res (le_top : (M.pull x).U j ≤ ⊤) w * τ'.s j := by
    let u : ∀ j, Γ((Sp R), (M.pull x).U j)ˣ := fun j => τ.s j * (τ'.s j)⁻¹
    have compat : ∀ i j, res (inf_le_left : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U i) (u i) =
        res (inf_le_right : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U j) (u j) := by
      intro i j
      simp only [u, map_mul, map_inv, hτ i j, hτ' i j, mul_inv]
      simp only [_root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
    have glue : ∀ (v : ∀ j, Γ((Sp R), (M.pull x).U j)ˣ),
        (∀ i j, res (inf_le_left : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U i) (v i) =
          res (inf_le_right : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U j) (v j)) →
        ∃ s : Γ((Sp R), ⊤), ∀ j, resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) s = (v j).val := by
      intro v hv
      exact (TopCat.Sheaf.existsUnique_gluing' (Sp R).sheaf (M.pull x).U ⊤ (fun _ => homOfLE le_top) hcov _ (by
          intro i j
          exact congrArg Units.val (hv i j))).exists
    obtain ⟨s, hs⟩ := glue u compat
    have compaτ' : ∀ i j, res (inf_le_left : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U i) ((u i)⁻¹) =
        res (inf_le_right : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U j) ((u j)⁻¹) := by
      intro i j
      rw [map_inv, map_inv, compat]
    obtain ⟨s', hs'⟩ := glue (fun j => (u j)⁻¹) compaτ'
    have hss : s * s' = 1 := by
      apply (Sp R).sheaf.eq_of_locally_eq' (M.pull x).U ⊤ (fun _ => homOfLE le_top) hcov
      intro j
      change resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) (s * s') = resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) 1
      rw [map_mul, map_one, hs, hs']
      exact Units.mul_inv (u j)
    let w : Γ((Sp R), ⊤)ˣ := ⟨s, s', hss, by simpa [mul_comm] using hss⟩
    refine ⟨w, fun j => ?_⟩
    have hw : res (le_top : (M.pull x).U j ≤ ⊤) w = u j := Units.ext (hs j)
    rw [hw]
    change τ.s j = (τ.s j * (τ'.s j)⁻¹) * τ'.s j
    simp
  obtain ⟨w, hw⟩ := global
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom w, fun i => ?_⟩
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v' i) =
      w.val * (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i) := by
    apply (Sp R).sheaf.eq_of_locally_eq' (M.pull x).U ⊤ (fun _ => homOfLE le_top) hcov
    intro j
    have e := (h' i j (pull_le M x j)).symm.trans (h i j (pull_le M x j))
    rw [hw j] at e
    show resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) _ = resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) _
    rw [map_mul]
    apply (Units.mul_left_inj (τ'.s j)).1
    refine e.trans ?_
    show _ * (resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) w.val * (τ'.s j).val) = _
    ring
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom key
  rw [map_mul] at this
  simpa using this

theorem secCoord_bc_scale_unique : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), M.IsLB → SecCoord M th x v → (∀ (R' : Type) [CommRing R'] (φ : R →+* R'), SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) ∧ (∀ u : Rˣ, SecCoord M th x (fun i => u * v i)) ∧ ∀ v', SecCoord M th x v' → ∃ u : Rˣ, ∀ i, v' i = u * v i :=
  fun _ _ _ _ _ _ _ _ hM h => ⟨fun _ _ φ => baseChange h φ, scale h, fun _ h' => unique hM h h'⟩

end GlobalTheory.ZM.Coord
end
end
