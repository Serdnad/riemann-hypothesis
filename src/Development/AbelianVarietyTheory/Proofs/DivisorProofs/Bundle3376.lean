module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
import Aesop.Frontend.Tactic
import Aesop.Main
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3367
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3372
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3371
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.CechH1Local

theorem isCob_of_refine_le {Y : Scheme.{0}} {I K : Type} (Uc : I → Y.Opens) (c : C1 Uc) (hc : IsCoc Uc c)
    (V : K → Y.Opens) (σ : K → I) (hV : ∀ p, V p ≤ Uc (σ p)) (hVt : ∀ i, Uc i ≤ ⨆ p, V p)
    (B : ∀ p, Γ(Y, V p)) (hB : ∀ p p', rsT (c (σ p) (σ p')) (V p ⊓ V p') =
      rsT (B p') (V p ⊓ V p') - rsT (B p) (V p ⊓ V p')) : IsCob Uc c := by
  have hV' : ∀ p y, y ∈ V p → y ∈ Uc (σ p) := fun p y h => hV p h
  have cov : ∀ O : Y.Opens, O ≤ ⨆ p, V p → O ≤ ⨆ p, O ⊓ V p := by
    intro O hO x hx
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 (hO hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hx, hp⟩
  have left {a b d : Y.Opens} (h : a ≤ d) : a ⊓ b ≤ d := inf_le_left.trans h
  have right {a b d : Y.Opens} (h : b ≤ d) : a ⊓ b ≤ d := inf_le_right.trans h
  have glue : ∀ i, ∃ t : Γ(Y, Uc i), ∀ p, rsT t (Uc i ⊓ V p) =
      rsT (B p) (Uc i ⊓ V p) + rsT (c (σ p) i) (Uc i ⊓ V p) := by
    intro i
    refine exists_rsT_eq (fun p => Uc i ⊓ V p) (fun p => inf_le_left) (cov _ (hVt i)) _ fun p p' => ?_
    have h1 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hB p p')
    have h2 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hc (σ p) (σ p') i)
    simp only [rsT_add, rsT_sub] at h1 h2 ⊢
    simp (disch := aesop (add safe apply [le_inf, inf_le_left, inf_le_right, left, right, hV])) only [rsT_rsT] at h1 h2 ⊢
    linear_combination h1 - h2
  choose t ht using glue
  refine ⟨t, fun i j => ?_⟩
  refine eq_of_rsT_eq (fun p => Uc i ⊓ Uc j ⊓ V p) (fun p => inf_le_left)
    (cov _ (inf_le_left.trans (hVt i))) _ _ fun p => ?_
  have h1 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht i p)
  have h2 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht j p)
  have h3 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (hc (σ p) i j)
  simp only [rsT_add, rsT_sub] at h1 h2 h3 ⊢
  simp (disch := aesop (add safe apply [le_inf, inf_le_left, inf_le_right, left, right, hV])) only [rsT_rsT] at h1 h2 h3 ⊢
  linear_combination h1 - h2 + h3

theorem rsT_field {Z : Scheme.{0}} {d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)} (hd : IsField ⊤ d) {O O' : Z.Opens}
    (h : O' ≤ O) (f : Γ(Z, O)) : rsT (d O f) O' = d O' (rsT f O') := by
  rw [rsT_of_le h, rsT_of_le h, hd.2.2 _ _ h le_top]

theorem rsT_appLE {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {O O' : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) (h' : O' ≤ O)
    (r : Γ(X, V)) : rsT ((π.appLE V O h).hom r) O' = (π.appLE V O' (h'.trans h)).hom r := by
  rw [rsT_of_le h']
  exact congrArg (fun φ => φ.hom r) (Scheme.Hom.appLE_map π h (homOfLE h').op)

theorem rsT_unit {Z : Scheme.{0}} {T O : Z.Opens} (h : O ≤ T) (u : Γ(Z, T)ˣ) :
    rsT u.val O * rsT u⁻¹.val O = 1 := by
  rw [← rsT_mul, Units.mul_inv, rsT_one h]

theorem isCoc_dlg {Z : Scheme.{0}} (L : LB Z) (hL : L.IsLB) {d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)}
    (hd : IsField ⊤ d) {J : Type} (W : J → Z.Opens) (j : J → L.ι) (hj : ∀ i, W i ≤ L.U (j i)) :
    IsCoc W (fun i i' => d (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) *
      rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) := by
  intro i i' i''
  set O := W i ⊓ W i' ⊓ W i''
  have l₁ : O ≤ W i ⊓ W i' := inf_le_left
  have l₂ : O ≤ W i' ⊓ W i'' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l₃ : O ≤ W i ⊓ W i'' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have m₁ : W i ⊓ W i' ≤ L.U (j i) ⊓ L.U (j i') := inf_le_inf (hj i) (hj i')
  have m₂ : W i' ⊓ W i'' ≤ L.U (j i') ⊓ L.U (j i'') := inf_le_inf (hj i') (hj i'')
  have m₃ : W i ⊓ W i'' ≤ L.U (j i) ⊓ L.U (j i'') := inf_le_inf (hj i) (hj i'')
  have k : ∀ (a b : J) (l : O ≤ W a ⊓ W b) (m : W a ⊓ W b ≤ L.U (j a) ⊓ L.U (j b)),
      rsT (d (W a ⊓ W b) (rsT (L.g (j a) (j b)).val (W a ⊓ W b)) * rsT (L.g (j a) (j b))⁻¹.val (W a ⊓ W b)) O =
        d O (rsT (L.g (j a) (j b)).val O) * rsT (L.g (j a) (j b))⁻¹.val O := by
    intro a b l m
    rw [rsT_mul, rsT_field hd l, rsT_rsT m l, rsT_rsT m l]
  rw [k i i' l₁ m₁, k i' i'' l₂ m₂, k i i'' l₃ m₃]
  have T3 : O ≤ L.U (j i) ⊓ L.U (j i') ⊓ L.U (j i'') :=
    le_inf (le_inf (l₁.trans (m₁.trans inf_le_left)) (l₁.trans (m₁.trans inf_le_right)))
      (l₂.trans (m₂.trans inf_le_right))
  have co := congrArg (fun u => rsT (Units.val u) O) (hL.cocycle (j i) (j i') (j i''))
  simp only [Units.val_mul, rsT_mul] at co
  have e : ∀ {T T' : Z.Opens} (h : T' ≤ T) (u : Γ(Z, T)ˣ), (res h u).val = resG Z h u.val := fun _ _ => rfl
  have r : ∀ {T T' : Z.Opens} (h : T' ≤ T) (s : Γ(Z, T)), O ≤ T' → rsT (resG Z h s) O = rsT s O :=
    fun h s hO => by rw [← rsT_of_le h, rsT_rsT h hO]
  rw [e, e, e, r _ _ T3, r _ _ T3, r _ _ T3] at co
  set a := rsT (L.g (j i) (j i')).val O
  set b := rsT (L.g (j i') (j i'')).val O
  set a' := rsT (L.g (j i) (j i'))⁻¹.val O
  set b' := rsT (L.g (j i') (j i''))⁻¹.val O
  set e' := rsT (L.g (j i) (j i''))⁻¹.val O
  have ha : a * a' = 1 := rsT_unit (l₁.trans m₁) _
  have hb : b * b' = 1 := rsT_unit (l₂.trans m₂) _
  have he : rsT (L.g (j i) (j i'')).val O * e' = 1 := rsT_unit (l₃.trans m₃) _
  rw [← co] at he ⊢
  have hdm := hd.2.1 O le_top a b
  rw [hdm]
  linear_combination (-(d O a * a' + d O b * b')) * he + (d O a * b * e') * ha + (d O b * a * e') * hb

theorem exists_dlog_add_coboundary_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → ∀ z : C1 W, IsCoc W z → ∃ (cc : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (y : ∀ i, Γ(t.G.left, W i)), ∀ i i', z i i' = ∑ b, GlobalTheory.HeatV.cst t.G.hom (GlobalTheory.HeatV.bo R c).1 (inf_le_left.trans (hW i)) (cc b) * (dd' b (W i ⊓ W i') (rsT (t.PP.L.g (j i) (j i')).val (W i ⊓ W i')) * rsT (t.PP.L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) + (rsT (y i') (W i ⊓ W i') - rsT (y i) (W i ⊓ W i')) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt htt hab c hc n v' dd' hdd J W j hW hWc hj z hz
  let K := {p : t.G.left.affineOpens × J // p.1.1 ≤ W p.2}
  let V : K → t.G.left.Opens := fun p => p.1.1.1
  let σ : K → J := fun p => p.1.2
  have hVσ : ∀ p, V p ≤ W (σ p) := fun p => p.2
  have hVt : ∀ i, W i ≤ ⨆ p, V p := by
    intro i x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := t.G.left.isBasis_affineOpens.exists_subset_of_mem_open hx (W i).isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, i), hUW⟩, hxU⟩
  have cover : ⨆ p, V p = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 := by
    refine le_antisymm (iSup_le fun p => (hVσ p).trans (hW _)) ?_
    rw [← hWc]
    exact iSup_le hVt
  let z' : C1 V := fun p p' => rsT (z (σ p) (σ p')) (V p ⊓ V p')
  have hz' : IsCoc V z' := by
    intro p p' p''
    have h := congrArg (fun s => rsT s (V p ⊓ V p' ⊓ V p'')) (hz (σ p) (σ p') (σ p''))
    simp only [rsT_add] at h
    have l₁ : V p ⊓ V p' ⊓ V p'' ≤ W (σ p) ⊓ W (σ p') ⊓ W (σ p'') :=
      inf_le_inf (inf_le_inf (hVσ p) (hVσ p')) (hVσ p'')
    simp only [z']
    rw [rsT_rsT (inf_le_inf (hVσ p) (hVσ p')) inf_le_left, rsT_rsT (inf_le_inf (hVσ p') (hVσ p''))
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
      rsT_rsT (inf_le_inf (hVσ p) (hVσ p'')) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)]
    rwa [rsT_rsT inf_le_left l₁, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) l₁,
      rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) l₁] at h
  obtain ⟨cc, y', hy'⟩ := GlobalTheory.T.basis_tangent_module_localized_abelian_locus E H R t P m tt htt hab c hc n v' dd' hdd K V (fun p => j (σ p))
    (fun p => (hVσ p).trans (hW _)) cover (fun p => (hVσ p).trans (hj _)) (fun p => p.1.1.2) z' hz'
  let dl : Fin n → C1 W := fun b i i' => dd' b (W i ⊓ W i') (rsT (t.PP.L.g (j i) (j i')).val (W i ⊓ W i')) *
    rsT (t.PP.L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')
  have hdl : ∀ b, IsCoc W (dl b) := fun b => isCoc_dlg t.PP.L t.PP.isLB (hdd b).1 W j hj
  let c0 : C1 W := fun i i' => z i i' - ∑ b, GlobalTheory.HeatV.cst t.G.hom (GlobalTheory.HeatV.bo R c).1
    (inf_le_left.trans (hW i)) (cc b) * dl b i i'
  let Cf : ∀ O : t.G.left.Opens, O ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → Fin n → Γ(t.G.left, O) :=
    fun O h b => (t.G.hom.appLE _ O h).hom (cc b)
  have key : ∀ (a a' : J) {O : t.G.left.Opens} (l : O ≤ W a ⊓ W a'),
      rsT (c0 a a') O = rsT (z a a') O - ∑ b, Cf O (l.trans (inf_le_left.trans (hW a))) b * rsT (dl b a a') O := by
    intro a a' O l
    simp only [c0]
    rw [rsT_sub, rsT_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [rsT_mul, rsT_appLE _ _ _ l]
  have hc0 : IsCoc W c0 := by
    intro i i' i''
    have l₁ : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i' := inf_le_left
    have l₂ : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have l₃ : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have h0 := hz i i' i''
    rw [key i i' l₁, key i' i'' l₂, key i i'' l₃]
    have hs : ∑ b, Cf _ (l₁.trans (inf_le_left.trans (hW i))) b * rsT (dl b i i') (W i ⊓ W i' ⊓ W i'') +
        ∑ b, Cf _ (l₁.trans (inf_le_left.trans (hW i))) b * rsT (dl b i' i'') (W i ⊓ W i' ⊓ W i'') =
        ∑ b, Cf _ (l₁.trans (inf_le_left.trans (hW i))) b * rsT (dl b i i'') (W i ⊓ W i' ⊓ W i'') := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_add, hdl b i i' i'']
    linear_combination h0 - hs
  have hB : ∀ p p', rsT (c0 (σ p) (σ p')) (V p ⊓ V p') = rsT (y' p') (V p ⊓ V p') - rsT (y' p) (V p ⊓ V p') := by
    intro p p'
    have l : V p ⊓ V p' ≤ W (σ p) ⊓ W (σ p') := inf_le_inf (hVσ p) (hVσ p')
    rw [key _ _ l, show rsT (z (σ p) (σ p')) (V p ⊓ V p') = z' p p' from rfl, hy' p p']
    have hs : ∀ b, rsT (dl b (σ p) (σ p')) (V p ⊓ V p') =
        dd' b (V p ⊓ V p') (rsT (t.PP.L.g (j (σ p)) (j (σ p'))).val (V p ⊓ V p')) *
          rsT (t.PP.L.g (j (σ p)) (j (σ p')))⁻¹.val (V p ⊓ V p') := fun b => by
      simp only [dl]
      rw [rsT_mul, rsT_field (hdd b).1 l, rsT_rsT (inf_le_inf (hj _) (hj _)) l, rsT_rsT (inf_le_inf (hj _) (hj _)) l]
    simp only [hs]
    ring
  obtain ⟨y, hy⟩ := isCob_of_refine_le W c0 hc0 V σ hVσ hVt y' hB
  refine ⟨cc, y, fun i i' => ?_⟩
  have := hy i i'
  simp only [c0] at this
  linear_combination this

end GlobalTheory.CechH1Local
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem smoothOfRelDim_of_pullback_snd_identity {S : Scheme.{0}} (X : Over S) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd X.hom (𝟙 S))) : SmoothOfRelativeDimension g X.hom := by
  have e : X.hom = inv (pullback.fst X.hom (𝟙 S)) ≫ pullback.snd X.hom (𝟙 S) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  have := smoothOfRelativeDimension_comp (n := 0) (m := g) (inv (pullback.fst X.hom (𝟙 S))) (pullback.snd X.hom (𝟙 S))
  simpa using this

theorem smoothOfRelDim_pullback_snd_identity {S : Scheme.{0}} (X : Over S) (g : ℕ)
    (h : SmoothOfRelativeDimension g X.hom) : SmoothOfRelativeDimension g (pullback.snd X.hom (𝟙 S)) := by
  have e : pullback.snd X.hom (𝟙 S) = pullback.fst X.hom (𝟙 S) ≫ X.hom := by
    rw [pullback.condition, Category.comp_id]
  rw [e]
  have := smoothOfRelativeDimension_comp (n := 0) (m := g) (pullback.fst X.hom (𝟙 S)) X.hom
  simpa using this

theorem dualAbelianScheme : GlobalTheory.Published.DualAbelianScheme := by
  intro S A _ hA
  obtain ⟨B, _, P, hB, hdim, hdual⟩ := GlobalTheory.T.exists_dual_abelianScheme_poincare S A hA
  refine ⟨B, inferInstance, P, hB, fun g hg => ?_, hdual, GlobalTheory.T.isDualAbelianSchemePoincare_swap S A B P hA hB hdim hdual⟩
  exact smoothOfRelDim_of_pullback_snd_identity B g (hdim g S (𝟙 S) (smoothOfRelDim_pullback_snd_identity A g hg))

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finiteFlat_torsion_harrisTaylor_abelian : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (w : Ideal (𝓞 D.F)), w ≠ ⊥ → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ o.A), IsMonHom i ∧ Mono i ∧ GlobalTheory.IwLevel.IsIsogDeg (toUnit K) ((Ideal.absNorm w ^ D.m) ^ D.n) ∧ ∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x := by
  first | (exact @GlobalTheory.HTTors.htTorsion) | (exact GlobalTheory.HTTors.htTorsion) | (intros; apply GlobalTheory.HTTors.htTorsion <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.isProper_of_properSpecialFibre_universallyOpen_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of W)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → UniversallyOpen f → GeometricallyIrreducible f → IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)))) → IsProper f := by
  first | exact @GlobalTheory.FibreProperDvr.isProper_of_specialFibre | exact GlobalTheory.FibreProperDvr.isProper_of_specialFibre | (intros; apply GlobalTheory.FibreProperDvr.isProper_of_specialFibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SteinFact

theorem finite_appTop_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}}
    (f : X ⟶ Sp R) [IsProper f] :
    ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom.Finite := by
  letI := GlobalTheory.algebraΓOfHom f
  have h0 := GlobalTheory.ProperFinite.finite_coh_of_isProper f (GlobalTheory.structureModule X) 0
  have h1 := Module.Finite.equiv (GlobalTheory.cohOn.zeroEquiv R (GlobalTheory.structureModule X) ⊤)
  let ρ : GlobalTheory.sectionsOn (GlobalTheory.structureModule X) ⊤ →ₗ[R] Γ(X, ⊤) :=
    { toFun := fun s => (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤ s : Γ(X, ⊤))
      map_add' := fun s t => map_add (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤) s t
      map_smul' := fun r s => by
        rw [GlobalTheory.sectionsOn.toΓ_smul]
        rw [GlobalTheory.restrictGlobal_top]
        rfl }
  have hρ : Function.Bijective ρ := (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤).bijective
  exact Module.Finite.equiv (LinearEquiv.ofBijective ρ hρ)

theorem finite_app_of_isProper {X Y : Scheme.{0}} (g : X ⟶ Y) [IsProper g] {V : Y.Opens}
    (hV : IsAffineOpen V) [IsNoetherianRing Γ(Y, V)] : (g.app V).hom.Finite := by
  let j := (g ⁻¹ᵁ V).ι
  let g' : (g ⁻¹ᵁ V).toScheme ⟶ Sp Γ(Y, V) := g ∣_ V ≫ hV.isoSpec.hom
  have : IsProper g' := inferInstanceAs (IsProper (g ∣_ V ≫ hV.isoSpec.hom))
  have h1 := finite_appTop_of_isProper g'
  have hle : j ''ᵁ ⊤ ≤ g ⁻¹ᵁ V := (g ⁻¹ᵁ V).ι_image_top.le
  have e : (Scheme.ΓSpecIso (.of Γ(Y, V))).inv ≫ g'.appTop = g.appLE V (j ''ᵁ ⊤) hle := by
    ext r
    change (g ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso Γ(Y, V)).inv r) = _
    rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop, ← CommRingCat.comp_apply, Category.assoc,
      Iso.inv_hom_id_assoc, GlobalTheory.ProperFinite.topIso_inv_appTop]
  rw [e] at h1
  have hi : IsIso (X.presheaf.map (homOfLE hle).op) := by
    rw [show homOfLE hle = eqToHom (g ⁻¹ᵁ V).ι_image_top from Subsingleton.elim _ _]
    infer_instance
  exact (RingHom.finite_respectsIso.cancel_right_isIso _ (X.presheaf.map (homOfLE hle).op)).1 h1

theorem stein_factorisation : ∀ (X Y : Scheme.{0}) (g : X ⟶ Y), IsLocallyNoetherian Y → IsProper g → ∃ (Y' : Scheme.{0}) (a : X ⟶ Y') (b : Y' ⟶ Y), a ≫ b = g ∧ IsFinite b ∧ IsProper a ∧ Surjective a ∧ (∀ V : Y'.Opens, Function.Bijective (a.app V).hom) ∧ ∀ y : Y', _root_.IsPreconnected {x : X | a x = y} := by
  intro X Y g hY hg
  have hb : IsFinite g.fromNormalization := by
    refine { toIsAffineHom := inferInstance, finite_app := fun U hU => ?_ }
    have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI := (g.app U).hom.toAlgebra
    have : Module.Finite Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := finite_app_of_isProper g hU
    have : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, g ⁻¹ᵁ U)) :=
      Module.IsNoetherian.finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, g ⁻¹ᵁ U)).toSubmodule
    rw [g.fromNormalization_app hU]
    exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).2 (RingHom.finite_algebraMap.2 this)
  have hY' : IsLocallyNoetherian g.normalization := LocallyOfFiniteType.isLocallyNoetherian g.fromNormalization
  have ha : IsProper g.toNormalization := by
    have : IsProper (g.toNormalization ≫ g.fromNormalization) := by
      rw [g.toNormalization_fromNormalization]; exact hg
    exact IsProper.of_comp _ g.fromNormalization
  have hbij : ∀ V : g.normalization.Opens, Function.Bijective (g.toNormalization.app V).hom := by
    intro V
    refine ⟨g.toNormalization.app_injective V, fun t => ?_⟩
    obtain ⟨s, hs⟩ := GlobalTheory.mem_range_app_of_forall_isAffineOpen g.toNormalization V t fun W hW hWV => by
      have : IsNoetherianRing Γ(g.normalization, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
      exact GlobalTheory.mem_range_toNormalization_app g W _
        (RingHom.IsIntegral.of_finite (finite_app_of_isProper g.toNormalization hW) _)
    exact ⟨s, hs⟩
  have hs : Surjective g.toNormalization := by
    have h := g.toNormalization.denseRange.closure_range
    rw [g.toNormalization.isClosedMap.isClosed_range.closure_eq] at h
    exact ⟨Set.range_eq_univ.mp h⟩
  exact ⟨g.normalization, g.toNormalization, g.fromNormalization, g.toNormalization_fromNormalization, hb, ha, hs,
    hbij, fun y => GlobalTheory.T.zariski_connectedness_isPreconnected_fibre X _ g.toNormalization hY' ha hbij y⟩

end GlobalTheory.SteinFact
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem connectedSpace_pullback_of_finitelyGenerated_residue :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R),
      IsProper π → Surjective π → Function.Bijective π.appTop.hom →
      ∀ (K : Type) [Field K] (κ : ResidueField R →+* K) (L : Subfield K) (hL : ∀ x, κ x ∈ L) (n : ℕ) (c : Fin n → K),
        L = Subfield.closure (Set.range κ ∪ Set.range c) →
        ConnectedSpace (pullback π (spMap ((κ.codRestrict L hL).comp (residue R))) : Scheme.{0}) := by
  intro R _ _ _ S π hprop hsurj hbij K _ κ L hL n c hLc
  haveI := hprop
  haveI := hsurj
  have hc : ∀ j, c j ∈ L := fun j => hLc ▸ Subfield.subset_closure (Or.inr ⟨j, rfl⟩)
  set A := MvPolynomial (Fin n) R
  set ιC : R →+* A := MvPolynomial.C with hC
  set β : R →+* L := (κ.codRestrict L hL).comp (residue R) with hβ
  set φ : A →+* L := MvPolynomial.eval₂Hom β (fun j => ⟨c j, hc j⟩) with hφ
  have hφC : φ.comp ιC = β := by
    refine RingHom.ext fun r => ?_
    show MvPolynomial.eval₂ β (fun j => (⟨c j, hc j⟩ : L)) (MvPolynomial.C r) = β r
    exact MvPolynomial.eval₂_C _ _ _
  have hx : spMap β = spMap φ ≫ spMap ιC := by
    rw [← hφC]
    show Spec.map (CommRingCat.ofHom (φ.comp ιC)) = Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ιC)
    rw [← Spec.map_comp]; rfl

  have hdiv : ∀ x : L, ∃ a b : A, φ b ≠ 0 ∧ φ b * x = φ a := by
    have hsub : Subring.closure (Set.range κ ∪ Set.range c) ≤ (φ.range).map L.subtype := by
      rw [Subring.closure_le]
      rintro y (⟨z, rfl⟩ | ⟨j, rfl⟩)
      · obtain ⟨r, rfl⟩ := residue_surjective z
        exact ⟨β r, ⟨MvPolynomial.C r, MvPolynomial.eval₂_C _ _ _⟩, rfl⟩
      · exact ⟨⟨c j, hc j⟩, ⟨MvPolynomial.X j, MvPolynomial.eval₂_X _ _ _⟩, rfl⟩
    intro x
    have hx' : (x : K) ∈ Subfield.closure (Set.range κ ∪ Set.range c) := hLc ▸ x.2
    obtain ⟨y, hy, z, hz, hyz⟩ := Subfield.mem_closure_iff.1 hx'
    obtain ⟨y', ⟨a, rfl⟩, rfl⟩ := hsub hy
    obtain ⟨z', ⟨b, rfl⟩, rfl⟩ := hsub hz
    by_cases hb : φ b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      have : (x : K) = 0 := by rw [← hyz]; simp [hb]
      have : x = 0 := Subtype.ext this
      simp [this]
    · refine ⟨a, b, hb, ?_⟩
      apply Subtype.ext
      have hb' : ((φ b : L) : K) ≠ 0 := fun h => hb (Subtype.ext h)
      simp only [Subfield.coe_mul, L.subtype_apply] at hyz ⊢
      rw [← hyz]; field_simp
  have hstalk : φ.SurjectiveOnStalks := by
    refine RingHom.surjectiveOnStalks_of_exists_div fun x => ?_
    obtain ⟨a, b, hb, e⟩ := hdiv x
    exact ⟨a, b, (isUnit_iff_ne_zero).2 hb, e⟩
  haveI hpre : IsPreimmersion (spMap φ) := by
    rw [IsPreimmersion.SpecMap_iff]
    refine ⟨?_, hstalk⟩
    haveI : Subsingleton (PrimeSpectrum L) := inferInstance
    exact Topology.IsEmbedding.of_subsingleton _

  set π' : pullback π (spMap ιC) ⟶ Sp A := pullback.snd π (spMap ιC) with hπ'
  have hflat : Flat (spMap ιC) := by
    refine Flat.SpecMap_iff.2 ?_
    show (algebraMap R A).Flat
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have hbij' : ∀ V : (Sp A).Opens, Function.Bijective (π'.app V).hom :=
    GlobalTheory.Mum.app_bijective_of_flat_baseChange R S (Sp A) _ π (spMap ιC) _ _ inferInstance inferInstance
      hbij hflat (IsPullback.of_hasPullback π (spMap ιC)).flip
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum L) := inferInstance
  have hconn := GlobalTheory.T.zariski_connectedness_isPreconnected_fibre _ _ π' inferInstance inferInstance hbij' (spMap φ q)
  have hrange : Set.range (spMap φ) = {spMap φ q} := by
    ext y
    constructor
    · rintro ⟨q', rfl⟩; rw [Subsingleton.elim q' q]; rfl
    · rintro rfl; exact ⟨q, rfl⟩
  set f := pullback.fst π' (spMap φ) with hf
  have hfr : Set.range f = {s | π' s = spMap φ q} := by
    rw [hf, Scheme.Pullback.range_fst, hrange]; rfl
  have hP : PreconnectedSpace ↥(pullback π' (spMap φ)) := by
    refine ⟨?_⟩
    rw [← f.isEmbedding.isInducing.isPreconnected_image, Set.image_univ, hfr]
    exact hconn
  have e : pullback π (spMap β) ≅ pullback π' (spMap φ) :=
    pullback.congrHom rfl hx ≪≫ (pullbackLeftPullbackSndIso π (spMap ιC) (spMap φ)).symm
  obtain ⟨z, -⟩ := (pullback.snd π (spMap β)).surjective q
  haveI : ConnectedSpace ↥(pullback π' (spMap φ)) := ConnectedSpace.mk ⟨e.hom z⟩
  exact (Scheme.homeoOfIso e).symm.surjective.connectedSpace (Scheme.homeoOfIso e).symm.continuous

end GlobalTheory.Mum
end
