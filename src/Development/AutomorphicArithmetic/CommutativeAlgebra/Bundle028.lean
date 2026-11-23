module

public import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle014
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle019
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle023
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle021
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle022
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle013
public import Development.EtaleCohomology.EtaleSheaves.Bundle028
public import Development.EtaleCohomology.EtaleSheaves.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle001
import Development.EtaleCohomology.EtaleSheaves.Bundle055

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.MvLin

variable {R : Type} [CommRing R]

private noncomputable abbrev pb {E' E : Spc} (π : E' ⟶ E) {I : Cx R} {n : ℤ} (a : Cochain ((chains R).obj E) I n) :
    Cochain ((chains R).obj E') I n :=
  (Cochain.ofHom ((chains R).map π)).comp a (zero_add n)

private noncomputable abbrev pbz {E' E : Spc} (π : E' ⟶ E) {I : Cx R} {n : ℤ} (a : Cocycle ((chains R).obj E) I n) :
    Cocycle ((chains R).obj E') I n :=
  zcomp (Cocycle.ofHom ((chains R).map π)) a (zero_add n)

private theorem pb_comp {E'' E' E : Spc} (π : E'' ⟶ E') (ρ : E' ⟶ E) {I : Cx R} {n : ℤ}
    (a : Cochain ((chains R).obj E) I n) : pb (π ≫ ρ) a = pb π (pb ρ a) := by
  simp only [pb, Functor.map_comp]
  rw [Cochain.ofHom_comp]
  exact Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ (zero_add n)

private theorem sub_map {E' E : Spc} (π : E' ⟶ E) {N : ℕ} {U : Scheme.{0}} (x : Sx E' N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.map π).sub j l h = (x.sub j l h).map π :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (π.naturality (SimplexCategory.subinterval j l h).op) (op U)) x).symm

private theorem ev_pb {E' E : Spc} (π : E' ⟶ E) {I : Cx R} {n : ℤ} (a : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E' p U) :
    ev (pb π a) p s h U x = ev a p s h U (x.map π) := by
  have hp := CupSpec.ev_pull π a p s h U x
  exact hp

private theorem aw_pb {I J K : Cx R} (μ : Pair I J K) {E' E : Spc} (π : E' ⟶ E) {n m k : ℤ} (hk : n + m = k)
    {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m} {c : Cochain ((chains R).obj E) K k}
    (h : μ.IsAW hk a b c) : μ.IsAW hk (pb π a) (pb π b) (pb π c) := by
  intro N w hw U x
  rw [ev_pb, h N w hw U (x.map π)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_pb, ev_pb, sub_map, sub_map]

private theorem aw_unique {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m} {c c' : Cochain ((chains R).obj E) K k}
    (h : μ.IsAW hk a b c) (h' : μ.IsAW hk a b c') : c = c' :=
  ((GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ hk).1 a b).unique h h'

private theorem aw_zero {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (a : Cochain ((chains R).obj E) I n) : μ.IsAW hk a (0 : Cochain ((chains R).obj E) J m) 0 := by
  obtain ⟨z, hz, -⟩ := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ hk).1 a (0 : Cochain ((chains R).obj E) J m)
  have h2 := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ hk).2.2 a 0 0 z z hz hz
  rw [add_zero] at h2
  have h3 : z + z = z := aw_unique μ hk h2 hz
  have h4 : z = 0 := by simpa using h3
  exact h4 ▸ hz

private theorem aw_delta {I J K : Cx R} (μ : Pair I J K) {E' E : Spc} (π : E' ⟶ E) {n m : ℤ}
    {a : Cochain ((chains R).obj E') I n} {z : Cocycle ((chains R).obj E) I (n + 1)} {η : Cocycle ((chains R).obj E) J m}
    {a' : Cochain ((chains R).obj E') K (n + m)} {z' : Cochain ((chains R).obj E) K (n + m + 1)}
    (hk : n + 1 + m = n + m + 1) (ha : δ n (n + 1) a = pb π z.1) (h1 : μ.IsAW rfl a (pbz π η).1 a')
    (h2 : μ.IsAW hk z.1 η.1 z') : δ (n + m) (n + m + 1) a' = pb π z' := by
  have h3 : μ.IsAW hk (δ n (n + 1) a) (pbz π η).1 (pb π z') := ha ▸ aw_pb μ π hk h2
  have h4 : μ.IsAW (by omega : n + (m + 1) = n + m + 1) a (δ m (m + 1) (pbz π η).1) 0 := by
    rw [Cocycle.δ_eq_zero]
    exact aw_zero μ _ a
  have h5 := GlobalTheory.T.alexanderWhitney_cup_leibniz_etale R μ rfl a (pbz π η).1 a' (pb π z') 0 h1 h3 h4
  simpa using h5

private theorem mv_core {I J K : Cx R} (μ : Pair I J K) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) {n m : ℤ}
    (γ : Cocycle ((chains R).obj (pullback f g)) I n) (ζ : Cocycle ((chains R).obj E) I (n + 1))
    (α : Cochain ((chains R).obj U) I n) (β : Cochain ((chains R).obj V) I n)
    (η : Cocycle ((chains R).obj E) J m)
    (hγ : pb (pullback.fst f g) α - pb (pullback.snd f g) β = γ.1)
    (hα : δ n (n + 1) α = pb f ζ.1) (hβ : δ n (n + 1) β = pb g ζ.1) (hk : n + 1 + m = n + m + 1) :
    ∃ (γ' : Cocycle ((chains R).obj (pullback f g)) K (n + m)) (ζ' : Cocycle ((chains R).obj E) K (n + m + 1))
      (α' : Cochain ((chains R).obj U) K (n + m)) (β' : Cochain ((chains R).obj V) K (n + m)),
      μ.IsAW rfl γ.1 (pbz (pullback.fst f g ≫ f) η).1 γ'.1 ∧ μ.IsAW hk ζ.1 η.1 ζ'.1 ∧
      pb (pullback.fst f g) α' - pb (pullback.snd f g) β' = γ'.1 ∧
      δ (n + m) (n + m + 1) α' = pb f ζ'.1 ∧ δ (n + m) (n + m + 1) β' = pb g ζ'.1 := by
  obtain ⟨γ', hγ'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ rfl).1 γ (pbz (pullback.fst f g ≫ f) η)
  obtain ⟨ζ', hζ'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ hk).1 ζ η
  obtain ⟨α', hα', -⟩ := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ rfl).1 α (pbz f η).1
  obtain ⟨β', hβ', -⟩ := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ rfl).1 β (pbz g η).1
  refine ⟨γ', ζ', α', β', hγ', hζ', ?_, aw_delta μ f hk hα hα' hζ', aw_delta μ g hk hβ hβ' hζ'⟩
  have e1 : pb (pullback.fst f g) (pbz f η).1 = (pbz (pullback.fst f g ≫ f) η).1 := (pb_comp _ _ _).symm
  have e2 : pb (pullback.snd f g) (pbz g η).1 = (pbz (pullback.fst f g ≫ f) η).1 :=
    (pb_comp _ _ _).symm.trans (by rw [pullback.condition]; rfl)
  have a1 := aw_pb μ (pullback.fst f g) rfl hα'
  have a2 := aw_pb μ (pullback.snd f g) rfl hβ'
  rw [e1] at a1
  rw [e2] at a2
  have a3 := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ rfl).2.1 _ _ _ _ _ hγ' a2
  have e3 : γ.1 + pb (pullback.snd f g) β = pb (pullback.fst f g) α := by rw [← hγ, sub_add_cancel]
  rw [e3] at a3
  have e4 := aw_unique μ rfl a1 a3
  rw [e4, add_sub_cancel_right]

private theorem cast_cup (q : ℕ) {E : Spc} {n m k i j : ℤ} (hk : n + m = k) (a : Ht q E n i) (b : Ht q E m j) :
    (cup q a b).cast hk rfl = (twPair q i j).cup E hk a b := by
  subst hk
  rfl

end UpperTheory.MvLin

open UpperTheory.MvLin in
theorem UpperTheory.mayerVietorisConnecting_cup_pullback :
    ∀ (q : ℕ) [NeZero q] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 (ZMod q) f g → ∀ (n m i j : ℤ) (c : Ht q (pullback f g) n i)
        (x : Ht q E (n + 1) i) (y : Ht q E m j), IsMVd f g (tw q i) n c x →
        IsMVd f g (tw q (i + j)) (n + m) (cup q c (pull _ (pullback.fst f g ≫ f) _ _ y)) ((cup q x y).cast (by ring) rfl) := by
  intro q _ U V E f g _ n m i j c x y h
  obtain ⟨γ, ζ, α, β, rfl, rfl, hγ, hα, hβ⟩ := h
  obtain ⟨η, rfl⟩ := y.mk_surjective
  have hk : n + 1 + m = n + m + 1 := by ring
  obtain ⟨γ', ζ', α', β', h1, h2, h3, h4, h5⟩ := mv_core (twPair q i j) f g γ ζ α β η hγ hα hβ hk
  refine ⟨γ', ζ', α', β', ?_, ?_, h3, h4, h5⟩
  · exact ((GlobalTheory.T.cup_eq_class_of_isAW _ (twPair q i j) rfl).2 γ _ γ' h1).symm
  · rw [cast_cup q hk]
    exact ((GlobalTheory.T.cup_eq_class_of_isAW _ (twPair q i j) hk).2 ζ η ζ' h2).symm
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem pull_bij (q : ℕ) {A B : Spc} (f : A ⟶ B) [IsIso f] (n i : ℤ) :
    Function.Bijective (fun x : Ht q B n i => (pull _ f _ _ x : Ht q A n i)) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun y => pull _ (inv f) _ _ y, fun x => ?_, fun y => ?_⟩
  · show pull _ (inv f) _ _ (pull _ f _ _ x) = x
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · show pull _ f _ _ (pull _ (inv f) _ _ y) = y
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]

private theorem pull_cup (q : ℕ) {A B : Spc} (f : A ⟶ B) {n m i j : ℤ} (a : Ht q B n i) (b : Ht q B m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b) :=
  GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b

private theorem pull_cast' (q : ℕ) {A B : Spc} (f : A ⟶ B) {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q B n i) : pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q A n i) := by
  subst hn; subst hi; rfl

theorem UpperTheory.lerayHirsch_of_iso_square :
    ∀ (q : ℕ) [NeZero q] {X X' E E' : Spc} (π : X ⟶ E) (π' : X' ⟶ E') (u : X' ⟶ X) (b : E' ⟶ E) [IsIso u] [IsIso b], u ≫ π = π' ≫ b →
        ∀ {m : ℕ} (d e : Fin m → ℤ) (c : ∀ j, Ht q X (d j) (e j)), LH q π d e c → LH q π' d e (fun j => pull _ u _ _ (c j)) := by
  intro q _ X X' E E' π π' u b _ _ w m d e c h n i
  have hP : Function.Bijective (fun (a : ∀ j, Ht q E (n - d j) (i - e j)) j =>
      (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) :=
    ⟨fun a a' haa => funext fun j => (pull_bij q b _ _).1 (congrFun haa j),
      fun y => ⟨fun j => ((pull_bij q b _ _).2 (y j)).choose,
        funext fun j => ((pull_bij q b _ _).2 (y j)).choose_spec⟩⟩
  have hc : ∀ a : ∀ j, Ht q E (n - d j) (i - e j),
      (∑ j, ((cup q (pull _ π' _ _ (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) (pull _ u _ _ (c j))).cast
        (by ring) (by ring) : Ht q X' n i)) =
      pull _ u _ _ (∑ j, ((cup q (pull _ π _ _ (a j)) (c j)).cast (by ring) (by ring) : Ht q X n i)) := by
    intro a

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pull_cast', pull_cup, ← pull_comp, ← pull_comp, w]
  have hcomp := (pull_bij q u n i).comp (h n i)
  have heq : (fun y : ∀ j, Ht q E' (n - d j) (i - e j) =>
      ∑ j, ((cup q (pull _ π' _ _ (y j)) (pull _ u _ _ (c j))).cast (by ring) (by ring) : Ht q X' n i)) ∘
      (fun (a : ∀ j, Ht q E (n - d j) (i - e j)) j =>
        (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) =
      (fun x : Ht q X n i => (pull _ u _ _ x : Ht q X' n i)) ∘ (fun a : ∀ j, Ht q E (n - d j) (i - e j) =>
        ∑ j, ((cup q (pull _ π _ _ (a j)) (c j)).cast (by ring) (by ring) : Ht q X n i)) :=
    funext hc
  rw [← heq] at hcomp
  exact (Function.Bijective.of_comp_iff _ hP).1 hcomp
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem key (aw : LeafAW) (q : ℕ) [NeZero q] {X : Scheme.{0}} (U : X.Opens) {E : Spc}
    (π : E ⟶ sch.obj X) (m j i : ℤ) (c : Hs q (opn U) m j) (β : Sec ((res _ (tw q j)).X m) X)
    (hβ : IsRep U β c.1)
    (Φ : (famDC (Sub.bot E) (res _ (tw q i)) 0).Hom
      (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) (res _ (tw q (i + j))) m))
    (hP : IsProd (twPair q i j) π β Φ) (hO : Φ.Ok) :
    (∀ n : ℤ, Function.Bijective fun a : Ht q E n i =>
      Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c)) ↔ Φ.TotEx := by
  exact UpperTheory.bijective_iff_totalQuasiIso_of_totalModels _ _ Φ (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) hO
    (fun n => Ht q E n i) (fun n => ↥(Hs q (abv U π) (n + m) (i + j)))
    (fun n x a => HRel x a) (fun n x b => SRel x (b : Ht q (dbl (abv U π)) (n + m) (i + j)))
    (fun n a => Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c))
    (fun n => UpperTheory.supportDoubleComplex_bot_totalModel _ _ _ n) (fun n => UpperTheory.relativeCohomology_isTotalModel_of_image q (abv U π) (i + j) m n (n + m) rfl)
    (fun n x a h => UpperTheory.relativeCupProduct_realizes_product_of_representative aw q U π m j i n c β hβ Φ hP x a h)

theorem UpperTheory.productLevelwise_of_alexanderWhitney :
    LeafAW → LeafPrdLevel := by
  intro aw _ q _ X U E π m j c hlev n i
  obtain ⟨β, hβ⟩ := UpperTheory.exists_section_representing_relativeClass q X U m j c
  obtain ⟨Φ, hP, hO⟩ := UpperTheory.exists_cupProduct_hom_of_cocycle_vanishing_on_open _ (twPair q i j) U π m β hβ.1 hβ.2.1
  have hT : Φ.TotEx := by
    refine UpperTheory.totalExact_of_columnExact _ _ Φ (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) hO ?_
    intro p
    obtain ⟨Ψ, hPΨ, hOΨ⟩ := UpperTheory.exists_cupProduct_hom_of_cocycle_vanishing_on_open _ (twPair q i j) U
      (disc.map (π.app (op { len := p }))) m β hβ.1 hβ.2.1
    refine UpperTheory.relativeCupProduct_levelwise_compat _ (twPair q i j) U π m β p Φ Ψ hP hPΨ ?_
    exact (key aw q U (disc.map (π.app (op { len := p }))) m j i c β hβ Ψ hPΨ hOΨ).1
      (fun n' => hlev (op { len := p }) n' i)
  exact (key aw q U π m j i c β hβ Φ hP hO).2 hT n
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

theorem UpperTheory.exists_fiber_pullback_square_of_open_immersions :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
      ∃ (r : pullback (fibMap p ι₁) (fibMap p ι₂) ⟶ pullback ι₁ ι₂) (c : pullback (fibMap p ι₁) (fibMap p ι₂) ⟶ Spec (CommRingCat.of (ResidueField A))),
        IsPullback r c (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) (cpt A) ∧
        r ≫ pullback.fst ι₁ ι₂ = pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ∧
        r ≫ pullback.snd ι₁ ι₂ = pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) := by
  intro A _ _ Z U V p ι₁ ι₂
  have m1 : ∀ {Y : Scheme.{0}} (ι : Y ⟶ Z), fibMap p ι ≫ pullback.fst p (cpt A) = pullback.fst (ι ≫ p) (cpt A) ≫ ι := by
    intro Y ι
    exact pullback.lift_fst _ _ _
  have m2 : ∀ {Y : Scheme.{0}} (ι : Y ⟶ Z), fibMap p ι ≫ pullback.snd p (cpt A) = pullback.snd (ι ≫ p) (cpt A) := by
    intro Y ι
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have m1' : ∀ {Y W : Scheme.{0}} (ι : Y ⟶ Z) (k : Z ⟶ W), fibMap p ι ≫ pullback.fst p (cpt A) ≫ k = pullback.fst (ι ≫ p) (cpt A) ≫ ι ≫ k := by
    intro Y W ι k
    rw [← Category.assoc, m1, Category.assoc]
  have m2' : ∀ {Y W : Scheme.{0}} (ι : Y ⟶ Z) (k : _ ⟶ W), fibMap p ι ≫ pullback.snd p (cpt A) ≫ k = pullback.snd (ι ≫ p) (cpt A) ≫ k := by
    intro Y W ι k
    rw [← Category.assoc, m2]
  have hr1 : (pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A)) ≫ ι₁ =
      (pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A)) ≫ ι₂ := by
    rw [Category.assoc, Category.assoc, ← m1, ← m1, ← Category.assoc, pullback.condition, Category.assoc]
  let r := pullback.lift _ _ hr1
  let c := pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.snd (ι₁ ≫ p) (cpt A)
  refine ⟨r, c, ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have cond : pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ ≫ p = pullback.snd (ι₁ ≫ p) (cpt A) ≫ cpt A := by
    exact pullback.condition
  have w : r ≫ pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p = c ≫ cpt A := by
    simp only [r, c, pullback.lift_fst_assoc, Category.assoc, cond]
  have cond2 : pullback.fst ι₁ ι₂ ≫ ι₁ = pullback.snd ι₁ ι₂ ≫ ι₂ := pullback.condition
  have L : ∀ (s : PullbackCone (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) (cpt A)),
      ∃ l : s.pt ⟶ pullback (fibMap p ι₁) (fibMap p ι₂), l ≫ r = s.fst ∧ l ≫ c = s.snd ∧
        ∀ m : s.pt ⟶ pullback (fibMap p ι₁) (fibMap p ι₂), m ≫ r = s.fst → m ≫ c = s.snd → m = l := by
    intro s
    have hs : s.fst ≫ pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p = s.snd ≫ cpt A := s.condition
    have hs1 : (s.fst ≫ pullback.fst ι₁ ι₂) ≫ ι₁ ≫ p = s.snd ≫ cpt A := by
      rw [Category.assoc]
      exact hs
    have hs2 : (s.fst ≫ pullback.snd ι₁ ι₂) ≫ ι₂ ≫ p = s.snd ≫ cpt A := by
      rw [Category.assoc, ← Category.assoc (pullback.snd ι₁ ι₂), ← cond2, Category.assoc]
      exact hs
    let x₁ := pullback.lift _ _ hs1
    let x₂ := pullback.lift _ _ hs2
    have hx : x₁ ≫ fibMap p ι₁ = x₂ ≫ fibMap p ι₂ := by
      apply pullback.hom_ext
      · simp only [x₁, x₂, Category.assoc, m1, pullback.lift_fst_assoc, cond2]
      · simp only [x₁, x₂, Category.assoc, m2, pullback.lift_snd]
    refine ⟨pullback.lift x₁ x₂ hx, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp only [r, x₁, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · simp only [r, x₂, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_fst]
    · simp only [c, x₁, pullback.lift_fst_assoc, pullback.lift_snd]
    · intro m hm1 hm2
      have e1 : m ≫ pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) = s.fst ≫ pullback.fst ι₁ ι₂ := by
        rw [← hm1, Category.assoc, pullback.lift_fst]
      have e2 : m ≫ pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) = s.fst ≫ pullback.snd ι₁ ι₂ := by
        rw [← hm1, Category.assoc, pullback.lift_snd]
      have e3 : m ≫ pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.snd (ι₁ ≫ p) (cpt A) = s.snd := hm2
      have e4 : m ≫ pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.snd (ι₂ ≫ p) (cpt A) = s.snd := by
        rw [← m2 ι₂, ← pullback.condition_assoc, m2 ι₁]
        exact e3
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, x₁, e1]
        · simp only [Category.assoc, pullback.lift_fst, x₁, e3, pullback.lift_snd]
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_snd, x₂, e2, pullback.lift_fst]
        · simp only [Category.assoc, pullback.lift_snd, x₂, e4]
  choose l hl1 hl2 hl3 using L
  exact IsPullback.of_isLimit (c := PullbackCone.mk r c w)
    (PullbackCone.IsLimit.mk w l hl1 hl2 (fun s m h1 h2 => hl3 s m h1 h2))

end
end

section

open IsLocalRing AlgebraicGeometry CategoryTheory

namespace UpperTheory.LocallyOfRingHomAway

private theorem exists_away (Ω R : Type) [Field Ω] [IsAlgClosed Ω] [CommRing R] [IsDomain R]
    [Algebra Ω R] [Algebra.FiniteType Ω R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R ≤ 1) (hnf : ¬ IsField R) (m : Ideal R) [hm : m.IsMaximal] :
    ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension 1 Ω (Localization.Away f) := by
  have hnoeth : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing Ω R
  have hkd : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff]
    exact_mod_cast hdim
  have hdl : Ring.DimensionLEOne R :=
    ⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩
  have hded : IsDedekindDomain R := { }
  have hmbot : m ≠ ⊥ := by
    intro h
    apply hnf
    rw [Ring.isField_iff_maximal_bot]
    rw [← h]
    exact hm
  let S := Localization.AtPrime m
  have hdvr : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hmbot S
  have hreg : IsRegularLocalRing S := inferInstance
  have hsm : Algebra.FormallySmooth Ω S :=
    GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField Ω S
  have het : Algebra.FormallyEtale Ω (ResidueField S) :=
    GlobalTheory.formallyEtale_residueField_of_isMaximal Ω Ω m S
  obtain ⟨_, hrk⟩ := GlobalTheory.free_and_finrank_kaehler_eq_finrank_cotangentSpace Ω S
  have hcot : Module.finrank (ResidueField S) (CotangentSpace S) = 1 := by
    have h1 := (IsRegularLocalRing.iff_finrank_cotangentSpace S).mp hreg
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one S] at h1
    exact_mod_cast h1
  have hfp : Algebra.FinitePresentation Ω R :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hsa : Algebra.IsSmoothAt Ω m := hsm
  exact GlobalTheory.exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt Ω m (hrk.trans hcot)

private theorem locally_of_ringHom (Ω R : Type) [Field Ω] [IsAlgClosed Ω] [CommRing R] [IsDomain R]
    (ψ : Ω →+* R) (hft : ψ.FiniteType) (hic : IsIntegrallyClosed R)
    (hdim : ringKrullDim R ≤ 1) (hnf : ¬ IsField R) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) ψ := by
  letI : Algebra Ω R := ψ.toAlgebra
  haveI : Algebra.FiniteType Ω R := hft
  refine ⟨{t | RingHom.IsStandardSmoothOfRelativeDimension 1
    ((algebraMap R (Localization.Away t)).comp ψ)}, ?_, fun t ht => ht⟩
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨f, hf, hsm⟩ := exists_away Ω R hdim hnf M
  apply hf
  apply hle
  apply Ideal.subset_span
  have heq : ((algebraMap R (Localization.Away f)).comp ψ).toAlgebra =
      (inferInstance : Algebra Ω (Localization.Away f)) :=
    Algebra.algebra_ext _ _ (fun r => (IsScalarTower.algebraMap_apply Ω R _ r).symm)
  show @Algebra.IsStandardSmoothOfRelativeDimension 1 Ω (Localization.Away f) _ _
    ((algebraMap R (Localization.Away f)).comp ψ).toAlgebra
  rw [heq]
  exact hsm

end UpperTheory.LocallyOfRingHomAway

theorem UpperTheory.smooth_of_normal_curve_perfectField :
    LateralTheory.E.LeafModelCurveCut.LeafSmoothOfNormal := by
  intro Ω _ _ C c hint hlft hic hdim
  have key : ∀ (V : C.Opens) (hV : IsAffineOpen V) (a b : C), a ∈ V → b ∈ V → a ≠ b →
      RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
        (c.appLE ⊤ V (by simp)).hom := by
    intro V hV a b ha hb hab
    haveI : Nonempty V := ⟨⟨a, ha⟩⟩
    have hdom : IsDomain Γ(C, V) := inferInstance
    let ι := (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv
    let ψ : Ω →+* Γ(C, V) := (c.appLE ⊤ V (by simp)).hom.comp ι.symm.toRingHom
    have hφ : (c.appLE ⊤ V (by simp)).hom = ψ.comp ι.toRingHom := by
      ext r
      simp [ψ]
    rw [hφ]
    apply (RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso).right
    apply UpperTheory.LocallyOfRingHomAway.locally_of_ringHom Ω Γ(C, V) ψ
    · have hft : (c.appLE ⊤ V (by simp)).hom.FiniteType :=
        HasRingHomProperty.appLE @LocallyOfFiniteType c hlft ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
      exact hft.comp (RingHom.FiniteType.of_surjective _ ι.symm.surjective)
    · refine IsIntegrallyClosed.of_localization_maximal (fun p _ hp => ?_)
      let y : PrimeSpectrum Γ(C, V) := ⟨p, hp.isPrime⟩
      have hy : hV.fromSpec y ∈ V := by
        have : hV.fromSpec y ∈ Set.range hV.fromSpec := ⟨y, rfl⟩
        rwa [hV.range_fromSpec] at this
      letI := TopCat.Presheaf.algebra_section_stalk C.presheaf ⟨hV.fromSpec y, hy⟩
      haveI hloc : IsLocalization p.primeCompl (C.presheaf.stalk (hV.fromSpec y)) :=
        hV.isLocalization_stalk' y hy
      exact (hic (hV.fromSpec y)).of_equiv
        (IsLocalization.algEquiv p.primeCompl (C.presheaf.stalk (hV.fromSpec y))
          (Localization.AtPrime p)).toRingEquiv
    · rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(C, V)]
      change topologicalKrullDim (Spec Γ(C, V)) ≤ 1
      rw [← IsHomeomorph.topologicalKrullDim_eq _ hV.isoSpec.hom.homeomorph.isHomeomorph]
      exact (topologicalKrullDim_subspace_le C V).trans hdim.le
    · intro hf
      letI := hf.toField
      have ha' : a ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact ha
      have hb' : b ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hb
      obtain ⟨pa, rfl⟩ := ha'
      obtain ⟨pb, rfl⟩ := hb'
      have hss : Subsingleton (PrimeSpectrum Γ(C, V)) := inferInstance
      exact hab (congrArg _ (hss.elim pa pb))
  have hgen : ∀ (W : C.Opens) (z : C), z ∈ W → genericPoint C ∈ W := by
    intro W z hz
    exact ((genericPoint_spec C).mem_open_set_iff W.isOpen).mpr ⟨z, trivial, hz⟩
  have hexists : ∃ z : C, z ≠ genericPoint C := by
    by_contra h
    push_neg at h
    have hsub : Subsingleton (TopologicalSpace.IrreducibleCloseds C) := by
      refine ⟨fun s t => ?_⟩
      obtain ⟨p, hp⟩ := s.isIrreducible.nonempty
      obtain ⟨q, hq⟩ := t.isIrreducible.nonempty
      ext y
      rw [h y]
      exact ⟨fun _ => h q ▸ hq, fun _ => h p ▸ hp⟩
    have h0 := Order.krullDim_nonpos_of_subsingleton (α := TopologicalSpace.IrreducibleCloseds C)
    unfold topologicalKrullDim at hdim
    rw [hdim] at h0
    exact absurd h0 (by norm_num)
  rw [HasRingHomProperty.iff_exists_appLE (P := @SmoothOfRelativeDimension 1)
    (RingHom.locally_stableUnderCompositionWithLocalizationAwaySource
      (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway 1).left)]
  intro x
  by_cases hx : x = genericPoint C
  · obtain ⟨z, hz⟩ := hexists
    obtain ⟨W, hW, hzW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ z)
    refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨W, hW⟩, hx ▸ hgen W z hzW, by simp, ?_⟩
    exact key W hW z (genericPoint C) hzW (hgen W z hzW) hz
  · obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ x)
    refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨W, hW⟩, hxW, by simp, ?_⟩
    exact key W hW x (genericPoint C) hxW (hgen W x hxW) hx
end
