module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsProductsCosocles
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Transport

variable {F F' : Type} [Field F] [Field F'] (r : F ≃+* F')

private theorem coe_phi {n : ℕ} (x : GL (Fin n) F) :
    ((Matrix.GeneralLinearGroup.map r.toRingHom x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (x : Matrix (Fin n) (Fin n) F).map r := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

private def phiE (n : ℕ) : GL (Fin n) F ≃ GL (Fin n) F' where
  toFun := Matrix.GeneralLinearGroup.map r.toRingHom
  invFun := Matrix.GeneralLinearGroup.map r.symm.toRingHom
  left_inv x := by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]
  right_inv x := by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]

private theorem inPar_phi (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    InPar a (Matrix.GeneralLinearGroup.map r.toRingHom x) ↔ InPar a x := by
  unfold InPar
  simp only [coe_phi, Matrix.map_apply]
  constructor
  · intro h i j hj hi
    exact (map_eq_zero_iff r r.injective).1 (h i j hj hi)
  · intro h i j hj hi
    rw [h i j hj hi, map_zero]

private theorem ent_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) :
    ent (M.map r) i j = r (ent M i j) := by
  unfold ent
  split_ifs
  · rfl
  · exact (map_zero r).symm

private theorem tl_map (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    tl a (M.map r) = (tl a M).map r := by
  ext i j
  simp [tl, ent_map]

private theorem br_map (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    br a b (M.map r) = (br a b M).map r := by
  ext i j
  simp [br, ent_map]

private theorem isUnit_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    IsUnit (M.map r) ↔ IsUnit M := by
  have := isUnit_map_iff (r.mapMatrix (m := Fin n)) M
  simpa [RingEquiv.mapMatrix_apply] using this

private theorem coe_toG {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsUnit M) :
    ((toG M : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = M := by
  unfold toG
  rw [dite_eq_left h]
  rfl

private theorem toG_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    toG (M.map r) = Matrix.GeneralLinearGroup.map r.toRingHom (toG M) := by
  by_cases h : IsUnit M
  · apply Units.ext
    rw [coe_toG ((isUnit_map r M).2 h), coe_phi, coe_toG h]
  · have h' : ¬ IsUnit (M.map r) := fun k => h ((isUnit_map r M).1 k)
    unfold toG
    rw [dite_eq_right h, dite_eq_right h', map_one]

private theorem tlG_phi (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    tlG a (Matrix.GeneralLinearGroup.map r.toRingHom x) =
      Matrix.GeneralLinearGroup.map r.toRingHom (tlG a x) := by
  unfold tlG
  rw [coe_phi, tl_map, toG_map]

private theorem brG_phi (a b : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    brG a b (Matrix.GeneralLinearGroup.map r.toRingHom x) =
      Matrix.GeneralLinearGroup.map r.toRingHom (brG a b x) := by
  unfold brG
  rw [coe_phi, br_map, toG_map]

include r in
private theorem card_phi (a n : ℕ) :
    Nat.card {p : GL (Fin n) F' // InPar a p} = Nat.card {p : GL (Fin n) F // InPar a p} :=
  (Nat.card_congr ((phiE r n).subtypeEquiv fun x => (inPar_phi r a x).symm)).symm

private theorem gal_id {K : Type} [Field K] (n : ℕ) (y : GL (Fin n) K) : gal (RingHom.id K) n y = y := by
  apply Units.ext
  ext i j
  simp [gal, Matrix.GeneralLinearGroup.map_apply]

private theorem hc_phi (a b : ℕ) (α : GL (Fin a) F' → ℂ) (β : GL (Fin b) F' → ℂ) (n : ℕ)
    (g : GL (Fin n) F) :
    hc a b α β n (Matrix.GeneralLinearGroup.map r.toRingHom g) =
      hc a b (fun x => α (Matrix.GeneralLinearGroup.map r.toRingHom x))
        (fun x => β (Matrix.GeneralLinearGroup.map r.toRingHom x)) n g := by
  unfold hc hcTw
  simp only [gal_id]
  rw [card_phi r a n, ← finsum_comp_equiv (phiE r n)]
  congr 1
  refine finsum_congr fun y => ?_
  have e : (phiE r n y)⁻¹ * Matrix.GeneralLinearGroup.map r.toRingHom g * phiE r n y =
      Matrix.GeneralLinearGroup.map r.toRingHom (y⁻¹ * g * y) := by
    simp only [map_mul, map_inv]
    rfl
  rw [e]
  simp only [inPar_phi, tlG_phi, brG_phi]

private theorem detc_phi (j : AlgebraicClosure F ≃+* AlgebraicClosure F')
    (hj : ∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) (θ : AlgebraicClosure F' →* ℂ)
    (t k : ℕ) (x : GL (Fin t) F) :
    detc θ t k (Matrix.GeneralLinearGroup.map r.toRingHom x) = detc (θ.comp j.toMonoidHom) t k x := by
  unfold detc
  have e : ((x : Matrix (Fin t) (Fin t) F).map r).det = r (x : Matrix (Fin t) (Fin t) F).det :=
    (RingHom.map_det r.toRingHom _).symm
  rw [coe_phi, e, ← hj]
  rfl

end Transport

theorem UpperTheory.Gal.InertialTypesAlt.jdIso :
    CuspIso → JDIso := by
  intro hC F F' _ _ _ r j hj θ D L n g
  have hJ : ∀ (L : List (ℕ × ℕ)) (n : ℕ) (g : GL (Fin n) F),
      J θ L n (Matrix.GeneralLinearGroup.map r.toRingHom g) = J (θ.comp j.toMonoidHom) L n g := by
    intro L
    induction L with
    | nil => intro n g; rfl
    | cons p L ih =>
      intro n g
      rw [J_cons, J_cons, hc_phi]
      congr 1
      · funext x
        exact hC F F' r j hj θ p.1 p.2 x
      · funext x
        exact ih _ x
  induction D generalizing n g with
  | nil => exact hJ L n g
  | cons p D ih =>
    rw [JD_cons, JD_cons, hc_phi]
    congr 1
    · funext x
      exact detc_phi r j hj θ p.1 p.2 x
    · funext x
      exact ih _ x
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem frob_ne_one {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hp : (Module.finrank F F').Prime) (hs : ∀ z, s z = z ^ Nat.card F) :
    s ≠ 1 := by
  rintro rfl
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  haveI : Fintype F' := Fintype.ofFinite F'
  have hcard : Nat.card F' = Nat.card F ^ Module.finrank F F' := Module.natCard_eq_pow_finrank
  have hq : 1 < Nat.card F := Finite.one_lt_card
  generalize Nat.card F = q at hs hq hcard
  have hne : (X ^ q - X : F'[X]) ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hq
  have hdeg : (X ^ q - X : F'[X]).natDegree = q := Polynomial.natDegree_X_pow_sub_X (R := F') hq
  have hsub : (Finset.univ : Finset F') ⊆ (X ^ q - X : F'[X]).roots.toFinset := by
    intro z _
    rw [Multiset.mem_toFinset, mem_roots hne]
    have := hs z
    simp only [AlgEquiv.one_apply] at this
    simp [IsRoot, ← this]
  have h1 : Nat.card F' ≤ q := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ Multiset.card (X ^ q - X : F'[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ q - X : F'[X]).natDegree := card_roots' _
      _ = q := hdeg
  rw [hcard] at h1
  have h2 : q ^ 2 ≤ q ^ Module.finrank F F' := Nat.pow_le_pow_right (by omega) hp.two_le
  nlinarith

theorem UpperTheory.Gal.InertialTypesAlt.killsNil :
    KillsAll → KillsOn fun a => a.D = [] := by
  intro h F F' _ _ _ _ s hp hs ι θ hθ a hD hok hq
  obtain ⟨q, D, L⟩ := a
  simp only at hD hq
  subst hD
  subst hq
  have key := h F F' s hp (frob_ne_one s hp hs) ι θ hθ L (fun p hp' => hok.2.2 p hp') (deg L) rfl
  have hrk : (⟨Nat.card F, [], L⟩ : Lbl).rk = deg L := by
    have h0 : GlobalTheory.Shin.deg ([] : List (ℕ × ℕ)) = 0 := rfl
    simp [Lbl.rk, h0]
  rw [hrk]
  simpa [Lbl.lift, JD_nil] using key
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt.TypesOfLabels

private noncomputable def chRep {H : Type} [Group H] (χ : H →* ℂˣ) : Representation ℂ H ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_comm]

private theorem chRep_apply {H : Type} [Group H] (χ : H →* ℂˣ) (g : H) (z : ℂ) :
    chRep χ g z = ((χ g : ℂˣ) : ℂ) • z := rfl

private theorem trace_chRep {H : Type} [Group H] (χ : H →* ℂˣ) (g : H) :
    LinearMap.trace ℂ ℂ (chRep χ g) = ((χ g : ℂˣ) : ℂ) := by
  show LinearMap.trace ℂ ℂ (((χ g : ℂˣ) : ℂ) • LinearMap.id) = _
  rw [map_smul, LinearMap.trace_id]
  simp

private theorem isCl_trace {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) : IsCl (fun g => LinearMap.trace ℂ W (ρ g)) := by
  intro x y
  simp only [map_mul]
  rw [LinearMap.trace_mul_cycle, ← map_mul, mul_inv_cancel, map_one, one_mul]

private theorem trace_zero {W : Type} [AddCommGroup W] [Module ℂ W] (h : ¬ FiniteDimensional ℂ W) :
    LinearMap.trace ℂ W = 0 := by
  ext f
  have hn : ¬ ∃ s : Finset W, Nonempty (Module.Basis s ℂ W) := by
    rintro ⟨s, ⟨b⟩⟩
    exact h (Module.Finite.of_basis b)
  simp only [LinearMap.trace, dif_neg hn]

private theorem ofFn_comp_get {β : Type} (M : List (ℕ × ℕ)) (f : ℕ × ℕ → β) :
    List.ofFn (fun a : Fin M.length => f (M.get a)) = M.map f := by
  rw [List.ofFn_comp', List.ofFn_get]

private theorem sum_fst (M : List (ℕ × ℕ)) : ∑ a : Fin M.length, (M.get a).1 = deg M := by
  unfold GlobalTheory.Shin.deg
  rw [← List.sum_ofFn]
  congr 1
  have := List.ofFn_comp' M.get Prod.fst
  simpa [List.ofFn_get] using this

end UpperTheory.Gal.InertialTypesAlt.TypesOfLabels

open UpperTheory.Gal.InertialTypesAlt.TypesOfLabels in

theorem UpperTheory.Gal.InertialTypesAlt.typeOfLbl :
    MeetsIff → FrobL → JDEq → TypeOfLbl := by
  intro hMI hFL hJD k _ _ _ _ θ N V _ _ π b hb hL
  obtain ⟨_, _, hN, hmeet⟩ := hb
  have hd : ∑ a : Fin (b.D ++ b.L).length, ((b.D ++ b.L).get a).1 = N := by
    rw [sum_fst, hN]
    simp [Lbl.rk, GlobalTheory.Shin.deg, List.map_append, List.sum_append]
  let ω : Fin (b.D ++ b.L).length → 𝓀[k]ˣ →* ℂˣ := fun a =>
    (powMonoidHom ((b.D ++ b.L).get a).2).comp
      ((Units.map (θ : AlgebraicClosure 𝓀[k] →* ℂ)).comp
        (Units.map (algebraMap 𝓀[k] (AlgebraicClosure 𝓀[k])).toMonoidHom))
  refine ⟨(b.D ++ b.L).length, fun a => ((b.D ++ b.L).get a).1,
    fun a => ((b.D ++ b.L).get a).2, hd, ω, ?_, ?_, ?_⟩
  · rw [show (fun a : Fin (b.D ++ b.L).length => (((b.D ++ b.L).get a).1, ((b.D ++ b.L).get a).2))
        = (b.D ++ b.L).get from funext fun a => rfl, List.ofFn_get]
  · intro a u
    simp [ω]
  have hJ : JD θ b.D b.L N = hcL (List.ofFn fun i : Fin (b.D ++ b.L).length =>
      (⟨((b.D ++ b.L).get i).1, detc θ ((b.D ++ b.L).get i).1 ((b.D ++ b.L).get i).2⟩ :
        (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N := by
    rw [(hJD 𝓀[k] θ).1, ofFn_comp_get (b.D ++ b.L)
      (fun p => (⟨p.1, detc θ p.1 p.2⟩ : (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))), List.map_append]
    congr 2
    apply List.map_congr_left
    rintro ⟨p1, p2⟩ hp
    have h1 : p1 = 1 := hL _ hp
    subst h1
    rw [(hJD 𝓀[k] θ).2.1]
  obtain ⟨c0, hc0, hF⟩ := hFL 𝓀[k] (b.D ++ b.L).length (fun a => ((b.D ++ b.L).get a).1) N hd
  have hsum := hF (fun i => detc θ ((b.D ++ b.L).get i).1 ((b.D ++ b.L).get i).2)
    (fun g => LinearMap.trace ℂ _ (levelZero π g)) (isCl_trace _)
  have hne : ∑ᶠ p : parab 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd),
      star (∏ i, detc θ ((b.D ++ b.L).get i).1 ((b.D ++ b.L).get i).2
        (leviProj 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd) p i)) *
        LinearMap.trace ℂ _ (levelZero π (p : GL (Fin N) 𝓀[k])) ≠ 0 := by
    intro h0
    unfold Meets at hmeet
    rw [hJ, hsum, h0, mul_zero] at hmeet
    exact hmeet rfl
  have hfd : FiniteDimensional ℂ (fixed π (KOne k (Fin N))) := by
    by_contra hfd
    apply hne
    simp [trace_zero hfd]
  let χ := (UpperTheory.Gal.TypesAndIwahori.leviChar (fun a : Fin (b.D ++ b.L).length => Fin ((b.D ++ b.L).get a).1) ω).comp
    (leviProj 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd))
  have hm : Meets ((levelZero π).comp (parab 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd)).subtype)
      (fun g => LinearMap.trace ℂ ℂ (chRep χ g)) := by
    unfold Meets
    convert hne using 3 with p
    simp only [trace_chRep]
    simp [χ, ω, UpperTheory.Gal.TypesAndIwahori.leviChar_apply, detc]
  obtain ⟨f, hf0, hf⟩ := ((hMI _ _ ℂ _ _).2).1 hm
  have hf1 : f 1 ≠ 0 := fun h => hf0 (LinearMap.ext_ring (by simpa using h))
  refine ⟨(f 1 : V), by simpa using hf1, ?_⟩
  intro g
  obtain ⟨hK, hP⟩ := mem_levelPre.1 g.2
  have h2 := congrArg Subtype.val (hf ⟨redK k (Fin N) ⟨(g : GL (Fin N) k), hK⟩, hP⟩ 1)
  rw [chRep_apply, map_smul] at h2
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, levelZero_apply,
    Submodule.coe_smul] at h2
  rw [← h2]
  rfl
end

section

noncomputable section

open GlobalTheory.Shin
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt

private theorem gal_id {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) :
    gal (RingHom.id F) n y = y := by
  ext i j
  simp [gal]

private theorem inPar_one {F : Type} [Field F] (a n : ℕ) : InPar a (1 : GL (Fin n) F) := by
  intro i j hj hi
  have hij : i ≠ j := by
    rintro rfl
    omega
  simp [Matrix.one_apply_ne hij]

theorem frobTwo : FrobTwo := by
  intro F _ _ a b n _
  haveI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin a) F) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin b) F) := Fintype.ofFinite _
  have hN : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) ≠ 0 := by
    haveI : Nonempty {p : GL (Fin n) F // InPar a p} := ⟨⟨1, inPar_one a n⟩⟩
    exact_mod_cast (Nat.card_pos (α := {p : GL (Fin n) F // InPar a p})).ne'
  have hG : (Fintype.card (GL (Fin n) F) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  refine ⟨star ((Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹) * (Fintype.card (GL (Fin n) F) : ℂ),
    mul_ne_zero (star_ne_zero.2 (inv_ne_zero hN)) hG, ?_⟩
  intro α β T hT
  set w : GL (Fin n) F → ℂ := fun p =>
    if InPar a p then star (α (tlG a p) * β (brG a b p)) * T p else 0 with hw
  have hleft : ∑ᶠ g, star (hc a b α β n g) * T g =
      star ((Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹) *
        ((Fintype.card (GL (Fin n) F) : ℂ) * ∑ p, w p) := by
    have hy : ∀ y : GL (Fin n) F,
        ∑ g : GL (Fin n) F, star (if InPar a (y⁻¹ * (g * y)) then
          α (tlG a (y⁻¹ * (g * y))) * β (brG a b (y⁻¹ * (g * y))) else 0) * T g = ∑ p, w p := by
      intro y
      refine Fintype.sum_equiv ((Equiv.mulRight y).trans (Equiv.mulLeft y⁻¹)) _ _ fun g => ?_
      have hTg : T (y⁻¹ * (g * y)) = T g := by
        rw [← mul_assoc]
        exact hT g y
      simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight, hw, hTg]
      split_ifs <;> simp
    rw [finsum_eq_sum_of_fintype]
    simp only [hc, hcTw, gal_id, finsum_eq_sum_of_fintype, star_mul', star_sum, mul_assoc,
      ← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [hy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hright : ∑ᶠ x, star (α x) * ∑ᶠ y, star (β y) * resT a b T x y = ∑ p, w p := by
    have key : ∀ p : GL (Fin n) F, ∑ x : GL (Fin a) F, ∑ y : GL (Fin b) F,
        star (α x) * (star (β y) *
          if InPar a p ∧ tlG a p = x ∧ brG a b p = y then T p else 0) = w p := by
      intro p
      rw [Finset.sum_eq_single (tlG a p), Finset.sum_eq_single (brG a b p)]
      · by_cases h : InPar a p <;> simp [hw, h, star_mul', mul_assoc]
      · intro y _ hy
        simp [Ne.symm hy]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    simp only [resT, finsum_eq_sum_of_fintype, Finset.mul_sum]
    rw [← Finset.sum_congr rfl fun p _ => key p]
    refine (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans ?_
    exact Finset.sum_comm
  rw [hleft, hright, mul_assoc]

end UpperTheory.Gal.InertialTypesAlt
end
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem polTop_sum (q : ℕ) (hq : 2 ≤ q) (L : List (ℕ × ℕ)) (hL : ∀ p ∈ L, p.1 = 1) :
    (L.map fun p => (Multiset.range p.1).map fun j =>
      ((1 : ℕ), ((p.2 * q ^ j * ((q - 1) / (q ^ p.1 - 1)) : ℕ) : ZMod (q - 1)))).sum =
      ((L.map fun p => (p.1, ((p.2 : ℕ) : ZMod (q - 1))) : List _) : Multiset _) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have h1 : p.1 = 1 := hL p (by simp)
    have hpos : 0 < q - 1 := by omega
    rw [List.map_cons, List.sum_cons, ih (fun r hr => hL r (List.mem_cons_of_mem _ hr)), List.map_cons,
      h1]
    simp [Nat.div_self hpos]

theorem UpperTheory.Gal.InertialTypesAlt.polTop :
    PolTop := by
  intro b x hq hL hx
  have hpos : 0 < b.q - 1 := by omega
  have hb : b.blocks b.q = ((b.D ++ b.L).map fun p => (p.1, ((p.2 : ℕ) : ZMod (b.q - 1))) : List _) := by
    unfold Lbl.blocks
    rw [polTop_sum b.q hq b.L hL, List.map_append, ← Multiset.coe_add]
    simp [Nat.div_self hpos]
  refine ⟨hb, ?_⟩
  unfold Lbl.pol
  rw [hb, Multiset.map_coe, Multiset.prod_coe, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  rw [ZMod.val_natCast, ← pow_eq_pow_mod p.2 hx]
end
