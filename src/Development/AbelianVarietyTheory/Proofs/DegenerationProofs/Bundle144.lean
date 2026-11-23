module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle134
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.TorsionZeroCountTwist
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle121
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle135
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle136
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistIsoTorsionRepresentativeMulEquiv
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.psiRel_of_expT' : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (I : Ideal V), AdmBase V I → ∀ (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U₀ : Unif I D A G), Under U U₀.toUnifPre → ∀ (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D.toPre (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 σ f → PsiRel D.toPre (𝟙_ _) f := by
  first | exact @GlobalTheory.PsiExpansion.psiRel_of_expT | exact GlobalTheory.PsiExpansion.psiRel_of_expT | (intros; apply GlobalTheory.PsiExpansion.psiRel_of_expT <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.AllLevels

theorem isThetaPt_comp {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I I' : Type} {x : I → (T ⟶ P.A)}
    {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P k x v) (f : I' → I) : IsThetaPt P k (fun i => x (f i)) fun i => v (f i) := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H.2.2 p
  exact ⟨V, hV, th, s1, α, τ, fun i => U (f i), fun i => s2 (f i), fun i => w (f i), u, a1, a2, a3, a4,
    fun i => a5 _, fun i => a6 _, fun i => a7 _, fun i => a8 _⟩

theorem isThetaPt_mul {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (c : Γ(T.left, ⊤)) (hc : IsUnit c)
    (H : IsThetaPt P k x v) : IsThetaPt P k x (fun i => c * v i) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  obtain ⟨c', hc'⟩ := hc.map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, (c' * (show Γ(V.toScheme, ⊤)ˣ from u) : Γ(V.toScheme, ⊤)ˣ), a1, a2, a3, a4,
    a5, a6, a7, fun i => ?_⟩
  have aux : ∀ (a : Γ(T.left, ⊤)) (u₀ : Γ(V.toScheme, ⊤)ˣ) (w₀ : Γ(V.toScheme, ⊤)),
      V.ι.appTop.hom a = u₀.val * w₀ → V.ι.appTop.hom (c * a) = (c' * u₀).val * w₀ := by
    intro a u₀ w₀ h
    rw [map_mul, h, Units.val_mul, hc', _root_.mul_assoc]
  exact aux (v i) u (w i) (a8 i)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem ev_nsmul {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso D k Q act e) (M r : ℕ) (a : D.La) : I.ev M (r • a) = I.ev M a ^ r := by
  induction r with
  | zero =>
    have := I.add M 0 0
    rw [add_zero] at this
    rw [zero_smul, pow_zero]
    exact left_eq_mul.1 this
  | succ r ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem theta_down (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] (o : Full D K) {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
    {v v' : D.La → K} (c : Kˣ) (hc : ∀ x, v (r • x) = c * v' x) (h : o.Theta (r * m) v) : o.Theta m v' := by
  have e : ∀ a, o.I.ev ((r * m) ^ 2) (r • a) ^ r = o.I.ev (m ^ 2) a := fun a => by
    rw [ev_nsmul, ← pow_mul, ← o.I.tower (m ^ 2) (r * r) (by positivity) (by positivity)]
    congr 2; ring
  have h₁ := GlobalTheory.T.isThetaPt_pow_of_isThetaPt_mul hL K o.P r m D.La _ _ (fun a => by
    rw [e]; exact (o.I.onto _ (by positivity) _).2 ⟨a, rfl⟩) (isThetaPt_comp h fun a => r • a)
  have h₂ := isThetaPt_mul (fnOf ((c⁻¹ : Kˣ) : K)) ((c⁻¹).isUnit.map _) h₁
  simp only [e] at h₂
  unfold Full.Theta
  convert h₂ using 2 with a
  rw [hc]
  exact (congrArg fnOf (Units.inv_mul_cancel_left c (v' a)).symm).trans (map_mul _ _ _)

theorem exists_iso (hL : Laws) (h₁ : ThetaPtDeterminesSt) (h₂ : EndDeterminedOnTorsionSt) (D : Datum H) {n : ℕ}
    (hn : n.Prime) (ho : Odd n) : ∃ J₀, ∀ J, J₀ ≤ J → ∀ (K : Type) [Field K] [IsAlgClosed K] (o o' : Full D K) (v : D.La → K),
      o.I.ζ ((n ^ J) ^ 2) = o'.I.ζ ((n ^ J) ^ 2) → o.Theta (n ^ J) v → o'.Theta (n ^ J) v →
      ∃ φ : o.P.A ≅ o'.P.A, IsPolIso o.P o'.P φ ∧
        (letI := H.starRing; ∀ x, o.oa.act x ≫ φ.hom = φ.hom ≫ o'.oa.act x) := by
  letI := H.starRing
  obtain ⟨bas, hbas⟩ := GlobalTheory.ZM.exists_isSympBasis E H D
  generalize Module.finrank ℚ E / 2 * (D.p + D.q) = g at bas hbas
  choose cn hcn using exists_starNormLE_of_isCMField E (fun a => H.bar_eq a)
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  let B := ((n ^ 2) ^ 2) ^ g * g.factorial + 4 ^ g * g.factorial * (2 * s.sup cn)
  refine ⟨B + 4, fun J hJ K _ _ o o' v hζ hv hv' => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 4 := ⟨J - 4, by omega⟩
  have hB : B < n ^ (j + 4) := lt_of_le_of_lt (by omega) (Nat.lt_pow_self hn.one_lt)
  have hp : 0 < n ^ (j + 4) := pow_pos hn.pos _
  set M := (n ^ (j + 4)) ^ 2 with hM
  have hM0 : 0 < M := pow_pos hp _
  haveI : NeZero M := ⟨hM0.ne'⟩
  haveI := o.charZero
  obtain ⟨hg, lev, hb, hl⟩ := GlobalTheory.T.exists_level_of_full' hL E H D g bas hbas K o M hM0
  have Q := GlobalTheory.T.exists_level_of_full' hL E H D g bas hbas K o' M hM0
  rw [← hζ] at Q
  obtain ⟨hg', lev', hb', hl'⟩ := Q
  let lab : (Fin (2 * g) → ZMod M) → D.La := fun a => bas fun i => ((a i).val : ℤ)
  have hlab : ∀ a : Fin (2 * g) → ZMod M, (fun i => (((a i).val : ℤ) : ZMod M)) = a := fun a => funext fun i => by simp
  have e : levelPoint lev hg = fun a => o.I.ev M (lab a) := funext fun a => by rw [← hl, hlab]
  have e' : levelPoint lev' hg' = fun a => o'.I.ev M (lab a) := funext fun a => by rw [← hl', hlab]
  have key : ∀ c, c ≤ s.sup cn → 4 ^ g * g.factorial * (2 * c) < M ^ 2 := fun c hc =>
    calc 4 ^ g * g.factorial * (2 * c) ≤ B := le_add_left (by gcongr)
      _ < n ^ (j + 4) := hB
      _ ≤ M := Nat.le_self_pow two_ne_zero _
      _ ≤ M ^ 2 := Nat.le_self_pow two_ne_zero _
  obtain ⟨φ, hφ, hφb⟩ := h₁ g n 2 j _ (n ^ (j + 4)) hn ho le_rfl rfl (by ring) (lt_of_le_of_lt (Nat.le_add_right _ _) hB) K
    (Nat.cast_ne_zero.2 hn.pos.ne') o.P o'.P hg hg' _ lev lev' (fun a => fnOf (v (lab a)))
    (e ▸ isThetaPt_comp hv lab) (e' ▸ isThetaPt_comp hv' lab)
  haveI := hφ.1
  have hev : ∀ a, o.I.ev M a ≫ φ.hom = o'.I.ev M a := fun a => by
    obtain ⟨c, rfl⟩ := bas.surjective a
    rw [← hl, ← hl', ThetaPtDet.levelPoint_eq, ThetaPtDet.levelPoint_eq, ThetaPtDet.linComb_comp]
    exact congrArg (linComb · _) (funext hφb)
  refine ⟨φ, hφ, fun x => ?_⟩
  have hx : x ∈ Submodule.span ℤ (s : Set (𝓞 E)) := hs ▸ Submodule.mem_top
  have add : ∀ a b, o.oa.act (a + b) = o.oa.act a * o.oa.act b := o.oa.map_add
  have add' : ∀ a b, o'.oa.act (a + b) = o'.oa.act a * o'.oa.act b := o'.oa.map_add
  let f : 𝓞 E →+ Additive (o.P.A ⟶ o'.P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (o.oa.act a ≫ φ.hom))
    fun a b => by rw [add, MonObj.mul_comp]; rfl
  let f' : 𝓞 E →+ Additive (o.P.A ⟶ o'.P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (φ.hom ≫ o'.oa.act a))
    fun a b => by rw [add', MonObj.comp_mul]; rfl
  have : f = f' := AddMonoidHom.eq_of_eqOn_dense (s := (s : Set (𝓞 E)))
    (by rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; rfl) fun a ha => by
    refine congrArg Additive.ofMul (h₂ g (cn a) M (key _ (Finset.le_sup ha)) K (Nat.cast_ne_zero.2 hM0.ne') o.P o'.P hg hg'
      φ hφ _ o.oa o'.oa a (hcn a) fun y hy => ?_)
    obtain ⟨b, rfl⟩ := (o.I.onto M hM0 y).1 hy
    have l := o.I.lin M a b
    have l' := o'.I.lin M a b
    rw [← Category.assoc, ← Category.assoc, ← l, hev, hev, l']
  exact Additive.ofMul.injective (DFunLike.congr_fun this x)

theorem exists_full_all (hL : Laws) (h₁ : ThetaPtDeterminesSt) (h₂ : EndDeterminedOnTorsionSt) {K : Type} [Field K]
    [IsAlgClosed K] (ρ : K) (ζ : ℕ → Kˣ) (hζ : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) (v : ℕ → D.La → K)
    (hv : ∀ r m, Odd r → Odd m → ∃ c : Kˣ, ∀ x, v (r * m) (r • x) = c * v m x) {n : ℕ} (hn : n.Prime) (ho : Odd n)
    (h : ∀ j, 2 ≤ j → ∃ o : Full D K, o.ρ = ρ ∧ o.I.ζ ((n ^ j) ^ 2) = ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (v (n ^ j))) :
    ∃ o : Full D K, o.ρ = ρ ∧ ∀ j, o.I.ζ (n ^ j) = ζ (n ^ j) ∧ o.Theta (n ^ j) (v (n ^ j)) := by
  obtain ⟨J, hJ⟩ := exists_iso hL h₁ h₂ D hn ho
  choose o hρ hz ht using fun j => h (J + 2 + j) (by omega)
  have hp : ∀ i, 0 < n ^ i := fun i => pow_pos hn.pos i
  have th : ∀ j i, i ≤ J + 2 + j → (o j).Theta (n ^ i) (v (n ^ i)) := fun j i hi => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hi
    obtain ⟨c, hc⟩ := hv (n ^ d) (n ^ i) ho.pow ho.pow
    refine theta_down hL (o j) (hp d) (hp i) c hc ?_
    rw [← pow_add, ← hd]; exact ht j
  have ze : ∀ j i, i ≤ 2 * (J + 2 + j) → (o j).I.ζ (n ^ i) = ζ (n ^ i) := fun j i hi => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
    have := hz j
    rw [← pow_mul, mul_comm, hd, pow_add] at this
    rw [← (o j).I.ζ_pow _ _ (hp i) (hp d), this, hζ _ _ (hp i) (hp d)]
  have ze' : ∀ j i, i ≤ J + 2 + j → (o j).I.ζ ((n ^ i) ^ 2) = ζ ((n ^ i) ^ 2) := fun j i hi => by
    rw [← pow_mul]; exact ze j _ (by omega)
  choose φ hφ hact using fun j => hJ (J + 2) (by omega) K (o j) (o 0) _
    ((ze' j _ (by omega)).trans (ze' 0 _ le_rfl).symm) (th j _ (by omega)) (th 0 _ le_rfl)
  choose I hIζ _ hI using fun j => GlobalTheory.T.exists_tateIso_of_isPolIso hL E H D K (o j) (o 0) (φ j) (hφ j) (hact j)
  obtain ⟨I', hI'⟩ := GlobalTheory.T.exists_limitPoint_tateIso_sequence E H D K _ _ _ I
  refine ⟨{ o 0 with I := I' }, hρ 0, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨j, hj, -, e⟩ := hI' _ (hp i) i
    exact e.trans ((congrFun (hIζ j) _).trans (ze j i (by omega)))
  · obtain ⟨j, hj, e, -⟩ := hI' _ (pow_pos (hp i) 2) i
    have := hI j _ _ (th j i (by omega))
    unfold Full.Theta at this ⊢
    dsimp only at this ⊢
    rw [e]; exact this

end GlobalTheory.Ex.AllLevels
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.TowerAlg

theorem closedPoint_mem_range {R : Type} [CommRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤) (e : ℕ) :
    IsLocalRing.closedPoint R ∈ Set.range (thick R I e) := by
  have h := range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := I ^ (e + 1)))
  refine h.ge ?_
  rw [Ideal.mk_ker]
  exact (Ideal.pow_le_self (Nat.succ_ne_zero e)).trans (IsLocalRing.le_maximalIdeal hI)

theorem triv_of_forall_thick (hG : GlobalFnsSt) (hS : SecAlgSt) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    {I : Ideal V} (hI : I ≠ ⊤) (hV : IsAdicComplete I V) (B : Over (Spec (CommRingCat.of V))) [GrpObj B]
    (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) (N : LB B.left) (hN : N.IsLB)
    (ht : ∀ e, Triv (N.pull (fstG I e B).left)) : Triv N := by
  let o : Spec (CommRingCat.of V) ⟶ B.left := (η[B]).left
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  obtain ⟨c, hc⟩ := DVR.exists_gen_of_local N hN (K := PUnit) (fun _ => o) (fun _ => 1)
  have pb : ∀ e, IsPullback (fstG I e B).left (thickObj V I e B).hom B.hom (thick V I e) :=
    fun e => IsPullback.of_hasPullback B.hom (thick V I e)
  choose t tg tv using fun e => AbTriv.exists_normalised hN ho c hc (pb e) (ht e)
  have tm : ∀ e, thickMap V I e B ≫ (fstG I (e + 1) B).left = (fstG I e B).left := fun e =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have compat : ∀ e z J, Good N z J → val (t (e + 1)) (thickMap V I e B) z J = val (t e) (𝟙 _) z J := by
    intro e z J hJ
    let a := (pb e).lift (thick V I e ≫ o) (𝟙 _) (by rw [Category.assoc, ho, Category.comp_id, Category.id_comp])
    have a₁ : a ≫ (fstG I e B).left = thick V I e ≫ o := (pb e).lift_fst _ _ _
    have key := gen_unique' hN (fun U _ k => by simp only [tm e]) (thickObj V I e B).hom a ((pb e).lift_snd _ _ _)
      (hG _ _ (TLinPf.isAb_pullback (thick V I e) B hB)).2 (tg e)
      (DVR.pullGen_isGen _ _ _ _ (tg (e + 1)) (thickMap V I e B))
      (fun y J hJ => (tv e _ a _ y J hJ a₁).trans ((val_pull hJ _ _ _).trans
        (tv (e + 1) _ _ _ y J hJ (by rw [Category.assoc, tm e, a₁]))).symm) _ (𝟙 _) z J hJ
    rw [val_pull hJ, Category.id_comp] at key
    exact key.symm
  obtain ⟨s, hs, -⟩ := hS V I hV B hB.smooth hp N hN (fun e => genSec (t e) (tg e))
    (fun e z J hJ => (sval_genSec _ _ _ z hJ).trans
      ((congrArg Units.val (compat e z J hJ)).trans (sval_genSec _ _ _ z hJ).symm))
  have := hB.proper
  have top : nonzeroLocus s = ⊤ := AbTriv.eq_top_of_closed_fibre B.hom _ fun x hx => by
    have hm : x ∈ Set.range (pullback.fst B.hom (thick V I 0)) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hx]
      exact closedPoint_mem_range hI 0
    obtain ⟨z, rfl⟩ := hm
    choose J hJ using fun ψ : ((Over.map (thick V I 0)).obj (thickObj V I 0 B)).left ⟶ B.left =>
      exists_chart hN (ψ z)
    refine (TwistZero.mem_nonzeroLocus_iff s (fstG I 0 B).left z hJ).2 ?_
    rw [hs 0 z J hJ, sval_genSec _ _ _ z hJ]
    exact Units.isUnit _
  refine AbTriv.triv_of_pull_id (TwistZero.triv_of_sec hN s fun y J hJ => ?_)
  exact (TwistZero.mem_nonzeroLocus_iff s (𝟙 _) y hJ).1 (by rw [top]; trivial)

theorem triv_pull_of_gen {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F)) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (r : Z ⟶ Y') (π : Z ⟶ Y)
    (hc : ∀ k, (r ≫ φ' k) ≫ F = π ≫ φ k) : Triv ((LB.LinComb L φ ε).pull π) := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨t, ht, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' _ (DVR.pullGen_isGen _ _ _ _ ha r)
  refine (KerPow.pull_iff φ ε π).2 ?_
  rw [← (funext hc : (fun k => (r ≫ φ' k) ≫ F) = fun k => π ≫ φ k)]
  exact ⟨t, ht⟩

section Level
variable {S S' Z : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
  {f : S' ⟶ S} {F : B'.left ⟶ B.left}


omit [IsCommMonObj B] [IsCommMonObj B'] in
theorem toBase_mul (h : IsGrpPullback B' B f F) (T : Over S') (x y : T ⟶ B') :
    toBase h.1.w (x * y) = toBase h.1.w x * toBase h.1.w y :=
  Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem triv_theta (h : IsGrpPullback B' B f F) (M' : CP B') {L : LB B.left} (hL : L.IsLB)
    (hw : LBIso M'.L.L (L.pull F)) (π : Z ⟶ (G3 B).left) (z : Z ⟶ S') (hz : π ≫ (G3 B).hom = z ≫ f) :
    Triv ((Theta B L).pull π) := by
  let ρ : Over.mk ((Over.mk z).hom ≫ f) ⟶ G3 B := Over.homMk π hz
  let x : Fin 3 → (Over.mk z ⟶ B') := fun i =>
    Over.homMk (h.1.lift (ρ ≫ x3 B i).left z (Over.w (ρ ≫ x3 B i))) (h.1.lift_snd _ _ _)
  let β := toBaseHom (toBase_mul h) (Over.mk z)
  have hx : ∀ i, β (x i) = ρ ≫ x3 B i := fun i => Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  let r : Over.mk z ⟶ G3 B' := lift (x 0) (lift (x 1) (x 2))
  have hr : ∀ i, r ≫ x3 B' i = x i := fun i => by fin_cases i <;> simp [r, x3]
  refine triv_pull_of_gen hL M'.L.isLB hw (φ := thφ B (x3 B)) (φ' := thφ B' (x3 B')) (ε := thε) M'.c.t M'.c.isGen
    r.left π fun I => ?_
  have e : β (r ≫ psum B' (x3 B') I.down) = ρ ≫ psum B (x3 B) I.down :=
    (psum_hom (β.comp (preHom r)) (x3 B') I.down).trans ((congrArg (fun q => psum B q I.down) (funext fun i =>
      (congrArg β (hr i)).trans (hx i))).trans (psum_hom (preHom ρ) (x3 B) I.down).symm)
  exact congrArg (fun q => q.left) e

theorem triv_sym (h : IsGrpPullback B' B f F) (M' : CP B') {L : LB B.left} (hL : L.IsLB)
    (hw : LBIso M'.L.L (L.pull F)) (π : Z ⟶ B.left) (z : Z ⟶ S') (hz : π ≫ B.hom = z ≫ f) :
    Triv ((LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]).pull π) := by
  let x : Over.mk z ⟶ B' := Over.homMk (h.1.lift π z hz) (h.1.lift_snd _ _ _)
  have hx : x.left ≫ F = π := h.1.lift_fst _ _ _
  refine triv_pull_of_gen hL M'.L.isLB hw M'.sym M'.sym_gen x.left π fun k => ?_
  fin_cases k
  · exact (inv_left_comp (toBase_mul h) x).trans (congrArg (· ≫ _) hx)
  · exact ((congrArg (· ≫ F) (Category.comp_id _)).trans hx).trans (Category.comp_id _).symm

end Level

section Pack
variable (hG : GlobalFnsSt) (hS : SecAlgSt) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  (hI : I ≠ ⊤) (hc : IsAdicComplete I R) {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
  [∀ e, GrpObj (Y e)] [∀ e, IsCommMonObj (Y e)] (N : ∀ e, CP (Y e)) {B : Over (Spec (CommRingCat.of R))} [GrpObj B]
  [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {b : ∀ e, (Y e).left ⟶ B.left}
  (hg : ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e)) {M : LB B.left} (hM : M.IsLB)
  (hiso : ∀ e, LBIso (N e).L.L (M.pull (b e)))
include hG hS hI hc hB hp hg hM hiso

theorem triv_theta_alg : Triv (Theta B M) :=
  triv_of_forall_thick hG hS hI hc (G3 B)
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB))
    (isProjBy_tensor R _ _ hp (isProjBy_tensor R _ _ hp hp)) (Theta B M) (LB.isLB_linComb hM _ _) fun e =>
      triv_theta (hg e) (N e) hM (hiso e) (fstG I e (G3 B)).left (pullback.snd (G3 B).hom (thick R I e))
        (pullback.condition (f := (G3 B).hom) (g := thick R I e))

theorem triv_sym_alg : Triv (LB.LinComb M (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]) :=
  triv_of_forall_thick hG hS hI hc B hB hp _ (LB.isLB_linComb hM _ _) fun e =>
    triv_sym (hg e) (N e) hM (hiso e) (fstG I e B).left (pullback.snd B.hom (thick R I e))
      (pullback.condition (f := B.hom) (g := thick R I e))

theorem exists_cp_alg (hY : ∀ e, IsAbelianScheme (Y e)) :
    ∃ Q : CP B, Q.L.L = M ∧ ∀ e, IsCPPullback (N e) Q (thick R I e) (b e) := by
  obtain ⟨r, hr⟩ := DVR.exists_gen_of_local M hM (K := PUnit) (fun _ => eSec B) (fun _ => 1)
  obtain ⟨Q, hQ⟩ := AbPackage.exists_cp hG hB ⟨M, r, hM, hr⟩ (triv_theta_alg hG hS hI hc N hB hp hg hM hiso)
    (triv_sym_alg hG hS hI hc N hB hp hg hM hiso)
  have e₀ : Q.L.L = M := congrArg (fun q => q.L) hQ
  refine ⟨Q, e₀, fun e => ⟨hg e, ?_⟩⟩
  obtain ⟨w, hw⟩ : LBIso (N e).L.L (Q.L.L.pull (b e)) := by rw [e₀]; exact hiso e
  exact AbPackage.exists_isCPMap_of_iso hG (hY e) Q (N e) (toBase_mul (hg e)) w hw

end Pack

end GlobalTheory.TowerAlg
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

theorem _root_.GlobalTheory.T.torsionIsometry_values_isTorsionLabelSystem : BrGtSt → BrWpSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F) (N : NumD F) (ν : NumOf D₀ F N) (q : ∀ n : ℕ, D.La → N.QT n), (∀ n a, ν.QPt (I.ev n a) (q n a)) → Labels N D.EF I.ζ q ∧ ∀ k, 0 < k → ∀ (x : 𝓞 E) (a : D.La), ∃ z, ν.eX (q k (x • a)).1.1.toAdd = x • ν.eX (q k a).1.1.toAdd + k • z := by
  first | exact @GlobalTheory.ModelData.labels_of_tateIsoQ | exact GlobalTheory.ModelData.labels_of_tateIsoQ | (intros; apply GlobalTheory.ModelData.labels_of_tateIsoQ <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

theorem _root_.GlobalTheory.T.valuesIso_respects_endomorphism_of_torsion_compat : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (I : NumB.Iso N.toNumB N'.toNumB), GeoIso ν ν' I → ∀ (O : Type) [CommRing O] [StarRing O] (oa : D.P.OAct O) (oa' : D'.P.OAct O) (n : ℕ), n.Prime → (n : F) ≠ 0 → ∀ x : O, (∀ (j : ℕ) (b : N.A), b ^ n ^ j = 1 → I.φ (actV ν oa x b) = actV ν' oa' x (I.φ b)) → ∀ b, I.φ (actV ν oa x b) = actV ν' oa' x (I.φ b) := by
  first | exact @GlobalTheory.Relabel.actV_compat_of_torsion | exact GlobalTheory.Relabel.actV_compat_of_torsion | (intros; apply GlobalTheory.Relabel.actV_compat_of_torsion <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

theorem _root_.GlobalTheory.T.twist_iso_torsionRepresentative_mulEquiv : ∀ (O : Type) [CommRing O] (N N' : NumD O) (k : ℕ) (β : N.Form k) (u : Oˣ) (J : NumD.Iso (N.twist β u) N'), (∀ (r : Oˣ) (j : ℕ), r ^ j = u → ∃ τ : N.QT j ≃* N'.QT j, (∀ q q', τ q = q' ↔ TwJ β u r J q q') ∧ (∀ q₁ q₂, N.QEq q₁ q₂ ↔ N'.QEq (τ q₁) (τ q₂)) ∧ ∀ q₁ q₂, N'.wp (τ q₁) (τ q₂) = N.wp q₁ q₂) ∧ ∀ (r₁ r₂ : Oˣ) (n n' m : ℕ) (q₁ : N.QT n) (q₂ : N.QT n') (q₁' : N'.QT n) (q₂' : N'.QT n'), r₂ ^ m = r₁ → q₁.1.1 = q₂.1.1 → q₁.1.2 = q₂.1.2 ^ m → TwJ β u r₁ J q₁ q₁' → TwJ β u r₂ J q₂ q₂' → q₁'.1.1 = q₂'.1.1 ∧ q₁'.1.2 = q₂'.1.2 ^ m := by
  first | exact @GlobalTheory.Relabel.twJ_mulEquiv | exact GlobalTheory.Relabel.twJ_mulEquiv | (intros; apply GlobalTheory.Relabel.twJ_mulEquiv <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section
namespace GlobalTheory.Relabel
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Ex.GtValues

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem gtAct_pt (hG : GlobalFnsSt) {y : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L y J) (oa : D.OAct O) (a : O)
    {u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)}
    (hu : TorusExt.IsRos D.P.L _ _ u) (g g' : GtPtF D F) :
    GtAct oa a g g' ↔ g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ,
      val (g'.s χ) (𝟙 _) y J = val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := by
  have vv : ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) χ,
      val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 (TF (R := R) F).left) y J =
        val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := fun u χ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  refine ⟨fun h => ⟨h.1, fun χ => (val_corr hJ (h.2 _ hu.1 hu.2 χ) _).symm.trans (vv _ χ)⟩,
    fun ⟨hb, hv⟩ => ⟨hb, fun u' hu' u₀ χ => corr_pt D.P.isLB (fun U _ h => ?_)
      (mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ hu' _)) (g'.isGen χ) hJ
      ((vv u' χ).trans ((congrArg₂ (· * ·) rfl
        (TorusExt.IsRos.unique hG D.P.isAb D.P.isLB ⟨hu', u₀⟩ hu hJ _ _)).trans (hv χ).symm))⟩⟩
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_gt g.b (star a • χ) h)
    (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
  rw [prod_gt, TorusExt.cPoint_smul oa, hb]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end

theorem gtAct_values : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N) (O : Type) [CommRing O] [StarRing O], (∀ (oa : D.P.OAct O) (x : O), ∃ ρ, RosV ν oa x ρ) ∧ ∀ [Module O D.X] (oa : D.OAct O) (x : O) (ρ : N.A → N.A → F), RosV ν oa.onB x ρ → ∀ g g' v v', ν.Pt g v → ν.Pt g' v' → (GtAct oa x g g' ↔ v'.b = actV ν oa.onB x v.b ∧ ∀ χ, (v'.s χ : F) = v.s (ν.eX.symm (star x • ν.eX χ)) * ρ (N.c χ) v.b) := by
  intro hG R _ _ D F _ _ N ν O _ _
  refine ⟨fun oa x => ?_, fun oa x ρ ⟨u, hu, u₀, hρ⟩ g g' v v' h h' => ?_⟩
  · have := oa.hom x
    have := oa.hom (star x)
    have hr := oa.rosati (star x)
    rw [star_star] at hr
    obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ hr
    exact ⟨_, u, hu, u₀, fun _ _ => rfl⟩
  · let y : Sp F := (⊥ : PrimeSpectrum F)
    have hJ := good ν y
    obtain ⟨a, b⟩ := (pt_iff ν y _ _).1 h
    obtain ⟨a', b'⟩ := (pt_iff ν y _ _).1 h'
    rw [gtAct_pt hG hJ oa x ⟨hu, u₀⟩, ν.eX.surjective.forall]
    refine and_congr ?_ (forall_congr' fun χ => ?_)
    · rw [← a, ← a', actV, ν.eA.eq_symm_apply]
    · have e := b (ν.eX.symm (star x • ν.eX χ))
      rw [ν.eX.apply_symm_apply] at e
      have r : toStk y (ρ (N.c χ) v.b) = (val₂ u y ν.J (cP D _ (ν.eX χ)) g.b).val := by
        rw [hρ, toStk_vF _ _ hJ, c_eq, a]; rfl
      rw [← (toStk y).injective.eq_iff, map_mul, r, ← e, ← b', ← Units.val_inj, Units.val_mul]
      rfl

end GlobalTheory.Relabel
end
end
