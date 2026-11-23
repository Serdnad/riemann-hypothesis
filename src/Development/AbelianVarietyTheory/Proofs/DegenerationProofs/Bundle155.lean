module

import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle122
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle141
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsSymplecticFamilySpan
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle142
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle143
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

namespace GlobalTheory.Ex.FibIso

theorem isThetaPt_mul {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (c : Γ(T.left, ⊤)) (hc : IsUnit c)
    (H : IsThetaPt P k x v) : IsThetaPt P k x (fun i => c * v i) := by
  apply _root_.GlobalTheory.Ex.AllLevels.isThetaPt_mul <;> assumption

def Reads {F : Type} [Field F] (B : NumB F) (Q : PolAV (Sp F)) (E : B.A ≃* (baseOver (Sp F) ⟶ Q.A)) : Prop :=
  (∀ k : ℕ, 1 ≤ k → ∀ b b' : B.A, b ^ k = 1 → b' ^ k = 1 →
    WeilIs Q.A Q.L k (E b) (E b') (unitOn (B.weil k b b'))) ∧
  ∀ m : ℕ, Odd m → (m : F) ≠ 0 → ∀ (Ix : Type) (b : Ix → B.A), (∀ i, b i ^ m ^ 2 = 1) →
    IsThetaPt Q m (fun i => E (b i)) (fun i => fnOf (B.uth m (b i) 1))

theorem exists_reads (hU : BrUthSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (h₁ : D.PsiEven)
    (h₂ : D.TauBimult) {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] {N : NumD F}
    (ν : NumOf D F N) {Q : PolAV (Sp F)} {Φ : Q.A.left ⟶ D.P.A.left} (hΦ : IsFib D F Q Φ) :
    ∃ E : N.A ≃* (baseOver (Sp F) ⟶ Q.A), (∀ b, (ν.eA b).left = (E b).left ≫ Φ) ∧ Reads N.toNumB Q E := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hΦ.1 (𝟙 (Sp F)) (TF (R := R) F).hom (Category.id_comp _).symm
  obtain ⟨w, t⟩ := hU R D h₁ h₂ F N ν
  have hE : ∀ b, (ν.eA b).left = ((ν.eA.trans e.symm) b).left ≫ Φ := fun b =>
    (congrArg (fun z => z.left) (e.apply_symm_apply (ν.eA b)).symm).trans (he _)
  refine ⟨ν.eA.trans e.symm, hE, fun k hk b b' hb hb' => ?_, fun m hm hm' Ix b hb => ?_⟩
  · have key : ∀ (s : Sp F ⟶ Sp R) (_ : s = 𝟙 _ ≫ (TF (R := R) F).hom) (x y : baseOver (Sp F) ⟶ Q.A)
        (x₀ y₀ : Over.mk s ⟶ D.P.A) (c : Γ(Sp F, ⊤)ˣ), x₀.left = x.left ≫ Φ → y₀.left = y.left ≫ Φ →
        WeilIs D.P.A D.P.L k x₀ y₀ c → WeilIs Q.A Q.L k x y c := by
      rintro s rfl x y x₀ y₀ c hx hy h
      have := Q.isAb.comm
      exact (weilIs_grpPullback_of_comm' _ _ _ _ _ Φ _ _ D.P.isLB Q.isLB hΦ.1 hΦ.2.1 (baseOver _) k x y x₀ y₀ c
        hx hy).2 h
    exact key _ (Category.id_comp _).symm _ _ _ _ _ (hE b) (hE b') (w k hk b b' hb hb')
  · have key : ∀ (s : Sp F ⟶ Sp R) (_ : s = 𝟙 _ ≫ (TF (R := R) F).hom) (x : Ix → (baseOver (Sp F) ⟶ Q.A))
        (x₀ : Ix → (Over.mk s ⟶ D.P.A)) (v : Ix → Γ(Sp F, ⊤)), (∀ i, (x₀ i).left = (x i).left ≫ Φ) →
        (∀ i, x i ^ m ^ 2 = 1) → IsThetaPt D.P m x₀ v → IsThetaPt Q m x v := by
      rintro s rfl x x₀ v hx hp h
      exact (ThetaPtUp.isThetaPt_iff (T := baseOver (Sp F)) hΦ.1 hΦ.2.1 hx hp _).2 h
    exact key _ (Category.id_comp _).symm _ _ _ (fun i => hE (b i))
      (fun i => by rw [← map_pow, hb, map_one]) (t m hm hm' Ix b hb).1

theorem linComb_map {S : Scheme.{0}} {A T : Over S} [GrpObj A] {G : Type} [Group G] (f : G →* (T ⟶ A)) {r : ℕ}
    (y : Fin r → G) (a : Fin r → ℕ) :
    linComb (fun i => f (y i)) a = f (List.ofFn fun i => y i ^ a i).prod := by
  rw [map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => (map_pow f (y i) (a i)).symm))

theorem exists_level (hL : Laws) {F : Type} [Field F] (Q : PolAV (Sp F)) {g : ℕ} (hg : Q.g = g) {M : ℕ}
    (hM : (M : F) ≠ 0) {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ M) (x : Fin (2 * g) → (baseOver (Sp F) ⟶ Q.A))
    (hx : ∀ i, x i ^ M = 1) (hp : ∀ i j, WeilIs Q.A Q.L M (x i) (x j) (unitOn ζ ^ stdSymp g i j)) :
    ∃ lev : Out.Level Q M (unitOn ζ), levelBasis lev hg = x := by
  subst hg
  have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.injective
  refine exists_level_of_pairing hL.globalFns hL.weil hL.mulN _ Q M _
    (hζ.map_of_injective (Units.map_injective inj)) (fun K _ s => ⟨?_, ?_⟩) x hx hp
  · rw [← map_natCast (Spec.preimage s).hom]
    exact (map_ne_zero _).2 hM
  · have : Nontrivial Γ(Spec (CommRingCat.of K), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.injective.nontrivial
    exact hζ.map_of_injective (Units.map_injective
      (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).injective)

theorem exists_iso_of_reads (hL : Laws) (hT : ThetaPtDeterminesSt) {F : Type} [Field F] [IsAlgClosed F]
    {B B' : NumB F} {Q Q' : PolAV (Sp F)} (hg : Q'.g = Q.g) {E : B.A ≃* (baseOver (Sp F) ⟶ Q.A)}
    {E' : B'.A ≃* (baseOver (Sp F) ⟶ Q'.A)} (hE : Reads B Q E) (hE' : Reads B' Q' E') {n : ℕ} (hn : n.Prime)
    (ho : Odd n) (hF : (n : F) ≠ 0) : ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (c : F) (ρ : B.A → B'.A), c ≠ 0 →
      TorsMap B B' (n ^ j) c ρ → ∃ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ ∧
        ∀ b, b ^ (n ^ j) ^ 2 = 1 → E b ≫ σ.hom = E' (ρ b) := by
  refine ⟨((n ^ 2) ^ 2) ^ Q.g * Q.g.factorial + 4, fun J hJ c ρ hc hρ => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 4 := ⟨J - 4, by omega⟩
  have hB : ((n ^ 2) ^ 2) ^ Q.g * Q.g.factorial < n ^ (j + 4) :=
    lt_of_le_of_lt (by omega) (Nat.lt_pow_self hn.one_lt)
  have hm : ((n ^ (j + 4) : ℕ) : F) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hF
  have hM : (((n ^ (j + 4)) ^ 2 : ℕ) : F) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hm
  have hM1 : 1 ≤ (n ^ (j + 4)) ^ 2 := pow_pos (pow_pos hn.pos _) _
  have hlev := nonempty_level_prime_pow hL F Q n ((j + 4) * 2) hn hF
  rw [pow_mul] at hlev
  have hT' := hT Q.g n 2 j _ (n ^ (j + 4)) hn ho le_rfl rfl (by ring) hB F hF Q Q' rfl hg
  have hom : Odd (n ^ (j + 4)) := ho.pow
  generalize n ^ (j + 4) = m at *
  have : NeZero ((m ^ 2 : ℕ) : F) := ⟨hM⟩
  have : NeZero (m ^ 2) := ⟨by omega⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (m ^ 2)
  have hζ := hz.isUnit_unit (NeZero.ne _)
  generalize (hz.isUnit (NeZero.ne _)).unit = ζ at hζ
  have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.injective
  obtain ⟨lev⟩ := hlev (unitOn ζ) (hζ.map_of_injective (Units.map_injective inj))
  let T : Subgroup B.A := (powMonoidHom (m ^ 2)).ker
  let f : T →* (baseOver (Sp F) ⟶ Q.A) := E.toMonoidHom.comp T.subtype
  let f' : T →* (baseOver (Sp F) ⟶ Q'.A) :=
    E'.toMonoidHom.comp (MonoidHom.mk' (fun t => ρ t.1) fun s t => (hρ.1 s.1 t.1 s.2 t.2).1)
  let b : Fin (2 * Q.g) → T := fun i => ⟨E.symm (lev.pt i), by
    show E.symm (lev.pt i) ^ m ^ 2 = 1
    rw [← map_pow, lev.torsion, map_one]⟩
  have hb : lev.pt = fun i => f (b i) := funext fun i => (E.apply_symm_apply _).symm
  obtain ⟨lev', hb'⟩ := exists_level hL Q' hg hM hζ (fun i => f' (b i))
    (fun i => by
      show E' (ρ (b i).1) ^ m ^ 2 = 1
      rw [← map_pow, (hρ.2 _ (b i).2).1, map_one])
    (fun i k => by
      have p₁ := hE.1 _ hM1 _ _ (b i).2 (b k).2
      have p₂ := hE'.1 _ hM1 _ _ (hρ.2 _ (b i).2).1 (hρ.2 _ (b k).2).1
      rw [(hρ.1 _ _ (b i).2 (b k).2).2] at p₂
      simp only [b, MulEquiv.apply_symm_apply] at p₁
      rw [← ((hL.weil _ Q (m ^ 2) (baseOver _)).1 _ _ (lev.torsion i) (lev.torsion k)).unique p₁ (lev.pairing i k)]
      exact p₂)
  let t : (Fin (2 * Q.g) → ℕ) → T := fun a => (List.ofFn fun i => b i ^ a i).prod
  have e : ∀ a, linComb lev.pt a = E (t a).1 := fun a => by rw [hb]; exact linComb_map f b a
  have e' : ∀ a, linComb (levelBasis lev' hg) a = E' (ρ (t a).1) := fun a => by rw [hb']; exact linComb_map f' b a
  let u : (Fin (2 * Q.g) → ZMod (m ^ 2)) → B.A := fun a => (t fun i => (a i).val).1
  have hu : ∀ a, u a ^ m ^ 2 = 1 := fun a => (t _).2
  have v₁ := isThetaPt_mul (fnOf c) ((IsUnit.mk0 c hc).map _) (hE.2 m hom hm _ u hu)
  have v₂ := hE'.2 m hom hm _ (fun a => ρ (u a)) fun a => (hρ.2 _ (hu a)).1
  have q : (fun a => fnOf (B'.uth m (ρ (u a)) 1)) = fun a => fnOf c * fnOf (B.uth m (u a) 1) :=
    funext fun a => by rw [(hρ.2 _ (hu a)).2]; exact map_mul _ _ _
  rw [q] at v₂
  have l : levelPoint lev rfl = fun a => E (u a) := funext fun a => e _
  have l' : levelPoint lev' hg = fun a => E' (ρ (u a)) := funext fun a =>
    (ThetaPtDet.levelPoint_eq _ _ _).trans (e' _)
  obtain ⟨σ, hσ, hσb⟩ := hT' _ lev lev' _ (l ▸ v₁) (l' ▸ v₂)
  refine ⟨σ, hσ, fun x hx => ?_⟩
  have := hσ.1
  obtain ⟨d, hd⟩ := lev.span F (𝟙 _) (E x) (by rw [← map_pow, hx, map_one])
  have hd' : linComb lev.pt (fun i => (d i : ℕ)) = E x :=
    (congrArg (linComb · _) (funext fun i => (Category.id_comp (lev.pt i)).symm)).trans hd
  have hx' : x = (t fun i => (d i : ℕ)).1 := E.injective (hd'.symm.trans (e _))
  rw [← hd', ThetaPtDet.linComb_comp, hx', ← e']
  exact congrArg (linComb · _) (funext hσb)

theorem exists_iso_fib : Laws → ThetaPtDeterminesSt → BrUthSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R), D.PsiEven → D.TauBimult → D'.PsiEven → D'.TauBimult → D.P.g = D'.P.g → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (Q Q' : PolAV (Sp F)) (Φ : Q.A.left ⟶ D.P.A.left) (Φ' : Q'.A.left ⟶ D'.P.A.left), IsFib D F Q Φ → IsFib D' F Q' Φ' → ∀ n : ℕ, n.Prime → Odd n → (n : F) ≠ 0 → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (c : F) (ρ : N.A → N'.A), c ≠ 0 → TorsMap N.toNumB N'.toNumB (n ^ j) c ρ → ∃ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ ∧ ∀ (x : baseOver (Sp F) ⟶ Q.A) (b : N.A), b ^ (n ^ j) ^ 2 = 1 → (ν.eA b).left = x.left ≫ Φ → (ν'.eA (ρ b)).left = (x ≫ σ.hom).left ≫ Φ' := by
  intro hL hT hU R _ _ D D' a₁ a₂ a₃ a₄ hg F _ _ _ N N' ν ν' Q Q' Φ Φ' hΦ hΦ' n hn ho hF
  obtain ⟨E, hE, rE⟩ := exists_reads hU a₁ a₂ ν hΦ
  obtain ⟨E', hE', rE'⟩ := exists_reads hU a₃ a₄ ν' hΦ'
  obtain ⟨j₀, h⟩ := exists_iso_of_reads hL hT (hΦ'.2.2.trans (hg.symm.trans hΦ.2.2.symm)) rE rE' hn ho hF
  refine ⟨j₀, fun j hj c ρ hc hρ => ?_⟩
  obtain ⟨σ, hσ, hb⟩ := h j hj c ρ hc hρ
  refine ⟨σ, hσ, fun x b hb' hx => ?_⟩
  obtain rfl : x = E b := Over.OverMorphism.ext
    (hΦ.1.1.hom_ext (hx.symm.trans (hE b)) (by rw [Over.w, Over.w]))
  rw [hb b hb', hE']

end GlobalTheory.Ex.FibIso
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecLiftClosed

variable {X Z : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem gs_comb {n : ℕ} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (W : X.Opens) (hz : r z ∈ W)
    (c : Fin n → R) (u : Fin n → Γ(X, W)) :
    gs r z W (∑ i, AbLaw.cst p W (c i) * u i) =
      ∑ i, gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) * gs r z W (u i) := by

  rw [gs_eq r z _ hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => (gs_eq r z _ hz _).symm.trans ((gs_mul r z _ hz _ _).trans ?_)
  exact congrArg (· * _) ((gs_res r z le_top hz _).trans (gs_pull r p z ⊤ trivial _))

theorem gs_const_comp (q : Z ⟶ Spec (CommRingCat.of R')) (h : R →+* R') (z : Z) (a : R) :
    gs (q ≫ Spec.map (CommRingCat.ofHom h)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) =
      gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (h a)) := by
  refine (gs_pull q (Spec.map (CommRingCat.ofHom h)) z ⊤ trivial _).symm.trans ?_
  exact congrArg (gs q z ⊤) (congrArg (fun t => t.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom h))).symm

def combSec {n : ℕ} (p : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (c : Fin n → R) (τ : Fin n → LB.Sec M) :
    LB.Sec M where
  f := fun k => ∑ i, AbLaw.cst p (M.U k) (c i) * (τ i).f k
  compat := fun i j => fn_ext fun y hy => by
    refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit _ y _ hy _) (gs_res _ y _ hy _))).symm)
    refine (gs_comb p (𝟙 X) y (M.U i) hy.1 _ _).trans (Eq.trans ?_ (congrArg (_ * ·)
      (gs_comb p (𝟙 X) y (M.U j) hy.2 _ _)).symm)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [GlobalTheory.SecPullIso.gs_sec_trans (τ a) (𝟙 X) y hy.1 hy.2, mul_left_comm]

theorem exists_lift : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∀ (A' : Type) [CommRing A'] (g : A →+* A'), Function.Surjective g → ∀ (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)), M'.IsLB → w.IsGen → ∀ s' : LB.Sec M', ∃ s : LB.Sec M, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) := by
  intro A _ _ _ X f hf hp M hM K _ g₀ hg₀ X₀ π f₀ hπ M₀ w₀ hM₀ hw₀ hH A' _ g hg X' β f' hβ M' w hM' hw s'
  obtain ⟨n, τ, hτ⟩ := GlobalTheory.T.exists_sections_basis_baseChange_h1Vanishing A X f hf hp M hM K g₀ hg₀ X₀ π f₀ hπ M₀ w₀ hM₀ hw₀ hH
  choose τ' hτ' using fun i => (GlobalTheory.SecPullIso.section_pull X X' β M M' w hM hM' hw (τ i)).1.exists
  obtain ⟨c, hc, -⟩ := hτ A' g X' β f' hβ M' w τ' hM' hw hτ' s'
  choose d hd using fun i => hg (c i)
  refine ⟨combSec f d τ, fun z k k' hk hk' => ?_⟩
  refine (gs_comb f β z (M.U k) hk _ _).trans ?_
  rw [hc k', gs_comb f' (𝟙 X') z (M'.U k') hk', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hβ.w, gs_const_comp, hd, hτ' i z k k' hk hk', Category.id_comp, mul_left_comm]

end GlobalTheory.SecLiftClosed
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem GlobalTheory.FullPoint.fullAt_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {K : Type} [Field K] (y : Sp K ⟶ Xo.XF c) (o : Full D K) :
    FullAt Y y o ↔ FullPoint.IsFibre Y.oF y o ∧ ∀ f : KA l →+* K, y ≫ pullback.fst _ _ ≫ Xo.s = spMap f →
      o.ρ = f (baseKA l).ρ ∧ (o.I.ζ l.A : K) = f (baseKA l).ζ :=
  ⟨fun ⟨φ, a, b, c, d, e, f⟩ => ⟨⟨φ, a, b, c, d, e⟩, f⟩, fun ⟨⟨φ, a, b, c, d, e⟩, f⟩ => ⟨φ, a, b, c, d, e, f⟩⟩

theorem GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] (bF : c.F →+* K), (∀ o : Full D K, (∀ r : c.F, (r : ℂ) = H.rt0 → o.ρ = bF r) → (∀ z : c.F, (z : ℂ) = zeta l.A → (o.I.ζ l.A : K) = bF z) → ∃! y : Sp K ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap bF ∧ FullAt Y y o) ∧ (∀ y : Sp K ⟶ Xo.XF c, ∃ o, FullAt Y y o) ∧ ∀ (K' : Type) [Field K'] (f : K →+* K') y o o', FullAt Y y o → FullExt f o o' → FullAt Y (spMap f ≫ y) o' := by
  intro hv _ _ _ _ _ _ E _ _ _ H D l Xo c W₀ Y K _ _ bF
  refine ⟨fun o hρ hζ => ?_, fun y => ?_, fun K' _ f y o o' h h' => ?_⟩
  · obtain ⟨y, ⟨h₁, h₂⟩, hu⟩ := FullPoint.existsUnique_point hv.1.1 Y bF o hρ hζ
    refine ⟨y, ⟨h₁, (FullPoint.fullAt_iff Y y o).2 ⟨h₂, fun f hf => ?_⟩⟩,
      fun y' h => hu y' ⟨h.1, ((FullPoint.fullAt_iff Y y' o).1 h.2).1⟩⟩
    rw [pullback.condition, ← Category.assoc, h₁, ← spMap_comp] at hf
    obtain rfl := FullPoint.spMap_inj hf
    exact ⟨hρ _ rfl, hζ _ rfl⟩
  · obtain ⟨o, h⟩ := FullPoint.exists_isFibre Y.oF y
    exact ⟨o, (FullPoint.fullAt_iff Y y o).2 h⟩
  · obtain ⟨hρ, hζ, ψ, g₁, g₂, g₃, g₄⟩ := h'
    obtain ⟨h₁, h₂⟩ := (FullPoint.fullAt_iff Y y o).1 h
    refine (FullPoint.fullAt_iff Y _ o').2 ⟨FullPoint.IsFibre.ext f h₁ ψ g₁ g₂ g₃ g₄, fun g hg => ?_⟩
    obtain ⟨j, hj⟩ : ∃ j : KA l →+* K, y ≫ pullback.fst _ _ ≫ Xo.s = spMap j :=
      ⟨(Spec.preimage (y ≫ pullback.fst _ _ ≫ Xo.s)).hom, (Spec.map_preimage _).symm⟩
    rw [Category.assoc, hj, ← spMap_comp] at hg
    obtain rfl := FullPoint.spMap_inj hg
    rw [hρ, hζ _ l.A_pos, (h₂ j hj).1, (h₂ j hj).2]
    exact ⟨rfl, rfl⟩
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_arcIsometry_torsion_integralGauge : Laws → BrGtSt → AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing O') F] (S : ValuationSubring F), (∀ r : O', algebraMap (FractionRing O') F (algebraMap O' _ r) ∈ S) → ∃ A : Lift a F, A.ν.Integral S := by
  first | exact @GlobalTheory.Ex.ArcLift.exists_lift | exact GlobalTheory.Ex.ArcLift.exists_lift | (intros; apply GlobalTheory.Ex.ArcLift.exists_lift <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.LiftExt
open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem qkExt_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' F'' : Type} [Field F] [Field F']
    [Field F''] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] [Algebra (FractionRing R) F'']
    {f : F →+* F'} {f' : F' →+* F''} {k : ℕ} {p : QkPt D F k} {p' : QkPt D F' k} {p'' : QkPt D F'' k}
    (h : QkExt f p p') (h' : QkExt f' p' p'') : QkExt (f'.comp f) p p'' := by
  have e : spMap (f'.comp f) = spMap f' ≫ spMap f := spMap_comp' f f'
  refine ⟨h'.1.trans h.1, by rw [h'.2.1, h.2.1, e, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (val_corr hJ (h'.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h.2.2 χ) _).trans
    ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
  rw [e, Category.assoc]

theorem equiv_of_base {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F F' : Type} [Field F]
    [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ}
    {p₀ : QkPt D (FractionRing R) k} {r : QkPt D F k}
    (h : ∀ p, QkExt (algebraMap (FractionRing R) F) p₀ p → QkPt.Equiv D F p r) (p' : QkPt D F' k)
    (hp' : QkExt (algebraMap (FractionRing R) F') p₀ p') : QkPt.Equiv D F' p' (qkExt hB f hf r) := by
  obtain ⟨p, hp, -⟩ := existsUnique_qkExt hB (algebraMap (FractionRing R) F) (RingHom.ext fun _ => rfl) p₀
  have h₁ := qkExt_trans hp ((qkExt_iff hB f hf p _).2 rfl)
  rw [hf] at h₁
  rw [(existsUnique_qkExt hB (algebraMap (FractionRing R) F') (RingHom.ext fun _ => rfl) p₀).unique hp' h₁]
  exact qkExt_congr hB f hf (h p hp)

theorem exists_lift_ext : Laws → BrGtSt → BrWpSt → AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (F F' : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing O') F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing O') F'] (f : F →+* F'), f.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F' → ∀ S : ValuationSubring F', (∀ r : O', algebraMap (FractionRing O') F' (algebraMap O' _ r) ∈ S) → ∀ A : Lift a F, ∃ A' : Lift a F', A'.ν.Integral S ∧ ∃ I : NumD.Hom f A.N A'.N, I.lam = 1 ∧ f A.ρ = A'.ρ ∧ (∀ n, 0 < n → f (A.I.ζ n) = A'.I.ζ n) ∧ (∀ y, A'.ν.eX (I.e y) = A.ν.eX y) ∧ ∀ n v, (A'.q n v).1.1.toAdd = I.e (A.q n v).1.1.toAdd ∧ I.Rel (A.q n v).1.2 (A'.q n v).1.2 := by
  intro hL hGt hWp E _ _ _ H D l Xo c W₀ Y R _ _ _ b ϖ a _ F F' _ _ _ _ _ _ f hf S hS A
  have hf₀ : ∀ x, f (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x := fun x =>
    DFunLike.congr_fun hf x
  have : CharZero F := charZero_of_isPrimitiveRoot A.I.ζ_prim
  obtain ⟨J', hg, hJ⟩ := GlobalTheory.ValuesExist.exists_gauge F' S a.D₀.P.isLB
  obtain ⟨N', ν', rfl, hth⟩ := GlobalTheory.GaugeValues.exists_numOf hL R a.D₀ a.even a.bimult F' J' hg A.ν.th A.ν.th_gen
  have G := (hGt R a.D₀ a.even a.bimult F A.N A.ν).2.2.2.2
  have G' := (hGt R a.D₀ a.even a.bimult F' N' ν').2.2.2.2
  obtain ⟨I, hlam, heX, hI⟩ := GlobalTheory.T.exists_numDHom_degenerationValues_fieldExtension R a.D₀ F F' f hf A.N N' A.ν ν' hth
  have hw : ∀ k, 1 ≤ k → ∀ (p p' : QkPt a.D₀ F k) (z : F), WeilQkIs a.D₀ F k p p' z →
      WeilQkIs a.D₀ F' k (qkExt a.bimult f hf p) (qkExt a.bimult f hf p') (f z) := fun k hk p p' z h => by
    obtain ⟨q, hq, -⟩ := (G k).1 p
    obtain ⟨q', hq', -⟩ := (G k).1 p'
    obtain ⟨r, hr, -⟩ := (G' k).1 (qkExt a.bimult f hf p)
    obtain ⟨r', hr', -⟩ := (G' k).1 (qkExt a.bimult f hf p')
    have e := hI k _ _ _ _ ((qkExt_iff a.bimult f hf _ _).2 rfl) hq hr
    have e' := hI k _ _ _ _ ((qkExt_iff a.bimult f hf _ _).2 rfl) hq' hr'
    rw [hWp R a.D₀ a.even a.bimult F' N' ν' k hk _ _ _ _ _ hr hr',
      (GlobalTheory.T.hom_transport_alt F F' f A.N N' I).2.2.2.1 k q q' r r' e.1 e.2 e'.1 e'.2,
      (hWp R a.D₀ a.even a.bimult F A.N A.ν k hk _ _ _ _ _ hq hq').1 h]
    rfl
  choose q' hq' using fun (n : ℕ) (v : D.La) => ((G' n).1 (qkExt a.bimult f hf (A.I.ev n v))).exists
  refine ⟨{ ρ := f A.ρ
            ρ_sq := by rw [← map_pow, A.ρ_sq, map_neg]; simp
            det := fun σ => ?_
            I := tateExt f hf a.bimult hL A.I hw, N := N', ν := ν', q := q', hq := hq'
            be := { be := a.be.compl₁₂ ν'.eX.toAddMonoidHom.toIntLinearMap ν'.eX.toAddMonoidHom.toIntLinearMap
                    symm := fun y z => a.be_symm _ _
                    pos := fun y hy => a.be_pos _ fun h => hy (ν'.eX.map_eq_zero_iff.1 h)
                    dvd := fun y z => a.be_dvd _ _ }
            be_eq := fun _ _ => rfl
            ρ_eq := fun r hr => (congrArg f (A.ρ_eq r hr)).trans (hf₀ _)
            ζ_eq := fun z hz => (congrArg f (A.ζ_eq z hz)).trans (hf₀ _)
            levA := fun v => equiv_of_base a.bimult f hf (A.levA v)
            levM := fun v hv => equiv_of_base a.bimult f hf (A.levM v hv)
            closed := inferInstance },
    fun x => hJ _ (GlobalTheory.ValuesExist.exists_ext a.D₀ F' S hS x), I, hlam, rfl, fun _ _ => rfl, heX,
    fun n v => hI n _ _ _ _ ((qkExt_iff a.bimult f hf _ _).2 rfl) (A.hq n v) (hq' n v)⟩
  obtain ⟨τ, rfl⟩ := DetExtend.exists_factor f σ
  obtain ⟨n, h₁, h₂⟩ := A.det τ
  have := a.D₀.P.isAb.smooth
  refine ⟨n, ?_, h₂.trans (by
    by_cases h : τ H.rt = A.ρ
    · rw [if_pos h, if_pos (show f.comp τ H.rt = f A.ρ from congrArg f h)]
    · rw [if_neg h, if_neg (show ¬ f.comp τ H.rt = f A.ρ from fun e => h (f.injective e))])⟩
  have e : spMap ((algebraMap (FractionRing R) F').comp (algebraMap R _)) =
      spMap f ≫ spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _)) := by
    rw [← spMap_comp', ← RingHom.comp_assoc, hf]
  rw [e]
  exact (DetExtend.lieMult_extend f _ _ τ n).2 h₁

end GlobalTheory.LiftExt
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.nonempty_uniformisation_trait_in_abelianLocus : GlobalTheory.LN.UDvrSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → Set.range χ ⊆ abLocus t.G → Nonempty (PELUnif (maximalIdeal W) t') := by
  first | exact @GlobalTheory.AbelianTrait.nonempty_pelUnif_of_abLocus | exact GlobalTheory.AbelianTrait.nonempty_pelUnif_of_abLocus | (intros; apply GlobalTheory.AbelianTrait.nonempty_pelUnif_of_abLocus <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.semiAbelianHomExtension_of_laws : Laws → Laws2 → HomExtSt := by
  first | exact @GlobalTheory.LN.homExt_of_laws | exact GlobalTheory.LN.homExt_of_laws | (intros; apply GlobalTheory.LN.homExt_of_laws <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

theorem _root_.GlobalTheory.T.torus_cut_by_invariantRatios_field : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H) (a) (j : Fin d → C.I), GeometricallyConnected H.hom → C.Torus c i → C.Based c a j → C.KerIs a j i := by
  first | exact @GlobalTheory.ZJ.Charts.kerIs_of_torus | exact GlobalTheory.ZJ.Charts.kerIs_of_torus | (intros; apply GlobalTheory.ZJ.Charts.kerIs_of_torus <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.thetaSections_independent_on_closed_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ l, ∀ z ∈ Q.W l, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (j), Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Q.G → g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x → ∑ i, c i * valF g _ ((Q.σ l i).f j) = 0) → c = 0 := by
  first | exact @GlobalTheory.ZH.IndepFib.indep_on_closed_fibre | exact GlobalTheory.ZH.IndepFib.indep_on_closed_fibre | (intros; apply GlobalTheory.ZH.IndepFib.indep_on_closed_fibre <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.family_fibre_eq_uniformised_pullback_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (χ : Sp R ⟶ Y.X) (m : SABMap t Y.t χ) (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : Sp F ⟶ Xo.XF c), y ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ → ∀ (o : Full D F) (φ₀ : o.P.A.left ⟶ Y.oF.t.G.left), IsGrpPullback o.P.A Y.oF.t.G y φ₀ → LBIso o.P.L (Y.oF.t.PP.L.pull φ₀) → (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ₀ = φ₀ ≫ (Y.oF.t.act.act x).left) → ∃ φ : o.P.A.left ⟶ P.A.A.left, IsGrpPullback o.P.A P.A.A (jFK (R := R) F) φ ∧ LBIso o.P.L (P.A.L.pull φ) ∧ (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ = φ ≫ (P.oA.act x).left) ∧ φ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ = φ₀ ≫ Y.m.φ := by
  first | exact @GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre | exact GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre | (intros; apply GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre <;> assumption)
end
