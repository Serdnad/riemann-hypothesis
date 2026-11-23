module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Algebra.MvPolynomial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


noncomputable section

namespace UpperTheory.V.Hi.LvR

section Abs

variable {l : ℕ} [Fact l.Prime] {F' F : W.GFrame l} (h : W.FHom F' F)

theorem ofRep_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) :
    (W.GDet.ofRep ρ).comap φ = W.GDet.ofRep (ρ.comp φ) := by
  apply W.GDet.ext
  intro B _ _ y
  have key : ∀ z : MonoidAlgebra B H,
      W.GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ z) = W.GDet.repAlg (ρ.comp φ) B z := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    | single g b => simp [W.GDet.repAlg, MonoidAlgebra.lift_single]
  exact congrArg Matrix.det (key y)

theorem chi_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G) (g : H) :
    (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
  simp only [W.GDet.chi, W.GDet.comap, MonoidAlgebra.mapRingHom_single, map_one]
  show (D.D A[X]) (MonoidAlgebra.mapDomainRingHom A[X] φ _) = _
  rw [map_sub, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply,
    MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single, map_one]

theorem polar_comap (O : Type) [CommRing O] [Algebra ℤ_[l] O] {R : Type} [CommRing R] [Algebra O R] {n : ℕ}
    (D : W.GDet n R F.G₀) (hD : F.IsPolar O D) : F'.IsPolar O (D.comap h.π₀) := by
  intro B _ _ _ _ y
  have key : ∀ z : MonoidAlgebra B F'.G₀, MonoidAlgebra.mapDomainRingHom B h.π₀ (F'.star O B n z) =
      F.star O B n (MonoidAlgebra.mapDomainRingHom B h.π₀ z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp [W.GFrame.star]
    | add a b ha hb =>
      simp only [W.GFrame.star, map_add (f := _), MulOpposite.unop_add] at *
      rw [ha, hb]
    | single g b =>
      have hc : h.π₀ (F'.conj g) = F.conj (h.π₀ g) := by
        apply Subtype.ext
        show h.π (F'.c * (g : F'.Γ) * F'.c⁻¹) = F.c * h.π g * F.c⁻¹
        rw [map_mul, map_mul, map_inv, h.hc]
      have he : F'.eps O B g = F.eps O B (h.π₀ g) := by
        apply Units.ext
        show (algebraMap O B) ((algebraMap ℤ_[l] O) (F'.ε g : ℤ_[l])) =
          (algebraMap O B) ((algebraMap ℤ_[l] O) (F.ε (h.π g) : ℤ_[l]))
        rw [h.hε]
      simp [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single, hc, he]
  show D.D B (MonoidAlgebra.mapDomainRingHom B h.π₀ _) = D.D B (MonoidAlgebra.mapDomainRingHom B h.π₀ _)
  rw [key]
  exact hD B _

def upG {Lc : Pa.Loc} {G' G : Pa.Glob l Lc} (h : G'.Hom G) {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    (r : Resid G.frame O n) (h1 : ∀ i, IsOpen (((r.chib i).comp h.p₀).ker : Set G'.G₀))
    (h2 : Function.Injective fun i => (r.chib i).comp h.p₀)
    (h3 : G'.frame.IsPolar O (W.GDet.ofRep (W.diagRep fun i => (r.chib i).comp h.p₀))) : Resid G'.frame O n :=
  ⟨fun i => (r.chib i).comp h.p₀, h1, h2, h3, r.psib, r.psib_open, r.th, r.th_comm⟩

theorem upG_compat {Lc : Pa.Loc} {G' G : Pa.Glob l Lc} (h : G'.Hom G) {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    (r : Resid G.frame O n) (h1 h2 h3) : Pa.Glob.Compat h (upG h r h1 h2 h3) r := ⟨fun _ => rfl, rfl, rfl⟩

end Abs

section Gen

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))

def fh : W.FHom V.frame V0.frame where
  π := h.p
  π_cont := h.cont
  hη := h.η
  hc := h.c
  hε := h.ε
  vl v := v
  gv _ := MonoidHom.id _
  gv_cont _ := continuous_id
  hφ v g := (h.φ v g).symm
  hI _ _ hg := hg

def p0 : V.frame.G₀ →* V0.frame.G₀ := (fh h).π₀

theorem continuous_levelChangeBaseGroupHom : Continuous (p0 h) := (h.cont.comp continuous_subtype_val).subtype_mk _

theorem surjective_levelChangeBaseGroupHom : Function.Surjective (p0 h) := by
  intro g
  obtain ⟨x, hx⟩ := h.surj (g : V0.frame.Γ)
  have hxk : V.η x = 1 := by
    have := h.η x
    rw [hx] at this
    exact this.symm.trans g.2
  exact ⟨⟨x, hxk⟩, Subtype.ext hx⟩

theorem levelChangeBaseGroupHom_apply_projection (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (g : G L Ω) : p0 h (V.pr g) = V0.pr g := Subtype.ext (hp _)

def rUp : Resid V.frame O n where
  chib i := (r.chib i).comp (p0 h)
  chib_open i := (r.chib_open i).preimage (continuous_levelChangeBaseGroupHom h)
  chib_inj i j e := r.chib_inj (MonoidHom.ext fun g => by
    obtain ⟨x, rfl⟩ := surjective_levelChangeBaseGroupHom h g
    exact DFunLike.congr_fun e x)
  polar := by
    have := polar_comap (fh h) O (W.GDet.ofRep (W.diagRep r.chib)) r.polar
    rw [ofRep_comap] at this
    exact this
  psib := r.psib
  psib_open := r.psib_open
  th v i := @id (W.muG l (Dec (F := L) (s.A v.1)) →* Oˣ) (r.th v i)
  th_comm v i := @id (∀ g : W.muG l (Dec (F := L) (s.A v.1)), (g : Dec (F := L) (s.A v.1)) ∈
    (commutator (Dec (F := L) (s.A v.1))).topologicalClosure → @id (W.muG l (Dec (F := L) (s.A v.1)) →* Oˣ) (r.th v i) g = 1) (r.th_comm v i)


theorem psi_up {R : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R] (v : Vl l L) (i : Fin n) (ψ : Dec (F := L) (s.A v.1) →* Rˣ) :
    (rUp h).IsPsi v i ψ ↔ r.IsPsi v i ψ := by
  constructor
  · intro H
    have hm : ∀ g : W.muG l (Dec (F := L) (s.A v.1)),
        ((ψ g : Rˣ) : R) = algebraMap O R ((r.th v i g : Oˣ) : O) := fun g => H.mu g
    exact ⟨H.cont, H.red, hm⟩
  · intro H
    have hm : ∀ g : W.muG l (Dec (F := L) (s.A v.1)),
        ((ψ g : Rˣ) : R) = algebraMap O R ((r.th v i g : Oˣ) : O) := fun g => H.mu g
    exact ⟨H.cont, H.red, hm⟩

theorem rUp_Dbar : (rUp h).Dbar = r.Dbar.comap (p0 h) := by
  rw [Resid.Dbar, Resid.Dbar, ofRep_comap]; rfl

def rN : Resid (Pa.globOf r V).frame O n :=
  upG h (Pa.residOf r) (rUp h).chib_open (rUp h).chib_inj (rUp h).polar

theorem rN_compat : Pa.Glob.Compat h (rN h) (Pa.residOf r) := upG_compat _ _ _ _ _

theorem rN_Ip_le (u : s.St) (g : V.η.ker) (hg : g ∈ (rN h).Ip u) : g ∈ (rUp h).Ip u := by
  obtain ⟨⟨γ, ⟨h1, -⟩, rfl⟩, h2⟩ := hg
  exact ⟨⟨Subtype.val γ, h1, rfl⟩, Subgroup.mem_iInf.2 fun i => Subgroup.mem_iInf.1 h2 i⟩

theorem psi_N {R : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R] (v : Vl l L) (i : Fin n) (ψ : Dec (F := L) (s.A v.1) →* Rˣ)
    (H : (rUp h).IsPsi v i ψ) : (rN h).IsPsi v i ψ := by
  have hm : ∀ g : W.muG l (Dec (F := L) (s.A v.1)),
      ((ψ g : Rˣ) : R) = algebraMap O R ((r.th v i g : Oˣ) : O) := fun g => H.mu g
  exact ⟨H.cont, H.red, hm⟩

def pairN {B : Type} [CommRing B] [Algebra O B] [Alg.IsCO O B] (u : Pair (rUp h) B) : Pair (rN h) B :=
  ⟨u.D, u.ψ, u.cont, u.red, fun v i => psi_N h v i _ (u.psi v i), u.P, u.Ord,
    fun w g hg => u.I w g (rN_Ip_le h w g hg)⟩

def lamUp (Λ : LamObj r) : LamObj (rUp h) where
  Λ := Λ.Λ
  κ := Λ.κ
  inert v i := by
    obtain ⟨ψ, hψ, e⟩ := Λ.inert v i
    exact ⟨ψ, (psi_up h v i ψ).2 hψ, e⟩
  univ R _ _ _ κ' hκ := Λ.univ R κ' fun v i => by
    obtain ⟨ψ, hψ, e⟩ := hκ v i
    exact ⟨ψ, (psi_up h v i ψ).1 hψ, e⟩

end Gen

end UpperTheory.V.Hi.LvR
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


section Abstract

open UpperTheory.V.W

private theorem jr_teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := inferInstanceAs (CharP (ResidueField O) l)
  haveI : PerfectRing (ResidueField O) l := inferInstance
  let j : ResidueField O →+* Perfection (O ⧸ maximalIdeal O) l :=
    Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O) (RingHom.id (ResidueField O))
  have hj : ∀ x, Perfection.coeff (O ⧸ maximalIdeal O) l 0 (j x) = x := fun x => by
    have := (Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O)).symm_apply_apply (RingHom.id (ResidueField O))
    exact RingHom.congr_fun this x
  refine ⟨(Perfection.teichmuller l (maximalIdeal O)).comp j, fun x => ?_⟩
  exact (Perfection.mk_teichmuller (j x)).trans (hj x)

private theorem jr_isTeich {l : ℕ} [hl : Fact l.Prime] {F : GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t ∧ ∀ i g, r.chib i g = 1 → t i g = 1 := by
  obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  obtain ⟨τ, hτ⟩ := jr_teich_ex l c.O
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩, fun i g h => ?_⟩
  · rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  · rw [MonoidHom.comp_apply, h, map_one]

private theorem jr_abs {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (J : Ideal B.B) {ι : Type} (K : Type) [CommRing K] [Algebra O K]
    (x : ι → B.B →ₐ[O] K) (hJ : ∀ i, ∀ b ∈ J, x i b = 0) (sep : ∀ b, (∀ i, x i b = 0) → b ∈ J)
    (ρ : ι → F.G₀ →* GL (Fin n) K) (hD : ∀ i, B.u.D.map (x i : B.B →+* K) = GDet.ofRep (mat (ρ i)))
    (form : ∀ i, ∃ P, F.IsForm O n (ρ i) P)
    (flag : ∀ i v, HasFlag ((ρ i).comp (F.φ v)) fun j => pushCh (x i : B.B →+* K) (B.u.ψ v j))
    (type : ∀ i t, r.IsTeich t → ∀ u, ∃ g : GL (Fin n) K, ∀ y ∈ F.Iu u,
      ((g * ρ i y * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun j => algebraMap O K (t j y))
    (unr : r.V0ok → ∀ i, ∀ g ∈ F.I0, ρ i g = 1)
    (hT : ∃ t, r.IsTeich t ∧ ∀ i g, r.chib i g = 1 → t i g = 1)
    (fin : ((Ideal.Quotient.mk J).comp (Λ.toPair B.u : Λ.Λ →+* B.B)).Finite)
    (tf : ∀ a : Λ.Λ, a ≠ 0 → ∀ b : B.B, Λ.toPair B.u a * b ∈ J → b ∈ J) : B.RingProps Λ J := by
  let f : ι → (B.B ⧸ J) →ₐ[O] K := fun i => Ideal.Quotient.liftₐ J (x i) (hJ i)
  have hf : ∀ i, (f i : B.B ⧸ J →+* K).comp (Ideal.Quotient.mk J) = x i := fun i => rfl
  have hinj : ∀ a, (∀ i, f i a = 0) → a = 0 := fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 (sep b ha)
  have hD' : ∀ i, (B.DD J).map (f i : B.B ⧸ J →+* K) = GDet.ofRep (mat (ρ i)) := fun i => by
    rw [UniversalOrdinaryDeterminantRing.DD, (UpperTheory.V.AlgebraTools.Det.mapApi B.u.D _).2.2.2.2.2.2.1, hf, hD]
  have hflag : ∀ i v, HasFlag ((ρ i).comp (F.φ v)) fun j => pushCh (f i : B.B ⧸ J →+* K) (B.psiT J v j) := flag
  have hP : F.IsPolar O (B.DD J) := UpperTheory.V.AlgebraTools.Det.polarInj F O _ n _ (fun _ => K) f hinj fun i => by
    obtain ⟨P, hP⟩ := form i
    rw [hD' i]
    exact (UpperTheory.V.AlgebraTools.Det.formRep F O K n (ρ i) P hP).2.2
  have hker : ∀ g, (∀ i, ρ i g = 1) → (B.DD J).Kills (MonoidAlgebra.single g 1 - 1) ∧
      (B.DD J).Kills (F.star O _ n (MonoidAlgebra.single g 1) - 1) := fun g hg => by
    have hk : (B.DD J).Kills (MonoidAlgebra.single g 1 - 1) := by
      refine UpperTheory.V.AlgebraTools.Det.kerTest (fun _ => K) (fun i => (f i : B.B ⧸ J →+* K)) (fun i => mat (ρ i)) _ hinj hD' _ fun i => ?_
      rw [map_sub, map_sub, map_one, map_one, MonoidAlgebra.mapRingHom_single, map_one]
      simp [GDet.repAlg, mat, hg i]
    refine ⟨hk, ?_⟩
    have h1 := UpperTheory.V.AlgebraTools.Det.killsStar F O _ n _ hP _ hk
    have h2 : F.star O (B.B ⧸ J) n (MonoidAlgebra.single g 1 - 1) = F.star O _ n (MonoidAlgebra.single g 1) - 1 := by
      simp [GFrame.star]
    rwa [h2] at h1
  refine ⟨fin, tf, hP, fun v g => ?_, fun v g => ?_, fun u g hg => hker g fun i => ?_, fun t ht u => ?_,
    fun h g hg => hker g fun i => unr h i g hg⟩
  · ext k
    rw [← sub_eq_zero]
    apply hinj
    intro i
    have h1 := (UpperTheory.V.AlgebraTools.Det.mapApi (B.DD J) (f i : B.B ⧸ J →+* K)).1 (MonoidAlgebra.single (F.φ v g) 1)
    rw [hD' i, MonoidAlgebra.mapRingHom_single, map_one, (UpperTheory.V.AlgebraTools.Det.repApi (mat (ρ i))).2.1] at h1
    have h2 := (UpperTheory.V.AlgebraTools.Det.flagRel _ _ (hflag i v)).1 g
    have h3 : mat ((ρ i).comp (F.φ v)) g = mat (ρ i) (F.φ v g) := rfl
    rw [h3, h1] at h2
    have h4 : (∏ j, (X - C ((B.psiT J v j g : (B.B ⧸ J)ˣ) : B.B ⧸ J))).map (f i : B.B ⧸ J →+* K) =
        ∏ j, (X - C ((pushCh (f i : B.B ⧸ J →+* K) (B.psiT J v j) g : Kˣ) : K)) := by
      rw [Polynomial.map_prod]
      simp
    have h5 := congrArg (fun p => p.coeff k) (h2.trans h4.symm)
    simp only [Polynomial.coeff_map] at h5
    rw [map_sub, sub_eq_zero]
    exact h5
  · have hk : (B.DD J).Kills (F.oEl v (B.psiT J v) g) := by
      refine UpperTheory.V.AlgebraTools.Det.kerTest (fun _ => K) (fun i => (f i : B.B ⧸ J →+* K)) (fun i => mat (ρ i)) _ hinj hD' _ fun i => ?_
      have h1 : MonoidAlgebra.mapRingHom F.G₀ (f i : B.B ⧸ J →+* K) (F.oEl v (B.psiT J v) g) =
          F.oEl v (fun j => pushCh (f i : B.B ⧸ J →+* K) (B.psiT J v j)) g := by
        unfold GFrame.oEl
        rw [map_list_prod, List.map_ofFn]
        congr 2
        funext j
        simp [pushCh]
      rw [h1]
      exact UpperTheory.V.AlgebraTools.Det.oElRep F O K n (ρ i) v _ (hflag i v) g
    exact ⟨hk, UpperTheory.V.AlgebraTools.Det.killsStar F O _ n _ hP _ hk⟩
  · obtain ⟨t, ht, ht1⟩ := hT
    obtain ⟨Q, hQ⟩ := type i t ht u
    have h1 := hQ g hg.1
    have h2 : ∀ j, t j g = 1 := fun j => ht1 j g (Subgroup.mem_iInf.1 hg.2 j)
    simp only [h2, Units.val_one, map_one, Matrix.diagonal_one] at h1
    have h3 : Q * ρ i g * Q⁻¹ = 1 := Units.ext h1
    simpa using h3
  · refine (UpperTheory.V.AlgebraTools.Det.injTest (fun _ => K) (fun i => (f i : B.B ⧸ J →+* K)) hinj).1 _ _ fun i => ?_
    obtain ⟨Q, hQ⟩ := type i t ht u
    have h1 : ((B.DD J).comap (F.Iu u).subtype).map (f i : B.B ⧸ J →+* K) =
        ((B.DD J).map (f i : B.B ⧸ J →+* K)).comap (F.Iu u).subtype := rfl
    rw [h1, hD', (UpperTheory.V.AlgebraTools.Det.repApi _).2.2.2.2.2.2.1, (UpperTheory.V.AlgebraTools.Det.repApi _).2.2.2.2.2.1]
    refine (UpperTheory.V.AlgebraTools.Det.repApi _).2.2.2.2.2.2.2 _ Q fun y => ?_
    have h2 : (RingHom.mapMatrix (f i : B.B ⧸ J →+* K)).toMonoidHom.comp
        (diagRep fun j => pushCh (algebraMap O (B.B ⧸ J)) ((t j).comp (F.Iu u).subtype)) y =
        Matrix.diagonal fun j => algebraMap O K (t j y) := by
      change (Matrix.diagonal _).map (f i) = _
      rw [Matrix.diagonal_map (map_zero _)]
      congr 1
      funext j
      exact (f i).commutes _
    rw [h2, ← hQ y y.2, ← Units.val_mul, inv_mul_cancel_right]
    rfl

private theorem jr_surj {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) {T : Type} [CommRing T] [Algebra O T] [Algebra Λ.Λ T] (f : B.B →ₐ[O] T)
    (hsurj : Function.Surjective f) (hlam : ∀ b, f (Λ.toPair B.u b) = algebraMap Λ.Λ T b) (K : Type) [CommRing K] [Algebra O K]
    (good : (T →ₐ[O] K) → Prop) (sep : ∀ t, (∀ x, good x → x t = 0) → t = 0)
    (pt : ∀ x, good x → ∃ ρ : F.G₀ →* GL (Fin n) K, (B.u.D.map f.toRingHom).map x.toRingHom = GDet.ofRep (mat ρ) ∧
      (∃ P, F.IsForm O n ρ P) ∧
      (∀ v, HasFlag (ρ.comp (F.φ v)) fun j => pushCh x.toRingHom (pushCh f.toRingHom (B.u.ψ v j))) ∧
      (∀ t, r.IsTeich t → ∀ u, ∃ g : GL (Fin n) K, ∀ y ∈ F.Iu u,
        ((g * ρ y * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun j => algebraMap O K (t j y)) ∧
      (r.V0ok → B.u.D.map (x.comp f : B.B →+* K) = GDet.ofRep (mat ρ) → ∀ g ∈ F.I0, ρ g = 1))
    (hT : ∃ t, r.IsTeich t ∧ ∀ i g, r.chib i g = 1 → t i g = 1) (hfin : (algebraMap Λ.Λ T).Finite)
    (htf : ∀ b : Λ.Λ, b ≠ 0 → ∀ t : T, algebraMap Λ.Λ T b * t = 0 → t = 0) : B.RingProps Λ (RingHom.ker f) := by
  choose ρ hD hform hfl hty hun using fun x : {x // good x} => pt x.1 x.2
  have hD' : ∀ x : {x // good x}, B.u.D.map (x.1.comp f : B.B →+* K) = GDet.ofRep (mat (ρ x)) := fun x => by
    rw [← hD x]
    exact ((UpperTheory.V.AlgebraTools.Det.mapApi B.u.D f.toRingHom).2.2.2.2.2.2.1 x.1.toRingHom).symm
  refine jr_abs B Λ _ K (fun x : {x // good x} => x.1.comp f) (fun x b hb => ?_) (fun b hb => ?_) ρ hD' hform hfl hty
    (fun h x => hun x h (hD' x)) hT ?_ ?_
  · rw [AlgHom.comp_apply, (RingHom.mem_ker).1 hb, map_zero]
  · exact sep (f b) fun x hx => hb ⟨x, hx⟩
  · let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
    have he : (Ideal.Quotient.mk (RingHom.ker f)).comp (Λ.toPair B.u : Λ.Λ →+* B.B) =
        (e.symm : T →+* B.B ⧸ RingHom.ker f).comp (algebraMap Λ.Λ T) := by
      refine RingHom.ext fun b => ?_
      change _ = e.symm (algebraMap Λ.Λ T b)
      rw [AlgEquiv.eq_symm_apply, ← hlam]
      rfl
    rw [he]
    exact (RingHom.Finite.of_surjective _ e.symm.surjective).comp hfin
  · intro a ha b hb
    refine htf a ha (f b) ?_
    rw [← hlam, ← map_mul]
    exact hb

end Abstract

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem galResContCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem UpperTheory.V.Hi.levelUR2GalRes :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (G : Type) [Group G] [TopologicalSpace G] (n : ℕ) (r : G →* GL (Fin n) (Qbar l)), Continuous r → ∀ φ : G → (ResidueField c.O)[X], IsLocallyConstant φ → ∀ S : Set G, Dense S → (∀ g ∈ S, ∀ (i : ℕ) (b : c.O), residue c.O b = (φ g).coeff i → ‖(r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖ < 1) → ∀ g (i : ℕ) (b : c.O), residue c.O b = (φ g).coeff i → ‖(r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖ < 1 := by
  intro l _ c G _ _ n r hr φ hφ S hS hSb g i b hb
  have hc : Continuous fun h : G => (r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
    (galResContCoeff n i).comp (Units.continuous_val.comp hr)
  have hU : IsOpen {h : G | φ h = φ g} := hφ.isOpen_fiber _
  have hW : IsOpen {h : G | ‖(r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i -
      (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i‖ < 1} :=
    isOpen_lt (continuous_norm.comp (hc.sub continuous_const)) continuous_const
  obtain ⟨h, ⟨hh1, hh2⟩, hhS⟩ := hS.inter_open_nonempty _ (hU.inter hW) ⟨g, rfl, by simp⟩
  have key := hSb h hhS i b (by rw [hb, Set.mem_setOf_eq.mp hh1])
  have hh2' := Set.mem_setOf_eq.mp hh2
  rw [norm_sub_rev] at hh2'
  calc ‖(r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖
      = ‖((r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i -
          (r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i) +
        ((r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i -
          algebraMap c.O (Qbar l) b)‖ := by congr 1; abel
    _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
    _ < 1 := max_lt hh2' key
end
