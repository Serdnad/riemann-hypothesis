module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle045
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle082
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcInTraceArc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle058
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle034
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle039
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle302
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeH
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.CuspFrom

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem tateIso_similar_zeta
    (he : ∀ n x y c c', e n x y c → e n x y c' → c = c') (I : TateIso D k Q act e) (I' : TateIso D' k Q act e) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧
      (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧
      (∀ n : ℕ, 0 < n → ∀ a, I.ev n a = I'.ev n (f n a)) ∧
      ∀ n : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν n := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D'.La, 0 < n → ∀ a, I.ev n a = I'.ev n (f a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    · obtain ⟨f, hf⟩ := tateIso_exists_lift_of_two_data I I' h
      exact ⟨f, fun _ => hf⟩
  have h2 : ∀ n : ℕ, ∃ ν : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | hn
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n hn).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n hn).pow_eq_one)
      exact ⟨i, fun _ => hi.symm⟩
  choose f hf using h1
  choose ν hν using h2
  refine ⟨f, fun n => ν n, ?_, ?_, ?_, ?_, ?_, hf, fun n hn => ?_⟩
  · intro n m hn hm a
    rw [← tateIso_ev_eq_iff_add I' hn, ← hf n hn, ← I'.tower n m hn hm, ← hf (n * m) (Nat.mul_pos hn hm),
      I.tower n m hn hm]
  · intro n hn
    refine ⟨fun a => ?_, fun a' => ?_⟩
    · rw [← I'.ker n hn, ← I.ker n hn, hf n hn]
    · obtain ⟨a, ha⟩ := (I.onto n hn _).1 (tateIso_ev_pow I' hn a')
      rw [hf n hn] at ha
      exact ⟨a, (tateIso_ev_eq_iff_add I' hn _ _).1 ha.symm⟩
  · intro n hn
    have h := I.ζ_prim n hn
    rw [hν n hn] at h
    exact Nat.isCoprime_iff_coprime.2 (((I'.ζ_prim n hn).pow_iff_coprime hn _).1 h)
  · intro n m hn hm
    have h : I'.ζ n ^ ν (n * m) = I'.ζ n ^ ν n := by
      rw [← hν n hn, ← I.ζ_pow n m hn hm, hν (n * m) (Nat.mul_pos hn hm), ← I'.ζ_pow n m hn hm, ← pow_mul,
        ← pow_mul, mul_comm m]
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, zpow_natCast, zpow_natCast, h, mul_inv_cancel]
  · intro n hn a b
    have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := he n _ _ _ _ e1 e2
    rw [hν n hn, ← zpow_natCast, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]
  · rw [zpow_natCast]
    exact hν n hn

end

theorem familyUnif_lattice_similar_zeta (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty)
    (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ty P) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] (U.Di i).La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ (U.Di i).EF (f n a) (f n a') - ν n * D.EF a a') ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, f l.M a = U.t i a + l.M • e) ∧
      (∀ a, ∃ e, f l.A a = U.t i a + l.A • e) ∧
      σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) := by
  obtain ⟨-, I, hζ, hA, hM⟩ := Xo.univ.geom ℂ (U.u i P) σ (U.over_σ i P hP)
  obtain ⟨f, ν, h1, h2, -, -, h5, h6, h7⟩ := tateIso_similar_zeta
    (fun n x y c c' => weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ n x y c c') I (familyUnifTateIso U hP)
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  refine ⟨f, ν, h1, h2, h5, fun a ha => ?_, fun a => ?_, ?_⟩
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) hM0, ← h6 _ hM0, ← hM a ha]
    exact U.ex_eta i P hP a ha
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) l.A_pos, ← h6 _ l.A_pos, ← hA a]
    exact U.ex_etaA i P hP a
  · rw [← hζ, h7 _ l.A_pos]
    exact expNegUnit_zpow_val _ _

theorem exists_arcIn_input : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (B : GlobalTheory.CM.PAT H (Sp ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) (ex : (Fin A.gB → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') → PrimAn H A → AbDat H A DB tyB eB → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → 1 ≤ Dw.p → 1 ≤ Dw.q → GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom) ex → ∃ (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC) (hA : Λ.A = A), (∀ v, Λ.Lifts (aC.eta v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v)))) ∧ ∀ v, Λ.Lifts (aC.etaA v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v))) := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x B hσ _
  let _ := H.starRing
  intro A gam ξ DB tyB eB ex ⟨hgam, _, T₀, hT₀⟩ hrk hbe ⟨hχ, hψ⟩ ⟨hF, hty, _, hEF, _⟩ hp hq hp1 hq1
    ⟨_, hol, add, onto, ker, lin, weil⟩
  have hK := GlobalTheory.ArcCM.known_holds
  obtain ⟨T, m, hg⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap (RingHom.id ℂ)) B
  obtain ⟨-, hiso⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ _ B _ m
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  obtain ⟨sym, hsym, hsym'⟩ := (GlobalTheory.isSymmetric_iff_exists_gen _ _ T.t.PP).1 T.t.sym
  have := T.t.act.hom H.w0
  obtain ⟨w, hw, hw'⟩ := CxFibre.exists_primGen T.t.PP (T.t.act.act H.w0) T.t.prim
  let oa : T.pol.OAct (𝓞 E) := ⟨T.t.act.toRingAct, fun a =>
    (GlobalTheory.RosLam.rosatiAdj_iff_lamEq hK.laws.globalFns _ T.pol _ _ (T.t.act.hom a) (T.t.act.hom _)).2 (by
      change GlobalTheory.CM.LamEq _ _ _ _ _ (T.t.act.act (H.bar a))
      simpa [GlobalTheory.CM.LamEq] using T.t.adj a)⟩
  obtain ⟨u, χ, hgP, lam, hAH, hrig, hθ, hex⟩ := CxFibre.exists_holUnif_of_exp hK.theta B.t.PP.isLB
    (spMap (RingHom.id ℂ)) T.pol T.t.PP.rig
    T.t.PP.rigGen m.φ m.cart ⟨w₀, hw₀⟩ A.abelian₂ A.discrete A.full A.Hm A.Hm_herm A.Hm_pos (fun a b => A.Ef a b) A.Ef_eq
    ex hol add onto
    (fun z => (ker z).trans ⟨fun ⟨a, ha⟩ => ha ▸ (eB a).2, fun hz => ⟨eB.symm ⟨z, hz⟩, by simp⟩⟩)
    (fun n a b c hn hc => by
      obtain ⟨a, rfl⟩ := eB.surjective a
      obtain ⟨b, rfl⟩ := eB.surjective b
      exact weil n a b c hn (by rw [hEF]; exact hc))
  have hact : ∀ (a : 𝓞 E) z, u.ex (fun i => tyB i (a : E) * z i) = u.ex z ≫ T.t.act.act a := fun a z =>
    Over.OverMorphism.ext (m.cart.1.hom_ext (by
      rw [hex, lin, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hex])
      (by rw [Over.w, Over.w]))
  have hact' : ∀ (a : 𝓞 E) z, u.ex (A.F a z) = u.ex z ≫ T.t.act.act a := fun a z => by
    rw [← hact]; exact congrArg u.ex (funext (hF a z))
  obtain rfl : χ = fun b : u.Λ => A.chi ⟨b, lam.le b.2⟩ := funext fun a => by
    rw [CxFibre.chi_eq T.t.PP.isLB _ w hw u A.Hm χ hAH (A.F H.w0) (hact' _) a
      ⟨_, lam.ge (A.F_mem H.w0 a (lam.le a.2))⟩ rfl, hχ]
    have h₁ := A.Ef_eq_im (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩
    rw [← A.H_conj, Complex.conj_im] at h₁
    have h₂ : (hermForm A.Hm a (A.F H.w0 a)).im = -(A.Ef (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩ : ℤ) := by
      rw [h₁, neg_neg]; rfl
    generalize A.Ef (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩ = n at h₂
    rw [h₂, ← Complex.exp_neg_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  obtain ⟨s, hs, -⟩ := hT₀ ((T₀ + 1 : ℝ) * Complex.I) (by simp)
  obtain ⟨f, ν, f₁, f₂, f₃, f₄, f₅, f₆⟩ :=
    familyUnif_lattice_similar_zeta E H Dw l Xo _ _ _ Uw.F (Uw.ik k) _ (Uw.period k ⟨_, hs⟩)
  obtain ⟨a, Λ, hA, -, -, -, -, -, -, heta, hetaA⟩ := GlobalTheory.ArcOfModel.exists_arcIn hK.laws hK.laws2 Dw l
    (RingHom.id c.F) σ T.pol T.t.PP.rig T.t.PP.rigGen T.t.cub sym hsym hsym' oa ⟨w, hw, hw'⟩ A u lam hAH hrig
    (fun j _ => hθ j) hact' hψ (Module.nontrivial_of_finrank_pos (R := 𝓞 E) (hrk ▸ one_pos)) hbe _ gam hgam
    (Uw.F.t (Uw.ik k)) f ν f₁ (fun n hn v => ((f₂ n hn).1 v).1) (fun n hn => (f₂ n hn).2)
    f₃ f₄ f₅
    (fun z hz => (congrArg σ (Subtype.ext hz)).trans f₆)
    (fun ρ hρ τ => by
      obtain ⟨τ₀, rfl⟩ := GlobalTheory.PeriodPoint.exists_embedding (RingHom.id ℂ) τ
      have hρ' : σ ρ = H.rt0 := by
        rw [← hσ]
        exact congrArg σ (Subtype.ext hρ)
      refine ⟨_, CxFibre.lieMult_card hK.theta T.pol hgP u _ tyB hact τ₀, ?_⟩
      rw [hrk, hρ']
      split_ifs with h
      · rw [(hty τ₀).1 h]; omega
      · rw [(hty τ₀).2 h]; omega)
  refine ⟨a, Λ.toGtAn₀, hA, fun v q hq => ?_, fun v q hq => ?_⟩
  · rw [(TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) (RingHom.comp_id _) _).unique hq (heta v)]
    exact qk_equiv_refl a.bimult _
  · rw [(TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) (RingHom.comp_id _) _).unique hq (hetaA v)]
    exact qk_equiv_refl a.bimult _

end GlobalTheory.CuspFrom
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam.Pad
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor

section Lin

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def horVal (K : Matrix (m ⊕ n) m ℂ) (C : Matrix n (m ⊕ n) ℂ) : ℂ :=
  (Matrix.fromRows (Classical.epsilon fun R : Matrix m (m ⊕ n) ℂ => R * K = 1) C).det

variable {K : Matrix (m ⊕ n) m ℂ} {C : Matrix n (m ⊕ n) ℂ} {R : Matrix m (m ⊕ n) ℂ} {S : Matrix (m ⊕ n) n ℂ}

theorem det_mul_det (h : C * K = 0) (hR : R * K = 1) (hS : C * S = 1) :
    (Matrix.fromRows R C).det * (Matrix.fromCols K S).det = 1 := by
  rw [← Matrix.det_mul, Matrix.fromRows_mul_fromCols, hR, hS, h, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_one, _root_.one_mul]

theorem horVal_mul (h : C * K = 0) (hR : R * K = 1) (hS : C * S = 1) :
    horVal K C * (Matrix.fromCols K S).det = 1 := by

  have hR0 : Classical.epsilon (fun R : Matrix m (m ⊕ n) ℂ => R * K = 1) * K = 1 :=
    Classical.epsilon_spec (p := fun R : Matrix m (m ⊕ n) ℂ => R * K = 1) ⟨R, hR⟩
  unfold horVal
  exact det_mul_det h hR0 hS

theorem horVal_eq (h : C * K = 0) (hR : R * K = 1) (hS : C * S = 1) : horVal K C = (Matrix.fromRows R C).det := by
  have h1 := horVal_mul h hR hS
  have h2 := det_mul_det h hR hS
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h2) (h1.trans h2.symm)

theorem horVal_ne_zero (h : C * K = 0) (hR : R * K = 1) (hS : C * S = 1) : horVal K C ≠ 0 :=
  left_ne_zero_of_mul_eq_one (horVal_mul h hR hS)

end Lin

section Hol

def HolTan {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} (B : Set V)
    (v : V → (Sp (DualNumber ℂ) ⟶ X)) : Prop :=
  ∀ (U : X.Opens) (f : Γ(X, U)), DifferentiableOn ℂ
    (fun b => (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (A := DualNumber ℂ) (v b) U f).snd) {b ∈ B | ⊤ ≤ v b ⁻¹ᵁ U}

def HolAlong {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} (N : Set (CxPts p σ))
    (φ : CxPts p σ → ℂ) : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (x : V → CxPts p σ),
    IsOpen B → IsHolTo B (fun b => (x b).1) → Set.MapsTo x B N → DifferentiableOn ℂ (fun b => φ (x b)) B

def logDom (n a : ℕ) : Set (Fin n → ℂ) := {s | ∀ k : Fin n, if (k : ℕ) < a then (s k).re < 0 else ‖s k‖ < 1}

def logExp (a : ℕ) {n : ℕ} (s : Fin n → ℂ) : Fin n → ℂ := fun k => if (k : ℕ) < a then Complex.exp (s k) else s k

end Hol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Lattice

scoped instance decEqLetter : DecidableEq (Letter Dw) := Classical.decEq _

abbrev Idx (Dw : Datum H) (τ : E →+* ℂ) : Type := Fin (Dw.mult (conjEmb τ)) ⊕ Fin (Dw.mult τ)

def IsPerBasis (Di : Datum H) {J : Type} [Fintype J] [DecidableEq J] (x : J → Di.La) (hm : Matrix J J E) : Prop :=
  LinearIndependent (𝓞 E) x ∧ (∀ v, ∃ n : ℕ, n ≠ 0 ∧ n • v ∈ Submodule.span (𝓞 E) (Set.range x)) ∧
    (∀ (a : 𝓞 E) k k', ((Di.EF (a • x k) (x k') : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * hm k k')) ∧ hm.det ≠ 0

def IsIsom (Di : Datum H) (gm : Di.La ≃ₗ[𝓞 E] Di.La) : Prop := ∀ a b, Di.EF (gm a) (gm b) = Di.EF a b

def IsLev (l : Level H) (Di : Datum H) (gm : Di.La ≃ₗ[𝓞 E] Di.La) : Prop :=
  ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Di.La), ∃ e, gm a = a + l.M • e

variable {Di : Datum H}

def perMat {J : Type} (x : J → Di.La) (Q : Di.La →+ (Letter Dw → ℂ)) (ρ : E →+* ℂ) : Matrix (Fin (Dw.mult ρ)) J ℂ :=
  Matrix.of fun i k => Q (x k) ⟨ρ, i⟩

variable (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E)

def kerMat (Q : Di.La →+ (Letter Dw → ℂ)) : Matrix (Idx Dw τ) (Fin (Dw.mult (conjEmb τ))) ℂ :=
  ((hm.map (Formalism.L2.PjFree.relab c σ τ))ᵀ)⁻¹ * (perMat x Q (conjEmb τ))ᵀ

def perVal (Q : Di.La →+ (Letter Dw → ℂ)) : ℂ := horVal (kerMat c σ τ x hm Q) (perMat x Q τ)

def GoodPer (Q : Di.La →+ (Letter Dw → ℂ)) : Prop :=
  (∀ (a : 𝓞 E) v (z : Letter Dw), Q (a • v) z = Formalism.L2.PjFree.relab c σ z.1 (a : E) * Q v z) ∧
    perMat x Q τ * kerMat c σ τ x hm Q = 0 ∧
    (∃ R : Matrix (Fin (Dw.mult (conjEmb τ))) (Idx Dw τ) ℂ, R * kerMat c σ τ x hm Q = 1) ∧
    ∃ S : Matrix (Idx Dw τ) (Fin (Dw.mult τ)) ℂ, perMat x Q τ * S = 1

variable {c σ τ x hm}

theorem GoodPer.perVal_ne_zero {Q : Di.La →+ (Letter Dw → ℂ)} (h : GoodPer c σ τ x hm Q) : perVal c σ τ x hm Q ≠ 0 := by
  obtain ⟨-, h1, ⟨R, hR⟩, ⟨S, hS⟩⟩ := h
  exact horVal_ne_zero h1 hR hS

end Lattice

variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (σ : c.F →+* ℂ)

abbrev CxFr : Type := Σ x : CxPts (genStr Z) σ, EigFrame Z σ (x.1 ≫ genι Z)

variable {Z σ}

def Inner (x : CxPts (genStr Z) σ) : Prop := x.1 (IsLocalRing.closedPoint ℂ) ∉ genBd Z

def Chg (a a' : CxFr Z σ) (ρ : E →+* ℂ) (M : Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) ℂ) : Prop :=
  a.1 = a'.1 ∧ ∀ i, IsCombAtG Z.t (a'.1.1 ≫ genι Z) (a.2.v ρ) (M i) (a'.2.v ρ i)

def HolFam {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (a : V → CxFr Z σ) : Prop :=
  IsHolTo B (fun b => (a b).1.1) ∧ ∀ ρ i, HolTan B fun b => (a b).2.v ρ i

def Dirs {g : ℕ} (a : CxFr Z σ) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left)) (W : Letter Dw → Fin g → ℂ) : Prop :=
  ∀ z : Letter Dw, IsDerivAt0 e (W z) (a.2.v z.1 z.2)

abbrev Fam (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) {g : ℕ} (e : Fin g ≃ Letter Dw) : Type 1 :=
  FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) fun j => Formalism.L2.PjFree.relab c σ (e j).1

def Per {g : ℕ} {e : Fin g ≃ Letter Dw} (Fu : Fam Xo c σ e) (a : CxFr Z σ) (i : Fin Fu.n)
    (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) : Prop :=
  ∃ (P : (Fu.Di i).La →+ (Fin g → ℂ)) (W : Letter Dw → Fin g → ℂ) (y : Sp ℂ ⟶ Xo.XF c),
    IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P ∧ y ≫ pullback.fst _ _ = Fu.u i P ∧
    y ≫ Z.jQ = a.1.1 ∧
    (∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
      IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ ≫ Z.m0.toSABMap.φ)) ∧
    ∀ v, P v = ∑ z, Q v z • W z


open Classical in
def horOf {g : ℕ} {e : Fin g ≃ Letter Dw} (Fu : Fam Xo c σ e) (τ : E →+* ℂ) (x : ∀ i, Idx Dw τ → (Fu.Di i).La)
    (hm : Fin Fu.n → Matrix (Idx Dw τ) (Idx Dw τ) E) (a : CxFr Z σ) : ℂ :=
  if h : ∃ iQ : Σ i : Fin Fu.n, (Fu.Di i).La →+ (Letter Dw → ℂ), Per Fu a iQ.1 iQ.2 then
    perVal c σ τ (x h.choose.1) (hm h.choose.1) h.choose.2 else 0

def LogGrowth (h : CxFr Z σ → ℂ) : Prop :=
  ∀ x₀ : CxPts (genStr Z) σ, ∃ (N : Set (CxPts (genStr Z) σ)) (φ : CxPts (genStr Z) σ → ℂ), IsOpen N ∧ x₀ ∈ N ∧
    HolAlong N φ ∧ (∀ x ∈ N, φ x ≠ 0 ↔ Inner x) ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ),
      IsOpen B → HolFam B a → (∀ b ∈ B, (a b).1 ∈ N) → ∀ b₀ ∈ B, ∃ (C : ℝ) (k : ℕ), ∀ᶠ b in 𝓝 b₀, Inner (a b).1 →
        ‖h (a b)‖ ≤ C * (1 + |Real.log ‖φ (a b).1‖|) ^ k ∧ ‖(h (a b))⁻¹‖ ≤ C * (1 + |Real.log ‖φ (a b).1‖|) ^ k

def HorFn (τ : E →+* ℂ) (h : CxFr Z σ → ℂ) : Prop :=
  (∀ a, Inner a.1 → h a ≠ 0) ∧
  (∀ a a' M N, Inner a.1 → Chg a a' τ M → Chg a a' (conjEmb τ) N → h a' * M.det = h a * N.det) ∧
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ),
    IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → DifferentiableOn ℂ (fun b => h (a b)) B) ∧
  LogGrowth h

abbrev ExpMaps (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) : Type :=
  ∀ x : CxPts (genStr Z) σ, (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)

def IsExpChart {n g : ℕ} (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) : Prop :=
  e.target = Metric.ball 0 1 ∧ (∀ k, HolAlong e.source fun x => e x k) ∧ IsHolTo e.target (fun z => (e.symm z).1) ∧
  (∀ x ∈ e.source, ∀ v w, ex x (v + w) = ex x v * ex x w) ∧
  IsHolTo (e.target ×ˢ (Set.univ : Set (Fin g → ℂ))) (fun zw => (ex (e.symm zw.1) zw.2).left) ∧
  ∀ x ∈ e.source, (∀ w, ∃! v, IsTanAtG Z.t (x.1 ≫ genι Z) v ∧ IsDerivAt0 (fun u => (ex x u).left) w v) ∧
    ∀ v, IsTanAtG Z.t (x.1 ≫ genι Z) v → ∃! w, IsDerivAt0 (fun u => (ex x u).left) w v

def IsLogChart {n g r : ℕ} (a : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g)
    (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ) : Prop :=
  IsExpChart e ex ∧ (∀ x ∈ e.source, Inner x ↔ ∀ k : Fin n, (k : ℕ) < a → e x k ≠ 0) ∧
  ContinuousOn lam (logDom n a) ∧
  (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧
    (∀ w, ex (e.symm (logExp a s)) w = 1 ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) ∧
    ∀ j, ∑ m, ρ j m • lam s m = Pi.single j 1) ∧
  ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) →
    ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k

end GlobalTheory.ShFam.Hor
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolDiv

theorem idlAlong_fromSpecStalk {X : Scheme.{0}} (I : X.IdealSheafData) (x : X) {W : Type} [CommRing W] [IsLocalRing W]
    (g : X.presheaf.stalk x →+* W) :
    idlAlong I (Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecStalk x) = (FinalTheorems.stalkId I x).map g := by
  obtain ⟨⟨U, hU⟩, hx, -⟩ := EffCartierData.exists_affine_le (show x ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have e0 : ∀ (y : X) (hy : y ∈ U), X.fromSpecStalk y = Spec.map (X.presheaf.germ U y hy) ≫ hU'.fromSpec :=
    fun y hy => (hU'.fromSpecStalk_eq_fromSpecStalk hy).symm
  generalize hχ : Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecStalk x = χ
  have e1 : χ = Spec.map (X.presheaf.germ U x hx ≫ CommRingCat.ofHom g) ≫ hU'.fromSpec := by
    rw [← hχ, e0 x hx]
    exact (Spec.map_comp_assoc (X.presheaf.germ U x hx) (CommRingCat.ofHom g) hU'.fromSpec).symm
  have hc : χ (closedPoint W) ∈ U := by
    have : χ (closedPoint W) ∈ Set.range hU'.fromSpec :=
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun f => f (closedPoint W)) e1.symm)⟩
    rwa [hU'.range_fromSpec] at this
  have e2 : χ = Spec.map (X.presheaf.germ U _ hc ≫ Scheme.stalkClosedPointTo χ) ≫ hU'.fromSpec := by
    rw [Spec.map_comp, Category.assoc, ← e0 _ hc]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ).symm
  have e3 := Spec.map_injective ((cancel_mono hU'.fromSpec).1 (e1.symm.trans e2))
  unfold idlAlong
  rw [ds_stalkId_eq_map I ⟨U, hU⟩ _ hc, ds_stalkId_eq_map I ⟨U, hU⟩ x hx, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← e3]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.PolDiv
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem GlobalTheory.ShFam.EigFrame.exists_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (A B : Type) [CommRing A] [CommRing B] (φ : c.F →+* A) (x : Sp A ⟶ Z.X) (fr : EigFrame Z φ x) (ψ : A →+* B), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z A B _ _ φ x fr ψ
  open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.LocM.FrameBC in
  have h : GlobalTheory.LocM.IsFrame Z.t (ψ.comp φ) (spMap ψ ≫ x) ((fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i)) := by
    letI : Algebra c.F A := φ.toAlgebra
    letI : Algebra c.F B := (ψ.comp φ).toAlgebra
    let v : ∀ τ, Fin (Dw.mult τ) → TanM x Z.t.G := fun τ i => tanOf (fr.tan τ i)
    have eps_dual (a : A) : spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (Formalism.L2.Pj.dualMap ψ) := by
      rw [spMap_comp_spMap, spMap_comp_spMap]
      congr 1
      refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [Formalism.L2.Pj.dualMap, epsMul, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, smul_eq_mul, mul_comm]
    have he : ∀ τ i (a : 𝓞 E), (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) τ i ≫ (Z.t.act.act a).left =
        spMap (epsMul ((ψ.comp φ) (embK c τ a))) ≫ (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) τ i := fun τ i a => by
      show (spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) ≫ _ = _ ≫ spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i
      rw [Category.assoc, fr.eig τ i a, ← Category.assoc, eps_dual, Category.assoc, RingHom.comp_apply]
    have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (fr.eig τ i)) fun τ n hn => by
      exact (existsUnique_congr fun a => LieMet.isComb_iff (v τ) a n).1 (fr.basis τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
    have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM ψ (v k.1 k.2) := by
      have h := full_equiv (eB Dw).symm (full_bc ψ (full_equiv (eB Dw) h1))
      exact (funext fun k => congrArg (fun j : IxB Dw => resM ψ (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
    refine ⟨fun τ i => ⟨isTan_map ψ rfl (fr.tan τ i), he τ i⟩, fun τ w hw hwe => ?_⟩
    have h3 := eig_of_full c (fun τ i => resM ψ (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
      ((eig_iff c τ _).1 hwe)
    exact (existsUnique_congr fun a => LieMet.isComb_iff (fun i => resM ψ (v τ i)) a (tanOf hw)).2 h3
  exact ⟨⟨_, fun τ i => (h.1 τ i).1, fun τ i => (h.1 τ i).2, h.2⟩, fun _ _ => rfl⟩
end
