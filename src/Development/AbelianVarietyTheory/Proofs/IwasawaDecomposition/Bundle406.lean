module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle388
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle341
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConditionsConjUnitaryKeepsStdLattice
public import Formalism.LocalToGlobal.Columns.Adelic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle369
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle345
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.Columns.Bundle014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle358
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle392
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle340

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

section FrLev

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
  {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem frDiv_mem_GLint (p p' : DecoF E n ST SG Q) (hN : p.deco.1.N = p'.deco.1.N) (P : Q) :
    (p.fr P)⁻¹ * p'.fr P ∈ GLint E n P.1 := by
  intro v
  have h1 := p.2 P (((p.fr P)⁻¹ * p'.fr P) v)
  have h2 := p'.2 P v
  have e : p.1.2 P (((p.fr P)⁻¹ * p'.fr P) v) = p'.fr P v := by
    show p.fr P ((p.fr P).symm (p'.fr P v)) = p'.fr P v
    exact LinearEquiv.apply_symm_apply _ _
  rw [e] at h1
  rw [← h1, ← h2]
  show p'.fr P v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N ↔ p'.fr P v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p'.deco.1.N
  rw [hN]

theorem rhoP_eq_fr {g : GL (Fin n) (AfE F E)} {q : DecoF E n ST SG Q} (hq : IsPtOf hc g q) (P : Q) :
    rhoP F P.1 g = bc (algebraMap E (P.1.adicCompletion E)) (toGLm E n (q.fr P)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ (((toGLm E n (q.fr P) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
  rw [hq.fr P i j, qsp_toGLm_apply]

end FrLev

end GlobalTheory.Mem.Col2.TopCh

namespace GlobalTheory.Mem.Col2.TopCh

theorem mem_topU_iff : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (U : Subgroup (GL (Fin n) (AfE F E))) (k t y x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x * (k * t)) p' → (x ∈ topU U t Θ d ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p') := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q Λ Θ d hd N hdN hΘ U k t y x p p' hk hkP ht hU hp hp'
  set g := y * (k * t) with hg
  set z := (k * t)⁻¹ * x * (k * t) with hz
  have hgz : y * x * (k * t) = g * z := by rw [hg, hz]; group
  rw [hgz] at hp'
  have step := fun h : GLG (E := E) (n := n) (SG := SG) => ((GlobalTheory.T.isPtOf_mul_J0_decoration F E hc n ST SG Q g z p p' h).1 hp hp')
  have htU : t ∈ UAd hc n := principal_le_adelic_unitary hc n ST SG ht
  have hktU : k * t ∈ UAd hc n := mul_mem hk htU
  have hgU : g ∈ UAd hc n := hp.uni
  have hgzU : g * z ∈ UAd hc n := hp'.uni
  have hyU : y ∈ UAd hc n := by
    have e : y = g * (k * t)⁻¹ := by rw [hg]; group
    rw [e]; exact mul_mem hgU (inv_mem hktU)
  have hxU : x ∈ UAd hc n := by
    have e : x = y⁻¹ * (g * z) * (k * t)⁻¹ := by rw [hg, hz]; group
    rw [e]; exact mul_mem (mul_mem (inv_mem hyU) hgzU) (inv_mem hktU)
  have hU' : x ∈ U ↔ z ∈ levU hc n ST SG Λ.grp := by
    rw [hU x hxU]
    have e : k⁻¹ * x * k = t * z * t⁻¹ := by rw [hz]; group
    rw [e]
    have htL : t ∈ levU hc n ST SG Λ.grp := kOne_le_unipotentLevel hc n ST SG _ ht
    constructor
    · intro h
      have h2 := mul_mem (mul_mem (inv_mem htL) h) htL
      have e2 : t⁻¹ * (t * z * t⁻¹) * t = z := by group
      rwa [e2] at h2
    · intro h
      exact mul_mem (mul_mem htL h) (inv_mem htL)
  have hT : ∀ P : Q, rhoT F P.1 t x = rhoP F P.1 z := by
    intro P
    show rhoP F P.1 (t⁻¹ * x * t⁻¹⁻¹) = rhoP F P.1 z
    rw [hz]
    simp only [map_mul, map_inv, hkP P, one_mul, inv_inv, _root_.mul_inv_rev, inv_one, mul_one]
  have hZ : ∀ (hN : p.deco.1.N = p'.deco.1.N) (P : Q),
      rhoP F P.1 z = iotaP P.1 ⟨_, frDiv_mem_GLint p p' hN P⟩ := by
    intro hN P
    have e : rhoP F P.1 z = (rhoP F P.1 g)⁻¹ * rhoP F P.1 (g * z) := by
      rw [← map_inv, ← map_mul, inv_mul_cancel_left]
    rw [e, rhoP_eq_fr hp P, rhoP_eq_fr hp' P, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
    rfl
  have hL : ∀ (hN : p.deco.1.N = p'.deco.1.N) (P : Q),
      rhoT F P.1 t x ∈ locLev P.1 (Θ P) (d P) ↔ (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1)) ∈ (Θ P).H := by
    intro hN P
    rw [hT P, hZ hN P]
    exact qbU_rat (F := E) P.1 (algebraMap E (P.1.adicCompletion E)) (phi_int P.1) (phi_lt P.1) (Θ P) (d P) (hd P) (hdN P)
      (hΘ P) _
  have hNs : ∀ h : GLG (E := E) (n := n) (SG := SG), p'.deco = ((1, h) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco → p.deco.1.N = p'.deco.1.N := by
    intro h e
    rw [e]
    show p.deco.1.N = Formalism.HermitianLatticesTheory.gmap (1 : Sp E n ≃ₗ[E] Sp E n) p.deco.1.N
    exact (Formalism.L2.Col.gmap_one _).symm
  constructor
  · intro hx
    obtain ⟨hz0, hzr⟩ := (mem_levU hc n ST SG _).1 (hU'.1 hx.1)
    let h : Λ.grp := ⟨(redG hc n ST SG ⟨z, hz0⟩)⁻¹, inv_mem hzr⟩
    have hdeco : p'.deco = ((1, h.1) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco := (step h.1).1 ⟨hz0, (inv_inv _).symm⟩
    have hN := hNs h.1 hdeco
    have hc' : ∀ P : Q, (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1)) ∈ (Θ P).H := fun P =>
      (hL hN P).1 (rhoT_mem hx P)
    let θ : Θ.grp := ⟨fun P => (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1))⁻¹, fun P _ => inv_mem (hc' P)⟩
    refine ⟨h, θ, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hdeco.symm
    · funext P
      show (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * (((θ.1 P)⁻¹ : ↥(GLint E n P.1)) : Sp E n ≃ₗ[E] Sp E n) = p'.fr P
      show (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * ((p.fr P)⁻¹ * p'.fr P) = p'.fr P
      rw [one_mul, mul_inv_cancel_left]
  · rintro ⟨h, θ, hθ⟩
    have hdeco : p'.deco = ((1, h.1) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco := by rw [← hθ]; rfl
    obtain ⟨hz0, hzr⟩ := (step h.1).2 hdeco
    have hN := hNs h.1 hdeco
    refine ⟨hU'.2 ((mem_levU hc n ST SG _).2 ⟨hz0, by rw [hzr]; exact inv_mem h.2⟩), ?_⟩
    refine Subgroup.mem_iInf.2 fun P => Subgroup.mem_comap.2 ((hL hN P).2 ?_)
    have hfr : p'.fr P = p.fr P * (((θ.1 P)⁻¹ : ↥(GLint E n P.1)) : Sp E n ≃ₗ[E] Sp E n) := by
      rw [← hθ]
      show (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * _ = _
      rw [one_mul]
    have e : (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1)) = (θ.1 P)⁻¹ := by
      apply Subtype.ext
      show (p.fr P)⁻¹ * p'.fr P = _
      rw [hfr, inv_mul_cancel_left]
    rw [e]
    exact inv_mem (θ.2 P (Set.mem_univ _))

end GlobalTheory.Mem.Col2.TopCh
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

variable {B : Base} {X : PreX B.toPre}

theorem bc_prV_entry {B : Base} (v : HeightOneSpectrum (𝓞 B.host.F)) {n : ℕ} (m : GA B n)
    (h : bc (prV (E := B.host.E) v) m = 1) (r j : Fin n) :
    prV (E := B.host.E) v ((m : Matrix (Fin n) (Fin n) _) r j) = if r = j then 1 else 0 := by
  have := congrArg (fun g : GL (Fin n) (TensorProduct (↥B.host.F) B.host.E (HeightOneSpectrum.adicCompletion (↥B.host.F) v)) =>
    (g.1 : Matrix (Fin n) (Fin n) _) r j) h
  simpa [bc, Matrix.one_apply] using this

theorem natCast_not_mem_of_goodPl {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]
    {S : Set ℕ} {w : HeightOneSpectrum (𝓞 F)} (hw : GoodPl E S w) {g : ℕ} (hg : Nat.Prime g) (hgS : g ∈ S) :
    ((g : 𝓞 F) ∉ w.asIdeal) := by
  intro hmem
  have h0 : ((g : 𝓞 F ⧸ w.asIdeal)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hmem
  have hdvd : ringChar (𝓞 F ⧸ w.asIdeal) ∣ g := ringChar.dvd h0
  haveI : Nontrivial (𝓞 F ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  have hne : ringChar (𝓞 F ⧸ w.asIdeal) ≠ 1 := CharP.ringChar_ne_one
  rcases (Nat.dvd_prime hg).1 hdvd with h | h
  · exact hne h
  · apply hw.2.2
    show ringChar (𝓞 F ⧸ w.asIdeal) ∈ S
    rw [h]; exact hgS

theorem locCQ_conj_iff_eq_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι)
    (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∀ (n : ℕ) (t s : GA B n) (θ : GLQ B.fields.E n (I.Q a)),
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) →
      bc (prV (E := B.host.E) v) t = 1) →
    (∀ v ∈ Q, bc (prV (E := B.host.E) v) s = 1) →
    (LocCQ (I.Q a) n (t⁻¹ * s * t) θ ↔ θ = 1) := by
  intro B X I hI l u a Q hQ n t s θ ht hs
  have key : ∀ (P : I.Q a) (r j : Fin n),
      adAt B.host.F P.1 (((t⁻¹ * s * t : GA B n) : Matrix (Fin n) (Fin n) _) r j) = if r = j then 1 else 0 := by
    intro P r j
    have hvQ : HeightOneSpectrum.under (𝓞 B.host.F) P.1 ∈ Q := (hQ _).2 ⟨P.1, P.2, rfl⟩
    obtain ⟨w, -, hsel, hgood⟩ := ColIn.exists_of_mem_Q I P.2
    have hvw : HeightOneSpectrum.under (𝓞 B.host.F) P.1 = w := by
      ext1
      have := hI.sel_ok w
      rw [hsel] at this
      exact this
    have htv : bc (prV (E := B.host.E) w) t = 1 :=
      ht w (Or.inr fun j => natCast_not_mem_of_goodPl B.fields.E hgood (B.host.g_prime j) (hI.g_mem j))
    have hsv : bc (prV (E := B.host.E) w) s = 1 := hs w (hvw ▸ hvQ)
    have hm : bc (prV (E := B.host.E) w) (t⁻¹ * s * t) = 1 := by
      rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, htv, hsv, inv_one, one_mul, one_mul]
    have entry := bc_prV_entry w _ hm r j
    split_ifs with hrj
    · exact GlobalTheory.Mem.Col2.FullDt.adAt_eq_one_of_prV P.1 (by rw [hvw, entry, if_pos hrj])
    · exact GlobalTheory.Mem.Col2.TilX.adAt_eq_zero_of_prV P.1 _ (by rw [hvw, entry, if_neg hrj])
  constructor
  · intro hL
    funext P
    show θ P = 1
    rw [← inv_eq_one]
    apply Subtype.ext
    apply (Pi.basisFun B.fields.E (Fin n)).ext'
    intro j
    funext r
    have h1 := hL P r j
    rw [key P r j] at h1
    have h2 : algebraMap B.host.E (HeightOneSpectrum.adicCompletion B.host.E P.1)
        ((((θ P)⁻¹ : ↥(GLint B.fields.E n P.1)).1) (Pi.single j 1) r) =
        algebraMap B.host.E _ ((Pi.single j (1 : B.host.E) : Fin n → B.host.E) r) := by
      rw [← h1, Pi.single_apply]; split_ifs <;> simp
    have h3 := (algebraMap B.host.E (HeightOneSpectrum.adicCompletion B.host.E P.1)).injective h2
    simpa [Pi.basisFun_apply] using h3
  · rintro rfl
    intro P r j
    rw [key P r j]
    simp [Pi.single_apply]

end GlobalTheory.Mem.Col2.TC.ChTw.Match
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localConditions_conj_unitary_keepsStdLattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (n : ℕ) (t s : GA B n)
    (x : ∀ w : (B.primes X).vGs, GL (Fin n) (𝓞 B.fields.E ⧸ w.1.asIdeal)) (h : GLG (E := B.fields.E) (n := n) (SG := (B.primes X).vGs)),
    (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf t p ∧ p.deco.1.N = stdLat B.fields.E n) →
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∈ v.asIdeal → bc (prV (E := B.host.E) v) t = 1) →
    (∀ (w : (B.primes X).vGs) (r j : Fin n), HasRes w.1 (adAt B.host.F w.1 ((t : Matrix (Fin n) (Fin n) _) r j)) ((x w).1 r j)) →
    (LocalCondMoveDecoratedLattice u n (t⁻¹ * s * t) h ↔ LocalCondMoveDecoratedLattice u n s (fun w => x w * h w * (x w)⁻¹)) := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.conj_unitary_preserves_stdLat_of_ptOf | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.conj_unitary_preserves_stdLat_of_ptOf | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.conj_unitary_preserves_stdLat_of_ptOf <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChTwRead

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

def noFr (p : DecoF E n ST SG Q) : DecoF E n ST SG ∅ :=
  ⟨(p.deco, fun P => absurd P.2 (Finset.notMem_empty _)), fun P => absurd P.2 (Finset.notMem_empty _)⟩

theorem isPtOf_iff (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) :
    IsPtOf hc g p ↔ (g ∈ UAd hc n ∧ p.deco.1 = decoRaw ST SG g) ∧
      ∀ (P : Q) (i j : Fin n), adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        algebraMap E _ (p.fr P (Pi.single j 1) i) := by
  have key := PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ g (noFr p) rfl
  constructor
  · intro h
    exact ⟨key.1 ⟨h.uni, h.lat, h.f, h.be, fun P => absurd P.2 (Finset.notMem_empty _)⟩, h.fr⟩
  · rintro ⟨h, h'⟩
    have h2 := key.2 h
    exact ⟨h2.uni, h2.lat, h2.f, h2.be, h'⟩

theorem adAt_congr_prV (P : HeightOneSpectrum (𝓞 E)) {z z' : AfE F E}
    (h : prV (E := E) (P.under (𝓞 F)) z = prV (E := E) (P.under (𝓞 F)) z') : adAt F P z = adAt F P z' := by
  have h0 := TilX.adAt_eq_zero_of_prV P (z - z') (by rw [map_sub, h, sub_self])
  rwa [map_sub, sub_eq_zero] at h0

theorem exists_pt_of_agree {g₁ g' : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h₁ : IsPtOf hc g₁ p)
    (hg' : g' ∈ UAd hc n)
    (hv : ∀ P ∈ Q, bc (prV (E := E) (P.under (𝓞 F))) g' = bc (prV (E := E) (P.under (𝓞 F))) g₁) :
    ∃ q : DecoF E n ST SG Q, IsPtOf hc g' q := by
  obtain ⟨⟨-, hd1⟩, -⟩ := (isPtOf_iff hc g₁ p).1 h₁
  have hloc : ∀ P ∈ Q, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat g' (stdLat E n)) =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal p.deco.1.N := by
    intro P hP
    rw [hd1]
    exact updn_mem_loc (v := P.under (𝓞 F)) (P := P) rfl (hv P hP)
  refine ⟨⟨(⟨decoRaw ST SG g', decorated_lattice_exists hc n ST SG g' hg'⟩, p.fr), fun P x => ?_⟩, ?_⟩
  · show p.fr P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat g' (stdLat E n)) ↔ _
    rw [hloc P.1 P.2]
    exact p.2 P x
  · refine (isPtOf_iff hc g' _).2 ⟨⟨hg', rfl⟩, fun P i j => ?_⟩
    show _ = algebraMap E _ (p.fr P (Pi.single j 1) i)
    rw [← h₁.fr P i j]
    apply adAt_congr_prV
    exact congrArg (fun g => g.1 i j) (hv P.1 P.2)

theorem isPtOf_mul {g g₁ s : GL (Fin n) (AfE F E)} {p q : DecoF E n ST SG Q} (h : GLG (E := E) (n := n) (SG := SG))
    (hq : q.deco.1 = p.deco.1.act 1 h) (hg : IsPtOf hc g p) (hg₁ : IsPtOf hc g₁ p) (hs : IsPtOf hc (g₁ * s) q) :
    IsPtOf hc (g * s) q := by
  obtain ⟨⟨hgu, hdg⟩, hfg⟩ := (isPtOf_iff hc g p).1 hg
  obtain ⟨⟨hu1, hd1⟩, hf1⟩ := (isPtOf_iff hc g₁ p).1 hg₁
  obtain ⟨⟨hsu, hds⟩, hfs⟩ := (isPtOf_iff hc (g₁ * s) q).1 hs
  have hsU : s ∈ UAd hc n := by
    have e : s = g₁⁻¹ * (g₁ * s) := by group
    rw [e]
    exact mul_mem (inv_mem hu1) hsu
  obtain ⟨hJ, -⟩ := mem_congruence_of_action hc ST SG hsu hu1 h (by rw [← hds, hq, hd1])
  have hK := mem_principal_of_same_decoration hc n ST SG hu1 hgu (hd1.symm.trans hdg)
  have hc' := K1_conj hc n ST SG ⟨_, hJ⟩ (a := ⟨g₁⁻¹ * g, principal_le_adelic_unitary hc n ST SG hK⟩)
    (Subgroup.mem_subgroupOf.2 hK)
  rw [Subgroup.mem_subgroupOf] at hc'
  have e : g * s = (g₁ * s) * ((((g₁ * s)⁻¹ * g₁) * (g₁⁻¹ * g)) * ((g₁ * s)⁻¹ * g₁)⁻¹) := by group
  have hdr : decoRaw ST SG (g * s) = decoRaw ST SG (g₁ * s) := by
    rw [e]
    exact decorated_lattice_mul_principal hc n ST SG _ hc'
  refine (isPtOf_iff hc (g * s) q).2 ⟨⟨mul_mem hgu hsU, hds.trans hdr.symm⟩, fun P i j => ?_⟩

  rw [← hfs P i j, Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_mul, hfg P i l, hf1 P i l]

end GlobalTheory.Mem.Col2.ChTwRead

namespace GlobalTheory.Mem.Col2.TC.ChTw

theorem locMv_of_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m → ∀ {Ch : Type} (chOf : (I.stp u a i).Cl → Ch) (Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U : Ch → Subgroup (GA B (B.R.N i))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a i).Cl → GA B (B.R.N i)) (st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k : Ch → GA B (B.R.N i)), I.Reads u a i chOf Lb U chi y st k → ∀ (c : (I.stp u a i).Cl) (x : GA B (B.R.N i)), x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) → (∀ v, I.UnderQ a v → bc (prV (E := B.host.E) v) x = 1) → x ∈ U (chOf c) → ∃ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((k (chOf c))⁻¹ * x * k (chOf c)) κ := by
  intro B X I hI _ u a i _ Ch chOf Lb U chi y st k hR c x hx hx1 hxU
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hp : PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  obtain ⟨pk, hpk, -⟩ := hR.k_std (chOf c)
  have hk : k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := hpk.uni
  have hg' : y c * x * k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := by
    have e : y c * x * k (chOf c) = y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) := by group
    rw [e]
    exact mul_mem hp.uni (mul_mem (mul_mem (inv_mem hk) hx) hk)
  have hv : ∀ P ∈ I.Q a, bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) (y c * x * k (chOf c)) =
      bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) (y c * k (chOf c)) := by
    intro P hP
    have h1 := hx1 (P.under (𝓞 B.host.F)) ⟨P, hP, rfl⟩
    simp only [map_mul, h1, mul_one]
  obtain ⟨q, hq⟩ := ChTwRead.exists_pt_of_agree B.sp.cm hp hg' hv
  obtain ⟨κ, hκ1, hκq, hκc⟩ := (hR.lev c x q hq).1 hxU
  refine ⟨κ, hκ1, hκc, fun g hg => ?_⟩
  have e : y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) = y c * x * k (chOf c) := by group
  have hγ : κ.1 = 1 := by
    have h1 : toGLm B.fields.E (B.R.N i) κ.1.1 = toGLm B.fields.E (B.R.N i) 1 := by
      rw [map_one]
      exact hκ1
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective h1)
  · refine ChTwRead.isPtOf_mul B.sp.cm κ.2.1.1 ?_ hg hp (by rw [e, hκq]; exact hq)
    show ((κ.1, (κ.2.1 : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs))) • ((I.stp u a i).rep c).1.1.deco).1 = _
    rw [hγ]
    rfl
end GlobalTheory.Mem.Col2.TC.ChTw
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.pairing_complexForms_const_on_row_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (F G : MtCx I a) (d d' : (rowS I a).D), (rowS I a).cls d = (rowS I a).cls d' → pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d)) (G.1 d) = pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d')) (G.1 d') := by
  first | exact @GlobalTheory.Mem.Df.pairB_conj_cls_eq | exact GlobalTheory.Mem.Df.pairB_conj_cls_eq | (intros; apply GlobalTheory.Mem.Df.pairB_conj_cls_eq <;> assumption)
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
open scoped Kronecker

namespace GlobalTheory.FlagFibre

theorem vecOf_mul_toMat_mul {p q : ℕ} (R : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ)
    (v : Fin p × Fin q → ℂ) : Formalism.MJ.vecOf (R * toMat v * T) = Matrix.toLin' (R ⊗ₖ Tᵀ) v := by
  funext ⟨a, b⟩
  simp only [Formalism.MJ.vecOf, Matrix.toLin'_apply, mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mul_apply,
    kroneckerMap_apply, transpose_apply, toMat, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem lintegral_affine :
    ∀ (p q : ℕ) (R : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin p) (Fin q) ℂ), IsUnit R.det → IsUnit T.det → ∀ f : (Fin p × Fin q → ℂ) → ℝ≥0∞, Measurable f → ∫⁻ v : Fin p × Fin q → ℂ, f (vecOf (R * toMat v * T + C)) = ENNReal.ofReal ((Complex.normSq R.det ^ q * Complex.normSq T.det ^ p)⁻¹) * ∫⁻ v, f v := by
  intro p q R T C hR hT f hf
  set Lr : (Fin p × Fin q → ℂ) →ₗ[ℝ] (Fin p × Fin q → ℂ) := (Matrix.toLin' (R ⊗ₖ Tᵀ)).restrictScalars ℝ with hLr
  have hdet : LinearMap.det Lr = Complex.normSq R.det ^ q * Complex.normSq T.det ^ p := by
    rw [hLr, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.det_toLin', det_kronecker,
      det_transpose]
    simp
  have hpos : 0 < Complex.normSq R.det ^ q * Complex.normSq T.det ^ p :=
    mul_pos (pow_pos (Complex.normSq_pos.2 hR.ne_zero) _) (pow_pos (Complex.normSq_pos.2 hT.ne_zero) _)
  have hdet0 : LinearMap.det Lr ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hLm : Measurable Lr := (LinearMap.continuous_of_finiteDimensional Lr).measurable
  have hg : Measurable fun w : Fin p × Fin q → ℂ => f (w + Formalism.MJ.vecOf C) := hf.comp (measurable_add_const _)
  have e1 : ∫⁻ v : Fin p × Fin q → ℂ, f (Formalism.MJ.vecOf (R * toMat v * T + C)) =
      ∫⁻ w, f (w + Formalism.MJ.vecOf C) ∂(Measure.map Lr volume) := by
    rw [lintegral_map hg hLm]
    refine lintegral_congr fun v => ?_
    have : Formalism.MJ.vecOf (R * toMat v * T + C) = Formalism.MJ.vecOf (R * toMat v * T) + Formalism.MJ.vecOf C := rfl
    rw [this, vecOf_mul_toMat_mul]; rfl
  refine e1.trans ?_
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet0, lintegral_smul_measure, hdet,
    abs_of_nonneg (inv_nonneg.2 hpos.le), smul_eq_mul, lintegral_add_right_eq_self]

end GlobalTheory.FlagFibre
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

theorem lminor_block : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ H : Matrix (Fin r) (Fin r) ℂ, IsUnit (reindex e e H).toBlocks₂₂.det → (∀ (i : Fin (r + 1)) (k : Fin (q + 1)), (i : ℕ) = k → lminor H i = lminor (reindex e e H).toBlocks₂₂ k) ∧ ∀ (i : Fin (r + 1)) (k : Fin (p + 1)), (i : ℕ) = q + k → lminor H i = (reindex e e H).toBlocks₂₂.det * lminor (schur (reindex e e H)) k := by
  intro r p q e he H hH
  constructor
  · rintro ⟨i, hi⟩ ⟨k, hk⟩ h
    obtain rfl : i = k := h
    unfold lminor
    congr 1
    ext a b
    simp only [submatrix_apply, toBlocks₂₂, reindex_apply, of_apply]
    congr 1 <;> exact Fin.ext (by rw [he.2]; rfl)
  · rintro ⟨i, hi⟩ ⟨k, hk⟩ h
    obtain rfl : i = q + k := h
    obtain ⟨f0, hf0⟩ := exists_isBlockOrderedSumEquiv k q
    let f : Fin (q + k) ≃ Fin k ⊕ Fin q := (finCongr (add_comm q k)).trans f0
    have hf : IsBlockSL2Embedding f := ⟨fun a => hf0.1 a, fun a => hf0.2 a⟩
    let c : Fin k → Fin p := Fin.castLE (Nat.le_of_lt_succ hk)
    let G : Matrix (Fin k ⊕ Fin q) (Fin k ⊕ Fin q) ℂ := (reindex e e H).submatrix (Sum.map c id) (Sum.map c id)
    have key : ∀ a, Fin.castLE (Nat.le_of_lt_succ hi) (f.symm a) = e.symm (Sum.map c id a) := by
      rintro (a | a) <;> apply Fin.ext
      · simp only [Fin.val_castLE, Sum.map_inl, hf.1, he.1, c]
      · simp only [Fin.val_castLE, Sum.map_inr, hf.2, he.2, id]
    have h1 : lminor H ⟨q + k, hi⟩ = G.det := by
      unfold lminor
      rw [← det_submatrix_equiv_self f.symm]
      congr 1
      ext a b
      simp only [G, submatrix_apply, reindex_apply, ← key]
    have h2 : G.toBlocks₂₂ = (reindex e e H).toBlocks₂₂ := rfl
    rw [h1, det_eq_mul_schur (h2 ▸ hH), h2]
    rfl

end GlobalTheory.FlagFibre
end
