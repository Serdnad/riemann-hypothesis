module

public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.FinalW
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle020
public import Formalism.LocalToGlobal.Columns.Bundle015
public import Formalism.LocalToGlobal.Columns.Bundle018
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Formalism.LocalToGlobal.Columns.Bundle009
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV

section Tr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E)


include hc in
theorem gls_trace_mem (a : 𝓞 E) : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = a + cO E a := by
  obtain ⟨b0, hb0⟩ := rll_norm_mem hc a
  obtain ⟨b1, hb1⟩ := rll_norm_mem hc (a + 1)
  refine ⟨b1 - b0 - 1, ?_⟩
  rw [map_sub, map_sub, map_one, hb1, hb0, map_add (cO E), map_one]
  ring

end Tr

section Ex

variable {X : Fields} {Pr : Primes X} (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok)


end Ex

end Formalism.L2.Col
end
end

section

noncomputable section

namespace Formalism.L2.Col

open NumberField

theorem unimodGenusLocAll_holds : UnimodGenusLocAll := unimodular_genus_unique

theorem unimodGenusLoc_holds (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : UnimodGenusLoc E n :=
  unimodGenusLocAll_holds E n

theorem unimodGenus_holds {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] : UnimodGenus hc n :=
  (Formalism.L2.GenusGluing.Gen.unimodGenus_iff hc n).1 (unimodGenusLoc_holds E n)

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QOrb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

theorem qdf_at_rat (q : QLoc hc n Q Θ) (P : Q) (γ : GL (Fin n) E) : q.at P (bc (iA F E) γ) = bc (q.phi P) γ := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rfl

theorem qdf_at_mul (q : QLoc hc n Q Θ) (P : Q) (x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : q.at P (x * y) = q.at P x * q.at P y := by
  show bc _ (bc _ (x * y)) = _
  rw [map_mul, map_mul]

theorem qdf_at_inv (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : q.at P x⁻¹ = (q.at P x)⁻¹ := by
  show bc _ (bc _ x⁻¹) = _
  rw [map_inv, map_inv]

theorem qdf_levUQ_le (H : Subgroup (GLG (E := E) (n := n) (SG := SG))) (q : QLoc hc n Q Θ) : levUQ hc n ST SG Q H q ≤ levU hc n ST SG H := inf_le_left

theorem qdf_levUQ_at (H : Subgroup (GLG (E := E) (n := n) (SG := SG))) (q : QLoc hc n Q Θ) {κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : κ ∈ levUQ hc n ST SG Q H q) (P : Q) : q.at P κ ∈ q.U P :=
  (Subgroup.mem_iInf.1 h.2) P

theorem qdf_ratio_val (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n) (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    (qdRatio p p' γ hN P).1 = (p'.fr P)⁻¹ * γ * p.fr P := rfl

variable (H : Subgroup (GLG (E := E) (n := n) (SG := SG)))

theorem qdf_orbit_of_rel (q : QLoc hc n Q Θ) {x x' : UAd hc n} {p p' : DecoF E n ST SG Q}
    (hx : FrOver q x.1 p) (hx' : FrOver q x'.1 p') (γ : URat hc n) (κ : levUQ hc n ST SG Q H q)
    (e : (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
      (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) :
    ∃ a : UF E n × H × Θ.grp, a.1 = ratHom hc n γ ∧ a.2.1 = levRed hc n ST SG H ⟨_, qdf_levUQ_le H q κ.2⟩ ∧ p' = a • p := by
  have hκ : (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ levU hc n ST SG H := qdf_levUQ_le H q κ.2
  have hd : decoOf ST SG (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((ratHom hc n γ, levRed hc n ST SG H ⟨_, hκ⟩) : UF E n × H) • decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [e]; exact rlc_decoOf_sm hc n ST SG H γ ⟨_, hκ⟩ x
  rw [hx.1, hx'.1] at hd
  have hN : p'.deco.1.N = gmap (ratHom hc n γ).1 p.deco.1.N := by rw [hd]; rfl
  have hinj : ∀ a b : GL (Fin n) E, Formalism.UG.glEquiv a = Formalism.UG.glEquiv b → a = b := fun a b h =>
    Units.ext (Matrix.ext_of_mulVec_single fun j => by
      have := congrArg (fun g : Sp E n ≃ₗ[E] Sp E n => g (Pi.single j 1)) h
      simpa [Formalism.UG.glEquiv] using this)
  have hγ : toGLm E n (ratHom hc n γ).1 = (γ : GL (Fin n) E) :=
    hinj _ _ (by rw [glEquiv_toGLm]; rfl)
  have hθ : ∀ P : Q, qdRatio p p' (ratHom hc n γ).1 hN P ∈ (Θ P).H := by
    intro P
    rw [← q.U_rat P]
    have h1 := hx.2 P
    have h2 := hx'.2 P
    have h3 := qdf_levUQ_at H q κ.2 P
    have hx'P : q.at P (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        bc (q.phi P) (γ : GL (Fin n) E) * q.at P x * (q.at P κ)⁻¹ := by
      rw [e, qdf_at_mul, qdf_at_mul, qdf_at_inv, qdf_at_rat]
    have key : bc (q.phi P) (qGL n (qdRatio p p' (ratHom hc n γ).1 hN P).1) =
        ((bc (q.phi P) (qGL n (p'.fr P)))⁻¹ * q.at P x') * q.at P κ * ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x)⁻¹ := by
      rw [qdf_ratio_val]
      simp only [qGL, map_mul, map_inv]
      rw [hγ, hx'P]
      group
    rw [key]
    exact mul_mem (mul_mem h2 h3) (inv_mem h1)
  refine ⟨(ratHom hc n γ, levRed hc n ST SG H ⟨_, hκ⟩, ⟨fun P => qdRatio p p' (ratHom hc n γ).1 hN P,
    (Subgroup.mem_pi _).2 fun P _ => hθ P⟩), rfl, rfl, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hd
  · funext P
    show p'.fr P = (ratHom hc n γ).1 * p.fr P * ((qdRatio p p' (ratHom hc n γ).1 hN P)⁻¹).1
    rw [Subgroup.coe_inv, qdf_ratio_val]
    group

end QOrb

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG

section QSurj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}


def QIntGL {v : HeightOneSpectrum (𝓞 F)} (k : GL (Fin n) (v.adicCompletion F)) : Prop :=
  (∀ i j, ((k : Matrix (Fin n) (Fin n) _) i j) ∈ v.adicCompletionIntegers F) ∧
    (∀ i j, (((k⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j) ∈ v.adicCompletionIntegers F)


variable (ST SG) in
def FrLat (q : QLoc hc n Q Θ) : Prop :=
  ∀ (x : UAd hc n) (p : DecoF E n ST SG Q), decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = p.deco → ∀ P : Q,
    QIntGL ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x)

end QSurj

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : ColRec} {u : D.what₂.Word} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

theorem hx_Pv_max (v : (D.mem u).A.vT) : (A.Pv v).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)

def AtTSeen : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ (v : (D.mem u).A.vT) (x : 𝓞 D.host.E) (y : D.what₂.LL),
      D.what₂.embLL y = D.host.emb (D.eTau ((D.fm u).tauOf w v)).1 (x : D.host.E) →
      ((0 : WithTop ℤ) < D.what₂.places.val w y ↔
        x ∈ (if (D.fm u).seenP w then A.Pv v else Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (A.Pv v)))


variable (D u) in
def AtTDisc : Prop :=
  ∀ i, i ≤ D.R.m → ∀ c : (D.mem u).C.cls i,
    Nonempty ((CH.Ld D u i c ⧸ (D.clsLat u i c).comap (CH.Ld D u i c).subtype) ≃ₗ[𝓞 D.host.E]
      (𝓞 D.host.E ⧸ Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)}))



structure AtTMoves where

  upG : ∀ i v (c : (D.mem u).C.cls i), CH.Ld D u i c → CH.GX D i

  up_tie : ∀ i, i ≤ D.R.m → ∀ v c (y : CH.Ld D u i c), (D.fm u).fv i v c (hxPr A P i v c y) = 1 →
    haveI := (hx_Pv_max A v).isPrime
    Formalism.L2.Herm.SameOff (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (D.clsLat u i ((D.fm u).up i v c (hxPr A P i v c y)))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (D.clsLat u i ((D.fm u).up i v c (hxPr A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CH.Ld D u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (CH.Ld D u i ((D.fm u).up i v c (hxPr A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CH.Ld D u i c ⊔
          Submodule.span (𝓞 D.host.E) {((D.mem u).A.T : D.host.E)⁻¹ • (y : (D.sp.X i).V)}) ∧
      (∀ (z : CH.Ld D u i ((D.fm u).up i v c (hxPr A P i v c y)))
        (hz : ((D.mem u).A.T : D.host.E) • (upG i v c y).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = (D.fm u).fv i v c (hxPr A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).up i v c (hxPr A P i v c y)))
        (hz : (upG i v c y).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩))
  dnG : ∀ i v (c : (D.mem u).C.cls i), Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) → CH.GX D i

  dn_tie : ∀ i, i ≤ D.R.m → ∀ v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ≠ 0 →
    haveI := (hx_Pv_max A v).isPrime
    Formalism.L2.Herm.SameOff (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (dnG i v c g).1 (D.clsLat u i ((D.fm u).dn i v c g))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (dnG i v c g).1 (CH.Ld D u i ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (D.clsLat u i c) ∧
      (∀ (z : CH.Ld D u i ((D.fm u).dn i v c g)) (hz : (dnG i v c g).1 (z : (D.sp.X i).V) ∈ CH.Lk D u (A.Pv v) i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = g (hxPrk A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).dn i v c g)) (hz : (dnG i v c g).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩))
  dilG : ∀ i v, ((D.mem u).A.Fv v)ˣ → (D.mem u).C.cls i → CH.GX D i

  dil_tie : ∀ i, i ≤ D.R.m → ∀ v (a : ((D.mem u).A.Fv v)ˣ) c,
      Formalism.HermitianLatticesTheory.gmap (dilG i v a c).1 (D.clsLat u i ((D.fm u).dil i v a c)) = D.clsLat u i c ∧
      (∀ (z : CH.Ld D u i ((D.fm u).dil i v a c)) (hz : (dilG i v a c).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c (hxPr A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).dil i v a c)) (hz : (dilG i v a c).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩))



structure AtTXp where

  lattice₂ : (D.fm u).clsP → Submodule (𝓞 D.host.E) D.sp.X'.V

  levP : Formalism.L2.Herm.StepLevel0 D.sp.cm D.sp.X' D.host.g (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0)

  clsP : Formalism.L2.Herm.ClassTie D.sp.cm D.sp.X' (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) levP.U (D.fm u).stabilizer₂ lattice₂

  z0 : (D.sp.X D.R.m).V
  cocycle_zero_mem_invariants : z0 ∈ Submodule.span D.host.E {D.sp.z}
  hermitianForm_lastCoordinateUniformizerVector_self : (D.sp.X D.R.m).hT z0 z0 = ((D.mem u).A.T : D.host.E)
  tilG : (D.fm u).clsP → CH.GX D D.R.m

  til_tie : ∀ c : (D.fm u).clsP,
    Formalism.HermitianLatticesTheory.gmap (tilG c).1 (D.clsLat u D.R.m ((D.fm u).til c)) =
      (lattice₂ c).map (D.sp.iX'.restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0} ∧
    ∀ v (z : CH.Ld D u D.R.m ((D.fm u).til c)) (a : 𝓞 D.host.E),
      (a : D.host.E) = (D.sp.X D.R.m).hT z0 ((tilG c).1 (z : (D.sp.X D.R.m).V)) →
      (D.fm u).fv D.R.m v _ (hxPr A P D.R.m v _ z) = A.res v a



def atTOf (eF : ∀ v : (D.mem u).A.vT, (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (A.eV v).1.asIdeal))
    (hF : ∀ v (a : 𝓞 D.host.F), eF v (A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a)) = Ideal.Quotient.mk _ a)
    (hs : AtTSeen A) (hd : AtTDisc D u) (M : AtTMoves A P) (Xp : AtTXp A P) : CH.AtT D u A.eV eF where
  piU := A.piU
  piU_K := A.piU_K
  piU_norm := A.piU_norm
  piU_cong := A.piU_cong
  Pv := A.Pv
  Pv_max := hx_Pv_max A
  Pv_pi := A.res_pi
  Pv_over := fun v => Ideal.ext fun x => ((A.res_v v x).symm)
  res := A.res
  res_surj := A.res_surj
  res_ker := fun _ => rfl
  res_F := hF
  seen := hs
  disc := hd
  pr := hxPr A P
  pr_surj := hxPr_surj A P
  pr_smul := hxPr_smul A P
  pr_ker := hxPr_ker A P
  fv_ker := hx_fv_ker A P
  prk := hxPrk A P
  prk_surj := hxPrk_surj A P
  prk_smul := hxPrk_smul A P
  prk_ker := hxPrk_ker A P
  te_tie := hx_te A P
  upG := M.upG
  up_tie := M.up_tie
  dnG := M.dnG
  dn_tie := M.dn_tie
  dilG := M.dilG
  dil_tie := M.dil_tie
  lattice₂ := Xp.lattice₂
  levP := Xp.levP
  clsP := Xp.clsP
  z0 := Xp.z0
  cocycle_zero_mem_invariants := Xp.cocycle_zero_mem_invariants
  hermitianForm_lastCoordinateUniformizerVector_self := Xp.hermitianForm_lastCoordinateUniformizerVector_self
  tilG := Xp.tilG
  til_tie := Xp.til_tie

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM)

section Ker

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E)
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
  (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a))

theorem glk_val_lt (x : v.adicCompletionIntegers F) (h : IsLocalRing.residue (v.adicCompletionIntegers F) x = 0) :
    Valued.v (x : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
  have hle := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 x.2
  refine lt_of_le_of_ne hle fun h1 => h ?_
  have hx0 : (x : v.adicCompletion F) ≠ 0 := fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1
  let y : v.adicCompletionIntegers F := ⟨(x : v.adicCompletion F)⁻¹,
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 (by rw [map_inv₀, h1, inv_one])⟩
  have hxy : x * y = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
  exact ⟨⟨x, y, hxy, (mul_comm _ _).trans hxy⟩, rfl⟩

theorem gloRho_oToS (a : 𝓞 E) : gloRho v spl halg (oToS F E a) = IsLocalRing.residue (v.adicCompletionIntegers F)
    ⟨gloPhi v spl (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E a)), by
      have := gloPhi_int v spl halg _ (afsplit_prV_int v _ (oToS F E a).2)
      rwa [show ((oToS F E a : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
        inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E a) from rfl, afsplit_prV_inclE] at this⟩ := by
  rw [gloRho_apply]
  congr 1


include hc in
theorem glk_ker (w : Pl E) (hov : IsOver v w) (ϖ : 𝓞 E) (h2 : cO E ϖ ∉ w.asIdeal)
    (hval : Valued.v (gloPhi v spl (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E ϖ))) < 1) :
    ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0 := by
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h2 (by rw [map_zero]; exact zero_mem _)
  have hϖ : gloRho v spl halg (oToS F E ϖ) = 0 := by
    rw [gloRho_oToS]
    exact glo_res_zero v _ hval
  let Q : Pl E :=
    { asIdeal := RingHom.ker ((gloRho v spl halg).comp (oToS F E))
      isPrime := RingHom.ker_isPrime _
      ne_bot := fun hb => hϖ0 (by
        have : ϖ ∈ RingHom.ker ((gloRho v spl halg).comp (oToS F E)) := hϖ
        rwa [hb, Ideal.mem_bot] at this) }
  have hQ : IsOver v Q := by
    show v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
    ext r
    rw [Ideal.mem_comap]
    show r ∈ v.asIdeal ↔ gloRho v spl halg (oToS F E (algebraMap (𝓞 F) (𝓞 E) r)) = 0
    rw [gloRho_algMap]
    constructor
    · intro hr
      refine glo_res_zero v _ ?_
      show Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1
      rw [csApprox_val_int]
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).2 hr
    · intro hr
      have := glk_val_lt v _ hr
      change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 at this
      rw [csApprox_val_int] at this
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).1 this
  rcases rll_over_cases hc hov hQ with h | h
  · intro a ha
    have : a ∈ Q.asIdeal := by rw [h]; exact ha
    exact this
  · exfalso
    have : ϖ ∈ Q.asIdeal := hϖ
    rw [h, mem_conjP] at this
    exact h2 this

end Ker

section Pl

variable {X : Fields} {Pr : Primes X} (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok)

structure GSplit where
  sp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal →
    X.E ⊗[X.F] v.adicCompletion X.F ≃+* v.adicCompletion X.F × v.adicCompletion X.F
  sp_sig : ∀ i v h x, sp i v h (sigR hc.sig (v.adicCompletion X.F) x) = swapR _ (sp i v h x)
  sp_alg : ∀ i v h (a : v.adicCompletion X.F), sp i v h ((1 : X.E) ⊗ₜ[X.F] a) = (a, a)
  sp_pi : ∀ i v h, Valued.v (sp i v h (inclE (F := X.F) (v.adicCompletion X.F) (hc.sig (Pr.piG i : X.E)))).1 < 1


variable {hc}



end Pl

end Formalism.L2.Col
end
end
