module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotOntoOfCharAlone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

def grp (G : HTGroup p) (β : G.Cˣ) : Subgroup (G.Cˣ × ℚˣ) where
  carrier := {y | (y.1 : G.C) * β * sh G y.1 = algebraMap ℚ G.C y.2 * β ∧ 0 < (y.2 : ℚ)}
  one_mem' := ⟨by simp [sh], by simp⟩
  mul_mem' := by
    rintro ⟨y, s⟩ ⟨y', s'⟩ ⟨h2, hs⟩ ⟨h2', hs'⟩
    refine ⟨?_, ?_⟩
    · change (y : G.C) * β * sh G y = algebraMap ℚ G.C s * β at h2
      change (y' : G.C) * β * sh G y' = algebraMap ℚ G.C s' * β at h2'
      change ((y * y' : G.Cˣ) : G.C) * β * sh G ((y * y' : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s * s' : ℚˣ) : ℚ) * β
      have e : sh G ((y * y' : G.Cˣ) : G.C) = sh G y' * sh G y := by
        simp only [sh, Units.val_mul, map_mul, MulOpposite.unop_mul]
      rw [e, Units.val_mul, Units.val_mul, map_mul]
      calc (y : G.C) * y' * β * (sh G y' * sh G y) = y * (y' * β * sh G y') * sh G y := by
            simp only [mul_assoc]
        _ = algebraMap ℚ G.C s' * (y * β * sh G y) := by
            rw [h2']; simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
        _ = _ := by rw [h2, ← mul_assoc, ← map_mul, ← map_mul, mul_comm (s' : ℚ)]
    · change 0 < ((s * s' : ℚˣ) : ℚ)
      rw [Units.val_mul]; exact mul_pos hs hs'
  inv_mem' := by
    rintro ⟨y, s⟩ ⟨h2, hs⟩
    change (y : G.C) * β * sh G y = algebraMap ℚ G.C s * β at h2
    refine ⟨?_, ?_⟩
    · change ((y⁻¹ : G.Cˣ) : G.C) * β * sh G ((y⁻¹ : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * β
      have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        simp only [sh]
        rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
      have hs' : algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ G.C (s : ℚ) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      calc ((y⁻¹ : G.Cˣ) : G.C) * β * sh G ((y⁻¹ : G.Cˣ) : G.C)
          = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * (((y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C (s : ℚ) * β) *
              sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
            rw [← mul_assoc, ← mul_assoc, ← mul_assoc, Algebra.commutes ((s⁻¹ : ℚˣ) : ℚ), mul_assoc ((y⁻¹ : G.Cˣ) : G.C) _ (algebraMap ℚ G.C (s : ℚ)), hs', mul_one]
        _ = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * ((((y⁻¹ : G.Cˣ) : G.C) * y) * β *
              (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C))) := by
            rw [← h2]; simp only [mul_assoc]
        _ = _ := by rw [Units.inv_mul, e, one_mul, mul_one]
    · change 0 < ((s⁻¹ : ℚˣ) : ℚ)
      rw [Units.val_inv_eq_inv_val]; exact inv_pos.2 hs

def toAfF (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) :
    grp G β →* G.GAf :=
  MonoidHom.codRestrict
    ((((MulAut.conj x).toMonoidHom.comp (Units.map (inC G (AfP p)).toMonoidHom)).prodMap
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom)).comp (grp G β).subtype) _ fun y => by
      have h := congrArg (inC G (AfP p)) y.2.1
      rw [map_mul, map_mul, map_mul] at h
      have e1 : inC G (AfP p) (sh G y.1.1) = (starT G.star (AfP p) (inC G (AfP p) y.1.1)).unop :=
        (starT_tmul G.star (AfP p) 1 _).symm
      have e2 : inC G (AfP p) (algebraMap ℚ G.C y.1.2) =
          algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) y.1.2) := by
        rw [← IsScalarTower.algebraMap_apply]
        exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
      rw [e1, e2] at h
      exact conj_mul_star (starT G.star (AfP p)) (inC G (AfP p) β) x
        (Units.map (inC G (AfP p)).toMonoidHom y.1.1) t _ hx h

def toP1 (G : HTGroup p) (β : G.Cˣ) : grp G β →* Gr G 1 :=
  ((inclG G 1).comp (locC G)).comp (grp G β).subtype

def toV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : grp G β →* GL (Fin G.n) ℂ :=
  (Units.map (G.psi v).toMonoidHom).comp ((MonoidHom.fst _ _).comp (grp G β).subtype)

def herm (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : Matrix (Fin G.n) (Fin G.n) ℂ :=
  G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)

def PosV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : Type :=
  {x : Fin G.n → ℂ // 0 < (star x ⬝ᵥ (herm G v β *ᵥ x)).re}

abbrev Dat (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : Type := (G.GAf × Gr G 1) × PosV G v β

def Same (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a b : Dat G v β) : Prop :=
  ∃ (y : grp G β) (k : G.GAf × Gr G 1) (c : ℂ), k.1 ∈ Kf ∧ k.2 ∈ K' ∧ c ≠ 0 ∧
    b.1 = ((toAfF G β x t hx y, toP1 G β y) : G.GAf × Gr G 1) * a.1 * k ∧
    b.2.1 = c • ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1)

def Pts (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) : Type :=
  Quot (Same G v β x t hx Kf K')

def FixL (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : Fin G.n → ℂ) : Prop :=
  ∃ c : ℂ, (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z = c • z

def Stab (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a : Dat G v β) : Type :=
  {y : grp G β // a.1.1⁻¹ * toAfF G β x t hx y * a.1.1 ∈ Kf ∧ a.1.2⁻¹ * toP1 G β y * a.1.2 ∈ K' ∧
    FixL G v β y a.2.1}

def cxSumAt (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (β : G.Cˣ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  ∑ᶠ q : Pts G v β x t hx Kf K',
    ((Nat.card (Stab G v β x t hx Kf K' (Quot.out q)) : ℕ) : ℂ)⁻¹ *
      ∑ᶠ y : grp G β, if FixL G v β y (Quot.out q).2.1 then
        f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) *
          f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) *
          wt (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) else 0

structure Form (G : HTGroup p) where

  β : G.Cˣ
  sym : sh G β = β
  trivAf : ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ), Triv G (AfP p) β x t
  trivR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1

def Form.Rel {G : HTGroup p} (P Q : Form G) : Prop :=
  ∃ (y : G.Cˣ) (s : ℚ), 0 < s ∧ (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y)

def FCls (G : HTGroup p) : Type := Quot (Form.Rel (G := G))

def cxSum (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (P : Form G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  cxSumAt G v wt P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec Kf f K' f'

def cxTotal (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  ∑ᶠ q : FCls G, cxSum G v wt (Quot.out q) Kf f K' f'

def RegAf (G : HTGroup p) (g : G.GAf) : Prop :=
  ∃ w : AwayP p, ∀ a b : w.1.adicCompletion ℚ ⊗[ℚ] G.C,
    Commute a ((ubcMap (AfP.eval w) g).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) →
    Commute b ((ubcMap (AfP.eval w) g).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) → Commute a b

def Form.one (G : HTGroup p) : Form G := ⟨1, sh_one_eq G, ⟨1, 1, by simp [Triv, inC]⟩, ⟨1, by simp [Triv, inC]⟩⟩

theorem fixL_one (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (z : Fin G.n → ℂ) : FixL G v β 1 z :=
  ⟨1, by simp [toV]⟩

theorem same_refl (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a : Dat G v β) :
    Same G v β x t hx Kf K' a a :=
  ⟨1, 1, 1, Kf.one_mem, K'.one_mem, one_ne_zero, by simp, by simp [toV]⟩

def Stab.one (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a : Dat G v β) :
    Stab G v β x t hx Kf K' a :=
  ⟨1, by simpa using Kf.one_mem, by simpa using K'.one_mem, fixL_one G v β _⟩



theorem finitePlacesAway_nonempty (p : ℕ) [Fact p.Prime] : Nonempty (AwayP p) := by
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (p+1)
  have hq' : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hqp
  refine ⟨⟨⟨Ideal.span {(q:ℤ)}, (Ideal.span_singleton_prime hq'.ne_zero).2 hq', by simpa using hqp.ne_zero⟩, fun h => ?_⟩⟩
  have h1 : (q:ℤ) ∣ (p:ℤ) := Ideal.mem_span_singleton.1 (by
    have : (p:ℤ) ∈ Ideal.span {(p:ℤ)} := Ideal.mem_span_singleton_self _
    rw [← h] at this; exact this)
  have h2 : q ∣ p := Int.natCast_dvd_natCast.1 h1
  have := Nat.le_of_dvd (Fact.out : p.Prime).pos h2
  omega

theorem sigG_one (G : HTGroup p) (g : Gr G 1) : sigG G 1 g = g := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · show GlobalTheory.LKLoc.sig p (Q0 p) 1 1 g.1 = g.1
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact DFunLike.congr_fun (frobQ_degree_one p) ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p 1)) i j)
  · show sigRes p (G.Fw i) G.n 1 (g.2 i) = g.2 i
    rw [sigRes_degree_one]; rfl


end GlobalTheory.LKCx
end
end

section

noncomputable section

open GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

def markedSumIrr (G : HTGroup p) (wt sel : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : Cls G, if Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol) then
    wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

end GlobalTheory.LKMid
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def ownAt (D : D7) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : ℕ := if plc v = D.host.pde then D.host.pde' else D.host.pde

structure TwoRuns (J : CoreJ D) (G : Type) : Type 1 where
  first : RunData J
  second : RunData J
  lev : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)

def TwoRuns.used {J : CoreJ D} (r : TwoRuns J G) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : RunData J :=
  if plc v = D.host.pde then r.second else r.first

section Rec

variable {L : SizeData₂ D} {Pm : ParameterChoice' D L}
variable {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

local instance runAlg' (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

structure RunsOk (fw : FWTie J R κ v₀) (r : TwoRuns J G) : Prop where
  laws : ∀ v, LawsFull (r.used v).full
  cover : ∀ v (i : Fin D.R.m), OneCover (r.used v).full.toTop ((i : ℕ) + 1)
  xiRat : ∀ v (i : Fin D.R.m), ∀ γ₀ ∈ GQ ((r.used v).full.V ((i : ℕ) + 1) (r.used v).full.σ₀),
    (r.used v).full.xi (Matrix.GeneralLinearGroup.det (finHom ((r.used v).full.V ((i : ℕ) + 1) (r.used v).full.σ₀) γ₀)) = 1
  run : ∀ v ∈ R.twPl, ∀ i : Fin D.R.m, RunPin (T := (r.used v).full) R i (κ i).n v (ownAt D v)
  level : ∀ v (i : Fin D.R.m), LevelPin (T := (r.used v).full) R i (r.lev i)
  action : ∀ v (i : Fin D.R.m), ActionPin (T := (r.used v).full) (R := R) (laws v).p fw i (r.lev i)
  half : J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal

@[reducible] def hostAlg (D : D7) : Algebra (𝓞 D.host.E) D.what₂.LL :=
  (D.embE.comp (algebraMap (𝓞 D.host.E) D.host.E)).toAlgebra

structure IsRec (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (F : Face D A) (fw : FWTie J R κ v₀) (r : TwoRuns J G)
    {c : OnConst} (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c) : Prop where
  ok : RunsOk fw r
  kap : ∀ i : Fin D.R.m, κ i = kaR Tp hK ((i : ℕ) + 1)
  tied : ∃ (hc : LawsCore J.toCore) (hinj : Function.Injective D.what₂.OtoLL),
    OnObjLevelCompatibility F fw hc r.used (fun v => (ok.laws v).p) hinj EX (ownAt D) (fun _ i => lR Tp hK ((i : ℕ) + 1))
      (fun _ i => fR Tp hK ((i : ℕ) + 1)) Tp.TO r.lev (fun _ => 1) (mirIncl R) O
  depth : ∃ st : StarRing (𝓞 D.host.E), letI := st; letI := hostAlg D
    GlobalTheory.RunDepth.RunTie J.toCore EX Tp hK O fun j : Fin D.R.m => (j : ℕ) + 1
  DF_eq : O.DF = ((Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (lR Tp hK ((j : ℕ) + 1)) : ℕ) : ℝ)
  rr_eq : O.rr = (D.R.r : ℝ)
  Nc_eq : O.Nc = L.Nc
  realisedChain_torus_eq : O.T2 = D.host.T2.card
  pde_eq : O.pde = D.host.pde

end Rec

section Leaves

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

def HasIndexBound (O : OnObj S P c) : Prop :=
  ∃ Th1 a r1 r2 de2, LatticeIndexBoundAtPairs ({ O with Th1 := Th1, a := a, r1 := r1, r2 := r2, de2 := de2 } : OnObj S P c)

def HasTwistBound (O : OnObj S P c) : Prop := ∃ ε, LeafTW1 ({ O with ε0 := ε } : OnObj S P c)

def HasExpBound (N : IndefNum Bs) (O : OnObj S P c) : Prop :=
  (∀ w ∈ S.Tw, ∀ j, 0 ≤ N.J0 (S.μ w) w j) ∧
    ∃ Jp, LeafJSum ({ O with Jp := Jp } : OnObj S P c) ∧ LeafJExp N ({ O with Jp := Jp } : OnObj S P c)

end Leaves

section Low

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def BaseLinks (R : RealDat D A Ks) (F : Face D A) : Prop :=
  (R.toCx F).H5 F.cr false ∧ (R.toCx F).RATth F.cr false ∧ (lv (F.fc (R.toCx F).zs) false).Proviso

def lowB (D : D7) (i : Fin D.R.m) (b : ℝ) : ℝ :=
  GlobalTheory.LiftLower.hookPlus D i - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D b

def LowTop (R : RealDat D A Ks) (b : ℝ) : Prop :=
  ∀ (i : Fin D.R.m) (l : ℝ) (x : (R.HW i (sg0 D A)).H), x ≠ 0 → 0 < l →
    R.thG i A.μ0 (LinearMap.adjoint (R.thG i A.μ0) x) = (l : ℂ) • x → lowB D i b ≤ Real.log l

def LowForm (R : RealDat D A Ks) (F : Face D A) (b : ℝ) : Prop :=
  ∀ (i : Fin D.R.m) (v : InfinitePlace D.what₂.LL), v ≠ A.v0 →
    ∀ x : Fin ((lv (F.fc (R.toCx F).zs) false).dZ i A.μ0) → D.what₂.LL,
      Real.exp (lowB D i b) * (Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx F).zs) false).XT i A.μ0) v x x).re ≤
        ‖(R.toCx F).wC false i v (cpt v.embedding (((R.toCx F).liftMat F.cr false i A.μ0).mulVec x))‖ ^ 2

def reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) : RealDat D A Ks := { R with lam := lam, kap := kap }

end Low

end GlobalTheory.BigOn

end
end
