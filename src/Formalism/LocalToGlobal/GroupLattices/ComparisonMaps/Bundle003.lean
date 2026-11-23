module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValRat
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

theorem castGL_symm_bc {a b : ℕ} (h : a = b) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin b) R) :
    (castGL h S).symm (bc f g) = bc f ((castGL h R).symm g) := by
  subst h; rfl

theorem bc_comp {m : ℕ} {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (f : R →+* S) (g : S →+* U) (x : GL (Fin m) R) :
    bc g (bc f x) = bc (g.comp f) x := by
  apply Units.ext; ext i j; rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ} {G : GAtP p}

def tPos (σ : E →ₐ[F] E) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (v : Fin G.P.nV) (s : Fin (G.P.n' v)) : E →+* LL :=
  if Even s.val then tE (pos ⟨v, s⟩) else (tE (pos ⟨v, s⟩)).comp (σ : E →+* E)

theorem tPos_apply (σ : E →ₐ[F] E) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (x : E) :
    tPos σ tE pos v s x = tE (pos ⟨v, s⟩) (if Even s.val then x else σ x) := by
  unfold tPos
  split_ifs <;> rfl

def blkLL (A : LocAt F E n G) (σ : E →ₐ[F] E) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (γ : GL (Fin n) E) (v : Fin G.P.nV) (s : Fin (G.P.n' v)) : GL (Fin (G.P.m + 1)) LL :=
  bc (tPos σ tE pos v s) ((castGL A.rk E).symm (A.B⁻¹ * γ * A.B))

theorem gPos_act (A : LocAt F E n G) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (e : LL →+* G.Kf) (hA : A.ActB)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (i : G.comp) (γ : (G.lev i).Γ) (v : Fin G.P.nV) (s : Fin (G.P.n' v)) :
    gPosGL G.P v s ((G.lev i).act v γ) = Matrix.GeneralLinearGroup.map e (blkLL A σ tE pos (A.gamI i γ) v s) := by
  have h1 : (G.lev i).act v γ = bc (A.iw v) ((castGL A.rk E).symm (A.B⁻¹ * A.gamI i γ * A.B)) := by
    rw [← castGL_symm_bc, ← hA i v γ, MulEquiv.symm_apply_apply]
  rw [h1]
  apply Units.ext
  ext a b
  show G.P.ι v ((G.P.σ v ^ s.val) (A.iw v _)) = e (tPos σ tE pos v s _)
  rw [tPos_apply, hpos]

theorem actX_map (A : LocAt F E n G) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (e : LL →+* G.Kf) (hA : A.ActB)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (i : G.comp) (γ : (G.lev i).Γ) (Q : XR G.P LL) :
    (G.lev i).actX γ (MvPolynomial.map e Q) =
      MvPolynomial.map e (natActR G.P LL (blkLL A σ tE pos (A.gamI i γ)) Q) := by
  unfold Level.actX
  rw [natAct_eq, map_natActR]
  congr 2
  funext v s
  exact gPos_act A tE pos e hA hpos i γ v s

def atInfGL (emb : Tau → E →+* ℂ) (γ : GL (Fin n) E) : Tau → GL (Fin n) ℂ := fun τ => bc (emb τ) γ

theorem unit_of_std {J : Matrix (Fin n) (Fin n) E} (B γ : GL (Fin n) E) (hB : cT (σ : E →+* E) B.1 * J * B.1 = 1)
    (hγ : γ ∈ UJ (σ : E →+* E) J) : cT (σ : E →+* E) (B⁻¹ * γ * B).1 * (B⁻¹ * γ * B).1 = 1 := by
  have h1 : cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * cT (σ : E →+* E) B.1 = 1 := by
    rw [← cT_mul, ← Units.val_mul, mul_inv_cancel]
    exact cT_one _
  have hJ : J = cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * (B⁻¹ : GL (Fin n) E).1 := by
    calc J = (cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * cT (σ : E →+* E) B.1) * J * (B.1 * (B⁻¹ : GL (Fin n) E).1) := by
          rw [h1, ← Units.val_mul, mul_inv_cancel]
          simp
      _ = cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * (cT (σ : E →+* E) B.1 * J * B.1) * (B⁻¹ : GL (Fin n) E).1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hB, Matrix.mul_one]
  have hγ' : cT (σ : E →+* E) γ.1 * J * γ.1 = J := hγ
  simp only [Units.val_mul, cT_mul]
  calc _ = cT (σ : E →+* E) B.1 * (cT (σ : E →+* E) γ.1 *
        (cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * (B⁻¹ : GL (Fin n) E).1) * γ.1) * B.1 := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [← hJ, hγ', hB]

theorem blk_hAt (A : LocAt F E n G) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (γ : GL (Fin n) E) (hU : cT (σ : E →+* E) (A.B⁻¹ * γ * A.B).1 * (A.B⁻¹ * γ * A.B).1 = 1)
    (v : Fin G.P.nV) (s : Fin (G.P.n' v)) :
    Matrix.GeneralLinearGroup.map embLL (blkLL A σ tE pos γ v s) =
      hAt G.P A.rk pos (atInfGL emb A.B⁻¹) (atInfGL emb γ) v s := by
  have hM : atInfGL emb A.B⁻¹ (pos ⟨v, s⟩) * atInfGL emb γ (pos ⟨v, s⟩) * (atInfGL emb A.B⁻¹ (pos ⟨v, s⟩))⁻¹ =
      bc (emb (pos ⟨v, s⟩)) (A.B⁻¹ * γ * A.B) := by
    simp [atInfGL, map_mul, map_inv]
  unfold hAt
  rw [hM]
  apply Units.ext
  ext a b
  by_cases hs : Even s.val
  · simp only [hs, if_true]
    show embLL (tPos σ tE pos v s _) = emb (pos ⟨v, s⟩) _
    rw [tPos_apply, if_pos hs, htE]
    rfl
  · simp only [hs, if_false]
    have hinv : ((A.B⁻¹ * γ * A.B)⁻¹ : GL (Fin n) E).1 = cT (σ : E →+* E) (A.B⁻¹ * γ * A.B).1 := by
      rw [Matrix.coe_units_inv]
      exact Matrix.inv_eq_left_inv hU
    show embLL (tPos σ tE pos v s _) =
      ((reG G.P A.rk (bc (emb (pos ⟨v, s⟩)) (A.B⁻¹ * γ * A.B)))⁻¹ : GL (Fin (G.P.m + 1)) ℂ).1 b a
    rw [tPos_apply, if_neg hs, htE, ← map_inv, ← map_inv]
    show _ = emb (pos ⟨v, s⟩) (((A.B⁻¹ * γ * A.B)⁻¹ : GL (Fin n) E).1 _ _)
    rw [hinv]
    rfl

theorem evC_blk (A : LocAt F E n G) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (γ : GL (Fin n) E) (hU : cT (σ : E →+* E) (A.B⁻¹ * γ * A.B).1 * (A.B⁻¹ * γ * A.B).1 = 1)
    (Gm : Tau → Matrix (Fin n) (Fin n) ℂ)
    (z z' : Frames Gm) (hz : IsTr (atInf emb γ) z z') (Q : XR G.P LL) :
    evC G.P A.rk pos Gm (crdB emb A.B) (MvPolynomial.map embLL (natActR G.P LL (blkLL A σ tE pos γ) Q)) z' =
      evC G.P A.rk pos Gm (crdB emb A.B) (MvPolynomial.map embLL Q) z := by
  rw [map_natActR]
  have h1 : (fun v s => Matrix.GeneralLinearGroup.map embLL (blkLL A σ tE pos γ v s)) =
      hAt G.P A.rk pos (atInfGL emb A.B⁻¹) (atInfGL emb γ) := by
    funext v s
    exact blk_hAt A tE pos emb embLL htE γ hU v s
  rw [h1]
  exact evC_natAct G.P A.rk pos Gm (atInfGL emb A.B⁻¹) (atInfGL emb γ) z z' hz (MvPolynomial.map embLL Q)

end Formalism.L2.G.Cmp

end
end

section

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Classical
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}
  (S : StepLevel F E σ J T f bad) (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ)
  (G : GAtP p) (e : LL →+* G.Kf) (A : LocAt F E n G) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
  {V cls : Type} [AddCommGroup V] [Module LL V] (embV : V →ₛₗ[embLL] (cls → Frames (gramC J emb) → ℂ))
  (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))

def IsVal (x : V) (i : G.comp) (L : G.P.Tup) (Q : XR G.P LL) : Prop :=
  Q ∈ VtupR G.P LL ∧
  ∀ g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v),
    (∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
    ∀ (c : cls) (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1) →
    ∀ z z' : Frames (gramC J emb), IsTr (atInf emb γ) z' z →
    evC G.P A.rk pos (gramC J emb) (crdB emb A.B) (MvPolynomial.map embLL Q) z = (S.chi κ : ℂ) * embV x c z'

def valC (x : V) (i : G.comp) (L : G.P.Tup) : XR G.P LL :=
  if h : ∃ Q, IsVal S emb embLL G A pos embV yc x i L Q then Classical.choose h else 0

def cmpC (x : V) : G.Fn :=
  fun i L => if G.P.IsLatTup L then MvPolynomial.map e (valC S emb embLL G A pos embV yc x i L) else 0

def ValEx : Prop := ∀ x i L, G.P.IsLatTup L → ∃ Q, IsVal S emb embLL G A pos embV yc x i L Q

def ValUniq : Prop := ∀ x i L Q Q', G.P.IsLatTup L → IsVal S emb embLL G A pos embV yc x i L Q →
  IsVal S emb embLL G A pos embV yc x i L Q' → Q = Q'

variable {S emb embLL G e A pos embV yc}

theorem valC_spec (hex : ValEx S emb embLL G A pos embV yc) (x : V) (i : G.comp) (L : G.P.Tup) (hL : G.P.IsLatTup L) :
    IsVal S emb embLL G A pos embV yc x i L (valC S emb embLL G A pos embV yc x i L) := by
  unfold valC
  rw [dite_eq_left (hex x i L hL)]
  exact Classical.choose_spec (hex x i L hL)

theorem map_smul' {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (a : R) (Q : MvPolynomial ι R) :
    MvPolynomial.map f (a • Q) = f a • MvPolynomial.map f Q := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem IsVal.add {x y : V} {i : G.comp} {L : G.P.Tup} {Q Q' : XR G.P LL}
    (h : IsVal S emb embLL G A pos embV yc x i L Q) (h' : IsVal S emb embLL G A pos embV yc y i L Q') :
    IsVal S emb embLL G A pos embV yc (x + y) i L (Q + Q') := by
  refine ⟨Submodule.add_mem _ h.1 h'.1, fun g hg c γ hγ κ hp z z' hz => ?_⟩
  rw [map_add (f := _), map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, Pi.add_apply, h.2 g hg c γ hγ κ hp z z' hz,
    h'.2 g hg c γ hγ κ hp z z' hz, mul_add]

theorem IsVal.smul {x : V} {i : G.comp} {L : G.P.Tup} {Q : XR G.P LL} (a : LL)
    (h : IsVal S emb embLL G A pos embV yc x i L Q) : IsVal S emb embLL G A pos embV yc (a • x) i L (a • Q) := by
  refine ⟨Submodule.smul_mem _ a h.1, fun g hg c γ hγ κ hp z z' hz => ?_⟩
  rw [map_smul', map_smul, LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
    h.2 g hg c γ hγ κ hp z z' hz, smul_eq_mul, smul_eq_mul]
  ring

def cmpL (hex : ValEx S emb embLL G A pos embV yc) (hu : ValUniq S emb embLL G A pos embV yc) : V →ₛₗ[e] G.Fn where
  toFun := cmpC S emb embLL G e A pos embV yc
  map_add' x y := by
    funext i L
    show cmpC S emb embLL G e A pos embV yc (x + y) i L =
      cmpC S emb embLL G e A pos embV yc x i L + cmpC S emb embLL G e A pos embV yc y i L
    unfold cmpC
    by_cases hL : G.P.IsLatTup L
    · simp only [hL, if_true]
      rw [← map_add (f := _)]
      congr 1
      exact hu (x + y) i L _ _ hL (valC_spec hex _ i L hL) ((valC_spec hex x i L hL).add (valC_spec hex y i L hL))
    · simp [hL]
  map_smul' a x := by
    funext i L
    show cmpC S emb embLL G e A pos embV yc (a • x) i L = e a • cmpC S emb embLL G e A pos embV yc x i L
    unfold cmpC
    by_cases hL : G.P.IsLatTup L
    · simp only [hL, if_true]
      rw [← map_smul']
      congr 1
      exact hu (a • x) i L _ _ hL (valC_spec hex _ i L hL) ((valC_spec hex x i L hL).smul a)
    · simp [hL]

def cmpC_tie (tE : Tau → E →+* LL) (hex : ValEx S emb embLL G A pos embV yc)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (hchi : ∀ i (γ : (G.lev i).Γ) (κ : S.U), A.IsAway i γ κ.1 →
      ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ algebraMap G.O G.Kf ((G.lev i).χ γ : G.O) * e r = 1) :
    CmpTie S emb embLL tE G e A pos (fun x => embV x) yc (cmpC S emb embLL G e A pos embV yc) where
  pos_emb := hpos
  val := valC S emb embLL G A pos embV yc
  val_cmp := fun x i L hL => by unfold cmpC; rw [if_pos hL]
  val_emb := fun x i L g hg => (valC_spec hex x i L
    (fun v => ⟨(g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)),
      (Matrix.isUnit_iff_isUnit_det _).1 (g v).isUnit, hg v⟩)).2 g hg
  chi := hchi

end Formalism.L2.G.Cmp

end
end
