module

public import Formalism.LocalToGlobal.GlobalTheory.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage
public import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement Formalism.HN Formalism.L2.GlobalTheoryTheory.DivPassage

theorem levelAmb_transfer
    {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {D0 D1 : ℕ}
    (A : LevelAmb K D0 D1) {G : Type} [Group G] [Fintype G] {T : A.S → Type}
    [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)] [∀ s, FiniteDimensional K (T s)]
    (τ : ∀ s, Representation K G (T s)) (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G)
    (χ : H →* (𝓞 K)ˣ) (ρ : Representation K G (Fin A.Dg → K))
    (hτ : IsGood τ) (hM : M1 τ H₀ χ₀)
    (h0 : A.ep0.mulVecLin = epP H₀ χ₀ ρ) (h1 : A.ep1.mulVecLin = epP H χ ρ)
    (hs : ∀ s, (A.es s).mulVecLin = eS (τ s) ρ) (hn : ∀ s, A.nS s = nS (τ s) H χ)
    (hG : A.G = Fintype.card G) (hgood : eGood τ ρ = LinearMap.id)
    (hX : A.FramesG) (hL : Submodule.IsFullLattice K A.Rg) (hst : ∀ g : G, ∀ a ∈ A.Rg, ρ g a ∈ A.Rg)
    (hU : IsUnitaryRep (Pi.basisFun K (Fin A.Dg)) A.Xg ρ) :
    A.Ranks ∧ A.Deg0 ∧ A.Deg1 ∧ (A.latticeAtSharpLevel ≠ ⊥ → A.MaxT) := by
  have h15 := all_parts_transfer_holds
  have hlat : IsGLat ρ A.Rg := by
    have : Submodule.IsFullLattice K A.Rg := hL
    exact ⟨Submodule.IsLattice.fg K A.Rg, Submodule.IsFullLattice.span_eq_top, hst⟩
  have p := h15 K G A.S T τ H₀ χ₀ H χ hτ hM _ _ (Pi.basisFun K (Fin A.Dg)) A.Xg ρ hX hU A.Rg hlat
  have q := h15 K G A.S T τ H₀ χ₀ H₀ χ₀ hτ hM _ _ (Pi.basisFun K (Fin A.Dg)) A.Xg ρ hX hU A.Rg hlat
  have e0 : A.latticeAtBaseLevel = cut A.Rg (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ) := by
    rw [hgood, LinearMap.comp_id, ← h0]; rfl
  have e1 : A.latticeAtSharpLevel = cut A.Rg (epP H χ ρ ∘ₗ eGood τ ρ) := by
    rw [hgood, LinearMap.comp_id, ← h1]; rfl
  have es : ∀ s, A.Rs s = cut A.Rg (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ) := fun s => by
    rw [← h0, ← hs, ← Matrix.mulVecLin_mul]; rfl
  unfold TransferLatticeConditions at p q
  dsimp only at p q
  simp only [← e0, ← e1, ← es, ← hn, ← hG] at p
  have hM' : ∀ s, nS (τ s) H₀ χ₀ = 1 := hM
  simp only [← e0, ← es, hM', one_mul] at q
  obtain ⟨⟨-, r1⟩, ⟨-, -, -, -, -, -, d0⟩, -, ⟨d1, -⟩, m⟩ := p
  have r0 := q.1.2
  have h85 : (8.5 : ℝ) = 17 / 2 := by norm_num
  rw [h85] at d1 m
  refine ⟨⟨r0, r1⟩, ?_, ?_, fun h => (m h).1⟩
  · unfold LevelAmb.Deg0
    rw [r0, Nat.cast_sum]
    exact sub_le_iff_le_add'.1 d0
  · unfold LevelAmb.Deg1
    rw [r1]
    have := (abs_le.1 d1).1
    exact sub_le_iff_le_add.2 (by
      have h2 := neg_le_sub_iff_le_add.1 this
      exact h2)

end Formalism.IndefR.LatticeTransfer
end
end

section

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx.GroupActionMatrices

section Inst3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty : Type}

theorem okOp_opAll {B : BlockDat K G Pl0} {D : InertDat3 B I0 Ty} {s : ℕ} (h : B.Ok s) (hD : D.Ok3) (hH : B.OkH)
    (hH3 : D.InertRationalAdjoint) : OkOp B D.opAll := by
  refine ⟨?_, ?_, hD.comm, InertDat3.splitOver_opAll D h hD, ?_⟩
  · intro i a b
    rcases i with p | k
    · exact hH.rat p a b
    · exact hH3.rat k a b
  · intro i
    rcases i with p | k
    · obtain ⟨p', hp'⟩ := hH.adj p
      exact ⟨Sum.inl p', hp'⟩
    · obtain ⟨k', hk'⟩ := hH3.adj k
      exact ⟨Sum.inr k', hk'⟩
  · intro i g
    rcases i with p | k
    · exact h.opG p g
    · exact hD.opG k g

end Inst3

section Main3

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3)

theorem proviso_of_lift_eigenvalues {s : ℕ} (hOk : A3.fam3.Ok3 s) (hH : ∀ j, (A3.A.fam.L j A3.A.fam.μ0).OkH ∧ (A3.liftI j A3.A.fam.μ0).InertRationalAdjoint)
    (P : Subgroup G) (ψ : P →* Kˣ) {C : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
    (hC : LiftsEig3 A3 X P ψ C) : (A3.side3 P ψ X.zs).Proviso := by
  intro j
  have hB := DefFam.blockHyp_lift A3.A.fam hOk.ok2 P ψ j A3.A.fam.μ0
  have hO : OkOp _ (A3.liftI j A3.A.fam.μ0).opAll :=
    okOp_opAll (hOk.ok2.lifts j A3.A.fam.μ0) (hOk.lifts j A3.A.fam.μ0) (hH j).1 (hH j).2
  have hr := eig_ratG hB hO (C j)
  rw [← hC j] at hr
  exact CyclotomicLifting.xq_rat hB hr

theorem types_of_lift_eigenvalues {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) (hst : X.zs.Stable) (P : Subgroup G)
    (ψ : P →* Kˣ) {C : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop} (hC : LiftsEig3 A3 X P ψ C)
    (hT : LiftsTyp3 A3 C) : (A3.side3 P ψ X.zs).Types := by
  intro j
  refine (A3.fam3.LI j A3.A.fam.μ0).inert_parts_span_top (ℓ := A3.A.fam.lvlA P ψ) (Z := X.Zl j A3.A.fam.μ0)
    hOk.ok2.conj (hOk.ok2.lifts j A3.A.fam.μ0) (hOk.lifts j A3.A.fam.μ0)
    hOk.ok2.irr ?_ (fun p : A3.fam3.base3.Ix => A3.fam3.tr3 j p.1) ?_ ?_
  · intro i
    exact Submodule.map_le_iff_le_comap.1 (hst.2 j A3.A.fam.μ0 (Sum.inl i))
  · intro p q hpq
    exact hsep p.1 p.2 q.1 q.2 (fun h => hpq (Subtype.ext h)) j
  · refine (hC j).le.trans ?_
    apply BlockDat.good_part_coordinates_mono
    refine Col.eigSum_mono fun x hx => ?_
    obtain ⟨p, hp, hx'⟩ := hT j x hx
    exact ⟨⟨p, hp⟩, hx'⟩

theorem majAt_eq_zero_of_mem_Qp_of_ne {s : ℕ} (hOk : A3.fam3.Ok3 s) (hH : (A3.A.fam.R A3.A.fam.μ0).OkH ∧ (A3.rowI A3.A.fam.μ0).InertRationalAdjoint)
    (hst : X.zs.Stable) (P : Subgroup G) (ψ : P →* Kˣ) (v : InfinitePlace K) (p q : A3.fam3.base3.Ix) (hpq : p ≠ q)
    (x : Fin ((A3.side3 P ψ X.zs).dQ A3.A.fam.μ0) → K) (hx : x ∈ (A3.side3 P ψ X.zs).Qp A3.A.fam.μ0 p)
    (y : Fin ((A3.side3 P ψ X.zs).dQ A3.A.fam.μ0) → K) (hy : y ∈ (A3.side3 P ψ X.zs).Qp A3.A.fam.μ0 q) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((A3.side3 P ψ X.zs).XQ A3.A.fam.μ0) v x y = 0 := by
  have hB : BlockHyp (A3.A.fam.R A3.A.fam.μ0) (A3.A.fam.lvl P ψ) A3.A.fam.v0 s :=
    ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ A3.A.fam.μ0⟩
  have hO : OkOp (A3.A.fam.R A3.A.fam.μ0) (A3.fam3.RI A3.A.fam.μ0).opAll :=
    okOp_opAll (hOk.ok2.what₂ A3.A.fam.μ0) (hOk.what₂ A3.A.fam.μ0) hH.1 hH.2
  refine part_orthg hB hO (fun i => Submodule.map_le_iff_le_comap.1 (hst.1 A3.A.fam.μ0 (Sum.inl i))) v
    (C := (A3.fam3.RI A3.A.fam.μ0).HasRes3 p.1) (C' := (A3.fam3.RI A3.A.fam.μ0).HasRes3 q.1) ?_ hx hy
  intro z hz
  exact (A3.fam3.RI A3.A.fam.μ0).excl3
    ((A3.fam3.RI A3.A.fam.μ0).diffAt_of_mem_ixFin3 q.2 p.2 (fun h => hpq (Subtype.ext h).symm)) z hz

end Main3

end Formalism.IndefR.Cx
end
end

section

open NumberField

noncomputable section

namespace Formalism.IndefR.Bridge

open Formalism.L2

section ColPts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Formalism.L2.DIV.Pl E))
  (H : Subgroup (Col.GLG (E := E) (n := n) (SG := SG)))

def colJ : Subgroup (Col.UAd hc n) := (Col.JH hc n ST SG H).map (Col.ToUnitaryAdelic hc n ST)

abbrev principalCongruenceSubgroup : Subgroup (Col.UAd hc n) := (Col.K1 hc n ST SG).subgroupOf (Col.UAd hc n)

theorem J0toU_injective : Function.Injective (Col.ToUnitaryAdelic hc n ST) := Subgroup.inclusion_injective _

def colJEquiv : Col.JH hc n ST SG H ≃* colJ hc n ST SG H :=
  (Col.JH hc n ST SG H).equivMapOfInjective _ (J0toU_injective hc n ST)

theorem colJEquiv_symm_coe (k : colJ hc n ST SG H) :
    Col.ToUnitaryAdelic hc n ST (((colJEquiv hc n ST SG H).symm k : Col.JH hc n ST SG H) : Col.J0 hc n ST) = (k : Col.UAd hc n) := by
  rw [← Subgroup.coe_equivMapOfInjective_apply (Col.JH hc n ST SG H) (Col.ToUnitaryAdelic hc n ST) (J0toU_injective hc n ST)]
  exact congrArg Subtype.val ((colJEquiv hc n ST SG H).apply_symm_apply k)

theorem mem_principal_congruence_iff (m : Col.J0 hc n ST) : Col.ToUnitaryAdelic hc n ST m ∈ principalCongruenceSubgroup hc n ST SG ↔ Col.redG hc n ST SG m = 1 := by
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := Subgroup.mem_subgroupOf.1 h
    have e : m' = m := Subtype.ext he
    rw [← e]
    exact MonoidHom.mem_ker.1 hm'
  · intro h
    exact Col.mem_principal_congruence_of hc n ST SG h

theorem principal_congruence_le_level_subgroup : principalCongruenceSubgroup hc n ST SG ≤ colJ hc n ST SG H := by
  intro a ha
  obtain ⟨m, hm, hma⟩ := Subgroup.mem_subgroupOf.1 ha
  refine Subgroup.mem_map.2 ⟨m, Subgroup.mem_comap.2 ?_, Subtype.ext hma⟩
  rw [MonoidHom.mem_ker.1 hm]
  exact H.one_mem

def colToAdG : Col.URat hc n × colJ hc n ST SG H →* Col.AdG hc n ST SG H :=
  show Col.URat hc n × colJ hc n ST SG H →* Col.URat hc n × (Col.JH hc n ST SG H ⧸ (Col.redH hc n ST SG H).ker) from
    MonoidHom.prodMap (MonoidHom.id _)
      ((QuotientGroup.mk' (Col.redH hc n ST SG H).ker).comp (colJEquiv hc n ST SG H).symm.toMonoidHom)

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Col.GSD K}

variable {hc n ST SG H}

def colGl (o : Col.OnDeco n ST SG H S) : Col.URat hc n × colJ hc n ST SG H →* S.G :=
  o.eG.toMonoidHom.comp ((Col.adHom hc n ST SG H).comp (colToAdG hc n ST SG H))

def colQ (o : Col.OnDeco n ST SG H S) (x : Col.UAd hc n) : S.D :=
  o.eD (Col.decoPt hc n ST SG (QuotientGroup.mk x : Col.adPt hc n ST SG))

variable (o : Col.OnDeco n ST SG H S)

theorem colGl_apply (γ : Col.URat hc n) (k : colJ hc n ST SG H) :
    colGl o (γ, k) = o.eG (Col.ratHom hc n γ, Col.redH hc n ST SG H ((colJEquiv hc n ST SG H).symm k)) := rfl

theorem colGl_surj (hR : Col.RedHSurj hc n ST SG H) : Function.Surjective (colGl (hc := hc) o) := by
  intro g
  obtain ⟨⟨u, h⟩, rfl⟩ := o.eG.surjective g
  obtain ⟨γ, hγ⟩ := (Col.ratHom_bijective hc n).2 u
  obtain ⟨k, hk⟩ := hR h
  refine ⟨(γ, colJEquiv hc n ST SG H k), ?_⟩
  rw [colGl_apply, MulEquiv.symm_apply_apply, hγ, hk]

theorem colGl_ker (γ : Col.URat hc n) (k : colJ hc n ST SG H) :
    colGl o (γ, k) = 1 ↔ γ = 1 ∧ (k : Col.UAd hc n) ∈ principalCongruenceSubgroup hc n ST SG := by
  rw [colGl_apply, MulEquiv.map_eq_one_iff, Prod.mk_eq_one,
    (injective_iff_map_eq_one' _).1 (Col.ratHom_bijective hc n).1, ← colJEquiv_symm_coe, mem_principal_congruence_iff]
  exact and_congr Iff.rfl Subtype.ext_iff

theorem colQ_surj (hS : Col.DecoPtSurj hc n ST SG) : Function.Surjective (colQ (hc := hc) o) := by
  intro d
  obtain ⟨d', rfl⟩ := o.eD.surjective d
  obtain ⟨p, rfl⟩ := hS d'
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
  exact ⟨x, rfl⟩

theorem colQ_fib (x x' : Col.UAd hc n) :
    colQ o x = colQ o x' ↔ ∃ k1 ∈ principalCongruenceSubgroup hc n ST SG, x' = x * k1 := by
  unfold colQ
  rw [o.eD.injective.eq_iff, (Col.decoPt_injective' hc n ST SG).eq_iff, QuotientGroup.eq]
  constructor
  · intro h
    exact ⟨_, h, by rw [mul_inv_cancel_left]⟩
  · rintro ⟨k1, hk1, rfl⟩
    rwa [inv_mul_cancel_left]

theorem colQ_eqv (γ : Col.URat hc n) (k : colJ hc n ST SG H) (x : Col.UAd hc n) :
    colQ o (Col.ratIn hc n γ * x * (k : Col.UAd hc n)⁻¹) = colGl o (γ, k) • colQ o x := by
  have e1 : Col.ratIn hc n γ * x * (k : Col.UAd hc n)⁻¹ =
      Col.rawSm hc n ST γ (((colJEquiv hc n ST SG H).symm k : Col.JH hc n ST SG H) : Col.J0 hc n ST) x := by
    unfold Col.rawSm
    rw [colJEquiv_symm_coe]
  have e2 := Col.decorated_point_equivariant hc n ST SG H
    ((γ, (((colJEquiv hc n ST SG H).symm k : Col.JH hc n ST SG H) : Col.JH hc n ST SG H ⧸ (Col.redH hc n ST SG H).ker)) :
      Col.AdG hc n ST SG H) (QuotientGroup.mk x : Col.adPt hc n ST SG)
  unfold colQ
  rw [e1, Col.adSmul_mk] at *
  rw [e2, o.smul]
  rfl

def colAdPts (hS : Col.DecoPtSurj hc n ST SG) : AdPts S (Col.ratIn hc n) (colJ hc n ST SG H) where
  K1 := principalCongruenceSubgroup hc n ST SG
  principal_congruence_le := principal_congruence_le_level_subgroup hc n ST SG H
  q := colQ o
  gl := colGl o
  gl_surj := colGl_surj o (Col.redHSurj_of hc n ST SG H (Col.decorated_lattice_exists hc n ST SG) hS)
  gl_ker := colGl_ker o
  q_surj := colQ_surj o hS
  q_eqv := colQ_eqv o
  q_fib := colQ_fib o


def colClassPres (hS : Col.DecoPtSurj hc n ST SG) (h : S.Ok) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (σ : K →+* ℂ) (ρ : Col.URat hc n →* Module.End ℂ W) (χ : colJ hc n ST SG H →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x'))
    (hK1 : ∀ k : colJ hc n ST SG H, (k : Col.UAd hc n) ∈ principalCongruenceSubgroup hc n ST SG → χ k = 1)
    (hgl : ∀ (γ : Col.URat hc n) (k : colJ hc n ST SG H) (v : S.V),
      coef (S.ρ (colGl o (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v)) :
    ClassPres (Col.ratIn hc n) (S.toCSD h) σ ρ (colJ hc n ST SG H) χ :=
  classPresOf (colAdPts o hS) h σ ρ χ coef hli hspan hpair hK1 hgl

end ColPts

section Forms

variable {X : Col.Fields} (hc : Formalism.BasicNotions.CMData X.F X.E) {n : ℕ} [NeZero n]
  {ST SG : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 X.E))}

end Forms

end Formalism.IndefR.Bridge
end
end
