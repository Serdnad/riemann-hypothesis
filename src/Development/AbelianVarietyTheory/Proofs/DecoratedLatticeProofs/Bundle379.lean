module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle348
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle345
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle353
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle349
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSaw.StdMatch
open GlobalTheory.LocMod GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

section Gen
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem latO_le (S T : HSp D) (LS LT) {p q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, p v → q v) : latO S T LS LT p ≤ latO S T LS LT q :=
  AddSubgroup.closure_mono fun _ ⟨α, h1, h2, h3⟩ => ⟨α, h1, fun v hv => h2 v fun hp => hv (h v hp), h3⟩

theorem mem_latO_at (q : GlobalTheory.FinPl.SplitPt D k) {S T : HSp D} {LS LT} {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True)
    (hh : IsHalf q.e u) : u ∈ latO S T LS LT (· = q.v) := by
  obtain ⟨ε, ⟨β, rfl, h1, h0⟩, hsum⟩ := q.above
  have hβ : β ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have main : (latO S T LS LT fun _ => True) ≤ (latO S T LS LT (· = q.v)).comap
      (DistribSMul.toAddMonoidHom (WO S T) (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β))) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨β * α, fun v => by rw [map_mul]; exact mul_mem (hβ v) (hα v), fun v hv => ?_,
      a, ha, s, hs, t, ht, ?_⟩
    · rw [map_mul, h0 v hv, zero_mul]
    · ext i j
      change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Matrix.of_apply]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  have h := main hu
  rw [AddSubgroup.mem_comap] at h
  convert h using 1
  ext i j
  change _ = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) * u i j
  rw [← hsum, ← hh i j, ← mul_assoc, add_mul, q.split.1, mul_comm (cA D q.e), q.split.2.1, add_zero]

theorem int_iff_up_mem (q : GlobalTheory.FinPl.SplitPt D k) (hq : q.UnitAA) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (eS : (LS : Set (Fin S.rank → D.host.E)) = intVec D S.rank)
    (eT : (LT : Set (Fin T.rank → D.host.E)) = intVec D T.rank)
    (hFS : ∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v))
    (hFT : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v))
    (x : Matrix Y Y' k) : (∀ r s, x r s ∈ 𝒪[k]) ↔ (ofSplit q).up FS FT x ∈ stdHom S T := by
  rw [stdHom, ← eS, ← eT]
  refine ⟨fun hx => latO_le S T _ _ (fun _ _ => trivial) (GlobalTheory.UpMem.up_mem_latO D k q hq Y Y' S T FS FT LS LT hS hT hFS hFT x hx),
    fun hx => ?_⟩
  have hh := Witness.up_half (ofSplit q) FS FT x
  obtain ⟨x', hx', e⟩ := GlobalTheory.HalfIntUp.exists_int_up D k q hq Y Y' S T FS FT LS LT hS hT hFS hFT _ (mem_latO_at q hx hh) hh
  have := congrArg ((ofSplit q).down FS FT) e
  rw [Witness.down_up, Witness.down_up] at this
  rwa [this]

theorem gamma_int (q : GlobalTheory.FinPl.SplitPt D k) {Y : Type} [Fintype Y] [DecidableEq Y] {T : HSp D} (FT : Frame k T.rank Y)
    {LT : GlobalTheory.FinPl.Lat T} (eT : (LT : Set (Fin T.rank → D.host.E)) = intVec D T.rank)
    (hFT : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) (r s) :
    FT.γ r s ∈ 𝒪[k] := by
  refine (hFT fun r => FT.γ r s).2 ?_ r
  have hs : (Pi.single s 1 : Fin T.rank → D.host.E) ∈ LT := by
    rw [← SetLike.mem_coe, eT]
    intro i
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  convert GlobalTheory.UpMem.e_mul_mem_latV q T LT hs using 2 with i
  have : (FT.β *ᵥ fun r => FT.γ r s) i = (FT.β * FT.γ) i s := rfl
  rw [this, FT.βγ, ← q.sec_pr, Matrix.one_apply, Pi.single_apply]
  split_ifs <;> simp

theorem mk_eq_mk_of_int {n : Type} {x y : n → k} (h : ∀ c, y c - x c ∈ 𝒪[k]) :
    (Submodule.Quotient.mk x : _ ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk y :=
  ((Submodule.Quotient.eq _).2 (show y - x ∈ box n (1 : kˣ) from fun c => h c)).symm

end Gen

section Mat
variable {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k]

theorem mul_toLoc (ι : E →+* k) {Y Y' : Type} [Fintype Y] [Fintype Y'] {a b nS nT : ℕ} (hS : nS = a) (hT : nT = b)
    (f : (Fin a → E) ≃ₗ[E] (Fin a → E)) (f' : (Fin b → E) ≃ₗ[E] (Fin b → E)) (e' : Y' ≃ Fin a) (e : Y ≃ Fin b)
    (β : Matrix (Fin nS) Y' k) (M : Matrix (Fin nT) Y k) (hβ : ∀ r c, β r c = ι (f (Pi.single (e' c) 1) (finCongr hS r)))
    (hM : ∀ r c, M r c = ι (f' (Pi.single (e c) 1) (finCongr hT r))) (γ : Matrix (Fin nT) (Fin nS) E) :
    M * toLoc ι e e' (Formalism.L2.Col.inFr f f' (Matrix.toLin' (γ.reindex (finCongr hT) (finCongr hS)))) = γ.map ι * β := by
  subst hS hT
  ext r c
  have key : ∀ x : Fin nT → E, ∑ y : Y, f' (Pi.single (e y) 1) r * x (e y) = f' x r := fun x => by
    rw [e.sum_comp fun j => f' (Pi.single j 1) r * x j]

    conv_rhs => rw [pi_eq_sum_univ' x, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

  simp only [Matrix.mul_apply, hβ, hM, toLoc, Matrix.map_apply, ← map_mul, ← map_sum, finCongr_refl, Equiv.refl_apply]
  rw [key]
  simp [Formalism.L2.Col.inFr, Matrix.mulVec, dotProduct]

end Mat

theorem twSt_h {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel) {S₀ : Set ℕ}
    (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (m2 j : ℕ)
    (al : (Formalism.L2.Col.twSt Ch sel mu cst m2 j).β) (P : Formalism.L2.Col.rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    (Formalism.L2.Col.twSt Ch sel mu cst m2 j).h al P = 1 := by
  revert al
  cases j with
  | zero => exact fun _ => rfl
  | succ i =>
    rw [Formalism.L2.Col.twSt]
    by_cases h1 : i + 1 ≤ m2
    · rw [if_pos h1]
      exact fun _ => dif_neg fun h => (@Finset.mem_sdiff _ (_) _ _ _).1 h |>.2 hP
    · rw [if_neg h1]
      by_cases h2 : i + 1 = m2 + 1
      · rw [if_pos h2]
        exact fun _ => rfl
      · rw [if_neg h2]
        exact fun al => al.elim

section World
open _root_.Formalism.L2.Col

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {v : B.Word} {Ch : ℕ → Type}
  {A : ColDat I l Z v Ch} {a : XPart (I.rec7 l Z) v} {ζ₀ : Fin a.Lz.rank → (I.rec7 l Z).host.E}
  {PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E} {G : GX a ζ₀ PP} {P : rowSG (B.primes X) I.sel (I.tup I.mu0)}



end World

section Main
open _root_.Formalism.L2.Col

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {w : World I l Z} {v : B.Word}
  {a : XPart (I.rec7 l Z) v} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {o : OffX a k ((B.primes X).vT v)} {G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1} {A : ColDat I l Z v (w.C.herm.base.Ch v)}

end Main

end GlobalTheory.SeeSaw.StdMatch
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData GlobalTheory.SymChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.SuppFirst

theorem e_mul_ι {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x : k) : p.e * p.ι x = p.ι x := by
  rw [← p.ι_π, p.π_ι]

theorem ι_mul' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have h := p.ι_π (p.ι x * p.ι y)
  rw [map_mul, p.π_ι, p.π_ι, ← mul_assoc, e_mul_ι] at h
  exact h

theorem ι_one' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.ι 1 = p.e := by
  have h := p.ι_π 1
  rwa [map_one, mul_one] at h

theorem shift_mul {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x y : k) :
    (p.ι x + (1 - p.e)) * (p.ι y + (1 - p.e)) = p.ι (x * y) + (1 - p.e) := by
  have he : p.e * p.e = p.e := p.split.1
  have h1 : p.ι x * (1 - p.e) = 0 := by
    rw [mul_sub, mul_one, mul_comm, e_mul_ι, sub_self]
  have h2 : (1 - p.e) * p.ι y = 0 := by
    rw [sub_mul, one_mul, e_mul_ι, sub_self]
  have h3 : (1 - p.e) * (1 - p.e) = 1 - p.e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  rw [ι_mul', add_mul, mul_add, mul_add, h1, h2, h3, add_zero, zero_add]

def shiftU {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : kˣ →* (AE D)ˣ where
  toFun x := ⟨p.ι x + (1 - p.e), p.ι (x⁻¹ : kˣ) + (1 - p.e), by
      rw [shift_mul, Units.mul_inv, ι_one']; ring, by
      rw [shift_mul, Units.inv_mul, ι_one']; ring⟩
  map_one' := by ext; simp [ι_one']
  map_mul' x y := by ext; simp [shift_mul]

theorem exists_comp {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (χ : (AE D)ˣ →* Circle) : ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ := by
  refine ⟨Circle.toUnits.comp (χ.comp (shiftU p)), fun x a ha => ?_⟩
  have : shiftU p x = a := Units.ext ha.symm
  simp [this]

theorem card_frame {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : Frame k N Y) :
    Fintype.card Y = N := by
  apply le_antisymm
  · have h := Matrix.rank_mul_le_left Fr.γ Fr.β
    rw [Fr.γβ, Matrix.rank_one] at h
    have h' := Matrix.rank_le_card_width Fr.γ
    rw [Fintype.card_fin] at h'
    exact h.trans h'
  · have h := Matrix.rank_mul_le_left Fr.β Fr.γ
    rw [Fr.βγ, Matrix.rank_one, Fintype.card_fin] at h
    exact h.trans (Matrix.rank_le_card_width Fr.β)

def prH {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : D.host.E →+* k := p.π.comp (incA D)

theorem prH_apply {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (a : D.host.E) : prH p a = p.pr a := rfl

theorem exists_coreFrame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} {n₀ n₁ n₂ : Type}
    [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] {c : ℕ}
    (F : Dbl p B J B' n₀ n₁ n₂ c) : ∃ C : Frame k B.V₀.rank (n₀ ⊕ Unit), p.IsCoreFrame B F.s F.F₀ C := by
  obtain ⟨hc, hA, -, hz, -⟩ := F.bes
  let M : Matrix (Fin B.V₀.rank) (n₀ ⊕ Unit) k :=
    fromCols (B.o.iA.map p.pr * F.F₀.β) (Matrix.of fun r (_ : Unit) => F.s * p.pr (vecB B.o B.ζ r))
  let f : n₀ ⊕ Unit → n₀ ⊕ Fin (c + 1 + 1 + 1) := Sum.elim Sum.inl fun _ => Sum.inr ⟨σ + 1, by omega⟩
  have hf : Function.Injective f := by
    rintro (a | _) (b | _) h <;> simp_all [f]
  have key : B.d.i₀.map p.pr * M = F.G₀.β.submatrix id f := by
    ext r (a | _)
    · simp only [M, f, Matrix.mul_fromCols, fromCols_apply_inl, submatrix_apply, id, Sum.elim_inl]
      rw [hA r a, ← Matrix.mul_assoc]
      have hm : B.d.i₀.map p.pr * B.o.iA.map p.pr = (B.d.i₀ * B.o.iA).map p.pr :=
        (Matrix.map_mul (f := prH p)).symm
      rw [hm]
    · simp only [M, f, Matrix.mul_fromCols, fromCols_apply_inr, submatrix_apply, id, Sum.elim_inr]
      rw [hz ⟨σ + 1, by omega⟩ rfl r]
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, mulVec, dotProduct]

      rw [← prH_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_mul, prH_apply, prH_apply]
      ring
  let L : Matrix (n₀ ⊕ Unit) (Fin B.V₀.rank) k := F.G₀.γ.submatrix f id * B.d.i₀.map p.pr
  have hLM : L * M = 1 := by
    simp only [L, Matrix.mul_assoc, key]
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, F.G₀.γβ]
    exact Matrix.submatrix_one _ hf
  have hcard : Fintype.card (n₀ ⊕ Unit) = B.V₀.rank := by
    have h1 := card_frame F.G₀
    have h2 := B.d.rank_add
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h1 ⊢
    omega
  have hML : M * L = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (n₀ ⊕ Unit) (Fin B.V₀.rank) k (A := L) (B := M) (by simpa using hcard)).mp hLM
  refine ⟨⟨M, L, hML, hLM⟩, fun r a => ?_, fun r => ?_⟩
  · simp [M]
  · simp [M]

theorem isLoc_one {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : Frame k V.rank Y) : p.IsLoc Fr 1 1 := by
  obtain ⟨hloc, -, -⟩ := GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p
  obtain ⟨g₀, hg₀, hu⟩ := (hloc V Y Fr).1 1
  have h2 := (hloc V Y Fr).2.2 _ _ _ _ hg₀ hg₀
  rw [mul_one] at h2
  have e : g₀ * g₀ = g₀ := hu _ h2
  have : g₀ = 1 := by
    have := congrArg (g₀⁻¹ * ·) e
    simpa [← mul_assoc] using this
  exact this ▸ hg₀

theorem gsupp1 : ∀ (D : D7), OmLoc D → FlatBF D → GlobalTheory.LocFlat.SymCollapse → GSupp1 D := by
  intro D hOm hFl hSym k _ _ _ _ p s κ S t _ _ ψ hψ j c H σ B J B' F s₁ hμ T₁ hT₁ Φ₁ hΦ₁ h hh hne
  obtain ⟨hloc, hjac, -⟩ := GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := exists_isUnitVol k
  haveI := hν.1
  obtain ⟨hk, hhk⟩ := (hloc J.W _ F.G₁).2.1 h hh
  have hc : c = 2 * σ := by have := F.bes.1; omega

  obtain ⟨μT, hT⟩ := exists_comp p s₁.χW
  have hS : p.IsComp s₁.χV (S.μ (j + 1))⁻¹ := by
    intro x a ha
    have := hμ x a ha
    simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv] at this ⊢
    rw [this, inv_inv]

  let Φ' : SB (Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1 + 1)) k) :=
    ⟨om (S.μ (j + 1)) 1 hk Φ₁.1, om_mem_SB (μ := S.μ (j + 1)) (1 : GL _ k) hk Φ₁.2⟩
  have hom : s₁.om (1, h) (T₁ Φ₁) = T₁ Φ' := by
    refine hOm k p ψ B.V J.W s₁.χV s₁.χW s₁.om s₁.weil _ μT hS hT _ _ F.G₀ F.G₁ T₁ hT₁ 1 1 h hk
      (isLoc_one p _) hhk Φ₁ Φ' ?_
    simp [Φ']

  obtain ⟨C, hC⟩ := exists_coreFrame p F
  obtain ⟨T₀, -, hT₀⟩ := hFl k p ν hν.1 ψ S.ψ hψ (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C F.G₀ F.F₁ F.G₁
    hC F.bes F.jac T₁ hT₁
  have hSB := ((GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k S.ψ ν S.cond.continuous hν.1 _ _ (c + 1 + 1) (σ + 1 + 1) (by omega)).1
    (by omega)).1 Φ'.1 Φ'.2
  have hflat := hT₀ Φ' ⟨_, hSB⟩ rfl
  rw [hom, hflat] at hne
  have hne' : GlobalTheory.LocFlat.flCol S.ψ ν (σ + 1 + 1) (om (S.μ (j + 1)) 1 hk ((S.T t).Phi j (c + 1 + 1) (by omega))) ≠ 0 := by
    intro h0
    apply hne
    have : (⟨_, hSB⟩ : SB _) = 0 := by
      ext1
      simpa [Φ', hΦ₁] using h0
    rw [this, map_zero]
  obtain ⟨β, q, hq, u, hu, hkeq⟩ := (hSym k ν hν s κ S t).1 j (c + 1) (by omega) (σ + 1) (by omega) hk hne'
  obtain ⟨r, hr, -⟩ := (hloc J.W _ F.G₁).1 (colE (c + 1 + 1) (σ + 1 + 1) β * q)
  obtain ⟨u', hu', -⟩ := (hloc J.W _ F.G₁).1 u
  have hprod := (hloc J.W _ F.G₁).2.2 _ _ _ _ hr hu'
  rw [← hkeq] at hprod
  obtain ⟨g', -, huniq⟩ := (hloc J.W _ F.G₁).1 hk
  refine ⟨r, hjac _ _ _ _ _ _ _ _ F.jac r β q hq hr, hr.1, u', u, hu', hu, ?_⟩
  exact (huniq _ hhk).trans (huniq _ hprod).symm

end GlobalTheory.LocMod.SuppFirst
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ u : WO S T, u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) → IsHalf q.e u → ∃ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) ∧ u = (ofSplit q).up FS FT x := by
  first | exact @GlobalTheory.HalfIntUp.exists_int_up | exact GlobalTheory.HalfIntUp.exists_int_up | (intros; apply GlobalTheory.HalfIntUp.exists_int_up <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPoint_heckeComponent_tame_and_residual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → DenseRange (ofSplit q).pr → ∀ (χ : (AE D)ˣ →* Circle) (H : Formalism.L2.Host.HChar D.host.E) (c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (μ : kˣ →* ℂˣ), ChrEq χ H → IsRes H PP c → (ofSplit q).IsComp χ μ → IsTame μ ∧ ∀ (a : D.host.E) (u : kˣ) (r : (Formalism.L2.DIV.kP PP)ˣ), Formalism.L2.Col.IntAt PP a → (r : Formalism.L2.DIV.kP PP) = Formalism.L2.Col.redP PP a → (u : k) = (ofSplit q).pr a → μ u = c r := by
  first | exact @GlobalTheory.LocMod.SplitHecke.tame_and_res | exact GlobalTheory.LocMod.SplitHecke.tame_and_res | (intros; apply GlobalTheory.LocMod.SplitHecke.tame_and_res <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SeeSaw.LevRed

open GlobalTheory.LocMod GlobalTheory.StepData GlobalTheory.SymChain

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one' (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem finE_val' (V : HSp D) (g : GA D V) : (Lev.finE V g).val = (mt V g).map (toEAf D) := rfl

theorem exists_lift (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul b α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

theorem frGL_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    (Formalism.L2.DIV.frGL β y).val * β.val = β.val * (Formalism.L2.DIV.intGL F E n y).val := by
  have h0 : Formalism.L2.DIV.frGL β y * β = β * Formalism.L2.DIV.intGL F E n y := inv_mul_cancel_right _ _
  rw [← Units.val_mul, h0, Units.val_mul]

theorem eq_map_of_moved {S K n : Type} [CommRing S] [CommRing K] [Fintype n] [DecidableEq n] (π : S →+* K) (β : GL n S)
    (x y : Matrix n n S) (h1 : x * β.val = β.val * y) (T T' H N M : Matrix n n K) (hT : T' * T = 1)
    (hN : T * β.val.map π = N) (hM : H * N = N * M) (hx : T * x.map π = H * T) : M = y.map π := by
  have h2 : x.map π * β.val.map π = β.val.map π * y.map π := by rw [← Matrix.map_mul, h1, Matrix.map_mul]
  have h3 : N * M = N * y.map π := by
    rw [← hM, ← hN, Matrix.mul_assoc _ _ (y.map π), ← h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hx]
  have h4 : ((β⁻¹).val.map π * T') * N = 1 := by
    rw [← hN, Matrix.mul_assoc, ← Matrix.mul_assoc T', hT, Matrix.one_mul, ← Matrix.map_mul,
      Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  calc M = ((β⁻¹).val.map π * T') * (N * M) := by rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
    _ = y.map π := by rw [h3, ← Matrix.mul_assoc, h4, Matrix.one_mul]



theorem red_of_movedTo (q : SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (t h : GA D V) (N M : Matrix (Fin V.rank) (Fin V.rank) k)
    (hN : MovedTo (ofSplit q) V t β N) (hM : (mt V h).map q.pr * N = N * M)
    (hx : Lev.finE V (t⁻¹ * h * t) ∈ Formalism.L2.DIV.St β) (i j : Fin V.rank) (z : 𝓞 D.host.E)
    (hz : Ideal.Quotient.mk PP.asIdeal z = (Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j) :
    valuation k (M i j - (ofSplit q).pr (z : D.host.E)) < 1 := by
  obtain ⟨π', hπ, hred, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D k q PP hPP
  obtain ⟨y, hy⟩ := hx
  rw [← hy, Formalism.L2.DIV.redFn_frGL] at hz
  choose l hl using exists_lift (D := D)
  have hπ' : ∀ m : Matrix (Fin V.rank) (Fin V.rank) (AE D), (m.map (toEAf D)).map π' = m.map q.pr := fun m => by
    ext a b; exact hπ _
  have hb : (β.val.map l).map (toEAf D) = β.val := by ext a b; exact hl _
  have hN' : (mt V t).map q.pr * β.val.map π' = N := by
    rw [← hN _ hb, Matrix.map_mul]
    congr 1
    conv_lhs => rw [← hb]
    exact hπ' _
  let ψ := π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
  have h1 : (Lev.finE V (t⁻¹ * h * t)).val * β.val = β.val * (Formalism.L2.DIV.intGL D.host.F D.host.E _ y).val := by
    have h0 := frGL_mul β y
    rw [hy] at h0
    exact h0
  have hfin : (Lev.finE V (t⁻¹ * h * t)).val.map π' = (mt V (t⁻¹ * h * t)).map q.pr := by
    rw [finE_val', hπ']
  have h5 := eq_map_of_moved π' β _ _ h1 ((mt V t).map q.pr) ((mt V t⁻¹).map q.pr) _ N M
    (by rw [← Matrix.map_mul, ← mt_mul', inv_mul_cancel, mt_one', Matrix.map_one _ (map_zero _) (map_one _)]) hN' hM
    (by
      rw [hfin, ← Matrix.map_mul, ← Matrix.map_mul, ← mt_mul', ← mt_mul', mul_assoc, mul_inv_cancel_left])
  have h7 : M i j = ψ (y.val i j) := congrFun (congrFun h5 i) j
  have h6 : (ofSplit q).pr (z : D.host.E) = ψ (Formalism.L2.DIV.oToS D.host.F D.host.E z) := (hπ _).symm
  rw [h7, h6, ← map_sub, ← hred.ker, map_sub, Formalism.L2.DIV.resS_oToS, hz]
  exact sub_self _

end GlobalTheory.SeeSaw.LevRed

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unramifiedHeckeChar_at_uniformizerIdele_eq_value : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP → ∀ (x : (AE D)ˣ) (ϖ : (Fv D.host.F v)ˣ), IsLocUnif φ x ϖ → ∀ χ : (AE D)ˣ →* Circle, GlobalTheory.LFun.UnrAt (F := D.host.F) χ PP → Circle.toUnits (χ x) = GlobalTheory.LFun.val (F := D.host.F) χ PP := by
  first | exact @GlobalTheory.LocUnifVal.value_eq_val | exact GlobalTheory.LocUnifVal.value_eq_val | (intros; apply GlobalTheory.LocUnifVal.value_eq_val <;> assumption)
end
